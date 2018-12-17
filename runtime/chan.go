// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package runtime

// This file contains the implementation of Go channels.

import "unsafe"

const (
	maxAlign  = 8
	hchanSize = unsafe.Sizeof(hchan{}) + uintptr(-int(unsafe.Sizeof(hchan{}))&(maxAlign-1))
)

type hchan struct {
	qcount   uint           // total data in the queue
	dataqsiz uint           // size of the circular queue
	buf      unsafe.Pointer // points to an array of dataqsiz elements
	elemsize uint16
	closed   uint32
	elemtype *_type // element type
	sendx    uint   // send index
	recvx    uint   // receive index
	recvq    waitq  // list of recv waiters
	sendq    waitq  // list of send waiters
	lock     mutex
}

type waitq struct {
	first *sudog
	last  *sudog
}

//go:linkname reflect_makechan reflect.makechan
func reflect_makechan(t *chantype, size int64) *hchan {
	return makechan(t, size)
}

func makechan(t *chantype, size int64) *hchan {
	elem := t.elem

	// compiler checks this but be safe.
	if elem.size >= 1<<16 {
		throw("makechan: invalid channel element type")
	}
	if hchanSize%maxAlign != 0 || elem.align > maxAlign {
		throw("makechan: bad alignment")
	}
	if size < 0 || int64(uintptr(size)) != size || (elem.size > 0 && uintptr(size) > (_MaxMem-hchanSize)/uintptr(elem.size)) {
		panic("makechan: size out of range")
	}

	var c *hchan
	if elem.kind&kindNoPointers != 0 || size == 0 {
		// Allocate memory in one call.
		// Hchan does not contain pointers interesting for GC in this case:
		// buf points into the same allocation, elemtype is persistent.
		// SudoG's are referenced from their owning thread so they can't be collected.
		// TODO(dvyukov,rlh): Rethink when collector can move allocated objects.
		c = (*hchan)(mallocgc(hchanSize+uintptr(size)*uintptr(elem.size), nil, flagNoScan))
		if size > 0 && elem.size != 0 {
			c.buf = add(unsafe.Pointer(c), hchanSize)
		} else {
			// race detector uses this location for synchronization
			// Also prevents us from pointing beyond the allocation (see issue 9401).
			c.buf = unsafe.Pointer(c)
		}
	} else {
		c = new(hchan)
		c.buf = newarray(elem, uintptr(size))
	}
	c.elemsize = uint16(elem.size)
	c.elemtype = elem
	c.dataqsiz = uint(size)

	return c
}

// chanbuf(c, i) 返回 buffer 中第 i 位数据的地址(指针)
func chanbuf(c *hchan, i uint) unsafe.Pointer {
	return add(c.buf, uintptr(i)*uintptr(c.elemsize))
}

// entry point for c <- x from compiled code
//go:nosplit
func chansend1(t *chantype, c *hchan, elem unsafe.Pointer) {
	chansend(t, c, elem, true, getcallerpc(unsafe.Pointer(&t)))
}

/*
 * generic single channel send/recv
 * If block is not nil,
 * then the protocol will not
 * sleep but return if it could
 * not complete.
 *
 * sleep can wake up with g.param == nil
 * when a channel involved in the sleep has
 * been closed.  it is easiest to loop and re-run
 * the operation; we'll see that it's now closed.
 * 如果参数 block == false, 那么该函数不会阻塞，而是直接返回是否成功发送数据到 channel
 */
func chansend(t *chantype, c *hchan, ep unsafe.Pointer, block bool, callerpc uintptr) bool {
	// channel 的值是 nil
	if c == nil {
		if !block {
			// 如果不 block, 则直接返回 false, 表示发送失败
			return false
		}
		// 项一个 nil 的 channel 发送数据, 永远 block 在这里
		gopark(nil, nil, "chan send (nil chan)", traceEvGoStop, 2)
		throw("unreachable")
	}

	// Fast path: check for failed non-blocking operation without acquiring the lock.
	//
	// After observing that the channel is not closed, we observe that the channel is
	// not ready for sending. Each of these observations is a single word-sized read
	// (first c.closed and second c.recvq.first or c.qcount depending on kind of channel).
	// Because a closed channel cannot transition from 'ready for sending' to
	// 'not ready for sending', even if the channel is closed between the two observations,
	// they imply a moment between the two when the channel was both not yet closed
	// and not ready for sending. We behave as if we observed the channel at that moment,
	// and report that the send cannot proceed.
	//
	// It is okay if the reads are reordered here: if we observe that the channel is not
	// ready for sending and then observe that it is not closed, that implies that the
	// channel wasn't closed during the first observation.
	// 快速通道, 在不需要加锁的情况下完成操作
	// 如果操作(不阻塞发送 && channel 没有关闭 && 目前没有 goroutine 正在读这个 channel), 这直接返回 false
	if !block && c.closed == 0 && ((c.dataqsiz == 0 && c.recvq.first == nil) ||
		(c.dataqsiz > 0 && c.qcount == c.dataqsiz)) {
		return false
	}

	var t0 int64

	lock(&c.lock)

	// channel 已经被 close 了，直接 panic
	if c.closed != 0 {
		unlock(&c.lock)
		panic("send on closed channel")
	}

	// 同步 channel, 也就是长度是 0 的 channel, no buffer channel
	if c.dataqsiz == 0 { // synchronous channel
		sg := c.recvq.dequeue()
		if sg != nil { // found a waiting receiver
			unlock(&c.lock)

			recvg := sg.g
			if sg.elem != nil {
				// syncsend 实际上是从一个 goroutine 的 stack 空间, copy value 到另一个 goroutine 的 stack 空间, 以此来减少 gc
				syncsend(c, sg, ep)
			}
			recvg.param = unsafe.Pointer(sg)
			if sg.releasetime != 0 {
				sg.releasetime = cputicks()
			}
			goready(recvg, 3)
			return true
		}

		if !block {
			unlock(&c.lock)
			return false
		}

		// 没有接收者, 则将当前的 goroutine 阻塞住, 放到 channel 的 sendq 里面
		// no receiver available: block on this channel.
		gp := getg() // gp 表示当前要执行发送操作的 goroutine
		mysg := acquireSudog()
		mysg.releasetime = 0
		if t0 != 0 {
			mysg.releasetime = -1
		}
		mysg.elem = ep
		mysg.waitlink = nil
		gp.waiting = mysg
		mysg.g = gp
		mysg.selectdone = nil
		gp.param = nil
		c.sendq.enqueue(mysg)
		goparkunlock(&c.lock, "chan send", traceEvGoBlockSend, 3)

		// someone woke us up.
		// goroutine 被唤醒了, 因为有其他 goroutine 要从 channel 中读取数据
		if mysg != gp.waiting {
			throw("G waiting list is corrupted!")
		}
		gp.waiting = nil
		if gp.param == nil {
			if c.closed == 0 {
				throw("chansend: spurious wakeup")
			}
			panic("send on closed channel")
		}
		gp.param = nil
		releaseSudog(mysg)
		return true
	}

	// asynchronous channel
	// wait for some space to write our data
	var t1 int64
	// 循环等待 channel 有空位了, 这个循环内 goroutine 可能会被反复的 block 和 ready, 但直到把数据放到 buffer 了才退出循环
	for futile := byte(0); c.qcount >= c.dataqsiz; futile = traceFutileWakeup {
		if !block { // 非阻塞就直接退出就行了
			unlock(&c.lock)
			return false
		}
		gp := getg()
		mysg := acquireSudog()
		mysg.releasetime = 0
		if t0 != 0 {
			mysg.releasetime = -1
		}
		mysg.g = gp
		mysg.elem = nil
		mysg.selectdone = nil
		// 加到 sendq 队列中
		c.sendq.enqueue(mysg)
		// 阻塞等待被唤醒
		goparkunlock(&c.lock, "chan send", traceEvGoBlockSend|futile, 3)

		// someone woke us up - try again
		// channel 有空间了, 被唤醒, 参见 chanrecv() 方法, 那里会因为读 channel 操作而唤醒这里的写 channel goroutine
		if mysg.releasetime > 0 {
			t1 = mysg.releasetime
		}
		releaseSudog(mysg)
		lock(&c.lock)
		if c.closed != 0 { // 被唤醒后发现 channel 已经被 close 了, 直接 panic
			unlock(&c.lock)
			panic("send on closed channel")
		}
	}

	typedmemmove(c.elemtype, chanbuf(c, c.sendx), ep)
	c.sendx++
	if c.sendx == c.dataqsiz {
		c.sendx = 0
	}
	c.qcount++

	// wake up a waiting receiver
	// 把数据成功放到 channel buffer 中后, 尝试唤醒一个等待接收 channel 的 goroutine
	sg := c.recvq.dequeue()
	if sg != nil {
		recvg := sg.g
		unlock(&c.lock)
		if sg.releasetime != 0 {
			sg.releasetime = cputicks()
		}
		goready(recvg, 3)
	} else {
		unlock(&c.lock)
	}
	return true
}

func syncsend(c *hchan, sg *sudog, elem unsafe.Pointer) {
	// Send on unbuffered channel is the only operation
	// in the entire runtime where one goroutine
	// writes to the stack of another goroutine. The GC assumes that
	// stack writes only happen when the goroutine is running and are
	// only done by that goroutine. Using a write barrier is sufficient to
	// make up for violating that assumption, but the write barrier has to work.
	// typedmemmove will call heapBitsBulkBarrier, but the target bytes
	// are not in the heap, so that will not help. We arrange to call
	// memmove and typeBitsBulkBarrier instead.
	memmove(sg.elem, elem, c.elemtype.size)
	typeBitsBulkBarrier(c.elemtype, uintptr(sg.elem), c.elemtype.size)
	sg.elem = nil
}

func closechan(c *hchan) {
	if c == nil {
		panic("close of nil channel")
	}

	lock(&c.lock)
	if c.closed != 0 {
		unlock(&c.lock)
		panic("close of closed channel")
	}

	c.closed = 1

	// release all readers
	for {
		sg := c.recvq.dequeue()
		if sg == nil {
			break
		}
		gp := sg.g
		sg.elem = nil
		gp.param = nil
		goready(gp, 3)
	}

	// release all writers
	for {
		sg := c.sendq.dequeue()
		if sg == nil {
			break
		}
		gp := sg.g
		sg.elem = nil
		gp.param = nil
		goready(gp, 3)
	}
	unlock(&c.lock)
}

// entry points for <- c from compiled code
//go:nosplit
func chanrecv1(t *chantype, c *hchan, elem unsafe.Pointer) {
	chanrecv(t, c, elem, true)
}

//go:nosplit
func chanrecv2(t *chantype, c *hchan, elem unsafe.Pointer) (received bool) {
	_, received = chanrecv(t, c, elem, true)
	return
}

// chanrecv receives on channel c and writes the received data to ep.
// ep may be nil, in which case received data is ignored.
// If block == false and no elements are available, returns (false, false).
// Otherwise, if c is closed, zeros *ep and returns (true, false).
// Otherwise, fills in *ep with an element and returns (true, true).
func chanrecv(t *chantype, c *hchan, ep unsafe.Pointer, block bool) (selected, received bool) {
	// raceenabled: don't need to check ep, as it is always on the stack.

	// 同 chansend 一样, 从一个 nil 的 channel 读取数据, 也会永远 block
	if c == nil {
		if !block {
			return
		}
		gopark(nil, nil, "chan receive (nil chan)", traceEvGoStop, 2)
		throw("unreachable")
	}

	// Fast path: check for failed non-blocking operation without acquiring the lock.
	//
	// After observing that the channel is not ready for receiving, we observe that the
	// channel is not closed. Each of these observations is a single word-sized read
	// (first c.sendq.first or c.qcount, and second c.closed).
	// Because a channel cannot be reopened, the later observation of the channel
	// being not closed implies that it was also not closed at the moment of the
	// first observation. We behave as if we observed the channel at that moment
	// and report that the receive cannot proceed.
	//
	// The order of operations is important here: reversing the operations can lead to
	// incorrect behavior when racing with a close.
	if !block && (c.dataqsiz == 0 && c.sendq.first == nil ||
		c.dataqsiz > 0 && atomicloaduint(&c.qcount) == 0) &&
		atomicload(&c.closed) == 0 {
		return
	}

	lock(&c.lock)
	if c.dataqsiz == 0 { // synchronous channel
		if c.closed != 0 {
			return recvclosed(c, ep)
		}

		sg := c.sendq.dequeue()
		if sg != nil {
			unlock(&c.lock)

			if ep != nil {
				typedmemmove(c.elemtype, ep, sg.elem)
			}
			sg.elem = nil
			gp := sg.g
			gp.param = unsafe.Pointer(sg)
			if sg.releasetime != 0 {
				sg.releasetime = cputicks()
			}
			goready(gp, 3)
			selected = true
			received = true
			return
		}

		if !block {
			unlock(&c.lock)
			return
		}

		// no sender available: block on this channel.
		gp := getg()
		mysg := acquireSudog()
		mysg.releasetime = 0
		mysg.elem = ep
		mysg.waitlink = nil
		gp.waiting = mysg
		mysg.g = gp
		mysg.selectdone = nil
		gp.param = nil
		c.recvq.enqueue(mysg)
		goparkunlock(&c.lock, "chan receive", traceEvGoBlockRecv, 3)

		// someone woke us up
		if mysg != gp.waiting {
			throw("G waiting list is corrupted!")
		}
		gp.waiting = nil
		haveData := gp.param != nil
		gp.param = nil
		releaseSudog(mysg)

		if haveData {
			// a sender sent us some data. It already wrote to ep.
			selected = true
			received = true
			return
		}

		lock(&c.lock)
		if c.closed == 0 {
			throw("chanrecv: spurious wakeup")
		}
		return recvclosed(c, ep)
	}

	// asynchronous channel
	// wait for some data to appear
	for futile := byte(0); c.qcount <= 0; futile = traceFutileWakeup {
		if c.closed != 0 {
			selected, received = recvclosed(c, ep)
			return
		}

		if !block {
			unlock(&c.lock)
			return
		}

		// wait for someone to send an element
		gp := getg()
		mysg := acquireSudog()
		mysg.releasetime = 0
		mysg.elem = nil
		mysg.g = gp
		mysg.selectdone = nil

		c.recvq.enqueue(mysg)
		goparkunlock(&c.lock, "chan receive", traceEvGoBlockRecv|futile, 3)
		// someone woke us up - try again
		releaseSudog(mysg)
		lock(&c.lock)
	}

	if ep != nil {
		typedmemmove(c.elemtype, ep, chanbuf(c, c.recvx))
	}
	memclr(chanbuf(c, c.recvx), uintptr(c.elemsize))

	c.recvx++
	if c.recvx == c.dataqsiz {
		c.recvx = 0
	}
	c.qcount--

	// ping a sender now that there is space
	sg := c.sendq.dequeue()
	if sg != nil {
		gp := sg.g
		unlock(&c.lock)
		if sg.releasetime != 0 {
			sg.releasetime = cputicks()
		}
		goready(gp, 3)
	} else {
		unlock(&c.lock)
	}

	selected = true
	received = true
	return
}

// recvclosed is a helper function for chanrecv.  Handles cleanup
// when the receiver encounters a closed channel.
// Caller must hold c.lock, recvclosed will release the lock.
func recvclosed(c *hchan, ep unsafe.Pointer) (selected, recevied bool) {
	unlock(&c.lock)
	if ep != nil {
		memclr(ep, uintptr(c.elemsize))
	}
	return true, false
}

// compiler implements
//
//	select {
//	case c <- v:
//		... foo
//	default:
//		... bar
//	}
//
// as
//
//	if selectnbsend(c, v) {
//		... foo
//	} else {
//		... bar
//	}
//
func selectnbsend(t *chantype, c *hchan, elem unsafe.Pointer) (selected bool) {
	return chansend(t, c, elem, false, getcallerpc(unsafe.Pointer(&t)))
}

// compiler implements
//
//	select {
//	case v = <-c:
//		... foo
//	default:
//		... bar
//	}
//
// as
//
//	if selectnbrecv(&v, c) {
//		... foo
//	} else {
//		... bar
//	}
//
func selectnbrecv(t *chantype, elem unsafe.Pointer, c *hchan) (selected bool) {
	selected, _ = chanrecv(t, c, elem, false)
	return
}

// compiler implements
//
//	select {
//	case v, ok = <-c:
//		... foo
//	default:
//		... bar
//	}
//
// as
//
//	if c != nil && selectnbrecv2(&v, &ok, c) {
//		... foo
//	} else {
//		... bar
//	}
//
func selectnbrecv2(t *chantype, elem unsafe.Pointer, received *bool, c *hchan) (selected bool) {
	// TODO(khr): just return 2 values from this function, now that it is in Go.
	selected, *received = chanrecv(t, c, elem, false)
	return
}

//go:linkname reflect_chanclose reflect.chanclose
func reflect_chanclose(c *hchan) {
	closechan(c)
}

func (q *waitq) enqueue(sgp *sudog) {
	sgp.next = nil
	x := q.last
	if x == nil {
		sgp.prev = nil
		q.first = sgp
		q.last = sgp
		return
	}
	sgp.prev = x
	x.next = sgp
	q.last = sgp
}

func (q *waitq) dequeue() *sudog {
	for {
		sgp := q.first
		if sgp == nil {
			return nil
		}
		y := sgp.next
		if y == nil {
			q.first = nil
			q.last = nil
		} else {
			y.prev = nil
			q.first = y
			sgp.next = nil // mark as removed (see dequeueSudog)
		}

		// if sgp participates in a select and is already signaled, ignore it
		if sgp.selectdone != nil {
			// claim the right to signal
			if *sgp.selectdone != 0 || !cas(sgp.selectdone, 0, 1) {
				continue
			}
		}

		return sgp
	}
}
