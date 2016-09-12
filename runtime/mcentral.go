// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Central free lists.
//
// See malloc.go for an overview.
//
// The MCentral doesn't actually contain the list of free objects; the MSpan does.
// Each MCentral is two lists of MSpans: those with free objects (c->nonempty)
// and those that are completely allocated (c->empty).

package runtime

// Central list of free objects of a given size.
type mcentral struct {
	lock      mutex
	sizeclass int32
	nonempty  mspan // list of spans with a free object
	empty     mspan // list of spans with no free objects (or cached in an mcache)
}

// Initialize a single central free list.
func mCentral_Init(c *mcentral, sizeclass int32) {
	c.sizeclass = sizeclass
	mSpanList_Init(&c.nonempty)
	mSpanList_Init(&c.empty)
}

// Allocate a span to use in an MCache.
func mCentral_CacheSpan(c *mcentral) *mspan {
	// Deduct credit for this span allocation and sweep if necessary.
	deductSweepCredit(uintptr(class_to_size[c.sizeclass]), 0)

	lock(&c.lock)
	sg := mheap_.sweepgen
retry:
	var s *mspan
	// nonempty 里的 span 里有空闲的位置给 object 用
	// 在 nonempty 列表中找到一个没有正在被清理的 span
	for s = c.nonempty.next; s != &c.nonempty; s = s.next {
		if s.sweepgen == sg-2 && cas(&s.sweepgen, sg-2, sg-1) {
			mSpanList_Remove(s)
			mSpanList_InsertBack(&c.empty, s)
			unlock(&c.lock)
			mSpan_Sweep(s, true)
			goto havespan
		}
		if s.sweepgen == sg-1 { // 正在被清理
			// the span is being swept by background sweeper, skip
			continue
		}
		// we have a nonempty span that does not require sweeping, allocate from it
		// 不需要清理的 span 块
		mSpanList_Remove(s)
		mSpanList_InsertBack(&c.empty, s)
		unlock(&c.lock)
		goto havespan
	}
	// empty 里所有的 span 都已经没有空位置了，都满了
	// 没有找到 span, 从 empty 列表里找
	for s = c.empty.next; s != &c.empty; s = s.next {
		if s.sweepgen == sg-2 && cas(&s.sweepgen, sg-2, sg-1) {
			// we have an empty span that requires sweeping,
			// sweep it and see if we can free some space in it
			mSpanList_Remove(s)
			// swept spans are at the end of the list
			mSpanList_InsertBack(&c.empty, s)
			unlock(&c.lock)
			mSpan_Sweep(s, true)
			if s.freelist.ptr() != nil {
				goto havespan
			}
			lock(&c.lock)
			// the span is still empty after sweep
			// it is already in the empty list, so just retry
			goto retry
		}
		if s.sweepgen == sg-1 {
			// the span is being swept by background sweeper, skip
			continue
		}
		// already swept empty span,
		// all subsequent ones must also be either swept or in process of sweeping
		break
	}
	unlock(&c.lock)

	// Replenish central list if empty.
	s = mCentral_Grow(c)
	if s == nil {
		return nil
	}
	lock(&c.lock)
	mSpanList_InsertBack(&c.empty, s)
	unlock(&c.lock)

	// At this point s is a non-empty span, queued at the end of the empty list,
	// c is unlocked.
havespan:
	cap := int32((s.npages << _PageShift) / s.elemsize) // 这个 span 最多能囊括 object 的个数
	n := cap - int32(s.ref)                             // 剩余可引用的 object 的数量
	if n == 0 {
		throw("empty span")
	}
	if s.freelist.ptr() == nil {
		throw("freelist empty")
	}
	s.incache = true
	return s
}

// Return span from an MCache.
func mCentral_UncacheSpan(c *mcentral, s *mspan) {
	lock(&c.lock)

	s.incache = false

	if s.ref == 0 {
		throw("uncaching full span")
	}

	cap := int32((s.npages << _PageShift) / s.elemsize)
	n := cap - int32(s.ref)
	if n > 0 {
		mSpanList_Remove(s)
		mSpanList_Insert(&c.nonempty, s)
	}
	unlock(&c.lock)
}

// Free n objects from a span s back into the central free list c.
// Called during sweep.
// Returns true if the span was returned to heap.  Sets sweepgen to
// the latest generation.
// If preserve=true, don't return the span to heap nor relink in MCentral lists;
// caller takes care of it.
func mCentral_FreeSpan(c *mcentral, s *mspan, n int32, start gclinkptr, end gclinkptr, preserve bool) bool {
	if s.incache {
		throw("freespan into cached span")
	}

	// Add the objects back to s's free list.
	wasempty := s.freelist.ptr() == nil
	end.ptr().next = s.freelist
	s.freelist = start
	s.ref -= uint16(n)

	if preserve {
		// preserve is set only when called from MCentral_CacheSpan above,
		// the span must be in the empty list.
		if s.next == nil {
			throw("can't preserve unlinked span")
		}
		atomicstore(&s.sweepgen, mheap_.sweepgen)
		return false
	}

	lock(&c.lock)

	// Move to nonempty if necessary.
	// wasempty 表示的是之前是否是 empty 的，如果是，现在不空了，放到需要放到 nonempty 里了
	// 如果 wasempty == false，说明之前就在 nonempty 里了，不用挪了
	if wasempty {
		mSpanList_Remove(s)
		mSpanList_Insert(&c.nonempty, s)
	}

	// delay updating sweepgen until here.  This is the signal that
	// the span may be used in an MCache, so it must come after the
	// linked list operations above (actually, just after the
	// lock of c above.)
	atomicstore(&s.sweepgen, mheap_.sweepgen)

	if s.ref != 0 { // 引用计数不为 0，说明 span 里还有其他 object 被使用被回收
		unlock(&c.lock)
		return false
	}

	// s is completely freed, return it to the heap.
	// span 里的所有的 object 都被释放了，说明这个 span 可以被回收到 heap 里了
	mSpanList_Remove(s)
	s.needzero = 1
	s.freelist = 0
	unlock(&c.lock)
	heapBitsForSpan(s.base()).initSpan(s.layout())
	mHeap_Free(&mheap_, s, 0)
	return true
}

// Fetch a new span from the heap and carve into objects for the free list.
// 从 heap 中获取新的 span，然后把它切割成 object 放入 freelist 中
func mCentral_Grow(c *mcentral) *mspan {
	npages := uintptr(class_to_allocnpages[c.sizeclass])
	size := uintptr(class_to_size[c.sizeclass])
	n := (npages << _PageShift) / size

	s := mHeap_Alloc(&mheap_, npages, c.sizeclass, false, true)
	if s == nil {
		return nil
	}

	p := uintptr(s.start << _PageShift)
	s.limit = p + size*n
	head := gclinkptr(p)
	tail := gclinkptr(p)
	// i==0 iteration already done
	for i := uintptr(1); i < n; i++ {
		p += size
		tail.ptr().next = gclinkptr(p)
		tail = gclinkptr(p)
	}
	if s.freelist.ptr() != nil {
		throw("freelist not empty")
	}
	tail.ptr().next = 0
	s.freelist = head
	heapBitsForSpan(s.base()).initSpan(s.layout())
	return s
}
