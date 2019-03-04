// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Memory allocator, based on tcmalloc.
// http://goog-perftools.sourceforge.net/doc/tcmalloc.html

// The main allocator works in runs of pages.
// Small allocation sizes (up to and including 32 kB) are
// rounded to one of about 100 size classes, each of which
// has its own free list of objects of exactly that size.
// Any free page of memory can be split into a set of objects
// of one size class, which are then managed using free list
// allocators.
//
// The allocator's data structures are:
//
//	FixAlloc: a free-list allocator for fixed-size objects,
//		used to manage storage used by the allocator.
//	MHeap: the malloc heap, managed at page (4096-byte) granularity.
//	MSpan: a run of pages managed by the MHeap.
//	MCentral: a shared free list for a given size class.
//	MCache: a per-thread (in Go, per-P) cache for small objects.
//	MStats: allocation statistics.
//
// Allocating a small object proceeds up a hierarchy of caches:
//
//	1. Round the size up to one of the small size classes
//	   and look in the corresponding MCache free list.
//	   If the list is not empty, allocate an object from it.
//	   This can all be done without acquiring a lock.
//
//	2. If the MCache free list is empty, replenish it by
//	   taking a bunch of objects from the MCentral free list.
//	   Moving a bunch amortizes the cost of acquiring the MCentral lock.
//
//	3. If the MCentral free list is empty, replenish it by
//	   allocating a run of pages from the MHeap and then
//	   chopping that memory into objects of the given size.
//	   Allocating many objects amortizes the cost of locking
//	   the heap.
//
//	4. If the MHeap is empty or has no page runs large enough,
//	   allocate a new group of pages (at least 1MB) from the
//	   operating system.  Allocating a large run of pages
//	   amortizes the cost of talking to the operating system.
//
// Freeing a small object proceeds up the same hierarchy:
//
//	1. Look up the size class for the object and add it to
//	   the MCache free list.
//
//	2. If the MCache free list is too long or the MCache has
//	   too much memory, return some to the MCentral free lists.
//
//	3. If all the objects in a given span have returned to
//	   the MCentral list, return that span to the page heap.
//
//	4. If the heap has too much memory, return some to the
//	   operating system.
//
//	TODO(rsc): Step 4 is not implemented.
//
// Allocating and freeing a large object uses the page heap
// directly, bypassing the MCache and MCentral free lists.
//
// The small objects on the MCache and MCentral free lists
// may or may not be zeroed.  They are zeroed if and only if
// the second word of the object is zero.  A span in the
// page heap is zeroed unless s->needzero is set. When a span
// is allocated to break into small objects, it is zeroed if needed
// and s->needzero is set. There are two main benefits to delaying the
// zeroing this way:
//
//	1. stack frames allocated from the small object lists
//	   or the page heap can avoid zeroing altogether.
//	2. the cost of zeroing when reusing a small object is
//	   charged to the mutator, not the garbage collector.
//
// This code was written with an eye toward translating to Go
// in the future.  Methods have the form Type_Method(Type *t, ...).

package runtime

import "unsafe"

const (
	debugMalloc = false

	flagNoScan = _FlagNoScan // 1 << 0
	flagNoZero = _FlagNoZero // 1 << 1

	maxTinySize   = _TinySize      // 16
	tinySizeClass = _TinySizeClass // 2
	maxSmallSize  = _MaxSmallSize  // 32K

	pageShift = _PageShift // 13
	pageSize  = _PageSize  // 1 << pageShift = 1 << 13 = 8K
	pageMask  = _PageMask  // pageSize - 1

	mSpanInUse = _MSpanInUse // 0

	concurrentSweep = _ConcurrentSweep // true
)

const (
	_PageShift = 13
	_PageSize  = 1 << _PageShift
	_PageMask  = _PageSize - 1
)

const (
	// _64bit = 1 on 64-bit systems, 0 on 32-bit systems
	_64bit = 1 << (^uintptr(0) >> 63) / 2 // 1

	// Computed constant.  The definition of MaxSmallSize and the
	// algorithm in msize.go produces some number of different allocation
	// size classes.  NumSizeClasses is that number.  It's needed here
	// because there are static arrays of this length; when msize runs its
	// size choosing algorithm it double-checks that NumSizeClasses agrees.
	_NumSizeClasses = 67

	// Tunable constants.
	_MaxSmallSize = 32 << 10 // 32K

	// Tiny allocator parameters, see "Tiny allocator" comment in malloc.go.
	_TinySize      = 16
	_TinySizeClass = 2

	_FixAllocChunk = 16 << 10               // Chunk size for FixAlloc
	_MaxMHeapList  = 1 << (20 - _PageShift) // 128, Maximum page length for fixed-size list in MHeap.
	// heap 从操作系统申请内存时，最少申请 1M
	_HeapAllocChunk = 1 << 20 // 1M, Chunk size for heap growth

	// Per-P, per order stack segment cache size.
	_StackCacheSize = 32 * 1024 // 32K

	// Number of orders that get caching.  Order 0 is FixedStack
	// and each successive order is twice as large.
	// We want to cache 2KB, 4KB, 8KB, and 16KB stacks.  Larger stacks
	// will be allocated directly.
	// Since FixedStack is different on different systems, we
	// must vary NumStackOrders to keep the same maximum cached size.
	//   OS               | FixedStack | NumStackOrders
	//   -----------------+------------+---------------
	//   linux/darwin/bsd | 2KB        | 4
	//   windows/32       | 4KB        | 3
	//   windows/64       | 8KB        | 2
	//   plan9            | 4KB        | 3
	_NumStackOrders = 4 - ptrSize/4*goos_windows - 1*goos_plan9

	// Number of bits in page to span calculations (4k pages).
	// On Windows 64-bit we limit the arena to 32GB or 35 bits.
	// Windows counts memory used by page table into committed memory
	// of the process, so we can't reserve too much memory.
	// See https://golang.org/issue/5402 and https://golang.org/issue/5236.
	// On other 64-bit platforms, we limit the arena to 512GB, or 39 bits.
	// On 32-bit, we don't bother limiting anything, so we use the full 32-bit address.
	// On Darwin/arm64, we cannot reserve more than ~5GB of virtual memory,
	// but as most devices have less than 4GB of physical memory anyway, we
	// try to be conservative here, and only ask for a 2GB heap.
	_MHeapMap_TotalBits = (_64bit*goos_windows)*35 + (_64bit*(1-goos_windows)*(1-goos_darwin*goarch_arm64))*39 + goos_darwin*goarch_arm64*31 + (1-_64bit)*32
	_MHeapMap_Bits      = _MHeapMap_TotalBits - _PageShift

	_MaxMem = uintptr(1<<_MHeapMap_TotalBits - 1) // 512GB

	// Max number of threads to run garbage collection.
	// 2, 3, and 4 are all plausible maximums depending
	// on the hardware details of the machine.  The garbage
	// collector scales well to 32 cpus.
	_MaxGcproc = 32
)

// Page number (address>>pageShift)
type pageID uintptr

const _MaxArena32 = 2 << 30

// OS-defined helpers:
//
// sysAlloc obtains a large chunk of zeroed memory from the
// operating system, typically on the order of a hundred kilobytes
// or a megabyte.
// NOTE: sysAlloc returns OS-aligned memory, but the heap allocator
// may use larger alignment, so the caller must be careful to realign the
// memory obtained by sysAlloc.
//
// SysUnused notifies the operating system that the contents
// of the memory region are no longer needed and can be reused
// for other purposes.
// SysUsed notifies the operating system that the contents
// of the memory region are needed again.
//
// SysFree returns it unconditionally; this is only used if
// an out-of-memory error has been detected midway through
// an allocation.  It is okay if SysFree is a no-op.
//
// SysReserve reserves address space without allocating memory.
// If the pointer passed to it is non-nil, the caller wants the
// reservation there, but SysReserve can still choose another
// location if that one is unavailable.  On some systems and in some
// cases SysReserve will simply check that the address space is
// available and not actually reserve it.  If SysReserve returns
// non-nil, it sets *reserved to true if the address space is
// reserved, false if it has merely been checked.
// NOTE: SysReserve returns OS-aligned memory, but the heap allocator
// may use larger alignment, so the caller must be careful to realign the
// memory obtained by sysAlloc.
//
// SysMap maps previously reserved address space for use.
// The reserved argument is true if the address space was really
// reserved, not merely checked.
//
// SysFault marks a (already sysAlloc'd) region to fault
// if accessed.  Used only for debugging the runtime.

func mallocinit() {

	// 就是初始化 size 相关的几个数组，这几个数组跟据系统不同而不同，所以不能在代码中写死。
	initSizes()

	// TinySizeClass = 2, _TinySize = 16.
	if class_to_size[_TinySizeClass] != _TinySize {
		throw("bad TinySizeClass")
	}

	var p, bitmapSize, spansSize, pSize, limit uintptr
	var reserved bool

	// limit = runtime.memlimit();
	// See https://golang.org/issue/5049
	// TODO(rsc): Fix after 1.1.
	limit = 0

	// Set up the allocation arena, a contiguous area of memory where
	// allocated data will be found.  The arena begins with a bitmap large
	// enough to hold 4 bits per allocated word.
	if ptrSize == 8 && (limit == 0 || limit > 1<<30) {
		// On a 64-bit machine, allocate from a single contiguous reservation.
		// 512 GB (MaxMem) should be big enough for now.
		//
		// The code will work with the reservation at any address, but ask
		// SysReserve to use 0x0000XXc000000000 if possible (XX=00...7f).
		// Allocating a 512 GB region takes away 39 bits, and the amd64
		// doesn't let us choose the top 17 bits, so that leaves the 9 bits
		// in the middle of 0x00c0 for us to choose.  Choosing 0x00c0 means
		// that the valid memory addresses will begin 0x00c0, 0x00c1, ..., 0x00df.
		// In little-endian, that's c0 00, c1 00, ..., df 00. None of those are valid
		// UTF-8 sequences, and they are otherwise as far away from
		// ff (likely a common byte) as possible.  If that fails, we try other 0xXXc0
		// addresses.  An earlier attempt to use 0x11f8 caused out of memory errors
		// on OS X during thread allocations.  0x00c0 causes conflicts with
		// AddressSanitizer which reserves all memory up to 0x0100.
		// These choices are both for debuggability and to reduce the
		// odds of a conservative garbage collector (as is still used in gccgo)
		// not collecting memory because some non-pointer block of memory
		// had a bit pattern that matched a memory address.
		//
		// Actually we reserve 544 GB (because the bitmap ends up being 32 GB)
		// but it hardly matters: e0 00 is not valid UTF-8 either.
		//
		// If this fails we fall back to the 32 bit memory mechanism
		//
		// However, on arm64, we ignore all this advice above and slam the
		// allocation at 0x40 << 32 because when using 4k pages with 3-level
		// translation buffers, the user address space is limited to 39 bits
		// On darwin/arm64, the address space is even smaller.
		arenaSize := round(_MaxMem, _PageSize) // 512G

		// arena 中的每个字(8byte)都要有 4位的标志位。
		// bitmapSize 空间用来存放标志位，来表示 512G arena的每个字的标志。
		// 下面这个表达式不好理解，转换一下, arenaSize / ptrSize * 4 / 8
		// arenaSize 总共 arenaSize / ptrSize 个字，每个字需要 4bit
		// 所以总共需要 arenaSize / ptrSize * 4 位来存放这些标志
		// 而这些位除以8就是字节数了，所以
		// arenaSize / ptrSize * 4 / 8 = arenaSize / (ptrSize * 8 / 4) = 32G
		bitmapSize = arenaSize / (ptrSize * 8 / 4) // 32G

		// spanSize用来存放所有 span 的地址
		// arena 可以放下 arenaSize / _PageSize 个 span
		// 每个 span 的地址需要 ptrSize 大小空间来存。
		spansSize = arenaSize / _PageSize * ptrSize // 512M
		spansSize = round(spansSize, _PageSize)     // 512M
		for i := 0; i <= 0x7f; i++ {
			switch {
			case GOARCH == "arm64" && GOOS == "darwin":
				p = uintptr(i)<<40 | uintptrMask&(0x0013<<28)
			case GOARCH == "arm64":
				p = uintptr(i)<<40 | uintptrMask&(0x0040<<32)
			default:
				p = uintptr(i)<<40 | uintptrMask&(0x00c0<<32)
			}

			// 总共申请内存大小, 32G + 512M + 512G + 8K = 544.5G
			pSize = bitmapSize + spansSize + arenaSize + _PageSize

			// 申请连续地址空间, sysReserve 对不同的操作系统进行了封装
			p = uintptr(sysReserve(unsafe.Pointer(p), pSize, &reserved))
			if p != 0 {
				break
			}
		}
	}

	// ...
	// 这里删掉了针对 32位系统的处理代码

	// PageSize can be larger than OS definition of page size,
	// so SysReserve can give us a PageSize-unaligned pointer.
	// To overcome this we ask for PageSize more and round up the pointer.
	p1 := round(p, _PageSize)
	//
	//      +         +                 +                                          +
	//      |  512M   |      32G        |                     512G                 |
	//      +----------------------------------------------------------------------+
	//      |  span   |     bitmap      |                arena                     |
	//      +----------------------------------------------------------------------+
	//      ^         ^                 ^                 ^                        ^
	// mheap.spans  mheap.bitmap   mheap.arena_start     mheap.arena_used       mheap.arena_end

	mheap_.spans = (**mspan)(unsafe.Pointer(p1))
	mheap_.bitmap = p1 + spansSize
	mheap_.arena_start = p1 + (spansSize + bitmapSize)
	mheap_.arena_used = mheap_.arena_start
	mheap_.arena_end = p + pSize
	mheap_.arena_reserved = reserved

	if mheap_.arena_start&(_PageSize-1) != 0 {
		println("bad pagesize", hex(p), hex(p1), hex(spansSize), hex(bitmapSize), hex(_PageSize), "start", hex(mheap_.arena_start))
		throw("misrounded allocation in mallocinit")
	}

	// 初始化 mheap 结构中的其他字段
	mHeap_Init(&mheap_, spansSize)
	_g_ := getg()
	_g_.m.mcache = allocmcache()
}

// sysReserveHigh reserves space somewhere high in the address space.
// sysReserve doesn't actually reserve the full amount requested on
// 64-bit systems, because of problems with ulimit. Instead it checks
// that it can get the first 64 kB and assumes it can grab the rest as
// needed. This doesn't work well with the "let the kernel pick an address"
// mode, so don't do that. Pick a high address instead.
func sysReserveHigh(n uintptr, reserved *bool) unsafe.Pointer {
	if ptrSize == 4 {
		return sysReserve(nil, n, reserved)
	}

	for i := 0; i <= 0x7f; i++ {
		p := uintptr(i)<<40 | uintptrMask&(0x00c0<<32)
		*reserved = false
		p = uintptr(sysReserve(unsafe.Pointer(p), n, reserved))
		if p != 0 {
			return unsafe.Pointer(p)
		}
	}

	return sysReserve(nil, n, reserved)
}

// 在 arena区间的 used 内存扩充(增加) n。并对 span 和 bitmap 区间相应的进行设置。
func mHeap_SysAlloc(h *mheap, n uintptr) unsafe.Pointer {

	// 要扩充的 n 已经超过 arena 整个空间，这在 64 位系统上是不太可能的，毕竟 500G 内存空间啊。
	if n > uintptr(h.arena_end)-uintptr(h.arena_used) {
		// We are in 32-bit mode, maybe we didn't use all possible address space yet.
		// Reserve some more space.
		p_size := round(n+_PageSize, 256<<20)
		new_end := h.arena_end + p_size // 扩充后 arena_end 指向的内存地址
		if new_end <= h.arena_start+_MaxArena32 {
			// TODO: It would be bad if part of the arena
			// is reserved and part is not.
			var reserved bool
			p := uintptr(sysReserve((unsafe.Pointer)(h.arena_end), p_size, &reserved))
			if p == h.arena_end {
				h.arena_end = new_end
				h.arena_reserved = reserved
			} else if p+p_size <= h.arena_start+_MaxArena32 {
				// Keep everything page-aligned.
				// Our pages are bigger than hardware pages.
				h.arena_end = p + p_size
				used := p + (-uintptr(p) & (_PageSize - 1))
				mHeap_MapBits(h, used)
				mHeap_MapSpans(h, used)
				h.arena_used = used
				h.arena_reserved = reserved
			} else {
				var stat uint64
				sysFree((unsafe.Pointer)(p), p_size, &stat)
			}
		}
	}

	// 其实核心就在这个 if 语句里，其他的都是各种异常的判断
	if n <= uintptr(h.arena_end)-uintptr(h.arena_used) {
		// Keep taking from our reservation.
		p := h.arena_used
		sysMap((unsafe.Pointer)(p), n, h.arena_reserved, &memstats.heap_sys)
		mHeap_MapBits(h, p+n)  // 更新 bitmap 信息
		mHeap_MapSpans(h, p+n) // 更新 span 信息
		h.arena_used = p + n

		if uintptr(p)&(_PageSize-1) != 0 {
			throw("misrounded allocation in MHeap_SysAlloc")
		}
		return (unsafe.Pointer)(p)
	}

	// If using 64-bit, our reservation is all we have.
	if uintptr(h.arena_end)-uintptr(h.arena_start) >= _MaxArena32 {
		return nil
	}

	// On 32-bit, once the reservation is gone we can
	// try to get memory at a location chosen by the OS
	// and hope that it is in the range we allocated bitmap for.
	p_size := round(n, _PageSize) + _PageSize
	p := uintptr(sysAlloc(p_size, &memstats.heap_sys))
	if p == 0 {
		return nil
	}

	if p < h.arena_start || uintptr(p)+p_size-uintptr(h.arena_start) >= _MaxArena32 {
		print("runtime: memory allocated by OS (", p, ") not in usable range [", hex(h.arena_start), ",", hex(h.arena_start+_MaxArena32), ")\n")
		sysFree((unsafe.Pointer)(p), p_size, &memstats.heap_sys)
		return nil
	}

	p_end := p + p_size
	p += -p & (_PageSize - 1)
	if uintptr(p)+n > uintptr(h.arena_used) {
		mHeap_MapBits(h, p+n)
		mHeap_MapSpans(h, p+n)
		h.arena_used = p + n
		if p_end > h.arena_end {
			h.arena_end = p_end
		}
		if raceenabled {
			racemapshadow((unsafe.Pointer)(p), n)
		}
	}

	if uintptr(p)&(_PageSize-1) != 0 {
		throw("misrounded allocation in MHeap_SysAlloc")
	}
	return (unsafe.Pointer)(p)
}

// base address for all 0-byte allocations
var zerobase uintptr

const (
	// flags to malloc
	_FlagNoScan = 1 << 0 // GC doesn't have to scan object
	_FlagNoZero = 1 << 1 // don't zero memory
)

// Allocate an object of size bytes.
// Small objects are allocated from the per-P cache's free lists.
// Large objects (> 32 kB) are allocated straight from the heap.
func mallocgc(size uintptr, typ *_type, flags uint32) unsafe.Pointer {

	// 申请的 0 大小空间的内存
	if size == 0 {
		return unsafe.Pointer(&zerobase)
	}

	// Set mp.mallocing to keep from being preempted by GC.
	// 获取线程 M，
	mp := acquirem()
	if mp.mallocing != 0 {
		throw("malloc deadlock")
	}
	if mp.gsignal == getg() {
		throw("malloc during signal")
	}
	mp.mallocing = 1

	shouldhelpgc := false
	dataSize := size

	// 当前 goroutine 所在线程 M 的 mcache，尝试从 cache 中获取内存空间
	c := gomcache()
	var s *mspan
	var x unsafe.Pointer
	// 空间较小的内存申请, 小于 32k
	if size <= maxSmallSize {
		// 如果申请的是 tiny 大小的对象，也就是小于 16 字节
		if flags&flagNoScan != 0 && size < maxTinySize {
			// Tiny allocator.
			//
			// Tiny allocator combines several tiny allocation requests
			// into a single memory block. The resulting memory block
			// is freed when all subobjects are unreachable. The subobjects
			// must be FlagNoScan (don't have pointers), this ensures that
			// the amount of potentially wasted memory is bounded. // 保证潜在的内存浪费被限制。
			//
			// Size of the memory block used for combining (maxTinySize) is tunable.
			// Current setting is 16 bytes, which relates to 2x worst case memory
			// wastage (when all but one subobjects are unreachable).
			// 8 bytes would result in no wastage at all, but provides less
			// opportunities for combining.
			// 32 bytes provides more opportunities for combining,
			// but can lead to 4x worst case wastage.
			// The best case winning is 8x regardless of block size.
			//
			// Objects obtained from tiny allocator must not be freed explicitly.
			// So when an object will be freed explicitly, we ensure that
			// its size >= maxTinySize.
			//
			// SetFinalizer has a special case for objects potentially coming
			// from tiny allocator, it such case it allows to set finalizers
			// for an inner byte of a memory block.
			//
			// The main targets of tiny allocator are small strings and
			// standalone escaping variables. On a json benchmark
			// the allocator reduces number of allocations by ~12% and
			// reduces heap size by ~20%.
			off := c.tinyoffset
			// Align tiny pointer for required (conservative) alignment.
			// 根据 size 的大小确定分配多少字节
			if size&7 == 0 { // 大于等于 8B
				off = round(off, 8)
			} else if size&3 == 0 { // 大于等于 4B
				off = round(off, 4)
			} else if size&1 == 0 { // 大于等于 2B
				off = round(off, 2)
			}
			// tiny 这个 span 中有足够的空间申请，
			if off+size <= maxTinySize && c.tiny != nil {
				// The object fits into existing tiny block.
				x = add(c.tiny, off)
				c.tinyoffset = off + size
				c.local_tinyallocs++
				mp.mallocing = 0
				releasem(mp)
				return x
			}
			// Allocate a new maxTinySize block.
			// tiny 空间不够，从 span 列表中申请一个过来给 tiny
			s = c.alloc[tinySizeClass]
			v := s.freelist
			if v.ptr() == nil { // 这个 span 已经用不了了，是空的
				systemstack(func() {
					mCache_Refill(c, tinySizeClass) // 冲新填充 mcache 的 span 列表
				})
				shouldhelpgc = true
				s = c.alloc[tinySizeClass]
				v = s.freelist
			}
			s.freelist = v.ptr().next
			s.ref++
			// prefetchnta offers best performance, see change list message.
			prefetchnta(uintptr(v.ptr().next))
			x = unsafe.Pointer(v)
			// 下面两句相当于置0了。tinySize是16byte，也就是长度为2的uint64的数组，都置成0，相当于 memset 了
			(*[2]uint64)(x)[0] = 0
			(*[2]uint64)(x)[1] = 0
			// See if we need to replace the existing tiny block with the new one
			// based on amount of remaining free space.
			// 如果 size 小于 c.tinyoffset，就是说块 span 还有额外的空间可用于下次分配
			// 如果 size >= c.tinyoffset 说明整块都给这个 tiny 对象用了，就不复制给 c.tiny 了，因为赋值了也没用
			if size < c.tinyoffset {
				c.tiny = x
				c.tinyoffset = size
			}
			size = maxTinySize
		} else {
			// 不是 tiny 类型的，直接从 alloc 表里面取一个适当大小的 span
			// 整体逻辑和上面的 tiny 差不多
			var sizeclass int8
			// 根据 size 的大小，确定需要的 sizeclass
			if size <= 1024-8 {
				sizeclass = size_to_class8[(size+7)>>3]
			} else {
				sizeclass = size_to_class128[(size-1024+127)>>7]
			}

			size = uintptr(class_to_size[sizeclass])
			s = c.alloc[sizeclass]
			v := s.freelist
			if v.ptr() == nil { // span 没有空间了
				systemstack(func() {
					mCache_Refill(c, int32(sizeclass)) // 重新填充这个 sizeclass 的span
				})
				shouldhelpgc = true
				s = c.alloc[sizeclass]
				v = s.freelist
			}
			s.freelist = v.ptr().next
			s.ref++
			// prefetchnta offers best performance, see change list message.
			prefetchnta(uintptr(v.ptr().next))
			x = unsafe.Pointer(v)
			if flags&flagNoZero == 0 { // 这个flag表示，是否对新拿到的内存清0。
				v.ptr().next = 0
				if size > 2*ptrSize && ((*[2]uintptr)(x))[1] != 0 {
					memclr(unsafe.Pointer(v), size)
				}
			}
		}
		c.local_cachealloc += size
	} else {
		// 大于 32K，是大对象
		var s *mspan
		shouldhelpgc = true
		systemstack(func() {
			s = largeAlloc(size, uint32(flags))
		})
		x = unsafe.Pointer(uintptr(s.start << pageShift))
		size = uintptr(s.elemsize)
	}

	// 到这里内存分配就结束了，分配的结果就是变量 x
	// 下面的代码主要和 gc，debug，race 有关。
	if flags&flagNoScan != 0 {
		// All objects are pre-marked as noscan. Nothing to do.
	} else {
		// If allocating a defer+arg block, now that we've picked a malloc size
		// large enough to hold everything, cut the "asked for" size down to
		// just the defer header, so that the GC bitmap will record the arg block
		// as containing nothing at all (as if it were unused space at the end of
		// a malloc block caused by size rounding).
		// The defer arg areas are scanned as part of scanstack.
		if typ == deferType {
			dataSize = unsafe.Sizeof(_defer{})
		}
		heapBitsSetType(uintptr(x), size, dataSize, typ)
		if dataSize > typ.size {
			// Array allocation. If there are any
			// pointers, GC has to scan to the last
			// element.
			if typ.ptrdata != 0 {
				c.local_scan += dataSize - typ.size + typ.ptrdata
			}
		} else {
			c.local_scan += typ.ptrdata
		}

		// Ensure that the stores above that initialize x to
		// type-safe memory and set the heap bits occur before
		// the caller can make x observable to the garbage
		// collector. Otherwise, on weakly ordered machines,
		// the garbage collector could follow a pointer to x,
		// but see uninitialized memory or stale heap bits.
		publicationBarrier()
	}

	// GCmarkterminate allocates black
	// All slots hold nil so no scanning is needed.
	// This may be racing with GC so do it atomically if there can be
	// a race marking the bit.
	if gcphase == _GCmarktermination || gcBlackenPromptly {
		systemstack(func() {
			gcmarknewobject_m(uintptr(x), size)
		})
	}

	mp.mallocing = 0
	releasem(mp)

	if shouldhelpgc && shouldtriggergc() {
		startGC(gcBackgroundMode, false)
	} else if gcBlackenEnabled != 0 {
		// Assist garbage collector. We delay this until the
		// epilogue so that it doesn't interfere with the
		// inner working of malloc such as mcache refills that
		// might happen while doing the gcAssistAlloc.
		gcAssistAlloc(size, shouldhelpgc)
	} else if shouldhelpgc && bggc.working != 0 {
		// The GC is starting up or shutting down, so we can't
		// assist, but we also can't allocate unabated. Slow
		// down this G's allocation and help the GC stay
		// scheduled by yielding.
		//
		// TODO: This is a workaround. Either help the GC make
		// the transition or block.
		gp := getg()
		if gp != gp.m.g0 && gp.m.locks == 0 && gp.m.preemptoff == "" {
			Gosched()
		}
	}

	return x
}

// 为大对象(>=32K)申请 size 大小的内存空间
func largeAlloc(size uintptr, flag uint32) *mspan {
	// print("largeAlloc size=", size, "\n")

	if size+_PageSize < size {
		throw("out of memory")
	}
	npages := size >> _PageShift // 需要多少页
	if size&_PageMask != 0 {
		npages++
	}

	// Deduct credit for this span allocation and sweep if
	// necessary. mHeap_Alloc will also sweep npages, so this only
	// pays the debt down to npage pages.
	deductSweepCredit(npages*_PageSize, npages)
	// 直接从 heap 里拿
	s := mHeap_Alloc(&mheap_, npages, 0, true, flag&_FlagNoZero == 0)
	if s == nil {
		throw("out of memory")
	}
	// 限制这块儿内存的使用界限。因为虽申请的是 size 大小，而实际 s 的内存可能要大于 size 的。所以这里限定以下。多出 size 部分的内存不能用。
	s.limit = uintptr(s.start)<<_PageShift + size
	heapBitsForSpan(s.base()).initSpan(s.layout())
	return s
}

// implementation of new builtin
func newobject(typ *_type) unsafe.Pointer {
	flags := uint32(0)
	if typ.kind&kindNoPointers != 0 {
		flags |= flagNoScan
	}
	return mallocgc(uintptr(typ.size), typ, flags)
}

//go:linkname reflect_unsafe_New reflect.unsafe_New
func reflect_unsafe_New(typ *_type) unsafe.Pointer {
	return newobject(typ)
}

// implementation of make builtin for slices
func newarray(typ *_type, n uintptr) unsafe.Pointer {
	flags := uint32(0)
	if typ.kind&kindNoPointers != 0 {
		flags |= flagNoScan
	}
	if int(n) < 0 || (typ.size > 0 && n > _MaxMem/uintptr(typ.size)) {
		panic("runtime: allocation size out of range")
	}
	return mallocgc(uintptr(typ.size)*n, typ, flags)
}

//go:linkname reflect_unsafe_NewArray reflect.unsafe_NewArray
func reflect_unsafe_NewArray(typ *_type, n uintptr) unsafe.Pointer {
	return newarray(typ, n)
}

// rawmem returns a chunk of pointerless memory.  It is
// not zeroed.
func rawmem(size uintptr) unsafe.Pointer {
	return mallocgc(size, nil, flagNoScan|flagNoZero)
}

func profilealloc(mp *m, x unsafe.Pointer, size uintptr) {
	c := mp.mcache
	rate := MemProfileRate
	if size < uintptr(rate) {
		// pick next profile time
		// If you change this, also change allocmcache.
		if rate > 0x3fffffff { // make 2*rate not overflow
			rate = 0x3fffffff
		}
		next := int32(fastrand1()) % (2 * int32(rate))
		// Subtract the "remainder" of the current allocation.
		// Otherwise objects that are close in size to sampling rate
		// will be under-sampled, because we consistently discard this remainder.
		next -= (int32(size) - c.next_sample)
		if next < 0 {
			next = 0
		}
		c.next_sample = next
	}

	mProf_Malloc(x, size)
}

type persistentAlloc struct {
	base unsafe.Pointer
	off  uintptr
}

var globalAlloc struct {
	mutex
	persistentAlloc
}

// Wrapper around sysAlloc that can allocate small chunks.
// There is no associated free operation.
// Intended for things like function/type/debug-related persistent data.
// If align is 0, uses default align (currently 8).
func persistentalloc(size, align uintptr, sysStat *uint64) unsafe.Pointer {
	var p unsafe.Pointer
	systemstack(func() {
		p = persistentalloc1(size, align, sysStat)
	})
	return p
}

// Must run on system stack because stack growth can (re)invoke it.
// See issue 9174.
//go:systemstack
func persistentalloc1(size, align uintptr, sysStat *uint64) unsafe.Pointer {
	const (
		chunk    = 256 << 10
		maxBlock = 64 << 10 // VM reservation granularity is 64K on windows
	)

	if size == 0 {
		throw("persistentalloc: size == 0")
	}
	if align != 0 {
		if align&(align-1) != 0 {
			throw("persistentalloc: align is not a power of 2")
		}
		if align > _PageSize {
			throw("persistentalloc: align is too large")
		}
	} else {
		align = 8
	}

	if size >= maxBlock {
		return sysAlloc(size, sysStat)
	}

	mp := acquirem()
	var persistent *persistentAlloc
	if mp != nil && mp.p != 0 {
		persistent = &mp.p.ptr().palloc
	} else {
		lock(&globalAlloc.mutex)
		persistent = &globalAlloc.persistentAlloc
	}
	persistent.off = round(persistent.off, align)
	if persistent.off+size > chunk || persistent.base == nil {
		persistent.base = sysAlloc(chunk, &memstats.other_sys)
		if persistent.base == nil {
			if persistent == &globalAlloc.persistentAlloc {
				unlock(&globalAlloc.mutex)
			}
			throw("runtime: cannot allocate memory")
		}
		persistent.off = 0
	}
	p := add(persistent.base, persistent.off)
	persistent.off += size
	releasem(mp)
	if persistent == &globalAlloc.persistentAlloc {
		unlock(&globalAlloc.mutex)
	}

	if sysStat != &memstats.other_sys {
		mSysStatInc(sysStat, size)
		mSysStatDec(&memstats.other_sys, size)
	}
	return p
}
