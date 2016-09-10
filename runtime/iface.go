// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package runtime

import "unsafe"

const (
	hashSize = 1009
)

var (
	ifaceLock mutex // lock for accessing hash
	hash      [hashSize]*itab
)

// fInterface is our standard non-empty interface.  We use it instead
// of interface{f()} in function prototypes because gofmt insists on
// putting lots of newlines in the otherwise concise interface{f()}.
type fInterface interface {
	f()
}

// 参数 canfail 是应对 yy, ok := xx.(inter) 的句型。这种情况下 canfail 是 true，表示允许失败不必panic。
func getitab(inter *interfacetype, typ *_type, canfail bool) *itab {
	if len(inter.mhdr) == 0 {
		throw("internal error - misuse of itab")
	}

	// easy case
	x := typ.x
	if x == nil {
		if canfail {
			return nil
		}
		panic(&TypeAssertionError{"", *typ._string, *inter.typ._string, *inter.mhdr[0].name})
	}

	// compiler has provided some good hash codes for us.
	// 类型的 hash 值是在编译时计算好的
	h := inter.typ.hash
	h += 17 * typ.hash
	// TODO(rsc): h += 23 * x.mhash ?
	h %= hashSize

	// look twice - once without lock, once with.
	// common case will be no lock contention.
	var m *itab
	var locked int
	// 在 hash 表中找到 itab，itab 相当于 interface 类型和一个类型实体的合体。
	// 以 bytes.Buffer 和 io.Reader 为例, 当 bytes.Buffer 要转换成类型 io.Reader 使用时
	// 就要找到这俩类型的 itab。
	//
	// 这里对 hash 表进行两次查找，第一次不带锁，如果没找到，对 hash 表加锁进行第二次查找。
	// 因为，如果每一次查找都对 hash 表加锁，对于并发而言，这无疑是个灾难。
	// 但如果 hash 表中找不到，需要对两个类型进行匹配，匹配成功创建新的 itab，匹配成功了对 hash 表进行修改，这时的修改就要加锁操作了。
	//
	// 加锁后再找以便，是因为有可能，在第二次循环开始前，其他 goroutine 对这个 hash 表进行了改写操作。所以锁后再找一便。
	for locked = 0; locked < 2; locked++ {
		if locked != 0 {
			lock(&ifaceLock)
		}
		for m = (*itab)(atomicloadp(unsafe.Pointer(&hash[h]))); m != nil; m = m.link {
			if m.inter == inter && m._type == typ {
				if m.bad != 0 {
					// 这种情况只有，之前匹配过，但没成功，而且当时 canfail = true 时，才会出现。
					// 所以多次执行 _, ok := xx.(some_interface)，并不会每次都重新匹配，hash 表里已经对这种情况进行了 cache
					// 但 yy := xx.(some_interface) 这种情况，就会每次都对两个类型进行匹配，这就对性能很伤了。
					m = nil
					if !canfail { // 不允许失败，进行重新匹配。
						// this can only happen if the conversion
						// was already done once using the , ok form
						// and we have a cached negative result.
						// the cached result doesn't record which
						// interface function was missing, so jump
						// down to the interface check, which will
						// do more work but give a better error.
						goto search
					}
				}
				if locked != 0 {
					unlock(&ifaceLock)
				}
				return m
			}
		}
	}

	// itab 没有找到，新建一个 itab。这里是为 itab 类型申请内存空间
	m = (*itab)(persistentalloc(unsafe.Sizeof(itab{})+uintptr(len(inter.mhdr)-1)*ptrSize, 0, &memstats.other_sys))
	m.inter = inter
	m._type = typ

search:
	// both inter and typ have method sorted by name,
	// and interface names are unique,
	// so can iterate over both in lock step;
	// the loop is O(ni+nt) not O(ni*nt).
	//
	// 对两个类型中的 method 进行匹配，就是看 interface 中所有 method 是否在 这个 type 中都存在(子集)。
	// 因为在编译时，编译器对 interface 和某类型下的 method 进行了排序(根据方法名)。所以这种匹配的复杂度是O(ni+nt)，而不是O(ni*nt)
	ni := len(inter.mhdr)
	nt := len(x.mhdr)
	j := 0
	for k := 0; k < ni; k++ {
		i := &inter.mhdr[k]
		iname := i.name
		ipkgpath := i.pkgpath
		itype := i._type
		for ; j < nt; j++ {
			t := &x.mhdr[j]
			if t.mtyp == itype && (t.name == iname || *t.name == *iname) && t.pkgpath == ipkgpath {
				if m != nil {
					*(*unsafe.Pointer)(add(unsafe.Pointer(&m.fun[0]), uintptr(k)*ptrSize)) = t.ifn
				}
				goto nextimethod
			}
		}
		// didn't find method
		// interface 中的某一个函数，在这个类型中没有找到对应的 method，表示匹配失败了。
		if !canfail { // 匹配失败，不允许失败，直接 panic。
			if locked != 0 {
				unlock(&ifaceLock)
			}
			panic(&TypeAssertionError{"", *typ._string, *inter.typ._string, *iname})
		}
		// 匹配失败，但允许失败。设置 bad 为 1，并把这个 m 放到 hash 表中。
		m.bad = 1
		break
	nextimethod:
	}
	if locked == 0 {
		throw("invalid itab locking")
	}
	// 把新的 itab 放到 hash 表中
	m.link = hash[h]
	atomicstorep(unsafe.Pointer(&hash[h]), unsafe.Pointer(m))
	unlock(&ifaceLock)
	if m.bad != 0 {
		return nil
	}
	return m
}

func typ2Itab(t *_type, inter *interfacetype, cache **itab) *itab {
	tab := getitab(inter, t, false)
	atomicstorep(unsafe.Pointer(cache), unsafe.Pointer(tab))
	return tab
}

// 普通类型转换成 interface{} 类型
func convT2E(t *_type, elem unsafe.Pointer, x unsafe.Pointer) (e interface{}) {
	ep := (*eface)(unsafe.Pointer(&e))
	// 参以下 eface 的类型, 有一个成员是 data unsafe.Pointer，是一个指向真正数据的指针
	// isDirectIface 就是表示，这个类型能否直接存入指针中，而不是新申请一个内存存数据，再用指针指过去。
	// 也就是，内存空间不大于 unsafe.Pointer 的类型，其数据都可以直接放里面，而对于 slice, map, struct等，就不满足 isDirectIface 了。
	if isDirectIface(t) { // 判断数据是否可以直接存放到interface{}中
		ep._type = t
		typedmemmove(t, unsafe.Pointer(&ep.data), elem)
	} else {
		if x == nil {
			x = newobject(t)
		}
		// TODO: We allocate a zeroed object only to overwrite it with
		// actual data.  Figure out how to avoid zeroing.  Also below in convT2I.
		typedmemmove(t, x, elem) // 新建对象，把数据 copy 过去
		ep._type = t
		ep.data = x // 数据指针指向新数据。
	}
	return
}

// 普通类型转成 interface{...} 类型，于 interface{} 类型不同，这种类型需要查找 itab。
// 参数中会给一个 cache，函数会看 cache 中是否有 itab，如果有就不从 hash 表里找了，如果没有再找，并把查到的 itab 放入 cache 中。、
// 整体上，和转成 interface{} 差不多，只是 interface{} 中存的是 type 类型，interface{...} 中存的是 itab。
func convT2I(t *_type, inter *interfacetype, cache **itab, elem unsafe.Pointer, x unsafe.Pointer) (i fInterface) {
	tab := (*itab)(atomicloadp(unsafe.Pointer(cache)))
	if tab == nil {
		tab = getitab(inter, t, false)
		atomicstorep(unsafe.Pointer(cache), unsafe.Pointer(tab))
	}
	pi := (*iface)(unsafe.Pointer(&i))
	if isDirectIface(t) {
		pi.tab = tab
		typedmemmove(t, unsafe.Pointer(&pi.data), elem)
	} else {
		if x == nil {
			x = newobject(t)
		}
		typedmemmove(t, x, elem)
		pi.tab = tab
		pi.data = x
	}
	return
}

func panicdottype(have, want, iface *_type) {
	haveString := ""
	if have != nil {
		haveString = *have._string
	}
	panic(&TypeAssertionError{*iface._string, haveString, *want._string, ""})
}

// 下面 4 个 assert 函数是用来断言 interface{} 或 interface{...} 是否是某类型的。
func assertI2T(t *_type, i fInterface, r unsafe.Pointer) {
	ip := (*iface)(unsafe.Pointer(&i))
	tab := ip.tab
	if tab == nil {
		panic(&TypeAssertionError{"", "", *t._string, ""})
	}
	if tab._type != t {
		panic(&TypeAssertionError{*tab.inter.typ._string, *tab._type._string, *t._string, ""})
	}
	if r != nil {
		if isDirectIface(t) {
			writebarrierptr((*uintptr)(r), uintptr(ip.data))
		} else {
			typedmemmove(t, r, ip.data)
		}
	}
}

func assertI2T2(t *_type, i fInterface, r unsafe.Pointer) bool {
	ip := (*iface)(unsafe.Pointer(&i))
	tab := ip.tab
	if tab == nil || tab._type != t {
		if r != nil {
			memclr(r, uintptr(t.size))
		}
		return false
	}
	if r != nil {
		if isDirectIface(t) {
			writebarrierptr((*uintptr)(r), uintptr(ip.data))
		} else {
			typedmemmove(t, r, ip.data)
		}
	}
	return true
}

func assertE2T(t *_type, e interface{}, r unsafe.Pointer) {
	ep := (*eface)(unsafe.Pointer(&e))
	if ep._type == nil {
		panic(&TypeAssertionError{"", "", *t._string, ""})
	}
	if ep._type != t {
		panic(&TypeAssertionError{"", *ep._type._string, *t._string, ""})
	}
	if r != nil {
		if isDirectIface(t) {
			writebarrierptr((*uintptr)(r), uintptr(ep.data))
		} else {
			typedmemmove(t, r, ep.data)
		}
	}
}

// The compiler ensures that r is non-nil.
func assertE2T2(t *_type, e interface{}, r unsafe.Pointer) bool {
	ep := (*eface)(unsafe.Pointer(&e))
	if ep._type != t {
		memclr(r, uintptr(t.size))
		return false
	}
	if isDirectIface(t) {
		writebarrierptr((*uintptr)(r), uintptr(ep.data))
	} else {
		typedmemmove(t, r, ep.data)
	}
	return true
}

// interface{...} 转换成 interface{}
func convI2E(i fInterface) (r interface{}) {
	ip := (*iface)(unsafe.Pointer(&i))
	tab := ip.tab
	if tab == nil {
		return
	}
	rp := (*eface)(unsafe.Pointer(&r))
	rp._type = tab._type
	rp.data = ip.data
	return
}

func assertI2E(inter *interfacetype, i fInterface, r *interface{}) {
	ip := (*iface)(unsafe.Pointer(&i))
	tab := ip.tab
	if tab == nil {
		// explicit conversions require non-nil interface value.
		panic(&TypeAssertionError{"", "", *inter.typ._string, ""})
	}
	rp := (*eface)(unsafe.Pointer(r))
	rp._type = tab._type
	rp.data = ip.data
	return
}

// The compiler ensures that r is non-nil.
func assertI2E2(inter *interfacetype, i fInterface, r *interface{}) bool {
	ip := (*iface)(unsafe.Pointer(&i))
	tab := ip.tab
	if tab == nil {
		return false
	}
	rp := (*eface)(unsafe.Pointer(r))
	rp._type = tab._type
	rp.data = ip.data
	return true
}

// interface{...} 之间的转换
func convI2I(inter *interfacetype, i fInterface) (r fInterface) {
	ip := (*iface)(unsafe.Pointer(&i))
	tab := ip.tab
	if tab == nil {
		return
	}
	rp := (*iface)(unsafe.Pointer(&r))
	if tab.inter == inter {
		rp.tab = tab
		rp.data = ip.data
		return
	}
	rp.tab = getitab(inter, tab._type, false)
	rp.data = ip.data
	return
}

func assertI2I(inter *interfacetype, i fInterface, r *fInterface) {
	ip := (*iface)(unsafe.Pointer(&i))
	tab := ip.tab
	if tab == nil {
		// explicit conversions require non-nil interface value.
		panic(&TypeAssertionError{"", "", *inter.typ._string, ""})
	}
	rp := (*iface)(unsafe.Pointer(r))
	if tab.inter == inter {
		rp.tab = tab
		rp.data = ip.data
		return
	}
	rp.tab = getitab(inter, tab._type, false)
	rp.data = ip.data
}

func assertI2I2(inter *interfacetype, i fInterface, r *fInterface) bool {
	ip := (*iface)(unsafe.Pointer(&i))
	tab := ip.tab
	if tab == nil {
		if r != nil {
			*r = nil
		}
		return false
	}
	if tab.inter != inter {
		tab = getitab(inter, tab._type, true)
		if tab == nil {
			if r != nil {
				*r = nil
			}
			return false
		}
	}
	if r != nil {
		rp := (*iface)(unsafe.Pointer(r))
		rp.tab = tab
		rp.data = ip.data
	}
	return true
}

func assertE2I(inter *interfacetype, e interface{}, r *fInterface) {
	ep := (*eface)(unsafe.Pointer(&e))
	t := ep._type
	if t == nil {
		// explicit conversions require non-nil interface value.
		panic(&TypeAssertionError{"", "", *inter.typ._string, ""})
	}
	rp := (*iface)(unsafe.Pointer(r))
	rp.tab = getitab(inter, t, false)
	rp.data = ep.data
}

var testingAssertE2I2GC bool

func assertE2I2(inter *interfacetype, e interface{}, r *fInterface) bool {
	if testingAssertE2I2GC {
		GC()
	}
	ep := (*eface)(unsafe.Pointer(&e))
	t := ep._type
	if t == nil {
		if r != nil {
			*r = nil
		}
		return false
	}
	tab := getitab(inter, t, true)
	if tab == nil {
		if r != nil {
			*r = nil
		}
		return false
	}
	if r != nil {
		rp := (*iface)(unsafe.Pointer(r))
		rp.tab = tab
		rp.data = ep.data
	}
	return true
}

//go:linkname reflect_ifaceE2I reflect.ifaceE2I
func reflect_ifaceE2I(inter *interfacetype, e interface{}, dst *fInterface) {
	assertE2I(inter, e, dst)
}

func assertE2E(inter *interfacetype, e interface{}, r *interface{}) {
	ep := (*eface)(unsafe.Pointer(&e))
	if ep._type == nil {
		// explicit conversions require non-nil interface value.
		panic(&TypeAssertionError{"", "", *inter.typ._string, ""})
	}
	*r = e
}

// The compiler ensures that r is non-nil.
func assertE2E2(inter *interfacetype, e interface{}, r *interface{}) bool {
	ep := (*eface)(unsafe.Pointer(&e))
	if ep._type == nil {
		*r = nil
		return false
	}
	*r = e
	return true
}

// interface{...} 所表示的实际类型的 hash 值
func ifacethash(i fInterface) uint32 {
	ip := (*iface)(unsafe.Pointer(&i))
	tab := ip.tab
	if tab == nil {
		return 0
	}
	return tab._type.hash
}

// interface{} 所表示的实际类型的 hash 值
func efacethash(e interface{}) uint32 {
	ep := (*eface)(unsafe.Pointer(&e))
	t := ep._type
	if t == nil {
		return 0
	}
	return t.hash
}

func iterate_itabs(fn func(*itab)) {
	for _, h := range &hash {
		for ; h != nil; h = h.link {
			fn(h)
		}
	}
}
