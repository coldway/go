// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build amd64 || 386
// +build amd64 386

package runtime

import (
	"runtime/internal/sys"
	"unsafe"
)

// adjust Gobuf as if it executed a call to fn with context ctxt
// and then stopped before the first instruction in fn.
func gostartcall(buf *gobuf, fn, ctxt unsafe.Pointer) {
	sp := buf.sp
	sp -= sys.PtrSize // 为返回地址预留空间
	// buf.pc 存储的是 funcPC(goexit) + sys.PCQuantum
	// 将其存储到返回地址是为了伪造成 fn 是被 goexit 调用的，在 fn 执行完后返回 goexit执行，做一些清理工作。
	*(*uintptr)(unsafe.Pointer(sp)) = buf.pc
	buf.sp = sp				// 重新赋值
	buf.pc = uintptr(fn)	// 赋值为函数指针
	buf.ctxt = ctxt
}
