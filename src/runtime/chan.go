// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package runtime

// This file contains the implementation of Go channels.

// Invariants:
//  At least one of c.sendq and c.recvq is empty,
//  except for the case of an unbuffered channel with a single goroutine
//  blocked on it for both sending and receiving using a select statement,
//  in which case the length of c.sendq and c.recvq is limited only by the
//  size of the select statement.
//
// For buffered channels, also:
//  c.qcount > 0 implies that c.recvq is empty.
//  c.qcount < c.dataqsiz implies that c.sendq is empty.

import (
	"runtime/internal/atomic"
	"runtime/internal/math"
	"unsafe"
)

const (
	maxAlign  = 8
	hchanSize = unsafe.Sizeof(hchan{}) + uintptr(-int(unsafe.Sizeof(hchan{}))&(maxAlign-1))
	debugChan = false
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

	// lock protects all fields in hchan, as well as several
	// fields in sudogs blocked on this channel.
	//
	// Do not change another G's status while holding this lock
	// (in particular, do not ready a G), as this can deadlock
	// with stack shrinking.
	lock mutex
}

type waitq struct {
	first *sudog
	last  *sudog
}

//go:linkname reflect_makechan reflect.makechan
func reflect_makechan(t *chantype, size int) *hchan {
	return makechan(t, size)
}

func makechan64(t *chantype, size int64) *hchan {
	if int64(int(size)) != size {
		panic(plainError("makechan: size out of range"))
	}

	return makechan(t, int(size))
}

func makechan(t *chantype, size int) *hchan {
	elem := t.elem

	// compiler checks this but be safe.
	// 编译器的检查, 元素的大小, 以及基本的校验
	if elem.size >= 1<<16 {
		throw("makechan: invalid channel element type")
	}
	if hchanSize%maxAlign != 0 || elem.align > maxAlign {
		throw("makechan: bad alignment")
	}

	mem, overflow := math.MulUintptr(elem.size, uintptr(size))
	if overflow || mem > maxAlloc-hchanSize || size < 0 {
		panic(plainError("makechan: size out of range"))
	}

	// Hchan does not contain pointers interesting for GC when elements stored in buf do not contain pointers.
	// buf points into the same allocation, elemtype is persistent.
	// SudoG's are referenced from their owning thread so they can't be collected.
	// TODO(dvyukov,rlh): Rethink when collector can move allocated objects.
	// 当存储在buf中的元素不包含指针时, hchan将不包含GC感兴趣的指针. buf指向相同的分配, elemtype是可持久化的.
	// sudog 从它们自己的线程中引用, 因此无法将其收集.
	var c *hchan
	switch {
	case mem == 0:
		// Queue or element size is zero.
		// elem.size*size 结果为0, 要么是 elem.size 为0, 要么是创建的size为0
		// 此时只分配 hchan 大小的内存.
		c = (*hchan)(mallocgc(hchanSize, nil, true))
		// Race detector uses this location for synchronization.
		c.buf = c.raceaddr()
	case elem.ptrdata == 0:
		// Elements do not contain pointers.
		// Allocate hchan and buf in one call.
		// elem 当中不包含指针. hchan和buf的地址是连续的. 此时分配 hchanSize + mem
		c = (*hchan)(mallocgc(hchanSize+mem, nil, true))
		c.buf = add(unsafe.Pointer(c), hchanSize)
	default:
		// Elements contain pointers.
		// elem 包含指针, 两次内存操作. hchan 和 buf的地址是不连续的
		c = new(hchan)
		c.buf = mallocgc(mem, elem, true)
	}

	c.elemsize = uint16(elem.size)
	c.elemtype = elem
	c.dataqsiz = uint(size)
	lockInit(&c.lock, lockRankHchan)

	if debugChan {
		print("makechan: chan=", c, "; elemsize=", elem.size, "; dataqsiz=", size, "\n")
	}
	return c
}

// chanbuf(c, i) is pointer to the i'th slot in the buffer.
func chanbuf(c *hchan, i uint) unsafe.Pointer {
	return add(c.buf, uintptr(i)*uintptr(c.elemsize))
}

// full reports whether a send on c would block (that is, the channel is full).
// It uses a single word-sized read of mutable state, so although
// the answer is instantaneously true, the correct answer may have changed
// by the time the calling function receives the return value.
func full(c *hchan) bool {
	// c.dataqsiz is immutable (never written after the channel is created)
	// so it is safe to read at any time during channel operation.
	if c.dataqsiz == 0 {
		// Assumes that a pointer read is relaxed-atomic.
		return c.recvq.first == nil
	}
	// Assumes that a uint read is relaxed-atomic.
	return c.qcount == c.dataqsiz
}

// entry point for c <- x from compiled code
//go:nosplit
func chansend1(c *hchan, elem unsafe.Pointer) {
	chansend(c, elem, true, getcallerpc())
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
 */
// 如果 block 不为 true, 则该 protocol 不会休眠
// 当关闭与休眠有关的chan时, 可以使用 g.param == nil 唤醒休眠.
func chansend(c *hchan, ep unsafe.Pointer, block bool, callerpc uintptr) bool {
	if c == nil {
		if !block {
			return false
		}
		gopark(nil, nil, waitReasonChanSendNilChan, traceEvGoStop, 2)
		throw("unreachable")
	}

	if debugChan {
		print("chansend: chan=", c, "\n")
	}

	if raceenabled {
		racereadpc(c.raceaddr(), callerpc, funcPC(chansend))
	}

	// Fast path: check for failed non-blocking operation without acquiring the lock.
	//
	// After observing that the channel is not closed, we observe that the channel is
	// not ready for sending. Each of these observations is a single word-sized read
	// (first c.closed and second full()).
	// Because a closed channel cannot transition from 'ready for sending' to
	// 'not ready for sending', even if the channel is closed between the two observations,
	// they imply a moment between the two when the channel was both not yet closed
	// and not ready for sending. We behave as if we observed the channel at that moment,
	// and report that the send cannot proceed.
	//
	// It is okay if the reads are reordered here: if we observe that the channel is not
	// ready for sending and then observe that it is not closed, that implies that the
	// channel wasn't closed during the first observation. However, nothing here
	// guarantees forward progress. We rely on the side effects of lock release in
	// chanrecv() and closechan() to update this thread's view of c.closed and full().
	// 快速判断: 在非阻塞模式下, 快速检测到失败, 不用获取锁, 快速返回(false)
	//
	// 如果 chan 未关闭且 chan 没有多余的缓冲空间. 这可能是:
	// 1. chan 是非缓冲型的, 且等待接收队列里没有 goroutine
	// 2. chan 是缓冲型的, 但缓冲队列已经装满了元素
	//
	// c.closed == 0, chan 未关闭
	// c.dataqsiz == 0 && c.recvq.first == nil, 非缓冲型 chan, 且 "接收队列(recvq)" 当中没有元素
	// c.dataqsiz > 0 && c.qcount == c.dataqsiz, 缓存型 chan, 且 "缓冲队列(buf)" 已满
	if !block && c.closed == 0 && full(c) {
		return false
	}

	var t0 int64
	if blockprofilerate > 0 {
		t0 = cputicks()
	}

	lock(&c.lock)

	if c.closed != 0 {
		unlock(&c.lock)
		panic(plainError("send on closed channel"))
	}
	//如果有等待的g直接发。 我日，这是不是有点不公平？前面的数据不应该消费？
	// 2021.11.15 上面这是不可能的，sendq和recvxq不会出现同时有数据。所以 这里应该就是有顺序的。
	// 从接收队列当中寻找一个接收者, 直接将当前的内容发送给这个接收者, 绕过缓存区
	if sg := c.recvq.dequeue(); sg != nil {
		// Found a waiting receiver. We pass the value we want to send
		// directly to the receiver, bypassing the channel buffer (if any).
		send(c, sg, ep, func() { unlock(&c.lock) }, 3)
		return true
	}

	if c.qcount < c.dataqsiz {
		// Space is available in the channel buffer. Enqueue the element to send.
		// 扩容
		qp := chanbuf(c, c.sendx)
		if raceenabled {
			racenotify(c, c.sendx, nil)
		}
		// 数据移动
		typedmemmove(c.elemtype, qp, ep)
		// 修正 sendx 和 qcount 变量
		c.sendx++
		if c.sendx == c.dataqsiz {
			c.sendx = 0
		}
		c.qcount++
		unlock(&c.lock)
		return true
	}

	// 当前没有合适的缓冲区来存储发送的元素. 这个时候需要根据 "是否是阻塞发送" 来做出抉择
	// 如果是 "阻塞发送", 那么就需要休眠当前的 goroutine
	// 如果是 "非阻塞发送", 那么就快速失败返回(false)
	if !block {
		unlock(&c.lock)
		return false
	}

	// Block on the channel. Some receiver will complete our operation for us.
	gp := getg()
	mysg := acquireSudog()
	mysg.releasetime = 0
	if t0 != 0 {
		mysg.releasetime = -1
	}
	// No stack splits between assigning elem and enqueuing mysg
	// on gp.waiting where copystack can find it.
	// 在"分配elem"和"将mysg入队到gp.waitcopy可以找到它的地方" 之间没有堆栈拆分.
	mysg.elem = ep
	mysg.waitlink = nil
	mysg.g = gp
	mysg.isSelect = false
	mysg.c = c
	gp.waiting = mysg
	gp.param = nil
	// 将当前的 sudog 入队列 sendq
	c.sendq.enqueue(mysg)
	// Signal to anyone trying to shrink our stack that we're about
	// to park on a channel. The window between when this G's status
	// changes and when we set gp.activeStackChans is not safe for
	// stack shrinking.
	atomic.Store8(&gp.parkingOnChan, 1)
	// 带 lock 休眠的休眠操作, 意味着在 goparkunlock 需要解锁 lock
	gopark(chanparkcommit, unsafe.Pointer(&c.lock), waitReasonChanSend, traceEvGoBlockSend, 2)
	// Ensure the value being sent is kept alive until the
	// receiver copies it out. The sudog has a pointer to the
	// stack object, but sudogs aren't considered as roots of the
	// stack tracer.
	// 确保 "发送的值" 保持活跃状态, 直到接收者将其复制出来. 也就是延长发送的值的生存周期, 防止提前被 GC 回收
	// sudog具有指向堆栈对象的指针, 但是sudog不被视为stack跟踪器的root.
	KeepAlive(ep)

	// someone woke us up.
	if mysg != gp.waiting {
		throw("G waiting list is corrupted")
	}
	gp.waiting = nil
	gp.activeStackChans = false
	closed := !mysg.success
	gp.param = nil
	if mysg.releasetime > 0 {
		blockevent(mysg.releasetime-t0, 2)
	}
	mysg.c = nil
	releaseSudog(mysg)
	if closed {
		// 发现 chan 已经关闭了, 那么发送肯定会存在问题
		if c.closed == 0 {
			throw("chansend: spurious wakeup")
		}
		panic(plainError("send on closed channel"))
	}
	return true
}

// send processes a send operation on an empty channel c.
// The value ep sent by the sender is copied to the receiver sg.
// The receiver is then woken up to go on its merry way.
// Channel c must be empty and locked.  send unlocks c with unlockf.
// sg must already be dequeued from c.
// ep must be non-nil and point to the heap or the caller's stack.
// send 是将发送方发送的ep值复制到接收方sg中(跳过缓冲区). 然后将接收方sg唤醒, 继续执行后续的操作.
//
// chan c 必须为空且已锁定. 使用unlockf()在发送后解锁c.
// sg 必须已经从 recvq 中出队.
// ep 必须为非nil, 并且指向堆或调用者的堆栈.
func send(c *hchan, sg *sudog, ep unsafe.Pointer, unlockf func(), skip int) {
	if raceenabled {
		if c.dataqsiz == 0 {
			racesync(c, sg)
		} else {
			// Pretend we go through the buffer, even though
			// we copy directly. Note that we need to increment
			// the head/tail locations only when raceenabled.
			racenotify(c, c.recvx, nil)
			racenotify(c, c.recvx, sg)
			c.recvx++
			if c.recvx == c.dataqsiz {
				c.recvx = 0
			}
			c.sendx = c.recvx // c.sendx = (c.sendx+1) % c.dataqsiz
		}
	}
	if sg.elem != nil {
		// 直接发送
		sendDirect(c.elemtype, sg, ep)
		sg.elem = nil
	}
	gp := sg.g
	unlockf()
	// 唤醒正在休眠的接收者
	gp.param = unsafe.Pointer(sg)
	sg.success = true
	if sg.releasetime != 0 {
		sg.releasetime = cputicks()
	}
	goready(gp, skip+1)
}

// Sends and receives on unbuffered or empty-buffered channels are the
// only operations where one running goroutine writes to the stack of
// another running goroutine. The GC assumes that stack writes only
// happen when the goroutine is running and are only done by that
// goroutine. Using a write barrier is sufficient to make up for
// violating that assumption, but the write barrier has to work.
// typedmemmove will call bulkBarrierPreWrite, but the target bytes
// are not in the heap, so that will not help. We arrange to call
// memmove and typeBitsBulkBarrier instead.
// 仅在 "一个正在运行的goroutine写入到另一个正在运行的goroutine的stack" 的操作是在 "无缓冲" 或 "空缓冲" chan 上
// 发送和接收.
//
// GC假定 stack 写入仅在goroutine运行时发生, 并且仅由该goroutine完成.
// 使用写屏障足以弥补违反该假设的缺点, 但是写屏障必须起作用.
// typedmemmove 将调用 bulkBarrierPreWrite, 但是目标字节不在 heap 中, 因此这无济于事.
// 因此这里安排调用 memmove 和 typeBitsBulkBarrier.

func sendDirect(t *_type, sg *sudog, src unsafe.Pointer) {
	// src is on our stack, dst is a slot on another stack.

	// Once we read sg.elem out of sg, it will no longer
	// be updated if the destination's stack gets copied (shrunk).
	// So make sure that no preemption points can happen between read & use.
	// src在我们的stack上, dst是另一个stack上的插槽.

	// 一旦我们从sg中读出了sg.elem, 如果目标 stack 被复制(缩小), 它将不再被更新.
	// 因此, 请确保在 read 和 use 之间没有任何抢占点.
	dst := sg.elem
	typeBitsBulkBarrier(t, uintptr(dst), uintptr(src), t.size)
	// No need for cgo write barrier checks because dst is always
	// Go memory.
	memmove(dst, src, t.size)
}

func recvDirect(t *_type, sg *sudog, dst unsafe.Pointer) {
	// dst is on our stack or the heap, src is on another stack.
	// The channel is locked, so src will not move during this
	// operation.
	src := sg.elem
	typeBitsBulkBarrier(t, uintptr(dst), uintptr(src), t.size)
	// 不需要go写屏障检查, 因为dst始终是Go内存.
	memmove(dst, src, t.size)
}

func closechan(c *hchan) {
	// 当前的 chan 为 nil. 关闭自然会报错
	if c == nil {
		panic(plainError("close of nil channel"))
	}

	lock(&c.lock)
	// 重复关闭一个 chan
	if c.closed != 0 {
		unlock(&c.lock)
		panic(plainError("close of closed channel"))
	}

	if raceenabled {
		callerpc := getcallerpc()
		racewritepc(c.raceaddr(), callerpc, funcPC(closechan))
		racerelease(c.raceaddr())
	}

	// 关闭
	c.closed = 1

	// 将所有处于阻塞状态的 g 串在一起. 链接点是 g.schedlink
	var glist gList

	// release all readers
	for {
		sg := c.recvq.dequeue()
		if sg == nil {
			break
		}
		// 清除 sg 当中的元素值
		if sg.elem != nil {
			typedmemclr(c.elemtype, sg.elem)
			sg.elem = nil
		}
		if sg.releasetime != 0 {
			sg.releasetime = cputicks()
		}
		gp := sg.g
		// 关闭的标志之一
		gp.param = unsafe.Pointer(sg)
		sg.success = false
		if raceenabled {
			raceacquireg(gp, c.raceaddr())
		}
		// 将 goroutine 存入 glist
		glist.push(gp)
	}

	// release all writers (they will panic)
	// 释放所有的 sendq (they will panic)
	for {
		sg := c.sendq.dequeue()
		if sg == nil {
			break
		}
		sg.elem = nil
		if sg.releasetime != 0 {
			sg.releasetime = cputicks()
		}
		gp := sg.g
		gp.param = unsafe.Pointer(sg)
		sg.success = false
		if raceenabled {
			raceacquireg(gp, c.raceaddr())
		}
		// 将 goroutine 存入 glist
		glist.push(gp)
	}
	unlock(&c.lock)

	// Ready all Gs now that we've dropped the channel lock.
	// 唤醒 glist 当中所有的 gp. 这样做的好处是减少锁定的时间
	for !glist.empty() {
		gp := glist.pop()
		gp.schedlink = 0
		goready(gp, 3)
	}
}

// empty reports whether a read from c would block (that is, the channel is
// empty).  It uses a single atomic read of mutable state.
func empty(c *hchan) bool {
	// c.dataqsiz is immutable.
	if c.dataqsiz == 0 {
		return atomic.Loadp(unsafe.Pointer(&c.sendq.first)) == nil
	}
	return atomic.Loaduint(&c.qcount) == 0
}

// entry points for <- c from compiled code
// 不带"ok"类型, 例如 val := <-ch
//go:nosplit
func chanrecv1(c *hchan, elem unsafe.Pointer) {
	chanrecv(c, elem, true)
}

// 带"ok"类型, 例如 val, ok := <-ch
//go:nosplit
func chanrecv2(c *hchan, elem unsafe.Pointer) (received bool) {
	_, received = chanrecv(c, elem, true)
	return
}

// chanrecv receives on channel c and writes the received data to ep.
// ep may be nil, in which case received data is ignored.
// If block == false and no elements are available, returns (false, false).
// Otherwise, if c is closed, zeros *ep and returns (true, false).
// Otherwise, fills in *ep with an element and returns (true, true).
// A non-nil ep must point to the heap or the caller's stack.
func chanrecv(c *hchan, ep unsafe.Pointer, block bool) (selected, received bool) {
	// raceenabled: don't need to check ep, as it is always on the stack
	// or is new memory allocated by reflect.

	if debugChan {
		print("chanrecv: chan=", c, "\n")
	}

	// 当前的 chan 为nil, 在非阻塞的状况下, 立即返回 (false,false), 否则阻塞当前的 goroutine 到永远
	if c == nil {
		if !block {
			return
		}
		gopark(nil, nil, waitReasonChanReceiveNilChan, traceEvGoStop, 2)
		throw("unreachable")
	}

	// Fast path: check for failed non-blocking operation without acquiring the lock.
	// 快速判断: 在非阻塞模式下, 快速检测到失败, 不用获取锁, 快速返回(false, false)
	//
	// 当我们观察到 chan 没准备好接收:
	// 1. 非缓冲型, 等待发送队列 sendq 里没有 goroutine 在等待
	// 2. 缓冲型, 在缓冲队列 buf 当中没有元素
	//
	// 之后, 又观察到 closed == 0, 即 chan 关闭了.
	// 由于 chan 不可能被重复打开, 所以前一个观察的时候 chan 也是未关闭的,  因此在这种状况下直接接收失败,
	// 返回 (fasle, false)
	//
	// 这里操作顺序在这里很重要: 在进行近距离追踪时, 反转操作可能导致错误的行为.
	//
	// c.dataqsiz == 0 && c.sendq.first == nil, 非缓冲型chan, 当前的 "发送队列(sendq)" 为空
	// c.dataqsiz > 0 && atomic.Loaduint(&c.qcount) == 0 缓冲型chan, 当前的 "缓冲队列(buf)" 为空
	// atomic.Load(&c.closed) == 0, chan 已关闭
	if !block && empty(c) {
		// After observing that the channel is not ready for receiving, we observe whether the
		// channel is closed.
		//
		// Reordering of these checks could lead to incorrect behavior when racing with a close.
		// For example, if the channel was open and not empty, was closed, and then drained,
		// reordered reads could incorrectly indicate "open and empty". To prevent reordering,
		// we use atomic loads for both checks, and rely on emptying and closing to happen in
		// separate critical sections under the same lock.  This assumption fails when closing
		// an unbuffered channel with a blocked send, but that is an error condition anyway.
		if atomic.Load(&c.closed) == 0 {
			// Because a channel cannot be reopened, the later observation of the channel
			// being not closed implies that it was also not closed at the moment of the
			// first observation. We behave as if we observed the channel at that moment
			// and report that the receive cannot proceed.
			return
		}
		// The channel is irreversibly closed. Re-check whether the channel has any pending data
		// to receive, which could have arrived between the empty and closed checks above.
		// Sequential consistency is also required here, when racing with such a send.
		if empty(c) {
			// The channel is irreversibly closed and empty.
			if raceenabled {
				raceacquire(c.raceaddr())
			}
			if ep != nil {
				typedmemclr(c.elemtype, ep)
			}
			return true, false
		}
	}

	var t0 int64
	if blockprofilerate > 0 {
		t0 = cputicks()
	}
	// 加锁
	lock(&c.lock)

	// 当前 chan 关闭的状况下, 并且"缓存队列(buf)"里面没有元素.
	// 也就是说, 即使是关闭状态, 对于缓冲型的 chan, "缓冲队列(buf)" 里面的元素依旧可以被接收到(qcount>0).
	if c.closed != 0 && c.qcount == 0 {
		if raceenabled {
			raceacquire(c.raceaddr())
		}
		unlock(&c.lock)
		if ep != nil {
			// 根据类型清理相应的内存
			typedmemclr(c.elemtype, ep)
		}
		return true, false
	}

	// 阻塞的 "发送队列(sendq)" 当中存在 sender. 则说明当前的缓冲队列已满.
	// 可能的状况:
	// 1. 非缓冲型的 chan
	// 2. 缓冲型的 chan, 但 buf 已经满了
	// 针对1, 直接内存拷贝
	// 针对2, 接收到 buf 的头元素(recvx), 并将发送者的元素放到 buf 的尾部(sendx) (这里sendx和recvx其实值是
	// 一样的), 然后唤醒休眠的发送者.
	if sg := c.sendq.dequeue(); sg != nil {
		// Found a waiting sender. If buffer is size 0, receive value
		// directly from sender. Otherwise, receive from head of queue
		// and add sender's value to the tail of the queue (both map to
		// the same buffer slot because the queue is full).
		recv(c, sg, ep, func() { unlock(&c.lock) }, 3)
		return true, true
	}

	// 缓冲型, 当前的缓存队列存在元素
	if c.qcount > 0 {
		// Receive directly from queue
		qp := chanbuf(c, c.recvx)
		if raceenabled {
			racenotify(c, c.recvx, nil)
		}
		//  将 qp 的数据拷贝到 ep
		if ep != nil {
			typedmemmove(c.elemtype, ep, qp)
		}
		// 清除 qp 内容
		typedmemclr(c.elemtype, qp)
		// 修正 recvx 和 qcount 的值
		c.recvx++
		if c.recvx == c.dataqsiz {
			c.recvx = 0
		}
		c.qcount--
		unlock(&c.lock)
		return true, true
	}

	// 当前缓队列没有任何元素, 隐含着 "发送队列(sendq)为空".
	// 非阻塞状况下(block为false), 快速返回 (false, false)
	// 阻塞状况下(block为true), 休眠当前的 goroutine
	if !block {
		unlock(&c.lock)
		return false, false
	}

	// no sender available: block on this channel.
	gp := getg()
	mysg := acquireSudog()
	mysg.releasetime = 0
	if t0 != 0 {
		mysg.releasetime = -1
	}
	// No stack splits between assigning elem and enqueuing mysg
	// on gp.waiting where copystack can find it.
	mysg.elem = ep
	mysg.waitlink = nil
	gp.waiting = mysg
	mysg.g = gp
	mysg.isSelect = false
	mysg.c = c
	gp.param = nil
	// 将当前的 sudog 入接收队列 recvq
	c.recvq.enqueue(mysg)
	// Signal to anyone trying to shrink our stack that we're about
	// to park on a channel. The window between when this G's status
	// changes and when we set gp.activeStackChans is not safe for
	// stack shrinking.
	atomic.Store8(&gp.parkingOnChan, 1)
	// 持有锁的状况下休眠
	gopark(chanparkcommit, unsafe.Pointer(&c.lock), waitReasonChanReceive, traceEvGoBlockRecv, 2)

	// someone woke us up
	if mysg != gp.waiting {
		throw("G waiting list is corrupted")
	}
	gp.waiting = nil
	gp.activeStackChans = false
	if mysg.releasetime > 0 {
		blockevent(mysg.releasetime-t0, 2)
	}
	success := mysg.success
	gp.param = nil
	mysg.c = nil
	releaseSudog(mysg)
	return true, success
}

// recv processes a receive operation on a full channel c.
// There are 2 parts:
// 1) The value sent by the sender sg is put into the channel
//    and the sender is woken up to go on its merry way.
// 2) The value received by the receiver (the current G) is
//    written to ep.
// For synchronous channels, both values are the same.
// For asynchronous channels, the receiver gets its data from
// the channel buffer and the sender's data is put in the
// channel buffer.
// Channel c must be full and locked. recv unlocks c with unlockf.
// sg must already be dequeued from c.
// A non-nil ep must point to the heap or the caller's stack.
// recv 在 full chan(缓冲通道已满或者非缓冲通道) c上处理接收操作.
// 包含2个部分:
// 1) 由发送方 sg 发送的值被放入通道, 并且唤醒发送方以继续执行其后续的逻辑.
// 2) 接收方接收到的值(当前G)被写入 ep.
// 对于同步通道, 两个值相同.
// 对于异步通道, 接收方从通道缓冲区获取其数据, 而发送方的数据放入通道缓冲区.
//
// chan c 必须已满并且已锁定. recv用 unlockf 函数解锁c.
// sg 必须已经从 sendq 中出队列.
// ep 必须为非nil, 并且指向 heap 或调用者的stack.
func recv(c *hchan, sg *sudog, ep unsafe.Pointer, unlockf func(), skip int) {
	// 非缓冲型通道, 或者同步通道.
	if c.dataqsiz == 0 {
		if raceenabled {
			racesync(c, sg)
		}
		if ep != nil {
			// copy data from sender
			// 直接从 sender 复制数据.
			recvDirect(c.elemtype, sg, ep)
		}
	} else {
		// Queue is full. Take the item at the
		// head of the queue. Make the sender enqueue
		// its item at the tail of the queue. Since the
		// queue is full, those are both the same slot.
		// 缓冲型通道, 或者异步通道
		//
		// 先获取 recvx 对应的 slot,
		// 先 slot 当中读取数据到 ep 当中, 然后将 sender 发送的数据再插入到 slot 当中.
		// 由于缓冲队列是满的, 所以经过上述的操作之后, 缓冲队列依旧是满的, 但是 recvx 需要向前移动一位(保证chan的元素
		// 都是先进先出的), 而且 sendx 也是需要向前移动一位. 但是 sendx 和 recvx 的值相等.

		// 获取 slot 的位置
		qp := chanbuf(c, c.recvx)
		if raceenabled {
			racenotify(c, c.recvx, nil)
			racenotify(c, c.recvx, sg)
		}
		// copy data from queue to receiver
		if ep != nil {
			typedmemmove(c.elemtype, ep, qp)
		}
		// copy data from sender to queue
		typedmemmove(c.elemtype, qp, sg.elem)
		// 更新 recvx 和 sendx
		c.recvx++
		if c.recvx == c.dataqsiz {
			c.recvx = 0
		}
		c.sendx = c.recvx // c.sendx = (c.sendx+1) % c.dataqsiz
	}
	// sg 清理工作
	sg.elem = nil
	gp := sg.g
	unlockf()
	// 唤醒对应的发送者
	gp.param = unsafe.Pointer(sg)
	sg.success = true
	if sg.releasetime != 0 {
		sg.releasetime = cputicks()
	}
	goready(gp, skip+1)
}

func chanparkcommit(gp *g, chanLock unsafe.Pointer) bool {
	// There are unlocked sudogs that point into gp's stack. Stack
	// copying must lock the channels of those sudogs.
	// Set activeStackChans here instead of before we try parking
	// because we could self-deadlock in stack growth on the
	// channel lock.
	gp.activeStackChans = true
	// Mark that it's safe for stack shrinking to occur now,
	// because any thread acquiring this G's stack for shrinking
	// is guaranteed to observe activeStackChans after this store.
	atomic.Store8(&gp.parkingOnChan, 0)
	// Make sure we unlock after setting activeStackChans and
	// unsetting parkingOnChan. The moment we unlock chanLock
	// we risk gp getting readied by a channel operation and
	// so gp could continue running before everything before
	// the unlock is visible (even to gp itself).
	unlock((*mutex)(chanLock))
	return true
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
func selectnbsend(c *hchan, elem unsafe.Pointer) (selected bool) {
	return chansend(c, elem, false, getcallerpc())
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
//	if selected, ok = selectnbrecv(&v, c); selected {
//		... foo
//	} else {
//		... bar
//	}
//
func selectnbrecv(elem unsafe.Pointer, c *hchan) (selected, received bool) {
	return chanrecv(c, elem, false)
}

//go:linkname reflect_chansend reflect.chansend
func reflect_chansend(c *hchan, elem unsafe.Pointer, nb bool) (selected bool) {
	return chansend(c, elem, !nb, getcallerpc())
}

//go:linkname reflect_chanrecv reflect.chanrecv
func reflect_chanrecv(c *hchan, nb bool, elem unsafe.Pointer) (selected bool, received bool) {
	return chanrecv(c, elem, !nb)
}

//go:linkname reflect_chanlen reflect.chanlen
func reflect_chanlen(c *hchan) int {
	if c == nil {
		return 0
	}
	return int(c.qcount)
}

//go:linkname reflectlite_chanlen internal/reflectlite.chanlen
func reflectlite_chanlen(c *hchan) int {
	if c == nil {
		return 0
	}
	return int(c.qcount)
}

//go:linkname reflect_chancap reflect.chancap
func reflect_chancap(c *hchan) int {
	if c == nil {
		return 0
	}
	return int(c.dataqsiz)
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

		// if a goroutine was put on this queue because of a
		// select, there is a small window between the goroutine
		// being woken up by a different case and it grabbing the
		// channel locks. Once it has the lock
		// it removes itself from the queue, so we won't see it after that.
		// We use a flag in the G struct to tell us when someone
		// else has won the race to signal this goroutine but the goroutine
		// hasn't removed itself from the queue yet.
		if sgp.isSelect && !atomic.Cas(&sgp.g.selectDone, 0, 1) {
			continue
		}

		return sgp
	}
}

func (c *hchan) raceaddr() unsafe.Pointer {
	// Treat read-like and write-like operations on the channel to
	// happen at this address. Avoid using the address of qcount
	// or dataqsiz, because the len() and cap() builtins read
	// those addresses, and we don't want them racing with
	// operations like close().
	return unsafe.Pointer(&c.buf)
}

func racesync(c *hchan, sg *sudog) {
	racerelease(chanbuf(c, 0))
	raceacquireg(sg.g, chanbuf(c, 0))
	racereleaseg(sg.g, chanbuf(c, 0))
	raceacquire(chanbuf(c, 0))
}

// Notify the race detector of a send or receive involving buffer entry idx
// and a channel c or its communicating partner sg.
// This function handles the special case of c.elemsize==0.
func racenotify(c *hchan, idx uint, sg *sudog) {
	// We could have passed the unsafe.Pointer corresponding to entry idx
	// instead of idx itself.  However, in a future version of this function,
	// we can use idx to better handle the case of elemsize==0.
	// A future improvement to the detector is to call TSan with c and idx:
	// this way, Go will continue to not allocating buffer entries for channels
	// of elemsize==0, yet the race detector can be made to handle multiple
	// sync objects underneath the hood (one sync object per idx)
	qp := chanbuf(c, idx)
	// When elemsize==0, we don't allocate a full buffer for the channel.
	// Instead of individual buffer entries, the race detector uses the
	// c.buf as the only buffer entry.  This simplification prevents us from
	// following the memory model's happens-before rules (rules that are
	// implemented in racereleaseacquire).  Instead, we accumulate happens-before
	// information in the synchronization object associated with c.buf.
	if c.elemsize == 0 {
		if sg == nil {
			raceacquire(qp)
			racerelease(qp)
		} else {
			raceacquireg(sg.g, qp)
			racereleaseg(sg.g, qp)
		}
	} else {
		if sg == nil {
			racereleaseacquire(qp)
		} else {
			racereleaseacquireg(sg.g, qp)
		}
	}
}
