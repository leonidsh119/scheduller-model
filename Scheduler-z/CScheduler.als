module CScheduler

open Process
open Chain[Process]

sig Time {
	current : lone Process,
	ready : Chain,
	free : Chain,
	blocked : Chain
}

pred Inv[t : Time] {
	// the sets and the current process are mutually exclusive
	all p : Process | (t.current = p =>
		Count[t.ready, p].add[
		Count[t.blocked, p].add[
		Count[t.free, p]]] = 0)
	all p : Process | (p != t.current =>
		Count[t.ready, p].add[
		Count[t.blocked, p].add[
		Count[t.free, p]]] = 1)
	// every process is either ready, blocked, free or current
	all p : Process |
		t.current = p
		or Exists[t.ready, p]
		or Exists[t.blocked, p]
		or Exists[t.free, p]
	Inv[t.ready]
	Inv[t.free]
	Inv[t.blocked]
}

pred Init[t : Time] {
	no t.current
	Empty[t.ready] 
	Empty[t.blocked]
	all p : Process | Exists[t.free, p]
	Inv[t.ready]
	Inv[t.free]
	Inv[t.blocked]
}

pred Create[t, t' : Time, pout : Process] {
	t'.current = t.current
	Exists[t.free, pout]
	RemoveAny[t.free, t'.free, pout]
	Add[t.ready, t'.ready, pout]
	Equals[t.blocked, t'.blocked]
}

pred Dispatch[t, t' : Time, pout : Process] {
	no t.current 
	Exists[t.ready, pout]
	Equals[t.blocked, t'.blocked]
	Equals[t.free, t'.free]
	RemoveAny[t.ready, t'.ready, pout]
	t'.current = pout
}

pred TimeOut[t, t' : Time, p : Process] {
	t.current = p
	no t'.current 
	Add[t.ready, t'.ready, p]
	Equals[t'.blocked, t.blocked]
	Equals[t'.free, t.free]
}

pred Block[t, t' : Time, p : Process] {
	t.current = p
	no t'.current
	Add[t.blocked, t'.blocked, p]
	Equals[t'.ready, t.ready]
	Equals[t'.free, t.free]
}

pred WakeUp[t, t' : Time, p : Process] {
	t'.current = t.current
	Exists[t.blocked, p]
	Add[t.ready, t'.ready, p]
	Remove[t.blocked, t'.blocked, p]
	Equals[t'.free, t.free]
}

pred DestroyCurrent[t, t' : Time, p : Process] {
	p = t.current
	no t'.current
	Equals[t.ready, t'.ready]
	Equals[t.blocked, t'.blocked]
	Add[t.free, t'.free, t.current]
}

pred DestroyReady[t, t' : Time, p : Process] {
	t.current = t'.current
	Exists[t.ready, p]
	Remove[t.ready, t'.ready, p]
	Equals[t.blocked, t'.blocked]
	Add[t.free, t'.free, p]
}

pred DestroyBlocked[t, t' : Time, p : Process] {
	t.current = t'.current
	Equals[t.ready, t'.ready]
	Exists[t.blocked, p]
	Remove[t.blocked, t'.blocked, p]
	Add[t.free, t'.free, p]
}

pred Destroy[t, t' : Time, p : Process] {
	DestroyCurrent[t, t', p] or
	DestroyReady[t, t', p] or
	DestroyBlocked[t, t', p] 
}
