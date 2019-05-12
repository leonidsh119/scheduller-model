module CScheduler

open Process
open Chain[Process]

sig Time {
	current : lone Process,
	ready : Chain,
	free : Chain,
	blocked : Chain
}

pred inv[t : Time] {
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

run RunInv { 
	some t : Time | inv[t] 
} for 4 but 1 Time

pred Init[t : Time] {
	no t.current
	Empty[t.ready] 
	Empty[t.blocked]
	all p : Process | Exists[t.free, p]
	Inv[t.ready]
	Inv[t.free]
	Inv[t.blocked]
}

run RunInit { 
	some t : Time | Init[t] 
} for 4 but 1 Time

check CheckInit { 
	all t : Time | Init[t] => inv[t] 
} for 4 but 1 Time

pred Create[t, t' : Time, pout : Process] {
	t'.current = t.current
	Exists[t.free, pout]
	RemoveAny[t.free, t'.free, pout]
	Add[t.ready, t'.ready, pout]
	Equals[t.blocked, t'.blocked]
}

run RunCreate { 
	some t, t' : Time, p : Process | 
		inv[t] and Create[t, t', p] 
} for 4 but 2 Time

check CheckCreate { 
	all t, t' : Time, p : Process |
		inv[t] and Create[t, t', p] => inv[t']
} for 4 but 2 Time

pred Dispatch[t, t' : Time, pout : Process] {
	no t.current 
	Exists[t.ready, pout]
	Equals[t.blocked, t'.blocked]
	Equals[t.free, t'.free]
	RemoveAny[t.ready, t'.ready, pout]
	t'.current = pout
}

run RunDispatch { 
	some t, t' : Time, pout : Process | 
		inv[t] and Dispatch[t, t', pout] 
} for 4 but 2 Time

check CheckDispatch { 
	all t, t' : Time, pout : Process | 
		inv[t] and Dispatch[t, t', pout] => inv[t']
} for 4 but 2 Time

pred TimeOut[t, t' : Time, p : Process] {
	t.current = p
	no t'.current 
	Add[t.ready, t'.ready, p]
	Equals[t'.blocked, t.blocked]
	Equals[t'.free, t.free]
}

run RunTimeOut { 
	some t, t' : Time, p : Process | 
		inv[t] and TimeOut[t, t', p] 
} for 4 but 2 Time

check CheckTimeOut { 
	all t, t' : Time, p : Process | 
		inv[t] and TimeOut[t, t', p] => inv[t'] 
} for 4 but 2 Time

pred Block[t, t' : Time, p : Process] {
	t.current = p
	no t'.current
	Add[t.blocked, t'.blocked, p]
	Equals[t'.ready, t.ready]
	Equals[t'.free, t.free]
}

run RunBlock { 
	some t, t' : Time, p : Process | 
		inv[t] and Block[t, t', p] 
} for 4 but 2 Time

check CheckBlock {
	all t, t' : Time, p : Process | 
		inv[t] and Block[t, t', p] => inv[t'] 
} for 4 but 2 Time

pred WakeUp[t, t' : Time, p : Process] {
	t'.current = t.current
	Exists[t.blocked, p]
	Add[t.ready, t'.ready, p]
	Remove[t.blocked, t'.blocked, p]
	Equals[t'.free, t.free]
}

run RunWakeUp { 
	some t, t' : Time, p : Process | 
		inv[t] and WakeUp[t, t', p] 
} for 4 but 2 Time

check CheckWakeUp { 
	all t, t' : Time, p : Process | 
		inv[t] and WakeUp[t, t', p] => inv[t'] 
} for 4 but 2 Time

pred DestroyCurrent[t, t' : Time, p : Process] {
	p = t.current
	no t'.current
	Equals[t.ready, t'.ready]
	Equals[t.blocked, t'.blocked]
	Add[t.free, t'.free, t.current]
}

run RunDestroyCurrent { 
	some t, t' : Time, p : Process | 
		inv[t] and DestroyCurrent[t, t', p] 
} for 4 but 2 Time

check CheckDestroyCurrent { 
	all t, t' : Time | 
		no t'.current or
		some p : Process | 
			inv[t] and DestroyCurrent[t, t', p] => inv[t'] 
} for 4 but 2 Time

pred DestroyReady[t, t' : Time, p : Process] {
	t.current = t'.current
	Exists[t.ready, p]
	Remove[t.ready, t'.ready, p]
	Equals[t.blocked, t'.blocked]
	Add[t.free, t'.free, p]
}

run RunDestroyReady { 
	some t, t' : Time, p : Process | 
		inv[t] and DestroyReady[t, t', p]
} for 4 but 2 Time

check CheckDestroyReady { 
	all t, t' : Time | 
		Empty[t.ready] or 
		some p : Process |
			inv[t] and DestroyReady[t, t', p] => inv[t'] 
} for 4 but 2 Time

pred DestroyBlocked[t, t' : Time, p : Process] {
	t.current = t'.current
	Equals[t.ready, t'.ready]
	Exists[t.blocked, p]
	Remove[t.blocked, t'.blocked, p]
	Add[t.free, t'.free, p]
}

run RunDestroyBlocked { 
	some t, t' : Time, p : Process | 
		inv[t] and DestroyBlocked[t, t', p] 
} for 4 but 2 Time

check CheckDestroyBlocked { 
	all t, t' : Time | 
		Empty[t.blocked] or 
		some p : Process |
			inv[t] and DestroyBlocked[t, t', p] => inv[t'] 
} for 4 but 2 Time

pred Destroy[t, t' : Time, p : Process] {
	DestroyCurrent[t, t', p] or
	DestroyReady[t, t', p] or
	DestroyBlocked[t, t', p] 
}

run RunDestroy { 
	some t, t' : Time, p : Process | 
		inv[t] and Destroy[t, t', p] 
} for 4 but 2 Time

check CheckDestroy { 
	all t, t' : Time | 
		Empty[t.blocked] or 
		some p : Process |
			inv[t] and Destroy[t, t', p] => inv[t'] 
} for 4 but 2 Time
