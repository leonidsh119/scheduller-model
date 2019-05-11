open Process
open Set[Process]

sig Time {
	current : lone Process,
	ready : Set,
	free : Set,
	blocked : Set
} {
	ready != free
	ready != blocked
	free != blocked
}

pred inv[t : Time] {
	// the sets and the current process are mutually exclusive
	all p : Process | (t.current = p =>
		Set_count[t.ready, p].add [
		Set_count[t.blocked, p].add [
		Set_count[t.free, p]]] = 0)
	all p : Process | (p != t.current =>
		Set_count[t.ready, p].add[
		Set_count[t.blocked, p].add[
		Set_count[t.free, p]]] = 1)
	// every process is either ready, blocked, free or current
	all p : Process |
		t.current = p
		or Set_exists[t.ready, p]
		or Set_exists[t.blocked, p]
		or Set_exists[t.free, p]
 }

run RunInv { 
	some t : Time | inv[t] 
} for 4 but 1 Time

pred Init[t : Time] {
	no t.current
	no p : Process | Set_exists[t.ready, p] 
	no p : Process | Set_exists[t.blocked, p] 
	all p : Process | Set_exists[t.free, p]
}

run RunInit { 
	some t : Time | Init[t] 
} for 4 but 1 Time

check CheckInit { 
	all t : Time | Init[t] => inv[t] 
} for 4

pred Create[t, t' : Time, pout : Process] {
	t'.current = t.current
	Set_remove_any[t.free, t'.free, pout]
	Set_add[t.ready, t'.ready, pout]
	Set_equal[t.blocked, t'.blocked]
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
	not Set_empty[t.ready]
	Set_equal[t.blocked, t'.blocked]
	Set_equal[t.free, t'.free]
	Set_remove_any[t.ready, t'.ready, pout]
	t'.current = pout
}

run RunDispatch { 
	some t, t' : Time, pout : Process | 
		inv[t] and Dispatch[t, t', pout] 
} for 4 but 2 Time

check CheckDispatch { 
	all t, t' : Time | 
		Set_empty[t.ready] or 
		some pout : Process | 
			inv[t] and Dispatch[t, t', pout] => inv[t']
} for 4 but 2 Time

pred TimeOut[t, t' : Time, p : Process] {
	t.current = p
	no t'.current 
	Set_add[t.ready, t'.ready, p]
	Set_equal[t'.blocked, t.blocked]
	Set_equal[t'.free, t.free]
}

run RunTimeOut { 
	some t, t' : Time, p : Process | 
		inv[t] and TimeOut[t, t', p] 
} for 4 but 2 Time

check CheckTimeOut { 
	all t, t' : Time, p : Process | 
		inv[t] and TimeOut[t, t', p] => inv[t'] 
} for 4

pred Block[t, t' : Time, p : Process] {
	t.current = p
	no t'.current
	Set_add[t.blocked, t'.blocked, p]
	Set_equal[t'.ready, t.ready]
	Set_equal[t'.free, t.free]
}

run RunBlock { 
	some t, t' : Time, p : Process | 
		inv[t] and Block[t, t', p] 
} for 4 but 2 Time

check CheckBlock {
	all t, t' : Time, p : Process | 
		inv[t] and Block[t, t', p] => inv[t'] 
} for 4

pred WakeUp[t, t' : Time, p : Process] {
	Set_exists[t.blocked, p]
	t'.current = t.current
	Set_add[t.ready, t'.ready, p]
	Set_remove[t.blocked, t'.blocked, p]
	Set_equal[t'.free, t.free]
}

run RunWakeUp { 
	some t, t' : Time, p : Process | 
		inv[t] and WakeUp[t, t', p] 
} for 4 but 2 Time

check CheckWakeUp { 
	all t, t' : Time, p : Process | 
		inv[t] and WakeUp[t, t', p] => inv[t'] 
} for 4

pred DestroyCurrent[t, t' : Time, p : Process] {
	p = t.current
	no t'.current
	Set_equal[t.ready, t'.ready]
	Set_equal[t.blocked, t'.blocked]
	Set_add[t.free, t'.free, t.current]
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
} for 4

pred DestroyReady[t, t' : Time, p : Process] {
	t.current = t'.current
	Set_exists[t.ready, p]
	Set_remove[t.ready, t'.ready, p]
	Set_equal[t.blocked, t'.blocked]
	Set_add[t.free, t'.free, p]
}

run RunDestroyReady { 
	some t, t' : Time, p : Process | 
		inv[t] and DestroyReady[t, t', p]
} for 4 but 2 Time

check CheckDestroyReady { 
	all t, t' : Time | 
		Set_empty[t.ready] or 
		some p : Process |
			inv[t] and DestroyReady[t, t', p] => inv[t'] 
} for 4

pred DestroyBlocked[t, t' : Time, p : Process] {
	t.current = t'.current
	Set_equal[t.ready, t'.ready]
	Set_exists[t.blocked, p]
	Set_remove[t.blocked, t'.blocked, p]
	Set_add[t.free, t'.free, p]
}

run RunDestroyBlocked { 
	some t, t' : Time, p : Process | 
		inv[t] and DestroyBlocked[t, t', p] 
} for 4 but 2 Time

check CheckDestroyBlocked { 
	all t, t' : Time | 
		Set_empty[t.blocked] or 
		some p : Process |
			inv[t] and DestroyBlocked[t, t', p] => inv[t'] 
} for 4

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
		Set_empty[t.blocked] or 
		some p : Process |
			inv[t] and Destroy[t, t', p] => inv[t'] 
} for 4
