open Process
open Chain[Process]

sig Time {
	current : lone Process,
	ready : Chain,
	free : Chain,
	blocked : Chain
} {
	ready != free
	ready != blocked
	free != blocked
}

pred inv[t : Time] {
	// the sets and the current process are mutually exclusive
	all p : Process | (t.current = p =>
		Chain_count[t.ready, p].add[
		Chain_count[t.blocked, p].add[
		Chain_count[t.free, p]]] = 0)
	all p : Process | (p != t.current =>
		Chain_count[t.ready, p].add[
		Chain_count[t.blocked, p].add[
		Chain_count[t.free, p]]] = 1)
	// every process is either ready, blocked, free or current
	all p : Process |
		t.current = p
		or Chain_exists[t.ready, p]
		or Chain_exists[t.blocked, p]
		or Chain_exists[t.free, p] 
 }

run RunInv { 
	some t : Time | inv[t] 
} for 4 but 1 Time

pred Init[t : Time] {
	no t.current
	no p : Process | Chain_exists[t.ready, p] 
	no p : Process | Chain_exists[t.blocked, p] 
	all p : Process | Chain_exists[t.free, p]
}

run RunInit { 
	some t : Time | Init[t] 
} for 4 but 1 Time

check CheckInit { 
	all t : Time | Init[t] => inv[t] 
} for 4

pred Create[t, t' : Time, pout : Process] {
	t'.current = t.current
	Chain_pop[t.free, t'.free, pout]
	Chain_push[t.ready, t'.ready, pout]
	Chain_equal[t.blocked, t'.blocked]
}

run RunCreate { 
	some t, t' : Time, p : Process | 
		inv[t] and Create[t, t', p] 
} for 4 but 2 Time

check CheckCreate { 
	all t, t' : Time, p : Process | 
		inv[t] and Create[t, t', p] => inv[t'] 
} for 4 but 2 Time


