
open Set[Process]

sig Process {}

sig Time {
	ready : Set,
	free : Set,
	blocked : Set,
	current : lone Process
}

pred inv[t:Time] {

	// the sets and the current process are mutually exclusive

	all p : Process | (t.current = p =>
		Set_count[t.ready,p].add [
		Set_count[t.blocked,p].add [
		Set_count[t.free,p] ] ] = 0)

	all p : Process | (p != t.current =>
		Set_count[t.ready,p].add [
		Set_count[t.blocked,p].add [
		Set_count[t.free,p] ] ] = 1)

	// every process is either ready, blocked, free or current

	all p : Process |
		Set_exists[t.ready,p] or
		Set_exists[t.blocked,p] or
		Set_exists[t.free,p] or
		t.current = p
}

run { some t:Time | inv[t] } for 4 but 1 Time

pred Init[t:Time] {

	no p : Process | Set_exists[t.ready, p] 
	no p : Process | Set_exists[t.blocked, p] 
	all p : Process | Set_exists[t.free, p]
	no t.current 
}

check { all t : Time | Init[t] => inv[t] } for 4

run { some t:Time | Init[t] } for 4 but 1 Time

pred Create[t,t':Time, p :Process] {
	Set_exists[t.free, p]

	Set_remove[t.free, t'.free, p]
	Set_add[t.ready, t'.ready, p]
	
	t'.current = t.current
	Set_equal[t'.blocked, t.blocked]
}

run { 
	some t,t':Time, p:Process | 
		inv[t] and Create[t,t',p] 
} for 4 but 2 Time

check { 
	all t,t':Time, p:Process | 
		inv[t] and Create[t,t',p] => inv[t'] 
} for 4 but 2 Time

pred Dispatch[t,t':Time, p:Process] {

	Set_exists[t.ready, p]
	no t.current 

	t'.current = p
	Set_remove[t.ready, t'.ready, p]
 
	Set_equal[t'.blocked, t.blocked]
	Set_equal[t'.free, t.free]
}

run { 
	some t,t':Time, p:Process | inv[t] and Dispatch[t,t',p] 
} for 4 but 2 Time

check { 
	all t,t':Time, p:Process | 
		inv[t] and Dispatch[t,t',p] => inv[t'] 
} for 4 but 2 Time

pred Timeout[t,t':Time, p:Process] {

	t.current = p

	no t'.current 
	Set_add[t.ready, t'.ready, p]

	Set_equal[t'.blocked, t.blocked]
	Set_equal[t'.free, t.free]
}

run { some t,t':Time, p:Process | inv[t] and Timeout[t,t',p] } for 4 but 2 Time

check { all t,t':Time, p:Process | 
	inv[t] and Timeout[t,t',p] => inv[t'] 
} for 4

pred Block[t,t':Time, p:Process] {
	
	t.current = p

	no t'.current

	Set_add[t.blocked, t'.blocked, p]

	Set_equal[t'.ready, t.ready]
	Set_equal[t'.free, t.free]
}

run { some t,t':Time, p:Process | 
	inv[t] and Block[t,t',p] } for 4 but 2 Time

check { all t,t':Time, p:Process | 
	inv[t] and Block[t,t',p] => inv[t'] 
} for 4

pred WakeUp[t,t':Time, p:Process] {

	Set_exists[t.blocked, p]

	t'.current = t.current

	Set_add[t.ready, t'.ready, p]
	Set_remove[t.blocked, t'.blocked, p]
	Set_equal[t'.free, t.free]
}

run { some t,t':Time, p:Process | 
	inv[t] and WakeUp[t,t',p] } for 4 but 2 Time

check { all t,t':Time, p:Process | 
	inv[t] and WakeUp[t,t',p] => inv[t'] 
} for 4

