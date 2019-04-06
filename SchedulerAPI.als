
sig Process {}

one sig NullProcess extends Process {}

abstract sig Set { items : Process }

pred Set_exists[s: Set, p : Process] {
	Set_count[s, p] = 1
}

fun Set_count[s:Set, p : Process] : Int {
	#(p <: s.items)
}

sig Time {
	ready : Set,
	free : Set,
	blocked : Set,
	current : Set
}

fact {
	all t:Time | 
		Set_exists[t.ready, NullProcess] or 
		Set_exists[t.current, NullProcess] 
}

fact {
	all t : Time | 
		all p : Process |
			Set_exists[t.ready,p] or
			Set_exists[t.blocked,p] or
			Set_exists[t.free,p] or
			Set_exists[t.current,p]
}

pred inv[t:Time] {

	one p : Process | Set_exists[t.current,p]

	all p : Process | 
			Set_count[t.ready,p].add [
			Set_count[t.blocked,p].add [
			Set_count[t.free,p].add [
			Set_count[t.current,p] ] ] ] = 1
}

run { some t:Time | inv[t] } for 4 but 1 Time

pred Init[t:Time] {

	no p : Process | Set_exists[t.ready, p] 
	no p : Process | Set_exists[t.blocked, p] 
	all p : Process - NullProcess | Set_exists[t.free, p]
	Set_exists[t.current, NullProcess]
}

check { all t : Time | Init[t] => inv[t] } for 4

run { some t:Time | Init[t] } for 4 but 1 Time

pred Dispatch[t,t':Time, p:Process] {
	Set_exists[t.ready, p]
	p != NullProcess

	Set_exists[t.current, NullProcess]	

	not Set_exists[t'.current, NullProcess]
	Set_exists[t'.current, p]

	all q : Process - p | 
		Set_exists[t.ready, q] implies Set_exists[t'.ready, q]

	not Set_exists[t'.ready, p]
	Set_exists[t'.ready, NullProcess]
 
	blocked.t' = blocked.t
	free.t' = free.t
}

run { some t,t':Time, p:Process | inv[t] and Dispatch[t,t',p] } for 3 but 2 Time

check { all t,t':Time, p:Process | inv[t] and Dispatch[t,t',p] => inv[t'] }
