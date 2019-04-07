
sig Process {
	ready : set Time,
	blocked : set Time,
	free : set Time,
	current : set Time
}

one sig NullProcess extends Process {}

sig Time {}

fact {
	all t:Time | NullProcess in ready.t + current.t
}

fact {
	all t : Time | Process = ready.t + blocked.t + free.t + current.t
}

pred inv[t:Time] {
	one current.t
	disj [ready.t, blocked.t, free.t, current.t]
}

run { some t:Time | inv[t] } for 3 but 1 Time

pred Init[t:Time] {

	no ready.t 
	no blocked.t 
	free.t = Process - NullProcess
	current.t = NullProcess
}

check { all t : Time | Init[t] => inv[t] }

run { some t:Time | Init[t] } for 3 but 1 Time

pred Dispatch[t,t':Time, p:Process] {
	p in ready.t
	p != NullProcess

	current.t = NullProcess
	current.t' = p
	ready.t' = ready.t - p + NullProcess 
	blocked.t' = blocked.t
	free.t' = free.t
}

run { some t,t':Time, p:Process | inv[t] and Dispatch[t,t',p] } for 3 but 2 Time

check { all t,t':Time, p:Process | inv[t] and Dispatch[t,t',p] => inv[t'] }

