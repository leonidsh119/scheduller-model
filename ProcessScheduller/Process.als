module scheduler
open util/ordering[Time]

sig Time {}

abstract sig PState {}

one sig Free, Ready, Current, Blocked extends PState {}

abstract sig Process {
	state : PState one -> Time
}

pred P_Create[t, t' : Time, p : Process] {
	p.state.t = Free
	p.state.t' = Ready
}

pred P_Dispatch[t, t' : Time, p : Process] {
	p.state.t = Ready
	p.state.t' = Current
}

pred P_Timeout[t, t' : Time, p : Process] {
	p.state.t = Current
	p.state.t' = Ready
}

pred P_Block[t, t' : Time, p : Process] {
	p.state.t = Current
	p.state.t' = Blocked
}

pred P_Wakeup[t, t' : Time, p : Process] {
	p.state.t = Blocked
	p.state.t' = Ready
}

pred P_DestroyReady[t, t' : Time, p : Process] {
	p.state.t = Ready
	p.state.t' = Free
}

pred P_DestroyCurrent[t, t' : Time, p : Process] {
	p.state.t = Blocked
	p.state.t' = Free
}

pred P_DestroyBlocked[t, t' : Time, p : Process] {
	p.state.t = Current
	p.state.t' = Free
}

pred P_PreserveState[t, t' : Time, p : Process] {
	p.state.t' = p.state.t
}
