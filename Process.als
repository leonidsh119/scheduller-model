module Process
open util/ordering[Time]

sig Time {}

abstract sig PState {}

one sig Free, Ready, Current, Blocked extends PState {}

sig Process {
	state : PState one -> Time
}

pred CreateProcess[t, t' : Time, p : Process] {
	p.state.t = Free
	p.state.t' = Ready
}

pred DispatchProcess[t, t' : Time, p : Process] {
	p.state.t = Ready
	p.state.t' = Current
}

pred TimeoutProcess[t, t' : Time, p : Process] {
	p.state.t = Current
	p.state.t' = Ready
}

pred BlockProcess[t, t' : Time, p : Process] {
	p.state.t = Current
	p.state.t' = Blocked
}

pred WakeupProcess[t, t' : Time, p : Process] {
	p.state.t = Blocked
	p.state.t' = Ready
}

pred DestroyReadyProcess[t, t' : Time, p : Process] {
	p.state.t = Ready
	p.state.t' = Free
}

pred DestroyCurrentProcess[t, t' : Time, p : Process] {
	p.state.t = Blocked
	p.state.t' = Free
}

pred DestroyBlockedProcess[t, t' : Time, p : Process] {
	p.state.t = Current
	p.state.t' = Free
}

pred PreserveStateProcess[t, t' : Time, p : Process] {
	p.state.t' = p.state.t
}
