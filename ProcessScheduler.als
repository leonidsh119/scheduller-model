module ProcessScheduler
open Process

abstract sig Action {
	currentAction : set Time
}

one sig InitAction, CreateAction, DispatchAction, TimeoutAction, BlockAction, WakeupAction, DestroyReadyAction, DestroyCurrentAction, DestroyBlockedAction extends Action {}

one sig NullProcess extends Process {}

fact {
	all t : Time | Inv[t]
}

pred Inv[t : Time] {
	one p : Process | p.state.t = Current
	some p : Process | p.state.t = Free
	(NullProcess.state.t = Current or NullProcess.state.t = Ready)
}

pred Init[t : Time] {
	all p : Process - NullProcess | p.state.t = Free
	NullProcess.state.t = Current
	currentAction.t = InitAction
}

pred Create[t, t' : Time, p : Process] {
	CreateProcess[t, t', p]
	PreserveStateProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = CreateAction
}

pred Dispatch[t, t' : Time, p : Process] {
	DispatchProcess[t, t', p]
	TimeoutProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = DispatchAction
}

pred Timeout[t, t' : Time, p : Process] {
	TimeoutProcess[t, t', p]
	DispatchProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = TimeoutAction
}

pred Block[t, t' : Time, p : Process] {
	BlockProcess[t, t', p]
	DispatchProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = BlockAction
}

pred Wakeup[t, t' : Time, p : Process] {
	WakeupProcess[t, t', p]
	TimeoutProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = WakeupAction
}

pred DestroyReady[t, t' : Time, p : Process] {
	DestroyReadyProcess[t, t', p]
	PreserveStateProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = DestroyReadyAction
}

pred DestroyCurrent[t, t' : Time, p : Process] {
	DestroyCurrentProcess[t, t', p]
	DispatchProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = DestroyCurrentAction
}

pred DestroyBlocked[t, t' : Time, p : Process] {
	DestroyBlockedProcess[t, t', p]
	PreserveStateProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = DestroyBlockedAction
}

pred	PreserveState[t, t' : Time, p : Process] {
	all other : Process - NullProcess - p | PreserveStateProcess[t, t', other]
}

pred PerformSomeAction[t, t' : Time] {
	some p : Process |
		Create[t, t', p]
		or Dispatch[t, t', p]
		or Timeout[t, t', p]
		or Block[t, t', p]
		or Wakeup[t, t', p]
		or DestroyReady[t, t', p]
		or DestroyCurrent[t, t', p]
		or DestroyBlocked[t, t', p]
}

run {
	Init[first]
	all t, t' : Time | t -> t' in next => PerformSomeAction[t, t']
} for 5  but 9 Action, 10 Time

check { 
	all t : Time | Init[t] => Inv[t]
}
