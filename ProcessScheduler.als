module ProcessScheduler
open Process

abstract sig Action {
	currentAction : set Time
}

one sig InitAction, CreateAction, DispatchAction, TimeoutAction, BlockAction, WakeupAction, DestroyReadyAction, DestroyCurrentAction, DestroyBlockedAction extends Action {}

sig CProcess extends Process {}

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
	all p : CProcess | p.state.t = Free
	NullProcess.state.t = Current
	currentAction.t = InitAction
}

pred Create[t, t' : Time, p : CProcess] {
	CreateProcess[t, t', p]
	PreserveStateProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = CreateAction
}

pred Dispatch[t, t' : Time, p : CProcess] {
	DispatchProcess[t, t', p]
	TimeoutProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = DispatchAction
}

pred Timeout[t, t' : Time, p : CProcess] {
	TimeoutProcess[t, t', p]
	DispatchProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = TimeoutAction
}

pred Block[t, t' : Time, p : CProcess] {
	BlockProcess[t, t', p]
	DispatchProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = BlockAction
}

pred Wakeup[t, t' : Time, p : CProcess] {
	WakeupProcess[t, t', p]
	TimeoutProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = WakeupAction
}

pred DestroyReady[t, t' : Time, p : CProcess] {
	DestroyReadyProcess[t, t', p]
	PreserveStateProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = DestroyReadyAction
}

pred DestroyCurrent[t, t' : Time, p : CProcess] {
	DestroyCurrentProcess[t, t', p]
	DispatchProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = DestroyCurrentAction
}

pred DestroyBlocked[t, t' : Time, p : CProcess] {
	DestroyBlockedProcess[t, t', p]
	PreserveStateProcess[t, t', NullProcess]
	PreserveState[t, t', p]
	currentAction.t' = DestroyBlockedAction
}

pred	PreserveState[t, t' : Time, p : CProcess] {
	all other : CProcess - p | PreserveStateProcess[t, t', other]
}

pred PerformSomeAction[t, t' : Time] {
	some p : CProcess |
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
