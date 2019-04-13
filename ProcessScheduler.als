module ProcessScheduler
open Process

abstract sig Action {
	currentAction : set Time
}

one sig InitAction, CreateAction, DispatchAction, TimeoutAction, BlockAction, WakeupAction, DestroyReadyAction, DestroyCurrentAction, DestroyBlockedAction extends Action {}

sig CProcess extends Process {}

one sig NullProcess extends Process {} {
	all t : Time | state.t = Current or state.t = Ready
}

pred Inv[t : Time] {
	one p : Process | p.state.t = Current
}

pred Init[t : Time] {
	all p : CProcess | p.state.t = Free
	NullProcess.state.t = Current
	currentAction.t = InitAction
}

assert InitOK {
	all t' : Time | Init[t'] => Inv[t']
}

check InitOK for 3 but 1 Time

pred Create[t, t' : Time] {
	some p : CProcess {
		CreateProcess[t, t', p]
		PreserveStateProcess[t, t', NullProcess]
		PreserveState[t, t', p]
		currentAction.t' = CreateAction
	}
}

assert CreateOK {
	all t, t' : Time | Inv[t] and Create[t, t'] => Inv[t']
}

check CreateOK for 3 but 2 Time

pred Dispatch[t, t' : Time] {
	some p : CProcess {
		DispatchProcess[t, t', p]
		TimeoutProcess[t, t', NullProcess]
		PreserveState[t, t', p]
		currentAction.t' = DispatchAction
	}
}

assert DispatchOK {
	all t, t' : Time | Inv[t] and Dispatch[t, t'] => Inv[t']
}

check DispatchOK for 3 but 2 Time

pred Timeout[t, t' : Time] {
	some p : CProcess {
		TimeoutProcess[t, t', p]
		DispatchProcess[t, t', NullProcess]
		PreserveState[t, t', p]
		currentAction.t' = TimeoutAction
	}
}

assert TimeoutOK {
	all t, t' : Time | Inv[t] and Timeout[t, t'] => Inv[t']
}

check TimeoutOK for 3 but 2 Time

pred Block[t, t' : Time] {
	some p : CProcess {
		BlockProcess[t, t', p]
		DispatchProcess[t, t', NullProcess]
		PreserveState[t, t', p]
		currentAction.t' = BlockAction
	}
}

assert BlockOK {
	all t, t' : Time | Inv[t] and Block[t, t'] => Inv[t']
}

check BlockOK for 3 but 2 Time

pred Wakeup[t, t' : Time] {
	some p : CProcess {
		WakeupProcess[t, t', p]
		TimeoutProcess[t, t', NullProcess]
		PreserveState[t, t', p]
		currentAction.t' = WakeupAction
	}
}

assert WakeupOK {
	all t, t' : Time | Inv[t] and Wakeup[t, t'] => Inv[t']
}

check WakeupOK for 3 but 2 Time

pred DestroyReady[t, t' : Time] {
	some p : CProcess {
		DestroyReadyProcess[t, t', p]
		PreserveStateProcess[t, t', NullProcess]
		PreserveState[t, t', p]
		currentAction.t' = DestroyReadyAction
	}
}

assert DestroyReadyOK {
	all t, t' : Time | Inv[t] and DestroyReady[t, t'] => Inv[t']
}

check DestroyReadyOK for 3 but 2 Time

pred DestroyCurrent[t, t' : Time] {
	some p : CProcess {
		DestroyCurrentProcess[t, t', p]
		DispatchProcess[t, t', NullProcess]
		PreserveState[t, t', p]
		currentAction.t' = DestroyCurrentAction
	}
}

assert DestroyCurrentOK {
	all t, t' : Time | Inv[t] and DestroyCurrent[t, t'] => Inv[t']
}

check DestroyCurrentOK for 3 but 2 Time

pred DestroyBlocked[t, t' : Time] {
	some p : CProcess {
		DestroyBlockedProcess[t, t', p]
		PreserveStateProcess[t, t', NullProcess]
		PreserveState[t, t', p]
		currentAction.t' = DestroyBlockedAction
	}
}

assert DestroyBlockedOK {
	all t, t' : Time | Inv[t] and DestroyBlocked[t, t'] => Inv[t']
}

check DestroyBlockedOK for 3 but 2 Time

pred	PreserveState[t, t' : Time, p : CProcess] {
	all other : CProcess - p | PreserveStateProcess[t, t', other]
}

pred PerformSomeAction[t, t' : Time] {
	Create[t, t']
	or Dispatch[t, t']
	or Timeout[t, t']
	or Block[t, t']
	or Wakeup[t, t']
	or DestroyReady[t, t']
	or DestroyCurrent[t, t']
	or DestroyBlocked[t, t']
}

run {
} 

fact {
	Init[first]
	all t, t' : Time | t -> t' in next => PerformSomeAction[t, t']
}

check { 
	all t : Time| Inv[t]
}
