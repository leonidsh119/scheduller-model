module scheduler
open Process

abstract sig Action {
	currentAction : set Time
}

one sig InitAction, CreateAction, DispatchAction, TimeoutAction, BlockAction, WakeupAction, DestroyReadyAction, DestroyCurrentAction, DestroyBlockedAction extends Action {}

pred AS_Inv[t : Time] {
	lone p : Process | p.state.t = Current
}

pred AS_Init[t : Time] {
	some Process
	all p : Process | p.state.t = Free
	currentAction.t = InitAction
}

assert InitOK {
	all t : Time | AS_Init[t] => AS_Inv[t]
}

check InitOK for 3 but 1 Time

pred AS_Create[t, t' : Time, p : Process] {
	P_Create[t, t', p]
	AS_PreserveState[t, t', p]
	currentAction.t' = CreateAction
}

assert CreateOK {
	all t, t' : Time | some p : Process | AS_Inv[t] and AS_Create[t, t', p] => AS_Inv[t']
}

check CreateOK for 3 but 2 Time

pred AS_CanDispatch[t : Time] {
	no other : Process | other.state.t = Current
}

pred AS_Dispatch[t, t' : Time, p : Process] {
	AS_CanDispatch[t]
	P_Dispatch[t, t', p]
	AS_PreserveState[t, t', p]
	currentAction.t' = DispatchAction
}

assert DispatchOK {
	all t, t' : Time | some p : Process | AS_Inv[t] and AS_Dispatch[t, t', p] => AS_Inv[t']
}

check DispatchOK for 3 but 2 Time

pred AS_Timeout[t, t' : Time, p : Process] {
	P_Timeout[t, t', p]
	AS_PreserveState[t, t', p]
	currentAction.t' = TimeoutAction
}

assert TimeoutOK {
	all t, t' : Time | some p : Process | AS_Inv[t] and AS_Timeout[t, t', p] => AS_Inv[t']
}

check TimeoutOK for 3 but 2 Time

pred AS_Block[t, t' : Time, p : Process] {
	P_Block[t, t', p]
	AS_PreserveState[t, t', p]
	currentAction.t' = BlockAction
}

assert BlockOK {
	all t, t' : Time | some p : Process | AS_Inv[t] and AS_Block[t, t', p] => AS_Inv[t']
}

check BlockOK for 3 but 2 Time

pred AS_Wakeup[t, t' : Time, p : Process] {
	P_Wakeup[t, t', p]
	AS_PreserveState[t, t', p]
	currentAction.t' = WakeupAction
}

assert WakeupOK {
	all t, t' : Time | some p : Process | AS_Inv[t] and AS_Wakeup[t, t', p] => AS_Inv[t']
}

check WakeupOK for 3 but 2 Time

pred AS_DestroyReady[t, t' : Time, p : Process] {
	P_DestroyReady[t, t', p]
	AS_PreserveState[t, t', p]
	currentAction.t' = DestroyReadyAction
}

assert DestroyReadyOK {
	all t, t' : Time | some p : Process | AS_Inv[t] and AS_DestroyReady[t, t', p] => AS_Inv[t']
}

check DestroyReadyOK for 3 but 2 Time

pred AS_DestroyCurrent[t, t' : Time, p : Process] {
	P_DestroyCurrent[t, t', p]
	AS_PreserveState[t, t', p]
	currentAction.t' = DestroyCurrentAction
}

assert DestroyCurrentOK {
	all t, t' : Time | some p : Process | AS_Inv[t] and AS_DestroyCurrent[t, t', p] => AS_Inv[t']
}

check DestroyCurrentOK for 3 but 2 Time

pred AS_DestroyBlocked[t, t' : Time, p : Process] {
	P_DestroyBlocked[t, t', p]
	AS_PreserveState[t, t', p]
	currentAction.t' = DestroyBlockedAction
}

assert DestroyBlockedOK {
	all t, t' : Time | some p : Process | AS_Inv[t] and AS_DestroyBlocked[t, t', p] => AS_Inv[t']
}

check DestroyBlockedOK for 3 but 2 Time

pred	AS_PreserveState[t, t' : Time, p : Process] {
	all other : Process - p | P_PreserveState[t, t', other]
}

pred AS_PerformSomeAction[t, t' : Time] {
	some p : Process |
		AS_Create[t, t', p]
		or AS_Dispatch[t, t', p]
		or AS_Timeout[t, t', p]
		or AS_Block[t, t', p]
		or AS_Wakeup[t, t', p]
		or AS_DestroyReady[t, t', p]
		or AS_DestroyCurrent[t, t', p]
		or AS_DestroyBlocked[t, t', p]
}

fact {
	all t : Time | some p : Process | p.state.t = Free // Liveness
	AS_Init[first]
	all t, t' : Time | t -> t' in next => AS_PerformSomeAction[t, t']
}

check { 
	all t : Time| AS_Inv[t]
}

run {
} for 9 but 9 Process, 9 Time // Why I am not getting 10 processes in model?

