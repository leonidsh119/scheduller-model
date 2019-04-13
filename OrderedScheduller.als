module scheduler
open AbstractScheduler // How can I make all the declarations in the same namespace?

one sig OrderedScheduller { // How can I get rid from OrderedScheduller and have current and ready as "global"?
	current : Process lone -> Time,
	ready : (seq Process) -> Time
} {
	all t : Time | !ready.t.hasDups[] 
}

pred OS_Inv[t : Time] {
	AS_Inv[t]
	no OrderedScheduller.current.t or OrderedScheduller.current.t.state.t = Current
	no OrderedScheduller.ready.t or (all idx : Int | (idx >= 0 and idx < #(OrderedScheduller.ready.t)) implies (OrderedScheduller.ready.t)[idx].state.t = Ready) //  Can we define it in more elegant way?
}

pred OS_Init[t : Time] {
	AS_Init[t]
	no OrderedScheduller.current.t
	no OrderedScheduller.ready.t
}

pred OS_Create[t, t' : Time] {
	some p : Process {
		OrderedScheduller.current.t' = OrderedScheduller.current.t
		OrderedScheduller.ready.t' = OrderedScheduller.ready.t.add[p]
		AS_Create[t, t', p]
	}
}

pred OS_Dispatch[t, t' : Time] {
	no OrderedScheduller.current.t
	some OrderedScheduller.ready.t

	OrderedScheduller.current.t' = (OrderedScheduller.ready.t)[0]
	OrderedScheduller.ready.t' = OrderedScheduller.ready.t.rest[]
	AS_Dispatch[t, t', (OrderedScheduller.ready.t)[0]]
}

pred OS_Timeout[t, t' : Time] {
	some OrderedScheduller.current.t
	no OrderedScheduller.current.t'

	OrderedScheduller.current.t' = OrderedScheduller.current.t
	OrderedScheduller.ready.t' = OrderedScheduller.ready.t
	AS_Timeout[t, t', OrderedScheduller.current.t]
}

pred OS_Block[t, t' : Time] {
	some OrderedScheduller.current.t
	no OrderedScheduller.current.t'

	OrderedScheduller.current.t' = OrderedScheduller.current.t
	OrderedScheduller.ready.t' = OrderedScheduller.ready.t
	AS_Block[t, t', OrderedScheduller.current.t]
}

pred OS_Wakeup[t, t' : Time, p : Process] {
	OrderedScheduller.current.t' = OrderedScheduller.current.t
	OrderedScheduller.ready.t' = OrderedScheduller.ready.t.add[p]
	AS_Wakeup[t, t', p]
}

pred OS_DestroyReady[t, t' : Time, p : Process] {
	OrderedScheduller.current.t' = OrderedScheduller.current.t
	OrderedScheduller.ready.t' = OrderedScheduller.ready.t.delete[OrderedScheduller.ready.t.idxOf[p]]
	AS_DestroyReady[t, t', p]
}

pred OS_DestroyCurrent[t, t' : Time] {
	some OrderedScheduller.current.t
	no OrderedScheduller.current.t'

	OrderedScheduller.current.t' = OrderedScheduller.current.t
	OrderedScheduller.ready.t' = OrderedScheduller.ready.t
	AS_DestroyCurrent[t, t', OrderedScheduller.current.t]
}

pred OS_DestroyBlocked[t, t' : Time, p : Process] {
	OrderedScheduller.current.t' = OrderedScheduller.current.t
	OrderedScheduller.ready.t' = OrderedScheduller.ready.t
	AS_DestroyBlocked[t, t', p]
}

pred OS_PerformSomeAction[t, t' : Time] {
	some p : Process |
		OS_Create[t, t']
		or OS_Dispatch[t, t']
		or OS_Timeout[t, t']
		or OS_Block[t, t']
		or OS_Wakeup[t, t', p]
		or OS_DestroyReady[t, t', p]
		or OS_DestroyCurrent[t, t']
		or OS_DestroyBlocked[t, t', p]
}

fact {
	OS_Init[first]
	all t, t' : Time | t -> t' in next implies OS_PerformSomeAction[t, t']
}

check { 
	all t : Time| OS_Inv[t]
}

run {
} for 10 // Why I am not getting 10 processes in model?
