module RunCScheduler

open CScheduler

run RunInv { 
	some t : Time | Inv[t] 
} for 4 but 1 Time

run RunInit { 
	some t : Time | Init[t] 
} for 4 but 1 Time

check CheckInit { 
	all t : Time | Init[t] => Inv[t] 
} for 4 but 1 Time

run RunCreate { 
	some t, t' : Time, p : Process | 
		Inv[t] and Create[t, t', p] 
} for 4 but 2 Time

check CheckCreate { 
	all t, t' : Time, p : Process |
		Inv[t] and Create[t, t', p] => Inv[t']
} for 4 but 2 Time

run RunDispatch { 
	some t, t' : Time, pout : Process | 
		Inv[t] and Dispatch[t, t', pout] 
} for 4 but 2 Time

check CheckDispatch { 
	all t, t' : Time, pout : Process | 
		Inv[t] and Dispatch[t, t', pout] => Inv[t']
} for 4 but 2 Time

run RunTimeOut { 
	some t, t' : Time, p : Process | 
		Inv[t] and TimeOut[t, t', p] 
} for 4 but 2 Time

check CheckTimeOut { 
	all t, t' : Time, p : Process | 
		Inv[t] and TimeOut[t, t', p] => Inv[t'] 
} for 4 but 2 Time

run RunBlock { 
	some t, t' : Time, p : Process | 
		Inv[t] and Block[t, t', p] 
} for 4 but 2 Time

check CheckBlock {
	all t, t' : Time, p : Process | 
		Inv[t] and Block[t, t', p] => Inv[t'] 
} for 4 but 2 Time

run RunWakeUp { 
	some t, t' : Time, p : Process | 
		Inv[t] and WakeUp[t, t', p] 
} for 4 but 2 Time

check CheckWakeUp { 
	all t, t' : Time, p : Process | 
		Inv[t] and WakeUp[t, t', p] => Inv[t'] 
} for 4 but 2 Time

run RunDestroyCurrent { 
	some t, t' : Time, p : Process | 
		Inv[t] and DestroyCurrent[t, t', p] 
} for 4 but 2 Time

check CheckDestroyCurrent { 
	all t, t' : Time | 
		no t'.current or
		some p : Process | 
			Inv[t] and DestroyCurrent[t, t', p] => Inv[t'] 
} for 4 but 2 Time

run RunDestroyReady { 
	some t, t' : Time, p : Process | 
		Inv[t] and DestroyReady[t, t', p]
} for 4 but 2 Time

check CheckDestroyReady { 
	all t, t' : Time | 
		Empty[t.ready] or 
		some p : Process |
			Inv[t] and DestroyReady[t, t', p] => Inv[t'] 
} for 4 but 2 Time

run RunDestroyBlocked { 
	some t, t' : Time, p : Process | 
		Inv[t] and DestroyBlocked[t, t', p] 
} for 4 but 2 Time

check CheckDestroyBlocked { 
	all t, t' : Time | 
		Empty[t.blocked] or 
		some p : Process |
			Inv[t] and DestroyBlocked[t, t', p] => Inv[t'] 
} for 4 but 2 Time

run RunDestroy { 
	some t, t' : Time, p : Process | 
		Inv[t] and Destroy[t, t', p] 
} for 4 but 2 Time

check CheckDestroy { 
	all t, t' : Time | 
		Empty[t.blocked] or 
		some p : Process |
			Inv[t] and Destroy[t, t', p] => Inv[t'] 
} for 4 but 2 Time
