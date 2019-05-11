open Process
open Set[Process/Process]
open Chain[Process/Process]
open AScheduler
open CScheduler

pred retrieve[at : AScheduler/Time, ct : CScheduler/Time]
{
	ct.current = at.current
	Chain/retrieve[at.ready, ct.ready]
	Chain/retrieve[at.free, ct.free]
	Chain/retrieve[at.blocked, ct.blocked]
}

check CheckRefinmentCreate {
	all at, at' : AScheduler/Time, ct, ct' : CScheduler/Time, pout : Process | 
		(retrieve[at, ct] and retrieve[at', ct']) => 
			(AScheduler/Create[at, at', pout] iff CScheduler/Create[ct, ct', pout])
}

check CheckRefinmentDispatch {
	all at, at' : AScheduler/Time, ct, ct' : CScheduler/Time, pout : Process | 
		(retrieve[at, ct] and retrieve[at', ct']) => 
			(AScheduler/Dispatch[at, at', pout] iff CScheduler/Dispatch[ct, ct', pout])
}

check CheckRefinmentTimeOut {
	all at, at' : AScheduler/Time, ct, ct' : CScheduler/Time, pout : Process | 
		(retrieve[at, ct] and retrieve[at', ct']) => 
			(AScheduler/TimeOut[at, at', pout] iff CScheduler/TimeOut[ct, ct', pout])
}

check CheckRefinmentBlock {
	all at, at' : AScheduler/Time, ct, ct' : CScheduler/Time, pout : Process | 
		(retrieve[at, ct] and retrieve[at', ct']) => 
			(AScheduler/Block[at, at', pout] iff CScheduler/Block[ct, ct', pout])
} 

check CheckRefinmentWakeUp {
	all at, at' : AScheduler/Time, ct, ct' : CScheduler/Time, pout : Process | 
		(retrieve[at, ct] and retrieve[at', ct']) => 
			(AScheduler/WakeUp[at, at', pout] iff CScheduler/WakeUp[ct, ct', pout])
} 

check CheckRefinmentDestroy {
	all at, at' : AScheduler/Time, ct, ct' : CScheduler/Time, pout : Process | 
		(retrieve[at, ct] and retrieve[at', ct']) => 
			(AScheduler/Destroy[at, at', pout] iff CScheduler/Destroy[ct, ct', pout])
} 
