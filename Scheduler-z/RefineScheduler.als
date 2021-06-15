open Process
open Set[Process/Process]
open Chain[Process/Process]
open AScheduler
open CScheduler

pred retrieve[at : AScheduler/Time, ct : CScheduler/Time]
{
	ct.current = at.current
	Chain/Retrieve[at.ready, ct.ready]
	Chain/Retrieve[at.free, ct.free]
	Chain/Retrieve[at.blocked, ct.blocked]
}

check CheckRefinmentCreate {
	all at,at' : AScheduler/Time, ct, ct' : CScheduler/Time, pout : Process | 
		(AScheduler/inv[at] and CScheduler/inv[ct] and retrieve[at, ct]  and retrieve[at', ct'] and CScheduler/Create[ct, ct', pout] )
			=> (AScheduler/Create[at, at', pout])
} for 5 but 2 AScheduler/Time, 2 CScheduler/Time

check CheckRefinmentDispatch {
	all at, at' : AScheduler/Time, ct, ct' : CScheduler/Time, pout : Process | 
		(retrieve[at, ct] and retrieve[at', ct']) => 
			(AScheduler/Dispatch[at, at', pout] iff CScheduler/Dispatch[ct, ct', pout])
} for 3 but 2 AScheduler/Time, 2 CScheduler/Time

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
