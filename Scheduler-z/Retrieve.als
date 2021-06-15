module Retrieve[T]

open Set[T]
open Chain[T]

pred Retrieve[s : Set, c : Chain] {
	s.items = (c.head).*(c.next)
}

check {
	all s : Set, c : Chain, p : T | 
		(Inv[c] and Retrieve[s, c]) => 
			(Exists[c, p] iff Exists[s, p])
} for 2 but 1 Set, 1 Chain

check {
	all s : Set, c : Chain, p : T | 
		(Inv[c] and Retrieve[s, c]) => 
			Count[c, p] = Count[s, p]
}

run { 
	some s : Set, c : Chain | 
		Inv[c] and Retrieve[s, c] 
} for 4 but 1 Set, 1 Chain

check {
	all s : Set, c : Chain | 
		Empty[s] and Empty[c] => Retrieve[s, c] 
}

check CheckChainPushNonEmpty {
	all c , c' : Chain, p : T | 
		Inv[c] and push_non_empty[c, c', p] => Inv[c']
} for 4 but 2 Chain

check CheckChainPushEmpty {
	all c , c' : Chain, p : T | 
		Inv[c] and push_empty[c, c', p] => Inv[c']
} for 4 but 2 Chain

run { 
	some c, c' : Chain, p : T | 
		Inv[c] and Push[c, c', p] 
} for 4 but 2 Chain

check CheckChainPush {
	all c , c' : Chain, p : T | 
		Inv[c] and Push[c, c', p] => Inv[c']
} for 4 but 2 Chain

check {
	all s, s' : Set, c, c' : Chain, p : T | {
		Inv[c] 
		Retrieve[s, c] 
		Retrieve[s', c'] 
		Push[c, c', p] 
	} => Add[s, s', p] 
} for 3 but 2 Set, 2 Chain

run { 
	some c, c' : Chain, p : T | Inv[c] and Pop[c, c', p] 
} for 4 but 2 Chain, 0 Set

check {
	all s, s' : Set, c, c' : Chain , p : T |
		Remove[s, s', p] and Retrieve[s, c] and Inv[c] and Pop[c, c', p] 
			=> Retrieve[s', c']
} for 4 but 2 Set, 2 Chain

assert ChainPopSetRemoveAny {
	all s, s' : Set, c, c' : Chain | {
		Retrieve[s, c] 
		Retrieve[s', c'] 
		Inv[c]  
		(some p : T | Pop[c, c', p])
	} => (some p : T | RemoveAny[s, s', p])
} 

check ChainPopSetRemoveAny for 3 but 2 Set, 2 Chain

check CheckChainRemoveFirstLone {
	all c, c' : Chain, p : T |
		Inv[c] 
		and remove_first_lone[c, c', p] => Inv[c']
} for 4 but 0 Set, 2 Chain

check CheckChainRemoveFirstMany {
	all c, c' : Chain, p : T |
		Inv[c] 
		and remove_first_many[c, c', p] => Inv[c']
} for 4 but 0 Set, 2 Chain

run { 
	some c, c' : Chain, p : T | 
		Inv[c] 
		and remove_middle[c, c', p] 
} for 4 but 2 Set, 2 Chain

check {
	all s, s' : Set, c, c' : Chain, p : T |
		Remove[s, s', p] 
		and Retrieve[s, c] 
		and Inv[c] 
		and remove_middle[c, c', p] => Retrieve[s', c']
} for 4 but 2 Set, 2 Chain

check {
	all s, s' : Set, c, c' : Chain, p : T |
		Remove[s, s', p] 
		and Retrieve[s, c] 
		and Inv[c] 
		and Remove[c, c', p] => Retrieve[s', c']
} for 4 but 2 Set, 2 Chain

check {
	all c, c' : Chain, p : T |
		Inv[c] 
		and remove_middle[c, c', p] => Inv[c']
} for 4 but 2 Set, 2 Chain

