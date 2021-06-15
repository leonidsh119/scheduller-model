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
