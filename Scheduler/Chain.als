module Chain[T]

open Set[T]

sig Chain {
	head : lone T,
	last : lone T,
	next : T lone -> lone T
}

pred Retrieve[s : Set, c : Chain] {
	s.items = (c.head).*(c.next)
}

pred Empty[c : Chain] {
	no c.head
	no c.last
	no c.next
}

pred Exists[c : Chain, p : T] {
	p in (c.head).*(c.next)
}

pred Equals[c1, c2 : Chain] {
	c1.head = c2.head
	c1.last = c2.last
	c1.next = c2.next
}

check {
	all s : Set, c : Chain, p : T | 
		(Inv[c] and Retrieve[s, c]) => 
			(Exists[c, p] iff Exists[s, p])
} for 2 but 1 Set, 1 Chain

fun Count[c : Chain, p : T] : Int {
	#(p <: (c.head).*(c.next))
}

check {
	all s : Set, c : Chain, p : T | 
		(Inv[c] and Retrieve[s, c]) => 
			Count[c, p] = Count[s, p]
}

pred Inv[c : Chain] {
	no iden & c.next
	some c.head => some c.last and (#(c.next) = sub[#((c.head).*(c.next)), 1])
	no c.head => (no c.last and no c.next)
	c.last in (c.head).*(c.next)
	no (c.last).(c.next)
	no (c.next).(c.head)
	(c.head = c.last) => no c.next
}

run { 
	some s : Set, c : Chain | 
		Inv[c] and Retrieve[s, c] 
} for 4 but 1 Set, 1 Chain

check {
	all s : Set, c : Chain | 
		Empty[s] and Empty[c] => Retrieve[s, c] 
}

pred push_non_empty[c, c' : Chain, p : T] {
	not Empty[c]
	not Exists[c, p]
	c'.next = c.next + p -> c.head
	c'.head = p
	c'.last = c.last
}

check CheckChainPushNonEmpty {
	all c , c' : Chain, p : T | 
		Inv[c] and push_non_empty[c, c', p] => Inv[c']
} for 4 but 2 Chain

pred push_empty[c, c' :  Chain, p : T] {
	Empty[c]
	c'.next = c.next
	c'.head = p
	c'.last = p
}

check CheckChainPushEmpty {
	all c , c' : Chain, p : T | 
		Inv[c] and push_empty[c, c', p] => Inv[c']
} for 4 but 2 Chain

pred Push[c, c' : Chain, p : T] {
	not Exists[c, p]
	push_non_empty[c, c', p] or push_empty[c, c', p]
}

// Alias
pred Add[c, c' : Chain, p : T] {
	Push[c, c', p]
}

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

pred Pop[c, c': Chain, p : T] {
	c.last = p
	(pop_last_one[c, c', p] or pop_more_than_one[c, c', p])
}

// Alias
pred RemoveAny[c, c' : Chain, p : T] {
	Pop[c, c', p]
}

pred pop_last_one[c, c' : Chain, p : T] {
	c.last = c.head
	no c'.head
	no c'.last
	no c'.next
}

pred pop_more_than_one[c, c' : Chain, p : T] {
	c.last != c.head
	c'.head = c.head
	(c'.last).(c.next) = c.last
	c'.next = c.next - (c'.last -> c.last)
}

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

pred Remove[c, c' : Chain, p : T] {
	remove_first[c, c', p] or 
	remove_last[c, c', p] or 
	remove_middle[c, c', p]
}

pred remove_first[c, c' : Chain, p : T] {
	remove_first_lone[c, c', p] or
	remove_first_many[c, c', p]
}

pred remove_first_lone[c, c' : Chain, p : T] {
	c.head = p
	pop_last_one[c, c', p]
}

check CheckChainRemoveFirstLone {
	all c, c' : Chain, p : T |
		Inv[c] 
		and remove_first_lone[c, c', p] => Inv[c']
} for 4 but 0 Set, 2 Chain

pred remove_first_many[c, c' : Chain, p : T] {
	c.head != c.last
	c.head = p
	c'.head = (c.head).(c.next)
	c'.next = c.next - (c.head -> c'.head)
	c'.last = c.last
}

check CheckChainRemoveFirstMany {
	all c, c' : Chain, p : T |
		Inv[c] 
		and remove_first_many[c, c', p] => Inv[c']
} for 4 but 0 Set, 2 Chain

pred remove_last[c, c' : Chain, p : T] {
	Pop[c, c', p]
}

pred remove_middle[c, c' : Chain, p : T] {
	c.head != p
	c.last != p
	p in (c.head).*(c.next)
	let prev = c.next.p {
		c'.next = c.next - (prev -> p) - (p -> p.(c.next)) + (prev -> p.(c.next))
		c'.head = c.head
		c'.last = c.last
	}
}

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

