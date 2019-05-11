module Chain[T]

open Set[T]

sig Chain {
	head : lone T,
	last : lone T,
	next : T lone -> lone T
}

pred retrieve[ s : Set , c : Chain ] {
	s.items = (c.head).*(c.next)
}

pred Chain_empty[c :Chain] {
	no c.head
}

pred Chain_exists[c :Chain, p : T] {
	p in (c.head).*(c.next)
}

check {
	all s : Set, c : Chain, p : T | 
		(Chain_inv[c] and retrieve[s,c]) => 
			(Chain_exists[c, p] iff Set_exists[s,p])
} for 2 but 1 Set, 1 Chain

fun Chain_count[c:Chain, p :T] : Int {
	#(p <: (c.head).*(c.next))
}

check {
	all s : Set, c : Chain, p : T | 
		(Chain_inv[c] and retrieve[s,c]) => 
			Chain_count[c, p] = Set_count[s,p]
}

pred Chain_inv[c : Chain] {

	no iden & c.next

	some c.head => some c.last

	c.last in (c.head).*(c.next)

	no (c.last).(c.next)

	(c.head = c.last) => no c.next
}

run { some s : Set, c : Chain | 
	Chain_inv[c] and retrieve[s,c] } for 4 but 1 Set, 1 Chain

check {
	all s : Set, c : Chain | 
		Set_empty[s] and Chain_empty[c] => retrieve[s,c] 
}

pred Chain_push_non_empty[c,c' : Chain ,p : T] {
	not Chain_empty[c]
	c'.next = c.next + p -> c.head
	c'.head = p
	c'.last = c.last
}

pred Chain_push_empty[c,c':Chain, p : T] {
	Chain_empty[c]
	c'.next = c.next
	c'.head = p
	c'.last = p
}

pred Chain_push[c,c' : Chain, p : T] {
	not Chain_exists[c,p]

	Chain_push_non_empty[c,c',p] or Chain_push_empty[c,c',p]
}

run { 
	some c,c':Chain, p : T | Chain_inv[c] and Chain_push[c,c',p] 
} for 3 but 2 Chain, 0 Set

check {
	all c,c':Chain , p : T | 
		Chain_inv[c] and Chain_push[c,c',p] => Chain_inv[c']
} for 3 but 2 Chain, 0 Set

check {
	all s,s' :Set, c,c' :Chain , p :T | {
		Chain_inv[c] 
		retrieve[s,c] 
		retrieve[s',c'] 
		Chain_push[c,c',p] 
		} => Set_add[s,s',p] 
} for 3 but 2 Set, 2 Chain

pred Chain_pop[c,c':Chain, p : T] {
	c.last = p

	(Chain_pop_last_one[c,c',p] or Chain_pop_more_than_one[c,c',p])
}

pred Chain_pop_last_one[c,c':Chain, p : T] {
	c.last = c.head

	no c'.head
	no c'.last
	no c'.next
}

pred Chain_pop_more_than_one[c,c':Chain, p :T] {

	c.last != c.head

	c'.head = c.head
	(c'.last).(c.next) = c.last
	c'.next = c.next - (c'.last -> c.last)
}

run { 
	some c,c':Chain, p : T | Chain_inv[c] and Chain_pop[c,c',p] 
} for 3 but 2 Chain, 0 Set

check {
	all s,s' :Set, c,c' :Chain , p :T |
		Set_remove[s,s',p] and retrieve[s,c] and Chain_inv[c] and Chain_pop[c,c',p] 
			=> retrieve[s',c']
} for 3 but 2 Set, 2 Chain

assert ChainPopSetRemoveAny {

	all s,s':Set, c,c':Chain | {
		retrieve[s,c] 
		retrieve[s',c'] 
		Chain_inv[c]  
		(some p : T | Chain_pop[c,c',p])
		} => (some p : T | Set_remove_any[s,s',p])
} 

check ChainPopSetRemoveAny for 3 but 2 Set, 2 Chain

pred Chain_delete[c,c':Chain, p: T] {
	Chain_delete_first[c,c',p] or 
	Chain_delete_last[c,c',p] or 
	Chain_delete_middle[c,c',p]
}

pred Chain_delete_first[c,c':Chain,p:T] {
	Chain_delete_first_lone[c,c',p] or
	Chain_delete_first_many[c,c',p]
}

pred Chain_delete_first_lone[c,c':Chain,p:T] {
	c.head = p
	Chain_pop_last_one[c,c',p]
}

pred Chain_delete_first_many[c,c':Chain,p:T] {
	c.head = p
	c'.head = (c.head).(c.next)
	c'.next = c.next - (c.head -> c'.head)
	c'.last = c.last
}

pred Chain_delete_last[c,c':Chain,p:T] {
	Chain_pop[c,c',p]
}

pred Chain_delete_middle[c,c':Chain, p:T] {

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
	some c,c':Chain, p : T | Chain_inv[c] and Chain_delete_middle[c,c',p] 
} for 3 but 2 Chain, 0 Set

check {
	all s,s' :Set, c,c' :Chain , p :T |
		Set_remove[s,s',p] and retrieve[s,c] and Chain_inv[c] and Chain_delete_middle[c,c',p] 
			=> retrieve[s',c']
} for 3 but 2 Set, 2 Chain

check {
	all s,s' :Set, c,c' :Chain , p :T |
		Set_remove[s,s',p] and retrieve[s,c] and Chain_inv[c] and Chain_delete[c,c',p] 
			=> retrieve[s',c']
} for 3 but 2 Set, 2 Chain

check {
	all c,c' :Chain , p :T |
		Chain_inv[c] and Chain_delete_middle[c,c',p] 
			=> Chain_inv[c']
} for 3 but 0 Set, 2 Chain

