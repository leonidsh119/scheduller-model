module Chain[T]

abstract sig Chain {
	head : lone T,
	last : lone T,
	next : T lone -> lone T
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

pred Empty[c : Chain] {
	no c.head
	no c.last
	no c.next
}

pred Exists[c : Chain, p : T] {
	p in (c.head).*(c.next)
}

fun Count[c : Chain, p : T] : Int {
	#(p <: (c.head).*(c.next))
}

pred Equals[c1, c2 : Chain] {
	c1.head = c2.head
	c1.last = c2.last
	c1.next = c2.next
}

pred Add[c, c' : Chain, p : T] {
	Push[c, c', p]
}

pred Remove[c, c' : Chain, p : T] {
	remove_first[c, c', p] or 
	remove_last[c, c', p] or 
	remove_middle[c, c', p]
}

pred RemoveAny[c, c' : Chain, p : T] {
	Pop[c, c', p]
}

pred Push[c, c' : Chain, p : T] {
	not Exists[c, p]
	push_non_empty[c, c', p] or push_empty[c, c', p]
}

pred Pop[c, c': Chain, p : T] {
	c.last = p
	(pop_last_one[c, c', p] or pop_more_than_one[c, c', p])
}


// internals

pred push_non_empty[c, c' : Chain, p : T] {
	not Empty[c]
	not Exists[c, p]
	c'.next = c.next + p -> c.head
	c'.head = p
	c'.last = c.last
}

pred push_empty[c, c' :  Chain, p : T] {
	Empty[c]
	c'.next = c.next
	c'.head = p
	c'.last = p
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

pred remove_first_lone[c, c' : Chain, p : T] {
	c.head = p
	pop_last_one[c, c', p]
}

pred remove_first_many[c, c' : Chain, p : T] {
	c.head != c.last
	c.head = p
	c'.head = (c.head).(c.next)
	c'.next = c.next - (c.head -> c'.head)
	c'.last = c.last
}

pred remove_first[c, c' : Chain, p : T] {
	remove_first_lone[c, c', p] or
	remove_first_many[c, c', p]
}

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
