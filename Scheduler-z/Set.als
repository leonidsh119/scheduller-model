module Set[T]

abstract sig Set { 
	items : set T 
}

pred Inv[s : Set] {}

pred Empty[s : Set] {
	no s.items
}

pred Exists[s: Set, p : T] {
	p in s.items
}

fun Count[s : Set, p : T] : Int {
	#(p <: s.items)
}

pred Equals[s, t : Set] {
	s.items = t.items
}

pred Add[s, s' : Set, p : T] {
	s'.items = s.items + p
}

pred Remove[s, s' : Set, p : T] {
	s'.items = s.items - p
}

pred RemoveAny[s, s' : Set, pout : T] {
	some p : s.items | {
		s'.items = s.items - p
		pout = p
	}
}
