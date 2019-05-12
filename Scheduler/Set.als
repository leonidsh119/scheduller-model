module Set[T]

abstract sig Set { 
	items : set T 
}

pred Set_empty[s : Set] {
	no s.items
}

pred Set_exists[s: Set, p : T] {
	p in s.items
}

fun Set_count[s : Set, p : T] : Int {
	#(p <: s.items)
}

pred Set_inv[s : Set] {}

pred Set_equal[s, t : Set] {
	s.items = t.items
}

pred Set_add[s, s' : Set, p : T] {
	s'.items = s.items + p
}

pred Set_remove[s, s' : Set, p : T] {
	s'.items = s.items - p
}

pred Set_replace[s, s' : Set,  old : T, new : T] {
	s'.items = s.items - old + new
}

pred Set_remove_any[s, s' : Set, pout : T] {
	some p : s.items | {
		s'.items = s.items - p
		pout = p
	}
}

