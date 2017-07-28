variables {α : Type} (r : α → α → Prop)

definition reflexive1 : Prop := ∀ (a : α), r a a
definition symmetric1 : Prop := ∀ {a b : α}, r a b → r b a
definition transitive1 : Prop := ∀ {a b c : α}, r a b → r b c → r a c
definition euclidean : Prop := ∀ {a b c : α}, r a b → r a c → r b c

variable {r}

theorem th1 (reflr : reflexive1 r) (euclr : euclidean r) : symmetric1 r :=
  take a b : α,
  suppose r a b,
  show r b a, from euclr this (reflr _)

theorem th2 (symmr : symmetric1 r) (euclr : euclidean r) : transitive1 r :=
  take (a b c : α),
  assume (rab : r a b) (rbc : r b c),
  euclr (symmr rab) rbc

-- ERROR: /
variable {e : euclidean r}
check e
check @e

theorem th3 (reflr : reflexive1 r) (euclr : euclidean r) : transitive1 r :=
  th2 (@th1 _ _ reflr @euclr) @euclr 
