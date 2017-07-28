example {H1 H2 H3 : Prop} (P : H1 → H2 → H3) : (H1 ∧ H2) → H3 :=
  take (a : H1 ∧ H2),
  P (and.left a) (and.right a)

example {H1 H2 H3 : Prop} (P : (H1 ∧ H2) → H3) : H1 → H2 → H3 :=
  take (a : H1),
  take (b : H2),
  P (and.intro a b) 


example {H1 H2 : Prop} (P : H1 ∧ H2) : H1 → H2 :=
  take (a : H1),
  and.right P

/- これは言えない
example {H1 H2 : Prop} (P : H1 → H2) : H1 ∧ H2 :=
  ...
-/
