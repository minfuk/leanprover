open classical

structure aaa {A : Type} {P : A → Prop} :=
(val : A)
(spec : P val)

example {A : Type} {P : A → Prop} (H : ∃x, P x) : (@aaa A P) :=
  aaa.mk (some H) (some_spec H)

example {A : Type} {P : A → Prop} (H : ∃x, P x) : A :=
  have a : (@aaa A P), from aaa.mk (some H) (some_spec H),
  aaa.val a

example {A : Type} {P : A → Prop} (H : ∃x, P x) : ∃x, P x :=
  have a : (@aaa A P), from aaa.mk (some H) (some_spec H),
  Exists.intro (aaa.val a) (aaa.spec a)

example {A B : Type} {P : A → B → Prop} (H : ∃x y, P x y) : A :=
  some H

open prod

example {A B : Type} {P : A → B → Prop} (H : ∃x y, P x y) : A × B :=
  have H2 : ∃y x, P x y, from
    obtain x y (H3 : P x y), from H,
    exists.intro y (exists.intro x H3),
  ((some H), (some H2))  

noncomputable definition some2 {A B : Type} {P : A → B → Prop} (H : ∃x y, P x y) : A × B :=
  have H2 : ∃p : A × B, P (pr1 p) (pr2 p), from
    obtain x y (H3 : P x y), from H,
    exists.intro (x, y) H3,
  some H2

theorem some_spec2 {A B : Type} {P : A → B → Prop} (H : ∃x y, P x y)
  : let x := some2 H in P (pr1 x) (pr2 x) :=
  have H2 : ∃p : A × B, P (pr1 p) (pr2 p), from
    obtain x y (H3 : P x y), from H,
    exists.intro (x, y) H3,
  some_spec H2

  
