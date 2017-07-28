import algebra.category.basic
  algebra.category.morphism

open eq eq.ops category morphism

structure coproduct {C : Category} (a b : C) :=
  (c : C)
  (i : a ⟶ c)
  (j : b ⟶ c)
  (univ : ∀(d : C) (f : a ⟶ d) (g : b ⟶ d),
    ∃!(h : c ⟶ d), f = h ∘ i ∧ g = h ∘ j)

attribute coproduct.c [coercion]

lemma univ_id {C : Category} {a b : C} (x : coproduct a b) :
  let xc : C := coproduct.c x in
  let xi : a ⟶ xc := coproduct.i x in
  let xj : b ⟶ xc := coproduct.j x in
  ∀(h' : xc ⟶ xc), xi = h' ∘ xi ∧ xj = h' ∘ xj → h' = (ID xc) :=
  let xc : C := coproduct.c x in
  let xi : a ⟶ xc := coproduct.i x in
  let xj : b ⟶ xc := coproduct.j x in
  take h' : xc ⟶ xc,
  assume H1 : xi = h' ∘ xi ∧ xj = h' ∘ xj,
  have H2 : ∀h, xi = h ∘ xi ∧ xj = h ∘ xj
    → (∀h'', xi = h'' ∘ xi ∧ xj = h'' ∘ xj → h'' = h)
    → h' = (ID xc), from
      take h : xc ⟶ xc,
      assume H3 : xi = h ∘ xi ∧ xj = h ∘ xj,
      assume H4 : ∀h'', xi = h'' ∘ xi ∧ xj = h'' ∘ xj → h'' = h,
      have H5 : xi = (ID xc) ∘ xi, from eq.symm (category.id_left xi),
      have H6 : xj = (ID xc) ∘ xj, from eq.symm (category.id_left xj),
      have H7 : (ID xc) = h, from H4 (ID xc) (and.intro H5 H6),
      have H8 : h' = h, from H4 h' H1,
      eq.trans H8 (eq.symm H7),
  exists_unique.elim (
    (coproduct.univ x) (coproduct.c x) (coproduct.i x) (coproduct.j x)) H2
    
