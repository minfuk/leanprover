import algebra.category.basic
  algebra.category.morphism
  algebra.category.functor
  algebra.category.constructions
  .cat_example06

open eq eq.ops category morphism functor category.product category.ops prod

definition diag_functor [constructor] (C : Category) : C ⇒ C ×c C :=
functor.mk
  (λa, pair a a)
  (λa b f, pair f f)
  (λa, rfl)
  (λa b c g f, rfl)

structure coproduct {C : Category} (a b : C) :=
  (c : C)
  (i : a ⟶ c)
  (j : b ⟶ c)
  (univ : ∀(d : C) (f : a ⟶ d) (g : b ⟶ d),
    ∃!(h : c ⟶ d), f = h ∘ i ∧ g = h ∘ j)

lemma aaa {A B : Type} {a : A} {b : B} {p : A × B} (H : p = pair a b) :
  pr1 p = a ∧ pr2 p = b :=
  have H1 : pr1 p = a, from
    calc pr1 p = pr1 (pair a b) : eq.symm H
           ... = a : pr1.mk a b,
  have H2 : pr2 p = b, from
    calc pr2 p = pr2 (pair a b) : eq.symm H
           ... = b : pr2.mk a b,
  and.intro H1 H2

lemma xxx {A B : Type} {a a' : A} {b : B} (H : a = a')
  : pair a b = pair a' b :=
  subst H rfl

lemma yyy {A B : Type} {a : A} {b b' : B} (H : b = b')
  : pair a b = pair a b' :=
  subst H rfl

example {C : Category} {a b : C} (x : coproduct a b)
  : universal_arrow (pair a b) (diag_functor C) :=
  universal_arrow.mk
    (coproduct.c x)
    (pair (coproduct.i x) (coproduct.j x))
    (show ∀(d : C) (f : @category.hom _ (C ×c C) (pair a b) (pair d d)),
      ∃!(f' : (coproduct.c x) ⟶ d),
      (pair f' f') ∘ (pair (coproduct.i x) (coproduct.j x)) = f, from
      take d,
      take f,
      have H1 : ∃!(h : (coproduct.c x) ⟶ d),
        (pr1 f) = h ∘ (coproduct.i x) ∧ (pr2 f) = h ∘ (coproduct.j x), from
        (coproduct.univ x) d (pr1 f) (pr2 f),
      obtain h (H2 : (pr1 f) = h ∘ (coproduct.i x)
        ∧ (pr2 f) = h ∘ (coproduct.j x)), from
        exists_of_exists_unique H1,
      have H3 : (pair h h) ∘ (pair (coproduct.i x) (coproduct.j x)) = f, from
        calc (pair h h) ∘ (pair (coproduct.i x) (coproduct.j x))
              = pair (h ∘ (coproduct.i x)) (h ∘ (coproduct.j x)) : rfl
          ... = pair (pr1 f) (h ∘ (coproduct.j x)) : xxx (eq.symm (and.left H2))
          ... = pair (pr1 f) (pr2 f) : yyy (eq.symm (and.right H2))
          ... = f : eta f,
      have H4 : ∀(h' : (coproduct.c x) ⟶ d),
        (pair h' h') ∘ (pair (coproduct.i x) (coproduct.j x)) = f
        → h' = h, from
        take h',
        assume H5 : (pair h' h') ∘ (pair (coproduct.i x) (coproduct.j x)) = f,
        have H6 : f = pair (h' ∘ (coproduct.i x)) (h' ∘ (coproduct.j x)), from
          calc f = (pair h' h') ∘ (pair (coproduct.i x) (coproduct.j x))
                    : eq.symm H5
             ... = pair (h' ∘ (coproduct.i x)) (h' ∘ (coproduct.j x)) : rfl,
        unique_of_exists_unique H1 (aaa H6) H2,
      exists_unique.intro h H3 H4)
