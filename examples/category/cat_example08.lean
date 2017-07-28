import algebra.category.basic
  algebra.category.morphism
  algebra.category.functor
  algebra.category.constructions
  .cat_example06

open eq eq.ops category morphism functor category.product category.ops

/-
structure universal_arrow {C D : Category} (c : C) (S : D ⇒ C) :=
  (r : D)
  (u : c ⟶ S r)
  (univ : ∀(d : D) (f : c ⟶ S d),
    ∃!(f' : r ⟶ d), (S f') ∘ u = f)
-/

structure coequalizer {C : Category} {a b : C} (f g : a ⟶ b) :=
  (e : C)
  (u : b ⟶ e)
  (i : u ∘ f = u ∘ g)
  (ii : ∀(c : C) (h : b ⟶ c), h ∘ f = h ∘ g
    → ∃!(h' : e ⟶ c), h = h' ∘ u)

open bool

inductive parallel_arrows_hom : bool → bool → Type :=
| id0 : parallel_arrows_hom ff ff
| id1 : parallel_arrows_hom tt tt
| f1 : parallel_arrows_hom ff tt
| f2 : parallel_arrows_hom ff tt

definition parallel_arrows_hom_comp {a b c: bool}
  (g : parallel_arrows_hom b c) (f : parallel_arrows_hom a b)
    : parallel_arrows_hom a c :=
begin
  cases a,
  cases c,
  exact parallel_arrows_hom.id0,
  cases b,
  exact g,
  exact f,
  cases c,
  cases b,
  exact f,
  exact g,
  exact parallel_arrows_hom.id1,
end

definition parallel_arrows_hom_id (a : bool) : parallel_arrows_hom a a :=
begin
  cases a,
  exact parallel_arrows_hom.id0,
  exact parallel_arrows_hom.id1,
end

theorem parallel_arrows_hom_id_left {a b : bool} (f : parallel_arrows_hom a b)
  : parallel_arrows_hom_comp (parallel_arrows_hom_id b) f = f :=
begin
  cases b,
  cases f,
  apply rfl,
  cases f,
  apply rfl,
  apply rfl,
  apply rfl,
end

theorem parallel_arrows_hom_id_right {a b : bool} (f : parallel_arrows_hom a b)
  : parallel_arrows_hom_comp f (parallel_arrows_hom_id a) = f :=
begin
  cases a,
  cases f,
  apply rfl,
  apply rfl,
  apply rfl,
  cases b,
  apply rfl,
  cases f,
  apply rfl,
end

theorem parallel_arrows_hom_assoc {a b c d : bool}
  (h : parallel_arrows_hom c d) (g : parallel_arrows_hom b c) (f : parallel_arrows_hom a b)
  : parallel_arrows_hom_comp h (parallel_arrows_hom_comp g f)
    = parallel_arrows_hom_comp (parallel_arrows_hom_comp h g) f :=
begin
  cases g,
  cases f,
  cases h,
  apply parallel_arrows_hom_id_right,
  apply parallel_arrows_hom_id_right,
  apply parallel_arrows_hom_id_left,
  cases h,
  apply parallel_arrows_hom_id_left,
  cases h,
  apply parallel_arrows_hom_id_left,
  cases h,
  cases f,
  apply parallel_arrows_hom_id_right,
end

definition category_parallel_arrows : category bool :=
mk (λ a b, parallel_arrows_hom a b)
   (λ a b c g f, parallel_arrows_hom_comp g f)
   (λ a, parallel_arrows_hom_id a)
   (λ a b c d h g f, parallel_arrows_hom_assoc h g f)
   (λ a b f, parallel_arrows_hom_id_left f)
   (λ a b f, parallel_arrows_hom_id_right f)

definition Category_parallel_arrows := Mk category_parallel_arrows

definition coequalizer_functor_target (C : Category) :=
  functor_category Category_parallel_arrows C

definition Coequalizer_functor_target (C : Category) :=
  Mk (coequalizer_functor_target C)

definition coequalizer_functor (C : Category) : C ⇒ (Coequalizer_functor_target C) :=
functor.mk (λ a, sorry)
           (λ a b f, sorry)
           (λ a, sorry)
           (λ a b c g f, sorry)

example {C : Category} {a b : C} (f g : a ⟶ b) (x : coequalizer f g)
  : universal_arrow (coequalizer f g) (coequalizer_functor C) :=
  universal_arrow.mk
    (coequalizer.e x)
    (pair (coproduct.i x) (coproduct.j x))
    (show ∀(d : C) (f : @category.hom _ (C ×c C) (pair a b) (pair d d)),
      ∃!(f' : (coproduct.c x) ⟶ d),
      (pair f' f') ∘ (pair (coproduct.i x) (coproduct.j x)) = f, from

