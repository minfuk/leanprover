import algebra.category.functor.basic algebra.category types.equiv types.lift

open eq category equiv iso is_equiv is_trunc function sigma

universe variables u

structure pointed_set :=
  (a : Set)
  (star : a)

structure pointed_set_morphism (a b : pointed_set) :=
  (f : (pointed_set.a a) → (pointed_set.a b))
  (star : f (pointed_set.star a) = (pointed_set.star b))

theorem pointed_set_morphism_eq {a b : pointed_set} (f f' : pointed_set_morphism a b)
  (H : pointed_set_morphism.f f = pointed_set_morphism.f f') : f = f' :=
  begin
    cases f,
    cases f',
    cases H,
    apply ap (pointed_set_morphism.mk f_1),
    apply is_prop.elim,
  end

theorem pointed_set_morphism_is_set (a b : pointed_set)
  : is_set (pointed_set_morphism a b) :=
begin
  apply is_trunc_equiv_closed_rev,
  have H : pointed_set_morphism a b ≃ (Σ f : (pointed_set.a a) → (pointed_set.a b),
    f (pointed_set.star a) = (pointed_set.star b)),
    begin
      fapply equiv.MK,
      { intro x, induction x, constructor, assumption, },
      { intro y, induction y, constructor, assumption, },
      { intro y, induction y, reflexivity, },
      { intro x, induction x, reflexivity, },
    end,
  apply H,
end

definition pointed_set_comp {a b c : pointed_set.{u}}
  (g : pointed_set_morphism b c) (f : pointed_set_morphism a b) :
  pointed_set_morphism a c :=
  pointed_set_morphism.mk
    ((pointed_set_morphism.f g) ∘ (pointed_set_morphism.f f))
    (calc ((pointed_set_morphism.f g) ∘ (pointed_set_morphism.f f)) (pointed_set.star a)
          = (pointed_set_morphism.f g) (pointed_set.star b) :
            ap (pointed_set_morphism.f g) (pointed_set_morphism.star f)
      ... = pointed_set.star c : pointed_set_morphism.star g)

definition pointed_set_ID (a : pointed_set) : pointed_set_morphism a a :=
  pointed_set_morphism.mk
    (λ x, x)
/-    
    (calc (λx, x) (pointed_set.star a)
          = (pointed_set.star a) : rfl)
-/
    (rfl)

theorem pointed_set_assoc {a b c d : pointed_set}
  (h : pointed_set_morphism c d) (g : pointed_set_morphism b c) (f : pointed_set_morphism a b) :
  pointed_set_comp h (pointed_set_comp g f) = pointed_set_comp (pointed_set_comp h g) f :=
  pointed_set_morphism_eq
    (pointed_set_comp h (pointed_set_comp g f))
    (pointed_set_comp (pointed_set_comp h g) f)
    (assoc (pointed_set_morphism.f h) (pointed_set_morphism.f g) (pointed_set_morphism.f f))

theorem pointed_set_idl {a b : pointed_set} (f : pointed_set_morphism a b) :
  pointed_set_comp (pointed_set_ID b) f = f :=
  pointed_set_morphism_eq
    (pointed_set_comp (pointed_set_ID b) f) f (rfl)

theorem pointed_set_idr {a b : pointed_set} (f : pointed_set_morphism a b) :
  pointed_set_comp f (pointed_set_ID a) = f :=
  pointed_set_morphism_eq
    (pointed_set_comp f (pointed_set_ID a)) f (rfl)

definition precategory_pointed_set : precategory pointed_set :=
  @precategory.mk _
    (λ a b, pointed_set_morphism a b)
    (λ a b, pointed_set_morphism_is_set a b)
    (λ a b c g f, pointed_set_comp g f)
    (λ a, pointed_set_ID a)
    (λ a b c d h g f, pointed_set_assoc h g f)
    (λ a b f, pointed_set_idl f)
    (λ a b f, pointed_set_idr f)
