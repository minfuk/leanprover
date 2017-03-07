import ..category
import ..functor

namespace fAlgebra

  open category functor

  section
    variable {C : Category}

    local infixl `⟶`:25 := @hom _ C^.struct
    local infixr `∘` := @comp _ C^.struct _ _ _

    structure FAlgebra (F : C ⇒ C) :=
    (carrier : C)
    (α : (F carrier) ⟶ carrier)

    variable {F : C ⇒ C}

    structure FAlgebra_morphism (a b : FAlgebra F) :=
    (mor : a^.carrier ⟶ b^.carrier)
    (commute : mor ∘ a^.α = b^.α ∘ (F^.morphism mor))

    private def assoc {a b c d : C} (f : c ⟶ d) (g : b ⟶ c) (h : a ⟶ b) :=
      @assoc _ C^.struct _ _ _ _ f g h

    definition FAlgebra_morphism_comp {a b c : FAlgebra F}
      (f : FAlgebra_morphism b c) (g : FAlgebra_morphism a b)
      : FAlgebra_morphism a c :=
      FAlgebra_morphism.mk
        (f^.mor ∘ g^.mor)
        (calc (f^.mor ∘ g^.mor) ∘ a^.α
              = f^.mor ∘ (g^.mor ∘ a^.α) : by rw (assoc f^.mor g^.mor a^.α)
          ... = f^.mor ∘ (b^.α ∘ (F^.morphism g^.mor)) : by rw g^.commute
          ... = (f^.mor ∘ b^.α) ∘ (F^.morphism g^.mor) :
            by rw assoc f^.mor b^.α (F^.morphism g^.mor)
          ... = (c^.α ∘ (F^.morphism f^.mor)) ∘ (F^.morphism g^.mor) :
            by rw f^.commute
          ... = c^.α ∘ ((F^.morphism f^.mor) ∘ (F^.morphism g^.mor)) :
            by rw assoc c^.α (F^.morphism f^.mor) (F^.morphism g^.mor)
          ... = c^.α ∘ (F^.morphism (f^.mor ∘ g^.mor)) :
            congr_arg (λ x, c^.α ∘ x) (eq.symm (F^.respect_comp f^.mor g^.mor)))

    private def ID (a : C) := @ID _ C^.struct a
    private def id_left {a b : C} (f : a ⟶ b) := @id_left _ C^.struct _ _ f
    private def id_right {a b : C} (f : a ⟶ b) := @id_right _ C^.struct _ _ f
    
    definition FAlgebra_id (a : FAlgebra F) : FAlgebra_morphism a a :=
      FAlgebra_morphism.mk
        (ID (a^.carrier))
        (calc (ID (a^.carrier)) ∘ a^.α
              = a^.α : id_left a^.α
          ... = a^.α ∘ (ID (F a^.carrier)) : eq.symm (id_right a^.α)
          ... = a^.α ∘ (F^.morphism (ID a^.carrier))
            : congr_arg (λ x, a^.α ∘ x) (eq.symm (F^.respect_id a^.carrier)))

    lemma FAlgebra_morphism_eta {a b : FAlgebra F} (f : FAlgebra_morphism a b)
      : f = FAlgebra_morphism.mk (f^.mor) (f^.commute) :=
    begin
      cases f,
      exact rfl,
    end

    lemma FAlgebra_morphism_eq {a b : FAlgebra F} (f g : FAlgebra_morphism a b)
      : f^.mor = g^.mor → f = g :=
    begin
      intro H,
      cases f,
      cases g,
      cases H,
      apply congr_arg (FAlgebra_morphism.mk mor),
      apply rfl,
    end

    theorem FAlgebra_morphism_assoc {a b c d : FAlgebra F}
      (f : FAlgebra_morphism c d) (g : FAlgebra_morphism b c)
      (h : FAlgebra_morphism a b)
      : FAlgebra_morphism_comp f (FAlgebra_morphism_comp g h)
        = FAlgebra_morphism_comp (FAlgebra_morphism_comp f g) h :=
      (FAlgebra_morphism_eq (FAlgebra_morphism_comp f (FAlgebra_morphism_comp g h))
        (FAlgebra_morphism_comp (FAlgebra_morphism_comp f g) h))
        (assoc f^.mor g^.mor h^.mor)

    theorem FAlgebra_morphism_id_left {a b : FAlgebra F}
      (f : FAlgebra_morphism a b)
      : FAlgebra_morphism_comp (FAlgebra_id b) f = f :=
      (FAlgebra_morphism_eq (FAlgebra_morphism_comp (FAlgebra_id b) f) f)
        (id_left f^.mor)

    theorem FAlgebra_morphism_id_right {a b : FAlgebra F}
      (f : FAlgebra_morphism a b)
      : FAlgebra_morphism_comp f (FAlgebra_id a) = f :=
      (FAlgebra_morphism_eq (FAlgebra_morphism_comp f (FAlgebra_id a)) f)
        (id_right f^.mor)

    definition fAlgebra_category : category (FAlgebra F) :=
    category.mk
      (λa b, FAlgebra_morphism a b)
      (λ a b c f g, FAlgebra_morphism_comp f g)
      (λ a, FAlgebra_id a)
      (λ a b c d f g h, FAlgebra_morphism_assoc f g h)
      (λ a b f, FAlgebra_morphism_id_left f)
      (λ a b f, FAlgebra_morphism_id_right f)
  end

end fAlgebra
