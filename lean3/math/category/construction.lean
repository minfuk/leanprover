import .category
import .functor
import .natural_transformation
import ...logic.logic
import ..prod

namespace category
  
  namespace opposite
    universe variable u

    attribute [reducible]
    definition opposite {ob : Type u} (C : category ob) : category ob :=
      mk (λa b, hom b a)
        (λ a b c f g, g ∘ f)
        (λ a, ID a)
        (λ a b c d f g h, eq.symm (assoc h g f))
        (λ a b f, id_right f)
        (λ a b f, id_left f)

    attribute [reducible]
    definition Opposite (C : Category) : Category := Mk (opposite C^.struct)

    infixr `∘op`:60 := @comp _ (opposite _) _ _ _

    section
      variables {C : Category} {a b c : C^.carrier}
      local infixr `⟶` := @hom _ C^.struct
      local infixr `∘op` := @comp _ (opposite C^.struct) _ _ _
      local infixr `∘` := @comp _ C^.struct _ _ _

      theorem compose_op {f : a ⟶ b} {g : b ⟶ c} : f ∘op g = g ∘ f := rfl

      theorem op_op' {ob : Type u} (C : category ob) : opposite (opposite C) = C :=
      category.rec (λ hom comp id assoc idl idr, eq.refl (mk _ _ _ _ _ _)) C

      definition op_op : Opposite (Opposite C) = C :=
        have H : Mk C^.struct = C, from Category.equal C,
        calc Opposite (Opposite C)
              = Mk (opposite (@Category.struct (Opposite C))) : rfl
          ... = Mk (opposite (opposite C^.struct)) : rfl
          ... = Mk C^.struct : congr_arg Mk (op_op' C^.struct)
          ... = C : Category.equal C
    end

  end opposite

  attribute [reducible]
  definition type_category : category Type :=
    mk (λa b, a → b)
      (λ a b c, function.comp)
      (λ a, _root_.id)
      (λ a b c d h g f, eq.symm (function.comp.assoc h g f))
      (λ a b f, function.comp.left_id f)
      (λ a b f, function.comp.right_id f)

  attribute [reducible]
  definition Type_category : Category := Mk type_category

  /-
  section
    open decidable unit empty
    variables {A : Type} [H : decidable_eq A]
    include H

    attribute [reducible]
    definition set_hom (a b : A) := @decidable.rec_on _ _ (H a b) (λ h, empty) (λ h, unit)

    attribute [instance]
    theorem set_hom_subsingleton (a b : A) : subsingleton (set_hom a b) := rec_subsingleton

    attribute [reducible]
    definition set_compose {a b c : A} (g : set_hom b c) (f : set_hom a b) : set_hom a c :=
    decidable.rec_on
      (H b c)
      (λ Hbc g, decidable.rec_on
        (H a b)
        (λ Hab f, rec_on_true (trans Hab Hbc) ⋆)
        (λh f, empty.rec _ f) f)
      (λh (g : empty), empty.rec _ g) g
    omit H

    definition discrete_category (A : Type) [H : decidable_eq A] : category A :=
    mk (λa b, set_hom a b)
      (λ a b c g f, set_compose g f)
      (λ a, decidable.rec_on_true rfl ⋆)
      (λ a b c d h g f, @subsingleton.elim (set_hom a d) _ _ _)
      (λ a b f, @subsingleton.elim (set_hom a b) _ _ _)
      (λ a b f, @subsingleton.elim (set_hom a b) _ _ _)
    local attribute discrete_category [reducible]

    definition Discrete_category (A : Type) [H : decidable_eq A] := Mk (discrete_category A)

    section
      local attribute discrete_category [instance]
      include H
      theorem discrete_category.endomorphism {a b : A} (f : a ⟶ b) : a = b :=
      decidable.rec_on (H a b) (λh f, h) (λh f, empty.rec _ f) f

      theorem discrete_category.discrete {a b : A} (f : a ⟶ b)
        : eq.rec_on (discrete_category.endomorphism f) f = (ID b) :=
      @subsingleton.elim _ !set_hom_subsingleton _ _

      definition discrete_category.rec_on {P : Πa b, a ⟶ b → Type} {a b : A} (f : a ⟶ b)
          (H : ∀a, P a a id) : P a b f :=
      cast (dcongr_arg3 P rfl (discrete_category.endomorphism f)⁻¹
                              (@subsingleton.elim _ !set_hom_subsingleton _ _))⁻¹ (H a)
    end
  end

  section
    open unit bool
    definition category_one := discrete_category unit
    definition Category_one := Mk category_one
    definition category_two := discrete_category bool
    definition Category_two := Mk category_two
  end
  -/

  namespace product
    section
      universe variables u v
      
      open prod
      
      attribute [reducible]
      definition prod_category {obC : Type u} {obD : Type v} (C : category obC) (D : category obD)
          : category (obC × obD) :=
        mk (λ a b, hom (pr₁ a) (pr₁ b) × hom (pr₂ a) (pr₂ b))
          (λ a b c g f, (pr₁ g ∘ pr₁ f , pr₂ g ∘ pr₂ f) )
          (λ a, (ID (pr₁ a), ID (pr₂ a)) )
          (λ a b c d h g f, pair_eq (assoc (pr₁ h) (pr₁ g) (pr₁ f))
            (assoc (pr₂ h) (pr₂ g) (pr₂ f)))
          (λ a b f, prod.eq (id_left (pr₁ f)) (id_left (pr₂ f)))
          (λ a b f, prod.eq (id_right (pr₁ f)) ( id_right (pr₂ f)))

      attribute [reducible]
      definition Prod_category (C D : Category) : Category :=
        Mk (prod_category C^.struct D^.struct)
    end
  end product

  namespace ops
    notation `type`:max := Type_category
    postfix `ᵒᵖ`:max := opposite.Opposite
    infixr `×c`:30 := product.Prod_category
    attribute [instance] type_category
--    attribute category_one [instance]
--    attribute category_two [instance]
    attribute [instance] product.prod_category
  end ops

  namespace opposite
    section
      open ops Functor
      attribute [reducible]
      definition opposite_functor {C : Category} {D : Category}
        (F : C ⇒ D) : Cᵒᵖ ⇒ Dᵒᵖ :=
        @Functor.mk (Cᵒᵖ) (Dᵒᵖ)
          (λ a, F a)
          (λ a b f, F^.morphism f)
          (λ a, respect_id F a)
          (λ a b c g f, by apply @respect_comp C D)
    end
  end opposite

  namespace product
    section
      open prod ops Functor
      attribute [reducible]
      definition prod_functor {C : Category} {C' : Category} {D : Category} {D' : Category}
        (F : C ⇒ D) (G : C' ⇒ D') : C ×c C' ⇒ D ×c D' :=
        Functor.mk (λ a, (F (pr₁ a), G (pr₂ a)) )
          (λ a b f, (F^.morphism (pr₁ f), G^.morphism (pr₂ f)) )
          (λ a, pair_eq (F^.respect_id (pr₁ a)) (G^.respect_id (pr₂ a)) )
          (λ a b c g f, pair_eq (F^.respect_comp (pr₁ g) (pr₁ f))
            (G^.respect_comp (pr₂ g) (pr₂ f)))
    end
  end product

  namespace ops
    infixr `×f`:30 := product.prod_functor
    infixr `ᵒᵖᶠ`:max := opposite.opposite_functor
  end ops

  definition functor_category (C : Category) (D : Category) : category (Functor C D) :=
    mk (λ a b, natural_transformation a b)
      (λ a b c g f, natural_transformation.compose g f)
      (λ a, natural_transformation.ID a)
      (λ a b c d h g f, natural_transformation.assoc h g f)
      (λ a b f, natural_transformation.id_left f)
      (λ a b f, natural_transformation.id_right f)

  attribute [reducible]
  definition Functor_category (C : Category) (D : Category) : Category :=
    Mk (functor_category C D)

end category