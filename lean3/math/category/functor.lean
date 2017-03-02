import .category
import ...logic.cast
open category

section abbr

variables {C : Category}

private def hom (a b : C) := @hom _ C^.struct a b
private def ID (a : C) := @ID _ C^.struct a
private def comp {a b c : C} (f : hom b c) (g : hom a b) :=
  @comp _ C^.struct _ _ _ f g

end abbr

structure Functor (C D : Category) :=
  (object : C → D)
  (morphism : Π ⦃a b : C⦄, hom a b → hom (object a) (object b))
  (respect_id : Π (a : C), morphism (ID a) = ID (object a))
  (respect_comp : Π ⦃a b c : C⦄ (g : hom b c) (f : hom a b),
    morphism (comp g f) = comp (morphism g) (morphism f))

infixl `⇒`:25 := Functor

namespace Functor
  attribute [irreducible] respect_id
  attribute [irreducible] respect_comp

  variables {A : Category}
  variables {B : Category}
  variables {C : Category}
  variables {D : Category}

  instance functor_object_to_fun : has_coe_to_fun (Functor A B) :=
  { F := λ _, A^.carrier → B^.carrier,
    coe := λ m, m^.object }

/-
  structure Hom (C : Category) :=
  (dom : C)
  (cod : C)
  (hom : hom dom cod)

  instance functor_morphism_to_fun : has_coe_to_fun (Functor A B) :=
  { F := λ m, Hom A → Hom B,
    coe := λ m, λ h, Hom.mk (m^.object (h^.dom)) (m^.object (h^.cod)) (m^.morphism (h^.hom)) }
-/

  attribute [reducible]
  protected definition compose (G : Functor B C) (F : Functor A B) : Functor A C :=
    Functor.mk
      (λx, G (F x))
      (λ a b f, G^.morphism (F^.morphism f))
      (λ a, calc G^.morphism (F^.morphism (ID a))
            = G^.morphism (ID (F a)) : congr_arg (@morphism _ _ G _ _) (respect_id F a)
        ... = ID (G (F a)) : respect_id G (F a))
      (λ a b c g f, calc G^.morphism (F^.morphism (comp g f))
            = G^.morphism (comp (F^.morphism g) (F^.morphism f))
              : congr_arg (@morphism _ _ G _ _) (respect_comp F g f)
        ... = comp (G^.morphism (F^.morphism g)) (G^.morphism (F^.morphism f))
              : respect_comp G (F^.morphism g) (F^.morphism f))

  infixr `∘f`:60 := Functor.compose

  protected theorem assoc (H : Functor C D) (G : Functor B C) (F : Functor A B) :
      H ∘f (G ∘f F) = (H ∘f G) ∘f F := rfl

  attribute [reducible]
  protected definition id {C : Category} : Functor C C :=
  mk (λa, a) (λ a b f, f) (λ a, rfl) (λ a b c f g, rfl)
  attribute [reducible]
  protected definition ID (C : Category) : Functor C C := @Functor.id C

  protected theorem id_left  (F : Functor C D) : (@Functor.id D) ∘f F = F :=
  begin
    cases F,
    apply rfl
  end

  protected theorem id_right (F : Functor C D) : F ∘f (@Functor.id C) = F :=
  begin
    cases F,
    apply rfl
  end

end Functor

namespace category
  open Functor
  attribute [reducible]
  definition category_of_categories : category Category :=
  mk (λ a b, Functor a b)
     (λ a b c g f, Functor.compose g f)
     (λ a, Functor.id)
     (λ a b c d h g f, Functor.assoc h g f)
     (λ a b f, Functor.id_left f)
     (λ a b f, Functor.id_right f)

  def Category_of_categories := Mk category_of_categories

  namespace ops
    notation `Cat`:max := Category_of_categories
  end ops
end category

/-
funext : ∀ {α : Type u} {β : α → Type v} {f₁ f₂ : Π (x : α), β x}, (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂
-/

namespace Functor

  variables {C : Category}
  variables {D : Category}

  protected theorem hequal {F G : C ⇒ D} : Π (Hob : ∀x, F x = G x)
      (Hmor : ∀a b (f : @category.hom _ C^.struct a b),
        F^.morphism f == G^.morphism f), F = G :=
  begin
    intro Hob,
    intro Hmor,
    have Hob' : F^.object = G^.object, from funext Hob,
    have Hmor' : F^.morphism == G^.morphism, from
      hfunext (λ a, hfunext (λ b, hfunext (λ (f : @category.hom _ C^.struct a b), Hmor a b f))),
    begin
      cases F,
      cases G,
      cases Hob',
      cases Hmor',
      apply rfl
    end
  end

end Functor