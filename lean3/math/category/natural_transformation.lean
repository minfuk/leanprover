/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
-/

import .category
import .functor
open category functor

structure natural_transformation {C D : Category} (F G : C ⇒ D) :=
(eta : Π(a : C), @hom _ D^.struct (F a) (G a))
(commute : Π {a b : C} (f : @hom _ C^.struct a b),
  @comp _ D^.struct _ _ _ (G^.morphism f) (eta a) = @comp _ D^.struct _ _ _ (eta b) (F^.morphism f))

infixl `⟹`:25 := natural_transformation -- \==>

namespace natural_transformation
  variables {C : Category}
  variables {D : Category}
  variables {F G H I : Functor C D}

  instance natural_map : has_coe_to_fun (F ⟹ G) :=
  {F := _, coe := λ m, m^.eta}

  theorem naturality (η : F ⟹ G) : Π⦃a b : C⦄ (f : @hom _ C^.struct a b),
    @comp _ D^.struct _ _ _ (G^.morphism f) (η a) =
      @comp _ D^.struct _ _ _ (η b) (F^.morphism f) :=
    take a, take b, η^.commute
  
  protected definition compose (η : G ⟹ H) (θ : F ⟹ G) : F ⟹ H :=
  let infixr `⟶` := λ(a b : D), @hom _ D^.struct a b in
  let infixr `∘` := λ{a b c : D} (f : b ⟶ c) (g : a ⟶ b), @comp _ D^.struct _ _ _ f g in
  let assoc := λ{a b c d : D} h g f, @assoc _ D^.struct a b c d h g f in
  natural_transformation.mk
    (λ a, (η a) ∘ (θ a))
    (λ a b f,
      calc (H^.morphism f) ∘ ((η a) ∘ (θ a))
            = ((H^.morphism f) ∘ (η a))∘  (θ a) : assoc (H^.morphism f) (η a) (θ a)
        ... = ((η b) ∘ (G^.morphism f)) ∘ (θ a) : congr_arg (λx, x ∘ (θ a)) (naturality η f)
        ... = (η b) ∘ ((G^.morphism f) ∘ (θ a)) : eq.symm (assoc (η b) (G^.morphism f) (θ a))
        ... = (η b) ∘ ((θ b) ∘ (F^.morphism f)) : congr_arg (λx, (η b) ∘ x) (naturality θ f)
        ... = ((η b) ∘ (θ b)) ∘ (F^.morphism f) : assoc (η b) (θ b) (F^.morphism f))

  infixr `∘n`:60 := natural_transformation.compose
  protected theorem assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) :
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  let infixr `⟶` := λ(a b : D), @hom _ D^.struct a b in
  let infixr `∘` := λ{a b c : D} (f : b ⟶ c) (g : a ⟶ b), @comp _ D^.struct _ _ _ f g in
  have H : (η₃ ∘n (η₂ ∘n η₁))^.eta = ((η₃ ∘n η₂) ∘n η₁)^.eta, from
    have H1 : ∀(a : C), (η₃ a) ∘ ((η₂ a) ∘ (η₁ a)) = ((η₃ a) ∘ (η₂ a)) ∘ (η₁ a), from
      take a,
      @assoc _ D^.struct _ _ _ _ (η₃ a) (η₂ a) (η₁ a),
    calc (η₃ ∘n (η₂ ∘n η₁))^.eta
          = λ(a : C), (η₃ a) ∘ ((η₂ a) ∘ (η₁ a)) : rfl
      ... = λ(a : C), ((η₃ a) ∘ (η₂ a)) ∘ (η₁ a) : funext H1
      ... = ((η₃ ∘n η₂) ∘n η₁)^.eta : rfl,
  begin
    cases η₃ ∘n (η₂ ∘n η₁),
    cases (η₃ ∘n η₂) ∘n η₁,
    cases H,
    apply rfl
  end

  protected definition id {C D : Category} {F : Functor C D} : natural_transformation F F :=
  mk (λa, @ID _ D^.struct (F a))
    (λa b f,
      calc @comp _ D^.struct _ _ _ (F^.morphism f) (@ID _ D^.struct (F a))
            = (F^.morphism f) : @id_right _ D^.struct _ _ (F^.morphism f)
        ... = @comp _ D^.struct _ _ _ (@ID _ D^.struct (F b)) (F^.morphism f)
          : eq.symm (@id_left _ D^.struct _ _ (F^.morphism f)))
  protected definition ID {C D : Category} (F : Functor C D) : natural_transformation F F := natural_transformation.id

  protected theorem id_left (η : F ⟹ G) : natural_transformation.compose natural_transformation.id η = η :=
  have H : (natural_transformation.compose natural_transformation.id η)^.eta = η^.eta, from
    have H' : ∀(a : C), @comp _ D^.struct _ _ _ (@ID _ D^.struct (G a)) (η a) = (η a), from
      take a,
      @id_left _ D^.struct _ _ (η a),
    funext H',
  begin
    cases (natural_transformation.compose natural_transformation.id η),
    cases η,
    cases H,
    apply rfl
  end

  protected theorem id_right (η : F ⟹ G) : natural_transformation.compose η natural_transformation.id = η :=
  have H : (natural_transformation.compose η natural_transformation.id)^.eta = η^.eta, from
    have H' : ∀(a : C), @comp _ D^.struct _ _ _ (η a) (@ID _ D^.struct (F a)) = (η a), from
      take a,
      @id_right _ D^.struct _ _ (η a),
    funext H',
  begin
    cases natural_transformation.compose η natural_transformation.id,
    cases η,
    cases H,
    apply rfl
  end
end natural_transformation
