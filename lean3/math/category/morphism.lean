import .category
import ..relation

open eq
open category

namespace morphism

  universe variable u

  variables {ob : Type u} [C : category ob]
  include C
  variables {a b c : ob}

  inductive is_section (f : a ⟶ b)
  | mk : ∀{g}, g ∘ f = id → is_section
  
  inductive is_retraction (f : a ⟶ b)
  | mk : ∀{g}, f ∘ g = id → is_retraction

  inductive is_iso (f : a ⟶ b)
  | mk : ∀{g}, g ∘ f = id → f ∘ g = id → is_iso

  attribute [class] is_section
  attribute [class] is_retraction
  attribute [class] is_iso

  definition retraction_of (f : a ⟶ b) [H : is_section f] : hom b a :=
  is_section.rec (λg h, g) H

  definition section_of (f : a ⟶ b) [H : is_retraction f] : hom b a :=
  is_retraction.rec (λg h, g) H

  definition inverse (f : a ⟶ b) [H : is_iso f] : hom b a :=
  is_iso.rec (λg h1 h2, g) H

  postfix `⁻¹` := inverse

  theorem inverse_compose (f : a ⟶ b) [H : is_iso f] : f⁻¹ ∘ f = id :=
  is_iso.rec (λg h1 h2, h1) H

  theorem compose_inverse (f : a ⟶ b) [H : is_iso f] : f ∘ f⁻¹ = id :=
  is_iso.rec (λg h1 h2, h2) H

  theorem retraction_compose (f : a ⟶ b) [H : is_section f] : retraction_of f ∘ f = id :=
  is_section.rec (λg h, h) H

  theorem compose_section (f : a ⟶ b) [H : is_retraction f] : f ∘ section_of f = id :=
  is_retraction.rec (λg h, h) H

  attribute [instance]
  theorem iso_imp_retraction (f : a ⟶ b) [H : is_iso f] : is_section f :=
  is_section.mk (inverse_compose f)

  attribute [instance]
  theorem iso_imp_section (f : a ⟶ b) [H : is_iso f] : is_retraction f :=
  is_retraction.mk (compose_inverse f)

  attribute [instance]
  theorem id_is_iso : is_iso (ID a) :=
  is_iso.mk (id_compose a) (id_compose a)

  attribute [instance]
  theorem inverse_is_iso (f : a ⟶ b) [H : is_iso f] : is_iso (f⁻¹) :=
  is_iso.mk (compose_inverse f) (inverse_compose f)

  theorem left_inverse_eq_right_inverse {f : a ⟶ b} {g g' : hom b a}
      (Hl : g ∘ f = id) (Hr : f ∘ g' = id) : g = g' :=
    calc g = g ∘ id : by rewrite id_right
      ... = g ∘ f ∘ g' : by rewrite -Hr
      ... = (g ∘ f) ∘ g' : by rewrite assoc
      ... = id ∘ g' : by rewrite Hl
      ... = g' : by rewrite id_left

  section
    variables {f : a ⟶ b} {g : b ⟶ c} {h : b ⟶ a}

    theorem retraction_eq_intro [H : is_section f] (H2 : f ∘ h = id) : retraction_of f = h :=
    left_inverse_eq_right_inverse (retraction_compose f) H2

    theorem section_eq_intro [H : is_retraction f] (H2 : h ∘ f = id) : section_of f = h :=
    eq.symm (left_inverse_eq_right_inverse H2 (compose_section f))

    theorem inverse_eq_intro_right [H : is_iso f] (H2 : f ∘ h = id) : f⁻¹ = h :=
    left_inverse_eq_right_inverse (inverse_compose f) H2

    theorem inverse_eq_intro_left [H : is_iso f] (H2 : h ∘ f = id) : f⁻¹ = h :=
    eq.symm (left_inverse_eq_right_inverse H2 (compose_inverse f))

    theorem section_eq_retraction (f : a ⟶ b) [Hl : is_section f] [Hr : is_retraction f]
      : retraction_of f = section_of f :=
    retraction_eq_intro (compose_section f)

    theorem section_retraction_imp_iso (f : a ⟶ b) [Hl : is_section f] [Hr : is_retraction f]
      : is_iso f :=
    have H : section_of f ∘ f = id, from subst (section_eq_retraction f) (retraction_compose f),
    is_iso.mk H (compose_section f)

    theorem inverse_unique (H H' : is_iso f) : @inverse _ _ _ _ f H = @inverse _ _ _ _ f H' :=
    @inverse_eq_intro_left _ _ _ _ _ _ H (inverse_compose f)

    theorem inverse_involutive (f : a ⟶ b) [H : is_iso f] : (f⁻¹)⁻¹ = f :=
    inverse_eq_intro_right (inverse_compose f)

    theorem retraction_of_id : retraction_of (ID a) = id :=
    retraction_eq_intro (id_compose a)

    theorem section_of_id : section_of (ID a) = id :=
    section_eq_intro (id_compose a)

    theorem iso_of_id : (ID a)⁻¹ = id :=
    inverse_eq_intro_left (id_compose a)

    attribute [instance]
    theorem composition_is_section [Hf : is_section f] [Hg : is_section g]
        : is_section (g ∘ f) :=
    is_section.mk
      (calc
        (retraction_of f ∘ retraction_of g) ∘ g ∘ f
              = retraction_of f ∘ retraction_of g ∘ g ∘ f   : by rewrite -assoc
          ... = retraction_of f ∘ (retraction_of g ∘ g) ∘ f : by rewrite (assoc _ g f)
          ... = retraction_of f ∘ id ∘ f                    : by rewrite retraction_compose
          ... = retraction_of f ∘ f                         : by rewrite id_left
          ... = id                                          : by rewrite retraction_compose)

    attribute [instance]
    theorem composition_is_retraction [Hf : is_retraction f] [Hg : is_retraction g]
        : is_retraction (g ∘ f) :=
    is_retraction.mk
      (calc
        (g ∘ f) ∘ section_of f ∘ section_of g
              = g ∘ f ∘ section_of f ∘ section_of g   : by rewrite -assoc
          ... = g ∘ (f ∘ section_of f) ∘ section_of g : by rewrite -assoc
          ... = g ∘ id ∘ section_of g                 : by rewrite compose_section
          ... = g ∘ section_of g                      : by rewrite id_left
          ... = id                                    : by rewrite compose_section)

    attribute [instance]
    theorem composition_is_iso [Hf : is_iso f] [Hg : is_iso g] : is_iso (g ∘ f) :=
    section_retraction_imp_iso (g ∘ f)

  end

  structure isomorphic (a b : ob) :=
    (iso : a ⟶ b)
    [is_iso : is_iso iso]

  infix `≅`:50 := morphism.isomorphic

  namespace isomorphic
    open relation
    theorem refl (a : ob) : a ≅ a := mk id
    theorem symm  ⦃a b : ob⦄ (H : a ≅ b) : b ≅ a := @mk _ _ _ _
      (@inverse _ _ _ _ (iso H) (is_iso H)) (@inverse_is_iso _ _ _ _ (iso H) (is_iso H))
    theorem trans ⦃a b c : ob⦄ (H1 : a ≅ b) (H2 : b ≅ c) : a ≅ c := @mk _ _ _ _
      (iso H2 ∘ iso H1) (@composition_is_iso _ _ _ _ _ _ _ (is_iso H1) (is_iso H2))

    variables {ob' : Type} [C' : category ob']
    omit C
    include C'

    attribute [instance]
    theorem is_equivalence_eq (T : Type) : is_equivalence (isomorphic : ob' → ob' → Type) :=
      is_equivalence.mk refl symm trans
    
    omit C'
    include C
  end isomorphic

  attribute [class]
  inductive is_mono (f : a ⟶ b) : Prop
  | mk : (∀c (g h : hom c a), f ∘ g = f ∘ h → g = h) → is_mono

  attribute [class]
  inductive is_epi (f : a ⟶ b) : Prop
  | mk : (∀c (g h : hom b c), g ∘ f = h ∘ f → g = h) → is_epi

  section
    variables {f : a ⟶ b}

    theorem mono_elim [H : is_mono f] {g h : c ⟶ a} (H2 : f ∘ g = f ∘ h) : g = h :=
    match H with
      is_mono.mk H3 := H3 c g h H2
    end

    theorem epi_elim [H : is_epi f] {g h : b ⟶ c} (H2 : g ∘ f = h ∘ f) : g = h :=
    match H with
      is_epi.mk H3 := H3 c g h H2
    end
  end

  attribute [instance]
  theorem section_is_mono (f : a ⟶ b) [H : is_section f] : is_mono f :=
  is_mono.mk
    (λ c g h H, calc
        g = id ∘ g                    : by rewrite id_left
      ... = (retraction_of f ∘ f) ∘ g : by rewrite -(retraction_compose f)
      ... = (retraction_of f ∘ f) ∘ h : by rewrite [-assoc, H, -assoc]
      ... = id ∘ h                    : by rewrite retraction_compose
      ... = h                         : by rewrite id_left)

  attribute [instance]
  theorem retraction_is_epi (f : a ⟶ b) [H : is_retraction f] : is_epi f :=
  is_epi.mk
    (λ c g h H, calc
        g = g ∘ id                 : by rewrite id_right
      ... = g ∘ f ∘ section_of f   : by rewrite -(compose_section f)
      ... = h ∘ f ∘ section_of f   : by rewrite [assoc, H, -assoc]
      ... = h ∘ id                 : by rewrite compose_section
      ... = h                      : by rewrite id_right)

  theorem id_is_mono : is_mono (ID a) := section_is_mono (ID a)
  theorem id_is_epi  : is_epi  (ID a) := retraction_is_epi (ID a)

  section
    variables {f : a ⟶ b} {g : b ⟶ c}
    
    attribute [instance]
    theorem composition_is_mono [Hf : is_mono f] [Hg : is_mono g] : is_mono (g ∘ f) :=
    is_mono.mk
      (λ d h₁ h₂ H,
        have H2 : g ∘ (f ∘ h₁) = g ∘ (f ∘ h₂),
        begin
          rewrite [assoc, assoc], exact H
        end,
        mono_elim (mono_elim H2))

    attribute [instance]
    theorem composition_is_epi  [Hf : is_epi f] [Hg : is_epi g] : is_epi  (g ∘ f) :=
    is_epi.mk
      (λ d h₁ h₂ H,
        have H2 : (h₁ ∘ g) ∘ f = (h₂ ∘ g) ∘ f,
        begin
          rewrite [-assoc, -assoc], exact H
        end,
        epi_elim (epi_elim H2))
  end

end morphism