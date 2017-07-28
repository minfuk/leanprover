import .category
import .morphism

namespace iso
  open category
  open morphism

  universe variables u

  variables {ob : Type u} [C : category ob]
  variables {a b : ob}
  include C

  attribute [class]
  structure split_mono (f : a ⟶ b) :=
  {retraction_of : b ⟶ a}
  (retraction_comp : retraction_of ∘ f = id)

  attribute [class]
  structure split_epi (f : a ⟶ b) :=
  {section_of : b ⟶ a}
  (section_map : f ∘ section_of = id)

  attribute [class]
  structure is_iso (f : a ⟶ b) :=
  (inverse : b ⟶ a)
  (left_inverse : inverse ∘ f = id)
  (right_inverse : f ∘ inverse = id)

  attribute [reducible] is_iso.inverse

  theorem left_inverse_eq_right_inverse {f : a ⟶ b} {g g' : hom b a}
      (Hl : g ∘ f = id) (Hr : f ∘ g' = id) : g = g' :=
  calc g
        = g ∘ (ID b) : eq.symm (id_right g)
    ... = g ∘ (f ∘ g') : congr_arg (λ x, g ∘ x) (eq.symm Hr)
    ... = (g ∘ f) ∘ g' : assoc g f g'
    ... = id ∘ g' : congr_arg (λ x, x ∘ g') Hl
    ... = g' : id_left g'

end iso