import .category
import .functor
import .natural_transformation

namespace category

  structure adjoint {C D : Category} (F : C ⇒ D) (G : D ⇒ C) :=
  (η : Functor.id ⟹ G ∘f F)
  (ε : F ∘f G ⟹ Functor.id)
  (H : Π(c : C), @category.comp _ D^.struct _ _ _ (ε (F c)) (F^.morphism (η c))
    = @category.ID _ D^.struct (F c))
  (K : Π(d : D), @category.comp _ C^.struct _ _ _ (G^.morphism (ε d)) (η (G d))
    = @category.ID _ C^.struct (G d))
  
  infix ` ⊣ `:55 := adjoint

  attribute [class]
  structure is_left_adjoint {C D : Category} (F : C ⇒ D) :=
  (G : D ⇒ C)
  (η : Functor.id ⟹ G ∘f F)
  (ε : F ∘f G ⟹ Functor.id)
  (H : Π(c : C), @category.comp _ D^.struct _ _ _ (ε (F c)) (F^.morphism (η c))
    = @category.ID _ D^.struct (F c))
  (K : Π(d : D), @category.comp _ C^.struct _ _ _ (G^.morphism (ε d)) (η (G d))
    = @category.ID _ C^.struct (G d))



end category