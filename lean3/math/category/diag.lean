import .category
import .functor
import .construction

namespace category.diag

  open category.ops

  attribute [reducible]
  definition diag_functor {C : Category} : C ⇒ (C ×c C) :=
  Functor.mk
    (λa, (a, a) )
    (λa b f, (f, f) )
    (λa, rfl)
    (λa b c g f, rfl)

end category.diag