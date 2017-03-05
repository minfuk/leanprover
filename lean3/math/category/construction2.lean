import .category
import .functor
import .construction

namespace category

  namespace diag
    open category.ops

    attribute [reducible]
    definition diag_functor {C : Category} : C ⇒ (C ×c C) :=
    Functor.mk
      (λa, (a, a) )
      (λa b f, (f, f) )
      (λa, rfl)
      (λa b c g f, rfl)

  end diag

  namespace const

    attribute [reducible]
    definition constant_functor (C : Category) {D : Category} (d : D) : C ⇒ D :=
    Functor.mk
      (λc, d)
      (λc c' f, @ID _ D^.struct d)
      (λc, rfl)
      (λa b c g f, eq.symm (@id_left _ D^.struct _ _ (@ID _ D^.struct d)))

  end const

end category