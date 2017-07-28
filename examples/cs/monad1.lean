structure Monad [class] (M : Type → Type) :=
  (return : Π {A : Type}, A → M A)
  (bind : Π {A B : Type}, M A → (A → M B) → M B)
  (left_identity : Π {A B : Type} (a : A) (f : A → M B),
    (bind (return a) f) = (f a))
  (right_identity : Π {A : Type} (m : M A), bind m return = m)
  (associativity : Π {A B C : Type} (m : M A) (f : A → M B) (g : B → M C),
    bind (bind m f) g = bind m (λx, bind (f x) g))

namespace maybe

  definition return {A : Type} (x : A) := option.some x

  definition bind {A B : Type} : option A → (A → option B) → option B
  | bind (option.none) f := (option.none)
  | bind (option.some x) f := f x

  theorem left_identity {A B : Type} (a : A) (f : A → option B) :
    bind (return a) f = f a :=
  begin
    apply rfl
  end

  theorem right_identity {A : Type} (m : option A) :
    bind m return = m :=
  begin
    cases m,
    apply rfl,
    apply rfl
  end

  theorem associativity {A B C : Type} (m : option A)
    (f : A → option B) (g : B → option C) :
    bind (bind m f) g = bind m (λx, bind (f x) g) :=
  begin
    cases m,
    apply rfl,
    apply rfl
  end
end maybe

definition Maybe [instance] {A : Type} : Monad option :=
Monad.mk (@maybe.return) (@maybe.bind)
  (@maybe.left_identity) (@maybe.right_identity)
  (@maybe.associativity)

