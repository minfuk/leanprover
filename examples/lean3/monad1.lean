class Monad (M : Type → Type) :=
  (return : Π {A : Type}, A → M A)
  (bind : Π {A B : Type}, M A → (A → M B) → M B)
  (left_identity : Π {A B : Type} (a : A) (f : A → M B),
    (bind (return a) f) = (f a))
  (right_identity : Π {A : Type} (m : M A), bind m return = m)
  (associativity : Π {A B C : Type} (m : M A) (f : A → M B) (g : B → M C),
    bind (bind m f) g = bind m (λx, bind (f x) g))

namespace maybe

  def return {A : Type} (x : A) := option.some x

  def bind2 {A B : Type} : option A → (A → option B) → option B
  | (option.none) f := (option.none)
  | (option.some x) f := f x

  theorem left_identity {A B : Type} (a : A) (f : A → option B) :
    bind2 (return a) f = f a :=
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

instance Maybe {A : Type} : Monad option :=
Monad.mk (@maybe.return) (@maybe.bind2)
  (@maybe.left_identity) (@maybe.right_identity)
  (@maybe.associativity)

