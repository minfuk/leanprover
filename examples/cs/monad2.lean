structure Monad [class] (M : Type → Type) :=
  (return : Π {A : Type}, A → M A)
  (bind : Π {A B : Type}, M A → (A → M B) → M B)
  (left_identity : Π {A B : Type} (a : A) (f : A → M B),
    (bind (return a) f) = (f a))
  (right_identity : Π {A : Type} (m : M A), bind m return = m)
  (associativity : Π {A B C : Type} (m : M A) (f : A → M B) (g : B → M C),
    bind (bind m f) g = bind m (λx, bind (f x) g))

definition contM (R A : Type) := (A → R) → R

namespace cont

  definition return {R A : Type} (x : A) := λ(k : A → R), k x

  definition bind {R A B : Type} (c : contM R A) (f : A → contM R B) : contM R B :=
    λ(k : B → R), c (λ(a : A), f a k)

  theorem left_identity {R A B : Type} (a : A) (f : A → contM R B) :
    bind (return a) f = f a :=
  begin
    apply rfl
  end

  theorem right_identity {R A : Type} (m : contM R A) :
    bind m return = m :=
  begin
    apply rfl
  end

  theorem associativity {R A B C : Type} (m : contM R A)
    (f : A → contM R B) (g : B → contM R C) :
    bind (bind m f) g = bind m (λx, bind (f x) g) :=
  begin
    apply rfl
  end

end cont

definition Cont [instance] {R A : Type} : Monad (contM R):=
Monad.mk (@cont.return R) (@cont.bind R)
  (@cont.left_identity R) (@cont.right_identity R)
  (@cont.associativity R)
