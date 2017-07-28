import data.prod
open prod

structure Monad [class] (M : Type → Type) :=
  (return : Π {A : Type}, A → M A)
  (bind : Π {A B : Type}, M A → (A → M B) → M B)
  (left_identity : Π {A B : Type} (a : A) (f : A → M B),
    (bind (return a) f) = (f a))
  (right_identity : Π {A : Type} (m : M A), bind m return = m)
  (associativity : Π {A B C : Type} (m : M A) (f : A → M B) (g : B → M C),
    bind (bind m f) g = bind m (λx, bind (f x) g))

definition stateM (S A : Type) := S → A × S

namespace state

  definition return {S A : Type} (x : A) := λ(s : S), (x, s)

  definition bind {S A B : Type} (c : stateM S A) (f : A → stateM S B) : stateM S B :=
    λ(s : S), (f (pr1 (c s))) (pr2 (c s))

  theorem left_identity {S A B : Type} (a : A) (f : A → stateM S B) :
    bind (return a) f = f a :=
  begin
    apply rfl
  end

  lemma lemma1 {A B C : Type} (f : A → B × C) :
    (λ(a : A),(pr1 (f a), pr2 (f a))) = (λ(a : A),(f a)) :=
  begin
    apply funext,
    take a : A,
    show (pr1 (f a), pr2 (f a)) = (f a), from
      begin
        apply eta,
      end
  end

  theorem right_identity {S A : Type} (m : stateM S A) :
    bind m return = m :=
  begin
    calc bind m return
          = λ(s : S), (pr1 (m s), pr2 (m s)) : rfl
      ... = λ(s : S), (m s) : lemma1
  end

  theorem associativity {S A B C : Type} (m : stateM S A)
    (f : A → stateM S B) (g : B → stateM S C) :
    bind (bind m f) g = bind m (λx, bind (f x) g) :=
  begin
    apply rfl
  end

end state

definition State [instance] {S A : Type} : Monad (stateM S):=
Monad.mk (@state.return S) (@state.bind S)
  (@state.left_identity S) (@state.right_identity S)
  (@state.associativity S)

check eta
check funext