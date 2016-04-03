import data.list data.prod
open list
open prod
open eq.ops

structure Monad [class] (M : Type → Type) :=
  (return : Π {A : Type}, A → M A)
  (bind : Π {A B : Type}, M A → (A → M B) → M B)
  (left_identity : Π {A B : Type} (a : A) (f : A → M B),
    (bind (return a) f) = (f a))
  (right_identity : Π {A : Type} (m : M A), bind m return = m)
  (associativity : Π {A B C : Type} (m : M A) (f : A → M B) (g : B → M C),
    bind (bind m f) g = bind m (λx, bind (f x) g))

/- ⟪⦃
-- 'option' has already defined.
inductive option (A : Type) : Type :=
| none {} : option A
| some    : A → option A
-/

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


namespace listM

  definition return {A : Type} (x : A) := x :: nil

  definition bind {A B : Type} : list A → (A → list B) → list B
  | bind nil f := nil
  | bind (x :: xs) f := (f x) ++ (bind xs f)

  theorem left_identity {A B : Type} (a : A) (f : A → list B) :
    bind (return a) f = f a :=
  begin
--    calc bind A B (return A a) f = bind A B (a :: nil) f : rfl
--                             ... = (f a) ++ (bind A B nil f) : rfl
--                             ... = (f a) ++ nil : rfl
--                             ... = f a : append_nil_right
    apply append_nil_right
  end

  theorem right_identity {A : Type} (m : list A) :
    bind m return = m :=
  begin
    induction m,
    apply rfl,
    calc bind (a :: a_1) (return) = (a :: nil) ++ (bind a_1 (return)) : rfl
                              ... = (a :: nil) ++ a_1 : v_0
                              ... = a :: (nil ++ a_1) : append_cons
                              ... = a :: a_1 : append_nil_left
  end

  lemma lemma_1 {B C : Type} (m1 m2 : list B) (g : B → list C) :
    bind (m1 ++ m2) g = (bind m1 g) ++ (bind m2 g) :=
  begin
    induction m1,
    apply rfl,
    induction m2,
    calc bind (a :: a_1 ++ nil) g = bind (a :: (a_1 ++ nil)) g : append_cons
                              ... = g a ++ bind (a_1 ++ nil) g : rfl
                              ... = g a ++ (bind a_1 g ++ bind nil g) : v_0
                              ... = (g a ++ bind a_1 g) ++ bind nil g : append.assoc
                              ... = (bind (a :: a_1) g) ++ bind nil g : rfl,
    calc bind (a :: a_1 ++ a_2 :: a_3) g = bind (a :: (a_1 ++ a_2 :: a_3)) g : append_cons
                                     ... = g a ++ bind (a_1 ++ a_2 :: a_3) g : rfl
                                     ... = g a ++ (bind a_1 g ++ bind (a_2 :: a_3) g) : v_0_1
                                     ... = (g a ++ bind a_1 g) ++ bind (a_2 :: a_3) g : append.assoc
                                     ... = bind (a :: a_1) g ++ bind (a_2 :: a_3) g : rfl
  end

  lemma lemma_2 {A B C : Type} (a : A)
    (f : A → list B) (g : B → list C) :
    (bind (f a) g) = (bind (a :: nil) (λ (x : A), bind (f x) g)) :=
  begin
    apply eq.symm,
    apply append_nil_right
    /-
    calc bind A C (a :: nil) (λ (x : A), bind B C (f x) g) = ((λ (x : A), bind B C (f x) g) a) ++ nil : rfl
                                                       ... = (bind B C (f a) g) ++ nil : rfl
                                                       ... = bind B C (f a) g : append_nil_right
    -/
  end

  lemma lemma_3 {A C : Type} (m1 m2 : list A) (h : A → list C) :
    (bind m1 h) ++ (bind m2 h) = bind (m1 ++ m2) h :=
  begin
    apply eq.symm,
    apply lemma_1
  end

  theorem associativity {A B C : Type} (m : list A)
    (f : A → list B) (g : B → list C) :
    bind (bind m f) g = bind m (λx, bind (f x) g) :=
  begin
    induction m,
    apply rfl,
    calc bind (bind (a :: a_1) f) g = bind ((f a) ++ (bind a_1 f)) g : rfl
                                ... = (bind (f a) g) ++ (bind (bind a_1 f) g) : lemma_1
                                ... = (bind (f a) g) ++ (bind a_1 (λ (x : A), bind (f x) g)) : v_0
--                              ... = (bind a (λ (x : A), bind (f x) g)) ++ (bind (bind a_1 f) g) : v_0
                                ... = (bind (a :: nil) (λ (x : A), bind (f x) g)) ++ (bind a_1 (λ (x : A), bind (f x) g)) : lemma_2
                                ... = bind ((a :: nil) ++ a_1) (λ (x : A), bind (f x) g) : lemma_3
                                ... = bind (a :: (nil ++ a_1)) (λ (x : A), bind (f x) g) : append_cons
                                ... = bind (a :: a_1) (λ (x : A), bind (f x) g) : append_nil_left
  end

end listM

definition List [instance] {A : Type} : Monad list :=
Monad.mk (@listM.return) (@listM.bind)
  (@listM.left_identity) (@listM.right_identity)
  (@listM.associativity)


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

  example {S A : Type} (m : stateM S A) (s : S) :
    (pr1 (m s), pr2 (m s)) = (m s) :=
  begin
    apply eta
  end
  
  example {A B C : Type} (f : A → B × C) :
    (λ(a : A),(f a)) = f :=
  begin
    apply rfl
  end
  
  example {A B C : Type} (f : A → B × C) (a : A) :
    (pr1 (f a), pr2 (f a)) = (f a) :=
  begin
    apply eta
  end

  lemma lemma_4 {A B C : Type} (f : A → B × C) :
    ∀(a : A),((pr1 (f a), pr2 (f a)) = (f a)) :=
  begin
    take a : A,
    show (pr1 (f a), pr2 (f a)) = (f a), from
      begin
        apply eta
      end
  end

  axiom axiom_1 {A B : Type} (f g : A → B) : (∀(a : A), (f a = g a)) → (f = g)

  lemma lemma_5 {A B C : Type} (f : A → B × C) :
    (λ(a : A),(pr1 (f a), pr2 (f a))) = (λ(a : A),(f a)) :=
  begin
    apply axiom_1,
    apply lemma_4,
  end

  theorem right_identity {S A : Type} (m : stateM S A) :
    bind m return = m :=
  begin
    calc bind m return = λ(s : S), (pr1 (m s), pr2 (m s)) : rfl
                   ... = λ(s : S), (m s) : lemma_5
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
