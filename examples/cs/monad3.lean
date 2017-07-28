import data.list
open list

structure Monad [class] (M : Type → Type) :=
  (return : Π {A : Type}, A → M A)
  (bind : Π {A B : Type}, M A → (A → M B) → M B)
  (left_identity : Π {A B : Type} (a : A) (f : A → M B),
    (bind (return a) f) = (f a))
  (right_identity : Π {A : Type} (m : M A), bind m return = m)
  (associativity : Π {A B C : Type} (m : M A) (f : A → M B) (g : B → M C),
    bind (bind m f) g = bind m (λx, bind (f x) g))

namespace listM

  definition return {A : Type} (x : A) := x :: nil

  definition bind {A B : Type} : list A → (A → list B) → list B
  | bind nil f := nil
  | bind (x :: xs) f := (f x) ++ (bind xs f)

  theorem left_identity {A B : Type} (a : A) (f : A → list B) :
    bind (return a) f = f a :=
  begin
    apply append_nil_right
  end

  theorem right_identity {A : Type} (m : list A) :
    bind m return = m :=
  begin
    induction m,
    apply rfl,
    calc bind (a :: a_1) (return)
          = (a :: nil) ++ (bind a_1 (return)) : rfl
      ... = (a :: nil) ++ a_1 : v_0
      ... = a :: (nil ++ a_1) : append_cons
      ... = a :: a_1 : append_nil_left
  end

  lemma lemma1 {B C : Type} (m1 m2 : list B) (g : B → list C) :
    bind (m1 ++ m2) g = (bind m1 g) ++ (bind m2 g) :=
  begin
    induction m1,
    apply rfl,
    induction m2,
    calc bind (a :: a_1 ++ nil) g
          = bind (a :: (a_1 ++ nil)) g : append_cons
      ... = g a ++ bind (a_1 ++ nil) g : rfl
      ... = g a ++ (bind a_1 g ++ bind nil g) : v_0
      ... = (g a ++ bind a_1 g) ++ bind nil g : append.assoc
      ... = (bind (a :: a_1) g) ++ bind nil g : rfl,
    calc bind (a :: a_1 ++ a_2 :: a_3) g
          = bind (a :: (a_1 ++ a_2 :: a_3)) g : append_cons
      ... = g a ++ bind (a_1 ++ a_2 :: a_3) g : rfl
      ... = g a ++ (bind a_1 g ++ bind (a_2 :: a_3) g) : v_0_1
      ... = (g a ++ bind a_1 g) ++ bind (a_2 :: a_3) g : append.assoc
      ... = bind (a :: a_1) g ++ bind (a_2 :: a_3) g : rfl
  end

  lemma lemma2 {A B C : Type} (a : A)
    (f : A → list B) (g : B → list C) :
    (bind (f a) g) = (bind (a :: nil) (λ (x : A), bind (f x) g)) :=
  begin
    apply eq.symm,
    apply append_nil_right
  end

  lemma lemma3 {A C : Type} (m1 m2 : list A) (h : A → list C) :
    (bind m1 h) ++ (bind m2 h) = bind (m1 ++ m2) h :=
  begin
    apply eq.symm,
    apply lemma1
  end

  theorem associativity {A B C : Type} (m : list A)
    (f : A → list B) (g : B → list C) :
    bind (bind m f) g = bind m (λx, bind (f x) g) :=
  begin
    induction m,
    apply rfl,
    calc bind (bind (a :: a_1) f) g
          = bind ((f a) ++ (bind a_1 f)) g : rfl
      ... = (bind (f a) g) ++ (bind (bind a_1 f) g) : lemma1
      ... = (bind (f a) g) ++ (bind a_1 (λ (x : A), bind (f x) g)) : v_0
      ... = (bind (a :: nil) (λ (x : A), bind (f x) g)) ++ (bind a_1 (λ (x : A), bind (f x) g)) : lemma2
      ... = bind ((a :: nil) ++ a_1) (λ (x : A), bind (f x) g) : lemma3
      ... = bind (a :: (nil ++ a_1)) (λ (x : A), bind (f x) g) : append_cons
      ... = bind (a :: a_1) (λ (x : A), bind (f x) g) : append_nil_left
  end

end listM

definition List [instance] {A : Type} : Monad list :=
Monad.mk (@listM.return) (@listM.bind)
  (@listM.left_identity) (@listM.right_identity)
  (@listM.associativity)
