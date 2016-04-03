import algebra.category.precategory algebra.category.category
  algebra.category.functor.basic algebra.category.functor.equivalence
  algebra.category.nat_trans
  algebra.category.constructions.product algebra.category.constructions.functor

open eq prod category functor iso prod.ops nat_trans category.hom

set_option unifier.max_steps 50000

definition left_const_product_functor [constructor] (C : Precategory) (a : C)
  : C ⇒ C ×c C :=
functor_prod (constant_functor C a) (functor.id)

definition right_const_product_functor [constructor] (C : Precategory) (a : C)
  : C ⇒ C ×c C :=
functor_prod (functor.id) (constant_functor C a)

definition left_first_tri_product [constructor] {C : Precategory} (tensor_product : C ×c C ⇒ C)
  : C ×c C ×c C ⇒ C :=
tensor_product ∘f ((tensor_product ∘f (pr1_functor ×f (pr1_functor ∘f pr2_functor))) ×f (pr2_functor ∘f pr2_functor))

definition right_first_tri_product [constructor] {C : Precategory} (tensor_product : C ×c C ⇒ C)
  : C ×c C ×c C ⇒ C :=
tensor_product ∘f (pr1_functor ×f (tensor_product ∘f pr2_functor))

/-
structure monoidal_category [class] {C : Precategory}
   (tensor_product : C ×c C ⇒ C) (unit : C)
   (α : left_first_tri_product tensor_product ⟹ right_first_tri_product tensor_product)
   (lambda : tensor_product ∘f (left_const_product_functor C unit) ⟹ 1)
   (ρ : tensor_product ∘f (right_const_product_functor C unit) ⟹ 1) :=
(h1: ∀(a : C ×c C ×c C), (left_first_tri_product tensor_product) a ≅ (right_first_tri_product tensor_product) a)
(h2: ∀(a : C), (tensor_product ∘f (left_const_product_functor C unit)) a ≅ a)
(h3: ∀(a : C), (tensor_product ∘f (right_const_product_functor C unit)) a ≅ a)
-/
--(penta: ∀(a b c d : C),
--  α (α (tensor_product (tensor_product (tensor_product a b) c) d))
--  = (1 ×n α) (α ((α ×n 1) (tensor_product (tensor_product (tensor_product a b) c) d))))
--(tri: ∀(a b : C),
--  (ρ ×n 1) (tensor_product (tensor_product a unit) b)
--  = ((1 ×n lambda) ∘n α) (tensor_product (tensor_produ\ct a unit) b))
--(tri: ∀(a b : C), tensor_product (tensor_product a unit) b ≅ tensor_product (tensor_product a unit) b)
structure monoidal_category [class] (C : Precategory) : Type :=
--  {F G : C ×c C ×c C ⇒ C} : Type :=
(tensor_product : C ×c C ⇒ C)
(unit : C)
(α : right_first_tri_product tensor_product ⟹ left_first_tri_product tensor_product)
--(lambda : tensor_product ∘f (left_const_product_functor C unit) ⟹ functor.id)
--(ρ : tensor_product ∘f (right_const_product_functor C unit) ⟹ functor.id)
/-
これでもよいはずだが、これだと失敗する
(α : (tensor_product ∘f (
  pr1_functor
  ×f (tensor_product ∘f pr2_functor))) ⟹ 
  tensor_product ∘f (
    (tensor_product ∘f (
      pr1_functor
      ×f (pr1_functor ∘f pr2_functor)))
    ×f (pr2_functor ∘f pr2_functor)))
-/
(lambda : (tensor_product ∘f (
  (constant_functor C unit)
  ×f functor.id)) ⟹ functor.id)
(ρ : (tensor_product ∘f (
  functor.id
  ×f (constant_functor C unit))) ⟹ functor.id)
(H1 : ∀(a : C ×c C ×c C), is_iso (α a))
(H2 : ∀(a : C), is_iso (lambda a))
(H3 : ∀(a : C), is_iso (ρ a))
(penta: ∀(a b c d: C),
  (α (tensor_product (a, b), (c, d))) ∘ (α (a, (b, tensor_product (c, d))))
  = (to_fun_hom tensor_product (α (a, (b, c)), ID d))
    ∘ (α (a, (tensor_product (b, c), d)))
    ∘ (to_fun_hom tensor_product (ID a, α (b, (c, d)))))
(tri: ∀(a b : C), to_fun_hom tensor_product (ID a, lambda b)
  = (to_fun_hom tensor_product (ρ a, ID b)) ∘ (α (a, (unit, b))))

-- tp (lambda a, id) と書いたら通らなかったので調査
definition x1 {C : Precategory} (tp : C ×c C ⇒ C) {a : C} (f : hom a a) :=
  tp (f, f)
-- → tp (f, f) は OK
definition x2 {C : Precategory} (tp : C ×c C ⇒ C) (a : C) :=
  tp (ID a, ID a)
-- → id ではなく ID a と書けばよさそう
definition x3 {C : Precategory} (tp : C ×c C ⇒ C) (a unit : C)
  (lambda : tp ∘f (left_const_product_functor C unit) ⟹ 1) :=
  tp (lambda a, ID a)
--check x3
-- → これでOKっぽい

-- f : hom a b のときに f a とできないのか実験
--definition x4 {C : Precategory} {a : C} (f : hom a a) :=
--f a\
-- → f a とはかけない
--definition x5 {C : Precategory} {b : C} (a : C) (f : hom a b) :=
--b
--check x5
-- → こう書けばよさそうだがそもそもその必要がなかった
-- → ちなみに x5 は codomain (cod) と書くのがよさそう

/-
-- α,　lambda, ρ の定義の仕方がわからなかったのでいろいろ実験した痕
definition x1 {C : Precategory} {F G : C ⇒ C} (α : F ⟹ G) (a : C) :=
(natural_map ((@nat_trans.id C C F) ×n α)) a
--(@nat_trans.id C C F) a

check x1
variable (C2 : Precategory)
variable (F2 : C2 ⇒ C2)
variable (G2 : C2 ⇒ C2)
variable (aaaa : F2 ⟹ G2)
--check natural_map (x1 aaaa)
variable (cccc : C2)
check (natural_map (x1 aaaa)) cccc
-/

-- α,　lambda, ρ の定義の仕方がわからなかったのでいろいろ実験した痕
variable (C1 : Precategory)
variable (tp : C1 ×c C1 ⇒ C1)
variable (u : C1)

definition tp31 : C1 ×c C1 ×c C1 ⇒ C1 :=
  tp ∘f ((tp ∘f (pr1_functor ×f (pr1_functor ∘f pr2_functor))) ×f (pr2_functor ∘f pr2_functor))

definition tp32 : C1 ×c C1 ×c C1 ⇒ C1 :=
  tp ∘f (pr1_functor ×f (tp ∘f pr2_functor))

variable (α : (@tp31 C1 tp) ⟹ (@tp32 C1 tp))

example (C : Precategory) : (C ×c C) ×c C ≅c C ×c (C ×c C) := sorry

/-
-- α,　lambda, ρ の定義の仕方がわからなかったのでいろいろ実験した痕
definition c1a (a : C1) : C1 := a
check c1a
-- → 一番基本的なものが通るか確認（当然OK）
definition tpab (a b : C1) : C1 := tp (a, b)
check tpab
-- → tp (a, b) のときに coercion が正しく働いて問題なし
definition tpab' (a b : carrier C1) : carrier C1 := tp (a, b)
-- → 自前でも当然かける
definition tpabc' (a b c : carrier C1) : carrier C1 := tp (tp (a, b), c)
-- → 自前なら当然かける
definition tpabc (a b c : C1) : C1 := tp (tp (a, b), c)
check tpabc
-- → 多段でもcoercion が正しく働く
definition tpabcx (a b c : C1) : C1 := tp (a, tp (b, c))
-- → 多段、こっち側でもcoercion が正しく働く
definition tpabce (a b c : C1) := tp (a, tp (b, c)) ≅ tp (a, tp (b, c))
definition tpabce' := ∀(a b c : C1), tp (a, tp (b, c)) ≅ tp (a, tp (b, c))
-- → coercion が正しく働いて問題なし

definition tpau (a : C1) := tp (a, u) ≅ a
definition tpua (a : C1) := tp (u, a) ≅ a
check tpau
check tpua
-- → coercion が正しく働いて問題なし

definition tpabcx' (aaa : C1 ×c C1 ×c C1) : C1 :=
  tp (aaa.1, tp (aaa.2.1, aaa.2.2))
check tpabcx'
-- → 積の第1および第2要素は a : C1 ×c C1 であればそれぞれ a.1, a.2 とかける

definition tpabcx'' :=
  λ(aaa : C1 ×c C1 ×c C1), tp (aaa.1, tp (aaa.2.1, aaa.2.2))
check tpabcx''
-/
/-
--definition tpahom (aaa : C1 ×c C1 ×c C1) : hom C1 C1 :=
definition tpahom (aaa : C1 ×c C1 ×c C1) :=
  tp (aaa.1, tp (aaa.2.1, aaa.2.2)) ⟶ tp (tp (aaa.1, aaa.2.1), aaa.2.2)
check tpahom
-- → hom a a を勘違いしていた、hom a a は型
-- → したがって射のそれぞれは f : hom a a のような実体となる
-/
/-
definition f1 {C : Precategory} (t : C ×c C ⇒ C) (a : C ×c C ×c C) : C :=
  t (t (a.1, a.2.1), a.2.2)

definition f2 {C : Precategory} (t : C ×c C ⇒ C) (a : C ×c C ×c C) : C :=
  t (a.1, t (a.2.1, a.2.2))
  
check f1
check f2
-/
/-
definition alpha {C : Precategory} (t : C ×c C ⇒ C) :=
nat_trans.mk
  (λ(a : C ×c C ×c C), hom ((f1 t) a) ((f2 t) a))
  (λ a b f,
    calc
      t (a.1, to_fun_ob t (a.2.1, a.2.2)) ⟶ t (b.1, t (b.2.1, b.2.2))
            = t (to_fun_ob t (a.1, a.2.1), a.2.2) ⟶ t (t (b.1, b.2.1), b.2.2) : by rfl)
-- → α を実体として定義できるかと思ったが、hom ((f1 t) a) ((f2 t) a)) のどの射をとるかは
--   個別の定義によるので monoidal_category の定義時点では実体にできない
--   （する必要もなかった）
-/
--check monoidal_category.tensor_product
--check monoidal_category.α
-- 型の確認用