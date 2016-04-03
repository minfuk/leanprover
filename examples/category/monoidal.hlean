import algebra.category.precategory algebra.category.category
  algebra.category.functor.basic algebra.category.functor.equivalence
  algebra.category.nat_trans
  algebra.category.constructions.product algebra.category.constructions.functor

open eq prod category functor iso prod.ops nat_trans category.hom

set_option unifier.max_steps 50000

definition left_first_tri_product [constructor] {C : Precategory} (tensor_product : C ×c C ⇒ C)
  : C ×c C ×c C ⇒ C :=
tensor_product ∘f ((tensor_product ∘f (pr1_functor ×f (pr1_functor ∘f pr2_functor))) ×f (pr2_functor ∘f pr2_functor))

definition right_first_tri_product [constructor] {C : Precategory} (tensor_product : C ×c C ⇒ C)
  : C ×c C ×c C ⇒ C :=
tensor_product ∘f (pr1_functor ×f (tensor_product ∘f pr2_functor))

structure monoidal_category [class] (C : Precategory) : Type :=
(tensor_product : C ×c C ⇒ C)
(unit : C)
(α : right_first_tri_product tensor_product ⟹ left_first_tri_product tensor_product)
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


