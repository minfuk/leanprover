import ..category
import ..functor
import ..construction
import ..morphism

universe variables u

namespace set

  structure Set :=
  (carrier : Type u)
  (struct : set carrier)

  instance Set_to_sort : has_coe_to_sort Set :=
  {S := _, coe := λ S, S^.carrier}

end set

namespace category
  
  namespace set
    open function
    open set

    definition set_category : category Set :=
      mk (λ x y, x → y)
        (λ x y z f g, f ∘ g)
        (λ x a, a)
        (λ x y z w f g h, @comp.assoc _ _ _ _ f g h)
        (λ x y f, comp.left_id f)
        (λ x y f, comp.right_id f)
    
    definition Set_category := Mk set_category

    variables {ob : Type u} [C : category ob]
    include C

    attribute [reducible]
    definition homset (x y : ob) : Set :=
    Set.mk (hom x y) (λ f, true)

  end set

end category

namespace Functor

  open category
  open category.opposite
  open category.ops
  open category.set
  open function

  variables {D : Category}
  variables {a : Dᵒᵖ^.carrier}

  definition contra_hom_functor_ob (z : Dᵒᵖ^.carrier) := @homset _ (Dᵒᵖ^.struct) a z

  definition contra_hom_functor_hom {x y : Dᵒᵖ^.carrier}
    (f : @hom _ (Dᵒᵖ^.struct) x y)
    : (contra_hom_functor_ob x) → (contra_hom_functor_ob y)
    := λ u, @category.comp _ (Dᵒᵖ^.struct) a _ _ f u

  attribute [reducible]
  private def comp_op_cat {x y z : Dᵒᵖ^.carrier}
    (f : @hom _ (Dᵒᵖ^.struct) y z) (g : @hom _ (Dᵒᵖ^.struct) x y)
    := @category.comp _ (Dᵒᵖ^.struct) x y z f g

  theorem contra_hom_functor_resp_id (x : Dᵒᵖ^.carrier) :
    contra_hom_functor_hom (@ID _ (Dᵒᵖ^.struct) x)
      = @ID _ Set_category^.struct (@contra_hom_functor_ob _ a x) :=
    let id' := (@ID _ (Dᵒᵖ^.struct) x) in
    funext (take x' : @contra_hom_functor_ob _ _ x,
      calc contra_hom_functor_hom id' x'
            = comp_op_cat id' x' : rfl
        ... = x' : @id_left _ (Dᵒᵖ^.struct) _ _ x')

  theorem contra_hom_functor_resp_comp {x y z : Dᵒᵖ^.carrier}
    (g : @hom _ (Dᵒᵖ^.struct) y z) (f : @hom _ (Dᵒᵖ^.struct) x y) :
    contra_hom_functor_hom (comp_op_cat g f)
      = @category.comp _ Set_category^.struct (@contra_hom_functor_ob D a x)
        (@contra_hom_functor_ob D a y) (@contra_hom_functor_ob D a z)
        (contra_hom_functor_hom g) (contra_hom_functor_hom f) :=
    funext (take i : contra_hom_functor_ob x,
        calc (contra_hom_functor_hom (comp_op_cat g f)) i
              = comp_op_cat (comp_op_cat g f) i : rfl
          ... = comp_op_cat g (comp_op_cat f i)
                : eq.symm (@assoc _ (Dᵒᵖ^.struct) _ _ _ _ g f i)
          ... = (contra_hom_functor_hom g) (comp_op_cat f i) : rfl
          ... = (@category.comp _ Set_category^.struct _ _ _
                  (contra_hom_functor_hom g) (contra_hom_functor_hom f)) i : rfl)

  -- 反変Hom関手
  definition contravariant_hom_functor (a : D^.carrier)
    : Dᵒᵖ ⇒ Set_category :=
    Functor.mk
      (@contra_hom_functor_ob D a)
      (@contra_hom_functor_hom D a)
      (@contra_hom_functor_resp_id D a)
      (@contra_hom_functor_resp_comp D a)

  definition co_hom_functor_ob (z : D^.carrier) := @homset _ D^.struct a z

  definition co_hom_functor_hom {x y : D^.carrier}
    (f : @hom _ D^.struct x y)
    : (co_hom_functor_ob x) → (co_hom_functor_ob y)
    := λ u, @category.comp _ D^.struct a _ _ f u

  attribute [reducible]
  private def comp_cat {x y z : D^.carrier}
    (f : @hom _ D^.struct y z) (g : @hom _ D^.struct x y)
    := @category.comp _ D^.struct x y z f g

  theorem co_hom_functor_resp_id (x : D^.carrier) :
    co_hom_functor_hom (@category.ID _ D^.struct x)
      = @category.ID _ Set_category^.struct (@co_hom_functor_ob D a x) :=
    let id' := (@category.ID _ D^.struct x) in
    funext (take x' : co_hom_functor_ob x,
      calc co_hom_functor_hom id' x'
            = comp_cat id' x' : rfl
        ... = x' : @id_left _ (D^.struct) _ _ x')

  theorem co_hom_functor_resp_comp {x y z : D^.carrier}
    (g : @hom _ D^.struct y z) (f : @hom _ D^.struct x y) :
    co_hom_functor_hom (comp_cat g f)
      = @category.comp _ Set_category^.struct (@co_hom_functor_ob D a x)
        (@co_hom_functor_ob D a y) (@co_hom_functor_ob D a z)
        (co_hom_functor_hom g) (co_hom_functor_hom f) :=
    funext (take i : co_hom_functor_ob x,
        calc (co_hom_functor_hom (comp_cat g f)) i
              = comp_cat (comp_cat g f) i : rfl
          ... = comp_cat g (comp_cat f i)
                : eq.symm (@assoc _ D^.struct _ _ _ _ g f i)
          ... = (co_hom_functor_hom g) (comp_cat f i) : rfl
          ... = (@category.comp _ Set_category^.struct _ _ _
                  (co_hom_functor_hom g) (co_hom_functor_hom f)) i : rfl)

  -- 共変Hom関手
  definition covariant_hom_functor (a : D^.carrier)
    : D ⇒ Set_category :=
    Functor.mk
      (@co_hom_functor_ob D a)
      (@co_hom_functor_hom D a)
      (@co_hom_functor_resp_id D a)
      (@co_hom_functor_resp_comp D a)

end Functor

namespace hom_functor
  
  open category
  open category.opposite
  open category.ops
  open category.set
  open function
  open Functor
  open morphism

  variables {D : Category}
  variables {a b : D^.carrier}

  theorem hom_functor_iso_object_iso
    (τ : @isomorphic _ (@Functor_category (Dᵒᵖ) Set_category)^.struct
      (contravariant_hom_functor a) (contravariant_hom_functor b))
    : @isomorphic _ D^.struct a b :=
    let τ_iso := τ^.iso in
    let τ_iso_inv := (@inverse _ (@Functor_category (Dᵒᵖ) Set_category)^.struct _ _ (τ^.iso) τ^.is_iso) in
    let i := τ_iso^.eta in
    let j := τ_iso_inv^.eta in
    let hom_a := λ (h : @hom _ D^.struct a a), (i a : (@hom _ D^.struct a a) → (@hom _ D^.struct a b)) h in
    let hom_b := λ (h : @hom _ D^.struct b a), (i b : (@hom _ D^.struct b a) → (@hom _ D^.struct b b)) h in
    let inv_a := λ (h : @hom _ D^.struct a b), (j a : (@hom _ D^.struct a b) → (@hom _ D^.struct a a)) h in
    let inv_b := λ (h : @hom _ D^.struct b b), (j b : (@hom _ D^.struct b b) → (@hom _ D^.struct b a)) h in
    let ia := hom_a (@ID _ D^.struct a) in
    let jb := inv_b (@ID _ D^.struct b) in
    have Ha0 : τ_iso_inv ∘n τ_iso
      = @natural_transformation.id (Dᵒᵖ) Set_category (contravariant_hom_functor a), from
      @inverse_compose _ (@Functor_category (Dᵒᵖ) Set_category)^.struct _ _ τ_iso τ^.is_iso,
    have Ha : ∀(h : @hom _ D^.struct a a), inv_a (hom_a h) = h, from
      take h,
      calc inv_a (hom_a h)
            = ((τ_iso_inv ∘n τ_iso) a) h : rfl
        ... = ((@natural_transformation.id (Dᵒᵖ) Set_category (contravariant_hom_functor a)) a) h
          : by rw Ha0
        ... = (λx, x) h : rfl
        ... = h : rfl,
    have Hb0 : τ_iso ∘n τ_iso_inv
      = @natural_transformation.id (Dᵒᵖ) Set_category (contravariant_hom_functor b), from
      @compose_inverse _ (@Functor_category (Dᵒᵖ) Set_category)^.struct _ _ τ_iso τ^.is_iso,
    have Hb : ∀(h : @hom _ D^.struct b b), hom_b (inv_b h) = h, from
      take h,
      calc hom_b (inv_b h)
            = ((τ_iso ∘n τ_iso_inv) b) h : rfl
        ... = ((@natural_transformation.id (Dᵒᵖ) Set_category (contravariant_hom_functor b)) b) h
          : by rw Hb0
        ... = (λx, x) h : rfl
        ... = h : rfl,
    have Ha0 : hom_a (@category.comp _ D^.struct _ _ _ jb ia)
      = @category.comp _ D^.struct _ _ _ (hom_b jb) ia, from
      calc hom_a (@category.comp _ D^.struct _ _ _ jb ia)
            = hom_a ((λx, @category.comp _ D^.struct _ _ _ x ia) jb) : rfl
        ... = ((τ_iso^.eta a) ∘ ((contravariant_hom_functor a)^.morphism ia)) jb : rfl
        ... = (((contravariant_hom_functor b)^.morphism ia) ∘ (τ_iso^.eta b)) jb
          : eq.symm (congr_fun (τ_iso^.commute ia) jb)
        ... = (λx, @category.comp _ D^.struct _ _ _ x ia) (hom_b jb) : rfl
        ... = @category.comp _ D^.struct _ _ _ (hom_b jb) ia : rfl,
    have Hb0 : inv_b (@category.comp _ D^.struct _ _ _ ia jb)
      = @category.comp _ D^.struct _ _ _ (inv_a ia) jb, from
      calc inv_b (@category.comp _ D^.struct _ _ _ ia jb)
            = inv_b ((λx, @category.comp _ D^.struct _ _ _ x jb) ia) : rfl
        ... = ((τ_iso_inv^.eta b) ∘ ((contravariant_hom_functor b)^.morphism jb)) ia : rfl
        ... = (((contravariant_hom_functor a)^.morphism jb) ∘ (τ_iso_inv^.eta a)) ia
          : eq.symm (congr_fun (τ_iso_inv^.commute jb) ia)
        ... = (λx, @category.comp _ D^.struct _ _ _ x jb) (inv_a ia) : rfl
        ... = @category.comp _ D^.struct _ _ _ (inv_a ia) jb : rfl,
    have H₁ : @category.comp _ D^.struct _ _ _ jb ia = @ID _ D^.struct a, from
      calc @category.comp _ D^.struct _ _ _ jb ia
            = inv_a (hom_a (@category.comp _ D^.struct _ _ _ jb ia))
              : eq.symm (Ha (@category.comp _ D^.struct _ _ _ jb ia))
        ... = inv_a (@category.comp _ D^.struct _ _ _ (hom_b jb) ia) : by rw Ha0
        ... = inv_a (@category.comp _ D^.struct _ _ _ (hom_b (inv_b (@ID _ D^.struct b))) ia) : rfl
        ... = inv_a (@category.comp _ D^.struct _ _ _ (@ID _ D^.struct b) ia) : by rw Hb (@ID _ D^.struct b)
        ... = inv_a (ia) : by rw @id_left _ D^.struct _ _ ia
        ... = inv_a (hom_a (@ID _ D^.struct a)) : rfl
        ... = @ID _ D^.struct a : Ha (@ID _ D^.struct a),
    have H₂ : @category.comp _ D^.struct _ _ _ ia jb = @ID _ D^.struct b, from
      calc @category.comp _ D^.struct _ _ _ ia jb
            = hom_b (inv_b (@category.comp _ D^.struct _ _ _ ia jb))
              : eq.symm (Hb (@category.comp _ D^.struct _ _ _ ia jb))
        ... = hom_b (@category.comp _ D^.struct _ _ _ (inv_a ia) jb) : by rw Hb0
        ... = hom_b (@category.comp _ D^.struct _ _ _ (inv_a (hom_a (@ID _ D^.struct a))) jb) : rfl
        ... = hom_b (@category.comp _ D^.struct _ _ _ (@ID _ D^.struct a) jb) : by rw Ha (@ID _ D^.struct a)
        ... = hom_b (jb) : by rw @id_left _ D^.struct _ _ jb
        ... = hom_b (inv_b (@ID _ D^.struct b)) : rfl
        ... = @ID _ D^.struct b : Hb (@ID _ D^.struct b),
    @isomorphic.mk _ D^.struct _ _ ia (is_iso.mk H₁ H₂)

end hom_functor
