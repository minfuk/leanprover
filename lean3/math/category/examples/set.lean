import ..category
import ..functor
import ..construction

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

/-
  variables {b : carrier D}

  example (i : a ⟶ b) (j : b ⟶ a)
    (H1 : j ∘ i = id) (H2 : i ∘ j = id) : a ≅ b :=
    iso.mk i (is_iso.mk _ H1 H2)
  
  definition hom.a [reducible] (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    (h : a ⟶ a) : a ⟶ b
    := (natural_map (to_hom τ) a : (a ⟶ a) → (a ⟶ b)) h
  
  definition hom.b [reducible] (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    (h : b ⟶ a) : b ⟶ b
    := (natural_map (to_hom τ) b : (b ⟶ a) → (b ⟶ b)) h
  
  definition inv.a [reducible] (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    (h : a ⟶ b) : a ⟶ a
    := (natural_map (to_inv τ) a : (a ⟶ b) → (a ⟶ a)) h
  
  definition inv.b [reducible] (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    (h : b ⟶ b) : b ⟶ a
    := (natural_map (to_inv τ) b : (b ⟶ b) → (b ⟶ a)) h

  theorem Ha0 (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    (i : a ⟶ b) (j : b ⟶ a) :
    hom.a τ (j ∘ i) = (hom.b τ j) ∘ i :=
-/
/-
    calc hom.a τ (j ∘ i)
          = hom.a τ ((λx, x ∘ i) j) : rfl
      ... = ((natural_map (to_hom τ) a) ∘ (to_fun_hom (contravariant_hom_functor a) i)) j : rfl
      ... = ((to_fun_hom (contravariant_hom_functor b) i) ∘ (natural_map (to_hom τ) b)) j
        : apd10' j ((@naturality _ _ _ _ (to_hom τ) b a i)⁻¹)
      ... = (λx, x ∘ i) (hom.b τ j) : rfl
      ... = (hom.b τ j) ∘ i : rfl
-/
/-
    apd10' j ((@naturality _ _ _ _ (to_hom τ) b a i)⁻¹)

  theorem Hb0 (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    (i : a ⟶ b) (j : b ⟶ a) :
    inv.b τ (i ∘ j) = (inv.a τ i) ∘ j :=
-/
/-
    calc inv.b τ (i ∘ j)
          = inv.b τ ((λx, x ∘ j) i) : rfl
      ... = ((natural_map (to_inv τ) b) ∘ (to_fun_hom (contravariant_hom_functor b) j)) i : rfl
      ... = ((to_fun_hom (contravariant_hom_functor a) j) ∘ (natural_map (to_inv τ) a)) i
        : apd10' i ((@naturality _ _ _ _ (to_inv τ) a b j)⁻¹)
      ... = (λx, x ∘ j) (inv.a τ i) : rfl
      ... = (inv.a τ i) ∘ j : rfl
-/
/-
    apd10' i ((@naturality _ _ _ _ (to_inv τ) a b j)⁻¹)

  theorem Ha1 (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    : (to_inv τ) ∘n (to_hom τ) = 1 :=
-/
/-
    calc (to_inv τ) ∘n (to_hom τ)
          = (@inverse (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _) ∘n (to_hom τ) : rfl
      ... = 1 : @left_inverse  (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _
-/
/-
    @left_inverse  (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _

  theorem Hb1 (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    : (to_hom τ) ∘n (to_inv τ) = 1 :=
-/
/-
    calc (to_hom τ) ∘n (to_inv τ)
          = (to_hom τ) ∘n (@inverse (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _) : rfl
      ... = 1 : @right_inverse  (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _
-/
/-
      @right_inverse  (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _
-/
/-
theorem Ha3 (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
  : (natural_map (to_inv τ) b) ∘ (natural_map (to_hom τ) a) =
    @homset _ D a a :=
  by apply left_inv

theorem Ha4 (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
  : ((to_hom τ⁻¹) a) ∘ ((to_hom τ) a) =
    @ID _ set.{v} (to_fun_ob (contravariant_hom_functor a) a) :=
  rfl
-/
/-
  example (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    : (natural_map (to_inv τ) a) ∘ (natural_map (to_hom τ) a) =
      (natural_map ((to_inv τ) ∘ (to_hom τ)) a) := rfl

  example (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    : (to_inv τ) = (to_hom τ)⁻¹ := rfl

  theorem Ha (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    (h : a ⟶ a) : inv.a τ (hom.a τ h) = h :=
    have Hx : natural_map ((to_inv τ) ∘n (to_hom τ)) a = λx, x, from
      calc natural_map ((to_inv τ) ∘n (to_hom τ)) a
            = natural_map (@nat_trans.id Dᵒᵖ set.{v} (contravariant_hom_functor a)) a :
              (Ha1 τ) ▸ rfl
        ... = λx, x : rfl,
    calc inv.a τ (hom.a τ h)
          = (natural_map ((to_inv τ) ∘n (to_hom τ)) a) h : rfl
      ... = (λx, x) h : apd10' h Hx
      ... = h : rfl

  theorem Hb (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    (h : b ⟶ b) : hom.b τ (inv.b τ h) = h :=
    have Hx : natural_map ((to_hom τ) ∘n (to_inv τ)) b = λx, x, from
      calc natural_map ((to_hom τ) ∘n (to_inv τ)) b
            = natural_map (@nat_trans.id Dᵒᵖ set.{v} (contravariant_hom_functor b)) b :
              (Hb1 τ) ▸ rfl
        ... = λx, x : rfl,
    calc hom.b τ (inv.b τ h)
          = (natural_map ((to_hom τ) ∘n (to_inv τ)) b) h : rfl
      ... = (λx, x) h : apd10' h Hx
      ... = h : rfl

set_option unifier.max_steps 50000

  example (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    : a ≅ b :=
    let i := hom.a τ (ID a) in
    let j := inv.b τ (ID b) in
    have H1 : j ∘ i = id, from
      calc j ∘ i
            = inv.a τ (hom.a τ (j ∘ i)) : (Ha τ (j ∘ i))⁻¹
        ... = inv.a τ ((hom.b τ j) ∘ i) : Ha0 τ i j
        ... = inv.a τ ((hom.b τ (inv.b τ (ID b))) ∘ i) : rfl
        ... = inv.a τ ((ID b) ∘ i) : Hb τ (ID b)
        ... = inv.a τ (i) : id_left i
        ... = inv.a τ (hom.a τ (ID a)) : rfl
        ... = ID a : Ha τ (ID a),
    have H2 : i ∘ j = id, from
      calc i ∘ j
            = hom.b τ (inv.b τ (i ∘ j)) : (Hb τ (i ∘ j))⁻¹
        ... = hom.b τ ((inv.a τ i) ∘ j) : Hb0 τ i j
        ... = hom.b τ ((inv.a τ (hom.a τ (ID a))) ∘ j) : rfl
        ... = hom.b τ ((ID a) ∘ j) : Ha τ (ID a)
        ... = hom.b τ (j) : id_left j
        ... = hom.b τ (inv.b τ (ID b)) : rfl
        ... = ID b : Hb τ (ID b),
    iso.mk i (is_iso.mk _ H1 H2)
-/

end Functor