import types.trunc types.pi arity algebra.category.default

open eq is_trunc pi equiv is_equiv iso funext

section entry20061028

end entry20061028

section entry20070111

end entry20070111

section entry20070125

end entry20070125

section entry20070306



end entry20070306

section entry20070413



end entry20070413

section entry20070507



end entry20070507

section entry20070508



end entry20070508

section entry20070524



end entry20070524

section entry20070821
  open category functor nat_trans iso

/-
  variables {ob : Type} [C : precategory ob]
  
  variables {a : ob}
  
  example (x y : ob) (f : x ⟶ y) :=
    let P := λ(z : ob), @precategory.hom _ C z a in
    take u,
    -- P (y : ob) : (= y ⟶ a : cset)
    -- P (f : x ⟶ y) : (P y) → (P x) (写像)
    assume H1 : u ∈ P y, -- u : y ⟶ a
    assume H2 : (P f) u = u ∘ f,  -- f : x ⟶ y, u ∘ f : x ⟶ a (∈ P x), (P f) : P y → P x (写像)
    have H3 : P id = id, from
      take v,
      calc (P id) v = v ∘ id : rfl,
                ... = v : id,
      
    have H4 : P (g ∘ f) = (P f) ∘ (P g), from
      take v,
      calc (P (g ∘ f)) v = v ∘ (g ∘ f) : rfl,
                     ... = (v ∘ g) ∘ f : assoc,
                     ... = (P f) (v ∘ g) : rfl,
                     ... = (P f) ((P g) v) : rfl,
                     ... = ((P f) ∘ (P g)) v : rfl,
      ∀x, f x = g x → f = g, by apply funext
-/

  universe variables u v
  variables {D : Precategory.{u v}}
  variables {a : carrier D}

  definition to_fun_ob' (z : carrier Dᵒᵖ) := @homset _ D z a

  definition to_fun_hom' {x y : carrier Dᵒᵖ} (f : x ⟶ y) :
    (to_fun_ob' x) ⟶ (to_fun_ob' y) := λ(u : @homset _ D x a), u ∘ f

  theorem respect_id' (x : carrier Dᵒᵖ) :
    to_fun_hom' (@precategory.ID _ (Dᵒᵖ) x)
      = @precategory.ID _ set.{v} (@to_fun_ob' D a x) :=
    have H : ∀(i : to_fun_ob' x),
      (to_fun_hom' (@precategory.ID _ (Dᵒᵖ) x)) i = i, from
      take i : to_fun_ob' x,
      calc to_fun_hom' (@precategory.ID _ (Dᵒᵖ) x) i
            = i ∘ (@precategory.ID _ (Dᵒᵖ) x) : rfl
        ... = i : id_right,
    eq_of_homotopy H

  theorem respect_comp' {x y z : carrier Dᵒᵖ} (g : y ⟶ z) (f : x ⟶ y) :
    to_fun_hom' (@precategory.comp _ (Dᵒᵖ) x y z g f)
      = @precategory.comp _ set.{v} (@to_fun_ob' D a x)
        (@to_fun_ob' D a y) (@to_fun_ob' D a z)
        (to_fun_hom' g) (to_fun_hom' f) :=
    have H : ∀(i : to_fun_ob' x),
      (to_fun_hom' (@precategory.comp _ (Dᵒᵖ) x y z g f)) i =
        (@precategory.comp _ set.{v} (@to_fun_ob' D a x)
          (@to_fun_ob' D a y) (@to_fun_ob' D a z)
          (to_fun_hom' g) (to_fun_hom' f)) i, from
        take i : to_fun_ob' x,
        calc (to_fun_hom' (@precategory.comp _ (Dᵒᵖ) x y z g f)) i
              = i ∘ (@precategory.comp _ (Dᵒᵖ) x y z g f) : rfl
          ... = (to_fun_hom' g) (i ∘ f) : assoc
          ... = (@precategory.comp _ set.{v} (@to_fun_ob' D a x)
                  (@to_fun_ob' D a y) (@to_fun_ob' D a z)
                  (to_fun_hom' g) (to_fun_hom' f)) i : rfl,
    eq_of_homotopy H

  -- universe変数をつけないとうまくいかない
  example : functor Dᵒᵖ set.{v} :=
    functor.mk
      (@to_fun_ob' D a)
      (@to_fun_hom' D a)
      (@respect_id' D a)
      (@respect_comp' D a)

  definition to_fun_ob'' (z : carrier D) := @homset _ D a z

  definition to_fun_hom'' {x y : carrier D} (f : x ⟶ y) :
    (to_fun_ob'' x) ⟶ (to_fun_ob'' y) := λ(u : @homset _ D a x), f ∘ u

  theorem respect_id'' (x : carrier D) :
    to_fun_hom'' (@precategory.ID _ D x)
      = @precategory.ID _ set.{v} (@to_fun_ob'' D a x) :=
    have H : ∀(i : to_fun_ob'' x),
      (to_fun_hom'' (@precategory.ID _ D x)) i = i, from
      take i : to_fun_ob'' x,
      calc to_fun_hom'' (@precategory.ID _ D x) i
            = (@precategory.ID _ D x) ∘ i : rfl
        ... = i : id_left,
    eq_of_homotopy H

  theorem respect_comp'' {x y z : carrier D} (g : y ⟶ z) (f : x ⟶ y) :
    to_fun_hom'' (@precategory.comp _ D x y z g f)
      = @precategory.comp _ set.{v} (@to_fun_ob'' D a x)
        (@to_fun_ob'' D a y) (@to_fun_ob'' D a z)
        (to_fun_hom'' g) (to_fun_hom'' f) :=
    have H : ∀(i : to_fun_ob'' x),
      (to_fun_hom'' (@precategory.comp _ D x y z g f)) i =
        (@precategory.comp _ set.{v} (@to_fun_ob'' D a x)
          (@to_fun_ob'' D a y) (@to_fun_ob'' D a z)
          (to_fun_hom'' g) (to_fun_hom'' f)) i, from
        take i : to_fun_ob'' x,
        calc (to_fun_hom'' (@precategory.comp _ D x y z g f)) i
              = (@precategory.comp _ D x y z g f) ∘ i : rfl
          ... = (to_fun_hom'' g) (f ∘ i) : assoc
          ... = (@precategory.comp _ set.{v} (@to_fun_ob'' D a x)
                  (@to_fun_ob'' D a y) (@to_fun_ob'' D a z)
                  (to_fun_hom'' g) (to_fun_hom'' f)) i : rfl,
    eq_of_homotopy H

  example : functor D set.{v} :=
    functor.mk
      (@to_fun_ob'' D a)
      (@to_fun_hom'' D a)
      (@respect_id'' D a)
      (@respect_comp'' D a)

  -- 反変Hom関手
  definition contravariant_hom_functor (a : carrier D) : Dᵒᵖ ⇒ set.{v} :=
    functor.mk
      (@to_fun_ob' D a)
      (@to_fun_hom' D a)
      (@respect_id' D a)
      (@respect_comp' D a)

  -- 共変Hom関手
  definition covariant_hom_functor (a : carrier D) : D ⇒ set.{v} :=
    functor.mk
      (@to_fun_ob'' D a)
      (@to_fun_hom'' D a)
      (@respect_id'' D a)
      (@respect_comp'' D a)

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
    calc hom.a τ (j ∘ i)
          = hom.a τ ((λx, x ∘ i) j) : rfl
      ... = ((natural_map (to_hom τ) a) ∘ (to_fun_hom (contravariant_hom_functor a) i)) j : rfl
      ... = ((to_fun_hom (contravariant_hom_functor b) i) ∘ (natural_map (to_hom τ) b)) j
        : apd10' j ((@naturality _ _ _ _ (to_hom τ) b a i)⁻¹)
      ... = (λx, x ∘ i) (hom.b τ j) : rfl
      ... = (hom.b τ j) ∘ i : rfl

  theorem Hb0 (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    (i : a ⟶ b) (j : b ⟶ a) :
    inv.b τ (i ∘ j) = (inv.a τ i) ∘ j :=
    calc inv.b τ (i ∘ j)
          = inv.b τ ((λx, x ∘ j) i) : rfl
      ... = ((natural_map (to_inv τ) b) ∘ (to_fun_hom (contravariant_hom_functor b) j)) i : rfl
      ... = ((to_fun_hom (contravariant_hom_functor a) j) ∘ (natural_map (to_inv τ) a)) i
        : apd10' i ((@naturality _ _ _ _ (to_inv τ) a b j)⁻¹)
      ... = (λx, x ∘ j) (inv.a τ i) : rfl
      ... = (inv.a τ i) ∘ j : rfl

  theorem Ha1 (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    : (to_inv τ) ∘n (to_hom τ) = 1 :=
    calc (to_inv τ) ∘n (to_hom τ)
          = (@inverse (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _) ∘n (to_hom τ) : rfl
      ... = 1 : @left_inverse  (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _

  theorem Hb1 (τ : (contravariant_hom_functor a) ≅ (contravariant_hom_functor b))
    : (to_hom τ) ∘n (to_inv τ) = 1 :=
    calc (to_hom τ) ∘n (to_inv τ)
          = (to_hom τ) ∘n (@inverse (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _) : rfl
      ... = 1 : @right_inverse  (Dᵒᵖ ⇒ set.{v}) _ _ _ (to_hom τ) _

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

end entry20070821

section entry20070827



end entry20070827

section entry20080121



end entry20080121

section entry20080123



end entry20080123

section entry20090430



end entry20090430

section entry20090525



end entry20090525

section entry20090817



end entry20090817

section entry20091030



end entry20091030

section entry20091111



end entry20091111

section entry20091112



end entry20091112

section entry20091127



end entry20091127

section entry20091201



end entry20091201

section entry20100210



end entry20100210

section entry20100305



end entry20100305


section entry20100821



end entry20100821

section entry20101102



end entry20101102

section entry20110520



end entry20110520

section entry20110603



end entry20110603

section entry20110628



end entry20110628

section entry20110721



end entry20110721
