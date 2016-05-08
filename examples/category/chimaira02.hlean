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
  open category

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

end entry20070821

section entry20070827



end entry20070827

section entry20080121



end entry20080121