import algebra.category.precategory algebra.category.category
  algebra.category.functor.basic algebra.category.functor.equivalence
  algebra.category.nat_trans
  algebra.category.constructions.product algebra.category.constructions.functor

open eq prod category functor iso prod.ops nat_trans category.hom is_trunc

lemma assoc4a {C : Precategory} {a b c d e : C}
  (i : d ⟶ e) (h : c ⟶ d) (g : b ⟶ c) (f : a ⟶ b) :
  (i ∘ h ∘ g) ∘ f = i ∘ h ∘ (g ∘ f) :=
  calc (i ∘ h ∘ g) ∘ f
        = i ∘ ((h ∘ g) ∘ f) : assoc' i (h ∘ g) f
    ... = i ∘ h ∘ (g ∘ f) : assoc' h g f

lemma assoc4b {C : Precategory} {a b c d e : C}
  (i : d ⟶ e) (h : c ⟶ d) (g : b ⟶ c) (f : a ⟶ b) :
  i ∘ (h ∘ g ∘ f) = (i ∘ h) ∘ g ∘ f := assoc i h (g ∘ f)

lemma assoc4c {C : Precategory} {a b c d e : C}
  (i : d ⟶ e) (h : c ⟶ d) (g : b ⟶ c) (f : a ⟶ b) :
  i ∘ (h ∘ g) ∘ f = (i ∘ h) ∘ (g ∘ f) :=
  calc i ∘ (h ∘ g) ∘ f
        = i ∘ h ∘ (g ∘ f) : assoc' h g f
    ... = (i ∘ h) ∘ (g ∘ f) : assoc i h (g ∘ f)

lemma cancel_right {C : Precategory} {a b : C}
  {ea : a ⟶ a} {eb : b ⟶ b} {f : a ⟶ b}
  (Ha : ea ∘ ea = ea) (Hf : eb ∘ f ∘ ea = f) : f ∘ ea = f :=
  have Hf' : f = eb ∘ f ∘ ea, from Hf⁻¹,
  calc f ∘ ea
        = (eb ∘ f ∘ ea) ∘ ea : Hf'
    ... = eb ∘ f ∘ (ea ∘ ea) : assoc4a eb f ea ea
    ... = eb ∘ f ∘ ea : Ha
    ... = f : Hf

lemma cancel_left {C : Precategory} {a b : C}
  {ea : a ⟶ a} {eb : b ⟶ b} {f : a ⟶ b}
  (Hb : eb ∘ eb = eb) (Hf : eb ∘ f ∘ ea = f) : eb ∘ f = f :=
  have Hf' : f = eb ∘ f ∘ ea, from Hf⁻¹,
  calc eb ∘ f
        = eb ∘ (eb ∘ f ∘ ea) : Hf'
    ... = (eb ∘ eb) ∘ f ∘ ea : assoc4b eb eb f ea
    ... = eb ∘ f ∘ ea : Hb
    ... = f : Hf

lemma simp_comp_simp {C : Precategory} {a b c : C}
  {ea : a ⟶ a} {eb : b ⟶ b} {ec : c ⟶ c} {f : a ⟶ b} {g : b ⟶ c}
  (iea : ea ∘ ea = ea) (ieb : eb ∘ eb = eb) (iec : ec ∘ ec = ec)
  (Hf : eb ∘ f ∘ ea = f) (Hg : ec ∘ g ∘ eb = g) :
  ec ∘ (g ∘ f) ∘ ea = g ∘ f :=
  have Hf' : f ∘ ea = f, from cancel_right iea Hf,
  have Hg' : ec ∘ g = g, from cancel_left iec Hg,
  calc ec ∘ (g ∘ f) ∘ ea
        = (ec ∘ g) ∘ (f ∘ ea) : assoc4c ec g f ea
    ... = (ec ∘ g) ∘ f : Hf'
    ... = g ∘ f : Hg'

structure karoubi_object (C : Precategory) : Type :=
  (dom : C)
  (endo : dom ⟶ dom)
  (idempo : endo ∘ endo = endo)

variables {C : Precategory}

abbreviation endo := @karoubi_object.endo
definition karoubi_to_obj := @karoubi_object.endo

local attribute karoubi_to_obj [coercion]

structure karoubi_morphism (a b : karoubi_object C) :=
  (mor : (karoubi_object.dom a) ⟶ (karoubi_object.dom b))
  (simp : (endo b) ∘ mor ∘ (endo a) = mor)

abbreviation mor := @karoubi_morphism.mor
definition karoubi_to_hom := @karoubi_morphism.mor

local attribute karoubi_to_hom [coercion]

theorem karoubi_hom_eq {a b : karoubi_object C} (f f' : karoubi_morphism a b)
  (H : karoubi_to_hom f = karoubi_to_hom f') : f = f' :=
  begin
    cases f,
    cases f',
    cases H,
    apply ap (karoubi_morphism.mk mor_1),
    apply is_prop.elim,
  end

definition karoubi_comp {a b c : karoubi_object C}
  (g : karoubi_morphism b c) (f : karoubi_morphism a b) :=
  karoubi_morphism.mk
    (mor g ∘ mor f)
    (simp_comp_simp (karoubi_object.idempo a)
      (karoubi_object.idempo b) (karoubi_object.idempo c)
      (karoubi_morphism.simp f) (karoubi_morphism.simp g))

theorem karoubi_assoc {a b c d : karoubi_object C}
  (h : karoubi_morphism c d) (g : karoubi_morphism b c) (f : karoubi_morphism a b) :
  karoubi_comp h (karoubi_comp g f) = karoubi_comp (karoubi_comp h g) f :=
  karoubi_hom_eq (karoubi_comp h (karoubi_comp g f)) (karoubi_comp (karoubi_comp h g) f)
    (assoc (mor h) (mor g) (mor f))

definition karoubi_ID (a : karoubi_object C) :=
  karoubi_morphism.mk
    (endo a)
    (show (endo a) ∘ (endo a) ∘ (endo a) = endo a, from
      calc (endo a) ∘ (endo a) ∘ (endo a)
            = (endo a) ∘ (endo a) : karoubi_object.idempo a
        ... = (endo a) : karoubi_object.idempo a)

theorem karoubi_id_left {a b : karoubi_object C}
  (f : karoubi_morphism a b) :
  karoubi_comp (karoubi_ID b) f = f :=
  karoubi_hom_eq (karoubi_comp (karoubi_ID b) f) f
    (cancel_left (karoubi_object.idempo b) (karoubi_morphism.simp f))

theorem karoubi_id_right {a b : karoubi_object C}
  (f : karoubi_morphism a b) :
  karoubi_comp f (karoubi_ID a) = f :=
  karoubi_hom_eq (karoubi_comp f (karoubi_ID a)) f
    (cancel_right (karoubi_object.idempo a) (karoubi_morphism.simp f))

theorem karoubi_is_set_hom (a b : karoubi_object C)
  : is_set (karoubi_morphism a b) :=
begin
  apply is_trunc_equiv_closed_rev,
  have H : karoubi_morphism a b ≃ (Σ f : karoubi_object.dom a ⟶ karoubi_object.dom b,
    endo b ∘ f ∘ endo a = f),
    begin
      fapply equiv.MK,
      { intro x, induction x, constructor, assumption, },
      { intro y, induction y, constructor, assumption, },
      { intro y, induction y, reflexivity, },
      { intro x, induction x, reflexivity, },
    end,
  apply H,
end

definition karoubi_category (C : Precategory) :
  precategory (karoubi_object C) :=
  precategory.mk'
    (λ a b, karoubi_morphism a b)
    (λ a b c f g, karoubi_comp f g)
    (λ a, karoubi_ID a)
    (λ a b c d f g h, karoubi_assoc f g h)
    (λ a b c d f g h, (karoubi_assoc f g h)⁻¹)
    (λ a b f, karoubi_id_left f)
    (λ a b f, karoubi_id_right f)
    (λ a, karoubi_id_left (karoubi_ID a))
    (λ a b, karoubi_is_set_hom a b)

