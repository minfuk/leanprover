import ..category

namespace karoubi
  universe variable u

  open category

  section
    variables {ob : Type u}
    variables {C : category ob}

    structure karoubi_object (C : category ob) :=
    (dom : ob)
    (endo : dom ⟶ dom)
    (idempo : endo ∘ endo = endo)

    structure karoubi_morphism (a b : karoubi_object C) :=
    (mor : (karoubi_object.dom a) ⟶ (karoubi_object.dom b))
    (simp : b^.endo ∘ mor ∘ a^.endo = mor)

    variables {a b c d : karoubi_object C}

    lemma cancel_right [C : category ob] {a b : ob}
      {ea : a ⟶ a} {eb : b ⟶ b} {f : a ⟶ b}
      (Ha : ea ∘ ea = ea) (Hf : eb ∘ f ∘ ea = f) : f ∘ ea = f :=
      calc f ∘ ea
            = (eb ∘ f ∘ ea) ∘ ea : by rewrite Hf
        ... = eb ∘ ((f ∘ ea) ∘ ea) : by rewrite (assoc eb (f ∘ ea) ea)
        ... = eb ∘ f ∘ (ea ∘ ea) : by rewrite (assoc f ea ea)
        ... = eb ∘ f ∘ ea : by rewrite Ha
        ... = f : Hf

    lemma cancel_left [C : category ob] {a b : ob}
      {ea : a ⟶ a} {eb : b ⟶ b} {f : a ⟶ b}
      (Hb : eb ∘ eb = eb) (Hf : eb ∘ f ∘ ea = f) : eb ∘ f = f :=
      calc eb ∘ f
            = eb ∘ (eb ∘ f ∘ ea) : by rewrite Hf
        ... = (eb ∘ eb) ∘ (f ∘ ea) : by rewrite (assoc eb eb (f ∘ ea))
        ... = (eb ∘ eb) ∘ f ∘ ea : by rewrite (assoc (eb ∘ eb) f ea)
        ... = eb ∘ f ∘ ea : by rewrite Hb
        ... = f : Hf

    lemma simp_comp_simp [C : category ob] {a b c : ob}
      {ea : a ⟶ a} {eb : b ⟶ b} {ec : c ⟶ c} {f : b ⟶ c} {g : a ⟶ b}
      (iea : ea ∘ ea = ea) (ieb : eb ∘ eb = eb) (iec : ec ∘ ec = ec)
      (Hf : ec ∘ f ∘ eb = f) (Hg : eb ∘ g ∘ ea = g) :
      ec ∘ (f ∘ g) ∘ ea = f ∘ g :=
      have Hf' : ec ∘ f = f, from cancel_left iec Hf,
      have Hg' : g ∘ ea = g, from cancel_right iea Hg,
      calc ec ∘ (f ∘ g) ∘ ea
            = ec ∘ f ∘ (g ∘ ea) : by rewrite (assoc f g ea)
        ... = (ec ∘ f) ∘ (g ∘ ea) : by rewrite (assoc ec f (g ∘ ea))
        ... = f ∘ g : by rewrite [Hf', Hg']

    definition karoubi_comp (f : karoubi_morphism b c)
      (g : karoubi_morphism a b) :=
      karoubi_morphism.mk
        (f^.mor ∘ g^.mor)
        (simp_comp_simp a^.idempo b^.idempo c^.idempo f^.simp g^.simp)

    definition karoubi_ID (a : karoubi_object C) :=
      karoubi_morphism.mk
        (a^.endo)
        (calc a^.endo ∘ a^.endo ∘ a^.endo
              = a^.endo ∘ a^.endo : congr_arg (λ x, a^.endo ∘ x) (a^.idempo)
          ... = a^.endo : a^.idempo)

    lemma karoubi_hom_eq (f f' : karoubi_morphism a b)
      (H : f^.mor = f'^.mor) : f = f' :=
      begin
        cases f,
        cases f',
        cases H,
        apply rfl,
      end

    theorem karoubi_assoc (f : karoubi_morphism c d)
      (g : karoubi_morphism b c) (h : karoubi_morphism a b) :
      karoubi_comp f (karoubi_comp g h) = karoubi_comp (karoubi_comp f g) h :=
      karoubi_hom_eq (karoubi_comp f (karoubi_comp g h))
        (karoubi_comp (karoubi_comp f g) h) (assoc f^.mor g^.mor h^.mor)

    theorem karoubi_id_left (f : karoubi_morphism a b) :
      karoubi_comp (karoubi_ID b) f = f :=
      karoubi_hom_eq (karoubi_comp (karoubi_ID b) f) f
        (cancel_left b^.idempo f^.simp)

    theorem karoubi_id_right (f : karoubi_morphism a b) :
      karoubi_comp f (karoubi_ID a) = f :=
      karoubi_hom_eq (karoubi_comp f (karoubi_ID a)) f
        (cancel_right a^.idempo f^.simp)
  end

  attribute [reducible]
  definition karoubi_category {ob : Type u} (C : category ob)
    : category (karoubi_object C) :=
    mk (λa b, karoubi_morphism a b)
      (λ a b c f g, karoubi_comp f g)
      (λ a, karoubi_ID a)
      (λ a b c d f g h, karoubi_assoc f g h)
      (λ a b f, karoubi_id_left f)
      (λ a b f, karoubi_id_right f)

end karoubi
