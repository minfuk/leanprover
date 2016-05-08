import types.trunc types.pi arity algebra.category.default

open eq is_trunc pi equiv

section entry20060828

  /-
   - hott/algebra/category/precategory.hlean 
   - をまねて作ってます。
   -/
  structure semicategory [class] (ob : Type) : Type :=
  mk' ::
    (hom : ob → ob → Type)
    (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
    (assoc : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
      comp h (comp g f) = comp (comp h g) f)
    (is_set_hom : Π(a b : ob), is_set (hom a b))

  attribute semicategory.is_set_hom [instance]

  infixr ∘ := semicategory.comp
  -- section の中では namespace は書けないので外しています。
  infixl ` ⟶ `:60 := semicategory.hom

  abbreviation comp [unfold 2] := @semicategory.comp

  structure semicategory_w_qi [class] (ob : Type) extends parent : semicategory ob :=
  mk' ::
    (qID : Π (a : ob), hom a a)
    (idempotency : Π (a : ob), comp !qID !qID = qID a)

  abbreviation qID [unfold 2] := @semicategory_w_qi.qID
    
  structure fullybuffer {ob : Type} (C : semicategory_w_qi ob) (a b : ob) :=
    (buffer : a ⟶ b)
    (qid_left : !qID ∘ buffer = buffer)
    (qid_right : buffer ∘ !qID = buffer)

  section exercises
    variables {ob : Type} [C : semicategory_w_qi ob]
    variables {a b c d : ob} {h : c ⟶ d} {g : b ⟶ c} {f f' : a ⟶ b}
    include C
    
    definition qid [reducible] [unfold 2] := qID a
    
    example (f : fullybuffer C a b) (g : fullybuffer C b c) : fullybuffer C a c :=
      let bf := @fullybuffer.buffer _ _ _ _ f in
      let bg := @fullybuffer.buffer _ _ _ _ g in
      fullybuffer.mk
        (bg ∘ bf)
        (calc !qID ∘ (bg ∘ bf)
              = (!qID ∘ bg) ∘ bf : semicategory.assoc
          ... = bg ∘ bf : @fullybuffer.qid_left _ _ _ _ g)
        (calc (bg ∘ bf) ∘ !qID
              = bg ∘ (bf ∘ !qID) : semicategory.assoc
          ... = bg ∘ bf : @fullybuffer.qid_right _ _ _ _ f)
      
    example : fullybuffer C a a :=
      fullybuffer.mk
        (qid)
        (calc !qID ∘ qid = qid : @semicategory_w_qi.idempotency _ _)
        (calc qid ∘ !qID = qid : @semicategory_w_qi.idempotency _ _)

  end exercises

end entry20060828
