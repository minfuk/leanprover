import algebra.category.default algebra.category.constructions.order

open eq is_trunc trunc equiv is_equiv iso funext category functor nat_trans bool

section entry20070827
  open algebra

  definition cat_a {A : Type} [HA : is_set A]
    [OA : weak_order A] [Hle : Π a b : A, is_prop (a ≤ b)]
    : Precategory :=
    Precategory.mk A (precategory_order A)

  definition cat_b : Precategory :=
    Precategory.mk unit (precategory.mk'
      (λ a b, bool)
      (λ a b c f g, f && g)
      (λ a, tt)
      (λ a b c d f g h, (band.assoc f g h)⁻¹)
      (λ a b c d f g h, band.assoc f g h)
      (λ a b f, tt_band f)
      (λ a b f, band_tt f)
      (λ a, tt_band tt)
      (λ a b, is_set_bool))

  open decidable

  variables {A : Type} [HA : is_set A]
    [OA : weak_order A] [Hle : Π a b : A, is_prop (a ≤ b)]

  variables [Hde : decidable_eq (@cat_a A HA OA Hle)]
  include Hde

  definition maphom {a b : (@cat_a A HA OA Hle)} (f : hom a b) : bool :=
  match Hde a b with
  | inl H₁ := tt
  | inr H₁ := ff
  end

  theorem maphom_tt {a b : (@cat_a A HA OA Hle)} (f : hom a b) (H : a = b)
    : maphom f = tt :=
    begin
      unfold maphom,
      cases (Hde a b),
      esimp,
      contradiction,
    end
  
  theorem maphom_ff {a b : (@cat_a A HA OA Hle)} (f : hom a b) (H : ¬(a = b))
    : maphom f = ff :=
    begin
      unfold maphom,
      cases (Hde a b),
      contradiction,
      esimp,
    end
  
  definition maphom_prop {a b c : (@cat_a A HA OA Hle)}
    (f : hom a b) (g : hom b c)
    : maphom (g ∘ f) = (maphom g) && (maphom f) :=
    have Hf : (@weak_order.le A _) a b, from f,
    have Hg : (@weak_order.le A _) b c, from g,
    decidable.by_cases
      (assume H1 : a = c,
        have H2 : a = b, from @eq_of_le_of_ge A OA a b Hf (H1⁻¹ ▸ Hg),
        have H3 : b = c, from @eq_of_le_of_ge A OA b c Hg (H1 ▸ Hf),
        have H4 : maphom (g ∘ f) = tt, from maphom_tt (g ∘ f) H1,
        have H5 : maphom g && maphom f = tt, from
          calc maphom g && maphom f
                = (maphom g) && tt : maphom_tt f H2
            ... = tt && tt : maphom_tt g H3
            ... = tt : tt_band tt,
        show maphom (g ∘ f) = maphom g && maphom f, from H5⁻¹ ▸ H4)
      (assume H1 :¬a = c,
        show maphom (g ∘ f) = maphom g && maphom f, from
          have H1a : maphom (g ∘ f) = ff, from maphom_ff (g ∘ f) H1,
          by_cases
            (assume H2a : b = c,
              have H3a : ¬a = b, from H2a⁻¹ ▸ H1,
              have H4a : maphom g && maphom f = ff, from
                calc maphom g && maphom f
                      = (maphom g) && ff : maphom_ff f H3a
                  ... = ff : band_ff (maphom g),
              H4a⁻¹ ▸ H1a)
            (assume H2b : ¬b = c,
              have H4b : maphom g && maphom f = ff, from
                calc maphom g && maphom f
                      = ff && (maphom f) : maphom_ff g H2b
                  ... = ff : ff_band (maphom f),
              H4b⁻¹ ▸ H1a))

  definition functor_example : functor (@cat_a A HA OA Hle) cat_b :=
    functor.mk
      (λ x, unit.star)
      (λ a b f, maphom f)
      (λ a, maphom_tt (ID a) (rfl))
      (λ a b c g f, maphom_prop f g)

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

section entry20091109

end entry20091109

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