import algebra.category.default algebra.category.constructions.order

open eq is_trunc equiv is_equiv iso funext category functor nat_trans iso bool

section entry20070827

  /- category A := precategory_order -/

  definition cat_b : precategory unit :=
    precategory.mk'
      (λ a b, bool)
      (λ a b c f g, f && g)
      (λ a, tt)
      (λ a b c d f g h, (band.assoc f g h)⁻¹)
      (λ a b c d f g h, band.assoc f g h)
      (λ a b f, tt_band f)
      (λ a b f, band_tt f)
      (λ a, tt_band tt)
      (λ a b, is_set_bool)

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