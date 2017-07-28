import logic.eq data.set.basic data.set.function data.set.finite
  theories.topology.basic
open eq eq.ops set classical topology

example {A : Type} {s t : set A} (H1 : ∀(x : set A), x ⊆ s → ∃(y : set A), x ⊆ y)
  (H2 : t ⊆ s) : (∃(y : set A), t ⊆ y) :=
  begin
    obtain (y : set A) (H : t ⊆ y), from H1 t H2,
    exists.intro y H
  end

example {A : Type} {s t u : set A}
  (H1 : ∀(x : set A), x ⊆ s → ∃(y : set A), x ⊆ y)
  (H2 : (t \ u) ⊆ s) : (∃(y : set A), (t \ u) ⊆ y) :=
  begin
    obtain (y : set A) (H : (t \ u) ⊆ y), from H1 (t \ u) H2,
    exists.intro y H
  end

lemma lem1 {B : Type} {b : B} {s t u : set B} (H1: b ∈ u) (H2 : s ⊆ t) (u0 : set B)
  : (insert b s) ⊆ t ∧ (insert b s) ⊆ u0 := sorry

example {B : Type} {u : set B} (u0 : set B)
  (H1 : ∃(b : B), b ∈ u ∧ b ∈ u0) (H2 : ∃(t : set B), t ⊆ u ∧ t ⊆ u0)
  : (∀(x : B), x ∈ u → x ∈ u0) → ∃(v : set B), v ⊆ u ∧ v ⊆ u0 :=
  begin
    assume H0 : (∀(x : B), x ∈ u → x ∈ u0),
    show ∃(v : set B), v ⊆ u ∧ v ⊆ u0, from
      begin
        obtain (b : B) (H1a : b ∈ u ∧ b ∈ u0), from H1,
        obtain (t : set B) (H2a : t ⊆ u ∧ t ⊆ u0), from H2,
        have H3a : (insert b t) ⊆ u ∧ (insert b t) ⊆ u0, from lem1 (and.left H1a) (and.left H2a) u0,
        exists.intro (insert b t) H3a,
      end,
  end

lemma xxx1 {s : set (set M)} {U : set M} {a : set M} (H : U ⊆ ⋃₀ (insert a s))
  : (U \ a) ⊆ ⋃₀ s := sorry
  
lemma xxx2 (f : M → N) (a : set M) (s : set(set M)) (b : set N) (t : set(set N))
  : ∀(y : set N), y ∈ (insert b t) → ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y)
  := sorry
  
lemma xxx3 (f : M → N) (a : set M) (s : set(set M)) (b : set N) (t : set(set N))
  : ∀(U : set M), U ⊆ ⋃₀ (insert a s) → f ' U ⊆ ⋃₀ (insert b t)
  := sorry
  
lemma xxx4 (b : set N) (t S : set(set N))
 : (insert b t) ⊆ S
 := sorry

lemma xxx5 (b : set N) (t : set(set N))
 : (insert b t) ⊆ (insert b t)
 := sorry

lemma finite_preimage_subset_finite_image_subset (S : set(set N)) (f : M → N)
  : ∀(s : set (set M)) [finite s], (
/-
      (∀(x : set M), x ∈ s → ∃(y : set N), y ∈ S ∧ (x = f '- y))
      → ∀(U : set M), (
        U ⊆ ⋃₀ s
        → (∃(t : set(set N)), t ⊆ S
          ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
          ∧ f ' U ⊆ ⋃₀ t
          ∧ finite t          
        )
      )
-/
      (∀(x : set M), x ∈ s → ∃(y : set N), y ∈ S ∧ (x = f '- y))
      → (∃(t : set(set N)), --t ⊆ S
--        ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
        (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
        ∧ (∀(U : set M), U ⊆ ⋃₀ s → f ' U ⊆ ⋃₀ t)
        ∧ finite t          
      )
    ) :=
  begin
    let P := λ(s : set (set M)),(
      (∀(x : set M), x ∈ s → ∃(y : set N), y ∈ S ∧ (x = f '- y))
/-
      → ∀(U : set M), (
        U ⊆ ⋃₀ s
        → (∃(t : set(set N)), t ⊆ S
          ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
          ∧ f ' U ⊆ ⋃₀ t
          ∧ finite t
        )
      )
-/
      → (∃(t : set(set N)), --t ⊆ S
--        ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
        (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
        ∧ (∀(U : set M), U ⊆ ⋃₀ s → f ' U ⊆ ⋃₀ t)
        ∧ finite t
      )
    ),
    have H1 : P ∅, from
      begin
        assume H1a : ∀(x : set M), x ∈ ∅ → ∃(y : set N), y ∈ S ∧ (x = f '- y),
/-
        show ∀(U : set M), U ⊆ ⋃₀ ∅ → ∃(t : set(set N)),
          t ⊆ S
            ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ ∅ ∧ (x = f '- y))
            ∧ f ' U ⊆ ⋃₀ t
            ∧ finite t, from
-/
        have Hx1 : ∅ ⊆ S, from empty_subset S,
        have H5 : ∀(y : set N), y ∈ ∅ → ∃(x : set M), x ∈ ∅ ∧ (x = f '- y), from
          begin
            take y : set N,
            assume H6 : y ∈ ∅,
            false.elim H6
          end,
        have H6 : ∀(U : set M), U ⊆ ⋃₀ ∅ → f ' U ⊆ ⋃₀ ∅, from
          begin
            take U : set M,
            assume H4 : U ⊆ ⋃₀ ∅,
            have H7 : U ⊆ ∅, from sUnion_empty ▸ H4,
            have H8 : f ' U ⊆ f ' ∅, from image_subset f H7,
            have H9 : f ' U ⊆ ∅, from image_empty f ▸ H8,
            subset.trans H9 (empty_subset (⋃₀ ∅))
          end,
        have H7 : finite ∅, from finite_empty,
        show ∃(t : set(set N)), --t ⊆ S
--            ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y))
            (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ ∅ ∧ (x = f '- y))
            ∧ (∀(U : set M), U ⊆ ⋃₀ ∅ → f ' U ⊆ ⋃₀ t)
            ∧ finite t, from
--          exists.intro ∅ (and.intro Hx1 (and.intro H5 (and.intro H6 H7))),
          exists.intro ∅ (and.intro H5 (and.intro H6 H7)),
/-
          begin
            have H5 : ∀(y : set N), y ∈ ∅ → ∃(x : set M), x ∈ ∅ ∧ (x = f '- y), from
            begin
              take y : set N,
              assume H6 : y ∈ ∅,
              false.elim H6
            end,
            have H6 : f ' U ⊆ ⋃₀ ∅, from
              begin
                have H7 : U ⊆ ∅, from sUnion_empty ▸ H4,
                have H8 : f ' U ⊆ f ' ∅, from image_subset f H7,
                have H9 : f ' U ⊆ ∅, from image_empty f ▸ H8,
                subset.trans H9 (empty_subset (⋃₀ ∅))
              end,
            have H7 : finite ∅, from finite_empty,
            exists.intro ∅ (and.intro Hx1 (and.intro H5 (and.intro H6 H7)))
          end,
-/
      end,
    have H2 : ∀(a : set M), ∀(s : set (set M)) [finite s],
      a ∉ s → P s → P (insert a s), from
      begin
        take a : set M,
        take s : set (set M),
        assume H20 : finite s,
        assume H2a : a ∉ s,
        assume H2b : P s,
        show P (insert a s), from
          begin
            assume H2c : (∀(x : set M), x ∈ (insert a s) → ∃(y : set N), y ∈ S ∧ (x = f '- y)),
            have H2g : ∀(x : set M), x ∈ s → ∃(y : set N), y ∈ S ∧ (x = f '- y), from
              begin
                take x : set M,
                assume H2h : x ∈ s,
                have H2i : x ∈ (insert a s), from
                  mem_of_subset_of_mem (subset_insert a s) H2h,
                H2c x H2i
              end,
            have zzz0 : a ∈ (insert a s) → ∃(y : set N), y ∈ S ∧ (a = f '- y), from
              begin
                apply H2c a
              end,
            have zzz1 : ∃(y : set N), y ∈ S ∧ (a = f '- y), from
              begin
                apply zzz0 (mem_insert a s)
              end,
            obtain (t : set(set N)) (H2j : --t ⊆ S
--              ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
              (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
              ∧ (∀(U : set M), U ⊆ ⋃₀ s → f ' U ⊆ ⋃₀ t)
              ∧ finite t), from H2b H2g,
--            obtain (b : set N) (H2k : b ∈ S ∧ (a = f '- b)), from H2c a (mem_insert a s),
            obtain (b : set N) (H2k : b ∈ S ∧ (a = f '- b)), from zzz1,
/-
            have H2p : (insert b t) ⊆ S, from
              begin
                apply insert_subset_mem_subset (and.left H2j) (and.left H2k),
              end,
-/
            have H2q : ∀(y : set N), y ∈ (insert b t)
              → ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y), from
              begin
                apply xxx2 f a s b t
              end,
            have H2o : ∀(U : set M), U ⊆ ⋃₀ (insert a s)
              → f ' U ⊆ ⋃₀ (insert b t), from
              begin
                apply xxx3 f a s b t
              end,
            have H2u : finite (insert b t), from
              begin
--                apply @finite_insert (set N) b t (and.right (and.right (and.right H2j))),
                apply @finite_insert (set N) b t (and.right (and.right H2j)),
              end,
--            have H2p : (insert b t) ⊆ S, from 
--              begin
--                apply xxx4 b t S
--              end,
            show ∃(t : set(set N)), --t ⊆ S
--              ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y))
              (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y))
              ∧ (∀(U : set M), U ⊆ ⋃₀ (insert a s) → f ' U ⊆ ⋃₀ t)
              ∧ finite t, from
--               exists.intro (insert b t) (and.intro H2p (and.intro H2q (and.intro H2o H2u))),
               exists.intro (insert b t) (and.intro H2q (and.intro H2o H2u)),
          end,
      end,
    apply induction_finite H1 H2
  end
/-        
        show P (insert a s), from
          begin
            assume H2c : (∀(x : set M), x ∈ (insert a s) → ∃(y : set N), y ∈ S ∧ (x = f '- y)),
            take U : set M,
            assume H2d : U ⊆ ⋃₀ (insert a s),
            have H2f : (U \ a) ⊆ ⋃₀ s, from xxx1 H2d,
            have H2g : ∀(x : set M), x ∈ s → ∃(y : set N), y ∈ S ∧ (x = f '- y), from
              begin
                take x : set M,
                assume H2h : x ∈ s,
                have H2i : x ∈ (insert a s), from
                  mem_of_subset_of_mem (subset_insert a s) H2h,
                H2c x H2i
              end,
            show ∃(t : set(set N)), t ⊆ S
              ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y))
              ∧ f ' U ⊆ ⋃₀ t
              ∧ finite t, from
              begin
                have H2e : U ⊆ a ∪ ⋃₀ s, from (sUnion_insert a s) ▸ H2d,
                have H2f0 : U ∩ (compl a) ⊆ (a ∪ ⋃₀ s) ∩ (compl a), from subset_diff H2e a,
                have H2f1 : (a ∪ ⋃₀ s) ∩ (compl a) ⊆ ⋃₀ s, from union_diff_subset a (⋃₀ s),
                have H2f : (U ∩ (compl a)) ⊆ ⋃₀ s, from subset.trans H2f0 H2f1,
                have H2g : ∀(x : set M), x ∈ s → ∃(y : set N), y ∈ S ∧ (x = f '- y), from
                  begin
                    take x : set M,
                    assume H2h : x ∈ s,
                    have H2i : x ∈ (insert a s), from
                      mem_of_subset_of_mem (subset_insert a s) H2h,
                    H2c x H2i
                  end,
                obtain (t : set(set N)) (H2j : t ⊆ S
                  ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
                  ∧ f ' (U ∩ (compl a)) ⊆ ⋃₀ t
                  ∧ finite t), from H2b H2g (U ∩ (compl a)) H2f,
                    have H2l0 : U \ a = U ∩ (f '- (compl b)), from
                      calc U \ a = U \ (f '- b) : diff_eq U (and.right H2k)
                             ... = U ∩ (compl (f '- b)) : diff_eq U (f '- b)
                             ... = U ∩ (f '- (compl b)) : preimage_compl f b,
                have Hxxxxx : ∃(t : set(set N)), t ⊆ S
          ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
          ∧ f ' (U \ a) ⊆ ⋃₀ t
          ∧ finite t, from H2b H2g (U \ a) H2f,
                obtain (t : set(set N)) (H2j : t ⊆ S
                  ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
                  ∧ f ' (U \ U) ⊆ ⋃₀ t
                  ∧ finite t), from Hxxxxx,
                obtain (b : set N) (H2k : b ∈ S ∧ (a = f '- b)), from H2c a (mem_insert a s),
                    have H2l : f ' (U \ a) = f ' U \ b, from sorry,
                      calc f ' (U \ a) = f ' (U ∩ (f '- (compl b))) : image_eq f H2l0
                                   ... = f ' U ∩ (compl b) : image_inter f U (compl b)
                                   ... = f ' U \ b : diff_eq (f 'U) b,
                    have H2m : f ' U \ b ⊆ ⋃₀ t, from H2l ▸ (and.left (and.right (and.right H2j))),
                    have H2n : f ' U ⊆ b ∪ ⋃₀ t, from diff_subset_union H2m,
                   have H2o : f ' U ⊆ ⋃₀ (insert b t), from (eq.symm (sUnion_insert b t)) ▸ H2n,
                     have H2p : (insert b t) ⊆ S, from
                      insert_subset_mem_subset (and.left H2j) (and.left H2k),
                    have H2q : ∀(y : set N), y ∈ (insert b t)
                      → ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y), from
                      begin
                        take y : set N,
                        assume H2r : y ∈ (insert b t),
                        or.elim H2r
                          (assume H2s : y = b,
                            (eq.symm H2s) ▸ exists.intro a (and.intro (mem_insert a s) (and.right H2k)))
                          (assume H2t : y ∈ t,
                            have Hx1 : ∃(x : set M), x ∈ s ∧ (x = f '- y), from (and.left (and.right H2j)) y H2t,
                            show ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y), from sorry)
                      end,
                    have H2u : finite (insert b t), from
                      @finite_insert (set N) b t (and.right (and.right (and.right H2j))),
                have H2p : (insert b t) ⊆ S, from sorry,
                have H2q : ∀(y : set N), y ∈ (insert b t)
                  → ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y), from sorry,
                have H2o : f ' U ⊆ ⋃₀ (insert b t), from sorry,
                have H2u : finite (insert b t), from sorry,
                exists.intro (insert b t) (and.intro H2p (and.intro H2q (and.intro H2o H2u)))
              end
          end,
      end,
    apply induction_finite H1 H2
  end
-/

/-
lemma finite_preimage_subset_finite_image_subset (S : set(set N)) (f : M → N)
  : let Sx := { x : set M | ∃(y : set N), y ∈ S ∧ x = f '- y },
    ∀(U : set M), U ⊆ ⋃₀ Sx ∧ finite Sx →
      ∃(Sy : set(set M)), Sy ⊆ S ∧ ∀(y : set N), y ∈ Sy → ∃(x : set M), x ∈ Sx ∧ x = f '- y
         ∧ f ' U ⊆ ⋃₀ Sy ∧ finite Sy :=
  take x1 : set M,
  assume H1 : x1 ∉ Sx,
  assume H2 : ∃(y1 : set N), y1 ∈ S ∧ x1 = f '- y1,
  assume H3 : U ⊆ ⋃₀ Sx ∧ finite Sx → f ' U ⊆ ⋃₀ Sy ∧ finite Sy,
  let Sx2 := insert x1 Sx in
  assume H4 : U ⊆ ⋃₀ Sx2,
  let Sy2 := { y : set N | y ∈ S ∧ (∃(x : set M), x ∈ Sx2 ∧ x = f '- y) } in
  have f ' U ⊆ ⋃₀ Sy2, from
    begin
      have H5 : ⋃₀ (insert x1 Sx) = x1 ∪ ⋃₀ Sx, from sUnion_insert x1 Sx,    
      have H6 : (x1 ∪ ⋃₀ Sx) \ x1 ⊆ ⋃₀ Sx, from a1 x1 (⋃₀ Sx),
      have H7 : U \ x1 ⊆ ⋃₀ Sx, from H4,
      obtain (y1 : set N) (H8 : y1 ∈ S ∧ x1 = f '- y1), from H2,
      have H9 : U \ (f '- y1) ⊆ ⋃₀ Sx, from (and.right H8) ▸ H7,
      have H10 : U \ (f '- y1) = U ∩ (- (f '- y1)) = U ∩ (f '- (-y1)), from sorry,
      have H11 : f ' (U ∩ (f '- (-y1))) = f ' U ∩ -y1, from image_inter f U (-y1),
      have H12 : f ' U \ y1 ⊆ ⋃₀ Sy, from H11,
      have H13 : f ' U ⊆ y1 ∪ ⋃₀ Sy, from a2 H12,
      have H14 : f ' U ⊆ (insert y1 Sy), from (sUnion_insert y1 Sy) ▸ H13,
      have H15 : y1 ∈ Sy2, from and.intro (and.left H2)
        (exists.intro (and.intro (mem_insert x1 Sx) (and.right H8))) 
    end,
-/  
/-  
  show ∀(x1 : set M), ∀(s : set (set M)), x1 ∉ s →
     U ⊆ ⋃₀ s ∧ x ∈ s → ∃(y : set N), y ∈ S ∧ x = f '- y
       ∧ (let Sy2 := { y : set N | y ∈ S ∧ (∃(x : set M), x ∈ s ∧ x = f '- y) }
         in f ' U ⊆ ⋃₀ Sy2 ∧ finite Sy2)
  induction_finite 
-/
