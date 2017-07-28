import logic.eq data.set.basic data.set.function data.set.finite
  theories.topology.basic theories.topology.continuous
open eq eq.ops set classical topology

-- check preimage
-- data.set.function で定義

-- check topology
-- theories.topology.basic で定義

-- check continuous
-- theories.topology.basic で定義

variables {M : Type} [Tm : topology M]
include Tm

-- continuous が structure でないので structure をやめる
definition connected (U : set M) :=
  ∀U1 U2 : set M, Open U1 → Open U2 → U ⊆ (U1 ∪ U2)
    → (U ∩ U1) ≠ ∅ → (U ∩ U2) ≠ ∅ → (U ∩ (U1 ∩ U2)) ≠ ∅

definition compact (U : set M) :=
  ∀S : set (set M), S ⊆ opens M → U ⊆ ⋃₀ S
    → ∃S' : set (set M), S' ⊆ S ∧ finite S' ∧ U ⊆ ⋃₀ S'

definition subset_family (A : set (set M)) (U : set M) :=
  ∀(a : set M), a ∈ A → a ⊆ U

definition finite_intersection_property (A : set (set M)) (U : set M) :=
  subset_family A U ∧ ∀(A' : set (set M)), A' ⊆ A ∧ finite A' → ⋂₀ A' ≠ ∅

lemma compact_contraposition (U : set M) [Hc : compact U]
  {A : set (set M)} (H0 : A ⊆ opens M)
  (H : ∀(A' : set (set M)), A' ⊆ A ∧ finite A' → ¬(U ⊆ ⋃₀ A')) :
  ¬(U ⊆ ⋃₀ A) :=
  assume H1 : U ⊆ ⋃₀ A,
  obtain (A' : set (set M)) (H2 : A' ⊆ A ∧ finite A' ∧ U ⊆ ⋃₀ A'),
    from Hc A H0 H1,
  have H3 : U ⊆ ⋃₀ A', from (and.right (and.right H2)),
  have H4 : ¬(U ⊆ ⋃₀ A'), from (H A' (and.intro (and.left H2) (and.left (and.right H2)))),
  show false, from not.elim H4 H3
  
lemma not_subset_mem_compl {U V : set M} (H : ¬(U ⊆ V)) : ∃(a : M), a ∈ -V :=
  have H1 : U ∩ (-V) ≠ ∅, from
    assume H2 : U ∩ (-V) = ∅,
    have H9 : U ⊆ V, from
      take x,
      assume H3 : x ∈ U,
      have H4 : x ∉ (-V), from
        assume H5 : x ∈ (-V),
        have H6 : x ∈ U ∧ x ∈ (-V), from and.intro H3 H5,
        have H7 : U ∩ (-V) ≠ ∅, from ne_empty_of_mem H6,
        not.elim H7 H2,
      show x ∈ V, from (compl_compl V) ▸ (mem_compl H4),
    not.elim H H9,
  have H8 : ∃(a : M), a ∈ U ∩ (-V), from exists_mem_of_ne_empty H1,
  obtain (a : M) (H2 : a ∈ U ∧ a ∈ (-V)), from H8,
  exists.intro a (and.right H2)

theorem compact_closed_subsets_inter_not_empty
  (U : set M) [Uc : compact U] [Im : inhabited M]:
  ∀(A : set (set M)), subset_family A U ∧ (∀(a : set M), a ∈ A → closed a)
    → finite_intersection_property A U
    → ⋂₀ A ≠ ∅ :=
  take A : set (set M),
  assume H1 : subset_family A U ∧ (∀(a : set M), a ∈ A → closed a),
  assume H2 : finite_intersection_property A U,
  have H001 : (compl ' A) ⊆ opens M, from
    take a : set M,
    assume H002 : a ∈ (compl ' A),
    have H003 : -a ∈ A, from (iff.elim_left (mem_image_compl a A)) H002,
    have H004 : closed (-a), from (and.right H1) (-a) H003,
    (iff.elim_right (Open_iff_closed_compl a)) H004,
  by_cases
    (assume H048 : U = ∅,
    have H047 : A = ∅, from
      by_contradiction (
        assume H043 : A ≠ ∅,
        obtain (a : set M) (H042 : a ∈ A), from exists_mem_of_ne_empty H043,
        have H041 : a ⊆ U, from (and.left H1) a H042,
        have H040 : a = ∅, from eq_empty_of_subset_empty (H048 ▸ H041),
        have H039 : ⋂₀ A = ∅,
          from eq_empty_of_subset_empty (H040 ▸ (sInter_subset_of_mem H042)),
        have H038 : ⋂₀ A ≠ ∅, from sorry,
        not.elim H038 H039),
    have H046 : ⋂₀ A = univ, from H047⁻¹ ▸ sInter_empty,
    show ⋂₀ A ≠ ∅, from
      assume H045 : ⋂₀ A = ∅,
      have H044 : ∅ = univ, from H046 ▸ H045⁻¹,
      not.elim empty_ne_univ H044)
    (assume H049 : U ≠ ∅,
    have H097 : ∀(A' : set (set M)), A' ⊆ (compl ' A) ∧ finite A' → ¬(U ⊆ ⋃₀ A'), from
      take A' : set(set M),
      assume H092 : A' ⊆ (compl ' A) ∧ finite A',
      have H095 : (compl ' A') ⊆ A, from
        take x : set M,
        assume H094 : x ∈ (compl ' A'),
        have H093 : -x ∈ A', from (iff.elim_left (mem_image_compl x A')) H094,
        have H091 : -x ∈ (compl ' A), from mem_of_subset_of_mem (and.left H092) H093,
        have H090 : -(-x) ∈ A, from (iff.elim_left (mem_image_compl (-x) A)) H091,
        (compl_compl x) ▸ H090, -- by classical
      have H088 : finite (compl ' A'), from @finite_image _ _ compl A' (and.right H092),
      have H096 : ⋂₀ (compl ' A') ≠ ∅,
        from (and.right H2) (compl ' A') (and.intro H095 H088),
      obtain (x : M) (H085 : x ∈ ⋂₀ (compl ' A')), from exists_mem_of_ne_empty H096,
      have H086 : x ∈ - ⋃₀ A', from ((compl_sUnion A')⁻¹) ▸ H085,
      have H059 : x ∉ ⋃₀ A', from not_mem_of_mem_compl H086,
      show ¬(U ⊆ ⋃₀ A'), from
        by_cases
          (assume H0x1 : compl ' A' = ∅,
          show ¬(U ⊆ ⋃₀ A'), from
            assume H0x2 : U ⊆ ⋃₀ A',
            have H0y3 : A' = ∅, from
              by_contradiction (
                assume H0x3 : A' ≠ ∅,
                obtain (a : set M) (H0x4 : a ∈ A'), from exists_mem_of_ne_empty H0x3,
                have H0x5 : (-a) ∈ compl ' A', from
                  (iff.elim_right (mem_image_compl (-a) A')) ((compl_compl a)⁻¹ ▸ H0x4),
                have H0x6 : compl ' A' ≠ ∅, from ne_empty_of_mem H0x5,
                not.elim H0x6 H0x1),
            have H0x7 : ⋃₀ A' = ∅, from H0y3⁻¹ ▸ sUnion_empty,
            have H0x8 : U = ∅, from eq_empty_of_subset_empty (H0x7 ▸ H0x2),
            not.elim H049 H0x8)
        (assume H058 : compl ' A' ≠ ∅,
        have H084 : x ∈ U, from
          obtain (a : set M) (H081 : a ∈ compl ' A'), from exists_mem_of_ne_empty H058,
          have H069 : x ∈ a, from H085 H081,
          have H080 : a ∈ A, from mem_of_subset_of_mem H095 H081,
          show x ∈ U, from mem_of_subset_of_mem ((and.left H1) a H080) H069,
        show ¬(U ⊆ ⋃₀ A'), from
          assume H077 : U ⊆ ⋃₀ A',
          have H075 : x ∈ ⋃₀ A', from H077 H084,
          not.elim H059 H075),
    have H099 : ¬(U ⊆ ⋃₀ (compl ' A)),
      from @compact_contraposition _ _ U Uc _ H001 H097,
    have H098 : ∃(a : M), a ∈ -(⋃₀ (compl ' A)), from not_subset_mem_compl H099,
    have H100 : ∃(a : M), a ∈ ⋂₀ A, from ((sInter_eq_comp_sUnion_compl A)⁻¹) ▸ H098,
    obtain (a : M) (H101 : a ∈ ⋂₀ A), from H100,
    show ⋂₀ A ≠ ∅, from ne_empty_of_mem H101)

variables {N : Type} [Tn : topology N]
include Tn

lemma open_continuous_preimage_open {f : M → N} (C : continuous f) {V : set N} (O : Open V)
  : Open (f '- V) :=
  let S := { U : set M | Open U ∧ f ' U ⊆ V } in
  have H1 : ⋃₀ S ⊆ f '- V, from
    take x,
    assume H2 : x ∈ ⋃₀ S,
    obtain (U1 : set M) (H3 : U1 ∈ S ∧ x ∈ U1), from H2,
    have H4 : Open U1 ∧ f ' U1 ⊆ V, from and.left H3,
    have H5 : U1 ⊆ f '- V, from iff.elim_left image_subset_iff (and.right H4),
    mem_of_subset_of_mem H5 (and.right H3),
  have H6 : ⋃₀ S ⊇ f '- V, from
    take x,
    assume H7 : x ∈ f '- V,
    have H8 : f x ∈ V, from  iff.elim_right (mem_preimage_iff f V x) H7, 
    obtain (U2 : set M) (H9 : x ∈ U2 ∧ Open U2 ∧ f ' U2 ⊆ V), from C x V H8 O,
    have H10 : U2 ∈ S, from and.right H9,
    mem_sUnion (and.left H9) H10,
  have H11 : ⋃₀ S = f '- V, from subset.antisymm H1 H6,
  have H12 : S ⊆ opens M, from take x, assume H13 : x ∈ S, and.left H13,
  have H14 : Open (⋃₀ S), from sUnion_mem_opens H12,
  H11 ▸ H14

corollary closed_continuous_preimage_closed {f : M → N} (C : continuous f) {V : set N} (H : closed V)
  : closed (f '- V) :=
  (preimage_compl f V) ▸ (open_continuous_preimage_open C H)

lemma not_empty_image_not_empty_preimage {f : M → N} {U : set M} (H : f ' U ≠ ∅)
  : U ≠ ∅ :=
  obtain (y : N) (H1 : y ∈ f ' U), from exists_mem_of_ne_empty H,
  obtain (x : M) (H2 : x ∈ U ∧ f x = y), from H1,
  ne_empty_of_mem (and.left H2)

lemma not_empty_image_not_empty {f : M → N} {U : set M} (H : U ≠ ∅)
  : f ' U ≠ ∅ :=
  obtain (x : M) (H1 : x ∈ U), from exists_mem_of_ne_empty H,
  have H2 : f x ∈ f ' U, from mem_image_of_mem f H1,
  ne_empty_of_mem H2

theorem connected_continuous_image_connected
  (f : M → N) [fc : continuous f] (U : set M) [Uc : connected U]
  : connected (f ' U) :=
  take V1 V2 : set N,
  assume H1 : Open V1,
  assume H2 : Open V2,
  assume H3 : (f ' U) ⊆ (V1 ∪ V2),
  assume H4 : ((f ' U) ∩ V1) ≠ ∅,
  assume H5 : ((f ' U) ∩ V2) ≠ ∅,
  show (f ' U) ∩ (V1 ∩ V2) ≠ ∅, from
    have H6 : U ⊆ f '- (V1 ∪ V2), from iff.elim_left image_subset_iff H3,
    have H7 : Open (f '- V1), from open_continuous_preimage_open fc H1,
    have H8 : Open (f '- V2), from open_continuous_preimage_open fc H2,
    have H9 : U ⊆ (f '- V1) ∪ (f '- V2), from (preimage_union f V1 V2) ▸ H6,
    have H10 : f ' (U ∩ (f '- V1)) ≠ ∅, from (image_inter f U V1) ▸ H4,
    have H11 : U ∩ (f '- V1) ≠ ∅, from not_empty_image_not_empty_preimage H10,
    have H12 : f ' (U ∩ (f '- V2)) ≠ ∅, from (image_inter f U V2) ▸ H5,
    have H13 : U ∩ (f '- V2) ≠ ∅, from not_empty_image_not_empty_preimage H12,
    have H14 : U ∩ ((f '- V1) ∩ (f '- V2)) ≠ ∅,
      from Uc (f '- V1) (f '- V2) H7 H8 H9 H11 H13,
    have H15 : U ∩ (f '- (V1 ∩ V2)) ≠ ∅, from ((preimage_inter f V1 V2)⁻¹) ▸ H14,
    have H16 : f ' (U ∩ (f '- (V1 ∩ V2))) ≠ ∅, from not_empty_image_not_empty H15,
    ((image_inter f U (V1 ∩ V2))⁻¹) ▸ H16


/-
-- これがやりたいけど次のエラーで無理
-- invalid recursive equations, failed to find recursive arguments
-- that are structurally smaller
-- (possible solution: use well-founded recursion)

definition erase {X : Type} (x : X) (a : set X) : set X
  := {y : X | y ∈ a ∧ y ≠ x}

definition convert_set {A B: Type} (f : A → B) (H : ∀(x : A), ∃(y : B), f x = y)
  : (set A) → (set B)
| convert_set ⌞∅⌟ := ∅
| convert_set a :=
  begin
    have H₁ : a ≠ ∅, from sorry,
    obtain (x : A) (H₂ : x ∈ a), from exists_mem_of_ne_empty H₁,
    obtain (y : B) (H₃ : f x = y), from (H x),
    insert y (convert_set (erase x a))
  end
-/
/-
  :=
  begin
    take S : set N,
    take (S₂ : set (set N)), -- (H4 : S₂ ⊆ S₁ ∧ finite S₂ ∧ U ⊆ ⋃₀ S₂),
    assume H1 : S ∉ S₂,
    assume H2 : finite S₂ ∧ U ⊆ ⋃₀ S₂ ∧ S₂ = { x : set M | ∃(y : set N), y ∈ S ∧ x = f '- y }
      → ∃(S₃ : set (set N)), finite S₃ ∧ f ' U ⊆ ⋃₀ S₃
        ∧ S₃ = { y : set N | ∃(x : set M), x ∈ S₂ ∧ x = f '- y },
    have (insert S O) ⊆ S, from Open S,
    have finite (insert S O), from finite O,
    have f ' U - S ⊆ ⋃₀ O - S, from xxx,
    have U - (f '- S) ⊆  f '- (⋃₀ O - S), from xxx,
    have 
  end

theorem preimage_eqv_rfl {A B : Type} (f : A → B) (O : set B)
  : f '- O = f '- O := sorry
theorem preimage_eqv_symm {A B : Type} (f : A → B) (O1 O2 : set B)
  : f '- O1 = f '- O2 → f '- O2 = f '- O1 := sorry
theorem preimage_eqv_trans {A B : Type} (f : A → B) (O1 O2 O3 : set B) :
  f '- O1 = f '- O2 → f '- O2 = f '- O3 → f '- O1 = f '- O3 := sorry
-/

section
  omit Tn Tm

  lemma subset_diff {X : Type} {s t : set X} (H : s ⊆ t) (u : set X)
    : s \ u ⊆ t \ u :=
    ((diff_eq s u)⁻¹) ▸ ((diff_eq t u)⁻¹) ▸ (inter_subset_inter_right (-u) H)

  lemma union_diff_subset {X : Type} (s t : set X) : ((s ∪ t) \ s) ⊆ t :=
    have H : (s ∪ t) ∩ (-s) = (t ∩ (-s)), from
      calc (s ∪ t) ∩ (-s)
            = (s ∩ -s) ∪ (t ∩ -s) : inter_distrib_right s t (-s)
        ... = ∅ ∪ (t ∩ -s) : inter_compl_self s
        ... = (t ∩ (-s)) : empty_union (t ∩ -s),
    (diff_eq (s ∪ t) s) ▸ H⁻¹ ▸ inter_subset_left t (compl s)

  lemma insert_super_diff_sub {X : Type} {a b : set X} {s : set(set X)}
    (H : b ⊆ ⋃₀ (insert a s)) : b \ a ⊆ ⋃₀ s :=
    have H1 : b ⊆ a ∪ ⋃₀ s, from (sUnion_insert a s) ▸ H,
    have H2 : b \ a ⊆ (a ∪ ⋃₀ s) \ a, from subset_diff H1 a,
    subset.trans H2 (union_diff_subset a (⋃₀ s))

  lemma diff_subset_union {X : Type} {s t u : set X} (H : s \ t ⊆ u) : s ⊆ t ∪ u :=
    have H1 : s ∩ -t ⊆ u, from diff_eq s t ▸ H,
    have H2 : u ⊆ t ∪ u, from subset_union_right t u,
    have H3 : t ∪ (s ∩ -t) ⊆ t ∪ u, from union_subset (subset_union_left t u) (subset.trans H1 H2),
    have H4 : t ∪ (s ∩ -t) = t ∪ s, from
      calc t ∪ (s ∩ -t) = (t ∪ s) ∩ (t ∪ -t) : union_distrib_left t s (-t)
                    ... = (t ∪ s) ∩ univ : union_compl_self t -- by classical
                    ... = t ∪ s : inter_univ (t ∪ s),
    subset.trans (subset_union_right t s) (H4 ▸ H3)

  lemma insert_subset_mem_subset {X : Type} {s t : set X} {a : X}
    (H1 : s ⊆ t) (H2 : a ∈ t) : (insert a s) ⊆ t :=
    take x,
    assume H3 : x ∈ (insert a s),
    or.elim H3
      (assume H4 : x = a,
        H4⁻¹ ▸ H2)
      (assume H5 : x ∈ s,
        mem_of_subset_of_mem H1 H5)
  
  lemma image_eq {X Y : Type} (f : X → Y) {a b : set X}
    (H : a = b) : f ' a = f ' b :=
    H ▸ rfl

  lemma inter_diff_eq {X : Type} (s : set X) {t u : set X} (H : t = u)
    : s ∩ t = s ∩ u :=
    H ▸ rfl

  lemma diff_image_subset {X Y : Type} {f : X → Y} {s : set X} {t y : set Y}
    (H : f ' (s \ (f '- y)) ⊆ t) : (f ' s) \ y ⊆ t :=
    have H1 : s \ f '- y = s ∩ (f '- (-y)), from
      calc s \ f '- y = s ∩ (-(f '- y)) : diff_eq s (f '- y)
                  ... = s ∩ (f '- (-y)) : inter_diff_eq s ((preimage_compl f y)⁻¹),
    have H2 : f ' (s \ f '- y) = (f ' s) \ y, from
      calc f ' (s \ f '- y) = f ' (s ∩ (f '- (-y))) : image_eq f H1
                        ... = f ' s ∩ (-y) : (image_inter f s (-y))⁻¹
                        ... = (f ' s) \ y : (diff_eq (f ' s) y)⁻¹,
    H2 ▸ H

end

lemma finite_preimage_subset_finite_image_subset (S : set(set N)) (f : M → N)
  : ∀(s : set (set M)) [finite s], (
      (∀(x : set M), x ∈ s → ∃(y : set N), y ∈ S ∧ (x = f '- y))
      → (∃(t : set(set N)), t ⊆ S
        ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
        ∧ (∀(U : set M), U ⊆ ⋃₀ s → f ' U ⊆ ⋃₀ t)
        ∧ finite t          
      )
    ) :=
  let P := λ(s : set (set M)),(
    (∀(x : set M), x ∈ s → ∃(y : set N), y ∈ S ∧ (x = f '- y))
    → (∃(t : set(set N)), t ⊆ S
        ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
        ∧ (∀(U : set M), U ⊆ ⋃₀ s → f ' U ⊆ ⋃₀ t)
        ∧ finite t
      )
    ) in
  have H1 : P ∅, from
    assume H1a : ∀(x : set M), x ∈ ∅ → ∃(y : set N), y ∈ S ∧ (x = f '- y),
    have Hx1 : ∅ ⊆ S, from empty_subset S,
    have H5 : ∀(y : set N), y ∈ ∅ → ∃(x : set M), x ∈ ∅ ∧ (x = f '- y), from
      take y : set N,
      assume H6 : y ∈ ∅,
      false.elim H6,
    have H6 : ∀(U : set M), U ⊆ ⋃₀ ∅ → f ' U ⊆ ⋃₀ ∅, from
      take U : set M,
      assume H4 : U ⊆ ⋃₀ ∅,
      have H7 : U ⊆ ∅, from sUnion_empty ▸ H4,
      have H8 : f ' U ⊆ f ' ∅, from image_subset f H7,
      have H9 : f ' U ⊆ ∅, from image_empty f ▸ H8,
      subset.trans H9 (empty_subset (⋃₀ ∅)),
    have H7 : finite ∅, from finite_empty,
    exists.intro ∅ (and.intro Hx1 (and.intro H5 (and.intro H6 H7))),
  have H2 : ∀(a : set M), ∀(s : set (set M)) [finite s],
    a ∉ s → P s → P (insert a s), from
    take a : set M,
    take s : set (set M),
    assume H20 : finite s,
    assume H2a : a ∉ s,
    assume H2b : P s,
    show P (insert a s), from
      assume H2c : (∀(x : set M), x ∈ (insert a s) → ∃(y : set N), y ∈ S ∧ (x = f '- y)),
      have H2g : ∀(x : set M), x ∈ s → ∃(y : set N), y ∈ S ∧ (x = f '- y), from
        take x : set M,
        assume H2h : x ∈ s,
        have H2i : x ∈ (insert a s), from
          mem_of_subset_of_mem (subset_insert a s) H2h,
        H2c x H2i,
      obtain (t : set(set N)) (H2j : t ⊆ S
        ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ s ∧ (x = f '- y))
        ∧ (∀(U : set M), U ⊆ ⋃₀ s → f ' U ⊆ ⋃₀ t)
        ∧ finite t), from H2b H2g,
      obtain (b : set N) (H2k : b ∈ S ∧ (a = f '- b)), from H2c a (mem_insert a s),
      have H2p : (insert b t) ⊆ S, from
        insert_subset_mem_subset (and.left H2j) (and.left H2k),
      have H2q : ∀(y : set N), y ∈ (insert b t)
        → ∃(x : set M), x ∈ (insert a s) ∧ (x = f '- y), from 
        take y : set N,
        assume H2r : y ∈ (insert b t),
          or.elim H2r
            (assume H2s : y = b,
              (eq.symm H2s) ▸ exists.intro a (and.intro (mem_insert a s) (and.right H2k)))
            (assume H2t : y ∈ t,
              have Hx1 : ∃(x : set M), x ∈ s ∧ (x = f '- y), from
                (and.left (and.right H2j)) y H2t,
              obtain (x1 : set M) (H2v : x1 ∈ s ∧ (x1 = f '- y)), from Hx1,
              have H2w : x1 ∈ (insert a s), from
                mem_insert_of_mem a (and.left H2v),
              exists.intro x1 (and.intro H2w (and.right H2v))),
      have H2o : ∀(U : set M), U ⊆ ⋃₀ (insert a s)
        → f ' U ⊆ ⋃₀ (insert b t), from
        take U : set M,
        assume H2a0 : U ⊆ ⋃₀ (insert a s),
        have H2a1 : U \ a ⊆ ⋃₀ s, from insert_super_diff_sub H2a0,
        have H2a3 : U \ (f '- b) ⊆ ⋃₀ s, from (and.right H2k) ▸ H2a1,
        have H2a4 : f ' (U \ f '- b) ⊆ ⋃₀ t, from
          (and.left (and.right (and.right H2j))) (U \ (f '- b)) H2a3,
        have H2a5 : f ' U \ b ⊆ ⋃₀ t, from diff_image_subset H2a4,
        have H2a6 : f ' U ⊆ b ∪ ⋃₀ t, from diff_subset_union H2a5,
        show f ' U ⊆ ⋃₀ (insert b t), from ((sUnion_insert b t)⁻¹) ▸ H2a6,
      have H2u : finite (insert b t), from
        @finite_insert _ b t (and.right (and.right (and.right H2j))),
      exists.intro (insert b t) (and.intro H2p (and.intro H2q (and.intro H2o H2u))),
  induction_finite H1 H2

theorem compact_continuous_image_compact
  (f : M → N) [fc : continuous f] (U : set M) [Uc : compact U]
  : compact (f ' U) :=
  take S,
  assume H1 : S ⊆ opens N,
  assume H2 : f ' U ⊆ ⋃₀ S,
  let S₁ := { O : set M | ∃(O₁ : set N), O₁ ∈ S ∧ O = f '- O₁ } in
  have H3 : U ⊆ ⋃₀ S₁, from
    take x,
    assume H4 : x ∈ U,
    have H5 : f x ∈ ⋃₀ S, from mem_of_subset_of_mem H2 (mem_image_of_mem f H4),
    obtain (O : set N) (H6 : O ∈ S ∧ f x ∈ O), from H5,
    have H7 : x ∈ f '- O, from mem_preimage (and.right H6),
    have H7a : f '- O = f '- O, from rfl,
    have H7b : (f '- O) ∈ S₁, from exists.intro O (and.intro (and.left H6) H7a),
    mem_sUnion H7 H7b,
  have H8 : S₁ ⊆ opens M, from
    take x,
    assume H8a : x ∈ S₁,
    obtain (y : set N) (H8b : y ∈ S ∧ x = f '- y), from H8a,
    have H8c : Open y, from mem_of_subset_of_mem H1 (and.left H8b),
    (and.right H8b)⁻¹ ▸ (open_continuous_preimage_open fc H8c),
  obtain (S₂ : set (set M)) (H9 : S₂ ⊆ S₁ ∧ finite S₂ ∧ U ⊆ ⋃₀ S₂),
    from Uc S₁ H8 H3,
  have H20 : ∀(x : set M), x ∈ S₂ → (∃ (y : set N), y ∈ S ∧ x = f '- y), from
    take x : set M,
    assume H20a : x ∈ S₂,
    mem_of_subset_of_mem (and.left H9) H20a,
  obtain (t : set(set N)) (H21 : t ⊆ S
    ∧ (∀(y : set N), y ∈ t → ∃(x : set M), x ∈ S₂ ∧ (x = f '- y))
    ∧ (∀(U : set M), U ⊆ ⋃₀ S₂ → f ' U ⊆ ⋃₀ t)
    ∧ finite t), from @finite_preimage_subset_finite_image_subset _ _ _ _
      S f S₂ (and.left (and.right H9)) H20,
  have H10 : t ⊆ S, from and.left H21,
  have H13 : finite t, from (and.right (and.right (and.right H21))),
  have H14 : (f ' U) ⊆ ⋃₀ t, from
    (and.left (and.right (and.right H21))) U (and.right (and.right H9)),
  exists.intro t (and.intro H10 (and.intro H13 H14))

