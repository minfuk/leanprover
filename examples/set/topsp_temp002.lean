import logic.eq data.set.basic data.set.function data.finset.basic
  theories.topology.basic
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

variables {N : Type} [Tn : topology N]
include Tn

lemma open_continuous_preimage_open {f : M → N} (C : continuous f) {V : set N} (O : Open V)
  : Open (f '- V) :=
begin
  let S := { U : set M | Open U ∧ f ' U ⊆ V },
  have H1 : ⋃₀ S ⊆ f '- V, from
    begin
      take x,
      assume H2 : x ∈ ⋃₀ S,
      obtain (U1 : set M) (H3 : U1 ∈ S ∧ x ∈ U1), from H2,
      have H4 : Open U1 ∧ f ' U1 ⊆ V, from and.left H3,
      have H5 : U1 ⊆ f '- V, from iff.elim_left image_subset_iff (and.right H4),
      mem_of_subset_of_mem H5 (and.right H3)
    end,
  have H6 : ⋃₀ S ⊇ f '- V, from
    begin
      take x,
      assume H7 : x ∈ f '- V,
      have H8 : f x ∈ V, from  iff.elim_right (mem_preimage_iff f V x) H7, 
      obtain (U2 : set M) (H9 : x ∈ U2 ∧ Open U2 ∧ f ' U2 ⊆ V), from C x V H8 O,
      have H10 : U2 ∈ S, from and.right H9,
      mem_sUnion (and.left H9) H10
    end,
  have H11 : ⋃₀ S = f '- V, from subset.antisymm H1 H6,
  have H12 : S ⊆ opens M, from take x, assume H13 : x ∈ S, and.left H13,
  have H14 : Open (⋃₀ S), from sUnion_mem_opens H12,
  apply H11 ▸ H14
end

corollary closed_continuous_preimage_closed {f : M → N} (C : continuous f) {V : set N} (H : closed V)
  : closed (f '- V) :=
  (preimage_compl f V) ▸ (open_continuous_preimage_open C H)

lemma not_empty_image_not_empty_preimage {f : M → N} {U : set M} (H : f ' U ≠ ∅)
  : U ≠ ∅ :=
begin
  obtain (y : N) (H1 : y ∈ f ' U), from exists_mem_of_ne_empty H,
  obtain (x : M) (H2 : x ∈ U ∧ f x = y), from H1,
  ne_empty_of_mem (and.left H2)
end

lemma not_empty_image_not_empty {f : M → N} {U : set M} (H : U ≠ ∅)
  : f ' U ≠ ∅ :=
begin
  obtain (x : M) (H1 : x ∈ U), from exists_mem_of_ne_empty H,
  have H2 : f x ∈ f ' U, from mem_image_of_mem f H1,
  ne_empty_of_mem H2
end

theorem connected_continuous_image_connected
  (f : M → N) [fc : continuous f] (U : set M) [Uc : connected U]
  : connected (f ' U) :=
begin
  take V1 V2 : set N,
  assume H1 : Open V1,
  assume H2 : Open V2,
  assume H3 : (f ' U) ⊆ (V1 ∪ V2),
  assume H4 : ((f ' U) ∩ V1) ≠ ∅,
  assume H5 : ((f ' U) ∩ V2) ≠ ∅,
  show (f ' U) ∩ (V1 ∩ V2) ≠ ∅, from
    begin
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
      apply ((image_inter f U (V1 ∩ V2))⁻¹) ▸ H16
    end
end

