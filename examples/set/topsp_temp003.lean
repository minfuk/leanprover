import logic.eq data.set.basic data.set.function data.set.finite
  theories.topology.basic
open eq eq.ops set classical topology

-- compact の定義を indexed を使ってみる
variables {I : Type}

-- この定義の仕方がおかしいので要調査
definition restrict {A : Type} (S : I → set A) (a : set I) (x : I) : set A :=
match (x ∈ a) with
| tt := S x
| ff := ∅
end

lemma restrict_mem {A : Type} (S : I → set A) {a : set I} {i : I} (H : i ∈ a)
  : (restrict S a) i = S i := sorry

lemma restrict_not_mem {A : Type} (S : I → set A) {a : set I} {i : I} (H : i ∉ a)
  : (restrict S a) i = ∅ := sorry

/-
variables {ix1 : I}
eval restrict (λi, univ) ∅ ix1
eval restrict (λi, univ) '{ix1} ix1
-/

variables {M : Type} [Tm : topology M]
include Tm

definition compact (U : set M) :=
  ∀(S : I → set M), ∀(a : set I),
    (S ' a) ⊆ opens M ∧ U ⊆ (⋃ i, (restrict S a) i)
  → ∃(b : set I), b ⊆ a ∧ finite b ∧ U ⊆ (⋃ i, (restrict S b) i)

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

lemma iff_mem_image_preimage (f : M → N) (S : I → set N) (a : set I) (i : I) (x : M) :
  f x ∈ (restrict S a) i ↔ x ∈ (restrict (λj, f '- (S j)) a) i :=
  let T := λj, f '- (S j) in
  iff.intro
    (assume Ha1 : f x ∈ (restrict S a) i,
    have Ha2 : i ∈ a, from
      by_contradiction
        (assume Ha3 : i ∉ a,
        have Ha4 : (restrict S a) i = ∅, from restrict_not_mem S Ha3,
        have Ha5 : (restrict S a) i ≠ ∅, from ne_empty_of_mem Ha1,
        not.elim Ha5 Ha4),
     have Ha6 : (restrict S a) i = S i, from restrict_mem S Ha2,
     have Ha7 : f x ∈ S i, from Ha6 ▸ Ha1,
     have Ha8 : x ∈ f '- (S i), from
       iff.elim_left (mem_preimage_iff f (S i) x) Ha7,
     have Ha9 : (restrict T a) i = f '- (S i), from restrict_mem T Ha2,
     Ha9⁻¹ ▸ Ha8)
    (assume Hb1 : x ∈ (restrict T a) i,
    have Hb2 : i ∈ a, from
      by_contradiction
        (assume Hb3 : i ∉ a,
        have Hb4 : (restrict T a) i = ∅, from restrict_not_mem T Hb3,
        have Hb5 : (restrict T a) i ≠ ∅, from ne_empty_of_mem Hb1,
        not.elim Hb5 Hb4),
     have Hb6 : (restrict T a) i = f '- (S i), from restrict_mem T Hb2,
     have Hb7 : x ∈ f '- (S i), from Hb6 ▸ Hb1,
     have Hb8 : f x ∈ S i, from
       iff.elim_right (mem_preimage_iff f (S i) x) Hb7,
     have Hb9 : (restrict S a) i = S i, from restrict_mem S Hb2,
     Hb9⁻¹ ▸ Hb8)

theorem compact_continuous_image_compact
  (f : M → N) [fc : continuous f] (U : set M) [Uc : @compact I _ _ U]
  : @compact I _ _ (f ' U) :=
  take S : I → set N,
  take a : set I,
  assume H1 : (S ' a) ⊆ opens N ∧ f ' U ⊆ (⋃ i, (restrict S a) i),
  let T := λi, f '- (S i) in
  have H3 : U ⊆ (⋃ i, (restrict T a) i), from
    take x,
    assume Ha1 : x ∈ U,
    have Ha3 : f x ∈ (⋃ i, (restrict S a) i),
      from mem_of_subset_of_mem (and.right H1) (mem_image_of_mem f Ha1),
    obtain (i0 : I) (Ha4 : f x ∈ (restrict S a) i0), from Ha3,
    have Ha5 : x ∈ (restrict T a) i0,
      from (iff.elim_left (iff_mem_image_preimage f S a i0 x)) Ha4,
    exists.intro i0 Ha5,
  have H8 : (T ' a) ⊆ opens M, from
    take b,
    assume Hb1 : b ∈ T ' a,
    obtain (i0 : I) (Hb2 : i0 ∈ a ∧ T i0 = b), from Hb1,
    have Hb4 : Open (S i0), from
      mem_of_subset_of_mem (and.left H1) (mem_image_of_mem S (and.left Hb2)),
    (and.right Hb2) ▸ (open_continuous_preimage_open fc Hb4),
  obtain (b : set I) (H21 : b ⊆ a ∧ finite b ∧ U ⊆ (⋃ i, (restrict T b) i)), from
    Uc T a (and.intro H8 H3),
  have H10 : b ⊆ a, from and.left H21,
  have H13 : finite b, from (and.left (and.right H21)),
  have H14 : (f ' U) ⊆ (⋃ i, (restrict S b) i), from
    take y,
    assume Hc1 : y ∈ f ' U,
    obtain (x : M) (Hc2 : x ∈ U ∧ f x = y), from Hc1,
    have Hc3 : x ∈ (⋃ i, (restrict T b) i),
      from mem_of_subset_of_mem (and.right (and.right H21)) (and.left Hc2),
    obtain (i0 : I) (Hc4 : x ∈ (restrict T b) i0), from Hc3,
    have Hc5 : f x ∈ (restrict S b) i0,
      from (iff.elim_right (iff_mem_image_preimage f S b i0 x)) Hc4,
    exists.intro i0 ((and.right Hc2) ▸ Hc5),
  exists.intro b (and.intro H10 (and.intro H13 H14))

