import logic.eq data.set.basic data.set.basic data.set.function data.finset.basic
open eq eq.ops set classical finset

variable {X : Type}

section large_unions 
  variables {I : Type} 
  variable a : set I 
  variable b : I → set X 
  variable C : set (set X) 


  definition sUnion : set X := {x : X | ∃₀ c ∈ C, x ∈ c} 
  definition sInter : set X := {x : X | ∀₀ c ∈ C, x ∈ c} 


  prefix `⋃₀`:110 := sUnion 
  prefix `⋂₀`:110 := sInter 


  definition Union  : set X := {x : X | ∃i, x ∈ b i} 
  definition Inter  : set X := {x : X | ∀i, x ∈ b i} 


  notation `⋃` binders `, ` r:(scoped f, Union f) := r 
  notation `⋂` binders `, ` r:(scoped f, Inter f) := r 


  definition bUnion : set X := {x : X | ∃₀ i ∈ a, x ∈ b i} 
  definition bInter : set X := {x : X | ∀₀ i ∈ a, x ∈ b i} 


  notation `⋃` binders ` ∈ ` s `, ` r:(scoped f, bUnion s f) := r 
  notation `⋂` binders ` ∈ ` s `, ` r:(scoped f, bInter s f) := r 

 
end large_unions 

/-
structure topspace [class] (a : set X) (openset : set (set X) → Prop) :=
(ts_univ : openset univ)
(ts_empty : openset ∅)
(ts_inter : ∀U1 U2 : set (set X), openset U1 → openset U2 → openset (U1 ∩ U2))
(ts_union : Π {I : Type} (b : I → set (set X)),
  (∀i : I, openset (b i)) → (openset (⋃ i, b i)))
-/

definition preimage {A B:Type} (f : A → B) (Y : set B) : set A := { x | f x ∈ Y }

structure topspace [class] (a : set X) (openset : set X → Prop) :=
(ts_univ : openset a)
(ts_empty : openset ∅)
(ts_inter : ∀U1 U2 : set X, openset U1 → openset U2 → openset (U1 ∩ U2))
(ts_union : Π {I : Type} (b : I → set X),
  (∀i : I, openset (b i)) → (openset (⋃ i, b i)))

variables {Y : Type}

/-
definition preimagex (f : set X → set Y) (V : set (set Y)) : set (set X) :=
  { x : set X | V (f x) }
--  { x :set X | λ(x : X), V (f x) }
--infix ` ' ` := image 

structure continuous [class] (a : set X) (b : set Y)
  (xopen : set (set X) → Prop) (yopen : set (set Y) → Prop)
  [topspace a xopen] [topspace b yopen] (f : set X → set Y) :=
(cont_preim : ∀V : set (set Y), yopen V → xopen (preimagex f V))

structure connected [class] (a : set X) (openset : set (set X) → Prop)
  (s : set (set X)) [topspace a openset] :=
(conn_insep : ∀U1 U2 : set (set X),
  openset U1 → openset U2 → s ⊆ (U1 ∪ U2)
    → (∃(x1 : set X), x1 ∈ (s ∩ U1))
    → (∃(x2 : set X), x2 ∈ (s ∩ U2))
    → ∃(x : set X), x ∈ (s ∩ (U1 ∩ U2)))

definition imagex (f : set X → set Y) (U : set (set X)) : set (set Y) :=
--  { y : set Y | ∃(x : set X), x ∈ U ∧ f x = y }
  { y : set Y | ∃(x : set X), (U x) ∧ f x = y }

lemma a1 (f : set X → set Y) (U : set (set X)) (V : set (set Y)) :
  ∀(y : set Y), y ∈ (imagex f U) ∩ V → ∃(x : set X), x ∈ U ∩ (preimage f V) := sorry
begin
  intro a,
  intro H,
  have ∃(x : set X), x ∈ U ∧ f x = a, from a ∈ imagex f U,
  have x ∈ (preimagex f V), from f x ∈ V,
  apply and.intro
end
lemma a2 : y ∈ V → ∀x, f x = y → x ∈ (preimagex f V) := trivial
lemma a3 : x ∈ U → (f x) ∈ (imagex f U) := trivial
lemma a4 : x ∈ (preimagex f V) → (f x) ∈ V := trivial

lemma a2 (f : set X → set Y) (U : set (set X)) (V : set (set Y)) :
  ∀(x : set X), x ∈ U ∩ (preimage f V) → (f x) ∈ (imagex f U) ∩ V := sorry
begin
  intros,
end
-/

structure continuous [class] (a : set X) (b : set Y)
  (xopen : set X → Prop) (yopen : set Y → Prop)
  [topspace a xopen] [topspace b yopen] (f : X → Y) :=
(cont_preim : ∀V : set Y, yopen V → xopen (preimage f V))

structure connected [class] (a : set X) (openset : set X → Prop)
  (s : set X) [topspace a openset] :=
(conn_insep : ∀U1 U2 : set X,
  openset U1 → openset U2 → s ⊆ (U1 ∪ U2)
/-
    → (∃(x1 : X), x1 ∈ (s ∩ U1))
    → (∃(x2 : X), x2 ∈ (s ∩ U2))
    → ∃(x : X), x ∈ (s ∩ (U1 ∩ U2)))
-/
    → (s ∩ U1) ≠ ∅ → (s ∩ U2) ≠ ∅ → (s ∩ (U1 ∩ U2)) ≠ ∅)

theorem a1 (u : set X) (f : X → Y) :
  ∀x, x ∈ u → (f x) ∈ (image f u) :=
begin
  intro a,
  intro H,
--  apply mem_image H rfl,
  apply exists.intro a (and.intro H rfl),
end

theorem mem_of_mem_preimage' (f : X → Y) {x : X} {a : set Y} :
  x ∈ (preimage f a) → f x ∈ a :=
  assume H, H

theorem mem_of_mem_preimage {f : X → Y} {x : X} {a : set Y}
  (H : x ∈ (preimage f a)) : f x ∈ a :=
  mem_of_mem_preimage' f H

theorem mem_preimage {f : X → Y} {x : X} {a : set Y} :
  f x ∈ a → x ∈ (preimage f a) := assume H, H

theorem preimage_subset {a b : set Y} (f : X → Y) (H : a ⊆ b) :
  (preimage f a) ⊆ (preimage f b) :=
  take x, assume Hx : x ∈ (preimage f a),
  have H1 : f x ∈ a, from mem_of_mem_preimage Hx,
  have H2 : f x ∈ b, from mem_of_subset_of_mem H H1,
  show x ∈ (preimage f b), from mem_preimage H2

theorem preimage_of_image_subset (f : X → Y) {a : set X} :
  a ⊆ (preimage f (image f a)) :=
  take x, assume Hx : x ∈ a,
  have H1 : f x ∈ image f a, from mem_image_of_mem f Hx,
  show x ∈ (preimage f (image f a)), from mem_preimage H1

theorem preimage_of_image_subset_of_set (f : X → Y) {a : set X} {b : set Y} :
  (image f a) ⊆ b → a ⊆ preimage f b :=
begin
  intro H,
  apply subset.trans (preimage_of_image_subset f) (preimage_subset f H)
end

theorem preimage_inter {f : X → Y} {a b : set Y} :
  preimage f (a ∩ b) = (preimage f a) ∩ (preimage f b) :=
ext (take x, iff.intro
  (assume H : x ∈ preimage f (a ∩ b),
    have H1 : f x ∈ (a ∩ b), from mem_of_mem_preimage H,
    and.intro
      (have H2 : f x ∈ a, from and.left H1,
        show x ∈ (preimage f a), from mem_preimage H2)
      (have H3 : f x ∈ b, from and.right H1,
        show x ∈ (preimage f b), from mem_preimage H3))
  (assume H : x ∈ (preimage f a) ∩ (preimage f b),
    have H1 : f x ∈ (a ∩ b), from
      and.intro
        (have H2 : x ∈ (preimage f a), from and.left H,
          mem_of_mem_preimage H2)
        (have H3 : x ∈ (preimage f b), from and.right H,
          mem_of_mem_preimage H3),
    mem_preimage H1))

theorem preimage_union {f : X → Y} {a b : set Y} :
  preimage f (a ∪ b) = (preimage f a) ∪ (preimage f b) :=
ext (take x, iff.intro
  (assume H : x ∈ preimage f (a ∪ b),
    have H1 : f x ∈ a ∪ b, from mem_of_mem_preimage H,
    or.elim H1
      (suppose f x ∈ a, or.inl (mem_preimage this))
      (suppose f x ∈ b, or.inr (mem_preimage this)))
  (assume H : x ∈ (preimage f a) ∪ (preimage f b),
    have H1 : f x ∈ (a ∪ b), from
      or.elim H
        (suppose x ∈ (preimage f a), or.inl(mem_of_mem_preimage this))
        (suppose x ∈ (preimage f b), or.inr(mem_of_mem_preimage this)),
    mem_preimage H1))

theorem ne_empty_of_mem {s : set X} {x : X} (H : x ∈ s) : s ≠ ∅ := 
begin intro Hs, rewrite Hs at H, apply not_mem_empty _ H end 

theorem exists_mem_of_ne_empty {s : set X} (H : s ≠ ∅) : ∃ x, x ∈ s := 
by_contradiction (assume H', H (eq_empty_of_forall_not_mem (forall_not_of_not_exists H'))) 

theorem not_empty_preimage_inter_image_inter_not_empty
  {f : X → Y} {a : set X} {b : set Y} :
  a ∩ preimage f b ≠ ∅ → image f a ∩ b ≠ ∅ :=
begin
  intro H,
  obtain (x : X) (H1 : x ∈ (a ∩ preimage f b)), from exists_mem_of_ne_empty H,
  have H2 : x ∈ a, from and.left H1,
  have H3 : x ∈ preimage f b, from and.right H1,
  have H4 : f x ∈ b, from mem_of_mem_preimage H3,
  have H5 : f x ∈ image f a, from mem_image_of_mem f H2,
  have H6 : f x ∈ (image f a) ∩ b, from and.intro H5 H4,
  ne_empty_of_mem H6
end

theorem not_empty_image_inter_preimage_inter_not_empty
  {f : X → Y} {a : set X} {b : set Y} :
  image f a ∩ b ≠ ∅ → a ∩ preimage f b ≠ ∅ :=
begin
  intro H,
  obtain (y : Y) (H1 : y ∈ image f a ∩ b), from exists_mem_of_ne_empty H,
  have H2 : y ∈ image f a, from and.left H1,
  have H3 : y ∈ b, from and.right H1,
  obtain (x : X) (H4 : x ∈ a ∧ f x = y), from H2,
  have H5 : x ∈ a, from and.left H4,
  have H6 : f x ∈ b, from ((and.right H4)⁻¹) ▸ H3,
  have H7 : x ∈ preimage f b, from mem_preimage H6,
  have H8 : x ∈ a ∩ preimage f b, from and.intro H5 H7,
  ne_empty_of_mem H8
end

theorem aaaa (f : X → Y) {a : set X} {b : set Y}
  {xopen : set X → Prop} {yopen : set Y → Prop}
  [Ha : topspace a xopen] [Hb : topspace b yopen]
  [continuous a b xopen yopen f] {V : set Y} :
  yopen V → xopen (preimage f V) :=
begin
  intro H,
  apply @continuous.cont_preim X Y a b xopen yopen Ha Hb f,
  apply H
end

theorem b1 {a : set X} {xopen : set X → Prop}
  [Ha : topspace a xopen] {u u1 u2: set X} [connected a xopen u] :
  xopen u1 → xopen u2 → u ⊆ (u1 ∪ u2)
    → (u ∩ u1) ≠ ∅ → (u ∩ u2) ≠ ∅ → (u ∩ (u1 ∩ u2)) ≠ ∅ :=
begin
  intros H1 H2 H3 H4 H5,
  apply @connected.conn_insep X a xopen u Ha,
  apply H1, apply H2, apply H3, apply H4, apply H5,
end

theorem b2 {a : set X} {xopen : set X → Prop}
  [Ha : topspace a xopen] {u : set X} :
  (∀(u1 u2 : set X), xopen u1 → xopen u2 → u ⊆ (u1 ∪ u2)
    → (u ∩ u1) ≠ ∅ → (u ∩ u2) ≠ ∅ → (u ∩ (u1 ∩ u2)) ≠ ∅)
  → connected a xopen u :=
begin
  intro H,
  apply @connected.mk X a xopen u Ha H
end

/-
theorem lemma001 {f : X → Y} {U : set X} {v1 v2 : set Y}
 : U ∩ ((preimage f v1) ∩ (preimage f v2)) ≠ ∅
    → U ∩ preimage f (v1 ∩ v2) ≠ ∅ := sorry
-/

theorem image_connected {x : set X} {y : set Y}
  {xopen : set X → Prop} {yopen : set Y → Prop}
  [Hx : topspace x xopen] [Hy : topspace y yopen] {f : X → Y}
  [Hc : continuous x y xopen yopen f] {U : set X} :
  (connected x xopen U) → (connected y yopen (image f U)) :=
begin
  intro H,
  apply b2
    (take v1 v2 : set Y,
    assume H1 : yopen v1,
    assume H2 : yopen v2,
    assume H3 : (image f U) ⊆ (v1 ∪ v2),
    assume H4 : ((image f U) ∩ v1) ≠ ∅,
    assume H5 : ((image f U) ∩ v2) ≠ ∅,
    show (image f U) ∩ (v1 ∩ v2) ≠ ∅, from
    begin
      have H6 : U ⊆ preimage f (v1 ∪ v2), from preimage_of_image_subset_of_set f H3,
      have H9 : xopen (preimage f v1), from @aaaa X Y f x y xopen yopen Hx Hy Hc v1 H1,
      have H10 : xopen (preimage f v2), from @aaaa X Y f x y xopen yopen Hx Hy Hc v2 H2,
      have H7 : U ⊆ (preimage f v1) ∪ (preimage f v2), from preimage_union ▸ H6,
      have H11 : U ∩ preimage f v1 ≠ ∅,
        from not_empty_image_inter_preimage_inter_not_empty H4,
      have H12 : U ∩ preimage f v2 ≠ ∅,
        from not_empty_image_inter_preimage_inter_not_empty H5,
      have H13 : U ∩ ((preimage f v1) ∩ (preimage f v2)) ≠ ∅,
        from @b1 X x xopen Hx U (preimage f v1) (preimage f v2) H H9 H10 H7 H11 H12,
      have H14 : U ∩ preimage f (v1 ∩ v2) ≠ ∅, from ((preimage_inter)⁻¹) ▸ H13,
      apply not_empty_preimage_inter_image_inter_not_empty H14
    end)
end

theorem image_of_preimage_subset {f : X → Y} {a : set Y} :
  (image f (preimage f a)) ⊆ a :=
  take y, assume H1 : y ∈ (image f (preimage f a)),
  obtain (x : X) (H2 : x ∈ (preimage f a) ∧ f x = y), from H1,
  have H3 : f x ∈ a, from mem_of_mem_preimage (and.left H2),
  show y ∈ a, from (and.right H2) ▸ H3


-- theorem aaaaaa (a : finset X) (b : set X) : a ⊆ b := sorry
