import algebra.category.basic
  algebra.category.morphism
  algebra.category.functor
  algebra.category.constructions

open eq eq.ops category morphism functor category.product category.ops

structure universal_arrow {C D : Category} (c : C) (S : D ⇒ C) :=
  (r : D)
  (u : c ⟶ S r)
  (univ : ∀(d : D) (f : c ⟶ S d),
    ∃!(f' : r ⟶ d), (S f') ∘ u = f)

example {C D : Category} {c : C} {S : D ⇒ C}
  (x y : universal_arrow c S)
  {P : Prop} (H : (universal_arrow.r x) ≅ (universal_arrow.r y) → P) : P :=
  let xr := universal_arrow.r x in
  let yr := universal_arrow.r y in
  let xu := universal_arrow.u x in
  let yu := universal_arrow.u y in
  obtain f1 (H3 : (S f1) ∘ xu = yu), from
    exists_of_exists_unique (universal_arrow.univ x yr yu),
  obtain f2 (H4 : (S f2) ∘ yu = xu), from
    exists_of_exists_unique (universal_arrow.univ y xr xu),
  have H5 : (S (f2 ∘ f1)) ∘ xu = xu, from
    calc (S (f2 ∘ f1)) ∘ xu
          = ((S f2) ∘ (S f1)) ∘ xu : functor.respect_comp S f2 f1
      ... = (S f2) ∘ ((S f1) ∘ xu) : eq.symm (assoc (S f2) (S f1) xu)
      ... = (S f2) ∘ yu : H3
      ... = xu : H4,
  have H6 : (S (f1 ∘ f2)) ∘ yu = yu, from
    calc (S (f1 ∘ f2)) ∘ yu
          = ((S f1) ∘ (S f2)) ∘ yu : functor.respect_comp S f1 f2
      ... = (S f1) ∘ ((S f2) ∘ yu) : eq.symm (assoc (S f1) (S f2) yu)
      ... = (S f1) ∘ xu : H4
      ... = yu : H3,
  have H7' : (S (ID xr)) ∘ xu = xu, from
    calc (S (ID xr)) ∘ xu
          = (ID (S xr)) ∘ xu : eq.symm (functor.respect_id S xr)
      ... = xu : category.id_left xu,
  have H7 : f2 ∘ f1 = ID xr, from
    unique_of_exists_unique (universal_arrow.univ x xr xu) H5 H7',
  have H8' : (S (ID yr)) ∘ yu = yu, from
    calc (S (ID yr)) ∘ yu
          = (ID (S yr)) ∘ yu : eq.symm (functor.respect_id S yr)
      ... = yu : category.id_left yu,
  have H8 : f1 ∘ f2 = ID yr, from
    unique_of_exists_unique (universal_arrow.univ y yr yu) H6 H8',
  have H9 : is_iso f1, from is_iso.mk H7 H8,
  H (isomorphic.mk f1)

open classical

example {C D : Category} {c : C} {S : D ⇒ C}
  (x y : universal_arrow c S)
  : (universal_arrow.r x) ≅ (universal_arrow.r y) :=
  let xr := universal_arrow.r x in
  let yr := universal_arrow.r y in
  let xu := universal_arrow.u x in
  let yu := universal_arrow.u y in
  have H10 : ∃f1 f2, f2 ∘ f1 = ID xr ∧ f1 ∘ f2 = ID yr, from
    obtain f1 (H3 : (S f1) ∘ xu = yu), from
      exists_of_exists_unique (universal_arrow.univ x yr yu),
    obtain f2 (H4 : (S f2) ∘ yu = xu), from
      exists_of_exists_unique (universal_arrow.univ y xr xu),
    have H5 : (S (f2 ∘ f1)) ∘ xu = xu, from
      calc (S (f2 ∘ f1)) ∘ xu
            = ((S f2) ∘ (S f1)) ∘ xu : functor.respect_comp S f2 f1
        ... = (S f2) ∘ ((S f1) ∘ xu) : eq.symm (assoc (S f2) (S f1) xu)
        ... = (S f2) ∘ yu : H3
        ... = xu : H4,
    have H6 : (S (f1 ∘ f2)) ∘ yu = yu, from
      calc (S (f1 ∘ f2)) ∘ yu
            = ((S f1) ∘ (S f2)) ∘ yu : functor.respect_comp S f1 f2
        ... = (S f1) ∘ ((S f2) ∘ yu) : eq.symm (assoc (S f1) (S f2) yu)
        ... = (S f1) ∘ xu : H4
        ... = yu : H3,
    have H7' : (S (ID xr)) ∘ xu = xu, from
      calc (S (ID xr)) ∘ xu
            = (ID (S xr)) ∘ xu : eq.symm (functor.respect_id S xr)
        ... = xu : category.id_left xu,
    have H7 : f2 ∘ f1 = ID xr, from
      unique_of_exists_unique (universal_arrow.univ x xr xu) H5 H7',
    have H8' : (S (ID yr)) ∘ yu = yu, from
      calc (S (ID yr)) ∘ yu
            = (ID (S yr)) ∘ yu : eq.symm (functor.respect_id S yr)
        ... = yu : category.id_left yu,
    have H8 : f1 ∘ f2 = ID yr, from
      unique_of_exists_unique (universal_arrow.univ y yr yu) H6 H8',
    exists.intro f1 f2 (and.intro H7 H8),
  have (f1', f2'), from some2 H10,
  have H11 : f2' ∘ f1' = ID xr ∧ f1' ∘ f2' = ID yr, from some_spec2 H10,
  have H9 : is_iso f1', from is_iso.mk (and.left H11) (and.right H11),
  isomorphic.mk f1'
