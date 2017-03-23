import .category
import .morphism

namespace universal

  open category
  open morphism

  variables {C : Category}

  local infix ` ⟶ ` := @hom _ C^.struct
  local infix ` ∘ ` := @comp _ C^.struct _ _ _

  structure coproduct (a b : C) :=
  (c : C)
  (i : a ⟶ c)
  (j : b ⟶ c)
  (univ : ∀(d : C) (f : a ⟶ d) (g : b ⟶ d),
    ∃(h : c ⟶ d), f = h ∘ i ∧ g = h ∘ j
      ∧ (∀(h' : c ⟶ d), f = h' ∘ i → g = h' ∘ j → h' = h))

  private definition iso' (a b : C) := @isomorphic _ C^.struct a b

  local infix ` ≅ ` := iso'

  private definition ID := @ID _ C^.struct
  private definition assoc {a b c d : C} (h : c ⟶ d) (g : b ⟶ c) (f : a ⟶ b) := @assoc _ C^.struct _ _ _ _ h g f
  private definition id_left {a b : C} (f : a ⟶ b) := @id_left _ C^.struct _ _ f

  theorem coproduct_id {a b : C} (x : coproduct a b) :
    ∀h, x^.i = h ∘ x^.i → x^.j = h ∘ x^.j → h = ID (x^.c) :=
    take h,
    assume H1 : x^.i = h ∘ x^.i,
    assume H2 : x^.j = h ∘ x^.j,
    have H3 : ∀(h1 h2 : x^.c ⟶ x^.c), x^.i = h1 ∘ x^.i → x^.j = h1 ∘ x^.j
      → x^.i = h2 ∘ x^.i → x^.j = h2 ∘ x^.j → h1 = h2,
      from exists.elim (x^.univ (x^.c) (x^.i) (x^.j)) (
        take hx,
        assume H4 : x^.i = hx ∘ x^.i ∧ x^.j = hx ∘ x^.j
          ∧ ∀(h' : x^.c ⟶ x^.c), x^.i = h' ∘ x^.i → x^.j = h' ∘ x^.j → h' = hx,
        take h1, take h2,
        assume H5 : x^.i = h1 ∘ x^.i,
        assume H6 : x^.j = h1 ∘ x^.j,
        assume H7 : x^.i = h2 ∘ x^.i,
        assume H8 : x^.j = h2 ∘ x^.j,
        have H9 : h1 = hx, from (and.right (and.right H4)) h1 H5 H6,
        have H10 : h2 = hx, from (and.right (and.right H4)) h2 H7 H8,
        eq.trans H9 (eq.symm H10)),
    have H11 : x^.i = (ID x^.c) ∘ x^.i, from eq.symm (id_left x^.i), 
    have H12 : x^.j = (ID x^.c) ∘ x^.j, from eq.symm (id_left x^.j), 
    H3 h (ID x^.c) H1 H2 H11 H12

  noncomputable theorem coproduct_iso {a b : C} (x y : coproduct a b) : x^.c ≅ y^.c :=
    have H : ∃h1 h2, h2 ∘ h1 = ID x^.c ∧ h1 ∘ h2 = ID y^.c, from
      exists.elim (x^.univ y^.c y^.i y^.j)
        (take h1, 
        assume H1 : y^.i = h1 ∘ x^.i ∧ y^.j = h1 ∘ x^.j
          ∧ (∀(h' : x^.c ⟶ y^.c), y^.i = h' ∘ x^.i → y^.j = h' ∘ x^.j → h' = h1),
        exists.elim (y^.univ x^.c x^.i x^.j)
          (take h2,
          assume H2 : x^.i = h2 ∘ y^.i ∧ x^.j = h2 ∘ y^.j
            ∧ (∀(h' : y^.c ⟶ x^.c), x^.i = h' ∘ y^.i → x^.j = h' ∘ y^.j → h' = h2),
          have H3 : x^.i = h2 ∘ h1 ∘ x^.i, from
            calc x^.i
                  = h2 ∘ y^.i : and.left H2
              ... = h2 ∘ (h1 ∘ x^.i) : congr_arg (λx, h2 ∘ x) (and.left H1)
              ... = (h2 ∘ h1) ∘ x^.i : assoc h2 h1 x^.i,
          have H4 : x^.j = h2 ∘ h1 ∘ x^.j, from
            calc x^.j
                  = h2 ∘ y^.j : and.left (and.right H2)
              ... = h2 ∘ (h1 ∘ x^.j) : congr_arg (λx, h2 ∘ x) (and.left (and.right H1))
              ... = (h2 ∘ h1) ∘ x^.j : assoc h2 h1 x^.j,
          have H5 : y^.i = h1 ∘ h2 ∘ y^.i, from
            calc y^.i
                  = h1 ∘ x^.i : and.left H1
              ... = h1 ∘ (h2 ∘ y^.i) : congr_arg (λx, h1 ∘ x) (and.left H2)
              ... = (h1 ∘ h2) ∘ y^.i : assoc h1 h2 y^.i,
          have H6 : y^.j = h1 ∘ h2 ∘ y^.j, from
            calc y^.j
                  = h1 ∘ x^.j : and.left (and.right H1)
              ... = h1 ∘ (h2 ∘ y^.j) : congr_arg (λx, h1 ∘ x) (and.left (and.right H2))
              ... = (h1 ∘ h2) ∘ y^.j : assoc h1 h2 y^.j,
          have H7 : h2 ∘ h1 = ID x^.c, from coproduct_id x (h2 ∘ h1) H3 H4,
          have H8 : h1 ∘ h2 = ID y^.c, from coproduct_id y (h1 ∘ h2) H5 H6,
          exists.intro h1 (exists.intro h2 (and.intro H7 H8)))),
    have H' : ∃(iso : x^.c ≅ y^.c), iso = iso, from
      exists.elim H
        (take h1,
        assume H10,
        exists.elim H10
          (take h2,
          assume H9 : h2 ∘ h1 = ID x^.c ∧ h1 ∘ h2 = ID y^.c,
          exists.intro (@isomorphic.mk _ C^.struct _ _ h1
            (@is_iso.mk _ C^.struct _ _ h1 h2 (and.left H9) (and.right H9))) rfl)),
    classical.some H'

  structure coequalizer {a b : C} (f g : a ⟶ b) :=
  (e : C)
  (u : b ⟶ e)
  (i : u ∘ f = u ∘ g)
  (ii : ∀(c : C) (h : b ⟶ c), ∃!(h' : e ⟶ c), h = h' ∘ u)

  theorem coequalizer_univ_id {a b : C} {f g : a ⟶ b} (x : coequalizer f g) :
    ∀h, x^.u = h ∘ x^.u → h = ID (x^.e) :=
    have H :  ∀h1 h2, x^.u = h1 ∘ x^.u → x^.u = h2 ∘ x^.u → h1 = h2, from
      take h1,
      take h2,
      assume H1 : x^.u = h1 ∘ x^.u,
      assume H2 : x^.u = h2 ∘ x^.u,
      unique_of_exists_unique (x^.ii x^.e x^.u) H1 H2,
    take h,
    assume H3 : x^.u = h ∘ x^.u,
    have H4 : x^.u = (ID x^.e) ∘ x^.u, from eq.symm (id_left x^.u),
    H h (ID x^.e) H3 H4

  noncomputable theorem coequalizer_iso {a b : C} {f g : a ⟶ b}
    (x y : coequalizer f g) : x^.e ≅ y^.e :=
    have H : ∃h1 h2, h2 ∘ h1 = ID x^.e ∧ h1 ∘ h2 = ID y^.e, from
      exists_unique.elim (x^.ii y^.e y^.u)
        (take h1,
        assume H1 : y^.u = h1 ∘ x^.u,
        assume H1_ : _,
        exists_unique.elim (y^.ii x^.e x^.u)
          (take h2,
          assume H2 : x^.u = h2 ∘ y^.u,
          assume H2_ : _,
          have H3 : x^.u = (h2 ∘ h1) ∘ x^.u, from
            calc x^.u
                  = h2 ∘ y^.u : H2
              ... = h2 ∘ (h1 ∘ x^.u) : congr_arg (λ x, h2 ∘ x) H1
              ... = (h2 ∘ h1) ∘ x^.u : assoc h2 h1 x^.u,
          have H4 : y^.u = (h1 ∘ h2) ∘ y^.u, from
            calc y^.u
                  = h1 ∘ x^.u : H1
              ... = h1 ∘ (h2 ∘ y^.u) : congr_arg (λ x, h1 ∘ x) H2
              ... = (h1 ∘ h2) ∘ y^.u : assoc h1 h2 y^.u,
          have H5 : h2 ∘ h1 = ID x^.e ∧ h1 ∘ h2 = ID y^.e, from
            and.intro (coequalizer_univ_id x (h2 ∘ h1) H3)
              (coequalizer_univ_id y (h1 ∘ h2) H4),
          exists.intro h1 (exists.intro h2 H5))),
    have H' : ∃(iso : x^.e ≅ y^.e), iso = iso, from
      exists.elim H
        (take h1,
        assume H6,
        exists.elim H6
          (take h2,
          assume H7 : h2 ∘ h1 = ID x^.e ∧ h1 ∘ h2 = ID y^.e,
          exists.intro (@isomorphic.mk _ C^.struct _ _ h1
            (@is_iso.mk _ C^.struct _ _ h1 h2 (and.left H7) (and.right H7))) rfl)),
    classical.some H'

end universal