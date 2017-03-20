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

end universal