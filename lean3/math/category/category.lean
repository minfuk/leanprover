universe variables u v

class category (ob : Type u) :=
  (hom : ob → ob → Type v)
  (comp : Π ⦃a b c : ob⦄, hom b c → hom a b → hom a c)
  (ID : Π (a : ob), hom a a)
  (assoc : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
    comp h (comp g f) = comp (comp h g) f)
  (id_left : Π ⦃a b : ob⦄ (f : hom a b), comp (ID _) f = f)
  (id_right : Π ⦃a b : ob⦄ (f : hom a b), comp f (ID _) = f)

namespace category
  variables {ob : Type u} [C : category ob]
  variables {a b c d : ob}
  include C

  def compose := @comp ob _

  attribute [reducible]
  def id {a : ob} : hom a a := ID a

  infixr `∘` := comp
  infixl `⟶`:25 := hom

  variables {h : hom c d} {g : hom b c} {f : hom a b} {i : hom a a}

  theorem id_compose (a : ob) : (ID a) ∘ id = id := id_left _

  theorem left_id_unique (H : Π {b} {f : hom b a}, i ∘ f = f) : i = id :=
    calc i = i ∘ id : eq.symm (id_right _)
       ... = id : H

  theorem right_id_unique (H : Π {b} {f : hom a b}, f ∘ i = f) : i = id :=
    calc i = id ∘ i : eq.symm (id_left _)
       ... = id : H

end category

structure Category :=
(carrier : Type u)
(struct : category carrier)

instance Category_to_sort : has_coe_to_sort Category :=
{S := _, coe := λ S, S^.carrier}

namespace category
  definition Mk {ob} (C) : Category := Category.mk ob C
  definition MK (a b c d e f g) : Category := Category.mk a (category.mk b c d e f g)

end category

theorem Category.equal (C : Category) : Category.mk C^.carrier C^.struct = C :=
Category.rec (λ ob c, rfl) C