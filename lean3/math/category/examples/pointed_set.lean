import init.data.set
import ..category

namespace pointed_set

  universe variables u v w t
  
  open category function

  structure pointed_set (α : Type u) :=
  (set : set α)
  (point : α)

  variables {α : Type u} {β : Type v}

  structure pointed_set_morphism (a : pointed_set α) (b : pointed_set β) :=
  (map : α → β)
  (point : map a^.point = b^.point)

  variables {γ : Type w}
  variables {a : pointed_set α} {b : pointed_set β} {c : pointed_set γ}

  theorem pointed_set_morphism_eq (f f' : pointed_set_morphism a b)
    (H : f^.map = f'^.map) : f = f' :=
    begin
      cases f,
      cases f',
      cases H,
      apply rfl
    end

  definition pointed_set_comp (f : pointed_set_morphism b c)
    (g : pointed_set_morphism a b) : pointed_set_morphism a c :=
    pointed_set_morphism.mk
      (f^.map ∘ g^.map)
      (calc (f^.map ∘ g^.map) a^.point
            = f^.map b^.point : congr_arg f^.map g^.point
        ... = c^.point : f^.point)

  definition pointed_set_ID (a : pointed_set α) : pointed_set_morphism a a :=
    pointed_set_morphism.mk
      (λ x, x)
      (rfl)

  variables {δ : Type t}
  variables {d : pointed_set δ}

  theorem pointed_set_assoc (f : pointed_set_morphism c d)
    (g : pointed_set_morphism b c) (h : pointed_set_morphism a b) :
    pointed_set_comp f (pointed_set_comp g h) = pointed_set_comp (pointed_set_comp f g) h :=
    pointed_set_morphism_eq
      (pointed_set_comp f (pointed_set_comp g h))
      (pointed_set_comp (pointed_set_comp f g) h)
      (@comp.assoc α β γ δ f^.map g^.map h^.map)

  theorem pointed_set_id_left (f : pointed_set_morphism a b) :
    pointed_set_comp (pointed_set_ID b) f = f :=
    pointed_set_morphism_eq
      (pointed_set_comp (pointed_set_ID b) f) f (rfl)

  theorem pointed_set_id_right (f : pointed_set_morphism a b) :
    pointed_set_comp f (pointed_set_ID a) = f :=
    pointed_set_morphism_eq
      (pointed_set_comp f (pointed_set_ID a)) f (rfl)

  structure Pointed_set :=
  (carrier : Type u)
  (struct : pointed_set carrier)

  instance Pointed_set_to_sort : has_coe_to_sort Pointed_set :=
  {S := _, coe := λ S, S^.carrier}

  definition pointed_set_category : category Pointed_set :=
    mk (λ a b, pointed_set_morphism a^.struct b^.struct)
      (λ a b c g f, pointed_set_comp g f)
      (λ a, pointed_set_ID a^.struct)
      (λ a b c d h g f, pointed_set_assoc h g f)
      (λ a b f, pointed_set_id_left f)
      (λ a b f, pointed_set_id_right f)

end pointed_set