
section
  universe variables u v
  variables {α α' : Type u} {β β' : α → Type v}

  theorem hcongr_fun {f : Π x, β x} {f' : Π x, β' x} (a : α) (H₁ : f == f') (H₂ : β = β') :
    f a == f' a :=
  begin
    cases H₂, cases H₁, reflexivity
  end

  theorem hcongr_arg (f : Π x, β x) {a b : α} (H : a = b) : f a == f b :=
  H ▸ (heq.refl (f a))
end

section
  universe variables u v
  variables {α α' : Type u} {β β' : α → Type v}

  theorem eq_rec_to_heq {a a' : α} {b : β a} {b' : β a'}
    (H₁ : a = a') (H₂ : @eq.rec_on α a β a' H₁ b = b') : b == b' :=
    by subst H₁; subst H₂

  theorem cast_to_heq {a : α} {a' : α'} {H₁ : α = α'} (H₂ : cast H₁ a = a') : a == a' :=
    eq_rec_to_heq H₁ H₂

  theorem pi_eq (H : β = β') : (Π x, β x) = (Π x, β' x) :=
    by subst H

  theorem cast_app (H : β = β') (f : Π x, β x) (a : α) :
    cast (pi_eq H) f a == f a :=
    hcongr_fun a (cast_heq (pi_eq H) f) (eq.symm H)

  theorem hfunext {f : Π (x : α), β x} {g : Π (x : α), β' x}
    (H : ∀ a, f a == g a) : f == g :=
    cast_to_heq (funext (λ a, eq_of_heq (heq.trans (cast_app (funext (λ x, type_eq_of_heq (H x))) f a) (H a))))

end