variables (T1 T2 T3 : Type)
variables (P1 P2 P3 : Prop)

structure XXX {T1 T2 T3 : Type} {P1 P2 P3 :  Prop} :=
(x1 : T1)
(x2 : T2)
(x3 : T3)
(p1 : P1)
(p2 : P2)
(p3 : P3)

example (a b : @XXX T1 T2 T3 P1 P2 P3) (H1 : a^.x1 = b^.x1) (H2 : a^.x2 = b^.x2) (H3 : a^.x3 = b^.x3)
  : a = b :=
begin
  cases a,
  cases b,
  cases H1,
  cases H2,
  cases H3,
  apply rfl
end

check @congr
-- congr : ∀ {α : Sort u_1} {β : Sort u_2} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ → a₁ = a₂ → f₁ a₁ = f₂ a₂

check @congr_arg
-- congr_arg : ∀ {α : Sort u_1} {β : Sort u_2} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂

check @congr_fun
-- congr_fun : ∀ {α : Sort u_1} {β : α → Sort u_2} {f g : Π (x : α), β x}, f = g → ∀ (a : α), f a = g a

check @funext
-- funext : ∀ {α : Type u_1} {β : α → Type u_2} {f₁ f₂ : Π (x : α), β x}, (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂

check @proof_irrel
-- proof_irrel : ∀ {a : Prop} (h₁ h₂ : a), h₁ = h₂

