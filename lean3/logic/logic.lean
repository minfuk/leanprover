
universe variables u v w

theorem congr_arg2 : ∀ {α : Sort u} {β : Sort v} {γ : Sort w} {a₁ a₂ : α} {b₁ b₂ : β}
  (f : α → β → γ), a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂ :=
take α β γ a₁ a₂ b₁ b₂ f,
take H1 : a₁ = a₂,
take H2 : b₁ = b₂,
have Hb : ∀(b : β), f a₁ b = f a₂ b, from take b, congr_arg (λa, f a b) H1,
have Ha : ∀(a : α), f a b₁ = f a b₂, from take a, congr_arg (λb, f a b) H2,
calc f a₁ b₁ = f a₂ b₁ : Hb b₁ ... = f a₂ b₂ : Ha a₂
