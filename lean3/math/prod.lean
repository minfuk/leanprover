namespace prod
  universe variables u v
  variables {A B : Type} {a₁ a₂ : A} {b₁ b₂ : B} {u : A × B}

  def pr₁ {α : Type u} {β : Type v} (p : α × β) := @fst _ _ p
  def pr₂ {α : Type u} {β : Type v} (p : α × β) := @snd _ _ p

  theorem pair_eq : a₁ = a₂ → b₁ = b₂ → (a₁, b₁) = (a₂, b₂) :=
  assume H1 H2, H1 ▸ H2 ▸ rfl

  theorem proj_pair_eq (p : prod A B) : p = (pr₁ p, pr₂ p) :=
  begin
    cases p,
    apply rfl
  end

  protected theorem eq {p₁ p₂ : prod A B} : pr₁ p₁ = pr₁ p₂ → pr₂ p₁ = pr₂ p₂ → p₁ = p₂ :=
    take H1 H2,
    calc p₁
          = (pr₁ p₁, pr₂ p₁) : proj_pair_eq p₁
      ... = (pr₁ p₂, pr₂ p₂) : pair_eq H1 H2
      ... = p₂ : eq.symm (proj_pair_eq p₂)

end prod
