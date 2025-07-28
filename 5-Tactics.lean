example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro hpq
    exact And.intro hpq.right hpq.left
  . intro hpq
    exact And.intro hpq.right hpq.left

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  exact ⟨Or.inl hp, Or.inr (Or.inl hp), Or.inr (Or.inr hp)⟩
