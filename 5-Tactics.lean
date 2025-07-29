example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro  <;>
  . intro hpq
    exact And.intro hpq.right hpq.left

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro <;>
  . intro
    | Or.inl hp => apply Or.inr hp
    | Or.inr hq => apply Or.inl hq

example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  apply hnq
  apply hpq
  exact hp


example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro ⟨hp, hf⟩
    exact hf
  . intro hf
    contradiction


example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro
    | Or.inl hp => exact hp
    | Or.inr hf => contradiction
  . intro
    apply Or.inl
    assumption


example : (¬p ∨ q) → (p → q) := by
  intro hpq hp
  cases hpq with
    | inl hnp => contradiction
    | inr hq => exact hq


example : ¬p → (p → q) := by
  intro hnp hp
  exfalso
  exact hnp hp


example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩ ptoq
  apply hnq (ptoq hp)

example : ¬(p ↔ ¬p) := by
  intro hpnp
  have np : ¬ p := (fun hp: p => (hpnp.mp hp) hp);
  exact np (hpnp.mpr np)

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hqr
  by_cases hq : q
  . apply Or.inl
    intro hp
    exact hq
  . apply Or.inr
    intro hp
    specialize hqr hp
    cases hqr with
    | inl hq => contradiction
    | inr hr => exact hr


example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro hnpq
  by_cases hp : p
  . right
    intro hq
    exact hnpq ⟨hp,hq⟩
  . left
    exact hp

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  exact ⟨Or.inl hp, Or.inr (Or.inl hp), Or.inr (Or.inr hp)⟩
