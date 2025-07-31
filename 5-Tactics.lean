-- Section 3 Revisited (+Tactics)

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

-- Section 4 Revisited (+Tactics)


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro ⟨ w, hr ⟩
  exact hr

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exact ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro ⟨w, hp, hr⟩
    exact ⟨⟨w, hp⟩ , hr⟩
  . intro ⟨⟨w, hp⟩ , hr⟩
    exact ⟨ w, hp , hr⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro ⟨ w, hpq ⟩
    apply Or.elim hpq
    . intro hp
      exact Or.intro_left  (∃ x, q x) ⟨w, hp⟩
    . intro hq
      exact Or.intro_right  (∃ x, p x) ⟨w, hq⟩
  . intro hor
    apply Or.elim hor
    . intro ⟨w, hp⟩
      exact ⟨w, Or.intro_left  (q w) hp ⟩
    . intro ⟨w, hq⟩
      exact ⟨w, Or.intro_right (p w) hq⟩


def myForall : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro hp ⟨w, hnp⟩
    exact hnp (hp w)
  . intro h_cont x
    apply byContradiction
    intro hnp
    exact h_cont ⟨x, hnp⟩

def myExists (h : ¬ ∀ x, ¬ p x) : ∃ x, p x := by
  apply byContradiction
  intro h_n_exists
  apply h
  intro x hp
  exact h_n_exists ⟨x, hp⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h_exist h_n_forall
    cases h_exist with
    | intro w pw =>
      exact h_n_forall w pw
  . intro n_forall
    apply byContradiction
    intro h_n_exists
    apply n_forall
    intro x px
    exact h_n_exists ⟨x, px⟩

def myForall2 : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro n_exists x px
    apply n_exists ⟨x, px⟩
  . intro h_n_forall h_p_exists
    cases h_p_exists with
    | intro w hw =>
      exact h_n_forall w hw

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h1
    apply byContradiction
    intro h2
    apply h1
    intro x
    apply byContradiction
    intro hnp
    apply h2 ⟨x, hnp⟩
  . intro h1 h2
    cases h1 with
    | intro w hw =>
      exact hw (h2 w)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  . intro h1 h2
    cases h2 with
    | intro w hw => exact h1 w hw
  . intro h1 x hpx
    exact h1 ⟨x, hpx⟩



example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h1
    apply And.intro
    . intro x
      apply And.left (h1 x)
    . intro x
      apply And.right (h1 x)
  . intro ⟨h1, h2⟩ x
    exact ⟨h1 x, h2 x⟩


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h1 h2 x
  apply h1  x (h2 x)


example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  exact ⟨Or.inl hp, Or.inr (Or.inl hp), Or.inr (Or.inr hp)⟩
