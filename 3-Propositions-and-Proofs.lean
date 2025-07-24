example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun hpq : p ∧ q => (And.intro hpq.right hpq.left))
    (fun hpq : q ∧ p => (And.intro hpq.right hpq.left))

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun hpq : p ∨ q =>
      Or.elim hpq
        (fun hp : p => Or.intro_right q hp)
        (fun hq : q => Or.intro_left p hq)
    )
    (fun hqp : q ∨ p =>
      Or.elim hqp
      (fun hq : q => Or.intro_right p hq)
      (fun hp : p => Or.intro_left q hp)
    )

example : (p → q) → (¬q → ¬p) := fun hpq : p → q => fun nq : ¬ q => fun hp : p => False.elim (nq (hpq hp))

example : p ∧ False ↔ False :=
  Iff.intro
  (fun hpf : p ∧ False => hpf.right)
  False.elim

example : p ∨ False ↔ p :=
  Iff.intro
  (fun hpf: p ∨ False => Or.elim hpf id False.elim)
  (fun hp : p => Or.intro_left False hp)

axiom pqp_ax: p → q → p

example : (¬p ∨ q) → (p → q) :=
  fun hpq : ¬p ∨ q =>
    fun hp : p =>
      Or.elim hpq
        (fun np: ¬p => False.elim (np hp))
        (id)

example : ¬p → (p → q) :=
  fun np : ¬p =>
    fun hp : p =>
      False.elim (np hp)

example : p ∧ ¬q → ¬(p → q) :=
  fun pnq : p ∧ ¬q =>
    fun pq : p → q =>
      False.elim (pnq.right (pq (pnq.left)))

example : ¬(p ↔ ¬p) :=
  fun hpnp : p ↔ ¬p =>
    have np : ¬ p := (fun hp: p => (hpnp.mp hp) hp);
    np (hpnp.mpr np)

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hpqr : p → q ∨ r =>
    Or.elim (em q)
      (fun hq : q => Or.inl fun _ => hq )
      (fun hnq : ¬q =>
        Or.inr (fun hp:p =>
        let hqr :q ∨ r := hpqr hp;
        Or.elim (hqr)
        (fun hq : q => absurd hq hnq)
        (fun hr : r => hr)
        )
      )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun hnpq : ¬(p ∧ q) =>
    Or.elim (em p)
    (fun hp: p => Or.inr (
      fun hq : q => hnpq (And.intro hp hq)
    ))
    (fun hnp : ¬p => Or.inl hnp)
