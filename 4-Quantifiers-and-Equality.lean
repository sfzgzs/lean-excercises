variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨ w, hr ⟩ => hr

example (a : α) : r → (∃ x : α, r) :=
  fun hr:r => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (fun ⟨w, hp, hr⟩ => ⟨⟨w, hp⟩ , hr⟩ )
  (fun ⟨⟨w, hp⟩, hr⟩ => ⟨w, hp, hr⟩)


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (fun ⟨ w, hpq ⟩ => Or.elim hpq
    (fun hp: (p w) =>  Or.intro_left  (∃ x, q x) ⟨w, hp⟩ )
    (fun hq : (q w) => Or.intro_right (∃ x, p x) ⟨w, hq⟩)
  )
  (fun h : (∃ x, p x) ∨ (∃ x, q x) => Or.elim h
    (fun ⟨w, hp⟩ => ⟨w, Or.intro_left  (q w) hp ⟩)
    (fun ⟨w, hq⟩ => ⟨ w, Or.intro_right (p w) hq⟩)
  )


open Classical

def myForall : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  (fun hp =>
    (fun ⟨w, hnp⟩ =>
    show False from hnp (hp w) )
  )
  (fun h :  ¬ (∃ x, ¬ p x) =>
      fun x =>
        byContradiction
        (fun hnp : ¬ p x =>
          show False from h ⟨x, hnp⟩
        )
  )

def myExists (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (fun ⟨w, hp⟩ =>
    (fun a:(∀ x, ¬ p x) => show False from (a w) hp ) )
  (myExists α p)


def myForall2 : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h : (¬ ∃ x, p x) =>
    fun x =>
      fun hp:p x =>
      show False from
      h ⟨x, hp⟩
    )
  (fun h: (∀ x, ¬ p x) =>
      (fun ⟨w, hnp⟩=> (h w) hnp)
  )

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h:(¬ ∀ x, p x) =>
    byContradiction
    fun nhnp: ¬(∃ x, ¬ p x)=>
      show False from h ((myForall α p).2 nhnp)
  )
  (fun ⟨w, hnp⟩ =>
    fun h: ∀ x, p x =>
      show False from hnp (h w)
  )


example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
  (fun h:(∀ x, p x → r) =>
    fun ⟨w, hp⟩=> h w hp)
  (fun h : (∃ x, p x) → r =>
    fun x =>
      fun hhp: p x =>
        h ⟨x, hhp⟩
  )


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (
    fun hpq : ∀x, p x ∧ q x =>
      And.intro
        (fun x => (hpq x).left)
        (fun x => (hpq x).right)
  )
  (
    fun ⟨h1, h2⟩ =>
      fun x =>
      And.intro
        (h1 x)
        (h2 x)
  )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h : (∀ x, p x → q x) =>
    fun h2 : (∀ x, p x) =>
      (fun x =>
        h x (h2 x))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h: (∀ x, p x) ∨ (∀ x, q x) =>
    h.elim
    (fun h1: (∀ x, p x) => fun x => Or.intro_left (q x) (h1 x) )
    (fun h1: (∀ x, q x) => fun x => Or.intro_right (p x) (h1 x))


example : α → ((∀ x : α, r) ↔ r) :=
  fun a : α =>
    Iff.intro
      (fun h:(∀ _ , r) =>h a)
      (fun hr:r => fun _ => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
