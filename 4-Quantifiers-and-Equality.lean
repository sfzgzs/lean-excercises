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
