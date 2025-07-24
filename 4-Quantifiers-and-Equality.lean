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
