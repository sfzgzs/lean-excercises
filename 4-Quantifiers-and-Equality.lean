
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


def indepFunc : α → ((∀ x : α, r) ↔ r) :=
  fun a : α =>
    Iff.intro
      (fun h:(∀ _ , r) =>h a)
      (fun hr:r => fun _ => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h: (∀ x, p x ∨ r) =>
        byCases
        (fun hr : r => Or.intro_right (∀ x, p x) hr)
        (fun nhr : ¬r =>
          Or.intro_left r (fun x =>
            match h x with
            | Or.inl px => px
            | Or.inr r' => False.elim (nhr r')
          )
        )
    )
    (fun h : (∀ x, p x) ∨ r =>
      match h with
      | Or.inl forallxp => fun x => Or.inl (forallxp x)
      | Or.inr hr => fun _ => Or.inr hr
    )


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h : (∀ x, r → p x) =>
      fun hr : r =>
        fun x =>
        (h x) hr
    )
  (fun hr : r → ∀ x, p x =>
      fun x =>
        fun hr2 : r =>
          (hr hr2) x
  )

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)


def pnotp {p} : ¬(p ↔ ¬p) :=
  fun hpnp : p ↔ ¬p =>
    have np : ¬ p := (fun hp: p => (hpnp.mp hp) hp);
    np (hpnp.mpr np)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  pnotp (h barber)


def even (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

def prime (n : Nat) : Prop := ¬ (∃ k ≤ n, ∃ m < n, m ≠ 1 ∧ m * k = n)
def prime2 (n : Nat) : Prop := ∀ k : Nat, ∀ m : Nat, (k*m = n → k = 1 ∨ k = n)

def infinitely_many_primes : Prop := ∀ n : Nat, ∃ m > n, prime m
def Fermat_prime (n : Nat) : Prop := ∃ m : Nat, n = 2 ^ (2 ^ m) + 1
def infinitely_many_Fermat_primes : Prop := ∀ n : Nat, ∃ m > n, Fermat_prime m
def goldbach_conjecture : Prop := ∀ n > 2, (even n → ∃ x1 x2 : Nat, prime x1 ∧ prime x2 ∧ n = x1 + x2)
def Goldbach's_weak_conjecture : Prop :=
  ∀ n > 5, ¬ even n →
    ∃ x1 x2 x3: Nat,
      prime x1 ∧ prime x2 ∧ prime x3 ∧ n = x1 + x2 + x3
def Fermat's_last_theorem : Prop :=
  ∀ n : Nat, n > 2 →
    ¬ ∃ a b c: Nat, a ^ n + b ^ n = c ^ n ∧ a > 0 ∧ b > 0 ∧ c > 0
