namespace myVect
variable (α : Type u)


inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)

def head : Nat → Vect α (n+1) → α
  | _, .cons a _ => a

def tail : Nat → Vect α (n+1) → Vect α n
  | _, .cons _ as => as

def map (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n
  | 0,   .nil,       .nil       => .nil
  | _, .cons a as, .cons b bs => .cons (f a b) (map f as bs)

def append_vectors {α : Type u} : {n : Nat} → {m : Nat} → Vect α n → Vect α m → Vect α (m+n)
  | 0, _, .nil, vm => vm
  | _, _, .cons a as, vm => .cons a (append_vectors as vm)
