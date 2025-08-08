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

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
deriving Repr

def sampleExpr : Expr :=
  .plus (.times (.var 0) (.const 7)) (.times (.const 2) (.var 1))

def eval (v : Nat → Nat) : Expr → Nat
  | .const n     => n
  | .var n       => v n
  | .plus e₁ e₂  => (eval v e₁) + (eval v e₂)
  | .times e₁ e₂ =>  (eval v e₁) * (eval v e₂)

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here. Done!
#eval eval sampleVal sampleExpr
