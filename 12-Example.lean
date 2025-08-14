open Classical


inductive Term where
  | var : String → Term
  | true
  | false
  | and : Term → Term → Term
  | or : Term → Term → Term

inductive Stmt where
  | skip : Stmt
  | assign : String → Term → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : Term → Stmt → Stmt → Stmt
  -- | while : Term → Stmt → Stmt


abbrev State := String → Bool

def evalTerm (t : Term) (σ : State) : Bool :=
  match t with
  | .var s => σ s
  | .true => Bool.true
  | .false => Bool.false
  | .and t₁ t₂ => Bool.and (evalTerm t₁ σ ) ( evalTerm t₂ σ)
  | .or t₁ t₂ => Bool.or (evalTerm t₁ σ ) ( evalTerm t₂ σ)


def evalStmt : Stmt →  State → State
  | .skip, σ₁ => σ₁
  | .assign s t, σ₁ => fun s' => if s = s' then evalTerm t σ₁ else σ₁ s'
  | .seq s₁ s₂, σ₁ => evalStmt s₂ (evalStmt s₁ σ₁)
  | .ifThenElse b s₁ s₂, σ₁ => if evalTerm b σ₁ then evalStmt s₁ σ₁ else evalStmt s₂ σ₁
