
inductive Hidden.Term
  | constnt : Nat → Hidden.Term
  | Var : Nat → Hidden.Term
  | Plus : Hidden.Term → Hidden.Term → Hidden.Term
  | Times : Hidden.Term → Hidden.Term → Hidden.Term

def Hidden.term_eval (term : Hidden.Term) (vars : Nat → Nat) : Nat :=
  match term with
  | .constnt n => n
  | .Var n => vars n
  | .Plus n m => term_eval n vars + term_eval m vars
  | .Times n m => term_eval n vars * term_eval m vars
