
inductive Hidden.Term
  | constnt : Nat → Hidden.Term
  | Var : Nat → Hidden.Term
  | Plus : Hidden.Term → Hidden.Term → Hidden.Term
  | Times : Hidden.Term → Hidden.Term → Hidden.Term

def Hidden.termEval (term : Hidden.Term) (vars : Nat → Nat) : Nat :=
  match term with
  | .constnt n => n
  | .Var n => vars n
  | .Plus n m => termEval n vars + termEval m vars
  | .Times n m => termEval n vars * termEval m vars
