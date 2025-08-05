namespace myProp

inductive Bool
  | True
  | False

def PropAnd (b1 : Bool) (b2 : Bool) :=
  match b1 with
  | .True => b2
  | .False => .False

def PropOr (b1 : Bool) (b2 : Bool) :=
  match b1 with
  | .False => b2
  | .True => .True

def PropNeg (b : Bool) : Bool :=
  match b with
  | .True => .False
  | .False => .True

inductive Formula
  | Bool : Bool → Formula
  | Var : Nat → Formula
  | Neg : Formula → Formula
  | And : Formula → Formula → Formula
  | Or : Formula → Formula → Formula

def Eval (varsEval : Nat → Bool) : Formula → Bool
  | .Bool b => b
  | .Var v => varsEval v
  | .Neg f => PropNeg (Eval varsEval f)
  | .And f1 f2 => PropAnd (Eval varsEval f1) (Eval varsEval f2)
  | .Or f1 f2 => PropOr (Eval varsEval f1) (Eval varsEval f2)
