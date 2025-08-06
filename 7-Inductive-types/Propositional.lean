namespace MyProp

inductive Bool
  | true
  | false

def prop_and (b1 : Bool) (b2 : Bool) :=
  match b1 with
  | .true => b2
  | .false => .false

def prop_or (b1 : Bool) (b2 : Bool) :=
  match b1 with
  | .false => b2
  | .true => .true

def prop_neg (b : Bool) : Bool :=
  match b with
  | .true => .false
  | .false => .true

inductive Formula
  | bool : Bool → Formula
  | var : Nat → Formula
  | neg : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula

def eval (vars_eval : Nat → Bool) : Formula → Bool
  | .bool b => b
  | .var v => vars_eval v
  | .neg f => prop_neg (eval vars_eval f)
  | .and f1 f2 => prop_and (eval vars_eval f1) (eval vars_eval f2)
  | .or f1 f2 => prop_or (eval vars_eval f1) (eval vars_eval f2)
