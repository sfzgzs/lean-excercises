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

def eval (varsEval : Nat → Bool) : Formula → Bool
  | .bool b => b
  | .var v => varsEval v
  | .neg f => prop_neg (eval varsEval f)
  | .and f1 f2 => prop_and (eval varsEval f1) (eval varsEval f2)
  | .or f1 f2 => prop_or (eval varsEval f1) (eval varsEval f2)


def substitute (var_index : Nat) (subFor : Formula) (mainFormula : Formula) : Formula :=
  match mainFormula with
  | .var v =>
    if v = var_index then subFor else .var v
  | .bool b => .bool b
  | .neg f => .neg (substitute var_index subFor f)
  | .and f1 f2 => .and
    (substitute var_index subFor f1)
    (substitute var_index subFor f2)
  | .or f1 f2 => .or
    (substitute var_index subFor f1)
    (substitute var_index subFor f2)


def complexity_depth (f : Formula) : Nat :=
  match f with
  | .bool _ => 1
  | .var _ => 1
  | .neg f => complexity_depth f + 1
  | .and f1 f2 =>
      (Nat.max (complexity_depth f1) (complexity_depth f2)) + 1
  | .or f1 f2 =>
      (Nat.max (complexity_depth f1) (complexity_depth f2)) + 1



def complexity_nodes_count (f : Formula) : Nat :=
  match f with
  | .bool _ => 1
  | .var _ => 1
  | .neg f => 1 + complexity_nodes_count f
  | .and f1 f2 =>
    1 + Nat.max (complexity_nodes_count f1) (complexity_nodes_count f2)
  | .or f1 f2 =>
    1 + Nat.max (complexity_nodes_count f1) (complexity_nodes_count f2)
