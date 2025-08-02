set_option pp.fieldNotation.generalized false

inductive NatNum
  | zero : NatNum
  | succ : NatNum → NatNum

namespace NatNum

def add (a:NatNum) (b:NatNum) :=
  match a with
  | .zero => b
  | .succ pre => .succ (add pre b)

def mult (a:NatNum) (b:NatNum) : NatNum :=
  match a with
  | .zero => .zero
  | .succ pre => .add (mult pre b) b

def pred (a:NatNum) : NatNum :=
  match a with
  | .zero => .zero
  | .succ pre => pre

def truncSub (a:NatNum) (b:NatNum) : NatNum :=
  match b with
  | .zero => a
  | .succ pre => .pred (truncSub a pre)

def pow (a:NatNum) (b:NatNum) : NatNum :=
  match b with
  | .zero => .succ .zero
  | .succ pre => .mult (pow a pre) a

theorem add_zero (a : NatNum) : add a zero = a := by
  induction a with
    | zero => simp [add]
    | succ pre hyp =>
      simp [add]
      exact hyp

theorem aux_lemm1  (a b : NatNum) : add a (succ b) = succ (add a b) := by
  induction a with
    | zero => simp [add]
    | succ pre hyp =>
      simp [add]
      exact hyp

theorem add_commutative (a b : NatNum) : add a b = add b a := by
  induction b with
    | zero => simp [add, add_zero]
    | succ pre hyp => simp [add, add_zero, ← hyp, aux_lemm1]
