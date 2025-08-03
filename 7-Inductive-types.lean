set_option pp.fieldNotation.generalized false

inductive NatNum
  | zero : NatNum
  | succ : NatNum → NatNum

namespace NatNum

def add (a:NatNum) (b:NatNum) :=
  match a with
  | .zero => b
  | .succ pre => .succ (add pre b)

infixl:65 " + " => add

def mult (a:NatNum) (b:NatNum) : NatNum :=
  match a with
  | .zero => .zero
  | .succ pre => .add (mult pre b) b

infixl:70 " * " => mult


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

infixl:70 " ** " => pow


theorem add_zero_right (a : NatNum) : add a zero = a := by
  induction a with
    | zero => simp [add]
    | succ pre hyp =>
      simp [add]
      exact hyp

theorem add_zero_left (a : NatNum) : add zero a = a := by
  induction a with
    | zero => simp [add]
    | succ pre hyp =>
      simp [add, hyp]

theorem aux_lemm1  (a b : NatNum) : add a (succ b) = succ (add a b) := by
  induction a with
    | zero => simp [add]
    | succ pre hyp =>
      simp [add]
      exact hyp

theorem add_commutative (a b : NatNum) : add a b = add b a := by
  induction b with
    | zero => simp [add, add_zero_right]
    | succ pre hyp => simp [add, add_zero_right, ← hyp, aux_lemm1]


theorem mult_zero (a : NatNum) : a * zero = zero := by
  induction a with
    | zero => simp [mult]
    | succ pre hyp =>
      simp [mult, add_zero_right, hyp]

theorem mutl_identity (a : NatNum) : a * succ zero = a := by
  induction a with
    | zero => simp [mult]
    | succ pre hyp =>
      simp [mult, hyp]
      rw [add_commutative]
      simp [add]

theorem add_ass (a b c: NatNum) : a + (b + c) = (a + b) + c := by
  induction a with
  | zero => simp [add]
  | succ pre hyp => simp [add, hyp]

theorem aux_lemma2 (a b: NatNum) : a * succ b = a * b + a := by
  induction a with
    | zero => simp [mult, mult_zero, add_zero_left, mutl_identity]
    | succ pre hyp =>
      simp [mult, add, hyp , aux_lemm1]
      simp [←add_ass]
      simp [add_commutative b pre]


theorem mult_commutative (a b : NatNum) : a * b =  b * a := by
  induction b with
    | zero => simp [mult, mult_zero]
    | succ pre hyp => simp [mult, ←hyp, aux_lemma2]
