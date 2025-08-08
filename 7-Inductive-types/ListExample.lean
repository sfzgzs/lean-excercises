open List

theorem append_nil (as : List α) :
    as ++ nil = as := by
    induction as with
    | nil => simp
    | cons head tail hyp => simp

@[simp]
def len (l : List Nat)  : Nat :=
  match l with
  | nil => 0
  | cons _ tail => 1 + (len tail)

@[simp]
theorem len_addition : len (xs ++ ys) = len xs + len ys := by
  induction xs with
  | nil => simp
  | cons head tail hyp => simp [hyp, Nat.add_assoc]

theorem len_reverse : len (reverse xs) = len xs := by
  induction xs with
  | nil => simp
  | cons head tail hyp => simp [hyp, Nat.add_comm]
@[simp]
def myReverse : List Nat → List Nat
  | nil => nil
  | cons head tail => myReverse tail ++ [head]

theorem myReverse_append (a b : List Nat) :
  myReverse (a ++ b) = (myReverse b) ++ (myReverse a) := by
  induction a with
  | nil => simp
  | cons head tail hyp =>
    simp [List.append_assoc, hyp]


theorem myReverse_singleton (x : Nat) :
  myReverse [x] = [x] := by simp

theorem reverse_of_reverse (l : List Nat) : myReverse (myReverse l) = l := by
  induction l with
  | nil => simp
  | cons head tail hyp =>
    simp [myReverse_append, hyp]
