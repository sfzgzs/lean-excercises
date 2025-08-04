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
