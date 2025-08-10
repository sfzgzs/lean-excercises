structure Rectangle where
  width : Nat
  height : Nat

def Rectangle.area (r : Rectangle) : Nat :=
  r.width * r.height

inductive Color where
  | red | green | blue


structure ColoredRectangle extends Rectangle where
  color : Color


def myRectangle : ColoredRectangle :=
  { width := 5, height := 3, color := Color.blue }


example : myRectangle.area = 15 := rfl
