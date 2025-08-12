class Shape (S : Type u → Type v) (α : Type u) where
  area : S α → α

structure Rectangle (α : Type u) where
  width : α
  height : α

structure Triangle (α : Type u) where
  base : α
  height : α

instance : Shape Rectangle Nat where
  area r := r.width * r.height

instance : Shape Triangle Nat where
  area t := (t.base * t.height) / 2

inductive Color where
  | red | green | blue
deriving Repr

instance : ToString Color where
  toString
    | Color.red   => "red"
    | Color.green => "green"
    | Color.blue  => "blue"


structure ColoredRectangle (α : Type u) extends Rectangle α where
  color : Color

instance [Shape Rectangle α] : Shape ColoredRectangle α where
  area cr := Shape.area cr.toRectangle

def myRectangle : ColoredRectangle Nat :=
  { width := 5, height := 3, color := Color.blue }

def myTriangle : Triangle Nat :=
  { base := 10, height := 4 }

example : Shape.area myRectangle = 15 := rfl
example : Shape.area myTriangle = 20 := rfl
