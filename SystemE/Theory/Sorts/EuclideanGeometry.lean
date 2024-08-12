universe u v w


structure PreEuclideanGeometry where
  (Point : Type u) (Line : Type v) (Circle : Type w)
  onLine : Point → Line → Prop
  sameSide : Point → Point → Line → Prop
  collinear (a b c : Point) : Prop
  between : Point → Point → Point → Prop
  onCircle : Point → Circle → Prop
  insideCircle : Point → Circle → Prop
  isCentre : Point → Circle → Prop
  intersectsLine : Line → Line → Prop
  intersectsCircle₁ : Line → Circle → Prop
  intersectsCircle₂ : Circle → Circle → Prop

namespace PreEuclideanGeometry

variable {Point : Type u} {Line : Type v} {Circle : Type w}

inductive Angle (E : PreEuclideanGeometry)
| ofPoints (a b c : Point) : Angle E

inductive Triangle (E : PreEuclideanGeometry)
| ofPoints (a b c : Point) : Triangle E

inductive Segment (E : PreEuclideanGeometry)
| endpoints (a b : Point) : Segment E

variable {E : PreEuclideanGeometry}

namespace Point

def sameSide := E.sameSide
def onLine := E.onLine
def onCircle := E.onCircle
def insideCircle := E.insideCircle

@[simp]
abbrev outsideCircle : E.Point → E.Circle → Prop :=
λ p c => ¬ p.insideCircle c ∧ ¬ p.onCircle c

@[simp]
abbrev opposingSides : E.Point → E.Point → E.Line → Prop :=
  λ a b l => ¬ a.onLine l  ∧ ¬ b.onLine l ∧ ¬ sameSide a b l

end Point

@[simp]
abbrev distinctPointsOnLine : E.Point → E.Point → E.Line → Prop := λ P Q L => P.onLine L ∧ Q.onLine L ∧ P ≠ Q

namespace Line

def intersectsLine := E.intersectsLine
def intersectsCircle := E.intersectsCircle₁

end Line

namespace Circle

def intersectsCircle := intersectsCircle₂

end Circle

@[simp]
abbrev formTriangle (a b c : E.Point) (AB BC CA : E.Line) : Prop :=
  distinctPointsOnLine a b AB ∧
  b.onLine BC ∧ c.onLine BC ∧ c.onLine CA ∧ a.onLine CA ∧
  AB ≠ BC ∧ BC ≠ CA ∧ CA ≠ AB

@[simp]
abbrev formRectilinearAngle (a b c : E.Point) (AB BC : E.Line) :=
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC

@[simp]
abbrev formParallelogram (a b c d : E.Point) (AB CD AC BD : E.Line) : Prop :=
    a.onLine AB ∧ b.onLine AB ∧ c.onLine CD ∧ d.onLine CD ∧ a.onLine AC ∧ c.onLine AC ∧ distinctPointsOnLine b d BD ∧
    (a.sameSide c BD) ∧ ¬(AB.intersectsLine CD) ∧ ¬(AC.intersectsLine BD)


end PreEuclideanGeometry

class EuclideanGeometry extends PreEuclideanGeometry where
  intersection_lines : ∀ (L M : Line), L.intersectsLine M →
    ∃ a : Point, (a.onLine L) ∧ (a.onLine M)
  intersections_circle_line : ∀ (α : Circle) (L : Line), L.intersectsCircle α →
    ∃ (a b : Point), (a.onCircle α) ∧ (a.onLine L) ∧ (b.onCircle α) ∧ (b.onLine L) ∧ a ≠ b
  intersection_circle_line_between_points : ∀ (α : Circle) (L : Line) (b c :Point),
    (b.insideCircle α) ∧ (b.onLine L) ∧ (c.outsideCircle α) ∧ (c.onLine L) →
    ∃ a : Point, (a.onCircle α) ∧ (a.onLine L) ∧ (between b a c)
-- (testAx1 : ∀ x : toPreEuclideanGeometry.Angle, x = x)
-- (testAx2 : ∀ x : toPreEuclideanGeometry.Triangle, x = x)
-- (testAx3 : ∀ x : toPreEuclideanGeometry.Segment, x = x)
