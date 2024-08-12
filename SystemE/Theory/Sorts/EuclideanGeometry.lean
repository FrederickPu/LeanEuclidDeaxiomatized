universe u v w


class PreEuclideanGeometry (Point : Type u) (Line : Type v) (Circle : Type w) where

namespace PreEuclideanGeometry

variable {Point : Type u} {Line : Type v} {Circle : Type w}

inductive Angle (E : PreEuclideanGeometry Point Line Circle)
| ofPoints (a b c : Point) : Angle E

inductive Triangle (E : PreEuclideanGeometry Point Line Circle)
| ofPoints (a b c : Point) : Triangle E

inductive Segment (E : PreEuclideanGeometry Point Line Circle)
| endpoints (a b : Point) : Segment E

end PreEuclideanGeometry

class EuclideanGeometry (Point : Type u) (Line : Type v) (Circle : Type w) extends PreEuclideanGeometry Point Line Circle where
(testAx1 : ∀ x : toPreEuclideanGeometry.Angle, x = x)
(testAx2 : ∀ x : toPreEuclideanGeometry.Triangle, x = x)
(testAx3 : ∀ x : toPreEuclideanGeometry.Segment, x = x)
