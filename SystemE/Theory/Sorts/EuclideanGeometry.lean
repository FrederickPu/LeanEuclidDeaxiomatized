import Mathlib.Data.Real.Basic

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
  -- for segment.length
  dist : Point → Point → ℝ

namespace PreEuclideanGeometry

variable {Point : Type u} {Line : Type v} {Circle : Type w}

inductive Angle (E : PreEuclideanGeometry)
| ofPoints (a b c : E.Point) : Angle E

inductive Triangle (E : PreEuclideanGeometry)
| ofPoints (a b c : E.Point) : Triangle E

inductive Segment (E : PreEuclideanGeometry)
| endpoints (a b : E.Point) : Segment E

variable {E : PreEuclideanGeometry}

#check E.Segment

namespace Segment

def length (s : E.Segment) : ℝ := match s with
| endpoints x y => E.dist x y

-- instance does not provide concrete values for (semi-)out-params
-- Coe ?E.Segment ℝ
instance : Coe (E.Segment) ℝ := ⟨length⟩

end Segment

open Lean PrettyPrinter

syntax "(" term "─" term ")": term

macro_rules
| `(($t:term ─ $s:term)) => `(Segment.endpoints $t $s)

@[app_unexpander Segment.endpoints]
def unexpand_endpoints : Unexpander
| `($_ $t $s) => `(($t ─ $s))
| _ => throw ()

/- Override the notation for absolute/magnitude used by Abs typeclass, i.e., | ⬝ |, -/
macro:max (priority := high) atomic("|" noWs) a:term noWs "|"  : term => `(Segment.length $a)

@[app_unexpander Segment.length]
def unexpand_length : Lean.PrettyPrinter.Unexpander
| `($_ $i:ident) => `(|$i:ident|)
| `($_ ($t:term ─ $s:term)) => `(|($t:term─$s:term)|)
| _ => throw ()


namespace Point

def sameSide := E.sameSide
def onLine := E.onLine
def onCircle := E.onCircle
def insideCircle := E.insideCircle
def isCentre := E.isCentre

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

def intersectsCircle := E.intersectsCircle₂

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

namespace PreEuclideanGeometry

class EuclideanGeometry extends PreEuclideanGeometry where
  -- intersections
  intersection_lines : ∀ (L M : Line), L.intersectsLine M →
    ∃ a : Point, (a.onLine L) ∧ (a.onLine M)
  intersections_circle_line : ∀ (α : Circle) (L : Line), L.intersectsCircle α →
    ∃ (a b : Point), (a.onCircle α) ∧ (a.onLine L) ∧ (b.onCircle α) ∧ (b.onLine L) ∧ a ≠ b
  intersection_circle_line_between_points : ∀ (α : Circle) (L : Line) (b c :Point),
    (b.insideCircle α) ∧ (b.onLine L) ∧ (c.outsideCircle α) ∧ (c.onLine L) →
    ∃ a : Point, (a.onCircle α) ∧ (a.onLine L) ∧ (between b a c)
  intersection_circle_line_extending_points : ∀ (α : Circle) (L : Line) (b c :Point),
    (b.insideCircle α) ∧ distinctPointsOnLine b c L →
    ∃ a : Point, (a.onCircle α) ∧ (a.onLine L) ∧ (between a b c)
  intersection_circles : ∀ (α β : Circle), α.intersectsCircle β →
    ∃ a : Point, (a.onCircle α) ∧ (a.onCircle β)
  intersection_same_side : ∀ (α β : Circle) (b c d : Point) (L : Line),
    (α.intersectsCircle β) ∧ (c.isCentre α) ∧ (d.isCentre β) ∧ (c.onLine L) ∧ (d.onLine L) ∧ ¬(b.onLine L) →
    ∃ a : Point, (a.onCircle α) ∧ (a.onCircle β) ∧ (a.sameSide b L)
  intersection_opposite_side : ∀ (α β : Circle) (b c d : Point) (L : Line),
    (α.intersectsCircle β) ∧ (c.isCentre α) ∧ (d.isCentre β) ∧ (c.onLine L) ∧ (d.onLine L) ∧ ¬(b.onLine L) →
    ∃ a : Point, (a.onCircle α) ∧ (a.onCircle β) ∧ a.opposingSides b L
  -- lines and circles
  line_from_points : ∀ (a b : Point), a ≠ b →
    ∃ L : Line, (a.onLine L) ∧ (b.onLine L)
  circle_from_points : ∀ (a b : Point), a ≠ b →
    ∃ α : Circle, (a.isCentre α) ∧ (b.onCircle α)
  -- points
  arbitrary_point :
    ∃ _ : Point, true
  distinct_points :
    ∀ p₁ : Point, ∃ p₂ : Point, p₁ ≠ p₂
  line_nonempty :
    ∀ l : Line, ∃ p : Point, p.onLine l
  exists_distincts_points_on_line :
    ∀ l : Line, ∀ p : Point, ∃ p' : Point, p ≠ p' ∧ p'.onLine l
  exists_point_between_points_on_line :
    ∀ (L : Line) (b c : Point), distinctPointsOnLine b c L
    → ∃ a : Point, (a.onLine L) ∧ (between b a c)
  exists_point_between_points_not_on_line :
    ∀ (L M : Line) (b c : Point), distinctPointsOnLine b c L ∧ L ≠ M
    → ∃ a : Point, (a.onLine L) ∧ (between b a c) ∧ ¬(a.onLine M)
  /--
  This rule is not in [Avigad et al., 2009] but is convenient for proving some propositions.
  -/
  point_between_points_shorter_than : ∀ (L : Line) (b c : Point) (s : toPreEuclideanGeometry.Segment),
    distinctPointsOnLine b c L ∧ (|s| > 0) →
    ∃ a : Point, (a.onLine L) ∧ (between b a c) ∧ |(b─a)| < |s|
  extend_point :
    ∀ (L : Line) (b c : Point), distinctPointsOnLine b c L
    → ∃ a : Point, (a.onLine L) ∧ (between b c a)
  extend_point_not_on_line :
    ∀ (L M : Line) (b c : Point), distinctPointsOnLine b c L ∧ L ≠ M
    → ∃ a : Point, (a.onLine L) ∧ (between b c a) ∧ ¬(a.onLine M)
  /--
  This rule is not in [Avigad et al., 2009] but is convenient for proving some propositions.
  -/
  extend_point_longer :
    ∀ (L : Line) (b c : Point) (s : toPreEuclideanGeometry.Segment), distinctPointsOnLine b c L
    → ∃ a : Point, (a.onLine L) ∧ (between b c a) ∧ |(c─a)| > |s|
  point_same_side :
    ∀ (L : Line) (b : Point), ¬(b.onLine L) → ∃ a : Point, a.sameSide b L
  distinct_point_same_side:
    ∀ (L : Line) (b c : Point), ¬(b.onLine L) → ∃ a : Point, a ≠ c ∧ a.sameSide b L
  /--
  A stronger version of the Points construction rule 6 in [Avigad et al., 2009], which is convenient for proving some propositions.
  -/
  point_on_line_same_side :
    ∀ (L M : Line) (b : Point), ¬(b.onLine L) ∧ (L.intersectsLine M)
    → ∃ a : Point, a.onLine M ∧ a.sameSide b L
  exists_point_opposite :
    ∀ (L : Line) (b : Point), ¬(b.onLine L) → ∃ a : Point, a.opposingSides b L
  exists_distinct_point_opposite_side :
    ∀ (L : Line) (b c : Point), ¬(b.onLine L) → ∃ a : Point, a ≠ c ∧ a.opposingSides b L
  exists_point_on_circle :
    ∀ (α : Circle), ∃ a : Point, a.onCircle α
  exists_distinct_point_on_circle :
    ∀ (α : Circle) (b : Point), ∃ a : Point, a ≠ b ∧ (a.onCircle α)
  exists_point_inside_circle :
    ∀ (α : Circle), ∃ a : Point, a.insideCircle α
  exists_distinct_point_inside_circle :
    ∀ (α : Circle) (b : Point), ∃ a : Point, a ≠ b ∧ a.insideCircle α
  exists_point_outside_circle :
    ∀ (α : Circle), ∃ a : Point, a.outsideCircle α
  exists_distinct_point_outside_circle :
    ∀ (α : Circle) (b : Point),  ∃ a : Point, a ≠ b ∧ a.outsideCircle α

end PreEuclideanGeometry
