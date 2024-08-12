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

namespace Angle

variable {E : PreEuclideanGeometry}

opaque Right : ℝ
opaque degree : E.Angle → ℝ
instance : Coe E.Angle ℝ := ⟨degree⟩

end Angle

notation "∟" => Angle.Right
notation:71 "∠" a ":" b ":" c:72 => Angle.degree (Angle.ofPoints a b c)

open Lean PrettyPrinter

@[app_unexpander Angle.degree]
def unexpand_degree : Unexpander
| `($_ (`Angle.ofPoints $a:ident $b:ident $c:ident)) => `(∠ $a:ident : $b:ident : $c:ident)
| _ => throw ()


inductive Triangle (E : PreEuclideanGeometry)
| ofPoints (a b c : E.Point) : Triangle E

opaque Triangle.area : Triangle E → ℝ

notation:max "△" a ":" b ":" c:66 => Triangle.ofPoints a b c

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
-- Constructions
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

-- Inferences
  -- diagrammatic
  /--
  If points `a` and `b` are distinct, and both points are on lines `L` and `M`, then `L = M`
  -/
  two_points_determine_line :
    ∀ (a b : Point) (L M : Line), distinctPointsOnLine a b L ∧ (a.onLine M) ∧ (b.onLine M) → L = M
  /--
  If points `a` and `b` are both centers of `(α : Circle)` then `a = b`
  -/
  centre_unique :
    ∀ (a b : Point) (α : Circle), (a.isCentre α) ∧ (b.isCentre α) → a = b
  -- ********
  -- 3
  -- If a is the centre of α then a is inside α
  -- ********
  center_inside_circle : ∀ (a : Point) (α : Circle),
    a.isCentre α → a.insideCircle α
  -- ********
  -- 4
  -- If (a : Point) is inside (α : Circle), then a is not on α
  -- -- ********
  inside_not_on_circle : ∀ (a : Point) (α : Circle),
    a.insideCircle α → ¬(a.onCircle α)
  -- ********  between axioms ********

  -- ********
  -- 1
  -- If b is  between a and c then b is  between c and a, a != b, a != c, and a is
  -- not a. between bnd c
  -- ********
  between_symm : ∀ (a b c : Point), between a b c →
    (between c b a) ∧ (a ≠ b) ∧ (a ≠ c) ∧ ¬(between b a c)
  -- ********
  -- 2
  -- If b is  between a and c, a is on L, and b is on L, then c is on L
  -- ********
  between_same_line_out : ∀ (a b c : Point) (L : Line),
    (between a b c) ∧ (a.onLine L) ∧ (b.onLine L) →
    c.onLine L
  -- ********
  -- 3  If b is  between a and c, a is on L, and c is on L, then b is on L
  -- ********
  between_same_line_in : ∀ (a b c : Point) (L : Line),
    (between a b c) ∧ (a.onLine L) ∧ (c.onLine L) →
    b.onLine L
  -- -- ********
  -- 4
  -- If b is  between a and c and d is  between a and b then d is  between a and c
  -- -- ********
  between_trans_in : ∀ (a b c d : Point),
    (between a b c) ∧ (between a d b) → between a d c
  -- ********
  -- 5
  -- If b is  between a and c and c is a. between bnd d then b is  between a and d
  -- ********
  between_trans_out : ∀ (a b c d : Point),
    (between a b c) ∧ (between b c d) → (between a b d)
  -- ********
  -- 6
  -- If a, b, and c are distinct points on a line L, then then either b is  between
  -- a and c, or a is a. between bnd c, or c is  between a and b
  -- ********
  between_points : ∀ (a b c : Point) (L : Line),
    (a ≠ b) ∧ (b ≠ c) ∧ (c ≠ a) ∧ (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) →
    (between a b c) ∨ (between b a c) ∨ (between a c b)
  -- ********
  -- 7
  -- If b is  between a and c and b is  between a and d then b is not  between c
  -- and d
  -- ********
  between_not_trans : ∀ (a b c d : Point),
    (between a b c) ∧ (between a b d) → ¬(between c b d)
  -- ******** same side axioms ********

  -- ********
  -- 1
  -- If a is not on L, then a and a are on the same side of L
  -- ********
  same_side_rfl : ∀ (a : Point) (L : Line),
    ¬(a.onLine L) → a.sameSide a L
  -- ********
  -- 2
  -- If a and b are on the same side of L, then b and a are on the same side of L
  -- ********
  same_side_symm : ∀ (a b : Point) (L : Line),
    a.sameSide b L → b.sameSide a L
  -- ********
  -- 3
  -- If a and b are on the same side of L, then a is not on L
  -- ********
  same_side_not_on_line : ∀ (a b : Point) (L : Line),
    a.sameSide b L → ¬(a.onLine L)
  -- ********
  -- 4
  -- If a and b are on the same side of L, and a and c are on the same side of
  -- L, then b and c are on the same side of L
  -- -- ********
  same_side_trans : ∀ (a b c : Point) (L : Line),
    (a.sameSide b L) ∧ (a.sameSide c L) → b.sameSide c L
  -- ********
  -- 5
  -- If a, b, and c are not on L, and a and b are not on the same side of L,
  -- then either a and c are on the same side of L, or b and c are on the same
  -- side of L
  -- ********
  same_side_pigeon_hole : ∀ (a b c : Point) (L : Line),
    ¬(a.onLine L) ∧ ¬(b.onLine L) ∧ ¬(c.onLine L) →
    (a.sameSide b L) ∨ (a.sameSide c L) ∨ (b.sameSide c L)
  -- ********
  -- 1
  -- If b is  between a and c and a and c are on the same side of L, then a and
  -- b are on the s
  pasch_1: ∀ (a b c : Point) (L : Line),
    (between a b c) ∧ (a.sameSide c L) → a.sameSide b L
  -- ********
  -- 2
  -- If b is  between a and c and a is on L and b is not on L, then b and c are
  -- on the same side of L
  -- -- ********
  pasch_2: ∀ (a b c : Point) (L : Line),
    (between a b c) ∧ (a.onLine L) ∧ ¬(b.onLine L) →
    b.sameSide c L
  -- ********
  -- 3
  -- If b is  between a and c and b is on L then a and c are not on the same
  -- side of L
  -- ********
  -- -- See also Avigad's notes on this rule (https://www.andrew.cmu.edu/user/avigad/Papers/euclid_notes.htm)
  pasch_3: ∀ (a b c : Point) (L : Line),
    (between a b c) ∧ (b.onLine L) → ¬(a.sameSide c L)
  -- ********
  -- 4
  -- If b is the intersection of distinct lines L and M, a and c are distinct points
  -- on M, a != b, c != b, and a and c are not on the same side of L, then b is
  --  between a and c
  -- ********
  pasch_4: ∀ (a b c : Point) (L M : Line),
    (L ≠ M) ∧ (b.onLine L) ∧ (b.onLine M) ∧ distinctPointsOnLine a c M ∧
    (a ≠ b) ∧ (c ≠ b) ∧ ¬(a.sameSide c L) →
    between a b c
  -- ******** triple incidence axioms ********

  -- ********
  -- 1
  -- If L, M, and N are lines meeting at a point a, and b, c, and d are points
  -- on L, M, and N respectively, and if c and d are on the same side of L,
  -- and b and c are on the same side of N, then b and d are not on the same
  -- side of M
  -- ********
  triple_incidence_1 : ∀ (L M N : Line) (a b c d : Point),
    (a.onLine L) ∧ (a.onLine M) ∧ (a.onLine N) ∧ (b.onLine L) ∧
    (c.onLine M) ∧ (d.onLine N) ∧ (c.sameSide d L) ∧ (b.sameSide c N) →
    ¬(b.sameSide d M)
  -- ********
  -- 2
  -- If L, M, and N are lines meeting at a point a, and b, c, and d are points
  -- on L, M, and N respectively, and if c and d are on the same side of L,
  -- and b and d are not on the same side of M, and d is not on M and b != a,
  -- then b and c are on the same side of N
  -- ********
  triple_incidence_2 : ∀ (L M N : Line) (a b c d : Point),
    (a.onLine L) ∧ (a.onLine M) ∧ (a.onLine N) ∧ (b.onLine L) ∧
    (c.onLine M) ∧ (d.onLine N) ∧ (c.sameSide d L) ∧ ¬(b.sameSide d M) ∧ ¬(d.onLine M) ∧ (b ≠ a) →
    b.sameSide c N
  -- ********
  -- 3
  -- If L, M, and N are lines meeting at a point a, and b, c, and d are points
  -- on L, M, and N respectively, and if c and d are on the same side of L,
  -- and b and c are on the same side of N, and d and e are on the same side
  -- of M, and c and e are on the same side of N, then c and e are on the same
  -- side of L
  -- ********
  triple_incidence_3 : ∀ (L M N : Line) (a b c d e : Point),
    (a.onLine L) ∧ (a.onLine M) ∧ (a.onLine N) ∧ (b.onLine L) ∧
    (c.onLine M) ∧ (d.onLine N) ∧ (c.sameSide d L) ∧ (b.sameSide c N) ∧
    (d.sameSide e M) ∧ (c.sameSide e N) →
    c.sameSide e L
  -- ******** circle axioms ********

  -- ********
  -- 1
  -- If a, b, and c are on L, a is inside α, b and c are on α, and b != c, then a
  -- -- is a. between bnd c
  -- -- ********
  circle_line_intersections : ∀ (a b c : Point) (L : Line) (α : Circle),
    (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) ∧
    (a.insideCircle α) ∧ (b.onCircle α) ∧ (c.onCircle α) ∧ (b ≠ c) →
    between b a c
  -- ********
  -- 2
  -- If a and b are each inside α or on α, and c is  between a and b, then c is
  -- inside α
  -- ********
  circle_points_between : ∀ (a b c : Point) (α : Circle),
    ¬(a.outsideCircle α) ∧ ¬(b.outsideCircle α) ∧ (between a c b) →
    c.insideCircle α
  -- ********
  -- 3
  -- If a is inside α or on α, c is not inside α, and c is  between a and b, then b
  -- is neither inside α nor on α
  -- ********
  circle_points_extend : ∀ (a b c : Point) (α : Circle),
    ¬(a.outsideCircle α) ∧ ¬(c.insideCircle α) ∧ (between a c b) →
    (b.outsideCircle α)
  -- ********
  -- 4  Let α and β be distinct circles that intersect in distinct points c and d
  -- Let a be a the centre of α, let b be the centre of β, and let L be the line
  -- through a and b  Then c and d are not on the same side of L
  -- ********
  circles_intersections_diff_side : ∀ (a b c d : Point) (α β : Circle) (L : Line),
    (α ≠ β) ∧ (c.onCircle α) ∧ (c.onCircle β) ∧ (d.onCircle α) ∧
    (d.onCircle β) ∧ (c ≠ d) ∧ (a.isCentre α) ∧ (b.isCentre β) ∧
    (a.onLine L) ∧ (b.onLine L) → ¬(c.sameSide d L)
  -- ******** intersection rules ********

  -- ********
  -- 1
  -- If a and b are on different sides of L, and M is the line through a and b,
  -- then L and M intersect
  -- ********
  intersection_lines_opposing: ∀ (a b : Point) (L M : Line),
    (a.opposingSides b L) ∧ (a.onLine M) ∧ (b.onLine M) →
    L.intersectsLine M
  -- /--
  -- Not in [Avigad et al., 2009]
  -- -/
  intersection_lines_common_point : ∀ (a : Point) (L M : Line),
    a.onLine L ∧ a.onLine M ∧ L ≠ M →
    L.intersectsLine M
  -- /--
  -- Not in [Avigad et al., 2009]
  -- -/
  parallel_line_unique : ∀ (a : Point) (L M N : Line),
    ¬(a.onLine L) ∧ a.onLine M ∧ a.onLine N ∧ ¬(L.intersectsLine M) ∧ ¬(L.intersectsLine N) →
    M = N
  -- /--
  -- Not in [Avigad et al., 2009]
  -- -/
  intersection_symm :
    ∀ (L M : Line), L.intersectsLine M → L.intersectsLine L
  -- ********
  -- 2
  -- If a is on or inside α, b is on or inside α, and a and b are on different sides
  -- of L, then L and α intersect
  -- ********
  intersection_circle_line_1: ∀ (a b : Point) (α : Circle) (L: Line),
    ¬(a.outsideCircle α) ∧ ¬(b.outsideCircle α) ∧ (a.opposingSides b L) →
    L.intersectsCircle α
  -- ********
  -- 3  If a is inside α and on L, then L and α intersect
  -- ********
  intersection_circle_line_2: ∀ (a : Point) (α : Circle) (L: Line),
    (a.insideCircle α) ∧ (a.onLine L) → L.intersectsCircle α
  -- ********
  -- 4  If a is on or inside α, b is on or inside α, a is inside β, and b is outside β,
  -- then α and β intersect
  -- ********
  intersection_circle_circle_1: ∀ (a b : Point) (α β : Circle),
    ¬(a.outsideCircle α) ∧ ¬(b.outsideCircle α) ∧ (a.insideCircle β) ∧ (b.outsideCircle β) →
    α.intersectsCircle β
  -- ********
  -- 5  If a is on α, b is in α, a is in β, and b is on β, then α and β intersect
  -- ********
  intersection_circle_circle_2: ∀ (a b : Point) (α β : Circle),
    (a.onCircle α) → (b.insideCircle α) → (a.insideCircle β) → (b.onCircle β) →
    α.intersectsCircle β
  -- ******** parallelogram rules ********
  -- /--
  -- Not in [Avigad et al., 2009]
  -- -/
  parallelogram_same_side : ∀ (a b c d : Point) (AB CD AC BD : Line),
    formParallelogram a b c d AB CD AC BD →
    b.sameSide d AC ∧ c.sameSide d AB ∧ a.sameSide b CD
  -- metric
  --
  -- Metric inferences defined in Sec. 3.5 of Avigad et al., 2009
  -- Generally speaking, they are not used explicitly in the tactics written by humans.
  -- *
  --   + is associative and commutative, with identity 0.

  --   < is a linear ordering with least element 0

  --   For any x, y, and z, if x < y then x + z < y + z

  --
  -- 1.
  -- ab = 0 if and only if a = b.
  --
  zero_segment_if :
    ∀ (a b : Point),  |(a ─ b)| = 0 → a = b
  zero_segment_onlyif : ∀ (a b : Point),
    a = b → |(a─b)| = 0
  -- --
  -- 2.
  -- ab ≥ 0
  --
  -- @[simp]
  segment_gte_zero : ∀ (s : toPreEuclideanGeometry.Segment),
    0 ≤ s.length

  --
  -- 3.
  -- ab = ba.
  --
  -- @[simp]
  segment_symmetric : ∀ (a b : Point),
    |(a─b)| = |(b─a)|
  --
  angle_symm : ∀ (a b c : Point),
    (a ≠ b) ∧ (b ≠ c) → ((∠ a:b:c) = (∠ c:b:a))
  --
  -- 5.
  -- 0 ≤ \abc and \abc ≤ right-angle + right-angle.
  -- --
  -- @[simp]
  angle_range : ∀ (ang : toPreEuclideanGeometry.Angle),
    (0 : ℝ) ≤ ang ∧ ang ≤ ∟ + ∟
  --
  -- 6.
  -- △aab = 0. △
  --
  -- @[simp]
  degenerated_area : ∀ (a b : Point), Triangle.area △ a:a:b = 0
  --
  -- 7.
  -- △abc ≥ 0.
  -- --
  -- @[simp]
  area_gte_zero : ∀ (ar : toPreEuclideanGeometry.Triangle), 0 ≤ Triangle.area ar
  --
  -- 8.
  -- △abc = △cab and △abc = △acb.
  --
  -- @[simp]
  area_symm_1 : ∀ (a b c : Point),
      Triangle.area (△a:b:c) = Triangle.area (△c:a:b)
  -- @[simp]
  area_symm_2 : ∀ (a b c : Point),
      Triangle.area (△ a:b:c) = Triangle.area (△a:c:b)
  --
  -- 9.
  -- If ab = a′b′, bc = b′c′, ca = c′a′, \abc = \a′b′c′, \bca = \b′c′a′, and
  -- \cab = \c′a′b′, then △abc = △a′b′c′.
  --
  area_congruence : ∀ (a b c a' b' c' : Point),
      |(a─b)| = |(a'─b')| ∧
      |(b─c)| = |(b'─c')| ∧
      |(c─a)| = |(c'─a')| ∧
      ∠ a:b:c = ∠ a':b':c' ∧
      ∠ b:c:a = ∠ b':c':a' ∧
      ∠ c:a:b = ∠ c':a':b'
      → Triangle.area (△ a:b:c) = Triangle.area (△ a':b':c')

  -- superposition
  /--
  A combination of the two superposition rules in [Avigad et al., 2009]
  -/
  superposition : ∀ (a b c d g h : Point) (AB BC AC L : Line),
    formTriangle a b c AB BC AC ∧ distinctPointsOnLine d g L ∧ ¬(h.onLine L) →
    ∃ (b' c' : Point) (BC' AC' : Line), (∠ b:a:c : ℝ) = (∠ b':d:c') ∧ (∠ a:c:b : ℝ) = (∠ d:c':b') ∧ (∠ c:b:a : ℝ) = (∠ c':b':d) ∧
    |(a─b)| = |(d─b')| ∧ |(b─c)| = |(b'─c')| ∧ |(c─a)| = |(c'─d)| ∧ b'.onLine L ∧ ¬(between b' d g) ∧ c'.sameSide h L ∧ distinctPointsOnLine b' c' BC' ∧ distinctPointsOnLine d c' AC'
  -- transfer
  --
  -- Transfer inferences defined in Sec. 3.6 of Avigad et al. 2009
  --
  --    diagram-segment transfer axioms

  --
  -- 1.
  -- If b is  between a and c, then ab + bc = ac.
  -- [between_if, equal_circles, point_on_circle_if, point_on_circle_onlyif, sum_angles_if, sum_angles_onlyif, perpendicudlar_if, sum_areas_if]

  -- Given any points a, b and c such that b is between a and c, then the straight-line from a to c is equal to the sum of the straight-lines from a to b and from b to c.
  between_if : ∀ (a b c : Point),
    between a b c → |(a─b)| + |(b─c)| = |(a─c)|

  --
  -- 2.
  -- If a is the centre of α and β, b is on α, c is on β, and ab = ac, then α = β.


  -- If a point x is the centre of two circles C and D, and given points b and d such that b is on C and c is on D and the straight-line from x to b is equal to the straight-line from x to c, then C is equal to D.
  equal_circles : ∀ (a b c : Point) (α β : Circle),
    (a.isCentre α) ∧ (a.isCentre β) ∧ (b.onCircle α) ∧ (c.onCircle β) ∧ |(a─b)| = |(a─c)| → α = β

  --
  -- 3.
  -- If a is the centre of α and b is on α, then ac = ab if and only if c is on α.


  -- If a point x is the centre of circle C and a point b is on C, then given some point c such that the straight-line from x to c is equal to the straight-line from x to b, then c is on C.
  point_on_circle_if : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─c)| = |(a─b)| → c.onCircle α

  -- TODO: make below flag work
  -- @[aesop unsafe 80% [forward, apply]]
  -- If a point x is the centre of circle C and a point b is on C, then given some point c on C, the straight-line from x to c is equal to the straight-line from x to b
  point_on_circle_onlyif : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ (c.onCircle α) → |(a─c)| = |(a─b)|

  --
  -- 4.
  -- If a is the centre of α and b is on α, and ac < ab if and only if c is in α.
  --
  -- -- Given any points b and c, and circle C, such that b is on C and the straight-line from the centre of C to c is less than the straight-line from the centre of C to b, then c is inside the circle C.
  point_in_circle_if : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─c)| < |(a─b)| → c.insideCircle α

  --
  -- -- Given any points b and c, and circle C, such that b is on C and c is inside the circle C, then the straight-line from the centre of C to c is less than the straight-line from the centre of C to b.
  point_in_circle_onlyif : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ (c.insideCircle α) → |(a─c)| < |(a─b)|

  --    diagram-angle transfer axioms

  --
  -- 1.
  -- Suppose a != b, a != c, a is on L, and b is on L. Then c is on L and a is
  -- not  between b and c if and only if \bac = 0.
  --
  -- Given points a, b and c such that a is not equal to b and a is not equal to c, and line L such that a, b, and c are all on L, and a is not between b and c, then the angle bac has degree zero.
  degenerated_angle_if : ∀ (a b c : Point) (L : Line),
    (a ≠ b) ∧ (a ≠ c) ∧ (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) ∧ ¬(between b a c) → ∠ b:a:c = 0

  -- Given points a, b and c such that a is not equal to b and a is not equal to c, and line L such that a and b are on L, and the angle formed by b:a:c has degree zero,  then c is on L and a is not between b and c.
  degenerated_angle_onlyif : ∀ (a b c : Point) (L : Line),
    (a ≠ b) ∧ (a ≠ c) ∧ (a.onLine L) ∧ (b.onLine L) ∧ (∠ b:a:c = 0)  → (c.onLine L) ∧ ¬(between b a c)
  --
  -- -- Given points a, b and c such that a is not equal to b and a is not equal to c, and line L such that a and b are on L, and the angle formed by b:a:c has degree zero,  then c is on L and a is not between b and c.
  -- axiom degenerated_angle_onlyif : ∀ (a b c : Point) (L : Line),
  --   (a ≠ b) ∧ (a ≠ c) ∧ (a.onLine L) ∧ (b.onLine L) ∧ (∠ b: a: c) = (0 : ℝ) → (c.onLine L) ∧ ¬(between b a c)

  -- --
  -- 2.
  -- Suppose a is on L and M, b is on L, c is on M, a != b, a != c, d is not on
  -- L or M, and L != M. Then \bac = \bad + \dac if and only if b and d
  -- are on the same side of M and c and d are on the same side of L.
  --

  -- Given point on a given lines L and M, point b  on L, and point c on M with a distinct from b, a distinct from c, point d  not on L or M, and L distinct from M, then the angle bac is equal to the sum of angles bad and dac only if b and d are on the same side of M and c and d are on the same side of L.
  -- Kaiyu: Jeremy's typo here.
  sum_angles_if : ∀ (a b c d : Point) (L M : Line),
    (a.onLine L) ∧ (a.onLine M) ∧ (b.onLine L) ∧ (c.onLine M) ∧ (a ≠ b) ∧ (a ≠ c) ∧
    ¬(d.onLine L) ∧ ¬(d.onLine M) ∧ (L ≠ M) ∧ (∠ b:a:c) = (∠ b:a:d) + (∠ d:a:c) →
    (b.sameSide d M) ∧ (c.sameSide d L)


  -- Given point on a given lines L and M, point b  on L, and point c on M with a distinct from b, a distinct from c, point d  not on L or M, and L distinct from M, then b and d are on the same side of M and c and d are on the same side of L only if the angle bac is equal to the sum of angles bad and dac
  sum_angles_onlyif : ∀ (a b c d : Point) (L M : Line),
  (a.onLine L) ∧ (a.onLine M) ∧ (b.onLine L) ∧ (c.onLine M) ∧ (a ≠ b) ∧ (a ≠ c) ∧
  ¬(d.onLine L) ∧ ¬(d.onLine M) ∧ (L ≠ M) ∧ (b.sameSide d M) ∧ (c.sameSide d L) →
  (∠ b:a:c) = (∠ b:a:d) + (∠ d:a:c)

  --
  -- 3.
  -- Suppose a and b are points on L, c is  between a and b, and d is not on L.
  -- Then \acd = \dcb if and only if \acd is equal to right-angle.
  --

  -- Given points a and b both lying on a given line L, and point c lying between a and b, and point d not on L such that the angle acd is equal to the angle dcb, then the angle acd is a right angle.
  perpendicular_if : ∀ (a b c d : Point) (L : Line),
    (a.onLine L) ∧ (b.onLine L) ∧ (between a c b) ∧ ¬(d.onLine L) ∧ (∠ a:c:d = ∠ d:c:b) →
    ∠ a:c:d = ∟

  -- Given points a and b both lying on a given line L, and point c lying between a and b, and point d not on L such that the angle acd is a right angle, then the angle acd is equal to the angle dcb.
  perpendicular_onlyif : ∀ (a b c d : Point) (L : Line),
    (a.onLine L) ∧ (b.onLine L) ∧ (between a c b) ∧ ¬(d.onLine L) ∧ (∠ a:c:d = ∟) →
    ∠ a:c:d = ∠ d:c:b

  -- Given points a b and c with a distinct from b and b distinct from c, such that angle abc is the sum of two right angles, then b is between a and c
  -- /--
  -- Not in [Avigad et al., 2009]
  -- -/
  --
  flat_angle_if : ∀ (a b c : Point),
    a ≠ b ∧ b ≠ c ∧ ∠ a:b:c = ∟ + ∟ → between a b c

  -- Given points a b and c with b between a and c, then the angle abc is the sum of two right angles

  /--
  Not in [Avigad et al., 2009]
  -/
  --
  flat_angle_onlyif : ∀ (a b c : Point),
    between a b c → ∠ a:b:c = ∟ + ∟


  --
  -- 4.
  -- Suppose a, b, and b′ are on L, a, c, and c′ are on M, b != a, b′ != a, c != a,
  -- c′ != a, a is not  between b and b′, and a is not between c and c′. Then
  -- \bac = \b′ac′.
  --

  --
  -- -- Given points a, b, and b′ all on a given line L, and points c, c' such that a, c, and c′ are all on given line M, with b distinct from a, b′ distinct from a, c distinct from a, c' distinct from a, a is not  between b and b′, and a is not between c and c′, then angle bac is equal to angle b′ac′.
  equal_angles : ∀ (a b b' c c' : Point) (L M : Line),
    (a.onLine L) ∧ (b.onLine L) ∧ (b'.onLine L) ∧ (a.onLine M) ∧ (c.onLine M) ∧ (c'.onLine M) ∧
    (b ≠ a) ∧ (b' ≠ a) ∧ (c ≠ a) ∧ (c' ≠ a) ∧ ¬(between b a b') ∧ ¬(between c a c') →
    (∠ b:a:c = ∠ b':a:c')

  -- 5.
  -- Suppose a and b are on L, b and c are on M, and c and d are on N. Suppose
  -- also that b != c, a and d are on the same side of M, and \abc + \bcd <
  -- right-angle + right-angle. Then L and N intersect, and if e is on L and
  -- N, then e and a are on the same side of M.
  --
  --
  -- -- Given lines a,b,c and d such that a and b are both on a given line L, b and c are both on a given line M, c and d are both on a given line N, b is distinct from c, a and d are on the same side of M, and the sum of angles abc and bcd is less than the sum of two right angles, then there is a point e such that e is on L and N and e is on the same side of M as a.
  lines_intersect : ∀ (a b c d : Point) (L M N : Line),
    (a.onLine L) ∧ (b.onLine L) ∧ (b.onLine M) ∧ (c.onLine M) ∧ (c.onLine N) ∧ (d.onLine N) ∧
    (b ≠ c) ∧ (a.sameSide d M) ∧ (∠ a:b:c) + (∠ b:c:d) < ∟ + ∟ →
    ∃ e : Point, (e.onLine L) ∧ (e.onLine N) ∧ (e.sameSide a M)

  --    diagram-area transfer axioms

  --
  -- If a and b are on L and a != b, then △abc = 0 if and only if c is on L.
  --
  -- If a and b are two distinct points both lying on a given line L, with a given a point c such that the area of the triangle abc is zero, then c must also be on L.
  degenerated_area_if : ∀ (a b c : Point) (L : Line),
    distinctPointsOnLine a b L ∧ (Triangle.area △ a:b:c) = 0 →
    c.onLine L

  -- If a and b are two distinct points both lying on a given line L, with a given a point c also lying on L, then the area of the triangle abc is zero
  degenerated_area_onlyif : ∀ (a b c : Point) (L : Line),
    distinctPointsOnLine a b L ∧ (c.onLine L) →
    (Triangle.area △ a:b:c) = 0


  -- If a, b, c are all on a given line point L and distinct from one another, and d is not on L, and  c is  between a and b, then the sum of the areas of triangles acd and dcb is equal to the area of triangle adb
  sum_areas_if : ∀ (a b c d : Point) (L : Line),
    (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ ¬(d.onLine L) ∧ (between a c b) →
    (Triangle.area △ a:c:d + Triangle.area △ d:c:b = Triangle.area △ a:d:b)

  -- If a, b, c are all on a given line point L and distinct from one another, and d is not on L, and the sum of the areas of triangles acd and dcb is equal to the area of triangle adb, then c is between a and b.
  sum_areas_onlyif : ∀ (a b c d : Point) (L : Line),
    (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ ¬(d.onLine L) ∧
    (Triangle.area △ a:c:d + Triangle.area △ d:c:b = Triangle.area △ a:d:b) →
    between a c b

  --    parallelogram rules

  /--
  Not in [Avigad et al., 2009]
  -/
  -- Given a parallelogram formed from points a, b, c and d, the sum of the areas of the triangles acd and adb is equal to the sum of the areas of triangles bac and bcd
  parallelogram_area : ∀ (a b c d : Point) (AB CD AC BD : Line), formParallelogram a b c d AB CD AC BD →
    Triangle.area △ a:c:d + Triangle.area △ a:d:b = Triangle.area △ b:a:c + Triangle.area △ b:c:d

  -- /--
  -- Not in [Avigad et al., 2009]
  -- -/
  --
  -- Given a parallelogram formed from points a, b, c and d, and given points e and f such that e is betwen a and b and f is between c and d, then the sum of the areas of the triangles acf, afe, efd, and edb is equal to the sum of the areas of triangles acd and adb
  sum_parallelograms_area : ∀ (a b c d e f : Point) (AB CD AC BD : Line),
    formParallelogram a b c d AB CD AC BD ∧ between a e b ∧ between c f d →
    Triangle.area △ a:c:f + Triangle.area △ a:f:e + (Triangle.area △ e:f:d) + (Triangle.area △ e:d:b) = (Triangle.area △ a:c:d) + (Triangle.area △ a:d:b)


  /--
  Not in [Avigad et al., 2009] but required by Proposition 47
  -/
  rectangle_area : ∀ (a b c d : Point) (AB CD AC BD : Line),
    formParallelogram a b c d AB CD AC BD ∧ (∠ a:c:d = ∟) →
    (Triangle.area △ a:c:d + Triangle.area △ a:b:d = |(a─b)| * |(a─c)|) ∧ (Triangle.area △ b:a:c + Triangle.area △ b:d:c) = |(a─b)| * |(a─c)|

end PreEuclideanGeometry
