import SystemE.Theory.PreEuclideanGeometry

open PreEuclideanGeometry

class EuclideanConstructions extends PreEuclideanGeometry where
-- Intersections
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

-- Lines and Circles
  line_from_points : ∀ (a b : Point), a ≠ b →
    ∃ L : Line, (a.onLine L) ∧ (b.onLine L)
  circle_from_points : ∀ (a b : Point), a ≠ b →
    ∃ α : Circle, (a.isCentre α) ∧ (b.onCircle α)

-- Points
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
