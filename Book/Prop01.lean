import SystemE

open EuclideanGeometry

variable { E : EuclideanGeometry }

theorem proposition_1 : ∀ (a b : E.Point) (AB : E.Line),
  PreEuclideanGeometry.distinctPointsOnLine a b AB →
  ∃ c : E.Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| :=
by
  euclid_intros
  euclid_apply E.circle_from_points a b as BCD
  euclid_apply E.circle_from_points b a as ACE
  euclid_apply E.intersection_circles BCD ACE as c
  euclid_apply E.point_on_circle_onlyif a b c BCD
  euclid_apply E.point_on_circle_onlyif b a c ACE
  use c
  euclid_finish

theorem proposition_1' : ∀ (a b x : E.Point) (AB : E.Line),
  E.distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) →
  ∃ c : E.Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| ∧ (c.opposingSides x AB) :=
by
  euclid_intros
  euclid_apply E.circle_from_points a b as BCD
  euclid_apply E.circle_from_points b a as ACE
  euclid_apply E.intersection_opposite_side BCD ACE x a b AB as c
  euclid_apply E.point_on_circle_onlyif a b c BCD
  euclid_apply E.point_on_circle_onlyif b a c ACE
  use c
  euclid_finish
