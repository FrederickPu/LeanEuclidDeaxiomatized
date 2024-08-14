import SystemE
import Lean
open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Meta

def chain (base : Expr): (names : List Name) → (l : List Level) → Expr
| [], l => base
| a :: L, l => mkApp (Expr.const a l) (chain base L l)

def varAbbrev (n : Name) : TermElabM Expr := do
  let lctx ← getLCtx
  for wlocal in lctx do
    let (varName, varType) := (wlocal.fvarId, wlocal.type)
    match varType with
    | Expr.const `EuclideanGeometry l =>
      return mkApp (Expr.const n l) (chain  (.fvar varName) [`EuclideanConstructions.toPreEuclideanGeometry, `EuclideanDiagrammatic.toEuclideanConstructions, `EuclideanMetric.toEuclideanDiagrammatic, `EuclideanSuperposition.toEuclideanMetric, `EuclideanGeometry.toEuclideanSuperposition] l)
    | _ => pure ()
  throwError "No EuclideanGeometry (model) variable could be found"

elab "Point" : term => varAbbrev `PreEuclideanGeometry.Point
elab "Line" : term => varAbbrev `PreEuclideanGeometry.Line
elab "Circle" : term => varAbbrev `PreEuclideanGeometry.Circle
elab "Triangle" : term => varAbbrev `PreEuclideanGeometry.Triangle
elab "Angle" : term => varAbbrev `PreEuclideanGeometry.Angle
elab "Segment" : term => varAbbrev `PreEuclideanGeometry.Segment
elab "distinctPointsOnLine" : term => varAbbrev `PreEuclideanGeometry.distinctPointsOnLine




open EuclideanGeometry

variable { E : EuclideanGeometry }


theorem proposition_1 : ∀ (a b : Point) (AB : Line),
  PreEuclideanGeometry.distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| :=
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
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| ∧ (c.opposingSides x AB) :=
by
  euclid_intros
  euclid_apply E.circle_from_points a b as BCD
  euclid_apply E.circle_from_points b a as ACE
  euclid_apply E.intersection_opposite_side BCD ACE x a b AB as c
  euclid_apply E.point_on_circle_onlyif a b c BCD
  euclid_apply E.point_on_circle_onlyif b a c ACE
  use c
  euclid_finish

end
