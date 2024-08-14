import SystemE
import Lean
open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Meta

-- Define a custom elaborator for the `Point` symbol
elab "Point" : term => do
  -- Get the local context
  let lctx ← getLCtx
  -- Iterate through local variables to find one of type `EuclideanGeometry`

  for wlocal in lctx do
    let (varName, varType) := (wlocal.fvarId, wlocal.type)
    -- Check if the variable is of type `EuclideanGeometry`
    let type ← inferType varType
    dbg_trace type
    match varType with
    | Expr.sort _ => dbg_trace "womp"
    | Expr.const `EuclideanGeometry l =>
      return (mkApp (Expr.const `PreEuclideanGeometry.Point l) (mkFVar varName))
    | _ => pure ()
  throwError "No EuclideanGeometry (model) variable could be found"

section

open EuclideanGeometry

variable { E : EuclideanGeometry } {α : Type} {G : Group α}


theorem proposition_1 : ∀ (a b : Point) (AB : E.Line),
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

end
