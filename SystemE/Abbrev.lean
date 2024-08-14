import SystemE.Theory.EuclideanGeometry
import Lean
open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Meta

def chain (base : Expr): (names : List Name) → (l : List Level) → Expr
| [], _ => base
| a :: L, l => mkApp (Expr.const a l) (chain base L l)

-- TODO:: add check to make sure there are not multiple instances of EuclideanGeometry in local context
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

-- note: only need to make abbreviations for primitives and sorts derived from primitives since all other things can be infered via namespace once the types of the underlying objects are defined
