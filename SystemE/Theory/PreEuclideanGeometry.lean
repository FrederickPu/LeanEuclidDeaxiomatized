import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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
  -- for Segment.length
  dist : Point → Point → ℝ
  -- for Angle.degree
  angleDegree : Point → Point → Point → ℝ
  -- for Triangle.area
  triangleArea : Point → Point → Point → ℝ

namespace PreEuclideanGeometry

variable {Point : Type u} {Line : Type v} {Circle : Type w}

inductive Angle (E : PreEuclideanGeometry)
| ofPoints (a b c : E.Point) : Angle E

namespace Angle

variable {E : PreEuclideanGeometry}

def degree (α : E.Angle) : ℝ := match α with
| ofPoints a b c => E.angleDegree a b c

noncomputable def Right := Real.pi / 2

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

def Triangle.area (t : Triangle E) : ℝ := match t with
| ofPoints a b c => E.triangleArea a b c

notation:max "△" a ":" b ":" c:66 => Triangle.ofPoints a b c

inductive Segment (E : PreEuclideanGeometry)
| endpoints (a b : E.Point) : Segment E

variable {E : PreEuclideanGeometry}

#check E.Segment

namespace Segment

def length (s : E.Segment) : ℝ := match s with
| endpoints x y => E.dist x y

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
