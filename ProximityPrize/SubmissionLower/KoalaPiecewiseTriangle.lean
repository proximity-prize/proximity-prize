import ProximityPrize.SubmissionLower.KoalaAffineTriangle
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option Elab.async false

namespace KoalaPiecewiseTriangle
open Finset
open scoped BigOperators

structure Line where
  a : ℤ
  d : ℤ

def Line.at (f : Line) (x : ℤ) : ℤ := f.a + f.d*x

def Line.sub (f g : Line) : Line := ⟨f.a-g.a,f.d-g.d⟩

inductive Expr
  | affine (f : Line)
  | lower (f g : Expr)
  | upper (f g : Expr)
  | sub (f g : Expr)

def Expr.at : Expr → ℤ → ℤ
  | .affine f, x => f.at x
  | .lower f g, x => min (f.at x) (g.at x)
  | .upper f g, x => max (f.at x) (g.at x)
  | .sub f g, x => f.at x - g.at x

def Expr.const (a : ℤ) : Expr := .affine ⟨a,0⟩

private def ordered (f g : Line) (lo hi : ℤ) : Prop :=
  f.at lo ≤ g.at lo ∧ f.at hi ≤ g.at hi

private instance (f g : Line) (lo hi : ℤ) : Decidable (ordered f g lo hi) := by
  unfold ordered
  infer_instance









structure BandCuts where
  l0 : ℤ
  q1 : ℤ
  first : ℤ
  last : ℤ



private def lineCutSum (b : BandCuts) (l q : Line) (k lo : ℤ) (n : ℕ) : ℤ :=
  let sum := KoalaAffineTriangle.sumFast
  sum (l.a-k-q.a) (l.d-q.d) lo n -
    sum (b.l0-k-q.a) (-q.d) lo n -
    (sum (l.a-k-b.q1) l.d lo n -
      (n : ℤ) * KoalaAffineTriangle.twiceTriangle (b.l0-k-b.q1))


private def lineBandSum (b : BandCuts) (l q : Line) (lo : ℤ) (n : ℕ) : ℤ :=
  lineCutSum b l q b.first lo n - lineCutSum b l q b.last lo n









end KoalaPiecewiseTriangle
