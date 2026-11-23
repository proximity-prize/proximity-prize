import ProximityPrize.SubmissionLower.Final50Price

set_option Elab.async false
set_option autoImplicit false

namespace Final50SharedPrice

open K1_13 (Shape chart ceilDiv mixed32 shape OnFactor extend)
open Final50Price (Messages SmallFactor ActiveFits ProperCut taylorLength primaryBox
  physicalPrice physicalDegree errors incidenceGap tiltedFits tiltedSurface)
open scoped Polynomial

abbrev slope : Shape := ⟨60,25,7⟩

inductive Surface where
  | ordinary
  | tilted
  deriving DecidableEq

def surfaceScale : Surface → ℕ
  | .ordinary => 32
  | .tilted => 1920

def surface (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixed32 p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltedSurface f.chamber q

def weights (kind : Surface) (f : Shape) : Shape :=
  let b := surface kind f ⟨1,0,0⟩
  let j := surface kind f ⟨1,1,0⟩ - b
  let t := surface kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩

def coord (p : Shape) (i : Fin 3) : ℕ := (![p.b,p.j,p.t] : Fin 3 → ℕ) i

/-- A bound for one of the two linear expressions in the chamber width. -/
def expression (w q : Shape) (useIndex topIndex : Bool) : ℕ :=
  3*w.b*(if useIndex then q.j else q.b) + 3*w.j*q.j +
    w.t*(if topIndex then q.j else 3*q.t)

def deficit (r a : ℕ) (f : Shape) : Shape :=
  ⟨r*slope.b-a*f.b,r*slope.j-a*f.j,r*slope.t-a*f.t⟩

structure Rate where
  kind : Surface
  pivot : Fin 3
  split : ℕ
  topIndex : Bool
  amount : ℕ

/-- The endpoint arithmetic for the common surface cut.
    Both expressions in the width are tested. One top bound suffices on the whole interval. -/
def RateFits (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weights u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))

instance (f : Shape) (u : Rate) : Decidable (RateFits f u) := by
  unfold RateFits
  infer_instance









def additiveBase (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixed32 p q z h + 2*x.t*mixed32 p p p h
  let pt := mixed32 p q z p + 2*x.t*mixed32 p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)

def nonsharedFee (x : Shape) (l : ℕ) : ℕ :=
  ceilDiv (2*x.b*primaryBox.b^2*(chart (taylorLength+2) x.chamber).b) l

def price (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPrice x l K + u.split*additiveBase x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l


end Final50SharedPrice
