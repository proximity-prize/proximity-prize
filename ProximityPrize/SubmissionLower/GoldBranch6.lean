import ProximityPrize.SubmissionLower.FrontBranch12
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6
noncomputable section
open Polynomial
open P3 (I K agreement)
open K1_13 (Geom extend Row Shape shape InBox Fits Contact remaining chart liftedChart
  mixed32 ceilDiv atJet OrderAt indexDegree)
open scoped BigOperators
abbrev physicalDegree := P3.physicalDegree
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev incidenceGap : ℕ := agreement - physicalDegree
abbrev primaryBox : Shape := P0_9.primaryBox
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
abbrev factorCap : ℕ := 0x32cdf437872295e
abbrev commonBox : Shape := ⟨6245, 2022, 0⟩
abbrev resultantBox : Shape := ⟨0x38c7faf0, 0x13315480, 0⟩
abbrev fatOrder : ℕ := 69360
abbrev divisorOrder : ℕ := 56875
abbrev isolatedOrder : ℕ := 1734
structure FatEquations where
  common : Row 3
  residual : Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ commonBox.b
  common_index : indexDegree common ≤ commonBox.j
  residual_total : residual.totalDegree ≤ resultantBox.b
  residual_index : indexDegree residual ≤ resultantBox.j
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPrice (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((P3.t + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (P3.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (P3.t * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (P3.t * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated
end
end P3_6
end
section
namespace P3_6
noncomputable section
open P3 (K)
open K1_13 (extend Row Shape shape Fits atJet OnFactor FatEligible)
open scoped BigOperators
end
end P3_6
end
