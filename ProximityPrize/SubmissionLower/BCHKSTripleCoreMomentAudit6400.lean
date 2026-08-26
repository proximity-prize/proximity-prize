import ProximityPrize.SubmissionLower.BCHKSFullCoreGoodOwnerCover6400
import ProximityPrize.SubmissionLower.BCHKSHybridCoreSwitchAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSTripleCoreMomentAudit6400

open BCHKSHybridHighDegreeAudit6400
open BCHKSHybridCoreSwitchAudit6400

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-!
Arithmetic and combinatorial-interface audit for the cubic-moment extension
of the common-core route.

Choose exactly `r` off-core agreement coordinates for each of `L` owners
inside an ambient set of size `N`, and let `q_x` be the number of chosen
rows containing coordinate `x`.  The power-mean lower bound is

`(L*r)^3 <= N^2 * sum_x q_x^3`.

If three distinct owners are not on one affine polynomial line, the
Vandermonde bridge bounds their common intersection by `s`.  A line has at
most `e` owners, and the line through two distinct owner points is unique.
Counting ordered triples gives the exact upper bound

`sum_x q_x^3 <=
   s*L^3 + (r-s)*(e+1)*L^2 - e*(r-s)*L`.

The `e+1` is real: the three repeated-index patterns contribute the
diagonal correction.  Dropping the final negative term gives the convenient
safe consequence

`L * (r^3-s*N^2) <= N^2*(r-s)*(e+1)`.

The finite-set power-mean and ordered-triple count are deliberately exposed
as hypotheses below.  This file audits their exact algebraic consequence and
the benchmark endpoint; it does not pretend that the final owner/profile
assembly has already been wired.
-/

def bchksTripleCoreMaxCodim6400 : ℕ := 16107
def bchksTripleCoreAmbient6400 : ℕ := 147180
def bchksTripleCoreIncidences6400 : ℕ := 70400
/-! Negating the target alignment conclusion `76780 + 1 < T.card`
supplies the inclusive line-fibre cap `76781`. -/
def bchksTripleCoreLineCap6400 : ℕ := 76781
def bchksTripleCoreMomentGap6400 : ℕ := 4596693200
def bchksTripleCoreSafeOwnerCap6400 : ℕ := 19645149527
def bchksTripleCoreExactQuadraticOwnerCap6400 : ℕ := 19645149526

def bchksTripleCoreSwitchExcess6400 : ℕ := 3246322589905
def bchksTripleCoreSwitchTotal6400 : ℕ := 274975831541727185
def bchksTripleCoreMaxUncoveredZMass129_6400 : ℕ := 3011018

/-- The cubic power-mean lower bound needed by the incidence argument is
already available over natural-number coordinate degrees. -/
theorem cubic_powerMean_nat
    {I : Type*} (U : Finset I) (q : I → ℕ) :
    (∑ x ∈ U, q x) ^ 3 ≤
      U.card ^ 2 * ∑ x ∈ U, (q x) ^ 3 := by
  simpa using
    (pow_sum_le_card_mul_sum_pow
      (s := U) (f := q) (fun _x _hx ↦ Nat.zero_le _) 2)

/-- Cancellation step after the power-mean lower bound and ordered-triple
upper bound.  `moment` stands for `sum_x q_x^3`. -/
theorem ownerCard_mul_gap_le_of_cubicMomentBounds
    (L N r s e gap moment : ℕ)
    (hL : 0 < L)
    (_hsr : s ≤ r)
    (hgap : gap + s * N ^ 2 = r ^ 3)
    (hlower : L ^ 3 * r ^ 3 ≤ N ^ 2 * moment)
    (hupper : moment ≤
      s * L ^ 3 + (r - s) * (e + 1) * L ^ 2) :
    L * gap ≤ N ^ 2 * (r - s) * (e + 1) := by
  have hcombined :
      L ^ 3 * r ^ 3 ≤
        N ^ 2 * (s * L ^ 3 + (r - s) * (e + 1) * L ^ 2) :=
    hlower.trans (Nat.mul_le_mul_left (N ^ 2) hupper)
  have hcancelled :
      L ^ 2 * (L * gap) ≤
        L ^ 2 * (N ^ 2 * (r - s) * (e + 1)) := by
    have hwithCommon :
        L ^ 2 * (L * gap) + L ^ 3 * (s * N ^ 2) ≤
          L ^ 2 * (N ^ 2 * (r - s) * (e + 1)) +
            L ^ 3 * (s * N ^ 2) := by
      calc
      L ^ 2 * (L * gap) + L ^ 3 * (s * N ^ 2) =
          L ^ 3 * r ^ 3 := by
        rw [← hgap]
        ring
      _ ≤ N ^ 2 * (s * L ^ 3 + (r - s) * (e + 1) * L ^ 2) :=
        hcombined
      _ = L ^ 2 * (N ^ 2 * (r - s) * (e + 1)) +
          L ^ 3 * (s * N ^ 2) := by ring
    omega
  exact Nat.le_of_mul_le_mul_left hcancelled (pow_pos hL 2)

/-- Division form of the cubic-moment cap. -/
theorem ownerCard_le_cubicMomentCapacity
    (L N r s e gap moment : ℕ)
    (hL : 0 < L)
    (hsr : s ≤ r)
    (hgap : gap + s * N ^ 2 = r ^ 3)
    (hgapPos : 0 < gap)
    (hlower : L ^ 3 * r ^ 3 ≤ N ^ 2 * moment)
    (hupper : moment ≤
      s * L ^ 3 + (r - s) * (e + 1) * L ^ 2) :
    L ≤ (N ^ 2 * (r - s) * (e + 1)) / gap := by
  rw [Nat.le_div_iff_mul_le hgapPos]
  simpa [mul_comm] using ownerCard_mul_gap_le_of_cubicMomentBounds
    L N r s e gap moment hL hsr hgap hlower hupper

/-- Exact ordered-triple algebra.  The three repeated-index patterns and
the `(e-2)` possible third points on the line through an ordered pair
simplify to the displayed `e+1` correction. -/
theorem orderedTriple_upper_algebra
    (L r s e : ℤ) :
    s * (L * (L - 1) * (L - 2)) +
          (r - s) * (L * (L - 1) * (e - 2)) +
          r * (3 * L ^ 2 - 2 * L) =
      s * L ^ 3 + (r - s) * (e + 1) * L ^ 2 -
        e * (r - s) * L := by
  ring

lemma bchksTripleCore_endpoint_exact6400 :
    bchksTripleCoreAmbient6400 =
        131073 + bchksTripleCoreMaxCodim6400 ∧
      bchksTripleCoreIncidences6400 =
        54293 + bchksTripleCoreMaxCodim6400 ∧
      bchksTripleCoreMomentGap6400 +
          bchksTripleCoreMaxCodim6400 *
            bchksTripleCoreAmbient6400 ^ 2 =
        bchksTripleCoreIncidences6400 ^ 3 ∧
      (bchksTripleCoreAmbient6400 ^ 2 *
          (bchksTripleCoreIncidences6400 -
            bchksTripleCoreMaxCodim6400) *
          (bchksTripleCoreLineCap6400 + 1)) /
          bchksTripleCoreMomentGap6400 =
        bchksTripleCoreSafeOwnerCap6400 := by
  norm_num [bchksTripleCoreAmbient6400, bchksTripleCoreMaxCodim6400,
    bchksTripleCoreIncidences6400, bchksTripleCoreMomentGap6400,
    bchksTripleCoreLineCap6400, bchksTripleCoreSafeOwnerCap6400]

/-- The exact quadratic inequality retains the negative linear term and
improves the simple division cap by one owner. -/
lemma bchksTripleCore_exactQuadratic_endpoint6400 :
    bchksTripleCoreMomentGap6400 *
        bchksTripleCoreExactQuadraticOwnerCap6400 ^ 2 ≤
      bchksTripleCoreAmbient6400 ^ 2 *
        (bchksTripleCoreIncidences6400 -
          bchksTripleCoreMaxCodim6400) *
        ((bchksTripleCoreLineCap6400 + 1) *
            bchksTripleCoreExactQuadraticOwnerCap6400 -
          bchksTripleCoreLineCap6400) ∧
    bchksTripleCoreAmbient6400 ^ 2 *
        (bchksTripleCoreIncidences6400 -
          bchksTripleCoreMaxCodim6400) *
        ((bchksTripleCoreLineCap6400 + 1) *
            bchksTripleCoreSafeOwnerCap6400 -
          bchksTripleCoreLineCap6400) <
      bchksTripleCoreMomentGap6400 *
        bchksTripleCoreSafeOwnerCap6400 ^ 2 := by
  norm_num [bchksTripleCoreMomentGap6400,
    bchksTripleCoreExactQuadraticOwnerCap6400,
    bchksTripleCoreAmbient6400, bchksTripleCoreIncidences6400,
    bchksTripleCoreMaxCodim6400, bchksTripleCoreLineCap6400,
    bchksTripleCoreSafeOwnerCap6400]

/-- The cubic gap is positive at codimension 16107 and negative one step
later (stated over integers to avoid truncated subtraction). -/
lemma bchksTripleCore_exactEndpoint_sign6400 :
    (0 : ℤ) < (70400 : ℤ) ^ 3 - 16107 * (147180 : ℤ) ^ 2 ∧
      (70400 : ℤ) ^ 3 - 16107 * (147180 : ℤ) ^ 2 =
        4596693200 ∧
      (70401 : ℤ) ^ 3 - 16108 * (147181 : ℤ) ^ 2 =
        -6938134987 := by
  norm_num

/-- The corrected cubic cap still fits the scaled hybrid switch with more
than three trillion elements of headroom. -/
lemma bchksTripleCore_hybridSwitchBudget6400 :
    bchksTripleCoreSwitchExcess6400 =
        (bchksTripleCoreSafeOwnerCap6400 * bchksHybridYMass6400 + 511) /
          512 ∧
      bchksTripleCoreSafeOwnerCap6400 * bchksHybridYMass6400 ≤
        512 * bchksTripleCoreSwitchExcess6400 ∧
      bchksTripleCoreSwitchTotal6400 =
        bchksHybridTotal128_6400 + bchksTripleCoreSwitchExcess6400 ∧
      bchksTripleCoreSwitchTotal6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksTripleCoreSwitchTotal6400 =
        3168458272815 := by
  norm_num [bchksTripleCoreSwitchExcess6400,
    bchksTripleCoreSafeOwnerCap6400, bchksHybridYMass6400,
    bchksTripleCoreSwitchTotal6400, bchksHybridTotal128_6400,
    bchksWeightedNumerator6400]

/-- There is essentially no room to leave large-defect degree-129 factors
on the universal branch.  After reserving the cubic structural surcharge,
at most 3,011,058 units (under 0.18% of the total support mass) can pay the
degree-129 coefficient crossover. -/
lemma bchksTripleCore_uncoveredDegree129_threshold6400 :
    bchksHybridUniversalZCoefficient129_6400 -
        bchksHybridLowZCoefficient6400 = 1052288 ∧
      bchksTripleCoreSwitchExcess6400 +
          1052288 * bchksTripleCoreMaxUncoveredZMass129_6400 ≤
        bchksWeightedNumerator6400 - bchksHybridTotal128_6400 ∧
      bchksWeightedNumerator6400 - bchksHybridTotal128_6400 -
          (bchksTripleCoreSwitchExcess6400 +
            1052288 * bchksTripleCoreMaxUncoveredZMass129_6400) =
        163631 ∧
      bchksWeightedNumerator6400 - bchksHybridTotal128_6400 <
        bchksTripleCoreSwitchExcess6400 +
          1052288 * (bchksTripleCoreMaxUncoveredZMass129_6400 + 1) := by
  norm_num [bchksHybridUniversalZCoefficient129_6400,
    bchksHybridLowZCoefficient6400, bchksTripleCoreSwitchExcess6400,
    bchksTripleCoreMaxUncoveredZMass129_6400,
    bchksWeightedNumerator6400, bchksHybridTotal128_6400]

/-- End-to-end arithmetic switch using the cubic owner cap.  The hypotheses
keep the two genuinely structural inputs explicit: every charged factor has
degree at least 128 and its owner charge obeys the cubic cap. -/
theorem sum_factorCharge_le_tripleCoreCap
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (degree zDegree charge : R → ℕ)
    (hdegree : ∀ r ∈ Rs, 128 ≤ degree r)
    (huniversal : ∀ r ∈ Rs, charge r ≤
      bchksHybridUniversalUnitCoefficient6400 * degree r * zDegree r)
    (hcore : ∀ r ∈ Rs,
      charge r ≤ bchksTripleCoreSafeOwnerCap6400)
    (hzMass : (∑ r ∈ Rs, zDegree r) ≤ bchksHybridZMass6400)
    (hyMass : (∑ r ∈ Rs, degree r) ≤ bchksHybridYMass6400) :
    (∑ r ∈ Rs, charge r) ≤
      bchksHybridZCover128_6400 + bchksTripleCoreSwitchExcess6400 := by
  have hscaled : ∀ r ∈ Rs,
      512 * charge r ≤
        512 * bchksHybridLowZCoefficient6400 * zDegree r +
          degree r * bchksTripleCoreSafeOwnerCap6400 := by
    intro r hr
    exact factorCharge_scaled_le_universal_or_core
      (degree r) (zDegree r) bchksTripleCoreSafeOwnerCap6400
        (charge r) (hdegree r hr) (huniversal r hr) (hcore r hr)
  have hsum := sum_factorCharge_scaled_le Rs degree zDegree charge
    bchksTripleCoreSafeOwnerCap6400 hscaled hzMass hyMass
  have hexcess := bchksTripleCore_hybridSwitchBudget6400.2.1
  have hexcess' :
      bchksHybridYMass6400 * bchksTripleCoreSafeOwnerCap6400 ≤
        512 * bchksTripleCoreSwitchExcess6400 := by
    rw [Nat.mul_comm]
    exact hexcess
  have hscaledFinal :
      512 * (∑ r ∈ Rs, charge r) ≤
        512 * (bchksHybridZCover128_6400 +
          bchksTripleCoreSwitchExcess6400) := by
    calc
      512 * (∑ r ∈ Rs, charge r) ≤
          512 * bchksHybridLowZCoefficient6400 * bchksHybridZMass6400 +
            bchksHybridYMass6400 *
              bchksTripleCoreSafeOwnerCap6400 := hsum
      _ ≤ 512 * bchksHybridZCover128_6400 +
          512 * bchksTripleCoreSwitchExcess6400 := by
        have hzCover := bchksHybrid_componentLedger_exact6400.1
        rw [hzCover]
        exact Nat.add_le_add_left hexcess'
          (512 * bchksHybridLowZCoefficient6400 * bchksHybridZMass6400)
      _ = 512 * (bchksHybridZCover128_6400 +
          bchksTripleCoreSwitchExcess6400) := by ring
  exact le_of_mul_le_mul_left hscaledFinal (by norm_num)

end BCHKSTripleCoreMomentAudit6400
end ProximityPrize.SubmissionLower
