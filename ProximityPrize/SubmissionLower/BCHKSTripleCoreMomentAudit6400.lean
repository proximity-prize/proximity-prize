import ProximityPrize.SubmissionLower.BCHKSFullCoreGoodOwnerCover6400
import ProximityPrize.SubmissionLower.BCHKSHybridCoreSwitchAudit6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSTripleCoreMomentAudit6400
open BCHKSHybridHighDegreeAudit6400
open BCHKSHybridCoreSwitchAudit6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def bchksTripleCoreMaxCodim6400 : ℕ := 16107
def bchksTripleCoreAmbient6400 : ℕ := 147180
def bchksTripleCoreIncidences6400 : ℕ := 70400
def bchksTripleCoreLineCap6400 : ℕ := 76781
def bchksTripleCoreMomentGap6400 : ℕ := 4596693200
def bchksTripleCoreSafeOwnerCap6400 : ℕ := 19645149527
def bchksTripleCoreExactQuadraticOwnerCap6400 : ℕ := 19645149526
def bchksTripleCoreSwitchExcess6400 : ℕ := 3246322589905
def bchksTripleCoreSwitchTotal6400 : ℕ := 274975831541727185
def bchksTripleCoreMaxUncoveredZMass129_6400 : ℕ := 3011018
theorem cubic_powerMean_nat
    {I : Type*} (U : Finset I) (q : I → ℕ) :
    (∑ x ∈ U, q x) ^ 3 ≤
      U.card ^ 2 * ∑ x ∈ U, (q x) ^ 3 := by
  simpa using
    (pow_sum_le_card_mul_sum_pow
      (s := U) (f := q) (fun _x _hx ↦ Nat.zero_le _) 2)
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
lemma bchksTripleCore_exactEndpoint_sign6400 :
    (0 : ℤ) < (70400 : ℤ) ^ 3 - 16107 * (147180 : ℤ) ^ 2 ∧
      (70400 : ℤ) ^ 3 - 16107 * (147180 : ℤ) ^ 2 =
        4596693200 ∧
      (70401 : ℤ) ^ 3 - 16108 * (147181 : ℤ) ^ 2 =
        -6938134987 := by
  norm_num
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
