import ProximityPrize.SubmissionLower.LocatorResidualRegular6803

/-!
Bridge from a remembered divisor of the selected gcd to the regular residual
pair.  It packages the two quotient-box applications and then invokes the
retuned 68.03 unequal-pair theorem.
-/

namespace ProximityPrize.SubmissionLower.LocatorRetainedResidualBridge6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN174
  RCN180 RCN234 RCN238 RCN259 RCN266 RCN319
open LocatorCoprimeQuotient LocatorRetainedQuotient6803
  LocatorResidualRegular6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

private theorem terminal_middle_cap (p : FlagDegree) (hs : p.all ≤ 29) :
    (32826703 - retainedContact 131071 p - 1) / 131071 ≤
      250 - middle p := by
  apply (Nat.div_le_iff_le_mul (by decide)).2
  unfold retainedContact middle
  omega

/-- The B quotient lies in the full retained flag box used by both the
regular-pair and grouped-derivative residual estimates. -/
theorem quotientB_mem_retained_box
    (QA QB P : P4) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hP : P ≠ 0)
    (hQBbox : QB ∈ RCN100.globalCoefficientBox K
      20131293 131071 14261 34)
    (hPH : P ∣ gcd12 QA QB) :
    quotientB QA QB ∈ RCN174.globalCoefficientBox K
      (20131293 - retainedContact 131071 (originalCumulativeFlag P)) 131071
      (14261 - total (originalCumulativeFlag P))
      (34 - (originalCumulativeFlag P).all) := by
  let H := gcd12 QA QB
  let Q := quotientB QA QB
  have hH : H ≠ 0 := gcd_ne_zero_of_left hQA
  have hQeq : QB = H * Q := b_eq_gcd12_mul_quotientB QA QB
  have hQ : Q ≠ 0 := by
    intro hz
    exact hQB (by rw [hQeq, hz, mul_zero])
  have hflag := quotient_mem_box_of_retained_divisor
    QB H Q P 20131293 131071 14261 34
    hQB hH hQ hP hQBbox hQeq hPH (by decide)
  exact flag_box_to_ordinary K
    (20131293 - retainedContact 131071 (originalCumulativeFlag P)) 131071
    (14261 - total (originalCumulativeFlag P))
    (34 - (originalCumulativeFlag P).all) Q hflag

/-- The T quotient receives the three separated degree caps used on the right
of the unequal pair. -/
theorem quotientA_retained_degree_caps
    (QA QB P : P4) (hQA : QA ≠ 0) (hP : P ≠ 0)
    (hQAbox : QA ∈ RCN100.globalCoefficientBox K
      32826703 131071 6679 56)
    (hPH : P ∣ gcd12 QA QB)
    (hs : (originalCumulativeFlag P).all ≤ 29) :
    (quotientA QA QB).degreeOf 1 ≤
        250 - middle (originalCumulativeFlag P) ∧
      (quotientA QA QB).degreeOf 2 ≤
        56 - (originalCumulativeFlag P).all ∧
      (quotientA QA QB).degreeOf 3 ≤
        6679 - total (originalCumulativeFlag P) := by
  let H := gcd12 QA QB
  let T := quotientA QA QB
  have hH : H ≠ 0 := gcd_ne_zero_of_left hQA
  have hTeq : QA = H * T := a_eq_gcd12_mul_quotientA QA QB
  have hT : T ≠ 0 := by
    intro hz
    exact hQA (by rw [hTeq, hz, mul_zero])
  exact quotient_degree_caps_of_retained_divisor
    QA H T P 32826703 131071 6679 56 250
    hQA hH hT hP hQAbox hTeq hPH (by decide)
    (terminal_middle_cap (originalCumulativeFlag P) hs)

/-- The complete regular-pair charge for the residual set after retaining
`P ∣ gcd(QA,QB)`. -/
theorem retained_regularPairSeeds_sum_le
    (QA QB P : P4) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hP : P ≠ 0)
    (hQAbox : QA ∈ RCN100.globalCoefficientBox K
      32826703 131071 6679 56)
    (hQBbox : QB ∈ RCN100.globalCoefficientBox K
      20131293 131071 14261 34)
    (hPH : P ∣ gcd12 QA QB)
    (hs : (originalCumulativeFlag P).all ≤ 29)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781) :
    (∑ F : RCN052.RegularIndex (quotientB QA QB),
      (regularPairSeeds (quotientB QA QB) (quotientA QA QB)
        selected Gamma F).card) ≤
      (residualPairStage (originalCumulativeFlag P)).regularCountCap := by
  have hQ : quotientB QA QB ≠ 0 := by
    intro hz
    have hH : gcd12 QA QB ≠ 0 := gcd_ne_zero_of_left hQA
    exact hQB (by
      rw [b_eq_gcd12_mul_quotientB QA QB, hz, mul_zero])
  have hQbox := quotientB_mem_retained_box
    QA QB P hQA hQB hP hQBbox hPH
  have hTcaps := quotientA_retained_degree_caps
    QA QB P hQA hP hQAbox hPH hs
  exact regularPairSeeds_sum_le (originalCumulativeFlag P) hs
    (quotientB QA QB) (quotientA QA QB) hQ
    (firstQuotients_isRelPrime hQA).symm hQbox hTcaps
    selected Gamma u0 u1 hdegree hagreement hno

end

end ProximityPrize.SubmissionLower.LocatorRetainedResidualBridge6803
