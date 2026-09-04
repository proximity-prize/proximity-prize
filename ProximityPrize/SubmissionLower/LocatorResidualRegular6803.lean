import ProximityPrize.SubmissionLower.LocatorRetainedQuotient6803
import ProximityPrize.SubmissionLower.LocatorDerivativeChain

/-!
The regular-pair part of the retained residual locator.  Both selected
quotients lose the cumulative flag `p` of the remembered gcd product; this
module turns those quotient boxes into the exact unequal-pair charge used by
the coupled 68.03 receipt.
-/

namespace ProximityPrize.SubmissionLower.LocatorResidualRegular6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN174 RCN180
  RCN234 RCN238 RCN260 RCN266 RCN294 RCN318 RCN319
open LocatorDerivativeChain LocatorRetainedQuotient6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

def residualPairStage (p : FlagDegree) : UnequalParameters :=
  ⟨262144, 131071, 181363,
    153 - middle p, 34 - p.all, 14261 - total p,
    250 - middle p, 56 - p.all, 6679 - total p⟩

theorem flag_order (p : FlagDegree) :
    p.all ≤ middle p ∧ middle p ≤ total p := by
  simp only [middle, total]
  omega

private theorem left_middle_cap (p : FlagDegree) (hs : p.all ≤ 29) :
    (20131293 - retainedContact 131071 p - 1) / 131071 ≤
      153 - middle p := by
  apply (Nat.div_le_iff_le_mul (by decide)).2
  unfold retainedContact middle
  omega

private theorem mixed_gates (p : FlagDegree) :
    (residualPairStage p).mixedCost.y < 2130706433 ∧
      (residualPairStage p).mixedCost.r < 2130706433 ∧
      (residualPairStage p).mixedCost.z < 2130706433 := by
  have ly : 153 - middle p ≤ 153 := Nat.sub_le _ _
  have lr : 34 - p.all ≤ 34 := Nat.sub_le _ _
  have lz : 14261 - total p ≤ 14261 := Nat.sub_le _ _
  have ry : 250 - middle p ≤ 250 := Nat.sub_le _ _
  have rr : 56 - p.all ≤ 56 := Nat.sub_le _ _
  have rz : 6679 - total p ≤ 6679 := Nat.sub_le _ _
  simp only [residualPairStage, UnequalParameters.mixedCost]
  constructor
  · calc
      (34 - p.all) * (6679 - total p) +
          (14261 - total p) * (56 - p.all) ≤
          34 * 6679 + 14261 * 56 :=
        Nat.add_le_add (Nat.mul_le_mul lr rz) (Nat.mul_le_mul lz rr)
      _ < 2130706433 := by decide
  constructor
  · calc
      (153 - middle p) * (6679 - total p) +
          (14261 - total p) * (250 - middle p) ≤
          153 * 6679 + 14261 * 250 :=
        Nat.add_le_add (Nat.mul_le_mul ly rz) (Nat.mul_le_mul lz ry)
      _ < 2130706433 := by decide
  · calc
      (153 - middle p) * (56 - p.all) +
          (34 - p.all) * (250 - middle p) ≤
          153 * 56 + 34 * 250 :=
        Nat.add_le_add (Nat.mul_le_mul ly rr) (Nat.mul_le_mul lr ry)
      _ < 2130706433 := by decide

/-- Sum of all regular-pair populations in the residual cover. -/
theorem regularPairSeeds_sum_le
    (p : FlagDegree) (hs : p.all ≤ 29)
    (Q T : P4) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (hQbox : Q ∈ RCN174.globalCoefficientBox K
      (20131293 - retainedContact 131071 p) 131071
      (14261 - total p) (34 - p.all))
    (hTcaps : T.degreeOf 1 ≤ 250 - middle p ∧
      T.degreeOf 2 ≤ 56 - p.all ∧ T.degreeOf 3 ≤ 6679 - total p)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781) :
    (∑ F : RCN052.RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card) ≤
        (residualPairStage p).regularCountCap := by
  let P := residualPairStage p
  have hmixed := mixed_gates p
  have hcount := all_regularPairSeeds_bound P Q T hQ hrel
    (20131293 - retainedContact 131071 p) 131071
    (14261 - total p) (34 - p.all) 2130706433
    hQbox (by decide) (left_middle_cap p hs) le_rfl le_rfl
    hTcaps.1 hTcaps.2.1 hTcaps.2.2
    (by simp only [P, residualPairStage]; omega)
    (by simp only [P, residualPairStage]; omega)
    (by simp only [P, residualPairStage]; omega)
    (by simp only [P, residualPairStage]; omega)
    hmixed.1 hmixed.2.1 hmixed.2.2
    selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by simp [P, residualPairStage, I, IRSProfile.Index])
    (by simp [P, residualPairStage])
    (by simp [P, residualPairStage])
    (by simp [P, residualPairStage])
    (by simp [P, residualPairStage])
    (by simpa [P, residualPairStage] using hdegree)
    (by simpa [P, residualPairStage] using hagreement)
    (by simpa [P, residualPairStage, UnequalParameters.errors] using hno)
  have hbudget := regularVector_budgets P Q hQ
    (20131293 - retainedContact 131071 p) 131071
    (14261 - total p) (34 - p.all) (by decide) hQbox
    (left_middle_cap p hs) le_rfl le_rfl
  have hscaled := sum_regular_counts_bound P Q T selected Gamma hbudget hcount
  exact P.regular_count_le _
    (by norm_num [P, residualPairStage, UnequalParameters.gap]) hscaled

end

end ProximityPrize.SubmissionLower.LocatorResidualRegular6803
