/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
import ProximityPrize.SubmissionLower.Mid6833K6833End1
import ProximityPrize.SubmissionLower.Mid6833K6833End2
import ProximityPrize.SubmissionLower.Mid6833K6833End3
import ProximityPrize.SubmissionLower.Mid6833K6833End4
import ProximityPrize.SubmissionLower.Mid6833K6833End5
import ProximityPrize.SubmissionLower.Mid6833K6833End6
import ProximityPrize.SubmissionLower.Mid6833K6833End7
import ProximityPrize.SubmissionLower.Mid6833K6833End8
import ProximityPrize.SubmissionLower.Mid6833K6833End9
import ProximityPrize.SubmissionLower.Mid6833K6833End10
import ProximityPrize.SubmissionLower.Mid6833K6833End11
import ProximityPrize.SubmissionLower.Mid6833K6833End12
import ProximityPrize.SubmissionLower.Mid6833K6833End13
import ProximityPrize.SubmissionLower.Mid6833K6833End14
import ProximityPrize.SubmissionLower.Mid6833K6833End15
import ProximityPrize.SubmissionLower.Mid6833K6833End16
namespace ProximityPrize.SubmissionLower.K6833AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open K6833FlowSources K6833FlowStages K6833FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
theorem checkedRanks (r : ℕ) (h : 1≤r) (h' : r≤16) : checkedRank r = true := by
  interval_cases r
  · exact checkedEnd1
  · exact checkedEnd2
  · exact checkedEnd3
  · exact checkedEnd4
  · exact checkedEnd5
  · exact checkedEnd6
  · exact checkedEnd7
  · exact checkedEnd8
  · exact checkedEnd9
  · exact checkedEnd10
  · exact checkedEnd11
  · exact checkedEnd12
  · exact checkedEnd13
  · exact checkedEnd14
  · exact checkedEnd15
  · exact checkedEnd16
private theorem cut_le {f : FlagDegree} (prev : Prior 5 f) {r y : ℕ}
    (rp:0<r) (ry:r≤y) (r16:r≤16) (yup:y≤maxY r+1) (hr:r≤f.all) (hy:y≤middle f) :
    total f≤endCap r y := by
  have c := getCheck (checkedRanks r rp r16) ry yup
  have ⟨a,b⟩ := Bool.and_eq_true_iff.mp c
  have aa := of_decide_eq_true a
  by_contra! nt
  exact prior_contra prev le_rfl (endEntry r y).2 rp ry aa.2.1 hr hy nt
    (Bool.and_eq_true_iff.mpr ⟨decide_eq_true aa.2.2.2,b⟩)

theorem inside {f : FlagDegree} (hp : 0<f.all) (prev : Prior 5 f) :
    1≤f.all ∧ f.all≤15 ∧ f.all≤middle f ∧ middle f≤maxY f.all := by
  have ry : f.all≤middle f := Nat.le_add_left _ _
  have yt : middle f≤total f := by unfold middle total; omega
  have r15 : f.all≤15 := by
    by_contra! z
    have h := cut_le (f:=f) prev (r:=16) (y:=16) (by decide) le_rfl le_rfl (by decide) z ((show 16≤f.all from z).trans ry)
    have e : endCap 16 16=15 := by decide +kernel
    omega
  refine ⟨hp,r15,ry,?_⟩
  by_contra! z
  have rbound : f.all≤maxY f.all+1 := by
    have all : ∀ r : Fin 16, r.val≤maxY r.val+1 := by decide +kernel
    exact all ⟨f.all,by omega⟩
  have h := cut_le (f:=f) prev hp rbound (by omega) le_rfl le_rfl z
  have ⟨a,_⟩ := Bool.and_eq_true_iff.mp (getCheck (r:=f.all) (y:=maxY f.all+1) (checkedRanks f.all hp (by omega)) rbound le_rfl)
  have eq := (of_decide_eq_true a).2.2.1 rfl
  unfold endCap at h
  omega

theorem end_bound (f : FlagDegree) (hpos : 0<f.all) (hprior : Prior 5 f) :
    total f ≤ endCap f.all (middle f) := by
  obtain ⟨_,rm,ry,ym⟩ := inside hpos hprior
  exact cut_le hprior hpos ry (by omega) (by omega) le_rfl le_rfl

#print axioms end_bound
end ProximityPrize.SubmissionLower.K6833AdaptiveCert
