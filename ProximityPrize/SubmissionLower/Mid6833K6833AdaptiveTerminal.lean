/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
import ProximityPrize.SubmissionLower.Mid6833K6833AdaptiveLink
import ProximityPrize.SubmissionLower.Mid6833GroupCredit
namespace ProximityPrize.SubmissionLower.K6833AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open K6833FlowSources K6833FlowStages K6833FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
open K6833Residual K6833Group
open scoped BigOperators

theorem credit_eq (j:Fin 5) (f:FlagDegree) :
    credit (capStage j) f=priceAt j f.all (middle f) (middle f) := by
  have hraw : creditFlag f = raw f.all (middle f) (middle f) := by
    cases f with | mk z y r =>
      change (⟨0,y,r⟩ : FlagDegree)=⟨(y+r)-(y+r),y+r-r,r⟩
      simp
  by_cases pos : 0<f.all
  · simp only [credit,priceAt,dif_pos pos]
    unfold stagePrice
    have cutEq {a b : FlagDegree} (e:a=b) (ha:0<a.all) (hb:0<b.all) :
        stageScaledCut a ha=stageScaledCut b hb := by cases e; rfl
    rw [cutEq hraw pos pos,hraw]
  · simp only [credit,priceAt,dif_neg pos]

theorem terminal_link (f : FlagDegree) (hpos : 0<f.all) (hprior : Prior 5 f) :
    ∃ row, rowAt f.all (middle f)=some row ∧ row.envelope.slope=f.all ∧
      row.envelope.middle=middle f ∧ total f ≤row.envelope.total ∧
      (∑ i : Fin 5, (fee i-credit (capStage i) f)) + row.terminalLimit ≤finalBudget := by
  simpa only [credit_eq,charged] using row_link hpos hprior

theorem empty_budget : (∑ i : Fin 5, fee i) ≤ finalBudget := by decide +kernel
#print axioms terminal_link

end ProximityPrize.SubmissionLower.K6833AdaptiveCert
