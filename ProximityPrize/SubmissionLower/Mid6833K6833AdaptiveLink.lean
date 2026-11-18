/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
import ProximityPrize.SubmissionLower.Mid6833K6833AdaptiveEnd
import ProximityPrize.SubmissionLower.Mid6833K6833LinkBase
namespace ProximityPrize.SubmissionLower.K6833AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open K6833FlowSources K6833FlowStages K6833FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
open K6833Residual
theorem row_link {f : FlagDegree} (hpos : 0<f.all) (hprior : Prior 5 f) :
    ∃ row, rowAt f.all (middle f)=some row ∧ row.envelope.slope=f.all ∧
      row.envelope.middle=middle f ∧ total f ≤row.envelope.total ∧
      charged f.all (middle f) + row.terminalLimit≤finalBudget := by
  have ⟨_,rm,ry,ym⟩ := inside hpos hprior
  have h : linkRank f.all = true := by
    have z := checkedLink ⟨f.all-1,by omega⟩
    simpa [Nat.sub_add_cancel hpos] using z
  have k : middle f-f.all ∈ List.range (maxY f.all+1-f.all) := List.mem_range.mpr (by omega)
  have a := List.all_eq_true.mp h (middle f-f.all) k
  rw [Nat.sub_add_cancel ry] at a
  unfold checkRow at a
  split at a
  · exact Bool.noConfusion a
  · rename_i row he
    obtain ⟨hs,hy,ht,hp⟩ := of_decide_eq_true a
    exact ⟨row,he,hs,hy,(end_bound f hpos hprior).trans_eq ht.symm,hp⟩

end ProximityPrize.SubmissionLower.K6833AdaptiveCert
