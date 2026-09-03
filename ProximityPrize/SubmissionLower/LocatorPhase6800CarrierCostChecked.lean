import ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck25
import ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck26
import ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck27
import ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck28

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostChecked

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000

theorem correct :
    ∀ r ∈ List.range 29, 1 ≤ r →
      ∀ v ∈ List.range (128 - r), Correct r v := by
  intro r hr hpos
  have hlt : r < 29 := List.mem_range.mp hr
  interval_cases r <;>
  first
    | exact LocatorPhase6800CarrierCostCheck01.correct
    | exact LocatorPhase6800CarrierCostCheck02.correct
    | exact LocatorPhase6800CarrierCostCheck03.correct
    | exact LocatorPhase6800CarrierCostCheck04.correct
    | exact LocatorPhase6800CarrierCostCheck05.correct
    | exact LocatorPhase6800CarrierCostCheck06.correct
    | exact LocatorPhase6800CarrierCostCheck07.correct
    | exact LocatorPhase6800CarrierCostCheck08.correct
    | exact LocatorPhase6800CarrierCostCheck09.correct
    | exact LocatorPhase6800CarrierCostCheck10.correct
    | exact LocatorPhase6800CarrierCostCheck11.correct
    | exact LocatorPhase6800CarrierCostCheck12.correct
    | exact LocatorPhase6800CarrierCostCheck13.correct
    | exact LocatorPhase6800CarrierCostCheck14.correct
    | exact LocatorPhase6800CarrierCostCheck15.correct
    | exact LocatorPhase6800CarrierCostCheck16.correct
    | exact LocatorPhase6800CarrierCostCheck17.correct
    | exact LocatorPhase6800CarrierCostCheck18.correct
    | exact LocatorPhase6800CarrierCostCheck19.correct
    | exact LocatorPhase6800CarrierCostCheck20.correct
    | exact LocatorPhase6800CarrierCostCheck21.correct
    | exact LocatorPhase6800CarrierCostCheck22.correct
    | exact LocatorPhase6800CarrierCostCheck23.correct
    | exact LocatorPhase6800CarrierCostCheck24.correct
    | exact LocatorPhase6800CarrierCostCheck25.correct
    | exact LocatorPhase6800CarrierCostCheck26.correct
    | exact LocatorPhase6800CarrierCostCheck27.correct
    | exact LocatorPhase6800CarrierCostCheck28.correct

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostChecked
