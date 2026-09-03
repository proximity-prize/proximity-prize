import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunData25
import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunData26
import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunData27
import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunData28
import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunsBridge

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked

open LocatorPhase6800Concrete LocatorPhase6800PhaseRunsBridge

set_option autoImplicit false
set_option maxRecDepth 100000

theorem states : PhaseStateChecks := by
  intro R hR hpos
  have hlt : R < 29 := List.mem_range.mp hR
  interval_cases R <;>
  first
    | exact sparseLayer_to_public 1 (by decide) (by decide)
        LocatorPhase6800PhaseRunData01.sparseStates
    | exact sparseLayer_to_public 2 (by decide) (by decide)
        LocatorPhase6800PhaseRunData02.sparseStates
    | exact sparseLayer_to_public 3 (by decide) (by decide)
        LocatorPhase6800PhaseRunData03.sparseStates
    | exact sparseLayer_to_public 4 (by decide) (by decide)
        LocatorPhase6800PhaseRunData04.sparseStates
    | exact sparseLayer_to_public 5 (by decide) (by decide)
        LocatorPhase6800PhaseRunData05.sparseStates
    | exact sparseLayer_to_public 6 (by decide) (by decide)
        LocatorPhase6800PhaseRunData06.sparseStates
    | exact sparseLayer_to_public 7 (by decide) (by decide)
        LocatorPhase6800PhaseRunData07.sparseStates
    | exact sparseLayer_to_public 8 (by decide) (by decide)
        LocatorPhase6800PhaseRunData08.sparseStates
    | exact sparseLayer_to_public 9 (by decide) (by decide)
        LocatorPhase6800PhaseRunData09.sparseStates
    | exact sparseLayer_to_public 10 (by decide) (by decide)
        LocatorPhase6800PhaseRunData10.sparseStates
    | exact sparseLayer_to_public 11 (by decide) (by decide)
        LocatorPhase6800PhaseRunData11.sparseStates
    | exact sparseLayer_to_public 12 (by decide) (by decide)
        LocatorPhase6800PhaseRunData12.sparseStates
    | exact sparseLayer_to_public 13 (by decide) (by decide)
        LocatorPhase6800PhaseRunData13.sparseStates
    | exact sparseLayer_to_public 14 (by decide) (by decide)
        LocatorPhase6800PhaseRunData14.sparseStates
    | exact sparseLayer_to_public 15 (by decide) (by decide)
        LocatorPhase6800PhaseRunData15.sparseStates
    | exact sparseLayer_to_public 16 (by decide) (by decide)
        LocatorPhase6800PhaseRunData16.sparseStates
    | exact sparseLayer_to_public 17 (by decide) (by decide)
        LocatorPhase6800PhaseRunData17.sparseStates
    | exact sparseLayer_to_public 18 (by decide) (by decide)
        LocatorPhase6800PhaseRunData18.sparseStates
    | exact sparseLayer_to_public 19 (by decide) (by decide)
        LocatorPhase6800PhaseRunData19.sparseStates
    | exact sparseLayer_to_public 20 (by decide) (by decide)
        LocatorPhase6800PhaseRunData20.sparseStates
    | exact sparseLayer_to_public 21 (by decide) (by decide)
        LocatorPhase6800PhaseRunData21.sparseStates
    | exact sparseLayer_to_public 22 (by decide) (by decide)
        LocatorPhase6800PhaseRunData22.sparseStates
    | exact sparseLayer_to_public 23 (by decide) (by decide)
        LocatorPhase6800PhaseRunData23.sparseStates
    | exact sparseLayer_to_public 24 (by decide) (by decide)
        LocatorPhase6800PhaseRunData24.sparseStates
    | exact sparseLayer_to_public 25 (by decide) (by decide)
        LocatorPhase6800PhaseRunData25.sparseStates
    | exact sparseLayer_to_public 26 (by decide) (by decide)
        LocatorPhase6800PhaseRunData26.sparseStates
    | exact sparseLayer_to_public 27 (by decide) (by decide)
        LocatorPhase6800PhaseRunData27.sparseStates
    | exact sparseLayer_to_public 28 (by decide) (by decide)
        LocatorPhase6800PhaseRunData28.sparseStates

end ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked

