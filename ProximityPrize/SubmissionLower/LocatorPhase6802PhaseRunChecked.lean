import ProximityPrize.SubmissionLower.LocatorPhase6802PhaseRunsBridge

namespace ProximityPrize.SubmissionLower.LocatorPhase6802PhaseRunChecked

open LocatorPhase6802Concrete LocatorPhase6802PhaseRunsBridge

set_option autoImplicit false
set_option maxRecDepth 100000

theorem states : PhaseStateChecks := by
  intro R hR hpos
  have hlt : R < 30 := List.mem_range.mp hR
  interval_cases R
  · exact sparseLayer_to_public 1 (by decide) (by decide)
      LocatorPhase6802PhaseRunData01.sparseStates
  · exact sparseLayer_to_public 2 (by decide) (by decide)
      LocatorPhase6802PhaseRunData02.sparseStates
  · exact sparseLayer_to_public 3 (by decide) (by decide)
      LocatorPhase6802PhaseRunData03.sparseStates
  · exact sparseLayer_to_public 4 (by decide) (by decide)
      LocatorPhase6802PhaseRunData04.sparseStates
  · exact sparseLayer_to_public 5 (by decide) (by decide)
      LocatorPhase6802PhaseRunData05.sparseStates
  · exact sparseLayer_to_public 6 (by decide) (by decide)
      LocatorPhase6802PhaseRunData06.sparseStates
  · exact sparseLayer_to_public 7 (by decide) (by decide)
      LocatorPhase6802PhaseRunData07.sparseStates
  · exact sparseLayer_to_public 8 (by decide) (by decide)
      LocatorPhase6802PhaseRunData08.sparseStates
  · exact sparseLayer_to_public 9 (by decide) (by decide)
      LocatorPhase6802PhaseRunData09.sparseStates
  · exact sparseLayer_to_public 10 (by decide) (by decide)
      LocatorPhase6802PhaseRunData10.sparseStates
  · exact sparseLayer_to_public 11 (by decide) (by decide)
      LocatorPhase6802PhaseRunData11.sparseStates
  · exact sparseLayer_to_public 12 (by decide) (by decide)
      LocatorPhase6802PhaseRunData12.sparseStates
  · exact sparseLayer_to_public 13 (by decide) (by decide)
      LocatorPhase6802PhaseRunData13.sparseStates
  · exact sparseLayer_to_public 14 (by decide) (by decide)
      LocatorPhase6802PhaseRunData14.sparseStates
  · exact sparseLayer_to_public 15 (by decide) (by decide)
      LocatorPhase6802PhaseRunData15.sparseStates
  · exact sparseLayer_to_public 16 (by decide) (by decide)
      LocatorPhase6802PhaseRunData16.sparseStates
  · exact sparseLayer_to_public 17 (by decide) (by decide)
      LocatorPhase6802PhaseRunData17.sparseStates
  · exact sparseLayer_to_public 18 (by decide) (by decide)
      LocatorPhase6802PhaseRunData18.sparseStates
  · exact sparseLayer_to_public 19 (by decide) (by decide)
      LocatorPhase6802PhaseRunData19.sparseStates
  · exact sparseLayer_to_public 20 (by decide) (by decide)
      LocatorPhase6802PhaseRunData20.sparseStates
  · exact sparseLayer_to_public 21 (by decide) (by decide)
      LocatorPhase6802PhaseRunData21.sparseStates
  · exact sparseLayer_to_public 22 (by decide) (by decide)
      LocatorPhase6802PhaseRunData22.sparseStates
  · exact sparseLayer_to_public 23 (by decide) (by decide)
      LocatorPhase6802PhaseRunData23.sparseStates
  · exact sparseLayer_to_public 24 (by decide) (by decide)
      LocatorPhase6802PhaseRunData24.sparseStates
  · exact sparseLayer_to_public 25 (by decide) (by decide)
      LocatorPhase6802PhaseRunData25.sparseStates
  · exact sparseLayer_to_public 26 (by decide) (by decide)
      LocatorPhase6802PhaseRunData26.sparseStates
  · exact sparseLayer_to_public 27 (by decide) (by decide)
      LocatorPhase6802PhaseRunData27.sparseStates
  · exact sparseLayer_to_public 28 (by decide) (by decide)
      LocatorPhase6802PhaseRunData28.sparseStates

  · exact sparseLayer_to_public 29 (by decide) (by decide)
      LocatorPhase6802PhaseRunData29.sparseStates

end ProximityPrize.SubmissionLower.LocatorPhase6802PhaseRunChecked
