import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31

import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correctAll:∀ R V,1 ≤ R → R ≤ 31 → R+V ≤ 142 → CorrectAt R V:=by
  intro R V hR hRmax hRV
  interval_cases R
  · exact cr1 V (List.mem_range.mpr (by omega))
  · exact cr2 V (List.mem_range.mpr (by omega))
  · exact cr3 V (List.mem_range.mpr (by omega))
  · exact cr4 V (List.mem_range.mpr (by omega))
  · exact cr5 V (List.mem_range.mpr (by omega))
  · exact cr6 V (List.mem_range.mpr (by omega))
  · exact cr7 V (List.mem_range.mpr (by omega))
  · exact cr8 V (List.mem_range.mpr (by omega))
  · exact cr9 V (List.mem_range.mpr (by omega))
  · exact cr10 V (List.mem_range.mpr (by omega))
  · exact cr11 V (List.mem_range.mpr (by omega))
  · exact cr12 V (List.mem_range.mpr (by omega))
  · exact cr13 V (List.mem_range.mpr (by omega))
  · exact cr14 V (List.mem_range.mpr (by omega))
  · exact cr15 V (List.mem_range.mpr (by omega))
  · exact cr16 V (List.mem_range.mpr (by omega))
  · exact cr17 V (List.mem_range.mpr (by omega))
  · exact cr18 V (List.mem_range.mpr (by omega))
  · exact cr19 V (List.mem_range.mpr (by omega))
  · exact cr20 V (List.mem_range.mpr (by omega))
  · exact cr21 V (List.mem_range.mpr (by omega))
  · exact cr22 V (List.mem_range.mpr (by omega))
  · exact cr23 V (List.mem_range.mpr (by omega))
  · exact cr24 V (List.mem_range.mpr (by omega))
  · exact cr25 V (List.mem_range.mpr (by omega))
  · exact cr26 V (List.mem_range.mpr (by omega))
  · exact cr27 V (List.mem_range.mpr (by omega))
  · exact cr28 V (List.mem_range.mpr (by omega))
  · exact cr29 V (List.mem_range.mpr (by omega))
  · exact cr30 V (List.mem_range.mpr (by omega))
  · exact cr31 V (List.mem_range.mpr (by omega))
theorem zeroAll:∀ R V,1 ≤ R → R ≤ 31 → R+V ≤ 142 → ZeroCheckAt R V:=by
  intro R V hR hRmax hRV
  interval_cases R
  · exact zr1 V (List.mem_range.mpr (by omega))
  · exact zr2 V (List.mem_range.mpr (by omega))
  · exact zr3 V (List.mem_range.mpr (by omega))
  · exact zr4 V (List.mem_range.mpr (by omega))
  · exact zr5 V (List.mem_range.mpr (by omega))
  · exact zr6 V (List.mem_range.mpr (by omega))
  · exact zr7 V (List.mem_range.mpr (by omega))
  · exact zr8 V (List.mem_range.mpr (by omega))
  · exact zr9 V (List.mem_range.mpr (by omega))
  · exact zr10 V (List.mem_range.mpr (by omega))
  · exact zr11 V (List.mem_range.mpr (by omega))
  · exact zr12 V (List.mem_range.mpr (by omega))
  · exact zr13 V (List.mem_range.mpr (by omega))
  · exact zr14 V (List.mem_range.mpr (by omega))
  · exact zr15 V (List.mem_range.mpr (by omega))
  · exact zr16 V (List.mem_range.mpr (by omega))
  · exact zr17 V (List.mem_range.mpr (by omega))
  · exact zr18 V (List.mem_range.mpr (by omega))
  · exact zr19 V (List.mem_range.mpr (by omega))
  · exact zr20 V (List.mem_range.mpr (by omega))
  · exact zr21 V (List.mem_range.mpr (by omega))
  · exact zr22 V (List.mem_range.mpr (by omega))
  · exact zr23 V (List.mem_range.mpr (by omega))
  · exact zr24 V (List.mem_range.mpr (by omega))
  · exact zr25 V (List.mem_range.mpr (by omega))
  · exact zr26 V (List.mem_range.mpr (by omega))
  · exact zr27 V (List.mem_range.mpr (by omega))
  · exact zr28 V (List.mem_range.mpr (by omega))
  · exact zr29 V (List.mem_range.mpr (by omega))
  · exact zr30 V (List.mem_range.mpr (by omega))
  · exact zr31 V (List.mem_range.mpr (by omega))
theorem strictAll:∀ R V,1 ≤ R → R ≤ 31 → R+V ≤ 142 → StrictCheckAt R V:=by
  intro R V hR hRmax hRV
  interval_cases R
  · exact sr1 V (List.mem_range.mpr (by omega))
  · exact sr2 V (List.mem_range.mpr (by omega))
  · exact sr3 V (List.mem_range.mpr (by omega))
  · exact sr4 V (List.mem_range.mpr (by omega))
  · exact sr5 V (List.mem_range.mpr (by omega))
  · exact sr6 V (List.mem_range.mpr (by omega))
  · exact sr7 V (List.mem_range.mpr (by omega))
  · exact sr8 V (List.mem_range.mpr (by omega))
  · exact sr9 V (List.mem_range.mpr (by omega))
  · exact sr10 V (List.mem_range.mpr (by omega))
  · exact sr11 V (List.mem_range.mpr (by omega))
  · exact sr12 V (List.mem_range.mpr (by omega))
  · exact sr13 V (List.mem_range.mpr (by omega))
  · exact sr14 V (List.mem_range.mpr (by omega))
  · exact sr15 V (List.mem_range.mpr (by omega))
  · exact sr16 V (List.mem_range.mpr (by omega))
  · exact sr17 V (List.mem_range.mpr (by omega))
  · exact sr18 V (List.mem_range.mpr (by omega))
  · exact sr19 V (List.mem_range.mpr (by omega))
  · exact sr20 V (List.mem_range.mpr (by omega))
  · exact sr21 V (List.mem_range.mpr (by omega))
  · exact sr22 V (List.mem_range.mpr (by omega))
  · exact sr23 V (List.mem_range.mpr (by omega))
  · exact sr24 V (List.mem_range.mpr (by omega))
  · exact sr25 V (List.mem_range.mpr (by omega))
  · exact sr26 V (List.mem_range.mpr (by omega))
  · exact sr27 V (List.mem_range.mpr (by omega))
  · exact sr28 V (List.mem_range.mpr (by omega))
  · exact sr29 V (List.mem_range.mpr (by omega))
  · exact sr30 V (List.mem_range.mpr (by omega))
  · exact sr31 V (List.mem_range.mpr (by omega))
theorem baseAll:∀ R V,1 ≤ R → R ≤ 31 → R+V ≤ 142 → BaseCheckAt R V:=by
  intro R V hR hRmax hRV
  interval_cases R
  · exact br1 V (List.mem_range.mpr (by omega))
  · exact br2 V (List.mem_range.mpr (by omega))
  · exact br3 V (List.mem_range.mpr (by omega))
  · exact br4 V (List.mem_range.mpr (by omega))
  · exact br5 V (List.mem_range.mpr (by omega))
  · exact br6 V (List.mem_range.mpr (by omega))
  · exact br7 V (List.mem_range.mpr (by omega))
  · exact br8 V (List.mem_range.mpr (by omega))
  · exact br9 V (List.mem_range.mpr (by omega))
  · exact br10 V (List.mem_range.mpr (by omega))
  · exact br11 V (List.mem_range.mpr (by omega))
  · exact br12 V (List.mem_range.mpr (by omega))
  · exact br13 V (List.mem_range.mpr (by omega))
  · exact br14 V (List.mem_range.mpr (by omega))
  · exact br15 V (List.mem_range.mpr (by omega))
  · exact br16 V (List.mem_range.mpr (by omega))
  · exact br17 V (List.mem_range.mpr (by omega))
  · exact br18 V (List.mem_range.mpr (by omega))
  · exact br19 V (List.mem_range.mpr (by omega))
  · exact br20 V (List.mem_range.mpr (by omega))
  · exact br21 V (List.mem_range.mpr (by omega))
  · exact br22 V (List.mem_range.mpr (by omega))
  · exact br23 V (List.mem_range.mpr (by omega))
  · exact br24 V (List.mem_range.mpr (by omega))
  · exact br25 V (List.mem_range.mpr (by omega))
  · exact br26 V (List.mem_range.mpr (by omega))
  · exact br27 V (List.mem_range.mpr (by omega))
  · exact br28 V (List.mem_range.mpr (by omega))
  · exact br29 V (List.mem_range.mpr (by omega))
  · exact br30 V (List.mem_range.mpr (by omega))
  · exact br31 V (List.mem_range.mpr (by omega))
theorem receipt:BoundaryTailBaseOracle.Receipt BoundaryTailStrictData.zero
    BoundaryTailStrictData.cap BoundaryTailBaseData.cap:=
  receipt_of_checks carriers runs correctAll zeroAll strictAll baseAll

theorem phaseReceipt:BoundaryTailBaseOracle.Receipt BoundaryTailStrictData.zero
    BoundaryTailStrictData.cap (Lower80801.PhaseSemantics.phaseCap 0):=by
  convert receipt using 1
  funext p
  rfl
end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
