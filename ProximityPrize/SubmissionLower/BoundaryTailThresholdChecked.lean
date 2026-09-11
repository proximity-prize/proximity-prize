import ProximityPrize.SubmissionLower.BoundaryTailThresholdCheckedR01R07
import ProximityPrize.SubmissionLower.BoundaryTailThresholdCheckedR08R14
import ProximityPrize.SubmissionLower.BoundaryTailThresholdCheckedR15R22
import ProximityPrize.SubmissionLower.BoundaryTailThresholdCheckedR23R31

namespace ProximityPrize.SubmissionLower.Lower80811.ThresholdCompressed
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem thresholdReceipt : Lower80811.PhaseSemantics.ThresholdReceiptSound := by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact checkedR1 V (List.mem_range.mpr (by omega))
    | exact checkedR2 V (List.mem_range.mpr (by omega))
    | exact checkedR3 V (List.mem_range.mpr (by omega))
    | exact checkedR4 V (List.mem_range.mpr (by omega))
    | exact checkedR5 V (List.mem_range.mpr (by omega))
    | exact checkedR6 V (List.mem_range.mpr (by omega))
    | exact checkedR7 V (List.mem_range.mpr (by omega))
    | exact checkedR8 V (List.mem_range.mpr (by omega))
    | exact checkedR9 V (List.mem_range.mpr (by omega))
    | exact checkedR10 V (List.mem_range.mpr (by omega))
    | exact checkedR11 V (List.mem_range.mpr (by omega))
    | exact checkedR12 V (List.mem_range.mpr (by omega))
    | exact checkedR13 V (List.mem_range.mpr (by omega))
    | exact checkedR14 V (List.mem_range.mpr (by omega))
    | exact checkedR15 V (List.mem_range.mpr (by omega))
    | exact checkedR16 V (List.mem_range.mpr (by omega))
    | exact checkedR17 V (List.mem_range.mpr (by omega))
    | exact checkedR18 V (List.mem_range.mpr (by omega))
    | exact checkedR19 V (List.mem_range.mpr (by omega))
    | exact checkedR20 V (List.mem_range.mpr (by omega))
    | exact checkedR21 V (List.mem_range.mpr (by omega))
    | exact checkedR22 V (List.mem_range.mpr (by omega))
    | exact checkedR23 V (List.mem_range.mpr (by omega))
    | exact checkedR24 V (List.mem_range.mpr (by omega))
    | exact checkedR25 V (List.mem_range.mpr (by omega))
    | exact checkedR26 V (List.mem_range.mpr (by omega))
    | exact checkedR27 V (List.mem_range.mpr (by omega))
    | exact checkedR28 V (List.mem_range.mpr (by omega))
    | exact checkedR29 V (List.mem_range.mpr (by omega))
    | exact checkedR30 V (List.mem_range.mpr (by omega))
    | exact checkedR31 V (List.mem_range.mpr (by omega))

end ProximityPrize.SubmissionLower.Lower80811.ThresholdCompressed
