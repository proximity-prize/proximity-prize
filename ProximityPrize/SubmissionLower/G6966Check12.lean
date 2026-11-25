import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_12_12_0 : (chunkOf (Low6966Gate.gateList 12 12) 0).all (fF 12 12) = true := by decide +kernel
theorem fb_12_12 : one 12 12 = true ∧ gtOne 12 12 = true :=
  both_of_chunks 12 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_12_0
  )
theorem f_12_13_0 : (chunkOf (Low6966Gate.gateList 12 13) 0).all (fF 12 13) = true := by decide +kernel
theorem fb_12_13 : one 12 13 = true ∧ gtOne 12 13 = true :=
  both_of_chunks 12 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_13_0
  )
end Gate6966Fin
