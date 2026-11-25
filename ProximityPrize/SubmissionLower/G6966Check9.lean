import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_9_10_0 : (chunkOf (Low6966Gate.gateList 9 10) 0).all (fF 9 10) = true := by decide +kernel
theorem fb_9_10 : one 9 10 = true ∧ gtOne 9 10 = true :=
  both_of_chunks 9 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_10_0
  )
theorem f_9_11_0 : (chunkOf (Low6966Gate.gateList 9 11) 0).all (fF 9 11) = true := by decide +kernel
theorem fb_9_11 : one 9 11 = true ∧ gtOne 9 11 = true :=
  both_of_chunks 9 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_11_0
  )
theorem f_9_12_0 : (chunkOf (Low6966Gate.gateList 9 12) 0).all (fF 9 12) = true := by decide +kernel
theorem fb_9_12 : one 9 12 = true ∧ gtOne 9 12 = true :=
  both_of_chunks 9 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_12_0
  )
theorem f_9_13_0 : (chunkOf (Low6966Gate.gateList 9 13) 0).all (fF 9 13) = true := by decide +kernel
theorem fb_9_13 : one 9 13 = true ∧ gtOne 9 13 = true :=
  both_of_chunks 9 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_13_0
  )
theorem f_9_14_0 : (chunkOf (Low6966Gate.gateList 9 14) 0).all (fF 9 14) = true := by decide +kernel
theorem fb_9_14 : one 9 14 = true ∧ gtOne 9 14 = true :=
  both_of_chunks 9 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_14_0
  )
end Gate6966Fin
