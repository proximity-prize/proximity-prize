import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_11_9_0 : (chunkOf (Low6966Gate.gateList 11 9) 0).all (fF 11 9) = true := by decide +kernel
theorem fb_11_9 : one 11 9 = true ∧ gtOne 11 9 = true :=
  both_of_chunks 11 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_9_0
  )
theorem f_11_10_0 : (chunkOf (Low6966Gate.gateList 11 10) 0).all (fF 11 10) = true := by decide +kernel
theorem fb_11_10 : one 11 10 = true ∧ gtOne 11 10 = true :=
  both_of_chunks 11 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_10_0
  )
theorem f_11_11_0 : (chunkOf (Low6966Gate.gateList 11 11) 0).all (fF 11 11) = true := by decide +kernel
theorem fb_11_11 : one 11 11 = true ∧ gtOne 11 11 = true :=
  both_of_chunks 11 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_11_0
  )
theorem f_11_12_0 : (chunkOf (Low6966Gate.gateList 11 12) 0).all (fF 11 12) = true := by decide +kernel
theorem fb_11_12 : one 11 12 = true ∧ gtOne 11 12 = true :=
  both_of_chunks 11 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_12_0
  )
theorem f_11_13_0 : (chunkOf (Low6966Gate.gateList 11 13) 0).all (fF 11 13) = true := by decide +kernel
theorem fb_11_13 : one 11 13 = true ∧ gtOne 11 13 = true :=
  both_of_chunks 11 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_13_0
  )
theorem f_11_14_0 : (chunkOf (Low6966Gate.gateList 11 14) 0).all (fF 11 14) = true := by decide +kernel
theorem fb_11_14 : one 11 14 = true ∧ gtOne 11 14 = true :=
  both_of_chunks 11 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_14_0
  )
end Gate6966Fin
