import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_10_7_0 : (chunkOf (Low6966Gate.gateList 10 7) 0).all (fF 10 7) = true := by decide +kernel
theorem fb_10_7 : one 10 7 = true ∧ gtOne 10 7 = true :=
  both_of_chunks 10 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_7_0
  )
theorem f_10_8_0 : (chunkOf (Low6966Gate.gateList 10 8) 0).all (fF 10 8) = true := by decide +kernel
theorem fb_10_8 : one 10 8 = true ∧ gtOne 10 8 = true :=
  both_of_chunks 10 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_8_0
  )
theorem f_10_9_0 : (chunkOf (Low6966Gate.gateList 10 9) 0).all (fF 10 9) = true := by decide +kernel
theorem fb_10_9 : one 10 9 = true ∧ gtOne 10 9 = true :=
  both_of_chunks 10 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_9_0
  )
theorem f_10_10_0 : (chunkOf (Low6966Gate.gateList 10 10) 0).all (fF 10 10) = true := by decide +kernel
theorem fb_10_10 : one 10 10 = true ∧ gtOne 10 10 = true :=
  both_of_chunks 10 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_10_0
  )
theorem f_10_11_0 : (chunkOf (Low6966Gate.gateList 10 11) 0).all (fF 10 11) = true := by decide +kernel
theorem fb_10_11 : one 10 11 = true ∧ gtOne 10 11 = true :=
  both_of_chunks 10 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_11_0
  )
theorem f_10_12_0 : (chunkOf (Low6966Gate.gateList 10 12) 0).all (fF 10 12) = true := by decide +kernel
theorem fb_10_12 : one 10 12 = true ∧ gtOne 10 12 = true :=
  both_of_chunks 10 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_12_0
  )
theorem f_10_13_0 : (chunkOf (Low6966Gate.gateList 10 13) 0).all (fF 10 13) = true := by decide +kernel
theorem fb_10_13 : one 10 13 = true ∧ gtOne 10 13 = true :=
  both_of_chunks 10 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_13_0
  )
theorem f_10_14_0 : (chunkOf (Low6966Gate.gateList 10 14) 0).all (fF 10 14) = true := by decide +kernel
theorem fb_10_14 : one 10 14 = true ∧ gtOne 10 14 = true :=
  both_of_chunks 10 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_14_0
  )
end Gate6966Fin
