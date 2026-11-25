import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_7_5_0 : (chunkOf (Low6966Gate.gateList 7 5) 0).all (fF 7 5) = true := by decide +kernel
theorem fb_7_5 : one 7 5 = true ∧ gtOne 7 5 = true :=
  both_of_chunks 7 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_5_0
  )
theorem f_7_6_0 : (chunkOf (Low6966Gate.gateList 7 6) 0).all (fF 7 6) = true := by decide +kernel
theorem fb_7_6 : one 7 6 = true ∧ gtOne 7 6 = true :=
  both_of_chunks 7 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_6_0
  )
theorem f_7_7_0 : (chunkOf (Low6966Gate.gateList 7 7) 0).all (fF 7 7) = true := by decide +kernel
theorem fb_7_7 : one 7 7 = true ∧ gtOne 7 7 = true :=
  both_of_chunks 7 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_7_0
  )
theorem f_7_8_0 : (chunkOf (Low6966Gate.gateList 7 8) 0).all (fF 7 8) = true := by decide +kernel
theorem fb_7_8 : one 7 8 = true ∧ gtOne 7 8 = true :=
  both_of_chunks 7 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_8_0
  )
theorem f_7_9_0 : (chunkOf (Low6966Gate.gateList 7 9) 0).all (fF 7 9) = true := by decide +kernel
theorem fb_7_9 : one 7 9 = true ∧ gtOne 7 9 = true :=
  both_of_chunks 7 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_9_0
  )
theorem f_7_10_0 : (chunkOf (Low6966Gate.gateList 7 10) 0).all (fF 7 10) = true := by decide +kernel
theorem fb_7_10 : one 7 10 = true ∧ gtOne 7 10 = true :=
  both_of_chunks 7 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_10_0
  )
theorem f_7_11_0 : (chunkOf (Low6966Gate.gateList 7 11) 0).all (fF 7 11) = true := by decide +kernel
theorem fb_7_11 : one 7 11 = true ∧ gtOne 7 11 = true :=
  both_of_chunks 7 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_11_0
  )
theorem f_7_12_0 : (chunkOf (Low6966Gate.gateList 7 12) 0).all (fF 7 12) = true := by decide +kernel
theorem fb_7_12 : one 7 12 = true ∧ gtOne 7 12 = true :=
  both_of_chunks 7 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_12_0
  )
theorem f_7_13_0 : (chunkOf (Low6966Gate.gateList 7 13) 0).all (fF 7 13) = true := by decide +kernel
theorem fb_7_13 : one 7 13 = true ∧ gtOne 7 13 = true :=
  both_of_chunks 7 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_13_0
  )
theorem f_7_14_0 : (chunkOf (Low6966Gate.gateList 7 14) 0).all (fF 7 14) = true := by decide +kernel
theorem fb_7_14 : one 7 14 = true ∧ gtOne 7 14 = true :=
  both_of_chunks 7 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_14_0
  )
end Gate6966Fin
