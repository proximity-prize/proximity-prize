import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_6_4_0 : (chunkOf (Low6966Gate.gateList 6 4) 0).all (fF 6 4) = true := by decide +kernel
theorem fb_6_4 : one 6 4 = true ∧ gtOne 6 4 = true :=
  both_of_chunks 6 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_4_0
  )
theorem f_6_5_0 : (chunkOf (Low6966Gate.gateList 6 5) 0).all (fF 6 5) = true := by decide +kernel
theorem fb_6_5 : one 6 5 = true ∧ gtOne 6 5 = true :=
  both_of_chunks 6 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_5_0
  )
theorem f_6_6_0 : (chunkOf (Low6966Gate.gateList 6 6) 0).all (fF 6 6) = true := by decide +kernel
theorem fb_6_6 : one 6 6 = true ∧ gtOne 6 6 = true :=
  both_of_chunks 6 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_6_0
  )
theorem f_6_7_0 : (chunkOf (Low6966Gate.gateList 6 7) 0).all (fF 6 7) = true := by decide +kernel
theorem fb_6_7 : one 6 7 = true ∧ gtOne 6 7 = true :=
  both_of_chunks 6 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_7_0
  )
theorem f_6_8_0 : (chunkOf (Low6966Gate.gateList 6 8) 0).all (fF 6 8) = true := by decide +kernel
theorem fb_6_8 : one 6 8 = true ∧ gtOne 6 8 = true :=
  both_of_chunks 6 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_8_0
  )
theorem f_6_9_0 : (chunkOf (Low6966Gate.gateList 6 9) 0).all (fF 6 9) = true := by decide +kernel
theorem f_6_9_1 : (chunkOf (Low6966Gate.gateList 6 9) 1).all (fF 6 9) = true := by decide +kernel
theorem fb_6_9 : one 6 9 = true ∧ gtOne 6 9 = true :=
  both_of_chunks 6 9 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_9_0
    · exact f_6_9_1
  )
theorem f_6_10_0 : (chunkOf (Low6966Gate.gateList 6 10) 0).all (fF 6 10) = true := by decide +kernel
theorem f_6_10_1 : (chunkOf (Low6966Gate.gateList 6 10) 1).all (fF 6 10) = true := by decide +kernel
theorem fb_6_10 : one 6 10 = true ∧ gtOne 6 10 = true :=
  both_of_chunks 6 10 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_10_0
    · exact f_6_10_1
  )
theorem f_6_11_0 : (chunkOf (Low6966Gate.gateList 6 11) 0).all (fF 6 11) = true := by decide +kernel
theorem f_6_11_1 : (chunkOf (Low6966Gate.gateList 6 11) 1).all (fF 6 11) = true := by decide +kernel
theorem fb_6_11 : one 6 11 = true ∧ gtOne 6 11 = true :=
  both_of_chunks 6 11 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_11_0
    · exact f_6_11_1
  )
theorem f_6_12_0 : (chunkOf (Low6966Gate.gateList 6 12) 0).all (fF 6 12) = true := by decide +kernel
theorem f_6_12_1 : (chunkOf (Low6966Gate.gateList 6 12) 1).all (fF 6 12) = true := by decide +kernel
theorem fb_6_12 : one 6 12 = true ∧ gtOne 6 12 = true :=
  both_of_chunks 6 12 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_12_0
    · exact f_6_12_1
  )
theorem f_6_13_0 : (chunkOf (Low6966Gate.gateList 6 13) 0).all (fF 6 13) = true := by decide +kernel
theorem f_6_13_1 : (chunkOf (Low6966Gate.gateList 6 13) 1).all (fF 6 13) = true := by decide +kernel
theorem fb_6_13 : one 6 13 = true ∧ gtOne 6 13 = true :=
  both_of_chunks 6 13 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_13_0
    · exact f_6_13_1
  )
theorem f_6_14_0 : (chunkOf (Low6966Gate.gateList 6 14) 0).all (fF 6 14) = true := by decide +kernel
theorem f_6_14_1 : (chunkOf (Low6966Gate.gateList 6 14) 1).all (fF 6 14) = true := by decide +kernel
theorem fb_6_14 : one 6 14 = true ∧ gtOne 6 14 = true :=
  both_of_chunks 6 14 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_14_0
    · exact f_6_14_1
  )
end Gate6966Fin
