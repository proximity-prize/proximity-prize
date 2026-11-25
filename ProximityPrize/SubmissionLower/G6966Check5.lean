import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_5_3_0 : (chunkOf (Low6966Gate.gateList 5 3) 0).all (fF 5 3) = true := by decide +kernel
theorem fb_5_3 : one 5 3 = true ∧ gtOne 5 3 = true :=
  both_of_chunks 5 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_3_0
  )
theorem f_5_4_0 : (chunkOf (Low6966Gate.gateList 5 4) 0).all (fF 5 4) = true := by decide +kernel
theorem fb_5_4 : one 5 4 = true ∧ gtOne 5 4 = true :=
  both_of_chunks 5 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_4_0
  )
theorem f_5_5_0 : (chunkOf (Low6966Gate.gateList 5 5) 0).all (fF 5 5) = true := by decide +kernel
theorem fb_5_5 : one 5 5 = true ∧ gtOne 5 5 = true :=
  both_of_chunks 5 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_5_0
  )
theorem f_5_6_0 : (chunkOf (Low6966Gate.gateList 5 6) 0).all (fF 5 6) = true := by decide +kernel
theorem fb_5_6 : one 5 6 = true ∧ gtOne 5 6 = true :=
  both_of_chunks 5 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_6_0
  )
theorem f_5_7_0 : (chunkOf (Low6966Gate.gateList 5 7) 0).all (fF 5 7) = true := by decide +kernel
theorem f_5_7_1 : (chunkOf (Low6966Gate.gateList 5 7) 1).all (fF 5 7) = true := by decide +kernel
theorem fb_5_7 : one 5 7 = true ∧ gtOne 5 7 = true :=
  both_of_chunks 5 7 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_7_0
    · exact f_5_7_1
  )
theorem f_5_8_0 : (chunkOf (Low6966Gate.gateList 5 8) 0).all (fF 5 8) = true := by decide +kernel
theorem f_5_8_1 : (chunkOf (Low6966Gate.gateList 5 8) 1).all (fF 5 8) = true := by decide +kernel
theorem fb_5_8 : one 5 8 = true ∧ gtOne 5 8 = true :=
  both_of_chunks 5 8 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_8_0
    · exact f_5_8_1
  )
theorem f_5_9_0 : (chunkOf (Low6966Gate.gateList 5 9) 0).all (fF 5 9) = true := by decide +kernel
theorem f_5_9_1 : (chunkOf (Low6966Gate.gateList 5 9) 1).all (fF 5 9) = true := by decide +kernel
theorem fb_5_9 : one 5 9 = true ∧ gtOne 5 9 = true :=
  both_of_chunks 5 9 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_9_0
    · exact f_5_9_1
  )
theorem f_5_10_0 : (chunkOf (Low6966Gate.gateList 5 10) 0).all (fF 5 10) = true := by decide +kernel
theorem f_5_10_1 : (chunkOf (Low6966Gate.gateList 5 10) 1).all (fF 5 10) = true := by decide +kernel
theorem fb_5_10 : one 5 10 = true ∧ gtOne 5 10 = true :=
  both_of_chunks 5 10 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_10_0
    · exact f_5_10_1
  )
theorem f_5_11_0 : (chunkOf (Low6966Gate.gateList 5 11) 0).all (fF 5 11) = true := by decide +kernel
theorem f_5_11_1 : (chunkOf (Low6966Gate.gateList 5 11) 1).all (fF 5 11) = true := by decide +kernel
theorem fb_5_11 : one 5 11 = true ∧ gtOne 5 11 = true :=
  both_of_chunks 5 11 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_11_0
    · exact f_5_11_1
  )
theorem f_5_12_0 : (chunkOf (Low6966Gate.gateList 5 12) 0).all (fF 5 12) = true := by decide +kernel
theorem f_5_12_1 : (chunkOf (Low6966Gate.gateList 5 12) 1).all (fF 5 12) = true := by decide +kernel
theorem fb_5_12 : one 5 12 = true ∧ gtOne 5 12 = true :=
  both_of_chunks 5 12 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_12_0
    · exact f_5_12_1
  )
theorem f_5_13_0 : (chunkOf (Low6966Gate.gateList 5 13) 0).all (fF 5 13) = true := by decide +kernel
theorem f_5_13_1 : (chunkOf (Low6966Gate.gateList 5 13) 1).all (fF 5 13) = true := by decide +kernel
theorem fb_5_13 : one 5 13 = true ∧ gtOne 5 13 = true :=
  both_of_chunks 5 13 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_13_0
    · exact f_5_13_1
  )
theorem f_5_14_0 : (chunkOf (Low6966Gate.gateList 5 14) 0).all (fF 5 14) = true := by decide +kernel
theorem f_5_14_1 : (chunkOf (Low6966Gate.gateList 5 14) 1).all (fF 5 14) = true := by decide +kernel
theorem f_5_14_2 : (chunkOf (Low6966Gate.gateList 5 14) 2).all (fF 5 14) = true := by decide +kernel
theorem fb_5_14 : one 5 14 = true ∧ gtOne 5 14 = true :=
  both_of_chunks 5 14 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_14_0
    · exact f_5_14_1
    · exact f_5_14_2
  )
end Gate6966Fin
