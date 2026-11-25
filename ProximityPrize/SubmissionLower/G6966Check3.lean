import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_3_2_0 : (chunkOf (Low6966Gate.gateList 3 2) 0).all (fF 3 2) = true := by decide +kernel
theorem fb_3_2 : one 3 2 = true ∧ gtOne 3 2 = true :=
  both_of_chunks 3 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_2_0
  )
theorem f_3_3_0 : (chunkOf (Low6966Gate.gateList 3 3) 0).all (fF 3 3) = true := by decide +kernel
theorem fb_3_3 : one 3 3 = true ∧ gtOne 3 3 = true :=
  both_of_chunks 3 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_3_0
  )
theorem f_3_4_0 : (chunkOf (Low6966Gate.gateList 3 4) 0).all (fF 3 4) = true := by decide +kernel
theorem f_3_4_1 : (chunkOf (Low6966Gate.gateList 3 4) 1).all (fF 3 4) = true := by decide +kernel
theorem fb_3_4 : one 3 4 = true ∧ gtOne 3 4 = true :=
  both_of_chunks 3 4 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_4_0
    · exact f_3_4_1
  )
theorem f_3_5_0 : (chunkOf (Low6966Gate.gateList 3 5) 0).all (fF 3 5) = true := by decide +kernel
theorem f_3_5_1 : (chunkOf (Low6966Gate.gateList 3 5) 1).all (fF 3 5) = true := by decide +kernel
theorem fb_3_5 : one 3 5 = true ∧ gtOne 3 5 = true :=
  both_of_chunks 3 5 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_5_0
    · exact f_3_5_1
  )
theorem f_3_6_0 : (chunkOf (Low6966Gate.gateList 3 6) 0).all (fF 3 6) = true := by decide +kernel
theorem f_3_6_1 : (chunkOf (Low6966Gate.gateList 3 6) 1).all (fF 3 6) = true := by decide +kernel
theorem f_3_6_2 : (chunkOf (Low6966Gate.gateList 3 6) 2).all (fF 3 6) = true := by decide +kernel
theorem fb_3_6 : one 3 6 = true ∧ gtOne 3 6 = true :=
  both_of_chunks 3 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_6_0
    · exact f_3_6_1
    · exact f_3_6_2
  )
theorem f_3_7_0 : (chunkOf (Low6966Gate.gateList 3 7) 0).all (fF 3 7) = true := by decide +kernel
theorem f_3_7_1 : (chunkOf (Low6966Gate.gateList 3 7) 1).all (fF 3 7) = true := by decide +kernel
theorem f_3_7_2 : (chunkOf (Low6966Gate.gateList 3 7) 2).all (fF 3 7) = true := by decide +kernel
theorem fb_3_7 : one 3 7 = true ∧ gtOne 3 7 = true :=
  both_of_chunks 3 7 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_7_0
    · exact f_3_7_1
    · exact f_3_7_2
  )
theorem f_3_8_0 : (chunkOf (Low6966Gate.gateList 3 8) 0).all (fF 3 8) = true := by decide +kernel
theorem f_3_8_1 : (chunkOf (Low6966Gate.gateList 3 8) 1).all (fF 3 8) = true := by decide +kernel
theorem f_3_8_2 : (chunkOf (Low6966Gate.gateList 3 8) 2).all (fF 3 8) = true := by decide +kernel
theorem fb_3_8 : one 3 8 = true ∧ gtOne 3 8 = true :=
  both_of_chunks 3 8 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_8_0
    · exact f_3_8_1
    · exact f_3_8_2
  )
theorem f_3_9_0 : (chunkOf (Low6966Gate.gateList 3 9) 0).all (fF 3 9) = true := by decide +kernel
theorem f_3_9_1 : (chunkOf (Low6966Gate.gateList 3 9) 1).all (fF 3 9) = true := by decide +kernel
theorem f_3_9_2 : (chunkOf (Low6966Gate.gateList 3 9) 2).all (fF 3 9) = true := by decide +kernel
theorem fb_3_9 : one 3 9 = true ∧ gtOne 3 9 = true :=
  both_of_chunks 3 9 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_9_0
    · exact f_3_9_1
    · exact f_3_9_2
  )
theorem f_3_10_0 : (chunkOf (Low6966Gate.gateList 3 10) 0).all (fF 3 10) = true := by decide +kernel
theorem f_3_10_1 : (chunkOf (Low6966Gate.gateList 3 10) 1).all (fF 3 10) = true := by decide +kernel
theorem f_3_10_2 : (chunkOf (Low6966Gate.gateList 3 10) 2).all (fF 3 10) = true := by decide +kernel
theorem f_3_10_3 : (chunkOf (Low6966Gate.gateList 3 10) 3).all (fF 3 10) = true := by decide +kernel
theorem fb_3_10 : one 3 10 = true ∧ gtOne 3 10 = true :=
  both_of_chunks 3 10 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_10_0
    · exact f_3_10_1
    · exact f_3_10_2
    · exact f_3_10_3
  )
theorem f_3_11_0 : (chunkOf (Low6966Gate.gateList 3 11) 0).all (fF 3 11) = true := by decide +kernel
theorem f_3_11_1 : (chunkOf (Low6966Gate.gateList 3 11) 1).all (fF 3 11) = true := by decide +kernel
theorem f_3_11_2 : (chunkOf (Low6966Gate.gateList 3 11) 2).all (fF 3 11) = true := by decide +kernel
theorem f_3_11_3 : (chunkOf (Low6966Gate.gateList 3 11) 3).all (fF 3 11) = true := by decide +kernel
theorem fb_3_11 : one 3 11 = true ∧ gtOne 3 11 = true :=
  both_of_chunks 3 11 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_11_0
    · exact f_3_11_1
    · exact f_3_11_2
    · exact f_3_11_3
  )
theorem f_3_12_0 : (chunkOf (Low6966Gate.gateList 3 12) 0).all (fF 3 12) = true := by decide +kernel
theorem f_3_12_1 : (chunkOf (Low6966Gate.gateList 3 12) 1).all (fF 3 12) = true := by decide +kernel
theorem f_3_12_2 : (chunkOf (Low6966Gate.gateList 3 12) 2).all (fF 3 12) = true := by decide +kernel
theorem f_3_12_3 : (chunkOf (Low6966Gate.gateList 3 12) 3).all (fF 3 12) = true := by decide +kernel
theorem fb_3_12 : one 3 12 = true ∧ gtOne 3 12 = true :=
  both_of_chunks 3 12 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_12_0
    · exact f_3_12_1
    · exact f_3_12_2
    · exact f_3_12_3
  )
theorem f_3_13_0 : (chunkOf (Low6966Gate.gateList 3 13) 0).all (fF 3 13) = true := by decide +kernel
theorem f_3_13_1 : (chunkOf (Low6966Gate.gateList 3 13) 1).all (fF 3 13) = true := by decide +kernel
theorem f_3_13_2 : (chunkOf (Low6966Gate.gateList 3 13) 2).all (fF 3 13) = true := by decide +kernel
theorem f_3_13_3 : (chunkOf (Low6966Gate.gateList 3 13) 3).all (fF 3 13) = true := by decide +kernel
theorem fb_3_13 : one 3 13 = true ∧ gtOne 3 13 = true :=
  both_of_chunks 3 13 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_13_0
    · exact f_3_13_1
    · exact f_3_13_2
    · exact f_3_13_3
  )
theorem f_3_14_0 : (chunkOf (Low6966Gate.gateList 3 14) 0).all (fF 3 14) = true := by decide +kernel
theorem f_3_14_1 : (chunkOf (Low6966Gate.gateList 3 14) 1).all (fF 3 14) = true := by decide +kernel
theorem f_3_14_2 : (chunkOf (Low6966Gate.gateList 3 14) 2).all (fF 3 14) = true := by decide +kernel
theorem f_3_14_3 : (chunkOf (Low6966Gate.gateList 3 14) 3).all (fF 3 14) = true := by decide +kernel
theorem fb_3_14 : one 3 14 = true ∧ gtOne 3 14 = true :=
  both_of_chunks 3 14 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_14_0
    · exact f_3_14_1
    · exact f_3_14_2
    · exact f_3_14_3
  )
end Gate6966Fin
