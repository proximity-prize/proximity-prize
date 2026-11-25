import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_1_2_0 : (chunkOf (Low6966Gate.gateList 1 2) 0).all (fF 1 2) = true := by decide +kernel
theorem fb_1_2 : one 1 2 = true ∧ gtOne 1 2 = true :=
  both_of_chunks 1 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_2_0
  )
theorem f_1_3_0 : (chunkOf (Low6966Gate.gateList 1 3) 0).all (fF 1 3) = true := by decide +kernel
theorem f_1_3_1 : (chunkOf (Low6966Gate.gateList 1 3) 1).all (fF 1 3) = true := by decide +kernel
theorem fb_1_3 : one 1 3 = true ∧ gtOne 1 3 = true :=
  both_of_chunks 1 3 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_3_0
    · exact f_1_3_1
  )
theorem f_1_4_0 : (chunkOf (Low6966Gate.gateList 1 4) 0).all (fF 1 4) = true := by decide +kernel
theorem f_1_4_1 : (chunkOf (Low6966Gate.gateList 1 4) 1).all (fF 1 4) = true := by decide +kernel
theorem fb_1_4 : one 1 4 = true ∧ gtOne 1 4 = true :=
  both_of_chunks 1 4 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_4_0
    · exact f_1_4_1
  )
theorem f_1_5_0 : (chunkOf (Low6966Gate.gateList 1 5) 0).all (fF 1 5) = true := by decide +kernel
theorem f_1_5_1 : (chunkOf (Low6966Gate.gateList 1 5) 1).all (fF 1 5) = true := by decide +kernel
theorem f_1_5_2 : (chunkOf (Low6966Gate.gateList 1 5) 2).all (fF 1 5) = true := by decide +kernel
theorem fb_1_5 : one 1 5 = true ∧ gtOne 1 5 = true :=
  both_of_chunks 1 5 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_5_0
    · exact f_1_5_1
    · exact f_1_5_2
  )
theorem f_1_6_0 : (chunkOf (Low6966Gate.gateList 1 6) 0).all (fF 1 6) = true := by decide +kernel
theorem f_1_6_1 : (chunkOf (Low6966Gate.gateList 1 6) 1).all (fF 1 6) = true := by decide +kernel
theorem f_1_6_2 : (chunkOf (Low6966Gate.gateList 1 6) 2).all (fF 1 6) = true := by decide +kernel
theorem fb_1_6 : one 1 6 = true ∧ gtOne 1 6 = true :=
  both_of_chunks 1 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_6_0
    · exact f_1_6_1
    · exact f_1_6_2
  )
theorem f_1_7_0 : (chunkOf (Low6966Gate.gateList 1 7) 0).all (fF 1 7) = true := by decide +kernel
theorem f_1_7_1 : (chunkOf (Low6966Gate.gateList 1 7) 1).all (fF 1 7) = true := by decide +kernel
theorem f_1_7_2 : (chunkOf (Low6966Gate.gateList 1 7) 2).all (fF 1 7) = true := by decide +kernel
theorem f_1_7_3 : (chunkOf (Low6966Gate.gateList 1 7) 3).all (fF 1 7) = true := by decide +kernel
theorem fb_1_7 : one 1 7 = true ∧ gtOne 1 7 = true :=
  both_of_chunks 1 7 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_7_0
    · exact f_1_7_1
    · exact f_1_7_2
    · exact f_1_7_3
  )
theorem f_1_8_0 : (chunkOf (Low6966Gate.gateList 1 8) 0).all (fF 1 8) = true := by decide +kernel
theorem f_1_8_1 : (chunkOf (Low6966Gate.gateList 1 8) 1).all (fF 1 8) = true := by decide +kernel
theorem f_1_8_2 : (chunkOf (Low6966Gate.gateList 1 8) 2).all (fF 1 8) = true := by decide +kernel
theorem f_1_8_3 : (chunkOf (Low6966Gate.gateList 1 8) 3).all (fF 1 8) = true := by decide +kernel
theorem fb_1_8 : one 1 8 = true ∧ gtOne 1 8 = true :=
  both_of_chunks 1 8 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_8_0
    · exact f_1_8_1
    · exact f_1_8_2
    · exact f_1_8_3
  )
theorem f_1_9_0 : (chunkOf (Low6966Gate.gateList 1 9) 0).all (fF 1 9) = true := by decide +kernel
theorem f_1_9_1 : (chunkOf (Low6966Gate.gateList 1 9) 1).all (fF 1 9) = true := by decide +kernel
theorem f_1_9_2 : (chunkOf (Low6966Gate.gateList 1 9) 2).all (fF 1 9) = true := by decide +kernel
theorem f_1_9_3 : (chunkOf (Low6966Gate.gateList 1 9) 3).all (fF 1 9) = true := by decide +kernel
theorem fb_1_9 : one 1 9 = true ∧ gtOne 1 9 = true :=
  both_of_chunks 1 9 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_9_0
    · exact f_1_9_1
    · exact f_1_9_2
    · exact f_1_9_3
  )
theorem f_1_10_0 : (chunkOf (Low6966Gate.gateList 1 10) 0).all (fF 1 10) = true := by decide +kernel
theorem f_1_10_1 : (chunkOf (Low6966Gate.gateList 1 10) 1).all (fF 1 10) = true := by decide +kernel
theorem f_1_10_2 : (chunkOf (Low6966Gate.gateList 1 10) 2).all (fF 1 10) = true := by decide +kernel
theorem f_1_10_3 : (chunkOf (Low6966Gate.gateList 1 10) 3).all (fF 1 10) = true := by decide +kernel
theorem f_1_10_4 : (chunkOf (Low6966Gate.gateList 1 10) 4).all (fF 1 10) = true := by decide +kernel
theorem fb_1_10 : one 1 10 = true ∧ gtOne 1 10 = true :=
  both_of_chunks 1 10 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_10_0
    · exact f_1_10_1
    · exact f_1_10_2
    · exact f_1_10_3
    · exact f_1_10_4
  )
theorem f_1_11_0 : (chunkOf (Low6966Gate.gateList 1 11) 0).all (fF 1 11) = true := by decide +kernel
theorem f_1_11_1 : (chunkOf (Low6966Gate.gateList 1 11) 1).all (fF 1 11) = true := by decide +kernel
theorem f_1_11_2 : (chunkOf (Low6966Gate.gateList 1 11) 2).all (fF 1 11) = true := by decide +kernel
theorem f_1_11_3 : (chunkOf (Low6966Gate.gateList 1 11) 3).all (fF 1 11) = true := by decide +kernel
theorem f_1_11_4 : (chunkOf (Low6966Gate.gateList 1 11) 4).all (fF 1 11) = true := by decide +kernel
theorem fb_1_11 : one 1 11 = true ∧ gtOne 1 11 = true :=
  both_of_chunks 1 11 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_11_0
    · exact f_1_11_1
    · exact f_1_11_2
    · exact f_1_11_3
    · exact f_1_11_4
  )
theorem f_1_12_0 : (chunkOf (Low6966Gate.gateList 1 12) 0).all (fF 1 12) = true := by decide +kernel
theorem f_1_12_1 : (chunkOf (Low6966Gate.gateList 1 12) 1).all (fF 1 12) = true := by decide +kernel
theorem f_1_12_2 : (chunkOf (Low6966Gate.gateList 1 12) 2).all (fF 1 12) = true := by decide +kernel
theorem f_1_12_3 : (chunkOf (Low6966Gate.gateList 1 12) 3).all (fF 1 12) = true := by decide +kernel
theorem f_1_12_4 : (chunkOf (Low6966Gate.gateList 1 12) 4).all (fF 1 12) = true := by decide +kernel
theorem fb_1_12 : one 1 12 = true ∧ gtOne 1 12 = true :=
  both_of_chunks 1 12 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_12_0
    · exact f_1_12_1
    · exact f_1_12_2
    · exact f_1_12_3
    · exact f_1_12_4
  )
theorem f_1_13_0 : (chunkOf (Low6966Gate.gateList 1 13) 0).all (fF 1 13) = true := by decide +kernel
theorem f_1_13_1 : (chunkOf (Low6966Gate.gateList 1 13) 1).all (fF 1 13) = true := by decide +kernel
theorem f_1_13_2 : (chunkOf (Low6966Gate.gateList 1 13) 2).all (fF 1 13) = true := by decide +kernel
theorem f_1_13_3 : (chunkOf (Low6966Gate.gateList 1 13) 3).all (fF 1 13) = true := by decide +kernel
theorem f_1_13_4 : (chunkOf (Low6966Gate.gateList 1 13) 4).all (fF 1 13) = true := by decide +kernel
theorem fb_1_13 : one 1 13 = true ∧ gtOne 1 13 = true :=
  both_of_chunks 1 13 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_13_0
    · exact f_1_13_1
    · exact f_1_13_2
    · exact f_1_13_3
    · exact f_1_13_4
  )
theorem f_1_14_0 : (chunkOf (Low6966Gate.gateList 1 14) 0).all (fF 1 14) = true := by decide +kernel
theorem f_1_14_1 : (chunkOf (Low6966Gate.gateList 1 14) 1).all (fF 1 14) = true := by decide +kernel
theorem f_1_14_2 : (chunkOf (Low6966Gate.gateList 1 14) 2).all (fF 1 14) = true := by decide +kernel
theorem f_1_14_3 : (chunkOf (Low6966Gate.gateList 1 14) 3).all (fF 1 14) = true := by decide +kernel
theorem f_1_14_4 : (chunkOf (Low6966Gate.gateList 1 14) 4).all (fF 1 14) = true := by decide +kernel
theorem fb_1_14 : one 1 14 = true ∧ gtOne 1 14 = true :=
  both_of_chunks 1 14 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_14_0
    · exact f_1_14_1
    · exact f_1_14_2
    · exact f_1_14_3
    · exact f_1_14_4
  )
end Gate6966Fin
