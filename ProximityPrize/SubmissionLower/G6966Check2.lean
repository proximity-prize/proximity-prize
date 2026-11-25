import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_2_2_0 : (chunkOf (Low6966Gate.gateList 2 2) 0).all (fF 2 2) = true := by decide +kernel
theorem fb_2_2 : one 2 2 = true ∧ gtOne 2 2 = true :=
  both_of_chunks 2 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_2_0
  )
theorem f_2_3_0 : (chunkOf (Low6966Gate.gateList 2 3) 0).all (fF 2 3) = true := by decide +kernel
theorem fb_2_3 : one 2 3 = true ∧ gtOne 2 3 = true :=
  both_of_chunks 2 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_3_0
  )
theorem f_2_4_0 : (chunkOf (Low6966Gate.gateList 2 4) 0).all (fF 2 4) = true := by decide +kernel
theorem f_2_4_1 : (chunkOf (Low6966Gate.gateList 2 4) 1).all (fF 2 4) = true := by decide +kernel
theorem fb_2_4 : one 2 4 = true ∧ gtOne 2 4 = true :=
  both_of_chunks 2 4 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_4_0
    · exact f_2_4_1
  )
theorem f_2_5_0 : (chunkOf (Low6966Gate.gateList 2 5) 0).all (fF 2 5) = true := by decide +kernel
theorem f_2_5_1 : (chunkOf (Low6966Gate.gateList 2 5) 1).all (fF 2 5) = true := by decide +kernel
theorem f_2_5_2 : (chunkOf (Low6966Gate.gateList 2 5) 2).all (fF 2 5) = true := by decide +kernel
theorem fb_2_5 : one 2 5 = true ∧ gtOne 2 5 = true :=
  both_of_chunks 2 5 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_5_0
    · exact f_2_5_1
    · exact f_2_5_2
  )
theorem f_2_6_0 : (chunkOf (Low6966Gate.gateList 2 6) 0).all (fF 2 6) = true := by decide +kernel
theorem f_2_6_1 : (chunkOf (Low6966Gate.gateList 2 6) 1).all (fF 2 6) = true := by decide +kernel
theorem f_2_6_2 : (chunkOf (Low6966Gate.gateList 2 6) 2).all (fF 2 6) = true := by decide +kernel
theorem fb_2_6 : one 2 6 = true ∧ gtOne 2 6 = true :=
  both_of_chunks 2 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_6_0
    · exact f_2_6_1
    · exact f_2_6_2
  )
theorem f_2_7_0 : (chunkOf (Low6966Gate.gateList 2 7) 0).all (fF 2 7) = true := by decide +kernel
theorem f_2_7_1 : (chunkOf (Low6966Gate.gateList 2 7) 1).all (fF 2 7) = true := by decide +kernel
theorem f_2_7_2 : (chunkOf (Low6966Gate.gateList 2 7) 2).all (fF 2 7) = true := by decide +kernel
theorem f_2_7_3 : (chunkOf (Low6966Gate.gateList 2 7) 3).all (fF 2 7) = true := by decide +kernel
theorem fb_2_7 : one 2 7 = true ∧ gtOne 2 7 = true :=
  both_of_chunks 2 7 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_7_0
    · exact f_2_7_1
    · exact f_2_7_2
    · exact f_2_7_3
  )
theorem f_2_8_0 : (chunkOf (Low6966Gate.gateList 2 8) 0).all (fF 2 8) = true := by decide +kernel
theorem f_2_8_1 : (chunkOf (Low6966Gate.gateList 2 8) 1).all (fF 2 8) = true := by decide +kernel
theorem f_2_8_2 : (chunkOf (Low6966Gate.gateList 2 8) 2).all (fF 2 8) = true := by decide +kernel
theorem f_2_8_3 : (chunkOf (Low6966Gate.gateList 2 8) 3).all (fF 2 8) = true := by decide +kernel
theorem fb_2_8 : one 2 8 = true ∧ gtOne 2 8 = true :=
  both_of_chunks 2 8 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_8_0
    · exact f_2_8_1
    · exact f_2_8_2
    · exact f_2_8_3
  )
theorem f_2_9_0 : (chunkOf (Low6966Gate.gateList 2 9) 0).all (fF 2 9) = true := by decide +kernel
theorem f_2_9_1 : (chunkOf (Low6966Gate.gateList 2 9) 1).all (fF 2 9) = true := by decide +kernel
theorem f_2_9_2 : (chunkOf (Low6966Gate.gateList 2 9) 2).all (fF 2 9) = true := by decide +kernel
theorem f_2_9_3 : (chunkOf (Low6966Gate.gateList 2 9) 3).all (fF 2 9) = true := by decide +kernel
theorem f_2_9_4 : (chunkOf (Low6966Gate.gateList 2 9) 4).all (fF 2 9) = true := by decide +kernel
theorem fb_2_9 : one 2 9 = true ∧ gtOne 2 9 = true :=
  both_of_chunks 2 9 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_9_0
    · exact f_2_9_1
    · exact f_2_9_2
    · exact f_2_9_3
    · exact f_2_9_4
  )
theorem f_2_10_0 : (chunkOf (Low6966Gate.gateList 2 10) 0).all (fF 2 10) = true := by decide +kernel
theorem f_2_10_1 : (chunkOf (Low6966Gate.gateList 2 10) 1).all (fF 2 10) = true := by decide +kernel
theorem f_2_10_2 : (chunkOf (Low6966Gate.gateList 2 10) 2).all (fF 2 10) = true := by decide +kernel
theorem f_2_10_3 : (chunkOf (Low6966Gate.gateList 2 10) 3).all (fF 2 10) = true := by decide +kernel
theorem f_2_10_4 : (chunkOf (Low6966Gate.gateList 2 10) 4).all (fF 2 10) = true := by decide +kernel
theorem fb_2_10 : one 2 10 = true ∧ gtOne 2 10 = true :=
  both_of_chunks 2 10 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_10_0
    · exact f_2_10_1
    · exact f_2_10_2
    · exact f_2_10_3
    · exact f_2_10_4
  )
theorem f_2_11_0 : (chunkOf (Low6966Gate.gateList 2 11) 0).all (fF 2 11) = true := by decide +kernel
theorem f_2_11_1 : (chunkOf (Low6966Gate.gateList 2 11) 1).all (fF 2 11) = true := by decide +kernel
theorem f_2_11_2 : (chunkOf (Low6966Gate.gateList 2 11) 2).all (fF 2 11) = true := by decide +kernel
theorem f_2_11_3 : (chunkOf (Low6966Gate.gateList 2 11) 3).all (fF 2 11) = true := by decide +kernel
theorem f_2_11_4 : (chunkOf (Low6966Gate.gateList 2 11) 4).all (fF 2 11) = true := by decide +kernel
theorem fb_2_11 : one 2 11 = true ∧ gtOne 2 11 = true :=
  both_of_chunks 2 11 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_11_0
    · exact f_2_11_1
    · exact f_2_11_2
    · exact f_2_11_3
    · exact f_2_11_4
  )
theorem f_2_12_0 : (chunkOf (Low6966Gate.gateList 2 12) 0).all (fF 2 12) = true := by decide +kernel
theorem f_2_12_1 : (chunkOf (Low6966Gate.gateList 2 12) 1).all (fF 2 12) = true := by decide +kernel
theorem f_2_12_2 : (chunkOf (Low6966Gate.gateList 2 12) 2).all (fF 2 12) = true := by decide +kernel
theorem f_2_12_3 : (chunkOf (Low6966Gate.gateList 2 12) 3).all (fF 2 12) = true := by decide +kernel
theorem f_2_12_4 : (chunkOf (Low6966Gate.gateList 2 12) 4).all (fF 2 12) = true := by decide +kernel
theorem fb_2_12 : one 2 12 = true ∧ gtOne 2 12 = true :=
  both_of_chunks 2 12 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_12_0
    · exact f_2_12_1
    · exact f_2_12_2
    · exact f_2_12_3
    · exact f_2_12_4
  )
theorem f_2_13_0 : (chunkOf (Low6966Gate.gateList 2 13) 0).all (fF 2 13) = true := by decide +kernel
theorem f_2_13_1 : (chunkOf (Low6966Gate.gateList 2 13) 1).all (fF 2 13) = true := by decide +kernel
theorem f_2_13_2 : (chunkOf (Low6966Gate.gateList 2 13) 2).all (fF 2 13) = true := by decide +kernel
theorem f_2_13_3 : (chunkOf (Low6966Gate.gateList 2 13) 3).all (fF 2 13) = true := by decide +kernel
theorem f_2_13_4 : (chunkOf (Low6966Gate.gateList 2 13) 4).all (fF 2 13) = true := by decide +kernel
theorem fb_2_13 : one 2 13 = true ∧ gtOne 2 13 = true :=
  both_of_chunks 2 13 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_13_0
    · exact f_2_13_1
    · exact f_2_13_2
    · exact f_2_13_3
    · exact f_2_13_4
  )
theorem f_2_14_0 : (chunkOf (Low6966Gate.gateList 2 14) 0).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_1 : (chunkOf (Low6966Gate.gateList 2 14) 1).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_2 : (chunkOf (Low6966Gate.gateList 2 14) 2).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_3 : (chunkOf (Low6966Gate.gateList 2 14) 3).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_4 : (chunkOf (Low6966Gate.gateList 2 14) 4).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_5 : (chunkOf (Low6966Gate.gateList 2 14) 5).all (fF 2 14) = true := by decide +kernel
theorem fb_2_14 : one 2 14 = true ∧ gtOne 2 14 = true :=
  both_of_chunks 2 14 6 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_14_0
    · exact f_2_14_1
    · exact f_2_14_2
    · exact f_2_14_3
    · exact f_2_14_4
    · exact f_2_14_5
  )
end Gate6966Fin
