import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_4_3_0 : (chunkOf (Low6966Gate.gateList 4 3) 0).all (fF 4 3) = true := by decide +kernel
theorem fb_4_3 : one 4 3 = true ∧ gtOne 4 3 = true :=
  both_of_chunks 4 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_3_0
  )
theorem f_4_4_0 : (chunkOf (Low6966Gate.gateList 4 4) 0).all (fF 4 4) = true := by decide +kernel
theorem fb_4_4 : one 4 4 = true ∧ gtOne 4 4 = true :=
  both_of_chunks 4 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_4_0
  )
theorem f_4_5_0 : (chunkOf (Low6966Gate.gateList 4 5) 0).all (fF 4 5) = true := by decide +kernel
theorem fb_4_5 : one 4 5 = true ∧ gtOne 4 5 = true :=
  both_of_chunks 4 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_5_0
  )
theorem f_4_6_0 : (chunkOf (Low6966Gate.gateList 4 6) 0).all (fF 4 6) = true := by decide +kernel
theorem f_4_6_1 : (chunkOf (Low6966Gate.gateList 4 6) 1).all (fF 4 6) = true := by decide +kernel
theorem fb_4_6 : one 4 6 = true ∧ gtOne 4 6 = true :=
  both_of_chunks 4 6 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_6_0
    · exact f_4_6_1
  )
theorem f_4_7_0 : (chunkOf (Low6966Gate.gateList 4 7) 0).all (fF 4 7) = true := by decide +kernel
theorem f_4_7_1 : (chunkOf (Low6966Gate.gateList 4 7) 1).all (fF 4 7) = true := by decide +kernel
theorem fb_4_7 : one 4 7 = true ∧ gtOne 4 7 = true :=
  both_of_chunks 4 7 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_7_0
    · exact f_4_7_1
  )
theorem f_4_8_0 : (chunkOf (Low6966Gate.gateList 4 8) 0).all (fF 4 8) = true := by decide +kernel
theorem f_4_8_1 : (chunkOf (Low6966Gate.gateList 4 8) 1).all (fF 4 8) = true := by decide +kernel
theorem fb_4_8 : one 4 8 = true ∧ gtOne 4 8 = true :=
  both_of_chunks 4 8 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_8_0
    · exact f_4_8_1
  )
theorem f_4_9_0 : (chunkOf (Low6966Gate.gateList 4 9) 0).all (fF 4 9) = true := by decide +kernel
theorem f_4_9_1 : (chunkOf (Low6966Gate.gateList 4 9) 1).all (fF 4 9) = true := by decide +kernel
theorem f_4_9_2 : (chunkOf (Low6966Gate.gateList 4 9) 2).all (fF 4 9) = true := by decide +kernel
theorem fb_4_9 : one 4 9 = true ∧ gtOne 4 9 = true :=
  both_of_chunks 4 9 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_9_0
    · exact f_4_9_1
    · exact f_4_9_2
  )
theorem f_4_10_0 : (chunkOf (Low6966Gate.gateList 4 10) 0).all (fF 4 10) = true := by decide +kernel
theorem f_4_10_1 : (chunkOf (Low6966Gate.gateList 4 10) 1).all (fF 4 10) = true := by decide +kernel
theorem f_4_10_2 : (chunkOf (Low6966Gate.gateList 4 10) 2).all (fF 4 10) = true := by decide +kernel
theorem fb_4_10 : one 4 10 = true ∧ gtOne 4 10 = true :=
  both_of_chunks 4 10 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_10_0
    · exact f_4_10_1
    · exact f_4_10_2
  )
theorem f_4_11_0 : (chunkOf (Low6966Gate.gateList 4 11) 0).all (fF 4 11) = true := by decide +kernel
theorem f_4_11_1 : (chunkOf (Low6966Gate.gateList 4 11) 1).all (fF 4 11) = true := by decide +kernel
theorem f_4_11_2 : (chunkOf (Low6966Gate.gateList 4 11) 2).all (fF 4 11) = true := by decide +kernel
theorem fb_4_11 : one 4 11 = true ∧ gtOne 4 11 = true :=
  both_of_chunks 4 11 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_11_0
    · exact f_4_11_1
    · exact f_4_11_2
  )
theorem f_4_12_0 : (chunkOf (Low6966Gate.gateList 4 12) 0).all (fF 4 12) = true := by decide +kernel
theorem f_4_12_1 : (chunkOf (Low6966Gate.gateList 4 12) 1).all (fF 4 12) = true := by decide +kernel
theorem f_4_12_2 : (chunkOf (Low6966Gate.gateList 4 12) 2).all (fF 4 12) = true := by decide +kernel
theorem fb_4_12 : one 4 12 = true ∧ gtOne 4 12 = true :=
  both_of_chunks 4 12 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_12_0
    · exact f_4_12_1
    · exact f_4_12_2
  )
theorem f_4_13_0 : (chunkOf (Low6966Gate.gateList 4 13) 0).all (fF 4 13) = true := by decide +kernel
theorem f_4_13_1 : (chunkOf (Low6966Gate.gateList 4 13) 1).all (fF 4 13) = true := by decide +kernel
theorem f_4_13_2 : (chunkOf (Low6966Gate.gateList 4 13) 2).all (fF 4 13) = true := by decide +kernel
theorem fb_4_13 : one 4 13 = true ∧ gtOne 4 13 = true :=
  both_of_chunks 4 13 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_13_0
    · exact f_4_13_1
    · exact f_4_13_2
  )
theorem f_4_14_0 : (chunkOf (Low6966Gate.gateList 4 14) 0).all (fF 4 14) = true := by decide +kernel
theorem f_4_14_1 : (chunkOf (Low6966Gate.gateList 4 14) 1).all (fF 4 14) = true := by decide +kernel
theorem f_4_14_2 : (chunkOf (Low6966Gate.gateList 4 14) 2).all (fF 4 14) = true := by decide +kernel
theorem fb_4_14 : one 4 14 = true ∧ gtOne 4 14 = true :=
  both_of_chunks 4 14 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_14_0
    · exact f_4_14_1
    · exact f_4_14_2
  )
end Gate6966Fin
