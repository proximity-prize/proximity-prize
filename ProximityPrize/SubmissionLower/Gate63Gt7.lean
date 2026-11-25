import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_1_12_0 : (chunkOf (Low6960Gate.gateList 1 12) 0).all (fF 1 12) = true := by decide +kernel
theorem f_1_12_1 : (chunkOf (Low6960Gate.gateList 1 12) 1).all (fF 1 12) = true := by decide +kernel
theorem fb_1_12 : one 1 12 = true ∧ gtOne 1 12 = true :=
  both_of_chunks 1 12 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_12_0
    · exact f_1_12_1
  )
theorem c_1_12 : one 1 12 = true := fb_1_12.1
theorem g_1_12 : gtOne 1 12 = true := fb_1_12.2

theorem f_1_13_0 : (chunkOf (Low6960Gate.gateList 1 13) 0).all (fF 1 13) = true := by decide +kernel
theorem f_1_13_1 : (chunkOf (Low6960Gate.gateList 1 13) 1).all (fF 1 13) = true := by decide +kernel
theorem fb_1_13 : one 1 13 = true ∧ gtOne 1 13 = true :=
  both_of_chunks 1 13 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_13_0
    · exact f_1_13_1
  )
theorem c_1_13 : one 1 13 = true := fb_1_13.1
theorem g_1_13 : gtOne 1 13 = true := fb_1_13.2

theorem f_2_2_0 : (chunkOf (Low6960Gate.gateList 2 2) 0).all (fF 2 2) = true := by decide +kernel
theorem fb_2_2 : one 2 2 = true ∧ gtOne 2 2 = true :=
  both_of_chunks 2 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_2_0
  )
theorem c_2_2 : one 2 2 = true := fb_2_2.1
theorem g_2_2 : gtOne 2 2 = true := fb_2_2.2

theorem f_2_3_0 : (chunkOf (Low6960Gate.gateList 2 3) 0).all (fF 2 3) = true := by decide +kernel
theorem fb_2_3 : one 2 3 = true ∧ gtOne 2 3 = true :=
  both_of_chunks 2 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_3_0
  )
theorem c_2_3 : one 2 3 = true := fb_2_3.1
theorem g_2_3 : gtOne 2 3 = true := fb_2_3.2

theorem f_2_4_0 : (chunkOf (Low6960Gate.gateList 2 4) 0).all (fF 2 4) = true := by decide +kernel
theorem fb_2_4 : one 2 4 = true ∧ gtOne 2 4 = true :=
  both_of_chunks 2 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_4_0
  )
theorem c_2_4 : one 2 4 = true := fb_2_4.1
theorem g_2_4 : gtOne 2 4 = true := fb_2_4.2

theorem f_2_5_0 : (chunkOf (Low6960Gate.gateList 2 5) 0).all (fF 2 5) = true := by decide +kernel
theorem fb_2_5 : one 2 5 = true ∧ gtOne 2 5 = true :=
  both_of_chunks 2 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_5_0
  )
theorem c_2_5 : one 2 5 = true := fb_2_5.1
theorem g_2_5 : gtOne 2 5 = true := fb_2_5.2

theorem f_2_6_0 : (chunkOf (Low6960Gate.gateList 2 6) 0).all (fF 2 6) = true := by decide +kernel
theorem fb_2_6 : one 2 6 = true ∧ gtOne 2 6 = true :=
  both_of_chunks 2 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_6_0
  )
theorem c_2_6 : one 2 6 = true := fb_2_6.1
theorem g_2_6 : gtOne 2 6 = true := fb_2_6.2

theorem f_2_7_0 : (chunkOf (Low6960Gate.gateList 2 7) 0).all (fF 2 7) = true := by decide +kernel
theorem fb_2_7 : one 2 7 = true ∧ gtOne 2 7 = true :=
  both_of_chunks 2 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_7_0
  )
theorem c_2_7 : one 2 7 = true := fb_2_7.1
theorem g_2_7 : gtOne 2 7 = true := fb_2_7.2

theorem f_2_8_0 : (chunkOf (Low6960Gate.gateList 2 8) 0).all (fF 2 8) = true := by decide +kernel
theorem fb_2_8 : one 2 8 = true ∧ gtOne 2 8 = true :=
  both_of_chunks 2 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_8_0
  )
theorem c_2_8 : one 2 8 = true := fb_2_8.1
theorem g_2_8 : gtOne 2 8 = true := fb_2_8.2

theorem f_2_9_0 : (chunkOf (Low6960Gate.gateList 2 9) 0).all (fF 2 9) = true := by decide +kernel
theorem fb_2_9 : one 2 9 = true ∧ gtOne 2 9 = true :=
  both_of_chunks 2 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_9_0
  )
theorem c_2_9 : one 2 9 = true := fb_2_9.1
theorem g_2_9 : gtOne 2 9 = true := fb_2_9.2

end Gate61Fin
