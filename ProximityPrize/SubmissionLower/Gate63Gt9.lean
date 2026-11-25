import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_3_10_0 : (chunkOf (Low6960Gate.gateList 3 10) 0).all (fF 3 10) = true := by decide +kernel
theorem fb_3_10 : one 3 10 = true ∧ gtOne 3 10 = true :=
  both_of_chunks 3 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_10_0
  )
theorem c_3_10 : one 3 10 = true := fb_3_10.1
theorem g_3_10 : gtOne 3 10 = true := fb_3_10.2

theorem f_3_11_0 : (chunkOf (Low6960Gate.gateList 3 11) 0).all (fF 3 11) = true := by decide +kernel
theorem fb_3_11 : one 3 11 = true ∧ gtOne 3 11 = true :=
  both_of_chunks 3 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_11_0
  )
theorem c_3_11 : one 3 11 = true := fb_3_11.1
theorem g_3_11 : gtOne 3 11 = true := fb_3_11.2

theorem f_3_12_0 : (chunkOf (Low6960Gate.gateList 3 12) 0).all (fF 3 12) = true := by decide +kernel
theorem fb_3_12 : one 3 12 = true ∧ gtOne 3 12 = true :=
  both_of_chunks 3 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_12_0
  )
theorem c_3_12 : one 3 12 = true := fb_3_12.1
theorem g_3_12 : gtOne 3 12 = true := fb_3_12.2

theorem f_3_13_0 : (chunkOf (Low6960Gate.gateList 3 13) 0).all (fF 3 13) = true := by decide +kernel
theorem fb_3_13 : one 3 13 = true ∧ gtOne 3 13 = true :=
  both_of_chunks 3 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_13_0
  )
theorem c_3_13 : one 3 13 = true := fb_3_13.1
theorem g_3_13 : gtOne 3 13 = true := fb_3_13.2

theorem f_4_2_0 : (chunkOf (Low6960Gate.gateList 4 2) 0).all (fF 4 2) = true := by decide +kernel
theorem fb_4_2 : one 4 2 = true ∧ gtOne 4 2 = true :=
  both_of_chunks 4 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_2_0
  )
theorem c_4_2 : one 4 2 = true := fb_4_2.1
theorem g_4_2 : gtOne 4 2 = true := fb_4_2.2

theorem f_4_3_0 : (chunkOf (Low6960Gate.gateList 4 3) 0).all (fF 4 3) = true := by decide +kernel
theorem fb_4_3 : one 4 3 = true ∧ gtOne 4 3 = true :=
  both_of_chunks 4 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_3_0
  )
theorem c_4_3 : one 4 3 = true := fb_4_3.1
theorem g_4_3 : gtOne 4 3 = true := fb_4_3.2

theorem f_4_4_0 : (chunkOf (Low6960Gate.gateList 4 4) 0).all (fF 4 4) = true := by decide +kernel
theorem fb_4_4 : one 4 4 = true ∧ gtOne 4 4 = true :=
  both_of_chunks 4 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_4_0
  )
theorem c_4_4 : one 4 4 = true := fb_4_4.1
theorem g_4_4 : gtOne 4 4 = true := fb_4_4.2

theorem f_4_5_0 : (chunkOf (Low6960Gate.gateList 4 5) 0).all (fF 4 5) = true := by decide +kernel
theorem fb_4_5 : one 4 5 = true ∧ gtOne 4 5 = true :=
  both_of_chunks 4 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_5_0
  )
theorem c_4_5 : one 4 5 = true := fb_4_5.1
theorem g_4_5 : gtOne 4 5 = true := fb_4_5.2

theorem f_4_6_0 : (chunkOf (Low6960Gate.gateList 4 6) 0).all (fF 4 6) = true := by decide +kernel
theorem fb_4_6 : one 4 6 = true ∧ gtOne 4 6 = true :=
  both_of_chunks 4 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_6_0
  )
theorem c_4_6 : one 4 6 = true := fb_4_6.1
theorem g_4_6 : gtOne 4 6 = true := fb_4_6.2

theorem f_4_7_0 : (chunkOf (Low6960Gate.gateList 4 7) 0).all (fF 4 7) = true := by decide +kernel
theorem fb_4_7 : one 4 7 = true ∧ gtOne 4 7 = true :=
  both_of_chunks 4 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_7_0
  )
theorem c_4_7 : one 4 7 = true := fb_4_7.1
theorem g_4_7 : gtOne 4 7 = true := fb_4_7.2

theorem f_4_8_0 : (chunkOf (Low6960Gate.gateList 4 8) 0).all (fF 4 8) = true := by decide +kernel
theorem fb_4_8 : one 4 8 = true ∧ gtOne 4 8 = true :=
  both_of_chunks 4 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_8_0
  )
theorem c_4_8 : one 4 8 = true := fb_4_8.1
theorem g_4_8 : gtOne 4 8 = true := fb_4_8.2

theorem f_4_9_0 : (chunkOf (Low6960Gate.gateList 4 9) 0).all (fF 4 9) = true := by decide +kernel
theorem fb_4_9 : one 4 9 = true ∧ gtOne 4 9 = true :=
  both_of_chunks 4 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_9_0
  )
theorem c_4_9 : one 4 9 = true := fb_4_9.1
theorem g_4_9 : gtOne 4 9 = true := fb_4_9.2

theorem f_4_10_0 : (chunkOf (Low6960Gate.gateList 4 10) 0).all (fF 4 10) = true := by decide +kernel
theorem fb_4_10 : one 4 10 = true ∧ gtOne 4 10 = true :=
  both_of_chunks 4 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_10_0
  )
theorem c_4_10 : one 4 10 = true := fb_4_10.1
theorem g_4_10 : gtOne 4 10 = true := fb_4_10.2

theorem f_4_11_0 : (chunkOf (Low6960Gate.gateList 4 11) 0).all (fF 4 11) = true := by decide +kernel
theorem fb_4_11 : one 4 11 = true ∧ gtOne 4 11 = true :=
  both_of_chunks 4 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_11_0
  )
theorem c_4_11 : one 4 11 = true := fb_4_11.1
theorem g_4_11 : gtOne 4 11 = true := fb_4_11.2

theorem f_4_12_0 : (chunkOf (Low6960Gate.gateList 4 12) 0).all (fF 4 12) = true := by decide +kernel
theorem fb_4_12 : one 4 12 = true ∧ gtOne 4 12 = true :=
  both_of_chunks 4 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_12_0
  )
theorem c_4_12 : one 4 12 = true := fb_4_12.1
theorem g_4_12 : gtOne 4 12 = true := fb_4_12.2

theorem f_4_13_0 : (chunkOf (Low6960Gate.gateList 4 13) 0).all (fF 4 13) = true := by decide +kernel
theorem fb_4_13 : one 4 13 = true ∧ gtOne 4 13 = true :=
  both_of_chunks 4 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_13_0
  )
theorem c_4_13 : one 4 13 = true := fb_4_13.1
theorem g_4_13 : gtOne 4 13 = true := fb_4_13.2

end Gate61Fin
