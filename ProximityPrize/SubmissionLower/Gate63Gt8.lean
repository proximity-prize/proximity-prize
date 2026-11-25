import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_2_10_0 : (chunkOf (Low6960Gate.gateList 2 10) 0).all (fF 2 10) = true := by decide +kernel
theorem fb_2_10 : one 2 10 = true ∧ gtOne 2 10 = true :=
  both_of_chunks 2 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_10_0
  )
theorem c_2_10 : one 2 10 = true := fb_2_10.1
theorem g_2_10 : gtOne 2 10 = true := fb_2_10.2

theorem f_2_11_0 : (chunkOf (Low6960Gate.gateList 2 11) 0).all (fF 2 11) = true := by decide +kernel
theorem fb_2_11 : one 2 11 = true ∧ gtOne 2 11 = true :=
  both_of_chunks 2 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_11_0
  )
theorem c_2_11 : one 2 11 = true := fb_2_11.1
theorem g_2_11 : gtOne 2 11 = true := fb_2_11.2

theorem f_2_12_0 : (chunkOf (Low6960Gate.gateList 2 12) 0).all (fF 2 12) = true := by decide +kernel
theorem fb_2_12 : one 2 12 = true ∧ gtOne 2 12 = true :=
  both_of_chunks 2 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_12_0
  )
theorem c_2_12 : one 2 12 = true := fb_2_12.1
theorem g_2_12 : gtOne 2 12 = true := fb_2_12.2

theorem f_2_13_0 : (chunkOf (Low6960Gate.gateList 2 13) 0).all (fF 2 13) = true := by decide +kernel
theorem fb_2_13 : one 2 13 = true ∧ gtOne 2 13 = true :=
  both_of_chunks 2 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_13_0
  )
theorem c_2_13 : one 2 13 = true := fb_2_13.1
theorem g_2_13 : gtOne 2 13 = true := fb_2_13.2

theorem f_3_2_0 : (chunkOf (Low6960Gate.gateList 3 2) 0).all (fF 3 2) = true := by decide +kernel
theorem fb_3_2 : one 3 2 = true ∧ gtOne 3 2 = true :=
  both_of_chunks 3 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_2_0
  )
theorem c_3_2 : one 3 2 = true := fb_3_2.1
theorem g_3_2 : gtOne 3 2 = true := fb_3_2.2

theorem f_3_3_0 : (chunkOf (Low6960Gate.gateList 3 3) 0).all (fF 3 3) = true := by decide +kernel
theorem fb_3_3 : one 3 3 = true ∧ gtOne 3 3 = true :=
  both_of_chunks 3 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_3_0
  )
theorem c_3_3 : one 3 3 = true := fb_3_3.1
theorem g_3_3 : gtOne 3 3 = true := fb_3_3.2

theorem f_3_4_0 : (chunkOf (Low6960Gate.gateList 3 4) 0).all (fF 3 4) = true := by decide +kernel
theorem fb_3_4 : one 3 4 = true ∧ gtOne 3 4 = true :=
  both_of_chunks 3 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_4_0
  )
theorem c_3_4 : one 3 4 = true := fb_3_4.1
theorem g_3_4 : gtOne 3 4 = true := fb_3_4.2

theorem f_3_5_0 : (chunkOf (Low6960Gate.gateList 3 5) 0).all (fF 3 5) = true := by decide +kernel
theorem fb_3_5 : one 3 5 = true ∧ gtOne 3 5 = true :=
  both_of_chunks 3 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_5_0
  )
theorem c_3_5 : one 3 5 = true := fb_3_5.1
theorem g_3_5 : gtOne 3 5 = true := fb_3_5.2

theorem f_3_6_0 : (chunkOf (Low6960Gate.gateList 3 6) 0).all (fF 3 6) = true := by decide +kernel
theorem fb_3_6 : one 3 6 = true ∧ gtOne 3 6 = true :=
  both_of_chunks 3 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_6_0
  )
theorem c_3_6 : one 3 6 = true := fb_3_6.1
theorem g_3_6 : gtOne 3 6 = true := fb_3_6.2

theorem f_3_7_0 : (chunkOf (Low6960Gate.gateList 3 7) 0).all (fF 3 7) = true := by decide +kernel
theorem fb_3_7 : one 3 7 = true ∧ gtOne 3 7 = true :=
  both_of_chunks 3 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_7_0
  )
theorem c_3_7 : one 3 7 = true := fb_3_7.1
theorem g_3_7 : gtOne 3 7 = true := fb_3_7.2

theorem f_3_8_0 : (chunkOf (Low6960Gate.gateList 3 8) 0).all (fF 3 8) = true := by decide +kernel
theorem fb_3_8 : one 3 8 = true ∧ gtOne 3 8 = true :=
  both_of_chunks 3 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_8_0
  )
theorem c_3_8 : one 3 8 = true := fb_3_8.1
theorem g_3_8 : gtOne 3 8 = true := fb_3_8.2

theorem f_3_9_0 : (chunkOf (Low6960Gate.gateList 3 9) 0).all (fF 3 9) = true := by decide +kernel
theorem fb_3_9 : one 3 9 = true ∧ gtOne 3 9 = true :=
  both_of_chunks 3 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_9_0
  )
theorem c_3_9 : one 3 9 = true := fb_3_9.1
theorem g_3_9 : gtOne 3 9 = true := fb_3_9.2

end Gate61Fin
