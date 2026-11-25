import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_5_3_0 : (chunkOf (Low6960Gate.gateList 5 3) 0).all (fF 5 3) = true := by decide +kernel
theorem fb_5_3 : one 5 3 = true ∧ gtOne 5 3 = true :=
  both_of_chunks 5 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_3_0
  )
theorem c_5_3 : one 5 3 = true := fb_5_3.1
theorem g_5_3 : gtOne 5 3 = true := fb_5_3.2

theorem f_5_4_0 : (chunkOf (Low6960Gate.gateList 5 4) 0).all (fF 5 4) = true := by decide +kernel
theorem fb_5_4 : one 5 4 = true ∧ gtOne 5 4 = true :=
  both_of_chunks 5 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_4_0
  )
theorem c_5_4 : one 5 4 = true := fb_5_4.1
theorem g_5_4 : gtOne 5 4 = true := fb_5_4.2

theorem f_5_5_0 : (chunkOf (Low6960Gate.gateList 5 5) 0).all (fF 5 5) = true := by decide +kernel
theorem fb_5_5 : one 5 5 = true ∧ gtOne 5 5 = true :=
  both_of_chunks 5 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_5_0
  )
theorem c_5_5 : one 5 5 = true := fb_5_5.1
theorem g_5_5 : gtOne 5 5 = true := fb_5_5.2

theorem f_5_6_0 : (chunkOf (Low6960Gate.gateList 5 6) 0).all (fF 5 6) = true := by decide +kernel
theorem fb_5_6 : one 5 6 = true ∧ gtOne 5 6 = true :=
  both_of_chunks 5 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_6_0
  )
theorem c_5_6 : one 5 6 = true := fb_5_6.1
theorem g_5_6 : gtOne 5 6 = true := fb_5_6.2

theorem f_5_7_0 : (chunkOf (Low6960Gate.gateList 5 7) 0).all (fF 5 7) = true := by decide +kernel
theorem fb_5_7 : one 5 7 = true ∧ gtOne 5 7 = true :=
  both_of_chunks 5 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_7_0
  )
theorem c_5_7 : one 5 7 = true := fb_5_7.1
theorem g_5_7 : gtOne 5 7 = true := fb_5_7.2

theorem f_5_8_0 : (chunkOf (Low6960Gate.gateList 5 8) 0).all (fF 5 8) = true := by decide +kernel
theorem fb_5_8 : one 5 8 = true ∧ gtOne 5 8 = true :=
  both_of_chunks 5 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_8_0
  )
theorem c_5_8 : one 5 8 = true := fb_5_8.1
theorem g_5_8 : gtOne 5 8 = true := fb_5_8.2

theorem f_5_9_0 : (chunkOf (Low6960Gate.gateList 5 9) 0).all (fF 5 9) = true := by decide +kernel
theorem fb_5_9 : one 5 9 = true ∧ gtOne 5 9 = true :=
  both_of_chunks 5 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_9_0
  )
theorem c_5_9 : one 5 9 = true := fb_5_9.1
theorem g_5_9 : gtOne 5 9 = true := fb_5_9.2

theorem f_5_10_0 : (chunkOf (Low6960Gate.gateList 5 10) 0).all (fF 5 10) = true := by decide +kernel
theorem fb_5_10 : one 5 10 = true ∧ gtOne 5 10 = true :=
  both_of_chunks 5 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_10_0
  )
theorem c_5_10 : one 5 10 = true := fb_5_10.1
theorem g_5_10 : gtOne 5 10 = true := fb_5_10.2

theorem f_5_11_0 : (chunkOf (Low6960Gate.gateList 5 11) 0).all (fF 5 11) = true := by decide +kernel
theorem fb_5_11 : one 5 11 = true ∧ gtOne 5 11 = true :=
  both_of_chunks 5 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_11_0
  )
theorem c_5_11 : one 5 11 = true := fb_5_11.1
theorem g_5_11 : gtOne 5 11 = true := fb_5_11.2

theorem f_5_12_0 : (chunkOf (Low6960Gate.gateList 5 12) 0).all (fF 5 12) = true := by decide +kernel
theorem fb_5_12 : one 5 12 = true ∧ gtOne 5 12 = true :=
  both_of_chunks 5 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_12_0
  )
theorem c_5_12 : one 5 12 = true := fb_5_12.1
theorem g_5_12 : gtOne 5 12 = true := fb_5_12.2

theorem f_5_13_0 : (chunkOf (Low6960Gate.gateList 5 13) 0).all (fF 5 13) = true := by decide +kernel
theorem fb_5_13 : one 5 13 = true ∧ gtOne 5 13 = true :=
  both_of_chunks 5 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_13_0
  )
theorem c_5_13 : one 5 13 = true := fb_5_13.1
theorem g_5_13 : gtOne 5 13 = true := fb_5_13.2

theorem f_6_3_0 : (chunkOf (Low6960Gate.gateList 6 3) 0).all (fF 6 3) = true := by decide +kernel
theorem fb_6_3 : one 6 3 = true ∧ gtOne 6 3 = true :=
  both_of_chunks 6 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_3_0
  )
theorem c_6_3 : one 6 3 = true := fb_6_3.1
theorem g_6_3 : gtOne 6 3 = true := fb_6_3.2

theorem f_6_4_0 : (chunkOf (Low6960Gate.gateList 6 4) 0).all (fF 6 4) = true := by decide +kernel
theorem fb_6_4 : one 6 4 = true ∧ gtOne 6 4 = true :=
  both_of_chunks 6 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_4_0
  )
theorem c_6_4 : one 6 4 = true := fb_6_4.1
theorem g_6_4 : gtOne 6 4 = true := fb_6_4.2

theorem f_6_5_0 : (chunkOf (Low6960Gate.gateList 6 5) 0).all (fF 6 5) = true := by decide +kernel
theorem fb_6_5 : one 6 5 = true ∧ gtOne 6 5 = true :=
  both_of_chunks 6 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_5_0
  )
theorem c_6_5 : one 6 5 = true := fb_6_5.1
theorem g_6_5 : gtOne 6 5 = true := fb_6_5.2

theorem f_6_6_0 : (chunkOf (Low6960Gate.gateList 6 6) 0).all (fF 6 6) = true := by decide +kernel
theorem fb_6_6 : one 6 6 = true ∧ gtOne 6 6 = true :=
  both_of_chunks 6 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_6_0
  )
theorem c_6_6 : one 6 6 = true := fb_6_6.1
theorem g_6_6 : gtOne 6 6 = true := fb_6_6.2

theorem f_6_7_0 : (chunkOf (Low6960Gate.gateList 6 7) 0).all (fF 6 7) = true := by decide +kernel
theorem fb_6_7 : one 6 7 = true ∧ gtOne 6 7 = true :=
  both_of_chunks 6 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_7_0
  )
theorem c_6_7 : one 6 7 = true := fb_6_7.1
theorem g_6_7 : gtOne 6 7 = true := fb_6_7.2

theorem f_6_8_0 : (chunkOf (Low6960Gate.gateList 6 8) 0).all (fF 6 8) = true := by decide +kernel
theorem fb_6_8 : one 6 8 = true ∧ gtOne 6 8 = true :=
  both_of_chunks 6 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_8_0
  )
theorem c_6_8 : one 6 8 = true := fb_6_8.1
theorem g_6_8 : gtOne 6 8 = true := fb_6_8.2

theorem f_6_9_0 : (chunkOf (Low6960Gate.gateList 6 9) 0).all (fF 6 9) = true := by decide +kernel
theorem fb_6_9 : one 6 9 = true ∧ gtOne 6 9 = true :=
  both_of_chunks 6 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_9_0
  )
theorem c_6_9 : one 6 9 = true := fb_6_9.1
theorem g_6_9 : gtOne 6 9 = true := fb_6_9.2

theorem f_6_10_0 : (chunkOf (Low6960Gate.gateList 6 10) 0).all (fF 6 10) = true := by decide +kernel
theorem fb_6_10 : one 6 10 = true ∧ gtOne 6 10 = true :=
  both_of_chunks 6 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_10_0
  )
theorem c_6_10 : one 6 10 = true := fb_6_10.1
theorem g_6_10 : gtOne 6 10 = true := fb_6_10.2

theorem f_6_11_0 : (chunkOf (Low6960Gate.gateList 6 11) 0).all (fF 6 11) = true := by decide +kernel
theorem fb_6_11 : one 6 11 = true ∧ gtOne 6 11 = true :=
  both_of_chunks 6 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_11_0
  )
theorem c_6_11 : one 6 11 = true := fb_6_11.1
theorem g_6_11 : gtOne 6 11 = true := fb_6_11.2

theorem f_6_12_0 : (chunkOf (Low6960Gate.gateList 6 12) 0).all (fF 6 12) = true := by decide +kernel
theorem fb_6_12 : one 6 12 = true ∧ gtOne 6 12 = true :=
  both_of_chunks 6 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_12_0
  )
theorem c_6_12 : one 6 12 = true := fb_6_12.1
theorem g_6_12 : gtOne 6 12 = true := fb_6_12.2

theorem f_6_13_0 : (chunkOf (Low6960Gate.gateList 6 13) 0).all (fF 6 13) = true := by decide +kernel
theorem fb_6_13 : one 6 13 = true ∧ gtOne 6 13 = true :=
  both_of_chunks 6 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_13_0
  )
theorem c_6_13 : one 6 13 = true := fb_6_13.1
theorem g_6_13 : gtOne 6 13 = true := fb_6_13.2

theorem f_7_4_0 : (chunkOf (Low6960Gate.gateList 7 4) 0).all (fF 7 4) = true := by decide +kernel
theorem fb_7_4 : one 7 4 = true ∧ gtOne 7 4 = true :=
  both_of_chunks 7 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_4_0
  )
theorem c_7_4 : one 7 4 = true := fb_7_4.1
theorem g_7_4 : gtOne 7 4 = true := fb_7_4.2

theorem f_7_5_0 : (chunkOf (Low6960Gate.gateList 7 5) 0).all (fF 7 5) = true := by decide +kernel
theorem fb_7_5 : one 7 5 = true ∧ gtOne 7 5 = true :=
  both_of_chunks 7 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_5_0
  )
theorem c_7_5 : one 7 5 = true := fb_7_5.1
theorem g_7_5 : gtOne 7 5 = true := fb_7_5.2

theorem f_7_6_0 : (chunkOf (Low6960Gate.gateList 7 6) 0).all (fF 7 6) = true := by decide +kernel
theorem fb_7_6 : one 7 6 = true ∧ gtOne 7 6 = true :=
  both_of_chunks 7 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_6_0
  )
theorem c_7_6 : one 7 6 = true := fb_7_6.1
theorem g_7_6 : gtOne 7 6 = true := fb_7_6.2

theorem f_7_7_0 : (chunkOf (Low6960Gate.gateList 7 7) 0).all (fF 7 7) = true := by decide +kernel
theorem fb_7_7 : one 7 7 = true ∧ gtOne 7 7 = true :=
  both_of_chunks 7 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_7_0
  )
theorem c_7_7 : one 7 7 = true := fb_7_7.1
theorem g_7_7 : gtOne 7 7 = true := fb_7_7.2

theorem f_7_8_0 : (chunkOf (Low6960Gate.gateList 7 8) 0).all (fF 7 8) = true := by decide +kernel
theorem fb_7_8 : one 7 8 = true ∧ gtOne 7 8 = true :=
  both_of_chunks 7 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_8_0
  )
theorem c_7_8 : one 7 8 = true := fb_7_8.1
theorem g_7_8 : gtOne 7 8 = true := fb_7_8.2

theorem f_7_9_0 : (chunkOf (Low6960Gate.gateList 7 9) 0).all (fF 7 9) = true := by decide +kernel
theorem fb_7_9 : one 7 9 = true ∧ gtOne 7 9 = true :=
  both_of_chunks 7 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_9_0
  )
theorem c_7_9 : one 7 9 = true := fb_7_9.1
theorem g_7_9 : gtOne 7 9 = true := fb_7_9.2

theorem f_7_10_0 : (chunkOf (Low6960Gate.gateList 7 10) 0).all (fF 7 10) = true := by decide +kernel
theorem fb_7_10 : one 7 10 = true ∧ gtOne 7 10 = true :=
  both_of_chunks 7 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_10_0
  )
theorem c_7_10 : one 7 10 = true := fb_7_10.1
theorem g_7_10 : gtOne 7 10 = true := fb_7_10.2

theorem f_7_11_0 : (chunkOf (Low6960Gate.gateList 7 11) 0).all (fF 7 11) = true := by decide +kernel
theorem fb_7_11 : one 7 11 = true ∧ gtOne 7 11 = true :=
  both_of_chunks 7 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_11_0
  )
theorem c_7_11 : one 7 11 = true := fb_7_11.1
theorem g_7_11 : gtOne 7 11 = true := fb_7_11.2

theorem f_7_12_0 : (chunkOf (Low6960Gate.gateList 7 12) 0).all (fF 7 12) = true := by decide +kernel
theorem fb_7_12 : one 7 12 = true ∧ gtOne 7 12 = true :=
  both_of_chunks 7 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_12_0
  )
theorem c_7_12 : one 7 12 = true := fb_7_12.1
theorem g_7_12 : gtOne 7 12 = true := fb_7_12.2

end Gate61Fin
