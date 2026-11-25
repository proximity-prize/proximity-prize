import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_7_13_0 : (chunkOf (Low6960Gate.gateList 7 13) 0).all (fF 7 13) = true := by decide +kernel
theorem fb_7_13 : one 7 13 = true ∧ gtOne 7 13 = true :=
  both_of_chunks 7 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_13_0
  )
theorem c_7_13 : one 7 13 = true := fb_7_13.1
theorem g_7_13 : gtOne 7 13 = true := fb_7_13.2

theorem f_8_5_0 : (chunkOf (Low6960Gate.gateList 8 5) 0).all (fF 8 5) = true := by decide +kernel
theorem fb_8_5 : one 8 5 = true ∧ gtOne 8 5 = true :=
  both_of_chunks 8 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_5_0
  )
theorem c_8_5 : one 8 5 = true := fb_8_5.1
theorem g_8_5 : gtOne 8 5 = true := fb_8_5.2

theorem f_8_6_0 : (chunkOf (Low6960Gate.gateList 8 6) 0).all (fF 8 6) = true := by decide +kernel
theorem fb_8_6 : one 8 6 = true ∧ gtOne 8 6 = true :=
  both_of_chunks 8 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_6_0
  )
theorem c_8_6 : one 8 6 = true := fb_8_6.1
theorem g_8_6 : gtOne 8 6 = true := fb_8_6.2

theorem f_8_7_0 : (chunkOf (Low6960Gate.gateList 8 7) 0).all (fF 8 7) = true := by decide +kernel
theorem fb_8_7 : one 8 7 = true ∧ gtOne 8 7 = true :=
  both_of_chunks 8 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_7_0
  )
theorem c_8_7 : one 8 7 = true := fb_8_7.1
theorem g_8_7 : gtOne 8 7 = true := fb_8_7.2

theorem f_8_8_0 : (chunkOf (Low6960Gate.gateList 8 8) 0).all (fF 8 8) = true := by decide +kernel
theorem fb_8_8 : one 8 8 = true ∧ gtOne 8 8 = true :=
  both_of_chunks 8 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_8_0
  )
theorem c_8_8 : one 8 8 = true := fb_8_8.1
theorem g_8_8 : gtOne 8 8 = true := fb_8_8.2

theorem f_8_9_0 : (chunkOf (Low6960Gate.gateList 8 9) 0).all (fF 8 9) = true := by decide +kernel
theorem fb_8_9 : one 8 9 = true ∧ gtOne 8 9 = true :=
  both_of_chunks 8 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_9_0
  )
theorem c_8_9 : one 8 9 = true := fb_8_9.1
theorem g_8_9 : gtOne 8 9 = true := fb_8_9.2

theorem f_8_10_0 : (chunkOf (Low6960Gate.gateList 8 10) 0).all (fF 8 10) = true := by decide +kernel
theorem fb_8_10 : one 8 10 = true ∧ gtOne 8 10 = true :=
  both_of_chunks 8 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_10_0
  )
theorem c_8_10 : one 8 10 = true := fb_8_10.1
theorem g_8_10 : gtOne 8 10 = true := fb_8_10.2

theorem f_8_11_0 : (chunkOf (Low6960Gate.gateList 8 11) 0).all (fF 8 11) = true := by decide +kernel
theorem fb_8_11 : one 8 11 = true ∧ gtOne 8 11 = true :=
  both_of_chunks 8 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_11_0
  )
theorem c_8_11 : one 8 11 = true := fb_8_11.1
theorem g_8_11 : gtOne 8 11 = true := fb_8_11.2

theorem f_8_12_0 : (chunkOf (Low6960Gate.gateList 8 12) 0).all (fF 8 12) = true := by decide +kernel
theorem fb_8_12 : one 8 12 = true ∧ gtOne 8 12 = true :=
  both_of_chunks 8 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_12_0
  )
theorem c_8_12 : one 8 12 = true := fb_8_12.1
theorem g_8_12 : gtOne 8 12 = true := fb_8_12.2

theorem f_8_13_0 : (chunkOf (Low6960Gate.gateList 8 13) 0).all (fF 8 13) = true := by decide +kernel
theorem fb_8_13 : one 8 13 = true ∧ gtOne 8 13 = true :=
  both_of_chunks 8 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_13_0
  )
theorem c_8_13 : one 8 13 = true := fb_8_13.1
theorem g_8_13 : gtOne 8 13 = true := fb_8_13.2

theorem f_9_7_0 : (chunkOf (Low6960Gate.gateList 9 7) 0).all (fF 9 7) = true := by decide +kernel
theorem fb_9_7 : one 9 7 = true ∧ gtOne 9 7 = true :=
  both_of_chunks 9 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_7_0
  )
theorem c_9_7 : one 9 7 = true := fb_9_7.1
theorem g_9_7 : gtOne 9 7 = true := fb_9_7.2

theorem f_9_8_0 : (chunkOf (Low6960Gate.gateList 9 8) 0).all (fF 9 8) = true := by decide +kernel
theorem fb_9_8 : one 9 8 = true ∧ gtOne 9 8 = true :=
  both_of_chunks 9 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_8_0
  )
theorem c_9_8 : one 9 8 = true := fb_9_8.1
theorem g_9_8 : gtOne 9 8 = true := fb_9_8.2

theorem f_9_9_0 : (chunkOf (Low6960Gate.gateList 9 9) 0).all (fF 9 9) = true := by decide +kernel
theorem fb_9_9 : one 9 9 = true ∧ gtOne 9 9 = true :=
  both_of_chunks 9 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_9_0
  )
theorem c_9_9 : one 9 9 = true := fb_9_9.1
theorem g_9_9 : gtOne 9 9 = true := fb_9_9.2

theorem f_9_10_0 : (chunkOf (Low6960Gate.gateList 9 10) 0).all (fF 9 10) = true := by decide +kernel
theorem fb_9_10 : one 9 10 = true ∧ gtOne 9 10 = true :=
  both_of_chunks 9 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_10_0
  )
theorem c_9_10 : one 9 10 = true := fb_9_10.1
theorem g_9_10 : gtOne 9 10 = true := fb_9_10.2

theorem f_9_11_0 : (chunkOf (Low6960Gate.gateList 9 11) 0).all (fF 9 11) = true := by decide +kernel
theorem fb_9_11 : one 9 11 = true ∧ gtOne 9 11 = true :=
  both_of_chunks 9 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_11_0
  )
theorem c_9_11 : one 9 11 = true := fb_9_11.1
theorem g_9_11 : gtOne 9 11 = true := fb_9_11.2

theorem f_9_12_0 : (chunkOf (Low6960Gate.gateList 9 12) 0).all (fF 9 12) = true := by decide +kernel
theorem fb_9_12 : one 9 12 = true ∧ gtOne 9 12 = true :=
  both_of_chunks 9 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_12_0
  )
theorem c_9_12 : one 9 12 = true := fb_9_12.1
theorem g_9_12 : gtOne 9 12 = true := fb_9_12.2

theorem f_9_13_0 : (chunkOf (Low6960Gate.gateList 9 13) 0).all (fF 9 13) = true := by decide +kernel
theorem fb_9_13 : one 9 13 = true ∧ gtOne 9 13 = true :=
  both_of_chunks 9 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_13_0
  )
theorem c_9_13 : one 9 13 = true := fb_9_13.1
theorem g_9_13 : gtOne 9 13 = true := fb_9_13.2

theorem f_10_10_0 : (chunkOf (Low6960Gate.gateList 10 10) 0).all (fF 10 10) = true := by decide +kernel
theorem fb_10_10 : one 10 10 = true ∧ gtOne 10 10 = true :=
  both_of_chunks 10 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_10_0
  )
theorem c_10_10 : one 10 10 = true := fb_10_10.1
theorem g_10_10 : gtOne 10 10 = true := fb_10_10.2

theorem f_10_11_0 : (chunkOf (Low6960Gate.gateList 10 11) 0).all (fF 10 11) = true := by decide +kernel
theorem fb_10_11 : one 10 11 = true ∧ gtOne 10 11 = true :=
  both_of_chunks 10 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_11_0
  )
theorem c_10_11 : one 10 11 = true := fb_10_11.1
theorem g_10_11 : gtOne 10 11 = true := fb_10_11.2

theorem f_10_12_0 : (chunkOf (Low6960Gate.gateList 10 12) 0).all (fF 10 12) = true := by decide +kernel
theorem fb_10_12 : one 10 12 = true ∧ gtOne 10 12 = true :=
  both_of_chunks 10 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_12_0
  )
theorem c_10_12 : one 10 12 = true := fb_10_12.1
theorem g_10_12 : gtOne 10 12 = true := fb_10_12.2

theorem f_10_13_0 : (chunkOf (Low6960Gate.gateList 10 13) 0).all (fF 10 13) = true := by decide +kernel
theorem fb_10_13 : one 10 13 = true ∧ gtOne 10 13 = true :=
  both_of_chunks 10 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_13_0
  )
theorem c_10_13 : one 10 13 = true := fb_10_13.1
theorem g_10_13 : gtOne 10 13 = true := fb_10_13.2

theorem f_12_5_0 : (chunkOf (Low6960Gate.gateList 12 5) 0).all (fF 12 5) = true := by decide +kernel
theorem fb_12_5 : one 12 5 = true ∧ gtOne 12 5 = true :=
  both_of_chunks 12 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_5_0
  )
theorem c_12_5 : one 12 5 = true := fb_12_5.1
theorem g_12_5 : gtOne 12 5 = true := fb_12_5.2

theorem f_12_6_0 : (chunkOf (Low6960Gate.gateList 12 6) 0).all (fF 12 6) = true := by decide +kernel
theorem fb_12_6 : one 12 6 = true ∧ gtOne 12 6 = true :=
  both_of_chunks 12 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_6_0
  )
theorem c_12_6 : one 12 6 = true := fb_12_6.1
theorem g_12_6 : gtOne 12 6 = true := fb_12_6.2

theorem f_12_7_0 : (chunkOf (Low6960Gate.gateList 12 7) 0).all (fF 12 7) = true := by decide +kernel
theorem fb_12_7 : one 12 7 = true ∧ gtOne 12 7 = true :=
  both_of_chunks 12 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_7_0
  )
theorem c_12_7 : one 12 7 = true := fb_12_7.1
theorem g_12_7 : gtOne 12 7 = true := fb_12_7.2

theorem f_12_8_0 : (chunkOf (Low6960Gate.gateList 12 8) 0).all (fF 12 8) = true := by decide +kernel
theorem fb_12_8 : one 12 8 = true ∧ gtOne 12 8 = true :=
  both_of_chunks 12 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_8_0
  )
theorem c_12_8 : one 12 8 = true := fb_12_8.1
theorem g_12_8 : gtOne 12 8 = true := fb_12_8.2

theorem f_12_9_0 : (chunkOf (Low6960Gate.gateList 12 9) 0).all (fF 12 9) = true := by decide +kernel
theorem fb_12_9 : one 12 9 = true ∧ gtOne 12 9 = true :=
  both_of_chunks 12 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_9_0
  )
theorem c_12_9 : one 12 9 = true := fb_12_9.1
theorem g_12_9 : gtOne 12 9 = true := fb_12_9.2

theorem f_12_10_0 : (chunkOf (Low6960Gate.gateList 12 10) 0).all (fF 12 10) = true := by decide +kernel
theorem fb_12_10 : one 12 10 = true ∧ gtOne 12 10 = true :=
  both_of_chunks 12 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_10_0
  )
theorem c_12_10 : one 12 10 = true := fb_12_10.1
theorem g_12_10 : gtOne 12 10 = true := fb_12_10.2

theorem f_12_11_0 : (chunkOf (Low6960Gate.gateList 12 11) 0).all (fF 12 11) = true := by decide +kernel
theorem fb_12_11 : one 12 11 = true ∧ gtOne 12 11 = true :=
  both_of_chunks 12 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_11_0
  )
theorem c_12_11 : one 12 11 = true := fb_12_11.1
theorem g_12_11 : gtOne 12 11 = true := fb_12_11.2

theorem f_12_12_0 : (chunkOf (Low6960Gate.gateList 12 12) 0).all (fF 12 12) = true := by decide +kernel
theorem fb_12_12 : one 12 12 = true ∧ gtOne 12 12 = true :=
  both_of_chunks 12 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_12_0
  )
theorem c_12_12 : one 12 12 = true := fb_12_12.1
theorem g_12_12 : gtOne 12 12 = true := fb_12_12.2

theorem f_12_13_0 : (chunkOf (Low6960Gate.gateList 12 13) 0).all (fF 12 13) = true := by decide +kernel
theorem fb_12_13 : one 12 13 = true ∧ gtOne 12 13 = true :=
  both_of_chunks 12 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_13_0
  )
theorem c_12_13 : one 12 13 = true := fb_12_13.1
theorem g_12_13 : gtOne 12 13 = true := fb_12_13.2

theorem f_13_6_0 : (chunkOf (Low6960Gate.gateList 13 6) 0).all (fF 13 6) = true := by decide +kernel
theorem fb_13_6 : one 13 6 = true ∧ gtOne 13 6 = true :=
  both_of_chunks 13 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_6_0
  )
theorem c_13_6 : one 13 6 = true := fb_13_6.1
theorem g_13_6 : gtOne 13 6 = true := fb_13_6.2

theorem f_13_7_0 : (chunkOf (Low6960Gate.gateList 13 7) 0).all (fF 13 7) = true := by decide +kernel
theorem fb_13_7 : one 13 7 = true ∧ gtOne 13 7 = true :=
  both_of_chunks 13 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_7_0
  )
theorem c_13_7 : one 13 7 = true := fb_13_7.1
theorem g_13_7 : gtOne 13 7 = true := fb_13_7.2

theorem f_13_8_0 : (chunkOf (Low6960Gate.gateList 13 8) 0).all (fF 13 8) = true := by decide +kernel
theorem fb_13_8 : one 13 8 = true ∧ gtOne 13 8 = true :=
  both_of_chunks 13 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_8_0
  )
theorem c_13_8 : one 13 8 = true := fb_13_8.1
theorem g_13_8 : gtOne 13 8 = true := fb_13_8.2

theorem f_13_9_0 : (chunkOf (Low6960Gate.gateList 13 9) 0).all (fF 13 9) = true := by decide +kernel
theorem fb_13_9 : one 13 9 = true ∧ gtOne 13 9 = true :=
  both_of_chunks 13 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_9_0
  )
theorem c_13_9 : one 13 9 = true := fb_13_9.1
theorem g_13_9 : gtOne 13 9 = true := fb_13_9.2

theorem f_13_10_0 : (chunkOf (Low6960Gate.gateList 13 10) 0).all (fF 13 10) = true := by decide +kernel
theorem fb_13_10 : one 13 10 = true ∧ gtOne 13 10 = true :=
  both_of_chunks 13 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_10_0
  )
theorem c_13_10 : one 13 10 = true := fb_13_10.1
theorem g_13_10 : gtOne 13 10 = true := fb_13_10.2

theorem f_13_11_0 : (chunkOf (Low6960Gate.gateList 13 11) 0).all (fF 13 11) = true := by decide +kernel
theorem fb_13_11 : one 13 11 = true ∧ gtOne 13 11 = true :=
  both_of_chunks 13 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_11_0
  )
theorem c_13_11 : one 13 11 = true := fb_13_11.1
theorem g_13_11 : gtOne 13 11 = true := fb_13_11.2

theorem f_13_12_0 : (chunkOf (Low6960Gate.gateList 13 12) 0).all (fF 13 12) = true := by decide +kernel
theorem fb_13_12 : one 13 12 = true ∧ gtOne 13 12 = true :=
  both_of_chunks 13 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_12_0
  )
theorem c_13_12 : one 13 12 = true := fb_13_12.1
theorem g_13_12 : gtOne 13 12 = true := fb_13_12.2

theorem f_13_13_0 : (chunkOf (Low6960Gate.gateList 13 13) 0).all (fF 13 13) = true := by decide +kernel
theorem fb_13_13 : one 13 13 = true ∧ gtOne 13 13 = true :=
  both_of_chunks 13 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_13_0
  )
theorem c_13_13 : one 13 13 = true := fb_13_13.1
theorem g_13_13 : gtOne 13 13 = true := fb_13_13.2

theorem f_14_7_0 : (chunkOf (Low6960Gate.gateList 14 7) 0).all (fF 14 7) = true := by decide +kernel
theorem fb_14_7 : one 14 7 = true ∧ gtOne 14 7 = true :=
  both_of_chunks 14 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_14_7_0
  )
theorem c_14_7 : one 14 7 = true := fb_14_7.1
theorem g_14_7 : gtOne 14 7 = true := fb_14_7.2

theorem f_14_8_0 : (chunkOf (Low6960Gate.gateList 14 8) 0).all (fF 14 8) = true := by decide +kernel
theorem fb_14_8 : one 14 8 = true ∧ gtOne 14 8 = true :=
  both_of_chunks 14 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_14_8_0
  )
theorem c_14_8 : one 14 8 = true := fb_14_8.1
theorem g_14_8 : gtOne 14 8 = true := fb_14_8.2

theorem f_14_9_0 : (chunkOf (Low6960Gate.gateList 14 9) 0).all (fF 14 9) = true := by decide +kernel
theorem fb_14_9 : one 14 9 = true ∧ gtOne 14 9 = true :=
  both_of_chunks 14 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_14_9_0
  )
theorem c_14_9 : one 14 9 = true := fb_14_9.1
theorem g_14_9 : gtOne 14 9 = true := fb_14_9.2

theorem f_14_10_0 : (chunkOf (Low6960Gate.gateList 14 10) 0).all (fF 14 10) = true := by decide +kernel
theorem fb_14_10 : one 14 10 = true ∧ gtOne 14 10 = true :=
  both_of_chunks 14 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_14_10_0
  )
theorem c_14_10 : one 14 10 = true := fb_14_10.1
theorem g_14_10 : gtOne 14 10 = true := fb_14_10.2

theorem f_14_11_0 : (chunkOf (Low6960Gate.gateList 14 11) 0).all (fF 14 11) = true := by decide +kernel
theorem fb_14_11 : one 14 11 = true ∧ gtOne 14 11 = true :=
  both_of_chunks 14 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_14_11_0
  )
theorem c_14_11 : one 14 11 = true := fb_14_11.1
theorem g_14_11 : gtOne 14 11 = true := fb_14_11.2

theorem f_14_12_0 : (chunkOf (Low6960Gate.gateList 14 12) 0).all (fF 14 12) = true := by decide +kernel
theorem fb_14_12 : one 14 12 = true ∧ gtOne 14 12 = true :=
  both_of_chunks 14 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_14_12_0
  )
theorem c_14_12 : one 14 12 = true := fb_14_12.1
theorem g_14_12 : gtOne 14 12 = true := fb_14_12.2

theorem f_14_13_0 : (chunkOf (Low6960Gate.gateList 14 13) 0).all (fF 14 13) = true := by decide +kernel
theorem fb_14_13 : one 14 13 = true ∧ gtOne 14 13 = true :=
  both_of_chunks 14 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_14_13_0
  )
theorem c_14_13 : one 14 13 = true := fb_14_13.1
theorem g_14_13 : gtOne 14 13 = true := fb_14_13.2

theorem f_15_10_0 : (chunkOf (Low6960Gate.gateList 15 10) 0).all (fF 15 10) = true := by decide +kernel
theorem fb_15_10 : one 15 10 = true ∧ gtOne 15 10 = true :=
  both_of_chunks 15 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_15_10_0
  )
theorem c_15_10 : one 15 10 = true := fb_15_10.1
theorem g_15_10 : gtOne 15 10 = true := fb_15_10.2

theorem f_15_11_0 : (chunkOf (Low6960Gate.gateList 15 11) 0).all (fF 15 11) = true := by decide +kernel
theorem fb_15_11 : one 15 11 = true ∧ gtOne 15 11 = true :=
  both_of_chunks 15 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_15_11_0
  )
theorem c_15_11 : one 15 11 = true := fb_15_11.1
theorem g_15_11 : gtOne 15 11 = true := fb_15_11.2

theorem f_15_12_0 : (chunkOf (Low6960Gate.gateList 15 12) 0).all (fF 15 12) = true := by decide +kernel
theorem fb_15_12 : one 15 12 = true ∧ gtOne 15 12 = true :=
  both_of_chunks 15 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_15_12_0
  )
theorem c_15_12 : one 15 12 = true := fb_15_12.1
theorem g_15_12 : gtOne 15 12 = true := fb_15_12.2

theorem f_15_13_0 : (chunkOf (Low6960Gate.gateList 15 13) 0).all (fF 15 13) = true := by decide +kernel
theorem fb_15_13 : one 15 13 = true ∧ gtOne 15 13 = true :=
  both_of_chunks 15 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_15_13_0
  )
theorem c_15_13 : one 15 13 = true := fb_15_13.1
theorem g_15_13 : gtOne 15 13 = true := fb_15_13.2

end Gate61Fin
