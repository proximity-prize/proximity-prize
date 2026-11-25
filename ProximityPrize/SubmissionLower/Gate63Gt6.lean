import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_1_5_0 : (chunkOf (Low6960Gate.gateList 1 5) 0).all (fF 1 5) = true := by decide +kernel
theorem fb_1_5 : one 1 5 = true ∧ gtOne 1 5 = true :=
  both_of_chunks 1 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_5_0
  )
theorem c_1_5 : one 1 5 = true := fb_1_5.1
theorem g_1_5 : gtOne 1 5 = true := fb_1_5.2

theorem f_1_6_0 : (chunkOf (Low6960Gate.gateList 1 6) 0).all (fF 1 6) = true := by decide +kernel
theorem fb_1_6 : one 1 6 = true ∧ gtOne 1 6 = true :=
  both_of_chunks 1 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_6_0
  )
theorem c_1_6 : one 1 6 = true := fb_1_6.1
theorem g_1_6 : gtOne 1 6 = true := fb_1_6.2

theorem f_1_7_0 : (chunkOf (Low6960Gate.gateList 1 7) 0).all (fF 1 7) = true := by decide +kernel
theorem fb_1_7 : one 1 7 = true ∧ gtOne 1 7 = true :=
  both_of_chunks 1 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_7_0
  )
theorem c_1_7 : one 1 7 = true := fb_1_7.1
theorem g_1_7 : gtOne 1 7 = true := fb_1_7.2

theorem f_1_8_0 : (chunkOf (Low6960Gate.gateList 1 8) 0).all (fF 1 8) = true := by decide +kernel
theorem f_1_8_1 : (chunkOf (Low6960Gate.gateList 1 8) 1).all (fF 1 8) = true := by decide +kernel
theorem fb_1_8 : one 1 8 = true ∧ gtOne 1 8 = true :=
  both_of_chunks 1 8 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_8_0
    · exact f_1_8_1
  )
theorem c_1_8 : one 1 8 = true := fb_1_8.1
theorem g_1_8 : gtOne 1 8 = true := fb_1_8.2

theorem f_1_9_0 : (chunkOf (Low6960Gate.gateList 1 9) 0).all (fF 1 9) = true := by decide +kernel
theorem f_1_9_1 : (chunkOf (Low6960Gate.gateList 1 9) 1).all (fF 1 9) = true := by decide +kernel
theorem fb_1_9 : one 1 9 = true ∧ gtOne 1 9 = true :=
  both_of_chunks 1 9 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_9_0
    · exact f_1_9_1
  )
theorem c_1_9 : one 1 9 = true := fb_1_9.1
theorem g_1_9 : gtOne 1 9 = true := fb_1_9.2

theorem f_1_10_0 : (chunkOf (Low6960Gate.gateList 1 10) 0).all (fF 1 10) = true := by decide +kernel
theorem f_1_10_1 : (chunkOf (Low6960Gate.gateList 1 10) 1).all (fF 1 10) = true := by decide +kernel
theorem fb_1_10 : one 1 10 = true ∧ gtOne 1 10 = true :=
  both_of_chunks 1 10 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_10_0
    · exact f_1_10_1
  )
theorem c_1_10 : one 1 10 = true := fb_1_10.1
theorem g_1_10 : gtOne 1 10 = true := fb_1_10.2

theorem f_1_11_0 : (chunkOf (Low6960Gate.gateList 1 11) 0).all (fF 1 11) = true := by decide +kernel
theorem f_1_11_1 : (chunkOf (Low6960Gate.gateList 1 11) 1).all (fF 1 11) = true := by decide +kernel
theorem fb_1_11 : one 1 11 = true ∧ gtOne 1 11 = true :=
  both_of_chunks 1 11 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_11_0
    · exact f_1_11_1
  )
theorem c_1_11 : one 1 11 = true := fb_1_11.1
theorem g_1_11 : gtOne 1 11 = true := fb_1_11.2

end Gate61Fin
