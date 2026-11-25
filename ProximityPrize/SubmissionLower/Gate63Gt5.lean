import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_0_13_0 : (chunkOf (Low6960Gate.gateList 0 13) 0).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_1 : (chunkOf (Low6960Gate.gateList 0 13) 1).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_2 : (chunkOf (Low6960Gate.gateList 0 13) 2).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_3 : (chunkOf (Low6960Gate.gateList 0 13) 3).all (fF 0 13) = true := by decide +kernel
theorem fb_0_13 : one 0 13 = true ∧ gtOne 0 13 = true :=
  both_of_chunks 0 13 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_13_0
    · exact f_0_13_1
    · exact f_0_13_2
    · exact f_0_13_3
  )
theorem c_0_13 : one 0 13 = true := fb_0_13.1
theorem g_0_13 : gtOne 0 13 = true := fb_0_13.2

theorem f_0_14_0 : (chunkOf (Low6960Gate.gateList 0 14) 0).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_1 : (chunkOf (Low6960Gate.gateList 0 14) 1).all (fF 0 14) = true := by decide +kernel
theorem fb_0_14 : one 0 14 = true ∧ gtOne 0 14 = true :=
  both_of_chunks 0 14 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_14_0
    · exact f_0_14_1
  )
theorem c_0_14 : one 0 14 = true := fb_0_14.1
theorem g_0_14 : gtOne 0 14 = true := fb_0_14.2

theorem f_1_2_0 : (chunkOf (Low6960Gate.gateList 1 2) 0).all (fF 1 2) = true := by decide +kernel
theorem fb_1_2 : one 1 2 = true ∧ gtOne 1 2 = true :=
  both_of_chunks 1 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_2_0
  )
theorem c_1_2 : one 1 2 = true := fb_1_2.1
theorem g_1_2 : gtOne 1 2 = true := fb_1_2.2

theorem f_1_3_0 : (chunkOf (Low6960Gate.gateList 1 3) 0).all (fF 1 3) = true := by decide +kernel
theorem fb_1_3 : one 1 3 = true ∧ gtOne 1 3 = true :=
  both_of_chunks 1 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_3_0
  )
theorem c_1_3 : one 1 3 = true := fb_1_3.1
theorem g_1_3 : gtOne 1 3 = true := fb_1_3.2

theorem f_1_4_0 : (chunkOf (Low6960Gate.gateList 1 4) 0).all (fF 1 4) = true := by decide +kernel
theorem fb_1_4 : one 1 4 = true ∧ gtOne 1 4 = true :=
  both_of_chunks 1 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_4_0
  )
theorem c_1_4 : one 1 4 = true := fb_1_4.1
theorem g_1_4 : gtOne 1 4 = true := fb_1_4.2

end Gate61Fin
