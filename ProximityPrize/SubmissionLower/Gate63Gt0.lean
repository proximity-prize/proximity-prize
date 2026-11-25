import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_0_2_0 : (chunkOf (Low6960Gate.gateList 0 2) 0).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_1 : (chunkOf (Low6960Gate.gateList 0 2) 1).all (fF 0 2) = true := by decide +kernel
theorem fb_0_2 : one 0 2 = true ∧ gtOne 0 2 = true :=
  both_of_chunks 0 2 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_2_0
    · exact f_0_2_1
  )
theorem c_0_2 : one 0 2 = true := fb_0_2.1
theorem g_0_2 : gtOne 0 2 = true := fb_0_2.2

theorem f_0_3_0 : (chunkOf (Low6960Gate.gateList 0 3) 0).all (fF 0 3) = true := by decide +kernel
theorem f_0_3_1 : (chunkOf (Low6960Gate.gateList 0 3) 1).all (fF 0 3) = true := by decide +kernel
theorem fb_0_3 : one 0 3 = true ∧ gtOne 0 3 = true :=
  both_of_chunks 0 3 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_3_0
    · exact f_0_3_1
  )
theorem c_0_3 : one 0 3 = true := fb_0_3.1
theorem g_0_3 : gtOne 0 3 = true := fb_0_3.2

theorem f_0_4_0 : (chunkOf (Low6960Gate.gateList 0 4) 0).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_1 : (chunkOf (Low6960Gate.gateList 0 4) 1).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_2 : (chunkOf (Low6960Gate.gateList 0 4) 2).all (fF 0 4) = true := by decide +kernel
theorem fb_0_4 : one 0 4 = true ∧ gtOne 0 4 = true :=
  both_of_chunks 0 4 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_4_0
    · exact f_0_4_1
    · exact f_0_4_2
  )
theorem c_0_4 : one 0 4 = true := fb_0_4.1
theorem g_0_4 : gtOne 0 4 = true := fb_0_4.2

end Gate61Fin
