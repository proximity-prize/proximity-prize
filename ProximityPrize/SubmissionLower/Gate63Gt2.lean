import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_0_7_0 : (chunkOf (Low6960Gate.gateList 0 7) 0).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_1 : (chunkOf (Low6960Gate.gateList 0 7) 1).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_2 : (chunkOf (Low6960Gate.gateList 0 7) 2).all (fF 0 7) = true := by decide +kernel
theorem fb_0_7 : one 0 7 = true ∧ gtOne 0 7 = true :=
  both_of_chunks 0 7 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_7_0
    · exact f_0_7_1
    · exact f_0_7_2
  )
theorem c_0_7 : one 0 7 = true := fb_0_7.1
theorem g_0_7 : gtOne 0 7 = true := fb_0_7.2

theorem f_0_8_0 : (chunkOf (Low6960Gate.gateList 0 8) 0).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_1 : (chunkOf (Low6960Gate.gateList 0 8) 1).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_2 : (chunkOf (Low6960Gate.gateList 0 8) 2).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_3 : (chunkOf (Low6960Gate.gateList 0 8) 3).all (fF 0 8) = true := by decide +kernel
theorem fb_0_8 : one 0 8 = true ∧ gtOne 0 8 = true :=
  both_of_chunks 0 8 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_8_0
    · exact f_0_8_1
    · exact f_0_8_2
    · exact f_0_8_3
  )
theorem c_0_8 : one 0 8 = true := fb_0_8.1
theorem g_0_8 : gtOne 0 8 = true := fb_0_8.2

end Gate61Fin
