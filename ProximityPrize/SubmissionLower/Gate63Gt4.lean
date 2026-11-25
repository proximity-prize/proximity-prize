import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_0_11_0 : (chunkOf (Low6960Gate.gateList 0 11) 0).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_1 : (chunkOf (Low6960Gate.gateList 0 11) 1).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_2 : (chunkOf (Low6960Gate.gateList 0 11) 2).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_3 : (chunkOf (Low6960Gate.gateList 0 11) 3).all (fF 0 11) = true := by decide +kernel
theorem fb_0_11 : one 0 11 = true ∧ gtOne 0 11 = true :=
  both_of_chunks 0 11 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_11_0
    · exact f_0_11_1
    · exact f_0_11_2
    · exact f_0_11_3
  )
theorem c_0_11 : one 0 11 = true := fb_0_11.1
theorem g_0_11 : gtOne 0 11 = true := fb_0_11.2

theorem f_0_12_0 : (chunkOf (Low6960Gate.gateList 0 12) 0).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_1 : (chunkOf (Low6960Gate.gateList 0 12) 1).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_2 : (chunkOf (Low6960Gate.gateList 0 12) 2).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_3 : (chunkOf (Low6960Gate.gateList 0 12) 3).all (fF 0 12) = true := by decide +kernel
theorem fb_0_12 : one 0 12 = true ∧ gtOne 0 12 = true :=
  both_of_chunks 0 12 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_12_0
    · exact f_0_12_1
    · exact f_0_12_2
    · exact f_0_12_3
  )
theorem c_0_12 : one 0 12 = true := fb_0_12.1
theorem g_0_12 : gtOne 0 12 = true := fb_0_12.2

end Gate61Fin
