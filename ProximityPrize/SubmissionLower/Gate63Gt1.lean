import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_0_5_0 : (chunkOf (Low6960Gate.gateList 0 5) 0).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_1 : (chunkOf (Low6960Gate.gateList 0 5) 1).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_2 : (chunkOf (Low6960Gate.gateList 0 5) 2).all (fF 0 5) = true := by decide +kernel
theorem fb_0_5 : one 0 5 = true ∧ gtOne 0 5 = true :=
  both_of_chunks 0 5 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_5_0
    · exact f_0_5_1
    · exact f_0_5_2
  )
theorem c_0_5 : one 0 5 = true := fb_0_5.1
theorem g_0_5 : gtOne 0 5 = true := fb_0_5.2

theorem f_0_6_0 : (chunkOf (Low6960Gate.gateList 0 6) 0).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_1 : (chunkOf (Low6960Gate.gateList 0 6) 1).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_2 : (chunkOf (Low6960Gate.gateList 0 6) 2).all (fF 0 6) = true := by decide +kernel
theorem fb_0_6 : one 0 6 = true ∧ gtOne 0 6 = true :=
  both_of_chunks 0 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_6_0
    · exact f_0_6_1
    · exact f_0_6_2
  )
theorem c_0_6 : one 0 6 = true := fb_0_6.1
theorem g_0_6 : gtOne 0 6 = true := fb_0_6.2

end Gate61Fin
