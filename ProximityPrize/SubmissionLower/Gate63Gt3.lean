import ProximityPrize.SubmissionLower.Gate63Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem f_0_9_0 : (chunkOf (Low6960Gate.gateList 0 9) 0).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_1 : (chunkOf (Low6960Gate.gateList 0 9) 1).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_2 : (chunkOf (Low6960Gate.gateList 0 9) 2).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_3 : (chunkOf (Low6960Gate.gateList 0 9) 3).all (fF 0 9) = true := by decide +kernel
theorem fb_0_9 : one 0 9 = true ∧ gtOne 0 9 = true :=
  both_of_chunks 0 9 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_9_0
    · exact f_0_9_1
    · exact f_0_9_2
    · exact f_0_9_3
  )
theorem c_0_9 : one 0 9 = true := fb_0_9.1
theorem g_0_9 : gtOne 0 9 = true := fb_0_9.2

theorem f_0_10_0 : (chunkOf (Low6960Gate.gateList 0 10) 0).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_1 : (chunkOf (Low6960Gate.gateList 0 10) 1).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_2 : (chunkOf (Low6960Gate.gateList 0 10) 2).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_3 : (chunkOf (Low6960Gate.gateList 0 10) 3).all (fF 0 10) = true := by decide +kernel
theorem fb_0_10 : one 0 10 = true ∧ gtOne 0 10 = true :=
  both_of_chunks 0 10 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_10_0
    · exact f_0_10_1
    · exact f_0_10_2
    · exact f_0_10_3
  )
theorem c_0_10 : one 0 10 = true := fb_0_10.1
theorem g_0_10 : gtOne 0 10 = true := fb_0_10.2

end Gate61Fin
