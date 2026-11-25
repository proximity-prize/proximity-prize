import ProximityPrize.SubmissionLower.G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_8_7_0 : (chunkOf (Low6966Gate.gateList 8 7) 0).all (fF 8 7) = true := by decide +kernel
theorem fb_8_7 : one 8 7 = true ∧ gtOne 8 7 = true :=
  both_of_chunks 8 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_7_0
  )
theorem f_8_8_0 : (chunkOf (Low6966Gate.gateList 8 8) 0).all (fF 8 8) = true := by decide +kernel
theorem fb_8_8 : one 8 8 = true ∧ gtOne 8 8 = true :=
  both_of_chunks 8 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_8_0
  )
theorem f_8_9_0 : (chunkOf (Low6966Gate.gateList 8 9) 0).all (fF 8 9) = true := by decide +kernel
theorem fb_8_9 : one 8 9 = true ∧ gtOne 8 9 = true :=
  both_of_chunks 8 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_9_0
  )
theorem f_8_10_0 : (chunkOf (Low6966Gate.gateList 8 10) 0).all (fF 8 10) = true := by decide +kernel
theorem fb_8_10 : one 8 10 = true ∧ gtOne 8 10 = true :=
  both_of_chunks 8 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_10_0
  )
theorem f_8_11_0 : (chunkOf (Low6966Gate.gateList 8 11) 0).all (fF 8 11) = true := by decide +kernel
theorem fb_8_11 : one 8 11 = true ∧ gtOne 8 11 = true :=
  both_of_chunks 8 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_11_0
  )
theorem f_8_12_0 : (chunkOf (Low6966Gate.gateList 8 12) 0).all (fF 8 12) = true := by decide +kernel
theorem fb_8_12 : one 8 12 = true ∧ gtOne 8 12 = true :=
  both_of_chunks 8 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_12_0
  )
theorem f_8_13_0 : (chunkOf (Low6966Gate.gateList 8 13) 0).all (fF 8 13) = true := by decide +kernel
theorem fb_8_13 : one 8 13 = true ∧ gtOne 8 13 = true :=
  both_of_chunks 8 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_13_0
  )
theorem f_8_14_0 : (chunkOf (Low6966Gate.gateList 8 14) 0).all (fF 8 14) = true := by decide +kernel
theorem fb_8_14 : one 8 14 = true ∧ gtOne 8 14 = true :=
  both_of_chunks 8 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_14_0
  )
end Gate6966Fin
