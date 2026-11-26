import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.G6966Check0

section Merged6967_G6966Check1
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_1_2_0 : (chunkOf (Low6966Gate.gateList 1 2) 0).all (fF 1 2) = true := by decide +kernel
theorem fb_1_2 : one 1 2 = true ∧ gtOne 1 2 = true :=
  both_of_chunks 1 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_2_0
  )
theorem f_1_3_0 : (chunkOf (Low6966Gate.gateList 1 3) 0).all (fF 1 3) = true := by decide +kernel
theorem f_1_3_1 : (chunkOf (Low6966Gate.gateList 1 3) 1).all (fF 1 3) = true := by decide +kernel
theorem fb_1_3 : one 1 3 = true ∧ gtOne 1 3 = true :=
  both_of_chunks 1 3 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_3_0
    · exact f_1_3_1
  )
theorem f_1_4_0 : (chunkOf (Low6966Gate.gateList 1 4) 0).all (fF 1 4) = true := by decide +kernel
theorem f_1_4_1 : (chunkOf (Low6966Gate.gateList 1 4) 1).all (fF 1 4) = true := by decide +kernel
theorem fb_1_4 : one 1 4 = true ∧ gtOne 1 4 = true :=
  both_of_chunks 1 4 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_4_0
    · exact f_1_4_1
  )
theorem f_1_5_0 : (chunkOf (Low6966Gate.gateList 1 5) 0).all (fF 1 5) = true := by decide +kernel
theorem f_1_5_1 : (chunkOf (Low6966Gate.gateList 1 5) 1).all (fF 1 5) = true := by decide +kernel
theorem f_1_5_2 : (chunkOf (Low6966Gate.gateList 1 5) 2).all (fF 1 5) = true := by decide +kernel
theorem fb_1_5 : one 1 5 = true ∧ gtOne 1 5 = true :=
  both_of_chunks 1 5 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_5_0
    · exact f_1_5_1
    · exact f_1_5_2
  )
theorem f_1_6_0 : (chunkOf (Low6966Gate.gateList 1 6) 0).all (fF 1 6) = true := by decide +kernel
theorem f_1_6_1 : (chunkOf (Low6966Gate.gateList 1 6) 1).all (fF 1 6) = true := by decide +kernel
theorem f_1_6_2 : (chunkOf (Low6966Gate.gateList 1 6) 2).all (fF 1 6) = true := by decide +kernel
theorem fb_1_6 : one 1 6 = true ∧ gtOne 1 6 = true :=
  both_of_chunks 1 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_6_0
    · exact f_1_6_1
    · exact f_1_6_2
  )
theorem f_1_7_0 : (chunkOf (Low6966Gate.gateList 1 7) 0).all (fF 1 7) = true := by decide +kernel
theorem f_1_7_1 : (chunkOf (Low6966Gate.gateList 1 7) 1).all (fF 1 7) = true := by decide +kernel
theorem f_1_7_2 : (chunkOf (Low6966Gate.gateList 1 7) 2).all (fF 1 7) = true := by decide +kernel
theorem f_1_7_3 : (chunkOf (Low6966Gate.gateList 1 7) 3).all (fF 1 7) = true := by decide +kernel
theorem fb_1_7 : one 1 7 = true ∧ gtOne 1 7 = true :=
  both_of_chunks 1 7 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_7_0
    · exact f_1_7_1
    · exact f_1_7_2
    · exact f_1_7_3
  )
theorem f_1_8_0 : (chunkOf (Low6966Gate.gateList 1 8) 0).all (fF 1 8) = true := by decide +kernel
theorem f_1_8_1 : (chunkOf (Low6966Gate.gateList 1 8) 1).all (fF 1 8) = true := by decide +kernel
theorem f_1_8_2 : (chunkOf (Low6966Gate.gateList 1 8) 2).all (fF 1 8) = true := by decide +kernel
theorem f_1_8_3 : (chunkOf (Low6966Gate.gateList 1 8) 3).all (fF 1 8) = true := by decide +kernel
theorem fb_1_8 : one 1 8 = true ∧ gtOne 1 8 = true :=
  both_of_chunks 1 8 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_8_0
    · exact f_1_8_1
    · exact f_1_8_2
    · exact f_1_8_3
  )
theorem f_1_9_0 : (chunkOf (Low6966Gate.gateList 1 9) 0).all (fF 1 9) = true := by decide +kernel
theorem f_1_9_1 : (chunkOf (Low6966Gate.gateList 1 9) 1).all (fF 1 9) = true := by decide +kernel
theorem f_1_9_2 : (chunkOf (Low6966Gate.gateList 1 9) 2).all (fF 1 9) = true := by decide +kernel
theorem f_1_9_3 : (chunkOf (Low6966Gate.gateList 1 9) 3).all (fF 1 9) = true := by decide +kernel
theorem fb_1_9 : one 1 9 = true ∧ gtOne 1 9 = true :=
  both_of_chunks 1 9 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_9_0
    · exact f_1_9_1
    · exact f_1_9_2
    · exact f_1_9_3
  )
theorem f_1_10_0 : (chunkOf (Low6966Gate.gateList 1 10) 0).all (fF 1 10) = true := by decide +kernel
theorem f_1_10_1 : (chunkOf (Low6966Gate.gateList 1 10) 1).all (fF 1 10) = true := by decide +kernel
theorem f_1_10_2 : (chunkOf (Low6966Gate.gateList 1 10) 2).all (fF 1 10) = true := by decide +kernel
theorem f_1_10_3 : (chunkOf (Low6966Gate.gateList 1 10) 3).all (fF 1 10) = true := by decide +kernel
theorem f_1_10_4 : (chunkOf (Low6966Gate.gateList 1 10) 4).all (fF 1 10) = true := by decide +kernel
theorem fb_1_10 : one 1 10 = true ∧ gtOne 1 10 = true :=
  both_of_chunks 1 10 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_10_0
    · exact f_1_10_1
    · exact f_1_10_2
    · exact f_1_10_3
    · exact f_1_10_4
  )
theorem f_1_11_0 : (chunkOf (Low6966Gate.gateList 1 11) 0).all (fF 1 11) = true := by decide +kernel
theorem f_1_11_1 : (chunkOf (Low6966Gate.gateList 1 11) 1).all (fF 1 11) = true := by decide +kernel
theorem f_1_11_2 : (chunkOf (Low6966Gate.gateList 1 11) 2).all (fF 1 11) = true := by decide +kernel
theorem f_1_11_3 : (chunkOf (Low6966Gate.gateList 1 11) 3).all (fF 1 11) = true := by decide +kernel
theorem f_1_11_4 : (chunkOf (Low6966Gate.gateList 1 11) 4).all (fF 1 11) = true := by decide +kernel
theorem fb_1_11 : one 1 11 = true ∧ gtOne 1 11 = true :=
  both_of_chunks 1 11 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_11_0
    · exact f_1_11_1
    · exact f_1_11_2
    · exact f_1_11_3
    · exact f_1_11_4
  )
theorem f_1_12_0 : (chunkOf (Low6966Gate.gateList 1 12) 0).all (fF 1 12) = true := by decide +kernel
theorem f_1_12_1 : (chunkOf (Low6966Gate.gateList 1 12) 1).all (fF 1 12) = true := by decide +kernel
theorem f_1_12_2 : (chunkOf (Low6966Gate.gateList 1 12) 2).all (fF 1 12) = true := by decide +kernel
theorem f_1_12_3 : (chunkOf (Low6966Gate.gateList 1 12) 3).all (fF 1 12) = true := by decide +kernel
theorem f_1_12_4 : (chunkOf (Low6966Gate.gateList 1 12) 4).all (fF 1 12) = true := by decide +kernel
theorem fb_1_12 : one 1 12 = true ∧ gtOne 1 12 = true :=
  both_of_chunks 1 12 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_12_0
    · exact f_1_12_1
    · exact f_1_12_2
    · exact f_1_12_3
    · exact f_1_12_4
  )
theorem f_1_13_0 : (chunkOf (Low6966Gate.gateList 1 13) 0).all (fF 1 13) = true := by decide +kernel
theorem f_1_13_1 : (chunkOf (Low6966Gate.gateList 1 13) 1).all (fF 1 13) = true := by decide +kernel
theorem f_1_13_2 : (chunkOf (Low6966Gate.gateList 1 13) 2).all (fF 1 13) = true := by decide +kernel
theorem f_1_13_3 : (chunkOf (Low6966Gate.gateList 1 13) 3).all (fF 1 13) = true := by decide +kernel
theorem f_1_13_4 : (chunkOf (Low6966Gate.gateList 1 13) 4).all (fF 1 13) = true := by decide +kernel
theorem fb_1_13 : one 1 13 = true ∧ gtOne 1 13 = true :=
  both_of_chunks 1 13 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_13_0
    · exact f_1_13_1
    · exact f_1_13_2
    · exact f_1_13_3
    · exact f_1_13_4
  )
theorem f_1_14_0 : (chunkOf (Low6966Gate.gateList 1 14) 0).all (fF 1 14) = true := by decide +kernel
theorem f_1_14_1 : (chunkOf (Low6966Gate.gateList 1 14) 1).all (fF 1 14) = true := by decide +kernel
theorem f_1_14_2 : (chunkOf (Low6966Gate.gateList 1 14) 2).all (fF 1 14) = true := by decide +kernel
theorem f_1_14_3 : (chunkOf (Low6966Gate.gateList 1 14) 3).all (fF 1 14) = true := by decide +kernel
theorem f_1_14_4 : (chunkOf (Low6966Gate.gateList 1 14) 4).all (fF 1 14) = true := by decide +kernel
theorem fb_1_14 : one 1 14 = true ∧ gtOne 1 14 = true :=
  both_of_chunks 1 14 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_14_0
    · exact f_1_14_1
    · exact f_1_14_2
    · exact f_1_14_3
    · exact f_1_14_4
  )
end Gate6966Fin

end Merged6967_G6966Check1

section Merged6967_G6966Check10
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_10_7_0 : (chunkOf (Low6966Gate.gateList 10 7) 0).all (fF 10 7) = true := by decide +kernel
theorem fb_10_7 : one 10 7 = true ∧ gtOne 10 7 = true :=
  both_of_chunks 10 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_7_0
  )
theorem f_10_8_0 : (chunkOf (Low6966Gate.gateList 10 8) 0).all (fF 10 8) = true := by decide +kernel
theorem fb_10_8 : one 10 8 = true ∧ gtOne 10 8 = true :=
  both_of_chunks 10 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_8_0
  )
theorem f_10_9_0 : (chunkOf (Low6966Gate.gateList 10 9) 0).all (fF 10 9) = true := by decide +kernel
theorem fb_10_9 : one 10 9 = true ∧ gtOne 10 9 = true :=
  both_of_chunks 10 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_9_0
  )
theorem f_10_10_0 : (chunkOf (Low6966Gate.gateList 10 10) 0).all (fF 10 10) = true := by decide +kernel
theorem fb_10_10 : one 10 10 = true ∧ gtOne 10 10 = true :=
  both_of_chunks 10 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_10_0
  )
theorem f_10_11_0 : (chunkOf (Low6966Gate.gateList 10 11) 0).all (fF 10 11) = true := by decide +kernel
theorem fb_10_11 : one 10 11 = true ∧ gtOne 10 11 = true :=
  both_of_chunks 10 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_11_0
  )
theorem f_10_12_0 : (chunkOf (Low6966Gate.gateList 10 12) 0).all (fF 10 12) = true := by decide +kernel
theorem fb_10_12 : one 10 12 = true ∧ gtOne 10 12 = true :=
  both_of_chunks 10 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_12_0
  )
theorem f_10_13_0 : (chunkOf (Low6966Gate.gateList 10 13) 0).all (fF 10 13) = true := by decide +kernel
theorem fb_10_13 : one 10 13 = true ∧ gtOne 10 13 = true :=
  both_of_chunks 10 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_13_0
  )
theorem f_10_14_0 : (chunkOf (Low6966Gate.gateList 10 14) 0).all (fF 10 14) = true := by decide +kernel
theorem fb_10_14 : one 10 14 = true ∧ gtOne 10 14 = true :=
  both_of_chunks 10 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_14_0
  )
end Gate6966Fin

end Merged6967_G6966Check10

section Merged6967_G6966Check11
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_11_9_0 : (chunkOf (Low6966Gate.gateList 11 9) 0).all (fF 11 9) = true := by decide +kernel
theorem fb_11_9 : one 11 9 = true ∧ gtOne 11 9 = true :=
  both_of_chunks 11 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_9_0
  )
theorem f_11_10_0 : (chunkOf (Low6966Gate.gateList 11 10) 0).all (fF 11 10) = true := by decide +kernel
theorem fb_11_10 : one 11 10 = true ∧ gtOne 11 10 = true :=
  both_of_chunks 11 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_10_0
  )
theorem f_11_11_0 : (chunkOf (Low6966Gate.gateList 11 11) 0).all (fF 11 11) = true := by decide +kernel
theorem fb_11_11 : one 11 11 = true ∧ gtOne 11 11 = true :=
  both_of_chunks 11 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_11_0
  )
theorem f_11_12_0 : (chunkOf (Low6966Gate.gateList 11 12) 0).all (fF 11 12) = true := by decide +kernel
theorem fb_11_12 : one 11 12 = true ∧ gtOne 11 12 = true :=
  both_of_chunks 11 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_12_0
  )
theorem f_11_13_0 : (chunkOf (Low6966Gate.gateList 11 13) 0).all (fF 11 13) = true := by decide +kernel
theorem fb_11_13 : one 11 13 = true ∧ gtOne 11 13 = true :=
  both_of_chunks 11 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_13_0
  )
theorem f_11_14_0 : (chunkOf (Low6966Gate.gateList 11 14) 0).all (fF 11 14) = true := by decide +kernel
theorem fb_11_14 : one 11 14 = true ∧ gtOne 11 14 = true :=
  both_of_chunks 11 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_14_0
  )
end Gate6966Fin

end Merged6967_G6966Check11

section Merged6967_G6966Check12
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_12_12_0 : (chunkOf (Low6966Gate.gateList 12 12) 0).all (fF 12 12) = true := by decide +kernel
theorem fb_12_12 : one 12 12 = true ∧ gtOne 12 12 = true :=
  both_of_chunks 12 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_12_0
  )
theorem f_12_13_0 : (chunkOf (Low6966Gate.gateList 12 13) 0).all (fF 12 13) = true := by decide +kernel
theorem fb_12_13 : one 12 13 = true ∧ gtOne 12 13 = true :=
  both_of_chunks 12 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_13_0
  )
end Gate6966Fin

end Merged6967_G6966Check12

section Merged6967_G6966Check2
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_2_2_0 : (chunkOf (Low6966Gate.gateList 2 2) 0).all (fF 2 2) = true := by decide +kernel
theorem fb_2_2 : one 2 2 = true ∧ gtOne 2 2 = true :=
  both_of_chunks 2 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_2_0
  )
theorem f_2_3_0 : (chunkOf (Low6966Gate.gateList 2 3) 0).all (fF 2 3) = true := by decide +kernel
theorem fb_2_3 : one 2 3 = true ∧ gtOne 2 3 = true :=
  both_of_chunks 2 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_3_0
  )
theorem f_2_4_0 : (chunkOf (Low6966Gate.gateList 2 4) 0).all (fF 2 4) = true := by decide +kernel
theorem f_2_4_1 : (chunkOf (Low6966Gate.gateList 2 4) 1).all (fF 2 4) = true := by decide +kernel
theorem fb_2_4 : one 2 4 = true ∧ gtOne 2 4 = true :=
  both_of_chunks 2 4 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_4_0
    · exact f_2_4_1
  )
theorem f_2_5_0 : (chunkOf (Low6966Gate.gateList 2 5) 0).all (fF 2 5) = true := by decide +kernel
theorem f_2_5_1 : (chunkOf (Low6966Gate.gateList 2 5) 1).all (fF 2 5) = true := by decide +kernel
theorem f_2_5_2 : (chunkOf (Low6966Gate.gateList 2 5) 2).all (fF 2 5) = true := by decide +kernel
theorem fb_2_5 : one 2 5 = true ∧ gtOne 2 5 = true :=
  both_of_chunks 2 5 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_5_0
    · exact f_2_5_1
    · exact f_2_5_2
  )
theorem f_2_6_0 : (chunkOf (Low6966Gate.gateList 2 6) 0).all (fF 2 6) = true := by decide +kernel
theorem f_2_6_1 : (chunkOf (Low6966Gate.gateList 2 6) 1).all (fF 2 6) = true := by decide +kernel
theorem f_2_6_2 : (chunkOf (Low6966Gate.gateList 2 6) 2).all (fF 2 6) = true := by decide +kernel
theorem fb_2_6 : one 2 6 = true ∧ gtOne 2 6 = true :=
  both_of_chunks 2 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_6_0
    · exact f_2_6_1
    · exact f_2_6_2
  )
theorem f_2_7_0 : (chunkOf (Low6966Gate.gateList 2 7) 0).all (fF 2 7) = true := by decide +kernel
theorem f_2_7_1 : (chunkOf (Low6966Gate.gateList 2 7) 1).all (fF 2 7) = true := by decide +kernel
theorem f_2_7_2 : (chunkOf (Low6966Gate.gateList 2 7) 2).all (fF 2 7) = true := by decide +kernel
theorem f_2_7_3 : (chunkOf (Low6966Gate.gateList 2 7) 3).all (fF 2 7) = true := by decide +kernel
theorem fb_2_7 : one 2 7 = true ∧ gtOne 2 7 = true :=
  both_of_chunks 2 7 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_7_0
    · exact f_2_7_1
    · exact f_2_7_2
    · exact f_2_7_3
  )
theorem f_2_8_0 : (chunkOf (Low6966Gate.gateList 2 8) 0).all (fF 2 8) = true := by decide +kernel
theorem f_2_8_1 : (chunkOf (Low6966Gate.gateList 2 8) 1).all (fF 2 8) = true := by decide +kernel
theorem f_2_8_2 : (chunkOf (Low6966Gate.gateList 2 8) 2).all (fF 2 8) = true := by decide +kernel
theorem f_2_8_3 : (chunkOf (Low6966Gate.gateList 2 8) 3).all (fF 2 8) = true := by decide +kernel
theorem fb_2_8 : one 2 8 = true ∧ gtOne 2 8 = true :=
  both_of_chunks 2 8 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_8_0
    · exact f_2_8_1
    · exact f_2_8_2
    · exact f_2_8_3
  )
theorem f_2_9_0 : (chunkOf (Low6966Gate.gateList 2 9) 0).all (fF 2 9) = true := by decide +kernel
theorem f_2_9_1 : (chunkOf (Low6966Gate.gateList 2 9) 1).all (fF 2 9) = true := by decide +kernel
theorem f_2_9_2 : (chunkOf (Low6966Gate.gateList 2 9) 2).all (fF 2 9) = true := by decide +kernel
theorem f_2_9_3 : (chunkOf (Low6966Gate.gateList 2 9) 3).all (fF 2 9) = true := by decide +kernel
theorem f_2_9_4 : (chunkOf (Low6966Gate.gateList 2 9) 4).all (fF 2 9) = true := by decide +kernel
theorem fb_2_9 : one 2 9 = true ∧ gtOne 2 9 = true :=
  both_of_chunks 2 9 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_9_0
    · exact f_2_9_1
    · exact f_2_9_2
    · exact f_2_9_3
    · exact f_2_9_4
  )
theorem f_2_10_0 : (chunkOf (Low6966Gate.gateList 2 10) 0).all (fF 2 10) = true := by decide +kernel
theorem f_2_10_1 : (chunkOf (Low6966Gate.gateList 2 10) 1).all (fF 2 10) = true := by decide +kernel
theorem f_2_10_2 : (chunkOf (Low6966Gate.gateList 2 10) 2).all (fF 2 10) = true := by decide +kernel
theorem f_2_10_3 : (chunkOf (Low6966Gate.gateList 2 10) 3).all (fF 2 10) = true := by decide +kernel
theorem f_2_10_4 : (chunkOf (Low6966Gate.gateList 2 10) 4).all (fF 2 10) = true := by decide +kernel
theorem fb_2_10 : one 2 10 = true ∧ gtOne 2 10 = true :=
  both_of_chunks 2 10 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_10_0
    · exact f_2_10_1
    · exact f_2_10_2
    · exact f_2_10_3
    · exact f_2_10_4
  )
theorem f_2_11_0 : (chunkOf (Low6966Gate.gateList 2 11) 0).all (fF 2 11) = true := by decide +kernel
theorem f_2_11_1 : (chunkOf (Low6966Gate.gateList 2 11) 1).all (fF 2 11) = true := by decide +kernel
theorem f_2_11_2 : (chunkOf (Low6966Gate.gateList 2 11) 2).all (fF 2 11) = true := by decide +kernel
theorem f_2_11_3 : (chunkOf (Low6966Gate.gateList 2 11) 3).all (fF 2 11) = true := by decide +kernel
theorem f_2_11_4 : (chunkOf (Low6966Gate.gateList 2 11) 4).all (fF 2 11) = true := by decide +kernel
theorem fb_2_11 : one 2 11 = true ∧ gtOne 2 11 = true :=
  both_of_chunks 2 11 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_11_0
    · exact f_2_11_1
    · exact f_2_11_2
    · exact f_2_11_3
    · exact f_2_11_4
  )
theorem f_2_12_0 : (chunkOf (Low6966Gate.gateList 2 12) 0).all (fF 2 12) = true := by decide +kernel
theorem f_2_12_1 : (chunkOf (Low6966Gate.gateList 2 12) 1).all (fF 2 12) = true := by decide +kernel
theorem f_2_12_2 : (chunkOf (Low6966Gate.gateList 2 12) 2).all (fF 2 12) = true := by decide +kernel
theorem f_2_12_3 : (chunkOf (Low6966Gate.gateList 2 12) 3).all (fF 2 12) = true := by decide +kernel
theorem f_2_12_4 : (chunkOf (Low6966Gate.gateList 2 12) 4).all (fF 2 12) = true := by decide +kernel
theorem fb_2_12 : one 2 12 = true ∧ gtOne 2 12 = true :=
  both_of_chunks 2 12 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_12_0
    · exact f_2_12_1
    · exact f_2_12_2
    · exact f_2_12_3
    · exact f_2_12_4
  )
theorem f_2_13_0 : (chunkOf (Low6966Gate.gateList 2 13) 0).all (fF 2 13) = true := by decide +kernel
theorem f_2_13_1 : (chunkOf (Low6966Gate.gateList 2 13) 1).all (fF 2 13) = true := by decide +kernel
theorem f_2_13_2 : (chunkOf (Low6966Gate.gateList 2 13) 2).all (fF 2 13) = true := by decide +kernel
theorem f_2_13_3 : (chunkOf (Low6966Gate.gateList 2 13) 3).all (fF 2 13) = true := by decide +kernel
theorem f_2_13_4 : (chunkOf (Low6966Gate.gateList 2 13) 4).all (fF 2 13) = true := by decide +kernel
theorem fb_2_13 : one 2 13 = true ∧ gtOne 2 13 = true :=
  both_of_chunks 2 13 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_13_0
    · exact f_2_13_1
    · exact f_2_13_2
    · exact f_2_13_3
    · exact f_2_13_4
  )
theorem f_2_14_0 : (chunkOf (Low6966Gate.gateList 2 14) 0).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_1 : (chunkOf (Low6966Gate.gateList 2 14) 1).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_2 : (chunkOf (Low6966Gate.gateList 2 14) 2).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_3 : (chunkOf (Low6966Gate.gateList 2 14) 3).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_4 : (chunkOf (Low6966Gate.gateList 2 14) 4).all (fF 2 14) = true := by decide +kernel
theorem f_2_14_5 : (chunkOf (Low6966Gate.gateList 2 14) 5).all (fF 2 14) = true := by decide +kernel
theorem fb_2_14 : one 2 14 = true ∧ gtOne 2 14 = true :=
  both_of_chunks 2 14 6 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_14_0
    · exact f_2_14_1
    · exact f_2_14_2
    · exact f_2_14_3
    · exact f_2_14_4
    · exact f_2_14_5
  )
end Gate6966Fin

end Merged6967_G6966Check2

section Merged6967_G6966Check3
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_3_2_0 : (chunkOf (Low6966Gate.gateList 3 2) 0).all (fF 3 2) = true := by decide +kernel
theorem fb_3_2 : one 3 2 = true ∧ gtOne 3 2 = true :=
  both_of_chunks 3 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_2_0
  )
theorem f_3_3_0 : (chunkOf (Low6966Gate.gateList 3 3) 0).all (fF 3 3) = true := by decide +kernel
theorem fb_3_3 : one 3 3 = true ∧ gtOne 3 3 = true :=
  both_of_chunks 3 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_3_0
  )
theorem f_3_4_0 : (chunkOf (Low6966Gate.gateList 3 4) 0).all (fF 3 4) = true := by decide +kernel
theorem f_3_4_1 : (chunkOf (Low6966Gate.gateList 3 4) 1).all (fF 3 4) = true := by decide +kernel
theorem fb_3_4 : one 3 4 = true ∧ gtOne 3 4 = true :=
  both_of_chunks 3 4 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_4_0
    · exact f_3_4_1
  )
theorem f_3_5_0 : (chunkOf (Low6966Gate.gateList 3 5) 0).all (fF 3 5) = true := by decide +kernel
theorem f_3_5_1 : (chunkOf (Low6966Gate.gateList 3 5) 1).all (fF 3 5) = true := by decide +kernel
theorem fb_3_5 : one 3 5 = true ∧ gtOne 3 5 = true :=
  both_of_chunks 3 5 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_5_0
    · exact f_3_5_1
  )
theorem f_3_6_0 : (chunkOf (Low6966Gate.gateList 3 6) 0).all (fF 3 6) = true := by decide +kernel
theorem f_3_6_1 : (chunkOf (Low6966Gate.gateList 3 6) 1).all (fF 3 6) = true := by decide +kernel
theorem f_3_6_2 : (chunkOf (Low6966Gate.gateList 3 6) 2).all (fF 3 6) = true := by decide +kernel
theorem fb_3_6 : one 3 6 = true ∧ gtOne 3 6 = true :=
  both_of_chunks 3 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_6_0
    · exact f_3_6_1
    · exact f_3_6_2
  )
theorem f_3_7_0 : (chunkOf (Low6966Gate.gateList 3 7) 0).all (fF 3 7) = true := by decide +kernel
theorem f_3_7_1 : (chunkOf (Low6966Gate.gateList 3 7) 1).all (fF 3 7) = true := by decide +kernel
theorem f_3_7_2 : (chunkOf (Low6966Gate.gateList 3 7) 2).all (fF 3 7) = true := by decide +kernel
theorem fb_3_7 : one 3 7 = true ∧ gtOne 3 7 = true :=
  both_of_chunks 3 7 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_7_0
    · exact f_3_7_1
    · exact f_3_7_2
  )
theorem f_3_8_0 : (chunkOf (Low6966Gate.gateList 3 8) 0).all (fF 3 8) = true := by decide +kernel
theorem f_3_8_1 : (chunkOf (Low6966Gate.gateList 3 8) 1).all (fF 3 8) = true := by decide +kernel
theorem f_3_8_2 : (chunkOf (Low6966Gate.gateList 3 8) 2).all (fF 3 8) = true := by decide +kernel
theorem fb_3_8 : one 3 8 = true ∧ gtOne 3 8 = true :=
  both_of_chunks 3 8 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_8_0
    · exact f_3_8_1
    · exact f_3_8_2
  )
theorem f_3_9_0 : (chunkOf (Low6966Gate.gateList 3 9) 0).all (fF 3 9) = true := by decide +kernel
theorem f_3_9_1 : (chunkOf (Low6966Gate.gateList 3 9) 1).all (fF 3 9) = true := by decide +kernel
theorem f_3_9_2 : (chunkOf (Low6966Gate.gateList 3 9) 2).all (fF 3 9) = true := by decide +kernel
theorem fb_3_9 : one 3 9 = true ∧ gtOne 3 9 = true :=
  both_of_chunks 3 9 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_9_0
    · exact f_3_9_1
    · exact f_3_9_2
  )
theorem f_3_10_0 : (chunkOf (Low6966Gate.gateList 3 10) 0).all (fF 3 10) = true := by decide +kernel
theorem f_3_10_1 : (chunkOf (Low6966Gate.gateList 3 10) 1).all (fF 3 10) = true := by decide +kernel
theorem f_3_10_2 : (chunkOf (Low6966Gate.gateList 3 10) 2).all (fF 3 10) = true := by decide +kernel
theorem f_3_10_3 : (chunkOf (Low6966Gate.gateList 3 10) 3).all (fF 3 10) = true := by decide +kernel
theorem fb_3_10 : one 3 10 = true ∧ gtOne 3 10 = true :=
  both_of_chunks 3 10 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_10_0
    · exact f_3_10_1
    · exact f_3_10_2
    · exact f_3_10_3
  )
theorem f_3_11_0 : (chunkOf (Low6966Gate.gateList 3 11) 0).all (fF 3 11) = true := by decide +kernel
theorem f_3_11_1 : (chunkOf (Low6966Gate.gateList 3 11) 1).all (fF 3 11) = true := by decide +kernel
theorem f_3_11_2 : (chunkOf (Low6966Gate.gateList 3 11) 2).all (fF 3 11) = true := by decide +kernel
theorem f_3_11_3 : (chunkOf (Low6966Gate.gateList 3 11) 3).all (fF 3 11) = true := by decide +kernel
theorem fb_3_11 : one 3 11 = true ∧ gtOne 3 11 = true :=
  both_of_chunks 3 11 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_11_0
    · exact f_3_11_1
    · exact f_3_11_2
    · exact f_3_11_3
  )
theorem f_3_12_0 : (chunkOf (Low6966Gate.gateList 3 12) 0).all (fF 3 12) = true := by decide +kernel
theorem f_3_12_1 : (chunkOf (Low6966Gate.gateList 3 12) 1).all (fF 3 12) = true := by decide +kernel
theorem f_3_12_2 : (chunkOf (Low6966Gate.gateList 3 12) 2).all (fF 3 12) = true := by decide +kernel
theorem f_3_12_3 : (chunkOf (Low6966Gate.gateList 3 12) 3).all (fF 3 12) = true := by decide +kernel
theorem fb_3_12 : one 3 12 = true ∧ gtOne 3 12 = true :=
  both_of_chunks 3 12 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_12_0
    · exact f_3_12_1
    · exact f_3_12_2
    · exact f_3_12_3
  )
theorem f_3_13_0 : (chunkOf (Low6966Gate.gateList 3 13) 0).all (fF 3 13) = true := by decide +kernel
theorem f_3_13_1 : (chunkOf (Low6966Gate.gateList 3 13) 1).all (fF 3 13) = true := by decide +kernel
theorem f_3_13_2 : (chunkOf (Low6966Gate.gateList 3 13) 2).all (fF 3 13) = true := by decide +kernel
theorem f_3_13_3 : (chunkOf (Low6966Gate.gateList 3 13) 3).all (fF 3 13) = true := by decide +kernel
theorem fb_3_13 : one 3 13 = true ∧ gtOne 3 13 = true :=
  both_of_chunks 3 13 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_13_0
    · exact f_3_13_1
    · exact f_3_13_2
    · exact f_3_13_3
  )
theorem f_3_14_0 : (chunkOf (Low6966Gate.gateList 3 14) 0).all (fF 3 14) = true := by decide +kernel
theorem f_3_14_1 : (chunkOf (Low6966Gate.gateList 3 14) 1).all (fF 3 14) = true := by decide +kernel
theorem f_3_14_2 : (chunkOf (Low6966Gate.gateList 3 14) 2).all (fF 3 14) = true := by decide +kernel
theorem f_3_14_3 : (chunkOf (Low6966Gate.gateList 3 14) 3).all (fF 3 14) = true := by decide +kernel
theorem fb_3_14 : one 3 14 = true ∧ gtOne 3 14 = true :=
  both_of_chunks 3 14 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_14_0
    · exact f_3_14_1
    · exact f_3_14_2
    · exact f_3_14_3
  )
end Gate6966Fin

end Merged6967_G6966Check3

section Merged6967_G6966Check4
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_4_3_0 : (chunkOf (Low6966Gate.gateList 4 3) 0).all (fF 4 3) = true := by decide +kernel
theorem fb_4_3 : one 4 3 = true ∧ gtOne 4 3 = true :=
  both_of_chunks 4 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_3_0
  )
theorem f_4_4_0 : (chunkOf (Low6966Gate.gateList 4 4) 0).all (fF 4 4) = true := by decide +kernel
theorem fb_4_4 : one 4 4 = true ∧ gtOne 4 4 = true :=
  both_of_chunks 4 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_4_0
  )
theorem f_4_5_0 : (chunkOf (Low6966Gate.gateList 4 5) 0).all (fF 4 5) = true := by decide +kernel
theorem fb_4_5 : one 4 5 = true ∧ gtOne 4 5 = true :=
  both_of_chunks 4 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_5_0
  )
theorem f_4_6_0 : (chunkOf (Low6966Gate.gateList 4 6) 0).all (fF 4 6) = true := by decide +kernel
theorem f_4_6_1 : (chunkOf (Low6966Gate.gateList 4 6) 1).all (fF 4 6) = true := by decide +kernel
theorem fb_4_6 : one 4 6 = true ∧ gtOne 4 6 = true :=
  both_of_chunks 4 6 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_6_0
    · exact f_4_6_1
  )
theorem f_4_7_0 : (chunkOf (Low6966Gate.gateList 4 7) 0).all (fF 4 7) = true := by decide +kernel
theorem f_4_7_1 : (chunkOf (Low6966Gate.gateList 4 7) 1).all (fF 4 7) = true := by decide +kernel
theorem fb_4_7 : one 4 7 = true ∧ gtOne 4 7 = true :=
  both_of_chunks 4 7 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_7_0
    · exact f_4_7_1
  )
theorem f_4_8_0 : (chunkOf (Low6966Gate.gateList 4 8) 0).all (fF 4 8) = true := by decide +kernel
theorem f_4_8_1 : (chunkOf (Low6966Gate.gateList 4 8) 1).all (fF 4 8) = true := by decide +kernel
theorem fb_4_8 : one 4 8 = true ∧ gtOne 4 8 = true :=
  both_of_chunks 4 8 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_8_0
    · exact f_4_8_1
  )
theorem f_4_9_0 : (chunkOf (Low6966Gate.gateList 4 9) 0).all (fF 4 9) = true := by decide +kernel
theorem f_4_9_1 : (chunkOf (Low6966Gate.gateList 4 9) 1).all (fF 4 9) = true := by decide +kernel
theorem f_4_9_2 : (chunkOf (Low6966Gate.gateList 4 9) 2).all (fF 4 9) = true := by decide +kernel
theorem fb_4_9 : one 4 9 = true ∧ gtOne 4 9 = true :=
  both_of_chunks 4 9 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_9_0
    · exact f_4_9_1
    · exact f_4_9_2
  )
theorem f_4_10_0 : (chunkOf (Low6966Gate.gateList 4 10) 0).all (fF 4 10) = true := by decide +kernel
theorem f_4_10_1 : (chunkOf (Low6966Gate.gateList 4 10) 1).all (fF 4 10) = true := by decide +kernel
theorem f_4_10_2 : (chunkOf (Low6966Gate.gateList 4 10) 2).all (fF 4 10) = true := by decide +kernel
theorem fb_4_10 : one 4 10 = true ∧ gtOne 4 10 = true :=
  both_of_chunks 4 10 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_10_0
    · exact f_4_10_1
    · exact f_4_10_2
  )
theorem f_4_11_0 : (chunkOf (Low6966Gate.gateList 4 11) 0).all (fF 4 11) = true := by decide +kernel
theorem f_4_11_1 : (chunkOf (Low6966Gate.gateList 4 11) 1).all (fF 4 11) = true := by decide +kernel
theorem f_4_11_2 : (chunkOf (Low6966Gate.gateList 4 11) 2).all (fF 4 11) = true := by decide +kernel
theorem fb_4_11 : one 4 11 = true ∧ gtOne 4 11 = true :=
  both_of_chunks 4 11 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_11_0
    · exact f_4_11_1
    · exact f_4_11_2
  )
theorem f_4_12_0 : (chunkOf (Low6966Gate.gateList 4 12) 0).all (fF 4 12) = true := by decide +kernel
theorem f_4_12_1 : (chunkOf (Low6966Gate.gateList 4 12) 1).all (fF 4 12) = true := by decide +kernel
theorem f_4_12_2 : (chunkOf (Low6966Gate.gateList 4 12) 2).all (fF 4 12) = true := by decide +kernel
theorem fb_4_12 : one 4 12 = true ∧ gtOne 4 12 = true :=
  both_of_chunks 4 12 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_12_0
    · exact f_4_12_1
    · exact f_4_12_2
  )
theorem f_4_13_0 : (chunkOf (Low6966Gate.gateList 4 13) 0).all (fF 4 13) = true := by decide +kernel
theorem f_4_13_1 : (chunkOf (Low6966Gate.gateList 4 13) 1).all (fF 4 13) = true := by decide +kernel
theorem f_4_13_2 : (chunkOf (Low6966Gate.gateList 4 13) 2).all (fF 4 13) = true := by decide +kernel
theorem fb_4_13 : one 4 13 = true ∧ gtOne 4 13 = true :=
  both_of_chunks 4 13 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_13_0
    · exact f_4_13_1
    · exact f_4_13_2
  )
theorem f_4_14_0 : (chunkOf (Low6966Gate.gateList 4 14) 0).all (fF 4 14) = true := by decide +kernel
theorem f_4_14_1 : (chunkOf (Low6966Gate.gateList 4 14) 1).all (fF 4 14) = true := by decide +kernel
theorem f_4_14_2 : (chunkOf (Low6966Gate.gateList 4 14) 2).all (fF 4 14) = true := by decide +kernel
theorem fb_4_14 : one 4 14 = true ∧ gtOne 4 14 = true :=
  both_of_chunks 4 14 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_14_0
    · exact f_4_14_1
    · exact f_4_14_2
  )
end Gate6966Fin

end Merged6967_G6966Check4

section Merged6967_G6966Check5
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_5_3_0 : (chunkOf (Low6966Gate.gateList 5 3) 0).all (fF 5 3) = true := by decide +kernel
theorem fb_5_3 : one 5 3 = true ∧ gtOne 5 3 = true :=
  both_of_chunks 5 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_3_0
  )
theorem f_5_4_0 : (chunkOf (Low6966Gate.gateList 5 4) 0).all (fF 5 4) = true := by decide +kernel
theorem fb_5_4 : one 5 4 = true ∧ gtOne 5 4 = true :=
  both_of_chunks 5 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_4_0
  )
theorem f_5_5_0 : (chunkOf (Low6966Gate.gateList 5 5) 0).all (fF 5 5) = true := by decide +kernel
theorem fb_5_5 : one 5 5 = true ∧ gtOne 5 5 = true :=
  both_of_chunks 5 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_5_0
  )
theorem f_5_6_0 : (chunkOf (Low6966Gate.gateList 5 6) 0).all (fF 5 6) = true := by decide +kernel
theorem fb_5_6 : one 5 6 = true ∧ gtOne 5 6 = true :=
  both_of_chunks 5 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_6_0
  )
theorem f_5_7_0 : (chunkOf (Low6966Gate.gateList 5 7) 0).all (fF 5 7) = true := by decide +kernel
theorem f_5_7_1 : (chunkOf (Low6966Gate.gateList 5 7) 1).all (fF 5 7) = true := by decide +kernel
theorem fb_5_7 : one 5 7 = true ∧ gtOne 5 7 = true :=
  both_of_chunks 5 7 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_7_0
    · exact f_5_7_1
  )
theorem f_5_8_0 : (chunkOf (Low6966Gate.gateList 5 8) 0).all (fF 5 8) = true := by decide +kernel
theorem f_5_8_1 : (chunkOf (Low6966Gate.gateList 5 8) 1).all (fF 5 8) = true := by decide +kernel
theorem fb_5_8 : one 5 8 = true ∧ gtOne 5 8 = true :=
  both_of_chunks 5 8 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_8_0
    · exact f_5_8_1
  )
theorem f_5_9_0 : (chunkOf (Low6966Gate.gateList 5 9) 0).all (fF 5 9) = true := by decide +kernel
theorem f_5_9_1 : (chunkOf (Low6966Gate.gateList 5 9) 1).all (fF 5 9) = true := by decide +kernel
theorem fb_5_9 : one 5 9 = true ∧ gtOne 5 9 = true :=
  both_of_chunks 5 9 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_9_0
    · exact f_5_9_1
  )
theorem f_5_10_0 : (chunkOf (Low6966Gate.gateList 5 10) 0).all (fF 5 10) = true := by decide +kernel
theorem f_5_10_1 : (chunkOf (Low6966Gate.gateList 5 10) 1).all (fF 5 10) = true := by decide +kernel
theorem fb_5_10 : one 5 10 = true ∧ gtOne 5 10 = true :=
  both_of_chunks 5 10 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_10_0
    · exact f_5_10_1
  )
theorem f_5_11_0 : (chunkOf (Low6966Gate.gateList 5 11) 0).all (fF 5 11) = true := by decide +kernel
theorem f_5_11_1 : (chunkOf (Low6966Gate.gateList 5 11) 1).all (fF 5 11) = true := by decide +kernel
theorem fb_5_11 : one 5 11 = true ∧ gtOne 5 11 = true :=
  both_of_chunks 5 11 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_11_0
    · exact f_5_11_1
  )
theorem f_5_12_0 : (chunkOf (Low6966Gate.gateList 5 12) 0).all (fF 5 12) = true := by decide +kernel
theorem f_5_12_1 : (chunkOf (Low6966Gate.gateList 5 12) 1).all (fF 5 12) = true := by decide +kernel
theorem fb_5_12 : one 5 12 = true ∧ gtOne 5 12 = true :=
  both_of_chunks 5 12 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_12_0
    · exact f_5_12_1
  )
theorem f_5_13_0 : (chunkOf (Low6966Gate.gateList 5 13) 0).all (fF 5 13) = true := by decide +kernel
theorem f_5_13_1 : (chunkOf (Low6966Gate.gateList 5 13) 1).all (fF 5 13) = true := by decide +kernel
theorem fb_5_13 : one 5 13 = true ∧ gtOne 5 13 = true :=
  both_of_chunks 5 13 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_13_0
    · exact f_5_13_1
  )
theorem f_5_14_0 : (chunkOf (Low6966Gate.gateList 5 14) 0).all (fF 5 14) = true := by decide +kernel
theorem f_5_14_1 : (chunkOf (Low6966Gate.gateList 5 14) 1).all (fF 5 14) = true := by decide +kernel
theorem f_5_14_2 : (chunkOf (Low6966Gate.gateList 5 14) 2).all (fF 5 14) = true := by decide +kernel
theorem fb_5_14 : one 5 14 = true ∧ gtOne 5 14 = true :=
  both_of_chunks 5 14 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_14_0
    · exact f_5_14_1
    · exact f_5_14_2
  )
end Gate6966Fin

end Merged6967_G6966Check5

section Merged6967_G6966Check6
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_6_4_0 : (chunkOf (Low6966Gate.gateList 6 4) 0).all (fF 6 4) = true := by decide +kernel
theorem fb_6_4 : one 6 4 = true ∧ gtOne 6 4 = true :=
  both_of_chunks 6 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_4_0
  )
theorem f_6_5_0 : (chunkOf (Low6966Gate.gateList 6 5) 0).all (fF 6 5) = true := by decide +kernel
theorem fb_6_5 : one 6 5 = true ∧ gtOne 6 5 = true :=
  both_of_chunks 6 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_5_0
  )
theorem f_6_6_0 : (chunkOf (Low6966Gate.gateList 6 6) 0).all (fF 6 6) = true := by decide +kernel
theorem fb_6_6 : one 6 6 = true ∧ gtOne 6 6 = true :=
  both_of_chunks 6 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_6_0
  )
theorem f_6_7_0 : (chunkOf (Low6966Gate.gateList 6 7) 0).all (fF 6 7) = true := by decide +kernel
theorem fb_6_7 : one 6 7 = true ∧ gtOne 6 7 = true :=
  both_of_chunks 6 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_7_0
  )
theorem f_6_8_0 : (chunkOf (Low6966Gate.gateList 6 8) 0).all (fF 6 8) = true := by decide +kernel
theorem fb_6_8 : one 6 8 = true ∧ gtOne 6 8 = true :=
  both_of_chunks 6 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_8_0
  )
theorem f_6_9_0 : (chunkOf (Low6966Gate.gateList 6 9) 0).all (fF 6 9) = true := by decide +kernel
theorem f_6_9_1 : (chunkOf (Low6966Gate.gateList 6 9) 1).all (fF 6 9) = true := by decide +kernel
theorem fb_6_9 : one 6 9 = true ∧ gtOne 6 9 = true :=
  both_of_chunks 6 9 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_9_0
    · exact f_6_9_1
  )
theorem f_6_10_0 : (chunkOf (Low6966Gate.gateList 6 10) 0).all (fF 6 10) = true := by decide +kernel
theorem f_6_10_1 : (chunkOf (Low6966Gate.gateList 6 10) 1).all (fF 6 10) = true := by decide +kernel
theorem fb_6_10 : one 6 10 = true ∧ gtOne 6 10 = true :=
  both_of_chunks 6 10 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_10_0
    · exact f_6_10_1
  )
theorem f_6_11_0 : (chunkOf (Low6966Gate.gateList 6 11) 0).all (fF 6 11) = true := by decide +kernel
theorem f_6_11_1 : (chunkOf (Low6966Gate.gateList 6 11) 1).all (fF 6 11) = true := by decide +kernel
theorem fb_6_11 : one 6 11 = true ∧ gtOne 6 11 = true :=
  both_of_chunks 6 11 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_11_0
    · exact f_6_11_1
  )
theorem f_6_12_0 : (chunkOf (Low6966Gate.gateList 6 12) 0).all (fF 6 12) = true := by decide +kernel
theorem f_6_12_1 : (chunkOf (Low6966Gate.gateList 6 12) 1).all (fF 6 12) = true := by decide +kernel
theorem fb_6_12 : one 6 12 = true ∧ gtOne 6 12 = true :=
  both_of_chunks 6 12 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_12_0
    · exact f_6_12_1
  )
theorem f_6_13_0 : (chunkOf (Low6966Gate.gateList 6 13) 0).all (fF 6 13) = true := by decide +kernel
theorem f_6_13_1 : (chunkOf (Low6966Gate.gateList 6 13) 1).all (fF 6 13) = true := by decide +kernel
theorem fb_6_13 : one 6 13 = true ∧ gtOne 6 13 = true :=
  both_of_chunks 6 13 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_13_0
    · exact f_6_13_1
  )
theorem f_6_14_0 : (chunkOf (Low6966Gate.gateList 6 14) 0).all (fF 6 14) = true := by decide +kernel
theorem f_6_14_1 : (chunkOf (Low6966Gate.gateList 6 14) 1).all (fF 6 14) = true := by decide +kernel
theorem fb_6_14 : one 6 14 = true ∧ gtOne 6 14 = true :=
  both_of_chunks 6 14 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_14_0
    · exact f_6_14_1
  )
end Gate6966Fin

end Merged6967_G6966Check6

section Merged6967_G6966Check7
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_7_5_0 : (chunkOf (Low6966Gate.gateList 7 5) 0).all (fF 7 5) = true := by decide +kernel
theorem fb_7_5 : one 7 5 = true ∧ gtOne 7 5 = true :=
  both_of_chunks 7 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_5_0
  )
theorem f_7_6_0 : (chunkOf (Low6966Gate.gateList 7 6) 0).all (fF 7 6) = true := by decide +kernel
theorem fb_7_6 : one 7 6 = true ∧ gtOne 7 6 = true :=
  both_of_chunks 7 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_6_0
  )
theorem f_7_7_0 : (chunkOf (Low6966Gate.gateList 7 7) 0).all (fF 7 7) = true := by decide +kernel
theorem fb_7_7 : one 7 7 = true ∧ gtOne 7 7 = true :=
  both_of_chunks 7 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_7_0
  )
theorem f_7_8_0 : (chunkOf (Low6966Gate.gateList 7 8) 0).all (fF 7 8) = true := by decide +kernel
theorem fb_7_8 : one 7 8 = true ∧ gtOne 7 8 = true :=
  both_of_chunks 7 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_8_0
  )
theorem f_7_9_0 : (chunkOf (Low6966Gate.gateList 7 9) 0).all (fF 7 9) = true := by decide +kernel
theorem fb_7_9 : one 7 9 = true ∧ gtOne 7 9 = true :=
  both_of_chunks 7 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_9_0
  )
theorem f_7_10_0 : (chunkOf (Low6966Gate.gateList 7 10) 0).all (fF 7 10) = true := by decide +kernel
theorem fb_7_10 : one 7 10 = true ∧ gtOne 7 10 = true :=
  both_of_chunks 7 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_10_0
  )
theorem f_7_11_0 : (chunkOf (Low6966Gate.gateList 7 11) 0).all (fF 7 11) = true := by decide +kernel
theorem fb_7_11 : one 7 11 = true ∧ gtOne 7 11 = true :=
  both_of_chunks 7 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_11_0
  )
theorem f_7_12_0 : (chunkOf (Low6966Gate.gateList 7 12) 0).all (fF 7 12) = true := by decide +kernel
theorem fb_7_12 : one 7 12 = true ∧ gtOne 7 12 = true :=
  both_of_chunks 7 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_12_0
  )
theorem f_7_13_0 : (chunkOf (Low6966Gate.gateList 7 13) 0).all (fF 7 13) = true := by decide +kernel
theorem fb_7_13 : one 7 13 = true ∧ gtOne 7 13 = true :=
  both_of_chunks 7 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_13_0
  )
theorem f_7_14_0 : (chunkOf (Low6966Gate.gateList 7 14) 0).all (fF 7 14) = true := by decide +kernel
theorem fb_7_14 : one 7 14 = true ∧ gtOne 7 14 = true :=
  both_of_chunks 7 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_14_0
  )
end Gate6966Fin

end Merged6967_G6966Check7

section Merged6967_G6966Check8
set_option Elab.async false

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

end Merged6967_G6966Check8

section Merged6967_G6966Check9
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_9_10_0 : (chunkOf (Low6966Gate.gateList 9 10) 0).all (fF 9 10) = true := by decide +kernel
theorem fb_9_10 : one 9 10 = true ∧ gtOne 9 10 = true :=
  both_of_chunks 9 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_10_0
  )
theorem f_9_11_0 : (chunkOf (Low6966Gate.gateList 9 11) 0).all (fF 9 11) = true := by decide +kernel
theorem fb_9_11 : one 9 11 = true ∧ gtOne 9 11 = true :=
  both_of_chunks 9 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_11_0
  )
theorem f_9_12_0 : (chunkOf (Low6966Gate.gateList 9 12) 0).all (fF 9 12) = true := by decide +kernel
theorem fb_9_12 : one 9 12 = true ∧ gtOne 9 12 = true :=
  both_of_chunks 9 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_12_0
  )
theorem f_9_13_0 : (chunkOf (Low6966Gate.gateList 9 13) 0).all (fF 9 13) = true := by decide +kernel
theorem fb_9_13 : one 9 13 = true ∧ gtOne 9 13 = true :=
  both_of_chunks 9 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_13_0
  )
theorem f_9_14_0 : (chunkOf (Low6966Gate.gateList 9 14) 0).all (fF 9 14) = true := by decide +kernel
theorem fb_9_14 : one 9 14 = true ∧ gtOne 9 14 = true :=
  both_of_chunks 9 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_14_0
  )
end Gate6966Fin

end Merged6967_G6966Check9
