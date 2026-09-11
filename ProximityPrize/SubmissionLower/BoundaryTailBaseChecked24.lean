import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24Fast

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r24 : ∀ V ∈ List.range 116, CorrectAt 24 V := by
  intro V hV
  have hv : V < 116 := List.mem_range.mp hV
  by_cases c0 : V < 8
  · have h := correct_r24_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
  · 
    by_cases c1 : V < 16
    · have h := correct_r24_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
    · 
      by_cases c2 : V < 24
      · have h := correct_r24_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
      · 
        by_cases c3 : V < 32
        · have h := correct_r24_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · 
          by_cases c4 : V < 40
          · have h := correct_r24_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · 
            by_cases c5 : V < 48
            · have h := correct_r24_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
            · 
              by_cases c6 : V < 56
              · have h := correct_r24_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · 
                by_cases c7 : V < 64
                · have h := correct_r24_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
                · 
                  by_cases c8 : V < 72
                  · have h := correct_r24_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
                  · 
                    by_cases c9 : V < 80
                    · have h := correct_r24_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
                    · 
                      by_cases c10 : V < 88
                      · have h := correct_r24_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
                      · 
                        by_cases c11 : V < 96
                        · have h := correct_r24_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
                        · 
                          by_cases c12 : V < 104
                          · have h := correct_r24_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
                          · 
                            by_cases c13 : V < 112
                            · have h := correct_r24_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
                            · 
                              have h := correct_r24_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem zero_r24 : ∀ V ∈ List.range 116, ZeroCheckAt 24 V := by
  intro V hV
  have hv : V < 116 := List.mem_range.mp hV
  exact zeroAt_of_algebra 24 V (by omega) (by omega) (by omega)

theorem strict_r24 : ∀ V ∈ List.range 116, StrictCheckAt 24 V := by
  intro V hV
  have hv : V < 116 := List.mem_range.mp hV
  by_cases c0 : V < 8
  · have h := strict_r24_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
  · 
    by_cases c1 : V < 16
    · have h := strict_r24_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
    · 
      by_cases c2 : V < 24
      · have h := strict_r24_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
      · 
        by_cases c3 : V < 32
        · have h := strict_r24_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · 
          by_cases c4 : V < 40
          · have h := strict_r24_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · 
            by_cases c5 : V < 48
            · have h := strict_r24_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
            · 
              by_cases c6 : V < 56
              · have h := strict_r24_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · 
                by_cases c7 : V < 64
                · have h := strict_r24_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
                · 
                  by_cases c8 : V < 72
                  · have h := strict_r24_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
                  · 
                    by_cases c9 : V < 80
                    · have h := strict_r24_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
                    · 
                      by_cases c10 : V < 88
                      · have h := strict_r24_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
                      · 
                        by_cases c11 : V < 96
                        · have h := strict_r24_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
                        · 
                          by_cases c12 : V < 104
                          · have h := strict_r24_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
                          · 
                            by_cases c13 : V < 112
                            · have h := strict_r24_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
                            · 
                              have h := strict_r24_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem base_r24 : ∀ V ∈ List.range 116, BaseCheckAt 24 V := by
  intro V hV
  have hv : V < 116 := List.mem_range.mp hV
  by_cases c0 : V < 8
  · have h := base_r24_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
  · 
    by_cases c1 : V < 16
    · have h := base_r24_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
    · 
      by_cases c2 : V < 24
      · have h := base_r24_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
      · 
        by_cases c3 : V < 32
        · have h := base_r24_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · 
          by_cases c4 : V < 40
          · have h := base_r24_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · 
            by_cases c5 : V < 48
            · have h := base_r24_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
            · 
              by_cases c6 : V < 56
              · have h := base_r24_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · 
                by_cases c7 : V < 64
                · have h := base_r24_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
                · 
                  by_cases c8 : V < 72
                  · have h := base_r24_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
                  · 
                    by_cases c9 : V < 80
                    · have h := base_r24_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
                    · 
                      by_cases c10 : V < 88
                      · have h := base_r24_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
                      · 
                        by_cases c11 : V < 96
                        · have h := base_r24_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
                        · 
                          by_cases c12 : V < 104
                          · have h := base_r24_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
                          · 
                            by_cases c13 : V < 112
                            · have h := base_r24_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
                            · 
                              have h := base_r24_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
