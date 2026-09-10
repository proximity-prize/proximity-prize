import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics
import ProximityPrize.SubmissionLower.BoundaryTailRunsChecked04

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseChecks Lower80801.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r21_part0 : ∀ i ∈ List.range 8, RunsAt 21 (0+i) := by
  decide +kernel

theorem runs_r21_part1 : ∀ i ∈ List.range 8, RunsAt 21 (8+i) := by
  decide +kernel

theorem runs_r21_part2 : ∀ i ∈ List.range 8, RunsAt 21 (16+i) := by
  decide +kernel

theorem runs_r21_part3 : ∀ i ∈ List.range 8, RunsAt 21 (24+i) := by
  decide +kernel

theorem runs_r21_part4 : ∀ i ∈ List.range 8, RunsAt 21 (32+i) := by
  decide +kernel

theorem runs_r21_part5 : ∀ i ∈ List.range 8, RunsAt 21 (40+i) := by
  decide +kernel

theorem runs_r21_part6 : ∀ i ∈ List.range 8, RunsAt 21 (48+i) := by
  decide +kernel

theorem runs_r21_part7 : ∀ i ∈ List.range 8, RunsAt 21 (56+i) := by
  decide +kernel

theorem runs_r21_part8 : ∀ i ∈ List.range 8, RunsAt 21 (64+i) := by
  decide +kernel

theorem runs_r21_part9 : ∀ i ∈ List.range 8, RunsAt 21 (72+i) := by
  decide +kernel

theorem runs_r21_part10 : ∀ i ∈ List.range 8, RunsAt 21 (80+i) := by
  decide +kernel

theorem runs_r21_part11 : ∀ i ∈ List.range 8, RunsAt 21 (88+i) := by
  decide +kernel

theorem runs_r21_part12 : ∀ i ∈ List.range 8, RunsAt 21 (96+i) := by
  decide +kernel

theorem runs_r21_part13 : ∀ i ∈ List.range 8, RunsAt 21 (104+i) := by
  decide +kernel

theorem runs_r21_part14 : ∀ i ∈ List.range 7, RunsAt 21 (112+i) := by
  decide +kernel

theorem runs_r21 : ∀ V ∈ List.range 119, RunsAt 21 V := by
  intro V hV
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r21_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r21_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r21_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r21_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r21_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r21_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r21_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r21_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r21_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r21_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r21_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r21_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r21_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r21_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi := runs_r21_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r22_part0 : ∀ i ∈ List.range 8, RunsAt 22 (0+i) := by
  decide +kernel

theorem runs_r22_part1 : ∀ i ∈ List.range 8, RunsAt 22 (8+i) := by
  decide +kernel

theorem runs_r22_part2 : ∀ i ∈ List.range 8, RunsAt 22 (16+i) := by
  decide +kernel

theorem runs_r22_part3 : ∀ i ∈ List.range 8, RunsAt 22 (24+i) := by
  decide +kernel

theorem runs_r22_part4 : ∀ i ∈ List.range 8, RunsAt 22 (32+i) := by
  decide +kernel

theorem runs_r22_part5 : ∀ i ∈ List.range 8, RunsAt 22 (40+i) := by
  decide +kernel

theorem runs_r22_part6 : ∀ i ∈ List.range 8, RunsAt 22 (48+i) := by
  decide +kernel

theorem runs_r22_part7 : ∀ i ∈ List.range 8, RunsAt 22 (56+i) := by
  decide +kernel

theorem runs_r22_part8 : ∀ i ∈ List.range 8, RunsAt 22 (64+i) := by
  decide +kernel

theorem runs_r22_part9 : ∀ i ∈ List.range 8, RunsAt 22 (72+i) := by
  decide +kernel

theorem runs_r22_part10 : ∀ i ∈ List.range 8, RunsAt 22 (80+i) := by
  decide +kernel

theorem runs_r22_part11 : ∀ i ∈ List.range 8, RunsAt 22 (88+i) := by
  decide +kernel

theorem runs_r22_part12 : ∀ i ∈ List.range 8, RunsAt 22 (96+i) := by
  decide +kernel

theorem runs_r22_part13 : ∀ i ∈ List.range 8, RunsAt 22 (104+i) := by
  decide +kernel

theorem runs_r22_part14 : ∀ i ∈ List.range 6, RunsAt 22 (112+i) := by
  decide +kernel

theorem runs_r22 : ∀ V ∈ List.range 118, RunsAt 22 V := by
  intro V hV
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r22_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r22_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r22_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r22_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r22_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r22_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r22_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r22_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r22_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r22_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r22_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r22_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r22_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r22_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi := runs_r22_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r23_part0 : ∀ i ∈ List.range 8, RunsAt 23 (0+i) := by
  decide +kernel

theorem runs_r23_part1 : ∀ i ∈ List.range 8, RunsAt 23 (8+i) := by
  decide +kernel

theorem runs_r23_part2 : ∀ i ∈ List.range 8, RunsAt 23 (16+i) := by
  decide +kernel

theorem runs_r23_part3 : ∀ i ∈ List.range 8, RunsAt 23 (24+i) := by
  decide +kernel

theorem runs_r23_part4 : ∀ i ∈ List.range 8, RunsAt 23 (32+i) := by
  decide +kernel

theorem runs_r23_part5 : ∀ i ∈ List.range 8, RunsAt 23 (40+i) := by
  decide +kernel

theorem runs_r23_part6 : ∀ i ∈ List.range 8, RunsAt 23 (48+i) := by
  decide +kernel

theorem runs_r23_part7 : ∀ i ∈ List.range 8, RunsAt 23 (56+i) := by
  decide +kernel

theorem runs_r23_part8 : ∀ i ∈ List.range 8, RunsAt 23 (64+i) := by
  decide +kernel

theorem runs_r23_part9 : ∀ i ∈ List.range 8, RunsAt 23 (72+i) := by
  decide +kernel

theorem runs_r23_part10 : ∀ i ∈ List.range 8, RunsAt 23 (80+i) := by
  decide +kernel

theorem runs_r23_part11 : ∀ i ∈ List.range 8, RunsAt 23 (88+i) := by
  decide +kernel

theorem runs_r23_part12 : ∀ i ∈ List.range 8, RunsAt 23 (96+i) := by
  decide +kernel

theorem runs_r23_part13 : ∀ i ∈ List.range 8, RunsAt 23 (104+i) := by
  decide +kernel

theorem runs_r23_part14 : ∀ i ∈ List.range 5, RunsAt 23 (112+i) := by
  decide +kernel

theorem runs_r23 : ∀ V ∈ List.range 117, RunsAt 23 V := by
  intro V hV
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r23_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r23_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r23_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r23_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r23_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r23_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r23_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r23_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r23_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r23_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r23_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r23_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r23_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r23_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi := runs_r23_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r24_part0 : ∀ i ∈ List.range 8, RunsAt 24 (0+i) := by
  decide +kernel

theorem runs_r24_part1 : ∀ i ∈ List.range 8, RunsAt 24 (8+i) := by
  decide +kernel

theorem runs_r24_part2 : ∀ i ∈ List.range 8, RunsAt 24 (16+i) := by
  decide +kernel

theorem runs_r24_part3 : ∀ i ∈ List.range 8, RunsAt 24 (24+i) := by
  decide +kernel

theorem runs_r24_part4 : ∀ i ∈ List.range 8, RunsAt 24 (32+i) := by
  decide +kernel

theorem runs_r24_part5 : ∀ i ∈ List.range 8, RunsAt 24 (40+i) := by
  decide +kernel

theorem runs_r24_part6 : ∀ i ∈ List.range 8, RunsAt 24 (48+i) := by
  decide +kernel

theorem runs_r24_part7 : ∀ i ∈ List.range 8, RunsAt 24 (56+i) := by
  decide +kernel

theorem runs_r24_part8 : ∀ i ∈ List.range 8, RunsAt 24 (64+i) := by
  decide +kernel

theorem runs_r24_part9 : ∀ i ∈ List.range 8, RunsAt 24 (72+i) := by
  decide +kernel

theorem runs_r24_part10 : ∀ i ∈ List.range 8, RunsAt 24 (80+i) := by
  decide +kernel

theorem runs_r24_part11 : ∀ i ∈ List.range 8, RunsAt 24 (88+i) := by
  decide +kernel

theorem runs_r24_part12 : ∀ i ∈ List.range 8, RunsAt 24 (96+i) := by
  decide +kernel

theorem runs_r24_part13 : ∀ i ∈ List.range 8, RunsAt 24 (104+i) := by
  decide +kernel

theorem runs_r24_part14 : ∀ i ∈ List.range 4, RunsAt 24 (112+i) := by
  decide +kernel

theorem runs_r24 : ∀ V ∈ List.range 116, RunsAt 24 V := by
  intro V hV
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r24_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r24_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r24_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r24_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r24_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r24_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r24_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r24_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r24_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r24_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r24_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r24_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r24_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r24_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi := runs_r24_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r25_part0 : ∀ i ∈ List.range 8, RunsAt 25 (0+i) := by
  decide +kernel

theorem runs_r25_part1 : ∀ i ∈ List.range 8, RunsAt 25 (8+i) := by
  decide +kernel

theorem runs_r25_part2 : ∀ i ∈ List.range 8, RunsAt 25 (16+i) := by
  decide +kernel

theorem runs_r25_part3 : ∀ i ∈ List.range 8, RunsAt 25 (24+i) := by
  decide +kernel

theorem runs_r25_part4 : ∀ i ∈ List.range 8, RunsAt 25 (32+i) := by
  decide +kernel

theorem runs_r25_part5 : ∀ i ∈ List.range 8, RunsAt 25 (40+i) := by
  decide +kernel

theorem runs_r25_part6 : ∀ i ∈ List.range 8, RunsAt 25 (48+i) := by
  decide +kernel

theorem runs_r25_part7 : ∀ i ∈ List.range 8, RunsAt 25 (56+i) := by
  decide +kernel

theorem runs_r25_part8 : ∀ i ∈ List.range 8, RunsAt 25 (64+i) := by
  decide +kernel

theorem runs_r25_part9 : ∀ i ∈ List.range 8, RunsAt 25 (72+i) := by
  decide +kernel

theorem runs_r25_part10 : ∀ i ∈ List.range 8, RunsAt 25 (80+i) := by
  decide +kernel

theorem runs_r25_part11 : ∀ i ∈ List.range 8, RunsAt 25 (88+i) := by
  decide +kernel

theorem runs_r25_part12 : ∀ i ∈ List.range 8, RunsAt 25 (96+i) := by
  decide +kernel

theorem runs_r25_part13 : ∀ i ∈ List.range 8, RunsAt 25 (104+i) := by
  decide +kernel

theorem runs_r25_part14 : ∀ i ∈ List.range 3, RunsAt 25 (112+i) := by
  decide +kernel

theorem runs_r25 : ∀ V ∈ List.range 115, RunsAt 25 V := by
  intro V hV
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r25_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r25_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r25_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r25_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r25_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r25_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r25_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r25_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r25_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r25_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r25_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r25_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r25_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r25_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi := runs_r25_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
