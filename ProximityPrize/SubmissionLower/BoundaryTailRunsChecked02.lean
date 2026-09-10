import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics
import ProximityPrize.SubmissionLower.BoundaryTailRunsChecked01

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseChecks Lower80801.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r6_part0 : ∀ i ∈ List.range 8, RunsAt 6 (0+i) := by
  decide +kernel

theorem runs_r6_part1 : ∀ i ∈ List.range 8, RunsAt 6 (8+i) := by
  decide +kernel

theorem runs_r6_part2 : ∀ i ∈ List.range 8, RunsAt 6 (16+i) := by
  decide +kernel

theorem runs_r6_part3 : ∀ i ∈ List.range 8, RunsAt 6 (24+i) := by
  decide +kernel

theorem runs_r6_part4 : ∀ i ∈ List.range 8, RunsAt 6 (32+i) := by
  decide +kernel

theorem runs_r6_part5 : ∀ i ∈ List.range 8, RunsAt 6 (40+i) := by
  decide +kernel

theorem runs_r6_part6 : ∀ i ∈ List.range 8, RunsAt 6 (48+i) := by
  decide +kernel

theorem runs_r6_part7 : ∀ i ∈ List.range 8, RunsAt 6 (56+i) := by
  decide +kernel

theorem runs_r6_part8 : ∀ i ∈ List.range 8, RunsAt 6 (64+i) := by
  decide +kernel

theorem runs_r6_part9 : ∀ i ∈ List.range 8, RunsAt 6 (72+i) := by
  decide +kernel

theorem runs_r6_part10 : ∀ i ∈ List.range 8, RunsAt 6 (80+i) := by
  decide +kernel

theorem runs_r6_part11 : ∀ i ∈ List.range 8, RunsAt 6 (88+i) := by
  decide +kernel

theorem runs_r6_part12 : ∀ i ∈ List.range 8, RunsAt 6 (96+i) := by
  decide +kernel

theorem runs_r6_part13 : ∀ i ∈ List.range 8, RunsAt 6 (104+i) := by
  decide +kernel

theorem runs_r6_part14 : ∀ i ∈ List.range 8, RunsAt 6 (112+i) := by
  decide +kernel

theorem runs_r6_part15 : ∀ i ∈ List.range 8, RunsAt 6 (120+i) := by
  decide +kernel

theorem runs_r6_part16 : ∀ i ∈ List.range 6, RunsAt 6 (128+i) := by
  decide +kernel

theorem runs_r6 : ∀ V ∈ List.range 134, RunsAt 6 V := by
  intro V hV
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r6_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r6_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r6_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r6_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r6_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r6_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r6_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r6_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r6_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r6_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r6_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r6_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r6_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r6_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r6_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r6_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi := runs_r6_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r7_part0 : ∀ i ∈ List.range 8, RunsAt 7 (0+i) := by
  decide +kernel

theorem runs_r7_part1 : ∀ i ∈ List.range 8, RunsAt 7 (8+i) := by
  decide +kernel

theorem runs_r7_part2 : ∀ i ∈ List.range 8, RunsAt 7 (16+i) := by
  decide +kernel

theorem runs_r7_part3 : ∀ i ∈ List.range 8, RunsAt 7 (24+i) := by
  decide +kernel

theorem runs_r7_part4 : ∀ i ∈ List.range 8, RunsAt 7 (32+i) := by
  decide +kernel

theorem runs_r7_part5 : ∀ i ∈ List.range 8, RunsAt 7 (40+i) := by
  decide +kernel

theorem runs_r7_part6 : ∀ i ∈ List.range 8, RunsAt 7 (48+i) := by
  decide +kernel

theorem runs_r7_part7 : ∀ i ∈ List.range 8, RunsAt 7 (56+i) := by
  decide +kernel

theorem runs_r7_part8 : ∀ i ∈ List.range 8, RunsAt 7 (64+i) := by
  decide +kernel

theorem runs_r7_part9 : ∀ i ∈ List.range 8, RunsAt 7 (72+i) := by
  decide +kernel

theorem runs_r7_part10 : ∀ i ∈ List.range 8, RunsAt 7 (80+i) := by
  decide +kernel

theorem runs_r7_part11 : ∀ i ∈ List.range 8, RunsAt 7 (88+i) := by
  decide +kernel

theorem runs_r7_part12 : ∀ i ∈ List.range 8, RunsAt 7 (96+i) := by
  decide +kernel

theorem runs_r7_part13 : ∀ i ∈ List.range 8, RunsAt 7 (104+i) := by
  decide +kernel

theorem runs_r7_part14 : ∀ i ∈ List.range 8, RunsAt 7 (112+i) := by
  decide +kernel

theorem runs_r7_part15 : ∀ i ∈ List.range 8, RunsAt 7 (120+i) := by
  decide +kernel

theorem runs_r7_part16 : ∀ i ∈ List.range 5, RunsAt 7 (128+i) := by
  decide +kernel

theorem runs_r7 : ∀ V ∈ List.range 133, RunsAt 7 V := by
  intro V hV
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r7_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r7_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r7_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r7_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r7_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r7_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r7_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r7_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r7_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r7_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r7_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r7_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r7_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r7_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r7_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r7_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi := runs_r7_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r8_part0 : ∀ i ∈ List.range 8, RunsAt 8 (0+i) := by
  decide +kernel

theorem runs_r8_part1 : ∀ i ∈ List.range 8, RunsAt 8 (8+i) := by
  decide +kernel

theorem runs_r8_part2 : ∀ i ∈ List.range 8, RunsAt 8 (16+i) := by
  decide +kernel

theorem runs_r8_part3 : ∀ i ∈ List.range 8, RunsAt 8 (24+i) := by
  decide +kernel

theorem runs_r8_part4 : ∀ i ∈ List.range 8, RunsAt 8 (32+i) := by
  decide +kernel

theorem runs_r8_part5 : ∀ i ∈ List.range 8, RunsAt 8 (40+i) := by
  decide +kernel

theorem runs_r8_part6 : ∀ i ∈ List.range 8, RunsAt 8 (48+i) := by
  decide +kernel

theorem runs_r8_part7 : ∀ i ∈ List.range 8, RunsAt 8 (56+i) := by
  decide +kernel

theorem runs_r8_part8 : ∀ i ∈ List.range 8, RunsAt 8 (64+i) := by
  decide +kernel

theorem runs_r8_part9 : ∀ i ∈ List.range 8, RunsAt 8 (72+i) := by
  decide +kernel

theorem runs_r8_part10 : ∀ i ∈ List.range 8, RunsAt 8 (80+i) := by
  decide +kernel

theorem runs_r8_part11 : ∀ i ∈ List.range 8, RunsAt 8 (88+i) := by
  decide +kernel

theorem runs_r8_part12 : ∀ i ∈ List.range 8, RunsAt 8 (96+i) := by
  decide +kernel

theorem runs_r8_part13 : ∀ i ∈ List.range 8, RunsAt 8 (104+i) := by
  decide +kernel

theorem runs_r8_part14 : ∀ i ∈ List.range 8, RunsAt 8 (112+i) := by
  decide +kernel

theorem runs_r8_part15 : ∀ i ∈ List.range 8, RunsAt 8 (120+i) := by
  decide +kernel

theorem runs_r8_part16 : ∀ i ∈ List.range 4, RunsAt 8 (128+i) := by
  decide +kernel

theorem runs_r8 : ∀ V ∈ List.range 132, RunsAt 8 V := by
  intro V hV
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r8_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r8_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r8_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r8_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r8_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r8_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r8_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r8_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r8_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r8_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r8_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r8_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r8_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r8_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r8_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r8_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi := runs_r8_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r9_part0 : ∀ i ∈ List.range 8, RunsAt 9 (0+i) := by
  decide +kernel

theorem runs_r9_part1 : ∀ i ∈ List.range 8, RunsAt 9 (8+i) := by
  decide +kernel

theorem runs_r9_part2 : ∀ i ∈ List.range 8, RunsAt 9 (16+i) := by
  decide +kernel

theorem runs_r9_part3 : ∀ i ∈ List.range 8, RunsAt 9 (24+i) := by
  decide +kernel

theorem runs_r9_part4 : ∀ i ∈ List.range 8, RunsAt 9 (32+i) := by
  decide +kernel

theorem runs_r9_part5 : ∀ i ∈ List.range 8, RunsAt 9 (40+i) := by
  decide +kernel

theorem runs_r9_part6 : ∀ i ∈ List.range 8, RunsAt 9 (48+i) := by
  decide +kernel

theorem runs_r9_part7 : ∀ i ∈ List.range 8, RunsAt 9 (56+i) := by
  decide +kernel

theorem runs_r9_part8 : ∀ i ∈ List.range 8, RunsAt 9 (64+i) := by
  decide +kernel

theorem runs_r9_part9 : ∀ i ∈ List.range 8, RunsAt 9 (72+i) := by
  decide +kernel

theorem runs_r9_part10 : ∀ i ∈ List.range 8, RunsAt 9 (80+i) := by
  decide +kernel

theorem runs_r9_part11 : ∀ i ∈ List.range 8, RunsAt 9 (88+i) := by
  decide +kernel

theorem runs_r9_part12 : ∀ i ∈ List.range 8, RunsAt 9 (96+i) := by
  decide +kernel

theorem runs_r9_part13 : ∀ i ∈ List.range 8, RunsAt 9 (104+i) := by
  decide +kernel

theorem runs_r9_part14 : ∀ i ∈ List.range 8, RunsAt 9 (112+i) := by
  decide +kernel

theorem runs_r9_part15 : ∀ i ∈ List.range 8, RunsAt 9 (120+i) := by
  decide +kernel

theorem runs_r9_part16 : ∀ i ∈ List.range 3, RunsAt 9 (128+i) := by
  decide +kernel

theorem runs_r9 : ∀ V ∈ List.range 131, RunsAt 9 V := by
  intro V hV
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r9_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r9_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r9_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r9_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r9_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r9_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r9_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r9_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r9_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r9_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r9_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r9_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r9_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r9_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r9_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r9_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi := runs_r9_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r10_part0 : ∀ i ∈ List.range 8, RunsAt 10 (0+i) := by
  decide +kernel

theorem runs_r10_part1 : ∀ i ∈ List.range 8, RunsAt 10 (8+i) := by
  decide +kernel

theorem runs_r10_part2 : ∀ i ∈ List.range 8, RunsAt 10 (16+i) := by
  decide +kernel

theorem runs_r10_part3 : ∀ i ∈ List.range 8, RunsAt 10 (24+i) := by
  decide +kernel

theorem runs_r10_part4 : ∀ i ∈ List.range 8, RunsAt 10 (32+i) := by
  decide +kernel

theorem runs_r10_part5 : ∀ i ∈ List.range 8, RunsAt 10 (40+i) := by
  decide +kernel

theorem runs_r10_part6 : ∀ i ∈ List.range 8, RunsAt 10 (48+i) := by
  decide +kernel

theorem runs_r10_part7 : ∀ i ∈ List.range 8, RunsAt 10 (56+i) := by
  decide +kernel

theorem runs_r10_part8 : ∀ i ∈ List.range 8, RunsAt 10 (64+i) := by
  decide +kernel

theorem runs_r10_part9 : ∀ i ∈ List.range 8, RunsAt 10 (72+i) := by
  decide +kernel

theorem runs_r10_part10 : ∀ i ∈ List.range 8, RunsAt 10 (80+i) := by
  decide +kernel

theorem runs_r10_part11 : ∀ i ∈ List.range 8, RunsAt 10 (88+i) := by
  decide +kernel

theorem runs_r10_part12 : ∀ i ∈ List.range 8, RunsAt 10 (96+i) := by
  decide +kernel

theorem runs_r10_part13 : ∀ i ∈ List.range 8, RunsAt 10 (104+i) := by
  decide +kernel

theorem runs_r10_part14 : ∀ i ∈ List.range 8, RunsAt 10 (112+i) := by
  decide +kernel

theorem runs_r10_part15 : ∀ i ∈ List.range 8, RunsAt 10 (120+i) := by
  decide +kernel

theorem runs_r10_part16 : ∀ i ∈ List.range 2, RunsAt 10 (128+i) := by
  decide +kernel

theorem runs_r10 : ∀ V ∈ List.range 130, RunsAt 10 V := by
  intro V hV
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r10_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r10_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r10_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r10_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r10_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r10_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r10_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r10_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r10_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r10_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r10_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r10_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r10_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r10_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r10_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r10_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi := runs_r10_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
