import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics
import ProximityPrize.SubmissionLower.BoundaryTailRunsChecked03

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseChecks Lower80801.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r16_part0 : ∀ i ∈ List.range 8, RunsAt 16 (0+i) := by
  decide +kernel

theorem runs_r16_part1 : ∀ i ∈ List.range 8, RunsAt 16 (8+i) := by
  decide +kernel

theorem runs_r16_part2 : ∀ i ∈ List.range 8, RunsAt 16 (16+i) := by
  decide +kernel

theorem runs_r16_part3 : ∀ i ∈ List.range 8, RunsAt 16 (24+i) := by
  decide +kernel

theorem runs_r16_part4 : ∀ i ∈ List.range 8, RunsAt 16 (32+i) := by
  decide +kernel

theorem runs_r16_part5 : ∀ i ∈ List.range 8, RunsAt 16 (40+i) := by
  decide +kernel

theorem runs_r16_part6 : ∀ i ∈ List.range 8, RunsAt 16 (48+i) := by
  decide +kernel

theorem runs_r16_part7 : ∀ i ∈ List.range 8, RunsAt 16 (56+i) := by
  decide +kernel

theorem runs_r16_part8 : ∀ i ∈ List.range 8, RunsAt 16 (64+i) := by
  decide +kernel

theorem runs_r16_part9 : ∀ i ∈ List.range 8, RunsAt 16 (72+i) := by
  decide +kernel

theorem runs_r16_part10 : ∀ i ∈ List.range 8, RunsAt 16 (80+i) := by
  decide +kernel

theorem runs_r16_part11 : ∀ i ∈ List.range 8, RunsAt 16 (88+i) := by
  decide +kernel

theorem runs_r16_part12 : ∀ i ∈ List.range 8, RunsAt 16 (96+i) := by
  decide +kernel

theorem runs_r16_part13 : ∀ i ∈ List.range 8, RunsAt 16 (104+i) := by
  decide +kernel

theorem runs_r16_part14 : ∀ i ∈ List.range 8, RunsAt 16 (112+i) := by
  decide +kernel

theorem runs_r16_part15 : ∀ i ∈ List.range 4, RunsAt 16 (120+i) := by
  decide +kernel

theorem runs_r16 : ∀ V ∈ List.range 124, RunsAt 16 V := by
  intro V hV
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r16_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r16_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r16_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r16_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r16_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r16_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r16_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r16_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r16_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r16_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r16_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r16_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r16_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r16_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r16_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi := runs_r16_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r17_part0 : ∀ i ∈ List.range 8, RunsAt 17 (0+i) := by
  decide +kernel

theorem runs_r17_part1 : ∀ i ∈ List.range 8, RunsAt 17 (8+i) := by
  decide +kernel

theorem runs_r17_part2 : ∀ i ∈ List.range 8, RunsAt 17 (16+i) := by
  decide +kernel

theorem runs_r17_part3 : ∀ i ∈ List.range 8, RunsAt 17 (24+i) := by
  decide +kernel

theorem runs_r17_part4 : ∀ i ∈ List.range 8, RunsAt 17 (32+i) := by
  decide +kernel

theorem runs_r17_part5 : ∀ i ∈ List.range 8, RunsAt 17 (40+i) := by
  decide +kernel

theorem runs_r17_part6 : ∀ i ∈ List.range 8, RunsAt 17 (48+i) := by
  decide +kernel

theorem runs_r17_part7 : ∀ i ∈ List.range 8, RunsAt 17 (56+i) := by
  decide +kernel

theorem runs_r17_part8 : ∀ i ∈ List.range 8, RunsAt 17 (64+i) := by
  decide +kernel

theorem runs_r17_part9 : ∀ i ∈ List.range 8, RunsAt 17 (72+i) := by
  decide +kernel

theorem runs_r17_part10 : ∀ i ∈ List.range 8, RunsAt 17 (80+i) := by
  decide +kernel

theorem runs_r17_part11 : ∀ i ∈ List.range 8, RunsAt 17 (88+i) := by
  decide +kernel

theorem runs_r17_part12 : ∀ i ∈ List.range 8, RunsAt 17 (96+i) := by
  decide +kernel

theorem runs_r17_part13 : ∀ i ∈ List.range 8, RunsAt 17 (104+i) := by
  decide +kernel

theorem runs_r17_part14 : ∀ i ∈ List.range 8, RunsAt 17 (112+i) := by
  decide +kernel

theorem runs_r17_part15 : ∀ i ∈ List.range 3, RunsAt 17 (120+i) := by
  decide +kernel

theorem runs_r17 : ∀ V ∈ List.range 123, RunsAt 17 V := by
  intro V hV
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r17_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r17_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r17_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r17_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r17_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r17_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r17_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r17_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r17_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r17_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r17_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r17_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r17_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r17_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r17_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi := runs_r17_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r18_part0 : ∀ i ∈ List.range 8, RunsAt 18 (0+i) := by
  decide +kernel

theorem runs_r18_part1 : ∀ i ∈ List.range 8, RunsAt 18 (8+i) := by
  decide +kernel

theorem runs_r18_part2 : ∀ i ∈ List.range 8, RunsAt 18 (16+i) := by
  decide +kernel

theorem runs_r18_part3 : ∀ i ∈ List.range 8, RunsAt 18 (24+i) := by
  decide +kernel

theorem runs_r18_part4 : ∀ i ∈ List.range 8, RunsAt 18 (32+i) := by
  decide +kernel

theorem runs_r18_part5 : ∀ i ∈ List.range 8, RunsAt 18 (40+i) := by
  decide +kernel

theorem runs_r18_part6 : ∀ i ∈ List.range 8, RunsAt 18 (48+i) := by
  decide +kernel

theorem runs_r18_part7 : ∀ i ∈ List.range 8, RunsAt 18 (56+i) := by
  decide +kernel

theorem runs_r18_part8 : ∀ i ∈ List.range 8, RunsAt 18 (64+i) := by
  decide +kernel

theorem runs_r18_part9 : ∀ i ∈ List.range 8, RunsAt 18 (72+i) := by
  decide +kernel

theorem runs_r18_part10 : ∀ i ∈ List.range 8, RunsAt 18 (80+i) := by
  decide +kernel

theorem runs_r18_part11 : ∀ i ∈ List.range 8, RunsAt 18 (88+i) := by
  decide +kernel

theorem runs_r18_part12 : ∀ i ∈ List.range 8, RunsAt 18 (96+i) := by
  decide +kernel

theorem runs_r18_part13 : ∀ i ∈ List.range 8, RunsAt 18 (104+i) := by
  decide +kernel

theorem runs_r18_part14 : ∀ i ∈ List.range 8, RunsAt 18 (112+i) := by
  decide +kernel

theorem runs_r18_part15 : ∀ i ∈ List.range 2, RunsAt 18 (120+i) := by
  decide +kernel

theorem runs_r18 : ∀ V ∈ List.range 122, RunsAt 18 V := by
  intro V hV
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r18_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r18_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r18_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r18_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r18_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r18_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r18_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r18_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r18_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r18_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r18_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r18_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r18_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r18_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r18_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi := runs_r18_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r19_part0 : ∀ i ∈ List.range 8, RunsAt 19 (0+i) := by
  decide +kernel

theorem runs_r19_part1 : ∀ i ∈ List.range 8, RunsAt 19 (8+i) := by
  decide +kernel

theorem runs_r19_part2 : ∀ i ∈ List.range 8, RunsAt 19 (16+i) := by
  decide +kernel

theorem runs_r19_part3 : ∀ i ∈ List.range 8, RunsAt 19 (24+i) := by
  decide +kernel

theorem runs_r19_part4 : ∀ i ∈ List.range 8, RunsAt 19 (32+i) := by
  decide +kernel

theorem runs_r19_part5 : ∀ i ∈ List.range 8, RunsAt 19 (40+i) := by
  decide +kernel

theorem runs_r19_part6 : ∀ i ∈ List.range 8, RunsAt 19 (48+i) := by
  decide +kernel

theorem runs_r19_part7 : ∀ i ∈ List.range 8, RunsAt 19 (56+i) := by
  decide +kernel

theorem runs_r19_part8 : ∀ i ∈ List.range 8, RunsAt 19 (64+i) := by
  decide +kernel

theorem runs_r19_part9 : ∀ i ∈ List.range 8, RunsAt 19 (72+i) := by
  decide +kernel

theorem runs_r19_part10 : ∀ i ∈ List.range 8, RunsAt 19 (80+i) := by
  decide +kernel

theorem runs_r19_part11 : ∀ i ∈ List.range 8, RunsAt 19 (88+i) := by
  decide +kernel

theorem runs_r19_part12 : ∀ i ∈ List.range 8, RunsAt 19 (96+i) := by
  decide +kernel

theorem runs_r19_part13 : ∀ i ∈ List.range 8, RunsAt 19 (104+i) := by
  decide +kernel

theorem runs_r19_part14 : ∀ i ∈ List.range 8, RunsAt 19 (112+i) := by
  decide +kernel

theorem runs_r19_part15 : ∀ i ∈ List.range 1, RunsAt 19 (120+i) := by
  decide +kernel

theorem runs_r19 : ∀ V ∈ List.range 121, RunsAt 19 V := by
  intro V hV
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r19_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r19_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r19_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r19_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r19_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r19_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r19_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r19_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r19_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r19_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r19_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r19_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r19_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r19_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r19_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi := runs_r19_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r20_part0 : ∀ i ∈ List.range 8, RunsAt 20 (0+i) := by
  decide +kernel

theorem runs_r20_part1 : ∀ i ∈ List.range 8, RunsAt 20 (8+i) := by
  decide +kernel

theorem runs_r20_part2 : ∀ i ∈ List.range 8, RunsAt 20 (16+i) := by
  decide +kernel

theorem runs_r20_part3 : ∀ i ∈ List.range 8, RunsAt 20 (24+i) := by
  decide +kernel

theorem runs_r20_part4 : ∀ i ∈ List.range 8, RunsAt 20 (32+i) := by
  decide +kernel

theorem runs_r20_part5 : ∀ i ∈ List.range 8, RunsAt 20 (40+i) := by
  decide +kernel

theorem runs_r20_part6 : ∀ i ∈ List.range 8, RunsAt 20 (48+i) := by
  decide +kernel

theorem runs_r20_part7 : ∀ i ∈ List.range 8, RunsAt 20 (56+i) := by
  decide +kernel

theorem runs_r20_part8 : ∀ i ∈ List.range 8, RunsAt 20 (64+i) := by
  decide +kernel

theorem runs_r20_part9 : ∀ i ∈ List.range 8, RunsAt 20 (72+i) := by
  decide +kernel

theorem runs_r20_part10 : ∀ i ∈ List.range 8, RunsAt 20 (80+i) := by
  decide +kernel

theorem runs_r20_part11 : ∀ i ∈ List.range 8, RunsAt 20 (88+i) := by
  decide +kernel

theorem runs_r20_part12 : ∀ i ∈ List.range 8, RunsAt 20 (96+i) := by
  decide +kernel

theorem runs_r20_part13 : ∀ i ∈ List.range 8, RunsAt 20 (104+i) := by
  decide +kernel

theorem runs_r20_part14 : ∀ i ∈ List.range 8, RunsAt 20 (112+i) := by
  decide +kernel

theorem runs_r20 : ∀ V ∈ List.range 120, RunsAt 20 V := by
  intro V hV
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r20_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r20_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r20_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r20_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r20_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r20_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r20_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r20_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r20_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r20_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r20_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r20_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r20_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r20_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi := runs_r20_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
