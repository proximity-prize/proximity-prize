import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics
import ProximityPrize.SubmissionLower.BoundaryTailPrefixChecked

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseChecks Lower80801.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r1_part0 : ∀ i ∈ List.range 8, RunsAt 1 (0+i) := by
  decide +kernel

theorem runs_r1_part1 : ∀ i ∈ List.range 8, RunsAt 1 (8+i) := by
  decide +kernel

theorem runs_r1_part2 : ∀ i ∈ List.range 8, RunsAt 1 (16+i) := by
  decide +kernel

theorem runs_r1_part3 : ∀ i ∈ List.range 8, RunsAt 1 (24+i) := by
  decide +kernel

theorem runs_r1_part4 : ∀ i ∈ List.range 8, RunsAt 1 (32+i) := by
  decide +kernel

theorem runs_r1_part5 : ∀ i ∈ List.range 8, RunsAt 1 (40+i) := by
  decide +kernel

theorem runs_r1_part6 : ∀ i ∈ List.range 8, RunsAt 1 (48+i) := by
  decide +kernel

theorem runs_r1_part7 : ∀ i ∈ List.range 8, RunsAt 1 (56+i) := by
  decide +kernel

theorem runs_r1_part8 : ∀ i ∈ List.range 8, RunsAt 1 (64+i) := by
  decide +kernel

theorem runs_r1_part9 : ∀ i ∈ List.range 8, RunsAt 1 (72+i) := by
  decide +kernel

theorem runs_r1_part10 : ∀ i ∈ List.range 8, RunsAt 1 (80+i) := by
  decide +kernel

theorem runs_r1_part11 : ∀ i ∈ List.range 8, RunsAt 1 (88+i) := by
  decide +kernel

theorem runs_r1_part12 : ∀ i ∈ List.range 8, RunsAt 1 (96+i) := by
  decide +kernel

theorem runs_r1_part13 : ∀ i ∈ List.range 8, RunsAt 1 (104+i) := by
  decide +kernel

theorem runs_r1_part14 : ∀ i ∈ List.range 8, RunsAt 1 (112+i) := by
  decide +kernel

theorem runs_r1_part15 : ∀ i ∈ List.range 8, RunsAt 1 (120+i) := by
  decide +kernel

theorem runs_r1_part16 : ∀ i ∈ List.range 8, RunsAt 1 (128+i) := by
  decide +kernel

theorem runs_r1_part17 : ∀ i ∈ List.range 3, RunsAt 1 (136+i) := by
  decide +kernel

theorem runs_r1 : ∀ V ∈ List.range 139, RunsAt 1 V := by
  intro V hV
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r1_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r1_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r1_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r1_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r1_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r1_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r1_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r1_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r1_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r1_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r1_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r1_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r1_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r1_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r1_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r1_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16 : V < 136
                                  · have hi := runs_r1_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi := runs_r1_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem runs_r2_part0 : ∀ i ∈ List.range 8, RunsAt 2 (0+i) := by
  decide +kernel

theorem runs_r2_part1 : ∀ i ∈ List.range 8, RunsAt 2 (8+i) := by
  decide +kernel

theorem runs_r2_part2 : ∀ i ∈ List.range 8, RunsAt 2 (16+i) := by
  decide +kernel

theorem runs_r2_part3 : ∀ i ∈ List.range 8, RunsAt 2 (24+i) := by
  decide +kernel

theorem runs_r2_part4 : ∀ i ∈ List.range 8, RunsAt 2 (32+i) := by
  decide +kernel

theorem runs_r2_part5 : ∀ i ∈ List.range 8, RunsAt 2 (40+i) := by
  decide +kernel

theorem runs_r2_part6 : ∀ i ∈ List.range 8, RunsAt 2 (48+i) := by
  decide +kernel

theorem runs_r2_part7 : ∀ i ∈ List.range 8, RunsAt 2 (56+i) := by
  decide +kernel

theorem runs_r2_part8 : ∀ i ∈ List.range 8, RunsAt 2 (64+i) := by
  decide +kernel

theorem runs_r2_part9 : ∀ i ∈ List.range 8, RunsAt 2 (72+i) := by
  decide +kernel

theorem runs_r2_part10 : ∀ i ∈ List.range 8, RunsAt 2 (80+i) := by
  decide +kernel

theorem runs_r2_part11 : ∀ i ∈ List.range 8, RunsAt 2 (88+i) := by
  decide +kernel

theorem runs_r2_part12 : ∀ i ∈ List.range 8, RunsAt 2 (96+i) := by
  decide +kernel

theorem runs_r2_part13 : ∀ i ∈ List.range 8, RunsAt 2 (104+i) := by
  decide +kernel

theorem runs_r2_part14 : ∀ i ∈ List.range 8, RunsAt 2 (112+i) := by
  decide +kernel

theorem runs_r2_part15 : ∀ i ∈ List.range 8, RunsAt 2 (120+i) := by
  decide +kernel

theorem runs_r2_part16 : ∀ i ∈ List.range 8, RunsAt 2 (128+i) := by
  decide +kernel

theorem runs_r2_part17 : ∀ i ∈ List.range 2, RunsAt 2 (136+i) := by
  decide +kernel

theorem runs_r2 : ∀ V ∈ List.range 138, RunsAt 2 V := by
  intro V hV
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r2_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r2_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r2_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r2_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r2_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r2_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r2_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r2_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r2_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r2_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r2_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r2_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r2_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r2_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r2_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r2_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16 : V < 136
                                  · have hi := runs_r2_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi := runs_r2_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem runs_r3_part0 : ∀ i ∈ List.range 8, RunsAt 3 (0+i) := by
  decide +kernel

theorem runs_r3_part1 : ∀ i ∈ List.range 8, RunsAt 3 (8+i) := by
  decide +kernel

theorem runs_r3_part2 : ∀ i ∈ List.range 8, RunsAt 3 (16+i) := by
  decide +kernel

theorem runs_r3_part3 : ∀ i ∈ List.range 8, RunsAt 3 (24+i) := by
  decide +kernel

theorem runs_r3_part4 : ∀ i ∈ List.range 8, RunsAt 3 (32+i) := by
  decide +kernel

theorem runs_r3_part5 : ∀ i ∈ List.range 8, RunsAt 3 (40+i) := by
  decide +kernel

theorem runs_r3_part6 : ∀ i ∈ List.range 8, RunsAt 3 (48+i) := by
  decide +kernel

theorem runs_r3_part7 : ∀ i ∈ List.range 8, RunsAt 3 (56+i) := by
  decide +kernel

theorem runs_r3_part8 : ∀ i ∈ List.range 8, RunsAt 3 (64+i) := by
  decide +kernel

theorem runs_r3_part9 : ∀ i ∈ List.range 8, RunsAt 3 (72+i) := by
  decide +kernel

theorem runs_r3_part10 : ∀ i ∈ List.range 8, RunsAt 3 (80+i) := by
  decide +kernel

theorem runs_r3_part11 : ∀ i ∈ List.range 8, RunsAt 3 (88+i) := by
  decide +kernel

theorem runs_r3_part12 : ∀ i ∈ List.range 8, RunsAt 3 (96+i) := by
  decide +kernel

theorem runs_r3_part13 : ∀ i ∈ List.range 8, RunsAt 3 (104+i) := by
  decide +kernel

theorem runs_r3_part14 : ∀ i ∈ List.range 8, RunsAt 3 (112+i) := by
  decide +kernel

theorem runs_r3_part15 : ∀ i ∈ List.range 8, RunsAt 3 (120+i) := by
  decide +kernel

theorem runs_r3_part16 : ∀ i ∈ List.range 8, RunsAt 3 (128+i) := by
  decide +kernel

theorem runs_r3_part17 : ∀ i ∈ List.range 1, RunsAt 3 (136+i) := by
  decide +kernel

theorem runs_r3 : ∀ V ∈ List.range 137, RunsAt 3 V := by
  intro V hV
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r3_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r3_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r3_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r3_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r3_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r3_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r3_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r3_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r3_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r3_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r3_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r3_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r3_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r3_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r3_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r3_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16 : V < 136
                                  · have hi := runs_r3_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi := runs_r3_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem runs_r4_part0 : ∀ i ∈ List.range 8, RunsAt 4 (0+i) := by
  decide +kernel

theorem runs_r4_part1 : ∀ i ∈ List.range 8, RunsAt 4 (8+i) := by
  decide +kernel

theorem runs_r4_part2 : ∀ i ∈ List.range 8, RunsAt 4 (16+i) := by
  decide +kernel

theorem runs_r4_part3 : ∀ i ∈ List.range 8, RunsAt 4 (24+i) := by
  decide +kernel

theorem runs_r4_part4 : ∀ i ∈ List.range 8, RunsAt 4 (32+i) := by
  decide +kernel

theorem runs_r4_part5 : ∀ i ∈ List.range 8, RunsAt 4 (40+i) := by
  decide +kernel

theorem runs_r4_part6 : ∀ i ∈ List.range 8, RunsAt 4 (48+i) := by
  decide +kernel

theorem runs_r4_part7 : ∀ i ∈ List.range 8, RunsAt 4 (56+i) := by
  decide +kernel

theorem runs_r4_part8 : ∀ i ∈ List.range 8, RunsAt 4 (64+i) := by
  decide +kernel

theorem runs_r4_part9 : ∀ i ∈ List.range 8, RunsAt 4 (72+i) := by
  decide +kernel

theorem runs_r4_part10 : ∀ i ∈ List.range 8, RunsAt 4 (80+i) := by
  decide +kernel

theorem runs_r4_part11 : ∀ i ∈ List.range 8, RunsAt 4 (88+i) := by
  decide +kernel

theorem runs_r4_part12 : ∀ i ∈ List.range 8, RunsAt 4 (96+i) := by
  decide +kernel

theorem runs_r4_part13 : ∀ i ∈ List.range 8, RunsAt 4 (104+i) := by
  decide +kernel

theorem runs_r4_part14 : ∀ i ∈ List.range 8, RunsAt 4 (112+i) := by
  decide +kernel

theorem runs_r4_part15 : ∀ i ∈ List.range 8, RunsAt 4 (120+i) := by
  decide +kernel

theorem runs_r4_part16 : ∀ i ∈ List.range 8, RunsAt 4 (128+i) := by
  decide +kernel

theorem runs_r4 : ∀ V ∈ List.range 136, RunsAt 4 V := by
  intro V hV
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r4_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r4_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r4_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r4_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r4_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r4_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r4_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r4_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r4_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r4_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r4_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r4_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r4_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r4_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r4_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r4_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi := runs_r4_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r5_part0 : ∀ i ∈ List.range 8, RunsAt 5 (0+i) := by
  decide +kernel

theorem runs_r5_part1 : ∀ i ∈ List.range 8, RunsAt 5 (8+i) := by
  decide +kernel

theorem runs_r5_part2 : ∀ i ∈ List.range 8, RunsAt 5 (16+i) := by
  decide +kernel

theorem runs_r5_part3 : ∀ i ∈ List.range 8, RunsAt 5 (24+i) := by
  decide +kernel

theorem runs_r5_part4 : ∀ i ∈ List.range 8, RunsAt 5 (32+i) := by
  decide +kernel

theorem runs_r5_part5 : ∀ i ∈ List.range 8, RunsAt 5 (40+i) := by
  decide +kernel

theorem runs_r5_part6 : ∀ i ∈ List.range 8, RunsAt 5 (48+i) := by
  decide +kernel

theorem runs_r5_part7 : ∀ i ∈ List.range 8, RunsAt 5 (56+i) := by
  decide +kernel

theorem runs_r5_part8 : ∀ i ∈ List.range 8, RunsAt 5 (64+i) := by
  decide +kernel

theorem runs_r5_part9 : ∀ i ∈ List.range 8, RunsAt 5 (72+i) := by
  decide +kernel

theorem runs_r5_part10 : ∀ i ∈ List.range 8, RunsAt 5 (80+i) := by
  decide +kernel

theorem runs_r5_part11 : ∀ i ∈ List.range 8, RunsAt 5 (88+i) := by
  decide +kernel

theorem runs_r5_part12 : ∀ i ∈ List.range 8, RunsAt 5 (96+i) := by
  decide +kernel

theorem runs_r5_part13 : ∀ i ∈ List.range 8, RunsAt 5 (104+i) := by
  decide +kernel

theorem runs_r5_part14 : ∀ i ∈ List.range 8, RunsAt 5 (112+i) := by
  decide +kernel

theorem runs_r5_part15 : ∀ i ∈ List.range 8, RunsAt 5 (120+i) := by
  decide +kernel

theorem runs_r5_part16 : ∀ i ∈ List.range 7, RunsAt 5 (128+i) := by
  decide +kernel

theorem runs_r5 : ∀ V ∈ List.range 135, RunsAt 5 V := by
  intro V hV
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hi := runs_r5_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1 : V < 16
    · have hi := runs_r5_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2 : V < 24
      · have hi := runs_r5_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3 : V < 32
        · have hi := runs_r5_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4 : V < 40
          · have hi := runs_r5_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5 : V < 48
            · have hi := runs_r5_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6 : V < 56
              · have hi := runs_r5_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7 : V < 64
                · have hi := runs_r5_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8 : V < 72
                  · have hi := runs_r5_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9 : V < 80
                    · have hi := runs_r5_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10 : V < 88
                      · have hi := runs_r5_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11 : V < 96
                        · have hi := runs_r5_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12 : V < 104
                          · have hi := runs_r5_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13 : V < 112
                            · have hi := runs_r5_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14 : V < 120
                              · have hi := runs_r5_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15 : V < 128
                                · have hi := runs_r5_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi := runs_r5_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
