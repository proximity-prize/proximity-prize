import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics
import ProximityPrize.SubmissionLower.BoundaryTailPrefixChecked

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseChecks Lower80801.PhaseSemantics
open Lower80801.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r1_part0:∀ i ∈ List.range 8,RunsAt 1 (0+i):=by
  decide +kernel

theorem runs_r1_part1:∀ i ∈ List.range 8,RunsAt 1 (8+i):=by
  decide +kernel

theorem runs_r1_part2:∀ i ∈ List.range 8,RunsAt 1 (16+i):=by
  decide +kernel

theorem runs_r1_part3:∀ i ∈ List.range 8,RunsAt 1 (24+i):=by
  decide +kernel

theorem runs_r1_part4:∀ i ∈ List.range 8,RunsAt 1 (32+i):=by
  decide +kernel

theorem runs_r1_part5:∀ i ∈ List.range 8,RunsAt 1 (40+i):=by
  decide +kernel

theorem runs_r1_part6:∀ i ∈ List.range 8,RunsAt 1 (48+i):=by
  decide +kernel

theorem runs_r1_part7:∀ i ∈ List.range 8,RunsAt 1 (56+i):=by
  decide +kernel

theorem runs_r1_part8:∀ i ∈ List.range 8,RunsAt 1 (64+i):=by
  decide +kernel

theorem runs_r1_part9:∀ i ∈ List.range 8,RunsAt 1 (72+i):=by
  decide +kernel

theorem runs_r1_part10:∀ i ∈ List.range 8,RunsAt 1 (80+i):=by
  decide +kernel

theorem runs_r1_part11:∀ i ∈ List.range 8,RunsAt 1 (88+i):=by
  decide +kernel

theorem runs_r1_part12:∀ i ∈ List.range 8,RunsAt 1 (96+i):=by
  decide +kernel

theorem runs_r1_part13:∀ i ∈ List.range 8,RunsAt 1 (104+i):=by
  decide +kernel

theorem runs_r1_part14:∀ i ∈ List.range 8,RunsAt 1 (112+i):=by
  decide +kernel

theorem runs_r1_part15:∀ i ∈ List.range 8,RunsAt 1 (120+i):=by
  decide +kernel

theorem runs_r1_part16:∀ i ∈ List.range 8,RunsAt 1 (128+i):=by
  decide +kernel

theorem runs_r1_part17:∀ i ∈ List.range 6,RunsAt 1 (136+i):=by
  decide +kernel

theorem runs_r1:∀ V ∈ List.range 142,RunsAt 1 V:=by
  intro V hV
  have hv:V < 142:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r1_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r1_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r1_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r1_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r1_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r1_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r1_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r1_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r1_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r1_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r1_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r1_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r1_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r1_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r1_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r1_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=runs_r1_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=runs_r1_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem runs_r2_part0:∀ i ∈ List.range 8,RunsAt 2 (0+i):=by
  decide +kernel

theorem runs_r2_part1:∀ i ∈ List.range 8,RunsAt 2 (8+i):=by
  decide +kernel

theorem runs_r2_part2:∀ i ∈ List.range 8,RunsAt 2 (16+i):=by
  decide +kernel

theorem runs_r2_part3:∀ i ∈ List.range 8,RunsAt 2 (24+i):=by
  decide +kernel

theorem runs_r2_part4:∀ i ∈ List.range 8,RunsAt 2 (32+i):=by
  decide +kernel

theorem runs_r2_part5:∀ i ∈ List.range 8,RunsAt 2 (40+i):=by
  decide +kernel

theorem runs_r2_part6:∀ i ∈ List.range 8,RunsAt 2 (48+i):=by
  decide +kernel

theorem runs_r2_part7:∀ i ∈ List.range 8,RunsAt 2 (56+i):=by
  decide +kernel

theorem runs_r2_part8:∀ i ∈ List.range 8,RunsAt 2 (64+i):=by
  decide +kernel

theorem runs_r2_part9:∀ i ∈ List.range 8,RunsAt 2 (72+i):=by
  decide +kernel

theorem runs_r2_part10:∀ i ∈ List.range 8,RunsAt 2 (80+i):=by
  decide +kernel

theorem runs_r2_part11:∀ i ∈ List.range 8,RunsAt 2 (88+i):=by
  decide +kernel

theorem runs_r2_part12:∀ i ∈ List.range 8,RunsAt 2 (96+i):=by
  decide +kernel

theorem runs_r2_part13:∀ i ∈ List.range 8,RunsAt 2 (104+i):=by
  decide +kernel

theorem runs_r2_part14:∀ i ∈ List.range 8,RunsAt 2 (112+i):=by
  decide +kernel

theorem runs_r2_part15:∀ i ∈ List.range 8,RunsAt 2 (120+i):=by
  decide +kernel

theorem runs_r2_part16:∀ i ∈ List.range 8,RunsAt 2 (128+i):=by
  decide +kernel

theorem runs_r2_part17:∀ i ∈ List.range 5,RunsAt 2 (136+i):=by
  decide +kernel

theorem runs_r2:∀ V ∈ List.range 141,RunsAt 2 V:=by
  intro V hV
  have hv:V < 141:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r2_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r2_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r2_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r2_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r2_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r2_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r2_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r2_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r2_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r2_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r2_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r2_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r2_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r2_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r2_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r2_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=runs_r2_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=runs_r2_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem runs_r3_part0:∀ i ∈ List.range 8,RunsAt 3 (0+i):=by
  decide +kernel

theorem runs_r3_part1:∀ i ∈ List.range 8,RunsAt 3 (8+i):=by
  decide +kernel

theorem runs_r3_part2:∀ i ∈ List.range 8,RunsAt 3 (16+i):=by
  decide +kernel

theorem runs_r3_part3:∀ i ∈ List.range 8,RunsAt 3 (24+i):=by
  decide +kernel

theorem runs_r3_part4:∀ i ∈ List.range 8,RunsAt 3 (32+i):=by
  decide +kernel

theorem runs_r3_part5:∀ i ∈ List.range 8,RunsAt 3 (40+i):=by
  decide +kernel

theorem runs_r3_part6:∀ i ∈ List.range 8,RunsAt 3 (48+i):=by
  decide +kernel

theorem runs_r3_part7:∀ i ∈ List.range 8,RunsAt 3 (56+i):=by
  decide +kernel

theorem runs_r3_part8:∀ i ∈ List.range 8,RunsAt 3 (64+i):=by
  decide +kernel

theorem runs_r3_part9:∀ i ∈ List.range 8,RunsAt 3 (72+i):=by
  decide +kernel

theorem runs_r3_part10:∀ i ∈ List.range 8,RunsAt 3 (80+i):=by
  decide +kernel

theorem runs_r3_part11:∀ i ∈ List.range 8,RunsAt 3 (88+i):=by
  decide +kernel

theorem runs_r3_part12:∀ i ∈ List.range 8,RunsAt 3 (96+i):=by
  decide +kernel

theorem runs_r3_part13:∀ i ∈ List.range 8,RunsAt 3 (104+i):=by
  decide +kernel

theorem runs_r3_part14:∀ i ∈ List.range 8,RunsAt 3 (112+i):=by
  decide +kernel

theorem runs_r3_part15:∀ i ∈ List.range 8,RunsAt 3 (120+i):=by
  decide +kernel

theorem runs_r3_part16:∀ i ∈ List.range 8,RunsAt 3 (128+i):=by
  decide +kernel

theorem runs_r3_part17:∀ i ∈ List.range 4,RunsAt 3 (136+i):=by
  decide +kernel

theorem runs_r3:∀ V ∈ List.range 140,RunsAt 3 V:=by
  intro V hV
  have hv:V < 140:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r3_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r3_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r3_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r3_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r3_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r3_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r3_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r3_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r3_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r3_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r3_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r3_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r3_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r3_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r3_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r3_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=runs_r3_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=runs_r3_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem runs_r4_part0:∀ i ∈ List.range 8,RunsAt 4 (0+i):=by
  decide +kernel

theorem runs_r4_part1:∀ i ∈ List.range 8,RunsAt 4 (8+i):=by
  decide +kernel

theorem runs_r4_part2:∀ i ∈ List.range 8,RunsAt 4 (16+i):=by
  decide +kernel

theorem runs_r4_part3:∀ i ∈ List.range 8,RunsAt 4 (24+i):=by
  decide +kernel

theorem runs_r4_part4:∀ i ∈ List.range 8,RunsAt 4 (32+i):=by
  decide +kernel

theorem runs_r4_part5:∀ i ∈ List.range 8,RunsAt 4 (40+i):=by
  decide +kernel

theorem runs_r4_part6:∀ i ∈ List.range 8,RunsAt 4 (48+i):=by
  decide +kernel

theorem runs_r4_part7:∀ i ∈ List.range 8,RunsAt 4 (56+i):=by
  decide +kernel

theorem runs_r4_part8:∀ i ∈ List.range 8,RunsAt 4 (64+i):=by
  decide +kernel

theorem runs_r4_part9:∀ i ∈ List.range 8,RunsAt 4 (72+i):=by
  decide +kernel

theorem runs_r4_part10:∀ i ∈ List.range 8,RunsAt 4 (80+i):=by
  decide +kernel

theorem runs_r4_part11:∀ i ∈ List.range 8,RunsAt 4 (88+i):=by
  decide +kernel

theorem runs_r4_part12:∀ i ∈ List.range 8,RunsAt 4 (96+i):=by
  decide +kernel

theorem runs_r4_part13:∀ i ∈ List.range 8,RunsAt 4 (104+i):=by
  decide +kernel

theorem runs_r4_part14:∀ i ∈ List.range 8,RunsAt 4 (112+i):=by
  decide +kernel

theorem runs_r4_part15:∀ i ∈ List.range 8,RunsAt 4 (120+i):=by
  decide +kernel

theorem runs_r4_part16:∀ i ∈ List.range 8,RunsAt 4 (128+i):=by
  decide +kernel

theorem runs_r4_part17:∀ i ∈ List.range 3,RunsAt 4 (136+i):=by
  decide +kernel

theorem runs_r4:∀ V ∈ List.range 139,RunsAt 4 V:=by
  intro V hV
  have hv:V < 139:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r4_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r4_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r4_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r4_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r4_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r4_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r4_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r4_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r4_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r4_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r4_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r4_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r4_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r4_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r4_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r4_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=runs_r4_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=runs_r4_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem runs_r5_part0:∀ i ∈ List.range 8,RunsAt 5 (0+i):=by
  decide +kernel

theorem runs_r5_part1:∀ i ∈ List.range 8,RunsAt 5 (8+i):=by
  decide +kernel

theorem runs_r5_part2:∀ i ∈ List.range 8,RunsAt 5 (16+i):=by
  decide +kernel

theorem runs_r5_part3:∀ i ∈ List.range 8,RunsAt 5 (24+i):=by
  decide +kernel

theorem runs_r5_part4:∀ i ∈ List.range 8,RunsAt 5 (32+i):=by
  decide +kernel

theorem runs_r5_part5:∀ i ∈ List.range 8,RunsAt 5 (40+i):=by
  decide +kernel

theorem runs_r5_part6:∀ i ∈ List.range 8,RunsAt 5 (48+i):=by
  decide +kernel

theorem runs_r5_part7:∀ i ∈ List.range 8,RunsAt 5 (56+i):=by
  decide +kernel

theorem runs_r5_part8:∀ i ∈ List.range 8,RunsAt 5 (64+i):=by
  decide +kernel

theorem runs_r5_part9:∀ i ∈ List.range 8,RunsAt 5 (72+i):=by
  decide +kernel

theorem runs_r5_part10:∀ i ∈ List.range 8,RunsAt 5 (80+i):=by
  decide +kernel

theorem runs_r5_part11:∀ i ∈ List.range 8,RunsAt 5 (88+i):=by
  decide +kernel

theorem runs_r5_part12:∀ i ∈ List.range 8,RunsAt 5 (96+i):=by
  decide +kernel

theorem runs_r5_part13:∀ i ∈ List.range 8,RunsAt 5 (104+i):=by
  decide +kernel

theorem runs_r5_part14:∀ i ∈ List.range 8,RunsAt 5 (112+i):=by
  decide +kernel

theorem runs_r5_part15:∀ i ∈ List.range 8,RunsAt 5 (120+i):=by
  decide +kernel

theorem runs_r5_part16:∀ i ∈ List.range 8,RunsAt 5 (128+i):=by
  decide +kernel

theorem runs_r5_part17:∀ i ∈ List.range 2,RunsAt 5 (136+i):=by
  decide +kernel

theorem runs_r5:∀ V ∈ List.range 138,RunsAt 5 V:=by
  intro V hV
  have hv:V < 138:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r5_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r5_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r5_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r5_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r5_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r5_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r5_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r5_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r5_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r5_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r5_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r5_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r5_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r5_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r5_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r5_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=runs_r5_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=runs_r5_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r6_part0:∀ i ∈ List.range 8,RunsAt 6 (0+i):=by
  decide +kernel

theorem runs_r6_part1:∀ i ∈ List.range 8,RunsAt 6 (8+i):=by
  decide +kernel

theorem runs_r6_part2:∀ i ∈ List.range 8,RunsAt 6 (16+i):=by
  decide +kernel

theorem runs_r6_part3:∀ i ∈ List.range 8,RunsAt 6 (24+i):=by
  decide +kernel

theorem runs_r6_part4:∀ i ∈ List.range 8,RunsAt 6 (32+i):=by
  decide +kernel

theorem runs_r6_part5:∀ i ∈ List.range 8,RunsAt 6 (40+i):=by
  decide +kernel

theorem runs_r6_part6:∀ i ∈ List.range 8,RunsAt 6 (48+i):=by
  decide +kernel

theorem runs_r6_part7:∀ i ∈ List.range 8,RunsAt 6 (56+i):=by
  decide +kernel

theorem runs_r6_part8:∀ i ∈ List.range 8,RunsAt 6 (64+i):=by
  decide +kernel

theorem runs_r6_part9:∀ i ∈ List.range 8,RunsAt 6 (72+i):=by
  decide +kernel

theorem runs_r6_part10:∀ i ∈ List.range 8,RunsAt 6 (80+i):=by
  decide +kernel

theorem runs_r6_part11:∀ i ∈ List.range 8,RunsAt 6 (88+i):=by
  decide +kernel

theorem runs_r6_part12:∀ i ∈ List.range 8,RunsAt 6 (96+i):=by
  decide +kernel

theorem runs_r6_part13:∀ i ∈ List.range 8,RunsAt 6 (104+i):=by
  decide +kernel

theorem runs_r6_part14:∀ i ∈ List.range 8,RunsAt 6 (112+i):=by
  decide +kernel

theorem runs_r6_part15:∀ i ∈ List.range 8,RunsAt 6 (120+i):=by
  decide +kernel

theorem runs_r6_part16:∀ i ∈ List.range 8,RunsAt 6 (128+i):=by
  decide +kernel

theorem runs_r6_part17:∀ i ∈ List.range 1,RunsAt 6 (136+i):=by
  decide +kernel

theorem runs_r6:∀ V ∈ List.range 137,RunsAt 6 V:=by
  intro V hV
  have hv:V < 137:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r6_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r6_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r6_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r6_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r6_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r6_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r6_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r6_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r6_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r6_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r6_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r6_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r6_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r6_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r6_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r6_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=runs_r6_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=runs_r6_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem runs_r7_part0:∀ i ∈ List.range 8,RunsAt 7 (0+i):=by
  decide +kernel

theorem runs_r7_part1:∀ i ∈ List.range 8,RunsAt 7 (8+i):=by
  decide +kernel

theorem runs_r7_part2:∀ i ∈ List.range 8,RunsAt 7 (16+i):=by
  decide +kernel

theorem runs_r7_part3:∀ i ∈ List.range 8,RunsAt 7 (24+i):=by
  decide +kernel

theorem runs_r7_part4:∀ i ∈ List.range 8,RunsAt 7 (32+i):=by
  decide +kernel

theorem runs_r7_part5:∀ i ∈ List.range 8,RunsAt 7 (40+i):=by
  decide +kernel

theorem runs_r7_part6:∀ i ∈ List.range 8,RunsAt 7 (48+i):=by
  decide +kernel

theorem runs_r7_part7:∀ i ∈ List.range 8,RunsAt 7 (56+i):=by
  decide +kernel

theorem runs_r7_part8:∀ i ∈ List.range 8,RunsAt 7 (64+i):=by
  decide +kernel

theorem runs_r7_part9:∀ i ∈ List.range 8,RunsAt 7 (72+i):=by
  decide +kernel

theorem runs_r7_part10:∀ i ∈ List.range 8,RunsAt 7 (80+i):=by
  decide +kernel

theorem runs_r7_part11:∀ i ∈ List.range 8,RunsAt 7 (88+i):=by
  decide +kernel

theorem runs_r7_part12:∀ i ∈ List.range 8,RunsAt 7 (96+i):=by
  decide +kernel

theorem runs_r7_part13:∀ i ∈ List.range 8,RunsAt 7 (104+i):=by
  decide +kernel

theorem runs_r7_part14:∀ i ∈ List.range 8,RunsAt 7 (112+i):=by
  decide +kernel

theorem runs_r7_part15:∀ i ∈ List.range 8,RunsAt 7 (120+i):=by
  decide +kernel

theorem runs_r7_part16:∀ i ∈ List.range 8,RunsAt 7 (128+i):=by
  decide +kernel

theorem runs_r7:∀ V ∈ List.range 136,RunsAt 7 V:=by
  intro V hV
  have hv:V < 136:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r7_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r7_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r7_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r7_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r7_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r7_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r7_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r7_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r7_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r7_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r7_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r7_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r7_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r7_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r7_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r7_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=runs_r7_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r8_part0:∀ i ∈ List.range 8,RunsAt 8 (0+i):=by
  decide +kernel

theorem runs_r8_part1:∀ i ∈ List.range 8,RunsAt 8 (8+i):=by
  decide +kernel

theorem runs_r8_part2:∀ i ∈ List.range 8,RunsAt 8 (16+i):=by
  decide +kernel

theorem runs_r8_part3:∀ i ∈ List.range 8,RunsAt 8 (24+i):=by
  decide +kernel

theorem runs_r8_part4:∀ i ∈ List.range 8,RunsAt 8 (32+i):=by
  decide +kernel

theorem runs_r8_part5:∀ i ∈ List.range 8,RunsAt 8 (40+i):=by
  decide +kernel

theorem runs_r8_part6:∀ i ∈ List.range 8,RunsAt 8 (48+i):=by
  decide +kernel

theorem runs_r8_part7:∀ i ∈ List.range 8,RunsAt 8 (56+i):=by
  decide +kernel

theorem runs_r8_part8:∀ i ∈ List.range 8,RunsAt 8 (64+i):=by
  decide +kernel

theorem runs_r8_part9:∀ i ∈ List.range 8,RunsAt 8 (72+i):=by
  decide +kernel

theorem runs_r8_part10:∀ i ∈ List.range 8,RunsAt 8 (80+i):=by
  decide +kernel

theorem runs_r8_part11:∀ i ∈ List.range 8,RunsAt 8 (88+i):=by
  decide +kernel

theorem runs_r8_part12:∀ i ∈ List.range 8,RunsAt 8 (96+i):=by
  decide +kernel

theorem runs_r8_part13:∀ i ∈ List.range 8,RunsAt 8 (104+i):=by
  decide +kernel

theorem runs_r8_part14:∀ i ∈ List.range 8,RunsAt 8 (112+i):=by
  decide +kernel

theorem runs_r8_part15:∀ i ∈ List.range 8,RunsAt 8 (120+i):=by
  decide +kernel

theorem runs_r8_part16:∀ i ∈ List.range 7,RunsAt 8 (128+i):=by
  decide +kernel

theorem runs_r8:∀ V ∈ List.range 135,RunsAt 8 V:=by
  intro V hV
  have hv:V < 135:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r8_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r8_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r8_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r8_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r8_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r8_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r8_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r8_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r8_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r8_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r8_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r8_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r8_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r8_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r8_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r8_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=runs_r8_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r9_part0:∀ i ∈ List.range 8,RunsAt 9 (0+i):=by
  decide +kernel

theorem runs_r9_part1:∀ i ∈ List.range 8,RunsAt 9 (8+i):=by
  decide +kernel

theorem runs_r9_part2:∀ i ∈ List.range 8,RunsAt 9 (16+i):=by
  decide +kernel

theorem runs_r9_part3:∀ i ∈ List.range 8,RunsAt 9 (24+i):=by
  decide +kernel

theorem runs_r9_part4:∀ i ∈ List.range 8,RunsAt 9 (32+i):=by
  decide +kernel

theorem runs_r9_part5:∀ i ∈ List.range 8,RunsAt 9 (40+i):=by
  decide +kernel

theorem runs_r9_part6:∀ i ∈ List.range 8,RunsAt 9 (48+i):=by
  decide +kernel

theorem runs_r9_part7:∀ i ∈ List.range 8,RunsAt 9 (56+i):=by
  decide +kernel

theorem runs_r9_part8:∀ i ∈ List.range 8,RunsAt 9 (64+i):=by
  decide +kernel

theorem runs_r9_part9:∀ i ∈ List.range 8,RunsAt 9 (72+i):=by
  decide +kernel

theorem runs_r9_part10:∀ i ∈ List.range 8,RunsAt 9 (80+i):=by
  decide +kernel

theorem runs_r9_part11:∀ i ∈ List.range 8,RunsAt 9 (88+i):=by
  decide +kernel

theorem runs_r9_part12:∀ i ∈ List.range 8,RunsAt 9 (96+i):=by
  decide +kernel

theorem runs_r9_part13:∀ i ∈ List.range 8,RunsAt 9 (104+i):=by
  decide +kernel

theorem runs_r9_part14:∀ i ∈ List.range 8,RunsAt 9 (112+i):=by
  decide +kernel

theorem runs_r9_part15:∀ i ∈ List.range 8,RunsAt 9 (120+i):=by
  decide +kernel

theorem runs_r9_part16:∀ i ∈ List.range 6,RunsAt 9 (128+i):=by
  decide +kernel

theorem runs_r9:∀ V ∈ List.range 134,RunsAt 9 V:=by
  intro V hV
  have hv:V < 134:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r9_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r9_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r9_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r9_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r9_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r9_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r9_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r9_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r9_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r9_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r9_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r9_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r9_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r9_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r9_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r9_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=runs_r9_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r10_part0:∀ i ∈ List.range 8,RunsAt 10 (0+i):=by
  decide +kernel

theorem runs_r10_part1:∀ i ∈ List.range 8,RunsAt 10 (8+i):=by
  decide +kernel

theorem runs_r10_part2:∀ i ∈ List.range 8,RunsAt 10 (16+i):=by
  decide +kernel

theorem runs_r10_part3:∀ i ∈ List.range 8,RunsAt 10 (24+i):=by
  decide +kernel

theorem runs_r10_part4:∀ i ∈ List.range 8,RunsAt 10 (32+i):=by
  decide +kernel

theorem runs_r10_part5:∀ i ∈ List.range 8,RunsAt 10 (40+i):=by
  decide +kernel

theorem runs_r10_part6:∀ i ∈ List.range 8,RunsAt 10 (48+i):=by
  decide +kernel

theorem runs_r10_part7:∀ i ∈ List.range 8,RunsAt 10 (56+i):=by
  decide +kernel

theorem runs_r10_part8:∀ i ∈ List.range 8,RunsAt 10 (64+i):=by
  decide +kernel

theorem runs_r10_part9:∀ i ∈ List.range 8,RunsAt 10 (72+i):=by
  decide +kernel

theorem runs_r10_part10:∀ i ∈ List.range 8,RunsAt 10 (80+i):=by
  decide +kernel

theorem runs_r10_part11:∀ i ∈ List.range 8,RunsAt 10 (88+i):=by
  decide +kernel

theorem runs_r10_part12:∀ i ∈ List.range 8,RunsAt 10 (96+i):=by
  decide +kernel

theorem runs_r10_part13:∀ i ∈ List.range 8,RunsAt 10 (104+i):=by
  decide +kernel

theorem runs_r10_part14:∀ i ∈ List.range 8,RunsAt 10 (112+i):=by
  decide +kernel

theorem runs_r10_part15:∀ i ∈ List.range 8,RunsAt 10 (120+i):=by
  decide +kernel

theorem runs_r10_part16:∀ i ∈ List.range 5,RunsAt 10 (128+i):=by
  decide +kernel

theorem runs_r10:∀ V ∈ List.range 133,RunsAt 10 V:=by
  intro V hV
  have hv:V < 133:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r10_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r10_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r10_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r10_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r10_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r10_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r10_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r10_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r10_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r10_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r10_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r10_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r10_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r10_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r10_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r10_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=runs_r10_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r11_part0:∀ i ∈ List.range 8,RunsAt 11 (0+i):=by
  decide +kernel

theorem runs_r11_part1:∀ i ∈ List.range 8,RunsAt 11 (8+i):=by
  decide +kernel

theorem runs_r11_part2:∀ i ∈ List.range 8,RunsAt 11 (16+i):=by
  decide +kernel

theorem runs_r11_part3:∀ i ∈ List.range 8,RunsAt 11 (24+i):=by
  decide +kernel

theorem runs_r11_part4:∀ i ∈ List.range 8,RunsAt 11 (32+i):=by
  decide +kernel

theorem runs_r11_part5:∀ i ∈ List.range 8,RunsAt 11 (40+i):=by
  decide +kernel

theorem runs_r11_part6:∀ i ∈ List.range 8,RunsAt 11 (48+i):=by
  decide +kernel

theorem runs_r11_part7:∀ i ∈ List.range 8,RunsAt 11 (56+i):=by
  decide +kernel

theorem runs_r11_part8:∀ i ∈ List.range 8,RunsAt 11 (64+i):=by
  decide +kernel

theorem runs_r11_part9:∀ i ∈ List.range 8,RunsAt 11 (72+i):=by
  decide +kernel

theorem runs_r11_part10:∀ i ∈ List.range 8,RunsAt 11 (80+i):=by
  decide +kernel

theorem runs_r11_part11:∀ i ∈ List.range 8,RunsAt 11 (88+i):=by
  decide +kernel

theorem runs_r11_part12:∀ i ∈ List.range 8,RunsAt 11 (96+i):=by
  decide +kernel

theorem runs_r11_part13:∀ i ∈ List.range 8,RunsAt 11 (104+i):=by
  decide +kernel

theorem runs_r11_part14:∀ i ∈ List.range 8,RunsAt 11 (112+i):=by
  decide +kernel

theorem runs_r11_part15:∀ i ∈ List.range 8,RunsAt 11 (120+i):=by
  decide +kernel

theorem runs_r11_part16:∀ i ∈ List.range 4,RunsAt 11 (128+i):=by
  decide +kernel

theorem runs_r11:∀ V ∈ List.range 132,RunsAt 11 V:=by
  intro V hV
  have hv:V < 132:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r11_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r11_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r11_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r11_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r11_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r11_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r11_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r11_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r11_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r11_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r11_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r11_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r11_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r11_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r11_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r11_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=runs_r11_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r12_part0:∀ i ∈ List.range 8,RunsAt 12 (0+i):=by
  decide +kernel

theorem runs_r12_part1:∀ i ∈ List.range 8,RunsAt 12 (8+i):=by
  decide +kernel

theorem runs_r12_part2:∀ i ∈ List.range 8,RunsAt 12 (16+i):=by
  decide +kernel

theorem runs_r12_part3:∀ i ∈ List.range 8,RunsAt 12 (24+i):=by
  decide +kernel

theorem runs_r12_part4:∀ i ∈ List.range 8,RunsAt 12 (32+i):=by
  decide +kernel

theorem runs_r12_part5:∀ i ∈ List.range 8,RunsAt 12 (40+i):=by
  decide +kernel

theorem runs_r12_part6:∀ i ∈ List.range 8,RunsAt 12 (48+i):=by
  decide +kernel

theorem runs_r12_part7:∀ i ∈ List.range 8,RunsAt 12 (56+i):=by
  decide +kernel

theorem runs_r12_part8:∀ i ∈ List.range 8,RunsAt 12 (64+i):=by
  decide +kernel

theorem runs_r12_part9:∀ i ∈ List.range 8,RunsAt 12 (72+i):=by
  decide +kernel

theorem runs_r12_part10:∀ i ∈ List.range 8,RunsAt 12 (80+i):=by
  decide +kernel

theorem runs_r12_part11:∀ i ∈ List.range 8,RunsAt 12 (88+i):=by
  decide +kernel

theorem runs_r12_part12:∀ i ∈ List.range 8,RunsAt 12 (96+i):=by
  decide +kernel

theorem runs_r12_part13:∀ i ∈ List.range 8,RunsAt 12 (104+i):=by
  decide +kernel

theorem runs_r12_part14:∀ i ∈ List.range 8,RunsAt 12 (112+i):=by
  decide +kernel

theorem runs_r12_part15:∀ i ∈ List.range 8,RunsAt 12 (120+i):=by
  decide +kernel

theorem runs_r12_part16:∀ i ∈ List.range 3,RunsAt 12 (128+i):=by
  decide +kernel

theorem runs_r12:∀ V ∈ List.range 131,RunsAt 12 V:=by
  intro V hV
  have hv:V < 131:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r12_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r12_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r12_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r12_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r12_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r12_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r12_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r12_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r12_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r12_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r12_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r12_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r12_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r12_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r12_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r12_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=runs_r12_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r13_part0:∀ i ∈ List.range 8,RunsAt 13 (0+i):=by
  decide +kernel

theorem runs_r13_part1:∀ i ∈ List.range 8,RunsAt 13 (8+i):=by
  decide +kernel

theorem runs_r13_part2:∀ i ∈ List.range 8,RunsAt 13 (16+i):=by
  decide +kernel

theorem runs_r13_part3:∀ i ∈ List.range 8,RunsAt 13 (24+i):=by
  decide +kernel

theorem runs_r13_part4:∀ i ∈ List.range 8,RunsAt 13 (32+i):=by
  decide +kernel

theorem runs_r13_part5:∀ i ∈ List.range 8,RunsAt 13 (40+i):=by
  decide +kernel

theorem runs_r13_part6:∀ i ∈ List.range 8,RunsAt 13 (48+i):=by
  decide +kernel

theorem runs_r13_part7:∀ i ∈ List.range 8,RunsAt 13 (56+i):=by
  decide +kernel

theorem runs_r13_part8:∀ i ∈ List.range 8,RunsAt 13 (64+i):=by
  decide +kernel

theorem runs_r13_part9:∀ i ∈ List.range 8,RunsAt 13 (72+i):=by
  decide +kernel

theorem runs_r13_part10:∀ i ∈ List.range 8,RunsAt 13 (80+i):=by
  decide +kernel

theorem runs_r13_part11:∀ i ∈ List.range 8,RunsAt 13 (88+i):=by
  decide +kernel

theorem runs_r13_part12:∀ i ∈ List.range 8,RunsAt 13 (96+i):=by
  decide +kernel

theorem runs_r13_part13:∀ i ∈ List.range 8,RunsAt 13 (104+i):=by
  decide +kernel

theorem runs_r13_part14:∀ i ∈ List.range 8,RunsAt 13 (112+i):=by
  decide +kernel

theorem runs_r13_part15:∀ i ∈ List.range 8,RunsAt 13 (120+i):=by
  decide +kernel

theorem runs_r13_part16:∀ i ∈ List.range 2,RunsAt 13 (128+i):=by
  decide +kernel

theorem runs_r13:∀ V ∈ List.range 130,RunsAt 13 V:=by
  intro V hV
  have hv:V < 130:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r13_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r13_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r13_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r13_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r13_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r13_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r13_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r13_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r13_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r13_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r13_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r13_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r13_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r13_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r13_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r13_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=runs_r13_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r14_part0:∀ i ∈ List.range 8,RunsAt 14 (0+i):=by
  decide +kernel

theorem runs_r14_part1:∀ i ∈ List.range 8,RunsAt 14 (8+i):=by
  decide +kernel

theorem runs_r14_part2:∀ i ∈ List.range 8,RunsAt 14 (16+i):=by
  decide +kernel

theorem runs_r14_part3:∀ i ∈ List.range 8,RunsAt 14 (24+i):=by
  decide +kernel

theorem runs_r14_part4:∀ i ∈ List.range 8,RunsAt 14 (32+i):=by
  decide +kernel

theorem runs_r14_part5:∀ i ∈ List.range 8,RunsAt 14 (40+i):=by
  decide +kernel

theorem runs_r14_part6:∀ i ∈ List.range 8,RunsAt 14 (48+i):=by
  decide +kernel

theorem runs_r14_part7:∀ i ∈ List.range 8,RunsAt 14 (56+i):=by
  decide +kernel

theorem runs_r14_part8:∀ i ∈ List.range 8,RunsAt 14 (64+i):=by
  decide +kernel

theorem runs_r14_part9:∀ i ∈ List.range 8,RunsAt 14 (72+i):=by
  decide +kernel

theorem runs_r14_part10:∀ i ∈ List.range 8,RunsAt 14 (80+i):=by
  decide +kernel

theorem runs_r14_part11:∀ i ∈ List.range 8,RunsAt 14 (88+i):=by
  decide +kernel

theorem runs_r14_part12:∀ i ∈ List.range 8,RunsAt 14 (96+i):=by
  decide +kernel

theorem runs_r14_part13:∀ i ∈ List.range 8,RunsAt 14 (104+i):=by
  decide +kernel

theorem runs_r14_part14:∀ i ∈ List.range 8,RunsAt 14 (112+i):=by
  decide +kernel

theorem runs_r14_part15:∀ i ∈ List.range 8,RunsAt 14 (120+i):=by
  decide +kernel

theorem runs_r14_part16:∀ i ∈ List.range 1,RunsAt 14 (128+i):=by
  decide +kernel

theorem runs_r14:∀ V ∈ List.range 129,RunsAt 14 V:=by
  intro V hV
  have hv:V < 129:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r14_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r14_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r14_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r14_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r14_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r14_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r14_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r14_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r14_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r14_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r14_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r14_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r14_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r14_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r14_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=runs_r14_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=runs_r14_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem runs_r15_part0:∀ i ∈ List.range 8,RunsAt 15 (0+i):=by
  decide +kernel

theorem runs_r15_part1:∀ i ∈ List.range 8,RunsAt 15 (8+i):=by
  decide +kernel

theorem runs_r15_part2:∀ i ∈ List.range 8,RunsAt 15 (16+i):=by
  decide +kernel

theorem runs_r15_part3:∀ i ∈ List.range 8,RunsAt 15 (24+i):=by
  decide +kernel

theorem runs_r15_part4:∀ i ∈ List.range 8,RunsAt 15 (32+i):=by
  decide +kernel

theorem runs_r15_part5:∀ i ∈ List.range 8,RunsAt 15 (40+i):=by
  decide +kernel

theorem runs_r15_part6:∀ i ∈ List.range 8,RunsAt 15 (48+i):=by
  decide +kernel

theorem runs_r15_part7:∀ i ∈ List.range 8,RunsAt 15 (56+i):=by
  decide +kernel

theorem runs_r15_part8:∀ i ∈ List.range 8,RunsAt 15 (64+i):=by
  decide +kernel

theorem runs_r15_part9:∀ i ∈ List.range 8,RunsAt 15 (72+i):=by
  decide +kernel

theorem runs_r15_part10:∀ i ∈ List.range 8,RunsAt 15 (80+i):=by
  decide +kernel

theorem runs_r15_part11:∀ i ∈ List.range 8,RunsAt 15 (88+i):=by
  decide +kernel

theorem runs_r15_part12:∀ i ∈ List.range 8,RunsAt 15 (96+i):=by
  decide +kernel

theorem runs_r15_part13:∀ i ∈ List.range 8,RunsAt 15 (104+i):=by
  decide +kernel

theorem runs_r15_part14:∀ i ∈ List.range 8,RunsAt 15 (112+i):=by
  decide +kernel

theorem runs_r15_part15:∀ i ∈ List.range 8,RunsAt 15 (120+i):=by
  decide +kernel

theorem runs_r15:∀ V ∈ List.range 128,RunsAt 15 V:=by
  intro V hV
  have hv:V < 128:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r15_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r15_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r15_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r15_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r15_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r15_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r15_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r15_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r15_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r15_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r15_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r15_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r15_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r15_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r15_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=runs_r15_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r16_part0:∀ i ∈ List.range 8,RunsAt 16 (0+i):=by
  decide +kernel

theorem runs_r16_part1:∀ i ∈ List.range 8,RunsAt 16 (8+i):=by
  decide +kernel

theorem runs_r16_part2:∀ i ∈ List.range 8,RunsAt 16 (16+i):=by
  decide +kernel

theorem runs_r16_part3:∀ i ∈ List.range 8,RunsAt 16 (24+i):=by
  decide +kernel

theorem runs_r16_part4:∀ i ∈ List.range 8,RunsAt 16 (32+i):=by
  decide +kernel

theorem runs_r16_part5:∀ i ∈ List.range 8,RunsAt 16 (40+i):=by
  decide +kernel

theorem runs_r16_part6:∀ i ∈ List.range 8,RunsAt 16 (48+i):=by
  decide +kernel

theorem runs_r16_part7:∀ i ∈ List.range 8,RunsAt 16 (56+i):=by
  decide +kernel

theorem runs_r16_part8:∀ i ∈ List.range 8,RunsAt 16 (64+i):=by
  decide +kernel

theorem runs_r16_part9:∀ i ∈ List.range 8,RunsAt 16 (72+i):=by
  decide +kernel

theorem runs_r16_part10:∀ i ∈ List.range 8,RunsAt 16 (80+i):=by
  decide +kernel

theorem runs_r16_part11:∀ i ∈ List.range 8,RunsAt 16 (88+i):=by
  decide +kernel

theorem runs_r16_part12:∀ i ∈ List.range 8,RunsAt 16 (96+i):=by
  decide +kernel

theorem runs_r16_part13:∀ i ∈ List.range 8,RunsAt 16 (104+i):=by
  decide +kernel

theorem runs_r16_part14:∀ i ∈ List.range 8,RunsAt 16 (112+i):=by
  decide +kernel

theorem runs_r16_part15:∀ i ∈ List.range 7,RunsAt 16 (120+i):=by
  decide +kernel

theorem runs_r16:∀ V ∈ List.range 127,RunsAt 16 V:=by
  intro V hV
  have hv:V < 127:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r16_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r16_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r16_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r16_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r16_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r16_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r16_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r16_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r16_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r16_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r16_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r16_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r16_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r16_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r16_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=runs_r16_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r17_part0:∀ i ∈ List.range 8,RunsAt 17 (0+i):=by
  decide +kernel

theorem runs_r17_part1:∀ i ∈ List.range 8,RunsAt 17 (8+i):=by
  decide +kernel

theorem runs_r17_part2:∀ i ∈ List.range 8,RunsAt 17 (16+i):=by
  decide +kernel

theorem runs_r17_part3:∀ i ∈ List.range 8,RunsAt 17 (24+i):=by
  decide +kernel

theorem runs_r17_part4:∀ i ∈ List.range 8,RunsAt 17 (32+i):=by
  decide +kernel

theorem runs_r17_part5:∀ i ∈ List.range 8,RunsAt 17 (40+i):=by
  decide +kernel

theorem runs_r17_part6:∀ i ∈ List.range 8,RunsAt 17 (48+i):=by
  decide +kernel

theorem runs_r17_part7:∀ i ∈ List.range 8,RunsAt 17 (56+i):=by
  decide +kernel

theorem runs_r17_part8:∀ i ∈ List.range 8,RunsAt 17 (64+i):=by
  decide +kernel

theorem runs_r17_part9:∀ i ∈ List.range 8,RunsAt 17 (72+i):=by
  decide +kernel

theorem runs_r17_part10:∀ i ∈ List.range 8,RunsAt 17 (80+i):=by
  decide +kernel

theorem runs_r17_part11:∀ i ∈ List.range 8,RunsAt 17 (88+i):=by
  decide +kernel

theorem runs_r17_part12:∀ i ∈ List.range 8,RunsAt 17 (96+i):=by
  decide +kernel

theorem runs_r17_part13:∀ i ∈ List.range 8,RunsAt 17 (104+i):=by
  decide +kernel

theorem runs_r17_part14:∀ i ∈ List.range 8,RunsAt 17 (112+i):=by
  decide +kernel

theorem runs_r17_part15:∀ i ∈ List.range 6,RunsAt 17 (120+i):=by
  decide +kernel

theorem runs_r17:∀ V ∈ List.range 126,RunsAt 17 V:=by
  intro V hV
  have hv:V < 126:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r17_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r17_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r17_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r17_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r17_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r17_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r17_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r17_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r17_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r17_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r17_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r17_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r17_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r17_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r17_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=runs_r17_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r18_part0:∀ i ∈ List.range 8,RunsAt 18 (0+i):=by
  decide +kernel

theorem runs_r18_part1:∀ i ∈ List.range 8,RunsAt 18 (8+i):=by
  decide +kernel

theorem runs_r18_part2:∀ i ∈ List.range 8,RunsAt 18 (16+i):=by
  decide +kernel

theorem runs_r18_part3:∀ i ∈ List.range 8,RunsAt 18 (24+i):=by
  decide +kernel

theorem runs_r18_part4:∀ i ∈ List.range 8,RunsAt 18 (32+i):=by
  decide +kernel

theorem runs_r18_part5:∀ i ∈ List.range 8,RunsAt 18 (40+i):=by
  decide +kernel

theorem runs_r18_part6:∀ i ∈ List.range 8,RunsAt 18 (48+i):=by
  decide +kernel

theorem runs_r18_part7:∀ i ∈ List.range 8,RunsAt 18 (56+i):=by
  decide +kernel

theorem runs_r18_part8:∀ i ∈ List.range 8,RunsAt 18 (64+i):=by
  decide +kernel

theorem runs_r18_part9:∀ i ∈ List.range 8,RunsAt 18 (72+i):=by
  decide +kernel

theorem runs_r18_part10:∀ i ∈ List.range 8,RunsAt 18 (80+i):=by
  decide +kernel

theorem runs_r18_part11:∀ i ∈ List.range 8,RunsAt 18 (88+i):=by
  decide +kernel

theorem runs_r18_part12:∀ i ∈ List.range 8,RunsAt 18 (96+i):=by
  decide +kernel

theorem runs_r18_part13:∀ i ∈ List.range 8,RunsAt 18 (104+i):=by
  decide +kernel

theorem runs_r18_part14:∀ i ∈ List.range 8,RunsAt 18 (112+i):=by
  decide +kernel

theorem runs_r18_part15:∀ i ∈ List.range 5,RunsAt 18 (120+i):=by
  decide +kernel

theorem runs_r18:∀ V ∈ List.range 125,RunsAt 18 V:=by
  intro V hV
  have hv:V < 125:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r18_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r18_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r18_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r18_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r18_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r18_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r18_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r18_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r18_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r18_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r18_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r18_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r18_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r18_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r18_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=runs_r18_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r19_part0:∀ i ∈ List.range 8,RunsAt 19 (0+i):=by
  decide +kernel

theorem runs_r19_part1:∀ i ∈ List.range 8,RunsAt 19 (8+i):=by
  decide +kernel

theorem runs_r19_part2:∀ i ∈ List.range 8,RunsAt 19 (16+i):=by
  decide +kernel

theorem runs_r19_part3:∀ i ∈ List.range 8,RunsAt 19 (24+i):=by
  decide +kernel

theorem runs_r19_part4:∀ i ∈ List.range 8,RunsAt 19 (32+i):=by
  decide +kernel

theorem runs_r19_part5:∀ i ∈ List.range 8,RunsAt 19 (40+i):=by
  decide +kernel

theorem runs_r19_part6:∀ i ∈ List.range 8,RunsAt 19 (48+i):=by
  decide +kernel

theorem runs_r19_part7:∀ i ∈ List.range 8,RunsAt 19 (56+i):=by
  decide +kernel

theorem runs_r19_part8:∀ i ∈ List.range 8,RunsAt 19 (64+i):=by
  decide +kernel

theorem runs_r19_part9:∀ i ∈ List.range 8,RunsAt 19 (72+i):=by
  decide +kernel

theorem runs_r19_part10:∀ i ∈ List.range 8,RunsAt 19 (80+i):=by
  decide +kernel

theorem runs_r19_part11:∀ i ∈ List.range 8,RunsAt 19 (88+i):=by
  decide +kernel

theorem runs_r19_part12:∀ i ∈ List.range 8,RunsAt 19 (96+i):=by
  decide +kernel

theorem runs_r19_part13:∀ i ∈ List.range 8,RunsAt 19 (104+i):=by
  decide +kernel

theorem runs_r19_part14:∀ i ∈ List.range 8,RunsAt 19 (112+i):=by
  decide +kernel

theorem runs_r19_part15:∀ i ∈ List.range 4,RunsAt 19 (120+i):=by
  decide +kernel

theorem runs_r19:∀ V ∈ List.range 124,RunsAt 19 V:=by
  intro V hV
  have hv:V < 124:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r19_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r19_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r19_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r19_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r19_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r19_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r19_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r19_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r19_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r19_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r19_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r19_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r19_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r19_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r19_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=runs_r19_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r20_part0:∀ i ∈ List.range 8,RunsAt 20 (0+i):=by
  decide +kernel

theorem runs_r20_part1:∀ i ∈ List.range 8,RunsAt 20 (8+i):=by
  decide +kernel

theorem runs_r20_part2:∀ i ∈ List.range 8,RunsAt 20 (16+i):=by
  decide +kernel

theorem runs_r20_part3:∀ i ∈ List.range 8,RunsAt 20 (24+i):=by
  decide +kernel

theorem runs_r20_part4:∀ i ∈ List.range 8,RunsAt 20 (32+i):=by
  decide +kernel

theorem runs_r20_part5:∀ i ∈ List.range 8,RunsAt 20 (40+i):=by
  decide +kernel

theorem runs_r20_part6:∀ i ∈ List.range 8,RunsAt 20 (48+i):=by
  decide +kernel

theorem runs_r20_part7:∀ i ∈ List.range 8,RunsAt 20 (56+i):=by
  decide +kernel

theorem runs_r20_part8:∀ i ∈ List.range 8,RunsAt 20 (64+i):=by
  decide +kernel

theorem runs_r20_part9:∀ i ∈ List.range 8,RunsAt 20 (72+i):=by
  decide +kernel

theorem runs_r20_part10:∀ i ∈ List.range 8,RunsAt 20 (80+i):=by
  decide +kernel

theorem runs_r20_part11:∀ i ∈ List.range 8,RunsAt 20 (88+i):=by
  decide +kernel

theorem runs_r20_part12:∀ i ∈ List.range 8,RunsAt 20 (96+i):=by
  decide +kernel

theorem runs_r20_part13:∀ i ∈ List.range 8,RunsAt 20 (104+i):=by
  decide +kernel

theorem runs_r20_part14:∀ i ∈ List.range 8,RunsAt 20 (112+i):=by
  decide +kernel

theorem runs_r20_part15:∀ i ∈ List.range 3,RunsAt 20 (120+i):=by
  decide +kernel

theorem runs_r20:∀ V ∈ List.range 123,RunsAt 20 V:=by
  intro V hV
  have hv:V < 123:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r20_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r20_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r20_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r20_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r20_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r20_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r20_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r20_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r20_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r20_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r20_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r20_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r20_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r20_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r20_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=runs_r20_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r21_part0:∀ i ∈ List.range 8,RunsAt 21 (0+i):=by
  decide +kernel

theorem runs_r21_part1:∀ i ∈ List.range 8,RunsAt 21 (8+i):=by
  decide +kernel

theorem runs_r21_part2:∀ i ∈ List.range 8,RunsAt 21 (16+i):=by
  decide +kernel

theorem runs_r21_part3:∀ i ∈ List.range 8,RunsAt 21 (24+i):=by
  decide +kernel

theorem runs_r21_part4:∀ i ∈ List.range 8,RunsAt 21 (32+i):=by
  decide +kernel

theorem runs_r21_part5:∀ i ∈ List.range 8,RunsAt 21 (40+i):=by
  decide +kernel

theorem runs_r21_part6:∀ i ∈ List.range 8,RunsAt 21 (48+i):=by
  decide +kernel

theorem runs_r21_part7:∀ i ∈ List.range 8,RunsAt 21 (56+i):=by
  decide +kernel

theorem runs_r21_part8:∀ i ∈ List.range 8,RunsAt 21 (64+i):=by
  decide +kernel

theorem runs_r21_part9:∀ i ∈ List.range 8,RunsAt 21 (72+i):=by
  decide +kernel

theorem runs_r21_part10:∀ i ∈ List.range 8,RunsAt 21 (80+i):=by
  decide +kernel

theorem runs_r21_part11:∀ i ∈ List.range 8,RunsAt 21 (88+i):=by
  decide +kernel

theorem runs_r21_part12:∀ i ∈ List.range 8,RunsAt 21 (96+i):=by
  decide +kernel

theorem runs_r21_part13:∀ i ∈ List.range 8,RunsAt 21 (104+i):=by
  decide +kernel

theorem runs_r21_part14:∀ i ∈ List.range 8,RunsAt 21 (112+i):=by
  decide +kernel

theorem runs_r21_part15:∀ i ∈ List.range 2,RunsAt 21 (120+i):=by
  decide +kernel

theorem runs_r21:∀ V ∈ List.range 122,RunsAt 21 V:=by
  intro V hV
  have hv:V < 122:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r21_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r21_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r21_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r21_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r21_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r21_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r21_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r21_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r21_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r21_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r21_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r21_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r21_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r21_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r21_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=runs_r21_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r22_part0:∀ i ∈ List.range 8,RunsAt 22 (0+i):=by
  decide +kernel

theorem runs_r22_part1:∀ i ∈ List.range 8,RunsAt 22 (8+i):=by
  decide +kernel

theorem runs_r22_part2:∀ i ∈ List.range 8,RunsAt 22 (16+i):=by
  decide +kernel

theorem runs_r22_part3:∀ i ∈ List.range 8,RunsAt 22 (24+i):=by
  decide +kernel

theorem runs_r22_part4:∀ i ∈ List.range 8,RunsAt 22 (32+i):=by
  decide +kernel

theorem runs_r22_part5:∀ i ∈ List.range 8,RunsAt 22 (40+i):=by
  decide +kernel

theorem runs_r22_part6:∀ i ∈ List.range 8,RunsAt 22 (48+i):=by
  decide +kernel

theorem runs_r22_part7:∀ i ∈ List.range 8,RunsAt 22 (56+i):=by
  decide +kernel

theorem runs_r22_part8:∀ i ∈ List.range 8,RunsAt 22 (64+i):=by
  decide +kernel

theorem runs_r22_part9:∀ i ∈ List.range 8,RunsAt 22 (72+i):=by
  decide +kernel

theorem runs_r22_part10:∀ i ∈ List.range 8,RunsAt 22 (80+i):=by
  decide +kernel

theorem runs_r22_part11:∀ i ∈ List.range 8,RunsAt 22 (88+i):=by
  decide +kernel

theorem runs_r22_part12:∀ i ∈ List.range 8,RunsAt 22 (96+i):=by
  decide +kernel

theorem runs_r22_part13:∀ i ∈ List.range 8,RunsAt 22 (104+i):=by
  decide +kernel

theorem runs_r22_part14:∀ i ∈ List.range 8,RunsAt 22 (112+i):=by
  decide +kernel

theorem runs_r22_part15:∀ i ∈ List.range 1,RunsAt 22 (120+i):=by
  decide +kernel

theorem runs_r22:∀ V ∈ List.range 121,RunsAt 22 V:=by
  intro V hV
  have hv:V < 121:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r22_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r22_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r22_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r22_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r22_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r22_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r22_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r22_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r22_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r22_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r22_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r22_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r22_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r22_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=runs_r22_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=runs_r22_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem runs_r23_part0:∀ i ∈ List.range 8,RunsAt 23 (0+i):=by
  decide +kernel

theorem runs_r23_part1:∀ i ∈ List.range 8,RunsAt 23 (8+i):=by
  decide +kernel

theorem runs_r23_part2:∀ i ∈ List.range 8,RunsAt 23 (16+i):=by
  decide +kernel

theorem runs_r23_part3:∀ i ∈ List.range 8,RunsAt 23 (24+i):=by
  decide +kernel

theorem runs_r23_part4:∀ i ∈ List.range 8,RunsAt 23 (32+i):=by
  decide +kernel

theorem runs_r23_part5:∀ i ∈ List.range 8,RunsAt 23 (40+i):=by
  decide +kernel

theorem runs_r23_part6:∀ i ∈ List.range 8,RunsAt 23 (48+i):=by
  decide +kernel

theorem runs_r23_part7:∀ i ∈ List.range 8,RunsAt 23 (56+i):=by
  decide +kernel

theorem runs_r23_part8:∀ i ∈ List.range 8,RunsAt 23 (64+i):=by
  decide +kernel

theorem runs_r23_part9:∀ i ∈ List.range 8,RunsAt 23 (72+i):=by
  decide +kernel

theorem runs_r23_part10:∀ i ∈ List.range 8,RunsAt 23 (80+i):=by
  decide +kernel

theorem runs_r23_part11:∀ i ∈ List.range 8,RunsAt 23 (88+i):=by
  decide +kernel

theorem runs_r23_part12:∀ i ∈ List.range 8,RunsAt 23 (96+i):=by
  decide +kernel

theorem runs_r23_part13:∀ i ∈ List.range 8,RunsAt 23 (104+i):=by
  decide +kernel

theorem runs_r23_part14:∀ i ∈ List.range 8,RunsAt 23 (112+i):=by
  decide +kernel

theorem runs_r23:∀ V ∈ List.range 120,RunsAt 23 V:=by
  intro V hV
  have hv:V < 120:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r23_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r23_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r23_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r23_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r23_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r23_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r23_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r23_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r23_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r23_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r23_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r23_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r23_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r23_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=runs_r23_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r24_part0:∀ i ∈ List.range 8,RunsAt 24 (0+i):=by
  decide +kernel

theorem runs_r24_part1:∀ i ∈ List.range 8,RunsAt 24 (8+i):=by
  decide +kernel

theorem runs_r24_part2:∀ i ∈ List.range 8,RunsAt 24 (16+i):=by
  decide +kernel

theorem runs_r24_part3:∀ i ∈ List.range 8,RunsAt 24 (24+i):=by
  decide +kernel

theorem runs_r24_part4:∀ i ∈ List.range 8,RunsAt 24 (32+i):=by
  decide +kernel

theorem runs_r24_part5:∀ i ∈ List.range 8,RunsAt 24 (40+i):=by
  decide +kernel

theorem runs_r24_part6:∀ i ∈ List.range 8,RunsAt 24 (48+i):=by
  decide +kernel

theorem runs_r24_part7:∀ i ∈ List.range 8,RunsAt 24 (56+i):=by
  decide +kernel

theorem runs_r24_part8:∀ i ∈ List.range 8,RunsAt 24 (64+i):=by
  decide +kernel

theorem runs_r24_part9:∀ i ∈ List.range 8,RunsAt 24 (72+i):=by
  decide +kernel

theorem runs_r24_part10:∀ i ∈ List.range 8,RunsAt 24 (80+i):=by
  decide +kernel

theorem runs_r24_part11:∀ i ∈ List.range 8,RunsAt 24 (88+i):=by
  decide +kernel

theorem runs_r24_part12:∀ i ∈ List.range 8,RunsAt 24 (96+i):=by
  decide +kernel

theorem runs_r24_part13:∀ i ∈ List.range 8,RunsAt 24 (104+i):=by
  decide +kernel

theorem runs_r24_part14:∀ i ∈ List.range 7,RunsAt 24 (112+i):=by
  decide +kernel

theorem runs_r24:∀ V ∈ List.range 119,RunsAt 24 V:=by
  intro V hV
  have hv:V < 119:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r24_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r24_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r24_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r24_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r24_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r24_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r24_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r24_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r24_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r24_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r24_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r24_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r24_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r24_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=runs_r24_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r25_part0:∀ i ∈ List.range 8,RunsAt 25 (0+i):=by
  decide +kernel

theorem runs_r25_part1:∀ i ∈ List.range 8,RunsAt 25 (8+i):=by
  decide +kernel

theorem runs_r25_part2:∀ i ∈ List.range 8,RunsAt 25 (16+i):=by
  decide +kernel

theorem runs_r25_part3:∀ i ∈ List.range 8,RunsAt 25 (24+i):=by
  decide +kernel

theorem runs_r25_part4:∀ i ∈ List.range 8,RunsAt 25 (32+i):=by
  decide +kernel

theorem runs_r25_part5:∀ i ∈ List.range 8,RunsAt 25 (40+i):=by
  decide +kernel

theorem runs_r25_part6:∀ i ∈ List.range 8,RunsAt 25 (48+i):=by
  decide +kernel

theorem runs_r25_part7:∀ i ∈ List.range 8,RunsAt 25 (56+i):=by
  decide +kernel

theorem runs_r25_part8:∀ i ∈ List.range 8,RunsAt 25 (64+i):=by
  decide +kernel

theorem runs_r25_part9:∀ i ∈ List.range 8,RunsAt 25 (72+i):=by
  decide +kernel

theorem runs_r25_part10:∀ i ∈ List.range 8,RunsAt 25 (80+i):=by
  decide +kernel

theorem runs_r25_part11:∀ i ∈ List.range 8,RunsAt 25 (88+i):=by
  decide +kernel

theorem runs_r25_part12:∀ i ∈ List.range 8,RunsAt 25 (96+i):=by
  decide +kernel

theorem runs_r25_part13:∀ i ∈ List.range 8,RunsAt 25 (104+i):=by
  decide +kernel

theorem runs_r25_part14:∀ i ∈ List.range 6,RunsAt 25 (112+i):=by
  decide +kernel

theorem runs_r25:∀ V ∈ List.range 118,RunsAt 25 V:=by
  intro V hV
  have hv:V < 118:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r25_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r25_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r25_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r25_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r25_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r25_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r25_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r25_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r25_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r25_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r25_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r25_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r25_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r25_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=runs_r25_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r26_part0:∀ i ∈ List.range 8,RunsAt 26 (0+i):=by
  decide +kernel

theorem runs_r26_part1:∀ i ∈ List.range 8,RunsAt 26 (8+i):=by
  decide +kernel

theorem runs_r26_part2:∀ i ∈ List.range 8,RunsAt 26 (16+i):=by
  decide +kernel

theorem runs_r26_part3:∀ i ∈ List.range 8,RunsAt 26 (24+i):=by
  decide +kernel

theorem runs_r26_part4:∀ i ∈ List.range 8,RunsAt 26 (32+i):=by
  decide +kernel

theorem runs_r26_part5:∀ i ∈ List.range 8,RunsAt 26 (40+i):=by
  decide +kernel

theorem runs_r26_part6:∀ i ∈ List.range 8,RunsAt 26 (48+i):=by
  decide +kernel

theorem runs_r26_part7:∀ i ∈ List.range 8,RunsAt 26 (56+i):=by
  decide +kernel

theorem runs_r26_part8:∀ i ∈ List.range 8,RunsAt 26 (64+i):=by
  decide +kernel

theorem runs_r26_part9:∀ i ∈ List.range 8,RunsAt 26 (72+i):=by
  decide +kernel

theorem runs_r26_part10:∀ i ∈ List.range 8,RunsAt 26 (80+i):=by
  decide +kernel

theorem runs_r26_part11:∀ i ∈ List.range 8,RunsAt 26 (88+i):=by
  decide +kernel

theorem runs_r26_part12:∀ i ∈ List.range 8,RunsAt 26 (96+i):=by
  decide +kernel

theorem runs_r26_part13:∀ i ∈ List.range 8,RunsAt 26 (104+i):=by
  decide +kernel

theorem runs_r26_part14:∀ i ∈ List.range 5,RunsAt 26 (112+i):=by
  decide +kernel

theorem runs_r26:∀ V ∈ List.range 117,RunsAt 26 V:=by
  intro V hV
  have hv:V < 117:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r26_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r26_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r26_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r26_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r26_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r26_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r26_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r26_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r26_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r26_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r26_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r26_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r26_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r26_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=runs_r26_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r27_part0:∀ i ∈ List.range 8,RunsAt 27 (0+i):=by
  decide +kernel

theorem runs_r27_part1:∀ i ∈ List.range 8,RunsAt 27 (8+i):=by
  decide +kernel

theorem runs_r27_part2:∀ i ∈ List.range 8,RunsAt 27 (16+i):=by
  decide +kernel

theorem runs_r27_part3:∀ i ∈ List.range 8,RunsAt 27 (24+i):=by
  decide +kernel

theorem runs_r27_part4:∀ i ∈ List.range 8,RunsAt 27 (32+i):=by
  decide +kernel

theorem runs_r27_part5:∀ i ∈ List.range 8,RunsAt 27 (40+i):=by
  decide +kernel

theorem runs_r27_part6:∀ i ∈ List.range 8,RunsAt 27 (48+i):=by
  decide +kernel

theorem runs_r27_part7:∀ i ∈ List.range 8,RunsAt 27 (56+i):=by
  decide +kernel

theorem runs_r27_part8:∀ i ∈ List.range 8,RunsAt 27 (64+i):=by
  decide +kernel

theorem runs_r27_part9:∀ i ∈ List.range 8,RunsAt 27 (72+i):=by
  decide +kernel

theorem runs_r27_part10:∀ i ∈ List.range 8,RunsAt 27 (80+i):=by
  decide +kernel

theorem runs_r27_part11:∀ i ∈ List.range 8,RunsAt 27 (88+i):=by
  decide +kernel

theorem runs_r27_part12:∀ i ∈ List.range 8,RunsAt 27 (96+i):=by
  decide +kernel

theorem runs_r27_part13:∀ i ∈ List.range 8,RunsAt 27 (104+i):=by
  decide +kernel

theorem runs_r27_part14:∀ i ∈ List.range 4,RunsAt 27 (112+i):=by
  decide +kernel

theorem runs_r27:∀ V ∈ List.range 116,RunsAt 27 V:=by
  intro V hV
  have hv:V < 116:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r27_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r27_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r27_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r27_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r27_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r27_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r27_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r27_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r27_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r27_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r27_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r27_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r27_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r27_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=runs_r27_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r28_part0:∀ i ∈ List.range 8,RunsAt 28 (0+i):=by
  decide +kernel

theorem runs_r28_part1:∀ i ∈ List.range 8,RunsAt 28 (8+i):=by
  decide +kernel

theorem runs_r28_part2:∀ i ∈ List.range 8,RunsAt 28 (16+i):=by
  decide +kernel

theorem runs_r28_part3:∀ i ∈ List.range 8,RunsAt 28 (24+i):=by
  decide +kernel

theorem runs_r28_part4:∀ i ∈ List.range 8,RunsAt 28 (32+i):=by
  decide +kernel

theorem runs_r28_part5:∀ i ∈ List.range 8,RunsAt 28 (40+i):=by
  decide +kernel

theorem runs_r28_part6:∀ i ∈ List.range 8,RunsAt 28 (48+i):=by
  decide +kernel

theorem runs_r28_part7:∀ i ∈ List.range 8,RunsAt 28 (56+i):=by
  decide +kernel

theorem runs_r28_part8:∀ i ∈ List.range 8,RunsAt 28 (64+i):=by
  decide +kernel

theorem runs_r28_part9:∀ i ∈ List.range 8,RunsAt 28 (72+i):=by
  decide +kernel

theorem runs_r28_part10:∀ i ∈ List.range 8,RunsAt 28 (80+i):=by
  decide +kernel

theorem runs_r28_part11:∀ i ∈ List.range 8,RunsAt 28 (88+i):=by
  decide +kernel

theorem runs_r28_part12:∀ i ∈ List.range 8,RunsAt 28 (96+i):=by
  decide +kernel

theorem runs_r28_part13:∀ i ∈ List.range 8,RunsAt 28 (104+i):=by
  decide +kernel

theorem runs_r28_part14:∀ i ∈ List.range 3,RunsAt 28 (112+i):=by
  decide +kernel

theorem runs_r28:∀ V ∈ List.range 115,RunsAt 28 V:=by
  intro V hV
  have hv:V < 115:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r28_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r28_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r28_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r28_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r28_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r28_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r28_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r28_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r28_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r28_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r28_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r28_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r28_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r28_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=runs_r28_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r29_part0:∀ i ∈ List.range 8,RunsAt 29 (0+i):=by
  decide +kernel

theorem runs_r29_part1:∀ i ∈ List.range 8,RunsAt 29 (8+i):=by
  decide +kernel

theorem runs_r29_part2:∀ i ∈ List.range 8,RunsAt 29 (16+i):=by
  decide +kernel

theorem runs_r29_part3:∀ i ∈ List.range 8,RunsAt 29 (24+i):=by
  decide +kernel

theorem runs_r29_part4:∀ i ∈ List.range 8,RunsAt 29 (32+i):=by
  decide +kernel

theorem runs_r29_part5:∀ i ∈ List.range 8,RunsAt 29 (40+i):=by
  decide +kernel

theorem runs_r29_part6:∀ i ∈ List.range 8,RunsAt 29 (48+i):=by
  decide +kernel

theorem runs_r29_part7:∀ i ∈ List.range 8,RunsAt 29 (56+i):=by
  decide +kernel

theorem runs_r29_part8:∀ i ∈ List.range 8,RunsAt 29 (64+i):=by
  decide +kernel

theorem runs_r29_part9:∀ i ∈ List.range 8,RunsAt 29 (72+i):=by
  decide +kernel

theorem runs_r29_part10:∀ i ∈ List.range 8,RunsAt 29 (80+i):=by
  decide +kernel

theorem runs_r29_part11:∀ i ∈ List.range 8,RunsAt 29 (88+i):=by
  decide +kernel

theorem runs_r29_part12:∀ i ∈ List.range 8,RunsAt 29 (96+i):=by
  decide +kernel

theorem runs_r29_part13:∀ i ∈ List.range 8,RunsAt 29 (104+i):=by
  decide +kernel

theorem runs_r29_part14:∀ i ∈ List.range 2,RunsAt 29 (112+i):=by
  decide +kernel

theorem runs_r29:∀ V ∈ List.range 114,RunsAt 29 V:=by
  intro V hV
  have hv:V < 114:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r29_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r29_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r29_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r29_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r29_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r29_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r29_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r29_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r29_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r29_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r29_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r29_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r29_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r29_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=runs_r29_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem runs_r30_part0:∀ i ∈ List.range 8,RunsAt 30 (0+i):=by
  decide +kernel

theorem runs_r30_part1:∀ i ∈ List.range 8,RunsAt 30 (8+i):=by
  decide +kernel

theorem runs_r30_part2:∀ i ∈ List.range 8,RunsAt 30 (16+i):=by
  decide +kernel

theorem runs_r30_part3:∀ i ∈ List.range 8,RunsAt 30 (24+i):=by
  decide +kernel

theorem runs_r30_part4:∀ i ∈ List.range 8,RunsAt 30 (32+i):=by
  decide +kernel

theorem runs_r30_part5:∀ i ∈ List.range 8,RunsAt 30 (40+i):=by
  decide +kernel

theorem runs_r30_part6:∀ i ∈ List.range 8,RunsAt 30 (48+i):=by
  decide +kernel

theorem runs_r30_part7:∀ i ∈ List.range 8,RunsAt 30 (56+i):=by
  decide +kernel

theorem runs_r30_part8:∀ i ∈ List.range 8,RunsAt 30 (64+i):=by
  decide +kernel

theorem runs_r30_part9:∀ i ∈ List.range 8,RunsAt 30 (72+i):=by
  decide +kernel

theorem runs_r30_part10:∀ i ∈ List.range 8,RunsAt 30 (80+i):=by
  decide +kernel

theorem runs_r30_part11:∀ i ∈ List.range 8,RunsAt 30 (88+i):=by
  decide +kernel

theorem runs_r30_part12:∀ i ∈ List.range 8,RunsAt 30 (96+i):=by
  decide +kernel

theorem runs_r30_part13:∀ i ∈ List.range 8,RunsAt 30 (104+i):=by
  decide +kernel

theorem runs_r30_part14:∀ i ∈ List.range 1,RunsAt 30 (112+i):=by
  decide +kernel

theorem runs_r30:∀ V ∈ List.range 113,RunsAt 30 V:=by
  intro V hV
  have hv:V < 113:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r30_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r30_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r30_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r30_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r30_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r30_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r30_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r30_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r30_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r30_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r30_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r30_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r30_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=runs_r30_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=runs_r30_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r31_part0:∀ i ∈ List.range 8,RunsAt 31 (0+i):=by
  decide +kernel

theorem runs_r31_part1:∀ i ∈ List.range 8,RunsAt 31 (8+i):=by
  decide +kernel

theorem runs_r31_part2:∀ i ∈ List.range 8,RunsAt 31 (16+i):=by
  decide +kernel

theorem runs_r31_part3:∀ i ∈ List.range 8,RunsAt 31 (24+i):=by
  decide +kernel

theorem runs_r31_part4:∀ i ∈ List.range 8,RunsAt 31 (32+i):=by
  decide +kernel

theorem runs_r31_part5:∀ i ∈ List.range 8,RunsAt 31 (40+i):=by
  decide +kernel

theorem runs_r31_part6:∀ i ∈ List.range 8,RunsAt 31 (48+i):=by
  decide +kernel

theorem runs_r31_part7:∀ i ∈ List.range 8,RunsAt 31 (56+i):=by
  decide +kernel

theorem runs_r31_part8:∀ i ∈ List.range 8,RunsAt 31 (64+i):=by
  decide +kernel

theorem runs_r31_part9:∀ i ∈ List.range 8,RunsAt 31 (72+i):=by
  decide +kernel

theorem runs_r31_part10:∀ i ∈ List.range 8,RunsAt 31 (80+i):=by
  decide +kernel

theorem runs_r31_part11:∀ i ∈ List.range 8,RunsAt 31 (88+i):=by
  decide +kernel

theorem runs_r31_part12:∀ i ∈ List.range 8,RunsAt 31 (96+i):=by
  decide +kernel

theorem runs_r31_part13:∀ i ∈ List.range 8,RunsAt 31 (104+i):=by
  decide +kernel

theorem runs_r31:∀ V ∈ List.range 112,RunsAt 31 V:=by
  intro V hV
  have hv:V < 112:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r31_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r31_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r31_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r31_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r31_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r31_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r31_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r31_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r31_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r31_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r31_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r31_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r31_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            have hi:=runs_r31_part13 (V-104) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi

theorem runsReceipt:RunReceiptSound:=by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact runs_r1 V (List.mem_range.mpr (by omega))
    | exact runs_r2 V (List.mem_range.mpr (by omega))
    | exact runs_r3 V (List.mem_range.mpr (by omega))
    | exact runs_r4 V (List.mem_range.mpr (by omega))
    | exact runs_r5 V (List.mem_range.mpr (by omega))
    | exact runs_r6 V (List.mem_range.mpr (by omega))
    | exact runs_r7 V (List.mem_range.mpr (by omega))
    | exact runs_r8 V (List.mem_range.mpr (by omega))
    | exact runs_r9 V (List.mem_range.mpr (by omega))
    | exact runs_r10 V (List.mem_range.mpr (by omega))
    | exact runs_r11 V (List.mem_range.mpr (by omega))
    | exact runs_r12 V (List.mem_range.mpr (by omega))
    | exact runs_r13 V (List.mem_range.mpr (by omega))
    | exact runs_r14 V (List.mem_range.mpr (by omega))
    | exact runs_r15 V (List.mem_range.mpr (by omega))
    | exact runs_r16 V (List.mem_range.mpr (by omega))
    | exact runs_r17 V (List.mem_range.mpr (by omega))
    | exact runs_r18 V (List.mem_range.mpr (by omega))
    | exact runs_r19 V (List.mem_range.mpr (by omega))
    | exact runs_r20 V (List.mem_range.mpr (by omega))
    | exact runs_r21 V (List.mem_range.mpr (by omega))
    | exact runs_r22 V (List.mem_range.mpr (by omega))
    | exact runs_r23 V (List.mem_range.mpr (by omega))
    | exact runs_r24 V (List.mem_range.mpr (by omega))
    | exact runs_r25 V (List.mem_range.mpr (by omega))
    | exact runs_r26 V (List.mem_range.mpr (by omega))
    | exact runs_r27 V (List.mem_range.mpr (by omega))
    | exact runs_r28 V (List.mem_range.mpr (by omega))
    | exact runs_r29 V (List.mem_range.mpr (by omega))
    | exact runs_r30 V (List.mem_range.mpr (by omega))
    | exact runs_r31 V (List.mem_range.mpr (by omega))

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
