import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseChecks Lower80801.PhaseSemantics
open Lower80801.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem prefix_r1_part0:∀ i ∈ List.range 8,PrefixAt 1 (0+i):=by
  decide +kernel

theorem prefix_r1_part1:∀ i ∈ List.range 8,PrefixAt 1 (8+i):=by
  decide +kernel

theorem prefix_r1_part2:∀ i ∈ List.range 8,PrefixAt 1 (16+i):=by
  decide +kernel

theorem prefix_r1_part3:∀ i ∈ List.range 8,PrefixAt 1 (24+i):=by
  decide +kernel

theorem prefix_r1_part4:∀ i ∈ List.range 8,PrefixAt 1 (32+i):=by
  decide +kernel

theorem prefix_r1_part5:∀ i ∈ List.range 8,PrefixAt 1 (40+i):=by
  decide +kernel

theorem prefix_r1_part6:∀ i ∈ List.range 8,PrefixAt 1 (48+i):=by
  decide +kernel

theorem prefix_r1_part7:∀ i ∈ List.range 8,PrefixAt 1 (56+i):=by
  decide +kernel

theorem prefix_r1_part8:∀ i ∈ List.range 8,PrefixAt 1 (64+i):=by
  decide +kernel

theorem prefix_r1_part9:∀ i ∈ List.range 8,PrefixAt 1 (72+i):=by
  decide +kernel

theorem prefix_r1_part10:∀ i ∈ List.range 8,PrefixAt 1 (80+i):=by
  decide +kernel

theorem prefix_r1_part11:∀ i ∈ List.range 8,PrefixAt 1 (88+i):=by
  decide +kernel

theorem prefix_r1_part12:∀ i ∈ List.range 8,PrefixAt 1 (96+i):=by
  decide +kernel

theorem prefix_r1_part13:∀ i ∈ List.range 8,PrefixAt 1 (104+i):=by
  decide +kernel

theorem prefix_r1_part14:∀ i ∈ List.range 8,PrefixAt 1 (112+i):=by
  decide +kernel

theorem prefix_r1_part15:∀ i ∈ List.range 8,PrefixAt 1 (120+i):=by
  decide +kernel

theorem prefix_r1_part16:∀ i ∈ List.range 8,PrefixAt 1 (128+i):=by
  decide +kernel

theorem prefix_r1_part17:∀ i ∈ List.range 6,PrefixAt 1 (136+i):=by
  decide +kernel

theorem prefix_r1:∀ V ∈ List.range 142,PrefixAt 1 V:=by
  intro V hV
  have hv:V < 142:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r1_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r1_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r1_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r1_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r1_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r1_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r1_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r1_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r1_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r1_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r1_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r1_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r1_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r1_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r1_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r1_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=prefix_r1_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=prefix_r1_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem prefix_r2_part0:∀ i ∈ List.range 8,PrefixAt 2 (0+i):=by
  decide +kernel

theorem prefix_r2_part1:∀ i ∈ List.range 8,PrefixAt 2 (8+i):=by
  decide +kernel

theorem prefix_r2_part2:∀ i ∈ List.range 8,PrefixAt 2 (16+i):=by
  decide +kernel

theorem prefix_r2_part3:∀ i ∈ List.range 8,PrefixAt 2 (24+i):=by
  decide +kernel

theorem prefix_r2_part4:∀ i ∈ List.range 8,PrefixAt 2 (32+i):=by
  decide +kernel

theorem prefix_r2_part5:∀ i ∈ List.range 8,PrefixAt 2 (40+i):=by
  decide +kernel

theorem prefix_r2_part6:∀ i ∈ List.range 8,PrefixAt 2 (48+i):=by
  decide +kernel

theorem prefix_r2_part7:∀ i ∈ List.range 8,PrefixAt 2 (56+i):=by
  decide +kernel

theorem prefix_r2_part8:∀ i ∈ List.range 8,PrefixAt 2 (64+i):=by
  decide +kernel

theorem prefix_r2_part9:∀ i ∈ List.range 8,PrefixAt 2 (72+i):=by
  decide +kernel

theorem prefix_r2_part10:∀ i ∈ List.range 8,PrefixAt 2 (80+i):=by
  decide +kernel

theorem prefix_r2_part11:∀ i ∈ List.range 8,PrefixAt 2 (88+i):=by
  decide +kernel

theorem prefix_r2_part12:∀ i ∈ List.range 8,PrefixAt 2 (96+i):=by
  decide +kernel

theorem prefix_r2_part13:∀ i ∈ List.range 8,PrefixAt 2 (104+i):=by
  decide +kernel

theorem prefix_r2_part14:∀ i ∈ List.range 8,PrefixAt 2 (112+i):=by
  decide +kernel

theorem prefix_r2_part15:∀ i ∈ List.range 8,PrefixAt 2 (120+i):=by
  decide +kernel

theorem prefix_r2_part16:∀ i ∈ List.range 8,PrefixAt 2 (128+i):=by
  decide +kernel

theorem prefix_r2_part17:∀ i ∈ List.range 5,PrefixAt 2 (136+i):=by
  decide +kernel

theorem prefix_r2:∀ V ∈ List.range 141,PrefixAt 2 V:=by
  intro V hV
  have hv:V < 141:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r2_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r2_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r2_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r2_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r2_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r2_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r2_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r2_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r2_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r2_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r2_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r2_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r2_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r2_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r2_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r2_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=prefix_r2_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=prefix_r2_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem prefix_r3_part0:∀ i ∈ List.range 8,PrefixAt 3 (0+i):=by
  decide +kernel

theorem prefix_r3_part1:∀ i ∈ List.range 8,PrefixAt 3 (8+i):=by
  decide +kernel

theorem prefix_r3_part2:∀ i ∈ List.range 8,PrefixAt 3 (16+i):=by
  decide +kernel

theorem prefix_r3_part3:∀ i ∈ List.range 8,PrefixAt 3 (24+i):=by
  decide +kernel

theorem prefix_r3_part4:∀ i ∈ List.range 8,PrefixAt 3 (32+i):=by
  decide +kernel

theorem prefix_r3_part5:∀ i ∈ List.range 8,PrefixAt 3 (40+i):=by
  decide +kernel

theorem prefix_r3_part6:∀ i ∈ List.range 8,PrefixAt 3 (48+i):=by
  decide +kernel

theorem prefix_r3_part7:∀ i ∈ List.range 8,PrefixAt 3 (56+i):=by
  decide +kernel

theorem prefix_r3_part8:∀ i ∈ List.range 8,PrefixAt 3 (64+i):=by
  decide +kernel

theorem prefix_r3_part9:∀ i ∈ List.range 8,PrefixAt 3 (72+i):=by
  decide +kernel

theorem prefix_r3_part10:∀ i ∈ List.range 8,PrefixAt 3 (80+i):=by
  decide +kernel

theorem prefix_r3_part11:∀ i ∈ List.range 8,PrefixAt 3 (88+i):=by
  decide +kernel

theorem prefix_r3_part12:∀ i ∈ List.range 8,PrefixAt 3 (96+i):=by
  decide +kernel

theorem prefix_r3_part13:∀ i ∈ List.range 8,PrefixAt 3 (104+i):=by
  decide +kernel

theorem prefix_r3_part14:∀ i ∈ List.range 8,PrefixAt 3 (112+i):=by
  decide +kernel

theorem prefix_r3_part15:∀ i ∈ List.range 8,PrefixAt 3 (120+i):=by
  decide +kernel

theorem prefix_r3_part16:∀ i ∈ List.range 8,PrefixAt 3 (128+i):=by
  decide +kernel

theorem prefix_r3_part17:∀ i ∈ List.range 4,PrefixAt 3 (136+i):=by
  decide +kernel

theorem prefix_r3:∀ V ∈ List.range 140,PrefixAt 3 V:=by
  intro V hV
  have hv:V < 140:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r3_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r3_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r3_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r3_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r3_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r3_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r3_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r3_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r3_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r3_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r3_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r3_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r3_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r3_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r3_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r3_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=prefix_r3_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=prefix_r3_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem prefix_r4_part0:∀ i ∈ List.range 8,PrefixAt 4 (0+i):=by
  decide +kernel

theorem prefix_r4_part1:∀ i ∈ List.range 8,PrefixAt 4 (8+i):=by
  decide +kernel

theorem prefix_r4_part2:∀ i ∈ List.range 8,PrefixAt 4 (16+i):=by
  decide +kernel

theorem prefix_r4_part3:∀ i ∈ List.range 8,PrefixAt 4 (24+i):=by
  decide +kernel

theorem prefix_r4_part4:∀ i ∈ List.range 8,PrefixAt 4 (32+i):=by
  decide +kernel

theorem prefix_r4_part5:∀ i ∈ List.range 8,PrefixAt 4 (40+i):=by
  decide +kernel

theorem prefix_r4_part6:∀ i ∈ List.range 8,PrefixAt 4 (48+i):=by
  decide +kernel

theorem prefix_r4_part7:∀ i ∈ List.range 8,PrefixAt 4 (56+i):=by
  decide +kernel

theorem prefix_r4_part8:∀ i ∈ List.range 8,PrefixAt 4 (64+i):=by
  decide +kernel

theorem prefix_r4_part9:∀ i ∈ List.range 8,PrefixAt 4 (72+i):=by
  decide +kernel

theorem prefix_r4_part10:∀ i ∈ List.range 8,PrefixAt 4 (80+i):=by
  decide +kernel

theorem prefix_r4_part11:∀ i ∈ List.range 8,PrefixAt 4 (88+i):=by
  decide +kernel

theorem prefix_r4_part12:∀ i ∈ List.range 8,PrefixAt 4 (96+i):=by
  decide +kernel

theorem prefix_r4_part13:∀ i ∈ List.range 8,PrefixAt 4 (104+i):=by
  decide +kernel

theorem prefix_r4_part14:∀ i ∈ List.range 8,PrefixAt 4 (112+i):=by
  decide +kernel

theorem prefix_r4_part15:∀ i ∈ List.range 8,PrefixAt 4 (120+i):=by
  decide +kernel

theorem prefix_r4_part16:∀ i ∈ List.range 8,PrefixAt 4 (128+i):=by
  decide +kernel

theorem prefix_r4_part17:∀ i ∈ List.range 3,PrefixAt 4 (136+i):=by
  decide +kernel

theorem prefix_r4:∀ V ∈ List.range 139,PrefixAt 4 V:=by
  intro V hV
  have hv:V < 139:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r4_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r4_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r4_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r4_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r4_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r4_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r4_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r4_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r4_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r4_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r4_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r4_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r4_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r4_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r4_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r4_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=prefix_r4_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=prefix_r4_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem prefix_r5_part0:∀ i ∈ List.range 8,PrefixAt 5 (0+i):=by
  decide +kernel

theorem prefix_r5_part1:∀ i ∈ List.range 8,PrefixAt 5 (8+i):=by
  decide +kernel

theorem prefix_r5_part2:∀ i ∈ List.range 8,PrefixAt 5 (16+i):=by
  decide +kernel

theorem prefix_r5_part3:∀ i ∈ List.range 8,PrefixAt 5 (24+i):=by
  decide +kernel

theorem prefix_r5_part4:∀ i ∈ List.range 8,PrefixAt 5 (32+i):=by
  decide +kernel

theorem prefix_r5_part5:∀ i ∈ List.range 8,PrefixAt 5 (40+i):=by
  decide +kernel

theorem prefix_r5_part6:∀ i ∈ List.range 8,PrefixAt 5 (48+i):=by
  decide +kernel

theorem prefix_r5_part7:∀ i ∈ List.range 8,PrefixAt 5 (56+i):=by
  decide +kernel

theorem prefix_r5_part8:∀ i ∈ List.range 8,PrefixAt 5 (64+i):=by
  decide +kernel

theorem prefix_r5_part9:∀ i ∈ List.range 8,PrefixAt 5 (72+i):=by
  decide +kernel

theorem prefix_r5_part10:∀ i ∈ List.range 8,PrefixAt 5 (80+i):=by
  decide +kernel

theorem prefix_r5_part11:∀ i ∈ List.range 8,PrefixAt 5 (88+i):=by
  decide +kernel

theorem prefix_r5_part12:∀ i ∈ List.range 8,PrefixAt 5 (96+i):=by
  decide +kernel

theorem prefix_r5_part13:∀ i ∈ List.range 8,PrefixAt 5 (104+i):=by
  decide +kernel

theorem prefix_r5_part14:∀ i ∈ List.range 8,PrefixAt 5 (112+i):=by
  decide +kernel

theorem prefix_r5_part15:∀ i ∈ List.range 8,PrefixAt 5 (120+i):=by
  decide +kernel

theorem prefix_r5_part16:∀ i ∈ List.range 8,PrefixAt 5 (128+i):=by
  decide +kernel

theorem prefix_r5_part17:∀ i ∈ List.range 2,PrefixAt 5 (136+i):=by
  decide +kernel

theorem prefix_r5:∀ V ∈ List.range 138,PrefixAt 5 V:=by
  intro V hV
  have hv:V < 138:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r5_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r5_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r5_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r5_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r5_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r5_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r5_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r5_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r5_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r5_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r5_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r5_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r5_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r5_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r5_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r5_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=prefix_r5_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=prefix_r5_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem prefix_r6_part0:∀ i ∈ List.range 8,PrefixAt 6 (0+i):=by
  decide +kernel

theorem prefix_r6_part1:∀ i ∈ List.range 8,PrefixAt 6 (8+i):=by
  decide +kernel

theorem prefix_r6_part2:∀ i ∈ List.range 8,PrefixAt 6 (16+i):=by
  decide +kernel

theorem prefix_r6_part3:∀ i ∈ List.range 8,PrefixAt 6 (24+i):=by
  decide +kernel

theorem prefix_r6_part4:∀ i ∈ List.range 8,PrefixAt 6 (32+i):=by
  decide +kernel

theorem prefix_r6_part5:∀ i ∈ List.range 8,PrefixAt 6 (40+i):=by
  decide +kernel

theorem prefix_r6_part6:∀ i ∈ List.range 8,PrefixAt 6 (48+i):=by
  decide +kernel

theorem prefix_r6_part7:∀ i ∈ List.range 8,PrefixAt 6 (56+i):=by
  decide +kernel

theorem prefix_r6_part8:∀ i ∈ List.range 8,PrefixAt 6 (64+i):=by
  decide +kernel

theorem prefix_r6_part9:∀ i ∈ List.range 8,PrefixAt 6 (72+i):=by
  decide +kernel

theorem prefix_r6_part10:∀ i ∈ List.range 8,PrefixAt 6 (80+i):=by
  decide +kernel

theorem prefix_r6_part11:∀ i ∈ List.range 8,PrefixAt 6 (88+i):=by
  decide +kernel

theorem prefix_r6_part12:∀ i ∈ List.range 8,PrefixAt 6 (96+i):=by
  decide +kernel

theorem prefix_r6_part13:∀ i ∈ List.range 8,PrefixAt 6 (104+i):=by
  decide +kernel

theorem prefix_r6_part14:∀ i ∈ List.range 8,PrefixAt 6 (112+i):=by
  decide +kernel

theorem prefix_r6_part15:∀ i ∈ List.range 8,PrefixAt 6 (120+i):=by
  decide +kernel

theorem prefix_r6_part16:∀ i ∈ List.range 8,PrefixAt 6 (128+i):=by
  decide +kernel

theorem prefix_r6_part17:∀ i ∈ List.range 1,PrefixAt 6 (136+i):=by
  decide +kernel

theorem prefix_r6:∀ V ∈ List.range 137,PrefixAt 6 V:=by
  intro V hV
  have hv:V < 137:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r6_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r6_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r6_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r6_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r6_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r6_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r6_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r6_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r6_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r6_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r6_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r6_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r6_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r6_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r6_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r6_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  by_cases h16:V < 136
                                  · have hi:=prefix_r6_part16 (V-128) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                                  ·
                                    have hi:=prefix_r6_part17 (V-136) (List.mem_range.mpr (by omega))
                                    simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem prefix_r7_part0:∀ i ∈ List.range 8,PrefixAt 7 (0+i):=by
  decide +kernel

theorem prefix_r7_part1:∀ i ∈ List.range 8,PrefixAt 7 (8+i):=by
  decide +kernel

theorem prefix_r7_part2:∀ i ∈ List.range 8,PrefixAt 7 (16+i):=by
  decide +kernel

theorem prefix_r7_part3:∀ i ∈ List.range 8,PrefixAt 7 (24+i):=by
  decide +kernel

theorem prefix_r7_part4:∀ i ∈ List.range 8,PrefixAt 7 (32+i):=by
  decide +kernel

theorem prefix_r7_part5:∀ i ∈ List.range 8,PrefixAt 7 (40+i):=by
  decide +kernel

theorem prefix_r7_part6:∀ i ∈ List.range 8,PrefixAt 7 (48+i):=by
  decide +kernel

theorem prefix_r7_part7:∀ i ∈ List.range 8,PrefixAt 7 (56+i):=by
  decide +kernel

theorem prefix_r7_part8:∀ i ∈ List.range 8,PrefixAt 7 (64+i):=by
  decide +kernel

theorem prefix_r7_part9:∀ i ∈ List.range 8,PrefixAt 7 (72+i):=by
  decide +kernel

theorem prefix_r7_part10:∀ i ∈ List.range 8,PrefixAt 7 (80+i):=by
  decide +kernel

theorem prefix_r7_part11:∀ i ∈ List.range 8,PrefixAt 7 (88+i):=by
  decide +kernel

theorem prefix_r7_part12:∀ i ∈ List.range 8,PrefixAt 7 (96+i):=by
  decide +kernel

theorem prefix_r7_part13:∀ i ∈ List.range 8,PrefixAt 7 (104+i):=by
  decide +kernel

theorem prefix_r7_part14:∀ i ∈ List.range 8,PrefixAt 7 (112+i):=by
  decide +kernel

theorem prefix_r7_part15:∀ i ∈ List.range 8,PrefixAt 7 (120+i):=by
  decide +kernel

theorem prefix_r7_part16:∀ i ∈ List.range 8,PrefixAt 7 (128+i):=by
  decide +kernel

theorem prefix_r7:∀ V ∈ List.range 136,PrefixAt 7 V:=by
  intro V hV
  have hv:V < 136:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r7_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r7_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r7_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r7_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r7_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r7_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r7_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r7_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r7_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r7_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r7_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r7_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r7_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r7_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r7_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r7_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=prefix_r7_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem prefix_r8_part0:∀ i ∈ List.range 8,PrefixAt 8 (0+i):=by
  decide +kernel

theorem prefix_r8_part1:∀ i ∈ List.range 8,PrefixAt 8 (8+i):=by
  decide +kernel

theorem prefix_r8_part2:∀ i ∈ List.range 8,PrefixAt 8 (16+i):=by
  decide +kernel

theorem prefix_r8_part3:∀ i ∈ List.range 8,PrefixAt 8 (24+i):=by
  decide +kernel

theorem prefix_r8_part4:∀ i ∈ List.range 8,PrefixAt 8 (32+i):=by
  decide +kernel

theorem prefix_r8_part5:∀ i ∈ List.range 8,PrefixAt 8 (40+i):=by
  decide +kernel

theorem prefix_r8_part6:∀ i ∈ List.range 8,PrefixAt 8 (48+i):=by
  decide +kernel

theorem prefix_r8_part7:∀ i ∈ List.range 8,PrefixAt 8 (56+i):=by
  decide +kernel

theorem prefix_r8_part8:∀ i ∈ List.range 8,PrefixAt 8 (64+i):=by
  decide +kernel

theorem prefix_r8_part9:∀ i ∈ List.range 8,PrefixAt 8 (72+i):=by
  decide +kernel

theorem prefix_r8_part10:∀ i ∈ List.range 8,PrefixAt 8 (80+i):=by
  decide +kernel

theorem prefix_r8_part11:∀ i ∈ List.range 8,PrefixAt 8 (88+i):=by
  decide +kernel

theorem prefix_r8_part12:∀ i ∈ List.range 8,PrefixAt 8 (96+i):=by
  decide +kernel

theorem prefix_r8_part13:∀ i ∈ List.range 8,PrefixAt 8 (104+i):=by
  decide +kernel

theorem prefix_r8_part14:∀ i ∈ List.range 8,PrefixAt 8 (112+i):=by
  decide +kernel

theorem prefix_r8_part15:∀ i ∈ List.range 8,PrefixAt 8 (120+i):=by
  decide +kernel

theorem prefix_r8_part16:∀ i ∈ List.range 7,PrefixAt 8 (128+i):=by
  decide +kernel

theorem prefix_r8:∀ V ∈ List.range 135,PrefixAt 8 V:=by
  intro V hV
  have hv:V < 135:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r8_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r8_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r8_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r8_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r8_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r8_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r8_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r8_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r8_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r8_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r8_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r8_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r8_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r8_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r8_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r8_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=prefix_r8_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem prefix_r9_part0:∀ i ∈ List.range 8,PrefixAt 9 (0+i):=by
  decide +kernel

theorem prefix_r9_part1:∀ i ∈ List.range 8,PrefixAt 9 (8+i):=by
  decide +kernel

theorem prefix_r9_part2:∀ i ∈ List.range 8,PrefixAt 9 (16+i):=by
  decide +kernel

theorem prefix_r9_part3:∀ i ∈ List.range 8,PrefixAt 9 (24+i):=by
  decide +kernel

theorem prefix_r9_part4:∀ i ∈ List.range 8,PrefixAt 9 (32+i):=by
  decide +kernel

theorem prefix_r9_part5:∀ i ∈ List.range 8,PrefixAt 9 (40+i):=by
  decide +kernel

theorem prefix_r9_part6:∀ i ∈ List.range 8,PrefixAt 9 (48+i):=by
  decide +kernel

theorem prefix_r9_part7:∀ i ∈ List.range 8,PrefixAt 9 (56+i):=by
  decide +kernel

theorem prefix_r9_part8:∀ i ∈ List.range 8,PrefixAt 9 (64+i):=by
  decide +kernel

theorem prefix_r9_part9:∀ i ∈ List.range 8,PrefixAt 9 (72+i):=by
  decide +kernel

theorem prefix_r9_part10:∀ i ∈ List.range 8,PrefixAt 9 (80+i):=by
  decide +kernel

theorem prefix_r9_part11:∀ i ∈ List.range 8,PrefixAt 9 (88+i):=by
  decide +kernel

theorem prefix_r9_part12:∀ i ∈ List.range 8,PrefixAt 9 (96+i):=by
  decide +kernel

theorem prefix_r9_part13:∀ i ∈ List.range 8,PrefixAt 9 (104+i):=by
  decide +kernel

theorem prefix_r9_part14:∀ i ∈ List.range 8,PrefixAt 9 (112+i):=by
  decide +kernel

theorem prefix_r9_part15:∀ i ∈ List.range 8,PrefixAt 9 (120+i):=by
  decide +kernel

theorem prefix_r9_part16:∀ i ∈ List.range 6,PrefixAt 9 (128+i):=by
  decide +kernel

theorem prefix_r9:∀ V ∈ List.range 134,PrefixAt 9 V:=by
  intro V hV
  have hv:V < 134:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r9_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r9_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r9_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r9_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r9_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r9_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r9_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r9_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r9_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r9_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r9_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r9_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r9_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r9_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r9_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r9_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=prefix_r9_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem prefix_r10_part0:∀ i ∈ List.range 8,PrefixAt 10 (0+i):=by
  decide +kernel

theorem prefix_r10_part1:∀ i ∈ List.range 8,PrefixAt 10 (8+i):=by
  decide +kernel

theorem prefix_r10_part2:∀ i ∈ List.range 8,PrefixAt 10 (16+i):=by
  decide +kernel

theorem prefix_r10_part3:∀ i ∈ List.range 8,PrefixAt 10 (24+i):=by
  decide +kernel

theorem prefix_r10_part4:∀ i ∈ List.range 8,PrefixAt 10 (32+i):=by
  decide +kernel

theorem prefix_r10_part5:∀ i ∈ List.range 8,PrefixAt 10 (40+i):=by
  decide +kernel

theorem prefix_r10_part6:∀ i ∈ List.range 8,PrefixAt 10 (48+i):=by
  decide +kernel

theorem prefix_r10_part7:∀ i ∈ List.range 8,PrefixAt 10 (56+i):=by
  decide +kernel

theorem prefix_r10_part8:∀ i ∈ List.range 8,PrefixAt 10 (64+i):=by
  decide +kernel

theorem prefix_r10_part9:∀ i ∈ List.range 8,PrefixAt 10 (72+i):=by
  decide +kernel

theorem prefix_r10_part10:∀ i ∈ List.range 8,PrefixAt 10 (80+i):=by
  decide +kernel

theorem prefix_r10_part11:∀ i ∈ List.range 8,PrefixAt 10 (88+i):=by
  decide +kernel

theorem prefix_r10_part12:∀ i ∈ List.range 8,PrefixAt 10 (96+i):=by
  decide +kernel

theorem prefix_r10_part13:∀ i ∈ List.range 8,PrefixAt 10 (104+i):=by
  decide +kernel

theorem prefix_r10_part14:∀ i ∈ List.range 8,PrefixAt 10 (112+i):=by
  decide +kernel

theorem prefix_r10_part15:∀ i ∈ List.range 8,PrefixAt 10 (120+i):=by
  decide +kernel

theorem prefix_r10_part16:∀ i ∈ List.range 5,PrefixAt 10 (128+i):=by
  decide +kernel

theorem prefix_r10:∀ V ∈ List.range 133,PrefixAt 10 V:=by
  intro V hV
  have hv:V < 133:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r10_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r10_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r10_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r10_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r10_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r10_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r10_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r10_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r10_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r10_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r10_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r10_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r10_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r10_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r10_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r10_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=prefix_r10_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem prefix_r11_part0:∀ i ∈ List.range 8,PrefixAt 11 (0+i):=by
  decide +kernel

theorem prefix_r11_part1:∀ i ∈ List.range 8,PrefixAt 11 (8+i):=by
  decide +kernel

theorem prefix_r11_part2:∀ i ∈ List.range 8,PrefixAt 11 (16+i):=by
  decide +kernel

theorem prefix_r11_part3:∀ i ∈ List.range 8,PrefixAt 11 (24+i):=by
  decide +kernel

theorem prefix_r11_part4:∀ i ∈ List.range 8,PrefixAt 11 (32+i):=by
  decide +kernel

theorem prefix_r11_part5:∀ i ∈ List.range 8,PrefixAt 11 (40+i):=by
  decide +kernel

theorem prefix_r11_part6:∀ i ∈ List.range 8,PrefixAt 11 (48+i):=by
  decide +kernel

theorem prefix_r11_part7:∀ i ∈ List.range 8,PrefixAt 11 (56+i):=by
  decide +kernel

theorem prefix_r11_part8:∀ i ∈ List.range 8,PrefixAt 11 (64+i):=by
  decide +kernel

theorem prefix_r11_part9:∀ i ∈ List.range 8,PrefixAt 11 (72+i):=by
  decide +kernel

theorem prefix_r11_part10:∀ i ∈ List.range 8,PrefixAt 11 (80+i):=by
  decide +kernel

theorem prefix_r11_part11:∀ i ∈ List.range 8,PrefixAt 11 (88+i):=by
  decide +kernel

theorem prefix_r11_part12:∀ i ∈ List.range 8,PrefixAt 11 (96+i):=by
  decide +kernel

theorem prefix_r11_part13:∀ i ∈ List.range 8,PrefixAt 11 (104+i):=by
  decide +kernel

theorem prefix_r11_part14:∀ i ∈ List.range 8,PrefixAt 11 (112+i):=by
  decide +kernel

theorem prefix_r11_part15:∀ i ∈ List.range 8,PrefixAt 11 (120+i):=by
  decide +kernel

theorem prefix_r11_part16:∀ i ∈ List.range 4,PrefixAt 11 (128+i):=by
  decide +kernel

theorem prefix_r11:∀ V ∈ List.range 132,PrefixAt 11 V:=by
  intro V hV
  have hv:V < 132:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r11_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r11_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r11_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r11_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r11_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r11_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r11_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r11_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r11_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r11_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r11_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r11_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r11_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r11_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r11_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r11_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=prefix_r11_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem prefix_r12_part0:∀ i ∈ List.range 8,PrefixAt 12 (0+i):=by
  decide +kernel

theorem prefix_r12_part1:∀ i ∈ List.range 8,PrefixAt 12 (8+i):=by
  decide +kernel

theorem prefix_r12_part2:∀ i ∈ List.range 8,PrefixAt 12 (16+i):=by
  decide +kernel

theorem prefix_r12_part3:∀ i ∈ List.range 8,PrefixAt 12 (24+i):=by
  decide +kernel

theorem prefix_r12_part4:∀ i ∈ List.range 8,PrefixAt 12 (32+i):=by
  decide +kernel

theorem prefix_r12_part5:∀ i ∈ List.range 8,PrefixAt 12 (40+i):=by
  decide +kernel

theorem prefix_r12_part6:∀ i ∈ List.range 8,PrefixAt 12 (48+i):=by
  decide +kernel

theorem prefix_r12_part7:∀ i ∈ List.range 8,PrefixAt 12 (56+i):=by
  decide +kernel

theorem prefix_r12_part8:∀ i ∈ List.range 8,PrefixAt 12 (64+i):=by
  decide +kernel

theorem prefix_r12_part9:∀ i ∈ List.range 8,PrefixAt 12 (72+i):=by
  decide +kernel

theorem prefix_r12_part10:∀ i ∈ List.range 8,PrefixAt 12 (80+i):=by
  decide +kernel

theorem prefix_r12_part11:∀ i ∈ List.range 8,PrefixAt 12 (88+i):=by
  decide +kernel

theorem prefix_r12_part12:∀ i ∈ List.range 8,PrefixAt 12 (96+i):=by
  decide +kernel

theorem prefix_r12_part13:∀ i ∈ List.range 8,PrefixAt 12 (104+i):=by
  decide +kernel

theorem prefix_r12_part14:∀ i ∈ List.range 8,PrefixAt 12 (112+i):=by
  decide +kernel

theorem prefix_r12_part15:∀ i ∈ List.range 8,PrefixAt 12 (120+i):=by
  decide +kernel

theorem prefix_r12_part16:∀ i ∈ List.range 3,PrefixAt 12 (128+i):=by
  decide +kernel

theorem prefix_r12:∀ V ∈ List.range 131,PrefixAt 12 V:=by
  intro V hV
  have hv:V < 131:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r12_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r12_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r12_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r12_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r12_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r12_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r12_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r12_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r12_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r12_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r12_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r12_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r12_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r12_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r12_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r12_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=prefix_r12_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem prefix_r13_part0:∀ i ∈ List.range 8,PrefixAt 13 (0+i):=by
  decide +kernel

theorem prefix_r13_part1:∀ i ∈ List.range 8,PrefixAt 13 (8+i):=by
  decide +kernel

theorem prefix_r13_part2:∀ i ∈ List.range 8,PrefixAt 13 (16+i):=by
  decide +kernel

theorem prefix_r13_part3:∀ i ∈ List.range 8,PrefixAt 13 (24+i):=by
  decide +kernel

theorem prefix_r13_part4:∀ i ∈ List.range 8,PrefixAt 13 (32+i):=by
  decide +kernel

theorem prefix_r13_part5:∀ i ∈ List.range 8,PrefixAt 13 (40+i):=by
  decide +kernel

theorem prefix_r13_part6:∀ i ∈ List.range 8,PrefixAt 13 (48+i):=by
  decide +kernel

theorem prefix_r13_part7:∀ i ∈ List.range 8,PrefixAt 13 (56+i):=by
  decide +kernel

theorem prefix_r13_part8:∀ i ∈ List.range 8,PrefixAt 13 (64+i):=by
  decide +kernel

theorem prefix_r13_part9:∀ i ∈ List.range 8,PrefixAt 13 (72+i):=by
  decide +kernel

theorem prefix_r13_part10:∀ i ∈ List.range 8,PrefixAt 13 (80+i):=by
  decide +kernel

theorem prefix_r13_part11:∀ i ∈ List.range 8,PrefixAt 13 (88+i):=by
  decide +kernel

theorem prefix_r13_part12:∀ i ∈ List.range 8,PrefixAt 13 (96+i):=by
  decide +kernel

theorem prefix_r13_part13:∀ i ∈ List.range 8,PrefixAt 13 (104+i):=by
  decide +kernel

theorem prefix_r13_part14:∀ i ∈ List.range 8,PrefixAt 13 (112+i):=by
  decide +kernel

theorem prefix_r13_part15:∀ i ∈ List.range 8,PrefixAt 13 (120+i):=by
  decide +kernel

theorem prefix_r13_part16:∀ i ∈ List.range 2,PrefixAt 13 (128+i):=by
  decide +kernel

theorem prefix_r13:∀ V ∈ List.range 130,PrefixAt 13 V:=by
  intro V hV
  have hv:V < 130:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r13_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r13_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r13_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r13_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r13_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r13_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r13_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r13_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r13_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r13_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r13_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r13_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r13_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r13_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r13_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r13_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=prefix_r13_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem prefix_r14_part0:∀ i ∈ List.range 8,PrefixAt 14 (0+i):=by
  decide +kernel

theorem prefix_r14_part1:∀ i ∈ List.range 8,PrefixAt 14 (8+i):=by
  decide +kernel

theorem prefix_r14_part2:∀ i ∈ List.range 8,PrefixAt 14 (16+i):=by
  decide +kernel

theorem prefix_r14_part3:∀ i ∈ List.range 8,PrefixAt 14 (24+i):=by
  decide +kernel

theorem prefix_r14_part4:∀ i ∈ List.range 8,PrefixAt 14 (32+i):=by
  decide +kernel

theorem prefix_r14_part5:∀ i ∈ List.range 8,PrefixAt 14 (40+i):=by
  decide +kernel

theorem prefix_r14_part6:∀ i ∈ List.range 8,PrefixAt 14 (48+i):=by
  decide +kernel

theorem prefix_r14_part7:∀ i ∈ List.range 8,PrefixAt 14 (56+i):=by
  decide +kernel

theorem prefix_r14_part8:∀ i ∈ List.range 8,PrefixAt 14 (64+i):=by
  decide +kernel

theorem prefix_r14_part9:∀ i ∈ List.range 8,PrefixAt 14 (72+i):=by
  decide +kernel

theorem prefix_r14_part10:∀ i ∈ List.range 8,PrefixAt 14 (80+i):=by
  decide +kernel

theorem prefix_r14_part11:∀ i ∈ List.range 8,PrefixAt 14 (88+i):=by
  decide +kernel

theorem prefix_r14_part12:∀ i ∈ List.range 8,PrefixAt 14 (96+i):=by
  decide +kernel

theorem prefix_r14_part13:∀ i ∈ List.range 8,PrefixAt 14 (104+i):=by
  decide +kernel

theorem prefix_r14_part14:∀ i ∈ List.range 8,PrefixAt 14 (112+i):=by
  decide +kernel

theorem prefix_r14_part15:∀ i ∈ List.range 8,PrefixAt 14 (120+i):=by
  decide +kernel

theorem prefix_r14_part16:∀ i ∈ List.range 1,PrefixAt 14 (128+i):=by
  decide +kernel

theorem prefix_r14:∀ V ∈ List.range 129,PrefixAt 14 V:=by
  intro V hV
  have hv:V < 129:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r14_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r14_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r14_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r14_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r14_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r14_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r14_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r14_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r14_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r14_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r14_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r14_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r14_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r14_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r14_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                by_cases h15:V < 128
                                · have hi:=prefix_r14_part15 (V-120) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                                ·
                                  have hi:=prefix_r14_part16 (V-128) (List.mem_range.mpr (by omega))
                                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem prefix_r15_part0:∀ i ∈ List.range 8,PrefixAt 15 (0+i):=by
  decide +kernel

theorem prefix_r15_part1:∀ i ∈ List.range 8,PrefixAt 15 (8+i):=by
  decide +kernel

theorem prefix_r15_part2:∀ i ∈ List.range 8,PrefixAt 15 (16+i):=by
  decide +kernel

theorem prefix_r15_part3:∀ i ∈ List.range 8,PrefixAt 15 (24+i):=by
  decide +kernel

theorem prefix_r15_part4:∀ i ∈ List.range 8,PrefixAt 15 (32+i):=by
  decide +kernel

theorem prefix_r15_part5:∀ i ∈ List.range 8,PrefixAt 15 (40+i):=by
  decide +kernel

theorem prefix_r15_part6:∀ i ∈ List.range 8,PrefixAt 15 (48+i):=by
  decide +kernel

theorem prefix_r15_part7:∀ i ∈ List.range 8,PrefixAt 15 (56+i):=by
  decide +kernel

theorem prefix_r15_part8:∀ i ∈ List.range 8,PrefixAt 15 (64+i):=by
  decide +kernel

theorem prefix_r15_part9:∀ i ∈ List.range 8,PrefixAt 15 (72+i):=by
  decide +kernel

theorem prefix_r15_part10:∀ i ∈ List.range 8,PrefixAt 15 (80+i):=by
  decide +kernel

theorem prefix_r15_part11:∀ i ∈ List.range 8,PrefixAt 15 (88+i):=by
  decide +kernel

theorem prefix_r15_part12:∀ i ∈ List.range 8,PrefixAt 15 (96+i):=by
  decide +kernel

theorem prefix_r15_part13:∀ i ∈ List.range 8,PrefixAt 15 (104+i):=by
  decide +kernel

theorem prefix_r15_part14:∀ i ∈ List.range 8,PrefixAt 15 (112+i):=by
  decide +kernel

theorem prefix_r15_part15:∀ i ∈ List.range 8,PrefixAt 15 (120+i):=by
  decide +kernel

theorem prefix_r15:∀ V ∈ List.range 128,PrefixAt 15 V:=by
  intro V hV
  have hv:V < 128:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r15_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r15_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r15_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r15_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r15_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r15_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r15_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r15_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r15_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r15_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r15_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r15_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r15_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r15_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r15_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=prefix_r15_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem prefix_r16_part0:∀ i ∈ List.range 8,PrefixAt 16 (0+i):=by
  decide +kernel

theorem prefix_r16_part1:∀ i ∈ List.range 8,PrefixAt 16 (8+i):=by
  decide +kernel

theorem prefix_r16_part2:∀ i ∈ List.range 8,PrefixAt 16 (16+i):=by
  decide +kernel

theorem prefix_r16_part3:∀ i ∈ List.range 8,PrefixAt 16 (24+i):=by
  decide +kernel

theorem prefix_r16_part4:∀ i ∈ List.range 8,PrefixAt 16 (32+i):=by
  decide +kernel

theorem prefix_r16_part5:∀ i ∈ List.range 8,PrefixAt 16 (40+i):=by
  decide +kernel

theorem prefix_r16_part6:∀ i ∈ List.range 8,PrefixAt 16 (48+i):=by
  decide +kernel

theorem prefix_r16_part7:∀ i ∈ List.range 8,PrefixAt 16 (56+i):=by
  decide +kernel

theorem prefix_r16_part8:∀ i ∈ List.range 8,PrefixAt 16 (64+i):=by
  decide +kernel

theorem prefix_r16_part9:∀ i ∈ List.range 8,PrefixAt 16 (72+i):=by
  decide +kernel

theorem prefix_r16_part10:∀ i ∈ List.range 8,PrefixAt 16 (80+i):=by
  decide +kernel

theorem prefix_r16_part11:∀ i ∈ List.range 8,PrefixAt 16 (88+i):=by
  decide +kernel

theorem prefix_r16_part12:∀ i ∈ List.range 8,PrefixAt 16 (96+i):=by
  decide +kernel

theorem prefix_r16_part13:∀ i ∈ List.range 8,PrefixAt 16 (104+i):=by
  decide +kernel

theorem prefix_r16_part14:∀ i ∈ List.range 8,PrefixAt 16 (112+i):=by
  decide +kernel

theorem prefix_r16_part15:∀ i ∈ List.range 7,PrefixAt 16 (120+i):=by
  decide +kernel

theorem prefix_r16:∀ V ∈ List.range 127,PrefixAt 16 V:=by
  intro V hV
  have hv:V < 127:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r16_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r16_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r16_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r16_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r16_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r16_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r16_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r16_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r16_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r16_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r16_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r16_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r16_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r16_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r16_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=prefix_r16_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem prefix_r17_part0:∀ i ∈ List.range 8,PrefixAt 17 (0+i):=by
  decide +kernel

theorem prefix_r17_part1:∀ i ∈ List.range 8,PrefixAt 17 (8+i):=by
  decide +kernel

theorem prefix_r17_part2:∀ i ∈ List.range 8,PrefixAt 17 (16+i):=by
  decide +kernel

theorem prefix_r17_part3:∀ i ∈ List.range 8,PrefixAt 17 (24+i):=by
  decide +kernel

theorem prefix_r17_part4:∀ i ∈ List.range 8,PrefixAt 17 (32+i):=by
  decide +kernel

theorem prefix_r17_part5:∀ i ∈ List.range 8,PrefixAt 17 (40+i):=by
  decide +kernel

theorem prefix_r17_part6:∀ i ∈ List.range 8,PrefixAt 17 (48+i):=by
  decide +kernel

theorem prefix_r17_part7:∀ i ∈ List.range 8,PrefixAt 17 (56+i):=by
  decide +kernel

theorem prefix_r17_part8:∀ i ∈ List.range 8,PrefixAt 17 (64+i):=by
  decide +kernel

theorem prefix_r17_part9:∀ i ∈ List.range 8,PrefixAt 17 (72+i):=by
  decide +kernel

theorem prefix_r17_part10:∀ i ∈ List.range 8,PrefixAt 17 (80+i):=by
  decide +kernel

theorem prefix_r17_part11:∀ i ∈ List.range 8,PrefixAt 17 (88+i):=by
  decide +kernel

theorem prefix_r17_part12:∀ i ∈ List.range 8,PrefixAt 17 (96+i):=by
  decide +kernel

theorem prefix_r17_part13:∀ i ∈ List.range 8,PrefixAt 17 (104+i):=by
  decide +kernel

theorem prefix_r17_part14:∀ i ∈ List.range 8,PrefixAt 17 (112+i):=by
  decide +kernel

theorem prefix_r17_part15:∀ i ∈ List.range 6,PrefixAt 17 (120+i):=by
  decide +kernel

theorem prefix_r17:∀ V ∈ List.range 126,PrefixAt 17 V:=by
  intro V hV
  have hv:V < 126:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r17_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r17_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r17_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r17_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r17_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r17_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r17_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r17_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r17_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r17_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r17_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r17_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r17_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r17_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r17_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=prefix_r17_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem prefix_r18_part0:∀ i ∈ List.range 8,PrefixAt 18 (0+i):=by
  decide +kernel

theorem prefix_r18_part1:∀ i ∈ List.range 8,PrefixAt 18 (8+i):=by
  decide +kernel

theorem prefix_r18_part2:∀ i ∈ List.range 8,PrefixAt 18 (16+i):=by
  decide +kernel

theorem prefix_r18_part3:∀ i ∈ List.range 8,PrefixAt 18 (24+i):=by
  decide +kernel

theorem prefix_r18_part4:∀ i ∈ List.range 8,PrefixAt 18 (32+i):=by
  decide +kernel

theorem prefix_r18_part5:∀ i ∈ List.range 8,PrefixAt 18 (40+i):=by
  decide +kernel

theorem prefix_r18_part6:∀ i ∈ List.range 8,PrefixAt 18 (48+i):=by
  decide +kernel

theorem prefix_r18_part7:∀ i ∈ List.range 8,PrefixAt 18 (56+i):=by
  decide +kernel

theorem prefix_r18_part8:∀ i ∈ List.range 8,PrefixAt 18 (64+i):=by
  decide +kernel

theorem prefix_r18_part9:∀ i ∈ List.range 8,PrefixAt 18 (72+i):=by
  decide +kernel

theorem prefix_r18_part10:∀ i ∈ List.range 8,PrefixAt 18 (80+i):=by
  decide +kernel

theorem prefix_r18_part11:∀ i ∈ List.range 8,PrefixAt 18 (88+i):=by
  decide +kernel

theorem prefix_r18_part12:∀ i ∈ List.range 8,PrefixAt 18 (96+i):=by
  decide +kernel

theorem prefix_r18_part13:∀ i ∈ List.range 8,PrefixAt 18 (104+i):=by
  decide +kernel

theorem prefix_r18_part14:∀ i ∈ List.range 8,PrefixAt 18 (112+i):=by
  decide +kernel

theorem prefix_r18_part15:∀ i ∈ List.range 5,PrefixAt 18 (120+i):=by
  decide +kernel

theorem prefix_r18:∀ V ∈ List.range 125,PrefixAt 18 V:=by
  intro V hV
  have hv:V < 125:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r18_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r18_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r18_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r18_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r18_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r18_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r18_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r18_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r18_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r18_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r18_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r18_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r18_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r18_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r18_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=prefix_r18_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem prefix_r19_part0:∀ i ∈ List.range 8,PrefixAt 19 (0+i):=by
  decide +kernel

theorem prefix_r19_part1:∀ i ∈ List.range 8,PrefixAt 19 (8+i):=by
  decide +kernel

theorem prefix_r19_part2:∀ i ∈ List.range 8,PrefixAt 19 (16+i):=by
  decide +kernel

theorem prefix_r19_part3:∀ i ∈ List.range 8,PrefixAt 19 (24+i):=by
  decide +kernel

theorem prefix_r19_part4:∀ i ∈ List.range 8,PrefixAt 19 (32+i):=by
  decide +kernel

theorem prefix_r19_part5:∀ i ∈ List.range 8,PrefixAt 19 (40+i):=by
  decide +kernel

theorem prefix_r19_part6:∀ i ∈ List.range 8,PrefixAt 19 (48+i):=by
  decide +kernel

theorem prefix_r19_part7:∀ i ∈ List.range 8,PrefixAt 19 (56+i):=by
  decide +kernel

theorem prefix_r19_part8:∀ i ∈ List.range 8,PrefixAt 19 (64+i):=by
  decide +kernel

theorem prefix_r19_part9:∀ i ∈ List.range 8,PrefixAt 19 (72+i):=by
  decide +kernel

theorem prefix_r19_part10:∀ i ∈ List.range 8,PrefixAt 19 (80+i):=by
  decide +kernel

theorem prefix_r19_part11:∀ i ∈ List.range 8,PrefixAt 19 (88+i):=by
  decide +kernel

theorem prefix_r19_part12:∀ i ∈ List.range 8,PrefixAt 19 (96+i):=by
  decide +kernel

theorem prefix_r19_part13:∀ i ∈ List.range 8,PrefixAt 19 (104+i):=by
  decide +kernel

theorem prefix_r19_part14:∀ i ∈ List.range 8,PrefixAt 19 (112+i):=by
  decide +kernel

theorem prefix_r19_part15:∀ i ∈ List.range 4,PrefixAt 19 (120+i):=by
  decide +kernel

theorem prefix_r19:∀ V ∈ List.range 124,PrefixAt 19 V:=by
  intro V hV
  have hv:V < 124:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r19_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r19_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r19_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r19_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r19_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r19_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r19_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r19_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r19_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r19_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r19_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r19_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r19_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r19_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r19_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=prefix_r19_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem prefix_r20_part0:∀ i ∈ List.range 8,PrefixAt 20 (0+i):=by
  decide +kernel

theorem prefix_r20_part1:∀ i ∈ List.range 8,PrefixAt 20 (8+i):=by
  decide +kernel

theorem prefix_r20_part2:∀ i ∈ List.range 8,PrefixAt 20 (16+i):=by
  decide +kernel

theorem prefix_r20_part3:∀ i ∈ List.range 8,PrefixAt 20 (24+i):=by
  decide +kernel

theorem prefix_r20_part4:∀ i ∈ List.range 8,PrefixAt 20 (32+i):=by
  decide +kernel

theorem prefix_r20_part5:∀ i ∈ List.range 8,PrefixAt 20 (40+i):=by
  decide +kernel

theorem prefix_r20_part6:∀ i ∈ List.range 8,PrefixAt 20 (48+i):=by
  decide +kernel

theorem prefix_r20_part7:∀ i ∈ List.range 8,PrefixAt 20 (56+i):=by
  decide +kernel

theorem prefix_r20_part8:∀ i ∈ List.range 8,PrefixAt 20 (64+i):=by
  decide +kernel

theorem prefix_r20_part9:∀ i ∈ List.range 8,PrefixAt 20 (72+i):=by
  decide +kernel

theorem prefix_r20_part10:∀ i ∈ List.range 8,PrefixAt 20 (80+i):=by
  decide +kernel

theorem prefix_r20_part11:∀ i ∈ List.range 8,PrefixAt 20 (88+i):=by
  decide +kernel

theorem prefix_r20_part12:∀ i ∈ List.range 8,PrefixAt 20 (96+i):=by
  decide +kernel

theorem prefix_r20_part13:∀ i ∈ List.range 8,PrefixAt 20 (104+i):=by
  decide +kernel

theorem prefix_r20_part14:∀ i ∈ List.range 8,PrefixAt 20 (112+i):=by
  decide +kernel

theorem prefix_r20_part15:∀ i ∈ List.range 3,PrefixAt 20 (120+i):=by
  decide +kernel

theorem prefix_r20:∀ V ∈ List.range 123,PrefixAt 20 V:=by
  intro V hV
  have hv:V < 123:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r20_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r20_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r20_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r20_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r20_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r20_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r20_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r20_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r20_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r20_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r20_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r20_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r20_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r20_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r20_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=prefix_r20_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem prefix_r21_part0:∀ i ∈ List.range 8,PrefixAt 21 (0+i):=by
  decide +kernel

theorem prefix_r21_part1:∀ i ∈ List.range 8,PrefixAt 21 (8+i):=by
  decide +kernel

theorem prefix_r21_part2:∀ i ∈ List.range 8,PrefixAt 21 (16+i):=by
  decide +kernel

theorem prefix_r21_part3:∀ i ∈ List.range 8,PrefixAt 21 (24+i):=by
  decide +kernel

theorem prefix_r21_part4:∀ i ∈ List.range 8,PrefixAt 21 (32+i):=by
  decide +kernel

theorem prefix_r21_part5:∀ i ∈ List.range 8,PrefixAt 21 (40+i):=by
  decide +kernel

theorem prefix_r21_part6:∀ i ∈ List.range 8,PrefixAt 21 (48+i):=by
  decide +kernel

theorem prefix_r21_part7:∀ i ∈ List.range 8,PrefixAt 21 (56+i):=by
  decide +kernel

theorem prefix_r21_part8:∀ i ∈ List.range 8,PrefixAt 21 (64+i):=by
  decide +kernel

theorem prefix_r21_part9:∀ i ∈ List.range 8,PrefixAt 21 (72+i):=by
  decide +kernel

theorem prefix_r21_part10:∀ i ∈ List.range 8,PrefixAt 21 (80+i):=by
  decide +kernel

theorem prefix_r21_part11:∀ i ∈ List.range 8,PrefixAt 21 (88+i):=by
  decide +kernel

theorem prefix_r21_part12:∀ i ∈ List.range 8,PrefixAt 21 (96+i):=by
  decide +kernel

theorem prefix_r21_part13:∀ i ∈ List.range 8,PrefixAt 21 (104+i):=by
  decide +kernel

theorem prefix_r21_part14:∀ i ∈ List.range 8,PrefixAt 21 (112+i):=by
  decide +kernel

theorem prefix_r21_part15:∀ i ∈ List.range 2,PrefixAt 21 (120+i):=by
  decide +kernel

theorem prefix_r21:∀ V ∈ List.range 122,PrefixAt 21 V:=by
  intro V hV
  have hv:V < 122:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r21_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r21_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r21_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r21_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r21_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r21_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r21_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r21_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r21_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r21_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r21_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r21_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r21_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r21_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r21_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=prefix_r21_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem prefix_r22_part0:∀ i ∈ List.range 8,PrefixAt 22 (0+i):=by
  decide +kernel

theorem prefix_r22_part1:∀ i ∈ List.range 8,PrefixAt 22 (8+i):=by
  decide +kernel

theorem prefix_r22_part2:∀ i ∈ List.range 8,PrefixAt 22 (16+i):=by
  decide +kernel

theorem prefix_r22_part3:∀ i ∈ List.range 8,PrefixAt 22 (24+i):=by
  decide +kernel

theorem prefix_r22_part4:∀ i ∈ List.range 8,PrefixAt 22 (32+i):=by
  decide +kernel

theorem prefix_r22_part5:∀ i ∈ List.range 8,PrefixAt 22 (40+i):=by
  decide +kernel

theorem prefix_r22_part6:∀ i ∈ List.range 8,PrefixAt 22 (48+i):=by
  decide +kernel

theorem prefix_r22_part7:∀ i ∈ List.range 8,PrefixAt 22 (56+i):=by
  decide +kernel

theorem prefix_r22_part8:∀ i ∈ List.range 8,PrefixAt 22 (64+i):=by
  decide +kernel

theorem prefix_r22_part9:∀ i ∈ List.range 8,PrefixAt 22 (72+i):=by
  decide +kernel

theorem prefix_r22_part10:∀ i ∈ List.range 8,PrefixAt 22 (80+i):=by
  decide +kernel

theorem prefix_r22_part11:∀ i ∈ List.range 8,PrefixAt 22 (88+i):=by
  decide +kernel

theorem prefix_r22_part12:∀ i ∈ List.range 8,PrefixAt 22 (96+i):=by
  decide +kernel

theorem prefix_r22_part13:∀ i ∈ List.range 8,PrefixAt 22 (104+i):=by
  decide +kernel

theorem prefix_r22_part14:∀ i ∈ List.range 8,PrefixAt 22 (112+i):=by
  decide +kernel

theorem prefix_r22_part15:∀ i ∈ List.range 1,PrefixAt 22 (120+i):=by
  decide +kernel

theorem prefix_r22:∀ V ∈ List.range 121,PrefixAt 22 V:=by
  intro V hV
  have hv:V < 121:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r22_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r22_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r22_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r22_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r22_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r22_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r22_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r22_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r22_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r22_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r22_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r22_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r22_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r22_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              by_cases h14:V < 120
                              · have hi:=prefix_r22_part14 (V-112) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                              ·
                                have hi:=prefix_r22_part15 (V-120) (List.mem_range.mpr (by omega))
                                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem prefix_r23_part0:∀ i ∈ List.range 8,PrefixAt 23 (0+i):=by
  decide +kernel

theorem prefix_r23_part1:∀ i ∈ List.range 8,PrefixAt 23 (8+i):=by
  decide +kernel

theorem prefix_r23_part2:∀ i ∈ List.range 8,PrefixAt 23 (16+i):=by
  decide +kernel

theorem prefix_r23_part3:∀ i ∈ List.range 8,PrefixAt 23 (24+i):=by
  decide +kernel

theorem prefix_r23_part4:∀ i ∈ List.range 8,PrefixAt 23 (32+i):=by
  decide +kernel

theorem prefix_r23_part5:∀ i ∈ List.range 8,PrefixAt 23 (40+i):=by
  decide +kernel

theorem prefix_r23_part6:∀ i ∈ List.range 8,PrefixAt 23 (48+i):=by
  decide +kernel

theorem prefix_r23_part7:∀ i ∈ List.range 8,PrefixAt 23 (56+i):=by
  decide +kernel

theorem prefix_r23_part8:∀ i ∈ List.range 8,PrefixAt 23 (64+i):=by
  decide +kernel

theorem prefix_r23_part9:∀ i ∈ List.range 8,PrefixAt 23 (72+i):=by
  decide +kernel

theorem prefix_r23_part10:∀ i ∈ List.range 8,PrefixAt 23 (80+i):=by
  decide +kernel

theorem prefix_r23_part11:∀ i ∈ List.range 8,PrefixAt 23 (88+i):=by
  decide +kernel

theorem prefix_r23_part12:∀ i ∈ List.range 8,PrefixAt 23 (96+i):=by
  decide +kernel

theorem prefix_r23_part13:∀ i ∈ List.range 8,PrefixAt 23 (104+i):=by
  decide +kernel

theorem prefix_r23_part14:∀ i ∈ List.range 8,PrefixAt 23 (112+i):=by
  decide +kernel

theorem prefix_r23:∀ V ∈ List.range 120,PrefixAt 23 V:=by
  intro V hV
  have hv:V < 120:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r23_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r23_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r23_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r23_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r23_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r23_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r23_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r23_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r23_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r23_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r23_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r23_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r23_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r23_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=prefix_r23_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem prefix_r24_part0:∀ i ∈ List.range 8,PrefixAt 24 (0+i):=by
  decide +kernel

theorem prefix_r24_part1:∀ i ∈ List.range 8,PrefixAt 24 (8+i):=by
  decide +kernel

theorem prefix_r24_part2:∀ i ∈ List.range 8,PrefixAt 24 (16+i):=by
  decide +kernel

theorem prefix_r24_part3:∀ i ∈ List.range 8,PrefixAt 24 (24+i):=by
  decide +kernel

theorem prefix_r24_part4:∀ i ∈ List.range 8,PrefixAt 24 (32+i):=by
  decide +kernel

theorem prefix_r24_part5:∀ i ∈ List.range 8,PrefixAt 24 (40+i):=by
  decide +kernel

theorem prefix_r24_part6:∀ i ∈ List.range 8,PrefixAt 24 (48+i):=by
  decide +kernel

theorem prefix_r24_part7:∀ i ∈ List.range 8,PrefixAt 24 (56+i):=by
  decide +kernel

theorem prefix_r24_part8:∀ i ∈ List.range 8,PrefixAt 24 (64+i):=by
  decide +kernel

theorem prefix_r24_part9:∀ i ∈ List.range 8,PrefixAt 24 (72+i):=by
  decide +kernel

theorem prefix_r24_part10:∀ i ∈ List.range 8,PrefixAt 24 (80+i):=by
  decide +kernel

theorem prefix_r24_part11:∀ i ∈ List.range 8,PrefixAt 24 (88+i):=by
  decide +kernel

theorem prefix_r24_part12:∀ i ∈ List.range 8,PrefixAt 24 (96+i):=by
  decide +kernel

theorem prefix_r24_part13:∀ i ∈ List.range 8,PrefixAt 24 (104+i):=by
  decide +kernel

theorem prefix_r24_part14:∀ i ∈ List.range 7,PrefixAt 24 (112+i):=by
  decide +kernel

theorem prefix_r24:∀ V ∈ List.range 119,PrefixAt 24 V:=by
  intro V hV
  have hv:V < 119:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r24_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r24_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r24_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r24_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r24_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r24_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r24_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r24_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r24_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r24_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r24_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r24_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r24_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r24_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=prefix_r24_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem prefix_r25_part0:∀ i ∈ List.range 8,PrefixAt 25 (0+i):=by
  decide +kernel

theorem prefix_r25_part1:∀ i ∈ List.range 8,PrefixAt 25 (8+i):=by
  decide +kernel

theorem prefix_r25_part2:∀ i ∈ List.range 8,PrefixAt 25 (16+i):=by
  decide +kernel

theorem prefix_r25_part3:∀ i ∈ List.range 8,PrefixAt 25 (24+i):=by
  decide +kernel

theorem prefix_r25_part4:∀ i ∈ List.range 8,PrefixAt 25 (32+i):=by
  decide +kernel

theorem prefix_r25_part5:∀ i ∈ List.range 8,PrefixAt 25 (40+i):=by
  decide +kernel

theorem prefix_r25_part6:∀ i ∈ List.range 8,PrefixAt 25 (48+i):=by
  decide +kernel

theorem prefix_r25_part7:∀ i ∈ List.range 8,PrefixAt 25 (56+i):=by
  decide +kernel

theorem prefix_r25_part8:∀ i ∈ List.range 8,PrefixAt 25 (64+i):=by
  decide +kernel

theorem prefix_r25_part9:∀ i ∈ List.range 8,PrefixAt 25 (72+i):=by
  decide +kernel

theorem prefix_r25_part10:∀ i ∈ List.range 8,PrefixAt 25 (80+i):=by
  decide +kernel

theorem prefix_r25_part11:∀ i ∈ List.range 8,PrefixAt 25 (88+i):=by
  decide +kernel

theorem prefix_r25_part12:∀ i ∈ List.range 8,PrefixAt 25 (96+i):=by
  decide +kernel

theorem prefix_r25_part13:∀ i ∈ List.range 8,PrefixAt 25 (104+i):=by
  decide +kernel

theorem prefix_r25_part14:∀ i ∈ List.range 6,PrefixAt 25 (112+i):=by
  decide +kernel

theorem prefix_r25:∀ V ∈ List.range 118,PrefixAt 25 V:=by
  intro V hV
  have hv:V < 118:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r25_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r25_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r25_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r25_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r25_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r25_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r25_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r25_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r25_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r25_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r25_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r25_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r25_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r25_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=prefix_r25_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem prefix_r26_part0:∀ i ∈ List.range 8,PrefixAt 26 (0+i):=by
  decide +kernel

theorem prefix_r26_part1:∀ i ∈ List.range 8,PrefixAt 26 (8+i):=by
  decide +kernel

theorem prefix_r26_part2:∀ i ∈ List.range 8,PrefixAt 26 (16+i):=by
  decide +kernel

theorem prefix_r26_part3:∀ i ∈ List.range 8,PrefixAt 26 (24+i):=by
  decide +kernel

theorem prefix_r26_part4:∀ i ∈ List.range 8,PrefixAt 26 (32+i):=by
  decide +kernel

theorem prefix_r26_part5:∀ i ∈ List.range 8,PrefixAt 26 (40+i):=by
  decide +kernel

theorem prefix_r26_part6:∀ i ∈ List.range 8,PrefixAt 26 (48+i):=by
  decide +kernel

theorem prefix_r26_part7:∀ i ∈ List.range 8,PrefixAt 26 (56+i):=by
  decide +kernel

theorem prefix_r26_part8:∀ i ∈ List.range 8,PrefixAt 26 (64+i):=by
  decide +kernel

theorem prefix_r26_part9:∀ i ∈ List.range 8,PrefixAt 26 (72+i):=by
  decide +kernel

theorem prefix_r26_part10:∀ i ∈ List.range 8,PrefixAt 26 (80+i):=by
  decide +kernel

theorem prefix_r26_part11:∀ i ∈ List.range 8,PrefixAt 26 (88+i):=by
  decide +kernel

theorem prefix_r26_part12:∀ i ∈ List.range 8,PrefixAt 26 (96+i):=by
  decide +kernel

theorem prefix_r26_part13:∀ i ∈ List.range 8,PrefixAt 26 (104+i):=by
  decide +kernel

theorem prefix_r26_part14:∀ i ∈ List.range 5,PrefixAt 26 (112+i):=by
  decide +kernel

theorem prefix_r26:∀ V ∈ List.range 117,PrefixAt 26 V:=by
  intro V hV
  have hv:V < 117:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r26_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r26_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r26_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r26_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r26_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r26_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r26_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r26_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r26_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r26_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r26_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r26_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r26_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r26_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=prefix_r26_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem prefix_r27_part0:∀ i ∈ List.range 8,PrefixAt 27 (0+i):=by
  decide +kernel

theorem prefix_r27_part1:∀ i ∈ List.range 8,PrefixAt 27 (8+i):=by
  decide +kernel

theorem prefix_r27_part2:∀ i ∈ List.range 8,PrefixAt 27 (16+i):=by
  decide +kernel

theorem prefix_r27_part3:∀ i ∈ List.range 8,PrefixAt 27 (24+i):=by
  decide +kernel

theorem prefix_r27_part4:∀ i ∈ List.range 8,PrefixAt 27 (32+i):=by
  decide +kernel

theorem prefix_r27_part5:∀ i ∈ List.range 8,PrefixAt 27 (40+i):=by
  decide +kernel

theorem prefix_r27_part6:∀ i ∈ List.range 8,PrefixAt 27 (48+i):=by
  decide +kernel

theorem prefix_r27_part7:∀ i ∈ List.range 8,PrefixAt 27 (56+i):=by
  decide +kernel

theorem prefix_r27_part8:∀ i ∈ List.range 8,PrefixAt 27 (64+i):=by
  decide +kernel

theorem prefix_r27_part9:∀ i ∈ List.range 8,PrefixAt 27 (72+i):=by
  decide +kernel

theorem prefix_r27_part10:∀ i ∈ List.range 8,PrefixAt 27 (80+i):=by
  decide +kernel

theorem prefix_r27_part11:∀ i ∈ List.range 8,PrefixAt 27 (88+i):=by
  decide +kernel

theorem prefix_r27_part12:∀ i ∈ List.range 8,PrefixAt 27 (96+i):=by
  decide +kernel

theorem prefix_r27_part13:∀ i ∈ List.range 8,PrefixAt 27 (104+i):=by
  decide +kernel

theorem prefix_r27_part14:∀ i ∈ List.range 4,PrefixAt 27 (112+i):=by
  decide +kernel

theorem prefix_r27:∀ V ∈ List.range 116,PrefixAt 27 V:=by
  intro V hV
  have hv:V < 116:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r27_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r27_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r27_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r27_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r27_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r27_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r27_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r27_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r27_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r27_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r27_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r27_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r27_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r27_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=prefix_r27_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem prefix_r28_part0:∀ i ∈ List.range 8,PrefixAt 28 (0+i):=by
  decide +kernel

theorem prefix_r28_part1:∀ i ∈ List.range 8,PrefixAt 28 (8+i):=by
  decide +kernel

theorem prefix_r28_part2:∀ i ∈ List.range 8,PrefixAt 28 (16+i):=by
  decide +kernel

theorem prefix_r28_part3:∀ i ∈ List.range 8,PrefixAt 28 (24+i):=by
  decide +kernel

theorem prefix_r28_part4:∀ i ∈ List.range 8,PrefixAt 28 (32+i):=by
  decide +kernel

theorem prefix_r28_part5:∀ i ∈ List.range 8,PrefixAt 28 (40+i):=by
  decide +kernel

theorem prefix_r28_part6:∀ i ∈ List.range 8,PrefixAt 28 (48+i):=by
  decide +kernel

theorem prefix_r28_part7:∀ i ∈ List.range 8,PrefixAt 28 (56+i):=by
  decide +kernel

theorem prefix_r28_part8:∀ i ∈ List.range 8,PrefixAt 28 (64+i):=by
  decide +kernel

theorem prefix_r28_part9:∀ i ∈ List.range 8,PrefixAt 28 (72+i):=by
  decide +kernel

theorem prefix_r28_part10:∀ i ∈ List.range 8,PrefixAt 28 (80+i):=by
  decide +kernel

theorem prefix_r28_part11:∀ i ∈ List.range 8,PrefixAt 28 (88+i):=by
  decide +kernel

theorem prefix_r28_part12:∀ i ∈ List.range 8,PrefixAt 28 (96+i):=by
  decide +kernel

theorem prefix_r28_part13:∀ i ∈ List.range 8,PrefixAt 28 (104+i):=by
  decide +kernel

theorem prefix_r28_part14:∀ i ∈ List.range 3,PrefixAt 28 (112+i):=by
  decide +kernel

theorem prefix_r28:∀ V ∈ List.range 115,PrefixAt 28 V:=by
  intro V hV
  have hv:V < 115:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r28_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r28_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r28_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r28_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r28_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r28_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r28_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r28_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r28_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r28_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r28_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r28_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r28_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r28_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=prefix_r28_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem prefix_r29_part0:∀ i ∈ List.range 8,PrefixAt 29 (0+i):=by
  decide +kernel

theorem prefix_r29_part1:∀ i ∈ List.range 8,PrefixAt 29 (8+i):=by
  decide +kernel

theorem prefix_r29_part2:∀ i ∈ List.range 8,PrefixAt 29 (16+i):=by
  decide +kernel

theorem prefix_r29_part3:∀ i ∈ List.range 8,PrefixAt 29 (24+i):=by
  decide +kernel

theorem prefix_r29_part4:∀ i ∈ List.range 8,PrefixAt 29 (32+i):=by
  decide +kernel

theorem prefix_r29_part5:∀ i ∈ List.range 8,PrefixAt 29 (40+i):=by
  decide +kernel

theorem prefix_r29_part6:∀ i ∈ List.range 8,PrefixAt 29 (48+i):=by
  decide +kernel

theorem prefix_r29_part7:∀ i ∈ List.range 8,PrefixAt 29 (56+i):=by
  decide +kernel

theorem prefix_r29_part8:∀ i ∈ List.range 8,PrefixAt 29 (64+i):=by
  decide +kernel

theorem prefix_r29_part9:∀ i ∈ List.range 8,PrefixAt 29 (72+i):=by
  decide +kernel

theorem prefix_r29_part10:∀ i ∈ List.range 8,PrefixAt 29 (80+i):=by
  decide +kernel

theorem prefix_r29_part11:∀ i ∈ List.range 8,PrefixAt 29 (88+i):=by
  decide +kernel

theorem prefix_r29_part12:∀ i ∈ List.range 8,PrefixAt 29 (96+i):=by
  decide +kernel

theorem prefix_r29_part13:∀ i ∈ List.range 8,PrefixAt 29 (104+i):=by
  decide +kernel

theorem prefix_r29_part14:∀ i ∈ List.range 2,PrefixAt 29 (112+i):=by
  decide +kernel

theorem prefix_r29:∀ V ∈ List.range 114,PrefixAt 29 V:=by
  intro V hV
  have hv:V < 114:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r29_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r29_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r29_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r29_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r29_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r29_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r29_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r29_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r29_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r29_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r29_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r29_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r29_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r29_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=prefix_r29_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem prefix_r30_part0:∀ i ∈ List.range 8,PrefixAt 30 (0+i):=by
  decide +kernel

theorem prefix_r30_part1:∀ i ∈ List.range 8,PrefixAt 30 (8+i):=by
  decide +kernel

theorem prefix_r30_part2:∀ i ∈ List.range 8,PrefixAt 30 (16+i):=by
  decide +kernel

theorem prefix_r30_part3:∀ i ∈ List.range 8,PrefixAt 30 (24+i):=by
  decide +kernel

theorem prefix_r30_part4:∀ i ∈ List.range 8,PrefixAt 30 (32+i):=by
  decide +kernel

theorem prefix_r30_part5:∀ i ∈ List.range 8,PrefixAt 30 (40+i):=by
  decide +kernel

theorem prefix_r30_part6:∀ i ∈ List.range 8,PrefixAt 30 (48+i):=by
  decide +kernel

theorem prefix_r30_part7:∀ i ∈ List.range 8,PrefixAt 30 (56+i):=by
  decide +kernel

theorem prefix_r30_part8:∀ i ∈ List.range 8,PrefixAt 30 (64+i):=by
  decide +kernel

theorem prefix_r30_part9:∀ i ∈ List.range 8,PrefixAt 30 (72+i):=by
  decide +kernel

theorem prefix_r30_part10:∀ i ∈ List.range 8,PrefixAt 30 (80+i):=by
  decide +kernel

theorem prefix_r30_part11:∀ i ∈ List.range 8,PrefixAt 30 (88+i):=by
  decide +kernel

theorem prefix_r30_part12:∀ i ∈ List.range 8,PrefixAt 30 (96+i):=by
  decide +kernel

theorem prefix_r30_part13:∀ i ∈ List.range 8,PrefixAt 30 (104+i):=by
  decide +kernel

theorem prefix_r30_part14:∀ i ∈ List.range 1,PrefixAt 30 (112+i):=by
  decide +kernel

theorem prefix_r30:∀ V ∈ List.range 113,PrefixAt 30 V:=by
  intro V hV
  have hv:V < 113:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r30_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r30_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r30_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r30_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r30_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r30_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r30_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r30_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r30_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r30_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r30_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r30_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r30_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            by_cases h13:V < 112
                            · have hi:=prefix_r30_part13 (V-104) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                            ·
                              have hi:=prefix_r30_part14 (V-112) (List.mem_range.mpr (by omega))
                              simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem prefix_r31_part0:∀ i ∈ List.range 8,PrefixAt 31 (0+i):=by
  decide +kernel

theorem prefix_r31_part1:∀ i ∈ List.range 8,PrefixAt 31 (8+i):=by
  decide +kernel

theorem prefix_r31_part2:∀ i ∈ List.range 8,PrefixAt 31 (16+i):=by
  decide +kernel

theorem prefix_r31_part3:∀ i ∈ List.range 8,PrefixAt 31 (24+i):=by
  decide +kernel

theorem prefix_r31_part4:∀ i ∈ List.range 8,PrefixAt 31 (32+i):=by
  decide +kernel

theorem prefix_r31_part5:∀ i ∈ List.range 8,PrefixAt 31 (40+i):=by
  decide +kernel

theorem prefix_r31_part6:∀ i ∈ List.range 8,PrefixAt 31 (48+i):=by
  decide +kernel

theorem prefix_r31_part7:∀ i ∈ List.range 8,PrefixAt 31 (56+i):=by
  decide +kernel

theorem prefix_r31_part8:∀ i ∈ List.range 8,PrefixAt 31 (64+i):=by
  decide +kernel

theorem prefix_r31_part9:∀ i ∈ List.range 8,PrefixAt 31 (72+i):=by
  decide +kernel

theorem prefix_r31_part10:∀ i ∈ List.range 8,PrefixAt 31 (80+i):=by
  decide +kernel

theorem prefix_r31_part11:∀ i ∈ List.range 8,PrefixAt 31 (88+i):=by
  decide +kernel

theorem prefix_r31_part12:∀ i ∈ List.range 8,PrefixAt 31 (96+i):=by
  decide +kernel

theorem prefix_r31_part13:∀ i ∈ List.range 8,PrefixAt 31 (104+i):=by
  decide +kernel

theorem prefix_r31:∀ V ∈ List.range 112,PrefixAt 31 V:=by
  intro V hV
  have hv:V < 112:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=prefix_r31_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=prefix_r31_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=prefix_r31_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=prefix_r31_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=prefix_r31_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=prefix_r31_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=prefix_r31_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=prefix_r31_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=prefix_r31_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=prefix_r31_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=prefix_r31_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=prefix_r31_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=prefix_r31_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            have hi:=prefix_r31_part13 (V-104) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi

theorem prefixReceipt:PrefixReceiptSound:=by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact prefix_r1 V (List.mem_range.mpr (by omega))
    | exact prefix_r2 V (List.mem_range.mpr (by omega))
    | exact prefix_r3 V (List.mem_range.mpr (by omega))
    | exact prefix_r4 V (List.mem_range.mpr (by omega))
    | exact prefix_r5 V (List.mem_range.mpr (by omega))
    | exact prefix_r6 V (List.mem_range.mpr (by omega))
    | exact prefix_r7 V (List.mem_range.mpr (by omega))
    | exact prefix_r8 V (List.mem_range.mpr (by omega))
    | exact prefix_r9 V (List.mem_range.mpr (by omega))
    | exact prefix_r10 V (List.mem_range.mpr (by omega))
    | exact prefix_r11 V (List.mem_range.mpr (by omega))
    | exact prefix_r12 V (List.mem_range.mpr (by omega))
    | exact prefix_r13 V (List.mem_range.mpr (by omega))
    | exact prefix_r14 V (List.mem_range.mpr (by omega))
    | exact prefix_r15 V (List.mem_range.mpr (by omega))
    | exact prefix_r16 V (List.mem_range.mpr (by omega))
    | exact prefix_r17 V (List.mem_range.mpr (by omega))
    | exact prefix_r18 V (List.mem_range.mpr (by omega))
    | exact prefix_r19 V (List.mem_range.mpr (by omega))
    | exact prefix_r20 V (List.mem_range.mpr (by omega))
    | exact prefix_r21 V (List.mem_range.mpr (by omega))
    | exact prefix_r22 V (List.mem_range.mpr (by omega))
    | exact prefix_r23 V (List.mem_range.mpr (by omega))
    | exact prefix_r24 V (List.mem_range.mpr (by omega))
    | exact prefix_r25 V (List.mem_range.mpr (by omega))
    | exact prefix_r26 V (List.mem_range.mpr (by omega))
    | exact prefix_r27 V (List.mem_range.mpr (by omega))
    | exact prefix_r28 V (List.mem_range.mpr (by omega))
    | exact prefix_r29 V (List.mem_range.mpr (by omega))
    | exact prefix_r30 V (List.mem_range.mpr (by omega))
    | exact prefix_r31 V (List.mem_range.mpr (by omega))

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
