import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics
import ProximityPrize.SubmissionLower.BoundaryTailRunsChecked02

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseChecks Lower80801.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

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

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
