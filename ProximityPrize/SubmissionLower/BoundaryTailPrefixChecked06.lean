import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics
import ProximityPrize.SubmissionLower.BoundaryTailPrefixChecked05

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseChecks Lower80801.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

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

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
