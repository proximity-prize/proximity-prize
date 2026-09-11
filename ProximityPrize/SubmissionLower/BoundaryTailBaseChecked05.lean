import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked05Base02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r5 : ∀ V ∈ List.range 135, CorrectAt 5 V := by
  intro V hV
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_17 : V < 64
  · by_cases h0_8 : V < 32
    · by_cases h0_4 : V < 16
      · by_cases h0_2 : V < 8
        · have hi := correct_r5_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r5_part1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h2_4 : V < 24
        · have hi := correct_r5_part2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r5_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h4_8 : V < 48
      · by_cases h4_6 : V < 40
        · have hi := correct_r5_part4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r5_part5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h6_8 : V < 56
        · have hi := correct_r5_part6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r5_part7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h8_17 : V < 96
    · by_cases h8_12 : V < 80
      · by_cases h8_10 : V < 72
        · have hi := correct_r5_part8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r5_part9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h10_12 : V < 88
        · have hi := correct_r5_part10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r5_part11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h12_17 : V < 112
      · by_cases h12_14 : V < 104
        · have hi := correct_r5_part12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r5_part13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h14_17 : V < 120
        · have hi := correct_r5_part14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h15_17 : V < 128
          · have hi := correct_r5_part15 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r5_part16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zero_r5 : ∀ V ∈ List.range 135, ZeroCheckAt 5 V := by
  intro V hV
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 67
  · by_cases h0_67 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := zero_r5_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := zero_r5_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := zero_r5_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := zero_r5_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := zero_r5_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := zero_r5_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := zero_r5_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := zero_r5_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := zero_r5_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := zero_r5_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := zero_r5_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := zero_r5_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := zero_r5_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := zero_r5_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := zero_r5_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := zero_r5_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := zero_r5_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := zero_r5_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := zero_r5_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := zero_r5_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := zero_r5_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := zero_r5_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := zero_r5_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := zero_r5_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := zero_r5_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := zero_r5_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := zero_r5_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := zero_r5_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := zero_r5_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := zero_r5_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_33 : V < 31
              · have hi := zero_r5_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · by_cases h31_33 : V < 32
                · have hi := zero_r5_part31 (V-31) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
                · have hi := zero_r5_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
    · by_cases h33_67 : V < 50
      · by_cases h33_50 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := zero_r5_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := zero_r5_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := zero_r5_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := zero_r5_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := zero_r5_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := zero_r5_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := zero_r5_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := zero_r5_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · by_cases h41_50 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := zero_r5_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := zero_r5_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := zero_r5_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := zero_r5_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_50 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := zero_r5_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := zero_r5_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_50 : V < 48
              · have hi := zero_r5_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · by_cases h48_50 : V < 49
                · have hi := zero_r5_part48 (V-48) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
                · have hi := zero_r5_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
      · by_cases h50_67 : V < 58
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have hi := zero_r5_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := zero_r5_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
            · by_cases h52_54 : V < 53
              · have hi := zero_r5_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := zero_r5_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have hi := zero_r5_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := zero_r5_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
            · by_cases h56_58 : V < 57
              · have hi := zero_r5_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := zero_r5_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
        · by_cases h58_67 : V < 62
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have hi := zero_r5_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := zero_r5_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
            · by_cases h60_62 : V < 61
              · have hi := zero_r5_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := zero_r5_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
          · by_cases h62_67 : V < 64
            · by_cases h62_64 : V < 63
              · have hi := zero_r5_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := zero_r5_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_67 : V < 65
              · have hi := zero_r5_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · by_cases h65_67 : V < 66
                · have hi := zero_r5_part65 (V-65) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
                · have hi := zero_r5_part66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
  · by_cases h67_135 : V < 101
    · by_cases h67_101 : V < 84
      · by_cases h67_84 : V < 75
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have hi := zero_r5_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := zero_r5_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
            · by_cases h69_71 : V < 70
              · have hi := zero_r5_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := zero_r5_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have hi := zero_r5_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := zero_r5_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := zero_r5_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := zero_r5_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
        · by_cases h75_84 : V < 79
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have hi := zero_r5_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := zero_r5_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79 : V < 78
              · have hi := zero_r5_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := zero_r5_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
          · by_cases h79_84 : V < 81
            · by_cases h79_81 : V < 80
              · have hi := zero_r5_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := zero_r5_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_84 : V < 82
              · have hi := zero_r5_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · by_cases h82_84 : V < 83
                · have hi := zero_r5_part82 (V-82) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
                · have hi := zero_r5_part83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
      · by_cases h84_101 : V < 92
        · by_cases h84_92 : V < 88
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have hi := zero_r5_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := zero_r5_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
            · by_cases h86_88 : V < 87
              · have hi := zero_r5_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := zero_r5_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have hi := zero_r5_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := zero_r5_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92 : V < 91
              · have hi := zero_r5_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := zero_r5_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
        · by_cases h92_101 : V < 96
          · by_cases h92_96 : V < 94
            · by_cases h92_94 : V < 93
              · have hi := zero_r5_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := zero_r5_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_96 : V < 95
              · have hi := zero_r5_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := zero_r5_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
          · by_cases h96_101 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := zero_r5_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := zero_r5_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_101 : V < 99
              · have hi := zero_r5_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · by_cases h99_101 : V < 100
                · have hi := zero_r5_part99 (V-99) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
                · have hi := zero_r5_part100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
    · by_cases h101_135 : V < 118
      · by_cases h101_118 : V < 109
        · by_cases h101_109 : V < 105
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := zero_r5_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := zero_r5_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := zero_r5_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := zero_r5_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := zero_r5_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := zero_r5_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := zero_r5_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := zero_r5_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
        · by_cases h109_118 : V < 113
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := zero_r5_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := zero_r5_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_113 : V < 112
              · have hi := zero_r5_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := zero_r5_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
          · by_cases h113_118 : V < 115
            · by_cases h113_115 : V < 114
              · have hi := zero_r5_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := zero_r5_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
            · by_cases h115_118 : V < 116
              · have hi := zero_r5_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · by_cases h116_118 : V < 117
                · have hi := zero_r5_part116 (V-116) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
                · have hi := zero_r5_part117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
      · by_cases h118_135 : V < 126
        · by_cases h118_126 : V < 122
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have hi := zero_r5_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := zero_r5_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
            · by_cases h120_122 : V < 121
              · have hi := zero_r5_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := zero_r5_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
          · by_cases h122_126 : V < 124
            · by_cases h122_124 : V < 123
              · have hi := zero_r5_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := zero_r5_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
            · by_cases h124_126 : V < 125
              · have hi := zero_r5_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := zero_r5_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
        · by_cases h126_135 : V < 130
          · by_cases h126_130 : V < 128
            · by_cases h126_128 : V < 127
              · have hi := zero_r5_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi := zero_r5_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
            · by_cases h128_130 : V < 129
              · have hi := zero_r5_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · have hi := zero_r5_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
          · by_cases h130_135 : V < 132
            · by_cases h130_132 : V < 131
              · have hi := zero_r5_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · have hi := zero_r5_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
            · by_cases h132_135 : V < 133
              · have hi := zero_r5_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · by_cases h133_135 : V < 134
                · have hi := zero_r5_part133 (V-133) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
                · have hi := zero_r5_part134 (V-134) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi

theorem strict_r5 : ∀ V ∈ List.range 135, StrictCheckAt 5 V := by
  intro V hV
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 67
  · by_cases h0_67 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strict_r5_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strict_r5_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strict_r5_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strict_r5_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strict_r5_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strict_r5_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strict_r5_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strict_r5_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strict_r5_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strict_r5_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strict_r5_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strict_r5_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strict_r5_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strict_r5_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := strict_r5_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := strict_r5_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := strict_r5_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strict_r5_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := strict_r5_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strict_r5_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := strict_r5_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strict_r5_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strict_r5_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strict_r5_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strict_r5_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strict_r5_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strict_r5_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strict_r5_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := strict_r5_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strict_r5_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_33 : V < 31
              · have hi := strict_r5_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · by_cases h31_33 : V < 32
                · have hi := strict_r5_part31 (V-31) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
                · have hi := strict_r5_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
    · by_cases h33_67 : V < 50
      · by_cases h33_50 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := strict_r5_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strict_r5_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := strict_r5_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strict_r5_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := strict_r5_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strict_r5_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := strict_r5_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strict_r5_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · by_cases h41_50 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := strict_r5_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strict_r5_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strict_r5_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strict_r5_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_50 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strict_r5_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strict_r5_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_50 : V < 48
              · have hi := strict_r5_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · by_cases h48_50 : V < 49
                · have hi := strict_r5_part48 (V-48) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
                · have hi := strict_r5_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
      · by_cases h50_67 : V < 58
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have hi := strict_r5_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strict_r5_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
            · by_cases h52_54 : V < 53
              · have hi := strict_r5_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strict_r5_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have hi := strict_r5_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strict_r5_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
            · by_cases h56_58 : V < 57
              · have hi := strict_r5_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strict_r5_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
        · by_cases h58_67 : V < 62
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have hi := strict_r5_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strict_r5_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
            · by_cases h60_62 : V < 61
              · have hi := strict_r5_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strict_r5_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
          · by_cases h62_67 : V < 64
            · by_cases h62_64 : V < 63
              · have hi := strict_r5_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strict_r5_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_67 : V < 65
              · have hi := strict_r5_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · by_cases h65_67 : V < 66
                · have hi := strict_r5_part65 (V-65) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
                · have hi := strict_r5_part66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
  · by_cases h67_135 : V < 101
    · by_cases h67_101 : V < 84
      · by_cases h67_84 : V < 75
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have hi := strict_r5_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strict_r5_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
            · by_cases h69_71 : V < 70
              · have hi := strict_r5_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strict_r5_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have hi := strict_r5_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strict_r5_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := strict_r5_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strict_r5_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
        · by_cases h75_84 : V < 79
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have hi := strict_r5_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strict_r5_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79 : V < 78
              · have hi := strict_r5_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strict_r5_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
          · by_cases h79_84 : V < 81
            · by_cases h79_81 : V < 80
              · have hi := strict_r5_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strict_r5_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_84 : V < 82
              · have hi := strict_r5_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · by_cases h82_84 : V < 83
                · have hi := strict_r5_part82 (V-82) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
                · have hi := strict_r5_part83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
      · by_cases h84_101 : V < 92
        · by_cases h84_92 : V < 88
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have hi := strict_r5_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strict_r5_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
            · by_cases h86_88 : V < 87
              · have hi := strict_r5_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strict_r5_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have hi := strict_r5_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strict_r5_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92 : V < 91
              · have hi := strict_r5_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strict_r5_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
        · by_cases h92_101 : V < 96
          · by_cases h92_96 : V < 94
            · by_cases h92_94 : V < 93
              · have hi := strict_r5_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strict_r5_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_96 : V < 95
              · have hi := strict_r5_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strict_r5_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
          · by_cases h96_101 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := strict_r5_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strict_r5_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_101 : V < 99
              · have hi := strict_r5_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · by_cases h99_101 : V < 100
                · have hi := strict_r5_part99 (V-99) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
                · have hi := strict_r5_part100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
    · by_cases h101_135 : V < 118
      · by_cases h101_118 : V < 109
        · by_cases h101_109 : V < 105
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := strict_r5_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strict_r5_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := strict_r5_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strict_r5_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := strict_r5_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strict_r5_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := strict_r5_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strict_r5_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
        · by_cases h109_118 : V < 113
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := strict_r5_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strict_r5_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_113 : V < 112
              · have hi := strict_r5_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strict_r5_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
          · by_cases h113_118 : V < 115
            · by_cases h113_115 : V < 114
              · have hi := strict_r5_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strict_r5_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
            · by_cases h115_118 : V < 116
              · have hi := strict_r5_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · by_cases h116_118 : V < 117
                · have hi := strict_r5_part116 (V-116) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
                · have hi := strict_r5_part117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
      · by_cases h118_135 : V < 126
        · by_cases h118_126 : V < 122
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have hi := strict_r5_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strict_r5_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
            · by_cases h120_122 : V < 121
              · have hi := strict_r5_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strict_r5_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
          · by_cases h122_126 : V < 124
            · by_cases h122_124 : V < 123
              · have hi := strict_r5_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strict_r5_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
            · by_cases h124_126 : V < 125
              · have hi := strict_r5_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strict_r5_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
        · by_cases h126_135 : V < 130
          · by_cases h126_130 : V < 128
            · by_cases h126_128 : V < 127
              · have hi := strict_r5_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi := strict_r5_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
            · by_cases h128_130 : V < 129
              · have hi := strict_r5_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · have hi := strict_r5_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
          · by_cases h130_135 : V < 132
            · by_cases h130_132 : V < 131
              · have hi := strict_r5_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · have hi := strict_r5_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
            · by_cases h132_135 : V < 133
              · have hi := strict_r5_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · by_cases h133_135 : V < 134
                · have hi := strict_r5_part133 (V-133) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
                · have hi := strict_r5_part134 (V-134) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi

theorem base_r5 : ∀ V ∈ List.range 135, BaseCheckAt 5 V := by
  intro V hV
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_34 : V < 68
  · by_cases h0_17 : V < 32
    · by_cases h0_8 : V < 16
      · by_cases h0_4 : V < 8
        · by_cases h0_2 : V < 4
          · have hi := base_r5_part0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
          · have hi := base_r5_part1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
        · by_cases h2_4 : V < 12
          · have hi := base_r5_part2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
          · have hi := base_r5_part3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
      · by_cases h4_8 : V < 24
        · by_cases h4_6 : V < 20
          · have hi := base_r5_part4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · have hi := base_r5_part5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h6_8 : V < 28
          · have hi := base_r5_part6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · have hi := base_r5_part7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
    · by_cases h8_17 : V < 48
      · by_cases h8_12 : V < 40
        · by_cases h8_10 : V < 36
          · have hi := base_r5_part8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          · have hi := base_r5_part9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
        · by_cases h10_12 : V < 44
          · have hi := base_r5_part10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
          · have hi := base_r5_part11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
      · by_cases h12_17 : V < 56
        · by_cases h12_14 : V < 52
          · have hi := base_r5_part12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
          · have hi := base_r5_part13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
        · by_cases h14_17 : V < 60
          · have hi := base_r5_part14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · by_cases h15_17 : V < 64
            · have hi := base_r5_part15 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · have hi := base_r5_part16 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h17_34 : V < 100
    · by_cases h17_25 : V < 84
      · by_cases h17_21 : V < 76
        · by_cases h17_19 : V < 72
          · have hi := base_r5_part17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
          · have hi := base_r5_part18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · by_cases h19_21 : V < 80
          · have hi := base_r5_part19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
          · have hi := base_r5_part20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h21_25 : V < 92
        · by_cases h21_23 : V < 88
          · have hi := base_r5_part21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
          · have hi := base_r5_part22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · by_cases h23_25 : V < 96
          · have hi := base_r5_part23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
          · have hi := base_r5_part24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h25_34 : V < 116
      · by_cases h25_29 : V < 108
        · by_cases h25_27 : V < 104
          · have hi := base_r5_part25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · have hi := base_r5_part26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · by_cases h27_29 : V < 112
          · have hi := base_r5_part27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · have hi := base_r5_part28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h29_34 : V < 124
        · by_cases h29_31 : V < 120
          · have hi := base_r5_part29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
          · have hi := base_r5_part30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h31_34 : V < 128
          · have hi := base_r5_part31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
          · by_cases h32_34 : V < 132
            · have hi := base_r5_part32 (V-128) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
            · have hi := base_r5_part33 (V-132) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
