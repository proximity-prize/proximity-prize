import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked04Base02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r4 : ∀ V ∈ List.range 136, CorrectAt 4 V := by
  intro V hV
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_17 : V < 64
  · by_cases h0_8 : V < 32
    · by_cases h0_4 : V < 16
      · by_cases h0_2 : V < 8
        · have hi := correct_r4_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r4_part1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h2_4 : V < 24
        · have hi := correct_r4_part2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r4_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h4_8 : V < 48
      · by_cases h4_6 : V < 40
        · have hi := correct_r4_part4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r4_part5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h6_8 : V < 56
        · have hi := correct_r4_part6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r4_part7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h8_17 : V < 96
    · by_cases h8_12 : V < 80
      · by_cases h8_10 : V < 72
        · have hi := correct_r4_part8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r4_part9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h10_12 : V < 88
        · have hi := correct_r4_part10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r4_part11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h12_17 : V < 112
      · by_cases h12_14 : V < 104
        · have hi := correct_r4_part12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r4_part13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h14_17 : V < 120
        · have hi := correct_r4_part14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h15_17 : V < 128
          · have hi := correct_r4_part15 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r4_part16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zero_r4 : ∀ V ∈ List.range 136, ZeroCheckAt 4 V := by
  intro V hV
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 68
  · by_cases h0_68 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := zero_r4_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := zero_r4_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := zero_r4_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := zero_r4_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := zero_r4_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := zero_r4_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := zero_r4_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := zero_r4_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := zero_r4_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := zero_r4_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := zero_r4_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := zero_r4_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := zero_r4_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := zero_r4_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := zero_r4_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := zero_r4_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := zero_r4_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := zero_r4_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := zero_r4_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := zero_r4_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := zero_r4_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := zero_r4_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := zero_r4_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := zero_r4_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := zero_r4_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := zero_r4_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := zero_r4_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := zero_r4_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := zero_r4_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have hi := zero_r4_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := zero_r4_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_34 : V < 32
              · have hi := zero_r4_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · by_cases h32_34 : V < 33
                · have hi := zero_r4_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
                · have hi := zero_r4_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
    · by_cases h34_68 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := zero_r4_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := zero_r4_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := zero_r4_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := zero_r4_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := zero_r4_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := zero_r4_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := zero_r4_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := zero_r4_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := zero_r4_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := zero_r4_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := zero_r4_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := zero_r4_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := zero_r4_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := zero_r4_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_51 : V < 49
              · have hi := zero_r4_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · by_cases h49_51 : V < 50
                · have hi := zero_r4_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
                · have hi := zero_r4_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
      · by_cases h51_68 : V < 59
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := zero_r4_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := zero_r4_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := zero_r4_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := zero_r4_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := zero_r4_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := zero_r4_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := zero_r4_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := zero_r4_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
        · by_cases h59_68 : V < 63
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have hi := zero_r4_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := zero_r4_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := zero_r4_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := zero_r4_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
          · by_cases h63_68 : V < 65
            · by_cases h63_65 : V < 64
              · have hi := zero_r4_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := zero_r4_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_68 : V < 66
              · have hi := zero_r4_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · by_cases h66_68 : V < 67
                · have hi := zero_r4_part66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
                · have hi := zero_r4_part67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
  · by_cases h68_136 : V < 102
    · by_cases h68_102 : V < 85
      · by_cases h68_85 : V < 76
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := zero_r4_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := zero_r4_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := zero_r4_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := zero_r4_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have hi := zero_r4_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := zero_r4_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76 : V < 75
              · have hi := zero_r4_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := zero_r4_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
        · by_cases h76_85 : V < 80
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have hi := zero_r4_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := zero_r4_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := zero_r4_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := zero_r4_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
          · by_cases h80_85 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := zero_r4_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := zero_r4_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_85 : V < 83
              · have hi := zero_r4_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · by_cases h83_85 : V < 84
                · have hi := zero_r4_part83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
                · have hi := zero_r4_part84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
      · by_cases h85_102 : V < 93
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have hi := zero_r4_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := zero_r4_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := zero_r4_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := zero_r4_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have hi := zero_r4_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := zero_r4_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := zero_r4_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := zero_r4_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
        · by_cases h93_102 : V < 97
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have hi := zero_r4_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := zero_r4_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97 : V < 96
              · have hi := zero_r4_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := zero_r4_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
          · by_cases h97_102 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := zero_r4_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := zero_r4_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_102 : V < 100
              · have hi := zero_r4_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · by_cases h100_102 : V < 101
                · have hi := zero_r4_part100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
                · have hi := zero_r4_part101 (V-101) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
    · by_cases h102_136 : V < 119
      · by_cases h102_119 : V < 110
        · by_cases h102_110 : V < 106
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have hi := zero_r4_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := zero_r4_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106 : V < 105
              · have hi := zero_r4_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := zero_r4_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := zero_r4_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := zero_r4_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := zero_r4_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := zero_r4_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
        · by_cases h110_119 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := zero_r4_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := zero_r4_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114 : V < 113
              · have hi := zero_r4_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := zero_r4_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
          · by_cases h114_119 : V < 116
            · by_cases h114_116 : V < 115
              · have hi := zero_r4_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := zero_r4_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_119 : V < 117
              · have hi := zero_r4_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · by_cases h117_119 : V < 118
                · have hi := zero_r4_part117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
                · have hi := zero_r4_part118 (V-118) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
      · by_cases h119_136 : V < 127
        · by_cases h119_127 : V < 123
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have hi := zero_r4_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := zero_r4_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_123 : V < 122
              · have hi := zero_r4_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := zero_r4_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
          · by_cases h123_127 : V < 125
            · by_cases h123_125 : V < 124
              · have hi := zero_r4_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := zero_r4_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
            · by_cases h125_127 : V < 126
              · have hi := zero_r4_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := zero_r4_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
        · by_cases h127_136 : V < 131
          · by_cases h127_131 : V < 129
            · by_cases h127_129 : V < 128
              · have hi := zero_r4_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · have hi := zero_r4_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
            · by_cases h129_131 : V < 130
              · have hi := zero_r4_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
              · have hi := zero_r4_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
          · by_cases h131_136 : V < 133
            · by_cases h131_133 : V < 132
              · have hi := zero_r4_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
              · have hi := zero_r4_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
            · by_cases h133_136 : V < 134
              · have hi := zero_r4_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
              · by_cases h134_136 : V < 135
                · have hi := zero_r4_part134 (V-134) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
                · have hi := zero_r4_part135 (V-135) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi

theorem strict_r4 : ∀ V ∈ List.range 136, StrictCheckAt 4 V := by
  intro V hV
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 68
  · by_cases h0_68 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strict_r4_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strict_r4_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strict_r4_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strict_r4_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strict_r4_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strict_r4_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strict_r4_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strict_r4_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strict_r4_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strict_r4_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strict_r4_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strict_r4_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strict_r4_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strict_r4_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := strict_r4_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := strict_r4_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := strict_r4_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strict_r4_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strict_r4_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strict_r4_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strict_r4_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strict_r4_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strict_r4_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strict_r4_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strict_r4_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strict_r4_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strict_r4_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strict_r4_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strict_r4_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have hi := strict_r4_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strict_r4_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_34 : V < 32
              · have hi := strict_r4_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · by_cases h32_34 : V < 33
                · have hi := strict_r4_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
                · have hi := strict_r4_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
    · by_cases h34_68 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := strict_r4_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strict_r4_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strict_r4_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strict_r4_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strict_r4_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strict_r4_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strict_r4_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strict_r4_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := strict_r4_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strict_r4_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strict_r4_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strict_r4_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strict_r4_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strict_r4_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_51 : V < 49
              · have hi := strict_r4_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · by_cases h49_51 : V < 50
                · have hi := strict_r4_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
                · have hi := strict_r4_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
      · by_cases h51_68 : V < 59
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strict_r4_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strict_r4_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strict_r4_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strict_r4_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strict_r4_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strict_r4_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := strict_r4_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strict_r4_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
        · by_cases h59_68 : V < 63
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have hi := strict_r4_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strict_r4_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := strict_r4_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strict_r4_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
          · by_cases h63_68 : V < 65
            · by_cases h63_65 : V < 64
              · have hi := strict_r4_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strict_r4_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_68 : V < 66
              · have hi := strict_r4_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · by_cases h66_68 : V < 67
                · have hi := strict_r4_part66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
                · have hi := strict_r4_part67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
  · by_cases h68_136 : V < 102
    · by_cases h68_102 : V < 85
      · by_cases h68_85 : V < 76
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := strict_r4_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strict_r4_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := strict_r4_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strict_r4_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have hi := strict_r4_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strict_r4_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76 : V < 75
              · have hi := strict_r4_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strict_r4_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
        · by_cases h76_85 : V < 80
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have hi := strict_r4_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strict_r4_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := strict_r4_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strict_r4_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
          · by_cases h80_85 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := strict_r4_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strict_r4_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_85 : V < 83
              · have hi := strict_r4_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · by_cases h83_85 : V < 84
                · have hi := strict_r4_part83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
                · have hi := strict_r4_part84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
      · by_cases h85_102 : V < 93
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have hi := strict_r4_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strict_r4_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := strict_r4_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strict_r4_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have hi := strict_r4_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strict_r4_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strict_r4_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strict_r4_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
        · by_cases h93_102 : V < 97
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have hi := strict_r4_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strict_r4_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97 : V < 96
              · have hi := strict_r4_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strict_r4_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
          · by_cases h97_102 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := strict_r4_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strict_r4_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_102 : V < 100
              · have hi := strict_r4_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · by_cases h100_102 : V < 101
                · have hi := strict_r4_part100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
                · have hi := strict_r4_part101 (V-101) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
    · by_cases h102_136 : V < 119
      · by_cases h102_119 : V < 110
        · by_cases h102_110 : V < 106
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have hi := strict_r4_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strict_r4_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106 : V < 105
              · have hi := strict_r4_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strict_r4_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := strict_r4_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strict_r4_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := strict_r4_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strict_r4_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
        · by_cases h110_119 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := strict_r4_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strict_r4_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114 : V < 113
              · have hi := strict_r4_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strict_r4_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
          · by_cases h114_119 : V < 116
            · by_cases h114_116 : V < 115
              · have hi := strict_r4_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strict_r4_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_119 : V < 117
              · have hi := strict_r4_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · by_cases h117_119 : V < 118
                · have hi := strict_r4_part117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
                · have hi := strict_r4_part118 (V-118) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
      · by_cases h119_136 : V < 127
        · by_cases h119_127 : V < 123
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have hi := strict_r4_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strict_r4_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_123 : V < 122
              · have hi := strict_r4_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strict_r4_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
          · by_cases h123_127 : V < 125
            · by_cases h123_125 : V < 124
              · have hi := strict_r4_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strict_r4_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
            · by_cases h125_127 : V < 126
              · have hi := strict_r4_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := strict_r4_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
        · by_cases h127_136 : V < 131
          · by_cases h127_131 : V < 129
            · by_cases h127_129 : V < 128
              · have hi := strict_r4_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · have hi := strict_r4_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
            · by_cases h129_131 : V < 130
              · have hi := strict_r4_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
              · have hi := strict_r4_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
          · by_cases h131_136 : V < 133
            · by_cases h131_133 : V < 132
              · have hi := strict_r4_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
              · have hi := strict_r4_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
            · by_cases h133_136 : V < 134
              · have hi := strict_r4_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
              · by_cases h134_136 : V < 135
                · have hi := strict_r4_part134 (V-134) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
                · have hi := strict_r4_part135 (V-135) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi

theorem base_r4 : ∀ V ∈ List.range 136, BaseCheckAt 4 V := by
  intro V hV
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_34 : V < 68
  · by_cases h0_17 : V < 32
    · by_cases h0_8 : V < 16
      · by_cases h0_4 : V < 8
        · by_cases h0_2 : V < 4
          · have hi := base_r4_part0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
          · have hi := base_r4_part1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
        · by_cases h2_4 : V < 12
          · have hi := base_r4_part2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
          · have hi := base_r4_part3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
      · by_cases h4_8 : V < 24
        · by_cases h4_6 : V < 20
          · have hi := base_r4_part4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · have hi := base_r4_part5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h6_8 : V < 28
          · have hi := base_r4_part6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · have hi := base_r4_part7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
    · by_cases h8_17 : V < 48
      · by_cases h8_12 : V < 40
        · by_cases h8_10 : V < 36
          · have hi := base_r4_part8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          · have hi := base_r4_part9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
        · by_cases h10_12 : V < 44
          · have hi := base_r4_part10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
          · have hi := base_r4_part11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
      · by_cases h12_17 : V < 56
        · by_cases h12_14 : V < 52
          · have hi := base_r4_part12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
          · have hi := base_r4_part13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
        · by_cases h14_17 : V < 60
          · have hi := base_r4_part14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · by_cases h15_17 : V < 64
            · have hi := base_r4_part15 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · have hi := base_r4_part16 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h17_34 : V < 100
    · by_cases h17_25 : V < 84
      · by_cases h17_21 : V < 76
        · by_cases h17_19 : V < 72
          · have hi := base_r4_part17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
          · have hi := base_r4_part18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · by_cases h19_21 : V < 80
          · have hi := base_r4_part19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
          · have hi := base_r4_part20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h21_25 : V < 92
        · by_cases h21_23 : V < 88
          · have hi := base_r4_part21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
          · have hi := base_r4_part22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · by_cases h23_25 : V < 96
          · have hi := base_r4_part23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
          · have hi := base_r4_part24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h25_34 : V < 116
      · by_cases h25_29 : V < 108
        · by_cases h25_27 : V < 104
          · have hi := base_r4_part25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · have hi := base_r4_part26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · by_cases h27_29 : V < 112
          · have hi := base_r4_part27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · have hi := base_r4_part28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h29_34 : V < 124
        · by_cases h29_31 : V < 120
          · have hi := base_r4_part29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
          · have hi := base_r4_part30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h31_34 : V < 128
          · have hi := base_r4_part31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
          · by_cases h32_34 : V < 132
            · have hi := base_r4_part32 (V-128) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
            · have hi := base_r4_part33 (V-132) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
