import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked01Base02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr1:∀ V ∈ List.range 142,CorrectAt 1 V:=by
  intro V hV
  have hv:V < 142:=List.mem_range.mp hV
  by_cases h0_18:V < 72
  · by_cases h0_9:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have hi:=cr1p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi:=cr1p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h2_4:V < 24
        · have hi:=cr1p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi:=cr1p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h4_9:V < 48
      · by_cases h4_6:V < 40
        · have hi:=cr1p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi:=cr1p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h6_9:V < 56
        · have hi:=cr1p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h7_9:V < 64
          · have hi:=cr1p7 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi:=cr1p8 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h9_18:V < 104
    · by_cases h9_13:V < 88
      · by_cases h9_11:V < 80
        · have hi:=cr1p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi:=cr1p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h11_13:V < 96
        · have hi:=cr1p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi:=cr1p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h13_18:V < 120
      · by_cases h13_15:V < 112
        · have hi:=cr1p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi:=cr1p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h15_18:V < 128
        · have hi:=cr1p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h16_18:V < 136
          · have hi:=cr1p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi:=cr1p17 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zr1:∀ V ∈ List.range 142,ZeroCheckAt 1 V:=by
  intro V hV
  have hv:V < 142:=List.mem_range.mp hV
  by_cases h0_142:V < 71
  · by_cases h0_71:V < 35
    · by_cases h0_35:V < 17
      · by_cases h0_17:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have hi:=zr1p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi:=zr1p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4:V < 3
              · have hi:=zr1p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi:=zr1p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have hi:=zr1p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi:=zr1p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8:V < 7
              · have hi:=zr1p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi:=zr1p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have hi:=zr1p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi:=zr1p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12:V < 11
              · have hi:=zr1p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi:=zr1p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17:V < 14
            · by_cases h12_14:V < 13
              · have hi:=zr1p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi:=zr1p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17:V < 15
              · have hi:=zr1p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17:V < 16
                · have hi:=zr1p15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi:=zr1p16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_35:V < 26
        · by_cases h17_26:V < 21
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have hi:=zr1p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi:=zr1p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21:V < 20
              · have hi:=zr1p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi:=zr1p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_26:V < 23
            · by_cases h21_23:V < 22
              · have hi:=zr1p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi:=zr1p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_26:V < 24
              · have hi:=zr1p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · by_cases h24_26:V < 25
                · have hi:=zr1p24 (V-24) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
                · have hi:=zr1p25 (V-25) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
        · by_cases h26_35:V < 30
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have hi:=zr1p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi:=zr1p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30:V < 29
              · have hi:=zr1p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi:=zr1p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
          · by_cases h30_35:V < 32
            · by_cases h30_32:V < 31
              · have hi:=zr1p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi:=zr1p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
            · by_cases h32_35:V < 33
              · have hi:=zr1p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · by_cases h33_35:V < 34
                · have hi:=zr1p33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
                · have hi:=zr1p34 (V-34) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
    · by_cases h35_71:V < 53
      · by_cases h35_53:V < 44
        · by_cases h35_44:V < 39
          · by_cases h35_39:V < 37
            · by_cases h35_37:V < 36
              · have hi:=zr1p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi:=zr1p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39:V < 38
              · have hi:=zr1p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi:=zr1p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
          · by_cases h39_44:V < 41
            · by_cases h39_41:V < 40
              · have hi:=zr1p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi:=zr1p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_44:V < 42
              · have hi:=zr1p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · by_cases h42_44:V < 43
                · have hi:=zr1p42 (V-42) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
                · have hi:=zr1p43 (V-43) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
        · by_cases h44_53:V < 48
          · by_cases h44_48:V < 46
            · by_cases h44_46:V < 45
              · have hi:=zr1p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi:=zr1p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
            · by_cases h46_48:V < 47
              · have hi:=zr1p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi:=zr1p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
          · by_cases h48_53:V < 50
            · by_cases h48_50:V < 49
              · have hi:=zr1p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi:=zr1p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_53:V < 51
              · have hi:=zr1p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · by_cases h51_53:V < 52
                · have hi:=zr1p51 (V-51) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
                · have hi:=zr1p52 (V-52) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
      · by_cases h53_71:V < 62
        · by_cases h53_62:V < 57
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have hi:=zr1p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi:=zr1p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
            · by_cases h55_57:V < 56
              · have hi:=zr1p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi:=zr1p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · by_cases h57_62:V < 59
            · by_cases h57_59:V < 58
              · have hi:=zr1p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi:=zr1p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
            · by_cases h59_62:V < 60
              · have hi:=zr1p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · by_cases h60_62:V < 61
                · have hi:=zr1p60 (V-60) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
                · have hi:=zr1p61 (V-61) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
        · by_cases h62_71:V < 66
          · by_cases h62_66:V < 64
            · by_cases h62_64:V < 63
              · have hi:=zr1p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi:=zr1p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_66:V < 65
              · have hi:=zr1p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi:=zr1p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
          · by_cases h66_71:V < 68
            · by_cases h66_68:V < 67
              · have hi:=zr1p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi:=zr1p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
            · by_cases h68_71:V < 69
              · have hi:=zr1p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · by_cases h69_71:V < 70
                · have hi:=zr1p69 (V-69) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
                · have hi:=zr1p70 (V-70) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
  · by_cases h71_142:V < 106
    · by_cases h71_106:V < 88
      · by_cases h71_88:V < 79
        · by_cases h71_79:V < 75
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have hi:=zr1p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi:=zr1p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75:V < 74
              · have hi:=zr1p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi:=zr1p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have hi:=zr1p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi:=zr1p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79:V < 78
              · have hi:=zr1p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi:=zr1p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
        · by_cases h79_88:V < 83
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have hi:=zr1p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi:=zr1p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_83:V < 82
              · have hi:=zr1p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi:=zr1p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
          · by_cases h83_88:V < 85
            · by_cases h83_85:V < 84
              · have hi:=zr1p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi:=zr1p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_88:V < 86
              · have hi:=zr1p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · by_cases h86_88:V < 87
                · have hi:=zr1p86 (V-86) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
                · have hi:=zr1p87 (V-87) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
      · by_cases h88_106:V < 97
        · by_cases h88_97:V < 92
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have hi:=zr1p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi:=zr1p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92:V < 91
              · have hi:=zr1p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi:=zr1p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
          · by_cases h92_97:V < 94
            · by_cases h92_94:V < 93
              · have hi:=zr1p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi:=zr1p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_97:V < 95
              · have hi:=zr1p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · by_cases h95_97:V < 96
                · have hi:=zr1p95 (V-95) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
                · have hi:=zr1p96 (V-96) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · by_cases h97_106:V < 101
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have hi:=zr1p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi:=zr1p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101:V < 100
              · have hi:=zr1p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi:=zr1p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · by_cases h101_106:V < 103
            · by_cases h101_103:V < 102
              · have hi:=zr1p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi:=zr1p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_106:V < 104
              · have hi:=zr1p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · by_cases h104_106:V < 105
                · have hi:=zr1p104 (V-104) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                · have hi:=zr1p105 (V-105) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
    · by_cases h106_142:V < 124
      · by_cases h106_124:V < 115
        · by_cases h106_115:V < 110
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have hi:=zr1p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi:=zr1p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110:V < 109
              · have hi:=zr1p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi:=zr1p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
          · by_cases h110_115:V < 112
            · by_cases h110_112:V < 111
              · have hi:=zr1p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi:=zr1p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_115:V < 113
              · have hi:=zr1p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · by_cases h113_115:V < 114
                · have hi:=zr1p113 (V-113) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
                · have hi:=zr1p114 (V-114) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
        · by_cases h115_124:V < 119
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have hi:=zr1p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi:=zr1p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
            · by_cases h117_119:V < 118
              · have hi:=zr1p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi:=zr1p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
          · by_cases h119_124:V < 121
            · by_cases h119_121:V < 120
              · have hi:=zr1p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi:=zr1p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_124:V < 122
              · have hi:=zr1p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · by_cases h122_124:V < 123
                · have hi:=zr1p122 (V-122) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
                · have hi:=zr1p123 (V-123) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
      · by_cases h124_142:V < 133
        · by_cases h124_133:V < 128
          · by_cases h124_128:V < 126
            · by_cases h124_126:V < 125
              · have hi:=zr1p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi:=zr1p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
            · by_cases h126_128:V < 127
              · have hi:=zr1p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi:=zr1p127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
          · by_cases h128_133:V < 130
            · by_cases h128_130:V < 129
              · have hi:=zr1p128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · have hi:=zr1p129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
            · by_cases h130_133:V < 131
              · have hi:=zr1p130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · by_cases h131_133:V < 132
                · have hi:=zr1p131 (V-131) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
                · have hi:=zr1p132 (V-132) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
        · by_cases h133_142:V < 137
          · by_cases h133_137:V < 135
            · by_cases h133_135:V < 134
              · have hi:=zr1p133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
              · have hi:=zr1p134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
            · by_cases h135_137:V < 136
              · have hi:=zr1p135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
              · have hi:=zr1p136 (V-136) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
          · by_cases h137_142:V < 139
            · by_cases h137_139:V < 138
              · have hi:=zr1p137 (V-137) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi
              · have hi:=zr1p138 (V-138) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 138 ≤ V by omega)] using hi
            · by_cases h139_142:V < 140
              · have hi:=zr1p139 (V-139) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 139 ≤ V by omega)] using hi
              · by_cases h140_142:V < 141
                · have hi:=zr1p140 (V-140) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 140 ≤ V by omega)] using hi
                · have hi:=zr1p141 (V-141) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 141 ≤ V by omega)] using hi

theorem sr1:∀ V ∈ List.range 142,StrictCheckAt 1 V:=by
  intro V hV
  have hv:V < 142:=List.mem_range.mp hV
  by_cases h0_142:V < 71
  · by_cases h0_71:V < 35
    · by_cases h0_35:V < 17
      · by_cases h0_17:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have hi:=sr1p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi:=sr1p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4:V < 3
              · have hi:=sr1p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi:=sr1p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have hi:=sr1p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi:=sr1p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8:V < 7
              · have hi:=sr1p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi:=sr1p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have hi:=sr1p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi:=sr1p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12:V < 11
              · have hi:=sr1p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi:=sr1p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17:V < 14
            · by_cases h12_14:V < 13
              · have hi:=sr1p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi:=sr1p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17:V < 15
              · have hi:=sr1p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17:V < 16
                · have hi:=sr1p15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi:=sr1p16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_35:V < 26
        · by_cases h17_26:V < 21
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have hi:=sr1p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi:=sr1p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21:V < 20
              · have hi:=sr1p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi:=sr1p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_26:V < 23
            · by_cases h21_23:V < 22
              · have hi:=sr1p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi:=sr1p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_26:V < 24
              · have hi:=sr1p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · by_cases h24_26:V < 25
                · have hi:=sr1p24 (V-24) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
                · have hi:=sr1p25 (V-25) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
        · by_cases h26_35:V < 30
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have hi:=sr1p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi:=sr1p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30:V < 29
              · have hi:=sr1p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi:=sr1p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
          · by_cases h30_35:V < 32
            · by_cases h30_32:V < 31
              · have hi:=sr1p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi:=sr1p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
            · by_cases h32_35:V < 33
              · have hi:=sr1p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · by_cases h33_35:V < 34
                · have hi:=sr1p33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
                · have hi:=sr1p34 (V-34) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
    · by_cases h35_71:V < 53
      · by_cases h35_53:V < 44
        · by_cases h35_44:V < 39
          · by_cases h35_39:V < 37
            · by_cases h35_37:V < 36
              · have hi:=sr1p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi:=sr1p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39:V < 38
              · have hi:=sr1p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi:=sr1p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
          · by_cases h39_44:V < 41
            · by_cases h39_41:V < 40
              · have hi:=sr1p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi:=sr1p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_44:V < 42
              · have hi:=sr1p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · by_cases h42_44:V < 43
                · have hi:=sr1p42 (V-42) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
                · have hi:=sr1p43 (V-43) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
        · by_cases h44_53:V < 48
          · by_cases h44_48:V < 46
            · by_cases h44_46:V < 45
              · have hi:=sr1p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi:=sr1p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
            · by_cases h46_48:V < 47
              · have hi:=sr1p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi:=sr1p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
          · by_cases h48_53:V < 50
            · by_cases h48_50:V < 49
              · have hi:=sr1p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi:=sr1p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_53:V < 51
              · have hi:=sr1p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · by_cases h51_53:V < 52
                · have hi:=sr1p51 (V-51) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
                · have hi:=sr1p52 (V-52) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
      · by_cases h53_71:V < 62
        · by_cases h53_62:V < 57
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have hi:=sr1p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi:=sr1p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
            · by_cases h55_57:V < 56
              · have hi:=sr1p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi:=sr1p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · by_cases h57_62:V < 59
            · by_cases h57_59:V < 58
              · have hi:=sr1p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi:=sr1p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
            · by_cases h59_62:V < 60
              · have hi:=sr1p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · by_cases h60_62:V < 61
                · have hi:=sr1p60 (V-60) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
                · have hi:=sr1p61 (V-61) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
        · by_cases h62_71:V < 66
          · by_cases h62_66:V < 64
            · by_cases h62_64:V < 63
              · have hi:=sr1p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi:=sr1p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_66:V < 65
              · have hi:=sr1p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi:=sr1p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
          · by_cases h66_71:V < 68
            · by_cases h66_68:V < 67
              · have hi:=sr1p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi:=sr1p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
            · by_cases h68_71:V < 69
              · have hi:=sr1p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · by_cases h69_71:V < 70
                · have hi:=sr1p69 (V-69) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
                · have hi:=sr1p70 (V-70) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
  · by_cases h71_142:V < 106
    · by_cases h71_106:V < 88
      · by_cases h71_88:V < 79
        · by_cases h71_79:V < 75
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have hi:=sr1p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi:=sr1p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75:V < 74
              · have hi:=sr1p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi:=sr1p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have hi:=sr1p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi:=sr1p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79:V < 78
              · have hi:=sr1p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi:=sr1p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
        · by_cases h79_88:V < 83
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have hi:=sr1p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi:=sr1p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_83:V < 82
              · have hi:=sr1p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi:=sr1p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
          · by_cases h83_88:V < 85
            · by_cases h83_85:V < 84
              · have hi:=sr1p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi:=sr1p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_88:V < 86
              · have hi:=sr1p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · by_cases h86_88:V < 87
                · have hi:=sr1p86 (V-86) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
                · have hi:=sr1p87 (V-87) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
      · by_cases h88_106:V < 97
        · by_cases h88_97:V < 92
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have hi:=sr1p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi:=sr1p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92:V < 91
              · have hi:=sr1p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi:=sr1p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
          · by_cases h92_97:V < 94
            · by_cases h92_94:V < 93
              · have hi:=sr1p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi:=sr1p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_97:V < 95
              · have hi:=sr1p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · by_cases h95_97:V < 96
                · have hi:=sr1p95 (V-95) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
                · have hi:=sr1p96 (V-96) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · by_cases h97_106:V < 101
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have hi:=sr1p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi:=sr1p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101:V < 100
              · have hi:=sr1p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi:=sr1p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · by_cases h101_106:V < 103
            · by_cases h101_103:V < 102
              · have hi:=sr1p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi:=sr1p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_106:V < 104
              · have hi:=sr1p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · by_cases h104_106:V < 105
                · have hi:=sr1p104 (V-104) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                · have hi:=sr1p105 (V-105) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
    · by_cases h106_142:V < 124
      · by_cases h106_124:V < 115
        · by_cases h106_115:V < 110
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have hi:=sr1p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi:=sr1p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110:V < 109
              · have hi:=sr1p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi:=sr1p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
          · by_cases h110_115:V < 112
            · by_cases h110_112:V < 111
              · have hi:=sr1p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi:=sr1p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_115:V < 113
              · have hi:=sr1p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · by_cases h113_115:V < 114
                · have hi:=sr1p113 (V-113) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
                · have hi:=sr1p114 (V-114) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
        · by_cases h115_124:V < 119
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have hi:=sr1p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi:=sr1p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
            · by_cases h117_119:V < 118
              · have hi:=sr1p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi:=sr1p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
          · by_cases h119_124:V < 121
            · by_cases h119_121:V < 120
              · have hi:=sr1p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi:=sr1p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_124:V < 122
              · have hi:=sr1p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · by_cases h122_124:V < 123
                · have hi:=sr1p122 (V-122) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
                · have hi:=sr1p123 (V-123) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
      · by_cases h124_142:V < 133
        · by_cases h124_133:V < 128
          · by_cases h124_128:V < 126
            · by_cases h124_126:V < 125
              · have hi:=sr1p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi:=sr1p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
            · by_cases h126_128:V < 127
              · have hi:=sr1p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi:=sr1p127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
          · by_cases h128_133:V < 130
            · by_cases h128_130:V < 129
              · have hi:=sr1p128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · have hi:=sr1p129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
            · by_cases h130_133:V < 131
              · have hi:=sr1p130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · by_cases h131_133:V < 132
                · have hi:=sr1p131 (V-131) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
                · have hi:=sr1p132 (V-132) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
        · by_cases h133_142:V < 137
          · by_cases h133_137:V < 135
            · by_cases h133_135:V < 134
              · have hi:=sr1p133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
              · have hi:=sr1p134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
            · by_cases h135_137:V < 136
              · have hi:=sr1p135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
              · have hi:=sr1p136 (V-136) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
          · by_cases h137_142:V < 139
            · by_cases h137_139:V < 138
              · have hi:=sr1p137 (V-137) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi
              · have hi:=sr1p138 (V-138) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 138 ≤ V by omega)] using hi
            · by_cases h139_142:V < 140
              · have hi:=sr1p139 (V-139) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 139 ≤ V by omega)] using hi
              · by_cases h140_142:V < 141
                · have hi:=sr1p140 (V-140) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 140 ≤ V by omega)] using hi
                · have hi:=sr1p141 (V-141) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 141 ≤ V by omega)] using hi

theorem br1:∀ V ∈ List.range 142,BaseCheckAt 1 V:=by
  intro V hV
  have hv:V < 142:=List.mem_range.mp hV
  by_cases h0_36:V < 72
  · by_cases h0_18:V < 36
    · by_cases h0_9:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have hi:=br1p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
          · have hi:=br1p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
        · by_cases h2_4:V < 12
          · have hi:=br1p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
          · have hi:=br1p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
      · by_cases h4_9:V < 24
        · by_cases h4_6:V < 20
          · have hi:=br1p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · have hi:=br1p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h6_9:V < 28
          · have hi:=br1p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · by_cases h7_9:V < 32
            · have hi:=br1p7 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · have hi:=br1p8 (V-32) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
    · by_cases h9_18:V < 52
      · by_cases h9_13:V < 44
        · by_cases h9_11:V < 40
          · have hi:=br1p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
          · have hi:=br1p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · by_cases h11_13:V < 48
          · have hi:=br1p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · have hi:=br1p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
      · by_cases h13_18:V < 60
        · by_cases h13_15:V < 56
          · have hi:=br1p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
          · have hi:=br1p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · by_cases h15_18:V < 64
          · have hi:=br1p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
          · by_cases h16_18:V < 68
            · have hi:=br1p16 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · have hi:=br1p17 (V-68) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
  · by_cases h18_36:V < 108
    · by_cases h18_27:V < 88
      · by_cases h18_22:V < 80
        · by_cases h18_20:V < 76
          · have hi:=br1p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · have hi:=br1p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
        · by_cases h20_22:V < 84
          · have hi:=br1p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
          · have hi:=br1p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
      · by_cases h22_27:V < 96
        · by_cases h22_24:V < 92
          · have hi:=br1p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · have hi:=br1p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
        · by_cases h24_27:V < 100
          · have hi:=br1p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
          · by_cases h25_27:V < 104
            · have hi:=br1p25 (V-100) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · have hi:=br1p26 (V-104) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
    · by_cases h27_36:V < 124
      · by_cases h27_31:V < 116
        · by_cases h27_29:V < 112
          · have hi:=br1p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · have hi:=br1p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h29_31:V < 120
          · have hi:=br1p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
          · have hi:=br1p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
      · by_cases h31_36:V < 132
        · by_cases h31_33:V < 128
          · have hi:=br1p31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
          · have hi:=br1p32 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
        · by_cases h33_36:V < 136
          · have hi:=br1p33 (V-132) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
          · by_cases h34_36:V < 140
            · have hi:=br1p34 (V-136) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
            · have hi:=br1p35 (V-140) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 140 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
