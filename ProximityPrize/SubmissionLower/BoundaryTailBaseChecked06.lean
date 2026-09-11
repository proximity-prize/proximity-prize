import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked06Strict05
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br6p0:∀ i ∈ List.range 4,BaseCheckAt 6 (0+i):=by decide +kernel

theorem br6p1:∀ i ∈ List.range 4,BaseCheckAt 6 (4+i):=by decide +kernel

theorem br6p2:∀ i ∈ List.range 4,BaseCheckAt 6 (8+i):=by decide +kernel

theorem br6p3:∀ i ∈ List.range 4,BaseCheckAt 6 (12+i):=by decide +kernel

theorem br6p4:∀ i ∈ List.range 4,BaseCheckAt 6 (16+i):=by decide +kernel

theorem br6p5:∀ i ∈ List.range 4,BaseCheckAt 6 (20+i):=by decide +kernel

theorem br6p6:∀ i ∈ List.range 4,BaseCheckAt 6 (24+i):=by decide +kernel

theorem br6p7:∀ i ∈ List.range 4,BaseCheckAt 6 (28+i):=by decide +kernel

theorem br6p8:∀ i ∈ List.range 4,BaseCheckAt 6 (32+i):=by decide +kernel

theorem br6p9:∀ i ∈ List.range 4,BaseCheckAt 6 (36+i):=by decide +kernel

theorem br6p10:∀ i ∈ List.range 4,BaseCheckAt 6 (40+i):=by decide +kernel

theorem br6p11:∀ i ∈ List.range 4,BaseCheckAt 6 (44+i):=by decide +kernel

theorem br6p12:∀ i ∈ List.range 4,BaseCheckAt 6 (48+i):=by decide +kernel

theorem br6p13:∀ i ∈ List.range 4,BaseCheckAt 6 (52+i):=by decide +kernel

theorem br6p14:∀ i ∈ List.range 4,BaseCheckAt 6 (56+i):=by decide +kernel

theorem br6p15:∀ i ∈ List.range 4,BaseCheckAt 6 (60+i):=by decide +kernel

theorem br6p16:∀ i ∈ List.range 4,BaseCheckAt 6 (64+i):=by decide +kernel

theorem br6p17:∀ i ∈ List.range 4,BaseCheckAt 6 (68+i):=by decide +kernel

theorem br6p18:∀ i ∈ List.range 4,BaseCheckAt 6 (72+i):=by decide +kernel

theorem br6p19:∀ i ∈ List.range 4,BaseCheckAt 6 (76+i):=by decide +kernel

theorem br6p20:∀ i ∈ List.range 4,BaseCheckAt 6 (80+i):=by decide +kernel

theorem br6p21:∀ i ∈ List.range 4,BaseCheckAt 6 (84+i):=by decide +kernel

theorem br6p22:∀ i ∈ List.range 4,BaseCheckAt 6 (88+i):=by decide +kernel

theorem br6p23:∀ i ∈ List.range 4,BaseCheckAt 6 (92+i):=by decide +kernel

theorem br6p24:∀ i ∈ List.range 4,BaseCheckAt 6 (96+i):=by decide +kernel

theorem br6p25:∀ i ∈ List.range 4,BaseCheckAt 6 (100+i):=by decide +kernel

theorem br6p26:∀ i ∈ List.range 4,BaseCheckAt 6 (104+i):=by decide +kernel

theorem br6p27:∀ i ∈ List.range 4,BaseCheckAt 6 (108+i):=by decide +kernel

theorem br6p28:∀ i ∈ List.range 4,BaseCheckAt 6 (112+i):=by decide +kernel

theorem br6p29:∀ i ∈ List.range 4,BaseCheckAt 6 (116+i):=by decide +kernel

theorem br6p30:∀ i ∈ List.range 4,BaseCheckAt 6 (120+i):=by decide +kernel

theorem br6p31:∀ i ∈ List.range 4,BaseCheckAt 6 (124+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br6p32:∀ i ∈ List.range 4,BaseCheckAt 6 (128+i):=by decide +kernel

theorem br6p33:∀ i ∈ List.range 4,BaseCheckAt 6 (132+i):=by decide +kernel

theorem br6p34:∀ i ∈ List.range 1,BaseCheckAt 6 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr6:∀ V ∈ List.range 137,CorrectAt 6 V:=by
  intro V hV
  have hv:V < 137:=List.mem_range.mp hV
  by_cases h0_18:V < 72
  · by_cases h0_9:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have hi:=cr6p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi:=cr6p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h2_4:V < 24
        · have hi:=cr6p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi:=cr6p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h4_9:V < 48
      · by_cases h4_6:V < 40
        · have hi:=cr6p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi:=cr6p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h6_9:V < 56
        · have hi:=cr6p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h7_9:V < 64
          · have hi:=cr6p7 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi:=cr6p8 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h9_18:V < 104
    · by_cases h9_13:V < 88
      · by_cases h9_11:V < 80
        · have hi:=cr6p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi:=cr6p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h11_13:V < 96
        · have hi:=cr6p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi:=cr6p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h13_18:V < 120
      · by_cases h13_15:V < 112
        · have hi:=cr6p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi:=cr6p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h15_18:V < 128
        · have hi:=cr6p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h16_18:V < 136
          · have hi:=cr6p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi:=cr6p17 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zr6:∀ V ∈ List.range 137,ZeroCheckAt 6 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 6 V (by omega) (by omega) (by omega)
theorem sr6:∀ V ∈ List.range 137,StrictCheckAt 6 V:=by
  intro V hV
  have hv:V < 137:=List.mem_range.mp hV
  by_cases h0_137:V < 68
  · by_cases h0_68:V < 34
    · by_cases h0_34:V < 17
      · by_cases h0_17:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have hi:=sr6p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi:=sr6p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4:V < 3
              · have hi:=sr6p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi:=sr6p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have hi:=sr6p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi:=sr6p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8:V < 7
              · have hi:=sr6p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi:=sr6p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have hi:=sr6p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi:=sr6p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12:V < 11
              · have hi:=sr6p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi:=sr6p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17:V < 14
            · by_cases h12_14:V < 13
              · have hi:=sr6p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi:=sr6p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17:V < 15
              · have hi:=sr6p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17:V < 16
                · have hi:=sr6p15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi:=sr6p16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_34:V < 25
        · by_cases h17_25:V < 21
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have hi:=sr6p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi:=sr6p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21:V < 20
              · have hi:=sr6p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi:=sr6p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have hi:=sr6p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi:=sr6p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25:V < 24
              · have hi:=sr6p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi:=sr6p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · by_cases h25_34:V < 29
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have hi:=sr6p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi:=sr6p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29:V < 28
              · have hi:=sr6p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi:=sr6p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
          · by_cases h29_34:V < 31
            · by_cases h29_31:V < 30
              · have hi:=sr6p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi:=sr6p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_34:V < 32
              · have hi:=sr6p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · by_cases h32_34:V < 33
                · have hi:=sr6p32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
                · have hi:=sr6p33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
    · by_cases h34_68:V < 51
      · by_cases h34_51:V < 42
        · by_cases h34_42:V < 38
          · by_cases h34_38:V < 36
            · by_cases h34_36:V < 35
              · have hi:=sr6p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi:=sr6p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38:V < 37
              · have hi:=sr6p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi:=sr6p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have hi:=sr6p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi:=sr6p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42:V < 41
              · have hi:=sr6p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi:=sr6p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
        · by_cases h42_51:V < 46
          · by_cases h42_46:V < 44
            · by_cases h42_44:V < 43
              · have hi:=sr6p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi:=sr6p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46:V < 45
              · have hi:=sr6p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi:=sr6p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_51:V < 48
            · by_cases h46_48:V < 47
              · have hi:=sr6p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi:=sr6p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_51:V < 49
              · have hi:=sr6p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · by_cases h49_51:V < 50
                · have hi:=sr6p49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
                · have hi:=sr6p50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
      · by_cases h51_68:V < 59
        · by_cases h51_59:V < 55
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have hi:=sr6p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi:=sr6p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55:V < 54
              · have hi:=sr6p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi:=sr6p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have hi:=sr6p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi:=sr6p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59:V < 58
              · have hi:=sr6p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi:=sr6p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
        · by_cases h59_68:V < 63
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have hi:=sr6p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi:=sr6p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63:V < 62
              · have hi:=sr6p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi:=sr6p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
          · by_cases h63_68:V < 65
            · by_cases h63_65:V < 64
              · have hi:=sr6p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi:=sr6p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_68:V < 66
              · have hi:=sr6p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · by_cases h66_68:V < 67
                · have hi:=sr6p66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
                · have hi:=sr6p67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
  · by_cases h68_137:V < 102
    · by_cases h68_102:V < 85
      · by_cases h68_85:V < 76
        · by_cases h68_76:V < 72
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have hi:=sr6p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi:=sr6p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72:V < 71
              · have hi:=sr6p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi:=sr6p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have hi:=sr6p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi:=sr6p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76:V < 75
              · have hi:=sr6p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi:=sr6p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
        · by_cases h76_85:V < 80
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have hi:=sr6p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi:=sr6p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80:V < 79
              · have hi:=sr6p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi:=sr6p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
          · by_cases h80_85:V < 82
            · by_cases h80_82:V < 81
              · have hi:=sr6p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi:=sr6p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_85:V < 83
              · have hi:=sr6p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · by_cases h83_85:V < 84
                · have hi:=sr6p83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
                · have hi:=sr6p84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
      · by_cases h85_102:V < 93
        · by_cases h85_93:V < 89
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have hi:=sr6p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi:=sr6p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89:V < 88
              · have hi:=sr6p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi:=sr6p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have hi:=sr6p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi:=sr6p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93:V < 92
              · have hi:=sr6p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi:=sr6p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
        · by_cases h93_102:V < 97
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have hi:=sr6p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi:=sr6p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97:V < 96
              · have hi:=sr6p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi:=sr6p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
          · by_cases h97_102:V < 99
            · by_cases h97_99:V < 98
              · have hi:=sr6p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi:=sr6p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_102:V < 100
              · have hi:=sr6p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · by_cases h100_102:V < 101
                · have hi:=sr6p100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
                · have hi:=sr6p101 (V-101) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
    · by_cases h102_137:V < 119
      · by_cases h102_119:V < 110
        · by_cases h102_110:V < 106
          · by_cases h102_106:V < 104
            · by_cases h102_104:V < 103
              · have hi:=sr6p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi:=sr6p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106:V < 105
              · have hi:=sr6p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi:=sr6p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have hi:=sr6p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi:=sr6p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110:V < 109
              · have hi:=sr6p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi:=sr6p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
        · by_cases h110_119:V < 114
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have hi:=sr6p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi:=sr6p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114:V < 113
              · have hi:=sr6p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi:=sr6p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
          · by_cases h114_119:V < 116
            · by_cases h114_116:V < 115
              · have hi:=sr6p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi:=sr6p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_119:V < 117
              · have hi:=sr6p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · by_cases h117_119:V < 118
                · have hi:=sr6p117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
                · have hi:=sr6p118 (V-118) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
      · by_cases h119_137:V < 128
        · by_cases h119_128:V < 123
          · by_cases h119_123:V < 121
            · by_cases h119_121:V < 120
              · have hi:=sr6p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi:=sr6p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_123:V < 122
              · have hi:=sr6p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi:=sr6p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
          · by_cases h123_128:V < 125
            · by_cases h123_125:V < 124
              · have hi:=sr6p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi:=sr6p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
            · by_cases h125_128:V < 126
              · have hi:=sr6p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · by_cases h126_128:V < 127
                · have hi:=sr6p126 (V-126) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
                · have hi:=sr6p127 (V-127) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
        · by_cases h128_137:V < 132
          · by_cases h128_132:V < 130
            · by_cases h128_130:V < 129
              · have hi:=sr6p128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · have hi:=sr6p129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
            · by_cases h130_132:V < 131
              · have hi:=sr6p130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · have hi:=sr6p131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
          · by_cases h132_137:V < 134
            · by_cases h132_134:V < 133
              · have hi:=sr6p132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · have hi:=sr6p133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
            · by_cases h134_137:V < 135
              · have hi:=sr6p134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
              · by_cases h135_137:V < 136
                · have hi:=sr6p135 (V-135) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
                · have hi:=sr6p136 (V-136) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem br6:∀ V ∈ List.range 137,BaseCheckAt 6 V:=by
  intro V hV
  have hv:V < 137:=List.mem_range.mp hV
  by_cases h0_35:V < 68
  · by_cases h0_17:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have hi:=br6p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
          · have hi:=br6p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
        · by_cases h2_4:V < 12
          · have hi:=br6p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
          · have hi:=br6p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have hi:=br6p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · have hi:=br6p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h6_8:V < 28
          · have hi:=br6p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · have hi:=br6p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
    · by_cases h8_17:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have hi:=br6p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          · have hi:=br6p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
        · by_cases h10_12:V < 44
          · have hi:=br6p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
          · have hi:=br6p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
      · by_cases h12_17:V < 56
        · by_cases h12_14:V < 52
          · have hi:=br6p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
          · have hi:=br6p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
        · by_cases h14_17:V < 60
          · have hi:=br6p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · by_cases h15_17:V < 64
            · have hi:=br6p15 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · have hi:=br6p16 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h17_35:V < 104
    · by_cases h17_26:V < 84
      · by_cases h17_21:V < 76
        · by_cases h17_19:V < 72
          · have hi:=br6p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
          · have hi:=br6p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · by_cases h19_21:V < 80
          · have hi:=br6p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
          · have hi:=br6p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h21_26:V < 92
        · by_cases h21_23:V < 88
          · have hi:=br6p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
          · have hi:=br6p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · by_cases h23_26:V < 96
          · have hi:=br6p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
          · by_cases h24_26:V < 100
            · have hi:=br6p24 (V-96) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · have hi:=br6p25 (V-100) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
    · by_cases h26_35:V < 120
      · by_cases h26_30:V < 112
        · by_cases h26_28:V < 108
          · have hi:=br6p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
          · have hi:=br6p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
        · by_cases h28_30:V < 116
          · have hi:=br6p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
          · have hi:=br6p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
      · by_cases h30_35:V < 128
        · by_cases h30_32:V < 124
          · have hi:=br6p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi:=br6p31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
        · by_cases h32_35:V < 132
          · have hi:=br6p32 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · by_cases h33_35:V < 136
            · have hi:=br6p33 (V-132) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
            · have hi:=br6p34 (V-136) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
