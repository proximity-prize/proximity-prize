import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked02Strict05
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br2p0:∀ i ∈ List.range 4,BaseCheckAt 2 (0+i):=by decide +kernel

theorem br2p1:∀ i ∈ List.range 4,BaseCheckAt 2 (4+i):=by decide +kernel

theorem br2p2:∀ i ∈ List.range 4,BaseCheckAt 2 (8+i):=by decide +kernel

theorem br2p3:∀ i ∈ List.range 4,BaseCheckAt 2 (12+i):=by decide +kernel

theorem br2p4:∀ i ∈ List.range 4,BaseCheckAt 2 (16+i):=by decide +kernel

theorem br2p5:∀ i ∈ List.range 4,BaseCheckAt 2 (20+i):=by decide +kernel

theorem br2p6:∀ i ∈ List.range 4,BaseCheckAt 2 (24+i):=by decide +kernel

theorem br2p7:∀ i ∈ List.range 4,BaseCheckAt 2 (28+i):=by decide +kernel

theorem br2p8:∀ i ∈ List.range 4,BaseCheckAt 2 (32+i):=by decide +kernel

theorem br2p9:∀ i ∈ List.range 4,BaseCheckAt 2 (36+i):=by decide +kernel

theorem br2p10:∀ i ∈ List.range 4,BaseCheckAt 2 (40+i):=by decide +kernel

theorem br2p11:∀ i ∈ List.range 4,BaseCheckAt 2 (44+i):=by decide +kernel

theorem br2p12:∀ i ∈ List.range 4,BaseCheckAt 2 (48+i):=by decide +kernel

theorem br2p13:∀ i ∈ List.range 4,BaseCheckAt 2 (52+i):=by decide +kernel

theorem br2p14:∀ i ∈ List.range 4,BaseCheckAt 2 (56+i):=by decide +kernel

theorem br2p15:∀ i ∈ List.range 4,BaseCheckAt 2 (60+i):=by decide +kernel

theorem br2p16:∀ i ∈ List.range 4,BaseCheckAt 2 (64+i):=by decide +kernel

theorem br2p17:∀ i ∈ List.range 4,BaseCheckAt 2 (68+i):=by decide +kernel

theorem br2p18:∀ i ∈ List.range 4,BaseCheckAt 2 (72+i):=by decide +kernel

theorem br2p19:∀ i ∈ List.range 4,BaseCheckAt 2 (76+i):=by decide +kernel

theorem br2p20:∀ i ∈ List.range 4,BaseCheckAt 2 (80+i):=by decide +kernel

theorem br2p21:∀ i ∈ List.range 4,BaseCheckAt 2 (84+i):=by decide +kernel

theorem br2p22:∀ i ∈ List.range 4,BaseCheckAt 2 (88+i):=by decide +kernel

theorem br2p23:∀ i ∈ List.range 4,BaseCheckAt 2 (92+i):=by decide +kernel

theorem br2p24:∀ i ∈ List.range 4,BaseCheckAt 2 (96+i):=by decide +kernel

theorem br2p25:∀ i ∈ List.range 4,BaseCheckAt 2 (100+i):=by decide +kernel

theorem br2p26:∀ i ∈ List.range 4,BaseCheckAt 2 (104+i):=by decide +kernel

theorem br2p27:∀ i ∈ List.range 4,BaseCheckAt 2 (108+i):=by decide +kernel

theorem br2p28:∀ i ∈ List.range 4,BaseCheckAt 2 (112+i):=by decide +kernel

theorem br2p29:∀ i ∈ List.range 4,BaseCheckAt 2 (116+i):=by decide +kernel

theorem br2p30:∀ i ∈ List.range 4,BaseCheckAt 2 (120+i):=by decide +kernel

theorem br2p31:∀ i ∈ List.range 4,BaseCheckAt 2 (124+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br2p32:∀ i ∈ List.range 4,BaseCheckAt 2 (128+i):=by decide +kernel

theorem br2p33:∀ i ∈ List.range 4,BaseCheckAt 2 (132+i):=by decide +kernel

theorem br2p34:∀ i ∈ List.range 4,BaseCheckAt 2 (136+i):=by decide +kernel

theorem br2p35:∀ i ∈ List.range 1,BaseCheckAt 2 (140+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr2:∀ V ∈ List.range 141,CorrectAt 2 V:=by
  intro V hV
  have hv:V < 141:=List.mem_range.mp hV
  by_cases h0_18:V < 72
  · by_cases h0_9:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have hi:=cr2p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi:=cr2p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h2_4:V < 24
        · have hi:=cr2p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi:=cr2p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h4_9:V < 48
      · by_cases h4_6:V < 40
        · have hi:=cr2p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi:=cr2p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h6_9:V < 56
        · have hi:=cr2p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h7_9:V < 64
          · have hi:=cr2p7 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi:=cr2p8 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h9_18:V < 104
    · by_cases h9_13:V < 88
      · by_cases h9_11:V < 80
        · have hi:=cr2p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi:=cr2p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h11_13:V < 96
        · have hi:=cr2p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi:=cr2p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h13_18:V < 120
      · by_cases h13_15:V < 112
        · have hi:=cr2p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi:=cr2p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h15_18:V < 128
        · have hi:=cr2p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h16_18:V < 136
          · have hi:=cr2p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi:=cr2p17 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zr2:∀ V ∈ List.range 141,ZeroCheckAt 2 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 2 V (by omega) (by omega) (by omega)
theorem sr2:∀ V ∈ List.range 141,StrictCheckAt 2 V:=by
  intro V hV
  have hv:V < 141:=List.mem_range.mp hV
  by_cases h0_141:V < 70
  · by_cases h0_70:V < 35
    · by_cases h0_35:V < 17
      · by_cases h0_17:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have hi:=sr2p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi:=sr2p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4:V < 3
              · have hi:=sr2p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi:=sr2p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have hi:=sr2p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi:=sr2p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8:V < 7
              · have hi:=sr2p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi:=sr2p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have hi:=sr2p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi:=sr2p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12:V < 11
              · have hi:=sr2p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi:=sr2p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17:V < 14
            · by_cases h12_14:V < 13
              · have hi:=sr2p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi:=sr2p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17:V < 15
              · have hi:=sr2p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17:V < 16
                · have hi:=sr2p15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi:=sr2p16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_35:V < 26
        · by_cases h17_26:V < 21
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have hi:=sr2p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi:=sr2p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21:V < 20
              · have hi:=sr2p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi:=sr2p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_26:V < 23
            · by_cases h21_23:V < 22
              · have hi:=sr2p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi:=sr2p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_26:V < 24
              · have hi:=sr2p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · by_cases h24_26:V < 25
                · have hi:=sr2p24 (V-24) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
                · have hi:=sr2p25 (V-25) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
        · by_cases h26_35:V < 30
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have hi:=sr2p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi:=sr2p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30:V < 29
              · have hi:=sr2p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi:=sr2p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
          · by_cases h30_35:V < 32
            · by_cases h30_32:V < 31
              · have hi:=sr2p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi:=sr2p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
            · by_cases h32_35:V < 33
              · have hi:=sr2p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · by_cases h33_35:V < 34
                · have hi:=sr2p33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
                · have hi:=sr2p34 (V-34) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
    · by_cases h35_70:V < 52
      · by_cases h35_52:V < 43
        · by_cases h35_43:V < 39
          · by_cases h35_39:V < 37
            · by_cases h35_37:V < 36
              · have hi:=sr2p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi:=sr2p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39:V < 38
              · have hi:=sr2p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi:=sr2p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
          · by_cases h39_43:V < 41
            · by_cases h39_41:V < 40
              · have hi:=sr2p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi:=sr2p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_43:V < 42
              · have hi:=sr2p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi:=sr2p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
        · by_cases h43_52:V < 47
          · by_cases h43_47:V < 45
            · by_cases h43_45:V < 44
              · have hi:=sr2p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi:=sr2p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
            · by_cases h45_47:V < 46
              · have hi:=sr2p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi:=sr2p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
          · by_cases h47_52:V < 49
            · by_cases h47_49:V < 48
              · have hi:=sr2p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi:=sr2p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
            · by_cases h49_52:V < 50
              · have hi:=sr2p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · by_cases h50_52:V < 51
                · have hi:=sr2p50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
                · have hi:=sr2p51 (V-51) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
      · by_cases h52_70:V < 61
        · by_cases h52_61:V < 56
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have hi:=sr2p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi:=sr2p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56:V < 55
              · have hi:=sr2p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi:=sr2p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
          · by_cases h56_61:V < 58
            · by_cases h56_58:V < 57
              · have hi:=sr2p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi:=sr2p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_61:V < 59
              · have hi:=sr2p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · by_cases h59_61:V < 60
                · have hi:=sr2p59 (V-59) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
                · have hi:=sr2p60 (V-60) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
        · by_cases h61_70:V < 65
          · by_cases h61_65:V < 63
            · by_cases h61_63:V < 62
              · have hi:=sr2p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi:=sr2p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
            · by_cases h63_65:V < 64
              · have hi:=sr2p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi:=sr2p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
          · by_cases h65_70:V < 67
            · by_cases h65_67:V < 66
              · have hi:=sr2p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi:=sr2p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
            · by_cases h67_70:V < 68
              · have hi:=sr2p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · by_cases h68_70:V < 69
                · have hi:=sr2p68 (V-68) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
                · have hi:=sr2p69 (V-69) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
  · by_cases h70_141:V < 105
    · by_cases h70_105:V < 87
      · by_cases h70_87:V < 78
        · by_cases h70_78:V < 74
          · by_cases h70_74:V < 72
            · by_cases h70_72:V < 71
              · have hi:=sr2p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi:=sr2p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
            · by_cases h72_74:V < 73
              · have hi:=sr2p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi:=sr2p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have hi:=sr2p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi:=sr2p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78:V < 77
              · have hi:=sr2p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi:=sr2p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
        · by_cases h78_87:V < 82
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have hi:=sr2p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi:=sr2p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
            · by_cases h80_82:V < 81
              · have hi:=sr2p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi:=sr2p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
          · by_cases h82_87:V < 84
            · by_cases h82_84:V < 83
              · have hi:=sr2p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi:=sr2p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
            · by_cases h84_87:V < 85
              · have hi:=sr2p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · by_cases h85_87:V < 86
                · have hi:=sr2p85 (V-85) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
                · have hi:=sr2p86 (V-86) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
      · by_cases h87_105:V < 96
        · by_cases h87_96:V < 91
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have hi:=sr2p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi:=sr2p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
            · by_cases h89_91:V < 90
              · have hi:=sr2p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi:=sr2p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
          · by_cases h91_96:V < 93
            · by_cases h91_93:V < 92
              · have hi:=sr2p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi:=sr2p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
            · by_cases h93_96:V < 94
              · have hi:=sr2p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · by_cases h94_96:V < 95
                · have hi:=sr2p94 (V-94) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
                · have hi:=sr2p95 (V-95) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
        · by_cases h96_105:V < 100
          · by_cases h96_100:V < 98
            · by_cases h96_98:V < 97
              · have hi:=sr2p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi:=sr2p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_100:V < 99
              · have hi:=sr2p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi:=sr2p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
          · by_cases h100_105:V < 102
            · by_cases h100_102:V < 101
              · have hi:=sr2p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi:=sr2p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
            · by_cases h102_105:V < 103
              · have hi:=sr2p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · by_cases h103_105:V < 104
                · have hi:=sr2p103 (V-103) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
                · have hi:=sr2p104 (V-104) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
    · by_cases h105_141:V < 123
      · by_cases h105_123:V < 114
        · by_cases h105_114:V < 109
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have hi:=sr2p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi:=sr2p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109:V < 108
              · have hi:=sr2p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi:=sr2p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · by_cases h109_114:V < 111
            · by_cases h109_111:V < 110
              · have hi:=sr2p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi:=sr2p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_114:V < 112
              · have hi:=sr2p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · by_cases h112_114:V < 113
                · have hi:=sr2p112 (V-112) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                · have hi:=sr2p113 (V-113) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
        · by_cases h114_123:V < 118
          · by_cases h114_118:V < 116
            · by_cases h114_116:V < 115
              · have hi:=sr2p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi:=sr2p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_118:V < 117
              · have hi:=sr2p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi:=sr2p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
          · by_cases h118_123:V < 120
            · by_cases h118_120:V < 119
              · have hi:=sr2p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi:=sr2p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
            · by_cases h120_123:V < 121
              · have hi:=sr2p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · by_cases h121_123:V < 122
                · have hi:=sr2p121 (V-121) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
                · have hi:=sr2p122 (V-122) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
      · by_cases h123_141:V < 132
        · by_cases h123_132:V < 127
          · by_cases h123_127:V < 125
            · by_cases h123_125:V < 124
              · have hi:=sr2p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi:=sr2p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
            · by_cases h125_127:V < 126
              · have hi:=sr2p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi:=sr2p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
          · by_cases h127_132:V < 129
            · by_cases h127_129:V < 128
              · have hi:=sr2p127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · have hi:=sr2p128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
            · by_cases h129_132:V < 130
              · have hi:=sr2p129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
              · by_cases h130_132:V < 131
                · have hi:=sr2p130 (V-130) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
                · have hi:=sr2p131 (V-131) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
        · by_cases h132_141:V < 136
          · by_cases h132_136:V < 134
            · by_cases h132_134:V < 133
              · have hi:=sr2p132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · have hi:=sr2p133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
            · by_cases h134_136:V < 135
              · have hi:=sr2p134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
              · have hi:=sr2p135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
          · by_cases h136_141:V < 138
            · by_cases h136_138:V < 137
              · have hi:=sr2p136 (V-136) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
              · have hi:=sr2p137 (V-137) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi
            · by_cases h138_141:V < 139
              · have hi:=sr2p138 (V-138) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 138 ≤ V by omega)] using hi
              · by_cases h139_141:V < 140
                · have hi:=sr2p139 (V-139) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 139 ≤ V by omega)] using hi
                · have hi:=sr2p140 (V-140) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 140 ≤ V by omega)] using hi

theorem br2:∀ V ∈ List.range 141,BaseCheckAt 2 V:=by
  intro V hV
  have hv:V < 141:=List.mem_range.mp hV
  by_cases h0_36:V < 72
  · by_cases h0_18:V < 36
    · by_cases h0_9:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have hi:=br2p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
          · have hi:=br2p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
        · by_cases h2_4:V < 12
          · have hi:=br2p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
          · have hi:=br2p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
      · by_cases h4_9:V < 24
        · by_cases h4_6:V < 20
          · have hi:=br2p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · have hi:=br2p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h6_9:V < 28
          · have hi:=br2p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · by_cases h7_9:V < 32
            · have hi:=br2p7 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · have hi:=br2p8 (V-32) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
    · by_cases h9_18:V < 52
      · by_cases h9_13:V < 44
        · by_cases h9_11:V < 40
          · have hi:=br2p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
          · have hi:=br2p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · by_cases h11_13:V < 48
          · have hi:=br2p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · have hi:=br2p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
      · by_cases h13_18:V < 60
        · by_cases h13_15:V < 56
          · have hi:=br2p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
          · have hi:=br2p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · by_cases h15_18:V < 64
          · have hi:=br2p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
          · by_cases h16_18:V < 68
            · have hi:=br2p16 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · have hi:=br2p17 (V-68) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
  · by_cases h18_36:V < 108
    · by_cases h18_27:V < 88
      · by_cases h18_22:V < 80
        · by_cases h18_20:V < 76
          · have hi:=br2p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · have hi:=br2p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
        · by_cases h20_22:V < 84
          · have hi:=br2p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
          · have hi:=br2p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
      · by_cases h22_27:V < 96
        · by_cases h22_24:V < 92
          · have hi:=br2p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · have hi:=br2p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
        · by_cases h24_27:V < 100
          · have hi:=br2p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
          · by_cases h25_27:V < 104
            · have hi:=br2p25 (V-100) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · have hi:=br2p26 (V-104) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
    · by_cases h27_36:V < 124
      · by_cases h27_31:V < 116
        · by_cases h27_29:V < 112
          · have hi:=br2p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · have hi:=br2p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h29_31:V < 120
          · have hi:=br2p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
          · have hi:=br2p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
      · by_cases h31_36:V < 132
        · by_cases h31_33:V < 128
          · have hi:=br2p31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
          · have hi:=br2p32 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
        · by_cases h33_36:V < 136
          · have hi:=br2p33 (V-132) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
          · by_cases h34_36:V < 140
            · have hi:=br2p34 (V-136) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
            · have hi:=br2p35 (V-140) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 140 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
