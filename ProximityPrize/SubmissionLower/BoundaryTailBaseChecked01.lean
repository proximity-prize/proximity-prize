import ProximityPrize.SubmissionLower.BoundaryTailBaseChecksData

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r1_part0 : ∀ i ∈ List.range 8, CorrectAt 1 (0+i) := by decide +kernel

theorem correct_r1_part1 : ∀ i ∈ List.range 8, CorrectAt 1 (8+i) := by decide +kernel

theorem correct_r1_part2 : ∀ i ∈ List.range 8, CorrectAt 1 (16+i) := by decide +kernel

theorem correct_r1_part3 : ∀ i ∈ List.range 8, CorrectAt 1 (24+i) := by decide +kernel

theorem correct_r1_part4 : ∀ i ∈ List.range 8, CorrectAt 1 (32+i) := by decide +kernel

theorem correct_r1_part5 : ∀ i ∈ List.range 8, CorrectAt 1 (40+i) := by decide +kernel

theorem correct_r1_part6 : ∀ i ∈ List.range 8, CorrectAt 1 (48+i) := by decide +kernel

theorem correct_r1_part7 : ∀ i ∈ List.range 8, CorrectAt 1 (56+i) := by decide +kernel

theorem correct_r1_part8 : ∀ i ∈ List.range 8, CorrectAt 1 (64+i) := by decide +kernel

theorem correct_r1_part9 : ∀ i ∈ List.range 8, CorrectAt 1 (72+i) := by decide +kernel

theorem correct_r1_part10 : ∀ i ∈ List.range 8, CorrectAt 1 (80+i) := by decide +kernel

theorem correct_r1_part11 : ∀ i ∈ List.range 8, CorrectAt 1 (88+i) := by decide +kernel

theorem correct_r1_part12 : ∀ i ∈ List.range 8, CorrectAt 1 (96+i) := by decide +kernel

theorem correct_r1_part13 : ∀ i ∈ List.range 8, CorrectAt 1 (104+i) := by decide +kernel

theorem correct_r1_part14 : ∀ i ∈ List.range 8, CorrectAt 1 (112+i) := by decide +kernel

theorem correct_r1_part15 : ∀ i ∈ List.range 8, CorrectAt 1 (120+i) := by decide +kernel

theorem correct_r1_part16 : ∀ i ∈ List.range 8, CorrectAt 1 (128+i) := by decide +kernel

theorem correct_r1_part17 : ∀ i ∈ List.range 3, CorrectAt 1 (136+i) := by decide +kernel

theorem correct_r1 : ∀ V ∈ List.range 139, CorrectAt 1 V := by
  intro V hV
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_18 : V < 72
  · by_cases h0_9 : V < 32
    · by_cases h0_4 : V < 16
      · by_cases h0_2 : V < 8
        · have hi := correct_r1_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r1_part1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h2_4 : V < 24
        · have hi := correct_r1_part2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r1_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h4_9 : V < 48
      · by_cases h4_6 : V < 40
        · have hi := correct_r1_part4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r1_part5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h6_9 : V < 56
        · have hi := correct_r1_part6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h7_9 : V < 64
          · have hi := correct_r1_part7 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := correct_r1_part8 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h9_18 : V < 104
    · by_cases h9_13 : V < 88
      · by_cases h9_11 : V < 80
        · have hi := correct_r1_part9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r1_part10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h11_13 : V < 96
        · have hi := correct_r1_part11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r1_part12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h13_18 : V < 120
      · by_cases h13_15 : V < 112
        · have hi := correct_r1_part13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r1_part14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h15_18 : V < 128
        · have hi := correct_r1_part15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h16_18 : V < 136
          · have hi := correct_r1_part16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := correct_r1_part17 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zero_r1_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (0+i) := by decide +kernel

theorem zero_r1_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (1+i) := by decide +kernel

theorem zero_r1_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (2+i) := by decide +kernel

theorem zero_r1_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (3+i) := by decide +kernel

theorem zero_r1_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (4+i) := by decide +kernel

theorem zero_r1_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (5+i) := by decide +kernel

theorem zero_r1_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (6+i) := by decide +kernel

theorem zero_r1_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (7+i) := by decide +kernel

theorem zero_r1_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (8+i) := by decide +kernel

theorem zero_r1_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (9+i) := by decide +kernel

theorem zero_r1_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (10+i) := by decide +kernel

theorem zero_r1_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (11+i) := by decide +kernel

theorem zero_r1_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (12+i) := by decide +kernel

theorem zero_r1_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (13+i) := by decide +kernel

theorem zero_r1_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (14+i) := by decide +kernel

theorem zero_r1_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (15+i) := by decide +kernel

theorem zero_r1_part16 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (16+i) := by decide +kernel

theorem zero_r1_part17 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (17+i) := by decide +kernel

theorem zero_r1_part18 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (18+i) := by decide +kernel

theorem zero_r1_part19 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (19+i) := by decide +kernel

theorem zero_r1_part20 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (20+i) := by decide +kernel

theorem zero_r1_part21 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (21+i) := by decide +kernel

theorem zero_r1_part22 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (22+i) := by decide +kernel

theorem zero_r1_part23 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (23+i) := by decide +kernel

theorem zero_r1_part24 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (24+i) := by decide +kernel

theorem zero_r1_part25 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (25+i) := by decide +kernel

theorem zero_r1_part26 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (26+i) := by decide +kernel

theorem zero_r1_part27 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (27+i) := by decide +kernel

theorem zero_r1_part28 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (28+i) := by decide +kernel

theorem zero_r1_part29 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (29+i) := by decide +kernel

theorem zero_r1_part30 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (30+i) := by decide +kernel

theorem zero_r1_part31 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (31+i) := by decide +kernel

theorem zero_r1_part32 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (32+i) := by decide +kernel

theorem zero_r1_part33 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (33+i) := by decide +kernel

theorem zero_r1_part34 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (34+i) := by decide +kernel

theorem zero_r1_part35 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (35+i) := by decide +kernel

theorem zero_r1_part36 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (36+i) := by decide +kernel

theorem zero_r1_part37 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (37+i) := by decide +kernel

theorem zero_r1_part38 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (38+i) := by decide +kernel

theorem zero_r1_part39 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (39+i) := by decide +kernel

theorem zero_r1_part40 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (40+i) := by decide +kernel

theorem zero_r1_part41 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (41+i) := by decide +kernel

theorem zero_r1_part42 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (42+i) := by decide +kernel

theorem zero_r1_part43 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (43+i) := by decide +kernel

theorem zero_r1_part44 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (44+i) := by decide +kernel

theorem zero_r1_part45 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (45+i) := by decide +kernel

theorem zero_r1_part46 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (46+i) := by decide +kernel

theorem zero_r1_part47 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (47+i) := by decide +kernel

theorem zero_r1_part48 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (48+i) := by decide +kernel

theorem zero_r1_part49 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (49+i) := by decide +kernel

theorem zero_r1_part50 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (50+i) := by decide +kernel

theorem zero_r1_part51 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (51+i) := by decide +kernel

theorem zero_r1_part52 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (52+i) := by decide +kernel

theorem zero_r1_part53 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (53+i) := by decide +kernel

theorem zero_r1_part54 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (54+i) := by decide +kernel

theorem zero_r1_part55 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (55+i) := by decide +kernel

theorem zero_r1_part56 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (56+i) := by decide +kernel

theorem zero_r1_part57 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (57+i) := by decide +kernel

theorem zero_r1_part58 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (58+i) := by decide +kernel

theorem zero_r1_part59 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (59+i) := by decide +kernel

theorem zero_r1_part60 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (60+i) := by decide +kernel

theorem zero_r1_part61 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (61+i) := by decide +kernel

theorem zero_r1_part62 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (62+i) := by decide +kernel

theorem zero_r1_part63 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (63+i) := by decide +kernel

theorem zero_r1_part64 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (64+i) := by decide +kernel

theorem zero_r1_part65 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (65+i) := by decide +kernel

theorem zero_r1_part66 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (66+i) := by decide +kernel

theorem zero_r1_part67 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (67+i) := by decide +kernel

theorem zero_r1_part68 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (68+i) := by decide +kernel

theorem zero_r1_part69 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (69+i) := by decide +kernel

theorem zero_r1_part70 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (70+i) := by decide +kernel

theorem zero_r1_part71 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (71+i) := by decide +kernel

theorem zero_r1_part72 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (72+i) := by decide +kernel

theorem zero_r1_part73 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (73+i) := by decide +kernel

theorem zero_r1_part74 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (74+i) := by decide +kernel

theorem zero_r1_part75 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (75+i) := by decide +kernel

theorem zero_r1_part76 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (76+i) := by decide +kernel

theorem zero_r1_part77 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (77+i) := by decide +kernel

theorem zero_r1_part78 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (78+i) := by decide +kernel

theorem zero_r1_part79 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (79+i) := by decide +kernel

theorem zero_r1_part80 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (80+i) := by decide +kernel

theorem zero_r1_part81 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (81+i) := by decide +kernel

theorem zero_r1_part82 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (82+i) := by decide +kernel

theorem zero_r1_part83 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (83+i) := by decide +kernel

theorem zero_r1_part84 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (84+i) := by decide +kernel

theorem zero_r1_part85 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (85+i) := by decide +kernel

theorem zero_r1_part86 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (86+i) := by decide +kernel

theorem zero_r1_part87 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (87+i) := by decide +kernel

theorem zero_r1_part88 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (88+i) := by decide +kernel

theorem zero_r1_part89 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (89+i) := by decide +kernel

theorem zero_r1_part90 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (90+i) := by decide +kernel

theorem zero_r1_part91 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (91+i) := by decide +kernel

theorem zero_r1_part92 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (92+i) := by decide +kernel

theorem zero_r1_part93 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (93+i) := by decide +kernel

theorem zero_r1_part94 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (94+i) := by decide +kernel

theorem zero_r1_part95 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (95+i) := by decide +kernel

theorem zero_r1_part96 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (96+i) := by decide +kernel

theorem zero_r1_part97 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (97+i) := by decide +kernel

theorem zero_r1_part98 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (98+i) := by decide +kernel

theorem zero_r1_part99 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (99+i) := by decide +kernel

theorem zero_r1_part100 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (100+i) := by decide +kernel

theorem zero_r1_part101 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (101+i) := by decide +kernel

theorem zero_r1_part102 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (102+i) := by decide +kernel

theorem zero_r1_part103 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (103+i) := by decide +kernel

theorem zero_r1_part104 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (104+i) := by decide +kernel

theorem zero_r1_part105 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (105+i) := by decide +kernel

theorem zero_r1_part106 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (106+i) := by decide +kernel

theorem zero_r1_part107 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (107+i) := by decide +kernel

theorem zero_r1_part108 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (108+i) := by decide +kernel

theorem zero_r1_part109 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (109+i) := by decide +kernel

theorem zero_r1_part110 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (110+i) := by decide +kernel

theorem zero_r1_part111 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (111+i) := by decide +kernel

theorem zero_r1_part112 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (112+i) := by decide +kernel

theorem zero_r1_part113 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (113+i) := by decide +kernel

theorem zero_r1_part114 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (114+i) := by decide +kernel

theorem zero_r1_part115 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (115+i) := by decide +kernel

theorem zero_r1_part116 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (116+i) := by decide +kernel

theorem zero_r1_part117 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (117+i) := by decide +kernel

theorem zero_r1_part118 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (118+i) := by decide +kernel

theorem zero_r1_part119 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (119+i) := by decide +kernel

theorem zero_r1_part120 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (120+i) := by decide +kernel

theorem zero_r1_part121 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (121+i) := by decide +kernel

theorem zero_r1_part122 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (122+i) := by decide +kernel

theorem zero_r1_part123 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (123+i) := by decide +kernel

theorem zero_r1_part124 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (124+i) := by decide +kernel

theorem zero_r1_part125 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (125+i) := by decide +kernel

theorem zero_r1_part126 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (126+i) := by decide +kernel

theorem zero_r1_part127 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (127+i) := by decide +kernel

theorem zero_r1_part128 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (128+i) := by decide +kernel

theorem zero_r1_part129 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (129+i) := by decide +kernel

theorem zero_r1_part130 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (130+i) := by decide +kernel

theorem zero_r1_part131 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (131+i) := by decide +kernel

theorem zero_r1_part132 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (132+i) := by decide +kernel

theorem zero_r1_part133 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (133+i) := by decide +kernel

theorem zero_r1_part134 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (134+i) := by decide +kernel

theorem zero_r1_part135 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (135+i) := by decide +kernel

theorem zero_r1_part136 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (136+i) := by decide +kernel

theorem zero_r1_part137 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (137+i) := by decide +kernel

theorem zero_r1_part138 : ∀ i ∈ List.range 1, ZeroCheckAt 1 (138+i) := by decide +kernel

theorem zero_r1 : ∀ V ∈ List.range 139, ZeroCheckAt 1 V := by
  intro V hV
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 69
  · by_cases h0_69 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := zero_r1_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := zero_r1_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := zero_r1_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := zero_r1_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := zero_r1_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := zero_r1_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := zero_r1_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := zero_r1_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := zero_r1_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := zero_r1_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := zero_r1_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := zero_r1_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := zero_r1_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := zero_r1_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := zero_r1_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := zero_r1_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := zero_r1_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := zero_r1_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := zero_r1_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := zero_r1_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := zero_r1_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := zero_r1_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := zero_r1_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := zero_r1_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := zero_r1_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := zero_r1_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := zero_r1_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := zero_r1_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := zero_r1_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have hi := zero_r1_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := zero_r1_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_34 : V < 32
              · have hi := zero_r1_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · by_cases h32_34 : V < 33
                · have hi := zero_r1_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
                · have hi := zero_r1_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
    · by_cases h34_69 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := zero_r1_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := zero_r1_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := zero_r1_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := zero_r1_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := zero_r1_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := zero_r1_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := zero_r1_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := zero_r1_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := zero_r1_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := zero_r1_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := zero_r1_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := zero_r1_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := zero_r1_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := zero_r1_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_51 : V < 49
              · have hi := zero_r1_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · by_cases h49_51 : V < 50
                · have hi := zero_r1_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
                · have hi := zero_r1_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
      · by_cases h51_69 : V < 60
        · by_cases h51_60 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := zero_r1_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := zero_r1_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := zero_r1_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := zero_r1_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_60 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := zero_r1_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := zero_r1_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_60 : V < 58
              · have hi := zero_r1_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · by_cases h58_60 : V < 59
                · have hi := zero_r1_part58 (V-58) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
                · have hi := zero_r1_part59 (V-59) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
        · by_cases h60_69 : V < 64
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := zero_r1_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := zero_r1_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := zero_r1_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := zero_r1_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
          · by_cases h64_69 : V < 66
            · by_cases h64_66 : V < 65
              · have hi := zero_r1_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := zero_r1_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_69 : V < 67
              · have hi := zero_r1_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · by_cases h67_69 : V < 68
                · have hi := zero_r1_part67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
                · have hi := zero_r1_part68 (V-68) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
  · by_cases h69_139 : V < 104
    · by_cases h69_104 : V < 86
      · by_cases h69_86 : V < 77
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have hi := zero_r1_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := zero_r1_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := zero_r1_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := zero_r1_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := zero_r1_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := zero_r1_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := zero_r1_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := zero_r1_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
        · by_cases h77_86 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have hi := zero_r1_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := zero_r1_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := zero_r1_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := zero_r1_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
          · by_cases h81_86 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := zero_r1_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := zero_r1_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_86 : V < 84
              · have hi := zero_r1_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · by_cases h84_86 : V < 85
                · have hi := zero_r1_part84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
                · have hi := zero_r1_part85 (V-85) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
      · by_cases h86_104 : V < 95
        · by_cases h86_95 : V < 90
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have hi := zero_r1_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := zero_r1_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := zero_r1_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := zero_r1_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
          · by_cases h90_95 : V < 92
            · by_cases h90_92 : V < 91
              · have hi := zero_r1_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := zero_r1_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_95 : V < 93
              · have hi := zero_r1_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · by_cases h93_95 : V < 94
                · have hi := zero_r1_part93 (V-93) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
                · have hi := zero_r1_part94 (V-94) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
        · by_cases h95_104 : V < 99
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have hi := zero_r1_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := zero_r1_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · by_cases h97_99 : V < 98
              · have hi := zero_r1_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := zero_r1_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
          · by_cases h99_104 : V < 101
            · by_cases h99_101 : V < 100
              · have hi := zero_r1_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := zero_r1_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · by_cases h101_104 : V < 102
              · have hi := zero_r1_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · by_cases h102_104 : V < 103
                · have hi := zero_r1_part102 (V-102) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
                · have hi := zero_r1_part103 (V-103) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
    · by_cases h104_139 : V < 121
      · by_cases h104_121 : V < 112
        · by_cases h104_112 : V < 108
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have hi := zero_r1_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := zero_r1_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := zero_r1_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := zero_r1_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := zero_r1_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := zero_r1_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := zero_r1_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := zero_r1_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
        · by_cases h112_121 : V < 116
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have hi := zero_r1_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := zero_r1_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
            · by_cases h114_116 : V < 115
              · have hi := zero_r1_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := zero_r1_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
          · by_cases h116_121 : V < 118
            · by_cases h116_118 : V < 117
              · have hi := zero_r1_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := zero_r1_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
            · by_cases h118_121 : V < 119
              · have hi := zero_r1_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · by_cases h119_121 : V < 120
                · have hi := zero_r1_part119 (V-119) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
                · have hi := zero_r1_part120 (V-120) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
      · by_cases h121_139 : V < 130
        · by_cases h121_130 : V < 125
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have hi := zero_r1_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := zero_r1_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
            · by_cases h123_125 : V < 124
              · have hi := zero_r1_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := zero_r1_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
          · by_cases h125_130 : V < 127
            · by_cases h125_127 : V < 126
              · have hi := zero_r1_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := zero_r1_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
            · by_cases h127_130 : V < 128
              · have hi := zero_r1_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · by_cases h128_130 : V < 129
                · have hi := zero_r1_part128 (V-128) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                · have hi := zero_r1_part129 (V-129) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
        · by_cases h130_139 : V < 134
          · by_cases h130_134 : V < 132
            · by_cases h130_132 : V < 131
              · have hi := zero_r1_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · have hi := zero_r1_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
            · by_cases h132_134 : V < 133
              · have hi := zero_r1_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · have hi := zero_r1_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
          · by_cases h134_139 : V < 136
            · by_cases h134_136 : V < 135
              · have hi := zero_r1_part134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
              · have hi := zero_r1_part135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
            · by_cases h136_139 : V < 137
              · have hi := zero_r1_part136 (V-136) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
              · by_cases h137_139 : V < 138
                · have hi := zero_r1_part137 (V-137) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi
                · have hi := zero_r1_part138 (V-138) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 138 ≤ V by omega)] using hi

theorem strict_r1_part0 : ∀ i ∈ List.range 1, StrictCheckAt 1 (0+i) := by decide +kernel

theorem strict_r1_part1 : ∀ i ∈ List.range 1, StrictCheckAt 1 (1+i) := by decide +kernel

theorem strict_r1_part2 : ∀ i ∈ List.range 1, StrictCheckAt 1 (2+i) := by decide +kernel

theorem strict_r1_part3 : ∀ i ∈ List.range 1, StrictCheckAt 1 (3+i) := by decide +kernel

theorem strict_r1_part4 : ∀ i ∈ List.range 1, StrictCheckAt 1 (4+i) := by decide +kernel

theorem strict_r1_part5 : ∀ i ∈ List.range 1, StrictCheckAt 1 (5+i) := by decide +kernel

theorem strict_r1_part6 : ∀ i ∈ List.range 1, StrictCheckAt 1 (6+i) := by decide +kernel

theorem strict_r1_part7 : ∀ i ∈ List.range 1, StrictCheckAt 1 (7+i) := by decide +kernel

theorem strict_r1_part8 : ∀ i ∈ List.range 1, StrictCheckAt 1 (8+i) := by decide +kernel

theorem strict_r1_part9 : ∀ i ∈ List.range 1, StrictCheckAt 1 (9+i) := by decide +kernel

theorem strict_r1_part10 : ∀ i ∈ List.range 1, StrictCheckAt 1 (10+i) := by decide +kernel

theorem strict_r1_part11 : ∀ i ∈ List.range 1, StrictCheckAt 1 (11+i) := by decide +kernel

theorem strict_r1_part12 : ∀ i ∈ List.range 1, StrictCheckAt 1 (12+i) := by decide +kernel

theorem strict_r1_part13 : ∀ i ∈ List.range 1, StrictCheckAt 1 (13+i) := by decide +kernel

theorem strict_r1_part14 : ∀ i ∈ List.range 1, StrictCheckAt 1 (14+i) := by decide +kernel

theorem strict_r1_part15 : ∀ i ∈ List.range 1, StrictCheckAt 1 (15+i) := by decide +kernel

theorem strict_r1_part16 : ∀ i ∈ List.range 1, StrictCheckAt 1 (16+i) := by decide +kernel

theorem strict_r1_part17 : ∀ i ∈ List.range 1, StrictCheckAt 1 (17+i) := by decide +kernel

theorem strict_r1_part18 : ∀ i ∈ List.range 1, StrictCheckAt 1 (18+i) := by decide +kernel

theorem strict_r1_part19 : ∀ i ∈ List.range 1, StrictCheckAt 1 (19+i) := by decide +kernel

theorem strict_r1_part20 : ∀ i ∈ List.range 1, StrictCheckAt 1 (20+i) := by decide +kernel

theorem strict_r1_part21 : ∀ i ∈ List.range 1, StrictCheckAt 1 (21+i) := by decide +kernel

theorem strict_r1_part22 : ∀ i ∈ List.range 1, StrictCheckAt 1 (22+i) := by decide +kernel

theorem strict_r1_part23 : ∀ i ∈ List.range 1, StrictCheckAt 1 (23+i) := by decide +kernel

theorem strict_r1_part24 : ∀ i ∈ List.range 1, StrictCheckAt 1 (24+i) := by decide +kernel

theorem strict_r1_part25 : ∀ i ∈ List.range 1, StrictCheckAt 1 (25+i) := by decide +kernel

theorem strict_r1_part26 : ∀ i ∈ List.range 1, StrictCheckAt 1 (26+i) := by decide +kernel

theorem strict_r1_part27 : ∀ i ∈ List.range 1, StrictCheckAt 1 (27+i) := by decide +kernel

theorem strict_r1_part28 : ∀ i ∈ List.range 1, StrictCheckAt 1 (28+i) := by decide +kernel

theorem strict_r1_part29 : ∀ i ∈ List.range 1, StrictCheckAt 1 (29+i) := by decide +kernel

theorem strict_r1_part30 : ∀ i ∈ List.range 1, StrictCheckAt 1 (30+i) := by decide +kernel

theorem strict_r1_part31 : ∀ i ∈ List.range 1, StrictCheckAt 1 (31+i) := by decide +kernel

theorem strict_r1_part32 : ∀ i ∈ List.range 1, StrictCheckAt 1 (32+i) := by decide +kernel

theorem strict_r1_part33 : ∀ i ∈ List.range 1, StrictCheckAt 1 (33+i) := by decide +kernel

theorem strict_r1_part34 : ∀ i ∈ List.range 1, StrictCheckAt 1 (34+i) := by decide +kernel

theorem strict_r1_part35 : ∀ i ∈ List.range 1, StrictCheckAt 1 (35+i) := by decide +kernel

theorem strict_r1_part36 : ∀ i ∈ List.range 1, StrictCheckAt 1 (36+i) := by decide +kernel

theorem strict_r1_part37 : ∀ i ∈ List.range 1, StrictCheckAt 1 (37+i) := by decide +kernel

theorem strict_r1_part38 : ∀ i ∈ List.range 1, StrictCheckAt 1 (38+i) := by decide +kernel

theorem strict_r1_part39 : ∀ i ∈ List.range 1, StrictCheckAt 1 (39+i) := by decide +kernel

theorem strict_r1_part40 : ∀ i ∈ List.range 1, StrictCheckAt 1 (40+i) := by decide +kernel

theorem strict_r1_part41 : ∀ i ∈ List.range 1, StrictCheckAt 1 (41+i) := by decide +kernel

theorem strict_r1_part42 : ∀ i ∈ List.range 1, StrictCheckAt 1 (42+i) := by decide +kernel

theorem strict_r1_part43 : ∀ i ∈ List.range 1, StrictCheckAt 1 (43+i) := by decide +kernel

theorem strict_r1_part44 : ∀ i ∈ List.range 1, StrictCheckAt 1 (44+i) := by decide +kernel

theorem strict_r1_part45 : ∀ i ∈ List.range 1, StrictCheckAt 1 (45+i) := by decide +kernel

theorem strict_r1_part46 : ∀ i ∈ List.range 1, StrictCheckAt 1 (46+i) := by decide +kernel

theorem strict_r1_part47 : ∀ i ∈ List.range 1, StrictCheckAt 1 (47+i) := by decide +kernel

theorem strict_r1_part48 : ∀ i ∈ List.range 1, StrictCheckAt 1 (48+i) := by decide +kernel

theorem strict_r1_part49 : ∀ i ∈ List.range 1, StrictCheckAt 1 (49+i) := by decide +kernel

theorem strict_r1_part50 : ∀ i ∈ List.range 1, StrictCheckAt 1 (50+i) := by decide +kernel

theorem strict_r1_part51 : ∀ i ∈ List.range 1, StrictCheckAt 1 (51+i) := by decide +kernel

theorem strict_r1_part52 : ∀ i ∈ List.range 1, StrictCheckAt 1 (52+i) := by decide +kernel

theorem strict_r1_part53 : ∀ i ∈ List.range 1, StrictCheckAt 1 (53+i) := by decide +kernel

theorem strict_r1_part54 : ∀ i ∈ List.range 1, StrictCheckAt 1 (54+i) := by decide +kernel

theorem strict_r1_part55 : ∀ i ∈ List.range 1, StrictCheckAt 1 (55+i) := by decide +kernel

theorem strict_r1_part56 : ∀ i ∈ List.range 1, StrictCheckAt 1 (56+i) := by decide +kernel

theorem strict_r1_part57 : ∀ i ∈ List.range 1, StrictCheckAt 1 (57+i) := by decide +kernel

theorem strict_r1_part58 : ∀ i ∈ List.range 1, StrictCheckAt 1 (58+i) := by decide +kernel

theorem strict_r1_part59 : ∀ i ∈ List.range 1, StrictCheckAt 1 (59+i) := by decide +kernel

theorem strict_r1_part60 : ∀ i ∈ List.range 1, StrictCheckAt 1 (60+i) := by decide +kernel

theorem strict_r1_part61 : ∀ i ∈ List.range 1, StrictCheckAt 1 (61+i) := by decide +kernel

theorem strict_r1_part62 : ∀ i ∈ List.range 1, StrictCheckAt 1 (62+i) := by decide +kernel

theorem strict_r1_part63 : ∀ i ∈ List.range 1, StrictCheckAt 1 (63+i) := by decide +kernel

theorem strict_r1_part64 : ∀ i ∈ List.range 1, StrictCheckAt 1 (64+i) := by decide +kernel

theorem strict_r1_part65 : ∀ i ∈ List.range 1, StrictCheckAt 1 (65+i) := by decide +kernel

theorem strict_r1_part66 : ∀ i ∈ List.range 1, StrictCheckAt 1 (66+i) := by decide +kernel

theorem strict_r1_part67 : ∀ i ∈ List.range 1, StrictCheckAt 1 (67+i) := by decide +kernel

theorem strict_r1_part68 : ∀ i ∈ List.range 1, StrictCheckAt 1 (68+i) := by decide +kernel

theorem strict_r1_part69 : ∀ i ∈ List.range 1, StrictCheckAt 1 (69+i) := by decide +kernel

theorem strict_r1_part70 : ∀ i ∈ List.range 1, StrictCheckAt 1 (70+i) := by decide +kernel

theorem strict_r1_part71 : ∀ i ∈ List.range 1, StrictCheckAt 1 (71+i) := by decide +kernel

theorem strict_r1_part72 : ∀ i ∈ List.range 1, StrictCheckAt 1 (72+i) := by decide +kernel

theorem strict_r1_part73 : ∀ i ∈ List.range 1, StrictCheckAt 1 (73+i) := by decide +kernel

theorem strict_r1_part74 : ∀ i ∈ List.range 1, StrictCheckAt 1 (74+i) := by decide +kernel

theorem strict_r1_part75 : ∀ i ∈ List.range 1, StrictCheckAt 1 (75+i) := by decide +kernel

theorem strict_r1_part76 : ∀ i ∈ List.range 1, StrictCheckAt 1 (76+i) := by decide +kernel

theorem strict_r1_part77 : ∀ i ∈ List.range 1, StrictCheckAt 1 (77+i) := by decide +kernel

theorem strict_r1_part78 : ∀ i ∈ List.range 1, StrictCheckAt 1 (78+i) := by decide +kernel

theorem strict_r1_part79 : ∀ i ∈ List.range 1, StrictCheckAt 1 (79+i) := by decide +kernel

theorem strict_r1_part80 : ∀ i ∈ List.range 1, StrictCheckAt 1 (80+i) := by decide +kernel

theorem strict_r1_part81 : ∀ i ∈ List.range 1, StrictCheckAt 1 (81+i) := by decide +kernel

theorem strict_r1_part82 : ∀ i ∈ List.range 1, StrictCheckAt 1 (82+i) := by decide +kernel

theorem strict_r1_part83 : ∀ i ∈ List.range 1, StrictCheckAt 1 (83+i) := by decide +kernel

theorem strict_r1_part84 : ∀ i ∈ List.range 1, StrictCheckAt 1 (84+i) := by decide +kernel

theorem strict_r1_part85 : ∀ i ∈ List.range 1, StrictCheckAt 1 (85+i) := by decide +kernel

theorem strict_r1_part86 : ∀ i ∈ List.range 1, StrictCheckAt 1 (86+i) := by decide +kernel

theorem strict_r1_part87 : ∀ i ∈ List.range 1, StrictCheckAt 1 (87+i) := by decide +kernel

theorem strict_r1_part88 : ∀ i ∈ List.range 1, StrictCheckAt 1 (88+i) := by decide +kernel

theorem strict_r1_part89 : ∀ i ∈ List.range 1, StrictCheckAt 1 (89+i) := by decide +kernel

theorem strict_r1_part90 : ∀ i ∈ List.range 1, StrictCheckAt 1 (90+i) := by decide +kernel

theorem strict_r1_part91 : ∀ i ∈ List.range 1, StrictCheckAt 1 (91+i) := by decide +kernel

theorem strict_r1_part92 : ∀ i ∈ List.range 1, StrictCheckAt 1 (92+i) := by decide +kernel

theorem strict_r1_part93 : ∀ i ∈ List.range 1, StrictCheckAt 1 (93+i) := by decide +kernel

theorem strict_r1_part94 : ∀ i ∈ List.range 1, StrictCheckAt 1 (94+i) := by decide +kernel

theorem strict_r1_part95 : ∀ i ∈ List.range 1, StrictCheckAt 1 (95+i) := by decide +kernel

theorem strict_r1_part96 : ∀ i ∈ List.range 1, StrictCheckAt 1 (96+i) := by decide +kernel

theorem strict_r1_part97 : ∀ i ∈ List.range 1, StrictCheckAt 1 (97+i) := by decide +kernel

theorem strict_r1_part98 : ∀ i ∈ List.range 1, StrictCheckAt 1 (98+i) := by decide +kernel

theorem strict_r1_part99 : ∀ i ∈ List.range 1, StrictCheckAt 1 (99+i) := by decide +kernel

theorem strict_r1_part100 : ∀ i ∈ List.range 1, StrictCheckAt 1 (100+i) := by decide +kernel

theorem strict_r1_part101 : ∀ i ∈ List.range 1, StrictCheckAt 1 (101+i) := by decide +kernel

theorem strict_r1_part102 : ∀ i ∈ List.range 1, StrictCheckAt 1 (102+i) := by decide +kernel

theorem strict_r1_part103 : ∀ i ∈ List.range 1, StrictCheckAt 1 (103+i) := by decide +kernel

theorem strict_r1_part104 : ∀ i ∈ List.range 1, StrictCheckAt 1 (104+i) := by decide +kernel

theorem strict_r1_part105 : ∀ i ∈ List.range 1, StrictCheckAt 1 (105+i) := by decide +kernel

theorem strict_r1_part106 : ∀ i ∈ List.range 1, StrictCheckAt 1 (106+i) := by decide +kernel

theorem strict_r1_part107 : ∀ i ∈ List.range 1, StrictCheckAt 1 (107+i) := by decide +kernel

theorem strict_r1_part108 : ∀ i ∈ List.range 1, StrictCheckAt 1 (108+i) := by decide +kernel

theorem strict_r1_part109 : ∀ i ∈ List.range 1, StrictCheckAt 1 (109+i) := by decide +kernel

theorem strict_r1_part110 : ∀ i ∈ List.range 1, StrictCheckAt 1 (110+i) := by decide +kernel

theorem strict_r1_part111 : ∀ i ∈ List.range 1, StrictCheckAt 1 (111+i) := by decide +kernel

theorem strict_r1_part112 : ∀ i ∈ List.range 1, StrictCheckAt 1 (112+i) := by decide +kernel

theorem strict_r1_part113 : ∀ i ∈ List.range 1, StrictCheckAt 1 (113+i) := by decide +kernel

theorem strict_r1_part114 : ∀ i ∈ List.range 1, StrictCheckAt 1 (114+i) := by decide +kernel

theorem strict_r1_part115 : ∀ i ∈ List.range 1, StrictCheckAt 1 (115+i) := by decide +kernel

theorem strict_r1_part116 : ∀ i ∈ List.range 1, StrictCheckAt 1 (116+i) := by decide +kernel

theorem strict_r1_part117 : ∀ i ∈ List.range 1, StrictCheckAt 1 (117+i) := by decide +kernel

theorem strict_r1_part118 : ∀ i ∈ List.range 1, StrictCheckAt 1 (118+i) := by decide +kernel

theorem strict_r1_part119 : ∀ i ∈ List.range 1, StrictCheckAt 1 (119+i) := by decide +kernel

theorem strict_r1_part120 : ∀ i ∈ List.range 1, StrictCheckAt 1 (120+i) := by decide +kernel

theorem strict_r1_part121 : ∀ i ∈ List.range 1, StrictCheckAt 1 (121+i) := by decide +kernel

theorem strict_r1_part122 : ∀ i ∈ List.range 1, StrictCheckAt 1 (122+i) := by decide +kernel

theorem strict_r1_part123 : ∀ i ∈ List.range 1, StrictCheckAt 1 (123+i) := by decide +kernel

theorem strict_r1_part124 : ∀ i ∈ List.range 1, StrictCheckAt 1 (124+i) := by decide +kernel

theorem strict_r1_part125 : ∀ i ∈ List.range 1, StrictCheckAt 1 (125+i) := by decide +kernel

theorem strict_r1_part126 : ∀ i ∈ List.range 1, StrictCheckAt 1 (126+i) := by decide +kernel

theorem strict_r1_part127 : ∀ i ∈ List.range 1, StrictCheckAt 1 (127+i) := by decide +kernel

theorem strict_r1_part128 : ∀ i ∈ List.range 1, StrictCheckAt 1 (128+i) := by decide +kernel

theorem strict_r1_part129 : ∀ i ∈ List.range 1, StrictCheckAt 1 (129+i) := by decide +kernel

theorem strict_r1_part130 : ∀ i ∈ List.range 1, StrictCheckAt 1 (130+i) := by decide +kernel

theorem strict_r1_part131 : ∀ i ∈ List.range 1, StrictCheckAt 1 (131+i) := by decide +kernel

theorem strict_r1_part132 : ∀ i ∈ List.range 1, StrictCheckAt 1 (132+i) := by decide +kernel

theorem strict_r1_part133 : ∀ i ∈ List.range 1, StrictCheckAt 1 (133+i) := by decide +kernel

theorem strict_r1_part134 : ∀ i ∈ List.range 1, StrictCheckAt 1 (134+i) := by decide +kernel

theorem strict_r1_part135 : ∀ i ∈ List.range 1, StrictCheckAt 1 (135+i) := by decide +kernel

theorem strict_r1_part136 : ∀ i ∈ List.range 1, StrictCheckAt 1 (136+i) := by decide +kernel

theorem strict_r1_part137 : ∀ i ∈ List.range 1, StrictCheckAt 1 (137+i) := by decide +kernel

theorem strict_r1_part138 : ∀ i ∈ List.range 1, StrictCheckAt 1 (138+i) := by decide +kernel

theorem strict_r1 : ∀ V ∈ List.range 139, StrictCheckAt 1 V := by
  intro V hV
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 69
  · by_cases h0_69 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strict_r1_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strict_r1_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strict_r1_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strict_r1_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strict_r1_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strict_r1_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strict_r1_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strict_r1_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strict_r1_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strict_r1_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strict_r1_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strict_r1_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strict_r1_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strict_r1_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := strict_r1_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := strict_r1_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := strict_r1_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strict_r1_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strict_r1_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strict_r1_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strict_r1_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strict_r1_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strict_r1_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strict_r1_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strict_r1_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strict_r1_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strict_r1_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strict_r1_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strict_r1_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have hi := strict_r1_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strict_r1_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_34 : V < 32
              · have hi := strict_r1_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · by_cases h32_34 : V < 33
                · have hi := strict_r1_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
                · have hi := strict_r1_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
    · by_cases h34_69 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := strict_r1_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strict_r1_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strict_r1_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strict_r1_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strict_r1_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strict_r1_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strict_r1_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strict_r1_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := strict_r1_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strict_r1_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strict_r1_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strict_r1_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strict_r1_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strict_r1_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_51 : V < 49
              · have hi := strict_r1_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · by_cases h49_51 : V < 50
                · have hi := strict_r1_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
                · have hi := strict_r1_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
      · by_cases h51_69 : V < 60
        · by_cases h51_60 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strict_r1_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strict_r1_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strict_r1_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strict_r1_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_60 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strict_r1_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strict_r1_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_60 : V < 58
              · have hi := strict_r1_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · by_cases h58_60 : V < 59
                · have hi := strict_r1_part58 (V-58) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
                · have hi := strict_r1_part59 (V-59) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
        · by_cases h60_69 : V < 64
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := strict_r1_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strict_r1_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := strict_r1_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strict_r1_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
          · by_cases h64_69 : V < 66
            · by_cases h64_66 : V < 65
              · have hi := strict_r1_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strict_r1_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_69 : V < 67
              · have hi := strict_r1_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · by_cases h67_69 : V < 68
                · have hi := strict_r1_part67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
                · have hi := strict_r1_part68 (V-68) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
  · by_cases h69_139 : V < 104
    · by_cases h69_104 : V < 86
      · by_cases h69_86 : V < 77
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have hi := strict_r1_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strict_r1_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strict_r1_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strict_r1_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := strict_r1_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strict_r1_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strict_r1_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strict_r1_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
        · by_cases h77_86 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have hi := strict_r1_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strict_r1_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := strict_r1_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strict_r1_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
          · by_cases h81_86 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := strict_r1_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strict_r1_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_86 : V < 84
              · have hi := strict_r1_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · by_cases h84_86 : V < 85
                · have hi := strict_r1_part84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
                · have hi := strict_r1_part85 (V-85) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
      · by_cases h86_104 : V < 95
        · by_cases h86_95 : V < 90
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have hi := strict_r1_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strict_r1_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strict_r1_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strict_r1_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
          · by_cases h90_95 : V < 92
            · by_cases h90_92 : V < 91
              · have hi := strict_r1_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strict_r1_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_95 : V < 93
              · have hi := strict_r1_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · by_cases h93_95 : V < 94
                · have hi := strict_r1_part93 (V-93) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
                · have hi := strict_r1_part94 (V-94) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
        · by_cases h95_104 : V < 99
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have hi := strict_r1_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strict_r1_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · by_cases h97_99 : V < 98
              · have hi := strict_r1_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strict_r1_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
          · by_cases h99_104 : V < 101
            · by_cases h99_101 : V < 100
              · have hi := strict_r1_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strict_r1_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · by_cases h101_104 : V < 102
              · have hi := strict_r1_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · by_cases h102_104 : V < 103
                · have hi := strict_r1_part102 (V-102) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
                · have hi := strict_r1_part103 (V-103) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
    · by_cases h104_139 : V < 121
      · by_cases h104_121 : V < 112
        · by_cases h104_112 : V < 108
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have hi := strict_r1_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strict_r1_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := strict_r1_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strict_r1_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := strict_r1_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strict_r1_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := strict_r1_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strict_r1_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
        · by_cases h112_121 : V < 116
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have hi := strict_r1_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strict_r1_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
            · by_cases h114_116 : V < 115
              · have hi := strict_r1_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strict_r1_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
          · by_cases h116_121 : V < 118
            · by_cases h116_118 : V < 117
              · have hi := strict_r1_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strict_r1_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
            · by_cases h118_121 : V < 119
              · have hi := strict_r1_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · by_cases h119_121 : V < 120
                · have hi := strict_r1_part119 (V-119) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
                · have hi := strict_r1_part120 (V-120) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
      · by_cases h121_139 : V < 130
        · by_cases h121_130 : V < 125
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have hi := strict_r1_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strict_r1_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
            · by_cases h123_125 : V < 124
              · have hi := strict_r1_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strict_r1_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
          · by_cases h125_130 : V < 127
            · by_cases h125_127 : V < 126
              · have hi := strict_r1_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := strict_r1_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
            · by_cases h127_130 : V < 128
              · have hi := strict_r1_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · by_cases h128_130 : V < 129
                · have hi := strict_r1_part128 (V-128) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                · have hi := strict_r1_part129 (V-129) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
        · by_cases h130_139 : V < 134
          · by_cases h130_134 : V < 132
            · by_cases h130_132 : V < 131
              · have hi := strict_r1_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · have hi := strict_r1_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
            · by_cases h132_134 : V < 133
              · have hi := strict_r1_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · have hi := strict_r1_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
          · by_cases h134_139 : V < 136
            · by_cases h134_136 : V < 135
              · have hi := strict_r1_part134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
              · have hi := strict_r1_part135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
            · by_cases h136_139 : V < 137
              · have hi := strict_r1_part136 (V-136) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
              · by_cases h137_139 : V < 138
                · have hi := strict_r1_part137 (V-137) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi
                · have hi := strict_r1_part138 (V-138) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 138 ≤ V by omega)] using hi

theorem base_r1_part0 : ∀ i ∈ List.range 4, BaseCheckAt 1 (0+i) := by decide +kernel

theorem base_r1_part1 : ∀ i ∈ List.range 4, BaseCheckAt 1 (4+i) := by decide +kernel

theorem base_r1_part2 : ∀ i ∈ List.range 4, BaseCheckAt 1 (8+i) := by decide +kernel

theorem base_r1_part3 : ∀ i ∈ List.range 4, BaseCheckAt 1 (12+i) := by decide +kernel

theorem base_r1_part4 : ∀ i ∈ List.range 4, BaseCheckAt 1 (16+i) := by decide +kernel

theorem base_r1_part5 : ∀ i ∈ List.range 4, BaseCheckAt 1 (20+i) := by decide +kernel

theorem base_r1_part6 : ∀ i ∈ List.range 4, BaseCheckAt 1 (24+i) := by decide +kernel

theorem base_r1_part7 : ∀ i ∈ List.range 4, BaseCheckAt 1 (28+i) := by decide +kernel

theorem base_r1_part8 : ∀ i ∈ List.range 4, BaseCheckAt 1 (32+i) := by decide +kernel

theorem base_r1_part9 : ∀ i ∈ List.range 4, BaseCheckAt 1 (36+i) := by decide +kernel

theorem base_r1_part10 : ∀ i ∈ List.range 4, BaseCheckAt 1 (40+i) := by decide +kernel

theorem base_r1_part11 : ∀ i ∈ List.range 4, BaseCheckAt 1 (44+i) := by decide +kernel

theorem base_r1_part12 : ∀ i ∈ List.range 4, BaseCheckAt 1 (48+i) := by decide +kernel

theorem base_r1_part13 : ∀ i ∈ List.range 4, BaseCheckAt 1 (52+i) := by decide +kernel

theorem base_r1_part14 : ∀ i ∈ List.range 4, BaseCheckAt 1 (56+i) := by decide +kernel

theorem base_r1_part15 : ∀ i ∈ List.range 4, BaseCheckAt 1 (60+i) := by decide +kernel

theorem base_r1_part16 : ∀ i ∈ List.range 4, BaseCheckAt 1 (64+i) := by decide +kernel

theorem base_r1_part17 : ∀ i ∈ List.range 4, BaseCheckAt 1 (68+i) := by decide +kernel

theorem base_r1_part18 : ∀ i ∈ List.range 4, BaseCheckAt 1 (72+i) := by decide +kernel

theorem base_r1_part19 : ∀ i ∈ List.range 4, BaseCheckAt 1 (76+i) := by decide +kernel

theorem base_r1_part20 : ∀ i ∈ List.range 4, BaseCheckAt 1 (80+i) := by decide +kernel

theorem base_r1_part21 : ∀ i ∈ List.range 4, BaseCheckAt 1 (84+i) := by decide +kernel

theorem base_r1_part22 : ∀ i ∈ List.range 4, BaseCheckAt 1 (88+i) := by decide +kernel

theorem base_r1_part23 : ∀ i ∈ List.range 4, BaseCheckAt 1 (92+i) := by decide +kernel

theorem base_r1_part24 : ∀ i ∈ List.range 4, BaseCheckAt 1 (96+i) := by decide +kernel

theorem base_r1_part25 : ∀ i ∈ List.range 4, BaseCheckAt 1 (100+i) := by decide +kernel

theorem base_r1_part26 : ∀ i ∈ List.range 4, BaseCheckAt 1 (104+i) := by decide +kernel

theorem base_r1_part27 : ∀ i ∈ List.range 4, BaseCheckAt 1 (108+i) := by decide +kernel

theorem base_r1_part28 : ∀ i ∈ List.range 4, BaseCheckAt 1 (112+i) := by decide +kernel

theorem base_r1_part29 : ∀ i ∈ List.range 4, BaseCheckAt 1 (116+i) := by decide +kernel

theorem base_r1_part30 : ∀ i ∈ List.range 4, BaseCheckAt 1 (120+i) := by decide +kernel

theorem base_r1_part31 : ∀ i ∈ List.range 4, BaseCheckAt 1 (124+i) := by decide +kernel

theorem base_r1_part32 : ∀ i ∈ List.range 4, BaseCheckAt 1 (128+i) := by decide +kernel

theorem base_r1_part33 : ∀ i ∈ List.range 4, BaseCheckAt 1 (132+i) := by decide +kernel

theorem base_r1_part34 : ∀ i ∈ List.range 3, BaseCheckAt 1 (136+i) := by decide +kernel

theorem base_r1 : ∀ V ∈ List.range 139, BaseCheckAt 1 V := by
  intro V hV
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_35 : V < 68
  · by_cases h0_17 : V < 32
    · by_cases h0_8 : V < 16
      · by_cases h0_4 : V < 8
        · by_cases h0_2 : V < 4
          · have hi := base_r1_part0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
          · have hi := base_r1_part1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
        · by_cases h2_4 : V < 12
          · have hi := base_r1_part2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
          · have hi := base_r1_part3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
      · by_cases h4_8 : V < 24
        · by_cases h4_6 : V < 20
          · have hi := base_r1_part4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · have hi := base_r1_part5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h6_8 : V < 28
          · have hi := base_r1_part6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · have hi := base_r1_part7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
    · by_cases h8_17 : V < 48
      · by_cases h8_12 : V < 40
        · by_cases h8_10 : V < 36
          · have hi := base_r1_part8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          · have hi := base_r1_part9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
        · by_cases h10_12 : V < 44
          · have hi := base_r1_part10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
          · have hi := base_r1_part11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
      · by_cases h12_17 : V < 56
        · by_cases h12_14 : V < 52
          · have hi := base_r1_part12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
          · have hi := base_r1_part13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
        · by_cases h14_17 : V < 60
          · have hi := base_r1_part14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · by_cases h15_17 : V < 64
            · have hi := base_r1_part15 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · have hi := base_r1_part16 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h17_35 : V < 104
    · by_cases h17_26 : V < 84
      · by_cases h17_21 : V < 76
        · by_cases h17_19 : V < 72
          · have hi := base_r1_part17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
          · have hi := base_r1_part18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · by_cases h19_21 : V < 80
          · have hi := base_r1_part19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
          · have hi := base_r1_part20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h21_26 : V < 92
        · by_cases h21_23 : V < 88
          · have hi := base_r1_part21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
          · have hi := base_r1_part22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · by_cases h23_26 : V < 96
          · have hi := base_r1_part23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
          · by_cases h24_26 : V < 100
            · have hi := base_r1_part24 (V-96) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · have hi := base_r1_part25 (V-100) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
    · by_cases h26_35 : V < 120
      · by_cases h26_30 : V < 112
        · by_cases h26_28 : V < 108
          · have hi := base_r1_part26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
          · have hi := base_r1_part27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
        · by_cases h28_30 : V < 116
          · have hi := base_r1_part28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
          · have hi := base_r1_part29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
      · by_cases h30_35 : V < 128
        · by_cases h30_32 : V < 124
          · have hi := base_r1_part30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := base_r1_part31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
        · by_cases h32_35 : V < 132
          · have hi := base_r1_part32 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · by_cases h33_35 : V < 136
            · have hi := base_r1_part33 (V-132) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
            · have hi := base_r1_part34 (V-136) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
