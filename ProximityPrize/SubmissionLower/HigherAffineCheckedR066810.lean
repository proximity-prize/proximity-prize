import ProximityPrize.SubmissionLower.HigherAffineCheckedR056810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_6_0 : ∀ i ∈ List.range 4, SingleAt 6 (0+i) := by decide +kernel

theorem single_6_4 : ∀ i ∈ List.range 4, SingleAt 6 (4+i) := by decide +kernel

theorem single_6_8 : ∀ i ∈ List.range 4, SingleAt 6 (8+i) := by decide +kernel

theorem single_6_12 : ∀ i ∈ List.range 4, SingleAt 6 (12+i) := by decide +kernel

theorem single_6_16 : ∀ i ∈ List.range 4, SingleAt 6 (16+i) := by decide +kernel

theorem single_6_20 : ∀ i ∈ List.range 4, SingleAt 6 (20+i) := by decide +kernel

theorem single_6_24 : ∀ i ∈ List.range 4, SingleAt 6 (24+i) := by decide +kernel

theorem single_6_28 : ∀ i ∈ List.range 4, SingleAt 6 (28+i) := by decide +kernel

theorem single_6_32 : ∀ i ∈ List.range 4, SingleAt 6 (32+i) := by decide +kernel

theorem single_6_36 : ∀ i ∈ List.range 4, SingleAt 6 (36+i) := by decide +kernel

theorem single_6_40 : ∀ i ∈ List.range 4, SingleAt 6 (40+i) := by decide +kernel

theorem single_6_44 : ∀ i ∈ List.range 4, SingleAt 6 (44+i) := by decide +kernel

theorem single_6_48 : ∀ i ∈ List.range 4, SingleAt 6 (48+i) := by decide +kernel

theorem single_6_52 : ∀ i ∈ List.range 4, SingleAt 6 (52+i) := by decide +kernel

theorem single_6_56 : ∀ i ∈ List.range 4, SingleAt 6 (56+i) := by decide +kernel

theorem single_6_60 : ∀ i ∈ List.range 4, SingleAt 6 (60+i) := by decide +kernel

theorem single_6_64 : ∀ i ∈ List.range 4, SingleAt 6 (64+i) := by decide +kernel

theorem single_6_68 : ∀ i ∈ List.range 4, SingleAt 6 (68+i) := by decide +kernel

theorem single_6_72 : ∀ i ∈ List.range 4, SingleAt 6 (72+i) := by decide +kernel

theorem single_6_76 : ∀ i ∈ List.range 4, SingleAt 6 (76+i) := by decide +kernel

theorem single_6_80 : ∀ i ∈ List.range 4, SingleAt 6 (80+i) := by decide +kernel

theorem single_6_84 : ∀ i ∈ List.range 4, SingleAt 6 (84+i) := by decide +kernel

theorem single_6_88 : ∀ i ∈ List.range 4, SingleAt 6 (88+i) := by decide +kernel

theorem single_6_92 : ∀ i ∈ List.range 4, SingleAt 6 (92+i) := by decide +kernel

theorem single_6_96 : ∀ i ∈ List.range 4, SingleAt 6 (96+i) := by decide +kernel

theorem single_6_100 : ∀ i ∈ List.range 4, SingleAt 6 (100+i) := by decide +kernel

theorem single_6_104 : ∀ i ∈ List.range 4, SingleAt 6 (104+i) := by decide +kernel

theorem single_6_108 : ∀ i ∈ List.range 4, SingleAt 6 (108+i) := by decide +kernel

theorem single_6_112 : ∀ i ∈ List.range 4, SingleAt 6 (112+i) := by decide +kernel

theorem single_6_116 : ∀ i ∈ List.range 4, SingleAt 6 (116+i) := by decide +kernel

theorem single_6_120 : ∀ i ∈ List.range 4, SingleAt 6 (120+i) := by decide +kernel

theorem single_6_124 : ∀ i ∈ List.range 4, SingleAt 6 (124+i) := by decide +kernel

theorem single_6_128 : ∀ i ∈ List.range 4, SingleAt 6 (128+i) := by decide +kernel

theorem single_6_132 : ∀ i ∈ List.range 4, SingleAt 6 (132+i) := by decide +kernel

theorem single_6_136 : ∀ i ∈ List.range 4, SingleAt 6 (136+i) := by decide +kernel

theorem single_6_140 : ∀ i ∈ List.range 4, SingleAt 6 (140+i) := by decide +kernel

theorem single_6_144 : ∀ i ∈ List.range 4, SingleAt 6 (144+i) := by decide +kernel

theorem single_6_148 : ∀ i ∈ List.range 3, SingleAt 6 (148+i) := by decide +kernel

theorem single_6 (v : ℕ) (hv : v ∈ List.range 151) : SingleAt 6 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 6 v)
  have h := (join 0 76 75 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_6_0 single_6_4) (join 8 4 4 single_6_8 single_6_12)) (join 16 8 12 (join 16 4 4 single_6_16 single_6_20) (join 24 4 8 single_6_24 (join 28 4 4 single_6_28 single_6_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 single_6_36 single_6_40) (join 44 4 8 single_6_44 (join 48 4 4 single_6_48 single_6_52))) (join 56 8 12 (join 56 4 4 single_6_56 single_6_60) (join 64 4 8 single_6_64 (join 68 4 4 single_6_68 single_6_72))))) (join 76 36 39 (join 76 16 20 (join 76 8 8 (join 76 4 4 single_6_76 single_6_80) (join 84 4 4 single_6_84 single_6_88)) (join 92 8 12 (join 92 4 4 single_6_92 single_6_96) (join 100 4 8 single_6_100 (join 104 4 4 single_6_104 single_6_108)))) (join 112 20 19 (join 112 8 12 (join 112 4 4 single_6_112 single_6_116) (join 120 4 8 single_6_120 (join 124 4 4 single_6_124 single_6_128))) (join 132 8 11 (join 132 4 4 single_6_132 single_6_136) (join 140 4 7 single_6_140 (join 144 4 3 single_6_144 single_6_148))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_6_0 : ∀ i ∈ List.range 4, PhaseAt 6 (0+i) := by decide +kernel

theorem phase_6_4 : ∀ i ∈ List.range 4, PhaseAt 6 (4+i) := by decide +kernel

theorem phase_6_8 : ∀ i ∈ List.range 4, PhaseAt 6 (8+i) := by decide +kernel

theorem phase_6_12 : ∀ i ∈ List.range 4, PhaseAt 6 (12+i) := by decide +kernel

theorem phase_6_16 : ∀ i ∈ List.range 4, PhaseAt 6 (16+i) := by decide +kernel

theorem phase_6_20 : ∀ i ∈ List.range 4, PhaseAt 6 (20+i) := by decide +kernel

theorem phase_6_24 : ∀ i ∈ List.range 4, PhaseAt 6 (24+i) := by decide +kernel

theorem phase_6_28 : ∀ i ∈ List.range 4, PhaseAt 6 (28+i) := by decide +kernel

theorem phase_6_32 : ∀ i ∈ List.range 4, PhaseAt 6 (32+i) := by decide +kernel

theorem phase_6_36 : ∀ i ∈ List.range 4, PhaseAt 6 (36+i) := by decide +kernel

theorem phase_6_40 : ∀ i ∈ List.range 4, PhaseAt 6 (40+i) := by decide +kernel

theorem phase_6_44 : ∀ i ∈ List.range 4, PhaseAt 6 (44+i) := by decide +kernel

theorem phase_6_48 : ∀ i ∈ List.range 4, PhaseAt 6 (48+i) := by decide +kernel

theorem phase_6_52 : ∀ i ∈ List.range 4, PhaseAt 6 (52+i) := by decide +kernel

theorem phase_6_56 : ∀ i ∈ List.range 4, PhaseAt 6 (56+i) := by decide +kernel

theorem phase_6_60 : ∀ i ∈ List.range 4, PhaseAt 6 (60+i) := by decide +kernel

theorem phase_6_64 : ∀ i ∈ List.range 4, PhaseAt 6 (64+i) := by decide +kernel

theorem phase_6_68 : ∀ i ∈ List.range 4, PhaseAt 6 (68+i) := by decide +kernel

theorem phase_6_72 : ∀ i ∈ List.range 4, PhaseAt 6 (72+i) := by decide +kernel

theorem phase_6_76 : ∀ i ∈ List.range 4, PhaseAt 6 (76+i) := by decide +kernel

theorem phase_6_80 : ∀ i ∈ List.range 4, PhaseAt 6 (80+i) := by decide +kernel

theorem phase_6_84 : ∀ i ∈ List.range 4, PhaseAt 6 (84+i) := by decide +kernel

theorem phase_6_88 : ∀ i ∈ List.range 4, PhaseAt 6 (88+i) := by decide +kernel

theorem phase_6_92 : ∀ i ∈ List.range 4, PhaseAt 6 (92+i) := by decide +kernel

theorem phase_6_96 : ∀ i ∈ List.range 4, PhaseAt 6 (96+i) := by decide +kernel

theorem phase_6_100 : ∀ i ∈ List.range 4, PhaseAt 6 (100+i) := by decide +kernel

theorem phase_6_104 : ∀ i ∈ List.range 4, PhaseAt 6 (104+i) := by decide +kernel

theorem phase_6_108 : ∀ i ∈ List.range 4, PhaseAt 6 (108+i) := by decide +kernel

theorem phase_6_112 : ∀ i ∈ List.range 4, PhaseAt 6 (112+i) := by decide +kernel

theorem phase_6_116 : ∀ i ∈ List.range 4, PhaseAt 6 (116+i) := by decide +kernel

theorem phase_6_120 : ∀ i ∈ List.range 4, PhaseAt 6 (120+i) := by decide +kernel

theorem phase_6_124 : ∀ i ∈ List.range 4, PhaseAt 6 (124+i) := by decide +kernel

theorem phase_6_128 : ∀ i ∈ List.range 4, PhaseAt 6 (128+i) := by decide +kernel

theorem phase_6_132 : ∀ i ∈ List.range 4, PhaseAt 6 (132+i) := by decide +kernel

theorem phase_6_136 : ∀ i ∈ List.range 4, PhaseAt 6 (136+i) := by decide +kernel

theorem phase_6_140 : ∀ i ∈ List.range 4, PhaseAt 6 (140+i) := by decide +kernel

theorem phase_6_144 : ∀ i ∈ List.range 4, PhaseAt 6 (144+i) := by decide +kernel

theorem phase_6_148 : ∀ i ∈ List.range 3, PhaseAt 6 (148+i) := by decide +kernel

theorem phase_6 (v : ℕ) (hv : v ∈ List.range 151) : PhaseAt 6 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 6 v)
  have h := (join 0 76 75 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_6_0 phase_6_4) (join 8 4 4 phase_6_8 phase_6_12)) (join 16 8 12 (join 16 4 4 phase_6_16 phase_6_20) (join 24 4 8 phase_6_24 (join 28 4 4 phase_6_28 phase_6_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 phase_6_36 phase_6_40) (join 44 4 8 phase_6_44 (join 48 4 4 phase_6_48 phase_6_52))) (join 56 8 12 (join 56 4 4 phase_6_56 phase_6_60) (join 64 4 8 phase_6_64 (join 68 4 4 phase_6_68 phase_6_72))))) (join 76 36 39 (join 76 16 20 (join 76 8 8 (join 76 4 4 phase_6_76 phase_6_80) (join 84 4 4 phase_6_84 phase_6_88)) (join 92 8 12 (join 92 4 4 phase_6_92 phase_6_96) (join 100 4 8 phase_6_100 (join 104 4 4 phase_6_104 phase_6_108)))) (join 112 20 19 (join 112 8 12 (join 112 4 4 phase_6_112 phase_6_116) (join 120 4 8 phase_6_120 (join 124 4 4 phase_6_124 phase_6_128))) (join 132 8 11 (join 132 4 4 phase_6_132 phase_6_136) (join 140 4 7 phase_6_140 (join 144 4 3 phase_6_144 phase_6_148))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_6_0 : ∀ i ∈ List.range 1, ThresholdAt 6 (0+i) := by decide +kernel

theorem threshold_6_1 : ∀ i ∈ List.range 1, ThresholdAt 6 (1+i) := by decide +kernel

theorem threshold_6_2 : ∀ i ∈ List.range 1, ThresholdAt 6 (2+i) := by decide +kernel

theorem threshold_6_3 : ∀ i ∈ List.range 1, ThresholdAt 6 (3+i) := by decide +kernel

theorem threshold_6_4 : ∀ i ∈ List.range 1, ThresholdAt 6 (4+i) := by decide +kernel

theorem threshold_6_5 : ∀ i ∈ List.range 1, ThresholdAt 6 (5+i) := by decide +kernel

theorem threshold_6_6 : ∀ i ∈ List.range 1, ThresholdAt 6 (6+i) := by decide +kernel

theorem threshold_6_7 : ∀ i ∈ List.range 1, ThresholdAt 6 (7+i) := by decide +kernel

theorem threshold_6_8 : ∀ i ∈ List.range 1, ThresholdAt 6 (8+i) := by decide +kernel

theorem threshold_6_9 : ∀ i ∈ List.range 1, ThresholdAt 6 (9+i) := by decide +kernel

theorem threshold_6_10 : ∀ i ∈ List.range 1, ThresholdAt 6 (10+i) := by decide +kernel

theorem threshold_6_11 : ∀ i ∈ List.range 1, ThresholdAt 6 (11+i) := by decide +kernel

theorem threshold_6_12 : ∀ i ∈ List.range 1, ThresholdAt 6 (12+i) := by decide +kernel

theorem threshold_6_13 : ∀ i ∈ List.range 1, ThresholdAt 6 (13+i) := by decide +kernel

theorem threshold_6_14 : ∀ i ∈ List.range 1, ThresholdAt 6 (14+i) := by decide +kernel

theorem threshold_6_15 : ∀ i ∈ List.range 1, ThresholdAt 6 (15+i) := by decide +kernel

theorem threshold_6_16 : ∀ i ∈ List.range 1, ThresholdAt 6 (16+i) := by decide +kernel

theorem threshold_6_17 : ∀ i ∈ List.range 1, ThresholdAt 6 (17+i) := by decide +kernel

theorem threshold_6_18 : ∀ i ∈ List.range 1, ThresholdAt 6 (18+i) := by decide +kernel

theorem threshold_6_19 : ∀ i ∈ List.range 1, ThresholdAt 6 (19+i) := by decide +kernel

theorem threshold_6_20 : ∀ i ∈ List.range 1, ThresholdAt 6 (20+i) := by decide +kernel

theorem threshold_6_21 : ∀ i ∈ List.range 1, ThresholdAt 6 (21+i) := by decide +kernel

theorem threshold_6_22 : ∀ i ∈ List.range 1, ThresholdAt 6 (22+i) := by decide +kernel

theorem threshold_6_23 : ∀ i ∈ List.range 1, ThresholdAt 6 (23+i) := by decide +kernel

theorem threshold_6_24 : ∀ i ∈ List.range 1, ThresholdAt 6 (24+i) := by decide +kernel

theorem threshold_6_25 : ∀ i ∈ List.range 1, ThresholdAt 6 (25+i) := by decide +kernel

theorem threshold_6_26 : ∀ i ∈ List.range 1, ThresholdAt 6 (26+i) := by decide +kernel

theorem threshold_6_27 : ∀ i ∈ List.range 1, ThresholdAt 6 (27+i) := by decide +kernel

theorem threshold_6_28 : ∀ i ∈ List.range 1, ThresholdAt 6 (28+i) := by decide +kernel

theorem threshold_6_29 : ∀ i ∈ List.range 1, ThresholdAt 6 (29+i) := by decide +kernel

theorem threshold_6_30 : ∀ i ∈ List.range 1, ThresholdAt 6 (30+i) := by decide +kernel

theorem threshold_6_31 : ∀ i ∈ List.range 1, ThresholdAt 6 (31+i) := by decide +kernel

theorem threshold_6_32 : ∀ i ∈ List.range 1, ThresholdAt 6 (32+i) := by decide +kernel

theorem threshold_6_33 : ∀ i ∈ List.range 1, ThresholdAt 6 (33+i) := by decide +kernel

theorem threshold_6_34 : ∀ i ∈ List.range 1, ThresholdAt 6 (34+i) := by decide +kernel

theorem threshold_6_35 : ∀ i ∈ List.range 1, ThresholdAt 6 (35+i) := by decide +kernel

theorem threshold_6_36 : ∀ i ∈ List.range 1, ThresholdAt 6 (36+i) := by decide +kernel

theorem threshold_6_37 : ∀ i ∈ List.range 1, ThresholdAt 6 (37+i) := by decide +kernel

theorem threshold_6_38 : ∀ i ∈ List.range 1, ThresholdAt 6 (38+i) := by decide +kernel

theorem threshold_6_39 : ∀ i ∈ List.range 1, ThresholdAt 6 (39+i) := by decide +kernel

theorem threshold_6_40 : ∀ i ∈ List.range 1, ThresholdAt 6 (40+i) := by decide +kernel

theorem threshold_6_41 : ∀ i ∈ List.range 1, ThresholdAt 6 (41+i) := by decide +kernel

theorem threshold_6_42 : ∀ i ∈ List.range 1, ThresholdAt 6 (42+i) := by decide +kernel

theorem threshold_6_43 : ∀ i ∈ List.range 1, ThresholdAt 6 (43+i) := by decide +kernel

theorem threshold_6_44 : ∀ i ∈ List.range 1, ThresholdAt 6 (44+i) := by decide +kernel

theorem threshold_6_45 : ∀ i ∈ List.range 1, ThresholdAt 6 (45+i) := by decide +kernel

theorem threshold_6_46 : ∀ i ∈ List.range 1, ThresholdAt 6 (46+i) := by decide +kernel

theorem threshold_6_47 : ∀ i ∈ List.range 1, ThresholdAt 6 (47+i) := by decide +kernel

theorem threshold_6_48 : ∀ i ∈ List.range 1, ThresholdAt 6 (48+i) := by decide +kernel

theorem threshold_6_49 : ∀ i ∈ List.range 1, ThresholdAt 6 (49+i) := by decide +kernel

theorem threshold_6_50 : ∀ i ∈ List.range 1, ThresholdAt 6 (50+i) := by decide +kernel

theorem threshold_6_51 : ∀ i ∈ List.range 1, ThresholdAt 6 (51+i) := by decide +kernel

theorem threshold_6_52 : ∀ i ∈ List.range 1, ThresholdAt 6 (52+i) := by decide +kernel

theorem threshold_6_53 : ∀ i ∈ List.range 1, ThresholdAt 6 (53+i) := by decide +kernel

theorem threshold_6_54 : ∀ i ∈ List.range 1, ThresholdAt 6 (54+i) := by decide +kernel

theorem threshold_6_55 : ∀ i ∈ List.range 1, ThresholdAt 6 (55+i) := by decide +kernel

theorem threshold_6_56 : ∀ i ∈ List.range 1, ThresholdAt 6 (56+i) := by decide +kernel

theorem threshold_6_57 : ∀ i ∈ List.range 1, ThresholdAt 6 (57+i) := by decide +kernel

theorem threshold_6_58 : ∀ i ∈ List.range 1, ThresholdAt 6 (58+i) := by decide +kernel

theorem threshold_6_59 : ∀ i ∈ List.range 1, ThresholdAt 6 (59+i) := by decide +kernel

theorem threshold_6_60 : ∀ i ∈ List.range 1, ThresholdAt 6 (60+i) := by decide +kernel

theorem threshold_6_61 : ∀ i ∈ List.range 1, ThresholdAt 6 (61+i) := by decide +kernel

theorem threshold_6_62 : ∀ i ∈ List.range 1, ThresholdAt 6 (62+i) := by decide +kernel

theorem threshold_6_63 : ∀ i ∈ List.range 1, ThresholdAt 6 (63+i) := by decide +kernel

theorem threshold_6_64 : ∀ i ∈ List.range 1, ThresholdAt 6 (64+i) := by decide +kernel

theorem threshold_6_65 : ∀ i ∈ List.range 1, ThresholdAt 6 (65+i) := by decide +kernel

theorem threshold_6_66 : ∀ i ∈ List.range 1, ThresholdAt 6 (66+i) := by decide +kernel

theorem threshold_6_67 : ∀ i ∈ List.range 1, ThresholdAt 6 (67+i) := by decide +kernel

theorem threshold_6_68 : ∀ i ∈ List.range 1, ThresholdAt 6 (68+i) := by decide +kernel

theorem threshold_6_69 : ∀ i ∈ List.range 1, ThresholdAt 6 (69+i) := by decide +kernel

theorem threshold_6_70 : ∀ i ∈ List.range 1, ThresholdAt 6 (70+i) := by decide +kernel

theorem threshold_6_71 : ∀ i ∈ List.range 1, ThresholdAt 6 (71+i) := by decide +kernel

theorem threshold_6_72 : ∀ i ∈ List.range 1, ThresholdAt 6 (72+i) := by decide +kernel

theorem threshold_6_73 : ∀ i ∈ List.range 1, ThresholdAt 6 (73+i) := by decide +kernel

theorem threshold_6_74 : ∀ i ∈ List.range 1, ThresholdAt 6 (74+i) := by decide +kernel

theorem threshold_6_75 : ∀ i ∈ List.range 1, ThresholdAt 6 (75+i) := by decide +kernel

theorem threshold_6_76 : ∀ i ∈ List.range 1, ThresholdAt 6 (76+i) := by decide +kernel

theorem threshold_6_77 : ∀ i ∈ List.range 1, ThresholdAt 6 (77+i) := by decide +kernel

theorem threshold_6_78 : ∀ i ∈ List.range 1, ThresholdAt 6 (78+i) := by decide +kernel

theorem threshold_6_79 : ∀ i ∈ List.range 1, ThresholdAt 6 (79+i) := by decide +kernel

theorem threshold_6_80 : ∀ i ∈ List.range 1, ThresholdAt 6 (80+i) := by decide +kernel

theorem threshold_6_81 : ∀ i ∈ List.range 1, ThresholdAt 6 (81+i) := by decide +kernel

theorem threshold_6_82 : ∀ i ∈ List.range 1, ThresholdAt 6 (82+i) := by decide +kernel

theorem threshold_6_83 : ∀ i ∈ List.range 1, ThresholdAt 6 (83+i) := by decide +kernel

theorem threshold_6_84 : ∀ i ∈ List.range 1, ThresholdAt 6 (84+i) := by decide +kernel

theorem threshold_6_85 : ∀ i ∈ List.range 1, ThresholdAt 6 (85+i) := by decide +kernel

theorem threshold_6_86 : ∀ i ∈ List.range 1, ThresholdAt 6 (86+i) := by decide +kernel

theorem threshold_6_87 : ∀ i ∈ List.range 1, ThresholdAt 6 (87+i) := by decide +kernel

theorem threshold_6_88 : ∀ i ∈ List.range 1, ThresholdAt 6 (88+i) := by decide +kernel

theorem threshold_6_89 : ∀ i ∈ List.range 1, ThresholdAt 6 (89+i) := by decide +kernel

theorem threshold_6_90 : ∀ i ∈ List.range 1, ThresholdAt 6 (90+i) := by decide +kernel

theorem threshold_6_91 : ∀ i ∈ List.range 1, ThresholdAt 6 (91+i) := by decide +kernel

theorem threshold_6_92 : ∀ i ∈ List.range 1, ThresholdAt 6 (92+i) := by decide +kernel

theorem threshold_6_93 : ∀ i ∈ List.range 1, ThresholdAt 6 (93+i) := by decide +kernel

theorem threshold_6_94 : ∀ i ∈ List.range 1, ThresholdAt 6 (94+i) := by decide +kernel

theorem threshold_6_95 : ∀ i ∈ List.range 1, ThresholdAt 6 (95+i) := by decide +kernel

theorem threshold_6_96 : ∀ i ∈ List.range 1, ThresholdAt 6 (96+i) := by decide +kernel

theorem threshold_6_97 : ∀ i ∈ List.range 1, ThresholdAt 6 (97+i) := by decide +kernel

theorem threshold_6_98 : ∀ i ∈ List.range 1, ThresholdAt 6 (98+i) := by decide +kernel

theorem threshold_6_99 : ∀ i ∈ List.range 1, ThresholdAt 6 (99+i) := by decide +kernel

theorem threshold_6_100 : ∀ i ∈ List.range 1, ThresholdAt 6 (100+i) := by decide +kernel

theorem threshold_6_101 : ∀ i ∈ List.range 1, ThresholdAt 6 (101+i) := by decide +kernel

theorem threshold_6_102 : ∀ i ∈ List.range 1, ThresholdAt 6 (102+i) := by decide +kernel

theorem threshold_6_103 : ∀ i ∈ List.range 1, ThresholdAt 6 (103+i) := by decide +kernel

theorem threshold_6_104 : ∀ i ∈ List.range 1, ThresholdAt 6 (104+i) := by decide +kernel

theorem threshold_6_105 : ∀ i ∈ List.range 1, ThresholdAt 6 (105+i) := by decide +kernel

theorem threshold_6_106 : ∀ i ∈ List.range 1, ThresholdAt 6 (106+i) := by decide +kernel

theorem threshold_6_107 : ∀ i ∈ List.range 1, ThresholdAt 6 (107+i) := by decide +kernel

theorem threshold_6_108 : ∀ i ∈ List.range 1, ThresholdAt 6 (108+i) := by decide +kernel

theorem threshold_6_109 : ∀ i ∈ List.range 1, ThresholdAt 6 (109+i) := by decide +kernel

theorem threshold_6_110 : ∀ i ∈ List.range 1, ThresholdAt 6 (110+i) := by decide +kernel

theorem threshold_6_111 : ∀ i ∈ List.range 1, ThresholdAt 6 (111+i) := by decide +kernel

theorem threshold_6_112 : ∀ i ∈ List.range 1, ThresholdAt 6 (112+i) := by decide +kernel

theorem threshold_6_113 : ∀ i ∈ List.range 1, ThresholdAt 6 (113+i) := by decide +kernel

theorem threshold_6_114 : ∀ i ∈ List.range 1, ThresholdAt 6 (114+i) := by decide +kernel

theorem threshold_6_115 : ∀ i ∈ List.range 1, ThresholdAt 6 (115+i) := by decide +kernel

theorem threshold_6_116 : ∀ i ∈ List.range 1, ThresholdAt 6 (116+i) := by decide +kernel

theorem threshold_6_117 : ∀ i ∈ List.range 1, ThresholdAt 6 (117+i) := by decide +kernel

theorem threshold_6_118 : ∀ i ∈ List.range 1, ThresholdAt 6 (118+i) := by decide +kernel

theorem threshold_6_119 : ∀ i ∈ List.range 1, ThresholdAt 6 (119+i) := by decide +kernel

theorem threshold_6_120 : ∀ i ∈ List.range 1, ThresholdAt 6 (120+i) := by decide +kernel

theorem threshold_6_121 : ∀ i ∈ List.range 1, ThresholdAt 6 (121+i) := by decide +kernel

theorem threshold_6_122 : ∀ i ∈ List.range 1, ThresholdAt 6 (122+i) := by decide +kernel

theorem threshold_6_123 : ∀ i ∈ List.range 1, ThresholdAt 6 (123+i) := by decide +kernel

theorem threshold_6_124 : ∀ i ∈ List.range 1, ThresholdAt 6 (124+i) := by decide +kernel

theorem threshold_6_125 : ∀ i ∈ List.range 1, ThresholdAt 6 (125+i) := by decide +kernel

theorem threshold_6_126 : ∀ i ∈ List.range 1, ThresholdAt 6 (126+i) := by decide +kernel

theorem threshold_6_127 : ∀ i ∈ List.range 1, ThresholdAt 6 (127+i) := by decide +kernel

theorem threshold_6_128 : ∀ i ∈ List.range 1, ThresholdAt 6 (128+i) := by decide +kernel

theorem threshold_6_129 : ∀ i ∈ List.range 1, ThresholdAt 6 (129+i) := by decide +kernel

theorem threshold_6_130 : ∀ i ∈ List.range 1, ThresholdAt 6 (130+i) := by decide +kernel

theorem threshold_6_131 : ∀ i ∈ List.range 1, ThresholdAt 6 (131+i) := by decide +kernel

theorem threshold_6_132 : ∀ i ∈ List.range 1, ThresholdAt 6 (132+i) := by decide +kernel

theorem threshold_6_133 : ∀ i ∈ List.range 1, ThresholdAt 6 (133+i) := by decide +kernel

theorem threshold_6_134 : ∀ i ∈ List.range 1, ThresholdAt 6 (134+i) := by decide +kernel

theorem threshold_6_135 : ∀ i ∈ List.range 1, ThresholdAt 6 (135+i) := by decide +kernel

theorem threshold_6_136 : ∀ i ∈ List.range 1, ThresholdAt 6 (136+i) := by decide +kernel

theorem threshold_6_137 : ∀ i ∈ List.range 1, ThresholdAt 6 (137+i) := by decide +kernel

theorem threshold_6_138 : ∀ i ∈ List.range 1, ThresholdAt 6 (138+i) := by decide +kernel

theorem threshold_6_139 : ∀ i ∈ List.range 1, ThresholdAt 6 (139+i) := by decide +kernel

theorem threshold_6_140 : ∀ i ∈ List.range 1, ThresholdAt 6 (140+i) := by decide +kernel

theorem threshold_6_141 : ∀ i ∈ List.range 1, ThresholdAt 6 (141+i) := by decide +kernel

theorem threshold_6_142 : ∀ i ∈ List.range 1, ThresholdAt 6 (142+i) := by decide +kernel

theorem threshold_6_143 : ∀ i ∈ List.range 1, ThresholdAt 6 (143+i) := by decide +kernel

theorem threshold_6_144 : ∀ i ∈ List.range 1, ThresholdAt 6 (144+i) := by decide +kernel

theorem threshold_6_145 : ∀ i ∈ List.range 1, ThresholdAt 6 (145+i) := by decide +kernel

theorem threshold_6_146 : ∀ i ∈ List.range 1, ThresholdAt 6 (146+i) := by decide +kernel

theorem threshold_6_147 : ∀ i ∈ List.range 1, ThresholdAt 6 (147+i) := by decide +kernel

theorem threshold_6_148 : ∀ i ∈ List.range 1, ThresholdAt 6 (148+i) := by decide +kernel

theorem threshold_6_149 : ∀ i ∈ List.range 1, ThresholdAt 6 (149+i) := by decide +kernel

theorem threshold_6_150 : ∀ i ∈ List.range 1, ThresholdAt 6 (150+i) := by decide +kernel

theorem threshold_6 (v : ℕ) (hv : v ∈ List.range 151) : ThresholdAt 6 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 6 v)
  have h := (join 0 75 76 (join 0 37 38 (join 0 18 19 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_6_0 threshold_6_1) (join 2 1 1 threshold_6_2 threshold_6_3)) (join 4 2 3 (join 4 1 1 threshold_6_4 threshold_6_5) (join 6 1 2 threshold_6_6 (join 7 1 1 threshold_6_7 threshold_6_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 threshold_6_9 threshold_6_10) (join 11 1 1 threshold_6_11 threshold_6_12)) (join 13 2 3 (join 13 1 1 threshold_6_13 threshold_6_14) (join 15 1 2 threshold_6_15 (join 16 1 1 threshold_6_16 threshold_6_17))))) (join 18 9 10 (join 18 4 5 (join 18 2 2 (join 18 1 1 threshold_6_18 threshold_6_19) (join 20 1 1 threshold_6_20 threshold_6_21)) (join 22 2 3 (join 22 1 1 threshold_6_22 threshold_6_23) (join 24 1 2 threshold_6_24 (join 25 1 1 threshold_6_25 threshold_6_26)))) (join 27 5 5 (join 27 2 3 (join 27 1 1 threshold_6_27 threshold_6_28) (join 29 1 2 threshold_6_29 (join 30 1 1 threshold_6_30 threshold_6_31))) (join 32 2 3 (join 32 1 1 threshold_6_32 threshold_6_33) (join 34 1 2 threshold_6_34 (join 35 1 1 threshold_6_35 threshold_6_36)))))) (join 37 19 19 (join 37 9 10 (join 37 4 5 (join 37 2 2 (join 37 1 1 threshold_6_37 threshold_6_38) (join 39 1 1 threshold_6_39 threshold_6_40)) (join 41 2 3 (join 41 1 1 threshold_6_41 threshold_6_42) (join 43 1 2 threshold_6_43 (join 44 1 1 threshold_6_44 threshold_6_45)))) (join 46 5 5 (join 46 2 3 (join 46 1 1 threshold_6_46 threshold_6_47) (join 48 1 2 threshold_6_48 (join 49 1 1 threshold_6_49 threshold_6_50))) (join 51 2 3 (join 51 1 1 threshold_6_51 threshold_6_52) (join 53 1 2 threshold_6_53 (join 54 1 1 threshold_6_54 threshold_6_55))))) (join 56 9 10 (join 56 4 5 (join 56 2 2 (join 56 1 1 threshold_6_56 threshold_6_57) (join 58 1 1 threshold_6_58 threshold_6_59)) (join 60 2 3 (join 60 1 1 threshold_6_60 threshold_6_61) (join 62 1 2 threshold_6_62 (join 63 1 1 threshold_6_63 threshold_6_64)))) (join 65 5 5 (join 65 2 3 (join 65 1 1 threshold_6_65 threshold_6_66) (join 67 1 2 threshold_6_67 (join 68 1 1 threshold_6_68 threshold_6_69))) (join 70 2 3 (join 70 1 1 threshold_6_70 threshold_6_71) (join 72 1 2 threshold_6_72 (join 73 1 1 threshold_6_73 threshold_6_74))))))) (join 75 38 38 (join 75 19 19 (join 75 9 10 (join 75 4 5 (join 75 2 2 (join 75 1 1 threshold_6_75 threshold_6_76) (join 77 1 1 threshold_6_77 threshold_6_78)) (join 79 2 3 (join 79 1 1 threshold_6_79 threshold_6_80) (join 81 1 2 threshold_6_81 (join 82 1 1 threshold_6_82 threshold_6_83)))) (join 84 5 5 (join 84 2 3 (join 84 1 1 threshold_6_84 threshold_6_85) (join 86 1 2 threshold_6_86 (join 87 1 1 threshold_6_87 threshold_6_88))) (join 89 2 3 (join 89 1 1 threshold_6_89 threshold_6_90) (join 91 1 2 threshold_6_91 (join 92 1 1 threshold_6_92 threshold_6_93))))) (join 94 9 10 (join 94 4 5 (join 94 2 2 (join 94 1 1 threshold_6_94 threshold_6_95) (join 96 1 1 threshold_6_96 threshold_6_97)) (join 98 2 3 (join 98 1 1 threshold_6_98 threshold_6_99) (join 100 1 2 threshold_6_100 (join 101 1 1 threshold_6_101 threshold_6_102)))) (join 103 5 5 (join 103 2 3 (join 103 1 1 threshold_6_103 threshold_6_104) (join 105 1 2 threshold_6_105 (join 106 1 1 threshold_6_106 threshold_6_107))) (join 108 2 3 (join 108 1 1 threshold_6_108 threshold_6_109) (join 110 1 2 threshold_6_110 (join 111 1 1 threshold_6_111 threshold_6_112)))))) (join 113 19 19 (join 113 9 10 (join 113 4 5 (join 113 2 2 (join 113 1 1 threshold_6_113 threshold_6_114) (join 115 1 1 threshold_6_115 threshold_6_116)) (join 117 2 3 (join 117 1 1 threshold_6_117 threshold_6_118) (join 119 1 2 threshold_6_119 (join 120 1 1 threshold_6_120 threshold_6_121)))) (join 122 5 5 (join 122 2 3 (join 122 1 1 threshold_6_122 threshold_6_123) (join 124 1 2 threshold_6_124 (join 125 1 1 threshold_6_125 threshold_6_126))) (join 127 2 3 (join 127 1 1 threshold_6_127 threshold_6_128) (join 129 1 2 threshold_6_129 (join 130 1 1 threshold_6_130 threshold_6_131))))) (join 132 9 10 (join 132 4 5 (join 132 2 2 (join 132 1 1 threshold_6_132 threshold_6_133) (join 134 1 1 threshold_6_134 threshold_6_135)) (join 136 2 3 (join 136 1 1 threshold_6_136 threshold_6_137) (join 138 1 2 threshold_6_138 (join 139 1 1 threshold_6_139 threshold_6_140)))) (join 141 5 5 (join 141 2 3 (join 141 1 1 threshold_6_141 threshold_6_142) (join 143 1 2 threshold_6_143 (join 144 1 1 threshold_6_144 threshold_6_145))) (join 146 2 3 (join 146 1 1 threshold_6_146 threshold_6_147) (join 148 1 2 threshold_6_148 (join 149 1 1 threshold_6_149 threshold_6_150))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_6_0 : ∀ i ∈ List.range 4, LedgerAt 6 (0+i) := by decide +kernel

theorem ledger_6_4 : ∀ i ∈ List.range 4, LedgerAt 6 (4+i) := by decide +kernel

theorem ledger_6_8 : ∀ i ∈ List.range 4, LedgerAt 6 (8+i) := by decide +kernel

theorem ledger_6_12 : ∀ i ∈ List.range 4, LedgerAt 6 (12+i) := by decide +kernel

theorem ledger_6_16 : ∀ i ∈ List.range 4, LedgerAt 6 (16+i) := by decide +kernel

theorem ledger_6_20 : ∀ i ∈ List.range 4, LedgerAt 6 (20+i) := by decide +kernel

theorem ledger_6_24 : ∀ i ∈ List.range 4, LedgerAt 6 (24+i) := by decide +kernel

theorem ledger_6_28 : ∀ i ∈ List.range 4, LedgerAt 6 (28+i) := by decide +kernel

theorem ledger_6_32 : ∀ i ∈ List.range 4, LedgerAt 6 (32+i) := by decide +kernel

theorem ledger_6_36 : ∀ i ∈ List.range 4, LedgerAt 6 (36+i) := by decide +kernel

theorem ledger_6_40 : ∀ i ∈ List.range 4, LedgerAt 6 (40+i) := by decide +kernel

theorem ledger_6_44 : ∀ i ∈ List.range 4, LedgerAt 6 (44+i) := by decide +kernel

theorem ledger_6_48 : ∀ i ∈ List.range 4, LedgerAt 6 (48+i) := by decide +kernel

theorem ledger_6_52 : ∀ i ∈ List.range 4, LedgerAt 6 (52+i) := by decide +kernel

theorem ledger_6_56 : ∀ i ∈ List.range 4, LedgerAt 6 (56+i) := by decide +kernel

theorem ledger_6_60 : ∀ i ∈ List.range 4, LedgerAt 6 (60+i) := by decide +kernel

theorem ledger_6_64 : ∀ i ∈ List.range 4, LedgerAt 6 (64+i) := by decide +kernel

theorem ledger_6_68 : ∀ i ∈ List.range 4, LedgerAt 6 (68+i) := by decide +kernel

theorem ledger_6_72 : ∀ i ∈ List.range 4, LedgerAt 6 (72+i) := by decide +kernel

theorem ledger_6_76 : ∀ i ∈ List.range 4, LedgerAt 6 (76+i) := by decide +kernel

theorem ledger_6_80 : ∀ i ∈ List.range 4, LedgerAt 6 (80+i) := by decide +kernel

theorem ledger_6_84 : ∀ i ∈ List.range 4, LedgerAt 6 (84+i) := by decide +kernel

theorem ledger_6_88 : ∀ i ∈ List.range 4, LedgerAt 6 (88+i) := by decide +kernel

theorem ledger_6_92 : ∀ i ∈ List.range 4, LedgerAt 6 (92+i) := by decide +kernel

theorem ledger_6_96 : ∀ i ∈ List.range 4, LedgerAt 6 (96+i) := by decide +kernel

theorem ledger_6_100 : ∀ i ∈ List.range 4, LedgerAt 6 (100+i) := by decide +kernel

theorem ledger_6_104 : ∀ i ∈ List.range 4, LedgerAt 6 (104+i) := by decide +kernel

theorem ledger_6_108 : ∀ i ∈ List.range 4, LedgerAt 6 (108+i) := by decide +kernel

theorem ledger_6_112 : ∀ i ∈ List.range 4, LedgerAt 6 (112+i) := by decide +kernel

theorem ledger_6_116 : ∀ i ∈ List.range 4, LedgerAt 6 (116+i) := by decide +kernel

theorem ledger_6_120 : ∀ i ∈ List.range 4, LedgerAt 6 (120+i) := by decide +kernel

theorem ledger_6_124 : ∀ i ∈ List.range 4, LedgerAt 6 (124+i) := by decide +kernel

theorem ledger_6_128 : ∀ i ∈ List.range 4, LedgerAt 6 (128+i) := by decide +kernel

theorem ledger_6_132 : ∀ i ∈ List.range 4, LedgerAt 6 (132+i) := by decide +kernel

theorem ledger_6_136 : ∀ i ∈ List.range 4, LedgerAt 6 (136+i) := by decide +kernel

theorem ledger_6_140 : ∀ i ∈ List.range 4, LedgerAt 6 (140+i) := by decide +kernel

theorem ledger_6_144 : ∀ i ∈ List.range 4, LedgerAt 6 (144+i) := by decide +kernel

theorem ledger_6_148 : ∀ i ∈ List.range 3, LedgerAt 6 (148+i) := by decide +kernel

theorem ledger_6 (v : ℕ) (hv : v ∈ List.range 151) : LedgerAt 6 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 6 v)
  have h := (join 0 76 75 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_6_0 ledger_6_4) (join 8 4 4 ledger_6_8 ledger_6_12)) (join 16 8 12 (join 16 4 4 ledger_6_16 ledger_6_20) (join 24 4 8 ledger_6_24 (join 28 4 4 ledger_6_28 ledger_6_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 ledger_6_36 ledger_6_40) (join 44 4 8 ledger_6_44 (join 48 4 4 ledger_6_48 ledger_6_52))) (join 56 8 12 (join 56 4 4 ledger_6_56 ledger_6_60) (join 64 4 8 ledger_6_64 (join 68 4 4 ledger_6_68 ledger_6_72))))) (join 76 36 39 (join 76 16 20 (join 76 8 8 (join 76 4 4 ledger_6_76 ledger_6_80) (join 84 4 4 ledger_6_84 ledger_6_88)) (join 92 8 12 (join 92 4 4 ledger_6_92 ledger_6_96) (join 100 4 8 ledger_6_100 (join 104 4 4 ledger_6_104 ledger_6_108)))) (join 112 20 19 (join 112 8 12 (join 112 4 4 ledger_6_112 ledger_6_116) (join 120 4 8 ledger_6_120 (join 124 4 4 ledger_6_124 ledger_6_128))) (join 132 8 11 (join 132 4 4 ledger_6_132 ledger_6_136) (join 140 4 7 ledger_6_140 (join 144 4 3 ledger_6_144 ledger_6_148))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
