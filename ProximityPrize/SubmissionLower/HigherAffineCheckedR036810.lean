import ProximityPrize.SubmissionLower.HigherAffineCheckedR026810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_3_0 : ∀ i ∈ List.range 4, SingleAt 3 (0+i) := by decide +kernel

theorem single_3_4 : ∀ i ∈ List.range 4, SingleAt 3 (4+i) := by decide +kernel

theorem single_3_8 : ∀ i ∈ List.range 4, SingleAt 3 (8+i) := by decide +kernel

theorem single_3_12 : ∀ i ∈ List.range 4, SingleAt 3 (12+i) := by decide +kernel

theorem single_3_16 : ∀ i ∈ List.range 4, SingleAt 3 (16+i) := by decide +kernel

theorem single_3_20 : ∀ i ∈ List.range 4, SingleAt 3 (20+i) := by decide +kernel

theorem single_3_24 : ∀ i ∈ List.range 4, SingleAt 3 (24+i) := by decide +kernel

theorem single_3_28 : ∀ i ∈ List.range 4, SingleAt 3 (28+i) := by decide +kernel

theorem single_3_32 : ∀ i ∈ List.range 4, SingleAt 3 (32+i) := by decide +kernel

theorem single_3_36 : ∀ i ∈ List.range 4, SingleAt 3 (36+i) := by decide +kernel

theorem single_3_40 : ∀ i ∈ List.range 4, SingleAt 3 (40+i) := by decide +kernel

theorem single_3_44 : ∀ i ∈ List.range 4, SingleAt 3 (44+i) := by decide +kernel

theorem single_3_48 : ∀ i ∈ List.range 4, SingleAt 3 (48+i) := by decide +kernel

theorem single_3_52 : ∀ i ∈ List.range 4, SingleAt 3 (52+i) := by decide +kernel

theorem single_3_56 : ∀ i ∈ List.range 4, SingleAt 3 (56+i) := by decide +kernel

theorem single_3_60 : ∀ i ∈ List.range 4, SingleAt 3 (60+i) := by decide +kernel

theorem single_3_64 : ∀ i ∈ List.range 4, SingleAt 3 (64+i) := by decide +kernel

theorem single_3_68 : ∀ i ∈ List.range 4, SingleAt 3 (68+i) := by decide +kernel

theorem single_3_72 : ∀ i ∈ List.range 4, SingleAt 3 (72+i) := by decide +kernel

theorem single_3_76 : ∀ i ∈ List.range 4, SingleAt 3 (76+i) := by decide +kernel

theorem single_3_80 : ∀ i ∈ List.range 4, SingleAt 3 (80+i) := by decide +kernel

theorem single_3_84 : ∀ i ∈ List.range 4, SingleAt 3 (84+i) := by decide +kernel

theorem single_3_88 : ∀ i ∈ List.range 4, SingleAt 3 (88+i) := by decide +kernel

theorem single_3_92 : ∀ i ∈ List.range 4, SingleAt 3 (92+i) := by decide +kernel

theorem single_3_96 : ∀ i ∈ List.range 4, SingleAt 3 (96+i) := by decide +kernel

theorem single_3_100 : ∀ i ∈ List.range 4, SingleAt 3 (100+i) := by decide +kernel

theorem single_3_104 : ∀ i ∈ List.range 4, SingleAt 3 (104+i) := by decide +kernel

theorem single_3_108 : ∀ i ∈ List.range 4, SingleAt 3 (108+i) := by decide +kernel

theorem single_3_112 : ∀ i ∈ List.range 4, SingleAt 3 (112+i) := by decide +kernel

theorem single_3_116 : ∀ i ∈ List.range 4, SingleAt 3 (116+i) := by decide +kernel

theorem single_3_120 : ∀ i ∈ List.range 4, SingleAt 3 (120+i) := by decide +kernel

theorem single_3_124 : ∀ i ∈ List.range 4, SingleAt 3 (124+i) := by decide +kernel

theorem single_3_128 : ∀ i ∈ List.range 4, SingleAt 3 (128+i) := by decide +kernel

theorem single_3_132 : ∀ i ∈ List.range 4, SingleAt 3 (132+i) := by decide +kernel

theorem single_3_136 : ∀ i ∈ List.range 4, SingleAt 3 (136+i) := by decide +kernel

theorem single_3_140 : ∀ i ∈ List.range 4, SingleAt 3 (140+i) := by decide +kernel

theorem single_3_144 : ∀ i ∈ List.range 4, SingleAt 3 (144+i) := by decide +kernel

theorem single_3_148 : ∀ i ∈ List.range 4, SingleAt 3 (148+i) := by decide +kernel

theorem single_3_152 : ∀ i ∈ List.range 2, SingleAt 3 (152+i) := by decide +kernel

theorem single_3 (v : ℕ) (hv : v ∈ List.range 154) : SingleAt 3 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 3 v)
  have h := (join 0 76 78 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_3_0 single_3_4) (join 8 4 4 single_3_8 single_3_12)) (join 16 8 12 (join 16 4 4 single_3_16 single_3_20) (join 24 4 8 single_3_24 (join 28 4 4 single_3_28 single_3_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 single_3_36 single_3_40) (join 44 4 8 single_3_44 (join 48 4 4 single_3_48 single_3_52))) (join 56 8 12 (join 56 4 4 single_3_56 single_3_60) (join 64 4 8 single_3_64 (join 68 4 4 single_3_68 single_3_72))))) (join 76 40 38 (join 76 20 20 (join 76 8 12 (join 76 4 4 single_3_76 single_3_80) (join 84 4 8 single_3_84 (join 88 4 4 single_3_88 single_3_92))) (join 96 8 12 (join 96 4 4 single_3_96 single_3_100) (join 104 4 8 single_3_104 (join 108 4 4 single_3_108 single_3_112)))) (join 116 20 18 (join 116 8 12 (join 116 4 4 single_3_116 single_3_120) (join 124 4 8 single_3_124 (join 128 4 4 single_3_128 single_3_132))) (join 136 8 10 (join 136 4 4 single_3_136 single_3_140) (join 144 4 6 single_3_144 (join 148 4 2 single_3_148 single_3_152))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_3_0 : ∀ i ∈ List.range 4, PhaseAt 3 (0+i) := by decide +kernel

theorem phase_3_4 : ∀ i ∈ List.range 4, PhaseAt 3 (4+i) := by decide +kernel

theorem phase_3_8 : ∀ i ∈ List.range 4, PhaseAt 3 (8+i) := by decide +kernel

theorem phase_3_12 : ∀ i ∈ List.range 4, PhaseAt 3 (12+i) := by decide +kernel

theorem phase_3_16 : ∀ i ∈ List.range 4, PhaseAt 3 (16+i) := by decide +kernel

theorem phase_3_20 : ∀ i ∈ List.range 4, PhaseAt 3 (20+i) := by decide +kernel

theorem phase_3_24 : ∀ i ∈ List.range 4, PhaseAt 3 (24+i) := by decide +kernel

theorem phase_3_28 : ∀ i ∈ List.range 4, PhaseAt 3 (28+i) := by decide +kernel

theorem phase_3_32 : ∀ i ∈ List.range 4, PhaseAt 3 (32+i) := by decide +kernel

theorem phase_3_36 : ∀ i ∈ List.range 4, PhaseAt 3 (36+i) := by decide +kernel

theorem phase_3_40 : ∀ i ∈ List.range 4, PhaseAt 3 (40+i) := by decide +kernel

theorem phase_3_44 : ∀ i ∈ List.range 4, PhaseAt 3 (44+i) := by decide +kernel

theorem phase_3_48 : ∀ i ∈ List.range 4, PhaseAt 3 (48+i) := by decide +kernel

theorem phase_3_52 : ∀ i ∈ List.range 4, PhaseAt 3 (52+i) := by decide +kernel

theorem phase_3_56 : ∀ i ∈ List.range 4, PhaseAt 3 (56+i) := by decide +kernel

theorem phase_3_60 : ∀ i ∈ List.range 4, PhaseAt 3 (60+i) := by decide +kernel

theorem phase_3_64 : ∀ i ∈ List.range 4, PhaseAt 3 (64+i) := by decide +kernel

theorem phase_3_68 : ∀ i ∈ List.range 4, PhaseAt 3 (68+i) := by decide +kernel

theorem phase_3_72 : ∀ i ∈ List.range 4, PhaseAt 3 (72+i) := by decide +kernel

theorem phase_3_76 : ∀ i ∈ List.range 4, PhaseAt 3 (76+i) := by decide +kernel

theorem phase_3_80 : ∀ i ∈ List.range 4, PhaseAt 3 (80+i) := by decide +kernel

theorem phase_3_84 : ∀ i ∈ List.range 4, PhaseAt 3 (84+i) := by decide +kernel

theorem phase_3_88 : ∀ i ∈ List.range 4, PhaseAt 3 (88+i) := by decide +kernel

theorem phase_3_92 : ∀ i ∈ List.range 4, PhaseAt 3 (92+i) := by decide +kernel

theorem phase_3_96 : ∀ i ∈ List.range 4, PhaseAt 3 (96+i) := by decide +kernel

theorem phase_3_100 : ∀ i ∈ List.range 4, PhaseAt 3 (100+i) := by decide +kernel

theorem phase_3_104 : ∀ i ∈ List.range 4, PhaseAt 3 (104+i) := by decide +kernel

theorem phase_3_108 : ∀ i ∈ List.range 4, PhaseAt 3 (108+i) := by decide +kernel

theorem phase_3_112 : ∀ i ∈ List.range 4, PhaseAt 3 (112+i) := by decide +kernel

theorem phase_3_116 : ∀ i ∈ List.range 4, PhaseAt 3 (116+i) := by decide +kernel

theorem phase_3_120 : ∀ i ∈ List.range 4, PhaseAt 3 (120+i) := by decide +kernel

theorem phase_3_124 : ∀ i ∈ List.range 4, PhaseAt 3 (124+i) := by decide +kernel

theorem phase_3_128 : ∀ i ∈ List.range 4, PhaseAt 3 (128+i) := by decide +kernel

theorem phase_3_132 : ∀ i ∈ List.range 4, PhaseAt 3 (132+i) := by decide +kernel

theorem phase_3_136 : ∀ i ∈ List.range 4, PhaseAt 3 (136+i) := by decide +kernel

theorem phase_3_140 : ∀ i ∈ List.range 4, PhaseAt 3 (140+i) := by decide +kernel

theorem phase_3_144 : ∀ i ∈ List.range 4, PhaseAt 3 (144+i) := by decide +kernel

theorem phase_3_148 : ∀ i ∈ List.range 4, PhaseAt 3 (148+i) := by decide +kernel

theorem phase_3_152 : ∀ i ∈ List.range 2, PhaseAt 3 (152+i) := by decide +kernel

theorem phase_3 (v : ℕ) (hv : v ∈ List.range 154) : PhaseAt 3 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 3 v)
  have h := (join 0 76 78 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_3_0 phase_3_4) (join 8 4 4 phase_3_8 phase_3_12)) (join 16 8 12 (join 16 4 4 phase_3_16 phase_3_20) (join 24 4 8 phase_3_24 (join 28 4 4 phase_3_28 phase_3_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 phase_3_36 phase_3_40) (join 44 4 8 phase_3_44 (join 48 4 4 phase_3_48 phase_3_52))) (join 56 8 12 (join 56 4 4 phase_3_56 phase_3_60) (join 64 4 8 phase_3_64 (join 68 4 4 phase_3_68 phase_3_72))))) (join 76 40 38 (join 76 20 20 (join 76 8 12 (join 76 4 4 phase_3_76 phase_3_80) (join 84 4 8 phase_3_84 (join 88 4 4 phase_3_88 phase_3_92))) (join 96 8 12 (join 96 4 4 phase_3_96 phase_3_100) (join 104 4 8 phase_3_104 (join 108 4 4 phase_3_108 phase_3_112)))) (join 116 20 18 (join 116 8 12 (join 116 4 4 phase_3_116 phase_3_120) (join 124 4 8 phase_3_124 (join 128 4 4 phase_3_128 phase_3_132))) (join 136 8 10 (join 136 4 4 phase_3_136 phase_3_140) (join 144 4 6 phase_3_144 (join 148 4 2 phase_3_148 phase_3_152))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_3_0 : ∀ i ∈ List.range 1, ThresholdAt 3 (0+i) := by decide +kernel

theorem threshold_3_1 : ∀ i ∈ List.range 1, ThresholdAt 3 (1+i) := by decide +kernel

theorem threshold_3_2 : ∀ i ∈ List.range 1, ThresholdAt 3 (2+i) := by decide +kernel

theorem threshold_3_3 : ∀ i ∈ List.range 1, ThresholdAt 3 (3+i) := by decide +kernel

theorem threshold_3_4 : ∀ i ∈ List.range 1, ThresholdAt 3 (4+i) := by decide +kernel

theorem threshold_3_5 : ∀ i ∈ List.range 1, ThresholdAt 3 (5+i) := by decide +kernel

theorem threshold_3_6 : ∀ i ∈ List.range 1, ThresholdAt 3 (6+i) := by decide +kernel

theorem threshold_3_7 : ∀ i ∈ List.range 1, ThresholdAt 3 (7+i) := by decide +kernel

theorem threshold_3_8 : ∀ i ∈ List.range 1, ThresholdAt 3 (8+i) := by decide +kernel

theorem threshold_3_9 : ∀ i ∈ List.range 1, ThresholdAt 3 (9+i) := by decide +kernel

theorem threshold_3_10 : ∀ i ∈ List.range 1, ThresholdAt 3 (10+i) := by decide +kernel

theorem threshold_3_11 : ∀ i ∈ List.range 1, ThresholdAt 3 (11+i) := by decide +kernel

theorem threshold_3_12 : ∀ i ∈ List.range 1, ThresholdAt 3 (12+i) := by decide +kernel

theorem threshold_3_13 : ∀ i ∈ List.range 1, ThresholdAt 3 (13+i) := by decide +kernel

theorem threshold_3_14 : ∀ i ∈ List.range 1, ThresholdAt 3 (14+i) := by decide +kernel

theorem threshold_3_15 : ∀ i ∈ List.range 1, ThresholdAt 3 (15+i) := by decide +kernel

theorem threshold_3_16 : ∀ i ∈ List.range 1, ThresholdAt 3 (16+i) := by decide +kernel

theorem threshold_3_17 : ∀ i ∈ List.range 1, ThresholdAt 3 (17+i) := by decide +kernel

theorem threshold_3_18 : ∀ i ∈ List.range 1, ThresholdAt 3 (18+i) := by decide +kernel

theorem threshold_3_19 : ∀ i ∈ List.range 1, ThresholdAt 3 (19+i) := by decide +kernel

theorem threshold_3_20 : ∀ i ∈ List.range 1, ThresholdAt 3 (20+i) := by decide +kernel

theorem threshold_3_21 : ∀ i ∈ List.range 1, ThresholdAt 3 (21+i) := by decide +kernel

theorem threshold_3_22 : ∀ i ∈ List.range 1, ThresholdAt 3 (22+i) := by decide +kernel

theorem threshold_3_23 : ∀ i ∈ List.range 1, ThresholdAt 3 (23+i) := by decide +kernel

theorem threshold_3_24 : ∀ i ∈ List.range 1, ThresholdAt 3 (24+i) := by decide +kernel

theorem threshold_3_25 : ∀ i ∈ List.range 1, ThresholdAt 3 (25+i) := by decide +kernel

theorem threshold_3_26 : ∀ i ∈ List.range 1, ThresholdAt 3 (26+i) := by decide +kernel

theorem threshold_3_27 : ∀ i ∈ List.range 1, ThresholdAt 3 (27+i) := by decide +kernel

theorem threshold_3_28 : ∀ i ∈ List.range 1, ThresholdAt 3 (28+i) := by decide +kernel

theorem threshold_3_29 : ∀ i ∈ List.range 1, ThresholdAt 3 (29+i) := by decide +kernel

theorem threshold_3_30 : ∀ i ∈ List.range 1, ThresholdAt 3 (30+i) := by decide +kernel

theorem threshold_3_31 : ∀ i ∈ List.range 1, ThresholdAt 3 (31+i) := by decide +kernel

theorem threshold_3_32 : ∀ i ∈ List.range 1, ThresholdAt 3 (32+i) := by decide +kernel

theorem threshold_3_33 : ∀ i ∈ List.range 1, ThresholdAt 3 (33+i) := by decide +kernel

theorem threshold_3_34 : ∀ i ∈ List.range 1, ThresholdAt 3 (34+i) := by decide +kernel

theorem threshold_3_35 : ∀ i ∈ List.range 1, ThresholdAt 3 (35+i) := by decide +kernel

theorem threshold_3_36 : ∀ i ∈ List.range 1, ThresholdAt 3 (36+i) := by decide +kernel

theorem threshold_3_37 : ∀ i ∈ List.range 1, ThresholdAt 3 (37+i) := by decide +kernel

theorem threshold_3_38 : ∀ i ∈ List.range 1, ThresholdAt 3 (38+i) := by decide +kernel

theorem threshold_3_39 : ∀ i ∈ List.range 1, ThresholdAt 3 (39+i) := by decide +kernel

theorem threshold_3_40 : ∀ i ∈ List.range 1, ThresholdAt 3 (40+i) := by decide +kernel

theorem threshold_3_41 : ∀ i ∈ List.range 1, ThresholdAt 3 (41+i) := by decide +kernel

theorem threshold_3_42 : ∀ i ∈ List.range 1, ThresholdAt 3 (42+i) := by decide +kernel

theorem threshold_3_43 : ∀ i ∈ List.range 1, ThresholdAt 3 (43+i) := by decide +kernel

theorem threshold_3_44 : ∀ i ∈ List.range 1, ThresholdAt 3 (44+i) := by decide +kernel

theorem threshold_3_45 : ∀ i ∈ List.range 1, ThresholdAt 3 (45+i) := by decide +kernel

theorem threshold_3_46 : ∀ i ∈ List.range 1, ThresholdAt 3 (46+i) := by decide +kernel

theorem threshold_3_47 : ∀ i ∈ List.range 1, ThresholdAt 3 (47+i) := by decide +kernel

theorem threshold_3_48 : ∀ i ∈ List.range 1, ThresholdAt 3 (48+i) := by decide +kernel

theorem threshold_3_49 : ∀ i ∈ List.range 1, ThresholdAt 3 (49+i) := by decide +kernel

theorem threshold_3_50 : ∀ i ∈ List.range 1, ThresholdAt 3 (50+i) := by decide +kernel

theorem threshold_3_51 : ∀ i ∈ List.range 1, ThresholdAt 3 (51+i) := by decide +kernel

theorem threshold_3_52 : ∀ i ∈ List.range 1, ThresholdAt 3 (52+i) := by decide +kernel

theorem threshold_3_53 : ∀ i ∈ List.range 1, ThresholdAt 3 (53+i) := by decide +kernel

theorem threshold_3_54 : ∀ i ∈ List.range 1, ThresholdAt 3 (54+i) := by decide +kernel

theorem threshold_3_55 : ∀ i ∈ List.range 1, ThresholdAt 3 (55+i) := by decide +kernel

theorem threshold_3_56 : ∀ i ∈ List.range 1, ThresholdAt 3 (56+i) := by decide +kernel

theorem threshold_3_57 : ∀ i ∈ List.range 1, ThresholdAt 3 (57+i) := by decide +kernel

theorem threshold_3_58 : ∀ i ∈ List.range 1, ThresholdAt 3 (58+i) := by decide +kernel

theorem threshold_3_59 : ∀ i ∈ List.range 1, ThresholdAt 3 (59+i) := by decide +kernel

theorem threshold_3_60 : ∀ i ∈ List.range 1, ThresholdAt 3 (60+i) := by decide +kernel

theorem threshold_3_61 : ∀ i ∈ List.range 1, ThresholdAt 3 (61+i) := by decide +kernel

theorem threshold_3_62 : ∀ i ∈ List.range 1, ThresholdAt 3 (62+i) := by decide +kernel

theorem threshold_3_63 : ∀ i ∈ List.range 1, ThresholdAt 3 (63+i) := by decide +kernel

theorem threshold_3_64 : ∀ i ∈ List.range 1, ThresholdAt 3 (64+i) := by decide +kernel

theorem threshold_3_65 : ∀ i ∈ List.range 1, ThresholdAt 3 (65+i) := by decide +kernel

theorem threshold_3_66 : ∀ i ∈ List.range 1, ThresholdAt 3 (66+i) := by decide +kernel

theorem threshold_3_67 : ∀ i ∈ List.range 1, ThresholdAt 3 (67+i) := by decide +kernel

theorem threshold_3_68 : ∀ i ∈ List.range 1, ThresholdAt 3 (68+i) := by decide +kernel

theorem threshold_3_69 : ∀ i ∈ List.range 1, ThresholdAt 3 (69+i) := by decide +kernel

theorem threshold_3_70 : ∀ i ∈ List.range 1, ThresholdAt 3 (70+i) := by decide +kernel

theorem threshold_3_71 : ∀ i ∈ List.range 1, ThresholdAt 3 (71+i) := by decide +kernel

theorem threshold_3_72 : ∀ i ∈ List.range 1, ThresholdAt 3 (72+i) := by decide +kernel

theorem threshold_3_73 : ∀ i ∈ List.range 1, ThresholdAt 3 (73+i) := by decide +kernel

theorem threshold_3_74 : ∀ i ∈ List.range 1, ThresholdAt 3 (74+i) := by decide +kernel

theorem threshold_3_75 : ∀ i ∈ List.range 1, ThresholdAt 3 (75+i) := by decide +kernel

theorem threshold_3_76 : ∀ i ∈ List.range 1, ThresholdAt 3 (76+i) := by decide +kernel

theorem threshold_3_77 : ∀ i ∈ List.range 1, ThresholdAt 3 (77+i) := by decide +kernel

theorem threshold_3_78 : ∀ i ∈ List.range 1, ThresholdAt 3 (78+i) := by decide +kernel

theorem threshold_3_79 : ∀ i ∈ List.range 1, ThresholdAt 3 (79+i) := by decide +kernel

theorem threshold_3_80 : ∀ i ∈ List.range 1, ThresholdAt 3 (80+i) := by decide +kernel

theorem threshold_3_81 : ∀ i ∈ List.range 1, ThresholdAt 3 (81+i) := by decide +kernel

theorem threshold_3_82 : ∀ i ∈ List.range 1, ThresholdAt 3 (82+i) := by decide +kernel

theorem threshold_3_83 : ∀ i ∈ List.range 1, ThresholdAt 3 (83+i) := by decide +kernel

theorem threshold_3_84 : ∀ i ∈ List.range 1, ThresholdAt 3 (84+i) := by decide +kernel

theorem threshold_3_85 : ∀ i ∈ List.range 1, ThresholdAt 3 (85+i) := by decide +kernel

theorem threshold_3_86 : ∀ i ∈ List.range 1, ThresholdAt 3 (86+i) := by decide +kernel

theorem threshold_3_87 : ∀ i ∈ List.range 1, ThresholdAt 3 (87+i) := by decide +kernel

theorem threshold_3_88 : ∀ i ∈ List.range 1, ThresholdAt 3 (88+i) := by decide +kernel

theorem threshold_3_89 : ∀ i ∈ List.range 1, ThresholdAt 3 (89+i) := by decide +kernel

theorem threshold_3_90 : ∀ i ∈ List.range 1, ThresholdAt 3 (90+i) := by decide +kernel

theorem threshold_3_91 : ∀ i ∈ List.range 1, ThresholdAt 3 (91+i) := by decide +kernel

theorem threshold_3_92 : ∀ i ∈ List.range 1, ThresholdAt 3 (92+i) := by decide +kernel

theorem threshold_3_93 : ∀ i ∈ List.range 1, ThresholdAt 3 (93+i) := by decide +kernel

theorem threshold_3_94 : ∀ i ∈ List.range 1, ThresholdAt 3 (94+i) := by decide +kernel

theorem threshold_3_95 : ∀ i ∈ List.range 1, ThresholdAt 3 (95+i) := by decide +kernel

theorem threshold_3_96 : ∀ i ∈ List.range 1, ThresholdAt 3 (96+i) := by decide +kernel

theorem threshold_3_97 : ∀ i ∈ List.range 1, ThresholdAt 3 (97+i) := by decide +kernel

theorem threshold_3_98 : ∀ i ∈ List.range 1, ThresholdAt 3 (98+i) := by decide +kernel

theorem threshold_3_99 : ∀ i ∈ List.range 1, ThresholdAt 3 (99+i) := by decide +kernel

theorem threshold_3_100 : ∀ i ∈ List.range 1, ThresholdAt 3 (100+i) := by decide +kernel

theorem threshold_3_101 : ∀ i ∈ List.range 1, ThresholdAt 3 (101+i) := by decide +kernel

theorem threshold_3_102 : ∀ i ∈ List.range 1, ThresholdAt 3 (102+i) := by decide +kernel

theorem threshold_3_103 : ∀ i ∈ List.range 1, ThresholdAt 3 (103+i) := by decide +kernel

theorem threshold_3_104 : ∀ i ∈ List.range 1, ThresholdAt 3 (104+i) := by decide +kernel

theorem threshold_3_105 : ∀ i ∈ List.range 1, ThresholdAt 3 (105+i) := by decide +kernel

theorem threshold_3_106 : ∀ i ∈ List.range 1, ThresholdAt 3 (106+i) := by decide +kernel

theorem threshold_3_107 : ∀ i ∈ List.range 1, ThresholdAt 3 (107+i) := by decide +kernel

theorem threshold_3_108 : ∀ i ∈ List.range 1, ThresholdAt 3 (108+i) := by decide +kernel

theorem threshold_3_109 : ∀ i ∈ List.range 1, ThresholdAt 3 (109+i) := by decide +kernel

theorem threshold_3_110 : ∀ i ∈ List.range 1, ThresholdAt 3 (110+i) := by decide +kernel

theorem threshold_3_111 : ∀ i ∈ List.range 1, ThresholdAt 3 (111+i) := by decide +kernel

theorem threshold_3_112 : ∀ i ∈ List.range 1, ThresholdAt 3 (112+i) := by decide +kernel

theorem threshold_3_113 : ∀ i ∈ List.range 1, ThresholdAt 3 (113+i) := by decide +kernel

theorem threshold_3_114 : ∀ i ∈ List.range 1, ThresholdAt 3 (114+i) := by decide +kernel

theorem threshold_3_115 : ∀ i ∈ List.range 1, ThresholdAt 3 (115+i) := by decide +kernel

theorem threshold_3_116 : ∀ i ∈ List.range 1, ThresholdAt 3 (116+i) := by decide +kernel

theorem threshold_3_117 : ∀ i ∈ List.range 1, ThresholdAt 3 (117+i) := by decide +kernel

theorem threshold_3_118 : ∀ i ∈ List.range 1, ThresholdAt 3 (118+i) := by decide +kernel

theorem threshold_3_119 : ∀ i ∈ List.range 1, ThresholdAt 3 (119+i) := by decide +kernel

theorem threshold_3_120 : ∀ i ∈ List.range 1, ThresholdAt 3 (120+i) := by decide +kernel

theorem threshold_3_121 : ∀ i ∈ List.range 1, ThresholdAt 3 (121+i) := by decide +kernel

theorem threshold_3_122 : ∀ i ∈ List.range 1, ThresholdAt 3 (122+i) := by decide +kernel

theorem threshold_3_123 : ∀ i ∈ List.range 1, ThresholdAt 3 (123+i) := by decide +kernel

theorem threshold_3_124 : ∀ i ∈ List.range 1, ThresholdAt 3 (124+i) := by decide +kernel

theorem threshold_3_125 : ∀ i ∈ List.range 1, ThresholdAt 3 (125+i) := by decide +kernel

theorem threshold_3_126 : ∀ i ∈ List.range 1, ThresholdAt 3 (126+i) := by decide +kernel

theorem threshold_3_127 : ∀ i ∈ List.range 1, ThresholdAt 3 (127+i) := by decide +kernel

theorem threshold_3_128 : ∀ i ∈ List.range 1, ThresholdAt 3 (128+i) := by decide +kernel

theorem threshold_3_129 : ∀ i ∈ List.range 1, ThresholdAt 3 (129+i) := by decide +kernel

theorem threshold_3_130 : ∀ i ∈ List.range 1, ThresholdAt 3 (130+i) := by decide +kernel

theorem threshold_3_131 : ∀ i ∈ List.range 1, ThresholdAt 3 (131+i) := by decide +kernel

theorem threshold_3_132 : ∀ i ∈ List.range 1, ThresholdAt 3 (132+i) := by decide +kernel

theorem threshold_3_133 : ∀ i ∈ List.range 1, ThresholdAt 3 (133+i) := by decide +kernel

theorem threshold_3_134 : ∀ i ∈ List.range 1, ThresholdAt 3 (134+i) := by decide +kernel

theorem threshold_3_135 : ∀ i ∈ List.range 1, ThresholdAt 3 (135+i) := by decide +kernel

theorem threshold_3_136 : ∀ i ∈ List.range 1, ThresholdAt 3 (136+i) := by decide +kernel

theorem threshold_3_137 : ∀ i ∈ List.range 1, ThresholdAt 3 (137+i) := by decide +kernel

theorem threshold_3_138 : ∀ i ∈ List.range 1, ThresholdAt 3 (138+i) := by decide +kernel

theorem threshold_3_139 : ∀ i ∈ List.range 1, ThresholdAt 3 (139+i) := by decide +kernel

theorem threshold_3_140 : ∀ i ∈ List.range 1, ThresholdAt 3 (140+i) := by decide +kernel

theorem threshold_3_141 : ∀ i ∈ List.range 1, ThresholdAt 3 (141+i) := by decide +kernel

theorem threshold_3_142 : ∀ i ∈ List.range 1, ThresholdAt 3 (142+i) := by decide +kernel

theorem threshold_3_143 : ∀ i ∈ List.range 1, ThresholdAt 3 (143+i) := by decide +kernel

theorem threshold_3_144 : ∀ i ∈ List.range 1, ThresholdAt 3 (144+i) := by decide +kernel

theorem threshold_3_145 : ∀ i ∈ List.range 1, ThresholdAt 3 (145+i) := by decide +kernel

theorem threshold_3_146 : ∀ i ∈ List.range 1, ThresholdAt 3 (146+i) := by decide +kernel

theorem threshold_3_147 : ∀ i ∈ List.range 1, ThresholdAt 3 (147+i) := by decide +kernel

theorem threshold_3_148 : ∀ i ∈ List.range 1, ThresholdAt 3 (148+i) := by decide +kernel

theorem threshold_3_149 : ∀ i ∈ List.range 1, ThresholdAt 3 (149+i) := by decide +kernel

theorem threshold_3_150 : ∀ i ∈ List.range 1, ThresholdAt 3 (150+i) := by decide +kernel

theorem threshold_3_151 : ∀ i ∈ List.range 1, ThresholdAt 3 (151+i) := by decide +kernel

theorem threshold_3_152 : ∀ i ∈ List.range 1, ThresholdAt 3 (152+i) := by decide +kernel

theorem threshold_3_153 : ∀ i ∈ List.range 1, ThresholdAt 3 (153+i) := by decide +kernel

theorem threshold_3 (v : ℕ) (hv : v ∈ List.range 154) : ThresholdAt 3 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 3 v)
  have h := (join 0 77 77 (join 0 38 39 (join 0 19 19 (join 0 9 10 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_3_0 threshold_3_1) (join 2 1 1 threshold_3_2 threshold_3_3)) (join 4 2 3 (join 4 1 1 threshold_3_4 threshold_3_5) (join 6 1 2 threshold_3_6 (join 7 1 1 threshold_3_7 threshold_3_8)))) (join 9 5 5 (join 9 2 3 (join 9 1 1 threshold_3_9 threshold_3_10) (join 11 1 2 threshold_3_11 (join 12 1 1 threshold_3_12 threshold_3_13))) (join 14 2 3 (join 14 1 1 threshold_3_14 threshold_3_15) (join 16 1 2 threshold_3_16 (join 17 1 1 threshold_3_17 threshold_3_18))))) (join 19 9 10 (join 19 4 5 (join 19 2 2 (join 19 1 1 threshold_3_19 threshold_3_20) (join 21 1 1 threshold_3_21 threshold_3_22)) (join 23 2 3 (join 23 1 1 threshold_3_23 threshold_3_24) (join 25 1 2 threshold_3_25 (join 26 1 1 threshold_3_26 threshold_3_27)))) (join 28 5 5 (join 28 2 3 (join 28 1 1 threshold_3_28 threshold_3_29) (join 30 1 2 threshold_3_30 (join 31 1 1 threshold_3_31 threshold_3_32))) (join 33 2 3 (join 33 1 1 threshold_3_33 threshold_3_34) (join 35 1 2 threshold_3_35 (join 36 1 1 threshold_3_36 threshold_3_37)))))) (join 38 19 20 (join 38 9 10 (join 38 4 5 (join 38 2 2 (join 38 1 1 threshold_3_38 threshold_3_39) (join 40 1 1 threshold_3_40 threshold_3_41)) (join 42 2 3 (join 42 1 1 threshold_3_42 threshold_3_43) (join 44 1 2 threshold_3_44 (join 45 1 1 threshold_3_45 threshold_3_46)))) (join 47 5 5 (join 47 2 3 (join 47 1 1 threshold_3_47 threshold_3_48) (join 49 1 2 threshold_3_49 (join 50 1 1 threshold_3_50 threshold_3_51))) (join 52 2 3 (join 52 1 1 threshold_3_52 threshold_3_53) (join 54 1 2 threshold_3_54 (join 55 1 1 threshold_3_55 threshold_3_56))))) (join 57 10 10 (join 57 5 5 (join 57 2 3 (join 57 1 1 threshold_3_57 threshold_3_58) (join 59 1 2 threshold_3_59 (join 60 1 1 threshold_3_60 threshold_3_61))) (join 62 2 3 (join 62 1 1 threshold_3_62 threshold_3_63) (join 64 1 2 threshold_3_64 (join 65 1 1 threshold_3_65 threshold_3_66)))) (join 67 5 5 (join 67 2 3 (join 67 1 1 threshold_3_67 threshold_3_68) (join 69 1 2 threshold_3_69 (join 70 1 1 threshold_3_70 threshold_3_71))) (join 72 2 3 (join 72 1 1 threshold_3_72 threshold_3_73) (join 74 1 2 threshold_3_74 (join 75 1 1 threshold_3_75 threshold_3_76))))))) (join 77 38 39 (join 77 19 19 (join 77 9 10 (join 77 4 5 (join 77 2 2 (join 77 1 1 threshold_3_77 threshold_3_78) (join 79 1 1 threshold_3_79 threshold_3_80)) (join 81 2 3 (join 81 1 1 threshold_3_81 threshold_3_82) (join 83 1 2 threshold_3_83 (join 84 1 1 threshold_3_84 threshold_3_85)))) (join 86 5 5 (join 86 2 3 (join 86 1 1 threshold_3_86 threshold_3_87) (join 88 1 2 threshold_3_88 (join 89 1 1 threshold_3_89 threshold_3_90))) (join 91 2 3 (join 91 1 1 threshold_3_91 threshold_3_92) (join 93 1 2 threshold_3_93 (join 94 1 1 threshold_3_94 threshold_3_95))))) (join 96 9 10 (join 96 4 5 (join 96 2 2 (join 96 1 1 threshold_3_96 threshold_3_97) (join 98 1 1 threshold_3_98 threshold_3_99)) (join 100 2 3 (join 100 1 1 threshold_3_100 threshold_3_101) (join 102 1 2 threshold_3_102 (join 103 1 1 threshold_3_103 threshold_3_104)))) (join 105 5 5 (join 105 2 3 (join 105 1 1 threshold_3_105 threshold_3_106) (join 107 1 2 threshold_3_107 (join 108 1 1 threshold_3_108 threshold_3_109))) (join 110 2 3 (join 110 1 1 threshold_3_110 threshold_3_111) (join 112 1 2 threshold_3_112 (join 113 1 1 threshold_3_113 threshold_3_114)))))) (join 115 19 20 (join 115 9 10 (join 115 4 5 (join 115 2 2 (join 115 1 1 threshold_3_115 threshold_3_116) (join 117 1 1 threshold_3_117 threshold_3_118)) (join 119 2 3 (join 119 1 1 threshold_3_119 threshold_3_120) (join 121 1 2 threshold_3_121 (join 122 1 1 threshold_3_122 threshold_3_123)))) (join 124 5 5 (join 124 2 3 (join 124 1 1 threshold_3_124 threshold_3_125) (join 126 1 2 threshold_3_126 (join 127 1 1 threshold_3_127 threshold_3_128))) (join 129 2 3 (join 129 1 1 threshold_3_129 threshold_3_130) (join 131 1 2 threshold_3_131 (join 132 1 1 threshold_3_132 threshold_3_133))))) (join 134 10 10 (join 134 5 5 (join 134 2 3 (join 134 1 1 threshold_3_134 threshold_3_135) (join 136 1 2 threshold_3_136 (join 137 1 1 threshold_3_137 threshold_3_138))) (join 139 2 3 (join 139 1 1 threshold_3_139 threshold_3_140) (join 141 1 2 threshold_3_141 (join 142 1 1 threshold_3_142 threshold_3_143)))) (join 144 5 5 (join 144 2 3 (join 144 1 1 threshold_3_144 threshold_3_145) (join 146 1 2 threshold_3_146 (join 147 1 1 threshold_3_147 threshold_3_148))) (join 149 2 3 (join 149 1 1 threshold_3_149 threshold_3_150) (join 151 1 2 threshold_3_151 (join 152 1 1 threshold_3_152 threshold_3_153))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_3_0 : ∀ i ∈ List.range 4, LedgerAt 3 (0+i) := by decide +kernel

theorem ledger_3_4 : ∀ i ∈ List.range 4, LedgerAt 3 (4+i) := by decide +kernel

theorem ledger_3_8 : ∀ i ∈ List.range 4, LedgerAt 3 (8+i) := by decide +kernel

theorem ledger_3_12 : ∀ i ∈ List.range 4, LedgerAt 3 (12+i) := by decide +kernel

theorem ledger_3_16 : ∀ i ∈ List.range 4, LedgerAt 3 (16+i) := by decide +kernel

theorem ledger_3_20 : ∀ i ∈ List.range 4, LedgerAt 3 (20+i) := by decide +kernel

theorem ledger_3_24 : ∀ i ∈ List.range 4, LedgerAt 3 (24+i) := by decide +kernel

theorem ledger_3_28 : ∀ i ∈ List.range 4, LedgerAt 3 (28+i) := by decide +kernel

theorem ledger_3_32 : ∀ i ∈ List.range 4, LedgerAt 3 (32+i) := by decide +kernel

theorem ledger_3_36 : ∀ i ∈ List.range 4, LedgerAt 3 (36+i) := by decide +kernel

theorem ledger_3_40 : ∀ i ∈ List.range 4, LedgerAt 3 (40+i) := by decide +kernel

theorem ledger_3_44 : ∀ i ∈ List.range 4, LedgerAt 3 (44+i) := by decide +kernel

theorem ledger_3_48 : ∀ i ∈ List.range 4, LedgerAt 3 (48+i) := by decide +kernel

theorem ledger_3_52 : ∀ i ∈ List.range 4, LedgerAt 3 (52+i) := by decide +kernel

theorem ledger_3_56 : ∀ i ∈ List.range 4, LedgerAt 3 (56+i) := by decide +kernel

theorem ledger_3_60 : ∀ i ∈ List.range 4, LedgerAt 3 (60+i) := by decide +kernel

theorem ledger_3_64 : ∀ i ∈ List.range 4, LedgerAt 3 (64+i) := by decide +kernel

theorem ledger_3_68 : ∀ i ∈ List.range 4, LedgerAt 3 (68+i) := by decide +kernel

theorem ledger_3_72 : ∀ i ∈ List.range 4, LedgerAt 3 (72+i) := by decide +kernel

theorem ledger_3_76 : ∀ i ∈ List.range 4, LedgerAt 3 (76+i) := by decide +kernel

theorem ledger_3_80 : ∀ i ∈ List.range 4, LedgerAt 3 (80+i) := by decide +kernel

theorem ledger_3_84 : ∀ i ∈ List.range 4, LedgerAt 3 (84+i) := by decide +kernel

theorem ledger_3_88 : ∀ i ∈ List.range 4, LedgerAt 3 (88+i) := by decide +kernel

theorem ledger_3_92 : ∀ i ∈ List.range 4, LedgerAt 3 (92+i) := by decide +kernel

theorem ledger_3_96 : ∀ i ∈ List.range 4, LedgerAt 3 (96+i) := by decide +kernel

theorem ledger_3_100 : ∀ i ∈ List.range 4, LedgerAt 3 (100+i) := by decide +kernel

theorem ledger_3_104 : ∀ i ∈ List.range 4, LedgerAt 3 (104+i) := by decide +kernel

theorem ledger_3_108 : ∀ i ∈ List.range 4, LedgerAt 3 (108+i) := by decide +kernel

theorem ledger_3_112 : ∀ i ∈ List.range 4, LedgerAt 3 (112+i) := by decide +kernel

theorem ledger_3_116 : ∀ i ∈ List.range 4, LedgerAt 3 (116+i) := by decide +kernel

theorem ledger_3_120 : ∀ i ∈ List.range 4, LedgerAt 3 (120+i) := by decide +kernel

theorem ledger_3_124 : ∀ i ∈ List.range 4, LedgerAt 3 (124+i) := by decide +kernel

theorem ledger_3_128 : ∀ i ∈ List.range 4, LedgerAt 3 (128+i) := by decide +kernel

theorem ledger_3_132 : ∀ i ∈ List.range 4, LedgerAt 3 (132+i) := by decide +kernel

theorem ledger_3_136 : ∀ i ∈ List.range 4, LedgerAt 3 (136+i) := by decide +kernel

theorem ledger_3_140 : ∀ i ∈ List.range 4, LedgerAt 3 (140+i) := by decide +kernel

theorem ledger_3_144 : ∀ i ∈ List.range 4, LedgerAt 3 (144+i) := by decide +kernel

theorem ledger_3_148 : ∀ i ∈ List.range 4, LedgerAt 3 (148+i) := by decide +kernel

theorem ledger_3_152 : ∀ i ∈ List.range 2, LedgerAt 3 (152+i) := by decide +kernel

theorem ledger_3 (v : ℕ) (hv : v ∈ List.range 154) : LedgerAt 3 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 3 v)
  have h := (join 0 76 78 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_3_0 ledger_3_4) (join 8 4 4 ledger_3_8 ledger_3_12)) (join 16 8 12 (join 16 4 4 ledger_3_16 ledger_3_20) (join 24 4 8 ledger_3_24 (join 28 4 4 ledger_3_28 ledger_3_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 ledger_3_36 ledger_3_40) (join 44 4 8 ledger_3_44 (join 48 4 4 ledger_3_48 ledger_3_52))) (join 56 8 12 (join 56 4 4 ledger_3_56 ledger_3_60) (join 64 4 8 ledger_3_64 (join 68 4 4 ledger_3_68 ledger_3_72))))) (join 76 40 38 (join 76 20 20 (join 76 8 12 (join 76 4 4 ledger_3_76 ledger_3_80) (join 84 4 8 ledger_3_84 (join 88 4 4 ledger_3_88 ledger_3_92))) (join 96 8 12 (join 96 4 4 ledger_3_96 ledger_3_100) (join 104 4 8 ledger_3_104 (join 108 4 4 ledger_3_108 ledger_3_112)))) (join 116 20 18 (join 116 8 12 (join 116 4 4 ledger_3_116 ledger_3_120) (join 124 4 8 ledger_3_124 (join 128 4 4 ledger_3_128 ledger_3_132))) (join 136 8 10 (join 136 4 4 ledger_3_136 ledger_3_140) (join 144 4 6 ledger_3_144 (join 148 4 2 ledger_3_148 ledger_3_152))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
