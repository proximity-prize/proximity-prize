import ProximityPrize.SubmissionLower.HigherAffineFiniteChecks6810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_1_0 : ∀ i ∈ List.range 4, SingleAt 1 (0+i) := by decide +kernel

theorem single_1_4 : ∀ i ∈ List.range 4, SingleAt 1 (4+i) := by decide +kernel

theorem single_1_8 : ∀ i ∈ List.range 4, SingleAt 1 (8+i) := by decide +kernel

theorem single_1_12 : ∀ i ∈ List.range 4, SingleAt 1 (12+i) := by decide +kernel

theorem single_1_16 : ∀ i ∈ List.range 4, SingleAt 1 (16+i) := by decide +kernel

theorem single_1_20 : ∀ i ∈ List.range 4, SingleAt 1 (20+i) := by decide +kernel

theorem single_1_24 : ∀ i ∈ List.range 4, SingleAt 1 (24+i) := by decide +kernel

theorem single_1_28 : ∀ i ∈ List.range 4, SingleAt 1 (28+i) := by decide +kernel

theorem single_1_32 : ∀ i ∈ List.range 4, SingleAt 1 (32+i) := by decide +kernel

theorem single_1_36 : ∀ i ∈ List.range 4, SingleAt 1 (36+i) := by decide +kernel

theorem single_1_40 : ∀ i ∈ List.range 4, SingleAt 1 (40+i) := by decide +kernel

theorem single_1_44 : ∀ i ∈ List.range 4, SingleAt 1 (44+i) := by decide +kernel

theorem single_1_48 : ∀ i ∈ List.range 4, SingleAt 1 (48+i) := by decide +kernel

theorem single_1_52 : ∀ i ∈ List.range 4, SingleAt 1 (52+i) := by decide +kernel

theorem single_1_56 : ∀ i ∈ List.range 4, SingleAt 1 (56+i) := by decide +kernel

theorem single_1_60 : ∀ i ∈ List.range 4, SingleAt 1 (60+i) := by decide +kernel

theorem single_1_64 : ∀ i ∈ List.range 4, SingleAt 1 (64+i) := by decide +kernel

theorem single_1_68 : ∀ i ∈ List.range 4, SingleAt 1 (68+i) := by decide +kernel

theorem single_1_72 : ∀ i ∈ List.range 4, SingleAt 1 (72+i) := by decide +kernel

theorem single_1_76 : ∀ i ∈ List.range 4, SingleAt 1 (76+i) := by decide +kernel

theorem single_1_80 : ∀ i ∈ List.range 4, SingleAt 1 (80+i) := by decide +kernel

theorem single_1_84 : ∀ i ∈ List.range 4, SingleAt 1 (84+i) := by decide +kernel

theorem single_1_88 : ∀ i ∈ List.range 4, SingleAt 1 (88+i) := by decide +kernel

theorem single_1_92 : ∀ i ∈ List.range 4, SingleAt 1 (92+i) := by decide +kernel

theorem single_1_96 : ∀ i ∈ List.range 4, SingleAt 1 (96+i) := by decide +kernel

theorem single_1_100 : ∀ i ∈ List.range 4, SingleAt 1 (100+i) := by decide +kernel

theorem single_1_104 : ∀ i ∈ List.range 4, SingleAt 1 (104+i) := by decide +kernel

theorem single_1_108 : ∀ i ∈ List.range 4, SingleAt 1 (108+i) := by decide +kernel

theorem single_1_112 : ∀ i ∈ List.range 4, SingleAt 1 (112+i) := by decide +kernel

theorem single_1_116 : ∀ i ∈ List.range 4, SingleAt 1 (116+i) := by decide +kernel

theorem single_1_120 : ∀ i ∈ List.range 4, SingleAt 1 (120+i) := by decide +kernel

theorem single_1_124 : ∀ i ∈ List.range 4, SingleAt 1 (124+i) := by decide +kernel

theorem single_1_128 : ∀ i ∈ List.range 4, SingleAt 1 (128+i) := by decide +kernel

theorem single_1_132 : ∀ i ∈ List.range 4, SingleAt 1 (132+i) := by decide +kernel

theorem single_1_136 : ∀ i ∈ List.range 4, SingleAt 1 (136+i) := by decide +kernel

theorem single_1_140 : ∀ i ∈ List.range 4, SingleAt 1 (140+i) := by decide +kernel

theorem single_1_144 : ∀ i ∈ List.range 4, SingleAt 1 (144+i) := by decide +kernel

theorem single_1_148 : ∀ i ∈ List.range 4, SingleAt 1 (148+i) := by decide +kernel

theorem single_1_152 : ∀ i ∈ List.range 4, SingleAt 1 (152+i) := by decide +kernel

theorem single_1 (v : ℕ) (hv : v ∈ List.range 156) : SingleAt 1 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 1 v)
  have h := (join 0 76 80 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_1_0 single_1_4) (join 8 4 4 single_1_8 single_1_12)) (join 16 8 12 (join 16 4 4 single_1_16 single_1_20) (join 24 4 8 single_1_24 (join 28 4 4 single_1_28 single_1_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 single_1_36 single_1_40) (join 44 4 8 single_1_44 (join 48 4 4 single_1_48 single_1_52))) (join 56 8 12 (join 56 4 4 single_1_56 single_1_60) (join 64 4 8 single_1_64 (join 68 4 4 single_1_68 single_1_72))))) (join 76 40 40 (join 76 20 20 (join 76 8 12 (join 76 4 4 single_1_76 single_1_80) (join 84 4 8 single_1_84 (join 88 4 4 single_1_88 single_1_92))) (join 96 8 12 (join 96 4 4 single_1_96 single_1_100) (join 104 4 8 single_1_104 (join 108 4 4 single_1_108 single_1_112)))) (join 116 20 20 (join 116 8 12 (join 116 4 4 single_1_116 single_1_120) (join 124 4 8 single_1_124 (join 128 4 4 single_1_128 single_1_132))) (join 136 8 12 (join 136 4 4 single_1_136 single_1_140) (join 144 4 8 single_1_144 (join 148 4 4 single_1_148 single_1_152))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_1_0 : ∀ i ∈ List.range 4, PhaseAt 1 (0+i) := by decide +kernel

theorem phase_1_4 : ∀ i ∈ List.range 4, PhaseAt 1 (4+i) := by decide +kernel

theorem phase_1_8 : ∀ i ∈ List.range 4, PhaseAt 1 (8+i) := by decide +kernel

theorem phase_1_12 : ∀ i ∈ List.range 4, PhaseAt 1 (12+i) := by decide +kernel

theorem phase_1_16 : ∀ i ∈ List.range 4, PhaseAt 1 (16+i) := by decide +kernel

theorem phase_1_20 : ∀ i ∈ List.range 4, PhaseAt 1 (20+i) := by decide +kernel

theorem phase_1_24 : ∀ i ∈ List.range 4, PhaseAt 1 (24+i) := by decide +kernel

theorem phase_1_28 : ∀ i ∈ List.range 4, PhaseAt 1 (28+i) := by decide +kernel

theorem phase_1_32 : ∀ i ∈ List.range 4, PhaseAt 1 (32+i) := by decide +kernel

theorem phase_1_36 : ∀ i ∈ List.range 4, PhaseAt 1 (36+i) := by decide +kernel

theorem phase_1_40 : ∀ i ∈ List.range 4, PhaseAt 1 (40+i) := by decide +kernel

theorem phase_1_44 : ∀ i ∈ List.range 4, PhaseAt 1 (44+i) := by decide +kernel

theorem phase_1_48 : ∀ i ∈ List.range 4, PhaseAt 1 (48+i) := by decide +kernel

theorem phase_1_52 : ∀ i ∈ List.range 4, PhaseAt 1 (52+i) := by decide +kernel

theorem phase_1_56 : ∀ i ∈ List.range 4, PhaseAt 1 (56+i) := by decide +kernel

theorem phase_1_60 : ∀ i ∈ List.range 4, PhaseAt 1 (60+i) := by decide +kernel

theorem phase_1_64 : ∀ i ∈ List.range 4, PhaseAt 1 (64+i) := by decide +kernel

theorem phase_1_68 : ∀ i ∈ List.range 4, PhaseAt 1 (68+i) := by decide +kernel

theorem phase_1_72 : ∀ i ∈ List.range 4, PhaseAt 1 (72+i) := by decide +kernel

theorem phase_1_76 : ∀ i ∈ List.range 4, PhaseAt 1 (76+i) := by decide +kernel

theorem phase_1_80 : ∀ i ∈ List.range 4, PhaseAt 1 (80+i) := by decide +kernel

theorem phase_1_84 : ∀ i ∈ List.range 4, PhaseAt 1 (84+i) := by decide +kernel

theorem phase_1_88 : ∀ i ∈ List.range 4, PhaseAt 1 (88+i) := by decide +kernel

theorem phase_1_92 : ∀ i ∈ List.range 4, PhaseAt 1 (92+i) := by decide +kernel

theorem phase_1_96 : ∀ i ∈ List.range 4, PhaseAt 1 (96+i) := by decide +kernel

theorem phase_1_100 : ∀ i ∈ List.range 4, PhaseAt 1 (100+i) := by decide +kernel

theorem phase_1_104 : ∀ i ∈ List.range 4, PhaseAt 1 (104+i) := by decide +kernel

theorem phase_1_108 : ∀ i ∈ List.range 4, PhaseAt 1 (108+i) := by decide +kernel

theorem phase_1_112 : ∀ i ∈ List.range 4, PhaseAt 1 (112+i) := by decide +kernel

theorem phase_1_116 : ∀ i ∈ List.range 4, PhaseAt 1 (116+i) := by decide +kernel

theorem phase_1_120 : ∀ i ∈ List.range 4, PhaseAt 1 (120+i) := by decide +kernel

theorem phase_1_124 : ∀ i ∈ List.range 4, PhaseAt 1 (124+i) := by decide +kernel

theorem phase_1_128 : ∀ i ∈ List.range 4, PhaseAt 1 (128+i) := by decide +kernel

theorem phase_1_132 : ∀ i ∈ List.range 4, PhaseAt 1 (132+i) := by decide +kernel

theorem phase_1_136 : ∀ i ∈ List.range 4, PhaseAt 1 (136+i) := by decide +kernel

theorem phase_1_140 : ∀ i ∈ List.range 4, PhaseAt 1 (140+i) := by decide +kernel

theorem phase_1_144 : ∀ i ∈ List.range 4, PhaseAt 1 (144+i) := by decide +kernel

theorem phase_1_148 : ∀ i ∈ List.range 4, PhaseAt 1 (148+i) := by decide +kernel

theorem phase_1_152 : ∀ i ∈ List.range 4, PhaseAt 1 (152+i) := by decide +kernel

theorem phase_1 (v : ℕ) (hv : v ∈ List.range 156) : PhaseAt 1 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 1 v)
  have h := (join 0 76 80 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_1_0 phase_1_4) (join 8 4 4 phase_1_8 phase_1_12)) (join 16 8 12 (join 16 4 4 phase_1_16 phase_1_20) (join 24 4 8 phase_1_24 (join 28 4 4 phase_1_28 phase_1_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 phase_1_36 phase_1_40) (join 44 4 8 phase_1_44 (join 48 4 4 phase_1_48 phase_1_52))) (join 56 8 12 (join 56 4 4 phase_1_56 phase_1_60) (join 64 4 8 phase_1_64 (join 68 4 4 phase_1_68 phase_1_72))))) (join 76 40 40 (join 76 20 20 (join 76 8 12 (join 76 4 4 phase_1_76 phase_1_80) (join 84 4 8 phase_1_84 (join 88 4 4 phase_1_88 phase_1_92))) (join 96 8 12 (join 96 4 4 phase_1_96 phase_1_100) (join 104 4 8 phase_1_104 (join 108 4 4 phase_1_108 phase_1_112)))) (join 116 20 20 (join 116 8 12 (join 116 4 4 phase_1_116 phase_1_120) (join 124 4 8 phase_1_124 (join 128 4 4 phase_1_128 phase_1_132))) (join 136 8 12 (join 136 4 4 phase_1_136 phase_1_140) (join 144 4 8 phase_1_144 (join 148 4 4 phase_1_148 phase_1_152))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_1_0 : ∀ i ∈ List.range 1, ThresholdAt 1 (0+i) := by decide +kernel

theorem threshold_1_1 : ∀ i ∈ List.range 1, ThresholdAt 1 (1+i) := by decide +kernel

theorem threshold_1_2 : ∀ i ∈ List.range 1, ThresholdAt 1 (2+i) := by decide +kernel

theorem threshold_1_3 : ∀ i ∈ List.range 1, ThresholdAt 1 (3+i) := by decide +kernel

theorem threshold_1_4 : ∀ i ∈ List.range 1, ThresholdAt 1 (4+i) := by decide +kernel

theorem threshold_1_5 : ∀ i ∈ List.range 1, ThresholdAt 1 (5+i) := by decide +kernel

theorem threshold_1_6 : ∀ i ∈ List.range 1, ThresholdAt 1 (6+i) := by decide +kernel

theorem threshold_1_7 : ∀ i ∈ List.range 1, ThresholdAt 1 (7+i) := by decide +kernel

theorem threshold_1_8 : ∀ i ∈ List.range 1, ThresholdAt 1 (8+i) := by decide +kernel

theorem threshold_1_9 : ∀ i ∈ List.range 1, ThresholdAt 1 (9+i) := by decide +kernel

theorem threshold_1_10 : ∀ i ∈ List.range 1, ThresholdAt 1 (10+i) := by decide +kernel

theorem threshold_1_11 : ∀ i ∈ List.range 1, ThresholdAt 1 (11+i) := by decide +kernel

theorem threshold_1_12 : ∀ i ∈ List.range 1, ThresholdAt 1 (12+i) := by decide +kernel

theorem threshold_1_13 : ∀ i ∈ List.range 1, ThresholdAt 1 (13+i) := by decide +kernel

theorem threshold_1_14 : ∀ i ∈ List.range 1, ThresholdAt 1 (14+i) := by decide +kernel

theorem threshold_1_15 : ∀ i ∈ List.range 1, ThresholdAt 1 (15+i) := by decide +kernel

theorem threshold_1_16 : ∀ i ∈ List.range 1, ThresholdAt 1 (16+i) := by decide +kernel

theorem threshold_1_17 : ∀ i ∈ List.range 1, ThresholdAt 1 (17+i) := by decide +kernel

theorem threshold_1_18 : ∀ i ∈ List.range 1, ThresholdAt 1 (18+i) := by decide +kernel

theorem threshold_1_19 : ∀ i ∈ List.range 1, ThresholdAt 1 (19+i) := by decide +kernel

theorem threshold_1_20 : ∀ i ∈ List.range 1, ThresholdAt 1 (20+i) := by decide +kernel

theorem threshold_1_21 : ∀ i ∈ List.range 1, ThresholdAt 1 (21+i) := by decide +kernel

theorem threshold_1_22 : ∀ i ∈ List.range 1, ThresholdAt 1 (22+i) := by decide +kernel

theorem threshold_1_23 : ∀ i ∈ List.range 1, ThresholdAt 1 (23+i) := by decide +kernel

theorem threshold_1_24 : ∀ i ∈ List.range 1, ThresholdAt 1 (24+i) := by decide +kernel

theorem threshold_1_25 : ∀ i ∈ List.range 1, ThresholdAt 1 (25+i) := by decide +kernel

theorem threshold_1_26 : ∀ i ∈ List.range 1, ThresholdAt 1 (26+i) := by decide +kernel

theorem threshold_1_27 : ∀ i ∈ List.range 1, ThresholdAt 1 (27+i) := by decide +kernel

theorem threshold_1_28 : ∀ i ∈ List.range 1, ThresholdAt 1 (28+i) := by decide +kernel

theorem threshold_1_29 : ∀ i ∈ List.range 1, ThresholdAt 1 (29+i) := by decide +kernel

theorem threshold_1_30 : ∀ i ∈ List.range 1, ThresholdAt 1 (30+i) := by decide +kernel

theorem threshold_1_31 : ∀ i ∈ List.range 1, ThresholdAt 1 (31+i) := by decide +kernel

theorem threshold_1_32 : ∀ i ∈ List.range 1, ThresholdAt 1 (32+i) := by decide +kernel

theorem threshold_1_33 : ∀ i ∈ List.range 1, ThresholdAt 1 (33+i) := by decide +kernel

theorem threshold_1_34 : ∀ i ∈ List.range 1, ThresholdAt 1 (34+i) := by decide +kernel

theorem threshold_1_35 : ∀ i ∈ List.range 1, ThresholdAt 1 (35+i) := by decide +kernel

theorem threshold_1_36 : ∀ i ∈ List.range 1, ThresholdAt 1 (36+i) := by decide +kernel

theorem threshold_1_37 : ∀ i ∈ List.range 1, ThresholdAt 1 (37+i) := by decide +kernel

theorem threshold_1_38 : ∀ i ∈ List.range 1, ThresholdAt 1 (38+i) := by decide +kernel

theorem threshold_1_39 : ∀ i ∈ List.range 1, ThresholdAt 1 (39+i) := by decide +kernel

theorem threshold_1_40 : ∀ i ∈ List.range 1, ThresholdAt 1 (40+i) := by decide +kernel

theorem threshold_1_41 : ∀ i ∈ List.range 1, ThresholdAt 1 (41+i) := by decide +kernel

theorem threshold_1_42 : ∀ i ∈ List.range 1, ThresholdAt 1 (42+i) := by decide +kernel

theorem threshold_1_43 : ∀ i ∈ List.range 1, ThresholdAt 1 (43+i) := by decide +kernel

theorem threshold_1_44 : ∀ i ∈ List.range 1, ThresholdAt 1 (44+i) := by decide +kernel

theorem threshold_1_45 : ∀ i ∈ List.range 1, ThresholdAt 1 (45+i) := by decide +kernel

theorem threshold_1_46 : ∀ i ∈ List.range 1, ThresholdAt 1 (46+i) := by decide +kernel

theorem threshold_1_47 : ∀ i ∈ List.range 1, ThresholdAt 1 (47+i) := by decide +kernel

theorem threshold_1_48 : ∀ i ∈ List.range 1, ThresholdAt 1 (48+i) := by decide +kernel

theorem threshold_1_49 : ∀ i ∈ List.range 1, ThresholdAt 1 (49+i) := by decide +kernel

theorem threshold_1_50 : ∀ i ∈ List.range 1, ThresholdAt 1 (50+i) := by decide +kernel

theorem threshold_1_51 : ∀ i ∈ List.range 1, ThresholdAt 1 (51+i) := by decide +kernel

theorem threshold_1_52 : ∀ i ∈ List.range 1, ThresholdAt 1 (52+i) := by decide +kernel

theorem threshold_1_53 : ∀ i ∈ List.range 1, ThresholdAt 1 (53+i) := by decide +kernel

theorem threshold_1_54 : ∀ i ∈ List.range 1, ThresholdAt 1 (54+i) := by decide +kernel

theorem threshold_1_55 : ∀ i ∈ List.range 1, ThresholdAt 1 (55+i) := by decide +kernel

theorem threshold_1_56 : ∀ i ∈ List.range 1, ThresholdAt 1 (56+i) := by decide +kernel

theorem threshold_1_57 : ∀ i ∈ List.range 1, ThresholdAt 1 (57+i) := by decide +kernel

theorem threshold_1_58 : ∀ i ∈ List.range 1, ThresholdAt 1 (58+i) := by decide +kernel

theorem threshold_1_59 : ∀ i ∈ List.range 1, ThresholdAt 1 (59+i) := by decide +kernel

theorem threshold_1_60 : ∀ i ∈ List.range 1, ThresholdAt 1 (60+i) := by decide +kernel

theorem threshold_1_61 : ∀ i ∈ List.range 1, ThresholdAt 1 (61+i) := by decide +kernel

theorem threshold_1_62 : ∀ i ∈ List.range 1, ThresholdAt 1 (62+i) := by decide +kernel

theorem threshold_1_63 : ∀ i ∈ List.range 1, ThresholdAt 1 (63+i) := by decide +kernel

theorem threshold_1_64 : ∀ i ∈ List.range 1, ThresholdAt 1 (64+i) := by decide +kernel

theorem threshold_1_65 : ∀ i ∈ List.range 1, ThresholdAt 1 (65+i) := by decide +kernel

theorem threshold_1_66 : ∀ i ∈ List.range 1, ThresholdAt 1 (66+i) := by decide +kernel

theorem threshold_1_67 : ∀ i ∈ List.range 1, ThresholdAt 1 (67+i) := by decide +kernel

theorem threshold_1_68 : ∀ i ∈ List.range 1, ThresholdAt 1 (68+i) := by decide +kernel

theorem threshold_1_69 : ∀ i ∈ List.range 1, ThresholdAt 1 (69+i) := by decide +kernel

theorem threshold_1_70 : ∀ i ∈ List.range 1, ThresholdAt 1 (70+i) := by decide +kernel

theorem threshold_1_71 : ∀ i ∈ List.range 1, ThresholdAt 1 (71+i) := by decide +kernel

theorem threshold_1_72 : ∀ i ∈ List.range 1, ThresholdAt 1 (72+i) := by decide +kernel

theorem threshold_1_73 : ∀ i ∈ List.range 1, ThresholdAt 1 (73+i) := by decide +kernel

theorem threshold_1_74 : ∀ i ∈ List.range 1, ThresholdAt 1 (74+i) := by decide +kernel

theorem threshold_1_75 : ∀ i ∈ List.range 1, ThresholdAt 1 (75+i) := by decide +kernel

theorem threshold_1_76 : ∀ i ∈ List.range 1, ThresholdAt 1 (76+i) := by decide +kernel

theorem threshold_1_77 : ∀ i ∈ List.range 1, ThresholdAt 1 (77+i) := by decide +kernel

theorem threshold_1_78 : ∀ i ∈ List.range 1, ThresholdAt 1 (78+i) := by decide +kernel

theorem threshold_1_79 : ∀ i ∈ List.range 1, ThresholdAt 1 (79+i) := by decide +kernel

theorem threshold_1_80 : ∀ i ∈ List.range 1, ThresholdAt 1 (80+i) := by decide +kernel

theorem threshold_1_81 : ∀ i ∈ List.range 1, ThresholdAt 1 (81+i) := by decide +kernel

theorem threshold_1_82 : ∀ i ∈ List.range 1, ThresholdAt 1 (82+i) := by decide +kernel

theorem threshold_1_83 : ∀ i ∈ List.range 1, ThresholdAt 1 (83+i) := by decide +kernel

theorem threshold_1_84 : ∀ i ∈ List.range 1, ThresholdAt 1 (84+i) := by decide +kernel

theorem threshold_1_85 : ∀ i ∈ List.range 1, ThresholdAt 1 (85+i) := by decide +kernel

theorem threshold_1_86 : ∀ i ∈ List.range 1, ThresholdAt 1 (86+i) := by decide +kernel

theorem threshold_1_87 : ∀ i ∈ List.range 1, ThresholdAt 1 (87+i) := by decide +kernel

theorem threshold_1_88 : ∀ i ∈ List.range 1, ThresholdAt 1 (88+i) := by decide +kernel

theorem threshold_1_89 : ∀ i ∈ List.range 1, ThresholdAt 1 (89+i) := by decide +kernel

theorem threshold_1_90 : ∀ i ∈ List.range 1, ThresholdAt 1 (90+i) := by decide +kernel

theorem threshold_1_91 : ∀ i ∈ List.range 1, ThresholdAt 1 (91+i) := by decide +kernel

theorem threshold_1_92 : ∀ i ∈ List.range 1, ThresholdAt 1 (92+i) := by decide +kernel

theorem threshold_1_93 : ∀ i ∈ List.range 1, ThresholdAt 1 (93+i) := by decide +kernel

theorem threshold_1_94 : ∀ i ∈ List.range 1, ThresholdAt 1 (94+i) := by decide +kernel

theorem threshold_1_95 : ∀ i ∈ List.range 1, ThresholdAt 1 (95+i) := by decide +kernel

theorem threshold_1_96 : ∀ i ∈ List.range 1, ThresholdAt 1 (96+i) := by decide +kernel

theorem threshold_1_97 : ∀ i ∈ List.range 1, ThresholdAt 1 (97+i) := by decide +kernel

theorem threshold_1_98 : ∀ i ∈ List.range 1, ThresholdAt 1 (98+i) := by decide +kernel

theorem threshold_1_99 : ∀ i ∈ List.range 1, ThresholdAt 1 (99+i) := by decide +kernel

theorem threshold_1_100 : ∀ i ∈ List.range 1, ThresholdAt 1 (100+i) := by decide +kernel

theorem threshold_1_101 : ∀ i ∈ List.range 1, ThresholdAt 1 (101+i) := by decide +kernel

theorem threshold_1_102 : ∀ i ∈ List.range 1, ThresholdAt 1 (102+i) := by decide +kernel

theorem threshold_1_103 : ∀ i ∈ List.range 1, ThresholdAt 1 (103+i) := by decide +kernel

theorem threshold_1_104 : ∀ i ∈ List.range 1, ThresholdAt 1 (104+i) := by decide +kernel

theorem threshold_1_105 : ∀ i ∈ List.range 1, ThresholdAt 1 (105+i) := by decide +kernel

theorem threshold_1_106 : ∀ i ∈ List.range 1, ThresholdAt 1 (106+i) := by decide +kernel

theorem threshold_1_107 : ∀ i ∈ List.range 1, ThresholdAt 1 (107+i) := by decide +kernel

theorem threshold_1_108 : ∀ i ∈ List.range 1, ThresholdAt 1 (108+i) := by decide +kernel

theorem threshold_1_109 : ∀ i ∈ List.range 1, ThresholdAt 1 (109+i) := by decide +kernel

theorem threshold_1_110 : ∀ i ∈ List.range 1, ThresholdAt 1 (110+i) := by decide +kernel

theorem threshold_1_111 : ∀ i ∈ List.range 1, ThresholdAt 1 (111+i) := by decide +kernel

theorem threshold_1_112 : ∀ i ∈ List.range 1, ThresholdAt 1 (112+i) := by decide +kernel

theorem threshold_1_113 : ∀ i ∈ List.range 1, ThresholdAt 1 (113+i) := by decide +kernel

theorem threshold_1_114 : ∀ i ∈ List.range 1, ThresholdAt 1 (114+i) := by decide +kernel

theorem threshold_1_115 : ∀ i ∈ List.range 1, ThresholdAt 1 (115+i) := by decide +kernel

theorem threshold_1_116 : ∀ i ∈ List.range 1, ThresholdAt 1 (116+i) := by decide +kernel

theorem threshold_1_117 : ∀ i ∈ List.range 1, ThresholdAt 1 (117+i) := by decide +kernel

theorem threshold_1_118 : ∀ i ∈ List.range 1, ThresholdAt 1 (118+i) := by decide +kernel

theorem threshold_1_119 : ∀ i ∈ List.range 1, ThresholdAt 1 (119+i) := by decide +kernel

theorem threshold_1_120 : ∀ i ∈ List.range 1, ThresholdAt 1 (120+i) := by decide +kernel

theorem threshold_1_121 : ∀ i ∈ List.range 1, ThresholdAt 1 (121+i) := by decide +kernel

theorem threshold_1_122 : ∀ i ∈ List.range 1, ThresholdAt 1 (122+i) := by decide +kernel

theorem threshold_1_123 : ∀ i ∈ List.range 1, ThresholdAt 1 (123+i) := by decide +kernel

theorem threshold_1_124 : ∀ i ∈ List.range 1, ThresholdAt 1 (124+i) := by decide +kernel

theorem threshold_1_125 : ∀ i ∈ List.range 1, ThresholdAt 1 (125+i) := by decide +kernel

theorem threshold_1_126 : ∀ i ∈ List.range 1, ThresholdAt 1 (126+i) := by decide +kernel

theorem threshold_1_127 : ∀ i ∈ List.range 1, ThresholdAt 1 (127+i) := by decide +kernel

theorem threshold_1_128 : ∀ i ∈ List.range 1, ThresholdAt 1 (128+i) := by decide +kernel

theorem threshold_1_129 : ∀ i ∈ List.range 1, ThresholdAt 1 (129+i) := by decide +kernel

theorem threshold_1_130 : ∀ i ∈ List.range 1, ThresholdAt 1 (130+i) := by decide +kernel

theorem threshold_1_131 : ∀ i ∈ List.range 1, ThresholdAt 1 (131+i) := by decide +kernel

theorem threshold_1_132 : ∀ i ∈ List.range 1, ThresholdAt 1 (132+i) := by decide +kernel

theorem threshold_1_133 : ∀ i ∈ List.range 1, ThresholdAt 1 (133+i) := by decide +kernel

theorem threshold_1_134 : ∀ i ∈ List.range 1, ThresholdAt 1 (134+i) := by decide +kernel

theorem threshold_1_135 : ∀ i ∈ List.range 1, ThresholdAt 1 (135+i) := by decide +kernel

theorem threshold_1_136 : ∀ i ∈ List.range 1, ThresholdAt 1 (136+i) := by decide +kernel

theorem threshold_1_137 : ∀ i ∈ List.range 1, ThresholdAt 1 (137+i) := by decide +kernel

theorem threshold_1_138 : ∀ i ∈ List.range 1, ThresholdAt 1 (138+i) := by decide +kernel

theorem threshold_1_139 : ∀ i ∈ List.range 1, ThresholdAt 1 (139+i) := by decide +kernel

theorem threshold_1_140 : ∀ i ∈ List.range 1, ThresholdAt 1 (140+i) := by decide +kernel

theorem threshold_1_141 : ∀ i ∈ List.range 1, ThresholdAt 1 (141+i) := by decide +kernel

theorem threshold_1_142 : ∀ i ∈ List.range 1, ThresholdAt 1 (142+i) := by decide +kernel

theorem threshold_1_143 : ∀ i ∈ List.range 1, ThresholdAt 1 (143+i) := by decide +kernel

theorem threshold_1_144 : ∀ i ∈ List.range 1, ThresholdAt 1 (144+i) := by decide +kernel

theorem threshold_1_145 : ∀ i ∈ List.range 1, ThresholdAt 1 (145+i) := by decide +kernel

theorem threshold_1_146 : ∀ i ∈ List.range 1, ThresholdAt 1 (146+i) := by decide +kernel

theorem threshold_1_147 : ∀ i ∈ List.range 1, ThresholdAt 1 (147+i) := by decide +kernel

theorem threshold_1_148 : ∀ i ∈ List.range 1, ThresholdAt 1 (148+i) := by decide +kernel

theorem threshold_1_149 : ∀ i ∈ List.range 1, ThresholdAt 1 (149+i) := by decide +kernel

theorem threshold_1_150 : ∀ i ∈ List.range 1, ThresholdAt 1 (150+i) := by decide +kernel

theorem threshold_1_151 : ∀ i ∈ List.range 1, ThresholdAt 1 (151+i) := by decide +kernel

theorem threshold_1_152 : ∀ i ∈ List.range 1, ThresholdAt 1 (152+i) := by decide +kernel

theorem threshold_1_153 : ∀ i ∈ List.range 1, ThresholdAt 1 (153+i) := by decide +kernel

theorem threshold_1_154 : ∀ i ∈ List.range 1, ThresholdAt 1 (154+i) := by decide +kernel

theorem threshold_1_155 : ∀ i ∈ List.range 1, ThresholdAt 1 (155+i) := by decide +kernel

theorem threshold_1 (v : ℕ) (hv : v ∈ List.range 156) : ThresholdAt 1 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 1 v)
  have h := (join 0 78 78 (join 0 39 39 (join 0 19 20 (join 0 9 10 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_1_0 threshold_1_1) (join 2 1 1 threshold_1_2 threshold_1_3)) (join 4 2 3 (join 4 1 1 threshold_1_4 threshold_1_5) (join 6 1 2 threshold_1_6 (join 7 1 1 threshold_1_7 threshold_1_8)))) (join 9 5 5 (join 9 2 3 (join 9 1 1 threshold_1_9 threshold_1_10) (join 11 1 2 threshold_1_11 (join 12 1 1 threshold_1_12 threshold_1_13))) (join 14 2 3 (join 14 1 1 threshold_1_14 threshold_1_15) (join 16 1 2 threshold_1_16 (join 17 1 1 threshold_1_17 threshold_1_18))))) (join 19 10 10 (join 19 5 5 (join 19 2 3 (join 19 1 1 threshold_1_19 threshold_1_20) (join 21 1 2 threshold_1_21 (join 22 1 1 threshold_1_22 threshold_1_23))) (join 24 2 3 (join 24 1 1 threshold_1_24 threshold_1_25) (join 26 1 2 threshold_1_26 (join 27 1 1 threshold_1_27 threshold_1_28)))) (join 29 5 5 (join 29 2 3 (join 29 1 1 threshold_1_29 threshold_1_30) (join 31 1 2 threshold_1_31 (join 32 1 1 threshold_1_32 threshold_1_33))) (join 34 2 3 (join 34 1 1 threshold_1_34 threshold_1_35) (join 36 1 2 threshold_1_36 (join 37 1 1 threshold_1_37 threshold_1_38)))))) (join 39 19 20 (join 39 9 10 (join 39 4 5 (join 39 2 2 (join 39 1 1 threshold_1_39 threshold_1_40) (join 41 1 1 threshold_1_41 threshold_1_42)) (join 43 2 3 (join 43 1 1 threshold_1_43 threshold_1_44) (join 45 1 2 threshold_1_45 (join 46 1 1 threshold_1_46 threshold_1_47)))) (join 48 5 5 (join 48 2 3 (join 48 1 1 threshold_1_48 threshold_1_49) (join 50 1 2 threshold_1_50 (join 51 1 1 threshold_1_51 threshold_1_52))) (join 53 2 3 (join 53 1 1 threshold_1_53 threshold_1_54) (join 55 1 2 threshold_1_55 (join 56 1 1 threshold_1_56 threshold_1_57))))) (join 58 10 10 (join 58 5 5 (join 58 2 3 (join 58 1 1 threshold_1_58 threshold_1_59) (join 60 1 2 threshold_1_60 (join 61 1 1 threshold_1_61 threshold_1_62))) (join 63 2 3 (join 63 1 1 threshold_1_63 threshold_1_64) (join 65 1 2 threshold_1_65 (join 66 1 1 threshold_1_66 threshold_1_67)))) (join 68 5 5 (join 68 2 3 (join 68 1 1 threshold_1_68 threshold_1_69) (join 70 1 2 threshold_1_70 (join 71 1 1 threshold_1_71 threshold_1_72))) (join 73 2 3 (join 73 1 1 threshold_1_73 threshold_1_74) (join 75 1 2 threshold_1_75 (join 76 1 1 threshold_1_76 threshold_1_77))))))) (join 78 39 39 (join 78 19 20 (join 78 9 10 (join 78 4 5 (join 78 2 2 (join 78 1 1 threshold_1_78 threshold_1_79) (join 80 1 1 threshold_1_80 threshold_1_81)) (join 82 2 3 (join 82 1 1 threshold_1_82 threshold_1_83) (join 84 1 2 threshold_1_84 (join 85 1 1 threshold_1_85 threshold_1_86)))) (join 87 5 5 (join 87 2 3 (join 87 1 1 threshold_1_87 threshold_1_88) (join 89 1 2 threshold_1_89 (join 90 1 1 threshold_1_90 threshold_1_91))) (join 92 2 3 (join 92 1 1 threshold_1_92 threshold_1_93) (join 94 1 2 threshold_1_94 (join 95 1 1 threshold_1_95 threshold_1_96))))) (join 97 10 10 (join 97 5 5 (join 97 2 3 (join 97 1 1 threshold_1_97 threshold_1_98) (join 99 1 2 threshold_1_99 (join 100 1 1 threshold_1_100 threshold_1_101))) (join 102 2 3 (join 102 1 1 threshold_1_102 threshold_1_103) (join 104 1 2 threshold_1_104 (join 105 1 1 threshold_1_105 threshold_1_106)))) (join 107 5 5 (join 107 2 3 (join 107 1 1 threshold_1_107 threshold_1_108) (join 109 1 2 threshold_1_109 (join 110 1 1 threshold_1_110 threshold_1_111))) (join 112 2 3 (join 112 1 1 threshold_1_112 threshold_1_113) (join 114 1 2 threshold_1_114 (join 115 1 1 threshold_1_115 threshold_1_116)))))) (join 117 19 20 (join 117 9 10 (join 117 4 5 (join 117 2 2 (join 117 1 1 threshold_1_117 threshold_1_118) (join 119 1 1 threshold_1_119 threshold_1_120)) (join 121 2 3 (join 121 1 1 threshold_1_121 threshold_1_122) (join 123 1 2 threshold_1_123 (join 124 1 1 threshold_1_124 threshold_1_125)))) (join 126 5 5 (join 126 2 3 (join 126 1 1 threshold_1_126 threshold_1_127) (join 128 1 2 threshold_1_128 (join 129 1 1 threshold_1_129 threshold_1_130))) (join 131 2 3 (join 131 1 1 threshold_1_131 threshold_1_132) (join 133 1 2 threshold_1_133 (join 134 1 1 threshold_1_134 threshold_1_135))))) (join 136 10 10 (join 136 5 5 (join 136 2 3 (join 136 1 1 threshold_1_136 threshold_1_137) (join 138 1 2 threshold_1_138 (join 139 1 1 threshold_1_139 threshold_1_140))) (join 141 2 3 (join 141 1 1 threshold_1_141 threshold_1_142) (join 143 1 2 threshold_1_143 (join 144 1 1 threshold_1_144 threshold_1_145)))) (join 146 5 5 (join 146 2 3 (join 146 1 1 threshold_1_146 threshold_1_147) (join 148 1 2 threshold_1_148 (join 149 1 1 threshold_1_149 threshold_1_150))) (join 151 2 3 (join 151 1 1 threshold_1_151 threshold_1_152) (join 153 1 2 threshold_1_153 (join 154 1 1 threshold_1_154 threshold_1_155))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_1_0 : ∀ i ∈ List.range 4, LedgerAt 1 (0+i) := by decide +kernel

theorem ledger_1_4 : ∀ i ∈ List.range 4, LedgerAt 1 (4+i) := by decide +kernel

theorem ledger_1_8 : ∀ i ∈ List.range 4, LedgerAt 1 (8+i) := by decide +kernel

theorem ledger_1_12 : ∀ i ∈ List.range 4, LedgerAt 1 (12+i) := by decide +kernel

theorem ledger_1_16 : ∀ i ∈ List.range 4, LedgerAt 1 (16+i) := by decide +kernel

theorem ledger_1_20 : ∀ i ∈ List.range 4, LedgerAt 1 (20+i) := by decide +kernel

theorem ledger_1_24 : ∀ i ∈ List.range 4, LedgerAt 1 (24+i) := by decide +kernel

theorem ledger_1_28 : ∀ i ∈ List.range 4, LedgerAt 1 (28+i) := by decide +kernel

theorem ledger_1_32 : ∀ i ∈ List.range 4, LedgerAt 1 (32+i) := by decide +kernel

theorem ledger_1_36 : ∀ i ∈ List.range 4, LedgerAt 1 (36+i) := by decide +kernel

theorem ledger_1_40 : ∀ i ∈ List.range 4, LedgerAt 1 (40+i) := by decide +kernel

theorem ledger_1_44 : ∀ i ∈ List.range 4, LedgerAt 1 (44+i) := by decide +kernel

theorem ledger_1_48 : ∀ i ∈ List.range 4, LedgerAt 1 (48+i) := by decide +kernel

theorem ledger_1_52 : ∀ i ∈ List.range 4, LedgerAt 1 (52+i) := by decide +kernel

theorem ledger_1_56 : ∀ i ∈ List.range 4, LedgerAt 1 (56+i) := by decide +kernel

theorem ledger_1_60 : ∀ i ∈ List.range 4, LedgerAt 1 (60+i) := by decide +kernel

theorem ledger_1_64 : ∀ i ∈ List.range 4, LedgerAt 1 (64+i) := by decide +kernel

theorem ledger_1_68 : ∀ i ∈ List.range 4, LedgerAt 1 (68+i) := by decide +kernel

theorem ledger_1_72 : ∀ i ∈ List.range 4, LedgerAt 1 (72+i) := by decide +kernel

theorem ledger_1_76 : ∀ i ∈ List.range 4, LedgerAt 1 (76+i) := by decide +kernel

theorem ledger_1_80 : ∀ i ∈ List.range 4, LedgerAt 1 (80+i) := by decide +kernel

theorem ledger_1_84 : ∀ i ∈ List.range 4, LedgerAt 1 (84+i) := by decide +kernel

theorem ledger_1_88 : ∀ i ∈ List.range 4, LedgerAt 1 (88+i) := by decide +kernel

theorem ledger_1_92 : ∀ i ∈ List.range 4, LedgerAt 1 (92+i) := by decide +kernel

theorem ledger_1_96 : ∀ i ∈ List.range 4, LedgerAt 1 (96+i) := by decide +kernel

theorem ledger_1_100 : ∀ i ∈ List.range 4, LedgerAt 1 (100+i) := by decide +kernel

theorem ledger_1_104 : ∀ i ∈ List.range 4, LedgerAt 1 (104+i) := by decide +kernel

theorem ledger_1_108 : ∀ i ∈ List.range 4, LedgerAt 1 (108+i) := by decide +kernel

theorem ledger_1_112 : ∀ i ∈ List.range 4, LedgerAt 1 (112+i) := by decide +kernel

theorem ledger_1_116 : ∀ i ∈ List.range 4, LedgerAt 1 (116+i) := by decide +kernel

theorem ledger_1_120 : ∀ i ∈ List.range 4, LedgerAt 1 (120+i) := by decide +kernel

theorem ledger_1_124 : ∀ i ∈ List.range 4, LedgerAt 1 (124+i) := by decide +kernel

theorem ledger_1_128 : ∀ i ∈ List.range 4, LedgerAt 1 (128+i) := by decide +kernel

theorem ledger_1_132 : ∀ i ∈ List.range 4, LedgerAt 1 (132+i) := by decide +kernel

theorem ledger_1_136 : ∀ i ∈ List.range 4, LedgerAt 1 (136+i) := by decide +kernel

theorem ledger_1_140 : ∀ i ∈ List.range 4, LedgerAt 1 (140+i) := by decide +kernel

theorem ledger_1_144 : ∀ i ∈ List.range 4, LedgerAt 1 (144+i) := by decide +kernel

theorem ledger_1_148 : ∀ i ∈ List.range 4, LedgerAt 1 (148+i) := by decide +kernel

theorem ledger_1_152 : ∀ i ∈ List.range 4, LedgerAt 1 (152+i) := by decide +kernel

theorem ledger_1 (v : ℕ) (hv : v ∈ List.range 156) : LedgerAt 1 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 1 v)
  have h := (join 0 76 80 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_1_0 ledger_1_4) (join 8 4 4 ledger_1_8 ledger_1_12)) (join 16 8 12 (join 16 4 4 ledger_1_16 ledger_1_20) (join 24 4 8 ledger_1_24 (join 28 4 4 ledger_1_28 ledger_1_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 ledger_1_36 ledger_1_40) (join 44 4 8 ledger_1_44 (join 48 4 4 ledger_1_48 ledger_1_52))) (join 56 8 12 (join 56 4 4 ledger_1_56 ledger_1_60) (join 64 4 8 ledger_1_64 (join 68 4 4 ledger_1_68 ledger_1_72))))) (join 76 40 40 (join 76 20 20 (join 76 8 12 (join 76 4 4 ledger_1_76 ledger_1_80) (join 84 4 8 ledger_1_84 (join 88 4 4 ledger_1_88 ledger_1_92))) (join 96 8 12 (join 96 4 4 ledger_1_96 ledger_1_100) (join 104 4 8 ledger_1_104 (join 108 4 4 ledger_1_108 ledger_1_112)))) (join 116 20 20 (join 116 8 12 (join 116 4 4 ledger_1_116 ledger_1_120) (join 124 4 8 ledger_1_124 (join 128 4 4 ledger_1_128 ledger_1_132))) (join 136 8 12 (join 136 4 4 ledger_1_136 ledger_1_140) (join 144 4 8 ledger_1_144 (join 148 4 4 ledger_1_148 ledger_1_152))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
