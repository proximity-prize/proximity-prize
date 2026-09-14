import ProximityPrize.SubmissionLower.HigherAffineCheckedR036810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_4_0 : ∀ i ∈ List.range 4, SingleAt 4 (0+i) := by decide +kernel

theorem single_4_4 : ∀ i ∈ List.range 4, SingleAt 4 (4+i) := by decide +kernel

theorem single_4_8 : ∀ i ∈ List.range 4, SingleAt 4 (8+i) := by decide +kernel

theorem single_4_12 : ∀ i ∈ List.range 4, SingleAt 4 (12+i) := by decide +kernel

theorem single_4_16 : ∀ i ∈ List.range 4, SingleAt 4 (16+i) := by decide +kernel

theorem single_4_20 : ∀ i ∈ List.range 4, SingleAt 4 (20+i) := by decide +kernel

theorem single_4_24 : ∀ i ∈ List.range 4, SingleAt 4 (24+i) := by decide +kernel

theorem single_4_28 : ∀ i ∈ List.range 4, SingleAt 4 (28+i) := by decide +kernel

theorem single_4_32 : ∀ i ∈ List.range 4, SingleAt 4 (32+i) := by decide +kernel

theorem single_4_36 : ∀ i ∈ List.range 4, SingleAt 4 (36+i) := by decide +kernel

theorem single_4_40 : ∀ i ∈ List.range 4, SingleAt 4 (40+i) := by decide +kernel

theorem single_4_44 : ∀ i ∈ List.range 4, SingleAt 4 (44+i) := by decide +kernel

theorem single_4_48 : ∀ i ∈ List.range 4, SingleAt 4 (48+i) := by decide +kernel

theorem single_4_52 : ∀ i ∈ List.range 4, SingleAt 4 (52+i) := by decide +kernel

theorem single_4_56 : ∀ i ∈ List.range 4, SingleAt 4 (56+i) := by decide +kernel

theorem single_4_60 : ∀ i ∈ List.range 4, SingleAt 4 (60+i) := by decide +kernel

theorem single_4_64 : ∀ i ∈ List.range 4, SingleAt 4 (64+i) := by decide +kernel

theorem single_4_68 : ∀ i ∈ List.range 4, SingleAt 4 (68+i) := by decide +kernel

theorem single_4_72 : ∀ i ∈ List.range 4, SingleAt 4 (72+i) := by decide +kernel

theorem single_4_76 : ∀ i ∈ List.range 4, SingleAt 4 (76+i) := by decide +kernel

theorem single_4_80 : ∀ i ∈ List.range 4, SingleAt 4 (80+i) := by decide +kernel

theorem single_4_84 : ∀ i ∈ List.range 4, SingleAt 4 (84+i) := by decide +kernel

theorem single_4_88 : ∀ i ∈ List.range 4, SingleAt 4 (88+i) := by decide +kernel

theorem single_4_92 : ∀ i ∈ List.range 4, SingleAt 4 (92+i) := by decide +kernel

theorem single_4_96 : ∀ i ∈ List.range 4, SingleAt 4 (96+i) := by decide +kernel

theorem single_4_100 : ∀ i ∈ List.range 4, SingleAt 4 (100+i) := by decide +kernel

theorem single_4_104 : ∀ i ∈ List.range 4, SingleAt 4 (104+i) := by decide +kernel

theorem single_4_108 : ∀ i ∈ List.range 4, SingleAt 4 (108+i) := by decide +kernel

theorem single_4_112 : ∀ i ∈ List.range 4, SingleAt 4 (112+i) := by decide +kernel

theorem single_4_116 : ∀ i ∈ List.range 4, SingleAt 4 (116+i) := by decide +kernel

theorem single_4_120 : ∀ i ∈ List.range 4, SingleAt 4 (120+i) := by decide +kernel

theorem single_4_124 : ∀ i ∈ List.range 4, SingleAt 4 (124+i) := by decide +kernel

theorem single_4_128 : ∀ i ∈ List.range 4, SingleAt 4 (128+i) := by decide +kernel

theorem single_4_132 : ∀ i ∈ List.range 4, SingleAt 4 (132+i) := by decide +kernel

theorem single_4_136 : ∀ i ∈ List.range 4, SingleAt 4 (136+i) := by decide +kernel

theorem single_4_140 : ∀ i ∈ List.range 4, SingleAt 4 (140+i) := by decide +kernel

theorem single_4_144 : ∀ i ∈ List.range 4, SingleAt 4 (144+i) := by decide +kernel

theorem single_4_148 : ∀ i ∈ List.range 4, SingleAt 4 (148+i) := by decide +kernel

theorem single_4_152 : ∀ i ∈ List.range 1, SingleAt 4 (152+i) := by decide +kernel

theorem single_4 (v : ℕ) (hv : v ∈ List.range 153) : SingleAt 4 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 4 v)
  have h := (join 0 76 77 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_4_0 single_4_4) (join 8 4 4 single_4_8 single_4_12)) (join 16 8 12 (join 16 4 4 single_4_16 single_4_20) (join 24 4 8 single_4_24 (join 28 4 4 single_4_28 single_4_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 single_4_36 single_4_40) (join 44 4 8 single_4_44 (join 48 4 4 single_4_48 single_4_52))) (join 56 8 12 (join 56 4 4 single_4_56 single_4_60) (join 64 4 8 single_4_64 (join 68 4 4 single_4_68 single_4_72))))) (join 76 40 37 (join 76 20 20 (join 76 8 12 (join 76 4 4 single_4_76 single_4_80) (join 84 4 8 single_4_84 (join 88 4 4 single_4_88 single_4_92))) (join 96 8 12 (join 96 4 4 single_4_96 single_4_100) (join 104 4 8 single_4_104 (join 108 4 4 single_4_108 single_4_112)))) (join 116 20 17 (join 116 8 12 (join 116 4 4 single_4_116 single_4_120) (join 124 4 8 single_4_124 (join 128 4 4 single_4_128 single_4_132))) (join 136 8 9 (join 136 4 4 single_4_136 single_4_140) (join 144 4 5 single_4_144 (join 148 4 1 single_4_148 single_4_152))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_4_0 : ∀ i ∈ List.range 4, PhaseAt 4 (0+i) := by decide +kernel

theorem phase_4_4 : ∀ i ∈ List.range 4, PhaseAt 4 (4+i) := by decide +kernel

theorem phase_4_8 : ∀ i ∈ List.range 4, PhaseAt 4 (8+i) := by decide +kernel

theorem phase_4_12 : ∀ i ∈ List.range 4, PhaseAt 4 (12+i) := by decide +kernel

theorem phase_4_16 : ∀ i ∈ List.range 4, PhaseAt 4 (16+i) := by decide +kernel

theorem phase_4_20 : ∀ i ∈ List.range 4, PhaseAt 4 (20+i) := by decide +kernel

theorem phase_4_24 : ∀ i ∈ List.range 4, PhaseAt 4 (24+i) := by decide +kernel

theorem phase_4_28 : ∀ i ∈ List.range 4, PhaseAt 4 (28+i) := by decide +kernel

theorem phase_4_32 : ∀ i ∈ List.range 4, PhaseAt 4 (32+i) := by decide +kernel

theorem phase_4_36 : ∀ i ∈ List.range 4, PhaseAt 4 (36+i) := by decide +kernel

theorem phase_4_40 : ∀ i ∈ List.range 4, PhaseAt 4 (40+i) := by decide +kernel

theorem phase_4_44 : ∀ i ∈ List.range 4, PhaseAt 4 (44+i) := by decide +kernel

theorem phase_4_48 : ∀ i ∈ List.range 4, PhaseAt 4 (48+i) := by decide +kernel

theorem phase_4_52 : ∀ i ∈ List.range 4, PhaseAt 4 (52+i) := by decide +kernel

theorem phase_4_56 : ∀ i ∈ List.range 4, PhaseAt 4 (56+i) := by decide +kernel

theorem phase_4_60 : ∀ i ∈ List.range 4, PhaseAt 4 (60+i) := by decide +kernel

theorem phase_4_64 : ∀ i ∈ List.range 4, PhaseAt 4 (64+i) := by decide +kernel

theorem phase_4_68 : ∀ i ∈ List.range 4, PhaseAt 4 (68+i) := by decide +kernel

theorem phase_4_72 : ∀ i ∈ List.range 4, PhaseAt 4 (72+i) := by decide +kernel

theorem phase_4_76 : ∀ i ∈ List.range 4, PhaseAt 4 (76+i) := by decide +kernel

theorem phase_4_80 : ∀ i ∈ List.range 4, PhaseAt 4 (80+i) := by decide +kernel

theorem phase_4_84 : ∀ i ∈ List.range 4, PhaseAt 4 (84+i) := by decide +kernel

theorem phase_4_88 : ∀ i ∈ List.range 4, PhaseAt 4 (88+i) := by decide +kernel

theorem phase_4_92 : ∀ i ∈ List.range 4, PhaseAt 4 (92+i) := by decide +kernel

theorem phase_4_96 : ∀ i ∈ List.range 4, PhaseAt 4 (96+i) := by decide +kernel

theorem phase_4_100 : ∀ i ∈ List.range 4, PhaseAt 4 (100+i) := by decide +kernel

theorem phase_4_104 : ∀ i ∈ List.range 4, PhaseAt 4 (104+i) := by decide +kernel

theorem phase_4_108 : ∀ i ∈ List.range 4, PhaseAt 4 (108+i) := by decide +kernel

theorem phase_4_112 : ∀ i ∈ List.range 4, PhaseAt 4 (112+i) := by decide +kernel

theorem phase_4_116 : ∀ i ∈ List.range 4, PhaseAt 4 (116+i) := by decide +kernel

theorem phase_4_120 : ∀ i ∈ List.range 4, PhaseAt 4 (120+i) := by decide +kernel

theorem phase_4_124 : ∀ i ∈ List.range 4, PhaseAt 4 (124+i) := by decide +kernel

theorem phase_4_128 : ∀ i ∈ List.range 4, PhaseAt 4 (128+i) := by decide +kernel

theorem phase_4_132 : ∀ i ∈ List.range 4, PhaseAt 4 (132+i) := by decide +kernel

theorem phase_4_136 : ∀ i ∈ List.range 4, PhaseAt 4 (136+i) := by decide +kernel

theorem phase_4_140 : ∀ i ∈ List.range 4, PhaseAt 4 (140+i) := by decide +kernel

theorem phase_4_144 : ∀ i ∈ List.range 4, PhaseAt 4 (144+i) := by decide +kernel

theorem phase_4_148 : ∀ i ∈ List.range 4, PhaseAt 4 (148+i) := by decide +kernel

theorem phase_4_152 : ∀ i ∈ List.range 1, PhaseAt 4 (152+i) := by decide +kernel

theorem phase_4 (v : ℕ) (hv : v ∈ List.range 153) : PhaseAt 4 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 4 v)
  have h := (join 0 76 77 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_4_0 phase_4_4) (join 8 4 4 phase_4_8 phase_4_12)) (join 16 8 12 (join 16 4 4 phase_4_16 phase_4_20) (join 24 4 8 phase_4_24 (join 28 4 4 phase_4_28 phase_4_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 phase_4_36 phase_4_40) (join 44 4 8 phase_4_44 (join 48 4 4 phase_4_48 phase_4_52))) (join 56 8 12 (join 56 4 4 phase_4_56 phase_4_60) (join 64 4 8 phase_4_64 (join 68 4 4 phase_4_68 phase_4_72))))) (join 76 40 37 (join 76 20 20 (join 76 8 12 (join 76 4 4 phase_4_76 phase_4_80) (join 84 4 8 phase_4_84 (join 88 4 4 phase_4_88 phase_4_92))) (join 96 8 12 (join 96 4 4 phase_4_96 phase_4_100) (join 104 4 8 phase_4_104 (join 108 4 4 phase_4_108 phase_4_112)))) (join 116 20 17 (join 116 8 12 (join 116 4 4 phase_4_116 phase_4_120) (join 124 4 8 phase_4_124 (join 128 4 4 phase_4_128 phase_4_132))) (join 136 8 9 (join 136 4 4 phase_4_136 phase_4_140) (join 144 4 5 phase_4_144 (join 148 4 1 phase_4_148 phase_4_152))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_4_0 : ∀ i ∈ List.range 1, ThresholdAt 4 (0+i) := by decide +kernel

theorem threshold_4_1 : ∀ i ∈ List.range 1, ThresholdAt 4 (1+i) := by decide +kernel

theorem threshold_4_2 : ∀ i ∈ List.range 1, ThresholdAt 4 (2+i) := by decide +kernel

theorem threshold_4_3 : ∀ i ∈ List.range 1, ThresholdAt 4 (3+i) := by decide +kernel

theorem threshold_4_4 : ∀ i ∈ List.range 1, ThresholdAt 4 (4+i) := by decide +kernel

theorem threshold_4_5 : ∀ i ∈ List.range 1, ThresholdAt 4 (5+i) := by decide +kernel

theorem threshold_4_6 : ∀ i ∈ List.range 1, ThresholdAt 4 (6+i) := by decide +kernel

theorem threshold_4_7 : ∀ i ∈ List.range 1, ThresholdAt 4 (7+i) := by decide +kernel

theorem threshold_4_8 : ∀ i ∈ List.range 1, ThresholdAt 4 (8+i) := by decide +kernel

theorem threshold_4_9 : ∀ i ∈ List.range 1, ThresholdAt 4 (9+i) := by decide +kernel

theorem threshold_4_10 : ∀ i ∈ List.range 1, ThresholdAt 4 (10+i) := by decide +kernel

theorem threshold_4_11 : ∀ i ∈ List.range 1, ThresholdAt 4 (11+i) := by decide +kernel

theorem threshold_4_12 : ∀ i ∈ List.range 1, ThresholdAt 4 (12+i) := by decide +kernel

theorem threshold_4_13 : ∀ i ∈ List.range 1, ThresholdAt 4 (13+i) := by decide +kernel

theorem threshold_4_14 : ∀ i ∈ List.range 1, ThresholdAt 4 (14+i) := by decide +kernel

theorem threshold_4_15 : ∀ i ∈ List.range 1, ThresholdAt 4 (15+i) := by decide +kernel

theorem threshold_4_16 : ∀ i ∈ List.range 1, ThresholdAt 4 (16+i) := by decide +kernel

theorem threshold_4_17 : ∀ i ∈ List.range 1, ThresholdAt 4 (17+i) := by decide +kernel

theorem threshold_4_18 : ∀ i ∈ List.range 1, ThresholdAt 4 (18+i) := by decide +kernel

theorem threshold_4_19 : ∀ i ∈ List.range 1, ThresholdAt 4 (19+i) := by decide +kernel

theorem threshold_4_20 : ∀ i ∈ List.range 1, ThresholdAt 4 (20+i) := by decide +kernel

theorem threshold_4_21 : ∀ i ∈ List.range 1, ThresholdAt 4 (21+i) := by decide +kernel

theorem threshold_4_22 : ∀ i ∈ List.range 1, ThresholdAt 4 (22+i) := by decide +kernel

theorem threshold_4_23 : ∀ i ∈ List.range 1, ThresholdAt 4 (23+i) := by decide +kernel

theorem threshold_4_24 : ∀ i ∈ List.range 1, ThresholdAt 4 (24+i) := by decide +kernel

theorem threshold_4_25 : ∀ i ∈ List.range 1, ThresholdAt 4 (25+i) := by decide +kernel

theorem threshold_4_26 : ∀ i ∈ List.range 1, ThresholdAt 4 (26+i) := by decide +kernel

theorem threshold_4_27 : ∀ i ∈ List.range 1, ThresholdAt 4 (27+i) := by decide +kernel

theorem threshold_4_28 : ∀ i ∈ List.range 1, ThresholdAt 4 (28+i) := by decide +kernel

theorem threshold_4_29 : ∀ i ∈ List.range 1, ThresholdAt 4 (29+i) := by decide +kernel

theorem threshold_4_30 : ∀ i ∈ List.range 1, ThresholdAt 4 (30+i) := by decide +kernel

theorem threshold_4_31 : ∀ i ∈ List.range 1, ThresholdAt 4 (31+i) := by decide +kernel

theorem threshold_4_32 : ∀ i ∈ List.range 1, ThresholdAt 4 (32+i) := by decide +kernel

theorem threshold_4_33 : ∀ i ∈ List.range 1, ThresholdAt 4 (33+i) := by decide +kernel

theorem threshold_4_34 : ∀ i ∈ List.range 1, ThresholdAt 4 (34+i) := by decide +kernel

theorem threshold_4_35 : ∀ i ∈ List.range 1, ThresholdAt 4 (35+i) := by decide +kernel

theorem threshold_4_36 : ∀ i ∈ List.range 1, ThresholdAt 4 (36+i) := by decide +kernel

theorem threshold_4_37 : ∀ i ∈ List.range 1, ThresholdAt 4 (37+i) := by decide +kernel

theorem threshold_4_38 : ∀ i ∈ List.range 1, ThresholdAt 4 (38+i) := by decide +kernel

theorem threshold_4_39 : ∀ i ∈ List.range 1, ThresholdAt 4 (39+i) := by decide +kernel

theorem threshold_4_40 : ∀ i ∈ List.range 1, ThresholdAt 4 (40+i) := by decide +kernel

theorem threshold_4_41 : ∀ i ∈ List.range 1, ThresholdAt 4 (41+i) := by decide +kernel

theorem threshold_4_42 : ∀ i ∈ List.range 1, ThresholdAt 4 (42+i) := by decide +kernel

theorem threshold_4_43 : ∀ i ∈ List.range 1, ThresholdAt 4 (43+i) := by decide +kernel

theorem threshold_4_44 : ∀ i ∈ List.range 1, ThresholdAt 4 (44+i) := by decide +kernel

theorem threshold_4_45 : ∀ i ∈ List.range 1, ThresholdAt 4 (45+i) := by decide +kernel

theorem threshold_4_46 : ∀ i ∈ List.range 1, ThresholdAt 4 (46+i) := by decide +kernel

theorem threshold_4_47 : ∀ i ∈ List.range 1, ThresholdAt 4 (47+i) := by decide +kernel

theorem threshold_4_48 : ∀ i ∈ List.range 1, ThresholdAt 4 (48+i) := by decide +kernel

theorem threshold_4_49 : ∀ i ∈ List.range 1, ThresholdAt 4 (49+i) := by decide +kernel

theorem threshold_4_50 : ∀ i ∈ List.range 1, ThresholdAt 4 (50+i) := by decide +kernel

theorem threshold_4_51 : ∀ i ∈ List.range 1, ThresholdAt 4 (51+i) := by decide +kernel

theorem threshold_4_52 : ∀ i ∈ List.range 1, ThresholdAt 4 (52+i) := by decide +kernel

theorem threshold_4_53 : ∀ i ∈ List.range 1, ThresholdAt 4 (53+i) := by decide +kernel

theorem threshold_4_54 : ∀ i ∈ List.range 1, ThresholdAt 4 (54+i) := by decide +kernel

theorem threshold_4_55 : ∀ i ∈ List.range 1, ThresholdAt 4 (55+i) := by decide +kernel

theorem threshold_4_56 : ∀ i ∈ List.range 1, ThresholdAt 4 (56+i) := by decide +kernel

theorem threshold_4_57 : ∀ i ∈ List.range 1, ThresholdAt 4 (57+i) := by decide +kernel

theorem threshold_4_58 : ∀ i ∈ List.range 1, ThresholdAt 4 (58+i) := by decide +kernel

theorem threshold_4_59 : ∀ i ∈ List.range 1, ThresholdAt 4 (59+i) := by decide +kernel

theorem threshold_4_60 : ∀ i ∈ List.range 1, ThresholdAt 4 (60+i) := by decide +kernel

theorem threshold_4_61 : ∀ i ∈ List.range 1, ThresholdAt 4 (61+i) := by decide +kernel

theorem threshold_4_62 : ∀ i ∈ List.range 1, ThresholdAt 4 (62+i) := by decide +kernel

theorem threshold_4_63 : ∀ i ∈ List.range 1, ThresholdAt 4 (63+i) := by decide +kernel

theorem threshold_4_64 : ∀ i ∈ List.range 1, ThresholdAt 4 (64+i) := by decide +kernel

theorem threshold_4_65 : ∀ i ∈ List.range 1, ThresholdAt 4 (65+i) := by decide +kernel

theorem threshold_4_66 : ∀ i ∈ List.range 1, ThresholdAt 4 (66+i) := by decide +kernel

theorem threshold_4_67 : ∀ i ∈ List.range 1, ThresholdAt 4 (67+i) := by decide +kernel

theorem threshold_4_68 : ∀ i ∈ List.range 1, ThresholdAt 4 (68+i) := by decide +kernel

theorem threshold_4_69 : ∀ i ∈ List.range 1, ThresholdAt 4 (69+i) := by decide +kernel

theorem threshold_4_70 : ∀ i ∈ List.range 1, ThresholdAt 4 (70+i) := by decide +kernel

theorem threshold_4_71 : ∀ i ∈ List.range 1, ThresholdAt 4 (71+i) := by decide +kernel

theorem threshold_4_72 : ∀ i ∈ List.range 1, ThresholdAt 4 (72+i) := by decide +kernel

theorem threshold_4_73 : ∀ i ∈ List.range 1, ThresholdAt 4 (73+i) := by decide +kernel

theorem threshold_4_74 : ∀ i ∈ List.range 1, ThresholdAt 4 (74+i) := by decide +kernel

theorem threshold_4_75 : ∀ i ∈ List.range 1, ThresholdAt 4 (75+i) := by decide +kernel

theorem threshold_4_76 : ∀ i ∈ List.range 1, ThresholdAt 4 (76+i) := by decide +kernel

theorem threshold_4_77 : ∀ i ∈ List.range 1, ThresholdAt 4 (77+i) := by decide +kernel

theorem threshold_4_78 : ∀ i ∈ List.range 1, ThresholdAt 4 (78+i) := by decide +kernel

theorem threshold_4_79 : ∀ i ∈ List.range 1, ThresholdAt 4 (79+i) := by decide +kernel

theorem threshold_4_80 : ∀ i ∈ List.range 1, ThresholdAt 4 (80+i) := by decide +kernel

theorem threshold_4_81 : ∀ i ∈ List.range 1, ThresholdAt 4 (81+i) := by decide +kernel

theorem threshold_4_82 : ∀ i ∈ List.range 1, ThresholdAt 4 (82+i) := by decide +kernel

theorem threshold_4_83 : ∀ i ∈ List.range 1, ThresholdAt 4 (83+i) := by decide +kernel

theorem threshold_4_84 : ∀ i ∈ List.range 1, ThresholdAt 4 (84+i) := by decide +kernel

theorem threshold_4_85 : ∀ i ∈ List.range 1, ThresholdAt 4 (85+i) := by decide +kernel

theorem threshold_4_86 : ∀ i ∈ List.range 1, ThresholdAt 4 (86+i) := by decide +kernel

theorem threshold_4_87 : ∀ i ∈ List.range 1, ThresholdAt 4 (87+i) := by decide +kernel

theorem threshold_4_88 : ∀ i ∈ List.range 1, ThresholdAt 4 (88+i) := by decide +kernel

theorem threshold_4_89 : ∀ i ∈ List.range 1, ThresholdAt 4 (89+i) := by decide +kernel

theorem threshold_4_90 : ∀ i ∈ List.range 1, ThresholdAt 4 (90+i) := by decide +kernel

theorem threshold_4_91 : ∀ i ∈ List.range 1, ThresholdAt 4 (91+i) := by decide +kernel

theorem threshold_4_92 : ∀ i ∈ List.range 1, ThresholdAt 4 (92+i) := by decide +kernel

theorem threshold_4_93 : ∀ i ∈ List.range 1, ThresholdAt 4 (93+i) := by decide +kernel

theorem threshold_4_94 : ∀ i ∈ List.range 1, ThresholdAt 4 (94+i) := by decide +kernel

theorem threshold_4_95 : ∀ i ∈ List.range 1, ThresholdAt 4 (95+i) := by decide +kernel

theorem threshold_4_96 : ∀ i ∈ List.range 1, ThresholdAt 4 (96+i) := by decide +kernel

theorem threshold_4_97 : ∀ i ∈ List.range 1, ThresholdAt 4 (97+i) := by decide +kernel

theorem threshold_4_98 : ∀ i ∈ List.range 1, ThresholdAt 4 (98+i) := by decide +kernel

theorem threshold_4_99 : ∀ i ∈ List.range 1, ThresholdAt 4 (99+i) := by decide +kernel

theorem threshold_4_100 : ∀ i ∈ List.range 1, ThresholdAt 4 (100+i) := by decide +kernel

theorem threshold_4_101 : ∀ i ∈ List.range 1, ThresholdAt 4 (101+i) := by decide +kernel

theorem threshold_4_102 : ∀ i ∈ List.range 1, ThresholdAt 4 (102+i) := by decide +kernel

theorem threshold_4_103 : ∀ i ∈ List.range 1, ThresholdAt 4 (103+i) := by decide +kernel

theorem threshold_4_104 : ∀ i ∈ List.range 1, ThresholdAt 4 (104+i) := by decide +kernel

theorem threshold_4_105 : ∀ i ∈ List.range 1, ThresholdAt 4 (105+i) := by decide +kernel

theorem threshold_4_106 : ∀ i ∈ List.range 1, ThresholdAt 4 (106+i) := by decide +kernel

theorem threshold_4_107 : ∀ i ∈ List.range 1, ThresholdAt 4 (107+i) := by decide +kernel

theorem threshold_4_108 : ∀ i ∈ List.range 1, ThresholdAt 4 (108+i) := by decide +kernel

theorem threshold_4_109 : ∀ i ∈ List.range 1, ThresholdAt 4 (109+i) := by decide +kernel

theorem threshold_4_110 : ∀ i ∈ List.range 1, ThresholdAt 4 (110+i) := by decide +kernel

theorem threshold_4_111 : ∀ i ∈ List.range 1, ThresholdAt 4 (111+i) := by decide +kernel

theorem threshold_4_112 : ∀ i ∈ List.range 1, ThresholdAt 4 (112+i) := by decide +kernel

theorem threshold_4_113 : ∀ i ∈ List.range 1, ThresholdAt 4 (113+i) := by decide +kernel

theorem threshold_4_114 : ∀ i ∈ List.range 1, ThresholdAt 4 (114+i) := by decide +kernel

theorem threshold_4_115 : ∀ i ∈ List.range 1, ThresholdAt 4 (115+i) := by decide +kernel

theorem threshold_4_116 : ∀ i ∈ List.range 1, ThresholdAt 4 (116+i) := by decide +kernel

theorem threshold_4_117 : ∀ i ∈ List.range 1, ThresholdAt 4 (117+i) := by decide +kernel

theorem threshold_4_118 : ∀ i ∈ List.range 1, ThresholdAt 4 (118+i) := by decide +kernel

theorem threshold_4_119 : ∀ i ∈ List.range 1, ThresholdAt 4 (119+i) := by decide +kernel

theorem threshold_4_120 : ∀ i ∈ List.range 1, ThresholdAt 4 (120+i) := by decide +kernel

theorem threshold_4_121 : ∀ i ∈ List.range 1, ThresholdAt 4 (121+i) := by decide +kernel

theorem threshold_4_122 : ∀ i ∈ List.range 1, ThresholdAt 4 (122+i) := by decide +kernel

theorem threshold_4_123 : ∀ i ∈ List.range 1, ThresholdAt 4 (123+i) := by decide +kernel

theorem threshold_4_124 : ∀ i ∈ List.range 1, ThresholdAt 4 (124+i) := by decide +kernel

theorem threshold_4_125 : ∀ i ∈ List.range 1, ThresholdAt 4 (125+i) := by decide +kernel

theorem threshold_4_126 : ∀ i ∈ List.range 1, ThresholdAt 4 (126+i) := by decide +kernel

theorem threshold_4_127 : ∀ i ∈ List.range 1, ThresholdAt 4 (127+i) := by decide +kernel

theorem threshold_4_128 : ∀ i ∈ List.range 1, ThresholdAt 4 (128+i) := by decide +kernel

theorem threshold_4_129 : ∀ i ∈ List.range 1, ThresholdAt 4 (129+i) := by decide +kernel

theorem threshold_4_130 : ∀ i ∈ List.range 1, ThresholdAt 4 (130+i) := by decide +kernel

theorem threshold_4_131 : ∀ i ∈ List.range 1, ThresholdAt 4 (131+i) := by decide +kernel

theorem threshold_4_132 : ∀ i ∈ List.range 1, ThresholdAt 4 (132+i) := by decide +kernel

theorem threshold_4_133 : ∀ i ∈ List.range 1, ThresholdAt 4 (133+i) := by decide +kernel

theorem threshold_4_134 : ∀ i ∈ List.range 1, ThresholdAt 4 (134+i) := by decide +kernel

theorem threshold_4_135 : ∀ i ∈ List.range 1, ThresholdAt 4 (135+i) := by decide +kernel

theorem threshold_4_136 : ∀ i ∈ List.range 1, ThresholdAt 4 (136+i) := by decide +kernel

theorem threshold_4_137 : ∀ i ∈ List.range 1, ThresholdAt 4 (137+i) := by decide +kernel

theorem threshold_4_138 : ∀ i ∈ List.range 1, ThresholdAt 4 (138+i) := by decide +kernel

theorem threshold_4_139 : ∀ i ∈ List.range 1, ThresholdAt 4 (139+i) := by decide +kernel

theorem threshold_4_140 : ∀ i ∈ List.range 1, ThresholdAt 4 (140+i) := by decide +kernel

theorem threshold_4_141 : ∀ i ∈ List.range 1, ThresholdAt 4 (141+i) := by decide +kernel

theorem threshold_4_142 : ∀ i ∈ List.range 1, ThresholdAt 4 (142+i) := by decide +kernel

theorem threshold_4_143 : ∀ i ∈ List.range 1, ThresholdAt 4 (143+i) := by decide +kernel

theorem threshold_4_144 : ∀ i ∈ List.range 1, ThresholdAt 4 (144+i) := by decide +kernel

theorem threshold_4_145 : ∀ i ∈ List.range 1, ThresholdAt 4 (145+i) := by decide +kernel

theorem threshold_4_146 : ∀ i ∈ List.range 1, ThresholdAt 4 (146+i) := by decide +kernel

theorem threshold_4_147 : ∀ i ∈ List.range 1, ThresholdAt 4 (147+i) := by decide +kernel

theorem threshold_4_148 : ∀ i ∈ List.range 1, ThresholdAt 4 (148+i) := by decide +kernel

theorem threshold_4_149 : ∀ i ∈ List.range 1, ThresholdAt 4 (149+i) := by decide +kernel

theorem threshold_4_150 : ∀ i ∈ List.range 1, ThresholdAt 4 (150+i) := by decide +kernel

theorem threshold_4_151 : ∀ i ∈ List.range 1, ThresholdAt 4 (151+i) := by decide +kernel

theorem threshold_4_152 : ∀ i ∈ List.range 1, ThresholdAt 4 (152+i) := by decide +kernel

theorem threshold_4 (v : ℕ) (hv : v ∈ List.range 153) : ThresholdAt 4 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 4 v)
  have h := (join 0 76 77 (join 0 38 38 (join 0 19 19 (join 0 9 10 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_4_0 threshold_4_1) (join 2 1 1 threshold_4_2 threshold_4_3)) (join 4 2 3 (join 4 1 1 threshold_4_4 threshold_4_5) (join 6 1 2 threshold_4_6 (join 7 1 1 threshold_4_7 threshold_4_8)))) (join 9 5 5 (join 9 2 3 (join 9 1 1 threshold_4_9 threshold_4_10) (join 11 1 2 threshold_4_11 (join 12 1 1 threshold_4_12 threshold_4_13))) (join 14 2 3 (join 14 1 1 threshold_4_14 threshold_4_15) (join 16 1 2 threshold_4_16 (join 17 1 1 threshold_4_17 threshold_4_18))))) (join 19 9 10 (join 19 4 5 (join 19 2 2 (join 19 1 1 threshold_4_19 threshold_4_20) (join 21 1 1 threshold_4_21 threshold_4_22)) (join 23 2 3 (join 23 1 1 threshold_4_23 threshold_4_24) (join 25 1 2 threshold_4_25 (join 26 1 1 threshold_4_26 threshold_4_27)))) (join 28 5 5 (join 28 2 3 (join 28 1 1 threshold_4_28 threshold_4_29) (join 30 1 2 threshold_4_30 (join 31 1 1 threshold_4_31 threshold_4_32))) (join 33 2 3 (join 33 1 1 threshold_4_33 threshold_4_34) (join 35 1 2 threshold_4_35 (join 36 1 1 threshold_4_36 threshold_4_37)))))) (join 38 19 19 (join 38 9 10 (join 38 4 5 (join 38 2 2 (join 38 1 1 threshold_4_38 threshold_4_39) (join 40 1 1 threshold_4_40 threshold_4_41)) (join 42 2 3 (join 42 1 1 threshold_4_42 threshold_4_43) (join 44 1 2 threshold_4_44 (join 45 1 1 threshold_4_45 threshold_4_46)))) (join 47 5 5 (join 47 2 3 (join 47 1 1 threshold_4_47 threshold_4_48) (join 49 1 2 threshold_4_49 (join 50 1 1 threshold_4_50 threshold_4_51))) (join 52 2 3 (join 52 1 1 threshold_4_52 threshold_4_53) (join 54 1 2 threshold_4_54 (join 55 1 1 threshold_4_55 threshold_4_56))))) (join 57 9 10 (join 57 4 5 (join 57 2 2 (join 57 1 1 threshold_4_57 threshold_4_58) (join 59 1 1 threshold_4_59 threshold_4_60)) (join 61 2 3 (join 61 1 1 threshold_4_61 threshold_4_62) (join 63 1 2 threshold_4_63 (join 64 1 1 threshold_4_64 threshold_4_65)))) (join 66 5 5 (join 66 2 3 (join 66 1 1 threshold_4_66 threshold_4_67) (join 68 1 2 threshold_4_68 (join 69 1 1 threshold_4_69 threshold_4_70))) (join 71 2 3 (join 71 1 1 threshold_4_71 threshold_4_72) (join 73 1 2 threshold_4_73 (join 74 1 1 threshold_4_74 threshold_4_75))))))) (join 76 38 39 (join 76 19 19 (join 76 9 10 (join 76 4 5 (join 76 2 2 (join 76 1 1 threshold_4_76 threshold_4_77) (join 78 1 1 threshold_4_78 threshold_4_79)) (join 80 2 3 (join 80 1 1 threshold_4_80 threshold_4_81) (join 82 1 2 threshold_4_82 (join 83 1 1 threshold_4_83 threshold_4_84)))) (join 85 5 5 (join 85 2 3 (join 85 1 1 threshold_4_85 threshold_4_86) (join 87 1 2 threshold_4_87 (join 88 1 1 threshold_4_88 threshold_4_89))) (join 90 2 3 (join 90 1 1 threshold_4_90 threshold_4_91) (join 92 1 2 threshold_4_92 (join 93 1 1 threshold_4_93 threshold_4_94))))) (join 95 9 10 (join 95 4 5 (join 95 2 2 (join 95 1 1 threshold_4_95 threshold_4_96) (join 97 1 1 threshold_4_97 threshold_4_98)) (join 99 2 3 (join 99 1 1 threshold_4_99 threshold_4_100) (join 101 1 2 threshold_4_101 (join 102 1 1 threshold_4_102 threshold_4_103)))) (join 104 5 5 (join 104 2 3 (join 104 1 1 threshold_4_104 threshold_4_105) (join 106 1 2 threshold_4_106 (join 107 1 1 threshold_4_107 threshold_4_108))) (join 109 2 3 (join 109 1 1 threshold_4_109 threshold_4_110) (join 111 1 2 threshold_4_111 (join 112 1 1 threshold_4_112 threshold_4_113)))))) (join 114 19 20 (join 114 9 10 (join 114 4 5 (join 114 2 2 (join 114 1 1 threshold_4_114 threshold_4_115) (join 116 1 1 threshold_4_116 threshold_4_117)) (join 118 2 3 (join 118 1 1 threshold_4_118 threshold_4_119) (join 120 1 2 threshold_4_120 (join 121 1 1 threshold_4_121 threshold_4_122)))) (join 123 5 5 (join 123 2 3 (join 123 1 1 threshold_4_123 threshold_4_124) (join 125 1 2 threshold_4_125 (join 126 1 1 threshold_4_126 threshold_4_127))) (join 128 2 3 (join 128 1 1 threshold_4_128 threshold_4_129) (join 130 1 2 threshold_4_130 (join 131 1 1 threshold_4_131 threshold_4_132))))) (join 133 10 10 (join 133 5 5 (join 133 2 3 (join 133 1 1 threshold_4_133 threshold_4_134) (join 135 1 2 threshold_4_135 (join 136 1 1 threshold_4_136 threshold_4_137))) (join 138 2 3 (join 138 1 1 threshold_4_138 threshold_4_139) (join 140 1 2 threshold_4_140 (join 141 1 1 threshold_4_141 threshold_4_142)))) (join 143 5 5 (join 143 2 3 (join 143 1 1 threshold_4_143 threshold_4_144) (join 145 1 2 threshold_4_145 (join 146 1 1 threshold_4_146 threshold_4_147))) (join 148 2 3 (join 148 1 1 threshold_4_148 threshold_4_149) (join 150 1 2 threshold_4_150 (join 151 1 1 threshold_4_151 threshold_4_152))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_4_0 : ∀ i ∈ List.range 4, LedgerAt 4 (0+i) := by decide +kernel

theorem ledger_4_4 : ∀ i ∈ List.range 4, LedgerAt 4 (4+i) := by decide +kernel

theorem ledger_4_8 : ∀ i ∈ List.range 4, LedgerAt 4 (8+i) := by decide +kernel

theorem ledger_4_12 : ∀ i ∈ List.range 4, LedgerAt 4 (12+i) := by decide +kernel

theorem ledger_4_16 : ∀ i ∈ List.range 4, LedgerAt 4 (16+i) := by decide +kernel

theorem ledger_4_20 : ∀ i ∈ List.range 4, LedgerAt 4 (20+i) := by decide +kernel

theorem ledger_4_24 : ∀ i ∈ List.range 4, LedgerAt 4 (24+i) := by decide +kernel

theorem ledger_4_28 : ∀ i ∈ List.range 4, LedgerAt 4 (28+i) := by decide +kernel

theorem ledger_4_32 : ∀ i ∈ List.range 4, LedgerAt 4 (32+i) := by decide +kernel

theorem ledger_4_36 : ∀ i ∈ List.range 4, LedgerAt 4 (36+i) := by decide +kernel

theorem ledger_4_40 : ∀ i ∈ List.range 4, LedgerAt 4 (40+i) := by decide +kernel

theorem ledger_4_44 : ∀ i ∈ List.range 4, LedgerAt 4 (44+i) := by decide +kernel

theorem ledger_4_48 : ∀ i ∈ List.range 4, LedgerAt 4 (48+i) := by decide +kernel

theorem ledger_4_52 : ∀ i ∈ List.range 4, LedgerAt 4 (52+i) := by decide +kernel

theorem ledger_4_56 : ∀ i ∈ List.range 4, LedgerAt 4 (56+i) := by decide +kernel

theorem ledger_4_60 : ∀ i ∈ List.range 4, LedgerAt 4 (60+i) := by decide +kernel

theorem ledger_4_64 : ∀ i ∈ List.range 4, LedgerAt 4 (64+i) := by decide +kernel

theorem ledger_4_68 : ∀ i ∈ List.range 4, LedgerAt 4 (68+i) := by decide +kernel

theorem ledger_4_72 : ∀ i ∈ List.range 4, LedgerAt 4 (72+i) := by decide +kernel

theorem ledger_4_76 : ∀ i ∈ List.range 4, LedgerAt 4 (76+i) := by decide +kernel

theorem ledger_4_80 : ∀ i ∈ List.range 4, LedgerAt 4 (80+i) := by decide +kernel

theorem ledger_4_84 : ∀ i ∈ List.range 4, LedgerAt 4 (84+i) := by decide +kernel

theorem ledger_4_88 : ∀ i ∈ List.range 4, LedgerAt 4 (88+i) := by decide +kernel

theorem ledger_4_92 : ∀ i ∈ List.range 4, LedgerAt 4 (92+i) := by decide +kernel

theorem ledger_4_96 : ∀ i ∈ List.range 4, LedgerAt 4 (96+i) := by decide +kernel

theorem ledger_4_100 : ∀ i ∈ List.range 4, LedgerAt 4 (100+i) := by decide +kernel

theorem ledger_4_104 : ∀ i ∈ List.range 4, LedgerAt 4 (104+i) := by decide +kernel

theorem ledger_4_108 : ∀ i ∈ List.range 4, LedgerAt 4 (108+i) := by decide +kernel

theorem ledger_4_112 : ∀ i ∈ List.range 4, LedgerAt 4 (112+i) := by decide +kernel

theorem ledger_4_116 : ∀ i ∈ List.range 4, LedgerAt 4 (116+i) := by decide +kernel

theorem ledger_4_120 : ∀ i ∈ List.range 4, LedgerAt 4 (120+i) := by decide +kernel

theorem ledger_4_124 : ∀ i ∈ List.range 4, LedgerAt 4 (124+i) := by decide +kernel

theorem ledger_4_128 : ∀ i ∈ List.range 4, LedgerAt 4 (128+i) := by decide +kernel

theorem ledger_4_132 : ∀ i ∈ List.range 4, LedgerAt 4 (132+i) := by decide +kernel

theorem ledger_4_136 : ∀ i ∈ List.range 4, LedgerAt 4 (136+i) := by decide +kernel

theorem ledger_4_140 : ∀ i ∈ List.range 4, LedgerAt 4 (140+i) := by decide +kernel

theorem ledger_4_144 : ∀ i ∈ List.range 4, LedgerAt 4 (144+i) := by decide +kernel

theorem ledger_4_148 : ∀ i ∈ List.range 4, LedgerAt 4 (148+i) := by decide +kernel

theorem ledger_4_152 : ∀ i ∈ List.range 1, LedgerAt 4 (152+i) := by decide +kernel

theorem ledger_4 (v : ℕ) (hv : v ∈ List.range 153) : LedgerAt 4 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 4 v)
  have h := (join 0 76 77 (join 0 36 40 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_4_0 ledger_4_4) (join 8 4 4 ledger_4_8 ledger_4_12)) (join 16 8 12 (join 16 4 4 ledger_4_16 ledger_4_20) (join 24 4 8 ledger_4_24 (join 28 4 4 ledger_4_28 ledger_4_32)))) (join 36 20 20 (join 36 8 12 (join 36 4 4 ledger_4_36 ledger_4_40) (join 44 4 8 ledger_4_44 (join 48 4 4 ledger_4_48 ledger_4_52))) (join 56 8 12 (join 56 4 4 ledger_4_56 ledger_4_60) (join 64 4 8 ledger_4_64 (join 68 4 4 ledger_4_68 ledger_4_72))))) (join 76 40 37 (join 76 20 20 (join 76 8 12 (join 76 4 4 ledger_4_76 ledger_4_80) (join 84 4 8 ledger_4_84 (join 88 4 4 ledger_4_88 ledger_4_92))) (join 96 8 12 (join 96 4 4 ledger_4_96 ledger_4_100) (join 104 4 8 ledger_4_104 (join 108 4 4 ledger_4_108 ledger_4_112)))) (join 116 20 17 (join 116 8 12 (join 116 4 4 ledger_4_116 ledger_4_120) (join 124 4 8 ledger_4_124 (join 128 4 4 ledger_4_128 ledger_4_132))) (join 136 8 9 (join 136 4 4 ledger_4_136 ledger_4_140) (join 144 4 5 ledger_4_144 (join 148 4 1 ledger_4_148 ledger_4_152))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
