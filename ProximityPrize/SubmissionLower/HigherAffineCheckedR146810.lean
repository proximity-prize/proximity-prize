import ProximityPrize.SubmissionLower.HigherAffineCheckedR136810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_14_0 : ∀ i ∈ List.range 4, SingleAt 14 (0+i) := by decide +kernel

theorem single_14_4 : ∀ i ∈ List.range 4, SingleAt 14 (4+i) := by decide +kernel

theorem single_14_8 : ∀ i ∈ List.range 4, SingleAt 14 (8+i) := by decide +kernel

theorem single_14_12 : ∀ i ∈ List.range 4, SingleAt 14 (12+i) := by decide +kernel

theorem single_14_16 : ∀ i ∈ List.range 4, SingleAt 14 (16+i) := by decide +kernel

theorem single_14_20 : ∀ i ∈ List.range 4, SingleAt 14 (20+i) := by decide +kernel

theorem single_14_24 : ∀ i ∈ List.range 4, SingleAt 14 (24+i) := by decide +kernel

theorem single_14_28 : ∀ i ∈ List.range 4, SingleAt 14 (28+i) := by decide +kernel

theorem single_14_32 : ∀ i ∈ List.range 4, SingleAt 14 (32+i) := by decide +kernel

theorem single_14_36 : ∀ i ∈ List.range 4, SingleAt 14 (36+i) := by decide +kernel

theorem single_14_40 : ∀ i ∈ List.range 4, SingleAt 14 (40+i) := by decide +kernel

theorem single_14_44 : ∀ i ∈ List.range 4, SingleAt 14 (44+i) := by decide +kernel

theorem single_14_48 : ∀ i ∈ List.range 4, SingleAt 14 (48+i) := by decide +kernel

theorem single_14_52 : ∀ i ∈ List.range 4, SingleAt 14 (52+i) := by decide +kernel

theorem single_14_56 : ∀ i ∈ List.range 4, SingleAt 14 (56+i) := by decide +kernel

theorem single_14_60 : ∀ i ∈ List.range 4, SingleAt 14 (60+i) := by decide +kernel

theorem single_14_64 : ∀ i ∈ List.range 4, SingleAt 14 (64+i) := by decide +kernel

theorem single_14_68 : ∀ i ∈ List.range 4, SingleAt 14 (68+i) := by decide +kernel

theorem single_14_72 : ∀ i ∈ List.range 4, SingleAt 14 (72+i) := by decide +kernel

theorem single_14_76 : ∀ i ∈ List.range 4, SingleAt 14 (76+i) := by decide +kernel

theorem single_14_80 : ∀ i ∈ List.range 4, SingleAt 14 (80+i) := by decide +kernel

theorem single_14_84 : ∀ i ∈ List.range 4, SingleAt 14 (84+i) := by decide +kernel

theorem single_14_88 : ∀ i ∈ List.range 4, SingleAt 14 (88+i) := by decide +kernel

theorem single_14_92 : ∀ i ∈ List.range 4, SingleAt 14 (92+i) := by decide +kernel

theorem single_14_96 : ∀ i ∈ List.range 4, SingleAt 14 (96+i) := by decide +kernel

theorem single_14_100 : ∀ i ∈ List.range 4, SingleAt 14 (100+i) := by decide +kernel

theorem single_14_104 : ∀ i ∈ List.range 4, SingleAt 14 (104+i) := by decide +kernel

theorem single_14_108 : ∀ i ∈ List.range 4, SingleAt 14 (108+i) := by decide +kernel

theorem single_14_112 : ∀ i ∈ List.range 4, SingleAt 14 (112+i) := by decide +kernel

theorem single_14_116 : ∀ i ∈ List.range 4, SingleAt 14 (116+i) := by decide +kernel

theorem single_14_120 : ∀ i ∈ List.range 4, SingleAt 14 (120+i) := by decide +kernel

theorem single_14_124 : ∀ i ∈ List.range 4, SingleAt 14 (124+i) := by decide +kernel

theorem single_14_128 : ∀ i ∈ List.range 4, SingleAt 14 (128+i) := by decide +kernel

theorem single_14_132 : ∀ i ∈ List.range 4, SingleAt 14 (132+i) := by decide +kernel

theorem single_14_136 : ∀ i ∈ List.range 4, SingleAt 14 (136+i) := by decide +kernel

theorem single_14_140 : ∀ i ∈ List.range 3, SingleAt 14 (140+i) := by decide +kernel

theorem single_14 (v : ℕ) (hv : v ∈ List.range 143) : SingleAt 14 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 14 v)
  have h := (join 0 72 71 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_14_0 single_14_4) (join 8 4 4 single_14_8 single_14_12)) (join 16 8 12 (join 16 4 4 single_14_16 single_14_20) (join 24 4 8 single_14_24 (join 28 4 4 single_14_28 single_14_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_14_36 single_14_40) (join 44 4 4 single_14_44 single_14_48)) (join 52 8 12 (join 52 4 4 single_14_52 single_14_56) (join 60 4 8 single_14_60 (join 64 4 4 single_14_64 single_14_68))))) (join 72 36 35 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_14_72 single_14_76) (join 80 4 4 single_14_80 single_14_84)) (join 88 8 12 (join 88 4 4 single_14_88 single_14_92) (join 96 4 8 single_14_96 (join 100 4 4 single_14_100 single_14_104)))) (join 108 16 19 (join 108 8 8 (join 108 4 4 single_14_108 single_14_112) (join 116 4 4 single_14_116 single_14_120)) (join 124 8 11 (join 124 4 4 single_14_124 single_14_128) (join 132 4 7 single_14_132 (join 136 4 3 single_14_136 single_14_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_14_0 : ∀ i ∈ List.range 4, PhaseAt 14 (0+i) := by decide +kernel

theorem phase_14_4 : ∀ i ∈ List.range 4, PhaseAt 14 (4+i) := by decide +kernel

theorem phase_14_8 : ∀ i ∈ List.range 4, PhaseAt 14 (8+i) := by decide +kernel

theorem phase_14_12 : ∀ i ∈ List.range 4, PhaseAt 14 (12+i) := by decide +kernel

theorem phase_14_16 : ∀ i ∈ List.range 4, PhaseAt 14 (16+i) := by decide +kernel

theorem phase_14_20 : ∀ i ∈ List.range 4, PhaseAt 14 (20+i) := by decide +kernel

theorem phase_14_24 : ∀ i ∈ List.range 4, PhaseAt 14 (24+i) := by decide +kernel

theorem phase_14_28 : ∀ i ∈ List.range 4, PhaseAt 14 (28+i) := by decide +kernel

theorem phase_14_32 : ∀ i ∈ List.range 4, PhaseAt 14 (32+i) := by decide +kernel

theorem phase_14_36 : ∀ i ∈ List.range 4, PhaseAt 14 (36+i) := by decide +kernel

theorem phase_14_40 : ∀ i ∈ List.range 4, PhaseAt 14 (40+i) := by decide +kernel

theorem phase_14_44 : ∀ i ∈ List.range 4, PhaseAt 14 (44+i) := by decide +kernel

theorem phase_14_48 : ∀ i ∈ List.range 4, PhaseAt 14 (48+i) := by decide +kernel

theorem phase_14_52 : ∀ i ∈ List.range 4, PhaseAt 14 (52+i) := by decide +kernel

theorem phase_14_56 : ∀ i ∈ List.range 4, PhaseAt 14 (56+i) := by decide +kernel

theorem phase_14_60 : ∀ i ∈ List.range 4, PhaseAt 14 (60+i) := by decide +kernel

theorem phase_14_64 : ∀ i ∈ List.range 4, PhaseAt 14 (64+i) := by decide +kernel

theorem phase_14_68 : ∀ i ∈ List.range 4, PhaseAt 14 (68+i) := by decide +kernel

theorem phase_14_72 : ∀ i ∈ List.range 4, PhaseAt 14 (72+i) := by decide +kernel

theorem phase_14_76 : ∀ i ∈ List.range 4, PhaseAt 14 (76+i) := by decide +kernel

theorem phase_14_80 : ∀ i ∈ List.range 4, PhaseAt 14 (80+i) := by decide +kernel

theorem phase_14_84 : ∀ i ∈ List.range 4, PhaseAt 14 (84+i) := by decide +kernel

theorem phase_14_88 : ∀ i ∈ List.range 4, PhaseAt 14 (88+i) := by decide +kernel

theorem phase_14_92 : ∀ i ∈ List.range 4, PhaseAt 14 (92+i) := by decide +kernel

theorem phase_14_96 : ∀ i ∈ List.range 4, PhaseAt 14 (96+i) := by decide +kernel

theorem phase_14_100 : ∀ i ∈ List.range 4, PhaseAt 14 (100+i) := by decide +kernel

theorem phase_14_104 : ∀ i ∈ List.range 4, PhaseAt 14 (104+i) := by decide +kernel

theorem phase_14_108 : ∀ i ∈ List.range 4, PhaseAt 14 (108+i) := by decide +kernel

theorem phase_14_112 : ∀ i ∈ List.range 4, PhaseAt 14 (112+i) := by decide +kernel

theorem phase_14_116 : ∀ i ∈ List.range 4, PhaseAt 14 (116+i) := by decide +kernel

theorem phase_14_120 : ∀ i ∈ List.range 4, PhaseAt 14 (120+i) := by decide +kernel

theorem phase_14_124 : ∀ i ∈ List.range 4, PhaseAt 14 (124+i) := by decide +kernel

theorem phase_14_128 : ∀ i ∈ List.range 4, PhaseAt 14 (128+i) := by decide +kernel

theorem phase_14_132 : ∀ i ∈ List.range 4, PhaseAt 14 (132+i) := by decide +kernel

theorem phase_14_136 : ∀ i ∈ List.range 4, PhaseAt 14 (136+i) := by decide +kernel

theorem phase_14_140 : ∀ i ∈ List.range 3, PhaseAt 14 (140+i) := by decide +kernel

theorem phase_14 (v : ℕ) (hv : v ∈ List.range 143) : PhaseAt 14 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 14 v)
  have h := (join 0 72 71 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_14_0 phase_14_4) (join 8 4 4 phase_14_8 phase_14_12)) (join 16 8 12 (join 16 4 4 phase_14_16 phase_14_20) (join 24 4 8 phase_14_24 (join 28 4 4 phase_14_28 phase_14_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_14_36 phase_14_40) (join 44 4 4 phase_14_44 phase_14_48)) (join 52 8 12 (join 52 4 4 phase_14_52 phase_14_56) (join 60 4 8 phase_14_60 (join 64 4 4 phase_14_64 phase_14_68))))) (join 72 36 35 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_14_72 phase_14_76) (join 80 4 4 phase_14_80 phase_14_84)) (join 88 8 12 (join 88 4 4 phase_14_88 phase_14_92) (join 96 4 8 phase_14_96 (join 100 4 4 phase_14_100 phase_14_104)))) (join 108 16 19 (join 108 8 8 (join 108 4 4 phase_14_108 phase_14_112) (join 116 4 4 phase_14_116 phase_14_120)) (join 124 8 11 (join 124 4 4 phase_14_124 phase_14_128) (join 132 4 7 phase_14_132 (join 136 4 3 phase_14_136 phase_14_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_14_0 : ∀ i ∈ List.range 1, ThresholdAt 14 (0+i) := by decide +kernel

theorem threshold_14_1 : ∀ i ∈ List.range 1, ThresholdAt 14 (1+i) := by decide +kernel

theorem threshold_14_2 : ∀ i ∈ List.range 1, ThresholdAt 14 (2+i) := by decide +kernel

theorem threshold_14_3 : ∀ i ∈ List.range 1, ThresholdAt 14 (3+i) := by decide +kernel

theorem threshold_14_4 : ∀ i ∈ List.range 1, ThresholdAt 14 (4+i) := by decide +kernel

theorem threshold_14_5 : ∀ i ∈ List.range 1, ThresholdAt 14 (5+i) := by decide +kernel

theorem threshold_14_6 : ∀ i ∈ List.range 1, ThresholdAt 14 (6+i) := by decide +kernel

theorem threshold_14_7 : ∀ i ∈ List.range 1, ThresholdAt 14 (7+i) := by decide +kernel

theorem threshold_14_8 : ∀ i ∈ List.range 1, ThresholdAt 14 (8+i) := by decide +kernel

theorem threshold_14_9 : ∀ i ∈ List.range 1, ThresholdAt 14 (9+i) := by decide +kernel

theorem threshold_14_10 : ∀ i ∈ List.range 1, ThresholdAt 14 (10+i) := by decide +kernel

theorem threshold_14_11 : ∀ i ∈ List.range 1, ThresholdAt 14 (11+i) := by decide +kernel

theorem threshold_14_12 : ∀ i ∈ List.range 1, ThresholdAt 14 (12+i) := by decide +kernel

theorem threshold_14_13 : ∀ i ∈ List.range 1, ThresholdAt 14 (13+i) := by decide +kernel

theorem threshold_14_14 : ∀ i ∈ List.range 1, ThresholdAt 14 (14+i) := by decide +kernel

theorem threshold_14_15 : ∀ i ∈ List.range 1, ThresholdAt 14 (15+i) := by decide +kernel

theorem threshold_14_16 : ∀ i ∈ List.range 1, ThresholdAt 14 (16+i) := by decide +kernel

theorem threshold_14_17 : ∀ i ∈ List.range 1, ThresholdAt 14 (17+i) := by decide +kernel

theorem threshold_14_18 : ∀ i ∈ List.range 1, ThresholdAt 14 (18+i) := by decide +kernel

theorem threshold_14_19 : ∀ i ∈ List.range 1, ThresholdAt 14 (19+i) := by decide +kernel

theorem threshold_14_20 : ∀ i ∈ List.range 1, ThresholdAt 14 (20+i) := by decide +kernel

theorem threshold_14_21 : ∀ i ∈ List.range 1, ThresholdAt 14 (21+i) := by decide +kernel

theorem threshold_14_22 : ∀ i ∈ List.range 1, ThresholdAt 14 (22+i) := by decide +kernel

theorem threshold_14_23 : ∀ i ∈ List.range 1, ThresholdAt 14 (23+i) := by decide +kernel

theorem threshold_14_24 : ∀ i ∈ List.range 1, ThresholdAt 14 (24+i) := by decide +kernel

theorem threshold_14_25 : ∀ i ∈ List.range 1, ThresholdAt 14 (25+i) := by decide +kernel

theorem threshold_14_26 : ∀ i ∈ List.range 1, ThresholdAt 14 (26+i) := by decide +kernel

theorem threshold_14_27 : ∀ i ∈ List.range 1, ThresholdAt 14 (27+i) := by decide +kernel

theorem threshold_14_28 : ∀ i ∈ List.range 1, ThresholdAt 14 (28+i) := by decide +kernel

theorem threshold_14_29 : ∀ i ∈ List.range 1, ThresholdAt 14 (29+i) := by decide +kernel

theorem threshold_14_30 : ∀ i ∈ List.range 1, ThresholdAt 14 (30+i) := by decide +kernel

theorem threshold_14_31 : ∀ i ∈ List.range 1, ThresholdAt 14 (31+i) := by decide +kernel

theorem threshold_14_32 : ∀ i ∈ List.range 1, ThresholdAt 14 (32+i) := by decide +kernel

theorem threshold_14_33 : ∀ i ∈ List.range 1, ThresholdAt 14 (33+i) := by decide +kernel

theorem threshold_14_34 : ∀ i ∈ List.range 1, ThresholdAt 14 (34+i) := by decide +kernel

theorem threshold_14_35 : ∀ i ∈ List.range 1, ThresholdAt 14 (35+i) := by decide +kernel

theorem threshold_14_36 : ∀ i ∈ List.range 1, ThresholdAt 14 (36+i) := by decide +kernel

theorem threshold_14_37 : ∀ i ∈ List.range 1, ThresholdAt 14 (37+i) := by decide +kernel

theorem threshold_14_38 : ∀ i ∈ List.range 1, ThresholdAt 14 (38+i) := by decide +kernel

theorem threshold_14_39 : ∀ i ∈ List.range 1, ThresholdAt 14 (39+i) := by decide +kernel

theorem threshold_14_40 : ∀ i ∈ List.range 1, ThresholdAt 14 (40+i) := by decide +kernel

theorem threshold_14_41 : ∀ i ∈ List.range 1, ThresholdAt 14 (41+i) := by decide +kernel

theorem threshold_14_42 : ∀ i ∈ List.range 1, ThresholdAt 14 (42+i) := by decide +kernel

theorem threshold_14_43 : ∀ i ∈ List.range 1, ThresholdAt 14 (43+i) := by decide +kernel

theorem threshold_14_44 : ∀ i ∈ List.range 1, ThresholdAt 14 (44+i) := by decide +kernel

theorem threshold_14_45 : ∀ i ∈ List.range 1, ThresholdAt 14 (45+i) := by decide +kernel

theorem threshold_14_46 : ∀ i ∈ List.range 1, ThresholdAt 14 (46+i) := by decide +kernel

theorem threshold_14_47 : ∀ i ∈ List.range 1, ThresholdAt 14 (47+i) := by decide +kernel

theorem threshold_14_48 : ∀ i ∈ List.range 1, ThresholdAt 14 (48+i) := by decide +kernel

theorem threshold_14_49 : ∀ i ∈ List.range 1, ThresholdAt 14 (49+i) := by decide +kernel

theorem threshold_14_50 : ∀ i ∈ List.range 1, ThresholdAt 14 (50+i) := by decide +kernel

theorem threshold_14_51 : ∀ i ∈ List.range 1, ThresholdAt 14 (51+i) := by decide +kernel

theorem threshold_14_52 : ∀ i ∈ List.range 1, ThresholdAt 14 (52+i) := by decide +kernel

theorem threshold_14_53 : ∀ i ∈ List.range 1, ThresholdAt 14 (53+i) := by decide +kernel

theorem threshold_14_54 : ∀ i ∈ List.range 1, ThresholdAt 14 (54+i) := by decide +kernel

theorem threshold_14_55 : ∀ i ∈ List.range 1, ThresholdAt 14 (55+i) := by decide +kernel

theorem threshold_14_56 : ∀ i ∈ List.range 1, ThresholdAt 14 (56+i) := by decide +kernel

theorem threshold_14_57 : ∀ i ∈ List.range 1, ThresholdAt 14 (57+i) := by decide +kernel

theorem threshold_14_58 : ∀ i ∈ List.range 1, ThresholdAt 14 (58+i) := by decide +kernel

theorem threshold_14_59 : ∀ i ∈ List.range 1, ThresholdAt 14 (59+i) := by decide +kernel

theorem threshold_14_60 : ∀ i ∈ List.range 1, ThresholdAt 14 (60+i) := by decide +kernel

theorem threshold_14_61 : ∀ i ∈ List.range 1, ThresholdAt 14 (61+i) := by decide +kernel

theorem threshold_14_62 : ∀ i ∈ List.range 1, ThresholdAt 14 (62+i) := by decide +kernel

theorem threshold_14_63 : ∀ i ∈ List.range 1, ThresholdAt 14 (63+i) := by decide +kernel

theorem threshold_14_64 : ∀ i ∈ List.range 1, ThresholdAt 14 (64+i) := by decide +kernel

theorem threshold_14_65 : ∀ i ∈ List.range 1, ThresholdAt 14 (65+i) := by decide +kernel

theorem threshold_14_66 : ∀ i ∈ List.range 1, ThresholdAt 14 (66+i) := by decide +kernel

theorem threshold_14_67 : ∀ i ∈ List.range 1, ThresholdAt 14 (67+i) := by decide +kernel

theorem threshold_14_68 : ∀ i ∈ List.range 1, ThresholdAt 14 (68+i) := by decide +kernel

theorem threshold_14_69 : ∀ i ∈ List.range 1, ThresholdAt 14 (69+i) := by decide +kernel

theorem threshold_14_70 : ∀ i ∈ List.range 1, ThresholdAt 14 (70+i) := by decide +kernel

theorem threshold_14_71 : ∀ i ∈ List.range 1, ThresholdAt 14 (71+i) := by decide +kernel

theorem threshold_14_72 : ∀ i ∈ List.range 1, ThresholdAt 14 (72+i) := by decide +kernel

theorem threshold_14_73 : ∀ i ∈ List.range 1, ThresholdAt 14 (73+i) := by decide +kernel

theorem threshold_14_74 : ∀ i ∈ List.range 1, ThresholdAt 14 (74+i) := by decide +kernel

theorem threshold_14_75 : ∀ i ∈ List.range 1, ThresholdAt 14 (75+i) := by decide +kernel

theorem threshold_14_76 : ∀ i ∈ List.range 1, ThresholdAt 14 (76+i) := by decide +kernel

theorem threshold_14_77 : ∀ i ∈ List.range 1, ThresholdAt 14 (77+i) := by decide +kernel

theorem threshold_14_78 : ∀ i ∈ List.range 1, ThresholdAt 14 (78+i) := by decide +kernel

theorem threshold_14_79 : ∀ i ∈ List.range 1, ThresholdAt 14 (79+i) := by decide +kernel

theorem threshold_14_80 : ∀ i ∈ List.range 1, ThresholdAt 14 (80+i) := by decide +kernel

theorem threshold_14_81 : ∀ i ∈ List.range 1, ThresholdAt 14 (81+i) := by decide +kernel

theorem threshold_14_82 : ∀ i ∈ List.range 1, ThresholdAt 14 (82+i) := by decide +kernel

theorem threshold_14_83 : ∀ i ∈ List.range 1, ThresholdAt 14 (83+i) := by decide +kernel

theorem threshold_14_84 : ∀ i ∈ List.range 1, ThresholdAt 14 (84+i) := by decide +kernel

theorem threshold_14_85 : ∀ i ∈ List.range 1, ThresholdAt 14 (85+i) := by decide +kernel

theorem threshold_14_86 : ∀ i ∈ List.range 1, ThresholdAt 14 (86+i) := by decide +kernel

theorem threshold_14_87 : ∀ i ∈ List.range 1, ThresholdAt 14 (87+i) := by decide +kernel

theorem threshold_14_88 : ∀ i ∈ List.range 1, ThresholdAt 14 (88+i) := by decide +kernel

theorem threshold_14_89 : ∀ i ∈ List.range 1, ThresholdAt 14 (89+i) := by decide +kernel

theorem threshold_14_90 : ∀ i ∈ List.range 1, ThresholdAt 14 (90+i) := by decide +kernel

theorem threshold_14_91 : ∀ i ∈ List.range 1, ThresholdAt 14 (91+i) := by decide +kernel

theorem threshold_14_92 : ∀ i ∈ List.range 1, ThresholdAt 14 (92+i) := by decide +kernel

theorem threshold_14_93 : ∀ i ∈ List.range 1, ThresholdAt 14 (93+i) := by decide +kernel

theorem threshold_14_94 : ∀ i ∈ List.range 1, ThresholdAt 14 (94+i) := by decide +kernel

theorem threshold_14_95 : ∀ i ∈ List.range 1, ThresholdAt 14 (95+i) := by decide +kernel

theorem threshold_14_96 : ∀ i ∈ List.range 1, ThresholdAt 14 (96+i) := by decide +kernel

theorem threshold_14_97 : ∀ i ∈ List.range 1, ThresholdAt 14 (97+i) := by decide +kernel

theorem threshold_14_98 : ∀ i ∈ List.range 1, ThresholdAt 14 (98+i) := by decide +kernel

theorem threshold_14_99 : ∀ i ∈ List.range 1, ThresholdAt 14 (99+i) := by decide +kernel

theorem threshold_14_100 : ∀ i ∈ List.range 1, ThresholdAt 14 (100+i) := by decide +kernel

theorem threshold_14_101 : ∀ i ∈ List.range 1, ThresholdAt 14 (101+i) := by decide +kernel

theorem threshold_14_102 : ∀ i ∈ List.range 1, ThresholdAt 14 (102+i) := by decide +kernel

theorem threshold_14_103 : ∀ i ∈ List.range 1, ThresholdAt 14 (103+i) := by decide +kernel

theorem threshold_14_104 : ∀ i ∈ List.range 1, ThresholdAt 14 (104+i) := by decide +kernel

theorem threshold_14_105 : ∀ i ∈ List.range 1, ThresholdAt 14 (105+i) := by decide +kernel

theorem threshold_14_106 : ∀ i ∈ List.range 1, ThresholdAt 14 (106+i) := by decide +kernel

theorem threshold_14_107 : ∀ i ∈ List.range 1, ThresholdAt 14 (107+i) := by decide +kernel

theorem threshold_14_108 : ∀ i ∈ List.range 1, ThresholdAt 14 (108+i) := by decide +kernel

theorem threshold_14_109 : ∀ i ∈ List.range 1, ThresholdAt 14 (109+i) := by decide +kernel

theorem threshold_14_110 : ∀ i ∈ List.range 1, ThresholdAt 14 (110+i) := by decide +kernel

theorem threshold_14_111 : ∀ i ∈ List.range 1, ThresholdAt 14 (111+i) := by decide +kernel

theorem threshold_14_112 : ∀ i ∈ List.range 1, ThresholdAt 14 (112+i) := by decide +kernel

theorem threshold_14_113 : ∀ i ∈ List.range 1, ThresholdAt 14 (113+i) := by decide +kernel

theorem threshold_14_114 : ∀ i ∈ List.range 1, ThresholdAt 14 (114+i) := by decide +kernel

theorem threshold_14_115 : ∀ i ∈ List.range 1, ThresholdAt 14 (115+i) := by decide +kernel

theorem threshold_14_116 : ∀ i ∈ List.range 1, ThresholdAt 14 (116+i) := by decide +kernel

theorem threshold_14_117 : ∀ i ∈ List.range 1, ThresholdAt 14 (117+i) := by decide +kernel

theorem threshold_14_118 : ∀ i ∈ List.range 1, ThresholdAt 14 (118+i) := by decide +kernel

theorem threshold_14_119 : ∀ i ∈ List.range 1, ThresholdAt 14 (119+i) := by decide +kernel

theorem threshold_14_120 : ∀ i ∈ List.range 1, ThresholdAt 14 (120+i) := by decide +kernel

theorem threshold_14_121 : ∀ i ∈ List.range 1, ThresholdAt 14 (121+i) := by decide +kernel

theorem threshold_14_122 : ∀ i ∈ List.range 1, ThresholdAt 14 (122+i) := by decide +kernel

theorem threshold_14_123 : ∀ i ∈ List.range 1, ThresholdAt 14 (123+i) := by decide +kernel

theorem threshold_14_124 : ∀ i ∈ List.range 1, ThresholdAt 14 (124+i) := by decide +kernel

theorem threshold_14_125 : ∀ i ∈ List.range 1, ThresholdAt 14 (125+i) := by decide +kernel

theorem threshold_14_126 : ∀ i ∈ List.range 1, ThresholdAt 14 (126+i) := by decide +kernel

theorem threshold_14_127 : ∀ i ∈ List.range 1, ThresholdAt 14 (127+i) := by decide +kernel

theorem threshold_14_128 : ∀ i ∈ List.range 1, ThresholdAt 14 (128+i) := by decide +kernel

theorem threshold_14_129 : ∀ i ∈ List.range 1, ThresholdAt 14 (129+i) := by decide +kernel

theorem threshold_14_130 : ∀ i ∈ List.range 1, ThresholdAt 14 (130+i) := by decide +kernel

theorem threshold_14_131 : ∀ i ∈ List.range 1, ThresholdAt 14 (131+i) := by decide +kernel

theorem threshold_14_132 : ∀ i ∈ List.range 1, ThresholdAt 14 (132+i) := by decide +kernel

theorem threshold_14_133 : ∀ i ∈ List.range 1, ThresholdAt 14 (133+i) := by decide +kernel

theorem threshold_14_134 : ∀ i ∈ List.range 1, ThresholdAt 14 (134+i) := by decide +kernel

theorem threshold_14_135 : ∀ i ∈ List.range 1, ThresholdAt 14 (135+i) := by decide +kernel

theorem threshold_14_136 : ∀ i ∈ List.range 1, ThresholdAt 14 (136+i) := by decide +kernel

theorem threshold_14_137 : ∀ i ∈ List.range 1, ThresholdAt 14 (137+i) := by decide +kernel

theorem threshold_14_138 : ∀ i ∈ List.range 1, ThresholdAt 14 (138+i) := by decide +kernel

theorem threshold_14_139 : ∀ i ∈ List.range 1, ThresholdAt 14 (139+i) := by decide +kernel

theorem threshold_14_140 : ∀ i ∈ List.range 1, ThresholdAt 14 (140+i) := by decide +kernel

theorem threshold_14_141 : ∀ i ∈ List.range 1, ThresholdAt 14 (141+i) := by decide +kernel

theorem threshold_14_142 : ∀ i ∈ List.range 1, ThresholdAt 14 (142+i) := by decide +kernel

theorem threshold_14 (v : ℕ) (hv : v ∈ List.range 143) : ThresholdAt 14 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 14 v)
  have h := (join 0 71 72 (join 0 35 36 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_14_0 threshold_14_1) (join 2 1 1 threshold_14_2 threshold_14_3)) (join 4 2 2 (join 4 1 1 threshold_14_4 threshold_14_5) (join 6 1 1 threshold_14_6 threshold_14_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_14_8 threshold_14_9) (join 10 1 1 threshold_14_10 threshold_14_11)) (join 12 2 3 (join 12 1 1 threshold_14_12 threshold_14_13) (join 14 1 2 threshold_14_14 (join 15 1 1 threshold_14_15 threshold_14_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 threshold_14_17 threshold_14_18) (join 19 1 1 threshold_14_19 threshold_14_20)) (join 21 2 3 (join 21 1 1 threshold_14_21 threshold_14_22) (join 23 1 2 threshold_14_23 (join 24 1 1 threshold_14_24 threshold_14_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 threshold_14_26 threshold_14_27) (join 28 1 1 threshold_14_28 threshold_14_29)) (join 30 2 3 (join 30 1 1 threshold_14_30 threshold_14_31) (join 32 1 2 threshold_14_32 (join 33 1 1 threshold_14_33 threshold_14_34)))))) (join 35 18 18 (join 35 9 9 (join 35 4 5 (join 35 2 2 (join 35 1 1 threshold_14_35 threshold_14_36) (join 37 1 1 threshold_14_37 threshold_14_38)) (join 39 2 3 (join 39 1 1 threshold_14_39 threshold_14_40) (join 41 1 2 threshold_14_41 (join 42 1 1 threshold_14_42 threshold_14_43)))) (join 44 4 5 (join 44 2 2 (join 44 1 1 threshold_14_44 threshold_14_45) (join 46 1 1 threshold_14_46 threshold_14_47)) (join 48 2 3 (join 48 1 1 threshold_14_48 threshold_14_49) (join 50 1 2 threshold_14_50 (join 51 1 1 threshold_14_51 threshold_14_52))))) (join 53 9 9 (join 53 4 5 (join 53 2 2 (join 53 1 1 threshold_14_53 threshold_14_54) (join 55 1 1 threshold_14_55 threshold_14_56)) (join 57 2 3 (join 57 1 1 threshold_14_57 threshold_14_58) (join 59 1 2 threshold_14_59 (join 60 1 1 threshold_14_60 threshold_14_61)))) (join 62 4 5 (join 62 2 2 (join 62 1 1 threshold_14_62 threshold_14_63) (join 64 1 1 threshold_14_64 threshold_14_65)) (join 66 2 3 (join 66 1 1 threshold_14_66 threshold_14_67) (join 68 1 2 threshold_14_68 (join 69 1 1 threshold_14_69 threshold_14_70))))))) (join 71 36 36 (join 71 18 18 (join 71 9 9 (join 71 4 5 (join 71 2 2 (join 71 1 1 threshold_14_71 threshold_14_72) (join 73 1 1 threshold_14_73 threshold_14_74)) (join 75 2 3 (join 75 1 1 threshold_14_75 threshold_14_76) (join 77 1 2 threshold_14_77 (join 78 1 1 threshold_14_78 threshold_14_79)))) (join 80 4 5 (join 80 2 2 (join 80 1 1 threshold_14_80 threshold_14_81) (join 82 1 1 threshold_14_82 threshold_14_83)) (join 84 2 3 (join 84 1 1 threshold_14_84 threshold_14_85) (join 86 1 2 threshold_14_86 (join 87 1 1 threshold_14_87 threshold_14_88))))) (join 89 9 9 (join 89 4 5 (join 89 2 2 (join 89 1 1 threshold_14_89 threshold_14_90) (join 91 1 1 threshold_14_91 threshold_14_92)) (join 93 2 3 (join 93 1 1 threshold_14_93 threshold_14_94) (join 95 1 2 threshold_14_95 (join 96 1 1 threshold_14_96 threshold_14_97)))) (join 98 4 5 (join 98 2 2 (join 98 1 1 threshold_14_98 threshold_14_99) (join 100 1 1 threshold_14_100 threshold_14_101)) (join 102 2 3 (join 102 1 1 threshold_14_102 threshold_14_103) (join 104 1 2 threshold_14_104 (join 105 1 1 threshold_14_105 threshold_14_106)))))) (join 107 18 18 (join 107 9 9 (join 107 4 5 (join 107 2 2 (join 107 1 1 threshold_14_107 threshold_14_108) (join 109 1 1 threshold_14_109 threshold_14_110)) (join 111 2 3 (join 111 1 1 threshold_14_111 threshold_14_112) (join 113 1 2 threshold_14_113 (join 114 1 1 threshold_14_114 threshold_14_115)))) (join 116 4 5 (join 116 2 2 (join 116 1 1 threshold_14_116 threshold_14_117) (join 118 1 1 threshold_14_118 threshold_14_119)) (join 120 2 3 (join 120 1 1 threshold_14_120 threshold_14_121) (join 122 1 2 threshold_14_122 (join 123 1 1 threshold_14_123 threshold_14_124))))) (join 125 9 9 (join 125 4 5 (join 125 2 2 (join 125 1 1 threshold_14_125 threshold_14_126) (join 127 1 1 threshold_14_127 threshold_14_128)) (join 129 2 3 (join 129 1 1 threshold_14_129 threshold_14_130) (join 131 1 2 threshold_14_131 (join 132 1 1 threshold_14_132 threshold_14_133)))) (join 134 4 5 (join 134 2 2 (join 134 1 1 threshold_14_134 threshold_14_135) (join 136 1 1 threshold_14_136 threshold_14_137)) (join 138 2 3 (join 138 1 1 threshold_14_138 threshold_14_139) (join 140 1 2 threshold_14_140 (join 141 1 1 threshold_14_141 threshold_14_142))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_14_0 : ∀ i ∈ List.range 4, LedgerAt 14 (0+i) := by decide +kernel

theorem ledger_14_4 : ∀ i ∈ List.range 4, LedgerAt 14 (4+i) := by decide +kernel

theorem ledger_14_8 : ∀ i ∈ List.range 4, LedgerAt 14 (8+i) := by decide +kernel

theorem ledger_14_12 : ∀ i ∈ List.range 4, LedgerAt 14 (12+i) := by decide +kernel

theorem ledger_14_16 : ∀ i ∈ List.range 4, LedgerAt 14 (16+i) := by decide +kernel

theorem ledger_14_20 : ∀ i ∈ List.range 4, LedgerAt 14 (20+i) := by decide +kernel

theorem ledger_14_24 : ∀ i ∈ List.range 4, LedgerAt 14 (24+i) := by decide +kernel

theorem ledger_14_28 : ∀ i ∈ List.range 4, LedgerAt 14 (28+i) := by decide +kernel

theorem ledger_14_32 : ∀ i ∈ List.range 4, LedgerAt 14 (32+i) := by decide +kernel

theorem ledger_14_36 : ∀ i ∈ List.range 4, LedgerAt 14 (36+i) := by decide +kernel

theorem ledger_14_40 : ∀ i ∈ List.range 4, LedgerAt 14 (40+i) := by decide +kernel

theorem ledger_14_44 : ∀ i ∈ List.range 4, LedgerAt 14 (44+i) := by decide +kernel

theorem ledger_14_48 : ∀ i ∈ List.range 4, LedgerAt 14 (48+i) := by decide +kernel

theorem ledger_14_52 : ∀ i ∈ List.range 4, LedgerAt 14 (52+i) := by decide +kernel

theorem ledger_14_56 : ∀ i ∈ List.range 4, LedgerAt 14 (56+i) := by decide +kernel

theorem ledger_14_60 : ∀ i ∈ List.range 4, LedgerAt 14 (60+i) := by decide +kernel

theorem ledger_14_64 : ∀ i ∈ List.range 4, LedgerAt 14 (64+i) := by decide +kernel

theorem ledger_14_68 : ∀ i ∈ List.range 4, LedgerAt 14 (68+i) := by decide +kernel

theorem ledger_14_72 : ∀ i ∈ List.range 4, LedgerAt 14 (72+i) := by decide +kernel

theorem ledger_14_76 : ∀ i ∈ List.range 4, LedgerAt 14 (76+i) := by decide +kernel

theorem ledger_14_80 : ∀ i ∈ List.range 4, LedgerAt 14 (80+i) := by decide +kernel

theorem ledger_14_84 : ∀ i ∈ List.range 4, LedgerAt 14 (84+i) := by decide +kernel

theorem ledger_14_88 : ∀ i ∈ List.range 4, LedgerAt 14 (88+i) := by decide +kernel

theorem ledger_14_92 : ∀ i ∈ List.range 4, LedgerAt 14 (92+i) := by decide +kernel

theorem ledger_14_96 : ∀ i ∈ List.range 4, LedgerAt 14 (96+i) := by decide +kernel

theorem ledger_14_100 : ∀ i ∈ List.range 4, LedgerAt 14 (100+i) := by decide +kernel

theorem ledger_14_104 : ∀ i ∈ List.range 4, LedgerAt 14 (104+i) := by decide +kernel

theorem ledger_14_108 : ∀ i ∈ List.range 4, LedgerAt 14 (108+i) := by decide +kernel

theorem ledger_14_112 : ∀ i ∈ List.range 4, LedgerAt 14 (112+i) := by decide +kernel

theorem ledger_14_116 : ∀ i ∈ List.range 4, LedgerAt 14 (116+i) := by decide +kernel

theorem ledger_14_120 : ∀ i ∈ List.range 4, LedgerAt 14 (120+i) := by decide +kernel

theorem ledger_14_124 : ∀ i ∈ List.range 4, LedgerAt 14 (124+i) := by decide +kernel

theorem ledger_14_128 : ∀ i ∈ List.range 4, LedgerAt 14 (128+i) := by decide +kernel

theorem ledger_14_132 : ∀ i ∈ List.range 4, LedgerAt 14 (132+i) := by decide +kernel

theorem ledger_14_136 : ∀ i ∈ List.range 4, LedgerAt 14 (136+i) := by decide +kernel

theorem ledger_14_140 : ∀ i ∈ List.range 3, LedgerAt 14 (140+i) := by decide +kernel

theorem ledger_14 (v : ℕ) (hv : v ∈ List.range 143) : LedgerAt 14 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 14 v)
  have h := (join 0 72 71 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_14_0 ledger_14_4) (join 8 4 4 ledger_14_8 ledger_14_12)) (join 16 8 12 (join 16 4 4 ledger_14_16 ledger_14_20) (join 24 4 8 ledger_14_24 (join 28 4 4 ledger_14_28 ledger_14_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_14_36 ledger_14_40) (join 44 4 4 ledger_14_44 ledger_14_48)) (join 52 8 12 (join 52 4 4 ledger_14_52 ledger_14_56) (join 60 4 8 ledger_14_60 (join 64 4 4 ledger_14_64 ledger_14_68))))) (join 72 36 35 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_14_72 ledger_14_76) (join 80 4 4 ledger_14_80 ledger_14_84)) (join 88 8 12 (join 88 4 4 ledger_14_88 ledger_14_92) (join 96 4 8 ledger_14_96 (join 100 4 4 ledger_14_100 ledger_14_104)))) (join 108 16 19 (join 108 8 8 (join 108 4 4 ledger_14_108 ledger_14_112) (join 116 4 4 ledger_14_116 ledger_14_120)) (join 124 8 11 (join 124 4 4 ledger_14_124 ledger_14_128) (join 132 4 7 ledger_14_132 (join 136 4 3 ledger_14_136 ledger_14_140))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
