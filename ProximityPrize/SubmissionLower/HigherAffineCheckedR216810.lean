import ProximityPrize.SubmissionLower.HigherAffineCheckedR206810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_21_0 : ∀ i ∈ List.range 4, SingleAt 21 (0+i) := by decide +kernel

theorem single_21_4 : ∀ i ∈ List.range 4, SingleAt 21 (4+i) := by decide +kernel

theorem single_21_8 : ∀ i ∈ List.range 4, SingleAt 21 (8+i) := by decide +kernel

theorem single_21_12 : ∀ i ∈ List.range 4, SingleAt 21 (12+i) := by decide +kernel

theorem single_21_16 : ∀ i ∈ List.range 4, SingleAt 21 (16+i) := by decide +kernel

theorem single_21_20 : ∀ i ∈ List.range 4, SingleAt 21 (20+i) := by decide +kernel

theorem single_21_24 : ∀ i ∈ List.range 4, SingleAt 21 (24+i) := by decide +kernel

theorem single_21_28 : ∀ i ∈ List.range 4, SingleAt 21 (28+i) := by decide +kernel

theorem single_21_32 : ∀ i ∈ List.range 4, SingleAt 21 (32+i) := by decide +kernel

theorem single_21_36 : ∀ i ∈ List.range 4, SingleAt 21 (36+i) := by decide +kernel

theorem single_21_40 : ∀ i ∈ List.range 4, SingleAt 21 (40+i) := by decide +kernel

theorem single_21_44 : ∀ i ∈ List.range 4, SingleAt 21 (44+i) := by decide +kernel

theorem single_21_48 : ∀ i ∈ List.range 4, SingleAt 21 (48+i) := by decide +kernel

theorem single_21_52 : ∀ i ∈ List.range 4, SingleAt 21 (52+i) := by decide +kernel

theorem single_21_56 : ∀ i ∈ List.range 4, SingleAt 21 (56+i) := by decide +kernel

theorem single_21_60 : ∀ i ∈ List.range 4, SingleAt 21 (60+i) := by decide +kernel

theorem single_21_64 : ∀ i ∈ List.range 4, SingleAt 21 (64+i) := by decide +kernel

theorem single_21_68 : ∀ i ∈ List.range 4, SingleAt 21 (68+i) := by decide +kernel

theorem single_21_72 : ∀ i ∈ List.range 4, SingleAt 21 (72+i) := by decide +kernel

theorem single_21_76 : ∀ i ∈ List.range 4, SingleAt 21 (76+i) := by decide +kernel

theorem single_21_80 : ∀ i ∈ List.range 4, SingleAt 21 (80+i) := by decide +kernel

theorem single_21_84 : ∀ i ∈ List.range 4, SingleAt 21 (84+i) := by decide +kernel

theorem single_21_88 : ∀ i ∈ List.range 4, SingleAt 21 (88+i) := by decide +kernel

theorem single_21_92 : ∀ i ∈ List.range 4, SingleAt 21 (92+i) := by decide +kernel

theorem single_21_96 : ∀ i ∈ List.range 4, SingleAt 21 (96+i) := by decide +kernel

theorem single_21_100 : ∀ i ∈ List.range 4, SingleAt 21 (100+i) := by decide +kernel

theorem single_21_104 : ∀ i ∈ List.range 4, SingleAt 21 (104+i) := by decide +kernel

theorem single_21_108 : ∀ i ∈ List.range 4, SingleAt 21 (108+i) := by decide +kernel

theorem single_21_112 : ∀ i ∈ List.range 4, SingleAt 21 (112+i) := by decide +kernel

theorem single_21_116 : ∀ i ∈ List.range 4, SingleAt 21 (116+i) := by decide +kernel

theorem single_21_120 : ∀ i ∈ List.range 4, SingleAt 21 (120+i) := by decide +kernel

theorem single_21_124 : ∀ i ∈ List.range 4, SingleAt 21 (124+i) := by decide +kernel

theorem single_21_128 : ∀ i ∈ List.range 4, SingleAt 21 (128+i) := by decide +kernel

theorem single_21_132 : ∀ i ∈ List.range 4, SingleAt 21 (132+i) := by decide +kernel

theorem single_21 (v : ℕ) (hv : v ∈ List.range 136) : SingleAt 21 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 21 v)
  have h := (join 0 68 68 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_21_0 single_21_4) (join 8 4 4 single_21_8 single_21_12)) (join 16 8 8 (join 16 4 4 single_21_16 single_21_20) (join 24 4 4 single_21_24 single_21_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 single_21_32 single_21_36) (join 40 4 4 single_21_40 single_21_44)) (join 48 8 12 (join 48 4 4 single_21_48 single_21_52) (join 56 4 8 single_21_56 (join 60 4 4 single_21_60 single_21_64))))) (join 68 32 36 (join 68 16 16 (join 68 8 8 (join 68 4 4 single_21_68 single_21_72) (join 76 4 4 single_21_76 single_21_80)) (join 84 8 8 (join 84 4 4 single_21_84 single_21_88) (join 92 4 4 single_21_92 single_21_96))) (join 100 16 20 (join 100 8 8 (join 100 4 4 single_21_100 single_21_104) (join 108 4 4 single_21_108 single_21_112)) (join 116 8 12 (join 116 4 4 single_21_116 single_21_120) (join 124 4 8 single_21_124 (join 128 4 4 single_21_128 single_21_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_21_0 : ∀ i ∈ List.range 4, PhaseAt 21 (0+i) := by decide +kernel

theorem phase_21_4 : ∀ i ∈ List.range 4, PhaseAt 21 (4+i) := by decide +kernel

theorem phase_21_8 : ∀ i ∈ List.range 4, PhaseAt 21 (8+i) := by decide +kernel

theorem phase_21_12 : ∀ i ∈ List.range 4, PhaseAt 21 (12+i) := by decide +kernel

theorem phase_21_16 : ∀ i ∈ List.range 4, PhaseAt 21 (16+i) := by decide +kernel

theorem phase_21_20 : ∀ i ∈ List.range 4, PhaseAt 21 (20+i) := by decide +kernel

theorem phase_21_24 : ∀ i ∈ List.range 4, PhaseAt 21 (24+i) := by decide +kernel

theorem phase_21_28 : ∀ i ∈ List.range 4, PhaseAt 21 (28+i) := by decide +kernel

theorem phase_21_32 : ∀ i ∈ List.range 4, PhaseAt 21 (32+i) := by decide +kernel

theorem phase_21_36 : ∀ i ∈ List.range 4, PhaseAt 21 (36+i) := by decide +kernel

theorem phase_21_40 : ∀ i ∈ List.range 4, PhaseAt 21 (40+i) := by decide +kernel

theorem phase_21_44 : ∀ i ∈ List.range 4, PhaseAt 21 (44+i) := by decide +kernel

theorem phase_21_48 : ∀ i ∈ List.range 4, PhaseAt 21 (48+i) := by decide +kernel

theorem phase_21_52 : ∀ i ∈ List.range 4, PhaseAt 21 (52+i) := by decide +kernel

theorem phase_21_56 : ∀ i ∈ List.range 4, PhaseAt 21 (56+i) := by decide +kernel

theorem phase_21_60 : ∀ i ∈ List.range 4, PhaseAt 21 (60+i) := by decide +kernel

theorem phase_21_64 : ∀ i ∈ List.range 4, PhaseAt 21 (64+i) := by decide +kernel

theorem phase_21_68 : ∀ i ∈ List.range 4, PhaseAt 21 (68+i) := by decide +kernel

theorem phase_21_72 : ∀ i ∈ List.range 4, PhaseAt 21 (72+i) := by decide +kernel

theorem phase_21_76 : ∀ i ∈ List.range 4, PhaseAt 21 (76+i) := by decide +kernel

theorem phase_21_80 : ∀ i ∈ List.range 4, PhaseAt 21 (80+i) := by decide +kernel

theorem phase_21_84 : ∀ i ∈ List.range 4, PhaseAt 21 (84+i) := by decide +kernel

theorem phase_21_88 : ∀ i ∈ List.range 4, PhaseAt 21 (88+i) := by decide +kernel

theorem phase_21_92 : ∀ i ∈ List.range 4, PhaseAt 21 (92+i) := by decide +kernel

theorem phase_21_96 : ∀ i ∈ List.range 4, PhaseAt 21 (96+i) := by decide +kernel

theorem phase_21_100 : ∀ i ∈ List.range 4, PhaseAt 21 (100+i) := by decide +kernel

theorem phase_21_104 : ∀ i ∈ List.range 4, PhaseAt 21 (104+i) := by decide +kernel

theorem phase_21_108 : ∀ i ∈ List.range 4, PhaseAt 21 (108+i) := by decide +kernel

theorem phase_21_112 : ∀ i ∈ List.range 4, PhaseAt 21 (112+i) := by decide +kernel

theorem phase_21_116 : ∀ i ∈ List.range 4, PhaseAt 21 (116+i) := by decide +kernel

theorem phase_21_120 : ∀ i ∈ List.range 4, PhaseAt 21 (120+i) := by decide +kernel

theorem phase_21_124 : ∀ i ∈ List.range 4, PhaseAt 21 (124+i) := by decide +kernel

theorem phase_21_128 : ∀ i ∈ List.range 4, PhaseAt 21 (128+i) := by decide +kernel

theorem phase_21_132 : ∀ i ∈ List.range 4, PhaseAt 21 (132+i) := by decide +kernel

theorem phase_21 (v : ℕ) (hv : v ∈ List.range 136) : PhaseAt 21 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 21 v)
  have h := (join 0 68 68 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_21_0 phase_21_4) (join 8 4 4 phase_21_8 phase_21_12)) (join 16 8 8 (join 16 4 4 phase_21_16 phase_21_20) (join 24 4 4 phase_21_24 phase_21_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_21_32 phase_21_36) (join 40 4 4 phase_21_40 phase_21_44)) (join 48 8 12 (join 48 4 4 phase_21_48 phase_21_52) (join 56 4 8 phase_21_56 (join 60 4 4 phase_21_60 phase_21_64))))) (join 68 32 36 (join 68 16 16 (join 68 8 8 (join 68 4 4 phase_21_68 phase_21_72) (join 76 4 4 phase_21_76 phase_21_80)) (join 84 8 8 (join 84 4 4 phase_21_84 phase_21_88) (join 92 4 4 phase_21_92 phase_21_96))) (join 100 16 20 (join 100 8 8 (join 100 4 4 phase_21_100 phase_21_104) (join 108 4 4 phase_21_108 phase_21_112)) (join 116 8 12 (join 116 4 4 phase_21_116 phase_21_120) (join 124 4 8 phase_21_124 (join 128 4 4 phase_21_128 phase_21_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_21_0 : ∀ i ∈ List.range 1, ThresholdAt 21 (0+i) := by decide +kernel

theorem threshold_21_1 : ∀ i ∈ List.range 1, ThresholdAt 21 (1+i) := by decide +kernel

theorem threshold_21_2 : ∀ i ∈ List.range 1, ThresholdAt 21 (2+i) := by decide +kernel

theorem threshold_21_3 : ∀ i ∈ List.range 1, ThresholdAt 21 (3+i) := by decide +kernel

theorem threshold_21_4 : ∀ i ∈ List.range 1, ThresholdAt 21 (4+i) := by decide +kernel

theorem threshold_21_5 : ∀ i ∈ List.range 1, ThresholdAt 21 (5+i) := by decide +kernel

theorem threshold_21_6 : ∀ i ∈ List.range 1, ThresholdAt 21 (6+i) := by decide +kernel

theorem threshold_21_7 : ∀ i ∈ List.range 1, ThresholdAt 21 (7+i) := by decide +kernel

theorem threshold_21_8 : ∀ i ∈ List.range 1, ThresholdAt 21 (8+i) := by decide +kernel

theorem threshold_21_9 : ∀ i ∈ List.range 1, ThresholdAt 21 (9+i) := by decide +kernel

theorem threshold_21_10 : ∀ i ∈ List.range 1, ThresholdAt 21 (10+i) := by decide +kernel

theorem threshold_21_11 : ∀ i ∈ List.range 1, ThresholdAt 21 (11+i) := by decide +kernel

theorem threshold_21_12 : ∀ i ∈ List.range 1, ThresholdAt 21 (12+i) := by decide +kernel

theorem threshold_21_13 : ∀ i ∈ List.range 1, ThresholdAt 21 (13+i) := by decide +kernel

theorem threshold_21_14 : ∀ i ∈ List.range 1, ThresholdAt 21 (14+i) := by decide +kernel

theorem threshold_21_15 : ∀ i ∈ List.range 1, ThresholdAt 21 (15+i) := by decide +kernel

theorem threshold_21_16 : ∀ i ∈ List.range 1, ThresholdAt 21 (16+i) := by decide +kernel

theorem threshold_21_17 : ∀ i ∈ List.range 1, ThresholdAt 21 (17+i) := by decide +kernel

theorem threshold_21_18 : ∀ i ∈ List.range 1, ThresholdAt 21 (18+i) := by decide +kernel

theorem threshold_21_19 : ∀ i ∈ List.range 1, ThresholdAt 21 (19+i) := by decide +kernel

theorem threshold_21_20 : ∀ i ∈ List.range 1, ThresholdAt 21 (20+i) := by decide +kernel

theorem threshold_21_21 : ∀ i ∈ List.range 1, ThresholdAt 21 (21+i) := by decide +kernel

theorem threshold_21_22 : ∀ i ∈ List.range 1, ThresholdAt 21 (22+i) := by decide +kernel

theorem threshold_21_23 : ∀ i ∈ List.range 1, ThresholdAt 21 (23+i) := by decide +kernel

theorem threshold_21_24 : ∀ i ∈ List.range 1, ThresholdAt 21 (24+i) := by decide +kernel

theorem threshold_21_25 : ∀ i ∈ List.range 1, ThresholdAt 21 (25+i) := by decide +kernel

theorem threshold_21_26 : ∀ i ∈ List.range 1, ThresholdAt 21 (26+i) := by decide +kernel

theorem threshold_21_27 : ∀ i ∈ List.range 1, ThresholdAt 21 (27+i) := by decide +kernel

theorem threshold_21_28 : ∀ i ∈ List.range 1, ThresholdAt 21 (28+i) := by decide +kernel

theorem threshold_21_29 : ∀ i ∈ List.range 1, ThresholdAt 21 (29+i) := by decide +kernel

theorem threshold_21_30 : ∀ i ∈ List.range 1, ThresholdAt 21 (30+i) := by decide +kernel

theorem threshold_21_31 : ∀ i ∈ List.range 1, ThresholdAt 21 (31+i) := by decide +kernel

theorem threshold_21_32 : ∀ i ∈ List.range 1, ThresholdAt 21 (32+i) := by decide +kernel

theorem threshold_21_33 : ∀ i ∈ List.range 1, ThresholdAt 21 (33+i) := by decide +kernel

theorem threshold_21_34 : ∀ i ∈ List.range 1, ThresholdAt 21 (34+i) := by decide +kernel

theorem threshold_21_35 : ∀ i ∈ List.range 1, ThresholdAt 21 (35+i) := by decide +kernel

theorem threshold_21_36 : ∀ i ∈ List.range 1, ThresholdAt 21 (36+i) := by decide +kernel

theorem threshold_21_37 : ∀ i ∈ List.range 1, ThresholdAt 21 (37+i) := by decide +kernel

theorem threshold_21_38 : ∀ i ∈ List.range 1, ThresholdAt 21 (38+i) := by decide +kernel

theorem threshold_21_39 : ∀ i ∈ List.range 1, ThresholdAt 21 (39+i) := by decide +kernel

theorem threshold_21_40 : ∀ i ∈ List.range 1, ThresholdAt 21 (40+i) := by decide +kernel

theorem threshold_21_41 : ∀ i ∈ List.range 1, ThresholdAt 21 (41+i) := by decide +kernel

theorem threshold_21_42 : ∀ i ∈ List.range 1, ThresholdAt 21 (42+i) := by decide +kernel

theorem threshold_21_43 : ∀ i ∈ List.range 1, ThresholdAt 21 (43+i) := by decide +kernel

theorem threshold_21_44 : ∀ i ∈ List.range 1, ThresholdAt 21 (44+i) := by decide +kernel

theorem threshold_21_45 : ∀ i ∈ List.range 1, ThresholdAt 21 (45+i) := by decide +kernel

theorem threshold_21_46 : ∀ i ∈ List.range 1, ThresholdAt 21 (46+i) := by decide +kernel

theorem threshold_21_47 : ∀ i ∈ List.range 1, ThresholdAt 21 (47+i) := by decide +kernel

theorem threshold_21_48 : ∀ i ∈ List.range 1, ThresholdAt 21 (48+i) := by decide +kernel

theorem threshold_21_49 : ∀ i ∈ List.range 1, ThresholdAt 21 (49+i) := by decide +kernel

theorem threshold_21_50 : ∀ i ∈ List.range 1, ThresholdAt 21 (50+i) := by decide +kernel

theorem threshold_21_51 : ∀ i ∈ List.range 1, ThresholdAt 21 (51+i) := by decide +kernel

theorem threshold_21_52 : ∀ i ∈ List.range 1, ThresholdAt 21 (52+i) := by decide +kernel

theorem threshold_21_53 : ∀ i ∈ List.range 1, ThresholdAt 21 (53+i) := by decide +kernel

theorem threshold_21_54 : ∀ i ∈ List.range 1, ThresholdAt 21 (54+i) := by decide +kernel

theorem threshold_21_55 : ∀ i ∈ List.range 1, ThresholdAt 21 (55+i) := by decide +kernel

theorem threshold_21_56 : ∀ i ∈ List.range 1, ThresholdAt 21 (56+i) := by decide +kernel

theorem threshold_21_57 : ∀ i ∈ List.range 1, ThresholdAt 21 (57+i) := by decide +kernel

theorem threshold_21_58 : ∀ i ∈ List.range 1, ThresholdAt 21 (58+i) := by decide +kernel

theorem threshold_21_59 : ∀ i ∈ List.range 1, ThresholdAt 21 (59+i) := by decide +kernel

theorem threshold_21_60 : ∀ i ∈ List.range 1, ThresholdAt 21 (60+i) := by decide +kernel

theorem threshold_21_61 : ∀ i ∈ List.range 1, ThresholdAt 21 (61+i) := by decide +kernel

theorem threshold_21_62 : ∀ i ∈ List.range 1, ThresholdAt 21 (62+i) := by decide +kernel

theorem threshold_21_63 : ∀ i ∈ List.range 1, ThresholdAt 21 (63+i) := by decide +kernel

theorem threshold_21_64 : ∀ i ∈ List.range 1, ThresholdAt 21 (64+i) := by decide +kernel

theorem threshold_21_65 : ∀ i ∈ List.range 1, ThresholdAt 21 (65+i) := by decide +kernel

theorem threshold_21_66 : ∀ i ∈ List.range 1, ThresholdAt 21 (66+i) := by decide +kernel

theorem threshold_21_67 : ∀ i ∈ List.range 1, ThresholdAt 21 (67+i) := by decide +kernel

theorem threshold_21_68 : ∀ i ∈ List.range 1, ThresholdAt 21 (68+i) := by decide +kernel

theorem threshold_21_69 : ∀ i ∈ List.range 1, ThresholdAt 21 (69+i) := by decide +kernel

theorem threshold_21_70 : ∀ i ∈ List.range 1, ThresholdAt 21 (70+i) := by decide +kernel

theorem threshold_21_71 : ∀ i ∈ List.range 1, ThresholdAt 21 (71+i) := by decide +kernel

theorem threshold_21_72 : ∀ i ∈ List.range 1, ThresholdAt 21 (72+i) := by decide +kernel

theorem threshold_21_73 : ∀ i ∈ List.range 1, ThresholdAt 21 (73+i) := by decide +kernel

theorem threshold_21_74 : ∀ i ∈ List.range 1, ThresholdAt 21 (74+i) := by decide +kernel

theorem threshold_21_75 : ∀ i ∈ List.range 1, ThresholdAt 21 (75+i) := by decide +kernel

theorem threshold_21_76 : ∀ i ∈ List.range 1, ThresholdAt 21 (76+i) := by decide +kernel

theorem threshold_21_77 : ∀ i ∈ List.range 1, ThresholdAt 21 (77+i) := by decide +kernel

theorem threshold_21_78 : ∀ i ∈ List.range 1, ThresholdAt 21 (78+i) := by decide +kernel

theorem threshold_21_79 : ∀ i ∈ List.range 1, ThresholdAt 21 (79+i) := by decide +kernel

theorem threshold_21_80 : ∀ i ∈ List.range 1, ThresholdAt 21 (80+i) := by decide +kernel

theorem threshold_21_81 : ∀ i ∈ List.range 1, ThresholdAt 21 (81+i) := by decide +kernel

theorem threshold_21_82 : ∀ i ∈ List.range 1, ThresholdAt 21 (82+i) := by decide +kernel

theorem threshold_21_83 : ∀ i ∈ List.range 1, ThresholdAt 21 (83+i) := by decide +kernel

theorem threshold_21_84 : ∀ i ∈ List.range 1, ThresholdAt 21 (84+i) := by decide +kernel

theorem threshold_21_85 : ∀ i ∈ List.range 1, ThresholdAt 21 (85+i) := by decide +kernel

theorem threshold_21_86 : ∀ i ∈ List.range 1, ThresholdAt 21 (86+i) := by decide +kernel

theorem threshold_21_87 : ∀ i ∈ List.range 1, ThresholdAt 21 (87+i) := by decide +kernel

theorem threshold_21_88 : ∀ i ∈ List.range 1, ThresholdAt 21 (88+i) := by decide +kernel

theorem threshold_21_89 : ∀ i ∈ List.range 1, ThresholdAt 21 (89+i) := by decide +kernel

theorem threshold_21_90 : ∀ i ∈ List.range 1, ThresholdAt 21 (90+i) := by decide +kernel

theorem threshold_21_91 : ∀ i ∈ List.range 1, ThresholdAt 21 (91+i) := by decide +kernel

theorem threshold_21_92 : ∀ i ∈ List.range 1, ThresholdAt 21 (92+i) := by decide +kernel

theorem threshold_21_93 : ∀ i ∈ List.range 1, ThresholdAt 21 (93+i) := by decide +kernel

theorem threshold_21_94 : ∀ i ∈ List.range 1, ThresholdAt 21 (94+i) := by decide +kernel

theorem threshold_21_95 : ∀ i ∈ List.range 1, ThresholdAt 21 (95+i) := by decide +kernel

theorem threshold_21_96 : ∀ i ∈ List.range 1, ThresholdAt 21 (96+i) := by decide +kernel

theorem threshold_21_97 : ∀ i ∈ List.range 1, ThresholdAt 21 (97+i) := by decide +kernel

theorem threshold_21_98 : ∀ i ∈ List.range 1, ThresholdAt 21 (98+i) := by decide +kernel

theorem threshold_21_99 : ∀ i ∈ List.range 1, ThresholdAt 21 (99+i) := by decide +kernel

theorem threshold_21_100 : ∀ i ∈ List.range 1, ThresholdAt 21 (100+i) := by decide +kernel

theorem threshold_21_101 : ∀ i ∈ List.range 1, ThresholdAt 21 (101+i) := by decide +kernel

theorem threshold_21_102 : ∀ i ∈ List.range 1, ThresholdAt 21 (102+i) := by decide +kernel

theorem threshold_21_103 : ∀ i ∈ List.range 1, ThresholdAt 21 (103+i) := by decide +kernel

theorem threshold_21_104 : ∀ i ∈ List.range 1, ThresholdAt 21 (104+i) := by decide +kernel

theorem threshold_21_105 : ∀ i ∈ List.range 1, ThresholdAt 21 (105+i) := by decide +kernel

theorem threshold_21_106 : ∀ i ∈ List.range 1, ThresholdAt 21 (106+i) := by decide +kernel

theorem threshold_21_107 : ∀ i ∈ List.range 1, ThresholdAt 21 (107+i) := by decide +kernel

theorem threshold_21_108 : ∀ i ∈ List.range 1, ThresholdAt 21 (108+i) := by decide +kernel

theorem threshold_21_109 : ∀ i ∈ List.range 1, ThresholdAt 21 (109+i) := by decide +kernel

theorem threshold_21_110 : ∀ i ∈ List.range 1, ThresholdAt 21 (110+i) := by decide +kernel

theorem threshold_21_111 : ∀ i ∈ List.range 1, ThresholdAt 21 (111+i) := by decide +kernel

theorem threshold_21_112 : ∀ i ∈ List.range 1, ThresholdAt 21 (112+i) := by decide +kernel

theorem threshold_21_113 : ∀ i ∈ List.range 1, ThresholdAt 21 (113+i) := by decide +kernel

theorem threshold_21_114 : ∀ i ∈ List.range 1, ThresholdAt 21 (114+i) := by decide +kernel

theorem threshold_21_115 : ∀ i ∈ List.range 1, ThresholdAt 21 (115+i) := by decide +kernel

theorem threshold_21_116 : ∀ i ∈ List.range 1, ThresholdAt 21 (116+i) := by decide +kernel

theorem threshold_21_117 : ∀ i ∈ List.range 1, ThresholdAt 21 (117+i) := by decide +kernel

theorem threshold_21_118 : ∀ i ∈ List.range 1, ThresholdAt 21 (118+i) := by decide +kernel

theorem threshold_21_119 : ∀ i ∈ List.range 1, ThresholdAt 21 (119+i) := by decide +kernel

theorem threshold_21_120 : ∀ i ∈ List.range 1, ThresholdAt 21 (120+i) := by decide +kernel

theorem threshold_21_121 : ∀ i ∈ List.range 1, ThresholdAt 21 (121+i) := by decide +kernel

theorem threshold_21_122 : ∀ i ∈ List.range 1, ThresholdAt 21 (122+i) := by decide +kernel

theorem threshold_21_123 : ∀ i ∈ List.range 1, ThresholdAt 21 (123+i) := by decide +kernel

theorem threshold_21_124 : ∀ i ∈ List.range 1, ThresholdAt 21 (124+i) := by decide +kernel

theorem threshold_21_125 : ∀ i ∈ List.range 1, ThresholdAt 21 (125+i) := by decide +kernel

theorem threshold_21_126 : ∀ i ∈ List.range 1, ThresholdAt 21 (126+i) := by decide +kernel

theorem threshold_21_127 : ∀ i ∈ List.range 1, ThresholdAt 21 (127+i) := by decide +kernel

theorem threshold_21_128 : ∀ i ∈ List.range 1, ThresholdAt 21 (128+i) := by decide +kernel

theorem threshold_21_129 : ∀ i ∈ List.range 1, ThresholdAt 21 (129+i) := by decide +kernel

theorem threshold_21_130 : ∀ i ∈ List.range 1, ThresholdAt 21 (130+i) := by decide +kernel

theorem threshold_21_131 : ∀ i ∈ List.range 1, ThresholdAt 21 (131+i) := by decide +kernel

theorem threshold_21_132 : ∀ i ∈ List.range 1, ThresholdAt 21 (132+i) := by decide +kernel

theorem threshold_21_133 : ∀ i ∈ List.range 1, ThresholdAt 21 (133+i) := by decide +kernel

theorem threshold_21_134 : ∀ i ∈ List.range 1, ThresholdAt 21 (134+i) := by decide +kernel

theorem threshold_21_135 : ∀ i ∈ List.range 1, ThresholdAt 21 (135+i) := by decide +kernel

theorem threshold_21 (v : ℕ) (hv : v ∈ List.range 136) : ThresholdAt 21 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 21 v)
  have h := (join 0 68 68 (join 0 34 34 (join 0 17 17 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_21_0 threshold_21_1) (join 2 1 1 threshold_21_2 threshold_21_3)) (join 4 2 2 (join 4 1 1 threshold_21_4 threshold_21_5) (join 6 1 1 threshold_21_6 threshold_21_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_21_8 threshold_21_9) (join 10 1 1 threshold_21_10 threshold_21_11)) (join 12 2 3 (join 12 1 1 threshold_21_12 threshold_21_13) (join 14 1 2 threshold_21_14 (join 15 1 1 threshold_21_15 threshold_21_16))))) (join 17 8 9 (join 17 4 4 (join 17 2 2 (join 17 1 1 threshold_21_17 threshold_21_18) (join 19 1 1 threshold_21_19 threshold_21_20)) (join 21 2 2 (join 21 1 1 threshold_21_21 threshold_21_22) (join 23 1 1 threshold_21_23 threshold_21_24))) (join 25 4 5 (join 25 2 2 (join 25 1 1 threshold_21_25 threshold_21_26) (join 27 1 1 threshold_21_27 threshold_21_28)) (join 29 2 3 (join 29 1 1 threshold_21_29 threshold_21_30) (join 31 1 2 threshold_21_31 (join 32 1 1 threshold_21_32 threshold_21_33)))))) (join 34 17 17 (join 34 8 9 (join 34 4 4 (join 34 2 2 (join 34 1 1 threshold_21_34 threshold_21_35) (join 36 1 1 threshold_21_36 threshold_21_37)) (join 38 2 2 (join 38 1 1 threshold_21_38 threshold_21_39) (join 40 1 1 threshold_21_40 threshold_21_41))) (join 42 4 5 (join 42 2 2 (join 42 1 1 threshold_21_42 threshold_21_43) (join 44 1 1 threshold_21_44 threshold_21_45)) (join 46 2 3 (join 46 1 1 threshold_21_46 threshold_21_47) (join 48 1 2 threshold_21_48 (join 49 1 1 threshold_21_49 threshold_21_50))))) (join 51 8 9 (join 51 4 4 (join 51 2 2 (join 51 1 1 threshold_21_51 threshold_21_52) (join 53 1 1 threshold_21_53 threshold_21_54)) (join 55 2 2 (join 55 1 1 threshold_21_55 threshold_21_56) (join 57 1 1 threshold_21_57 threshold_21_58))) (join 59 4 5 (join 59 2 2 (join 59 1 1 threshold_21_59 threshold_21_60) (join 61 1 1 threshold_21_61 threshold_21_62)) (join 63 2 3 (join 63 1 1 threshold_21_63 threshold_21_64) (join 65 1 2 threshold_21_65 (join 66 1 1 threshold_21_66 threshold_21_67))))))) (join 68 34 34 (join 68 17 17 (join 68 8 9 (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_21_68 threshold_21_69) (join 70 1 1 threshold_21_70 threshold_21_71)) (join 72 2 2 (join 72 1 1 threshold_21_72 threshold_21_73) (join 74 1 1 threshold_21_74 threshold_21_75))) (join 76 4 5 (join 76 2 2 (join 76 1 1 threshold_21_76 threshold_21_77) (join 78 1 1 threshold_21_78 threshold_21_79)) (join 80 2 3 (join 80 1 1 threshold_21_80 threshold_21_81) (join 82 1 2 threshold_21_82 (join 83 1 1 threshold_21_83 threshold_21_84))))) (join 85 8 9 (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_21_85 threshold_21_86) (join 87 1 1 threshold_21_87 threshold_21_88)) (join 89 2 2 (join 89 1 1 threshold_21_89 threshold_21_90) (join 91 1 1 threshold_21_91 threshold_21_92))) (join 93 4 5 (join 93 2 2 (join 93 1 1 threshold_21_93 threshold_21_94) (join 95 1 1 threshold_21_95 threshold_21_96)) (join 97 2 3 (join 97 1 1 threshold_21_97 threshold_21_98) (join 99 1 2 threshold_21_99 (join 100 1 1 threshold_21_100 threshold_21_101)))))) (join 102 17 17 (join 102 8 9 (join 102 4 4 (join 102 2 2 (join 102 1 1 threshold_21_102 threshold_21_103) (join 104 1 1 threshold_21_104 threshold_21_105)) (join 106 2 2 (join 106 1 1 threshold_21_106 threshold_21_107) (join 108 1 1 threshold_21_108 threshold_21_109))) (join 110 4 5 (join 110 2 2 (join 110 1 1 threshold_21_110 threshold_21_111) (join 112 1 1 threshold_21_112 threshold_21_113)) (join 114 2 3 (join 114 1 1 threshold_21_114 threshold_21_115) (join 116 1 2 threshold_21_116 (join 117 1 1 threshold_21_117 threshold_21_118))))) (join 119 8 9 (join 119 4 4 (join 119 2 2 (join 119 1 1 threshold_21_119 threshold_21_120) (join 121 1 1 threshold_21_121 threshold_21_122)) (join 123 2 2 (join 123 1 1 threshold_21_123 threshold_21_124) (join 125 1 1 threshold_21_125 threshold_21_126))) (join 127 4 5 (join 127 2 2 (join 127 1 1 threshold_21_127 threshold_21_128) (join 129 1 1 threshold_21_129 threshold_21_130)) (join 131 2 3 (join 131 1 1 threshold_21_131 threshold_21_132) (join 133 1 2 threshold_21_133 (join 134 1 1 threshold_21_134 threshold_21_135))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_21_0 : ∀ i ∈ List.range 4, LedgerAt 21 (0+i) := by decide +kernel

theorem ledger_21_4 : ∀ i ∈ List.range 4, LedgerAt 21 (4+i) := by decide +kernel

theorem ledger_21_8 : ∀ i ∈ List.range 4, LedgerAt 21 (8+i) := by decide +kernel

theorem ledger_21_12 : ∀ i ∈ List.range 4, LedgerAt 21 (12+i) := by decide +kernel

theorem ledger_21_16 : ∀ i ∈ List.range 4, LedgerAt 21 (16+i) := by decide +kernel

theorem ledger_21_20 : ∀ i ∈ List.range 4, LedgerAt 21 (20+i) := by decide +kernel

theorem ledger_21_24 : ∀ i ∈ List.range 4, LedgerAt 21 (24+i) := by decide +kernel

theorem ledger_21_28 : ∀ i ∈ List.range 4, LedgerAt 21 (28+i) := by decide +kernel

theorem ledger_21_32 : ∀ i ∈ List.range 4, LedgerAt 21 (32+i) := by decide +kernel

theorem ledger_21_36 : ∀ i ∈ List.range 4, LedgerAt 21 (36+i) := by decide +kernel

theorem ledger_21_40 : ∀ i ∈ List.range 4, LedgerAt 21 (40+i) := by decide +kernel

theorem ledger_21_44 : ∀ i ∈ List.range 4, LedgerAt 21 (44+i) := by decide +kernel

theorem ledger_21_48 : ∀ i ∈ List.range 4, LedgerAt 21 (48+i) := by decide +kernel

theorem ledger_21_52 : ∀ i ∈ List.range 4, LedgerAt 21 (52+i) := by decide +kernel

theorem ledger_21_56 : ∀ i ∈ List.range 4, LedgerAt 21 (56+i) := by decide +kernel

theorem ledger_21_60 : ∀ i ∈ List.range 4, LedgerAt 21 (60+i) := by decide +kernel

theorem ledger_21_64 : ∀ i ∈ List.range 4, LedgerAt 21 (64+i) := by decide +kernel

theorem ledger_21_68 : ∀ i ∈ List.range 4, LedgerAt 21 (68+i) := by decide +kernel

theorem ledger_21_72 : ∀ i ∈ List.range 4, LedgerAt 21 (72+i) := by decide +kernel

theorem ledger_21_76 : ∀ i ∈ List.range 4, LedgerAt 21 (76+i) := by decide +kernel

theorem ledger_21_80 : ∀ i ∈ List.range 4, LedgerAt 21 (80+i) := by decide +kernel

theorem ledger_21_84 : ∀ i ∈ List.range 4, LedgerAt 21 (84+i) := by decide +kernel

theorem ledger_21_88 : ∀ i ∈ List.range 4, LedgerAt 21 (88+i) := by decide +kernel

theorem ledger_21_92 : ∀ i ∈ List.range 4, LedgerAt 21 (92+i) := by decide +kernel

theorem ledger_21_96 : ∀ i ∈ List.range 4, LedgerAt 21 (96+i) := by decide +kernel

theorem ledger_21_100 : ∀ i ∈ List.range 4, LedgerAt 21 (100+i) := by decide +kernel

theorem ledger_21_104 : ∀ i ∈ List.range 4, LedgerAt 21 (104+i) := by decide +kernel

theorem ledger_21_108 : ∀ i ∈ List.range 4, LedgerAt 21 (108+i) := by decide +kernel

theorem ledger_21_112 : ∀ i ∈ List.range 4, LedgerAt 21 (112+i) := by decide +kernel

theorem ledger_21_116 : ∀ i ∈ List.range 4, LedgerAt 21 (116+i) := by decide +kernel

theorem ledger_21_120 : ∀ i ∈ List.range 4, LedgerAt 21 (120+i) := by decide +kernel

theorem ledger_21_124 : ∀ i ∈ List.range 4, LedgerAt 21 (124+i) := by decide +kernel

theorem ledger_21_128 : ∀ i ∈ List.range 4, LedgerAt 21 (128+i) := by decide +kernel

theorem ledger_21_132 : ∀ i ∈ List.range 4, LedgerAt 21 (132+i) := by decide +kernel

theorem ledger_21 (v : ℕ) (hv : v ∈ List.range 136) : LedgerAt 21 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 21 v)
  have h := (join 0 68 68 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_21_0 ledger_21_4) (join 8 4 4 ledger_21_8 ledger_21_12)) (join 16 8 8 (join 16 4 4 ledger_21_16 ledger_21_20) (join 24 4 4 ledger_21_24 ledger_21_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_21_32 ledger_21_36) (join 40 4 4 ledger_21_40 ledger_21_44)) (join 48 8 12 (join 48 4 4 ledger_21_48 ledger_21_52) (join 56 4 8 ledger_21_56 (join 60 4 4 ledger_21_60 ledger_21_64))))) (join 68 32 36 (join 68 16 16 (join 68 8 8 (join 68 4 4 ledger_21_68 ledger_21_72) (join 76 4 4 ledger_21_76 ledger_21_80)) (join 84 8 8 (join 84 4 4 ledger_21_84 ledger_21_88) (join 92 4 4 ledger_21_92 ledger_21_96))) (join 100 16 20 (join 100 8 8 (join 100 4 4 ledger_21_100 ledger_21_104) (join 108 4 4 ledger_21_108 ledger_21_112)) (join 116 8 12 (join 116 4 4 ledger_21_116 ledger_21_120) (join 124 4 8 ledger_21_124 (join 128 4 4 ledger_21_128 ledger_21_132))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
