import ProximityPrize.SubmissionLower.HigherAffineCheckedR216810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_22_0 : ∀ i ∈ List.range 4, SingleAt 22 (0+i) := by decide +kernel

theorem single_22_4 : ∀ i ∈ List.range 4, SingleAt 22 (4+i) := by decide +kernel

theorem single_22_8 : ∀ i ∈ List.range 4, SingleAt 22 (8+i) := by decide +kernel

theorem single_22_12 : ∀ i ∈ List.range 4, SingleAt 22 (12+i) := by decide +kernel

theorem single_22_16 : ∀ i ∈ List.range 4, SingleAt 22 (16+i) := by decide +kernel

theorem single_22_20 : ∀ i ∈ List.range 4, SingleAt 22 (20+i) := by decide +kernel

theorem single_22_24 : ∀ i ∈ List.range 4, SingleAt 22 (24+i) := by decide +kernel

theorem single_22_28 : ∀ i ∈ List.range 4, SingleAt 22 (28+i) := by decide +kernel

theorem single_22_32 : ∀ i ∈ List.range 4, SingleAt 22 (32+i) := by decide +kernel

theorem single_22_36 : ∀ i ∈ List.range 4, SingleAt 22 (36+i) := by decide +kernel

theorem single_22_40 : ∀ i ∈ List.range 4, SingleAt 22 (40+i) := by decide +kernel

theorem single_22_44 : ∀ i ∈ List.range 4, SingleAt 22 (44+i) := by decide +kernel

theorem single_22_48 : ∀ i ∈ List.range 4, SingleAt 22 (48+i) := by decide +kernel

theorem single_22_52 : ∀ i ∈ List.range 4, SingleAt 22 (52+i) := by decide +kernel

theorem single_22_56 : ∀ i ∈ List.range 4, SingleAt 22 (56+i) := by decide +kernel

theorem single_22_60 : ∀ i ∈ List.range 4, SingleAt 22 (60+i) := by decide +kernel

theorem single_22_64 : ∀ i ∈ List.range 4, SingleAt 22 (64+i) := by decide +kernel

theorem single_22_68 : ∀ i ∈ List.range 4, SingleAt 22 (68+i) := by decide +kernel

theorem single_22_72 : ∀ i ∈ List.range 4, SingleAt 22 (72+i) := by decide +kernel

theorem single_22_76 : ∀ i ∈ List.range 4, SingleAt 22 (76+i) := by decide +kernel

theorem single_22_80 : ∀ i ∈ List.range 4, SingleAt 22 (80+i) := by decide +kernel

theorem single_22_84 : ∀ i ∈ List.range 4, SingleAt 22 (84+i) := by decide +kernel

theorem single_22_88 : ∀ i ∈ List.range 4, SingleAt 22 (88+i) := by decide +kernel

theorem single_22_92 : ∀ i ∈ List.range 4, SingleAt 22 (92+i) := by decide +kernel

theorem single_22_96 : ∀ i ∈ List.range 4, SingleAt 22 (96+i) := by decide +kernel

theorem single_22_100 : ∀ i ∈ List.range 4, SingleAt 22 (100+i) := by decide +kernel

theorem single_22_104 : ∀ i ∈ List.range 4, SingleAt 22 (104+i) := by decide +kernel

theorem single_22_108 : ∀ i ∈ List.range 4, SingleAt 22 (108+i) := by decide +kernel

theorem single_22_112 : ∀ i ∈ List.range 4, SingleAt 22 (112+i) := by decide +kernel

theorem single_22_116 : ∀ i ∈ List.range 4, SingleAt 22 (116+i) := by decide +kernel

theorem single_22_120 : ∀ i ∈ List.range 4, SingleAt 22 (120+i) := by decide +kernel

theorem single_22_124 : ∀ i ∈ List.range 4, SingleAt 22 (124+i) := by decide +kernel

theorem single_22_128 : ∀ i ∈ List.range 4, SingleAt 22 (128+i) := by decide +kernel

theorem single_22_132 : ∀ i ∈ List.range 3, SingleAt 22 (132+i) := by decide +kernel

theorem single_22 (v : ℕ) (hv : v ∈ List.range 135) : SingleAt 22 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 22 v)
  have h := (join 0 68 67 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_22_0 single_22_4) (join 8 4 4 single_22_8 single_22_12)) (join 16 8 8 (join 16 4 4 single_22_16 single_22_20) (join 24 4 4 single_22_24 single_22_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 single_22_32 single_22_36) (join 40 4 4 single_22_40 single_22_44)) (join 48 8 12 (join 48 4 4 single_22_48 single_22_52) (join 56 4 8 single_22_56 (join 60 4 4 single_22_60 single_22_64))))) (join 68 32 35 (join 68 16 16 (join 68 8 8 (join 68 4 4 single_22_68 single_22_72) (join 76 4 4 single_22_76 single_22_80)) (join 84 8 8 (join 84 4 4 single_22_84 single_22_88) (join 92 4 4 single_22_92 single_22_96))) (join 100 16 19 (join 100 8 8 (join 100 4 4 single_22_100 single_22_104) (join 108 4 4 single_22_108 single_22_112)) (join 116 8 11 (join 116 4 4 single_22_116 single_22_120) (join 124 4 7 single_22_124 (join 128 4 3 single_22_128 single_22_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_22_0 : ∀ i ∈ List.range 4, PhaseAt 22 (0+i) := by decide +kernel

theorem phase_22_4 : ∀ i ∈ List.range 4, PhaseAt 22 (4+i) := by decide +kernel

theorem phase_22_8 : ∀ i ∈ List.range 4, PhaseAt 22 (8+i) := by decide +kernel

theorem phase_22_12 : ∀ i ∈ List.range 4, PhaseAt 22 (12+i) := by decide +kernel

theorem phase_22_16 : ∀ i ∈ List.range 4, PhaseAt 22 (16+i) := by decide +kernel

theorem phase_22_20 : ∀ i ∈ List.range 4, PhaseAt 22 (20+i) := by decide +kernel

theorem phase_22_24 : ∀ i ∈ List.range 4, PhaseAt 22 (24+i) := by decide +kernel

theorem phase_22_28 : ∀ i ∈ List.range 4, PhaseAt 22 (28+i) := by decide +kernel

theorem phase_22_32 : ∀ i ∈ List.range 4, PhaseAt 22 (32+i) := by decide +kernel

theorem phase_22_36 : ∀ i ∈ List.range 4, PhaseAt 22 (36+i) := by decide +kernel

theorem phase_22_40 : ∀ i ∈ List.range 4, PhaseAt 22 (40+i) := by decide +kernel

theorem phase_22_44 : ∀ i ∈ List.range 4, PhaseAt 22 (44+i) := by decide +kernel

theorem phase_22_48 : ∀ i ∈ List.range 4, PhaseAt 22 (48+i) := by decide +kernel

theorem phase_22_52 : ∀ i ∈ List.range 4, PhaseAt 22 (52+i) := by decide +kernel

theorem phase_22_56 : ∀ i ∈ List.range 4, PhaseAt 22 (56+i) := by decide +kernel

theorem phase_22_60 : ∀ i ∈ List.range 4, PhaseAt 22 (60+i) := by decide +kernel

theorem phase_22_64 : ∀ i ∈ List.range 4, PhaseAt 22 (64+i) := by decide +kernel

theorem phase_22_68 : ∀ i ∈ List.range 4, PhaseAt 22 (68+i) := by decide +kernel

theorem phase_22_72 : ∀ i ∈ List.range 4, PhaseAt 22 (72+i) := by decide +kernel

theorem phase_22_76 : ∀ i ∈ List.range 4, PhaseAt 22 (76+i) := by decide +kernel

theorem phase_22_80 : ∀ i ∈ List.range 4, PhaseAt 22 (80+i) := by decide +kernel

theorem phase_22_84 : ∀ i ∈ List.range 4, PhaseAt 22 (84+i) := by decide +kernel

theorem phase_22_88 : ∀ i ∈ List.range 4, PhaseAt 22 (88+i) := by decide +kernel

theorem phase_22_92 : ∀ i ∈ List.range 4, PhaseAt 22 (92+i) := by decide +kernel

theorem phase_22_96 : ∀ i ∈ List.range 4, PhaseAt 22 (96+i) := by decide +kernel

theorem phase_22_100 : ∀ i ∈ List.range 4, PhaseAt 22 (100+i) := by decide +kernel

theorem phase_22_104 : ∀ i ∈ List.range 4, PhaseAt 22 (104+i) := by decide +kernel

theorem phase_22_108 : ∀ i ∈ List.range 4, PhaseAt 22 (108+i) := by decide +kernel

theorem phase_22_112 : ∀ i ∈ List.range 4, PhaseAt 22 (112+i) := by decide +kernel

theorem phase_22_116 : ∀ i ∈ List.range 4, PhaseAt 22 (116+i) := by decide +kernel

theorem phase_22_120 : ∀ i ∈ List.range 4, PhaseAt 22 (120+i) := by decide +kernel

theorem phase_22_124 : ∀ i ∈ List.range 4, PhaseAt 22 (124+i) := by decide +kernel

theorem phase_22_128 : ∀ i ∈ List.range 4, PhaseAt 22 (128+i) := by decide +kernel

theorem phase_22_132 : ∀ i ∈ List.range 3, PhaseAt 22 (132+i) := by decide +kernel

theorem phase_22 (v : ℕ) (hv : v ∈ List.range 135) : PhaseAt 22 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 22 v)
  have h := (join 0 68 67 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_22_0 phase_22_4) (join 8 4 4 phase_22_8 phase_22_12)) (join 16 8 8 (join 16 4 4 phase_22_16 phase_22_20) (join 24 4 4 phase_22_24 phase_22_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_22_32 phase_22_36) (join 40 4 4 phase_22_40 phase_22_44)) (join 48 8 12 (join 48 4 4 phase_22_48 phase_22_52) (join 56 4 8 phase_22_56 (join 60 4 4 phase_22_60 phase_22_64))))) (join 68 32 35 (join 68 16 16 (join 68 8 8 (join 68 4 4 phase_22_68 phase_22_72) (join 76 4 4 phase_22_76 phase_22_80)) (join 84 8 8 (join 84 4 4 phase_22_84 phase_22_88) (join 92 4 4 phase_22_92 phase_22_96))) (join 100 16 19 (join 100 8 8 (join 100 4 4 phase_22_100 phase_22_104) (join 108 4 4 phase_22_108 phase_22_112)) (join 116 8 11 (join 116 4 4 phase_22_116 phase_22_120) (join 124 4 7 phase_22_124 (join 128 4 3 phase_22_128 phase_22_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_22_0 : ∀ i ∈ List.range 1, ThresholdAt 22 (0+i) := by decide +kernel

theorem threshold_22_1 : ∀ i ∈ List.range 1, ThresholdAt 22 (1+i) := by decide +kernel

theorem threshold_22_2 : ∀ i ∈ List.range 1, ThresholdAt 22 (2+i) := by decide +kernel

theorem threshold_22_3 : ∀ i ∈ List.range 1, ThresholdAt 22 (3+i) := by decide +kernel

theorem threshold_22_4 : ∀ i ∈ List.range 1, ThresholdAt 22 (4+i) := by decide +kernel

theorem threshold_22_5 : ∀ i ∈ List.range 1, ThresholdAt 22 (5+i) := by decide +kernel

theorem threshold_22_6 : ∀ i ∈ List.range 1, ThresholdAt 22 (6+i) := by decide +kernel

theorem threshold_22_7 : ∀ i ∈ List.range 1, ThresholdAt 22 (7+i) := by decide +kernel

theorem threshold_22_8 : ∀ i ∈ List.range 1, ThresholdAt 22 (8+i) := by decide +kernel

theorem threshold_22_9 : ∀ i ∈ List.range 1, ThresholdAt 22 (9+i) := by decide +kernel

theorem threshold_22_10 : ∀ i ∈ List.range 1, ThresholdAt 22 (10+i) := by decide +kernel

theorem threshold_22_11 : ∀ i ∈ List.range 1, ThresholdAt 22 (11+i) := by decide +kernel

theorem threshold_22_12 : ∀ i ∈ List.range 1, ThresholdAt 22 (12+i) := by decide +kernel

theorem threshold_22_13 : ∀ i ∈ List.range 1, ThresholdAt 22 (13+i) := by decide +kernel

theorem threshold_22_14 : ∀ i ∈ List.range 1, ThresholdAt 22 (14+i) := by decide +kernel

theorem threshold_22_15 : ∀ i ∈ List.range 1, ThresholdAt 22 (15+i) := by decide +kernel

theorem threshold_22_16 : ∀ i ∈ List.range 1, ThresholdAt 22 (16+i) := by decide +kernel

theorem threshold_22_17 : ∀ i ∈ List.range 1, ThresholdAt 22 (17+i) := by decide +kernel

theorem threshold_22_18 : ∀ i ∈ List.range 1, ThresholdAt 22 (18+i) := by decide +kernel

theorem threshold_22_19 : ∀ i ∈ List.range 1, ThresholdAt 22 (19+i) := by decide +kernel

theorem threshold_22_20 : ∀ i ∈ List.range 1, ThresholdAt 22 (20+i) := by decide +kernel

theorem threshold_22_21 : ∀ i ∈ List.range 1, ThresholdAt 22 (21+i) := by decide +kernel

theorem threshold_22_22 : ∀ i ∈ List.range 1, ThresholdAt 22 (22+i) := by decide +kernel

theorem threshold_22_23 : ∀ i ∈ List.range 1, ThresholdAt 22 (23+i) := by decide +kernel

theorem threshold_22_24 : ∀ i ∈ List.range 1, ThresholdAt 22 (24+i) := by decide +kernel

theorem threshold_22_25 : ∀ i ∈ List.range 1, ThresholdAt 22 (25+i) := by decide +kernel

theorem threshold_22_26 : ∀ i ∈ List.range 1, ThresholdAt 22 (26+i) := by decide +kernel

theorem threshold_22_27 : ∀ i ∈ List.range 1, ThresholdAt 22 (27+i) := by decide +kernel

theorem threshold_22_28 : ∀ i ∈ List.range 1, ThresholdAt 22 (28+i) := by decide +kernel

theorem threshold_22_29 : ∀ i ∈ List.range 1, ThresholdAt 22 (29+i) := by decide +kernel

theorem threshold_22_30 : ∀ i ∈ List.range 1, ThresholdAt 22 (30+i) := by decide +kernel

theorem threshold_22_31 : ∀ i ∈ List.range 1, ThresholdAt 22 (31+i) := by decide +kernel

theorem threshold_22_32 : ∀ i ∈ List.range 1, ThresholdAt 22 (32+i) := by decide +kernel

theorem threshold_22_33 : ∀ i ∈ List.range 1, ThresholdAt 22 (33+i) := by decide +kernel

theorem threshold_22_34 : ∀ i ∈ List.range 1, ThresholdAt 22 (34+i) := by decide +kernel

theorem threshold_22_35 : ∀ i ∈ List.range 1, ThresholdAt 22 (35+i) := by decide +kernel

theorem threshold_22_36 : ∀ i ∈ List.range 1, ThresholdAt 22 (36+i) := by decide +kernel

theorem threshold_22_37 : ∀ i ∈ List.range 1, ThresholdAt 22 (37+i) := by decide +kernel

theorem threshold_22_38 : ∀ i ∈ List.range 1, ThresholdAt 22 (38+i) := by decide +kernel

theorem threshold_22_39 : ∀ i ∈ List.range 1, ThresholdAt 22 (39+i) := by decide +kernel

theorem threshold_22_40 : ∀ i ∈ List.range 1, ThresholdAt 22 (40+i) := by decide +kernel

theorem threshold_22_41 : ∀ i ∈ List.range 1, ThresholdAt 22 (41+i) := by decide +kernel

theorem threshold_22_42 : ∀ i ∈ List.range 1, ThresholdAt 22 (42+i) := by decide +kernel

theorem threshold_22_43 : ∀ i ∈ List.range 1, ThresholdAt 22 (43+i) := by decide +kernel

theorem threshold_22_44 : ∀ i ∈ List.range 1, ThresholdAt 22 (44+i) := by decide +kernel

theorem threshold_22_45 : ∀ i ∈ List.range 1, ThresholdAt 22 (45+i) := by decide +kernel

theorem threshold_22_46 : ∀ i ∈ List.range 1, ThresholdAt 22 (46+i) := by decide +kernel

theorem threshold_22_47 : ∀ i ∈ List.range 1, ThresholdAt 22 (47+i) := by decide +kernel

theorem threshold_22_48 : ∀ i ∈ List.range 1, ThresholdAt 22 (48+i) := by decide +kernel

theorem threshold_22_49 : ∀ i ∈ List.range 1, ThresholdAt 22 (49+i) := by decide +kernel

theorem threshold_22_50 : ∀ i ∈ List.range 1, ThresholdAt 22 (50+i) := by decide +kernel

theorem threshold_22_51 : ∀ i ∈ List.range 1, ThresholdAt 22 (51+i) := by decide +kernel

theorem threshold_22_52 : ∀ i ∈ List.range 1, ThresholdAt 22 (52+i) := by decide +kernel

theorem threshold_22_53 : ∀ i ∈ List.range 1, ThresholdAt 22 (53+i) := by decide +kernel

theorem threshold_22_54 : ∀ i ∈ List.range 1, ThresholdAt 22 (54+i) := by decide +kernel

theorem threshold_22_55 : ∀ i ∈ List.range 1, ThresholdAt 22 (55+i) := by decide +kernel

theorem threshold_22_56 : ∀ i ∈ List.range 1, ThresholdAt 22 (56+i) := by decide +kernel

theorem threshold_22_57 : ∀ i ∈ List.range 1, ThresholdAt 22 (57+i) := by decide +kernel

theorem threshold_22_58 : ∀ i ∈ List.range 1, ThresholdAt 22 (58+i) := by decide +kernel

theorem threshold_22_59 : ∀ i ∈ List.range 1, ThresholdAt 22 (59+i) := by decide +kernel

theorem threshold_22_60 : ∀ i ∈ List.range 1, ThresholdAt 22 (60+i) := by decide +kernel

theorem threshold_22_61 : ∀ i ∈ List.range 1, ThresholdAt 22 (61+i) := by decide +kernel

theorem threshold_22_62 : ∀ i ∈ List.range 1, ThresholdAt 22 (62+i) := by decide +kernel

theorem threshold_22_63 : ∀ i ∈ List.range 1, ThresholdAt 22 (63+i) := by decide +kernel

theorem threshold_22_64 : ∀ i ∈ List.range 1, ThresholdAt 22 (64+i) := by decide +kernel

theorem threshold_22_65 : ∀ i ∈ List.range 1, ThresholdAt 22 (65+i) := by decide +kernel

theorem threshold_22_66 : ∀ i ∈ List.range 1, ThresholdAt 22 (66+i) := by decide +kernel

theorem threshold_22_67 : ∀ i ∈ List.range 1, ThresholdAt 22 (67+i) := by decide +kernel

theorem threshold_22_68 : ∀ i ∈ List.range 1, ThresholdAt 22 (68+i) := by decide +kernel

theorem threshold_22_69 : ∀ i ∈ List.range 1, ThresholdAt 22 (69+i) := by decide +kernel

theorem threshold_22_70 : ∀ i ∈ List.range 1, ThresholdAt 22 (70+i) := by decide +kernel

theorem threshold_22_71 : ∀ i ∈ List.range 1, ThresholdAt 22 (71+i) := by decide +kernel

theorem threshold_22_72 : ∀ i ∈ List.range 1, ThresholdAt 22 (72+i) := by decide +kernel

theorem threshold_22_73 : ∀ i ∈ List.range 1, ThresholdAt 22 (73+i) := by decide +kernel

theorem threshold_22_74 : ∀ i ∈ List.range 1, ThresholdAt 22 (74+i) := by decide +kernel

theorem threshold_22_75 : ∀ i ∈ List.range 1, ThresholdAt 22 (75+i) := by decide +kernel

theorem threshold_22_76 : ∀ i ∈ List.range 1, ThresholdAt 22 (76+i) := by decide +kernel

theorem threshold_22_77 : ∀ i ∈ List.range 1, ThresholdAt 22 (77+i) := by decide +kernel

theorem threshold_22_78 : ∀ i ∈ List.range 1, ThresholdAt 22 (78+i) := by decide +kernel

theorem threshold_22_79 : ∀ i ∈ List.range 1, ThresholdAt 22 (79+i) := by decide +kernel

theorem threshold_22_80 : ∀ i ∈ List.range 1, ThresholdAt 22 (80+i) := by decide +kernel

theorem threshold_22_81 : ∀ i ∈ List.range 1, ThresholdAt 22 (81+i) := by decide +kernel

theorem threshold_22_82 : ∀ i ∈ List.range 1, ThresholdAt 22 (82+i) := by decide +kernel

theorem threshold_22_83 : ∀ i ∈ List.range 1, ThresholdAt 22 (83+i) := by decide +kernel

theorem threshold_22_84 : ∀ i ∈ List.range 1, ThresholdAt 22 (84+i) := by decide +kernel

theorem threshold_22_85 : ∀ i ∈ List.range 1, ThresholdAt 22 (85+i) := by decide +kernel

theorem threshold_22_86 : ∀ i ∈ List.range 1, ThresholdAt 22 (86+i) := by decide +kernel

theorem threshold_22_87 : ∀ i ∈ List.range 1, ThresholdAt 22 (87+i) := by decide +kernel

theorem threshold_22_88 : ∀ i ∈ List.range 1, ThresholdAt 22 (88+i) := by decide +kernel

theorem threshold_22_89 : ∀ i ∈ List.range 1, ThresholdAt 22 (89+i) := by decide +kernel

theorem threshold_22_90 : ∀ i ∈ List.range 1, ThresholdAt 22 (90+i) := by decide +kernel

theorem threshold_22_91 : ∀ i ∈ List.range 1, ThresholdAt 22 (91+i) := by decide +kernel

theorem threshold_22_92 : ∀ i ∈ List.range 1, ThresholdAt 22 (92+i) := by decide +kernel

theorem threshold_22_93 : ∀ i ∈ List.range 1, ThresholdAt 22 (93+i) := by decide +kernel

theorem threshold_22_94 : ∀ i ∈ List.range 1, ThresholdAt 22 (94+i) := by decide +kernel

theorem threshold_22_95 : ∀ i ∈ List.range 1, ThresholdAt 22 (95+i) := by decide +kernel

theorem threshold_22_96 : ∀ i ∈ List.range 1, ThresholdAt 22 (96+i) := by decide +kernel

theorem threshold_22_97 : ∀ i ∈ List.range 1, ThresholdAt 22 (97+i) := by decide +kernel

theorem threshold_22_98 : ∀ i ∈ List.range 1, ThresholdAt 22 (98+i) := by decide +kernel

theorem threshold_22_99 : ∀ i ∈ List.range 1, ThresholdAt 22 (99+i) := by decide +kernel

theorem threshold_22_100 : ∀ i ∈ List.range 1, ThresholdAt 22 (100+i) := by decide +kernel

theorem threshold_22_101 : ∀ i ∈ List.range 1, ThresholdAt 22 (101+i) := by decide +kernel

theorem threshold_22_102 : ∀ i ∈ List.range 1, ThresholdAt 22 (102+i) := by decide +kernel

theorem threshold_22_103 : ∀ i ∈ List.range 1, ThresholdAt 22 (103+i) := by decide +kernel

theorem threshold_22_104 : ∀ i ∈ List.range 1, ThresholdAt 22 (104+i) := by decide +kernel

theorem threshold_22_105 : ∀ i ∈ List.range 1, ThresholdAt 22 (105+i) := by decide +kernel

theorem threshold_22_106 : ∀ i ∈ List.range 1, ThresholdAt 22 (106+i) := by decide +kernel

theorem threshold_22_107 : ∀ i ∈ List.range 1, ThresholdAt 22 (107+i) := by decide +kernel

theorem threshold_22_108 : ∀ i ∈ List.range 1, ThresholdAt 22 (108+i) := by decide +kernel

theorem threshold_22_109 : ∀ i ∈ List.range 1, ThresholdAt 22 (109+i) := by decide +kernel

theorem threshold_22_110 : ∀ i ∈ List.range 1, ThresholdAt 22 (110+i) := by decide +kernel

theorem threshold_22_111 : ∀ i ∈ List.range 1, ThresholdAt 22 (111+i) := by decide +kernel

theorem threshold_22_112 : ∀ i ∈ List.range 1, ThresholdAt 22 (112+i) := by decide +kernel

theorem threshold_22_113 : ∀ i ∈ List.range 1, ThresholdAt 22 (113+i) := by decide +kernel

theorem threshold_22_114 : ∀ i ∈ List.range 1, ThresholdAt 22 (114+i) := by decide +kernel

theorem threshold_22_115 : ∀ i ∈ List.range 1, ThresholdAt 22 (115+i) := by decide +kernel

theorem threshold_22_116 : ∀ i ∈ List.range 1, ThresholdAt 22 (116+i) := by decide +kernel

theorem threshold_22_117 : ∀ i ∈ List.range 1, ThresholdAt 22 (117+i) := by decide +kernel

theorem threshold_22_118 : ∀ i ∈ List.range 1, ThresholdAt 22 (118+i) := by decide +kernel

theorem threshold_22_119 : ∀ i ∈ List.range 1, ThresholdAt 22 (119+i) := by decide +kernel

theorem threshold_22_120 : ∀ i ∈ List.range 1, ThresholdAt 22 (120+i) := by decide +kernel

theorem threshold_22_121 : ∀ i ∈ List.range 1, ThresholdAt 22 (121+i) := by decide +kernel

theorem threshold_22_122 : ∀ i ∈ List.range 1, ThresholdAt 22 (122+i) := by decide +kernel

theorem threshold_22_123 : ∀ i ∈ List.range 1, ThresholdAt 22 (123+i) := by decide +kernel

theorem threshold_22_124 : ∀ i ∈ List.range 1, ThresholdAt 22 (124+i) := by decide +kernel

theorem threshold_22_125 : ∀ i ∈ List.range 1, ThresholdAt 22 (125+i) := by decide +kernel

theorem threshold_22_126 : ∀ i ∈ List.range 1, ThresholdAt 22 (126+i) := by decide +kernel

theorem threshold_22_127 : ∀ i ∈ List.range 1, ThresholdAt 22 (127+i) := by decide +kernel

theorem threshold_22_128 : ∀ i ∈ List.range 1, ThresholdAt 22 (128+i) := by decide +kernel

theorem threshold_22_129 : ∀ i ∈ List.range 1, ThresholdAt 22 (129+i) := by decide +kernel

theorem threshold_22_130 : ∀ i ∈ List.range 1, ThresholdAt 22 (130+i) := by decide +kernel

theorem threshold_22_131 : ∀ i ∈ List.range 1, ThresholdAt 22 (131+i) := by decide +kernel

theorem threshold_22_132 : ∀ i ∈ List.range 1, ThresholdAt 22 (132+i) := by decide +kernel

theorem threshold_22_133 : ∀ i ∈ List.range 1, ThresholdAt 22 (133+i) := by decide +kernel

theorem threshold_22_134 : ∀ i ∈ List.range 1, ThresholdAt 22 (134+i) := by decide +kernel

theorem threshold_22 (v : ℕ) (hv : v ∈ List.range 135) : ThresholdAt 22 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 22 v)
  have h := (join 0 67 68 (join 0 33 34 (join 0 16 17 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_22_0 threshold_22_1) (join 2 1 1 threshold_22_2 threshold_22_3)) (join 4 2 2 (join 4 1 1 threshold_22_4 threshold_22_5) (join 6 1 1 threshold_22_6 threshold_22_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_22_8 threshold_22_9) (join 10 1 1 threshold_22_10 threshold_22_11)) (join 12 2 2 (join 12 1 1 threshold_22_12 threshold_22_13) (join 14 1 1 threshold_22_14 threshold_22_15)))) (join 16 8 9 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_22_16 threshold_22_17) (join 18 1 1 threshold_22_18 threshold_22_19)) (join 20 2 2 (join 20 1 1 threshold_22_20 threshold_22_21) (join 22 1 1 threshold_22_22 threshold_22_23))) (join 24 4 5 (join 24 2 2 (join 24 1 1 threshold_22_24 threshold_22_25) (join 26 1 1 threshold_22_26 threshold_22_27)) (join 28 2 3 (join 28 1 1 threshold_22_28 threshold_22_29) (join 30 1 2 threshold_22_30 (join 31 1 1 threshold_22_31 threshold_22_32)))))) (join 33 17 17 (join 33 8 9 (join 33 4 4 (join 33 2 2 (join 33 1 1 threshold_22_33 threshold_22_34) (join 35 1 1 threshold_22_35 threshold_22_36)) (join 37 2 2 (join 37 1 1 threshold_22_37 threshold_22_38) (join 39 1 1 threshold_22_39 threshold_22_40))) (join 41 4 5 (join 41 2 2 (join 41 1 1 threshold_22_41 threshold_22_42) (join 43 1 1 threshold_22_43 threshold_22_44)) (join 45 2 3 (join 45 1 1 threshold_22_45 threshold_22_46) (join 47 1 2 threshold_22_47 (join 48 1 1 threshold_22_48 threshold_22_49))))) (join 50 8 9 (join 50 4 4 (join 50 2 2 (join 50 1 1 threshold_22_50 threshold_22_51) (join 52 1 1 threshold_22_52 threshold_22_53)) (join 54 2 2 (join 54 1 1 threshold_22_54 threshold_22_55) (join 56 1 1 threshold_22_56 threshold_22_57))) (join 58 4 5 (join 58 2 2 (join 58 1 1 threshold_22_58 threshold_22_59) (join 60 1 1 threshold_22_60 threshold_22_61)) (join 62 2 3 (join 62 1 1 threshold_22_62 threshold_22_63) (join 64 1 2 threshold_22_64 (join 65 1 1 threshold_22_65 threshold_22_66))))))) (join 67 34 34 (join 67 17 17 (join 67 8 9 (join 67 4 4 (join 67 2 2 (join 67 1 1 threshold_22_67 threshold_22_68) (join 69 1 1 threshold_22_69 threshold_22_70)) (join 71 2 2 (join 71 1 1 threshold_22_71 threshold_22_72) (join 73 1 1 threshold_22_73 threshold_22_74))) (join 75 4 5 (join 75 2 2 (join 75 1 1 threshold_22_75 threshold_22_76) (join 77 1 1 threshold_22_77 threshold_22_78)) (join 79 2 3 (join 79 1 1 threshold_22_79 threshold_22_80) (join 81 1 2 threshold_22_81 (join 82 1 1 threshold_22_82 threshold_22_83))))) (join 84 8 9 (join 84 4 4 (join 84 2 2 (join 84 1 1 threshold_22_84 threshold_22_85) (join 86 1 1 threshold_22_86 threshold_22_87)) (join 88 2 2 (join 88 1 1 threshold_22_88 threshold_22_89) (join 90 1 1 threshold_22_90 threshold_22_91))) (join 92 4 5 (join 92 2 2 (join 92 1 1 threshold_22_92 threshold_22_93) (join 94 1 1 threshold_22_94 threshold_22_95)) (join 96 2 3 (join 96 1 1 threshold_22_96 threshold_22_97) (join 98 1 2 threshold_22_98 (join 99 1 1 threshold_22_99 threshold_22_100)))))) (join 101 17 17 (join 101 8 9 (join 101 4 4 (join 101 2 2 (join 101 1 1 threshold_22_101 threshold_22_102) (join 103 1 1 threshold_22_103 threshold_22_104)) (join 105 2 2 (join 105 1 1 threshold_22_105 threshold_22_106) (join 107 1 1 threshold_22_107 threshold_22_108))) (join 109 4 5 (join 109 2 2 (join 109 1 1 threshold_22_109 threshold_22_110) (join 111 1 1 threshold_22_111 threshold_22_112)) (join 113 2 3 (join 113 1 1 threshold_22_113 threshold_22_114) (join 115 1 2 threshold_22_115 (join 116 1 1 threshold_22_116 threshold_22_117))))) (join 118 8 9 (join 118 4 4 (join 118 2 2 (join 118 1 1 threshold_22_118 threshold_22_119) (join 120 1 1 threshold_22_120 threshold_22_121)) (join 122 2 2 (join 122 1 1 threshold_22_122 threshold_22_123) (join 124 1 1 threshold_22_124 threshold_22_125))) (join 126 4 5 (join 126 2 2 (join 126 1 1 threshold_22_126 threshold_22_127) (join 128 1 1 threshold_22_128 threshold_22_129)) (join 130 2 3 (join 130 1 1 threshold_22_130 threshold_22_131) (join 132 1 2 threshold_22_132 (join 133 1 1 threshold_22_133 threshold_22_134))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_22_0 : ∀ i ∈ List.range 4, LedgerAt 22 (0+i) := by decide +kernel

theorem ledger_22_4 : ∀ i ∈ List.range 4, LedgerAt 22 (4+i) := by decide +kernel

theorem ledger_22_8 : ∀ i ∈ List.range 4, LedgerAt 22 (8+i) := by decide +kernel

theorem ledger_22_12 : ∀ i ∈ List.range 4, LedgerAt 22 (12+i) := by decide +kernel

theorem ledger_22_16 : ∀ i ∈ List.range 4, LedgerAt 22 (16+i) := by decide +kernel

theorem ledger_22_20 : ∀ i ∈ List.range 4, LedgerAt 22 (20+i) := by decide +kernel

theorem ledger_22_24 : ∀ i ∈ List.range 4, LedgerAt 22 (24+i) := by decide +kernel

theorem ledger_22_28 : ∀ i ∈ List.range 4, LedgerAt 22 (28+i) := by decide +kernel

theorem ledger_22_32 : ∀ i ∈ List.range 4, LedgerAt 22 (32+i) := by decide +kernel

theorem ledger_22_36 : ∀ i ∈ List.range 4, LedgerAt 22 (36+i) := by decide +kernel

theorem ledger_22_40 : ∀ i ∈ List.range 4, LedgerAt 22 (40+i) := by decide +kernel

theorem ledger_22_44 : ∀ i ∈ List.range 4, LedgerAt 22 (44+i) := by decide +kernel

theorem ledger_22_48 : ∀ i ∈ List.range 4, LedgerAt 22 (48+i) := by decide +kernel

theorem ledger_22_52 : ∀ i ∈ List.range 4, LedgerAt 22 (52+i) := by decide +kernel

theorem ledger_22_56 : ∀ i ∈ List.range 4, LedgerAt 22 (56+i) := by decide +kernel

theorem ledger_22_60 : ∀ i ∈ List.range 4, LedgerAt 22 (60+i) := by decide +kernel

theorem ledger_22_64 : ∀ i ∈ List.range 4, LedgerAt 22 (64+i) := by decide +kernel

theorem ledger_22_68 : ∀ i ∈ List.range 4, LedgerAt 22 (68+i) := by decide +kernel

theorem ledger_22_72 : ∀ i ∈ List.range 4, LedgerAt 22 (72+i) := by decide +kernel

theorem ledger_22_76 : ∀ i ∈ List.range 4, LedgerAt 22 (76+i) := by decide +kernel

theorem ledger_22_80 : ∀ i ∈ List.range 4, LedgerAt 22 (80+i) := by decide +kernel

theorem ledger_22_84 : ∀ i ∈ List.range 4, LedgerAt 22 (84+i) := by decide +kernel

theorem ledger_22_88 : ∀ i ∈ List.range 4, LedgerAt 22 (88+i) := by decide +kernel

theorem ledger_22_92 : ∀ i ∈ List.range 4, LedgerAt 22 (92+i) := by decide +kernel

theorem ledger_22_96 : ∀ i ∈ List.range 4, LedgerAt 22 (96+i) := by decide +kernel

theorem ledger_22_100 : ∀ i ∈ List.range 4, LedgerAt 22 (100+i) := by decide +kernel

theorem ledger_22_104 : ∀ i ∈ List.range 4, LedgerAt 22 (104+i) := by decide +kernel

theorem ledger_22_108 : ∀ i ∈ List.range 4, LedgerAt 22 (108+i) := by decide +kernel

theorem ledger_22_112 : ∀ i ∈ List.range 4, LedgerAt 22 (112+i) := by decide +kernel

theorem ledger_22_116 : ∀ i ∈ List.range 4, LedgerAt 22 (116+i) := by decide +kernel

theorem ledger_22_120 : ∀ i ∈ List.range 4, LedgerAt 22 (120+i) := by decide +kernel

theorem ledger_22_124 : ∀ i ∈ List.range 4, LedgerAt 22 (124+i) := by decide +kernel

theorem ledger_22_128 : ∀ i ∈ List.range 4, LedgerAt 22 (128+i) := by decide +kernel

theorem ledger_22_132 : ∀ i ∈ List.range 3, LedgerAt 22 (132+i) := by decide +kernel

theorem ledger_22 (v : ℕ) (hv : v ∈ List.range 135) : LedgerAt 22 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 22 v)
  have h := (join 0 68 67 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_22_0 ledger_22_4) (join 8 4 4 ledger_22_8 ledger_22_12)) (join 16 8 8 (join 16 4 4 ledger_22_16 ledger_22_20) (join 24 4 4 ledger_22_24 ledger_22_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_22_32 ledger_22_36) (join 40 4 4 ledger_22_40 ledger_22_44)) (join 48 8 12 (join 48 4 4 ledger_22_48 ledger_22_52) (join 56 4 8 ledger_22_56 (join 60 4 4 ledger_22_60 ledger_22_64))))) (join 68 32 35 (join 68 16 16 (join 68 8 8 (join 68 4 4 ledger_22_68 ledger_22_72) (join 76 4 4 ledger_22_76 ledger_22_80)) (join 84 8 8 (join 84 4 4 ledger_22_84 ledger_22_88) (join 92 4 4 ledger_22_92 ledger_22_96))) (join 100 16 19 (join 100 8 8 (join 100 4 4 ledger_22_100 ledger_22_104) (join 108 4 4 ledger_22_108 ledger_22_112)) (join 116 8 11 (join 116 4 4 ledger_22_116 ledger_22_120) (join 124 4 7 ledger_22_124 (join 128 4 3 ledger_22_128 ledger_22_132))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
