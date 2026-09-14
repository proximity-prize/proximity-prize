import ProximityPrize.SubmissionLower.HigherAffineCheckedR176810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_18_0 : ∀ i ∈ List.range 4, SingleAt 18 (0+i) := by decide +kernel

theorem single_18_4 : ∀ i ∈ List.range 4, SingleAt 18 (4+i) := by decide +kernel

theorem single_18_8 : ∀ i ∈ List.range 4, SingleAt 18 (8+i) := by decide +kernel

theorem single_18_12 : ∀ i ∈ List.range 4, SingleAt 18 (12+i) := by decide +kernel

theorem single_18_16 : ∀ i ∈ List.range 4, SingleAt 18 (16+i) := by decide +kernel

theorem single_18_20 : ∀ i ∈ List.range 4, SingleAt 18 (20+i) := by decide +kernel

theorem single_18_24 : ∀ i ∈ List.range 4, SingleAt 18 (24+i) := by decide +kernel

theorem single_18_28 : ∀ i ∈ List.range 4, SingleAt 18 (28+i) := by decide +kernel

theorem single_18_32 : ∀ i ∈ List.range 4, SingleAt 18 (32+i) := by decide +kernel

theorem single_18_36 : ∀ i ∈ List.range 4, SingleAt 18 (36+i) := by decide +kernel

theorem single_18_40 : ∀ i ∈ List.range 4, SingleAt 18 (40+i) := by decide +kernel

theorem single_18_44 : ∀ i ∈ List.range 4, SingleAt 18 (44+i) := by decide +kernel

theorem single_18_48 : ∀ i ∈ List.range 4, SingleAt 18 (48+i) := by decide +kernel

theorem single_18_52 : ∀ i ∈ List.range 4, SingleAt 18 (52+i) := by decide +kernel

theorem single_18_56 : ∀ i ∈ List.range 4, SingleAt 18 (56+i) := by decide +kernel

theorem single_18_60 : ∀ i ∈ List.range 4, SingleAt 18 (60+i) := by decide +kernel

theorem single_18_64 : ∀ i ∈ List.range 4, SingleAt 18 (64+i) := by decide +kernel

theorem single_18_68 : ∀ i ∈ List.range 4, SingleAt 18 (68+i) := by decide +kernel

theorem single_18_72 : ∀ i ∈ List.range 4, SingleAt 18 (72+i) := by decide +kernel

theorem single_18_76 : ∀ i ∈ List.range 4, SingleAt 18 (76+i) := by decide +kernel

theorem single_18_80 : ∀ i ∈ List.range 4, SingleAt 18 (80+i) := by decide +kernel

theorem single_18_84 : ∀ i ∈ List.range 4, SingleAt 18 (84+i) := by decide +kernel

theorem single_18_88 : ∀ i ∈ List.range 4, SingleAt 18 (88+i) := by decide +kernel

theorem single_18_92 : ∀ i ∈ List.range 4, SingleAt 18 (92+i) := by decide +kernel

theorem single_18_96 : ∀ i ∈ List.range 4, SingleAt 18 (96+i) := by decide +kernel

theorem single_18_100 : ∀ i ∈ List.range 4, SingleAt 18 (100+i) := by decide +kernel

theorem single_18_104 : ∀ i ∈ List.range 4, SingleAt 18 (104+i) := by decide +kernel

theorem single_18_108 : ∀ i ∈ List.range 4, SingleAt 18 (108+i) := by decide +kernel

theorem single_18_112 : ∀ i ∈ List.range 4, SingleAt 18 (112+i) := by decide +kernel

theorem single_18_116 : ∀ i ∈ List.range 4, SingleAt 18 (116+i) := by decide +kernel

theorem single_18_120 : ∀ i ∈ List.range 4, SingleAt 18 (120+i) := by decide +kernel

theorem single_18_124 : ∀ i ∈ List.range 4, SingleAt 18 (124+i) := by decide +kernel

theorem single_18_128 : ∀ i ∈ List.range 4, SingleAt 18 (128+i) := by decide +kernel

theorem single_18_132 : ∀ i ∈ List.range 4, SingleAt 18 (132+i) := by decide +kernel

theorem single_18_136 : ∀ i ∈ List.range 3, SingleAt 18 (136+i) := by decide +kernel

theorem single_18 (v : ℕ) (hv : v ∈ List.range 139) : SingleAt 18 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 18 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_18_0 single_18_4) (join 8 4 4 single_18_8 single_18_12)) (join 16 8 8 (join 16 4 4 single_18_16 single_18_20) (join 24 4 4 single_18_24 single_18_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 single_18_32 single_18_36) (join 40 4 4 single_18_40 single_18_44)) (join 48 8 12 (join 48 4 4 single_18_48 single_18_52) (join 56 4 8 single_18_56 (join 60 4 4 single_18_60 single_18_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 single_18_68 single_18_72) (join 76 4 4 single_18_76 single_18_80)) (join 84 8 12 (join 84 4 4 single_18_84 single_18_88) (join 92 4 8 single_18_92 (join 96 4 4 single_18_96 single_18_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 single_18_104 single_18_108) (join 112 4 4 single_18_112 single_18_116)) (join 120 8 11 (join 120 4 4 single_18_120 single_18_124) (join 128 4 7 single_18_128 (join 132 4 3 single_18_132 single_18_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_18_0 : ∀ i ∈ List.range 4, PhaseAt 18 (0+i) := by decide +kernel

theorem phase_18_4 : ∀ i ∈ List.range 4, PhaseAt 18 (4+i) := by decide +kernel

theorem phase_18_8 : ∀ i ∈ List.range 4, PhaseAt 18 (8+i) := by decide +kernel

theorem phase_18_12 : ∀ i ∈ List.range 4, PhaseAt 18 (12+i) := by decide +kernel

theorem phase_18_16 : ∀ i ∈ List.range 4, PhaseAt 18 (16+i) := by decide +kernel

theorem phase_18_20 : ∀ i ∈ List.range 4, PhaseAt 18 (20+i) := by decide +kernel

theorem phase_18_24 : ∀ i ∈ List.range 4, PhaseAt 18 (24+i) := by decide +kernel

theorem phase_18_28 : ∀ i ∈ List.range 4, PhaseAt 18 (28+i) := by decide +kernel

theorem phase_18_32 : ∀ i ∈ List.range 4, PhaseAt 18 (32+i) := by decide +kernel

theorem phase_18_36 : ∀ i ∈ List.range 4, PhaseAt 18 (36+i) := by decide +kernel

theorem phase_18_40 : ∀ i ∈ List.range 4, PhaseAt 18 (40+i) := by decide +kernel

theorem phase_18_44 : ∀ i ∈ List.range 4, PhaseAt 18 (44+i) := by decide +kernel

theorem phase_18_48 : ∀ i ∈ List.range 4, PhaseAt 18 (48+i) := by decide +kernel

theorem phase_18_52 : ∀ i ∈ List.range 4, PhaseAt 18 (52+i) := by decide +kernel

theorem phase_18_56 : ∀ i ∈ List.range 4, PhaseAt 18 (56+i) := by decide +kernel

theorem phase_18_60 : ∀ i ∈ List.range 4, PhaseAt 18 (60+i) := by decide +kernel

theorem phase_18_64 : ∀ i ∈ List.range 4, PhaseAt 18 (64+i) := by decide +kernel

theorem phase_18_68 : ∀ i ∈ List.range 4, PhaseAt 18 (68+i) := by decide +kernel

theorem phase_18_72 : ∀ i ∈ List.range 4, PhaseAt 18 (72+i) := by decide +kernel

theorem phase_18_76 : ∀ i ∈ List.range 4, PhaseAt 18 (76+i) := by decide +kernel

theorem phase_18_80 : ∀ i ∈ List.range 4, PhaseAt 18 (80+i) := by decide +kernel

theorem phase_18_84 : ∀ i ∈ List.range 4, PhaseAt 18 (84+i) := by decide +kernel

theorem phase_18_88 : ∀ i ∈ List.range 4, PhaseAt 18 (88+i) := by decide +kernel

theorem phase_18_92 : ∀ i ∈ List.range 4, PhaseAt 18 (92+i) := by decide +kernel

theorem phase_18_96 : ∀ i ∈ List.range 4, PhaseAt 18 (96+i) := by decide +kernel

theorem phase_18_100 : ∀ i ∈ List.range 4, PhaseAt 18 (100+i) := by decide +kernel

theorem phase_18_104 : ∀ i ∈ List.range 4, PhaseAt 18 (104+i) := by decide +kernel

theorem phase_18_108 : ∀ i ∈ List.range 4, PhaseAt 18 (108+i) := by decide +kernel

theorem phase_18_112 : ∀ i ∈ List.range 4, PhaseAt 18 (112+i) := by decide +kernel

theorem phase_18_116 : ∀ i ∈ List.range 4, PhaseAt 18 (116+i) := by decide +kernel

theorem phase_18_120 : ∀ i ∈ List.range 4, PhaseAt 18 (120+i) := by decide +kernel

theorem phase_18_124 : ∀ i ∈ List.range 4, PhaseAt 18 (124+i) := by decide +kernel

theorem phase_18_128 : ∀ i ∈ List.range 4, PhaseAt 18 (128+i) := by decide +kernel

theorem phase_18_132 : ∀ i ∈ List.range 4, PhaseAt 18 (132+i) := by decide +kernel

theorem phase_18_136 : ∀ i ∈ List.range 3, PhaseAt 18 (136+i) := by decide +kernel

theorem phase_18 (v : ℕ) (hv : v ∈ List.range 139) : PhaseAt 18 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 18 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_18_0 phase_18_4) (join 8 4 4 phase_18_8 phase_18_12)) (join 16 8 8 (join 16 4 4 phase_18_16 phase_18_20) (join 24 4 4 phase_18_24 phase_18_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_18_32 phase_18_36) (join 40 4 4 phase_18_40 phase_18_44)) (join 48 8 12 (join 48 4 4 phase_18_48 phase_18_52) (join 56 4 8 phase_18_56 (join 60 4 4 phase_18_60 phase_18_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 phase_18_68 phase_18_72) (join 76 4 4 phase_18_76 phase_18_80)) (join 84 8 12 (join 84 4 4 phase_18_84 phase_18_88) (join 92 4 8 phase_18_92 (join 96 4 4 phase_18_96 phase_18_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 phase_18_104 phase_18_108) (join 112 4 4 phase_18_112 phase_18_116)) (join 120 8 11 (join 120 4 4 phase_18_120 phase_18_124) (join 128 4 7 phase_18_128 (join 132 4 3 phase_18_132 phase_18_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_18_0 : ∀ i ∈ List.range 1, ThresholdAt 18 (0+i) := by decide +kernel

theorem threshold_18_1 : ∀ i ∈ List.range 1, ThresholdAt 18 (1+i) := by decide +kernel

theorem threshold_18_2 : ∀ i ∈ List.range 1, ThresholdAt 18 (2+i) := by decide +kernel

theorem threshold_18_3 : ∀ i ∈ List.range 1, ThresholdAt 18 (3+i) := by decide +kernel

theorem threshold_18_4 : ∀ i ∈ List.range 1, ThresholdAt 18 (4+i) := by decide +kernel

theorem threshold_18_5 : ∀ i ∈ List.range 1, ThresholdAt 18 (5+i) := by decide +kernel

theorem threshold_18_6 : ∀ i ∈ List.range 1, ThresholdAt 18 (6+i) := by decide +kernel

theorem threshold_18_7 : ∀ i ∈ List.range 1, ThresholdAt 18 (7+i) := by decide +kernel

theorem threshold_18_8 : ∀ i ∈ List.range 1, ThresholdAt 18 (8+i) := by decide +kernel

theorem threshold_18_9 : ∀ i ∈ List.range 1, ThresholdAt 18 (9+i) := by decide +kernel

theorem threshold_18_10 : ∀ i ∈ List.range 1, ThresholdAt 18 (10+i) := by decide +kernel

theorem threshold_18_11 : ∀ i ∈ List.range 1, ThresholdAt 18 (11+i) := by decide +kernel

theorem threshold_18_12 : ∀ i ∈ List.range 1, ThresholdAt 18 (12+i) := by decide +kernel

theorem threshold_18_13 : ∀ i ∈ List.range 1, ThresholdAt 18 (13+i) := by decide +kernel

theorem threshold_18_14 : ∀ i ∈ List.range 1, ThresholdAt 18 (14+i) := by decide +kernel

theorem threshold_18_15 : ∀ i ∈ List.range 1, ThresholdAt 18 (15+i) := by decide +kernel

theorem threshold_18_16 : ∀ i ∈ List.range 1, ThresholdAt 18 (16+i) := by decide +kernel

theorem threshold_18_17 : ∀ i ∈ List.range 1, ThresholdAt 18 (17+i) := by decide +kernel

theorem threshold_18_18 : ∀ i ∈ List.range 1, ThresholdAt 18 (18+i) := by decide +kernel

theorem threshold_18_19 : ∀ i ∈ List.range 1, ThresholdAt 18 (19+i) := by decide +kernel

theorem threshold_18_20 : ∀ i ∈ List.range 1, ThresholdAt 18 (20+i) := by decide +kernel

theorem threshold_18_21 : ∀ i ∈ List.range 1, ThresholdAt 18 (21+i) := by decide +kernel

theorem threshold_18_22 : ∀ i ∈ List.range 1, ThresholdAt 18 (22+i) := by decide +kernel

theorem threshold_18_23 : ∀ i ∈ List.range 1, ThresholdAt 18 (23+i) := by decide +kernel

theorem threshold_18_24 : ∀ i ∈ List.range 1, ThresholdAt 18 (24+i) := by decide +kernel

theorem threshold_18_25 : ∀ i ∈ List.range 1, ThresholdAt 18 (25+i) := by decide +kernel

theorem threshold_18_26 : ∀ i ∈ List.range 1, ThresholdAt 18 (26+i) := by decide +kernel

theorem threshold_18_27 : ∀ i ∈ List.range 1, ThresholdAt 18 (27+i) := by decide +kernel

theorem threshold_18_28 : ∀ i ∈ List.range 1, ThresholdAt 18 (28+i) := by decide +kernel

theorem threshold_18_29 : ∀ i ∈ List.range 1, ThresholdAt 18 (29+i) := by decide +kernel

theorem threshold_18_30 : ∀ i ∈ List.range 1, ThresholdAt 18 (30+i) := by decide +kernel

theorem threshold_18_31 : ∀ i ∈ List.range 1, ThresholdAt 18 (31+i) := by decide +kernel

theorem threshold_18_32 : ∀ i ∈ List.range 1, ThresholdAt 18 (32+i) := by decide +kernel

theorem threshold_18_33 : ∀ i ∈ List.range 1, ThresholdAt 18 (33+i) := by decide +kernel

theorem threshold_18_34 : ∀ i ∈ List.range 1, ThresholdAt 18 (34+i) := by decide +kernel

theorem threshold_18_35 : ∀ i ∈ List.range 1, ThresholdAt 18 (35+i) := by decide +kernel

theorem threshold_18_36 : ∀ i ∈ List.range 1, ThresholdAt 18 (36+i) := by decide +kernel

theorem threshold_18_37 : ∀ i ∈ List.range 1, ThresholdAt 18 (37+i) := by decide +kernel

theorem threshold_18_38 : ∀ i ∈ List.range 1, ThresholdAt 18 (38+i) := by decide +kernel

theorem threshold_18_39 : ∀ i ∈ List.range 1, ThresholdAt 18 (39+i) := by decide +kernel

theorem threshold_18_40 : ∀ i ∈ List.range 1, ThresholdAt 18 (40+i) := by decide +kernel

theorem threshold_18_41 : ∀ i ∈ List.range 1, ThresholdAt 18 (41+i) := by decide +kernel

theorem threshold_18_42 : ∀ i ∈ List.range 1, ThresholdAt 18 (42+i) := by decide +kernel

theorem threshold_18_43 : ∀ i ∈ List.range 1, ThresholdAt 18 (43+i) := by decide +kernel

theorem threshold_18_44 : ∀ i ∈ List.range 1, ThresholdAt 18 (44+i) := by decide +kernel

theorem threshold_18_45 : ∀ i ∈ List.range 1, ThresholdAt 18 (45+i) := by decide +kernel

theorem threshold_18_46 : ∀ i ∈ List.range 1, ThresholdAt 18 (46+i) := by decide +kernel

theorem threshold_18_47 : ∀ i ∈ List.range 1, ThresholdAt 18 (47+i) := by decide +kernel

theorem threshold_18_48 : ∀ i ∈ List.range 1, ThresholdAt 18 (48+i) := by decide +kernel

theorem threshold_18_49 : ∀ i ∈ List.range 1, ThresholdAt 18 (49+i) := by decide +kernel

theorem threshold_18_50 : ∀ i ∈ List.range 1, ThresholdAt 18 (50+i) := by decide +kernel

theorem threshold_18_51 : ∀ i ∈ List.range 1, ThresholdAt 18 (51+i) := by decide +kernel

theorem threshold_18_52 : ∀ i ∈ List.range 1, ThresholdAt 18 (52+i) := by decide +kernel

theorem threshold_18_53 : ∀ i ∈ List.range 1, ThresholdAt 18 (53+i) := by decide +kernel

theorem threshold_18_54 : ∀ i ∈ List.range 1, ThresholdAt 18 (54+i) := by decide +kernel

theorem threshold_18_55 : ∀ i ∈ List.range 1, ThresholdAt 18 (55+i) := by decide +kernel

theorem threshold_18_56 : ∀ i ∈ List.range 1, ThresholdAt 18 (56+i) := by decide +kernel

theorem threshold_18_57 : ∀ i ∈ List.range 1, ThresholdAt 18 (57+i) := by decide +kernel

theorem threshold_18_58 : ∀ i ∈ List.range 1, ThresholdAt 18 (58+i) := by decide +kernel

theorem threshold_18_59 : ∀ i ∈ List.range 1, ThresholdAt 18 (59+i) := by decide +kernel

theorem threshold_18_60 : ∀ i ∈ List.range 1, ThresholdAt 18 (60+i) := by decide +kernel

theorem threshold_18_61 : ∀ i ∈ List.range 1, ThresholdAt 18 (61+i) := by decide +kernel

theorem threshold_18_62 : ∀ i ∈ List.range 1, ThresholdAt 18 (62+i) := by decide +kernel

theorem threshold_18_63 : ∀ i ∈ List.range 1, ThresholdAt 18 (63+i) := by decide +kernel

theorem threshold_18_64 : ∀ i ∈ List.range 1, ThresholdAt 18 (64+i) := by decide +kernel

theorem threshold_18_65 : ∀ i ∈ List.range 1, ThresholdAt 18 (65+i) := by decide +kernel

theorem threshold_18_66 : ∀ i ∈ List.range 1, ThresholdAt 18 (66+i) := by decide +kernel

theorem threshold_18_67 : ∀ i ∈ List.range 1, ThresholdAt 18 (67+i) := by decide +kernel

theorem threshold_18_68 : ∀ i ∈ List.range 1, ThresholdAt 18 (68+i) := by decide +kernel

theorem threshold_18_69 : ∀ i ∈ List.range 1, ThresholdAt 18 (69+i) := by decide +kernel

theorem threshold_18_70 : ∀ i ∈ List.range 1, ThresholdAt 18 (70+i) := by decide +kernel

theorem threshold_18_71 : ∀ i ∈ List.range 1, ThresholdAt 18 (71+i) := by decide +kernel

theorem threshold_18_72 : ∀ i ∈ List.range 1, ThresholdAt 18 (72+i) := by decide +kernel

theorem threshold_18_73 : ∀ i ∈ List.range 1, ThresholdAt 18 (73+i) := by decide +kernel

theorem threshold_18_74 : ∀ i ∈ List.range 1, ThresholdAt 18 (74+i) := by decide +kernel

theorem threshold_18_75 : ∀ i ∈ List.range 1, ThresholdAt 18 (75+i) := by decide +kernel

theorem threshold_18_76 : ∀ i ∈ List.range 1, ThresholdAt 18 (76+i) := by decide +kernel

theorem threshold_18_77 : ∀ i ∈ List.range 1, ThresholdAt 18 (77+i) := by decide +kernel

theorem threshold_18_78 : ∀ i ∈ List.range 1, ThresholdAt 18 (78+i) := by decide +kernel

theorem threshold_18_79 : ∀ i ∈ List.range 1, ThresholdAt 18 (79+i) := by decide +kernel

theorem threshold_18_80 : ∀ i ∈ List.range 1, ThresholdAt 18 (80+i) := by decide +kernel

theorem threshold_18_81 : ∀ i ∈ List.range 1, ThresholdAt 18 (81+i) := by decide +kernel

theorem threshold_18_82 : ∀ i ∈ List.range 1, ThresholdAt 18 (82+i) := by decide +kernel

theorem threshold_18_83 : ∀ i ∈ List.range 1, ThresholdAt 18 (83+i) := by decide +kernel

theorem threshold_18_84 : ∀ i ∈ List.range 1, ThresholdAt 18 (84+i) := by decide +kernel

theorem threshold_18_85 : ∀ i ∈ List.range 1, ThresholdAt 18 (85+i) := by decide +kernel

theorem threshold_18_86 : ∀ i ∈ List.range 1, ThresholdAt 18 (86+i) := by decide +kernel

theorem threshold_18_87 : ∀ i ∈ List.range 1, ThresholdAt 18 (87+i) := by decide +kernel

theorem threshold_18_88 : ∀ i ∈ List.range 1, ThresholdAt 18 (88+i) := by decide +kernel

theorem threshold_18_89 : ∀ i ∈ List.range 1, ThresholdAt 18 (89+i) := by decide +kernel

theorem threshold_18_90 : ∀ i ∈ List.range 1, ThresholdAt 18 (90+i) := by decide +kernel

theorem threshold_18_91 : ∀ i ∈ List.range 1, ThresholdAt 18 (91+i) := by decide +kernel

theorem threshold_18_92 : ∀ i ∈ List.range 1, ThresholdAt 18 (92+i) := by decide +kernel

theorem threshold_18_93 : ∀ i ∈ List.range 1, ThresholdAt 18 (93+i) := by decide +kernel

theorem threshold_18_94 : ∀ i ∈ List.range 1, ThresholdAt 18 (94+i) := by decide +kernel

theorem threshold_18_95 : ∀ i ∈ List.range 1, ThresholdAt 18 (95+i) := by decide +kernel

theorem threshold_18_96 : ∀ i ∈ List.range 1, ThresholdAt 18 (96+i) := by decide +kernel

theorem threshold_18_97 : ∀ i ∈ List.range 1, ThresholdAt 18 (97+i) := by decide +kernel

theorem threshold_18_98 : ∀ i ∈ List.range 1, ThresholdAt 18 (98+i) := by decide +kernel

theorem threshold_18_99 : ∀ i ∈ List.range 1, ThresholdAt 18 (99+i) := by decide +kernel

theorem threshold_18_100 : ∀ i ∈ List.range 1, ThresholdAt 18 (100+i) := by decide +kernel

theorem threshold_18_101 : ∀ i ∈ List.range 1, ThresholdAt 18 (101+i) := by decide +kernel

theorem threshold_18_102 : ∀ i ∈ List.range 1, ThresholdAt 18 (102+i) := by decide +kernel

theorem threshold_18_103 : ∀ i ∈ List.range 1, ThresholdAt 18 (103+i) := by decide +kernel

theorem threshold_18_104 : ∀ i ∈ List.range 1, ThresholdAt 18 (104+i) := by decide +kernel

theorem threshold_18_105 : ∀ i ∈ List.range 1, ThresholdAt 18 (105+i) := by decide +kernel

theorem threshold_18_106 : ∀ i ∈ List.range 1, ThresholdAt 18 (106+i) := by decide +kernel

theorem threshold_18_107 : ∀ i ∈ List.range 1, ThresholdAt 18 (107+i) := by decide +kernel

theorem threshold_18_108 : ∀ i ∈ List.range 1, ThresholdAt 18 (108+i) := by decide +kernel

theorem threshold_18_109 : ∀ i ∈ List.range 1, ThresholdAt 18 (109+i) := by decide +kernel

theorem threshold_18_110 : ∀ i ∈ List.range 1, ThresholdAt 18 (110+i) := by decide +kernel

theorem threshold_18_111 : ∀ i ∈ List.range 1, ThresholdAt 18 (111+i) := by decide +kernel

theorem threshold_18_112 : ∀ i ∈ List.range 1, ThresholdAt 18 (112+i) := by decide +kernel

theorem threshold_18_113 : ∀ i ∈ List.range 1, ThresholdAt 18 (113+i) := by decide +kernel

theorem threshold_18_114 : ∀ i ∈ List.range 1, ThresholdAt 18 (114+i) := by decide +kernel

theorem threshold_18_115 : ∀ i ∈ List.range 1, ThresholdAt 18 (115+i) := by decide +kernel

theorem threshold_18_116 : ∀ i ∈ List.range 1, ThresholdAt 18 (116+i) := by decide +kernel

theorem threshold_18_117 : ∀ i ∈ List.range 1, ThresholdAt 18 (117+i) := by decide +kernel

theorem threshold_18_118 : ∀ i ∈ List.range 1, ThresholdAt 18 (118+i) := by decide +kernel

theorem threshold_18_119 : ∀ i ∈ List.range 1, ThresholdAt 18 (119+i) := by decide +kernel

theorem threshold_18_120 : ∀ i ∈ List.range 1, ThresholdAt 18 (120+i) := by decide +kernel

theorem threshold_18_121 : ∀ i ∈ List.range 1, ThresholdAt 18 (121+i) := by decide +kernel

theorem threshold_18_122 : ∀ i ∈ List.range 1, ThresholdAt 18 (122+i) := by decide +kernel

theorem threshold_18_123 : ∀ i ∈ List.range 1, ThresholdAt 18 (123+i) := by decide +kernel

theorem threshold_18_124 : ∀ i ∈ List.range 1, ThresholdAt 18 (124+i) := by decide +kernel

theorem threshold_18_125 : ∀ i ∈ List.range 1, ThresholdAt 18 (125+i) := by decide +kernel

theorem threshold_18_126 : ∀ i ∈ List.range 1, ThresholdAt 18 (126+i) := by decide +kernel

theorem threshold_18_127 : ∀ i ∈ List.range 1, ThresholdAt 18 (127+i) := by decide +kernel

theorem threshold_18_128 : ∀ i ∈ List.range 1, ThresholdAt 18 (128+i) := by decide +kernel

theorem threshold_18_129 : ∀ i ∈ List.range 1, ThresholdAt 18 (129+i) := by decide +kernel

theorem threshold_18_130 : ∀ i ∈ List.range 1, ThresholdAt 18 (130+i) := by decide +kernel

theorem threshold_18_131 : ∀ i ∈ List.range 1, ThresholdAt 18 (131+i) := by decide +kernel

theorem threshold_18_132 : ∀ i ∈ List.range 1, ThresholdAt 18 (132+i) := by decide +kernel

theorem threshold_18_133 : ∀ i ∈ List.range 1, ThresholdAt 18 (133+i) := by decide +kernel

theorem threshold_18_134 : ∀ i ∈ List.range 1, ThresholdAt 18 (134+i) := by decide +kernel

theorem threshold_18_135 : ∀ i ∈ List.range 1, ThresholdAt 18 (135+i) := by decide +kernel

theorem threshold_18_136 : ∀ i ∈ List.range 1, ThresholdAt 18 (136+i) := by decide +kernel

theorem threshold_18_137 : ∀ i ∈ List.range 1, ThresholdAt 18 (137+i) := by decide +kernel

theorem threshold_18_138 : ∀ i ∈ List.range 1, ThresholdAt 18 (138+i) := by decide +kernel

theorem threshold_18 (v : ℕ) (hv : v ∈ List.range 139) : ThresholdAt 18 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 18 v)
  have h := (join 0 69 70 (join 0 34 35 (join 0 17 17 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_18_0 threshold_18_1) (join 2 1 1 threshold_18_2 threshold_18_3)) (join 4 2 2 (join 4 1 1 threshold_18_4 threshold_18_5) (join 6 1 1 threshold_18_6 threshold_18_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_18_8 threshold_18_9) (join 10 1 1 threshold_18_10 threshold_18_11)) (join 12 2 3 (join 12 1 1 threshold_18_12 threshold_18_13) (join 14 1 2 threshold_18_14 (join 15 1 1 threshold_18_15 threshold_18_16))))) (join 17 8 9 (join 17 4 4 (join 17 2 2 (join 17 1 1 threshold_18_17 threshold_18_18) (join 19 1 1 threshold_18_19 threshold_18_20)) (join 21 2 2 (join 21 1 1 threshold_18_21 threshold_18_22) (join 23 1 1 threshold_18_23 threshold_18_24))) (join 25 4 5 (join 25 2 2 (join 25 1 1 threshold_18_25 threshold_18_26) (join 27 1 1 threshold_18_27 threshold_18_28)) (join 29 2 3 (join 29 1 1 threshold_18_29 threshold_18_30) (join 31 1 2 threshold_18_31 (join 32 1 1 threshold_18_32 threshold_18_33)))))) (join 34 17 18 (join 34 8 9 (join 34 4 4 (join 34 2 2 (join 34 1 1 threshold_18_34 threshold_18_35) (join 36 1 1 threshold_18_36 threshold_18_37)) (join 38 2 2 (join 38 1 1 threshold_18_38 threshold_18_39) (join 40 1 1 threshold_18_40 threshold_18_41))) (join 42 4 5 (join 42 2 2 (join 42 1 1 threshold_18_42 threshold_18_43) (join 44 1 1 threshold_18_44 threshold_18_45)) (join 46 2 3 (join 46 1 1 threshold_18_46 threshold_18_47) (join 48 1 2 threshold_18_48 (join 49 1 1 threshold_18_49 threshold_18_50))))) (join 51 9 9 (join 51 4 5 (join 51 2 2 (join 51 1 1 threshold_18_51 threshold_18_52) (join 53 1 1 threshold_18_53 threshold_18_54)) (join 55 2 3 (join 55 1 1 threshold_18_55 threshold_18_56) (join 57 1 2 threshold_18_57 (join 58 1 1 threshold_18_58 threshold_18_59)))) (join 60 4 5 (join 60 2 2 (join 60 1 1 threshold_18_60 threshold_18_61) (join 62 1 1 threshold_18_62 threshold_18_63)) (join 64 2 3 (join 64 1 1 threshold_18_64 threshold_18_65) (join 66 1 2 threshold_18_66 (join 67 1 1 threshold_18_67 threshold_18_68))))))) (join 69 35 35 (join 69 17 18 (join 69 8 9 (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_18_69 threshold_18_70) (join 71 1 1 threshold_18_71 threshold_18_72)) (join 73 2 2 (join 73 1 1 threshold_18_73 threshold_18_74) (join 75 1 1 threshold_18_75 threshold_18_76))) (join 77 4 5 (join 77 2 2 (join 77 1 1 threshold_18_77 threshold_18_78) (join 79 1 1 threshold_18_79 threshold_18_80)) (join 81 2 3 (join 81 1 1 threshold_18_81 threshold_18_82) (join 83 1 2 threshold_18_83 (join 84 1 1 threshold_18_84 threshold_18_85))))) (join 86 9 9 (join 86 4 5 (join 86 2 2 (join 86 1 1 threshold_18_86 threshold_18_87) (join 88 1 1 threshold_18_88 threshold_18_89)) (join 90 2 3 (join 90 1 1 threshold_18_90 threshold_18_91) (join 92 1 2 threshold_18_92 (join 93 1 1 threshold_18_93 threshold_18_94)))) (join 95 4 5 (join 95 2 2 (join 95 1 1 threshold_18_95 threshold_18_96) (join 97 1 1 threshold_18_97 threshold_18_98)) (join 99 2 3 (join 99 1 1 threshold_18_99 threshold_18_100) (join 101 1 2 threshold_18_101 (join 102 1 1 threshold_18_102 threshold_18_103)))))) (join 104 17 18 (join 104 8 9 (join 104 4 4 (join 104 2 2 (join 104 1 1 threshold_18_104 threshold_18_105) (join 106 1 1 threshold_18_106 threshold_18_107)) (join 108 2 2 (join 108 1 1 threshold_18_108 threshold_18_109) (join 110 1 1 threshold_18_110 threshold_18_111))) (join 112 4 5 (join 112 2 2 (join 112 1 1 threshold_18_112 threshold_18_113) (join 114 1 1 threshold_18_114 threshold_18_115)) (join 116 2 3 (join 116 1 1 threshold_18_116 threshold_18_117) (join 118 1 2 threshold_18_118 (join 119 1 1 threshold_18_119 threshold_18_120))))) (join 121 9 9 (join 121 4 5 (join 121 2 2 (join 121 1 1 threshold_18_121 threshold_18_122) (join 123 1 1 threshold_18_123 threshold_18_124)) (join 125 2 3 (join 125 1 1 threshold_18_125 threshold_18_126) (join 127 1 2 threshold_18_127 (join 128 1 1 threshold_18_128 threshold_18_129)))) (join 130 4 5 (join 130 2 2 (join 130 1 1 threshold_18_130 threshold_18_131) (join 132 1 1 threshold_18_132 threshold_18_133)) (join 134 2 3 (join 134 1 1 threshold_18_134 threshold_18_135) (join 136 1 2 threshold_18_136 (join 137 1 1 threshold_18_137 threshold_18_138))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_18_0 : ∀ i ∈ List.range 4, LedgerAt 18 (0+i) := by decide +kernel

theorem ledger_18_4 : ∀ i ∈ List.range 4, LedgerAt 18 (4+i) := by decide +kernel

theorem ledger_18_8 : ∀ i ∈ List.range 4, LedgerAt 18 (8+i) := by decide +kernel

theorem ledger_18_12 : ∀ i ∈ List.range 4, LedgerAt 18 (12+i) := by decide +kernel

theorem ledger_18_16 : ∀ i ∈ List.range 4, LedgerAt 18 (16+i) := by decide +kernel

theorem ledger_18_20 : ∀ i ∈ List.range 4, LedgerAt 18 (20+i) := by decide +kernel

theorem ledger_18_24 : ∀ i ∈ List.range 4, LedgerAt 18 (24+i) := by decide +kernel

theorem ledger_18_28 : ∀ i ∈ List.range 4, LedgerAt 18 (28+i) := by decide +kernel

theorem ledger_18_32 : ∀ i ∈ List.range 4, LedgerAt 18 (32+i) := by decide +kernel

theorem ledger_18_36 : ∀ i ∈ List.range 4, LedgerAt 18 (36+i) := by decide +kernel

theorem ledger_18_40 : ∀ i ∈ List.range 4, LedgerAt 18 (40+i) := by decide +kernel

theorem ledger_18_44 : ∀ i ∈ List.range 4, LedgerAt 18 (44+i) := by decide +kernel

theorem ledger_18_48 : ∀ i ∈ List.range 4, LedgerAt 18 (48+i) := by decide +kernel

theorem ledger_18_52 : ∀ i ∈ List.range 4, LedgerAt 18 (52+i) := by decide +kernel

theorem ledger_18_56 : ∀ i ∈ List.range 4, LedgerAt 18 (56+i) := by decide +kernel

theorem ledger_18_60 : ∀ i ∈ List.range 4, LedgerAt 18 (60+i) := by decide +kernel

theorem ledger_18_64 : ∀ i ∈ List.range 4, LedgerAt 18 (64+i) := by decide +kernel

theorem ledger_18_68 : ∀ i ∈ List.range 4, LedgerAt 18 (68+i) := by decide +kernel

theorem ledger_18_72 : ∀ i ∈ List.range 4, LedgerAt 18 (72+i) := by decide +kernel

theorem ledger_18_76 : ∀ i ∈ List.range 4, LedgerAt 18 (76+i) := by decide +kernel

theorem ledger_18_80 : ∀ i ∈ List.range 4, LedgerAt 18 (80+i) := by decide +kernel

theorem ledger_18_84 : ∀ i ∈ List.range 4, LedgerAt 18 (84+i) := by decide +kernel

theorem ledger_18_88 : ∀ i ∈ List.range 4, LedgerAt 18 (88+i) := by decide +kernel

theorem ledger_18_92 : ∀ i ∈ List.range 4, LedgerAt 18 (92+i) := by decide +kernel

theorem ledger_18_96 : ∀ i ∈ List.range 4, LedgerAt 18 (96+i) := by decide +kernel

theorem ledger_18_100 : ∀ i ∈ List.range 4, LedgerAt 18 (100+i) := by decide +kernel

theorem ledger_18_104 : ∀ i ∈ List.range 4, LedgerAt 18 (104+i) := by decide +kernel

theorem ledger_18_108 : ∀ i ∈ List.range 4, LedgerAt 18 (108+i) := by decide +kernel

theorem ledger_18_112 : ∀ i ∈ List.range 4, LedgerAt 18 (112+i) := by decide +kernel

theorem ledger_18_116 : ∀ i ∈ List.range 4, LedgerAt 18 (116+i) := by decide +kernel

theorem ledger_18_120 : ∀ i ∈ List.range 4, LedgerAt 18 (120+i) := by decide +kernel

theorem ledger_18_124 : ∀ i ∈ List.range 4, LedgerAt 18 (124+i) := by decide +kernel

theorem ledger_18_128 : ∀ i ∈ List.range 4, LedgerAt 18 (128+i) := by decide +kernel

theorem ledger_18_132 : ∀ i ∈ List.range 4, LedgerAt 18 (132+i) := by decide +kernel

theorem ledger_18_136 : ∀ i ∈ List.range 3, LedgerAt 18 (136+i) := by decide +kernel

theorem ledger_18 (v : ℕ) (hv : v ∈ List.range 139) : LedgerAt 18 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 18 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_18_0 ledger_18_4) (join 8 4 4 ledger_18_8 ledger_18_12)) (join 16 8 8 (join 16 4 4 ledger_18_16 ledger_18_20) (join 24 4 4 ledger_18_24 ledger_18_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_18_32 ledger_18_36) (join 40 4 4 ledger_18_40 ledger_18_44)) (join 48 8 12 (join 48 4 4 ledger_18_48 ledger_18_52) (join 56 4 8 ledger_18_56 (join 60 4 4 ledger_18_60 ledger_18_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 ledger_18_68 ledger_18_72) (join 76 4 4 ledger_18_76 ledger_18_80)) (join 84 8 12 (join 84 4 4 ledger_18_84 ledger_18_88) (join 92 4 8 ledger_18_92 (join 96 4 4 ledger_18_96 ledger_18_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 ledger_18_104 ledger_18_108) (join 112 4 4 ledger_18_112 ledger_18_116)) (join 120 8 11 (join 120 4 4 ledger_18_120 ledger_18_124) (join 128 4 7 ledger_18_128 (join 132 4 3 ledger_18_132 ledger_18_136))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
