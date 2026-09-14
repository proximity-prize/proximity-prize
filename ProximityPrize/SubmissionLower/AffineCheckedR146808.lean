import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
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

theorem single_14 (v : ℕ) (hv : v ∈ List.range 136) : SingleAt 14 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 14 v)
  have h := (join 0 68 68 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_14_0 single_14_4) (join 8 4 4 single_14_8 single_14_12)) (join 16 8 8 (join 16 4 4 single_14_16 single_14_20) (join 24 4 4 single_14_24 single_14_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 single_14_32 single_14_36) (join 40 4 4 single_14_40 single_14_44)) (join 48 8 12 (join 48 4 4 single_14_48 single_14_52) (join 56 4 8 single_14_56 (join 60 4 4 single_14_60 single_14_64))))) (join 68 32 36 (join 68 16 16 (join 68 8 8 (join 68 4 4 single_14_68 single_14_72) (join 76 4 4 single_14_76 single_14_80)) (join 84 8 8 (join 84 4 4 single_14_84 single_14_88) (join 92 4 4 single_14_92 single_14_96))) (join 100 16 20 (join 100 8 8 (join 100 4 4 single_14_100 single_14_104) (join 108 4 4 single_14_108 single_14_112)) (join 116 8 12 (join 116 4 4 single_14_116 single_14_120) (join 124 4 8 single_14_124 (join 128 4 4 single_14_128 single_14_132))))))
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

theorem phase_14 (v : ℕ) (hv : v ∈ List.range 136) : PhaseAt 14 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 14 v)
  have h := (join 0 68 68 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_14_0 phase_14_4) (join 8 4 4 phase_14_8 phase_14_12)) (join 16 8 8 (join 16 4 4 phase_14_16 phase_14_20) (join 24 4 4 phase_14_24 phase_14_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_14_32 phase_14_36) (join 40 4 4 phase_14_40 phase_14_44)) (join 48 8 12 (join 48 4 4 phase_14_48 phase_14_52) (join 56 4 8 phase_14_56 (join 60 4 4 phase_14_60 phase_14_64))))) (join 68 32 36 (join 68 16 16 (join 68 8 8 (join 68 4 4 phase_14_68 phase_14_72) (join 76 4 4 phase_14_76 phase_14_80)) (join 84 8 8 (join 84 4 4 phase_14_84 phase_14_88) (join 92 4 4 phase_14_92 phase_14_96))) (join 100 16 20 (join 100 8 8 (join 100 4 4 phase_14_100 phase_14_104) (join 108 4 4 phase_14_108 phase_14_112)) (join 116 8 12 (join 116 4 4 phase_14_116 phase_14_120) (join 124 4 8 phase_14_124 (join 128 4 4 phase_14_128 phase_14_132))))))
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

theorem threshold_14 (v : ℕ) (hv : v ∈ List.range 136) : ThresholdAt 14 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 14 v)
  have h := (join 0 68 68 (join 0 34 34 (join 0 17 17 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_14_0 threshold_14_1) (join 2 1 1 threshold_14_2 threshold_14_3)) (join 4 2 2 (join 4 1 1 threshold_14_4 threshold_14_5) (join 6 1 1 threshold_14_6 threshold_14_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_14_8 threshold_14_9) (join 10 1 1 threshold_14_10 threshold_14_11)) (join 12 2 3 (join 12 1 1 threshold_14_12 threshold_14_13) (join 14 1 2 threshold_14_14 (join 15 1 1 threshold_14_15 threshold_14_16))))) (join 17 8 9 (join 17 4 4 (join 17 2 2 (join 17 1 1 threshold_14_17 threshold_14_18) (join 19 1 1 threshold_14_19 threshold_14_20)) (join 21 2 2 (join 21 1 1 threshold_14_21 threshold_14_22) (join 23 1 1 threshold_14_23 threshold_14_24))) (join 25 4 5 (join 25 2 2 (join 25 1 1 threshold_14_25 threshold_14_26) (join 27 1 1 threshold_14_27 threshold_14_28)) (join 29 2 3 (join 29 1 1 threshold_14_29 threshold_14_30) (join 31 1 2 threshold_14_31 (join 32 1 1 threshold_14_32 threshold_14_33)))))) (join 34 17 17 (join 34 8 9 (join 34 4 4 (join 34 2 2 (join 34 1 1 threshold_14_34 threshold_14_35) (join 36 1 1 threshold_14_36 threshold_14_37)) (join 38 2 2 (join 38 1 1 threshold_14_38 threshold_14_39) (join 40 1 1 threshold_14_40 threshold_14_41))) (join 42 4 5 (join 42 2 2 (join 42 1 1 threshold_14_42 threshold_14_43) (join 44 1 1 threshold_14_44 threshold_14_45)) (join 46 2 3 (join 46 1 1 threshold_14_46 threshold_14_47) (join 48 1 2 threshold_14_48 (join 49 1 1 threshold_14_49 threshold_14_50))))) (join 51 8 9 (join 51 4 4 (join 51 2 2 (join 51 1 1 threshold_14_51 threshold_14_52) (join 53 1 1 threshold_14_53 threshold_14_54)) (join 55 2 2 (join 55 1 1 threshold_14_55 threshold_14_56) (join 57 1 1 threshold_14_57 threshold_14_58))) (join 59 4 5 (join 59 2 2 (join 59 1 1 threshold_14_59 threshold_14_60) (join 61 1 1 threshold_14_61 threshold_14_62)) (join 63 2 3 (join 63 1 1 threshold_14_63 threshold_14_64) (join 65 1 2 threshold_14_65 (join 66 1 1 threshold_14_66 threshold_14_67))))))) (join 68 34 34 (join 68 17 17 (join 68 8 9 (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_14_68 threshold_14_69) (join 70 1 1 threshold_14_70 threshold_14_71)) (join 72 2 2 (join 72 1 1 threshold_14_72 threshold_14_73) (join 74 1 1 threshold_14_74 threshold_14_75))) (join 76 4 5 (join 76 2 2 (join 76 1 1 threshold_14_76 threshold_14_77) (join 78 1 1 threshold_14_78 threshold_14_79)) (join 80 2 3 (join 80 1 1 threshold_14_80 threshold_14_81) (join 82 1 2 threshold_14_82 (join 83 1 1 threshold_14_83 threshold_14_84))))) (join 85 8 9 (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_14_85 threshold_14_86) (join 87 1 1 threshold_14_87 threshold_14_88)) (join 89 2 2 (join 89 1 1 threshold_14_89 threshold_14_90) (join 91 1 1 threshold_14_91 threshold_14_92))) (join 93 4 5 (join 93 2 2 (join 93 1 1 threshold_14_93 threshold_14_94) (join 95 1 1 threshold_14_95 threshold_14_96)) (join 97 2 3 (join 97 1 1 threshold_14_97 threshold_14_98) (join 99 1 2 threshold_14_99 (join 100 1 1 threshold_14_100 threshold_14_101)))))) (join 102 17 17 (join 102 8 9 (join 102 4 4 (join 102 2 2 (join 102 1 1 threshold_14_102 threshold_14_103) (join 104 1 1 threshold_14_104 threshold_14_105)) (join 106 2 2 (join 106 1 1 threshold_14_106 threshold_14_107) (join 108 1 1 threshold_14_108 threshold_14_109))) (join 110 4 5 (join 110 2 2 (join 110 1 1 threshold_14_110 threshold_14_111) (join 112 1 1 threshold_14_112 threshold_14_113)) (join 114 2 3 (join 114 1 1 threshold_14_114 threshold_14_115) (join 116 1 2 threshold_14_116 (join 117 1 1 threshold_14_117 threshold_14_118))))) (join 119 8 9 (join 119 4 4 (join 119 2 2 (join 119 1 1 threshold_14_119 threshold_14_120) (join 121 1 1 threshold_14_121 threshold_14_122)) (join 123 2 2 (join 123 1 1 threshold_14_123 threshold_14_124) (join 125 1 1 threshold_14_125 threshold_14_126))) (join 127 4 5 (join 127 2 2 (join 127 1 1 threshold_14_127 threshold_14_128) (join 129 1 1 threshold_14_129 threshold_14_130)) (join 131 2 3 (join 131 1 1 threshold_14_131 threshold_14_132) (join 133 1 2 threshold_14_133 (join 134 1 1 threshold_14_134 threshold_14_135))))))))
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

theorem ledger_14 (v : ℕ) (hv : v ∈ List.range 136) : LedgerAt 14 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 14 v)
  have h := (join 0 68 68 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_14_0 ledger_14_4) (join 8 4 4 ledger_14_8 ledger_14_12)) (join 16 8 8 (join 16 4 4 ledger_14_16 ledger_14_20) (join 24 4 4 ledger_14_24 ledger_14_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_14_32 ledger_14_36) (join 40 4 4 ledger_14_40 ledger_14_44)) (join 48 8 12 (join 48 4 4 ledger_14_48 ledger_14_52) (join 56 4 8 ledger_14_56 (join 60 4 4 ledger_14_60 ledger_14_64))))) (join 68 32 36 (join 68 16 16 (join 68 8 8 (join 68 4 4 ledger_14_68 ledger_14_72) (join 76 4 4 ledger_14_76 ledger_14_80)) (join 84 8 8 (join 84 4 4 ledger_14_84 ledger_14_88) (join 92 4 4 ledger_14_92 ledger_14_96))) (join 100 16 20 (join 100 8 8 (join 100 4 4 ledger_14_100 ledger_14_104) (join 108 4 4 ledger_14_108 ledger_14_112)) (join 116 8 12 (join 116 4 4 ledger_14_116 ledger_14_120) (join 124 4 8 ledger_14_124 (join 128 4 4 ledger_14_128 ledger_14_132))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
