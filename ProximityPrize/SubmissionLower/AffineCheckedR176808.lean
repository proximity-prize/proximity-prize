import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_17_0 : ∀ i ∈ List.range 4, SingleAt 17 (0+i) := by decide +kernel

theorem single_17_4 : ∀ i ∈ List.range 4, SingleAt 17 (4+i) := by decide +kernel

theorem single_17_8 : ∀ i ∈ List.range 4, SingleAt 17 (8+i) := by decide +kernel

theorem single_17_12 : ∀ i ∈ List.range 4, SingleAt 17 (12+i) := by decide +kernel

theorem single_17_16 : ∀ i ∈ List.range 4, SingleAt 17 (16+i) := by decide +kernel

theorem single_17_20 : ∀ i ∈ List.range 4, SingleAt 17 (20+i) := by decide +kernel

theorem single_17_24 : ∀ i ∈ List.range 4, SingleAt 17 (24+i) := by decide +kernel

theorem single_17_28 : ∀ i ∈ List.range 4, SingleAt 17 (28+i) := by decide +kernel

theorem single_17_32 : ∀ i ∈ List.range 4, SingleAt 17 (32+i) := by decide +kernel

theorem single_17_36 : ∀ i ∈ List.range 4, SingleAt 17 (36+i) := by decide +kernel

theorem single_17_40 : ∀ i ∈ List.range 4, SingleAt 17 (40+i) := by decide +kernel

theorem single_17_44 : ∀ i ∈ List.range 4, SingleAt 17 (44+i) := by decide +kernel

theorem single_17_48 : ∀ i ∈ List.range 4, SingleAt 17 (48+i) := by decide +kernel

theorem single_17_52 : ∀ i ∈ List.range 4, SingleAt 17 (52+i) := by decide +kernel

theorem single_17_56 : ∀ i ∈ List.range 4, SingleAt 17 (56+i) := by decide +kernel

theorem single_17_60 : ∀ i ∈ List.range 4, SingleAt 17 (60+i) := by decide +kernel

theorem single_17_64 : ∀ i ∈ List.range 4, SingleAt 17 (64+i) := by decide +kernel

theorem single_17_68 : ∀ i ∈ List.range 4, SingleAt 17 (68+i) := by decide +kernel

theorem single_17_72 : ∀ i ∈ List.range 4, SingleAt 17 (72+i) := by decide +kernel

theorem single_17_76 : ∀ i ∈ List.range 4, SingleAt 17 (76+i) := by decide +kernel

theorem single_17_80 : ∀ i ∈ List.range 4, SingleAt 17 (80+i) := by decide +kernel

theorem single_17_84 : ∀ i ∈ List.range 4, SingleAt 17 (84+i) := by decide +kernel

theorem single_17_88 : ∀ i ∈ List.range 4, SingleAt 17 (88+i) := by decide +kernel

theorem single_17_92 : ∀ i ∈ List.range 4, SingleAt 17 (92+i) := by decide +kernel

theorem single_17_96 : ∀ i ∈ List.range 4, SingleAt 17 (96+i) := by decide +kernel

theorem single_17_100 : ∀ i ∈ List.range 4, SingleAt 17 (100+i) := by decide +kernel

theorem single_17_104 : ∀ i ∈ List.range 4, SingleAt 17 (104+i) := by decide +kernel

theorem single_17_108 : ∀ i ∈ List.range 4, SingleAt 17 (108+i) := by decide +kernel

theorem single_17_112 : ∀ i ∈ List.range 4, SingleAt 17 (112+i) := by decide +kernel

theorem single_17_116 : ∀ i ∈ List.range 4, SingleAt 17 (116+i) := by decide +kernel

theorem single_17_120 : ∀ i ∈ List.range 4, SingleAt 17 (120+i) := by decide +kernel

theorem single_17_124 : ∀ i ∈ List.range 4, SingleAt 17 (124+i) := by decide +kernel

theorem single_17_128 : ∀ i ∈ List.range 4, SingleAt 17 (128+i) := by decide +kernel

theorem single_17_132 : ∀ i ∈ List.range 1, SingleAt 17 (132+i) := by decide +kernel

theorem single_17 (v : ℕ) (hv : v ∈ List.range 133) : SingleAt 17 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 17 v)
  have h := (join 0 68 65 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_17_0 single_17_4) (join 8 4 4 single_17_8 single_17_12)) (join 16 8 8 (join 16 4 4 single_17_16 single_17_20) (join 24 4 4 single_17_24 single_17_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 single_17_32 single_17_36) (join 40 4 4 single_17_40 single_17_44)) (join 48 8 12 (join 48 4 4 single_17_48 single_17_52) (join 56 4 8 single_17_56 (join 60 4 4 single_17_60 single_17_64))))) (join 68 32 33 (join 68 16 16 (join 68 8 8 (join 68 4 4 single_17_68 single_17_72) (join 76 4 4 single_17_76 single_17_80)) (join 84 8 8 (join 84 4 4 single_17_84 single_17_88) (join 92 4 4 single_17_92 single_17_96))) (join 100 16 17 (join 100 8 8 (join 100 4 4 single_17_100 single_17_104) (join 108 4 4 single_17_108 single_17_112)) (join 116 8 9 (join 116 4 4 single_17_116 single_17_120) (join 124 4 5 single_17_124 (join 128 4 1 single_17_128 single_17_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_17_0 : ∀ i ∈ List.range 4, PhaseAt 17 (0+i) := by decide +kernel

theorem phase_17_4 : ∀ i ∈ List.range 4, PhaseAt 17 (4+i) := by decide +kernel

theorem phase_17_8 : ∀ i ∈ List.range 4, PhaseAt 17 (8+i) := by decide +kernel

theorem phase_17_12 : ∀ i ∈ List.range 4, PhaseAt 17 (12+i) := by decide +kernel

theorem phase_17_16 : ∀ i ∈ List.range 4, PhaseAt 17 (16+i) := by decide +kernel

theorem phase_17_20 : ∀ i ∈ List.range 4, PhaseAt 17 (20+i) := by decide +kernel

theorem phase_17_24 : ∀ i ∈ List.range 4, PhaseAt 17 (24+i) := by decide +kernel

theorem phase_17_28 : ∀ i ∈ List.range 4, PhaseAt 17 (28+i) := by decide +kernel

theorem phase_17_32 : ∀ i ∈ List.range 4, PhaseAt 17 (32+i) := by decide +kernel

theorem phase_17_36 : ∀ i ∈ List.range 4, PhaseAt 17 (36+i) := by decide +kernel

theorem phase_17_40 : ∀ i ∈ List.range 4, PhaseAt 17 (40+i) := by decide +kernel

theorem phase_17_44 : ∀ i ∈ List.range 4, PhaseAt 17 (44+i) := by decide +kernel

theorem phase_17_48 : ∀ i ∈ List.range 4, PhaseAt 17 (48+i) := by decide +kernel

theorem phase_17_52 : ∀ i ∈ List.range 4, PhaseAt 17 (52+i) := by decide +kernel

theorem phase_17_56 : ∀ i ∈ List.range 4, PhaseAt 17 (56+i) := by decide +kernel

theorem phase_17_60 : ∀ i ∈ List.range 4, PhaseAt 17 (60+i) := by decide +kernel

theorem phase_17_64 : ∀ i ∈ List.range 4, PhaseAt 17 (64+i) := by decide +kernel

theorem phase_17_68 : ∀ i ∈ List.range 4, PhaseAt 17 (68+i) := by decide +kernel

theorem phase_17_72 : ∀ i ∈ List.range 4, PhaseAt 17 (72+i) := by decide +kernel

theorem phase_17_76 : ∀ i ∈ List.range 4, PhaseAt 17 (76+i) := by decide +kernel

theorem phase_17_80 : ∀ i ∈ List.range 4, PhaseAt 17 (80+i) := by decide +kernel

theorem phase_17_84 : ∀ i ∈ List.range 4, PhaseAt 17 (84+i) := by decide +kernel

theorem phase_17_88 : ∀ i ∈ List.range 4, PhaseAt 17 (88+i) := by decide +kernel

theorem phase_17_92 : ∀ i ∈ List.range 4, PhaseAt 17 (92+i) := by decide +kernel

theorem phase_17_96 : ∀ i ∈ List.range 4, PhaseAt 17 (96+i) := by decide +kernel

theorem phase_17_100 : ∀ i ∈ List.range 4, PhaseAt 17 (100+i) := by decide +kernel

theorem phase_17_104 : ∀ i ∈ List.range 4, PhaseAt 17 (104+i) := by decide +kernel

theorem phase_17_108 : ∀ i ∈ List.range 4, PhaseAt 17 (108+i) := by decide +kernel

theorem phase_17_112 : ∀ i ∈ List.range 4, PhaseAt 17 (112+i) := by decide +kernel

theorem phase_17_116 : ∀ i ∈ List.range 4, PhaseAt 17 (116+i) := by decide +kernel

theorem phase_17_120 : ∀ i ∈ List.range 4, PhaseAt 17 (120+i) := by decide +kernel

theorem phase_17_124 : ∀ i ∈ List.range 4, PhaseAt 17 (124+i) := by decide +kernel

theorem phase_17_128 : ∀ i ∈ List.range 4, PhaseAt 17 (128+i) := by decide +kernel

theorem phase_17_132 : ∀ i ∈ List.range 1, PhaseAt 17 (132+i) := by decide +kernel

theorem phase_17 (v : ℕ) (hv : v ∈ List.range 133) : PhaseAt 17 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 17 v)
  have h := (join 0 68 65 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_17_0 phase_17_4) (join 8 4 4 phase_17_8 phase_17_12)) (join 16 8 8 (join 16 4 4 phase_17_16 phase_17_20) (join 24 4 4 phase_17_24 phase_17_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_17_32 phase_17_36) (join 40 4 4 phase_17_40 phase_17_44)) (join 48 8 12 (join 48 4 4 phase_17_48 phase_17_52) (join 56 4 8 phase_17_56 (join 60 4 4 phase_17_60 phase_17_64))))) (join 68 32 33 (join 68 16 16 (join 68 8 8 (join 68 4 4 phase_17_68 phase_17_72) (join 76 4 4 phase_17_76 phase_17_80)) (join 84 8 8 (join 84 4 4 phase_17_84 phase_17_88) (join 92 4 4 phase_17_92 phase_17_96))) (join 100 16 17 (join 100 8 8 (join 100 4 4 phase_17_100 phase_17_104) (join 108 4 4 phase_17_108 phase_17_112)) (join 116 8 9 (join 116 4 4 phase_17_116 phase_17_120) (join 124 4 5 phase_17_124 (join 128 4 1 phase_17_128 phase_17_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_17_0 : ∀ i ∈ List.range 1, ThresholdAt 17 (0+i) := by decide +kernel

theorem threshold_17_1 : ∀ i ∈ List.range 1, ThresholdAt 17 (1+i) := by decide +kernel

theorem threshold_17_2 : ∀ i ∈ List.range 1, ThresholdAt 17 (2+i) := by decide +kernel

theorem threshold_17_3 : ∀ i ∈ List.range 1, ThresholdAt 17 (3+i) := by decide +kernel

theorem threshold_17_4 : ∀ i ∈ List.range 1, ThresholdAt 17 (4+i) := by decide +kernel

theorem threshold_17_5 : ∀ i ∈ List.range 1, ThresholdAt 17 (5+i) := by decide +kernel

theorem threshold_17_6 : ∀ i ∈ List.range 1, ThresholdAt 17 (6+i) := by decide +kernel

theorem threshold_17_7 : ∀ i ∈ List.range 1, ThresholdAt 17 (7+i) := by decide +kernel

theorem threshold_17_8 : ∀ i ∈ List.range 1, ThresholdAt 17 (8+i) := by decide +kernel

theorem threshold_17_9 : ∀ i ∈ List.range 1, ThresholdAt 17 (9+i) := by decide +kernel

theorem threshold_17_10 : ∀ i ∈ List.range 1, ThresholdAt 17 (10+i) := by decide +kernel

theorem threshold_17_11 : ∀ i ∈ List.range 1, ThresholdAt 17 (11+i) := by decide +kernel

theorem threshold_17_12 : ∀ i ∈ List.range 1, ThresholdAt 17 (12+i) := by decide +kernel

theorem threshold_17_13 : ∀ i ∈ List.range 1, ThresholdAt 17 (13+i) := by decide +kernel

theorem threshold_17_14 : ∀ i ∈ List.range 1, ThresholdAt 17 (14+i) := by decide +kernel

theorem threshold_17_15 : ∀ i ∈ List.range 1, ThresholdAt 17 (15+i) := by decide +kernel

theorem threshold_17_16 : ∀ i ∈ List.range 1, ThresholdAt 17 (16+i) := by decide +kernel

theorem threshold_17_17 : ∀ i ∈ List.range 1, ThresholdAt 17 (17+i) := by decide +kernel

theorem threshold_17_18 : ∀ i ∈ List.range 1, ThresholdAt 17 (18+i) := by decide +kernel

theorem threshold_17_19 : ∀ i ∈ List.range 1, ThresholdAt 17 (19+i) := by decide +kernel

theorem threshold_17_20 : ∀ i ∈ List.range 1, ThresholdAt 17 (20+i) := by decide +kernel

theorem threshold_17_21 : ∀ i ∈ List.range 1, ThresholdAt 17 (21+i) := by decide +kernel

theorem threshold_17_22 : ∀ i ∈ List.range 1, ThresholdAt 17 (22+i) := by decide +kernel

theorem threshold_17_23 : ∀ i ∈ List.range 1, ThresholdAt 17 (23+i) := by decide +kernel

theorem threshold_17_24 : ∀ i ∈ List.range 1, ThresholdAt 17 (24+i) := by decide +kernel

theorem threshold_17_25 : ∀ i ∈ List.range 1, ThresholdAt 17 (25+i) := by decide +kernel

theorem threshold_17_26 : ∀ i ∈ List.range 1, ThresholdAt 17 (26+i) := by decide +kernel

theorem threshold_17_27 : ∀ i ∈ List.range 1, ThresholdAt 17 (27+i) := by decide +kernel

theorem threshold_17_28 : ∀ i ∈ List.range 1, ThresholdAt 17 (28+i) := by decide +kernel

theorem threshold_17_29 : ∀ i ∈ List.range 1, ThresholdAt 17 (29+i) := by decide +kernel

theorem threshold_17_30 : ∀ i ∈ List.range 1, ThresholdAt 17 (30+i) := by decide +kernel

theorem threshold_17_31 : ∀ i ∈ List.range 1, ThresholdAt 17 (31+i) := by decide +kernel

theorem threshold_17_32 : ∀ i ∈ List.range 1, ThresholdAt 17 (32+i) := by decide +kernel

theorem threshold_17_33 : ∀ i ∈ List.range 1, ThresholdAt 17 (33+i) := by decide +kernel

theorem threshold_17_34 : ∀ i ∈ List.range 1, ThresholdAt 17 (34+i) := by decide +kernel

theorem threshold_17_35 : ∀ i ∈ List.range 1, ThresholdAt 17 (35+i) := by decide +kernel

theorem threshold_17_36 : ∀ i ∈ List.range 1, ThresholdAt 17 (36+i) := by decide +kernel

theorem threshold_17_37 : ∀ i ∈ List.range 1, ThresholdAt 17 (37+i) := by decide +kernel

theorem threshold_17_38 : ∀ i ∈ List.range 1, ThresholdAt 17 (38+i) := by decide +kernel

theorem threshold_17_39 : ∀ i ∈ List.range 1, ThresholdAt 17 (39+i) := by decide +kernel

theorem threshold_17_40 : ∀ i ∈ List.range 1, ThresholdAt 17 (40+i) := by decide +kernel

theorem threshold_17_41 : ∀ i ∈ List.range 1, ThresholdAt 17 (41+i) := by decide +kernel

theorem threshold_17_42 : ∀ i ∈ List.range 1, ThresholdAt 17 (42+i) := by decide +kernel

theorem threshold_17_43 : ∀ i ∈ List.range 1, ThresholdAt 17 (43+i) := by decide +kernel

theorem threshold_17_44 : ∀ i ∈ List.range 1, ThresholdAt 17 (44+i) := by decide +kernel

theorem threshold_17_45 : ∀ i ∈ List.range 1, ThresholdAt 17 (45+i) := by decide +kernel

theorem threshold_17_46 : ∀ i ∈ List.range 1, ThresholdAt 17 (46+i) := by decide +kernel

theorem threshold_17_47 : ∀ i ∈ List.range 1, ThresholdAt 17 (47+i) := by decide +kernel

theorem threshold_17_48 : ∀ i ∈ List.range 1, ThresholdAt 17 (48+i) := by decide +kernel

theorem threshold_17_49 : ∀ i ∈ List.range 1, ThresholdAt 17 (49+i) := by decide +kernel

theorem threshold_17_50 : ∀ i ∈ List.range 1, ThresholdAt 17 (50+i) := by decide +kernel

theorem threshold_17_51 : ∀ i ∈ List.range 1, ThresholdAt 17 (51+i) := by decide +kernel

theorem threshold_17_52 : ∀ i ∈ List.range 1, ThresholdAt 17 (52+i) := by decide +kernel

theorem threshold_17_53 : ∀ i ∈ List.range 1, ThresholdAt 17 (53+i) := by decide +kernel

theorem threshold_17_54 : ∀ i ∈ List.range 1, ThresholdAt 17 (54+i) := by decide +kernel

theorem threshold_17_55 : ∀ i ∈ List.range 1, ThresholdAt 17 (55+i) := by decide +kernel

theorem threshold_17_56 : ∀ i ∈ List.range 1, ThresholdAt 17 (56+i) := by decide +kernel

theorem threshold_17_57 : ∀ i ∈ List.range 1, ThresholdAt 17 (57+i) := by decide +kernel

theorem threshold_17_58 : ∀ i ∈ List.range 1, ThresholdAt 17 (58+i) := by decide +kernel

theorem threshold_17_59 : ∀ i ∈ List.range 1, ThresholdAt 17 (59+i) := by decide +kernel

theorem threshold_17_60 : ∀ i ∈ List.range 1, ThresholdAt 17 (60+i) := by decide +kernel

theorem threshold_17_61 : ∀ i ∈ List.range 1, ThresholdAt 17 (61+i) := by decide +kernel

theorem threshold_17_62 : ∀ i ∈ List.range 1, ThresholdAt 17 (62+i) := by decide +kernel

theorem threshold_17_63 : ∀ i ∈ List.range 1, ThresholdAt 17 (63+i) := by decide +kernel

theorem threshold_17_64 : ∀ i ∈ List.range 1, ThresholdAt 17 (64+i) := by decide +kernel

theorem threshold_17_65 : ∀ i ∈ List.range 1, ThresholdAt 17 (65+i) := by decide +kernel

theorem threshold_17_66 : ∀ i ∈ List.range 1, ThresholdAt 17 (66+i) := by decide +kernel

theorem threshold_17_67 : ∀ i ∈ List.range 1, ThresholdAt 17 (67+i) := by decide +kernel

theorem threshold_17_68 : ∀ i ∈ List.range 1, ThresholdAt 17 (68+i) := by decide +kernel

theorem threshold_17_69 : ∀ i ∈ List.range 1, ThresholdAt 17 (69+i) := by decide +kernel

theorem threshold_17_70 : ∀ i ∈ List.range 1, ThresholdAt 17 (70+i) := by decide +kernel

theorem threshold_17_71 : ∀ i ∈ List.range 1, ThresholdAt 17 (71+i) := by decide +kernel

theorem threshold_17_72 : ∀ i ∈ List.range 1, ThresholdAt 17 (72+i) := by decide +kernel

theorem threshold_17_73 : ∀ i ∈ List.range 1, ThresholdAt 17 (73+i) := by decide +kernel

theorem threshold_17_74 : ∀ i ∈ List.range 1, ThresholdAt 17 (74+i) := by decide +kernel

theorem threshold_17_75 : ∀ i ∈ List.range 1, ThresholdAt 17 (75+i) := by decide +kernel

theorem threshold_17_76 : ∀ i ∈ List.range 1, ThresholdAt 17 (76+i) := by decide +kernel

theorem threshold_17_77 : ∀ i ∈ List.range 1, ThresholdAt 17 (77+i) := by decide +kernel

theorem threshold_17_78 : ∀ i ∈ List.range 1, ThresholdAt 17 (78+i) := by decide +kernel

theorem threshold_17_79 : ∀ i ∈ List.range 1, ThresholdAt 17 (79+i) := by decide +kernel

theorem threshold_17_80 : ∀ i ∈ List.range 1, ThresholdAt 17 (80+i) := by decide +kernel

theorem threshold_17_81 : ∀ i ∈ List.range 1, ThresholdAt 17 (81+i) := by decide +kernel

theorem threshold_17_82 : ∀ i ∈ List.range 1, ThresholdAt 17 (82+i) := by decide +kernel

theorem threshold_17_83 : ∀ i ∈ List.range 1, ThresholdAt 17 (83+i) := by decide +kernel

theorem threshold_17_84 : ∀ i ∈ List.range 1, ThresholdAt 17 (84+i) := by decide +kernel

theorem threshold_17_85 : ∀ i ∈ List.range 1, ThresholdAt 17 (85+i) := by decide +kernel

theorem threshold_17_86 : ∀ i ∈ List.range 1, ThresholdAt 17 (86+i) := by decide +kernel

theorem threshold_17_87 : ∀ i ∈ List.range 1, ThresholdAt 17 (87+i) := by decide +kernel

theorem threshold_17_88 : ∀ i ∈ List.range 1, ThresholdAt 17 (88+i) := by decide +kernel

theorem threshold_17_89 : ∀ i ∈ List.range 1, ThresholdAt 17 (89+i) := by decide +kernel

theorem threshold_17_90 : ∀ i ∈ List.range 1, ThresholdAt 17 (90+i) := by decide +kernel

theorem threshold_17_91 : ∀ i ∈ List.range 1, ThresholdAt 17 (91+i) := by decide +kernel

theorem threshold_17_92 : ∀ i ∈ List.range 1, ThresholdAt 17 (92+i) := by decide +kernel

theorem threshold_17_93 : ∀ i ∈ List.range 1, ThresholdAt 17 (93+i) := by decide +kernel

theorem threshold_17_94 : ∀ i ∈ List.range 1, ThresholdAt 17 (94+i) := by decide +kernel

theorem threshold_17_95 : ∀ i ∈ List.range 1, ThresholdAt 17 (95+i) := by decide +kernel

theorem threshold_17_96 : ∀ i ∈ List.range 1, ThresholdAt 17 (96+i) := by decide +kernel

theorem threshold_17_97 : ∀ i ∈ List.range 1, ThresholdAt 17 (97+i) := by decide +kernel

theorem threshold_17_98 : ∀ i ∈ List.range 1, ThresholdAt 17 (98+i) := by decide +kernel

theorem threshold_17_99 : ∀ i ∈ List.range 1, ThresholdAt 17 (99+i) := by decide +kernel

theorem threshold_17_100 : ∀ i ∈ List.range 1, ThresholdAt 17 (100+i) := by decide +kernel

theorem threshold_17_101 : ∀ i ∈ List.range 1, ThresholdAt 17 (101+i) := by decide +kernel

theorem threshold_17_102 : ∀ i ∈ List.range 1, ThresholdAt 17 (102+i) := by decide +kernel

theorem threshold_17_103 : ∀ i ∈ List.range 1, ThresholdAt 17 (103+i) := by decide +kernel

theorem threshold_17_104 : ∀ i ∈ List.range 1, ThresholdAt 17 (104+i) := by decide +kernel

theorem threshold_17_105 : ∀ i ∈ List.range 1, ThresholdAt 17 (105+i) := by decide +kernel

theorem threshold_17_106 : ∀ i ∈ List.range 1, ThresholdAt 17 (106+i) := by decide +kernel

theorem threshold_17_107 : ∀ i ∈ List.range 1, ThresholdAt 17 (107+i) := by decide +kernel

theorem threshold_17_108 : ∀ i ∈ List.range 1, ThresholdAt 17 (108+i) := by decide +kernel

theorem threshold_17_109 : ∀ i ∈ List.range 1, ThresholdAt 17 (109+i) := by decide +kernel

theorem threshold_17_110 : ∀ i ∈ List.range 1, ThresholdAt 17 (110+i) := by decide +kernel

theorem threshold_17_111 : ∀ i ∈ List.range 1, ThresholdAt 17 (111+i) := by decide +kernel

theorem threshold_17_112 : ∀ i ∈ List.range 1, ThresholdAt 17 (112+i) := by decide +kernel

theorem threshold_17_113 : ∀ i ∈ List.range 1, ThresholdAt 17 (113+i) := by decide +kernel

theorem threshold_17_114 : ∀ i ∈ List.range 1, ThresholdAt 17 (114+i) := by decide +kernel

theorem threshold_17_115 : ∀ i ∈ List.range 1, ThresholdAt 17 (115+i) := by decide +kernel

theorem threshold_17_116 : ∀ i ∈ List.range 1, ThresholdAt 17 (116+i) := by decide +kernel

theorem threshold_17_117 : ∀ i ∈ List.range 1, ThresholdAt 17 (117+i) := by decide +kernel

theorem threshold_17_118 : ∀ i ∈ List.range 1, ThresholdAt 17 (118+i) := by decide +kernel

theorem threshold_17_119 : ∀ i ∈ List.range 1, ThresholdAt 17 (119+i) := by decide +kernel

theorem threshold_17_120 : ∀ i ∈ List.range 1, ThresholdAt 17 (120+i) := by decide +kernel

theorem threshold_17_121 : ∀ i ∈ List.range 1, ThresholdAt 17 (121+i) := by decide +kernel

theorem threshold_17_122 : ∀ i ∈ List.range 1, ThresholdAt 17 (122+i) := by decide +kernel

theorem threshold_17_123 : ∀ i ∈ List.range 1, ThresholdAt 17 (123+i) := by decide +kernel

theorem threshold_17_124 : ∀ i ∈ List.range 1, ThresholdAt 17 (124+i) := by decide +kernel

theorem threshold_17_125 : ∀ i ∈ List.range 1, ThresholdAt 17 (125+i) := by decide +kernel

theorem threshold_17_126 : ∀ i ∈ List.range 1, ThresholdAt 17 (126+i) := by decide +kernel

theorem threshold_17_127 : ∀ i ∈ List.range 1, ThresholdAt 17 (127+i) := by decide +kernel

theorem threshold_17_128 : ∀ i ∈ List.range 1, ThresholdAt 17 (128+i) := by decide +kernel

theorem threshold_17_129 : ∀ i ∈ List.range 1, ThresholdAt 17 (129+i) := by decide +kernel

theorem threshold_17_130 : ∀ i ∈ List.range 1, ThresholdAt 17 (130+i) := by decide +kernel

theorem threshold_17_131 : ∀ i ∈ List.range 1, ThresholdAt 17 (131+i) := by decide +kernel

theorem threshold_17_132 : ∀ i ∈ List.range 1, ThresholdAt 17 (132+i) := by decide +kernel

theorem threshold_17 (v : ℕ) (hv : v ∈ List.range 133) : ThresholdAt 17 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 17 v)
  have h := (join 0 66 67 (join 0 33 33 (join 0 16 17 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_17_0 threshold_17_1) (join 2 1 1 threshold_17_2 threshold_17_3)) (join 4 2 2 (join 4 1 1 threshold_17_4 threshold_17_5) (join 6 1 1 threshold_17_6 threshold_17_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_17_8 threshold_17_9) (join 10 1 1 threshold_17_10 threshold_17_11)) (join 12 2 2 (join 12 1 1 threshold_17_12 threshold_17_13) (join 14 1 1 threshold_17_14 threshold_17_15)))) (join 16 8 9 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_17_16 threshold_17_17) (join 18 1 1 threshold_17_18 threshold_17_19)) (join 20 2 2 (join 20 1 1 threshold_17_20 threshold_17_21) (join 22 1 1 threshold_17_22 threshold_17_23))) (join 24 4 5 (join 24 2 2 (join 24 1 1 threshold_17_24 threshold_17_25) (join 26 1 1 threshold_17_26 threshold_17_27)) (join 28 2 3 (join 28 1 1 threshold_17_28 threshold_17_29) (join 30 1 2 threshold_17_30 (join 31 1 1 threshold_17_31 threshold_17_32)))))) (join 33 16 17 (join 33 8 8 (join 33 4 4 (join 33 2 2 (join 33 1 1 threshold_17_33 threshold_17_34) (join 35 1 1 threshold_17_35 threshold_17_36)) (join 37 2 2 (join 37 1 1 threshold_17_37 threshold_17_38) (join 39 1 1 threshold_17_39 threshold_17_40))) (join 41 4 4 (join 41 2 2 (join 41 1 1 threshold_17_41 threshold_17_42) (join 43 1 1 threshold_17_43 threshold_17_44)) (join 45 2 2 (join 45 1 1 threshold_17_45 threshold_17_46) (join 47 1 1 threshold_17_47 threshold_17_48)))) (join 49 8 9 (join 49 4 4 (join 49 2 2 (join 49 1 1 threshold_17_49 threshold_17_50) (join 51 1 1 threshold_17_51 threshold_17_52)) (join 53 2 2 (join 53 1 1 threshold_17_53 threshold_17_54) (join 55 1 1 threshold_17_55 threshold_17_56))) (join 57 4 5 (join 57 2 2 (join 57 1 1 threshold_17_57 threshold_17_58) (join 59 1 1 threshold_17_59 threshold_17_60)) (join 61 2 3 (join 61 1 1 threshold_17_61 threshold_17_62) (join 63 1 2 threshold_17_63 (join 64 1 1 threshold_17_64 threshold_17_65))))))) (join 66 33 34 (join 66 16 17 (join 66 8 8 (join 66 4 4 (join 66 2 2 (join 66 1 1 threshold_17_66 threshold_17_67) (join 68 1 1 threshold_17_68 threshold_17_69)) (join 70 2 2 (join 70 1 1 threshold_17_70 threshold_17_71) (join 72 1 1 threshold_17_72 threshold_17_73))) (join 74 4 4 (join 74 2 2 (join 74 1 1 threshold_17_74 threshold_17_75) (join 76 1 1 threshold_17_76 threshold_17_77)) (join 78 2 2 (join 78 1 1 threshold_17_78 threshold_17_79) (join 80 1 1 threshold_17_80 threshold_17_81)))) (join 82 8 9 (join 82 4 4 (join 82 2 2 (join 82 1 1 threshold_17_82 threshold_17_83) (join 84 1 1 threshold_17_84 threshold_17_85)) (join 86 2 2 (join 86 1 1 threshold_17_86 threshold_17_87) (join 88 1 1 threshold_17_88 threshold_17_89))) (join 90 4 5 (join 90 2 2 (join 90 1 1 threshold_17_90 threshold_17_91) (join 92 1 1 threshold_17_92 threshold_17_93)) (join 94 2 3 (join 94 1 1 threshold_17_94 threshold_17_95) (join 96 1 2 threshold_17_96 (join 97 1 1 threshold_17_97 threshold_17_98)))))) (join 99 17 17 (join 99 8 9 (join 99 4 4 (join 99 2 2 (join 99 1 1 threshold_17_99 threshold_17_100) (join 101 1 1 threshold_17_101 threshold_17_102)) (join 103 2 2 (join 103 1 1 threshold_17_103 threshold_17_104) (join 105 1 1 threshold_17_105 threshold_17_106))) (join 107 4 5 (join 107 2 2 (join 107 1 1 threshold_17_107 threshold_17_108) (join 109 1 1 threshold_17_109 threshold_17_110)) (join 111 2 3 (join 111 1 1 threshold_17_111 threshold_17_112) (join 113 1 2 threshold_17_113 (join 114 1 1 threshold_17_114 threshold_17_115))))) (join 116 8 9 (join 116 4 4 (join 116 2 2 (join 116 1 1 threshold_17_116 threshold_17_117) (join 118 1 1 threshold_17_118 threshold_17_119)) (join 120 2 2 (join 120 1 1 threshold_17_120 threshold_17_121) (join 122 1 1 threshold_17_122 threshold_17_123))) (join 124 4 5 (join 124 2 2 (join 124 1 1 threshold_17_124 threshold_17_125) (join 126 1 1 threshold_17_126 threshold_17_127)) (join 128 2 3 (join 128 1 1 threshold_17_128 threshold_17_129) (join 130 1 2 threshold_17_130 (join 131 1 1 threshold_17_131 threshold_17_132))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_17_0 : ∀ i ∈ List.range 4, LedgerAt 17 (0+i) := by decide +kernel

theorem ledger_17_4 : ∀ i ∈ List.range 4, LedgerAt 17 (4+i) := by decide +kernel

theorem ledger_17_8 : ∀ i ∈ List.range 4, LedgerAt 17 (8+i) := by decide +kernel

theorem ledger_17_12 : ∀ i ∈ List.range 4, LedgerAt 17 (12+i) := by decide +kernel

theorem ledger_17_16 : ∀ i ∈ List.range 4, LedgerAt 17 (16+i) := by decide +kernel

theorem ledger_17_20 : ∀ i ∈ List.range 4, LedgerAt 17 (20+i) := by decide +kernel

theorem ledger_17_24 : ∀ i ∈ List.range 4, LedgerAt 17 (24+i) := by decide +kernel

theorem ledger_17_28 : ∀ i ∈ List.range 4, LedgerAt 17 (28+i) := by decide +kernel

theorem ledger_17_32 : ∀ i ∈ List.range 4, LedgerAt 17 (32+i) := by decide +kernel

theorem ledger_17_36 : ∀ i ∈ List.range 4, LedgerAt 17 (36+i) := by decide +kernel

theorem ledger_17_40 : ∀ i ∈ List.range 4, LedgerAt 17 (40+i) := by decide +kernel

theorem ledger_17_44 : ∀ i ∈ List.range 4, LedgerAt 17 (44+i) := by decide +kernel

theorem ledger_17_48 : ∀ i ∈ List.range 4, LedgerAt 17 (48+i) := by decide +kernel

theorem ledger_17_52 : ∀ i ∈ List.range 4, LedgerAt 17 (52+i) := by decide +kernel

theorem ledger_17_56 : ∀ i ∈ List.range 4, LedgerAt 17 (56+i) := by decide +kernel

theorem ledger_17_60 : ∀ i ∈ List.range 4, LedgerAt 17 (60+i) := by decide +kernel

theorem ledger_17_64 : ∀ i ∈ List.range 4, LedgerAt 17 (64+i) := by decide +kernel

theorem ledger_17_68 : ∀ i ∈ List.range 4, LedgerAt 17 (68+i) := by decide +kernel

theorem ledger_17_72 : ∀ i ∈ List.range 4, LedgerAt 17 (72+i) := by decide +kernel

theorem ledger_17_76 : ∀ i ∈ List.range 4, LedgerAt 17 (76+i) := by decide +kernel

theorem ledger_17_80 : ∀ i ∈ List.range 4, LedgerAt 17 (80+i) := by decide +kernel

theorem ledger_17_84 : ∀ i ∈ List.range 4, LedgerAt 17 (84+i) := by decide +kernel

theorem ledger_17_88 : ∀ i ∈ List.range 4, LedgerAt 17 (88+i) := by decide +kernel

theorem ledger_17_92 : ∀ i ∈ List.range 4, LedgerAt 17 (92+i) := by decide +kernel

theorem ledger_17_96 : ∀ i ∈ List.range 4, LedgerAt 17 (96+i) := by decide +kernel

theorem ledger_17_100 : ∀ i ∈ List.range 4, LedgerAt 17 (100+i) := by decide +kernel

theorem ledger_17_104 : ∀ i ∈ List.range 4, LedgerAt 17 (104+i) := by decide +kernel

theorem ledger_17_108 : ∀ i ∈ List.range 4, LedgerAt 17 (108+i) := by decide +kernel

theorem ledger_17_112 : ∀ i ∈ List.range 4, LedgerAt 17 (112+i) := by decide +kernel

theorem ledger_17_116 : ∀ i ∈ List.range 4, LedgerAt 17 (116+i) := by decide +kernel

theorem ledger_17_120 : ∀ i ∈ List.range 4, LedgerAt 17 (120+i) := by decide +kernel

theorem ledger_17_124 : ∀ i ∈ List.range 4, LedgerAt 17 (124+i) := by decide +kernel

theorem ledger_17_128 : ∀ i ∈ List.range 4, LedgerAt 17 (128+i) := by decide +kernel

theorem ledger_17_132 : ∀ i ∈ List.range 1, LedgerAt 17 (132+i) := by decide +kernel

theorem ledger_17 (v : ℕ) (hv : v ∈ List.range 133) : LedgerAt 17 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 17 v)
  have h := (join 0 68 65 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_17_0 ledger_17_4) (join 8 4 4 ledger_17_8 ledger_17_12)) (join 16 8 8 (join 16 4 4 ledger_17_16 ledger_17_20) (join 24 4 4 ledger_17_24 ledger_17_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_17_32 ledger_17_36) (join 40 4 4 ledger_17_40 ledger_17_44)) (join 48 8 12 (join 48 4 4 ledger_17_48 ledger_17_52) (join 56 4 8 ledger_17_56 (join 60 4 4 ledger_17_60 ledger_17_64))))) (join 68 32 33 (join 68 16 16 (join 68 8 8 (join 68 4 4 ledger_17_68 ledger_17_72) (join 76 4 4 ledger_17_76 ledger_17_80)) (join 84 8 8 (join 84 4 4 ledger_17_84 ledger_17_88) (join 92 4 4 ledger_17_92 ledger_17_96))) (join 100 16 17 (join 100 8 8 (join 100 4 4 ledger_17_100 ledger_17_104) (join 108 4 4 ledger_17_108 ledger_17_112)) (join 116 8 9 (join 116 4 4 ledger_17_116 ledger_17_120) (join 124 4 5 ledger_17_124 (join 128 4 1 ledger_17_128 ledger_17_132))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
