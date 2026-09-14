import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_11_0 : ∀ i ∈ List.range 4, SingleAt 11 (0+i) := by decide +kernel

theorem single_11_4 : ∀ i ∈ List.range 4, SingleAt 11 (4+i) := by decide +kernel

theorem single_11_8 : ∀ i ∈ List.range 4, SingleAt 11 (8+i) := by decide +kernel

theorem single_11_12 : ∀ i ∈ List.range 4, SingleAt 11 (12+i) := by decide +kernel

theorem single_11_16 : ∀ i ∈ List.range 4, SingleAt 11 (16+i) := by decide +kernel

theorem single_11_20 : ∀ i ∈ List.range 4, SingleAt 11 (20+i) := by decide +kernel

theorem single_11_24 : ∀ i ∈ List.range 4, SingleAt 11 (24+i) := by decide +kernel

theorem single_11_28 : ∀ i ∈ List.range 4, SingleAt 11 (28+i) := by decide +kernel

theorem single_11_32 : ∀ i ∈ List.range 4, SingleAt 11 (32+i) := by decide +kernel

theorem single_11_36 : ∀ i ∈ List.range 4, SingleAt 11 (36+i) := by decide +kernel

theorem single_11_40 : ∀ i ∈ List.range 4, SingleAt 11 (40+i) := by decide +kernel

theorem single_11_44 : ∀ i ∈ List.range 4, SingleAt 11 (44+i) := by decide +kernel

theorem single_11_48 : ∀ i ∈ List.range 4, SingleAt 11 (48+i) := by decide +kernel

theorem single_11_52 : ∀ i ∈ List.range 4, SingleAt 11 (52+i) := by decide +kernel

theorem single_11_56 : ∀ i ∈ List.range 4, SingleAt 11 (56+i) := by decide +kernel

theorem single_11_60 : ∀ i ∈ List.range 4, SingleAt 11 (60+i) := by decide +kernel

theorem single_11_64 : ∀ i ∈ List.range 4, SingleAt 11 (64+i) := by decide +kernel

theorem single_11_68 : ∀ i ∈ List.range 4, SingleAt 11 (68+i) := by decide +kernel

theorem single_11_72 : ∀ i ∈ List.range 4, SingleAt 11 (72+i) := by decide +kernel

theorem single_11_76 : ∀ i ∈ List.range 4, SingleAt 11 (76+i) := by decide +kernel

theorem single_11_80 : ∀ i ∈ List.range 4, SingleAt 11 (80+i) := by decide +kernel

theorem single_11_84 : ∀ i ∈ List.range 4, SingleAt 11 (84+i) := by decide +kernel

theorem single_11_88 : ∀ i ∈ List.range 4, SingleAt 11 (88+i) := by decide +kernel

theorem single_11_92 : ∀ i ∈ List.range 4, SingleAt 11 (92+i) := by decide +kernel

theorem single_11_96 : ∀ i ∈ List.range 4, SingleAt 11 (96+i) := by decide +kernel

theorem single_11_100 : ∀ i ∈ List.range 4, SingleAt 11 (100+i) := by decide +kernel

theorem single_11_104 : ∀ i ∈ List.range 4, SingleAt 11 (104+i) := by decide +kernel

theorem single_11_108 : ∀ i ∈ List.range 4, SingleAt 11 (108+i) := by decide +kernel

theorem single_11_112 : ∀ i ∈ List.range 4, SingleAt 11 (112+i) := by decide +kernel

theorem single_11_116 : ∀ i ∈ List.range 4, SingleAt 11 (116+i) := by decide +kernel

theorem single_11_120 : ∀ i ∈ List.range 4, SingleAt 11 (120+i) := by decide +kernel

theorem single_11_124 : ∀ i ∈ List.range 4, SingleAt 11 (124+i) := by decide +kernel

theorem single_11_128 : ∀ i ∈ List.range 4, SingleAt 11 (128+i) := by decide +kernel

theorem single_11_132 : ∀ i ∈ List.range 4, SingleAt 11 (132+i) := by decide +kernel

theorem single_11_136 : ∀ i ∈ List.range 3, SingleAt 11 (136+i) := by decide +kernel

theorem single_11 (v : ℕ) (hv : v ∈ List.range 139) : SingleAt 11 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 11 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_11_0 single_11_4) (join 8 4 4 single_11_8 single_11_12)) (join 16 8 8 (join 16 4 4 single_11_16 single_11_20) (join 24 4 4 single_11_24 single_11_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 single_11_32 single_11_36) (join 40 4 4 single_11_40 single_11_44)) (join 48 8 12 (join 48 4 4 single_11_48 single_11_52) (join 56 4 8 single_11_56 (join 60 4 4 single_11_60 single_11_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 single_11_68 single_11_72) (join 76 4 4 single_11_76 single_11_80)) (join 84 8 12 (join 84 4 4 single_11_84 single_11_88) (join 92 4 8 single_11_92 (join 96 4 4 single_11_96 single_11_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 single_11_104 single_11_108) (join 112 4 4 single_11_112 single_11_116)) (join 120 8 11 (join 120 4 4 single_11_120 single_11_124) (join 128 4 7 single_11_128 (join 132 4 3 single_11_132 single_11_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_11_0 : ∀ i ∈ List.range 4, PhaseAt 11 (0+i) := by decide +kernel

theorem phase_11_4 : ∀ i ∈ List.range 4, PhaseAt 11 (4+i) := by decide +kernel

theorem phase_11_8 : ∀ i ∈ List.range 4, PhaseAt 11 (8+i) := by decide +kernel

theorem phase_11_12 : ∀ i ∈ List.range 4, PhaseAt 11 (12+i) := by decide +kernel

theorem phase_11_16 : ∀ i ∈ List.range 4, PhaseAt 11 (16+i) := by decide +kernel

theorem phase_11_20 : ∀ i ∈ List.range 4, PhaseAt 11 (20+i) := by decide +kernel

theorem phase_11_24 : ∀ i ∈ List.range 4, PhaseAt 11 (24+i) := by decide +kernel

theorem phase_11_28 : ∀ i ∈ List.range 4, PhaseAt 11 (28+i) := by decide +kernel

theorem phase_11_32 : ∀ i ∈ List.range 4, PhaseAt 11 (32+i) := by decide +kernel

theorem phase_11_36 : ∀ i ∈ List.range 4, PhaseAt 11 (36+i) := by decide +kernel

theorem phase_11_40 : ∀ i ∈ List.range 4, PhaseAt 11 (40+i) := by decide +kernel

theorem phase_11_44 : ∀ i ∈ List.range 4, PhaseAt 11 (44+i) := by decide +kernel

theorem phase_11_48 : ∀ i ∈ List.range 4, PhaseAt 11 (48+i) := by decide +kernel

theorem phase_11_52 : ∀ i ∈ List.range 4, PhaseAt 11 (52+i) := by decide +kernel

theorem phase_11_56 : ∀ i ∈ List.range 4, PhaseAt 11 (56+i) := by decide +kernel

theorem phase_11_60 : ∀ i ∈ List.range 4, PhaseAt 11 (60+i) := by decide +kernel

theorem phase_11_64 : ∀ i ∈ List.range 4, PhaseAt 11 (64+i) := by decide +kernel

theorem phase_11_68 : ∀ i ∈ List.range 4, PhaseAt 11 (68+i) := by decide +kernel

theorem phase_11_72 : ∀ i ∈ List.range 4, PhaseAt 11 (72+i) := by decide +kernel

theorem phase_11_76 : ∀ i ∈ List.range 4, PhaseAt 11 (76+i) := by decide +kernel

theorem phase_11_80 : ∀ i ∈ List.range 4, PhaseAt 11 (80+i) := by decide +kernel

theorem phase_11_84 : ∀ i ∈ List.range 4, PhaseAt 11 (84+i) := by decide +kernel

theorem phase_11_88 : ∀ i ∈ List.range 4, PhaseAt 11 (88+i) := by decide +kernel

theorem phase_11_92 : ∀ i ∈ List.range 4, PhaseAt 11 (92+i) := by decide +kernel

theorem phase_11_96 : ∀ i ∈ List.range 4, PhaseAt 11 (96+i) := by decide +kernel

theorem phase_11_100 : ∀ i ∈ List.range 4, PhaseAt 11 (100+i) := by decide +kernel

theorem phase_11_104 : ∀ i ∈ List.range 4, PhaseAt 11 (104+i) := by decide +kernel

theorem phase_11_108 : ∀ i ∈ List.range 4, PhaseAt 11 (108+i) := by decide +kernel

theorem phase_11_112 : ∀ i ∈ List.range 4, PhaseAt 11 (112+i) := by decide +kernel

theorem phase_11_116 : ∀ i ∈ List.range 4, PhaseAt 11 (116+i) := by decide +kernel

theorem phase_11_120 : ∀ i ∈ List.range 4, PhaseAt 11 (120+i) := by decide +kernel

theorem phase_11_124 : ∀ i ∈ List.range 4, PhaseAt 11 (124+i) := by decide +kernel

theorem phase_11_128 : ∀ i ∈ List.range 4, PhaseAt 11 (128+i) := by decide +kernel

theorem phase_11_132 : ∀ i ∈ List.range 4, PhaseAt 11 (132+i) := by decide +kernel

theorem phase_11_136 : ∀ i ∈ List.range 3, PhaseAt 11 (136+i) := by decide +kernel

theorem phase_11 (v : ℕ) (hv : v ∈ List.range 139) : PhaseAt 11 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 11 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_11_0 phase_11_4) (join 8 4 4 phase_11_8 phase_11_12)) (join 16 8 8 (join 16 4 4 phase_11_16 phase_11_20) (join 24 4 4 phase_11_24 phase_11_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_11_32 phase_11_36) (join 40 4 4 phase_11_40 phase_11_44)) (join 48 8 12 (join 48 4 4 phase_11_48 phase_11_52) (join 56 4 8 phase_11_56 (join 60 4 4 phase_11_60 phase_11_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 phase_11_68 phase_11_72) (join 76 4 4 phase_11_76 phase_11_80)) (join 84 8 12 (join 84 4 4 phase_11_84 phase_11_88) (join 92 4 8 phase_11_92 (join 96 4 4 phase_11_96 phase_11_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 phase_11_104 phase_11_108) (join 112 4 4 phase_11_112 phase_11_116)) (join 120 8 11 (join 120 4 4 phase_11_120 phase_11_124) (join 128 4 7 phase_11_128 (join 132 4 3 phase_11_132 phase_11_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_11_0 : ∀ i ∈ List.range 1, ThresholdAt 11 (0+i) := by decide +kernel

theorem threshold_11_1 : ∀ i ∈ List.range 1, ThresholdAt 11 (1+i) := by decide +kernel

theorem threshold_11_2 : ∀ i ∈ List.range 1, ThresholdAt 11 (2+i) := by decide +kernel

theorem threshold_11_3 : ∀ i ∈ List.range 1, ThresholdAt 11 (3+i) := by decide +kernel

theorem threshold_11_4 : ∀ i ∈ List.range 1, ThresholdAt 11 (4+i) := by decide +kernel

theorem threshold_11_5 : ∀ i ∈ List.range 1, ThresholdAt 11 (5+i) := by decide +kernel

theorem threshold_11_6 : ∀ i ∈ List.range 1, ThresholdAt 11 (6+i) := by decide +kernel

theorem threshold_11_7 : ∀ i ∈ List.range 1, ThresholdAt 11 (7+i) := by decide +kernel

theorem threshold_11_8 : ∀ i ∈ List.range 1, ThresholdAt 11 (8+i) := by decide +kernel

theorem threshold_11_9 : ∀ i ∈ List.range 1, ThresholdAt 11 (9+i) := by decide +kernel

theorem threshold_11_10 : ∀ i ∈ List.range 1, ThresholdAt 11 (10+i) := by decide +kernel

theorem threshold_11_11 : ∀ i ∈ List.range 1, ThresholdAt 11 (11+i) := by decide +kernel

theorem threshold_11_12 : ∀ i ∈ List.range 1, ThresholdAt 11 (12+i) := by decide +kernel

theorem threshold_11_13 : ∀ i ∈ List.range 1, ThresholdAt 11 (13+i) := by decide +kernel

theorem threshold_11_14 : ∀ i ∈ List.range 1, ThresholdAt 11 (14+i) := by decide +kernel

theorem threshold_11_15 : ∀ i ∈ List.range 1, ThresholdAt 11 (15+i) := by decide +kernel

theorem threshold_11_16 : ∀ i ∈ List.range 1, ThresholdAt 11 (16+i) := by decide +kernel

theorem threshold_11_17 : ∀ i ∈ List.range 1, ThresholdAt 11 (17+i) := by decide +kernel

theorem threshold_11_18 : ∀ i ∈ List.range 1, ThresholdAt 11 (18+i) := by decide +kernel

theorem threshold_11_19 : ∀ i ∈ List.range 1, ThresholdAt 11 (19+i) := by decide +kernel

theorem threshold_11_20 : ∀ i ∈ List.range 1, ThresholdAt 11 (20+i) := by decide +kernel

theorem threshold_11_21 : ∀ i ∈ List.range 1, ThresholdAt 11 (21+i) := by decide +kernel

theorem threshold_11_22 : ∀ i ∈ List.range 1, ThresholdAt 11 (22+i) := by decide +kernel

theorem threshold_11_23 : ∀ i ∈ List.range 1, ThresholdAt 11 (23+i) := by decide +kernel

theorem threshold_11_24 : ∀ i ∈ List.range 1, ThresholdAt 11 (24+i) := by decide +kernel

theorem threshold_11_25 : ∀ i ∈ List.range 1, ThresholdAt 11 (25+i) := by decide +kernel

theorem threshold_11_26 : ∀ i ∈ List.range 1, ThresholdAt 11 (26+i) := by decide +kernel

theorem threshold_11_27 : ∀ i ∈ List.range 1, ThresholdAt 11 (27+i) := by decide +kernel

theorem threshold_11_28 : ∀ i ∈ List.range 1, ThresholdAt 11 (28+i) := by decide +kernel

theorem threshold_11_29 : ∀ i ∈ List.range 1, ThresholdAt 11 (29+i) := by decide +kernel

theorem threshold_11_30 : ∀ i ∈ List.range 1, ThresholdAt 11 (30+i) := by decide +kernel

theorem threshold_11_31 : ∀ i ∈ List.range 1, ThresholdAt 11 (31+i) := by decide +kernel

theorem threshold_11_32 : ∀ i ∈ List.range 1, ThresholdAt 11 (32+i) := by decide +kernel

theorem threshold_11_33 : ∀ i ∈ List.range 1, ThresholdAt 11 (33+i) := by decide +kernel

theorem threshold_11_34 : ∀ i ∈ List.range 1, ThresholdAt 11 (34+i) := by decide +kernel

theorem threshold_11_35 : ∀ i ∈ List.range 1, ThresholdAt 11 (35+i) := by decide +kernel

theorem threshold_11_36 : ∀ i ∈ List.range 1, ThresholdAt 11 (36+i) := by decide +kernel

theorem threshold_11_37 : ∀ i ∈ List.range 1, ThresholdAt 11 (37+i) := by decide +kernel

theorem threshold_11_38 : ∀ i ∈ List.range 1, ThresholdAt 11 (38+i) := by decide +kernel

theorem threshold_11_39 : ∀ i ∈ List.range 1, ThresholdAt 11 (39+i) := by decide +kernel

theorem threshold_11_40 : ∀ i ∈ List.range 1, ThresholdAt 11 (40+i) := by decide +kernel

theorem threshold_11_41 : ∀ i ∈ List.range 1, ThresholdAt 11 (41+i) := by decide +kernel

theorem threshold_11_42 : ∀ i ∈ List.range 1, ThresholdAt 11 (42+i) := by decide +kernel

theorem threshold_11_43 : ∀ i ∈ List.range 1, ThresholdAt 11 (43+i) := by decide +kernel

theorem threshold_11_44 : ∀ i ∈ List.range 1, ThresholdAt 11 (44+i) := by decide +kernel

theorem threshold_11_45 : ∀ i ∈ List.range 1, ThresholdAt 11 (45+i) := by decide +kernel

theorem threshold_11_46 : ∀ i ∈ List.range 1, ThresholdAt 11 (46+i) := by decide +kernel

theorem threshold_11_47 : ∀ i ∈ List.range 1, ThresholdAt 11 (47+i) := by decide +kernel

theorem threshold_11_48 : ∀ i ∈ List.range 1, ThresholdAt 11 (48+i) := by decide +kernel

theorem threshold_11_49 : ∀ i ∈ List.range 1, ThresholdAt 11 (49+i) := by decide +kernel

theorem threshold_11_50 : ∀ i ∈ List.range 1, ThresholdAt 11 (50+i) := by decide +kernel

theorem threshold_11_51 : ∀ i ∈ List.range 1, ThresholdAt 11 (51+i) := by decide +kernel

theorem threshold_11_52 : ∀ i ∈ List.range 1, ThresholdAt 11 (52+i) := by decide +kernel

theorem threshold_11_53 : ∀ i ∈ List.range 1, ThresholdAt 11 (53+i) := by decide +kernel

theorem threshold_11_54 : ∀ i ∈ List.range 1, ThresholdAt 11 (54+i) := by decide +kernel

theorem threshold_11_55 : ∀ i ∈ List.range 1, ThresholdAt 11 (55+i) := by decide +kernel

theorem threshold_11_56 : ∀ i ∈ List.range 1, ThresholdAt 11 (56+i) := by decide +kernel

theorem threshold_11_57 : ∀ i ∈ List.range 1, ThresholdAt 11 (57+i) := by decide +kernel

theorem threshold_11_58 : ∀ i ∈ List.range 1, ThresholdAt 11 (58+i) := by decide +kernel

theorem threshold_11_59 : ∀ i ∈ List.range 1, ThresholdAt 11 (59+i) := by decide +kernel

theorem threshold_11_60 : ∀ i ∈ List.range 1, ThresholdAt 11 (60+i) := by decide +kernel

theorem threshold_11_61 : ∀ i ∈ List.range 1, ThresholdAt 11 (61+i) := by decide +kernel

theorem threshold_11_62 : ∀ i ∈ List.range 1, ThresholdAt 11 (62+i) := by decide +kernel

theorem threshold_11_63 : ∀ i ∈ List.range 1, ThresholdAt 11 (63+i) := by decide +kernel

theorem threshold_11_64 : ∀ i ∈ List.range 1, ThresholdAt 11 (64+i) := by decide +kernel

theorem threshold_11_65 : ∀ i ∈ List.range 1, ThresholdAt 11 (65+i) := by decide +kernel

theorem threshold_11_66 : ∀ i ∈ List.range 1, ThresholdAt 11 (66+i) := by decide +kernel

theorem threshold_11_67 : ∀ i ∈ List.range 1, ThresholdAt 11 (67+i) := by decide +kernel

theorem threshold_11_68 : ∀ i ∈ List.range 1, ThresholdAt 11 (68+i) := by decide +kernel

theorem threshold_11_69 : ∀ i ∈ List.range 1, ThresholdAt 11 (69+i) := by decide +kernel

theorem threshold_11_70 : ∀ i ∈ List.range 1, ThresholdAt 11 (70+i) := by decide +kernel

theorem threshold_11_71 : ∀ i ∈ List.range 1, ThresholdAt 11 (71+i) := by decide +kernel

theorem threshold_11_72 : ∀ i ∈ List.range 1, ThresholdAt 11 (72+i) := by decide +kernel

theorem threshold_11_73 : ∀ i ∈ List.range 1, ThresholdAt 11 (73+i) := by decide +kernel

theorem threshold_11_74 : ∀ i ∈ List.range 1, ThresholdAt 11 (74+i) := by decide +kernel

theorem threshold_11_75 : ∀ i ∈ List.range 1, ThresholdAt 11 (75+i) := by decide +kernel

theorem threshold_11_76 : ∀ i ∈ List.range 1, ThresholdAt 11 (76+i) := by decide +kernel

theorem threshold_11_77 : ∀ i ∈ List.range 1, ThresholdAt 11 (77+i) := by decide +kernel

theorem threshold_11_78 : ∀ i ∈ List.range 1, ThresholdAt 11 (78+i) := by decide +kernel

theorem threshold_11_79 : ∀ i ∈ List.range 1, ThresholdAt 11 (79+i) := by decide +kernel

theorem threshold_11_80 : ∀ i ∈ List.range 1, ThresholdAt 11 (80+i) := by decide +kernel

theorem threshold_11_81 : ∀ i ∈ List.range 1, ThresholdAt 11 (81+i) := by decide +kernel

theorem threshold_11_82 : ∀ i ∈ List.range 1, ThresholdAt 11 (82+i) := by decide +kernel

theorem threshold_11_83 : ∀ i ∈ List.range 1, ThresholdAt 11 (83+i) := by decide +kernel

theorem threshold_11_84 : ∀ i ∈ List.range 1, ThresholdAt 11 (84+i) := by decide +kernel

theorem threshold_11_85 : ∀ i ∈ List.range 1, ThresholdAt 11 (85+i) := by decide +kernel

theorem threshold_11_86 : ∀ i ∈ List.range 1, ThresholdAt 11 (86+i) := by decide +kernel

theorem threshold_11_87 : ∀ i ∈ List.range 1, ThresholdAt 11 (87+i) := by decide +kernel

theorem threshold_11_88 : ∀ i ∈ List.range 1, ThresholdAt 11 (88+i) := by decide +kernel

theorem threshold_11_89 : ∀ i ∈ List.range 1, ThresholdAt 11 (89+i) := by decide +kernel

theorem threshold_11_90 : ∀ i ∈ List.range 1, ThresholdAt 11 (90+i) := by decide +kernel

theorem threshold_11_91 : ∀ i ∈ List.range 1, ThresholdAt 11 (91+i) := by decide +kernel

theorem threshold_11_92 : ∀ i ∈ List.range 1, ThresholdAt 11 (92+i) := by decide +kernel

theorem threshold_11_93 : ∀ i ∈ List.range 1, ThresholdAt 11 (93+i) := by decide +kernel

theorem threshold_11_94 : ∀ i ∈ List.range 1, ThresholdAt 11 (94+i) := by decide +kernel

theorem threshold_11_95 : ∀ i ∈ List.range 1, ThresholdAt 11 (95+i) := by decide +kernel

theorem threshold_11_96 : ∀ i ∈ List.range 1, ThresholdAt 11 (96+i) := by decide +kernel

theorem threshold_11_97 : ∀ i ∈ List.range 1, ThresholdAt 11 (97+i) := by decide +kernel

theorem threshold_11_98 : ∀ i ∈ List.range 1, ThresholdAt 11 (98+i) := by decide +kernel

theorem threshold_11_99 : ∀ i ∈ List.range 1, ThresholdAt 11 (99+i) := by decide +kernel

theorem threshold_11_100 : ∀ i ∈ List.range 1, ThresholdAt 11 (100+i) := by decide +kernel

theorem threshold_11_101 : ∀ i ∈ List.range 1, ThresholdAt 11 (101+i) := by decide +kernel

theorem threshold_11_102 : ∀ i ∈ List.range 1, ThresholdAt 11 (102+i) := by decide +kernel

theorem threshold_11_103 : ∀ i ∈ List.range 1, ThresholdAt 11 (103+i) := by decide +kernel

theorem threshold_11_104 : ∀ i ∈ List.range 1, ThresholdAt 11 (104+i) := by decide +kernel

theorem threshold_11_105 : ∀ i ∈ List.range 1, ThresholdAt 11 (105+i) := by decide +kernel

theorem threshold_11_106 : ∀ i ∈ List.range 1, ThresholdAt 11 (106+i) := by decide +kernel

theorem threshold_11_107 : ∀ i ∈ List.range 1, ThresholdAt 11 (107+i) := by decide +kernel

theorem threshold_11_108 : ∀ i ∈ List.range 1, ThresholdAt 11 (108+i) := by decide +kernel

theorem threshold_11_109 : ∀ i ∈ List.range 1, ThresholdAt 11 (109+i) := by decide +kernel

theorem threshold_11_110 : ∀ i ∈ List.range 1, ThresholdAt 11 (110+i) := by decide +kernel

theorem threshold_11_111 : ∀ i ∈ List.range 1, ThresholdAt 11 (111+i) := by decide +kernel

theorem threshold_11_112 : ∀ i ∈ List.range 1, ThresholdAt 11 (112+i) := by decide +kernel

theorem threshold_11_113 : ∀ i ∈ List.range 1, ThresholdAt 11 (113+i) := by decide +kernel

theorem threshold_11_114 : ∀ i ∈ List.range 1, ThresholdAt 11 (114+i) := by decide +kernel

theorem threshold_11_115 : ∀ i ∈ List.range 1, ThresholdAt 11 (115+i) := by decide +kernel

theorem threshold_11_116 : ∀ i ∈ List.range 1, ThresholdAt 11 (116+i) := by decide +kernel

theorem threshold_11_117 : ∀ i ∈ List.range 1, ThresholdAt 11 (117+i) := by decide +kernel

theorem threshold_11_118 : ∀ i ∈ List.range 1, ThresholdAt 11 (118+i) := by decide +kernel

theorem threshold_11_119 : ∀ i ∈ List.range 1, ThresholdAt 11 (119+i) := by decide +kernel

theorem threshold_11_120 : ∀ i ∈ List.range 1, ThresholdAt 11 (120+i) := by decide +kernel

theorem threshold_11_121 : ∀ i ∈ List.range 1, ThresholdAt 11 (121+i) := by decide +kernel

theorem threshold_11_122 : ∀ i ∈ List.range 1, ThresholdAt 11 (122+i) := by decide +kernel

theorem threshold_11_123 : ∀ i ∈ List.range 1, ThresholdAt 11 (123+i) := by decide +kernel

theorem threshold_11_124 : ∀ i ∈ List.range 1, ThresholdAt 11 (124+i) := by decide +kernel

theorem threshold_11_125 : ∀ i ∈ List.range 1, ThresholdAt 11 (125+i) := by decide +kernel

theorem threshold_11_126 : ∀ i ∈ List.range 1, ThresholdAt 11 (126+i) := by decide +kernel

theorem threshold_11_127 : ∀ i ∈ List.range 1, ThresholdAt 11 (127+i) := by decide +kernel

theorem threshold_11_128 : ∀ i ∈ List.range 1, ThresholdAt 11 (128+i) := by decide +kernel

theorem threshold_11_129 : ∀ i ∈ List.range 1, ThresholdAt 11 (129+i) := by decide +kernel

theorem threshold_11_130 : ∀ i ∈ List.range 1, ThresholdAt 11 (130+i) := by decide +kernel

theorem threshold_11_131 : ∀ i ∈ List.range 1, ThresholdAt 11 (131+i) := by decide +kernel

theorem threshold_11_132 : ∀ i ∈ List.range 1, ThresholdAt 11 (132+i) := by decide +kernel

theorem threshold_11_133 : ∀ i ∈ List.range 1, ThresholdAt 11 (133+i) := by decide +kernel

theorem threshold_11_134 : ∀ i ∈ List.range 1, ThresholdAt 11 (134+i) := by decide +kernel

theorem threshold_11_135 : ∀ i ∈ List.range 1, ThresholdAt 11 (135+i) := by decide +kernel

theorem threshold_11_136 : ∀ i ∈ List.range 1, ThresholdAt 11 (136+i) := by decide +kernel

theorem threshold_11_137 : ∀ i ∈ List.range 1, ThresholdAt 11 (137+i) := by decide +kernel

theorem threshold_11_138 : ∀ i ∈ List.range 1, ThresholdAt 11 (138+i) := by decide +kernel

theorem threshold_11 (v : ℕ) (hv : v ∈ List.range 139) : ThresholdAt 11 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 11 v)
  have h := (join 0 69 70 (join 0 34 35 (join 0 17 17 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_11_0 threshold_11_1) (join 2 1 1 threshold_11_2 threshold_11_3)) (join 4 2 2 (join 4 1 1 threshold_11_4 threshold_11_5) (join 6 1 1 threshold_11_6 threshold_11_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_11_8 threshold_11_9) (join 10 1 1 threshold_11_10 threshold_11_11)) (join 12 2 3 (join 12 1 1 threshold_11_12 threshold_11_13) (join 14 1 2 threshold_11_14 (join 15 1 1 threshold_11_15 threshold_11_16))))) (join 17 8 9 (join 17 4 4 (join 17 2 2 (join 17 1 1 threshold_11_17 threshold_11_18) (join 19 1 1 threshold_11_19 threshold_11_20)) (join 21 2 2 (join 21 1 1 threshold_11_21 threshold_11_22) (join 23 1 1 threshold_11_23 threshold_11_24))) (join 25 4 5 (join 25 2 2 (join 25 1 1 threshold_11_25 threshold_11_26) (join 27 1 1 threshold_11_27 threshold_11_28)) (join 29 2 3 (join 29 1 1 threshold_11_29 threshold_11_30) (join 31 1 2 threshold_11_31 (join 32 1 1 threshold_11_32 threshold_11_33)))))) (join 34 17 18 (join 34 8 9 (join 34 4 4 (join 34 2 2 (join 34 1 1 threshold_11_34 threshold_11_35) (join 36 1 1 threshold_11_36 threshold_11_37)) (join 38 2 2 (join 38 1 1 threshold_11_38 threshold_11_39) (join 40 1 1 threshold_11_40 threshold_11_41))) (join 42 4 5 (join 42 2 2 (join 42 1 1 threshold_11_42 threshold_11_43) (join 44 1 1 threshold_11_44 threshold_11_45)) (join 46 2 3 (join 46 1 1 threshold_11_46 threshold_11_47) (join 48 1 2 threshold_11_48 (join 49 1 1 threshold_11_49 threshold_11_50))))) (join 51 9 9 (join 51 4 5 (join 51 2 2 (join 51 1 1 threshold_11_51 threshold_11_52) (join 53 1 1 threshold_11_53 threshold_11_54)) (join 55 2 3 (join 55 1 1 threshold_11_55 threshold_11_56) (join 57 1 2 threshold_11_57 (join 58 1 1 threshold_11_58 threshold_11_59)))) (join 60 4 5 (join 60 2 2 (join 60 1 1 threshold_11_60 threshold_11_61) (join 62 1 1 threshold_11_62 threshold_11_63)) (join 64 2 3 (join 64 1 1 threshold_11_64 threshold_11_65) (join 66 1 2 threshold_11_66 (join 67 1 1 threshold_11_67 threshold_11_68))))))) (join 69 35 35 (join 69 17 18 (join 69 8 9 (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_11_69 threshold_11_70) (join 71 1 1 threshold_11_71 threshold_11_72)) (join 73 2 2 (join 73 1 1 threshold_11_73 threshold_11_74) (join 75 1 1 threshold_11_75 threshold_11_76))) (join 77 4 5 (join 77 2 2 (join 77 1 1 threshold_11_77 threshold_11_78) (join 79 1 1 threshold_11_79 threshold_11_80)) (join 81 2 3 (join 81 1 1 threshold_11_81 threshold_11_82) (join 83 1 2 threshold_11_83 (join 84 1 1 threshold_11_84 threshold_11_85))))) (join 86 9 9 (join 86 4 5 (join 86 2 2 (join 86 1 1 threshold_11_86 threshold_11_87) (join 88 1 1 threshold_11_88 threshold_11_89)) (join 90 2 3 (join 90 1 1 threshold_11_90 threshold_11_91) (join 92 1 2 threshold_11_92 (join 93 1 1 threshold_11_93 threshold_11_94)))) (join 95 4 5 (join 95 2 2 (join 95 1 1 threshold_11_95 threshold_11_96) (join 97 1 1 threshold_11_97 threshold_11_98)) (join 99 2 3 (join 99 1 1 threshold_11_99 threshold_11_100) (join 101 1 2 threshold_11_101 (join 102 1 1 threshold_11_102 threshold_11_103)))))) (join 104 17 18 (join 104 8 9 (join 104 4 4 (join 104 2 2 (join 104 1 1 threshold_11_104 threshold_11_105) (join 106 1 1 threshold_11_106 threshold_11_107)) (join 108 2 2 (join 108 1 1 threshold_11_108 threshold_11_109) (join 110 1 1 threshold_11_110 threshold_11_111))) (join 112 4 5 (join 112 2 2 (join 112 1 1 threshold_11_112 threshold_11_113) (join 114 1 1 threshold_11_114 threshold_11_115)) (join 116 2 3 (join 116 1 1 threshold_11_116 threshold_11_117) (join 118 1 2 threshold_11_118 (join 119 1 1 threshold_11_119 threshold_11_120))))) (join 121 9 9 (join 121 4 5 (join 121 2 2 (join 121 1 1 threshold_11_121 threshold_11_122) (join 123 1 1 threshold_11_123 threshold_11_124)) (join 125 2 3 (join 125 1 1 threshold_11_125 threshold_11_126) (join 127 1 2 threshold_11_127 (join 128 1 1 threshold_11_128 threshold_11_129)))) (join 130 4 5 (join 130 2 2 (join 130 1 1 threshold_11_130 threshold_11_131) (join 132 1 1 threshold_11_132 threshold_11_133)) (join 134 2 3 (join 134 1 1 threshold_11_134 threshold_11_135) (join 136 1 2 threshold_11_136 (join 137 1 1 threshold_11_137 threshold_11_138))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_11_0 : ∀ i ∈ List.range 4, LedgerAt 11 (0+i) := by decide +kernel

theorem ledger_11_4 : ∀ i ∈ List.range 4, LedgerAt 11 (4+i) := by decide +kernel

theorem ledger_11_8 : ∀ i ∈ List.range 4, LedgerAt 11 (8+i) := by decide +kernel

theorem ledger_11_12 : ∀ i ∈ List.range 4, LedgerAt 11 (12+i) := by decide +kernel

theorem ledger_11_16 : ∀ i ∈ List.range 4, LedgerAt 11 (16+i) := by decide +kernel

theorem ledger_11_20 : ∀ i ∈ List.range 4, LedgerAt 11 (20+i) := by decide +kernel

theorem ledger_11_24 : ∀ i ∈ List.range 4, LedgerAt 11 (24+i) := by decide +kernel

theorem ledger_11_28 : ∀ i ∈ List.range 4, LedgerAt 11 (28+i) := by decide +kernel

theorem ledger_11_32 : ∀ i ∈ List.range 4, LedgerAt 11 (32+i) := by decide +kernel

theorem ledger_11_36 : ∀ i ∈ List.range 4, LedgerAt 11 (36+i) := by decide +kernel

theorem ledger_11_40 : ∀ i ∈ List.range 4, LedgerAt 11 (40+i) := by decide +kernel

theorem ledger_11_44 : ∀ i ∈ List.range 4, LedgerAt 11 (44+i) := by decide +kernel

theorem ledger_11_48 : ∀ i ∈ List.range 4, LedgerAt 11 (48+i) := by decide +kernel

theorem ledger_11_52 : ∀ i ∈ List.range 4, LedgerAt 11 (52+i) := by decide +kernel

theorem ledger_11_56 : ∀ i ∈ List.range 4, LedgerAt 11 (56+i) := by decide +kernel

theorem ledger_11_60 : ∀ i ∈ List.range 4, LedgerAt 11 (60+i) := by decide +kernel

theorem ledger_11_64 : ∀ i ∈ List.range 4, LedgerAt 11 (64+i) := by decide +kernel

theorem ledger_11_68 : ∀ i ∈ List.range 4, LedgerAt 11 (68+i) := by decide +kernel

theorem ledger_11_72 : ∀ i ∈ List.range 4, LedgerAt 11 (72+i) := by decide +kernel

theorem ledger_11_76 : ∀ i ∈ List.range 4, LedgerAt 11 (76+i) := by decide +kernel

theorem ledger_11_80 : ∀ i ∈ List.range 4, LedgerAt 11 (80+i) := by decide +kernel

theorem ledger_11_84 : ∀ i ∈ List.range 4, LedgerAt 11 (84+i) := by decide +kernel

theorem ledger_11_88 : ∀ i ∈ List.range 4, LedgerAt 11 (88+i) := by decide +kernel

theorem ledger_11_92 : ∀ i ∈ List.range 4, LedgerAt 11 (92+i) := by decide +kernel

theorem ledger_11_96 : ∀ i ∈ List.range 4, LedgerAt 11 (96+i) := by decide +kernel

theorem ledger_11_100 : ∀ i ∈ List.range 4, LedgerAt 11 (100+i) := by decide +kernel

theorem ledger_11_104 : ∀ i ∈ List.range 4, LedgerAt 11 (104+i) := by decide +kernel

theorem ledger_11_108 : ∀ i ∈ List.range 4, LedgerAt 11 (108+i) := by decide +kernel

theorem ledger_11_112 : ∀ i ∈ List.range 4, LedgerAt 11 (112+i) := by decide +kernel

theorem ledger_11_116 : ∀ i ∈ List.range 4, LedgerAt 11 (116+i) := by decide +kernel

theorem ledger_11_120 : ∀ i ∈ List.range 4, LedgerAt 11 (120+i) := by decide +kernel

theorem ledger_11_124 : ∀ i ∈ List.range 4, LedgerAt 11 (124+i) := by decide +kernel

theorem ledger_11_128 : ∀ i ∈ List.range 4, LedgerAt 11 (128+i) := by decide +kernel

theorem ledger_11_132 : ∀ i ∈ List.range 4, LedgerAt 11 (132+i) := by decide +kernel

theorem ledger_11_136 : ∀ i ∈ List.range 3, LedgerAt 11 (136+i) := by decide +kernel

theorem ledger_11 (v : ℕ) (hv : v ∈ List.range 139) : LedgerAt 11 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 11 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_11_0 ledger_11_4) (join 8 4 4 ledger_11_8 ledger_11_12)) (join 16 8 8 (join 16 4 4 ledger_11_16 ledger_11_20) (join 24 4 4 ledger_11_24 ledger_11_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_11_32 ledger_11_36) (join 40 4 4 ledger_11_40 ledger_11_44)) (join 48 8 12 (join 48 4 4 ledger_11_48 ledger_11_52) (join 56 4 8 ledger_11_56 (join 60 4 4 ledger_11_60 ledger_11_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 ledger_11_68 ledger_11_72) (join 76 4 4 ledger_11_76 ledger_11_80)) (join 84 8 12 (join 84 4 4 ledger_11_84 ledger_11_88) (join 92 4 8 ledger_11_92 (join 96 4 4 ledger_11_96 ledger_11_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 ledger_11_104 ledger_11_108) (join 112 4 4 ledger_11_112 ledger_11_116)) (join 120 8 11 (join 120 4 4 ledger_11_120 ledger_11_124) (join 128 4 7 ledger_11_128 (join 132 4 3 ledger_11_132 ledger_11_136))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
