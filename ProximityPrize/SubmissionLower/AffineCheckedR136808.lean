import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_13_0 : ∀ i ∈ List.range 4, SingleAt 13 (0+i) := by decide +kernel

theorem single_13_4 : ∀ i ∈ List.range 4, SingleAt 13 (4+i) := by decide +kernel

theorem single_13_8 : ∀ i ∈ List.range 4, SingleAt 13 (8+i) := by decide +kernel

theorem single_13_12 : ∀ i ∈ List.range 4, SingleAt 13 (12+i) := by decide +kernel

theorem single_13_16 : ∀ i ∈ List.range 4, SingleAt 13 (16+i) := by decide +kernel

theorem single_13_20 : ∀ i ∈ List.range 4, SingleAt 13 (20+i) := by decide +kernel

theorem single_13_24 : ∀ i ∈ List.range 4, SingleAt 13 (24+i) := by decide +kernel

theorem single_13_28 : ∀ i ∈ List.range 4, SingleAt 13 (28+i) := by decide +kernel

theorem single_13_32 : ∀ i ∈ List.range 4, SingleAt 13 (32+i) := by decide +kernel

theorem single_13_36 : ∀ i ∈ List.range 4, SingleAt 13 (36+i) := by decide +kernel

theorem single_13_40 : ∀ i ∈ List.range 4, SingleAt 13 (40+i) := by decide +kernel

theorem single_13_44 : ∀ i ∈ List.range 4, SingleAt 13 (44+i) := by decide +kernel

theorem single_13_48 : ∀ i ∈ List.range 4, SingleAt 13 (48+i) := by decide +kernel

theorem single_13_52 : ∀ i ∈ List.range 4, SingleAt 13 (52+i) := by decide +kernel

theorem single_13_56 : ∀ i ∈ List.range 4, SingleAt 13 (56+i) := by decide +kernel

theorem single_13_60 : ∀ i ∈ List.range 4, SingleAt 13 (60+i) := by decide +kernel

theorem single_13_64 : ∀ i ∈ List.range 4, SingleAt 13 (64+i) := by decide +kernel

theorem single_13_68 : ∀ i ∈ List.range 4, SingleAt 13 (68+i) := by decide +kernel

theorem single_13_72 : ∀ i ∈ List.range 4, SingleAt 13 (72+i) := by decide +kernel

theorem single_13_76 : ∀ i ∈ List.range 4, SingleAt 13 (76+i) := by decide +kernel

theorem single_13_80 : ∀ i ∈ List.range 4, SingleAt 13 (80+i) := by decide +kernel

theorem single_13_84 : ∀ i ∈ List.range 4, SingleAt 13 (84+i) := by decide +kernel

theorem single_13_88 : ∀ i ∈ List.range 4, SingleAt 13 (88+i) := by decide +kernel

theorem single_13_92 : ∀ i ∈ List.range 4, SingleAt 13 (92+i) := by decide +kernel

theorem single_13_96 : ∀ i ∈ List.range 4, SingleAt 13 (96+i) := by decide +kernel

theorem single_13_100 : ∀ i ∈ List.range 4, SingleAt 13 (100+i) := by decide +kernel

theorem single_13_104 : ∀ i ∈ List.range 4, SingleAt 13 (104+i) := by decide +kernel

theorem single_13_108 : ∀ i ∈ List.range 4, SingleAt 13 (108+i) := by decide +kernel

theorem single_13_112 : ∀ i ∈ List.range 4, SingleAt 13 (112+i) := by decide +kernel

theorem single_13_116 : ∀ i ∈ List.range 4, SingleAt 13 (116+i) := by decide +kernel

theorem single_13_120 : ∀ i ∈ List.range 4, SingleAt 13 (120+i) := by decide +kernel

theorem single_13_124 : ∀ i ∈ List.range 4, SingleAt 13 (124+i) := by decide +kernel

theorem single_13_128 : ∀ i ∈ List.range 4, SingleAt 13 (128+i) := by decide +kernel

theorem single_13_132 : ∀ i ∈ List.range 4, SingleAt 13 (132+i) := by decide +kernel

theorem single_13_136 : ∀ i ∈ List.range 1, SingleAt 13 (136+i) := by decide +kernel

theorem single_13 (v : ℕ) (hv : v ∈ List.range 137) : SingleAt 13 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 13 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_13_0 single_13_4) (join 8 4 4 single_13_8 single_13_12)) (join 16 8 8 (join 16 4 4 single_13_16 single_13_20) (join 24 4 4 single_13_24 single_13_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 single_13_32 single_13_36) (join 40 4 4 single_13_40 single_13_44)) (join 48 8 12 (join 48 4 4 single_13_48 single_13_52) (join 56 4 8 single_13_56 (join 60 4 4 single_13_60 single_13_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 single_13_68 single_13_72) (join 76 4 4 single_13_76 single_13_80)) (join 84 8 12 (join 84 4 4 single_13_84 single_13_88) (join 92 4 8 single_13_92 (join 96 4 4 single_13_96 single_13_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 single_13_104 single_13_108) (join 112 4 4 single_13_112 single_13_116)) (join 120 8 9 (join 120 4 4 single_13_120 single_13_124) (join 128 4 5 single_13_128 (join 132 4 1 single_13_132 single_13_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_13_0 : ∀ i ∈ List.range 4, PhaseAt 13 (0+i) := by decide +kernel

theorem phase_13_4 : ∀ i ∈ List.range 4, PhaseAt 13 (4+i) := by decide +kernel

theorem phase_13_8 : ∀ i ∈ List.range 4, PhaseAt 13 (8+i) := by decide +kernel

theorem phase_13_12 : ∀ i ∈ List.range 4, PhaseAt 13 (12+i) := by decide +kernel

theorem phase_13_16 : ∀ i ∈ List.range 4, PhaseAt 13 (16+i) := by decide +kernel

theorem phase_13_20 : ∀ i ∈ List.range 4, PhaseAt 13 (20+i) := by decide +kernel

theorem phase_13_24 : ∀ i ∈ List.range 4, PhaseAt 13 (24+i) := by decide +kernel

theorem phase_13_28 : ∀ i ∈ List.range 4, PhaseAt 13 (28+i) := by decide +kernel

theorem phase_13_32 : ∀ i ∈ List.range 4, PhaseAt 13 (32+i) := by decide +kernel

theorem phase_13_36 : ∀ i ∈ List.range 4, PhaseAt 13 (36+i) := by decide +kernel

theorem phase_13_40 : ∀ i ∈ List.range 4, PhaseAt 13 (40+i) := by decide +kernel

theorem phase_13_44 : ∀ i ∈ List.range 4, PhaseAt 13 (44+i) := by decide +kernel

theorem phase_13_48 : ∀ i ∈ List.range 4, PhaseAt 13 (48+i) := by decide +kernel

theorem phase_13_52 : ∀ i ∈ List.range 4, PhaseAt 13 (52+i) := by decide +kernel

theorem phase_13_56 : ∀ i ∈ List.range 4, PhaseAt 13 (56+i) := by decide +kernel

theorem phase_13_60 : ∀ i ∈ List.range 4, PhaseAt 13 (60+i) := by decide +kernel

theorem phase_13_64 : ∀ i ∈ List.range 4, PhaseAt 13 (64+i) := by decide +kernel

theorem phase_13_68 : ∀ i ∈ List.range 4, PhaseAt 13 (68+i) := by decide +kernel

theorem phase_13_72 : ∀ i ∈ List.range 4, PhaseAt 13 (72+i) := by decide +kernel

theorem phase_13_76 : ∀ i ∈ List.range 4, PhaseAt 13 (76+i) := by decide +kernel

theorem phase_13_80 : ∀ i ∈ List.range 4, PhaseAt 13 (80+i) := by decide +kernel

theorem phase_13_84 : ∀ i ∈ List.range 4, PhaseAt 13 (84+i) := by decide +kernel

theorem phase_13_88 : ∀ i ∈ List.range 4, PhaseAt 13 (88+i) := by decide +kernel

theorem phase_13_92 : ∀ i ∈ List.range 4, PhaseAt 13 (92+i) := by decide +kernel

theorem phase_13_96 : ∀ i ∈ List.range 4, PhaseAt 13 (96+i) := by decide +kernel

theorem phase_13_100 : ∀ i ∈ List.range 4, PhaseAt 13 (100+i) := by decide +kernel

theorem phase_13_104 : ∀ i ∈ List.range 4, PhaseAt 13 (104+i) := by decide +kernel

theorem phase_13_108 : ∀ i ∈ List.range 4, PhaseAt 13 (108+i) := by decide +kernel

theorem phase_13_112 : ∀ i ∈ List.range 4, PhaseAt 13 (112+i) := by decide +kernel

theorem phase_13_116 : ∀ i ∈ List.range 4, PhaseAt 13 (116+i) := by decide +kernel

theorem phase_13_120 : ∀ i ∈ List.range 4, PhaseAt 13 (120+i) := by decide +kernel

theorem phase_13_124 : ∀ i ∈ List.range 4, PhaseAt 13 (124+i) := by decide +kernel

theorem phase_13_128 : ∀ i ∈ List.range 4, PhaseAt 13 (128+i) := by decide +kernel

theorem phase_13_132 : ∀ i ∈ List.range 4, PhaseAt 13 (132+i) := by decide +kernel

theorem phase_13_136 : ∀ i ∈ List.range 1, PhaseAt 13 (136+i) := by decide +kernel

theorem phase_13 (v : ℕ) (hv : v ∈ List.range 137) : PhaseAt 13 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 13 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_13_0 phase_13_4) (join 8 4 4 phase_13_8 phase_13_12)) (join 16 8 8 (join 16 4 4 phase_13_16 phase_13_20) (join 24 4 4 phase_13_24 phase_13_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_13_32 phase_13_36) (join 40 4 4 phase_13_40 phase_13_44)) (join 48 8 12 (join 48 4 4 phase_13_48 phase_13_52) (join 56 4 8 phase_13_56 (join 60 4 4 phase_13_60 phase_13_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 phase_13_68 phase_13_72) (join 76 4 4 phase_13_76 phase_13_80)) (join 84 8 12 (join 84 4 4 phase_13_84 phase_13_88) (join 92 4 8 phase_13_92 (join 96 4 4 phase_13_96 phase_13_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 phase_13_104 phase_13_108) (join 112 4 4 phase_13_112 phase_13_116)) (join 120 8 9 (join 120 4 4 phase_13_120 phase_13_124) (join 128 4 5 phase_13_128 (join 132 4 1 phase_13_132 phase_13_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_13_0 : ∀ i ∈ List.range 1, ThresholdAt 13 (0+i) := by decide +kernel

theorem threshold_13_1 : ∀ i ∈ List.range 1, ThresholdAt 13 (1+i) := by decide +kernel

theorem threshold_13_2 : ∀ i ∈ List.range 1, ThresholdAt 13 (2+i) := by decide +kernel

theorem threshold_13_3 : ∀ i ∈ List.range 1, ThresholdAt 13 (3+i) := by decide +kernel

theorem threshold_13_4 : ∀ i ∈ List.range 1, ThresholdAt 13 (4+i) := by decide +kernel

theorem threshold_13_5 : ∀ i ∈ List.range 1, ThresholdAt 13 (5+i) := by decide +kernel

theorem threshold_13_6 : ∀ i ∈ List.range 1, ThresholdAt 13 (6+i) := by decide +kernel

theorem threshold_13_7 : ∀ i ∈ List.range 1, ThresholdAt 13 (7+i) := by decide +kernel

theorem threshold_13_8 : ∀ i ∈ List.range 1, ThresholdAt 13 (8+i) := by decide +kernel

theorem threshold_13_9 : ∀ i ∈ List.range 1, ThresholdAt 13 (9+i) := by decide +kernel

theorem threshold_13_10 : ∀ i ∈ List.range 1, ThresholdAt 13 (10+i) := by decide +kernel

theorem threshold_13_11 : ∀ i ∈ List.range 1, ThresholdAt 13 (11+i) := by decide +kernel

theorem threshold_13_12 : ∀ i ∈ List.range 1, ThresholdAt 13 (12+i) := by decide +kernel

theorem threshold_13_13 : ∀ i ∈ List.range 1, ThresholdAt 13 (13+i) := by decide +kernel

theorem threshold_13_14 : ∀ i ∈ List.range 1, ThresholdAt 13 (14+i) := by decide +kernel

theorem threshold_13_15 : ∀ i ∈ List.range 1, ThresholdAt 13 (15+i) := by decide +kernel

theorem threshold_13_16 : ∀ i ∈ List.range 1, ThresholdAt 13 (16+i) := by decide +kernel

theorem threshold_13_17 : ∀ i ∈ List.range 1, ThresholdAt 13 (17+i) := by decide +kernel

theorem threshold_13_18 : ∀ i ∈ List.range 1, ThresholdAt 13 (18+i) := by decide +kernel

theorem threshold_13_19 : ∀ i ∈ List.range 1, ThresholdAt 13 (19+i) := by decide +kernel

theorem threshold_13_20 : ∀ i ∈ List.range 1, ThresholdAt 13 (20+i) := by decide +kernel

theorem threshold_13_21 : ∀ i ∈ List.range 1, ThresholdAt 13 (21+i) := by decide +kernel

theorem threshold_13_22 : ∀ i ∈ List.range 1, ThresholdAt 13 (22+i) := by decide +kernel

theorem threshold_13_23 : ∀ i ∈ List.range 1, ThresholdAt 13 (23+i) := by decide +kernel

theorem threshold_13_24 : ∀ i ∈ List.range 1, ThresholdAt 13 (24+i) := by decide +kernel

theorem threshold_13_25 : ∀ i ∈ List.range 1, ThresholdAt 13 (25+i) := by decide +kernel

theorem threshold_13_26 : ∀ i ∈ List.range 1, ThresholdAt 13 (26+i) := by decide +kernel

theorem threshold_13_27 : ∀ i ∈ List.range 1, ThresholdAt 13 (27+i) := by decide +kernel

theorem threshold_13_28 : ∀ i ∈ List.range 1, ThresholdAt 13 (28+i) := by decide +kernel

theorem threshold_13_29 : ∀ i ∈ List.range 1, ThresholdAt 13 (29+i) := by decide +kernel

theorem threshold_13_30 : ∀ i ∈ List.range 1, ThresholdAt 13 (30+i) := by decide +kernel

theorem threshold_13_31 : ∀ i ∈ List.range 1, ThresholdAt 13 (31+i) := by decide +kernel

theorem threshold_13_32 : ∀ i ∈ List.range 1, ThresholdAt 13 (32+i) := by decide +kernel

theorem threshold_13_33 : ∀ i ∈ List.range 1, ThresholdAt 13 (33+i) := by decide +kernel

theorem threshold_13_34 : ∀ i ∈ List.range 1, ThresholdAt 13 (34+i) := by decide +kernel

theorem threshold_13_35 : ∀ i ∈ List.range 1, ThresholdAt 13 (35+i) := by decide +kernel

theorem threshold_13_36 : ∀ i ∈ List.range 1, ThresholdAt 13 (36+i) := by decide +kernel

theorem threshold_13_37 : ∀ i ∈ List.range 1, ThresholdAt 13 (37+i) := by decide +kernel

theorem threshold_13_38 : ∀ i ∈ List.range 1, ThresholdAt 13 (38+i) := by decide +kernel

theorem threshold_13_39 : ∀ i ∈ List.range 1, ThresholdAt 13 (39+i) := by decide +kernel

theorem threshold_13_40 : ∀ i ∈ List.range 1, ThresholdAt 13 (40+i) := by decide +kernel

theorem threshold_13_41 : ∀ i ∈ List.range 1, ThresholdAt 13 (41+i) := by decide +kernel

theorem threshold_13_42 : ∀ i ∈ List.range 1, ThresholdAt 13 (42+i) := by decide +kernel

theorem threshold_13_43 : ∀ i ∈ List.range 1, ThresholdAt 13 (43+i) := by decide +kernel

theorem threshold_13_44 : ∀ i ∈ List.range 1, ThresholdAt 13 (44+i) := by decide +kernel

theorem threshold_13_45 : ∀ i ∈ List.range 1, ThresholdAt 13 (45+i) := by decide +kernel

theorem threshold_13_46 : ∀ i ∈ List.range 1, ThresholdAt 13 (46+i) := by decide +kernel

theorem threshold_13_47 : ∀ i ∈ List.range 1, ThresholdAt 13 (47+i) := by decide +kernel

theorem threshold_13_48 : ∀ i ∈ List.range 1, ThresholdAt 13 (48+i) := by decide +kernel

theorem threshold_13_49 : ∀ i ∈ List.range 1, ThresholdAt 13 (49+i) := by decide +kernel

theorem threshold_13_50 : ∀ i ∈ List.range 1, ThresholdAt 13 (50+i) := by decide +kernel

theorem threshold_13_51 : ∀ i ∈ List.range 1, ThresholdAt 13 (51+i) := by decide +kernel

theorem threshold_13_52 : ∀ i ∈ List.range 1, ThresholdAt 13 (52+i) := by decide +kernel

theorem threshold_13_53 : ∀ i ∈ List.range 1, ThresholdAt 13 (53+i) := by decide +kernel

theorem threshold_13_54 : ∀ i ∈ List.range 1, ThresholdAt 13 (54+i) := by decide +kernel

theorem threshold_13_55 : ∀ i ∈ List.range 1, ThresholdAt 13 (55+i) := by decide +kernel

theorem threshold_13_56 : ∀ i ∈ List.range 1, ThresholdAt 13 (56+i) := by decide +kernel

theorem threshold_13_57 : ∀ i ∈ List.range 1, ThresholdAt 13 (57+i) := by decide +kernel

theorem threshold_13_58 : ∀ i ∈ List.range 1, ThresholdAt 13 (58+i) := by decide +kernel

theorem threshold_13_59 : ∀ i ∈ List.range 1, ThresholdAt 13 (59+i) := by decide +kernel

theorem threshold_13_60 : ∀ i ∈ List.range 1, ThresholdAt 13 (60+i) := by decide +kernel

theorem threshold_13_61 : ∀ i ∈ List.range 1, ThresholdAt 13 (61+i) := by decide +kernel

theorem threshold_13_62 : ∀ i ∈ List.range 1, ThresholdAt 13 (62+i) := by decide +kernel

theorem threshold_13_63 : ∀ i ∈ List.range 1, ThresholdAt 13 (63+i) := by decide +kernel

theorem threshold_13_64 : ∀ i ∈ List.range 1, ThresholdAt 13 (64+i) := by decide +kernel

theorem threshold_13_65 : ∀ i ∈ List.range 1, ThresholdAt 13 (65+i) := by decide +kernel

theorem threshold_13_66 : ∀ i ∈ List.range 1, ThresholdAt 13 (66+i) := by decide +kernel

theorem threshold_13_67 : ∀ i ∈ List.range 1, ThresholdAt 13 (67+i) := by decide +kernel

theorem threshold_13_68 : ∀ i ∈ List.range 1, ThresholdAt 13 (68+i) := by decide +kernel

theorem threshold_13_69 : ∀ i ∈ List.range 1, ThresholdAt 13 (69+i) := by decide +kernel

theorem threshold_13_70 : ∀ i ∈ List.range 1, ThresholdAt 13 (70+i) := by decide +kernel

theorem threshold_13_71 : ∀ i ∈ List.range 1, ThresholdAt 13 (71+i) := by decide +kernel

theorem threshold_13_72 : ∀ i ∈ List.range 1, ThresholdAt 13 (72+i) := by decide +kernel

theorem threshold_13_73 : ∀ i ∈ List.range 1, ThresholdAt 13 (73+i) := by decide +kernel

theorem threshold_13_74 : ∀ i ∈ List.range 1, ThresholdAt 13 (74+i) := by decide +kernel

theorem threshold_13_75 : ∀ i ∈ List.range 1, ThresholdAt 13 (75+i) := by decide +kernel

theorem threshold_13_76 : ∀ i ∈ List.range 1, ThresholdAt 13 (76+i) := by decide +kernel

theorem threshold_13_77 : ∀ i ∈ List.range 1, ThresholdAt 13 (77+i) := by decide +kernel

theorem threshold_13_78 : ∀ i ∈ List.range 1, ThresholdAt 13 (78+i) := by decide +kernel

theorem threshold_13_79 : ∀ i ∈ List.range 1, ThresholdAt 13 (79+i) := by decide +kernel

theorem threshold_13_80 : ∀ i ∈ List.range 1, ThresholdAt 13 (80+i) := by decide +kernel

theorem threshold_13_81 : ∀ i ∈ List.range 1, ThresholdAt 13 (81+i) := by decide +kernel

theorem threshold_13_82 : ∀ i ∈ List.range 1, ThresholdAt 13 (82+i) := by decide +kernel

theorem threshold_13_83 : ∀ i ∈ List.range 1, ThresholdAt 13 (83+i) := by decide +kernel

theorem threshold_13_84 : ∀ i ∈ List.range 1, ThresholdAt 13 (84+i) := by decide +kernel

theorem threshold_13_85 : ∀ i ∈ List.range 1, ThresholdAt 13 (85+i) := by decide +kernel

theorem threshold_13_86 : ∀ i ∈ List.range 1, ThresholdAt 13 (86+i) := by decide +kernel

theorem threshold_13_87 : ∀ i ∈ List.range 1, ThresholdAt 13 (87+i) := by decide +kernel

theorem threshold_13_88 : ∀ i ∈ List.range 1, ThresholdAt 13 (88+i) := by decide +kernel

theorem threshold_13_89 : ∀ i ∈ List.range 1, ThresholdAt 13 (89+i) := by decide +kernel

theorem threshold_13_90 : ∀ i ∈ List.range 1, ThresholdAt 13 (90+i) := by decide +kernel

theorem threshold_13_91 : ∀ i ∈ List.range 1, ThresholdAt 13 (91+i) := by decide +kernel

theorem threshold_13_92 : ∀ i ∈ List.range 1, ThresholdAt 13 (92+i) := by decide +kernel

theorem threshold_13_93 : ∀ i ∈ List.range 1, ThresholdAt 13 (93+i) := by decide +kernel

theorem threshold_13_94 : ∀ i ∈ List.range 1, ThresholdAt 13 (94+i) := by decide +kernel

theorem threshold_13_95 : ∀ i ∈ List.range 1, ThresholdAt 13 (95+i) := by decide +kernel

theorem threshold_13_96 : ∀ i ∈ List.range 1, ThresholdAt 13 (96+i) := by decide +kernel

theorem threshold_13_97 : ∀ i ∈ List.range 1, ThresholdAt 13 (97+i) := by decide +kernel

theorem threshold_13_98 : ∀ i ∈ List.range 1, ThresholdAt 13 (98+i) := by decide +kernel

theorem threshold_13_99 : ∀ i ∈ List.range 1, ThresholdAt 13 (99+i) := by decide +kernel

theorem threshold_13_100 : ∀ i ∈ List.range 1, ThresholdAt 13 (100+i) := by decide +kernel

theorem threshold_13_101 : ∀ i ∈ List.range 1, ThresholdAt 13 (101+i) := by decide +kernel

theorem threshold_13_102 : ∀ i ∈ List.range 1, ThresholdAt 13 (102+i) := by decide +kernel

theorem threshold_13_103 : ∀ i ∈ List.range 1, ThresholdAt 13 (103+i) := by decide +kernel

theorem threshold_13_104 : ∀ i ∈ List.range 1, ThresholdAt 13 (104+i) := by decide +kernel

theorem threshold_13_105 : ∀ i ∈ List.range 1, ThresholdAt 13 (105+i) := by decide +kernel

theorem threshold_13_106 : ∀ i ∈ List.range 1, ThresholdAt 13 (106+i) := by decide +kernel

theorem threshold_13_107 : ∀ i ∈ List.range 1, ThresholdAt 13 (107+i) := by decide +kernel

theorem threshold_13_108 : ∀ i ∈ List.range 1, ThresholdAt 13 (108+i) := by decide +kernel

theorem threshold_13_109 : ∀ i ∈ List.range 1, ThresholdAt 13 (109+i) := by decide +kernel

theorem threshold_13_110 : ∀ i ∈ List.range 1, ThresholdAt 13 (110+i) := by decide +kernel

theorem threshold_13_111 : ∀ i ∈ List.range 1, ThresholdAt 13 (111+i) := by decide +kernel

theorem threshold_13_112 : ∀ i ∈ List.range 1, ThresholdAt 13 (112+i) := by decide +kernel

theorem threshold_13_113 : ∀ i ∈ List.range 1, ThresholdAt 13 (113+i) := by decide +kernel

theorem threshold_13_114 : ∀ i ∈ List.range 1, ThresholdAt 13 (114+i) := by decide +kernel

theorem threshold_13_115 : ∀ i ∈ List.range 1, ThresholdAt 13 (115+i) := by decide +kernel

theorem threshold_13_116 : ∀ i ∈ List.range 1, ThresholdAt 13 (116+i) := by decide +kernel

theorem threshold_13_117 : ∀ i ∈ List.range 1, ThresholdAt 13 (117+i) := by decide +kernel

theorem threshold_13_118 : ∀ i ∈ List.range 1, ThresholdAt 13 (118+i) := by decide +kernel

theorem threshold_13_119 : ∀ i ∈ List.range 1, ThresholdAt 13 (119+i) := by decide +kernel

theorem threshold_13_120 : ∀ i ∈ List.range 1, ThresholdAt 13 (120+i) := by decide +kernel

theorem threshold_13_121 : ∀ i ∈ List.range 1, ThresholdAt 13 (121+i) := by decide +kernel

theorem threshold_13_122 : ∀ i ∈ List.range 1, ThresholdAt 13 (122+i) := by decide +kernel

theorem threshold_13_123 : ∀ i ∈ List.range 1, ThresholdAt 13 (123+i) := by decide +kernel

theorem threshold_13_124 : ∀ i ∈ List.range 1, ThresholdAt 13 (124+i) := by decide +kernel

theorem threshold_13_125 : ∀ i ∈ List.range 1, ThresholdAt 13 (125+i) := by decide +kernel

theorem threshold_13_126 : ∀ i ∈ List.range 1, ThresholdAt 13 (126+i) := by decide +kernel

theorem threshold_13_127 : ∀ i ∈ List.range 1, ThresholdAt 13 (127+i) := by decide +kernel

theorem threshold_13_128 : ∀ i ∈ List.range 1, ThresholdAt 13 (128+i) := by decide +kernel

theorem threshold_13_129 : ∀ i ∈ List.range 1, ThresholdAt 13 (129+i) := by decide +kernel

theorem threshold_13_130 : ∀ i ∈ List.range 1, ThresholdAt 13 (130+i) := by decide +kernel

theorem threshold_13_131 : ∀ i ∈ List.range 1, ThresholdAt 13 (131+i) := by decide +kernel

theorem threshold_13_132 : ∀ i ∈ List.range 1, ThresholdAt 13 (132+i) := by decide +kernel

theorem threshold_13_133 : ∀ i ∈ List.range 1, ThresholdAt 13 (133+i) := by decide +kernel

theorem threshold_13_134 : ∀ i ∈ List.range 1, ThresholdAt 13 (134+i) := by decide +kernel

theorem threshold_13_135 : ∀ i ∈ List.range 1, ThresholdAt 13 (135+i) := by decide +kernel

theorem threshold_13_136 : ∀ i ∈ List.range 1, ThresholdAt 13 (136+i) := by decide +kernel

theorem threshold_13 (v : ℕ) (hv : v ∈ List.range 137) : ThresholdAt 13 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 13 v)
  have h := (join 0 68 69 (join 0 34 34 (join 0 17 17 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_13_0 threshold_13_1) (join 2 1 1 threshold_13_2 threshold_13_3)) (join 4 2 2 (join 4 1 1 threshold_13_4 threshold_13_5) (join 6 1 1 threshold_13_6 threshold_13_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_13_8 threshold_13_9) (join 10 1 1 threshold_13_10 threshold_13_11)) (join 12 2 3 (join 12 1 1 threshold_13_12 threshold_13_13) (join 14 1 2 threshold_13_14 (join 15 1 1 threshold_13_15 threshold_13_16))))) (join 17 8 9 (join 17 4 4 (join 17 2 2 (join 17 1 1 threshold_13_17 threshold_13_18) (join 19 1 1 threshold_13_19 threshold_13_20)) (join 21 2 2 (join 21 1 1 threshold_13_21 threshold_13_22) (join 23 1 1 threshold_13_23 threshold_13_24))) (join 25 4 5 (join 25 2 2 (join 25 1 1 threshold_13_25 threshold_13_26) (join 27 1 1 threshold_13_27 threshold_13_28)) (join 29 2 3 (join 29 1 1 threshold_13_29 threshold_13_30) (join 31 1 2 threshold_13_31 (join 32 1 1 threshold_13_32 threshold_13_33)))))) (join 34 17 17 (join 34 8 9 (join 34 4 4 (join 34 2 2 (join 34 1 1 threshold_13_34 threshold_13_35) (join 36 1 1 threshold_13_36 threshold_13_37)) (join 38 2 2 (join 38 1 1 threshold_13_38 threshold_13_39) (join 40 1 1 threshold_13_40 threshold_13_41))) (join 42 4 5 (join 42 2 2 (join 42 1 1 threshold_13_42 threshold_13_43) (join 44 1 1 threshold_13_44 threshold_13_45)) (join 46 2 3 (join 46 1 1 threshold_13_46 threshold_13_47) (join 48 1 2 threshold_13_48 (join 49 1 1 threshold_13_49 threshold_13_50))))) (join 51 8 9 (join 51 4 4 (join 51 2 2 (join 51 1 1 threshold_13_51 threshold_13_52) (join 53 1 1 threshold_13_53 threshold_13_54)) (join 55 2 2 (join 55 1 1 threshold_13_55 threshold_13_56) (join 57 1 1 threshold_13_57 threshold_13_58))) (join 59 4 5 (join 59 2 2 (join 59 1 1 threshold_13_59 threshold_13_60) (join 61 1 1 threshold_13_61 threshold_13_62)) (join 63 2 3 (join 63 1 1 threshold_13_63 threshold_13_64) (join 65 1 2 threshold_13_65 (join 66 1 1 threshold_13_66 threshold_13_67))))))) (join 68 34 35 (join 68 17 17 (join 68 8 9 (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_13_68 threshold_13_69) (join 70 1 1 threshold_13_70 threshold_13_71)) (join 72 2 2 (join 72 1 1 threshold_13_72 threshold_13_73) (join 74 1 1 threshold_13_74 threshold_13_75))) (join 76 4 5 (join 76 2 2 (join 76 1 1 threshold_13_76 threshold_13_77) (join 78 1 1 threshold_13_78 threshold_13_79)) (join 80 2 3 (join 80 1 1 threshold_13_80 threshold_13_81) (join 82 1 2 threshold_13_82 (join 83 1 1 threshold_13_83 threshold_13_84))))) (join 85 8 9 (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_13_85 threshold_13_86) (join 87 1 1 threshold_13_87 threshold_13_88)) (join 89 2 2 (join 89 1 1 threshold_13_89 threshold_13_90) (join 91 1 1 threshold_13_91 threshold_13_92))) (join 93 4 5 (join 93 2 2 (join 93 1 1 threshold_13_93 threshold_13_94) (join 95 1 1 threshold_13_95 threshold_13_96)) (join 97 2 3 (join 97 1 1 threshold_13_97 threshold_13_98) (join 99 1 2 threshold_13_99 (join 100 1 1 threshold_13_100 threshold_13_101)))))) (join 102 17 18 (join 102 8 9 (join 102 4 4 (join 102 2 2 (join 102 1 1 threshold_13_102 threshold_13_103) (join 104 1 1 threshold_13_104 threshold_13_105)) (join 106 2 2 (join 106 1 1 threshold_13_106 threshold_13_107) (join 108 1 1 threshold_13_108 threshold_13_109))) (join 110 4 5 (join 110 2 2 (join 110 1 1 threshold_13_110 threshold_13_111) (join 112 1 1 threshold_13_112 threshold_13_113)) (join 114 2 3 (join 114 1 1 threshold_13_114 threshold_13_115) (join 116 1 2 threshold_13_116 (join 117 1 1 threshold_13_117 threshold_13_118))))) (join 119 9 9 (join 119 4 5 (join 119 2 2 (join 119 1 1 threshold_13_119 threshold_13_120) (join 121 1 1 threshold_13_121 threshold_13_122)) (join 123 2 3 (join 123 1 1 threshold_13_123 threshold_13_124) (join 125 1 2 threshold_13_125 (join 126 1 1 threshold_13_126 threshold_13_127)))) (join 128 4 5 (join 128 2 2 (join 128 1 1 threshold_13_128 threshold_13_129) (join 130 1 1 threshold_13_130 threshold_13_131)) (join 132 2 3 (join 132 1 1 threshold_13_132 threshold_13_133) (join 134 1 2 threshold_13_134 (join 135 1 1 threshold_13_135 threshold_13_136))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_13_0 : ∀ i ∈ List.range 4, LedgerAt 13 (0+i) := by decide +kernel

theorem ledger_13_4 : ∀ i ∈ List.range 4, LedgerAt 13 (4+i) := by decide +kernel

theorem ledger_13_8 : ∀ i ∈ List.range 4, LedgerAt 13 (8+i) := by decide +kernel

theorem ledger_13_12 : ∀ i ∈ List.range 4, LedgerAt 13 (12+i) := by decide +kernel

theorem ledger_13_16 : ∀ i ∈ List.range 4, LedgerAt 13 (16+i) := by decide +kernel

theorem ledger_13_20 : ∀ i ∈ List.range 4, LedgerAt 13 (20+i) := by decide +kernel

theorem ledger_13_24 : ∀ i ∈ List.range 4, LedgerAt 13 (24+i) := by decide +kernel

theorem ledger_13_28 : ∀ i ∈ List.range 4, LedgerAt 13 (28+i) := by decide +kernel

theorem ledger_13_32 : ∀ i ∈ List.range 4, LedgerAt 13 (32+i) := by decide +kernel

theorem ledger_13_36 : ∀ i ∈ List.range 4, LedgerAt 13 (36+i) := by decide +kernel

theorem ledger_13_40 : ∀ i ∈ List.range 4, LedgerAt 13 (40+i) := by decide +kernel

theorem ledger_13_44 : ∀ i ∈ List.range 4, LedgerAt 13 (44+i) := by decide +kernel

theorem ledger_13_48 : ∀ i ∈ List.range 4, LedgerAt 13 (48+i) := by decide +kernel

theorem ledger_13_52 : ∀ i ∈ List.range 4, LedgerAt 13 (52+i) := by decide +kernel

theorem ledger_13_56 : ∀ i ∈ List.range 4, LedgerAt 13 (56+i) := by decide +kernel

theorem ledger_13_60 : ∀ i ∈ List.range 4, LedgerAt 13 (60+i) := by decide +kernel

theorem ledger_13_64 : ∀ i ∈ List.range 4, LedgerAt 13 (64+i) := by decide +kernel

theorem ledger_13_68 : ∀ i ∈ List.range 4, LedgerAt 13 (68+i) := by decide +kernel

theorem ledger_13_72 : ∀ i ∈ List.range 4, LedgerAt 13 (72+i) := by decide +kernel

theorem ledger_13_76 : ∀ i ∈ List.range 4, LedgerAt 13 (76+i) := by decide +kernel

theorem ledger_13_80 : ∀ i ∈ List.range 4, LedgerAt 13 (80+i) := by decide +kernel

theorem ledger_13_84 : ∀ i ∈ List.range 4, LedgerAt 13 (84+i) := by decide +kernel

theorem ledger_13_88 : ∀ i ∈ List.range 4, LedgerAt 13 (88+i) := by decide +kernel

theorem ledger_13_92 : ∀ i ∈ List.range 4, LedgerAt 13 (92+i) := by decide +kernel

theorem ledger_13_96 : ∀ i ∈ List.range 4, LedgerAt 13 (96+i) := by decide +kernel

theorem ledger_13_100 : ∀ i ∈ List.range 4, LedgerAt 13 (100+i) := by decide +kernel

theorem ledger_13_104 : ∀ i ∈ List.range 4, LedgerAt 13 (104+i) := by decide +kernel

theorem ledger_13_108 : ∀ i ∈ List.range 4, LedgerAt 13 (108+i) := by decide +kernel

theorem ledger_13_112 : ∀ i ∈ List.range 4, LedgerAt 13 (112+i) := by decide +kernel

theorem ledger_13_116 : ∀ i ∈ List.range 4, LedgerAt 13 (116+i) := by decide +kernel

theorem ledger_13_120 : ∀ i ∈ List.range 4, LedgerAt 13 (120+i) := by decide +kernel

theorem ledger_13_124 : ∀ i ∈ List.range 4, LedgerAt 13 (124+i) := by decide +kernel

theorem ledger_13_128 : ∀ i ∈ List.range 4, LedgerAt 13 (128+i) := by decide +kernel

theorem ledger_13_132 : ∀ i ∈ List.range 4, LedgerAt 13 (132+i) := by decide +kernel

theorem ledger_13_136 : ∀ i ∈ List.range 1, LedgerAt 13 (136+i) := by decide +kernel

theorem ledger_13 (v : ℕ) (hv : v ∈ List.range 137) : LedgerAt 13 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 13 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_13_0 ledger_13_4) (join 8 4 4 ledger_13_8 ledger_13_12)) (join 16 8 8 (join 16 4 4 ledger_13_16 ledger_13_20) (join 24 4 4 ledger_13_24 ledger_13_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_13_32 ledger_13_36) (join 40 4 4 ledger_13_40 ledger_13_44)) (join 48 8 12 (join 48 4 4 ledger_13_48 ledger_13_52) (join 56 4 8 ledger_13_56 (join 60 4 4 ledger_13_60 ledger_13_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 ledger_13_68 ledger_13_72) (join 76 4 4 ledger_13_76 ledger_13_80)) (join 84 8 12 (join 84 4 4 ledger_13_84 ledger_13_88) (join 92 4 8 ledger_13_92 (join 96 4 4 ledger_13_96 ledger_13_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 ledger_13_104 ledger_13_108) (join 112 4 4 ledger_13_112 ledger_13_116)) (join 120 8 9 (join 120 4 4 ledger_13_120 ledger_13_124) (join 128 4 5 ledger_13_128 (join 132 4 1 ledger_13_132 ledger_13_136))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
