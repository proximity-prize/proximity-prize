import ProximityPrize.SubmissionLower.AffineCheckedR096808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_10_0 : ∀ i ∈ List.range 4, SingleAt 10 (0+i) := by decide +kernel

theorem single_10_4 : ∀ i ∈ List.range 4, SingleAt 10 (4+i) := by decide +kernel

theorem single_10_8 : ∀ i ∈ List.range 4, SingleAt 10 (8+i) := by decide +kernel

theorem single_10_12 : ∀ i ∈ List.range 4, SingleAt 10 (12+i) := by decide +kernel

theorem single_10_16 : ∀ i ∈ List.range 4, SingleAt 10 (16+i) := by decide +kernel

theorem single_10_20 : ∀ i ∈ List.range 4, SingleAt 10 (20+i) := by decide +kernel

theorem single_10_24 : ∀ i ∈ List.range 4, SingleAt 10 (24+i) := by decide +kernel

theorem single_10_28 : ∀ i ∈ List.range 4, SingleAt 10 (28+i) := by decide +kernel

theorem single_10_32 : ∀ i ∈ List.range 4, SingleAt 10 (32+i) := by decide +kernel

theorem single_10_36 : ∀ i ∈ List.range 4, SingleAt 10 (36+i) := by decide +kernel

theorem single_10_40 : ∀ i ∈ List.range 4, SingleAt 10 (40+i) := by decide +kernel

theorem single_10_44 : ∀ i ∈ List.range 4, SingleAt 10 (44+i) := by decide +kernel

theorem single_10_48 : ∀ i ∈ List.range 4, SingleAt 10 (48+i) := by decide +kernel

theorem single_10_52 : ∀ i ∈ List.range 4, SingleAt 10 (52+i) := by decide +kernel

theorem single_10_56 : ∀ i ∈ List.range 4, SingleAt 10 (56+i) := by decide +kernel

theorem single_10_60 : ∀ i ∈ List.range 4, SingleAt 10 (60+i) := by decide +kernel

theorem single_10_64 : ∀ i ∈ List.range 4, SingleAt 10 (64+i) := by decide +kernel

theorem single_10_68 : ∀ i ∈ List.range 4, SingleAt 10 (68+i) := by decide +kernel

theorem single_10_72 : ∀ i ∈ List.range 4, SingleAt 10 (72+i) := by decide +kernel

theorem single_10_76 : ∀ i ∈ List.range 4, SingleAt 10 (76+i) := by decide +kernel

theorem single_10_80 : ∀ i ∈ List.range 4, SingleAt 10 (80+i) := by decide +kernel

theorem single_10_84 : ∀ i ∈ List.range 4, SingleAt 10 (84+i) := by decide +kernel

theorem single_10_88 : ∀ i ∈ List.range 4, SingleAt 10 (88+i) := by decide +kernel

theorem single_10_92 : ∀ i ∈ List.range 4, SingleAt 10 (92+i) := by decide +kernel

theorem single_10_96 : ∀ i ∈ List.range 4, SingleAt 10 (96+i) := by decide +kernel

theorem single_10_100 : ∀ i ∈ List.range 4, SingleAt 10 (100+i) := by decide +kernel

theorem single_10_104 : ∀ i ∈ List.range 4, SingleAt 10 (104+i) := by decide +kernel

theorem single_10_108 : ∀ i ∈ List.range 4, SingleAt 10 (108+i) := by decide +kernel

theorem single_10_112 : ∀ i ∈ List.range 4, SingleAt 10 (112+i) := by decide +kernel

theorem single_10_116 : ∀ i ∈ List.range 4, SingleAt 10 (116+i) := by decide +kernel

theorem single_10_120 : ∀ i ∈ List.range 4, SingleAt 10 (120+i) := by decide +kernel

theorem single_10_124 : ∀ i ∈ List.range 4, SingleAt 10 (124+i) := by decide +kernel

theorem single_10_128 : ∀ i ∈ List.range 4, SingleAt 10 (128+i) := by decide +kernel

theorem single_10_132 : ∀ i ∈ List.range 4, SingleAt 10 (132+i) := by decide +kernel

theorem single_10_136 : ∀ i ∈ List.range 4, SingleAt 10 (136+i) := by decide +kernel

theorem single_10 (v : ℕ) (hv : v ∈ List.range 140) : SingleAt 10 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 10 v)
  have h := (join 0 68 72 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_10_0 single_10_4) (join 8 4 4 single_10_8 single_10_12)) (join 16 8 8 (join 16 4 4 single_10_16 single_10_20) (join 24 4 4 single_10_24 single_10_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 single_10_32 single_10_36) (join 40 4 4 single_10_40 single_10_44)) (join 48 8 12 (join 48 4 4 single_10_48 single_10_52) (join 56 4 8 single_10_56 (join 60 4 4 single_10_60 single_10_64))))) (join 68 36 36 (join 68 16 20 (join 68 8 8 (join 68 4 4 single_10_68 single_10_72) (join 76 4 4 single_10_76 single_10_80)) (join 84 8 12 (join 84 4 4 single_10_84 single_10_88) (join 92 4 8 single_10_92 (join 96 4 4 single_10_96 single_10_100)))) (join 104 16 20 (join 104 8 8 (join 104 4 4 single_10_104 single_10_108) (join 112 4 4 single_10_112 single_10_116)) (join 120 8 12 (join 120 4 4 single_10_120 single_10_124) (join 128 4 8 single_10_128 (join 132 4 4 single_10_132 single_10_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_10_0 : ∀ i ∈ List.range 4, PhaseAt 10 (0+i) := by decide +kernel

theorem phase_10_4 : ∀ i ∈ List.range 4, PhaseAt 10 (4+i) := by decide +kernel

theorem phase_10_8 : ∀ i ∈ List.range 4, PhaseAt 10 (8+i) := by decide +kernel

theorem phase_10_12 : ∀ i ∈ List.range 4, PhaseAt 10 (12+i) := by decide +kernel

theorem phase_10_16 : ∀ i ∈ List.range 4, PhaseAt 10 (16+i) := by decide +kernel

theorem phase_10_20 : ∀ i ∈ List.range 4, PhaseAt 10 (20+i) := by decide +kernel

theorem phase_10_24 : ∀ i ∈ List.range 4, PhaseAt 10 (24+i) := by decide +kernel

theorem phase_10_28 : ∀ i ∈ List.range 4, PhaseAt 10 (28+i) := by decide +kernel

theorem phase_10_32 : ∀ i ∈ List.range 4, PhaseAt 10 (32+i) := by decide +kernel

theorem phase_10_36 : ∀ i ∈ List.range 4, PhaseAt 10 (36+i) := by decide +kernel

theorem phase_10_40 : ∀ i ∈ List.range 4, PhaseAt 10 (40+i) := by decide +kernel

theorem phase_10_44 : ∀ i ∈ List.range 4, PhaseAt 10 (44+i) := by decide +kernel

theorem phase_10_48 : ∀ i ∈ List.range 4, PhaseAt 10 (48+i) := by decide +kernel

theorem phase_10_52 : ∀ i ∈ List.range 4, PhaseAt 10 (52+i) := by decide +kernel

theorem phase_10_56 : ∀ i ∈ List.range 4, PhaseAt 10 (56+i) := by decide +kernel

theorem phase_10_60 : ∀ i ∈ List.range 4, PhaseAt 10 (60+i) := by decide +kernel

theorem phase_10_64 : ∀ i ∈ List.range 4, PhaseAt 10 (64+i) := by decide +kernel

theorem phase_10_68 : ∀ i ∈ List.range 4, PhaseAt 10 (68+i) := by decide +kernel

theorem phase_10_72 : ∀ i ∈ List.range 4, PhaseAt 10 (72+i) := by decide +kernel

theorem phase_10_76 : ∀ i ∈ List.range 4, PhaseAt 10 (76+i) := by decide +kernel

theorem phase_10_80 : ∀ i ∈ List.range 4, PhaseAt 10 (80+i) := by decide +kernel

theorem phase_10_84 : ∀ i ∈ List.range 4, PhaseAt 10 (84+i) := by decide +kernel

theorem phase_10_88 : ∀ i ∈ List.range 4, PhaseAt 10 (88+i) := by decide +kernel

theorem phase_10_92 : ∀ i ∈ List.range 4, PhaseAt 10 (92+i) := by decide +kernel

theorem phase_10_96 : ∀ i ∈ List.range 4, PhaseAt 10 (96+i) := by decide +kernel

theorem phase_10_100 : ∀ i ∈ List.range 4, PhaseAt 10 (100+i) := by decide +kernel

theorem phase_10_104 : ∀ i ∈ List.range 4, PhaseAt 10 (104+i) := by decide +kernel

theorem phase_10_108 : ∀ i ∈ List.range 4, PhaseAt 10 (108+i) := by decide +kernel

theorem phase_10_112 : ∀ i ∈ List.range 4, PhaseAt 10 (112+i) := by decide +kernel

theorem phase_10_116 : ∀ i ∈ List.range 4, PhaseAt 10 (116+i) := by decide +kernel

theorem phase_10_120 : ∀ i ∈ List.range 4, PhaseAt 10 (120+i) := by decide +kernel

theorem phase_10_124 : ∀ i ∈ List.range 4, PhaseAt 10 (124+i) := by decide +kernel

theorem phase_10_128 : ∀ i ∈ List.range 4, PhaseAt 10 (128+i) := by decide +kernel

theorem phase_10_132 : ∀ i ∈ List.range 4, PhaseAt 10 (132+i) := by decide +kernel

theorem phase_10_136 : ∀ i ∈ List.range 4, PhaseAt 10 (136+i) := by decide +kernel

theorem phase_10 (v : ℕ) (hv : v ∈ List.range 140) : PhaseAt 10 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 10 v)
  have h := (join 0 68 72 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_10_0 phase_10_4) (join 8 4 4 phase_10_8 phase_10_12)) (join 16 8 8 (join 16 4 4 phase_10_16 phase_10_20) (join 24 4 4 phase_10_24 phase_10_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_10_32 phase_10_36) (join 40 4 4 phase_10_40 phase_10_44)) (join 48 8 12 (join 48 4 4 phase_10_48 phase_10_52) (join 56 4 8 phase_10_56 (join 60 4 4 phase_10_60 phase_10_64))))) (join 68 36 36 (join 68 16 20 (join 68 8 8 (join 68 4 4 phase_10_68 phase_10_72) (join 76 4 4 phase_10_76 phase_10_80)) (join 84 8 12 (join 84 4 4 phase_10_84 phase_10_88) (join 92 4 8 phase_10_92 (join 96 4 4 phase_10_96 phase_10_100)))) (join 104 16 20 (join 104 8 8 (join 104 4 4 phase_10_104 phase_10_108) (join 112 4 4 phase_10_112 phase_10_116)) (join 120 8 12 (join 120 4 4 phase_10_120 phase_10_124) (join 128 4 8 phase_10_128 (join 132 4 4 phase_10_132 phase_10_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_10_0 : ∀ i ∈ List.range 1, ThresholdAt 10 (0+i) := by decide +kernel

theorem threshold_10_1 : ∀ i ∈ List.range 1, ThresholdAt 10 (1+i) := by decide +kernel

theorem threshold_10_2 : ∀ i ∈ List.range 1, ThresholdAt 10 (2+i) := by decide +kernel

theorem threshold_10_3 : ∀ i ∈ List.range 1, ThresholdAt 10 (3+i) := by decide +kernel

theorem threshold_10_4 : ∀ i ∈ List.range 1, ThresholdAt 10 (4+i) := by decide +kernel

theorem threshold_10_5 : ∀ i ∈ List.range 1, ThresholdAt 10 (5+i) := by decide +kernel

theorem threshold_10_6 : ∀ i ∈ List.range 1, ThresholdAt 10 (6+i) := by decide +kernel

theorem threshold_10_7 : ∀ i ∈ List.range 1, ThresholdAt 10 (7+i) := by decide +kernel

theorem threshold_10_8 : ∀ i ∈ List.range 1, ThresholdAt 10 (8+i) := by decide +kernel

theorem threshold_10_9 : ∀ i ∈ List.range 1, ThresholdAt 10 (9+i) := by decide +kernel

theorem threshold_10_10 : ∀ i ∈ List.range 1, ThresholdAt 10 (10+i) := by decide +kernel

theorem threshold_10_11 : ∀ i ∈ List.range 1, ThresholdAt 10 (11+i) := by decide +kernel

theorem threshold_10_12 : ∀ i ∈ List.range 1, ThresholdAt 10 (12+i) := by decide +kernel

theorem threshold_10_13 : ∀ i ∈ List.range 1, ThresholdAt 10 (13+i) := by decide +kernel

theorem threshold_10_14 : ∀ i ∈ List.range 1, ThresholdAt 10 (14+i) := by decide +kernel

theorem threshold_10_15 : ∀ i ∈ List.range 1, ThresholdAt 10 (15+i) := by decide +kernel

theorem threshold_10_16 : ∀ i ∈ List.range 1, ThresholdAt 10 (16+i) := by decide +kernel

theorem threshold_10_17 : ∀ i ∈ List.range 1, ThresholdAt 10 (17+i) := by decide +kernel

theorem threshold_10_18 : ∀ i ∈ List.range 1, ThresholdAt 10 (18+i) := by decide +kernel

theorem threshold_10_19 : ∀ i ∈ List.range 1, ThresholdAt 10 (19+i) := by decide +kernel

theorem threshold_10_20 : ∀ i ∈ List.range 1, ThresholdAt 10 (20+i) := by decide +kernel

theorem threshold_10_21 : ∀ i ∈ List.range 1, ThresholdAt 10 (21+i) := by decide +kernel

theorem threshold_10_22 : ∀ i ∈ List.range 1, ThresholdAt 10 (22+i) := by decide +kernel

theorem threshold_10_23 : ∀ i ∈ List.range 1, ThresholdAt 10 (23+i) := by decide +kernel

theorem threshold_10_24 : ∀ i ∈ List.range 1, ThresholdAt 10 (24+i) := by decide +kernel

theorem threshold_10_25 : ∀ i ∈ List.range 1, ThresholdAt 10 (25+i) := by decide +kernel

theorem threshold_10_26 : ∀ i ∈ List.range 1, ThresholdAt 10 (26+i) := by decide +kernel

theorem threshold_10_27 : ∀ i ∈ List.range 1, ThresholdAt 10 (27+i) := by decide +kernel

theorem threshold_10_28 : ∀ i ∈ List.range 1, ThresholdAt 10 (28+i) := by decide +kernel

theorem threshold_10_29 : ∀ i ∈ List.range 1, ThresholdAt 10 (29+i) := by decide +kernel

theorem threshold_10_30 : ∀ i ∈ List.range 1, ThresholdAt 10 (30+i) := by decide +kernel

theorem threshold_10_31 : ∀ i ∈ List.range 1, ThresholdAt 10 (31+i) := by decide +kernel

theorem threshold_10_32 : ∀ i ∈ List.range 1, ThresholdAt 10 (32+i) := by decide +kernel

theorem threshold_10_33 : ∀ i ∈ List.range 1, ThresholdAt 10 (33+i) := by decide +kernel

theorem threshold_10_34 : ∀ i ∈ List.range 1, ThresholdAt 10 (34+i) := by decide +kernel

theorem threshold_10_35 : ∀ i ∈ List.range 1, ThresholdAt 10 (35+i) := by decide +kernel

theorem threshold_10_36 : ∀ i ∈ List.range 1, ThresholdAt 10 (36+i) := by decide +kernel

theorem threshold_10_37 : ∀ i ∈ List.range 1, ThresholdAt 10 (37+i) := by decide +kernel

theorem threshold_10_38 : ∀ i ∈ List.range 1, ThresholdAt 10 (38+i) := by decide +kernel

theorem threshold_10_39 : ∀ i ∈ List.range 1, ThresholdAt 10 (39+i) := by decide +kernel

theorem threshold_10_40 : ∀ i ∈ List.range 1, ThresholdAt 10 (40+i) := by decide +kernel

theorem threshold_10_41 : ∀ i ∈ List.range 1, ThresholdAt 10 (41+i) := by decide +kernel

theorem threshold_10_42 : ∀ i ∈ List.range 1, ThresholdAt 10 (42+i) := by decide +kernel

theorem threshold_10_43 : ∀ i ∈ List.range 1, ThresholdAt 10 (43+i) := by decide +kernel

theorem threshold_10_44 : ∀ i ∈ List.range 1, ThresholdAt 10 (44+i) := by decide +kernel

theorem threshold_10_45 : ∀ i ∈ List.range 1, ThresholdAt 10 (45+i) := by decide +kernel

theorem threshold_10_46 : ∀ i ∈ List.range 1, ThresholdAt 10 (46+i) := by decide +kernel

theorem threshold_10_47 : ∀ i ∈ List.range 1, ThresholdAt 10 (47+i) := by decide +kernel

theorem threshold_10_48 : ∀ i ∈ List.range 1, ThresholdAt 10 (48+i) := by decide +kernel

theorem threshold_10_49 : ∀ i ∈ List.range 1, ThresholdAt 10 (49+i) := by decide +kernel

theorem threshold_10_50 : ∀ i ∈ List.range 1, ThresholdAt 10 (50+i) := by decide +kernel

theorem threshold_10_51 : ∀ i ∈ List.range 1, ThresholdAt 10 (51+i) := by decide +kernel

theorem threshold_10_52 : ∀ i ∈ List.range 1, ThresholdAt 10 (52+i) := by decide +kernel

theorem threshold_10_53 : ∀ i ∈ List.range 1, ThresholdAt 10 (53+i) := by decide +kernel

theorem threshold_10_54 : ∀ i ∈ List.range 1, ThresholdAt 10 (54+i) := by decide +kernel

theorem threshold_10_55 : ∀ i ∈ List.range 1, ThresholdAt 10 (55+i) := by decide +kernel

theorem threshold_10_56 : ∀ i ∈ List.range 1, ThresholdAt 10 (56+i) := by decide +kernel

theorem threshold_10_57 : ∀ i ∈ List.range 1, ThresholdAt 10 (57+i) := by decide +kernel

theorem threshold_10_58 : ∀ i ∈ List.range 1, ThresholdAt 10 (58+i) := by decide +kernel

theorem threshold_10_59 : ∀ i ∈ List.range 1, ThresholdAt 10 (59+i) := by decide +kernel

theorem threshold_10_60 : ∀ i ∈ List.range 1, ThresholdAt 10 (60+i) := by decide +kernel

theorem threshold_10_61 : ∀ i ∈ List.range 1, ThresholdAt 10 (61+i) := by decide +kernel

theorem threshold_10_62 : ∀ i ∈ List.range 1, ThresholdAt 10 (62+i) := by decide +kernel

theorem threshold_10_63 : ∀ i ∈ List.range 1, ThresholdAt 10 (63+i) := by decide +kernel

theorem threshold_10_64 : ∀ i ∈ List.range 1, ThresholdAt 10 (64+i) := by decide +kernel

theorem threshold_10_65 : ∀ i ∈ List.range 1, ThresholdAt 10 (65+i) := by decide +kernel

theorem threshold_10_66 : ∀ i ∈ List.range 1, ThresholdAt 10 (66+i) := by decide +kernel

theorem threshold_10_67 : ∀ i ∈ List.range 1, ThresholdAt 10 (67+i) := by decide +kernel

theorem threshold_10_68 : ∀ i ∈ List.range 1, ThresholdAt 10 (68+i) := by decide +kernel

theorem threshold_10_69 : ∀ i ∈ List.range 1, ThresholdAt 10 (69+i) := by decide +kernel

theorem threshold_10_70 : ∀ i ∈ List.range 1, ThresholdAt 10 (70+i) := by decide +kernel

theorem threshold_10_71 : ∀ i ∈ List.range 1, ThresholdAt 10 (71+i) := by decide +kernel

theorem threshold_10_72 : ∀ i ∈ List.range 1, ThresholdAt 10 (72+i) := by decide +kernel

theorem threshold_10_73 : ∀ i ∈ List.range 1, ThresholdAt 10 (73+i) := by decide +kernel

theorem threshold_10_74 : ∀ i ∈ List.range 1, ThresholdAt 10 (74+i) := by decide +kernel

theorem threshold_10_75 : ∀ i ∈ List.range 1, ThresholdAt 10 (75+i) := by decide +kernel

theorem threshold_10_76 : ∀ i ∈ List.range 1, ThresholdAt 10 (76+i) := by decide +kernel

theorem threshold_10_77 : ∀ i ∈ List.range 1, ThresholdAt 10 (77+i) := by decide +kernel

theorem threshold_10_78 : ∀ i ∈ List.range 1, ThresholdAt 10 (78+i) := by decide +kernel

theorem threshold_10_79 : ∀ i ∈ List.range 1, ThresholdAt 10 (79+i) := by decide +kernel

theorem threshold_10_80 : ∀ i ∈ List.range 1, ThresholdAt 10 (80+i) := by decide +kernel

theorem threshold_10_81 : ∀ i ∈ List.range 1, ThresholdAt 10 (81+i) := by decide +kernel

theorem threshold_10_82 : ∀ i ∈ List.range 1, ThresholdAt 10 (82+i) := by decide +kernel

theorem threshold_10_83 : ∀ i ∈ List.range 1, ThresholdAt 10 (83+i) := by decide +kernel

theorem threshold_10_84 : ∀ i ∈ List.range 1, ThresholdAt 10 (84+i) := by decide +kernel

theorem threshold_10_85 : ∀ i ∈ List.range 1, ThresholdAt 10 (85+i) := by decide +kernel

theorem threshold_10_86 : ∀ i ∈ List.range 1, ThresholdAt 10 (86+i) := by decide +kernel

theorem threshold_10_87 : ∀ i ∈ List.range 1, ThresholdAt 10 (87+i) := by decide +kernel

theorem threshold_10_88 : ∀ i ∈ List.range 1, ThresholdAt 10 (88+i) := by decide +kernel

theorem threshold_10_89 : ∀ i ∈ List.range 1, ThresholdAt 10 (89+i) := by decide +kernel

theorem threshold_10_90 : ∀ i ∈ List.range 1, ThresholdAt 10 (90+i) := by decide +kernel

theorem threshold_10_91 : ∀ i ∈ List.range 1, ThresholdAt 10 (91+i) := by decide +kernel

theorem threshold_10_92 : ∀ i ∈ List.range 1, ThresholdAt 10 (92+i) := by decide +kernel

theorem threshold_10_93 : ∀ i ∈ List.range 1, ThresholdAt 10 (93+i) := by decide +kernel

theorem threshold_10_94 : ∀ i ∈ List.range 1, ThresholdAt 10 (94+i) := by decide +kernel

theorem threshold_10_95 : ∀ i ∈ List.range 1, ThresholdAt 10 (95+i) := by decide +kernel

theorem threshold_10_96 : ∀ i ∈ List.range 1, ThresholdAt 10 (96+i) := by decide +kernel

theorem threshold_10_97 : ∀ i ∈ List.range 1, ThresholdAt 10 (97+i) := by decide +kernel

theorem threshold_10_98 : ∀ i ∈ List.range 1, ThresholdAt 10 (98+i) := by decide +kernel

theorem threshold_10_99 : ∀ i ∈ List.range 1, ThresholdAt 10 (99+i) := by decide +kernel

theorem threshold_10_100 : ∀ i ∈ List.range 1, ThresholdAt 10 (100+i) := by decide +kernel

theorem threshold_10_101 : ∀ i ∈ List.range 1, ThresholdAt 10 (101+i) := by decide +kernel

theorem threshold_10_102 : ∀ i ∈ List.range 1, ThresholdAt 10 (102+i) := by decide +kernel

theorem threshold_10_103 : ∀ i ∈ List.range 1, ThresholdAt 10 (103+i) := by decide +kernel

theorem threshold_10_104 : ∀ i ∈ List.range 1, ThresholdAt 10 (104+i) := by decide +kernel

theorem threshold_10_105 : ∀ i ∈ List.range 1, ThresholdAt 10 (105+i) := by decide +kernel

theorem threshold_10_106 : ∀ i ∈ List.range 1, ThresholdAt 10 (106+i) := by decide +kernel

theorem threshold_10_107 : ∀ i ∈ List.range 1, ThresholdAt 10 (107+i) := by decide +kernel

theorem threshold_10_108 : ∀ i ∈ List.range 1, ThresholdAt 10 (108+i) := by decide +kernel

theorem threshold_10_109 : ∀ i ∈ List.range 1, ThresholdAt 10 (109+i) := by decide +kernel

theorem threshold_10_110 : ∀ i ∈ List.range 1, ThresholdAt 10 (110+i) := by decide +kernel

theorem threshold_10_111 : ∀ i ∈ List.range 1, ThresholdAt 10 (111+i) := by decide +kernel

theorem threshold_10_112 : ∀ i ∈ List.range 1, ThresholdAt 10 (112+i) := by decide +kernel

theorem threshold_10_113 : ∀ i ∈ List.range 1, ThresholdAt 10 (113+i) := by decide +kernel

theorem threshold_10_114 : ∀ i ∈ List.range 1, ThresholdAt 10 (114+i) := by decide +kernel

theorem threshold_10_115 : ∀ i ∈ List.range 1, ThresholdAt 10 (115+i) := by decide +kernel

theorem threshold_10_116 : ∀ i ∈ List.range 1, ThresholdAt 10 (116+i) := by decide +kernel

theorem threshold_10_117 : ∀ i ∈ List.range 1, ThresholdAt 10 (117+i) := by decide +kernel

theorem threshold_10_118 : ∀ i ∈ List.range 1, ThresholdAt 10 (118+i) := by decide +kernel

theorem threshold_10_119 : ∀ i ∈ List.range 1, ThresholdAt 10 (119+i) := by decide +kernel

theorem threshold_10_120 : ∀ i ∈ List.range 1, ThresholdAt 10 (120+i) := by decide +kernel

theorem threshold_10_121 : ∀ i ∈ List.range 1, ThresholdAt 10 (121+i) := by decide +kernel

theorem threshold_10_122 : ∀ i ∈ List.range 1, ThresholdAt 10 (122+i) := by decide +kernel

theorem threshold_10_123 : ∀ i ∈ List.range 1, ThresholdAt 10 (123+i) := by decide +kernel

theorem threshold_10_124 : ∀ i ∈ List.range 1, ThresholdAt 10 (124+i) := by decide +kernel

theorem threshold_10_125 : ∀ i ∈ List.range 1, ThresholdAt 10 (125+i) := by decide +kernel

theorem threshold_10_126 : ∀ i ∈ List.range 1, ThresholdAt 10 (126+i) := by decide +kernel

theorem threshold_10_127 : ∀ i ∈ List.range 1, ThresholdAt 10 (127+i) := by decide +kernel

theorem threshold_10_128 : ∀ i ∈ List.range 1, ThresholdAt 10 (128+i) := by decide +kernel

theorem threshold_10_129 : ∀ i ∈ List.range 1, ThresholdAt 10 (129+i) := by decide +kernel

theorem threshold_10_130 : ∀ i ∈ List.range 1, ThresholdAt 10 (130+i) := by decide +kernel

theorem threshold_10_131 : ∀ i ∈ List.range 1, ThresholdAt 10 (131+i) := by decide +kernel

theorem threshold_10_132 : ∀ i ∈ List.range 1, ThresholdAt 10 (132+i) := by decide +kernel

theorem threshold_10_133 : ∀ i ∈ List.range 1, ThresholdAt 10 (133+i) := by decide +kernel

theorem threshold_10_134 : ∀ i ∈ List.range 1, ThresholdAt 10 (134+i) := by decide +kernel

theorem threshold_10_135 : ∀ i ∈ List.range 1, ThresholdAt 10 (135+i) := by decide +kernel

theorem threshold_10_136 : ∀ i ∈ List.range 1, ThresholdAt 10 (136+i) := by decide +kernel

theorem threshold_10_137 : ∀ i ∈ List.range 1, ThresholdAt 10 (137+i) := by decide +kernel

theorem threshold_10_138 : ∀ i ∈ List.range 1, ThresholdAt 10 (138+i) := by decide +kernel

theorem threshold_10_139 : ∀ i ∈ List.range 1, ThresholdAt 10 (139+i) := by decide +kernel

theorem threshold_10 (v : ℕ) (hv : v ∈ List.range 140) : ThresholdAt 10 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 10 v)
  have h := (join 0 70 70 (join 0 35 35 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_10_0 threshold_10_1) (join 2 1 1 threshold_10_2 threshold_10_3)) (join 4 2 2 (join 4 1 1 threshold_10_4 threshold_10_5) (join 6 1 1 threshold_10_6 threshold_10_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_10_8 threshold_10_9) (join 10 1 1 threshold_10_10 threshold_10_11)) (join 12 2 3 (join 12 1 1 threshold_10_12 threshold_10_13) (join 14 1 2 threshold_10_14 (join 15 1 1 threshold_10_15 threshold_10_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 threshold_10_17 threshold_10_18) (join 19 1 1 threshold_10_19 threshold_10_20)) (join 21 2 3 (join 21 1 1 threshold_10_21 threshold_10_22) (join 23 1 2 threshold_10_23 (join 24 1 1 threshold_10_24 threshold_10_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 threshold_10_26 threshold_10_27) (join 28 1 1 threshold_10_28 threshold_10_29)) (join 30 2 3 (join 30 1 1 threshold_10_30 threshold_10_31) (join 32 1 2 threshold_10_32 (join 33 1 1 threshold_10_33 threshold_10_34)))))) (join 35 17 18 (join 35 8 9 (join 35 4 4 (join 35 2 2 (join 35 1 1 threshold_10_35 threshold_10_36) (join 37 1 1 threshold_10_37 threshold_10_38)) (join 39 2 2 (join 39 1 1 threshold_10_39 threshold_10_40) (join 41 1 1 threshold_10_41 threshold_10_42))) (join 43 4 5 (join 43 2 2 (join 43 1 1 threshold_10_43 threshold_10_44) (join 45 1 1 threshold_10_45 threshold_10_46)) (join 47 2 3 (join 47 1 1 threshold_10_47 threshold_10_48) (join 49 1 2 threshold_10_49 (join 50 1 1 threshold_10_50 threshold_10_51))))) (join 52 9 9 (join 52 4 5 (join 52 2 2 (join 52 1 1 threshold_10_52 threshold_10_53) (join 54 1 1 threshold_10_54 threshold_10_55)) (join 56 2 3 (join 56 1 1 threshold_10_56 threshold_10_57) (join 58 1 2 threshold_10_58 (join 59 1 1 threshold_10_59 threshold_10_60)))) (join 61 4 5 (join 61 2 2 (join 61 1 1 threshold_10_61 threshold_10_62) (join 63 1 1 threshold_10_63 threshold_10_64)) (join 65 2 3 (join 65 1 1 threshold_10_65 threshold_10_66) (join 67 1 2 threshold_10_67 (join 68 1 1 threshold_10_68 threshold_10_69))))))) (join 70 35 35 (join 70 17 18 (join 70 8 9 (join 70 4 4 (join 70 2 2 (join 70 1 1 threshold_10_70 threshold_10_71) (join 72 1 1 threshold_10_72 threshold_10_73)) (join 74 2 2 (join 74 1 1 threshold_10_74 threshold_10_75) (join 76 1 1 threshold_10_76 threshold_10_77))) (join 78 4 5 (join 78 2 2 (join 78 1 1 threshold_10_78 threshold_10_79) (join 80 1 1 threshold_10_80 threshold_10_81)) (join 82 2 3 (join 82 1 1 threshold_10_82 threshold_10_83) (join 84 1 2 threshold_10_84 (join 85 1 1 threshold_10_85 threshold_10_86))))) (join 87 9 9 (join 87 4 5 (join 87 2 2 (join 87 1 1 threshold_10_87 threshold_10_88) (join 89 1 1 threshold_10_89 threshold_10_90)) (join 91 2 3 (join 91 1 1 threshold_10_91 threshold_10_92) (join 93 1 2 threshold_10_93 (join 94 1 1 threshold_10_94 threshold_10_95)))) (join 96 4 5 (join 96 2 2 (join 96 1 1 threshold_10_96 threshold_10_97) (join 98 1 1 threshold_10_98 threshold_10_99)) (join 100 2 3 (join 100 1 1 threshold_10_100 threshold_10_101) (join 102 1 2 threshold_10_102 (join 103 1 1 threshold_10_103 threshold_10_104)))))) (join 105 17 18 (join 105 8 9 (join 105 4 4 (join 105 2 2 (join 105 1 1 threshold_10_105 threshold_10_106) (join 107 1 1 threshold_10_107 threshold_10_108)) (join 109 2 2 (join 109 1 1 threshold_10_109 threshold_10_110) (join 111 1 1 threshold_10_111 threshold_10_112))) (join 113 4 5 (join 113 2 2 (join 113 1 1 threshold_10_113 threshold_10_114) (join 115 1 1 threshold_10_115 threshold_10_116)) (join 117 2 3 (join 117 1 1 threshold_10_117 threshold_10_118) (join 119 1 2 threshold_10_119 (join 120 1 1 threshold_10_120 threshold_10_121))))) (join 122 9 9 (join 122 4 5 (join 122 2 2 (join 122 1 1 threshold_10_122 threshold_10_123) (join 124 1 1 threshold_10_124 threshold_10_125)) (join 126 2 3 (join 126 1 1 threshold_10_126 threshold_10_127) (join 128 1 2 threshold_10_128 (join 129 1 1 threshold_10_129 threshold_10_130)))) (join 131 4 5 (join 131 2 2 (join 131 1 1 threshold_10_131 threshold_10_132) (join 133 1 1 threshold_10_133 threshold_10_134)) (join 135 2 3 (join 135 1 1 threshold_10_135 threshold_10_136) (join 137 1 2 threshold_10_137 (join 138 1 1 threshold_10_138 threshold_10_139))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_10_0 : ∀ i ∈ List.range 4, LedgerAt 10 (0+i) := by decide +kernel

theorem ledger_10_4 : ∀ i ∈ List.range 4, LedgerAt 10 (4+i) := by decide +kernel

theorem ledger_10_8 : ∀ i ∈ List.range 4, LedgerAt 10 (8+i) := by decide +kernel

theorem ledger_10_12 : ∀ i ∈ List.range 4, LedgerAt 10 (12+i) := by decide +kernel

theorem ledger_10_16 : ∀ i ∈ List.range 4, LedgerAt 10 (16+i) := by decide +kernel

theorem ledger_10_20 : ∀ i ∈ List.range 4, LedgerAt 10 (20+i) := by decide +kernel

theorem ledger_10_24 : ∀ i ∈ List.range 4, LedgerAt 10 (24+i) := by decide +kernel

theorem ledger_10_28 : ∀ i ∈ List.range 4, LedgerAt 10 (28+i) := by decide +kernel

theorem ledger_10_32 : ∀ i ∈ List.range 4, LedgerAt 10 (32+i) := by decide +kernel

theorem ledger_10_36 : ∀ i ∈ List.range 4, LedgerAt 10 (36+i) := by decide +kernel

theorem ledger_10_40 : ∀ i ∈ List.range 4, LedgerAt 10 (40+i) := by decide +kernel

theorem ledger_10_44 : ∀ i ∈ List.range 4, LedgerAt 10 (44+i) := by decide +kernel

theorem ledger_10_48 : ∀ i ∈ List.range 4, LedgerAt 10 (48+i) := by decide +kernel

theorem ledger_10_52 : ∀ i ∈ List.range 4, LedgerAt 10 (52+i) := by decide +kernel

theorem ledger_10_56 : ∀ i ∈ List.range 4, LedgerAt 10 (56+i) := by decide +kernel

theorem ledger_10_60 : ∀ i ∈ List.range 4, LedgerAt 10 (60+i) := by decide +kernel

theorem ledger_10_64 : ∀ i ∈ List.range 4, LedgerAt 10 (64+i) := by decide +kernel

theorem ledger_10_68 : ∀ i ∈ List.range 4, LedgerAt 10 (68+i) := by decide +kernel

theorem ledger_10_72 : ∀ i ∈ List.range 4, LedgerAt 10 (72+i) := by decide +kernel

theorem ledger_10_76 : ∀ i ∈ List.range 4, LedgerAt 10 (76+i) := by decide +kernel

theorem ledger_10_80 : ∀ i ∈ List.range 4, LedgerAt 10 (80+i) := by decide +kernel

theorem ledger_10_84 : ∀ i ∈ List.range 4, LedgerAt 10 (84+i) := by decide +kernel

theorem ledger_10_88 : ∀ i ∈ List.range 4, LedgerAt 10 (88+i) := by decide +kernel

theorem ledger_10_92 : ∀ i ∈ List.range 4, LedgerAt 10 (92+i) := by decide +kernel

theorem ledger_10_96 : ∀ i ∈ List.range 4, LedgerAt 10 (96+i) := by decide +kernel

theorem ledger_10_100 : ∀ i ∈ List.range 4, LedgerAt 10 (100+i) := by decide +kernel

theorem ledger_10_104 : ∀ i ∈ List.range 4, LedgerAt 10 (104+i) := by decide +kernel

theorem ledger_10_108 : ∀ i ∈ List.range 4, LedgerAt 10 (108+i) := by decide +kernel

theorem ledger_10_112 : ∀ i ∈ List.range 4, LedgerAt 10 (112+i) := by decide +kernel

theorem ledger_10_116 : ∀ i ∈ List.range 4, LedgerAt 10 (116+i) := by decide +kernel

theorem ledger_10_120 : ∀ i ∈ List.range 4, LedgerAt 10 (120+i) := by decide +kernel

theorem ledger_10_124 : ∀ i ∈ List.range 4, LedgerAt 10 (124+i) := by decide +kernel

theorem ledger_10_128 : ∀ i ∈ List.range 4, LedgerAt 10 (128+i) := by decide +kernel

theorem ledger_10_132 : ∀ i ∈ List.range 4, LedgerAt 10 (132+i) := by decide +kernel

theorem ledger_10_136 : ∀ i ∈ List.range 4, LedgerAt 10 (136+i) := by decide +kernel

theorem ledger_10 (v : ℕ) (hv : v ∈ List.range 140) : LedgerAt 10 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 10 v)
  have h := (join 0 68 72 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_10_0 ledger_10_4) (join 8 4 4 ledger_10_8 ledger_10_12)) (join 16 8 8 (join 16 4 4 ledger_10_16 ledger_10_20) (join 24 4 4 ledger_10_24 ledger_10_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_10_32 ledger_10_36) (join 40 4 4 ledger_10_40 ledger_10_44)) (join 48 8 12 (join 48 4 4 ledger_10_48 ledger_10_52) (join 56 4 8 ledger_10_56 (join 60 4 4 ledger_10_60 ledger_10_64))))) (join 68 36 36 (join 68 16 20 (join 68 8 8 (join 68 4 4 ledger_10_68 ledger_10_72) (join 76 4 4 ledger_10_76 ledger_10_80)) (join 84 8 12 (join 84 4 4 ledger_10_84 ledger_10_88) (join 92 4 8 ledger_10_92 (join 96 4 4 ledger_10_96 ledger_10_100)))) (join 104 16 20 (join 104 8 8 (join 104 4 4 ledger_10_104 ledger_10_108) (join 112 4 4 ledger_10_112 ledger_10_116)) (join 120 8 12 (join 120 4 4 ledger_10_120 ledger_10_124) (join 128 4 8 ledger_10_128 (join 132 4 4 ledger_10_132 ledger_10_136))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
