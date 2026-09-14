import ProximityPrize.SubmissionLower.HigherAffineCheckedR196810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_20_0 : ∀ i ∈ List.range 4, SingleAt 20 (0+i) := by decide +kernel

theorem single_20_4 : ∀ i ∈ List.range 4, SingleAt 20 (4+i) := by decide +kernel

theorem single_20_8 : ∀ i ∈ List.range 4, SingleAt 20 (8+i) := by decide +kernel

theorem single_20_12 : ∀ i ∈ List.range 4, SingleAt 20 (12+i) := by decide +kernel

theorem single_20_16 : ∀ i ∈ List.range 4, SingleAt 20 (16+i) := by decide +kernel

theorem single_20_20 : ∀ i ∈ List.range 4, SingleAt 20 (20+i) := by decide +kernel

theorem single_20_24 : ∀ i ∈ List.range 4, SingleAt 20 (24+i) := by decide +kernel

theorem single_20_28 : ∀ i ∈ List.range 4, SingleAt 20 (28+i) := by decide +kernel

theorem single_20_32 : ∀ i ∈ List.range 4, SingleAt 20 (32+i) := by decide +kernel

theorem single_20_36 : ∀ i ∈ List.range 4, SingleAt 20 (36+i) := by decide +kernel

theorem single_20_40 : ∀ i ∈ List.range 4, SingleAt 20 (40+i) := by decide +kernel

theorem single_20_44 : ∀ i ∈ List.range 4, SingleAt 20 (44+i) := by decide +kernel

theorem single_20_48 : ∀ i ∈ List.range 4, SingleAt 20 (48+i) := by decide +kernel

theorem single_20_52 : ∀ i ∈ List.range 4, SingleAt 20 (52+i) := by decide +kernel

theorem single_20_56 : ∀ i ∈ List.range 4, SingleAt 20 (56+i) := by decide +kernel

theorem single_20_60 : ∀ i ∈ List.range 4, SingleAt 20 (60+i) := by decide +kernel

theorem single_20_64 : ∀ i ∈ List.range 4, SingleAt 20 (64+i) := by decide +kernel

theorem single_20_68 : ∀ i ∈ List.range 4, SingleAt 20 (68+i) := by decide +kernel

theorem single_20_72 : ∀ i ∈ List.range 4, SingleAt 20 (72+i) := by decide +kernel

theorem single_20_76 : ∀ i ∈ List.range 4, SingleAt 20 (76+i) := by decide +kernel

theorem single_20_80 : ∀ i ∈ List.range 4, SingleAt 20 (80+i) := by decide +kernel

theorem single_20_84 : ∀ i ∈ List.range 4, SingleAt 20 (84+i) := by decide +kernel

theorem single_20_88 : ∀ i ∈ List.range 4, SingleAt 20 (88+i) := by decide +kernel

theorem single_20_92 : ∀ i ∈ List.range 4, SingleAt 20 (92+i) := by decide +kernel

theorem single_20_96 : ∀ i ∈ List.range 4, SingleAt 20 (96+i) := by decide +kernel

theorem single_20_100 : ∀ i ∈ List.range 4, SingleAt 20 (100+i) := by decide +kernel

theorem single_20_104 : ∀ i ∈ List.range 4, SingleAt 20 (104+i) := by decide +kernel

theorem single_20_108 : ∀ i ∈ List.range 4, SingleAt 20 (108+i) := by decide +kernel

theorem single_20_112 : ∀ i ∈ List.range 4, SingleAt 20 (112+i) := by decide +kernel

theorem single_20_116 : ∀ i ∈ List.range 4, SingleAt 20 (116+i) := by decide +kernel

theorem single_20_120 : ∀ i ∈ List.range 4, SingleAt 20 (120+i) := by decide +kernel

theorem single_20_124 : ∀ i ∈ List.range 4, SingleAt 20 (124+i) := by decide +kernel

theorem single_20_128 : ∀ i ∈ List.range 4, SingleAt 20 (128+i) := by decide +kernel

theorem single_20_132 : ∀ i ∈ List.range 4, SingleAt 20 (132+i) := by decide +kernel

theorem single_20_136 : ∀ i ∈ List.range 1, SingleAt 20 (136+i) := by decide +kernel

theorem single_20 (v : ℕ) (hv : v ∈ List.range 137) : SingleAt 20 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 20 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_20_0 single_20_4) (join 8 4 4 single_20_8 single_20_12)) (join 16 8 8 (join 16 4 4 single_20_16 single_20_20) (join 24 4 4 single_20_24 single_20_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 single_20_32 single_20_36) (join 40 4 4 single_20_40 single_20_44)) (join 48 8 12 (join 48 4 4 single_20_48 single_20_52) (join 56 4 8 single_20_56 (join 60 4 4 single_20_60 single_20_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 single_20_68 single_20_72) (join 76 4 4 single_20_76 single_20_80)) (join 84 8 12 (join 84 4 4 single_20_84 single_20_88) (join 92 4 8 single_20_92 (join 96 4 4 single_20_96 single_20_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 single_20_104 single_20_108) (join 112 4 4 single_20_112 single_20_116)) (join 120 8 9 (join 120 4 4 single_20_120 single_20_124) (join 128 4 5 single_20_128 (join 132 4 1 single_20_132 single_20_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_20_0 : ∀ i ∈ List.range 4, PhaseAt 20 (0+i) := by decide +kernel

theorem phase_20_4 : ∀ i ∈ List.range 4, PhaseAt 20 (4+i) := by decide +kernel

theorem phase_20_8 : ∀ i ∈ List.range 4, PhaseAt 20 (8+i) := by decide +kernel

theorem phase_20_12 : ∀ i ∈ List.range 4, PhaseAt 20 (12+i) := by decide +kernel

theorem phase_20_16 : ∀ i ∈ List.range 4, PhaseAt 20 (16+i) := by decide +kernel

theorem phase_20_20 : ∀ i ∈ List.range 4, PhaseAt 20 (20+i) := by decide +kernel

theorem phase_20_24 : ∀ i ∈ List.range 4, PhaseAt 20 (24+i) := by decide +kernel

theorem phase_20_28 : ∀ i ∈ List.range 4, PhaseAt 20 (28+i) := by decide +kernel

theorem phase_20_32 : ∀ i ∈ List.range 4, PhaseAt 20 (32+i) := by decide +kernel

theorem phase_20_36 : ∀ i ∈ List.range 4, PhaseAt 20 (36+i) := by decide +kernel

theorem phase_20_40 : ∀ i ∈ List.range 4, PhaseAt 20 (40+i) := by decide +kernel

theorem phase_20_44 : ∀ i ∈ List.range 4, PhaseAt 20 (44+i) := by decide +kernel

theorem phase_20_48 : ∀ i ∈ List.range 4, PhaseAt 20 (48+i) := by decide +kernel

theorem phase_20_52 : ∀ i ∈ List.range 4, PhaseAt 20 (52+i) := by decide +kernel

theorem phase_20_56 : ∀ i ∈ List.range 4, PhaseAt 20 (56+i) := by decide +kernel

theorem phase_20_60 : ∀ i ∈ List.range 4, PhaseAt 20 (60+i) := by decide +kernel

theorem phase_20_64 : ∀ i ∈ List.range 4, PhaseAt 20 (64+i) := by decide +kernel

theorem phase_20_68 : ∀ i ∈ List.range 4, PhaseAt 20 (68+i) := by decide +kernel

theorem phase_20_72 : ∀ i ∈ List.range 4, PhaseAt 20 (72+i) := by decide +kernel

theorem phase_20_76 : ∀ i ∈ List.range 4, PhaseAt 20 (76+i) := by decide +kernel

theorem phase_20_80 : ∀ i ∈ List.range 4, PhaseAt 20 (80+i) := by decide +kernel

theorem phase_20_84 : ∀ i ∈ List.range 4, PhaseAt 20 (84+i) := by decide +kernel

theorem phase_20_88 : ∀ i ∈ List.range 4, PhaseAt 20 (88+i) := by decide +kernel

theorem phase_20_92 : ∀ i ∈ List.range 4, PhaseAt 20 (92+i) := by decide +kernel

theorem phase_20_96 : ∀ i ∈ List.range 4, PhaseAt 20 (96+i) := by decide +kernel

theorem phase_20_100 : ∀ i ∈ List.range 4, PhaseAt 20 (100+i) := by decide +kernel

theorem phase_20_104 : ∀ i ∈ List.range 4, PhaseAt 20 (104+i) := by decide +kernel

theorem phase_20_108 : ∀ i ∈ List.range 4, PhaseAt 20 (108+i) := by decide +kernel

theorem phase_20_112 : ∀ i ∈ List.range 4, PhaseAt 20 (112+i) := by decide +kernel

theorem phase_20_116 : ∀ i ∈ List.range 4, PhaseAt 20 (116+i) := by decide +kernel

theorem phase_20_120 : ∀ i ∈ List.range 4, PhaseAt 20 (120+i) := by decide +kernel

theorem phase_20_124 : ∀ i ∈ List.range 4, PhaseAt 20 (124+i) := by decide +kernel

theorem phase_20_128 : ∀ i ∈ List.range 4, PhaseAt 20 (128+i) := by decide +kernel

theorem phase_20_132 : ∀ i ∈ List.range 4, PhaseAt 20 (132+i) := by decide +kernel

theorem phase_20_136 : ∀ i ∈ List.range 1, PhaseAt 20 (136+i) := by decide +kernel

theorem phase_20 (v : ℕ) (hv : v ∈ List.range 137) : PhaseAt 20 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 20 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_20_0 phase_20_4) (join 8 4 4 phase_20_8 phase_20_12)) (join 16 8 8 (join 16 4 4 phase_20_16 phase_20_20) (join 24 4 4 phase_20_24 phase_20_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_20_32 phase_20_36) (join 40 4 4 phase_20_40 phase_20_44)) (join 48 8 12 (join 48 4 4 phase_20_48 phase_20_52) (join 56 4 8 phase_20_56 (join 60 4 4 phase_20_60 phase_20_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 phase_20_68 phase_20_72) (join 76 4 4 phase_20_76 phase_20_80)) (join 84 8 12 (join 84 4 4 phase_20_84 phase_20_88) (join 92 4 8 phase_20_92 (join 96 4 4 phase_20_96 phase_20_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 phase_20_104 phase_20_108) (join 112 4 4 phase_20_112 phase_20_116)) (join 120 8 9 (join 120 4 4 phase_20_120 phase_20_124) (join 128 4 5 phase_20_128 (join 132 4 1 phase_20_132 phase_20_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_20_0 : ∀ i ∈ List.range 1, ThresholdAt 20 (0+i) := by decide +kernel

theorem threshold_20_1 : ∀ i ∈ List.range 1, ThresholdAt 20 (1+i) := by decide +kernel

theorem threshold_20_2 : ∀ i ∈ List.range 1, ThresholdAt 20 (2+i) := by decide +kernel

theorem threshold_20_3 : ∀ i ∈ List.range 1, ThresholdAt 20 (3+i) := by decide +kernel

theorem threshold_20_4 : ∀ i ∈ List.range 1, ThresholdAt 20 (4+i) := by decide +kernel

theorem threshold_20_5 : ∀ i ∈ List.range 1, ThresholdAt 20 (5+i) := by decide +kernel

theorem threshold_20_6 : ∀ i ∈ List.range 1, ThresholdAt 20 (6+i) := by decide +kernel

theorem threshold_20_7 : ∀ i ∈ List.range 1, ThresholdAt 20 (7+i) := by decide +kernel

theorem threshold_20_8 : ∀ i ∈ List.range 1, ThresholdAt 20 (8+i) := by decide +kernel

theorem threshold_20_9 : ∀ i ∈ List.range 1, ThresholdAt 20 (9+i) := by decide +kernel

theorem threshold_20_10 : ∀ i ∈ List.range 1, ThresholdAt 20 (10+i) := by decide +kernel

theorem threshold_20_11 : ∀ i ∈ List.range 1, ThresholdAt 20 (11+i) := by decide +kernel

theorem threshold_20_12 : ∀ i ∈ List.range 1, ThresholdAt 20 (12+i) := by decide +kernel

theorem threshold_20_13 : ∀ i ∈ List.range 1, ThresholdAt 20 (13+i) := by decide +kernel

theorem threshold_20_14 : ∀ i ∈ List.range 1, ThresholdAt 20 (14+i) := by decide +kernel

theorem threshold_20_15 : ∀ i ∈ List.range 1, ThresholdAt 20 (15+i) := by decide +kernel

theorem threshold_20_16 : ∀ i ∈ List.range 1, ThresholdAt 20 (16+i) := by decide +kernel

theorem threshold_20_17 : ∀ i ∈ List.range 1, ThresholdAt 20 (17+i) := by decide +kernel

theorem threshold_20_18 : ∀ i ∈ List.range 1, ThresholdAt 20 (18+i) := by decide +kernel

theorem threshold_20_19 : ∀ i ∈ List.range 1, ThresholdAt 20 (19+i) := by decide +kernel

theorem threshold_20_20 : ∀ i ∈ List.range 1, ThresholdAt 20 (20+i) := by decide +kernel

theorem threshold_20_21 : ∀ i ∈ List.range 1, ThresholdAt 20 (21+i) := by decide +kernel

theorem threshold_20_22 : ∀ i ∈ List.range 1, ThresholdAt 20 (22+i) := by decide +kernel

theorem threshold_20_23 : ∀ i ∈ List.range 1, ThresholdAt 20 (23+i) := by decide +kernel

theorem threshold_20_24 : ∀ i ∈ List.range 1, ThresholdAt 20 (24+i) := by decide +kernel

theorem threshold_20_25 : ∀ i ∈ List.range 1, ThresholdAt 20 (25+i) := by decide +kernel

theorem threshold_20_26 : ∀ i ∈ List.range 1, ThresholdAt 20 (26+i) := by decide +kernel

theorem threshold_20_27 : ∀ i ∈ List.range 1, ThresholdAt 20 (27+i) := by decide +kernel

theorem threshold_20_28 : ∀ i ∈ List.range 1, ThresholdAt 20 (28+i) := by decide +kernel

theorem threshold_20_29 : ∀ i ∈ List.range 1, ThresholdAt 20 (29+i) := by decide +kernel

theorem threshold_20_30 : ∀ i ∈ List.range 1, ThresholdAt 20 (30+i) := by decide +kernel

theorem threshold_20_31 : ∀ i ∈ List.range 1, ThresholdAt 20 (31+i) := by decide +kernel

theorem threshold_20_32 : ∀ i ∈ List.range 1, ThresholdAt 20 (32+i) := by decide +kernel

theorem threshold_20_33 : ∀ i ∈ List.range 1, ThresholdAt 20 (33+i) := by decide +kernel

theorem threshold_20_34 : ∀ i ∈ List.range 1, ThresholdAt 20 (34+i) := by decide +kernel

theorem threshold_20_35 : ∀ i ∈ List.range 1, ThresholdAt 20 (35+i) := by decide +kernel

theorem threshold_20_36 : ∀ i ∈ List.range 1, ThresholdAt 20 (36+i) := by decide +kernel

theorem threshold_20_37 : ∀ i ∈ List.range 1, ThresholdAt 20 (37+i) := by decide +kernel

theorem threshold_20_38 : ∀ i ∈ List.range 1, ThresholdAt 20 (38+i) := by decide +kernel

theorem threshold_20_39 : ∀ i ∈ List.range 1, ThresholdAt 20 (39+i) := by decide +kernel

theorem threshold_20_40 : ∀ i ∈ List.range 1, ThresholdAt 20 (40+i) := by decide +kernel

theorem threshold_20_41 : ∀ i ∈ List.range 1, ThresholdAt 20 (41+i) := by decide +kernel

theorem threshold_20_42 : ∀ i ∈ List.range 1, ThresholdAt 20 (42+i) := by decide +kernel

theorem threshold_20_43 : ∀ i ∈ List.range 1, ThresholdAt 20 (43+i) := by decide +kernel

theorem threshold_20_44 : ∀ i ∈ List.range 1, ThresholdAt 20 (44+i) := by decide +kernel

theorem threshold_20_45 : ∀ i ∈ List.range 1, ThresholdAt 20 (45+i) := by decide +kernel

theorem threshold_20_46 : ∀ i ∈ List.range 1, ThresholdAt 20 (46+i) := by decide +kernel

theorem threshold_20_47 : ∀ i ∈ List.range 1, ThresholdAt 20 (47+i) := by decide +kernel

theorem threshold_20_48 : ∀ i ∈ List.range 1, ThresholdAt 20 (48+i) := by decide +kernel

theorem threshold_20_49 : ∀ i ∈ List.range 1, ThresholdAt 20 (49+i) := by decide +kernel

theorem threshold_20_50 : ∀ i ∈ List.range 1, ThresholdAt 20 (50+i) := by decide +kernel

theorem threshold_20_51 : ∀ i ∈ List.range 1, ThresholdAt 20 (51+i) := by decide +kernel

theorem threshold_20_52 : ∀ i ∈ List.range 1, ThresholdAt 20 (52+i) := by decide +kernel

theorem threshold_20_53 : ∀ i ∈ List.range 1, ThresholdAt 20 (53+i) := by decide +kernel

theorem threshold_20_54 : ∀ i ∈ List.range 1, ThresholdAt 20 (54+i) := by decide +kernel

theorem threshold_20_55 : ∀ i ∈ List.range 1, ThresholdAt 20 (55+i) := by decide +kernel

theorem threshold_20_56 : ∀ i ∈ List.range 1, ThresholdAt 20 (56+i) := by decide +kernel

theorem threshold_20_57 : ∀ i ∈ List.range 1, ThresholdAt 20 (57+i) := by decide +kernel

theorem threshold_20_58 : ∀ i ∈ List.range 1, ThresholdAt 20 (58+i) := by decide +kernel

theorem threshold_20_59 : ∀ i ∈ List.range 1, ThresholdAt 20 (59+i) := by decide +kernel

theorem threshold_20_60 : ∀ i ∈ List.range 1, ThresholdAt 20 (60+i) := by decide +kernel

theorem threshold_20_61 : ∀ i ∈ List.range 1, ThresholdAt 20 (61+i) := by decide +kernel

theorem threshold_20_62 : ∀ i ∈ List.range 1, ThresholdAt 20 (62+i) := by decide +kernel

theorem threshold_20_63 : ∀ i ∈ List.range 1, ThresholdAt 20 (63+i) := by decide +kernel

theorem threshold_20_64 : ∀ i ∈ List.range 1, ThresholdAt 20 (64+i) := by decide +kernel

theorem threshold_20_65 : ∀ i ∈ List.range 1, ThresholdAt 20 (65+i) := by decide +kernel

theorem threshold_20_66 : ∀ i ∈ List.range 1, ThresholdAt 20 (66+i) := by decide +kernel

theorem threshold_20_67 : ∀ i ∈ List.range 1, ThresholdAt 20 (67+i) := by decide +kernel

theorem threshold_20_68 : ∀ i ∈ List.range 1, ThresholdAt 20 (68+i) := by decide +kernel

theorem threshold_20_69 : ∀ i ∈ List.range 1, ThresholdAt 20 (69+i) := by decide +kernel

theorem threshold_20_70 : ∀ i ∈ List.range 1, ThresholdAt 20 (70+i) := by decide +kernel

theorem threshold_20_71 : ∀ i ∈ List.range 1, ThresholdAt 20 (71+i) := by decide +kernel

theorem threshold_20_72 : ∀ i ∈ List.range 1, ThresholdAt 20 (72+i) := by decide +kernel

theorem threshold_20_73 : ∀ i ∈ List.range 1, ThresholdAt 20 (73+i) := by decide +kernel

theorem threshold_20_74 : ∀ i ∈ List.range 1, ThresholdAt 20 (74+i) := by decide +kernel

theorem threshold_20_75 : ∀ i ∈ List.range 1, ThresholdAt 20 (75+i) := by decide +kernel

theorem threshold_20_76 : ∀ i ∈ List.range 1, ThresholdAt 20 (76+i) := by decide +kernel

theorem threshold_20_77 : ∀ i ∈ List.range 1, ThresholdAt 20 (77+i) := by decide +kernel

theorem threshold_20_78 : ∀ i ∈ List.range 1, ThresholdAt 20 (78+i) := by decide +kernel

theorem threshold_20_79 : ∀ i ∈ List.range 1, ThresholdAt 20 (79+i) := by decide +kernel

theorem threshold_20_80 : ∀ i ∈ List.range 1, ThresholdAt 20 (80+i) := by decide +kernel

theorem threshold_20_81 : ∀ i ∈ List.range 1, ThresholdAt 20 (81+i) := by decide +kernel

theorem threshold_20_82 : ∀ i ∈ List.range 1, ThresholdAt 20 (82+i) := by decide +kernel

theorem threshold_20_83 : ∀ i ∈ List.range 1, ThresholdAt 20 (83+i) := by decide +kernel

theorem threshold_20_84 : ∀ i ∈ List.range 1, ThresholdAt 20 (84+i) := by decide +kernel

theorem threshold_20_85 : ∀ i ∈ List.range 1, ThresholdAt 20 (85+i) := by decide +kernel

theorem threshold_20_86 : ∀ i ∈ List.range 1, ThresholdAt 20 (86+i) := by decide +kernel

theorem threshold_20_87 : ∀ i ∈ List.range 1, ThresholdAt 20 (87+i) := by decide +kernel

theorem threshold_20_88 : ∀ i ∈ List.range 1, ThresholdAt 20 (88+i) := by decide +kernel

theorem threshold_20_89 : ∀ i ∈ List.range 1, ThresholdAt 20 (89+i) := by decide +kernel

theorem threshold_20_90 : ∀ i ∈ List.range 1, ThresholdAt 20 (90+i) := by decide +kernel

theorem threshold_20_91 : ∀ i ∈ List.range 1, ThresholdAt 20 (91+i) := by decide +kernel

theorem threshold_20_92 : ∀ i ∈ List.range 1, ThresholdAt 20 (92+i) := by decide +kernel

theorem threshold_20_93 : ∀ i ∈ List.range 1, ThresholdAt 20 (93+i) := by decide +kernel

theorem threshold_20_94 : ∀ i ∈ List.range 1, ThresholdAt 20 (94+i) := by decide +kernel

theorem threshold_20_95 : ∀ i ∈ List.range 1, ThresholdAt 20 (95+i) := by decide +kernel

theorem threshold_20_96 : ∀ i ∈ List.range 1, ThresholdAt 20 (96+i) := by decide +kernel

theorem threshold_20_97 : ∀ i ∈ List.range 1, ThresholdAt 20 (97+i) := by decide +kernel

theorem threshold_20_98 : ∀ i ∈ List.range 1, ThresholdAt 20 (98+i) := by decide +kernel

theorem threshold_20_99 : ∀ i ∈ List.range 1, ThresholdAt 20 (99+i) := by decide +kernel

theorem threshold_20_100 : ∀ i ∈ List.range 1, ThresholdAt 20 (100+i) := by decide +kernel

theorem threshold_20_101 : ∀ i ∈ List.range 1, ThresholdAt 20 (101+i) := by decide +kernel

theorem threshold_20_102 : ∀ i ∈ List.range 1, ThresholdAt 20 (102+i) := by decide +kernel

theorem threshold_20_103 : ∀ i ∈ List.range 1, ThresholdAt 20 (103+i) := by decide +kernel

theorem threshold_20_104 : ∀ i ∈ List.range 1, ThresholdAt 20 (104+i) := by decide +kernel

theorem threshold_20_105 : ∀ i ∈ List.range 1, ThresholdAt 20 (105+i) := by decide +kernel

theorem threshold_20_106 : ∀ i ∈ List.range 1, ThresholdAt 20 (106+i) := by decide +kernel

theorem threshold_20_107 : ∀ i ∈ List.range 1, ThresholdAt 20 (107+i) := by decide +kernel

theorem threshold_20_108 : ∀ i ∈ List.range 1, ThresholdAt 20 (108+i) := by decide +kernel

theorem threshold_20_109 : ∀ i ∈ List.range 1, ThresholdAt 20 (109+i) := by decide +kernel

theorem threshold_20_110 : ∀ i ∈ List.range 1, ThresholdAt 20 (110+i) := by decide +kernel

theorem threshold_20_111 : ∀ i ∈ List.range 1, ThresholdAt 20 (111+i) := by decide +kernel

theorem threshold_20_112 : ∀ i ∈ List.range 1, ThresholdAt 20 (112+i) := by decide +kernel

theorem threshold_20_113 : ∀ i ∈ List.range 1, ThresholdAt 20 (113+i) := by decide +kernel

theorem threshold_20_114 : ∀ i ∈ List.range 1, ThresholdAt 20 (114+i) := by decide +kernel

theorem threshold_20_115 : ∀ i ∈ List.range 1, ThresholdAt 20 (115+i) := by decide +kernel

theorem threshold_20_116 : ∀ i ∈ List.range 1, ThresholdAt 20 (116+i) := by decide +kernel

theorem threshold_20_117 : ∀ i ∈ List.range 1, ThresholdAt 20 (117+i) := by decide +kernel

theorem threshold_20_118 : ∀ i ∈ List.range 1, ThresholdAt 20 (118+i) := by decide +kernel

theorem threshold_20_119 : ∀ i ∈ List.range 1, ThresholdAt 20 (119+i) := by decide +kernel

theorem threshold_20_120 : ∀ i ∈ List.range 1, ThresholdAt 20 (120+i) := by decide +kernel

theorem threshold_20_121 : ∀ i ∈ List.range 1, ThresholdAt 20 (121+i) := by decide +kernel

theorem threshold_20_122 : ∀ i ∈ List.range 1, ThresholdAt 20 (122+i) := by decide +kernel

theorem threshold_20_123 : ∀ i ∈ List.range 1, ThresholdAt 20 (123+i) := by decide +kernel

theorem threshold_20_124 : ∀ i ∈ List.range 1, ThresholdAt 20 (124+i) := by decide +kernel

theorem threshold_20_125 : ∀ i ∈ List.range 1, ThresholdAt 20 (125+i) := by decide +kernel

theorem threshold_20_126 : ∀ i ∈ List.range 1, ThresholdAt 20 (126+i) := by decide +kernel

theorem threshold_20_127 : ∀ i ∈ List.range 1, ThresholdAt 20 (127+i) := by decide +kernel

theorem threshold_20_128 : ∀ i ∈ List.range 1, ThresholdAt 20 (128+i) := by decide +kernel

theorem threshold_20_129 : ∀ i ∈ List.range 1, ThresholdAt 20 (129+i) := by decide +kernel

theorem threshold_20_130 : ∀ i ∈ List.range 1, ThresholdAt 20 (130+i) := by decide +kernel

theorem threshold_20_131 : ∀ i ∈ List.range 1, ThresholdAt 20 (131+i) := by decide +kernel

theorem threshold_20_132 : ∀ i ∈ List.range 1, ThresholdAt 20 (132+i) := by decide +kernel

theorem threshold_20_133 : ∀ i ∈ List.range 1, ThresholdAt 20 (133+i) := by decide +kernel

theorem threshold_20_134 : ∀ i ∈ List.range 1, ThresholdAt 20 (134+i) := by decide +kernel

theorem threshold_20_135 : ∀ i ∈ List.range 1, ThresholdAt 20 (135+i) := by decide +kernel

theorem threshold_20_136 : ∀ i ∈ List.range 1, ThresholdAt 20 (136+i) := by decide +kernel

theorem threshold_20 (v : ℕ) (hv : v ∈ List.range 137) : ThresholdAt 20 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 20 v)
  have h := (join 0 68 69 (join 0 34 34 (join 0 17 17 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_20_0 threshold_20_1) (join 2 1 1 threshold_20_2 threshold_20_3)) (join 4 2 2 (join 4 1 1 threshold_20_4 threshold_20_5) (join 6 1 1 threshold_20_6 threshold_20_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_20_8 threshold_20_9) (join 10 1 1 threshold_20_10 threshold_20_11)) (join 12 2 3 (join 12 1 1 threshold_20_12 threshold_20_13) (join 14 1 2 threshold_20_14 (join 15 1 1 threshold_20_15 threshold_20_16))))) (join 17 8 9 (join 17 4 4 (join 17 2 2 (join 17 1 1 threshold_20_17 threshold_20_18) (join 19 1 1 threshold_20_19 threshold_20_20)) (join 21 2 2 (join 21 1 1 threshold_20_21 threshold_20_22) (join 23 1 1 threshold_20_23 threshold_20_24))) (join 25 4 5 (join 25 2 2 (join 25 1 1 threshold_20_25 threshold_20_26) (join 27 1 1 threshold_20_27 threshold_20_28)) (join 29 2 3 (join 29 1 1 threshold_20_29 threshold_20_30) (join 31 1 2 threshold_20_31 (join 32 1 1 threshold_20_32 threshold_20_33)))))) (join 34 17 17 (join 34 8 9 (join 34 4 4 (join 34 2 2 (join 34 1 1 threshold_20_34 threshold_20_35) (join 36 1 1 threshold_20_36 threshold_20_37)) (join 38 2 2 (join 38 1 1 threshold_20_38 threshold_20_39) (join 40 1 1 threshold_20_40 threshold_20_41))) (join 42 4 5 (join 42 2 2 (join 42 1 1 threshold_20_42 threshold_20_43) (join 44 1 1 threshold_20_44 threshold_20_45)) (join 46 2 3 (join 46 1 1 threshold_20_46 threshold_20_47) (join 48 1 2 threshold_20_48 (join 49 1 1 threshold_20_49 threshold_20_50))))) (join 51 8 9 (join 51 4 4 (join 51 2 2 (join 51 1 1 threshold_20_51 threshold_20_52) (join 53 1 1 threshold_20_53 threshold_20_54)) (join 55 2 2 (join 55 1 1 threshold_20_55 threshold_20_56) (join 57 1 1 threshold_20_57 threshold_20_58))) (join 59 4 5 (join 59 2 2 (join 59 1 1 threshold_20_59 threshold_20_60) (join 61 1 1 threshold_20_61 threshold_20_62)) (join 63 2 3 (join 63 1 1 threshold_20_63 threshold_20_64) (join 65 1 2 threshold_20_65 (join 66 1 1 threshold_20_66 threshold_20_67))))))) (join 68 34 35 (join 68 17 17 (join 68 8 9 (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_20_68 threshold_20_69) (join 70 1 1 threshold_20_70 threshold_20_71)) (join 72 2 2 (join 72 1 1 threshold_20_72 threshold_20_73) (join 74 1 1 threshold_20_74 threshold_20_75))) (join 76 4 5 (join 76 2 2 (join 76 1 1 threshold_20_76 threshold_20_77) (join 78 1 1 threshold_20_78 threshold_20_79)) (join 80 2 3 (join 80 1 1 threshold_20_80 threshold_20_81) (join 82 1 2 threshold_20_82 (join 83 1 1 threshold_20_83 threshold_20_84))))) (join 85 8 9 (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_20_85 threshold_20_86) (join 87 1 1 threshold_20_87 threshold_20_88)) (join 89 2 2 (join 89 1 1 threshold_20_89 threshold_20_90) (join 91 1 1 threshold_20_91 threshold_20_92))) (join 93 4 5 (join 93 2 2 (join 93 1 1 threshold_20_93 threshold_20_94) (join 95 1 1 threshold_20_95 threshold_20_96)) (join 97 2 3 (join 97 1 1 threshold_20_97 threshold_20_98) (join 99 1 2 threshold_20_99 (join 100 1 1 threshold_20_100 threshold_20_101)))))) (join 102 17 18 (join 102 8 9 (join 102 4 4 (join 102 2 2 (join 102 1 1 threshold_20_102 threshold_20_103) (join 104 1 1 threshold_20_104 threshold_20_105)) (join 106 2 2 (join 106 1 1 threshold_20_106 threshold_20_107) (join 108 1 1 threshold_20_108 threshold_20_109))) (join 110 4 5 (join 110 2 2 (join 110 1 1 threshold_20_110 threshold_20_111) (join 112 1 1 threshold_20_112 threshold_20_113)) (join 114 2 3 (join 114 1 1 threshold_20_114 threshold_20_115) (join 116 1 2 threshold_20_116 (join 117 1 1 threshold_20_117 threshold_20_118))))) (join 119 9 9 (join 119 4 5 (join 119 2 2 (join 119 1 1 threshold_20_119 threshold_20_120) (join 121 1 1 threshold_20_121 threshold_20_122)) (join 123 2 3 (join 123 1 1 threshold_20_123 threshold_20_124) (join 125 1 2 threshold_20_125 (join 126 1 1 threshold_20_126 threshold_20_127)))) (join 128 4 5 (join 128 2 2 (join 128 1 1 threshold_20_128 threshold_20_129) (join 130 1 1 threshold_20_130 threshold_20_131)) (join 132 2 3 (join 132 1 1 threshold_20_132 threshold_20_133) (join 134 1 2 threshold_20_134 (join 135 1 1 threshold_20_135 threshold_20_136))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_20_0 : ∀ i ∈ List.range 4, LedgerAt 20 (0+i) := by decide +kernel

theorem ledger_20_4 : ∀ i ∈ List.range 4, LedgerAt 20 (4+i) := by decide +kernel

theorem ledger_20_8 : ∀ i ∈ List.range 4, LedgerAt 20 (8+i) := by decide +kernel

theorem ledger_20_12 : ∀ i ∈ List.range 4, LedgerAt 20 (12+i) := by decide +kernel

theorem ledger_20_16 : ∀ i ∈ List.range 4, LedgerAt 20 (16+i) := by decide +kernel

theorem ledger_20_20 : ∀ i ∈ List.range 4, LedgerAt 20 (20+i) := by decide +kernel

theorem ledger_20_24 : ∀ i ∈ List.range 4, LedgerAt 20 (24+i) := by decide +kernel

theorem ledger_20_28 : ∀ i ∈ List.range 4, LedgerAt 20 (28+i) := by decide +kernel

theorem ledger_20_32 : ∀ i ∈ List.range 4, LedgerAt 20 (32+i) := by decide +kernel

theorem ledger_20_36 : ∀ i ∈ List.range 4, LedgerAt 20 (36+i) := by decide +kernel

theorem ledger_20_40 : ∀ i ∈ List.range 4, LedgerAt 20 (40+i) := by decide +kernel

theorem ledger_20_44 : ∀ i ∈ List.range 4, LedgerAt 20 (44+i) := by decide +kernel

theorem ledger_20_48 : ∀ i ∈ List.range 4, LedgerAt 20 (48+i) := by decide +kernel

theorem ledger_20_52 : ∀ i ∈ List.range 4, LedgerAt 20 (52+i) := by decide +kernel

theorem ledger_20_56 : ∀ i ∈ List.range 4, LedgerAt 20 (56+i) := by decide +kernel

theorem ledger_20_60 : ∀ i ∈ List.range 4, LedgerAt 20 (60+i) := by decide +kernel

theorem ledger_20_64 : ∀ i ∈ List.range 4, LedgerAt 20 (64+i) := by decide +kernel

theorem ledger_20_68 : ∀ i ∈ List.range 4, LedgerAt 20 (68+i) := by decide +kernel

theorem ledger_20_72 : ∀ i ∈ List.range 4, LedgerAt 20 (72+i) := by decide +kernel

theorem ledger_20_76 : ∀ i ∈ List.range 4, LedgerAt 20 (76+i) := by decide +kernel

theorem ledger_20_80 : ∀ i ∈ List.range 4, LedgerAt 20 (80+i) := by decide +kernel

theorem ledger_20_84 : ∀ i ∈ List.range 4, LedgerAt 20 (84+i) := by decide +kernel

theorem ledger_20_88 : ∀ i ∈ List.range 4, LedgerAt 20 (88+i) := by decide +kernel

theorem ledger_20_92 : ∀ i ∈ List.range 4, LedgerAt 20 (92+i) := by decide +kernel

theorem ledger_20_96 : ∀ i ∈ List.range 4, LedgerAt 20 (96+i) := by decide +kernel

theorem ledger_20_100 : ∀ i ∈ List.range 4, LedgerAt 20 (100+i) := by decide +kernel

theorem ledger_20_104 : ∀ i ∈ List.range 4, LedgerAt 20 (104+i) := by decide +kernel

theorem ledger_20_108 : ∀ i ∈ List.range 4, LedgerAt 20 (108+i) := by decide +kernel

theorem ledger_20_112 : ∀ i ∈ List.range 4, LedgerAt 20 (112+i) := by decide +kernel

theorem ledger_20_116 : ∀ i ∈ List.range 4, LedgerAt 20 (116+i) := by decide +kernel

theorem ledger_20_120 : ∀ i ∈ List.range 4, LedgerAt 20 (120+i) := by decide +kernel

theorem ledger_20_124 : ∀ i ∈ List.range 4, LedgerAt 20 (124+i) := by decide +kernel

theorem ledger_20_128 : ∀ i ∈ List.range 4, LedgerAt 20 (128+i) := by decide +kernel

theorem ledger_20_132 : ∀ i ∈ List.range 4, LedgerAt 20 (132+i) := by decide +kernel

theorem ledger_20_136 : ∀ i ∈ List.range 1, LedgerAt 20 (136+i) := by decide +kernel

theorem ledger_20 (v : ℕ) (hv : v ∈ List.range 137) : LedgerAt 20 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 20 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_20_0 ledger_20_4) (join 8 4 4 ledger_20_8 ledger_20_12)) (join 16 8 8 (join 16 4 4 ledger_20_16 ledger_20_20) (join 24 4 4 ledger_20_24 ledger_20_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_20_32 ledger_20_36) (join 40 4 4 ledger_20_40 ledger_20_44)) (join 48 8 12 (join 48 4 4 ledger_20_48 ledger_20_52) (join 56 4 8 ledger_20_56 (join 60 4 4 ledger_20_60 ledger_20_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 ledger_20_68 ledger_20_72) (join 76 4 4 ledger_20_76 ledger_20_80)) (join 84 8 12 (join 84 4 4 ledger_20_84 ledger_20_88) (join 92 4 8 ledger_20_92 (join 96 4 4 ledger_20_96 ledger_20_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 ledger_20_104 ledger_20_108) (join 112 4 4 ledger_20_112 ledger_20_116)) (join 120 8 9 (join 120 4 4 ledger_20_120 ledger_20_124) (join 128 4 5 ledger_20_128 (join 132 4 1 ledger_20_132 ledger_20_136))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
