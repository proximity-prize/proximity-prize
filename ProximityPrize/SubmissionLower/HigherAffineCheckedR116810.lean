import ProximityPrize.SubmissionLower.HigherAffineCheckedR106810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
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

theorem single_11_136 : ∀ i ∈ List.range 4, SingleAt 11 (136+i) := by decide +kernel

theorem single_11_140 : ∀ i ∈ List.range 4, SingleAt 11 (140+i) := by decide +kernel

theorem single_11_144 : ∀ i ∈ List.range 2, SingleAt 11 (144+i) := by decide +kernel

theorem single_11 (v : ℕ) (hv : v ∈ List.range 146) : SingleAt 11 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 11 v)
  have h := (join 0 72 74 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_11_0 single_11_4) (join 8 4 4 single_11_8 single_11_12)) (join 16 8 12 (join 16 4 4 single_11_16 single_11_20) (join 24 4 8 single_11_24 (join 28 4 4 single_11_28 single_11_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_11_36 single_11_40) (join 44 4 4 single_11_44 single_11_48)) (join 52 8 12 (join 52 4 4 single_11_52 single_11_56) (join 60 4 8 single_11_60 (join 64 4 4 single_11_64 single_11_68))))) (join 72 36 38 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_11_72 single_11_76) (join 80 4 4 single_11_80 single_11_84)) (join 88 8 12 (join 88 4 4 single_11_88 single_11_92) (join 96 4 8 single_11_96 (join 100 4 4 single_11_100 single_11_104)))) (join 108 20 18 (join 108 8 12 (join 108 4 4 single_11_108 single_11_112) (join 116 4 8 single_11_116 (join 120 4 4 single_11_120 single_11_124))) (join 128 8 10 (join 128 4 4 single_11_128 single_11_132) (join 136 4 6 single_11_136 (join 140 4 2 single_11_140 single_11_144))))))
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

theorem phase_11_136 : ∀ i ∈ List.range 4, PhaseAt 11 (136+i) := by decide +kernel

theorem phase_11_140 : ∀ i ∈ List.range 4, PhaseAt 11 (140+i) := by decide +kernel

theorem phase_11_144 : ∀ i ∈ List.range 2, PhaseAt 11 (144+i) := by decide +kernel

theorem phase_11 (v : ℕ) (hv : v ∈ List.range 146) : PhaseAt 11 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 11 v)
  have h := (join 0 72 74 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_11_0 phase_11_4) (join 8 4 4 phase_11_8 phase_11_12)) (join 16 8 12 (join 16 4 4 phase_11_16 phase_11_20) (join 24 4 8 phase_11_24 (join 28 4 4 phase_11_28 phase_11_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_11_36 phase_11_40) (join 44 4 4 phase_11_44 phase_11_48)) (join 52 8 12 (join 52 4 4 phase_11_52 phase_11_56) (join 60 4 8 phase_11_60 (join 64 4 4 phase_11_64 phase_11_68))))) (join 72 36 38 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_11_72 phase_11_76) (join 80 4 4 phase_11_80 phase_11_84)) (join 88 8 12 (join 88 4 4 phase_11_88 phase_11_92) (join 96 4 8 phase_11_96 (join 100 4 4 phase_11_100 phase_11_104)))) (join 108 20 18 (join 108 8 12 (join 108 4 4 phase_11_108 phase_11_112) (join 116 4 8 phase_11_116 (join 120 4 4 phase_11_120 phase_11_124))) (join 128 8 10 (join 128 4 4 phase_11_128 phase_11_132) (join 136 4 6 phase_11_136 (join 140 4 2 phase_11_140 phase_11_144))))))
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

theorem threshold_11_139 : ∀ i ∈ List.range 1, ThresholdAt 11 (139+i) := by decide +kernel

theorem threshold_11_140 : ∀ i ∈ List.range 1, ThresholdAt 11 (140+i) := by decide +kernel

theorem threshold_11_141 : ∀ i ∈ List.range 1, ThresholdAt 11 (141+i) := by decide +kernel

theorem threshold_11_142 : ∀ i ∈ List.range 1, ThresholdAt 11 (142+i) := by decide +kernel

theorem threshold_11_143 : ∀ i ∈ List.range 1, ThresholdAt 11 (143+i) := by decide +kernel

theorem threshold_11_144 : ∀ i ∈ List.range 1, ThresholdAt 11 (144+i) := by decide +kernel

theorem threshold_11_145 : ∀ i ∈ List.range 1, ThresholdAt 11 (145+i) := by decide +kernel

theorem threshold_11 (v : ℕ) (hv : v ∈ List.range 146) : ThresholdAt 11 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 11 v)
  have h := (join 0 73 73 (join 0 36 37 (join 0 18 18 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_11_0 threshold_11_1) (join 2 1 1 threshold_11_2 threshold_11_3)) (join 4 2 3 (join 4 1 1 threshold_11_4 threshold_11_5) (join 6 1 2 threshold_11_6 (join 7 1 1 threshold_11_7 threshold_11_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 threshold_11_9 threshold_11_10) (join 11 1 1 threshold_11_11 threshold_11_12)) (join 13 2 3 (join 13 1 1 threshold_11_13 threshold_11_14) (join 15 1 2 threshold_11_15 (join 16 1 1 threshold_11_16 threshold_11_17))))) (join 18 9 9 (join 18 4 5 (join 18 2 2 (join 18 1 1 threshold_11_18 threshold_11_19) (join 20 1 1 threshold_11_20 threshold_11_21)) (join 22 2 3 (join 22 1 1 threshold_11_22 threshold_11_23) (join 24 1 2 threshold_11_24 (join 25 1 1 threshold_11_25 threshold_11_26)))) (join 27 4 5 (join 27 2 2 (join 27 1 1 threshold_11_27 threshold_11_28) (join 29 1 1 threshold_11_29 threshold_11_30)) (join 31 2 3 (join 31 1 1 threshold_11_31 threshold_11_32) (join 33 1 2 threshold_11_33 (join 34 1 1 threshold_11_34 threshold_11_35)))))) (join 36 18 19 (join 36 9 9 (join 36 4 5 (join 36 2 2 (join 36 1 1 threshold_11_36 threshold_11_37) (join 38 1 1 threshold_11_38 threshold_11_39)) (join 40 2 3 (join 40 1 1 threshold_11_40 threshold_11_41) (join 42 1 2 threshold_11_42 (join 43 1 1 threshold_11_43 threshold_11_44)))) (join 45 4 5 (join 45 2 2 (join 45 1 1 threshold_11_45 threshold_11_46) (join 47 1 1 threshold_11_47 threshold_11_48)) (join 49 2 3 (join 49 1 1 threshold_11_49 threshold_11_50) (join 51 1 2 threshold_11_51 (join 52 1 1 threshold_11_52 threshold_11_53))))) (join 54 9 10 (join 54 4 5 (join 54 2 2 (join 54 1 1 threshold_11_54 threshold_11_55) (join 56 1 1 threshold_11_56 threshold_11_57)) (join 58 2 3 (join 58 1 1 threshold_11_58 threshold_11_59) (join 60 1 2 threshold_11_60 (join 61 1 1 threshold_11_61 threshold_11_62)))) (join 63 5 5 (join 63 2 3 (join 63 1 1 threshold_11_63 threshold_11_64) (join 65 1 2 threshold_11_65 (join 66 1 1 threshold_11_66 threshold_11_67))) (join 68 2 3 (join 68 1 1 threshold_11_68 threshold_11_69) (join 70 1 2 threshold_11_70 (join 71 1 1 threshold_11_71 threshold_11_72))))))) (join 73 36 37 (join 73 18 18 (join 73 9 9 (join 73 4 5 (join 73 2 2 (join 73 1 1 threshold_11_73 threshold_11_74) (join 75 1 1 threshold_11_75 threshold_11_76)) (join 77 2 3 (join 77 1 1 threshold_11_77 threshold_11_78) (join 79 1 2 threshold_11_79 (join 80 1 1 threshold_11_80 threshold_11_81)))) (join 82 4 5 (join 82 2 2 (join 82 1 1 threshold_11_82 threshold_11_83) (join 84 1 1 threshold_11_84 threshold_11_85)) (join 86 2 3 (join 86 1 1 threshold_11_86 threshold_11_87) (join 88 1 2 threshold_11_88 (join 89 1 1 threshold_11_89 threshold_11_90))))) (join 91 9 9 (join 91 4 5 (join 91 2 2 (join 91 1 1 threshold_11_91 threshold_11_92) (join 93 1 1 threshold_11_93 threshold_11_94)) (join 95 2 3 (join 95 1 1 threshold_11_95 threshold_11_96) (join 97 1 2 threshold_11_97 (join 98 1 1 threshold_11_98 threshold_11_99)))) (join 100 4 5 (join 100 2 2 (join 100 1 1 threshold_11_100 threshold_11_101) (join 102 1 1 threshold_11_102 threshold_11_103)) (join 104 2 3 (join 104 1 1 threshold_11_104 threshold_11_105) (join 106 1 2 threshold_11_106 (join 107 1 1 threshold_11_107 threshold_11_108)))))) (join 109 18 19 (join 109 9 9 (join 109 4 5 (join 109 2 2 (join 109 1 1 threshold_11_109 threshold_11_110) (join 111 1 1 threshold_11_111 threshold_11_112)) (join 113 2 3 (join 113 1 1 threshold_11_113 threshold_11_114) (join 115 1 2 threshold_11_115 (join 116 1 1 threshold_11_116 threshold_11_117)))) (join 118 4 5 (join 118 2 2 (join 118 1 1 threshold_11_118 threshold_11_119) (join 120 1 1 threshold_11_120 threshold_11_121)) (join 122 2 3 (join 122 1 1 threshold_11_122 threshold_11_123) (join 124 1 2 threshold_11_124 (join 125 1 1 threshold_11_125 threshold_11_126))))) (join 127 9 10 (join 127 4 5 (join 127 2 2 (join 127 1 1 threshold_11_127 threshold_11_128) (join 129 1 1 threshold_11_129 threshold_11_130)) (join 131 2 3 (join 131 1 1 threshold_11_131 threshold_11_132) (join 133 1 2 threshold_11_133 (join 134 1 1 threshold_11_134 threshold_11_135)))) (join 136 5 5 (join 136 2 3 (join 136 1 1 threshold_11_136 threshold_11_137) (join 138 1 2 threshold_11_138 (join 139 1 1 threshold_11_139 threshold_11_140))) (join 141 2 3 (join 141 1 1 threshold_11_141 threshold_11_142) (join 143 1 2 threshold_11_143 (join 144 1 1 threshold_11_144 threshold_11_145))))))))
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

theorem ledger_11_136 : ∀ i ∈ List.range 4, LedgerAt 11 (136+i) := by decide +kernel

theorem ledger_11_140 : ∀ i ∈ List.range 4, LedgerAt 11 (140+i) := by decide +kernel

theorem ledger_11_144 : ∀ i ∈ List.range 2, LedgerAt 11 (144+i) := by decide +kernel

theorem ledger_11 (v : ℕ) (hv : v ∈ List.range 146) : LedgerAt 11 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 11 v)
  have h := (join 0 72 74 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_11_0 ledger_11_4) (join 8 4 4 ledger_11_8 ledger_11_12)) (join 16 8 12 (join 16 4 4 ledger_11_16 ledger_11_20) (join 24 4 8 ledger_11_24 (join 28 4 4 ledger_11_28 ledger_11_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_11_36 ledger_11_40) (join 44 4 4 ledger_11_44 ledger_11_48)) (join 52 8 12 (join 52 4 4 ledger_11_52 ledger_11_56) (join 60 4 8 ledger_11_60 (join 64 4 4 ledger_11_64 ledger_11_68))))) (join 72 36 38 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_11_72 ledger_11_76) (join 80 4 4 ledger_11_80 ledger_11_84)) (join 88 8 12 (join 88 4 4 ledger_11_88 ledger_11_92) (join 96 4 8 ledger_11_96 (join 100 4 4 ledger_11_100 ledger_11_104)))) (join 108 20 18 (join 108 8 12 (join 108 4 4 ledger_11_108 ledger_11_112) (join 116 4 8 ledger_11_116 (join 120 4 4 ledger_11_120 ledger_11_124))) (join 128 8 10 (join 128 4 4 ledger_11_128 ledger_11_132) (join 136 4 6 ledger_11_136 (join 140 4 2 ledger_11_140 ledger_11_144))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
