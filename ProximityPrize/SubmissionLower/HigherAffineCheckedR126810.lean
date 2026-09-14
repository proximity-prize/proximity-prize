import ProximityPrize.SubmissionLower.HigherAffineCheckedR116810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_12_0 : ∀ i ∈ List.range 4, SingleAt 12 (0+i) := by decide +kernel

theorem single_12_4 : ∀ i ∈ List.range 4, SingleAt 12 (4+i) := by decide +kernel

theorem single_12_8 : ∀ i ∈ List.range 4, SingleAt 12 (8+i) := by decide +kernel

theorem single_12_12 : ∀ i ∈ List.range 4, SingleAt 12 (12+i) := by decide +kernel

theorem single_12_16 : ∀ i ∈ List.range 4, SingleAt 12 (16+i) := by decide +kernel

theorem single_12_20 : ∀ i ∈ List.range 4, SingleAt 12 (20+i) := by decide +kernel

theorem single_12_24 : ∀ i ∈ List.range 4, SingleAt 12 (24+i) := by decide +kernel

theorem single_12_28 : ∀ i ∈ List.range 4, SingleAt 12 (28+i) := by decide +kernel

theorem single_12_32 : ∀ i ∈ List.range 4, SingleAt 12 (32+i) := by decide +kernel

theorem single_12_36 : ∀ i ∈ List.range 4, SingleAt 12 (36+i) := by decide +kernel

theorem single_12_40 : ∀ i ∈ List.range 4, SingleAt 12 (40+i) := by decide +kernel

theorem single_12_44 : ∀ i ∈ List.range 4, SingleAt 12 (44+i) := by decide +kernel

theorem single_12_48 : ∀ i ∈ List.range 4, SingleAt 12 (48+i) := by decide +kernel

theorem single_12_52 : ∀ i ∈ List.range 4, SingleAt 12 (52+i) := by decide +kernel

theorem single_12_56 : ∀ i ∈ List.range 4, SingleAt 12 (56+i) := by decide +kernel

theorem single_12_60 : ∀ i ∈ List.range 4, SingleAt 12 (60+i) := by decide +kernel

theorem single_12_64 : ∀ i ∈ List.range 4, SingleAt 12 (64+i) := by decide +kernel

theorem single_12_68 : ∀ i ∈ List.range 4, SingleAt 12 (68+i) := by decide +kernel

theorem single_12_72 : ∀ i ∈ List.range 4, SingleAt 12 (72+i) := by decide +kernel

theorem single_12_76 : ∀ i ∈ List.range 4, SingleAt 12 (76+i) := by decide +kernel

theorem single_12_80 : ∀ i ∈ List.range 4, SingleAt 12 (80+i) := by decide +kernel

theorem single_12_84 : ∀ i ∈ List.range 4, SingleAt 12 (84+i) := by decide +kernel

theorem single_12_88 : ∀ i ∈ List.range 4, SingleAt 12 (88+i) := by decide +kernel

theorem single_12_92 : ∀ i ∈ List.range 4, SingleAt 12 (92+i) := by decide +kernel

theorem single_12_96 : ∀ i ∈ List.range 4, SingleAt 12 (96+i) := by decide +kernel

theorem single_12_100 : ∀ i ∈ List.range 4, SingleAt 12 (100+i) := by decide +kernel

theorem single_12_104 : ∀ i ∈ List.range 4, SingleAt 12 (104+i) := by decide +kernel

theorem single_12_108 : ∀ i ∈ List.range 4, SingleAt 12 (108+i) := by decide +kernel

theorem single_12_112 : ∀ i ∈ List.range 4, SingleAt 12 (112+i) := by decide +kernel

theorem single_12_116 : ∀ i ∈ List.range 4, SingleAt 12 (116+i) := by decide +kernel

theorem single_12_120 : ∀ i ∈ List.range 4, SingleAt 12 (120+i) := by decide +kernel

theorem single_12_124 : ∀ i ∈ List.range 4, SingleAt 12 (124+i) := by decide +kernel

theorem single_12_128 : ∀ i ∈ List.range 4, SingleAt 12 (128+i) := by decide +kernel

theorem single_12_132 : ∀ i ∈ List.range 4, SingleAt 12 (132+i) := by decide +kernel

theorem single_12_136 : ∀ i ∈ List.range 4, SingleAt 12 (136+i) := by decide +kernel

theorem single_12_140 : ∀ i ∈ List.range 4, SingleAt 12 (140+i) := by decide +kernel

theorem single_12_144 : ∀ i ∈ List.range 1, SingleAt 12 (144+i) := by decide +kernel

theorem single_12 (v : ℕ) (hv : v ∈ List.range 145) : SingleAt 12 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 12 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_12_0 single_12_4) (join 8 4 4 single_12_8 single_12_12)) (join 16 8 12 (join 16 4 4 single_12_16 single_12_20) (join 24 4 8 single_12_24 (join 28 4 4 single_12_28 single_12_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_12_36 single_12_40) (join 44 4 4 single_12_44 single_12_48)) (join 52 8 12 (join 52 4 4 single_12_52 single_12_56) (join 60 4 8 single_12_60 (join 64 4 4 single_12_64 single_12_68))))) (join 72 36 37 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_12_72 single_12_76) (join 80 4 4 single_12_80 single_12_84)) (join 88 8 12 (join 88 4 4 single_12_88 single_12_92) (join 96 4 8 single_12_96 (join 100 4 4 single_12_100 single_12_104)))) (join 108 20 17 (join 108 8 12 (join 108 4 4 single_12_108 single_12_112) (join 116 4 8 single_12_116 (join 120 4 4 single_12_120 single_12_124))) (join 128 8 9 (join 128 4 4 single_12_128 single_12_132) (join 136 4 5 single_12_136 (join 140 4 1 single_12_140 single_12_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_12_0 : ∀ i ∈ List.range 4, PhaseAt 12 (0+i) := by decide +kernel

theorem phase_12_4 : ∀ i ∈ List.range 4, PhaseAt 12 (4+i) := by decide +kernel

theorem phase_12_8 : ∀ i ∈ List.range 4, PhaseAt 12 (8+i) := by decide +kernel

theorem phase_12_12 : ∀ i ∈ List.range 4, PhaseAt 12 (12+i) := by decide +kernel

theorem phase_12_16 : ∀ i ∈ List.range 4, PhaseAt 12 (16+i) := by decide +kernel

theorem phase_12_20 : ∀ i ∈ List.range 4, PhaseAt 12 (20+i) := by decide +kernel

theorem phase_12_24 : ∀ i ∈ List.range 4, PhaseAt 12 (24+i) := by decide +kernel

theorem phase_12_28 : ∀ i ∈ List.range 4, PhaseAt 12 (28+i) := by decide +kernel

theorem phase_12_32 : ∀ i ∈ List.range 4, PhaseAt 12 (32+i) := by decide +kernel

theorem phase_12_36 : ∀ i ∈ List.range 4, PhaseAt 12 (36+i) := by decide +kernel

theorem phase_12_40 : ∀ i ∈ List.range 4, PhaseAt 12 (40+i) := by decide +kernel

theorem phase_12_44 : ∀ i ∈ List.range 4, PhaseAt 12 (44+i) := by decide +kernel

theorem phase_12_48 : ∀ i ∈ List.range 4, PhaseAt 12 (48+i) := by decide +kernel

theorem phase_12_52 : ∀ i ∈ List.range 4, PhaseAt 12 (52+i) := by decide +kernel

theorem phase_12_56 : ∀ i ∈ List.range 4, PhaseAt 12 (56+i) := by decide +kernel

theorem phase_12_60 : ∀ i ∈ List.range 4, PhaseAt 12 (60+i) := by decide +kernel

theorem phase_12_64 : ∀ i ∈ List.range 4, PhaseAt 12 (64+i) := by decide +kernel

theorem phase_12_68 : ∀ i ∈ List.range 4, PhaseAt 12 (68+i) := by decide +kernel

theorem phase_12_72 : ∀ i ∈ List.range 4, PhaseAt 12 (72+i) := by decide +kernel

theorem phase_12_76 : ∀ i ∈ List.range 4, PhaseAt 12 (76+i) := by decide +kernel

theorem phase_12_80 : ∀ i ∈ List.range 4, PhaseAt 12 (80+i) := by decide +kernel

theorem phase_12_84 : ∀ i ∈ List.range 4, PhaseAt 12 (84+i) := by decide +kernel

theorem phase_12_88 : ∀ i ∈ List.range 4, PhaseAt 12 (88+i) := by decide +kernel

theorem phase_12_92 : ∀ i ∈ List.range 4, PhaseAt 12 (92+i) := by decide +kernel

theorem phase_12_96 : ∀ i ∈ List.range 4, PhaseAt 12 (96+i) := by decide +kernel

theorem phase_12_100 : ∀ i ∈ List.range 4, PhaseAt 12 (100+i) := by decide +kernel

theorem phase_12_104 : ∀ i ∈ List.range 4, PhaseAt 12 (104+i) := by decide +kernel

theorem phase_12_108 : ∀ i ∈ List.range 4, PhaseAt 12 (108+i) := by decide +kernel

theorem phase_12_112 : ∀ i ∈ List.range 4, PhaseAt 12 (112+i) := by decide +kernel

theorem phase_12_116 : ∀ i ∈ List.range 4, PhaseAt 12 (116+i) := by decide +kernel

theorem phase_12_120 : ∀ i ∈ List.range 4, PhaseAt 12 (120+i) := by decide +kernel

theorem phase_12_124 : ∀ i ∈ List.range 4, PhaseAt 12 (124+i) := by decide +kernel

theorem phase_12_128 : ∀ i ∈ List.range 4, PhaseAt 12 (128+i) := by decide +kernel

theorem phase_12_132 : ∀ i ∈ List.range 4, PhaseAt 12 (132+i) := by decide +kernel

theorem phase_12_136 : ∀ i ∈ List.range 4, PhaseAt 12 (136+i) := by decide +kernel

theorem phase_12_140 : ∀ i ∈ List.range 4, PhaseAt 12 (140+i) := by decide +kernel

theorem phase_12_144 : ∀ i ∈ List.range 1, PhaseAt 12 (144+i) := by decide +kernel

theorem phase_12 (v : ℕ) (hv : v ∈ List.range 145) : PhaseAt 12 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 12 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_12_0 phase_12_4) (join 8 4 4 phase_12_8 phase_12_12)) (join 16 8 12 (join 16 4 4 phase_12_16 phase_12_20) (join 24 4 8 phase_12_24 (join 28 4 4 phase_12_28 phase_12_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_12_36 phase_12_40) (join 44 4 4 phase_12_44 phase_12_48)) (join 52 8 12 (join 52 4 4 phase_12_52 phase_12_56) (join 60 4 8 phase_12_60 (join 64 4 4 phase_12_64 phase_12_68))))) (join 72 36 37 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_12_72 phase_12_76) (join 80 4 4 phase_12_80 phase_12_84)) (join 88 8 12 (join 88 4 4 phase_12_88 phase_12_92) (join 96 4 8 phase_12_96 (join 100 4 4 phase_12_100 phase_12_104)))) (join 108 20 17 (join 108 8 12 (join 108 4 4 phase_12_108 phase_12_112) (join 116 4 8 phase_12_116 (join 120 4 4 phase_12_120 phase_12_124))) (join 128 8 9 (join 128 4 4 phase_12_128 phase_12_132) (join 136 4 5 phase_12_136 (join 140 4 1 phase_12_140 phase_12_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_12_0 : ∀ i ∈ List.range 1, ThresholdAt 12 (0+i) := by decide +kernel

theorem threshold_12_1 : ∀ i ∈ List.range 1, ThresholdAt 12 (1+i) := by decide +kernel

theorem threshold_12_2 : ∀ i ∈ List.range 1, ThresholdAt 12 (2+i) := by decide +kernel

theorem threshold_12_3 : ∀ i ∈ List.range 1, ThresholdAt 12 (3+i) := by decide +kernel

theorem threshold_12_4 : ∀ i ∈ List.range 1, ThresholdAt 12 (4+i) := by decide +kernel

theorem threshold_12_5 : ∀ i ∈ List.range 1, ThresholdAt 12 (5+i) := by decide +kernel

theorem threshold_12_6 : ∀ i ∈ List.range 1, ThresholdAt 12 (6+i) := by decide +kernel

theorem threshold_12_7 : ∀ i ∈ List.range 1, ThresholdAt 12 (7+i) := by decide +kernel

theorem threshold_12_8 : ∀ i ∈ List.range 1, ThresholdAt 12 (8+i) := by decide +kernel

theorem threshold_12_9 : ∀ i ∈ List.range 1, ThresholdAt 12 (9+i) := by decide +kernel

theorem threshold_12_10 : ∀ i ∈ List.range 1, ThresholdAt 12 (10+i) := by decide +kernel

theorem threshold_12_11 : ∀ i ∈ List.range 1, ThresholdAt 12 (11+i) := by decide +kernel

theorem threshold_12_12 : ∀ i ∈ List.range 1, ThresholdAt 12 (12+i) := by decide +kernel

theorem threshold_12_13 : ∀ i ∈ List.range 1, ThresholdAt 12 (13+i) := by decide +kernel

theorem threshold_12_14 : ∀ i ∈ List.range 1, ThresholdAt 12 (14+i) := by decide +kernel

theorem threshold_12_15 : ∀ i ∈ List.range 1, ThresholdAt 12 (15+i) := by decide +kernel

theorem threshold_12_16 : ∀ i ∈ List.range 1, ThresholdAt 12 (16+i) := by decide +kernel

theorem threshold_12_17 : ∀ i ∈ List.range 1, ThresholdAt 12 (17+i) := by decide +kernel

theorem threshold_12_18 : ∀ i ∈ List.range 1, ThresholdAt 12 (18+i) := by decide +kernel

theorem threshold_12_19 : ∀ i ∈ List.range 1, ThresholdAt 12 (19+i) := by decide +kernel

theorem threshold_12_20 : ∀ i ∈ List.range 1, ThresholdAt 12 (20+i) := by decide +kernel

theorem threshold_12_21 : ∀ i ∈ List.range 1, ThresholdAt 12 (21+i) := by decide +kernel

theorem threshold_12_22 : ∀ i ∈ List.range 1, ThresholdAt 12 (22+i) := by decide +kernel

theorem threshold_12_23 : ∀ i ∈ List.range 1, ThresholdAt 12 (23+i) := by decide +kernel

theorem threshold_12_24 : ∀ i ∈ List.range 1, ThresholdAt 12 (24+i) := by decide +kernel

theorem threshold_12_25 : ∀ i ∈ List.range 1, ThresholdAt 12 (25+i) := by decide +kernel

theorem threshold_12_26 : ∀ i ∈ List.range 1, ThresholdAt 12 (26+i) := by decide +kernel

theorem threshold_12_27 : ∀ i ∈ List.range 1, ThresholdAt 12 (27+i) := by decide +kernel

theorem threshold_12_28 : ∀ i ∈ List.range 1, ThresholdAt 12 (28+i) := by decide +kernel

theorem threshold_12_29 : ∀ i ∈ List.range 1, ThresholdAt 12 (29+i) := by decide +kernel

theorem threshold_12_30 : ∀ i ∈ List.range 1, ThresholdAt 12 (30+i) := by decide +kernel

theorem threshold_12_31 : ∀ i ∈ List.range 1, ThresholdAt 12 (31+i) := by decide +kernel

theorem threshold_12_32 : ∀ i ∈ List.range 1, ThresholdAt 12 (32+i) := by decide +kernel

theorem threshold_12_33 : ∀ i ∈ List.range 1, ThresholdAt 12 (33+i) := by decide +kernel

theorem threshold_12_34 : ∀ i ∈ List.range 1, ThresholdAt 12 (34+i) := by decide +kernel

theorem threshold_12_35 : ∀ i ∈ List.range 1, ThresholdAt 12 (35+i) := by decide +kernel

theorem threshold_12_36 : ∀ i ∈ List.range 1, ThresholdAt 12 (36+i) := by decide +kernel

theorem threshold_12_37 : ∀ i ∈ List.range 1, ThresholdAt 12 (37+i) := by decide +kernel

theorem threshold_12_38 : ∀ i ∈ List.range 1, ThresholdAt 12 (38+i) := by decide +kernel

theorem threshold_12_39 : ∀ i ∈ List.range 1, ThresholdAt 12 (39+i) := by decide +kernel

theorem threshold_12_40 : ∀ i ∈ List.range 1, ThresholdAt 12 (40+i) := by decide +kernel

theorem threshold_12_41 : ∀ i ∈ List.range 1, ThresholdAt 12 (41+i) := by decide +kernel

theorem threshold_12_42 : ∀ i ∈ List.range 1, ThresholdAt 12 (42+i) := by decide +kernel

theorem threshold_12_43 : ∀ i ∈ List.range 1, ThresholdAt 12 (43+i) := by decide +kernel

theorem threshold_12_44 : ∀ i ∈ List.range 1, ThresholdAt 12 (44+i) := by decide +kernel

theorem threshold_12_45 : ∀ i ∈ List.range 1, ThresholdAt 12 (45+i) := by decide +kernel

theorem threshold_12_46 : ∀ i ∈ List.range 1, ThresholdAt 12 (46+i) := by decide +kernel

theorem threshold_12_47 : ∀ i ∈ List.range 1, ThresholdAt 12 (47+i) := by decide +kernel

theorem threshold_12_48 : ∀ i ∈ List.range 1, ThresholdAt 12 (48+i) := by decide +kernel

theorem threshold_12_49 : ∀ i ∈ List.range 1, ThresholdAt 12 (49+i) := by decide +kernel

theorem threshold_12_50 : ∀ i ∈ List.range 1, ThresholdAt 12 (50+i) := by decide +kernel

theorem threshold_12_51 : ∀ i ∈ List.range 1, ThresholdAt 12 (51+i) := by decide +kernel

theorem threshold_12_52 : ∀ i ∈ List.range 1, ThresholdAt 12 (52+i) := by decide +kernel

theorem threshold_12_53 : ∀ i ∈ List.range 1, ThresholdAt 12 (53+i) := by decide +kernel

theorem threshold_12_54 : ∀ i ∈ List.range 1, ThresholdAt 12 (54+i) := by decide +kernel

theorem threshold_12_55 : ∀ i ∈ List.range 1, ThresholdAt 12 (55+i) := by decide +kernel

theorem threshold_12_56 : ∀ i ∈ List.range 1, ThresholdAt 12 (56+i) := by decide +kernel

theorem threshold_12_57 : ∀ i ∈ List.range 1, ThresholdAt 12 (57+i) := by decide +kernel

theorem threshold_12_58 : ∀ i ∈ List.range 1, ThresholdAt 12 (58+i) := by decide +kernel

theorem threshold_12_59 : ∀ i ∈ List.range 1, ThresholdAt 12 (59+i) := by decide +kernel

theorem threshold_12_60 : ∀ i ∈ List.range 1, ThresholdAt 12 (60+i) := by decide +kernel

theorem threshold_12_61 : ∀ i ∈ List.range 1, ThresholdAt 12 (61+i) := by decide +kernel

theorem threshold_12_62 : ∀ i ∈ List.range 1, ThresholdAt 12 (62+i) := by decide +kernel

theorem threshold_12_63 : ∀ i ∈ List.range 1, ThresholdAt 12 (63+i) := by decide +kernel

theorem threshold_12_64 : ∀ i ∈ List.range 1, ThresholdAt 12 (64+i) := by decide +kernel

theorem threshold_12_65 : ∀ i ∈ List.range 1, ThresholdAt 12 (65+i) := by decide +kernel

theorem threshold_12_66 : ∀ i ∈ List.range 1, ThresholdAt 12 (66+i) := by decide +kernel

theorem threshold_12_67 : ∀ i ∈ List.range 1, ThresholdAt 12 (67+i) := by decide +kernel

theorem threshold_12_68 : ∀ i ∈ List.range 1, ThresholdAt 12 (68+i) := by decide +kernel

theorem threshold_12_69 : ∀ i ∈ List.range 1, ThresholdAt 12 (69+i) := by decide +kernel

theorem threshold_12_70 : ∀ i ∈ List.range 1, ThresholdAt 12 (70+i) := by decide +kernel

theorem threshold_12_71 : ∀ i ∈ List.range 1, ThresholdAt 12 (71+i) := by decide +kernel

theorem threshold_12_72 : ∀ i ∈ List.range 1, ThresholdAt 12 (72+i) := by decide +kernel

theorem threshold_12_73 : ∀ i ∈ List.range 1, ThresholdAt 12 (73+i) := by decide +kernel

theorem threshold_12_74 : ∀ i ∈ List.range 1, ThresholdAt 12 (74+i) := by decide +kernel

theorem threshold_12_75 : ∀ i ∈ List.range 1, ThresholdAt 12 (75+i) := by decide +kernel

theorem threshold_12_76 : ∀ i ∈ List.range 1, ThresholdAt 12 (76+i) := by decide +kernel

theorem threshold_12_77 : ∀ i ∈ List.range 1, ThresholdAt 12 (77+i) := by decide +kernel

theorem threshold_12_78 : ∀ i ∈ List.range 1, ThresholdAt 12 (78+i) := by decide +kernel

theorem threshold_12_79 : ∀ i ∈ List.range 1, ThresholdAt 12 (79+i) := by decide +kernel

theorem threshold_12_80 : ∀ i ∈ List.range 1, ThresholdAt 12 (80+i) := by decide +kernel

theorem threshold_12_81 : ∀ i ∈ List.range 1, ThresholdAt 12 (81+i) := by decide +kernel

theorem threshold_12_82 : ∀ i ∈ List.range 1, ThresholdAt 12 (82+i) := by decide +kernel

theorem threshold_12_83 : ∀ i ∈ List.range 1, ThresholdAt 12 (83+i) := by decide +kernel

theorem threshold_12_84 : ∀ i ∈ List.range 1, ThresholdAt 12 (84+i) := by decide +kernel

theorem threshold_12_85 : ∀ i ∈ List.range 1, ThresholdAt 12 (85+i) := by decide +kernel

theorem threshold_12_86 : ∀ i ∈ List.range 1, ThresholdAt 12 (86+i) := by decide +kernel

theorem threshold_12_87 : ∀ i ∈ List.range 1, ThresholdAt 12 (87+i) := by decide +kernel

theorem threshold_12_88 : ∀ i ∈ List.range 1, ThresholdAt 12 (88+i) := by decide +kernel

theorem threshold_12_89 : ∀ i ∈ List.range 1, ThresholdAt 12 (89+i) := by decide +kernel

theorem threshold_12_90 : ∀ i ∈ List.range 1, ThresholdAt 12 (90+i) := by decide +kernel

theorem threshold_12_91 : ∀ i ∈ List.range 1, ThresholdAt 12 (91+i) := by decide +kernel

theorem threshold_12_92 : ∀ i ∈ List.range 1, ThresholdAt 12 (92+i) := by decide +kernel

theorem threshold_12_93 : ∀ i ∈ List.range 1, ThresholdAt 12 (93+i) := by decide +kernel

theorem threshold_12_94 : ∀ i ∈ List.range 1, ThresholdAt 12 (94+i) := by decide +kernel

theorem threshold_12_95 : ∀ i ∈ List.range 1, ThresholdAt 12 (95+i) := by decide +kernel

theorem threshold_12_96 : ∀ i ∈ List.range 1, ThresholdAt 12 (96+i) := by decide +kernel

theorem threshold_12_97 : ∀ i ∈ List.range 1, ThresholdAt 12 (97+i) := by decide +kernel

theorem threshold_12_98 : ∀ i ∈ List.range 1, ThresholdAt 12 (98+i) := by decide +kernel

theorem threshold_12_99 : ∀ i ∈ List.range 1, ThresholdAt 12 (99+i) := by decide +kernel

theorem threshold_12_100 : ∀ i ∈ List.range 1, ThresholdAt 12 (100+i) := by decide +kernel

theorem threshold_12_101 : ∀ i ∈ List.range 1, ThresholdAt 12 (101+i) := by decide +kernel

theorem threshold_12_102 : ∀ i ∈ List.range 1, ThresholdAt 12 (102+i) := by decide +kernel

theorem threshold_12_103 : ∀ i ∈ List.range 1, ThresholdAt 12 (103+i) := by decide +kernel

theorem threshold_12_104 : ∀ i ∈ List.range 1, ThresholdAt 12 (104+i) := by decide +kernel

theorem threshold_12_105 : ∀ i ∈ List.range 1, ThresholdAt 12 (105+i) := by decide +kernel

theorem threshold_12_106 : ∀ i ∈ List.range 1, ThresholdAt 12 (106+i) := by decide +kernel

theorem threshold_12_107 : ∀ i ∈ List.range 1, ThresholdAt 12 (107+i) := by decide +kernel

theorem threshold_12_108 : ∀ i ∈ List.range 1, ThresholdAt 12 (108+i) := by decide +kernel

theorem threshold_12_109 : ∀ i ∈ List.range 1, ThresholdAt 12 (109+i) := by decide +kernel

theorem threshold_12_110 : ∀ i ∈ List.range 1, ThresholdAt 12 (110+i) := by decide +kernel

theorem threshold_12_111 : ∀ i ∈ List.range 1, ThresholdAt 12 (111+i) := by decide +kernel

theorem threshold_12_112 : ∀ i ∈ List.range 1, ThresholdAt 12 (112+i) := by decide +kernel

theorem threshold_12_113 : ∀ i ∈ List.range 1, ThresholdAt 12 (113+i) := by decide +kernel

theorem threshold_12_114 : ∀ i ∈ List.range 1, ThresholdAt 12 (114+i) := by decide +kernel

theorem threshold_12_115 : ∀ i ∈ List.range 1, ThresholdAt 12 (115+i) := by decide +kernel

theorem threshold_12_116 : ∀ i ∈ List.range 1, ThresholdAt 12 (116+i) := by decide +kernel

theorem threshold_12_117 : ∀ i ∈ List.range 1, ThresholdAt 12 (117+i) := by decide +kernel

theorem threshold_12_118 : ∀ i ∈ List.range 1, ThresholdAt 12 (118+i) := by decide +kernel

theorem threshold_12_119 : ∀ i ∈ List.range 1, ThresholdAt 12 (119+i) := by decide +kernel

theorem threshold_12_120 : ∀ i ∈ List.range 1, ThresholdAt 12 (120+i) := by decide +kernel

theorem threshold_12_121 : ∀ i ∈ List.range 1, ThresholdAt 12 (121+i) := by decide +kernel

theorem threshold_12_122 : ∀ i ∈ List.range 1, ThresholdAt 12 (122+i) := by decide +kernel

theorem threshold_12_123 : ∀ i ∈ List.range 1, ThresholdAt 12 (123+i) := by decide +kernel

theorem threshold_12_124 : ∀ i ∈ List.range 1, ThresholdAt 12 (124+i) := by decide +kernel

theorem threshold_12_125 : ∀ i ∈ List.range 1, ThresholdAt 12 (125+i) := by decide +kernel

theorem threshold_12_126 : ∀ i ∈ List.range 1, ThresholdAt 12 (126+i) := by decide +kernel

theorem threshold_12_127 : ∀ i ∈ List.range 1, ThresholdAt 12 (127+i) := by decide +kernel

theorem threshold_12_128 : ∀ i ∈ List.range 1, ThresholdAt 12 (128+i) := by decide +kernel

theorem threshold_12_129 : ∀ i ∈ List.range 1, ThresholdAt 12 (129+i) := by decide +kernel

theorem threshold_12_130 : ∀ i ∈ List.range 1, ThresholdAt 12 (130+i) := by decide +kernel

theorem threshold_12_131 : ∀ i ∈ List.range 1, ThresholdAt 12 (131+i) := by decide +kernel

theorem threshold_12_132 : ∀ i ∈ List.range 1, ThresholdAt 12 (132+i) := by decide +kernel

theorem threshold_12_133 : ∀ i ∈ List.range 1, ThresholdAt 12 (133+i) := by decide +kernel

theorem threshold_12_134 : ∀ i ∈ List.range 1, ThresholdAt 12 (134+i) := by decide +kernel

theorem threshold_12_135 : ∀ i ∈ List.range 1, ThresholdAt 12 (135+i) := by decide +kernel

theorem threshold_12_136 : ∀ i ∈ List.range 1, ThresholdAt 12 (136+i) := by decide +kernel

theorem threshold_12_137 : ∀ i ∈ List.range 1, ThresholdAt 12 (137+i) := by decide +kernel

theorem threshold_12_138 : ∀ i ∈ List.range 1, ThresholdAt 12 (138+i) := by decide +kernel

theorem threshold_12_139 : ∀ i ∈ List.range 1, ThresholdAt 12 (139+i) := by decide +kernel

theorem threshold_12_140 : ∀ i ∈ List.range 1, ThresholdAt 12 (140+i) := by decide +kernel

theorem threshold_12_141 : ∀ i ∈ List.range 1, ThresholdAt 12 (141+i) := by decide +kernel

theorem threshold_12_142 : ∀ i ∈ List.range 1, ThresholdAt 12 (142+i) := by decide +kernel

theorem threshold_12_143 : ∀ i ∈ List.range 1, ThresholdAt 12 (143+i) := by decide +kernel

theorem threshold_12_144 : ∀ i ∈ List.range 1, ThresholdAt 12 (144+i) := by decide +kernel

theorem threshold_12 (v : ℕ) (hv : v ∈ List.range 145) : ThresholdAt 12 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 12 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 18 18 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_12_0 threshold_12_1) (join 2 1 1 threshold_12_2 threshold_12_3)) (join 4 2 3 (join 4 1 1 threshold_12_4 threshold_12_5) (join 6 1 2 threshold_12_6 (join 7 1 1 threshold_12_7 threshold_12_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 threshold_12_9 threshold_12_10) (join 11 1 1 threshold_12_11 threshold_12_12)) (join 13 2 3 (join 13 1 1 threshold_12_13 threshold_12_14) (join 15 1 2 threshold_12_15 (join 16 1 1 threshold_12_16 threshold_12_17))))) (join 18 9 9 (join 18 4 5 (join 18 2 2 (join 18 1 1 threshold_12_18 threshold_12_19) (join 20 1 1 threshold_12_20 threshold_12_21)) (join 22 2 3 (join 22 1 1 threshold_12_22 threshold_12_23) (join 24 1 2 threshold_12_24 (join 25 1 1 threshold_12_25 threshold_12_26)))) (join 27 4 5 (join 27 2 2 (join 27 1 1 threshold_12_27 threshold_12_28) (join 29 1 1 threshold_12_29 threshold_12_30)) (join 31 2 3 (join 31 1 1 threshold_12_31 threshold_12_32) (join 33 1 2 threshold_12_33 (join 34 1 1 threshold_12_34 threshold_12_35)))))) (join 36 18 18 (join 36 9 9 (join 36 4 5 (join 36 2 2 (join 36 1 1 threshold_12_36 threshold_12_37) (join 38 1 1 threshold_12_38 threshold_12_39)) (join 40 2 3 (join 40 1 1 threshold_12_40 threshold_12_41) (join 42 1 2 threshold_12_42 (join 43 1 1 threshold_12_43 threshold_12_44)))) (join 45 4 5 (join 45 2 2 (join 45 1 1 threshold_12_45 threshold_12_46) (join 47 1 1 threshold_12_47 threshold_12_48)) (join 49 2 3 (join 49 1 1 threshold_12_49 threshold_12_50) (join 51 1 2 threshold_12_51 (join 52 1 1 threshold_12_52 threshold_12_53))))) (join 54 9 9 (join 54 4 5 (join 54 2 2 (join 54 1 1 threshold_12_54 threshold_12_55) (join 56 1 1 threshold_12_56 threshold_12_57)) (join 58 2 3 (join 58 1 1 threshold_12_58 threshold_12_59) (join 60 1 2 threshold_12_60 (join 61 1 1 threshold_12_61 threshold_12_62)))) (join 63 4 5 (join 63 2 2 (join 63 1 1 threshold_12_63 threshold_12_64) (join 65 1 1 threshold_12_65 threshold_12_66)) (join 67 2 3 (join 67 1 1 threshold_12_67 threshold_12_68) (join 69 1 2 threshold_12_69 (join 70 1 1 threshold_12_70 threshold_12_71))))))) (join 72 36 37 (join 72 18 18 (join 72 9 9 (join 72 4 5 (join 72 2 2 (join 72 1 1 threshold_12_72 threshold_12_73) (join 74 1 1 threshold_12_74 threshold_12_75)) (join 76 2 3 (join 76 1 1 threshold_12_76 threshold_12_77) (join 78 1 2 threshold_12_78 (join 79 1 1 threshold_12_79 threshold_12_80)))) (join 81 4 5 (join 81 2 2 (join 81 1 1 threshold_12_81 threshold_12_82) (join 83 1 1 threshold_12_83 threshold_12_84)) (join 85 2 3 (join 85 1 1 threshold_12_85 threshold_12_86) (join 87 1 2 threshold_12_87 (join 88 1 1 threshold_12_88 threshold_12_89))))) (join 90 9 9 (join 90 4 5 (join 90 2 2 (join 90 1 1 threshold_12_90 threshold_12_91) (join 92 1 1 threshold_12_92 threshold_12_93)) (join 94 2 3 (join 94 1 1 threshold_12_94 threshold_12_95) (join 96 1 2 threshold_12_96 (join 97 1 1 threshold_12_97 threshold_12_98)))) (join 99 4 5 (join 99 2 2 (join 99 1 1 threshold_12_99 threshold_12_100) (join 101 1 1 threshold_12_101 threshold_12_102)) (join 103 2 3 (join 103 1 1 threshold_12_103 threshold_12_104) (join 105 1 2 threshold_12_105 (join 106 1 1 threshold_12_106 threshold_12_107)))))) (join 108 18 19 (join 108 9 9 (join 108 4 5 (join 108 2 2 (join 108 1 1 threshold_12_108 threshold_12_109) (join 110 1 1 threshold_12_110 threshold_12_111)) (join 112 2 3 (join 112 1 1 threshold_12_112 threshold_12_113) (join 114 1 2 threshold_12_114 (join 115 1 1 threshold_12_115 threshold_12_116)))) (join 117 4 5 (join 117 2 2 (join 117 1 1 threshold_12_117 threshold_12_118) (join 119 1 1 threshold_12_119 threshold_12_120)) (join 121 2 3 (join 121 1 1 threshold_12_121 threshold_12_122) (join 123 1 2 threshold_12_123 (join 124 1 1 threshold_12_124 threshold_12_125))))) (join 126 9 10 (join 126 4 5 (join 126 2 2 (join 126 1 1 threshold_12_126 threshold_12_127) (join 128 1 1 threshold_12_128 threshold_12_129)) (join 130 2 3 (join 130 1 1 threshold_12_130 threshold_12_131) (join 132 1 2 threshold_12_132 (join 133 1 1 threshold_12_133 threshold_12_134)))) (join 135 5 5 (join 135 2 3 (join 135 1 1 threshold_12_135 threshold_12_136) (join 137 1 2 threshold_12_137 (join 138 1 1 threshold_12_138 threshold_12_139))) (join 140 2 3 (join 140 1 1 threshold_12_140 threshold_12_141) (join 142 1 2 threshold_12_142 (join 143 1 1 threshold_12_143 threshold_12_144))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_12_0 : ∀ i ∈ List.range 4, LedgerAt 12 (0+i) := by decide +kernel

theorem ledger_12_4 : ∀ i ∈ List.range 4, LedgerAt 12 (4+i) := by decide +kernel

theorem ledger_12_8 : ∀ i ∈ List.range 4, LedgerAt 12 (8+i) := by decide +kernel

theorem ledger_12_12 : ∀ i ∈ List.range 4, LedgerAt 12 (12+i) := by decide +kernel

theorem ledger_12_16 : ∀ i ∈ List.range 4, LedgerAt 12 (16+i) := by decide +kernel

theorem ledger_12_20 : ∀ i ∈ List.range 4, LedgerAt 12 (20+i) := by decide +kernel

theorem ledger_12_24 : ∀ i ∈ List.range 4, LedgerAt 12 (24+i) := by decide +kernel

theorem ledger_12_28 : ∀ i ∈ List.range 4, LedgerAt 12 (28+i) := by decide +kernel

theorem ledger_12_32 : ∀ i ∈ List.range 4, LedgerAt 12 (32+i) := by decide +kernel

theorem ledger_12_36 : ∀ i ∈ List.range 4, LedgerAt 12 (36+i) := by decide +kernel

theorem ledger_12_40 : ∀ i ∈ List.range 4, LedgerAt 12 (40+i) := by decide +kernel

theorem ledger_12_44 : ∀ i ∈ List.range 4, LedgerAt 12 (44+i) := by decide +kernel

theorem ledger_12_48 : ∀ i ∈ List.range 4, LedgerAt 12 (48+i) := by decide +kernel

theorem ledger_12_52 : ∀ i ∈ List.range 4, LedgerAt 12 (52+i) := by decide +kernel

theorem ledger_12_56 : ∀ i ∈ List.range 4, LedgerAt 12 (56+i) := by decide +kernel

theorem ledger_12_60 : ∀ i ∈ List.range 4, LedgerAt 12 (60+i) := by decide +kernel

theorem ledger_12_64 : ∀ i ∈ List.range 4, LedgerAt 12 (64+i) := by decide +kernel

theorem ledger_12_68 : ∀ i ∈ List.range 4, LedgerAt 12 (68+i) := by decide +kernel

theorem ledger_12_72 : ∀ i ∈ List.range 4, LedgerAt 12 (72+i) := by decide +kernel

theorem ledger_12_76 : ∀ i ∈ List.range 4, LedgerAt 12 (76+i) := by decide +kernel

theorem ledger_12_80 : ∀ i ∈ List.range 4, LedgerAt 12 (80+i) := by decide +kernel

theorem ledger_12_84 : ∀ i ∈ List.range 4, LedgerAt 12 (84+i) := by decide +kernel

theorem ledger_12_88 : ∀ i ∈ List.range 4, LedgerAt 12 (88+i) := by decide +kernel

theorem ledger_12_92 : ∀ i ∈ List.range 4, LedgerAt 12 (92+i) := by decide +kernel

theorem ledger_12_96 : ∀ i ∈ List.range 4, LedgerAt 12 (96+i) := by decide +kernel

theorem ledger_12_100 : ∀ i ∈ List.range 4, LedgerAt 12 (100+i) := by decide +kernel

theorem ledger_12_104 : ∀ i ∈ List.range 4, LedgerAt 12 (104+i) := by decide +kernel

theorem ledger_12_108 : ∀ i ∈ List.range 4, LedgerAt 12 (108+i) := by decide +kernel

theorem ledger_12_112 : ∀ i ∈ List.range 4, LedgerAt 12 (112+i) := by decide +kernel

theorem ledger_12_116 : ∀ i ∈ List.range 4, LedgerAt 12 (116+i) := by decide +kernel

theorem ledger_12_120 : ∀ i ∈ List.range 4, LedgerAt 12 (120+i) := by decide +kernel

theorem ledger_12_124 : ∀ i ∈ List.range 4, LedgerAt 12 (124+i) := by decide +kernel

theorem ledger_12_128 : ∀ i ∈ List.range 4, LedgerAt 12 (128+i) := by decide +kernel

theorem ledger_12_132 : ∀ i ∈ List.range 4, LedgerAt 12 (132+i) := by decide +kernel

theorem ledger_12_136 : ∀ i ∈ List.range 4, LedgerAt 12 (136+i) := by decide +kernel

theorem ledger_12_140 : ∀ i ∈ List.range 4, LedgerAt 12 (140+i) := by decide +kernel

theorem ledger_12_144 : ∀ i ∈ List.range 1, LedgerAt 12 (144+i) := by decide +kernel

theorem ledger_12 (v : ℕ) (hv : v ∈ List.range 145) : LedgerAt 12 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 12 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_12_0 ledger_12_4) (join 8 4 4 ledger_12_8 ledger_12_12)) (join 16 8 12 (join 16 4 4 ledger_12_16 ledger_12_20) (join 24 4 8 ledger_12_24 (join 28 4 4 ledger_12_28 ledger_12_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_12_36 ledger_12_40) (join 44 4 4 ledger_12_44 ledger_12_48)) (join 52 8 12 (join 52 4 4 ledger_12_52 ledger_12_56) (join 60 4 8 ledger_12_60 (join 64 4 4 ledger_12_64 ledger_12_68))))) (join 72 36 37 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_12_72 ledger_12_76) (join 80 4 4 ledger_12_80 ledger_12_84)) (join 88 8 12 (join 88 4 4 ledger_12_88 ledger_12_92) (join 96 4 8 ledger_12_96 (join 100 4 4 ledger_12_100 ledger_12_104)))) (join 108 20 17 (join 108 8 12 (join 108 4 4 ledger_12_108 ledger_12_112) (join 116 4 8 ledger_12_116 (join 120 4 4 ledger_12_120 ledger_12_124))) (join 128 8 9 (join 128 4 4 ledger_12_128 ledger_12_132) (join 136 4 5 ledger_12_136 (join 140 4 1 ledger_12_140 ledger_12_144))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
