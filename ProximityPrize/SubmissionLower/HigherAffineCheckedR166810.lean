import ProximityPrize.SubmissionLower.HigherAffineCheckedR156810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_16_0 : ∀ i ∈ List.range 4, SingleAt 16 (0+i) := by decide +kernel

theorem single_16_4 : ∀ i ∈ List.range 4, SingleAt 16 (4+i) := by decide +kernel

theorem single_16_8 : ∀ i ∈ List.range 4, SingleAt 16 (8+i) := by decide +kernel

theorem single_16_12 : ∀ i ∈ List.range 4, SingleAt 16 (12+i) := by decide +kernel

theorem single_16_16 : ∀ i ∈ List.range 4, SingleAt 16 (16+i) := by decide +kernel

theorem single_16_20 : ∀ i ∈ List.range 4, SingleAt 16 (20+i) := by decide +kernel

theorem single_16_24 : ∀ i ∈ List.range 4, SingleAt 16 (24+i) := by decide +kernel

theorem single_16_28 : ∀ i ∈ List.range 4, SingleAt 16 (28+i) := by decide +kernel

theorem single_16_32 : ∀ i ∈ List.range 4, SingleAt 16 (32+i) := by decide +kernel

theorem single_16_36 : ∀ i ∈ List.range 4, SingleAt 16 (36+i) := by decide +kernel

theorem single_16_40 : ∀ i ∈ List.range 4, SingleAt 16 (40+i) := by decide +kernel

theorem single_16_44 : ∀ i ∈ List.range 4, SingleAt 16 (44+i) := by decide +kernel

theorem single_16_48 : ∀ i ∈ List.range 4, SingleAt 16 (48+i) := by decide +kernel

theorem single_16_52 : ∀ i ∈ List.range 4, SingleAt 16 (52+i) := by decide +kernel

theorem single_16_56 : ∀ i ∈ List.range 4, SingleAt 16 (56+i) := by decide +kernel

theorem single_16_60 : ∀ i ∈ List.range 4, SingleAt 16 (60+i) := by decide +kernel

theorem single_16_64 : ∀ i ∈ List.range 4, SingleAt 16 (64+i) := by decide +kernel

theorem single_16_68 : ∀ i ∈ List.range 4, SingleAt 16 (68+i) := by decide +kernel

theorem single_16_72 : ∀ i ∈ List.range 4, SingleAt 16 (72+i) := by decide +kernel

theorem single_16_76 : ∀ i ∈ List.range 4, SingleAt 16 (76+i) := by decide +kernel

theorem single_16_80 : ∀ i ∈ List.range 4, SingleAt 16 (80+i) := by decide +kernel

theorem single_16_84 : ∀ i ∈ List.range 4, SingleAt 16 (84+i) := by decide +kernel

theorem single_16_88 : ∀ i ∈ List.range 4, SingleAt 16 (88+i) := by decide +kernel

theorem single_16_92 : ∀ i ∈ List.range 4, SingleAt 16 (92+i) := by decide +kernel

theorem single_16_96 : ∀ i ∈ List.range 4, SingleAt 16 (96+i) := by decide +kernel

theorem single_16_100 : ∀ i ∈ List.range 4, SingleAt 16 (100+i) := by decide +kernel

theorem single_16_104 : ∀ i ∈ List.range 4, SingleAt 16 (104+i) := by decide +kernel

theorem single_16_108 : ∀ i ∈ List.range 4, SingleAt 16 (108+i) := by decide +kernel

theorem single_16_112 : ∀ i ∈ List.range 4, SingleAt 16 (112+i) := by decide +kernel

theorem single_16_116 : ∀ i ∈ List.range 4, SingleAt 16 (116+i) := by decide +kernel

theorem single_16_120 : ∀ i ∈ List.range 4, SingleAt 16 (120+i) := by decide +kernel

theorem single_16_124 : ∀ i ∈ List.range 4, SingleAt 16 (124+i) := by decide +kernel

theorem single_16_128 : ∀ i ∈ List.range 4, SingleAt 16 (128+i) := by decide +kernel

theorem single_16_132 : ∀ i ∈ List.range 4, SingleAt 16 (132+i) := by decide +kernel

theorem single_16_136 : ∀ i ∈ List.range 4, SingleAt 16 (136+i) := by decide +kernel

theorem single_16_140 : ∀ i ∈ List.range 1, SingleAt 16 (140+i) := by decide +kernel

theorem single_16 (v : ℕ) (hv : v ∈ List.range 141) : SingleAt 16 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 16 v)
  have h := (join 0 72 69 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_16_0 single_16_4) (join 8 4 4 single_16_8 single_16_12)) (join 16 8 12 (join 16 4 4 single_16_16 single_16_20) (join 24 4 8 single_16_24 (join 28 4 4 single_16_28 single_16_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_16_36 single_16_40) (join 44 4 4 single_16_44 single_16_48)) (join 52 8 12 (join 52 4 4 single_16_52 single_16_56) (join 60 4 8 single_16_60 (join 64 4 4 single_16_64 single_16_68))))) (join 72 36 33 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_16_72 single_16_76) (join 80 4 4 single_16_80 single_16_84)) (join 88 8 12 (join 88 4 4 single_16_88 single_16_92) (join 96 4 8 single_16_96 (join 100 4 4 single_16_100 single_16_104)))) (join 108 16 17 (join 108 8 8 (join 108 4 4 single_16_108 single_16_112) (join 116 4 4 single_16_116 single_16_120)) (join 124 8 9 (join 124 4 4 single_16_124 single_16_128) (join 132 4 5 single_16_132 (join 136 4 1 single_16_136 single_16_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_16_0 : ∀ i ∈ List.range 4, PhaseAt 16 (0+i) := by decide +kernel

theorem phase_16_4 : ∀ i ∈ List.range 4, PhaseAt 16 (4+i) := by decide +kernel

theorem phase_16_8 : ∀ i ∈ List.range 4, PhaseAt 16 (8+i) := by decide +kernel

theorem phase_16_12 : ∀ i ∈ List.range 4, PhaseAt 16 (12+i) := by decide +kernel

theorem phase_16_16 : ∀ i ∈ List.range 4, PhaseAt 16 (16+i) := by decide +kernel

theorem phase_16_20 : ∀ i ∈ List.range 4, PhaseAt 16 (20+i) := by decide +kernel

theorem phase_16_24 : ∀ i ∈ List.range 4, PhaseAt 16 (24+i) := by decide +kernel

theorem phase_16_28 : ∀ i ∈ List.range 4, PhaseAt 16 (28+i) := by decide +kernel

theorem phase_16_32 : ∀ i ∈ List.range 4, PhaseAt 16 (32+i) := by decide +kernel

theorem phase_16_36 : ∀ i ∈ List.range 4, PhaseAt 16 (36+i) := by decide +kernel

theorem phase_16_40 : ∀ i ∈ List.range 4, PhaseAt 16 (40+i) := by decide +kernel

theorem phase_16_44 : ∀ i ∈ List.range 4, PhaseAt 16 (44+i) := by decide +kernel

theorem phase_16_48 : ∀ i ∈ List.range 4, PhaseAt 16 (48+i) := by decide +kernel

theorem phase_16_52 : ∀ i ∈ List.range 4, PhaseAt 16 (52+i) := by decide +kernel

theorem phase_16_56 : ∀ i ∈ List.range 4, PhaseAt 16 (56+i) := by decide +kernel

theorem phase_16_60 : ∀ i ∈ List.range 4, PhaseAt 16 (60+i) := by decide +kernel

theorem phase_16_64 : ∀ i ∈ List.range 4, PhaseAt 16 (64+i) := by decide +kernel

theorem phase_16_68 : ∀ i ∈ List.range 4, PhaseAt 16 (68+i) := by decide +kernel

theorem phase_16_72 : ∀ i ∈ List.range 4, PhaseAt 16 (72+i) := by decide +kernel

theorem phase_16_76 : ∀ i ∈ List.range 4, PhaseAt 16 (76+i) := by decide +kernel

theorem phase_16_80 : ∀ i ∈ List.range 4, PhaseAt 16 (80+i) := by decide +kernel

theorem phase_16_84 : ∀ i ∈ List.range 4, PhaseAt 16 (84+i) := by decide +kernel

theorem phase_16_88 : ∀ i ∈ List.range 4, PhaseAt 16 (88+i) := by decide +kernel

theorem phase_16_92 : ∀ i ∈ List.range 4, PhaseAt 16 (92+i) := by decide +kernel

theorem phase_16_96 : ∀ i ∈ List.range 4, PhaseAt 16 (96+i) := by decide +kernel

theorem phase_16_100 : ∀ i ∈ List.range 4, PhaseAt 16 (100+i) := by decide +kernel

theorem phase_16_104 : ∀ i ∈ List.range 4, PhaseAt 16 (104+i) := by decide +kernel

theorem phase_16_108 : ∀ i ∈ List.range 4, PhaseAt 16 (108+i) := by decide +kernel

theorem phase_16_112 : ∀ i ∈ List.range 4, PhaseAt 16 (112+i) := by decide +kernel

theorem phase_16_116 : ∀ i ∈ List.range 4, PhaseAt 16 (116+i) := by decide +kernel

theorem phase_16_120 : ∀ i ∈ List.range 4, PhaseAt 16 (120+i) := by decide +kernel

theorem phase_16_124 : ∀ i ∈ List.range 4, PhaseAt 16 (124+i) := by decide +kernel

theorem phase_16_128 : ∀ i ∈ List.range 4, PhaseAt 16 (128+i) := by decide +kernel

theorem phase_16_132 : ∀ i ∈ List.range 4, PhaseAt 16 (132+i) := by decide +kernel

theorem phase_16_136 : ∀ i ∈ List.range 4, PhaseAt 16 (136+i) := by decide +kernel

theorem phase_16_140 : ∀ i ∈ List.range 1, PhaseAt 16 (140+i) := by decide +kernel

theorem phase_16 (v : ℕ) (hv : v ∈ List.range 141) : PhaseAt 16 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 16 v)
  have h := (join 0 72 69 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_16_0 phase_16_4) (join 8 4 4 phase_16_8 phase_16_12)) (join 16 8 12 (join 16 4 4 phase_16_16 phase_16_20) (join 24 4 8 phase_16_24 (join 28 4 4 phase_16_28 phase_16_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_16_36 phase_16_40) (join 44 4 4 phase_16_44 phase_16_48)) (join 52 8 12 (join 52 4 4 phase_16_52 phase_16_56) (join 60 4 8 phase_16_60 (join 64 4 4 phase_16_64 phase_16_68))))) (join 72 36 33 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_16_72 phase_16_76) (join 80 4 4 phase_16_80 phase_16_84)) (join 88 8 12 (join 88 4 4 phase_16_88 phase_16_92) (join 96 4 8 phase_16_96 (join 100 4 4 phase_16_100 phase_16_104)))) (join 108 16 17 (join 108 8 8 (join 108 4 4 phase_16_108 phase_16_112) (join 116 4 4 phase_16_116 phase_16_120)) (join 124 8 9 (join 124 4 4 phase_16_124 phase_16_128) (join 132 4 5 phase_16_132 (join 136 4 1 phase_16_136 phase_16_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_16_0 : ∀ i ∈ List.range 1, ThresholdAt 16 (0+i) := by decide +kernel

theorem threshold_16_1 : ∀ i ∈ List.range 1, ThresholdAt 16 (1+i) := by decide +kernel

theorem threshold_16_2 : ∀ i ∈ List.range 1, ThresholdAt 16 (2+i) := by decide +kernel

theorem threshold_16_3 : ∀ i ∈ List.range 1, ThresholdAt 16 (3+i) := by decide +kernel

theorem threshold_16_4 : ∀ i ∈ List.range 1, ThresholdAt 16 (4+i) := by decide +kernel

theorem threshold_16_5 : ∀ i ∈ List.range 1, ThresholdAt 16 (5+i) := by decide +kernel

theorem threshold_16_6 : ∀ i ∈ List.range 1, ThresholdAt 16 (6+i) := by decide +kernel

theorem threshold_16_7 : ∀ i ∈ List.range 1, ThresholdAt 16 (7+i) := by decide +kernel

theorem threshold_16_8 : ∀ i ∈ List.range 1, ThresholdAt 16 (8+i) := by decide +kernel

theorem threshold_16_9 : ∀ i ∈ List.range 1, ThresholdAt 16 (9+i) := by decide +kernel

theorem threshold_16_10 : ∀ i ∈ List.range 1, ThresholdAt 16 (10+i) := by decide +kernel

theorem threshold_16_11 : ∀ i ∈ List.range 1, ThresholdAt 16 (11+i) := by decide +kernel

theorem threshold_16_12 : ∀ i ∈ List.range 1, ThresholdAt 16 (12+i) := by decide +kernel

theorem threshold_16_13 : ∀ i ∈ List.range 1, ThresholdAt 16 (13+i) := by decide +kernel

theorem threshold_16_14 : ∀ i ∈ List.range 1, ThresholdAt 16 (14+i) := by decide +kernel

theorem threshold_16_15 : ∀ i ∈ List.range 1, ThresholdAt 16 (15+i) := by decide +kernel

theorem threshold_16_16 : ∀ i ∈ List.range 1, ThresholdAt 16 (16+i) := by decide +kernel

theorem threshold_16_17 : ∀ i ∈ List.range 1, ThresholdAt 16 (17+i) := by decide +kernel

theorem threshold_16_18 : ∀ i ∈ List.range 1, ThresholdAt 16 (18+i) := by decide +kernel

theorem threshold_16_19 : ∀ i ∈ List.range 1, ThresholdAt 16 (19+i) := by decide +kernel

theorem threshold_16_20 : ∀ i ∈ List.range 1, ThresholdAt 16 (20+i) := by decide +kernel

theorem threshold_16_21 : ∀ i ∈ List.range 1, ThresholdAt 16 (21+i) := by decide +kernel

theorem threshold_16_22 : ∀ i ∈ List.range 1, ThresholdAt 16 (22+i) := by decide +kernel

theorem threshold_16_23 : ∀ i ∈ List.range 1, ThresholdAt 16 (23+i) := by decide +kernel

theorem threshold_16_24 : ∀ i ∈ List.range 1, ThresholdAt 16 (24+i) := by decide +kernel

theorem threshold_16_25 : ∀ i ∈ List.range 1, ThresholdAt 16 (25+i) := by decide +kernel

theorem threshold_16_26 : ∀ i ∈ List.range 1, ThresholdAt 16 (26+i) := by decide +kernel

theorem threshold_16_27 : ∀ i ∈ List.range 1, ThresholdAt 16 (27+i) := by decide +kernel

theorem threshold_16_28 : ∀ i ∈ List.range 1, ThresholdAt 16 (28+i) := by decide +kernel

theorem threshold_16_29 : ∀ i ∈ List.range 1, ThresholdAt 16 (29+i) := by decide +kernel

theorem threshold_16_30 : ∀ i ∈ List.range 1, ThresholdAt 16 (30+i) := by decide +kernel

theorem threshold_16_31 : ∀ i ∈ List.range 1, ThresholdAt 16 (31+i) := by decide +kernel

theorem threshold_16_32 : ∀ i ∈ List.range 1, ThresholdAt 16 (32+i) := by decide +kernel

theorem threshold_16_33 : ∀ i ∈ List.range 1, ThresholdAt 16 (33+i) := by decide +kernel

theorem threshold_16_34 : ∀ i ∈ List.range 1, ThresholdAt 16 (34+i) := by decide +kernel

theorem threshold_16_35 : ∀ i ∈ List.range 1, ThresholdAt 16 (35+i) := by decide +kernel

theorem threshold_16_36 : ∀ i ∈ List.range 1, ThresholdAt 16 (36+i) := by decide +kernel

theorem threshold_16_37 : ∀ i ∈ List.range 1, ThresholdAt 16 (37+i) := by decide +kernel

theorem threshold_16_38 : ∀ i ∈ List.range 1, ThresholdAt 16 (38+i) := by decide +kernel

theorem threshold_16_39 : ∀ i ∈ List.range 1, ThresholdAt 16 (39+i) := by decide +kernel

theorem threshold_16_40 : ∀ i ∈ List.range 1, ThresholdAt 16 (40+i) := by decide +kernel

theorem threshold_16_41 : ∀ i ∈ List.range 1, ThresholdAt 16 (41+i) := by decide +kernel

theorem threshold_16_42 : ∀ i ∈ List.range 1, ThresholdAt 16 (42+i) := by decide +kernel

theorem threshold_16_43 : ∀ i ∈ List.range 1, ThresholdAt 16 (43+i) := by decide +kernel

theorem threshold_16_44 : ∀ i ∈ List.range 1, ThresholdAt 16 (44+i) := by decide +kernel

theorem threshold_16_45 : ∀ i ∈ List.range 1, ThresholdAt 16 (45+i) := by decide +kernel

theorem threshold_16_46 : ∀ i ∈ List.range 1, ThresholdAt 16 (46+i) := by decide +kernel

theorem threshold_16_47 : ∀ i ∈ List.range 1, ThresholdAt 16 (47+i) := by decide +kernel

theorem threshold_16_48 : ∀ i ∈ List.range 1, ThresholdAt 16 (48+i) := by decide +kernel

theorem threshold_16_49 : ∀ i ∈ List.range 1, ThresholdAt 16 (49+i) := by decide +kernel

theorem threshold_16_50 : ∀ i ∈ List.range 1, ThresholdAt 16 (50+i) := by decide +kernel

theorem threshold_16_51 : ∀ i ∈ List.range 1, ThresholdAt 16 (51+i) := by decide +kernel

theorem threshold_16_52 : ∀ i ∈ List.range 1, ThresholdAt 16 (52+i) := by decide +kernel

theorem threshold_16_53 : ∀ i ∈ List.range 1, ThresholdAt 16 (53+i) := by decide +kernel

theorem threshold_16_54 : ∀ i ∈ List.range 1, ThresholdAt 16 (54+i) := by decide +kernel

theorem threshold_16_55 : ∀ i ∈ List.range 1, ThresholdAt 16 (55+i) := by decide +kernel

theorem threshold_16_56 : ∀ i ∈ List.range 1, ThresholdAt 16 (56+i) := by decide +kernel

theorem threshold_16_57 : ∀ i ∈ List.range 1, ThresholdAt 16 (57+i) := by decide +kernel

theorem threshold_16_58 : ∀ i ∈ List.range 1, ThresholdAt 16 (58+i) := by decide +kernel

theorem threshold_16_59 : ∀ i ∈ List.range 1, ThresholdAt 16 (59+i) := by decide +kernel

theorem threshold_16_60 : ∀ i ∈ List.range 1, ThresholdAt 16 (60+i) := by decide +kernel

theorem threshold_16_61 : ∀ i ∈ List.range 1, ThresholdAt 16 (61+i) := by decide +kernel

theorem threshold_16_62 : ∀ i ∈ List.range 1, ThresholdAt 16 (62+i) := by decide +kernel

theorem threshold_16_63 : ∀ i ∈ List.range 1, ThresholdAt 16 (63+i) := by decide +kernel

theorem threshold_16_64 : ∀ i ∈ List.range 1, ThresholdAt 16 (64+i) := by decide +kernel

theorem threshold_16_65 : ∀ i ∈ List.range 1, ThresholdAt 16 (65+i) := by decide +kernel

theorem threshold_16_66 : ∀ i ∈ List.range 1, ThresholdAt 16 (66+i) := by decide +kernel

theorem threshold_16_67 : ∀ i ∈ List.range 1, ThresholdAt 16 (67+i) := by decide +kernel

theorem threshold_16_68 : ∀ i ∈ List.range 1, ThresholdAt 16 (68+i) := by decide +kernel

theorem threshold_16_69 : ∀ i ∈ List.range 1, ThresholdAt 16 (69+i) := by decide +kernel

theorem threshold_16_70 : ∀ i ∈ List.range 1, ThresholdAt 16 (70+i) := by decide +kernel

theorem threshold_16_71 : ∀ i ∈ List.range 1, ThresholdAt 16 (71+i) := by decide +kernel

theorem threshold_16_72 : ∀ i ∈ List.range 1, ThresholdAt 16 (72+i) := by decide +kernel

theorem threshold_16_73 : ∀ i ∈ List.range 1, ThresholdAt 16 (73+i) := by decide +kernel

theorem threshold_16_74 : ∀ i ∈ List.range 1, ThresholdAt 16 (74+i) := by decide +kernel

theorem threshold_16_75 : ∀ i ∈ List.range 1, ThresholdAt 16 (75+i) := by decide +kernel

theorem threshold_16_76 : ∀ i ∈ List.range 1, ThresholdAt 16 (76+i) := by decide +kernel

theorem threshold_16_77 : ∀ i ∈ List.range 1, ThresholdAt 16 (77+i) := by decide +kernel

theorem threshold_16_78 : ∀ i ∈ List.range 1, ThresholdAt 16 (78+i) := by decide +kernel

theorem threshold_16_79 : ∀ i ∈ List.range 1, ThresholdAt 16 (79+i) := by decide +kernel

theorem threshold_16_80 : ∀ i ∈ List.range 1, ThresholdAt 16 (80+i) := by decide +kernel

theorem threshold_16_81 : ∀ i ∈ List.range 1, ThresholdAt 16 (81+i) := by decide +kernel

theorem threshold_16_82 : ∀ i ∈ List.range 1, ThresholdAt 16 (82+i) := by decide +kernel

theorem threshold_16_83 : ∀ i ∈ List.range 1, ThresholdAt 16 (83+i) := by decide +kernel

theorem threshold_16_84 : ∀ i ∈ List.range 1, ThresholdAt 16 (84+i) := by decide +kernel

theorem threshold_16_85 : ∀ i ∈ List.range 1, ThresholdAt 16 (85+i) := by decide +kernel

theorem threshold_16_86 : ∀ i ∈ List.range 1, ThresholdAt 16 (86+i) := by decide +kernel

theorem threshold_16_87 : ∀ i ∈ List.range 1, ThresholdAt 16 (87+i) := by decide +kernel

theorem threshold_16_88 : ∀ i ∈ List.range 1, ThresholdAt 16 (88+i) := by decide +kernel

theorem threshold_16_89 : ∀ i ∈ List.range 1, ThresholdAt 16 (89+i) := by decide +kernel

theorem threshold_16_90 : ∀ i ∈ List.range 1, ThresholdAt 16 (90+i) := by decide +kernel

theorem threshold_16_91 : ∀ i ∈ List.range 1, ThresholdAt 16 (91+i) := by decide +kernel

theorem threshold_16_92 : ∀ i ∈ List.range 1, ThresholdAt 16 (92+i) := by decide +kernel

theorem threshold_16_93 : ∀ i ∈ List.range 1, ThresholdAt 16 (93+i) := by decide +kernel

theorem threshold_16_94 : ∀ i ∈ List.range 1, ThresholdAt 16 (94+i) := by decide +kernel

theorem threshold_16_95 : ∀ i ∈ List.range 1, ThresholdAt 16 (95+i) := by decide +kernel

theorem threshold_16_96 : ∀ i ∈ List.range 1, ThresholdAt 16 (96+i) := by decide +kernel

theorem threshold_16_97 : ∀ i ∈ List.range 1, ThresholdAt 16 (97+i) := by decide +kernel

theorem threshold_16_98 : ∀ i ∈ List.range 1, ThresholdAt 16 (98+i) := by decide +kernel

theorem threshold_16_99 : ∀ i ∈ List.range 1, ThresholdAt 16 (99+i) := by decide +kernel

theorem threshold_16_100 : ∀ i ∈ List.range 1, ThresholdAt 16 (100+i) := by decide +kernel

theorem threshold_16_101 : ∀ i ∈ List.range 1, ThresholdAt 16 (101+i) := by decide +kernel

theorem threshold_16_102 : ∀ i ∈ List.range 1, ThresholdAt 16 (102+i) := by decide +kernel

theorem threshold_16_103 : ∀ i ∈ List.range 1, ThresholdAt 16 (103+i) := by decide +kernel

theorem threshold_16_104 : ∀ i ∈ List.range 1, ThresholdAt 16 (104+i) := by decide +kernel

theorem threshold_16_105 : ∀ i ∈ List.range 1, ThresholdAt 16 (105+i) := by decide +kernel

theorem threshold_16_106 : ∀ i ∈ List.range 1, ThresholdAt 16 (106+i) := by decide +kernel

theorem threshold_16_107 : ∀ i ∈ List.range 1, ThresholdAt 16 (107+i) := by decide +kernel

theorem threshold_16_108 : ∀ i ∈ List.range 1, ThresholdAt 16 (108+i) := by decide +kernel

theorem threshold_16_109 : ∀ i ∈ List.range 1, ThresholdAt 16 (109+i) := by decide +kernel

theorem threshold_16_110 : ∀ i ∈ List.range 1, ThresholdAt 16 (110+i) := by decide +kernel

theorem threshold_16_111 : ∀ i ∈ List.range 1, ThresholdAt 16 (111+i) := by decide +kernel

theorem threshold_16_112 : ∀ i ∈ List.range 1, ThresholdAt 16 (112+i) := by decide +kernel

theorem threshold_16_113 : ∀ i ∈ List.range 1, ThresholdAt 16 (113+i) := by decide +kernel

theorem threshold_16_114 : ∀ i ∈ List.range 1, ThresholdAt 16 (114+i) := by decide +kernel

theorem threshold_16_115 : ∀ i ∈ List.range 1, ThresholdAt 16 (115+i) := by decide +kernel

theorem threshold_16_116 : ∀ i ∈ List.range 1, ThresholdAt 16 (116+i) := by decide +kernel

theorem threshold_16_117 : ∀ i ∈ List.range 1, ThresholdAt 16 (117+i) := by decide +kernel

theorem threshold_16_118 : ∀ i ∈ List.range 1, ThresholdAt 16 (118+i) := by decide +kernel

theorem threshold_16_119 : ∀ i ∈ List.range 1, ThresholdAt 16 (119+i) := by decide +kernel

theorem threshold_16_120 : ∀ i ∈ List.range 1, ThresholdAt 16 (120+i) := by decide +kernel

theorem threshold_16_121 : ∀ i ∈ List.range 1, ThresholdAt 16 (121+i) := by decide +kernel

theorem threshold_16_122 : ∀ i ∈ List.range 1, ThresholdAt 16 (122+i) := by decide +kernel

theorem threshold_16_123 : ∀ i ∈ List.range 1, ThresholdAt 16 (123+i) := by decide +kernel

theorem threshold_16_124 : ∀ i ∈ List.range 1, ThresholdAt 16 (124+i) := by decide +kernel

theorem threshold_16_125 : ∀ i ∈ List.range 1, ThresholdAt 16 (125+i) := by decide +kernel

theorem threshold_16_126 : ∀ i ∈ List.range 1, ThresholdAt 16 (126+i) := by decide +kernel

theorem threshold_16_127 : ∀ i ∈ List.range 1, ThresholdAt 16 (127+i) := by decide +kernel

theorem threshold_16_128 : ∀ i ∈ List.range 1, ThresholdAt 16 (128+i) := by decide +kernel

theorem threshold_16_129 : ∀ i ∈ List.range 1, ThresholdAt 16 (129+i) := by decide +kernel

theorem threshold_16_130 : ∀ i ∈ List.range 1, ThresholdAt 16 (130+i) := by decide +kernel

theorem threshold_16_131 : ∀ i ∈ List.range 1, ThresholdAt 16 (131+i) := by decide +kernel

theorem threshold_16_132 : ∀ i ∈ List.range 1, ThresholdAt 16 (132+i) := by decide +kernel

theorem threshold_16_133 : ∀ i ∈ List.range 1, ThresholdAt 16 (133+i) := by decide +kernel

theorem threshold_16_134 : ∀ i ∈ List.range 1, ThresholdAt 16 (134+i) := by decide +kernel

theorem threshold_16_135 : ∀ i ∈ List.range 1, ThresholdAt 16 (135+i) := by decide +kernel

theorem threshold_16_136 : ∀ i ∈ List.range 1, ThresholdAt 16 (136+i) := by decide +kernel

theorem threshold_16_137 : ∀ i ∈ List.range 1, ThresholdAt 16 (137+i) := by decide +kernel

theorem threshold_16_138 : ∀ i ∈ List.range 1, ThresholdAt 16 (138+i) := by decide +kernel

theorem threshold_16_139 : ∀ i ∈ List.range 1, ThresholdAt 16 (139+i) := by decide +kernel

theorem threshold_16_140 : ∀ i ∈ List.range 1, ThresholdAt 16 (140+i) := by decide +kernel

theorem threshold_16 (v : ℕ) (hv : v ∈ List.range 141) : ThresholdAt 16 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 16 v)
  have h := (join 0 70 71 (join 0 35 35 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_16_0 threshold_16_1) (join 2 1 1 threshold_16_2 threshold_16_3)) (join 4 2 2 (join 4 1 1 threshold_16_4 threshold_16_5) (join 6 1 1 threshold_16_6 threshold_16_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_16_8 threshold_16_9) (join 10 1 1 threshold_16_10 threshold_16_11)) (join 12 2 3 (join 12 1 1 threshold_16_12 threshold_16_13) (join 14 1 2 threshold_16_14 (join 15 1 1 threshold_16_15 threshold_16_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 threshold_16_17 threshold_16_18) (join 19 1 1 threshold_16_19 threshold_16_20)) (join 21 2 3 (join 21 1 1 threshold_16_21 threshold_16_22) (join 23 1 2 threshold_16_23 (join 24 1 1 threshold_16_24 threshold_16_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 threshold_16_26 threshold_16_27) (join 28 1 1 threshold_16_28 threshold_16_29)) (join 30 2 3 (join 30 1 1 threshold_16_30 threshold_16_31) (join 32 1 2 threshold_16_32 (join 33 1 1 threshold_16_33 threshold_16_34)))))) (join 35 17 18 (join 35 8 9 (join 35 4 4 (join 35 2 2 (join 35 1 1 threshold_16_35 threshold_16_36) (join 37 1 1 threshold_16_37 threshold_16_38)) (join 39 2 2 (join 39 1 1 threshold_16_39 threshold_16_40) (join 41 1 1 threshold_16_41 threshold_16_42))) (join 43 4 5 (join 43 2 2 (join 43 1 1 threshold_16_43 threshold_16_44) (join 45 1 1 threshold_16_45 threshold_16_46)) (join 47 2 3 (join 47 1 1 threshold_16_47 threshold_16_48) (join 49 1 2 threshold_16_49 (join 50 1 1 threshold_16_50 threshold_16_51))))) (join 52 9 9 (join 52 4 5 (join 52 2 2 (join 52 1 1 threshold_16_52 threshold_16_53) (join 54 1 1 threshold_16_54 threshold_16_55)) (join 56 2 3 (join 56 1 1 threshold_16_56 threshold_16_57) (join 58 1 2 threshold_16_58 (join 59 1 1 threshold_16_59 threshold_16_60)))) (join 61 4 5 (join 61 2 2 (join 61 1 1 threshold_16_61 threshold_16_62) (join 63 1 1 threshold_16_63 threshold_16_64)) (join 65 2 3 (join 65 1 1 threshold_16_65 threshold_16_66) (join 67 1 2 threshold_16_67 (join 68 1 1 threshold_16_68 threshold_16_69))))))) (join 70 35 36 (join 70 17 18 (join 70 8 9 (join 70 4 4 (join 70 2 2 (join 70 1 1 threshold_16_70 threshold_16_71) (join 72 1 1 threshold_16_72 threshold_16_73)) (join 74 2 2 (join 74 1 1 threshold_16_74 threshold_16_75) (join 76 1 1 threshold_16_76 threshold_16_77))) (join 78 4 5 (join 78 2 2 (join 78 1 1 threshold_16_78 threshold_16_79) (join 80 1 1 threshold_16_80 threshold_16_81)) (join 82 2 3 (join 82 1 1 threshold_16_82 threshold_16_83) (join 84 1 2 threshold_16_84 (join 85 1 1 threshold_16_85 threshold_16_86))))) (join 87 9 9 (join 87 4 5 (join 87 2 2 (join 87 1 1 threshold_16_87 threshold_16_88) (join 89 1 1 threshold_16_89 threshold_16_90)) (join 91 2 3 (join 91 1 1 threshold_16_91 threshold_16_92) (join 93 1 2 threshold_16_93 (join 94 1 1 threshold_16_94 threshold_16_95)))) (join 96 4 5 (join 96 2 2 (join 96 1 1 threshold_16_96 threshold_16_97) (join 98 1 1 threshold_16_98 threshold_16_99)) (join 100 2 3 (join 100 1 1 threshold_16_100 threshold_16_101) (join 102 1 2 threshold_16_102 (join 103 1 1 threshold_16_103 threshold_16_104)))))) (join 105 18 18 (join 105 9 9 (join 105 4 5 (join 105 2 2 (join 105 1 1 threshold_16_105 threshold_16_106) (join 107 1 1 threshold_16_107 threshold_16_108)) (join 109 2 3 (join 109 1 1 threshold_16_109 threshold_16_110) (join 111 1 2 threshold_16_111 (join 112 1 1 threshold_16_112 threshold_16_113)))) (join 114 4 5 (join 114 2 2 (join 114 1 1 threshold_16_114 threshold_16_115) (join 116 1 1 threshold_16_116 threshold_16_117)) (join 118 2 3 (join 118 1 1 threshold_16_118 threshold_16_119) (join 120 1 2 threshold_16_120 (join 121 1 1 threshold_16_121 threshold_16_122))))) (join 123 9 9 (join 123 4 5 (join 123 2 2 (join 123 1 1 threshold_16_123 threshold_16_124) (join 125 1 1 threshold_16_125 threshold_16_126)) (join 127 2 3 (join 127 1 1 threshold_16_127 threshold_16_128) (join 129 1 2 threshold_16_129 (join 130 1 1 threshold_16_130 threshold_16_131)))) (join 132 4 5 (join 132 2 2 (join 132 1 1 threshold_16_132 threshold_16_133) (join 134 1 1 threshold_16_134 threshold_16_135)) (join 136 2 3 (join 136 1 1 threshold_16_136 threshold_16_137) (join 138 1 2 threshold_16_138 (join 139 1 1 threshold_16_139 threshold_16_140))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_16_0 : ∀ i ∈ List.range 4, LedgerAt 16 (0+i) := by decide +kernel

theorem ledger_16_4 : ∀ i ∈ List.range 4, LedgerAt 16 (4+i) := by decide +kernel

theorem ledger_16_8 : ∀ i ∈ List.range 4, LedgerAt 16 (8+i) := by decide +kernel

theorem ledger_16_12 : ∀ i ∈ List.range 4, LedgerAt 16 (12+i) := by decide +kernel

theorem ledger_16_16 : ∀ i ∈ List.range 4, LedgerAt 16 (16+i) := by decide +kernel

theorem ledger_16_20 : ∀ i ∈ List.range 4, LedgerAt 16 (20+i) := by decide +kernel

theorem ledger_16_24 : ∀ i ∈ List.range 4, LedgerAt 16 (24+i) := by decide +kernel

theorem ledger_16_28 : ∀ i ∈ List.range 4, LedgerAt 16 (28+i) := by decide +kernel

theorem ledger_16_32 : ∀ i ∈ List.range 4, LedgerAt 16 (32+i) := by decide +kernel

theorem ledger_16_36 : ∀ i ∈ List.range 4, LedgerAt 16 (36+i) := by decide +kernel

theorem ledger_16_40 : ∀ i ∈ List.range 4, LedgerAt 16 (40+i) := by decide +kernel

theorem ledger_16_44 : ∀ i ∈ List.range 4, LedgerAt 16 (44+i) := by decide +kernel

theorem ledger_16_48 : ∀ i ∈ List.range 4, LedgerAt 16 (48+i) := by decide +kernel

theorem ledger_16_52 : ∀ i ∈ List.range 4, LedgerAt 16 (52+i) := by decide +kernel

theorem ledger_16_56 : ∀ i ∈ List.range 4, LedgerAt 16 (56+i) := by decide +kernel

theorem ledger_16_60 : ∀ i ∈ List.range 4, LedgerAt 16 (60+i) := by decide +kernel

theorem ledger_16_64 : ∀ i ∈ List.range 4, LedgerAt 16 (64+i) := by decide +kernel

theorem ledger_16_68 : ∀ i ∈ List.range 4, LedgerAt 16 (68+i) := by decide +kernel

theorem ledger_16_72 : ∀ i ∈ List.range 4, LedgerAt 16 (72+i) := by decide +kernel

theorem ledger_16_76 : ∀ i ∈ List.range 4, LedgerAt 16 (76+i) := by decide +kernel

theorem ledger_16_80 : ∀ i ∈ List.range 4, LedgerAt 16 (80+i) := by decide +kernel

theorem ledger_16_84 : ∀ i ∈ List.range 4, LedgerAt 16 (84+i) := by decide +kernel

theorem ledger_16_88 : ∀ i ∈ List.range 4, LedgerAt 16 (88+i) := by decide +kernel

theorem ledger_16_92 : ∀ i ∈ List.range 4, LedgerAt 16 (92+i) := by decide +kernel

theorem ledger_16_96 : ∀ i ∈ List.range 4, LedgerAt 16 (96+i) := by decide +kernel

theorem ledger_16_100 : ∀ i ∈ List.range 4, LedgerAt 16 (100+i) := by decide +kernel

theorem ledger_16_104 : ∀ i ∈ List.range 4, LedgerAt 16 (104+i) := by decide +kernel

theorem ledger_16_108 : ∀ i ∈ List.range 4, LedgerAt 16 (108+i) := by decide +kernel

theorem ledger_16_112 : ∀ i ∈ List.range 4, LedgerAt 16 (112+i) := by decide +kernel

theorem ledger_16_116 : ∀ i ∈ List.range 4, LedgerAt 16 (116+i) := by decide +kernel

theorem ledger_16_120 : ∀ i ∈ List.range 4, LedgerAt 16 (120+i) := by decide +kernel

theorem ledger_16_124 : ∀ i ∈ List.range 4, LedgerAt 16 (124+i) := by decide +kernel

theorem ledger_16_128 : ∀ i ∈ List.range 4, LedgerAt 16 (128+i) := by decide +kernel

theorem ledger_16_132 : ∀ i ∈ List.range 4, LedgerAt 16 (132+i) := by decide +kernel

theorem ledger_16_136 : ∀ i ∈ List.range 4, LedgerAt 16 (136+i) := by decide +kernel

theorem ledger_16_140 : ∀ i ∈ List.range 1, LedgerAt 16 (140+i) := by decide +kernel

theorem ledger_16 (v : ℕ) (hv : v ∈ List.range 141) : LedgerAt 16 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 16 v)
  have h := (join 0 72 69 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_16_0 ledger_16_4) (join 8 4 4 ledger_16_8 ledger_16_12)) (join 16 8 12 (join 16 4 4 ledger_16_16 ledger_16_20) (join 24 4 8 ledger_16_24 (join 28 4 4 ledger_16_28 ledger_16_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_16_36 ledger_16_40) (join 44 4 4 ledger_16_44 ledger_16_48)) (join 52 8 12 (join 52 4 4 ledger_16_52 ledger_16_56) (join 60 4 8 ledger_16_60 (join 64 4 4 ledger_16_64 ledger_16_68))))) (join 72 36 33 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_16_72 ledger_16_76) (join 80 4 4 ledger_16_80 ledger_16_84)) (join 88 8 12 (join 88 4 4 ledger_16_88 ledger_16_92) (join 96 4 8 ledger_16_96 (join 100 4 4 ledger_16_100 ledger_16_104)))) (join 108 16 17 (join 108 8 8 (join 108 4 4 ledger_16_108 ledger_16_112) (join 116 4 4 ledger_16_116 ledger_16_120)) (join 124 8 9 (join 124 4 4 ledger_16_124 ledger_16_128) (join 132 4 5 ledger_16_132 (join 136 4 1 ledger_16_136 ledger_16_140))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
