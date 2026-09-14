import ProximityPrize.SubmissionLower.HigherAffineCheckedR146810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_15_0 : ∀ i ∈ List.range 4, SingleAt 15 (0+i) := by decide +kernel

theorem single_15_4 : ∀ i ∈ List.range 4, SingleAt 15 (4+i) := by decide +kernel

theorem single_15_8 : ∀ i ∈ List.range 4, SingleAt 15 (8+i) := by decide +kernel

theorem single_15_12 : ∀ i ∈ List.range 4, SingleAt 15 (12+i) := by decide +kernel

theorem single_15_16 : ∀ i ∈ List.range 4, SingleAt 15 (16+i) := by decide +kernel

theorem single_15_20 : ∀ i ∈ List.range 4, SingleAt 15 (20+i) := by decide +kernel

theorem single_15_24 : ∀ i ∈ List.range 4, SingleAt 15 (24+i) := by decide +kernel

theorem single_15_28 : ∀ i ∈ List.range 4, SingleAt 15 (28+i) := by decide +kernel

theorem single_15_32 : ∀ i ∈ List.range 4, SingleAt 15 (32+i) := by decide +kernel

theorem single_15_36 : ∀ i ∈ List.range 4, SingleAt 15 (36+i) := by decide +kernel

theorem single_15_40 : ∀ i ∈ List.range 4, SingleAt 15 (40+i) := by decide +kernel

theorem single_15_44 : ∀ i ∈ List.range 4, SingleAt 15 (44+i) := by decide +kernel

theorem single_15_48 : ∀ i ∈ List.range 4, SingleAt 15 (48+i) := by decide +kernel

theorem single_15_52 : ∀ i ∈ List.range 4, SingleAt 15 (52+i) := by decide +kernel

theorem single_15_56 : ∀ i ∈ List.range 4, SingleAt 15 (56+i) := by decide +kernel

theorem single_15_60 : ∀ i ∈ List.range 4, SingleAt 15 (60+i) := by decide +kernel

theorem single_15_64 : ∀ i ∈ List.range 4, SingleAt 15 (64+i) := by decide +kernel

theorem single_15_68 : ∀ i ∈ List.range 4, SingleAt 15 (68+i) := by decide +kernel

theorem single_15_72 : ∀ i ∈ List.range 4, SingleAt 15 (72+i) := by decide +kernel

theorem single_15_76 : ∀ i ∈ List.range 4, SingleAt 15 (76+i) := by decide +kernel

theorem single_15_80 : ∀ i ∈ List.range 4, SingleAt 15 (80+i) := by decide +kernel

theorem single_15_84 : ∀ i ∈ List.range 4, SingleAt 15 (84+i) := by decide +kernel

theorem single_15_88 : ∀ i ∈ List.range 4, SingleAt 15 (88+i) := by decide +kernel

theorem single_15_92 : ∀ i ∈ List.range 4, SingleAt 15 (92+i) := by decide +kernel

theorem single_15_96 : ∀ i ∈ List.range 4, SingleAt 15 (96+i) := by decide +kernel

theorem single_15_100 : ∀ i ∈ List.range 4, SingleAt 15 (100+i) := by decide +kernel

theorem single_15_104 : ∀ i ∈ List.range 4, SingleAt 15 (104+i) := by decide +kernel

theorem single_15_108 : ∀ i ∈ List.range 4, SingleAt 15 (108+i) := by decide +kernel

theorem single_15_112 : ∀ i ∈ List.range 4, SingleAt 15 (112+i) := by decide +kernel

theorem single_15_116 : ∀ i ∈ List.range 4, SingleAt 15 (116+i) := by decide +kernel

theorem single_15_120 : ∀ i ∈ List.range 4, SingleAt 15 (120+i) := by decide +kernel

theorem single_15_124 : ∀ i ∈ List.range 4, SingleAt 15 (124+i) := by decide +kernel

theorem single_15_128 : ∀ i ∈ List.range 4, SingleAt 15 (128+i) := by decide +kernel

theorem single_15_132 : ∀ i ∈ List.range 4, SingleAt 15 (132+i) := by decide +kernel

theorem single_15_136 : ∀ i ∈ List.range 4, SingleAt 15 (136+i) := by decide +kernel

theorem single_15_140 : ∀ i ∈ List.range 2, SingleAt 15 (140+i) := by decide +kernel

theorem single_15 (v : ℕ) (hv : v ∈ List.range 142) : SingleAt 15 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 15 v)
  have h := (join 0 72 70 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_15_0 single_15_4) (join 8 4 4 single_15_8 single_15_12)) (join 16 8 12 (join 16 4 4 single_15_16 single_15_20) (join 24 4 8 single_15_24 (join 28 4 4 single_15_28 single_15_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_15_36 single_15_40) (join 44 4 4 single_15_44 single_15_48)) (join 52 8 12 (join 52 4 4 single_15_52 single_15_56) (join 60 4 8 single_15_60 (join 64 4 4 single_15_64 single_15_68))))) (join 72 36 34 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_15_72 single_15_76) (join 80 4 4 single_15_80 single_15_84)) (join 88 8 12 (join 88 4 4 single_15_88 single_15_92) (join 96 4 8 single_15_96 (join 100 4 4 single_15_100 single_15_104)))) (join 108 16 18 (join 108 8 8 (join 108 4 4 single_15_108 single_15_112) (join 116 4 4 single_15_116 single_15_120)) (join 124 8 10 (join 124 4 4 single_15_124 single_15_128) (join 132 4 6 single_15_132 (join 136 4 2 single_15_136 single_15_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_15_0 : ∀ i ∈ List.range 4, PhaseAt 15 (0+i) := by decide +kernel

theorem phase_15_4 : ∀ i ∈ List.range 4, PhaseAt 15 (4+i) := by decide +kernel

theorem phase_15_8 : ∀ i ∈ List.range 4, PhaseAt 15 (8+i) := by decide +kernel

theorem phase_15_12 : ∀ i ∈ List.range 4, PhaseAt 15 (12+i) := by decide +kernel

theorem phase_15_16 : ∀ i ∈ List.range 4, PhaseAt 15 (16+i) := by decide +kernel

theorem phase_15_20 : ∀ i ∈ List.range 4, PhaseAt 15 (20+i) := by decide +kernel

theorem phase_15_24 : ∀ i ∈ List.range 4, PhaseAt 15 (24+i) := by decide +kernel

theorem phase_15_28 : ∀ i ∈ List.range 4, PhaseAt 15 (28+i) := by decide +kernel

theorem phase_15_32 : ∀ i ∈ List.range 4, PhaseAt 15 (32+i) := by decide +kernel

theorem phase_15_36 : ∀ i ∈ List.range 4, PhaseAt 15 (36+i) := by decide +kernel

theorem phase_15_40 : ∀ i ∈ List.range 4, PhaseAt 15 (40+i) := by decide +kernel

theorem phase_15_44 : ∀ i ∈ List.range 4, PhaseAt 15 (44+i) := by decide +kernel

theorem phase_15_48 : ∀ i ∈ List.range 4, PhaseAt 15 (48+i) := by decide +kernel

theorem phase_15_52 : ∀ i ∈ List.range 4, PhaseAt 15 (52+i) := by decide +kernel

theorem phase_15_56 : ∀ i ∈ List.range 4, PhaseAt 15 (56+i) := by decide +kernel

theorem phase_15_60 : ∀ i ∈ List.range 4, PhaseAt 15 (60+i) := by decide +kernel

theorem phase_15_64 : ∀ i ∈ List.range 4, PhaseAt 15 (64+i) := by decide +kernel

theorem phase_15_68 : ∀ i ∈ List.range 4, PhaseAt 15 (68+i) := by decide +kernel

theorem phase_15_72 : ∀ i ∈ List.range 4, PhaseAt 15 (72+i) := by decide +kernel

theorem phase_15_76 : ∀ i ∈ List.range 4, PhaseAt 15 (76+i) := by decide +kernel

theorem phase_15_80 : ∀ i ∈ List.range 4, PhaseAt 15 (80+i) := by decide +kernel

theorem phase_15_84 : ∀ i ∈ List.range 4, PhaseAt 15 (84+i) := by decide +kernel

theorem phase_15_88 : ∀ i ∈ List.range 4, PhaseAt 15 (88+i) := by decide +kernel

theorem phase_15_92 : ∀ i ∈ List.range 4, PhaseAt 15 (92+i) := by decide +kernel

theorem phase_15_96 : ∀ i ∈ List.range 4, PhaseAt 15 (96+i) := by decide +kernel

theorem phase_15_100 : ∀ i ∈ List.range 4, PhaseAt 15 (100+i) := by decide +kernel

theorem phase_15_104 : ∀ i ∈ List.range 4, PhaseAt 15 (104+i) := by decide +kernel

theorem phase_15_108 : ∀ i ∈ List.range 4, PhaseAt 15 (108+i) := by decide +kernel

theorem phase_15_112 : ∀ i ∈ List.range 4, PhaseAt 15 (112+i) := by decide +kernel

theorem phase_15_116 : ∀ i ∈ List.range 4, PhaseAt 15 (116+i) := by decide +kernel

theorem phase_15_120 : ∀ i ∈ List.range 4, PhaseAt 15 (120+i) := by decide +kernel

theorem phase_15_124 : ∀ i ∈ List.range 4, PhaseAt 15 (124+i) := by decide +kernel

theorem phase_15_128 : ∀ i ∈ List.range 4, PhaseAt 15 (128+i) := by decide +kernel

theorem phase_15_132 : ∀ i ∈ List.range 4, PhaseAt 15 (132+i) := by decide +kernel

theorem phase_15_136 : ∀ i ∈ List.range 4, PhaseAt 15 (136+i) := by decide +kernel

theorem phase_15_140 : ∀ i ∈ List.range 2, PhaseAt 15 (140+i) := by decide +kernel

theorem phase_15 (v : ℕ) (hv : v ∈ List.range 142) : PhaseAt 15 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 15 v)
  have h := (join 0 72 70 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_15_0 phase_15_4) (join 8 4 4 phase_15_8 phase_15_12)) (join 16 8 12 (join 16 4 4 phase_15_16 phase_15_20) (join 24 4 8 phase_15_24 (join 28 4 4 phase_15_28 phase_15_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_15_36 phase_15_40) (join 44 4 4 phase_15_44 phase_15_48)) (join 52 8 12 (join 52 4 4 phase_15_52 phase_15_56) (join 60 4 8 phase_15_60 (join 64 4 4 phase_15_64 phase_15_68))))) (join 72 36 34 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_15_72 phase_15_76) (join 80 4 4 phase_15_80 phase_15_84)) (join 88 8 12 (join 88 4 4 phase_15_88 phase_15_92) (join 96 4 8 phase_15_96 (join 100 4 4 phase_15_100 phase_15_104)))) (join 108 16 18 (join 108 8 8 (join 108 4 4 phase_15_108 phase_15_112) (join 116 4 4 phase_15_116 phase_15_120)) (join 124 8 10 (join 124 4 4 phase_15_124 phase_15_128) (join 132 4 6 phase_15_132 (join 136 4 2 phase_15_136 phase_15_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_15_0 : ∀ i ∈ List.range 1, ThresholdAt 15 (0+i) := by decide +kernel

theorem threshold_15_1 : ∀ i ∈ List.range 1, ThresholdAt 15 (1+i) := by decide +kernel

theorem threshold_15_2 : ∀ i ∈ List.range 1, ThresholdAt 15 (2+i) := by decide +kernel

theorem threshold_15_3 : ∀ i ∈ List.range 1, ThresholdAt 15 (3+i) := by decide +kernel

theorem threshold_15_4 : ∀ i ∈ List.range 1, ThresholdAt 15 (4+i) := by decide +kernel

theorem threshold_15_5 : ∀ i ∈ List.range 1, ThresholdAt 15 (5+i) := by decide +kernel

theorem threshold_15_6 : ∀ i ∈ List.range 1, ThresholdAt 15 (6+i) := by decide +kernel

theorem threshold_15_7 : ∀ i ∈ List.range 1, ThresholdAt 15 (7+i) := by decide +kernel

theorem threshold_15_8 : ∀ i ∈ List.range 1, ThresholdAt 15 (8+i) := by decide +kernel

theorem threshold_15_9 : ∀ i ∈ List.range 1, ThresholdAt 15 (9+i) := by decide +kernel

theorem threshold_15_10 : ∀ i ∈ List.range 1, ThresholdAt 15 (10+i) := by decide +kernel

theorem threshold_15_11 : ∀ i ∈ List.range 1, ThresholdAt 15 (11+i) := by decide +kernel

theorem threshold_15_12 : ∀ i ∈ List.range 1, ThresholdAt 15 (12+i) := by decide +kernel

theorem threshold_15_13 : ∀ i ∈ List.range 1, ThresholdAt 15 (13+i) := by decide +kernel

theorem threshold_15_14 : ∀ i ∈ List.range 1, ThresholdAt 15 (14+i) := by decide +kernel

theorem threshold_15_15 : ∀ i ∈ List.range 1, ThresholdAt 15 (15+i) := by decide +kernel

theorem threshold_15_16 : ∀ i ∈ List.range 1, ThresholdAt 15 (16+i) := by decide +kernel

theorem threshold_15_17 : ∀ i ∈ List.range 1, ThresholdAt 15 (17+i) := by decide +kernel

theorem threshold_15_18 : ∀ i ∈ List.range 1, ThresholdAt 15 (18+i) := by decide +kernel

theorem threshold_15_19 : ∀ i ∈ List.range 1, ThresholdAt 15 (19+i) := by decide +kernel

theorem threshold_15_20 : ∀ i ∈ List.range 1, ThresholdAt 15 (20+i) := by decide +kernel

theorem threshold_15_21 : ∀ i ∈ List.range 1, ThresholdAt 15 (21+i) := by decide +kernel

theorem threshold_15_22 : ∀ i ∈ List.range 1, ThresholdAt 15 (22+i) := by decide +kernel

theorem threshold_15_23 : ∀ i ∈ List.range 1, ThresholdAt 15 (23+i) := by decide +kernel

theorem threshold_15_24 : ∀ i ∈ List.range 1, ThresholdAt 15 (24+i) := by decide +kernel

theorem threshold_15_25 : ∀ i ∈ List.range 1, ThresholdAt 15 (25+i) := by decide +kernel

theorem threshold_15_26 : ∀ i ∈ List.range 1, ThresholdAt 15 (26+i) := by decide +kernel

theorem threshold_15_27 : ∀ i ∈ List.range 1, ThresholdAt 15 (27+i) := by decide +kernel

theorem threshold_15_28 : ∀ i ∈ List.range 1, ThresholdAt 15 (28+i) := by decide +kernel

theorem threshold_15_29 : ∀ i ∈ List.range 1, ThresholdAt 15 (29+i) := by decide +kernel

theorem threshold_15_30 : ∀ i ∈ List.range 1, ThresholdAt 15 (30+i) := by decide +kernel

theorem threshold_15_31 : ∀ i ∈ List.range 1, ThresholdAt 15 (31+i) := by decide +kernel

theorem threshold_15_32 : ∀ i ∈ List.range 1, ThresholdAt 15 (32+i) := by decide +kernel

theorem threshold_15_33 : ∀ i ∈ List.range 1, ThresholdAt 15 (33+i) := by decide +kernel

theorem threshold_15_34 : ∀ i ∈ List.range 1, ThresholdAt 15 (34+i) := by decide +kernel

theorem threshold_15_35 : ∀ i ∈ List.range 1, ThresholdAt 15 (35+i) := by decide +kernel

theorem threshold_15_36 : ∀ i ∈ List.range 1, ThresholdAt 15 (36+i) := by decide +kernel

theorem threshold_15_37 : ∀ i ∈ List.range 1, ThresholdAt 15 (37+i) := by decide +kernel

theorem threshold_15_38 : ∀ i ∈ List.range 1, ThresholdAt 15 (38+i) := by decide +kernel

theorem threshold_15_39 : ∀ i ∈ List.range 1, ThresholdAt 15 (39+i) := by decide +kernel

theorem threshold_15_40 : ∀ i ∈ List.range 1, ThresholdAt 15 (40+i) := by decide +kernel

theorem threshold_15_41 : ∀ i ∈ List.range 1, ThresholdAt 15 (41+i) := by decide +kernel

theorem threshold_15_42 : ∀ i ∈ List.range 1, ThresholdAt 15 (42+i) := by decide +kernel

theorem threshold_15_43 : ∀ i ∈ List.range 1, ThresholdAt 15 (43+i) := by decide +kernel

theorem threshold_15_44 : ∀ i ∈ List.range 1, ThresholdAt 15 (44+i) := by decide +kernel

theorem threshold_15_45 : ∀ i ∈ List.range 1, ThresholdAt 15 (45+i) := by decide +kernel

theorem threshold_15_46 : ∀ i ∈ List.range 1, ThresholdAt 15 (46+i) := by decide +kernel

theorem threshold_15_47 : ∀ i ∈ List.range 1, ThresholdAt 15 (47+i) := by decide +kernel

theorem threshold_15_48 : ∀ i ∈ List.range 1, ThresholdAt 15 (48+i) := by decide +kernel

theorem threshold_15_49 : ∀ i ∈ List.range 1, ThresholdAt 15 (49+i) := by decide +kernel

theorem threshold_15_50 : ∀ i ∈ List.range 1, ThresholdAt 15 (50+i) := by decide +kernel

theorem threshold_15_51 : ∀ i ∈ List.range 1, ThresholdAt 15 (51+i) := by decide +kernel

theorem threshold_15_52 : ∀ i ∈ List.range 1, ThresholdAt 15 (52+i) := by decide +kernel

theorem threshold_15_53 : ∀ i ∈ List.range 1, ThresholdAt 15 (53+i) := by decide +kernel

theorem threshold_15_54 : ∀ i ∈ List.range 1, ThresholdAt 15 (54+i) := by decide +kernel

theorem threshold_15_55 : ∀ i ∈ List.range 1, ThresholdAt 15 (55+i) := by decide +kernel

theorem threshold_15_56 : ∀ i ∈ List.range 1, ThresholdAt 15 (56+i) := by decide +kernel

theorem threshold_15_57 : ∀ i ∈ List.range 1, ThresholdAt 15 (57+i) := by decide +kernel

theorem threshold_15_58 : ∀ i ∈ List.range 1, ThresholdAt 15 (58+i) := by decide +kernel

theorem threshold_15_59 : ∀ i ∈ List.range 1, ThresholdAt 15 (59+i) := by decide +kernel

theorem threshold_15_60 : ∀ i ∈ List.range 1, ThresholdAt 15 (60+i) := by decide +kernel

theorem threshold_15_61 : ∀ i ∈ List.range 1, ThresholdAt 15 (61+i) := by decide +kernel

theorem threshold_15_62 : ∀ i ∈ List.range 1, ThresholdAt 15 (62+i) := by decide +kernel

theorem threshold_15_63 : ∀ i ∈ List.range 1, ThresholdAt 15 (63+i) := by decide +kernel

theorem threshold_15_64 : ∀ i ∈ List.range 1, ThresholdAt 15 (64+i) := by decide +kernel

theorem threshold_15_65 : ∀ i ∈ List.range 1, ThresholdAt 15 (65+i) := by decide +kernel

theorem threshold_15_66 : ∀ i ∈ List.range 1, ThresholdAt 15 (66+i) := by decide +kernel

theorem threshold_15_67 : ∀ i ∈ List.range 1, ThresholdAt 15 (67+i) := by decide +kernel

theorem threshold_15_68 : ∀ i ∈ List.range 1, ThresholdAt 15 (68+i) := by decide +kernel

theorem threshold_15_69 : ∀ i ∈ List.range 1, ThresholdAt 15 (69+i) := by decide +kernel

theorem threshold_15_70 : ∀ i ∈ List.range 1, ThresholdAt 15 (70+i) := by decide +kernel

theorem threshold_15_71 : ∀ i ∈ List.range 1, ThresholdAt 15 (71+i) := by decide +kernel

theorem threshold_15_72 : ∀ i ∈ List.range 1, ThresholdAt 15 (72+i) := by decide +kernel

theorem threshold_15_73 : ∀ i ∈ List.range 1, ThresholdAt 15 (73+i) := by decide +kernel

theorem threshold_15_74 : ∀ i ∈ List.range 1, ThresholdAt 15 (74+i) := by decide +kernel

theorem threshold_15_75 : ∀ i ∈ List.range 1, ThresholdAt 15 (75+i) := by decide +kernel

theorem threshold_15_76 : ∀ i ∈ List.range 1, ThresholdAt 15 (76+i) := by decide +kernel

theorem threshold_15_77 : ∀ i ∈ List.range 1, ThresholdAt 15 (77+i) := by decide +kernel

theorem threshold_15_78 : ∀ i ∈ List.range 1, ThresholdAt 15 (78+i) := by decide +kernel

theorem threshold_15_79 : ∀ i ∈ List.range 1, ThresholdAt 15 (79+i) := by decide +kernel

theorem threshold_15_80 : ∀ i ∈ List.range 1, ThresholdAt 15 (80+i) := by decide +kernel

theorem threshold_15_81 : ∀ i ∈ List.range 1, ThresholdAt 15 (81+i) := by decide +kernel

theorem threshold_15_82 : ∀ i ∈ List.range 1, ThresholdAt 15 (82+i) := by decide +kernel

theorem threshold_15_83 : ∀ i ∈ List.range 1, ThresholdAt 15 (83+i) := by decide +kernel

theorem threshold_15_84 : ∀ i ∈ List.range 1, ThresholdAt 15 (84+i) := by decide +kernel

theorem threshold_15_85 : ∀ i ∈ List.range 1, ThresholdAt 15 (85+i) := by decide +kernel

theorem threshold_15_86 : ∀ i ∈ List.range 1, ThresholdAt 15 (86+i) := by decide +kernel

theorem threshold_15_87 : ∀ i ∈ List.range 1, ThresholdAt 15 (87+i) := by decide +kernel

theorem threshold_15_88 : ∀ i ∈ List.range 1, ThresholdAt 15 (88+i) := by decide +kernel

theorem threshold_15_89 : ∀ i ∈ List.range 1, ThresholdAt 15 (89+i) := by decide +kernel

theorem threshold_15_90 : ∀ i ∈ List.range 1, ThresholdAt 15 (90+i) := by decide +kernel

theorem threshold_15_91 : ∀ i ∈ List.range 1, ThresholdAt 15 (91+i) := by decide +kernel

theorem threshold_15_92 : ∀ i ∈ List.range 1, ThresholdAt 15 (92+i) := by decide +kernel

theorem threshold_15_93 : ∀ i ∈ List.range 1, ThresholdAt 15 (93+i) := by decide +kernel

theorem threshold_15_94 : ∀ i ∈ List.range 1, ThresholdAt 15 (94+i) := by decide +kernel

theorem threshold_15_95 : ∀ i ∈ List.range 1, ThresholdAt 15 (95+i) := by decide +kernel

theorem threshold_15_96 : ∀ i ∈ List.range 1, ThresholdAt 15 (96+i) := by decide +kernel

theorem threshold_15_97 : ∀ i ∈ List.range 1, ThresholdAt 15 (97+i) := by decide +kernel

theorem threshold_15_98 : ∀ i ∈ List.range 1, ThresholdAt 15 (98+i) := by decide +kernel

theorem threshold_15_99 : ∀ i ∈ List.range 1, ThresholdAt 15 (99+i) := by decide +kernel

theorem threshold_15_100 : ∀ i ∈ List.range 1, ThresholdAt 15 (100+i) := by decide +kernel

theorem threshold_15_101 : ∀ i ∈ List.range 1, ThresholdAt 15 (101+i) := by decide +kernel

theorem threshold_15_102 : ∀ i ∈ List.range 1, ThresholdAt 15 (102+i) := by decide +kernel

theorem threshold_15_103 : ∀ i ∈ List.range 1, ThresholdAt 15 (103+i) := by decide +kernel

theorem threshold_15_104 : ∀ i ∈ List.range 1, ThresholdAt 15 (104+i) := by decide +kernel

theorem threshold_15_105 : ∀ i ∈ List.range 1, ThresholdAt 15 (105+i) := by decide +kernel

theorem threshold_15_106 : ∀ i ∈ List.range 1, ThresholdAt 15 (106+i) := by decide +kernel

theorem threshold_15_107 : ∀ i ∈ List.range 1, ThresholdAt 15 (107+i) := by decide +kernel

theorem threshold_15_108 : ∀ i ∈ List.range 1, ThresholdAt 15 (108+i) := by decide +kernel

theorem threshold_15_109 : ∀ i ∈ List.range 1, ThresholdAt 15 (109+i) := by decide +kernel

theorem threshold_15_110 : ∀ i ∈ List.range 1, ThresholdAt 15 (110+i) := by decide +kernel

theorem threshold_15_111 : ∀ i ∈ List.range 1, ThresholdAt 15 (111+i) := by decide +kernel

theorem threshold_15_112 : ∀ i ∈ List.range 1, ThresholdAt 15 (112+i) := by decide +kernel

theorem threshold_15_113 : ∀ i ∈ List.range 1, ThresholdAt 15 (113+i) := by decide +kernel

theorem threshold_15_114 : ∀ i ∈ List.range 1, ThresholdAt 15 (114+i) := by decide +kernel

theorem threshold_15_115 : ∀ i ∈ List.range 1, ThresholdAt 15 (115+i) := by decide +kernel

theorem threshold_15_116 : ∀ i ∈ List.range 1, ThresholdAt 15 (116+i) := by decide +kernel

theorem threshold_15_117 : ∀ i ∈ List.range 1, ThresholdAt 15 (117+i) := by decide +kernel

theorem threshold_15_118 : ∀ i ∈ List.range 1, ThresholdAt 15 (118+i) := by decide +kernel

theorem threshold_15_119 : ∀ i ∈ List.range 1, ThresholdAt 15 (119+i) := by decide +kernel

theorem threshold_15_120 : ∀ i ∈ List.range 1, ThresholdAt 15 (120+i) := by decide +kernel

theorem threshold_15_121 : ∀ i ∈ List.range 1, ThresholdAt 15 (121+i) := by decide +kernel

theorem threshold_15_122 : ∀ i ∈ List.range 1, ThresholdAt 15 (122+i) := by decide +kernel

theorem threshold_15_123 : ∀ i ∈ List.range 1, ThresholdAt 15 (123+i) := by decide +kernel

theorem threshold_15_124 : ∀ i ∈ List.range 1, ThresholdAt 15 (124+i) := by decide +kernel

theorem threshold_15_125 : ∀ i ∈ List.range 1, ThresholdAt 15 (125+i) := by decide +kernel

theorem threshold_15_126 : ∀ i ∈ List.range 1, ThresholdAt 15 (126+i) := by decide +kernel

theorem threshold_15_127 : ∀ i ∈ List.range 1, ThresholdAt 15 (127+i) := by decide +kernel

theorem threshold_15_128 : ∀ i ∈ List.range 1, ThresholdAt 15 (128+i) := by decide +kernel

theorem threshold_15_129 : ∀ i ∈ List.range 1, ThresholdAt 15 (129+i) := by decide +kernel

theorem threshold_15_130 : ∀ i ∈ List.range 1, ThresholdAt 15 (130+i) := by decide +kernel

theorem threshold_15_131 : ∀ i ∈ List.range 1, ThresholdAt 15 (131+i) := by decide +kernel

theorem threshold_15_132 : ∀ i ∈ List.range 1, ThresholdAt 15 (132+i) := by decide +kernel

theorem threshold_15_133 : ∀ i ∈ List.range 1, ThresholdAt 15 (133+i) := by decide +kernel

theorem threshold_15_134 : ∀ i ∈ List.range 1, ThresholdAt 15 (134+i) := by decide +kernel

theorem threshold_15_135 : ∀ i ∈ List.range 1, ThresholdAt 15 (135+i) := by decide +kernel

theorem threshold_15_136 : ∀ i ∈ List.range 1, ThresholdAt 15 (136+i) := by decide +kernel

theorem threshold_15_137 : ∀ i ∈ List.range 1, ThresholdAt 15 (137+i) := by decide +kernel

theorem threshold_15_138 : ∀ i ∈ List.range 1, ThresholdAt 15 (138+i) := by decide +kernel

theorem threshold_15_139 : ∀ i ∈ List.range 1, ThresholdAt 15 (139+i) := by decide +kernel

theorem threshold_15_140 : ∀ i ∈ List.range 1, ThresholdAt 15 (140+i) := by decide +kernel

theorem threshold_15_141 : ∀ i ∈ List.range 1, ThresholdAt 15 (141+i) := by decide +kernel

theorem threshold_15 (v : ℕ) (hv : v ∈ List.range 142) : ThresholdAt 15 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 15 v)
  have h := (join 0 71 71 (join 0 35 36 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_15_0 threshold_15_1) (join 2 1 1 threshold_15_2 threshold_15_3)) (join 4 2 2 (join 4 1 1 threshold_15_4 threshold_15_5) (join 6 1 1 threshold_15_6 threshold_15_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_15_8 threshold_15_9) (join 10 1 1 threshold_15_10 threshold_15_11)) (join 12 2 3 (join 12 1 1 threshold_15_12 threshold_15_13) (join 14 1 2 threshold_15_14 (join 15 1 1 threshold_15_15 threshold_15_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 threshold_15_17 threshold_15_18) (join 19 1 1 threshold_15_19 threshold_15_20)) (join 21 2 3 (join 21 1 1 threshold_15_21 threshold_15_22) (join 23 1 2 threshold_15_23 (join 24 1 1 threshold_15_24 threshold_15_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 threshold_15_26 threshold_15_27) (join 28 1 1 threshold_15_28 threshold_15_29)) (join 30 2 3 (join 30 1 1 threshold_15_30 threshold_15_31) (join 32 1 2 threshold_15_32 (join 33 1 1 threshold_15_33 threshold_15_34)))))) (join 35 18 18 (join 35 9 9 (join 35 4 5 (join 35 2 2 (join 35 1 1 threshold_15_35 threshold_15_36) (join 37 1 1 threshold_15_37 threshold_15_38)) (join 39 2 3 (join 39 1 1 threshold_15_39 threshold_15_40) (join 41 1 2 threshold_15_41 (join 42 1 1 threshold_15_42 threshold_15_43)))) (join 44 4 5 (join 44 2 2 (join 44 1 1 threshold_15_44 threshold_15_45) (join 46 1 1 threshold_15_46 threshold_15_47)) (join 48 2 3 (join 48 1 1 threshold_15_48 threshold_15_49) (join 50 1 2 threshold_15_50 (join 51 1 1 threshold_15_51 threshold_15_52))))) (join 53 9 9 (join 53 4 5 (join 53 2 2 (join 53 1 1 threshold_15_53 threshold_15_54) (join 55 1 1 threshold_15_55 threshold_15_56)) (join 57 2 3 (join 57 1 1 threshold_15_57 threshold_15_58) (join 59 1 2 threshold_15_59 (join 60 1 1 threshold_15_60 threshold_15_61)))) (join 62 4 5 (join 62 2 2 (join 62 1 1 threshold_15_62 threshold_15_63) (join 64 1 1 threshold_15_64 threshold_15_65)) (join 66 2 3 (join 66 1 1 threshold_15_66 threshold_15_67) (join 68 1 2 threshold_15_68 (join 69 1 1 threshold_15_69 threshold_15_70))))))) (join 71 35 36 (join 71 17 18 (join 71 8 9 (join 71 4 4 (join 71 2 2 (join 71 1 1 threshold_15_71 threshold_15_72) (join 73 1 1 threshold_15_73 threshold_15_74)) (join 75 2 2 (join 75 1 1 threshold_15_75 threshold_15_76) (join 77 1 1 threshold_15_77 threshold_15_78))) (join 79 4 5 (join 79 2 2 (join 79 1 1 threshold_15_79 threshold_15_80) (join 81 1 1 threshold_15_81 threshold_15_82)) (join 83 2 3 (join 83 1 1 threshold_15_83 threshold_15_84) (join 85 1 2 threshold_15_85 (join 86 1 1 threshold_15_86 threshold_15_87))))) (join 88 9 9 (join 88 4 5 (join 88 2 2 (join 88 1 1 threshold_15_88 threshold_15_89) (join 90 1 1 threshold_15_90 threshold_15_91)) (join 92 2 3 (join 92 1 1 threshold_15_92 threshold_15_93) (join 94 1 2 threshold_15_94 (join 95 1 1 threshold_15_95 threshold_15_96)))) (join 97 4 5 (join 97 2 2 (join 97 1 1 threshold_15_97 threshold_15_98) (join 99 1 1 threshold_15_99 threshold_15_100)) (join 101 2 3 (join 101 1 1 threshold_15_101 threshold_15_102) (join 103 1 2 threshold_15_103 (join 104 1 1 threshold_15_104 threshold_15_105)))))) (join 106 18 18 (join 106 9 9 (join 106 4 5 (join 106 2 2 (join 106 1 1 threshold_15_106 threshold_15_107) (join 108 1 1 threshold_15_108 threshold_15_109)) (join 110 2 3 (join 110 1 1 threshold_15_110 threshold_15_111) (join 112 1 2 threshold_15_112 (join 113 1 1 threshold_15_113 threshold_15_114)))) (join 115 4 5 (join 115 2 2 (join 115 1 1 threshold_15_115 threshold_15_116) (join 117 1 1 threshold_15_117 threshold_15_118)) (join 119 2 3 (join 119 1 1 threshold_15_119 threshold_15_120) (join 121 1 2 threshold_15_121 (join 122 1 1 threshold_15_122 threshold_15_123))))) (join 124 9 9 (join 124 4 5 (join 124 2 2 (join 124 1 1 threshold_15_124 threshold_15_125) (join 126 1 1 threshold_15_126 threshold_15_127)) (join 128 2 3 (join 128 1 1 threshold_15_128 threshold_15_129) (join 130 1 2 threshold_15_130 (join 131 1 1 threshold_15_131 threshold_15_132)))) (join 133 4 5 (join 133 2 2 (join 133 1 1 threshold_15_133 threshold_15_134) (join 135 1 1 threshold_15_135 threshold_15_136)) (join 137 2 3 (join 137 1 1 threshold_15_137 threshold_15_138) (join 139 1 2 threshold_15_139 (join 140 1 1 threshold_15_140 threshold_15_141))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_15_0 : ∀ i ∈ List.range 4, LedgerAt 15 (0+i) := by decide +kernel

theorem ledger_15_4 : ∀ i ∈ List.range 4, LedgerAt 15 (4+i) := by decide +kernel

theorem ledger_15_8 : ∀ i ∈ List.range 4, LedgerAt 15 (8+i) := by decide +kernel

theorem ledger_15_12 : ∀ i ∈ List.range 4, LedgerAt 15 (12+i) := by decide +kernel

theorem ledger_15_16 : ∀ i ∈ List.range 4, LedgerAt 15 (16+i) := by decide +kernel

theorem ledger_15_20 : ∀ i ∈ List.range 4, LedgerAt 15 (20+i) := by decide +kernel

theorem ledger_15_24 : ∀ i ∈ List.range 4, LedgerAt 15 (24+i) := by decide +kernel

theorem ledger_15_28 : ∀ i ∈ List.range 4, LedgerAt 15 (28+i) := by decide +kernel

theorem ledger_15_32 : ∀ i ∈ List.range 4, LedgerAt 15 (32+i) := by decide +kernel

theorem ledger_15_36 : ∀ i ∈ List.range 4, LedgerAt 15 (36+i) := by decide +kernel

theorem ledger_15_40 : ∀ i ∈ List.range 4, LedgerAt 15 (40+i) := by decide +kernel

theorem ledger_15_44 : ∀ i ∈ List.range 4, LedgerAt 15 (44+i) := by decide +kernel

theorem ledger_15_48 : ∀ i ∈ List.range 4, LedgerAt 15 (48+i) := by decide +kernel

theorem ledger_15_52 : ∀ i ∈ List.range 4, LedgerAt 15 (52+i) := by decide +kernel

theorem ledger_15_56 : ∀ i ∈ List.range 4, LedgerAt 15 (56+i) := by decide +kernel

theorem ledger_15_60 : ∀ i ∈ List.range 4, LedgerAt 15 (60+i) := by decide +kernel

theorem ledger_15_64 : ∀ i ∈ List.range 4, LedgerAt 15 (64+i) := by decide +kernel

theorem ledger_15_68 : ∀ i ∈ List.range 4, LedgerAt 15 (68+i) := by decide +kernel

theorem ledger_15_72 : ∀ i ∈ List.range 4, LedgerAt 15 (72+i) := by decide +kernel

theorem ledger_15_76 : ∀ i ∈ List.range 4, LedgerAt 15 (76+i) := by decide +kernel

theorem ledger_15_80 : ∀ i ∈ List.range 4, LedgerAt 15 (80+i) := by decide +kernel

theorem ledger_15_84 : ∀ i ∈ List.range 4, LedgerAt 15 (84+i) := by decide +kernel

theorem ledger_15_88 : ∀ i ∈ List.range 4, LedgerAt 15 (88+i) := by decide +kernel

theorem ledger_15_92 : ∀ i ∈ List.range 4, LedgerAt 15 (92+i) := by decide +kernel

theorem ledger_15_96 : ∀ i ∈ List.range 4, LedgerAt 15 (96+i) := by decide +kernel

theorem ledger_15_100 : ∀ i ∈ List.range 4, LedgerAt 15 (100+i) := by decide +kernel

theorem ledger_15_104 : ∀ i ∈ List.range 4, LedgerAt 15 (104+i) := by decide +kernel

theorem ledger_15_108 : ∀ i ∈ List.range 4, LedgerAt 15 (108+i) := by decide +kernel

theorem ledger_15_112 : ∀ i ∈ List.range 4, LedgerAt 15 (112+i) := by decide +kernel

theorem ledger_15_116 : ∀ i ∈ List.range 4, LedgerAt 15 (116+i) := by decide +kernel

theorem ledger_15_120 : ∀ i ∈ List.range 4, LedgerAt 15 (120+i) := by decide +kernel

theorem ledger_15_124 : ∀ i ∈ List.range 4, LedgerAt 15 (124+i) := by decide +kernel

theorem ledger_15_128 : ∀ i ∈ List.range 4, LedgerAt 15 (128+i) := by decide +kernel

theorem ledger_15_132 : ∀ i ∈ List.range 4, LedgerAt 15 (132+i) := by decide +kernel

theorem ledger_15_136 : ∀ i ∈ List.range 4, LedgerAt 15 (136+i) := by decide +kernel

theorem ledger_15_140 : ∀ i ∈ List.range 2, LedgerAt 15 (140+i) := by decide +kernel

theorem ledger_15 (v : ℕ) (hv : v ∈ List.range 142) : LedgerAt 15 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 15 v)
  have h := (join 0 72 70 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_15_0 ledger_15_4) (join 8 4 4 ledger_15_8 ledger_15_12)) (join 16 8 12 (join 16 4 4 ledger_15_16 ledger_15_20) (join 24 4 8 ledger_15_24 (join 28 4 4 ledger_15_28 ledger_15_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_15_36 ledger_15_40) (join 44 4 4 ledger_15_44 ledger_15_48)) (join 52 8 12 (join 52 4 4 ledger_15_52 ledger_15_56) (join 60 4 8 ledger_15_60 (join 64 4 4 ledger_15_64 ledger_15_68))))) (join 72 36 34 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_15_72 ledger_15_76) (join 80 4 4 ledger_15_80 ledger_15_84)) (join 88 8 12 (join 88 4 4 ledger_15_88 ledger_15_92) (join 96 4 8 ledger_15_96 (join 100 4 4 ledger_15_100 ledger_15_104)))) (join 108 16 18 (join 108 8 8 (join 108 4 4 ledger_15_108 ledger_15_112) (join 116 4 4 ledger_15_116 ledger_15_120)) (join 124 8 10 (join 124 4 4 ledger_15_124 ledger_15_128) (join 132 4 6 ledger_15_132 (join 136 4 2 ledger_15_136 ledger_15_140))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
