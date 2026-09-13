import ProximityPrize.SubmissionLower.AffineCheckedR056808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_6_0 : ∀ i ∈ List.range 4, SingleAt 6 (0+i) := by decide +kernel

theorem single_6_4 : ∀ i ∈ List.range 4, SingleAt 6 (4+i) := by decide +kernel

theorem single_6_8 : ∀ i ∈ List.range 4, SingleAt 6 (8+i) := by decide +kernel

theorem single_6_12 : ∀ i ∈ List.range 4, SingleAt 6 (12+i) := by decide +kernel

theorem single_6_16 : ∀ i ∈ List.range 4, SingleAt 6 (16+i) := by decide +kernel

theorem single_6_20 : ∀ i ∈ List.range 4, SingleAt 6 (20+i) := by decide +kernel

theorem single_6_24 : ∀ i ∈ List.range 4, SingleAt 6 (24+i) := by decide +kernel

theorem single_6_28 : ∀ i ∈ List.range 4, SingleAt 6 (28+i) := by decide +kernel

theorem single_6_32 : ∀ i ∈ List.range 4, SingleAt 6 (32+i) := by decide +kernel

theorem single_6_36 : ∀ i ∈ List.range 4, SingleAt 6 (36+i) := by decide +kernel

theorem single_6_40 : ∀ i ∈ List.range 4, SingleAt 6 (40+i) := by decide +kernel

theorem single_6_44 : ∀ i ∈ List.range 4, SingleAt 6 (44+i) := by decide +kernel

theorem single_6_48 : ∀ i ∈ List.range 4, SingleAt 6 (48+i) := by decide +kernel

theorem single_6_52 : ∀ i ∈ List.range 4, SingleAt 6 (52+i) := by decide +kernel

theorem single_6_56 : ∀ i ∈ List.range 4, SingleAt 6 (56+i) := by decide +kernel

theorem single_6_60 : ∀ i ∈ List.range 4, SingleAt 6 (60+i) := by decide +kernel

theorem single_6_64 : ∀ i ∈ List.range 4, SingleAt 6 (64+i) := by decide +kernel

theorem single_6_68 : ∀ i ∈ List.range 4, SingleAt 6 (68+i) := by decide +kernel

theorem single_6_72 : ∀ i ∈ List.range 4, SingleAt 6 (72+i) := by decide +kernel

theorem single_6_76 : ∀ i ∈ List.range 4, SingleAt 6 (76+i) := by decide +kernel

theorem single_6_80 : ∀ i ∈ List.range 4, SingleAt 6 (80+i) := by decide +kernel

theorem single_6_84 : ∀ i ∈ List.range 4, SingleAt 6 (84+i) := by decide +kernel

theorem single_6_88 : ∀ i ∈ List.range 4, SingleAt 6 (88+i) := by decide +kernel

theorem single_6_92 : ∀ i ∈ List.range 4, SingleAt 6 (92+i) := by decide +kernel

theorem single_6_96 : ∀ i ∈ List.range 4, SingleAt 6 (96+i) := by decide +kernel

theorem single_6_100 : ∀ i ∈ List.range 4, SingleAt 6 (100+i) := by decide +kernel

theorem single_6_104 : ∀ i ∈ List.range 4, SingleAt 6 (104+i) := by decide +kernel

theorem single_6_108 : ∀ i ∈ List.range 4, SingleAt 6 (108+i) := by decide +kernel

theorem single_6_112 : ∀ i ∈ List.range 4, SingleAt 6 (112+i) := by decide +kernel

theorem single_6_116 : ∀ i ∈ List.range 4, SingleAt 6 (116+i) := by decide +kernel

theorem single_6_120 : ∀ i ∈ List.range 4, SingleAt 6 (120+i) := by decide +kernel

theorem single_6_124 : ∀ i ∈ List.range 4, SingleAt 6 (124+i) := by decide +kernel

theorem single_6_128 : ∀ i ∈ List.range 4, SingleAt 6 (128+i) := by decide +kernel

theorem single_6_132 : ∀ i ∈ List.range 4, SingleAt 6 (132+i) := by decide +kernel

theorem single_6_136 : ∀ i ∈ List.range 4, SingleAt 6 (136+i) := by decide +kernel

theorem single_6_140 : ∀ i ∈ List.range 4, SingleAt 6 (140+i) := by decide +kernel

theorem single_6 (v : ℕ) (hv : v ∈ List.range 144) : SingleAt 6 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 6 v)
  have h := (join 0 72 72 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_6_0 single_6_4) (join 8 4 4 single_6_8 single_6_12)) (join 16 8 12 (join 16 4 4 single_6_16 single_6_20) (join 24 4 8 single_6_24 (join 28 4 4 single_6_28 single_6_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_6_36 single_6_40) (join 44 4 4 single_6_44 single_6_48)) (join 52 8 12 (join 52 4 4 single_6_52 single_6_56) (join 60 4 8 single_6_60 (join 64 4 4 single_6_64 single_6_68))))) (join 72 36 36 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_6_72 single_6_76) (join 80 4 4 single_6_80 single_6_84)) (join 88 8 12 (join 88 4 4 single_6_88 single_6_92) (join 96 4 8 single_6_96 (join 100 4 4 single_6_100 single_6_104)))) (join 108 16 20 (join 108 8 8 (join 108 4 4 single_6_108 single_6_112) (join 116 4 4 single_6_116 single_6_120)) (join 124 8 12 (join 124 4 4 single_6_124 single_6_128) (join 132 4 8 single_6_132 (join 136 4 4 single_6_136 single_6_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_6_0 : ∀ i ∈ List.range 4, PhaseAt 6 (0+i) := by decide +kernel

theorem phase_6_4 : ∀ i ∈ List.range 4, PhaseAt 6 (4+i) := by decide +kernel

theorem phase_6_8 : ∀ i ∈ List.range 4, PhaseAt 6 (8+i) := by decide +kernel

theorem phase_6_12 : ∀ i ∈ List.range 4, PhaseAt 6 (12+i) := by decide +kernel

theorem phase_6_16 : ∀ i ∈ List.range 4, PhaseAt 6 (16+i) := by decide +kernel

theorem phase_6_20 : ∀ i ∈ List.range 4, PhaseAt 6 (20+i) := by decide +kernel

theorem phase_6_24 : ∀ i ∈ List.range 4, PhaseAt 6 (24+i) := by decide +kernel

theorem phase_6_28 : ∀ i ∈ List.range 4, PhaseAt 6 (28+i) := by decide +kernel

theorem phase_6_32 : ∀ i ∈ List.range 4, PhaseAt 6 (32+i) := by decide +kernel

theorem phase_6_36 : ∀ i ∈ List.range 4, PhaseAt 6 (36+i) := by decide +kernel

theorem phase_6_40 : ∀ i ∈ List.range 4, PhaseAt 6 (40+i) := by decide +kernel

theorem phase_6_44 : ∀ i ∈ List.range 4, PhaseAt 6 (44+i) := by decide +kernel

theorem phase_6_48 : ∀ i ∈ List.range 4, PhaseAt 6 (48+i) := by decide +kernel

theorem phase_6_52 : ∀ i ∈ List.range 4, PhaseAt 6 (52+i) := by decide +kernel

theorem phase_6_56 : ∀ i ∈ List.range 4, PhaseAt 6 (56+i) := by decide +kernel

theorem phase_6_60 : ∀ i ∈ List.range 4, PhaseAt 6 (60+i) := by decide +kernel

theorem phase_6_64 : ∀ i ∈ List.range 4, PhaseAt 6 (64+i) := by decide +kernel

theorem phase_6_68 : ∀ i ∈ List.range 4, PhaseAt 6 (68+i) := by decide +kernel

theorem phase_6_72 : ∀ i ∈ List.range 4, PhaseAt 6 (72+i) := by decide +kernel

theorem phase_6_76 : ∀ i ∈ List.range 4, PhaseAt 6 (76+i) := by decide +kernel

theorem phase_6_80 : ∀ i ∈ List.range 4, PhaseAt 6 (80+i) := by decide +kernel

theorem phase_6_84 : ∀ i ∈ List.range 4, PhaseAt 6 (84+i) := by decide +kernel

theorem phase_6_88 : ∀ i ∈ List.range 4, PhaseAt 6 (88+i) := by decide +kernel

theorem phase_6_92 : ∀ i ∈ List.range 4, PhaseAt 6 (92+i) := by decide +kernel

theorem phase_6_96 : ∀ i ∈ List.range 4, PhaseAt 6 (96+i) := by decide +kernel

theorem phase_6_100 : ∀ i ∈ List.range 4, PhaseAt 6 (100+i) := by decide +kernel

theorem phase_6_104 : ∀ i ∈ List.range 4, PhaseAt 6 (104+i) := by decide +kernel

theorem phase_6_108 : ∀ i ∈ List.range 4, PhaseAt 6 (108+i) := by decide +kernel

theorem phase_6_112 : ∀ i ∈ List.range 4, PhaseAt 6 (112+i) := by decide +kernel

theorem phase_6_116 : ∀ i ∈ List.range 4, PhaseAt 6 (116+i) := by decide +kernel

theorem phase_6_120 : ∀ i ∈ List.range 4, PhaseAt 6 (120+i) := by decide +kernel

theorem phase_6_124 : ∀ i ∈ List.range 4, PhaseAt 6 (124+i) := by decide +kernel

theorem phase_6_128 : ∀ i ∈ List.range 4, PhaseAt 6 (128+i) := by decide +kernel

theorem phase_6_132 : ∀ i ∈ List.range 4, PhaseAt 6 (132+i) := by decide +kernel

theorem phase_6_136 : ∀ i ∈ List.range 4, PhaseAt 6 (136+i) := by decide +kernel

theorem phase_6_140 : ∀ i ∈ List.range 4, PhaseAt 6 (140+i) := by decide +kernel

theorem phase_6 (v : ℕ) (hv : v ∈ List.range 144) : PhaseAt 6 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 6 v)
  have h := (join 0 72 72 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_6_0 phase_6_4) (join 8 4 4 phase_6_8 phase_6_12)) (join 16 8 12 (join 16 4 4 phase_6_16 phase_6_20) (join 24 4 8 phase_6_24 (join 28 4 4 phase_6_28 phase_6_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_6_36 phase_6_40) (join 44 4 4 phase_6_44 phase_6_48)) (join 52 8 12 (join 52 4 4 phase_6_52 phase_6_56) (join 60 4 8 phase_6_60 (join 64 4 4 phase_6_64 phase_6_68))))) (join 72 36 36 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_6_72 phase_6_76) (join 80 4 4 phase_6_80 phase_6_84)) (join 88 8 12 (join 88 4 4 phase_6_88 phase_6_92) (join 96 4 8 phase_6_96 (join 100 4 4 phase_6_100 phase_6_104)))) (join 108 16 20 (join 108 8 8 (join 108 4 4 phase_6_108 phase_6_112) (join 116 4 4 phase_6_116 phase_6_120)) (join 124 8 12 (join 124 4 4 phase_6_124 phase_6_128) (join 132 4 8 phase_6_132 (join 136 4 4 phase_6_136 phase_6_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_6_0 : ∀ i ∈ List.range 1, ThresholdAt 6 (0+i) := by decide +kernel

theorem threshold_6_1 : ∀ i ∈ List.range 1, ThresholdAt 6 (1+i) := by decide +kernel

theorem threshold_6_2 : ∀ i ∈ List.range 1, ThresholdAt 6 (2+i) := by decide +kernel

theorem threshold_6_3 : ∀ i ∈ List.range 1, ThresholdAt 6 (3+i) := by decide +kernel

theorem threshold_6_4 : ∀ i ∈ List.range 1, ThresholdAt 6 (4+i) := by decide +kernel

theorem threshold_6_5 : ∀ i ∈ List.range 1, ThresholdAt 6 (5+i) := by decide +kernel

theorem threshold_6_6 : ∀ i ∈ List.range 1, ThresholdAt 6 (6+i) := by decide +kernel

theorem threshold_6_7 : ∀ i ∈ List.range 1, ThresholdAt 6 (7+i) := by decide +kernel

theorem threshold_6_8 : ∀ i ∈ List.range 1, ThresholdAt 6 (8+i) := by decide +kernel

theorem threshold_6_9 : ∀ i ∈ List.range 1, ThresholdAt 6 (9+i) := by decide +kernel

theorem threshold_6_10 : ∀ i ∈ List.range 1, ThresholdAt 6 (10+i) := by decide +kernel

theorem threshold_6_11 : ∀ i ∈ List.range 1, ThresholdAt 6 (11+i) := by decide +kernel

theorem threshold_6_12 : ∀ i ∈ List.range 1, ThresholdAt 6 (12+i) := by decide +kernel

theorem threshold_6_13 : ∀ i ∈ List.range 1, ThresholdAt 6 (13+i) := by decide +kernel

theorem threshold_6_14 : ∀ i ∈ List.range 1, ThresholdAt 6 (14+i) := by decide +kernel

theorem threshold_6_15 : ∀ i ∈ List.range 1, ThresholdAt 6 (15+i) := by decide +kernel

theorem threshold_6_16 : ∀ i ∈ List.range 1, ThresholdAt 6 (16+i) := by decide +kernel

theorem threshold_6_17 : ∀ i ∈ List.range 1, ThresholdAt 6 (17+i) := by decide +kernel

theorem threshold_6_18 : ∀ i ∈ List.range 1, ThresholdAt 6 (18+i) := by decide +kernel

theorem threshold_6_19 : ∀ i ∈ List.range 1, ThresholdAt 6 (19+i) := by decide +kernel

theorem threshold_6_20 : ∀ i ∈ List.range 1, ThresholdAt 6 (20+i) := by decide +kernel

theorem threshold_6_21 : ∀ i ∈ List.range 1, ThresholdAt 6 (21+i) := by decide +kernel

theorem threshold_6_22 : ∀ i ∈ List.range 1, ThresholdAt 6 (22+i) := by decide +kernel

theorem threshold_6_23 : ∀ i ∈ List.range 1, ThresholdAt 6 (23+i) := by decide +kernel

theorem threshold_6_24 : ∀ i ∈ List.range 1, ThresholdAt 6 (24+i) := by decide +kernel

theorem threshold_6_25 : ∀ i ∈ List.range 1, ThresholdAt 6 (25+i) := by decide +kernel

theorem threshold_6_26 : ∀ i ∈ List.range 1, ThresholdAt 6 (26+i) := by decide +kernel

theorem threshold_6_27 : ∀ i ∈ List.range 1, ThresholdAt 6 (27+i) := by decide +kernel

theorem threshold_6_28 : ∀ i ∈ List.range 1, ThresholdAt 6 (28+i) := by decide +kernel

theorem threshold_6_29 : ∀ i ∈ List.range 1, ThresholdAt 6 (29+i) := by decide +kernel

theorem threshold_6_30 : ∀ i ∈ List.range 1, ThresholdAt 6 (30+i) := by decide +kernel

theorem threshold_6_31 : ∀ i ∈ List.range 1, ThresholdAt 6 (31+i) := by decide +kernel

theorem threshold_6_32 : ∀ i ∈ List.range 1, ThresholdAt 6 (32+i) := by decide +kernel

theorem threshold_6_33 : ∀ i ∈ List.range 1, ThresholdAt 6 (33+i) := by decide +kernel

theorem threshold_6_34 : ∀ i ∈ List.range 1, ThresholdAt 6 (34+i) := by decide +kernel

theorem threshold_6_35 : ∀ i ∈ List.range 1, ThresholdAt 6 (35+i) := by decide +kernel

theorem threshold_6_36 : ∀ i ∈ List.range 1, ThresholdAt 6 (36+i) := by decide +kernel

theorem threshold_6_37 : ∀ i ∈ List.range 1, ThresholdAt 6 (37+i) := by decide +kernel

theorem threshold_6_38 : ∀ i ∈ List.range 1, ThresholdAt 6 (38+i) := by decide +kernel

theorem threshold_6_39 : ∀ i ∈ List.range 1, ThresholdAt 6 (39+i) := by decide +kernel

theorem threshold_6_40 : ∀ i ∈ List.range 1, ThresholdAt 6 (40+i) := by decide +kernel

theorem threshold_6_41 : ∀ i ∈ List.range 1, ThresholdAt 6 (41+i) := by decide +kernel

theorem threshold_6_42 : ∀ i ∈ List.range 1, ThresholdAt 6 (42+i) := by decide +kernel

theorem threshold_6_43 : ∀ i ∈ List.range 1, ThresholdAt 6 (43+i) := by decide +kernel

theorem threshold_6_44 : ∀ i ∈ List.range 1, ThresholdAt 6 (44+i) := by decide +kernel

theorem threshold_6_45 : ∀ i ∈ List.range 1, ThresholdAt 6 (45+i) := by decide +kernel

theorem threshold_6_46 : ∀ i ∈ List.range 1, ThresholdAt 6 (46+i) := by decide +kernel

theorem threshold_6_47 : ∀ i ∈ List.range 1, ThresholdAt 6 (47+i) := by decide +kernel

theorem threshold_6_48 : ∀ i ∈ List.range 1, ThresholdAt 6 (48+i) := by decide +kernel

theorem threshold_6_49 : ∀ i ∈ List.range 1, ThresholdAt 6 (49+i) := by decide +kernel

theorem threshold_6_50 : ∀ i ∈ List.range 1, ThresholdAt 6 (50+i) := by decide +kernel

theorem threshold_6_51 : ∀ i ∈ List.range 1, ThresholdAt 6 (51+i) := by decide +kernel

theorem threshold_6_52 : ∀ i ∈ List.range 1, ThresholdAt 6 (52+i) := by decide +kernel

theorem threshold_6_53 : ∀ i ∈ List.range 1, ThresholdAt 6 (53+i) := by decide +kernel

theorem threshold_6_54 : ∀ i ∈ List.range 1, ThresholdAt 6 (54+i) := by decide +kernel

theorem threshold_6_55 : ∀ i ∈ List.range 1, ThresholdAt 6 (55+i) := by decide +kernel

theorem threshold_6_56 : ∀ i ∈ List.range 1, ThresholdAt 6 (56+i) := by decide +kernel

theorem threshold_6_57 : ∀ i ∈ List.range 1, ThresholdAt 6 (57+i) := by decide +kernel

theorem threshold_6_58 : ∀ i ∈ List.range 1, ThresholdAt 6 (58+i) := by decide +kernel

theorem threshold_6_59 : ∀ i ∈ List.range 1, ThresholdAt 6 (59+i) := by decide +kernel

theorem threshold_6_60 : ∀ i ∈ List.range 1, ThresholdAt 6 (60+i) := by decide +kernel

theorem threshold_6_61 : ∀ i ∈ List.range 1, ThresholdAt 6 (61+i) := by decide +kernel

theorem threshold_6_62 : ∀ i ∈ List.range 1, ThresholdAt 6 (62+i) := by decide +kernel

theorem threshold_6_63 : ∀ i ∈ List.range 1, ThresholdAt 6 (63+i) := by decide +kernel

theorem threshold_6_64 : ∀ i ∈ List.range 1, ThresholdAt 6 (64+i) := by decide +kernel

theorem threshold_6_65 : ∀ i ∈ List.range 1, ThresholdAt 6 (65+i) := by decide +kernel

theorem threshold_6_66 : ∀ i ∈ List.range 1, ThresholdAt 6 (66+i) := by decide +kernel

theorem threshold_6_67 : ∀ i ∈ List.range 1, ThresholdAt 6 (67+i) := by decide +kernel

theorem threshold_6_68 : ∀ i ∈ List.range 1, ThresholdAt 6 (68+i) := by decide +kernel

theorem threshold_6_69 : ∀ i ∈ List.range 1, ThresholdAt 6 (69+i) := by decide +kernel

theorem threshold_6_70 : ∀ i ∈ List.range 1, ThresholdAt 6 (70+i) := by decide +kernel

theorem threshold_6_71 : ∀ i ∈ List.range 1, ThresholdAt 6 (71+i) := by decide +kernel

theorem threshold_6_72 : ∀ i ∈ List.range 1, ThresholdAt 6 (72+i) := by decide +kernel

theorem threshold_6_73 : ∀ i ∈ List.range 1, ThresholdAt 6 (73+i) := by decide +kernel

theorem threshold_6_74 : ∀ i ∈ List.range 1, ThresholdAt 6 (74+i) := by decide +kernel

theorem threshold_6_75 : ∀ i ∈ List.range 1, ThresholdAt 6 (75+i) := by decide +kernel

theorem threshold_6_76 : ∀ i ∈ List.range 1, ThresholdAt 6 (76+i) := by decide +kernel

theorem threshold_6_77 : ∀ i ∈ List.range 1, ThresholdAt 6 (77+i) := by decide +kernel

theorem threshold_6_78 : ∀ i ∈ List.range 1, ThresholdAt 6 (78+i) := by decide +kernel

theorem threshold_6_79 : ∀ i ∈ List.range 1, ThresholdAt 6 (79+i) := by decide +kernel

theorem threshold_6_80 : ∀ i ∈ List.range 1, ThresholdAt 6 (80+i) := by decide +kernel

theorem threshold_6_81 : ∀ i ∈ List.range 1, ThresholdAt 6 (81+i) := by decide +kernel

theorem threshold_6_82 : ∀ i ∈ List.range 1, ThresholdAt 6 (82+i) := by decide +kernel

theorem threshold_6_83 : ∀ i ∈ List.range 1, ThresholdAt 6 (83+i) := by decide +kernel

theorem threshold_6_84 : ∀ i ∈ List.range 1, ThresholdAt 6 (84+i) := by decide +kernel

theorem threshold_6_85 : ∀ i ∈ List.range 1, ThresholdAt 6 (85+i) := by decide +kernel

theorem threshold_6_86 : ∀ i ∈ List.range 1, ThresholdAt 6 (86+i) := by decide +kernel

theorem threshold_6_87 : ∀ i ∈ List.range 1, ThresholdAt 6 (87+i) := by decide +kernel

theorem threshold_6_88 : ∀ i ∈ List.range 1, ThresholdAt 6 (88+i) := by decide +kernel

theorem threshold_6_89 : ∀ i ∈ List.range 1, ThresholdAt 6 (89+i) := by decide +kernel

theorem threshold_6_90 : ∀ i ∈ List.range 1, ThresholdAt 6 (90+i) := by decide +kernel

theorem threshold_6_91 : ∀ i ∈ List.range 1, ThresholdAt 6 (91+i) := by decide +kernel

theorem threshold_6_92 : ∀ i ∈ List.range 1, ThresholdAt 6 (92+i) := by decide +kernel

theorem threshold_6_93 : ∀ i ∈ List.range 1, ThresholdAt 6 (93+i) := by decide +kernel

theorem threshold_6_94 : ∀ i ∈ List.range 1, ThresholdAt 6 (94+i) := by decide +kernel

theorem threshold_6_95 : ∀ i ∈ List.range 1, ThresholdAt 6 (95+i) := by decide +kernel

theorem threshold_6_96 : ∀ i ∈ List.range 1, ThresholdAt 6 (96+i) := by decide +kernel

theorem threshold_6_97 : ∀ i ∈ List.range 1, ThresholdAt 6 (97+i) := by decide +kernel

theorem threshold_6_98 : ∀ i ∈ List.range 1, ThresholdAt 6 (98+i) := by decide +kernel

theorem threshold_6_99 : ∀ i ∈ List.range 1, ThresholdAt 6 (99+i) := by decide +kernel

theorem threshold_6_100 : ∀ i ∈ List.range 1, ThresholdAt 6 (100+i) := by decide +kernel

theorem threshold_6_101 : ∀ i ∈ List.range 1, ThresholdAt 6 (101+i) := by decide +kernel

theorem threshold_6_102 : ∀ i ∈ List.range 1, ThresholdAt 6 (102+i) := by decide +kernel

theorem threshold_6_103 : ∀ i ∈ List.range 1, ThresholdAt 6 (103+i) := by decide +kernel

theorem threshold_6_104 : ∀ i ∈ List.range 1, ThresholdAt 6 (104+i) := by decide +kernel

theorem threshold_6_105 : ∀ i ∈ List.range 1, ThresholdAt 6 (105+i) := by decide +kernel

theorem threshold_6_106 : ∀ i ∈ List.range 1, ThresholdAt 6 (106+i) := by decide +kernel

theorem threshold_6_107 : ∀ i ∈ List.range 1, ThresholdAt 6 (107+i) := by decide +kernel

theorem threshold_6_108 : ∀ i ∈ List.range 1, ThresholdAt 6 (108+i) := by decide +kernel

theorem threshold_6_109 : ∀ i ∈ List.range 1, ThresholdAt 6 (109+i) := by decide +kernel

theorem threshold_6_110 : ∀ i ∈ List.range 1, ThresholdAt 6 (110+i) := by decide +kernel

theorem threshold_6_111 : ∀ i ∈ List.range 1, ThresholdAt 6 (111+i) := by decide +kernel

theorem threshold_6_112 : ∀ i ∈ List.range 1, ThresholdAt 6 (112+i) := by decide +kernel

theorem threshold_6_113 : ∀ i ∈ List.range 1, ThresholdAt 6 (113+i) := by decide +kernel

theorem threshold_6_114 : ∀ i ∈ List.range 1, ThresholdAt 6 (114+i) := by decide +kernel

theorem threshold_6_115 : ∀ i ∈ List.range 1, ThresholdAt 6 (115+i) := by decide +kernel

theorem threshold_6_116 : ∀ i ∈ List.range 1, ThresholdAt 6 (116+i) := by decide +kernel

theorem threshold_6_117 : ∀ i ∈ List.range 1, ThresholdAt 6 (117+i) := by decide +kernel

theorem threshold_6_118 : ∀ i ∈ List.range 1, ThresholdAt 6 (118+i) := by decide +kernel

theorem threshold_6_119 : ∀ i ∈ List.range 1, ThresholdAt 6 (119+i) := by decide +kernel

theorem threshold_6_120 : ∀ i ∈ List.range 1, ThresholdAt 6 (120+i) := by decide +kernel

theorem threshold_6_121 : ∀ i ∈ List.range 1, ThresholdAt 6 (121+i) := by decide +kernel

theorem threshold_6_122 : ∀ i ∈ List.range 1, ThresholdAt 6 (122+i) := by decide +kernel

theorem threshold_6_123 : ∀ i ∈ List.range 1, ThresholdAt 6 (123+i) := by decide +kernel

theorem threshold_6_124 : ∀ i ∈ List.range 1, ThresholdAt 6 (124+i) := by decide +kernel

theorem threshold_6_125 : ∀ i ∈ List.range 1, ThresholdAt 6 (125+i) := by decide +kernel

theorem threshold_6_126 : ∀ i ∈ List.range 1, ThresholdAt 6 (126+i) := by decide +kernel

theorem threshold_6_127 : ∀ i ∈ List.range 1, ThresholdAt 6 (127+i) := by decide +kernel

theorem threshold_6_128 : ∀ i ∈ List.range 1, ThresholdAt 6 (128+i) := by decide +kernel

theorem threshold_6_129 : ∀ i ∈ List.range 1, ThresholdAt 6 (129+i) := by decide +kernel

theorem threshold_6_130 : ∀ i ∈ List.range 1, ThresholdAt 6 (130+i) := by decide +kernel

theorem threshold_6_131 : ∀ i ∈ List.range 1, ThresholdAt 6 (131+i) := by decide +kernel

theorem threshold_6_132 : ∀ i ∈ List.range 1, ThresholdAt 6 (132+i) := by decide +kernel

theorem threshold_6_133 : ∀ i ∈ List.range 1, ThresholdAt 6 (133+i) := by decide +kernel

theorem threshold_6_134 : ∀ i ∈ List.range 1, ThresholdAt 6 (134+i) := by decide +kernel

theorem threshold_6_135 : ∀ i ∈ List.range 1, ThresholdAt 6 (135+i) := by decide +kernel

theorem threshold_6_136 : ∀ i ∈ List.range 1, ThresholdAt 6 (136+i) := by decide +kernel

theorem threshold_6_137 : ∀ i ∈ List.range 1, ThresholdAt 6 (137+i) := by decide +kernel

theorem threshold_6_138 : ∀ i ∈ List.range 1, ThresholdAt 6 (138+i) := by decide +kernel

theorem threshold_6_139 : ∀ i ∈ List.range 1, ThresholdAt 6 (139+i) := by decide +kernel

theorem threshold_6_140 : ∀ i ∈ List.range 1, ThresholdAt 6 (140+i) := by decide +kernel

theorem threshold_6_141 : ∀ i ∈ List.range 1, ThresholdAt 6 (141+i) := by decide +kernel

theorem threshold_6_142 : ∀ i ∈ List.range 1, ThresholdAt 6 (142+i) := by decide +kernel

theorem threshold_6_143 : ∀ i ∈ List.range 1, ThresholdAt 6 (143+i) := by decide +kernel

theorem threshold_6 (v : ℕ) (hv : v ∈ List.range 144) : ThresholdAt 6 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 6 v)
  have h := (join 0 72 72 (join 0 36 36 (join 0 18 18 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_6_0 threshold_6_1) (join 2 1 1 threshold_6_2 threshold_6_3)) (join 4 2 3 (join 4 1 1 threshold_6_4 threshold_6_5) (join 6 1 2 threshold_6_6 (join 7 1 1 threshold_6_7 threshold_6_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 threshold_6_9 threshold_6_10) (join 11 1 1 threshold_6_11 threshold_6_12)) (join 13 2 3 (join 13 1 1 threshold_6_13 threshold_6_14) (join 15 1 2 threshold_6_15 (join 16 1 1 threshold_6_16 threshold_6_17))))) (join 18 9 9 (join 18 4 5 (join 18 2 2 (join 18 1 1 threshold_6_18 threshold_6_19) (join 20 1 1 threshold_6_20 threshold_6_21)) (join 22 2 3 (join 22 1 1 threshold_6_22 threshold_6_23) (join 24 1 2 threshold_6_24 (join 25 1 1 threshold_6_25 threshold_6_26)))) (join 27 4 5 (join 27 2 2 (join 27 1 1 threshold_6_27 threshold_6_28) (join 29 1 1 threshold_6_29 threshold_6_30)) (join 31 2 3 (join 31 1 1 threshold_6_31 threshold_6_32) (join 33 1 2 threshold_6_33 (join 34 1 1 threshold_6_34 threshold_6_35)))))) (join 36 18 18 (join 36 9 9 (join 36 4 5 (join 36 2 2 (join 36 1 1 threshold_6_36 threshold_6_37) (join 38 1 1 threshold_6_38 threshold_6_39)) (join 40 2 3 (join 40 1 1 threshold_6_40 threshold_6_41) (join 42 1 2 threshold_6_42 (join 43 1 1 threshold_6_43 threshold_6_44)))) (join 45 4 5 (join 45 2 2 (join 45 1 1 threshold_6_45 threshold_6_46) (join 47 1 1 threshold_6_47 threshold_6_48)) (join 49 2 3 (join 49 1 1 threshold_6_49 threshold_6_50) (join 51 1 2 threshold_6_51 (join 52 1 1 threshold_6_52 threshold_6_53))))) (join 54 9 9 (join 54 4 5 (join 54 2 2 (join 54 1 1 threshold_6_54 threshold_6_55) (join 56 1 1 threshold_6_56 threshold_6_57)) (join 58 2 3 (join 58 1 1 threshold_6_58 threshold_6_59) (join 60 1 2 threshold_6_60 (join 61 1 1 threshold_6_61 threshold_6_62)))) (join 63 4 5 (join 63 2 2 (join 63 1 1 threshold_6_63 threshold_6_64) (join 65 1 1 threshold_6_65 threshold_6_66)) (join 67 2 3 (join 67 1 1 threshold_6_67 threshold_6_68) (join 69 1 2 threshold_6_69 (join 70 1 1 threshold_6_70 threshold_6_71))))))) (join 72 36 36 (join 72 18 18 (join 72 9 9 (join 72 4 5 (join 72 2 2 (join 72 1 1 threshold_6_72 threshold_6_73) (join 74 1 1 threshold_6_74 threshold_6_75)) (join 76 2 3 (join 76 1 1 threshold_6_76 threshold_6_77) (join 78 1 2 threshold_6_78 (join 79 1 1 threshold_6_79 threshold_6_80)))) (join 81 4 5 (join 81 2 2 (join 81 1 1 threshold_6_81 threshold_6_82) (join 83 1 1 threshold_6_83 threshold_6_84)) (join 85 2 3 (join 85 1 1 threshold_6_85 threshold_6_86) (join 87 1 2 threshold_6_87 (join 88 1 1 threshold_6_88 threshold_6_89))))) (join 90 9 9 (join 90 4 5 (join 90 2 2 (join 90 1 1 threshold_6_90 threshold_6_91) (join 92 1 1 threshold_6_92 threshold_6_93)) (join 94 2 3 (join 94 1 1 threshold_6_94 threshold_6_95) (join 96 1 2 threshold_6_96 (join 97 1 1 threshold_6_97 threshold_6_98)))) (join 99 4 5 (join 99 2 2 (join 99 1 1 threshold_6_99 threshold_6_100) (join 101 1 1 threshold_6_101 threshold_6_102)) (join 103 2 3 (join 103 1 1 threshold_6_103 threshold_6_104) (join 105 1 2 threshold_6_105 (join 106 1 1 threshold_6_106 threshold_6_107)))))) (join 108 18 18 (join 108 9 9 (join 108 4 5 (join 108 2 2 (join 108 1 1 threshold_6_108 threshold_6_109) (join 110 1 1 threshold_6_110 threshold_6_111)) (join 112 2 3 (join 112 1 1 threshold_6_112 threshold_6_113) (join 114 1 2 threshold_6_114 (join 115 1 1 threshold_6_115 threshold_6_116)))) (join 117 4 5 (join 117 2 2 (join 117 1 1 threshold_6_117 threshold_6_118) (join 119 1 1 threshold_6_119 threshold_6_120)) (join 121 2 3 (join 121 1 1 threshold_6_121 threshold_6_122) (join 123 1 2 threshold_6_123 (join 124 1 1 threshold_6_124 threshold_6_125))))) (join 126 9 9 (join 126 4 5 (join 126 2 2 (join 126 1 1 threshold_6_126 threshold_6_127) (join 128 1 1 threshold_6_128 threshold_6_129)) (join 130 2 3 (join 130 1 1 threshold_6_130 threshold_6_131) (join 132 1 2 threshold_6_132 (join 133 1 1 threshold_6_133 threshold_6_134)))) (join 135 4 5 (join 135 2 2 (join 135 1 1 threshold_6_135 threshold_6_136) (join 137 1 1 threshold_6_137 threshold_6_138)) (join 139 2 3 (join 139 1 1 threshold_6_139 threshold_6_140) (join 141 1 2 threshold_6_141 (join 142 1 1 threshold_6_142 threshold_6_143))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_6_0 : ∀ i ∈ List.range 4, LedgerAt 6 (0+i) := by decide +kernel

theorem ledger_6_4 : ∀ i ∈ List.range 4, LedgerAt 6 (4+i) := by decide +kernel

theorem ledger_6_8 : ∀ i ∈ List.range 4, LedgerAt 6 (8+i) := by decide +kernel

theorem ledger_6_12 : ∀ i ∈ List.range 4, LedgerAt 6 (12+i) := by decide +kernel

theorem ledger_6_16 : ∀ i ∈ List.range 4, LedgerAt 6 (16+i) := by decide +kernel

theorem ledger_6_20 : ∀ i ∈ List.range 4, LedgerAt 6 (20+i) := by decide +kernel

theorem ledger_6_24 : ∀ i ∈ List.range 4, LedgerAt 6 (24+i) := by decide +kernel

theorem ledger_6_28 : ∀ i ∈ List.range 4, LedgerAt 6 (28+i) := by decide +kernel

theorem ledger_6_32 : ∀ i ∈ List.range 4, LedgerAt 6 (32+i) := by decide +kernel

theorem ledger_6_36 : ∀ i ∈ List.range 4, LedgerAt 6 (36+i) := by decide +kernel

theorem ledger_6_40 : ∀ i ∈ List.range 4, LedgerAt 6 (40+i) := by decide +kernel

theorem ledger_6_44 : ∀ i ∈ List.range 4, LedgerAt 6 (44+i) := by decide +kernel

theorem ledger_6_48 : ∀ i ∈ List.range 4, LedgerAt 6 (48+i) := by decide +kernel

theorem ledger_6_52 : ∀ i ∈ List.range 4, LedgerAt 6 (52+i) := by decide +kernel

theorem ledger_6_56 : ∀ i ∈ List.range 4, LedgerAt 6 (56+i) := by decide +kernel

theorem ledger_6_60 : ∀ i ∈ List.range 4, LedgerAt 6 (60+i) := by decide +kernel

theorem ledger_6_64 : ∀ i ∈ List.range 4, LedgerAt 6 (64+i) := by decide +kernel

theorem ledger_6_68 : ∀ i ∈ List.range 4, LedgerAt 6 (68+i) := by decide +kernel

theorem ledger_6_72 : ∀ i ∈ List.range 4, LedgerAt 6 (72+i) := by decide +kernel

theorem ledger_6_76 : ∀ i ∈ List.range 4, LedgerAt 6 (76+i) := by decide +kernel

theorem ledger_6_80 : ∀ i ∈ List.range 4, LedgerAt 6 (80+i) := by decide +kernel

theorem ledger_6_84 : ∀ i ∈ List.range 4, LedgerAt 6 (84+i) := by decide +kernel

theorem ledger_6_88 : ∀ i ∈ List.range 4, LedgerAt 6 (88+i) := by decide +kernel

theorem ledger_6_92 : ∀ i ∈ List.range 4, LedgerAt 6 (92+i) := by decide +kernel

theorem ledger_6_96 : ∀ i ∈ List.range 4, LedgerAt 6 (96+i) := by decide +kernel

theorem ledger_6_100 : ∀ i ∈ List.range 4, LedgerAt 6 (100+i) := by decide +kernel

theorem ledger_6_104 : ∀ i ∈ List.range 4, LedgerAt 6 (104+i) := by decide +kernel

theorem ledger_6_108 : ∀ i ∈ List.range 4, LedgerAt 6 (108+i) := by decide +kernel

theorem ledger_6_112 : ∀ i ∈ List.range 4, LedgerAt 6 (112+i) := by decide +kernel

theorem ledger_6_116 : ∀ i ∈ List.range 4, LedgerAt 6 (116+i) := by decide +kernel

theorem ledger_6_120 : ∀ i ∈ List.range 4, LedgerAt 6 (120+i) := by decide +kernel

theorem ledger_6_124 : ∀ i ∈ List.range 4, LedgerAt 6 (124+i) := by decide +kernel

theorem ledger_6_128 : ∀ i ∈ List.range 4, LedgerAt 6 (128+i) := by decide +kernel

theorem ledger_6_132 : ∀ i ∈ List.range 4, LedgerAt 6 (132+i) := by decide +kernel

theorem ledger_6_136 : ∀ i ∈ List.range 4, LedgerAt 6 (136+i) := by decide +kernel

theorem ledger_6_140 : ∀ i ∈ List.range 4, LedgerAt 6 (140+i) := by decide +kernel

theorem ledger_6 (v : ℕ) (hv : v ∈ List.range 144) : LedgerAt 6 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 6 v)
  have h := (join 0 72 72 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_6_0 ledger_6_4) (join 8 4 4 ledger_6_8 ledger_6_12)) (join 16 8 12 (join 16 4 4 ledger_6_16 ledger_6_20) (join 24 4 8 ledger_6_24 (join 28 4 4 ledger_6_28 ledger_6_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_6_36 ledger_6_40) (join 44 4 4 ledger_6_44 ledger_6_48)) (join 52 8 12 (join 52 4 4 ledger_6_52 ledger_6_56) (join 60 4 8 ledger_6_60 (join 64 4 4 ledger_6_64 ledger_6_68))))) (join 72 36 36 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_6_72 ledger_6_76) (join 80 4 4 ledger_6_80 ledger_6_84)) (join 88 8 12 (join 88 4 4 ledger_6_88 ledger_6_92) (join 96 4 8 ledger_6_96 (join 100 4 4 ledger_6_100 ledger_6_104)))) (join 108 16 20 (join 108 8 8 (join 108 4 4 ledger_6_108 ledger_6_112) (join 116 4 4 ledger_6_116 ledger_6_120)) (join 124 8 12 (join 124 4 4 ledger_6_124 ledger_6_128) (join 132 4 8 ledger_6_132 (join 136 4 4 ledger_6_136 ledger_6_140))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
