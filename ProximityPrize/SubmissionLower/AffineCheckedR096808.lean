import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_9_0 : ∀ i ∈ List.range 4, SingleAt 9 (0+i) := by decide +kernel

theorem single_9_4 : ∀ i ∈ List.range 4, SingleAt 9 (4+i) := by decide +kernel

theorem single_9_8 : ∀ i ∈ List.range 4, SingleAt 9 (8+i) := by decide +kernel

theorem single_9_12 : ∀ i ∈ List.range 4, SingleAt 9 (12+i) := by decide +kernel

theorem single_9_16 : ∀ i ∈ List.range 4, SingleAt 9 (16+i) := by decide +kernel

theorem single_9_20 : ∀ i ∈ List.range 4, SingleAt 9 (20+i) := by decide +kernel

theorem single_9_24 : ∀ i ∈ List.range 4, SingleAt 9 (24+i) := by decide +kernel

theorem single_9_28 : ∀ i ∈ List.range 4, SingleAt 9 (28+i) := by decide +kernel

theorem single_9_32 : ∀ i ∈ List.range 4, SingleAt 9 (32+i) := by decide +kernel

theorem single_9_36 : ∀ i ∈ List.range 4, SingleAt 9 (36+i) := by decide +kernel

theorem single_9_40 : ∀ i ∈ List.range 4, SingleAt 9 (40+i) := by decide +kernel

theorem single_9_44 : ∀ i ∈ List.range 4, SingleAt 9 (44+i) := by decide +kernel

theorem single_9_48 : ∀ i ∈ List.range 4, SingleAt 9 (48+i) := by decide +kernel

theorem single_9_52 : ∀ i ∈ List.range 4, SingleAt 9 (52+i) := by decide +kernel

theorem single_9_56 : ∀ i ∈ List.range 4, SingleAt 9 (56+i) := by decide +kernel

theorem single_9_60 : ∀ i ∈ List.range 4, SingleAt 9 (60+i) := by decide +kernel

theorem single_9_64 : ∀ i ∈ List.range 4, SingleAt 9 (64+i) := by decide +kernel

theorem single_9_68 : ∀ i ∈ List.range 4, SingleAt 9 (68+i) := by decide +kernel

theorem single_9_72 : ∀ i ∈ List.range 4, SingleAt 9 (72+i) := by decide +kernel

theorem single_9_76 : ∀ i ∈ List.range 4, SingleAt 9 (76+i) := by decide +kernel

theorem single_9_80 : ∀ i ∈ List.range 4, SingleAt 9 (80+i) := by decide +kernel

theorem single_9_84 : ∀ i ∈ List.range 4, SingleAt 9 (84+i) := by decide +kernel

theorem single_9_88 : ∀ i ∈ List.range 4, SingleAt 9 (88+i) := by decide +kernel

theorem single_9_92 : ∀ i ∈ List.range 4, SingleAt 9 (92+i) := by decide +kernel

theorem single_9_96 : ∀ i ∈ List.range 4, SingleAt 9 (96+i) := by decide +kernel

theorem single_9_100 : ∀ i ∈ List.range 4, SingleAt 9 (100+i) := by decide +kernel

theorem single_9_104 : ∀ i ∈ List.range 4, SingleAt 9 (104+i) := by decide +kernel

theorem single_9_108 : ∀ i ∈ List.range 4, SingleAt 9 (108+i) := by decide +kernel

theorem single_9_112 : ∀ i ∈ List.range 4, SingleAt 9 (112+i) := by decide +kernel

theorem single_9_116 : ∀ i ∈ List.range 4, SingleAt 9 (116+i) := by decide +kernel

theorem single_9_120 : ∀ i ∈ List.range 4, SingleAt 9 (120+i) := by decide +kernel

theorem single_9_124 : ∀ i ∈ List.range 4, SingleAt 9 (124+i) := by decide +kernel

theorem single_9_128 : ∀ i ∈ List.range 4, SingleAt 9 (128+i) := by decide +kernel

theorem single_9_132 : ∀ i ∈ List.range 4, SingleAt 9 (132+i) := by decide +kernel

theorem single_9_136 : ∀ i ∈ List.range 4, SingleAt 9 (136+i) := by decide +kernel

theorem single_9_140 : ∀ i ∈ List.range 1, SingleAt 9 (140+i) := by decide +kernel

theorem single_9 (v : ℕ) (hv : v ∈ List.range 141) : SingleAt 9 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 9 v)
  have h := (join 0 72 69 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_9_0 single_9_4) (join 8 4 4 single_9_8 single_9_12)) (join 16 8 12 (join 16 4 4 single_9_16 single_9_20) (join 24 4 8 single_9_24 (join 28 4 4 single_9_28 single_9_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_9_36 single_9_40) (join 44 4 4 single_9_44 single_9_48)) (join 52 8 12 (join 52 4 4 single_9_52 single_9_56) (join 60 4 8 single_9_60 (join 64 4 4 single_9_64 single_9_68))))) (join 72 36 33 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_9_72 single_9_76) (join 80 4 4 single_9_80 single_9_84)) (join 88 8 12 (join 88 4 4 single_9_88 single_9_92) (join 96 4 8 single_9_96 (join 100 4 4 single_9_100 single_9_104)))) (join 108 16 17 (join 108 8 8 (join 108 4 4 single_9_108 single_9_112) (join 116 4 4 single_9_116 single_9_120)) (join 124 8 9 (join 124 4 4 single_9_124 single_9_128) (join 132 4 5 single_9_132 (join 136 4 1 single_9_136 single_9_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_9_0 : ∀ i ∈ List.range 4, PhaseAt 9 (0+i) := by decide +kernel

theorem phase_9_4 : ∀ i ∈ List.range 4, PhaseAt 9 (4+i) := by decide +kernel

theorem phase_9_8 : ∀ i ∈ List.range 4, PhaseAt 9 (8+i) := by decide +kernel

theorem phase_9_12 : ∀ i ∈ List.range 4, PhaseAt 9 (12+i) := by decide +kernel

theorem phase_9_16 : ∀ i ∈ List.range 4, PhaseAt 9 (16+i) := by decide +kernel

theorem phase_9_20 : ∀ i ∈ List.range 4, PhaseAt 9 (20+i) := by decide +kernel

theorem phase_9_24 : ∀ i ∈ List.range 4, PhaseAt 9 (24+i) := by decide +kernel

theorem phase_9_28 : ∀ i ∈ List.range 4, PhaseAt 9 (28+i) := by decide +kernel

theorem phase_9_32 : ∀ i ∈ List.range 4, PhaseAt 9 (32+i) := by decide +kernel

theorem phase_9_36 : ∀ i ∈ List.range 4, PhaseAt 9 (36+i) := by decide +kernel

theorem phase_9_40 : ∀ i ∈ List.range 4, PhaseAt 9 (40+i) := by decide +kernel

theorem phase_9_44 : ∀ i ∈ List.range 4, PhaseAt 9 (44+i) := by decide +kernel

theorem phase_9_48 : ∀ i ∈ List.range 4, PhaseAt 9 (48+i) := by decide +kernel

theorem phase_9_52 : ∀ i ∈ List.range 4, PhaseAt 9 (52+i) := by decide +kernel

theorem phase_9_56 : ∀ i ∈ List.range 4, PhaseAt 9 (56+i) := by decide +kernel

theorem phase_9_60 : ∀ i ∈ List.range 4, PhaseAt 9 (60+i) := by decide +kernel

theorem phase_9_64 : ∀ i ∈ List.range 4, PhaseAt 9 (64+i) := by decide +kernel

theorem phase_9_68 : ∀ i ∈ List.range 4, PhaseAt 9 (68+i) := by decide +kernel

theorem phase_9_72 : ∀ i ∈ List.range 4, PhaseAt 9 (72+i) := by decide +kernel

theorem phase_9_76 : ∀ i ∈ List.range 4, PhaseAt 9 (76+i) := by decide +kernel

theorem phase_9_80 : ∀ i ∈ List.range 4, PhaseAt 9 (80+i) := by decide +kernel

theorem phase_9_84 : ∀ i ∈ List.range 4, PhaseAt 9 (84+i) := by decide +kernel

theorem phase_9_88 : ∀ i ∈ List.range 4, PhaseAt 9 (88+i) := by decide +kernel

theorem phase_9_92 : ∀ i ∈ List.range 4, PhaseAt 9 (92+i) := by decide +kernel

theorem phase_9_96 : ∀ i ∈ List.range 4, PhaseAt 9 (96+i) := by decide +kernel

theorem phase_9_100 : ∀ i ∈ List.range 4, PhaseAt 9 (100+i) := by decide +kernel

theorem phase_9_104 : ∀ i ∈ List.range 4, PhaseAt 9 (104+i) := by decide +kernel

theorem phase_9_108 : ∀ i ∈ List.range 4, PhaseAt 9 (108+i) := by decide +kernel

theorem phase_9_112 : ∀ i ∈ List.range 4, PhaseAt 9 (112+i) := by decide +kernel

theorem phase_9_116 : ∀ i ∈ List.range 4, PhaseAt 9 (116+i) := by decide +kernel

theorem phase_9_120 : ∀ i ∈ List.range 4, PhaseAt 9 (120+i) := by decide +kernel

theorem phase_9_124 : ∀ i ∈ List.range 4, PhaseAt 9 (124+i) := by decide +kernel

theorem phase_9_128 : ∀ i ∈ List.range 4, PhaseAt 9 (128+i) := by decide +kernel

theorem phase_9_132 : ∀ i ∈ List.range 4, PhaseAt 9 (132+i) := by decide +kernel

theorem phase_9_136 : ∀ i ∈ List.range 4, PhaseAt 9 (136+i) := by decide +kernel

theorem phase_9_140 : ∀ i ∈ List.range 1, PhaseAt 9 (140+i) := by decide +kernel

theorem phase_9 (v : ℕ) (hv : v ∈ List.range 141) : PhaseAt 9 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 9 v)
  have h := (join 0 72 69 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_9_0 phase_9_4) (join 8 4 4 phase_9_8 phase_9_12)) (join 16 8 12 (join 16 4 4 phase_9_16 phase_9_20) (join 24 4 8 phase_9_24 (join 28 4 4 phase_9_28 phase_9_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_9_36 phase_9_40) (join 44 4 4 phase_9_44 phase_9_48)) (join 52 8 12 (join 52 4 4 phase_9_52 phase_9_56) (join 60 4 8 phase_9_60 (join 64 4 4 phase_9_64 phase_9_68))))) (join 72 36 33 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_9_72 phase_9_76) (join 80 4 4 phase_9_80 phase_9_84)) (join 88 8 12 (join 88 4 4 phase_9_88 phase_9_92) (join 96 4 8 phase_9_96 (join 100 4 4 phase_9_100 phase_9_104)))) (join 108 16 17 (join 108 8 8 (join 108 4 4 phase_9_108 phase_9_112) (join 116 4 4 phase_9_116 phase_9_120)) (join 124 8 9 (join 124 4 4 phase_9_124 phase_9_128) (join 132 4 5 phase_9_132 (join 136 4 1 phase_9_136 phase_9_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_9_0 : ∀ i ∈ List.range 1, ThresholdAt 9 (0+i) := by decide +kernel

theorem threshold_9_1 : ∀ i ∈ List.range 1, ThresholdAt 9 (1+i) := by decide +kernel

theorem threshold_9_2 : ∀ i ∈ List.range 1, ThresholdAt 9 (2+i) := by decide +kernel

theorem threshold_9_3 : ∀ i ∈ List.range 1, ThresholdAt 9 (3+i) := by decide +kernel

theorem threshold_9_4 : ∀ i ∈ List.range 1, ThresholdAt 9 (4+i) := by decide +kernel

theorem threshold_9_5 : ∀ i ∈ List.range 1, ThresholdAt 9 (5+i) := by decide +kernel

theorem threshold_9_6 : ∀ i ∈ List.range 1, ThresholdAt 9 (6+i) := by decide +kernel

theorem threshold_9_7 : ∀ i ∈ List.range 1, ThresholdAt 9 (7+i) := by decide +kernel

theorem threshold_9_8 : ∀ i ∈ List.range 1, ThresholdAt 9 (8+i) := by decide +kernel

theorem threshold_9_9 : ∀ i ∈ List.range 1, ThresholdAt 9 (9+i) := by decide +kernel

theorem threshold_9_10 : ∀ i ∈ List.range 1, ThresholdAt 9 (10+i) := by decide +kernel

theorem threshold_9_11 : ∀ i ∈ List.range 1, ThresholdAt 9 (11+i) := by decide +kernel

theorem threshold_9_12 : ∀ i ∈ List.range 1, ThresholdAt 9 (12+i) := by decide +kernel

theorem threshold_9_13 : ∀ i ∈ List.range 1, ThresholdAt 9 (13+i) := by decide +kernel

theorem threshold_9_14 : ∀ i ∈ List.range 1, ThresholdAt 9 (14+i) := by decide +kernel

theorem threshold_9_15 : ∀ i ∈ List.range 1, ThresholdAt 9 (15+i) := by decide +kernel

theorem threshold_9_16 : ∀ i ∈ List.range 1, ThresholdAt 9 (16+i) := by decide +kernel

theorem threshold_9_17 : ∀ i ∈ List.range 1, ThresholdAt 9 (17+i) := by decide +kernel

theorem threshold_9_18 : ∀ i ∈ List.range 1, ThresholdAt 9 (18+i) := by decide +kernel

theorem threshold_9_19 : ∀ i ∈ List.range 1, ThresholdAt 9 (19+i) := by decide +kernel

theorem threshold_9_20 : ∀ i ∈ List.range 1, ThresholdAt 9 (20+i) := by decide +kernel

theorem threshold_9_21 : ∀ i ∈ List.range 1, ThresholdAt 9 (21+i) := by decide +kernel

theorem threshold_9_22 : ∀ i ∈ List.range 1, ThresholdAt 9 (22+i) := by decide +kernel

theorem threshold_9_23 : ∀ i ∈ List.range 1, ThresholdAt 9 (23+i) := by decide +kernel

theorem threshold_9_24 : ∀ i ∈ List.range 1, ThresholdAt 9 (24+i) := by decide +kernel

theorem threshold_9_25 : ∀ i ∈ List.range 1, ThresholdAt 9 (25+i) := by decide +kernel

theorem threshold_9_26 : ∀ i ∈ List.range 1, ThresholdAt 9 (26+i) := by decide +kernel

theorem threshold_9_27 : ∀ i ∈ List.range 1, ThresholdAt 9 (27+i) := by decide +kernel

theorem threshold_9_28 : ∀ i ∈ List.range 1, ThresholdAt 9 (28+i) := by decide +kernel

theorem threshold_9_29 : ∀ i ∈ List.range 1, ThresholdAt 9 (29+i) := by decide +kernel

theorem threshold_9_30 : ∀ i ∈ List.range 1, ThresholdAt 9 (30+i) := by decide +kernel

theorem threshold_9_31 : ∀ i ∈ List.range 1, ThresholdAt 9 (31+i) := by decide +kernel

theorem threshold_9_32 : ∀ i ∈ List.range 1, ThresholdAt 9 (32+i) := by decide +kernel

theorem threshold_9_33 : ∀ i ∈ List.range 1, ThresholdAt 9 (33+i) := by decide +kernel

theorem threshold_9_34 : ∀ i ∈ List.range 1, ThresholdAt 9 (34+i) := by decide +kernel

theorem threshold_9_35 : ∀ i ∈ List.range 1, ThresholdAt 9 (35+i) := by decide +kernel

theorem threshold_9_36 : ∀ i ∈ List.range 1, ThresholdAt 9 (36+i) := by decide +kernel

theorem threshold_9_37 : ∀ i ∈ List.range 1, ThresholdAt 9 (37+i) := by decide +kernel

theorem threshold_9_38 : ∀ i ∈ List.range 1, ThresholdAt 9 (38+i) := by decide +kernel

theorem threshold_9_39 : ∀ i ∈ List.range 1, ThresholdAt 9 (39+i) := by decide +kernel

theorem threshold_9_40 : ∀ i ∈ List.range 1, ThresholdAt 9 (40+i) := by decide +kernel

theorem threshold_9_41 : ∀ i ∈ List.range 1, ThresholdAt 9 (41+i) := by decide +kernel

theorem threshold_9_42 : ∀ i ∈ List.range 1, ThresholdAt 9 (42+i) := by decide +kernel

theorem threshold_9_43 : ∀ i ∈ List.range 1, ThresholdAt 9 (43+i) := by decide +kernel

theorem threshold_9_44 : ∀ i ∈ List.range 1, ThresholdAt 9 (44+i) := by decide +kernel

theorem threshold_9_45 : ∀ i ∈ List.range 1, ThresholdAt 9 (45+i) := by decide +kernel

theorem threshold_9_46 : ∀ i ∈ List.range 1, ThresholdAt 9 (46+i) := by decide +kernel

theorem threshold_9_47 : ∀ i ∈ List.range 1, ThresholdAt 9 (47+i) := by decide +kernel

theorem threshold_9_48 : ∀ i ∈ List.range 1, ThresholdAt 9 (48+i) := by decide +kernel

theorem threshold_9_49 : ∀ i ∈ List.range 1, ThresholdAt 9 (49+i) := by decide +kernel

theorem threshold_9_50 : ∀ i ∈ List.range 1, ThresholdAt 9 (50+i) := by decide +kernel

theorem threshold_9_51 : ∀ i ∈ List.range 1, ThresholdAt 9 (51+i) := by decide +kernel

theorem threshold_9_52 : ∀ i ∈ List.range 1, ThresholdAt 9 (52+i) := by decide +kernel

theorem threshold_9_53 : ∀ i ∈ List.range 1, ThresholdAt 9 (53+i) := by decide +kernel

theorem threshold_9_54 : ∀ i ∈ List.range 1, ThresholdAt 9 (54+i) := by decide +kernel

theorem threshold_9_55 : ∀ i ∈ List.range 1, ThresholdAt 9 (55+i) := by decide +kernel

theorem threshold_9_56 : ∀ i ∈ List.range 1, ThresholdAt 9 (56+i) := by decide +kernel

theorem threshold_9_57 : ∀ i ∈ List.range 1, ThresholdAt 9 (57+i) := by decide +kernel

theorem threshold_9_58 : ∀ i ∈ List.range 1, ThresholdAt 9 (58+i) := by decide +kernel

theorem threshold_9_59 : ∀ i ∈ List.range 1, ThresholdAt 9 (59+i) := by decide +kernel

theorem threshold_9_60 : ∀ i ∈ List.range 1, ThresholdAt 9 (60+i) := by decide +kernel

theorem threshold_9_61 : ∀ i ∈ List.range 1, ThresholdAt 9 (61+i) := by decide +kernel

theorem threshold_9_62 : ∀ i ∈ List.range 1, ThresholdAt 9 (62+i) := by decide +kernel

theorem threshold_9_63 : ∀ i ∈ List.range 1, ThresholdAt 9 (63+i) := by decide +kernel

theorem threshold_9_64 : ∀ i ∈ List.range 1, ThresholdAt 9 (64+i) := by decide +kernel

theorem threshold_9_65 : ∀ i ∈ List.range 1, ThresholdAt 9 (65+i) := by decide +kernel

theorem threshold_9_66 : ∀ i ∈ List.range 1, ThresholdAt 9 (66+i) := by decide +kernel

theorem threshold_9_67 : ∀ i ∈ List.range 1, ThresholdAt 9 (67+i) := by decide +kernel

theorem threshold_9_68 : ∀ i ∈ List.range 1, ThresholdAt 9 (68+i) := by decide +kernel

theorem threshold_9_69 : ∀ i ∈ List.range 1, ThresholdAt 9 (69+i) := by decide +kernel

theorem threshold_9_70 : ∀ i ∈ List.range 1, ThresholdAt 9 (70+i) := by decide +kernel

theorem threshold_9_71 : ∀ i ∈ List.range 1, ThresholdAt 9 (71+i) := by decide +kernel

theorem threshold_9_72 : ∀ i ∈ List.range 1, ThresholdAt 9 (72+i) := by decide +kernel

theorem threshold_9_73 : ∀ i ∈ List.range 1, ThresholdAt 9 (73+i) := by decide +kernel

theorem threshold_9_74 : ∀ i ∈ List.range 1, ThresholdAt 9 (74+i) := by decide +kernel

theorem threshold_9_75 : ∀ i ∈ List.range 1, ThresholdAt 9 (75+i) := by decide +kernel

theorem threshold_9_76 : ∀ i ∈ List.range 1, ThresholdAt 9 (76+i) := by decide +kernel

theorem threshold_9_77 : ∀ i ∈ List.range 1, ThresholdAt 9 (77+i) := by decide +kernel

theorem threshold_9_78 : ∀ i ∈ List.range 1, ThresholdAt 9 (78+i) := by decide +kernel

theorem threshold_9_79 : ∀ i ∈ List.range 1, ThresholdAt 9 (79+i) := by decide +kernel

theorem threshold_9_80 : ∀ i ∈ List.range 1, ThresholdAt 9 (80+i) := by decide +kernel

theorem threshold_9_81 : ∀ i ∈ List.range 1, ThresholdAt 9 (81+i) := by decide +kernel

theorem threshold_9_82 : ∀ i ∈ List.range 1, ThresholdAt 9 (82+i) := by decide +kernel

theorem threshold_9_83 : ∀ i ∈ List.range 1, ThresholdAt 9 (83+i) := by decide +kernel

theorem threshold_9_84 : ∀ i ∈ List.range 1, ThresholdAt 9 (84+i) := by decide +kernel

theorem threshold_9_85 : ∀ i ∈ List.range 1, ThresholdAt 9 (85+i) := by decide +kernel

theorem threshold_9_86 : ∀ i ∈ List.range 1, ThresholdAt 9 (86+i) := by decide +kernel

theorem threshold_9_87 : ∀ i ∈ List.range 1, ThresholdAt 9 (87+i) := by decide +kernel

theorem threshold_9_88 : ∀ i ∈ List.range 1, ThresholdAt 9 (88+i) := by decide +kernel

theorem threshold_9_89 : ∀ i ∈ List.range 1, ThresholdAt 9 (89+i) := by decide +kernel

theorem threshold_9_90 : ∀ i ∈ List.range 1, ThresholdAt 9 (90+i) := by decide +kernel

theorem threshold_9_91 : ∀ i ∈ List.range 1, ThresholdAt 9 (91+i) := by decide +kernel

theorem threshold_9_92 : ∀ i ∈ List.range 1, ThresholdAt 9 (92+i) := by decide +kernel

theorem threshold_9_93 : ∀ i ∈ List.range 1, ThresholdAt 9 (93+i) := by decide +kernel

theorem threshold_9_94 : ∀ i ∈ List.range 1, ThresholdAt 9 (94+i) := by decide +kernel

theorem threshold_9_95 : ∀ i ∈ List.range 1, ThresholdAt 9 (95+i) := by decide +kernel

theorem threshold_9_96 : ∀ i ∈ List.range 1, ThresholdAt 9 (96+i) := by decide +kernel

theorem threshold_9_97 : ∀ i ∈ List.range 1, ThresholdAt 9 (97+i) := by decide +kernel

theorem threshold_9_98 : ∀ i ∈ List.range 1, ThresholdAt 9 (98+i) := by decide +kernel

theorem threshold_9_99 : ∀ i ∈ List.range 1, ThresholdAt 9 (99+i) := by decide +kernel

theorem threshold_9_100 : ∀ i ∈ List.range 1, ThresholdAt 9 (100+i) := by decide +kernel

theorem threshold_9_101 : ∀ i ∈ List.range 1, ThresholdAt 9 (101+i) := by decide +kernel

theorem threshold_9_102 : ∀ i ∈ List.range 1, ThresholdAt 9 (102+i) := by decide +kernel

theorem threshold_9_103 : ∀ i ∈ List.range 1, ThresholdAt 9 (103+i) := by decide +kernel

theorem threshold_9_104 : ∀ i ∈ List.range 1, ThresholdAt 9 (104+i) := by decide +kernel

theorem threshold_9_105 : ∀ i ∈ List.range 1, ThresholdAt 9 (105+i) := by decide +kernel

theorem threshold_9_106 : ∀ i ∈ List.range 1, ThresholdAt 9 (106+i) := by decide +kernel

theorem threshold_9_107 : ∀ i ∈ List.range 1, ThresholdAt 9 (107+i) := by decide +kernel

theorem threshold_9_108 : ∀ i ∈ List.range 1, ThresholdAt 9 (108+i) := by decide +kernel

theorem threshold_9_109 : ∀ i ∈ List.range 1, ThresholdAt 9 (109+i) := by decide +kernel

theorem threshold_9_110 : ∀ i ∈ List.range 1, ThresholdAt 9 (110+i) := by decide +kernel

theorem threshold_9_111 : ∀ i ∈ List.range 1, ThresholdAt 9 (111+i) := by decide +kernel

theorem threshold_9_112 : ∀ i ∈ List.range 1, ThresholdAt 9 (112+i) := by decide +kernel

theorem threshold_9_113 : ∀ i ∈ List.range 1, ThresholdAt 9 (113+i) := by decide +kernel

theorem threshold_9_114 : ∀ i ∈ List.range 1, ThresholdAt 9 (114+i) := by decide +kernel

theorem threshold_9_115 : ∀ i ∈ List.range 1, ThresholdAt 9 (115+i) := by decide +kernel

theorem threshold_9_116 : ∀ i ∈ List.range 1, ThresholdAt 9 (116+i) := by decide +kernel

theorem threshold_9_117 : ∀ i ∈ List.range 1, ThresholdAt 9 (117+i) := by decide +kernel

theorem threshold_9_118 : ∀ i ∈ List.range 1, ThresholdAt 9 (118+i) := by decide +kernel

theorem threshold_9_119 : ∀ i ∈ List.range 1, ThresholdAt 9 (119+i) := by decide +kernel

theorem threshold_9_120 : ∀ i ∈ List.range 1, ThresholdAt 9 (120+i) := by decide +kernel

theorem threshold_9_121 : ∀ i ∈ List.range 1, ThresholdAt 9 (121+i) := by decide +kernel

theorem threshold_9_122 : ∀ i ∈ List.range 1, ThresholdAt 9 (122+i) := by decide +kernel

theorem threshold_9_123 : ∀ i ∈ List.range 1, ThresholdAt 9 (123+i) := by decide +kernel

theorem threshold_9_124 : ∀ i ∈ List.range 1, ThresholdAt 9 (124+i) := by decide +kernel

theorem threshold_9_125 : ∀ i ∈ List.range 1, ThresholdAt 9 (125+i) := by decide +kernel

theorem threshold_9_126 : ∀ i ∈ List.range 1, ThresholdAt 9 (126+i) := by decide +kernel

theorem threshold_9_127 : ∀ i ∈ List.range 1, ThresholdAt 9 (127+i) := by decide +kernel

theorem threshold_9_128 : ∀ i ∈ List.range 1, ThresholdAt 9 (128+i) := by decide +kernel

theorem threshold_9_129 : ∀ i ∈ List.range 1, ThresholdAt 9 (129+i) := by decide +kernel

theorem threshold_9_130 : ∀ i ∈ List.range 1, ThresholdAt 9 (130+i) := by decide +kernel

theorem threshold_9_131 : ∀ i ∈ List.range 1, ThresholdAt 9 (131+i) := by decide +kernel

theorem threshold_9_132 : ∀ i ∈ List.range 1, ThresholdAt 9 (132+i) := by decide +kernel

theorem threshold_9_133 : ∀ i ∈ List.range 1, ThresholdAt 9 (133+i) := by decide +kernel

theorem threshold_9_134 : ∀ i ∈ List.range 1, ThresholdAt 9 (134+i) := by decide +kernel

theorem threshold_9_135 : ∀ i ∈ List.range 1, ThresholdAt 9 (135+i) := by decide +kernel

theorem threshold_9_136 : ∀ i ∈ List.range 1, ThresholdAt 9 (136+i) := by decide +kernel

theorem threshold_9_137 : ∀ i ∈ List.range 1, ThresholdAt 9 (137+i) := by decide +kernel

theorem threshold_9_138 : ∀ i ∈ List.range 1, ThresholdAt 9 (138+i) := by decide +kernel

theorem threshold_9_139 : ∀ i ∈ List.range 1, ThresholdAt 9 (139+i) := by decide +kernel

theorem threshold_9_140 : ∀ i ∈ List.range 1, ThresholdAt 9 (140+i) := by decide +kernel

theorem threshold_9 (v : ℕ) (hv : v ∈ List.range 141) : ThresholdAt 9 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 9 v)
  have h := (join 0 70 71 (join 0 35 35 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_9_0 threshold_9_1) (join 2 1 1 threshold_9_2 threshold_9_3)) (join 4 2 2 (join 4 1 1 threshold_9_4 threshold_9_5) (join 6 1 1 threshold_9_6 threshold_9_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_9_8 threshold_9_9) (join 10 1 1 threshold_9_10 threshold_9_11)) (join 12 2 3 (join 12 1 1 threshold_9_12 threshold_9_13) (join 14 1 2 threshold_9_14 (join 15 1 1 threshold_9_15 threshold_9_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 threshold_9_17 threshold_9_18) (join 19 1 1 threshold_9_19 threshold_9_20)) (join 21 2 3 (join 21 1 1 threshold_9_21 threshold_9_22) (join 23 1 2 threshold_9_23 (join 24 1 1 threshold_9_24 threshold_9_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 threshold_9_26 threshold_9_27) (join 28 1 1 threshold_9_28 threshold_9_29)) (join 30 2 3 (join 30 1 1 threshold_9_30 threshold_9_31) (join 32 1 2 threshold_9_32 (join 33 1 1 threshold_9_33 threshold_9_34)))))) (join 35 17 18 (join 35 8 9 (join 35 4 4 (join 35 2 2 (join 35 1 1 threshold_9_35 threshold_9_36) (join 37 1 1 threshold_9_37 threshold_9_38)) (join 39 2 2 (join 39 1 1 threshold_9_39 threshold_9_40) (join 41 1 1 threshold_9_41 threshold_9_42))) (join 43 4 5 (join 43 2 2 (join 43 1 1 threshold_9_43 threshold_9_44) (join 45 1 1 threshold_9_45 threshold_9_46)) (join 47 2 3 (join 47 1 1 threshold_9_47 threshold_9_48) (join 49 1 2 threshold_9_49 (join 50 1 1 threshold_9_50 threshold_9_51))))) (join 52 9 9 (join 52 4 5 (join 52 2 2 (join 52 1 1 threshold_9_52 threshold_9_53) (join 54 1 1 threshold_9_54 threshold_9_55)) (join 56 2 3 (join 56 1 1 threshold_9_56 threshold_9_57) (join 58 1 2 threshold_9_58 (join 59 1 1 threshold_9_59 threshold_9_60)))) (join 61 4 5 (join 61 2 2 (join 61 1 1 threshold_9_61 threshold_9_62) (join 63 1 1 threshold_9_63 threshold_9_64)) (join 65 2 3 (join 65 1 1 threshold_9_65 threshold_9_66) (join 67 1 2 threshold_9_67 (join 68 1 1 threshold_9_68 threshold_9_69))))))) (join 70 35 36 (join 70 17 18 (join 70 8 9 (join 70 4 4 (join 70 2 2 (join 70 1 1 threshold_9_70 threshold_9_71) (join 72 1 1 threshold_9_72 threshold_9_73)) (join 74 2 2 (join 74 1 1 threshold_9_74 threshold_9_75) (join 76 1 1 threshold_9_76 threshold_9_77))) (join 78 4 5 (join 78 2 2 (join 78 1 1 threshold_9_78 threshold_9_79) (join 80 1 1 threshold_9_80 threshold_9_81)) (join 82 2 3 (join 82 1 1 threshold_9_82 threshold_9_83) (join 84 1 2 threshold_9_84 (join 85 1 1 threshold_9_85 threshold_9_86))))) (join 87 9 9 (join 87 4 5 (join 87 2 2 (join 87 1 1 threshold_9_87 threshold_9_88) (join 89 1 1 threshold_9_89 threshold_9_90)) (join 91 2 3 (join 91 1 1 threshold_9_91 threshold_9_92) (join 93 1 2 threshold_9_93 (join 94 1 1 threshold_9_94 threshold_9_95)))) (join 96 4 5 (join 96 2 2 (join 96 1 1 threshold_9_96 threshold_9_97) (join 98 1 1 threshold_9_98 threshold_9_99)) (join 100 2 3 (join 100 1 1 threshold_9_100 threshold_9_101) (join 102 1 2 threshold_9_102 (join 103 1 1 threshold_9_103 threshold_9_104)))))) (join 105 18 18 (join 105 9 9 (join 105 4 5 (join 105 2 2 (join 105 1 1 threshold_9_105 threshold_9_106) (join 107 1 1 threshold_9_107 threshold_9_108)) (join 109 2 3 (join 109 1 1 threshold_9_109 threshold_9_110) (join 111 1 2 threshold_9_111 (join 112 1 1 threshold_9_112 threshold_9_113)))) (join 114 4 5 (join 114 2 2 (join 114 1 1 threshold_9_114 threshold_9_115) (join 116 1 1 threshold_9_116 threshold_9_117)) (join 118 2 3 (join 118 1 1 threshold_9_118 threshold_9_119) (join 120 1 2 threshold_9_120 (join 121 1 1 threshold_9_121 threshold_9_122))))) (join 123 9 9 (join 123 4 5 (join 123 2 2 (join 123 1 1 threshold_9_123 threshold_9_124) (join 125 1 1 threshold_9_125 threshold_9_126)) (join 127 2 3 (join 127 1 1 threshold_9_127 threshold_9_128) (join 129 1 2 threshold_9_129 (join 130 1 1 threshold_9_130 threshold_9_131)))) (join 132 4 5 (join 132 2 2 (join 132 1 1 threshold_9_132 threshold_9_133) (join 134 1 1 threshold_9_134 threshold_9_135)) (join 136 2 3 (join 136 1 1 threshold_9_136 threshold_9_137) (join 138 1 2 threshold_9_138 (join 139 1 1 threshold_9_139 threshold_9_140))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_9_0 : ∀ i ∈ List.range 4, LedgerAt 9 (0+i) := by decide +kernel

theorem ledger_9_4 : ∀ i ∈ List.range 4, LedgerAt 9 (4+i) := by decide +kernel

theorem ledger_9_8 : ∀ i ∈ List.range 4, LedgerAt 9 (8+i) := by decide +kernel

theorem ledger_9_12 : ∀ i ∈ List.range 4, LedgerAt 9 (12+i) := by decide +kernel

theorem ledger_9_16 : ∀ i ∈ List.range 4, LedgerAt 9 (16+i) := by decide +kernel

theorem ledger_9_20 : ∀ i ∈ List.range 4, LedgerAt 9 (20+i) := by decide +kernel

theorem ledger_9_24 : ∀ i ∈ List.range 4, LedgerAt 9 (24+i) := by decide +kernel

theorem ledger_9_28 : ∀ i ∈ List.range 4, LedgerAt 9 (28+i) := by decide +kernel

theorem ledger_9_32 : ∀ i ∈ List.range 4, LedgerAt 9 (32+i) := by decide +kernel

theorem ledger_9_36 : ∀ i ∈ List.range 4, LedgerAt 9 (36+i) := by decide +kernel

theorem ledger_9_40 : ∀ i ∈ List.range 4, LedgerAt 9 (40+i) := by decide +kernel

theorem ledger_9_44 : ∀ i ∈ List.range 4, LedgerAt 9 (44+i) := by decide +kernel

theorem ledger_9_48 : ∀ i ∈ List.range 4, LedgerAt 9 (48+i) := by decide +kernel

theorem ledger_9_52 : ∀ i ∈ List.range 4, LedgerAt 9 (52+i) := by decide +kernel

theorem ledger_9_56 : ∀ i ∈ List.range 4, LedgerAt 9 (56+i) := by decide +kernel

theorem ledger_9_60 : ∀ i ∈ List.range 4, LedgerAt 9 (60+i) := by decide +kernel

theorem ledger_9_64 : ∀ i ∈ List.range 4, LedgerAt 9 (64+i) := by decide +kernel

theorem ledger_9_68 : ∀ i ∈ List.range 4, LedgerAt 9 (68+i) := by decide +kernel

theorem ledger_9_72 : ∀ i ∈ List.range 4, LedgerAt 9 (72+i) := by decide +kernel

theorem ledger_9_76 : ∀ i ∈ List.range 4, LedgerAt 9 (76+i) := by decide +kernel

theorem ledger_9_80 : ∀ i ∈ List.range 4, LedgerAt 9 (80+i) := by decide +kernel

theorem ledger_9_84 : ∀ i ∈ List.range 4, LedgerAt 9 (84+i) := by decide +kernel

theorem ledger_9_88 : ∀ i ∈ List.range 4, LedgerAt 9 (88+i) := by decide +kernel

theorem ledger_9_92 : ∀ i ∈ List.range 4, LedgerAt 9 (92+i) := by decide +kernel

theorem ledger_9_96 : ∀ i ∈ List.range 4, LedgerAt 9 (96+i) := by decide +kernel

theorem ledger_9_100 : ∀ i ∈ List.range 4, LedgerAt 9 (100+i) := by decide +kernel

theorem ledger_9_104 : ∀ i ∈ List.range 4, LedgerAt 9 (104+i) := by decide +kernel

theorem ledger_9_108 : ∀ i ∈ List.range 4, LedgerAt 9 (108+i) := by decide +kernel

theorem ledger_9_112 : ∀ i ∈ List.range 4, LedgerAt 9 (112+i) := by decide +kernel

theorem ledger_9_116 : ∀ i ∈ List.range 4, LedgerAt 9 (116+i) := by decide +kernel

theorem ledger_9_120 : ∀ i ∈ List.range 4, LedgerAt 9 (120+i) := by decide +kernel

theorem ledger_9_124 : ∀ i ∈ List.range 4, LedgerAt 9 (124+i) := by decide +kernel

theorem ledger_9_128 : ∀ i ∈ List.range 4, LedgerAt 9 (128+i) := by decide +kernel

theorem ledger_9_132 : ∀ i ∈ List.range 4, LedgerAt 9 (132+i) := by decide +kernel

theorem ledger_9_136 : ∀ i ∈ List.range 4, LedgerAt 9 (136+i) := by decide +kernel

theorem ledger_9_140 : ∀ i ∈ List.range 1, LedgerAt 9 (140+i) := by decide +kernel

theorem ledger_9 (v : ℕ) (hv : v ∈ List.range 141) : LedgerAt 9 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 9 v)
  have h := (join 0 72 69 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_9_0 ledger_9_4) (join 8 4 4 ledger_9_8 ledger_9_12)) (join 16 8 12 (join 16 4 4 ledger_9_16 ledger_9_20) (join 24 4 8 ledger_9_24 (join 28 4 4 ledger_9_28 ledger_9_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_9_36 ledger_9_40) (join 44 4 4 ledger_9_44 ledger_9_48)) (join 52 8 12 (join 52 4 4 ledger_9_52 ledger_9_56) (join 60 4 8 ledger_9_60 (join 64 4 4 ledger_9_64 ledger_9_68))))) (join 72 36 33 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_9_72 ledger_9_76) (join 80 4 4 ledger_9_80 ledger_9_84)) (join 88 8 12 (join 88 4 4 ledger_9_88 ledger_9_92) (join 96 4 8 ledger_9_96 (join 100 4 4 ledger_9_100 ledger_9_104)))) (join 108 16 17 (join 108 8 8 (join 108 4 4 ledger_9_108 ledger_9_112) (join 116 4 4 ledger_9_116 ledger_9_120)) (join 124 8 9 (join 124 4 4 ledger_9_124 ledger_9_128) (join 132 4 5 ledger_9_132 (join 136 4 1 ledger_9_136 ledger_9_140))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
