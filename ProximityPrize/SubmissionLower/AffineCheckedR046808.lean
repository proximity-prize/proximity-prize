import ProximityPrize.SubmissionLower.AffineCheckedR036808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_4_0 : ∀ i ∈ List.range 4, SingleAt 4 (0+i) := by decide +kernel

theorem single_4_4 : ∀ i ∈ List.range 4, SingleAt 4 (4+i) := by decide +kernel

theorem single_4_8 : ∀ i ∈ List.range 4, SingleAt 4 (8+i) := by decide +kernel

theorem single_4_12 : ∀ i ∈ List.range 4, SingleAt 4 (12+i) := by decide +kernel

theorem single_4_16 : ∀ i ∈ List.range 4, SingleAt 4 (16+i) := by decide +kernel

theorem single_4_20 : ∀ i ∈ List.range 4, SingleAt 4 (20+i) := by decide +kernel

theorem single_4_24 : ∀ i ∈ List.range 4, SingleAt 4 (24+i) := by decide +kernel

theorem single_4_28 : ∀ i ∈ List.range 4, SingleAt 4 (28+i) := by decide +kernel

theorem single_4_32 : ∀ i ∈ List.range 4, SingleAt 4 (32+i) := by decide +kernel

theorem single_4_36 : ∀ i ∈ List.range 4, SingleAt 4 (36+i) := by decide +kernel

theorem single_4_40 : ∀ i ∈ List.range 4, SingleAt 4 (40+i) := by decide +kernel

theorem single_4_44 : ∀ i ∈ List.range 4, SingleAt 4 (44+i) := by decide +kernel

theorem single_4_48 : ∀ i ∈ List.range 4, SingleAt 4 (48+i) := by decide +kernel

theorem single_4_52 : ∀ i ∈ List.range 4, SingleAt 4 (52+i) := by decide +kernel

theorem single_4_56 : ∀ i ∈ List.range 4, SingleAt 4 (56+i) := by decide +kernel

theorem single_4_60 : ∀ i ∈ List.range 4, SingleAt 4 (60+i) := by decide +kernel

theorem single_4_64 : ∀ i ∈ List.range 4, SingleAt 4 (64+i) := by decide +kernel

theorem single_4_68 : ∀ i ∈ List.range 4, SingleAt 4 (68+i) := by decide +kernel

theorem single_4_72 : ∀ i ∈ List.range 4, SingleAt 4 (72+i) := by decide +kernel

theorem single_4_76 : ∀ i ∈ List.range 4, SingleAt 4 (76+i) := by decide +kernel

theorem single_4_80 : ∀ i ∈ List.range 4, SingleAt 4 (80+i) := by decide +kernel

theorem single_4_84 : ∀ i ∈ List.range 4, SingleAt 4 (84+i) := by decide +kernel

theorem single_4_88 : ∀ i ∈ List.range 4, SingleAt 4 (88+i) := by decide +kernel

theorem single_4_92 : ∀ i ∈ List.range 4, SingleAt 4 (92+i) := by decide +kernel

theorem single_4_96 : ∀ i ∈ List.range 4, SingleAt 4 (96+i) := by decide +kernel

theorem single_4_100 : ∀ i ∈ List.range 4, SingleAt 4 (100+i) := by decide +kernel

theorem single_4_104 : ∀ i ∈ List.range 4, SingleAt 4 (104+i) := by decide +kernel

theorem single_4_108 : ∀ i ∈ List.range 4, SingleAt 4 (108+i) := by decide +kernel

theorem single_4_112 : ∀ i ∈ List.range 4, SingleAt 4 (112+i) := by decide +kernel

theorem single_4_116 : ∀ i ∈ List.range 4, SingleAt 4 (116+i) := by decide +kernel

theorem single_4_120 : ∀ i ∈ List.range 4, SingleAt 4 (120+i) := by decide +kernel

theorem single_4_124 : ∀ i ∈ List.range 4, SingleAt 4 (124+i) := by decide +kernel

theorem single_4_128 : ∀ i ∈ List.range 4, SingleAt 4 (128+i) := by decide +kernel

theorem single_4_132 : ∀ i ∈ List.range 4, SingleAt 4 (132+i) := by decide +kernel

theorem single_4_136 : ∀ i ∈ List.range 4, SingleAt 4 (136+i) := by decide +kernel

theorem single_4_140 : ∀ i ∈ List.range 4, SingleAt 4 (140+i) := by decide +kernel

theorem single_4_144 : ∀ i ∈ List.range 2, SingleAt 4 (144+i) := by decide +kernel

theorem single_4 (v : ℕ) (hv : v ∈ List.range 146) : SingleAt 4 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 4 v)
  have h := (join 0 72 74 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_4_0 single_4_4) (join 8 4 4 single_4_8 single_4_12)) (join 16 8 12 (join 16 4 4 single_4_16 single_4_20) (join 24 4 8 single_4_24 (join 28 4 4 single_4_28 single_4_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_4_36 single_4_40) (join 44 4 4 single_4_44 single_4_48)) (join 52 8 12 (join 52 4 4 single_4_52 single_4_56) (join 60 4 8 single_4_60 (join 64 4 4 single_4_64 single_4_68))))) (join 72 36 38 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_4_72 single_4_76) (join 80 4 4 single_4_80 single_4_84)) (join 88 8 12 (join 88 4 4 single_4_88 single_4_92) (join 96 4 8 single_4_96 (join 100 4 4 single_4_100 single_4_104)))) (join 108 20 18 (join 108 8 12 (join 108 4 4 single_4_108 single_4_112) (join 116 4 8 single_4_116 (join 120 4 4 single_4_120 single_4_124))) (join 128 8 10 (join 128 4 4 single_4_128 single_4_132) (join 136 4 6 single_4_136 (join 140 4 2 single_4_140 single_4_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_4_0 : ∀ i ∈ List.range 4, PhaseAt 4 (0+i) := by decide +kernel

theorem phase_4_4 : ∀ i ∈ List.range 4, PhaseAt 4 (4+i) := by decide +kernel

theorem phase_4_8 : ∀ i ∈ List.range 4, PhaseAt 4 (8+i) := by decide +kernel

theorem phase_4_12 : ∀ i ∈ List.range 4, PhaseAt 4 (12+i) := by decide +kernel

theorem phase_4_16 : ∀ i ∈ List.range 4, PhaseAt 4 (16+i) := by decide +kernel

theorem phase_4_20 : ∀ i ∈ List.range 4, PhaseAt 4 (20+i) := by decide +kernel

theorem phase_4_24 : ∀ i ∈ List.range 4, PhaseAt 4 (24+i) := by decide +kernel

theorem phase_4_28 : ∀ i ∈ List.range 4, PhaseAt 4 (28+i) := by decide +kernel

theorem phase_4_32 : ∀ i ∈ List.range 4, PhaseAt 4 (32+i) := by decide +kernel

theorem phase_4_36 : ∀ i ∈ List.range 4, PhaseAt 4 (36+i) := by decide +kernel

theorem phase_4_40 : ∀ i ∈ List.range 4, PhaseAt 4 (40+i) := by decide +kernel

theorem phase_4_44 : ∀ i ∈ List.range 4, PhaseAt 4 (44+i) := by decide +kernel

theorem phase_4_48 : ∀ i ∈ List.range 4, PhaseAt 4 (48+i) := by decide +kernel

theorem phase_4_52 : ∀ i ∈ List.range 4, PhaseAt 4 (52+i) := by decide +kernel

theorem phase_4_56 : ∀ i ∈ List.range 4, PhaseAt 4 (56+i) := by decide +kernel

theorem phase_4_60 : ∀ i ∈ List.range 4, PhaseAt 4 (60+i) := by decide +kernel

theorem phase_4_64 : ∀ i ∈ List.range 4, PhaseAt 4 (64+i) := by decide +kernel

theorem phase_4_68 : ∀ i ∈ List.range 4, PhaseAt 4 (68+i) := by decide +kernel

theorem phase_4_72 : ∀ i ∈ List.range 4, PhaseAt 4 (72+i) := by decide +kernel

theorem phase_4_76 : ∀ i ∈ List.range 4, PhaseAt 4 (76+i) := by decide +kernel

theorem phase_4_80 : ∀ i ∈ List.range 4, PhaseAt 4 (80+i) := by decide +kernel

theorem phase_4_84 : ∀ i ∈ List.range 4, PhaseAt 4 (84+i) := by decide +kernel

theorem phase_4_88 : ∀ i ∈ List.range 4, PhaseAt 4 (88+i) := by decide +kernel

theorem phase_4_92 : ∀ i ∈ List.range 4, PhaseAt 4 (92+i) := by decide +kernel

theorem phase_4_96 : ∀ i ∈ List.range 4, PhaseAt 4 (96+i) := by decide +kernel

theorem phase_4_100 : ∀ i ∈ List.range 4, PhaseAt 4 (100+i) := by decide +kernel

theorem phase_4_104 : ∀ i ∈ List.range 4, PhaseAt 4 (104+i) := by decide +kernel

theorem phase_4_108 : ∀ i ∈ List.range 4, PhaseAt 4 (108+i) := by decide +kernel

theorem phase_4_112 : ∀ i ∈ List.range 4, PhaseAt 4 (112+i) := by decide +kernel

theorem phase_4_116 : ∀ i ∈ List.range 4, PhaseAt 4 (116+i) := by decide +kernel

theorem phase_4_120 : ∀ i ∈ List.range 4, PhaseAt 4 (120+i) := by decide +kernel

theorem phase_4_124 : ∀ i ∈ List.range 4, PhaseAt 4 (124+i) := by decide +kernel

theorem phase_4_128 : ∀ i ∈ List.range 4, PhaseAt 4 (128+i) := by decide +kernel

theorem phase_4_132 : ∀ i ∈ List.range 4, PhaseAt 4 (132+i) := by decide +kernel

theorem phase_4_136 : ∀ i ∈ List.range 4, PhaseAt 4 (136+i) := by decide +kernel

theorem phase_4_140 : ∀ i ∈ List.range 4, PhaseAt 4 (140+i) := by decide +kernel

theorem phase_4_144 : ∀ i ∈ List.range 2, PhaseAt 4 (144+i) := by decide +kernel

theorem phase_4 (v : ℕ) (hv : v ∈ List.range 146) : PhaseAt 4 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 4 v)
  have h := (join 0 72 74 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_4_0 phase_4_4) (join 8 4 4 phase_4_8 phase_4_12)) (join 16 8 12 (join 16 4 4 phase_4_16 phase_4_20) (join 24 4 8 phase_4_24 (join 28 4 4 phase_4_28 phase_4_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_4_36 phase_4_40) (join 44 4 4 phase_4_44 phase_4_48)) (join 52 8 12 (join 52 4 4 phase_4_52 phase_4_56) (join 60 4 8 phase_4_60 (join 64 4 4 phase_4_64 phase_4_68))))) (join 72 36 38 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_4_72 phase_4_76) (join 80 4 4 phase_4_80 phase_4_84)) (join 88 8 12 (join 88 4 4 phase_4_88 phase_4_92) (join 96 4 8 phase_4_96 (join 100 4 4 phase_4_100 phase_4_104)))) (join 108 20 18 (join 108 8 12 (join 108 4 4 phase_4_108 phase_4_112) (join 116 4 8 phase_4_116 (join 120 4 4 phase_4_120 phase_4_124))) (join 128 8 10 (join 128 4 4 phase_4_128 phase_4_132) (join 136 4 6 phase_4_136 (join 140 4 2 phase_4_140 phase_4_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_4_0 : ∀ i ∈ List.range 1, ThresholdAt 4 (0+i) := by decide +kernel

theorem threshold_4_1 : ∀ i ∈ List.range 1, ThresholdAt 4 (1+i) := by decide +kernel

theorem threshold_4_2 : ∀ i ∈ List.range 1, ThresholdAt 4 (2+i) := by decide +kernel

theorem threshold_4_3 : ∀ i ∈ List.range 1, ThresholdAt 4 (3+i) := by decide +kernel

theorem threshold_4_4 : ∀ i ∈ List.range 1, ThresholdAt 4 (4+i) := by decide +kernel

theorem threshold_4_5 : ∀ i ∈ List.range 1, ThresholdAt 4 (5+i) := by decide +kernel

theorem threshold_4_6 : ∀ i ∈ List.range 1, ThresholdAt 4 (6+i) := by decide +kernel

theorem threshold_4_7 : ∀ i ∈ List.range 1, ThresholdAt 4 (7+i) := by decide +kernel

theorem threshold_4_8 : ∀ i ∈ List.range 1, ThresholdAt 4 (8+i) := by decide +kernel

theorem threshold_4_9 : ∀ i ∈ List.range 1, ThresholdAt 4 (9+i) := by decide +kernel

theorem threshold_4_10 : ∀ i ∈ List.range 1, ThresholdAt 4 (10+i) := by decide +kernel

theorem threshold_4_11 : ∀ i ∈ List.range 1, ThresholdAt 4 (11+i) := by decide +kernel

theorem threshold_4_12 : ∀ i ∈ List.range 1, ThresholdAt 4 (12+i) := by decide +kernel

theorem threshold_4_13 : ∀ i ∈ List.range 1, ThresholdAt 4 (13+i) := by decide +kernel

theorem threshold_4_14 : ∀ i ∈ List.range 1, ThresholdAt 4 (14+i) := by decide +kernel

theorem threshold_4_15 : ∀ i ∈ List.range 1, ThresholdAt 4 (15+i) := by decide +kernel

theorem threshold_4_16 : ∀ i ∈ List.range 1, ThresholdAt 4 (16+i) := by decide +kernel

theorem threshold_4_17 : ∀ i ∈ List.range 1, ThresholdAt 4 (17+i) := by decide +kernel

theorem threshold_4_18 : ∀ i ∈ List.range 1, ThresholdAt 4 (18+i) := by decide +kernel

theorem threshold_4_19 : ∀ i ∈ List.range 1, ThresholdAt 4 (19+i) := by decide +kernel

theorem threshold_4_20 : ∀ i ∈ List.range 1, ThresholdAt 4 (20+i) := by decide +kernel

theorem threshold_4_21 : ∀ i ∈ List.range 1, ThresholdAt 4 (21+i) := by decide +kernel

theorem threshold_4_22 : ∀ i ∈ List.range 1, ThresholdAt 4 (22+i) := by decide +kernel

theorem threshold_4_23 : ∀ i ∈ List.range 1, ThresholdAt 4 (23+i) := by decide +kernel

theorem threshold_4_24 : ∀ i ∈ List.range 1, ThresholdAt 4 (24+i) := by decide +kernel

theorem threshold_4_25 : ∀ i ∈ List.range 1, ThresholdAt 4 (25+i) := by decide +kernel

theorem threshold_4_26 : ∀ i ∈ List.range 1, ThresholdAt 4 (26+i) := by decide +kernel

theorem threshold_4_27 : ∀ i ∈ List.range 1, ThresholdAt 4 (27+i) := by decide +kernel

theorem threshold_4_28 : ∀ i ∈ List.range 1, ThresholdAt 4 (28+i) := by decide +kernel

theorem threshold_4_29 : ∀ i ∈ List.range 1, ThresholdAt 4 (29+i) := by decide +kernel

theorem threshold_4_30 : ∀ i ∈ List.range 1, ThresholdAt 4 (30+i) := by decide +kernel

theorem threshold_4_31 : ∀ i ∈ List.range 1, ThresholdAt 4 (31+i) := by decide +kernel

theorem threshold_4_32 : ∀ i ∈ List.range 1, ThresholdAt 4 (32+i) := by decide +kernel

theorem threshold_4_33 : ∀ i ∈ List.range 1, ThresholdAt 4 (33+i) := by decide +kernel

theorem threshold_4_34 : ∀ i ∈ List.range 1, ThresholdAt 4 (34+i) := by decide +kernel

theorem threshold_4_35 : ∀ i ∈ List.range 1, ThresholdAt 4 (35+i) := by decide +kernel

theorem threshold_4_36 : ∀ i ∈ List.range 1, ThresholdAt 4 (36+i) := by decide +kernel

theorem threshold_4_37 : ∀ i ∈ List.range 1, ThresholdAt 4 (37+i) := by decide +kernel

theorem threshold_4_38 : ∀ i ∈ List.range 1, ThresholdAt 4 (38+i) := by decide +kernel

theorem threshold_4_39 : ∀ i ∈ List.range 1, ThresholdAt 4 (39+i) := by decide +kernel

theorem threshold_4_40 : ∀ i ∈ List.range 1, ThresholdAt 4 (40+i) := by decide +kernel

theorem threshold_4_41 : ∀ i ∈ List.range 1, ThresholdAt 4 (41+i) := by decide +kernel

theorem threshold_4_42 : ∀ i ∈ List.range 1, ThresholdAt 4 (42+i) := by decide +kernel

theorem threshold_4_43 : ∀ i ∈ List.range 1, ThresholdAt 4 (43+i) := by decide +kernel

theorem threshold_4_44 : ∀ i ∈ List.range 1, ThresholdAt 4 (44+i) := by decide +kernel

theorem threshold_4_45 : ∀ i ∈ List.range 1, ThresholdAt 4 (45+i) := by decide +kernel

theorem threshold_4_46 : ∀ i ∈ List.range 1, ThresholdAt 4 (46+i) := by decide +kernel

theorem threshold_4_47 : ∀ i ∈ List.range 1, ThresholdAt 4 (47+i) := by decide +kernel

theorem threshold_4_48 : ∀ i ∈ List.range 1, ThresholdAt 4 (48+i) := by decide +kernel

theorem threshold_4_49 : ∀ i ∈ List.range 1, ThresholdAt 4 (49+i) := by decide +kernel

theorem threshold_4_50 : ∀ i ∈ List.range 1, ThresholdAt 4 (50+i) := by decide +kernel

theorem threshold_4_51 : ∀ i ∈ List.range 1, ThresholdAt 4 (51+i) := by decide +kernel

theorem threshold_4_52 : ∀ i ∈ List.range 1, ThresholdAt 4 (52+i) := by decide +kernel

theorem threshold_4_53 : ∀ i ∈ List.range 1, ThresholdAt 4 (53+i) := by decide +kernel

theorem threshold_4_54 : ∀ i ∈ List.range 1, ThresholdAt 4 (54+i) := by decide +kernel

theorem threshold_4_55 : ∀ i ∈ List.range 1, ThresholdAt 4 (55+i) := by decide +kernel

theorem threshold_4_56 : ∀ i ∈ List.range 1, ThresholdAt 4 (56+i) := by decide +kernel

theorem threshold_4_57 : ∀ i ∈ List.range 1, ThresholdAt 4 (57+i) := by decide +kernel

theorem threshold_4_58 : ∀ i ∈ List.range 1, ThresholdAt 4 (58+i) := by decide +kernel

theorem threshold_4_59 : ∀ i ∈ List.range 1, ThresholdAt 4 (59+i) := by decide +kernel

theorem threshold_4_60 : ∀ i ∈ List.range 1, ThresholdAt 4 (60+i) := by decide +kernel

theorem threshold_4_61 : ∀ i ∈ List.range 1, ThresholdAt 4 (61+i) := by decide +kernel

theorem threshold_4_62 : ∀ i ∈ List.range 1, ThresholdAt 4 (62+i) := by decide +kernel

theorem threshold_4_63 : ∀ i ∈ List.range 1, ThresholdAt 4 (63+i) := by decide +kernel

theorem threshold_4_64 : ∀ i ∈ List.range 1, ThresholdAt 4 (64+i) := by decide +kernel

theorem threshold_4_65 : ∀ i ∈ List.range 1, ThresholdAt 4 (65+i) := by decide +kernel

theorem threshold_4_66 : ∀ i ∈ List.range 1, ThresholdAt 4 (66+i) := by decide +kernel

theorem threshold_4_67 : ∀ i ∈ List.range 1, ThresholdAt 4 (67+i) := by decide +kernel

theorem threshold_4_68 : ∀ i ∈ List.range 1, ThresholdAt 4 (68+i) := by decide +kernel

theorem threshold_4_69 : ∀ i ∈ List.range 1, ThresholdAt 4 (69+i) := by decide +kernel

theorem threshold_4_70 : ∀ i ∈ List.range 1, ThresholdAt 4 (70+i) := by decide +kernel

theorem threshold_4_71 : ∀ i ∈ List.range 1, ThresholdAt 4 (71+i) := by decide +kernel

theorem threshold_4_72 : ∀ i ∈ List.range 1, ThresholdAt 4 (72+i) := by decide +kernel

theorem threshold_4_73 : ∀ i ∈ List.range 1, ThresholdAt 4 (73+i) := by decide +kernel

theorem threshold_4_74 : ∀ i ∈ List.range 1, ThresholdAt 4 (74+i) := by decide +kernel

theorem threshold_4_75 : ∀ i ∈ List.range 1, ThresholdAt 4 (75+i) := by decide +kernel

theorem threshold_4_76 : ∀ i ∈ List.range 1, ThresholdAt 4 (76+i) := by decide +kernel

theorem threshold_4_77 : ∀ i ∈ List.range 1, ThresholdAt 4 (77+i) := by decide +kernel

theorem threshold_4_78 : ∀ i ∈ List.range 1, ThresholdAt 4 (78+i) := by decide +kernel

theorem threshold_4_79 : ∀ i ∈ List.range 1, ThresholdAt 4 (79+i) := by decide +kernel

theorem threshold_4_80 : ∀ i ∈ List.range 1, ThresholdAt 4 (80+i) := by decide +kernel

theorem threshold_4_81 : ∀ i ∈ List.range 1, ThresholdAt 4 (81+i) := by decide +kernel

theorem threshold_4_82 : ∀ i ∈ List.range 1, ThresholdAt 4 (82+i) := by decide +kernel

theorem threshold_4_83 : ∀ i ∈ List.range 1, ThresholdAt 4 (83+i) := by decide +kernel

theorem threshold_4_84 : ∀ i ∈ List.range 1, ThresholdAt 4 (84+i) := by decide +kernel

theorem threshold_4_85 : ∀ i ∈ List.range 1, ThresholdAt 4 (85+i) := by decide +kernel

theorem threshold_4_86 : ∀ i ∈ List.range 1, ThresholdAt 4 (86+i) := by decide +kernel

theorem threshold_4_87 : ∀ i ∈ List.range 1, ThresholdAt 4 (87+i) := by decide +kernel

theorem threshold_4_88 : ∀ i ∈ List.range 1, ThresholdAt 4 (88+i) := by decide +kernel

theorem threshold_4_89 : ∀ i ∈ List.range 1, ThresholdAt 4 (89+i) := by decide +kernel

theorem threshold_4_90 : ∀ i ∈ List.range 1, ThresholdAt 4 (90+i) := by decide +kernel

theorem threshold_4_91 : ∀ i ∈ List.range 1, ThresholdAt 4 (91+i) := by decide +kernel

theorem threshold_4_92 : ∀ i ∈ List.range 1, ThresholdAt 4 (92+i) := by decide +kernel

theorem threshold_4_93 : ∀ i ∈ List.range 1, ThresholdAt 4 (93+i) := by decide +kernel

theorem threshold_4_94 : ∀ i ∈ List.range 1, ThresholdAt 4 (94+i) := by decide +kernel

theorem threshold_4_95 : ∀ i ∈ List.range 1, ThresholdAt 4 (95+i) := by decide +kernel

theorem threshold_4_96 : ∀ i ∈ List.range 1, ThresholdAt 4 (96+i) := by decide +kernel

theorem threshold_4_97 : ∀ i ∈ List.range 1, ThresholdAt 4 (97+i) := by decide +kernel

theorem threshold_4_98 : ∀ i ∈ List.range 1, ThresholdAt 4 (98+i) := by decide +kernel

theorem threshold_4_99 : ∀ i ∈ List.range 1, ThresholdAt 4 (99+i) := by decide +kernel

theorem threshold_4_100 : ∀ i ∈ List.range 1, ThresholdAt 4 (100+i) := by decide +kernel

theorem threshold_4_101 : ∀ i ∈ List.range 1, ThresholdAt 4 (101+i) := by decide +kernel

theorem threshold_4_102 : ∀ i ∈ List.range 1, ThresholdAt 4 (102+i) := by decide +kernel

theorem threshold_4_103 : ∀ i ∈ List.range 1, ThresholdAt 4 (103+i) := by decide +kernel

theorem threshold_4_104 : ∀ i ∈ List.range 1, ThresholdAt 4 (104+i) := by decide +kernel

theorem threshold_4_105 : ∀ i ∈ List.range 1, ThresholdAt 4 (105+i) := by decide +kernel

theorem threshold_4_106 : ∀ i ∈ List.range 1, ThresholdAt 4 (106+i) := by decide +kernel

theorem threshold_4_107 : ∀ i ∈ List.range 1, ThresholdAt 4 (107+i) := by decide +kernel

theorem threshold_4_108 : ∀ i ∈ List.range 1, ThresholdAt 4 (108+i) := by decide +kernel

theorem threshold_4_109 : ∀ i ∈ List.range 1, ThresholdAt 4 (109+i) := by decide +kernel

theorem threshold_4_110 : ∀ i ∈ List.range 1, ThresholdAt 4 (110+i) := by decide +kernel

theorem threshold_4_111 : ∀ i ∈ List.range 1, ThresholdAt 4 (111+i) := by decide +kernel

theorem threshold_4_112 : ∀ i ∈ List.range 1, ThresholdAt 4 (112+i) := by decide +kernel

theorem threshold_4_113 : ∀ i ∈ List.range 1, ThresholdAt 4 (113+i) := by decide +kernel

theorem threshold_4_114 : ∀ i ∈ List.range 1, ThresholdAt 4 (114+i) := by decide +kernel

theorem threshold_4_115 : ∀ i ∈ List.range 1, ThresholdAt 4 (115+i) := by decide +kernel

theorem threshold_4_116 : ∀ i ∈ List.range 1, ThresholdAt 4 (116+i) := by decide +kernel

theorem threshold_4_117 : ∀ i ∈ List.range 1, ThresholdAt 4 (117+i) := by decide +kernel

theorem threshold_4_118 : ∀ i ∈ List.range 1, ThresholdAt 4 (118+i) := by decide +kernel

theorem threshold_4_119 : ∀ i ∈ List.range 1, ThresholdAt 4 (119+i) := by decide +kernel

theorem threshold_4_120 : ∀ i ∈ List.range 1, ThresholdAt 4 (120+i) := by decide +kernel

theorem threshold_4_121 : ∀ i ∈ List.range 1, ThresholdAt 4 (121+i) := by decide +kernel

theorem threshold_4_122 : ∀ i ∈ List.range 1, ThresholdAt 4 (122+i) := by decide +kernel

theorem threshold_4_123 : ∀ i ∈ List.range 1, ThresholdAt 4 (123+i) := by decide +kernel

theorem threshold_4_124 : ∀ i ∈ List.range 1, ThresholdAt 4 (124+i) := by decide +kernel

theorem threshold_4_125 : ∀ i ∈ List.range 1, ThresholdAt 4 (125+i) := by decide +kernel

theorem threshold_4_126 : ∀ i ∈ List.range 1, ThresholdAt 4 (126+i) := by decide +kernel

theorem threshold_4_127 : ∀ i ∈ List.range 1, ThresholdAt 4 (127+i) := by decide +kernel

theorem threshold_4_128 : ∀ i ∈ List.range 1, ThresholdAt 4 (128+i) := by decide +kernel

theorem threshold_4_129 : ∀ i ∈ List.range 1, ThresholdAt 4 (129+i) := by decide +kernel

theorem threshold_4_130 : ∀ i ∈ List.range 1, ThresholdAt 4 (130+i) := by decide +kernel

theorem threshold_4_131 : ∀ i ∈ List.range 1, ThresholdAt 4 (131+i) := by decide +kernel

theorem threshold_4_132 : ∀ i ∈ List.range 1, ThresholdAt 4 (132+i) := by decide +kernel

theorem threshold_4_133 : ∀ i ∈ List.range 1, ThresholdAt 4 (133+i) := by decide +kernel

theorem threshold_4_134 : ∀ i ∈ List.range 1, ThresholdAt 4 (134+i) := by decide +kernel

theorem threshold_4_135 : ∀ i ∈ List.range 1, ThresholdAt 4 (135+i) := by decide +kernel

theorem threshold_4_136 : ∀ i ∈ List.range 1, ThresholdAt 4 (136+i) := by decide +kernel

theorem threshold_4_137 : ∀ i ∈ List.range 1, ThresholdAt 4 (137+i) := by decide +kernel

theorem threshold_4_138 : ∀ i ∈ List.range 1, ThresholdAt 4 (138+i) := by decide +kernel

theorem threshold_4_139 : ∀ i ∈ List.range 1, ThresholdAt 4 (139+i) := by decide +kernel

theorem threshold_4_140 : ∀ i ∈ List.range 1, ThresholdAt 4 (140+i) := by decide +kernel

theorem threshold_4_141 : ∀ i ∈ List.range 1, ThresholdAt 4 (141+i) := by decide +kernel

theorem threshold_4_142 : ∀ i ∈ List.range 1, ThresholdAt 4 (142+i) := by decide +kernel

theorem threshold_4_143 : ∀ i ∈ List.range 1, ThresholdAt 4 (143+i) := by decide +kernel

theorem threshold_4_144 : ∀ i ∈ List.range 1, ThresholdAt 4 (144+i) := by decide +kernel

theorem threshold_4_145 : ∀ i ∈ List.range 1, ThresholdAt 4 (145+i) := by decide +kernel

theorem threshold_4 (v : ℕ) (hv : v ∈ List.range 146) : ThresholdAt 4 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 4 v)
  have h := (join 0 73 73 (join 0 36 37 (join 0 18 18 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_4_0 threshold_4_1) (join 2 1 1 threshold_4_2 threshold_4_3)) (join 4 2 3 (join 4 1 1 threshold_4_4 threshold_4_5) (join 6 1 2 threshold_4_6 (join 7 1 1 threshold_4_7 threshold_4_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 threshold_4_9 threshold_4_10) (join 11 1 1 threshold_4_11 threshold_4_12)) (join 13 2 3 (join 13 1 1 threshold_4_13 threshold_4_14) (join 15 1 2 threshold_4_15 (join 16 1 1 threshold_4_16 threshold_4_17))))) (join 18 9 9 (join 18 4 5 (join 18 2 2 (join 18 1 1 threshold_4_18 threshold_4_19) (join 20 1 1 threshold_4_20 threshold_4_21)) (join 22 2 3 (join 22 1 1 threshold_4_22 threshold_4_23) (join 24 1 2 threshold_4_24 (join 25 1 1 threshold_4_25 threshold_4_26)))) (join 27 4 5 (join 27 2 2 (join 27 1 1 threshold_4_27 threshold_4_28) (join 29 1 1 threshold_4_29 threshold_4_30)) (join 31 2 3 (join 31 1 1 threshold_4_31 threshold_4_32) (join 33 1 2 threshold_4_33 (join 34 1 1 threshold_4_34 threshold_4_35)))))) (join 36 18 19 (join 36 9 9 (join 36 4 5 (join 36 2 2 (join 36 1 1 threshold_4_36 threshold_4_37) (join 38 1 1 threshold_4_38 threshold_4_39)) (join 40 2 3 (join 40 1 1 threshold_4_40 threshold_4_41) (join 42 1 2 threshold_4_42 (join 43 1 1 threshold_4_43 threshold_4_44)))) (join 45 4 5 (join 45 2 2 (join 45 1 1 threshold_4_45 threshold_4_46) (join 47 1 1 threshold_4_47 threshold_4_48)) (join 49 2 3 (join 49 1 1 threshold_4_49 threshold_4_50) (join 51 1 2 threshold_4_51 (join 52 1 1 threshold_4_52 threshold_4_53))))) (join 54 9 10 (join 54 4 5 (join 54 2 2 (join 54 1 1 threshold_4_54 threshold_4_55) (join 56 1 1 threshold_4_56 threshold_4_57)) (join 58 2 3 (join 58 1 1 threshold_4_58 threshold_4_59) (join 60 1 2 threshold_4_60 (join 61 1 1 threshold_4_61 threshold_4_62)))) (join 63 5 5 (join 63 2 3 (join 63 1 1 threshold_4_63 threshold_4_64) (join 65 1 2 threshold_4_65 (join 66 1 1 threshold_4_66 threshold_4_67))) (join 68 2 3 (join 68 1 1 threshold_4_68 threshold_4_69) (join 70 1 2 threshold_4_70 (join 71 1 1 threshold_4_71 threshold_4_72))))))) (join 73 36 37 (join 73 18 18 (join 73 9 9 (join 73 4 5 (join 73 2 2 (join 73 1 1 threshold_4_73 threshold_4_74) (join 75 1 1 threshold_4_75 threshold_4_76)) (join 77 2 3 (join 77 1 1 threshold_4_77 threshold_4_78) (join 79 1 2 threshold_4_79 (join 80 1 1 threshold_4_80 threshold_4_81)))) (join 82 4 5 (join 82 2 2 (join 82 1 1 threshold_4_82 threshold_4_83) (join 84 1 1 threshold_4_84 threshold_4_85)) (join 86 2 3 (join 86 1 1 threshold_4_86 threshold_4_87) (join 88 1 2 threshold_4_88 (join 89 1 1 threshold_4_89 threshold_4_90))))) (join 91 9 9 (join 91 4 5 (join 91 2 2 (join 91 1 1 threshold_4_91 threshold_4_92) (join 93 1 1 threshold_4_93 threshold_4_94)) (join 95 2 3 (join 95 1 1 threshold_4_95 threshold_4_96) (join 97 1 2 threshold_4_97 (join 98 1 1 threshold_4_98 threshold_4_99)))) (join 100 4 5 (join 100 2 2 (join 100 1 1 threshold_4_100 threshold_4_101) (join 102 1 1 threshold_4_102 threshold_4_103)) (join 104 2 3 (join 104 1 1 threshold_4_104 threshold_4_105) (join 106 1 2 threshold_4_106 (join 107 1 1 threshold_4_107 threshold_4_108)))))) (join 109 18 19 (join 109 9 9 (join 109 4 5 (join 109 2 2 (join 109 1 1 threshold_4_109 threshold_4_110) (join 111 1 1 threshold_4_111 threshold_4_112)) (join 113 2 3 (join 113 1 1 threshold_4_113 threshold_4_114) (join 115 1 2 threshold_4_115 (join 116 1 1 threshold_4_116 threshold_4_117)))) (join 118 4 5 (join 118 2 2 (join 118 1 1 threshold_4_118 threshold_4_119) (join 120 1 1 threshold_4_120 threshold_4_121)) (join 122 2 3 (join 122 1 1 threshold_4_122 threshold_4_123) (join 124 1 2 threshold_4_124 (join 125 1 1 threshold_4_125 threshold_4_126))))) (join 127 9 10 (join 127 4 5 (join 127 2 2 (join 127 1 1 threshold_4_127 threshold_4_128) (join 129 1 1 threshold_4_129 threshold_4_130)) (join 131 2 3 (join 131 1 1 threshold_4_131 threshold_4_132) (join 133 1 2 threshold_4_133 (join 134 1 1 threshold_4_134 threshold_4_135)))) (join 136 5 5 (join 136 2 3 (join 136 1 1 threshold_4_136 threshold_4_137) (join 138 1 2 threshold_4_138 (join 139 1 1 threshold_4_139 threshold_4_140))) (join 141 2 3 (join 141 1 1 threshold_4_141 threshold_4_142) (join 143 1 2 threshold_4_143 (join 144 1 1 threshold_4_144 threshold_4_145))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_4_0 : ∀ i ∈ List.range 4, LedgerAt 4 (0+i) := by decide +kernel

theorem ledger_4_4 : ∀ i ∈ List.range 4, LedgerAt 4 (4+i) := by decide +kernel

theorem ledger_4_8 : ∀ i ∈ List.range 4, LedgerAt 4 (8+i) := by decide +kernel

theorem ledger_4_12 : ∀ i ∈ List.range 4, LedgerAt 4 (12+i) := by decide +kernel

theorem ledger_4_16 : ∀ i ∈ List.range 4, LedgerAt 4 (16+i) := by decide +kernel

theorem ledger_4_20 : ∀ i ∈ List.range 4, LedgerAt 4 (20+i) := by decide +kernel

theorem ledger_4_24 : ∀ i ∈ List.range 4, LedgerAt 4 (24+i) := by decide +kernel

theorem ledger_4_28 : ∀ i ∈ List.range 4, LedgerAt 4 (28+i) := by decide +kernel

theorem ledger_4_32 : ∀ i ∈ List.range 4, LedgerAt 4 (32+i) := by decide +kernel

theorem ledger_4_36 : ∀ i ∈ List.range 4, LedgerAt 4 (36+i) := by decide +kernel

theorem ledger_4_40 : ∀ i ∈ List.range 4, LedgerAt 4 (40+i) := by decide +kernel

theorem ledger_4_44 : ∀ i ∈ List.range 4, LedgerAt 4 (44+i) := by decide +kernel

theorem ledger_4_48 : ∀ i ∈ List.range 4, LedgerAt 4 (48+i) := by decide +kernel

theorem ledger_4_52 : ∀ i ∈ List.range 4, LedgerAt 4 (52+i) := by decide +kernel

theorem ledger_4_56 : ∀ i ∈ List.range 4, LedgerAt 4 (56+i) := by decide +kernel

theorem ledger_4_60 : ∀ i ∈ List.range 4, LedgerAt 4 (60+i) := by decide +kernel

theorem ledger_4_64 : ∀ i ∈ List.range 4, LedgerAt 4 (64+i) := by decide +kernel

theorem ledger_4_68 : ∀ i ∈ List.range 4, LedgerAt 4 (68+i) := by decide +kernel

theorem ledger_4_72 : ∀ i ∈ List.range 4, LedgerAt 4 (72+i) := by decide +kernel

theorem ledger_4_76 : ∀ i ∈ List.range 4, LedgerAt 4 (76+i) := by decide +kernel

theorem ledger_4_80 : ∀ i ∈ List.range 4, LedgerAt 4 (80+i) := by decide +kernel

theorem ledger_4_84 : ∀ i ∈ List.range 4, LedgerAt 4 (84+i) := by decide +kernel

theorem ledger_4_88 : ∀ i ∈ List.range 4, LedgerAt 4 (88+i) := by decide +kernel

theorem ledger_4_92 : ∀ i ∈ List.range 4, LedgerAt 4 (92+i) := by decide +kernel

theorem ledger_4_96 : ∀ i ∈ List.range 4, LedgerAt 4 (96+i) := by decide +kernel

theorem ledger_4_100 : ∀ i ∈ List.range 4, LedgerAt 4 (100+i) := by decide +kernel

theorem ledger_4_104 : ∀ i ∈ List.range 4, LedgerAt 4 (104+i) := by decide +kernel

theorem ledger_4_108 : ∀ i ∈ List.range 4, LedgerAt 4 (108+i) := by decide +kernel

theorem ledger_4_112 : ∀ i ∈ List.range 4, LedgerAt 4 (112+i) := by decide +kernel

theorem ledger_4_116 : ∀ i ∈ List.range 4, LedgerAt 4 (116+i) := by decide +kernel

theorem ledger_4_120 : ∀ i ∈ List.range 4, LedgerAt 4 (120+i) := by decide +kernel

theorem ledger_4_124 : ∀ i ∈ List.range 4, LedgerAt 4 (124+i) := by decide +kernel

theorem ledger_4_128 : ∀ i ∈ List.range 4, LedgerAt 4 (128+i) := by decide +kernel

theorem ledger_4_132 : ∀ i ∈ List.range 4, LedgerAt 4 (132+i) := by decide +kernel

theorem ledger_4_136 : ∀ i ∈ List.range 4, LedgerAt 4 (136+i) := by decide +kernel

theorem ledger_4_140 : ∀ i ∈ List.range 4, LedgerAt 4 (140+i) := by decide +kernel

theorem ledger_4_144 : ∀ i ∈ List.range 2, LedgerAt 4 (144+i) := by decide +kernel

theorem ledger_4 (v : ℕ) (hv : v ∈ List.range 146) : LedgerAt 4 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 4 v)
  have h := (join 0 72 74 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_4_0 ledger_4_4) (join 8 4 4 ledger_4_8 ledger_4_12)) (join 16 8 12 (join 16 4 4 ledger_4_16 ledger_4_20) (join 24 4 8 ledger_4_24 (join 28 4 4 ledger_4_28 ledger_4_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_4_36 ledger_4_40) (join 44 4 4 ledger_4_44 ledger_4_48)) (join 52 8 12 (join 52 4 4 ledger_4_52 ledger_4_56) (join 60 4 8 ledger_4_60 (join 64 4 4 ledger_4_64 ledger_4_68))))) (join 72 36 38 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_4_72 ledger_4_76) (join 80 4 4 ledger_4_80 ledger_4_84)) (join 88 8 12 (join 88 4 4 ledger_4_88 ledger_4_92) (join 96 4 8 ledger_4_96 (join 100 4 4 ledger_4_100 ledger_4_104)))) (join 108 20 18 (join 108 8 12 (join 108 4 4 ledger_4_108 ledger_4_112) (join 116 4 8 ledger_4_116 (join 120 4 4 ledger_4_120 ledger_4_124))) (join 128 8 10 (join 128 4 4 ledger_4_128 ledger_4_132) (join 136 4 6 ledger_4_136 (join 140 4 2 ledger_4_140 ledger_4_144))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
