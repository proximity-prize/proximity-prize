import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_5_0 : ∀ i ∈ List.range 4, SingleAt 5 (0+i) := by decide +kernel

theorem single_5_4 : ∀ i ∈ List.range 4, SingleAt 5 (4+i) := by decide +kernel

theorem single_5_8 : ∀ i ∈ List.range 4, SingleAt 5 (8+i) := by decide +kernel

theorem single_5_12 : ∀ i ∈ List.range 4, SingleAt 5 (12+i) := by decide +kernel

theorem single_5_16 : ∀ i ∈ List.range 4, SingleAt 5 (16+i) := by decide +kernel

theorem single_5_20 : ∀ i ∈ List.range 4, SingleAt 5 (20+i) := by decide +kernel

theorem single_5_24 : ∀ i ∈ List.range 4, SingleAt 5 (24+i) := by decide +kernel

theorem single_5_28 : ∀ i ∈ List.range 4, SingleAt 5 (28+i) := by decide +kernel

theorem single_5_32 : ∀ i ∈ List.range 4, SingleAt 5 (32+i) := by decide +kernel

theorem single_5_36 : ∀ i ∈ List.range 4, SingleAt 5 (36+i) := by decide +kernel

theorem single_5_40 : ∀ i ∈ List.range 4, SingleAt 5 (40+i) := by decide +kernel

theorem single_5_44 : ∀ i ∈ List.range 4, SingleAt 5 (44+i) := by decide +kernel

theorem single_5_48 : ∀ i ∈ List.range 4, SingleAt 5 (48+i) := by decide +kernel

theorem single_5_52 : ∀ i ∈ List.range 4, SingleAt 5 (52+i) := by decide +kernel

theorem single_5_56 : ∀ i ∈ List.range 4, SingleAt 5 (56+i) := by decide +kernel

theorem single_5_60 : ∀ i ∈ List.range 4, SingleAt 5 (60+i) := by decide +kernel

theorem single_5_64 : ∀ i ∈ List.range 4, SingleAt 5 (64+i) := by decide +kernel

theorem single_5_68 : ∀ i ∈ List.range 4, SingleAt 5 (68+i) := by decide +kernel

theorem single_5_72 : ∀ i ∈ List.range 4, SingleAt 5 (72+i) := by decide +kernel

theorem single_5_76 : ∀ i ∈ List.range 4, SingleAt 5 (76+i) := by decide +kernel

theorem single_5_80 : ∀ i ∈ List.range 4, SingleAt 5 (80+i) := by decide +kernel

theorem single_5_84 : ∀ i ∈ List.range 4, SingleAt 5 (84+i) := by decide +kernel

theorem single_5_88 : ∀ i ∈ List.range 4, SingleAt 5 (88+i) := by decide +kernel

theorem single_5_92 : ∀ i ∈ List.range 4, SingleAt 5 (92+i) := by decide +kernel

theorem single_5_96 : ∀ i ∈ List.range 4, SingleAt 5 (96+i) := by decide +kernel

theorem single_5_100 : ∀ i ∈ List.range 4, SingleAt 5 (100+i) := by decide +kernel

theorem single_5_104 : ∀ i ∈ List.range 4, SingleAt 5 (104+i) := by decide +kernel

theorem single_5_108 : ∀ i ∈ List.range 4, SingleAt 5 (108+i) := by decide +kernel

theorem single_5_112 : ∀ i ∈ List.range 4, SingleAt 5 (112+i) := by decide +kernel

theorem single_5_116 : ∀ i ∈ List.range 4, SingleAt 5 (116+i) := by decide +kernel

theorem single_5_120 : ∀ i ∈ List.range 4, SingleAt 5 (120+i) := by decide +kernel

theorem single_5_124 : ∀ i ∈ List.range 4, SingleAt 5 (124+i) := by decide +kernel

theorem single_5_128 : ∀ i ∈ List.range 4, SingleAt 5 (128+i) := by decide +kernel

theorem single_5_132 : ∀ i ∈ List.range 4, SingleAt 5 (132+i) := by decide +kernel

theorem single_5_136 : ∀ i ∈ List.range 4, SingleAt 5 (136+i) := by decide +kernel

theorem single_5_140 : ∀ i ∈ List.range 4, SingleAt 5 (140+i) := by decide +kernel

theorem single_5_144 : ∀ i ∈ List.range 1, SingleAt 5 (144+i) := by decide +kernel

theorem single_5 (v : ℕ) (hv : v ∈ List.range 145) : SingleAt 5 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 5 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_5_0 single_5_4) (join 8 4 4 single_5_8 single_5_12)) (join 16 8 12 (join 16 4 4 single_5_16 single_5_20) (join 24 4 8 single_5_24 (join 28 4 4 single_5_28 single_5_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_5_36 single_5_40) (join 44 4 4 single_5_44 single_5_48)) (join 52 8 12 (join 52 4 4 single_5_52 single_5_56) (join 60 4 8 single_5_60 (join 64 4 4 single_5_64 single_5_68))))) (join 72 36 37 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_5_72 single_5_76) (join 80 4 4 single_5_80 single_5_84)) (join 88 8 12 (join 88 4 4 single_5_88 single_5_92) (join 96 4 8 single_5_96 (join 100 4 4 single_5_100 single_5_104)))) (join 108 20 17 (join 108 8 12 (join 108 4 4 single_5_108 single_5_112) (join 116 4 8 single_5_116 (join 120 4 4 single_5_120 single_5_124))) (join 128 8 9 (join 128 4 4 single_5_128 single_5_132) (join 136 4 5 single_5_136 (join 140 4 1 single_5_140 single_5_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_5_0 : ∀ i ∈ List.range 4, PhaseAt 5 (0+i) := by decide +kernel

theorem phase_5_4 : ∀ i ∈ List.range 4, PhaseAt 5 (4+i) := by decide +kernel

theorem phase_5_8 : ∀ i ∈ List.range 4, PhaseAt 5 (8+i) := by decide +kernel

theorem phase_5_12 : ∀ i ∈ List.range 4, PhaseAt 5 (12+i) := by decide +kernel

theorem phase_5_16 : ∀ i ∈ List.range 4, PhaseAt 5 (16+i) := by decide +kernel

theorem phase_5_20 : ∀ i ∈ List.range 4, PhaseAt 5 (20+i) := by decide +kernel

theorem phase_5_24 : ∀ i ∈ List.range 4, PhaseAt 5 (24+i) := by decide +kernel

theorem phase_5_28 : ∀ i ∈ List.range 4, PhaseAt 5 (28+i) := by decide +kernel

theorem phase_5_32 : ∀ i ∈ List.range 4, PhaseAt 5 (32+i) := by decide +kernel

theorem phase_5_36 : ∀ i ∈ List.range 4, PhaseAt 5 (36+i) := by decide +kernel

theorem phase_5_40 : ∀ i ∈ List.range 4, PhaseAt 5 (40+i) := by decide +kernel

theorem phase_5_44 : ∀ i ∈ List.range 4, PhaseAt 5 (44+i) := by decide +kernel

theorem phase_5_48 : ∀ i ∈ List.range 4, PhaseAt 5 (48+i) := by decide +kernel

theorem phase_5_52 : ∀ i ∈ List.range 4, PhaseAt 5 (52+i) := by decide +kernel

theorem phase_5_56 : ∀ i ∈ List.range 4, PhaseAt 5 (56+i) := by decide +kernel

theorem phase_5_60 : ∀ i ∈ List.range 4, PhaseAt 5 (60+i) := by decide +kernel

theorem phase_5_64 : ∀ i ∈ List.range 4, PhaseAt 5 (64+i) := by decide +kernel

theorem phase_5_68 : ∀ i ∈ List.range 4, PhaseAt 5 (68+i) := by decide +kernel

theorem phase_5_72 : ∀ i ∈ List.range 4, PhaseAt 5 (72+i) := by decide +kernel

theorem phase_5_76 : ∀ i ∈ List.range 4, PhaseAt 5 (76+i) := by decide +kernel

theorem phase_5_80 : ∀ i ∈ List.range 4, PhaseAt 5 (80+i) := by decide +kernel

theorem phase_5_84 : ∀ i ∈ List.range 4, PhaseAt 5 (84+i) := by decide +kernel

theorem phase_5_88 : ∀ i ∈ List.range 4, PhaseAt 5 (88+i) := by decide +kernel

theorem phase_5_92 : ∀ i ∈ List.range 4, PhaseAt 5 (92+i) := by decide +kernel

theorem phase_5_96 : ∀ i ∈ List.range 4, PhaseAt 5 (96+i) := by decide +kernel

theorem phase_5_100 : ∀ i ∈ List.range 4, PhaseAt 5 (100+i) := by decide +kernel

theorem phase_5_104 : ∀ i ∈ List.range 4, PhaseAt 5 (104+i) := by decide +kernel

theorem phase_5_108 : ∀ i ∈ List.range 4, PhaseAt 5 (108+i) := by decide +kernel

theorem phase_5_112 : ∀ i ∈ List.range 4, PhaseAt 5 (112+i) := by decide +kernel

theorem phase_5_116 : ∀ i ∈ List.range 4, PhaseAt 5 (116+i) := by decide +kernel

theorem phase_5_120 : ∀ i ∈ List.range 4, PhaseAt 5 (120+i) := by decide +kernel

theorem phase_5_124 : ∀ i ∈ List.range 4, PhaseAt 5 (124+i) := by decide +kernel

theorem phase_5_128 : ∀ i ∈ List.range 4, PhaseAt 5 (128+i) := by decide +kernel

theorem phase_5_132 : ∀ i ∈ List.range 4, PhaseAt 5 (132+i) := by decide +kernel

theorem phase_5_136 : ∀ i ∈ List.range 4, PhaseAt 5 (136+i) := by decide +kernel

theorem phase_5_140 : ∀ i ∈ List.range 4, PhaseAt 5 (140+i) := by decide +kernel

theorem phase_5_144 : ∀ i ∈ List.range 1, PhaseAt 5 (144+i) := by decide +kernel

theorem phase_5 (v : ℕ) (hv : v ∈ List.range 145) : PhaseAt 5 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 5 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_5_0 phase_5_4) (join 8 4 4 phase_5_8 phase_5_12)) (join 16 8 12 (join 16 4 4 phase_5_16 phase_5_20) (join 24 4 8 phase_5_24 (join 28 4 4 phase_5_28 phase_5_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_5_36 phase_5_40) (join 44 4 4 phase_5_44 phase_5_48)) (join 52 8 12 (join 52 4 4 phase_5_52 phase_5_56) (join 60 4 8 phase_5_60 (join 64 4 4 phase_5_64 phase_5_68))))) (join 72 36 37 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_5_72 phase_5_76) (join 80 4 4 phase_5_80 phase_5_84)) (join 88 8 12 (join 88 4 4 phase_5_88 phase_5_92) (join 96 4 8 phase_5_96 (join 100 4 4 phase_5_100 phase_5_104)))) (join 108 20 17 (join 108 8 12 (join 108 4 4 phase_5_108 phase_5_112) (join 116 4 8 phase_5_116 (join 120 4 4 phase_5_120 phase_5_124))) (join 128 8 9 (join 128 4 4 phase_5_128 phase_5_132) (join 136 4 5 phase_5_136 (join 140 4 1 phase_5_140 phase_5_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_5_0 : ∀ i ∈ List.range 1, ThresholdAt 5 (0+i) := by decide +kernel

theorem threshold_5_1 : ∀ i ∈ List.range 1, ThresholdAt 5 (1+i) := by decide +kernel

theorem threshold_5_2 : ∀ i ∈ List.range 1, ThresholdAt 5 (2+i) := by decide +kernel

theorem threshold_5_3 : ∀ i ∈ List.range 1, ThresholdAt 5 (3+i) := by decide +kernel

theorem threshold_5_4 : ∀ i ∈ List.range 1, ThresholdAt 5 (4+i) := by decide +kernel

theorem threshold_5_5 : ∀ i ∈ List.range 1, ThresholdAt 5 (5+i) := by decide +kernel

theorem threshold_5_6 : ∀ i ∈ List.range 1, ThresholdAt 5 (6+i) := by decide +kernel

theorem threshold_5_7 : ∀ i ∈ List.range 1, ThresholdAt 5 (7+i) := by decide +kernel

theorem threshold_5_8 : ∀ i ∈ List.range 1, ThresholdAt 5 (8+i) := by decide +kernel

theorem threshold_5_9 : ∀ i ∈ List.range 1, ThresholdAt 5 (9+i) := by decide +kernel

theorem threshold_5_10 : ∀ i ∈ List.range 1, ThresholdAt 5 (10+i) := by decide +kernel

theorem threshold_5_11 : ∀ i ∈ List.range 1, ThresholdAt 5 (11+i) := by decide +kernel

theorem threshold_5_12 : ∀ i ∈ List.range 1, ThresholdAt 5 (12+i) := by decide +kernel

theorem threshold_5_13 : ∀ i ∈ List.range 1, ThresholdAt 5 (13+i) := by decide +kernel

theorem threshold_5_14 : ∀ i ∈ List.range 1, ThresholdAt 5 (14+i) := by decide +kernel

theorem threshold_5_15 : ∀ i ∈ List.range 1, ThresholdAt 5 (15+i) := by decide +kernel

theorem threshold_5_16 : ∀ i ∈ List.range 1, ThresholdAt 5 (16+i) := by decide +kernel

theorem threshold_5_17 : ∀ i ∈ List.range 1, ThresholdAt 5 (17+i) := by decide +kernel

theorem threshold_5_18 : ∀ i ∈ List.range 1, ThresholdAt 5 (18+i) := by decide +kernel

theorem threshold_5_19 : ∀ i ∈ List.range 1, ThresholdAt 5 (19+i) := by decide +kernel

theorem threshold_5_20 : ∀ i ∈ List.range 1, ThresholdAt 5 (20+i) := by decide +kernel

theorem threshold_5_21 : ∀ i ∈ List.range 1, ThresholdAt 5 (21+i) := by decide +kernel

theorem threshold_5_22 : ∀ i ∈ List.range 1, ThresholdAt 5 (22+i) := by decide +kernel

theorem threshold_5_23 : ∀ i ∈ List.range 1, ThresholdAt 5 (23+i) := by decide +kernel

theorem threshold_5_24 : ∀ i ∈ List.range 1, ThresholdAt 5 (24+i) := by decide +kernel

theorem threshold_5_25 : ∀ i ∈ List.range 1, ThresholdAt 5 (25+i) := by decide +kernel

theorem threshold_5_26 : ∀ i ∈ List.range 1, ThresholdAt 5 (26+i) := by decide +kernel

theorem threshold_5_27 : ∀ i ∈ List.range 1, ThresholdAt 5 (27+i) := by decide +kernel

theorem threshold_5_28 : ∀ i ∈ List.range 1, ThresholdAt 5 (28+i) := by decide +kernel

theorem threshold_5_29 : ∀ i ∈ List.range 1, ThresholdAt 5 (29+i) := by decide +kernel

theorem threshold_5_30 : ∀ i ∈ List.range 1, ThresholdAt 5 (30+i) := by decide +kernel

theorem threshold_5_31 : ∀ i ∈ List.range 1, ThresholdAt 5 (31+i) := by decide +kernel

theorem threshold_5_32 : ∀ i ∈ List.range 1, ThresholdAt 5 (32+i) := by decide +kernel

theorem threshold_5_33 : ∀ i ∈ List.range 1, ThresholdAt 5 (33+i) := by decide +kernel

theorem threshold_5_34 : ∀ i ∈ List.range 1, ThresholdAt 5 (34+i) := by decide +kernel

theorem threshold_5_35 : ∀ i ∈ List.range 1, ThresholdAt 5 (35+i) := by decide +kernel

theorem threshold_5_36 : ∀ i ∈ List.range 1, ThresholdAt 5 (36+i) := by decide +kernel

theorem threshold_5_37 : ∀ i ∈ List.range 1, ThresholdAt 5 (37+i) := by decide +kernel

theorem threshold_5_38 : ∀ i ∈ List.range 1, ThresholdAt 5 (38+i) := by decide +kernel

theorem threshold_5_39 : ∀ i ∈ List.range 1, ThresholdAt 5 (39+i) := by decide +kernel

theorem threshold_5_40 : ∀ i ∈ List.range 1, ThresholdAt 5 (40+i) := by decide +kernel

theorem threshold_5_41 : ∀ i ∈ List.range 1, ThresholdAt 5 (41+i) := by decide +kernel

theorem threshold_5_42 : ∀ i ∈ List.range 1, ThresholdAt 5 (42+i) := by decide +kernel

theorem threshold_5_43 : ∀ i ∈ List.range 1, ThresholdAt 5 (43+i) := by decide +kernel

theorem threshold_5_44 : ∀ i ∈ List.range 1, ThresholdAt 5 (44+i) := by decide +kernel

theorem threshold_5_45 : ∀ i ∈ List.range 1, ThresholdAt 5 (45+i) := by decide +kernel

theorem threshold_5_46 : ∀ i ∈ List.range 1, ThresholdAt 5 (46+i) := by decide +kernel

theorem threshold_5_47 : ∀ i ∈ List.range 1, ThresholdAt 5 (47+i) := by decide +kernel

theorem threshold_5_48 : ∀ i ∈ List.range 1, ThresholdAt 5 (48+i) := by decide +kernel

theorem threshold_5_49 : ∀ i ∈ List.range 1, ThresholdAt 5 (49+i) := by decide +kernel

theorem threshold_5_50 : ∀ i ∈ List.range 1, ThresholdAt 5 (50+i) := by decide +kernel

theorem threshold_5_51 : ∀ i ∈ List.range 1, ThresholdAt 5 (51+i) := by decide +kernel

theorem threshold_5_52 : ∀ i ∈ List.range 1, ThresholdAt 5 (52+i) := by decide +kernel

theorem threshold_5_53 : ∀ i ∈ List.range 1, ThresholdAt 5 (53+i) := by decide +kernel

theorem threshold_5_54 : ∀ i ∈ List.range 1, ThresholdAt 5 (54+i) := by decide +kernel

theorem threshold_5_55 : ∀ i ∈ List.range 1, ThresholdAt 5 (55+i) := by decide +kernel

theorem threshold_5_56 : ∀ i ∈ List.range 1, ThresholdAt 5 (56+i) := by decide +kernel

theorem threshold_5_57 : ∀ i ∈ List.range 1, ThresholdAt 5 (57+i) := by decide +kernel

theorem threshold_5_58 : ∀ i ∈ List.range 1, ThresholdAt 5 (58+i) := by decide +kernel

theorem threshold_5_59 : ∀ i ∈ List.range 1, ThresholdAt 5 (59+i) := by decide +kernel

theorem threshold_5_60 : ∀ i ∈ List.range 1, ThresholdAt 5 (60+i) := by decide +kernel

theorem threshold_5_61 : ∀ i ∈ List.range 1, ThresholdAt 5 (61+i) := by decide +kernel

theorem threshold_5_62 : ∀ i ∈ List.range 1, ThresholdAt 5 (62+i) := by decide +kernel

theorem threshold_5_63 : ∀ i ∈ List.range 1, ThresholdAt 5 (63+i) := by decide +kernel

theorem threshold_5_64 : ∀ i ∈ List.range 1, ThresholdAt 5 (64+i) := by decide +kernel

theorem threshold_5_65 : ∀ i ∈ List.range 1, ThresholdAt 5 (65+i) := by decide +kernel

theorem threshold_5_66 : ∀ i ∈ List.range 1, ThresholdAt 5 (66+i) := by decide +kernel

theorem threshold_5_67 : ∀ i ∈ List.range 1, ThresholdAt 5 (67+i) := by decide +kernel

theorem threshold_5_68 : ∀ i ∈ List.range 1, ThresholdAt 5 (68+i) := by decide +kernel

theorem threshold_5_69 : ∀ i ∈ List.range 1, ThresholdAt 5 (69+i) := by decide +kernel

theorem threshold_5_70 : ∀ i ∈ List.range 1, ThresholdAt 5 (70+i) := by decide +kernel

theorem threshold_5_71 : ∀ i ∈ List.range 1, ThresholdAt 5 (71+i) := by decide +kernel

theorem threshold_5_72 : ∀ i ∈ List.range 1, ThresholdAt 5 (72+i) := by decide +kernel

theorem threshold_5_73 : ∀ i ∈ List.range 1, ThresholdAt 5 (73+i) := by decide +kernel

theorem threshold_5_74 : ∀ i ∈ List.range 1, ThresholdAt 5 (74+i) := by decide +kernel

theorem threshold_5_75 : ∀ i ∈ List.range 1, ThresholdAt 5 (75+i) := by decide +kernel

theorem threshold_5_76 : ∀ i ∈ List.range 1, ThresholdAt 5 (76+i) := by decide +kernel

theorem threshold_5_77 : ∀ i ∈ List.range 1, ThresholdAt 5 (77+i) := by decide +kernel

theorem threshold_5_78 : ∀ i ∈ List.range 1, ThresholdAt 5 (78+i) := by decide +kernel

theorem threshold_5_79 : ∀ i ∈ List.range 1, ThresholdAt 5 (79+i) := by decide +kernel

theorem threshold_5_80 : ∀ i ∈ List.range 1, ThresholdAt 5 (80+i) := by decide +kernel

theorem threshold_5_81 : ∀ i ∈ List.range 1, ThresholdAt 5 (81+i) := by decide +kernel

theorem threshold_5_82 : ∀ i ∈ List.range 1, ThresholdAt 5 (82+i) := by decide +kernel

theorem threshold_5_83 : ∀ i ∈ List.range 1, ThresholdAt 5 (83+i) := by decide +kernel

theorem threshold_5_84 : ∀ i ∈ List.range 1, ThresholdAt 5 (84+i) := by decide +kernel

theorem threshold_5_85 : ∀ i ∈ List.range 1, ThresholdAt 5 (85+i) := by decide +kernel

theorem threshold_5_86 : ∀ i ∈ List.range 1, ThresholdAt 5 (86+i) := by decide +kernel

theorem threshold_5_87 : ∀ i ∈ List.range 1, ThresholdAt 5 (87+i) := by decide +kernel

theorem threshold_5_88 : ∀ i ∈ List.range 1, ThresholdAt 5 (88+i) := by decide +kernel

theorem threshold_5_89 : ∀ i ∈ List.range 1, ThresholdAt 5 (89+i) := by decide +kernel

theorem threshold_5_90 : ∀ i ∈ List.range 1, ThresholdAt 5 (90+i) := by decide +kernel

theorem threshold_5_91 : ∀ i ∈ List.range 1, ThresholdAt 5 (91+i) := by decide +kernel

theorem threshold_5_92 : ∀ i ∈ List.range 1, ThresholdAt 5 (92+i) := by decide +kernel

theorem threshold_5_93 : ∀ i ∈ List.range 1, ThresholdAt 5 (93+i) := by decide +kernel

theorem threshold_5_94 : ∀ i ∈ List.range 1, ThresholdAt 5 (94+i) := by decide +kernel

theorem threshold_5_95 : ∀ i ∈ List.range 1, ThresholdAt 5 (95+i) := by decide +kernel

theorem threshold_5_96 : ∀ i ∈ List.range 1, ThresholdAt 5 (96+i) := by decide +kernel

theorem threshold_5_97 : ∀ i ∈ List.range 1, ThresholdAt 5 (97+i) := by decide +kernel

theorem threshold_5_98 : ∀ i ∈ List.range 1, ThresholdAt 5 (98+i) := by decide +kernel

theorem threshold_5_99 : ∀ i ∈ List.range 1, ThresholdAt 5 (99+i) := by decide +kernel

theorem threshold_5_100 : ∀ i ∈ List.range 1, ThresholdAt 5 (100+i) := by decide +kernel

theorem threshold_5_101 : ∀ i ∈ List.range 1, ThresholdAt 5 (101+i) := by decide +kernel

theorem threshold_5_102 : ∀ i ∈ List.range 1, ThresholdAt 5 (102+i) := by decide +kernel

theorem threshold_5_103 : ∀ i ∈ List.range 1, ThresholdAt 5 (103+i) := by decide +kernel

theorem threshold_5_104 : ∀ i ∈ List.range 1, ThresholdAt 5 (104+i) := by decide +kernel

theorem threshold_5_105 : ∀ i ∈ List.range 1, ThresholdAt 5 (105+i) := by decide +kernel

theorem threshold_5_106 : ∀ i ∈ List.range 1, ThresholdAt 5 (106+i) := by decide +kernel

theorem threshold_5_107 : ∀ i ∈ List.range 1, ThresholdAt 5 (107+i) := by decide +kernel

theorem threshold_5_108 : ∀ i ∈ List.range 1, ThresholdAt 5 (108+i) := by decide +kernel

theorem threshold_5_109 : ∀ i ∈ List.range 1, ThresholdAt 5 (109+i) := by decide +kernel

theorem threshold_5_110 : ∀ i ∈ List.range 1, ThresholdAt 5 (110+i) := by decide +kernel

theorem threshold_5_111 : ∀ i ∈ List.range 1, ThresholdAt 5 (111+i) := by decide +kernel

theorem threshold_5_112 : ∀ i ∈ List.range 1, ThresholdAt 5 (112+i) := by decide +kernel

theorem threshold_5_113 : ∀ i ∈ List.range 1, ThresholdAt 5 (113+i) := by decide +kernel

theorem threshold_5_114 : ∀ i ∈ List.range 1, ThresholdAt 5 (114+i) := by decide +kernel

theorem threshold_5_115 : ∀ i ∈ List.range 1, ThresholdAt 5 (115+i) := by decide +kernel

theorem threshold_5_116 : ∀ i ∈ List.range 1, ThresholdAt 5 (116+i) := by decide +kernel

theorem threshold_5_117 : ∀ i ∈ List.range 1, ThresholdAt 5 (117+i) := by decide +kernel

theorem threshold_5_118 : ∀ i ∈ List.range 1, ThresholdAt 5 (118+i) := by decide +kernel

theorem threshold_5_119 : ∀ i ∈ List.range 1, ThresholdAt 5 (119+i) := by decide +kernel

theorem threshold_5_120 : ∀ i ∈ List.range 1, ThresholdAt 5 (120+i) := by decide +kernel

theorem threshold_5_121 : ∀ i ∈ List.range 1, ThresholdAt 5 (121+i) := by decide +kernel

theorem threshold_5_122 : ∀ i ∈ List.range 1, ThresholdAt 5 (122+i) := by decide +kernel

theorem threshold_5_123 : ∀ i ∈ List.range 1, ThresholdAt 5 (123+i) := by decide +kernel

theorem threshold_5_124 : ∀ i ∈ List.range 1, ThresholdAt 5 (124+i) := by decide +kernel

theorem threshold_5_125 : ∀ i ∈ List.range 1, ThresholdAt 5 (125+i) := by decide +kernel

theorem threshold_5_126 : ∀ i ∈ List.range 1, ThresholdAt 5 (126+i) := by decide +kernel

theorem threshold_5_127 : ∀ i ∈ List.range 1, ThresholdAt 5 (127+i) := by decide +kernel

theorem threshold_5_128 : ∀ i ∈ List.range 1, ThresholdAt 5 (128+i) := by decide +kernel

theorem threshold_5_129 : ∀ i ∈ List.range 1, ThresholdAt 5 (129+i) := by decide +kernel

theorem threshold_5_130 : ∀ i ∈ List.range 1, ThresholdAt 5 (130+i) := by decide +kernel

theorem threshold_5_131 : ∀ i ∈ List.range 1, ThresholdAt 5 (131+i) := by decide +kernel

theorem threshold_5_132 : ∀ i ∈ List.range 1, ThresholdAt 5 (132+i) := by decide +kernel

theorem threshold_5_133 : ∀ i ∈ List.range 1, ThresholdAt 5 (133+i) := by decide +kernel

theorem threshold_5_134 : ∀ i ∈ List.range 1, ThresholdAt 5 (134+i) := by decide +kernel

theorem threshold_5_135 : ∀ i ∈ List.range 1, ThresholdAt 5 (135+i) := by decide +kernel

theorem threshold_5_136 : ∀ i ∈ List.range 1, ThresholdAt 5 (136+i) := by decide +kernel

theorem threshold_5_137 : ∀ i ∈ List.range 1, ThresholdAt 5 (137+i) := by decide +kernel

theorem threshold_5_138 : ∀ i ∈ List.range 1, ThresholdAt 5 (138+i) := by decide +kernel

theorem threshold_5_139 : ∀ i ∈ List.range 1, ThresholdAt 5 (139+i) := by decide +kernel

theorem threshold_5_140 : ∀ i ∈ List.range 1, ThresholdAt 5 (140+i) := by decide +kernel

theorem threshold_5_141 : ∀ i ∈ List.range 1, ThresholdAt 5 (141+i) := by decide +kernel

theorem threshold_5_142 : ∀ i ∈ List.range 1, ThresholdAt 5 (142+i) := by decide +kernel

theorem threshold_5_143 : ∀ i ∈ List.range 1, ThresholdAt 5 (143+i) := by decide +kernel

theorem threshold_5_144 : ∀ i ∈ List.range 1, ThresholdAt 5 (144+i) := by decide +kernel

theorem threshold_5 (v : ℕ) (hv : v ∈ List.range 145) : ThresholdAt 5 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 5 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 18 18 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_5_0 threshold_5_1) (join 2 1 1 threshold_5_2 threshold_5_3)) (join 4 2 3 (join 4 1 1 threshold_5_4 threshold_5_5) (join 6 1 2 threshold_5_6 (join 7 1 1 threshold_5_7 threshold_5_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 threshold_5_9 threshold_5_10) (join 11 1 1 threshold_5_11 threshold_5_12)) (join 13 2 3 (join 13 1 1 threshold_5_13 threshold_5_14) (join 15 1 2 threshold_5_15 (join 16 1 1 threshold_5_16 threshold_5_17))))) (join 18 9 9 (join 18 4 5 (join 18 2 2 (join 18 1 1 threshold_5_18 threshold_5_19) (join 20 1 1 threshold_5_20 threshold_5_21)) (join 22 2 3 (join 22 1 1 threshold_5_22 threshold_5_23) (join 24 1 2 threshold_5_24 (join 25 1 1 threshold_5_25 threshold_5_26)))) (join 27 4 5 (join 27 2 2 (join 27 1 1 threshold_5_27 threshold_5_28) (join 29 1 1 threshold_5_29 threshold_5_30)) (join 31 2 3 (join 31 1 1 threshold_5_31 threshold_5_32) (join 33 1 2 threshold_5_33 (join 34 1 1 threshold_5_34 threshold_5_35)))))) (join 36 18 18 (join 36 9 9 (join 36 4 5 (join 36 2 2 (join 36 1 1 threshold_5_36 threshold_5_37) (join 38 1 1 threshold_5_38 threshold_5_39)) (join 40 2 3 (join 40 1 1 threshold_5_40 threshold_5_41) (join 42 1 2 threshold_5_42 (join 43 1 1 threshold_5_43 threshold_5_44)))) (join 45 4 5 (join 45 2 2 (join 45 1 1 threshold_5_45 threshold_5_46) (join 47 1 1 threshold_5_47 threshold_5_48)) (join 49 2 3 (join 49 1 1 threshold_5_49 threshold_5_50) (join 51 1 2 threshold_5_51 (join 52 1 1 threshold_5_52 threshold_5_53))))) (join 54 9 9 (join 54 4 5 (join 54 2 2 (join 54 1 1 threshold_5_54 threshold_5_55) (join 56 1 1 threshold_5_56 threshold_5_57)) (join 58 2 3 (join 58 1 1 threshold_5_58 threshold_5_59) (join 60 1 2 threshold_5_60 (join 61 1 1 threshold_5_61 threshold_5_62)))) (join 63 4 5 (join 63 2 2 (join 63 1 1 threshold_5_63 threshold_5_64) (join 65 1 1 threshold_5_65 threshold_5_66)) (join 67 2 3 (join 67 1 1 threshold_5_67 threshold_5_68) (join 69 1 2 threshold_5_69 (join 70 1 1 threshold_5_70 threshold_5_71))))))) (join 72 36 37 (join 72 18 18 (join 72 9 9 (join 72 4 5 (join 72 2 2 (join 72 1 1 threshold_5_72 threshold_5_73) (join 74 1 1 threshold_5_74 threshold_5_75)) (join 76 2 3 (join 76 1 1 threshold_5_76 threshold_5_77) (join 78 1 2 threshold_5_78 (join 79 1 1 threshold_5_79 threshold_5_80)))) (join 81 4 5 (join 81 2 2 (join 81 1 1 threshold_5_81 threshold_5_82) (join 83 1 1 threshold_5_83 threshold_5_84)) (join 85 2 3 (join 85 1 1 threshold_5_85 threshold_5_86) (join 87 1 2 threshold_5_87 (join 88 1 1 threshold_5_88 threshold_5_89))))) (join 90 9 9 (join 90 4 5 (join 90 2 2 (join 90 1 1 threshold_5_90 threshold_5_91) (join 92 1 1 threshold_5_92 threshold_5_93)) (join 94 2 3 (join 94 1 1 threshold_5_94 threshold_5_95) (join 96 1 2 threshold_5_96 (join 97 1 1 threshold_5_97 threshold_5_98)))) (join 99 4 5 (join 99 2 2 (join 99 1 1 threshold_5_99 threshold_5_100) (join 101 1 1 threshold_5_101 threshold_5_102)) (join 103 2 3 (join 103 1 1 threshold_5_103 threshold_5_104) (join 105 1 2 threshold_5_105 (join 106 1 1 threshold_5_106 threshold_5_107)))))) (join 108 18 19 (join 108 9 9 (join 108 4 5 (join 108 2 2 (join 108 1 1 threshold_5_108 threshold_5_109) (join 110 1 1 threshold_5_110 threshold_5_111)) (join 112 2 3 (join 112 1 1 threshold_5_112 threshold_5_113) (join 114 1 2 threshold_5_114 (join 115 1 1 threshold_5_115 threshold_5_116)))) (join 117 4 5 (join 117 2 2 (join 117 1 1 threshold_5_117 threshold_5_118) (join 119 1 1 threshold_5_119 threshold_5_120)) (join 121 2 3 (join 121 1 1 threshold_5_121 threshold_5_122) (join 123 1 2 threshold_5_123 (join 124 1 1 threshold_5_124 threshold_5_125))))) (join 126 9 10 (join 126 4 5 (join 126 2 2 (join 126 1 1 threshold_5_126 threshold_5_127) (join 128 1 1 threshold_5_128 threshold_5_129)) (join 130 2 3 (join 130 1 1 threshold_5_130 threshold_5_131) (join 132 1 2 threshold_5_132 (join 133 1 1 threshold_5_133 threshold_5_134)))) (join 135 5 5 (join 135 2 3 (join 135 1 1 threshold_5_135 threshold_5_136) (join 137 1 2 threshold_5_137 (join 138 1 1 threshold_5_138 threshold_5_139))) (join 140 2 3 (join 140 1 1 threshold_5_140 threshold_5_141) (join 142 1 2 threshold_5_142 (join 143 1 1 threshold_5_143 threshold_5_144))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_5_0 : ∀ i ∈ List.range 4, LedgerAt 5 (0+i) := by decide +kernel

theorem ledger_5_4 : ∀ i ∈ List.range 4, LedgerAt 5 (4+i) := by decide +kernel

theorem ledger_5_8 : ∀ i ∈ List.range 4, LedgerAt 5 (8+i) := by decide +kernel

theorem ledger_5_12 : ∀ i ∈ List.range 4, LedgerAt 5 (12+i) := by decide +kernel

theorem ledger_5_16 : ∀ i ∈ List.range 4, LedgerAt 5 (16+i) := by decide +kernel

theorem ledger_5_20 : ∀ i ∈ List.range 4, LedgerAt 5 (20+i) := by decide +kernel

theorem ledger_5_24 : ∀ i ∈ List.range 4, LedgerAt 5 (24+i) := by decide +kernel

theorem ledger_5_28 : ∀ i ∈ List.range 4, LedgerAt 5 (28+i) := by decide +kernel

theorem ledger_5_32 : ∀ i ∈ List.range 4, LedgerAt 5 (32+i) := by decide +kernel

theorem ledger_5_36 : ∀ i ∈ List.range 4, LedgerAt 5 (36+i) := by decide +kernel

theorem ledger_5_40 : ∀ i ∈ List.range 4, LedgerAt 5 (40+i) := by decide +kernel

theorem ledger_5_44 : ∀ i ∈ List.range 4, LedgerAt 5 (44+i) := by decide +kernel

theorem ledger_5_48 : ∀ i ∈ List.range 4, LedgerAt 5 (48+i) := by decide +kernel

theorem ledger_5_52 : ∀ i ∈ List.range 4, LedgerAt 5 (52+i) := by decide +kernel

theorem ledger_5_56 : ∀ i ∈ List.range 4, LedgerAt 5 (56+i) := by decide +kernel

theorem ledger_5_60 : ∀ i ∈ List.range 4, LedgerAt 5 (60+i) := by decide +kernel

theorem ledger_5_64 : ∀ i ∈ List.range 4, LedgerAt 5 (64+i) := by decide +kernel

theorem ledger_5_68 : ∀ i ∈ List.range 4, LedgerAt 5 (68+i) := by decide +kernel

theorem ledger_5_72 : ∀ i ∈ List.range 4, LedgerAt 5 (72+i) := by decide +kernel

theorem ledger_5_76 : ∀ i ∈ List.range 4, LedgerAt 5 (76+i) := by decide +kernel

theorem ledger_5_80 : ∀ i ∈ List.range 4, LedgerAt 5 (80+i) := by decide +kernel

theorem ledger_5_84 : ∀ i ∈ List.range 4, LedgerAt 5 (84+i) := by decide +kernel

theorem ledger_5_88 : ∀ i ∈ List.range 4, LedgerAt 5 (88+i) := by decide +kernel

theorem ledger_5_92 : ∀ i ∈ List.range 4, LedgerAt 5 (92+i) := by decide +kernel

theorem ledger_5_96 : ∀ i ∈ List.range 4, LedgerAt 5 (96+i) := by decide +kernel

theorem ledger_5_100 : ∀ i ∈ List.range 4, LedgerAt 5 (100+i) := by decide +kernel

theorem ledger_5_104 : ∀ i ∈ List.range 4, LedgerAt 5 (104+i) := by decide +kernel

theorem ledger_5_108 : ∀ i ∈ List.range 4, LedgerAt 5 (108+i) := by decide +kernel

theorem ledger_5_112 : ∀ i ∈ List.range 4, LedgerAt 5 (112+i) := by decide +kernel

theorem ledger_5_116 : ∀ i ∈ List.range 4, LedgerAt 5 (116+i) := by decide +kernel

theorem ledger_5_120 : ∀ i ∈ List.range 4, LedgerAt 5 (120+i) := by decide +kernel

theorem ledger_5_124 : ∀ i ∈ List.range 4, LedgerAt 5 (124+i) := by decide +kernel

theorem ledger_5_128 : ∀ i ∈ List.range 4, LedgerAt 5 (128+i) := by decide +kernel

theorem ledger_5_132 : ∀ i ∈ List.range 4, LedgerAt 5 (132+i) := by decide +kernel

theorem ledger_5_136 : ∀ i ∈ List.range 4, LedgerAt 5 (136+i) := by decide +kernel

theorem ledger_5_140 : ∀ i ∈ List.range 4, LedgerAt 5 (140+i) := by decide +kernel

theorem ledger_5_144 : ∀ i ∈ List.range 1, LedgerAt 5 (144+i) := by decide +kernel

theorem ledger_5 (v : ℕ) (hv : v ∈ List.range 145) : LedgerAt 5 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 5 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_5_0 ledger_5_4) (join 8 4 4 ledger_5_8 ledger_5_12)) (join 16 8 12 (join 16 4 4 ledger_5_16 ledger_5_20) (join 24 4 8 ledger_5_24 (join 28 4 4 ledger_5_28 ledger_5_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_5_36 ledger_5_40) (join 44 4 4 ledger_5_44 ledger_5_48)) (join 52 8 12 (join 52 4 4 ledger_5_52 ledger_5_56) (join 60 4 8 ledger_5_60 (join 64 4 4 ledger_5_64 ledger_5_68))))) (join 72 36 37 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_5_72 ledger_5_76) (join 80 4 4 ledger_5_80 ledger_5_84)) (join 88 8 12 (join 88 4 4 ledger_5_88 ledger_5_92) (join 96 4 8 ledger_5_96 (join 100 4 4 ledger_5_100 ledger_5_104)))) (join 108 20 17 (join 108 8 12 (join 108 4 4 ledger_5_108 ledger_5_112) (join 116 4 8 ledger_5_116 (join 120 4 4 ledger_5_120 ledger_5_124))) (join 128 8 9 (join 128 4 4 ledger_5_128 ledger_5_132) (join 136 4 5 ledger_5_136 (join 140 4 1 ledger_5_140 ledger_5_144))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
