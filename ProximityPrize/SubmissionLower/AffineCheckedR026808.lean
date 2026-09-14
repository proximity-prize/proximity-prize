import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_2_0 : ∀ i ∈ List.range 4, SingleAt 2 (0+i) := by decide +kernel

theorem single_2_4 : ∀ i ∈ List.range 4, SingleAt 2 (4+i) := by decide +kernel

theorem single_2_8 : ∀ i ∈ List.range 4, SingleAt 2 (8+i) := by decide +kernel

theorem single_2_12 : ∀ i ∈ List.range 4, SingleAt 2 (12+i) := by decide +kernel

theorem single_2_16 : ∀ i ∈ List.range 4, SingleAt 2 (16+i) := by decide +kernel

theorem single_2_20 : ∀ i ∈ List.range 4, SingleAt 2 (20+i) := by decide +kernel

theorem single_2_24 : ∀ i ∈ List.range 4, SingleAt 2 (24+i) := by decide +kernel

theorem single_2_28 : ∀ i ∈ List.range 4, SingleAt 2 (28+i) := by decide +kernel

theorem single_2_32 : ∀ i ∈ List.range 4, SingleAt 2 (32+i) := by decide +kernel

theorem single_2_36 : ∀ i ∈ List.range 4, SingleAt 2 (36+i) := by decide +kernel

theorem single_2_40 : ∀ i ∈ List.range 4, SingleAt 2 (40+i) := by decide +kernel

theorem single_2_44 : ∀ i ∈ List.range 4, SingleAt 2 (44+i) := by decide +kernel

theorem single_2_48 : ∀ i ∈ List.range 4, SingleAt 2 (48+i) := by decide +kernel

theorem single_2_52 : ∀ i ∈ List.range 4, SingleAt 2 (52+i) := by decide +kernel

theorem single_2_56 : ∀ i ∈ List.range 4, SingleAt 2 (56+i) := by decide +kernel

theorem single_2_60 : ∀ i ∈ List.range 4, SingleAt 2 (60+i) := by decide +kernel

theorem single_2_64 : ∀ i ∈ List.range 4, SingleAt 2 (64+i) := by decide +kernel

theorem single_2_68 : ∀ i ∈ List.range 4, SingleAt 2 (68+i) := by decide +kernel

theorem single_2_72 : ∀ i ∈ List.range 4, SingleAt 2 (72+i) := by decide +kernel

theorem single_2_76 : ∀ i ∈ List.range 4, SingleAt 2 (76+i) := by decide +kernel

theorem single_2_80 : ∀ i ∈ List.range 4, SingleAt 2 (80+i) := by decide +kernel

theorem single_2_84 : ∀ i ∈ List.range 4, SingleAt 2 (84+i) := by decide +kernel

theorem single_2_88 : ∀ i ∈ List.range 4, SingleAt 2 (88+i) := by decide +kernel

theorem single_2_92 : ∀ i ∈ List.range 4, SingleAt 2 (92+i) := by decide +kernel

theorem single_2_96 : ∀ i ∈ List.range 4, SingleAt 2 (96+i) := by decide +kernel

theorem single_2_100 : ∀ i ∈ List.range 4, SingleAt 2 (100+i) := by decide +kernel

theorem single_2_104 : ∀ i ∈ List.range 4, SingleAt 2 (104+i) := by decide +kernel

theorem single_2_108 : ∀ i ∈ List.range 4, SingleAt 2 (108+i) := by decide +kernel

theorem single_2_112 : ∀ i ∈ List.range 4, SingleAt 2 (112+i) := by decide +kernel

theorem single_2_116 : ∀ i ∈ List.range 4, SingleAt 2 (116+i) := by decide +kernel

theorem single_2_120 : ∀ i ∈ List.range 4, SingleAt 2 (120+i) := by decide +kernel

theorem single_2_124 : ∀ i ∈ List.range 4, SingleAt 2 (124+i) := by decide +kernel

theorem single_2_128 : ∀ i ∈ List.range 4, SingleAt 2 (128+i) := by decide +kernel

theorem single_2_132 : ∀ i ∈ List.range 4, SingleAt 2 (132+i) := by decide +kernel

theorem single_2_136 : ∀ i ∈ List.range 4, SingleAt 2 (136+i) := by decide +kernel

theorem single_2_140 : ∀ i ∈ List.range 4, SingleAt 2 (140+i) := by decide +kernel

theorem single_2_144 : ∀ i ∈ List.range 4, SingleAt 2 (144+i) := by decide +kernel

theorem single_2 (v : ℕ) (hv : v ∈ List.range 148) : SingleAt 2 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 2 v)
  have h := (join 0 72 76 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 single_2_0 single_2_4) (join 8 4 4 single_2_8 single_2_12)) (join 16 8 12 (join 16 4 4 single_2_16 single_2_20) (join 24 4 8 single_2_24 (join 28 4 4 single_2_28 single_2_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 single_2_36 single_2_40) (join 44 4 4 single_2_44 single_2_48)) (join 52 8 12 (join 52 4 4 single_2_52 single_2_56) (join 60 4 8 single_2_60 (join 64 4 4 single_2_64 single_2_68))))) (join 72 36 40 (join 72 16 20 (join 72 8 8 (join 72 4 4 single_2_72 single_2_76) (join 80 4 4 single_2_80 single_2_84)) (join 88 8 12 (join 88 4 4 single_2_88 single_2_92) (join 96 4 8 single_2_96 (join 100 4 4 single_2_100 single_2_104)))) (join 108 20 20 (join 108 8 12 (join 108 4 4 single_2_108 single_2_112) (join 116 4 8 single_2_116 (join 120 4 4 single_2_120 single_2_124))) (join 128 8 12 (join 128 4 4 single_2_128 single_2_132) (join 136 4 8 single_2_136 (join 140 4 4 single_2_140 single_2_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_2_0 : ∀ i ∈ List.range 4, PhaseAt 2 (0+i) := by decide +kernel

theorem phase_2_4 : ∀ i ∈ List.range 4, PhaseAt 2 (4+i) := by decide +kernel

theorem phase_2_8 : ∀ i ∈ List.range 4, PhaseAt 2 (8+i) := by decide +kernel

theorem phase_2_12 : ∀ i ∈ List.range 4, PhaseAt 2 (12+i) := by decide +kernel

theorem phase_2_16 : ∀ i ∈ List.range 4, PhaseAt 2 (16+i) := by decide +kernel

theorem phase_2_20 : ∀ i ∈ List.range 4, PhaseAt 2 (20+i) := by decide +kernel

theorem phase_2_24 : ∀ i ∈ List.range 4, PhaseAt 2 (24+i) := by decide +kernel

theorem phase_2_28 : ∀ i ∈ List.range 4, PhaseAt 2 (28+i) := by decide +kernel

theorem phase_2_32 : ∀ i ∈ List.range 4, PhaseAt 2 (32+i) := by decide +kernel

theorem phase_2_36 : ∀ i ∈ List.range 4, PhaseAt 2 (36+i) := by decide +kernel

theorem phase_2_40 : ∀ i ∈ List.range 4, PhaseAt 2 (40+i) := by decide +kernel

theorem phase_2_44 : ∀ i ∈ List.range 4, PhaseAt 2 (44+i) := by decide +kernel

theorem phase_2_48 : ∀ i ∈ List.range 4, PhaseAt 2 (48+i) := by decide +kernel

theorem phase_2_52 : ∀ i ∈ List.range 4, PhaseAt 2 (52+i) := by decide +kernel

theorem phase_2_56 : ∀ i ∈ List.range 4, PhaseAt 2 (56+i) := by decide +kernel

theorem phase_2_60 : ∀ i ∈ List.range 4, PhaseAt 2 (60+i) := by decide +kernel

theorem phase_2_64 : ∀ i ∈ List.range 4, PhaseAt 2 (64+i) := by decide +kernel

theorem phase_2_68 : ∀ i ∈ List.range 4, PhaseAt 2 (68+i) := by decide +kernel

theorem phase_2_72 : ∀ i ∈ List.range 4, PhaseAt 2 (72+i) := by decide +kernel

theorem phase_2_76 : ∀ i ∈ List.range 4, PhaseAt 2 (76+i) := by decide +kernel

theorem phase_2_80 : ∀ i ∈ List.range 4, PhaseAt 2 (80+i) := by decide +kernel

theorem phase_2_84 : ∀ i ∈ List.range 4, PhaseAt 2 (84+i) := by decide +kernel

theorem phase_2_88 : ∀ i ∈ List.range 4, PhaseAt 2 (88+i) := by decide +kernel

theorem phase_2_92 : ∀ i ∈ List.range 4, PhaseAt 2 (92+i) := by decide +kernel

theorem phase_2_96 : ∀ i ∈ List.range 4, PhaseAt 2 (96+i) := by decide +kernel

theorem phase_2_100 : ∀ i ∈ List.range 4, PhaseAt 2 (100+i) := by decide +kernel

theorem phase_2_104 : ∀ i ∈ List.range 4, PhaseAt 2 (104+i) := by decide +kernel

theorem phase_2_108 : ∀ i ∈ List.range 4, PhaseAt 2 (108+i) := by decide +kernel

theorem phase_2_112 : ∀ i ∈ List.range 4, PhaseAt 2 (112+i) := by decide +kernel

theorem phase_2_116 : ∀ i ∈ List.range 4, PhaseAt 2 (116+i) := by decide +kernel

theorem phase_2_120 : ∀ i ∈ List.range 4, PhaseAt 2 (120+i) := by decide +kernel

theorem phase_2_124 : ∀ i ∈ List.range 4, PhaseAt 2 (124+i) := by decide +kernel

theorem phase_2_128 : ∀ i ∈ List.range 4, PhaseAt 2 (128+i) := by decide +kernel

theorem phase_2_132 : ∀ i ∈ List.range 4, PhaseAt 2 (132+i) := by decide +kernel

theorem phase_2_136 : ∀ i ∈ List.range 4, PhaseAt 2 (136+i) := by decide +kernel

theorem phase_2_140 : ∀ i ∈ List.range 4, PhaseAt 2 (140+i) := by decide +kernel

theorem phase_2_144 : ∀ i ∈ List.range 4, PhaseAt 2 (144+i) := by decide +kernel

theorem phase_2 (v : ℕ) (hv : v ∈ List.range 148) : PhaseAt 2 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 2 v)
  have h := (join 0 72 76 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_2_0 phase_2_4) (join 8 4 4 phase_2_8 phase_2_12)) (join 16 8 12 (join 16 4 4 phase_2_16 phase_2_20) (join 24 4 8 phase_2_24 (join 28 4 4 phase_2_28 phase_2_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_2_36 phase_2_40) (join 44 4 4 phase_2_44 phase_2_48)) (join 52 8 12 (join 52 4 4 phase_2_52 phase_2_56) (join 60 4 8 phase_2_60 (join 64 4 4 phase_2_64 phase_2_68))))) (join 72 36 40 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_2_72 phase_2_76) (join 80 4 4 phase_2_80 phase_2_84)) (join 88 8 12 (join 88 4 4 phase_2_88 phase_2_92) (join 96 4 8 phase_2_96 (join 100 4 4 phase_2_100 phase_2_104)))) (join 108 20 20 (join 108 8 12 (join 108 4 4 phase_2_108 phase_2_112) (join 116 4 8 phase_2_116 (join 120 4 4 phase_2_120 phase_2_124))) (join 128 8 12 (join 128 4 4 phase_2_128 phase_2_132) (join 136 4 8 phase_2_136 (join 140 4 4 phase_2_140 phase_2_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_2_0 : ∀ i ∈ List.range 1, ThresholdAt 2 (0+i) := by decide +kernel

theorem threshold_2_1 : ∀ i ∈ List.range 1, ThresholdAt 2 (1+i) := by decide +kernel

theorem threshold_2_2 : ∀ i ∈ List.range 1, ThresholdAt 2 (2+i) := by decide +kernel

theorem threshold_2_3 : ∀ i ∈ List.range 1, ThresholdAt 2 (3+i) := by decide +kernel

theorem threshold_2_4 : ∀ i ∈ List.range 1, ThresholdAt 2 (4+i) := by decide +kernel

theorem threshold_2_5 : ∀ i ∈ List.range 1, ThresholdAt 2 (5+i) := by decide +kernel

theorem threshold_2_6 : ∀ i ∈ List.range 1, ThresholdAt 2 (6+i) := by decide +kernel

theorem threshold_2_7 : ∀ i ∈ List.range 1, ThresholdAt 2 (7+i) := by decide +kernel

theorem threshold_2_8 : ∀ i ∈ List.range 1, ThresholdAt 2 (8+i) := by decide +kernel

theorem threshold_2_9 : ∀ i ∈ List.range 1, ThresholdAt 2 (9+i) := by decide +kernel

theorem threshold_2_10 : ∀ i ∈ List.range 1, ThresholdAt 2 (10+i) := by decide +kernel

theorem threshold_2_11 : ∀ i ∈ List.range 1, ThresholdAt 2 (11+i) := by decide +kernel

theorem threshold_2_12 : ∀ i ∈ List.range 1, ThresholdAt 2 (12+i) := by decide +kernel

theorem threshold_2_13 : ∀ i ∈ List.range 1, ThresholdAt 2 (13+i) := by decide +kernel

theorem threshold_2_14 : ∀ i ∈ List.range 1, ThresholdAt 2 (14+i) := by decide +kernel

theorem threshold_2_15 : ∀ i ∈ List.range 1, ThresholdAt 2 (15+i) := by decide +kernel

theorem threshold_2_16 : ∀ i ∈ List.range 1, ThresholdAt 2 (16+i) := by decide +kernel

theorem threshold_2_17 : ∀ i ∈ List.range 1, ThresholdAt 2 (17+i) := by decide +kernel

theorem threshold_2_18 : ∀ i ∈ List.range 1, ThresholdAt 2 (18+i) := by decide +kernel

theorem threshold_2_19 : ∀ i ∈ List.range 1, ThresholdAt 2 (19+i) := by decide +kernel

theorem threshold_2_20 : ∀ i ∈ List.range 1, ThresholdAt 2 (20+i) := by decide +kernel

theorem threshold_2_21 : ∀ i ∈ List.range 1, ThresholdAt 2 (21+i) := by decide +kernel

theorem threshold_2_22 : ∀ i ∈ List.range 1, ThresholdAt 2 (22+i) := by decide +kernel

theorem threshold_2_23 : ∀ i ∈ List.range 1, ThresholdAt 2 (23+i) := by decide +kernel

theorem threshold_2_24 : ∀ i ∈ List.range 1, ThresholdAt 2 (24+i) := by decide +kernel

theorem threshold_2_25 : ∀ i ∈ List.range 1, ThresholdAt 2 (25+i) := by decide +kernel

theorem threshold_2_26 : ∀ i ∈ List.range 1, ThresholdAt 2 (26+i) := by decide +kernel

theorem threshold_2_27 : ∀ i ∈ List.range 1, ThresholdAt 2 (27+i) := by decide +kernel

theorem threshold_2_28 : ∀ i ∈ List.range 1, ThresholdAt 2 (28+i) := by decide +kernel

theorem threshold_2_29 : ∀ i ∈ List.range 1, ThresholdAt 2 (29+i) := by decide +kernel

theorem threshold_2_30 : ∀ i ∈ List.range 1, ThresholdAt 2 (30+i) := by decide +kernel

theorem threshold_2_31 : ∀ i ∈ List.range 1, ThresholdAt 2 (31+i) := by decide +kernel

theorem threshold_2_32 : ∀ i ∈ List.range 1, ThresholdAt 2 (32+i) := by decide +kernel

theorem threshold_2_33 : ∀ i ∈ List.range 1, ThresholdAt 2 (33+i) := by decide +kernel

theorem threshold_2_34 : ∀ i ∈ List.range 1, ThresholdAt 2 (34+i) := by decide +kernel

theorem threshold_2_35 : ∀ i ∈ List.range 1, ThresholdAt 2 (35+i) := by decide +kernel

theorem threshold_2_36 : ∀ i ∈ List.range 1, ThresholdAt 2 (36+i) := by decide +kernel

theorem threshold_2_37 : ∀ i ∈ List.range 1, ThresholdAt 2 (37+i) := by decide +kernel

theorem threshold_2_38 : ∀ i ∈ List.range 1, ThresholdAt 2 (38+i) := by decide +kernel

theorem threshold_2_39 : ∀ i ∈ List.range 1, ThresholdAt 2 (39+i) := by decide +kernel

theorem threshold_2_40 : ∀ i ∈ List.range 1, ThresholdAt 2 (40+i) := by decide +kernel

theorem threshold_2_41 : ∀ i ∈ List.range 1, ThresholdAt 2 (41+i) := by decide +kernel

theorem threshold_2_42 : ∀ i ∈ List.range 1, ThresholdAt 2 (42+i) := by decide +kernel

theorem threshold_2_43 : ∀ i ∈ List.range 1, ThresholdAt 2 (43+i) := by decide +kernel

theorem threshold_2_44 : ∀ i ∈ List.range 1, ThresholdAt 2 (44+i) := by decide +kernel

theorem threshold_2_45 : ∀ i ∈ List.range 1, ThresholdAt 2 (45+i) := by decide +kernel

theorem threshold_2_46 : ∀ i ∈ List.range 1, ThresholdAt 2 (46+i) := by decide +kernel

theorem threshold_2_47 : ∀ i ∈ List.range 1, ThresholdAt 2 (47+i) := by decide +kernel

theorem threshold_2_48 : ∀ i ∈ List.range 1, ThresholdAt 2 (48+i) := by decide +kernel

theorem threshold_2_49 : ∀ i ∈ List.range 1, ThresholdAt 2 (49+i) := by decide +kernel

theorem threshold_2_50 : ∀ i ∈ List.range 1, ThresholdAt 2 (50+i) := by decide +kernel

theorem threshold_2_51 : ∀ i ∈ List.range 1, ThresholdAt 2 (51+i) := by decide +kernel

theorem threshold_2_52 : ∀ i ∈ List.range 1, ThresholdAt 2 (52+i) := by decide +kernel

theorem threshold_2_53 : ∀ i ∈ List.range 1, ThresholdAt 2 (53+i) := by decide +kernel

theorem threshold_2_54 : ∀ i ∈ List.range 1, ThresholdAt 2 (54+i) := by decide +kernel

theorem threshold_2_55 : ∀ i ∈ List.range 1, ThresholdAt 2 (55+i) := by decide +kernel

theorem threshold_2_56 : ∀ i ∈ List.range 1, ThresholdAt 2 (56+i) := by decide +kernel

theorem threshold_2_57 : ∀ i ∈ List.range 1, ThresholdAt 2 (57+i) := by decide +kernel

theorem threshold_2_58 : ∀ i ∈ List.range 1, ThresholdAt 2 (58+i) := by decide +kernel

theorem threshold_2_59 : ∀ i ∈ List.range 1, ThresholdAt 2 (59+i) := by decide +kernel

theorem threshold_2_60 : ∀ i ∈ List.range 1, ThresholdAt 2 (60+i) := by decide +kernel

theorem threshold_2_61 : ∀ i ∈ List.range 1, ThresholdAt 2 (61+i) := by decide +kernel

theorem threshold_2_62 : ∀ i ∈ List.range 1, ThresholdAt 2 (62+i) := by decide +kernel

theorem threshold_2_63 : ∀ i ∈ List.range 1, ThresholdAt 2 (63+i) := by decide +kernel

theorem threshold_2_64 : ∀ i ∈ List.range 1, ThresholdAt 2 (64+i) := by decide +kernel

theorem threshold_2_65 : ∀ i ∈ List.range 1, ThresholdAt 2 (65+i) := by decide +kernel

theorem threshold_2_66 : ∀ i ∈ List.range 1, ThresholdAt 2 (66+i) := by decide +kernel

theorem threshold_2_67 : ∀ i ∈ List.range 1, ThresholdAt 2 (67+i) := by decide +kernel

theorem threshold_2_68 : ∀ i ∈ List.range 1, ThresholdAt 2 (68+i) := by decide +kernel

theorem threshold_2_69 : ∀ i ∈ List.range 1, ThresholdAt 2 (69+i) := by decide +kernel

theorem threshold_2_70 : ∀ i ∈ List.range 1, ThresholdAt 2 (70+i) := by decide +kernel

theorem threshold_2_71 : ∀ i ∈ List.range 1, ThresholdAt 2 (71+i) := by decide +kernel

theorem threshold_2_72 : ∀ i ∈ List.range 1, ThresholdAt 2 (72+i) := by decide +kernel

theorem threshold_2_73 : ∀ i ∈ List.range 1, ThresholdAt 2 (73+i) := by decide +kernel

theorem threshold_2_74 : ∀ i ∈ List.range 1, ThresholdAt 2 (74+i) := by decide +kernel

theorem threshold_2_75 : ∀ i ∈ List.range 1, ThresholdAt 2 (75+i) := by decide +kernel

theorem threshold_2_76 : ∀ i ∈ List.range 1, ThresholdAt 2 (76+i) := by decide +kernel

theorem threshold_2_77 : ∀ i ∈ List.range 1, ThresholdAt 2 (77+i) := by decide +kernel

theorem threshold_2_78 : ∀ i ∈ List.range 1, ThresholdAt 2 (78+i) := by decide +kernel

theorem threshold_2_79 : ∀ i ∈ List.range 1, ThresholdAt 2 (79+i) := by decide +kernel

theorem threshold_2_80 : ∀ i ∈ List.range 1, ThresholdAt 2 (80+i) := by decide +kernel

theorem threshold_2_81 : ∀ i ∈ List.range 1, ThresholdAt 2 (81+i) := by decide +kernel

theorem threshold_2_82 : ∀ i ∈ List.range 1, ThresholdAt 2 (82+i) := by decide +kernel

theorem threshold_2_83 : ∀ i ∈ List.range 1, ThresholdAt 2 (83+i) := by decide +kernel

theorem threshold_2_84 : ∀ i ∈ List.range 1, ThresholdAt 2 (84+i) := by decide +kernel

theorem threshold_2_85 : ∀ i ∈ List.range 1, ThresholdAt 2 (85+i) := by decide +kernel

theorem threshold_2_86 : ∀ i ∈ List.range 1, ThresholdAt 2 (86+i) := by decide +kernel

theorem threshold_2_87 : ∀ i ∈ List.range 1, ThresholdAt 2 (87+i) := by decide +kernel

theorem threshold_2_88 : ∀ i ∈ List.range 1, ThresholdAt 2 (88+i) := by decide +kernel

theorem threshold_2_89 : ∀ i ∈ List.range 1, ThresholdAt 2 (89+i) := by decide +kernel

theorem threshold_2_90 : ∀ i ∈ List.range 1, ThresholdAt 2 (90+i) := by decide +kernel

theorem threshold_2_91 : ∀ i ∈ List.range 1, ThresholdAt 2 (91+i) := by decide +kernel

theorem threshold_2_92 : ∀ i ∈ List.range 1, ThresholdAt 2 (92+i) := by decide +kernel

theorem threshold_2_93 : ∀ i ∈ List.range 1, ThresholdAt 2 (93+i) := by decide +kernel

theorem threshold_2_94 : ∀ i ∈ List.range 1, ThresholdAt 2 (94+i) := by decide +kernel

theorem threshold_2_95 : ∀ i ∈ List.range 1, ThresholdAt 2 (95+i) := by decide +kernel

theorem threshold_2_96 : ∀ i ∈ List.range 1, ThresholdAt 2 (96+i) := by decide +kernel

theorem threshold_2_97 : ∀ i ∈ List.range 1, ThresholdAt 2 (97+i) := by decide +kernel

theorem threshold_2_98 : ∀ i ∈ List.range 1, ThresholdAt 2 (98+i) := by decide +kernel

theorem threshold_2_99 : ∀ i ∈ List.range 1, ThresholdAt 2 (99+i) := by decide +kernel

theorem threshold_2_100 : ∀ i ∈ List.range 1, ThresholdAt 2 (100+i) := by decide +kernel

theorem threshold_2_101 : ∀ i ∈ List.range 1, ThresholdAt 2 (101+i) := by decide +kernel

theorem threshold_2_102 : ∀ i ∈ List.range 1, ThresholdAt 2 (102+i) := by decide +kernel

theorem threshold_2_103 : ∀ i ∈ List.range 1, ThresholdAt 2 (103+i) := by decide +kernel

theorem threshold_2_104 : ∀ i ∈ List.range 1, ThresholdAt 2 (104+i) := by decide +kernel

theorem threshold_2_105 : ∀ i ∈ List.range 1, ThresholdAt 2 (105+i) := by decide +kernel

theorem threshold_2_106 : ∀ i ∈ List.range 1, ThresholdAt 2 (106+i) := by decide +kernel

theorem threshold_2_107 : ∀ i ∈ List.range 1, ThresholdAt 2 (107+i) := by decide +kernel

theorem threshold_2_108 : ∀ i ∈ List.range 1, ThresholdAt 2 (108+i) := by decide +kernel

theorem threshold_2_109 : ∀ i ∈ List.range 1, ThresholdAt 2 (109+i) := by decide +kernel

theorem threshold_2_110 : ∀ i ∈ List.range 1, ThresholdAt 2 (110+i) := by decide +kernel

theorem threshold_2_111 : ∀ i ∈ List.range 1, ThresholdAt 2 (111+i) := by decide +kernel

theorem threshold_2_112 : ∀ i ∈ List.range 1, ThresholdAt 2 (112+i) := by decide +kernel

theorem threshold_2_113 : ∀ i ∈ List.range 1, ThresholdAt 2 (113+i) := by decide +kernel

theorem threshold_2_114 : ∀ i ∈ List.range 1, ThresholdAt 2 (114+i) := by decide +kernel

theorem threshold_2_115 : ∀ i ∈ List.range 1, ThresholdAt 2 (115+i) := by decide +kernel

theorem threshold_2_116 : ∀ i ∈ List.range 1, ThresholdAt 2 (116+i) := by decide +kernel

theorem threshold_2_117 : ∀ i ∈ List.range 1, ThresholdAt 2 (117+i) := by decide +kernel

theorem threshold_2_118 : ∀ i ∈ List.range 1, ThresholdAt 2 (118+i) := by decide +kernel

theorem threshold_2_119 : ∀ i ∈ List.range 1, ThresholdAt 2 (119+i) := by decide +kernel

theorem threshold_2_120 : ∀ i ∈ List.range 1, ThresholdAt 2 (120+i) := by decide +kernel

theorem threshold_2_121 : ∀ i ∈ List.range 1, ThresholdAt 2 (121+i) := by decide +kernel

theorem threshold_2_122 : ∀ i ∈ List.range 1, ThresholdAt 2 (122+i) := by decide +kernel

theorem threshold_2_123 : ∀ i ∈ List.range 1, ThresholdAt 2 (123+i) := by decide +kernel

theorem threshold_2_124 : ∀ i ∈ List.range 1, ThresholdAt 2 (124+i) := by decide +kernel

theorem threshold_2_125 : ∀ i ∈ List.range 1, ThresholdAt 2 (125+i) := by decide +kernel

theorem threshold_2_126 : ∀ i ∈ List.range 1, ThresholdAt 2 (126+i) := by decide +kernel

theorem threshold_2_127 : ∀ i ∈ List.range 1, ThresholdAt 2 (127+i) := by decide +kernel

theorem threshold_2_128 : ∀ i ∈ List.range 1, ThresholdAt 2 (128+i) := by decide +kernel

theorem threshold_2_129 : ∀ i ∈ List.range 1, ThresholdAt 2 (129+i) := by decide +kernel

theorem threshold_2_130 : ∀ i ∈ List.range 1, ThresholdAt 2 (130+i) := by decide +kernel

theorem threshold_2_131 : ∀ i ∈ List.range 1, ThresholdAt 2 (131+i) := by decide +kernel

theorem threshold_2_132 : ∀ i ∈ List.range 1, ThresholdAt 2 (132+i) := by decide +kernel

theorem threshold_2_133 : ∀ i ∈ List.range 1, ThresholdAt 2 (133+i) := by decide +kernel

theorem threshold_2_134 : ∀ i ∈ List.range 1, ThresholdAt 2 (134+i) := by decide +kernel

theorem threshold_2_135 : ∀ i ∈ List.range 1, ThresholdAt 2 (135+i) := by decide +kernel

theorem threshold_2_136 : ∀ i ∈ List.range 1, ThresholdAt 2 (136+i) := by decide +kernel

theorem threshold_2_137 : ∀ i ∈ List.range 1, ThresholdAt 2 (137+i) := by decide +kernel

theorem threshold_2_138 : ∀ i ∈ List.range 1, ThresholdAt 2 (138+i) := by decide +kernel

theorem threshold_2_139 : ∀ i ∈ List.range 1, ThresholdAt 2 (139+i) := by decide +kernel

theorem threshold_2_140 : ∀ i ∈ List.range 1, ThresholdAt 2 (140+i) := by decide +kernel

theorem threshold_2_141 : ∀ i ∈ List.range 1, ThresholdAt 2 (141+i) := by decide +kernel

theorem threshold_2_142 : ∀ i ∈ List.range 1, ThresholdAt 2 (142+i) := by decide +kernel

theorem threshold_2_143 : ∀ i ∈ List.range 1, ThresholdAt 2 (143+i) := by decide +kernel

theorem threshold_2_144 : ∀ i ∈ List.range 1, ThresholdAt 2 (144+i) := by decide +kernel

theorem threshold_2_145 : ∀ i ∈ List.range 1, ThresholdAt 2 (145+i) := by decide +kernel

theorem threshold_2_146 : ∀ i ∈ List.range 1, ThresholdAt 2 (146+i) := by decide +kernel

theorem threshold_2_147 : ∀ i ∈ List.range 1, ThresholdAt 2 (147+i) := by decide +kernel

theorem threshold_2 (v : ℕ) (hv : v ∈ List.range 148) : ThresholdAt 2 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 2 v)
  have h := (join 0 74 74 (join 0 37 37 (join 0 18 19 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_2_0 threshold_2_1) (join 2 1 1 threshold_2_2 threshold_2_3)) (join 4 2 3 (join 4 1 1 threshold_2_4 threshold_2_5) (join 6 1 2 threshold_2_6 (join 7 1 1 threshold_2_7 threshold_2_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 threshold_2_9 threshold_2_10) (join 11 1 1 threshold_2_11 threshold_2_12)) (join 13 2 3 (join 13 1 1 threshold_2_13 threshold_2_14) (join 15 1 2 threshold_2_15 (join 16 1 1 threshold_2_16 threshold_2_17))))) (join 18 9 10 (join 18 4 5 (join 18 2 2 (join 18 1 1 threshold_2_18 threshold_2_19) (join 20 1 1 threshold_2_20 threshold_2_21)) (join 22 2 3 (join 22 1 1 threshold_2_22 threshold_2_23) (join 24 1 2 threshold_2_24 (join 25 1 1 threshold_2_25 threshold_2_26)))) (join 27 5 5 (join 27 2 3 (join 27 1 1 threshold_2_27 threshold_2_28) (join 29 1 2 threshold_2_29 (join 30 1 1 threshold_2_30 threshold_2_31))) (join 32 2 3 (join 32 1 1 threshold_2_32 threshold_2_33) (join 34 1 2 threshold_2_34 (join 35 1 1 threshold_2_35 threshold_2_36)))))) (join 37 18 19 (join 37 9 9 (join 37 4 5 (join 37 2 2 (join 37 1 1 threshold_2_37 threshold_2_38) (join 39 1 1 threshold_2_39 threshold_2_40)) (join 41 2 3 (join 41 1 1 threshold_2_41 threshold_2_42) (join 43 1 2 threshold_2_43 (join 44 1 1 threshold_2_44 threshold_2_45)))) (join 46 4 5 (join 46 2 2 (join 46 1 1 threshold_2_46 threshold_2_47) (join 48 1 1 threshold_2_48 threshold_2_49)) (join 50 2 3 (join 50 1 1 threshold_2_50 threshold_2_51) (join 52 1 2 threshold_2_52 (join 53 1 1 threshold_2_53 threshold_2_54))))) (join 55 9 10 (join 55 4 5 (join 55 2 2 (join 55 1 1 threshold_2_55 threshold_2_56) (join 57 1 1 threshold_2_57 threshold_2_58)) (join 59 2 3 (join 59 1 1 threshold_2_59 threshold_2_60) (join 61 1 2 threshold_2_61 (join 62 1 1 threshold_2_62 threshold_2_63)))) (join 64 5 5 (join 64 2 3 (join 64 1 1 threshold_2_64 threshold_2_65) (join 66 1 2 threshold_2_66 (join 67 1 1 threshold_2_67 threshold_2_68))) (join 69 2 3 (join 69 1 1 threshold_2_69 threshold_2_70) (join 71 1 2 threshold_2_71 (join 72 1 1 threshold_2_72 threshold_2_73))))))) (join 74 37 37 (join 74 18 19 (join 74 9 9 (join 74 4 5 (join 74 2 2 (join 74 1 1 threshold_2_74 threshold_2_75) (join 76 1 1 threshold_2_76 threshold_2_77)) (join 78 2 3 (join 78 1 1 threshold_2_78 threshold_2_79) (join 80 1 2 threshold_2_80 (join 81 1 1 threshold_2_81 threshold_2_82)))) (join 83 4 5 (join 83 2 2 (join 83 1 1 threshold_2_83 threshold_2_84) (join 85 1 1 threshold_2_85 threshold_2_86)) (join 87 2 3 (join 87 1 1 threshold_2_87 threshold_2_88) (join 89 1 2 threshold_2_89 (join 90 1 1 threshold_2_90 threshold_2_91))))) (join 92 9 10 (join 92 4 5 (join 92 2 2 (join 92 1 1 threshold_2_92 threshold_2_93) (join 94 1 1 threshold_2_94 threshold_2_95)) (join 96 2 3 (join 96 1 1 threshold_2_96 threshold_2_97) (join 98 1 2 threshold_2_98 (join 99 1 1 threshold_2_99 threshold_2_100)))) (join 101 5 5 (join 101 2 3 (join 101 1 1 threshold_2_101 threshold_2_102) (join 103 1 2 threshold_2_103 (join 104 1 1 threshold_2_104 threshold_2_105))) (join 106 2 3 (join 106 1 1 threshold_2_106 threshold_2_107) (join 108 1 2 threshold_2_108 (join 109 1 1 threshold_2_109 threshold_2_110)))))) (join 111 18 19 (join 111 9 9 (join 111 4 5 (join 111 2 2 (join 111 1 1 threshold_2_111 threshold_2_112) (join 113 1 1 threshold_2_113 threshold_2_114)) (join 115 2 3 (join 115 1 1 threshold_2_115 threshold_2_116) (join 117 1 2 threshold_2_117 (join 118 1 1 threshold_2_118 threshold_2_119)))) (join 120 4 5 (join 120 2 2 (join 120 1 1 threshold_2_120 threshold_2_121) (join 122 1 1 threshold_2_122 threshold_2_123)) (join 124 2 3 (join 124 1 1 threshold_2_124 threshold_2_125) (join 126 1 2 threshold_2_126 (join 127 1 1 threshold_2_127 threshold_2_128))))) (join 129 9 10 (join 129 4 5 (join 129 2 2 (join 129 1 1 threshold_2_129 threshold_2_130) (join 131 1 1 threshold_2_131 threshold_2_132)) (join 133 2 3 (join 133 1 1 threshold_2_133 threshold_2_134) (join 135 1 2 threshold_2_135 (join 136 1 1 threshold_2_136 threshold_2_137)))) (join 138 5 5 (join 138 2 3 (join 138 1 1 threshold_2_138 threshold_2_139) (join 140 1 2 threshold_2_140 (join 141 1 1 threshold_2_141 threshold_2_142))) (join 143 2 3 (join 143 1 1 threshold_2_143 threshold_2_144) (join 145 1 2 threshold_2_145 (join 146 1 1 threshold_2_146 threshold_2_147))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_2_0 : ∀ i ∈ List.range 4, LedgerAt 2 (0+i) := by decide +kernel

theorem ledger_2_4 : ∀ i ∈ List.range 4, LedgerAt 2 (4+i) := by decide +kernel

theorem ledger_2_8 : ∀ i ∈ List.range 4, LedgerAt 2 (8+i) := by decide +kernel

theorem ledger_2_12 : ∀ i ∈ List.range 4, LedgerAt 2 (12+i) := by decide +kernel

theorem ledger_2_16 : ∀ i ∈ List.range 4, LedgerAt 2 (16+i) := by decide +kernel

theorem ledger_2_20 : ∀ i ∈ List.range 4, LedgerAt 2 (20+i) := by decide +kernel

theorem ledger_2_24 : ∀ i ∈ List.range 4, LedgerAt 2 (24+i) := by decide +kernel

theorem ledger_2_28 : ∀ i ∈ List.range 4, LedgerAt 2 (28+i) := by decide +kernel

theorem ledger_2_32 : ∀ i ∈ List.range 4, LedgerAt 2 (32+i) := by decide +kernel

theorem ledger_2_36 : ∀ i ∈ List.range 4, LedgerAt 2 (36+i) := by decide +kernel

theorem ledger_2_40 : ∀ i ∈ List.range 4, LedgerAt 2 (40+i) := by decide +kernel

theorem ledger_2_44 : ∀ i ∈ List.range 4, LedgerAt 2 (44+i) := by decide +kernel

theorem ledger_2_48 : ∀ i ∈ List.range 4, LedgerAt 2 (48+i) := by decide +kernel

theorem ledger_2_52 : ∀ i ∈ List.range 4, LedgerAt 2 (52+i) := by decide +kernel

theorem ledger_2_56 : ∀ i ∈ List.range 4, LedgerAt 2 (56+i) := by decide +kernel

theorem ledger_2_60 : ∀ i ∈ List.range 4, LedgerAt 2 (60+i) := by decide +kernel

theorem ledger_2_64 : ∀ i ∈ List.range 4, LedgerAt 2 (64+i) := by decide +kernel

theorem ledger_2_68 : ∀ i ∈ List.range 4, LedgerAt 2 (68+i) := by decide +kernel

theorem ledger_2_72 : ∀ i ∈ List.range 4, LedgerAt 2 (72+i) := by decide +kernel

theorem ledger_2_76 : ∀ i ∈ List.range 4, LedgerAt 2 (76+i) := by decide +kernel

theorem ledger_2_80 : ∀ i ∈ List.range 4, LedgerAt 2 (80+i) := by decide +kernel

theorem ledger_2_84 : ∀ i ∈ List.range 4, LedgerAt 2 (84+i) := by decide +kernel

theorem ledger_2_88 : ∀ i ∈ List.range 4, LedgerAt 2 (88+i) := by decide +kernel

theorem ledger_2_92 : ∀ i ∈ List.range 4, LedgerAt 2 (92+i) := by decide +kernel

theorem ledger_2_96 : ∀ i ∈ List.range 4, LedgerAt 2 (96+i) := by decide +kernel

theorem ledger_2_100 : ∀ i ∈ List.range 4, LedgerAt 2 (100+i) := by decide +kernel

theorem ledger_2_104 : ∀ i ∈ List.range 4, LedgerAt 2 (104+i) := by decide +kernel

theorem ledger_2_108 : ∀ i ∈ List.range 4, LedgerAt 2 (108+i) := by decide +kernel

theorem ledger_2_112 : ∀ i ∈ List.range 4, LedgerAt 2 (112+i) := by decide +kernel

theorem ledger_2_116 : ∀ i ∈ List.range 4, LedgerAt 2 (116+i) := by decide +kernel

theorem ledger_2_120 : ∀ i ∈ List.range 4, LedgerAt 2 (120+i) := by decide +kernel

theorem ledger_2_124 : ∀ i ∈ List.range 4, LedgerAt 2 (124+i) := by decide +kernel

theorem ledger_2_128 : ∀ i ∈ List.range 4, LedgerAt 2 (128+i) := by decide +kernel

theorem ledger_2_132 : ∀ i ∈ List.range 4, LedgerAt 2 (132+i) := by decide +kernel

theorem ledger_2_136 : ∀ i ∈ List.range 4, LedgerAt 2 (136+i) := by decide +kernel

theorem ledger_2_140 : ∀ i ∈ List.range 4, LedgerAt 2 (140+i) := by decide +kernel

theorem ledger_2_144 : ∀ i ∈ List.range 4, LedgerAt 2 (144+i) := by decide +kernel

theorem ledger_2 (v : ℕ) (hv : v ∈ List.range 148) : LedgerAt 2 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 2 v)
  have h := (join 0 72 76 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_2_0 ledger_2_4) (join 8 4 4 ledger_2_8 ledger_2_12)) (join 16 8 12 (join 16 4 4 ledger_2_16 ledger_2_20) (join 24 4 8 ledger_2_24 (join 28 4 4 ledger_2_28 ledger_2_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_2_36 ledger_2_40) (join 44 4 4 ledger_2_44 ledger_2_48)) (join 52 8 12 (join 52 4 4 ledger_2_52 ledger_2_56) (join 60 4 8 ledger_2_60 (join 64 4 4 ledger_2_64 ledger_2_68))))) (join 72 36 40 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_2_72 ledger_2_76) (join 80 4 4 ledger_2_80 ledger_2_84)) (join 88 8 12 (join 88 4 4 ledger_2_88 ledger_2_92) (join 96 4 8 ledger_2_96 (join 100 4 4 ledger_2_100 ledger_2_104)))) (join 108 20 20 (join 108 8 12 (join 108 4 4 ledger_2_108 ledger_2_112) (join 116 4 8 ledger_2_116 (join 120 4 4 ledger_2_120 ledger_2_124))) (join 128 8 12 (join 128 4 4 ledger_2_128 ledger_2_132) (join 136 4 8 ledger_2_136 (join 140 4 4 ledger_2_140 ledger_2_144))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
