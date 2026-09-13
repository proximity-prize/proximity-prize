import ProximityPrize.SubmissionLower.AffineCheckedR176808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_18_0 : ∀ i ∈ List.range 4, SingleAt 18 (0+i) := by decide +kernel

theorem single_18_4 : ∀ i ∈ List.range 4, SingleAt 18 (4+i) := by decide +kernel

theorem single_18_8 : ∀ i ∈ List.range 4, SingleAt 18 (8+i) := by decide +kernel

theorem single_18_12 : ∀ i ∈ List.range 4, SingleAt 18 (12+i) := by decide +kernel

theorem single_18_16 : ∀ i ∈ List.range 4, SingleAt 18 (16+i) := by decide +kernel

theorem single_18_20 : ∀ i ∈ List.range 4, SingleAt 18 (20+i) := by decide +kernel

theorem single_18_24 : ∀ i ∈ List.range 4, SingleAt 18 (24+i) := by decide +kernel

theorem single_18_28 : ∀ i ∈ List.range 4, SingleAt 18 (28+i) := by decide +kernel

theorem single_18_32 : ∀ i ∈ List.range 4, SingleAt 18 (32+i) := by decide +kernel

theorem single_18_36 : ∀ i ∈ List.range 4, SingleAt 18 (36+i) := by decide +kernel

theorem single_18_40 : ∀ i ∈ List.range 4, SingleAt 18 (40+i) := by decide +kernel

theorem single_18_44 : ∀ i ∈ List.range 4, SingleAt 18 (44+i) := by decide +kernel

theorem single_18_48 : ∀ i ∈ List.range 4, SingleAt 18 (48+i) := by decide +kernel

theorem single_18_52 : ∀ i ∈ List.range 4, SingleAt 18 (52+i) := by decide +kernel

theorem single_18_56 : ∀ i ∈ List.range 4, SingleAt 18 (56+i) := by decide +kernel

theorem single_18_60 : ∀ i ∈ List.range 4, SingleAt 18 (60+i) := by decide +kernel

theorem single_18_64 : ∀ i ∈ List.range 4, SingleAt 18 (64+i) := by decide +kernel

theorem single_18_68 : ∀ i ∈ List.range 4, SingleAt 18 (68+i) := by decide +kernel

theorem single_18_72 : ∀ i ∈ List.range 4, SingleAt 18 (72+i) := by decide +kernel

theorem single_18_76 : ∀ i ∈ List.range 4, SingleAt 18 (76+i) := by decide +kernel

theorem single_18_80 : ∀ i ∈ List.range 4, SingleAt 18 (80+i) := by decide +kernel

theorem single_18_84 : ∀ i ∈ List.range 4, SingleAt 18 (84+i) := by decide +kernel

theorem single_18_88 : ∀ i ∈ List.range 4, SingleAt 18 (88+i) := by decide +kernel

theorem single_18_92 : ∀ i ∈ List.range 4, SingleAt 18 (92+i) := by decide +kernel

theorem single_18_96 : ∀ i ∈ List.range 4, SingleAt 18 (96+i) := by decide +kernel

theorem single_18_100 : ∀ i ∈ List.range 4, SingleAt 18 (100+i) := by decide +kernel

theorem single_18_104 : ∀ i ∈ List.range 4, SingleAt 18 (104+i) := by decide +kernel

theorem single_18_108 : ∀ i ∈ List.range 4, SingleAt 18 (108+i) := by decide +kernel

theorem single_18_112 : ∀ i ∈ List.range 4, SingleAt 18 (112+i) := by decide +kernel

theorem single_18_116 : ∀ i ∈ List.range 4, SingleAt 18 (116+i) := by decide +kernel

theorem single_18_120 : ∀ i ∈ List.range 4, SingleAt 18 (120+i) := by decide +kernel

theorem single_18_124 : ∀ i ∈ List.range 4, SingleAt 18 (124+i) := by decide +kernel

theorem single_18_128 : ∀ i ∈ List.range 4, SingleAt 18 (128+i) := by decide +kernel

theorem single_18 (v : ℕ) (hv : v ∈ List.range 132) : SingleAt 18 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 18 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_18_0 single_18_4) (join 8 4 4 single_18_8 single_18_12)) (join 16 8 8 (join 16 4 4 single_18_16 single_18_20) (join 24 4 4 single_18_24 single_18_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_18_32 single_18_36) (join 40 4 4 single_18_40 single_18_44)) (join 48 8 8 (join 48 4 4 single_18_48 single_18_52) (join 56 4 4 single_18_56 single_18_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_18_64 single_18_68) (join 72 4 4 single_18_72 single_18_76)) (join 80 8 8 (join 80 4 4 single_18_80 single_18_84) (join 88 4 4 single_18_88 single_18_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 single_18_96 single_18_100) (join 104 4 4 single_18_104 single_18_108)) (join 112 8 12 (join 112 4 4 single_18_112 single_18_116) (join 120 4 8 single_18_120 (join 124 4 4 single_18_124 single_18_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_18_0 : ∀ i ∈ List.range 4, PhaseAt 18 (0+i) := by decide +kernel

theorem phase_18_4 : ∀ i ∈ List.range 4, PhaseAt 18 (4+i) := by decide +kernel

theorem phase_18_8 : ∀ i ∈ List.range 4, PhaseAt 18 (8+i) := by decide +kernel

theorem phase_18_12 : ∀ i ∈ List.range 4, PhaseAt 18 (12+i) := by decide +kernel

theorem phase_18_16 : ∀ i ∈ List.range 4, PhaseAt 18 (16+i) := by decide +kernel

theorem phase_18_20 : ∀ i ∈ List.range 4, PhaseAt 18 (20+i) := by decide +kernel

theorem phase_18_24 : ∀ i ∈ List.range 4, PhaseAt 18 (24+i) := by decide +kernel

theorem phase_18_28 : ∀ i ∈ List.range 4, PhaseAt 18 (28+i) := by decide +kernel

theorem phase_18_32 : ∀ i ∈ List.range 4, PhaseAt 18 (32+i) := by decide +kernel

theorem phase_18_36 : ∀ i ∈ List.range 4, PhaseAt 18 (36+i) := by decide +kernel

theorem phase_18_40 : ∀ i ∈ List.range 4, PhaseAt 18 (40+i) := by decide +kernel

theorem phase_18_44 : ∀ i ∈ List.range 4, PhaseAt 18 (44+i) := by decide +kernel

theorem phase_18_48 : ∀ i ∈ List.range 4, PhaseAt 18 (48+i) := by decide +kernel

theorem phase_18_52 : ∀ i ∈ List.range 4, PhaseAt 18 (52+i) := by decide +kernel

theorem phase_18_56 : ∀ i ∈ List.range 4, PhaseAt 18 (56+i) := by decide +kernel

theorem phase_18_60 : ∀ i ∈ List.range 4, PhaseAt 18 (60+i) := by decide +kernel

theorem phase_18_64 : ∀ i ∈ List.range 4, PhaseAt 18 (64+i) := by decide +kernel

theorem phase_18_68 : ∀ i ∈ List.range 4, PhaseAt 18 (68+i) := by decide +kernel

theorem phase_18_72 : ∀ i ∈ List.range 4, PhaseAt 18 (72+i) := by decide +kernel

theorem phase_18_76 : ∀ i ∈ List.range 4, PhaseAt 18 (76+i) := by decide +kernel

theorem phase_18_80 : ∀ i ∈ List.range 4, PhaseAt 18 (80+i) := by decide +kernel

theorem phase_18_84 : ∀ i ∈ List.range 4, PhaseAt 18 (84+i) := by decide +kernel

theorem phase_18_88 : ∀ i ∈ List.range 4, PhaseAt 18 (88+i) := by decide +kernel

theorem phase_18_92 : ∀ i ∈ List.range 4, PhaseAt 18 (92+i) := by decide +kernel

theorem phase_18_96 : ∀ i ∈ List.range 4, PhaseAt 18 (96+i) := by decide +kernel

theorem phase_18_100 : ∀ i ∈ List.range 4, PhaseAt 18 (100+i) := by decide +kernel

theorem phase_18_104 : ∀ i ∈ List.range 4, PhaseAt 18 (104+i) := by decide +kernel

theorem phase_18_108 : ∀ i ∈ List.range 4, PhaseAt 18 (108+i) := by decide +kernel

theorem phase_18_112 : ∀ i ∈ List.range 4, PhaseAt 18 (112+i) := by decide +kernel

theorem phase_18_116 : ∀ i ∈ List.range 4, PhaseAt 18 (116+i) := by decide +kernel

theorem phase_18_120 : ∀ i ∈ List.range 4, PhaseAt 18 (120+i) := by decide +kernel

theorem phase_18_124 : ∀ i ∈ List.range 4, PhaseAt 18 (124+i) := by decide +kernel

theorem phase_18_128 : ∀ i ∈ List.range 4, PhaseAt 18 (128+i) := by decide +kernel

theorem phase_18 (v : ℕ) (hv : v ∈ List.range 132) : PhaseAt 18 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 18 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_18_0 phase_18_4) (join 8 4 4 phase_18_8 phase_18_12)) (join 16 8 8 (join 16 4 4 phase_18_16 phase_18_20) (join 24 4 4 phase_18_24 phase_18_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_18_32 phase_18_36) (join 40 4 4 phase_18_40 phase_18_44)) (join 48 8 8 (join 48 4 4 phase_18_48 phase_18_52) (join 56 4 4 phase_18_56 phase_18_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_18_64 phase_18_68) (join 72 4 4 phase_18_72 phase_18_76)) (join 80 8 8 (join 80 4 4 phase_18_80 phase_18_84) (join 88 4 4 phase_18_88 phase_18_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 phase_18_96 phase_18_100) (join 104 4 4 phase_18_104 phase_18_108)) (join 112 8 12 (join 112 4 4 phase_18_112 phase_18_116) (join 120 4 8 phase_18_120 (join 124 4 4 phase_18_124 phase_18_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_18_0 : ∀ i ∈ List.range 1, ThresholdAt 18 (0+i) := by decide +kernel

theorem threshold_18_1 : ∀ i ∈ List.range 1, ThresholdAt 18 (1+i) := by decide +kernel

theorem threshold_18_2 : ∀ i ∈ List.range 1, ThresholdAt 18 (2+i) := by decide +kernel

theorem threshold_18_3 : ∀ i ∈ List.range 1, ThresholdAt 18 (3+i) := by decide +kernel

theorem threshold_18_4 : ∀ i ∈ List.range 1, ThresholdAt 18 (4+i) := by decide +kernel

theorem threshold_18_5 : ∀ i ∈ List.range 1, ThresholdAt 18 (5+i) := by decide +kernel

theorem threshold_18_6 : ∀ i ∈ List.range 1, ThresholdAt 18 (6+i) := by decide +kernel

theorem threshold_18_7 : ∀ i ∈ List.range 1, ThresholdAt 18 (7+i) := by decide +kernel

theorem threshold_18_8 : ∀ i ∈ List.range 1, ThresholdAt 18 (8+i) := by decide +kernel

theorem threshold_18_9 : ∀ i ∈ List.range 1, ThresholdAt 18 (9+i) := by decide +kernel

theorem threshold_18_10 : ∀ i ∈ List.range 1, ThresholdAt 18 (10+i) := by decide +kernel

theorem threshold_18_11 : ∀ i ∈ List.range 1, ThresholdAt 18 (11+i) := by decide +kernel

theorem threshold_18_12 : ∀ i ∈ List.range 1, ThresholdAt 18 (12+i) := by decide +kernel

theorem threshold_18_13 : ∀ i ∈ List.range 1, ThresholdAt 18 (13+i) := by decide +kernel

theorem threshold_18_14 : ∀ i ∈ List.range 1, ThresholdAt 18 (14+i) := by decide +kernel

theorem threshold_18_15 : ∀ i ∈ List.range 1, ThresholdAt 18 (15+i) := by decide +kernel

theorem threshold_18_16 : ∀ i ∈ List.range 1, ThresholdAt 18 (16+i) := by decide +kernel

theorem threshold_18_17 : ∀ i ∈ List.range 1, ThresholdAt 18 (17+i) := by decide +kernel

theorem threshold_18_18 : ∀ i ∈ List.range 1, ThresholdAt 18 (18+i) := by decide +kernel

theorem threshold_18_19 : ∀ i ∈ List.range 1, ThresholdAt 18 (19+i) := by decide +kernel

theorem threshold_18_20 : ∀ i ∈ List.range 1, ThresholdAt 18 (20+i) := by decide +kernel

theorem threshold_18_21 : ∀ i ∈ List.range 1, ThresholdAt 18 (21+i) := by decide +kernel

theorem threshold_18_22 : ∀ i ∈ List.range 1, ThresholdAt 18 (22+i) := by decide +kernel

theorem threshold_18_23 : ∀ i ∈ List.range 1, ThresholdAt 18 (23+i) := by decide +kernel

theorem threshold_18_24 : ∀ i ∈ List.range 1, ThresholdAt 18 (24+i) := by decide +kernel

theorem threshold_18_25 : ∀ i ∈ List.range 1, ThresholdAt 18 (25+i) := by decide +kernel

theorem threshold_18_26 : ∀ i ∈ List.range 1, ThresholdAt 18 (26+i) := by decide +kernel

theorem threshold_18_27 : ∀ i ∈ List.range 1, ThresholdAt 18 (27+i) := by decide +kernel

theorem threshold_18_28 : ∀ i ∈ List.range 1, ThresholdAt 18 (28+i) := by decide +kernel

theorem threshold_18_29 : ∀ i ∈ List.range 1, ThresholdAt 18 (29+i) := by decide +kernel

theorem threshold_18_30 : ∀ i ∈ List.range 1, ThresholdAt 18 (30+i) := by decide +kernel

theorem threshold_18_31 : ∀ i ∈ List.range 1, ThresholdAt 18 (31+i) := by decide +kernel

theorem threshold_18_32 : ∀ i ∈ List.range 1, ThresholdAt 18 (32+i) := by decide +kernel

theorem threshold_18_33 : ∀ i ∈ List.range 1, ThresholdAt 18 (33+i) := by decide +kernel

theorem threshold_18_34 : ∀ i ∈ List.range 1, ThresholdAt 18 (34+i) := by decide +kernel

theorem threshold_18_35 : ∀ i ∈ List.range 1, ThresholdAt 18 (35+i) := by decide +kernel

theorem threshold_18_36 : ∀ i ∈ List.range 1, ThresholdAt 18 (36+i) := by decide +kernel

theorem threshold_18_37 : ∀ i ∈ List.range 1, ThresholdAt 18 (37+i) := by decide +kernel

theorem threshold_18_38 : ∀ i ∈ List.range 1, ThresholdAt 18 (38+i) := by decide +kernel

theorem threshold_18_39 : ∀ i ∈ List.range 1, ThresholdAt 18 (39+i) := by decide +kernel

theorem threshold_18_40 : ∀ i ∈ List.range 1, ThresholdAt 18 (40+i) := by decide +kernel

theorem threshold_18_41 : ∀ i ∈ List.range 1, ThresholdAt 18 (41+i) := by decide +kernel

theorem threshold_18_42 : ∀ i ∈ List.range 1, ThresholdAt 18 (42+i) := by decide +kernel

theorem threshold_18_43 : ∀ i ∈ List.range 1, ThresholdAt 18 (43+i) := by decide +kernel

theorem threshold_18_44 : ∀ i ∈ List.range 1, ThresholdAt 18 (44+i) := by decide +kernel

theorem threshold_18_45 : ∀ i ∈ List.range 1, ThresholdAt 18 (45+i) := by decide +kernel

theorem threshold_18_46 : ∀ i ∈ List.range 1, ThresholdAt 18 (46+i) := by decide +kernel

theorem threshold_18_47 : ∀ i ∈ List.range 1, ThresholdAt 18 (47+i) := by decide +kernel

theorem threshold_18_48 : ∀ i ∈ List.range 1, ThresholdAt 18 (48+i) := by decide +kernel

theorem threshold_18_49 : ∀ i ∈ List.range 1, ThresholdAt 18 (49+i) := by decide +kernel

theorem threshold_18_50 : ∀ i ∈ List.range 1, ThresholdAt 18 (50+i) := by decide +kernel

theorem threshold_18_51 : ∀ i ∈ List.range 1, ThresholdAt 18 (51+i) := by decide +kernel

theorem threshold_18_52 : ∀ i ∈ List.range 1, ThresholdAt 18 (52+i) := by decide +kernel

theorem threshold_18_53 : ∀ i ∈ List.range 1, ThresholdAt 18 (53+i) := by decide +kernel

theorem threshold_18_54 : ∀ i ∈ List.range 1, ThresholdAt 18 (54+i) := by decide +kernel

theorem threshold_18_55 : ∀ i ∈ List.range 1, ThresholdAt 18 (55+i) := by decide +kernel

theorem threshold_18_56 : ∀ i ∈ List.range 1, ThresholdAt 18 (56+i) := by decide +kernel

theorem threshold_18_57 : ∀ i ∈ List.range 1, ThresholdAt 18 (57+i) := by decide +kernel

theorem threshold_18_58 : ∀ i ∈ List.range 1, ThresholdAt 18 (58+i) := by decide +kernel

theorem threshold_18_59 : ∀ i ∈ List.range 1, ThresholdAt 18 (59+i) := by decide +kernel

theorem threshold_18_60 : ∀ i ∈ List.range 1, ThresholdAt 18 (60+i) := by decide +kernel

theorem threshold_18_61 : ∀ i ∈ List.range 1, ThresholdAt 18 (61+i) := by decide +kernel

theorem threshold_18_62 : ∀ i ∈ List.range 1, ThresholdAt 18 (62+i) := by decide +kernel

theorem threshold_18_63 : ∀ i ∈ List.range 1, ThresholdAt 18 (63+i) := by decide +kernel

theorem threshold_18_64 : ∀ i ∈ List.range 1, ThresholdAt 18 (64+i) := by decide +kernel

theorem threshold_18_65 : ∀ i ∈ List.range 1, ThresholdAt 18 (65+i) := by decide +kernel

theorem threshold_18_66 : ∀ i ∈ List.range 1, ThresholdAt 18 (66+i) := by decide +kernel

theorem threshold_18_67 : ∀ i ∈ List.range 1, ThresholdAt 18 (67+i) := by decide +kernel

theorem threshold_18_68 : ∀ i ∈ List.range 1, ThresholdAt 18 (68+i) := by decide +kernel

theorem threshold_18_69 : ∀ i ∈ List.range 1, ThresholdAt 18 (69+i) := by decide +kernel

theorem threshold_18_70 : ∀ i ∈ List.range 1, ThresholdAt 18 (70+i) := by decide +kernel

theorem threshold_18_71 : ∀ i ∈ List.range 1, ThresholdAt 18 (71+i) := by decide +kernel

theorem threshold_18_72 : ∀ i ∈ List.range 1, ThresholdAt 18 (72+i) := by decide +kernel

theorem threshold_18_73 : ∀ i ∈ List.range 1, ThresholdAt 18 (73+i) := by decide +kernel

theorem threshold_18_74 : ∀ i ∈ List.range 1, ThresholdAt 18 (74+i) := by decide +kernel

theorem threshold_18_75 : ∀ i ∈ List.range 1, ThresholdAt 18 (75+i) := by decide +kernel

theorem threshold_18_76 : ∀ i ∈ List.range 1, ThresholdAt 18 (76+i) := by decide +kernel

theorem threshold_18_77 : ∀ i ∈ List.range 1, ThresholdAt 18 (77+i) := by decide +kernel

theorem threshold_18_78 : ∀ i ∈ List.range 1, ThresholdAt 18 (78+i) := by decide +kernel

theorem threshold_18_79 : ∀ i ∈ List.range 1, ThresholdAt 18 (79+i) := by decide +kernel

theorem threshold_18_80 : ∀ i ∈ List.range 1, ThresholdAt 18 (80+i) := by decide +kernel

theorem threshold_18_81 : ∀ i ∈ List.range 1, ThresholdAt 18 (81+i) := by decide +kernel

theorem threshold_18_82 : ∀ i ∈ List.range 1, ThresholdAt 18 (82+i) := by decide +kernel

theorem threshold_18_83 : ∀ i ∈ List.range 1, ThresholdAt 18 (83+i) := by decide +kernel

theorem threshold_18_84 : ∀ i ∈ List.range 1, ThresholdAt 18 (84+i) := by decide +kernel

theorem threshold_18_85 : ∀ i ∈ List.range 1, ThresholdAt 18 (85+i) := by decide +kernel

theorem threshold_18_86 : ∀ i ∈ List.range 1, ThresholdAt 18 (86+i) := by decide +kernel

theorem threshold_18_87 : ∀ i ∈ List.range 1, ThresholdAt 18 (87+i) := by decide +kernel

theorem threshold_18_88 : ∀ i ∈ List.range 1, ThresholdAt 18 (88+i) := by decide +kernel

theorem threshold_18_89 : ∀ i ∈ List.range 1, ThresholdAt 18 (89+i) := by decide +kernel

theorem threshold_18_90 : ∀ i ∈ List.range 1, ThresholdAt 18 (90+i) := by decide +kernel

theorem threshold_18_91 : ∀ i ∈ List.range 1, ThresholdAt 18 (91+i) := by decide +kernel

theorem threshold_18_92 : ∀ i ∈ List.range 1, ThresholdAt 18 (92+i) := by decide +kernel

theorem threshold_18_93 : ∀ i ∈ List.range 1, ThresholdAt 18 (93+i) := by decide +kernel

theorem threshold_18_94 : ∀ i ∈ List.range 1, ThresholdAt 18 (94+i) := by decide +kernel

theorem threshold_18_95 : ∀ i ∈ List.range 1, ThresholdAt 18 (95+i) := by decide +kernel

theorem threshold_18_96 : ∀ i ∈ List.range 1, ThresholdAt 18 (96+i) := by decide +kernel

theorem threshold_18_97 : ∀ i ∈ List.range 1, ThresholdAt 18 (97+i) := by decide +kernel

theorem threshold_18_98 : ∀ i ∈ List.range 1, ThresholdAt 18 (98+i) := by decide +kernel

theorem threshold_18_99 : ∀ i ∈ List.range 1, ThresholdAt 18 (99+i) := by decide +kernel

theorem threshold_18_100 : ∀ i ∈ List.range 1, ThresholdAt 18 (100+i) := by decide +kernel

theorem threshold_18_101 : ∀ i ∈ List.range 1, ThresholdAt 18 (101+i) := by decide +kernel

theorem threshold_18_102 : ∀ i ∈ List.range 1, ThresholdAt 18 (102+i) := by decide +kernel

theorem threshold_18_103 : ∀ i ∈ List.range 1, ThresholdAt 18 (103+i) := by decide +kernel

theorem threshold_18_104 : ∀ i ∈ List.range 1, ThresholdAt 18 (104+i) := by decide +kernel

theorem threshold_18_105 : ∀ i ∈ List.range 1, ThresholdAt 18 (105+i) := by decide +kernel

theorem threshold_18_106 : ∀ i ∈ List.range 1, ThresholdAt 18 (106+i) := by decide +kernel

theorem threshold_18_107 : ∀ i ∈ List.range 1, ThresholdAt 18 (107+i) := by decide +kernel

theorem threshold_18_108 : ∀ i ∈ List.range 1, ThresholdAt 18 (108+i) := by decide +kernel

theorem threshold_18_109 : ∀ i ∈ List.range 1, ThresholdAt 18 (109+i) := by decide +kernel

theorem threshold_18_110 : ∀ i ∈ List.range 1, ThresholdAt 18 (110+i) := by decide +kernel

theorem threshold_18_111 : ∀ i ∈ List.range 1, ThresholdAt 18 (111+i) := by decide +kernel

theorem threshold_18_112 : ∀ i ∈ List.range 1, ThresholdAt 18 (112+i) := by decide +kernel

theorem threshold_18_113 : ∀ i ∈ List.range 1, ThresholdAt 18 (113+i) := by decide +kernel

theorem threshold_18_114 : ∀ i ∈ List.range 1, ThresholdAt 18 (114+i) := by decide +kernel

theorem threshold_18_115 : ∀ i ∈ List.range 1, ThresholdAt 18 (115+i) := by decide +kernel

theorem threshold_18_116 : ∀ i ∈ List.range 1, ThresholdAt 18 (116+i) := by decide +kernel

theorem threshold_18_117 : ∀ i ∈ List.range 1, ThresholdAt 18 (117+i) := by decide +kernel

theorem threshold_18_118 : ∀ i ∈ List.range 1, ThresholdAt 18 (118+i) := by decide +kernel

theorem threshold_18_119 : ∀ i ∈ List.range 1, ThresholdAt 18 (119+i) := by decide +kernel

theorem threshold_18_120 : ∀ i ∈ List.range 1, ThresholdAt 18 (120+i) := by decide +kernel

theorem threshold_18_121 : ∀ i ∈ List.range 1, ThresholdAt 18 (121+i) := by decide +kernel

theorem threshold_18_122 : ∀ i ∈ List.range 1, ThresholdAt 18 (122+i) := by decide +kernel

theorem threshold_18_123 : ∀ i ∈ List.range 1, ThresholdAt 18 (123+i) := by decide +kernel

theorem threshold_18_124 : ∀ i ∈ List.range 1, ThresholdAt 18 (124+i) := by decide +kernel

theorem threshold_18_125 : ∀ i ∈ List.range 1, ThresholdAt 18 (125+i) := by decide +kernel

theorem threshold_18_126 : ∀ i ∈ List.range 1, ThresholdAt 18 (126+i) := by decide +kernel

theorem threshold_18_127 : ∀ i ∈ List.range 1, ThresholdAt 18 (127+i) := by decide +kernel

theorem threshold_18_128 : ∀ i ∈ List.range 1, ThresholdAt 18 (128+i) := by decide +kernel

theorem threshold_18_129 : ∀ i ∈ List.range 1, ThresholdAt 18 (129+i) := by decide +kernel

theorem threshold_18_130 : ∀ i ∈ List.range 1, ThresholdAt 18 (130+i) := by decide +kernel

theorem threshold_18_131 : ∀ i ∈ List.range 1, ThresholdAt 18 (131+i) := by decide +kernel

theorem threshold_18 (v : ℕ) (hv : v ∈ List.range 132) : ThresholdAt 18 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 18 v)
  have h := (join 0 66 66 (join 0 33 33 (join 0 16 17 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_18_0 threshold_18_1) (join 2 1 1 threshold_18_2 threshold_18_3)) (join 4 2 2 (join 4 1 1 threshold_18_4 threshold_18_5) (join 6 1 1 threshold_18_6 threshold_18_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_18_8 threshold_18_9) (join 10 1 1 threshold_18_10 threshold_18_11)) (join 12 2 2 (join 12 1 1 threshold_18_12 threshold_18_13) (join 14 1 1 threshold_18_14 threshold_18_15)))) (join 16 8 9 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_18_16 threshold_18_17) (join 18 1 1 threshold_18_18 threshold_18_19)) (join 20 2 2 (join 20 1 1 threshold_18_20 threshold_18_21) (join 22 1 1 threshold_18_22 threshold_18_23))) (join 24 4 5 (join 24 2 2 (join 24 1 1 threshold_18_24 threshold_18_25) (join 26 1 1 threshold_18_26 threshold_18_27)) (join 28 2 3 (join 28 1 1 threshold_18_28 threshold_18_29) (join 30 1 2 threshold_18_30 (join 31 1 1 threshold_18_31 threshold_18_32)))))) (join 33 16 17 (join 33 8 8 (join 33 4 4 (join 33 2 2 (join 33 1 1 threshold_18_33 threshold_18_34) (join 35 1 1 threshold_18_35 threshold_18_36)) (join 37 2 2 (join 37 1 1 threshold_18_37 threshold_18_38) (join 39 1 1 threshold_18_39 threshold_18_40))) (join 41 4 4 (join 41 2 2 (join 41 1 1 threshold_18_41 threshold_18_42) (join 43 1 1 threshold_18_43 threshold_18_44)) (join 45 2 2 (join 45 1 1 threshold_18_45 threshold_18_46) (join 47 1 1 threshold_18_47 threshold_18_48)))) (join 49 8 9 (join 49 4 4 (join 49 2 2 (join 49 1 1 threshold_18_49 threshold_18_50) (join 51 1 1 threshold_18_51 threshold_18_52)) (join 53 2 2 (join 53 1 1 threshold_18_53 threshold_18_54) (join 55 1 1 threshold_18_55 threshold_18_56))) (join 57 4 5 (join 57 2 2 (join 57 1 1 threshold_18_57 threshold_18_58) (join 59 1 1 threshold_18_59 threshold_18_60)) (join 61 2 3 (join 61 1 1 threshold_18_61 threshold_18_62) (join 63 1 2 threshold_18_63 (join 64 1 1 threshold_18_64 threshold_18_65))))))) (join 66 33 33 (join 66 16 17 (join 66 8 8 (join 66 4 4 (join 66 2 2 (join 66 1 1 threshold_18_66 threshold_18_67) (join 68 1 1 threshold_18_68 threshold_18_69)) (join 70 2 2 (join 70 1 1 threshold_18_70 threshold_18_71) (join 72 1 1 threshold_18_72 threshold_18_73))) (join 74 4 4 (join 74 2 2 (join 74 1 1 threshold_18_74 threshold_18_75) (join 76 1 1 threshold_18_76 threshold_18_77)) (join 78 2 2 (join 78 1 1 threshold_18_78 threshold_18_79) (join 80 1 1 threshold_18_80 threshold_18_81)))) (join 82 8 9 (join 82 4 4 (join 82 2 2 (join 82 1 1 threshold_18_82 threshold_18_83) (join 84 1 1 threshold_18_84 threshold_18_85)) (join 86 2 2 (join 86 1 1 threshold_18_86 threshold_18_87) (join 88 1 1 threshold_18_88 threshold_18_89))) (join 90 4 5 (join 90 2 2 (join 90 1 1 threshold_18_90 threshold_18_91) (join 92 1 1 threshold_18_92 threshold_18_93)) (join 94 2 3 (join 94 1 1 threshold_18_94 threshold_18_95) (join 96 1 2 threshold_18_96 (join 97 1 1 threshold_18_97 threshold_18_98)))))) (join 99 16 17 (join 99 8 8 (join 99 4 4 (join 99 2 2 (join 99 1 1 threshold_18_99 threshold_18_100) (join 101 1 1 threshold_18_101 threshold_18_102)) (join 103 2 2 (join 103 1 1 threshold_18_103 threshold_18_104) (join 105 1 1 threshold_18_105 threshold_18_106))) (join 107 4 4 (join 107 2 2 (join 107 1 1 threshold_18_107 threshold_18_108) (join 109 1 1 threshold_18_109 threshold_18_110)) (join 111 2 2 (join 111 1 1 threshold_18_111 threshold_18_112) (join 113 1 1 threshold_18_113 threshold_18_114)))) (join 115 8 9 (join 115 4 4 (join 115 2 2 (join 115 1 1 threshold_18_115 threshold_18_116) (join 117 1 1 threshold_18_117 threshold_18_118)) (join 119 2 2 (join 119 1 1 threshold_18_119 threshold_18_120) (join 121 1 1 threshold_18_121 threshold_18_122))) (join 123 4 5 (join 123 2 2 (join 123 1 1 threshold_18_123 threshold_18_124) (join 125 1 1 threshold_18_125 threshold_18_126)) (join 127 2 3 (join 127 1 1 threshold_18_127 threshold_18_128) (join 129 1 2 threshold_18_129 (join 130 1 1 threshold_18_130 threshold_18_131))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_18_0 : ∀ i ∈ List.range 4, LedgerAt 18 (0+i) := by decide +kernel

theorem ledger_18_4 : ∀ i ∈ List.range 4, LedgerAt 18 (4+i) := by decide +kernel

theorem ledger_18_8 : ∀ i ∈ List.range 4, LedgerAt 18 (8+i) := by decide +kernel

theorem ledger_18_12 : ∀ i ∈ List.range 4, LedgerAt 18 (12+i) := by decide +kernel

theorem ledger_18_16 : ∀ i ∈ List.range 4, LedgerAt 18 (16+i) := by decide +kernel

theorem ledger_18_20 : ∀ i ∈ List.range 4, LedgerAt 18 (20+i) := by decide +kernel

theorem ledger_18_24 : ∀ i ∈ List.range 4, LedgerAt 18 (24+i) := by decide +kernel

theorem ledger_18_28 : ∀ i ∈ List.range 4, LedgerAt 18 (28+i) := by decide +kernel

theorem ledger_18_32 : ∀ i ∈ List.range 4, LedgerAt 18 (32+i) := by decide +kernel

theorem ledger_18_36 : ∀ i ∈ List.range 4, LedgerAt 18 (36+i) := by decide +kernel

theorem ledger_18_40 : ∀ i ∈ List.range 4, LedgerAt 18 (40+i) := by decide +kernel

theorem ledger_18_44 : ∀ i ∈ List.range 4, LedgerAt 18 (44+i) := by decide +kernel

theorem ledger_18_48 : ∀ i ∈ List.range 4, LedgerAt 18 (48+i) := by decide +kernel

theorem ledger_18_52 : ∀ i ∈ List.range 4, LedgerAt 18 (52+i) := by decide +kernel

theorem ledger_18_56 : ∀ i ∈ List.range 4, LedgerAt 18 (56+i) := by decide +kernel

theorem ledger_18_60 : ∀ i ∈ List.range 4, LedgerAt 18 (60+i) := by decide +kernel

theorem ledger_18_64 : ∀ i ∈ List.range 4, LedgerAt 18 (64+i) := by decide +kernel

theorem ledger_18_68 : ∀ i ∈ List.range 4, LedgerAt 18 (68+i) := by decide +kernel

theorem ledger_18_72 : ∀ i ∈ List.range 4, LedgerAt 18 (72+i) := by decide +kernel

theorem ledger_18_76 : ∀ i ∈ List.range 4, LedgerAt 18 (76+i) := by decide +kernel

theorem ledger_18_80 : ∀ i ∈ List.range 4, LedgerAt 18 (80+i) := by decide +kernel

theorem ledger_18_84 : ∀ i ∈ List.range 4, LedgerAt 18 (84+i) := by decide +kernel

theorem ledger_18_88 : ∀ i ∈ List.range 4, LedgerAt 18 (88+i) := by decide +kernel

theorem ledger_18_92 : ∀ i ∈ List.range 4, LedgerAt 18 (92+i) := by decide +kernel

theorem ledger_18_96 : ∀ i ∈ List.range 4, LedgerAt 18 (96+i) := by decide +kernel

theorem ledger_18_100 : ∀ i ∈ List.range 4, LedgerAt 18 (100+i) := by decide +kernel

theorem ledger_18_104 : ∀ i ∈ List.range 4, LedgerAt 18 (104+i) := by decide +kernel

theorem ledger_18_108 : ∀ i ∈ List.range 4, LedgerAt 18 (108+i) := by decide +kernel

theorem ledger_18_112 : ∀ i ∈ List.range 4, LedgerAt 18 (112+i) := by decide +kernel

theorem ledger_18_116 : ∀ i ∈ List.range 4, LedgerAt 18 (116+i) := by decide +kernel

theorem ledger_18_120 : ∀ i ∈ List.range 4, LedgerAt 18 (120+i) := by decide +kernel

theorem ledger_18_124 : ∀ i ∈ List.range 4, LedgerAt 18 (124+i) := by decide +kernel

theorem ledger_18_128 : ∀ i ∈ List.range 4, LedgerAt 18 (128+i) := by decide +kernel

theorem ledger_18 (v : ℕ) (hv : v ∈ List.range 132) : LedgerAt 18 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 18 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_18_0 ledger_18_4) (join 8 4 4 ledger_18_8 ledger_18_12)) (join 16 8 8 (join 16 4 4 ledger_18_16 ledger_18_20) (join 24 4 4 ledger_18_24 ledger_18_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_18_32 ledger_18_36) (join 40 4 4 ledger_18_40 ledger_18_44)) (join 48 8 8 (join 48 4 4 ledger_18_48 ledger_18_52) (join 56 4 4 ledger_18_56 ledger_18_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_18_64 ledger_18_68) (join 72 4 4 ledger_18_72 ledger_18_76)) (join 80 8 8 (join 80 4 4 ledger_18_80 ledger_18_84) (join 88 4 4 ledger_18_88 ledger_18_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 ledger_18_96 ledger_18_100) (join 104 4 4 ledger_18_104 ledger_18_108)) (join 112 8 12 (join 112 4 4 ledger_18_112 ledger_18_116) (join 120 4 8 ledger_18_120 (join 124 4 4 ledger_18_124 ledger_18_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
