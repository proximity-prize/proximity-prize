import ProximityPrize.SubmissionLower.HigherAffineCheckedR256810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_26_0 : ∀ i ∈ List.range 4, SingleAt 26 (0+i) := by decide +kernel

theorem single_26_4 : ∀ i ∈ List.range 4, SingleAt 26 (4+i) := by decide +kernel

theorem single_26_8 : ∀ i ∈ List.range 4, SingleAt 26 (8+i) := by decide +kernel

theorem single_26_12 : ∀ i ∈ List.range 4, SingleAt 26 (12+i) := by decide +kernel

theorem single_26_16 : ∀ i ∈ List.range 4, SingleAt 26 (16+i) := by decide +kernel

theorem single_26_20 : ∀ i ∈ List.range 4, SingleAt 26 (20+i) := by decide +kernel

theorem single_26_24 : ∀ i ∈ List.range 4, SingleAt 26 (24+i) := by decide +kernel

theorem single_26_28 : ∀ i ∈ List.range 4, SingleAt 26 (28+i) := by decide +kernel

theorem single_26_32 : ∀ i ∈ List.range 4, SingleAt 26 (32+i) := by decide +kernel

theorem single_26_36 : ∀ i ∈ List.range 4, SingleAt 26 (36+i) := by decide +kernel

theorem single_26_40 : ∀ i ∈ List.range 4, SingleAt 26 (40+i) := by decide +kernel

theorem single_26_44 : ∀ i ∈ List.range 4, SingleAt 26 (44+i) := by decide +kernel

theorem single_26_48 : ∀ i ∈ List.range 4, SingleAt 26 (48+i) := by decide +kernel

theorem single_26_52 : ∀ i ∈ List.range 4, SingleAt 26 (52+i) := by decide +kernel

theorem single_26_56 : ∀ i ∈ List.range 4, SingleAt 26 (56+i) := by decide +kernel

theorem single_26_60 : ∀ i ∈ List.range 4, SingleAt 26 (60+i) := by decide +kernel

theorem single_26_64 : ∀ i ∈ List.range 4, SingleAt 26 (64+i) := by decide +kernel

theorem single_26_68 : ∀ i ∈ List.range 4, SingleAt 26 (68+i) := by decide +kernel

theorem single_26_72 : ∀ i ∈ List.range 4, SingleAt 26 (72+i) := by decide +kernel

theorem single_26_76 : ∀ i ∈ List.range 4, SingleAt 26 (76+i) := by decide +kernel

theorem single_26_80 : ∀ i ∈ List.range 4, SingleAt 26 (80+i) := by decide +kernel

theorem single_26_84 : ∀ i ∈ List.range 4, SingleAt 26 (84+i) := by decide +kernel

theorem single_26_88 : ∀ i ∈ List.range 4, SingleAt 26 (88+i) := by decide +kernel

theorem single_26_92 : ∀ i ∈ List.range 4, SingleAt 26 (92+i) := by decide +kernel

theorem single_26_96 : ∀ i ∈ List.range 4, SingleAt 26 (96+i) := by decide +kernel

theorem single_26_100 : ∀ i ∈ List.range 4, SingleAt 26 (100+i) := by decide +kernel

theorem single_26_104 : ∀ i ∈ List.range 4, SingleAt 26 (104+i) := by decide +kernel

theorem single_26_108 : ∀ i ∈ List.range 4, SingleAt 26 (108+i) := by decide +kernel

theorem single_26_112 : ∀ i ∈ List.range 4, SingleAt 26 (112+i) := by decide +kernel

theorem single_26_116 : ∀ i ∈ List.range 4, SingleAt 26 (116+i) := by decide +kernel

theorem single_26_120 : ∀ i ∈ List.range 4, SingleAt 26 (120+i) := by decide +kernel

theorem single_26_124 : ∀ i ∈ List.range 4, SingleAt 26 (124+i) := by decide +kernel

theorem single_26_128 : ∀ i ∈ List.range 3, SingleAt 26 (128+i) := by decide +kernel

theorem single_26 (v : ℕ) (hv : v ∈ List.range 131) : SingleAt 26 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 26 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_26_0 single_26_4) (join 8 4 4 single_26_8 single_26_12)) (join 16 8 8 (join 16 4 4 single_26_16 single_26_20) (join 24 4 4 single_26_24 single_26_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_26_32 single_26_36) (join 40 4 4 single_26_40 single_26_44)) (join 48 8 8 (join 48 4 4 single_26_48 single_26_52) (join 56 4 4 single_26_56 single_26_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_26_64 single_26_68) (join 72 4 4 single_26_72 single_26_76)) (join 80 8 8 (join 80 4 4 single_26_80 single_26_84) (join 88 4 4 single_26_88 single_26_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 single_26_96 single_26_100) (join 104 4 4 single_26_104 single_26_108)) (join 112 8 11 (join 112 4 4 single_26_112 single_26_116) (join 120 4 7 single_26_120 (join 124 4 3 single_26_124 single_26_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_26_0 : ∀ i ∈ List.range 4, PhaseAt 26 (0+i) := by decide +kernel

theorem phase_26_4 : ∀ i ∈ List.range 4, PhaseAt 26 (4+i) := by decide +kernel

theorem phase_26_8 : ∀ i ∈ List.range 4, PhaseAt 26 (8+i) := by decide +kernel

theorem phase_26_12 : ∀ i ∈ List.range 4, PhaseAt 26 (12+i) := by decide +kernel

theorem phase_26_16 : ∀ i ∈ List.range 4, PhaseAt 26 (16+i) := by decide +kernel

theorem phase_26_20 : ∀ i ∈ List.range 4, PhaseAt 26 (20+i) := by decide +kernel

theorem phase_26_24 : ∀ i ∈ List.range 4, PhaseAt 26 (24+i) := by decide +kernel

theorem phase_26_28 : ∀ i ∈ List.range 4, PhaseAt 26 (28+i) := by decide +kernel

theorem phase_26_32 : ∀ i ∈ List.range 4, PhaseAt 26 (32+i) := by decide +kernel

theorem phase_26_36 : ∀ i ∈ List.range 4, PhaseAt 26 (36+i) := by decide +kernel

theorem phase_26_40 : ∀ i ∈ List.range 4, PhaseAt 26 (40+i) := by decide +kernel

theorem phase_26_44 : ∀ i ∈ List.range 4, PhaseAt 26 (44+i) := by decide +kernel

theorem phase_26_48 : ∀ i ∈ List.range 4, PhaseAt 26 (48+i) := by decide +kernel

theorem phase_26_52 : ∀ i ∈ List.range 4, PhaseAt 26 (52+i) := by decide +kernel

theorem phase_26_56 : ∀ i ∈ List.range 4, PhaseAt 26 (56+i) := by decide +kernel

theorem phase_26_60 : ∀ i ∈ List.range 4, PhaseAt 26 (60+i) := by decide +kernel

theorem phase_26_64 : ∀ i ∈ List.range 4, PhaseAt 26 (64+i) := by decide +kernel

theorem phase_26_68 : ∀ i ∈ List.range 4, PhaseAt 26 (68+i) := by decide +kernel

theorem phase_26_72 : ∀ i ∈ List.range 4, PhaseAt 26 (72+i) := by decide +kernel

theorem phase_26_76 : ∀ i ∈ List.range 4, PhaseAt 26 (76+i) := by decide +kernel

theorem phase_26_80 : ∀ i ∈ List.range 4, PhaseAt 26 (80+i) := by decide +kernel

theorem phase_26_84 : ∀ i ∈ List.range 4, PhaseAt 26 (84+i) := by decide +kernel

theorem phase_26_88 : ∀ i ∈ List.range 4, PhaseAt 26 (88+i) := by decide +kernel

theorem phase_26_92 : ∀ i ∈ List.range 4, PhaseAt 26 (92+i) := by decide +kernel

theorem phase_26_96 : ∀ i ∈ List.range 4, PhaseAt 26 (96+i) := by decide +kernel

theorem phase_26_100 : ∀ i ∈ List.range 4, PhaseAt 26 (100+i) := by decide +kernel

theorem phase_26_104 : ∀ i ∈ List.range 4, PhaseAt 26 (104+i) := by decide +kernel

theorem phase_26_108 : ∀ i ∈ List.range 4, PhaseAt 26 (108+i) := by decide +kernel

theorem phase_26_112 : ∀ i ∈ List.range 4, PhaseAt 26 (112+i) := by decide +kernel

theorem phase_26_116 : ∀ i ∈ List.range 4, PhaseAt 26 (116+i) := by decide +kernel

theorem phase_26_120 : ∀ i ∈ List.range 4, PhaseAt 26 (120+i) := by decide +kernel

theorem phase_26_124 : ∀ i ∈ List.range 4, PhaseAt 26 (124+i) := by decide +kernel

theorem phase_26_128 : ∀ i ∈ List.range 3, PhaseAt 26 (128+i) := by decide +kernel

theorem phase_26 (v : ℕ) (hv : v ∈ List.range 131) : PhaseAt 26 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 26 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_26_0 phase_26_4) (join 8 4 4 phase_26_8 phase_26_12)) (join 16 8 8 (join 16 4 4 phase_26_16 phase_26_20) (join 24 4 4 phase_26_24 phase_26_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_26_32 phase_26_36) (join 40 4 4 phase_26_40 phase_26_44)) (join 48 8 8 (join 48 4 4 phase_26_48 phase_26_52) (join 56 4 4 phase_26_56 phase_26_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_26_64 phase_26_68) (join 72 4 4 phase_26_72 phase_26_76)) (join 80 8 8 (join 80 4 4 phase_26_80 phase_26_84) (join 88 4 4 phase_26_88 phase_26_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 phase_26_96 phase_26_100) (join 104 4 4 phase_26_104 phase_26_108)) (join 112 8 11 (join 112 4 4 phase_26_112 phase_26_116) (join 120 4 7 phase_26_120 (join 124 4 3 phase_26_124 phase_26_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_26_0 : ∀ i ∈ List.range 1, ThresholdAt 26 (0+i) := by decide +kernel

theorem threshold_26_1 : ∀ i ∈ List.range 1, ThresholdAt 26 (1+i) := by decide +kernel

theorem threshold_26_2 : ∀ i ∈ List.range 1, ThresholdAt 26 (2+i) := by decide +kernel

theorem threshold_26_3 : ∀ i ∈ List.range 1, ThresholdAt 26 (3+i) := by decide +kernel

theorem threshold_26_4 : ∀ i ∈ List.range 1, ThresholdAt 26 (4+i) := by decide +kernel

theorem threshold_26_5 : ∀ i ∈ List.range 1, ThresholdAt 26 (5+i) := by decide +kernel

theorem threshold_26_6 : ∀ i ∈ List.range 1, ThresholdAt 26 (6+i) := by decide +kernel

theorem threshold_26_7 : ∀ i ∈ List.range 1, ThresholdAt 26 (7+i) := by decide +kernel

theorem threshold_26_8 : ∀ i ∈ List.range 1, ThresholdAt 26 (8+i) := by decide +kernel

theorem threshold_26_9 : ∀ i ∈ List.range 1, ThresholdAt 26 (9+i) := by decide +kernel

theorem threshold_26_10 : ∀ i ∈ List.range 1, ThresholdAt 26 (10+i) := by decide +kernel

theorem threshold_26_11 : ∀ i ∈ List.range 1, ThresholdAt 26 (11+i) := by decide +kernel

theorem threshold_26_12 : ∀ i ∈ List.range 1, ThresholdAt 26 (12+i) := by decide +kernel

theorem threshold_26_13 : ∀ i ∈ List.range 1, ThresholdAt 26 (13+i) := by decide +kernel

theorem threshold_26_14 : ∀ i ∈ List.range 1, ThresholdAt 26 (14+i) := by decide +kernel

theorem threshold_26_15 : ∀ i ∈ List.range 1, ThresholdAt 26 (15+i) := by decide +kernel

theorem threshold_26_16 : ∀ i ∈ List.range 1, ThresholdAt 26 (16+i) := by decide +kernel

theorem threshold_26_17 : ∀ i ∈ List.range 1, ThresholdAt 26 (17+i) := by decide +kernel

theorem threshold_26_18 : ∀ i ∈ List.range 1, ThresholdAt 26 (18+i) := by decide +kernel

theorem threshold_26_19 : ∀ i ∈ List.range 1, ThresholdAt 26 (19+i) := by decide +kernel

theorem threshold_26_20 : ∀ i ∈ List.range 1, ThresholdAt 26 (20+i) := by decide +kernel

theorem threshold_26_21 : ∀ i ∈ List.range 1, ThresholdAt 26 (21+i) := by decide +kernel

theorem threshold_26_22 : ∀ i ∈ List.range 1, ThresholdAt 26 (22+i) := by decide +kernel

theorem threshold_26_23 : ∀ i ∈ List.range 1, ThresholdAt 26 (23+i) := by decide +kernel

theorem threshold_26_24 : ∀ i ∈ List.range 1, ThresholdAt 26 (24+i) := by decide +kernel

theorem threshold_26_25 : ∀ i ∈ List.range 1, ThresholdAt 26 (25+i) := by decide +kernel

theorem threshold_26_26 : ∀ i ∈ List.range 1, ThresholdAt 26 (26+i) := by decide +kernel

theorem threshold_26_27 : ∀ i ∈ List.range 1, ThresholdAt 26 (27+i) := by decide +kernel

theorem threshold_26_28 : ∀ i ∈ List.range 1, ThresholdAt 26 (28+i) := by decide +kernel

theorem threshold_26_29 : ∀ i ∈ List.range 1, ThresholdAt 26 (29+i) := by decide +kernel

theorem threshold_26_30 : ∀ i ∈ List.range 1, ThresholdAt 26 (30+i) := by decide +kernel

theorem threshold_26_31 : ∀ i ∈ List.range 1, ThresholdAt 26 (31+i) := by decide +kernel

theorem threshold_26_32 : ∀ i ∈ List.range 1, ThresholdAt 26 (32+i) := by decide +kernel

theorem threshold_26_33 : ∀ i ∈ List.range 1, ThresholdAt 26 (33+i) := by decide +kernel

theorem threshold_26_34 : ∀ i ∈ List.range 1, ThresholdAt 26 (34+i) := by decide +kernel

theorem threshold_26_35 : ∀ i ∈ List.range 1, ThresholdAt 26 (35+i) := by decide +kernel

theorem threshold_26_36 : ∀ i ∈ List.range 1, ThresholdAt 26 (36+i) := by decide +kernel

theorem threshold_26_37 : ∀ i ∈ List.range 1, ThresholdAt 26 (37+i) := by decide +kernel

theorem threshold_26_38 : ∀ i ∈ List.range 1, ThresholdAt 26 (38+i) := by decide +kernel

theorem threshold_26_39 : ∀ i ∈ List.range 1, ThresholdAt 26 (39+i) := by decide +kernel

theorem threshold_26_40 : ∀ i ∈ List.range 1, ThresholdAt 26 (40+i) := by decide +kernel

theorem threshold_26_41 : ∀ i ∈ List.range 1, ThresholdAt 26 (41+i) := by decide +kernel

theorem threshold_26_42 : ∀ i ∈ List.range 1, ThresholdAt 26 (42+i) := by decide +kernel

theorem threshold_26_43 : ∀ i ∈ List.range 1, ThresholdAt 26 (43+i) := by decide +kernel

theorem threshold_26_44 : ∀ i ∈ List.range 1, ThresholdAt 26 (44+i) := by decide +kernel

theorem threshold_26_45 : ∀ i ∈ List.range 1, ThresholdAt 26 (45+i) := by decide +kernel

theorem threshold_26_46 : ∀ i ∈ List.range 1, ThresholdAt 26 (46+i) := by decide +kernel

theorem threshold_26_47 : ∀ i ∈ List.range 1, ThresholdAt 26 (47+i) := by decide +kernel

theorem threshold_26_48 : ∀ i ∈ List.range 1, ThresholdAt 26 (48+i) := by decide +kernel

theorem threshold_26_49 : ∀ i ∈ List.range 1, ThresholdAt 26 (49+i) := by decide +kernel

theorem threshold_26_50 : ∀ i ∈ List.range 1, ThresholdAt 26 (50+i) := by decide +kernel

theorem threshold_26_51 : ∀ i ∈ List.range 1, ThresholdAt 26 (51+i) := by decide +kernel

theorem threshold_26_52 : ∀ i ∈ List.range 1, ThresholdAt 26 (52+i) := by decide +kernel

theorem threshold_26_53 : ∀ i ∈ List.range 1, ThresholdAt 26 (53+i) := by decide +kernel

theorem threshold_26_54 : ∀ i ∈ List.range 1, ThresholdAt 26 (54+i) := by decide +kernel

theorem threshold_26_55 : ∀ i ∈ List.range 1, ThresholdAt 26 (55+i) := by decide +kernel

theorem threshold_26_56 : ∀ i ∈ List.range 1, ThresholdAt 26 (56+i) := by decide +kernel

theorem threshold_26_57 : ∀ i ∈ List.range 1, ThresholdAt 26 (57+i) := by decide +kernel

theorem threshold_26_58 : ∀ i ∈ List.range 1, ThresholdAt 26 (58+i) := by decide +kernel

theorem threshold_26_59 : ∀ i ∈ List.range 1, ThresholdAt 26 (59+i) := by decide +kernel

theorem threshold_26_60 : ∀ i ∈ List.range 1, ThresholdAt 26 (60+i) := by decide +kernel

theorem threshold_26_61 : ∀ i ∈ List.range 1, ThresholdAt 26 (61+i) := by decide +kernel

theorem threshold_26_62 : ∀ i ∈ List.range 1, ThresholdAt 26 (62+i) := by decide +kernel

theorem threshold_26_63 : ∀ i ∈ List.range 1, ThresholdAt 26 (63+i) := by decide +kernel

theorem threshold_26_64 : ∀ i ∈ List.range 1, ThresholdAt 26 (64+i) := by decide +kernel

theorem threshold_26_65 : ∀ i ∈ List.range 1, ThresholdAt 26 (65+i) := by decide +kernel

theorem threshold_26_66 : ∀ i ∈ List.range 1, ThresholdAt 26 (66+i) := by decide +kernel

theorem threshold_26_67 : ∀ i ∈ List.range 1, ThresholdAt 26 (67+i) := by decide +kernel

theorem threshold_26_68 : ∀ i ∈ List.range 1, ThresholdAt 26 (68+i) := by decide +kernel

theorem threshold_26_69 : ∀ i ∈ List.range 1, ThresholdAt 26 (69+i) := by decide +kernel

theorem threshold_26_70 : ∀ i ∈ List.range 1, ThresholdAt 26 (70+i) := by decide +kernel

theorem threshold_26_71 : ∀ i ∈ List.range 1, ThresholdAt 26 (71+i) := by decide +kernel

theorem threshold_26_72 : ∀ i ∈ List.range 1, ThresholdAt 26 (72+i) := by decide +kernel

theorem threshold_26_73 : ∀ i ∈ List.range 1, ThresholdAt 26 (73+i) := by decide +kernel

theorem threshold_26_74 : ∀ i ∈ List.range 1, ThresholdAt 26 (74+i) := by decide +kernel

theorem threshold_26_75 : ∀ i ∈ List.range 1, ThresholdAt 26 (75+i) := by decide +kernel

theorem threshold_26_76 : ∀ i ∈ List.range 1, ThresholdAt 26 (76+i) := by decide +kernel

theorem threshold_26_77 : ∀ i ∈ List.range 1, ThresholdAt 26 (77+i) := by decide +kernel

theorem threshold_26_78 : ∀ i ∈ List.range 1, ThresholdAt 26 (78+i) := by decide +kernel

theorem threshold_26_79 : ∀ i ∈ List.range 1, ThresholdAt 26 (79+i) := by decide +kernel

theorem threshold_26_80 : ∀ i ∈ List.range 1, ThresholdAt 26 (80+i) := by decide +kernel

theorem threshold_26_81 : ∀ i ∈ List.range 1, ThresholdAt 26 (81+i) := by decide +kernel

theorem threshold_26_82 : ∀ i ∈ List.range 1, ThresholdAt 26 (82+i) := by decide +kernel

theorem threshold_26_83 : ∀ i ∈ List.range 1, ThresholdAt 26 (83+i) := by decide +kernel

theorem threshold_26_84 : ∀ i ∈ List.range 1, ThresholdAt 26 (84+i) := by decide +kernel

theorem threshold_26_85 : ∀ i ∈ List.range 1, ThresholdAt 26 (85+i) := by decide +kernel

theorem threshold_26_86 : ∀ i ∈ List.range 1, ThresholdAt 26 (86+i) := by decide +kernel

theorem threshold_26_87 : ∀ i ∈ List.range 1, ThresholdAt 26 (87+i) := by decide +kernel

theorem threshold_26_88 : ∀ i ∈ List.range 1, ThresholdAt 26 (88+i) := by decide +kernel

theorem threshold_26_89 : ∀ i ∈ List.range 1, ThresholdAt 26 (89+i) := by decide +kernel

theorem threshold_26_90 : ∀ i ∈ List.range 1, ThresholdAt 26 (90+i) := by decide +kernel

theorem threshold_26_91 : ∀ i ∈ List.range 1, ThresholdAt 26 (91+i) := by decide +kernel

theorem threshold_26_92 : ∀ i ∈ List.range 1, ThresholdAt 26 (92+i) := by decide +kernel

theorem threshold_26_93 : ∀ i ∈ List.range 1, ThresholdAt 26 (93+i) := by decide +kernel

theorem threshold_26_94 : ∀ i ∈ List.range 1, ThresholdAt 26 (94+i) := by decide +kernel

theorem threshold_26_95 : ∀ i ∈ List.range 1, ThresholdAt 26 (95+i) := by decide +kernel

theorem threshold_26_96 : ∀ i ∈ List.range 1, ThresholdAt 26 (96+i) := by decide +kernel

theorem threshold_26_97 : ∀ i ∈ List.range 1, ThresholdAt 26 (97+i) := by decide +kernel

theorem threshold_26_98 : ∀ i ∈ List.range 1, ThresholdAt 26 (98+i) := by decide +kernel

theorem threshold_26_99 : ∀ i ∈ List.range 1, ThresholdAt 26 (99+i) := by decide +kernel

theorem threshold_26_100 : ∀ i ∈ List.range 1, ThresholdAt 26 (100+i) := by decide +kernel

theorem threshold_26_101 : ∀ i ∈ List.range 1, ThresholdAt 26 (101+i) := by decide +kernel

theorem threshold_26_102 : ∀ i ∈ List.range 1, ThresholdAt 26 (102+i) := by decide +kernel

theorem threshold_26_103 : ∀ i ∈ List.range 1, ThresholdAt 26 (103+i) := by decide +kernel

theorem threshold_26_104 : ∀ i ∈ List.range 1, ThresholdAt 26 (104+i) := by decide +kernel

theorem threshold_26_105 : ∀ i ∈ List.range 1, ThresholdAt 26 (105+i) := by decide +kernel

theorem threshold_26_106 : ∀ i ∈ List.range 1, ThresholdAt 26 (106+i) := by decide +kernel

theorem threshold_26_107 : ∀ i ∈ List.range 1, ThresholdAt 26 (107+i) := by decide +kernel

theorem threshold_26_108 : ∀ i ∈ List.range 1, ThresholdAt 26 (108+i) := by decide +kernel

theorem threshold_26_109 : ∀ i ∈ List.range 1, ThresholdAt 26 (109+i) := by decide +kernel

theorem threshold_26_110 : ∀ i ∈ List.range 1, ThresholdAt 26 (110+i) := by decide +kernel

theorem threshold_26_111 : ∀ i ∈ List.range 1, ThresholdAt 26 (111+i) := by decide +kernel

theorem threshold_26_112 : ∀ i ∈ List.range 1, ThresholdAt 26 (112+i) := by decide +kernel

theorem threshold_26_113 : ∀ i ∈ List.range 1, ThresholdAt 26 (113+i) := by decide +kernel

theorem threshold_26_114 : ∀ i ∈ List.range 1, ThresholdAt 26 (114+i) := by decide +kernel

theorem threshold_26_115 : ∀ i ∈ List.range 1, ThresholdAt 26 (115+i) := by decide +kernel

theorem threshold_26_116 : ∀ i ∈ List.range 1, ThresholdAt 26 (116+i) := by decide +kernel

theorem threshold_26_117 : ∀ i ∈ List.range 1, ThresholdAt 26 (117+i) := by decide +kernel

theorem threshold_26_118 : ∀ i ∈ List.range 1, ThresholdAt 26 (118+i) := by decide +kernel

theorem threshold_26_119 : ∀ i ∈ List.range 1, ThresholdAt 26 (119+i) := by decide +kernel

theorem threshold_26_120 : ∀ i ∈ List.range 1, ThresholdAt 26 (120+i) := by decide +kernel

theorem threshold_26_121 : ∀ i ∈ List.range 1, ThresholdAt 26 (121+i) := by decide +kernel

theorem threshold_26_122 : ∀ i ∈ List.range 1, ThresholdAt 26 (122+i) := by decide +kernel

theorem threshold_26_123 : ∀ i ∈ List.range 1, ThresholdAt 26 (123+i) := by decide +kernel

theorem threshold_26_124 : ∀ i ∈ List.range 1, ThresholdAt 26 (124+i) := by decide +kernel

theorem threshold_26_125 : ∀ i ∈ List.range 1, ThresholdAt 26 (125+i) := by decide +kernel

theorem threshold_26_126 : ∀ i ∈ List.range 1, ThresholdAt 26 (126+i) := by decide +kernel

theorem threshold_26_127 : ∀ i ∈ List.range 1, ThresholdAt 26 (127+i) := by decide +kernel

theorem threshold_26_128 : ∀ i ∈ List.range 1, ThresholdAt 26 (128+i) := by decide +kernel

theorem threshold_26_129 : ∀ i ∈ List.range 1, ThresholdAt 26 (129+i) := by decide +kernel

theorem threshold_26_130 : ∀ i ∈ List.range 1, ThresholdAt 26 (130+i) := by decide +kernel

theorem threshold_26 (v : ℕ) (hv : v ∈ List.range 131) : ThresholdAt 26 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 26 v)
  have h := (join 0 65 66 (join 0 32 33 (join 0 16 16 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_26_0 threshold_26_1) (join 2 1 1 threshold_26_2 threshold_26_3)) (join 4 2 2 (join 4 1 1 threshold_26_4 threshold_26_5) (join 6 1 1 threshold_26_6 threshold_26_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_26_8 threshold_26_9) (join 10 1 1 threshold_26_10 threshold_26_11)) (join 12 2 2 (join 12 1 1 threshold_26_12 threshold_26_13) (join 14 1 1 threshold_26_14 threshold_26_15)))) (join 16 8 8 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_26_16 threshold_26_17) (join 18 1 1 threshold_26_18 threshold_26_19)) (join 20 2 2 (join 20 1 1 threshold_26_20 threshold_26_21) (join 22 1 1 threshold_26_22 threshold_26_23))) (join 24 4 4 (join 24 2 2 (join 24 1 1 threshold_26_24 threshold_26_25) (join 26 1 1 threshold_26_26 threshold_26_27)) (join 28 2 2 (join 28 1 1 threshold_26_28 threshold_26_29) (join 30 1 1 threshold_26_30 threshold_26_31))))) (join 32 16 17 (join 32 8 8 (join 32 4 4 (join 32 2 2 (join 32 1 1 threshold_26_32 threshold_26_33) (join 34 1 1 threshold_26_34 threshold_26_35)) (join 36 2 2 (join 36 1 1 threshold_26_36 threshold_26_37) (join 38 1 1 threshold_26_38 threshold_26_39))) (join 40 4 4 (join 40 2 2 (join 40 1 1 threshold_26_40 threshold_26_41) (join 42 1 1 threshold_26_42 threshold_26_43)) (join 44 2 2 (join 44 1 1 threshold_26_44 threshold_26_45) (join 46 1 1 threshold_26_46 threshold_26_47)))) (join 48 8 9 (join 48 4 4 (join 48 2 2 (join 48 1 1 threshold_26_48 threshold_26_49) (join 50 1 1 threshold_26_50 threshold_26_51)) (join 52 2 2 (join 52 1 1 threshold_26_52 threshold_26_53) (join 54 1 1 threshold_26_54 threshold_26_55))) (join 56 4 5 (join 56 2 2 (join 56 1 1 threshold_26_56 threshold_26_57) (join 58 1 1 threshold_26_58 threshold_26_59)) (join 60 2 3 (join 60 1 1 threshold_26_60 threshold_26_61) (join 62 1 2 threshold_26_62 (join 63 1 1 threshold_26_63 threshold_26_64))))))) (join 65 33 33 (join 65 16 17 (join 65 8 8 (join 65 4 4 (join 65 2 2 (join 65 1 1 threshold_26_65 threshold_26_66) (join 67 1 1 threshold_26_67 threshold_26_68)) (join 69 2 2 (join 69 1 1 threshold_26_69 threshold_26_70) (join 71 1 1 threshold_26_71 threshold_26_72))) (join 73 4 4 (join 73 2 2 (join 73 1 1 threshold_26_73 threshold_26_74) (join 75 1 1 threshold_26_75 threshold_26_76)) (join 77 2 2 (join 77 1 1 threshold_26_77 threshold_26_78) (join 79 1 1 threshold_26_79 threshold_26_80)))) (join 81 8 9 (join 81 4 4 (join 81 2 2 (join 81 1 1 threshold_26_81 threshold_26_82) (join 83 1 1 threshold_26_83 threshold_26_84)) (join 85 2 2 (join 85 1 1 threshold_26_85 threshold_26_86) (join 87 1 1 threshold_26_87 threshold_26_88))) (join 89 4 5 (join 89 2 2 (join 89 1 1 threshold_26_89 threshold_26_90) (join 91 1 1 threshold_26_91 threshold_26_92)) (join 93 2 3 (join 93 1 1 threshold_26_93 threshold_26_94) (join 95 1 2 threshold_26_95 (join 96 1 1 threshold_26_96 threshold_26_97)))))) (join 98 16 17 (join 98 8 8 (join 98 4 4 (join 98 2 2 (join 98 1 1 threshold_26_98 threshold_26_99) (join 100 1 1 threshold_26_100 threshold_26_101)) (join 102 2 2 (join 102 1 1 threshold_26_102 threshold_26_103) (join 104 1 1 threshold_26_104 threshold_26_105))) (join 106 4 4 (join 106 2 2 (join 106 1 1 threshold_26_106 threshold_26_107) (join 108 1 1 threshold_26_108 threshold_26_109)) (join 110 2 2 (join 110 1 1 threshold_26_110 threshold_26_111) (join 112 1 1 threshold_26_112 threshold_26_113)))) (join 114 8 9 (join 114 4 4 (join 114 2 2 (join 114 1 1 threshold_26_114 threshold_26_115) (join 116 1 1 threshold_26_116 threshold_26_117)) (join 118 2 2 (join 118 1 1 threshold_26_118 threshold_26_119) (join 120 1 1 threshold_26_120 threshold_26_121))) (join 122 4 5 (join 122 2 2 (join 122 1 1 threshold_26_122 threshold_26_123) (join 124 1 1 threshold_26_124 threshold_26_125)) (join 126 2 3 (join 126 1 1 threshold_26_126 threshold_26_127) (join 128 1 2 threshold_26_128 (join 129 1 1 threshold_26_129 threshold_26_130))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_26_0 : ∀ i ∈ List.range 4, LedgerAt 26 (0+i) := by decide +kernel

theorem ledger_26_4 : ∀ i ∈ List.range 4, LedgerAt 26 (4+i) := by decide +kernel

theorem ledger_26_8 : ∀ i ∈ List.range 4, LedgerAt 26 (8+i) := by decide +kernel

theorem ledger_26_12 : ∀ i ∈ List.range 4, LedgerAt 26 (12+i) := by decide +kernel

theorem ledger_26_16 : ∀ i ∈ List.range 4, LedgerAt 26 (16+i) := by decide +kernel

theorem ledger_26_20 : ∀ i ∈ List.range 4, LedgerAt 26 (20+i) := by decide +kernel

theorem ledger_26_24 : ∀ i ∈ List.range 4, LedgerAt 26 (24+i) := by decide +kernel

theorem ledger_26_28 : ∀ i ∈ List.range 4, LedgerAt 26 (28+i) := by decide +kernel

theorem ledger_26_32 : ∀ i ∈ List.range 4, LedgerAt 26 (32+i) := by decide +kernel

theorem ledger_26_36 : ∀ i ∈ List.range 4, LedgerAt 26 (36+i) := by decide +kernel

theorem ledger_26_40 : ∀ i ∈ List.range 4, LedgerAt 26 (40+i) := by decide +kernel

theorem ledger_26_44 : ∀ i ∈ List.range 4, LedgerAt 26 (44+i) := by decide +kernel

theorem ledger_26_48 : ∀ i ∈ List.range 4, LedgerAt 26 (48+i) := by decide +kernel

theorem ledger_26_52 : ∀ i ∈ List.range 4, LedgerAt 26 (52+i) := by decide +kernel

theorem ledger_26_56 : ∀ i ∈ List.range 4, LedgerAt 26 (56+i) := by decide +kernel

theorem ledger_26_60 : ∀ i ∈ List.range 4, LedgerAt 26 (60+i) := by decide +kernel

theorem ledger_26_64 : ∀ i ∈ List.range 4, LedgerAt 26 (64+i) := by decide +kernel

theorem ledger_26_68 : ∀ i ∈ List.range 4, LedgerAt 26 (68+i) := by decide +kernel

theorem ledger_26_72 : ∀ i ∈ List.range 4, LedgerAt 26 (72+i) := by decide +kernel

theorem ledger_26_76 : ∀ i ∈ List.range 4, LedgerAt 26 (76+i) := by decide +kernel

theorem ledger_26_80 : ∀ i ∈ List.range 4, LedgerAt 26 (80+i) := by decide +kernel

theorem ledger_26_84 : ∀ i ∈ List.range 4, LedgerAt 26 (84+i) := by decide +kernel

theorem ledger_26_88 : ∀ i ∈ List.range 4, LedgerAt 26 (88+i) := by decide +kernel

theorem ledger_26_92 : ∀ i ∈ List.range 4, LedgerAt 26 (92+i) := by decide +kernel

theorem ledger_26_96 : ∀ i ∈ List.range 4, LedgerAt 26 (96+i) := by decide +kernel

theorem ledger_26_100 : ∀ i ∈ List.range 4, LedgerAt 26 (100+i) := by decide +kernel

theorem ledger_26_104 : ∀ i ∈ List.range 4, LedgerAt 26 (104+i) := by decide +kernel

theorem ledger_26_108 : ∀ i ∈ List.range 4, LedgerAt 26 (108+i) := by decide +kernel

theorem ledger_26_112 : ∀ i ∈ List.range 4, LedgerAt 26 (112+i) := by decide +kernel

theorem ledger_26_116 : ∀ i ∈ List.range 4, LedgerAt 26 (116+i) := by decide +kernel

theorem ledger_26_120 : ∀ i ∈ List.range 4, LedgerAt 26 (120+i) := by decide +kernel

theorem ledger_26_124 : ∀ i ∈ List.range 4, LedgerAt 26 (124+i) := by decide +kernel

theorem ledger_26_128 : ∀ i ∈ List.range 3, LedgerAt 26 (128+i) := by decide +kernel

theorem ledger_26 (v : ℕ) (hv : v ∈ List.range 131) : LedgerAt 26 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 26 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_26_0 ledger_26_4) (join 8 4 4 ledger_26_8 ledger_26_12)) (join 16 8 8 (join 16 4 4 ledger_26_16 ledger_26_20) (join 24 4 4 ledger_26_24 ledger_26_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_26_32 ledger_26_36) (join 40 4 4 ledger_26_40 ledger_26_44)) (join 48 8 8 (join 48 4 4 ledger_26_48 ledger_26_52) (join 56 4 4 ledger_26_56 ledger_26_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_26_64 ledger_26_68) (join 72 4 4 ledger_26_72 ledger_26_76)) (join 80 8 8 (join 80 4 4 ledger_26_80 ledger_26_84) (join 88 4 4 ledger_26_88 ledger_26_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 ledger_26_96 ledger_26_100) (join 104 4 4 ledger_26_104 ledger_26_108)) (join 112 8 11 (join 112 4 4 ledger_26_112 ledger_26_116) (join 120 4 7 ledger_26_120 (join 124 4 3 ledger_26_124 ledger_26_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
