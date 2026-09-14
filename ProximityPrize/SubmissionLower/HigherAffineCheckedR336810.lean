import ProximityPrize.SubmissionLower.HigherAffineCheckedR326810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_33_0 : ∀ i ∈ List.range 4, SingleAt 33 (0+i) := by decide +kernel

theorem single_33_4 : ∀ i ∈ List.range 4, SingleAt 33 (4+i) := by decide +kernel

theorem single_33_8 : ∀ i ∈ List.range 4, SingleAt 33 (8+i) := by decide +kernel

theorem single_33_12 : ∀ i ∈ List.range 4, SingleAt 33 (12+i) := by decide +kernel

theorem single_33_16 : ∀ i ∈ List.range 4, SingleAt 33 (16+i) := by decide +kernel

theorem single_33_20 : ∀ i ∈ List.range 4, SingleAt 33 (20+i) := by decide +kernel

theorem single_33_24 : ∀ i ∈ List.range 4, SingleAt 33 (24+i) := by decide +kernel

theorem single_33_28 : ∀ i ∈ List.range 4, SingleAt 33 (28+i) := by decide +kernel

theorem single_33_32 : ∀ i ∈ List.range 4, SingleAt 33 (32+i) := by decide +kernel

theorem single_33_36 : ∀ i ∈ List.range 4, SingleAt 33 (36+i) := by decide +kernel

theorem single_33_40 : ∀ i ∈ List.range 4, SingleAt 33 (40+i) := by decide +kernel

theorem single_33_44 : ∀ i ∈ List.range 4, SingleAt 33 (44+i) := by decide +kernel

theorem single_33_48 : ∀ i ∈ List.range 4, SingleAt 33 (48+i) := by decide +kernel

theorem single_33_52 : ∀ i ∈ List.range 4, SingleAt 33 (52+i) := by decide +kernel

theorem single_33_56 : ∀ i ∈ List.range 4, SingleAt 33 (56+i) := by decide +kernel

theorem single_33_60 : ∀ i ∈ List.range 4, SingleAt 33 (60+i) := by decide +kernel

theorem single_33_64 : ∀ i ∈ List.range 4, SingleAt 33 (64+i) := by decide +kernel

theorem single_33_68 : ∀ i ∈ List.range 4, SingleAt 33 (68+i) := by decide +kernel

theorem single_33_72 : ∀ i ∈ List.range 4, SingleAt 33 (72+i) := by decide +kernel

theorem single_33_76 : ∀ i ∈ List.range 4, SingleAt 33 (76+i) := by decide +kernel

theorem single_33_80 : ∀ i ∈ List.range 4, SingleAt 33 (80+i) := by decide +kernel

theorem single_33_84 : ∀ i ∈ List.range 4, SingleAt 33 (84+i) := by decide +kernel

theorem single_33_88 : ∀ i ∈ List.range 4, SingleAt 33 (88+i) := by decide +kernel

theorem single_33_92 : ∀ i ∈ List.range 4, SingleAt 33 (92+i) := by decide +kernel

theorem single_33_96 : ∀ i ∈ List.range 4, SingleAt 33 (96+i) := by decide +kernel

theorem single_33_100 : ∀ i ∈ List.range 4, SingleAt 33 (100+i) := by decide +kernel

theorem single_33_104 : ∀ i ∈ List.range 4, SingleAt 33 (104+i) := by decide +kernel

theorem single_33_108 : ∀ i ∈ List.range 4, SingleAt 33 (108+i) := by decide +kernel

theorem single_33_112 : ∀ i ∈ List.range 4, SingleAt 33 (112+i) := by decide +kernel

theorem single_33_116 : ∀ i ∈ List.range 4, SingleAt 33 (116+i) := by decide +kernel

theorem single_33_120 : ∀ i ∈ List.range 4, SingleAt 33 (120+i) := by decide +kernel

theorem single_33 (v : ℕ) (hv : v ∈ List.range 124) : SingleAt 33 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 33 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 single_33_0 (join 4 4 4 single_33_4 single_33_8)) (join 12 8 8 (join 12 4 4 single_33_12 single_33_16) (join 20 4 4 single_33_20 single_33_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 single_33_28 single_33_32) (join 36 4 4 single_33_36 single_33_40)) (join 44 8 8 (join 44 4 4 single_33_44 single_33_48) (join 52 4 4 single_33_52 single_33_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 single_33_60 single_33_64) (join 68 4 4 single_33_68 single_33_72)) (join 76 8 8 (join 76 4 4 single_33_76 single_33_80) (join 84 4 4 single_33_84 single_33_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 single_33_92 single_33_96) (join 100 4 4 single_33_100 single_33_104)) (join 108 8 8 (join 108 4 4 single_33_108 single_33_112) (join 116 4 4 single_33_116 single_33_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_33_0 : ∀ i ∈ List.range 4, PhaseAt 33 (0+i) := by decide +kernel

theorem phase_33_4 : ∀ i ∈ List.range 4, PhaseAt 33 (4+i) := by decide +kernel

theorem phase_33_8 : ∀ i ∈ List.range 4, PhaseAt 33 (8+i) := by decide +kernel

theorem phase_33_12 : ∀ i ∈ List.range 4, PhaseAt 33 (12+i) := by decide +kernel

theorem phase_33_16 : ∀ i ∈ List.range 4, PhaseAt 33 (16+i) := by decide +kernel

theorem phase_33_20 : ∀ i ∈ List.range 4, PhaseAt 33 (20+i) := by decide +kernel

theorem phase_33_24 : ∀ i ∈ List.range 4, PhaseAt 33 (24+i) := by decide +kernel

theorem phase_33_28 : ∀ i ∈ List.range 4, PhaseAt 33 (28+i) := by decide +kernel

theorem phase_33_32 : ∀ i ∈ List.range 4, PhaseAt 33 (32+i) := by decide +kernel

theorem phase_33_36 : ∀ i ∈ List.range 4, PhaseAt 33 (36+i) := by decide +kernel

theorem phase_33_40 : ∀ i ∈ List.range 4, PhaseAt 33 (40+i) := by decide +kernel

theorem phase_33_44 : ∀ i ∈ List.range 4, PhaseAt 33 (44+i) := by decide +kernel

theorem phase_33_48 : ∀ i ∈ List.range 4, PhaseAt 33 (48+i) := by decide +kernel

theorem phase_33_52 : ∀ i ∈ List.range 4, PhaseAt 33 (52+i) := by decide +kernel

theorem phase_33_56 : ∀ i ∈ List.range 4, PhaseAt 33 (56+i) := by decide +kernel

theorem phase_33_60 : ∀ i ∈ List.range 4, PhaseAt 33 (60+i) := by decide +kernel

theorem phase_33_64 : ∀ i ∈ List.range 4, PhaseAt 33 (64+i) := by decide +kernel

theorem phase_33_68 : ∀ i ∈ List.range 4, PhaseAt 33 (68+i) := by decide +kernel

theorem phase_33_72 : ∀ i ∈ List.range 4, PhaseAt 33 (72+i) := by decide +kernel

theorem phase_33_76 : ∀ i ∈ List.range 4, PhaseAt 33 (76+i) := by decide +kernel

theorem phase_33_80 : ∀ i ∈ List.range 4, PhaseAt 33 (80+i) := by decide +kernel

theorem phase_33_84 : ∀ i ∈ List.range 4, PhaseAt 33 (84+i) := by decide +kernel

theorem phase_33_88 : ∀ i ∈ List.range 4, PhaseAt 33 (88+i) := by decide +kernel

theorem phase_33_92 : ∀ i ∈ List.range 4, PhaseAt 33 (92+i) := by decide +kernel

theorem phase_33_96 : ∀ i ∈ List.range 4, PhaseAt 33 (96+i) := by decide +kernel

theorem phase_33_100 : ∀ i ∈ List.range 4, PhaseAt 33 (100+i) := by decide +kernel

theorem phase_33_104 : ∀ i ∈ List.range 4, PhaseAt 33 (104+i) := by decide +kernel

theorem phase_33_108 : ∀ i ∈ List.range 4, PhaseAt 33 (108+i) := by decide +kernel

theorem phase_33_112 : ∀ i ∈ List.range 4, PhaseAt 33 (112+i) := by decide +kernel

theorem phase_33_116 : ∀ i ∈ List.range 4, PhaseAt 33 (116+i) := by decide +kernel

theorem phase_33_120 : ∀ i ∈ List.range 4, PhaseAt 33 (120+i) := by decide +kernel

theorem phase_33 (v : ℕ) (hv : v ∈ List.range 124) : PhaseAt 33 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 33 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_33_0 (join 4 4 4 phase_33_4 phase_33_8)) (join 12 8 8 (join 12 4 4 phase_33_12 phase_33_16) (join 20 4 4 phase_33_20 phase_33_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_33_28 phase_33_32) (join 36 4 4 phase_33_36 phase_33_40)) (join 44 8 8 (join 44 4 4 phase_33_44 phase_33_48) (join 52 4 4 phase_33_52 phase_33_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 phase_33_60 phase_33_64) (join 68 4 4 phase_33_68 phase_33_72)) (join 76 8 8 (join 76 4 4 phase_33_76 phase_33_80) (join 84 4 4 phase_33_84 phase_33_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 phase_33_92 phase_33_96) (join 100 4 4 phase_33_100 phase_33_104)) (join 108 8 8 (join 108 4 4 phase_33_108 phase_33_112) (join 116 4 4 phase_33_116 phase_33_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_33_0 : ∀ i ∈ List.range 1, ThresholdAt 33 (0+i) := by decide +kernel

theorem threshold_33_1 : ∀ i ∈ List.range 1, ThresholdAt 33 (1+i) := by decide +kernel

theorem threshold_33_2 : ∀ i ∈ List.range 1, ThresholdAt 33 (2+i) := by decide +kernel

theorem threshold_33_3 : ∀ i ∈ List.range 1, ThresholdAt 33 (3+i) := by decide +kernel

theorem threshold_33_4 : ∀ i ∈ List.range 1, ThresholdAt 33 (4+i) := by decide +kernel

theorem threshold_33_5 : ∀ i ∈ List.range 1, ThresholdAt 33 (5+i) := by decide +kernel

theorem threshold_33_6 : ∀ i ∈ List.range 1, ThresholdAt 33 (6+i) := by decide +kernel

theorem threshold_33_7 : ∀ i ∈ List.range 1, ThresholdAt 33 (7+i) := by decide +kernel

theorem threshold_33_8 : ∀ i ∈ List.range 1, ThresholdAt 33 (8+i) := by decide +kernel

theorem threshold_33_9 : ∀ i ∈ List.range 1, ThresholdAt 33 (9+i) := by decide +kernel

theorem threshold_33_10 : ∀ i ∈ List.range 1, ThresholdAt 33 (10+i) := by decide +kernel

theorem threshold_33_11 : ∀ i ∈ List.range 1, ThresholdAt 33 (11+i) := by decide +kernel

theorem threshold_33_12 : ∀ i ∈ List.range 1, ThresholdAt 33 (12+i) := by decide +kernel

theorem threshold_33_13 : ∀ i ∈ List.range 1, ThresholdAt 33 (13+i) := by decide +kernel

theorem threshold_33_14 : ∀ i ∈ List.range 1, ThresholdAt 33 (14+i) := by decide +kernel

theorem threshold_33_15 : ∀ i ∈ List.range 1, ThresholdAt 33 (15+i) := by decide +kernel

theorem threshold_33_16 : ∀ i ∈ List.range 1, ThresholdAt 33 (16+i) := by decide +kernel

theorem threshold_33_17 : ∀ i ∈ List.range 1, ThresholdAt 33 (17+i) := by decide +kernel

theorem threshold_33_18 : ∀ i ∈ List.range 1, ThresholdAt 33 (18+i) := by decide +kernel

theorem threshold_33_19 : ∀ i ∈ List.range 1, ThresholdAt 33 (19+i) := by decide +kernel

theorem threshold_33_20 : ∀ i ∈ List.range 1, ThresholdAt 33 (20+i) := by decide +kernel

theorem threshold_33_21 : ∀ i ∈ List.range 1, ThresholdAt 33 (21+i) := by decide +kernel

theorem threshold_33_22 : ∀ i ∈ List.range 1, ThresholdAt 33 (22+i) := by decide +kernel

theorem threshold_33_23 : ∀ i ∈ List.range 1, ThresholdAt 33 (23+i) := by decide +kernel

theorem threshold_33_24 : ∀ i ∈ List.range 1, ThresholdAt 33 (24+i) := by decide +kernel

theorem threshold_33_25 : ∀ i ∈ List.range 1, ThresholdAt 33 (25+i) := by decide +kernel

theorem threshold_33_26 : ∀ i ∈ List.range 1, ThresholdAt 33 (26+i) := by decide +kernel

theorem threshold_33_27 : ∀ i ∈ List.range 1, ThresholdAt 33 (27+i) := by decide +kernel

theorem threshold_33_28 : ∀ i ∈ List.range 1, ThresholdAt 33 (28+i) := by decide +kernel

theorem threshold_33_29 : ∀ i ∈ List.range 1, ThresholdAt 33 (29+i) := by decide +kernel

theorem threshold_33_30 : ∀ i ∈ List.range 1, ThresholdAt 33 (30+i) := by decide +kernel

theorem threshold_33_31 : ∀ i ∈ List.range 1, ThresholdAt 33 (31+i) := by decide +kernel

theorem threshold_33_32 : ∀ i ∈ List.range 1, ThresholdAt 33 (32+i) := by decide +kernel

theorem threshold_33_33 : ∀ i ∈ List.range 1, ThresholdAt 33 (33+i) := by decide +kernel

theorem threshold_33_34 : ∀ i ∈ List.range 1, ThresholdAt 33 (34+i) := by decide +kernel

theorem threshold_33_35 : ∀ i ∈ List.range 1, ThresholdAt 33 (35+i) := by decide +kernel

theorem threshold_33_36 : ∀ i ∈ List.range 1, ThresholdAt 33 (36+i) := by decide +kernel

theorem threshold_33_37 : ∀ i ∈ List.range 1, ThresholdAt 33 (37+i) := by decide +kernel

theorem threshold_33_38 : ∀ i ∈ List.range 1, ThresholdAt 33 (38+i) := by decide +kernel

theorem threshold_33_39 : ∀ i ∈ List.range 1, ThresholdAt 33 (39+i) := by decide +kernel

theorem threshold_33_40 : ∀ i ∈ List.range 1, ThresholdAt 33 (40+i) := by decide +kernel

theorem threshold_33_41 : ∀ i ∈ List.range 1, ThresholdAt 33 (41+i) := by decide +kernel

theorem threshold_33_42 : ∀ i ∈ List.range 1, ThresholdAt 33 (42+i) := by decide +kernel

theorem threshold_33_43 : ∀ i ∈ List.range 1, ThresholdAt 33 (43+i) := by decide +kernel

theorem threshold_33_44 : ∀ i ∈ List.range 1, ThresholdAt 33 (44+i) := by decide +kernel

theorem threshold_33_45 : ∀ i ∈ List.range 1, ThresholdAt 33 (45+i) := by decide +kernel

theorem threshold_33_46 : ∀ i ∈ List.range 1, ThresholdAt 33 (46+i) := by decide +kernel

theorem threshold_33_47 : ∀ i ∈ List.range 1, ThresholdAt 33 (47+i) := by decide +kernel

theorem threshold_33_48 : ∀ i ∈ List.range 1, ThresholdAt 33 (48+i) := by decide +kernel

theorem threshold_33_49 : ∀ i ∈ List.range 1, ThresholdAt 33 (49+i) := by decide +kernel

theorem threshold_33_50 : ∀ i ∈ List.range 1, ThresholdAt 33 (50+i) := by decide +kernel

theorem threshold_33_51 : ∀ i ∈ List.range 1, ThresholdAt 33 (51+i) := by decide +kernel

theorem threshold_33_52 : ∀ i ∈ List.range 1, ThresholdAt 33 (52+i) := by decide +kernel

theorem threshold_33_53 : ∀ i ∈ List.range 1, ThresholdAt 33 (53+i) := by decide +kernel

theorem threshold_33_54 : ∀ i ∈ List.range 1, ThresholdAt 33 (54+i) := by decide +kernel

theorem threshold_33_55 : ∀ i ∈ List.range 1, ThresholdAt 33 (55+i) := by decide +kernel

theorem threshold_33_56 : ∀ i ∈ List.range 1, ThresholdAt 33 (56+i) := by decide +kernel

theorem threshold_33_57 : ∀ i ∈ List.range 1, ThresholdAt 33 (57+i) := by decide +kernel

theorem threshold_33_58 : ∀ i ∈ List.range 1, ThresholdAt 33 (58+i) := by decide +kernel

theorem threshold_33_59 : ∀ i ∈ List.range 1, ThresholdAt 33 (59+i) := by decide +kernel

theorem threshold_33_60 : ∀ i ∈ List.range 1, ThresholdAt 33 (60+i) := by decide +kernel

theorem threshold_33_61 : ∀ i ∈ List.range 1, ThresholdAt 33 (61+i) := by decide +kernel

theorem threshold_33_62 : ∀ i ∈ List.range 1, ThresholdAt 33 (62+i) := by decide +kernel

theorem threshold_33_63 : ∀ i ∈ List.range 1, ThresholdAt 33 (63+i) := by decide +kernel

theorem threshold_33_64 : ∀ i ∈ List.range 1, ThresholdAt 33 (64+i) := by decide +kernel

theorem threshold_33_65 : ∀ i ∈ List.range 1, ThresholdAt 33 (65+i) := by decide +kernel

theorem threshold_33_66 : ∀ i ∈ List.range 1, ThresholdAt 33 (66+i) := by decide +kernel

theorem threshold_33_67 : ∀ i ∈ List.range 1, ThresholdAt 33 (67+i) := by decide +kernel

theorem threshold_33_68 : ∀ i ∈ List.range 1, ThresholdAt 33 (68+i) := by decide +kernel

theorem threshold_33_69 : ∀ i ∈ List.range 1, ThresholdAt 33 (69+i) := by decide +kernel

theorem threshold_33_70 : ∀ i ∈ List.range 1, ThresholdAt 33 (70+i) := by decide +kernel

theorem threshold_33_71 : ∀ i ∈ List.range 1, ThresholdAt 33 (71+i) := by decide +kernel

theorem threshold_33_72 : ∀ i ∈ List.range 1, ThresholdAt 33 (72+i) := by decide +kernel

theorem threshold_33_73 : ∀ i ∈ List.range 1, ThresholdAt 33 (73+i) := by decide +kernel

theorem threshold_33_74 : ∀ i ∈ List.range 1, ThresholdAt 33 (74+i) := by decide +kernel

theorem threshold_33_75 : ∀ i ∈ List.range 1, ThresholdAt 33 (75+i) := by decide +kernel

theorem threshold_33_76 : ∀ i ∈ List.range 1, ThresholdAt 33 (76+i) := by decide +kernel

theorem threshold_33_77 : ∀ i ∈ List.range 1, ThresholdAt 33 (77+i) := by decide +kernel

theorem threshold_33_78 : ∀ i ∈ List.range 1, ThresholdAt 33 (78+i) := by decide +kernel

theorem threshold_33_79 : ∀ i ∈ List.range 1, ThresholdAt 33 (79+i) := by decide +kernel

theorem threshold_33_80 : ∀ i ∈ List.range 1, ThresholdAt 33 (80+i) := by decide +kernel

theorem threshold_33_81 : ∀ i ∈ List.range 1, ThresholdAt 33 (81+i) := by decide +kernel

theorem threshold_33_82 : ∀ i ∈ List.range 1, ThresholdAt 33 (82+i) := by decide +kernel

theorem threshold_33_83 : ∀ i ∈ List.range 1, ThresholdAt 33 (83+i) := by decide +kernel

theorem threshold_33_84 : ∀ i ∈ List.range 1, ThresholdAt 33 (84+i) := by decide +kernel

theorem threshold_33_85 : ∀ i ∈ List.range 1, ThresholdAt 33 (85+i) := by decide +kernel

theorem threshold_33_86 : ∀ i ∈ List.range 1, ThresholdAt 33 (86+i) := by decide +kernel

theorem threshold_33_87 : ∀ i ∈ List.range 1, ThresholdAt 33 (87+i) := by decide +kernel

theorem threshold_33_88 : ∀ i ∈ List.range 1, ThresholdAt 33 (88+i) := by decide +kernel

theorem threshold_33_89 : ∀ i ∈ List.range 1, ThresholdAt 33 (89+i) := by decide +kernel

theorem threshold_33_90 : ∀ i ∈ List.range 1, ThresholdAt 33 (90+i) := by decide +kernel

theorem threshold_33_91 : ∀ i ∈ List.range 1, ThresholdAt 33 (91+i) := by decide +kernel

theorem threshold_33_92 : ∀ i ∈ List.range 1, ThresholdAt 33 (92+i) := by decide +kernel

theorem threshold_33_93 : ∀ i ∈ List.range 1, ThresholdAt 33 (93+i) := by decide +kernel

theorem threshold_33_94 : ∀ i ∈ List.range 1, ThresholdAt 33 (94+i) := by decide +kernel

theorem threshold_33_95 : ∀ i ∈ List.range 1, ThresholdAt 33 (95+i) := by decide +kernel

theorem threshold_33_96 : ∀ i ∈ List.range 1, ThresholdAt 33 (96+i) := by decide +kernel

theorem threshold_33_97 : ∀ i ∈ List.range 1, ThresholdAt 33 (97+i) := by decide +kernel

theorem threshold_33_98 : ∀ i ∈ List.range 1, ThresholdAt 33 (98+i) := by decide +kernel

theorem threshold_33_99 : ∀ i ∈ List.range 1, ThresholdAt 33 (99+i) := by decide +kernel

theorem threshold_33_100 : ∀ i ∈ List.range 1, ThresholdAt 33 (100+i) := by decide +kernel

theorem threshold_33_101 : ∀ i ∈ List.range 1, ThresholdAt 33 (101+i) := by decide +kernel

theorem threshold_33_102 : ∀ i ∈ List.range 1, ThresholdAt 33 (102+i) := by decide +kernel

theorem threshold_33_103 : ∀ i ∈ List.range 1, ThresholdAt 33 (103+i) := by decide +kernel

theorem threshold_33_104 : ∀ i ∈ List.range 1, ThresholdAt 33 (104+i) := by decide +kernel

theorem threshold_33_105 : ∀ i ∈ List.range 1, ThresholdAt 33 (105+i) := by decide +kernel

theorem threshold_33_106 : ∀ i ∈ List.range 1, ThresholdAt 33 (106+i) := by decide +kernel

theorem threshold_33_107 : ∀ i ∈ List.range 1, ThresholdAt 33 (107+i) := by decide +kernel

theorem threshold_33_108 : ∀ i ∈ List.range 1, ThresholdAt 33 (108+i) := by decide +kernel

theorem threshold_33_109 : ∀ i ∈ List.range 1, ThresholdAt 33 (109+i) := by decide +kernel

theorem threshold_33_110 : ∀ i ∈ List.range 1, ThresholdAt 33 (110+i) := by decide +kernel

theorem threshold_33_111 : ∀ i ∈ List.range 1, ThresholdAt 33 (111+i) := by decide +kernel

theorem threshold_33_112 : ∀ i ∈ List.range 1, ThresholdAt 33 (112+i) := by decide +kernel

theorem threshold_33_113 : ∀ i ∈ List.range 1, ThresholdAt 33 (113+i) := by decide +kernel

theorem threshold_33_114 : ∀ i ∈ List.range 1, ThresholdAt 33 (114+i) := by decide +kernel

theorem threshold_33_115 : ∀ i ∈ List.range 1, ThresholdAt 33 (115+i) := by decide +kernel

theorem threshold_33_116 : ∀ i ∈ List.range 1, ThresholdAt 33 (116+i) := by decide +kernel

theorem threshold_33_117 : ∀ i ∈ List.range 1, ThresholdAt 33 (117+i) := by decide +kernel

theorem threshold_33_118 : ∀ i ∈ List.range 1, ThresholdAt 33 (118+i) := by decide +kernel

theorem threshold_33_119 : ∀ i ∈ List.range 1, ThresholdAt 33 (119+i) := by decide +kernel

theorem threshold_33_120 : ∀ i ∈ List.range 1, ThresholdAt 33 (120+i) := by decide +kernel

theorem threshold_33_121 : ∀ i ∈ List.range 1, ThresholdAt 33 (121+i) := by decide +kernel

theorem threshold_33_122 : ∀ i ∈ List.range 1, ThresholdAt 33 (122+i) := by decide +kernel

theorem threshold_33_123 : ∀ i ∈ List.range 1, ThresholdAt 33 (123+i) := by decide +kernel

theorem threshold_33 (v : ℕ) (hv : v ∈ List.range 124) : ThresholdAt 33 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 33 v)
  have h := (join 0 62 62 (join 0 31 31 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_33_0 (join 1 1 1 threshold_33_1 threshold_33_2)) (join 3 2 2 (join 3 1 1 threshold_33_3 threshold_33_4) (join 5 1 1 threshold_33_5 threshold_33_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_33_7 threshold_33_8) (join 9 1 1 threshold_33_9 threshold_33_10)) (join 11 2 2 (join 11 1 1 threshold_33_11 threshold_33_12) (join 13 1 1 threshold_33_13 threshold_33_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_33_15 threshold_33_16) (join 17 1 1 threshold_33_17 threshold_33_18)) (join 19 2 2 (join 19 1 1 threshold_33_19 threshold_33_20) (join 21 1 1 threshold_33_21 threshold_33_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_33_23 threshold_33_24) (join 25 1 1 threshold_33_25 threshold_33_26)) (join 27 2 2 (join 27 1 1 threshold_33_27 threshold_33_28) (join 29 1 1 threshold_33_29 threshold_33_30))))) (join 31 15 16 (join 31 7 8 (join 31 3 4 (join 31 1 2 threshold_33_31 (join 32 1 1 threshold_33_32 threshold_33_33)) (join 34 2 2 (join 34 1 1 threshold_33_34 threshold_33_35) (join 36 1 1 threshold_33_36 threshold_33_37))) (join 38 4 4 (join 38 2 2 (join 38 1 1 threshold_33_38 threshold_33_39) (join 40 1 1 threshold_33_40 threshold_33_41)) (join 42 2 2 (join 42 1 1 threshold_33_42 threshold_33_43) (join 44 1 1 threshold_33_44 threshold_33_45)))) (join 46 8 8 (join 46 4 4 (join 46 2 2 (join 46 1 1 threshold_33_46 threshold_33_47) (join 48 1 1 threshold_33_48 threshold_33_49)) (join 50 2 2 (join 50 1 1 threshold_33_50 threshold_33_51) (join 52 1 1 threshold_33_52 threshold_33_53))) (join 54 4 4 (join 54 2 2 (join 54 1 1 threshold_33_54 threshold_33_55) (join 56 1 1 threshold_33_56 threshold_33_57)) (join 58 2 2 (join 58 1 1 threshold_33_58 threshold_33_59) (join 60 1 1 threshold_33_60 threshold_33_61)))))) (join 62 31 31 (join 62 15 16 (join 62 7 8 (join 62 3 4 (join 62 1 2 threshold_33_62 (join 63 1 1 threshold_33_63 threshold_33_64)) (join 65 2 2 (join 65 1 1 threshold_33_65 threshold_33_66) (join 67 1 1 threshold_33_67 threshold_33_68))) (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_33_69 threshold_33_70) (join 71 1 1 threshold_33_71 threshold_33_72)) (join 73 2 2 (join 73 1 1 threshold_33_73 threshold_33_74) (join 75 1 1 threshold_33_75 threshold_33_76)))) (join 77 8 8 (join 77 4 4 (join 77 2 2 (join 77 1 1 threshold_33_77 threshold_33_78) (join 79 1 1 threshold_33_79 threshold_33_80)) (join 81 2 2 (join 81 1 1 threshold_33_81 threshold_33_82) (join 83 1 1 threshold_33_83 threshold_33_84))) (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_33_85 threshold_33_86) (join 87 1 1 threshold_33_87 threshold_33_88)) (join 89 2 2 (join 89 1 1 threshold_33_89 threshold_33_90) (join 91 1 1 threshold_33_91 threshold_33_92))))) (join 93 15 16 (join 93 7 8 (join 93 3 4 (join 93 1 2 threshold_33_93 (join 94 1 1 threshold_33_94 threshold_33_95)) (join 96 2 2 (join 96 1 1 threshold_33_96 threshold_33_97) (join 98 1 1 threshold_33_98 threshold_33_99))) (join 100 4 4 (join 100 2 2 (join 100 1 1 threshold_33_100 threshold_33_101) (join 102 1 1 threshold_33_102 threshold_33_103)) (join 104 2 2 (join 104 1 1 threshold_33_104 threshold_33_105) (join 106 1 1 threshold_33_106 threshold_33_107)))) (join 108 8 8 (join 108 4 4 (join 108 2 2 (join 108 1 1 threshold_33_108 threshold_33_109) (join 110 1 1 threshold_33_110 threshold_33_111)) (join 112 2 2 (join 112 1 1 threshold_33_112 threshold_33_113) (join 114 1 1 threshold_33_114 threshold_33_115))) (join 116 4 4 (join 116 2 2 (join 116 1 1 threshold_33_116 threshold_33_117) (join 118 1 1 threshold_33_118 threshold_33_119)) (join 120 2 2 (join 120 1 1 threshold_33_120 threshold_33_121) (join 122 1 1 threshold_33_122 threshold_33_123)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_33_0 : ∀ i ∈ List.range 4, LedgerAt 33 (0+i) := by decide +kernel

theorem ledger_33_4 : ∀ i ∈ List.range 4, LedgerAt 33 (4+i) := by decide +kernel

theorem ledger_33_8 : ∀ i ∈ List.range 4, LedgerAt 33 (8+i) := by decide +kernel

theorem ledger_33_12 : ∀ i ∈ List.range 4, LedgerAt 33 (12+i) := by decide +kernel

theorem ledger_33_16 : ∀ i ∈ List.range 4, LedgerAt 33 (16+i) := by decide +kernel

theorem ledger_33_20 : ∀ i ∈ List.range 4, LedgerAt 33 (20+i) := by decide +kernel

theorem ledger_33_24 : ∀ i ∈ List.range 4, LedgerAt 33 (24+i) := by decide +kernel

theorem ledger_33_28 : ∀ i ∈ List.range 4, LedgerAt 33 (28+i) := by decide +kernel

theorem ledger_33_32 : ∀ i ∈ List.range 4, LedgerAt 33 (32+i) := by decide +kernel

theorem ledger_33_36 : ∀ i ∈ List.range 4, LedgerAt 33 (36+i) := by decide +kernel

theorem ledger_33_40 : ∀ i ∈ List.range 4, LedgerAt 33 (40+i) := by decide +kernel

theorem ledger_33_44 : ∀ i ∈ List.range 4, LedgerAt 33 (44+i) := by decide +kernel

theorem ledger_33_48 : ∀ i ∈ List.range 4, LedgerAt 33 (48+i) := by decide +kernel

theorem ledger_33_52 : ∀ i ∈ List.range 4, LedgerAt 33 (52+i) := by decide +kernel

theorem ledger_33_56 : ∀ i ∈ List.range 4, LedgerAt 33 (56+i) := by decide +kernel

theorem ledger_33_60 : ∀ i ∈ List.range 4, LedgerAt 33 (60+i) := by decide +kernel

theorem ledger_33_64 : ∀ i ∈ List.range 4, LedgerAt 33 (64+i) := by decide +kernel

theorem ledger_33_68 : ∀ i ∈ List.range 4, LedgerAt 33 (68+i) := by decide +kernel

theorem ledger_33_72 : ∀ i ∈ List.range 4, LedgerAt 33 (72+i) := by decide +kernel

theorem ledger_33_76 : ∀ i ∈ List.range 4, LedgerAt 33 (76+i) := by decide +kernel

theorem ledger_33_80 : ∀ i ∈ List.range 4, LedgerAt 33 (80+i) := by decide +kernel

theorem ledger_33_84 : ∀ i ∈ List.range 4, LedgerAt 33 (84+i) := by decide +kernel

theorem ledger_33_88 : ∀ i ∈ List.range 4, LedgerAt 33 (88+i) := by decide +kernel

theorem ledger_33_92 : ∀ i ∈ List.range 4, LedgerAt 33 (92+i) := by decide +kernel

theorem ledger_33_96 : ∀ i ∈ List.range 4, LedgerAt 33 (96+i) := by decide +kernel

theorem ledger_33_100 : ∀ i ∈ List.range 4, LedgerAt 33 (100+i) := by decide +kernel

theorem ledger_33_104 : ∀ i ∈ List.range 4, LedgerAt 33 (104+i) := by decide +kernel

theorem ledger_33_108 : ∀ i ∈ List.range 4, LedgerAt 33 (108+i) := by decide +kernel

theorem ledger_33_112 : ∀ i ∈ List.range 4, LedgerAt 33 (112+i) := by decide +kernel

theorem ledger_33_116 : ∀ i ∈ List.range 4, LedgerAt 33 (116+i) := by decide +kernel

theorem ledger_33_120 : ∀ i ∈ List.range 4, LedgerAt 33 (120+i) := by decide +kernel

theorem ledger_33 (v : ℕ) (hv : v ∈ List.range 124) : LedgerAt 33 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 33 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_33_0 (join 4 4 4 ledger_33_4 ledger_33_8)) (join 12 8 8 (join 12 4 4 ledger_33_12 ledger_33_16) (join 20 4 4 ledger_33_20 ledger_33_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_33_28 ledger_33_32) (join 36 4 4 ledger_33_36 ledger_33_40)) (join 44 8 8 (join 44 4 4 ledger_33_44 ledger_33_48) (join 52 4 4 ledger_33_52 ledger_33_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 ledger_33_60 ledger_33_64) (join 68 4 4 ledger_33_68 ledger_33_72)) (join 76 8 8 (join 76 4 4 ledger_33_76 ledger_33_80) (join 84 4 4 ledger_33_84 ledger_33_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 ledger_33_92 ledger_33_96) (join 100 4 4 ledger_33_100 ledger_33_104)) (join 108 8 8 (join 108 4 4 ledger_33_108 ledger_33_112) (join 116 4 4 ledger_33_116 ledger_33_120)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
