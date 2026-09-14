import ProximityPrize.SubmissionLower.HigherAffineCheckedR336810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_34_0 : ∀ i ∈ List.range 4, SingleAt 34 (0+i) := by decide +kernel

theorem single_34_4 : ∀ i ∈ List.range 4, SingleAt 34 (4+i) := by decide +kernel

theorem single_34_8 : ∀ i ∈ List.range 4, SingleAt 34 (8+i) := by decide +kernel

theorem single_34_12 : ∀ i ∈ List.range 4, SingleAt 34 (12+i) := by decide +kernel

theorem single_34_16 : ∀ i ∈ List.range 4, SingleAt 34 (16+i) := by decide +kernel

theorem single_34_20 : ∀ i ∈ List.range 4, SingleAt 34 (20+i) := by decide +kernel

theorem single_34_24 : ∀ i ∈ List.range 4, SingleAt 34 (24+i) := by decide +kernel

theorem single_34_28 : ∀ i ∈ List.range 4, SingleAt 34 (28+i) := by decide +kernel

theorem single_34_32 : ∀ i ∈ List.range 4, SingleAt 34 (32+i) := by decide +kernel

theorem single_34_36 : ∀ i ∈ List.range 4, SingleAt 34 (36+i) := by decide +kernel

theorem single_34_40 : ∀ i ∈ List.range 4, SingleAt 34 (40+i) := by decide +kernel

theorem single_34_44 : ∀ i ∈ List.range 4, SingleAt 34 (44+i) := by decide +kernel

theorem single_34_48 : ∀ i ∈ List.range 4, SingleAt 34 (48+i) := by decide +kernel

theorem single_34_52 : ∀ i ∈ List.range 4, SingleAt 34 (52+i) := by decide +kernel

theorem single_34_56 : ∀ i ∈ List.range 4, SingleAt 34 (56+i) := by decide +kernel

theorem single_34_60 : ∀ i ∈ List.range 4, SingleAt 34 (60+i) := by decide +kernel

theorem single_34_64 : ∀ i ∈ List.range 4, SingleAt 34 (64+i) := by decide +kernel

theorem single_34_68 : ∀ i ∈ List.range 4, SingleAt 34 (68+i) := by decide +kernel

theorem single_34_72 : ∀ i ∈ List.range 4, SingleAt 34 (72+i) := by decide +kernel

theorem single_34_76 : ∀ i ∈ List.range 4, SingleAt 34 (76+i) := by decide +kernel

theorem single_34_80 : ∀ i ∈ List.range 4, SingleAt 34 (80+i) := by decide +kernel

theorem single_34_84 : ∀ i ∈ List.range 4, SingleAt 34 (84+i) := by decide +kernel

theorem single_34_88 : ∀ i ∈ List.range 4, SingleAt 34 (88+i) := by decide +kernel

theorem single_34_92 : ∀ i ∈ List.range 4, SingleAt 34 (92+i) := by decide +kernel

theorem single_34_96 : ∀ i ∈ List.range 4, SingleAt 34 (96+i) := by decide +kernel

theorem single_34_100 : ∀ i ∈ List.range 4, SingleAt 34 (100+i) := by decide +kernel

theorem single_34_104 : ∀ i ∈ List.range 4, SingleAt 34 (104+i) := by decide +kernel

theorem single_34_108 : ∀ i ∈ List.range 4, SingleAt 34 (108+i) := by decide +kernel

theorem single_34_112 : ∀ i ∈ List.range 4, SingleAt 34 (112+i) := by decide +kernel

theorem single_34_116 : ∀ i ∈ List.range 4, SingleAt 34 (116+i) := by decide +kernel

theorem single_34_120 : ∀ i ∈ List.range 3, SingleAt 34 (120+i) := by decide +kernel

theorem single_34 (v : ℕ) (hv : v ∈ List.range 123) : SingleAt 34 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 34 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 single_34_0 (join 4 4 4 single_34_4 single_34_8)) (join 12 8 8 (join 12 4 4 single_34_12 single_34_16) (join 20 4 4 single_34_20 single_34_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 single_34_28 single_34_32) (join 36 4 4 single_34_36 single_34_40)) (join 44 8 8 (join 44 4 4 single_34_44 single_34_48) (join 52 4 4 single_34_52 single_34_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 single_34_60 single_34_64) (join 68 4 4 single_34_68 single_34_72)) (join 76 8 8 (join 76 4 4 single_34_76 single_34_80) (join 84 4 4 single_34_84 single_34_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 single_34_92 single_34_96) (join 100 4 4 single_34_100 single_34_104)) (join 108 8 7 (join 108 4 4 single_34_108 single_34_112) (join 116 4 3 single_34_116 single_34_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_34_0 : ∀ i ∈ List.range 4, PhaseAt 34 (0+i) := by decide +kernel

theorem phase_34_4 : ∀ i ∈ List.range 4, PhaseAt 34 (4+i) := by decide +kernel

theorem phase_34_8 : ∀ i ∈ List.range 4, PhaseAt 34 (8+i) := by decide +kernel

theorem phase_34_12 : ∀ i ∈ List.range 4, PhaseAt 34 (12+i) := by decide +kernel

theorem phase_34_16 : ∀ i ∈ List.range 4, PhaseAt 34 (16+i) := by decide +kernel

theorem phase_34_20 : ∀ i ∈ List.range 4, PhaseAt 34 (20+i) := by decide +kernel

theorem phase_34_24 : ∀ i ∈ List.range 4, PhaseAt 34 (24+i) := by decide +kernel

theorem phase_34_28 : ∀ i ∈ List.range 4, PhaseAt 34 (28+i) := by decide +kernel

theorem phase_34_32 : ∀ i ∈ List.range 4, PhaseAt 34 (32+i) := by decide +kernel

theorem phase_34_36 : ∀ i ∈ List.range 4, PhaseAt 34 (36+i) := by decide +kernel

theorem phase_34_40 : ∀ i ∈ List.range 4, PhaseAt 34 (40+i) := by decide +kernel

theorem phase_34_44 : ∀ i ∈ List.range 4, PhaseAt 34 (44+i) := by decide +kernel

theorem phase_34_48 : ∀ i ∈ List.range 4, PhaseAt 34 (48+i) := by decide +kernel

theorem phase_34_52 : ∀ i ∈ List.range 4, PhaseAt 34 (52+i) := by decide +kernel

theorem phase_34_56 : ∀ i ∈ List.range 4, PhaseAt 34 (56+i) := by decide +kernel

theorem phase_34_60 : ∀ i ∈ List.range 4, PhaseAt 34 (60+i) := by decide +kernel

theorem phase_34_64 : ∀ i ∈ List.range 4, PhaseAt 34 (64+i) := by decide +kernel

theorem phase_34_68 : ∀ i ∈ List.range 4, PhaseAt 34 (68+i) := by decide +kernel

theorem phase_34_72 : ∀ i ∈ List.range 4, PhaseAt 34 (72+i) := by decide +kernel

theorem phase_34_76 : ∀ i ∈ List.range 4, PhaseAt 34 (76+i) := by decide +kernel

theorem phase_34_80 : ∀ i ∈ List.range 4, PhaseAt 34 (80+i) := by decide +kernel

theorem phase_34_84 : ∀ i ∈ List.range 4, PhaseAt 34 (84+i) := by decide +kernel

theorem phase_34_88 : ∀ i ∈ List.range 4, PhaseAt 34 (88+i) := by decide +kernel

theorem phase_34_92 : ∀ i ∈ List.range 4, PhaseAt 34 (92+i) := by decide +kernel

theorem phase_34_96 : ∀ i ∈ List.range 4, PhaseAt 34 (96+i) := by decide +kernel

theorem phase_34_100 : ∀ i ∈ List.range 4, PhaseAt 34 (100+i) := by decide +kernel

theorem phase_34_104 : ∀ i ∈ List.range 4, PhaseAt 34 (104+i) := by decide +kernel

theorem phase_34_108 : ∀ i ∈ List.range 4, PhaseAt 34 (108+i) := by decide +kernel

theorem phase_34_112 : ∀ i ∈ List.range 4, PhaseAt 34 (112+i) := by decide +kernel

theorem phase_34_116 : ∀ i ∈ List.range 4, PhaseAt 34 (116+i) := by decide +kernel

theorem phase_34_120 : ∀ i ∈ List.range 3, PhaseAt 34 (120+i) := by decide +kernel

theorem phase_34 (v : ℕ) (hv : v ∈ List.range 123) : PhaseAt 34 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 34 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_34_0 (join 4 4 4 phase_34_4 phase_34_8)) (join 12 8 8 (join 12 4 4 phase_34_12 phase_34_16) (join 20 4 4 phase_34_20 phase_34_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_34_28 phase_34_32) (join 36 4 4 phase_34_36 phase_34_40)) (join 44 8 8 (join 44 4 4 phase_34_44 phase_34_48) (join 52 4 4 phase_34_52 phase_34_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 phase_34_60 phase_34_64) (join 68 4 4 phase_34_68 phase_34_72)) (join 76 8 8 (join 76 4 4 phase_34_76 phase_34_80) (join 84 4 4 phase_34_84 phase_34_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 phase_34_92 phase_34_96) (join 100 4 4 phase_34_100 phase_34_104)) (join 108 8 7 (join 108 4 4 phase_34_108 phase_34_112) (join 116 4 3 phase_34_116 phase_34_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_34_0 : ∀ i ∈ List.range 1, ThresholdAt 34 (0+i) := by decide +kernel

theorem threshold_34_1 : ∀ i ∈ List.range 1, ThresholdAt 34 (1+i) := by decide +kernel

theorem threshold_34_2 : ∀ i ∈ List.range 1, ThresholdAt 34 (2+i) := by decide +kernel

theorem threshold_34_3 : ∀ i ∈ List.range 1, ThresholdAt 34 (3+i) := by decide +kernel

theorem threshold_34_4 : ∀ i ∈ List.range 1, ThresholdAt 34 (4+i) := by decide +kernel

theorem threshold_34_5 : ∀ i ∈ List.range 1, ThresholdAt 34 (5+i) := by decide +kernel

theorem threshold_34_6 : ∀ i ∈ List.range 1, ThresholdAt 34 (6+i) := by decide +kernel

theorem threshold_34_7 : ∀ i ∈ List.range 1, ThresholdAt 34 (7+i) := by decide +kernel

theorem threshold_34_8 : ∀ i ∈ List.range 1, ThresholdAt 34 (8+i) := by decide +kernel

theorem threshold_34_9 : ∀ i ∈ List.range 1, ThresholdAt 34 (9+i) := by decide +kernel

theorem threshold_34_10 : ∀ i ∈ List.range 1, ThresholdAt 34 (10+i) := by decide +kernel

theorem threshold_34_11 : ∀ i ∈ List.range 1, ThresholdAt 34 (11+i) := by decide +kernel

theorem threshold_34_12 : ∀ i ∈ List.range 1, ThresholdAt 34 (12+i) := by decide +kernel

theorem threshold_34_13 : ∀ i ∈ List.range 1, ThresholdAt 34 (13+i) := by decide +kernel

theorem threshold_34_14 : ∀ i ∈ List.range 1, ThresholdAt 34 (14+i) := by decide +kernel

theorem threshold_34_15 : ∀ i ∈ List.range 1, ThresholdAt 34 (15+i) := by decide +kernel

theorem threshold_34_16 : ∀ i ∈ List.range 1, ThresholdAt 34 (16+i) := by decide +kernel

theorem threshold_34_17 : ∀ i ∈ List.range 1, ThresholdAt 34 (17+i) := by decide +kernel

theorem threshold_34_18 : ∀ i ∈ List.range 1, ThresholdAt 34 (18+i) := by decide +kernel

theorem threshold_34_19 : ∀ i ∈ List.range 1, ThresholdAt 34 (19+i) := by decide +kernel

theorem threshold_34_20 : ∀ i ∈ List.range 1, ThresholdAt 34 (20+i) := by decide +kernel

theorem threshold_34_21 : ∀ i ∈ List.range 1, ThresholdAt 34 (21+i) := by decide +kernel

theorem threshold_34_22 : ∀ i ∈ List.range 1, ThresholdAt 34 (22+i) := by decide +kernel

theorem threshold_34_23 : ∀ i ∈ List.range 1, ThresholdAt 34 (23+i) := by decide +kernel

theorem threshold_34_24 : ∀ i ∈ List.range 1, ThresholdAt 34 (24+i) := by decide +kernel

theorem threshold_34_25 : ∀ i ∈ List.range 1, ThresholdAt 34 (25+i) := by decide +kernel

theorem threshold_34_26 : ∀ i ∈ List.range 1, ThresholdAt 34 (26+i) := by decide +kernel

theorem threshold_34_27 : ∀ i ∈ List.range 1, ThresholdAt 34 (27+i) := by decide +kernel

theorem threshold_34_28 : ∀ i ∈ List.range 1, ThresholdAt 34 (28+i) := by decide +kernel

theorem threshold_34_29 : ∀ i ∈ List.range 1, ThresholdAt 34 (29+i) := by decide +kernel

theorem threshold_34_30 : ∀ i ∈ List.range 1, ThresholdAt 34 (30+i) := by decide +kernel

theorem threshold_34_31 : ∀ i ∈ List.range 1, ThresholdAt 34 (31+i) := by decide +kernel

theorem threshold_34_32 : ∀ i ∈ List.range 1, ThresholdAt 34 (32+i) := by decide +kernel

theorem threshold_34_33 : ∀ i ∈ List.range 1, ThresholdAt 34 (33+i) := by decide +kernel

theorem threshold_34_34 : ∀ i ∈ List.range 1, ThresholdAt 34 (34+i) := by decide +kernel

theorem threshold_34_35 : ∀ i ∈ List.range 1, ThresholdAt 34 (35+i) := by decide +kernel

theorem threshold_34_36 : ∀ i ∈ List.range 1, ThresholdAt 34 (36+i) := by decide +kernel

theorem threshold_34_37 : ∀ i ∈ List.range 1, ThresholdAt 34 (37+i) := by decide +kernel

theorem threshold_34_38 : ∀ i ∈ List.range 1, ThresholdAt 34 (38+i) := by decide +kernel

theorem threshold_34_39 : ∀ i ∈ List.range 1, ThresholdAt 34 (39+i) := by decide +kernel

theorem threshold_34_40 : ∀ i ∈ List.range 1, ThresholdAt 34 (40+i) := by decide +kernel

theorem threshold_34_41 : ∀ i ∈ List.range 1, ThresholdAt 34 (41+i) := by decide +kernel

theorem threshold_34_42 : ∀ i ∈ List.range 1, ThresholdAt 34 (42+i) := by decide +kernel

theorem threshold_34_43 : ∀ i ∈ List.range 1, ThresholdAt 34 (43+i) := by decide +kernel

theorem threshold_34_44 : ∀ i ∈ List.range 1, ThresholdAt 34 (44+i) := by decide +kernel

theorem threshold_34_45 : ∀ i ∈ List.range 1, ThresholdAt 34 (45+i) := by decide +kernel

theorem threshold_34_46 : ∀ i ∈ List.range 1, ThresholdAt 34 (46+i) := by decide +kernel

theorem threshold_34_47 : ∀ i ∈ List.range 1, ThresholdAt 34 (47+i) := by decide +kernel

theorem threshold_34_48 : ∀ i ∈ List.range 1, ThresholdAt 34 (48+i) := by decide +kernel

theorem threshold_34_49 : ∀ i ∈ List.range 1, ThresholdAt 34 (49+i) := by decide +kernel

theorem threshold_34_50 : ∀ i ∈ List.range 1, ThresholdAt 34 (50+i) := by decide +kernel

theorem threshold_34_51 : ∀ i ∈ List.range 1, ThresholdAt 34 (51+i) := by decide +kernel

theorem threshold_34_52 : ∀ i ∈ List.range 1, ThresholdAt 34 (52+i) := by decide +kernel

theorem threshold_34_53 : ∀ i ∈ List.range 1, ThresholdAt 34 (53+i) := by decide +kernel

theorem threshold_34_54 : ∀ i ∈ List.range 1, ThresholdAt 34 (54+i) := by decide +kernel

theorem threshold_34_55 : ∀ i ∈ List.range 1, ThresholdAt 34 (55+i) := by decide +kernel

theorem threshold_34_56 : ∀ i ∈ List.range 1, ThresholdAt 34 (56+i) := by decide +kernel

theorem threshold_34_57 : ∀ i ∈ List.range 1, ThresholdAt 34 (57+i) := by decide +kernel

theorem threshold_34_58 : ∀ i ∈ List.range 1, ThresholdAt 34 (58+i) := by decide +kernel

theorem threshold_34_59 : ∀ i ∈ List.range 1, ThresholdAt 34 (59+i) := by decide +kernel

theorem threshold_34_60 : ∀ i ∈ List.range 1, ThresholdAt 34 (60+i) := by decide +kernel

theorem threshold_34_61 : ∀ i ∈ List.range 1, ThresholdAt 34 (61+i) := by decide +kernel

theorem threshold_34_62 : ∀ i ∈ List.range 1, ThresholdAt 34 (62+i) := by decide +kernel

theorem threshold_34_63 : ∀ i ∈ List.range 1, ThresholdAt 34 (63+i) := by decide +kernel

theorem threshold_34_64 : ∀ i ∈ List.range 1, ThresholdAt 34 (64+i) := by decide +kernel

theorem threshold_34_65 : ∀ i ∈ List.range 1, ThresholdAt 34 (65+i) := by decide +kernel

theorem threshold_34_66 : ∀ i ∈ List.range 1, ThresholdAt 34 (66+i) := by decide +kernel

theorem threshold_34_67 : ∀ i ∈ List.range 1, ThresholdAt 34 (67+i) := by decide +kernel

theorem threshold_34_68 : ∀ i ∈ List.range 1, ThresholdAt 34 (68+i) := by decide +kernel

theorem threshold_34_69 : ∀ i ∈ List.range 1, ThresholdAt 34 (69+i) := by decide +kernel

theorem threshold_34_70 : ∀ i ∈ List.range 1, ThresholdAt 34 (70+i) := by decide +kernel

theorem threshold_34_71 : ∀ i ∈ List.range 1, ThresholdAt 34 (71+i) := by decide +kernel

theorem threshold_34_72 : ∀ i ∈ List.range 1, ThresholdAt 34 (72+i) := by decide +kernel

theorem threshold_34_73 : ∀ i ∈ List.range 1, ThresholdAt 34 (73+i) := by decide +kernel

theorem threshold_34_74 : ∀ i ∈ List.range 1, ThresholdAt 34 (74+i) := by decide +kernel

theorem threshold_34_75 : ∀ i ∈ List.range 1, ThresholdAt 34 (75+i) := by decide +kernel

theorem threshold_34_76 : ∀ i ∈ List.range 1, ThresholdAt 34 (76+i) := by decide +kernel

theorem threshold_34_77 : ∀ i ∈ List.range 1, ThresholdAt 34 (77+i) := by decide +kernel

theorem threshold_34_78 : ∀ i ∈ List.range 1, ThresholdAt 34 (78+i) := by decide +kernel

theorem threshold_34_79 : ∀ i ∈ List.range 1, ThresholdAt 34 (79+i) := by decide +kernel

theorem threshold_34_80 : ∀ i ∈ List.range 1, ThresholdAt 34 (80+i) := by decide +kernel

theorem threshold_34_81 : ∀ i ∈ List.range 1, ThresholdAt 34 (81+i) := by decide +kernel

theorem threshold_34_82 : ∀ i ∈ List.range 1, ThresholdAt 34 (82+i) := by decide +kernel

theorem threshold_34_83 : ∀ i ∈ List.range 1, ThresholdAt 34 (83+i) := by decide +kernel

theorem threshold_34_84 : ∀ i ∈ List.range 1, ThresholdAt 34 (84+i) := by decide +kernel

theorem threshold_34_85 : ∀ i ∈ List.range 1, ThresholdAt 34 (85+i) := by decide +kernel

theorem threshold_34_86 : ∀ i ∈ List.range 1, ThresholdAt 34 (86+i) := by decide +kernel

theorem threshold_34_87 : ∀ i ∈ List.range 1, ThresholdAt 34 (87+i) := by decide +kernel

theorem threshold_34_88 : ∀ i ∈ List.range 1, ThresholdAt 34 (88+i) := by decide +kernel

theorem threshold_34_89 : ∀ i ∈ List.range 1, ThresholdAt 34 (89+i) := by decide +kernel

theorem threshold_34_90 : ∀ i ∈ List.range 1, ThresholdAt 34 (90+i) := by decide +kernel

theorem threshold_34_91 : ∀ i ∈ List.range 1, ThresholdAt 34 (91+i) := by decide +kernel

theorem threshold_34_92 : ∀ i ∈ List.range 1, ThresholdAt 34 (92+i) := by decide +kernel

theorem threshold_34_93 : ∀ i ∈ List.range 1, ThresholdAt 34 (93+i) := by decide +kernel

theorem threshold_34_94 : ∀ i ∈ List.range 1, ThresholdAt 34 (94+i) := by decide +kernel

theorem threshold_34_95 : ∀ i ∈ List.range 1, ThresholdAt 34 (95+i) := by decide +kernel

theorem threshold_34_96 : ∀ i ∈ List.range 1, ThresholdAt 34 (96+i) := by decide +kernel

theorem threshold_34_97 : ∀ i ∈ List.range 1, ThresholdAt 34 (97+i) := by decide +kernel

theorem threshold_34_98 : ∀ i ∈ List.range 1, ThresholdAt 34 (98+i) := by decide +kernel

theorem threshold_34_99 : ∀ i ∈ List.range 1, ThresholdAt 34 (99+i) := by decide +kernel

theorem threshold_34_100 : ∀ i ∈ List.range 1, ThresholdAt 34 (100+i) := by decide +kernel

theorem threshold_34_101 : ∀ i ∈ List.range 1, ThresholdAt 34 (101+i) := by decide +kernel

theorem threshold_34_102 : ∀ i ∈ List.range 1, ThresholdAt 34 (102+i) := by decide +kernel

theorem threshold_34_103 : ∀ i ∈ List.range 1, ThresholdAt 34 (103+i) := by decide +kernel

theorem threshold_34_104 : ∀ i ∈ List.range 1, ThresholdAt 34 (104+i) := by decide +kernel

theorem threshold_34_105 : ∀ i ∈ List.range 1, ThresholdAt 34 (105+i) := by decide +kernel

theorem threshold_34_106 : ∀ i ∈ List.range 1, ThresholdAt 34 (106+i) := by decide +kernel

theorem threshold_34_107 : ∀ i ∈ List.range 1, ThresholdAt 34 (107+i) := by decide +kernel

theorem threshold_34_108 : ∀ i ∈ List.range 1, ThresholdAt 34 (108+i) := by decide +kernel

theorem threshold_34_109 : ∀ i ∈ List.range 1, ThresholdAt 34 (109+i) := by decide +kernel

theorem threshold_34_110 : ∀ i ∈ List.range 1, ThresholdAt 34 (110+i) := by decide +kernel

theorem threshold_34_111 : ∀ i ∈ List.range 1, ThresholdAt 34 (111+i) := by decide +kernel

theorem threshold_34_112 : ∀ i ∈ List.range 1, ThresholdAt 34 (112+i) := by decide +kernel

theorem threshold_34_113 : ∀ i ∈ List.range 1, ThresholdAt 34 (113+i) := by decide +kernel

theorem threshold_34_114 : ∀ i ∈ List.range 1, ThresholdAt 34 (114+i) := by decide +kernel

theorem threshold_34_115 : ∀ i ∈ List.range 1, ThresholdAt 34 (115+i) := by decide +kernel

theorem threshold_34_116 : ∀ i ∈ List.range 1, ThresholdAt 34 (116+i) := by decide +kernel

theorem threshold_34_117 : ∀ i ∈ List.range 1, ThresholdAt 34 (117+i) := by decide +kernel

theorem threshold_34_118 : ∀ i ∈ List.range 1, ThresholdAt 34 (118+i) := by decide +kernel

theorem threshold_34_119 : ∀ i ∈ List.range 1, ThresholdAt 34 (119+i) := by decide +kernel

theorem threshold_34_120 : ∀ i ∈ List.range 1, ThresholdAt 34 (120+i) := by decide +kernel

theorem threshold_34_121 : ∀ i ∈ List.range 1, ThresholdAt 34 (121+i) := by decide +kernel

theorem threshold_34_122 : ∀ i ∈ List.range 1, ThresholdAt 34 (122+i) := by decide +kernel

theorem threshold_34 (v : ℕ) (hv : v ∈ List.range 123) : ThresholdAt 34 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 34 v)
  have h := (join 0 61 62 (join 0 30 31 (join 0 15 15 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_34_0 (join 1 1 1 threshold_34_1 threshold_34_2)) (join 3 2 2 (join 3 1 1 threshold_34_3 threshold_34_4) (join 5 1 1 threshold_34_5 threshold_34_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_34_7 threshold_34_8) (join 9 1 1 threshold_34_9 threshold_34_10)) (join 11 2 2 (join 11 1 1 threshold_34_11 threshold_34_12) (join 13 1 1 threshold_34_13 threshold_34_14)))) (join 15 7 8 (join 15 3 4 (join 15 1 2 threshold_34_15 (join 16 1 1 threshold_34_16 threshold_34_17)) (join 18 2 2 (join 18 1 1 threshold_34_18 threshold_34_19) (join 20 1 1 threshold_34_20 threshold_34_21))) (join 22 4 4 (join 22 2 2 (join 22 1 1 threshold_34_22 threshold_34_23) (join 24 1 1 threshold_34_24 threshold_34_25)) (join 26 2 2 (join 26 1 1 threshold_34_26 threshold_34_27) (join 28 1 1 threshold_34_28 threshold_34_29))))) (join 30 15 16 (join 30 7 8 (join 30 3 4 (join 30 1 2 threshold_34_30 (join 31 1 1 threshold_34_31 threshold_34_32)) (join 33 2 2 (join 33 1 1 threshold_34_33 threshold_34_34) (join 35 1 1 threshold_34_35 threshold_34_36))) (join 37 4 4 (join 37 2 2 (join 37 1 1 threshold_34_37 threshold_34_38) (join 39 1 1 threshold_34_39 threshold_34_40)) (join 41 2 2 (join 41 1 1 threshold_34_41 threshold_34_42) (join 43 1 1 threshold_34_43 threshold_34_44)))) (join 45 8 8 (join 45 4 4 (join 45 2 2 (join 45 1 1 threshold_34_45 threshold_34_46) (join 47 1 1 threshold_34_47 threshold_34_48)) (join 49 2 2 (join 49 1 1 threshold_34_49 threshold_34_50) (join 51 1 1 threshold_34_51 threshold_34_52))) (join 53 4 4 (join 53 2 2 (join 53 1 1 threshold_34_53 threshold_34_54) (join 55 1 1 threshold_34_55 threshold_34_56)) (join 57 2 2 (join 57 1 1 threshold_34_57 threshold_34_58) (join 59 1 1 threshold_34_59 threshold_34_60)))))) (join 61 31 31 (join 61 15 16 (join 61 7 8 (join 61 3 4 (join 61 1 2 threshold_34_61 (join 62 1 1 threshold_34_62 threshold_34_63)) (join 64 2 2 (join 64 1 1 threshold_34_64 threshold_34_65) (join 66 1 1 threshold_34_66 threshold_34_67))) (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_34_68 threshold_34_69) (join 70 1 1 threshold_34_70 threshold_34_71)) (join 72 2 2 (join 72 1 1 threshold_34_72 threshold_34_73) (join 74 1 1 threshold_34_74 threshold_34_75)))) (join 76 8 8 (join 76 4 4 (join 76 2 2 (join 76 1 1 threshold_34_76 threshold_34_77) (join 78 1 1 threshold_34_78 threshold_34_79)) (join 80 2 2 (join 80 1 1 threshold_34_80 threshold_34_81) (join 82 1 1 threshold_34_82 threshold_34_83))) (join 84 4 4 (join 84 2 2 (join 84 1 1 threshold_34_84 threshold_34_85) (join 86 1 1 threshold_34_86 threshold_34_87)) (join 88 2 2 (join 88 1 1 threshold_34_88 threshold_34_89) (join 90 1 1 threshold_34_90 threshold_34_91))))) (join 92 15 16 (join 92 7 8 (join 92 3 4 (join 92 1 2 threshold_34_92 (join 93 1 1 threshold_34_93 threshold_34_94)) (join 95 2 2 (join 95 1 1 threshold_34_95 threshold_34_96) (join 97 1 1 threshold_34_97 threshold_34_98))) (join 99 4 4 (join 99 2 2 (join 99 1 1 threshold_34_99 threshold_34_100) (join 101 1 1 threshold_34_101 threshold_34_102)) (join 103 2 2 (join 103 1 1 threshold_34_103 threshold_34_104) (join 105 1 1 threshold_34_105 threshold_34_106)))) (join 107 8 8 (join 107 4 4 (join 107 2 2 (join 107 1 1 threshold_34_107 threshold_34_108) (join 109 1 1 threshold_34_109 threshold_34_110)) (join 111 2 2 (join 111 1 1 threshold_34_111 threshold_34_112) (join 113 1 1 threshold_34_113 threshold_34_114))) (join 115 4 4 (join 115 2 2 (join 115 1 1 threshold_34_115 threshold_34_116) (join 117 1 1 threshold_34_117 threshold_34_118)) (join 119 2 2 (join 119 1 1 threshold_34_119 threshold_34_120) (join 121 1 1 threshold_34_121 threshold_34_122)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_34_0 : ∀ i ∈ List.range 4, LedgerAt 34 (0+i) := by decide +kernel

theorem ledger_34_4 : ∀ i ∈ List.range 4, LedgerAt 34 (4+i) := by decide +kernel

theorem ledger_34_8 : ∀ i ∈ List.range 4, LedgerAt 34 (8+i) := by decide +kernel

theorem ledger_34_12 : ∀ i ∈ List.range 4, LedgerAt 34 (12+i) := by decide +kernel

theorem ledger_34_16 : ∀ i ∈ List.range 4, LedgerAt 34 (16+i) := by decide +kernel

theorem ledger_34_20 : ∀ i ∈ List.range 4, LedgerAt 34 (20+i) := by decide +kernel

theorem ledger_34_24 : ∀ i ∈ List.range 4, LedgerAt 34 (24+i) := by decide +kernel

theorem ledger_34_28 : ∀ i ∈ List.range 4, LedgerAt 34 (28+i) := by decide +kernel

theorem ledger_34_32 : ∀ i ∈ List.range 4, LedgerAt 34 (32+i) := by decide +kernel

theorem ledger_34_36 : ∀ i ∈ List.range 4, LedgerAt 34 (36+i) := by decide +kernel

theorem ledger_34_40 : ∀ i ∈ List.range 4, LedgerAt 34 (40+i) := by decide +kernel

theorem ledger_34_44 : ∀ i ∈ List.range 4, LedgerAt 34 (44+i) := by decide +kernel

theorem ledger_34_48 : ∀ i ∈ List.range 4, LedgerAt 34 (48+i) := by decide +kernel

theorem ledger_34_52 : ∀ i ∈ List.range 4, LedgerAt 34 (52+i) := by decide +kernel

theorem ledger_34_56 : ∀ i ∈ List.range 4, LedgerAt 34 (56+i) := by decide +kernel

theorem ledger_34_60 : ∀ i ∈ List.range 4, LedgerAt 34 (60+i) := by decide +kernel

theorem ledger_34_64 : ∀ i ∈ List.range 4, LedgerAt 34 (64+i) := by decide +kernel

theorem ledger_34_68 : ∀ i ∈ List.range 4, LedgerAt 34 (68+i) := by decide +kernel

theorem ledger_34_72 : ∀ i ∈ List.range 4, LedgerAt 34 (72+i) := by decide +kernel

theorem ledger_34_76 : ∀ i ∈ List.range 4, LedgerAt 34 (76+i) := by decide +kernel

theorem ledger_34_80 : ∀ i ∈ List.range 4, LedgerAt 34 (80+i) := by decide +kernel

theorem ledger_34_84 : ∀ i ∈ List.range 4, LedgerAt 34 (84+i) := by decide +kernel

theorem ledger_34_88 : ∀ i ∈ List.range 4, LedgerAt 34 (88+i) := by decide +kernel

theorem ledger_34_92 : ∀ i ∈ List.range 4, LedgerAt 34 (92+i) := by decide +kernel

theorem ledger_34_96 : ∀ i ∈ List.range 4, LedgerAt 34 (96+i) := by decide +kernel

theorem ledger_34_100 : ∀ i ∈ List.range 4, LedgerAt 34 (100+i) := by decide +kernel

theorem ledger_34_104 : ∀ i ∈ List.range 4, LedgerAt 34 (104+i) := by decide +kernel

theorem ledger_34_108 : ∀ i ∈ List.range 4, LedgerAt 34 (108+i) := by decide +kernel

theorem ledger_34_112 : ∀ i ∈ List.range 4, LedgerAt 34 (112+i) := by decide +kernel

theorem ledger_34_116 : ∀ i ∈ List.range 4, LedgerAt 34 (116+i) := by decide +kernel

theorem ledger_34_120 : ∀ i ∈ List.range 3, LedgerAt 34 (120+i) := by decide +kernel

theorem ledger_34 (v : ℕ) (hv : v ∈ List.range 123) : LedgerAt 34 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 34 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_34_0 (join 4 4 4 ledger_34_4 ledger_34_8)) (join 12 8 8 (join 12 4 4 ledger_34_12 ledger_34_16) (join 20 4 4 ledger_34_20 ledger_34_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_34_28 ledger_34_32) (join 36 4 4 ledger_34_36 ledger_34_40)) (join 44 8 8 (join 44 4 4 ledger_34_44 ledger_34_48) (join 52 4 4 ledger_34_52 ledger_34_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 ledger_34_60 ledger_34_64) (join 68 4 4 ledger_34_68 ledger_34_72)) (join 76 8 8 (join 76 4 4 ledger_34_76 ledger_34_80) (join 84 4 4 ledger_34_84 ledger_34_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 ledger_34_92 ledger_34_96) (join 100 4 4 ledger_34_100 ledger_34_104)) (join 108 8 7 (join 108 4 4 ledger_34_108 ledger_34_112) (join 116 4 3 ledger_34_116 ledger_34_120)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
