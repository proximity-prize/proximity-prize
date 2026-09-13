import ProximityPrize.SubmissionLower.AffineCheckedR286808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_29_0 : ∀ i ∈ List.range 4, SingleAt 29 (0+i) := by decide +kernel

theorem single_29_4 : ∀ i ∈ List.range 4, SingleAt 29 (4+i) := by decide +kernel

theorem single_29_8 : ∀ i ∈ List.range 4, SingleAt 29 (8+i) := by decide +kernel

theorem single_29_12 : ∀ i ∈ List.range 4, SingleAt 29 (12+i) := by decide +kernel

theorem single_29_16 : ∀ i ∈ List.range 4, SingleAt 29 (16+i) := by decide +kernel

theorem single_29_20 : ∀ i ∈ List.range 4, SingleAt 29 (20+i) := by decide +kernel

theorem single_29_24 : ∀ i ∈ List.range 4, SingleAt 29 (24+i) := by decide +kernel

theorem single_29_28 : ∀ i ∈ List.range 4, SingleAt 29 (28+i) := by decide +kernel

theorem single_29_32 : ∀ i ∈ List.range 4, SingleAt 29 (32+i) := by decide +kernel

theorem single_29_36 : ∀ i ∈ List.range 4, SingleAt 29 (36+i) := by decide +kernel

theorem single_29_40 : ∀ i ∈ List.range 4, SingleAt 29 (40+i) := by decide +kernel

theorem single_29_44 : ∀ i ∈ List.range 4, SingleAt 29 (44+i) := by decide +kernel

theorem single_29_48 : ∀ i ∈ List.range 4, SingleAt 29 (48+i) := by decide +kernel

theorem single_29_52 : ∀ i ∈ List.range 4, SingleAt 29 (52+i) := by decide +kernel

theorem single_29_56 : ∀ i ∈ List.range 4, SingleAt 29 (56+i) := by decide +kernel

theorem single_29_60 : ∀ i ∈ List.range 4, SingleAt 29 (60+i) := by decide +kernel

theorem single_29_64 : ∀ i ∈ List.range 4, SingleAt 29 (64+i) := by decide +kernel

theorem single_29_68 : ∀ i ∈ List.range 4, SingleAt 29 (68+i) := by decide +kernel

theorem single_29_72 : ∀ i ∈ List.range 4, SingleAt 29 (72+i) := by decide +kernel

theorem single_29_76 : ∀ i ∈ List.range 4, SingleAt 29 (76+i) := by decide +kernel

theorem single_29_80 : ∀ i ∈ List.range 4, SingleAt 29 (80+i) := by decide +kernel

theorem single_29_84 : ∀ i ∈ List.range 4, SingleAt 29 (84+i) := by decide +kernel

theorem single_29_88 : ∀ i ∈ List.range 4, SingleAt 29 (88+i) := by decide +kernel

theorem single_29_92 : ∀ i ∈ List.range 4, SingleAt 29 (92+i) := by decide +kernel

theorem single_29_96 : ∀ i ∈ List.range 4, SingleAt 29 (96+i) := by decide +kernel

theorem single_29_100 : ∀ i ∈ List.range 4, SingleAt 29 (100+i) := by decide +kernel

theorem single_29_104 : ∀ i ∈ List.range 4, SingleAt 29 (104+i) := by decide +kernel

theorem single_29_108 : ∀ i ∈ List.range 4, SingleAt 29 (108+i) := by decide +kernel

theorem single_29_112 : ∀ i ∈ List.range 4, SingleAt 29 (112+i) := by decide +kernel

theorem single_29_116 : ∀ i ∈ List.range 4, SingleAt 29 (116+i) := by decide +kernel

theorem single_29_120 : ∀ i ∈ List.range 1, SingleAt 29 (120+i) := by decide +kernel

theorem single_29 (v : ℕ) (hv : v ∈ List.range 121) : SingleAt 29 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 29 v)
  have h := (join 0 60 61 (join 0 28 32 (join 0 12 16 (join 0 4 8 single_29_0 (join 4 4 4 single_29_4 single_29_8)) (join 12 8 8 (join 12 4 4 single_29_12 single_29_16) (join 20 4 4 single_29_20 single_29_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 single_29_28 single_29_32) (join 36 4 4 single_29_36 single_29_40)) (join 44 8 8 (join 44 4 4 single_29_44 single_29_48) (join 52 4 4 single_29_52 single_29_56)))) (join 60 32 29 (join 60 16 16 (join 60 8 8 (join 60 4 4 single_29_60 single_29_64) (join 68 4 4 single_29_68 single_29_72)) (join 76 8 8 (join 76 4 4 single_29_76 single_29_80) (join 84 4 4 single_29_84 single_29_88))) (join 92 16 13 (join 92 8 8 (join 92 4 4 single_29_92 single_29_96) (join 100 4 4 single_29_100 single_29_104)) (join 108 8 5 (join 108 4 4 single_29_108 single_29_112) (join 116 4 1 single_29_116 single_29_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_29_0 : ∀ i ∈ List.range 4, PhaseAt 29 (0+i) := by decide +kernel

theorem phase_29_4 : ∀ i ∈ List.range 4, PhaseAt 29 (4+i) := by decide +kernel

theorem phase_29_8 : ∀ i ∈ List.range 4, PhaseAt 29 (8+i) := by decide +kernel

theorem phase_29_12 : ∀ i ∈ List.range 4, PhaseAt 29 (12+i) := by decide +kernel

theorem phase_29_16 : ∀ i ∈ List.range 4, PhaseAt 29 (16+i) := by decide +kernel

theorem phase_29_20 : ∀ i ∈ List.range 4, PhaseAt 29 (20+i) := by decide +kernel

theorem phase_29_24 : ∀ i ∈ List.range 4, PhaseAt 29 (24+i) := by decide +kernel

theorem phase_29_28 : ∀ i ∈ List.range 4, PhaseAt 29 (28+i) := by decide +kernel

theorem phase_29_32 : ∀ i ∈ List.range 4, PhaseAt 29 (32+i) := by decide +kernel

theorem phase_29_36 : ∀ i ∈ List.range 4, PhaseAt 29 (36+i) := by decide +kernel

theorem phase_29_40 : ∀ i ∈ List.range 4, PhaseAt 29 (40+i) := by decide +kernel

theorem phase_29_44 : ∀ i ∈ List.range 4, PhaseAt 29 (44+i) := by decide +kernel

theorem phase_29_48 : ∀ i ∈ List.range 4, PhaseAt 29 (48+i) := by decide +kernel

theorem phase_29_52 : ∀ i ∈ List.range 4, PhaseAt 29 (52+i) := by decide +kernel

theorem phase_29_56 : ∀ i ∈ List.range 4, PhaseAt 29 (56+i) := by decide +kernel

theorem phase_29_60 : ∀ i ∈ List.range 4, PhaseAt 29 (60+i) := by decide +kernel

theorem phase_29_64 : ∀ i ∈ List.range 4, PhaseAt 29 (64+i) := by decide +kernel

theorem phase_29_68 : ∀ i ∈ List.range 4, PhaseAt 29 (68+i) := by decide +kernel

theorem phase_29_72 : ∀ i ∈ List.range 4, PhaseAt 29 (72+i) := by decide +kernel

theorem phase_29_76 : ∀ i ∈ List.range 4, PhaseAt 29 (76+i) := by decide +kernel

theorem phase_29_80 : ∀ i ∈ List.range 4, PhaseAt 29 (80+i) := by decide +kernel

theorem phase_29_84 : ∀ i ∈ List.range 4, PhaseAt 29 (84+i) := by decide +kernel

theorem phase_29_88 : ∀ i ∈ List.range 4, PhaseAt 29 (88+i) := by decide +kernel

theorem phase_29_92 : ∀ i ∈ List.range 4, PhaseAt 29 (92+i) := by decide +kernel

theorem phase_29_96 : ∀ i ∈ List.range 4, PhaseAt 29 (96+i) := by decide +kernel

theorem phase_29_100 : ∀ i ∈ List.range 4, PhaseAt 29 (100+i) := by decide +kernel

theorem phase_29_104 : ∀ i ∈ List.range 4, PhaseAt 29 (104+i) := by decide +kernel

theorem phase_29_108 : ∀ i ∈ List.range 4, PhaseAt 29 (108+i) := by decide +kernel

theorem phase_29_112 : ∀ i ∈ List.range 4, PhaseAt 29 (112+i) := by decide +kernel

theorem phase_29_116 : ∀ i ∈ List.range 4, PhaseAt 29 (116+i) := by decide +kernel

theorem phase_29_120 : ∀ i ∈ List.range 1, PhaseAt 29 (120+i) := by decide +kernel

theorem phase_29 (v : ℕ) (hv : v ∈ List.range 121) : PhaseAt 29 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 29 v)
  have h := (join 0 60 61 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_29_0 (join 4 4 4 phase_29_4 phase_29_8)) (join 12 8 8 (join 12 4 4 phase_29_12 phase_29_16) (join 20 4 4 phase_29_20 phase_29_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_29_28 phase_29_32) (join 36 4 4 phase_29_36 phase_29_40)) (join 44 8 8 (join 44 4 4 phase_29_44 phase_29_48) (join 52 4 4 phase_29_52 phase_29_56)))) (join 60 32 29 (join 60 16 16 (join 60 8 8 (join 60 4 4 phase_29_60 phase_29_64) (join 68 4 4 phase_29_68 phase_29_72)) (join 76 8 8 (join 76 4 4 phase_29_76 phase_29_80) (join 84 4 4 phase_29_84 phase_29_88))) (join 92 16 13 (join 92 8 8 (join 92 4 4 phase_29_92 phase_29_96) (join 100 4 4 phase_29_100 phase_29_104)) (join 108 8 5 (join 108 4 4 phase_29_108 phase_29_112) (join 116 4 1 phase_29_116 phase_29_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_29_0 : ∀ i ∈ List.range 1, ThresholdAt 29 (0+i) := by decide +kernel

theorem threshold_29_1 : ∀ i ∈ List.range 1, ThresholdAt 29 (1+i) := by decide +kernel

theorem threshold_29_2 : ∀ i ∈ List.range 1, ThresholdAt 29 (2+i) := by decide +kernel

theorem threshold_29_3 : ∀ i ∈ List.range 1, ThresholdAt 29 (3+i) := by decide +kernel

theorem threshold_29_4 : ∀ i ∈ List.range 1, ThresholdAt 29 (4+i) := by decide +kernel

theorem threshold_29_5 : ∀ i ∈ List.range 1, ThresholdAt 29 (5+i) := by decide +kernel

theorem threshold_29_6 : ∀ i ∈ List.range 1, ThresholdAt 29 (6+i) := by decide +kernel

theorem threshold_29_7 : ∀ i ∈ List.range 1, ThresholdAt 29 (7+i) := by decide +kernel

theorem threshold_29_8 : ∀ i ∈ List.range 1, ThresholdAt 29 (8+i) := by decide +kernel

theorem threshold_29_9 : ∀ i ∈ List.range 1, ThresholdAt 29 (9+i) := by decide +kernel

theorem threshold_29_10 : ∀ i ∈ List.range 1, ThresholdAt 29 (10+i) := by decide +kernel

theorem threshold_29_11 : ∀ i ∈ List.range 1, ThresholdAt 29 (11+i) := by decide +kernel

theorem threshold_29_12 : ∀ i ∈ List.range 1, ThresholdAt 29 (12+i) := by decide +kernel

theorem threshold_29_13 : ∀ i ∈ List.range 1, ThresholdAt 29 (13+i) := by decide +kernel

theorem threshold_29_14 : ∀ i ∈ List.range 1, ThresholdAt 29 (14+i) := by decide +kernel

theorem threshold_29_15 : ∀ i ∈ List.range 1, ThresholdAt 29 (15+i) := by decide +kernel

theorem threshold_29_16 : ∀ i ∈ List.range 1, ThresholdAt 29 (16+i) := by decide +kernel

theorem threshold_29_17 : ∀ i ∈ List.range 1, ThresholdAt 29 (17+i) := by decide +kernel

theorem threshold_29_18 : ∀ i ∈ List.range 1, ThresholdAt 29 (18+i) := by decide +kernel

theorem threshold_29_19 : ∀ i ∈ List.range 1, ThresholdAt 29 (19+i) := by decide +kernel

theorem threshold_29_20 : ∀ i ∈ List.range 1, ThresholdAt 29 (20+i) := by decide +kernel

theorem threshold_29_21 : ∀ i ∈ List.range 1, ThresholdAt 29 (21+i) := by decide +kernel

theorem threshold_29_22 : ∀ i ∈ List.range 1, ThresholdAt 29 (22+i) := by decide +kernel

theorem threshold_29_23 : ∀ i ∈ List.range 1, ThresholdAt 29 (23+i) := by decide +kernel

theorem threshold_29_24 : ∀ i ∈ List.range 1, ThresholdAt 29 (24+i) := by decide +kernel

theorem threshold_29_25 : ∀ i ∈ List.range 1, ThresholdAt 29 (25+i) := by decide +kernel

theorem threshold_29_26 : ∀ i ∈ List.range 1, ThresholdAt 29 (26+i) := by decide +kernel

theorem threshold_29_27 : ∀ i ∈ List.range 1, ThresholdAt 29 (27+i) := by decide +kernel

theorem threshold_29_28 : ∀ i ∈ List.range 1, ThresholdAt 29 (28+i) := by decide +kernel

theorem threshold_29_29 : ∀ i ∈ List.range 1, ThresholdAt 29 (29+i) := by decide +kernel

theorem threshold_29_30 : ∀ i ∈ List.range 1, ThresholdAt 29 (30+i) := by decide +kernel

theorem threshold_29_31 : ∀ i ∈ List.range 1, ThresholdAt 29 (31+i) := by decide +kernel

theorem threshold_29_32 : ∀ i ∈ List.range 1, ThresholdAt 29 (32+i) := by decide +kernel

theorem threshold_29_33 : ∀ i ∈ List.range 1, ThresholdAt 29 (33+i) := by decide +kernel

theorem threshold_29_34 : ∀ i ∈ List.range 1, ThresholdAt 29 (34+i) := by decide +kernel

theorem threshold_29_35 : ∀ i ∈ List.range 1, ThresholdAt 29 (35+i) := by decide +kernel

theorem threshold_29_36 : ∀ i ∈ List.range 1, ThresholdAt 29 (36+i) := by decide +kernel

theorem threshold_29_37 : ∀ i ∈ List.range 1, ThresholdAt 29 (37+i) := by decide +kernel

theorem threshold_29_38 : ∀ i ∈ List.range 1, ThresholdAt 29 (38+i) := by decide +kernel

theorem threshold_29_39 : ∀ i ∈ List.range 1, ThresholdAt 29 (39+i) := by decide +kernel

theorem threshold_29_40 : ∀ i ∈ List.range 1, ThresholdAt 29 (40+i) := by decide +kernel

theorem threshold_29_41 : ∀ i ∈ List.range 1, ThresholdAt 29 (41+i) := by decide +kernel

theorem threshold_29_42 : ∀ i ∈ List.range 1, ThresholdAt 29 (42+i) := by decide +kernel

theorem threshold_29_43 : ∀ i ∈ List.range 1, ThresholdAt 29 (43+i) := by decide +kernel

theorem threshold_29_44 : ∀ i ∈ List.range 1, ThresholdAt 29 (44+i) := by decide +kernel

theorem threshold_29_45 : ∀ i ∈ List.range 1, ThresholdAt 29 (45+i) := by decide +kernel

theorem threshold_29_46 : ∀ i ∈ List.range 1, ThresholdAt 29 (46+i) := by decide +kernel

theorem threshold_29_47 : ∀ i ∈ List.range 1, ThresholdAt 29 (47+i) := by decide +kernel

theorem threshold_29_48 : ∀ i ∈ List.range 1, ThresholdAt 29 (48+i) := by decide +kernel

theorem threshold_29_49 : ∀ i ∈ List.range 1, ThresholdAt 29 (49+i) := by decide +kernel

theorem threshold_29_50 : ∀ i ∈ List.range 1, ThresholdAt 29 (50+i) := by decide +kernel

theorem threshold_29_51 : ∀ i ∈ List.range 1, ThresholdAt 29 (51+i) := by decide +kernel

theorem threshold_29_52 : ∀ i ∈ List.range 1, ThresholdAt 29 (52+i) := by decide +kernel

theorem threshold_29_53 : ∀ i ∈ List.range 1, ThresholdAt 29 (53+i) := by decide +kernel

theorem threshold_29_54 : ∀ i ∈ List.range 1, ThresholdAt 29 (54+i) := by decide +kernel

theorem threshold_29_55 : ∀ i ∈ List.range 1, ThresholdAt 29 (55+i) := by decide +kernel

theorem threshold_29_56 : ∀ i ∈ List.range 1, ThresholdAt 29 (56+i) := by decide +kernel

theorem threshold_29_57 : ∀ i ∈ List.range 1, ThresholdAt 29 (57+i) := by decide +kernel

theorem threshold_29_58 : ∀ i ∈ List.range 1, ThresholdAt 29 (58+i) := by decide +kernel

theorem threshold_29_59 : ∀ i ∈ List.range 1, ThresholdAt 29 (59+i) := by decide +kernel

theorem threshold_29_60 : ∀ i ∈ List.range 1, ThresholdAt 29 (60+i) := by decide +kernel

theorem threshold_29_61 : ∀ i ∈ List.range 1, ThresholdAt 29 (61+i) := by decide +kernel

theorem threshold_29_62 : ∀ i ∈ List.range 1, ThresholdAt 29 (62+i) := by decide +kernel

theorem threshold_29_63 : ∀ i ∈ List.range 1, ThresholdAt 29 (63+i) := by decide +kernel

theorem threshold_29_64 : ∀ i ∈ List.range 1, ThresholdAt 29 (64+i) := by decide +kernel

theorem threshold_29_65 : ∀ i ∈ List.range 1, ThresholdAt 29 (65+i) := by decide +kernel

theorem threshold_29_66 : ∀ i ∈ List.range 1, ThresholdAt 29 (66+i) := by decide +kernel

theorem threshold_29_67 : ∀ i ∈ List.range 1, ThresholdAt 29 (67+i) := by decide +kernel

theorem threshold_29_68 : ∀ i ∈ List.range 1, ThresholdAt 29 (68+i) := by decide +kernel

theorem threshold_29_69 : ∀ i ∈ List.range 1, ThresholdAt 29 (69+i) := by decide +kernel

theorem threshold_29_70 : ∀ i ∈ List.range 1, ThresholdAt 29 (70+i) := by decide +kernel

theorem threshold_29_71 : ∀ i ∈ List.range 1, ThresholdAt 29 (71+i) := by decide +kernel

theorem threshold_29_72 : ∀ i ∈ List.range 1, ThresholdAt 29 (72+i) := by decide +kernel

theorem threshold_29_73 : ∀ i ∈ List.range 1, ThresholdAt 29 (73+i) := by decide +kernel

theorem threshold_29_74 : ∀ i ∈ List.range 1, ThresholdAt 29 (74+i) := by decide +kernel

theorem threshold_29_75 : ∀ i ∈ List.range 1, ThresholdAt 29 (75+i) := by decide +kernel

theorem threshold_29_76 : ∀ i ∈ List.range 1, ThresholdAt 29 (76+i) := by decide +kernel

theorem threshold_29_77 : ∀ i ∈ List.range 1, ThresholdAt 29 (77+i) := by decide +kernel

theorem threshold_29_78 : ∀ i ∈ List.range 1, ThresholdAt 29 (78+i) := by decide +kernel

theorem threshold_29_79 : ∀ i ∈ List.range 1, ThresholdAt 29 (79+i) := by decide +kernel

theorem threshold_29_80 : ∀ i ∈ List.range 1, ThresholdAt 29 (80+i) := by decide +kernel

theorem threshold_29_81 : ∀ i ∈ List.range 1, ThresholdAt 29 (81+i) := by decide +kernel

theorem threshold_29_82 : ∀ i ∈ List.range 1, ThresholdAt 29 (82+i) := by decide +kernel

theorem threshold_29_83 : ∀ i ∈ List.range 1, ThresholdAt 29 (83+i) := by decide +kernel

theorem threshold_29_84 : ∀ i ∈ List.range 1, ThresholdAt 29 (84+i) := by decide +kernel

theorem threshold_29_85 : ∀ i ∈ List.range 1, ThresholdAt 29 (85+i) := by decide +kernel

theorem threshold_29_86 : ∀ i ∈ List.range 1, ThresholdAt 29 (86+i) := by decide +kernel

theorem threshold_29_87 : ∀ i ∈ List.range 1, ThresholdAt 29 (87+i) := by decide +kernel

theorem threshold_29_88 : ∀ i ∈ List.range 1, ThresholdAt 29 (88+i) := by decide +kernel

theorem threshold_29_89 : ∀ i ∈ List.range 1, ThresholdAt 29 (89+i) := by decide +kernel

theorem threshold_29_90 : ∀ i ∈ List.range 1, ThresholdAt 29 (90+i) := by decide +kernel

theorem threshold_29_91 : ∀ i ∈ List.range 1, ThresholdAt 29 (91+i) := by decide +kernel

theorem threshold_29_92 : ∀ i ∈ List.range 1, ThresholdAt 29 (92+i) := by decide +kernel

theorem threshold_29_93 : ∀ i ∈ List.range 1, ThresholdAt 29 (93+i) := by decide +kernel

theorem threshold_29_94 : ∀ i ∈ List.range 1, ThresholdAt 29 (94+i) := by decide +kernel

theorem threshold_29_95 : ∀ i ∈ List.range 1, ThresholdAt 29 (95+i) := by decide +kernel

theorem threshold_29_96 : ∀ i ∈ List.range 1, ThresholdAt 29 (96+i) := by decide +kernel

theorem threshold_29_97 : ∀ i ∈ List.range 1, ThresholdAt 29 (97+i) := by decide +kernel

theorem threshold_29_98 : ∀ i ∈ List.range 1, ThresholdAt 29 (98+i) := by decide +kernel

theorem threshold_29_99 : ∀ i ∈ List.range 1, ThresholdAt 29 (99+i) := by decide +kernel

theorem threshold_29_100 : ∀ i ∈ List.range 1, ThresholdAt 29 (100+i) := by decide +kernel

theorem threshold_29_101 : ∀ i ∈ List.range 1, ThresholdAt 29 (101+i) := by decide +kernel

theorem threshold_29_102 : ∀ i ∈ List.range 1, ThresholdAt 29 (102+i) := by decide +kernel

theorem threshold_29_103 : ∀ i ∈ List.range 1, ThresholdAt 29 (103+i) := by decide +kernel

theorem threshold_29_104 : ∀ i ∈ List.range 1, ThresholdAt 29 (104+i) := by decide +kernel

theorem threshold_29_105 : ∀ i ∈ List.range 1, ThresholdAt 29 (105+i) := by decide +kernel

theorem threshold_29_106 : ∀ i ∈ List.range 1, ThresholdAt 29 (106+i) := by decide +kernel

theorem threshold_29_107 : ∀ i ∈ List.range 1, ThresholdAt 29 (107+i) := by decide +kernel

theorem threshold_29_108 : ∀ i ∈ List.range 1, ThresholdAt 29 (108+i) := by decide +kernel

theorem threshold_29_109 : ∀ i ∈ List.range 1, ThresholdAt 29 (109+i) := by decide +kernel

theorem threshold_29_110 : ∀ i ∈ List.range 1, ThresholdAt 29 (110+i) := by decide +kernel

theorem threshold_29_111 : ∀ i ∈ List.range 1, ThresholdAt 29 (111+i) := by decide +kernel

theorem threshold_29_112 : ∀ i ∈ List.range 1, ThresholdAt 29 (112+i) := by decide +kernel

theorem threshold_29_113 : ∀ i ∈ List.range 1, ThresholdAt 29 (113+i) := by decide +kernel

theorem threshold_29_114 : ∀ i ∈ List.range 1, ThresholdAt 29 (114+i) := by decide +kernel

theorem threshold_29_115 : ∀ i ∈ List.range 1, ThresholdAt 29 (115+i) := by decide +kernel

theorem threshold_29_116 : ∀ i ∈ List.range 1, ThresholdAt 29 (116+i) := by decide +kernel

theorem threshold_29_117 : ∀ i ∈ List.range 1, ThresholdAt 29 (117+i) := by decide +kernel

theorem threshold_29_118 : ∀ i ∈ List.range 1, ThresholdAt 29 (118+i) := by decide +kernel

theorem threshold_29_119 : ∀ i ∈ List.range 1, ThresholdAt 29 (119+i) := by decide +kernel

theorem threshold_29_120 : ∀ i ∈ List.range 1, ThresholdAt 29 (120+i) := by decide +kernel

theorem threshold_29 (v : ℕ) (hv : v ∈ List.range 121) : ThresholdAt 29 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 29 v)
  have h := (join 0 60 61 (join 0 30 30 (join 0 15 15 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_29_0 (join 1 1 1 threshold_29_1 threshold_29_2)) (join 3 2 2 (join 3 1 1 threshold_29_3 threshold_29_4) (join 5 1 1 threshold_29_5 threshold_29_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_29_7 threshold_29_8) (join 9 1 1 threshold_29_9 threshold_29_10)) (join 11 2 2 (join 11 1 1 threshold_29_11 threshold_29_12) (join 13 1 1 threshold_29_13 threshold_29_14)))) (join 15 7 8 (join 15 3 4 (join 15 1 2 threshold_29_15 (join 16 1 1 threshold_29_16 threshold_29_17)) (join 18 2 2 (join 18 1 1 threshold_29_18 threshold_29_19) (join 20 1 1 threshold_29_20 threshold_29_21))) (join 22 4 4 (join 22 2 2 (join 22 1 1 threshold_29_22 threshold_29_23) (join 24 1 1 threshold_29_24 threshold_29_25)) (join 26 2 2 (join 26 1 1 threshold_29_26 threshold_29_27) (join 28 1 1 threshold_29_28 threshold_29_29))))) (join 30 15 15 (join 30 7 8 (join 30 3 4 (join 30 1 2 threshold_29_30 (join 31 1 1 threshold_29_31 threshold_29_32)) (join 33 2 2 (join 33 1 1 threshold_29_33 threshold_29_34) (join 35 1 1 threshold_29_35 threshold_29_36))) (join 37 4 4 (join 37 2 2 (join 37 1 1 threshold_29_37 threshold_29_38) (join 39 1 1 threshold_29_39 threshold_29_40)) (join 41 2 2 (join 41 1 1 threshold_29_41 threshold_29_42) (join 43 1 1 threshold_29_43 threshold_29_44)))) (join 45 7 8 (join 45 3 4 (join 45 1 2 threshold_29_45 (join 46 1 1 threshold_29_46 threshold_29_47)) (join 48 2 2 (join 48 1 1 threshold_29_48 threshold_29_49) (join 50 1 1 threshold_29_50 threshold_29_51))) (join 52 4 4 (join 52 2 2 (join 52 1 1 threshold_29_52 threshold_29_53) (join 54 1 1 threshold_29_54 threshold_29_55)) (join 56 2 2 (join 56 1 1 threshold_29_56 threshold_29_57) (join 58 1 1 threshold_29_58 threshold_29_59)))))) (join 60 30 31 (join 60 15 15 (join 60 7 8 (join 60 3 4 (join 60 1 2 threshold_29_60 (join 61 1 1 threshold_29_61 threshold_29_62)) (join 63 2 2 (join 63 1 1 threshold_29_63 threshold_29_64) (join 65 1 1 threshold_29_65 threshold_29_66))) (join 67 4 4 (join 67 2 2 (join 67 1 1 threshold_29_67 threshold_29_68) (join 69 1 1 threshold_29_69 threshold_29_70)) (join 71 2 2 (join 71 1 1 threshold_29_71 threshold_29_72) (join 73 1 1 threshold_29_73 threshold_29_74)))) (join 75 7 8 (join 75 3 4 (join 75 1 2 threshold_29_75 (join 76 1 1 threshold_29_76 threshold_29_77)) (join 78 2 2 (join 78 1 1 threshold_29_78 threshold_29_79) (join 80 1 1 threshold_29_80 threshold_29_81))) (join 82 4 4 (join 82 2 2 (join 82 1 1 threshold_29_82 threshold_29_83) (join 84 1 1 threshold_29_84 threshold_29_85)) (join 86 2 2 (join 86 1 1 threshold_29_86 threshold_29_87) (join 88 1 1 threshold_29_88 threshold_29_89))))) (join 90 15 16 (join 90 7 8 (join 90 3 4 (join 90 1 2 threshold_29_90 (join 91 1 1 threshold_29_91 threshold_29_92)) (join 93 2 2 (join 93 1 1 threshold_29_93 threshold_29_94) (join 95 1 1 threshold_29_95 threshold_29_96))) (join 97 4 4 (join 97 2 2 (join 97 1 1 threshold_29_97 threshold_29_98) (join 99 1 1 threshold_29_99 threshold_29_100)) (join 101 2 2 (join 101 1 1 threshold_29_101 threshold_29_102) (join 103 1 1 threshold_29_103 threshold_29_104)))) (join 105 8 8 (join 105 4 4 (join 105 2 2 (join 105 1 1 threshold_29_105 threshold_29_106) (join 107 1 1 threshold_29_107 threshold_29_108)) (join 109 2 2 (join 109 1 1 threshold_29_109 threshold_29_110) (join 111 1 1 threshold_29_111 threshold_29_112))) (join 113 4 4 (join 113 2 2 (join 113 1 1 threshold_29_113 threshold_29_114) (join 115 1 1 threshold_29_115 threshold_29_116)) (join 117 2 2 (join 117 1 1 threshold_29_117 threshold_29_118) (join 119 1 1 threshold_29_119 threshold_29_120)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_29_0 : ∀ i ∈ List.range 4, LedgerAt 29 (0+i) := by decide +kernel

theorem ledger_29_4 : ∀ i ∈ List.range 4, LedgerAt 29 (4+i) := by decide +kernel

theorem ledger_29_8 : ∀ i ∈ List.range 4, LedgerAt 29 (8+i) := by decide +kernel

theorem ledger_29_12 : ∀ i ∈ List.range 4, LedgerAt 29 (12+i) := by decide +kernel

theorem ledger_29_16 : ∀ i ∈ List.range 4, LedgerAt 29 (16+i) := by decide +kernel

theorem ledger_29_20 : ∀ i ∈ List.range 4, LedgerAt 29 (20+i) := by decide +kernel

theorem ledger_29_24 : ∀ i ∈ List.range 4, LedgerAt 29 (24+i) := by decide +kernel

theorem ledger_29_28 : ∀ i ∈ List.range 4, LedgerAt 29 (28+i) := by decide +kernel

theorem ledger_29_32 : ∀ i ∈ List.range 4, LedgerAt 29 (32+i) := by decide +kernel

theorem ledger_29_36 : ∀ i ∈ List.range 4, LedgerAt 29 (36+i) := by decide +kernel

theorem ledger_29_40 : ∀ i ∈ List.range 4, LedgerAt 29 (40+i) := by decide +kernel

theorem ledger_29_44 : ∀ i ∈ List.range 4, LedgerAt 29 (44+i) := by decide +kernel

theorem ledger_29_48 : ∀ i ∈ List.range 4, LedgerAt 29 (48+i) := by decide +kernel

theorem ledger_29_52 : ∀ i ∈ List.range 4, LedgerAt 29 (52+i) := by decide +kernel

theorem ledger_29_56 : ∀ i ∈ List.range 4, LedgerAt 29 (56+i) := by decide +kernel

theorem ledger_29_60 : ∀ i ∈ List.range 4, LedgerAt 29 (60+i) := by decide +kernel

theorem ledger_29_64 : ∀ i ∈ List.range 4, LedgerAt 29 (64+i) := by decide +kernel

theorem ledger_29_68 : ∀ i ∈ List.range 4, LedgerAt 29 (68+i) := by decide +kernel

theorem ledger_29_72 : ∀ i ∈ List.range 4, LedgerAt 29 (72+i) := by decide +kernel

theorem ledger_29_76 : ∀ i ∈ List.range 4, LedgerAt 29 (76+i) := by decide +kernel

theorem ledger_29_80 : ∀ i ∈ List.range 4, LedgerAt 29 (80+i) := by decide +kernel

theorem ledger_29_84 : ∀ i ∈ List.range 4, LedgerAt 29 (84+i) := by decide +kernel

theorem ledger_29_88 : ∀ i ∈ List.range 4, LedgerAt 29 (88+i) := by decide +kernel

theorem ledger_29_92 : ∀ i ∈ List.range 4, LedgerAt 29 (92+i) := by decide +kernel

theorem ledger_29_96 : ∀ i ∈ List.range 4, LedgerAt 29 (96+i) := by decide +kernel

theorem ledger_29_100 : ∀ i ∈ List.range 4, LedgerAt 29 (100+i) := by decide +kernel

theorem ledger_29_104 : ∀ i ∈ List.range 4, LedgerAt 29 (104+i) := by decide +kernel

theorem ledger_29_108 : ∀ i ∈ List.range 4, LedgerAt 29 (108+i) := by decide +kernel

theorem ledger_29_112 : ∀ i ∈ List.range 4, LedgerAt 29 (112+i) := by decide +kernel

theorem ledger_29_116 : ∀ i ∈ List.range 4, LedgerAt 29 (116+i) := by decide +kernel

theorem ledger_29_120 : ∀ i ∈ List.range 1, LedgerAt 29 (120+i) := by decide +kernel

theorem ledger_29 (v : ℕ) (hv : v ∈ List.range 121) : LedgerAt 29 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 29 v)
  have h := (join 0 60 61 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_29_0 (join 4 4 4 ledger_29_4 ledger_29_8)) (join 12 8 8 (join 12 4 4 ledger_29_12 ledger_29_16) (join 20 4 4 ledger_29_20 ledger_29_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_29_28 ledger_29_32) (join 36 4 4 ledger_29_36 ledger_29_40)) (join 44 8 8 (join 44 4 4 ledger_29_44 ledger_29_48) (join 52 4 4 ledger_29_52 ledger_29_56)))) (join 60 32 29 (join 60 16 16 (join 60 8 8 (join 60 4 4 ledger_29_60 ledger_29_64) (join 68 4 4 ledger_29_68 ledger_29_72)) (join 76 8 8 (join 76 4 4 ledger_29_76 ledger_29_80) (join 84 4 4 ledger_29_84 ledger_29_88))) (join 92 16 13 (join 92 8 8 (join 92 4 4 ledger_29_92 ledger_29_96) (join 100 4 4 ledger_29_100 ledger_29_104)) (join 108 8 5 (join 108 4 4 ledger_29_108 ledger_29_112) (join 116 4 1 ledger_29_116 ledger_29_120)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
