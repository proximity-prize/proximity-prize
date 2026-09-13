import ProximityPrize.SubmissionLower.AffineCheckedR266808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_27_0 : ∀ i ∈ List.range 4, SingleAt 27 (0+i) := by decide +kernel

theorem single_27_4 : ∀ i ∈ List.range 4, SingleAt 27 (4+i) := by decide +kernel

theorem single_27_8 : ∀ i ∈ List.range 4, SingleAt 27 (8+i) := by decide +kernel

theorem single_27_12 : ∀ i ∈ List.range 4, SingleAt 27 (12+i) := by decide +kernel

theorem single_27_16 : ∀ i ∈ List.range 4, SingleAt 27 (16+i) := by decide +kernel

theorem single_27_20 : ∀ i ∈ List.range 4, SingleAt 27 (20+i) := by decide +kernel

theorem single_27_24 : ∀ i ∈ List.range 4, SingleAt 27 (24+i) := by decide +kernel

theorem single_27_28 : ∀ i ∈ List.range 4, SingleAt 27 (28+i) := by decide +kernel

theorem single_27_32 : ∀ i ∈ List.range 4, SingleAt 27 (32+i) := by decide +kernel

theorem single_27_36 : ∀ i ∈ List.range 4, SingleAt 27 (36+i) := by decide +kernel

theorem single_27_40 : ∀ i ∈ List.range 4, SingleAt 27 (40+i) := by decide +kernel

theorem single_27_44 : ∀ i ∈ List.range 4, SingleAt 27 (44+i) := by decide +kernel

theorem single_27_48 : ∀ i ∈ List.range 4, SingleAt 27 (48+i) := by decide +kernel

theorem single_27_52 : ∀ i ∈ List.range 4, SingleAt 27 (52+i) := by decide +kernel

theorem single_27_56 : ∀ i ∈ List.range 4, SingleAt 27 (56+i) := by decide +kernel

theorem single_27_60 : ∀ i ∈ List.range 4, SingleAt 27 (60+i) := by decide +kernel

theorem single_27_64 : ∀ i ∈ List.range 4, SingleAt 27 (64+i) := by decide +kernel

theorem single_27_68 : ∀ i ∈ List.range 4, SingleAt 27 (68+i) := by decide +kernel

theorem single_27_72 : ∀ i ∈ List.range 4, SingleAt 27 (72+i) := by decide +kernel

theorem single_27_76 : ∀ i ∈ List.range 4, SingleAt 27 (76+i) := by decide +kernel

theorem single_27_80 : ∀ i ∈ List.range 4, SingleAt 27 (80+i) := by decide +kernel

theorem single_27_84 : ∀ i ∈ List.range 4, SingleAt 27 (84+i) := by decide +kernel

theorem single_27_88 : ∀ i ∈ List.range 4, SingleAt 27 (88+i) := by decide +kernel

theorem single_27_92 : ∀ i ∈ List.range 4, SingleAt 27 (92+i) := by decide +kernel

theorem single_27_96 : ∀ i ∈ List.range 4, SingleAt 27 (96+i) := by decide +kernel

theorem single_27_100 : ∀ i ∈ List.range 4, SingleAt 27 (100+i) := by decide +kernel

theorem single_27_104 : ∀ i ∈ List.range 4, SingleAt 27 (104+i) := by decide +kernel

theorem single_27_108 : ∀ i ∈ List.range 4, SingleAt 27 (108+i) := by decide +kernel

theorem single_27_112 : ∀ i ∈ List.range 4, SingleAt 27 (112+i) := by decide +kernel

theorem single_27_116 : ∀ i ∈ List.range 4, SingleAt 27 (116+i) := by decide +kernel

theorem single_27_120 : ∀ i ∈ List.range 3, SingleAt 27 (120+i) := by decide +kernel

theorem single_27 (v : ℕ) (hv : v ∈ List.range 123) : SingleAt 27 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 27 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 single_27_0 (join 4 4 4 single_27_4 single_27_8)) (join 12 8 8 (join 12 4 4 single_27_12 single_27_16) (join 20 4 4 single_27_20 single_27_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 single_27_28 single_27_32) (join 36 4 4 single_27_36 single_27_40)) (join 44 8 8 (join 44 4 4 single_27_44 single_27_48) (join 52 4 4 single_27_52 single_27_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 single_27_60 single_27_64) (join 68 4 4 single_27_68 single_27_72)) (join 76 8 8 (join 76 4 4 single_27_76 single_27_80) (join 84 4 4 single_27_84 single_27_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 single_27_92 single_27_96) (join 100 4 4 single_27_100 single_27_104)) (join 108 8 7 (join 108 4 4 single_27_108 single_27_112) (join 116 4 3 single_27_116 single_27_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_27_0 : ∀ i ∈ List.range 4, PhaseAt 27 (0+i) := by decide +kernel

theorem phase_27_4 : ∀ i ∈ List.range 4, PhaseAt 27 (4+i) := by decide +kernel

theorem phase_27_8 : ∀ i ∈ List.range 4, PhaseAt 27 (8+i) := by decide +kernel

theorem phase_27_12 : ∀ i ∈ List.range 4, PhaseAt 27 (12+i) := by decide +kernel

theorem phase_27_16 : ∀ i ∈ List.range 4, PhaseAt 27 (16+i) := by decide +kernel

theorem phase_27_20 : ∀ i ∈ List.range 4, PhaseAt 27 (20+i) := by decide +kernel

theorem phase_27_24 : ∀ i ∈ List.range 4, PhaseAt 27 (24+i) := by decide +kernel

theorem phase_27_28 : ∀ i ∈ List.range 4, PhaseAt 27 (28+i) := by decide +kernel

theorem phase_27_32 : ∀ i ∈ List.range 4, PhaseAt 27 (32+i) := by decide +kernel

theorem phase_27_36 : ∀ i ∈ List.range 4, PhaseAt 27 (36+i) := by decide +kernel

theorem phase_27_40 : ∀ i ∈ List.range 4, PhaseAt 27 (40+i) := by decide +kernel

theorem phase_27_44 : ∀ i ∈ List.range 4, PhaseAt 27 (44+i) := by decide +kernel

theorem phase_27_48 : ∀ i ∈ List.range 4, PhaseAt 27 (48+i) := by decide +kernel

theorem phase_27_52 : ∀ i ∈ List.range 4, PhaseAt 27 (52+i) := by decide +kernel

theorem phase_27_56 : ∀ i ∈ List.range 4, PhaseAt 27 (56+i) := by decide +kernel

theorem phase_27_60 : ∀ i ∈ List.range 4, PhaseAt 27 (60+i) := by decide +kernel

theorem phase_27_64 : ∀ i ∈ List.range 4, PhaseAt 27 (64+i) := by decide +kernel

theorem phase_27_68 : ∀ i ∈ List.range 4, PhaseAt 27 (68+i) := by decide +kernel

theorem phase_27_72 : ∀ i ∈ List.range 4, PhaseAt 27 (72+i) := by decide +kernel

theorem phase_27_76 : ∀ i ∈ List.range 4, PhaseAt 27 (76+i) := by decide +kernel

theorem phase_27_80 : ∀ i ∈ List.range 4, PhaseAt 27 (80+i) := by decide +kernel

theorem phase_27_84 : ∀ i ∈ List.range 4, PhaseAt 27 (84+i) := by decide +kernel

theorem phase_27_88 : ∀ i ∈ List.range 4, PhaseAt 27 (88+i) := by decide +kernel

theorem phase_27_92 : ∀ i ∈ List.range 4, PhaseAt 27 (92+i) := by decide +kernel

theorem phase_27_96 : ∀ i ∈ List.range 4, PhaseAt 27 (96+i) := by decide +kernel

theorem phase_27_100 : ∀ i ∈ List.range 4, PhaseAt 27 (100+i) := by decide +kernel

theorem phase_27_104 : ∀ i ∈ List.range 4, PhaseAt 27 (104+i) := by decide +kernel

theorem phase_27_108 : ∀ i ∈ List.range 4, PhaseAt 27 (108+i) := by decide +kernel

theorem phase_27_112 : ∀ i ∈ List.range 4, PhaseAt 27 (112+i) := by decide +kernel

theorem phase_27_116 : ∀ i ∈ List.range 4, PhaseAt 27 (116+i) := by decide +kernel

theorem phase_27_120 : ∀ i ∈ List.range 3, PhaseAt 27 (120+i) := by decide +kernel

theorem phase_27 (v : ℕ) (hv : v ∈ List.range 123) : PhaseAt 27 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 27 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_27_0 (join 4 4 4 phase_27_4 phase_27_8)) (join 12 8 8 (join 12 4 4 phase_27_12 phase_27_16) (join 20 4 4 phase_27_20 phase_27_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_27_28 phase_27_32) (join 36 4 4 phase_27_36 phase_27_40)) (join 44 8 8 (join 44 4 4 phase_27_44 phase_27_48) (join 52 4 4 phase_27_52 phase_27_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 phase_27_60 phase_27_64) (join 68 4 4 phase_27_68 phase_27_72)) (join 76 8 8 (join 76 4 4 phase_27_76 phase_27_80) (join 84 4 4 phase_27_84 phase_27_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 phase_27_92 phase_27_96) (join 100 4 4 phase_27_100 phase_27_104)) (join 108 8 7 (join 108 4 4 phase_27_108 phase_27_112) (join 116 4 3 phase_27_116 phase_27_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_27_0 : ∀ i ∈ List.range 1, ThresholdAt 27 (0+i) := by decide +kernel

theorem threshold_27_1 : ∀ i ∈ List.range 1, ThresholdAt 27 (1+i) := by decide +kernel

theorem threshold_27_2 : ∀ i ∈ List.range 1, ThresholdAt 27 (2+i) := by decide +kernel

theorem threshold_27_3 : ∀ i ∈ List.range 1, ThresholdAt 27 (3+i) := by decide +kernel

theorem threshold_27_4 : ∀ i ∈ List.range 1, ThresholdAt 27 (4+i) := by decide +kernel

theorem threshold_27_5 : ∀ i ∈ List.range 1, ThresholdAt 27 (5+i) := by decide +kernel

theorem threshold_27_6 : ∀ i ∈ List.range 1, ThresholdAt 27 (6+i) := by decide +kernel

theorem threshold_27_7 : ∀ i ∈ List.range 1, ThresholdAt 27 (7+i) := by decide +kernel

theorem threshold_27_8 : ∀ i ∈ List.range 1, ThresholdAt 27 (8+i) := by decide +kernel

theorem threshold_27_9 : ∀ i ∈ List.range 1, ThresholdAt 27 (9+i) := by decide +kernel

theorem threshold_27_10 : ∀ i ∈ List.range 1, ThresholdAt 27 (10+i) := by decide +kernel

theorem threshold_27_11 : ∀ i ∈ List.range 1, ThresholdAt 27 (11+i) := by decide +kernel

theorem threshold_27_12 : ∀ i ∈ List.range 1, ThresholdAt 27 (12+i) := by decide +kernel

theorem threshold_27_13 : ∀ i ∈ List.range 1, ThresholdAt 27 (13+i) := by decide +kernel

theorem threshold_27_14 : ∀ i ∈ List.range 1, ThresholdAt 27 (14+i) := by decide +kernel

theorem threshold_27_15 : ∀ i ∈ List.range 1, ThresholdAt 27 (15+i) := by decide +kernel

theorem threshold_27_16 : ∀ i ∈ List.range 1, ThresholdAt 27 (16+i) := by decide +kernel

theorem threshold_27_17 : ∀ i ∈ List.range 1, ThresholdAt 27 (17+i) := by decide +kernel

theorem threshold_27_18 : ∀ i ∈ List.range 1, ThresholdAt 27 (18+i) := by decide +kernel

theorem threshold_27_19 : ∀ i ∈ List.range 1, ThresholdAt 27 (19+i) := by decide +kernel

theorem threshold_27_20 : ∀ i ∈ List.range 1, ThresholdAt 27 (20+i) := by decide +kernel

theorem threshold_27_21 : ∀ i ∈ List.range 1, ThresholdAt 27 (21+i) := by decide +kernel

theorem threshold_27_22 : ∀ i ∈ List.range 1, ThresholdAt 27 (22+i) := by decide +kernel

theorem threshold_27_23 : ∀ i ∈ List.range 1, ThresholdAt 27 (23+i) := by decide +kernel

theorem threshold_27_24 : ∀ i ∈ List.range 1, ThresholdAt 27 (24+i) := by decide +kernel

theorem threshold_27_25 : ∀ i ∈ List.range 1, ThresholdAt 27 (25+i) := by decide +kernel

theorem threshold_27_26 : ∀ i ∈ List.range 1, ThresholdAt 27 (26+i) := by decide +kernel

theorem threshold_27_27 : ∀ i ∈ List.range 1, ThresholdAt 27 (27+i) := by decide +kernel

theorem threshold_27_28 : ∀ i ∈ List.range 1, ThresholdAt 27 (28+i) := by decide +kernel

theorem threshold_27_29 : ∀ i ∈ List.range 1, ThresholdAt 27 (29+i) := by decide +kernel

theorem threshold_27_30 : ∀ i ∈ List.range 1, ThresholdAt 27 (30+i) := by decide +kernel

theorem threshold_27_31 : ∀ i ∈ List.range 1, ThresholdAt 27 (31+i) := by decide +kernel

theorem threshold_27_32 : ∀ i ∈ List.range 1, ThresholdAt 27 (32+i) := by decide +kernel

theorem threshold_27_33 : ∀ i ∈ List.range 1, ThresholdAt 27 (33+i) := by decide +kernel

theorem threshold_27_34 : ∀ i ∈ List.range 1, ThresholdAt 27 (34+i) := by decide +kernel

theorem threshold_27_35 : ∀ i ∈ List.range 1, ThresholdAt 27 (35+i) := by decide +kernel

theorem threshold_27_36 : ∀ i ∈ List.range 1, ThresholdAt 27 (36+i) := by decide +kernel

theorem threshold_27_37 : ∀ i ∈ List.range 1, ThresholdAt 27 (37+i) := by decide +kernel

theorem threshold_27_38 : ∀ i ∈ List.range 1, ThresholdAt 27 (38+i) := by decide +kernel

theorem threshold_27_39 : ∀ i ∈ List.range 1, ThresholdAt 27 (39+i) := by decide +kernel

theorem threshold_27_40 : ∀ i ∈ List.range 1, ThresholdAt 27 (40+i) := by decide +kernel

theorem threshold_27_41 : ∀ i ∈ List.range 1, ThresholdAt 27 (41+i) := by decide +kernel

theorem threshold_27_42 : ∀ i ∈ List.range 1, ThresholdAt 27 (42+i) := by decide +kernel

theorem threshold_27_43 : ∀ i ∈ List.range 1, ThresholdAt 27 (43+i) := by decide +kernel

theorem threshold_27_44 : ∀ i ∈ List.range 1, ThresholdAt 27 (44+i) := by decide +kernel

theorem threshold_27_45 : ∀ i ∈ List.range 1, ThresholdAt 27 (45+i) := by decide +kernel

theorem threshold_27_46 : ∀ i ∈ List.range 1, ThresholdAt 27 (46+i) := by decide +kernel

theorem threshold_27_47 : ∀ i ∈ List.range 1, ThresholdAt 27 (47+i) := by decide +kernel

theorem threshold_27_48 : ∀ i ∈ List.range 1, ThresholdAt 27 (48+i) := by decide +kernel

theorem threshold_27_49 : ∀ i ∈ List.range 1, ThresholdAt 27 (49+i) := by decide +kernel

theorem threshold_27_50 : ∀ i ∈ List.range 1, ThresholdAt 27 (50+i) := by decide +kernel

theorem threshold_27_51 : ∀ i ∈ List.range 1, ThresholdAt 27 (51+i) := by decide +kernel

theorem threshold_27_52 : ∀ i ∈ List.range 1, ThresholdAt 27 (52+i) := by decide +kernel

theorem threshold_27_53 : ∀ i ∈ List.range 1, ThresholdAt 27 (53+i) := by decide +kernel

theorem threshold_27_54 : ∀ i ∈ List.range 1, ThresholdAt 27 (54+i) := by decide +kernel

theorem threshold_27_55 : ∀ i ∈ List.range 1, ThresholdAt 27 (55+i) := by decide +kernel

theorem threshold_27_56 : ∀ i ∈ List.range 1, ThresholdAt 27 (56+i) := by decide +kernel

theorem threshold_27_57 : ∀ i ∈ List.range 1, ThresholdAt 27 (57+i) := by decide +kernel

theorem threshold_27_58 : ∀ i ∈ List.range 1, ThresholdAt 27 (58+i) := by decide +kernel

theorem threshold_27_59 : ∀ i ∈ List.range 1, ThresholdAt 27 (59+i) := by decide +kernel

theorem threshold_27_60 : ∀ i ∈ List.range 1, ThresholdAt 27 (60+i) := by decide +kernel

theorem threshold_27_61 : ∀ i ∈ List.range 1, ThresholdAt 27 (61+i) := by decide +kernel

theorem threshold_27_62 : ∀ i ∈ List.range 1, ThresholdAt 27 (62+i) := by decide +kernel

theorem threshold_27_63 : ∀ i ∈ List.range 1, ThresholdAt 27 (63+i) := by decide +kernel

theorem threshold_27_64 : ∀ i ∈ List.range 1, ThresholdAt 27 (64+i) := by decide +kernel

theorem threshold_27_65 : ∀ i ∈ List.range 1, ThresholdAt 27 (65+i) := by decide +kernel

theorem threshold_27_66 : ∀ i ∈ List.range 1, ThresholdAt 27 (66+i) := by decide +kernel

theorem threshold_27_67 : ∀ i ∈ List.range 1, ThresholdAt 27 (67+i) := by decide +kernel

theorem threshold_27_68 : ∀ i ∈ List.range 1, ThresholdAt 27 (68+i) := by decide +kernel

theorem threshold_27_69 : ∀ i ∈ List.range 1, ThresholdAt 27 (69+i) := by decide +kernel

theorem threshold_27_70 : ∀ i ∈ List.range 1, ThresholdAt 27 (70+i) := by decide +kernel

theorem threshold_27_71 : ∀ i ∈ List.range 1, ThresholdAt 27 (71+i) := by decide +kernel

theorem threshold_27_72 : ∀ i ∈ List.range 1, ThresholdAt 27 (72+i) := by decide +kernel

theorem threshold_27_73 : ∀ i ∈ List.range 1, ThresholdAt 27 (73+i) := by decide +kernel

theorem threshold_27_74 : ∀ i ∈ List.range 1, ThresholdAt 27 (74+i) := by decide +kernel

theorem threshold_27_75 : ∀ i ∈ List.range 1, ThresholdAt 27 (75+i) := by decide +kernel

theorem threshold_27_76 : ∀ i ∈ List.range 1, ThresholdAt 27 (76+i) := by decide +kernel

theorem threshold_27_77 : ∀ i ∈ List.range 1, ThresholdAt 27 (77+i) := by decide +kernel

theorem threshold_27_78 : ∀ i ∈ List.range 1, ThresholdAt 27 (78+i) := by decide +kernel

theorem threshold_27_79 : ∀ i ∈ List.range 1, ThresholdAt 27 (79+i) := by decide +kernel

theorem threshold_27_80 : ∀ i ∈ List.range 1, ThresholdAt 27 (80+i) := by decide +kernel

theorem threshold_27_81 : ∀ i ∈ List.range 1, ThresholdAt 27 (81+i) := by decide +kernel

theorem threshold_27_82 : ∀ i ∈ List.range 1, ThresholdAt 27 (82+i) := by decide +kernel

theorem threshold_27_83 : ∀ i ∈ List.range 1, ThresholdAt 27 (83+i) := by decide +kernel

theorem threshold_27_84 : ∀ i ∈ List.range 1, ThresholdAt 27 (84+i) := by decide +kernel

theorem threshold_27_85 : ∀ i ∈ List.range 1, ThresholdAt 27 (85+i) := by decide +kernel

theorem threshold_27_86 : ∀ i ∈ List.range 1, ThresholdAt 27 (86+i) := by decide +kernel

theorem threshold_27_87 : ∀ i ∈ List.range 1, ThresholdAt 27 (87+i) := by decide +kernel

theorem threshold_27_88 : ∀ i ∈ List.range 1, ThresholdAt 27 (88+i) := by decide +kernel

theorem threshold_27_89 : ∀ i ∈ List.range 1, ThresholdAt 27 (89+i) := by decide +kernel

theorem threshold_27_90 : ∀ i ∈ List.range 1, ThresholdAt 27 (90+i) := by decide +kernel

theorem threshold_27_91 : ∀ i ∈ List.range 1, ThresholdAt 27 (91+i) := by decide +kernel

theorem threshold_27_92 : ∀ i ∈ List.range 1, ThresholdAt 27 (92+i) := by decide +kernel

theorem threshold_27_93 : ∀ i ∈ List.range 1, ThresholdAt 27 (93+i) := by decide +kernel

theorem threshold_27_94 : ∀ i ∈ List.range 1, ThresholdAt 27 (94+i) := by decide +kernel

theorem threshold_27_95 : ∀ i ∈ List.range 1, ThresholdAt 27 (95+i) := by decide +kernel

theorem threshold_27_96 : ∀ i ∈ List.range 1, ThresholdAt 27 (96+i) := by decide +kernel

theorem threshold_27_97 : ∀ i ∈ List.range 1, ThresholdAt 27 (97+i) := by decide +kernel

theorem threshold_27_98 : ∀ i ∈ List.range 1, ThresholdAt 27 (98+i) := by decide +kernel

theorem threshold_27_99 : ∀ i ∈ List.range 1, ThresholdAt 27 (99+i) := by decide +kernel

theorem threshold_27_100 : ∀ i ∈ List.range 1, ThresholdAt 27 (100+i) := by decide +kernel

theorem threshold_27_101 : ∀ i ∈ List.range 1, ThresholdAt 27 (101+i) := by decide +kernel

theorem threshold_27_102 : ∀ i ∈ List.range 1, ThresholdAt 27 (102+i) := by decide +kernel

theorem threshold_27_103 : ∀ i ∈ List.range 1, ThresholdAt 27 (103+i) := by decide +kernel

theorem threshold_27_104 : ∀ i ∈ List.range 1, ThresholdAt 27 (104+i) := by decide +kernel

theorem threshold_27_105 : ∀ i ∈ List.range 1, ThresholdAt 27 (105+i) := by decide +kernel

theorem threshold_27_106 : ∀ i ∈ List.range 1, ThresholdAt 27 (106+i) := by decide +kernel

theorem threshold_27_107 : ∀ i ∈ List.range 1, ThresholdAt 27 (107+i) := by decide +kernel

theorem threshold_27_108 : ∀ i ∈ List.range 1, ThresholdAt 27 (108+i) := by decide +kernel

theorem threshold_27_109 : ∀ i ∈ List.range 1, ThresholdAt 27 (109+i) := by decide +kernel

theorem threshold_27_110 : ∀ i ∈ List.range 1, ThresholdAt 27 (110+i) := by decide +kernel

theorem threshold_27_111 : ∀ i ∈ List.range 1, ThresholdAt 27 (111+i) := by decide +kernel

theorem threshold_27_112 : ∀ i ∈ List.range 1, ThresholdAt 27 (112+i) := by decide +kernel

theorem threshold_27_113 : ∀ i ∈ List.range 1, ThresholdAt 27 (113+i) := by decide +kernel

theorem threshold_27_114 : ∀ i ∈ List.range 1, ThresholdAt 27 (114+i) := by decide +kernel

theorem threshold_27_115 : ∀ i ∈ List.range 1, ThresholdAt 27 (115+i) := by decide +kernel

theorem threshold_27_116 : ∀ i ∈ List.range 1, ThresholdAt 27 (116+i) := by decide +kernel

theorem threshold_27_117 : ∀ i ∈ List.range 1, ThresholdAt 27 (117+i) := by decide +kernel

theorem threshold_27_118 : ∀ i ∈ List.range 1, ThresholdAt 27 (118+i) := by decide +kernel

theorem threshold_27_119 : ∀ i ∈ List.range 1, ThresholdAt 27 (119+i) := by decide +kernel

theorem threshold_27_120 : ∀ i ∈ List.range 1, ThresholdAt 27 (120+i) := by decide +kernel

theorem threshold_27_121 : ∀ i ∈ List.range 1, ThresholdAt 27 (121+i) := by decide +kernel

theorem threshold_27_122 : ∀ i ∈ List.range 1, ThresholdAt 27 (122+i) := by decide +kernel

theorem threshold_27 (v : ℕ) (hv : v ∈ List.range 123) : ThresholdAt 27 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 27 v)
  have h := (join 0 61 62 (join 0 30 31 (join 0 15 15 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_27_0 (join 1 1 1 threshold_27_1 threshold_27_2)) (join 3 2 2 (join 3 1 1 threshold_27_3 threshold_27_4) (join 5 1 1 threshold_27_5 threshold_27_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_27_7 threshold_27_8) (join 9 1 1 threshold_27_9 threshold_27_10)) (join 11 2 2 (join 11 1 1 threshold_27_11 threshold_27_12) (join 13 1 1 threshold_27_13 threshold_27_14)))) (join 15 7 8 (join 15 3 4 (join 15 1 2 threshold_27_15 (join 16 1 1 threshold_27_16 threshold_27_17)) (join 18 2 2 (join 18 1 1 threshold_27_18 threshold_27_19) (join 20 1 1 threshold_27_20 threshold_27_21))) (join 22 4 4 (join 22 2 2 (join 22 1 1 threshold_27_22 threshold_27_23) (join 24 1 1 threshold_27_24 threshold_27_25)) (join 26 2 2 (join 26 1 1 threshold_27_26 threshold_27_27) (join 28 1 1 threshold_27_28 threshold_27_29))))) (join 30 15 16 (join 30 7 8 (join 30 3 4 (join 30 1 2 threshold_27_30 (join 31 1 1 threshold_27_31 threshold_27_32)) (join 33 2 2 (join 33 1 1 threshold_27_33 threshold_27_34) (join 35 1 1 threshold_27_35 threshold_27_36))) (join 37 4 4 (join 37 2 2 (join 37 1 1 threshold_27_37 threshold_27_38) (join 39 1 1 threshold_27_39 threshold_27_40)) (join 41 2 2 (join 41 1 1 threshold_27_41 threshold_27_42) (join 43 1 1 threshold_27_43 threshold_27_44)))) (join 45 8 8 (join 45 4 4 (join 45 2 2 (join 45 1 1 threshold_27_45 threshold_27_46) (join 47 1 1 threshold_27_47 threshold_27_48)) (join 49 2 2 (join 49 1 1 threshold_27_49 threshold_27_50) (join 51 1 1 threshold_27_51 threshold_27_52))) (join 53 4 4 (join 53 2 2 (join 53 1 1 threshold_27_53 threshold_27_54) (join 55 1 1 threshold_27_55 threshold_27_56)) (join 57 2 2 (join 57 1 1 threshold_27_57 threshold_27_58) (join 59 1 1 threshold_27_59 threshold_27_60)))))) (join 61 31 31 (join 61 15 16 (join 61 7 8 (join 61 3 4 (join 61 1 2 threshold_27_61 (join 62 1 1 threshold_27_62 threshold_27_63)) (join 64 2 2 (join 64 1 1 threshold_27_64 threshold_27_65) (join 66 1 1 threshold_27_66 threshold_27_67))) (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_27_68 threshold_27_69) (join 70 1 1 threshold_27_70 threshold_27_71)) (join 72 2 2 (join 72 1 1 threshold_27_72 threshold_27_73) (join 74 1 1 threshold_27_74 threshold_27_75)))) (join 76 8 8 (join 76 4 4 (join 76 2 2 (join 76 1 1 threshold_27_76 threshold_27_77) (join 78 1 1 threshold_27_78 threshold_27_79)) (join 80 2 2 (join 80 1 1 threshold_27_80 threshold_27_81) (join 82 1 1 threshold_27_82 threshold_27_83))) (join 84 4 4 (join 84 2 2 (join 84 1 1 threshold_27_84 threshold_27_85) (join 86 1 1 threshold_27_86 threshold_27_87)) (join 88 2 2 (join 88 1 1 threshold_27_88 threshold_27_89) (join 90 1 1 threshold_27_90 threshold_27_91))))) (join 92 15 16 (join 92 7 8 (join 92 3 4 (join 92 1 2 threshold_27_92 (join 93 1 1 threshold_27_93 threshold_27_94)) (join 95 2 2 (join 95 1 1 threshold_27_95 threshold_27_96) (join 97 1 1 threshold_27_97 threshold_27_98))) (join 99 4 4 (join 99 2 2 (join 99 1 1 threshold_27_99 threshold_27_100) (join 101 1 1 threshold_27_101 threshold_27_102)) (join 103 2 2 (join 103 1 1 threshold_27_103 threshold_27_104) (join 105 1 1 threshold_27_105 threshold_27_106)))) (join 107 8 8 (join 107 4 4 (join 107 2 2 (join 107 1 1 threshold_27_107 threshold_27_108) (join 109 1 1 threshold_27_109 threshold_27_110)) (join 111 2 2 (join 111 1 1 threshold_27_111 threshold_27_112) (join 113 1 1 threshold_27_113 threshold_27_114))) (join 115 4 4 (join 115 2 2 (join 115 1 1 threshold_27_115 threshold_27_116) (join 117 1 1 threshold_27_117 threshold_27_118)) (join 119 2 2 (join 119 1 1 threshold_27_119 threshold_27_120) (join 121 1 1 threshold_27_121 threshold_27_122)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_27_0 : ∀ i ∈ List.range 4, LedgerAt 27 (0+i) := by decide +kernel

theorem ledger_27_4 : ∀ i ∈ List.range 4, LedgerAt 27 (4+i) := by decide +kernel

theorem ledger_27_8 : ∀ i ∈ List.range 4, LedgerAt 27 (8+i) := by decide +kernel

theorem ledger_27_12 : ∀ i ∈ List.range 4, LedgerAt 27 (12+i) := by decide +kernel

theorem ledger_27_16 : ∀ i ∈ List.range 4, LedgerAt 27 (16+i) := by decide +kernel

theorem ledger_27_20 : ∀ i ∈ List.range 4, LedgerAt 27 (20+i) := by decide +kernel

theorem ledger_27_24 : ∀ i ∈ List.range 4, LedgerAt 27 (24+i) := by decide +kernel

theorem ledger_27_28 : ∀ i ∈ List.range 4, LedgerAt 27 (28+i) := by decide +kernel

theorem ledger_27_32 : ∀ i ∈ List.range 4, LedgerAt 27 (32+i) := by decide +kernel

theorem ledger_27_36 : ∀ i ∈ List.range 4, LedgerAt 27 (36+i) := by decide +kernel

theorem ledger_27_40 : ∀ i ∈ List.range 4, LedgerAt 27 (40+i) := by decide +kernel

theorem ledger_27_44 : ∀ i ∈ List.range 4, LedgerAt 27 (44+i) := by decide +kernel

theorem ledger_27_48 : ∀ i ∈ List.range 4, LedgerAt 27 (48+i) := by decide +kernel

theorem ledger_27_52 : ∀ i ∈ List.range 4, LedgerAt 27 (52+i) := by decide +kernel

theorem ledger_27_56 : ∀ i ∈ List.range 4, LedgerAt 27 (56+i) := by decide +kernel

theorem ledger_27_60 : ∀ i ∈ List.range 4, LedgerAt 27 (60+i) := by decide +kernel

theorem ledger_27_64 : ∀ i ∈ List.range 4, LedgerAt 27 (64+i) := by decide +kernel

theorem ledger_27_68 : ∀ i ∈ List.range 4, LedgerAt 27 (68+i) := by decide +kernel

theorem ledger_27_72 : ∀ i ∈ List.range 4, LedgerAt 27 (72+i) := by decide +kernel

theorem ledger_27_76 : ∀ i ∈ List.range 4, LedgerAt 27 (76+i) := by decide +kernel

theorem ledger_27_80 : ∀ i ∈ List.range 4, LedgerAt 27 (80+i) := by decide +kernel

theorem ledger_27_84 : ∀ i ∈ List.range 4, LedgerAt 27 (84+i) := by decide +kernel

theorem ledger_27_88 : ∀ i ∈ List.range 4, LedgerAt 27 (88+i) := by decide +kernel

theorem ledger_27_92 : ∀ i ∈ List.range 4, LedgerAt 27 (92+i) := by decide +kernel

theorem ledger_27_96 : ∀ i ∈ List.range 4, LedgerAt 27 (96+i) := by decide +kernel

theorem ledger_27_100 : ∀ i ∈ List.range 4, LedgerAt 27 (100+i) := by decide +kernel

theorem ledger_27_104 : ∀ i ∈ List.range 4, LedgerAt 27 (104+i) := by decide +kernel

theorem ledger_27_108 : ∀ i ∈ List.range 4, LedgerAt 27 (108+i) := by decide +kernel

theorem ledger_27_112 : ∀ i ∈ List.range 4, LedgerAt 27 (112+i) := by decide +kernel

theorem ledger_27_116 : ∀ i ∈ List.range 4, LedgerAt 27 (116+i) := by decide +kernel

theorem ledger_27_120 : ∀ i ∈ List.range 3, LedgerAt 27 (120+i) := by decide +kernel

theorem ledger_27 (v : ℕ) (hv : v ∈ List.range 123) : LedgerAt 27 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 27 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_27_0 (join 4 4 4 ledger_27_4 ledger_27_8)) (join 12 8 8 (join 12 4 4 ledger_27_12 ledger_27_16) (join 20 4 4 ledger_27_20 ledger_27_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_27_28 ledger_27_32) (join 36 4 4 ledger_27_36 ledger_27_40)) (join 44 8 8 (join 44 4 4 ledger_27_44 ledger_27_48) (join 52 4 4 ledger_27_52 ledger_27_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 ledger_27_60 ledger_27_64) (join 68 4 4 ledger_27_68 ledger_27_72)) (join 76 8 8 (join 76 4 4 ledger_27_76 ledger_27_80) (join 84 4 4 ledger_27_84 ledger_27_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 ledger_27_92 ledger_27_96) (join 100 4 4 ledger_27_100 ledger_27_104)) (join 108 8 7 (join 108 4 4 ledger_27_108 ledger_27_112) (join 116 4 3 ledger_27_116 ledger_27_120)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
