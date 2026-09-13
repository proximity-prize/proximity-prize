import ProximityPrize.SubmissionLower.AffineCheckedR306808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_31_0 : ∀ i ∈ List.range 4, SingleAt 31 (0+i) := by decide +kernel

theorem single_31_4 : ∀ i ∈ List.range 4, SingleAt 31 (4+i) := by decide +kernel

theorem single_31_8 : ∀ i ∈ List.range 4, SingleAt 31 (8+i) := by decide +kernel

theorem single_31_12 : ∀ i ∈ List.range 4, SingleAt 31 (12+i) := by decide +kernel

theorem single_31_16 : ∀ i ∈ List.range 4, SingleAt 31 (16+i) := by decide +kernel

theorem single_31_20 : ∀ i ∈ List.range 4, SingleAt 31 (20+i) := by decide +kernel

theorem single_31_24 : ∀ i ∈ List.range 4, SingleAt 31 (24+i) := by decide +kernel

theorem single_31_28 : ∀ i ∈ List.range 4, SingleAt 31 (28+i) := by decide +kernel

theorem single_31_32 : ∀ i ∈ List.range 4, SingleAt 31 (32+i) := by decide +kernel

theorem single_31_36 : ∀ i ∈ List.range 4, SingleAt 31 (36+i) := by decide +kernel

theorem single_31_40 : ∀ i ∈ List.range 4, SingleAt 31 (40+i) := by decide +kernel

theorem single_31_44 : ∀ i ∈ List.range 4, SingleAt 31 (44+i) := by decide +kernel

theorem single_31_48 : ∀ i ∈ List.range 4, SingleAt 31 (48+i) := by decide +kernel

theorem single_31_52 : ∀ i ∈ List.range 4, SingleAt 31 (52+i) := by decide +kernel

theorem single_31_56 : ∀ i ∈ List.range 4, SingleAt 31 (56+i) := by decide +kernel

theorem single_31_60 : ∀ i ∈ List.range 4, SingleAt 31 (60+i) := by decide +kernel

theorem single_31_64 : ∀ i ∈ List.range 4, SingleAt 31 (64+i) := by decide +kernel

theorem single_31_68 : ∀ i ∈ List.range 4, SingleAt 31 (68+i) := by decide +kernel

theorem single_31_72 : ∀ i ∈ List.range 4, SingleAt 31 (72+i) := by decide +kernel

theorem single_31_76 : ∀ i ∈ List.range 4, SingleAt 31 (76+i) := by decide +kernel

theorem single_31_80 : ∀ i ∈ List.range 4, SingleAt 31 (80+i) := by decide +kernel

theorem single_31_84 : ∀ i ∈ List.range 4, SingleAt 31 (84+i) := by decide +kernel

theorem single_31_88 : ∀ i ∈ List.range 4, SingleAt 31 (88+i) := by decide +kernel

theorem single_31_92 : ∀ i ∈ List.range 4, SingleAt 31 (92+i) := by decide +kernel

theorem single_31_96 : ∀ i ∈ List.range 4, SingleAt 31 (96+i) := by decide +kernel

theorem single_31_100 : ∀ i ∈ List.range 4, SingleAt 31 (100+i) := by decide +kernel

theorem single_31_104 : ∀ i ∈ List.range 4, SingleAt 31 (104+i) := by decide +kernel

theorem single_31_108 : ∀ i ∈ List.range 4, SingleAt 31 (108+i) := by decide +kernel

theorem single_31_112 : ∀ i ∈ List.range 4, SingleAt 31 (112+i) := by decide +kernel

theorem single_31_116 : ∀ i ∈ List.range 3, SingleAt 31 (116+i) := by decide +kernel

theorem single_31 (v : ℕ) (hv : v ∈ List.range 119) : SingleAt 31 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 31 v)
  have h := (join 0 60 59 (join 0 28 32 (join 0 12 16 (join 0 4 8 single_31_0 (join 4 4 4 single_31_4 single_31_8)) (join 12 8 8 (join 12 4 4 single_31_12 single_31_16) (join 20 4 4 single_31_20 single_31_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 single_31_28 single_31_32) (join 36 4 4 single_31_36 single_31_40)) (join 44 8 8 (join 44 4 4 single_31_44 single_31_48) (join 52 4 4 single_31_52 single_31_56)))) (join 60 28 31 (join 60 12 16 (join 60 4 8 single_31_60 (join 64 4 4 single_31_64 single_31_68)) (join 72 8 8 (join 72 4 4 single_31_72 single_31_76) (join 80 4 4 single_31_80 single_31_84))) (join 88 16 15 (join 88 8 8 (join 88 4 4 single_31_88 single_31_92) (join 96 4 4 single_31_96 single_31_100)) (join 104 8 7 (join 104 4 4 single_31_104 single_31_108) (join 112 4 3 single_31_112 single_31_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_31_0 : ∀ i ∈ List.range 4, PhaseAt 31 (0+i) := by decide +kernel

theorem phase_31_4 : ∀ i ∈ List.range 4, PhaseAt 31 (4+i) := by decide +kernel

theorem phase_31_8 : ∀ i ∈ List.range 4, PhaseAt 31 (8+i) := by decide +kernel

theorem phase_31_12 : ∀ i ∈ List.range 4, PhaseAt 31 (12+i) := by decide +kernel

theorem phase_31_16 : ∀ i ∈ List.range 4, PhaseAt 31 (16+i) := by decide +kernel

theorem phase_31_20 : ∀ i ∈ List.range 4, PhaseAt 31 (20+i) := by decide +kernel

theorem phase_31_24 : ∀ i ∈ List.range 4, PhaseAt 31 (24+i) := by decide +kernel

theorem phase_31_28 : ∀ i ∈ List.range 4, PhaseAt 31 (28+i) := by decide +kernel

theorem phase_31_32 : ∀ i ∈ List.range 4, PhaseAt 31 (32+i) := by decide +kernel

theorem phase_31_36 : ∀ i ∈ List.range 4, PhaseAt 31 (36+i) := by decide +kernel

theorem phase_31_40 : ∀ i ∈ List.range 4, PhaseAt 31 (40+i) := by decide +kernel

theorem phase_31_44 : ∀ i ∈ List.range 4, PhaseAt 31 (44+i) := by decide +kernel

theorem phase_31_48 : ∀ i ∈ List.range 4, PhaseAt 31 (48+i) := by decide +kernel

theorem phase_31_52 : ∀ i ∈ List.range 4, PhaseAt 31 (52+i) := by decide +kernel

theorem phase_31_56 : ∀ i ∈ List.range 4, PhaseAt 31 (56+i) := by decide +kernel

theorem phase_31_60 : ∀ i ∈ List.range 4, PhaseAt 31 (60+i) := by decide +kernel

theorem phase_31_64 : ∀ i ∈ List.range 4, PhaseAt 31 (64+i) := by decide +kernel

theorem phase_31_68 : ∀ i ∈ List.range 4, PhaseAt 31 (68+i) := by decide +kernel

theorem phase_31_72 : ∀ i ∈ List.range 4, PhaseAt 31 (72+i) := by decide +kernel

theorem phase_31_76 : ∀ i ∈ List.range 4, PhaseAt 31 (76+i) := by decide +kernel

theorem phase_31_80 : ∀ i ∈ List.range 4, PhaseAt 31 (80+i) := by decide +kernel

theorem phase_31_84 : ∀ i ∈ List.range 4, PhaseAt 31 (84+i) := by decide +kernel

theorem phase_31_88 : ∀ i ∈ List.range 4, PhaseAt 31 (88+i) := by decide +kernel

theorem phase_31_92 : ∀ i ∈ List.range 4, PhaseAt 31 (92+i) := by decide +kernel

theorem phase_31_96 : ∀ i ∈ List.range 4, PhaseAt 31 (96+i) := by decide +kernel

theorem phase_31_100 : ∀ i ∈ List.range 4, PhaseAt 31 (100+i) := by decide +kernel

theorem phase_31_104 : ∀ i ∈ List.range 4, PhaseAt 31 (104+i) := by decide +kernel

theorem phase_31_108 : ∀ i ∈ List.range 4, PhaseAt 31 (108+i) := by decide +kernel

theorem phase_31_112 : ∀ i ∈ List.range 4, PhaseAt 31 (112+i) := by decide +kernel

theorem phase_31_116 : ∀ i ∈ List.range 3, PhaseAt 31 (116+i) := by decide +kernel

theorem phase_31 (v : ℕ) (hv : v ∈ List.range 119) : PhaseAt 31 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 31 v)
  have h := (join 0 60 59 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_31_0 (join 4 4 4 phase_31_4 phase_31_8)) (join 12 8 8 (join 12 4 4 phase_31_12 phase_31_16) (join 20 4 4 phase_31_20 phase_31_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_31_28 phase_31_32) (join 36 4 4 phase_31_36 phase_31_40)) (join 44 8 8 (join 44 4 4 phase_31_44 phase_31_48) (join 52 4 4 phase_31_52 phase_31_56)))) (join 60 28 31 (join 60 12 16 (join 60 4 8 phase_31_60 (join 64 4 4 phase_31_64 phase_31_68)) (join 72 8 8 (join 72 4 4 phase_31_72 phase_31_76) (join 80 4 4 phase_31_80 phase_31_84))) (join 88 16 15 (join 88 8 8 (join 88 4 4 phase_31_88 phase_31_92) (join 96 4 4 phase_31_96 phase_31_100)) (join 104 8 7 (join 104 4 4 phase_31_104 phase_31_108) (join 112 4 3 phase_31_112 phase_31_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_31_0 : ∀ i ∈ List.range 1, ThresholdAt 31 (0+i) := by decide +kernel

theorem threshold_31_1 : ∀ i ∈ List.range 1, ThresholdAt 31 (1+i) := by decide +kernel

theorem threshold_31_2 : ∀ i ∈ List.range 1, ThresholdAt 31 (2+i) := by decide +kernel

theorem threshold_31_3 : ∀ i ∈ List.range 1, ThresholdAt 31 (3+i) := by decide +kernel

theorem threshold_31_4 : ∀ i ∈ List.range 1, ThresholdAt 31 (4+i) := by decide +kernel

theorem threshold_31_5 : ∀ i ∈ List.range 1, ThresholdAt 31 (5+i) := by decide +kernel

theorem threshold_31_6 : ∀ i ∈ List.range 1, ThresholdAt 31 (6+i) := by decide +kernel

theorem threshold_31_7 : ∀ i ∈ List.range 1, ThresholdAt 31 (7+i) := by decide +kernel

theorem threshold_31_8 : ∀ i ∈ List.range 1, ThresholdAt 31 (8+i) := by decide +kernel

theorem threshold_31_9 : ∀ i ∈ List.range 1, ThresholdAt 31 (9+i) := by decide +kernel

theorem threshold_31_10 : ∀ i ∈ List.range 1, ThresholdAt 31 (10+i) := by decide +kernel

theorem threshold_31_11 : ∀ i ∈ List.range 1, ThresholdAt 31 (11+i) := by decide +kernel

theorem threshold_31_12 : ∀ i ∈ List.range 1, ThresholdAt 31 (12+i) := by decide +kernel

theorem threshold_31_13 : ∀ i ∈ List.range 1, ThresholdAt 31 (13+i) := by decide +kernel

theorem threshold_31_14 : ∀ i ∈ List.range 1, ThresholdAt 31 (14+i) := by decide +kernel

theorem threshold_31_15 : ∀ i ∈ List.range 1, ThresholdAt 31 (15+i) := by decide +kernel

theorem threshold_31_16 : ∀ i ∈ List.range 1, ThresholdAt 31 (16+i) := by decide +kernel

theorem threshold_31_17 : ∀ i ∈ List.range 1, ThresholdAt 31 (17+i) := by decide +kernel

theorem threshold_31_18 : ∀ i ∈ List.range 1, ThresholdAt 31 (18+i) := by decide +kernel

theorem threshold_31_19 : ∀ i ∈ List.range 1, ThresholdAt 31 (19+i) := by decide +kernel

theorem threshold_31_20 : ∀ i ∈ List.range 1, ThresholdAt 31 (20+i) := by decide +kernel

theorem threshold_31_21 : ∀ i ∈ List.range 1, ThresholdAt 31 (21+i) := by decide +kernel

theorem threshold_31_22 : ∀ i ∈ List.range 1, ThresholdAt 31 (22+i) := by decide +kernel

theorem threshold_31_23 : ∀ i ∈ List.range 1, ThresholdAt 31 (23+i) := by decide +kernel

theorem threshold_31_24 : ∀ i ∈ List.range 1, ThresholdAt 31 (24+i) := by decide +kernel

theorem threshold_31_25 : ∀ i ∈ List.range 1, ThresholdAt 31 (25+i) := by decide +kernel

theorem threshold_31_26 : ∀ i ∈ List.range 1, ThresholdAt 31 (26+i) := by decide +kernel

theorem threshold_31_27 : ∀ i ∈ List.range 1, ThresholdAt 31 (27+i) := by decide +kernel

theorem threshold_31_28 : ∀ i ∈ List.range 1, ThresholdAt 31 (28+i) := by decide +kernel

theorem threshold_31_29 : ∀ i ∈ List.range 1, ThresholdAt 31 (29+i) := by decide +kernel

theorem threshold_31_30 : ∀ i ∈ List.range 1, ThresholdAt 31 (30+i) := by decide +kernel

theorem threshold_31_31 : ∀ i ∈ List.range 1, ThresholdAt 31 (31+i) := by decide +kernel

theorem threshold_31_32 : ∀ i ∈ List.range 1, ThresholdAt 31 (32+i) := by decide +kernel

theorem threshold_31_33 : ∀ i ∈ List.range 1, ThresholdAt 31 (33+i) := by decide +kernel

theorem threshold_31_34 : ∀ i ∈ List.range 1, ThresholdAt 31 (34+i) := by decide +kernel

theorem threshold_31_35 : ∀ i ∈ List.range 1, ThresholdAt 31 (35+i) := by decide +kernel

theorem threshold_31_36 : ∀ i ∈ List.range 1, ThresholdAt 31 (36+i) := by decide +kernel

theorem threshold_31_37 : ∀ i ∈ List.range 1, ThresholdAt 31 (37+i) := by decide +kernel

theorem threshold_31_38 : ∀ i ∈ List.range 1, ThresholdAt 31 (38+i) := by decide +kernel

theorem threshold_31_39 : ∀ i ∈ List.range 1, ThresholdAt 31 (39+i) := by decide +kernel

theorem threshold_31_40 : ∀ i ∈ List.range 1, ThresholdAt 31 (40+i) := by decide +kernel

theorem threshold_31_41 : ∀ i ∈ List.range 1, ThresholdAt 31 (41+i) := by decide +kernel

theorem threshold_31_42 : ∀ i ∈ List.range 1, ThresholdAt 31 (42+i) := by decide +kernel

theorem threshold_31_43 : ∀ i ∈ List.range 1, ThresholdAt 31 (43+i) := by decide +kernel

theorem threshold_31_44 : ∀ i ∈ List.range 1, ThresholdAt 31 (44+i) := by decide +kernel

theorem threshold_31_45 : ∀ i ∈ List.range 1, ThresholdAt 31 (45+i) := by decide +kernel

theorem threshold_31_46 : ∀ i ∈ List.range 1, ThresholdAt 31 (46+i) := by decide +kernel

theorem threshold_31_47 : ∀ i ∈ List.range 1, ThresholdAt 31 (47+i) := by decide +kernel

theorem threshold_31_48 : ∀ i ∈ List.range 1, ThresholdAt 31 (48+i) := by decide +kernel

theorem threshold_31_49 : ∀ i ∈ List.range 1, ThresholdAt 31 (49+i) := by decide +kernel

theorem threshold_31_50 : ∀ i ∈ List.range 1, ThresholdAt 31 (50+i) := by decide +kernel

theorem threshold_31_51 : ∀ i ∈ List.range 1, ThresholdAt 31 (51+i) := by decide +kernel

theorem threshold_31_52 : ∀ i ∈ List.range 1, ThresholdAt 31 (52+i) := by decide +kernel

theorem threshold_31_53 : ∀ i ∈ List.range 1, ThresholdAt 31 (53+i) := by decide +kernel

theorem threshold_31_54 : ∀ i ∈ List.range 1, ThresholdAt 31 (54+i) := by decide +kernel

theorem threshold_31_55 : ∀ i ∈ List.range 1, ThresholdAt 31 (55+i) := by decide +kernel

theorem threshold_31_56 : ∀ i ∈ List.range 1, ThresholdAt 31 (56+i) := by decide +kernel

theorem threshold_31_57 : ∀ i ∈ List.range 1, ThresholdAt 31 (57+i) := by decide +kernel

theorem threshold_31_58 : ∀ i ∈ List.range 1, ThresholdAt 31 (58+i) := by decide +kernel

theorem threshold_31_59 : ∀ i ∈ List.range 1, ThresholdAt 31 (59+i) := by decide +kernel

theorem threshold_31_60 : ∀ i ∈ List.range 1, ThresholdAt 31 (60+i) := by decide +kernel

theorem threshold_31_61 : ∀ i ∈ List.range 1, ThresholdAt 31 (61+i) := by decide +kernel

theorem threshold_31_62 : ∀ i ∈ List.range 1, ThresholdAt 31 (62+i) := by decide +kernel

theorem threshold_31_63 : ∀ i ∈ List.range 1, ThresholdAt 31 (63+i) := by decide +kernel

theorem threshold_31_64 : ∀ i ∈ List.range 1, ThresholdAt 31 (64+i) := by decide +kernel

theorem threshold_31_65 : ∀ i ∈ List.range 1, ThresholdAt 31 (65+i) := by decide +kernel

theorem threshold_31_66 : ∀ i ∈ List.range 1, ThresholdAt 31 (66+i) := by decide +kernel

theorem threshold_31_67 : ∀ i ∈ List.range 1, ThresholdAt 31 (67+i) := by decide +kernel

theorem threshold_31_68 : ∀ i ∈ List.range 1, ThresholdAt 31 (68+i) := by decide +kernel

theorem threshold_31_69 : ∀ i ∈ List.range 1, ThresholdAt 31 (69+i) := by decide +kernel

theorem threshold_31_70 : ∀ i ∈ List.range 1, ThresholdAt 31 (70+i) := by decide +kernel

theorem threshold_31_71 : ∀ i ∈ List.range 1, ThresholdAt 31 (71+i) := by decide +kernel

theorem threshold_31_72 : ∀ i ∈ List.range 1, ThresholdAt 31 (72+i) := by decide +kernel

theorem threshold_31_73 : ∀ i ∈ List.range 1, ThresholdAt 31 (73+i) := by decide +kernel

theorem threshold_31_74 : ∀ i ∈ List.range 1, ThresholdAt 31 (74+i) := by decide +kernel

theorem threshold_31_75 : ∀ i ∈ List.range 1, ThresholdAt 31 (75+i) := by decide +kernel

theorem threshold_31_76 : ∀ i ∈ List.range 1, ThresholdAt 31 (76+i) := by decide +kernel

theorem threshold_31_77 : ∀ i ∈ List.range 1, ThresholdAt 31 (77+i) := by decide +kernel

theorem threshold_31_78 : ∀ i ∈ List.range 1, ThresholdAt 31 (78+i) := by decide +kernel

theorem threshold_31_79 : ∀ i ∈ List.range 1, ThresholdAt 31 (79+i) := by decide +kernel

theorem threshold_31_80 : ∀ i ∈ List.range 1, ThresholdAt 31 (80+i) := by decide +kernel

theorem threshold_31_81 : ∀ i ∈ List.range 1, ThresholdAt 31 (81+i) := by decide +kernel

theorem threshold_31_82 : ∀ i ∈ List.range 1, ThresholdAt 31 (82+i) := by decide +kernel

theorem threshold_31_83 : ∀ i ∈ List.range 1, ThresholdAt 31 (83+i) := by decide +kernel

theorem threshold_31_84 : ∀ i ∈ List.range 1, ThresholdAt 31 (84+i) := by decide +kernel

theorem threshold_31_85 : ∀ i ∈ List.range 1, ThresholdAt 31 (85+i) := by decide +kernel

theorem threshold_31_86 : ∀ i ∈ List.range 1, ThresholdAt 31 (86+i) := by decide +kernel

theorem threshold_31_87 : ∀ i ∈ List.range 1, ThresholdAt 31 (87+i) := by decide +kernel

theorem threshold_31_88 : ∀ i ∈ List.range 1, ThresholdAt 31 (88+i) := by decide +kernel

theorem threshold_31_89 : ∀ i ∈ List.range 1, ThresholdAt 31 (89+i) := by decide +kernel

theorem threshold_31_90 : ∀ i ∈ List.range 1, ThresholdAt 31 (90+i) := by decide +kernel

theorem threshold_31_91 : ∀ i ∈ List.range 1, ThresholdAt 31 (91+i) := by decide +kernel

theorem threshold_31_92 : ∀ i ∈ List.range 1, ThresholdAt 31 (92+i) := by decide +kernel

theorem threshold_31_93 : ∀ i ∈ List.range 1, ThresholdAt 31 (93+i) := by decide +kernel

theorem threshold_31_94 : ∀ i ∈ List.range 1, ThresholdAt 31 (94+i) := by decide +kernel

theorem threshold_31_95 : ∀ i ∈ List.range 1, ThresholdAt 31 (95+i) := by decide +kernel

theorem threshold_31_96 : ∀ i ∈ List.range 1, ThresholdAt 31 (96+i) := by decide +kernel

theorem threshold_31_97 : ∀ i ∈ List.range 1, ThresholdAt 31 (97+i) := by decide +kernel

theorem threshold_31_98 : ∀ i ∈ List.range 1, ThresholdAt 31 (98+i) := by decide +kernel

theorem threshold_31_99 : ∀ i ∈ List.range 1, ThresholdAt 31 (99+i) := by decide +kernel

theorem threshold_31_100 : ∀ i ∈ List.range 1, ThresholdAt 31 (100+i) := by decide +kernel

theorem threshold_31_101 : ∀ i ∈ List.range 1, ThresholdAt 31 (101+i) := by decide +kernel

theorem threshold_31_102 : ∀ i ∈ List.range 1, ThresholdAt 31 (102+i) := by decide +kernel

theorem threshold_31_103 : ∀ i ∈ List.range 1, ThresholdAt 31 (103+i) := by decide +kernel

theorem threshold_31_104 : ∀ i ∈ List.range 1, ThresholdAt 31 (104+i) := by decide +kernel

theorem threshold_31_105 : ∀ i ∈ List.range 1, ThresholdAt 31 (105+i) := by decide +kernel

theorem threshold_31_106 : ∀ i ∈ List.range 1, ThresholdAt 31 (106+i) := by decide +kernel

theorem threshold_31_107 : ∀ i ∈ List.range 1, ThresholdAt 31 (107+i) := by decide +kernel

theorem threshold_31_108 : ∀ i ∈ List.range 1, ThresholdAt 31 (108+i) := by decide +kernel

theorem threshold_31_109 : ∀ i ∈ List.range 1, ThresholdAt 31 (109+i) := by decide +kernel

theorem threshold_31_110 : ∀ i ∈ List.range 1, ThresholdAt 31 (110+i) := by decide +kernel

theorem threshold_31_111 : ∀ i ∈ List.range 1, ThresholdAt 31 (111+i) := by decide +kernel

theorem threshold_31_112 : ∀ i ∈ List.range 1, ThresholdAt 31 (112+i) := by decide +kernel

theorem threshold_31_113 : ∀ i ∈ List.range 1, ThresholdAt 31 (113+i) := by decide +kernel

theorem threshold_31_114 : ∀ i ∈ List.range 1, ThresholdAt 31 (114+i) := by decide +kernel

theorem threshold_31_115 : ∀ i ∈ List.range 1, ThresholdAt 31 (115+i) := by decide +kernel

theorem threshold_31_116 : ∀ i ∈ List.range 1, ThresholdAt 31 (116+i) := by decide +kernel

theorem threshold_31_117 : ∀ i ∈ List.range 1, ThresholdAt 31 (117+i) := by decide +kernel

theorem threshold_31_118 : ∀ i ∈ List.range 1, ThresholdAt 31 (118+i) := by decide +kernel

theorem threshold_31 (v : ℕ) (hv : v ∈ List.range 119) : ThresholdAt 31 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 31 v)
  have h := (join 0 59 60 (join 0 29 30 (join 0 14 15 (join 0 7 7 (join 0 3 4 (join 0 1 2 threshold_31_0 (join 1 1 1 threshold_31_1 threshold_31_2)) (join 3 2 2 (join 3 1 1 threshold_31_3 threshold_31_4) (join 5 1 1 threshold_31_5 threshold_31_6))) (join 7 3 4 (join 7 1 2 threshold_31_7 (join 8 1 1 threshold_31_8 threshold_31_9)) (join 10 2 2 (join 10 1 1 threshold_31_10 threshold_31_11) (join 12 1 1 threshold_31_12 threshold_31_13)))) (join 14 7 8 (join 14 3 4 (join 14 1 2 threshold_31_14 (join 15 1 1 threshold_31_15 threshold_31_16)) (join 17 2 2 (join 17 1 1 threshold_31_17 threshold_31_18) (join 19 1 1 threshold_31_19 threshold_31_20))) (join 21 4 4 (join 21 2 2 (join 21 1 1 threshold_31_21 threshold_31_22) (join 23 1 1 threshold_31_23 threshold_31_24)) (join 25 2 2 (join 25 1 1 threshold_31_25 threshold_31_26) (join 27 1 1 threshold_31_27 threshold_31_28))))) (join 29 15 15 (join 29 7 8 (join 29 3 4 (join 29 1 2 threshold_31_29 (join 30 1 1 threshold_31_30 threshold_31_31)) (join 32 2 2 (join 32 1 1 threshold_31_32 threshold_31_33) (join 34 1 1 threshold_31_34 threshold_31_35))) (join 36 4 4 (join 36 2 2 (join 36 1 1 threshold_31_36 threshold_31_37) (join 38 1 1 threshold_31_38 threshold_31_39)) (join 40 2 2 (join 40 1 1 threshold_31_40 threshold_31_41) (join 42 1 1 threshold_31_42 threshold_31_43)))) (join 44 7 8 (join 44 3 4 (join 44 1 2 threshold_31_44 (join 45 1 1 threshold_31_45 threshold_31_46)) (join 47 2 2 (join 47 1 1 threshold_31_47 threshold_31_48) (join 49 1 1 threshold_31_49 threshold_31_50))) (join 51 4 4 (join 51 2 2 (join 51 1 1 threshold_31_51 threshold_31_52) (join 53 1 1 threshold_31_53 threshold_31_54)) (join 55 2 2 (join 55 1 1 threshold_31_55 threshold_31_56) (join 57 1 1 threshold_31_57 threshold_31_58)))))) (join 59 30 30 (join 59 15 15 (join 59 7 8 (join 59 3 4 (join 59 1 2 threshold_31_59 (join 60 1 1 threshold_31_60 threshold_31_61)) (join 62 2 2 (join 62 1 1 threshold_31_62 threshold_31_63) (join 64 1 1 threshold_31_64 threshold_31_65))) (join 66 4 4 (join 66 2 2 (join 66 1 1 threshold_31_66 threshold_31_67) (join 68 1 1 threshold_31_68 threshold_31_69)) (join 70 2 2 (join 70 1 1 threshold_31_70 threshold_31_71) (join 72 1 1 threshold_31_72 threshold_31_73)))) (join 74 7 8 (join 74 3 4 (join 74 1 2 threshold_31_74 (join 75 1 1 threshold_31_75 threshold_31_76)) (join 77 2 2 (join 77 1 1 threshold_31_77 threshold_31_78) (join 79 1 1 threshold_31_79 threshold_31_80))) (join 81 4 4 (join 81 2 2 (join 81 1 1 threshold_31_81 threshold_31_82) (join 83 1 1 threshold_31_83 threshold_31_84)) (join 85 2 2 (join 85 1 1 threshold_31_85 threshold_31_86) (join 87 1 1 threshold_31_87 threshold_31_88))))) (join 89 15 15 (join 89 7 8 (join 89 3 4 (join 89 1 2 threshold_31_89 (join 90 1 1 threshold_31_90 threshold_31_91)) (join 92 2 2 (join 92 1 1 threshold_31_92 threshold_31_93) (join 94 1 1 threshold_31_94 threshold_31_95))) (join 96 4 4 (join 96 2 2 (join 96 1 1 threshold_31_96 threshold_31_97) (join 98 1 1 threshold_31_98 threshold_31_99)) (join 100 2 2 (join 100 1 1 threshold_31_100 threshold_31_101) (join 102 1 1 threshold_31_102 threshold_31_103)))) (join 104 7 8 (join 104 3 4 (join 104 1 2 threshold_31_104 (join 105 1 1 threshold_31_105 threshold_31_106)) (join 107 2 2 (join 107 1 1 threshold_31_107 threshold_31_108) (join 109 1 1 threshold_31_109 threshold_31_110))) (join 111 4 4 (join 111 2 2 (join 111 1 1 threshold_31_111 threshold_31_112) (join 113 1 1 threshold_31_113 threshold_31_114)) (join 115 2 2 (join 115 1 1 threshold_31_115 threshold_31_116) (join 117 1 1 threshold_31_117 threshold_31_118)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_31_0 : ∀ i ∈ List.range 4, LedgerAt 31 (0+i) := by decide +kernel

theorem ledger_31_4 : ∀ i ∈ List.range 4, LedgerAt 31 (4+i) := by decide +kernel

theorem ledger_31_8 : ∀ i ∈ List.range 4, LedgerAt 31 (8+i) := by decide +kernel

theorem ledger_31_12 : ∀ i ∈ List.range 4, LedgerAt 31 (12+i) := by decide +kernel

theorem ledger_31_16 : ∀ i ∈ List.range 4, LedgerAt 31 (16+i) := by decide +kernel

theorem ledger_31_20 : ∀ i ∈ List.range 4, LedgerAt 31 (20+i) := by decide +kernel

theorem ledger_31_24 : ∀ i ∈ List.range 4, LedgerAt 31 (24+i) := by decide +kernel

theorem ledger_31_28 : ∀ i ∈ List.range 4, LedgerAt 31 (28+i) := by decide +kernel

theorem ledger_31_32 : ∀ i ∈ List.range 4, LedgerAt 31 (32+i) := by decide +kernel

theorem ledger_31_36 : ∀ i ∈ List.range 4, LedgerAt 31 (36+i) := by decide +kernel

theorem ledger_31_40 : ∀ i ∈ List.range 4, LedgerAt 31 (40+i) := by decide +kernel

theorem ledger_31_44 : ∀ i ∈ List.range 4, LedgerAt 31 (44+i) := by decide +kernel

theorem ledger_31_48 : ∀ i ∈ List.range 4, LedgerAt 31 (48+i) := by decide +kernel

theorem ledger_31_52 : ∀ i ∈ List.range 4, LedgerAt 31 (52+i) := by decide +kernel

theorem ledger_31_56 : ∀ i ∈ List.range 4, LedgerAt 31 (56+i) := by decide +kernel

theorem ledger_31_60 : ∀ i ∈ List.range 4, LedgerAt 31 (60+i) := by decide +kernel

theorem ledger_31_64 : ∀ i ∈ List.range 4, LedgerAt 31 (64+i) := by decide +kernel

theorem ledger_31_68 : ∀ i ∈ List.range 4, LedgerAt 31 (68+i) := by decide +kernel

theorem ledger_31_72 : ∀ i ∈ List.range 4, LedgerAt 31 (72+i) := by decide +kernel

theorem ledger_31_76 : ∀ i ∈ List.range 4, LedgerAt 31 (76+i) := by decide +kernel

theorem ledger_31_80 : ∀ i ∈ List.range 4, LedgerAt 31 (80+i) := by decide +kernel

theorem ledger_31_84 : ∀ i ∈ List.range 4, LedgerAt 31 (84+i) := by decide +kernel

theorem ledger_31_88 : ∀ i ∈ List.range 4, LedgerAt 31 (88+i) := by decide +kernel

theorem ledger_31_92 : ∀ i ∈ List.range 4, LedgerAt 31 (92+i) := by decide +kernel

theorem ledger_31_96 : ∀ i ∈ List.range 4, LedgerAt 31 (96+i) := by decide +kernel

theorem ledger_31_100 : ∀ i ∈ List.range 4, LedgerAt 31 (100+i) := by decide +kernel

theorem ledger_31_104 : ∀ i ∈ List.range 4, LedgerAt 31 (104+i) := by decide +kernel

theorem ledger_31_108 : ∀ i ∈ List.range 4, LedgerAt 31 (108+i) := by decide +kernel

theorem ledger_31_112 : ∀ i ∈ List.range 4, LedgerAt 31 (112+i) := by decide +kernel

theorem ledger_31_116 : ∀ i ∈ List.range 3, LedgerAt 31 (116+i) := by decide +kernel

theorem ledger_31 (v : ℕ) (hv : v ∈ List.range 119) : LedgerAt 31 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 31 v)
  have h := (join 0 60 59 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_31_0 (join 4 4 4 ledger_31_4 ledger_31_8)) (join 12 8 8 (join 12 4 4 ledger_31_12 ledger_31_16) (join 20 4 4 ledger_31_20 ledger_31_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_31_28 ledger_31_32) (join 36 4 4 ledger_31_36 ledger_31_40)) (join 44 8 8 (join 44 4 4 ledger_31_44 ledger_31_48) (join 52 4 4 ledger_31_52 ledger_31_56)))) (join 60 28 31 (join 60 12 16 (join 60 4 8 ledger_31_60 (join 64 4 4 ledger_31_64 ledger_31_68)) (join 72 8 8 (join 72 4 4 ledger_31_72 ledger_31_76) (join 80 4 4 ledger_31_80 ledger_31_84))) (join 88 16 15 (join 88 8 8 (join 88 4 4 ledger_31_88 ledger_31_92) (join 96 4 4 ledger_31_96 ledger_31_100)) (join 104 8 7 (join 104 4 4 ledger_31_104 ledger_31_108) (join 112 4 3 ledger_31_112 ledger_31_116)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
