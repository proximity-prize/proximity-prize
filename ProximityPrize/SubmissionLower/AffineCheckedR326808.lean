import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_32_0 : ∀ i ∈ List.range 4, SingleAt 32 (0+i) := by decide +kernel

theorem single_32_4 : ∀ i ∈ List.range 4, SingleAt 32 (4+i) := by decide +kernel

theorem single_32_8 : ∀ i ∈ List.range 4, SingleAt 32 (8+i) := by decide +kernel

theorem single_32_12 : ∀ i ∈ List.range 4, SingleAt 32 (12+i) := by decide +kernel

theorem single_32_16 : ∀ i ∈ List.range 4, SingleAt 32 (16+i) := by decide +kernel

theorem single_32_20 : ∀ i ∈ List.range 4, SingleAt 32 (20+i) := by decide +kernel

theorem single_32_24 : ∀ i ∈ List.range 4, SingleAt 32 (24+i) := by decide +kernel

theorem single_32_28 : ∀ i ∈ List.range 4, SingleAt 32 (28+i) := by decide +kernel

theorem single_32_32 : ∀ i ∈ List.range 4, SingleAt 32 (32+i) := by decide +kernel

theorem single_32_36 : ∀ i ∈ List.range 4, SingleAt 32 (36+i) := by decide +kernel

theorem single_32_40 : ∀ i ∈ List.range 4, SingleAt 32 (40+i) := by decide +kernel

theorem single_32_44 : ∀ i ∈ List.range 4, SingleAt 32 (44+i) := by decide +kernel

theorem single_32_48 : ∀ i ∈ List.range 4, SingleAt 32 (48+i) := by decide +kernel

theorem single_32_52 : ∀ i ∈ List.range 4, SingleAt 32 (52+i) := by decide +kernel

theorem single_32_56 : ∀ i ∈ List.range 4, SingleAt 32 (56+i) := by decide +kernel

theorem single_32_60 : ∀ i ∈ List.range 4, SingleAt 32 (60+i) := by decide +kernel

theorem single_32_64 : ∀ i ∈ List.range 4, SingleAt 32 (64+i) := by decide +kernel

theorem single_32_68 : ∀ i ∈ List.range 4, SingleAt 32 (68+i) := by decide +kernel

theorem single_32_72 : ∀ i ∈ List.range 4, SingleAt 32 (72+i) := by decide +kernel

theorem single_32_76 : ∀ i ∈ List.range 4, SingleAt 32 (76+i) := by decide +kernel

theorem single_32_80 : ∀ i ∈ List.range 4, SingleAt 32 (80+i) := by decide +kernel

theorem single_32_84 : ∀ i ∈ List.range 4, SingleAt 32 (84+i) := by decide +kernel

theorem single_32_88 : ∀ i ∈ List.range 4, SingleAt 32 (88+i) := by decide +kernel

theorem single_32_92 : ∀ i ∈ List.range 4, SingleAt 32 (92+i) := by decide +kernel

theorem single_32_96 : ∀ i ∈ List.range 4, SingleAt 32 (96+i) := by decide +kernel

theorem single_32_100 : ∀ i ∈ List.range 4, SingleAt 32 (100+i) := by decide +kernel

theorem single_32_104 : ∀ i ∈ List.range 4, SingleAt 32 (104+i) := by decide +kernel

theorem single_32_108 : ∀ i ∈ List.range 4, SingleAt 32 (108+i) := by decide +kernel

theorem single_32_112 : ∀ i ∈ List.range 4, SingleAt 32 (112+i) := by decide +kernel

theorem single_32_116 : ∀ i ∈ List.range 2, SingleAt 32 (116+i) := by decide +kernel

theorem single_32 (v : ℕ) (hv : v ∈ List.range 118) : SingleAt 32 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 32 v)
  have h := (join 0 60 58 (join 0 28 32 (join 0 12 16 (join 0 4 8 single_32_0 (join 4 4 4 single_32_4 single_32_8)) (join 12 8 8 (join 12 4 4 single_32_12 single_32_16) (join 20 4 4 single_32_20 single_32_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 single_32_28 single_32_32) (join 36 4 4 single_32_36 single_32_40)) (join 44 8 8 (join 44 4 4 single_32_44 single_32_48) (join 52 4 4 single_32_52 single_32_56)))) (join 60 28 30 (join 60 12 16 (join 60 4 8 single_32_60 (join 64 4 4 single_32_64 single_32_68)) (join 72 8 8 (join 72 4 4 single_32_72 single_32_76) (join 80 4 4 single_32_80 single_32_84))) (join 88 16 14 (join 88 8 8 (join 88 4 4 single_32_88 single_32_92) (join 96 4 4 single_32_96 single_32_100)) (join 104 8 6 (join 104 4 4 single_32_104 single_32_108) (join 112 4 2 single_32_112 single_32_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_32_0 : ∀ i ∈ List.range 4, PhaseAt 32 (0+i) := by decide +kernel

theorem phase_32_4 : ∀ i ∈ List.range 4, PhaseAt 32 (4+i) := by decide +kernel

theorem phase_32_8 : ∀ i ∈ List.range 4, PhaseAt 32 (8+i) := by decide +kernel

theorem phase_32_12 : ∀ i ∈ List.range 4, PhaseAt 32 (12+i) := by decide +kernel

theorem phase_32_16 : ∀ i ∈ List.range 4, PhaseAt 32 (16+i) := by decide +kernel

theorem phase_32_20 : ∀ i ∈ List.range 4, PhaseAt 32 (20+i) := by decide +kernel

theorem phase_32_24 : ∀ i ∈ List.range 4, PhaseAt 32 (24+i) := by decide +kernel

theorem phase_32_28 : ∀ i ∈ List.range 4, PhaseAt 32 (28+i) := by decide +kernel

theorem phase_32_32 : ∀ i ∈ List.range 4, PhaseAt 32 (32+i) := by decide +kernel

theorem phase_32_36 : ∀ i ∈ List.range 4, PhaseAt 32 (36+i) := by decide +kernel

theorem phase_32_40 : ∀ i ∈ List.range 4, PhaseAt 32 (40+i) := by decide +kernel

theorem phase_32_44 : ∀ i ∈ List.range 4, PhaseAt 32 (44+i) := by decide +kernel

theorem phase_32_48 : ∀ i ∈ List.range 4, PhaseAt 32 (48+i) := by decide +kernel

theorem phase_32_52 : ∀ i ∈ List.range 4, PhaseAt 32 (52+i) := by decide +kernel

theorem phase_32_56 : ∀ i ∈ List.range 4, PhaseAt 32 (56+i) := by decide +kernel

theorem phase_32_60 : ∀ i ∈ List.range 4, PhaseAt 32 (60+i) := by decide +kernel

theorem phase_32_64 : ∀ i ∈ List.range 4, PhaseAt 32 (64+i) := by decide +kernel

theorem phase_32_68 : ∀ i ∈ List.range 4, PhaseAt 32 (68+i) := by decide +kernel

theorem phase_32_72 : ∀ i ∈ List.range 4, PhaseAt 32 (72+i) := by decide +kernel

theorem phase_32_76 : ∀ i ∈ List.range 4, PhaseAt 32 (76+i) := by decide +kernel

theorem phase_32_80 : ∀ i ∈ List.range 4, PhaseAt 32 (80+i) := by decide +kernel

theorem phase_32_84 : ∀ i ∈ List.range 4, PhaseAt 32 (84+i) := by decide +kernel

theorem phase_32_88 : ∀ i ∈ List.range 4, PhaseAt 32 (88+i) := by decide +kernel

theorem phase_32_92 : ∀ i ∈ List.range 4, PhaseAt 32 (92+i) := by decide +kernel

theorem phase_32_96 : ∀ i ∈ List.range 4, PhaseAt 32 (96+i) := by decide +kernel

theorem phase_32_100 : ∀ i ∈ List.range 4, PhaseAt 32 (100+i) := by decide +kernel

theorem phase_32_104 : ∀ i ∈ List.range 4, PhaseAt 32 (104+i) := by decide +kernel

theorem phase_32_108 : ∀ i ∈ List.range 4, PhaseAt 32 (108+i) := by decide +kernel

theorem phase_32_112 : ∀ i ∈ List.range 4, PhaseAt 32 (112+i) := by decide +kernel

theorem phase_32_116 : ∀ i ∈ List.range 2, PhaseAt 32 (116+i) := by decide +kernel

theorem phase_32 (v : ℕ) (hv : v ∈ List.range 118) : PhaseAt 32 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 32 v)
  have h := (join 0 60 58 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_32_0 (join 4 4 4 phase_32_4 phase_32_8)) (join 12 8 8 (join 12 4 4 phase_32_12 phase_32_16) (join 20 4 4 phase_32_20 phase_32_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_32_28 phase_32_32) (join 36 4 4 phase_32_36 phase_32_40)) (join 44 8 8 (join 44 4 4 phase_32_44 phase_32_48) (join 52 4 4 phase_32_52 phase_32_56)))) (join 60 28 30 (join 60 12 16 (join 60 4 8 phase_32_60 (join 64 4 4 phase_32_64 phase_32_68)) (join 72 8 8 (join 72 4 4 phase_32_72 phase_32_76) (join 80 4 4 phase_32_80 phase_32_84))) (join 88 16 14 (join 88 8 8 (join 88 4 4 phase_32_88 phase_32_92) (join 96 4 4 phase_32_96 phase_32_100)) (join 104 8 6 (join 104 4 4 phase_32_104 phase_32_108) (join 112 4 2 phase_32_112 phase_32_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_32_0 : ∀ i ∈ List.range 1, ThresholdAt 32 (0+i) := by decide +kernel

theorem threshold_32_1 : ∀ i ∈ List.range 1, ThresholdAt 32 (1+i) := by decide +kernel

theorem threshold_32_2 : ∀ i ∈ List.range 1, ThresholdAt 32 (2+i) := by decide +kernel

theorem threshold_32_3 : ∀ i ∈ List.range 1, ThresholdAt 32 (3+i) := by decide +kernel

theorem threshold_32_4 : ∀ i ∈ List.range 1, ThresholdAt 32 (4+i) := by decide +kernel

theorem threshold_32_5 : ∀ i ∈ List.range 1, ThresholdAt 32 (5+i) := by decide +kernel

theorem threshold_32_6 : ∀ i ∈ List.range 1, ThresholdAt 32 (6+i) := by decide +kernel

theorem threshold_32_7 : ∀ i ∈ List.range 1, ThresholdAt 32 (7+i) := by decide +kernel

theorem threshold_32_8 : ∀ i ∈ List.range 1, ThresholdAt 32 (8+i) := by decide +kernel

theorem threshold_32_9 : ∀ i ∈ List.range 1, ThresholdAt 32 (9+i) := by decide +kernel

theorem threshold_32_10 : ∀ i ∈ List.range 1, ThresholdAt 32 (10+i) := by decide +kernel

theorem threshold_32_11 : ∀ i ∈ List.range 1, ThresholdAt 32 (11+i) := by decide +kernel

theorem threshold_32_12 : ∀ i ∈ List.range 1, ThresholdAt 32 (12+i) := by decide +kernel

theorem threshold_32_13 : ∀ i ∈ List.range 1, ThresholdAt 32 (13+i) := by decide +kernel

theorem threshold_32_14 : ∀ i ∈ List.range 1, ThresholdAt 32 (14+i) := by decide +kernel

theorem threshold_32_15 : ∀ i ∈ List.range 1, ThresholdAt 32 (15+i) := by decide +kernel

theorem threshold_32_16 : ∀ i ∈ List.range 1, ThresholdAt 32 (16+i) := by decide +kernel

theorem threshold_32_17 : ∀ i ∈ List.range 1, ThresholdAt 32 (17+i) := by decide +kernel

theorem threshold_32_18 : ∀ i ∈ List.range 1, ThresholdAt 32 (18+i) := by decide +kernel

theorem threshold_32_19 : ∀ i ∈ List.range 1, ThresholdAt 32 (19+i) := by decide +kernel

theorem threshold_32_20 : ∀ i ∈ List.range 1, ThresholdAt 32 (20+i) := by decide +kernel

theorem threshold_32_21 : ∀ i ∈ List.range 1, ThresholdAt 32 (21+i) := by decide +kernel

theorem threshold_32_22 : ∀ i ∈ List.range 1, ThresholdAt 32 (22+i) := by decide +kernel

theorem threshold_32_23 : ∀ i ∈ List.range 1, ThresholdAt 32 (23+i) := by decide +kernel

theorem threshold_32_24 : ∀ i ∈ List.range 1, ThresholdAt 32 (24+i) := by decide +kernel

theorem threshold_32_25 : ∀ i ∈ List.range 1, ThresholdAt 32 (25+i) := by decide +kernel

theorem threshold_32_26 : ∀ i ∈ List.range 1, ThresholdAt 32 (26+i) := by decide +kernel

theorem threshold_32_27 : ∀ i ∈ List.range 1, ThresholdAt 32 (27+i) := by decide +kernel

theorem threshold_32_28 : ∀ i ∈ List.range 1, ThresholdAt 32 (28+i) := by decide +kernel

theorem threshold_32_29 : ∀ i ∈ List.range 1, ThresholdAt 32 (29+i) := by decide +kernel

theorem threshold_32_30 : ∀ i ∈ List.range 1, ThresholdAt 32 (30+i) := by decide +kernel

theorem threshold_32_31 : ∀ i ∈ List.range 1, ThresholdAt 32 (31+i) := by decide +kernel

theorem threshold_32_32 : ∀ i ∈ List.range 1, ThresholdAt 32 (32+i) := by decide +kernel

theorem threshold_32_33 : ∀ i ∈ List.range 1, ThresholdAt 32 (33+i) := by decide +kernel

theorem threshold_32_34 : ∀ i ∈ List.range 1, ThresholdAt 32 (34+i) := by decide +kernel

theorem threshold_32_35 : ∀ i ∈ List.range 1, ThresholdAt 32 (35+i) := by decide +kernel

theorem threshold_32_36 : ∀ i ∈ List.range 1, ThresholdAt 32 (36+i) := by decide +kernel

theorem threshold_32_37 : ∀ i ∈ List.range 1, ThresholdAt 32 (37+i) := by decide +kernel

theorem threshold_32_38 : ∀ i ∈ List.range 1, ThresholdAt 32 (38+i) := by decide +kernel

theorem threshold_32_39 : ∀ i ∈ List.range 1, ThresholdAt 32 (39+i) := by decide +kernel

theorem threshold_32_40 : ∀ i ∈ List.range 1, ThresholdAt 32 (40+i) := by decide +kernel

theorem threshold_32_41 : ∀ i ∈ List.range 1, ThresholdAt 32 (41+i) := by decide +kernel

theorem threshold_32_42 : ∀ i ∈ List.range 1, ThresholdAt 32 (42+i) := by decide +kernel

theorem threshold_32_43 : ∀ i ∈ List.range 1, ThresholdAt 32 (43+i) := by decide +kernel

theorem threshold_32_44 : ∀ i ∈ List.range 1, ThresholdAt 32 (44+i) := by decide +kernel

theorem threshold_32_45 : ∀ i ∈ List.range 1, ThresholdAt 32 (45+i) := by decide +kernel

theorem threshold_32_46 : ∀ i ∈ List.range 1, ThresholdAt 32 (46+i) := by decide +kernel

theorem threshold_32_47 : ∀ i ∈ List.range 1, ThresholdAt 32 (47+i) := by decide +kernel

theorem threshold_32_48 : ∀ i ∈ List.range 1, ThresholdAt 32 (48+i) := by decide +kernel

theorem threshold_32_49 : ∀ i ∈ List.range 1, ThresholdAt 32 (49+i) := by decide +kernel

theorem threshold_32_50 : ∀ i ∈ List.range 1, ThresholdAt 32 (50+i) := by decide +kernel

theorem threshold_32_51 : ∀ i ∈ List.range 1, ThresholdAt 32 (51+i) := by decide +kernel

theorem threshold_32_52 : ∀ i ∈ List.range 1, ThresholdAt 32 (52+i) := by decide +kernel

theorem threshold_32_53 : ∀ i ∈ List.range 1, ThresholdAt 32 (53+i) := by decide +kernel

theorem threshold_32_54 : ∀ i ∈ List.range 1, ThresholdAt 32 (54+i) := by decide +kernel

theorem threshold_32_55 : ∀ i ∈ List.range 1, ThresholdAt 32 (55+i) := by decide +kernel

theorem threshold_32_56 : ∀ i ∈ List.range 1, ThresholdAt 32 (56+i) := by decide +kernel

theorem threshold_32_57 : ∀ i ∈ List.range 1, ThresholdAt 32 (57+i) := by decide +kernel

theorem threshold_32_58 : ∀ i ∈ List.range 1, ThresholdAt 32 (58+i) := by decide +kernel

theorem threshold_32_59 : ∀ i ∈ List.range 1, ThresholdAt 32 (59+i) := by decide +kernel

theorem threshold_32_60 : ∀ i ∈ List.range 1, ThresholdAt 32 (60+i) := by decide +kernel

theorem threshold_32_61 : ∀ i ∈ List.range 1, ThresholdAt 32 (61+i) := by decide +kernel

theorem threshold_32_62 : ∀ i ∈ List.range 1, ThresholdAt 32 (62+i) := by decide +kernel

theorem threshold_32_63 : ∀ i ∈ List.range 1, ThresholdAt 32 (63+i) := by decide +kernel

theorem threshold_32_64 : ∀ i ∈ List.range 1, ThresholdAt 32 (64+i) := by decide +kernel

theorem threshold_32_65 : ∀ i ∈ List.range 1, ThresholdAt 32 (65+i) := by decide +kernel

theorem threshold_32_66 : ∀ i ∈ List.range 1, ThresholdAt 32 (66+i) := by decide +kernel

theorem threshold_32_67 : ∀ i ∈ List.range 1, ThresholdAt 32 (67+i) := by decide +kernel

theorem threshold_32_68 : ∀ i ∈ List.range 1, ThresholdAt 32 (68+i) := by decide +kernel

theorem threshold_32_69 : ∀ i ∈ List.range 1, ThresholdAt 32 (69+i) := by decide +kernel

theorem threshold_32_70 : ∀ i ∈ List.range 1, ThresholdAt 32 (70+i) := by decide +kernel

theorem threshold_32_71 : ∀ i ∈ List.range 1, ThresholdAt 32 (71+i) := by decide +kernel

theorem threshold_32_72 : ∀ i ∈ List.range 1, ThresholdAt 32 (72+i) := by decide +kernel

theorem threshold_32_73 : ∀ i ∈ List.range 1, ThresholdAt 32 (73+i) := by decide +kernel

theorem threshold_32_74 : ∀ i ∈ List.range 1, ThresholdAt 32 (74+i) := by decide +kernel

theorem threshold_32_75 : ∀ i ∈ List.range 1, ThresholdAt 32 (75+i) := by decide +kernel

theorem threshold_32_76 : ∀ i ∈ List.range 1, ThresholdAt 32 (76+i) := by decide +kernel

theorem threshold_32_77 : ∀ i ∈ List.range 1, ThresholdAt 32 (77+i) := by decide +kernel

theorem threshold_32_78 : ∀ i ∈ List.range 1, ThresholdAt 32 (78+i) := by decide +kernel

theorem threshold_32_79 : ∀ i ∈ List.range 1, ThresholdAt 32 (79+i) := by decide +kernel

theorem threshold_32_80 : ∀ i ∈ List.range 1, ThresholdAt 32 (80+i) := by decide +kernel

theorem threshold_32_81 : ∀ i ∈ List.range 1, ThresholdAt 32 (81+i) := by decide +kernel

theorem threshold_32_82 : ∀ i ∈ List.range 1, ThresholdAt 32 (82+i) := by decide +kernel

theorem threshold_32_83 : ∀ i ∈ List.range 1, ThresholdAt 32 (83+i) := by decide +kernel

theorem threshold_32_84 : ∀ i ∈ List.range 1, ThresholdAt 32 (84+i) := by decide +kernel

theorem threshold_32_85 : ∀ i ∈ List.range 1, ThresholdAt 32 (85+i) := by decide +kernel

theorem threshold_32_86 : ∀ i ∈ List.range 1, ThresholdAt 32 (86+i) := by decide +kernel

theorem threshold_32_87 : ∀ i ∈ List.range 1, ThresholdAt 32 (87+i) := by decide +kernel

theorem threshold_32_88 : ∀ i ∈ List.range 1, ThresholdAt 32 (88+i) := by decide +kernel

theorem threshold_32_89 : ∀ i ∈ List.range 1, ThresholdAt 32 (89+i) := by decide +kernel

theorem threshold_32_90 : ∀ i ∈ List.range 1, ThresholdAt 32 (90+i) := by decide +kernel

theorem threshold_32_91 : ∀ i ∈ List.range 1, ThresholdAt 32 (91+i) := by decide +kernel

theorem threshold_32_92 : ∀ i ∈ List.range 1, ThresholdAt 32 (92+i) := by decide +kernel

theorem threshold_32_93 : ∀ i ∈ List.range 1, ThresholdAt 32 (93+i) := by decide +kernel

theorem threshold_32_94 : ∀ i ∈ List.range 1, ThresholdAt 32 (94+i) := by decide +kernel

theorem threshold_32_95 : ∀ i ∈ List.range 1, ThresholdAt 32 (95+i) := by decide +kernel

theorem threshold_32_96 : ∀ i ∈ List.range 1, ThresholdAt 32 (96+i) := by decide +kernel

theorem threshold_32_97 : ∀ i ∈ List.range 1, ThresholdAt 32 (97+i) := by decide +kernel

theorem threshold_32_98 : ∀ i ∈ List.range 1, ThresholdAt 32 (98+i) := by decide +kernel

theorem threshold_32_99 : ∀ i ∈ List.range 1, ThresholdAt 32 (99+i) := by decide +kernel

theorem threshold_32_100 : ∀ i ∈ List.range 1, ThresholdAt 32 (100+i) := by decide +kernel

theorem threshold_32_101 : ∀ i ∈ List.range 1, ThresholdAt 32 (101+i) := by decide +kernel

theorem threshold_32_102 : ∀ i ∈ List.range 1, ThresholdAt 32 (102+i) := by decide +kernel

theorem threshold_32_103 : ∀ i ∈ List.range 1, ThresholdAt 32 (103+i) := by decide +kernel

theorem threshold_32_104 : ∀ i ∈ List.range 1, ThresholdAt 32 (104+i) := by decide +kernel

theorem threshold_32_105 : ∀ i ∈ List.range 1, ThresholdAt 32 (105+i) := by decide +kernel

theorem threshold_32_106 : ∀ i ∈ List.range 1, ThresholdAt 32 (106+i) := by decide +kernel

theorem threshold_32_107 : ∀ i ∈ List.range 1, ThresholdAt 32 (107+i) := by decide +kernel

theorem threshold_32_108 : ∀ i ∈ List.range 1, ThresholdAt 32 (108+i) := by decide +kernel

theorem threshold_32_109 : ∀ i ∈ List.range 1, ThresholdAt 32 (109+i) := by decide +kernel

theorem threshold_32_110 : ∀ i ∈ List.range 1, ThresholdAt 32 (110+i) := by decide +kernel

theorem threshold_32_111 : ∀ i ∈ List.range 1, ThresholdAt 32 (111+i) := by decide +kernel

theorem threshold_32_112 : ∀ i ∈ List.range 1, ThresholdAt 32 (112+i) := by decide +kernel

theorem threshold_32_113 : ∀ i ∈ List.range 1, ThresholdAt 32 (113+i) := by decide +kernel

theorem threshold_32_114 : ∀ i ∈ List.range 1, ThresholdAt 32 (114+i) := by decide +kernel

theorem threshold_32_115 : ∀ i ∈ List.range 1, ThresholdAt 32 (115+i) := by decide +kernel

theorem threshold_32_116 : ∀ i ∈ List.range 1, ThresholdAt 32 (116+i) := by decide +kernel

theorem threshold_32_117 : ∀ i ∈ List.range 1, ThresholdAt 32 (117+i) := by decide +kernel

theorem threshold_32 (v : ℕ) (hv : v ∈ List.range 118) : ThresholdAt 32 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 32 v)
  have h := (join 0 59 59 (join 0 29 30 (join 0 14 15 (join 0 7 7 (join 0 3 4 (join 0 1 2 threshold_32_0 (join 1 1 1 threshold_32_1 threshold_32_2)) (join 3 2 2 (join 3 1 1 threshold_32_3 threshold_32_4) (join 5 1 1 threshold_32_5 threshold_32_6))) (join 7 3 4 (join 7 1 2 threshold_32_7 (join 8 1 1 threshold_32_8 threshold_32_9)) (join 10 2 2 (join 10 1 1 threshold_32_10 threshold_32_11) (join 12 1 1 threshold_32_12 threshold_32_13)))) (join 14 7 8 (join 14 3 4 (join 14 1 2 threshold_32_14 (join 15 1 1 threshold_32_15 threshold_32_16)) (join 17 2 2 (join 17 1 1 threshold_32_17 threshold_32_18) (join 19 1 1 threshold_32_19 threshold_32_20))) (join 21 4 4 (join 21 2 2 (join 21 1 1 threshold_32_21 threshold_32_22) (join 23 1 1 threshold_32_23 threshold_32_24)) (join 25 2 2 (join 25 1 1 threshold_32_25 threshold_32_26) (join 27 1 1 threshold_32_27 threshold_32_28))))) (join 29 15 15 (join 29 7 8 (join 29 3 4 (join 29 1 2 threshold_32_29 (join 30 1 1 threshold_32_30 threshold_32_31)) (join 32 2 2 (join 32 1 1 threshold_32_32 threshold_32_33) (join 34 1 1 threshold_32_34 threshold_32_35))) (join 36 4 4 (join 36 2 2 (join 36 1 1 threshold_32_36 threshold_32_37) (join 38 1 1 threshold_32_38 threshold_32_39)) (join 40 2 2 (join 40 1 1 threshold_32_40 threshold_32_41) (join 42 1 1 threshold_32_42 threshold_32_43)))) (join 44 7 8 (join 44 3 4 (join 44 1 2 threshold_32_44 (join 45 1 1 threshold_32_45 threshold_32_46)) (join 47 2 2 (join 47 1 1 threshold_32_47 threshold_32_48) (join 49 1 1 threshold_32_49 threshold_32_50))) (join 51 4 4 (join 51 2 2 (join 51 1 1 threshold_32_51 threshold_32_52) (join 53 1 1 threshold_32_53 threshold_32_54)) (join 55 2 2 (join 55 1 1 threshold_32_55 threshold_32_56) (join 57 1 1 threshold_32_57 threshold_32_58)))))) (join 59 29 30 (join 59 14 15 (join 59 7 7 (join 59 3 4 (join 59 1 2 threshold_32_59 (join 60 1 1 threshold_32_60 threshold_32_61)) (join 62 2 2 (join 62 1 1 threshold_32_62 threshold_32_63) (join 64 1 1 threshold_32_64 threshold_32_65))) (join 66 3 4 (join 66 1 2 threshold_32_66 (join 67 1 1 threshold_32_67 threshold_32_68)) (join 69 2 2 (join 69 1 1 threshold_32_69 threshold_32_70) (join 71 1 1 threshold_32_71 threshold_32_72)))) (join 73 7 8 (join 73 3 4 (join 73 1 2 threshold_32_73 (join 74 1 1 threshold_32_74 threshold_32_75)) (join 76 2 2 (join 76 1 1 threshold_32_76 threshold_32_77) (join 78 1 1 threshold_32_78 threshold_32_79))) (join 80 4 4 (join 80 2 2 (join 80 1 1 threshold_32_80 threshold_32_81) (join 82 1 1 threshold_32_82 threshold_32_83)) (join 84 2 2 (join 84 1 1 threshold_32_84 threshold_32_85) (join 86 1 1 threshold_32_86 threshold_32_87))))) (join 88 15 15 (join 88 7 8 (join 88 3 4 (join 88 1 2 threshold_32_88 (join 89 1 1 threshold_32_89 threshold_32_90)) (join 91 2 2 (join 91 1 1 threshold_32_91 threshold_32_92) (join 93 1 1 threshold_32_93 threshold_32_94))) (join 95 4 4 (join 95 2 2 (join 95 1 1 threshold_32_95 threshold_32_96) (join 97 1 1 threshold_32_97 threshold_32_98)) (join 99 2 2 (join 99 1 1 threshold_32_99 threshold_32_100) (join 101 1 1 threshold_32_101 threshold_32_102)))) (join 103 7 8 (join 103 3 4 (join 103 1 2 threshold_32_103 (join 104 1 1 threshold_32_104 threshold_32_105)) (join 106 2 2 (join 106 1 1 threshold_32_106 threshold_32_107) (join 108 1 1 threshold_32_108 threshold_32_109))) (join 110 4 4 (join 110 2 2 (join 110 1 1 threshold_32_110 threshold_32_111) (join 112 1 1 threshold_32_112 threshold_32_113)) (join 114 2 2 (join 114 1 1 threshold_32_114 threshold_32_115) (join 116 1 1 threshold_32_116 threshold_32_117)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_32_0 : ∀ i ∈ List.range 4, LedgerAt 32 (0+i) := by decide +kernel

theorem ledger_32_4 : ∀ i ∈ List.range 4, LedgerAt 32 (4+i) := by decide +kernel

theorem ledger_32_8 : ∀ i ∈ List.range 4, LedgerAt 32 (8+i) := by decide +kernel

theorem ledger_32_12 : ∀ i ∈ List.range 4, LedgerAt 32 (12+i) := by decide +kernel

theorem ledger_32_16 : ∀ i ∈ List.range 4, LedgerAt 32 (16+i) := by decide +kernel

theorem ledger_32_20 : ∀ i ∈ List.range 4, LedgerAt 32 (20+i) := by decide +kernel

theorem ledger_32_24 : ∀ i ∈ List.range 4, LedgerAt 32 (24+i) := by decide +kernel

theorem ledger_32_28 : ∀ i ∈ List.range 4, LedgerAt 32 (28+i) := by decide +kernel

theorem ledger_32_32 : ∀ i ∈ List.range 4, LedgerAt 32 (32+i) := by decide +kernel

theorem ledger_32_36 : ∀ i ∈ List.range 4, LedgerAt 32 (36+i) := by decide +kernel

theorem ledger_32_40 : ∀ i ∈ List.range 4, LedgerAt 32 (40+i) := by decide +kernel

theorem ledger_32_44 : ∀ i ∈ List.range 4, LedgerAt 32 (44+i) := by decide +kernel

theorem ledger_32_48 : ∀ i ∈ List.range 4, LedgerAt 32 (48+i) := by decide +kernel

theorem ledger_32_52 : ∀ i ∈ List.range 4, LedgerAt 32 (52+i) := by decide +kernel

theorem ledger_32_56 : ∀ i ∈ List.range 4, LedgerAt 32 (56+i) := by decide +kernel

theorem ledger_32_60 : ∀ i ∈ List.range 4, LedgerAt 32 (60+i) := by decide +kernel

theorem ledger_32_64 : ∀ i ∈ List.range 4, LedgerAt 32 (64+i) := by decide +kernel

theorem ledger_32_68 : ∀ i ∈ List.range 4, LedgerAt 32 (68+i) := by decide +kernel

theorem ledger_32_72 : ∀ i ∈ List.range 4, LedgerAt 32 (72+i) := by decide +kernel

theorem ledger_32_76 : ∀ i ∈ List.range 4, LedgerAt 32 (76+i) := by decide +kernel

theorem ledger_32_80 : ∀ i ∈ List.range 4, LedgerAt 32 (80+i) := by decide +kernel

theorem ledger_32_84 : ∀ i ∈ List.range 4, LedgerAt 32 (84+i) := by decide +kernel

theorem ledger_32_88 : ∀ i ∈ List.range 4, LedgerAt 32 (88+i) := by decide +kernel

theorem ledger_32_92 : ∀ i ∈ List.range 4, LedgerAt 32 (92+i) := by decide +kernel

theorem ledger_32_96 : ∀ i ∈ List.range 4, LedgerAt 32 (96+i) := by decide +kernel

theorem ledger_32_100 : ∀ i ∈ List.range 4, LedgerAt 32 (100+i) := by decide +kernel

theorem ledger_32_104 : ∀ i ∈ List.range 4, LedgerAt 32 (104+i) := by decide +kernel

theorem ledger_32_108 : ∀ i ∈ List.range 4, LedgerAt 32 (108+i) := by decide +kernel

theorem ledger_32_112 : ∀ i ∈ List.range 4, LedgerAt 32 (112+i) := by decide +kernel

theorem ledger_32_116 : ∀ i ∈ List.range 2, LedgerAt 32 (116+i) := by decide +kernel

theorem ledger_32 (v : ℕ) (hv : v ∈ List.range 118) : LedgerAt 32 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 32 v)
  have h := (join 0 60 58 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_32_0 (join 4 4 4 ledger_32_4 ledger_32_8)) (join 12 8 8 (join 12 4 4 ledger_32_12 ledger_32_16) (join 20 4 4 ledger_32_20 ledger_32_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_32_28 ledger_32_32) (join 36 4 4 ledger_32_36 ledger_32_40)) (join 44 8 8 (join 44 4 4 ledger_32_44 ledger_32_48) (join 52 4 4 ledger_32_52 ledger_32_56)))) (join 60 28 30 (join 60 12 16 (join 60 4 8 ledger_32_60 (join 64 4 4 ledger_32_64 ledger_32_68)) (join 72 8 8 (join 72 4 4 ledger_32_72 ledger_32_76) (join 80 4 4 ledger_32_80 ledger_32_84))) (join 88 16 14 (join 88 8 8 (join 88 4 4 ledger_32_88 ledger_32_92) (join 96 4 4 ledger_32_96 ledger_32_100)) (join 104 8 6 (join 104 4 4 ledger_32_104 ledger_32_108) (join 112 4 2 ledger_32_112 ledger_32_116)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
