import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_30_0 : ∀ i ∈ List.range 4, SingleAt 30 (0+i) := by decide +kernel

theorem single_30_4 : ∀ i ∈ List.range 4, SingleAt 30 (4+i) := by decide +kernel

theorem single_30_8 : ∀ i ∈ List.range 4, SingleAt 30 (8+i) := by decide +kernel

theorem single_30_12 : ∀ i ∈ List.range 4, SingleAt 30 (12+i) := by decide +kernel

theorem single_30_16 : ∀ i ∈ List.range 4, SingleAt 30 (16+i) := by decide +kernel

theorem single_30_20 : ∀ i ∈ List.range 4, SingleAt 30 (20+i) := by decide +kernel

theorem single_30_24 : ∀ i ∈ List.range 4, SingleAt 30 (24+i) := by decide +kernel

theorem single_30_28 : ∀ i ∈ List.range 4, SingleAt 30 (28+i) := by decide +kernel

theorem single_30_32 : ∀ i ∈ List.range 4, SingleAt 30 (32+i) := by decide +kernel

theorem single_30_36 : ∀ i ∈ List.range 4, SingleAt 30 (36+i) := by decide +kernel

theorem single_30_40 : ∀ i ∈ List.range 4, SingleAt 30 (40+i) := by decide +kernel

theorem single_30_44 : ∀ i ∈ List.range 4, SingleAt 30 (44+i) := by decide +kernel

theorem single_30_48 : ∀ i ∈ List.range 4, SingleAt 30 (48+i) := by decide +kernel

theorem single_30_52 : ∀ i ∈ List.range 4, SingleAt 30 (52+i) := by decide +kernel

theorem single_30_56 : ∀ i ∈ List.range 4, SingleAt 30 (56+i) := by decide +kernel

theorem single_30_60 : ∀ i ∈ List.range 4, SingleAt 30 (60+i) := by decide +kernel

theorem single_30_64 : ∀ i ∈ List.range 4, SingleAt 30 (64+i) := by decide +kernel

theorem single_30_68 : ∀ i ∈ List.range 4, SingleAt 30 (68+i) := by decide +kernel

theorem single_30_72 : ∀ i ∈ List.range 4, SingleAt 30 (72+i) := by decide +kernel

theorem single_30_76 : ∀ i ∈ List.range 4, SingleAt 30 (76+i) := by decide +kernel

theorem single_30_80 : ∀ i ∈ List.range 4, SingleAt 30 (80+i) := by decide +kernel

theorem single_30_84 : ∀ i ∈ List.range 4, SingleAt 30 (84+i) := by decide +kernel

theorem single_30_88 : ∀ i ∈ List.range 4, SingleAt 30 (88+i) := by decide +kernel

theorem single_30_92 : ∀ i ∈ List.range 4, SingleAt 30 (92+i) := by decide +kernel

theorem single_30_96 : ∀ i ∈ List.range 4, SingleAt 30 (96+i) := by decide +kernel

theorem single_30_100 : ∀ i ∈ List.range 4, SingleAt 30 (100+i) := by decide +kernel

theorem single_30_104 : ∀ i ∈ List.range 4, SingleAt 30 (104+i) := by decide +kernel

theorem single_30_108 : ∀ i ∈ List.range 4, SingleAt 30 (108+i) := by decide +kernel

theorem single_30_112 : ∀ i ∈ List.range 4, SingleAt 30 (112+i) := by decide +kernel

theorem single_30_116 : ∀ i ∈ List.range 4, SingleAt 30 (116+i) := by decide +kernel

theorem single_30 (v : ℕ) (hv : v ∈ List.range 120) : SingleAt 30 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 30 v)
  have h := (join 0 60 60 (join 0 28 32 (join 0 12 16 (join 0 4 8 single_30_0 (join 4 4 4 single_30_4 single_30_8)) (join 12 8 8 (join 12 4 4 single_30_12 single_30_16) (join 20 4 4 single_30_20 single_30_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 single_30_28 single_30_32) (join 36 4 4 single_30_36 single_30_40)) (join 44 8 8 (join 44 4 4 single_30_44 single_30_48) (join 52 4 4 single_30_52 single_30_56)))) (join 60 28 32 (join 60 12 16 (join 60 4 8 single_30_60 (join 64 4 4 single_30_64 single_30_68)) (join 72 8 8 (join 72 4 4 single_30_72 single_30_76) (join 80 4 4 single_30_80 single_30_84))) (join 88 16 16 (join 88 8 8 (join 88 4 4 single_30_88 single_30_92) (join 96 4 4 single_30_96 single_30_100)) (join 104 8 8 (join 104 4 4 single_30_104 single_30_108) (join 112 4 4 single_30_112 single_30_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_30_0 : ∀ i ∈ List.range 4, PhaseAt 30 (0+i) := by decide +kernel

theorem phase_30_4 : ∀ i ∈ List.range 4, PhaseAt 30 (4+i) := by decide +kernel

theorem phase_30_8 : ∀ i ∈ List.range 4, PhaseAt 30 (8+i) := by decide +kernel

theorem phase_30_12 : ∀ i ∈ List.range 4, PhaseAt 30 (12+i) := by decide +kernel

theorem phase_30_16 : ∀ i ∈ List.range 4, PhaseAt 30 (16+i) := by decide +kernel

theorem phase_30_20 : ∀ i ∈ List.range 4, PhaseAt 30 (20+i) := by decide +kernel

theorem phase_30_24 : ∀ i ∈ List.range 4, PhaseAt 30 (24+i) := by decide +kernel

theorem phase_30_28 : ∀ i ∈ List.range 4, PhaseAt 30 (28+i) := by decide +kernel

theorem phase_30_32 : ∀ i ∈ List.range 4, PhaseAt 30 (32+i) := by decide +kernel

theorem phase_30_36 : ∀ i ∈ List.range 4, PhaseAt 30 (36+i) := by decide +kernel

theorem phase_30_40 : ∀ i ∈ List.range 4, PhaseAt 30 (40+i) := by decide +kernel

theorem phase_30_44 : ∀ i ∈ List.range 4, PhaseAt 30 (44+i) := by decide +kernel

theorem phase_30_48 : ∀ i ∈ List.range 4, PhaseAt 30 (48+i) := by decide +kernel

theorem phase_30_52 : ∀ i ∈ List.range 4, PhaseAt 30 (52+i) := by decide +kernel

theorem phase_30_56 : ∀ i ∈ List.range 4, PhaseAt 30 (56+i) := by decide +kernel

theorem phase_30_60 : ∀ i ∈ List.range 4, PhaseAt 30 (60+i) := by decide +kernel

theorem phase_30_64 : ∀ i ∈ List.range 4, PhaseAt 30 (64+i) := by decide +kernel

theorem phase_30_68 : ∀ i ∈ List.range 4, PhaseAt 30 (68+i) := by decide +kernel

theorem phase_30_72 : ∀ i ∈ List.range 4, PhaseAt 30 (72+i) := by decide +kernel

theorem phase_30_76 : ∀ i ∈ List.range 4, PhaseAt 30 (76+i) := by decide +kernel

theorem phase_30_80 : ∀ i ∈ List.range 4, PhaseAt 30 (80+i) := by decide +kernel

theorem phase_30_84 : ∀ i ∈ List.range 4, PhaseAt 30 (84+i) := by decide +kernel

theorem phase_30_88 : ∀ i ∈ List.range 4, PhaseAt 30 (88+i) := by decide +kernel

theorem phase_30_92 : ∀ i ∈ List.range 4, PhaseAt 30 (92+i) := by decide +kernel

theorem phase_30_96 : ∀ i ∈ List.range 4, PhaseAt 30 (96+i) := by decide +kernel

theorem phase_30_100 : ∀ i ∈ List.range 4, PhaseAt 30 (100+i) := by decide +kernel

theorem phase_30_104 : ∀ i ∈ List.range 4, PhaseAt 30 (104+i) := by decide +kernel

theorem phase_30_108 : ∀ i ∈ List.range 4, PhaseAt 30 (108+i) := by decide +kernel

theorem phase_30_112 : ∀ i ∈ List.range 4, PhaseAt 30 (112+i) := by decide +kernel

theorem phase_30_116 : ∀ i ∈ List.range 4, PhaseAt 30 (116+i) := by decide +kernel

theorem phase_30 (v : ℕ) (hv : v ∈ List.range 120) : PhaseAt 30 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 30 v)
  have h := (join 0 60 60 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_30_0 (join 4 4 4 phase_30_4 phase_30_8)) (join 12 8 8 (join 12 4 4 phase_30_12 phase_30_16) (join 20 4 4 phase_30_20 phase_30_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_30_28 phase_30_32) (join 36 4 4 phase_30_36 phase_30_40)) (join 44 8 8 (join 44 4 4 phase_30_44 phase_30_48) (join 52 4 4 phase_30_52 phase_30_56)))) (join 60 28 32 (join 60 12 16 (join 60 4 8 phase_30_60 (join 64 4 4 phase_30_64 phase_30_68)) (join 72 8 8 (join 72 4 4 phase_30_72 phase_30_76) (join 80 4 4 phase_30_80 phase_30_84))) (join 88 16 16 (join 88 8 8 (join 88 4 4 phase_30_88 phase_30_92) (join 96 4 4 phase_30_96 phase_30_100)) (join 104 8 8 (join 104 4 4 phase_30_104 phase_30_108) (join 112 4 4 phase_30_112 phase_30_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_30_0 : ∀ i ∈ List.range 1, ThresholdAt 30 (0+i) := by decide +kernel

theorem threshold_30_1 : ∀ i ∈ List.range 1, ThresholdAt 30 (1+i) := by decide +kernel

theorem threshold_30_2 : ∀ i ∈ List.range 1, ThresholdAt 30 (2+i) := by decide +kernel

theorem threshold_30_3 : ∀ i ∈ List.range 1, ThresholdAt 30 (3+i) := by decide +kernel

theorem threshold_30_4 : ∀ i ∈ List.range 1, ThresholdAt 30 (4+i) := by decide +kernel

theorem threshold_30_5 : ∀ i ∈ List.range 1, ThresholdAt 30 (5+i) := by decide +kernel

theorem threshold_30_6 : ∀ i ∈ List.range 1, ThresholdAt 30 (6+i) := by decide +kernel

theorem threshold_30_7 : ∀ i ∈ List.range 1, ThresholdAt 30 (7+i) := by decide +kernel

theorem threshold_30_8 : ∀ i ∈ List.range 1, ThresholdAt 30 (8+i) := by decide +kernel

theorem threshold_30_9 : ∀ i ∈ List.range 1, ThresholdAt 30 (9+i) := by decide +kernel

theorem threshold_30_10 : ∀ i ∈ List.range 1, ThresholdAt 30 (10+i) := by decide +kernel

theorem threshold_30_11 : ∀ i ∈ List.range 1, ThresholdAt 30 (11+i) := by decide +kernel

theorem threshold_30_12 : ∀ i ∈ List.range 1, ThresholdAt 30 (12+i) := by decide +kernel

theorem threshold_30_13 : ∀ i ∈ List.range 1, ThresholdAt 30 (13+i) := by decide +kernel

theorem threshold_30_14 : ∀ i ∈ List.range 1, ThresholdAt 30 (14+i) := by decide +kernel

theorem threshold_30_15 : ∀ i ∈ List.range 1, ThresholdAt 30 (15+i) := by decide +kernel

theorem threshold_30_16 : ∀ i ∈ List.range 1, ThresholdAt 30 (16+i) := by decide +kernel

theorem threshold_30_17 : ∀ i ∈ List.range 1, ThresholdAt 30 (17+i) := by decide +kernel

theorem threshold_30_18 : ∀ i ∈ List.range 1, ThresholdAt 30 (18+i) := by decide +kernel

theorem threshold_30_19 : ∀ i ∈ List.range 1, ThresholdAt 30 (19+i) := by decide +kernel

theorem threshold_30_20 : ∀ i ∈ List.range 1, ThresholdAt 30 (20+i) := by decide +kernel

theorem threshold_30_21 : ∀ i ∈ List.range 1, ThresholdAt 30 (21+i) := by decide +kernel

theorem threshold_30_22 : ∀ i ∈ List.range 1, ThresholdAt 30 (22+i) := by decide +kernel

theorem threshold_30_23 : ∀ i ∈ List.range 1, ThresholdAt 30 (23+i) := by decide +kernel

theorem threshold_30_24 : ∀ i ∈ List.range 1, ThresholdAt 30 (24+i) := by decide +kernel

theorem threshold_30_25 : ∀ i ∈ List.range 1, ThresholdAt 30 (25+i) := by decide +kernel

theorem threshold_30_26 : ∀ i ∈ List.range 1, ThresholdAt 30 (26+i) := by decide +kernel

theorem threshold_30_27 : ∀ i ∈ List.range 1, ThresholdAt 30 (27+i) := by decide +kernel

theorem threshold_30_28 : ∀ i ∈ List.range 1, ThresholdAt 30 (28+i) := by decide +kernel

theorem threshold_30_29 : ∀ i ∈ List.range 1, ThresholdAt 30 (29+i) := by decide +kernel

theorem threshold_30_30 : ∀ i ∈ List.range 1, ThresholdAt 30 (30+i) := by decide +kernel

theorem threshold_30_31 : ∀ i ∈ List.range 1, ThresholdAt 30 (31+i) := by decide +kernel

theorem threshold_30_32 : ∀ i ∈ List.range 1, ThresholdAt 30 (32+i) := by decide +kernel

theorem threshold_30_33 : ∀ i ∈ List.range 1, ThresholdAt 30 (33+i) := by decide +kernel

theorem threshold_30_34 : ∀ i ∈ List.range 1, ThresholdAt 30 (34+i) := by decide +kernel

theorem threshold_30_35 : ∀ i ∈ List.range 1, ThresholdAt 30 (35+i) := by decide +kernel

theorem threshold_30_36 : ∀ i ∈ List.range 1, ThresholdAt 30 (36+i) := by decide +kernel

theorem threshold_30_37 : ∀ i ∈ List.range 1, ThresholdAt 30 (37+i) := by decide +kernel

theorem threshold_30_38 : ∀ i ∈ List.range 1, ThresholdAt 30 (38+i) := by decide +kernel

theorem threshold_30_39 : ∀ i ∈ List.range 1, ThresholdAt 30 (39+i) := by decide +kernel

theorem threshold_30_40 : ∀ i ∈ List.range 1, ThresholdAt 30 (40+i) := by decide +kernel

theorem threshold_30_41 : ∀ i ∈ List.range 1, ThresholdAt 30 (41+i) := by decide +kernel

theorem threshold_30_42 : ∀ i ∈ List.range 1, ThresholdAt 30 (42+i) := by decide +kernel

theorem threshold_30_43 : ∀ i ∈ List.range 1, ThresholdAt 30 (43+i) := by decide +kernel

theorem threshold_30_44 : ∀ i ∈ List.range 1, ThresholdAt 30 (44+i) := by decide +kernel

theorem threshold_30_45 : ∀ i ∈ List.range 1, ThresholdAt 30 (45+i) := by decide +kernel

theorem threshold_30_46 : ∀ i ∈ List.range 1, ThresholdAt 30 (46+i) := by decide +kernel

theorem threshold_30_47 : ∀ i ∈ List.range 1, ThresholdAt 30 (47+i) := by decide +kernel

theorem threshold_30_48 : ∀ i ∈ List.range 1, ThresholdAt 30 (48+i) := by decide +kernel

theorem threshold_30_49 : ∀ i ∈ List.range 1, ThresholdAt 30 (49+i) := by decide +kernel

theorem threshold_30_50 : ∀ i ∈ List.range 1, ThresholdAt 30 (50+i) := by decide +kernel

theorem threshold_30_51 : ∀ i ∈ List.range 1, ThresholdAt 30 (51+i) := by decide +kernel

theorem threshold_30_52 : ∀ i ∈ List.range 1, ThresholdAt 30 (52+i) := by decide +kernel

theorem threshold_30_53 : ∀ i ∈ List.range 1, ThresholdAt 30 (53+i) := by decide +kernel

theorem threshold_30_54 : ∀ i ∈ List.range 1, ThresholdAt 30 (54+i) := by decide +kernel

theorem threshold_30_55 : ∀ i ∈ List.range 1, ThresholdAt 30 (55+i) := by decide +kernel

theorem threshold_30_56 : ∀ i ∈ List.range 1, ThresholdAt 30 (56+i) := by decide +kernel

theorem threshold_30_57 : ∀ i ∈ List.range 1, ThresholdAt 30 (57+i) := by decide +kernel

theorem threshold_30_58 : ∀ i ∈ List.range 1, ThresholdAt 30 (58+i) := by decide +kernel

theorem threshold_30_59 : ∀ i ∈ List.range 1, ThresholdAt 30 (59+i) := by decide +kernel

theorem threshold_30_60 : ∀ i ∈ List.range 1, ThresholdAt 30 (60+i) := by decide +kernel

theorem threshold_30_61 : ∀ i ∈ List.range 1, ThresholdAt 30 (61+i) := by decide +kernel

theorem threshold_30_62 : ∀ i ∈ List.range 1, ThresholdAt 30 (62+i) := by decide +kernel

theorem threshold_30_63 : ∀ i ∈ List.range 1, ThresholdAt 30 (63+i) := by decide +kernel

theorem threshold_30_64 : ∀ i ∈ List.range 1, ThresholdAt 30 (64+i) := by decide +kernel

theorem threshold_30_65 : ∀ i ∈ List.range 1, ThresholdAt 30 (65+i) := by decide +kernel

theorem threshold_30_66 : ∀ i ∈ List.range 1, ThresholdAt 30 (66+i) := by decide +kernel

theorem threshold_30_67 : ∀ i ∈ List.range 1, ThresholdAt 30 (67+i) := by decide +kernel

theorem threshold_30_68 : ∀ i ∈ List.range 1, ThresholdAt 30 (68+i) := by decide +kernel

theorem threshold_30_69 : ∀ i ∈ List.range 1, ThresholdAt 30 (69+i) := by decide +kernel

theorem threshold_30_70 : ∀ i ∈ List.range 1, ThresholdAt 30 (70+i) := by decide +kernel

theorem threshold_30_71 : ∀ i ∈ List.range 1, ThresholdAt 30 (71+i) := by decide +kernel

theorem threshold_30_72 : ∀ i ∈ List.range 1, ThresholdAt 30 (72+i) := by decide +kernel

theorem threshold_30_73 : ∀ i ∈ List.range 1, ThresholdAt 30 (73+i) := by decide +kernel

theorem threshold_30_74 : ∀ i ∈ List.range 1, ThresholdAt 30 (74+i) := by decide +kernel

theorem threshold_30_75 : ∀ i ∈ List.range 1, ThresholdAt 30 (75+i) := by decide +kernel

theorem threshold_30_76 : ∀ i ∈ List.range 1, ThresholdAt 30 (76+i) := by decide +kernel

theorem threshold_30_77 : ∀ i ∈ List.range 1, ThresholdAt 30 (77+i) := by decide +kernel

theorem threshold_30_78 : ∀ i ∈ List.range 1, ThresholdAt 30 (78+i) := by decide +kernel

theorem threshold_30_79 : ∀ i ∈ List.range 1, ThresholdAt 30 (79+i) := by decide +kernel

theorem threshold_30_80 : ∀ i ∈ List.range 1, ThresholdAt 30 (80+i) := by decide +kernel

theorem threshold_30_81 : ∀ i ∈ List.range 1, ThresholdAt 30 (81+i) := by decide +kernel

theorem threshold_30_82 : ∀ i ∈ List.range 1, ThresholdAt 30 (82+i) := by decide +kernel

theorem threshold_30_83 : ∀ i ∈ List.range 1, ThresholdAt 30 (83+i) := by decide +kernel

theorem threshold_30_84 : ∀ i ∈ List.range 1, ThresholdAt 30 (84+i) := by decide +kernel

theorem threshold_30_85 : ∀ i ∈ List.range 1, ThresholdAt 30 (85+i) := by decide +kernel

theorem threshold_30_86 : ∀ i ∈ List.range 1, ThresholdAt 30 (86+i) := by decide +kernel

theorem threshold_30_87 : ∀ i ∈ List.range 1, ThresholdAt 30 (87+i) := by decide +kernel

theorem threshold_30_88 : ∀ i ∈ List.range 1, ThresholdAt 30 (88+i) := by decide +kernel

theorem threshold_30_89 : ∀ i ∈ List.range 1, ThresholdAt 30 (89+i) := by decide +kernel

theorem threshold_30_90 : ∀ i ∈ List.range 1, ThresholdAt 30 (90+i) := by decide +kernel

theorem threshold_30_91 : ∀ i ∈ List.range 1, ThresholdAt 30 (91+i) := by decide +kernel

theorem threshold_30_92 : ∀ i ∈ List.range 1, ThresholdAt 30 (92+i) := by decide +kernel

theorem threshold_30_93 : ∀ i ∈ List.range 1, ThresholdAt 30 (93+i) := by decide +kernel

theorem threshold_30_94 : ∀ i ∈ List.range 1, ThresholdAt 30 (94+i) := by decide +kernel

theorem threshold_30_95 : ∀ i ∈ List.range 1, ThresholdAt 30 (95+i) := by decide +kernel

theorem threshold_30_96 : ∀ i ∈ List.range 1, ThresholdAt 30 (96+i) := by decide +kernel

theorem threshold_30_97 : ∀ i ∈ List.range 1, ThresholdAt 30 (97+i) := by decide +kernel

theorem threshold_30_98 : ∀ i ∈ List.range 1, ThresholdAt 30 (98+i) := by decide +kernel

theorem threshold_30_99 : ∀ i ∈ List.range 1, ThresholdAt 30 (99+i) := by decide +kernel

theorem threshold_30_100 : ∀ i ∈ List.range 1, ThresholdAt 30 (100+i) := by decide +kernel

theorem threshold_30_101 : ∀ i ∈ List.range 1, ThresholdAt 30 (101+i) := by decide +kernel

theorem threshold_30_102 : ∀ i ∈ List.range 1, ThresholdAt 30 (102+i) := by decide +kernel

theorem threshold_30_103 : ∀ i ∈ List.range 1, ThresholdAt 30 (103+i) := by decide +kernel

theorem threshold_30_104 : ∀ i ∈ List.range 1, ThresholdAt 30 (104+i) := by decide +kernel

theorem threshold_30_105 : ∀ i ∈ List.range 1, ThresholdAt 30 (105+i) := by decide +kernel

theorem threshold_30_106 : ∀ i ∈ List.range 1, ThresholdAt 30 (106+i) := by decide +kernel

theorem threshold_30_107 : ∀ i ∈ List.range 1, ThresholdAt 30 (107+i) := by decide +kernel

theorem threshold_30_108 : ∀ i ∈ List.range 1, ThresholdAt 30 (108+i) := by decide +kernel

theorem threshold_30_109 : ∀ i ∈ List.range 1, ThresholdAt 30 (109+i) := by decide +kernel

theorem threshold_30_110 : ∀ i ∈ List.range 1, ThresholdAt 30 (110+i) := by decide +kernel

theorem threshold_30_111 : ∀ i ∈ List.range 1, ThresholdAt 30 (111+i) := by decide +kernel

theorem threshold_30_112 : ∀ i ∈ List.range 1, ThresholdAt 30 (112+i) := by decide +kernel

theorem threshold_30_113 : ∀ i ∈ List.range 1, ThresholdAt 30 (113+i) := by decide +kernel

theorem threshold_30_114 : ∀ i ∈ List.range 1, ThresholdAt 30 (114+i) := by decide +kernel

theorem threshold_30_115 : ∀ i ∈ List.range 1, ThresholdAt 30 (115+i) := by decide +kernel

theorem threshold_30_116 : ∀ i ∈ List.range 1, ThresholdAt 30 (116+i) := by decide +kernel

theorem threshold_30_117 : ∀ i ∈ List.range 1, ThresholdAt 30 (117+i) := by decide +kernel

theorem threshold_30_118 : ∀ i ∈ List.range 1, ThresholdAt 30 (118+i) := by decide +kernel

theorem threshold_30_119 : ∀ i ∈ List.range 1, ThresholdAt 30 (119+i) := by decide +kernel

theorem threshold_30 (v : ℕ) (hv : v ∈ List.range 120) : ThresholdAt 30 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 30 v)
  have h := (join 0 60 60 (join 0 30 30 (join 0 15 15 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_30_0 (join 1 1 1 threshold_30_1 threshold_30_2)) (join 3 2 2 (join 3 1 1 threshold_30_3 threshold_30_4) (join 5 1 1 threshold_30_5 threshold_30_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_30_7 threshold_30_8) (join 9 1 1 threshold_30_9 threshold_30_10)) (join 11 2 2 (join 11 1 1 threshold_30_11 threshold_30_12) (join 13 1 1 threshold_30_13 threshold_30_14)))) (join 15 7 8 (join 15 3 4 (join 15 1 2 threshold_30_15 (join 16 1 1 threshold_30_16 threshold_30_17)) (join 18 2 2 (join 18 1 1 threshold_30_18 threshold_30_19) (join 20 1 1 threshold_30_20 threshold_30_21))) (join 22 4 4 (join 22 2 2 (join 22 1 1 threshold_30_22 threshold_30_23) (join 24 1 1 threshold_30_24 threshold_30_25)) (join 26 2 2 (join 26 1 1 threshold_30_26 threshold_30_27) (join 28 1 1 threshold_30_28 threshold_30_29))))) (join 30 15 15 (join 30 7 8 (join 30 3 4 (join 30 1 2 threshold_30_30 (join 31 1 1 threshold_30_31 threshold_30_32)) (join 33 2 2 (join 33 1 1 threshold_30_33 threshold_30_34) (join 35 1 1 threshold_30_35 threshold_30_36))) (join 37 4 4 (join 37 2 2 (join 37 1 1 threshold_30_37 threshold_30_38) (join 39 1 1 threshold_30_39 threshold_30_40)) (join 41 2 2 (join 41 1 1 threshold_30_41 threshold_30_42) (join 43 1 1 threshold_30_43 threshold_30_44)))) (join 45 7 8 (join 45 3 4 (join 45 1 2 threshold_30_45 (join 46 1 1 threshold_30_46 threshold_30_47)) (join 48 2 2 (join 48 1 1 threshold_30_48 threshold_30_49) (join 50 1 1 threshold_30_50 threshold_30_51))) (join 52 4 4 (join 52 2 2 (join 52 1 1 threshold_30_52 threshold_30_53) (join 54 1 1 threshold_30_54 threshold_30_55)) (join 56 2 2 (join 56 1 1 threshold_30_56 threshold_30_57) (join 58 1 1 threshold_30_58 threshold_30_59)))))) (join 60 30 30 (join 60 15 15 (join 60 7 8 (join 60 3 4 (join 60 1 2 threshold_30_60 (join 61 1 1 threshold_30_61 threshold_30_62)) (join 63 2 2 (join 63 1 1 threshold_30_63 threshold_30_64) (join 65 1 1 threshold_30_65 threshold_30_66))) (join 67 4 4 (join 67 2 2 (join 67 1 1 threshold_30_67 threshold_30_68) (join 69 1 1 threshold_30_69 threshold_30_70)) (join 71 2 2 (join 71 1 1 threshold_30_71 threshold_30_72) (join 73 1 1 threshold_30_73 threshold_30_74)))) (join 75 7 8 (join 75 3 4 (join 75 1 2 threshold_30_75 (join 76 1 1 threshold_30_76 threshold_30_77)) (join 78 2 2 (join 78 1 1 threshold_30_78 threshold_30_79) (join 80 1 1 threshold_30_80 threshold_30_81))) (join 82 4 4 (join 82 2 2 (join 82 1 1 threshold_30_82 threshold_30_83) (join 84 1 1 threshold_30_84 threshold_30_85)) (join 86 2 2 (join 86 1 1 threshold_30_86 threshold_30_87) (join 88 1 1 threshold_30_88 threshold_30_89))))) (join 90 15 15 (join 90 7 8 (join 90 3 4 (join 90 1 2 threshold_30_90 (join 91 1 1 threshold_30_91 threshold_30_92)) (join 93 2 2 (join 93 1 1 threshold_30_93 threshold_30_94) (join 95 1 1 threshold_30_95 threshold_30_96))) (join 97 4 4 (join 97 2 2 (join 97 1 1 threshold_30_97 threshold_30_98) (join 99 1 1 threshold_30_99 threshold_30_100)) (join 101 2 2 (join 101 1 1 threshold_30_101 threshold_30_102) (join 103 1 1 threshold_30_103 threshold_30_104)))) (join 105 7 8 (join 105 3 4 (join 105 1 2 threshold_30_105 (join 106 1 1 threshold_30_106 threshold_30_107)) (join 108 2 2 (join 108 1 1 threshold_30_108 threshold_30_109) (join 110 1 1 threshold_30_110 threshold_30_111))) (join 112 4 4 (join 112 2 2 (join 112 1 1 threshold_30_112 threshold_30_113) (join 114 1 1 threshold_30_114 threshold_30_115)) (join 116 2 2 (join 116 1 1 threshold_30_116 threshold_30_117) (join 118 1 1 threshold_30_118 threshold_30_119)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_30_0 : ∀ i ∈ List.range 4, LedgerAt 30 (0+i) := by decide +kernel

theorem ledger_30_4 : ∀ i ∈ List.range 4, LedgerAt 30 (4+i) := by decide +kernel

theorem ledger_30_8 : ∀ i ∈ List.range 4, LedgerAt 30 (8+i) := by decide +kernel

theorem ledger_30_12 : ∀ i ∈ List.range 4, LedgerAt 30 (12+i) := by decide +kernel

theorem ledger_30_16 : ∀ i ∈ List.range 4, LedgerAt 30 (16+i) := by decide +kernel

theorem ledger_30_20 : ∀ i ∈ List.range 4, LedgerAt 30 (20+i) := by decide +kernel

theorem ledger_30_24 : ∀ i ∈ List.range 4, LedgerAt 30 (24+i) := by decide +kernel

theorem ledger_30_28 : ∀ i ∈ List.range 4, LedgerAt 30 (28+i) := by decide +kernel

theorem ledger_30_32 : ∀ i ∈ List.range 4, LedgerAt 30 (32+i) := by decide +kernel

theorem ledger_30_36 : ∀ i ∈ List.range 4, LedgerAt 30 (36+i) := by decide +kernel

theorem ledger_30_40 : ∀ i ∈ List.range 4, LedgerAt 30 (40+i) := by decide +kernel

theorem ledger_30_44 : ∀ i ∈ List.range 4, LedgerAt 30 (44+i) := by decide +kernel

theorem ledger_30_48 : ∀ i ∈ List.range 4, LedgerAt 30 (48+i) := by decide +kernel

theorem ledger_30_52 : ∀ i ∈ List.range 4, LedgerAt 30 (52+i) := by decide +kernel

theorem ledger_30_56 : ∀ i ∈ List.range 4, LedgerAt 30 (56+i) := by decide +kernel

theorem ledger_30_60 : ∀ i ∈ List.range 4, LedgerAt 30 (60+i) := by decide +kernel

theorem ledger_30_64 : ∀ i ∈ List.range 4, LedgerAt 30 (64+i) := by decide +kernel

theorem ledger_30_68 : ∀ i ∈ List.range 4, LedgerAt 30 (68+i) := by decide +kernel

theorem ledger_30_72 : ∀ i ∈ List.range 4, LedgerAt 30 (72+i) := by decide +kernel

theorem ledger_30_76 : ∀ i ∈ List.range 4, LedgerAt 30 (76+i) := by decide +kernel

theorem ledger_30_80 : ∀ i ∈ List.range 4, LedgerAt 30 (80+i) := by decide +kernel

theorem ledger_30_84 : ∀ i ∈ List.range 4, LedgerAt 30 (84+i) := by decide +kernel

theorem ledger_30_88 : ∀ i ∈ List.range 4, LedgerAt 30 (88+i) := by decide +kernel

theorem ledger_30_92 : ∀ i ∈ List.range 4, LedgerAt 30 (92+i) := by decide +kernel

theorem ledger_30_96 : ∀ i ∈ List.range 4, LedgerAt 30 (96+i) := by decide +kernel

theorem ledger_30_100 : ∀ i ∈ List.range 4, LedgerAt 30 (100+i) := by decide +kernel

theorem ledger_30_104 : ∀ i ∈ List.range 4, LedgerAt 30 (104+i) := by decide +kernel

theorem ledger_30_108 : ∀ i ∈ List.range 4, LedgerAt 30 (108+i) := by decide +kernel

theorem ledger_30_112 : ∀ i ∈ List.range 4, LedgerAt 30 (112+i) := by decide +kernel

theorem ledger_30_116 : ∀ i ∈ List.range 4, LedgerAt 30 (116+i) := by decide +kernel

theorem ledger_30 (v : ℕ) (hv : v ∈ List.range 120) : LedgerAt 30 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 30 v)
  have h := (join 0 60 60 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_30_0 (join 4 4 4 ledger_30_4 ledger_30_8)) (join 12 8 8 (join 12 4 4 ledger_30_12 ledger_30_16) (join 20 4 4 ledger_30_20 ledger_30_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_30_28 ledger_30_32) (join 36 4 4 ledger_30_36 ledger_30_40)) (join 44 8 8 (join 44 4 4 ledger_30_44 ledger_30_48) (join 52 4 4 ledger_30_52 ledger_30_56)))) (join 60 28 32 (join 60 12 16 (join 60 4 8 ledger_30_60 (join 64 4 4 ledger_30_64 ledger_30_68)) (join 72 8 8 (join 72 4 4 ledger_30_72 ledger_30_76) (join 80 4 4 ledger_30_80 ledger_30_84))) (join 88 16 16 (join 88 8 8 (join 88 4 4 ledger_30_88 ledger_30_92) (join 96 4 4 ledger_30_96 ledger_30_100)) (join 104 8 8 (join 104 4 4 ledger_30_104 ledger_30_108) (join 112 4 4 ledger_30_112 ledger_30_116)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
