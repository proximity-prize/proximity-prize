import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_28_0 : ∀ i ∈ List.range 4, SingleAt 28 (0+i) := by decide +kernel

theorem single_28_4 : ∀ i ∈ List.range 4, SingleAt 28 (4+i) := by decide +kernel

theorem single_28_8 : ∀ i ∈ List.range 4, SingleAt 28 (8+i) := by decide +kernel

theorem single_28_12 : ∀ i ∈ List.range 4, SingleAt 28 (12+i) := by decide +kernel

theorem single_28_16 : ∀ i ∈ List.range 4, SingleAt 28 (16+i) := by decide +kernel

theorem single_28_20 : ∀ i ∈ List.range 4, SingleAt 28 (20+i) := by decide +kernel

theorem single_28_24 : ∀ i ∈ List.range 4, SingleAt 28 (24+i) := by decide +kernel

theorem single_28_28 : ∀ i ∈ List.range 4, SingleAt 28 (28+i) := by decide +kernel

theorem single_28_32 : ∀ i ∈ List.range 4, SingleAt 28 (32+i) := by decide +kernel

theorem single_28_36 : ∀ i ∈ List.range 4, SingleAt 28 (36+i) := by decide +kernel

theorem single_28_40 : ∀ i ∈ List.range 4, SingleAt 28 (40+i) := by decide +kernel

theorem single_28_44 : ∀ i ∈ List.range 4, SingleAt 28 (44+i) := by decide +kernel

theorem single_28_48 : ∀ i ∈ List.range 4, SingleAt 28 (48+i) := by decide +kernel

theorem single_28_52 : ∀ i ∈ List.range 4, SingleAt 28 (52+i) := by decide +kernel

theorem single_28_56 : ∀ i ∈ List.range 4, SingleAt 28 (56+i) := by decide +kernel

theorem single_28_60 : ∀ i ∈ List.range 4, SingleAt 28 (60+i) := by decide +kernel

theorem single_28_64 : ∀ i ∈ List.range 4, SingleAt 28 (64+i) := by decide +kernel

theorem single_28_68 : ∀ i ∈ List.range 4, SingleAt 28 (68+i) := by decide +kernel

theorem single_28_72 : ∀ i ∈ List.range 4, SingleAt 28 (72+i) := by decide +kernel

theorem single_28_76 : ∀ i ∈ List.range 4, SingleAt 28 (76+i) := by decide +kernel

theorem single_28_80 : ∀ i ∈ List.range 4, SingleAt 28 (80+i) := by decide +kernel

theorem single_28_84 : ∀ i ∈ List.range 4, SingleAt 28 (84+i) := by decide +kernel

theorem single_28_88 : ∀ i ∈ List.range 4, SingleAt 28 (88+i) := by decide +kernel

theorem single_28_92 : ∀ i ∈ List.range 4, SingleAt 28 (92+i) := by decide +kernel

theorem single_28_96 : ∀ i ∈ List.range 4, SingleAt 28 (96+i) := by decide +kernel

theorem single_28_100 : ∀ i ∈ List.range 4, SingleAt 28 (100+i) := by decide +kernel

theorem single_28_104 : ∀ i ∈ List.range 4, SingleAt 28 (104+i) := by decide +kernel

theorem single_28_108 : ∀ i ∈ List.range 4, SingleAt 28 (108+i) := by decide +kernel

theorem single_28_112 : ∀ i ∈ List.range 4, SingleAt 28 (112+i) := by decide +kernel

theorem single_28_116 : ∀ i ∈ List.range 4, SingleAt 28 (116+i) := by decide +kernel

theorem single_28_120 : ∀ i ∈ List.range 2, SingleAt 28 (120+i) := by decide +kernel

theorem single_28 (v : ℕ) (hv : v ∈ List.range 122) : SingleAt 28 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 28 v)
  have h := (join 0 60 62 (join 0 28 32 (join 0 12 16 (join 0 4 8 single_28_0 (join 4 4 4 single_28_4 single_28_8)) (join 12 8 8 (join 12 4 4 single_28_12 single_28_16) (join 20 4 4 single_28_20 single_28_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 single_28_28 single_28_32) (join 36 4 4 single_28_36 single_28_40)) (join 44 8 8 (join 44 4 4 single_28_44 single_28_48) (join 52 4 4 single_28_52 single_28_56)))) (join 60 32 30 (join 60 16 16 (join 60 8 8 (join 60 4 4 single_28_60 single_28_64) (join 68 4 4 single_28_68 single_28_72)) (join 76 8 8 (join 76 4 4 single_28_76 single_28_80) (join 84 4 4 single_28_84 single_28_88))) (join 92 16 14 (join 92 8 8 (join 92 4 4 single_28_92 single_28_96) (join 100 4 4 single_28_100 single_28_104)) (join 108 8 6 (join 108 4 4 single_28_108 single_28_112) (join 116 4 2 single_28_116 single_28_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_28_0 : ∀ i ∈ List.range 4, PhaseAt 28 (0+i) := by decide +kernel

theorem phase_28_4 : ∀ i ∈ List.range 4, PhaseAt 28 (4+i) := by decide +kernel

theorem phase_28_8 : ∀ i ∈ List.range 4, PhaseAt 28 (8+i) := by decide +kernel

theorem phase_28_12 : ∀ i ∈ List.range 4, PhaseAt 28 (12+i) := by decide +kernel

theorem phase_28_16 : ∀ i ∈ List.range 4, PhaseAt 28 (16+i) := by decide +kernel

theorem phase_28_20 : ∀ i ∈ List.range 4, PhaseAt 28 (20+i) := by decide +kernel

theorem phase_28_24 : ∀ i ∈ List.range 4, PhaseAt 28 (24+i) := by decide +kernel

theorem phase_28_28 : ∀ i ∈ List.range 4, PhaseAt 28 (28+i) := by decide +kernel

theorem phase_28_32 : ∀ i ∈ List.range 4, PhaseAt 28 (32+i) := by decide +kernel

theorem phase_28_36 : ∀ i ∈ List.range 4, PhaseAt 28 (36+i) := by decide +kernel

theorem phase_28_40 : ∀ i ∈ List.range 4, PhaseAt 28 (40+i) := by decide +kernel

theorem phase_28_44 : ∀ i ∈ List.range 4, PhaseAt 28 (44+i) := by decide +kernel

theorem phase_28_48 : ∀ i ∈ List.range 4, PhaseAt 28 (48+i) := by decide +kernel

theorem phase_28_52 : ∀ i ∈ List.range 4, PhaseAt 28 (52+i) := by decide +kernel

theorem phase_28_56 : ∀ i ∈ List.range 4, PhaseAt 28 (56+i) := by decide +kernel

theorem phase_28_60 : ∀ i ∈ List.range 4, PhaseAt 28 (60+i) := by decide +kernel

theorem phase_28_64 : ∀ i ∈ List.range 4, PhaseAt 28 (64+i) := by decide +kernel

theorem phase_28_68 : ∀ i ∈ List.range 4, PhaseAt 28 (68+i) := by decide +kernel

theorem phase_28_72 : ∀ i ∈ List.range 4, PhaseAt 28 (72+i) := by decide +kernel

theorem phase_28_76 : ∀ i ∈ List.range 4, PhaseAt 28 (76+i) := by decide +kernel

theorem phase_28_80 : ∀ i ∈ List.range 4, PhaseAt 28 (80+i) := by decide +kernel

theorem phase_28_84 : ∀ i ∈ List.range 4, PhaseAt 28 (84+i) := by decide +kernel

theorem phase_28_88 : ∀ i ∈ List.range 4, PhaseAt 28 (88+i) := by decide +kernel

theorem phase_28_92 : ∀ i ∈ List.range 4, PhaseAt 28 (92+i) := by decide +kernel

theorem phase_28_96 : ∀ i ∈ List.range 4, PhaseAt 28 (96+i) := by decide +kernel

theorem phase_28_100 : ∀ i ∈ List.range 4, PhaseAt 28 (100+i) := by decide +kernel

theorem phase_28_104 : ∀ i ∈ List.range 4, PhaseAt 28 (104+i) := by decide +kernel

theorem phase_28_108 : ∀ i ∈ List.range 4, PhaseAt 28 (108+i) := by decide +kernel

theorem phase_28_112 : ∀ i ∈ List.range 4, PhaseAt 28 (112+i) := by decide +kernel

theorem phase_28_116 : ∀ i ∈ List.range 4, PhaseAt 28 (116+i) := by decide +kernel

theorem phase_28_120 : ∀ i ∈ List.range 2, PhaseAt 28 (120+i) := by decide +kernel

theorem phase_28 (v : ℕ) (hv : v ∈ List.range 122) : PhaseAt 28 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 28 v)
  have h := (join 0 60 62 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_28_0 (join 4 4 4 phase_28_4 phase_28_8)) (join 12 8 8 (join 12 4 4 phase_28_12 phase_28_16) (join 20 4 4 phase_28_20 phase_28_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_28_28 phase_28_32) (join 36 4 4 phase_28_36 phase_28_40)) (join 44 8 8 (join 44 4 4 phase_28_44 phase_28_48) (join 52 4 4 phase_28_52 phase_28_56)))) (join 60 32 30 (join 60 16 16 (join 60 8 8 (join 60 4 4 phase_28_60 phase_28_64) (join 68 4 4 phase_28_68 phase_28_72)) (join 76 8 8 (join 76 4 4 phase_28_76 phase_28_80) (join 84 4 4 phase_28_84 phase_28_88))) (join 92 16 14 (join 92 8 8 (join 92 4 4 phase_28_92 phase_28_96) (join 100 4 4 phase_28_100 phase_28_104)) (join 108 8 6 (join 108 4 4 phase_28_108 phase_28_112) (join 116 4 2 phase_28_116 phase_28_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_28_0 : ∀ i ∈ List.range 1, ThresholdAt 28 (0+i) := by decide +kernel

theorem threshold_28_1 : ∀ i ∈ List.range 1, ThresholdAt 28 (1+i) := by decide +kernel

theorem threshold_28_2 : ∀ i ∈ List.range 1, ThresholdAt 28 (2+i) := by decide +kernel

theorem threshold_28_3 : ∀ i ∈ List.range 1, ThresholdAt 28 (3+i) := by decide +kernel

theorem threshold_28_4 : ∀ i ∈ List.range 1, ThresholdAt 28 (4+i) := by decide +kernel

theorem threshold_28_5 : ∀ i ∈ List.range 1, ThresholdAt 28 (5+i) := by decide +kernel

theorem threshold_28_6 : ∀ i ∈ List.range 1, ThresholdAt 28 (6+i) := by decide +kernel

theorem threshold_28_7 : ∀ i ∈ List.range 1, ThresholdAt 28 (7+i) := by decide +kernel

theorem threshold_28_8 : ∀ i ∈ List.range 1, ThresholdAt 28 (8+i) := by decide +kernel

theorem threshold_28_9 : ∀ i ∈ List.range 1, ThresholdAt 28 (9+i) := by decide +kernel

theorem threshold_28_10 : ∀ i ∈ List.range 1, ThresholdAt 28 (10+i) := by decide +kernel

theorem threshold_28_11 : ∀ i ∈ List.range 1, ThresholdAt 28 (11+i) := by decide +kernel

theorem threshold_28_12 : ∀ i ∈ List.range 1, ThresholdAt 28 (12+i) := by decide +kernel

theorem threshold_28_13 : ∀ i ∈ List.range 1, ThresholdAt 28 (13+i) := by decide +kernel

theorem threshold_28_14 : ∀ i ∈ List.range 1, ThresholdAt 28 (14+i) := by decide +kernel

theorem threshold_28_15 : ∀ i ∈ List.range 1, ThresholdAt 28 (15+i) := by decide +kernel

theorem threshold_28_16 : ∀ i ∈ List.range 1, ThresholdAt 28 (16+i) := by decide +kernel

theorem threshold_28_17 : ∀ i ∈ List.range 1, ThresholdAt 28 (17+i) := by decide +kernel

theorem threshold_28_18 : ∀ i ∈ List.range 1, ThresholdAt 28 (18+i) := by decide +kernel

theorem threshold_28_19 : ∀ i ∈ List.range 1, ThresholdAt 28 (19+i) := by decide +kernel

theorem threshold_28_20 : ∀ i ∈ List.range 1, ThresholdAt 28 (20+i) := by decide +kernel

theorem threshold_28_21 : ∀ i ∈ List.range 1, ThresholdAt 28 (21+i) := by decide +kernel

theorem threshold_28_22 : ∀ i ∈ List.range 1, ThresholdAt 28 (22+i) := by decide +kernel

theorem threshold_28_23 : ∀ i ∈ List.range 1, ThresholdAt 28 (23+i) := by decide +kernel

theorem threshold_28_24 : ∀ i ∈ List.range 1, ThresholdAt 28 (24+i) := by decide +kernel

theorem threshold_28_25 : ∀ i ∈ List.range 1, ThresholdAt 28 (25+i) := by decide +kernel

theorem threshold_28_26 : ∀ i ∈ List.range 1, ThresholdAt 28 (26+i) := by decide +kernel

theorem threshold_28_27 : ∀ i ∈ List.range 1, ThresholdAt 28 (27+i) := by decide +kernel

theorem threshold_28_28 : ∀ i ∈ List.range 1, ThresholdAt 28 (28+i) := by decide +kernel

theorem threshold_28_29 : ∀ i ∈ List.range 1, ThresholdAt 28 (29+i) := by decide +kernel

theorem threshold_28_30 : ∀ i ∈ List.range 1, ThresholdAt 28 (30+i) := by decide +kernel

theorem threshold_28_31 : ∀ i ∈ List.range 1, ThresholdAt 28 (31+i) := by decide +kernel

theorem threshold_28_32 : ∀ i ∈ List.range 1, ThresholdAt 28 (32+i) := by decide +kernel

theorem threshold_28_33 : ∀ i ∈ List.range 1, ThresholdAt 28 (33+i) := by decide +kernel

theorem threshold_28_34 : ∀ i ∈ List.range 1, ThresholdAt 28 (34+i) := by decide +kernel

theorem threshold_28_35 : ∀ i ∈ List.range 1, ThresholdAt 28 (35+i) := by decide +kernel

theorem threshold_28_36 : ∀ i ∈ List.range 1, ThresholdAt 28 (36+i) := by decide +kernel

theorem threshold_28_37 : ∀ i ∈ List.range 1, ThresholdAt 28 (37+i) := by decide +kernel

theorem threshold_28_38 : ∀ i ∈ List.range 1, ThresholdAt 28 (38+i) := by decide +kernel

theorem threshold_28_39 : ∀ i ∈ List.range 1, ThresholdAt 28 (39+i) := by decide +kernel

theorem threshold_28_40 : ∀ i ∈ List.range 1, ThresholdAt 28 (40+i) := by decide +kernel

theorem threshold_28_41 : ∀ i ∈ List.range 1, ThresholdAt 28 (41+i) := by decide +kernel

theorem threshold_28_42 : ∀ i ∈ List.range 1, ThresholdAt 28 (42+i) := by decide +kernel

theorem threshold_28_43 : ∀ i ∈ List.range 1, ThresholdAt 28 (43+i) := by decide +kernel

theorem threshold_28_44 : ∀ i ∈ List.range 1, ThresholdAt 28 (44+i) := by decide +kernel

theorem threshold_28_45 : ∀ i ∈ List.range 1, ThresholdAt 28 (45+i) := by decide +kernel

theorem threshold_28_46 : ∀ i ∈ List.range 1, ThresholdAt 28 (46+i) := by decide +kernel

theorem threshold_28_47 : ∀ i ∈ List.range 1, ThresholdAt 28 (47+i) := by decide +kernel

theorem threshold_28_48 : ∀ i ∈ List.range 1, ThresholdAt 28 (48+i) := by decide +kernel

theorem threshold_28_49 : ∀ i ∈ List.range 1, ThresholdAt 28 (49+i) := by decide +kernel

theorem threshold_28_50 : ∀ i ∈ List.range 1, ThresholdAt 28 (50+i) := by decide +kernel

theorem threshold_28_51 : ∀ i ∈ List.range 1, ThresholdAt 28 (51+i) := by decide +kernel

theorem threshold_28_52 : ∀ i ∈ List.range 1, ThresholdAt 28 (52+i) := by decide +kernel

theorem threshold_28_53 : ∀ i ∈ List.range 1, ThresholdAt 28 (53+i) := by decide +kernel

theorem threshold_28_54 : ∀ i ∈ List.range 1, ThresholdAt 28 (54+i) := by decide +kernel

theorem threshold_28_55 : ∀ i ∈ List.range 1, ThresholdAt 28 (55+i) := by decide +kernel

theorem threshold_28_56 : ∀ i ∈ List.range 1, ThresholdAt 28 (56+i) := by decide +kernel

theorem threshold_28_57 : ∀ i ∈ List.range 1, ThresholdAt 28 (57+i) := by decide +kernel

theorem threshold_28_58 : ∀ i ∈ List.range 1, ThresholdAt 28 (58+i) := by decide +kernel

theorem threshold_28_59 : ∀ i ∈ List.range 1, ThresholdAt 28 (59+i) := by decide +kernel

theorem threshold_28_60 : ∀ i ∈ List.range 1, ThresholdAt 28 (60+i) := by decide +kernel

theorem threshold_28_61 : ∀ i ∈ List.range 1, ThresholdAt 28 (61+i) := by decide +kernel

theorem threshold_28_62 : ∀ i ∈ List.range 1, ThresholdAt 28 (62+i) := by decide +kernel

theorem threshold_28_63 : ∀ i ∈ List.range 1, ThresholdAt 28 (63+i) := by decide +kernel

theorem threshold_28_64 : ∀ i ∈ List.range 1, ThresholdAt 28 (64+i) := by decide +kernel

theorem threshold_28_65 : ∀ i ∈ List.range 1, ThresholdAt 28 (65+i) := by decide +kernel

theorem threshold_28_66 : ∀ i ∈ List.range 1, ThresholdAt 28 (66+i) := by decide +kernel

theorem threshold_28_67 : ∀ i ∈ List.range 1, ThresholdAt 28 (67+i) := by decide +kernel

theorem threshold_28_68 : ∀ i ∈ List.range 1, ThresholdAt 28 (68+i) := by decide +kernel

theorem threshold_28_69 : ∀ i ∈ List.range 1, ThresholdAt 28 (69+i) := by decide +kernel

theorem threshold_28_70 : ∀ i ∈ List.range 1, ThresholdAt 28 (70+i) := by decide +kernel

theorem threshold_28_71 : ∀ i ∈ List.range 1, ThresholdAt 28 (71+i) := by decide +kernel

theorem threshold_28_72 : ∀ i ∈ List.range 1, ThresholdAt 28 (72+i) := by decide +kernel

theorem threshold_28_73 : ∀ i ∈ List.range 1, ThresholdAt 28 (73+i) := by decide +kernel

theorem threshold_28_74 : ∀ i ∈ List.range 1, ThresholdAt 28 (74+i) := by decide +kernel

theorem threshold_28_75 : ∀ i ∈ List.range 1, ThresholdAt 28 (75+i) := by decide +kernel

theorem threshold_28_76 : ∀ i ∈ List.range 1, ThresholdAt 28 (76+i) := by decide +kernel

theorem threshold_28_77 : ∀ i ∈ List.range 1, ThresholdAt 28 (77+i) := by decide +kernel

theorem threshold_28_78 : ∀ i ∈ List.range 1, ThresholdAt 28 (78+i) := by decide +kernel

theorem threshold_28_79 : ∀ i ∈ List.range 1, ThresholdAt 28 (79+i) := by decide +kernel

theorem threshold_28_80 : ∀ i ∈ List.range 1, ThresholdAt 28 (80+i) := by decide +kernel

theorem threshold_28_81 : ∀ i ∈ List.range 1, ThresholdAt 28 (81+i) := by decide +kernel

theorem threshold_28_82 : ∀ i ∈ List.range 1, ThresholdAt 28 (82+i) := by decide +kernel

theorem threshold_28_83 : ∀ i ∈ List.range 1, ThresholdAt 28 (83+i) := by decide +kernel

theorem threshold_28_84 : ∀ i ∈ List.range 1, ThresholdAt 28 (84+i) := by decide +kernel

theorem threshold_28_85 : ∀ i ∈ List.range 1, ThresholdAt 28 (85+i) := by decide +kernel

theorem threshold_28_86 : ∀ i ∈ List.range 1, ThresholdAt 28 (86+i) := by decide +kernel

theorem threshold_28_87 : ∀ i ∈ List.range 1, ThresholdAt 28 (87+i) := by decide +kernel

theorem threshold_28_88 : ∀ i ∈ List.range 1, ThresholdAt 28 (88+i) := by decide +kernel

theorem threshold_28_89 : ∀ i ∈ List.range 1, ThresholdAt 28 (89+i) := by decide +kernel

theorem threshold_28_90 : ∀ i ∈ List.range 1, ThresholdAt 28 (90+i) := by decide +kernel

theorem threshold_28_91 : ∀ i ∈ List.range 1, ThresholdAt 28 (91+i) := by decide +kernel

theorem threshold_28_92 : ∀ i ∈ List.range 1, ThresholdAt 28 (92+i) := by decide +kernel

theorem threshold_28_93 : ∀ i ∈ List.range 1, ThresholdAt 28 (93+i) := by decide +kernel

theorem threshold_28_94 : ∀ i ∈ List.range 1, ThresholdAt 28 (94+i) := by decide +kernel

theorem threshold_28_95 : ∀ i ∈ List.range 1, ThresholdAt 28 (95+i) := by decide +kernel

theorem threshold_28_96 : ∀ i ∈ List.range 1, ThresholdAt 28 (96+i) := by decide +kernel

theorem threshold_28_97 : ∀ i ∈ List.range 1, ThresholdAt 28 (97+i) := by decide +kernel

theorem threshold_28_98 : ∀ i ∈ List.range 1, ThresholdAt 28 (98+i) := by decide +kernel

theorem threshold_28_99 : ∀ i ∈ List.range 1, ThresholdAt 28 (99+i) := by decide +kernel

theorem threshold_28_100 : ∀ i ∈ List.range 1, ThresholdAt 28 (100+i) := by decide +kernel

theorem threshold_28_101 : ∀ i ∈ List.range 1, ThresholdAt 28 (101+i) := by decide +kernel

theorem threshold_28_102 : ∀ i ∈ List.range 1, ThresholdAt 28 (102+i) := by decide +kernel

theorem threshold_28_103 : ∀ i ∈ List.range 1, ThresholdAt 28 (103+i) := by decide +kernel

theorem threshold_28_104 : ∀ i ∈ List.range 1, ThresholdAt 28 (104+i) := by decide +kernel

theorem threshold_28_105 : ∀ i ∈ List.range 1, ThresholdAt 28 (105+i) := by decide +kernel

theorem threshold_28_106 : ∀ i ∈ List.range 1, ThresholdAt 28 (106+i) := by decide +kernel

theorem threshold_28_107 : ∀ i ∈ List.range 1, ThresholdAt 28 (107+i) := by decide +kernel

theorem threshold_28_108 : ∀ i ∈ List.range 1, ThresholdAt 28 (108+i) := by decide +kernel

theorem threshold_28_109 : ∀ i ∈ List.range 1, ThresholdAt 28 (109+i) := by decide +kernel

theorem threshold_28_110 : ∀ i ∈ List.range 1, ThresholdAt 28 (110+i) := by decide +kernel

theorem threshold_28_111 : ∀ i ∈ List.range 1, ThresholdAt 28 (111+i) := by decide +kernel

theorem threshold_28_112 : ∀ i ∈ List.range 1, ThresholdAt 28 (112+i) := by decide +kernel

theorem threshold_28_113 : ∀ i ∈ List.range 1, ThresholdAt 28 (113+i) := by decide +kernel

theorem threshold_28_114 : ∀ i ∈ List.range 1, ThresholdAt 28 (114+i) := by decide +kernel

theorem threshold_28_115 : ∀ i ∈ List.range 1, ThresholdAt 28 (115+i) := by decide +kernel

theorem threshold_28_116 : ∀ i ∈ List.range 1, ThresholdAt 28 (116+i) := by decide +kernel

theorem threshold_28_117 : ∀ i ∈ List.range 1, ThresholdAt 28 (117+i) := by decide +kernel

theorem threshold_28_118 : ∀ i ∈ List.range 1, ThresholdAt 28 (118+i) := by decide +kernel

theorem threshold_28_119 : ∀ i ∈ List.range 1, ThresholdAt 28 (119+i) := by decide +kernel

theorem threshold_28_120 : ∀ i ∈ List.range 1, ThresholdAt 28 (120+i) := by decide +kernel

theorem threshold_28_121 : ∀ i ∈ List.range 1, ThresholdAt 28 (121+i) := by decide +kernel

theorem threshold_28 (v : ℕ) (hv : v ∈ List.range 122) : ThresholdAt 28 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 28 v)
  have h := (join 0 61 61 (join 0 30 31 (join 0 15 15 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_28_0 (join 1 1 1 threshold_28_1 threshold_28_2)) (join 3 2 2 (join 3 1 1 threshold_28_3 threshold_28_4) (join 5 1 1 threshold_28_5 threshold_28_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_28_7 threshold_28_8) (join 9 1 1 threshold_28_9 threshold_28_10)) (join 11 2 2 (join 11 1 1 threshold_28_11 threshold_28_12) (join 13 1 1 threshold_28_13 threshold_28_14)))) (join 15 7 8 (join 15 3 4 (join 15 1 2 threshold_28_15 (join 16 1 1 threshold_28_16 threshold_28_17)) (join 18 2 2 (join 18 1 1 threshold_28_18 threshold_28_19) (join 20 1 1 threshold_28_20 threshold_28_21))) (join 22 4 4 (join 22 2 2 (join 22 1 1 threshold_28_22 threshold_28_23) (join 24 1 1 threshold_28_24 threshold_28_25)) (join 26 2 2 (join 26 1 1 threshold_28_26 threshold_28_27) (join 28 1 1 threshold_28_28 threshold_28_29))))) (join 30 15 16 (join 30 7 8 (join 30 3 4 (join 30 1 2 threshold_28_30 (join 31 1 1 threshold_28_31 threshold_28_32)) (join 33 2 2 (join 33 1 1 threshold_28_33 threshold_28_34) (join 35 1 1 threshold_28_35 threshold_28_36))) (join 37 4 4 (join 37 2 2 (join 37 1 1 threshold_28_37 threshold_28_38) (join 39 1 1 threshold_28_39 threshold_28_40)) (join 41 2 2 (join 41 1 1 threshold_28_41 threshold_28_42) (join 43 1 1 threshold_28_43 threshold_28_44)))) (join 45 8 8 (join 45 4 4 (join 45 2 2 (join 45 1 1 threshold_28_45 threshold_28_46) (join 47 1 1 threshold_28_47 threshold_28_48)) (join 49 2 2 (join 49 1 1 threshold_28_49 threshold_28_50) (join 51 1 1 threshold_28_51 threshold_28_52))) (join 53 4 4 (join 53 2 2 (join 53 1 1 threshold_28_53 threshold_28_54) (join 55 1 1 threshold_28_55 threshold_28_56)) (join 57 2 2 (join 57 1 1 threshold_28_57 threshold_28_58) (join 59 1 1 threshold_28_59 threshold_28_60)))))) (join 61 30 31 (join 61 15 15 (join 61 7 8 (join 61 3 4 (join 61 1 2 threshold_28_61 (join 62 1 1 threshold_28_62 threshold_28_63)) (join 64 2 2 (join 64 1 1 threshold_28_64 threshold_28_65) (join 66 1 1 threshold_28_66 threshold_28_67))) (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_28_68 threshold_28_69) (join 70 1 1 threshold_28_70 threshold_28_71)) (join 72 2 2 (join 72 1 1 threshold_28_72 threshold_28_73) (join 74 1 1 threshold_28_74 threshold_28_75)))) (join 76 7 8 (join 76 3 4 (join 76 1 2 threshold_28_76 (join 77 1 1 threshold_28_77 threshold_28_78)) (join 79 2 2 (join 79 1 1 threshold_28_79 threshold_28_80) (join 81 1 1 threshold_28_81 threshold_28_82))) (join 83 4 4 (join 83 2 2 (join 83 1 1 threshold_28_83 threshold_28_84) (join 85 1 1 threshold_28_85 threshold_28_86)) (join 87 2 2 (join 87 1 1 threshold_28_87 threshold_28_88) (join 89 1 1 threshold_28_89 threshold_28_90))))) (join 91 15 16 (join 91 7 8 (join 91 3 4 (join 91 1 2 threshold_28_91 (join 92 1 1 threshold_28_92 threshold_28_93)) (join 94 2 2 (join 94 1 1 threshold_28_94 threshold_28_95) (join 96 1 1 threshold_28_96 threshold_28_97))) (join 98 4 4 (join 98 2 2 (join 98 1 1 threshold_28_98 threshold_28_99) (join 100 1 1 threshold_28_100 threshold_28_101)) (join 102 2 2 (join 102 1 1 threshold_28_102 threshold_28_103) (join 104 1 1 threshold_28_104 threshold_28_105)))) (join 106 8 8 (join 106 4 4 (join 106 2 2 (join 106 1 1 threshold_28_106 threshold_28_107) (join 108 1 1 threshold_28_108 threshold_28_109)) (join 110 2 2 (join 110 1 1 threshold_28_110 threshold_28_111) (join 112 1 1 threshold_28_112 threshold_28_113))) (join 114 4 4 (join 114 2 2 (join 114 1 1 threshold_28_114 threshold_28_115) (join 116 1 1 threshold_28_116 threshold_28_117)) (join 118 2 2 (join 118 1 1 threshold_28_118 threshold_28_119) (join 120 1 1 threshold_28_120 threshold_28_121)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_28_0 : ∀ i ∈ List.range 4, LedgerAt 28 (0+i) := by decide +kernel

theorem ledger_28_4 : ∀ i ∈ List.range 4, LedgerAt 28 (4+i) := by decide +kernel

theorem ledger_28_8 : ∀ i ∈ List.range 4, LedgerAt 28 (8+i) := by decide +kernel

theorem ledger_28_12 : ∀ i ∈ List.range 4, LedgerAt 28 (12+i) := by decide +kernel

theorem ledger_28_16 : ∀ i ∈ List.range 4, LedgerAt 28 (16+i) := by decide +kernel

theorem ledger_28_20 : ∀ i ∈ List.range 4, LedgerAt 28 (20+i) := by decide +kernel

theorem ledger_28_24 : ∀ i ∈ List.range 4, LedgerAt 28 (24+i) := by decide +kernel

theorem ledger_28_28 : ∀ i ∈ List.range 4, LedgerAt 28 (28+i) := by decide +kernel

theorem ledger_28_32 : ∀ i ∈ List.range 4, LedgerAt 28 (32+i) := by decide +kernel

theorem ledger_28_36 : ∀ i ∈ List.range 4, LedgerAt 28 (36+i) := by decide +kernel

theorem ledger_28_40 : ∀ i ∈ List.range 4, LedgerAt 28 (40+i) := by decide +kernel

theorem ledger_28_44 : ∀ i ∈ List.range 4, LedgerAt 28 (44+i) := by decide +kernel

theorem ledger_28_48 : ∀ i ∈ List.range 4, LedgerAt 28 (48+i) := by decide +kernel

theorem ledger_28_52 : ∀ i ∈ List.range 4, LedgerAt 28 (52+i) := by decide +kernel

theorem ledger_28_56 : ∀ i ∈ List.range 4, LedgerAt 28 (56+i) := by decide +kernel

theorem ledger_28_60 : ∀ i ∈ List.range 4, LedgerAt 28 (60+i) := by decide +kernel

theorem ledger_28_64 : ∀ i ∈ List.range 4, LedgerAt 28 (64+i) := by decide +kernel

theorem ledger_28_68 : ∀ i ∈ List.range 4, LedgerAt 28 (68+i) := by decide +kernel

theorem ledger_28_72 : ∀ i ∈ List.range 4, LedgerAt 28 (72+i) := by decide +kernel

theorem ledger_28_76 : ∀ i ∈ List.range 4, LedgerAt 28 (76+i) := by decide +kernel

theorem ledger_28_80 : ∀ i ∈ List.range 4, LedgerAt 28 (80+i) := by decide +kernel

theorem ledger_28_84 : ∀ i ∈ List.range 4, LedgerAt 28 (84+i) := by decide +kernel

theorem ledger_28_88 : ∀ i ∈ List.range 4, LedgerAt 28 (88+i) := by decide +kernel

theorem ledger_28_92 : ∀ i ∈ List.range 4, LedgerAt 28 (92+i) := by decide +kernel

theorem ledger_28_96 : ∀ i ∈ List.range 4, LedgerAt 28 (96+i) := by decide +kernel

theorem ledger_28_100 : ∀ i ∈ List.range 4, LedgerAt 28 (100+i) := by decide +kernel

theorem ledger_28_104 : ∀ i ∈ List.range 4, LedgerAt 28 (104+i) := by decide +kernel

theorem ledger_28_108 : ∀ i ∈ List.range 4, LedgerAt 28 (108+i) := by decide +kernel

theorem ledger_28_112 : ∀ i ∈ List.range 4, LedgerAt 28 (112+i) := by decide +kernel

theorem ledger_28_116 : ∀ i ∈ List.range 4, LedgerAt 28 (116+i) := by decide +kernel

theorem ledger_28_120 : ∀ i ∈ List.range 2, LedgerAt 28 (120+i) := by decide +kernel

theorem ledger_28 (v : ℕ) (hv : v ∈ List.range 122) : LedgerAt 28 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 28 v)
  have h := (join 0 60 62 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_28_0 (join 4 4 4 ledger_28_4 ledger_28_8)) (join 12 8 8 (join 12 4 4 ledger_28_12 ledger_28_16) (join 20 4 4 ledger_28_20 ledger_28_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_28_28 ledger_28_32) (join 36 4 4 ledger_28_36 ledger_28_40)) (join 44 8 8 (join 44 4 4 ledger_28_44 ledger_28_48) (join 52 4 4 ledger_28_52 ledger_28_56)))) (join 60 32 30 (join 60 16 16 (join 60 8 8 (join 60 4 4 ledger_28_60 ledger_28_64) (join 68 4 4 ledger_28_68 ledger_28_72)) (join 76 8 8 (join 76 4 4 ledger_28_76 ledger_28_80) (join 84 4 4 ledger_28_84 ledger_28_88))) (join 92 16 14 (join 92 8 8 (join 92 4 4 ledger_28_92 ledger_28_96) (join 100 4 4 ledger_28_100 ledger_28_104)) (join 108 8 6 (join 108 4 4 ledger_28_108 ledger_28_112) (join 116 4 2 ledger_28_116 ledger_28_120)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
