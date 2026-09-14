import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
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

theorem single_26 (v : ℕ) (hv : v ∈ List.range 124) : SingleAt 26 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 26 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 single_26_0 (join 4 4 4 single_26_4 single_26_8)) (join 12 8 8 (join 12 4 4 single_26_12 single_26_16) (join 20 4 4 single_26_20 single_26_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 single_26_28 single_26_32) (join 36 4 4 single_26_36 single_26_40)) (join 44 8 8 (join 44 4 4 single_26_44 single_26_48) (join 52 4 4 single_26_52 single_26_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 single_26_60 single_26_64) (join 68 4 4 single_26_68 single_26_72)) (join 76 8 8 (join 76 4 4 single_26_76 single_26_80) (join 84 4 4 single_26_84 single_26_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 single_26_92 single_26_96) (join 100 4 4 single_26_100 single_26_104)) (join 108 8 8 (join 108 4 4 single_26_108 single_26_112) (join 116 4 4 single_26_116 single_26_120)))))
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

theorem phase_26 (v : ℕ) (hv : v ∈ List.range 124) : PhaseAt 26 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 26 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_26_0 (join 4 4 4 phase_26_4 phase_26_8)) (join 12 8 8 (join 12 4 4 phase_26_12 phase_26_16) (join 20 4 4 phase_26_20 phase_26_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_26_28 phase_26_32) (join 36 4 4 phase_26_36 phase_26_40)) (join 44 8 8 (join 44 4 4 phase_26_44 phase_26_48) (join 52 4 4 phase_26_52 phase_26_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 phase_26_60 phase_26_64) (join 68 4 4 phase_26_68 phase_26_72)) (join 76 8 8 (join 76 4 4 phase_26_76 phase_26_80) (join 84 4 4 phase_26_84 phase_26_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 phase_26_92 phase_26_96) (join 100 4 4 phase_26_100 phase_26_104)) (join 108 8 8 (join 108 4 4 phase_26_108 phase_26_112) (join 116 4 4 phase_26_116 phase_26_120)))))
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

theorem threshold_26 (v : ℕ) (hv : v ∈ List.range 124) : ThresholdAt 26 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 26 v)
  have h := (join 0 62 62 (join 0 31 31 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_26_0 (join 1 1 1 threshold_26_1 threshold_26_2)) (join 3 2 2 (join 3 1 1 threshold_26_3 threshold_26_4) (join 5 1 1 threshold_26_5 threshold_26_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_26_7 threshold_26_8) (join 9 1 1 threshold_26_9 threshold_26_10)) (join 11 2 2 (join 11 1 1 threshold_26_11 threshold_26_12) (join 13 1 1 threshold_26_13 threshold_26_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_26_15 threshold_26_16) (join 17 1 1 threshold_26_17 threshold_26_18)) (join 19 2 2 (join 19 1 1 threshold_26_19 threshold_26_20) (join 21 1 1 threshold_26_21 threshold_26_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_26_23 threshold_26_24) (join 25 1 1 threshold_26_25 threshold_26_26)) (join 27 2 2 (join 27 1 1 threshold_26_27 threshold_26_28) (join 29 1 1 threshold_26_29 threshold_26_30))))) (join 31 15 16 (join 31 7 8 (join 31 3 4 (join 31 1 2 threshold_26_31 (join 32 1 1 threshold_26_32 threshold_26_33)) (join 34 2 2 (join 34 1 1 threshold_26_34 threshold_26_35) (join 36 1 1 threshold_26_36 threshold_26_37))) (join 38 4 4 (join 38 2 2 (join 38 1 1 threshold_26_38 threshold_26_39) (join 40 1 1 threshold_26_40 threshold_26_41)) (join 42 2 2 (join 42 1 1 threshold_26_42 threshold_26_43) (join 44 1 1 threshold_26_44 threshold_26_45)))) (join 46 8 8 (join 46 4 4 (join 46 2 2 (join 46 1 1 threshold_26_46 threshold_26_47) (join 48 1 1 threshold_26_48 threshold_26_49)) (join 50 2 2 (join 50 1 1 threshold_26_50 threshold_26_51) (join 52 1 1 threshold_26_52 threshold_26_53))) (join 54 4 4 (join 54 2 2 (join 54 1 1 threshold_26_54 threshold_26_55) (join 56 1 1 threshold_26_56 threshold_26_57)) (join 58 2 2 (join 58 1 1 threshold_26_58 threshold_26_59) (join 60 1 1 threshold_26_60 threshold_26_61)))))) (join 62 31 31 (join 62 15 16 (join 62 7 8 (join 62 3 4 (join 62 1 2 threshold_26_62 (join 63 1 1 threshold_26_63 threshold_26_64)) (join 65 2 2 (join 65 1 1 threshold_26_65 threshold_26_66) (join 67 1 1 threshold_26_67 threshold_26_68))) (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_26_69 threshold_26_70) (join 71 1 1 threshold_26_71 threshold_26_72)) (join 73 2 2 (join 73 1 1 threshold_26_73 threshold_26_74) (join 75 1 1 threshold_26_75 threshold_26_76)))) (join 77 8 8 (join 77 4 4 (join 77 2 2 (join 77 1 1 threshold_26_77 threshold_26_78) (join 79 1 1 threshold_26_79 threshold_26_80)) (join 81 2 2 (join 81 1 1 threshold_26_81 threshold_26_82) (join 83 1 1 threshold_26_83 threshold_26_84))) (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_26_85 threshold_26_86) (join 87 1 1 threshold_26_87 threshold_26_88)) (join 89 2 2 (join 89 1 1 threshold_26_89 threshold_26_90) (join 91 1 1 threshold_26_91 threshold_26_92))))) (join 93 15 16 (join 93 7 8 (join 93 3 4 (join 93 1 2 threshold_26_93 (join 94 1 1 threshold_26_94 threshold_26_95)) (join 96 2 2 (join 96 1 1 threshold_26_96 threshold_26_97) (join 98 1 1 threshold_26_98 threshold_26_99))) (join 100 4 4 (join 100 2 2 (join 100 1 1 threshold_26_100 threshold_26_101) (join 102 1 1 threshold_26_102 threshold_26_103)) (join 104 2 2 (join 104 1 1 threshold_26_104 threshold_26_105) (join 106 1 1 threshold_26_106 threshold_26_107)))) (join 108 8 8 (join 108 4 4 (join 108 2 2 (join 108 1 1 threshold_26_108 threshold_26_109) (join 110 1 1 threshold_26_110 threshold_26_111)) (join 112 2 2 (join 112 1 1 threshold_26_112 threshold_26_113) (join 114 1 1 threshold_26_114 threshold_26_115))) (join 116 4 4 (join 116 2 2 (join 116 1 1 threshold_26_116 threshold_26_117) (join 118 1 1 threshold_26_118 threshold_26_119)) (join 120 2 2 (join 120 1 1 threshold_26_120 threshold_26_121) (join 122 1 1 threshold_26_122 threshold_26_123)))))))
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

theorem ledger_26 (v : ℕ) (hv : v ∈ List.range 124) : LedgerAt 26 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 26 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_26_0 (join 4 4 4 ledger_26_4 ledger_26_8)) (join 12 8 8 (join 12 4 4 ledger_26_12 ledger_26_16) (join 20 4 4 ledger_26_20 ledger_26_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_26_28 ledger_26_32) (join 36 4 4 ledger_26_36 ledger_26_40)) (join 44 8 8 (join 44 4 4 ledger_26_44 ledger_26_48) (join 52 4 4 ledger_26_52 ledger_26_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 ledger_26_60 ledger_26_64) (join 68 4 4 ledger_26_68 ledger_26_72)) (join 76 8 8 (join 76 4 4 ledger_26_76 ledger_26_80) (join 84 4 4 ledger_26_84 ledger_26_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 ledger_26_92 ledger_26_96) (join 100 4 4 ledger_26_100 ledger_26_104)) (join 108 8 8 (join 108 4 4 ledger_26_108 ledger_26_112) (join 116 4 4 ledger_26_116 ledger_26_120)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
