import ProximityPrize.SubmissionLower.AffineCheckedR226808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_23_0 : ∀ i ∈ List.range 4, SingleAt 23 (0+i) := by decide +kernel

theorem single_23_4 : ∀ i ∈ List.range 4, SingleAt 23 (4+i) := by decide +kernel

theorem single_23_8 : ∀ i ∈ List.range 4, SingleAt 23 (8+i) := by decide +kernel

theorem single_23_12 : ∀ i ∈ List.range 4, SingleAt 23 (12+i) := by decide +kernel

theorem single_23_16 : ∀ i ∈ List.range 4, SingleAt 23 (16+i) := by decide +kernel

theorem single_23_20 : ∀ i ∈ List.range 4, SingleAt 23 (20+i) := by decide +kernel

theorem single_23_24 : ∀ i ∈ List.range 4, SingleAt 23 (24+i) := by decide +kernel

theorem single_23_28 : ∀ i ∈ List.range 4, SingleAt 23 (28+i) := by decide +kernel

theorem single_23_32 : ∀ i ∈ List.range 4, SingleAt 23 (32+i) := by decide +kernel

theorem single_23_36 : ∀ i ∈ List.range 4, SingleAt 23 (36+i) := by decide +kernel

theorem single_23_40 : ∀ i ∈ List.range 4, SingleAt 23 (40+i) := by decide +kernel

theorem single_23_44 : ∀ i ∈ List.range 4, SingleAt 23 (44+i) := by decide +kernel

theorem single_23_48 : ∀ i ∈ List.range 4, SingleAt 23 (48+i) := by decide +kernel

theorem single_23_52 : ∀ i ∈ List.range 4, SingleAt 23 (52+i) := by decide +kernel

theorem single_23_56 : ∀ i ∈ List.range 4, SingleAt 23 (56+i) := by decide +kernel

theorem single_23_60 : ∀ i ∈ List.range 4, SingleAt 23 (60+i) := by decide +kernel

theorem single_23_64 : ∀ i ∈ List.range 4, SingleAt 23 (64+i) := by decide +kernel

theorem single_23_68 : ∀ i ∈ List.range 4, SingleAt 23 (68+i) := by decide +kernel

theorem single_23_72 : ∀ i ∈ List.range 4, SingleAt 23 (72+i) := by decide +kernel

theorem single_23_76 : ∀ i ∈ List.range 4, SingleAt 23 (76+i) := by decide +kernel

theorem single_23_80 : ∀ i ∈ List.range 4, SingleAt 23 (80+i) := by decide +kernel

theorem single_23_84 : ∀ i ∈ List.range 4, SingleAt 23 (84+i) := by decide +kernel

theorem single_23_88 : ∀ i ∈ List.range 4, SingleAt 23 (88+i) := by decide +kernel

theorem single_23_92 : ∀ i ∈ List.range 4, SingleAt 23 (92+i) := by decide +kernel

theorem single_23_96 : ∀ i ∈ List.range 4, SingleAt 23 (96+i) := by decide +kernel

theorem single_23_100 : ∀ i ∈ List.range 4, SingleAt 23 (100+i) := by decide +kernel

theorem single_23_104 : ∀ i ∈ List.range 4, SingleAt 23 (104+i) := by decide +kernel

theorem single_23_108 : ∀ i ∈ List.range 4, SingleAt 23 (108+i) := by decide +kernel

theorem single_23_112 : ∀ i ∈ List.range 4, SingleAt 23 (112+i) := by decide +kernel

theorem single_23_116 : ∀ i ∈ List.range 4, SingleAt 23 (116+i) := by decide +kernel

theorem single_23_120 : ∀ i ∈ List.range 4, SingleAt 23 (120+i) := by decide +kernel

theorem single_23_124 : ∀ i ∈ List.range 3, SingleAt 23 (124+i) := by decide +kernel

theorem single_23 (v : ℕ) (hv : v ∈ List.range 127) : SingleAt 23 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 23 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_23_0 single_23_4) (join 8 4 4 single_23_8 single_23_12)) (join 16 8 8 (join 16 4 4 single_23_16 single_23_20) (join 24 4 4 single_23_24 single_23_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_23_32 single_23_36) (join 40 4 4 single_23_40 single_23_44)) (join 48 8 8 (join 48 4 4 single_23_48 single_23_52) (join 56 4 4 single_23_56 single_23_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_23_64 single_23_68) (join 72 4 4 single_23_72 single_23_76)) (join 80 8 8 (join 80 4 4 single_23_80 single_23_84) (join 88 4 4 single_23_88 single_23_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 single_23_96 single_23_100) (join 104 4 4 single_23_104 single_23_108)) (join 112 8 7 (join 112 4 4 single_23_112 single_23_116) (join 120 4 3 single_23_120 single_23_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_23_0 : ∀ i ∈ List.range 4, PhaseAt 23 (0+i) := by decide +kernel

theorem phase_23_4 : ∀ i ∈ List.range 4, PhaseAt 23 (4+i) := by decide +kernel

theorem phase_23_8 : ∀ i ∈ List.range 4, PhaseAt 23 (8+i) := by decide +kernel

theorem phase_23_12 : ∀ i ∈ List.range 4, PhaseAt 23 (12+i) := by decide +kernel

theorem phase_23_16 : ∀ i ∈ List.range 4, PhaseAt 23 (16+i) := by decide +kernel

theorem phase_23_20 : ∀ i ∈ List.range 4, PhaseAt 23 (20+i) := by decide +kernel

theorem phase_23_24 : ∀ i ∈ List.range 4, PhaseAt 23 (24+i) := by decide +kernel

theorem phase_23_28 : ∀ i ∈ List.range 4, PhaseAt 23 (28+i) := by decide +kernel

theorem phase_23_32 : ∀ i ∈ List.range 4, PhaseAt 23 (32+i) := by decide +kernel

theorem phase_23_36 : ∀ i ∈ List.range 4, PhaseAt 23 (36+i) := by decide +kernel

theorem phase_23_40 : ∀ i ∈ List.range 4, PhaseAt 23 (40+i) := by decide +kernel

theorem phase_23_44 : ∀ i ∈ List.range 4, PhaseAt 23 (44+i) := by decide +kernel

theorem phase_23_48 : ∀ i ∈ List.range 4, PhaseAt 23 (48+i) := by decide +kernel

theorem phase_23_52 : ∀ i ∈ List.range 4, PhaseAt 23 (52+i) := by decide +kernel

theorem phase_23_56 : ∀ i ∈ List.range 4, PhaseAt 23 (56+i) := by decide +kernel

theorem phase_23_60 : ∀ i ∈ List.range 4, PhaseAt 23 (60+i) := by decide +kernel

theorem phase_23_64 : ∀ i ∈ List.range 4, PhaseAt 23 (64+i) := by decide +kernel

theorem phase_23_68 : ∀ i ∈ List.range 4, PhaseAt 23 (68+i) := by decide +kernel

theorem phase_23_72 : ∀ i ∈ List.range 4, PhaseAt 23 (72+i) := by decide +kernel

theorem phase_23_76 : ∀ i ∈ List.range 4, PhaseAt 23 (76+i) := by decide +kernel

theorem phase_23_80 : ∀ i ∈ List.range 4, PhaseAt 23 (80+i) := by decide +kernel

theorem phase_23_84 : ∀ i ∈ List.range 4, PhaseAt 23 (84+i) := by decide +kernel

theorem phase_23_88 : ∀ i ∈ List.range 4, PhaseAt 23 (88+i) := by decide +kernel

theorem phase_23_92 : ∀ i ∈ List.range 4, PhaseAt 23 (92+i) := by decide +kernel

theorem phase_23_96 : ∀ i ∈ List.range 4, PhaseAt 23 (96+i) := by decide +kernel

theorem phase_23_100 : ∀ i ∈ List.range 4, PhaseAt 23 (100+i) := by decide +kernel

theorem phase_23_104 : ∀ i ∈ List.range 4, PhaseAt 23 (104+i) := by decide +kernel

theorem phase_23_108 : ∀ i ∈ List.range 4, PhaseAt 23 (108+i) := by decide +kernel

theorem phase_23_112 : ∀ i ∈ List.range 4, PhaseAt 23 (112+i) := by decide +kernel

theorem phase_23_116 : ∀ i ∈ List.range 4, PhaseAt 23 (116+i) := by decide +kernel

theorem phase_23_120 : ∀ i ∈ List.range 4, PhaseAt 23 (120+i) := by decide +kernel

theorem phase_23_124 : ∀ i ∈ List.range 3, PhaseAt 23 (124+i) := by decide +kernel

theorem phase_23 (v : ℕ) (hv : v ∈ List.range 127) : PhaseAt 23 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 23 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_23_0 phase_23_4) (join 8 4 4 phase_23_8 phase_23_12)) (join 16 8 8 (join 16 4 4 phase_23_16 phase_23_20) (join 24 4 4 phase_23_24 phase_23_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_23_32 phase_23_36) (join 40 4 4 phase_23_40 phase_23_44)) (join 48 8 8 (join 48 4 4 phase_23_48 phase_23_52) (join 56 4 4 phase_23_56 phase_23_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_23_64 phase_23_68) (join 72 4 4 phase_23_72 phase_23_76)) (join 80 8 8 (join 80 4 4 phase_23_80 phase_23_84) (join 88 4 4 phase_23_88 phase_23_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 phase_23_96 phase_23_100) (join 104 4 4 phase_23_104 phase_23_108)) (join 112 8 7 (join 112 4 4 phase_23_112 phase_23_116) (join 120 4 3 phase_23_120 phase_23_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_23_0 : ∀ i ∈ List.range 1, ThresholdAt 23 (0+i) := by decide +kernel

theorem threshold_23_1 : ∀ i ∈ List.range 1, ThresholdAt 23 (1+i) := by decide +kernel

theorem threshold_23_2 : ∀ i ∈ List.range 1, ThresholdAt 23 (2+i) := by decide +kernel

theorem threshold_23_3 : ∀ i ∈ List.range 1, ThresholdAt 23 (3+i) := by decide +kernel

theorem threshold_23_4 : ∀ i ∈ List.range 1, ThresholdAt 23 (4+i) := by decide +kernel

theorem threshold_23_5 : ∀ i ∈ List.range 1, ThresholdAt 23 (5+i) := by decide +kernel

theorem threshold_23_6 : ∀ i ∈ List.range 1, ThresholdAt 23 (6+i) := by decide +kernel

theorem threshold_23_7 : ∀ i ∈ List.range 1, ThresholdAt 23 (7+i) := by decide +kernel

theorem threshold_23_8 : ∀ i ∈ List.range 1, ThresholdAt 23 (8+i) := by decide +kernel

theorem threshold_23_9 : ∀ i ∈ List.range 1, ThresholdAt 23 (9+i) := by decide +kernel

theorem threshold_23_10 : ∀ i ∈ List.range 1, ThresholdAt 23 (10+i) := by decide +kernel

theorem threshold_23_11 : ∀ i ∈ List.range 1, ThresholdAt 23 (11+i) := by decide +kernel

theorem threshold_23_12 : ∀ i ∈ List.range 1, ThresholdAt 23 (12+i) := by decide +kernel

theorem threshold_23_13 : ∀ i ∈ List.range 1, ThresholdAt 23 (13+i) := by decide +kernel

theorem threshold_23_14 : ∀ i ∈ List.range 1, ThresholdAt 23 (14+i) := by decide +kernel

theorem threshold_23_15 : ∀ i ∈ List.range 1, ThresholdAt 23 (15+i) := by decide +kernel

theorem threshold_23_16 : ∀ i ∈ List.range 1, ThresholdAt 23 (16+i) := by decide +kernel

theorem threshold_23_17 : ∀ i ∈ List.range 1, ThresholdAt 23 (17+i) := by decide +kernel

theorem threshold_23_18 : ∀ i ∈ List.range 1, ThresholdAt 23 (18+i) := by decide +kernel

theorem threshold_23_19 : ∀ i ∈ List.range 1, ThresholdAt 23 (19+i) := by decide +kernel

theorem threshold_23_20 : ∀ i ∈ List.range 1, ThresholdAt 23 (20+i) := by decide +kernel

theorem threshold_23_21 : ∀ i ∈ List.range 1, ThresholdAt 23 (21+i) := by decide +kernel

theorem threshold_23_22 : ∀ i ∈ List.range 1, ThresholdAt 23 (22+i) := by decide +kernel

theorem threshold_23_23 : ∀ i ∈ List.range 1, ThresholdAt 23 (23+i) := by decide +kernel

theorem threshold_23_24 : ∀ i ∈ List.range 1, ThresholdAt 23 (24+i) := by decide +kernel

theorem threshold_23_25 : ∀ i ∈ List.range 1, ThresholdAt 23 (25+i) := by decide +kernel

theorem threshold_23_26 : ∀ i ∈ List.range 1, ThresholdAt 23 (26+i) := by decide +kernel

theorem threshold_23_27 : ∀ i ∈ List.range 1, ThresholdAt 23 (27+i) := by decide +kernel

theorem threshold_23_28 : ∀ i ∈ List.range 1, ThresholdAt 23 (28+i) := by decide +kernel

theorem threshold_23_29 : ∀ i ∈ List.range 1, ThresholdAt 23 (29+i) := by decide +kernel

theorem threshold_23_30 : ∀ i ∈ List.range 1, ThresholdAt 23 (30+i) := by decide +kernel

theorem threshold_23_31 : ∀ i ∈ List.range 1, ThresholdAt 23 (31+i) := by decide +kernel

theorem threshold_23_32 : ∀ i ∈ List.range 1, ThresholdAt 23 (32+i) := by decide +kernel

theorem threshold_23_33 : ∀ i ∈ List.range 1, ThresholdAt 23 (33+i) := by decide +kernel

theorem threshold_23_34 : ∀ i ∈ List.range 1, ThresholdAt 23 (34+i) := by decide +kernel

theorem threshold_23_35 : ∀ i ∈ List.range 1, ThresholdAt 23 (35+i) := by decide +kernel

theorem threshold_23_36 : ∀ i ∈ List.range 1, ThresholdAt 23 (36+i) := by decide +kernel

theorem threshold_23_37 : ∀ i ∈ List.range 1, ThresholdAt 23 (37+i) := by decide +kernel

theorem threshold_23_38 : ∀ i ∈ List.range 1, ThresholdAt 23 (38+i) := by decide +kernel

theorem threshold_23_39 : ∀ i ∈ List.range 1, ThresholdAt 23 (39+i) := by decide +kernel

theorem threshold_23_40 : ∀ i ∈ List.range 1, ThresholdAt 23 (40+i) := by decide +kernel

theorem threshold_23_41 : ∀ i ∈ List.range 1, ThresholdAt 23 (41+i) := by decide +kernel

theorem threshold_23_42 : ∀ i ∈ List.range 1, ThresholdAt 23 (42+i) := by decide +kernel

theorem threshold_23_43 : ∀ i ∈ List.range 1, ThresholdAt 23 (43+i) := by decide +kernel

theorem threshold_23_44 : ∀ i ∈ List.range 1, ThresholdAt 23 (44+i) := by decide +kernel

theorem threshold_23_45 : ∀ i ∈ List.range 1, ThresholdAt 23 (45+i) := by decide +kernel

theorem threshold_23_46 : ∀ i ∈ List.range 1, ThresholdAt 23 (46+i) := by decide +kernel

theorem threshold_23_47 : ∀ i ∈ List.range 1, ThresholdAt 23 (47+i) := by decide +kernel

theorem threshold_23_48 : ∀ i ∈ List.range 1, ThresholdAt 23 (48+i) := by decide +kernel

theorem threshold_23_49 : ∀ i ∈ List.range 1, ThresholdAt 23 (49+i) := by decide +kernel

theorem threshold_23_50 : ∀ i ∈ List.range 1, ThresholdAt 23 (50+i) := by decide +kernel

theorem threshold_23_51 : ∀ i ∈ List.range 1, ThresholdAt 23 (51+i) := by decide +kernel

theorem threshold_23_52 : ∀ i ∈ List.range 1, ThresholdAt 23 (52+i) := by decide +kernel

theorem threshold_23_53 : ∀ i ∈ List.range 1, ThresholdAt 23 (53+i) := by decide +kernel

theorem threshold_23_54 : ∀ i ∈ List.range 1, ThresholdAt 23 (54+i) := by decide +kernel

theorem threshold_23_55 : ∀ i ∈ List.range 1, ThresholdAt 23 (55+i) := by decide +kernel

theorem threshold_23_56 : ∀ i ∈ List.range 1, ThresholdAt 23 (56+i) := by decide +kernel

theorem threshold_23_57 : ∀ i ∈ List.range 1, ThresholdAt 23 (57+i) := by decide +kernel

theorem threshold_23_58 : ∀ i ∈ List.range 1, ThresholdAt 23 (58+i) := by decide +kernel

theorem threshold_23_59 : ∀ i ∈ List.range 1, ThresholdAt 23 (59+i) := by decide +kernel

theorem threshold_23_60 : ∀ i ∈ List.range 1, ThresholdAt 23 (60+i) := by decide +kernel

theorem threshold_23_61 : ∀ i ∈ List.range 1, ThresholdAt 23 (61+i) := by decide +kernel

theorem threshold_23_62 : ∀ i ∈ List.range 1, ThresholdAt 23 (62+i) := by decide +kernel

theorem threshold_23_63 : ∀ i ∈ List.range 1, ThresholdAt 23 (63+i) := by decide +kernel

theorem threshold_23_64 : ∀ i ∈ List.range 1, ThresholdAt 23 (64+i) := by decide +kernel

theorem threshold_23_65 : ∀ i ∈ List.range 1, ThresholdAt 23 (65+i) := by decide +kernel

theorem threshold_23_66 : ∀ i ∈ List.range 1, ThresholdAt 23 (66+i) := by decide +kernel

theorem threshold_23_67 : ∀ i ∈ List.range 1, ThresholdAt 23 (67+i) := by decide +kernel

theorem threshold_23_68 : ∀ i ∈ List.range 1, ThresholdAt 23 (68+i) := by decide +kernel

theorem threshold_23_69 : ∀ i ∈ List.range 1, ThresholdAt 23 (69+i) := by decide +kernel

theorem threshold_23_70 : ∀ i ∈ List.range 1, ThresholdAt 23 (70+i) := by decide +kernel

theorem threshold_23_71 : ∀ i ∈ List.range 1, ThresholdAt 23 (71+i) := by decide +kernel

theorem threshold_23_72 : ∀ i ∈ List.range 1, ThresholdAt 23 (72+i) := by decide +kernel

theorem threshold_23_73 : ∀ i ∈ List.range 1, ThresholdAt 23 (73+i) := by decide +kernel

theorem threshold_23_74 : ∀ i ∈ List.range 1, ThresholdAt 23 (74+i) := by decide +kernel

theorem threshold_23_75 : ∀ i ∈ List.range 1, ThresholdAt 23 (75+i) := by decide +kernel

theorem threshold_23_76 : ∀ i ∈ List.range 1, ThresholdAt 23 (76+i) := by decide +kernel

theorem threshold_23_77 : ∀ i ∈ List.range 1, ThresholdAt 23 (77+i) := by decide +kernel

theorem threshold_23_78 : ∀ i ∈ List.range 1, ThresholdAt 23 (78+i) := by decide +kernel

theorem threshold_23_79 : ∀ i ∈ List.range 1, ThresholdAt 23 (79+i) := by decide +kernel

theorem threshold_23_80 : ∀ i ∈ List.range 1, ThresholdAt 23 (80+i) := by decide +kernel

theorem threshold_23_81 : ∀ i ∈ List.range 1, ThresholdAt 23 (81+i) := by decide +kernel

theorem threshold_23_82 : ∀ i ∈ List.range 1, ThresholdAt 23 (82+i) := by decide +kernel

theorem threshold_23_83 : ∀ i ∈ List.range 1, ThresholdAt 23 (83+i) := by decide +kernel

theorem threshold_23_84 : ∀ i ∈ List.range 1, ThresholdAt 23 (84+i) := by decide +kernel

theorem threshold_23_85 : ∀ i ∈ List.range 1, ThresholdAt 23 (85+i) := by decide +kernel

theorem threshold_23_86 : ∀ i ∈ List.range 1, ThresholdAt 23 (86+i) := by decide +kernel

theorem threshold_23_87 : ∀ i ∈ List.range 1, ThresholdAt 23 (87+i) := by decide +kernel

theorem threshold_23_88 : ∀ i ∈ List.range 1, ThresholdAt 23 (88+i) := by decide +kernel

theorem threshold_23_89 : ∀ i ∈ List.range 1, ThresholdAt 23 (89+i) := by decide +kernel

theorem threshold_23_90 : ∀ i ∈ List.range 1, ThresholdAt 23 (90+i) := by decide +kernel

theorem threshold_23_91 : ∀ i ∈ List.range 1, ThresholdAt 23 (91+i) := by decide +kernel

theorem threshold_23_92 : ∀ i ∈ List.range 1, ThresholdAt 23 (92+i) := by decide +kernel

theorem threshold_23_93 : ∀ i ∈ List.range 1, ThresholdAt 23 (93+i) := by decide +kernel

theorem threshold_23_94 : ∀ i ∈ List.range 1, ThresholdAt 23 (94+i) := by decide +kernel

theorem threshold_23_95 : ∀ i ∈ List.range 1, ThresholdAt 23 (95+i) := by decide +kernel

theorem threshold_23_96 : ∀ i ∈ List.range 1, ThresholdAt 23 (96+i) := by decide +kernel

theorem threshold_23_97 : ∀ i ∈ List.range 1, ThresholdAt 23 (97+i) := by decide +kernel

theorem threshold_23_98 : ∀ i ∈ List.range 1, ThresholdAt 23 (98+i) := by decide +kernel

theorem threshold_23_99 : ∀ i ∈ List.range 1, ThresholdAt 23 (99+i) := by decide +kernel

theorem threshold_23_100 : ∀ i ∈ List.range 1, ThresholdAt 23 (100+i) := by decide +kernel

theorem threshold_23_101 : ∀ i ∈ List.range 1, ThresholdAt 23 (101+i) := by decide +kernel

theorem threshold_23_102 : ∀ i ∈ List.range 1, ThresholdAt 23 (102+i) := by decide +kernel

theorem threshold_23_103 : ∀ i ∈ List.range 1, ThresholdAt 23 (103+i) := by decide +kernel

theorem threshold_23_104 : ∀ i ∈ List.range 1, ThresholdAt 23 (104+i) := by decide +kernel

theorem threshold_23_105 : ∀ i ∈ List.range 1, ThresholdAt 23 (105+i) := by decide +kernel

theorem threshold_23_106 : ∀ i ∈ List.range 1, ThresholdAt 23 (106+i) := by decide +kernel

theorem threshold_23_107 : ∀ i ∈ List.range 1, ThresholdAt 23 (107+i) := by decide +kernel

theorem threshold_23_108 : ∀ i ∈ List.range 1, ThresholdAt 23 (108+i) := by decide +kernel

theorem threshold_23_109 : ∀ i ∈ List.range 1, ThresholdAt 23 (109+i) := by decide +kernel

theorem threshold_23_110 : ∀ i ∈ List.range 1, ThresholdAt 23 (110+i) := by decide +kernel

theorem threshold_23_111 : ∀ i ∈ List.range 1, ThresholdAt 23 (111+i) := by decide +kernel

theorem threshold_23_112 : ∀ i ∈ List.range 1, ThresholdAt 23 (112+i) := by decide +kernel

theorem threshold_23_113 : ∀ i ∈ List.range 1, ThresholdAt 23 (113+i) := by decide +kernel

theorem threshold_23_114 : ∀ i ∈ List.range 1, ThresholdAt 23 (114+i) := by decide +kernel

theorem threshold_23_115 : ∀ i ∈ List.range 1, ThresholdAt 23 (115+i) := by decide +kernel

theorem threshold_23_116 : ∀ i ∈ List.range 1, ThresholdAt 23 (116+i) := by decide +kernel

theorem threshold_23_117 : ∀ i ∈ List.range 1, ThresholdAt 23 (117+i) := by decide +kernel

theorem threshold_23_118 : ∀ i ∈ List.range 1, ThresholdAt 23 (118+i) := by decide +kernel

theorem threshold_23_119 : ∀ i ∈ List.range 1, ThresholdAt 23 (119+i) := by decide +kernel

theorem threshold_23_120 : ∀ i ∈ List.range 1, ThresholdAt 23 (120+i) := by decide +kernel

theorem threshold_23_121 : ∀ i ∈ List.range 1, ThresholdAt 23 (121+i) := by decide +kernel

theorem threshold_23_122 : ∀ i ∈ List.range 1, ThresholdAt 23 (122+i) := by decide +kernel

theorem threshold_23_123 : ∀ i ∈ List.range 1, ThresholdAt 23 (123+i) := by decide +kernel

theorem threshold_23_124 : ∀ i ∈ List.range 1, ThresholdAt 23 (124+i) := by decide +kernel

theorem threshold_23_125 : ∀ i ∈ List.range 1, ThresholdAt 23 (125+i) := by decide +kernel

theorem threshold_23_126 : ∀ i ∈ List.range 1, ThresholdAt 23 (126+i) := by decide +kernel

theorem threshold_23 (v : ℕ) (hv : v ∈ List.range 127) : ThresholdAt 23 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 23 v)
  have h := (join 0 63 64 (join 0 31 32 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_23_0 (join 1 1 1 threshold_23_1 threshold_23_2)) (join 3 2 2 (join 3 1 1 threshold_23_3 threshold_23_4) (join 5 1 1 threshold_23_5 threshold_23_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_23_7 threshold_23_8) (join 9 1 1 threshold_23_9 threshold_23_10)) (join 11 2 2 (join 11 1 1 threshold_23_11 threshold_23_12) (join 13 1 1 threshold_23_13 threshold_23_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_23_15 threshold_23_16) (join 17 1 1 threshold_23_17 threshold_23_18)) (join 19 2 2 (join 19 1 1 threshold_23_19 threshold_23_20) (join 21 1 1 threshold_23_21 threshold_23_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_23_23 threshold_23_24) (join 25 1 1 threshold_23_25 threshold_23_26)) (join 27 2 2 (join 27 1 1 threshold_23_27 threshold_23_28) (join 29 1 1 threshold_23_29 threshold_23_30))))) (join 31 16 16 (join 31 8 8 (join 31 4 4 (join 31 2 2 (join 31 1 1 threshold_23_31 threshold_23_32) (join 33 1 1 threshold_23_33 threshold_23_34)) (join 35 2 2 (join 35 1 1 threshold_23_35 threshold_23_36) (join 37 1 1 threshold_23_37 threshold_23_38))) (join 39 4 4 (join 39 2 2 (join 39 1 1 threshold_23_39 threshold_23_40) (join 41 1 1 threshold_23_41 threshold_23_42)) (join 43 2 2 (join 43 1 1 threshold_23_43 threshold_23_44) (join 45 1 1 threshold_23_45 threshold_23_46)))) (join 47 8 8 (join 47 4 4 (join 47 2 2 (join 47 1 1 threshold_23_47 threshold_23_48) (join 49 1 1 threshold_23_49 threshold_23_50)) (join 51 2 2 (join 51 1 1 threshold_23_51 threshold_23_52) (join 53 1 1 threshold_23_53 threshold_23_54))) (join 55 4 4 (join 55 2 2 (join 55 1 1 threshold_23_55 threshold_23_56) (join 57 1 1 threshold_23_57 threshold_23_58)) (join 59 2 2 (join 59 1 1 threshold_23_59 threshold_23_60) (join 61 1 1 threshold_23_61 threshold_23_62)))))) (join 63 32 32 (join 63 16 16 (join 63 8 8 (join 63 4 4 (join 63 2 2 (join 63 1 1 threshold_23_63 threshold_23_64) (join 65 1 1 threshold_23_65 threshold_23_66)) (join 67 2 2 (join 67 1 1 threshold_23_67 threshold_23_68) (join 69 1 1 threshold_23_69 threshold_23_70))) (join 71 4 4 (join 71 2 2 (join 71 1 1 threshold_23_71 threshold_23_72) (join 73 1 1 threshold_23_73 threshold_23_74)) (join 75 2 2 (join 75 1 1 threshold_23_75 threshold_23_76) (join 77 1 1 threshold_23_77 threshold_23_78)))) (join 79 8 8 (join 79 4 4 (join 79 2 2 (join 79 1 1 threshold_23_79 threshold_23_80) (join 81 1 1 threshold_23_81 threshold_23_82)) (join 83 2 2 (join 83 1 1 threshold_23_83 threshold_23_84) (join 85 1 1 threshold_23_85 threshold_23_86))) (join 87 4 4 (join 87 2 2 (join 87 1 1 threshold_23_87 threshold_23_88) (join 89 1 1 threshold_23_89 threshold_23_90)) (join 91 2 2 (join 91 1 1 threshold_23_91 threshold_23_92) (join 93 1 1 threshold_23_93 threshold_23_94))))) (join 95 16 16 (join 95 8 8 (join 95 4 4 (join 95 2 2 (join 95 1 1 threshold_23_95 threshold_23_96) (join 97 1 1 threshold_23_97 threshold_23_98)) (join 99 2 2 (join 99 1 1 threshold_23_99 threshold_23_100) (join 101 1 1 threshold_23_101 threshold_23_102))) (join 103 4 4 (join 103 2 2 (join 103 1 1 threshold_23_103 threshold_23_104) (join 105 1 1 threshold_23_105 threshold_23_106)) (join 107 2 2 (join 107 1 1 threshold_23_107 threshold_23_108) (join 109 1 1 threshold_23_109 threshold_23_110)))) (join 111 8 8 (join 111 4 4 (join 111 2 2 (join 111 1 1 threshold_23_111 threshold_23_112) (join 113 1 1 threshold_23_113 threshold_23_114)) (join 115 2 2 (join 115 1 1 threshold_23_115 threshold_23_116) (join 117 1 1 threshold_23_117 threshold_23_118))) (join 119 4 4 (join 119 2 2 (join 119 1 1 threshold_23_119 threshold_23_120) (join 121 1 1 threshold_23_121 threshold_23_122)) (join 123 2 2 (join 123 1 1 threshold_23_123 threshold_23_124) (join 125 1 1 threshold_23_125 threshold_23_126)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_23_0 : ∀ i ∈ List.range 4, LedgerAt 23 (0+i) := by decide +kernel

theorem ledger_23_4 : ∀ i ∈ List.range 4, LedgerAt 23 (4+i) := by decide +kernel

theorem ledger_23_8 : ∀ i ∈ List.range 4, LedgerAt 23 (8+i) := by decide +kernel

theorem ledger_23_12 : ∀ i ∈ List.range 4, LedgerAt 23 (12+i) := by decide +kernel

theorem ledger_23_16 : ∀ i ∈ List.range 4, LedgerAt 23 (16+i) := by decide +kernel

theorem ledger_23_20 : ∀ i ∈ List.range 4, LedgerAt 23 (20+i) := by decide +kernel

theorem ledger_23_24 : ∀ i ∈ List.range 4, LedgerAt 23 (24+i) := by decide +kernel

theorem ledger_23_28 : ∀ i ∈ List.range 4, LedgerAt 23 (28+i) := by decide +kernel

theorem ledger_23_32 : ∀ i ∈ List.range 4, LedgerAt 23 (32+i) := by decide +kernel

theorem ledger_23_36 : ∀ i ∈ List.range 4, LedgerAt 23 (36+i) := by decide +kernel

theorem ledger_23_40 : ∀ i ∈ List.range 4, LedgerAt 23 (40+i) := by decide +kernel

theorem ledger_23_44 : ∀ i ∈ List.range 4, LedgerAt 23 (44+i) := by decide +kernel

theorem ledger_23_48 : ∀ i ∈ List.range 4, LedgerAt 23 (48+i) := by decide +kernel

theorem ledger_23_52 : ∀ i ∈ List.range 4, LedgerAt 23 (52+i) := by decide +kernel

theorem ledger_23_56 : ∀ i ∈ List.range 4, LedgerAt 23 (56+i) := by decide +kernel

theorem ledger_23_60 : ∀ i ∈ List.range 4, LedgerAt 23 (60+i) := by decide +kernel

theorem ledger_23_64 : ∀ i ∈ List.range 4, LedgerAt 23 (64+i) := by decide +kernel

theorem ledger_23_68 : ∀ i ∈ List.range 4, LedgerAt 23 (68+i) := by decide +kernel

theorem ledger_23_72 : ∀ i ∈ List.range 4, LedgerAt 23 (72+i) := by decide +kernel

theorem ledger_23_76 : ∀ i ∈ List.range 4, LedgerAt 23 (76+i) := by decide +kernel

theorem ledger_23_80 : ∀ i ∈ List.range 4, LedgerAt 23 (80+i) := by decide +kernel

theorem ledger_23_84 : ∀ i ∈ List.range 4, LedgerAt 23 (84+i) := by decide +kernel

theorem ledger_23_88 : ∀ i ∈ List.range 4, LedgerAt 23 (88+i) := by decide +kernel

theorem ledger_23_92 : ∀ i ∈ List.range 4, LedgerAt 23 (92+i) := by decide +kernel

theorem ledger_23_96 : ∀ i ∈ List.range 4, LedgerAt 23 (96+i) := by decide +kernel

theorem ledger_23_100 : ∀ i ∈ List.range 4, LedgerAt 23 (100+i) := by decide +kernel

theorem ledger_23_104 : ∀ i ∈ List.range 4, LedgerAt 23 (104+i) := by decide +kernel

theorem ledger_23_108 : ∀ i ∈ List.range 4, LedgerAt 23 (108+i) := by decide +kernel

theorem ledger_23_112 : ∀ i ∈ List.range 4, LedgerAt 23 (112+i) := by decide +kernel

theorem ledger_23_116 : ∀ i ∈ List.range 4, LedgerAt 23 (116+i) := by decide +kernel

theorem ledger_23_120 : ∀ i ∈ List.range 4, LedgerAt 23 (120+i) := by decide +kernel

theorem ledger_23_124 : ∀ i ∈ List.range 3, LedgerAt 23 (124+i) := by decide +kernel

theorem ledger_23 (v : ℕ) (hv : v ∈ List.range 127) : LedgerAt 23 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 23 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_23_0 ledger_23_4) (join 8 4 4 ledger_23_8 ledger_23_12)) (join 16 8 8 (join 16 4 4 ledger_23_16 ledger_23_20) (join 24 4 4 ledger_23_24 ledger_23_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_23_32 ledger_23_36) (join 40 4 4 ledger_23_40 ledger_23_44)) (join 48 8 8 (join 48 4 4 ledger_23_48 ledger_23_52) (join 56 4 4 ledger_23_56 ledger_23_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_23_64 ledger_23_68) (join 72 4 4 ledger_23_72 ledger_23_76)) (join 80 8 8 (join 80 4 4 ledger_23_80 ledger_23_84) (join 88 4 4 ledger_23_88 ledger_23_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 ledger_23_96 ledger_23_100) (join 104 4 4 ledger_23_104 ledger_23_108)) (join 112 8 7 (join 112 4 4 ledger_23_112 ledger_23_116) (join 120 4 3 ledger_23_120 ledger_23_124)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
