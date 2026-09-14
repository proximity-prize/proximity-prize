import ProximityPrize.SubmissionLower.HigherAffineCheckedR296810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
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

theorem single_30_120 : ∀ i ∈ List.range 4, SingleAt 30 (120+i) := by decide +kernel

theorem single_30_124 : ∀ i ∈ List.range 3, SingleAt 30 (124+i) := by decide +kernel

theorem single_30 (v : ℕ) (hv : v ∈ List.range 127) : SingleAt 30 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 30 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_30_0 single_30_4) (join 8 4 4 single_30_8 single_30_12)) (join 16 8 8 (join 16 4 4 single_30_16 single_30_20) (join 24 4 4 single_30_24 single_30_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_30_32 single_30_36) (join 40 4 4 single_30_40 single_30_44)) (join 48 8 8 (join 48 4 4 single_30_48 single_30_52) (join 56 4 4 single_30_56 single_30_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_30_64 single_30_68) (join 72 4 4 single_30_72 single_30_76)) (join 80 8 8 (join 80 4 4 single_30_80 single_30_84) (join 88 4 4 single_30_88 single_30_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 single_30_96 single_30_100) (join 104 4 4 single_30_104 single_30_108)) (join 112 8 7 (join 112 4 4 single_30_112 single_30_116) (join 120 4 3 single_30_120 single_30_124)))))
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

theorem phase_30_120 : ∀ i ∈ List.range 4, PhaseAt 30 (120+i) := by decide +kernel

theorem phase_30_124 : ∀ i ∈ List.range 3, PhaseAt 30 (124+i) := by decide +kernel

theorem phase_30 (v : ℕ) (hv : v ∈ List.range 127) : PhaseAt 30 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 30 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_30_0 phase_30_4) (join 8 4 4 phase_30_8 phase_30_12)) (join 16 8 8 (join 16 4 4 phase_30_16 phase_30_20) (join 24 4 4 phase_30_24 phase_30_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_30_32 phase_30_36) (join 40 4 4 phase_30_40 phase_30_44)) (join 48 8 8 (join 48 4 4 phase_30_48 phase_30_52) (join 56 4 4 phase_30_56 phase_30_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_30_64 phase_30_68) (join 72 4 4 phase_30_72 phase_30_76)) (join 80 8 8 (join 80 4 4 phase_30_80 phase_30_84) (join 88 4 4 phase_30_88 phase_30_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 phase_30_96 phase_30_100) (join 104 4 4 phase_30_104 phase_30_108)) (join 112 8 7 (join 112 4 4 phase_30_112 phase_30_116) (join 120 4 3 phase_30_120 phase_30_124)))))
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

theorem threshold_30_120 : ∀ i ∈ List.range 1, ThresholdAt 30 (120+i) := by decide +kernel

theorem threshold_30_121 : ∀ i ∈ List.range 1, ThresholdAt 30 (121+i) := by decide +kernel

theorem threshold_30_122 : ∀ i ∈ List.range 1, ThresholdAt 30 (122+i) := by decide +kernel

theorem threshold_30_123 : ∀ i ∈ List.range 1, ThresholdAt 30 (123+i) := by decide +kernel

theorem threshold_30_124 : ∀ i ∈ List.range 1, ThresholdAt 30 (124+i) := by decide +kernel

theorem threshold_30_125 : ∀ i ∈ List.range 1, ThresholdAt 30 (125+i) := by decide +kernel

theorem threshold_30_126 : ∀ i ∈ List.range 1, ThresholdAt 30 (126+i) := by decide +kernel

theorem threshold_30 (v : ℕ) (hv : v ∈ List.range 127) : ThresholdAt 30 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 30 v)
  have h := (join 0 63 64 (join 0 31 32 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_30_0 (join 1 1 1 threshold_30_1 threshold_30_2)) (join 3 2 2 (join 3 1 1 threshold_30_3 threshold_30_4) (join 5 1 1 threshold_30_5 threshold_30_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_30_7 threshold_30_8) (join 9 1 1 threshold_30_9 threshold_30_10)) (join 11 2 2 (join 11 1 1 threshold_30_11 threshold_30_12) (join 13 1 1 threshold_30_13 threshold_30_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_30_15 threshold_30_16) (join 17 1 1 threshold_30_17 threshold_30_18)) (join 19 2 2 (join 19 1 1 threshold_30_19 threshold_30_20) (join 21 1 1 threshold_30_21 threshold_30_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_30_23 threshold_30_24) (join 25 1 1 threshold_30_25 threshold_30_26)) (join 27 2 2 (join 27 1 1 threshold_30_27 threshold_30_28) (join 29 1 1 threshold_30_29 threshold_30_30))))) (join 31 16 16 (join 31 8 8 (join 31 4 4 (join 31 2 2 (join 31 1 1 threshold_30_31 threshold_30_32) (join 33 1 1 threshold_30_33 threshold_30_34)) (join 35 2 2 (join 35 1 1 threshold_30_35 threshold_30_36) (join 37 1 1 threshold_30_37 threshold_30_38))) (join 39 4 4 (join 39 2 2 (join 39 1 1 threshold_30_39 threshold_30_40) (join 41 1 1 threshold_30_41 threshold_30_42)) (join 43 2 2 (join 43 1 1 threshold_30_43 threshold_30_44) (join 45 1 1 threshold_30_45 threshold_30_46)))) (join 47 8 8 (join 47 4 4 (join 47 2 2 (join 47 1 1 threshold_30_47 threshold_30_48) (join 49 1 1 threshold_30_49 threshold_30_50)) (join 51 2 2 (join 51 1 1 threshold_30_51 threshold_30_52) (join 53 1 1 threshold_30_53 threshold_30_54))) (join 55 4 4 (join 55 2 2 (join 55 1 1 threshold_30_55 threshold_30_56) (join 57 1 1 threshold_30_57 threshold_30_58)) (join 59 2 2 (join 59 1 1 threshold_30_59 threshold_30_60) (join 61 1 1 threshold_30_61 threshold_30_62)))))) (join 63 32 32 (join 63 16 16 (join 63 8 8 (join 63 4 4 (join 63 2 2 (join 63 1 1 threshold_30_63 threshold_30_64) (join 65 1 1 threshold_30_65 threshold_30_66)) (join 67 2 2 (join 67 1 1 threshold_30_67 threshold_30_68) (join 69 1 1 threshold_30_69 threshold_30_70))) (join 71 4 4 (join 71 2 2 (join 71 1 1 threshold_30_71 threshold_30_72) (join 73 1 1 threshold_30_73 threshold_30_74)) (join 75 2 2 (join 75 1 1 threshold_30_75 threshold_30_76) (join 77 1 1 threshold_30_77 threshold_30_78)))) (join 79 8 8 (join 79 4 4 (join 79 2 2 (join 79 1 1 threshold_30_79 threshold_30_80) (join 81 1 1 threshold_30_81 threshold_30_82)) (join 83 2 2 (join 83 1 1 threshold_30_83 threshold_30_84) (join 85 1 1 threshold_30_85 threshold_30_86))) (join 87 4 4 (join 87 2 2 (join 87 1 1 threshold_30_87 threshold_30_88) (join 89 1 1 threshold_30_89 threshold_30_90)) (join 91 2 2 (join 91 1 1 threshold_30_91 threshold_30_92) (join 93 1 1 threshold_30_93 threshold_30_94))))) (join 95 16 16 (join 95 8 8 (join 95 4 4 (join 95 2 2 (join 95 1 1 threshold_30_95 threshold_30_96) (join 97 1 1 threshold_30_97 threshold_30_98)) (join 99 2 2 (join 99 1 1 threshold_30_99 threshold_30_100) (join 101 1 1 threshold_30_101 threshold_30_102))) (join 103 4 4 (join 103 2 2 (join 103 1 1 threshold_30_103 threshold_30_104) (join 105 1 1 threshold_30_105 threshold_30_106)) (join 107 2 2 (join 107 1 1 threshold_30_107 threshold_30_108) (join 109 1 1 threshold_30_109 threshold_30_110)))) (join 111 8 8 (join 111 4 4 (join 111 2 2 (join 111 1 1 threshold_30_111 threshold_30_112) (join 113 1 1 threshold_30_113 threshold_30_114)) (join 115 2 2 (join 115 1 1 threshold_30_115 threshold_30_116) (join 117 1 1 threshold_30_117 threshold_30_118))) (join 119 4 4 (join 119 2 2 (join 119 1 1 threshold_30_119 threshold_30_120) (join 121 1 1 threshold_30_121 threshold_30_122)) (join 123 2 2 (join 123 1 1 threshold_30_123 threshold_30_124) (join 125 1 1 threshold_30_125 threshold_30_126)))))))
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

theorem ledger_30_120 : ∀ i ∈ List.range 4, LedgerAt 30 (120+i) := by decide +kernel

theorem ledger_30_124 : ∀ i ∈ List.range 3, LedgerAt 30 (124+i) := by decide +kernel

theorem ledger_30 (v : ℕ) (hv : v ∈ List.range 127) : LedgerAt 30 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 30 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_30_0 ledger_30_4) (join 8 4 4 ledger_30_8 ledger_30_12)) (join 16 8 8 (join 16 4 4 ledger_30_16 ledger_30_20) (join 24 4 4 ledger_30_24 ledger_30_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_30_32 ledger_30_36) (join 40 4 4 ledger_30_40 ledger_30_44)) (join 48 8 8 (join 48 4 4 ledger_30_48 ledger_30_52) (join 56 4 4 ledger_30_56 ledger_30_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_30_64 ledger_30_68) (join 72 4 4 ledger_30_72 ledger_30_76)) (join 80 8 8 (join 80 4 4 ledger_30_80 ledger_30_84) (join 88 4 4 ledger_30_88 ledger_30_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 ledger_30_96 ledger_30_100) (join 104 4 4 ledger_30_104 ledger_30_108)) (join 112 8 7 (join 112 4 4 ledger_30_112 ledger_30_116) (join 120 4 3 ledger_30_120 ledger_30_124)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
