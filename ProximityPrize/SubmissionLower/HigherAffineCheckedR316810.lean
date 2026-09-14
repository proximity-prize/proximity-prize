import ProximityPrize.SubmissionLower.HigherAffineCheckedR306810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
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

theorem single_31_116 : ∀ i ∈ List.range 4, SingleAt 31 (116+i) := by decide +kernel

theorem single_31_120 : ∀ i ∈ List.range 4, SingleAt 31 (120+i) := by decide +kernel

theorem single_31_124 : ∀ i ∈ List.range 2, SingleAt 31 (124+i) := by decide +kernel

theorem single_31 (v : ℕ) (hv : v ∈ List.range 126) : SingleAt 31 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 31 v)
  have h := (join 0 64 62 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_31_0 single_31_4) (join 8 4 4 single_31_8 single_31_12)) (join 16 8 8 (join 16 4 4 single_31_16 single_31_20) (join 24 4 4 single_31_24 single_31_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_31_32 single_31_36) (join 40 4 4 single_31_40 single_31_44)) (join 48 8 8 (join 48 4 4 single_31_48 single_31_52) (join 56 4 4 single_31_56 single_31_60)))) (join 64 32 30 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_31_64 single_31_68) (join 72 4 4 single_31_72 single_31_76)) (join 80 8 8 (join 80 4 4 single_31_80 single_31_84) (join 88 4 4 single_31_88 single_31_92))) (join 96 16 14 (join 96 8 8 (join 96 4 4 single_31_96 single_31_100) (join 104 4 4 single_31_104 single_31_108)) (join 112 8 6 (join 112 4 4 single_31_112 single_31_116) (join 120 4 2 single_31_120 single_31_124)))))
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

theorem phase_31_116 : ∀ i ∈ List.range 4, PhaseAt 31 (116+i) := by decide +kernel

theorem phase_31_120 : ∀ i ∈ List.range 4, PhaseAt 31 (120+i) := by decide +kernel

theorem phase_31_124 : ∀ i ∈ List.range 2, PhaseAt 31 (124+i) := by decide +kernel

theorem phase_31 (v : ℕ) (hv : v ∈ List.range 126) : PhaseAt 31 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 31 v)
  have h := (join 0 64 62 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_31_0 phase_31_4) (join 8 4 4 phase_31_8 phase_31_12)) (join 16 8 8 (join 16 4 4 phase_31_16 phase_31_20) (join 24 4 4 phase_31_24 phase_31_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_31_32 phase_31_36) (join 40 4 4 phase_31_40 phase_31_44)) (join 48 8 8 (join 48 4 4 phase_31_48 phase_31_52) (join 56 4 4 phase_31_56 phase_31_60)))) (join 64 32 30 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_31_64 phase_31_68) (join 72 4 4 phase_31_72 phase_31_76)) (join 80 8 8 (join 80 4 4 phase_31_80 phase_31_84) (join 88 4 4 phase_31_88 phase_31_92))) (join 96 16 14 (join 96 8 8 (join 96 4 4 phase_31_96 phase_31_100) (join 104 4 4 phase_31_104 phase_31_108)) (join 112 8 6 (join 112 4 4 phase_31_112 phase_31_116) (join 120 4 2 phase_31_120 phase_31_124)))))
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

theorem threshold_31_119 : ∀ i ∈ List.range 1, ThresholdAt 31 (119+i) := by decide +kernel

theorem threshold_31_120 : ∀ i ∈ List.range 1, ThresholdAt 31 (120+i) := by decide +kernel

theorem threshold_31_121 : ∀ i ∈ List.range 1, ThresholdAt 31 (121+i) := by decide +kernel

theorem threshold_31_122 : ∀ i ∈ List.range 1, ThresholdAt 31 (122+i) := by decide +kernel

theorem threshold_31_123 : ∀ i ∈ List.range 1, ThresholdAt 31 (123+i) := by decide +kernel

theorem threshold_31_124 : ∀ i ∈ List.range 1, ThresholdAt 31 (124+i) := by decide +kernel

theorem threshold_31_125 : ∀ i ∈ List.range 1, ThresholdAt 31 (125+i) := by decide +kernel

theorem threshold_31 (v : ℕ) (hv : v ∈ List.range 126) : ThresholdAt 31 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 31 v)
  have h := (join 0 63 63 (join 0 31 32 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_31_0 (join 1 1 1 threshold_31_1 threshold_31_2)) (join 3 2 2 (join 3 1 1 threshold_31_3 threshold_31_4) (join 5 1 1 threshold_31_5 threshold_31_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_31_7 threshold_31_8) (join 9 1 1 threshold_31_9 threshold_31_10)) (join 11 2 2 (join 11 1 1 threshold_31_11 threshold_31_12) (join 13 1 1 threshold_31_13 threshold_31_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_31_15 threshold_31_16) (join 17 1 1 threshold_31_17 threshold_31_18)) (join 19 2 2 (join 19 1 1 threshold_31_19 threshold_31_20) (join 21 1 1 threshold_31_21 threshold_31_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_31_23 threshold_31_24) (join 25 1 1 threshold_31_25 threshold_31_26)) (join 27 2 2 (join 27 1 1 threshold_31_27 threshold_31_28) (join 29 1 1 threshold_31_29 threshold_31_30))))) (join 31 16 16 (join 31 8 8 (join 31 4 4 (join 31 2 2 (join 31 1 1 threshold_31_31 threshold_31_32) (join 33 1 1 threshold_31_33 threshold_31_34)) (join 35 2 2 (join 35 1 1 threshold_31_35 threshold_31_36) (join 37 1 1 threshold_31_37 threshold_31_38))) (join 39 4 4 (join 39 2 2 (join 39 1 1 threshold_31_39 threshold_31_40) (join 41 1 1 threshold_31_41 threshold_31_42)) (join 43 2 2 (join 43 1 1 threshold_31_43 threshold_31_44) (join 45 1 1 threshold_31_45 threshold_31_46)))) (join 47 8 8 (join 47 4 4 (join 47 2 2 (join 47 1 1 threshold_31_47 threshold_31_48) (join 49 1 1 threshold_31_49 threshold_31_50)) (join 51 2 2 (join 51 1 1 threshold_31_51 threshold_31_52) (join 53 1 1 threshold_31_53 threshold_31_54))) (join 55 4 4 (join 55 2 2 (join 55 1 1 threshold_31_55 threshold_31_56) (join 57 1 1 threshold_31_57 threshold_31_58)) (join 59 2 2 (join 59 1 1 threshold_31_59 threshold_31_60) (join 61 1 1 threshold_31_61 threshold_31_62)))))) (join 63 31 32 (join 63 15 16 (join 63 7 8 (join 63 3 4 (join 63 1 2 threshold_31_63 (join 64 1 1 threshold_31_64 threshold_31_65)) (join 66 2 2 (join 66 1 1 threshold_31_66 threshold_31_67) (join 68 1 1 threshold_31_68 threshold_31_69))) (join 70 4 4 (join 70 2 2 (join 70 1 1 threshold_31_70 threshold_31_71) (join 72 1 1 threshold_31_72 threshold_31_73)) (join 74 2 2 (join 74 1 1 threshold_31_74 threshold_31_75) (join 76 1 1 threshold_31_76 threshold_31_77)))) (join 78 8 8 (join 78 4 4 (join 78 2 2 (join 78 1 1 threshold_31_78 threshold_31_79) (join 80 1 1 threshold_31_80 threshold_31_81)) (join 82 2 2 (join 82 1 1 threshold_31_82 threshold_31_83) (join 84 1 1 threshold_31_84 threshold_31_85))) (join 86 4 4 (join 86 2 2 (join 86 1 1 threshold_31_86 threshold_31_87) (join 88 1 1 threshold_31_88 threshold_31_89)) (join 90 2 2 (join 90 1 1 threshold_31_90 threshold_31_91) (join 92 1 1 threshold_31_92 threshold_31_93))))) (join 94 16 16 (join 94 8 8 (join 94 4 4 (join 94 2 2 (join 94 1 1 threshold_31_94 threshold_31_95) (join 96 1 1 threshold_31_96 threshold_31_97)) (join 98 2 2 (join 98 1 1 threshold_31_98 threshold_31_99) (join 100 1 1 threshold_31_100 threshold_31_101))) (join 102 4 4 (join 102 2 2 (join 102 1 1 threshold_31_102 threshold_31_103) (join 104 1 1 threshold_31_104 threshold_31_105)) (join 106 2 2 (join 106 1 1 threshold_31_106 threshold_31_107) (join 108 1 1 threshold_31_108 threshold_31_109)))) (join 110 8 8 (join 110 4 4 (join 110 2 2 (join 110 1 1 threshold_31_110 threshold_31_111) (join 112 1 1 threshold_31_112 threshold_31_113)) (join 114 2 2 (join 114 1 1 threshold_31_114 threshold_31_115) (join 116 1 1 threshold_31_116 threshold_31_117))) (join 118 4 4 (join 118 2 2 (join 118 1 1 threshold_31_118 threshold_31_119) (join 120 1 1 threshold_31_120 threshold_31_121)) (join 122 2 2 (join 122 1 1 threshold_31_122 threshold_31_123) (join 124 1 1 threshold_31_124 threshold_31_125)))))))
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

theorem ledger_31_116 : ∀ i ∈ List.range 4, LedgerAt 31 (116+i) := by decide +kernel

theorem ledger_31_120 : ∀ i ∈ List.range 4, LedgerAt 31 (120+i) := by decide +kernel

theorem ledger_31_124 : ∀ i ∈ List.range 2, LedgerAt 31 (124+i) := by decide +kernel

theorem ledger_31 (v : ℕ) (hv : v ∈ List.range 126) : LedgerAt 31 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 31 v)
  have h := (join 0 64 62 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_31_0 ledger_31_4) (join 8 4 4 ledger_31_8 ledger_31_12)) (join 16 8 8 (join 16 4 4 ledger_31_16 ledger_31_20) (join 24 4 4 ledger_31_24 ledger_31_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_31_32 ledger_31_36) (join 40 4 4 ledger_31_40 ledger_31_44)) (join 48 8 8 (join 48 4 4 ledger_31_48 ledger_31_52) (join 56 4 4 ledger_31_56 ledger_31_60)))) (join 64 32 30 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_31_64 ledger_31_68) (join 72 4 4 ledger_31_72 ledger_31_76)) (join 80 8 8 (join 80 4 4 ledger_31_80 ledger_31_84) (join 88 4 4 ledger_31_88 ledger_31_92))) (join 96 16 14 (join 96 8 8 (join 96 4 4 ledger_31_96 ledger_31_100) (join 104 4 4 ledger_31_104 ledger_31_108)) (join 112 8 6 (join 112 4 4 ledger_31_112 ledger_31_116) (join 120 4 2 ledger_31_120 ledger_31_124)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
