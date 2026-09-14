import ProximityPrize.SubmissionLower.HigherAffineCheckedR316810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
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

theorem single_32_116 : ∀ i ∈ List.range 4, SingleAt 32 (116+i) := by decide +kernel

theorem single_32_120 : ∀ i ∈ List.range 4, SingleAt 32 (120+i) := by decide +kernel

theorem single_32_124 : ∀ i ∈ List.range 1, SingleAt 32 (124+i) := by decide +kernel

theorem single_32 (v : ℕ) (hv : v ∈ List.range 125) : SingleAt 32 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 32 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_32_0 single_32_4) (join 8 4 4 single_32_8 single_32_12)) (join 16 8 8 (join 16 4 4 single_32_16 single_32_20) (join 24 4 4 single_32_24 single_32_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_32_32 single_32_36) (join 40 4 4 single_32_40 single_32_44)) (join 48 8 8 (join 48 4 4 single_32_48 single_32_52) (join 56 4 4 single_32_56 single_32_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_32_64 single_32_68) (join 72 4 4 single_32_72 single_32_76)) (join 80 8 8 (join 80 4 4 single_32_80 single_32_84) (join 88 4 4 single_32_88 single_32_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 single_32_96 single_32_100) (join 104 4 4 single_32_104 single_32_108)) (join 112 8 5 (join 112 4 4 single_32_112 single_32_116) (join 120 4 1 single_32_120 single_32_124)))))
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

theorem phase_32_116 : ∀ i ∈ List.range 4, PhaseAt 32 (116+i) := by decide +kernel

theorem phase_32_120 : ∀ i ∈ List.range 4, PhaseAt 32 (120+i) := by decide +kernel

theorem phase_32_124 : ∀ i ∈ List.range 1, PhaseAt 32 (124+i) := by decide +kernel

theorem phase_32 (v : ℕ) (hv : v ∈ List.range 125) : PhaseAt 32 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 32 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_32_0 phase_32_4) (join 8 4 4 phase_32_8 phase_32_12)) (join 16 8 8 (join 16 4 4 phase_32_16 phase_32_20) (join 24 4 4 phase_32_24 phase_32_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_32_32 phase_32_36) (join 40 4 4 phase_32_40 phase_32_44)) (join 48 8 8 (join 48 4 4 phase_32_48 phase_32_52) (join 56 4 4 phase_32_56 phase_32_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_32_64 phase_32_68) (join 72 4 4 phase_32_72 phase_32_76)) (join 80 8 8 (join 80 4 4 phase_32_80 phase_32_84) (join 88 4 4 phase_32_88 phase_32_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 phase_32_96 phase_32_100) (join 104 4 4 phase_32_104 phase_32_108)) (join 112 8 5 (join 112 4 4 phase_32_112 phase_32_116) (join 120 4 1 phase_32_120 phase_32_124)))))
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

theorem threshold_32_118 : ∀ i ∈ List.range 1, ThresholdAt 32 (118+i) := by decide +kernel

theorem threshold_32_119 : ∀ i ∈ List.range 1, ThresholdAt 32 (119+i) := by decide +kernel

theorem threshold_32_120 : ∀ i ∈ List.range 1, ThresholdAt 32 (120+i) := by decide +kernel

theorem threshold_32_121 : ∀ i ∈ List.range 1, ThresholdAt 32 (121+i) := by decide +kernel

theorem threshold_32_122 : ∀ i ∈ List.range 1, ThresholdAt 32 (122+i) := by decide +kernel

theorem threshold_32_123 : ∀ i ∈ List.range 1, ThresholdAt 32 (123+i) := by decide +kernel

theorem threshold_32_124 : ∀ i ∈ List.range 1, ThresholdAt 32 (124+i) := by decide +kernel

theorem threshold_32 (v : ℕ) (hv : v ∈ List.range 125) : ThresholdAt 32 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 32 v)
  have h := (join 0 62 63 (join 0 31 31 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_32_0 (join 1 1 1 threshold_32_1 threshold_32_2)) (join 3 2 2 (join 3 1 1 threshold_32_3 threshold_32_4) (join 5 1 1 threshold_32_5 threshold_32_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_32_7 threshold_32_8) (join 9 1 1 threshold_32_9 threshold_32_10)) (join 11 2 2 (join 11 1 1 threshold_32_11 threshold_32_12) (join 13 1 1 threshold_32_13 threshold_32_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_32_15 threshold_32_16) (join 17 1 1 threshold_32_17 threshold_32_18)) (join 19 2 2 (join 19 1 1 threshold_32_19 threshold_32_20) (join 21 1 1 threshold_32_21 threshold_32_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_32_23 threshold_32_24) (join 25 1 1 threshold_32_25 threshold_32_26)) (join 27 2 2 (join 27 1 1 threshold_32_27 threshold_32_28) (join 29 1 1 threshold_32_29 threshold_32_30))))) (join 31 15 16 (join 31 7 8 (join 31 3 4 (join 31 1 2 threshold_32_31 (join 32 1 1 threshold_32_32 threshold_32_33)) (join 34 2 2 (join 34 1 1 threshold_32_34 threshold_32_35) (join 36 1 1 threshold_32_36 threshold_32_37))) (join 38 4 4 (join 38 2 2 (join 38 1 1 threshold_32_38 threshold_32_39) (join 40 1 1 threshold_32_40 threshold_32_41)) (join 42 2 2 (join 42 1 1 threshold_32_42 threshold_32_43) (join 44 1 1 threshold_32_44 threshold_32_45)))) (join 46 8 8 (join 46 4 4 (join 46 2 2 (join 46 1 1 threshold_32_46 threshold_32_47) (join 48 1 1 threshold_32_48 threshold_32_49)) (join 50 2 2 (join 50 1 1 threshold_32_50 threshold_32_51) (join 52 1 1 threshold_32_52 threshold_32_53))) (join 54 4 4 (join 54 2 2 (join 54 1 1 threshold_32_54 threshold_32_55) (join 56 1 1 threshold_32_56 threshold_32_57)) (join 58 2 2 (join 58 1 1 threshold_32_58 threshold_32_59) (join 60 1 1 threshold_32_60 threshold_32_61)))))) (join 62 31 32 (join 62 15 16 (join 62 7 8 (join 62 3 4 (join 62 1 2 threshold_32_62 (join 63 1 1 threshold_32_63 threshold_32_64)) (join 65 2 2 (join 65 1 1 threshold_32_65 threshold_32_66) (join 67 1 1 threshold_32_67 threshold_32_68))) (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_32_69 threshold_32_70) (join 71 1 1 threshold_32_71 threshold_32_72)) (join 73 2 2 (join 73 1 1 threshold_32_73 threshold_32_74) (join 75 1 1 threshold_32_75 threshold_32_76)))) (join 77 8 8 (join 77 4 4 (join 77 2 2 (join 77 1 1 threshold_32_77 threshold_32_78) (join 79 1 1 threshold_32_79 threshold_32_80)) (join 81 2 2 (join 81 1 1 threshold_32_81 threshold_32_82) (join 83 1 1 threshold_32_83 threshold_32_84))) (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_32_85 threshold_32_86) (join 87 1 1 threshold_32_87 threshold_32_88)) (join 89 2 2 (join 89 1 1 threshold_32_89 threshold_32_90) (join 91 1 1 threshold_32_91 threshold_32_92))))) (join 93 16 16 (join 93 8 8 (join 93 4 4 (join 93 2 2 (join 93 1 1 threshold_32_93 threshold_32_94) (join 95 1 1 threshold_32_95 threshold_32_96)) (join 97 2 2 (join 97 1 1 threshold_32_97 threshold_32_98) (join 99 1 1 threshold_32_99 threshold_32_100))) (join 101 4 4 (join 101 2 2 (join 101 1 1 threshold_32_101 threshold_32_102) (join 103 1 1 threshold_32_103 threshold_32_104)) (join 105 2 2 (join 105 1 1 threshold_32_105 threshold_32_106) (join 107 1 1 threshold_32_107 threshold_32_108)))) (join 109 8 8 (join 109 4 4 (join 109 2 2 (join 109 1 1 threshold_32_109 threshold_32_110) (join 111 1 1 threshold_32_111 threshold_32_112)) (join 113 2 2 (join 113 1 1 threshold_32_113 threshold_32_114) (join 115 1 1 threshold_32_115 threshold_32_116))) (join 117 4 4 (join 117 2 2 (join 117 1 1 threshold_32_117 threshold_32_118) (join 119 1 1 threshold_32_119 threshold_32_120)) (join 121 2 2 (join 121 1 1 threshold_32_121 threshold_32_122) (join 123 1 1 threshold_32_123 threshold_32_124)))))))
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

theorem ledger_32_116 : ∀ i ∈ List.range 4, LedgerAt 32 (116+i) := by decide +kernel

theorem ledger_32_120 : ∀ i ∈ List.range 4, LedgerAt 32 (120+i) := by decide +kernel

theorem ledger_32_124 : ∀ i ∈ List.range 1, LedgerAt 32 (124+i) := by decide +kernel

theorem ledger_32 (v : ℕ) (hv : v ∈ List.range 125) : LedgerAt 32 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 32 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_32_0 ledger_32_4) (join 8 4 4 ledger_32_8 ledger_32_12)) (join 16 8 8 (join 16 4 4 ledger_32_16 ledger_32_20) (join 24 4 4 ledger_32_24 ledger_32_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_32_32 ledger_32_36) (join 40 4 4 ledger_32_40 ledger_32_44)) (join 48 8 8 (join 48 4 4 ledger_32_48 ledger_32_52) (join 56 4 4 ledger_32_56 ledger_32_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_32_64 ledger_32_68) (join 72 4 4 ledger_32_72 ledger_32_76)) (join 80 8 8 (join 80 4 4 ledger_32_80 ledger_32_84) (join 88 4 4 ledger_32_88 ledger_32_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 ledger_32_96 ledger_32_100) (join 104 4 4 ledger_32_104 ledger_32_108)) (join 112 8 5 (join 112 4 4 ledger_32_112 ledger_32_116) (join 120 4 1 ledger_32_120 ledger_32_124)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
