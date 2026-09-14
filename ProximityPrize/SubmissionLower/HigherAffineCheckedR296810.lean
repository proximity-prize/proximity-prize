import ProximityPrize.SubmissionLower.HigherAffineCheckedR286810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_29_0 : ∀ i ∈ List.range 4, SingleAt 29 (0+i) := by decide +kernel

theorem single_29_4 : ∀ i ∈ List.range 4, SingleAt 29 (4+i) := by decide +kernel

theorem single_29_8 : ∀ i ∈ List.range 4, SingleAt 29 (8+i) := by decide +kernel

theorem single_29_12 : ∀ i ∈ List.range 4, SingleAt 29 (12+i) := by decide +kernel

theorem single_29_16 : ∀ i ∈ List.range 4, SingleAt 29 (16+i) := by decide +kernel

theorem single_29_20 : ∀ i ∈ List.range 4, SingleAt 29 (20+i) := by decide +kernel

theorem single_29_24 : ∀ i ∈ List.range 4, SingleAt 29 (24+i) := by decide +kernel

theorem single_29_28 : ∀ i ∈ List.range 4, SingleAt 29 (28+i) := by decide +kernel

theorem single_29_32 : ∀ i ∈ List.range 4, SingleAt 29 (32+i) := by decide +kernel

theorem single_29_36 : ∀ i ∈ List.range 4, SingleAt 29 (36+i) := by decide +kernel

theorem single_29_40 : ∀ i ∈ List.range 4, SingleAt 29 (40+i) := by decide +kernel

theorem single_29_44 : ∀ i ∈ List.range 4, SingleAt 29 (44+i) := by decide +kernel

theorem single_29_48 : ∀ i ∈ List.range 4, SingleAt 29 (48+i) := by decide +kernel

theorem single_29_52 : ∀ i ∈ List.range 4, SingleAt 29 (52+i) := by decide +kernel

theorem single_29_56 : ∀ i ∈ List.range 4, SingleAt 29 (56+i) := by decide +kernel

theorem single_29_60 : ∀ i ∈ List.range 4, SingleAt 29 (60+i) := by decide +kernel

theorem single_29_64 : ∀ i ∈ List.range 4, SingleAt 29 (64+i) := by decide +kernel

theorem single_29_68 : ∀ i ∈ List.range 4, SingleAt 29 (68+i) := by decide +kernel

theorem single_29_72 : ∀ i ∈ List.range 4, SingleAt 29 (72+i) := by decide +kernel

theorem single_29_76 : ∀ i ∈ List.range 4, SingleAt 29 (76+i) := by decide +kernel

theorem single_29_80 : ∀ i ∈ List.range 4, SingleAt 29 (80+i) := by decide +kernel

theorem single_29_84 : ∀ i ∈ List.range 4, SingleAt 29 (84+i) := by decide +kernel

theorem single_29_88 : ∀ i ∈ List.range 4, SingleAt 29 (88+i) := by decide +kernel

theorem single_29_92 : ∀ i ∈ List.range 4, SingleAt 29 (92+i) := by decide +kernel

theorem single_29_96 : ∀ i ∈ List.range 4, SingleAt 29 (96+i) := by decide +kernel

theorem single_29_100 : ∀ i ∈ List.range 4, SingleAt 29 (100+i) := by decide +kernel

theorem single_29_104 : ∀ i ∈ List.range 4, SingleAt 29 (104+i) := by decide +kernel

theorem single_29_108 : ∀ i ∈ List.range 4, SingleAt 29 (108+i) := by decide +kernel

theorem single_29_112 : ∀ i ∈ List.range 4, SingleAt 29 (112+i) := by decide +kernel

theorem single_29_116 : ∀ i ∈ List.range 4, SingleAt 29 (116+i) := by decide +kernel

theorem single_29_120 : ∀ i ∈ List.range 4, SingleAt 29 (120+i) := by decide +kernel

theorem single_29_124 : ∀ i ∈ List.range 4, SingleAt 29 (124+i) := by decide +kernel

theorem single_29 (v : ℕ) (hv : v ∈ List.range 128) : SingleAt 29 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 29 v)
  have h := (join 0 64 64 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_29_0 single_29_4) (join 8 4 4 single_29_8 single_29_12)) (join 16 8 8 (join 16 4 4 single_29_16 single_29_20) (join 24 4 4 single_29_24 single_29_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_29_32 single_29_36) (join 40 4 4 single_29_40 single_29_44)) (join 48 8 8 (join 48 4 4 single_29_48 single_29_52) (join 56 4 4 single_29_56 single_29_60)))) (join 64 32 32 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_29_64 single_29_68) (join 72 4 4 single_29_72 single_29_76)) (join 80 8 8 (join 80 4 4 single_29_80 single_29_84) (join 88 4 4 single_29_88 single_29_92))) (join 96 16 16 (join 96 8 8 (join 96 4 4 single_29_96 single_29_100) (join 104 4 4 single_29_104 single_29_108)) (join 112 8 8 (join 112 4 4 single_29_112 single_29_116) (join 120 4 4 single_29_120 single_29_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_29_0 : ∀ i ∈ List.range 4, PhaseAt 29 (0+i) := by decide +kernel

theorem phase_29_4 : ∀ i ∈ List.range 4, PhaseAt 29 (4+i) := by decide +kernel

theorem phase_29_8 : ∀ i ∈ List.range 4, PhaseAt 29 (8+i) := by decide +kernel

theorem phase_29_12 : ∀ i ∈ List.range 4, PhaseAt 29 (12+i) := by decide +kernel

theorem phase_29_16 : ∀ i ∈ List.range 4, PhaseAt 29 (16+i) := by decide +kernel

theorem phase_29_20 : ∀ i ∈ List.range 4, PhaseAt 29 (20+i) := by decide +kernel

theorem phase_29_24 : ∀ i ∈ List.range 4, PhaseAt 29 (24+i) := by decide +kernel

theorem phase_29_28 : ∀ i ∈ List.range 4, PhaseAt 29 (28+i) := by decide +kernel

theorem phase_29_32 : ∀ i ∈ List.range 4, PhaseAt 29 (32+i) := by decide +kernel

theorem phase_29_36 : ∀ i ∈ List.range 4, PhaseAt 29 (36+i) := by decide +kernel

theorem phase_29_40 : ∀ i ∈ List.range 4, PhaseAt 29 (40+i) := by decide +kernel

theorem phase_29_44 : ∀ i ∈ List.range 4, PhaseAt 29 (44+i) := by decide +kernel

theorem phase_29_48 : ∀ i ∈ List.range 4, PhaseAt 29 (48+i) := by decide +kernel

theorem phase_29_52 : ∀ i ∈ List.range 4, PhaseAt 29 (52+i) := by decide +kernel

theorem phase_29_56 : ∀ i ∈ List.range 4, PhaseAt 29 (56+i) := by decide +kernel

theorem phase_29_60 : ∀ i ∈ List.range 4, PhaseAt 29 (60+i) := by decide +kernel

theorem phase_29_64 : ∀ i ∈ List.range 4, PhaseAt 29 (64+i) := by decide +kernel

theorem phase_29_68 : ∀ i ∈ List.range 4, PhaseAt 29 (68+i) := by decide +kernel

theorem phase_29_72 : ∀ i ∈ List.range 4, PhaseAt 29 (72+i) := by decide +kernel

theorem phase_29_76 : ∀ i ∈ List.range 4, PhaseAt 29 (76+i) := by decide +kernel

theorem phase_29_80 : ∀ i ∈ List.range 4, PhaseAt 29 (80+i) := by decide +kernel

theorem phase_29_84 : ∀ i ∈ List.range 4, PhaseAt 29 (84+i) := by decide +kernel

theorem phase_29_88 : ∀ i ∈ List.range 4, PhaseAt 29 (88+i) := by decide +kernel

theorem phase_29_92 : ∀ i ∈ List.range 4, PhaseAt 29 (92+i) := by decide +kernel

theorem phase_29_96 : ∀ i ∈ List.range 4, PhaseAt 29 (96+i) := by decide +kernel

theorem phase_29_100 : ∀ i ∈ List.range 4, PhaseAt 29 (100+i) := by decide +kernel

theorem phase_29_104 : ∀ i ∈ List.range 4, PhaseAt 29 (104+i) := by decide +kernel

theorem phase_29_108 : ∀ i ∈ List.range 4, PhaseAt 29 (108+i) := by decide +kernel

theorem phase_29_112 : ∀ i ∈ List.range 4, PhaseAt 29 (112+i) := by decide +kernel

theorem phase_29_116 : ∀ i ∈ List.range 4, PhaseAt 29 (116+i) := by decide +kernel

theorem phase_29_120 : ∀ i ∈ List.range 4, PhaseAt 29 (120+i) := by decide +kernel

theorem phase_29_124 : ∀ i ∈ List.range 4, PhaseAt 29 (124+i) := by decide +kernel

theorem phase_29 (v : ℕ) (hv : v ∈ List.range 128) : PhaseAt 29 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 29 v)
  have h := (join 0 64 64 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_29_0 phase_29_4) (join 8 4 4 phase_29_8 phase_29_12)) (join 16 8 8 (join 16 4 4 phase_29_16 phase_29_20) (join 24 4 4 phase_29_24 phase_29_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_29_32 phase_29_36) (join 40 4 4 phase_29_40 phase_29_44)) (join 48 8 8 (join 48 4 4 phase_29_48 phase_29_52) (join 56 4 4 phase_29_56 phase_29_60)))) (join 64 32 32 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_29_64 phase_29_68) (join 72 4 4 phase_29_72 phase_29_76)) (join 80 8 8 (join 80 4 4 phase_29_80 phase_29_84) (join 88 4 4 phase_29_88 phase_29_92))) (join 96 16 16 (join 96 8 8 (join 96 4 4 phase_29_96 phase_29_100) (join 104 4 4 phase_29_104 phase_29_108)) (join 112 8 8 (join 112 4 4 phase_29_112 phase_29_116) (join 120 4 4 phase_29_120 phase_29_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_29_0 : ∀ i ∈ List.range 1, ThresholdAt 29 (0+i) := by decide +kernel

theorem threshold_29_1 : ∀ i ∈ List.range 1, ThresholdAt 29 (1+i) := by decide +kernel

theorem threshold_29_2 : ∀ i ∈ List.range 1, ThresholdAt 29 (2+i) := by decide +kernel

theorem threshold_29_3 : ∀ i ∈ List.range 1, ThresholdAt 29 (3+i) := by decide +kernel

theorem threshold_29_4 : ∀ i ∈ List.range 1, ThresholdAt 29 (4+i) := by decide +kernel

theorem threshold_29_5 : ∀ i ∈ List.range 1, ThresholdAt 29 (5+i) := by decide +kernel

theorem threshold_29_6 : ∀ i ∈ List.range 1, ThresholdAt 29 (6+i) := by decide +kernel

theorem threshold_29_7 : ∀ i ∈ List.range 1, ThresholdAt 29 (7+i) := by decide +kernel

theorem threshold_29_8 : ∀ i ∈ List.range 1, ThresholdAt 29 (8+i) := by decide +kernel

theorem threshold_29_9 : ∀ i ∈ List.range 1, ThresholdAt 29 (9+i) := by decide +kernel

theorem threshold_29_10 : ∀ i ∈ List.range 1, ThresholdAt 29 (10+i) := by decide +kernel

theorem threshold_29_11 : ∀ i ∈ List.range 1, ThresholdAt 29 (11+i) := by decide +kernel

theorem threshold_29_12 : ∀ i ∈ List.range 1, ThresholdAt 29 (12+i) := by decide +kernel

theorem threshold_29_13 : ∀ i ∈ List.range 1, ThresholdAt 29 (13+i) := by decide +kernel

theorem threshold_29_14 : ∀ i ∈ List.range 1, ThresholdAt 29 (14+i) := by decide +kernel

theorem threshold_29_15 : ∀ i ∈ List.range 1, ThresholdAt 29 (15+i) := by decide +kernel

theorem threshold_29_16 : ∀ i ∈ List.range 1, ThresholdAt 29 (16+i) := by decide +kernel

theorem threshold_29_17 : ∀ i ∈ List.range 1, ThresholdAt 29 (17+i) := by decide +kernel

theorem threshold_29_18 : ∀ i ∈ List.range 1, ThresholdAt 29 (18+i) := by decide +kernel

theorem threshold_29_19 : ∀ i ∈ List.range 1, ThresholdAt 29 (19+i) := by decide +kernel

theorem threshold_29_20 : ∀ i ∈ List.range 1, ThresholdAt 29 (20+i) := by decide +kernel

theorem threshold_29_21 : ∀ i ∈ List.range 1, ThresholdAt 29 (21+i) := by decide +kernel

theorem threshold_29_22 : ∀ i ∈ List.range 1, ThresholdAt 29 (22+i) := by decide +kernel

theorem threshold_29_23 : ∀ i ∈ List.range 1, ThresholdAt 29 (23+i) := by decide +kernel

theorem threshold_29_24 : ∀ i ∈ List.range 1, ThresholdAt 29 (24+i) := by decide +kernel

theorem threshold_29_25 : ∀ i ∈ List.range 1, ThresholdAt 29 (25+i) := by decide +kernel

theorem threshold_29_26 : ∀ i ∈ List.range 1, ThresholdAt 29 (26+i) := by decide +kernel

theorem threshold_29_27 : ∀ i ∈ List.range 1, ThresholdAt 29 (27+i) := by decide +kernel

theorem threshold_29_28 : ∀ i ∈ List.range 1, ThresholdAt 29 (28+i) := by decide +kernel

theorem threshold_29_29 : ∀ i ∈ List.range 1, ThresholdAt 29 (29+i) := by decide +kernel

theorem threshold_29_30 : ∀ i ∈ List.range 1, ThresholdAt 29 (30+i) := by decide +kernel

theorem threshold_29_31 : ∀ i ∈ List.range 1, ThresholdAt 29 (31+i) := by decide +kernel

theorem threshold_29_32 : ∀ i ∈ List.range 1, ThresholdAt 29 (32+i) := by decide +kernel

theorem threshold_29_33 : ∀ i ∈ List.range 1, ThresholdAt 29 (33+i) := by decide +kernel

theorem threshold_29_34 : ∀ i ∈ List.range 1, ThresholdAt 29 (34+i) := by decide +kernel

theorem threshold_29_35 : ∀ i ∈ List.range 1, ThresholdAt 29 (35+i) := by decide +kernel

theorem threshold_29_36 : ∀ i ∈ List.range 1, ThresholdAt 29 (36+i) := by decide +kernel

theorem threshold_29_37 : ∀ i ∈ List.range 1, ThresholdAt 29 (37+i) := by decide +kernel

theorem threshold_29_38 : ∀ i ∈ List.range 1, ThresholdAt 29 (38+i) := by decide +kernel

theorem threshold_29_39 : ∀ i ∈ List.range 1, ThresholdAt 29 (39+i) := by decide +kernel

theorem threshold_29_40 : ∀ i ∈ List.range 1, ThresholdAt 29 (40+i) := by decide +kernel

theorem threshold_29_41 : ∀ i ∈ List.range 1, ThresholdAt 29 (41+i) := by decide +kernel

theorem threshold_29_42 : ∀ i ∈ List.range 1, ThresholdAt 29 (42+i) := by decide +kernel

theorem threshold_29_43 : ∀ i ∈ List.range 1, ThresholdAt 29 (43+i) := by decide +kernel

theorem threshold_29_44 : ∀ i ∈ List.range 1, ThresholdAt 29 (44+i) := by decide +kernel

theorem threshold_29_45 : ∀ i ∈ List.range 1, ThresholdAt 29 (45+i) := by decide +kernel

theorem threshold_29_46 : ∀ i ∈ List.range 1, ThresholdAt 29 (46+i) := by decide +kernel

theorem threshold_29_47 : ∀ i ∈ List.range 1, ThresholdAt 29 (47+i) := by decide +kernel

theorem threshold_29_48 : ∀ i ∈ List.range 1, ThresholdAt 29 (48+i) := by decide +kernel

theorem threshold_29_49 : ∀ i ∈ List.range 1, ThresholdAt 29 (49+i) := by decide +kernel

theorem threshold_29_50 : ∀ i ∈ List.range 1, ThresholdAt 29 (50+i) := by decide +kernel

theorem threshold_29_51 : ∀ i ∈ List.range 1, ThresholdAt 29 (51+i) := by decide +kernel

theorem threshold_29_52 : ∀ i ∈ List.range 1, ThresholdAt 29 (52+i) := by decide +kernel

theorem threshold_29_53 : ∀ i ∈ List.range 1, ThresholdAt 29 (53+i) := by decide +kernel

theorem threshold_29_54 : ∀ i ∈ List.range 1, ThresholdAt 29 (54+i) := by decide +kernel

theorem threshold_29_55 : ∀ i ∈ List.range 1, ThresholdAt 29 (55+i) := by decide +kernel

theorem threshold_29_56 : ∀ i ∈ List.range 1, ThresholdAt 29 (56+i) := by decide +kernel

theorem threshold_29_57 : ∀ i ∈ List.range 1, ThresholdAt 29 (57+i) := by decide +kernel

theorem threshold_29_58 : ∀ i ∈ List.range 1, ThresholdAt 29 (58+i) := by decide +kernel

theorem threshold_29_59 : ∀ i ∈ List.range 1, ThresholdAt 29 (59+i) := by decide +kernel

theorem threshold_29_60 : ∀ i ∈ List.range 1, ThresholdAt 29 (60+i) := by decide +kernel

theorem threshold_29_61 : ∀ i ∈ List.range 1, ThresholdAt 29 (61+i) := by decide +kernel

theorem threshold_29_62 : ∀ i ∈ List.range 1, ThresholdAt 29 (62+i) := by decide +kernel

theorem threshold_29_63 : ∀ i ∈ List.range 1, ThresholdAt 29 (63+i) := by decide +kernel

theorem threshold_29_64 : ∀ i ∈ List.range 1, ThresholdAt 29 (64+i) := by decide +kernel

theorem threshold_29_65 : ∀ i ∈ List.range 1, ThresholdAt 29 (65+i) := by decide +kernel

theorem threshold_29_66 : ∀ i ∈ List.range 1, ThresholdAt 29 (66+i) := by decide +kernel

theorem threshold_29_67 : ∀ i ∈ List.range 1, ThresholdAt 29 (67+i) := by decide +kernel

theorem threshold_29_68 : ∀ i ∈ List.range 1, ThresholdAt 29 (68+i) := by decide +kernel

theorem threshold_29_69 : ∀ i ∈ List.range 1, ThresholdAt 29 (69+i) := by decide +kernel

theorem threshold_29_70 : ∀ i ∈ List.range 1, ThresholdAt 29 (70+i) := by decide +kernel

theorem threshold_29_71 : ∀ i ∈ List.range 1, ThresholdAt 29 (71+i) := by decide +kernel

theorem threshold_29_72 : ∀ i ∈ List.range 1, ThresholdAt 29 (72+i) := by decide +kernel

theorem threshold_29_73 : ∀ i ∈ List.range 1, ThresholdAt 29 (73+i) := by decide +kernel

theorem threshold_29_74 : ∀ i ∈ List.range 1, ThresholdAt 29 (74+i) := by decide +kernel

theorem threshold_29_75 : ∀ i ∈ List.range 1, ThresholdAt 29 (75+i) := by decide +kernel

theorem threshold_29_76 : ∀ i ∈ List.range 1, ThresholdAt 29 (76+i) := by decide +kernel

theorem threshold_29_77 : ∀ i ∈ List.range 1, ThresholdAt 29 (77+i) := by decide +kernel

theorem threshold_29_78 : ∀ i ∈ List.range 1, ThresholdAt 29 (78+i) := by decide +kernel

theorem threshold_29_79 : ∀ i ∈ List.range 1, ThresholdAt 29 (79+i) := by decide +kernel

theorem threshold_29_80 : ∀ i ∈ List.range 1, ThresholdAt 29 (80+i) := by decide +kernel

theorem threshold_29_81 : ∀ i ∈ List.range 1, ThresholdAt 29 (81+i) := by decide +kernel

theorem threshold_29_82 : ∀ i ∈ List.range 1, ThresholdAt 29 (82+i) := by decide +kernel

theorem threshold_29_83 : ∀ i ∈ List.range 1, ThresholdAt 29 (83+i) := by decide +kernel

theorem threshold_29_84 : ∀ i ∈ List.range 1, ThresholdAt 29 (84+i) := by decide +kernel

theorem threshold_29_85 : ∀ i ∈ List.range 1, ThresholdAt 29 (85+i) := by decide +kernel

theorem threshold_29_86 : ∀ i ∈ List.range 1, ThresholdAt 29 (86+i) := by decide +kernel

theorem threshold_29_87 : ∀ i ∈ List.range 1, ThresholdAt 29 (87+i) := by decide +kernel

theorem threshold_29_88 : ∀ i ∈ List.range 1, ThresholdAt 29 (88+i) := by decide +kernel

theorem threshold_29_89 : ∀ i ∈ List.range 1, ThresholdAt 29 (89+i) := by decide +kernel

theorem threshold_29_90 : ∀ i ∈ List.range 1, ThresholdAt 29 (90+i) := by decide +kernel

theorem threshold_29_91 : ∀ i ∈ List.range 1, ThresholdAt 29 (91+i) := by decide +kernel

theorem threshold_29_92 : ∀ i ∈ List.range 1, ThresholdAt 29 (92+i) := by decide +kernel

theorem threshold_29_93 : ∀ i ∈ List.range 1, ThresholdAt 29 (93+i) := by decide +kernel

theorem threshold_29_94 : ∀ i ∈ List.range 1, ThresholdAt 29 (94+i) := by decide +kernel

theorem threshold_29_95 : ∀ i ∈ List.range 1, ThresholdAt 29 (95+i) := by decide +kernel

theorem threshold_29_96 : ∀ i ∈ List.range 1, ThresholdAt 29 (96+i) := by decide +kernel

theorem threshold_29_97 : ∀ i ∈ List.range 1, ThresholdAt 29 (97+i) := by decide +kernel

theorem threshold_29_98 : ∀ i ∈ List.range 1, ThresholdAt 29 (98+i) := by decide +kernel

theorem threshold_29_99 : ∀ i ∈ List.range 1, ThresholdAt 29 (99+i) := by decide +kernel

theorem threshold_29_100 : ∀ i ∈ List.range 1, ThresholdAt 29 (100+i) := by decide +kernel

theorem threshold_29_101 : ∀ i ∈ List.range 1, ThresholdAt 29 (101+i) := by decide +kernel

theorem threshold_29_102 : ∀ i ∈ List.range 1, ThresholdAt 29 (102+i) := by decide +kernel

theorem threshold_29_103 : ∀ i ∈ List.range 1, ThresholdAt 29 (103+i) := by decide +kernel

theorem threshold_29_104 : ∀ i ∈ List.range 1, ThresholdAt 29 (104+i) := by decide +kernel

theorem threshold_29_105 : ∀ i ∈ List.range 1, ThresholdAt 29 (105+i) := by decide +kernel

theorem threshold_29_106 : ∀ i ∈ List.range 1, ThresholdAt 29 (106+i) := by decide +kernel

theorem threshold_29_107 : ∀ i ∈ List.range 1, ThresholdAt 29 (107+i) := by decide +kernel

theorem threshold_29_108 : ∀ i ∈ List.range 1, ThresholdAt 29 (108+i) := by decide +kernel

theorem threshold_29_109 : ∀ i ∈ List.range 1, ThresholdAt 29 (109+i) := by decide +kernel

theorem threshold_29_110 : ∀ i ∈ List.range 1, ThresholdAt 29 (110+i) := by decide +kernel

theorem threshold_29_111 : ∀ i ∈ List.range 1, ThresholdAt 29 (111+i) := by decide +kernel

theorem threshold_29_112 : ∀ i ∈ List.range 1, ThresholdAt 29 (112+i) := by decide +kernel

theorem threshold_29_113 : ∀ i ∈ List.range 1, ThresholdAt 29 (113+i) := by decide +kernel

theorem threshold_29_114 : ∀ i ∈ List.range 1, ThresholdAt 29 (114+i) := by decide +kernel

theorem threshold_29_115 : ∀ i ∈ List.range 1, ThresholdAt 29 (115+i) := by decide +kernel

theorem threshold_29_116 : ∀ i ∈ List.range 1, ThresholdAt 29 (116+i) := by decide +kernel

theorem threshold_29_117 : ∀ i ∈ List.range 1, ThresholdAt 29 (117+i) := by decide +kernel

theorem threshold_29_118 : ∀ i ∈ List.range 1, ThresholdAt 29 (118+i) := by decide +kernel

theorem threshold_29_119 : ∀ i ∈ List.range 1, ThresholdAt 29 (119+i) := by decide +kernel

theorem threshold_29_120 : ∀ i ∈ List.range 1, ThresholdAt 29 (120+i) := by decide +kernel

theorem threshold_29_121 : ∀ i ∈ List.range 1, ThresholdAt 29 (121+i) := by decide +kernel

theorem threshold_29_122 : ∀ i ∈ List.range 1, ThresholdAt 29 (122+i) := by decide +kernel

theorem threshold_29_123 : ∀ i ∈ List.range 1, ThresholdAt 29 (123+i) := by decide +kernel

theorem threshold_29_124 : ∀ i ∈ List.range 1, ThresholdAt 29 (124+i) := by decide +kernel

theorem threshold_29_125 : ∀ i ∈ List.range 1, ThresholdAt 29 (125+i) := by decide +kernel

theorem threshold_29_126 : ∀ i ∈ List.range 1, ThresholdAt 29 (126+i) := by decide +kernel

theorem threshold_29_127 : ∀ i ∈ List.range 1, ThresholdAt 29 (127+i) := by decide +kernel

theorem threshold_29 (v : ℕ) (hv : v ∈ List.range 128) : ThresholdAt 29 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 29 v)
  have h := (join 0 64 64 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_29_0 threshold_29_1) (join 2 1 1 threshold_29_2 threshold_29_3)) (join 4 2 2 (join 4 1 1 threshold_29_4 threshold_29_5) (join 6 1 1 threshold_29_6 threshold_29_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_29_8 threshold_29_9) (join 10 1 1 threshold_29_10 threshold_29_11)) (join 12 2 2 (join 12 1 1 threshold_29_12 threshold_29_13) (join 14 1 1 threshold_29_14 threshold_29_15)))) (join 16 8 8 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_29_16 threshold_29_17) (join 18 1 1 threshold_29_18 threshold_29_19)) (join 20 2 2 (join 20 1 1 threshold_29_20 threshold_29_21) (join 22 1 1 threshold_29_22 threshold_29_23))) (join 24 4 4 (join 24 2 2 (join 24 1 1 threshold_29_24 threshold_29_25) (join 26 1 1 threshold_29_26 threshold_29_27)) (join 28 2 2 (join 28 1 1 threshold_29_28 threshold_29_29) (join 30 1 1 threshold_29_30 threshold_29_31))))) (join 32 16 16 (join 32 8 8 (join 32 4 4 (join 32 2 2 (join 32 1 1 threshold_29_32 threshold_29_33) (join 34 1 1 threshold_29_34 threshold_29_35)) (join 36 2 2 (join 36 1 1 threshold_29_36 threshold_29_37) (join 38 1 1 threshold_29_38 threshold_29_39))) (join 40 4 4 (join 40 2 2 (join 40 1 1 threshold_29_40 threshold_29_41) (join 42 1 1 threshold_29_42 threshold_29_43)) (join 44 2 2 (join 44 1 1 threshold_29_44 threshold_29_45) (join 46 1 1 threshold_29_46 threshold_29_47)))) (join 48 8 8 (join 48 4 4 (join 48 2 2 (join 48 1 1 threshold_29_48 threshold_29_49) (join 50 1 1 threshold_29_50 threshold_29_51)) (join 52 2 2 (join 52 1 1 threshold_29_52 threshold_29_53) (join 54 1 1 threshold_29_54 threshold_29_55))) (join 56 4 4 (join 56 2 2 (join 56 1 1 threshold_29_56 threshold_29_57) (join 58 1 1 threshold_29_58 threshold_29_59)) (join 60 2 2 (join 60 1 1 threshold_29_60 threshold_29_61) (join 62 1 1 threshold_29_62 threshold_29_63)))))) (join 64 32 32 (join 64 16 16 (join 64 8 8 (join 64 4 4 (join 64 2 2 (join 64 1 1 threshold_29_64 threshold_29_65) (join 66 1 1 threshold_29_66 threshold_29_67)) (join 68 2 2 (join 68 1 1 threshold_29_68 threshold_29_69) (join 70 1 1 threshold_29_70 threshold_29_71))) (join 72 4 4 (join 72 2 2 (join 72 1 1 threshold_29_72 threshold_29_73) (join 74 1 1 threshold_29_74 threshold_29_75)) (join 76 2 2 (join 76 1 1 threshold_29_76 threshold_29_77) (join 78 1 1 threshold_29_78 threshold_29_79)))) (join 80 8 8 (join 80 4 4 (join 80 2 2 (join 80 1 1 threshold_29_80 threshold_29_81) (join 82 1 1 threshold_29_82 threshold_29_83)) (join 84 2 2 (join 84 1 1 threshold_29_84 threshold_29_85) (join 86 1 1 threshold_29_86 threshold_29_87))) (join 88 4 4 (join 88 2 2 (join 88 1 1 threshold_29_88 threshold_29_89) (join 90 1 1 threshold_29_90 threshold_29_91)) (join 92 2 2 (join 92 1 1 threshold_29_92 threshold_29_93) (join 94 1 1 threshold_29_94 threshold_29_95))))) (join 96 16 16 (join 96 8 8 (join 96 4 4 (join 96 2 2 (join 96 1 1 threshold_29_96 threshold_29_97) (join 98 1 1 threshold_29_98 threshold_29_99)) (join 100 2 2 (join 100 1 1 threshold_29_100 threshold_29_101) (join 102 1 1 threshold_29_102 threshold_29_103))) (join 104 4 4 (join 104 2 2 (join 104 1 1 threshold_29_104 threshold_29_105) (join 106 1 1 threshold_29_106 threshold_29_107)) (join 108 2 2 (join 108 1 1 threshold_29_108 threshold_29_109) (join 110 1 1 threshold_29_110 threshold_29_111)))) (join 112 8 8 (join 112 4 4 (join 112 2 2 (join 112 1 1 threshold_29_112 threshold_29_113) (join 114 1 1 threshold_29_114 threshold_29_115)) (join 116 2 2 (join 116 1 1 threshold_29_116 threshold_29_117) (join 118 1 1 threshold_29_118 threshold_29_119))) (join 120 4 4 (join 120 2 2 (join 120 1 1 threshold_29_120 threshold_29_121) (join 122 1 1 threshold_29_122 threshold_29_123)) (join 124 2 2 (join 124 1 1 threshold_29_124 threshold_29_125) (join 126 1 1 threshold_29_126 threshold_29_127)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_29_0 : ∀ i ∈ List.range 4, LedgerAt 29 (0+i) := by decide +kernel

theorem ledger_29_4 : ∀ i ∈ List.range 4, LedgerAt 29 (4+i) := by decide +kernel

theorem ledger_29_8 : ∀ i ∈ List.range 4, LedgerAt 29 (8+i) := by decide +kernel

theorem ledger_29_12 : ∀ i ∈ List.range 4, LedgerAt 29 (12+i) := by decide +kernel

theorem ledger_29_16 : ∀ i ∈ List.range 4, LedgerAt 29 (16+i) := by decide +kernel

theorem ledger_29_20 : ∀ i ∈ List.range 4, LedgerAt 29 (20+i) := by decide +kernel

theorem ledger_29_24 : ∀ i ∈ List.range 4, LedgerAt 29 (24+i) := by decide +kernel

theorem ledger_29_28 : ∀ i ∈ List.range 4, LedgerAt 29 (28+i) := by decide +kernel

theorem ledger_29_32 : ∀ i ∈ List.range 4, LedgerAt 29 (32+i) := by decide +kernel

theorem ledger_29_36 : ∀ i ∈ List.range 4, LedgerAt 29 (36+i) := by decide +kernel

theorem ledger_29_40 : ∀ i ∈ List.range 4, LedgerAt 29 (40+i) := by decide +kernel

theorem ledger_29_44 : ∀ i ∈ List.range 4, LedgerAt 29 (44+i) := by decide +kernel

theorem ledger_29_48 : ∀ i ∈ List.range 4, LedgerAt 29 (48+i) := by decide +kernel

theorem ledger_29_52 : ∀ i ∈ List.range 4, LedgerAt 29 (52+i) := by decide +kernel

theorem ledger_29_56 : ∀ i ∈ List.range 4, LedgerAt 29 (56+i) := by decide +kernel

theorem ledger_29_60 : ∀ i ∈ List.range 4, LedgerAt 29 (60+i) := by decide +kernel

theorem ledger_29_64 : ∀ i ∈ List.range 4, LedgerAt 29 (64+i) := by decide +kernel

theorem ledger_29_68 : ∀ i ∈ List.range 4, LedgerAt 29 (68+i) := by decide +kernel

theorem ledger_29_72 : ∀ i ∈ List.range 4, LedgerAt 29 (72+i) := by decide +kernel

theorem ledger_29_76 : ∀ i ∈ List.range 4, LedgerAt 29 (76+i) := by decide +kernel

theorem ledger_29_80 : ∀ i ∈ List.range 4, LedgerAt 29 (80+i) := by decide +kernel

theorem ledger_29_84 : ∀ i ∈ List.range 4, LedgerAt 29 (84+i) := by decide +kernel

theorem ledger_29_88 : ∀ i ∈ List.range 4, LedgerAt 29 (88+i) := by decide +kernel

theorem ledger_29_92 : ∀ i ∈ List.range 4, LedgerAt 29 (92+i) := by decide +kernel

theorem ledger_29_96 : ∀ i ∈ List.range 4, LedgerAt 29 (96+i) := by decide +kernel

theorem ledger_29_100 : ∀ i ∈ List.range 4, LedgerAt 29 (100+i) := by decide +kernel

theorem ledger_29_104 : ∀ i ∈ List.range 4, LedgerAt 29 (104+i) := by decide +kernel

theorem ledger_29_108 : ∀ i ∈ List.range 4, LedgerAt 29 (108+i) := by decide +kernel

theorem ledger_29_112 : ∀ i ∈ List.range 4, LedgerAt 29 (112+i) := by decide +kernel

theorem ledger_29_116 : ∀ i ∈ List.range 4, LedgerAt 29 (116+i) := by decide +kernel

theorem ledger_29_120 : ∀ i ∈ List.range 4, LedgerAt 29 (120+i) := by decide +kernel

theorem ledger_29_124 : ∀ i ∈ List.range 4, LedgerAt 29 (124+i) := by decide +kernel

theorem ledger_29 (v : ℕ) (hv : v ∈ List.range 128) : LedgerAt 29 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 29 v)
  have h := (join 0 64 64 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_29_0 ledger_29_4) (join 8 4 4 ledger_29_8 ledger_29_12)) (join 16 8 8 (join 16 4 4 ledger_29_16 ledger_29_20) (join 24 4 4 ledger_29_24 ledger_29_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_29_32 ledger_29_36) (join 40 4 4 ledger_29_40 ledger_29_44)) (join 48 8 8 (join 48 4 4 ledger_29_48 ledger_29_52) (join 56 4 4 ledger_29_56 ledger_29_60)))) (join 64 32 32 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_29_64 ledger_29_68) (join 72 4 4 ledger_29_72 ledger_29_76)) (join 80 8 8 (join 80 4 4 ledger_29_80 ledger_29_84) (join 88 4 4 ledger_29_88 ledger_29_92))) (join 96 16 16 (join 96 8 8 (join 96 4 4 ledger_29_96 ledger_29_100) (join 104 4 4 ledger_29_104 ledger_29_108)) (join 112 8 8 (join 112 4 4 ledger_29_112 ledger_29_116) (join 120 4 4 ledger_29_120 ledger_29_124)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
