import ProximityPrize.SubmissionLower.AffineCheckedR246808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_25_0 : ∀ i ∈ List.range 4, SingleAt 25 (0+i) := by decide +kernel

theorem single_25_4 : ∀ i ∈ List.range 4, SingleAt 25 (4+i) := by decide +kernel

theorem single_25_8 : ∀ i ∈ List.range 4, SingleAt 25 (8+i) := by decide +kernel

theorem single_25_12 : ∀ i ∈ List.range 4, SingleAt 25 (12+i) := by decide +kernel

theorem single_25_16 : ∀ i ∈ List.range 4, SingleAt 25 (16+i) := by decide +kernel

theorem single_25_20 : ∀ i ∈ List.range 4, SingleAt 25 (20+i) := by decide +kernel

theorem single_25_24 : ∀ i ∈ List.range 4, SingleAt 25 (24+i) := by decide +kernel

theorem single_25_28 : ∀ i ∈ List.range 4, SingleAt 25 (28+i) := by decide +kernel

theorem single_25_32 : ∀ i ∈ List.range 4, SingleAt 25 (32+i) := by decide +kernel

theorem single_25_36 : ∀ i ∈ List.range 4, SingleAt 25 (36+i) := by decide +kernel

theorem single_25_40 : ∀ i ∈ List.range 4, SingleAt 25 (40+i) := by decide +kernel

theorem single_25_44 : ∀ i ∈ List.range 4, SingleAt 25 (44+i) := by decide +kernel

theorem single_25_48 : ∀ i ∈ List.range 4, SingleAt 25 (48+i) := by decide +kernel

theorem single_25_52 : ∀ i ∈ List.range 4, SingleAt 25 (52+i) := by decide +kernel

theorem single_25_56 : ∀ i ∈ List.range 4, SingleAt 25 (56+i) := by decide +kernel

theorem single_25_60 : ∀ i ∈ List.range 4, SingleAt 25 (60+i) := by decide +kernel

theorem single_25_64 : ∀ i ∈ List.range 4, SingleAt 25 (64+i) := by decide +kernel

theorem single_25_68 : ∀ i ∈ List.range 4, SingleAt 25 (68+i) := by decide +kernel

theorem single_25_72 : ∀ i ∈ List.range 4, SingleAt 25 (72+i) := by decide +kernel

theorem single_25_76 : ∀ i ∈ List.range 4, SingleAt 25 (76+i) := by decide +kernel

theorem single_25_80 : ∀ i ∈ List.range 4, SingleAt 25 (80+i) := by decide +kernel

theorem single_25_84 : ∀ i ∈ List.range 4, SingleAt 25 (84+i) := by decide +kernel

theorem single_25_88 : ∀ i ∈ List.range 4, SingleAt 25 (88+i) := by decide +kernel

theorem single_25_92 : ∀ i ∈ List.range 4, SingleAt 25 (92+i) := by decide +kernel

theorem single_25_96 : ∀ i ∈ List.range 4, SingleAt 25 (96+i) := by decide +kernel

theorem single_25_100 : ∀ i ∈ List.range 4, SingleAt 25 (100+i) := by decide +kernel

theorem single_25_104 : ∀ i ∈ List.range 4, SingleAt 25 (104+i) := by decide +kernel

theorem single_25_108 : ∀ i ∈ List.range 4, SingleAt 25 (108+i) := by decide +kernel

theorem single_25_112 : ∀ i ∈ List.range 4, SingleAt 25 (112+i) := by decide +kernel

theorem single_25_116 : ∀ i ∈ List.range 4, SingleAt 25 (116+i) := by decide +kernel

theorem single_25_120 : ∀ i ∈ List.range 4, SingleAt 25 (120+i) := by decide +kernel

theorem single_25_124 : ∀ i ∈ List.range 1, SingleAt 25 (124+i) := by decide +kernel

theorem single_25 (v : ℕ) (hv : v ∈ List.range 125) : SingleAt 25 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 25 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_25_0 single_25_4) (join 8 4 4 single_25_8 single_25_12)) (join 16 8 8 (join 16 4 4 single_25_16 single_25_20) (join 24 4 4 single_25_24 single_25_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_25_32 single_25_36) (join 40 4 4 single_25_40 single_25_44)) (join 48 8 8 (join 48 4 4 single_25_48 single_25_52) (join 56 4 4 single_25_56 single_25_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_25_64 single_25_68) (join 72 4 4 single_25_72 single_25_76)) (join 80 8 8 (join 80 4 4 single_25_80 single_25_84) (join 88 4 4 single_25_88 single_25_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 single_25_96 single_25_100) (join 104 4 4 single_25_104 single_25_108)) (join 112 8 5 (join 112 4 4 single_25_112 single_25_116) (join 120 4 1 single_25_120 single_25_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_25_0 : ∀ i ∈ List.range 4, PhaseAt 25 (0+i) := by decide +kernel

theorem phase_25_4 : ∀ i ∈ List.range 4, PhaseAt 25 (4+i) := by decide +kernel

theorem phase_25_8 : ∀ i ∈ List.range 4, PhaseAt 25 (8+i) := by decide +kernel

theorem phase_25_12 : ∀ i ∈ List.range 4, PhaseAt 25 (12+i) := by decide +kernel

theorem phase_25_16 : ∀ i ∈ List.range 4, PhaseAt 25 (16+i) := by decide +kernel

theorem phase_25_20 : ∀ i ∈ List.range 4, PhaseAt 25 (20+i) := by decide +kernel

theorem phase_25_24 : ∀ i ∈ List.range 4, PhaseAt 25 (24+i) := by decide +kernel

theorem phase_25_28 : ∀ i ∈ List.range 4, PhaseAt 25 (28+i) := by decide +kernel

theorem phase_25_32 : ∀ i ∈ List.range 4, PhaseAt 25 (32+i) := by decide +kernel

theorem phase_25_36 : ∀ i ∈ List.range 4, PhaseAt 25 (36+i) := by decide +kernel

theorem phase_25_40 : ∀ i ∈ List.range 4, PhaseAt 25 (40+i) := by decide +kernel

theorem phase_25_44 : ∀ i ∈ List.range 4, PhaseAt 25 (44+i) := by decide +kernel

theorem phase_25_48 : ∀ i ∈ List.range 4, PhaseAt 25 (48+i) := by decide +kernel

theorem phase_25_52 : ∀ i ∈ List.range 4, PhaseAt 25 (52+i) := by decide +kernel

theorem phase_25_56 : ∀ i ∈ List.range 4, PhaseAt 25 (56+i) := by decide +kernel

theorem phase_25_60 : ∀ i ∈ List.range 4, PhaseAt 25 (60+i) := by decide +kernel

theorem phase_25_64 : ∀ i ∈ List.range 4, PhaseAt 25 (64+i) := by decide +kernel

theorem phase_25_68 : ∀ i ∈ List.range 4, PhaseAt 25 (68+i) := by decide +kernel

theorem phase_25_72 : ∀ i ∈ List.range 4, PhaseAt 25 (72+i) := by decide +kernel

theorem phase_25_76 : ∀ i ∈ List.range 4, PhaseAt 25 (76+i) := by decide +kernel

theorem phase_25_80 : ∀ i ∈ List.range 4, PhaseAt 25 (80+i) := by decide +kernel

theorem phase_25_84 : ∀ i ∈ List.range 4, PhaseAt 25 (84+i) := by decide +kernel

theorem phase_25_88 : ∀ i ∈ List.range 4, PhaseAt 25 (88+i) := by decide +kernel

theorem phase_25_92 : ∀ i ∈ List.range 4, PhaseAt 25 (92+i) := by decide +kernel

theorem phase_25_96 : ∀ i ∈ List.range 4, PhaseAt 25 (96+i) := by decide +kernel

theorem phase_25_100 : ∀ i ∈ List.range 4, PhaseAt 25 (100+i) := by decide +kernel

theorem phase_25_104 : ∀ i ∈ List.range 4, PhaseAt 25 (104+i) := by decide +kernel

theorem phase_25_108 : ∀ i ∈ List.range 4, PhaseAt 25 (108+i) := by decide +kernel

theorem phase_25_112 : ∀ i ∈ List.range 4, PhaseAt 25 (112+i) := by decide +kernel

theorem phase_25_116 : ∀ i ∈ List.range 4, PhaseAt 25 (116+i) := by decide +kernel

theorem phase_25_120 : ∀ i ∈ List.range 4, PhaseAt 25 (120+i) := by decide +kernel

theorem phase_25_124 : ∀ i ∈ List.range 1, PhaseAt 25 (124+i) := by decide +kernel

theorem phase_25 (v : ℕ) (hv : v ∈ List.range 125) : PhaseAt 25 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 25 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_25_0 phase_25_4) (join 8 4 4 phase_25_8 phase_25_12)) (join 16 8 8 (join 16 4 4 phase_25_16 phase_25_20) (join 24 4 4 phase_25_24 phase_25_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_25_32 phase_25_36) (join 40 4 4 phase_25_40 phase_25_44)) (join 48 8 8 (join 48 4 4 phase_25_48 phase_25_52) (join 56 4 4 phase_25_56 phase_25_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_25_64 phase_25_68) (join 72 4 4 phase_25_72 phase_25_76)) (join 80 8 8 (join 80 4 4 phase_25_80 phase_25_84) (join 88 4 4 phase_25_88 phase_25_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 phase_25_96 phase_25_100) (join 104 4 4 phase_25_104 phase_25_108)) (join 112 8 5 (join 112 4 4 phase_25_112 phase_25_116) (join 120 4 1 phase_25_120 phase_25_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_25_0 : ∀ i ∈ List.range 1, ThresholdAt 25 (0+i) := by decide +kernel

theorem threshold_25_1 : ∀ i ∈ List.range 1, ThresholdAt 25 (1+i) := by decide +kernel

theorem threshold_25_2 : ∀ i ∈ List.range 1, ThresholdAt 25 (2+i) := by decide +kernel

theorem threshold_25_3 : ∀ i ∈ List.range 1, ThresholdAt 25 (3+i) := by decide +kernel

theorem threshold_25_4 : ∀ i ∈ List.range 1, ThresholdAt 25 (4+i) := by decide +kernel

theorem threshold_25_5 : ∀ i ∈ List.range 1, ThresholdAt 25 (5+i) := by decide +kernel

theorem threshold_25_6 : ∀ i ∈ List.range 1, ThresholdAt 25 (6+i) := by decide +kernel

theorem threshold_25_7 : ∀ i ∈ List.range 1, ThresholdAt 25 (7+i) := by decide +kernel

theorem threshold_25_8 : ∀ i ∈ List.range 1, ThresholdAt 25 (8+i) := by decide +kernel

theorem threshold_25_9 : ∀ i ∈ List.range 1, ThresholdAt 25 (9+i) := by decide +kernel

theorem threshold_25_10 : ∀ i ∈ List.range 1, ThresholdAt 25 (10+i) := by decide +kernel

theorem threshold_25_11 : ∀ i ∈ List.range 1, ThresholdAt 25 (11+i) := by decide +kernel

theorem threshold_25_12 : ∀ i ∈ List.range 1, ThresholdAt 25 (12+i) := by decide +kernel

theorem threshold_25_13 : ∀ i ∈ List.range 1, ThresholdAt 25 (13+i) := by decide +kernel

theorem threshold_25_14 : ∀ i ∈ List.range 1, ThresholdAt 25 (14+i) := by decide +kernel

theorem threshold_25_15 : ∀ i ∈ List.range 1, ThresholdAt 25 (15+i) := by decide +kernel

theorem threshold_25_16 : ∀ i ∈ List.range 1, ThresholdAt 25 (16+i) := by decide +kernel

theorem threshold_25_17 : ∀ i ∈ List.range 1, ThresholdAt 25 (17+i) := by decide +kernel

theorem threshold_25_18 : ∀ i ∈ List.range 1, ThresholdAt 25 (18+i) := by decide +kernel

theorem threshold_25_19 : ∀ i ∈ List.range 1, ThresholdAt 25 (19+i) := by decide +kernel

theorem threshold_25_20 : ∀ i ∈ List.range 1, ThresholdAt 25 (20+i) := by decide +kernel

theorem threshold_25_21 : ∀ i ∈ List.range 1, ThresholdAt 25 (21+i) := by decide +kernel

theorem threshold_25_22 : ∀ i ∈ List.range 1, ThresholdAt 25 (22+i) := by decide +kernel

theorem threshold_25_23 : ∀ i ∈ List.range 1, ThresholdAt 25 (23+i) := by decide +kernel

theorem threshold_25_24 : ∀ i ∈ List.range 1, ThresholdAt 25 (24+i) := by decide +kernel

theorem threshold_25_25 : ∀ i ∈ List.range 1, ThresholdAt 25 (25+i) := by decide +kernel

theorem threshold_25_26 : ∀ i ∈ List.range 1, ThresholdAt 25 (26+i) := by decide +kernel

theorem threshold_25_27 : ∀ i ∈ List.range 1, ThresholdAt 25 (27+i) := by decide +kernel

theorem threshold_25_28 : ∀ i ∈ List.range 1, ThresholdAt 25 (28+i) := by decide +kernel

theorem threshold_25_29 : ∀ i ∈ List.range 1, ThresholdAt 25 (29+i) := by decide +kernel

theorem threshold_25_30 : ∀ i ∈ List.range 1, ThresholdAt 25 (30+i) := by decide +kernel

theorem threshold_25_31 : ∀ i ∈ List.range 1, ThresholdAt 25 (31+i) := by decide +kernel

theorem threshold_25_32 : ∀ i ∈ List.range 1, ThresholdAt 25 (32+i) := by decide +kernel

theorem threshold_25_33 : ∀ i ∈ List.range 1, ThresholdAt 25 (33+i) := by decide +kernel

theorem threshold_25_34 : ∀ i ∈ List.range 1, ThresholdAt 25 (34+i) := by decide +kernel

theorem threshold_25_35 : ∀ i ∈ List.range 1, ThresholdAt 25 (35+i) := by decide +kernel

theorem threshold_25_36 : ∀ i ∈ List.range 1, ThresholdAt 25 (36+i) := by decide +kernel

theorem threshold_25_37 : ∀ i ∈ List.range 1, ThresholdAt 25 (37+i) := by decide +kernel

theorem threshold_25_38 : ∀ i ∈ List.range 1, ThresholdAt 25 (38+i) := by decide +kernel

theorem threshold_25_39 : ∀ i ∈ List.range 1, ThresholdAt 25 (39+i) := by decide +kernel

theorem threshold_25_40 : ∀ i ∈ List.range 1, ThresholdAt 25 (40+i) := by decide +kernel

theorem threshold_25_41 : ∀ i ∈ List.range 1, ThresholdAt 25 (41+i) := by decide +kernel

theorem threshold_25_42 : ∀ i ∈ List.range 1, ThresholdAt 25 (42+i) := by decide +kernel

theorem threshold_25_43 : ∀ i ∈ List.range 1, ThresholdAt 25 (43+i) := by decide +kernel

theorem threshold_25_44 : ∀ i ∈ List.range 1, ThresholdAt 25 (44+i) := by decide +kernel

theorem threshold_25_45 : ∀ i ∈ List.range 1, ThresholdAt 25 (45+i) := by decide +kernel

theorem threshold_25_46 : ∀ i ∈ List.range 1, ThresholdAt 25 (46+i) := by decide +kernel

theorem threshold_25_47 : ∀ i ∈ List.range 1, ThresholdAt 25 (47+i) := by decide +kernel

theorem threshold_25_48 : ∀ i ∈ List.range 1, ThresholdAt 25 (48+i) := by decide +kernel

theorem threshold_25_49 : ∀ i ∈ List.range 1, ThresholdAt 25 (49+i) := by decide +kernel

theorem threshold_25_50 : ∀ i ∈ List.range 1, ThresholdAt 25 (50+i) := by decide +kernel

theorem threshold_25_51 : ∀ i ∈ List.range 1, ThresholdAt 25 (51+i) := by decide +kernel

theorem threshold_25_52 : ∀ i ∈ List.range 1, ThresholdAt 25 (52+i) := by decide +kernel

theorem threshold_25_53 : ∀ i ∈ List.range 1, ThresholdAt 25 (53+i) := by decide +kernel

theorem threshold_25_54 : ∀ i ∈ List.range 1, ThresholdAt 25 (54+i) := by decide +kernel

theorem threshold_25_55 : ∀ i ∈ List.range 1, ThresholdAt 25 (55+i) := by decide +kernel

theorem threshold_25_56 : ∀ i ∈ List.range 1, ThresholdAt 25 (56+i) := by decide +kernel

theorem threshold_25_57 : ∀ i ∈ List.range 1, ThresholdAt 25 (57+i) := by decide +kernel

theorem threshold_25_58 : ∀ i ∈ List.range 1, ThresholdAt 25 (58+i) := by decide +kernel

theorem threshold_25_59 : ∀ i ∈ List.range 1, ThresholdAt 25 (59+i) := by decide +kernel

theorem threshold_25_60 : ∀ i ∈ List.range 1, ThresholdAt 25 (60+i) := by decide +kernel

theorem threshold_25_61 : ∀ i ∈ List.range 1, ThresholdAt 25 (61+i) := by decide +kernel

theorem threshold_25_62 : ∀ i ∈ List.range 1, ThresholdAt 25 (62+i) := by decide +kernel

theorem threshold_25_63 : ∀ i ∈ List.range 1, ThresholdAt 25 (63+i) := by decide +kernel

theorem threshold_25_64 : ∀ i ∈ List.range 1, ThresholdAt 25 (64+i) := by decide +kernel

theorem threshold_25_65 : ∀ i ∈ List.range 1, ThresholdAt 25 (65+i) := by decide +kernel

theorem threshold_25_66 : ∀ i ∈ List.range 1, ThresholdAt 25 (66+i) := by decide +kernel

theorem threshold_25_67 : ∀ i ∈ List.range 1, ThresholdAt 25 (67+i) := by decide +kernel

theorem threshold_25_68 : ∀ i ∈ List.range 1, ThresholdAt 25 (68+i) := by decide +kernel

theorem threshold_25_69 : ∀ i ∈ List.range 1, ThresholdAt 25 (69+i) := by decide +kernel

theorem threshold_25_70 : ∀ i ∈ List.range 1, ThresholdAt 25 (70+i) := by decide +kernel

theorem threshold_25_71 : ∀ i ∈ List.range 1, ThresholdAt 25 (71+i) := by decide +kernel

theorem threshold_25_72 : ∀ i ∈ List.range 1, ThresholdAt 25 (72+i) := by decide +kernel

theorem threshold_25_73 : ∀ i ∈ List.range 1, ThresholdAt 25 (73+i) := by decide +kernel

theorem threshold_25_74 : ∀ i ∈ List.range 1, ThresholdAt 25 (74+i) := by decide +kernel

theorem threshold_25_75 : ∀ i ∈ List.range 1, ThresholdAt 25 (75+i) := by decide +kernel

theorem threshold_25_76 : ∀ i ∈ List.range 1, ThresholdAt 25 (76+i) := by decide +kernel

theorem threshold_25_77 : ∀ i ∈ List.range 1, ThresholdAt 25 (77+i) := by decide +kernel

theorem threshold_25_78 : ∀ i ∈ List.range 1, ThresholdAt 25 (78+i) := by decide +kernel

theorem threshold_25_79 : ∀ i ∈ List.range 1, ThresholdAt 25 (79+i) := by decide +kernel

theorem threshold_25_80 : ∀ i ∈ List.range 1, ThresholdAt 25 (80+i) := by decide +kernel

theorem threshold_25_81 : ∀ i ∈ List.range 1, ThresholdAt 25 (81+i) := by decide +kernel

theorem threshold_25_82 : ∀ i ∈ List.range 1, ThresholdAt 25 (82+i) := by decide +kernel

theorem threshold_25_83 : ∀ i ∈ List.range 1, ThresholdAt 25 (83+i) := by decide +kernel

theorem threshold_25_84 : ∀ i ∈ List.range 1, ThresholdAt 25 (84+i) := by decide +kernel

theorem threshold_25_85 : ∀ i ∈ List.range 1, ThresholdAt 25 (85+i) := by decide +kernel

theorem threshold_25_86 : ∀ i ∈ List.range 1, ThresholdAt 25 (86+i) := by decide +kernel

theorem threshold_25_87 : ∀ i ∈ List.range 1, ThresholdAt 25 (87+i) := by decide +kernel

theorem threshold_25_88 : ∀ i ∈ List.range 1, ThresholdAt 25 (88+i) := by decide +kernel

theorem threshold_25_89 : ∀ i ∈ List.range 1, ThresholdAt 25 (89+i) := by decide +kernel

theorem threshold_25_90 : ∀ i ∈ List.range 1, ThresholdAt 25 (90+i) := by decide +kernel

theorem threshold_25_91 : ∀ i ∈ List.range 1, ThresholdAt 25 (91+i) := by decide +kernel

theorem threshold_25_92 : ∀ i ∈ List.range 1, ThresholdAt 25 (92+i) := by decide +kernel

theorem threshold_25_93 : ∀ i ∈ List.range 1, ThresholdAt 25 (93+i) := by decide +kernel

theorem threshold_25_94 : ∀ i ∈ List.range 1, ThresholdAt 25 (94+i) := by decide +kernel

theorem threshold_25_95 : ∀ i ∈ List.range 1, ThresholdAt 25 (95+i) := by decide +kernel

theorem threshold_25_96 : ∀ i ∈ List.range 1, ThresholdAt 25 (96+i) := by decide +kernel

theorem threshold_25_97 : ∀ i ∈ List.range 1, ThresholdAt 25 (97+i) := by decide +kernel

theorem threshold_25_98 : ∀ i ∈ List.range 1, ThresholdAt 25 (98+i) := by decide +kernel

theorem threshold_25_99 : ∀ i ∈ List.range 1, ThresholdAt 25 (99+i) := by decide +kernel

theorem threshold_25_100 : ∀ i ∈ List.range 1, ThresholdAt 25 (100+i) := by decide +kernel

theorem threshold_25_101 : ∀ i ∈ List.range 1, ThresholdAt 25 (101+i) := by decide +kernel

theorem threshold_25_102 : ∀ i ∈ List.range 1, ThresholdAt 25 (102+i) := by decide +kernel

theorem threshold_25_103 : ∀ i ∈ List.range 1, ThresholdAt 25 (103+i) := by decide +kernel

theorem threshold_25_104 : ∀ i ∈ List.range 1, ThresholdAt 25 (104+i) := by decide +kernel

theorem threshold_25_105 : ∀ i ∈ List.range 1, ThresholdAt 25 (105+i) := by decide +kernel

theorem threshold_25_106 : ∀ i ∈ List.range 1, ThresholdAt 25 (106+i) := by decide +kernel

theorem threshold_25_107 : ∀ i ∈ List.range 1, ThresholdAt 25 (107+i) := by decide +kernel

theorem threshold_25_108 : ∀ i ∈ List.range 1, ThresholdAt 25 (108+i) := by decide +kernel

theorem threshold_25_109 : ∀ i ∈ List.range 1, ThresholdAt 25 (109+i) := by decide +kernel

theorem threshold_25_110 : ∀ i ∈ List.range 1, ThresholdAt 25 (110+i) := by decide +kernel

theorem threshold_25_111 : ∀ i ∈ List.range 1, ThresholdAt 25 (111+i) := by decide +kernel

theorem threshold_25_112 : ∀ i ∈ List.range 1, ThresholdAt 25 (112+i) := by decide +kernel

theorem threshold_25_113 : ∀ i ∈ List.range 1, ThresholdAt 25 (113+i) := by decide +kernel

theorem threshold_25_114 : ∀ i ∈ List.range 1, ThresholdAt 25 (114+i) := by decide +kernel

theorem threshold_25_115 : ∀ i ∈ List.range 1, ThresholdAt 25 (115+i) := by decide +kernel

theorem threshold_25_116 : ∀ i ∈ List.range 1, ThresholdAt 25 (116+i) := by decide +kernel

theorem threshold_25_117 : ∀ i ∈ List.range 1, ThresholdAt 25 (117+i) := by decide +kernel

theorem threshold_25_118 : ∀ i ∈ List.range 1, ThresholdAt 25 (118+i) := by decide +kernel

theorem threshold_25_119 : ∀ i ∈ List.range 1, ThresholdAt 25 (119+i) := by decide +kernel

theorem threshold_25_120 : ∀ i ∈ List.range 1, ThresholdAt 25 (120+i) := by decide +kernel

theorem threshold_25_121 : ∀ i ∈ List.range 1, ThresholdAt 25 (121+i) := by decide +kernel

theorem threshold_25_122 : ∀ i ∈ List.range 1, ThresholdAt 25 (122+i) := by decide +kernel

theorem threshold_25_123 : ∀ i ∈ List.range 1, ThresholdAt 25 (123+i) := by decide +kernel

theorem threshold_25_124 : ∀ i ∈ List.range 1, ThresholdAt 25 (124+i) := by decide +kernel

theorem threshold_25 (v : ℕ) (hv : v ∈ List.range 125) : ThresholdAt 25 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 25 v)
  have h := (join 0 62 63 (join 0 31 31 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_25_0 (join 1 1 1 threshold_25_1 threshold_25_2)) (join 3 2 2 (join 3 1 1 threshold_25_3 threshold_25_4) (join 5 1 1 threshold_25_5 threshold_25_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_25_7 threshold_25_8) (join 9 1 1 threshold_25_9 threshold_25_10)) (join 11 2 2 (join 11 1 1 threshold_25_11 threshold_25_12) (join 13 1 1 threshold_25_13 threshold_25_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_25_15 threshold_25_16) (join 17 1 1 threshold_25_17 threshold_25_18)) (join 19 2 2 (join 19 1 1 threshold_25_19 threshold_25_20) (join 21 1 1 threshold_25_21 threshold_25_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_25_23 threshold_25_24) (join 25 1 1 threshold_25_25 threshold_25_26)) (join 27 2 2 (join 27 1 1 threshold_25_27 threshold_25_28) (join 29 1 1 threshold_25_29 threshold_25_30))))) (join 31 15 16 (join 31 7 8 (join 31 3 4 (join 31 1 2 threshold_25_31 (join 32 1 1 threshold_25_32 threshold_25_33)) (join 34 2 2 (join 34 1 1 threshold_25_34 threshold_25_35) (join 36 1 1 threshold_25_36 threshold_25_37))) (join 38 4 4 (join 38 2 2 (join 38 1 1 threshold_25_38 threshold_25_39) (join 40 1 1 threshold_25_40 threshold_25_41)) (join 42 2 2 (join 42 1 1 threshold_25_42 threshold_25_43) (join 44 1 1 threshold_25_44 threshold_25_45)))) (join 46 8 8 (join 46 4 4 (join 46 2 2 (join 46 1 1 threshold_25_46 threshold_25_47) (join 48 1 1 threshold_25_48 threshold_25_49)) (join 50 2 2 (join 50 1 1 threshold_25_50 threshold_25_51) (join 52 1 1 threshold_25_52 threshold_25_53))) (join 54 4 4 (join 54 2 2 (join 54 1 1 threshold_25_54 threshold_25_55) (join 56 1 1 threshold_25_56 threshold_25_57)) (join 58 2 2 (join 58 1 1 threshold_25_58 threshold_25_59) (join 60 1 1 threshold_25_60 threshold_25_61)))))) (join 62 31 32 (join 62 15 16 (join 62 7 8 (join 62 3 4 (join 62 1 2 threshold_25_62 (join 63 1 1 threshold_25_63 threshold_25_64)) (join 65 2 2 (join 65 1 1 threshold_25_65 threshold_25_66) (join 67 1 1 threshold_25_67 threshold_25_68))) (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_25_69 threshold_25_70) (join 71 1 1 threshold_25_71 threshold_25_72)) (join 73 2 2 (join 73 1 1 threshold_25_73 threshold_25_74) (join 75 1 1 threshold_25_75 threshold_25_76)))) (join 77 8 8 (join 77 4 4 (join 77 2 2 (join 77 1 1 threshold_25_77 threshold_25_78) (join 79 1 1 threshold_25_79 threshold_25_80)) (join 81 2 2 (join 81 1 1 threshold_25_81 threshold_25_82) (join 83 1 1 threshold_25_83 threshold_25_84))) (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_25_85 threshold_25_86) (join 87 1 1 threshold_25_87 threshold_25_88)) (join 89 2 2 (join 89 1 1 threshold_25_89 threshold_25_90) (join 91 1 1 threshold_25_91 threshold_25_92))))) (join 93 16 16 (join 93 8 8 (join 93 4 4 (join 93 2 2 (join 93 1 1 threshold_25_93 threshold_25_94) (join 95 1 1 threshold_25_95 threshold_25_96)) (join 97 2 2 (join 97 1 1 threshold_25_97 threshold_25_98) (join 99 1 1 threshold_25_99 threshold_25_100))) (join 101 4 4 (join 101 2 2 (join 101 1 1 threshold_25_101 threshold_25_102) (join 103 1 1 threshold_25_103 threshold_25_104)) (join 105 2 2 (join 105 1 1 threshold_25_105 threshold_25_106) (join 107 1 1 threshold_25_107 threshold_25_108)))) (join 109 8 8 (join 109 4 4 (join 109 2 2 (join 109 1 1 threshold_25_109 threshold_25_110) (join 111 1 1 threshold_25_111 threshold_25_112)) (join 113 2 2 (join 113 1 1 threshold_25_113 threshold_25_114) (join 115 1 1 threshold_25_115 threshold_25_116))) (join 117 4 4 (join 117 2 2 (join 117 1 1 threshold_25_117 threshold_25_118) (join 119 1 1 threshold_25_119 threshold_25_120)) (join 121 2 2 (join 121 1 1 threshold_25_121 threshold_25_122) (join 123 1 1 threshold_25_123 threshold_25_124)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_25_0 : ∀ i ∈ List.range 4, LedgerAt 25 (0+i) := by decide +kernel

theorem ledger_25_4 : ∀ i ∈ List.range 4, LedgerAt 25 (4+i) := by decide +kernel

theorem ledger_25_8 : ∀ i ∈ List.range 4, LedgerAt 25 (8+i) := by decide +kernel

theorem ledger_25_12 : ∀ i ∈ List.range 4, LedgerAt 25 (12+i) := by decide +kernel

theorem ledger_25_16 : ∀ i ∈ List.range 4, LedgerAt 25 (16+i) := by decide +kernel

theorem ledger_25_20 : ∀ i ∈ List.range 4, LedgerAt 25 (20+i) := by decide +kernel

theorem ledger_25_24 : ∀ i ∈ List.range 4, LedgerAt 25 (24+i) := by decide +kernel

theorem ledger_25_28 : ∀ i ∈ List.range 4, LedgerAt 25 (28+i) := by decide +kernel

theorem ledger_25_32 : ∀ i ∈ List.range 4, LedgerAt 25 (32+i) := by decide +kernel

theorem ledger_25_36 : ∀ i ∈ List.range 4, LedgerAt 25 (36+i) := by decide +kernel

theorem ledger_25_40 : ∀ i ∈ List.range 4, LedgerAt 25 (40+i) := by decide +kernel

theorem ledger_25_44 : ∀ i ∈ List.range 4, LedgerAt 25 (44+i) := by decide +kernel

theorem ledger_25_48 : ∀ i ∈ List.range 4, LedgerAt 25 (48+i) := by decide +kernel

theorem ledger_25_52 : ∀ i ∈ List.range 4, LedgerAt 25 (52+i) := by decide +kernel

theorem ledger_25_56 : ∀ i ∈ List.range 4, LedgerAt 25 (56+i) := by decide +kernel

theorem ledger_25_60 : ∀ i ∈ List.range 4, LedgerAt 25 (60+i) := by decide +kernel

theorem ledger_25_64 : ∀ i ∈ List.range 4, LedgerAt 25 (64+i) := by decide +kernel

theorem ledger_25_68 : ∀ i ∈ List.range 4, LedgerAt 25 (68+i) := by decide +kernel

theorem ledger_25_72 : ∀ i ∈ List.range 4, LedgerAt 25 (72+i) := by decide +kernel

theorem ledger_25_76 : ∀ i ∈ List.range 4, LedgerAt 25 (76+i) := by decide +kernel

theorem ledger_25_80 : ∀ i ∈ List.range 4, LedgerAt 25 (80+i) := by decide +kernel

theorem ledger_25_84 : ∀ i ∈ List.range 4, LedgerAt 25 (84+i) := by decide +kernel

theorem ledger_25_88 : ∀ i ∈ List.range 4, LedgerAt 25 (88+i) := by decide +kernel

theorem ledger_25_92 : ∀ i ∈ List.range 4, LedgerAt 25 (92+i) := by decide +kernel

theorem ledger_25_96 : ∀ i ∈ List.range 4, LedgerAt 25 (96+i) := by decide +kernel

theorem ledger_25_100 : ∀ i ∈ List.range 4, LedgerAt 25 (100+i) := by decide +kernel

theorem ledger_25_104 : ∀ i ∈ List.range 4, LedgerAt 25 (104+i) := by decide +kernel

theorem ledger_25_108 : ∀ i ∈ List.range 4, LedgerAt 25 (108+i) := by decide +kernel

theorem ledger_25_112 : ∀ i ∈ List.range 4, LedgerAt 25 (112+i) := by decide +kernel

theorem ledger_25_116 : ∀ i ∈ List.range 4, LedgerAt 25 (116+i) := by decide +kernel

theorem ledger_25_120 : ∀ i ∈ List.range 4, LedgerAt 25 (120+i) := by decide +kernel

theorem ledger_25_124 : ∀ i ∈ List.range 1, LedgerAt 25 (124+i) := by decide +kernel

theorem ledger_25 (v : ℕ) (hv : v ∈ List.range 125) : LedgerAt 25 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 25 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_25_0 ledger_25_4) (join 8 4 4 ledger_25_8 ledger_25_12)) (join 16 8 8 (join 16 4 4 ledger_25_16 ledger_25_20) (join 24 4 4 ledger_25_24 ledger_25_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_25_32 ledger_25_36) (join 40 4 4 ledger_25_40 ledger_25_44)) (join 48 8 8 (join 48 4 4 ledger_25_48 ledger_25_52) (join 56 4 4 ledger_25_56 ledger_25_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_25_64 ledger_25_68) (join 72 4 4 ledger_25_72 ledger_25_76)) (join 80 8 8 (join 80 4 4 ledger_25_80 ledger_25_84) (join 88 4 4 ledger_25_88 ledger_25_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 ledger_25_96 ledger_25_100) (join 104 4 4 ledger_25_104 ledger_25_108)) (join 112 8 5 (join 112 4 4 ledger_25_112 ledger_25_116) (join 120 4 1 ledger_25_120 ledger_25_124)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
