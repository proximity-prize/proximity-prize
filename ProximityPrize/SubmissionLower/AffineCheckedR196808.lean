import ProximityPrize.SubmissionLower.AffineCheckedR186808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_19_0 : ∀ i ∈ List.range 4, SingleAt 19 (0+i) := by decide +kernel

theorem single_19_4 : ∀ i ∈ List.range 4, SingleAt 19 (4+i) := by decide +kernel

theorem single_19_8 : ∀ i ∈ List.range 4, SingleAt 19 (8+i) := by decide +kernel

theorem single_19_12 : ∀ i ∈ List.range 4, SingleAt 19 (12+i) := by decide +kernel

theorem single_19_16 : ∀ i ∈ List.range 4, SingleAt 19 (16+i) := by decide +kernel

theorem single_19_20 : ∀ i ∈ List.range 4, SingleAt 19 (20+i) := by decide +kernel

theorem single_19_24 : ∀ i ∈ List.range 4, SingleAt 19 (24+i) := by decide +kernel

theorem single_19_28 : ∀ i ∈ List.range 4, SingleAt 19 (28+i) := by decide +kernel

theorem single_19_32 : ∀ i ∈ List.range 4, SingleAt 19 (32+i) := by decide +kernel

theorem single_19_36 : ∀ i ∈ List.range 4, SingleAt 19 (36+i) := by decide +kernel

theorem single_19_40 : ∀ i ∈ List.range 4, SingleAt 19 (40+i) := by decide +kernel

theorem single_19_44 : ∀ i ∈ List.range 4, SingleAt 19 (44+i) := by decide +kernel

theorem single_19_48 : ∀ i ∈ List.range 4, SingleAt 19 (48+i) := by decide +kernel

theorem single_19_52 : ∀ i ∈ List.range 4, SingleAt 19 (52+i) := by decide +kernel

theorem single_19_56 : ∀ i ∈ List.range 4, SingleAt 19 (56+i) := by decide +kernel

theorem single_19_60 : ∀ i ∈ List.range 4, SingleAt 19 (60+i) := by decide +kernel

theorem single_19_64 : ∀ i ∈ List.range 4, SingleAt 19 (64+i) := by decide +kernel

theorem single_19_68 : ∀ i ∈ List.range 4, SingleAt 19 (68+i) := by decide +kernel

theorem single_19_72 : ∀ i ∈ List.range 4, SingleAt 19 (72+i) := by decide +kernel

theorem single_19_76 : ∀ i ∈ List.range 4, SingleAt 19 (76+i) := by decide +kernel

theorem single_19_80 : ∀ i ∈ List.range 4, SingleAt 19 (80+i) := by decide +kernel

theorem single_19_84 : ∀ i ∈ List.range 4, SingleAt 19 (84+i) := by decide +kernel

theorem single_19_88 : ∀ i ∈ List.range 4, SingleAt 19 (88+i) := by decide +kernel

theorem single_19_92 : ∀ i ∈ List.range 4, SingleAt 19 (92+i) := by decide +kernel

theorem single_19_96 : ∀ i ∈ List.range 4, SingleAt 19 (96+i) := by decide +kernel

theorem single_19_100 : ∀ i ∈ List.range 4, SingleAt 19 (100+i) := by decide +kernel

theorem single_19_104 : ∀ i ∈ List.range 4, SingleAt 19 (104+i) := by decide +kernel

theorem single_19_108 : ∀ i ∈ List.range 4, SingleAt 19 (108+i) := by decide +kernel

theorem single_19_112 : ∀ i ∈ List.range 4, SingleAt 19 (112+i) := by decide +kernel

theorem single_19_116 : ∀ i ∈ List.range 4, SingleAt 19 (116+i) := by decide +kernel

theorem single_19_120 : ∀ i ∈ List.range 4, SingleAt 19 (120+i) := by decide +kernel

theorem single_19_124 : ∀ i ∈ List.range 4, SingleAt 19 (124+i) := by decide +kernel

theorem single_19_128 : ∀ i ∈ List.range 3, SingleAt 19 (128+i) := by decide +kernel

theorem single_19 (v : ℕ) (hv : v ∈ List.range 131) : SingleAt 19 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 19 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_19_0 single_19_4) (join 8 4 4 single_19_8 single_19_12)) (join 16 8 8 (join 16 4 4 single_19_16 single_19_20) (join 24 4 4 single_19_24 single_19_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_19_32 single_19_36) (join 40 4 4 single_19_40 single_19_44)) (join 48 8 8 (join 48 4 4 single_19_48 single_19_52) (join 56 4 4 single_19_56 single_19_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_19_64 single_19_68) (join 72 4 4 single_19_72 single_19_76)) (join 80 8 8 (join 80 4 4 single_19_80 single_19_84) (join 88 4 4 single_19_88 single_19_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 single_19_96 single_19_100) (join 104 4 4 single_19_104 single_19_108)) (join 112 8 11 (join 112 4 4 single_19_112 single_19_116) (join 120 4 7 single_19_120 (join 124 4 3 single_19_124 single_19_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_19_0 : ∀ i ∈ List.range 4, PhaseAt 19 (0+i) := by decide +kernel

theorem phase_19_4 : ∀ i ∈ List.range 4, PhaseAt 19 (4+i) := by decide +kernel

theorem phase_19_8 : ∀ i ∈ List.range 4, PhaseAt 19 (8+i) := by decide +kernel

theorem phase_19_12 : ∀ i ∈ List.range 4, PhaseAt 19 (12+i) := by decide +kernel

theorem phase_19_16 : ∀ i ∈ List.range 4, PhaseAt 19 (16+i) := by decide +kernel

theorem phase_19_20 : ∀ i ∈ List.range 4, PhaseAt 19 (20+i) := by decide +kernel

theorem phase_19_24 : ∀ i ∈ List.range 4, PhaseAt 19 (24+i) := by decide +kernel

theorem phase_19_28 : ∀ i ∈ List.range 4, PhaseAt 19 (28+i) := by decide +kernel

theorem phase_19_32 : ∀ i ∈ List.range 4, PhaseAt 19 (32+i) := by decide +kernel

theorem phase_19_36 : ∀ i ∈ List.range 4, PhaseAt 19 (36+i) := by decide +kernel

theorem phase_19_40 : ∀ i ∈ List.range 4, PhaseAt 19 (40+i) := by decide +kernel

theorem phase_19_44 : ∀ i ∈ List.range 4, PhaseAt 19 (44+i) := by decide +kernel

theorem phase_19_48 : ∀ i ∈ List.range 4, PhaseAt 19 (48+i) := by decide +kernel

theorem phase_19_52 : ∀ i ∈ List.range 4, PhaseAt 19 (52+i) := by decide +kernel

theorem phase_19_56 : ∀ i ∈ List.range 4, PhaseAt 19 (56+i) := by decide +kernel

theorem phase_19_60 : ∀ i ∈ List.range 4, PhaseAt 19 (60+i) := by decide +kernel

theorem phase_19_64 : ∀ i ∈ List.range 4, PhaseAt 19 (64+i) := by decide +kernel

theorem phase_19_68 : ∀ i ∈ List.range 4, PhaseAt 19 (68+i) := by decide +kernel

theorem phase_19_72 : ∀ i ∈ List.range 4, PhaseAt 19 (72+i) := by decide +kernel

theorem phase_19_76 : ∀ i ∈ List.range 4, PhaseAt 19 (76+i) := by decide +kernel

theorem phase_19_80 : ∀ i ∈ List.range 4, PhaseAt 19 (80+i) := by decide +kernel

theorem phase_19_84 : ∀ i ∈ List.range 4, PhaseAt 19 (84+i) := by decide +kernel

theorem phase_19_88 : ∀ i ∈ List.range 4, PhaseAt 19 (88+i) := by decide +kernel

theorem phase_19_92 : ∀ i ∈ List.range 4, PhaseAt 19 (92+i) := by decide +kernel

theorem phase_19_96 : ∀ i ∈ List.range 4, PhaseAt 19 (96+i) := by decide +kernel

theorem phase_19_100 : ∀ i ∈ List.range 4, PhaseAt 19 (100+i) := by decide +kernel

theorem phase_19_104 : ∀ i ∈ List.range 4, PhaseAt 19 (104+i) := by decide +kernel

theorem phase_19_108 : ∀ i ∈ List.range 4, PhaseAt 19 (108+i) := by decide +kernel

theorem phase_19_112 : ∀ i ∈ List.range 4, PhaseAt 19 (112+i) := by decide +kernel

theorem phase_19_116 : ∀ i ∈ List.range 4, PhaseAt 19 (116+i) := by decide +kernel

theorem phase_19_120 : ∀ i ∈ List.range 4, PhaseAt 19 (120+i) := by decide +kernel

theorem phase_19_124 : ∀ i ∈ List.range 4, PhaseAt 19 (124+i) := by decide +kernel

theorem phase_19_128 : ∀ i ∈ List.range 3, PhaseAt 19 (128+i) := by decide +kernel

theorem phase_19 (v : ℕ) (hv : v ∈ List.range 131) : PhaseAt 19 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 19 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_19_0 phase_19_4) (join 8 4 4 phase_19_8 phase_19_12)) (join 16 8 8 (join 16 4 4 phase_19_16 phase_19_20) (join 24 4 4 phase_19_24 phase_19_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_19_32 phase_19_36) (join 40 4 4 phase_19_40 phase_19_44)) (join 48 8 8 (join 48 4 4 phase_19_48 phase_19_52) (join 56 4 4 phase_19_56 phase_19_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_19_64 phase_19_68) (join 72 4 4 phase_19_72 phase_19_76)) (join 80 8 8 (join 80 4 4 phase_19_80 phase_19_84) (join 88 4 4 phase_19_88 phase_19_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 phase_19_96 phase_19_100) (join 104 4 4 phase_19_104 phase_19_108)) (join 112 8 11 (join 112 4 4 phase_19_112 phase_19_116) (join 120 4 7 phase_19_120 (join 124 4 3 phase_19_124 phase_19_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_19_0 : ∀ i ∈ List.range 1, ThresholdAt 19 (0+i) := by decide +kernel

theorem threshold_19_1 : ∀ i ∈ List.range 1, ThresholdAt 19 (1+i) := by decide +kernel

theorem threshold_19_2 : ∀ i ∈ List.range 1, ThresholdAt 19 (2+i) := by decide +kernel

theorem threshold_19_3 : ∀ i ∈ List.range 1, ThresholdAt 19 (3+i) := by decide +kernel

theorem threshold_19_4 : ∀ i ∈ List.range 1, ThresholdAt 19 (4+i) := by decide +kernel

theorem threshold_19_5 : ∀ i ∈ List.range 1, ThresholdAt 19 (5+i) := by decide +kernel

theorem threshold_19_6 : ∀ i ∈ List.range 1, ThresholdAt 19 (6+i) := by decide +kernel

theorem threshold_19_7 : ∀ i ∈ List.range 1, ThresholdAt 19 (7+i) := by decide +kernel

theorem threshold_19_8 : ∀ i ∈ List.range 1, ThresholdAt 19 (8+i) := by decide +kernel

theorem threshold_19_9 : ∀ i ∈ List.range 1, ThresholdAt 19 (9+i) := by decide +kernel

theorem threshold_19_10 : ∀ i ∈ List.range 1, ThresholdAt 19 (10+i) := by decide +kernel

theorem threshold_19_11 : ∀ i ∈ List.range 1, ThresholdAt 19 (11+i) := by decide +kernel

theorem threshold_19_12 : ∀ i ∈ List.range 1, ThresholdAt 19 (12+i) := by decide +kernel

theorem threshold_19_13 : ∀ i ∈ List.range 1, ThresholdAt 19 (13+i) := by decide +kernel

theorem threshold_19_14 : ∀ i ∈ List.range 1, ThresholdAt 19 (14+i) := by decide +kernel

theorem threshold_19_15 : ∀ i ∈ List.range 1, ThresholdAt 19 (15+i) := by decide +kernel

theorem threshold_19_16 : ∀ i ∈ List.range 1, ThresholdAt 19 (16+i) := by decide +kernel

theorem threshold_19_17 : ∀ i ∈ List.range 1, ThresholdAt 19 (17+i) := by decide +kernel

theorem threshold_19_18 : ∀ i ∈ List.range 1, ThresholdAt 19 (18+i) := by decide +kernel

theorem threshold_19_19 : ∀ i ∈ List.range 1, ThresholdAt 19 (19+i) := by decide +kernel

theorem threshold_19_20 : ∀ i ∈ List.range 1, ThresholdAt 19 (20+i) := by decide +kernel

theorem threshold_19_21 : ∀ i ∈ List.range 1, ThresholdAt 19 (21+i) := by decide +kernel

theorem threshold_19_22 : ∀ i ∈ List.range 1, ThresholdAt 19 (22+i) := by decide +kernel

theorem threshold_19_23 : ∀ i ∈ List.range 1, ThresholdAt 19 (23+i) := by decide +kernel

theorem threshold_19_24 : ∀ i ∈ List.range 1, ThresholdAt 19 (24+i) := by decide +kernel

theorem threshold_19_25 : ∀ i ∈ List.range 1, ThresholdAt 19 (25+i) := by decide +kernel

theorem threshold_19_26 : ∀ i ∈ List.range 1, ThresholdAt 19 (26+i) := by decide +kernel

theorem threshold_19_27 : ∀ i ∈ List.range 1, ThresholdAt 19 (27+i) := by decide +kernel

theorem threshold_19_28 : ∀ i ∈ List.range 1, ThresholdAt 19 (28+i) := by decide +kernel

theorem threshold_19_29 : ∀ i ∈ List.range 1, ThresholdAt 19 (29+i) := by decide +kernel

theorem threshold_19_30 : ∀ i ∈ List.range 1, ThresholdAt 19 (30+i) := by decide +kernel

theorem threshold_19_31 : ∀ i ∈ List.range 1, ThresholdAt 19 (31+i) := by decide +kernel

theorem threshold_19_32 : ∀ i ∈ List.range 1, ThresholdAt 19 (32+i) := by decide +kernel

theorem threshold_19_33 : ∀ i ∈ List.range 1, ThresholdAt 19 (33+i) := by decide +kernel

theorem threshold_19_34 : ∀ i ∈ List.range 1, ThresholdAt 19 (34+i) := by decide +kernel

theorem threshold_19_35 : ∀ i ∈ List.range 1, ThresholdAt 19 (35+i) := by decide +kernel

theorem threshold_19_36 : ∀ i ∈ List.range 1, ThresholdAt 19 (36+i) := by decide +kernel

theorem threshold_19_37 : ∀ i ∈ List.range 1, ThresholdAt 19 (37+i) := by decide +kernel

theorem threshold_19_38 : ∀ i ∈ List.range 1, ThresholdAt 19 (38+i) := by decide +kernel

theorem threshold_19_39 : ∀ i ∈ List.range 1, ThresholdAt 19 (39+i) := by decide +kernel

theorem threshold_19_40 : ∀ i ∈ List.range 1, ThresholdAt 19 (40+i) := by decide +kernel

theorem threshold_19_41 : ∀ i ∈ List.range 1, ThresholdAt 19 (41+i) := by decide +kernel

theorem threshold_19_42 : ∀ i ∈ List.range 1, ThresholdAt 19 (42+i) := by decide +kernel

theorem threshold_19_43 : ∀ i ∈ List.range 1, ThresholdAt 19 (43+i) := by decide +kernel

theorem threshold_19_44 : ∀ i ∈ List.range 1, ThresholdAt 19 (44+i) := by decide +kernel

theorem threshold_19_45 : ∀ i ∈ List.range 1, ThresholdAt 19 (45+i) := by decide +kernel

theorem threshold_19_46 : ∀ i ∈ List.range 1, ThresholdAt 19 (46+i) := by decide +kernel

theorem threshold_19_47 : ∀ i ∈ List.range 1, ThresholdAt 19 (47+i) := by decide +kernel

theorem threshold_19_48 : ∀ i ∈ List.range 1, ThresholdAt 19 (48+i) := by decide +kernel

theorem threshold_19_49 : ∀ i ∈ List.range 1, ThresholdAt 19 (49+i) := by decide +kernel

theorem threshold_19_50 : ∀ i ∈ List.range 1, ThresholdAt 19 (50+i) := by decide +kernel

theorem threshold_19_51 : ∀ i ∈ List.range 1, ThresholdAt 19 (51+i) := by decide +kernel

theorem threshold_19_52 : ∀ i ∈ List.range 1, ThresholdAt 19 (52+i) := by decide +kernel

theorem threshold_19_53 : ∀ i ∈ List.range 1, ThresholdAt 19 (53+i) := by decide +kernel

theorem threshold_19_54 : ∀ i ∈ List.range 1, ThresholdAt 19 (54+i) := by decide +kernel

theorem threshold_19_55 : ∀ i ∈ List.range 1, ThresholdAt 19 (55+i) := by decide +kernel

theorem threshold_19_56 : ∀ i ∈ List.range 1, ThresholdAt 19 (56+i) := by decide +kernel

theorem threshold_19_57 : ∀ i ∈ List.range 1, ThresholdAt 19 (57+i) := by decide +kernel

theorem threshold_19_58 : ∀ i ∈ List.range 1, ThresholdAt 19 (58+i) := by decide +kernel

theorem threshold_19_59 : ∀ i ∈ List.range 1, ThresholdAt 19 (59+i) := by decide +kernel

theorem threshold_19_60 : ∀ i ∈ List.range 1, ThresholdAt 19 (60+i) := by decide +kernel

theorem threshold_19_61 : ∀ i ∈ List.range 1, ThresholdAt 19 (61+i) := by decide +kernel

theorem threshold_19_62 : ∀ i ∈ List.range 1, ThresholdAt 19 (62+i) := by decide +kernel

theorem threshold_19_63 : ∀ i ∈ List.range 1, ThresholdAt 19 (63+i) := by decide +kernel

theorem threshold_19_64 : ∀ i ∈ List.range 1, ThresholdAt 19 (64+i) := by decide +kernel

theorem threshold_19_65 : ∀ i ∈ List.range 1, ThresholdAt 19 (65+i) := by decide +kernel

theorem threshold_19_66 : ∀ i ∈ List.range 1, ThresholdAt 19 (66+i) := by decide +kernel

theorem threshold_19_67 : ∀ i ∈ List.range 1, ThresholdAt 19 (67+i) := by decide +kernel

theorem threshold_19_68 : ∀ i ∈ List.range 1, ThresholdAt 19 (68+i) := by decide +kernel

theorem threshold_19_69 : ∀ i ∈ List.range 1, ThresholdAt 19 (69+i) := by decide +kernel

theorem threshold_19_70 : ∀ i ∈ List.range 1, ThresholdAt 19 (70+i) := by decide +kernel

theorem threshold_19_71 : ∀ i ∈ List.range 1, ThresholdAt 19 (71+i) := by decide +kernel

theorem threshold_19_72 : ∀ i ∈ List.range 1, ThresholdAt 19 (72+i) := by decide +kernel

theorem threshold_19_73 : ∀ i ∈ List.range 1, ThresholdAt 19 (73+i) := by decide +kernel

theorem threshold_19_74 : ∀ i ∈ List.range 1, ThresholdAt 19 (74+i) := by decide +kernel

theorem threshold_19_75 : ∀ i ∈ List.range 1, ThresholdAt 19 (75+i) := by decide +kernel

theorem threshold_19_76 : ∀ i ∈ List.range 1, ThresholdAt 19 (76+i) := by decide +kernel

theorem threshold_19_77 : ∀ i ∈ List.range 1, ThresholdAt 19 (77+i) := by decide +kernel

theorem threshold_19_78 : ∀ i ∈ List.range 1, ThresholdAt 19 (78+i) := by decide +kernel

theorem threshold_19_79 : ∀ i ∈ List.range 1, ThresholdAt 19 (79+i) := by decide +kernel

theorem threshold_19_80 : ∀ i ∈ List.range 1, ThresholdAt 19 (80+i) := by decide +kernel

theorem threshold_19_81 : ∀ i ∈ List.range 1, ThresholdAt 19 (81+i) := by decide +kernel

theorem threshold_19_82 : ∀ i ∈ List.range 1, ThresholdAt 19 (82+i) := by decide +kernel

theorem threshold_19_83 : ∀ i ∈ List.range 1, ThresholdAt 19 (83+i) := by decide +kernel

theorem threshold_19_84 : ∀ i ∈ List.range 1, ThresholdAt 19 (84+i) := by decide +kernel

theorem threshold_19_85 : ∀ i ∈ List.range 1, ThresholdAt 19 (85+i) := by decide +kernel

theorem threshold_19_86 : ∀ i ∈ List.range 1, ThresholdAt 19 (86+i) := by decide +kernel

theorem threshold_19_87 : ∀ i ∈ List.range 1, ThresholdAt 19 (87+i) := by decide +kernel

theorem threshold_19_88 : ∀ i ∈ List.range 1, ThresholdAt 19 (88+i) := by decide +kernel

theorem threshold_19_89 : ∀ i ∈ List.range 1, ThresholdAt 19 (89+i) := by decide +kernel

theorem threshold_19_90 : ∀ i ∈ List.range 1, ThresholdAt 19 (90+i) := by decide +kernel

theorem threshold_19_91 : ∀ i ∈ List.range 1, ThresholdAt 19 (91+i) := by decide +kernel

theorem threshold_19_92 : ∀ i ∈ List.range 1, ThresholdAt 19 (92+i) := by decide +kernel

theorem threshold_19_93 : ∀ i ∈ List.range 1, ThresholdAt 19 (93+i) := by decide +kernel

theorem threshold_19_94 : ∀ i ∈ List.range 1, ThresholdAt 19 (94+i) := by decide +kernel

theorem threshold_19_95 : ∀ i ∈ List.range 1, ThresholdAt 19 (95+i) := by decide +kernel

theorem threshold_19_96 : ∀ i ∈ List.range 1, ThresholdAt 19 (96+i) := by decide +kernel

theorem threshold_19_97 : ∀ i ∈ List.range 1, ThresholdAt 19 (97+i) := by decide +kernel

theorem threshold_19_98 : ∀ i ∈ List.range 1, ThresholdAt 19 (98+i) := by decide +kernel

theorem threshold_19_99 : ∀ i ∈ List.range 1, ThresholdAt 19 (99+i) := by decide +kernel

theorem threshold_19_100 : ∀ i ∈ List.range 1, ThresholdAt 19 (100+i) := by decide +kernel

theorem threshold_19_101 : ∀ i ∈ List.range 1, ThresholdAt 19 (101+i) := by decide +kernel

theorem threshold_19_102 : ∀ i ∈ List.range 1, ThresholdAt 19 (102+i) := by decide +kernel

theorem threshold_19_103 : ∀ i ∈ List.range 1, ThresholdAt 19 (103+i) := by decide +kernel

theorem threshold_19_104 : ∀ i ∈ List.range 1, ThresholdAt 19 (104+i) := by decide +kernel

theorem threshold_19_105 : ∀ i ∈ List.range 1, ThresholdAt 19 (105+i) := by decide +kernel

theorem threshold_19_106 : ∀ i ∈ List.range 1, ThresholdAt 19 (106+i) := by decide +kernel

theorem threshold_19_107 : ∀ i ∈ List.range 1, ThresholdAt 19 (107+i) := by decide +kernel

theorem threshold_19_108 : ∀ i ∈ List.range 1, ThresholdAt 19 (108+i) := by decide +kernel

theorem threshold_19_109 : ∀ i ∈ List.range 1, ThresholdAt 19 (109+i) := by decide +kernel

theorem threshold_19_110 : ∀ i ∈ List.range 1, ThresholdAt 19 (110+i) := by decide +kernel

theorem threshold_19_111 : ∀ i ∈ List.range 1, ThresholdAt 19 (111+i) := by decide +kernel

theorem threshold_19_112 : ∀ i ∈ List.range 1, ThresholdAt 19 (112+i) := by decide +kernel

theorem threshold_19_113 : ∀ i ∈ List.range 1, ThresholdAt 19 (113+i) := by decide +kernel

theorem threshold_19_114 : ∀ i ∈ List.range 1, ThresholdAt 19 (114+i) := by decide +kernel

theorem threshold_19_115 : ∀ i ∈ List.range 1, ThresholdAt 19 (115+i) := by decide +kernel

theorem threshold_19_116 : ∀ i ∈ List.range 1, ThresholdAt 19 (116+i) := by decide +kernel

theorem threshold_19_117 : ∀ i ∈ List.range 1, ThresholdAt 19 (117+i) := by decide +kernel

theorem threshold_19_118 : ∀ i ∈ List.range 1, ThresholdAt 19 (118+i) := by decide +kernel

theorem threshold_19_119 : ∀ i ∈ List.range 1, ThresholdAt 19 (119+i) := by decide +kernel

theorem threshold_19_120 : ∀ i ∈ List.range 1, ThresholdAt 19 (120+i) := by decide +kernel

theorem threshold_19_121 : ∀ i ∈ List.range 1, ThresholdAt 19 (121+i) := by decide +kernel

theorem threshold_19_122 : ∀ i ∈ List.range 1, ThresholdAt 19 (122+i) := by decide +kernel

theorem threshold_19_123 : ∀ i ∈ List.range 1, ThresholdAt 19 (123+i) := by decide +kernel

theorem threshold_19_124 : ∀ i ∈ List.range 1, ThresholdAt 19 (124+i) := by decide +kernel

theorem threshold_19_125 : ∀ i ∈ List.range 1, ThresholdAt 19 (125+i) := by decide +kernel

theorem threshold_19_126 : ∀ i ∈ List.range 1, ThresholdAt 19 (126+i) := by decide +kernel

theorem threshold_19_127 : ∀ i ∈ List.range 1, ThresholdAt 19 (127+i) := by decide +kernel

theorem threshold_19_128 : ∀ i ∈ List.range 1, ThresholdAt 19 (128+i) := by decide +kernel

theorem threshold_19_129 : ∀ i ∈ List.range 1, ThresholdAt 19 (129+i) := by decide +kernel

theorem threshold_19_130 : ∀ i ∈ List.range 1, ThresholdAt 19 (130+i) := by decide +kernel

theorem threshold_19 (v : ℕ) (hv : v ∈ List.range 131) : ThresholdAt 19 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 19 v)
  have h := (join 0 65 66 (join 0 32 33 (join 0 16 16 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_19_0 threshold_19_1) (join 2 1 1 threshold_19_2 threshold_19_3)) (join 4 2 2 (join 4 1 1 threshold_19_4 threshold_19_5) (join 6 1 1 threshold_19_6 threshold_19_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_19_8 threshold_19_9) (join 10 1 1 threshold_19_10 threshold_19_11)) (join 12 2 2 (join 12 1 1 threshold_19_12 threshold_19_13) (join 14 1 1 threshold_19_14 threshold_19_15)))) (join 16 8 8 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_19_16 threshold_19_17) (join 18 1 1 threshold_19_18 threshold_19_19)) (join 20 2 2 (join 20 1 1 threshold_19_20 threshold_19_21) (join 22 1 1 threshold_19_22 threshold_19_23))) (join 24 4 4 (join 24 2 2 (join 24 1 1 threshold_19_24 threshold_19_25) (join 26 1 1 threshold_19_26 threshold_19_27)) (join 28 2 2 (join 28 1 1 threshold_19_28 threshold_19_29) (join 30 1 1 threshold_19_30 threshold_19_31))))) (join 32 16 17 (join 32 8 8 (join 32 4 4 (join 32 2 2 (join 32 1 1 threshold_19_32 threshold_19_33) (join 34 1 1 threshold_19_34 threshold_19_35)) (join 36 2 2 (join 36 1 1 threshold_19_36 threshold_19_37) (join 38 1 1 threshold_19_38 threshold_19_39))) (join 40 4 4 (join 40 2 2 (join 40 1 1 threshold_19_40 threshold_19_41) (join 42 1 1 threshold_19_42 threshold_19_43)) (join 44 2 2 (join 44 1 1 threshold_19_44 threshold_19_45) (join 46 1 1 threshold_19_46 threshold_19_47)))) (join 48 8 9 (join 48 4 4 (join 48 2 2 (join 48 1 1 threshold_19_48 threshold_19_49) (join 50 1 1 threshold_19_50 threshold_19_51)) (join 52 2 2 (join 52 1 1 threshold_19_52 threshold_19_53) (join 54 1 1 threshold_19_54 threshold_19_55))) (join 56 4 5 (join 56 2 2 (join 56 1 1 threshold_19_56 threshold_19_57) (join 58 1 1 threshold_19_58 threshold_19_59)) (join 60 2 3 (join 60 1 1 threshold_19_60 threshold_19_61) (join 62 1 2 threshold_19_62 (join 63 1 1 threshold_19_63 threshold_19_64))))))) (join 65 33 33 (join 65 16 17 (join 65 8 8 (join 65 4 4 (join 65 2 2 (join 65 1 1 threshold_19_65 threshold_19_66) (join 67 1 1 threshold_19_67 threshold_19_68)) (join 69 2 2 (join 69 1 1 threshold_19_69 threshold_19_70) (join 71 1 1 threshold_19_71 threshold_19_72))) (join 73 4 4 (join 73 2 2 (join 73 1 1 threshold_19_73 threshold_19_74) (join 75 1 1 threshold_19_75 threshold_19_76)) (join 77 2 2 (join 77 1 1 threshold_19_77 threshold_19_78) (join 79 1 1 threshold_19_79 threshold_19_80)))) (join 81 8 9 (join 81 4 4 (join 81 2 2 (join 81 1 1 threshold_19_81 threshold_19_82) (join 83 1 1 threshold_19_83 threshold_19_84)) (join 85 2 2 (join 85 1 1 threshold_19_85 threshold_19_86) (join 87 1 1 threshold_19_87 threshold_19_88))) (join 89 4 5 (join 89 2 2 (join 89 1 1 threshold_19_89 threshold_19_90) (join 91 1 1 threshold_19_91 threshold_19_92)) (join 93 2 3 (join 93 1 1 threshold_19_93 threshold_19_94) (join 95 1 2 threshold_19_95 (join 96 1 1 threshold_19_96 threshold_19_97)))))) (join 98 16 17 (join 98 8 8 (join 98 4 4 (join 98 2 2 (join 98 1 1 threshold_19_98 threshold_19_99) (join 100 1 1 threshold_19_100 threshold_19_101)) (join 102 2 2 (join 102 1 1 threshold_19_102 threshold_19_103) (join 104 1 1 threshold_19_104 threshold_19_105))) (join 106 4 4 (join 106 2 2 (join 106 1 1 threshold_19_106 threshold_19_107) (join 108 1 1 threshold_19_108 threshold_19_109)) (join 110 2 2 (join 110 1 1 threshold_19_110 threshold_19_111) (join 112 1 1 threshold_19_112 threshold_19_113)))) (join 114 8 9 (join 114 4 4 (join 114 2 2 (join 114 1 1 threshold_19_114 threshold_19_115) (join 116 1 1 threshold_19_116 threshold_19_117)) (join 118 2 2 (join 118 1 1 threshold_19_118 threshold_19_119) (join 120 1 1 threshold_19_120 threshold_19_121))) (join 122 4 5 (join 122 2 2 (join 122 1 1 threshold_19_122 threshold_19_123) (join 124 1 1 threshold_19_124 threshold_19_125)) (join 126 2 3 (join 126 1 1 threshold_19_126 threshold_19_127) (join 128 1 2 threshold_19_128 (join 129 1 1 threshold_19_129 threshold_19_130))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_19_0 : ∀ i ∈ List.range 4, LedgerAt 19 (0+i) := by decide +kernel

theorem ledger_19_4 : ∀ i ∈ List.range 4, LedgerAt 19 (4+i) := by decide +kernel

theorem ledger_19_8 : ∀ i ∈ List.range 4, LedgerAt 19 (8+i) := by decide +kernel

theorem ledger_19_12 : ∀ i ∈ List.range 4, LedgerAt 19 (12+i) := by decide +kernel

theorem ledger_19_16 : ∀ i ∈ List.range 4, LedgerAt 19 (16+i) := by decide +kernel

theorem ledger_19_20 : ∀ i ∈ List.range 4, LedgerAt 19 (20+i) := by decide +kernel

theorem ledger_19_24 : ∀ i ∈ List.range 4, LedgerAt 19 (24+i) := by decide +kernel

theorem ledger_19_28 : ∀ i ∈ List.range 4, LedgerAt 19 (28+i) := by decide +kernel

theorem ledger_19_32 : ∀ i ∈ List.range 4, LedgerAt 19 (32+i) := by decide +kernel

theorem ledger_19_36 : ∀ i ∈ List.range 4, LedgerAt 19 (36+i) := by decide +kernel

theorem ledger_19_40 : ∀ i ∈ List.range 4, LedgerAt 19 (40+i) := by decide +kernel

theorem ledger_19_44 : ∀ i ∈ List.range 4, LedgerAt 19 (44+i) := by decide +kernel

theorem ledger_19_48 : ∀ i ∈ List.range 4, LedgerAt 19 (48+i) := by decide +kernel

theorem ledger_19_52 : ∀ i ∈ List.range 4, LedgerAt 19 (52+i) := by decide +kernel

theorem ledger_19_56 : ∀ i ∈ List.range 4, LedgerAt 19 (56+i) := by decide +kernel

theorem ledger_19_60 : ∀ i ∈ List.range 4, LedgerAt 19 (60+i) := by decide +kernel

theorem ledger_19_64 : ∀ i ∈ List.range 4, LedgerAt 19 (64+i) := by decide +kernel

theorem ledger_19_68 : ∀ i ∈ List.range 4, LedgerAt 19 (68+i) := by decide +kernel

theorem ledger_19_72 : ∀ i ∈ List.range 4, LedgerAt 19 (72+i) := by decide +kernel

theorem ledger_19_76 : ∀ i ∈ List.range 4, LedgerAt 19 (76+i) := by decide +kernel

theorem ledger_19_80 : ∀ i ∈ List.range 4, LedgerAt 19 (80+i) := by decide +kernel

theorem ledger_19_84 : ∀ i ∈ List.range 4, LedgerAt 19 (84+i) := by decide +kernel

theorem ledger_19_88 : ∀ i ∈ List.range 4, LedgerAt 19 (88+i) := by decide +kernel

theorem ledger_19_92 : ∀ i ∈ List.range 4, LedgerAt 19 (92+i) := by decide +kernel

theorem ledger_19_96 : ∀ i ∈ List.range 4, LedgerAt 19 (96+i) := by decide +kernel

theorem ledger_19_100 : ∀ i ∈ List.range 4, LedgerAt 19 (100+i) := by decide +kernel

theorem ledger_19_104 : ∀ i ∈ List.range 4, LedgerAt 19 (104+i) := by decide +kernel

theorem ledger_19_108 : ∀ i ∈ List.range 4, LedgerAt 19 (108+i) := by decide +kernel

theorem ledger_19_112 : ∀ i ∈ List.range 4, LedgerAt 19 (112+i) := by decide +kernel

theorem ledger_19_116 : ∀ i ∈ List.range 4, LedgerAt 19 (116+i) := by decide +kernel

theorem ledger_19_120 : ∀ i ∈ List.range 4, LedgerAt 19 (120+i) := by decide +kernel

theorem ledger_19_124 : ∀ i ∈ List.range 4, LedgerAt 19 (124+i) := by decide +kernel

theorem ledger_19_128 : ∀ i ∈ List.range 3, LedgerAt 19 (128+i) := by decide +kernel

theorem ledger_19 (v : ℕ) (hv : v ∈ List.range 131) : LedgerAt 19 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 19 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_19_0 ledger_19_4) (join 8 4 4 ledger_19_8 ledger_19_12)) (join 16 8 8 (join 16 4 4 ledger_19_16 ledger_19_20) (join 24 4 4 ledger_19_24 ledger_19_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_19_32 ledger_19_36) (join 40 4 4 ledger_19_40 ledger_19_44)) (join 48 8 8 (join 48 4 4 ledger_19_48 ledger_19_52) (join 56 4 4 ledger_19_56 ledger_19_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_19_64 ledger_19_68) (join 72 4 4 ledger_19_72 ledger_19_76)) (join 80 8 8 (join 80 4 4 ledger_19_80 ledger_19_84) (join 88 4 4 ledger_19_88 ledger_19_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 ledger_19_96 ledger_19_100) (join 104 4 4 ledger_19_104 ledger_19_108)) (join 112 8 11 (join 112 4 4 ledger_19_112 ledger_19_116) (join 120 4 7 ledger_19_120 (join 124 4 3 ledger_19_124 ledger_19_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
