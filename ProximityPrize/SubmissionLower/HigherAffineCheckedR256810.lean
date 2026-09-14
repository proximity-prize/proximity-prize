import ProximityPrize.SubmissionLower.HigherAffineCheckedR246810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
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

theorem single_25_124 : ∀ i ∈ List.range 4, SingleAt 25 (124+i) := by decide +kernel

theorem single_25_128 : ∀ i ∈ List.range 4, SingleAt 25 (128+i) := by decide +kernel

theorem single_25 (v : ℕ) (hv : v ∈ List.range 132) : SingleAt 25 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 25 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_25_0 single_25_4) (join 8 4 4 single_25_8 single_25_12)) (join 16 8 8 (join 16 4 4 single_25_16 single_25_20) (join 24 4 4 single_25_24 single_25_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_25_32 single_25_36) (join 40 4 4 single_25_40 single_25_44)) (join 48 8 8 (join 48 4 4 single_25_48 single_25_52) (join 56 4 4 single_25_56 single_25_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_25_64 single_25_68) (join 72 4 4 single_25_72 single_25_76)) (join 80 8 8 (join 80 4 4 single_25_80 single_25_84) (join 88 4 4 single_25_88 single_25_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 single_25_96 single_25_100) (join 104 4 4 single_25_104 single_25_108)) (join 112 8 12 (join 112 4 4 single_25_112 single_25_116) (join 120 4 8 single_25_120 (join 124 4 4 single_25_124 single_25_128))))))
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

theorem phase_25_124 : ∀ i ∈ List.range 4, PhaseAt 25 (124+i) := by decide +kernel

theorem phase_25_128 : ∀ i ∈ List.range 4, PhaseAt 25 (128+i) := by decide +kernel

theorem phase_25 (v : ℕ) (hv : v ∈ List.range 132) : PhaseAt 25 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 25 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_25_0 phase_25_4) (join 8 4 4 phase_25_8 phase_25_12)) (join 16 8 8 (join 16 4 4 phase_25_16 phase_25_20) (join 24 4 4 phase_25_24 phase_25_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_25_32 phase_25_36) (join 40 4 4 phase_25_40 phase_25_44)) (join 48 8 8 (join 48 4 4 phase_25_48 phase_25_52) (join 56 4 4 phase_25_56 phase_25_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_25_64 phase_25_68) (join 72 4 4 phase_25_72 phase_25_76)) (join 80 8 8 (join 80 4 4 phase_25_80 phase_25_84) (join 88 4 4 phase_25_88 phase_25_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 phase_25_96 phase_25_100) (join 104 4 4 phase_25_104 phase_25_108)) (join 112 8 12 (join 112 4 4 phase_25_112 phase_25_116) (join 120 4 8 phase_25_120 (join 124 4 4 phase_25_124 phase_25_128))))))
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

theorem threshold_25_125 : ∀ i ∈ List.range 1, ThresholdAt 25 (125+i) := by decide +kernel

theorem threshold_25_126 : ∀ i ∈ List.range 1, ThresholdAt 25 (126+i) := by decide +kernel

theorem threshold_25_127 : ∀ i ∈ List.range 1, ThresholdAt 25 (127+i) := by decide +kernel

theorem threshold_25_128 : ∀ i ∈ List.range 1, ThresholdAt 25 (128+i) := by decide +kernel

theorem threshold_25_129 : ∀ i ∈ List.range 1, ThresholdAt 25 (129+i) := by decide +kernel

theorem threshold_25_130 : ∀ i ∈ List.range 1, ThresholdAt 25 (130+i) := by decide +kernel

theorem threshold_25_131 : ∀ i ∈ List.range 1, ThresholdAt 25 (131+i) := by decide +kernel

theorem threshold_25 (v : ℕ) (hv : v ∈ List.range 132) : ThresholdAt 25 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 25 v)
  have h := (join 0 66 66 (join 0 33 33 (join 0 16 17 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_25_0 threshold_25_1) (join 2 1 1 threshold_25_2 threshold_25_3)) (join 4 2 2 (join 4 1 1 threshold_25_4 threshold_25_5) (join 6 1 1 threshold_25_6 threshold_25_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_25_8 threshold_25_9) (join 10 1 1 threshold_25_10 threshold_25_11)) (join 12 2 2 (join 12 1 1 threshold_25_12 threshold_25_13) (join 14 1 1 threshold_25_14 threshold_25_15)))) (join 16 8 9 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_25_16 threshold_25_17) (join 18 1 1 threshold_25_18 threshold_25_19)) (join 20 2 2 (join 20 1 1 threshold_25_20 threshold_25_21) (join 22 1 1 threshold_25_22 threshold_25_23))) (join 24 4 5 (join 24 2 2 (join 24 1 1 threshold_25_24 threshold_25_25) (join 26 1 1 threshold_25_26 threshold_25_27)) (join 28 2 3 (join 28 1 1 threshold_25_28 threshold_25_29) (join 30 1 2 threshold_25_30 (join 31 1 1 threshold_25_31 threshold_25_32)))))) (join 33 16 17 (join 33 8 8 (join 33 4 4 (join 33 2 2 (join 33 1 1 threshold_25_33 threshold_25_34) (join 35 1 1 threshold_25_35 threshold_25_36)) (join 37 2 2 (join 37 1 1 threshold_25_37 threshold_25_38) (join 39 1 1 threshold_25_39 threshold_25_40))) (join 41 4 4 (join 41 2 2 (join 41 1 1 threshold_25_41 threshold_25_42) (join 43 1 1 threshold_25_43 threshold_25_44)) (join 45 2 2 (join 45 1 1 threshold_25_45 threshold_25_46) (join 47 1 1 threshold_25_47 threshold_25_48)))) (join 49 8 9 (join 49 4 4 (join 49 2 2 (join 49 1 1 threshold_25_49 threshold_25_50) (join 51 1 1 threshold_25_51 threshold_25_52)) (join 53 2 2 (join 53 1 1 threshold_25_53 threshold_25_54) (join 55 1 1 threshold_25_55 threshold_25_56))) (join 57 4 5 (join 57 2 2 (join 57 1 1 threshold_25_57 threshold_25_58) (join 59 1 1 threshold_25_59 threshold_25_60)) (join 61 2 3 (join 61 1 1 threshold_25_61 threshold_25_62) (join 63 1 2 threshold_25_63 (join 64 1 1 threshold_25_64 threshold_25_65))))))) (join 66 33 33 (join 66 16 17 (join 66 8 8 (join 66 4 4 (join 66 2 2 (join 66 1 1 threshold_25_66 threshold_25_67) (join 68 1 1 threshold_25_68 threshold_25_69)) (join 70 2 2 (join 70 1 1 threshold_25_70 threshold_25_71) (join 72 1 1 threshold_25_72 threshold_25_73))) (join 74 4 4 (join 74 2 2 (join 74 1 1 threshold_25_74 threshold_25_75) (join 76 1 1 threshold_25_76 threshold_25_77)) (join 78 2 2 (join 78 1 1 threshold_25_78 threshold_25_79) (join 80 1 1 threshold_25_80 threshold_25_81)))) (join 82 8 9 (join 82 4 4 (join 82 2 2 (join 82 1 1 threshold_25_82 threshold_25_83) (join 84 1 1 threshold_25_84 threshold_25_85)) (join 86 2 2 (join 86 1 1 threshold_25_86 threshold_25_87) (join 88 1 1 threshold_25_88 threshold_25_89))) (join 90 4 5 (join 90 2 2 (join 90 1 1 threshold_25_90 threshold_25_91) (join 92 1 1 threshold_25_92 threshold_25_93)) (join 94 2 3 (join 94 1 1 threshold_25_94 threshold_25_95) (join 96 1 2 threshold_25_96 (join 97 1 1 threshold_25_97 threshold_25_98)))))) (join 99 16 17 (join 99 8 8 (join 99 4 4 (join 99 2 2 (join 99 1 1 threshold_25_99 threshold_25_100) (join 101 1 1 threshold_25_101 threshold_25_102)) (join 103 2 2 (join 103 1 1 threshold_25_103 threshold_25_104) (join 105 1 1 threshold_25_105 threshold_25_106))) (join 107 4 4 (join 107 2 2 (join 107 1 1 threshold_25_107 threshold_25_108) (join 109 1 1 threshold_25_109 threshold_25_110)) (join 111 2 2 (join 111 1 1 threshold_25_111 threshold_25_112) (join 113 1 1 threshold_25_113 threshold_25_114)))) (join 115 8 9 (join 115 4 4 (join 115 2 2 (join 115 1 1 threshold_25_115 threshold_25_116) (join 117 1 1 threshold_25_117 threshold_25_118)) (join 119 2 2 (join 119 1 1 threshold_25_119 threshold_25_120) (join 121 1 1 threshold_25_121 threshold_25_122))) (join 123 4 5 (join 123 2 2 (join 123 1 1 threshold_25_123 threshold_25_124) (join 125 1 1 threshold_25_125 threshold_25_126)) (join 127 2 3 (join 127 1 1 threshold_25_127 threshold_25_128) (join 129 1 2 threshold_25_129 (join 130 1 1 threshold_25_130 threshold_25_131))))))))
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

theorem ledger_25_124 : ∀ i ∈ List.range 4, LedgerAt 25 (124+i) := by decide +kernel

theorem ledger_25_128 : ∀ i ∈ List.range 4, LedgerAt 25 (128+i) := by decide +kernel

theorem ledger_25 (v : ℕ) (hv : v ∈ List.range 132) : LedgerAt 25 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 25 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_25_0 ledger_25_4) (join 8 4 4 ledger_25_8 ledger_25_12)) (join 16 8 8 (join 16 4 4 ledger_25_16 ledger_25_20) (join 24 4 4 ledger_25_24 ledger_25_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_25_32 ledger_25_36) (join 40 4 4 ledger_25_40 ledger_25_44)) (join 48 8 8 (join 48 4 4 ledger_25_48 ledger_25_52) (join 56 4 4 ledger_25_56 ledger_25_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_25_64 ledger_25_68) (join 72 4 4 ledger_25_72 ledger_25_76)) (join 80 8 8 (join 80 4 4 ledger_25_80 ledger_25_84) (join 88 4 4 ledger_25_88 ledger_25_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 ledger_25_96 ledger_25_100) (join 104 4 4 ledger_25_104 ledger_25_108)) (join 112 8 12 (join 112 4 4 ledger_25_112 ledger_25_116) (join 120 4 8 ledger_25_120 (join 124 4 4 ledger_25_124 ledger_25_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
