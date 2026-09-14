import ProximityPrize.SubmissionLower.HigherAffineCheckedR266810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_27_0 : ∀ i ∈ List.range 4, SingleAt 27 (0+i) := by decide +kernel

theorem single_27_4 : ∀ i ∈ List.range 4, SingleAt 27 (4+i) := by decide +kernel

theorem single_27_8 : ∀ i ∈ List.range 4, SingleAt 27 (8+i) := by decide +kernel

theorem single_27_12 : ∀ i ∈ List.range 4, SingleAt 27 (12+i) := by decide +kernel

theorem single_27_16 : ∀ i ∈ List.range 4, SingleAt 27 (16+i) := by decide +kernel

theorem single_27_20 : ∀ i ∈ List.range 4, SingleAt 27 (20+i) := by decide +kernel

theorem single_27_24 : ∀ i ∈ List.range 4, SingleAt 27 (24+i) := by decide +kernel

theorem single_27_28 : ∀ i ∈ List.range 4, SingleAt 27 (28+i) := by decide +kernel

theorem single_27_32 : ∀ i ∈ List.range 4, SingleAt 27 (32+i) := by decide +kernel

theorem single_27_36 : ∀ i ∈ List.range 4, SingleAt 27 (36+i) := by decide +kernel

theorem single_27_40 : ∀ i ∈ List.range 4, SingleAt 27 (40+i) := by decide +kernel

theorem single_27_44 : ∀ i ∈ List.range 4, SingleAt 27 (44+i) := by decide +kernel

theorem single_27_48 : ∀ i ∈ List.range 4, SingleAt 27 (48+i) := by decide +kernel

theorem single_27_52 : ∀ i ∈ List.range 4, SingleAt 27 (52+i) := by decide +kernel

theorem single_27_56 : ∀ i ∈ List.range 4, SingleAt 27 (56+i) := by decide +kernel

theorem single_27_60 : ∀ i ∈ List.range 4, SingleAt 27 (60+i) := by decide +kernel

theorem single_27_64 : ∀ i ∈ List.range 4, SingleAt 27 (64+i) := by decide +kernel

theorem single_27_68 : ∀ i ∈ List.range 4, SingleAt 27 (68+i) := by decide +kernel

theorem single_27_72 : ∀ i ∈ List.range 4, SingleAt 27 (72+i) := by decide +kernel

theorem single_27_76 : ∀ i ∈ List.range 4, SingleAt 27 (76+i) := by decide +kernel

theorem single_27_80 : ∀ i ∈ List.range 4, SingleAt 27 (80+i) := by decide +kernel

theorem single_27_84 : ∀ i ∈ List.range 4, SingleAt 27 (84+i) := by decide +kernel

theorem single_27_88 : ∀ i ∈ List.range 4, SingleAt 27 (88+i) := by decide +kernel

theorem single_27_92 : ∀ i ∈ List.range 4, SingleAt 27 (92+i) := by decide +kernel

theorem single_27_96 : ∀ i ∈ List.range 4, SingleAt 27 (96+i) := by decide +kernel

theorem single_27_100 : ∀ i ∈ List.range 4, SingleAt 27 (100+i) := by decide +kernel

theorem single_27_104 : ∀ i ∈ List.range 4, SingleAt 27 (104+i) := by decide +kernel

theorem single_27_108 : ∀ i ∈ List.range 4, SingleAt 27 (108+i) := by decide +kernel

theorem single_27_112 : ∀ i ∈ List.range 4, SingleAt 27 (112+i) := by decide +kernel

theorem single_27_116 : ∀ i ∈ List.range 4, SingleAt 27 (116+i) := by decide +kernel

theorem single_27_120 : ∀ i ∈ List.range 4, SingleAt 27 (120+i) := by decide +kernel

theorem single_27_124 : ∀ i ∈ List.range 4, SingleAt 27 (124+i) := by decide +kernel

theorem single_27_128 : ∀ i ∈ List.range 2, SingleAt 27 (128+i) := by decide +kernel

theorem single_27 (v : ℕ) (hv : v ∈ List.range 130) : SingleAt 27 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 27 v)
  have h := (join 0 64 66 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_27_0 single_27_4) (join 8 4 4 single_27_8 single_27_12)) (join 16 8 8 (join 16 4 4 single_27_16 single_27_20) (join 24 4 4 single_27_24 single_27_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_27_32 single_27_36) (join 40 4 4 single_27_40 single_27_44)) (join 48 8 8 (join 48 4 4 single_27_48 single_27_52) (join 56 4 4 single_27_56 single_27_60)))) (join 64 32 34 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_27_64 single_27_68) (join 72 4 4 single_27_72 single_27_76)) (join 80 8 8 (join 80 4 4 single_27_80 single_27_84) (join 88 4 4 single_27_88 single_27_92))) (join 96 16 18 (join 96 8 8 (join 96 4 4 single_27_96 single_27_100) (join 104 4 4 single_27_104 single_27_108)) (join 112 8 10 (join 112 4 4 single_27_112 single_27_116) (join 120 4 6 single_27_120 (join 124 4 2 single_27_124 single_27_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_27_0 : ∀ i ∈ List.range 4, PhaseAt 27 (0+i) := by decide +kernel

theorem phase_27_4 : ∀ i ∈ List.range 4, PhaseAt 27 (4+i) := by decide +kernel

theorem phase_27_8 : ∀ i ∈ List.range 4, PhaseAt 27 (8+i) := by decide +kernel

theorem phase_27_12 : ∀ i ∈ List.range 4, PhaseAt 27 (12+i) := by decide +kernel

theorem phase_27_16 : ∀ i ∈ List.range 4, PhaseAt 27 (16+i) := by decide +kernel

theorem phase_27_20 : ∀ i ∈ List.range 4, PhaseAt 27 (20+i) := by decide +kernel

theorem phase_27_24 : ∀ i ∈ List.range 4, PhaseAt 27 (24+i) := by decide +kernel

theorem phase_27_28 : ∀ i ∈ List.range 4, PhaseAt 27 (28+i) := by decide +kernel

theorem phase_27_32 : ∀ i ∈ List.range 4, PhaseAt 27 (32+i) := by decide +kernel

theorem phase_27_36 : ∀ i ∈ List.range 4, PhaseAt 27 (36+i) := by decide +kernel

theorem phase_27_40 : ∀ i ∈ List.range 4, PhaseAt 27 (40+i) := by decide +kernel

theorem phase_27_44 : ∀ i ∈ List.range 4, PhaseAt 27 (44+i) := by decide +kernel

theorem phase_27_48 : ∀ i ∈ List.range 4, PhaseAt 27 (48+i) := by decide +kernel

theorem phase_27_52 : ∀ i ∈ List.range 4, PhaseAt 27 (52+i) := by decide +kernel

theorem phase_27_56 : ∀ i ∈ List.range 4, PhaseAt 27 (56+i) := by decide +kernel

theorem phase_27_60 : ∀ i ∈ List.range 4, PhaseAt 27 (60+i) := by decide +kernel

theorem phase_27_64 : ∀ i ∈ List.range 4, PhaseAt 27 (64+i) := by decide +kernel

theorem phase_27_68 : ∀ i ∈ List.range 4, PhaseAt 27 (68+i) := by decide +kernel

theorem phase_27_72 : ∀ i ∈ List.range 4, PhaseAt 27 (72+i) := by decide +kernel

theorem phase_27_76 : ∀ i ∈ List.range 4, PhaseAt 27 (76+i) := by decide +kernel

theorem phase_27_80 : ∀ i ∈ List.range 4, PhaseAt 27 (80+i) := by decide +kernel

theorem phase_27_84 : ∀ i ∈ List.range 4, PhaseAt 27 (84+i) := by decide +kernel

theorem phase_27_88 : ∀ i ∈ List.range 4, PhaseAt 27 (88+i) := by decide +kernel

theorem phase_27_92 : ∀ i ∈ List.range 4, PhaseAt 27 (92+i) := by decide +kernel

theorem phase_27_96 : ∀ i ∈ List.range 4, PhaseAt 27 (96+i) := by decide +kernel

theorem phase_27_100 : ∀ i ∈ List.range 4, PhaseAt 27 (100+i) := by decide +kernel

theorem phase_27_104 : ∀ i ∈ List.range 4, PhaseAt 27 (104+i) := by decide +kernel

theorem phase_27_108 : ∀ i ∈ List.range 4, PhaseAt 27 (108+i) := by decide +kernel

theorem phase_27_112 : ∀ i ∈ List.range 4, PhaseAt 27 (112+i) := by decide +kernel

theorem phase_27_116 : ∀ i ∈ List.range 4, PhaseAt 27 (116+i) := by decide +kernel

theorem phase_27_120 : ∀ i ∈ List.range 4, PhaseAt 27 (120+i) := by decide +kernel

theorem phase_27_124 : ∀ i ∈ List.range 4, PhaseAt 27 (124+i) := by decide +kernel

theorem phase_27_128 : ∀ i ∈ List.range 2, PhaseAt 27 (128+i) := by decide +kernel

theorem phase_27 (v : ℕ) (hv : v ∈ List.range 130) : PhaseAt 27 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 27 v)
  have h := (join 0 64 66 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_27_0 phase_27_4) (join 8 4 4 phase_27_8 phase_27_12)) (join 16 8 8 (join 16 4 4 phase_27_16 phase_27_20) (join 24 4 4 phase_27_24 phase_27_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_27_32 phase_27_36) (join 40 4 4 phase_27_40 phase_27_44)) (join 48 8 8 (join 48 4 4 phase_27_48 phase_27_52) (join 56 4 4 phase_27_56 phase_27_60)))) (join 64 32 34 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_27_64 phase_27_68) (join 72 4 4 phase_27_72 phase_27_76)) (join 80 8 8 (join 80 4 4 phase_27_80 phase_27_84) (join 88 4 4 phase_27_88 phase_27_92))) (join 96 16 18 (join 96 8 8 (join 96 4 4 phase_27_96 phase_27_100) (join 104 4 4 phase_27_104 phase_27_108)) (join 112 8 10 (join 112 4 4 phase_27_112 phase_27_116) (join 120 4 6 phase_27_120 (join 124 4 2 phase_27_124 phase_27_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_27_0 : ∀ i ∈ List.range 1, ThresholdAt 27 (0+i) := by decide +kernel

theorem threshold_27_1 : ∀ i ∈ List.range 1, ThresholdAt 27 (1+i) := by decide +kernel

theorem threshold_27_2 : ∀ i ∈ List.range 1, ThresholdAt 27 (2+i) := by decide +kernel

theorem threshold_27_3 : ∀ i ∈ List.range 1, ThresholdAt 27 (3+i) := by decide +kernel

theorem threshold_27_4 : ∀ i ∈ List.range 1, ThresholdAt 27 (4+i) := by decide +kernel

theorem threshold_27_5 : ∀ i ∈ List.range 1, ThresholdAt 27 (5+i) := by decide +kernel

theorem threshold_27_6 : ∀ i ∈ List.range 1, ThresholdAt 27 (6+i) := by decide +kernel

theorem threshold_27_7 : ∀ i ∈ List.range 1, ThresholdAt 27 (7+i) := by decide +kernel

theorem threshold_27_8 : ∀ i ∈ List.range 1, ThresholdAt 27 (8+i) := by decide +kernel

theorem threshold_27_9 : ∀ i ∈ List.range 1, ThresholdAt 27 (9+i) := by decide +kernel

theorem threshold_27_10 : ∀ i ∈ List.range 1, ThresholdAt 27 (10+i) := by decide +kernel

theorem threshold_27_11 : ∀ i ∈ List.range 1, ThresholdAt 27 (11+i) := by decide +kernel

theorem threshold_27_12 : ∀ i ∈ List.range 1, ThresholdAt 27 (12+i) := by decide +kernel

theorem threshold_27_13 : ∀ i ∈ List.range 1, ThresholdAt 27 (13+i) := by decide +kernel

theorem threshold_27_14 : ∀ i ∈ List.range 1, ThresholdAt 27 (14+i) := by decide +kernel

theorem threshold_27_15 : ∀ i ∈ List.range 1, ThresholdAt 27 (15+i) := by decide +kernel

theorem threshold_27_16 : ∀ i ∈ List.range 1, ThresholdAt 27 (16+i) := by decide +kernel

theorem threshold_27_17 : ∀ i ∈ List.range 1, ThresholdAt 27 (17+i) := by decide +kernel

theorem threshold_27_18 : ∀ i ∈ List.range 1, ThresholdAt 27 (18+i) := by decide +kernel

theorem threshold_27_19 : ∀ i ∈ List.range 1, ThresholdAt 27 (19+i) := by decide +kernel

theorem threshold_27_20 : ∀ i ∈ List.range 1, ThresholdAt 27 (20+i) := by decide +kernel

theorem threshold_27_21 : ∀ i ∈ List.range 1, ThresholdAt 27 (21+i) := by decide +kernel

theorem threshold_27_22 : ∀ i ∈ List.range 1, ThresholdAt 27 (22+i) := by decide +kernel

theorem threshold_27_23 : ∀ i ∈ List.range 1, ThresholdAt 27 (23+i) := by decide +kernel

theorem threshold_27_24 : ∀ i ∈ List.range 1, ThresholdAt 27 (24+i) := by decide +kernel

theorem threshold_27_25 : ∀ i ∈ List.range 1, ThresholdAt 27 (25+i) := by decide +kernel

theorem threshold_27_26 : ∀ i ∈ List.range 1, ThresholdAt 27 (26+i) := by decide +kernel

theorem threshold_27_27 : ∀ i ∈ List.range 1, ThresholdAt 27 (27+i) := by decide +kernel

theorem threshold_27_28 : ∀ i ∈ List.range 1, ThresholdAt 27 (28+i) := by decide +kernel

theorem threshold_27_29 : ∀ i ∈ List.range 1, ThresholdAt 27 (29+i) := by decide +kernel

theorem threshold_27_30 : ∀ i ∈ List.range 1, ThresholdAt 27 (30+i) := by decide +kernel

theorem threshold_27_31 : ∀ i ∈ List.range 1, ThresholdAt 27 (31+i) := by decide +kernel

theorem threshold_27_32 : ∀ i ∈ List.range 1, ThresholdAt 27 (32+i) := by decide +kernel

theorem threshold_27_33 : ∀ i ∈ List.range 1, ThresholdAt 27 (33+i) := by decide +kernel

theorem threshold_27_34 : ∀ i ∈ List.range 1, ThresholdAt 27 (34+i) := by decide +kernel

theorem threshold_27_35 : ∀ i ∈ List.range 1, ThresholdAt 27 (35+i) := by decide +kernel

theorem threshold_27_36 : ∀ i ∈ List.range 1, ThresholdAt 27 (36+i) := by decide +kernel

theorem threshold_27_37 : ∀ i ∈ List.range 1, ThresholdAt 27 (37+i) := by decide +kernel

theorem threshold_27_38 : ∀ i ∈ List.range 1, ThresholdAt 27 (38+i) := by decide +kernel

theorem threshold_27_39 : ∀ i ∈ List.range 1, ThresholdAt 27 (39+i) := by decide +kernel

theorem threshold_27_40 : ∀ i ∈ List.range 1, ThresholdAt 27 (40+i) := by decide +kernel

theorem threshold_27_41 : ∀ i ∈ List.range 1, ThresholdAt 27 (41+i) := by decide +kernel

theorem threshold_27_42 : ∀ i ∈ List.range 1, ThresholdAt 27 (42+i) := by decide +kernel

theorem threshold_27_43 : ∀ i ∈ List.range 1, ThresholdAt 27 (43+i) := by decide +kernel

theorem threshold_27_44 : ∀ i ∈ List.range 1, ThresholdAt 27 (44+i) := by decide +kernel

theorem threshold_27_45 : ∀ i ∈ List.range 1, ThresholdAt 27 (45+i) := by decide +kernel

theorem threshold_27_46 : ∀ i ∈ List.range 1, ThresholdAt 27 (46+i) := by decide +kernel

theorem threshold_27_47 : ∀ i ∈ List.range 1, ThresholdAt 27 (47+i) := by decide +kernel

theorem threshold_27_48 : ∀ i ∈ List.range 1, ThresholdAt 27 (48+i) := by decide +kernel

theorem threshold_27_49 : ∀ i ∈ List.range 1, ThresholdAt 27 (49+i) := by decide +kernel

theorem threshold_27_50 : ∀ i ∈ List.range 1, ThresholdAt 27 (50+i) := by decide +kernel

theorem threshold_27_51 : ∀ i ∈ List.range 1, ThresholdAt 27 (51+i) := by decide +kernel

theorem threshold_27_52 : ∀ i ∈ List.range 1, ThresholdAt 27 (52+i) := by decide +kernel

theorem threshold_27_53 : ∀ i ∈ List.range 1, ThresholdAt 27 (53+i) := by decide +kernel

theorem threshold_27_54 : ∀ i ∈ List.range 1, ThresholdAt 27 (54+i) := by decide +kernel

theorem threshold_27_55 : ∀ i ∈ List.range 1, ThresholdAt 27 (55+i) := by decide +kernel

theorem threshold_27_56 : ∀ i ∈ List.range 1, ThresholdAt 27 (56+i) := by decide +kernel

theorem threshold_27_57 : ∀ i ∈ List.range 1, ThresholdAt 27 (57+i) := by decide +kernel

theorem threshold_27_58 : ∀ i ∈ List.range 1, ThresholdAt 27 (58+i) := by decide +kernel

theorem threshold_27_59 : ∀ i ∈ List.range 1, ThresholdAt 27 (59+i) := by decide +kernel

theorem threshold_27_60 : ∀ i ∈ List.range 1, ThresholdAt 27 (60+i) := by decide +kernel

theorem threshold_27_61 : ∀ i ∈ List.range 1, ThresholdAt 27 (61+i) := by decide +kernel

theorem threshold_27_62 : ∀ i ∈ List.range 1, ThresholdAt 27 (62+i) := by decide +kernel

theorem threshold_27_63 : ∀ i ∈ List.range 1, ThresholdAt 27 (63+i) := by decide +kernel

theorem threshold_27_64 : ∀ i ∈ List.range 1, ThresholdAt 27 (64+i) := by decide +kernel

theorem threshold_27_65 : ∀ i ∈ List.range 1, ThresholdAt 27 (65+i) := by decide +kernel

theorem threshold_27_66 : ∀ i ∈ List.range 1, ThresholdAt 27 (66+i) := by decide +kernel

theorem threshold_27_67 : ∀ i ∈ List.range 1, ThresholdAt 27 (67+i) := by decide +kernel

theorem threshold_27_68 : ∀ i ∈ List.range 1, ThresholdAt 27 (68+i) := by decide +kernel

theorem threshold_27_69 : ∀ i ∈ List.range 1, ThresholdAt 27 (69+i) := by decide +kernel

theorem threshold_27_70 : ∀ i ∈ List.range 1, ThresholdAt 27 (70+i) := by decide +kernel

theorem threshold_27_71 : ∀ i ∈ List.range 1, ThresholdAt 27 (71+i) := by decide +kernel

theorem threshold_27_72 : ∀ i ∈ List.range 1, ThresholdAt 27 (72+i) := by decide +kernel

theorem threshold_27_73 : ∀ i ∈ List.range 1, ThresholdAt 27 (73+i) := by decide +kernel

theorem threshold_27_74 : ∀ i ∈ List.range 1, ThresholdAt 27 (74+i) := by decide +kernel

theorem threshold_27_75 : ∀ i ∈ List.range 1, ThresholdAt 27 (75+i) := by decide +kernel

theorem threshold_27_76 : ∀ i ∈ List.range 1, ThresholdAt 27 (76+i) := by decide +kernel

theorem threshold_27_77 : ∀ i ∈ List.range 1, ThresholdAt 27 (77+i) := by decide +kernel

theorem threshold_27_78 : ∀ i ∈ List.range 1, ThresholdAt 27 (78+i) := by decide +kernel

theorem threshold_27_79 : ∀ i ∈ List.range 1, ThresholdAt 27 (79+i) := by decide +kernel

theorem threshold_27_80 : ∀ i ∈ List.range 1, ThresholdAt 27 (80+i) := by decide +kernel

theorem threshold_27_81 : ∀ i ∈ List.range 1, ThresholdAt 27 (81+i) := by decide +kernel

theorem threshold_27_82 : ∀ i ∈ List.range 1, ThresholdAt 27 (82+i) := by decide +kernel

theorem threshold_27_83 : ∀ i ∈ List.range 1, ThresholdAt 27 (83+i) := by decide +kernel

theorem threshold_27_84 : ∀ i ∈ List.range 1, ThresholdAt 27 (84+i) := by decide +kernel

theorem threshold_27_85 : ∀ i ∈ List.range 1, ThresholdAt 27 (85+i) := by decide +kernel

theorem threshold_27_86 : ∀ i ∈ List.range 1, ThresholdAt 27 (86+i) := by decide +kernel

theorem threshold_27_87 : ∀ i ∈ List.range 1, ThresholdAt 27 (87+i) := by decide +kernel

theorem threshold_27_88 : ∀ i ∈ List.range 1, ThresholdAt 27 (88+i) := by decide +kernel

theorem threshold_27_89 : ∀ i ∈ List.range 1, ThresholdAt 27 (89+i) := by decide +kernel

theorem threshold_27_90 : ∀ i ∈ List.range 1, ThresholdAt 27 (90+i) := by decide +kernel

theorem threshold_27_91 : ∀ i ∈ List.range 1, ThresholdAt 27 (91+i) := by decide +kernel

theorem threshold_27_92 : ∀ i ∈ List.range 1, ThresholdAt 27 (92+i) := by decide +kernel

theorem threshold_27_93 : ∀ i ∈ List.range 1, ThresholdAt 27 (93+i) := by decide +kernel

theorem threshold_27_94 : ∀ i ∈ List.range 1, ThresholdAt 27 (94+i) := by decide +kernel

theorem threshold_27_95 : ∀ i ∈ List.range 1, ThresholdAt 27 (95+i) := by decide +kernel

theorem threshold_27_96 : ∀ i ∈ List.range 1, ThresholdAt 27 (96+i) := by decide +kernel

theorem threshold_27_97 : ∀ i ∈ List.range 1, ThresholdAt 27 (97+i) := by decide +kernel

theorem threshold_27_98 : ∀ i ∈ List.range 1, ThresholdAt 27 (98+i) := by decide +kernel

theorem threshold_27_99 : ∀ i ∈ List.range 1, ThresholdAt 27 (99+i) := by decide +kernel

theorem threshold_27_100 : ∀ i ∈ List.range 1, ThresholdAt 27 (100+i) := by decide +kernel

theorem threshold_27_101 : ∀ i ∈ List.range 1, ThresholdAt 27 (101+i) := by decide +kernel

theorem threshold_27_102 : ∀ i ∈ List.range 1, ThresholdAt 27 (102+i) := by decide +kernel

theorem threshold_27_103 : ∀ i ∈ List.range 1, ThresholdAt 27 (103+i) := by decide +kernel

theorem threshold_27_104 : ∀ i ∈ List.range 1, ThresholdAt 27 (104+i) := by decide +kernel

theorem threshold_27_105 : ∀ i ∈ List.range 1, ThresholdAt 27 (105+i) := by decide +kernel

theorem threshold_27_106 : ∀ i ∈ List.range 1, ThresholdAt 27 (106+i) := by decide +kernel

theorem threshold_27_107 : ∀ i ∈ List.range 1, ThresholdAt 27 (107+i) := by decide +kernel

theorem threshold_27_108 : ∀ i ∈ List.range 1, ThresholdAt 27 (108+i) := by decide +kernel

theorem threshold_27_109 : ∀ i ∈ List.range 1, ThresholdAt 27 (109+i) := by decide +kernel

theorem threshold_27_110 : ∀ i ∈ List.range 1, ThresholdAt 27 (110+i) := by decide +kernel

theorem threshold_27_111 : ∀ i ∈ List.range 1, ThresholdAt 27 (111+i) := by decide +kernel

theorem threshold_27_112 : ∀ i ∈ List.range 1, ThresholdAt 27 (112+i) := by decide +kernel

theorem threshold_27_113 : ∀ i ∈ List.range 1, ThresholdAt 27 (113+i) := by decide +kernel

theorem threshold_27_114 : ∀ i ∈ List.range 1, ThresholdAt 27 (114+i) := by decide +kernel

theorem threshold_27_115 : ∀ i ∈ List.range 1, ThresholdAt 27 (115+i) := by decide +kernel

theorem threshold_27_116 : ∀ i ∈ List.range 1, ThresholdAt 27 (116+i) := by decide +kernel

theorem threshold_27_117 : ∀ i ∈ List.range 1, ThresholdAt 27 (117+i) := by decide +kernel

theorem threshold_27_118 : ∀ i ∈ List.range 1, ThresholdAt 27 (118+i) := by decide +kernel

theorem threshold_27_119 : ∀ i ∈ List.range 1, ThresholdAt 27 (119+i) := by decide +kernel

theorem threshold_27_120 : ∀ i ∈ List.range 1, ThresholdAt 27 (120+i) := by decide +kernel

theorem threshold_27_121 : ∀ i ∈ List.range 1, ThresholdAt 27 (121+i) := by decide +kernel

theorem threshold_27_122 : ∀ i ∈ List.range 1, ThresholdAt 27 (122+i) := by decide +kernel

theorem threshold_27_123 : ∀ i ∈ List.range 1, ThresholdAt 27 (123+i) := by decide +kernel

theorem threshold_27_124 : ∀ i ∈ List.range 1, ThresholdAt 27 (124+i) := by decide +kernel

theorem threshold_27_125 : ∀ i ∈ List.range 1, ThresholdAt 27 (125+i) := by decide +kernel

theorem threshold_27_126 : ∀ i ∈ List.range 1, ThresholdAt 27 (126+i) := by decide +kernel

theorem threshold_27_127 : ∀ i ∈ List.range 1, ThresholdAt 27 (127+i) := by decide +kernel

theorem threshold_27_128 : ∀ i ∈ List.range 1, ThresholdAt 27 (128+i) := by decide +kernel

theorem threshold_27_129 : ∀ i ∈ List.range 1, ThresholdAt 27 (129+i) := by decide +kernel

theorem threshold_27 (v : ℕ) (hv : v ∈ List.range 130) : ThresholdAt 27 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 27 v)
  have h := (join 0 65 65 (join 0 32 33 (join 0 16 16 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_27_0 threshold_27_1) (join 2 1 1 threshold_27_2 threshold_27_3)) (join 4 2 2 (join 4 1 1 threshold_27_4 threshold_27_5) (join 6 1 1 threshold_27_6 threshold_27_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_27_8 threshold_27_9) (join 10 1 1 threshold_27_10 threshold_27_11)) (join 12 2 2 (join 12 1 1 threshold_27_12 threshold_27_13) (join 14 1 1 threshold_27_14 threshold_27_15)))) (join 16 8 8 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_27_16 threshold_27_17) (join 18 1 1 threshold_27_18 threshold_27_19)) (join 20 2 2 (join 20 1 1 threshold_27_20 threshold_27_21) (join 22 1 1 threshold_27_22 threshold_27_23))) (join 24 4 4 (join 24 2 2 (join 24 1 1 threshold_27_24 threshold_27_25) (join 26 1 1 threshold_27_26 threshold_27_27)) (join 28 2 2 (join 28 1 1 threshold_27_28 threshold_27_29) (join 30 1 1 threshold_27_30 threshold_27_31))))) (join 32 16 17 (join 32 8 8 (join 32 4 4 (join 32 2 2 (join 32 1 1 threshold_27_32 threshold_27_33) (join 34 1 1 threshold_27_34 threshold_27_35)) (join 36 2 2 (join 36 1 1 threshold_27_36 threshold_27_37) (join 38 1 1 threshold_27_38 threshold_27_39))) (join 40 4 4 (join 40 2 2 (join 40 1 1 threshold_27_40 threshold_27_41) (join 42 1 1 threshold_27_42 threshold_27_43)) (join 44 2 2 (join 44 1 1 threshold_27_44 threshold_27_45) (join 46 1 1 threshold_27_46 threshold_27_47)))) (join 48 8 9 (join 48 4 4 (join 48 2 2 (join 48 1 1 threshold_27_48 threshold_27_49) (join 50 1 1 threshold_27_50 threshold_27_51)) (join 52 2 2 (join 52 1 1 threshold_27_52 threshold_27_53) (join 54 1 1 threshold_27_54 threshold_27_55))) (join 56 4 5 (join 56 2 2 (join 56 1 1 threshold_27_56 threshold_27_57) (join 58 1 1 threshold_27_58 threshold_27_59)) (join 60 2 3 (join 60 1 1 threshold_27_60 threshold_27_61) (join 62 1 2 threshold_27_62 (join 63 1 1 threshold_27_63 threshold_27_64))))))) (join 65 32 33 (join 65 16 16 (join 65 8 8 (join 65 4 4 (join 65 2 2 (join 65 1 1 threshold_27_65 threshold_27_66) (join 67 1 1 threshold_27_67 threshold_27_68)) (join 69 2 2 (join 69 1 1 threshold_27_69 threshold_27_70) (join 71 1 1 threshold_27_71 threshold_27_72))) (join 73 4 4 (join 73 2 2 (join 73 1 1 threshold_27_73 threshold_27_74) (join 75 1 1 threshold_27_75 threshold_27_76)) (join 77 2 2 (join 77 1 1 threshold_27_77 threshold_27_78) (join 79 1 1 threshold_27_79 threshold_27_80)))) (join 81 8 8 (join 81 4 4 (join 81 2 2 (join 81 1 1 threshold_27_81 threshold_27_82) (join 83 1 1 threshold_27_83 threshold_27_84)) (join 85 2 2 (join 85 1 1 threshold_27_85 threshold_27_86) (join 87 1 1 threshold_27_87 threshold_27_88))) (join 89 4 4 (join 89 2 2 (join 89 1 1 threshold_27_89 threshold_27_90) (join 91 1 1 threshold_27_91 threshold_27_92)) (join 93 2 2 (join 93 1 1 threshold_27_93 threshold_27_94) (join 95 1 1 threshold_27_95 threshold_27_96))))) (join 97 16 17 (join 97 8 8 (join 97 4 4 (join 97 2 2 (join 97 1 1 threshold_27_97 threshold_27_98) (join 99 1 1 threshold_27_99 threshold_27_100)) (join 101 2 2 (join 101 1 1 threshold_27_101 threshold_27_102) (join 103 1 1 threshold_27_103 threshold_27_104))) (join 105 4 4 (join 105 2 2 (join 105 1 1 threshold_27_105 threshold_27_106) (join 107 1 1 threshold_27_107 threshold_27_108)) (join 109 2 2 (join 109 1 1 threshold_27_109 threshold_27_110) (join 111 1 1 threshold_27_111 threshold_27_112)))) (join 113 8 9 (join 113 4 4 (join 113 2 2 (join 113 1 1 threshold_27_113 threshold_27_114) (join 115 1 1 threshold_27_115 threshold_27_116)) (join 117 2 2 (join 117 1 1 threshold_27_117 threshold_27_118) (join 119 1 1 threshold_27_119 threshold_27_120))) (join 121 4 5 (join 121 2 2 (join 121 1 1 threshold_27_121 threshold_27_122) (join 123 1 1 threshold_27_123 threshold_27_124)) (join 125 2 3 (join 125 1 1 threshold_27_125 threshold_27_126) (join 127 1 2 threshold_27_127 (join 128 1 1 threshold_27_128 threshold_27_129))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_27_0 : ∀ i ∈ List.range 4, LedgerAt 27 (0+i) := by decide +kernel

theorem ledger_27_4 : ∀ i ∈ List.range 4, LedgerAt 27 (4+i) := by decide +kernel

theorem ledger_27_8 : ∀ i ∈ List.range 4, LedgerAt 27 (8+i) := by decide +kernel

theorem ledger_27_12 : ∀ i ∈ List.range 4, LedgerAt 27 (12+i) := by decide +kernel

theorem ledger_27_16 : ∀ i ∈ List.range 4, LedgerAt 27 (16+i) := by decide +kernel

theorem ledger_27_20 : ∀ i ∈ List.range 4, LedgerAt 27 (20+i) := by decide +kernel

theorem ledger_27_24 : ∀ i ∈ List.range 4, LedgerAt 27 (24+i) := by decide +kernel

theorem ledger_27_28 : ∀ i ∈ List.range 4, LedgerAt 27 (28+i) := by decide +kernel

theorem ledger_27_32 : ∀ i ∈ List.range 4, LedgerAt 27 (32+i) := by decide +kernel

theorem ledger_27_36 : ∀ i ∈ List.range 4, LedgerAt 27 (36+i) := by decide +kernel

theorem ledger_27_40 : ∀ i ∈ List.range 4, LedgerAt 27 (40+i) := by decide +kernel

theorem ledger_27_44 : ∀ i ∈ List.range 4, LedgerAt 27 (44+i) := by decide +kernel

theorem ledger_27_48 : ∀ i ∈ List.range 4, LedgerAt 27 (48+i) := by decide +kernel

theorem ledger_27_52 : ∀ i ∈ List.range 4, LedgerAt 27 (52+i) := by decide +kernel

theorem ledger_27_56 : ∀ i ∈ List.range 4, LedgerAt 27 (56+i) := by decide +kernel

theorem ledger_27_60 : ∀ i ∈ List.range 4, LedgerAt 27 (60+i) := by decide +kernel

theorem ledger_27_64 : ∀ i ∈ List.range 4, LedgerAt 27 (64+i) := by decide +kernel

theorem ledger_27_68 : ∀ i ∈ List.range 4, LedgerAt 27 (68+i) := by decide +kernel

theorem ledger_27_72 : ∀ i ∈ List.range 4, LedgerAt 27 (72+i) := by decide +kernel

theorem ledger_27_76 : ∀ i ∈ List.range 4, LedgerAt 27 (76+i) := by decide +kernel

theorem ledger_27_80 : ∀ i ∈ List.range 4, LedgerAt 27 (80+i) := by decide +kernel

theorem ledger_27_84 : ∀ i ∈ List.range 4, LedgerAt 27 (84+i) := by decide +kernel

theorem ledger_27_88 : ∀ i ∈ List.range 4, LedgerAt 27 (88+i) := by decide +kernel

theorem ledger_27_92 : ∀ i ∈ List.range 4, LedgerAt 27 (92+i) := by decide +kernel

theorem ledger_27_96 : ∀ i ∈ List.range 4, LedgerAt 27 (96+i) := by decide +kernel

theorem ledger_27_100 : ∀ i ∈ List.range 4, LedgerAt 27 (100+i) := by decide +kernel

theorem ledger_27_104 : ∀ i ∈ List.range 4, LedgerAt 27 (104+i) := by decide +kernel

theorem ledger_27_108 : ∀ i ∈ List.range 4, LedgerAt 27 (108+i) := by decide +kernel

theorem ledger_27_112 : ∀ i ∈ List.range 4, LedgerAt 27 (112+i) := by decide +kernel

theorem ledger_27_116 : ∀ i ∈ List.range 4, LedgerAt 27 (116+i) := by decide +kernel

theorem ledger_27_120 : ∀ i ∈ List.range 4, LedgerAt 27 (120+i) := by decide +kernel

theorem ledger_27_124 : ∀ i ∈ List.range 4, LedgerAt 27 (124+i) := by decide +kernel

theorem ledger_27_128 : ∀ i ∈ List.range 2, LedgerAt 27 (128+i) := by decide +kernel

theorem ledger_27 (v : ℕ) (hv : v ∈ List.range 130) : LedgerAt 27 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 27 v)
  have h := (join 0 64 66 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_27_0 ledger_27_4) (join 8 4 4 ledger_27_8 ledger_27_12)) (join 16 8 8 (join 16 4 4 ledger_27_16 ledger_27_20) (join 24 4 4 ledger_27_24 ledger_27_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_27_32 ledger_27_36) (join 40 4 4 ledger_27_40 ledger_27_44)) (join 48 8 8 (join 48 4 4 ledger_27_48 ledger_27_52) (join 56 4 4 ledger_27_56 ledger_27_60)))) (join 64 32 34 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_27_64 ledger_27_68) (join 72 4 4 ledger_27_72 ledger_27_76)) (join 80 8 8 (join 80 4 4 ledger_27_80 ledger_27_84) (join 88 4 4 ledger_27_88 ledger_27_92))) (join 96 16 18 (join 96 8 8 (join 96 4 4 ledger_27_96 ledger_27_100) (join 104 4 4 ledger_27_104 ledger_27_108)) (join 112 8 10 (join 112 4 4 ledger_27_112 ledger_27_116) (join 120 4 6 ledger_27_120 (join 124 4 2 ledger_27_124 ledger_27_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
