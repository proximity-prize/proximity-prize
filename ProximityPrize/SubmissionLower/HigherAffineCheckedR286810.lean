import ProximityPrize.SubmissionLower.HigherAffineCheckedR276810
namespace ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
open HigherAffineFiniteChecks6810
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_28_0 : ∀ i ∈ List.range 4, SingleAt 28 (0+i) := by decide +kernel

theorem single_28_4 : ∀ i ∈ List.range 4, SingleAt 28 (4+i) := by decide +kernel

theorem single_28_8 : ∀ i ∈ List.range 4, SingleAt 28 (8+i) := by decide +kernel

theorem single_28_12 : ∀ i ∈ List.range 4, SingleAt 28 (12+i) := by decide +kernel

theorem single_28_16 : ∀ i ∈ List.range 4, SingleAt 28 (16+i) := by decide +kernel

theorem single_28_20 : ∀ i ∈ List.range 4, SingleAt 28 (20+i) := by decide +kernel

theorem single_28_24 : ∀ i ∈ List.range 4, SingleAt 28 (24+i) := by decide +kernel

theorem single_28_28 : ∀ i ∈ List.range 4, SingleAt 28 (28+i) := by decide +kernel

theorem single_28_32 : ∀ i ∈ List.range 4, SingleAt 28 (32+i) := by decide +kernel

theorem single_28_36 : ∀ i ∈ List.range 4, SingleAt 28 (36+i) := by decide +kernel

theorem single_28_40 : ∀ i ∈ List.range 4, SingleAt 28 (40+i) := by decide +kernel

theorem single_28_44 : ∀ i ∈ List.range 4, SingleAt 28 (44+i) := by decide +kernel

theorem single_28_48 : ∀ i ∈ List.range 4, SingleAt 28 (48+i) := by decide +kernel

theorem single_28_52 : ∀ i ∈ List.range 4, SingleAt 28 (52+i) := by decide +kernel

theorem single_28_56 : ∀ i ∈ List.range 4, SingleAt 28 (56+i) := by decide +kernel

theorem single_28_60 : ∀ i ∈ List.range 4, SingleAt 28 (60+i) := by decide +kernel

theorem single_28_64 : ∀ i ∈ List.range 4, SingleAt 28 (64+i) := by decide +kernel

theorem single_28_68 : ∀ i ∈ List.range 4, SingleAt 28 (68+i) := by decide +kernel

theorem single_28_72 : ∀ i ∈ List.range 4, SingleAt 28 (72+i) := by decide +kernel

theorem single_28_76 : ∀ i ∈ List.range 4, SingleAt 28 (76+i) := by decide +kernel

theorem single_28_80 : ∀ i ∈ List.range 4, SingleAt 28 (80+i) := by decide +kernel

theorem single_28_84 : ∀ i ∈ List.range 4, SingleAt 28 (84+i) := by decide +kernel

theorem single_28_88 : ∀ i ∈ List.range 4, SingleAt 28 (88+i) := by decide +kernel

theorem single_28_92 : ∀ i ∈ List.range 4, SingleAt 28 (92+i) := by decide +kernel

theorem single_28_96 : ∀ i ∈ List.range 4, SingleAt 28 (96+i) := by decide +kernel

theorem single_28_100 : ∀ i ∈ List.range 4, SingleAt 28 (100+i) := by decide +kernel

theorem single_28_104 : ∀ i ∈ List.range 4, SingleAt 28 (104+i) := by decide +kernel

theorem single_28_108 : ∀ i ∈ List.range 4, SingleAt 28 (108+i) := by decide +kernel

theorem single_28_112 : ∀ i ∈ List.range 4, SingleAt 28 (112+i) := by decide +kernel

theorem single_28_116 : ∀ i ∈ List.range 4, SingleAt 28 (116+i) := by decide +kernel

theorem single_28_120 : ∀ i ∈ List.range 4, SingleAt 28 (120+i) := by decide +kernel

theorem single_28_124 : ∀ i ∈ List.range 4, SingleAt 28 (124+i) := by decide +kernel

theorem single_28_128 : ∀ i ∈ List.range 1, SingleAt 28 (128+i) := by decide +kernel

theorem single_28 (v : ℕ) (hv : v ∈ List.range 129) : SingleAt 28 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => SingleAt 28 v)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_28_0 single_28_4) (join 8 4 4 single_28_8 single_28_12)) (join 16 8 8 (join 16 4 4 single_28_16 single_28_20) (join 24 4 4 single_28_24 single_28_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_28_32 single_28_36) (join 40 4 4 single_28_40 single_28_44)) (join 48 8 8 (join 48 4 4 single_28_48 single_28_52) (join 56 4 4 single_28_56 single_28_60)))) (join 64 32 33 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_28_64 single_28_68) (join 72 4 4 single_28_72 single_28_76)) (join 80 8 8 (join 80 4 4 single_28_80 single_28_84) (join 88 4 4 single_28_88 single_28_92))) (join 96 16 17 (join 96 8 8 (join 96 4 4 single_28_96 single_28_100) (join 104 4 4 single_28_104 single_28_108)) (join 112 8 9 (join 112 4 4 single_28_112 single_28_116) (join 120 4 5 single_28_120 (join 124 4 1 single_28_124 single_28_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_28_0 : ∀ i ∈ List.range 4, PhaseAt 28 (0+i) := by decide +kernel

theorem phase_28_4 : ∀ i ∈ List.range 4, PhaseAt 28 (4+i) := by decide +kernel

theorem phase_28_8 : ∀ i ∈ List.range 4, PhaseAt 28 (8+i) := by decide +kernel

theorem phase_28_12 : ∀ i ∈ List.range 4, PhaseAt 28 (12+i) := by decide +kernel

theorem phase_28_16 : ∀ i ∈ List.range 4, PhaseAt 28 (16+i) := by decide +kernel

theorem phase_28_20 : ∀ i ∈ List.range 4, PhaseAt 28 (20+i) := by decide +kernel

theorem phase_28_24 : ∀ i ∈ List.range 4, PhaseAt 28 (24+i) := by decide +kernel

theorem phase_28_28 : ∀ i ∈ List.range 4, PhaseAt 28 (28+i) := by decide +kernel

theorem phase_28_32 : ∀ i ∈ List.range 4, PhaseAt 28 (32+i) := by decide +kernel

theorem phase_28_36 : ∀ i ∈ List.range 4, PhaseAt 28 (36+i) := by decide +kernel

theorem phase_28_40 : ∀ i ∈ List.range 4, PhaseAt 28 (40+i) := by decide +kernel

theorem phase_28_44 : ∀ i ∈ List.range 4, PhaseAt 28 (44+i) := by decide +kernel

theorem phase_28_48 : ∀ i ∈ List.range 4, PhaseAt 28 (48+i) := by decide +kernel

theorem phase_28_52 : ∀ i ∈ List.range 4, PhaseAt 28 (52+i) := by decide +kernel

theorem phase_28_56 : ∀ i ∈ List.range 4, PhaseAt 28 (56+i) := by decide +kernel

theorem phase_28_60 : ∀ i ∈ List.range 4, PhaseAt 28 (60+i) := by decide +kernel

theorem phase_28_64 : ∀ i ∈ List.range 4, PhaseAt 28 (64+i) := by decide +kernel

theorem phase_28_68 : ∀ i ∈ List.range 4, PhaseAt 28 (68+i) := by decide +kernel

theorem phase_28_72 : ∀ i ∈ List.range 4, PhaseAt 28 (72+i) := by decide +kernel

theorem phase_28_76 : ∀ i ∈ List.range 4, PhaseAt 28 (76+i) := by decide +kernel

theorem phase_28_80 : ∀ i ∈ List.range 4, PhaseAt 28 (80+i) := by decide +kernel

theorem phase_28_84 : ∀ i ∈ List.range 4, PhaseAt 28 (84+i) := by decide +kernel

theorem phase_28_88 : ∀ i ∈ List.range 4, PhaseAt 28 (88+i) := by decide +kernel

theorem phase_28_92 : ∀ i ∈ List.range 4, PhaseAt 28 (92+i) := by decide +kernel

theorem phase_28_96 : ∀ i ∈ List.range 4, PhaseAt 28 (96+i) := by decide +kernel

theorem phase_28_100 : ∀ i ∈ List.range 4, PhaseAt 28 (100+i) := by decide +kernel

theorem phase_28_104 : ∀ i ∈ List.range 4, PhaseAt 28 (104+i) := by decide +kernel

theorem phase_28_108 : ∀ i ∈ List.range 4, PhaseAt 28 (108+i) := by decide +kernel

theorem phase_28_112 : ∀ i ∈ List.range 4, PhaseAt 28 (112+i) := by decide +kernel

theorem phase_28_116 : ∀ i ∈ List.range 4, PhaseAt 28 (116+i) := by decide +kernel

theorem phase_28_120 : ∀ i ∈ List.range 4, PhaseAt 28 (120+i) := by decide +kernel

theorem phase_28_124 : ∀ i ∈ List.range 4, PhaseAt 28 (124+i) := by decide +kernel

theorem phase_28_128 : ∀ i ∈ List.range 1, PhaseAt 28 (128+i) := by decide +kernel

theorem phase_28 (v : ℕ) (hv : v ∈ List.range 129) : PhaseAt 28 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => PhaseAt 28 v)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_28_0 phase_28_4) (join 8 4 4 phase_28_8 phase_28_12)) (join 16 8 8 (join 16 4 4 phase_28_16 phase_28_20) (join 24 4 4 phase_28_24 phase_28_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_28_32 phase_28_36) (join 40 4 4 phase_28_40 phase_28_44)) (join 48 8 8 (join 48 4 4 phase_28_48 phase_28_52) (join 56 4 4 phase_28_56 phase_28_60)))) (join 64 32 33 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_28_64 phase_28_68) (join 72 4 4 phase_28_72 phase_28_76)) (join 80 8 8 (join 80 4 4 phase_28_80 phase_28_84) (join 88 4 4 phase_28_88 phase_28_92))) (join 96 16 17 (join 96 8 8 (join 96 4 4 phase_28_96 phase_28_100) (join 104 4 4 phase_28_104 phase_28_108)) (join 112 8 9 (join 112 4 4 phase_28_112 phase_28_116) (join 120 4 5 phase_28_120 (join 124 4 1 phase_28_124 phase_28_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_28_0 : ∀ i ∈ List.range 1, ThresholdAt 28 (0+i) := by decide +kernel

theorem threshold_28_1 : ∀ i ∈ List.range 1, ThresholdAt 28 (1+i) := by decide +kernel

theorem threshold_28_2 : ∀ i ∈ List.range 1, ThresholdAt 28 (2+i) := by decide +kernel

theorem threshold_28_3 : ∀ i ∈ List.range 1, ThresholdAt 28 (3+i) := by decide +kernel

theorem threshold_28_4 : ∀ i ∈ List.range 1, ThresholdAt 28 (4+i) := by decide +kernel

theorem threshold_28_5 : ∀ i ∈ List.range 1, ThresholdAt 28 (5+i) := by decide +kernel

theorem threshold_28_6 : ∀ i ∈ List.range 1, ThresholdAt 28 (6+i) := by decide +kernel

theorem threshold_28_7 : ∀ i ∈ List.range 1, ThresholdAt 28 (7+i) := by decide +kernel

theorem threshold_28_8 : ∀ i ∈ List.range 1, ThresholdAt 28 (8+i) := by decide +kernel

theorem threshold_28_9 : ∀ i ∈ List.range 1, ThresholdAt 28 (9+i) := by decide +kernel

theorem threshold_28_10 : ∀ i ∈ List.range 1, ThresholdAt 28 (10+i) := by decide +kernel

theorem threshold_28_11 : ∀ i ∈ List.range 1, ThresholdAt 28 (11+i) := by decide +kernel

theorem threshold_28_12 : ∀ i ∈ List.range 1, ThresholdAt 28 (12+i) := by decide +kernel

theorem threshold_28_13 : ∀ i ∈ List.range 1, ThresholdAt 28 (13+i) := by decide +kernel

theorem threshold_28_14 : ∀ i ∈ List.range 1, ThresholdAt 28 (14+i) := by decide +kernel

theorem threshold_28_15 : ∀ i ∈ List.range 1, ThresholdAt 28 (15+i) := by decide +kernel

theorem threshold_28_16 : ∀ i ∈ List.range 1, ThresholdAt 28 (16+i) := by decide +kernel

theorem threshold_28_17 : ∀ i ∈ List.range 1, ThresholdAt 28 (17+i) := by decide +kernel

theorem threshold_28_18 : ∀ i ∈ List.range 1, ThresholdAt 28 (18+i) := by decide +kernel

theorem threshold_28_19 : ∀ i ∈ List.range 1, ThresholdAt 28 (19+i) := by decide +kernel

theorem threshold_28_20 : ∀ i ∈ List.range 1, ThresholdAt 28 (20+i) := by decide +kernel

theorem threshold_28_21 : ∀ i ∈ List.range 1, ThresholdAt 28 (21+i) := by decide +kernel

theorem threshold_28_22 : ∀ i ∈ List.range 1, ThresholdAt 28 (22+i) := by decide +kernel

theorem threshold_28_23 : ∀ i ∈ List.range 1, ThresholdAt 28 (23+i) := by decide +kernel

theorem threshold_28_24 : ∀ i ∈ List.range 1, ThresholdAt 28 (24+i) := by decide +kernel

theorem threshold_28_25 : ∀ i ∈ List.range 1, ThresholdAt 28 (25+i) := by decide +kernel

theorem threshold_28_26 : ∀ i ∈ List.range 1, ThresholdAt 28 (26+i) := by decide +kernel

theorem threshold_28_27 : ∀ i ∈ List.range 1, ThresholdAt 28 (27+i) := by decide +kernel

theorem threshold_28_28 : ∀ i ∈ List.range 1, ThresholdAt 28 (28+i) := by decide +kernel

theorem threshold_28_29 : ∀ i ∈ List.range 1, ThresholdAt 28 (29+i) := by decide +kernel

theorem threshold_28_30 : ∀ i ∈ List.range 1, ThresholdAt 28 (30+i) := by decide +kernel

theorem threshold_28_31 : ∀ i ∈ List.range 1, ThresholdAt 28 (31+i) := by decide +kernel

theorem threshold_28_32 : ∀ i ∈ List.range 1, ThresholdAt 28 (32+i) := by decide +kernel

theorem threshold_28_33 : ∀ i ∈ List.range 1, ThresholdAt 28 (33+i) := by decide +kernel

theorem threshold_28_34 : ∀ i ∈ List.range 1, ThresholdAt 28 (34+i) := by decide +kernel

theorem threshold_28_35 : ∀ i ∈ List.range 1, ThresholdAt 28 (35+i) := by decide +kernel

theorem threshold_28_36 : ∀ i ∈ List.range 1, ThresholdAt 28 (36+i) := by decide +kernel

theorem threshold_28_37 : ∀ i ∈ List.range 1, ThresholdAt 28 (37+i) := by decide +kernel

theorem threshold_28_38 : ∀ i ∈ List.range 1, ThresholdAt 28 (38+i) := by decide +kernel

theorem threshold_28_39 : ∀ i ∈ List.range 1, ThresholdAt 28 (39+i) := by decide +kernel

theorem threshold_28_40 : ∀ i ∈ List.range 1, ThresholdAt 28 (40+i) := by decide +kernel

theorem threshold_28_41 : ∀ i ∈ List.range 1, ThresholdAt 28 (41+i) := by decide +kernel

theorem threshold_28_42 : ∀ i ∈ List.range 1, ThresholdAt 28 (42+i) := by decide +kernel

theorem threshold_28_43 : ∀ i ∈ List.range 1, ThresholdAt 28 (43+i) := by decide +kernel

theorem threshold_28_44 : ∀ i ∈ List.range 1, ThresholdAt 28 (44+i) := by decide +kernel

theorem threshold_28_45 : ∀ i ∈ List.range 1, ThresholdAt 28 (45+i) := by decide +kernel

theorem threshold_28_46 : ∀ i ∈ List.range 1, ThresholdAt 28 (46+i) := by decide +kernel

theorem threshold_28_47 : ∀ i ∈ List.range 1, ThresholdAt 28 (47+i) := by decide +kernel

theorem threshold_28_48 : ∀ i ∈ List.range 1, ThresholdAt 28 (48+i) := by decide +kernel

theorem threshold_28_49 : ∀ i ∈ List.range 1, ThresholdAt 28 (49+i) := by decide +kernel

theorem threshold_28_50 : ∀ i ∈ List.range 1, ThresholdAt 28 (50+i) := by decide +kernel

theorem threshold_28_51 : ∀ i ∈ List.range 1, ThresholdAt 28 (51+i) := by decide +kernel

theorem threshold_28_52 : ∀ i ∈ List.range 1, ThresholdAt 28 (52+i) := by decide +kernel

theorem threshold_28_53 : ∀ i ∈ List.range 1, ThresholdAt 28 (53+i) := by decide +kernel

theorem threshold_28_54 : ∀ i ∈ List.range 1, ThresholdAt 28 (54+i) := by decide +kernel

theorem threshold_28_55 : ∀ i ∈ List.range 1, ThresholdAt 28 (55+i) := by decide +kernel

theorem threshold_28_56 : ∀ i ∈ List.range 1, ThresholdAt 28 (56+i) := by decide +kernel

theorem threshold_28_57 : ∀ i ∈ List.range 1, ThresholdAt 28 (57+i) := by decide +kernel

theorem threshold_28_58 : ∀ i ∈ List.range 1, ThresholdAt 28 (58+i) := by decide +kernel

theorem threshold_28_59 : ∀ i ∈ List.range 1, ThresholdAt 28 (59+i) := by decide +kernel

theorem threshold_28_60 : ∀ i ∈ List.range 1, ThresholdAt 28 (60+i) := by decide +kernel

theorem threshold_28_61 : ∀ i ∈ List.range 1, ThresholdAt 28 (61+i) := by decide +kernel

theorem threshold_28_62 : ∀ i ∈ List.range 1, ThresholdAt 28 (62+i) := by decide +kernel

theorem threshold_28_63 : ∀ i ∈ List.range 1, ThresholdAt 28 (63+i) := by decide +kernel

theorem threshold_28_64 : ∀ i ∈ List.range 1, ThresholdAt 28 (64+i) := by decide +kernel

theorem threshold_28_65 : ∀ i ∈ List.range 1, ThresholdAt 28 (65+i) := by decide +kernel

theorem threshold_28_66 : ∀ i ∈ List.range 1, ThresholdAt 28 (66+i) := by decide +kernel

theorem threshold_28_67 : ∀ i ∈ List.range 1, ThresholdAt 28 (67+i) := by decide +kernel

theorem threshold_28_68 : ∀ i ∈ List.range 1, ThresholdAt 28 (68+i) := by decide +kernel

theorem threshold_28_69 : ∀ i ∈ List.range 1, ThresholdAt 28 (69+i) := by decide +kernel

theorem threshold_28_70 : ∀ i ∈ List.range 1, ThresholdAt 28 (70+i) := by decide +kernel

theorem threshold_28_71 : ∀ i ∈ List.range 1, ThresholdAt 28 (71+i) := by decide +kernel

theorem threshold_28_72 : ∀ i ∈ List.range 1, ThresholdAt 28 (72+i) := by decide +kernel

theorem threshold_28_73 : ∀ i ∈ List.range 1, ThresholdAt 28 (73+i) := by decide +kernel

theorem threshold_28_74 : ∀ i ∈ List.range 1, ThresholdAt 28 (74+i) := by decide +kernel

theorem threshold_28_75 : ∀ i ∈ List.range 1, ThresholdAt 28 (75+i) := by decide +kernel

theorem threshold_28_76 : ∀ i ∈ List.range 1, ThresholdAt 28 (76+i) := by decide +kernel

theorem threshold_28_77 : ∀ i ∈ List.range 1, ThresholdAt 28 (77+i) := by decide +kernel

theorem threshold_28_78 : ∀ i ∈ List.range 1, ThresholdAt 28 (78+i) := by decide +kernel

theorem threshold_28_79 : ∀ i ∈ List.range 1, ThresholdAt 28 (79+i) := by decide +kernel

theorem threshold_28_80 : ∀ i ∈ List.range 1, ThresholdAt 28 (80+i) := by decide +kernel

theorem threshold_28_81 : ∀ i ∈ List.range 1, ThresholdAt 28 (81+i) := by decide +kernel

theorem threshold_28_82 : ∀ i ∈ List.range 1, ThresholdAt 28 (82+i) := by decide +kernel

theorem threshold_28_83 : ∀ i ∈ List.range 1, ThresholdAt 28 (83+i) := by decide +kernel

theorem threshold_28_84 : ∀ i ∈ List.range 1, ThresholdAt 28 (84+i) := by decide +kernel

theorem threshold_28_85 : ∀ i ∈ List.range 1, ThresholdAt 28 (85+i) := by decide +kernel

theorem threshold_28_86 : ∀ i ∈ List.range 1, ThresholdAt 28 (86+i) := by decide +kernel

theorem threshold_28_87 : ∀ i ∈ List.range 1, ThresholdAt 28 (87+i) := by decide +kernel

theorem threshold_28_88 : ∀ i ∈ List.range 1, ThresholdAt 28 (88+i) := by decide +kernel

theorem threshold_28_89 : ∀ i ∈ List.range 1, ThresholdAt 28 (89+i) := by decide +kernel

theorem threshold_28_90 : ∀ i ∈ List.range 1, ThresholdAt 28 (90+i) := by decide +kernel

theorem threshold_28_91 : ∀ i ∈ List.range 1, ThresholdAt 28 (91+i) := by decide +kernel

theorem threshold_28_92 : ∀ i ∈ List.range 1, ThresholdAt 28 (92+i) := by decide +kernel

theorem threshold_28_93 : ∀ i ∈ List.range 1, ThresholdAt 28 (93+i) := by decide +kernel

theorem threshold_28_94 : ∀ i ∈ List.range 1, ThresholdAt 28 (94+i) := by decide +kernel

theorem threshold_28_95 : ∀ i ∈ List.range 1, ThresholdAt 28 (95+i) := by decide +kernel

theorem threshold_28_96 : ∀ i ∈ List.range 1, ThresholdAt 28 (96+i) := by decide +kernel

theorem threshold_28_97 : ∀ i ∈ List.range 1, ThresholdAt 28 (97+i) := by decide +kernel

theorem threshold_28_98 : ∀ i ∈ List.range 1, ThresholdAt 28 (98+i) := by decide +kernel

theorem threshold_28_99 : ∀ i ∈ List.range 1, ThresholdAt 28 (99+i) := by decide +kernel

theorem threshold_28_100 : ∀ i ∈ List.range 1, ThresholdAt 28 (100+i) := by decide +kernel

theorem threshold_28_101 : ∀ i ∈ List.range 1, ThresholdAt 28 (101+i) := by decide +kernel

theorem threshold_28_102 : ∀ i ∈ List.range 1, ThresholdAt 28 (102+i) := by decide +kernel

theorem threshold_28_103 : ∀ i ∈ List.range 1, ThresholdAt 28 (103+i) := by decide +kernel

theorem threshold_28_104 : ∀ i ∈ List.range 1, ThresholdAt 28 (104+i) := by decide +kernel

theorem threshold_28_105 : ∀ i ∈ List.range 1, ThresholdAt 28 (105+i) := by decide +kernel

theorem threshold_28_106 : ∀ i ∈ List.range 1, ThresholdAt 28 (106+i) := by decide +kernel

theorem threshold_28_107 : ∀ i ∈ List.range 1, ThresholdAt 28 (107+i) := by decide +kernel

theorem threshold_28_108 : ∀ i ∈ List.range 1, ThresholdAt 28 (108+i) := by decide +kernel

theorem threshold_28_109 : ∀ i ∈ List.range 1, ThresholdAt 28 (109+i) := by decide +kernel

theorem threshold_28_110 : ∀ i ∈ List.range 1, ThresholdAt 28 (110+i) := by decide +kernel

theorem threshold_28_111 : ∀ i ∈ List.range 1, ThresholdAt 28 (111+i) := by decide +kernel

theorem threshold_28_112 : ∀ i ∈ List.range 1, ThresholdAt 28 (112+i) := by decide +kernel

theorem threshold_28_113 : ∀ i ∈ List.range 1, ThresholdAt 28 (113+i) := by decide +kernel

theorem threshold_28_114 : ∀ i ∈ List.range 1, ThresholdAt 28 (114+i) := by decide +kernel

theorem threshold_28_115 : ∀ i ∈ List.range 1, ThresholdAt 28 (115+i) := by decide +kernel

theorem threshold_28_116 : ∀ i ∈ List.range 1, ThresholdAt 28 (116+i) := by decide +kernel

theorem threshold_28_117 : ∀ i ∈ List.range 1, ThresholdAt 28 (117+i) := by decide +kernel

theorem threshold_28_118 : ∀ i ∈ List.range 1, ThresholdAt 28 (118+i) := by decide +kernel

theorem threshold_28_119 : ∀ i ∈ List.range 1, ThresholdAt 28 (119+i) := by decide +kernel

theorem threshold_28_120 : ∀ i ∈ List.range 1, ThresholdAt 28 (120+i) := by decide +kernel

theorem threshold_28_121 : ∀ i ∈ List.range 1, ThresholdAt 28 (121+i) := by decide +kernel

theorem threshold_28_122 : ∀ i ∈ List.range 1, ThresholdAt 28 (122+i) := by decide +kernel

theorem threshold_28_123 : ∀ i ∈ List.range 1, ThresholdAt 28 (123+i) := by decide +kernel

theorem threshold_28_124 : ∀ i ∈ List.range 1, ThresholdAt 28 (124+i) := by decide +kernel

theorem threshold_28_125 : ∀ i ∈ List.range 1, ThresholdAt 28 (125+i) := by decide +kernel

theorem threshold_28_126 : ∀ i ∈ List.range 1, ThresholdAt 28 (126+i) := by decide +kernel

theorem threshold_28_127 : ∀ i ∈ List.range 1, ThresholdAt 28 (127+i) := by decide +kernel

theorem threshold_28_128 : ∀ i ∈ List.range 1, ThresholdAt 28 (128+i) := by decide +kernel

theorem threshold_28 (v : ℕ) (hv : v ∈ List.range 129) : ThresholdAt 28 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => ThresholdAt 28 v)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_28_0 threshold_28_1) (join 2 1 1 threshold_28_2 threshold_28_3)) (join 4 2 2 (join 4 1 1 threshold_28_4 threshold_28_5) (join 6 1 1 threshold_28_6 threshold_28_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_28_8 threshold_28_9) (join 10 1 1 threshold_28_10 threshold_28_11)) (join 12 2 2 (join 12 1 1 threshold_28_12 threshold_28_13) (join 14 1 1 threshold_28_14 threshold_28_15)))) (join 16 8 8 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_28_16 threshold_28_17) (join 18 1 1 threshold_28_18 threshold_28_19)) (join 20 2 2 (join 20 1 1 threshold_28_20 threshold_28_21) (join 22 1 1 threshold_28_22 threshold_28_23))) (join 24 4 4 (join 24 2 2 (join 24 1 1 threshold_28_24 threshold_28_25) (join 26 1 1 threshold_28_26 threshold_28_27)) (join 28 2 2 (join 28 1 1 threshold_28_28 threshold_28_29) (join 30 1 1 threshold_28_30 threshold_28_31))))) (join 32 16 16 (join 32 8 8 (join 32 4 4 (join 32 2 2 (join 32 1 1 threshold_28_32 threshold_28_33) (join 34 1 1 threshold_28_34 threshold_28_35)) (join 36 2 2 (join 36 1 1 threshold_28_36 threshold_28_37) (join 38 1 1 threshold_28_38 threshold_28_39))) (join 40 4 4 (join 40 2 2 (join 40 1 1 threshold_28_40 threshold_28_41) (join 42 1 1 threshold_28_42 threshold_28_43)) (join 44 2 2 (join 44 1 1 threshold_28_44 threshold_28_45) (join 46 1 1 threshold_28_46 threshold_28_47)))) (join 48 8 8 (join 48 4 4 (join 48 2 2 (join 48 1 1 threshold_28_48 threshold_28_49) (join 50 1 1 threshold_28_50 threshold_28_51)) (join 52 2 2 (join 52 1 1 threshold_28_52 threshold_28_53) (join 54 1 1 threshold_28_54 threshold_28_55))) (join 56 4 4 (join 56 2 2 (join 56 1 1 threshold_28_56 threshold_28_57) (join 58 1 1 threshold_28_58 threshold_28_59)) (join 60 2 2 (join 60 1 1 threshold_28_60 threshold_28_61) (join 62 1 1 threshold_28_62 threshold_28_63)))))) (join 64 32 33 (join 64 16 16 (join 64 8 8 (join 64 4 4 (join 64 2 2 (join 64 1 1 threshold_28_64 threshold_28_65) (join 66 1 1 threshold_28_66 threshold_28_67)) (join 68 2 2 (join 68 1 1 threshold_28_68 threshold_28_69) (join 70 1 1 threshold_28_70 threshold_28_71))) (join 72 4 4 (join 72 2 2 (join 72 1 1 threshold_28_72 threshold_28_73) (join 74 1 1 threshold_28_74 threshold_28_75)) (join 76 2 2 (join 76 1 1 threshold_28_76 threshold_28_77) (join 78 1 1 threshold_28_78 threshold_28_79)))) (join 80 8 8 (join 80 4 4 (join 80 2 2 (join 80 1 1 threshold_28_80 threshold_28_81) (join 82 1 1 threshold_28_82 threshold_28_83)) (join 84 2 2 (join 84 1 1 threshold_28_84 threshold_28_85) (join 86 1 1 threshold_28_86 threshold_28_87))) (join 88 4 4 (join 88 2 2 (join 88 1 1 threshold_28_88 threshold_28_89) (join 90 1 1 threshold_28_90 threshold_28_91)) (join 92 2 2 (join 92 1 1 threshold_28_92 threshold_28_93) (join 94 1 1 threshold_28_94 threshold_28_95))))) (join 96 16 17 (join 96 8 8 (join 96 4 4 (join 96 2 2 (join 96 1 1 threshold_28_96 threshold_28_97) (join 98 1 1 threshold_28_98 threshold_28_99)) (join 100 2 2 (join 100 1 1 threshold_28_100 threshold_28_101) (join 102 1 1 threshold_28_102 threshold_28_103))) (join 104 4 4 (join 104 2 2 (join 104 1 1 threshold_28_104 threshold_28_105) (join 106 1 1 threshold_28_106 threshold_28_107)) (join 108 2 2 (join 108 1 1 threshold_28_108 threshold_28_109) (join 110 1 1 threshold_28_110 threshold_28_111)))) (join 112 8 9 (join 112 4 4 (join 112 2 2 (join 112 1 1 threshold_28_112 threshold_28_113) (join 114 1 1 threshold_28_114 threshold_28_115)) (join 116 2 2 (join 116 1 1 threshold_28_116 threshold_28_117) (join 118 1 1 threshold_28_118 threshold_28_119))) (join 120 4 5 (join 120 2 2 (join 120 1 1 threshold_28_120 threshold_28_121) (join 122 1 1 threshold_28_122 threshold_28_123)) (join 124 2 3 (join 124 1 1 threshold_28_124 threshold_28_125) (join 126 1 2 threshold_28_126 (join 127 1 1 threshold_28_127 threshold_28_128))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_28_0 : ∀ i ∈ List.range 4, LedgerAt 28 (0+i) := by decide +kernel

theorem ledger_28_4 : ∀ i ∈ List.range 4, LedgerAt 28 (4+i) := by decide +kernel

theorem ledger_28_8 : ∀ i ∈ List.range 4, LedgerAt 28 (8+i) := by decide +kernel

theorem ledger_28_12 : ∀ i ∈ List.range 4, LedgerAt 28 (12+i) := by decide +kernel

theorem ledger_28_16 : ∀ i ∈ List.range 4, LedgerAt 28 (16+i) := by decide +kernel

theorem ledger_28_20 : ∀ i ∈ List.range 4, LedgerAt 28 (20+i) := by decide +kernel

theorem ledger_28_24 : ∀ i ∈ List.range 4, LedgerAt 28 (24+i) := by decide +kernel

theorem ledger_28_28 : ∀ i ∈ List.range 4, LedgerAt 28 (28+i) := by decide +kernel

theorem ledger_28_32 : ∀ i ∈ List.range 4, LedgerAt 28 (32+i) := by decide +kernel

theorem ledger_28_36 : ∀ i ∈ List.range 4, LedgerAt 28 (36+i) := by decide +kernel

theorem ledger_28_40 : ∀ i ∈ List.range 4, LedgerAt 28 (40+i) := by decide +kernel

theorem ledger_28_44 : ∀ i ∈ List.range 4, LedgerAt 28 (44+i) := by decide +kernel

theorem ledger_28_48 : ∀ i ∈ List.range 4, LedgerAt 28 (48+i) := by decide +kernel

theorem ledger_28_52 : ∀ i ∈ List.range 4, LedgerAt 28 (52+i) := by decide +kernel

theorem ledger_28_56 : ∀ i ∈ List.range 4, LedgerAt 28 (56+i) := by decide +kernel

theorem ledger_28_60 : ∀ i ∈ List.range 4, LedgerAt 28 (60+i) := by decide +kernel

theorem ledger_28_64 : ∀ i ∈ List.range 4, LedgerAt 28 (64+i) := by decide +kernel

theorem ledger_28_68 : ∀ i ∈ List.range 4, LedgerAt 28 (68+i) := by decide +kernel

theorem ledger_28_72 : ∀ i ∈ List.range 4, LedgerAt 28 (72+i) := by decide +kernel

theorem ledger_28_76 : ∀ i ∈ List.range 4, LedgerAt 28 (76+i) := by decide +kernel

theorem ledger_28_80 : ∀ i ∈ List.range 4, LedgerAt 28 (80+i) := by decide +kernel

theorem ledger_28_84 : ∀ i ∈ List.range 4, LedgerAt 28 (84+i) := by decide +kernel

theorem ledger_28_88 : ∀ i ∈ List.range 4, LedgerAt 28 (88+i) := by decide +kernel

theorem ledger_28_92 : ∀ i ∈ List.range 4, LedgerAt 28 (92+i) := by decide +kernel

theorem ledger_28_96 : ∀ i ∈ List.range 4, LedgerAt 28 (96+i) := by decide +kernel

theorem ledger_28_100 : ∀ i ∈ List.range 4, LedgerAt 28 (100+i) := by decide +kernel

theorem ledger_28_104 : ∀ i ∈ List.range 4, LedgerAt 28 (104+i) := by decide +kernel

theorem ledger_28_108 : ∀ i ∈ List.range 4, LedgerAt 28 (108+i) := by decide +kernel

theorem ledger_28_112 : ∀ i ∈ List.range 4, LedgerAt 28 (112+i) := by decide +kernel

theorem ledger_28_116 : ∀ i ∈ List.range 4, LedgerAt 28 (116+i) := by decide +kernel

theorem ledger_28_120 : ∀ i ∈ List.range 4, LedgerAt 28 (120+i) := by decide +kernel

theorem ledger_28_124 : ∀ i ∈ List.range 4, LedgerAt 28 (124+i) := by decide +kernel

theorem ledger_28_128 : ∀ i ∈ List.range 1, LedgerAt 28 (128+i) := by decide +kernel

theorem ledger_28 (v : ℕ) (hv : v ∈ List.range 129) : LedgerAt 28 v := by
  let join := @HigherAffineFiniteChecks6810.range_join (fun v => LedgerAt 28 v)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_28_0 ledger_28_4) (join 8 4 4 ledger_28_8 ledger_28_12)) (join 16 8 8 (join 16 4 4 ledger_28_16 ledger_28_20) (join 24 4 4 ledger_28_24 ledger_28_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_28_32 ledger_28_36) (join 40 4 4 ledger_28_40 ledger_28_44)) (join 48 8 8 (join 48 4 4 ledger_28_48 ledger_28_52) (join 56 4 4 ledger_28_56 ledger_28_60)))) (join 64 32 33 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_28_64 ledger_28_68) (join 72 4 4 ledger_28_72 ledger_28_76)) (join 80 8 8 (join 80 4 4 ledger_28_80 ledger_28_84) (join 88 4 4 ledger_28_88 ledger_28_92))) (join 96 16 17 (join 96 8 8 (join 96 4 4 ledger_28_96 ledger_28_100) (join 104 4 4 ledger_28_104 ledger_28_108)) (join 112 8 9 (join 112 4 4 ledger_28_112 ledger_28_116) (join 120 4 5 ledger_28_120 (join 124 4 1 ledger_28_124 ledger_28_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.HigherAffineRowsChecked6810
