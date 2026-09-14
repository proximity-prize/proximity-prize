import ProximityPrize.SubmissionLower.AffineFiniteChecks6808
namespace ProximityPrize.SubmissionLower.AffineRowsChecked6808
open AffineFiniteChecks6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem single_24_0 : ∀ i ∈ List.range 4, SingleAt 24 (0+i) := by decide +kernel

theorem single_24_4 : ∀ i ∈ List.range 4, SingleAt 24 (4+i) := by decide +kernel

theorem single_24_8 : ∀ i ∈ List.range 4, SingleAt 24 (8+i) := by decide +kernel

theorem single_24_12 : ∀ i ∈ List.range 4, SingleAt 24 (12+i) := by decide +kernel

theorem single_24_16 : ∀ i ∈ List.range 4, SingleAt 24 (16+i) := by decide +kernel

theorem single_24_20 : ∀ i ∈ List.range 4, SingleAt 24 (20+i) := by decide +kernel

theorem single_24_24 : ∀ i ∈ List.range 4, SingleAt 24 (24+i) := by decide +kernel

theorem single_24_28 : ∀ i ∈ List.range 4, SingleAt 24 (28+i) := by decide +kernel

theorem single_24_32 : ∀ i ∈ List.range 4, SingleAt 24 (32+i) := by decide +kernel

theorem single_24_36 : ∀ i ∈ List.range 4, SingleAt 24 (36+i) := by decide +kernel

theorem single_24_40 : ∀ i ∈ List.range 4, SingleAt 24 (40+i) := by decide +kernel

theorem single_24_44 : ∀ i ∈ List.range 4, SingleAt 24 (44+i) := by decide +kernel

theorem single_24_48 : ∀ i ∈ List.range 4, SingleAt 24 (48+i) := by decide +kernel

theorem single_24_52 : ∀ i ∈ List.range 4, SingleAt 24 (52+i) := by decide +kernel

theorem single_24_56 : ∀ i ∈ List.range 4, SingleAt 24 (56+i) := by decide +kernel

theorem single_24_60 : ∀ i ∈ List.range 4, SingleAt 24 (60+i) := by decide +kernel

theorem single_24_64 : ∀ i ∈ List.range 4, SingleAt 24 (64+i) := by decide +kernel

theorem single_24_68 : ∀ i ∈ List.range 4, SingleAt 24 (68+i) := by decide +kernel

theorem single_24_72 : ∀ i ∈ List.range 4, SingleAt 24 (72+i) := by decide +kernel

theorem single_24_76 : ∀ i ∈ List.range 4, SingleAt 24 (76+i) := by decide +kernel

theorem single_24_80 : ∀ i ∈ List.range 4, SingleAt 24 (80+i) := by decide +kernel

theorem single_24_84 : ∀ i ∈ List.range 4, SingleAt 24 (84+i) := by decide +kernel

theorem single_24_88 : ∀ i ∈ List.range 4, SingleAt 24 (88+i) := by decide +kernel

theorem single_24_92 : ∀ i ∈ List.range 4, SingleAt 24 (92+i) := by decide +kernel

theorem single_24_96 : ∀ i ∈ List.range 4, SingleAt 24 (96+i) := by decide +kernel

theorem single_24_100 : ∀ i ∈ List.range 4, SingleAt 24 (100+i) := by decide +kernel

theorem single_24_104 : ∀ i ∈ List.range 4, SingleAt 24 (104+i) := by decide +kernel

theorem single_24_108 : ∀ i ∈ List.range 4, SingleAt 24 (108+i) := by decide +kernel

theorem single_24_112 : ∀ i ∈ List.range 4, SingleAt 24 (112+i) := by decide +kernel

theorem single_24_116 : ∀ i ∈ List.range 4, SingleAt 24 (116+i) := by decide +kernel

theorem single_24_120 : ∀ i ∈ List.range 4, SingleAt 24 (120+i) := by decide +kernel

theorem single_24_124 : ∀ i ∈ List.range 2, SingleAt 24 (124+i) := by decide +kernel

theorem single_24 (v : ℕ) (hv : v ∈ List.range 126) : SingleAt 24 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => SingleAt 24 v)
  have h := (join 0 64 62 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 single_24_0 single_24_4) (join 8 4 4 single_24_8 single_24_12)) (join 16 8 8 (join 16 4 4 single_24_16 single_24_20) (join 24 4 4 single_24_24 single_24_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 single_24_32 single_24_36) (join 40 4 4 single_24_40 single_24_44)) (join 48 8 8 (join 48 4 4 single_24_48 single_24_52) (join 56 4 4 single_24_56 single_24_60)))) (join 64 32 30 (join 64 16 16 (join 64 8 8 (join 64 4 4 single_24_64 single_24_68) (join 72 4 4 single_24_72 single_24_76)) (join 80 8 8 (join 80 4 4 single_24_80 single_24_84) (join 88 4 4 single_24_88 single_24_92))) (join 96 16 14 (join 96 8 8 (join 96 4 4 single_24_96 single_24_100) (join 104 4 4 single_24_104 single_24_108)) (join 112 8 6 (join 112 4 4 single_24_112 single_24_116) (join 120 4 2 single_24_120 single_24_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_24_0 : ∀ i ∈ List.range 4, PhaseAt 24 (0+i) := by decide +kernel

theorem phase_24_4 : ∀ i ∈ List.range 4, PhaseAt 24 (4+i) := by decide +kernel

theorem phase_24_8 : ∀ i ∈ List.range 4, PhaseAt 24 (8+i) := by decide +kernel

theorem phase_24_12 : ∀ i ∈ List.range 4, PhaseAt 24 (12+i) := by decide +kernel

theorem phase_24_16 : ∀ i ∈ List.range 4, PhaseAt 24 (16+i) := by decide +kernel

theorem phase_24_20 : ∀ i ∈ List.range 4, PhaseAt 24 (20+i) := by decide +kernel

theorem phase_24_24 : ∀ i ∈ List.range 4, PhaseAt 24 (24+i) := by decide +kernel

theorem phase_24_28 : ∀ i ∈ List.range 4, PhaseAt 24 (28+i) := by decide +kernel

theorem phase_24_32 : ∀ i ∈ List.range 4, PhaseAt 24 (32+i) := by decide +kernel

theorem phase_24_36 : ∀ i ∈ List.range 4, PhaseAt 24 (36+i) := by decide +kernel

theorem phase_24_40 : ∀ i ∈ List.range 4, PhaseAt 24 (40+i) := by decide +kernel

theorem phase_24_44 : ∀ i ∈ List.range 4, PhaseAt 24 (44+i) := by decide +kernel

theorem phase_24_48 : ∀ i ∈ List.range 4, PhaseAt 24 (48+i) := by decide +kernel

theorem phase_24_52 : ∀ i ∈ List.range 4, PhaseAt 24 (52+i) := by decide +kernel

theorem phase_24_56 : ∀ i ∈ List.range 4, PhaseAt 24 (56+i) := by decide +kernel

theorem phase_24_60 : ∀ i ∈ List.range 4, PhaseAt 24 (60+i) := by decide +kernel

theorem phase_24_64 : ∀ i ∈ List.range 4, PhaseAt 24 (64+i) := by decide +kernel

theorem phase_24_68 : ∀ i ∈ List.range 4, PhaseAt 24 (68+i) := by decide +kernel

theorem phase_24_72 : ∀ i ∈ List.range 4, PhaseAt 24 (72+i) := by decide +kernel

theorem phase_24_76 : ∀ i ∈ List.range 4, PhaseAt 24 (76+i) := by decide +kernel

theorem phase_24_80 : ∀ i ∈ List.range 4, PhaseAt 24 (80+i) := by decide +kernel

theorem phase_24_84 : ∀ i ∈ List.range 4, PhaseAt 24 (84+i) := by decide +kernel

theorem phase_24_88 : ∀ i ∈ List.range 4, PhaseAt 24 (88+i) := by decide +kernel

theorem phase_24_92 : ∀ i ∈ List.range 4, PhaseAt 24 (92+i) := by decide +kernel

theorem phase_24_96 : ∀ i ∈ List.range 4, PhaseAt 24 (96+i) := by decide +kernel

theorem phase_24_100 : ∀ i ∈ List.range 4, PhaseAt 24 (100+i) := by decide +kernel

theorem phase_24_104 : ∀ i ∈ List.range 4, PhaseAt 24 (104+i) := by decide +kernel

theorem phase_24_108 : ∀ i ∈ List.range 4, PhaseAt 24 (108+i) := by decide +kernel

theorem phase_24_112 : ∀ i ∈ List.range 4, PhaseAt 24 (112+i) := by decide +kernel

theorem phase_24_116 : ∀ i ∈ List.range 4, PhaseAt 24 (116+i) := by decide +kernel

theorem phase_24_120 : ∀ i ∈ List.range 4, PhaseAt 24 (120+i) := by decide +kernel

theorem phase_24_124 : ∀ i ∈ List.range 2, PhaseAt 24 (124+i) := by decide +kernel

theorem phase_24 (v : ℕ) (hv : v ∈ List.range 126) : PhaseAt 24 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => PhaseAt 24 v)
  have h := (join 0 64 62 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_24_0 phase_24_4) (join 8 4 4 phase_24_8 phase_24_12)) (join 16 8 8 (join 16 4 4 phase_24_16 phase_24_20) (join 24 4 4 phase_24_24 phase_24_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_24_32 phase_24_36) (join 40 4 4 phase_24_40 phase_24_44)) (join 48 8 8 (join 48 4 4 phase_24_48 phase_24_52) (join 56 4 4 phase_24_56 phase_24_60)))) (join 64 32 30 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_24_64 phase_24_68) (join 72 4 4 phase_24_72 phase_24_76)) (join 80 8 8 (join 80 4 4 phase_24_80 phase_24_84) (join 88 4 4 phase_24_88 phase_24_92))) (join 96 16 14 (join 96 8 8 (join 96 4 4 phase_24_96 phase_24_100) (join 104 4 4 phase_24_104 phase_24_108)) (join 112 8 6 (join 112 4 4 phase_24_112 phase_24_116) (join 120 4 2 phase_24_120 phase_24_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_24_0 : ∀ i ∈ List.range 1, ThresholdAt 24 (0+i) := by decide +kernel

theorem threshold_24_1 : ∀ i ∈ List.range 1, ThresholdAt 24 (1+i) := by decide +kernel

theorem threshold_24_2 : ∀ i ∈ List.range 1, ThresholdAt 24 (2+i) := by decide +kernel

theorem threshold_24_3 : ∀ i ∈ List.range 1, ThresholdAt 24 (3+i) := by decide +kernel

theorem threshold_24_4 : ∀ i ∈ List.range 1, ThresholdAt 24 (4+i) := by decide +kernel

theorem threshold_24_5 : ∀ i ∈ List.range 1, ThresholdAt 24 (5+i) := by decide +kernel

theorem threshold_24_6 : ∀ i ∈ List.range 1, ThresholdAt 24 (6+i) := by decide +kernel

theorem threshold_24_7 : ∀ i ∈ List.range 1, ThresholdAt 24 (7+i) := by decide +kernel

theorem threshold_24_8 : ∀ i ∈ List.range 1, ThresholdAt 24 (8+i) := by decide +kernel

theorem threshold_24_9 : ∀ i ∈ List.range 1, ThresholdAt 24 (9+i) := by decide +kernel

theorem threshold_24_10 : ∀ i ∈ List.range 1, ThresholdAt 24 (10+i) := by decide +kernel

theorem threshold_24_11 : ∀ i ∈ List.range 1, ThresholdAt 24 (11+i) := by decide +kernel

theorem threshold_24_12 : ∀ i ∈ List.range 1, ThresholdAt 24 (12+i) := by decide +kernel

theorem threshold_24_13 : ∀ i ∈ List.range 1, ThresholdAt 24 (13+i) := by decide +kernel

theorem threshold_24_14 : ∀ i ∈ List.range 1, ThresholdAt 24 (14+i) := by decide +kernel

theorem threshold_24_15 : ∀ i ∈ List.range 1, ThresholdAt 24 (15+i) := by decide +kernel

theorem threshold_24_16 : ∀ i ∈ List.range 1, ThresholdAt 24 (16+i) := by decide +kernel

theorem threshold_24_17 : ∀ i ∈ List.range 1, ThresholdAt 24 (17+i) := by decide +kernel

theorem threshold_24_18 : ∀ i ∈ List.range 1, ThresholdAt 24 (18+i) := by decide +kernel

theorem threshold_24_19 : ∀ i ∈ List.range 1, ThresholdAt 24 (19+i) := by decide +kernel

theorem threshold_24_20 : ∀ i ∈ List.range 1, ThresholdAt 24 (20+i) := by decide +kernel

theorem threshold_24_21 : ∀ i ∈ List.range 1, ThresholdAt 24 (21+i) := by decide +kernel

theorem threshold_24_22 : ∀ i ∈ List.range 1, ThresholdAt 24 (22+i) := by decide +kernel

theorem threshold_24_23 : ∀ i ∈ List.range 1, ThresholdAt 24 (23+i) := by decide +kernel

theorem threshold_24_24 : ∀ i ∈ List.range 1, ThresholdAt 24 (24+i) := by decide +kernel

theorem threshold_24_25 : ∀ i ∈ List.range 1, ThresholdAt 24 (25+i) := by decide +kernel

theorem threshold_24_26 : ∀ i ∈ List.range 1, ThresholdAt 24 (26+i) := by decide +kernel

theorem threshold_24_27 : ∀ i ∈ List.range 1, ThresholdAt 24 (27+i) := by decide +kernel

theorem threshold_24_28 : ∀ i ∈ List.range 1, ThresholdAt 24 (28+i) := by decide +kernel

theorem threshold_24_29 : ∀ i ∈ List.range 1, ThresholdAt 24 (29+i) := by decide +kernel

theorem threshold_24_30 : ∀ i ∈ List.range 1, ThresholdAt 24 (30+i) := by decide +kernel

theorem threshold_24_31 : ∀ i ∈ List.range 1, ThresholdAt 24 (31+i) := by decide +kernel

theorem threshold_24_32 : ∀ i ∈ List.range 1, ThresholdAt 24 (32+i) := by decide +kernel

theorem threshold_24_33 : ∀ i ∈ List.range 1, ThresholdAt 24 (33+i) := by decide +kernel

theorem threshold_24_34 : ∀ i ∈ List.range 1, ThresholdAt 24 (34+i) := by decide +kernel

theorem threshold_24_35 : ∀ i ∈ List.range 1, ThresholdAt 24 (35+i) := by decide +kernel

theorem threshold_24_36 : ∀ i ∈ List.range 1, ThresholdAt 24 (36+i) := by decide +kernel

theorem threshold_24_37 : ∀ i ∈ List.range 1, ThresholdAt 24 (37+i) := by decide +kernel

theorem threshold_24_38 : ∀ i ∈ List.range 1, ThresholdAt 24 (38+i) := by decide +kernel

theorem threshold_24_39 : ∀ i ∈ List.range 1, ThresholdAt 24 (39+i) := by decide +kernel

theorem threshold_24_40 : ∀ i ∈ List.range 1, ThresholdAt 24 (40+i) := by decide +kernel

theorem threshold_24_41 : ∀ i ∈ List.range 1, ThresholdAt 24 (41+i) := by decide +kernel

theorem threshold_24_42 : ∀ i ∈ List.range 1, ThresholdAt 24 (42+i) := by decide +kernel

theorem threshold_24_43 : ∀ i ∈ List.range 1, ThresholdAt 24 (43+i) := by decide +kernel

theorem threshold_24_44 : ∀ i ∈ List.range 1, ThresholdAt 24 (44+i) := by decide +kernel

theorem threshold_24_45 : ∀ i ∈ List.range 1, ThresholdAt 24 (45+i) := by decide +kernel

theorem threshold_24_46 : ∀ i ∈ List.range 1, ThresholdAt 24 (46+i) := by decide +kernel

theorem threshold_24_47 : ∀ i ∈ List.range 1, ThresholdAt 24 (47+i) := by decide +kernel

theorem threshold_24_48 : ∀ i ∈ List.range 1, ThresholdAt 24 (48+i) := by decide +kernel

theorem threshold_24_49 : ∀ i ∈ List.range 1, ThresholdAt 24 (49+i) := by decide +kernel

theorem threshold_24_50 : ∀ i ∈ List.range 1, ThresholdAt 24 (50+i) := by decide +kernel

theorem threshold_24_51 : ∀ i ∈ List.range 1, ThresholdAt 24 (51+i) := by decide +kernel

theorem threshold_24_52 : ∀ i ∈ List.range 1, ThresholdAt 24 (52+i) := by decide +kernel

theorem threshold_24_53 : ∀ i ∈ List.range 1, ThresholdAt 24 (53+i) := by decide +kernel

theorem threshold_24_54 : ∀ i ∈ List.range 1, ThresholdAt 24 (54+i) := by decide +kernel

theorem threshold_24_55 : ∀ i ∈ List.range 1, ThresholdAt 24 (55+i) := by decide +kernel

theorem threshold_24_56 : ∀ i ∈ List.range 1, ThresholdAt 24 (56+i) := by decide +kernel

theorem threshold_24_57 : ∀ i ∈ List.range 1, ThresholdAt 24 (57+i) := by decide +kernel

theorem threshold_24_58 : ∀ i ∈ List.range 1, ThresholdAt 24 (58+i) := by decide +kernel

theorem threshold_24_59 : ∀ i ∈ List.range 1, ThresholdAt 24 (59+i) := by decide +kernel

theorem threshold_24_60 : ∀ i ∈ List.range 1, ThresholdAt 24 (60+i) := by decide +kernel

theorem threshold_24_61 : ∀ i ∈ List.range 1, ThresholdAt 24 (61+i) := by decide +kernel

theorem threshold_24_62 : ∀ i ∈ List.range 1, ThresholdAt 24 (62+i) := by decide +kernel

theorem threshold_24_63 : ∀ i ∈ List.range 1, ThresholdAt 24 (63+i) := by decide +kernel

theorem threshold_24_64 : ∀ i ∈ List.range 1, ThresholdAt 24 (64+i) := by decide +kernel

theorem threshold_24_65 : ∀ i ∈ List.range 1, ThresholdAt 24 (65+i) := by decide +kernel

theorem threshold_24_66 : ∀ i ∈ List.range 1, ThresholdAt 24 (66+i) := by decide +kernel

theorem threshold_24_67 : ∀ i ∈ List.range 1, ThresholdAt 24 (67+i) := by decide +kernel

theorem threshold_24_68 : ∀ i ∈ List.range 1, ThresholdAt 24 (68+i) := by decide +kernel

theorem threshold_24_69 : ∀ i ∈ List.range 1, ThresholdAt 24 (69+i) := by decide +kernel

theorem threshold_24_70 : ∀ i ∈ List.range 1, ThresholdAt 24 (70+i) := by decide +kernel

theorem threshold_24_71 : ∀ i ∈ List.range 1, ThresholdAt 24 (71+i) := by decide +kernel

theorem threshold_24_72 : ∀ i ∈ List.range 1, ThresholdAt 24 (72+i) := by decide +kernel

theorem threshold_24_73 : ∀ i ∈ List.range 1, ThresholdAt 24 (73+i) := by decide +kernel

theorem threshold_24_74 : ∀ i ∈ List.range 1, ThresholdAt 24 (74+i) := by decide +kernel

theorem threshold_24_75 : ∀ i ∈ List.range 1, ThresholdAt 24 (75+i) := by decide +kernel

theorem threshold_24_76 : ∀ i ∈ List.range 1, ThresholdAt 24 (76+i) := by decide +kernel

theorem threshold_24_77 : ∀ i ∈ List.range 1, ThresholdAt 24 (77+i) := by decide +kernel

theorem threshold_24_78 : ∀ i ∈ List.range 1, ThresholdAt 24 (78+i) := by decide +kernel

theorem threshold_24_79 : ∀ i ∈ List.range 1, ThresholdAt 24 (79+i) := by decide +kernel

theorem threshold_24_80 : ∀ i ∈ List.range 1, ThresholdAt 24 (80+i) := by decide +kernel

theorem threshold_24_81 : ∀ i ∈ List.range 1, ThresholdAt 24 (81+i) := by decide +kernel

theorem threshold_24_82 : ∀ i ∈ List.range 1, ThresholdAt 24 (82+i) := by decide +kernel

theorem threshold_24_83 : ∀ i ∈ List.range 1, ThresholdAt 24 (83+i) := by decide +kernel

theorem threshold_24_84 : ∀ i ∈ List.range 1, ThresholdAt 24 (84+i) := by decide +kernel

theorem threshold_24_85 : ∀ i ∈ List.range 1, ThresholdAt 24 (85+i) := by decide +kernel

theorem threshold_24_86 : ∀ i ∈ List.range 1, ThresholdAt 24 (86+i) := by decide +kernel

theorem threshold_24_87 : ∀ i ∈ List.range 1, ThresholdAt 24 (87+i) := by decide +kernel

theorem threshold_24_88 : ∀ i ∈ List.range 1, ThresholdAt 24 (88+i) := by decide +kernel

theorem threshold_24_89 : ∀ i ∈ List.range 1, ThresholdAt 24 (89+i) := by decide +kernel

theorem threshold_24_90 : ∀ i ∈ List.range 1, ThresholdAt 24 (90+i) := by decide +kernel

theorem threshold_24_91 : ∀ i ∈ List.range 1, ThresholdAt 24 (91+i) := by decide +kernel

theorem threshold_24_92 : ∀ i ∈ List.range 1, ThresholdAt 24 (92+i) := by decide +kernel

theorem threshold_24_93 : ∀ i ∈ List.range 1, ThresholdAt 24 (93+i) := by decide +kernel

theorem threshold_24_94 : ∀ i ∈ List.range 1, ThresholdAt 24 (94+i) := by decide +kernel

theorem threshold_24_95 : ∀ i ∈ List.range 1, ThresholdAt 24 (95+i) := by decide +kernel

theorem threshold_24_96 : ∀ i ∈ List.range 1, ThresholdAt 24 (96+i) := by decide +kernel

theorem threshold_24_97 : ∀ i ∈ List.range 1, ThresholdAt 24 (97+i) := by decide +kernel

theorem threshold_24_98 : ∀ i ∈ List.range 1, ThresholdAt 24 (98+i) := by decide +kernel

theorem threshold_24_99 : ∀ i ∈ List.range 1, ThresholdAt 24 (99+i) := by decide +kernel

theorem threshold_24_100 : ∀ i ∈ List.range 1, ThresholdAt 24 (100+i) := by decide +kernel

theorem threshold_24_101 : ∀ i ∈ List.range 1, ThresholdAt 24 (101+i) := by decide +kernel

theorem threshold_24_102 : ∀ i ∈ List.range 1, ThresholdAt 24 (102+i) := by decide +kernel

theorem threshold_24_103 : ∀ i ∈ List.range 1, ThresholdAt 24 (103+i) := by decide +kernel

theorem threshold_24_104 : ∀ i ∈ List.range 1, ThresholdAt 24 (104+i) := by decide +kernel

theorem threshold_24_105 : ∀ i ∈ List.range 1, ThresholdAt 24 (105+i) := by decide +kernel

theorem threshold_24_106 : ∀ i ∈ List.range 1, ThresholdAt 24 (106+i) := by decide +kernel

theorem threshold_24_107 : ∀ i ∈ List.range 1, ThresholdAt 24 (107+i) := by decide +kernel

theorem threshold_24_108 : ∀ i ∈ List.range 1, ThresholdAt 24 (108+i) := by decide +kernel

theorem threshold_24_109 : ∀ i ∈ List.range 1, ThresholdAt 24 (109+i) := by decide +kernel

theorem threshold_24_110 : ∀ i ∈ List.range 1, ThresholdAt 24 (110+i) := by decide +kernel

theorem threshold_24_111 : ∀ i ∈ List.range 1, ThresholdAt 24 (111+i) := by decide +kernel

theorem threshold_24_112 : ∀ i ∈ List.range 1, ThresholdAt 24 (112+i) := by decide +kernel

theorem threshold_24_113 : ∀ i ∈ List.range 1, ThresholdAt 24 (113+i) := by decide +kernel

theorem threshold_24_114 : ∀ i ∈ List.range 1, ThresholdAt 24 (114+i) := by decide +kernel

theorem threshold_24_115 : ∀ i ∈ List.range 1, ThresholdAt 24 (115+i) := by decide +kernel

theorem threshold_24_116 : ∀ i ∈ List.range 1, ThresholdAt 24 (116+i) := by decide +kernel

theorem threshold_24_117 : ∀ i ∈ List.range 1, ThresholdAt 24 (117+i) := by decide +kernel

theorem threshold_24_118 : ∀ i ∈ List.range 1, ThresholdAt 24 (118+i) := by decide +kernel

theorem threshold_24_119 : ∀ i ∈ List.range 1, ThresholdAt 24 (119+i) := by decide +kernel

theorem threshold_24_120 : ∀ i ∈ List.range 1, ThresholdAt 24 (120+i) := by decide +kernel

theorem threshold_24_121 : ∀ i ∈ List.range 1, ThresholdAt 24 (121+i) := by decide +kernel

theorem threshold_24_122 : ∀ i ∈ List.range 1, ThresholdAt 24 (122+i) := by decide +kernel

theorem threshold_24_123 : ∀ i ∈ List.range 1, ThresholdAt 24 (123+i) := by decide +kernel

theorem threshold_24_124 : ∀ i ∈ List.range 1, ThresholdAt 24 (124+i) := by decide +kernel

theorem threshold_24_125 : ∀ i ∈ List.range 1, ThresholdAt 24 (125+i) := by decide +kernel

theorem threshold_24 (v : ℕ) (hv : v ∈ List.range 126) : ThresholdAt 24 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => ThresholdAt 24 v)
  have h := (join 0 63 63 (join 0 31 32 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_24_0 (join 1 1 1 threshold_24_1 threshold_24_2)) (join 3 2 2 (join 3 1 1 threshold_24_3 threshold_24_4) (join 5 1 1 threshold_24_5 threshold_24_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_24_7 threshold_24_8) (join 9 1 1 threshold_24_9 threshold_24_10)) (join 11 2 2 (join 11 1 1 threshold_24_11 threshold_24_12) (join 13 1 1 threshold_24_13 threshold_24_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_24_15 threshold_24_16) (join 17 1 1 threshold_24_17 threshold_24_18)) (join 19 2 2 (join 19 1 1 threshold_24_19 threshold_24_20) (join 21 1 1 threshold_24_21 threshold_24_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_24_23 threshold_24_24) (join 25 1 1 threshold_24_25 threshold_24_26)) (join 27 2 2 (join 27 1 1 threshold_24_27 threshold_24_28) (join 29 1 1 threshold_24_29 threshold_24_30))))) (join 31 16 16 (join 31 8 8 (join 31 4 4 (join 31 2 2 (join 31 1 1 threshold_24_31 threshold_24_32) (join 33 1 1 threshold_24_33 threshold_24_34)) (join 35 2 2 (join 35 1 1 threshold_24_35 threshold_24_36) (join 37 1 1 threshold_24_37 threshold_24_38))) (join 39 4 4 (join 39 2 2 (join 39 1 1 threshold_24_39 threshold_24_40) (join 41 1 1 threshold_24_41 threshold_24_42)) (join 43 2 2 (join 43 1 1 threshold_24_43 threshold_24_44) (join 45 1 1 threshold_24_45 threshold_24_46)))) (join 47 8 8 (join 47 4 4 (join 47 2 2 (join 47 1 1 threshold_24_47 threshold_24_48) (join 49 1 1 threshold_24_49 threshold_24_50)) (join 51 2 2 (join 51 1 1 threshold_24_51 threshold_24_52) (join 53 1 1 threshold_24_53 threshold_24_54))) (join 55 4 4 (join 55 2 2 (join 55 1 1 threshold_24_55 threshold_24_56) (join 57 1 1 threshold_24_57 threshold_24_58)) (join 59 2 2 (join 59 1 1 threshold_24_59 threshold_24_60) (join 61 1 1 threshold_24_61 threshold_24_62)))))) (join 63 31 32 (join 63 15 16 (join 63 7 8 (join 63 3 4 (join 63 1 2 threshold_24_63 (join 64 1 1 threshold_24_64 threshold_24_65)) (join 66 2 2 (join 66 1 1 threshold_24_66 threshold_24_67) (join 68 1 1 threshold_24_68 threshold_24_69))) (join 70 4 4 (join 70 2 2 (join 70 1 1 threshold_24_70 threshold_24_71) (join 72 1 1 threshold_24_72 threshold_24_73)) (join 74 2 2 (join 74 1 1 threshold_24_74 threshold_24_75) (join 76 1 1 threshold_24_76 threshold_24_77)))) (join 78 8 8 (join 78 4 4 (join 78 2 2 (join 78 1 1 threshold_24_78 threshold_24_79) (join 80 1 1 threshold_24_80 threshold_24_81)) (join 82 2 2 (join 82 1 1 threshold_24_82 threshold_24_83) (join 84 1 1 threshold_24_84 threshold_24_85))) (join 86 4 4 (join 86 2 2 (join 86 1 1 threshold_24_86 threshold_24_87) (join 88 1 1 threshold_24_88 threshold_24_89)) (join 90 2 2 (join 90 1 1 threshold_24_90 threshold_24_91) (join 92 1 1 threshold_24_92 threshold_24_93))))) (join 94 16 16 (join 94 8 8 (join 94 4 4 (join 94 2 2 (join 94 1 1 threshold_24_94 threshold_24_95) (join 96 1 1 threshold_24_96 threshold_24_97)) (join 98 2 2 (join 98 1 1 threshold_24_98 threshold_24_99) (join 100 1 1 threshold_24_100 threshold_24_101))) (join 102 4 4 (join 102 2 2 (join 102 1 1 threshold_24_102 threshold_24_103) (join 104 1 1 threshold_24_104 threshold_24_105)) (join 106 2 2 (join 106 1 1 threshold_24_106 threshold_24_107) (join 108 1 1 threshold_24_108 threshold_24_109)))) (join 110 8 8 (join 110 4 4 (join 110 2 2 (join 110 1 1 threshold_24_110 threshold_24_111) (join 112 1 1 threshold_24_112 threshold_24_113)) (join 114 2 2 (join 114 1 1 threshold_24_114 threshold_24_115) (join 116 1 1 threshold_24_116 threshold_24_117))) (join 118 4 4 (join 118 2 2 (join 118 1 1 threshold_24_118 threshold_24_119) (join 120 1 1 threshold_24_120 threshold_24_121)) (join 122 2 2 (join 122 1 1 threshold_24_122 threshold_24_123) (join 124 1 1 threshold_24_124 threshold_24_125)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_24_0 : ∀ i ∈ List.range 4, LedgerAt 24 (0+i) := by decide +kernel

theorem ledger_24_4 : ∀ i ∈ List.range 4, LedgerAt 24 (4+i) := by decide +kernel

theorem ledger_24_8 : ∀ i ∈ List.range 4, LedgerAt 24 (8+i) := by decide +kernel

theorem ledger_24_12 : ∀ i ∈ List.range 4, LedgerAt 24 (12+i) := by decide +kernel

theorem ledger_24_16 : ∀ i ∈ List.range 4, LedgerAt 24 (16+i) := by decide +kernel

theorem ledger_24_20 : ∀ i ∈ List.range 4, LedgerAt 24 (20+i) := by decide +kernel

theorem ledger_24_24 : ∀ i ∈ List.range 4, LedgerAt 24 (24+i) := by decide +kernel

theorem ledger_24_28 : ∀ i ∈ List.range 4, LedgerAt 24 (28+i) := by decide +kernel

theorem ledger_24_32 : ∀ i ∈ List.range 4, LedgerAt 24 (32+i) := by decide +kernel

theorem ledger_24_36 : ∀ i ∈ List.range 4, LedgerAt 24 (36+i) := by decide +kernel

theorem ledger_24_40 : ∀ i ∈ List.range 4, LedgerAt 24 (40+i) := by decide +kernel

theorem ledger_24_44 : ∀ i ∈ List.range 4, LedgerAt 24 (44+i) := by decide +kernel

theorem ledger_24_48 : ∀ i ∈ List.range 4, LedgerAt 24 (48+i) := by decide +kernel

theorem ledger_24_52 : ∀ i ∈ List.range 4, LedgerAt 24 (52+i) := by decide +kernel

theorem ledger_24_56 : ∀ i ∈ List.range 4, LedgerAt 24 (56+i) := by decide +kernel

theorem ledger_24_60 : ∀ i ∈ List.range 4, LedgerAt 24 (60+i) := by decide +kernel

theorem ledger_24_64 : ∀ i ∈ List.range 4, LedgerAt 24 (64+i) := by decide +kernel

theorem ledger_24_68 : ∀ i ∈ List.range 4, LedgerAt 24 (68+i) := by decide +kernel

theorem ledger_24_72 : ∀ i ∈ List.range 4, LedgerAt 24 (72+i) := by decide +kernel

theorem ledger_24_76 : ∀ i ∈ List.range 4, LedgerAt 24 (76+i) := by decide +kernel

theorem ledger_24_80 : ∀ i ∈ List.range 4, LedgerAt 24 (80+i) := by decide +kernel

theorem ledger_24_84 : ∀ i ∈ List.range 4, LedgerAt 24 (84+i) := by decide +kernel

theorem ledger_24_88 : ∀ i ∈ List.range 4, LedgerAt 24 (88+i) := by decide +kernel

theorem ledger_24_92 : ∀ i ∈ List.range 4, LedgerAt 24 (92+i) := by decide +kernel

theorem ledger_24_96 : ∀ i ∈ List.range 4, LedgerAt 24 (96+i) := by decide +kernel

theorem ledger_24_100 : ∀ i ∈ List.range 4, LedgerAt 24 (100+i) := by decide +kernel

theorem ledger_24_104 : ∀ i ∈ List.range 4, LedgerAt 24 (104+i) := by decide +kernel

theorem ledger_24_108 : ∀ i ∈ List.range 4, LedgerAt 24 (108+i) := by decide +kernel

theorem ledger_24_112 : ∀ i ∈ List.range 4, LedgerAt 24 (112+i) := by decide +kernel

theorem ledger_24_116 : ∀ i ∈ List.range 4, LedgerAt 24 (116+i) := by decide +kernel

theorem ledger_24_120 : ∀ i ∈ List.range 4, LedgerAt 24 (120+i) := by decide +kernel

theorem ledger_24_124 : ∀ i ∈ List.range 2, LedgerAt 24 (124+i) := by decide +kernel

theorem ledger_24 (v : ℕ) (hv : v ∈ List.range 126) : LedgerAt 24 v := by
  let join := @AffineFiniteChecks6808.range_join (fun v => LedgerAt 24 v)
  have h := (join 0 64 62 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_24_0 ledger_24_4) (join 8 4 4 ledger_24_8 ledger_24_12)) (join 16 8 8 (join 16 4 4 ledger_24_16 ledger_24_20) (join 24 4 4 ledger_24_24 ledger_24_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_24_32 ledger_24_36) (join 40 4 4 ledger_24_40 ledger_24_44)) (join 48 8 8 (join 48 4 4 ledger_24_48 ledger_24_52) (join 56 4 4 ledger_24_56 ledger_24_60)))) (join 64 32 30 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_24_64 ledger_24_68) (join 72 4 4 ledger_24_72 ledger_24_76)) (join 80 8 8 (join 80 4 4 ledger_24_80 ledger_24_84) (join 88 4 4 ledger_24_88 ledger_24_92))) (join 96 16 14 (join 96 8 8 (join 96 4 4 ledger_24_96 ledger_24_100) (join 104 4 4 ledger_24_104 ledger_24_108)) (join 112 8 6 (join 112 4 4 ledger_24_112 ledger_24_116) (join 120 4 2 ledger_24_120 ledger_24_124)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.AffineRowsChecked6808
