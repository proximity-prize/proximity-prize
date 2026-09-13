import ProximityPrize.SubmissionLower.BoundaryTailCheckedR056807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_6_0 : ∀ i ∈ List.range 4, GeometryAt 6 (0+i) := by decide +kernel

theorem geometry_6_4 : ∀ i ∈ List.range 4, GeometryAt 6 (4+i) := by decide +kernel

theorem geometry_6_8 : ∀ i ∈ List.range 4, GeometryAt 6 (8+i) := by decide +kernel

theorem geometry_6_12 : ∀ i ∈ List.range 4, GeometryAt 6 (12+i) := by decide +kernel

theorem geometry_6_16 : ∀ i ∈ List.range 4, GeometryAt 6 (16+i) := by decide +kernel

theorem geometry_6_20 : ∀ i ∈ List.range 4, GeometryAt 6 (20+i) := by decide +kernel

theorem geometry_6_24 : ∀ i ∈ List.range 4, GeometryAt 6 (24+i) := by decide +kernel

theorem geometry_6_28 : ∀ i ∈ List.range 4, GeometryAt 6 (28+i) := by decide +kernel

theorem geometry_6_32 : ∀ i ∈ List.range 4, GeometryAt 6 (32+i) := by decide +kernel

theorem geometry_6_36 : ∀ i ∈ List.range 4, GeometryAt 6 (36+i) := by decide +kernel

theorem geometry_6_40 : ∀ i ∈ List.range 4, GeometryAt 6 (40+i) := by decide +kernel

theorem geometry_6_44 : ∀ i ∈ List.range 4, GeometryAt 6 (44+i) := by decide +kernel

theorem geometry_6_48 : ∀ i ∈ List.range 4, GeometryAt 6 (48+i) := by decide +kernel

theorem geometry_6_52 : ∀ i ∈ List.range 4, GeometryAt 6 (52+i) := by decide +kernel

theorem geometry_6_56 : ∀ i ∈ List.range 4, GeometryAt 6 (56+i) := by decide +kernel

theorem geometry_6_60 : ∀ i ∈ List.range 4, GeometryAt 6 (60+i) := by decide +kernel

theorem geometry_6_64 : ∀ i ∈ List.range 4, GeometryAt 6 (64+i) := by decide +kernel

theorem geometry_6_68 : ∀ i ∈ List.range 4, GeometryAt 6 (68+i) := by decide +kernel

theorem geometry_6_72 : ∀ i ∈ List.range 4, GeometryAt 6 (72+i) := by decide +kernel

theorem geometry_6_76 : ∀ i ∈ List.range 4, GeometryAt 6 (76+i) := by decide +kernel

theorem geometry_6_80 : ∀ i ∈ List.range 4, GeometryAt 6 (80+i) := by decide +kernel

theorem geometry_6_84 : ∀ i ∈ List.range 4, GeometryAt 6 (84+i) := by decide +kernel

theorem geometry_6_88 : ∀ i ∈ List.range 4, GeometryAt 6 (88+i) := by decide +kernel

theorem geometry_6_92 : ∀ i ∈ List.range 4, GeometryAt 6 (92+i) := by decide +kernel

theorem geometry_6_96 : ∀ i ∈ List.range 4, GeometryAt 6 (96+i) := by decide +kernel

theorem geometry_6_100 : ∀ i ∈ List.range 4, GeometryAt 6 (100+i) := by decide +kernel

theorem geometry_6_104 : ∀ i ∈ List.range 4, GeometryAt 6 (104+i) := by decide +kernel

theorem geometry_6_108 : ∀ i ∈ List.range 4, GeometryAt 6 (108+i) := by decide +kernel

theorem geometry_6_112 : ∀ i ∈ List.range 4, GeometryAt 6 (112+i) := by decide +kernel

theorem geometry_6_116 : ∀ i ∈ List.range 4, GeometryAt 6 (116+i) := by decide +kernel

theorem geometry_6_120 : ∀ i ∈ List.range 4, GeometryAt 6 (120+i) := by decide +kernel

theorem geometry_6_124 : ∀ i ∈ List.range 4, GeometryAt 6 (124+i) := by decide +kernel

theorem geometry_6_128 : ∀ i ∈ List.range 4, GeometryAt 6 (128+i) := by decide +kernel

theorem geometry_6_132 : ∀ i ∈ List.range 4, GeometryAt 6 (132+i) := by decide +kernel

theorem geometry_6_136 : ∀ i ∈ List.range 4, GeometryAt 6 (136+i) := by decide +kernel

theorem geometry_6_140 : ∀ i ∈ List.range 1, GeometryAt 6 (140+i) := by decide +kernel

theorem geometry_6 (v : ℕ) (hv : v ∈ List.range 141) : GeometryAt 6 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 6 v)
  have h := (join 0 72 69 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 geometry_6_0 geometry_6_4) (join 8 4 4 geometry_6_8 geometry_6_12)) (join 16 8 12 (join 16 4 4 geometry_6_16 geometry_6_20) (join 24 4 8 geometry_6_24 (join 28 4 4 geometry_6_28 geometry_6_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 geometry_6_36 geometry_6_40) (join 44 4 4 geometry_6_44 geometry_6_48)) (join 52 8 12 (join 52 4 4 geometry_6_52 geometry_6_56) (join 60 4 8 geometry_6_60 (join 64 4 4 geometry_6_64 geometry_6_68))))) (join 72 36 33 (join 72 16 20 (join 72 8 8 (join 72 4 4 geometry_6_72 geometry_6_76) (join 80 4 4 geometry_6_80 geometry_6_84)) (join 88 8 12 (join 88 4 4 geometry_6_88 geometry_6_92) (join 96 4 8 geometry_6_96 (join 100 4 4 geometry_6_100 geometry_6_104)))) (join 108 16 17 (join 108 8 8 (join 108 4 4 geometry_6_108 geometry_6_112) (join 116 4 4 geometry_6_116 geometry_6_120)) (join 124 8 9 (join 124 4 4 geometry_6_124 geometry_6_128) (join 132 4 5 geometry_6_132 (join 136 4 1 geometry_6_136 geometry_6_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_6_0 : ∀ i ∈ List.range 1, StrictAt 6 (0+i) := by decide +kernel

theorem strict_6_1 : ∀ i ∈ List.range 1, StrictAt 6 (1+i) := by decide +kernel

theorem strict_6_2 : ∀ i ∈ List.range 1, StrictAt 6 (2+i) := by decide +kernel

theorem strict_6_3 : ∀ i ∈ List.range 1, StrictAt 6 (3+i) := by decide +kernel

theorem strict_6_4 : ∀ i ∈ List.range 1, StrictAt 6 (4+i) := by decide +kernel

theorem strict_6_5 : ∀ i ∈ List.range 1, StrictAt 6 (5+i) := by decide +kernel

theorem strict_6_6 : ∀ i ∈ List.range 1, StrictAt 6 (6+i) := by decide +kernel

theorem strict_6_7 : ∀ i ∈ List.range 1, StrictAt 6 (7+i) := by decide +kernel

theorem strict_6_8 : ∀ i ∈ List.range 1, StrictAt 6 (8+i) := by decide +kernel

theorem strict_6_9 : ∀ i ∈ List.range 1, StrictAt 6 (9+i) := by decide +kernel

theorem strict_6_10 : ∀ i ∈ List.range 1, StrictAt 6 (10+i) := by decide +kernel

theorem strict_6_11 : ∀ i ∈ List.range 1, StrictAt 6 (11+i) := by decide +kernel

theorem strict_6_12 : ∀ i ∈ List.range 1, StrictAt 6 (12+i) := by decide +kernel

theorem strict_6_13 : ∀ i ∈ List.range 1, StrictAt 6 (13+i) := by decide +kernel

theorem strict_6_14 : ∀ i ∈ List.range 1, StrictAt 6 (14+i) := by decide +kernel

theorem strict_6_15 : ∀ i ∈ List.range 1, StrictAt 6 (15+i) := by decide +kernel

theorem strict_6_16 : ∀ i ∈ List.range 1, StrictAt 6 (16+i) := by decide +kernel

theorem strict_6_17 : ∀ i ∈ List.range 1, StrictAt 6 (17+i) := by decide +kernel

theorem strict_6_18 : ∀ i ∈ List.range 1, StrictAt 6 (18+i) := by decide +kernel

theorem strict_6_19 : ∀ i ∈ List.range 1, StrictAt 6 (19+i) := by decide +kernel

theorem strict_6_20 : ∀ i ∈ List.range 1, StrictAt 6 (20+i) := by decide +kernel

theorem strict_6_21 : ∀ i ∈ List.range 1, StrictAt 6 (21+i) := by decide +kernel

theorem strict_6_22 : ∀ i ∈ List.range 1, StrictAt 6 (22+i) := by decide +kernel

theorem strict_6_23 : ∀ i ∈ List.range 1, StrictAt 6 (23+i) := by decide +kernel

theorem strict_6_24 : ∀ i ∈ List.range 1, StrictAt 6 (24+i) := by decide +kernel

theorem strict_6_25 : ∀ i ∈ List.range 1, StrictAt 6 (25+i) := by decide +kernel

theorem strict_6_26 : ∀ i ∈ List.range 1, StrictAt 6 (26+i) := by decide +kernel

theorem strict_6_27 : ∀ i ∈ List.range 1, StrictAt 6 (27+i) := by decide +kernel

theorem strict_6_28 : ∀ i ∈ List.range 1, StrictAt 6 (28+i) := by decide +kernel

theorem strict_6_29 : ∀ i ∈ List.range 1, StrictAt 6 (29+i) := by decide +kernel

theorem strict_6_30 : ∀ i ∈ List.range 1, StrictAt 6 (30+i) := by decide +kernel

theorem strict_6_31 : ∀ i ∈ List.range 1, StrictAt 6 (31+i) := by decide +kernel

theorem strict_6_32 : ∀ i ∈ List.range 1, StrictAt 6 (32+i) := by decide +kernel

theorem strict_6_33 : ∀ i ∈ List.range 1, StrictAt 6 (33+i) := by decide +kernel

theorem strict_6_34 : ∀ i ∈ List.range 1, StrictAt 6 (34+i) := by decide +kernel

theorem strict_6_35 : ∀ i ∈ List.range 1, StrictAt 6 (35+i) := by decide +kernel

theorem strict_6_36 : ∀ i ∈ List.range 1, StrictAt 6 (36+i) := by decide +kernel

theorem strict_6_37 : ∀ i ∈ List.range 1, StrictAt 6 (37+i) := by decide +kernel

theorem strict_6_38 : ∀ i ∈ List.range 1, StrictAt 6 (38+i) := by decide +kernel

theorem strict_6_39 : ∀ i ∈ List.range 1, StrictAt 6 (39+i) := by decide +kernel

theorem strict_6_40 : ∀ i ∈ List.range 1, StrictAt 6 (40+i) := by decide +kernel

theorem strict_6_41 : ∀ i ∈ List.range 1, StrictAt 6 (41+i) := by decide +kernel

theorem strict_6_42 : ∀ i ∈ List.range 1, StrictAt 6 (42+i) := by decide +kernel

theorem strict_6_43 : ∀ i ∈ List.range 1, StrictAt 6 (43+i) := by decide +kernel

theorem strict_6_44 : ∀ i ∈ List.range 1, StrictAt 6 (44+i) := by decide +kernel

theorem strict_6_45 : ∀ i ∈ List.range 1, StrictAt 6 (45+i) := by decide +kernel

theorem strict_6_46 : ∀ i ∈ List.range 1, StrictAt 6 (46+i) := by decide +kernel

theorem strict_6_47 : ∀ i ∈ List.range 1, StrictAt 6 (47+i) := by decide +kernel

theorem strict_6_48 : ∀ i ∈ List.range 1, StrictAt 6 (48+i) := by decide +kernel

theorem strict_6_49 : ∀ i ∈ List.range 1, StrictAt 6 (49+i) := by decide +kernel

theorem strict_6_50 : ∀ i ∈ List.range 1, StrictAt 6 (50+i) := by decide +kernel

theorem strict_6_51 : ∀ i ∈ List.range 1, StrictAt 6 (51+i) := by decide +kernel

theorem strict_6_52 : ∀ i ∈ List.range 1, StrictAt 6 (52+i) := by decide +kernel

theorem strict_6_53 : ∀ i ∈ List.range 1, StrictAt 6 (53+i) := by decide +kernel

theorem strict_6_54 : ∀ i ∈ List.range 1, StrictAt 6 (54+i) := by decide +kernel

theorem strict_6_55 : ∀ i ∈ List.range 1, StrictAt 6 (55+i) := by decide +kernel

theorem strict_6_56 : ∀ i ∈ List.range 1, StrictAt 6 (56+i) := by decide +kernel

theorem strict_6_57 : ∀ i ∈ List.range 1, StrictAt 6 (57+i) := by decide +kernel

theorem strict_6_58 : ∀ i ∈ List.range 1, StrictAt 6 (58+i) := by decide +kernel

theorem strict_6_59 : ∀ i ∈ List.range 1, StrictAt 6 (59+i) := by decide +kernel

theorem strict_6_60 : ∀ i ∈ List.range 1, StrictAt 6 (60+i) := by decide +kernel

theorem strict_6_61 : ∀ i ∈ List.range 1, StrictAt 6 (61+i) := by decide +kernel

theorem strict_6_62 : ∀ i ∈ List.range 1, StrictAt 6 (62+i) := by decide +kernel

theorem strict_6_63 : ∀ i ∈ List.range 1, StrictAt 6 (63+i) := by decide +kernel

theorem strict_6_64 : ∀ i ∈ List.range 1, StrictAt 6 (64+i) := by decide +kernel

theorem strict_6_65 : ∀ i ∈ List.range 1, StrictAt 6 (65+i) := by decide +kernel

theorem strict_6_66 : ∀ i ∈ List.range 1, StrictAt 6 (66+i) := by decide +kernel

theorem strict_6_67 : ∀ i ∈ List.range 1, StrictAt 6 (67+i) := by decide +kernel

theorem strict_6_68 : ∀ i ∈ List.range 1, StrictAt 6 (68+i) := by decide +kernel

theorem strict_6_69 : ∀ i ∈ List.range 1, StrictAt 6 (69+i) := by decide +kernel

theorem strict_6_70 : ∀ i ∈ List.range 1, StrictAt 6 (70+i) := by decide +kernel

theorem strict_6_71 : ∀ i ∈ List.range 1, StrictAt 6 (71+i) := by decide +kernel

theorem strict_6_72 : ∀ i ∈ List.range 1, StrictAt 6 (72+i) := by decide +kernel

theorem strict_6_73 : ∀ i ∈ List.range 1, StrictAt 6 (73+i) := by decide +kernel

theorem strict_6_74 : ∀ i ∈ List.range 1, StrictAt 6 (74+i) := by decide +kernel

theorem strict_6_75 : ∀ i ∈ List.range 1, StrictAt 6 (75+i) := by decide +kernel

theorem strict_6_76 : ∀ i ∈ List.range 1, StrictAt 6 (76+i) := by decide +kernel

theorem strict_6_77 : ∀ i ∈ List.range 1, StrictAt 6 (77+i) := by decide +kernel

theorem strict_6_78 : ∀ i ∈ List.range 1, StrictAt 6 (78+i) := by decide +kernel

theorem strict_6_79 : ∀ i ∈ List.range 1, StrictAt 6 (79+i) := by decide +kernel

theorem strict_6_80 : ∀ i ∈ List.range 1, StrictAt 6 (80+i) := by decide +kernel

theorem strict_6_81 : ∀ i ∈ List.range 1, StrictAt 6 (81+i) := by decide +kernel

theorem strict_6_82 : ∀ i ∈ List.range 1, StrictAt 6 (82+i) := by decide +kernel

theorem strict_6_83 : ∀ i ∈ List.range 1, StrictAt 6 (83+i) := by decide +kernel

theorem strict_6_84 : ∀ i ∈ List.range 1, StrictAt 6 (84+i) := by decide +kernel

theorem strict_6_85 : ∀ i ∈ List.range 1, StrictAt 6 (85+i) := by decide +kernel

theorem strict_6_86 : ∀ i ∈ List.range 1, StrictAt 6 (86+i) := by decide +kernel

theorem strict_6_87 : ∀ i ∈ List.range 1, StrictAt 6 (87+i) := by decide +kernel

theorem strict_6_88 : ∀ i ∈ List.range 1, StrictAt 6 (88+i) := by decide +kernel

theorem strict_6_89 : ∀ i ∈ List.range 1, StrictAt 6 (89+i) := by decide +kernel

theorem strict_6_90 : ∀ i ∈ List.range 1, StrictAt 6 (90+i) := by decide +kernel

theorem strict_6_91 : ∀ i ∈ List.range 1, StrictAt 6 (91+i) := by decide +kernel

theorem strict_6_92 : ∀ i ∈ List.range 1, StrictAt 6 (92+i) := by decide +kernel

theorem strict_6_93 : ∀ i ∈ List.range 1, StrictAt 6 (93+i) := by decide +kernel

theorem strict_6_94 : ∀ i ∈ List.range 1, StrictAt 6 (94+i) := by decide +kernel

theorem strict_6_95 : ∀ i ∈ List.range 1, StrictAt 6 (95+i) := by decide +kernel

theorem strict_6_96 : ∀ i ∈ List.range 1, StrictAt 6 (96+i) := by decide +kernel

theorem strict_6_97 : ∀ i ∈ List.range 1, StrictAt 6 (97+i) := by decide +kernel

theorem strict_6_98 : ∀ i ∈ List.range 1, StrictAt 6 (98+i) := by decide +kernel

theorem strict_6_99 : ∀ i ∈ List.range 1, StrictAt 6 (99+i) := by decide +kernel

theorem strict_6_100 : ∀ i ∈ List.range 1, StrictAt 6 (100+i) := by decide +kernel

theorem strict_6_101 : ∀ i ∈ List.range 1, StrictAt 6 (101+i) := by decide +kernel

theorem strict_6_102 : ∀ i ∈ List.range 1, StrictAt 6 (102+i) := by decide +kernel

theorem strict_6_103 : ∀ i ∈ List.range 1, StrictAt 6 (103+i) := by decide +kernel

theorem strict_6_104 : ∀ i ∈ List.range 1, StrictAt 6 (104+i) := by decide +kernel

theorem strict_6_105 : ∀ i ∈ List.range 1, StrictAt 6 (105+i) := by decide +kernel

theorem strict_6_106 : ∀ i ∈ List.range 1, StrictAt 6 (106+i) := by decide +kernel

theorem strict_6_107 : ∀ i ∈ List.range 1, StrictAt 6 (107+i) := by decide +kernel

theorem strict_6_108 : ∀ i ∈ List.range 1, StrictAt 6 (108+i) := by decide +kernel

theorem strict_6_109 : ∀ i ∈ List.range 1, StrictAt 6 (109+i) := by decide +kernel

theorem strict_6_110 : ∀ i ∈ List.range 1, StrictAt 6 (110+i) := by decide +kernel

theorem strict_6_111 : ∀ i ∈ List.range 1, StrictAt 6 (111+i) := by decide +kernel

theorem strict_6_112 : ∀ i ∈ List.range 1, StrictAt 6 (112+i) := by decide +kernel

theorem strict_6_113 : ∀ i ∈ List.range 1, StrictAt 6 (113+i) := by decide +kernel

theorem strict_6_114 : ∀ i ∈ List.range 1, StrictAt 6 (114+i) := by decide +kernel

theorem strict_6_115 : ∀ i ∈ List.range 1, StrictAt 6 (115+i) := by decide +kernel

theorem strict_6_116 : ∀ i ∈ List.range 1, StrictAt 6 (116+i) := by decide +kernel

theorem strict_6_117 : ∀ i ∈ List.range 1, StrictAt 6 (117+i) := by decide +kernel

theorem strict_6_118 : ∀ i ∈ List.range 1, StrictAt 6 (118+i) := by decide +kernel

theorem strict_6_119 : ∀ i ∈ List.range 1, StrictAt 6 (119+i) := by decide +kernel

theorem strict_6_120 : ∀ i ∈ List.range 1, StrictAt 6 (120+i) := by decide +kernel

theorem strict_6_121 : ∀ i ∈ List.range 1, StrictAt 6 (121+i) := by decide +kernel

theorem strict_6_122 : ∀ i ∈ List.range 1, StrictAt 6 (122+i) := by decide +kernel

theorem strict_6_123 : ∀ i ∈ List.range 1, StrictAt 6 (123+i) := by decide +kernel

theorem strict_6_124 : ∀ i ∈ List.range 1, StrictAt 6 (124+i) := by decide +kernel

theorem strict_6_125 : ∀ i ∈ List.range 1, StrictAt 6 (125+i) := by decide +kernel

theorem strict_6_126 : ∀ i ∈ List.range 1, StrictAt 6 (126+i) := by decide +kernel

theorem strict_6_127 : ∀ i ∈ List.range 1, StrictAt 6 (127+i) := by decide +kernel

theorem strict_6_128 : ∀ i ∈ List.range 1, StrictAt 6 (128+i) := by decide +kernel

theorem strict_6_129 : ∀ i ∈ List.range 1, StrictAt 6 (129+i) := by decide +kernel

theorem strict_6_130 : ∀ i ∈ List.range 1, StrictAt 6 (130+i) := by decide +kernel

theorem strict_6_131 : ∀ i ∈ List.range 1, StrictAt 6 (131+i) := by decide +kernel

theorem strict_6_132 : ∀ i ∈ List.range 1, StrictAt 6 (132+i) := by decide +kernel

theorem strict_6_133 : ∀ i ∈ List.range 1, StrictAt 6 (133+i) := by decide +kernel

theorem strict_6_134 : ∀ i ∈ List.range 1, StrictAt 6 (134+i) := by decide +kernel

theorem strict_6_135 : ∀ i ∈ List.range 1, StrictAt 6 (135+i) := by decide +kernel

theorem strict_6_136 : ∀ i ∈ List.range 1, StrictAt 6 (136+i) := by decide +kernel

theorem strict_6_137 : ∀ i ∈ List.range 1, StrictAt 6 (137+i) := by decide +kernel

theorem strict_6_138 : ∀ i ∈ List.range 1, StrictAt 6 (138+i) := by decide +kernel

theorem strict_6_139 : ∀ i ∈ List.range 1, StrictAt 6 (139+i) := by decide +kernel

theorem strict_6_140 : ∀ i ∈ List.range 1, StrictAt 6 (140+i) := by decide +kernel

theorem strict_6 (v : ℕ) (hv : v ∈ List.range 141) : StrictAt 6 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 6 v)
  have h := (join 0 70 71 (join 0 35 35 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 strict_6_0 strict_6_1) (join 2 1 1 strict_6_2 strict_6_3)) (join 4 2 2 (join 4 1 1 strict_6_4 strict_6_5) (join 6 1 1 strict_6_6 strict_6_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 strict_6_8 strict_6_9) (join 10 1 1 strict_6_10 strict_6_11)) (join 12 2 3 (join 12 1 1 strict_6_12 strict_6_13) (join 14 1 2 strict_6_14 (join 15 1 1 strict_6_15 strict_6_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 strict_6_17 strict_6_18) (join 19 1 1 strict_6_19 strict_6_20)) (join 21 2 3 (join 21 1 1 strict_6_21 strict_6_22) (join 23 1 2 strict_6_23 (join 24 1 1 strict_6_24 strict_6_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 strict_6_26 strict_6_27) (join 28 1 1 strict_6_28 strict_6_29)) (join 30 2 3 (join 30 1 1 strict_6_30 strict_6_31) (join 32 1 2 strict_6_32 (join 33 1 1 strict_6_33 strict_6_34)))))) (join 35 17 18 (join 35 8 9 (join 35 4 4 (join 35 2 2 (join 35 1 1 strict_6_35 strict_6_36) (join 37 1 1 strict_6_37 strict_6_38)) (join 39 2 2 (join 39 1 1 strict_6_39 strict_6_40) (join 41 1 1 strict_6_41 strict_6_42))) (join 43 4 5 (join 43 2 2 (join 43 1 1 strict_6_43 strict_6_44) (join 45 1 1 strict_6_45 strict_6_46)) (join 47 2 3 (join 47 1 1 strict_6_47 strict_6_48) (join 49 1 2 strict_6_49 (join 50 1 1 strict_6_50 strict_6_51))))) (join 52 9 9 (join 52 4 5 (join 52 2 2 (join 52 1 1 strict_6_52 strict_6_53) (join 54 1 1 strict_6_54 strict_6_55)) (join 56 2 3 (join 56 1 1 strict_6_56 strict_6_57) (join 58 1 2 strict_6_58 (join 59 1 1 strict_6_59 strict_6_60)))) (join 61 4 5 (join 61 2 2 (join 61 1 1 strict_6_61 strict_6_62) (join 63 1 1 strict_6_63 strict_6_64)) (join 65 2 3 (join 65 1 1 strict_6_65 strict_6_66) (join 67 1 2 strict_6_67 (join 68 1 1 strict_6_68 strict_6_69))))))) (join 70 35 36 (join 70 17 18 (join 70 8 9 (join 70 4 4 (join 70 2 2 (join 70 1 1 strict_6_70 strict_6_71) (join 72 1 1 strict_6_72 strict_6_73)) (join 74 2 2 (join 74 1 1 strict_6_74 strict_6_75) (join 76 1 1 strict_6_76 strict_6_77))) (join 78 4 5 (join 78 2 2 (join 78 1 1 strict_6_78 strict_6_79) (join 80 1 1 strict_6_80 strict_6_81)) (join 82 2 3 (join 82 1 1 strict_6_82 strict_6_83) (join 84 1 2 strict_6_84 (join 85 1 1 strict_6_85 strict_6_86))))) (join 87 9 9 (join 87 4 5 (join 87 2 2 (join 87 1 1 strict_6_87 strict_6_88) (join 89 1 1 strict_6_89 strict_6_90)) (join 91 2 3 (join 91 1 1 strict_6_91 strict_6_92) (join 93 1 2 strict_6_93 (join 94 1 1 strict_6_94 strict_6_95)))) (join 96 4 5 (join 96 2 2 (join 96 1 1 strict_6_96 strict_6_97) (join 98 1 1 strict_6_98 strict_6_99)) (join 100 2 3 (join 100 1 1 strict_6_100 strict_6_101) (join 102 1 2 strict_6_102 (join 103 1 1 strict_6_103 strict_6_104)))))) (join 105 18 18 (join 105 9 9 (join 105 4 5 (join 105 2 2 (join 105 1 1 strict_6_105 strict_6_106) (join 107 1 1 strict_6_107 strict_6_108)) (join 109 2 3 (join 109 1 1 strict_6_109 strict_6_110) (join 111 1 2 strict_6_111 (join 112 1 1 strict_6_112 strict_6_113)))) (join 114 4 5 (join 114 2 2 (join 114 1 1 strict_6_114 strict_6_115) (join 116 1 1 strict_6_116 strict_6_117)) (join 118 2 3 (join 118 1 1 strict_6_118 strict_6_119) (join 120 1 2 strict_6_120 (join 121 1 1 strict_6_121 strict_6_122))))) (join 123 9 9 (join 123 4 5 (join 123 2 2 (join 123 1 1 strict_6_123 strict_6_124) (join 125 1 1 strict_6_125 strict_6_126)) (join 127 2 3 (join 127 1 1 strict_6_127 strict_6_128) (join 129 1 2 strict_6_129 (join 130 1 1 strict_6_130 strict_6_131)))) (join 132 4 5 (join 132 2 2 (join 132 1 1 strict_6_132 strict_6_133) (join 134 1 1 strict_6_134 strict_6_135)) (join 136 2 3 (join 136 1 1 strict_6_136 strict_6_137) (join 138 1 2 strict_6_138 (join 139 1 1 strict_6_139 strict_6_140))))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_6_0 : ∀ i ∈ List.range 4, PhaseAt 6 (0+i) := by decide +kernel

theorem phase_6_4 : ∀ i ∈ List.range 4, PhaseAt 6 (4+i) := by decide +kernel

theorem phase_6_8 : ∀ i ∈ List.range 4, PhaseAt 6 (8+i) := by decide +kernel

theorem phase_6_12 : ∀ i ∈ List.range 4, PhaseAt 6 (12+i) := by decide +kernel

theorem phase_6_16 : ∀ i ∈ List.range 4, PhaseAt 6 (16+i) := by decide +kernel

theorem phase_6_20 : ∀ i ∈ List.range 4, PhaseAt 6 (20+i) := by decide +kernel

theorem phase_6_24 : ∀ i ∈ List.range 4, PhaseAt 6 (24+i) := by decide +kernel

theorem phase_6_28 : ∀ i ∈ List.range 4, PhaseAt 6 (28+i) := by decide +kernel

theorem phase_6_32 : ∀ i ∈ List.range 4, PhaseAt 6 (32+i) := by decide +kernel

theorem phase_6_36 : ∀ i ∈ List.range 4, PhaseAt 6 (36+i) := by decide +kernel

theorem phase_6_40 : ∀ i ∈ List.range 4, PhaseAt 6 (40+i) := by decide +kernel

theorem phase_6_44 : ∀ i ∈ List.range 4, PhaseAt 6 (44+i) := by decide +kernel

theorem phase_6_48 : ∀ i ∈ List.range 4, PhaseAt 6 (48+i) := by decide +kernel

theorem phase_6_52 : ∀ i ∈ List.range 4, PhaseAt 6 (52+i) := by decide +kernel

theorem phase_6_56 : ∀ i ∈ List.range 4, PhaseAt 6 (56+i) := by decide +kernel

theorem phase_6_60 : ∀ i ∈ List.range 4, PhaseAt 6 (60+i) := by decide +kernel

theorem phase_6_64 : ∀ i ∈ List.range 4, PhaseAt 6 (64+i) := by decide +kernel

theorem phase_6_68 : ∀ i ∈ List.range 4, PhaseAt 6 (68+i) := by decide +kernel

theorem phase_6_72 : ∀ i ∈ List.range 4, PhaseAt 6 (72+i) := by decide +kernel

theorem phase_6_76 : ∀ i ∈ List.range 4, PhaseAt 6 (76+i) := by decide +kernel

theorem phase_6_80 : ∀ i ∈ List.range 4, PhaseAt 6 (80+i) := by decide +kernel

theorem phase_6_84 : ∀ i ∈ List.range 4, PhaseAt 6 (84+i) := by decide +kernel

theorem phase_6_88 : ∀ i ∈ List.range 4, PhaseAt 6 (88+i) := by decide +kernel

theorem phase_6_92 : ∀ i ∈ List.range 4, PhaseAt 6 (92+i) := by decide +kernel

theorem phase_6_96 : ∀ i ∈ List.range 4, PhaseAt 6 (96+i) := by decide +kernel

theorem phase_6_100 : ∀ i ∈ List.range 4, PhaseAt 6 (100+i) := by decide +kernel

theorem phase_6_104 : ∀ i ∈ List.range 4, PhaseAt 6 (104+i) := by decide +kernel

theorem phase_6_108 : ∀ i ∈ List.range 4, PhaseAt 6 (108+i) := by decide +kernel

theorem phase_6_112 : ∀ i ∈ List.range 4, PhaseAt 6 (112+i) := by decide +kernel

theorem phase_6_116 : ∀ i ∈ List.range 4, PhaseAt 6 (116+i) := by decide +kernel

theorem phase_6_120 : ∀ i ∈ List.range 4, PhaseAt 6 (120+i) := by decide +kernel

theorem phase_6_124 : ∀ i ∈ List.range 4, PhaseAt 6 (124+i) := by decide +kernel

theorem phase_6_128 : ∀ i ∈ List.range 4, PhaseAt 6 (128+i) := by decide +kernel

theorem phase_6_132 : ∀ i ∈ List.range 4, PhaseAt 6 (132+i) := by decide +kernel

theorem phase_6_136 : ∀ i ∈ List.range 4, PhaseAt 6 (136+i) := by decide +kernel

theorem phase_6_140 : ∀ i ∈ List.range 1, PhaseAt 6 (140+i) := by decide +kernel

theorem phase_6 (v : ℕ) (hv : v ∈ List.range 141) : PhaseAt 6 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 6 v)
  have h := (join 0 72 69 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_6_0 phase_6_4) (join 8 4 4 phase_6_8 phase_6_12)) (join 16 8 12 (join 16 4 4 phase_6_16 phase_6_20) (join 24 4 8 phase_6_24 (join 28 4 4 phase_6_28 phase_6_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_6_36 phase_6_40) (join 44 4 4 phase_6_44 phase_6_48)) (join 52 8 12 (join 52 4 4 phase_6_52 phase_6_56) (join 60 4 8 phase_6_60 (join 64 4 4 phase_6_64 phase_6_68))))) (join 72 36 33 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_6_72 phase_6_76) (join 80 4 4 phase_6_80 phase_6_84)) (join 88 8 12 (join 88 4 4 phase_6_88 phase_6_92) (join 96 4 8 phase_6_96 (join 100 4 4 phase_6_100 phase_6_104)))) (join 108 16 17 (join 108 8 8 (join 108 4 4 phase_6_108 phase_6_112) (join 116 4 4 phase_6_116 phase_6_120)) (join 124 8 9 (join 124 4 4 phase_6_124 phase_6_128) (join 132 4 5 phase_6_132 (join 136 4 1 phase_6_136 phase_6_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_6_0 : ∀ i ∈ List.range 1, ThresholdAt 6 (0+i) := by decide +kernel

theorem threshold_6_1 : ∀ i ∈ List.range 1, ThresholdAt 6 (1+i) := by decide +kernel

theorem threshold_6_2 : ∀ i ∈ List.range 1, ThresholdAt 6 (2+i) := by decide +kernel

theorem threshold_6_3 : ∀ i ∈ List.range 1, ThresholdAt 6 (3+i) := by decide +kernel

theorem threshold_6_4 : ∀ i ∈ List.range 1, ThresholdAt 6 (4+i) := by decide +kernel

theorem threshold_6_5 : ∀ i ∈ List.range 1, ThresholdAt 6 (5+i) := by decide +kernel

theorem threshold_6_6 : ∀ i ∈ List.range 1, ThresholdAt 6 (6+i) := by decide +kernel

theorem threshold_6_7 : ∀ i ∈ List.range 1, ThresholdAt 6 (7+i) := by decide +kernel

theorem threshold_6_8 : ∀ i ∈ List.range 1, ThresholdAt 6 (8+i) := by decide +kernel

theorem threshold_6_9 : ∀ i ∈ List.range 1, ThresholdAt 6 (9+i) := by decide +kernel

theorem threshold_6_10 : ∀ i ∈ List.range 1, ThresholdAt 6 (10+i) := by decide +kernel

theorem threshold_6_11 : ∀ i ∈ List.range 1, ThresholdAt 6 (11+i) := by decide +kernel

theorem threshold_6_12 : ∀ i ∈ List.range 1, ThresholdAt 6 (12+i) := by decide +kernel

theorem threshold_6_13 : ∀ i ∈ List.range 1, ThresholdAt 6 (13+i) := by decide +kernel

theorem threshold_6_14 : ∀ i ∈ List.range 1, ThresholdAt 6 (14+i) := by decide +kernel

theorem threshold_6_15 : ∀ i ∈ List.range 1, ThresholdAt 6 (15+i) := by decide +kernel

theorem threshold_6_16 : ∀ i ∈ List.range 1, ThresholdAt 6 (16+i) := by decide +kernel

theorem threshold_6_17 : ∀ i ∈ List.range 1, ThresholdAt 6 (17+i) := by decide +kernel

theorem threshold_6_18 : ∀ i ∈ List.range 1, ThresholdAt 6 (18+i) := by decide +kernel

theorem threshold_6_19 : ∀ i ∈ List.range 1, ThresholdAt 6 (19+i) := by decide +kernel

theorem threshold_6_20 : ∀ i ∈ List.range 1, ThresholdAt 6 (20+i) := by decide +kernel

theorem threshold_6_21 : ∀ i ∈ List.range 1, ThresholdAt 6 (21+i) := by decide +kernel

theorem threshold_6_22 : ∀ i ∈ List.range 1, ThresholdAt 6 (22+i) := by decide +kernel

theorem threshold_6_23 : ∀ i ∈ List.range 1, ThresholdAt 6 (23+i) := by decide +kernel

theorem threshold_6_24 : ∀ i ∈ List.range 1, ThresholdAt 6 (24+i) := by decide +kernel

theorem threshold_6_25 : ∀ i ∈ List.range 1, ThresholdAt 6 (25+i) := by decide +kernel

theorem threshold_6_26 : ∀ i ∈ List.range 1, ThresholdAt 6 (26+i) := by decide +kernel

theorem threshold_6_27 : ∀ i ∈ List.range 1, ThresholdAt 6 (27+i) := by decide +kernel

theorem threshold_6_28 : ∀ i ∈ List.range 1, ThresholdAt 6 (28+i) := by decide +kernel

theorem threshold_6_29 : ∀ i ∈ List.range 1, ThresholdAt 6 (29+i) := by decide +kernel

theorem threshold_6_30 : ∀ i ∈ List.range 1, ThresholdAt 6 (30+i) := by decide +kernel

theorem threshold_6_31 : ∀ i ∈ List.range 1, ThresholdAt 6 (31+i) := by decide +kernel

theorem threshold_6_32 : ∀ i ∈ List.range 1, ThresholdAt 6 (32+i) := by decide +kernel

theorem threshold_6_33 : ∀ i ∈ List.range 1, ThresholdAt 6 (33+i) := by decide +kernel

theorem threshold_6_34 : ∀ i ∈ List.range 1, ThresholdAt 6 (34+i) := by decide +kernel

theorem threshold_6_35 : ∀ i ∈ List.range 1, ThresholdAt 6 (35+i) := by decide +kernel

theorem threshold_6_36 : ∀ i ∈ List.range 1, ThresholdAt 6 (36+i) := by decide +kernel

theorem threshold_6_37 : ∀ i ∈ List.range 1, ThresholdAt 6 (37+i) := by decide +kernel

theorem threshold_6_38 : ∀ i ∈ List.range 1, ThresholdAt 6 (38+i) := by decide +kernel

theorem threshold_6_39 : ∀ i ∈ List.range 1, ThresholdAt 6 (39+i) := by decide +kernel

theorem threshold_6_40 : ∀ i ∈ List.range 1, ThresholdAt 6 (40+i) := by decide +kernel

theorem threshold_6_41 : ∀ i ∈ List.range 1, ThresholdAt 6 (41+i) := by decide +kernel

theorem threshold_6_42 : ∀ i ∈ List.range 1, ThresholdAt 6 (42+i) := by decide +kernel

theorem threshold_6_43 : ∀ i ∈ List.range 1, ThresholdAt 6 (43+i) := by decide +kernel

theorem threshold_6_44 : ∀ i ∈ List.range 1, ThresholdAt 6 (44+i) := by decide +kernel

theorem threshold_6_45 : ∀ i ∈ List.range 1, ThresholdAt 6 (45+i) := by decide +kernel

theorem threshold_6_46 : ∀ i ∈ List.range 1, ThresholdAt 6 (46+i) := by decide +kernel

theorem threshold_6_47 : ∀ i ∈ List.range 1, ThresholdAt 6 (47+i) := by decide +kernel

theorem threshold_6_48 : ∀ i ∈ List.range 1, ThresholdAt 6 (48+i) := by decide +kernel

theorem threshold_6_49 : ∀ i ∈ List.range 1, ThresholdAt 6 (49+i) := by decide +kernel

theorem threshold_6_50 : ∀ i ∈ List.range 1, ThresholdAt 6 (50+i) := by decide +kernel

theorem threshold_6_51 : ∀ i ∈ List.range 1, ThresholdAt 6 (51+i) := by decide +kernel

theorem threshold_6_52 : ∀ i ∈ List.range 1, ThresholdAt 6 (52+i) := by decide +kernel

theorem threshold_6_53 : ∀ i ∈ List.range 1, ThresholdAt 6 (53+i) := by decide +kernel

theorem threshold_6_54 : ∀ i ∈ List.range 1, ThresholdAt 6 (54+i) := by decide +kernel

theorem threshold_6_55 : ∀ i ∈ List.range 1, ThresholdAt 6 (55+i) := by decide +kernel

theorem threshold_6_56 : ∀ i ∈ List.range 1, ThresholdAt 6 (56+i) := by decide +kernel

theorem threshold_6_57 : ∀ i ∈ List.range 1, ThresholdAt 6 (57+i) := by decide +kernel

theorem threshold_6_58 : ∀ i ∈ List.range 1, ThresholdAt 6 (58+i) := by decide +kernel

theorem threshold_6_59 : ∀ i ∈ List.range 1, ThresholdAt 6 (59+i) := by decide +kernel

theorem threshold_6_60 : ∀ i ∈ List.range 1, ThresholdAt 6 (60+i) := by decide +kernel

theorem threshold_6_61 : ∀ i ∈ List.range 1, ThresholdAt 6 (61+i) := by decide +kernel

theorem threshold_6_62 : ∀ i ∈ List.range 1, ThresholdAt 6 (62+i) := by decide +kernel

theorem threshold_6_63 : ∀ i ∈ List.range 1, ThresholdAt 6 (63+i) := by decide +kernel

theorem threshold_6_64 : ∀ i ∈ List.range 1, ThresholdAt 6 (64+i) := by decide +kernel

theorem threshold_6_65 : ∀ i ∈ List.range 1, ThresholdAt 6 (65+i) := by decide +kernel

theorem threshold_6_66 : ∀ i ∈ List.range 1, ThresholdAt 6 (66+i) := by decide +kernel

theorem threshold_6_67 : ∀ i ∈ List.range 1, ThresholdAt 6 (67+i) := by decide +kernel

theorem threshold_6_68 : ∀ i ∈ List.range 1, ThresholdAt 6 (68+i) := by decide +kernel

theorem threshold_6_69 : ∀ i ∈ List.range 1, ThresholdAt 6 (69+i) := by decide +kernel

theorem threshold_6_70 : ∀ i ∈ List.range 1, ThresholdAt 6 (70+i) := by decide +kernel

theorem threshold_6_71 : ∀ i ∈ List.range 1, ThresholdAt 6 (71+i) := by decide +kernel

theorem threshold_6_72 : ∀ i ∈ List.range 1, ThresholdAt 6 (72+i) := by decide +kernel

theorem threshold_6_73 : ∀ i ∈ List.range 1, ThresholdAt 6 (73+i) := by decide +kernel

theorem threshold_6_74 : ∀ i ∈ List.range 1, ThresholdAt 6 (74+i) := by decide +kernel

theorem threshold_6_75 : ∀ i ∈ List.range 1, ThresholdAt 6 (75+i) := by decide +kernel

theorem threshold_6_76 : ∀ i ∈ List.range 1, ThresholdAt 6 (76+i) := by decide +kernel

theorem threshold_6_77 : ∀ i ∈ List.range 1, ThresholdAt 6 (77+i) := by decide +kernel

theorem threshold_6_78 : ∀ i ∈ List.range 1, ThresholdAt 6 (78+i) := by decide +kernel

theorem threshold_6_79 : ∀ i ∈ List.range 1, ThresholdAt 6 (79+i) := by decide +kernel

theorem threshold_6_80 : ∀ i ∈ List.range 1, ThresholdAt 6 (80+i) := by decide +kernel

theorem threshold_6_81 : ∀ i ∈ List.range 1, ThresholdAt 6 (81+i) := by decide +kernel

theorem threshold_6_82 : ∀ i ∈ List.range 1, ThresholdAt 6 (82+i) := by decide +kernel

theorem threshold_6_83 : ∀ i ∈ List.range 1, ThresholdAt 6 (83+i) := by decide +kernel

theorem threshold_6_84 : ∀ i ∈ List.range 1, ThresholdAt 6 (84+i) := by decide +kernel

theorem threshold_6_85 : ∀ i ∈ List.range 1, ThresholdAt 6 (85+i) := by decide +kernel

theorem threshold_6_86 : ∀ i ∈ List.range 1, ThresholdAt 6 (86+i) := by decide +kernel

theorem threshold_6_87 : ∀ i ∈ List.range 1, ThresholdAt 6 (87+i) := by decide +kernel

theorem threshold_6_88 : ∀ i ∈ List.range 1, ThresholdAt 6 (88+i) := by decide +kernel

theorem threshold_6_89 : ∀ i ∈ List.range 1, ThresholdAt 6 (89+i) := by decide +kernel

theorem threshold_6_90 : ∀ i ∈ List.range 1, ThresholdAt 6 (90+i) := by decide +kernel

theorem threshold_6_91 : ∀ i ∈ List.range 1, ThresholdAt 6 (91+i) := by decide +kernel

theorem threshold_6_92 : ∀ i ∈ List.range 1, ThresholdAt 6 (92+i) := by decide +kernel

theorem threshold_6_93 : ∀ i ∈ List.range 1, ThresholdAt 6 (93+i) := by decide +kernel

theorem threshold_6_94 : ∀ i ∈ List.range 1, ThresholdAt 6 (94+i) := by decide +kernel

theorem threshold_6_95 : ∀ i ∈ List.range 1, ThresholdAt 6 (95+i) := by decide +kernel

theorem threshold_6_96 : ∀ i ∈ List.range 1, ThresholdAt 6 (96+i) := by decide +kernel

theorem threshold_6_97 : ∀ i ∈ List.range 1, ThresholdAt 6 (97+i) := by decide +kernel

theorem threshold_6_98 : ∀ i ∈ List.range 1, ThresholdAt 6 (98+i) := by decide +kernel

theorem threshold_6_99 : ∀ i ∈ List.range 1, ThresholdAt 6 (99+i) := by decide +kernel

theorem threshold_6_100 : ∀ i ∈ List.range 1, ThresholdAt 6 (100+i) := by decide +kernel

theorem threshold_6_101 : ∀ i ∈ List.range 1, ThresholdAt 6 (101+i) := by decide +kernel

theorem threshold_6_102 : ∀ i ∈ List.range 1, ThresholdAt 6 (102+i) := by decide +kernel

theorem threshold_6_103 : ∀ i ∈ List.range 1, ThresholdAt 6 (103+i) := by decide +kernel

theorem threshold_6_104 : ∀ i ∈ List.range 1, ThresholdAt 6 (104+i) := by decide +kernel

theorem threshold_6_105 : ∀ i ∈ List.range 1, ThresholdAt 6 (105+i) := by decide +kernel

theorem threshold_6_106 : ∀ i ∈ List.range 1, ThresholdAt 6 (106+i) := by decide +kernel

theorem threshold_6_107 : ∀ i ∈ List.range 1, ThresholdAt 6 (107+i) := by decide +kernel

theorem threshold_6_108 : ∀ i ∈ List.range 1, ThresholdAt 6 (108+i) := by decide +kernel

theorem threshold_6_109 : ∀ i ∈ List.range 1, ThresholdAt 6 (109+i) := by decide +kernel

theorem threshold_6_110 : ∀ i ∈ List.range 1, ThresholdAt 6 (110+i) := by decide +kernel

theorem threshold_6_111 : ∀ i ∈ List.range 1, ThresholdAt 6 (111+i) := by decide +kernel

theorem threshold_6_112 : ∀ i ∈ List.range 1, ThresholdAt 6 (112+i) := by decide +kernel

theorem threshold_6_113 : ∀ i ∈ List.range 1, ThresholdAt 6 (113+i) := by decide +kernel

theorem threshold_6_114 : ∀ i ∈ List.range 1, ThresholdAt 6 (114+i) := by decide +kernel

theorem threshold_6_115 : ∀ i ∈ List.range 1, ThresholdAt 6 (115+i) := by decide +kernel

theorem threshold_6_116 : ∀ i ∈ List.range 1, ThresholdAt 6 (116+i) := by decide +kernel

theorem threshold_6_117 : ∀ i ∈ List.range 1, ThresholdAt 6 (117+i) := by decide +kernel

theorem threshold_6_118 : ∀ i ∈ List.range 1, ThresholdAt 6 (118+i) := by decide +kernel

theorem threshold_6_119 : ∀ i ∈ List.range 1, ThresholdAt 6 (119+i) := by decide +kernel

theorem threshold_6_120 : ∀ i ∈ List.range 1, ThresholdAt 6 (120+i) := by decide +kernel

theorem threshold_6_121 : ∀ i ∈ List.range 1, ThresholdAt 6 (121+i) := by decide +kernel

theorem threshold_6_122 : ∀ i ∈ List.range 1, ThresholdAt 6 (122+i) := by decide +kernel

theorem threshold_6_123 : ∀ i ∈ List.range 1, ThresholdAt 6 (123+i) := by decide +kernel

theorem threshold_6_124 : ∀ i ∈ List.range 1, ThresholdAt 6 (124+i) := by decide +kernel

theorem threshold_6_125 : ∀ i ∈ List.range 1, ThresholdAt 6 (125+i) := by decide +kernel

theorem threshold_6_126 : ∀ i ∈ List.range 1, ThresholdAt 6 (126+i) := by decide +kernel

theorem threshold_6_127 : ∀ i ∈ List.range 1, ThresholdAt 6 (127+i) := by decide +kernel

theorem threshold_6_128 : ∀ i ∈ List.range 1, ThresholdAt 6 (128+i) := by decide +kernel

theorem threshold_6_129 : ∀ i ∈ List.range 1, ThresholdAt 6 (129+i) := by decide +kernel

theorem threshold_6_130 : ∀ i ∈ List.range 1, ThresholdAt 6 (130+i) := by decide +kernel

theorem threshold_6_131 : ∀ i ∈ List.range 1, ThresholdAt 6 (131+i) := by decide +kernel

theorem threshold_6_132 : ∀ i ∈ List.range 1, ThresholdAt 6 (132+i) := by decide +kernel

theorem threshold_6_133 : ∀ i ∈ List.range 1, ThresholdAt 6 (133+i) := by decide +kernel

theorem threshold_6_134 : ∀ i ∈ List.range 1, ThresholdAt 6 (134+i) := by decide +kernel

theorem threshold_6_135 : ∀ i ∈ List.range 1, ThresholdAt 6 (135+i) := by decide +kernel

theorem threshold_6_136 : ∀ i ∈ List.range 1, ThresholdAt 6 (136+i) := by decide +kernel

theorem threshold_6_137 : ∀ i ∈ List.range 1, ThresholdAt 6 (137+i) := by decide +kernel

theorem threshold_6_138 : ∀ i ∈ List.range 1, ThresholdAt 6 (138+i) := by decide +kernel

theorem threshold_6_139 : ∀ i ∈ List.range 1, ThresholdAt 6 (139+i) := by decide +kernel

theorem threshold_6_140 : ∀ i ∈ List.range 1, ThresholdAt 6 (140+i) := by decide +kernel

theorem threshold_6 (v : ℕ) (hv : v ∈ List.range 141) : ThresholdAt 6 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 6 v)
  have h := (join 0 70 71 (join 0 35 35 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_6_0 threshold_6_1) (join 2 1 1 threshold_6_2 threshold_6_3)) (join 4 2 2 (join 4 1 1 threshold_6_4 threshold_6_5) (join 6 1 1 threshold_6_6 threshold_6_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_6_8 threshold_6_9) (join 10 1 1 threshold_6_10 threshold_6_11)) (join 12 2 3 (join 12 1 1 threshold_6_12 threshold_6_13) (join 14 1 2 threshold_6_14 (join 15 1 1 threshold_6_15 threshold_6_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 threshold_6_17 threshold_6_18) (join 19 1 1 threshold_6_19 threshold_6_20)) (join 21 2 3 (join 21 1 1 threshold_6_21 threshold_6_22) (join 23 1 2 threshold_6_23 (join 24 1 1 threshold_6_24 threshold_6_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 threshold_6_26 threshold_6_27) (join 28 1 1 threshold_6_28 threshold_6_29)) (join 30 2 3 (join 30 1 1 threshold_6_30 threshold_6_31) (join 32 1 2 threshold_6_32 (join 33 1 1 threshold_6_33 threshold_6_34)))))) (join 35 17 18 (join 35 8 9 (join 35 4 4 (join 35 2 2 (join 35 1 1 threshold_6_35 threshold_6_36) (join 37 1 1 threshold_6_37 threshold_6_38)) (join 39 2 2 (join 39 1 1 threshold_6_39 threshold_6_40) (join 41 1 1 threshold_6_41 threshold_6_42))) (join 43 4 5 (join 43 2 2 (join 43 1 1 threshold_6_43 threshold_6_44) (join 45 1 1 threshold_6_45 threshold_6_46)) (join 47 2 3 (join 47 1 1 threshold_6_47 threshold_6_48) (join 49 1 2 threshold_6_49 (join 50 1 1 threshold_6_50 threshold_6_51))))) (join 52 9 9 (join 52 4 5 (join 52 2 2 (join 52 1 1 threshold_6_52 threshold_6_53) (join 54 1 1 threshold_6_54 threshold_6_55)) (join 56 2 3 (join 56 1 1 threshold_6_56 threshold_6_57) (join 58 1 2 threshold_6_58 (join 59 1 1 threshold_6_59 threshold_6_60)))) (join 61 4 5 (join 61 2 2 (join 61 1 1 threshold_6_61 threshold_6_62) (join 63 1 1 threshold_6_63 threshold_6_64)) (join 65 2 3 (join 65 1 1 threshold_6_65 threshold_6_66) (join 67 1 2 threshold_6_67 (join 68 1 1 threshold_6_68 threshold_6_69))))))) (join 70 35 36 (join 70 17 18 (join 70 8 9 (join 70 4 4 (join 70 2 2 (join 70 1 1 threshold_6_70 threshold_6_71) (join 72 1 1 threshold_6_72 threshold_6_73)) (join 74 2 2 (join 74 1 1 threshold_6_74 threshold_6_75) (join 76 1 1 threshold_6_76 threshold_6_77))) (join 78 4 5 (join 78 2 2 (join 78 1 1 threshold_6_78 threshold_6_79) (join 80 1 1 threshold_6_80 threshold_6_81)) (join 82 2 3 (join 82 1 1 threshold_6_82 threshold_6_83) (join 84 1 2 threshold_6_84 (join 85 1 1 threshold_6_85 threshold_6_86))))) (join 87 9 9 (join 87 4 5 (join 87 2 2 (join 87 1 1 threshold_6_87 threshold_6_88) (join 89 1 1 threshold_6_89 threshold_6_90)) (join 91 2 3 (join 91 1 1 threshold_6_91 threshold_6_92) (join 93 1 2 threshold_6_93 (join 94 1 1 threshold_6_94 threshold_6_95)))) (join 96 4 5 (join 96 2 2 (join 96 1 1 threshold_6_96 threshold_6_97) (join 98 1 1 threshold_6_98 threshold_6_99)) (join 100 2 3 (join 100 1 1 threshold_6_100 threshold_6_101) (join 102 1 2 threshold_6_102 (join 103 1 1 threshold_6_103 threshold_6_104)))))) (join 105 18 18 (join 105 9 9 (join 105 4 5 (join 105 2 2 (join 105 1 1 threshold_6_105 threshold_6_106) (join 107 1 1 threshold_6_107 threshold_6_108)) (join 109 2 3 (join 109 1 1 threshold_6_109 threshold_6_110) (join 111 1 2 threshold_6_111 (join 112 1 1 threshold_6_112 threshold_6_113)))) (join 114 4 5 (join 114 2 2 (join 114 1 1 threshold_6_114 threshold_6_115) (join 116 1 1 threshold_6_116 threshold_6_117)) (join 118 2 3 (join 118 1 1 threshold_6_118 threshold_6_119) (join 120 1 2 threshold_6_120 (join 121 1 1 threshold_6_121 threshold_6_122))))) (join 123 9 9 (join 123 4 5 (join 123 2 2 (join 123 1 1 threshold_6_123 threshold_6_124) (join 125 1 1 threshold_6_125 threshold_6_126)) (join 127 2 3 (join 127 1 1 threshold_6_127 threshold_6_128) (join 129 1 2 threshold_6_129 (join 130 1 1 threshold_6_130 threshold_6_131)))) (join 132 4 5 (join 132 2 2 (join 132 1 1 threshold_6_132 threshold_6_133) (join 134 1 1 threshold_6_134 threshold_6_135)) (join 136 2 3 (join 136 1 1 threshold_6_136 threshold_6_137) (join 138 1 2 threshold_6_138 (join 139 1 1 threshold_6_139 threshold_6_140))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_6_0 : ∀ i ∈ List.range 4, LedgerAt 6 (0+i) := by decide +kernel

theorem ledger_6_4 : ∀ i ∈ List.range 4, LedgerAt 6 (4+i) := by decide +kernel

theorem ledger_6_8 : ∀ i ∈ List.range 4, LedgerAt 6 (8+i) := by decide +kernel

theorem ledger_6_12 : ∀ i ∈ List.range 4, LedgerAt 6 (12+i) := by decide +kernel

theorem ledger_6_16 : ∀ i ∈ List.range 4, LedgerAt 6 (16+i) := by decide +kernel

theorem ledger_6_20 : ∀ i ∈ List.range 4, LedgerAt 6 (20+i) := by decide +kernel

theorem ledger_6_24 : ∀ i ∈ List.range 4, LedgerAt 6 (24+i) := by decide +kernel

theorem ledger_6_28 : ∀ i ∈ List.range 4, LedgerAt 6 (28+i) := by decide +kernel

theorem ledger_6_32 : ∀ i ∈ List.range 4, LedgerAt 6 (32+i) := by decide +kernel

theorem ledger_6_36 : ∀ i ∈ List.range 4, LedgerAt 6 (36+i) := by decide +kernel

theorem ledger_6_40 : ∀ i ∈ List.range 4, LedgerAt 6 (40+i) := by decide +kernel

theorem ledger_6_44 : ∀ i ∈ List.range 4, LedgerAt 6 (44+i) := by decide +kernel

theorem ledger_6_48 : ∀ i ∈ List.range 4, LedgerAt 6 (48+i) := by decide +kernel

theorem ledger_6_52 : ∀ i ∈ List.range 4, LedgerAt 6 (52+i) := by decide +kernel

theorem ledger_6_56 : ∀ i ∈ List.range 4, LedgerAt 6 (56+i) := by decide +kernel

theorem ledger_6_60 : ∀ i ∈ List.range 4, LedgerAt 6 (60+i) := by decide +kernel

theorem ledger_6_64 : ∀ i ∈ List.range 4, LedgerAt 6 (64+i) := by decide +kernel

theorem ledger_6_68 : ∀ i ∈ List.range 4, LedgerAt 6 (68+i) := by decide +kernel

theorem ledger_6_72 : ∀ i ∈ List.range 4, LedgerAt 6 (72+i) := by decide +kernel

theorem ledger_6_76 : ∀ i ∈ List.range 4, LedgerAt 6 (76+i) := by decide +kernel

theorem ledger_6_80 : ∀ i ∈ List.range 4, LedgerAt 6 (80+i) := by decide +kernel

theorem ledger_6_84 : ∀ i ∈ List.range 4, LedgerAt 6 (84+i) := by decide +kernel

theorem ledger_6_88 : ∀ i ∈ List.range 4, LedgerAt 6 (88+i) := by decide +kernel

theorem ledger_6_92 : ∀ i ∈ List.range 4, LedgerAt 6 (92+i) := by decide +kernel

theorem ledger_6_96 : ∀ i ∈ List.range 4, LedgerAt 6 (96+i) := by decide +kernel

theorem ledger_6_100 : ∀ i ∈ List.range 4, LedgerAt 6 (100+i) := by decide +kernel

theorem ledger_6_104 : ∀ i ∈ List.range 4, LedgerAt 6 (104+i) := by decide +kernel

theorem ledger_6_108 : ∀ i ∈ List.range 4, LedgerAt 6 (108+i) := by decide +kernel

theorem ledger_6_112 : ∀ i ∈ List.range 4, LedgerAt 6 (112+i) := by decide +kernel

theorem ledger_6_116 : ∀ i ∈ List.range 4, LedgerAt 6 (116+i) := by decide +kernel

theorem ledger_6_120 : ∀ i ∈ List.range 4, LedgerAt 6 (120+i) := by decide +kernel

theorem ledger_6_124 : ∀ i ∈ List.range 4, LedgerAt 6 (124+i) := by decide +kernel

theorem ledger_6_128 : ∀ i ∈ List.range 4, LedgerAt 6 (128+i) := by decide +kernel

theorem ledger_6_132 : ∀ i ∈ List.range 4, LedgerAt 6 (132+i) := by decide +kernel

theorem ledger_6_136 : ∀ i ∈ List.range 4, LedgerAt 6 (136+i) := by decide +kernel

theorem ledger_6_140 : ∀ i ∈ List.range 1, LedgerAt 6 (140+i) := by decide +kernel

theorem ledger_6 (v : ℕ) (hv : v ∈ List.range 141) : LedgerAt 6 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 6 v)
  have h := (join 0 72 69 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_6_0 ledger_6_4) (join 8 4 4 ledger_6_8 ledger_6_12)) (join 16 8 12 (join 16 4 4 ledger_6_16 ledger_6_20) (join 24 4 8 ledger_6_24 (join 28 4 4 ledger_6_28 ledger_6_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_6_36 ledger_6_40) (join 44 4 4 ledger_6_44 ledger_6_48)) (join 52 8 12 (join 52 4 4 ledger_6_52 ledger_6_56) (join 60 4 8 ledger_6_60 (join 64 4 4 ledger_6_64 ledger_6_68))))) (join 72 36 33 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_6_72 ledger_6_76) (join 80 4 4 ledger_6_80 ledger_6_84)) (join 88 8 12 (join 88 4 4 ledger_6_88 ledger_6_92) (join 96 4 8 ledger_6_96 (join 100 4 4 ledger_6_100 ledger_6_104)))) (join 108 16 17 (join 108 8 8 (join 108 4 4 ledger_6_108 ledger_6_112) (join 116 4 4 ledger_6_116 ledger_6_120)) (join 124 8 9 (join 124 4 4 ledger_6_124 ledger_6_128) (join 132 4 5 ledger_6_132 (join 136 4 1 ledger_6_136 ledger_6_140))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
