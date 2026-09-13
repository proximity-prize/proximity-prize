import ProximityPrize.SubmissionLower.BoundaryTailCheckedR036807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_4_0 : ∀ i ∈ List.range 4, GeometryAt 4 (0+i) := by decide +kernel

theorem geometry_4_4 : ∀ i ∈ List.range 4, GeometryAt 4 (4+i) := by decide +kernel

theorem geometry_4_8 : ∀ i ∈ List.range 4, GeometryAt 4 (8+i) := by decide +kernel

theorem geometry_4_12 : ∀ i ∈ List.range 4, GeometryAt 4 (12+i) := by decide +kernel

theorem geometry_4_16 : ∀ i ∈ List.range 4, GeometryAt 4 (16+i) := by decide +kernel

theorem geometry_4_20 : ∀ i ∈ List.range 4, GeometryAt 4 (20+i) := by decide +kernel

theorem geometry_4_24 : ∀ i ∈ List.range 4, GeometryAt 4 (24+i) := by decide +kernel

theorem geometry_4_28 : ∀ i ∈ List.range 4, GeometryAt 4 (28+i) := by decide +kernel

theorem geometry_4_32 : ∀ i ∈ List.range 4, GeometryAt 4 (32+i) := by decide +kernel

theorem geometry_4_36 : ∀ i ∈ List.range 4, GeometryAt 4 (36+i) := by decide +kernel

theorem geometry_4_40 : ∀ i ∈ List.range 4, GeometryAt 4 (40+i) := by decide +kernel

theorem geometry_4_44 : ∀ i ∈ List.range 4, GeometryAt 4 (44+i) := by decide +kernel

theorem geometry_4_48 : ∀ i ∈ List.range 4, GeometryAt 4 (48+i) := by decide +kernel

theorem geometry_4_52 : ∀ i ∈ List.range 4, GeometryAt 4 (52+i) := by decide +kernel

theorem geometry_4_56 : ∀ i ∈ List.range 4, GeometryAt 4 (56+i) := by decide +kernel

theorem geometry_4_60 : ∀ i ∈ List.range 4, GeometryAt 4 (60+i) := by decide +kernel

theorem geometry_4_64 : ∀ i ∈ List.range 4, GeometryAt 4 (64+i) := by decide +kernel

theorem geometry_4_68 : ∀ i ∈ List.range 4, GeometryAt 4 (68+i) := by decide +kernel

theorem geometry_4_72 : ∀ i ∈ List.range 4, GeometryAt 4 (72+i) := by decide +kernel

theorem geometry_4_76 : ∀ i ∈ List.range 4, GeometryAt 4 (76+i) := by decide +kernel

theorem geometry_4_80 : ∀ i ∈ List.range 4, GeometryAt 4 (80+i) := by decide +kernel

theorem geometry_4_84 : ∀ i ∈ List.range 4, GeometryAt 4 (84+i) := by decide +kernel

theorem geometry_4_88 : ∀ i ∈ List.range 4, GeometryAt 4 (88+i) := by decide +kernel

theorem geometry_4_92 : ∀ i ∈ List.range 4, GeometryAt 4 (92+i) := by decide +kernel

theorem geometry_4_96 : ∀ i ∈ List.range 4, GeometryAt 4 (96+i) := by decide +kernel

theorem geometry_4_100 : ∀ i ∈ List.range 4, GeometryAt 4 (100+i) := by decide +kernel

theorem geometry_4_104 : ∀ i ∈ List.range 4, GeometryAt 4 (104+i) := by decide +kernel

theorem geometry_4_108 : ∀ i ∈ List.range 4, GeometryAt 4 (108+i) := by decide +kernel

theorem geometry_4_112 : ∀ i ∈ List.range 4, GeometryAt 4 (112+i) := by decide +kernel

theorem geometry_4_116 : ∀ i ∈ List.range 4, GeometryAt 4 (116+i) := by decide +kernel

theorem geometry_4_120 : ∀ i ∈ List.range 4, GeometryAt 4 (120+i) := by decide +kernel

theorem geometry_4_124 : ∀ i ∈ List.range 4, GeometryAt 4 (124+i) := by decide +kernel

theorem geometry_4_128 : ∀ i ∈ List.range 4, GeometryAt 4 (128+i) := by decide +kernel

theorem geometry_4_132 : ∀ i ∈ List.range 4, GeometryAt 4 (132+i) := by decide +kernel

theorem geometry_4_136 : ∀ i ∈ List.range 4, GeometryAt 4 (136+i) := by decide +kernel

theorem geometry_4_140 : ∀ i ∈ List.range 3, GeometryAt 4 (140+i) := by decide +kernel

theorem geometry_4 (v : ℕ) (hv : v ∈ List.range 143) : GeometryAt 4 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 4 v)
  have h := (join 0 72 71 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 geometry_4_0 geometry_4_4) (join 8 4 4 geometry_4_8 geometry_4_12)) (join 16 8 12 (join 16 4 4 geometry_4_16 geometry_4_20) (join 24 4 8 geometry_4_24 (join 28 4 4 geometry_4_28 geometry_4_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 geometry_4_36 geometry_4_40) (join 44 4 4 geometry_4_44 geometry_4_48)) (join 52 8 12 (join 52 4 4 geometry_4_52 geometry_4_56) (join 60 4 8 geometry_4_60 (join 64 4 4 geometry_4_64 geometry_4_68))))) (join 72 36 35 (join 72 16 20 (join 72 8 8 (join 72 4 4 geometry_4_72 geometry_4_76) (join 80 4 4 geometry_4_80 geometry_4_84)) (join 88 8 12 (join 88 4 4 geometry_4_88 geometry_4_92) (join 96 4 8 geometry_4_96 (join 100 4 4 geometry_4_100 geometry_4_104)))) (join 108 16 19 (join 108 8 8 (join 108 4 4 geometry_4_108 geometry_4_112) (join 116 4 4 geometry_4_116 geometry_4_120)) (join 124 8 11 (join 124 4 4 geometry_4_124 geometry_4_128) (join 132 4 7 geometry_4_132 (join 136 4 3 geometry_4_136 geometry_4_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_4_0 : ∀ i ∈ List.range 1, StrictAt 4 (0+i) := by decide +kernel

theorem strict_4_1 : ∀ i ∈ List.range 1, StrictAt 4 (1+i) := by decide +kernel

theorem strict_4_2 : ∀ i ∈ List.range 1, StrictAt 4 (2+i) := by decide +kernel

theorem strict_4_3 : ∀ i ∈ List.range 1, StrictAt 4 (3+i) := by decide +kernel

theorem strict_4_4 : ∀ i ∈ List.range 1, StrictAt 4 (4+i) := by decide +kernel

theorem strict_4_5 : ∀ i ∈ List.range 1, StrictAt 4 (5+i) := by decide +kernel

theorem strict_4_6 : ∀ i ∈ List.range 1, StrictAt 4 (6+i) := by decide +kernel

theorem strict_4_7 : ∀ i ∈ List.range 1, StrictAt 4 (7+i) := by decide +kernel

theorem strict_4_8 : ∀ i ∈ List.range 1, StrictAt 4 (8+i) := by decide +kernel

theorem strict_4_9 : ∀ i ∈ List.range 1, StrictAt 4 (9+i) := by decide +kernel

theorem strict_4_10 : ∀ i ∈ List.range 1, StrictAt 4 (10+i) := by decide +kernel

theorem strict_4_11 : ∀ i ∈ List.range 1, StrictAt 4 (11+i) := by decide +kernel

theorem strict_4_12 : ∀ i ∈ List.range 1, StrictAt 4 (12+i) := by decide +kernel

theorem strict_4_13 : ∀ i ∈ List.range 1, StrictAt 4 (13+i) := by decide +kernel

theorem strict_4_14 : ∀ i ∈ List.range 1, StrictAt 4 (14+i) := by decide +kernel

theorem strict_4_15 : ∀ i ∈ List.range 1, StrictAt 4 (15+i) := by decide +kernel

theorem strict_4_16 : ∀ i ∈ List.range 1, StrictAt 4 (16+i) := by decide +kernel

theorem strict_4_17 : ∀ i ∈ List.range 1, StrictAt 4 (17+i) := by decide +kernel

theorem strict_4_18 : ∀ i ∈ List.range 1, StrictAt 4 (18+i) := by decide +kernel

theorem strict_4_19 : ∀ i ∈ List.range 1, StrictAt 4 (19+i) := by decide +kernel

theorem strict_4_20 : ∀ i ∈ List.range 1, StrictAt 4 (20+i) := by decide +kernel

theorem strict_4_21 : ∀ i ∈ List.range 1, StrictAt 4 (21+i) := by decide +kernel

theorem strict_4_22 : ∀ i ∈ List.range 1, StrictAt 4 (22+i) := by decide +kernel

theorem strict_4_23 : ∀ i ∈ List.range 1, StrictAt 4 (23+i) := by decide +kernel

theorem strict_4_24 : ∀ i ∈ List.range 1, StrictAt 4 (24+i) := by decide +kernel

theorem strict_4_25 : ∀ i ∈ List.range 1, StrictAt 4 (25+i) := by decide +kernel

theorem strict_4_26 : ∀ i ∈ List.range 1, StrictAt 4 (26+i) := by decide +kernel

theorem strict_4_27 : ∀ i ∈ List.range 1, StrictAt 4 (27+i) := by decide +kernel

theorem strict_4_28 : ∀ i ∈ List.range 1, StrictAt 4 (28+i) := by decide +kernel

theorem strict_4_29 : ∀ i ∈ List.range 1, StrictAt 4 (29+i) := by decide +kernel

theorem strict_4_30 : ∀ i ∈ List.range 1, StrictAt 4 (30+i) := by decide +kernel

theorem strict_4_31 : ∀ i ∈ List.range 1, StrictAt 4 (31+i) := by decide +kernel

theorem strict_4_32 : ∀ i ∈ List.range 1, StrictAt 4 (32+i) := by decide +kernel

theorem strict_4_33 : ∀ i ∈ List.range 1, StrictAt 4 (33+i) := by decide +kernel

theorem strict_4_34 : ∀ i ∈ List.range 1, StrictAt 4 (34+i) := by decide +kernel

theorem strict_4_35 : ∀ i ∈ List.range 1, StrictAt 4 (35+i) := by decide +kernel

theorem strict_4_36 : ∀ i ∈ List.range 1, StrictAt 4 (36+i) := by decide +kernel

theorem strict_4_37 : ∀ i ∈ List.range 1, StrictAt 4 (37+i) := by decide +kernel

theorem strict_4_38 : ∀ i ∈ List.range 1, StrictAt 4 (38+i) := by decide +kernel

theorem strict_4_39 : ∀ i ∈ List.range 1, StrictAt 4 (39+i) := by decide +kernel

theorem strict_4_40 : ∀ i ∈ List.range 1, StrictAt 4 (40+i) := by decide +kernel

theorem strict_4_41 : ∀ i ∈ List.range 1, StrictAt 4 (41+i) := by decide +kernel

theorem strict_4_42 : ∀ i ∈ List.range 1, StrictAt 4 (42+i) := by decide +kernel

theorem strict_4_43 : ∀ i ∈ List.range 1, StrictAt 4 (43+i) := by decide +kernel

theorem strict_4_44 : ∀ i ∈ List.range 1, StrictAt 4 (44+i) := by decide +kernel

theorem strict_4_45 : ∀ i ∈ List.range 1, StrictAt 4 (45+i) := by decide +kernel

theorem strict_4_46 : ∀ i ∈ List.range 1, StrictAt 4 (46+i) := by decide +kernel

theorem strict_4_47 : ∀ i ∈ List.range 1, StrictAt 4 (47+i) := by decide +kernel

theorem strict_4_48 : ∀ i ∈ List.range 1, StrictAt 4 (48+i) := by decide +kernel

theorem strict_4_49 : ∀ i ∈ List.range 1, StrictAt 4 (49+i) := by decide +kernel

theorem strict_4_50 : ∀ i ∈ List.range 1, StrictAt 4 (50+i) := by decide +kernel

theorem strict_4_51 : ∀ i ∈ List.range 1, StrictAt 4 (51+i) := by decide +kernel

theorem strict_4_52 : ∀ i ∈ List.range 1, StrictAt 4 (52+i) := by decide +kernel

theorem strict_4_53 : ∀ i ∈ List.range 1, StrictAt 4 (53+i) := by decide +kernel

theorem strict_4_54 : ∀ i ∈ List.range 1, StrictAt 4 (54+i) := by decide +kernel

theorem strict_4_55 : ∀ i ∈ List.range 1, StrictAt 4 (55+i) := by decide +kernel

theorem strict_4_56 : ∀ i ∈ List.range 1, StrictAt 4 (56+i) := by decide +kernel

theorem strict_4_57 : ∀ i ∈ List.range 1, StrictAt 4 (57+i) := by decide +kernel

theorem strict_4_58 : ∀ i ∈ List.range 1, StrictAt 4 (58+i) := by decide +kernel

theorem strict_4_59 : ∀ i ∈ List.range 1, StrictAt 4 (59+i) := by decide +kernel

theorem strict_4_60 : ∀ i ∈ List.range 1, StrictAt 4 (60+i) := by decide +kernel

theorem strict_4_61 : ∀ i ∈ List.range 1, StrictAt 4 (61+i) := by decide +kernel

theorem strict_4_62 : ∀ i ∈ List.range 1, StrictAt 4 (62+i) := by decide +kernel

theorem strict_4_63 : ∀ i ∈ List.range 1, StrictAt 4 (63+i) := by decide +kernel

theorem strict_4_64 : ∀ i ∈ List.range 1, StrictAt 4 (64+i) := by decide +kernel

theorem strict_4_65 : ∀ i ∈ List.range 1, StrictAt 4 (65+i) := by decide +kernel

theorem strict_4_66 : ∀ i ∈ List.range 1, StrictAt 4 (66+i) := by decide +kernel

theorem strict_4_67 : ∀ i ∈ List.range 1, StrictAt 4 (67+i) := by decide +kernel

theorem strict_4_68 : ∀ i ∈ List.range 1, StrictAt 4 (68+i) := by decide +kernel

theorem strict_4_69 : ∀ i ∈ List.range 1, StrictAt 4 (69+i) := by decide +kernel

theorem strict_4_70 : ∀ i ∈ List.range 1, StrictAt 4 (70+i) := by decide +kernel

theorem strict_4_71 : ∀ i ∈ List.range 1, StrictAt 4 (71+i) := by decide +kernel

theorem strict_4_72 : ∀ i ∈ List.range 1, StrictAt 4 (72+i) := by decide +kernel

theorem strict_4_73 : ∀ i ∈ List.range 1, StrictAt 4 (73+i) := by decide +kernel

theorem strict_4_74 : ∀ i ∈ List.range 1, StrictAt 4 (74+i) := by decide +kernel

theorem strict_4_75 : ∀ i ∈ List.range 1, StrictAt 4 (75+i) := by decide +kernel

theorem strict_4_76 : ∀ i ∈ List.range 1, StrictAt 4 (76+i) := by decide +kernel

theorem strict_4_77 : ∀ i ∈ List.range 1, StrictAt 4 (77+i) := by decide +kernel

theorem strict_4_78 : ∀ i ∈ List.range 1, StrictAt 4 (78+i) := by decide +kernel

theorem strict_4_79 : ∀ i ∈ List.range 1, StrictAt 4 (79+i) := by decide +kernel

theorem strict_4_80 : ∀ i ∈ List.range 1, StrictAt 4 (80+i) := by decide +kernel

theorem strict_4_81 : ∀ i ∈ List.range 1, StrictAt 4 (81+i) := by decide +kernel

theorem strict_4_82 : ∀ i ∈ List.range 1, StrictAt 4 (82+i) := by decide +kernel

theorem strict_4_83 : ∀ i ∈ List.range 1, StrictAt 4 (83+i) := by decide +kernel

theorem strict_4_84 : ∀ i ∈ List.range 1, StrictAt 4 (84+i) := by decide +kernel

theorem strict_4_85 : ∀ i ∈ List.range 1, StrictAt 4 (85+i) := by decide +kernel

theorem strict_4_86 : ∀ i ∈ List.range 1, StrictAt 4 (86+i) := by decide +kernel

theorem strict_4_87 : ∀ i ∈ List.range 1, StrictAt 4 (87+i) := by decide +kernel

theorem strict_4_88 : ∀ i ∈ List.range 1, StrictAt 4 (88+i) := by decide +kernel

theorem strict_4_89 : ∀ i ∈ List.range 1, StrictAt 4 (89+i) := by decide +kernel

theorem strict_4_90 : ∀ i ∈ List.range 1, StrictAt 4 (90+i) := by decide +kernel

theorem strict_4_91 : ∀ i ∈ List.range 1, StrictAt 4 (91+i) := by decide +kernel

theorem strict_4_92 : ∀ i ∈ List.range 1, StrictAt 4 (92+i) := by decide +kernel

theorem strict_4_93 : ∀ i ∈ List.range 1, StrictAt 4 (93+i) := by decide +kernel

theorem strict_4_94 : ∀ i ∈ List.range 1, StrictAt 4 (94+i) := by decide +kernel

theorem strict_4_95 : ∀ i ∈ List.range 1, StrictAt 4 (95+i) := by decide +kernel

theorem strict_4_96 : ∀ i ∈ List.range 1, StrictAt 4 (96+i) := by decide +kernel

theorem strict_4_97 : ∀ i ∈ List.range 1, StrictAt 4 (97+i) := by decide +kernel

theorem strict_4_98 : ∀ i ∈ List.range 1, StrictAt 4 (98+i) := by decide +kernel

theorem strict_4_99 : ∀ i ∈ List.range 1, StrictAt 4 (99+i) := by decide +kernel

theorem strict_4_100 : ∀ i ∈ List.range 1, StrictAt 4 (100+i) := by decide +kernel

theorem strict_4_101 : ∀ i ∈ List.range 1, StrictAt 4 (101+i) := by decide +kernel

theorem strict_4_102 : ∀ i ∈ List.range 1, StrictAt 4 (102+i) := by decide +kernel

theorem strict_4_103 : ∀ i ∈ List.range 1, StrictAt 4 (103+i) := by decide +kernel

theorem strict_4_104 : ∀ i ∈ List.range 1, StrictAt 4 (104+i) := by decide +kernel

theorem strict_4_105 : ∀ i ∈ List.range 1, StrictAt 4 (105+i) := by decide +kernel

theorem strict_4_106 : ∀ i ∈ List.range 1, StrictAt 4 (106+i) := by decide +kernel

theorem strict_4_107 : ∀ i ∈ List.range 1, StrictAt 4 (107+i) := by decide +kernel

theorem strict_4_108 : ∀ i ∈ List.range 1, StrictAt 4 (108+i) := by decide +kernel

theorem strict_4_109 : ∀ i ∈ List.range 1, StrictAt 4 (109+i) := by decide +kernel

theorem strict_4_110 : ∀ i ∈ List.range 1, StrictAt 4 (110+i) := by decide +kernel

theorem strict_4_111 : ∀ i ∈ List.range 1, StrictAt 4 (111+i) := by decide +kernel

theorem strict_4_112 : ∀ i ∈ List.range 1, StrictAt 4 (112+i) := by decide +kernel

theorem strict_4_113 : ∀ i ∈ List.range 1, StrictAt 4 (113+i) := by decide +kernel

theorem strict_4_114 : ∀ i ∈ List.range 1, StrictAt 4 (114+i) := by decide +kernel

theorem strict_4_115 : ∀ i ∈ List.range 1, StrictAt 4 (115+i) := by decide +kernel

theorem strict_4_116 : ∀ i ∈ List.range 1, StrictAt 4 (116+i) := by decide +kernel

theorem strict_4_117 : ∀ i ∈ List.range 1, StrictAt 4 (117+i) := by decide +kernel

theorem strict_4_118 : ∀ i ∈ List.range 1, StrictAt 4 (118+i) := by decide +kernel

theorem strict_4_119 : ∀ i ∈ List.range 1, StrictAt 4 (119+i) := by decide +kernel

theorem strict_4_120 : ∀ i ∈ List.range 1, StrictAt 4 (120+i) := by decide +kernel

theorem strict_4_121 : ∀ i ∈ List.range 1, StrictAt 4 (121+i) := by decide +kernel

theorem strict_4_122 : ∀ i ∈ List.range 1, StrictAt 4 (122+i) := by decide +kernel

theorem strict_4_123 : ∀ i ∈ List.range 1, StrictAt 4 (123+i) := by decide +kernel

theorem strict_4_124 : ∀ i ∈ List.range 1, StrictAt 4 (124+i) := by decide +kernel

theorem strict_4_125 : ∀ i ∈ List.range 1, StrictAt 4 (125+i) := by decide +kernel

theorem strict_4_126 : ∀ i ∈ List.range 1, StrictAt 4 (126+i) := by decide +kernel

theorem strict_4_127 : ∀ i ∈ List.range 1, StrictAt 4 (127+i) := by decide +kernel

theorem strict_4_128 : ∀ i ∈ List.range 1, StrictAt 4 (128+i) := by decide +kernel

theorem strict_4_129 : ∀ i ∈ List.range 1, StrictAt 4 (129+i) := by decide +kernel

theorem strict_4_130 : ∀ i ∈ List.range 1, StrictAt 4 (130+i) := by decide +kernel

theorem strict_4_131 : ∀ i ∈ List.range 1, StrictAt 4 (131+i) := by decide +kernel

theorem strict_4_132 : ∀ i ∈ List.range 1, StrictAt 4 (132+i) := by decide +kernel

theorem strict_4_133 : ∀ i ∈ List.range 1, StrictAt 4 (133+i) := by decide +kernel

theorem strict_4_134 : ∀ i ∈ List.range 1, StrictAt 4 (134+i) := by decide +kernel

theorem strict_4_135 : ∀ i ∈ List.range 1, StrictAt 4 (135+i) := by decide +kernel

theorem strict_4_136 : ∀ i ∈ List.range 1, StrictAt 4 (136+i) := by decide +kernel

theorem strict_4_137 : ∀ i ∈ List.range 1, StrictAt 4 (137+i) := by decide +kernel

theorem strict_4_138 : ∀ i ∈ List.range 1, StrictAt 4 (138+i) := by decide +kernel

theorem strict_4_139 : ∀ i ∈ List.range 1, StrictAt 4 (139+i) := by decide +kernel

theorem strict_4_140 : ∀ i ∈ List.range 1, StrictAt 4 (140+i) := by decide +kernel

theorem strict_4_141 : ∀ i ∈ List.range 1, StrictAt 4 (141+i) := by decide +kernel

theorem strict_4_142 : ∀ i ∈ List.range 1, StrictAt 4 (142+i) := by decide +kernel

theorem strict_4 (v : ℕ) (hv : v ∈ List.range 143) : StrictAt 4 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 4 v)
  have h := (join 0 71 72 (join 0 35 36 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 strict_4_0 strict_4_1) (join 2 1 1 strict_4_2 strict_4_3)) (join 4 2 2 (join 4 1 1 strict_4_4 strict_4_5) (join 6 1 1 strict_4_6 strict_4_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 strict_4_8 strict_4_9) (join 10 1 1 strict_4_10 strict_4_11)) (join 12 2 3 (join 12 1 1 strict_4_12 strict_4_13) (join 14 1 2 strict_4_14 (join 15 1 1 strict_4_15 strict_4_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 strict_4_17 strict_4_18) (join 19 1 1 strict_4_19 strict_4_20)) (join 21 2 3 (join 21 1 1 strict_4_21 strict_4_22) (join 23 1 2 strict_4_23 (join 24 1 1 strict_4_24 strict_4_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 strict_4_26 strict_4_27) (join 28 1 1 strict_4_28 strict_4_29)) (join 30 2 3 (join 30 1 1 strict_4_30 strict_4_31) (join 32 1 2 strict_4_32 (join 33 1 1 strict_4_33 strict_4_34)))))) (join 35 18 18 (join 35 9 9 (join 35 4 5 (join 35 2 2 (join 35 1 1 strict_4_35 strict_4_36) (join 37 1 1 strict_4_37 strict_4_38)) (join 39 2 3 (join 39 1 1 strict_4_39 strict_4_40) (join 41 1 2 strict_4_41 (join 42 1 1 strict_4_42 strict_4_43)))) (join 44 4 5 (join 44 2 2 (join 44 1 1 strict_4_44 strict_4_45) (join 46 1 1 strict_4_46 strict_4_47)) (join 48 2 3 (join 48 1 1 strict_4_48 strict_4_49) (join 50 1 2 strict_4_50 (join 51 1 1 strict_4_51 strict_4_52))))) (join 53 9 9 (join 53 4 5 (join 53 2 2 (join 53 1 1 strict_4_53 strict_4_54) (join 55 1 1 strict_4_55 strict_4_56)) (join 57 2 3 (join 57 1 1 strict_4_57 strict_4_58) (join 59 1 2 strict_4_59 (join 60 1 1 strict_4_60 strict_4_61)))) (join 62 4 5 (join 62 2 2 (join 62 1 1 strict_4_62 strict_4_63) (join 64 1 1 strict_4_64 strict_4_65)) (join 66 2 3 (join 66 1 1 strict_4_66 strict_4_67) (join 68 1 2 strict_4_68 (join 69 1 1 strict_4_69 strict_4_70))))))) (join 71 36 36 (join 71 18 18 (join 71 9 9 (join 71 4 5 (join 71 2 2 (join 71 1 1 strict_4_71 strict_4_72) (join 73 1 1 strict_4_73 strict_4_74)) (join 75 2 3 (join 75 1 1 strict_4_75 strict_4_76) (join 77 1 2 strict_4_77 (join 78 1 1 strict_4_78 strict_4_79)))) (join 80 4 5 (join 80 2 2 (join 80 1 1 strict_4_80 strict_4_81) (join 82 1 1 strict_4_82 strict_4_83)) (join 84 2 3 (join 84 1 1 strict_4_84 strict_4_85) (join 86 1 2 strict_4_86 (join 87 1 1 strict_4_87 strict_4_88))))) (join 89 9 9 (join 89 4 5 (join 89 2 2 (join 89 1 1 strict_4_89 strict_4_90) (join 91 1 1 strict_4_91 strict_4_92)) (join 93 2 3 (join 93 1 1 strict_4_93 strict_4_94) (join 95 1 2 strict_4_95 (join 96 1 1 strict_4_96 strict_4_97)))) (join 98 4 5 (join 98 2 2 (join 98 1 1 strict_4_98 strict_4_99) (join 100 1 1 strict_4_100 strict_4_101)) (join 102 2 3 (join 102 1 1 strict_4_102 strict_4_103) (join 104 1 2 strict_4_104 (join 105 1 1 strict_4_105 strict_4_106)))))) (join 107 18 18 (join 107 9 9 (join 107 4 5 (join 107 2 2 (join 107 1 1 strict_4_107 strict_4_108) (join 109 1 1 strict_4_109 strict_4_110)) (join 111 2 3 (join 111 1 1 strict_4_111 strict_4_112) (join 113 1 2 strict_4_113 (join 114 1 1 strict_4_114 strict_4_115)))) (join 116 4 5 (join 116 2 2 (join 116 1 1 strict_4_116 strict_4_117) (join 118 1 1 strict_4_118 strict_4_119)) (join 120 2 3 (join 120 1 1 strict_4_120 strict_4_121) (join 122 1 2 strict_4_122 (join 123 1 1 strict_4_123 strict_4_124))))) (join 125 9 9 (join 125 4 5 (join 125 2 2 (join 125 1 1 strict_4_125 strict_4_126) (join 127 1 1 strict_4_127 strict_4_128)) (join 129 2 3 (join 129 1 1 strict_4_129 strict_4_130) (join 131 1 2 strict_4_131 (join 132 1 1 strict_4_132 strict_4_133)))) (join 134 4 5 (join 134 2 2 (join 134 1 1 strict_4_134 strict_4_135) (join 136 1 1 strict_4_136 strict_4_137)) (join 138 2 3 (join 138 1 1 strict_4_138 strict_4_139) (join 140 1 2 strict_4_140 (join 141 1 1 strict_4_141 strict_4_142))))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_4_0 : ∀ i ∈ List.range 4, PhaseAt 4 (0+i) := by decide +kernel

theorem phase_4_4 : ∀ i ∈ List.range 4, PhaseAt 4 (4+i) := by decide +kernel

theorem phase_4_8 : ∀ i ∈ List.range 4, PhaseAt 4 (8+i) := by decide +kernel

theorem phase_4_12 : ∀ i ∈ List.range 4, PhaseAt 4 (12+i) := by decide +kernel

theorem phase_4_16 : ∀ i ∈ List.range 4, PhaseAt 4 (16+i) := by decide +kernel

theorem phase_4_20 : ∀ i ∈ List.range 4, PhaseAt 4 (20+i) := by decide +kernel

theorem phase_4_24 : ∀ i ∈ List.range 4, PhaseAt 4 (24+i) := by decide +kernel

theorem phase_4_28 : ∀ i ∈ List.range 4, PhaseAt 4 (28+i) := by decide +kernel

theorem phase_4_32 : ∀ i ∈ List.range 4, PhaseAt 4 (32+i) := by decide +kernel

theorem phase_4_36 : ∀ i ∈ List.range 4, PhaseAt 4 (36+i) := by decide +kernel

theorem phase_4_40 : ∀ i ∈ List.range 4, PhaseAt 4 (40+i) := by decide +kernel

theorem phase_4_44 : ∀ i ∈ List.range 4, PhaseAt 4 (44+i) := by decide +kernel

theorem phase_4_48 : ∀ i ∈ List.range 4, PhaseAt 4 (48+i) := by decide +kernel

theorem phase_4_52 : ∀ i ∈ List.range 4, PhaseAt 4 (52+i) := by decide +kernel

theorem phase_4_56 : ∀ i ∈ List.range 4, PhaseAt 4 (56+i) := by decide +kernel

theorem phase_4_60 : ∀ i ∈ List.range 4, PhaseAt 4 (60+i) := by decide +kernel

theorem phase_4_64 : ∀ i ∈ List.range 4, PhaseAt 4 (64+i) := by decide +kernel

theorem phase_4_68 : ∀ i ∈ List.range 4, PhaseAt 4 (68+i) := by decide +kernel

theorem phase_4_72 : ∀ i ∈ List.range 4, PhaseAt 4 (72+i) := by decide +kernel

theorem phase_4_76 : ∀ i ∈ List.range 4, PhaseAt 4 (76+i) := by decide +kernel

theorem phase_4_80 : ∀ i ∈ List.range 4, PhaseAt 4 (80+i) := by decide +kernel

theorem phase_4_84 : ∀ i ∈ List.range 4, PhaseAt 4 (84+i) := by decide +kernel

theorem phase_4_88 : ∀ i ∈ List.range 4, PhaseAt 4 (88+i) := by decide +kernel

theorem phase_4_92 : ∀ i ∈ List.range 4, PhaseAt 4 (92+i) := by decide +kernel

theorem phase_4_96 : ∀ i ∈ List.range 4, PhaseAt 4 (96+i) := by decide +kernel

theorem phase_4_100 : ∀ i ∈ List.range 4, PhaseAt 4 (100+i) := by decide +kernel

theorem phase_4_104 : ∀ i ∈ List.range 4, PhaseAt 4 (104+i) := by decide +kernel

theorem phase_4_108 : ∀ i ∈ List.range 4, PhaseAt 4 (108+i) := by decide +kernel

theorem phase_4_112 : ∀ i ∈ List.range 4, PhaseAt 4 (112+i) := by decide +kernel

theorem phase_4_116 : ∀ i ∈ List.range 4, PhaseAt 4 (116+i) := by decide +kernel

theorem phase_4_120 : ∀ i ∈ List.range 4, PhaseAt 4 (120+i) := by decide +kernel

theorem phase_4_124 : ∀ i ∈ List.range 4, PhaseAt 4 (124+i) := by decide +kernel

theorem phase_4_128 : ∀ i ∈ List.range 4, PhaseAt 4 (128+i) := by decide +kernel

theorem phase_4_132 : ∀ i ∈ List.range 4, PhaseAt 4 (132+i) := by decide +kernel

theorem phase_4_136 : ∀ i ∈ List.range 4, PhaseAt 4 (136+i) := by decide +kernel

theorem phase_4_140 : ∀ i ∈ List.range 3, PhaseAt 4 (140+i) := by decide +kernel

theorem phase_4 (v : ℕ) (hv : v ∈ List.range 143) : PhaseAt 4 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 4 v)
  have h := (join 0 72 71 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_4_0 phase_4_4) (join 8 4 4 phase_4_8 phase_4_12)) (join 16 8 12 (join 16 4 4 phase_4_16 phase_4_20) (join 24 4 8 phase_4_24 (join 28 4 4 phase_4_28 phase_4_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_4_36 phase_4_40) (join 44 4 4 phase_4_44 phase_4_48)) (join 52 8 12 (join 52 4 4 phase_4_52 phase_4_56) (join 60 4 8 phase_4_60 (join 64 4 4 phase_4_64 phase_4_68))))) (join 72 36 35 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_4_72 phase_4_76) (join 80 4 4 phase_4_80 phase_4_84)) (join 88 8 12 (join 88 4 4 phase_4_88 phase_4_92) (join 96 4 8 phase_4_96 (join 100 4 4 phase_4_100 phase_4_104)))) (join 108 16 19 (join 108 8 8 (join 108 4 4 phase_4_108 phase_4_112) (join 116 4 4 phase_4_116 phase_4_120)) (join 124 8 11 (join 124 4 4 phase_4_124 phase_4_128) (join 132 4 7 phase_4_132 (join 136 4 3 phase_4_136 phase_4_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_4_0 : ∀ i ∈ List.range 1, ThresholdAt 4 (0+i) := by decide +kernel

theorem threshold_4_1 : ∀ i ∈ List.range 1, ThresholdAt 4 (1+i) := by decide +kernel

theorem threshold_4_2 : ∀ i ∈ List.range 1, ThresholdAt 4 (2+i) := by decide +kernel

theorem threshold_4_3 : ∀ i ∈ List.range 1, ThresholdAt 4 (3+i) := by decide +kernel

theorem threshold_4_4 : ∀ i ∈ List.range 1, ThresholdAt 4 (4+i) := by decide +kernel

theorem threshold_4_5 : ∀ i ∈ List.range 1, ThresholdAt 4 (5+i) := by decide +kernel

theorem threshold_4_6 : ∀ i ∈ List.range 1, ThresholdAt 4 (6+i) := by decide +kernel

theorem threshold_4_7 : ∀ i ∈ List.range 1, ThresholdAt 4 (7+i) := by decide +kernel

theorem threshold_4_8 : ∀ i ∈ List.range 1, ThresholdAt 4 (8+i) := by decide +kernel

theorem threshold_4_9 : ∀ i ∈ List.range 1, ThresholdAt 4 (9+i) := by decide +kernel

theorem threshold_4_10 : ∀ i ∈ List.range 1, ThresholdAt 4 (10+i) := by decide +kernel

theorem threshold_4_11 : ∀ i ∈ List.range 1, ThresholdAt 4 (11+i) := by decide +kernel

theorem threshold_4_12 : ∀ i ∈ List.range 1, ThresholdAt 4 (12+i) := by decide +kernel

theorem threshold_4_13 : ∀ i ∈ List.range 1, ThresholdAt 4 (13+i) := by decide +kernel

theorem threshold_4_14 : ∀ i ∈ List.range 1, ThresholdAt 4 (14+i) := by decide +kernel

theorem threshold_4_15 : ∀ i ∈ List.range 1, ThresholdAt 4 (15+i) := by decide +kernel

theorem threshold_4_16 : ∀ i ∈ List.range 1, ThresholdAt 4 (16+i) := by decide +kernel

theorem threshold_4_17 : ∀ i ∈ List.range 1, ThresholdAt 4 (17+i) := by decide +kernel

theorem threshold_4_18 : ∀ i ∈ List.range 1, ThresholdAt 4 (18+i) := by decide +kernel

theorem threshold_4_19 : ∀ i ∈ List.range 1, ThresholdAt 4 (19+i) := by decide +kernel

theorem threshold_4_20 : ∀ i ∈ List.range 1, ThresholdAt 4 (20+i) := by decide +kernel

theorem threshold_4_21 : ∀ i ∈ List.range 1, ThresholdAt 4 (21+i) := by decide +kernel

theorem threshold_4_22 : ∀ i ∈ List.range 1, ThresholdAt 4 (22+i) := by decide +kernel

theorem threshold_4_23 : ∀ i ∈ List.range 1, ThresholdAt 4 (23+i) := by decide +kernel

theorem threshold_4_24 : ∀ i ∈ List.range 1, ThresholdAt 4 (24+i) := by decide +kernel

theorem threshold_4_25 : ∀ i ∈ List.range 1, ThresholdAt 4 (25+i) := by decide +kernel

theorem threshold_4_26 : ∀ i ∈ List.range 1, ThresholdAt 4 (26+i) := by decide +kernel

theorem threshold_4_27 : ∀ i ∈ List.range 1, ThresholdAt 4 (27+i) := by decide +kernel

theorem threshold_4_28 : ∀ i ∈ List.range 1, ThresholdAt 4 (28+i) := by decide +kernel

theorem threshold_4_29 : ∀ i ∈ List.range 1, ThresholdAt 4 (29+i) := by decide +kernel

theorem threshold_4_30 : ∀ i ∈ List.range 1, ThresholdAt 4 (30+i) := by decide +kernel

theorem threshold_4_31 : ∀ i ∈ List.range 1, ThresholdAt 4 (31+i) := by decide +kernel

theorem threshold_4_32 : ∀ i ∈ List.range 1, ThresholdAt 4 (32+i) := by decide +kernel

theorem threshold_4_33 : ∀ i ∈ List.range 1, ThresholdAt 4 (33+i) := by decide +kernel

theorem threshold_4_34 : ∀ i ∈ List.range 1, ThresholdAt 4 (34+i) := by decide +kernel

theorem threshold_4_35 : ∀ i ∈ List.range 1, ThresholdAt 4 (35+i) := by decide +kernel

theorem threshold_4_36 : ∀ i ∈ List.range 1, ThresholdAt 4 (36+i) := by decide +kernel

theorem threshold_4_37 : ∀ i ∈ List.range 1, ThresholdAt 4 (37+i) := by decide +kernel

theorem threshold_4_38 : ∀ i ∈ List.range 1, ThresholdAt 4 (38+i) := by decide +kernel

theorem threshold_4_39 : ∀ i ∈ List.range 1, ThresholdAt 4 (39+i) := by decide +kernel

theorem threshold_4_40 : ∀ i ∈ List.range 1, ThresholdAt 4 (40+i) := by decide +kernel

theorem threshold_4_41 : ∀ i ∈ List.range 1, ThresholdAt 4 (41+i) := by decide +kernel

theorem threshold_4_42 : ∀ i ∈ List.range 1, ThresholdAt 4 (42+i) := by decide +kernel

theorem threshold_4_43 : ∀ i ∈ List.range 1, ThresholdAt 4 (43+i) := by decide +kernel

theorem threshold_4_44 : ∀ i ∈ List.range 1, ThresholdAt 4 (44+i) := by decide +kernel

theorem threshold_4_45 : ∀ i ∈ List.range 1, ThresholdAt 4 (45+i) := by decide +kernel

theorem threshold_4_46 : ∀ i ∈ List.range 1, ThresholdAt 4 (46+i) := by decide +kernel

theorem threshold_4_47 : ∀ i ∈ List.range 1, ThresholdAt 4 (47+i) := by decide +kernel

theorem threshold_4_48 : ∀ i ∈ List.range 1, ThresholdAt 4 (48+i) := by decide +kernel

theorem threshold_4_49 : ∀ i ∈ List.range 1, ThresholdAt 4 (49+i) := by decide +kernel

theorem threshold_4_50 : ∀ i ∈ List.range 1, ThresholdAt 4 (50+i) := by decide +kernel

theorem threshold_4_51 : ∀ i ∈ List.range 1, ThresholdAt 4 (51+i) := by decide +kernel

theorem threshold_4_52 : ∀ i ∈ List.range 1, ThresholdAt 4 (52+i) := by decide +kernel

theorem threshold_4_53 : ∀ i ∈ List.range 1, ThresholdAt 4 (53+i) := by decide +kernel

theorem threshold_4_54 : ∀ i ∈ List.range 1, ThresholdAt 4 (54+i) := by decide +kernel

theorem threshold_4_55 : ∀ i ∈ List.range 1, ThresholdAt 4 (55+i) := by decide +kernel

theorem threshold_4_56 : ∀ i ∈ List.range 1, ThresholdAt 4 (56+i) := by decide +kernel

theorem threshold_4_57 : ∀ i ∈ List.range 1, ThresholdAt 4 (57+i) := by decide +kernel

theorem threshold_4_58 : ∀ i ∈ List.range 1, ThresholdAt 4 (58+i) := by decide +kernel

theorem threshold_4_59 : ∀ i ∈ List.range 1, ThresholdAt 4 (59+i) := by decide +kernel

theorem threshold_4_60 : ∀ i ∈ List.range 1, ThresholdAt 4 (60+i) := by decide +kernel

theorem threshold_4_61 : ∀ i ∈ List.range 1, ThresholdAt 4 (61+i) := by decide +kernel

theorem threshold_4_62 : ∀ i ∈ List.range 1, ThresholdAt 4 (62+i) := by decide +kernel

theorem threshold_4_63 : ∀ i ∈ List.range 1, ThresholdAt 4 (63+i) := by decide +kernel

theorem threshold_4_64 : ∀ i ∈ List.range 1, ThresholdAt 4 (64+i) := by decide +kernel

theorem threshold_4_65 : ∀ i ∈ List.range 1, ThresholdAt 4 (65+i) := by decide +kernel

theorem threshold_4_66 : ∀ i ∈ List.range 1, ThresholdAt 4 (66+i) := by decide +kernel

theorem threshold_4_67 : ∀ i ∈ List.range 1, ThresholdAt 4 (67+i) := by decide +kernel

theorem threshold_4_68 : ∀ i ∈ List.range 1, ThresholdAt 4 (68+i) := by decide +kernel

theorem threshold_4_69 : ∀ i ∈ List.range 1, ThresholdAt 4 (69+i) := by decide +kernel

theorem threshold_4_70 : ∀ i ∈ List.range 1, ThresholdAt 4 (70+i) := by decide +kernel

theorem threshold_4_71 : ∀ i ∈ List.range 1, ThresholdAt 4 (71+i) := by decide +kernel

theorem threshold_4_72 : ∀ i ∈ List.range 1, ThresholdAt 4 (72+i) := by decide +kernel

theorem threshold_4_73 : ∀ i ∈ List.range 1, ThresholdAt 4 (73+i) := by decide +kernel

theorem threshold_4_74 : ∀ i ∈ List.range 1, ThresholdAt 4 (74+i) := by decide +kernel

theorem threshold_4_75 : ∀ i ∈ List.range 1, ThresholdAt 4 (75+i) := by decide +kernel

theorem threshold_4_76 : ∀ i ∈ List.range 1, ThresholdAt 4 (76+i) := by decide +kernel

theorem threshold_4_77 : ∀ i ∈ List.range 1, ThresholdAt 4 (77+i) := by decide +kernel

theorem threshold_4_78 : ∀ i ∈ List.range 1, ThresholdAt 4 (78+i) := by decide +kernel

theorem threshold_4_79 : ∀ i ∈ List.range 1, ThresholdAt 4 (79+i) := by decide +kernel

theorem threshold_4_80 : ∀ i ∈ List.range 1, ThresholdAt 4 (80+i) := by decide +kernel

theorem threshold_4_81 : ∀ i ∈ List.range 1, ThresholdAt 4 (81+i) := by decide +kernel

theorem threshold_4_82 : ∀ i ∈ List.range 1, ThresholdAt 4 (82+i) := by decide +kernel

theorem threshold_4_83 : ∀ i ∈ List.range 1, ThresholdAt 4 (83+i) := by decide +kernel

theorem threshold_4_84 : ∀ i ∈ List.range 1, ThresholdAt 4 (84+i) := by decide +kernel

theorem threshold_4_85 : ∀ i ∈ List.range 1, ThresholdAt 4 (85+i) := by decide +kernel

theorem threshold_4_86 : ∀ i ∈ List.range 1, ThresholdAt 4 (86+i) := by decide +kernel

theorem threshold_4_87 : ∀ i ∈ List.range 1, ThresholdAt 4 (87+i) := by decide +kernel

theorem threshold_4_88 : ∀ i ∈ List.range 1, ThresholdAt 4 (88+i) := by decide +kernel

theorem threshold_4_89 : ∀ i ∈ List.range 1, ThresholdAt 4 (89+i) := by decide +kernel

theorem threshold_4_90 : ∀ i ∈ List.range 1, ThresholdAt 4 (90+i) := by decide +kernel

theorem threshold_4_91 : ∀ i ∈ List.range 1, ThresholdAt 4 (91+i) := by decide +kernel

theorem threshold_4_92 : ∀ i ∈ List.range 1, ThresholdAt 4 (92+i) := by decide +kernel

theorem threshold_4_93 : ∀ i ∈ List.range 1, ThresholdAt 4 (93+i) := by decide +kernel

theorem threshold_4_94 : ∀ i ∈ List.range 1, ThresholdAt 4 (94+i) := by decide +kernel

theorem threshold_4_95 : ∀ i ∈ List.range 1, ThresholdAt 4 (95+i) := by decide +kernel

theorem threshold_4_96 : ∀ i ∈ List.range 1, ThresholdAt 4 (96+i) := by decide +kernel

theorem threshold_4_97 : ∀ i ∈ List.range 1, ThresholdAt 4 (97+i) := by decide +kernel

theorem threshold_4_98 : ∀ i ∈ List.range 1, ThresholdAt 4 (98+i) := by decide +kernel

theorem threshold_4_99 : ∀ i ∈ List.range 1, ThresholdAt 4 (99+i) := by decide +kernel

theorem threshold_4_100 : ∀ i ∈ List.range 1, ThresholdAt 4 (100+i) := by decide +kernel

theorem threshold_4_101 : ∀ i ∈ List.range 1, ThresholdAt 4 (101+i) := by decide +kernel

theorem threshold_4_102 : ∀ i ∈ List.range 1, ThresholdAt 4 (102+i) := by decide +kernel

theorem threshold_4_103 : ∀ i ∈ List.range 1, ThresholdAt 4 (103+i) := by decide +kernel

theorem threshold_4_104 : ∀ i ∈ List.range 1, ThresholdAt 4 (104+i) := by decide +kernel

theorem threshold_4_105 : ∀ i ∈ List.range 1, ThresholdAt 4 (105+i) := by decide +kernel

theorem threshold_4_106 : ∀ i ∈ List.range 1, ThresholdAt 4 (106+i) := by decide +kernel

theorem threshold_4_107 : ∀ i ∈ List.range 1, ThresholdAt 4 (107+i) := by decide +kernel

theorem threshold_4_108 : ∀ i ∈ List.range 1, ThresholdAt 4 (108+i) := by decide +kernel

theorem threshold_4_109 : ∀ i ∈ List.range 1, ThresholdAt 4 (109+i) := by decide +kernel

theorem threshold_4_110 : ∀ i ∈ List.range 1, ThresholdAt 4 (110+i) := by decide +kernel

theorem threshold_4_111 : ∀ i ∈ List.range 1, ThresholdAt 4 (111+i) := by decide +kernel

theorem threshold_4_112 : ∀ i ∈ List.range 1, ThresholdAt 4 (112+i) := by decide +kernel

theorem threshold_4_113 : ∀ i ∈ List.range 1, ThresholdAt 4 (113+i) := by decide +kernel

theorem threshold_4_114 : ∀ i ∈ List.range 1, ThresholdAt 4 (114+i) := by decide +kernel

theorem threshold_4_115 : ∀ i ∈ List.range 1, ThresholdAt 4 (115+i) := by decide +kernel

theorem threshold_4_116 : ∀ i ∈ List.range 1, ThresholdAt 4 (116+i) := by decide +kernel

theorem threshold_4_117 : ∀ i ∈ List.range 1, ThresholdAt 4 (117+i) := by decide +kernel

theorem threshold_4_118 : ∀ i ∈ List.range 1, ThresholdAt 4 (118+i) := by decide +kernel

theorem threshold_4_119 : ∀ i ∈ List.range 1, ThresholdAt 4 (119+i) := by decide +kernel

theorem threshold_4_120 : ∀ i ∈ List.range 1, ThresholdAt 4 (120+i) := by decide +kernel

theorem threshold_4_121 : ∀ i ∈ List.range 1, ThresholdAt 4 (121+i) := by decide +kernel

theorem threshold_4_122 : ∀ i ∈ List.range 1, ThresholdAt 4 (122+i) := by decide +kernel

theorem threshold_4_123 : ∀ i ∈ List.range 1, ThresholdAt 4 (123+i) := by decide +kernel

theorem threshold_4_124 : ∀ i ∈ List.range 1, ThresholdAt 4 (124+i) := by decide +kernel

theorem threshold_4_125 : ∀ i ∈ List.range 1, ThresholdAt 4 (125+i) := by decide +kernel

theorem threshold_4_126 : ∀ i ∈ List.range 1, ThresholdAt 4 (126+i) := by decide +kernel

theorem threshold_4_127 : ∀ i ∈ List.range 1, ThresholdAt 4 (127+i) := by decide +kernel

theorem threshold_4_128 : ∀ i ∈ List.range 1, ThresholdAt 4 (128+i) := by decide +kernel

theorem threshold_4_129 : ∀ i ∈ List.range 1, ThresholdAt 4 (129+i) := by decide +kernel

theorem threshold_4_130 : ∀ i ∈ List.range 1, ThresholdAt 4 (130+i) := by decide +kernel

theorem threshold_4_131 : ∀ i ∈ List.range 1, ThresholdAt 4 (131+i) := by decide +kernel

theorem threshold_4_132 : ∀ i ∈ List.range 1, ThresholdAt 4 (132+i) := by decide +kernel

theorem threshold_4_133 : ∀ i ∈ List.range 1, ThresholdAt 4 (133+i) := by decide +kernel

theorem threshold_4_134 : ∀ i ∈ List.range 1, ThresholdAt 4 (134+i) := by decide +kernel

theorem threshold_4_135 : ∀ i ∈ List.range 1, ThresholdAt 4 (135+i) := by decide +kernel

theorem threshold_4_136 : ∀ i ∈ List.range 1, ThresholdAt 4 (136+i) := by decide +kernel

theorem threshold_4_137 : ∀ i ∈ List.range 1, ThresholdAt 4 (137+i) := by decide +kernel

theorem threshold_4_138 : ∀ i ∈ List.range 1, ThresholdAt 4 (138+i) := by decide +kernel

theorem threshold_4_139 : ∀ i ∈ List.range 1, ThresholdAt 4 (139+i) := by decide +kernel

theorem threshold_4_140 : ∀ i ∈ List.range 1, ThresholdAt 4 (140+i) := by decide +kernel

theorem threshold_4_141 : ∀ i ∈ List.range 1, ThresholdAt 4 (141+i) := by decide +kernel

theorem threshold_4_142 : ∀ i ∈ List.range 1, ThresholdAt 4 (142+i) := by decide +kernel

theorem threshold_4 (v : ℕ) (hv : v ∈ List.range 143) : ThresholdAt 4 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 4 v)
  have h := (join 0 71 72 (join 0 35 36 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_4_0 threshold_4_1) (join 2 1 1 threshold_4_2 threshold_4_3)) (join 4 2 2 (join 4 1 1 threshold_4_4 threshold_4_5) (join 6 1 1 threshold_4_6 threshold_4_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_4_8 threshold_4_9) (join 10 1 1 threshold_4_10 threshold_4_11)) (join 12 2 3 (join 12 1 1 threshold_4_12 threshold_4_13) (join 14 1 2 threshold_4_14 (join 15 1 1 threshold_4_15 threshold_4_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 threshold_4_17 threshold_4_18) (join 19 1 1 threshold_4_19 threshold_4_20)) (join 21 2 3 (join 21 1 1 threshold_4_21 threshold_4_22) (join 23 1 2 threshold_4_23 (join 24 1 1 threshold_4_24 threshold_4_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 threshold_4_26 threshold_4_27) (join 28 1 1 threshold_4_28 threshold_4_29)) (join 30 2 3 (join 30 1 1 threshold_4_30 threshold_4_31) (join 32 1 2 threshold_4_32 (join 33 1 1 threshold_4_33 threshold_4_34)))))) (join 35 18 18 (join 35 9 9 (join 35 4 5 (join 35 2 2 (join 35 1 1 threshold_4_35 threshold_4_36) (join 37 1 1 threshold_4_37 threshold_4_38)) (join 39 2 3 (join 39 1 1 threshold_4_39 threshold_4_40) (join 41 1 2 threshold_4_41 (join 42 1 1 threshold_4_42 threshold_4_43)))) (join 44 4 5 (join 44 2 2 (join 44 1 1 threshold_4_44 threshold_4_45) (join 46 1 1 threshold_4_46 threshold_4_47)) (join 48 2 3 (join 48 1 1 threshold_4_48 threshold_4_49) (join 50 1 2 threshold_4_50 (join 51 1 1 threshold_4_51 threshold_4_52))))) (join 53 9 9 (join 53 4 5 (join 53 2 2 (join 53 1 1 threshold_4_53 threshold_4_54) (join 55 1 1 threshold_4_55 threshold_4_56)) (join 57 2 3 (join 57 1 1 threshold_4_57 threshold_4_58) (join 59 1 2 threshold_4_59 (join 60 1 1 threshold_4_60 threshold_4_61)))) (join 62 4 5 (join 62 2 2 (join 62 1 1 threshold_4_62 threshold_4_63) (join 64 1 1 threshold_4_64 threshold_4_65)) (join 66 2 3 (join 66 1 1 threshold_4_66 threshold_4_67) (join 68 1 2 threshold_4_68 (join 69 1 1 threshold_4_69 threshold_4_70))))))) (join 71 36 36 (join 71 18 18 (join 71 9 9 (join 71 4 5 (join 71 2 2 (join 71 1 1 threshold_4_71 threshold_4_72) (join 73 1 1 threshold_4_73 threshold_4_74)) (join 75 2 3 (join 75 1 1 threshold_4_75 threshold_4_76) (join 77 1 2 threshold_4_77 (join 78 1 1 threshold_4_78 threshold_4_79)))) (join 80 4 5 (join 80 2 2 (join 80 1 1 threshold_4_80 threshold_4_81) (join 82 1 1 threshold_4_82 threshold_4_83)) (join 84 2 3 (join 84 1 1 threshold_4_84 threshold_4_85) (join 86 1 2 threshold_4_86 (join 87 1 1 threshold_4_87 threshold_4_88))))) (join 89 9 9 (join 89 4 5 (join 89 2 2 (join 89 1 1 threshold_4_89 threshold_4_90) (join 91 1 1 threshold_4_91 threshold_4_92)) (join 93 2 3 (join 93 1 1 threshold_4_93 threshold_4_94) (join 95 1 2 threshold_4_95 (join 96 1 1 threshold_4_96 threshold_4_97)))) (join 98 4 5 (join 98 2 2 (join 98 1 1 threshold_4_98 threshold_4_99) (join 100 1 1 threshold_4_100 threshold_4_101)) (join 102 2 3 (join 102 1 1 threshold_4_102 threshold_4_103) (join 104 1 2 threshold_4_104 (join 105 1 1 threshold_4_105 threshold_4_106)))))) (join 107 18 18 (join 107 9 9 (join 107 4 5 (join 107 2 2 (join 107 1 1 threshold_4_107 threshold_4_108) (join 109 1 1 threshold_4_109 threshold_4_110)) (join 111 2 3 (join 111 1 1 threshold_4_111 threshold_4_112) (join 113 1 2 threshold_4_113 (join 114 1 1 threshold_4_114 threshold_4_115)))) (join 116 4 5 (join 116 2 2 (join 116 1 1 threshold_4_116 threshold_4_117) (join 118 1 1 threshold_4_118 threshold_4_119)) (join 120 2 3 (join 120 1 1 threshold_4_120 threshold_4_121) (join 122 1 2 threshold_4_122 (join 123 1 1 threshold_4_123 threshold_4_124))))) (join 125 9 9 (join 125 4 5 (join 125 2 2 (join 125 1 1 threshold_4_125 threshold_4_126) (join 127 1 1 threshold_4_127 threshold_4_128)) (join 129 2 3 (join 129 1 1 threshold_4_129 threshold_4_130) (join 131 1 2 threshold_4_131 (join 132 1 1 threshold_4_132 threshold_4_133)))) (join 134 4 5 (join 134 2 2 (join 134 1 1 threshold_4_134 threshold_4_135) (join 136 1 1 threshold_4_136 threshold_4_137)) (join 138 2 3 (join 138 1 1 threshold_4_138 threshold_4_139) (join 140 1 2 threshold_4_140 (join 141 1 1 threshold_4_141 threshold_4_142))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_4_0 : ∀ i ∈ List.range 4, LedgerAt 4 (0+i) := by decide +kernel

theorem ledger_4_4 : ∀ i ∈ List.range 4, LedgerAt 4 (4+i) := by decide +kernel

theorem ledger_4_8 : ∀ i ∈ List.range 4, LedgerAt 4 (8+i) := by decide +kernel

theorem ledger_4_12 : ∀ i ∈ List.range 4, LedgerAt 4 (12+i) := by decide +kernel

theorem ledger_4_16 : ∀ i ∈ List.range 4, LedgerAt 4 (16+i) := by decide +kernel

theorem ledger_4_20 : ∀ i ∈ List.range 4, LedgerAt 4 (20+i) := by decide +kernel

theorem ledger_4_24 : ∀ i ∈ List.range 4, LedgerAt 4 (24+i) := by decide +kernel

theorem ledger_4_28 : ∀ i ∈ List.range 4, LedgerAt 4 (28+i) := by decide +kernel

theorem ledger_4_32 : ∀ i ∈ List.range 4, LedgerAt 4 (32+i) := by decide +kernel

theorem ledger_4_36 : ∀ i ∈ List.range 4, LedgerAt 4 (36+i) := by decide +kernel

theorem ledger_4_40 : ∀ i ∈ List.range 4, LedgerAt 4 (40+i) := by decide +kernel

theorem ledger_4_44 : ∀ i ∈ List.range 4, LedgerAt 4 (44+i) := by decide +kernel

theorem ledger_4_48 : ∀ i ∈ List.range 4, LedgerAt 4 (48+i) := by decide +kernel

theorem ledger_4_52 : ∀ i ∈ List.range 4, LedgerAt 4 (52+i) := by decide +kernel

theorem ledger_4_56 : ∀ i ∈ List.range 4, LedgerAt 4 (56+i) := by decide +kernel

theorem ledger_4_60 : ∀ i ∈ List.range 4, LedgerAt 4 (60+i) := by decide +kernel

theorem ledger_4_64 : ∀ i ∈ List.range 4, LedgerAt 4 (64+i) := by decide +kernel

theorem ledger_4_68 : ∀ i ∈ List.range 4, LedgerAt 4 (68+i) := by decide +kernel

theorem ledger_4_72 : ∀ i ∈ List.range 4, LedgerAt 4 (72+i) := by decide +kernel

theorem ledger_4_76 : ∀ i ∈ List.range 4, LedgerAt 4 (76+i) := by decide +kernel

theorem ledger_4_80 : ∀ i ∈ List.range 4, LedgerAt 4 (80+i) := by decide +kernel

theorem ledger_4_84 : ∀ i ∈ List.range 4, LedgerAt 4 (84+i) := by decide +kernel

theorem ledger_4_88 : ∀ i ∈ List.range 4, LedgerAt 4 (88+i) := by decide +kernel

theorem ledger_4_92 : ∀ i ∈ List.range 4, LedgerAt 4 (92+i) := by decide +kernel

theorem ledger_4_96 : ∀ i ∈ List.range 4, LedgerAt 4 (96+i) := by decide +kernel

theorem ledger_4_100 : ∀ i ∈ List.range 4, LedgerAt 4 (100+i) := by decide +kernel

theorem ledger_4_104 : ∀ i ∈ List.range 4, LedgerAt 4 (104+i) := by decide +kernel

theorem ledger_4_108 : ∀ i ∈ List.range 4, LedgerAt 4 (108+i) := by decide +kernel

theorem ledger_4_112 : ∀ i ∈ List.range 4, LedgerAt 4 (112+i) := by decide +kernel

theorem ledger_4_116 : ∀ i ∈ List.range 4, LedgerAt 4 (116+i) := by decide +kernel

theorem ledger_4_120 : ∀ i ∈ List.range 4, LedgerAt 4 (120+i) := by decide +kernel

theorem ledger_4_124 : ∀ i ∈ List.range 4, LedgerAt 4 (124+i) := by decide +kernel

theorem ledger_4_128 : ∀ i ∈ List.range 4, LedgerAt 4 (128+i) := by decide +kernel

theorem ledger_4_132 : ∀ i ∈ List.range 4, LedgerAt 4 (132+i) := by decide +kernel

theorem ledger_4_136 : ∀ i ∈ List.range 4, LedgerAt 4 (136+i) := by decide +kernel

theorem ledger_4_140 : ∀ i ∈ List.range 3, LedgerAt 4 (140+i) := by decide +kernel

theorem ledger_4 (v : ℕ) (hv : v ∈ List.range 143) : LedgerAt 4 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 4 v)
  have h := (join 0 72 71 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_4_0 ledger_4_4) (join 8 4 4 ledger_4_8 ledger_4_12)) (join 16 8 12 (join 16 4 4 ledger_4_16 ledger_4_20) (join 24 4 8 ledger_4_24 (join 28 4 4 ledger_4_28 ledger_4_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_4_36 ledger_4_40) (join 44 4 4 ledger_4_44 ledger_4_48)) (join 52 8 12 (join 52 4 4 ledger_4_52 ledger_4_56) (join 60 4 8 ledger_4_60 (join 64 4 4 ledger_4_64 ledger_4_68))))) (join 72 36 35 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_4_72 ledger_4_76) (join 80 4 4 ledger_4_80 ledger_4_84)) (join 88 8 12 (join 88 4 4 ledger_4_88 ledger_4_92) (join 96 4 8 ledger_4_96 (join 100 4 4 ledger_4_100 ledger_4_104)))) (join 108 16 19 (join 108 8 8 (join 108 4 4 ledger_4_108 ledger_4_112) (join 116 4 4 ledger_4_116 ledger_4_120)) (join 124 8 11 (join 124 4 4 ledger_4_124 ledger_4_128) (join 132 4 7 ledger_4_132 (join 136 4 3 ledger_4_136 ledger_4_140))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
