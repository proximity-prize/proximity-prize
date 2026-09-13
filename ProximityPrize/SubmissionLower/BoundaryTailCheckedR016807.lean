import ProximityPrize.SubmissionLower.BoundaryTailFiniteChecks6807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem geometry_1_0 : ∀ i ∈ List.range 4, GeometryAt 1 (0+i) := by decide +kernel

theorem geometry_1_4 : ∀ i ∈ List.range 4, GeometryAt 1 (4+i) := by decide +kernel

theorem geometry_1_8 : ∀ i ∈ List.range 4, GeometryAt 1 (8+i) := by decide +kernel

theorem geometry_1_12 : ∀ i ∈ List.range 4, GeometryAt 1 (12+i) := by decide +kernel

theorem geometry_1_16 : ∀ i ∈ List.range 4, GeometryAt 1 (16+i) := by decide +kernel

theorem geometry_1_20 : ∀ i ∈ List.range 4, GeometryAt 1 (20+i) := by decide +kernel

theorem geometry_1_24 : ∀ i ∈ List.range 4, GeometryAt 1 (24+i) := by decide +kernel

theorem geometry_1_28 : ∀ i ∈ List.range 4, GeometryAt 1 (28+i) := by decide +kernel

theorem geometry_1_32 : ∀ i ∈ List.range 4, GeometryAt 1 (32+i) := by decide +kernel

theorem geometry_1_36 : ∀ i ∈ List.range 4, GeometryAt 1 (36+i) := by decide +kernel

theorem geometry_1_40 : ∀ i ∈ List.range 4, GeometryAt 1 (40+i) := by decide +kernel

theorem geometry_1_44 : ∀ i ∈ List.range 4, GeometryAt 1 (44+i) := by decide +kernel

theorem geometry_1_48 : ∀ i ∈ List.range 4, GeometryAt 1 (48+i) := by decide +kernel

theorem geometry_1_52 : ∀ i ∈ List.range 4, GeometryAt 1 (52+i) := by decide +kernel

theorem geometry_1_56 : ∀ i ∈ List.range 4, GeometryAt 1 (56+i) := by decide +kernel

theorem geometry_1_60 : ∀ i ∈ List.range 4, GeometryAt 1 (60+i) := by decide +kernel

theorem geometry_1_64 : ∀ i ∈ List.range 4, GeometryAt 1 (64+i) := by decide +kernel

theorem geometry_1_68 : ∀ i ∈ List.range 4, GeometryAt 1 (68+i) := by decide +kernel

theorem geometry_1_72 : ∀ i ∈ List.range 4, GeometryAt 1 (72+i) := by decide +kernel

theorem geometry_1_76 : ∀ i ∈ List.range 4, GeometryAt 1 (76+i) := by decide +kernel

theorem geometry_1_80 : ∀ i ∈ List.range 4, GeometryAt 1 (80+i) := by decide +kernel

theorem geometry_1_84 : ∀ i ∈ List.range 4, GeometryAt 1 (84+i) := by decide +kernel

theorem geometry_1_88 : ∀ i ∈ List.range 4, GeometryAt 1 (88+i) := by decide +kernel

theorem geometry_1_92 : ∀ i ∈ List.range 4, GeometryAt 1 (92+i) := by decide +kernel

theorem geometry_1_96 : ∀ i ∈ List.range 4, GeometryAt 1 (96+i) := by decide +kernel

theorem geometry_1_100 : ∀ i ∈ List.range 4, GeometryAt 1 (100+i) := by decide +kernel

theorem geometry_1_104 : ∀ i ∈ List.range 4, GeometryAt 1 (104+i) := by decide +kernel

theorem geometry_1_108 : ∀ i ∈ List.range 4, GeometryAt 1 (108+i) := by decide +kernel

theorem geometry_1_112 : ∀ i ∈ List.range 4, GeometryAt 1 (112+i) := by decide +kernel

theorem geometry_1_116 : ∀ i ∈ List.range 4, GeometryAt 1 (116+i) := by decide +kernel

theorem geometry_1_120 : ∀ i ∈ List.range 4, GeometryAt 1 (120+i) := by decide +kernel

theorem geometry_1_124 : ∀ i ∈ List.range 4, GeometryAt 1 (124+i) := by decide +kernel

theorem geometry_1_128 : ∀ i ∈ List.range 4, GeometryAt 1 (128+i) := by decide +kernel

theorem geometry_1_132 : ∀ i ∈ List.range 4, GeometryAt 1 (132+i) := by decide +kernel

theorem geometry_1_136 : ∀ i ∈ List.range 4, GeometryAt 1 (136+i) := by decide +kernel

theorem geometry_1_140 : ∀ i ∈ List.range 4, GeometryAt 1 (140+i) := by decide +kernel

theorem geometry_1_144 : ∀ i ∈ List.range 2, GeometryAt 1 (144+i) := by decide +kernel

theorem geometry_1 (v : ℕ) (hv : v ∈ List.range 146) : GeometryAt 1 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 1 v)
  have h := (join 0 72 74 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 geometry_1_0 geometry_1_4) (join 8 4 4 geometry_1_8 geometry_1_12)) (join 16 8 12 (join 16 4 4 geometry_1_16 geometry_1_20) (join 24 4 8 geometry_1_24 (join 28 4 4 geometry_1_28 geometry_1_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 geometry_1_36 geometry_1_40) (join 44 4 4 geometry_1_44 geometry_1_48)) (join 52 8 12 (join 52 4 4 geometry_1_52 geometry_1_56) (join 60 4 8 geometry_1_60 (join 64 4 4 geometry_1_64 geometry_1_68))))) (join 72 36 38 (join 72 16 20 (join 72 8 8 (join 72 4 4 geometry_1_72 geometry_1_76) (join 80 4 4 geometry_1_80 geometry_1_84)) (join 88 8 12 (join 88 4 4 geometry_1_88 geometry_1_92) (join 96 4 8 geometry_1_96 (join 100 4 4 geometry_1_100 geometry_1_104)))) (join 108 20 18 (join 108 8 12 (join 108 4 4 geometry_1_108 geometry_1_112) (join 116 4 8 geometry_1_116 (join 120 4 4 geometry_1_120 geometry_1_124))) (join 128 8 10 (join 128 4 4 geometry_1_128 geometry_1_132) (join 136 4 6 geometry_1_136 (join 140 4 2 geometry_1_140 geometry_1_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_1_0 : ∀ i ∈ List.range 1, StrictAt 1 (0+i) := by decide +kernel

theorem strict_1_1 : ∀ i ∈ List.range 1, StrictAt 1 (1+i) := by decide +kernel

theorem strict_1_2 : ∀ i ∈ List.range 1, StrictAt 1 (2+i) := by decide +kernel

theorem strict_1_3 : ∀ i ∈ List.range 1, StrictAt 1 (3+i) := by decide +kernel

theorem strict_1_4 : ∀ i ∈ List.range 1, StrictAt 1 (4+i) := by decide +kernel

theorem strict_1_5 : ∀ i ∈ List.range 1, StrictAt 1 (5+i) := by decide +kernel

theorem strict_1_6 : ∀ i ∈ List.range 1, StrictAt 1 (6+i) := by decide +kernel

theorem strict_1_7 : ∀ i ∈ List.range 1, StrictAt 1 (7+i) := by decide +kernel

theorem strict_1_8 : ∀ i ∈ List.range 1, StrictAt 1 (8+i) := by decide +kernel

theorem strict_1_9 : ∀ i ∈ List.range 1, StrictAt 1 (9+i) := by decide +kernel

theorem strict_1_10 : ∀ i ∈ List.range 1, StrictAt 1 (10+i) := by decide +kernel

theorem strict_1_11 : ∀ i ∈ List.range 1, StrictAt 1 (11+i) := by decide +kernel

theorem strict_1_12 : ∀ i ∈ List.range 1, StrictAt 1 (12+i) := by decide +kernel

theorem strict_1_13 : ∀ i ∈ List.range 1, StrictAt 1 (13+i) := by decide +kernel

theorem strict_1_14 : ∀ i ∈ List.range 1, StrictAt 1 (14+i) := by decide +kernel

theorem strict_1_15 : ∀ i ∈ List.range 1, StrictAt 1 (15+i) := by decide +kernel

theorem strict_1_16 : ∀ i ∈ List.range 1, StrictAt 1 (16+i) := by decide +kernel

theorem strict_1_17 : ∀ i ∈ List.range 1, StrictAt 1 (17+i) := by decide +kernel

theorem strict_1_18 : ∀ i ∈ List.range 1, StrictAt 1 (18+i) := by decide +kernel

theorem strict_1_19 : ∀ i ∈ List.range 1, StrictAt 1 (19+i) := by decide +kernel

theorem strict_1_20 : ∀ i ∈ List.range 1, StrictAt 1 (20+i) := by decide +kernel

theorem strict_1_21 : ∀ i ∈ List.range 1, StrictAt 1 (21+i) := by decide +kernel

theorem strict_1_22 : ∀ i ∈ List.range 1, StrictAt 1 (22+i) := by decide +kernel

theorem strict_1_23 : ∀ i ∈ List.range 1, StrictAt 1 (23+i) := by decide +kernel

theorem strict_1_24 : ∀ i ∈ List.range 1, StrictAt 1 (24+i) := by decide +kernel

theorem strict_1_25 : ∀ i ∈ List.range 1, StrictAt 1 (25+i) := by decide +kernel

theorem strict_1_26 : ∀ i ∈ List.range 1, StrictAt 1 (26+i) := by decide +kernel

theorem strict_1_27 : ∀ i ∈ List.range 1, StrictAt 1 (27+i) := by decide +kernel

theorem strict_1_28 : ∀ i ∈ List.range 1, StrictAt 1 (28+i) := by decide +kernel

theorem strict_1_29 : ∀ i ∈ List.range 1, StrictAt 1 (29+i) := by decide +kernel

theorem strict_1_30 : ∀ i ∈ List.range 1, StrictAt 1 (30+i) := by decide +kernel

theorem strict_1_31 : ∀ i ∈ List.range 1, StrictAt 1 (31+i) := by decide +kernel

theorem strict_1_32 : ∀ i ∈ List.range 1, StrictAt 1 (32+i) := by decide +kernel

theorem strict_1_33 : ∀ i ∈ List.range 1, StrictAt 1 (33+i) := by decide +kernel

theorem strict_1_34 : ∀ i ∈ List.range 1, StrictAt 1 (34+i) := by decide +kernel

theorem strict_1_35 : ∀ i ∈ List.range 1, StrictAt 1 (35+i) := by decide +kernel

theorem strict_1_36 : ∀ i ∈ List.range 1, StrictAt 1 (36+i) := by decide +kernel

theorem strict_1_37 : ∀ i ∈ List.range 1, StrictAt 1 (37+i) := by decide +kernel

theorem strict_1_38 : ∀ i ∈ List.range 1, StrictAt 1 (38+i) := by decide +kernel

theorem strict_1_39 : ∀ i ∈ List.range 1, StrictAt 1 (39+i) := by decide +kernel

theorem strict_1_40 : ∀ i ∈ List.range 1, StrictAt 1 (40+i) := by decide +kernel

theorem strict_1_41 : ∀ i ∈ List.range 1, StrictAt 1 (41+i) := by decide +kernel

theorem strict_1_42 : ∀ i ∈ List.range 1, StrictAt 1 (42+i) := by decide +kernel

theorem strict_1_43 : ∀ i ∈ List.range 1, StrictAt 1 (43+i) := by decide +kernel

theorem strict_1_44 : ∀ i ∈ List.range 1, StrictAt 1 (44+i) := by decide +kernel

theorem strict_1_45 : ∀ i ∈ List.range 1, StrictAt 1 (45+i) := by decide +kernel

theorem strict_1_46 : ∀ i ∈ List.range 1, StrictAt 1 (46+i) := by decide +kernel

theorem strict_1_47 : ∀ i ∈ List.range 1, StrictAt 1 (47+i) := by decide +kernel

theorem strict_1_48 : ∀ i ∈ List.range 1, StrictAt 1 (48+i) := by decide +kernel

theorem strict_1_49 : ∀ i ∈ List.range 1, StrictAt 1 (49+i) := by decide +kernel

theorem strict_1_50 : ∀ i ∈ List.range 1, StrictAt 1 (50+i) := by decide +kernel

theorem strict_1_51 : ∀ i ∈ List.range 1, StrictAt 1 (51+i) := by decide +kernel

theorem strict_1_52 : ∀ i ∈ List.range 1, StrictAt 1 (52+i) := by decide +kernel

theorem strict_1_53 : ∀ i ∈ List.range 1, StrictAt 1 (53+i) := by decide +kernel

theorem strict_1_54 : ∀ i ∈ List.range 1, StrictAt 1 (54+i) := by decide +kernel

theorem strict_1_55 : ∀ i ∈ List.range 1, StrictAt 1 (55+i) := by decide +kernel

theorem strict_1_56 : ∀ i ∈ List.range 1, StrictAt 1 (56+i) := by decide +kernel

theorem strict_1_57 : ∀ i ∈ List.range 1, StrictAt 1 (57+i) := by decide +kernel

theorem strict_1_58 : ∀ i ∈ List.range 1, StrictAt 1 (58+i) := by decide +kernel

theorem strict_1_59 : ∀ i ∈ List.range 1, StrictAt 1 (59+i) := by decide +kernel

theorem strict_1_60 : ∀ i ∈ List.range 1, StrictAt 1 (60+i) := by decide +kernel

theorem strict_1_61 : ∀ i ∈ List.range 1, StrictAt 1 (61+i) := by decide +kernel

theorem strict_1_62 : ∀ i ∈ List.range 1, StrictAt 1 (62+i) := by decide +kernel

theorem strict_1_63 : ∀ i ∈ List.range 1, StrictAt 1 (63+i) := by decide +kernel

theorem strict_1_64 : ∀ i ∈ List.range 1, StrictAt 1 (64+i) := by decide +kernel

theorem strict_1_65 : ∀ i ∈ List.range 1, StrictAt 1 (65+i) := by decide +kernel

theorem strict_1_66 : ∀ i ∈ List.range 1, StrictAt 1 (66+i) := by decide +kernel

theorem strict_1_67 : ∀ i ∈ List.range 1, StrictAt 1 (67+i) := by decide +kernel

theorem strict_1_68 : ∀ i ∈ List.range 1, StrictAt 1 (68+i) := by decide +kernel

theorem strict_1_69 : ∀ i ∈ List.range 1, StrictAt 1 (69+i) := by decide +kernel

theorem strict_1_70 : ∀ i ∈ List.range 1, StrictAt 1 (70+i) := by decide +kernel

theorem strict_1_71 : ∀ i ∈ List.range 1, StrictAt 1 (71+i) := by decide +kernel

theorem strict_1_72 : ∀ i ∈ List.range 1, StrictAt 1 (72+i) := by decide +kernel

theorem strict_1_73 : ∀ i ∈ List.range 1, StrictAt 1 (73+i) := by decide +kernel

theorem strict_1_74 : ∀ i ∈ List.range 1, StrictAt 1 (74+i) := by decide +kernel

theorem strict_1_75 : ∀ i ∈ List.range 1, StrictAt 1 (75+i) := by decide +kernel

theorem strict_1_76 : ∀ i ∈ List.range 1, StrictAt 1 (76+i) := by decide +kernel

theorem strict_1_77 : ∀ i ∈ List.range 1, StrictAt 1 (77+i) := by decide +kernel

theorem strict_1_78 : ∀ i ∈ List.range 1, StrictAt 1 (78+i) := by decide +kernel

theorem strict_1_79 : ∀ i ∈ List.range 1, StrictAt 1 (79+i) := by decide +kernel

theorem strict_1_80 : ∀ i ∈ List.range 1, StrictAt 1 (80+i) := by decide +kernel

theorem strict_1_81 : ∀ i ∈ List.range 1, StrictAt 1 (81+i) := by decide +kernel

theorem strict_1_82 : ∀ i ∈ List.range 1, StrictAt 1 (82+i) := by decide +kernel

theorem strict_1_83 : ∀ i ∈ List.range 1, StrictAt 1 (83+i) := by decide +kernel

theorem strict_1_84 : ∀ i ∈ List.range 1, StrictAt 1 (84+i) := by decide +kernel

theorem strict_1_85 : ∀ i ∈ List.range 1, StrictAt 1 (85+i) := by decide +kernel

theorem strict_1_86 : ∀ i ∈ List.range 1, StrictAt 1 (86+i) := by decide +kernel

theorem strict_1_87 : ∀ i ∈ List.range 1, StrictAt 1 (87+i) := by decide +kernel

theorem strict_1_88 : ∀ i ∈ List.range 1, StrictAt 1 (88+i) := by decide +kernel

theorem strict_1_89 : ∀ i ∈ List.range 1, StrictAt 1 (89+i) := by decide +kernel

theorem strict_1_90 : ∀ i ∈ List.range 1, StrictAt 1 (90+i) := by decide +kernel

theorem strict_1_91 : ∀ i ∈ List.range 1, StrictAt 1 (91+i) := by decide +kernel

theorem strict_1_92 : ∀ i ∈ List.range 1, StrictAt 1 (92+i) := by decide +kernel

theorem strict_1_93 : ∀ i ∈ List.range 1, StrictAt 1 (93+i) := by decide +kernel

theorem strict_1_94 : ∀ i ∈ List.range 1, StrictAt 1 (94+i) := by decide +kernel

theorem strict_1_95 : ∀ i ∈ List.range 1, StrictAt 1 (95+i) := by decide +kernel

theorem strict_1_96 : ∀ i ∈ List.range 1, StrictAt 1 (96+i) := by decide +kernel

theorem strict_1_97 : ∀ i ∈ List.range 1, StrictAt 1 (97+i) := by decide +kernel

theorem strict_1_98 : ∀ i ∈ List.range 1, StrictAt 1 (98+i) := by decide +kernel

theorem strict_1_99 : ∀ i ∈ List.range 1, StrictAt 1 (99+i) := by decide +kernel

theorem strict_1_100 : ∀ i ∈ List.range 1, StrictAt 1 (100+i) := by decide +kernel

theorem strict_1_101 : ∀ i ∈ List.range 1, StrictAt 1 (101+i) := by decide +kernel

theorem strict_1_102 : ∀ i ∈ List.range 1, StrictAt 1 (102+i) := by decide +kernel

theorem strict_1_103 : ∀ i ∈ List.range 1, StrictAt 1 (103+i) := by decide +kernel

theorem strict_1_104 : ∀ i ∈ List.range 1, StrictAt 1 (104+i) := by decide +kernel

theorem strict_1_105 : ∀ i ∈ List.range 1, StrictAt 1 (105+i) := by decide +kernel

theorem strict_1_106 : ∀ i ∈ List.range 1, StrictAt 1 (106+i) := by decide +kernel

theorem strict_1_107 : ∀ i ∈ List.range 1, StrictAt 1 (107+i) := by decide +kernel

theorem strict_1_108 : ∀ i ∈ List.range 1, StrictAt 1 (108+i) := by decide +kernel

theorem strict_1_109 : ∀ i ∈ List.range 1, StrictAt 1 (109+i) := by decide +kernel

theorem strict_1_110 : ∀ i ∈ List.range 1, StrictAt 1 (110+i) := by decide +kernel

theorem strict_1_111 : ∀ i ∈ List.range 1, StrictAt 1 (111+i) := by decide +kernel

theorem strict_1_112 : ∀ i ∈ List.range 1, StrictAt 1 (112+i) := by decide +kernel

theorem strict_1_113 : ∀ i ∈ List.range 1, StrictAt 1 (113+i) := by decide +kernel

theorem strict_1_114 : ∀ i ∈ List.range 1, StrictAt 1 (114+i) := by decide +kernel

theorem strict_1_115 : ∀ i ∈ List.range 1, StrictAt 1 (115+i) := by decide +kernel

theorem strict_1_116 : ∀ i ∈ List.range 1, StrictAt 1 (116+i) := by decide +kernel

theorem strict_1_117 : ∀ i ∈ List.range 1, StrictAt 1 (117+i) := by decide +kernel

theorem strict_1_118 : ∀ i ∈ List.range 1, StrictAt 1 (118+i) := by decide +kernel

theorem strict_1_119 : ∀ i ∈ List.range 1, StrictAt 1 (119+i) := by decide +kernel

theorem strict_1_120 : ∀ i ∈ List.range 1, StrictAt 1 (120+i) := by decide +kernel

theorem strict_1_121 : ∀ i ∈ List.range 1, StrictAt 1 (121+i) := by decide +kernel

theorem strict_1_122 : ∀ i ∈ List.range 1, StrictAt 1 (122+i) := by decide +kernel

theorem strict_1_123 : ∀ i ∈ List.range 1, StrictAt 1 (123+i) := by decide +kernel

theorem strict_1_124 : ∀ i ∈ List.range 1, StrictAt 1 (124+i) := by decide +kernel

theorem strict_1_125 : ∀ i ∈ List.range 1, StrictAt 1 (125+i) := by decide +kernel

theorem strict_1_126 : ∀ i ∈ List.range 1, StrictAt 1 (126+i) := by decide +kernel

theorem strict_1_127 : ∀ i ∈ List.range 1, StrictAt 1 (127+i) := by decide +kernel

theorem strict_1_128 : ∀ i ∈ List.range 1, StrictAt 1 (128+i) := by decide +kernel

theorem strict_1_129 : ∀ i ∈ List.range 1, StrictAt 1 (129+i) := by decide +kernel

theorem strict_1_130 : ∀ i ∈ List.range 1, StrictAt 1 (130+i) := by decide +kernel

theorem strict_1_131 : ∀ i ∈ List.range 1, StrictAt 1 (131+i) := by decide +kernel

theorem strict_1_132 : ∀ i ∈ List.range 1, StrictAt 1 (132+i) := by decide +kernel

theorem strict_1_133 : ∀ i ∈ List.range 1, StrictAt 1 (133+i) := by decide +kernel

theorem strict_1_134 : ∀ i ∈ List.range 1, StrictAt 1 (134+i) := by decide +kernel

theorem strict_1_135 : ∀ i ∈ List.range 1, StrictAt 1 (135+i) := by decide +kernel

theorem strict_1_136 : ∀ i ∈ List.range 1, StrictAt 1 (136+i) := by decide +kernel

theorem strict_1_137 : ∀ i ∈ List.range 1, StrictAt 1 (137+i) := by decide +kernel

theorem strict_1_138 : ∀ i ∈ List.range 1, StrictAt 1 (138+i) := by decide +kernel

theorem strict_1_139 : ∀ i ∈ List.range 1, StrictAt 1 (139+i) := by decide +kernel

theorem strict_1_140 : ∀ i ∈ List.range 1, StrictAt 1 (140+i) := by decide +kernel

theorem strict_1_141 : ∀ i ∈ List.range 1, StrictAt 1 (141+i) := by decide +kernel

theorem strict_1_142 : ∀ i ∈ List.range 1, StrictAt 1 (142+i) := by decide +kernel

theorem strict_1_143 : ∀ i ∈ List.range 1, StrictAt 1 (143+i) := by decide +kernel

theorem strict_1_144 : ∀ i ∈ List.range 1, StrictAt 1 (144+i) := by decide +kernel

theorem strict_1_145 : ∀ i ∈ List.range 1, StrictAt 1 (145+i) := by decide +kernel

theorem strict_1 (v : ℕ) (hv : v ∈ List.range 146) : StrictAt 1 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 1 v)
  have h := (join 0 73 73 (join 0 36 37 (join 0 18 18 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 strict_1_0 strict_1_1) (join 2 1 1 strict_1_2 strict_1_3)) (join 4 2 3 (join 4 1 1 strict_1_4 strict_1_5) (join 6 1 2 strict_1_6 (join 7 1 1 strict_1_7 strict_1_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 strict_1_9 strict_1_10) (join 11 1 1 strict_1_11 strict_1_12)) (join 13 2 3 (join 13 1 1 strict_1_13 strict_1_14) (join 15 1 2 strict_1_15 (join 16 1 1 strict_1_16 strict_1_17))))) (join 18 9 9 (join 18 4 5 (join 18 2 2 (join 18 1 1 strict_1_18 strict_1_19) (join 20 1 1 strict_1_20 strict_1_21)) (join 22 2 3 (join 22 1 1 strict_1_22 strict_1_23) (join 24 1 2 strict_1_24 (join 25 1 1 strict_1_25 strict_1_26)))) (join 27 4 5 (join 27 2 2 (join 27 1 1 strict_1_27 strict_1_28) (join 29 1 1 strict_1_29 strict_1_30)) (join 31 2 3 (join 31 1 1 strict_1_31 strict_1_32) (join 33 1 2 strict_1_33 (join 34 1 1 strict_1_34 strict_1_35)))))) (join 36 18 19 (join 36 9 9 (join 36 4 5 (join 36 2 2 (join 36 1 1 strict_1_36 strict_1_37) (join 38 1 1 strict_1_38 strict_1_39)) (join 40 2 3 (join 40 1 1 strict_1_40 strict_1_41) (join 42 1 2 strict_1_42 (join 43 1 1 strict_1_43 strict_1_44)))) (join 45 4 5 (join 45 2 2 (join 45 1 1 strict_1_45 strict_1_46) (join 47 1 1 strict_1_47 strict_1_48)) (join 49 2 3 (join 49 1 1 strict_1_49 strict_1_50) (join 51 1 2 strict_1_51 (join 52 1 1 strict_1_52 strict_1_53))))) (join 54 9 10 (join 54 4 5 (join 54 2 2 (join 54 1 1 strict_1_54 strict_1_55) (join 56 1 1 strict_1_56 strict_1_57)) (join 58 2 3 (join 58 1 1 strict_1_58 strict_1_59) (join 60 1 2 strict_1_60 (join 61 1 1 strict_1_61 strict_1_62)))) (join 63 5 5 (join 63 2 3 (join 63 1 1 strict_1_63 strict_1_64) (join 65 1 2 strict_1_65 (join 66 1 1 strict_1_66 strict_1_67))) (join 68 2 3 (join 68 1 1 strict_1_68 strict_1_69) (join 70 1 2 strict_1_70 (join 71 1 1 strict_1_71 strict_1_72))))))) (join 73 36 37 (join 73 18 18 (join 73 9 9 (join 73 4 5 (join 73 2 2 (join 73 1 1 strict_1_73 strict_1_74) (join 75 1 1 strict_1_75 strict_1_76)) (join 77 2 3 (join 77 1 1 strict_1_77 strict_1_78) (join 79 1 2 strict_1_79 (join 80 1 1 strict_1_80 strict_1_81)))) (join 82 4 5 (join 82 2 2 (join 82 1 1 strict_1_82 strict_1_83) (join 84 1 1 strict_1_84 strict_1_85)) (join 86 2 3 (join 86 1 1 strict_1_86 strict_1_87) (join 88 1 2 strict_1_88 (join 89 1 1 strict_1_89 strict_1_90))))) (join 91 9 9 (join 91 4 5 (join 91 2 2 (join 91 1 1 strict_1_91 strict_1_92) (join 93 1 1 strict_1_93 strict_1_94)) (join 95 2 3 (join 95 1 1 strict_1_95 strict_1_96) (join 97 1 2 strict_1_97 (join 98 1 1 strict_1_98 strict_1_99)))) (join 100 4 5 (join 100 2 2 (join 100 1 1 strict_1_100 strict_1_101) (join 102 1 1 strict_1_102 strict_1_103)) (join 104 2 3 (join 104 1 1 strict_1_104 strict_1_105) (join 106 1 2 strict_1_106 (join 107 1 1 strict_1_107 strict_1_108)))))) (join 109 18 19 (join 109 9 9 (join 109 4 5 (join 109 2 2 (join 109 1 1 strict_1_109 strict_1_110) (join 111 1 1 strict_1_111 strict_1_112)) (join 113 2 3 (join 113 1 1 strict_1_113 strict_1_114) (join 115 1 2 strict_1_115 (join 116 1 1 strict_1_116 strict_1_117)))) (join 118 4 5 (join 118 2 2 (join 118 1 1 strict_1_118 strict_1_119) (join 120 1 1 strict_1_120 strict_1_121)) (join 122 2 3 (join 122 1 1 strict_1_122 strict_1_123) (join 124 1 2 strict_1_124 (join 125 1 1 strict_1_125 strict_1_126))))) (join 127 9 10 (join 127 4 5 (join 127 2 2 (join 127 1 1 strict_1_127 strict_1_128) (join 129 1 1 strict_1_129 strict_1_130)) (join 131 2 3 (join 131 1 1 strict_1_131 strict_1_132) (join 133 1 2 strict_1_133 (join 134 1 1 strict_1_134 strict_1_135)))) (join 136 5 5 (join 136 2 3 (join 136 1 1 strict_1_136 strict_1_137) (join 138 1 2 strict_1_138 (join 139 1 1 strict_1_139 strict_1_140))) (join 141 2 3 (join 141 1 1 strict_1_141 strict_1_142) (join 143 1 2 strict_1_143 (join 144 1 1 strict_1_144 strict_1_145))))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_1_0 : ∀ i ∈ List.range 4, PhaseAt 1 (0+i) := by decide +kernel

theorem phase_1_4 : ∀ i ∈ List.range 4, PhaseAt 1 (4+i) := by decide +kernel

theorem phase_1_8 : ∀ i ∈ List.range 4, PhaseAt 1 (8+i) := by decide +kernel

theorem phase_1_12 : ∀ i ∈ List.range 4, PhaseAt 1 (12+i) := by decide +kernel

theorem phase_1_16 : ∀ i ∈ List.range 4, PhaseAt 1 (16+i) := by decide +kernel

theorem phase_1_20 : ∀ i ∈ List.range 4, PhaseAt 1 (20+i) := by decide +kernel

theorem phase_1_24 : ∀ i ∈ List.range 4, PhaseAt 1 (24+i) := by decide +kernel

theorem phase_1_28 : ∀ i ∈ List.range 4, PhaseAt 1 (28+i) := by decide +kernel

theorem phase_1_32 : ∀ i ∈ List.range 4, PhaseAt 1 (32+i) := by decide +kernel

theorem phase_1_36 : ∀ i ∈ List.range 4, PhaseAt 1 (36+i) := by decide +kernel

theorem phase_1_40 : ∀ i ∈ List.range 4, PhaseAt 1 (40+i) := by decide +kernel

theorem phase_1_44 : ∀ i ∈ List.range 4, PhaseAt 1 (44+i) := by decide +kernel

theorem phase_1_48 : ∀ i ∈ List.range 4, PhaseAt 1 (48+i) := by decide +kernel

theorem phase_1_52 : ∀ i ∈ List.range 4, PhaseAt 1 (52+i) := by decide +kernel

theorem phase_1_56 : ∀ i ∈ List.range 4, PhaseAt 1 (56+i) := by decide +kernel

theorem phase_1_60 : ∀ i ∈ List.range 4, PhaseAt 1 (60+i) := by decide +kernel

theorem phase_1_64 : ∀ i ∈ List.range 4, PhaseAt 1 (64+i) := by decide +kernel

theorem phase_1_68 : ∀ i ∈ List.range 4, PhaseAt 1 (68+i) := by decide +kernel

theorem phase_1_72 : ∀ i ∈ List.range 4, PhaseAt 1 (72+i) := by decide +kernel

theorem phase_1_76 : ∀ i ∈ List.range 4, PhaseAt 1 (76+i) := by decide +kernel

theorem phase_1_80 : ∀ i ∈ List.range 4, PhaseAt 1 (80+i) := by decide +kernel

theorem phase_1_84 : ∀ i ∈ List.range 4, PhaseAt 1 (84+i) := by decide +kernel

theorem phase_1_88 : ∀ i ∈ List.range 4, PhaseAt 1 (88+i) := by decide +kernel

theorem phase_1_92 : ∀ i ∈ List.range 4, PhaseAt 1 (92+i) := by decide +kernel

theorem phase_1_96 : ∀ i ∈ List.range 4, PhaseAt 1 (96+i) := by decide +kernel

theorem phase_1_100 : ∀ i ∈ List.range 4, PhaseAt 1 (100+i) := by decide +kernel

theorem phase_1_104 : ∀ i ∈ List.range 4, PhaseAt 1 (104+i) := by decide +kernel

theorem phase_1_108 : ∀ i ∈ List.range 4, PhaseAt 1 (108+i) := by decide +kernel

theorem phase_1_112 : ∀ i ∈ List.range 4, PhaseAt 1 (112+i) := by decide +kernel

theorem phase_1_116 : ∀ i ∈ List.range 4, PhaseAt 1 (116+i) := by decide +kernel

theorem phase_1_120 : ∀ i ∈ List.range 4, PhaseAt 1 (120+i) := by decide +kernel

theorem phase_1_124 : ∀ i ∈ List.range 4, PhaseAt 1 (124+i) := by decide +kernel

theorem phase_1_128 : ∀ i ∈ List.range 4, PhaseAt 1 (128+i) := by decide +kernel

theorem phase_1_132 : ∀ i ∈ List.range 4, PhaseAt 1 (132+i) := by decide +kernel

theorem phase_1_136 : ∀ i ∈ List.range 4, PhaseAt 1 (136+i) := by decide +kernel

theorem phase_1_140 : ∀ i ∈ List.range 4, PhaseAt 1 (140+i) := by decide +kernel

theorem phase_1_144 : ∀ i ∈ List.range 2, PhaseAt 1 (144+i) := by decide +kernel

theorem phase_1 (v : ℕ) (hv : v ∈ List.range 146) : PhaseAt 1 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 1 v)
  have h := (join 0 72 74 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_1_0 phase_1_4) (join 8 4 4 phase_1_8 phase_1_12)) (join 16 8 12 (join 16 4 4 phase_1_16 phase_1_20) (join 24 4 8 phase_1_24 (join 28 4 4 phase_1_28 phase_1_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_1_36 phase_1_40) (join 44 4 4 phase_1_44 phase_1_48)) (join 52 8 12 (join 52 4 4 phase_1_52 phase_1_56) (join 60 4 8 phase_1_60 (join 64 4 4 phase_1_64 phase_1_68))))) (join 72 36 38 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_1_72 phase_1_76) (join 80 4 4 phase_1_80 phase_1_84)) (join 88 8 12 (join 88 4 4 phase_1_88 phase_1_92) (join 96 4 8 phase_1_96 (join 100 4 4 phase_1_100 phase_1_104)))) (join 108 20 18 (join 108 8 12 (join 108 4 4 phase_1_108 phase_1_112) (join 116 4 8 phase_1_116 (join 120 4 4 phase_1_120 phase_1_124))) (join 128 8 10 (join 128 4 4 phase_1_128 phase_1_132) (join 136 4 6 phase_1_136 (join 140 4 2 phase_1_140 phase_1_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_1_0 : ∀ i ∈ List.range 1, ThresholdAt 1 (0+i) := by decide +kernel

theorem threshold_1_1 : ∀ i ∈ List.range 1, ThresholdAt 1 (1+i) := by decide +kernel

theorem threshold_1_2 : ∀ i ∈ List.range 1, ThresholdAt 1 (2+i) := by decide +kernel

theorem threshold_1_3 : ∀ i ∈ List.range 1, ThresholdAt 1 (3+i) := by decide +kernel

theorem threshold_1_4 : ∀ i ∈ List.range 1, ThresholdAt 1 (4+i) := by decide +kernel

theorem threshold_1_5 : ∀ i ∈ List.range 1, ThresholdAt 1 (5+i) := by decide +kernel

theorem threshold_1_6 : ∀ i ∈ List.range 1, ThresholdAt 1 (6+i) := by decide +kernel

theorem threshold_1_7 : ∀ i ∈ List.range 1, ThresholdAt 1 (7+i) := by decide +kernel

theorem threshold_1_8 : ∀ i ∈ List.range 1, ThresholdAt 1 (8+i) := by decide +kernel

theorem threshold_1_9 : ∀ i ∈ List.range 1, ThresholdAt 1 (9+i) := by decide +kernel

theorem threshold_1_10 : ∀ i ∈ List.range 1, ThresholdAt 1 (10+i) := by decide +kernel

theorem threshold_1_11 : ∀ i ∈ List.range 1, ThresholdAt 1 (11+i) := by decide +kernel

theorem threshold_1_12 : ∀ i ∈ List.range 1, ThresholdAt 1 (12+i) := by decide +kernel

theorem threshold_1_13 : ∀ i ∈ List.range 1, ThresholdAt 1 (13+i) := by decide +kernel

theorem threshold_1_14 : ∀ i ∈ List.range 1, ThresholdAt 1 (14+i) := by decide +kernel

theorem threshold_1_15 : ∀ i ∈ List.range 1, ThresholdAt 1 (15+i) := by decide +kernel

theorem threshold_1_16 : ∀ i ∈ List.range 1, ThresholdAt 1 (16+i) := by decide +kernel

theorem threshold_1_17 : ∀ i ∈ List.range 1, ThresholdAt 1 (17+i) := by decide +kernel

theorem threshold_1_18 : ∀ i ∈ List.range 1, ThresholdAt 1 (18+i) := by decide +kernel

theorem threshold_1_19 : ∀ i ∈ List.range 1, ThresholdAt 1 (19+i) := by decide +kernel

theorem threshold_1_20 : ∀ i ∈ List.range 1, ThresholdAt 1 (20+i) := by decide +kernel

theorem threshold_1_21 : ∀ i ∈ List.range 1, ThresholdAt 1 (21+i) := by decide +kernel

theorem threshold_1_22 : ∀ i ∈ List.range 1, ThresholdAt 1 (22+i) := by decide +kernel

theorem threshold_1_23 : ∀ i ∈ List.range 1, ThresholdAt 1 (23+i) := by decide +kernel

theorem threshold_1_24 : ∀ i ∈ List.range 1, ThresholdAt 1 (24+i) := by decide +kernel

theorem threshold_1_25 : ∀ i ∈ List.range 1, ThresholdAt 1 (25+i) := by decide +kernel

theorem threshold_1_26 : ∀ i ∈ List.range 1, ThresholdAt 1 (26+i) := by decide +kernel

theorem threshold_1_27 : ∀ i ∈ List.range 1, ThresholdAt 1 (27+i) := by decide +kernel

theorem threshold_1_28 : ∀ i ∈ List.range 1, ThresholdAt 1 (28+i) := by decide +kernel

theorem threshold_1_29 : ∀ i ∈ List.range 1, ThresholdAt 1 (29+i) := by decide +kernel

theorem threshold_1_30 : ∀ i ∈ List.range 1, ThresholdAt 1 (30+i) := by decide +kernel

theorem threshold_1_31 : ∀ i ∈ List.range 1, ThresholdAt 1 (31+i) := by decide +kernel

theorem threshold_1_32 : ∀ i ∈ List.range 1, ThresholdAt 1 (32+i) := by decide +kernel

theorem threshold_1_33 : ∀ i ∈ List.range 1, ThresholdAt 1 (33+i) := by decide +kernel

theorem threshold_1_34 : ∀ i ∈ List.range 1, ThresholdAt 1 (34+i) := by decide +kernel

theorem threshold_1_35 : ∀ i ∈ List.range 1, ThresholdAt 1 (35+i) := by decide +kernel

theorem threshold_1_36 : ∀ i ∈ List.range 1, ThresholdAt 1 (36+i) := by decide +kernel

theorem threshold_1_37 : ∀ i ∈ List.range 1, ThresholdAt 1 (37+i) := by decide +kernel

theorem threshold_1_38 : ∀ i ∈ List.range 1, ThresholdAt 1 (38+i) := by decide +kernel

theorem threshold_1_39 : ∀ i ∈ List.range 1, ThresholdAt 1 (39+i) := by decide +kernel

theorem threshold_1_40 : ∀ i ∈ List.range 1, ThresholdAt 1 (40+i) := by decide +kernel

theorem threshold_1_41 : ∀ i ∈ List.range 1, ThresholdAt 1 (41+i) := by decide +kernel

theorem threshold_1_42 : ∀ i ∈ List.range 1, ThresholdAt 1 (42+i) := by decide +kernel

theorem threshold_1_43 : ∀ i ∈ List.range 1, ThresholdAt 1 (43+i) := by decide +kernel

theorem threshold_1_44 : ∀ i ∈ List.range 1, ThresholdAt 1 (44+i) := by decide +kernel

theorem threshold_1_45 : ∀ i ∈ List.range 1, ThresholdAt 1 (45+i) := by decide +kernel

theorem threshold_1_46 : ∀ i ∈ List.range 1, ThresholdAt 1 (46+i) := by decide +kernel

theorem threshold_1_47 : ∀ i ∈ List.range 1, ThresholdAt 1 (47+i) := by decide +kernel

theorem threshold_1_48 : ∀ i ∈ List.range 1, ThresholdAt 1 (48+i) := by decide +kernel

theorem threshold_1_49 : ∀ i ∈ List.range 1, ThresholdAt 1 (49+i) := by decide +kernel

theorem threshold_1_50 : ∀ i ∈ List.range 1, ThresholdAt 1 (50+i) := by decide +kernel

theorem threshold_1_51 : ∀ i ∈ List.range 1, ThresholdAt 1 (51+i) := by decide +kernel

theorem threshold_1_52 : ∀ i ∈ List.range 1, ThresholdAt 1 (52+i) := by decide +kernel

theorem threshold_1_53 : ∀ i ∈ List.range 1, ThresholdAt 1 (53+i) := by decide +kernel

theorem threshold_1_54 : ∀ i ∈ List.range 1, ThresholdAt 1 (54+i) := by decide +kernel

theorem threshold_1_55 : ∀ i ∈ List.range 1, ThresholdAt 1 (55+i) := by decide +kernel

theorem threshold_1_56 : ∀ i ∈ List.range 1, ThresholdAt 1 (56+i) := by decide +kernel

theorem threshold_1_57 : ∀ i ∈ List.range 1, ThresholdAt 1 (57+i) := by decide +kernel

theorem threshold_1_58 : ∀ i ∈ List.range 1, ThresholdAt 1 (58+i) := by decide +kernel

theorem threshold_1_59 : ∀ i ∈ List.range 1, ThresholdAt 1 (59+i) := by decide +kernel

theorem threshold_1_60 : ∀ i ∈ List.range 1, ThresholdAt 1 (60+i) := by decide +kernel

theorem threshold_1_61 : ∀ i ∈ List.range 1, ThresholdAt 1 (61+i) := by decide +kernel

theorem threshold_1_62 : ∀ i ∈ List.range 1, ThresholdAt 1 (62+i) := by decide +kernel

theorem threshold_1_63 : ∀ i ∈ List.range 1, ThresholdAt 1 (63+i) := by decide +kernel

theorem threshold_1_64 : ∀ i ∈ List.range 1, ThresholdAt 1 (64+i) := by decide +kernel

theorem threshold_1_65 : ∀ i ∈ List.range 1, ThresholdAt 1 (65+i) := by decide +kernel

theorem threshold_1_66 : ∀ i ∈ List.range 1, ThresholdAt 1 (66+i) := by decide +kernel

theorem threshold_1_67 : ∀ i ∈ List.range 1, ThresholdAt 1 (67+i) := by decide +kernel

theorem threshold_1_68 : ∀ i ∈ List.range 1, ThresholdAt 1 (68+i) := by decide +kernel

theorem threshold_1_69 : ∀ i ∈ List.range 1, ThresholdAt 1 (69+i) := by decide +kernel

theorem threshold_1_70 : ∀ i ∈ List.range 1, ThresholdAt 1 (70+i) := by decide +kernel

theorem threshold_1_71 : ∀ i ∈ List.range 1, ThresholdAt 1 (71+i) := by decide +kernel

theorem threshold_1_72 : ∀ i ∈ List.range 1, ThresholdAt 1 (72+i) := by decide +kernel

theorem threshold_1_73 : ∀ i ∈ List.range 1, ThresholdAt 1 (73+i) := by decide +kernel

theorem threshold_1_74 : ∀ i ∈ List.range 1, ThresholdAt 1 (74+i) := by decide +kernel

theorem threshold_1_75 : ∀ i ∈ List.range 1, ThresholdAt 1 (75+i) := by decide +kernel

theorem threshold_1_76 : ∀ i ∈ List.range 1, ThresholdAt 1 (76+i) := by decide +kernel

theorem threshold_1_77 : ∀ i ∈ List.range 1, ThresholdAt 1 (77+i) := by decide +kernel

theorem threshold_1_78 : ∀ i ∈ List.range 1, ThresholdAt 1 (78+i) := by decide +kernel

theorem threshold_1_79 : ∀ i ∈ List.range 1, ThresholdAt 1 (79+i) := by decide +kernel

theorem threshold_1_80 : ∀ i ∈ List.range 1, ThresholdAt 1 (80+i) := by decide +kernel

theorem threshold_1_81 : ∀ i ∈ List.range 1, ThresholdAt 1 (81+i) := by decide +kernel

theorem threshold_1_82 : ∀ i ∈ List.range 1, ThresholdAt 1 (82+i) := by decide +kernel

theorem threshold_1_83 : ∀ i ∈ List.range 1, ThresholdAt 1 (83+i) := by decide +kernel

theorem threshold_1_84 : ∀ i ∈ List.range 1, ThresholdAt 1 (84+i) := by decide +kernel

theorem threshold_1_85 : ∀ i ∈ List.range 1, ThresholdAt 1 (85+i) := by decide +kernel

theorem threshold_1_86 : ∀ i ∈ List.range 1, ThresholdAt 1 (86+i) := by decide +kernel

theorem threshold_1_87 : ∀ i ∈ List.range 1, ThresholdAt 1 (87+i) := by decide +kernel

theorem threshold_1_88 : ∀ i ∈ List.range 1, ThresholdAt 1 (88+i) := by decide +kernel

theorem threshold_1_89 : ∀ i ∈ List.range 1, ThresholdAt 1 (89+i) := by decide +kernel

theorem threshold_1_90 : ∀ i ∈ List.range 1, ThresholdAt 1 (90+i) := by decide +kernel

theorem threshold_1_91 : ∀ i ∈ List.range 1, ThresholdAt 1 (91+i) := by decide +kernel

theorem threshold_1_92 : ∀ i ∈ List.range 1, ThresholdAt 1 (92+i) := by decide +kernel

theorem threshold_1_93 : ∀ i ∈ List.range 1, ThresholdAt 1 (93+i) := by decide +kernel

theorem threshold_1_94 : ∀ i ∈ List.range 1, ThresholdAt 1 (94+i) := by decide +kernel

theorem threshold_1_95 : ∀ i ∈ List.range 1, ThresholdAt 1 (95+i) := by decide +kernel

theorem threshold_1_96 : ∀ i ∈ List.range 1, ThresholdAt 1 (96+i) := by decide +kernel

theorem threshold_1_97 : ∀ i ∈ List.range 1, ThresholdAt 1 (97+i) := by decide +kernel

theorem threshold_1_98 : ∀ i ∈ List.range 1, ThresholdAt 1 (98+i) := by decide +kernel

theorem threshold_1_99 : ∀ i ∈ List.range 1, ThresholdAt 1 (99+i) := by decide +kernel

theorem threshold_1_100 : ∀ i ∈ List.range 1, ThresholdAt 1 (100+i) := by decide +kernel

theorem threshold_1_101 : ∀ i ∈ List.range 1, ThresholdAt 1 (101+i) := by decide +kernel

theorem threshold_1_102 : ∀ i ∈ List.range 1, ThresholdAt 1 (102+i) := by decide +kernel

theorem threshold_1_103 : ∀ i ∈ List.range 1, ThresholdAt 1 (103+i) := by decide +kernel

theorem threshold_1_104 : ∀ i ∈ List.range 1, ThresholdAt 1 (104+i) := by decide +kernel

theorem threshold_1_105 : ∀ i ∈ List.range 1, ThresholdAt 1 (105+i) := by decide +kernel

theorem threshold_1_106 : ∀ i ∈ List.range 1, ThresholdAt 1 (106+i) := by decide +kernel

theorem threshold_1_107 : ∀ i ∈ List.range 1, ThresholdAt 1 (107+i) := by decide +kernel

theorem threshold_1_108 : ∀ i ∈ List.range 1, ThresholdAt 1 (108+i) := by decide +kernel

theorem threshold_1_109 : ∀ i ∈ List.range 1, ThresholdAt 1 (109+i) := by decide +kernel

theorem threshold_1_110 : ∀ i ∈ List.range 1, ThresholdAt 1 (110+i) := by decide +kernel

theorem threshold_1_111 : ∀ i ∈ List.range 1, ThresholdAt 1 (111+i) := by decide +kernel

theorem threshold_1_112 : ∀ i ∈ List.range 1, ThresholdAt 1 (112+i) := by decide +kernel

theorem threshold_1_113 : ∀ i ∈ List.range 1, ThresholdAt 1 (113+i) := by decide +kernel

theorem threshold_1_114 : ∀ i ∈ List.range 1, ThresholdAt 1 (114+i) := by decide +kernel

theorem threshold_1_115 : ∀ i ∈ List.range 1, ThresholdAt 1 (115+i) := by decide +kernel

theorem threshold_1_116 : ∀ i ∈ List.range 1, ThresholdAt 1 (116+i) := by decide +kernel

theorem threshold_1_117 : ∀ i ∈ List.range 1, ThresholdAt 1 (117+i) := by decide +kernel

theorem threshold_1_118 : ∀ i ∈ List.range 1, ThresholdAt 1 (118+i) := by decide +kernel

theorem threshold_1_119 : ∀ i ∈ List.range 1, ThresholdAt 1 (119+i) := by decide +kernel

theorem threshold_1_120 : ∀ i ∈ List.range 1, ThresholdAt 1 (120+i) := by decide +kernel

theorem threshold_1_121 : ∀ i ∈ List.range 1, ThresholdAt 1 (121+i) := by decide +kernel

theorem threshold_1_122 : ∀ i ∈ List.range 1, ThresholdAt 1 (122+i) := by decide +kernel

theorem threshold_1_123 : ∀ i ∈ List.range 1, ThresholdAt 1 (123+i) := by decide +kernel

theorem threshold_1_124 : ∀ i ∈ List.range 1, ThresholdAt 1 (124+i) := by decide +kernel

theorem threshold_1_125 : ∀ i ∈ List.range 1, ThresholdAt 1 (125+i) := by decide +kernel

theorem threshold_1_126 : ∀ i ∈ List.range 1, ThresholdAt 1 (126+i) := by decide +kernel

theorem threshold_1_127 : ∀ i ∈ List.range 1, ThresholdAt 1 (127+i) := by decide +kernel

theorem threshold_1_128 : ∀ i ∈ List.range 1, ThresholdAt 1 (128+i) := by decide +kernel

theorem threshold_1_129 : ∀ i ∈ List.range 1, ThresholdAt 1 (129+i) := by decide +kernel

theorem threshold_1_130 : ∀ i ∈ List.range 1, ThresholdAt 1 (130+i) := by decide +kernel

theorem threshold_1_131 : ∀ i ∈ List.range 1, ThresholdAt 1 (131+i) := by decide +kernel

theorem threshold_1_132 : ∀ i ∈ List.range 1, ThresholdAt 1 (132+i) := by decide +kernel

theorem threshold_1_133 : ∀ i ∈ List.range 1, ThresholdAt 1 (133+i) := by decide +kernel

theorem threshold_1_134 : ∀ i ∈ List.range 1, ThresholdAt 1 (134+i) := by decide +kernel

theorem threshold_1_135 : ∀ i ∈ List.range 1, ThresholdAt 1 (135+i) := by decide +kernel

theorem threshold_1_136 : ∀ i ∈ List.range 1, ThresholdAt 1 (136+i) := by decide +kernel

theorem threshold_1_137 : ∀ i ∈ List.range 1, ThresholdAt 1 (137+i) := by decide +kernel

theorem threshold_1_138 : ∀ i ∈ List.range 1, ThresholdAt 1 (138+i) := by decide +kernel

theorem threshold_1_139 : ∀ i ∈ List.range 1, ThresholdAt 1 (139+i) := by decide +kernel

theorem threshold_1_140 : ∀ i ∈ List.range 1, ThresholdAt 1 (140+i) := by decide +kernel

theorem threshold_1_141 : ∀ i ∈ List.range 1, ThresholdAt 1 (141+i) := by decide +kernel

theorem threshold_1_142 : ∀ i ∈ List.range 1, ThresholdAt 1 (142+i) := by decide +kernel

theorem threshold_1_143 : ∀ i ∈ List.range 1, ThresholdAt 1 (143+i) := by decide +kernel

theorem threshold_1_144 : ∀ i ∈ List.range 1, ThresholdAt 1 (144+i) := by decide +kernel

theorem threshold_1_145 : ∀ i ∈ List.range 1, ThresholdAt 1 (145+i) := by decide +kernel

theorem threshold_1 (v : ℕ) (hv : v ∈ List.range 146) : ThresholdAt 1 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 1 v)
  have h := (join 0 73 73 (join 0 36 37 (join 0 18 18 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_1_0 threshold_1_1) (join 2 1 1 threshold_1_2 threshold_1_3)) (join 4 2 3 (join 4 1 1 threshold_1_4 threshold_1_5) (join 6 1 2 threshold_1_6 (join 7 1 1 threshold_1_7 threshold_1_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 threshold_1_9 threshold_1_10) (join 11 1 1 threshold_1_11 threshold_1_12)) (join 13 2 3 (join 13 1 1 threshold_1_13 threshold_1_14) (join 15 1 2 threshold_1_15 (join 16 1 1 threshold_1_16 threshold_1_17))))) (join 18 9 9 (join 18 4 5 (join 18 2 2 (join 18 1 1 threshold_1_18 threshold_1_19) (join 20 1 1 threshold_1_20 threshold_1_21)) (join 22 2 3 (join 22 1 1 threshold_1_22 threshold_1_23) (join 24 1 2 threshold_1_24 (join 25 1 1 threshold_1_25 threshold_1_26)))) (join 27 4 5 (join 27 2 2 (join 27 1 1 threshold_1_27 threshold_1_28) (join 29 1 1 threshold_1_29 threshold_1_30)) (join 31 2 3 (join 31 1 1 threshold_1_31 threshold_1_32) (join 33 1 2 threshold_1_33 (join 34 1 1 threshold_1_34 threshold_1_35)))))) (join 36 18 19 (join 36 9 9 (join 36 4 5 (join 36 2 2 (join 36 1 1 threshold_1_36 threshold_1_37) (join 38 1 1 threshold_1_38 threshold_1_39)) (join 40 2 3 (join 40 1 1 threshold_1_40 threshold_1_41) (join 42 1 2 threshold_1_42 (join 43 1 1 threshold_1_43 threshold_1_44)))) (join 45 4 5 (join 45 2 2 (join 45 1 1 threshold_1_45 threshold_1_46) (join 47 1 1 threshold_1_47 threshold_1_48)) (join 49 2 3 (join 49 1 1 threshold_1_49 threshold_1_50) (join 51 1 2 threshold_1_51 (join 52 1 1 threshold_1_52 threshold_1_53))))) (join 54 9 10 (join 54 4 5 (join 54 2 2 (join 54 1 1 threshold_1_54 threshold_1_55) (join 56 1 1 threshold_1_56 threshold_1_57)) (join 58 2 3 (join 58 1 1 threshold_1_58 threshold_1_59) (join 60 1 2 threshold_1_60 (join 61 1 1 threshold_1_61 threshold_1_62)))) (join 63 5 5 (join 63 2 3 (join 63 1 1 threshold_1_63 threshold_1_64) (join 65 1 2 threshold_1_65 (join 66 1 1 threshold_1_66 threshold_1_67))) (join 68 2 3 (join 68 1 1 threshold_1_68 threshold_1_69) (join 70 1 2 threshold_1_70 (join 71 1 1 threshold_1_71 threshold_1_72))))))) (join 73 36 37 (join 73 18 18 (join 73 9 9 (join 73 4 5 (join 73 2 2 (join 73 1 1 threshold_1_73 threshold_1_74) (join 75 1 1 threshold_1_75 threshold_1_76)) (join 77 2 3 (join 77 1 1 threshold_1_77 threshold_1_78) (join 79 1 2 threshold_1_79 (join 80 1 1 threshold_1_80 threshold_1_81)))) (join 82 4 5 (join 82 2 2 (join 82 1 1 threshold_1_82 threshold_1_83) (join 84 1 1 threshold_1_84 threshold_1_85)) (join 86 2 3 (join 86 1 1 threshold_1_86 threshold_1_87) (join 88 1 2 threshold_1_88 (join 89 1 1 threshold_1_89 threshold_1_90))))) (join 91 9 9 (join 91 4 5 (join 91 2 2 (join 91 1 1 threshold_1_91 threshold_1_92) (join 93 1 1 threshold_1_93 threshold_1_94)) (join 95 2 3 (join 95 1 1 threshold_1_95 threshold_1_96) (join 97 1 2 threshold_1_97 (join 98 1 1 threshold_1_98 threshold_1_99)))) (join 100 4 5 (join 100 2 2 (join 100 1 1 threshold_1_100 threshold_1_101) (join 102 1 1 threshold_1_102 threshold_1_103)) (join 104 2 3 (join 104 1 1 threshold_1_104 threshold_1_105) (join 106 1 2 threshold_1_106 (join 107 1 1 threshold_1_107 threshold_1_108)))))) (join 109 18 19 (join 109 9 9 (join 109 4 5 (join 109 2 2 (join 109 1 1 threshold_1_109 threshold_1_110) (join 111 1 1 threshold_1_111 threshold_1_112)) (join 113 2 3 (join 113 1 1 threshold_1_113 threshold_1_114) (join 115 1 2 threshold_1_115 (join 116 1 1 threshold_1_116 threshold_1_117)))) (join 118 4 5 (join 118 2 2 (join 118 1 1 threshold_1_118 threshold_1_119) (join 120 1 1 threshold_1_120 threshold_1_121)) (join 122 2 3 (join 122 1 1 threshold_1_122 threshold_1_123) (join 124 1 2 threshold_1_124 (join 125 1 1 threshold_1_125 threshold_1_126))))) (join 127 9 10 (join 127 4 5 (join 127 2 2 (join 127 1 1 threshold_1_127 threshold_1_128) (join 129 1 1 threshold_1_129 threshold_1_130)) (join 131 2 3 (join 131 1 1 threshold_1_131 threshold_1_132) (join 133 1 2 threshold_1_133 (join 134 1 1 threshold_1_134 threshold_1_135)))) (join 136 5 5 (join 136 2 3 (join 136 1 1 threshold_1_136 threshold_1_137) (join 138 1 2 threshold_1_138 (join 139 1 1 threshold_1_139 threshold_1_140))) (join 141 2 3 (join 141 1 1 threshold_1_141 threshold_1_142) (join 143 1 2 threshold_1_143 (join 144 1 1 threshold_1_144 threshold_1_145))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_1_0 : ∀ i ∈ List.range 4, LedgerAt 1 (0+i) := by decide +kernel

theorem ledger_1_4 : ∀ i ∈ List.range 4, LedgerAt 1 (4+i) := by decide +kernel

theorem ledger_1_8 : ∀ i ∈ List.range 4, LedgerAt 1 (8+i) := by decide +kernel

theorem ledger_1_12 : ∀ i ∈ List.range 4, LedgerAt 1 (12+i) := by decide +kernel

theorem ledger_1_16 : ∀ i ∈ List.range 4, LedgerAt 1 (16+i) := by decide +kernel

theorem ledger_1_20 : ∀ i ∈ List.range 4, LedgerAt 1 (20+i) := by decide +kernel

theorem ledger_1_24 : ∀ i ∈ List.range 4, LedgerAt 1 (24+i) := by decide +kernel

theorem ledger_1_28 : ∀ i ∈ List.range 4, LedgerAt 1 (28+i) := by decide +kernel

theorem ledger_1_32 : ∀ i ∈ List.range 4, LedgerAt 1 (32+i) := by decide +kernel

theorem ledger_1_36 : ∀ i ∈ List.range 4, LedgerAt 1 (36+i) := by decide +kernel

theorem ledger_1_40 : ∀ i ∈ List.range 4, LedgerAt 1 (40+i) := by decide +kernel

theorem ledger_1_44 : ∀ i ∈ List.range 4, LedgerAt 1 (44+i) := by decide +kernel

theorem ledger_1_48 : ∀ i ∈ List.range 4, LedgerAt 1 (48+i) := by decide +kernel

theorem ledger_1_52 : ∀ i ∈ List.range 4, LedgerAt 1 (52+i) := by decide +kernel

theorem ledger_1_56 : ∀ i ∈ List.range 4, LedgerAt 1 (56+i) := by decide +kernel

theorem ledger_1_60 : ∀ i ∈ List.range 4, LedgerAt 1 (60+i) := by decide +kernel

theorem ledger_1_64 : ∀ i ∈ List.range 4, LedgerAt 1 (64+i) := by decide +kernel

theorem ledger_1_68 : ∀ i ∈ List.range 4, LedgerAt 1 (68+i) := by decide +kernel

theorem ledger_1_72 : ∀ i ∈ List.range 4, LedgerAt 1 (72+i) := by decide +kernel

theorem ledger_1_76 : ∀ i ∈ List.range 4, LedgerAt 1 (76+i) := by decide +kernel

theorem ledger_1_80 : ∀ i ∈ List.range 4, LedgerAt 1 (80+i) := by decide +kernel

theorem ledger_1_84 : ∀ i ∈ List.range 4, LedgerAt 1 (84+i) := by decide +kernel

theorem ledger_1_88 : ∀ i ∈ List.range 4, LedgerAt 1 (88+i) := by decide +kernel

theorem ledger_1_92 : ∀ i ∈ List.range 4, LedgerAt 1 (92+i) := by decide +kernel

theorem ledger_1_96 : ∀ i ∈ List.range 4, LedgerAt 1 (96+i) := by decide +kernel

theorem ledger_1_100 : ∀ i ∈ List.range 4, LedgerAt 1 (100+i) := by decide +kernel

theorem ledger_1_104 : ∀ i ∈ List.range 4, LedgerAt 1 (104+i) := by decide +kernel

theorem ledger_1_108 : ∀ i ∈ List.range 4, LedgerAt 1 (108+i) := by decide +kernel

theorem ledger_1_112 : ∀ i ∈ List.range 4, LedgerAt 1 (112+i) := by decide +kernel

theorem ledger_1_116 : ∀ i ∈ List.range 4, LedgerAt 1 (116+i) := by decide +kernel

theorem ledger_1_120 : ∀ i ∈ List.range 4, LedgerAt 1 (120+i) := by decide +kernel

theorem ledger_1_124 : ∀ i ∈ List.range 4, LedgerAt 1 (124+i) := by decide +kernel

theorem ledger_1_128 : ∀ i ∈ List.range 4, LedgerAt 1 (128+i) := by decide +kernel

theorem ledger_1_132 : ∀ i ∈ List.range 4, LedgerAt 1 (132+i) := by decide +kernel

theorem ledger_1_136 : ∀ i ∈ List.range 4, LedgerAt 1 (136+i) := by decide +kernel

theorem ledger_1_140 : ∀ i ∈ List.range 4, LedgerAt 1 (140+i) := by decide +kernel

theorem ledger_1_144 : ∀ i ∈ List.range 2, LedgerAt 1 (144+i) := by decide +kernel

theorem ledger_1 (v : ℕ) (hv : v ∈ List.range 146) : LedgerAt 1 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 1 v)
  have h := (join 0 72 74 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_1_0 ledger_1_4) (join 8 4 4 ledger_1_8 ledger_1_12)) (join 16 8 12 (join 16 4 4 ledger_1_16 ledger_1_20) (join 24 4 8 ledger_1_24 (join 28 4 4 ledger_1_28 ledger_1_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_1_36 ledger_1_40) (join 44 4 4 ledger_1_44 ledger_1_48)) (join 52 8 12 (join 52 4 4 ledger_1_52 ledger_1_56) (join 60 4 8 ledger_1_60 (join 64 4 4 ledger_1_64 ledger_1_68))))) (join 72 36 38 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_1_72 ledger_1_76) (join 80 4 4 ledger_1_80 ledger_1_84)) (join 88 8 12 (join 88 4 4 ledger_1_88 ledger_1_92) (join 96 4 8 ledger_1_96 (join 100 4 4 ledger_1_100 ledger_1_104)))) (join 108 20 18 (join 108 8 12 (join 108 4 4 ledger_1_108 ledger_1_112) (join 116 4 8 ledger_1_116 (join 120 4 4 ledger_1_120 ledger_1_124))) (join 128 8 10 (join 128 4 4 ledger_1_128 ledger_1_132) (join 136 4 6 ledger_1_136 (join 140 4 2 ledger_1_140 ledger_1_144))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
