import ProximityPrize.SubmissionLower.BoundaryTailCheckedR016807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem geometry_2_0 : ∀ i ∈ List.range 4, GeometryAt 2 (0+i) := by decide +kernel

theorem geometry_2_4 : ∀ i ∈ List.range 4, GeometryAt 2 (4+i) := by decide +kernel

theorem geometry_2_8 : ∀ i ∈ List.range 4, GeometryAt 2 (8+i) := by decide +kernel

theorem geometry_2_12 : ∀ i ∈ List.range 4, GeometryAt 2 (12+i) := by decide +kernel

theorem geometry_2_16 : ∀ i ∈ List.range 4, GeometryAt 2 (16+i) := by decide +kernel

theorem geometry_2_20 : ∀ i ∈ List.range 4, GeometryAt 2 (20+i) := by decide +kernel

theorem geometry_2_24 : ∀ i ∈ List.range 4, GeometryAt 2 (24+i) := by decide +kernel

theorem geometry_2_28 : ∀ i ∈ List.range 4, GeometryAt 2 (28+i) := by decide +kernel

theorem geometry_2_32 : ∀ i ∈ List.range 4, GeometryAt 2 (32+i) := by decide +kernel

theorem geometry_2_36 : ∀ i ∈ List.range 4, GeometryAt 2 (36+i) := by decide +kernel

theorem geometry_2_40 : ∀ i ∈ List.range 4, GeometryAt 2 (40+i) := by decide +kernel

theorem geometry_2_44 : ∀ i ∈ List.range 4, GeometryAt 2 (44+i) := by decide +kernel

theorem geometry_2_48 : ∀ i ∈ List.range 4, GeometryAt 2 (48+i) := by decide +kernel

theorem geometry_2_52 : ∀ i ∈ List.range 4, GeometryAt 2 (52+i) := by decide +kernel

theorem geometry_2_56 : ∀ i ∈ List.range 4, GeometryAt 2 (56+i) := by decide +kernel

theorem geometry_2_60 : ∀ i ∈ List.range 4, GeometryAt 2 (60+i) := by decide +kernel

theorem geometry_2_64 : ∀ i ∈ List.range 4, GeometryAt 2 (64+i) := by decide +kernel

theorem geometry_2_68 : ∀ i ∈ List.range 4, GeometryAt 2 (68+i) := by decide +kernel

theorem geometry_2_72 : ∀ i ∈ List.range 4, GeometryAt 2 (72+i) := by decide +kernel

theorem geometry_2_76 : ∀ i ∈ List.range 4, GeometryAt 2 (76+i) := by decide +kernel

theorem geometry_2_80 : ∀ i ∈ List.range 4, GeometryAt 2 (80+i) := by decide +kernel

theorem geometry_2_84 : ∀ i ∈ List.range 4, GeometryAt 2 (84+i) := by decide +kernel

theorem geometry_2_88 : ∀ i ∈ List.range 4, GeometryAt 2 (88+i) := by decide +kernel

theorem geometry_2_92 : ∀ i ∈ List.range 4, GeometryAt 2 (92+i) := by decide +kernel

theorem geometry_2_96 : ∀ i ∈ List.range 4, GeometryAt 2 (96+i) := by decide +kernel

theorem geometry_2_100 : ∀ i ∈ List.range 4, GeometryAt 2 (100+i) := by decide +kernel

theorem geometry_2_104 : ∀ i ∈ List.range 4, GeometryAt 2 (104+i) := by decide +kernel

theorem geometry_2_108 : ∀ i ∈ List.range 4, GeometryAt 2 (108+i) := by decide +kernel

theorem geometry_2_112 : ∀ i ∈ List.range 4, GeometryAt 2 (112+i) := by decide +kernel

theorem geometry_2_116 : ∀ i ∈ List.range 4, GeometryAt 2 (116+i) := by decide +kernel

theorem geometry_2_120 : ∀ i ∈ List.range 4, GeometryAt 2 (120+i) := by decide +kernel

theorem geometry_2_124 : ∀ i ∈ List.range 4, GeometryAt 2 (124+i) := by decide +kernel

theorem geometry_2_128 : ∀ i ∈ List.range 4, GeometryAt 2 (128+i) := by decide +kernel

theorem geometry_2_132 : ∀ i ∈ List.range 4, GeometryAt 2 (132+i) := by decide +kernel

theorem geometry_2_136 : ∀ i ∈ List.range 4, GeometryAt 2 (136+i) := by decide +kernel

theorem geometry_2_140 : ∀ i ∈ List.range 4, GeometryAt 2 (140+i) := by decide +kernel

theorem geometry_2_144 : ∀ i ∈ List.range 1, GeometryAt 2 (144+i) := by decide +kernel

theorem geometry_2 (v : ℕ) (hv : v ∈ List.range 145) : GeometryAt 2 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 2 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 geometry_2_0 geometry_2_4) (join 8 4 4 geometry_2_8 geometry_2_12)) (join 16 8 12 (join 16 4 4 geometry_2_16 geometry_2_20) (join 24 4 8 geometry_2_24 (join 28 4 4 geometry_2_28 geometry_2_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 geometry_2_36 geometry_2_40) (join 44 4 4 geometry_2_44 geometry_2_48)) (join 52 8 12 (join 52 4 4 geometry_2_52 geometry_2_56) (join 60 4 8 geometry_2_60 (join 64 4 4 geometry_2_64 geometry_2_68))))) (join 72 36 37 (join 72 16 20 (join 72 8 8 (join 72 4 4 geometry_2_72 geometry_2_76) (join 80 4 4 geometry_2_80 geometry_2_84)) (join 88 8 12 (join 88 4 4 geometry_2_88 geometry_2_92) (join 96 4 8 geometry_2_96 (join 100 4 4 geometry_2_100 geometry_2_104)))) (join 108 20 17 (join 108 8 12 (join 108 4 4 geometry_2_108 geometry_2_112) (join 116 4 8 geometry_2_116 (join 120 4 4 geometry_2_120 geometry_2_124))) (join 128 8 9 (join 128 4 4 geometry_2_128 geometry_2_132) (join 136 4 5 geometry_2_136 (join 140 4 1 geometry_2_140 geometry_2_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_2_0 : ∀ i ∈ List.range 1, StrictAt 2 (0+i) := by decide +kernel

theorem strict_2_1 : ∀ i ∈ List.range 1, StrictAt 2 (1+i) := by decide +kernel

theorem strict_2_2 : ∀ i ∈ List.range 1, StrictAt 2 (2+i) := by decide +kernel

theorem strict_2_3 : ∀ i ∈ List.range 1, StrictAt 2 (3+i) := by decide +kernel

theorem strict_2_4 : ∀ i ∈ List.range 1, StrictAt 2 (4+i) := by decide +kernel

theorem strict_2_5 : ∀ i ∈ List.range 1, StrictAt 2 (5+i) := by decide +kernel

theorem strict_2_6 : ∀ i ∈ List.range 1, StrictAt 2 (6+i) := by decide +kernel

theorem strict_2_7 : ∀ i ∈ List.range 1, StrictAt 2 (7+i) := by decide +kernel

theorem strict_2_8 : ∀ i ∈ List.range 1, StrictAt 2 (8+i) := by decide +kernel

theorem strict_2_9 : ∀ i ∈ List.range 1, StrictAt 2 (9+i) := by decide +kernel

theorem strict_2_10 : ∀ i ∈ List.range 1, StrictAt 2 (10+i) := by decide +kernel

theorem strict_2_11 : ∀ i ∈ List.range 1, StrictAt 2 (11+i) := by decide +kernel

theorem strict_2_12 : ∀ i ∈ List.range 1, StrictAt 2 (12+i) := by decide +kernel

theorem strict_2_13 : ∀ i ∈ List.range 1, StrictAt 2 (13+i) := by decide +kernel

theorem strict_2_14 : ∀ i ∈ List.range 1, StrictAt 2 (14+i) := by decide +kernel

theorem strict_2_15 : ∀ i ∈ List.range 1, StrictAt 2 (15+i) := by decide +kernel

theorem strict_2_16 : ∀ i ∈ List.range 1, StrictAt 2 (16+i) := by decide +kernel

theorem strict_2_17 : ∀ i ∈ List.range 1, StrictAt 2 (17+i) := by decide +kernel

theorem strict_2_18 : ∀ i ∈ List.range 1, StrictAt 2 (18+i) := by decide +kernel

theorem strict_2_19 : ∀ i ∈ List.range 1, StrictAt 2 (19+i) := by decide +kernel

theorem strict_2_20 : ∀ i ∈ List.range 1, StrictAt 2 (20+i) := by decide +kernel

theorem strict_2_21 : ∀ i ∈ List.range 1, StrictAt 2 (21+i) := by decide +kernel

theorem strict_2_22 : ∀ i ∈ List.range 1, StrictAt 2 (22+i) := by decide +kernel

theorem strict_2_23 : ∀ i ∈ List.range 1, StrictAt 2 (23+i) := by decide +kernel

theorem strict_2_24 : ∀ i ∈ List.range 1, StrictAt 2 (24+i) := by decide +kernel

theorem strict_2_25 : ∀ i ∈ List.range 1, StrictAt 2 (25+i) := by decide +kernel

theorem strict_2_26 : ∀ i ∈ List.range 1, StrictAt 2 (26+i) := by decide +kernel

theorem strict_2_27 : ∀ i ∈ List.range 1, StrictAt 2 (27+i) := by decide +kernel

theorem strict_2_28 : ∀ i ∈ List.range 1, StrictAt 2 (28+i) := by decide +kernel

theorem strict_2_29 : ∀ i ∈ List.range 1, StrictAt 2 (29+i) := by decide +kernel

theorem strict_2_30 : ∀ i ∈ List.range 1, StrictAt 2 (30+i) := by decide +kernel

theorem strict_2_31 : ∀ i ∈ List.range 1, StrictAt 2 (31+i) := by decide +kernel

theorem strict_2_32 : ∀ i ∈ List.range 1, StrictAt 2 (32+i) := by decide +kernel

theorem strict_2_33 : ∀ i ∈ List.range 1, StrictAt 2 (33+i) := by decide +kernel

theorem strict_2_34 : ∀ i ∈ List.range 1, StrictAt 2 (34+i) := by decide +kernel

theorem strict_2_35 : ∀ i ∈ List.range 1, StrictAt 2 (35+i) := by decide +kernel

theorem strict_2_36 : ∀ i ∈ List.range 1, StrictAt 2 (36+i) := by decide +kernel

theorem strict_2_37 : ∀ i ∈ List.range 1, StrictAt 2 (37+i) := by decide +kernel

theorem strict_2_38 : ∀ i ∈ List.range 1, StrictAt 2 (38+i) := by decide +kernel

theorem strict_2_39 : ∀ i ∈ List.range 1, StrictAt 2 (39+i) := by decide +kernel

theorem strict_2_40 : ∀ i ∈ List.range 1, StrictAt 2 (40+i) := by decide +kernel

theorem strict_2_41 : ∀ i ∈ List.range 1, StrictAt 2 (41+i) := by decide +kernel

theorem strict_2_42 : ∀ i ∈ List.range 1, StrictAt 2 (42+i) := by decide +kernel

theorem strict_2_43 : ∀ i ∈ List.range 1, StrictAt 2 (43+i) := by decide +kernel

theorem strict_2_44 : ∀ i ∈ List.range 1, StrictAt 2 (44+i) := by decide +kernel

theorem strict_2_45 : ∀ i ∈ List.range 1, StrictAt 2 (45+i) := by decide +kernel

theorem strict_2_46 : ∀ i ∈ List.range 1, StrictAt 2 (46+i) := by decide +kernel

theorem strict_2_47 : ∀ i ∈ List.range 1, StrictAt 2 (47+i) := by decide +kernel

theorem strict_2_48 : ∀ i ∈ List.range 1, StrictAt 2 (48+i) := by decide +kernel

theorem strict_2_49 : ∀ i ∈ List.range 1, StrictAt 2 (49+i) := by decide +kernel

theorem strict_2_50 : ∀ i ∈ List.range 1, StrictAt 2 (50+i) := by decide +kernel

theorem strict_2_51 : ∀ i ∈ List.range 1, StrictAt 2 (51+i) := by decide +kernel

theorem strict_2_52 : ∀ i ∈ List.range 1, StrictAt 2 (52+i) := by decide +kernel

theorem strict_2_53 : ∀ i ∈ List.range 1, StrictAt 2 (53+i) := by decide +kernel

theorem strict_2_54 : ∀ i ∈ List.range 1, StrictAt 2 (54+i) := by decide +kernel

theorem strict_2_55 : ∀ i ∈ List.range 1, StrictAt 2 (55+i) := by decide +kernel

theorem strict_2_56 : ∀ i ∈ List.range 1, StrictAt 2 (56+i) := by decide +kernel

theorem strict_2_57 : ∀ i ∈ List.range 1, StrictAt 2 (57+i) := by decide +kernel

theorem strict_2_58 : ∀ i ∈ List.range 1, StrictAt 2 (58+i) := by decide +kernel

theorem strict_2_59 : ∀ i ∈ List.range 1, StrictAt 2 (59+i) := by decide +kernel

theorem strict_2_60 : ∀ i ∈ List.range 1, StrictAt 2 (60+i) := by decide +kernel

theorem strict_2_61 : ∀ i ∈ List.range 1, StrictAt 2 (61+i) := by decide +kernel

theorem strict_2_62 : ∀ i ∈ List.range 1, StrictAt 2 (62+i) := by decide +kernel

theorem strict_2_63 : ∀ i ∈ List.range 1, StrictAt 2 (63+i) := by decide +kernel

theorem strict_2_64 : ∀ i ∈ List.range 1, StrictAt 2 (64+i) := by decide +kernel

theorem strict_2_65 : ∀ i ∈ List.range 1, StrictAt 2 (65+i) := by decide +kernel

theorem strict_2_66 : ∀ i ∈ List.range 1, StrictAt 2 (66+i) := by decide +kernel

theorem strict_2_67 : ∀ i ∈ List.range 1, StrictAt 2 (67+i) := by decide +kernel

theorem strict_2_68 : ∀ i ∈ List.range 1, StrictAt 2 (68+i) := by decide +kernel

theorem strict_2_69 : ∀ i ∈ List.range 1, StrictAt 2 (69+i) := by decide +kernel

theorem strict_2_70 : ∀ i ∈ List.range 1, StrictAt 2 (70+i) := by decide +kernel

theorem strict_2_71 : ∀ i ∈ List.range 1, StrictAt 2 (71+i) := by decide +kernel

theorem strict_2_72 : ∀ i ∈ List.range 1, StrictAt 2 (72+i) := by decide +kernel

theorem strict_2_73 : ∀ i ∈ List.range 1, StrictAt 2 (73+i) := by decide +kernel

theorem strict_2_74 : ∀ i ∈ List.range 1, StrictAt 2 (74+i) := by decide +kernel

theorem strict_2_75 : ∀ i ∈ List.range 1, StrictAt 2 (75+i) := by decide +kernel

theorem strict_2_76 : ∀ i ∈ List.range 1, StrictAt 2 (76+i) := by decide +kernel

theorem strict_2_77 : ∀ i ∈ List.range 1, StrictAt 2 (77+i) := by decide +kernel

theorem strict_2_78 : ∀ i ∈ List.range 1, StrictAt 2 (78+i) := by decide +kernel

theorem strict_2_79 : ∀ i ∈ List.range 1, StrictAt 2 (79+i) := by decide +kernel

theorem strict_2_80 : ∀ i ∈ List.range 1, StrictAt 2 (80+i) := by decide +kernel

theorem strict_2_81 : ∀ i ∈ List.range 1, StrictAt 2 (81+i) := by decide +kernel

theorem strict_2_82 : ∀ i ∈ List.range 1, StrictAt 2 (82+i) := by decide +kernel

theorem strict_2_83 : ∀ i ∈ List.range 1, StrictAt 2 (83+i) := by decide +kernel

theorem strict_2_84 : ∀ i ∈ List.range 1, StrictAt 2 (84+i) := by decide +kernel

theorem strict_2_85 : ∀ i ∈ List.range 1, StrictAt 2 (85+i) := by decide +kernel

theorem strict_2_86 : ∀ i ∈ List.range 1, StrictAt 2 (86+i) := by decide +kernel

theorem strict_2_87 : ∀ i ∈ List.range 1, StrictAt 2 (87+i) := by decide +kernel

theorem strict_2_88 : ∀ i ∈ List.range 1, StrictAt 2 (88+i) := by decide +kernel

theorem strict_2_89 : ∀ i ∈ List.range 1, StrictAt 2 (89+i) := by decide +kernel

theorem strict_2_90 : ∀ i ∈ List.range 1, StrictAt 2 (90+i) := by decide +kernel

theorem strict_2_91 : ∀ i ∈ List.range 1, StrictAt 2 (91+i) := by decide +kernel

theorem strict_2_92 : ∀ i ∈ List.range 1, StrictAt 2 (92+i) := by decide +kernel

theorem strict_2_93 : ∀ i ∈ List.range 1, StrictAt 2 (93+i) := by decide +kernel

theorem strict_2_94 : ∀ i ∈ List.range 1, StrictAt 2 (94+i) := by decide +kernel

theorem strict_2_95 : ∀ i ∈ List.range 1, StrictAt 2 (95+i) := by decide +kernel

theorem strict_2_96 : ∀ i ∈ List.range 1, StrictAt 2 (96+i) := by decide +kernel

theorem strict_2_97 : ∀ i ∈ List.range 1, StrictAt 2 (97+i) := by decide +kernel

theorem strict_2_98 : ∀ i ∈ List.range 1, StrictAt 2 (98+i) := by decide +kernel

theorem strict_2_99 : ∀ i ∈ List.range 1, StrictAt 2 (99+i) := by decide +kernel

theorem strict_2_100 : ∀ i ∈ List.range 1, StrictAt 2 (100+i) := by decide +kernel

theorem strict_2_101 : ∀ i ∈ List.range 1, StrictAt 2 (101+i) := by decide +kernel

theorem strict_2_102 : ∀ i ∈ List.range 1, StrictAt 2 (102+i) := by decide +kernel

theorem strict_2_103 : ∀ i ∈ List.range 1, StrictAt 2 (103+i) := by decide +kernel

theorem strict_2_104 : ∀ i ∈ List.range 1, StrictAt 2 (104+i) := by decide +kernel

theorem strict_2_105 : ∀ i ∈ List.range 1, StrictAt 2 (105+i) := by decide +kernel

theorem strict_2_106 : ∀ i ∈ List.range 1, StrictAt 2 (106+i) := by decide +kernel

theorem strict_2_107 : ∀ i ∈ List.range 1, StrictAt 2 (107+i) := by decide +kernel

theorem strict_2_108 : ∀ i ∈ List.range 1, StrictAt 2 (108+i) := by decide +kernel

theorem strict_2_109 : ∀ i ∈ List.range 1, StrictAt 2 (109+i) := by decide +kernel

theorem strict_2_110 : ∀ i ∈ List.range 1, StrictAt 2 (110+i) := by decide +kernel

theorem strict_2_111 : ∀ i ∈ List.range 1, StrictAt 2 (111+i) := by decide +kernel

theorem strict_2_112 : ∀ i ∈ List.range 1, StrictAt 2 (112+i) := by decide +kernel

theorem strict_2_113 : ∀ i ∈ List.range 1, StrictAt 2 (113+i) := by decide +kernel

theorem strict_2_114 : ∀ i ∈ List.range 1, StrictAt 2 (114+i) := by decide +kernel

theorem strict_2_115 : ∀ i ∈ List.range 1, StrictAt 2 (115+i) := by decide +kernel

theorem strict_2_116 : ∀ i ∈ List.range 1, StrictAt 2 (116+i) := by decide +kernel

theorem strict_2_117 : ∀ i ∈ List.range 1, StrictAt 2 (117+i) := by decide +kernel

theorem strict_2_118 : ∀ i ∈ List.range 1, StrictAt 2 (118+i) := by decide +kernel

theorem strict_2_119 : ∀ i ∈ List.range 1, StrictAt 2 (119+i) := by decide +kernel

theorem strict_2_120 : ∀ i ∈ List.range 1, StrictAt 2 (120+i) := by decide +kernel

theorem strict_2_121 : ∀ i ∈ List.range 1, StrictAt 2 (121+i) := by decide +kernel

theorem strict_2_122 : ∀ i ∈ List.range 1, StrictAt 2 (122+i) := by decide +kernel

theorem strict_2_123 : ∀ i ∈ List.range 1, StrictAt 2 (123+i) := by decide +kernel

theorem strict_2_124 : ∀ i ∈ List.range 1, StrictAt 2 (124+i) := by decide +kernel

theorem strict_2_125 : ∀ i ∈ List.range 1, StrictAt 2 (125+i) := by decide +kernel

theorem strict_2_126 : ∀ i ∈ List.range 1, StrictAt 2 (126+i) := by decide +kernel

theorem strict_2_127 : ∀ i ∈ List.range 1, StrictAt 2 (127+i) := by decide +kernel

theorem strict_2_128 : ∀ i ∈ List.range 1, StrictAt 2 (128+i) := by decide +kernel

theorem strict_2_129 : ∀ i ∈ List.range 1, StrictAt 2 (129+i) := by decide +kernel

theorem strict_2_130 : ∀ i ∈ List.range 1, StrictAt 2 (130+i) := by decide +kernel

theorem strict_2_131 : ∀ i ∈ List.range 1, StrictAt 2 (131+i) := by decide +kernel

theorem strict_2_132 : ∀ i ∈ List.range 1, StrictAt 2 (132+i) := by decide +kernel

theorem strict_2_133 : ∀ i ∈ List.range 1, StrictAt 2 (133+i) := by decide +kernel

theorem strict_2_134 : ∀ i ∈ List.range 1, StrictAt 2 (134+i) := by decide +kernel

theorem strict_2_135 : ∀ i ∈ List.range 1, StrictAt 2 (135+i) := by decide +kernel

theorem strict_2_136 : ∀ i ∈ List.range 1, StrictAt 2 (136+i) := by decide +kernel

theorem strict_2_137 : ∀ i ∈ List.range 1, StrictAt 2 (137+i) := by decide +kernel

theorem strict_2_138 : ∀ i ∈ List.range 1, StrictAt 2 (138+i) := by decide +kernel

theorem strict_2_139 : ∀ i ∈ List.range 1, StrictAt 2 (139+i) := by decide +kernel

theorem strict_2_140 : ∀ i ∈ List.range 1, StrictAt 2 (140+i) := by decide +kernel

theorem strict_2_141 : ∀ i ∈ List.range 1, StrictAt 2 (141+i) := by decide +kernel

theorem strict_2_142 : ∀ i ∈ List.range 1, StrictAt 2 (142+i) := by decide +kernel

theorem strict_2_143 : ∀ i ∈ List.range 1, StrictAt 2 (143+i) := by decide +kernel

theorem strict_2_144 : ∀ i ∈ List.range 1, StrictAt 2 (144+i) := by decide +kernel

theorem strict_2 (v : ℕ) (hv : v ∈ List.range 145) : StrictAt 2 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 2 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 18 18 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 strict_2_0 strict_2_1) (join 2 1 1 strict_2_2 strict_2_3)) (join 4 2 3 (join 4 1 1 strict_2_4 strict_2_5) (join 6 1 2 strict_2_6 (join 7 1 1 strict_2_7 strict_2_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 strict_2_9 strict_2_10) (join 11 1 1 strict_2_11 strict_2_12)) (join 13 2 3 (join 13 1 1 strict_2_13 strict_2_14) (join 15 1 2 strict_2_15 (join 16 1 1 strict_2_16 strict_2_17))))) (join 18 9 9 (join 18 4 5 (join 18 2 2 (join 18 1 1 strict_2_18 strict_2_19) (join 20 1 1 strict_2_20 strict_2_21)) (join 22 2 3 (join 22 1 1 strict_2_22 strict_2_23) (join 24 1 2 strict_2_24 (join 25 1 1 strict_2_25 strict_2_26)))) (join 27 4 5 (join 27 2 2 (join 27 1 1 strict_2_27 strict_2_28) (join 29 1 1 strict_2_29 strict_2_30)) (join 31 2 3 (join 31 1 1 strict_2_31 strict_2_32) (join 33 1 2 strict_2_33 (join 34 1 1 strict_2_34 strict_2_35)))))) (join 36 18 18 (join 36 9 9 (join 36 4 5 (join 36 2 2 (join 36 1 1 strict_2_36 strict_2_37) (join 38 1 1 strict_2_38 strict_2_39)) (join 40 2 3 (join 40 1 1 strict_2_40 strict_2_41) (join 42 1 2 strict_2_42 (join 43 1 1 strict_2_43 strict_2_44)))) (join 45 4 5 (join 45 2 2 (join 45 1 1 strict_2_45 strict_2_46) (join 47 1 1 strict_2_47 strict_2_48)) (join 49 2 3 (join 49 1 1 strict_2_49 strict_2_50) (join 51 1 2 strict_2_51 (join 52 1 1 strict_2_52 strict_2_53))))) (join 54 9 9 (join 54 4 5 (join 54 2 2 (join 54 1 1 strict_2_54 strict_2_55) (join 56 1 1 strict_2_56 strict_2_57)) (join 58 2 3 (join 58 1 1 strict_2_58 strict_2_59) (join 60 1 2 strict_2_60 (join 61 1 1 strict_2_61 strict_2_62)))) (join 63 4 5 (join 63 2 2 (join 63 1 1 strict_2_63 strict_2_64) (join 65 1 1 strict_2_65 strict_2_66)) (join 67 2 3 (join 67 1 1 strict_2_67 strict_2_68) (join 69 1 2 strict_2_69 (join 70 1 1 strict_2_70 strict_2_71))))))) (join 72 36 37 (join 72 18 18 (join 72 9 9 (join 72 4 5 (join 72 2 2 (join 72 1 1 strict_2_72 strict_2_73) (join 74 1 1 strict_2_74 strict_2_75)) (join 76 2 3 (join 76 1 1 strict_2_76 strict_2_77) (join 78 1 2 strict_2_78 (join 79 1 1 strict_2_79 strict_2_80)))) (join 81 4 5 (join 81 2 2 (join 81 1 1 strict_2_81 strict_2_82) (join 83 1 1 strict_2_83 strict_2_84)) (join 85 2 3 (join 85 1 1 strict_2_85 strict_2_86) (join 87 1 2 strict_2_87 (join 88 1 1 strict_2_88 strict_2_89))))) (join 90 9 9 (join 90 4 5 (join 90 2 2 (join 90 1 1 strict_2_90 strict_2_91) (join 92 1 1 strict_2_92 strict_2_93)) (join 94 2 3 (join 94 1 1 strict_2_94 strict_2_95) (join 96 1 2 strict_2_96 (join 97 1 1 strict_2_97 strict_2_98)))) (join 99 4 5 (join 99 2 2 (join 99 1 1 strict_2_99 strict_2_100) (join 101 1 1 strict_2_101 strict_2_102)) (join 103 2 3 (join 103 1 1 strict_2_103 strict_2_104) (join 105 1 2 strict_2_105 (join 106 1 1 strict_2_106 strict_2_107)))))) (join 108 18 19 (join 108 9 9 (join 108 4 5 (join 108 2 2 (join 108 1 1 strict_2_108 strict_2_109) (join 110 1 1 strict_2_110 strict_2_111)) (join 112 2 3 (join 112 1 1 strict_2_112 strict_2_113) (join 114 1 2 strict_2_114 (join 115 1 1 strict_2_115 strict_2_116)))) (join 117 4 5 (join 117 2 2 (join 117 1 1 strict_2_117 strict_2_118) (join 119 1 1 strict_2_119 strict_2_120)) (join 121 2 3 (join 121 1 1 strict_2_121 strict_2_122) (join 123 1 2 strict_2_123 (join 124 1 1 strict_2_124 strict_2_125))))) (join 126 9 10 (join 126 4 5 (join 126 2 2 (join 126 1 1 strict_2_126 strict_2_127) (join 128 1 1 strict_2_128 strict_2_129)) (join 130 2 3 (join 130 1 1 strict_2_130 strict_2_131) (join 132 1 2 strict_2_132 (join 133 1 1 strict_2_133 strict_2_134)))) (join 135 5 5 (join 135 2 3 (join 135 1 1 strict_2_135 strict_2_136) (join 137 1 2 strict_2_137 (join 138 1 1 strict_2_138 strict_2_139))) (join 140 2 3 (join 140 1 1 strict_2_140 strict_2_141) (join 142 1 2 strict_2_142 (join 143 1 1 strict_2_143 strict_2_144))))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_2_0 : ∀ i ∈ List.range 4, PhaseAt 2 (0+i) := by decide +kernel

theorem phase_2_4 : ∀ i ∈ List.range 4, PhaseAt 2 (4+i) := by decide +kernel

theorem phase_2_8 : ∀ i ∈ List.range 4, PhaseAt 2 (8+i) := by decide +kernel

theorem phase_2_12 : ∀ i ∈ List.range 4, PhaseAt 2 (12+i) := by decide +kernel

theorem phase_2_16 : ∀ i ∈ List.range 4, PhaseAt 2 (16+i) := by decide +kernel

theorem phase_2_20 : ∀ i ∈ List.range 4, PhaseAt 2 (20+i) := by decide +kernel

theorem phase_2_24 : ∀ i ∈ List.range 4, PhaseAt 2 (24+i) := by decide +kernel

theorem phase_2_28 : ∀ i ∈ List.range 4, PhaseAt 2 (28+i) := by decide +kernel

theorem phase_2_32 : ∀ i ∈ List.range 4, PhaseAt 2 (32+i) := by decide +kernel

theorem phase_2_36 : ∀ i ∈ List.range 4, PhaseAt 2 (36+i) := by decide +kernel

theorem phase_2_40 : ∀ i ∈ List.range 4, PhaseAt 2 (40+i) := by decide +kernel

theorem phase_2_44 : ∀ i ∈ List.range 4, PhaseAt 2 (44+i) := by decide +kernel

theorem phase_2_48 : ∀ i ∈ List.range 4, PhaseAt 2 (48+i) := by decide +kernel

theorem phase_2_52 : ∀ i ∈ List.range 4, PhaseAt 2 (52+i) := by decide +kernel

theorem phase_2_56 : ∀ i ∈ List.range 4, PhaseAt 2 (56+i) := by decide +kernel

theorem phase_2_60 : ∀ i ∈ List.range 4, PhaseAt 2 (60+i) := by decide +kernel

theorem phase_2_64 : ∀ i ∈ List.range 4, PhaseAt 2 (64+i) := by decide +kernel

theorem phase_2_68 : ∀ i ∈ List.range 4, PhaseAt 2 (68+i) := by decide +kernel

theorem phase_2_72 : ∀ i ∈ List.range 4, PhaseAt 2 (72+i) := by decide +kernel

theorem phase_2_76 : ∀ i ∈ List.range 4, PhaseAt 2 (76+i) := by decide +kernel

theorem phase_2_80 : ∀ i ∈ List.range 4, PhaseAt 2 (80+i) := by decide +kernel

theorem phase_2_84 : ∀ i ∈ List.range 4, PhaseAt 2 (84+i) := by decide +kernel

theorem phase_2_88 : ∀ i ∈ List.range 4, PhaseAt 2 (88+i) := by decide +kernel

theorem phase_2_92 : ∀ i ∈ List.range 4, PhaseAt 2 (92+i) := by decide +kernel

theorem phase_2_96 : ∀ i ∈ List.range 4, PhaseAt 2 (96+i) := by decide +kernel

theorem phase_2_100 : ∀ i ∈ List.range 4, PhaseAt 2 (100+i) := by decide +kernel

theorem phase_2_104 : ∀ i ∈ List.range 4, PhaseAt 2 (104+i) := by decide +kernel

theorem phase_2_108 : ∀ i ∈ List.range 4, PhaseAt 2 (108+i) := by decide +kernel

theorem phase_2_112 : ∀ i ∈ List.range 4, PhaseAt 2 (112+i) := by decide +kernel

theorem phase_2_116 : ∀ i ∈ List.range 4, PhaseAt 2 (116+i) := by decide +kernel

theorem phase_2_120 : ∀ i ∈ List.range 4, PhaseAt 2 (120+i) := by decide +kernel

theorem phase_2_124 : ∀ i ∈ List.range 4, PhaseAt 2 (124+i) := by decide +kernel

theorem phase_2_128 : ∀ i ∈ List.range 4, PhaseAt 2 (128+i) := by decide +kernel

theorem phase_2_132 : ∀ i ∈ List.range 4, PhaseAt 2 (132+i) := by decide +kernel

theorem phase_2_136 : ∀ i ∈ List.range 4, PhaseAt 2 (136+i) := by decide +kernel

theorem phase_2_140 : ∀ i ∈ List.range 4, PhaseAt 2 (140+i) := by decide +kernel

theorem phase_2_144 : ∀ i ∈ List.range 1, PhaseAt 2 (144+i) := by decide +kernel

theorem phase_2 (v : ℕ) (hv : v ∈ List.range 145) : PhaseAt 2 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 2 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_2_0 phase_2_4) (join 8 4 4 phase_2_8 phase_2_12)) (join 16 8 12 (join 16 4 4 phase_2_16 phase_2_20) (join 24 4 8 phase_2_24 (join 28 4 4 phase_2_28 phase_2_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_2_36 phase_2_40) (join 44 4 4 phase_2_44 phase_2_48)) (join 52 8 12 (join 52 4 4 phase_2_52 phase_2_56) (join 60 4 8 phase_2_60 (join 64 4 4 phase_2_64 phase_2_68))))) (join 72 36 37 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_2_72 phase_2_76) (join 80 4 4 phase_2_80 phase_2_84)) (join 88 8 12 (join 88 4 4 phase_2_88 phase_2_92) (join 96 4 8 phase_2_96 (join 100 4 4 phase_2_100 phase_2_104)))) (join 108 20 17 (join 108 8 12 (join 108 4 4 phase_2_108 phase_2_112) (join 116 4 8 phase_2_116 (join 120 4 4 phase_2_120 phase_2_124))) (join 128 8 9 (join 128 4 4 phase_2_128 phase_2_132) (join 136 4 5 phase_2_136 (join 140 4 1 phase_2_140 phase_2_144))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_2_0 : ∀ i ∈ List.range 1, ThresholdAt 2 (0+i) := by decide +kernel

theorem threshold_2_1 : ∀ i ∈ List.range 1, ThresholdAt 2 (1+i) := by decide +kernel

theorem threshold_2_2 : ∀ i ∈ List.range 1, ThresholdAt 2 (2+i) := by decide +kernel

theorem threshold_2_3 : ∀ i ∈ List.range 1, ThresholdAt 2 (3+i) := by decide +kernel

theorem threshold_2_4 : ∀ i ∈ List.range 1, ThresholdAt 2 (4+i) := by decide +kernel

theorem threshold_2_5 : ∀ i ∈ List.range 1, ThresholdAt 2 (5+i) := by decide +kernel

theorem threshold_2_6 : ∀ i ∈ List.range 1, ThresholdAt 2 (6+i) := by decide +kernel

theorem threshold_2_7 : ∀ i ∈ List.range 1, ThresholdAt 2 (7+i) := by decide +kernel

theorem threshold_2_8 : ∀ i ∈ List.range 1, ThresholdAt 2 (8+i) := by decide +kernel

theorem threshold_2_9 : ∀ i ∈ List.range 1, ThresholdAt 2 (9+i) := by decide +kernel

theorem threshold_2_10 : ∀ i ∈ List.range 1, ThresholdAt 2 (10+i) := by decide +kernel

theorem threshold_2_11 : ∀ i ∈ List.range 1, ThresholdAt 2 (11+i) := by decide +kernel

theorem threshold_2_12 : ∀ i ∈ List.range 1, ThresholdAt 2 (12+i) := by decide +kernel

theorem threshold_2_13 : ∀ i ∈ List.range 1, ThresholdAt 2 (13+i) := by decide +kernel

theorem threshold_2_14 : ∀ i ∈ List.range 1, ThresholdAt 2 (14+i) := by decide +kernel

theorem threshold_2_15 : ∀ i ∈ List.range 1, ThresholdAt 2 (15+i) := by decide +kernel

theorem threshold_2_16 : ∀ i ∈ List.range 1, ThresholdAt 2 (16+i) := by decide +kernel

theorem threshold_2_17 : ∀ i ∈ List.range 1, ThresholdAt 2 (17+i) := by decide +kernel

theorem threshold_2_18 : ∀ i ∈ List.range 1, ThresholdAt 2 (18+i) := by decide +kernel

theorem threshold_2_19 : ∀ i ∈ List.range 1, ThresholdAt 2 (19+i) := by decide +kernel

theorem threshold_2_20 : ∀ i ∈ List.range 1, ThresholdAt 2 (20+i) := by decide +kernel

theorem threshold_2_21 : ∀ i ∈ List.range 1, ThresholdAt 2 (21+i) := by decide +kernel

theorem threshold_2_22 : ∀ i ∈ List.range 1, ThresholdAt 2 (22+i) := by decide +kernel

theorem threshold_2_23 : ∀ i ∈ List.range 1, ThresholdAt 2 (23+i) := by decide +kernel

theorem threshold_2_24 : ∀ i ∈ List.range 1, ThresholdAt 2 (24+i) := by decide +kernel

theorem threshold_2_25 : ∀ i ∈ List.range 1, ThresholdAt 2 (25+i) := by decide +kernel

theorem threshold_2_26 : ∀ i ∈ List.range 1, ThresholdAt 2 (26+i) := by decide +kernel

theorem threshold_2_27 : ∀ i ∈ List.range 1, ThresholdAt 2 (27+i) := by decide +kernel

theorem threshold_2_28 : ∀ i ∈ List.range 1, ThresholdAt 2 (28+i) := by decide +kernel

theorem threshold_2_29 : ∀ i ∈ List.range 1, ThresholdAt 2 (29+i) := by decide +kernel

theorem threshold_2_30 : ∀ i ∈ List.range 1, ThresholdAt 2 (30+i) := by decide +kernel

theorem threshold_2_31 : ∀ i ∈ List.range 1, ThresholdAt 2 (31+i) := by decide +kernel

theorem threshold_2_32 : ∀ i ∈ List.range 1, ThresholdAt 2 (32+i) := by decide +kernel

theorem threshold_2_33 : ∀ i ∈ List.range 1, ThresholdAt 2 (33+i) := by decide +kernel

theorem threshold_2_34 : ∀ i ∈ List.range 1, ThresholdAt 2 (34+i) := by decide +kernel

theorem threshold_2_35 : ∀ i ∈ List.range 1, ThresholdAt 2 (35+i) := by decide +kernel

theorem threshold_2_36 : ∀ i ∈ List.range 1, ThresholdAt 2 (36+i) := by decide +kernel

theorem threshold_2_37 : ∀ i ∈ List.range 1, ThresholdAt 2 (37+i) := by decide +kernel

theorem threshold_2_38 : ∀ i ∈ List.range 1, ThresholdAt 2 (38+i) := by decide +kernel

theorem threshold_2_39 : ∀ i ∈ List.range 1, ThresholdAt 2 (39+i) := by decide +kernel

theorem threshold_2_40 : ∀ i ∈ List.range 1, ThresholdAt 2 (40+i) := by decide +kernel

theorem threshold_2_41 : ∀ i ∈ List.range 1, ThresholdAt 2 (41+i) := by decide +kernel

theorem threshold_2_42 : ∀ i ∈ List.range 1, ThresholdAt 2 (42+i) := by decide +kernel

theorem threshold_2_43 : ∀ i ∈ List.range 1, ThresholdAt 2 (43+i) := by decide +kernel

theorem threshold_2_44 : ∀ i ∈ List.range 1, ThresholdAt 2 (44+i) := by decide +kernel

theorem threshold_2_45 : ∀ i ∈ List.range 1, ThresholdAt 2 (45+i) := by decide +kernel

theorem threshold_2_46 : ∀ i ∈ List.range 1, ThresholdAt 2 (46+i) := by decide +kernel

theorem threshold_2_47 : ∀ i ∈ List.range 1, ThresholdAt 2 (47+i) := by decide +kernel

theorem threshold_2_48 : ∀ i ∈ List.range 1, ThresholdAt 2 (48+i) := by decide +kernel

theorem threshold_2_49 : ∀ i ∈ List.range 1, ThresholdAt 2 (49+i) := by decide +kernel

theorem threshold_2_50 : ∀ i ∈ List.range 1, ThresholdAt 2 (50+i) := by decide +kernel

theorem threshold_2_51 : ∀ i ∈ List.range 1, ThresholdAt 2 (51+i) := by decide +kernel

theorem threshold_2_52 : ∀ i ∈ List.range 1, ThresholdAt 2 (52+i) := by decide +kernel

theorem threshold_2_53 : ∀ i ∈ List.range 1, ThresholdAt 2 (53+i) := by decide +kernel

theorem threshold_2_54 : ∀ i ∈ List.range 1, ThresholdAt 2 (54+i) := by decide +kernel

theorem threshold_2_55 : ∀ i ∈ List.range 1, ThresholdAt 2 (55+i) := by decide +kernel

theorem threshold_2_56 : ∀ i ∈ List.range 1, ThresholdAt 2 (56+i) := by decide +kernel

theorem threshold_2_57 : ∀ i ∈ List.range 1, ThresholdAt 2 (57+i) := by decide +kernel

theorem threshold_2_58 : ∀ i ∈ List.range 1, ThresholdAt 2 (58+i) := by decide +kernel

theorem threshold_2_59 : ∀ i ∈ List.range 1, ThresholdAt 2 (59+i) := by decide +kernel

theorem threshold_2_60 : ∀ i ∈ List.range 1, ThresholdAt 2 (60+i) := by decide +kernel

theorem threshold_2_61 : ∀ i ∈ List.range 1, ThresholdAt 2 (61+i) := by decide +kernel

theorem threshold_2_62 : ∀ i ∈ List.range 1, ThresholdAt 2 (62+i) := by decide +kernel

theorem threshold_2_63 : ∀ i ∈ List.range 1, ThresholdAt 2 (63+i) := by decide +kernel

theorem threshold_2_64 : ∀ i ∈ List.range 1, ThresholdAt 2 (64+i) := by decide +kernel

theorem threshold_2_65 : ∀ i ∈ List.range 1, ThresholdAt 2 (65+i) := by decide +kernel

theorem threshold_2_66 : ∀ i ∈ List.range 1, ThresholdAt 2 (66+i) := by decide +kernel

theorem threshold_2_67 : ∀ i ∈ List.range 1, ThresholdAt 2 (67+i) := by decide +kernel

theorem threshold_2_68 : ∀ i ∈ List.range 1, ThresholdAt 2 (68+i) := by decide +kernel

theorem threshold_2_69 : ∀ i ∈ List.range 1, ThresholdAt 2 (69+i) := by decide +kernel

theorem threshold_2_70 : ∀ i ∈ List.range 1, ThresholdAt 2 (70+i) := by decide +kernel

theorem threshold_2_71 : ∀ i ∈ List.range 1, ThresholdAt 2 (71+i) := by decide +kernel

theorem threshold_2_72 : ∀ i ∈ List.range 1, ThresholdAt 2 (72+i) := by decide +kernel

theorem threshold_2_73 : ∀ i ∈ List.range 1, ThresholdAt 2 (73+i) := by decide +kernel

theorem threshold_2_74 : ∀ i ∈ List.range 1, ThresholdAt 2 (74+i) := by decide +kernel

theorem threshold_2_75 : ∀ i ∈ List.range 1, ThresholdAt 2 (75+i) := by decide +kernel

theorem threshold_2_76 : ∀ i ∈ List.range 1, ThresholdAt 2 (76+i) := by decide +kernel

theorem threshold_2_77 : ∀ i ∈ List.range 1, ThresholdAt 2 (77+i) := by decide +kernel

theorem threshold_2_78 : ∀ i ∈ List.range 1, ThresholdAt 2 (78+i) := by decide +kernel

theorem threshold_2_79 : ∀ i ∈ List.range 1, ThresholdAt 2 (79+i) := by decide +kernel

theorem threshold_2_80 : ∀ i ∈ List.range 1, ThresholdAt 2 (80+i) := by decide +kernel

theorem threshold_2_81 : ∀ i ∈ List.range 1, ThresholdAt 2 (81+i) := by decide +kernel

theorem threshold_2_82 : ∀ i ∈ List.range 1, ThresholdAt 2 (82+i) := by decide +kernel

theorem threshold_2_83 : ∀ i ∈ List.range 1, ThresholdAt 2 (83+i) := by decide +kernel

theorem threshold_2_84 : ∀ i ∈ List.range 1, ThresholdAt 2 (84+i) := by decide +kernel

theorem threshold_2_85 : ∀ i ∈ List.range 1, ThresholdAt 2 (85+i) := by decide +kernel

theorem threshold_2_86 : ∀ i ∈ List.range 1, ThresholdAt 2 (86+i) := by decide +kernel

theorem threshold_2_87 : ∀ i ∈ List.range 1, ThresholdAt 2 (87+i) := by decide +kernel

theorem threshold_2_88 : ∀ i ∈ List.range 1, ThresholdAt 2 (88+i) := by decide +kernel

theorem threshold_2_89 : ∀ i ∈ List.range 1, ThresholdAt 2 (89+i) := by decide +kernel

theorem threshold_2_90 : ∀ i ∈ List.range 1, ThresholdAt 2 (90+i) := by decide +kernel

theorem threshold_2_91 : ∀ i ∈ List.range 1, ThresholdAt 2 (91+i) := by decide +kernel

theorem threshold_2_92 : ∀ i ∈ List.range 1, ThresholdAt 2 (92+i) := by decide +kernel

theorem threshold_2_93 : ∀ i ∈ List.range 1, ThresholdAt 2 (93+i) := by decide +kernel

theorem threshold_2_94 : ∀ i ∈ List.range 1, ThresholdAt 2 (94+i) := by decide +kernel

theorem threshold_2_95 : ∀ i ∈ List.range 1, ThresholdAt 2 (95+i) := by decide +kernel

theorem threshold_2_96 : ∀ i ∈ List.range 1, ThresholdAt 2 (96+i) := by decide +kernel

theorem threshold_2_97 : ∀ i ∈ List.range 1, ThresholdAt 2 (97+i) := by decide +kernel

theorem threshold_2_98 : ∀ i ∈ List.range 1, ThresholdAt 2 (98+i) := by decide +kernel

theorem threshold_2_99 : ∀ i ∈ List.range 1, ThresholdAt 2 (99+i) := by decide +kernel

theorem threshold_2_100 : ∀ i ∈ List.range 1, ThresholdAt 2 (100+i) := by decide +kernel

theorem threshold_2_101 : ∀ i ∈ List.range 1, ThresholdAt 2 (101+i) := by decide +kernel

theorem threshold_2_102 : ∀ i ∈ List.range 1, ThresholdAt 2 (102+i) := by decide +kernel

theorem threshold_2_103 : ∀ i ∈ List.range 1, ThresholdAt 2 (103+i) := by decide +kernel

theorem threshold_2_104 : ∀ i ∈ List.range 1, ThresholdAt 2 (104+i) := by decide +kernel

theorem threshold_2_105 : ∀ i ∈ List.range 1, ThresholdAt 2 (105+i) := by decide +kernel

theorem threshold_2_106 : ∀ i ∈ List.range 1, ThresholdAt 2 (106+i) := by decide +kernel

theorem threshold_2_107 : ∀ i ∈ List.range 1, ThresholdAt 2 (107+i) := by decide +kernel

theorem threshold_2_108 : ∀ i ∈ List.range 1, ThresholdAt 2 (108+i) := by decide +kernel

theorem threshold_2_109 : ∀ i ∈ List.range 1, ThresholdAt 2 (109+i) := by decide +kernel

theorem threshold_2_110 : ∀ i ∈ List.range 1, ThresholdAt 2 (110+i) := by decide +kernel

theorem threshold_2_111 : ∀ i ∈ List.range 1, ThresholdAt 2 (111+i) := by decide +kernel

theorem threshold_2_112 : ∀ i ∈ List.range 1, ThresholdAt 2 (112+i) := by decide +kernel

theorem threshold_2_113 : ∀ i ∈ List.range 1, ThresholdAt 2 (113+i) := by decide +kernel

theorem threshold_2_114 : ∀ i ∈ List.range 1, ThresholdAt 2 (114+i) := by decide +kernel

theorem threshold_2_115 : ∀ i ∈ List.range 1, ThresholdAt 2 (115+i) := by decide +kernel

theorem threshold_2_116 : ∀ i ∈ List.range 1, ThresholdAt 2 (116+i) := by decide +kernel

theorem threshold_2_117 : ∀ i ∈ List.range 1, ThresholdAt 2 (117+i) := by decide +kernel

theorem threshold_2_118 : ∀ i ∈ List.range 1, ThresholdAt 2 (118+i) := by decide +kernel

theorem threshold_2_119 : ∀ i ∈ List.range 1, ThresholdAt 2 (119+i) := by decide +kernel

theorem threshold_2_120 : ∀ i ∈ List.range 1, ThresholdAt 2 (120+i) := by decide +kernel

theorem threshold_2_121 : ∀ i ∈ List.range 1, ThresholdAt 2 (121+i) := by decide +kernel

theorem threshold_2_122 : ∀ i ∈ List.range 1, ThresholdAt 2 (122+i) := by decide +kernel

theorem threshold_2_123 : ∀ i ∈ List.range 1, ThresholdAt 2 (123+i) := by decide +kernel

theorem threshold_2_124 : ∀ i ∈ List.range 1, ThresholdAt 2 (124+i) := by decide +kernel

theorem threshold_2_125 : ∀ i ∈ List.range 1, ThresholdAt 2 (125+i) := by decide +kernel

theorem threshold_2_126 : ∀ i ∈ List.range 1, ThresholdAt 2 (126+i) := by decide +kernel

theorem threshold_2_127 : ∀ i ∈ List.range 1, ThresholdAt 2 (127+i) := by decide +kernel

theorem threshold_2_128 : ∀ i ∈ List.range 1, ThresholdAt 2 (128+i) := by decide +kernel

theorem threshold_2_129 : ∀ i ∈ List.range 1, ThresholdAt 2 (129+i) := by decide +kernel

theorem threshold_2_130 : ∀ i ∈ List.range 1, ThresholdAt 2 (130+i) := by decide +kernel

theorem threshold_2_131 : ∀ i ∈ List.range 1, ThresholdAt 2 (131+i) := by decide +kernel

theorem threshold_2_132 : ∀ i ∈ List.range 1, ThresholdAt 2 (132+i) := by decide +kernel

theorem threshold_2_133 : ∀ i ∈ List.range 1, ThresholdAt 2 (133+i) := by decide +kernel

theorem threshold_2_134 : ∀ i ∈ List.range 1, ThresholdAt 2 (134+i) := by decide +kernel

theorem threshold_2_135 : ∀ i ∈ List.range 1, ThresholdAt 2 (135+i) := by decide +kernel

theorem threshold_2_136 : ∀ i ∈ List.range 1, ThresholdAt 2 (136+i) := by decide +kernel

theorem threshold_2_137 : ∀ i ∈ List.range 1, ThresholdAt 2 (137+i) := by decide +kernel

theorem threshold_2_138 : ∀ i ∈ List.range 1, ThresholdAt 2 (138+i) := by decide +kernel

theorem threshold_2_139 : ∀ i ∈ List.range 1, ThresholdAt 2 (139+i) := by decide +kernel

theorem threshold_2_140 : ∀ i ∈ List.range 1, ThresholdAt 2 (140+i) := by decide +kernel

theorem threshold_2_141 : ∀ i ∈ List.range 1, ThresholdAt 2 (141+i) := by decide +kernel

theorem threshold_2_142 : ∀ i ∈ List.range 1, ThresholdAt 2 (142+i) := by decide +kernel

theorem threshold_2_143 : ∀ i ∈ List.range 1, ThresholdAt 2 (143+i) := by decide +kernel

theorem threshold_2_144 : ∀ i ∈ List.range 1, ThresholdAt 2 (144+i) := by decide +kernel

theorem threshold_2 (v : ℕ) (hv : v ∈ List.range 145) : ThresholdAt 2 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 2 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 18 18 (join 0 9 9 (join 0 4 5 (join 0 2 2 (join 0 1 1 threshold_2_0 threshold_2_1) (join 2 1 1 threshold_2_2 threshold_2_3)) (join 4 2 3 (join 4 1 1 threshold_2_4 threshold_2_5) (join 6 1 2 threshold_2_6 (join 7 1 1 threshold_2_7 threshold_2_8)))) (join 9 4 5 (join 9 2 2 (join 9 1 1 threshold_2_9 threshold_2_10) (join 11 1 1 threshold_2_11 threshold_2_12)) (join 13 2 3 (join 13 1 1 threshold_2_13 threshold_2_14) (join 15 1 2 threshold_2_15 (join 16 1 1 threshold_2_16 threshold_2_17))))) (join 18 9 9 (join 18 4 5 (join 18 2 2 (join 18 1 1 threshold_2_18 threshold_2_19) (join 20 1 1 threshold_2_20 threshold_2_21)) (join 22 2 3 (join 22 1 1 threshold_2_22 threshold_2_23) (join 24 1 2 threshold_2_24 (join 25 1 1 threshold_2_25 threshold_2_26)))) (join 27 4 5 (join 27 2 2 (join 27 1 1 threshold_2_27 threshold_2_28) (join 29 1 1 threshold_2_29 threshold_2_30)) (join 31 2 3 (join 31 1 1 threshold_2_31 threshold_2_32) (join 33 1 2 threshold_2_33 (join 34 1 1 threshold_2_34 threshold_2_35)))))) (join 36 18 18 (join 36 9 9 (join 36 4 5 (join 36 2 2 (join 36 1 1 threshold_2_36 threshold_2_37) (join 38 1 1 threshold_2_38 threshold_2_39)) (join 40 2 3 (join 40 1 1 threshold_2_40 threshold_2_41) (join 42 1 2 threshold_2_42 (join 43 1 1 threshold_2_43 threshold_2_44)))) (join 45 4 5 (join 45 2 2 (join 45 1 1 threshold_2_45 threshold_2_46) (join 47 1 1 threshold_2_47 threshold_2_48)) (join 49 2 3 (join 49 1 1 threshold_2_49 threshold_2_50) (join 51 1 2 threshold_2_51 (join 52 1 1 threshold_2_52 threshold_2_53))))) (join 54 9 9 (join 54 4 5 (join 54 2 2 (join 54 1 1 threshold_2_54 threshold_2_55) (join 56 1 1 threshold_2_56 threshold_2_57)) (join 58 2 3 (join 58 1 1 threshold_2_58 threshold_2_59) (join 60 1 2 threshold_2_60 (join 61 1 1 threshold_2_61 threshold_2_62)))) (join 63 4 5 (join 63 2 2 (join 63 1 1 threshold_2_63 threshold_2_64) (join 65 1 1 threshold_2_65 threshold_2_66)) (join 67 2 3 (join 67 1 1 threshold_2_67 threshold_2_68) (join 69 1 2 threshold_2_69 (join 70 1 1 threshold_2_70 threshold_2_71))))))) (join 72 36 37 (join 72 18 18 (join 72 9 9 (join 72 4 5 (join 72 2 2 (join 72 1 1 threshold_2_72 threshold_2_73) (join 74 1 1 threshold_2_74 threshold_2_75)) (join 76 2 3 (join 76 1 1 threshold_2_76 threshold_2_77) (join 78 1 2 threshold_2_78 (join 79 1 1 threshold_2_79 threshold_2_80)))) (join 81 4 5 (join 81 2 2 (join 81 1 1 threshold_2_81 threshold_2_82) (join 83 1 1 threshold_2_83 threshold_2_84)) (join 85 2 3 (join 85 1 1 threshold_2_85 threshold_2_86) (join 87 1 2 threshold_2_87 (join 88 1 1 threshold_2_88 threshold_2_89))))) (join 90 9 9 (join 90 4 5 (join 90 2 2 (join 90 1 1 threshold_2_90 threshold_2_91) (join 92 1 1 threshold_2_92 threshold_2_93)) (join 94 2 3 (join 94 1 1 threshold_2_94 threshold_2_95) (join 96 1 2 threshold_2_96 (join 97 1 1 threshold_2_97 threshold_2_98)))) (join 99 4 5 (join 99 2 2 (join 99 1 1 threshold_2_99 threshold_2_100) (join 101 1 1 threshold_2_101 threshold_2_102)) (join 103 2 3 (join 103 1 1 threshold_2_103 threshold_2_104) (join 105 1 2 threshold_2_105 (join 106 1 1 threshold_2_106 threshold_2_107)))))) (join 108 18 19 (join 108 9 9 (join 108 4 5 (join 108 2 2 (join 108 1 1 threshold_2_108 threshold_2_109) (join 110 1 1 threshold_2_110 threshold_2_111)) (join 112 2 3 (join 112 1 1 threshold_2_112 threshold_2_113) (join 114 1 2 threshold_2_114 (join 115 1 1 threshold_2_115 threshold_2_116)))) (join 117 4 5 (join 117 2 2 (join 117 1 1 threshold_2_117 threshold_2_118) (join 119 1 1 threshold_2_119 threshold_2_120)) (join 121 2 3 (join 121 1 1 threshold_2_121 threshold_2_122) (join 123 1 2 threshold_2_123 (join 124 1 1 threshold_2_124 threshold_2_125))))) (join 126 9 10 (join 126 4 5 (join 126 2 2 (join 126 1 1 threshold_2_126 threshold_2_127) (join 128 1 1 threshold_2_128 threshold_2_129)) (join 130 2 3 (join 130 1 1 threshold_2_130 threshold_2_131) (join 132 1 2 threshold_2_132 (join 133 1 1 threshold_2_133 threshold_2_134)))) (join 135 5 5 (join 135 2 3 (join 135 1 1 threshold_2_135 threshold_2_136) (join 137 1 2 threshold_2_137 (join 138 1 1 threshold_2_138 threshold_2_139))) (join 140 2 3 (join 140 1 1 threshold_2_140 threshold_2_141) (join 142 1 2 threshold_2_142 (join 143 1 1 threshold_2_143 threshold_2_144))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_2_0 : ∀ i ∈ List.range 4, LedgerAt 2 (0+i) := by decide +kernel

theorem ledger_2_4 : ∀ i ∈ List.range 4, LedgerAt 2 (4+i) := by decide +kernel

theorem ledger_2_8 : ∀ i ∈ List.range 4, LedgerAt 2 (8+i) := by decide +kernel

theorem ledger_2_12 : ∀ i ∈ List.range 4, LedgerAt 2 (12+i) := by decide +kernel

theorem ledger_2_16 : ∀ i ∈ List.range 4, LedgerAt 2 (16+i) := by decide +kernel

theorem ledger_2_20 : ∀ i ∈ List.range 4, LedgerAt 2 (20+i) := by decide +kernel

theorem ledger_2_24 : ∀ i ∈ List.range 4, LedgerAt 2 (24+i) := by decide +kernel

theorem ledger_2_28 : ∀ i ∈ List.range 4, LedgerAt 2 (28+i) := by decide +kernel

theorem ledger_2_32 : ∀ i ∈ List.range 4, LedgerAt 2 (32+i) := by decide +kernel

theorem ledger_2_36 : ∀ i ∈ List.range 4, LedgerAt 2 (36+i) := by decide +kernel

theorem ledger_2_40 : ∀ i ∈ List.range 4, LedgerAt 2 (40+i) := by decide +kernel

theorem ledger_2_44 : ∀ i ∈ List.range 4, LedgerAt 2 (44+i) := by decide +kernel

theorem ledger_2_48 : ∀ i ∈ List.range 4, LedgerAt 2 (48+i) := by decide +kernel

theorem ledger_2_52 : ∀ i ∈ List.range 4, LedgerAt 2 (52+i) := by decide +kernel

theorem ledger_2_56 : ∀ i ∈ List.range 4, LedgerAt 2 (56+i) := by decide +kernel

theorem ledger_2_60 : ∀ i ∈ List.range 4, LedgerAt 2 (60+i) := by decide +kernel

theorem ledger_2_64 : ∀ i ∈ List.range 4, LedgerAt 2 (64+i) := by decide +kernel

theorem ledger_2_68 : ∀ i ∈ List.range 4, LedgerAt 2 (68+i) := by decide +kernel

theorem ledger_2_72 : ∀ i ∈ List.range 4, LedgerAt 2 (72+i) := by decide +kernel

theorem ledger_2_76 : ∀ i ∈ List.range 4, LedgerAt 2 (76+i) := by decide +kernel

theorem ledger_2_80 : ∀ i ∈ List.range 4, LedgerAt 2 (80+i) := by decide +kernel

theorem ledger_2_84 : ∀ i ∈ List.range 4, LedgerAt 2 (84+i) := by decide +kernel

theorem ledger_2_88 : ∀ i ∈ List.range 4, LedgerAt 2 (88+i) := by decide +kernel

theorem ledger_2_92 : ∀ i ∈ List.range 4, LedgerAt 2 (92+i) := by decide +kernel

theorem ledger_2_96 : ∀ i ∈ List.range 4, LedgerAt 2 (96+i) := by decide +kernel

theorem ledger_2_100 : ∀ i ∈ List.range 4, LedgerAt 2 (100+i) := by decide +kernel

theorem ledger_2_104 : ∀ i ∈ List.range 4, LedgerAt 2 (104+i) := by decide +kernel

theorem ledger_2_108 : ∀ i ∈ List.range 4, LedgerAt 2 (108+i) := by decide +kernel

theorem ledger_2_112 : ∀ i ∈ List.range 4, LedgerAt 2 (112+i) := by decide +kernel

theorem ledger_2_116 : ∀ i ∈ List.range 4, LedgerAt 2 (116+i) := by decide +kernel

theorem ledger_2_120 : ∀ i ∈ List.range 4, LedgerAt 2 (120+i) := by decide +kernel

theorem ledger_2_124 : ∀ i ∈ List.range 4, LedgerAt 2 (124+i) := by decide +kernel

theorem ledger_2_128 : ∀ i ∈ List.range 4, LedgerAt 2 (128+i) := by decide +kernel

theorem ledger_2_132 : ∀ i ∈ List.range 4, LedgerAt 2 (132+i) := by decide +kernel

theorem ledger_2_136 : ∀ i ∈ List.range 4, LedgerAt 2 (136+i) := by decide +kernel

theorem ledger_2_140 : ∀ i ∈ List.range 4, LedgerAt 2 (140+i) := by decide +kernel

theorem ledger_2_144 : ∀ i ∈ List.range 1, LedgerAt 2 (144+i) := by decide +kernel

theorem ledger_2 (v : ℕ) (hv : v ∈ List.range 145) : LedgerAt 2 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 2 v)
  have h := (join 0 72 73 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_2_0 ledger_2_4) (join 8 4 4 ledger_2_8 ledger_2_12)) (join 16 8 12 (join 16 4 4 ledger_2_16 ledger_2_20) (join 24 4 8 ledger_2_24 (join 28 4 4 ledger_2_28 ledger_2_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_2_36 ledger_2_40) (join 44 4 4 ledger_2_44 ledger_2_48)) (join 52 8 12 (join 52 4 4 ledger_2_52 ledger_2_56) (join 60 4 8 ledger_2_60 (join 64 4 4 ledger_2_64 ledger_2_68))))) (join 72 36 37 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_2_72 ledger_2_76) (join 80 4 4 ledger_2_80 ledger_2_84)) (join 88 8 12 (join 88 4 4 ledger_2_88 ledger_2_92) (join 96 4 8 ledger_2_96 (join 100 4 4 ledger_2_100 ledger_2_104)))) (join 108 20 17 (join 108 8 12 (join 108 4 4 ledger_2_108 ledger_2_112) (join 116 4 8 ledger_2_116 (join 120 4 4 ledger_2_120 ledger_2_124))) (join 128 8 9 (join 128 4 4 ledger_2_128 ledger_2_132) (join 136 4 5 ledger_2_136 (join 140 4 1 ledger_2_140 ledger_2_144))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
