import ProximityPrize.SubmissionLower.BoundaryTailCheckedR046807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_5_0 : ∀ i ∈ List.range 4, GeometryAt 5 (0+i) := by decide +kernel

theorem geometry_5_4 : ∀ i ∈ List.range 4, GeometryAt 5 (4+i) := by decide +kernel

theorem geometry_5_8 : ∀ i ∈ List.range 4, GeometryAt 5 (8+i) := by decide +kernel

theorem geometry_5_12 : ∀ i ∈ List.range 4, GeometryAt 5 (12+i) := by decide +kernel

theorem geometry_5_16 : ∀ i ∈ List.range 4, GeometryAt 5 (16+i) := by decide +kernel

theorem geometry_5_20 : ∀ i ∈ List.range 4, GeometryAt 5 (20+i) := by decide +kernel

theorem geometry_5_24 : ∀ i ∈ List.range 4, GeometryAt 5 (24+i) := by decide +kernel

theorem geometry_5_28 : ∀ i ∈ List.range 4, GeometryAt 5 (28+i) := by decide +kernel

theorem geometry_5_32 : ∀ i ∈ List.range 4, GeometryAt 5 (32+i) := by decide +kernel

theorem geometry_5_36 : ∀ i ∈ List.range 4, GeometryAt 5 (36+i) := by decide +kernel

theorem geometry_5_40 : ∀ i ∈ List.range 4, GeometryAt 5 (40+i) := by decide +kernel

theorem geometry_5_44 : ∀ i ∈ List.range 4, GeometryAt 5 (44+i) := by decide +kernel

theorem geometry_5_48 : ∀ i ∈ List.range 4, GeometryAt 5 (48+i) := by decide +kernel

theorem geometry_5_52 : ∀ i ∈ List.range 4, GeometryAt 5 (52+i) := by decide +kernel

theorem geometry_5_56 : ∀ i ∈ List.range 4, GeometryAt 5 (56+i) := by decide +kernel

theorem geometry_5_60 : ∀ i ∈ List.range 4, GeometryAt 5 (60+i) := by decide +kernel

theorem geometry_5_64 : ∀ i ∈ List.range 4, GeometryAt 5 (64+i) := by decide +kernel

theorem geometry_5_68 : ∀ i ∈ List.range 4, GeometryAt 5 (68+i) := by decide +kernel

theorem geometry_5_72 : ∀ i ∈ List.range 4, GeometryAt 5 (72+i) := by decide +kernel

theorem geometry_5_76 : ∀ i ∈ List.range 4, GeometryAt 5 (76+i) := by decide +kernel

theorem geometry_5_80 : ∀ i ∈ List.range 4, GeometryAt 5 (80+i) := by decide +kernel

theorem geometry_5_84 : ∀ i ∈ List.range 4, GeometryAt 5 (84+i) := by decide +kernel

theorem geometry_5_88 : ∀ i ∈ List.range 4, GeometryAt 5 (88+i) := by decide +kernel

theorem geometry_5_92 : ∀ i ∈ List.range 4, GeometryAt 5 (92+i) := by decide +kernel

theorem geometry_5_96 : ∀ i ∈ List.range 4, GeometryAt 5 (96+i) := by decide +kernel

theorem geometry_5_100 : ∀ i ∈ List.range 4, GeometryAt 5 (100+i) := by decide +kernel

theorem geometry_5_104 : ∀ i ∈ List.range 4, GeometryAt 5 (104+i) := by decide +kernel

theorem geometry_5_108 : ∀ i ∈ List.range 4, GeometryAt 5 (108+i) := by decide +kernel

theorem geometry_5_112 : ∀ i ∈ List.range 4, GeometryAt 5 (112+i) := by decide +kernel

theorem geometry_5_116 : ∀ i ∈ List.range 4, GeometryAt 5 (116+i) := by decide +kernel

theorem geometry_5_120 : ∀ i ∈ List.range 4, GeometryAt 5 (120+i) := by decide +kernel

theorem geometry_5_124 : ∀ i ∈ List.range 4, GeometryAt 5 (124+i) := by decide +kernel

theorem geometry_5_128 : ∀ i ∈ List.range 4, GeometryAt 5 (128+i) := by decide +kernel

theorem geometry_5_132 : ∀ i ∈ List.range 4, GeometryAt 5 (132+i) := by decide +kernel

theorem geometry_5_136 : ∀ i ∈ List.range 4, GeometryAt 5 (136+i) := by decide +kernel

theorem geometry_5_140 : ∀ i ∈ List.range 2, GeometryAt 5 (140+i) := by decide +kernel

theorem geometry_5 (v : ℕ) (hv : v ∈ List.range 142) : GeometryAt 5 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 5 v)
  have h := (join 0 72 70 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 geometry_5_0 geometry_5_4) (join 8 4 4 geometry_5_8 geometry_5_12)) (join 16 8 12 (join 16 4 4 geometry_5_16 geometry_5_20) (join 24 4 8 geometry_5_24 (join 28 4 4 geometry_5_28 geometry_5_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 geometry_5_36 geometry_5_40) (join 44 4 4 geometry_5_44 geometry_5_48)) (join 52 8 12 (join 52 4 4 geometry_5_52 geometry_5_56) (join 60 4 8 geometry_5_60 (join 64 4 4 geometry_5_64 geometry_5_68))))) (join 72 36 34 (join 72 16 20 (join 72 8 8 (join 72 4 4 geometry_5_72 geometry_5_76) (join 80 4 4 geometry_5_80 geometry_5_84)) (join 88 8 12 (join 88 4 4 geometry_5_88 geometry_5_92) (join 96 4 8 geometry_5_96 (join 100 4 4 geometry_5_100 geometry_5_104)))) (join 108 16 18 (join 108 8 8 (join 108 4 4 geometry_5_108 geometry_5_112) (join 116 4 4 geometry_5_116 geometry_5_120)) (join 124 8 10 (join 124 4 4 geometry_5_124 geometry_5_128) (join 132 4 6 geometry_5_132 (join 136 4 2 geometry_5_136 geometry_5_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_5_0 : ∀ i ∈ List.range 1, StrictAt 5 (0+i) := by decide +kernel

theorem strict_5_1 : ∀ i ∈ List.range 1, StrictAt 5 (1+i) := by decide +kernel

theorem strict_5_2 : ∀ i ∈ List.range 1, StrictAt 5 (2+i) := by decide +kernel

theorem strict_5_3 : ∀ i ∈ List.range 1, StrictAt 5 (3+i) := by decide +kernel

theorem strict_5_4 : ∀ i ∈ List.range 1, StrictAt 5 (4+i) := by decide +kernel

theorem strict_5_5 : ∀ i ∈ List.range 1, StrictAt 5 (5+i) := by decide +kernel

theorem strict_5_6 : ∀ i ∈ List.range 1, StrictAt 5 (6+i) := by decide +kernel

theorem strict_5_7 : ∀ i ∈ List.range 1, StrictAt 5 (7+i) := by decide +kernel

theorem strict_5_8 : ∀ i ∈ List.range 1, StrictAt 5 (8+i) := by decide +kernel

theorem strict_5_9 : ∀ i ∈ List.range 1, StrictAt 5 (9+i) := by decide +kernel

theorem strict_5_10 : ∀ i ∈ List.range 1, StrictAt 5 (10+i) := by decide +kernel

theorem strict_5_11 : ∀ i ∈ List.range 1, StrictAt 5 (11+i) := by decide +kernel

theorem strict_5_12 : ∀ i ∈ List.range 1, StrictAt 5 (12+i) := by decide +kernel

theorem strict_5_13 : ∀ i ∈ List.range 1, StrictAt 5 (13+i) := by decide +kernel

theorem strict_5_14 : ∀ i ∈ List.range 1, StrictAt 5 (14+i) := by decide +kernel

theorem strict_5_15 : ∀ i ∈ List.range 1, StrictAt 5 (15+i) := by decide +kernel

theorem strict_5_16 : ∀ i ∈ List.range 1, StrictAt 5 (16+i) := by decide +kernel

theorem strict_5_17 : ∀ i ∈ List.range 1, StrictAt 5 (17+i) := by decide +kernel

theorem strict_5_18 : ∀ i ∈ List.range 1, StrictAt 5 (18+i) := by decide +kernel

theorem strict_5_19 : ∀ i ∈ List.range 1, StrictAt 5 (19+i) := by decide +kernel

theorem strict_5_20 : ∀ i ∈ List.range 1, StrictAt 5 (20+i) := by decide +kernel

theorem strict_5_21 : ∀ i ∈ List.range 1, StrictAt 5 (21+i) := by decide +kernel

theorem strict_5_22 : ∀ i ∈ List.range 1, StrictAt 5 (22+i) := by decide +kernel

theorem strict_5_23 : ∀ i ∈ List.range 1, StrictAt 5 (23+i) := by decide +kernel

theorem strict_5_24 : ∀ i ∈ List.range 1, StrictAt 5 (24+i) := by decide +kernel

theorem strict_5_25 : ∀ i ∈ List.range 1, StrictAt 5 (25+i) := by decide +kernel

theorem strict_5_26 : ∀ i ∈ List.range 1, StrictAt 5 (26+i) := by decide +kernel

theorem strict_5_27 : ∀ i ∈ List.range 1, StrictAt 5 (27+i) := by decide +kernel

theorem strict_5_28 : ∀ i ∈ List.range 1, StrictAt 5 (28+i) := by decide +kernel

theorem strict_5_29 : ∀ i ∈ List.range 1, StrictAt 5 (29+i) := by decide +kernel

theorem strict_5_30 : ∀ i ∈ List.range 1, StrictAt 5 (30+i) := by decide +kernel

theorem strict_5_31 : ∀ i ∈ List.range 1, StrictAt 5 (31+i) := by decide +kernel

theorem strict_5_32 : ∀ i ∈ List.range 1, StrictAt 5 (32+i) := by decide +kernel

theorem strict_5_33 : ∀ i ∈ List.range 1, StrictAt 5 (33+i) := by decide +kernel

theorem strict_5_34 : ∀ i ∈ List.range 1, StrictAt 5 (34+i) := by decide +kernel

theorem strict_5_35 : ∀ i ∈ List.range 1, StrictAt 5 (35+i) := by decide +kernel

theorem strict_5_36 : ∀ i ∈ List.range 1, StrictAt 5 (36+i) := by decide +kernel

theorem strict_5_37 : ∀ i ∈ List.range 1, StrictAt 5 (37+i) := by decide +kernel

theorem strict_5_38 : ∀ i ∈ List.range 1, StrictAt 5 (38+i) := by decide +kernel

theorem strict_5_39 : ∀ i ∈ List.range 1, StrictAt 5 (39+i) := by decide +kernel

theorem strict_5_40 : ∀ i ∈ List.range 1, StrictAt 5 (40+i) := by decide +kernel

theorem strict_5_41 : ∀ i ∈ List.range 1, StrictAt 5 (41+i) := by decide +kernel

theorem strict_5_42 : ∀ i ∈ List.range 1, StrictAt 5 (42+i) := by decide +kernel

theorem strict_5_43 : ∀ i ∈ List.range 1, StrictAt 5 (43+i) := by decide +kernel

theorem strict_5_44 : ∀ i ∈ List.range 1, StrictAt 5 (44+i) := by decide +kernel

theorem strict_5_45 : ∀ i ∈ List.range 1, StrictAt 5 (45+i) := by decide +kernel

theorem strict_5_46 : ∀ i ∈ List.range 1, StrictAt 5 (46+i) := by decide +kernel

theorem strict_5_47 : ∀ i ∈ List.range 1, StrictAt 5 (47+i) := by decide +kernel

theorem strict_5_48 : ∀ i ∈ List.range 1, StrictAt 5 (48+i) := by decide +kernel

theorem strict_5_49 : ∀ i ∈ List.range 1, StrictAt 5 (49+i) := by decide +kernel

theorem strict_5_50 : ∀ i ∈ List.range 1, StrictAt 5 (50+i) := by decide +kernel

theorem strict_5_51 : ∀ i ∈ List.range 1, StrictAt 5 (51+i) := by decide +kernel

theorem strict_5_52 : ∀ i ∈ List.range 1, StrictAt 5 (52+i) := by decide +kernel

theorem strict_5_53 : ∀ i ∈ List.range 1, StrictAt 5 (53+i) := by decide +kernel

theorem strict_5_54 : ∀ i ∈ List.range 1, StrictAt 5 (54+i) := by decide +kernel

theorem strict_5_55 : ∀ i ∈ List.range 1, StrictAt 5 (55+i) := by decide +kernel

theorem strict_5_56 : ∀ i ∈ List.range 1, StrictAt 5 (56+i) := by decide +kernel

theorem strict_5_57 : ∀ i ∈ List.range 1, StrictAt 5 (57+i) := by decide +kernel

theorem strict_5_58 : ∀ i ∈ List.range 1, StrictAt 5 (58+i) := by decide +kernel

theorem strict_5_59 : ∀ i ∈ List.range 1, StrictAt 5 (59+i) := by decide +kernel

theorem strict_5_60 : ∀ i ∈ List.range 1, StrictAt 5 (60+i) := by decide +kernel

theorem strict_5_61 : ∀ i ∈ List.range 1, StrictAt 5 (61+i) := by decide +kernel

theorem strict_5_62 : ∀ i ∈ List.range 1, StrictAt 5 (62+i) := by decide +kernel

theorem strict_5_63 : ∀ i ∈ List.range 1, StrictAt 5 (63+i) := by decide +kernel

theorem strict_5_64 : ∀ i ∈ List.range 1, StrictAt 5 (64+i) := by decide +kernel

theorem strict_5_65 : ∀ i ∈ List.range 1, StrictAt 5 (65+i) := by decide +kernel

theorem strict_5_66 : ∀ i ∈ List.range 1, StrictAt 5 (66+i) := by decide +kernel

theorem strict_5_67 : ∀ i ∈ List.range 1, StrictAt 5 (67+i) := by decide +kernel

theorem strict_5_68 : ∀ i ∈ List.range 1, StrictAt 5 (68+i) := by decide +kernel

theorem strict_5_69 : ∀ i ∈ List.range 1, StrictAt 5 (69+i) := by decide +kernel

theorem strict_5_70 : ∀ i ∈ List.range 1, StrictAt 5 (70+i) := by decide +kernel

theorem strict_5_71 : ∀ i ∈ List.range 1, StrictAt 5 (71+i) := by decide +kernel

theorem strict_5_72 : ∀ i ∈ List.range 1, StrictAt 5 (72+i) := by decide +kernel

theorem strict_5_73 : ∀ i ∈ List.range 1, StrictAt 5 (73+i) := by decide +kernel

theorem strict_5_74 : ∀ i ∈ List.range 1, StrictAt 5 (74+i) := by decide +kernel

theorem strict_5_75 : ∀ i ∈ List.range 1, StrictAt 5 (75+i) := by decide +kernel

theorem strict_5_76 : ∀ i ∈ List.range 1, StrictAt 5 (76+i) := by decide +kernel

theorem strict_5_77 : ∀ i ∈ List.range 1, StrictAt 5 (77+i) := by decide +kernel

theorem strict_5_78 : ∀ i ∈ List.range 1, StrictAt 5 (78+i) := by decide +kernel

theorem strict_5_79 : ∀ i ∈ List.range 1, StrictAt 5 (79+i) := by decide +kernel

theorem strict_5_80 : ∀ i ∈ List.range 1, StrictAt 5 (80+i) := by decide +kernel

theorem strict_5_81 : ∀ i ∈ List.range 1, StrictAt 5 (81+i) := by decide +kernel

theorem strict_5_82 : ∀ i ∈ List.range 1, StrictAt 5 (82+i) := by decide +kernel

theorem strict_5_83 : ∀ i ∈ List.range 1, StrictAt 5 (83+i) := by decide +kernel

theorem strict_5_84 : ∀ i ∈ List.range 1, StrictAt 5 (84+i) := by decide +kernel

theorem strict_5_85 : ∀ i ∈ List.range 1, StrictAt 5 (85+i) := by decide +kernel

theorem strict_5_86 : ∀ i ∈ List.range 1, StrictAt 5 (86+i) := by decide +kernel

theorem strict_5_87 : ∀ i ∈ List.range 1, StrictAt 5 (87+i) := by decide +kernel

theorem strict_5_88 : ∀ i ∈ List.range 1, StrictAt 5 (88+i) := by decide +kernel

theorem strict_5_89 : ∀ i ∈ List.range 1, StrictAt 5 (89+i) := by decide +kernel

theorem strict_5_90 : ∀ i ∈ List.range 1, StrictAt 5 (90+i) := by decide +kernel

theorem strict_5_91 : ∀ i ∈ List.range 1, StrictAt 5 (91+i) := by decide +kernel

theorem strict_5_92 : ∀ i ∈ List.range 1, StrictAt 5 (92+i) := by decide +kernel

theorem strict_5_93 : ∀ i ∈ List.range 1, StrictAt 5 (93+i) := by decide +kernel

theorem strict_5_94 : ∀ i ∈ List.range 1, StrictAt 5 (94+i) := by decide +kernel

theorem strict_5_95 : ∀ i ∈ List.range 1, StrictAt 5 (95+i) := by decide +kernel

theorem strict_5_96 : ∀ i ∈ List.range 1, StrictAt 5 (96+i) := by decide +kernel

theorem strict_5_97 : ∀ i ∈ List.range 1, StrictAt 5 (97+i) := by decide +kernel

theorem strict_5_98 : ∀ i ∈ List.range 1, StrictAt 5 (98+i) := by decide +kernel

theorem strict_5_99 : ∀ i ∈ List.range 1, StrictAt 5 (99+i) := by decide +kernel

theorem strict_5_100 : ∀ i ∈ List.range 1, StrictAt 5 (100+i) := by decide +kernel

theorem strict_5_101 : ∀ i ∈ List.range 1, StrictAt 5 (101+i) := by decide +kernel

theorem strict_5_102 : ∀ i ∈ List.range 1, StrictAt 5 (102+i) := by decide +kernel

theorem strict_5_103 : ∀ i ∈ List.range 1, StrictAt 5 (103+i) := by decide +kernel

theorem strict_5_104 : ∀ i ∈ List.range 1, StrictAt 5 (104+i) := by decide +kernel

theorem strict_5_105 : ∀ i ∈ List.range 1, StrictAt 5 (105+i) := by decide +kernel

theorem strict_5_106 : ∀ i ∈ List.range 1, StrictAt 5 (106+i) := by decide +kernel

theorem strict_5_107 : ∀ i ∈ List.range 1, StrictAt 5 (107+i) := by decide +kernel

theorem strict_5_108 : ∀ i ∈ List.range 1, StrictAt 5 (108+i) := by decide +kernel

theorem strict_5_109 : ∀ i ∈ List.range 1, StrictAt 5 (109+i) := by decide +kernel

theorem strict_5_110 : ∀ i ∈ List.range 1, StrictAt 5 (110+i) := by decide +kernel

theorem strict_5_111 : ∀ i ∈ List.range 1, StrictAt 5 (111+i) := by decide +kernel

theorem strict_5_112 : ∀ i ∈ List.range 1, StrictAt 5 (112+i) := by decide +kernel

theorem strict_5_113 : ∀ i ∈ List.range 1, StrictAt 5 (113+i) := by decide +kernel

theorem strict_5_114 : ∀ i ∈ List.range 1, StrictAt 5 (114+i) := by decide +kernel

theorem strict_5_115 : ∀ i ∈ List.range 1, StrictAt 5 (115+i) := by decide +kernel

theorem strict_5_116 : ∀ i ∈ List.range 1, StrictAt 5 (116+i) := by decide +kernel

theorem strict_5_117 : ∀ i ∈ List.range 1, StrictAt 5 (117+i) := by decide +kernel

theorem strict_5_118 : ∀ i ∈ List.range 1, StrictAt 5 (118+i) := by decide +kernel

theorem strict_5_119 : ∀ i ∈ List.range 1, StrictAt 5 (119+i) := by decide +kernel

theorem strict_5_120 : ∀ i ∈ List.range 1, StrictAt 5 (120+i) := by decide +kernel

theorem strict_5_121 : ∀ i ∈ List.range 1, StrictAt 5 (121+i) := by decide +kernel

theorem strict_5_122 : ∀ i ∈ List.range 1, StrictAt 5 (122+i) := by decide +kernel

theorem strict_5_123 : ∀ i ∈ List.range 1, StrictAt 5 (123+i) := by decide +kernel

theorem strict_5_124 : ∀ i ∈ List.range 1, StrictAt 5 (124+i) := by decide +kernel

theorem strict_5_125 : ∀ i ∈ List.range 1, StrictAt 5 (125+i) := by decide +kernel

theorem strict_5_126 : ∀ i ∈ List.range 1, StrictAt 5 (126+i) := by decide +kernel

theorem strict_5_127 : ∀ i ∈ List.range 1, StrictAt 5 (127+i) := by decide +kernel

theorem strict_5_128 : ∀ i ∈ List.range 1, StrictAt 5 (128+i) := by decide +kernel

theorem strict_5_129 : ∀ i ∈ List.range 1, StrictAt 5 (129+i) := by decide +kernel

theorem strict_5_130 : ∀ i ∈ List.range 1, StrictAt 5 (130+i) := by decide +kernel

theorem strict_5_131 : ∀ i ∈ List.range 1, StrictAt 5 (131+i) := by decide +kernel

theorem strict_5_132 : ∀ i ∈ List.range 1, StrictAt 5 (132+i) := by decide +kernel

theorem strict_5_133 : ∀ i ∈ List.range 1, StrictAt 5 (133+i) := by decide +kernel

theorem strict_5_134 : ∀ i ∈ List.range 1, StrictAt 5 (134+i) := by decide +kernel

theorem strict_5_135 : ∀ i ∈ List.range 1, StrictAt 5 (135+i) := by decide +kernel

theorem strict_5_136 : ∀ i ∈ List.range 1, StrictAt 5 (136+i) := by decide +kernel

theorem strict_5_137 : ∀ i ∈ List.range 1, StrictAt 5 (137+i) := by decide +kernel

theorem strict_5_138 : ∀ i ∈ List.range 1, StrictAt 5 (138+i) := by decide +kernel

theorem strict_5_139 : ∀ i ∈ List.range 1, StrictAt 5 (139+i) := by decide +kernel

theorem strict_5_140 : ∀ i ∈ List.range 1, StrictAt 5 (140+i) := by decide +kernel

theorem strict_5_141 : ∀ i ∈ List.range 1, StrictAt 5 (141+i) := by decide +kernel

theorem strict_5 (v : ℕ) (hv : v ∈ List.range 142) : StrictAt 5 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 5 v)
  have h := (join 0 71 71 (join 0 35 36 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 strict_5_0 strict_5_1) (join 2 1 1 strict_5_2 strict_5_3)) (join 4 2 2 (join 4 1 1 strict_5_4 strict_5_5) (join 6 1 1 strict_5_6 strict_5_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 strict_5_8 strict_5_9) (join 10 1 1 strict_5_10 strict_5_11)) (join 12 2 3 (join 12 1 1 strict_5_12 strict_5_13) (join 14 1 2 strict_5_14 (join 15 1 1 strict_5_15 strict_5_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 strict_5_17 strict_5_18) (join 19 1 1 strict_5_19 strict_5_20)) (join 21 2 3 (join 21 1 1 strict_5_21 strict_5_22) (join 23 1 2 strict_5_23 (join 24 1 1 strict_5_24 strict_5_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 strict_5_26 strict_5_27) (join 28 1 1 strict_5_28 strict_5_29)) (join 30 2 3 (join 30 1 1 strict_5_30 strict_5_31) (join 32 1 2 strict_5_32 (join 33 1 1 strict_5_33 strict_5_34)))))) (join 35 18 18 (join 35 9 9 (join 35 4 5 (join 35 2 2 (join 35 1 1 strict_5_35 strict_5_36) (join 37 1 1 strict_5_37 strict_5_38)) (join 39 2 3 (join 39 1 1 strict_5_39 strict_5_40) (join 41 1 2 strict_5_41 (join 42 1 1 strict_5_42 strict_5_43)))) (join 44 4 5 (join 44 2 2 (join 44 1 1 strict_5_44 strict_5_45) (join 46 1 1 strict_5_46 strict_5_47)) (join 48 2 3 (join 48 1 1 strict_5_48 strict_5_49) (join 50 1 2 strict_5_50 (join 51 1 1 strict_5_51 strict_5_52))))) (join 53 9 9 (join 53 4 5 (join 53 2 2 (join 53 1 1 strict_5_53 strict_5_54) (join 55 1 1 strict_5_55 strict_5_56)) (join 57 2 3 (join 57 1 1 strict_5_57 strict_5_58) (join 59 1 2 strict_5_59 (join 60 1 1 strict_5_60 strict_5_61)))) (join 62 4 5 (join 62 2 2 (join 62 1 1 strict_5_62 strict_5_63) (join 64 1 1 strict_5_64 strict_5_65)) (join 66 2 3 (join 66 1 1 strict_5_66 strict_5_67) (join 68 1 2 strict_5_68 (join 69 1 1 strict_5_69 strict_5_70))))))) (join 71 35 36 (join 71 17 18 (join 71 8 9 (join 71 4 4 (join 71 2 2 (join 71 1 1 strict_5_71 strict_5_72) (join 73 1 1 strict_5_73 strict_5_74)) (join 75 2 2 (join 75 1 1 strict_5_75 strict_5_76) (join 77 1 1 strict_5_77 strict_5_78))) (join 79 4 5 (join 79 2 2 (join 79 1 1 strict_5_79 strict_5_80) (join 81 1 1 strict_5_81 strict_5_82)) (join 83 2 3 (join 83 1 1 strict_5_83 strict_5_84) (join 85 1 2 strict_5_85 (join 86 1 1 strict_5_86 strict_5_87))))) (join 88 9 9 (join 88 4 5 (join 88 2 2 (join 88 1 1 strict_5_88 strict_5_89) (join 90 1 1 strict_5_90 strict_5_91)) (join 92 2 3 (join 92 1 1 strict_5_92 strict_5_93) (join 94 1 2 strict_5_94 (join 95 1 1 strict_5_95 strict_5_96)))) (join 97 4 5 (join 97 2 2 (join 97 1 1 strict_5_97 strict_5_98) (join 99 1 1 strict_5_99 strict_5_100)) (join 101 2 3 (join 101 1 1 strict_5_101 strict_5_102) (join 103 1 2 strict_5_103 (join 104 1 1 strict_5_104 strict_5_105)))))) (join 106 18 18 (join 106 9 9 (join 106 4 5 (join 106 2 2 (join 106 1 1 strict_5_106 strict_5_107) (join 108 1 1 strict_5_108 strict_5_109)) (join 110 2 3 (join 110 1 1 strict_5_110 strict_5_111) (join 112 1 2 strict_5_112 (join 113 1 1 strict_5_113 strict_5_114)))) (join 115 4 5 (join 115 2 2 (join 115 1 1 strict_5_115 strict_5_116) (join 117 1 1 strict_5_117 strict_5_118)) (join 119 2 3 (join 119 1 1 strict_5_119 strict_5_120) (join 121 1 2 strict_5_121 (join 122 1 1 strict_5_122 strict_5_123))))) (join 124 9 9 (join 124 4 5 (join 124 2 2 (join 124 1 1 strict_5_124 strict_5_125) (join 126 1 1 strict_5_126 strict_5_127)) (join 128 2 3 (join 128 1 1 strict_5_128 strict_5_129) (join 130 1 2 strict_5_130 (join 131 1 1 strict_5_131 strict_5_132)))) (join 133 4 5 (join 133 2 2 (join 133 1 1 strict_5_133 strict_5_134) (join 135 1 1 strict_5_135 strict_5_136)) (join 137 2 3 (join 137 1 1 strict_5_137 strict_5_138) (join 139 1 2 strict_5_139 (join 140 1 1 strict_5_140 strict_5_141))))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_5_0 : ∀ i ∈ List.range 4, PhaseAt 5 (0+i) := by decide +kernel

theorem phase_5_4 : ∀ i ∈ List.range 4, PhaseAt 5 (4+i) := by decide +kernel

theorem phase_5_8 : ∀ i ∈ List.range 4, PhaseAt 5 (8+i) := by decide +kernel

theorem phase_5_12 : ∀ i ∈ List.range 4, PhaseAt 5 (12+i) := by decide +kernel

theorem phase_5_16 : ∀ i ∈ List.range 4, PhaseAt 5 (16+i) := by decide +kernel

theorem phase_5_20 : ∀ i ∈ List.range 4, PhaseAt 5 (20+i) := by decide +kernel

theorem phase_5_24 : ∀ i ∈ List.range 4, PhaseAt 5 (24+i) := by decide +kernel

theorem phase_5_28 : ∀ i ∈ List.range 4, PhaseAt 5 (28+i) := by decide +kernel

theorem phase_5_32 : ∀ i ∈ List.range 4, PhaseAt 5 (32+i) := by decide +kernel

theorem phase_5_36 : ∀ i ∈ List.range 4, PhaseAt 5 (36+i) := by decide +kernel

theorem phase_5_40 : ∀ i ∈ List.range 4, PhaseAt 5 (40+i) := by decide +kernel

theorem phase_5_44 : ∀ i ∈ List.range 4, PhaseAt 5 (44+i) := by decide +kernel

theorem phase_5_48 : ∀ i ∈ List.range 4, PhaseAt 5 (48+i) := by decide +kernel

theorem phase_5_52 : ∀ i ∈ List.range 4, PhaseAt 5 (52+i) := by decide +kernel

theorem phase_5_56 : ∀ i ∈ List.range 4, PhaseAt 5 (56+i) := by decide +kernel

theorem phase_5_60 : ∀ i ∈ List.range 4, PhaseAt 5 (60+i) := by decide +kernel

theorem phase_5_64 : ∀ i ∈ List.range 4, PhaseAt 5 (64+i) := by decide +kernel

theorem phase_5_68 : ∀ i ∈ List.range 4, PhaseAt 5 (68+i) := by decide +kernel

theorem phase_5_72 : ∀ i ∈ List.range 4, PhaseAt 5 (72+i) := by decide +kernel

theorem phase_5_76 : ∀ i ∈ List.range 4, PhaseAt 5 (76+i) := by decide +kernel

theorem phase_5_80 : ∀ i ∈ List.range 4, PhaseAt 5 (80+i) := by decide +kernel

theorem phase_5_84 : ∀ i ∈ List.range 4, PhaseAt 5 (84+i) := by decide +kernel

theorem phase_5_88 : ∀ i ∈ List.range 4, PhaseAt 5 (88+i) := by decide +kernel

theorem phase_5_92 : ∀ i ∈ List.range 4, PhaseAt 5 (92+i) := by decide +kernel

theorem phase_5_96 : ∀ i ∈ List.range 4, PhaseAt 5 (96+i) := by decide +kernel

theorem phase_5_100 : ∀ i ∈ List.range 4, PhaseAt 5 (100+i) := by decide +kernel

theorem phase_5_104 : ∀ i ∈ List.range 4, PhaseAt 5 (104+i) := by decide +kernel

theorem phase_5_108 : ∀ i ∈ List.range 4, PhaseAt 5 (108+i) := by decide +kernel

theorem phase_5_112 : ∀ i ∈ List.range 4, PhaseAt 5 (112+i) := by decide +kernel

theorem phase_5_116 : ∀ i ∈ List.range 4, PhaseAt 5 (116+i) := by decide +kernel

theorem phase_5_120 : ∀ i ∈ List.range 4, PhaseAt 5 (120+i) := by decide +kernel

theorem phase_5_124 : ∀ i ∈ List.range 4, PhaseAt 5 (124+i) := by decide +kernel

theorem phase_5_128 : ∀ i ∈ List.range 4, PhaseAt 5 (128+i) := by decide +kernel

theorem phase_5_132 : ∀ i ∈ List.range 4, PhaseAt 5 (132+i) := by decide +kernel

theorem phase_5_136 : ∀ i ∈ List.range 4, PhaseAt 5 (136+i) := by decide +kernel

theorem phase_5_140 : ∀ i ∈ List.range 2, PhaseAt 5 (140+i) := by decide +kernel

theorem phase_5 (v : ℕ) (hv : v ∈ List.range 142) : PhaseAt 5 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 5 v)
  have h := (join 0 72 70 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 phase_5_0 phase_5_4) (join 8 4 4 phase_5_8 phase_5_12)) (join 16 8 12 (join 16 4 4 phase_5_16 phase_5_20) (join 24 4 8 phase_5_24 (join 28 4 4 phase_5_28 phase_5_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 phase_5_36 phase_5_40) (join 44 4 4 phase_5_44 phase_5_48)) (join 52 8 12 (join 52 4 4 phase_5_52 phase_5_56) (join 60 4 8 phase_5_60 (join 64 4 4 phase_5_64 phase_5_68))))) (join 72 36 34 (join 72 16 20 (join 72 8 8 (join 72 4 4 phase_5_72 phase_5_76) (join 80 4 4 phase_5_80 phase_5_84)) (join 88 8 12 (join 88 4 4 phase_5_88 phase_5_92) (join 96 4 8 phase_5_96 (join 100 4 4 phase_5_100 phase_5_104)))) (join 108 16 18 (join 108 8 8 (join 108 4 4 phase_5_108 phase_5_112) (join 116 4 4 phase_5_116 phase_5_120)) (join 124 8 10 (join 124 4 4 phase_5_124 phase_5_128) (join 132 4 6 phase_5_132 (join 136 4 2 phase_5_136 phase_5_140))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_5_0 : ∀ i ∈ List.range 1, ThresholdAt 5 (0+i) := by decide +kernel

theorem threshold_5_1 : ∀ i ∈ List.range 1, ThresholdAt 5 (1+i) := by decide +kernel

theorem threshold_5_2 : ∀ i ∈ List.range 1, ThresholdAt 5 (2+i) := by decide +kernel

theorem threshold_5_3 : ∀ i ∈ List.range 1, ThresholdAt 5 (3+i) := by decide +kernel

theorem threshold_5_4 : ∀ i ∈ List.range 1, ThresholdAt 5 (4+i) := by decide +kernel

theorem threshold_5_5 : ∀ i ∈ List.range 1, ThresholdAt 5 (5+i) := by decide +kernel

theorem threshold_5_6 : ∀ i ∈ List.range 1, ThresholdAt 5 (6+i) := by decide +kernel

theorem threshold_5_7 : ∀ i ∈ List.range 1, ThresholdAt 5 (7+i) := by decide +kernel

theorem threshold_5_8 : ∀ i ∈ List.range 1, ThresholdAt 5 (8+i) := by decide +kernel

theorem threshold_5_9 : ∀ i ∈ List.range 1, ThresholdAt 5 (9+i) := by decide +kernel

theorem threshold_5_10 : ∀ i ∈ List.range 1, ThresholdAt 5 (10+i) := by decide +kernel

theorem threshold_5_11 : ∀ i ∈ List.range 1, ThresholdAt 5 (11+i) := by decide +kernel

theorem threshold_5_12 : ∀ i ∈ List.range 1, ThresholdAt 5 (12+i) := by decide +kernel

theorem threshold_5_13 : ∀ i ∈ List.range 1, ThresholdAt 5 (13+i) := by decide +kernel

theorem threshold_5_14 : ∀ i ∈ List.range 1, ThresholdAt 5 (14+i) := by decide +kernel

theorem threshold_5_15 : ∀ i ∈ List.range 1, ThresholdAt 5 (15+i) := by decide +kernel

theorem threshold_5_16 : ∀ i ∈ List.range 1, ThresholdAt 5 (16+i) := by decide +kernel

theorem threshold_5_17 : ∀ i ∈ List.range 1, ThresholdAt 5 (17+i) := by decide +kernel

theorem threshold_5_18 : ∀ i ∈ List.range 1, ThresholdAt 5 (18+i) := by decide +kernel

theorem threshold_5_19 : ∀ i ∈ List.range 1, ThresholdAt 5 (19+i) := by decide +kernel

theorem threshold_5_20 : ∀ i ∈ List.range 1, ThresholdAt 5 (20+i) := by decide +kernel

theorem threshold_5_21 : ∀ i ∈ List.range 1, ThresholdAt 5 (21+i) := by decide +kernel

theorem threshold_5_22 : ∀ i ∈ List.range 1, ThresholdAt 5 (22+i) := by decide +kernel

theorem threshold_5_23 : ∀ i ∈ List.range 1, ThresholdAt 5 (23+i) := by decide +kernel

theorem threshold_5_24 : ∀ i ∈ List.range 1, ThresholdAt 5 (24+i) := by decide +kernel

theorem threshold_5_25 : ∀ i ∈ List.range 1, ThresholdAt 5 (25+i) := by decide +kernel

theorem threshold_5_26 : ∀ i ∈ List.range 1, ThresholdAt 5 (26+i) := by decide +kernel

theorem threshold_5_27 : ∀ i ∈ List.range 1, ThresholdAt 5 (27+i) := by decide +kernel

theorem threshold_5_28 : ∀ i ∈ List.range 1, ThresholdAt 5 (28+i) := by decide +kernel

theorem threshold_5_29 : ∀ i ∈ List.range 1, ThresholdAt 5 (29+i) := by decide +kernel

theorem threshold_5_30 : ∀ i ∈ List.range 1, ThresholdAt 5 (30+i) := by decide +kernel

theorem threshold_5_31 : ∀ i ∈ List.range 1, ThresholdAt 5 (31+i) := by decide +kernel

theorem threshold_5_32 : ∀ i ∈ List.range 1, ThresholdAt 5 (32+i) := by decide +kernel

theorem threshold_5_33 : ∀ i ∈ List.range 1, ThresholdAt 5 (33+i) := by decide +kernel

theorem threshold_5_34 : ∀ i ∈ List.range 1, ThresholdAt 5 (34+i) := by decide +kernel

theorem threshold_5_35 : ∀ i ∈ List.range 1, ThresholdAt 5 (35+i) := by decide +kernel

theorem threshold_5_36 : ∀ i ∈ List.range 1, ThresholdAt 5 (36+i) := by decide +kernel

theorem threshold_5_37 : ∀ i ∈ List.range 1, ThresholdAt 5 (37+i) := by decide +kernel

theorem threshold_5_38 : ∀ i ∈ List.range 1, ThresholdAt 5 (38+i) := by decide +kernel

theorem threshold_5_39 : ∀ i ∈ List.range 1, ThresholdAt 5 (39+i) := by decide +kernel

theorem threshold_5_40 : ∀ i ∈ List.range 1, ThresholdAt 5 (40+i) := by decide +kernel

theorem threshold_5_41 : ∀ i ∈ List.range 1, ThresholdAt 5 (41+i) := by decide +kernel

theorem threshold_5_42 : ∀ i ∈ List.range 1, ThresholdAt 5 (42+i) := by decide +kernel

theorem threshold_5_43 : ∀ i ∈ List.range 1, ThresholdAt 5 (43+i) := by decide +kernel

theorem threshold_5_44 : ∀ i ∈ List.range 1, ThresholdAt 5 (44+i) := by decide +kernel

theorem threshold_5_45 : ∀ i ∈ List.range 1, ThresholdAt 5 (45+i) := by decide +kernel

theorem threshold_5_46 : ∀ i ∈ List.range 1, ThresholdAt 5 (46+i) := by decide +kernel

theorem threshold_5_47 : ∀ i ∈ List.range 1, ThresholdAt 5 (47+i) := by decide +kernel

theorem threshold_5_48 : ∀ i ∈ List.range 1, ThresholdAt 5 (48+i) := by decide +kernel

theorem threshold_5_49 : ∀ i ∈ List.range 1, ThresholdAt 5 (49+i) := by decide +kernel

theorem threshold_5_50 : ∀ i ∈ List.range 1, ThresholdAt 5 (50+i) := by decide +kernel

theorem threshold_5_51 : ∀ i ∈ List.range 1, ThresholdAt 5 (51+i) := by decide +kernel

theorem threshold_5_52 : ∀ i ∈ List.range 1, ThresholdAt 5 (52+i) := by decide +kernel

theorem threshold_5_53 : ∀ i ∈ List.range 1, ThresholdAt 5 (53+i) := by decide +kernel

theorem threshold_5_54 : ∀ i ∈ List.range 1, ThresholdAt 5 (54+i) := by decide +kernel

theorem threshold_5_55 : ∀ i ∈ List.range 1, ThresholdAt 5 (55+i) := by decide +kernel

theorem threshold_5_56 : ∀ i ∈ List.range 1, ThresholdAt 5 (56+i) := by decide +kernel

theorem threshold_5_57 : ∀ i ∈ List.range 1, ThresholdAt 5 (57+i) := by decide +kernel

theorem threshold_5_58 : ∀ i ∈ List.range 1, ThresholdAt 5 (58+i) := by decide +kernel

theorem threshold_5_59 : ∀ i ∈ List.range 1, ThresholdAt 5 (59+i) := by decide +kernel

theorem threshold_5_60 : ∀ i ∈ List.range 1, ThresholdAt 5 (60+i) := by decide +kernel

theorem threshold_5_61 : ∀ i ∈ List.range 1, ThresholdAt 5 (61+i) := by decide +kernel

theorem threshold_5_62 : ∀ i ∈ List.range 1, ThresholdAt 5 (62+i) := by decide +kernel

theorem threshold_5_63 : ∀ i ∈ List.range 1, ThresholdAt 5 (63+i) := by decide +kernel

theorem threshold_5_64 : ∀ i ∈ List.range 1, ThresholdAt 5 (64+i) := by decide +kernel

theorem threshold_5_65 : ∀ i ∈ List.range 1, ThresholdAt 5 (65+i) := by decide +kernel

theorem threshold_5_66 : ∀ i ∈ List.range 1, ThresholdAt 5 (66+i) := by decide +kernel

theorem threshold_5_67 : ∀ i ∈ List.range 1, ThresholdAt 5 (67+i) := by decide +kernel

theorem threshold_5_68 : ∀ i ∈ List.range 1, ThresholdAt 5 (68+i) := by decide +kernel

theorem threshold_5_69 : ∀ i ∈ List.range 1, ThresholdAt 5 (69+i) := by decide +kernel

theorem threshold_5_70 : ∀ i ∈ List.range 1, ThresholdAt 5 (70+i) := by decide +kernel

theorem threshold_5_71 : ∀ i ∈ List.range 1, ThresholdAt 5 (71+i) := by decide +kernel

theorem threshold_5_72 : ∀ i ∈ List.range 1, ThresholdAt 5 (72+i) := by decide +kernel

theorem threshold_5_73 : ∀ i ∈ List.range 1, ThresholdAt 5 (73+i) := by decide +kernel

theorem threshold_5_74 : ∀ i ∈ List.range 1, ThresholdAt 5 (74+i) := by decide +kernel

theorem threshold_5_75 : ∀ i ∈ List.range 1, ThresholdAt 5 (75+i) := by decide +kernel

theorem threshold_5_76 : ∀ i ∈ List.range 1, ThresholdAt 5 (76+i) := by decide +kernel

theorem threshold_5_77 : ∀ i ∈ List.range 1, ThresholdAt 5 (77+i) := by decide +kernel

theorem threshold_5_78 : ∀ i ∈ List.range 1, ThresholdAt 5 (78+i) := by decide +kernel

theorem threshold_5_79 : ∀ i ∈ List.range 1, ThresholdAt 5 (79+i) := by decide +kernel

theorem threshold_5_80 : ∀ i ∈ List.range 1, ThresholdAt 5 (80+i) := by decide +kernel

theorem threshold_5_81 : ∀ i ∈ List.range 1, ThresholdAt 5 (81+i) := by decide +kernel

theorem threshold_5_82 : ∀ i ∈ List.range 1, ThresholdAt 5 (82+i) := by decide +kernel

theorem threshold_5_83 : ∀ i ∈ List.range 1, ThresholdAt 5 (83+i) := by decide +kernel

theorem threshold_5_84 : ∀ i ∈ List.range 1, ThresholdAt 5 (84+i) := by decide +kernel

theorem threshold_5_85 : ∀ i ∈ List.range 1, ThresholdAt 5 (85+i) := by decide +kernel

theorem threshold_5_86 : ∀ i ∈ List.range 1, ThresholdAt 5 (86+i) := by decide +kernel

theorem threshold_5_87 : ∀ i ∈ List.range 1, ThresholdAt 5 (87+i) := by decide +kernel

theorem threshold_5_88 : ∀ i ∈ List.range 1, ThresholdAt 5 (88+i) := by decide +kernel

theorem threshold_5_89 : ∀ i ∈ List.range 1, ThresholdAt 5 (89+i) := by decide +kernel

theorem threshold_5_90 : ∀ i ∈ List.range 1, ThresholdAt 5 (90+i) := by decide +kernel

theorem threshold_5_91 : ∀ i ∈ List.range 1, ThresholdAt 5 (91+i) := by decide +kernel

theorem threshold_5_92 : ∀ i ∈ List.range 1, ThresholdAt 5 (92+i) := by decide +kernel

theorem threshold_5_93 : ∀ i ∈ List.range 1, ThresholdAt 5 (93+i) := by decide +kernel

theorem threshold_5_94 : ∀ i ∈ List.range 1, ThresholdAt 5 (94+i) := by decide +kernel

theorem threshold_5_95 : ∀ i ∈ List.range 1, ThresholdAt 5 (95+i) := by decide +kernel

theorem threshold_5_96 : ∀ i ∈ List.range 1, ThresholdAt 5 (96+i) := by decide +kernel

theorem threshold_5_97 : ∀ i ∈ List.range 1, ThresholdAt 5 (97+i) := by decide +kernel

theorem threshold_5_98 : ∀ i ∈ List.range 1, ThresholdAt 5 (98+i) := by decide +kernel

theorem threshold_5_99 : ∀ i ∈ List.range 1, ThresholdAt 5 (99+i) := by decide +kernel

theorem threshold_5_100 : ∀ i ∈ List.range 1, ThresholdAt 5 (100+i) := by decide +kernel

theorem threshold_5_101 : ∀ i ∈ List.range 1, ThresholdAt 5 (101+i) := by decide +kernel

theorem threshold_5_102 : ∀ i ∈ List.range 1, ThresholdAt 5 (102+i) := by decide +kernel

theorem threshold_5_103 : ∀ i ∈ List.range 1, ThresholdAt 5 (103+i) := by decide +kernel

theorem threshold_5_104 : ∀ i ∈ List.range 1, ThresholdAt 5 (104+i) := by decide +kernel

theorem threshold_5_105 : ∀ i ∈ List.range 1, ThresholdAt 5 (105+i) := by decide +kernel

theorem threshold_5_106 : ∀ i ∈ List.range 1, ThresholdAt 5 (106+i) := by decide +kernel

theorem threshold_5_107 : ∀ i ∈ List.range 1, ThresholdAt 5 (107+i) := by decide +kernel

theorem threshold_5_108 : ∀ i ∈ List.range 1, ThresholdAt 5 (108+i) := by decide +kernel

theorem threshold_5_109 : ∀ i ∈ List.range 1, ThresholdAt 5 (109+i) := by decide +kernel

theorem threshold_5_110 : ∀ i ∈ List.range 1, ThresholdAt 5 (110+i) := by decide +kernel

theorem threshold_5_111 : ∀ i ∈ List.range 1, ThresholdAt 5 (111+i) := by decide +kernel

theorem threshold_5_112 : ∀ i ∈ List.range 1, ThresholdAt 5 (112+i) := by decide +kernel

theorem threshold_5_113 : ∀ i ∈ List.range 1, ThresholdAt 5 (113+i) := by decide +kernel

theorem threshold_5_114 : ∀ i ∈ List.range 1, ThresholdAt 5 (114+i) := by decide +kernel

theorem threshold_5_115 : ∀ i ∈ List.range 1, ThresholdAt 5 (115+i) := by decide +kernel

theorem threshold_5_116 : ∀ i ∈ List.range 1, ThresholdAt 5 (116+i) := by decide +kernel

theorem threshold_5_117 : ∀ i ∈ List.range 1, ThresholdAt 5 (117+i) := by decide +kernel

theorem threshold_5_118 : ∀ i ∈ List.range 1, ThresholdAt 5 (118+i) := by decide +kernel

theorem threshold_5_119 : ∀ i ∈ List.range 1, ThresholdAt 5 (119+i) := by decide +kernel

theorem threshold_5_120 : ∀ i ∈ List.range 1, ThresholdAt 5 (120+i) := by decide +kernel

theorem threshold_5_121 : ∀ i ∈ List.range 1, ThresholdAt 5 (121+i) := by decide +kernel

theorem threshold_5_122 : ∀ i ∈ List.range 1, ThresholdAt 5 (122+i) := by decide +kernel

theorem threshold_5_123 : ∀ i ∈ List.range 1, ThresholdAt 5 (123+i) := by decide +kernel

theorem threshold_5_124 : ∀ i ∈ List.range 1, ThresholdAt 5 (124+i) := by decide +kernel

theorem threshold_5_125 : ∀ i ∈ List.range 1, ThresholdAt 5 (125+i) := by decide +kernel

theorem threshold_5_126 : ∀ i ∈ List.range 1, ThresholdAt 5 (126+i) := by decide +kernel

theorem threshold_5_127 : ∀ i ∈ List.range 1, ThresholdAt 5 (127+i) := by decide +kernel

theorem threshold_5_128 : ∀ i ∈ List.range 1, ThresholdAt 5 (128+i) := by decide +kernel

theorem threshold_5_129 : ∀ i ∈ List.range 1, ThresholdAt 5 (129+i) := by decide +kernel

theorem threshold_5_130 : ∀ i ∈ List.range 1, ThresholdAt 5 (130+i) := by decide +kernel

theorem threshold_5_131 : ∀ i ∈ List.range 1, ThresholdAt 5 (131+i) := by decide +kernel

theorem threshold_5_132 : ∀ i ∈ List.range 1, ThresholdAt 5 (132+i) := by decide +kernel

theorem threshold_5_133 : ∀ i ∈ List.range 1, ThresholdAt 5 (133+i) := by decide +kernel

theorem threshold_5_134 : ∀ i ∈ List.range 1, ThresholdAt 5 (134+i) := by decide +kernel

theorem threshold_5_135 : ∀ i ∈ List.range 1, ThresholdAt 5 (135+i) := by decide +kernel

theorem threshold_5_136 : ∀ i ∈ List.range 1, ThresholdAt 5 (136+i) := by decide +kernel

theorem threshold_5_137 : ∀ i ∈ List.range 1, ThresholdAt 5 (137+i) := by decide +kernel

theorem threshold_5_138 : ∀ i ∈ List.range 1, ThresholdAt 5 (138+i) := by decide +kernel

theorem threshold_5_139 : ∀ i ∈ List.range 1, ThresholdAt 5 (139+i) := by decide +kernel

theorem threshold_5_140 : ∀ i ∈ List.range 1, ThresholdAt 5 (140+i) := by decide +kernel

theorem threshold_5_141 : ∀ i ∈ List.range 1, ThresholdAt 5 (141+i) := by decide +kernel

theorem threshold_5 (v : ℕ) (hv : v ∈ List.range 142) : ThresholdAt 5 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 5 v)
  have h := (join 0 71 71 (join 0 35 36 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_5_0 threshold_5_1) (join 2 1 1 threshold_5_2 threshold_5_3)) (join 4 2 2 (join 4 1 1 threshold_5_4 threshold_5_5) (join 6 1 1 threshold_5_6 threshold_5_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_5_8 threshold_5_9) (join 10 1 1 threshold_5_10 threshold_5_11)) (join 12 2 3 (join 12 1 1 threshold_5_12 threshold_5_13) (join 14 1 2 threshold_5_14 (join 15 1 1 threshold_5_15 threshold_5_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 threshold_5_17 threshold_5_18) (join 19 1 1 threshold_5_19 threshold_5_20)) (join 21 2 3 (join 21 1 1 threshold_5_21 threshold_5_22) (join 23 1 2 threshold_5_23 (join 24 1 1 threshold_5_24 threshold_5_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 threshold_5_26 threshold_5_27) (join 28 1 1 threshold_5_28 threshold_5_29)) (join 30 2 3 (join 30 1 1 threshold_5_30 threshold_5_31) (join 32 1 2 threshold_5_32 (join 33 1 1 threshold_5_33 threshold_5_34)))))) (join 35 18 18 (join 35 9 9 (join 35 4 5 (join 35 2 2 (join 35 1 1 threshold_5_35 threshold_5_36) (join 37 1 1 threshold_5_37 threshold_5_38)) (join 39 2 3 (join 39 1 1 threshold_5_39 threshold_5_40) (join 41 1 2 threshold_5_41 (join 42 1 1 threshold_5_42 threshold_5_43)))) (join 44 4 5 (join 44 2 2 (join 44 1 1 threshold_5_44 threshold_5_45) (join 46 1 1 threshold_5_46 threshold_5_47)) (join 48 2 3 (join 48 1 1 threshold_5_48 threshold_5_49) (join 50 1 2 threshold_5_50 (join 51 1 1 threshold_5_51 threshold_5_52))))) (join 53 9 9 (join 53 4 5 (join 53 2 2 (join 53 1 1 threshold_5_53 threshold_5_54) (join 55 1 1 threshold_5_55 threshold_5_56)) (join 57 2 3 (join 57 1 1 threshold_5_57 threshold_5_58) (join 59 1 2 threshold_5_59 (join 60 1 1 threshold_5_60 threshold_5_61)))) (join 62 4 5 (join 62 2 2 (join 62 1 1 threshold_5_62 threshold_5_63) (join 64 1 1 threshold_5_64 threshold_5_65)) (join 66 2 3 (join 66 1 1 threshold_5_66 threshold_5_67) (join 68 1 2 threshold_5_68 (join 69 1 1 threshold_5_69 threshold_5_70))))))) (join 71 35 36 (join 71 17 18 (join 71 8 9 (join 71 4 4 (join 71 2 2 (join 71 1 1 threshold_5_71 threshold_5_72) (join 73 1 1 threshold_5_73 threshold_5_74)) (join 75 2 2 (join 75 1 1 threshold_5_75 threshold_5_76) (join 77 1 1 threshold_5_77 threshold_5_78))) (join 79 4 5 (join 79 2 2 (join 79 1 1 threshold_5_79 threshold_5_80) (join 81 1 1 threshold_5_81 threshold_5_82)) (join 83 2 3 (join 83 1 1 threshold_5_83 threshold_5_84) (join 85 1 2 threshold_5_85 (join 86 1 1 threshold_5_86 threshold_5_87))))) (join 88 9 9 (join 88 4 5 (join 88 2 2 (join 88 1 1 threshold_5_88 threshold_5_89) (join 90 1 1 threshold_5_90 threshold_5_91)) (join 92 2 3 (join 92 1 1 threshold_5_92 threshold_5_93) (join 94 1 2 threshold_5_94 (join 95 1 1 threshold_5_95 threshold_5_96)))) (join 97 4 5 (join 97 2 2 (join 97 1 1 threshold_5_97 threshold_5_98) (join 99 1 1 threshold_5_99 threshold_5_100)) (join 101 2 3 (join 101 1 1 threshold_5_101 threshold_5_102) (join 103 1 2 threshold_5_103 (join 104 1 1 threshold_5_104 threshold_5_105)))))) (join 106 18 18 (join 106 9 9 (join 106 4 5 (join 106 2 2 (join 106 1 1 threshold_5_106 threshold_5_107) (join 108 1 1 threshold_5_108 threshold_5_109)) (join 110 2 3 (join 110 1 1 threshold_5_110 threshold_5_111) (join 112 1 2 threshold_5_112 (join 113 1 1 threshold_5_113 threshold_5_114)))) (join 115 4 5 (join 115 2 2 (join 115 1 1 threshold_5_115 threshold_5_116) (join 117 1 1 threshold_5_117 threshold_5_118)) (join 119 2 3 (join 119 1 1 threshold_5_119 threshold_5_120) (join 121 1 2 threshold_5_121 (join 122 1 1 threshold_5_122 threshold_5_123))))) (join 124 9 9 (join 124 4 5 (join 124 2 2 (join 124 1 1 threshold_5_124 threshold_5_125) (join 126 1 1 threshold_5_126 threshold_5_127)) (join 128 2 3 (join 128 1 1 threshold_5_128 threshold_5_129) (join 130 1 2 threshold_5_130 (join 131 1 1 threshold_5_131 threshold_5_132)))) (join 133 4 5 (join 133 2 2 (join 133 1 1 threshold_5_133 threshold_5_134) (join 135 1 1 threshold_5_135 threshold_5_136)) (join 137 2 3 (join 137 1 1 threshold_5_137 threshold_5_138) (join 139 1 2 threshold_5_139 (join 140 1 1 threshold_5_140 threshold_5_141))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_5_0 : ∀ i ∈ List.range 4, LedgerAt 5 (0+i) := by decide +kernel

theorem ledger_5_4 : ∀ i ∈ List.range 4, LedgerAt 5 (4+i) := by decide +kernel

theorem ledger_5_8 : ∀ i ∈ List.range 4, LedgerAt 5 (8+i) := by decide +kernel

theorem ledger_5_12 : ∀ i ∈ List.range 4, LedgerAt 5 (12+i) := by decide +kernel

theorem ledger_5_16 : ∀ i ∈ List.range 4, LedgerAt 5 (16+i) := by decide +kernel

theorem ledger_5_20 : ∀ i ∈ List.range 4, LedgerAt 5 (20+i) := by decide +kernel

theorem ledger_5_24 : ∀ i ∈ List.range 4, LedgerAt 5 (24+i) := by decide +kernel

theorem ledger_5_28 : ∀ i ∈ List.range 4, LedgerAt 5 (28+i) := by decide +kernel

theorem ledger_5_32 : ∀ i ∈ List.range 4, LedgerAt 5 (32+i) := by decide +kernel

theorem ledger_5_36 : ∀ i ∈ List.range 4, LedgerAt 5 (36+i) := by decide +kernel

theorem ledger_5_40 : ∀ i ∈ List.range 4, LedgerAt 5 (40+i) := by decide +kernel

theorem ledger_5_44 : ∀ i ∈ List.range 4, LedgerAt 5 (44+i) := by decide +kernel

theorem ledger_5_48 : ∀ i ∈ List.range 4, LedgerAt 5 (48+i) := by decide +kernel

theorem ledger_5_52 : ∀ i ∈ List.range 4, LedgerAt 5 (52+i) := by decide +kernel

theorem ledger_5_56 : ∀ i ∈ List.range 4, LedgerAt 5 (56+i) := by decide +kernel

theorem ledger_5_60 : ∀ i ∈ List.range 4, LedgerAt 5 (60+i) := by decide +kernel

theorem ledger_5_64 : ∀ i ∈ List.range 4, LedgerAt 5 (64+i) := by decide +kernel

theorem ledger_5_68 : ∀ i ∈ List.range 4, LedgerAt 5 (68+i) := by decide +kernel

theorem ledger_5_72 : ∀ i ∈ List.range 4, LedgerAt 5 (72+i) := by decide +kernel

theorem ledger_5_76 : ∀ i ∈ List.range 4, LedgerAt 5 (76+i) := by decide +kernel

theorem ledger_5_80 : ∀ i ∈ List.range 4, LedgerAt 5 (80+i) := by decide +kernel

theorem ledger_5_84 : ∀ i ∈ List.range 4, LedgerAt 5 (84+i) := by decide +kernel

theorem ledger_5_88 : ∀ i ∈ List.range 4, LedgerAt 5 (88+i) := by decide +kernel

theorem ledger_5_92 : ∀ i ∈ List.range 4, LedgerAt 5 (92+i) := by decide +kernel

theorem ledger_5_96 : ∀ i ∈ List.range 4, LedgerAt 5 (96+i) := by decide +kernel

theorem ledger_5_100 : ∀ i ∈ List.range 4, LedgerAt 5 (100+i) := by decide +kernel

theorem ledger_5_104 : ∀ i ∈ List.range 4, LedgerAt 5 (104+i) := by decide +kernel

theorem ledger_5_108 : ∀ i ∈ List.range 4, LedgerAt 5 (108+i) := by decide +kernel

theorem ledger_5_112 : ∀ i ∈ List.range 4, LedgerAt 5 (112+i) := by decide +kernel

theorem ledger_5_116 : ∀ i ∈ List.range 4, LedgerAt 5 (116+i) := by decide +kernel

theorem ledger_5_120 : ∀ i ∈ List.range 4, LedgerAt 5 (120+i) := by decide +kernel

theorem ledger_5_124 : ∀ i ∈ List.range 4, LedgerAt 5 (124+i) := by decide +kernel

theorem ledger_5_128 : ∀ i ∈ List.range 4, LedgerAt 5 (128+i) := by decide +kernel

theorem ledger_5_132 : ∀ i ∈ List.range 4, LedgerAt 5 (132+i) := by decide +kernel

theorem ledger_5_136 : ∀ i ∈ List.range 4, LedgerAt 5 (136+i) := by decide +kernel

theorem ledger_5_140 : ∀ i ∈ List.range 2, LedgerAt 5 (140+i) := by decide +kernel

theorem ledger_5 (v : ℕ) (hv : v ∈ List.range 142) : LedgerAt 5 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 5 v)
  have h := (join 0 72 70 (join 0 36 36 (join 0 16 20 (join 0 8 8 (join 0 4 4 ledger_5_0 ledger_5_4) (join 8 4 4 ledger_5_8 ledger_5_12)) (join 16 8 12 (join 16 4 4 ledger_5_16 ledger_5_20) (join 24 4 8 ledger_5_24 (join 28 4 4 ledger_5_28 ledger_5_32)))) (join 36 16 20 (join 36 8 8 (join 36 4 4 ledger_5_36 ledger_5_40) (join 44 4 4 ledger_5_44 ledger_5_48)) (join 52 8 12 (join 52 4 4 ledger_5_52 ledger_5_56) (join 60 4 8 ledger_5_60 (join 64 4 4 ledger_5_64 ledger_5_68))))) (join 72 36 34 (join 72 16 20 (join 72 8 8 (join 72 4 4 ledger_5_72 ledger_5_76) (join 80 4 4 ledger_5_80 ledger_5_84)) (join 88 8 12 (join 88 4 4 ledger_5_88 ledger_5_92) (join 96 4 8 ledger_5_96 (join 100 4 4 ledger_5_100 ledger_5_104)))) (join 108 16 18 (join 108 8 8 (join 108 4 4 ledger_5_108 ledger_5_112) (join 116 4 4 ledger_5_116 ledger_5_120)) (join 124 8 10 (join 124 4 4 ledger_5_124 ledger_5_128) (join 132 4 6 ledger_5_132 (join 136 4 2 ledger_5_136 ledger_5_140))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
