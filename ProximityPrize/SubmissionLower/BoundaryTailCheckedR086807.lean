import ProximityPrize.SubmissionLower.BoundaryTailCheckedR076807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_8_0 : ∀ i ∈ List.range 4, GeometryAt 8 (0+i) := by decide +kernel

theorem geometry_8_4 : ∀ i ∈ List.range 4, GeometryAt 8 (4+i) := by decide +kernel

theorem geometry_8_8 : ∀ i ∈ List.range 4, GeometryAt 8 (8+i) := by decide +kernel

theorem geometry_8_12 : ∀ i ∈ List.range 4, GeometryAt 8 (12+i) := by decide +kernel

theorem geometry_8_16 : ∀ i ∈ List.range 4, GeometryAt 8 (16+i) := by decide +kernel

theorem geometry_8_20 : ∀ i ∈ List.range 4, GeometryAt 8 (20+i) := by decide +kernel

theorem geometry_8_24 : ∀ i ∈ List.range 4, GeometryAt 8 (24+i) := by decide +kernel

theorem geometry_8_28 : ∀ i ∈ List.range 4, GeometryAt 8 (28+i) := by decide +kernel

theorem geometry_8_32 : ∀ i ∈ List.range 4, GeometryAt 8 (32+i) := by decide +kernel

theorem geometry_8_36 : ∀ i ∈ List.range 4, GeometryAt 8 (36+i) := by decide +kernel

theorem geometry_8_40 : ∀ i ∈ List.range 4, GeometryAt 8 (40+i) := by decide +kernel

theorem geometry_8_44 : ∀ i ∈ List.range 4, GeometryAt 8 (44+i) := by decide +kernel

theorem geometry_8_48 : ∀ i ∈ List.range 4, GeometryAt 8 (48+i) := by decide +kernel

theorem geometry_8_52 : ∀ i ∈ List.range 4, GeometryAt 8 (52+i) := by decide +kernel

theorem geometry_8_56 : ∀ i ∈ List.range 4, GeometryAt 8 (56+i) := by decide +kernel

theorem geometry_8_60 : ∀ i ∈ List.range 4, GeometryAt 8 (60+i) := by decide +kernel

theorem geometry_8_64 : ∀ i ∈ List.range 4, GeometryAt 8 (64+i) := by decide +kernel

theorem geometry_8_68 : ∀ i ∈ List.range 4, GeometryAt 8 (68+i) := by decide +kernel

theorem geometry_8_72 : ∀ i ∈ List.range 4, GeometryAt 8 (72+i) := by decide +kernel

theorem geometry_8_76 : ∀ i ∈ List.range 4, GeometryAt 8 (76+i) := by decide +kernel

theorem geometry_8_80 : ∀ i ∈ List.range 4, GeometryAt 8 (80+i) := by decide +kernel

theorem geometry_8_84 : ∀ i ∈ List.range 4, GeometryAt 8 (84+i) := by decide +kernel

theorem geometry_8_88 : ∀ i ∈ List.range 4, GeometryAt 8 (88+i) := by decide +kernel

theorem geometry_8_92 : ∀ i ∈ List.range 4, GeometryAt 8 (92+i) := by decide +kernel

theorem geometry_8_96 : ∀ i ∈ List.range 4, GeometryAt 8 (96+i) := by decide +kernel

theorem geometry_8_100 : ∀ i ∈ List.range 4, GeometryAt 8 (100+i) := by decide +kernel

theorem geometry_8_104 : ∀ i ∈ List.range 4, GeometryAt 8 (104+i) := by decide +kernel

theorem geometry_8_108 : ∀ i ∈ List.range 4, GeometryAt 8 (108+i) := by decide +kernel

theorem geometry_8_112 : ∀ i ∈ List.range 4, GeometryAt 8 (112+i) := by decide +kernel

theorem geometry_8_116 : ∀ i ∈ List.range 4, GeometryAt 8 (116+i) := by decide +kernel

theorem geometry_8_120 : ∀ i ∈ List.range 4, GeometryAt 8 (120+i) := by decide +kernel

theorem geometry_8_124 : ∀ i ∈ List.range 4, GeometryAt 8 (124+i) := by decide +kernel

theorem geometry_8_128 : ∀ i ∈ List.range 4, GeometryAt 8 (128+i) := by decide +kernel

theorem geometry_8_132 : ∀ i ∈ List.range 4, GeometryAt 8 (132+i) := by decide +kernel

theorem geometry_8_136 : ∀ i ∈ List.range 3, GeometryAt 8 (136+i) := by decide +kernel

theorem geometry_8 (v : ℕ) (hv : v ∈ List.range 139) : GeometryAt 8 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 8 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_8_0 geometry_8_4) (join 8 4 4 geometry_8_8 geometry_8_12)) (join 16 8 8 (join 16 4 4 geometry_8_16 geometry_8_20) (join 24 4 4 geometry_8_24 geometry_8_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 geometry_8_32 geometry_8_36) (join 40 4 4 geometry_8_40 geometry_8_44)) (join 48 8 12 (join 48 4 4 geometry_8_48 geometry_8_52) (join 56 4 8 geometry_8_56 (join 60 4 4 geometry_8_60 geometry_8_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 geometry_8_68 geometry_8_72) (join 76 4 4 geometry_8_76 geometry_8_80)) (join 84 8 12 (join 84 4 4 geometry_8_84 geometry_8_88) (join 92 4 8 geometry_8_92 (join 96 4 4 geometry_8_96 geometry_8_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 geometry_8_104 geometry_8_108) (join 112 4 4 geometry_8_112 geometry_8_116)) (join 120 8 11 (join 120 4 4 geometry_8_120 geometry_8_124) (join 128 4 7 geometry_8_128 (join 132 4 3 geometry_8_132 geometry_8_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_8_0 : ∀ i ∈ List.range 4, StrictAt 8 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (0+i)) 8 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_4 : ∀ i ∈ List.range 4, StrictAt 8 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (4+i)) 8 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_8 : ∀ i ∈ List.range 4, StrictAt 8 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (8+i)) 8 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_12 : ∀ i ∈ List.range 4, StrictAt 8 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (12+i)) 8 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_16 : ∀ i ∈ List.range 4, StrictAt 8 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (16+i)) 8 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_20 : ∀ i ∈ List.range 4, StrictAt 8 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (20+i)) 8 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_24 : ∀ i ∈ List.range 4, StrictAt 8 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (24+i)) 8 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_28 : ∀ i ∈ List.range 4, StrictAt 8 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (28+i)) 8 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_32 : ∀ i ∈ List.range 4, StrictAt 8 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (32+i)) 8 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_36 : ∀ i ∈ List.range 4, StrictAt 8 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (36+i)) 8 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_40 : ∀ i ∈ List.range 4, StrictAt 8 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (40+i)) 8 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_44 : ∀ i ∈ List.range 4, StrictAt 8 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (44+i)) 8 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_48 : ∀ i ∈ List.range 4, StrictAt 8 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (48+i)) 8 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_52 : ∀ i ∈ List.range 4, StrictAt 8 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (52+i)) 8 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_56 : ∀ i ∈ List.range 4, StrictAt 8 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (56+i)) 8 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_60 : ∀ i ∈ List.range 4, StrictAt 8 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (60+i)) 8 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_64 : ∀ i ∈ List.range 4, StrictAt 8 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (64+i)) 8 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_68 : ∀ i ∈ List.range 4, StrictAt 8 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (68+i)) 8 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_72 : ∀ i ∈ List.range 4, StrictAt 8 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (72+i)) 8 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_76 : ∀ i ∈ List.range 4, StrictAt 8 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (76+i)) 8 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_80 : ∀ i ∈ List.range 4, StrictAt 8 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (80+i)) 8 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_84 : ∀ i ∈ List.range 4, StrictAt 8 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (84+i)) 8 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_88 : ∀ i ∈ List.range 4, StrictAt 8 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (88+i)) 8 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_92 : ∀ i ∈ List.range 4, StrictAt 8 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (92+i)) 8 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_96 : ∀ i ∈ List.range 4, StrictAt 8 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (96+i)) 8 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_100 : ∀ i ∈ List.range 4, StrictAt 8 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (100+i)) 8 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_104 : ∀ i ∈ List.range 4, StrictAt 8 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (104+i)) 8 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_108 : ∀ i ∈ List.range 4, StrictAt 8 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (108+i)) 8 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_112 : ∀ i ∈ List.range 4, StrictAt 8 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (112+i)) 8 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_116 : ∀ i ∈ List.range 4, StrictAt 8 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (116+i)) 8 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_120 : ∀ i ∈ List.range 4, StrictAt 8 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (120+i)) 8 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_124 : ∀ i ∈ List.range 4, StrictAt 8 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (124+i)) 8 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_128 : ∀ i ∈ List.range 4, StrictAt 8 (128+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (128+i)) 8 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_132 : ∀ i ∈ List.range 4, StrictAt 8 (132+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (132+i)) 8 (132+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8_136 : ∀ i ∈ List.range 3, StrictAt 8 (136+i) := by
  have h : ∀ i ∈ List.range 3, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 8 (136+i)) 8 (136+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_8 (v : ℕ) (hv : v ∈ List.range 139) : StrictAt 8 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 8 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_8_0 strict_8_4) (join 8 4 4 strict_8_8 strict_8_12)) (join 16 8 8 (join 16 4 4 strict_8_16 strict_8_20) (join 24 4 4 strict_8_24 strict_8_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 strict_8_32 strict_8_36) (join 40 4 4 strict_8_40 strict_8_44)) (join 48 8 12 (join 48 4 4 strict_8_48 strict_8_52) (join 56 4 8 strict_8_56 (join 60 4 4 strict_8_60 strict_8_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 strict_8_68 strict_8_72) (join 76 4 4 strict_8_76 strict_8_80)) (join 84 8 12 (join 84 4 4 strict_8_84 strict_8_88) (join 92 4 8 strict_8_92 (join 96 4 4 strict_8_96 strict_8_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 strict_8_104 strict_8_108) (join 112 4 4 strict_8_112 strict_8_116)) (join 120 8 11 (join 120 4 4 strict_8_120 strict_8_124) (join 128 4 7 strict_8_128 (join 132 4 3 strict_8_132 strict_8_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_8_0 : ∀ i ∈ List.range 4, PhaseAt 8 (0+i) := by decide +kernel

theorem phase_8_4 : ∀ i ∈ List.range 4, PhaseAt 8 (4+i) := by decide +kernel

theorem phase_8_8 : ∀ i ∈ List.range 4, PhaseAt 8 (8+i) := by decide +kernel

theorem phase_8_12 : ∀ i ∈ List.range 4, PhaseAt 8 (12+i) := by decide +kernel

theorem phase_8_16 : ∀ i ∈ List.range 4, PhaseAt 8 (16+i) := by decide +kernel

theorem phase_8_20 : ∀ i ∈ List.range 4, PhaseAt 8 (20+i) := by decide +kernel

theorem phase_8_24 : ∀ i ∈ List.range 4, PhaseAt 8 (24+i) := by decide +kernel

theorem phase_8_28 : ∀ i ∈ List.range 4, PhaseAt 8 (28+i) := by decide +kernel

theorem phase_8_32 : ∀ i ∈ List.range 4, PhaseAt 8 (32+i) := by decide +kernel

theorem phase_8_36 : ∀ i ∈ List.range 4, PhaseAt 8 (36+i) := by decide +kernel

theorem phase_8_40 : ∀ i ∈ List.range 4, PhaseAt 8 (40+i) := by decide +kernel

theorem phase_8_44 : ∀ i ∈ List.range 4, PhaseAt 8 (44+i) := by decide +kernel

theorem phase_8_48 : ∀ i ∈ List.range 4, PhaseAt 8 (48+i) := by decide +kernel

theorem phase_8_52 : ∀ i ∈ List.range 4, PhaseAt 8 (52+i) := by decide +kernel

theorem phase_8_56 : ∀ i ∈ List.range 4, PhaseAt 8 (56+i) := by decide +kernel

theorem phase_8_60 : ∀ i ∈ List.range 4, PhaseAt 8 (60+i) := by decide +kernel

theorem phase_8_64 : ∀ i ∈ List.range 4, PhaseAt 8 (64+i) := by decide +kernel

theorem phase_8_68 : ∀ i ∈ List.range 4, PhaseAt 8 (68+i) := by decide +kernel

theorem phase_8_72 : ∀ i ∈ List.range 4, PhaseAt 8 (72+i) := by decide +kernel

theorem phase_8_76 : ∀ i ∈ List.range 4, PhaseAt 8 (76+i) := by decide +kernel

theorem phase_8_80 : ∀ i ∈ List.range 4, PhaseAt 8 (80+i) := by decide +kernel

theorem phase_8_84 : ∀ i ∈ List.range 4, PhaseAt 8 (84+i) := by decide +kernel

theorem phase_8_88 : ∀ i ∈ List.range 4, PhaseAt 8 (88+i) := by decide +kernel

theorem phase_8_92 : ∀ i ∈ List.range 4, PhaseAt 8 (92+i) := by decide +kernel

theorem phase_8_96 : ∀ i ∈ List.range 4, PhaseAt 8 (96+i) := by decide +kernel

theorem phase_8_100 : ∀ i ∈ List.range 4, PhaseAt 8 (100+i) := by decide +kernel

theorem phase_8_104 : ∀ i ∈ List.range 4, PhaseAt 8 (104+i) := by decide +kernel

theorem phase_8_108 : ∀ i ∈ List.range 4, PhaseAt 8 (108+i) := by decide +kernel

theorem phase_8_112 : ∀ i ∈ List.range 4, PhaseAt 8 (112+i) := by decide +kernel

theorem phase_8_116 : ∀ i ∈ List.range 4, PhaseAt 8 (116+i) := by decide +kernel

theorem phase_8_120 : ∀ i ∈ List.range 4, PhaseAt 8 (120+i) := by decide +kernel

theorem phase_8_124 : ∀ i ∈ List.range 4, PhaseAt 8 (124+i) := by decide +kernel

theorem phase_8_128 : ∀ i ∈ List.range 4, PhaseAt 8 (128+i) := by decide +kernel

theorem phase_8_132 : ∀ i ∈ List.range 4, PhaseAt 8 (132+i) := by decide +kernel

theorem phase_8_136 : ∀ i ∈ List.range 3, PhaseAt 8 (136+i) := by decide +kernel

theorem phase_8 (v : ℕ) (hv : v ∈ List.range 139) : PhaseAt 8 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 8 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_8_0 phase_8_4) (join 8 4 4 phase_8_8 phase_8_12)) (join 16 8 8 (join 16 4 4 phase_8_16 phase_8_20) (join 24 4 4 phase_8_24 phase_8_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_8_32 phase_8_36) (join 40 4 4 phase_8_40 phase_8_44)) (join 48 8 12 (join 48 4 4 phase_8_48 phase_8_52) (join 56 4 8 phase_8_56 (join 60 4 4 phase_8_60 phase_8_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 phase_8_68 phase_8_72) (join 76 4 4 phase_8_76 phase_8_80)) (join 84 8 12 (join 84 4 4 phase_8_84 phase_8_88) (join 92 4 8 phase_8_92 (join 96 4 4 phase_8_96 phase_8_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 phase_8_104 phase_8_108) (join 112 4 4 phase_8_112 phase_8_116)) (join 120 8 11 (join 120 4 4 phase_8_120 phase_8_124) (join 128 4 7 phase_8_128 (join 132 4 3 phase_8_132 phase_8_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_8_0 : ∀ i ∈ List.range 1, ThresholdAt 8 (0+i) := by decide +kernel

theorem threshold_8_1 : ∀ i ∈ List.range 1, ThresholdAt 8 (1+i) := by decide +kernel

theorem threshold_8_2 : ∀ i ∈ List.range 1, ThresholdAt 8 (2+i) := by decide +kernel

theorem threshold_8_3 : ∀ i ∈ List.range 1, ThresholdAt 8 (3+i) := by decide +kernel

theorem threshold_8_4 : ∀ i ∈ List.range 1, ThresholdAt 8 (4+i) := by decide +kernel

theorem threshold_8_5 : ∀ i ∈ List.range 1, ThresholdAt 8 (5+i) := by decide +kernel

theorem threshold_8_6 : ∀ i ∈ List.range 1, ThresholdAt 8 (6+i) := by decide +kernel

theorem threshold_8_7 : ∀ i ∈ List.range 1, ThresholdAt 8 (7+i) := by decide +kernel

theorem threshold_8_8 : ∀ i ∈ List.range 1, ThresholdAt 8 (8+i) := by decide +kernel

theorem threshold_8_9 : ∀ i ∈ List.range 1, ThresholdAt 8 (9+i) := by decide +kernel

theorem threshold_8_10 : ∀ i ∈ List.range 1, ThresholdAt 8 (10+i) := by decide +kernel

theorem threshold_8_11 : ∀ i ∈ List.range 1, ThresholdAt 8 (11+i) := by decide +kernel

theorem threshold_8_12 : ∀ i ∈ List.range 1, ThresholdAt 8 (12+i) := by decide +kernel

theorem threshold_8_13 : ∀ i ∈ List.range 1, ThresholdAt 8 (13+i) := by decide +kernel

theorem threshold_8_14 : ∀ i ∈ List.range 1, ThresholdAt 8 (14+i) := by decide +kernel

theorem threshold_8_15 : ∀ i ∈ List.range 1, ThresholdAt 8 (15+i) := by decide +kernel

theorem threshold_8_16 : ∀ i ∈ List.range 1, ThresholdAt 8 (16+i) := by decide +kernel

theorem threshold_8_17 : ∀ i ∈ List.range 1, ThresholdAt 8 (17+i) := by decide +kernel

theorem threshold_8_18 : ∀ i ∈ List.range 1, ThresholdAt 8 (18+i) := by decide +kernel

theorem threshold_8_19 : ∀ i ∈ List.range 1, ThresholdAt 8 (19+i) := by decide +kernel

theorem threshold_8_20 : ∀ i ∈ List.range 1, ThresholdAt 8 (20+i) := by decide +kernel

theorem threshold_8_21 : ∀ i ∈ List.range 1, ThresholdAt 8 (21+i) := by decide +kernel

theorem threshold_8_22 : ∀ i ∈ List.range 1, ThresholdAt 8 (22+i) := by decide +kernel

theorem threshold_8_23 : ∀ i ∈ List.range 1, ThresholdAt 8 (23+i) := by decide +kernel

theorem threshold_8_24 : ∀ i ∈ List.range 1, ThresholdAt 8 (24+i) := by decide +kernel

theorem threshold_8_25 : ∀ i ∈ List.range 1, ThresholdAt 8 (25+i) := by decide +kernel

theorem threshold_8_26 : ∀ i ∈ List.range 1, ThresholdAt 8 (26+i) := by decide +kernel

theorem threshold_8_27 : ∀ i ∈ List.range 1, ThresholdAt 8 (27+i) := by decide +kernel

theorem threshold_8_28 : ∀ i ∈ List.range 1, ThresholdAt 8 (28+i) := by decide +kernel

theorem threshold_8_29 : ∀ i ∈ List.range 1, ThresholdAt 8 (29+i) := by decide +kernel

theorem threshold_8_30 : ∀ i ∈ List.range 1, ThresholdAt 8 (30+i) := by decide +kernel

theorem threshold_8_31 : ∀ i ∈ List.range 1, ThresholdAt 8 (31+i) := by decide +kernel

theorem threshold_8_32 : ∀ i ∈ List.range 1, ThresholdAt 8 (32+i) := by decide +kernel

theorem threshold_8_33 : ∀ i ∈ List.range 1, ThresholdAt 8 (33+i) := by decide +kernel

theorem threshold_8_34 : ∀ i ∈ List.range 1, ThresholdAt 8 (34+i) := by decide +kernel

theorem threshold_8_35 : ∀ i ∈ List.range 1, ThresholdAt 8 (35+i) := by decide +kernel

theorem threshold_8_36 : ∀ i ∈ List.range 1, ThresholdAt 8 (36+i) := by decide +kernel

theorem threshold_8_37 : ∀ i ∈ List.range 1, ThresholdAt 8 (37+i) := by decide +kernel

theorem threshold_8_38 : ∀ i ∈ List.range 1, ThresholdAt 8 (38+i) := by decide +kernel

theorem threshold_8_39 : ∀ i ∈ List.range 1, ThresholdAt 8 (39+i) := by decide +kernel

theorem threshold_8_40 : ∀ i ∈ List.range 1, ThresholdAt 8 (40+i) := by decide +kernel

theorem threshold_8_41 : ∀ i ∈ List.range 1, ThresholdAt 8 (41+i) := by decide +kernel

theorem threshold_8_42 : ∀ i ∈ List.range 1, ThresholdAt 8 (42+i) := by decide +kernel

theorem threshold_8_43 : ∀ i ∈ List.range 1, ThresholdAt 8 (43+i) := by decide +kernel

theorem threshold_8_44 : ∀ i ∈ List.range 1, ThresholdAt 8 (44+i) := by decide +kernel

theorem threshold_8_45 : ∀ i ∈ List.range 1, ThresholdAt 8 (45+i) := by decide +kernel

theorem threshold_8_46 : ∀ i ∈ List.range 1, ThresholdAt 8 (46+i) := by decide +kernel

theorem threshold_8_47 : ∀ i ∈ List.range 1, ThresholdAt 8 (47+i) := by decide +kernel

theorem threshold_8_48 : ∀ i ∈ List.range 1, ThresholdAt 8 (48+i) := by decide +kernel

theorem threshold_8_49 : ∀ i ∈ List.range 1, ThresholdAt 8 (49+i) := by decide +kernel

theorem threshold_8_50 : ∀ i ∈ List.range 1, ThresholdAt 8 (50+i) := by decide +kernel

theorem threshold_8_51 : ∀ i ∈ List.range 1, ThresholdAt 8 (51+i) := by decide +kernel

theorem threshold_8_52 : ∀ i ∈ List.range 1, ThresholdAt 8 (52+i) := by decide +kernel

theorem threshold_8_53 : ∀ i ∈ List.range 1, ThresholdAt 8 (53+i) := by decide +kernel

theorem threshold_8_54 : ∀ i ∈ List.range 1, ThresholdAt 8 (54+i) := by decide +kernel

theorem threshold_8_55 : ∀ i ∈ List.range 1, ThresholdAt 8 (55+i) := by decide +kernel

theorem threshold_8_56 : ∀ i ∈ List.range 1, ThresholdAt 8 (56+i) := by decide +kernel

theorem threshold_8_57 : ∀ i ∈ List.range 1, ThresholdAt 8 (57+i) := by decide +kernel

theorem threshold_8_58 : ∀ i ∈ List.range 1, ThresholdAt 8 (58+i) := by decide +kernel

theorem threshold_8_59 : ∀ i ∈ List.range 1, ThresholdAt 8 (59+i) := by decide +kernel

theorem threshold_8_60 : ∀ i ∈ List.range 1, ThresholdAt 8 (60+i) := by decide +kernel

theorem threshold_8_61 : ∀ i ∈ List.range 1, ThresholdAt 8 (61+i) := by decide +kernel

theorem threshold_8_62 : ∀ i ∈ List.range 1, ThresholdAt 8 (62+i) := by decide +kernel

theorem threshold_8_63 : ∀ i ∈ List.range 1, ThresholdAt 8 (63+i) := by decide +kernel

theorem threshold_8_64 : ∀ i ∈ List.range 1, ThresholdAt 8 (64+i) := by decide +kernel

theorem threshold_8_65 : ∀ i ∈ List.range 1, ThresholdAt 8 (65+i) := by decide +kernel

theorem threshold_8_66 : ∀ i ∈ List.range 1, ThresholdAt 8 (66+i) := by decide +kernel

theorem threshold_8_67 : ∀ i ∈ List.range 1, ThresholdAt 8 (67+i) := by decide +kernel

theorem threshold_8_68 : ∀ i ∈ List.range 1, ThresholdAt 8 (68+i) := by decide +kernel

theorem threshold_8_69 : ∀ i ∈ List.range 1, ThresholdAt 8 (69+i) := by decide +kernel

theorem threshold_8_70 : ∀ i ∈ List.range 1, ThresholdAt 8 (70+i) := by decide +kernel

theorem threshold_8_71 : ∀ i ∈ List.range 1, ThresholdAt 8 (71+i) := by decide +kernel

theorem threshold_8_72 : ∀ i ∈ List.range 1, ThresholdAt 8 (72+i) := by decide +kernel

theorem threshold_8_73 : ∀ i ∈ List.range 1, ThresholdAt 8 (73+i) := by decide +kernel

theorem threshold_8_74 : ∀ i ∈ List.range 1, ThresholdAt 8 (74+i) := by decide +kernel

theorem threshold_8_75 : ∀ i ∈ List.range 1, ThresholdAt 8 (75+i) := by decide +kernel

theorem threshold_8_76 : ∀ i ∈ List.range 1, ThresholdAt 8 (76+i) := by decide +kernel

theorem threshold_8_77 : ∀ i ∈ List.range 1, ThresholdAt 8 (77+i) := by decide +kernel

theorem threshold_8_78 : ∀ i ∈ List.range 1, ThresholdAt 8 (78+i) := by decide +kernel

theorem threshold_8_79 : ∀ i ∈ List.range 1, ThresholdAt 8 (79+i) := by decide +kernel

theorem threshold_8_80 : ∀ i ∈ List.range 1, ThresholdAt 8 (80+i) := by decide +kernel

theorem threshold_8_81 : ∀ i ∈ List.range 1, ThresholdAt 8 (81+i) := by decide +kernel

theorem threshold_8_82 : ∀ i ∈ List.range 1, ThresholdAt 8 (82+i) := by decide +kernel

theorem threshold_8_83 : ∀ i ∈ List.range 1, ThresholdAt 8 (83+i) := by decide +kernel

theorem threshold_8_84 : ∀ i ∈ List.range 1, ThresholdAt 8 (84+i) := by decide +kernel

theorem threshold_8_85 : ∀ i ∈ List.range 1, ThresholdAt 8 (85+i) := by decide +kernel

theorem threshold_8_86 : ∀ i ∈ List.range 1, ThresholdAt 8 (86+i) := by decide +kernel

theorem threshold_8_87 : ∀ i ∈ List.range 1, ThresholdAt 8 (87+i) := by decide +kernel

theorem threshold_8_88 : ∀ i ∈ List.range 1, ThresholdAt 8 (88+i) := by decide +kernel

theorem threshold_8_89 : ∀ i ∈ List.range 1, ThresholdAt 8 (89+i) := by decide +kernel

theorem threshold_8_90 : ∀ i ∈ List.range 1, ThresholdAt 8 (90+i) := by decide +kernel

theorem threshold_8_91 : ∀ i ∈ List.range 1, ThresholdAt 8 (91+i) := by decide +kernel

theorem threshold_8_92 : ∀ i ∈ List.range 1, ThresholdAt 8 (92+i) := by decide +kernel

theorem threshold_8_93 : ∀ i ∈ List.range 1, ThresholdAt 8 (93+i) := by decide +kernel

theorem threshold_8_94 : ∀ i ∈ List.range 1, ThresholdAt 8 (94+i) := by decide +kernel

theorem threshold_8_95 : ∀ i ∈ List.range 1, ThresholdAt 8 (95+i) := by decide +kernel

theorem threshold_8_96 : ∀ i ∈ List.range 1, ThresholdAt 8 (96+i) := by decide +kernel

theorem threshold_8_97 : ∀ i ∈ List.range 1, ThresholdAt 8 (97+i) := by decide +kernel

theorem threshold_8_98 : ∀ i ∈ List.range 1, ThresholdAt 8 (98+i) := by decide +kernel

theorem threshold_8_99 : ∀ i ∈ List.range 1, ThresholdAt 8 (99+i) := by decide +kernel

theorem threshold_8_100 : ∀ i ∈ List.range 1, ThresholdAt 8 (100+i) := by decide +kernel

theorem threshold_8_101 : ∀ i ∈ List.range 1, ThresholdAt 8 (101+i) := by decide +kernel

theorem threshold_8_102 : ∀ i ∈ List.range 1, ThresholdAt 8 (102+i) := by decide +kernel

theorem threshold_8_103 : ∀ i ∈ List.range 1, ThresholdAt 8 (103+i) := by decide +kernel

theorem threshold_8_104 : ∀ i ∈ List.range 1, ThresholdAt 8 (104+i) := by decide +kernel

theorem threshold_8_105 : ∀ i ∈ List.range 1, ThresholdAt 8 (105+i) := by decide +kernel

theorem threshold_8_106 : ∀ i ∈ List.range 1, ThresholdAt 8 (106+i) := by decide +kernel

theorem threshold_8_107 : ∀ i ∈ List.range 1, ThresholdAt 8 (107+i) := by decide +kernel

theorem threshold_8_108 : ∀ i ∈ List.range 1, ThresholdAt 8 (108+i) := by decide +kernel

theorem threshold_8_109 : ∀ i ∈ List.range 1, ThresholdAt 8 (109+i) := by decide +kernel

theorem threshold_8_110 : ∀ i ∈ List.range 1, ThresholdAt 8 (110+i) := by decide +kernel

theorem threshold_8_111 : ∀ i ∈ List.range 1, ThresholdAt 8 (111+i) := by decide +kernel

theorem threshold_8_112 : ∀ i ∈ List.range 1, ThresholdAt 8 (112+i) := by decide +kernel

theorem threshold_8_113 : ∀ i ∈ List.range 1, ThresholdAt 8 (113+i) := by decide +kernel

theorem threshold_8_114 : ∀ i ∈ List.range 1, ThresholdAt 8 (114+i) := by decide +kernel

theorem threshold_8_115 : ∀ i ∈ List.range 1, ThresholdAt 8 (115+i) := by decide +kernel

theorem threshold_8_116 : ∀ i ∈ List.range 1, ThresholdAt 8 (116+i) := by decide +kernel

theorem threshold_8_117 : ∀ i ∈ List.range 1, ThresholdAt 8 (117+i) := by decide +kernel

theorem threshold_8_118 : ∀ i ∈ List.range 1, ThresholdAt 8 (118+i) := by decide +kernel

theorem threshold_8_119 : ∀ i ∈ List.range 1, ThresholdAt 8 (119+i) := by decide +kernel

theorem threshold_8_120 : ∀ i ∈ List.range 1, ThresholdAt 8 (120+i) := by decide +kernel

theorem threshold_8_121 : ∀ i ∈ List.range 1, ThresholdAt 8 (121+i) := by decide +kernel

theorem threshold_8_122 : ∀ i ∈ List.range 1, ThresholdAt 8 (122+i) := by decide +kernel

theorem threshold_8_123 : ∀ i ∈ List.range 1, ThresholdAt 8 (123+i) := by decide +kernel

theorem threshold_8_124 : ∀ i ∈ List.range 1, ThresholdAt 8 (124+i) := by decide +kernel

theorem threshold_8_125 : ∀ i ∈ List.range 1, ThresholdAt 8 (125+i) := by decide +kernel

theorem threshold_8_126 : ∀ i ∈ List.range 1, ThresholdAt 8 (126+i) := by decide +kernel

theorem threshold_8_127 : ∀ i ∈ List.range 1, ThresholdAt 8 (127+i) := by decide +kernel

theorem threshold_8_128 : ∀ i ∈ List.range 1, ThresholdAt 8 (128+i) := by decide +kernel

theorem threshold_8_129 : ∀ i ∈ List.range 1, ThresholdAt 8 (129+i) := by decide +kernel

theorem threshold_8_130 : ∀ i ∈ List.range 1, ThresholdAt 8 (130+i) := by decide +kernel

theorem threshold_8_131 : ∀ i ∈ List.range 1, ThresholdAt 8 (131+i) := by decide +kernel

theorem threshold_8_132 : ∀ i ∈ List.range 1, ThresholdAt 8 (132+i) := by decide +kernel

theorem threshold_8_133 : ∀ i ∈ List.range 1, ThresholdAt 8 (133+i) := by decide +kernel

theorem threshold_8_134 : ∀ i ∈ List.range 1, ThresholdAt 8 (134+i) := by decide +kernel

theorem threshold_8_135 : ∀ i ∈ List.range 1, ThresholdAt 8 (135+i) := by decide +kernel

theorem threshold_8_136 : ∀ i ∈ List.range 1, ThresholdAt 8 (136+i) := by decide +kernel

theorem threshold_8_137 : ∀ i ∈ List.range 1, ThresholdAt 8 (137+i) := by decide +kernel

theorem threshold_8_138 : ∀ i ∈ List.range 1, ThresholdAt 8 (138+i) := by decide +kernel

theorem threshold_8 (v : ℕ) (hv : v ∈ List.range 139) : ThresholdAt 8 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 8 v)
  have h := (join 0 69 70 (join 0 34 35 (join 0 17 17 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_8_0 threshold_8_1) (join 2 1 1 threshold_8_2 threshold_8_3)) (join 4 2 2 (join 4 1 1 threshold_8_4 threshold_8_5) (join 6 1 1 threshold_8_6 threshold_8_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_8_8 threshold_8_9) (join 10 1 1 threshold_8_10 threshold_8_11)) (join 12 2 3 (join 12 1 1 threshold_8_12 threshold_8_13) (join 14 1 2 threshold_8_14 (join 15 1 1 threshold_8_15 threshold_8_16))))) (join 17 8 9 (join 17 4 4 (join 17 2 2 (join 17 1 1 threshold_8_17 threshold_8_18) (join 19 1 1 threshold_8_19 threshold_8_20)) (join 21 2 2 (join 21 1 1 threshold_8_21 threshold_8_22) (join 23 1 1 threshold_8_23 threshold_8_24))) (join 25 4 5 (join 25 2 2 (join 25 1 1 threshold_8_25 threshold_8_26) (join 27 1 1 threshold_8_27 threshold_8_28)) (join 29 2 3 (join 29 1 1 threshold_8_29 threshold_8_30) (join 31 1 2 threshold_8_31 (join 32 1 1 threshold_8_32 threshold_8_33)))))) (join 34 17 18 (join 34 8 9 (join 34 4 4 (join 34 2 2 (join 34 1 1 threshold_8_34 threshold_8_35) (join 36 1 1 threshold_8_36 threshold_8_37)) (join 38 2 2 (join 38 1 1 threshold_8_38 threshold_8_39) (join 40 1 1 threshold_8_40 threshold_8_41))) (join 42 4 5 (join 42 2 2 (join 42 1 1 threshold_8_42 threshold_8_43) (join 44 1 1 threshold_8_44 threshold_8_45)) (join 46 2 3 (join 46 1 1 threshold_8_46 threshold_8_47) (join 48 1 2 threshold_8_48 (join 49 1 1 threshold_8_49 threshold_8_50))))) (join 51 9 9 (join 51 4 5 (join 51 2 2 (join 51 1 1 threshold_8_51 threshold_8_52) (join 53 1 1 threshold_8_53 threshold_8_54)) (join 55 2 3 (join 55 1 1 threshold_8_55 threshold_8_56) (join 57 1 2 threshold_8_57 (join 58 1 1 threshold_8_58 threshold_8_59)))) (join 60 4 5 (join 60 2 2 (join 60 1 1 threshold_8_60 threshold_8_61) (join 62 1 1 threshold_8_62 threshold_8_63)) (join 64 2 3 (join 64 1 1 threshold_8_64 threshold_8_65) (join 66 1 2 threshold_8_66 (join 67 1 1 threshold_8_67 threshold_8_68))))))) (join 69 35 35 (join 69 17 18 (join 69 8 9 (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_8_69 threshold_8_70) (join 71 1 1 threshold_8_71 threshold_8_72)) (join 73 2 2 (join 73 1 1 threshold_8_73 threshold_8_74) (join 75 1 1 threshold_8_75 threshold_8_76))) (join 77 4 5 (join 77 2 2 (join 77 1 1 threshold_8_77 threshold_8_78) (join 79 1 1 threshold_8_79 threshold_8_80)) (join 81 2 3 (join 81 1 1 threshold_8_81 threshold_8_82) (join 83 1 2 threshold_8_83 (join 84 1 1 threshold_8_84 threshold_8_85))))) (join 86 9 9 (join 86 4 5 (join 86 2 2 (join 86 1 1 threshold_8_86 threshold_8_87) (join 88 1 1 threshold_8_88 threshold_8_89)) (join 90 2 3 (join 90 1 1 threshold_8_90 threshold_8_91) (join 92 1 2 threshold_8_92 (join 93 1 1 threshold_8_93 threshold_8_94)))) (join 95 4 5 (join 95 2 2 (join 95 1 1 threshold_8_95 threshold_8_96) (join 97 1 1 threshold_8_97 threshold_8_98)) (join 99 2 3 (join 99 1 1 threshold_8_99 threshold_8_100) (join 101 1 2 threshold_8_101 (join 102 1 1 threshold_8_102 threshold_8_103)))))) (join 104 17 18 (join 104 8 9 (join 104 4 4 (join 104 2 2 (join 104 1 1 threshold_8_104 threshold_8_105) (join 106 1 1 threshold_8_106 threshold_8_107)) (join 108 2 2 (join 108 1 1 threshold_8_108 threshold_8_109) (join 110 1 1 threshold_8_110 threshold_8_111))) (join 112 4 5 (join 112 2 2 (join 112 1 1 threshold_8_112 threshold_8_113) (join 114 1 1 threshold_8_114 threshold_8_115)) (join 116 2 3 (join 116 1 1 threshold_8_116 threshold_8_117) (join 118 1 2 threshold_8_118 (join 119 1 1 threshold_8_119 threshold_8_120))))) (join 121 9 9 (join 121 4 5 (join 121 2 2 (join 121 1 1 threshold_8_121 threshold_8_122) (join 123 1 1 threshold_8_123 threshold_8_124)) (join 125 2 3 (join 125 1 1 threshold_8_125 threshold_8_126) (join 127 1 2 threshold_8_127 (join 128 1 1 threshold_8_128 threshold_8_129)))) (join 130 4 5 (join 130 2 2 (join 130 1 1 threshold_8_130 threshold_8_131) (join 132 1 1 threshold_8_132 threshold_8_133)) (join 134 2 3 (join 134 1 1 threshold_8_134 threshold_8_135) (join 136 1 2 threshold_8_136 (join 137 1 1 threshold_8_137 threshold_8_138))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_8_0 : ∀ i ∈ List.range 4, LedgerAt 8 (0+i) := by decide +kernel

theorem ledger_8_4 : ∀ i ∈ List.range 4, LedgerAt 8 (4+i) := by decide +kernel

theorem ledger_8_8 : ∀ i ∈ List.range 4, LedgerAt 8 (8+i) := by decide +kernel

theorem ledger_8_12 : ∀ i ∈ List.range 4, LedgerAt 8 (12+i) := by decide +kernel

theorem ledger_8_16 : ∀ i ∈ List.range 4, LedgerAt 8 (16+i) := by decide +kernel

theorem ledger_8_20 : ∀ i ∈ List.range 4, LedgerAt 8 (20+i) := by decide +kernel

theorem ledger_8_24 : ∀ i ∈ List.range 4, LedgerAt 8 (24+i) := by decide +kernel

theorem ledger_8_28 : ∀ i ∈ List.range 4, LedgerAt 8 (28+i) := by decide +kernel

theorem ledger_8_32 : ∀ i ∈ List.range 4, LedgerAt 8 (32+i) := by decide +kernel

theorem ledger_8_36 : ∀ i ∈ List.range 4, LedgerAt 8 (36+i) := by decide +kernel

theorem ledger_8_40 : ∀ i ∈ List.range 4, LedgerAt 8 (40+i) := by decide +kernel

theorem ledger_8_44 : ∀ i ∈ List.range 4, LedgerAt 8 (44+i) := by decide +kernel

theorem ledger_8_48 : ∀ i ∈ List.range 4, LedgerAt 8 (48+i) := by decide +kernel

theorem ledger_8_52 : ∀ i ∈ List.range 4, LedgerAt 8 (52+i) := by decide +kernel

theorem ledger_8_56 : ∀ i ∈ List.range 4, LedgerAt 8 (56+i) := by decide +kernel

theorem ledger_8_60 : ∀ i ∈ List.range 4, LedgerAt 8 (60+i) := by decide +kernel

theorem ledger_8_64 : ∀ i ∈ List.range 4, LedgerAt 8 (64+i) := by decide +kernel

theorem ledger_8_68 : ∀ i ∈ List.range 4, LedgerAt 8 (68+i) := by decide +kernel

theorem ledger_8_72 : ∀ i ∈ List.range 4, LedgerAt 8 (72+i) := by decide +kernel

theorem ledger_8_76 : ∀ i ∈ List.range 4, LedgerAt 8 (76+i) := by decide +kernel

theorem ledger_8_80 : ∀ i ∈ List.range 4, LedgerAt 8 (80+i) := by decide +kernel

theorem ledger_8_84 : ∀ i ∈ List.range 4, LedgerAt 8 (84+i) := by decide +kernel

theorem ledger_8_88 : ∀ i ∈ List.range 4, LedgerAt 8 (88+i) := by decide +kernel

theorem ledger_8_92 : ∀ i ∈ List.range 4, LedgerAt 8 (92+i) := by decide +kernel

theorem ledger_8_96 : ∀ i ∈ List.range 4, LedgerAt 8 (96+i) := by decide +kernel

theorem ledger_8_100 : ∀ i ∈ List.range 4, LedgerAt 8 (100+i) := by decide +kernel

theorem ledger_8_104 : ∀ i ∈ List.range 4, LedgerAt 8 (104+i) := by decide +kernel

theorem ledger_8_108 : ∀ i ∈ List.range 4, LedgerAt 8 (108+i) := by decide +kernel

theorem ledger_8_112 : ∀ i ∈ List.range 4, LedgerAt 8 (112+i) := by decide +kernel

theorem ledger_8_116 : ∀ i ∈ List.range 4, LedgerAt 8 (116+i) := by decide +kernel

theorem ledger_8_120 : ∀ i ∈ List.range 4, LedgerAt 8 (120+i) := by decide +kernel

theorem ledger_8_124 : ∀ i ∈ List.range 4, LedgerAt 8 (124+i) := by decide +kernel

theorem ledger_8_128 : ∀ i ∈ List.range 4, LedgerAt 8 (128+i) := by decide +kernel

theorem ledger_8_132 : ∀ i ∈ List.range 4, LedgerAt 8 (132+i) := by decide +kernel

theorem ledger_8_136 : ∀ i ∈ List.range 3, LedgerAt 8 (136+i) := by decide +kernel

theorem ledger_8 (v : ℕ) (hv : v ∈ List.range 139) : LedgerAt 8 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 8 v)
  have h := (join 0 68 71 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_8_0 ledger_8_4) (join 8 4 4 ledger_8_8 ledger_8_12)) (join 16 8 8 (join 16 4 4 ledger_8_16 ledger_8_20) (join 24 4 4 ledger_8_24 ledger_8_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_8_32 ledger_8_36) (join 40 4 4 ledger_8_40 ledger_8_44)) (join 48 8 12 (join 48 4 4 ledger_8_48 ledger_8_52) (join 56 4 8 ledger_8_56 (join 60 4 4 ledger_8_60 ledger_8_64))))) (join 68 36 35 (join 68 16 20 (join 68 8 8 (join 68 4 4 ledger_8_68 ledger_8_72) (join 76 4 4 ledger_8_76 ledger_8_80)) (join 84 8 12 (join 84 4 4 ledger_8_84 ledger_8_88) (join 92 4 8 ledger_8_92 (join 96 4 4 ledger_8_96 ledger_8_100)))) (join 104 16 19 (join 104 8 8 (join 104 4 4 ledger_8_104 ledger_8_108) (join 112 4 4 ledger_8_112 ledger_8_116)) (join 120 8 11 (join 120 4 4 ledger_8_120 ledger_8_124) (join 128 4 7 ledger_8_128 (join 132 4 3 ledger_8_132 ledger_8_136))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
