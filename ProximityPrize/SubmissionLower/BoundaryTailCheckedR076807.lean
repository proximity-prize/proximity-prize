import ProximityPrize.SubmissionLower.BoundaryTailCheckedR066807
import ProximityPrize.SubmissionLower.BoundaryTailStrictCorners6807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_7_0 : ∀ i ∈ List.range 4, GeometryAt 7 (0+i) := by decide +kernel

theorem geometry_7_4 : ∀ i ∈ List.range 4, GeometryAt 7 (4+i) := by decide +kernel

theorem geometry_7_8 : ∀ i ∈ List.range 4, GeometryAt 7 (8+i) := by decide +kernel

theorem geometry_7_12 : ∀ i ∈ List.range 4, GeometryAt 7 (12+i) := by decide +kernel

theorem geometry_7_16 : ∀ i ∈ List.range 4, GeometryAt 7 (16+i) := by decide +kernel

theorem geometry_7_20 : ∀ i ∈ List.range 4, GeometryAt 7 (20+i) := by decide +kernel

theorem geometry_7_24 : ∀ i ∈ List.range 4, GeometryAt 7 (24+i) := by decide +kernel

theorem geometry_7_28 : ∀ i ∈ List.range 4, GeometryAt 7 (28+i) := by decide +kernel

theorem geometry_7_32 : ∀ i ∈ List.range 4, GeometryAt 7 (32+i) := by decide +kernel

theorem geometry_7_36 : ∀ i ∈ List.range 4, GeometryAt 7 (36+i) := by decide +kernel

theorem geometry_7_40 : ∀ i ∈ List.range 4, GeometryAt 7 (40+i) := by decide +kernel

theorem geometry_7_44 : ∀ i ∈ List.range 4, GeometryAt 7 (44+i) := by decide +kernel

theorem geometry_7_48 : ∀ i ∈ List.range 4, GeometryAt 7 (48+i) := by decide +kernel

theorem geometry_7_52 : ∀ i ∈ List.range 4, GeometryAt 7 (52+i) := by decide +kernel

theorem geometry_7_56 : ∀ i ∈ List.range 4, GeometryAt 7 (56+i) := by decide +kernel

theorem geometry_7_60 : ∀ i ∈ List.range 4, GeometryAt 7 (60+i) := by decide +kernel

theorem geometry_7_64 : ∀ i ∈ List.range 4, GeometryAt 7 (64+i) := by decide +kernel

theorem geometry_7_68 : ∀ i ∈ List.range 4, GeometryAt 7 (68+i) := by decide +kernel

theorem geometry_7_72 : ∀ i ∈ List.range 4, GeometryAt 7 (72+i) := by decide +kernel

theorem geometry_7_76 : ∀ i ∈ List.range 4, GeometryAt 7 (76+i) := by decide +kernel

theorem geometry_7_80 : ∀ i ∈ List.range 4, GeometryAt 7 (80+i) := by decide +kernel

theorem geometry_7_84 : ∀ i ∈ List.range 4, GeometryAt 7 (84+i) := by decide +kernel

theorem geometry_7_88 : ∀ i ∈ List.range 4, GeometryAt 7 (88+i) := by decide +kernel

theorem geometry_7_92 : ∀ i ∈ List.range 4, GeometryAt 7 (92+i) := by decide +kernel

theorem geometry_7_96 : ∀ i ∈ List.range 4, GeometryAt 7 (96+i) := by decide +kernel

theorem geometry_7_100 : ∀ i ∈ List.range 4, GeometryAt 7 (100+i) := by decide +kernel

theorem geometry_7_104 : ∀ i ∈ List.range 4, GeometryAt 7 (104+i) := by decide +kernel

theorem geometry_7_108 : ∀ i ∈ List.range 4, GeometryAt 7 (108+i) := by decide +kernel

theorem geometry_7_112 : ∀ i ∈ List.range 4, GeometryAt 7 (112+i) := by decide +kernel

theorem geometry_7_116 : ∀ i ∈ List.range 4, GeometryAt 7 (116+i) := by decide +kernel

theorem geometry_7_120 : ∀ i ∈ List.range 4, GeometryAt 7 (120+i) := by decide +kernel

theorem geometry_7_124 : ∀ i ∈ List.range 4, GeometryAt 7 (124+i) := by decide +kernel

theorem geometry_7_128 : ∀ i ∈ List.range 4, GeometryAt 7 (128+i) := by decide +kernel

theorem geometry_7_132 : ∀ i ∈ List.range 4, GeometryAt 7 (132+i) := by decide +kernel

theorem geometry_7_136 : ∀ i ∈ List.range 4, GeometryAt 7 (136+i) := by decide +kernel

theorem geometry_7 (v : ℕ) (hv : v ∈ List.range 140) : GeometryAt 7 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 7 v)
  have h := (join 0 68 72 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_7_0 geometry_7_4) (join 8 4 4 geometry_7_8 geometry_7_12)) (join 16 8 8 (join 16 4 4 geometry_7_16 geometry_7_20) (join 24 4 4 geometry_7_24 geometry_7_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 geometry_7_32 geometry_7_36) (join 40 4 4 geometry_7_40 geometry_7_44)) (join 48 8 12 (join 48 4 4 geometry_7_48 geometry_7_52) (join 56 4 8 geometry_7_56 (join 60 4 4 geometry_7_60 geometry_7_64))))) (join 68 36 36 (join 68 16 20 (join 68 8 8 (join 68 4 4 geometry_7_68 geometry_7_72) (join 76 4 4 geometry_7_76 geometry_7_80)) (join 84 8 12 (join 84 4 4 geometry_7_84 geometry_7_88) (join 92 4 8 geometry_7_92 (join 96 4 4 geometry_7_96 geometry_7_100)))) (join 104 16 20 (join 104 8 8 (join 104 4 4 geometry_7_104 geometry_7_108) (join 112 4 4 geometry_7_112 geometry_7_116)) (join 120 8 12 (join 120 4 4 geometry_7_120 geometry_7_124) (join 128 4 8 geometry_7_128 (join 132 4 4 geometry_7_132 geometry_7_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_7_0 : ∀ i ∈ List.range 4, StrictAt 7 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (0+i)) 7 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_4 : ∀ i ∈ List.range 4, StrictAt 7 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (4+i)) 7 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_8 : ∀ i ∈ List.range 4, StrictAt 7 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (8+i)) 7 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_12 : ∀ i ∈ List.range 4, StrictAt 7 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (12+i)) 7 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_16 : ∀ i ∈ List.range 4, StrictAt 7 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (16+i)) 7 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_20 : ∀ i ∈ List.range 4, StrictAt 7 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (20+i)) 7 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_24 : ∀ i ∈ List.range 4, StrictAt 7 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (24+i)) 7 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_28 : ∀ i ∈ List.range 4, StrictAt 7 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (28+i)) 7 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_32 : ∀ i ∈ List.range 4, StrictAt 7 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (32+i)) 7 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_36 : ∀ i ∈ List.range 4, StrictAt 7 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (36+i)) 7 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_40 : ∀ i ∈ List.range 4, StrictAt 7 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (40+i)) 7 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_44 : ∀ i ∈ List.range 4, StrictAt 7 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (44+i)) 7 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_48 : ∀ i ∈ List.range 4, StrictAt 7 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (48+i)) 7 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_52 : ∀ i ∈ List.range 4, StrictAt 7 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (52+i)) 7 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_56 : ∀ i ∈ List.range 4, StrictAt 7 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (56+i)) 7 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_60 : ∀ i ∈ List.range 4, StrictAt 7 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (60+i)) 7 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_64 : ∀ i ∈ List.range 4, StrictAt 7 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (64+i)) 7 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_68 : ∀ i ∈ List.range 4, StrictAt 7 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (68+i)) 7 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_72 : ∀ i ∈ List.range 4, StrictAt 7 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (72+i)) 7 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_76 : ∀ i ∈ List.range 4, StrictAt 7 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (76+i)) 7 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_80 : ∀ i ∈ List.range 4, StrictAt 7 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (80+i)) 7 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_84 : ∀ i ∈ List.range 4, StrictAt 7 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (84+i)) 7 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_88 : ∀ i ∈ List.range 4, StrictAt 7 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (88+i)) 7 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_92 : ∀ i ∈ List.range 4, StrictAt 7 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (92+i)) 7 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_96 : ∀ i ∈ List.range 4, StrictAt 7 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (96+i)) 7 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_100 : ∀ i ∈ List.range 4, StrictAt 7 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (100+i)) 7 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_104 : ∀ i ∈ List.range 4, StrictAt 7 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (104+i)) 7 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_108 : ∀ i ∈ List.range 4, StrictAt 7 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (108+i)) 7 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_112 : ∀ i ∈ List.range 4, StrictAt 7 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (112+i)) 7 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_116 : ∀ i ∈ List.range 4, StrictAt 7 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (116+i)) 7 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_120 : ∀ i ∈ List.range 4, StrictAt 7 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (120+i)) 7 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_124 : ∀ i ∈ List.range 4, StrictAt 7 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (124+i)) 7 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_128 : ∀ i ∈ List.range 4, StrictAt 7 (128+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (128+i)) 7 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_132 : ∀ i ∈ List.range 4, StrictAt 7 (132+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (132+i)) 7 (132+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7_136 : ∀ i ∈ List.range 4, StrictAt 7 (136+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 7 (136+i)) 7 (136+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_7 (v : ℕ) (hv : v ∈ List.range 140) : StrictAt 7 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 7 v)
  have h := (join 0 68 72 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_7_0 strict_7_4) (join 8 4 4 strict_7_8 strict_7_12)) (join 16 8 8 (join 16 4 4 strict_7_16 strict_7_20) (join 24 4 4 strict_7_24 strict_7_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 strict_7_32 strict_7_36) (join 40 4 4 strict_7_40 strict_7_44)) (join 48 8 12 (join 48 4 4 strict_7_48 strict_7_52) (join 56 4 8 strict_7_56 (join 60 4 4 strict_7_60 strict_7_64))))) (join 68 36 36 (join 68 16 20 (join 68 8 8 (join 68 4 4 strict_7_68 strict_7_72) (join 76 4 4 strict_7_76 strict_7_80)) (join 84 8 12 (join 84 4 4 strict_7_84 strict_7_88) (join 92 4 8 strict_7_92 (join 96 4 4 strict_7_96 strict_7_100)))) (join 104 16 20 (join 104 8 8 (join 104 4 4 strict_7_104 strict_7_108) (join 112 4 4 strict_7_112 strict_7_116)) (join 120 8 12 (join 120 4 4 strict_7_120 strict_7_124) (join 128 4 8 strict_7_128 (join 132 4 4 strict_7_132 strict_7_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_7_0 : ∀ i ∈ List.range 4, PhaseAt 7 (0+i) := by decide +kernel

theorem phase_7_4 : ∀ i ∈ List.range 4, PhaseAt 7 (4+i) := by decide +kernel

theorem phase_7_8 : ∀ i ∈ List.range 4, PhaseAt 7 (8+i) := by decide +kernel

theorem phase_7_12 : ∀ i ∈ List.range 4, PhaseAt 7 (12+i) := by decide +kernel

theorem phase_7_16 : ∀ i ∈ List.range 4, PhaseAt 7 (16+i) := by decide +kernel

theorem phase_7_20 : ∀ i ∈ List.range 4, PhaseAt 7 (20+i) := by decide +kernel

theorem phase_7_24 : ∀ i ∈ List.range 4, PhaseAt 7 (24+i) := by decide +kernel

theorem phase_7_28 : ∀ i ∈ List.range 4, PhaseAt 7 (28+i) := by decide +kernel

theorem phase_7_32 : ∀ i ∈ List.range 4, PhaseAt 7 (32+i) := by decide +kernel

theorem phase_7_36 : ∀ i ∈ List.range 4, PhaseAt 7 (36+i) := by decide +kernel

theorem phase_7_40 : ∀ i ∈ List.range 4, PhaseAt 7 (40+i) := by decide +kernel

theorem phase_7_44 : ∀ i ∈ List.range 4, PhaseAt 7 (44+i) := by decide +kernel

theorem phase_7_48 : ∀ i ∈ List.range 4, PhaseAt 7 (48+i) := by decide +kernel

theorem phase_7_52 : ∀ i ∈ List.range 4, PhaseAt 7 (52+i) := by decide +kernel

theorem phase_7_56 : ∀ i ∈ List.range 4, PhaseAt 7 (56+i) := by decide +kernel

theorem phase_7_60 : ∀ i ∈ List.range 4, PhaseAt 7 (60+i) := by decide +kernel

theorem phase_7_64 : ∀ i ∈ List.range 4, PhaseAt 7 (64+i) := by decide +kernel

theorem phase_7_68 : ∀ i ∈ List.range 4, PhaseAt 7 (68+i) := by decide +kernel

theorem phase_7_72 : ∀ i ∈ List.range 4, PhaseAt 7 (72+i) := by decide +kernel

theorem phase_7_76 : ∀ i ∈ List.range 4, PhaseAt 7 (76+i) := by decide +kernel

theorem phase_7_80 : ∀ i ∈ List.range 4, PhaseAt 7 (80+i) := by decide +kernel

theorem phase_7_84 : ∀ i ∈ List.range 4, PhaseAt 7 (84+i) := by decide +kernel

theorem phase_7_88 : ∀ i ∈ List.range 4, PhaseAt 7 (88+i) := by decide +kernel

theorem phase_7_92 : ∀ i ∈ List.range 4, PhaseAt 7 (92+i) := by decide +kernel

theorem phase_7_96 : ∀ i ∈ List.range 4, PhaseAt 7 (96+i) := by decide +kernel

theorem phase_7_100 : ∀ i ∈ List.range 4, PhaseAt 7 (100+i) := by decide +kernel

theorem phase_7_104 : ∀ i ∈ List.range 4, PhaseAt 7 (104+i) := by decide +kernel

theorem phase_7_108 : ∀ i ∈ List.range 4, PhaseAt 7 (108+i) := by decide +kernel

theorem phase_7_112 : ∀ i ∈ List.range 4, PhaseAt 7 (112+i) := by decide +kernel

theorem phase_7_116 : ∀ i ∈ List.range 4, PhaseAt 7 (116+i) := by decide +kernel

theorem phase_7_120 : ∀ i ∈ List.range 4, PhaseAt 7 (120+i) := by decide +kernel

theorem phase_7_124 : ∀ i ∈ List.range 4, PhaseAt 7 (124+i) := by decide +kernel

theorem phase_7_128 : ∀ i ∈ List.range 4, PhaseAt 7 (128+i) := by decide +kernel

theorem phase_7_132 : ∀ i ∈ List.range 4, PhaseAt 7 (132+i) := by decide +kernel

theorem phase_7_136 : ∀ i ∈ List.range 4, PhaseAt 7 (136+i) := by decide +kernel

theorem phase_7 (v : ℕ) (hv : v ∈ List.range 140) : PhaseAt 7 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 7 v)
  have h := (join 0 68 72 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_7_0 phase_7_4) (join 8 4 4 phase_7_8 phase_7_12)) (join 16 8 8 (join 16 4 4 phase_7_16 phase_7_20) (join 24 4 4 phase_7_24 phase_7_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_7_32 phase_7_36) (join 40 4 4 phase_7_40 phase_7_44)) (join 48 8 12 (join 48 4 4 phase_7_48 phase_7_52) (join 56 4 8 phase_7_56 (join 60 4 4 phase_7_60 phase_7_64))))) (join 68 36 36 (join 68 16 20 (join 68 8 8 (join 68 4 4 phase_7_68 phase_7_72) (join 76 4 4 phase_7_76 phase_7_80)) (join 84 8 12 (join 84 4 4 phase_7_84 phase_7_88) (join 92 4 8 phase_7_92 (join 96 4 4 phase_7_96 phase_7_100)))) (join 104 16 20 (join 104 8 8 (join 104 4 4 phase_7_104 phase_7_108) (join 112 4 4 phase_7_112 phase_7_116)) (join 120 8 12 (join 120 4 4 phase_7_120 phase_7_124) (join 128 4 8 phase_7_128 (join 132 4 4 phase_7_132 phase_7_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_7_0 : ∀ i ∈ List.range 1, ThresholdAt 7 (0+i) := by decide +kernel

theorem threshold_7_1 : ∀ i ∈ List.range 1, ThresholdAt 7 (1+i) := by decide +kernel

theorem threshold_7_2 : ∀ i ∈ List.range 1, ThresholdAt 7 (2+i) := by decide +kernel

theorem threshold_7_3 : ∀ i ∈ List.range 1, ThresholdAt 7 (3+i) := by decide +kernel

theorem threshold_7_4 : ∀ i ∈ List.range 1, ThresholdAt 7 (4+i) := by decide +kernel

theorem threshold_7_5 : ∀ i ∈ List.range 1, ThresholdAt 7 (5+i) := by decide +kernel

theorem threshold_7_6 : ∀ i ∈ List.range 1, ThresholdAt 7 (6+i) := by decide +kernel

theorem threshold_7_7 : ∀ i ∈ List.range 1, ThresholdAt 7 (7+i) := by decide +kernel

theorem threshold_7_8 : ∀ i ∈ List.range 1, ThresholdAt 7 (8+i) := by decide +kernel

theorem threshold_7_9 : ∀ i ∈ List.range 1, ThresholdAt 7 (9+i) := by decide +kernel

theorem threshold_7_10 : ∀ i ∈ List.range 1, ThresholdAt 7 (10+i) := by decide +kernel

theorem threshold_7_11 : ∀ i ∈ List.range 1, ThresholdAt 7 (11+i) := by decide +kernel

theorem threshold_7_12 : ∀ i ∈ List.range 1, ThresholdAt 7 (12+i) := by decide +kernel

theorem threshold_7_13 : ∀ i ∈ List.range 1, ThresholdAt 7 (13+i) := by decide +kernel

theorem threshold_7_14 : ∀ i ∈ List.range 1, ThresholdAt 7 (14+i) := by decide +kernel

theorem threshold_7_15 : ∀ i ∈ List.range 1, ThresholdAt 7 (15+i) := by decide +kernel

theorem threshold_7_16 : ∀ i ∈ List.range 1, ThresholdAt 7 (16+i) := by decide +kernel

theorem threshold_7_17 : ∀ i ∈ List.range 1, ThresholdAt 7 (17+i) := by decide +kernel

theorem threshold_7_18 : ∀ i ∈ List.range 1, ThresholdAt 7 (18+i) := by decide +kernel

theorem threshold_7_19 : ∀ i ∈ List.range 1, ThresholdAt 7 (19+i) := by decide +kernel

theorem threshold_7_20 : ∀ i ∈ List.range 1, ThresholdAt 7 (20+i) := by decide +kernel

theorem threshold_7_21 : ∀ i ∈ List.range 1, ThresholdAt 7 (21+i) := by decide +kernel

theorem threshold_7_22 : ∀ i ∈ List.range 1, ThresholdAt 7 (22+i) := by decide +kernel

theorem threshold_7_23 : ∀ i ∈ List.range 1, ThresholdAt 7 (23+i) := by decide +kernel

theorem threshold_7_24 : ∀ i ∈ List.range 1, ThresholdAt 7 (24+i) := by decide +kernel

theorem threshold_7_25 : ∀ i ∈ List.range 1, ThresholdAt 7 (25+i) := by decide +kernel

theorem threshold_7_26 : ∀ i ∈ List.range 1, ThresholdAt 7 (26+i) := by decide +kernel

theorem threshold_7_27 : ∀ i ∈ List.range 1, ThresholdAt 7 (27+i) := by decide +kernel

theorem threshold_7_28 : ∀ i ∈ List.range 1, ThresholdAt 7 (28+i) := by decide +kernel

theorem threshold_7_29 : ∀ i ∈ List.range 1, ThresholdAt 7 (29+i) := by decide +kernel

theorem threshold_7_30 : ∀ i ∈ List.range 1, ThresholdAt 7 (30+i) := by decide +kernel

theorem threshold_7_31 : ∀ i ∈ List.range 1, ThresholdAt 7 (31+i) := by decide +kernel

theorem threshold_7_32 : ∀ i ∈ List.range 1, ThresholdAt 7 (32+i) := by decide +kernel

theorem threshold_7_33 : ∀ i ∈ List.range 1, ThresholdAt 7 (33+i) := by decide +kernel

theorem threshold_7_34 : ∀ i ∈ List.range 1, ThresholdAt 7 (34+i) := by decide +kernel

theorem threshold_7_35 : ∀ i ∈ List.range 1, ThresholdAt 7 (35+i) := by decide +kernel

theorem threshold_7_36 : ∀ i ∈ List.range 1, ThresholdAt 7 (36+i) := by decide +kernel

theorem threshold_7_37 : ∀ i ∈ List.range 1, ThresholdAt 7 (37+i) := by decide +kernel

theorem threshold_7_38 : ∀ i ∈ List.range 1, ThresholdAt 7 (38+i) := by decide +kernel

theorem threshold_7_39 : ∀ i ∈ List.range 1, ThresholdAt 7 (39+i) := by decide +kernel

theorem threshold_7_40 : ∀ i ∈ List.range 1, ThresholdAt 7 (40+i) := by decide +kernel

theorem threshold_7_41 : ∀ i ∈ List.range 1, ThresholdAt 7 (41+i) := by decide +kernel

theorem threshold_7_42 : ∀ i ∈ List.range 1, ThresholdAt 7 (42+i) := by decide +kernel

theorem threshold_7_43 : ∀ i ∈ List.range 1, ThresholdAt 7 (43+i) := by decide +kernel

theorem threshold_7_44 : ∀ i ∈ List.range 1, ThresholdAt 7 (44+i) := by decide +kernel

theorem threshold_7_45 : ∀ i ∈ List.range 1, ThresholdAt 7 (45+i) := by decide +kernel

theorem threshold_7_46 : ∀ i ∈ List.range 1, ThresholdAt 7 (46+i) := by decide +kernel

theorem threshold_7_47 : ∀ i ∈ List.range 1, ThresholdAt 7 (47+i) := by decide +kernel

theorem threshold_7_48 : ∀ i ∈ List.range 1, ThresholdAt 7 (48+i) := by decide +kernel

theorem threshold_7_49 : ∀ i ∈ List.range 1, ThresholdAt 7 (49+i) := by decide +kernel

theorem threshold_7_50 : ∀ i ∈ List.range 1, ThresholdAt 7 (50+i) := by decide +kernel

theorem threshold_7_51 : ∀ i ∈ List.range 1, ThresholdAt 7 (51+i) := by decide +kernel

theorem threshold_7_52 : ∀ i ∈ List.range 1, ThresholdAt 7 (52+i) := by decide +kernel

theorem threshold_7_53 : ∀ i ∈ List.range 1, ThresholdAt 7 (53+i) := by decide +kernel

theorem threshold_7_54 : ∀ i ∈ List.range 1, ThresholdAt 7 (54+i) := by decide +kernel

theorem threshold_7_55 : ∀ i ∈ List.range 1, ThresholdAt 7 (55+i) := by decide +kernel

theorem threshold_7_56 : ∀ i ∈ List.range 1, ThresholdAt 7 (56+i) := by decide +kernel

theorem threshold_7_57 : ∀ i ∈ List.range 1, ThresholdAt 7 (57+i) := by decide +kernel

theorem threshold_7_58 : ∀ i ∈ List.range 1, ThresholdAt 7 (58+i) := by decide +kernel

theorem threshold_7_59 : ∀ i ∈ List.range 1, ThresholdAt 7 (59+i) := by decide +kernel

theorem threshold_7_60 : ∀ i ∈ List.range 1, ThresholdAt 7 (60+i) := by decide +kernel

theorem threshold_7_61 : ∀ i ∈ List.range 1, ThresholdAt 7 (61+i) := by decide +kernel

theorem threshold_7_62 : ∀ i ∈ List.range 1, ThresholdAt 7 (62+i) := by decide +kernel

theorem threshold_7_63 : ∀ i ∈ List.range 1, ThresholdAt 7 (63+i) := by decide +kernel

theorem threshold_7_64 : ∀ i ∈ List.range 1, ThresholdAt 7 (64+i) := by decide +kernel

theorem threshold_7_65 : ∀ i ∈ List.range 1, ThresholdAt 7 (65+i) := by decide +kernel

theorem threshold_7_66 : ∀ i ∈ List.range 1, ThresholdAt 7 (66+i) := by decide +kernel

theorem threshold_7_67 : ∀ i ∈ List.range 1, ThresholdAt 7 (67+i) := by decide +kernel

theorem threshold_7_68 : ∀ i ∈ List.range 1, ThresholdAt 7 (68+i) := by decide +kernel

theorem threshold_7_69 : ∀ i ∈ List.range 1, ThresholdAt 7 (69+i) := by decide +kernel

theorem threshold_7_70 : ∀ i ∈ List.range 1, ThresholdAt 7 (70+i) := by decide +kernel

theorem threshold_7_71 : ∀ i ∈ List.range 1, ThresholdAt 7 (71+i) := by decide +kernel

theorem threshold_7_72 : ∀ i ∈ List.range 1, ThresholdAt 7 (72+i) := by decide +kernel

theorem threshold_7_73 : ∀ i ∈ List.range 1, ThresholdAt 7 (73+i) := by decide +kernel

theorem threshold_7_74 : ∀ i ∈ List.range 1, ThresholdAt 7 (74+i) := by decide +kernel

theorem threshold_7_75 : ∀ i ∈ List.range 1, ThresholdAt 7 (75+i) := by decide +kernel

theorem threshold_7_76 : ∀ i ∈ List.range 1, ThresholdAt 7 (76+i) := by decide +kernel

theorem threshold_7_77 : ∀ i ∈ List.range 1, ThresholdAt 7 (77+i) := by decide +kernel

theorem threshold_7_78 : ∀ i ∈ List.range 1, ThresholdAt 7 (78+i) := by decide +kernel

theorem threshold_7_79 : ∀ i ∈ List.range 1, ThresholdAt 7 (79+i) := by decide +kernel

theorem threshold_7_80 : ∀ i ∈ List.range 1, ThresholdAt 7 (80+i) := by decide +kernel

theorem threshold_7_81 : ∀ i ∈ List.range 1, ThresholdAt 7 (81+i) := by decide +kernel

theorem threshold_7_82 : ∀ i ∈ List.range 1, ThresholdAt 7 (82+i) := by decide +kernel

theorem threshold_7_83 : ∀ i ∈ List.range 1, ThresholdAt 7 (83+i) := by decide +kernel

theorem threshold_7_84 : ∀ i ∈ List.range 1, ThresholdAt 7 (84+i) := by decide +kernel

theorem threshold_7_85 : ∀ i ∈ List.range 1, ThresholdAt 7 (85+i) := by decide +kernel

theorem threshold_7_86 : ∀ i ∈ List.range 1, ThresholdAt 7 (86+i) := by decide +kernel

theorem threshold_7_87 : ∀ i ∈ List.range 1, ThresholdAt 7 (87+i) := by decide +kernel

theorem threshold_7_88 : ∀ i ∈ List.range 1, ThresholdAt 7 (88+i) := by decide +kernel

theorem threshold_7_89 : ∀ i ∈ List.range 1, ThresholdAt 7 (89+i) := by decide +kernel

theorem threshold_7_90 : ∀ i ∈ List.range 1, ThresholdAt 7 (90+i) := by decide +kernel

theorem threshold_7_91 : ∀ i ∈ List.range 1, ThresholdAt 7 (91+i) := by decide +kernel

theorem threshold_7_92 : ∀ i ∈ List.range 1, ThresholdAt 7 (92+i) := by decide +kernel

theorem threshold_7_93 : ∀ i ∈ List.range 1, ThresholdAt 7 (93+i) := by decide +kernel

theorem threshold_7_94 : ∀ i ∈ List.range 1, ThresholdAt 7 (94+i) := by decide +kernel

theorem threshold_7_95 : ∀ i ∈ List.range 1, ThresholdAt 7 (95+i) := by decide +kernel

theorem threshold_7_96 : ∀ i ∈ List.range 1, ThresholdAt 7 (96+i) := by decide +kernel

theorem threshold_7_97 : ∀ i ∈ List.range 1, ThresholdAt 7 (97+i) := by decide +kernel

theorem threshold_7_98 : ∀ i ∈ List.range 1, ThresholdAt 7 (98+i) := by decide +kernel

theorem threshold_7_99 : ∀ i ∈ List.range 1, ThresholdAt 7 (99+i) := by decide +kernel

theorem threshold_7_100 : ∀ i ∈ List.range 1, ThresholdAt 7 (100+i) := by decide +kernel

theorem threshold_7_101 : ∀ i ∈ List.range 1, ThresholdAt 7 (101+i) := by decide +kernel

theorem threshold_7_102 : ∀ i ∈ List.range 1, ThresholdAt 7 (102+i) := by decide +kernel

theorem threshold_7_103 : ∀ i ∈ List.range 1, ThresholdAt 7 (103+i) := by decide +kernel

theorem threshold_7_104 : ∀ i ∈ List.range 1, ThresholdAt 7 (104+i) := by decide +kernel

theorem threshold_7_105 : ∀ i ∈ List.range 1, ThresholdAt 7 (105+i) := by decide +kernel

theorem threshold_7_106 : ∀ i ∈ List.range 1, ThresholdAt 7 (106+i) := by decide +kernel

theorem threshold_7_107 : ∀ i ∈ List.range 1, ThresholdAt 7 (107+i) := by decide +kernel

theorem threshold_7_108 : ∀ i ∈ List.range 1, ThresholdAt 7 (108+i) := by decide +kernel

theorem threshold_7_109 : ∀ i ∈ List.range 1, ThresholdAt 7 (109+i) := by decide +kernel

theorem threshold_7_110 : ∀ i ∈ List.range 1, ThresholdAt 7 (110+i) := by decide +kernel

theorem threshold_7_111 : ∀ i ∈ List.range 1, ThresholdAt 7 (111+i) := by decide +kernel

theorem threshold_7_112 : ∀ i ∈ List.range 1, ThresholdAt 7 (112+i) := by decide +kernel

theorem threshold_7_113 : ∀ i ∈ List.range 1, ThresholdAt 7 (113+i) := by decide +kernel

theorem threshold_7_114 : ∀ i ∈ List.range 1, ThresholdAt 7 (114+i) := by decide +kernel

theorem threshold_7_115 : ∀ i ∈ List.range 1, ThresholdAt 7 (115+i) := by decide +kernel

theorem threshold_7_116 : ∀ i ∈ List.range 1, ThresholdAt 7 (116+i) := by decide +kernel

theorem threshold_7_117 : ∀ i ∈ List.range 1, ThresholdAt 7 (117+i) := by decide +kernel

theorem threshold_7_118 : ∀ i ∈ List.range 1, ThresholdAt 7 (118+i) := by decide +kernel

theorem threshold_7_119 : ∀ i ∈ List.range 1, ThresholdAt 7 (119+i) := by decide +kernel

theorem threshold_7_120 : ∀ i ∈ List.range 1, ThresholdAt 7 (120+i) := by decide +kernel

theorem threshold_7_121 : ∀ i ∈ List.range 1, ThresholdAt 7 (121+i) := by decide +kernel

theorem threshold_7_122 : ∀ i ∈ List.range 1, ThresholdAt 7 (122+i) := by decide +kernel

theorem threshold_7_123 : ∀ i ∈ List.range 1, ThresholdAt 7 (123+i) := by decide +kernel

theorem threshold_7_124 : ∀ i ∈ List.range 1, ThresholdAt 7 (124+i) := by decide +kernel

theorem threshold_7_125 : ∀ i ∈ List.range 1, ThresholdAt 7 (125+i) := by decide +kernel

theorem threshold_7_126 : ∀ i ∈ List.range 1, ThresholdAt 7 (126+i) := by decide +kernel

theorem threshold_7_127 : ∀ i ∈ List.range 1, ThresholdAt 7 (127+i) := by decide +kernel

theorem threshold_7_128 : ∀ i ∈ List.range 1, ThresholdAt 7 (128+i) := by decide +kernel

theorem threshold_7_129 : ∀ i ∈ List.range 1, ThresholdAt 7 (129+i) := by decide +kernel

theorem threshold_7_130 : ∀ i ∈ List.range 1, ThresholdAt 7 (130+i) := by decide +kernel

theorem threshold_7_131 : ∀ i ∈ List.range 1, ThresholdAt 7 (131+i) := by decide +kernel

theorem threshold_7_132 : ∀ i ∈ List.range 1, ThresholdAt 7 (132+i) := by decide +kernel

theorem threshold_7_133 : ∀ i ∈ List.range 1, ThresholdAt 7 (133+i) := by decide +kernel

theorem threshold_7_134 : ∀ i ∈ List.range 1, ThresholdAt 7 (134+i) := by decide +kernel

theorem threshold_7_135 : ∀ i ∈ List.range 1, ThresholdAt 7 (135+i) := by decide +kernel

theorem threshold_7_136 : ∀ i ∈ List.range 1, ThresholdAt 7 (136+i) := by decide +kernel

theorem threshold_7_137 : ∀ i ∈ List.range 1, ThresholdAt 7 (137+i) := by decide +kernel

theorem threshold_7_138 : ∀ i ∈ List.range 1, ThresholdAt 7 (138+i) := by decide +kernel

theorem threshold_7_139 : ∀ i ∈ List.range 1, ThresholdAt 7 (139+i) := by decide +kernel

theorem threshold_7 (v : ℕ) (hv : v ∈ List.range 140) : ThresholdAt 7 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 7 v)
  have h := (join 0 70 70 (join 0 35 35 (join 0 17 18 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_7_0 threshold_7_1) (join 2 1 1 threshold_7_2 threshold_7_3)) (join 4 2 2 (join 4 1 1 threshold_7_4 threshold_7_5) (join 6 1 1 threshold_7_6 threshold_7_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_7_8 threshold_7_9) (join 10 1 1 threshold_7_10 threshold_7_11)) (join 12 2 3 (join 12 1 1 threshold_7_12 threshold_7_13) (join 14 1 2 threshold_7_14 (join 15 1 1 threshold_7_15 threshold_7_16))))) (join 17 9 9 (join 17 4 5 (join 17 2 2 (join 17 1 1 threshold_7_17 threshold_7_18) (join 19 1 1 threshold_7_19 threshold_7_20)) (join 21 2 3 (join 21 1 1 threshold_7_21 threshold_7_22) (join 23 1 2 threshold_7_23 (join 24 1 1 threshold_7_24 threshold_7_25)))) (join 26 4 5 (join 26 2 2 (join 26 1 1 threshold_7_26 threshold_7_27) (join 28 1 1 threshold_7_28 threshold_7_29)) (join 30 2 3 (join 30 1 1 threshold_7_30 threshold_7_31) (join 32 1 2 threshold_7_32 (join 33 1 1 threshold_7_33 threshold_7_34)))))) (join 35 17 18 (join 35 8 9 (join 35 4 4 (join 35 2 2 (join 35 1 1 threshold_7_35 threshold_7_36) (join 37 1 1 threshold_7_37 threshold_7_38)) (join 39 2 2 (join 39 1 1 threshold_7_39 threshold_7_40) (join 41 1 1 threshold_7_41 threshold_7_42))) (join 43 4 5 (join 43 2 2 (join 43 1 1 threshold_7_43 threshold_7_44) (join 45 1 1 threshold_7_45 threshold_7_46)) (join 47 2 3 (join 47 1 1 threshold_7_47 threshold_7_48) (join 49 1 2 threshold_7_49 (join 50 1 1 threshold_7_50 threshold_7_51))))) (join 52 9 9 (join 52 4 5 (join 52 2 2 (join 52 1 1 threshold_7_52 threshold_7_53) (join 54 1 1 threshold_7_54 threshold_7_55)) (join 56 2 3 (join 56 1 1 threshold_7_56 threshold_7_57) (join 58 1 2 threshold_7_58 (join 59 1 1 threshold_7_59 threshold_7_60)))) (join 61 4 5 (join 61 2 2 (join 61 1 1 threshold_7_61 threshold_7_62) (join 63 1 1 threshold_7_63 threshold_7_64)) (join 65 2 3 (join 65 1 1 threshold_7_65 threshold_7_66) (join 67 1 2 threshold_7_67 (join 68 1 1 threshold_7_68 threshold_7_69))))))) (join 70 35 35 (join 70 17 18 (join 70 8 9 (join 70 4 4 (join 70 2 2 (join 70 1 1 threshold_7_70 threshold_7_71) (join 72 1 1 threshold_7_72 threshold_7_73)) (join 74 2 2 (join 74 1 1 threshold_7_74 threshold_7_75) (join 76 1 1 threshold_7_76 threshold_7_77))) (join 78 4 5 (join 78 2 2 (join 78 1 1 threshold_7_78 threshold_7_79) (join 80 1 1 threshold_7_80 threshold_7_81)) (join 82 2 3 (join 82 1 1 threshold_7_82 threshold_7_83) (join 84 1 2 threshold_7_84 (join 85 1 1 threshold_7_85 threshold_7_86))))) (join 87 9 9 (join 87 4 5 (join 87 2 2 (join 87 1 1 threshold_7_87 threshold_7_88) (join 89 1 1 threshold_7_89 threshold_7_90)) (join 91 2 3 (join 91 1 1 threshold_7_91 threshold_7_92) (join 93 1 2 threshold_7_93 (join 94 1 1 threshold_7_94 threshold_7_95)))) (join 96 4 5 (join 96 2 2 (join 96 1 1 threshold_7_96 threshold_7_97) (join 98 1 1 threshold_7_98 threshold_7_99)) (join 100 2 3 (join 100 1 1 threshold_7_100 threshold_7_101) (join 102 1 2 threshold_7_102 (join 103 1 1 threshold_7_103 threshold_7_104)))))) (join 105 17 18 (join 105 8 9 (join 105 4 4 (join 105 2 2 (join 105 1 1 threshold_7_105 threshold_7_106) (join 107 1 1 threshold_7_107 threshold_7_108)) (join 109 2 2 (join 109 1 1 threshold_7_109 threshold_7_110) (join 111 1 1 threshold_7_111 threshold_7_112))) (join 113 4 5 (join 113 2 2 (join 113 1 1 threshold_7_113 threshold_7_114) (join 115 1 1 threshold_7_115 threshold_7_116)) (join 117 2 3 (join 117 1 1 threshold_7_117 threshold_7_118) (join 119 1 2 threshold_7_119 (join 120 1 1 threshold_7_120 threshold_7_121))))) (join 122 9 9 (join 122 4 5 (join 122 2 2 (join 122 1 1 threshold_7_122 threshold_7_123) (join 124 1 1 threshold_7_124 threshold_7_125)) (join 126 2 3 (join 126 1 1 threshold_7_126 threshold_7_127) (join 128 1 2 threshold_7_128 (join 129 1 1 threshold_7_129 threshold_7_130)))) (join 131 4 5 (join 131 2 2 (join 131 1 1 threshold_7_131 threshold_7_132) (join 133 1 1 threshold_7_133 threshold_7_134)) (join 135 2 3 (join 135 1 1 threshold_7_135 threshold_7_136) (join 137 1 2 threshold_7_137 (join 138 1 1 threshold_7_138 threshold_7_139))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_7_0 : ∀ i ∈ List.range 4, LedgerAt 7 (0+i) := by decide +kernel

theorem ledger_7_4 : ∀ i ∈ List.range 4, LedgerAt 7 (4+i) := by decide +kernel

theorem ledger_7_8 : ∀ i ∈ List.range 4, LedgerAt 7 (8+i) := by decide +kernel

theorem ledger_7_12 : ∀ i ∈ List.range 4, LedgerAt 7 (12+i) := by decide +kernel

theorem ledger_7_16 : ∀ i ∈ List.range 4, LedgerAt 7 (16+i) := by decide +kernel

theorem ledger_7_20 : ∀ i ∈ List.range 4, LedgerAt 7 (20+i) := by decide +kernel

theorem ledger_7_24 : ∀ i ∈ List.range 4, LedgerAt 7 (24+i) := by decide +kernel

theorem ledger_7_28 : ∀ i ∈ List.range 4, LedgerAt 7 (28+i) := by decide +kernel

theorem ledger_7_32 : ∀ i ∈ List.range 4, LedgerAt 7 (32+i) := by decide +kernel

theorem ledger_7_36 : ∀ i ∈ List.range 4, LedgerAt 7 (36+i) := by decide +kernel

theorem ledger_7_40 : ∀ i ∈ List.range 4, LedgerAt 7 (40+i) := by decide +kernel

theorem ledger_7_44 : ∀ i ∈ List.range 4, LedgerAt 7 (44+i) := by decide +kernel

theorem ledger_7_48 : ∀ i ∈ List.range 4, LedgerAt 7 (48+i) := by decide +kernel

theorem ledger_7_52 : ∀ i ∈ List.range 4, LedgerAt 7 (52+i) := by decide +kernel

theorem ledger_7_56 : ∀ i ∈ List.range 4, LedgerAt 7 (56+i) := by decide +kernel

theorem ledger_7_60 : ∀ i ∈ List.range 4, LedgerAt 7 (60+i) := by decide +kernel

theorem ledger_7_64 : ∀ i ∈ List.range 4, LedgerAt 7 (64+i) := by decide +kernel

theorem ledger_7_68 : ∀ i ∈ List.range 4, LedgerAt 7 (68+i) := by decide +kernel

theorem ledger_7_72 : ∀ i ∈ List.range 4, LedgerAt 7 (72+i) := by decide +kernel

theorem ledger_7_76 : ∀ i ∈ List.range 4, LedgerAt 7 (76+i) := by decide +kernel

theorem ledger_7_80 : ∀ i ∈ List.range 4, LedgerAt 7 (80+i) := by decide +kernel

theorem ledger_7_84 : ∀ i ∈ List.range 4, LedgerAt 7 (84+i) := by decide +kernel

theorem ledger_7_88 : ∀ i ∈ List.range 4, LedgerAt 7 (88+i) := by decide +kernel

theorem ledger_7_92 : ∀ i ∈ List.range 4, LedgerAt 7 (92+i) := by decide +kernel

theorem ledger_7_96 : ∀ i ∈ List.range 4, LedgerAt 7 (96+i) := by decide +kernel

theorem ledger_7_100 : ∀ i ∈ List.range 4, LedgerAt 7 (100+i) := by decide +kernel

theorem ledger_7_104 : ∀ i ∈ List.range 4, LedgerAt 7 (104+i) := by decide +kernel

theorem ledger_7_108 : ∀ i ∈ List.range 4, LedgerAt 7 (108+i) := by decide +kernel

theorem ledger_7_112 : ∀ i ∈ List.range 4, LedgerAt 7 (112+i) := by decide +kernel

theorem ledger_7_116 : ∀ i ∈ List.range 4, LedgerAt 7 (116+i) := by decide +kernel

theorem ledger_7_120 : ∀ i ∈ List.range 4, LedgerAt 7 (120+i) := by decide +kernel

theorem ledger_7_124 : ∀ i ∈ List.range 4, LedgerAt 7 (124+i) := by decide +kernel

theorem ledger_7_128 : ∀ i ∈ List.range 4, LedgerAt 7 (128+i) := by decide +kernel

theorem ledger_7_132 : ∀ i ∈ List.range 4, LedgerAt 7 (132+i) := by decide +kernel

theorem ledger_7_136 : ∀ i ∈ List.range 4, LedgerAt 7 (136+i) := by decide +kernel

theorem ledger_7 (v : ℕ) (hv : v ∈ List.range 140) : LedgerAt 7 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 7 v)
  have h := (join 0 68 72 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_7_0 ledger_7_4) (join 8 4 4 ledger_7_8 ledger_7_12)) (join 16 8 8 (join 16 4 4 ledger_7_16 ledger_7_20) (join 24 4 4 ledger_7_24 ledger_7_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_7_32 ledger_7_36) (join 40 4 4 ledger_7_40 ledger_7_44)) (join 48 8 12 (join 48 4 4 ledger_7_48 ledger_7_52) (join 56 4 8 ledger_7_56 (join 60 4 4 ledger_7_60 ledger_7_64))))) (join 68 36 36 (join 68 16 20 (join 68 8 8 (join 68 4 4 ledger_7_68 ledger_7_72) (join 76 4 4 ledger_7_76 ledger_7_80)) (join 84 8 12 (join 84 4 4 ledger_7_84 ledger_7_88) (join 92 4 8 ledger_7_92 (join 96 4 4 ledger_7_96 ledger_7_100)))) (join 104 16 20 (join 104 8 8 (join 104 4 4 ledger_7_104 ledger_7_108) (join 112 4 4 ledger_7_112 ledger_7_116)) (join 120 8 12 (join 120 4 4 ledger_7_120 ledger_7_124) (join 128 4 8 ledger_7_128 (join 132 4 4 ledger_7_132 ledger_7_136))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
