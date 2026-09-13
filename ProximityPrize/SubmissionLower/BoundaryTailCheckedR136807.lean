import ProximityPrize.SubmissionLower.BoundaryTailCheckedR126807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_13_0 : ∀ i ∈ List.range 4, GeometryAt 13 (0+i) := by decide +kernel

theorem geometry_13_4 : ∀ i ∈ List.range 4, GeometryAt 13 (4+i) := by decide +kernel

theorem geometry_13_8 : ∀ i ∈ List.range 4, GeometryAt 13 (8+i) := by decide +kernel

theorem geometry_13_12 : ∀ i ∈ List.range 4, GeometryAt 13 (12+i) := by decide +kernel

theorem geometry_13_16 : ∀ i ∈ List.range 4, GeometryAt 13 (16+i) := by decide +kernel

theorem geometry_13_20 : ∀ i ∈ List.range 4, GeometryAt 13 (20+i) := by decide +kernel

theorem geometry_13_24 : ∀ i ∈ List.range 4, GeometryAt 13 (24+i) := by decide +kernel

theorem geometry_13_28 : ∀ i ∈ List.range 4, GeometryAt 13 (28+i) := by decide +kernel

theorem geometry_13_32 : ∀ i ∈ List.range 4, GeometryAt 13 (32+i) := by decide +kernel

theorem geometry_13_36 : ∀ i ∈ List.range 4, GeometryAt 13 (36+i) := by decide +kernel

theorem geometry_13_40 : ∀ i ∈ List.range 4, GeometryAt 13 (40+i) := by decide +kernel

theorem geometry_13_44 : ∀ i ∈ List.range 4, GeometryAt 13 (44+i) := by decide +kernel

theorem geometry_13_48 : ∀ i ∈ List.range 4, GeometryAt 13 (48+i) := by decide +kernel

theorem geometry_13_52 : ∀ i ∈ List.range 4, GeometryAt 13 (52+i) := by decide +kernel

theorem geometry_13_56 : ∀ i ∈ List.range 4, GeometryAt 13 (56+i) := by decide +kernel

theorem geometry_13_60 : ∀ i ∈ List.range 4, GeometryAt 13 (60+i) := by decide +kernel

theorem geometry_13_64 : ∀ i ∈ List.range 4, GeometryAt 13 (64+i) := by decide +kernel

theorem geometry_13_68 : ∀ i ∈ List.range 4, GeometryAt 13 (68+i) := by decide +kernel

theorem geometry_13_72 : ∀ i ∈ List.range 4, GeometryAt 13 (72+i) := by decide +kernel

theorem geometry_13_76 : ∀ i ∈ List.range 4, GeometryAt 13 (76+i) := by decide +kernel

theorem geometry_13_80 : ∀ i ∈ List.range 4, GeometryAt 13 (80+i) := by decide +kernel

theorem geometry_13_84 : ∀ i ∈ List.range 4, GeometryAt 13 (84+i) := by decide +kernel

theorem geometry_13_88 : ∀ i ∈ List.range 4, GeometryAt 13 (88+i) := by decide +kernel

theorem geometry_13_92 : ∀ i ∈ List.range 4, GeometryAt 13 (92+i) := by decide +kernel

theorem geometry_13_96 : ∀ i ∈ List.range 4, GeometryAt 13 (96+i) := by decide +kernel

theorem geometry_13_100 : ∀ i ∈ List.range 4, GeometryAt 13 (100+i) := by decide +kernel

theorem geometry_13_104 : ∀ i ∈ List.range 4, GeometryAt 13 (104+i) := by decide +kernel

theorem geometry_13_108 : ∀ i ∈ List.range 4, GeometryAt 13 (108+i) := by decide +kernel

theorem geometry_13_112 : ∀ i ∈ List.range 4, GeometryAt 13 (112+i) := by decide +kernel

theorem geometry_13_116 : ∀ i ∈ List.range 4, GeometryAt 13 (116+i) := by decide +kernel

theorem geometry_13_120 : ∀ i ∈ List.range 4, GeometryAt 13 (120+i) := by decide +kernel

theorem geometry_13_124 : ∀ i ∈ List.range 4, GeometryAt 13 (124+i) := by decide +kernel

theorem geometry_13_128 : ∀ i ∈ List.range 4, GeometryAt 13 (128+i) := by decide +kernel

theorem geometry_13_132 : ∀ i ∈ List.range 2, GeometryAt 13 (132+i) := by decide +kernel

theorem geometry_13 (v : ℕ) (hv : v ∈ List.range 134) : GeometryAt 13 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 13 v)
  have h := (join 0 68 66 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_13_0 geometry_13_4) (join 8 4 4 geometry_13_8 geometry_13_12)) (join 16 8 8 (join 16 4 4 geometry_13_16 geometry_13_20) (join 24 4 4 geometry_13_24 geometry_13_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 geometry_13_32 geometry_13_36) (join 40 4 4 geometry_13_40 geometry_13_44)) (join 48 8 12 (join 48 4 4 geometry_13_48 geometry_13_52) (join 56 4 8 geometry_13_56 (join 60 4 4 geometry_13_60 geometry_13_64))))) (join 68 32 34 (join 68 16 16 (join 68 8 8 (join 68 4 4 geometry_13_68 geometry_13_72) (join 76 4 4 geometry_13_76 geometry_13_80)) (join 84 8 8 (join 84 4 4 geometry_13_84 geometry_13_88) (join 92 4 4 geometry_13_92 geometry_13_96))) (join 100 16 18 (join 100 8 8 (join 100 4 4 geometry_13_100 geometry_13_104) (join 108 4 4 geometry_13_108 geometry_13_112)) (join 116 8 10 (join 116 4 4 geometry_13_116 geometry_13_120) (join 124 4 6 geometry_13_124 (join 128 4 2 geometry_13_128 geometry_13_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_13_0 : ∀ i ∈ List.range 4, StrictAt 13 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (0+i)) 13 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_4 : ∀ i ∈ List.range 4, StrictAt 13 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (4+i)) 13 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_8 : ∀ i ∈ List.range 4, StrictAt 13 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (8+i)) 13 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_12 : ∀ i ∈ List.range 4, StrictAt 13 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (12+i)) 13 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_16 : ∀ i ∈ List.range 4, StrictAt 13 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (16+i)) 13 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_20 : ∀ i ∈ List.range 4, StrictAt 13 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (20+i)) 13 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_24 : ∀ i ∈ List.range 4, StrictAt 13 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (24+i)) 13 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_28 : ∀ i ∈ List.range 4, StrictAt 13 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (28+i)) 13 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_32 : ∀ i ∈ List.range 4, StrictAt 13 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (32+i)) 13 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_36 : ∀ i ∈ List.range 4, StrictAt 13 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (36+i)) 13 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_40 : ∀ i ∈ List.range 4, StrictAt 13 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (40+i)) 13 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_44 : ∀ i ∈ List.range 4, StrictAt 13 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (44+i)) 13 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_48 : ∀ i ∈ List.range 4, StrictAt 13 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (48+i)) 13 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_52 : ∀ i ∈ List.range 4, StrictAt 13 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (52+i)) 13 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_56 : ∀ i ∈ List.range 4, StrictAt 13 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (56+i)) 13 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_60 : ∀ i ∈ List.range 4, StrictAt 13 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (60+i)) 13 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_64 : ∀ i ∈ List.range 4, StrictAt 13 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (64+i)) 13 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_68 : ∀ i ∈ List.range 4, StrictAt 13 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (68+i)) 13 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_72 : ∀ i ∈ List.range 4, StrictAt 13 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (72+i)) 13 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_76 : ∀ i ∈ List.range 4, StrictAt 13 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (76+i)) 13 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_80 : ∀ i ∈ List.range 4, StrictAt 13 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (80+i)) 13 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_84 : ∀ i ∈ List.range 4, StrictAt 13 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (84+i)) 13 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_88 : ∀ i ∈ List.range 4, StrictAt 13 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (88+i)) 13 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_92 : ∀ i ∈ List.range 4, StrictAt 13 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (92+i)) 13 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_96 : ∀ i ∈ List.range 4, StrictAt 13 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (96+i)) 13 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_100 : ∀ i ∈ List.range 4, StrictAt 13 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (100+i)) 13 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_104 : ∀ i ∈ List.range 4, StrictAt 13 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (104+i)) 13 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_108 : ∀ i ∈ List.range 4, StrictAt 13 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (108+i)) 13 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_112 : ∀ i ∈ List.range 4, StrictAt 13 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (112+i)) 13 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_116 : ∀ i ∈ List.range 4, StrictAt 13 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (116+i)) 13 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_120 : ∀ i ∈ List.range 4, StrictAt 13 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (120+i)) 13 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_124 : ∀ i ∈ List.range 4, StrictAt 13 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (124+i)) 13 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_128 : ∀ i ∈ List.range 4, StrictAt 13 (128+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (128+i)) 13 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13_132 : ∀ i ∈ List.range 2, StrictAt 13 (132+i) := by
  have h : ∀ i ∈ List.range 2, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 13 (132+i)) 13 (132+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_13 (v : ℕ) (hv : v ∈ List.range 134) : StrictAt 13 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 13 v)
  have h := (join 0 68 66 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_13_0 strict_13_4) (join 8 4 4 strict_13_8 strict_13_12)) (join 16 8 8 (join 16 4 4 strict_13_16 strict_13_20) (join 24 4 4 strict_13_24 strict_13_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 strict_13_32 strict_13_36) (join 40 4 4 strict_13_40 strict_13_44)) (join 48 8 12 (join 48 4 4 strict_13_48 strict_13_52) (join 56 4 8 strict_13_56 (join 60 4 4 strict_13_60 strict_13_64))))) (join 68 32 34 (join 68 16 16 (join 68 8 8 (join 68 4 4 strict_13_68 strict_13_72) (join 76 4 4 strict_13_76 strict_13_80)) (join 84 8 8 (join 84 4 4 strict_13_84 strict_13_88) (join 92 4 4 strict_13_92 strict_13_96))) (join 100 16 18 (join 100 8 8 (join 100 4 4 strict_13_100 strict_13_104) (join 108 4 4 strict_13_108 strict_13_112)) (join 116 8 10 (join 116 4 4 strict_13_116 strict_13_120) (join 124 4 6 strict_13_124 (join 128 4 2 strict_13_128 strict_13_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_13_0 : ∀ i ∈ List.range 4, PhaseAt 13 (0+i) := by decide +kernel

theorem phase_13_4 : ∀ i ∈ List.range 4, PhaseAt 13 (4+i) := by decide +kernel

theorem phase_13_8 : ∀ i ∈ List.range 4, PhaseAt 13 (8+i) := by decide +kernel

theorem phase_13_12 : ∀ i ∈ List.range 4, PhaseAt 13 (12+i) := by decide +kernel

theorem phase_13_16 : ∀ i ∈ List.range 4, PhaseAt 13 (16+i) := by decide +kernel

theorem phase_13_20 : ∀ i ∈ List.range 4, PhaseAt 13 (20+i) := by decide +kernel

theorem phase_13_24 : ∀ i ∈ List.range 4, PhaseAt 13 (24+i) := by decide +kernel

theorem phase_13_28 : ∀ i ∈ List.range 4, PhaseAt 13 (28+i) := by decide +kernel

theorem phase_13_32 : ∀ i ∈ List.range 4, PhaseAt 13 (32+i) := by decide +kernel

theorem phase_13_36 : ∀ i ∈ List.range 4, PhaseAt 13 (36+i) := by decide +kernel

theorem phase_13_40 : ∀ i ∈ List.range 4, PhaseAt 13 (40+i) := by decide +kernel

theorem phase_13_44 : ∀ i ∈ List.range 4, PhaseAt 13 (44+i) := by decide +kernel

theorem phase_13_48 : ∀ i ∈ List.range 4, PhaseAt 13 (48+i) := by decide +kernel

theorem phase_13_52 : ∀ i ∈ List.range 4, PhaseAt 13 (52+i) := by decide +kernel

theorem phase_13_56 : ∀ i ∈ List.range 4, PhaseAt 13 (56+i) := by decide +kernel

theorem phase_13_60 : ∀ i ∈ List.range 4, PhaseAt 13 (60+i) := by decide +kernel

theorem phase_13_64 : ∀ i ∈ List.range 4, PhaseAt 13 (64+i) := by decide +kernel

theorem phase_13_68 : ∀ i ∈ List.range 4, PhaseAt 13 (68+i) := by decide +kernel

theorem phase_13_72 : ∀ i ∈ List.range 4, PhaseAt 13 (72+i) := by decide +kernel

theorem phase_13_76 : ∀ i ∈ List.range 4, PhaseAt 13 (76+i) := by decide +kernel

theorem phase_13_80 : ∀ i ∈ List.range 4, PhaseAt 13 (80+i) := by decide +kernel

theorem phase_13_84 : ∀ i ∈ List.range 4, PhaseAt 13 (84+i) := by decide +kernel

theorem phase_13_88 : ∀ i ∈ List.range 4, PhaseAt 13 (88+i) := by decide +kernel

theorem phase_13_92 : ∀ i ∈ List.range 4, PhaseAt 13 (92+i) := by decide +kernel

theorem phase_13_96 : ∀ i ∈ List.range 4, PhaseAt 13 (96+i) := by decide +kernel

theorem phase_13_100 : ∀ i ∈ List.range 4, PhaseAt 13 (100+i) := by decide +kernel

theorem phase_13_104 : ∀ i ∈ List.range 4, PhaseAt 13 (104+i) := by decide +kernel

theorem phase_13_108 : ∀ i ∈ List.range 4, PhaseAt 13 (108+i) := by decide +kernel

theorem phase_13_112 : ∀ i ∈ List.range 4, PhaseAt 13 (112+i) := by decide +kernel

theorem phase_13_116 : ∀ i ∈ List.range 4, PhaseAt 13 (116+i) := by decide +kernel

theorem phase_13_120 : ∀ i ∈ List.range 4, PhaseAt 13 (120+i) := by decide +kernel

theorem phase_13_124 : ∀ i ∈ List.range 4, PhaseAt 13 (124+i) := by decide +kernel

theorem phase_13_128 : ∀ i ∈ List.range 4, PhaseAt 13 (128+i) := by decide +kernel

theorem phase_13_132 : ∀ i ∈ List.range 2, PhaseAt 13 (132+i) := by decide +kernel

theorem phase_13 (v : ℕ) (hv : v ∈ List.range 134) : PhaseAt 13 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 13 v)
  have h := (join 0 68 66 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_13_0 phase_13_4) (join 8 4 4 phase_13_8 phase_13_12)) (join 16 8 8 (join 16 4 4 phase_13_16 phase_13_20) (join 24 4 4 phase_13_24 phase_13_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_13_32 phase_13_36) (join 40 4 4 phase_13_40 phase_13_44)) (join 48 8 12 (join 48 4 4 phase_13_48 phase_13_52) (join 56 4 8 phase_13_56 (join 60 4 4 phase_13_60 phase_13_64))))) (join 68 32 34 (join 68 16 16 (join 68 8 8 (join 68 4 4 phase_13_68 phase_13_72) (join 76 4 4 phase_13_76 phase_13_80)) (join 84 8 8 (join 84 4 4 phase_13_84 phase_13_88) (join 92 4 4 phase_13_92 phase_13_96))) (join 100 16 18 (join 100 8 8 (join 100 4 4 phase_13_100 phase_13_104) (join 108 4 4 phase_13_108 phase_13_112)) (join 116 8 10 (join 116 4 4 phase_13_116 phase_13_120) (join 124 4 6 phase_13_124 (join 128 4 2 phase_13_128 phase_13_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_13_0 : ∀ i ∈ List.range 1, ThresholdAt 13 (0+i) := by decide +kernel

theorem threshold_13_1 : ∀ i ∈ List.range 1, ThresholdAt 13 (1+i) := by decide +kernel

theorem threshold_13_2 : ∀ i ∈ List.range 1, ThresholdAt 13 (2+i) := by decide +kernel

theorem threshold_13_3 : ∀ i ∈ List.range 1, ThresholdAt 13 (3+i) := by decide +kernel

theorem threshold_13_4 : ∀ i ∈ List.range 1, ThresholdAt 13 (4+i) := by decide +kernel

theorem threshold_13_5 : ∀ i ∈ List.range 1, ThresholdAt 13 (5+i) := by decide +kernel

theorem threshold_13_6 : ∀ i ∈ List.range 1, ThresholdAt 13 (6+i) := by decide +kernel

theorem threshold_13_7 : ∀ i ∈ List.range 1, ThresholdAt 13 (7+i) := by decide +kernel

theorem threshold_13_8 : ∀ i ∈ List.range 1, ThresholdAt 13 (8+i) := by decide +kernel

theorem threshold_13_9 : ∀ i ∈ List.range 1, ThresholdAt 13 (9+i) := by decide +kernel

theorem threshold_13_10 : ∀ i ∈ List.range 1, ThresholdAt 13 (10+i) := by decide +kernel

theorem threshold_13_11 : ∀ i ∈ List.range 1, ThresholdAt 13 (11+i) := by decide +kernel

theorem threshold_13_12 : ∀ i ∈ List.range 1, ThresholdAt 13 (12+i) := by decide +kernel

theorem threshold_13_13 : ∀ i ∈ List.range 1, ThresholdAt 13 (13+i) := by decide +kernel

theorem threshold_13_14 : ∀ i ∈ List.range 1, ThresholdAt 13 (14+i) := by decide +kernel

theorem threshold_13_15 : ∀ i ∈ List.range 1, ThresholdAt 13 (15+i) := by decide +kernel

theorem threshold_13_16 : ∀ i ∈ List.range 1, ThresholdAt 13 (16+i) := by decide +kernel

theorem threshold_13_17 : ∀ i ∈ List.range 1, ThresholdAt 13 (17+i) := by decide +kernel

theorem threshold_13_18 : ∀ i ∈ List.range 1, ThresholdAt 13 (18+i) := by decide +kernel

theorem threshold_13_19 : ∀ i ∈ List.range 1, ThresholdAt 13 (19+i) := by decide +kernel

theorem threshold_13_20 : ∀ i ∈ List.range 1, ThresholdAt 13 (20+i) := by decide +kernel

theorem threshold_13_21 : ∀ i ∈ List.range 1, ThresholdAt 13 (21+i) := by decide +kernel

theorem threshold_13_22 : ∀ i ∈ List.range 1, ThresholdAt 13 (22+i) := by decide +kernel

theorem threshold_13_23 : ∀ i ∈ List.range 1, ThresholdAt 13 (23+i) := by decide +kernel

theorem threshold_13_24 : ∀ i ∈ List.range 1, ThresholdAt 13 (24+i) := by decide +kernel

theorem threshold_13_25 : ∀ i ∈ List.range 1, ThresholdAt 13 (25+i) := by decide +kernel

theorem threshold_13_26 : ∀ i ∈ List.range 1, ThresholdAt 13 (26+i) := by decide +kernel

theorem threshold_13_27 : ∀ i ∈ List.range 1, ThresholdAt 13 (27+i) := by decide +kernel

theorem threshold_13_28 : ∀ i ∈ List.range 1, ThresholdAt 13 (28+i) := by decide +kernel

theorem threshold_13_29 : ∀ i ∈ List.range 1, ThresholdAt 13 (29+i) := by decide +kernel

theorem threshold_13_30 : ∀ i ∈ List.range 1, ThresholdAt 13 (30+i) := by decide +kernel

theorem threshold_13_31 : ∀ i ∈ List.range 1, ThresholdAt 13 (31+i) := by decide +kernel

theorem threshold_13_32 : ∀ i ∈ List.range 1, ThresholdAt 13 (32+i) := by decide +kernel

theorem threshold_13_33 : ∀ i ∈ List.range 1, ThresholdAt 13 (33+i) := by decide +kernel

theorem threshold_13_34 : ∀ i ∈ List.range 1, ThresholdAt 13 (34+i) := by decide +kernel

theorem threshold_13_35 : ∀ i ∈ List.range 1, ThresholdAt 13 (35+i) := by decide +kernel

theorem threshold_13_36 : ∀ i ∈ List.range 1, ThresholdAt 13 (36+i) := by decide +kernel

theorem threshold_13_37 : ∀ i ∈ List.range 1, ThresholdAt 13 (37+i) := by decide +kernel

theorem threshold_13_38 : ∀ i ∈ List.range 1, ThresholdAt 13 (38+i) := by decide +kernel

theorem threshold_13_39 : ∀ i ∈ List.range 1, ThresholdAt 13 (39+i) := by decide +kernel

theorem threshold_13_40 : ∀ i ∈ List.range 1, ThresholdAt 13 (40+i) := by decide +kernel

theorem threshold_13_41 : ∀ i ∈ List.range 1, ThresholdAt 13 (41+i) := by decide +kernel

theorem threshold_13_42 : ∀ i ∈ List.range 1, ThresholdAt 13 (42+i) := by decide +kernel

theorem threshold_13_43 : ∀ i ∈ List.range 1, ThresholdAt 13 (43+i) := by decide +kernel

theorem threshold_13_44 : ∀ i ∈ List.range 1, ThresholdAt 13 (44+i) := by decide +kernel

theorem threshold_13_45 : ∀ i ∈ List.range 1, ThresholdAt 13 (45+i) := by decide +kernel

theorem threshold_13_46 : ∀ i ∈ List.range 1, ThresholdAt 13 (46+i) := by decide +kernel

theorem threshold_13_47 : ∀ i ∈ List.range 1, ThresholdAt 13 (47+i) := by decide +kernel

theorem threshold_13_48 : ∀ i ∈ List.range 1, ThresholdAt 13 (48+i) := by decide +kernel

theorem threshold_13_49 : ∀ i ∈ List.range 1, ThresholdAt 13 (49+i) := by decide +kernel

theorem threshold_13_50 : ∀ i ∈ List.range 1, ThresholdAt 13 (50+i) := by decide +kernel

theorem threshold_13_51 : ∀ i ∈ List.range 1, ThresholdAt 13 (51+i) := by decide +kernel

theorem threshold_13_52 : ∀ i ∈ List.range 1, ThresholdAt 13 (52+i) := by decide +kernel

theorem threshold_13_53 : ∀ i ∈ List.range 1, ThresholdAt 13 (53+i) := by decide +kernel

theorem threshold_13_54 : ∀ i ∈ List.range 1, ThresholdAt 13 (54+i) := by decide +kernel

theorem threshold_13_55 : ∀ i ∈ List.range 1, ThresholdAt 13 (55+i) := by decide +kernel

theorem threshold_13_56 : ∀ i ∈ List.range 1, ThresholdAt 13 (56+i) := by decide +kernel

theorem threshold_13_57 : ∀ i ∈ List.range 1, ThresholdAt 13 (57+i) := by decide +kernel

theorem threshold_13_58 : ∀ i ∈ List.range 1, ThresholdAt 13 (58+i) := by decide +kernel

theorem threshold_13_59 : ∀ i ∈ List.range 1, ThresholdAt 13 (59+i) := by decide +kernel

theorem threshold_13_60 : ∀ i ∈ List.range 1, ThresholdAt 13 (60+i) := by decide +kernel

theorem threshold_13_61 : ∀ i ∈ List.range 1, ThresholdAt 13 (61+i) := by decide +kernel

theorem threshold_13_62 : ∀ i ∈ List.range 1, ThresholdAt 13 (62+i) := by decide +kernel

theorem threshold_13_63 : ∀ i ∈ List.range 1, ThresholdAt 13 (63+i) := by decide +kernel

theorem threshold_13_64 : ∀ i ∈ List.range 1, ThresholdAt 13 (64+i) := by decide +kernel

theorem threshold_13_65 : ∀ i ∈ List.range 1, ThresholdAt 13 (65+i) := by decide +kernel

theorem threshold_13_66 : ∀ i ∈ List.range 1, ThresholdAt 13 (66+i) := by decide +kernel

theorem threshold_13_67 : ∀ i ∈ List.range 1, ThresholdAt 13 (67+i) := by decide +kernel

theorem threshold_13_68 : ∀ i ∈ List.range 1, ThresholdAt 13 (68+i) := by decide +kernel

theorem threshold_13_69 : ∀ i ∈ List.range 1, ThresholdAt 13 (69+i) := by decide +kernel

theorem threshold_13_70 : ∀ i ∈ List.range 1, ThresholdAt 13 (70+i) := by decide +kernel

theorem threshold_13_71 : ∀ i ∈ List.range 1, ThresholdAt 13 (71+i) := by decide +kernel

theorem threshold_13_72 : ∀ i ∈ List.range 1, ThresholdAt 13 (72+i) := by decide +kernel

theorem threshold_13_73 : ∀ i ∈ List.range 1, ThresholdAt 13 (73+i) := by decide +kernel

theorem threshold_13_74 : ∀ i ∈ List.range 1, ThresholdAt 13 (74+i) := by decide +kernel

theorem threshold_13_75 : ∀ i ∈ List.range 1, ThresholdAt 13 (75+i) := by decide +kernel

theorem threshold_13_76 : ∀ i ∈ List.range 1, ThresholdAt 13 (76+i) := by decide +kernel

theorem threshold_13_77 : ∀ i ∈ List.range 1, ThresholdAt 13 (77+i) := by decide +kernel

theorem threshold_13_78 : ∀ i ∈ List.range 1, ThresholdAt 13 (78+i) := by decide +kernel

theorem threshold_13_79 : ∀ i ∈ List.range 1, ThresholdAt 13 (79+i) := by decide +kernel

theorem threshold_13_80 : ∀ i ∈ List.range 1, ThresholdAt 13 (80+i) := by decide +kernel

theorem threshold_13_81 : ∀ i ∈ List.range 1, ThresholdAt 13 (81+i) := by decide +kernel

theorem threshold_13_82 : ∀ i ∈ List.range 1, ThresholdAt 13 (82+i) := by decide +kernel

theorem threshold_13_83 : ∀ i ∈ List.range 1, ThresholdAt 13 (83+i) := by decide +kernel

theorem threshold_13_84 : ∀ i ∈ List.range 1, ThresholdAt 13 (84+i) := by decide +kernel

theorem threshold_13_85 : ∀ i ∈ List.range 1, ThresholdAt 13 (85+i) := by decide +kernel

theorem threshold_13_86 : ∀ i ∈ List.range 1, ThresholdAt 13 (86+i) := by decide +kernel

theorem threshold_13_87 : ∀ i ∈ List.range 1, ThresholdAt 13 (87+i) := by decide +kernel

theorem threshold_13_88 : ∀ i ∈ List.range 1, ThresholdAt 13 (88+i) := by decide +kernel

theorem threshold_13_89 : ∀ i ∈ List.range 1, ThresholdAt 13 (89+i) := by decide +kernel

theorem threshold_13_90 : ∀ i ∈ List.range 1, ThresholdAt 13 (90+i) := by decide +kernel

theorem threshold_13_91 : ∀ i ∈ List.range 1, ThresholdAt 13 (91+i) := by decide +kernel

theorem threshold_13_92 : ∀ i ∈ List.range 1, ThresholdAt 13 (92+i) := by decide +kernel

theorem threshold_13_93 : ∀ i ∈ List.range 1, ThresholdAt 13 (93+i) := by decide +kernel

theorem threshold_13_94 : ∀ i ∈ List.range 1, ThresholdAt 13 (94+i) := by decide +kernel

theorem threshold_13_95 : ∀ i ∈ List.range 1, ThresholdAt 13 (95+i) := by decide +kernel

theorem threshold_13_96 : ∀ i ∈ List.range 1, ThresholdAt 13 (96+i) := by decide +kernel

theorem threshold_13_97 : ∀ i ∈ List.range 1, ThresholdAt 13 (97+i) := by decide +kernel

theorem threshold_13_98 : ∀ i ∈ List.range 1, ThresholdAt 13 (98+i) := by decide +kernel

theorem threshold_13_99 : ∀ i ∈ List.range 1, ThresholdAt 13 (99+i) := by decide +kernel

theorem threshold_13_100 : ∀ i ∈ List.range 1, ThresholdAt 13 (100+i) := by decide +kernel

theorem threshold_13_101 : ∀ i ∈ List.range 1, ThresholdAt 13 (101+i) := by decide +kernel

theorem threshold_13_102 : ∀ i ∈ List.range 1, ThresholdAt 13 (102+i) := by decide +kernel

theorem threshold_13_103 : ∀ i ∈ List.range 1, ThresholdAt 13 (103+i) := by decide +kernel

theorem threshold_13_104 : ∀ i ∈ List.range 1, ThresholdAt 13 (104+i) := by decide +kernel

theorem threshold_13_105 : ∀ i ∈ List.range 1, ThresholdAt 13 (105+i) := by decide +kernel

theorem threshold_13_106 : ∀ i ∈ List.range 1, ThresholdAt 13 (106+i) := by decide +kernel

theorem threshold_13_107 : ∀ i ∈ List.range 1, ThresholdAt 13 (107+i) := by decide +kernel

theorem threshold_13_108 : ∀ i ∈ List.range 1, ThresholdAt 13 (108+i) := by decide +kernel

theorem threshold_13_109 : ∀ i ∈ List.range 1, ThresholdAt 13 (109+i) := by decide +kernel

theorem threshold_13_110 : ∀ i ∈ List.range 1, ThresholdAt 13 (110+i) := by decide +kernel

theorem threshold_13_111 : ∀ i ∈ List.range 1, ThresholdAt 13 (111+i) := by decide +kernel

theorem threshold_13_112 : ∀ i ∈ List.range 1, ThresholdAt 13 (112+i) := by decide +kernel

theorem threshold_13_113 : ∀ i ∈ List.range 1, ThresholdAt 13 (113+i) := by decide +kernel

theorem threshold_13_114 : ∀ i ∈ List.range 1, ThresholdAt 13 (114+i) := by decide +kernel

theorem threshold_13_115 : ∀ i ∈ List.range 1, ThresholdAt 13 (115+i) := by decide +kernel

theorem threshold_13_116 : ∀ i ∈ List.range 1, ThresholdAt 13 (116+i) := by decide +kernel

theorem threshold_13_117 : ∀ i ∈ List.range 1, ThresholdAt 13 (117+i) := by decide +kernel

theorem threshold_13_118 : ∀ i ∈ List.range 1, ThresholdAt 13 (118+i) := by decide +kernel

theorem threshold_13_119 : ∀ i ∈ List.range 1, ThresholdAt 13 (119+i) := by decide +kernel

theorem threshold_13_120 : ∀ i ∈ List.range 1, ThresholdAt 13 (120+i) := by decide +kernel

theorem threshold_13_121 : ∀ i ∈ List.range 1, ThresholdAt 13 (121+i) := by decide +kernel

theorem threshold_13_122 : ∀ i ∈ List.range 1, ThresholdAt 13 (122+i) := by decide +kernel

theorem threshold_13_123 : ∀ i ∈ List.range 1, ThresholdAt 13 (123+i) := by decide +kernel

theorem threshold_13_124 : ∀ i ∈ List.range 1, ThresholdAt 13 (124+i) := by decide +kernel

theorem threshold_13_125 : ∀ i ∈ List.range 1, ThresholdAt 13 (125+i) := by decide +kernel

theorem threshold_13_126 : ∀ i ∈ List.range 1, ThresholdAt 13 (126+i) := by decide +kernel

theorem threshold_13_127 : ∀ i ∈ List.range 1, ThresholdAt 13 (127+i) := by decide +kernel

theorem threshold_13_128 : ∀ i ∈ List.range 1, ThresholdAt 13 (128+i) := by decide +kernel

theorem threshold_13_129 : ∀ i ∈ List.range 1, ThresholdAt 13 (129+i) := by decide +kernel

theorem threshold_13_130 : ∀ i ∈ List.range 1, ThresholdAt 13 (130+i) := by decide +kernel

theorem threshold_13_131 : ∀ i ∈ List.range 1, ThresholdAt 13 (131+i) := by decide +kernel

theorem threshold_13_132 : ∀ i ∈ List.range 1, ThresholdAt 13 (132+i) := by decide +kernel

theorem threshold_13_133 : ∀ i ∈ List.range 1, ThresholdAt 13 (133+i) := by decide +kernel

theorem threshold_13 (v : ℕ) (hv : v ∈ List.range 134) : ThresholdAt 13 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 13 v)
  have h := (join 0 67 67 (join 0 33 34 (join 0 16 17 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_13_0 threshold_13_1) (join 2 1 1 threshold_13_2 threshold_13_3)) (join 4 2 2 (join 4 1 1 threshold_13_4 threshold_13_5) (join 6 1 1 threshold_13_6 threshold_13_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_13_8 threshold_13_9) (join 10 1 1 threshold_13_10 threshold_13_11)) (join 12 2 2 (join 12 1 1 threshold_13_12 threshold_13_13) (join 14 1 1 threshold_13_14 threshold_13_15)))) (join 16 8 9 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_13_16 threshold_13_17) (join 18 1 1 threshold_13_18 threshold_13_19)) (join 20 2 2 (join 20 1 1 threshold_13_20 threshold_13_21) (join 22 1 1 threshold_13_22 threshold_13_23))) (join 24 4 5 (join 24 2 2 (join 24 1 1 threshold_13_24 threshold_13_25) (join 26 1 1 threshold_13_26 threshold_13_27)) (join 28 2 3 (join 28 1 1 threshold_13_28 threshold_13_29) (join 30 1 2 threshold_13_30 (join 31 1 1 threshold_13_31 threshold_13_32)))))) (join 33 17 17 (join 33 8 9 (join 33 4 4 (join 33 2 2 (join 33 1 1 threshold_13_33 threshold_13_34) (join 35 1 1 threshold_13_35 threshold_13_36)) (join 37 2 2 (join 37 1 1 threshold_13_37 threshold_13_38) (join 39 1 1 threshold_13_39 threshold_13_40))) (join 41 4 5 (join 41 2 2 (join 41 1 1 threshold_13_41 threshold_13_42) (join 43 1 1 threshold_13_43 threshold_13_44)) (join 45 2 3 (join 45 1 1 threshold_13_45 threshold_13_46) (join 47 1 2 threshold_13_47 (join 48 1 1 threshold_13_48 threshold_13_49))))) (join 50 8 9 (join 50 4 4 (join 50 2 2 (join 50 1 1 threshold_13_50 threshold_13_51) (join 52 1 1 threshold_13_52 threshold_13_53)) (join 54 2 2 (join 54 1 1 threshold_13_54 threshold_13_55) (join 56 1 1 threshold_13_56 threshold_13_57))) (join 58 4 5 (join 58 2 2 (join 58 1 1 threshold_13_58 threshold_13_59) (join 60 1 1 threshold_13_60 threshold_13_61)) (join 62 2 3 (join 62 1 1 threshold_13_62 threshold_13_63) (join 64 1 2 threshold_13_64 (join 65 1 1 threshold_13_65 threshold_13_66))))))) (join 67 33 34 (join 67 16 17 (join 67 8 8 (join 67 4 4 (join 67 2 2 (join 67 1 1 threshold_13_67 threshold_13_68) (join 69 1 1 threshold_13_69 threshold_13_70)) (join 71 2 2 (join 71 1 1 threshold_13_71 threshold_13_72) (join 73 1 1 threshold_13_73 threshold_13_74))) (join 75 4 4 (join 75 2 2 (join 75 1 1 threshold_13_75 threshold_13_76) (join 77 1 1 threshold_13_77 threshold_13_78)) (join 79 2 2 (join 79 1 1 threshold_13_79 threshold_13_80) (join 81 1 1 threshold_13_81 threshold_13_82)))) (join 83 8 9 (join 83 4 4 (join 83 2 2 (join 83 1 1 threshold_13_83 threshold_13_84) (join 85 1 1 threshold_13_85 threshold_13_86)) (join 87 2 2 (join 87 1 1 threshold_13_87 threshold_13_88) (join 89 1 1 threshold_13_89 threshold_13_90))) (join 91 4 5 (join 91 2 2 (join 91 1 1 threshold_13_91 threshold_13_92) (join 93 1 1 threshold_13_93 threshold_13_94)) (join 95 2 3 (join 95 1 1 threshold_13_95 threshold_13_96) (join 97 1 2 threshold_13_97 (join 98 1 1 threshold_13_98 threshold_13_99)))))) (join 100 17 17 (join 100 8 9 (join 100 4 4 (join 100 2 2 (join 100 1 1 threshold_13_100 threshold_13_101) (join 102 1 1 threshold_13_102 threshold_13_103)) (join 104 2 2 (join 104 1 1 threshold_13_104 threshold_13_105) (join 106 1 1 threshold_13_106 threshold_13_107))) (join 108 4 5 (join 108 2 2 (join 108 1 1 threshold_13_108 threshold_13_109) (join 110 1 1 threshold_13_110 threshold_13_111)) (join 112 2 3 (join 112 1 1 threshold_13_112 threshold_13_113) (join 114 1 2 threshold_13_114 (join 115 1 1 threshold_13_115 threshold_13_116))))) (join 117 8 9 (join 117 4 4 (join 117 2 2 (join 117 1 1 threshold_13_117 threshold_13_118) (join 119 1 1 threshold_13_119 threshold_13_120)) (join 121 2 2 (join 121 1 1 threshold_13_121 threshold_13_122) (join 123 1 1 threshold_13_123 threshold_13_124))) (join 125 4 5 (join 125 2 2 (join 125 1 1 threshold_13_125 threshold_13_126) (join 127 1 1 threshold_13_127 threshold_13_128)) (join 129 2 3 (join 129 1 1 threshold_13_129 threshold_13_130) (join 131 1 2 threshold_13_131 (join 132 1 1 threshold_13_132 threshold_13_133))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_13_0 : ∀ i ∈ List.range 4, LedgerAt 13 (0+i) := by decide +kernel

theorem ledger_13_4 : ∀ i ∈ List.range 4, LedgerAt 13 (4+i) := by decide +kernel

theorem ledger_13_8 : ∀ i ∈ List.range 4, LedgerAt 13 (8+i) := by decide +kernel

theorem ledger_13_12 : ∀ i ∈ List.range 4, LedgerAt 13 (12+i) := by decide +kernel

theorem ledger_13_16 : ∀ i ∈ List.range 4, LedgerAt 13 (16+i) := by decide +kernel

theorem ledger_13_20 : ∀ i ∈ List.range 4, LedgerAt 13 (20+i) := by decide +kernel

theorem ledger_13_24 : ∀ i ∈ List.range 4, LedgerAt 13 (24+i) := by decide +kernel

theorem ledger_13_28 : ∀ i ∈ List.range 4, LedgerAt 13 (28+i) := by decide +kernel

theorem ledger_13_32 : ∀ i ∈ List.range 4, LedgerAt 13 (32+i) := by decide +kernel

theorem ledger_13_36 : ∀ i ∈ List.range 4, LedgerAt 13 (36+i) := by decide +kernel

theorem ledger_13_40 : ∀ i ∈ List.range 4, LedgerAt 13 (40+i) := by decide +kernel

theorem ledger_13_44 : ∀ i ∈ List.range 4, LedgerAt 13 (44+i) := by decide +kernel

theorem ledger_13_48 : ∀ i ∈ List.range 4, LedgerAt 13 (48+i) := by decide +kernel

theorem ledger_13_52 : ∀ i ∈ List.range 4, LedgerAt 13 (52+i) := by decide +kernel

theorem ledger_13_56 : ∀ i ∈ List.range 4, LedgerAt 13 (56+i) := by decide +kernel

theorem ledger_13_60 : ∀ i ∈ List.range 4, LedgerAt 13 (60+i) := by decide +kernel

theorem ledger_13_64 : ∀ i ∈ List.range 4, LedgerAt 13 (64+i) := by decide +kernel

theorem ledger_13_68 : ∀ i ∈ List.range 4, LedgerAt 13 (68+i) := by decide +kernel

theorem ledger_13_72 : ∀ i ∈ List.range 4, LedgerAt 13 (72+i) := by decide +kernel

theorem ledger_13_76 : ∀ i ∈ List.range 4, LedgerAt 13 (76+i) := by decide +kernel

theorem ledger_13_80 : ∀ i ∈ List.range 4, LedgerAt 13 (80+i) := by decide +kernel

theorem ledger_13_84 : ∀ i ∈ List.range 4, LedgerAt 13 (84+i) := by decide +kernel

theorem ledger_13_88 : ∀ i ∈ List.range 4, LedgerAt 13 (88+i) := by decide +kernel

theorem ledger_13_92 : ∀ i ∈ List.range 4, LedgerAt 13 (92+i) := by decide +kernel

theorem ledger_13_96 : ∀ i ∈ List.range 4, LedgerAt 13 (96+i) := by decide +kernel

theorem ledger_13_100 : ∀ i ∈ List.range 4, LedgerAt 13 (100+i) := by decide +kernel

theorem ledger_13_104 : ∀ i ∈ List.range 4, LedgerAt 13 (104+i) := by decide +kernel

theorem ledger_13_108 : ∀ i ∈ List.range 4, LedgerAt 13 (108+i) := by decide +kernel

theorem ledger_13_112 : ∀ i ∈ List.range 4, LedgerAt 13 (112+i) := by decide +kernel

theorem ledger_13_116 : ∀ i ∈ List.range 4, LedgerAt 13 (116+i) := by decide +kernel

theorem ledger_13_120 : ∀ i ∈ List.range 4, LedgerAt 13 (120+i) := by decide +kernel

theorem ledger_13_124 : ∀ i ∈ List.range 4, LedgerAt 13 (124+i) := by decide +kernel

theorem ledger_13_128 : ∀ i ∈ List.range 4, LedgerAt 13 (128+i) := by decide +kernel

theorem ledger_13_132 : ∀ i ∈ List.range 2, LedgerAt 13 (132+i) := by decide +kernel

theorem ledger_13 (v : ℕ) (hv : v ∈ List.range 134) : LedgerAt 13 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 13 v)
  have h := (join 0 68 66 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_13_0 ledger_13_4) (join 8 4 4 ledger_13_8 ledger_13_12)) (join 16 8 8 (join 16 4 4 ledger_13_16 ledger_13_20) (join 24 4 4 ledger_13_24 ledger_13_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_13_32 ledger_13_36) (join 40 4 4 ledger_13_40 ledger_13_44)) (join 48 8 12 (join 48 4 4 ledger_13_48 ledger_13_52) (join 56 4 8 ledger_13_56 (join 60 4 4 ledger_13_60 ledger_13_64))))) (join 68 32 34 (join 68 16 16 (join 68 8 8 (join 68 4 4 ledger_13_68 ledger_13_72) (join 76 4 4 ledger_13_76 ledger_13_80)) (join 84 8 8 (join 84 4 4 ledger_13_84 ledger_13_88) (join 92 4 4 ledger_13_92 ledger_13_96))) (join 100 16 18 (join 100 8 8 (join 100 4 4 ledger_13_100 ledger_13_104) (join 108 4 4 ledger_13_108 ledger_13_112)) (join 116 8 10 (join 116 4 4 ledger_13_116 ledger_13_120) (join 124 4 6 ledger_13_124 (join 128 4 2 ledger_13_128 ledger_13_132))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
