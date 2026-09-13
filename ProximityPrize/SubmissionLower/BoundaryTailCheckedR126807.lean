import ProximityPrize.SubmissionLower.BoundaryTailCheckedR116807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_12_0 : ∀ i ∈ List.range 4, GeometryAt 12 (0+i) := by decide +kernel

theorem geometry_12_4 : ∀ i ∈ List.range 4, GeometryAt 12 (4+i) := by decide +kernel

theorem geometry_12_8 : ∀ i ∈ List.range 4, GeometryAt 12 (8+i) := by decide +kernel

theorem geometry_12_12 : ∀ i ∈ List.range 4, GeometryAt 12 (12+i) := by decide +kernel

theorem geometry_12_16 : ∀ i ∈ List.range 4, GeometryAt 12 (16+i) := by decide +kernel

theorem geometry_12_20 : ∀ i ∈ List.range 4, GeometryAt 12 (20+i) := by decide +kernel

theorem geometry_12_24 : ∀ i ∈ List.range 4, GeometryAt 12 (24+i) := by decide +kernel

theorem geometry_12_28 : ∀ i ∈ List.range 4, GeometryAt 12 (28+i) := by decide +kernel

theorem geometry_12_32 : ∀ i ∈ List.range 4, GeometryAt 12 (32+i) := by decide +kernel

theorem geometry_12_36 : ∀ i ∈ List.range 4, GeometryAt 12 (36+i) := by decide +kernel

theorem geometry_12_40 : ∀ i ∈ List.range 4, GeometryAt 12 (40+i) := by decide +kernel

theorem geometry_12_44 : ∀ i ∈ List.range 4, GeometryAt 12 (44+i) := by decide +kernel

theorem geometry_12_48 : ∀ i ∈ List.range 4, GeometryAt 12 (48+i) := by decide +kernel

theorem geometry_12_52 : ∀ i ∈ List.range 4, GeometryAt 12 (52+i) := by decide +kernel

theorem geometry_12_56 : ∀ i ∈ List.range 4, GeometryAt 12 (56+i) := by decide +kernel

theorem geometry_12_60 : ∀ i ∈ List.range 4, GeometryAt 12 (60+i) := by decide +kernel

theorem geometry_12_64 : ∀ i ∈ List.range 4, GeometryAt 12 (64+i) := by decide +kernel

theorem geometry_12_68 : ∀ i ∈ List.range 4, GeometryAt 12 (68+i) := by decide +kernel

theorem geometry_12_72 : ∀ i ∈ List.range 4, GeometryAt 12 (72+i) := by decide +kernel

theorem geometry_12_76 : ∀ i ∈ List.range 4, GeometryAt 12 (76+i) := by decide +kernel

theorem geometry_12_80 : ∀ i ∈ List.range 4, GeometryAt 12 (80+i) := by decide +kernel

theorem geometry_12_84 : ∀ i ∈ List.range 4, GeometryAt 12 (84+i) := by decide +kernel

theorem geometry_12_88 : ∀ i ∈ List.range 4, GeometryAt 12 (88+i) := by decide +kernel

theorem geometry_12_92 : ∀ i ∈ List.range 4, GeometryAt 12 (92+i) := by decide +kernel

theorem geometry_12_96 : ∀ i ∈ List.range 4, GeometryAt 12 (96+i) := by decide +kernel

theorem geometry_12_100 : ∀ i ∈ List.range 4, GeometryAt 12 (100+i) := by decide +kernel

theorem geometry_12_104 : ∀ i ∈ List.range 4, GeometryAt 12 (104+i) := by decide +kernel

theorem geometry_12_108 : ∀ i ∈ List.range 4, GeometryAt 12 (108+i) := by decide +kernel

theorem geometry_12_112 : ∀ i ∈ List.range 4, GeometryAt 12 (112+i) := by decide +kernel

theorem geometry_12_116 : ∀ i ∈ List.range 4, GeometryAt 12 (116+i) := by decide +kernel

theorem geometry_12_120 : ∀ i ∈ List.range 4, GeometryAt 12 (120+i) := by decide +kernel

theorem geometry_12_124 : ∀ i ∈ List.range 4, GeometryAt 12 (124+i) := by decide +kernel

theorem geometry_12_128 : ∀ i ∈ List.range 4, GeometryAt 12 (128+i) := by decide +kernel

theorem geometry_12_132 : ∀ i ∈ List.range 3, GeometryAt 12 (132+i) := by decide +kernel

theorem geometry_12 (v : ℕ) (hv : v ∈ List.range 135) : GeometryAt 12 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 12 v)
  have h := (join 0 68 67 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_12_0 geometry_12_4) (join 8 4 4 geometry_12_8 geometry_12_12)) (join 16 8 8 (join 16 4 4 geometry_12_16 geometry_12_20) (join 24 4 4 geometry_12_24 geometry_12_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 geometry_12_32 geometry_12_36) (join 40 4 4 geometry_12_40 geometry_12_44)) (join 48 8 12 (join 48 4 4 geometry_12_48 geometry_12_52) (join 56 4 8 geometry_12_56 (join 60 4 4 geometry_12_60 geometry_12_64))))) (join 68 32 35 (join 68 16 16 (join 68 8 8 (join 68 4 4 geometry_12_68 geometry_12_72) (join 76 4 4 geometry_12_76 geometry_12_80)) (join 84 8 8 (join 84 4 4 geometry_12_84 geometry_12_88) (join 92 4 4 geometry_12_92 geometry_12_96))) (join 100 16 19 (join 100 8 8 (join 100 4 4 geometry_12_100 geometry_12_104) (join 108 4 4 geometry_12_108 geometry_12_112)) (join 116 8 11 (join 116 4 4 geometry_12_116 geometry_12_120) (join 124 4 7 geometry_12_124 (join 128 4 3 geometry_12_128 geometry_12_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_12_0 : ∀ i ∈ List.range 4, StrictAt 12 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (0+i)) 12 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_4 : ∀ i ∈ List.range 4, StrictAt 12 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (4+i)) 12 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_8 : ∀ i ∈ List.range 4, StrictAt 12 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (8+i)) 12 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_12 : ∀ i ∈ List.range 4, StrictAt 12 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (12+i)) 12 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_16 : ∀ i ∈ List.range 4, StrictAt 12 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (16+i)) 12 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_20 : ∀ i ∈ List.range 4, StrictAt 12 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (20+i)) 12 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_24 : ∀ i ∈ List.range 4, StrictAt 12 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (24+i)) 12 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_28 : ∀ i ∈ List.range 4, StrictAt 12 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (28+i)) 12 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_32 : ∀ i ∈ List.range 4, StrictAt 12 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (32+i)) 12 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_36 : ∀ i ∈ List.range 4, StrictAt 12 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (36+i)) 12 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_40 : ∀ i ∈ List.range 4, StrictAt 12 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (40+i)) 12 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_44 : ∀ i ∈ List.range 4, StrictAt 12 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (44+i)) 12 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_48 : ∀ i ∈ List.range 4, StrictAt 12 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (48+i)) 12 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_52 : ∀ i ∈ List.range 4, StrictAt 12 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (52+i)) 12 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_56 : ∀ i ∈ List.range 4, StrictAt 12 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (56+i)) 12 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_60 : ∀ i ∈ List.range 4, StrictAt 12 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (60+i)) 12 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_64 : ∀ i ∈ List.range 4, StrictAt 12 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (64+i)) 12 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_68 : ∀ i ∈ List.range 4, StrictAt 12 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (68+i)) 12 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_72 : ∀ i ∈ List.range 4, StrictAt 12 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (72+i)) 12 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_76 : ∀ i ∈ List.range 4, StrictAt 12 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (76+i)) 12 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_80 : ∀ i ∈ List.range 4, StrictAt 12 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (80+i)) 12 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_84 : ∀ i ∈ List.range 4, StrictAt 12 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (84+i)) 12 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_88 : ∀ i ∈ List.range 4, StrictAt 12 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (88+i)) 12 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_92 : ∀ i ∈ List.range 4, StrictAt 12 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (92+i)) 12 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_96 : ∀ i ∈ List.range 4, StrictAt 12 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (96+i)) 12 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_100 : ∀ i ∈ List.range 4, StrictAt 12 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (100+i)) 12 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_104 : ∀ i ∈ List.range 4, StrictAt 12 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (104+i)) 12 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_108 : ∀ i ∈ List.range 4, StrictAt 12 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (108+i)) 12 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_112 : ∀ i ∈ List.range 4, StrictAt 12 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (112+i)) 12 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_116 : ∀ i ∈ List.range 4, StrictAt 12 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (116+i)) 12 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_120 : ∀ i ∈ List.range 4, StrictAt 12 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (120+i)) 12 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_124 : ∀ i ∈ List.range 4, StrictAt 12 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (124+i)) 12 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_128 : ∀ i ∈ List.range 4, StrictAt 12 (128+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (128+i)) 12 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12_132 : ∀ i ∈ List.range 3, StrictAt 12 (132+i) := by
  have h : ∀ i ∈ List.range 3, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 12 (132+i)) 12 (132+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_12 (v : ℕ) (hv : v ∈ List.range 135) : StrictAt 12 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 12 v)
  have h := (join 0 68 67 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_12_0 strict_12_4) (join 8 4 4 strict_12_8 strict_12_12)) (join 16 8 8 (join 16 4 4 strict_12_16 strict_12_20) (join 24 4 4 strict_12_24 strict_12_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 strict_12_32 strict_12_36) (join 40 4 4 strict_12_40 strict_12_44)) (join 48 8 12 (join 48 4 4 strict_12_48 strict_12_52) (join 56 4 8 strict_12_56 (join 60 4 4 strict_12_60 strict_12_64))))) (join 68 32 35 (join 68 16 16 (join 68 8 8 (join 68 4 4 strict_12_68 strict_12_72) (join 76 4 4 strict_12_76 strict_12_80)) (join 84 8 8 (join 84 4 4 strict_12_84 strict_12_88) (join 92 4 4 strict_12_92 strict_12_96))) (join 100 16 19 (join 100 8 8 (join 100 4 4 strict_12_100 strict_12_104) (join 108 4 4 strict_12_108 strict_12_112)) (join 116 8 11 (join 116 4 4 strict_12_116 strict_12_120) (join 124 4 7 strict_12_124 (join 128 4 3 strict_12_128 strict_12_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_12_0 : ∀ i ∈ List.range 4, PhaseAt 12 (0+i) := by decide +kernel

theorem phase_12_4 : ∀ i ∈ List.range 4, PhaseAt 12 (4+i) := by decide +kernel

theorem phase_12_8 : ∀ i ∈ List.range 4, PhaseAt 12 (8+i) := by decide +kernel

theorem phase_12_12 : ∀ i ∈ List.range 4, PhaseAt 12 (12+i) := by decide +kernel

theorem phase_12_16 : ∀ i ∈ List.range 4, PhaseAt 12 (16+i) := by decide +kernel

theorem phase_12_20 : ∀ i ∈ List.range 4, PhaseAt 12 (20+i) := by decide +kernel

theorem phase_12_24 : ∀ i ∈ List.range 4, PhaseAt 12 (24+i) := by decide +kernel

theorem phase_12_28 : ∀ i ∈ List.range 4, PhaseAt 12 (28+i) := by decide +kernel

theorem phase_12_32 : ∀ i ∈ List.range 4, PhaseAt 12 (32+i) := by decide +kernel

theorem phase_12_36 : ∀ i ∈ List.range 4, PhaseAt 12 (36+i) := by decide +kernel

theorem phase_12_40 : ∀ i ∈ List.range 4, PhaseAt 12 (40+i) := by decide +kernel

theorem phase_12_44 : ∀ i ∈ List.range 4, PhaseAt 12 (44+i) := by decide +kernel

theorem phase_12_48 : ∀ i ∈ List.range 4, PhaseAt 12 (48+i) := by decide +kernel

theorem phase_12_52 : ∀ i ∈ List.range 4, PhaseAt 12 (52+i) := by decide +kernel

theorem phase_12_56 : ∀ i ∈ List.range 4, PhaseAt 12 (56+i) := by decide +kernel

theorem phase_12_60 : ∀ i ∈ List.range 4, PhaseAt 12 (60+i) := by decide +kernel

theorem phase_12_64 : ∀ i ∈ List.range 4, PhaseAt 12 (64+i) := by decide +kernel

theorem phase_12_68 : ∀ i ∈ List.range 4, PhaseAt 12 (68+i) := by decide +kernel

theorem phase_12_72 : ∀ i ∈ List.range 4, PhaseAt 12 (72+i) := by decide +kernel

theorem phase_12_76 : ∀ i ∈ List.range 4, PhaseAt 12 (76+i) := by decide +kernel

theorem phase_12_80 : ∀ i ∈ List.range 4, PhaseAt 12 (80+i) := by decide +kernel

theorem phase_12_84 : ∀ i ∈ List.range 4, PhaseAt 12 (84+i) := by decide +kernel

theorem phase_12_88 : ∀ i ∈ List.range 4, PhaseAt 12 (88+i) := by decide +kernel

theorem phase_12_92 : ∀ i ∈ List.range 4, PhaseAt 12 (92+i) := by decide +kernel

theorem phase_12_96 : ∀ i ∈ List.range 4, PhaseAt 12 (96+i) := by decide +kernel

theorem phase_12_100 : ∀ i ∈ List.range 4, PhaseAt 12 (100+i) := by decide +kernel

theorem phase_12_104 : ∀ i ∈ List.range 4, PhaseAt 12 (104+i) := by decide +kernel

theorem phase_12_108 : ∀ i ∈ List.range 4, PhaseAt 12 (108+i) := by decide +kernel

theorem phase_12_112 : ∀ i ∈ List.range 4, PhaseAt 12 (112+i) := by decide +kernel

theorem phase_12_116 : ∀ i ∈ List.range 4, PhaseAt 12 (116+i) := by decide +kernel

theorem phase_12_120 : ∀ i ∈ List.range 4, PhaseAt 12 (120+i) := by decide +kernel

theorem phase_12_124 : ∀ i ∈ List.range 4, PhaseAt 12 (124+i) := by decide +kernel

theorem phase_12_128 : ∀ i ∈ List.range 4, PhaseAt 12 (128+i) := by decide +kernel

theorem phase_12_132 : ∀ i ∈ List.range 3, PhaseAt 12 (132+i) := by decide +kernel

theorem phase_12 (v : ℕ) (hv : v ∈ List.range 135) : PhaseAt 12 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 12 v)
  have h := (join 0 68 67 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_12_0 phase_12_4) (join 8 4 4 phase_12_8 phase_12_12)) (join 16 8 8 (join 16 4 4 phase_12_16 phase_12_20) (join 24 4 4 phase_12_24 phase_12_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_12_32 phase_12_36) (join 40 4 4 phase_12_40 phase_12_44)) (join 48 8 12 (join 48 4 4 phase_12_48 phase_12_52) (join 56 4 8 phase_12_56 (join 60 4 4 phase_12_60 phase_12_64))))) (join 68 32 35 (join 68 16 16 (join 68 8 8 (join 68 4 4 phase_12_68 phase_12_72) (join 76 4 4 phase_12_76 phase_12_80)) (join 84 8 8 (join 84 4 4 phase_12_84 phase_12_88) (join 92 4 4 phase_12_92 phase_12_96))) (join 100 16 19 (join 100 8 8 (join 100 4 4 phase_12_100 phase_12_104) (join 108 4 4 phase_12_108 phase_12_112)) (join 116 8 11 (join 116 4 4 phase_12_116 phase_12_120) (join 124 4 7 phase_12_124 (join 128 4 3 phase_12_128 phase_12_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_12_0 : ∀ i ∈ List.range 1, ThresholdAt 12 (0+i) := by decide +kernel

theorem threshold_12_1 : ∀ i ∈ List.range 1, ThresholdAt 12 (1+i) := by decide +kernel

theorem threshold_12_2 : ∀ i ∈ List.range 1, ThresholdAt 12 (2+i) := by decide +kernel

theorem threshold_12_3 : ∀ i ∈ List.range 1, ThresholdAt 12 (3+i) := by decide +kernel

theorem threshold_12_4 : ∀ i ∈ List.range 1, ThresholdAt 12 (4+i) := by decide +kernel

theorem threshold_12_5 : ∀ i ∈ List.range 1, ThresholdAt 12 (5+i) := by decide +kernel

theorem threshold_12_6 : ∀ i ∈ List.range 1, ThresholdAt 12 (6+i) := by decide +kernel

theorem threshold_12_7 : ∀ i ∈ List.range 1, ThresholdAt 12 (7+i) := by decide +kernel

theorem threshold_12_8 : ∀ i ∈ List.range 1, ThresholdAt 12 (8+i) := by decide +kernel

theorem threshold_12_9 : ∀ i ∈ List.range 1, ThresholdAt 12 (9+i) := by decide +kernel

theorem threshold_12_10 : ∀ i ∈ List.range 1, ThresholdAt 12 (10+i) := by decide +kernel

theorem threshold_12_11 : ∀ i ∈ List.range 1, ThresholdAt 12 (11+i) := by decide +kernel

theorem threshold_12_12 : ∀ i ∈ List.range 1, ThresholdAt 12 (12+i) := by decide +kernel

theorem threshold_12_13 : ∀ i ∈ List.range 1, ThresholdAt 12 (13+i) := by decide +kernel

theorem threshold_12_14 : ∀ i ∈ List.range 1, ThresholdAt 12 (14+i) := by decide +kernel

theorem threshold_12_15 : ∀ i ∈ List.range 1, ThresholdAt 12 (15+i) := by decide +kernel

theorem threshold_12_16 : ∀ i ∈ List.range 1, ThresholdAt 12 (16+i) := by decide +kernel

theorem threshold_12_17 : ∀ i ∈ List.range 1, ThresholdAt 12 (17+i) := by decide +kernel

theorem threshold_12_18 : ∀ i ∈ List.range 1, ThresholdAt 12 (18+i) := by decide +kernel

theorem threshold_12_19 : ∀ i ∈ List.range 1, ThresholdAt 12 (19+i) := by decide +kernel

theorem threshold_12_20 : ∀ i ∈ List.range 1, ThresholdAt 12 (20+i) := by decide +kernel

theorem threshold_12_21 : ∀ i ∈ List.range 1, ThresholdAt 12 (21+i) := by decide +kernel

theorem threshold_12_22 : ∀ i ∈ List.range 1, ThresholdAt 12 (22+i) := by decide +kernel

theorem threshold_12_23 : ∀ i ∈ List.range 1, ThresholdAt 12 (23+i) := by decide +kernel

theorem threshold_12_24 : ∀ i ∈ List.range 1, ThresholdAt 12 (24+i) := by decide +kernel

theorem threshold_12_25 : ∀ i ∈ List.range 1, ThresholdAt 12 (25+i) := by decide +kernel

theorem threshold_12_26 : ∀ i ∈ List.range 1, ThresholdAt 12 (26+i) := by decide +kernel

theorem threshold_12_27 : ∀ i ∈ List.range 1, ThresholdAt 12 (27+i) := by decide +kernel

theorem threshold_12_28 : ∀ i ∈ List.range 1, ThresholdAt 12 (28+i) := by decide +kernel

theorem threshold_12_29 : ∀ i ∈ List.range 1, ThresholdAt 12 (29+i) := by decide +kernel

theorem threshold_12_30 : ∀ i ∈ List.range 1, ThresholdAt 12 (30+i) := by decide +kernel

theorem threshold_12_31 : ∀ i ∈ List.range 1, ThresholdAt 12 (31+i) := by decide +kernel

theorem threshold_12_32 : ∀ i ∈ List.range 1, ThresholdAt 12 (32+i) := by decide +kernel

theorem threshold_12_33 : ∀ i ∈ List.range 1, ThresholdAt 12 (33+i) := by decide +kernel

theorem threshold_12_34 : ∀ i ∈ List.range 1, ThresholdAt 12 (34+i) := by decide +kernel

theorem threshold_12_35 : ∀ i ∈ List.range 1, ThresholdAt 12 (35+i) := by decide +kernel

theorem threshold_12_36 : ∀ i ∈ List.range 1, ThresholdAt 12 (36+i) := by decide +kernel

theorem threshold_12_37 : ∀ i ∈ List.range 1, ThresholdAt 12 (37+i) := by decide +kernel

theorem threshold_12_38 : ∀ i ∈ List.range 1, ThresholdAt 12 (38+i) := by decide +kernel

theorem threshold_12_39 : ∀ i ∈ List.range 1, ThresholdAt 12 (39+i) := by decide +kernel

theorem threshold_12_40 : ∀ i ∈ List.range 1, ThresholdAt 12 (40+i) := by decide +kernel

theorem threshold_12_41 : ∀ i ∈ List.range 1, ThresholdAt 12 (41+i) := by decide +kernel

theorem threshold_12_42 : ∀ i ∈ List.range 1, ThresholdAt 12 (42+i) := by decide +kernel

theorem threshold_12_43 : ∀ i ∈ List.range 1, ThresholdAt 12 (43+i) := by decide +kernel

theorem threshold_12_44 : ∀ i ∈ List.range 1, ThresholdAt 12 (44+i) := by decide +kernel

theorem threshold_12_45 : ∀ i ∈ List.range 1, ThresholdAt 12 (45+i) := by decide +kernel

theorem threshold_12_46 : ∀ i ∈ List.range 1, ThresholdAt 12 (46+i) := by decide +kernel

theorem threshold_12_47 : ∀ i ∈ List.range 1, ThresholdAt 12 (47+i) := by decide +kernel

theorem threshold_12_48 : ∀ i ∈ List.range 1, ThresholdAt 12 (48+i) := by decide +kernel

theorem threshold_12_49 : ∀ i ∈ List.range 1, ThresholdAt 12 (49+i) := by decide +kernel

theorem threshold_12_50 : ∀ i ∈ List.range 1, ThresholdAt 12 (50+i) := by decide +kernel

theorem threshold_12_51 : ∀ i ∈ List.range 1, ThresholdAt 12 (51+i) := by decide +kernel

theorem threshold_12_52 : ∀ i ∈ List.range 1, ThresholdAt 12 (52+i) := by decide +kernel

theorem threshold_12_53 : ∀ i ∈ List.range 1, ThresholdAt 12 (53+i) := by decide +kernel

theorem threshold_12_54 : ∀ i ∈ List.range 1, ThresholdAt 12 (54+i) := by decide +kernel

theorem threshold_12_55 : ∀ i ∈ List.range 1, ThresholdAt 12 (55+i) := by decide +kernel

theorem threshold_12_56 : ∀ i ∈ List.range 1, ThresholdAt 12 (56+i) := by decide +kernel

theorem threshold_12_57 : ∀ i ∈ List.range 1, ThresholdAt 12 (57+i) := by decide +kernel

theorem threshold_12_58 : ∀ i ∈ List.range 1, ThresholdAt 12 (58+i) := by decide +kernel

theorem threshold_12_59 : ∀ i ∈ List.range 1, ThresholdAt 12 (59+i) := by decide +kernel

theorem threshold_12_60 : ∀ i ∈ List.range 1, ThresholdAt 12 (60+i) := by decide +kernel

theorem threshold_12_61 : ∀ i ∈ List.range 1, ThresholdAt 12 (61+i) := by decide +kernel

theorem threshold_12_62 : ∀ i ∈ List.range 1, ThresholdAt 12 (62+i) := by decide +kernel

theorem threshold_12_63 : ∀ i ∈ List.range 1, ThresholdAt 12 (63+i) := by decide +kernel

theorem threshold_12_64 : ∀ i ∈ List.range 1, ThresholdAt 12 (64+i) := by decide +kernel

theorem threshold_12_65 : ∀ i ∈ List.range 1, ThresholdAt 12 (65+i) := by decide +kernel

theorem threshold_12_66 : ∀ i ∈ List.range 1, ThresholdAt 12 (66+i) := by decide +kernel

theorem threshold_12_67 : ∀ i ∈ List.range 1, ThresholdAt 12 (67+i) := by decide +kernel

theorem threshold_12_68 : ∀ i ∈ List.range 1, ThresholdAt 12 (68+i) := by decide +kernel

theorem threshold_12_69 : ∀ i ∈ List.range 1, ThresholdAt 12 (69+i) := by decide +kernel

theorem threshold_12_70 : ∀ i ∈ List.range 1, ThresholdAt 12 (70+i) := by decide +kernel

theorem threshold_12_71 : ∀ i ∈ List.range 1, ThresholdAt 12 (71+i) := by decide +kernel

theorem threshold_12_72 : ∀ i ∈ List.range 1, ThresholdAt 12 (72+i) := by decide +kernel

theorem threshold_12_73 : ∀ i ∈ List.range 1, ThresholdAt 12 (73+i) := by decide +kernel

theorem threshold_12_74 : ∀ i ∈ List.range 1, ThresholdAt 12 (74+i) := by decide +kernel

theorem threshold_12_75 : ∀ i ∈ List.range 1, ThresholdAt 12 (75+i) := by decide +kernel

theorem threshold_12_76 : ∀ i ∈ List.range 1, ThresholdAt 12 (76+i) := by decide +kernel

theorem threshold_12_77 : ∀ i ∈ List.range 1, ThresholdAt 12 (77+i) := by decide +kernel

theorem threshold_12_78 : ∀ i ∈ List.range 1, ThresholdAt 12 (78+i) := by decide +kernel

theorem threshold_12_79 : ∀ i ∈ List.range 1, ThresholdAt 12 (79+i) := by decide +kernel

theorem threshold_12_80 : ∀ i ∈ List.range 1, ThresholdAt 12 (80+i) := by decide +kernel

theorem threshold_12_81 : ∀ i ∈ List.range 1, ThresholdAt 12 (81+i) := by decide +kernel

theorem threshold_12_82 : ∀ i ∈ List.range 1, ThresholdAt 12 (82+i) := by decide +kernel

theorem threshold_12_83 : ∀ i ∈ List.range 1, ThresholdAt 12 (83+i) := by decide +kernel

theorem threshold_12_84 : ∀ i ∈ List.range 1, ThresholdAt 12 (84+i) := by decide +kernel

theorem threshold_12_85 : ∀ i ∈ List.range 1, ThresholdAt 12 (85+i) := by decide +kernel

theorem threshold_12_86 : ∀ i ∈ List.range 1, ThresholdAt 12 (86+i) := by decide +kernel

theorem threshold_12_87 : ∀ i ∈ List.range 1, ThresholdAt 12 (87+i) := by decide +kernel

theorem threshold_12_88 : ∀ i ∈ List.range 1, ThresholdAt 12 (88+i) := by decide +kernel

theorem threshold_12_89 : ∀ i ∈ List.range 1, ThresholdAt 12 (89+i) := by decide +kernel

theorem threshold_12_90 : ∀ i ∈ List.range 1, ThresholdAt 12 (90+i) := by decide +kernel

theorem threshold_12_91 : ∀ i ∈ List.range 1, ThresholdAt 12 (91+i) := by decide +kernel

theorem threshold_12_92 : ∀ i ∈ List.range 1, ThresholdAt 12 (92+i) := by decide +kernel

theorem threshold_12_93 : ∀ i ∈ List.range 1, ThresholdAt 12 (93+i) := by decide +kernel

theorem threshold_12_94 : ∀ i ∈ List.range 1, ThresholdAt 12 (94+i) := by decide +kernel

theorem threshold_12_95 : ∀ i ∈ List.range 1, ThresholdAt 12 (95+i) := by decide +kernel

theorem threshold_12_96 : ∀ i ∈ List.range 1, ThresholdAt 12 (96+i) := by decide +kernel

theorem threshold_12_97 : ∀ i ∈ List.range 1, ThresholdAt 12 (97+i) := by decide +kernel

theorem threshold_12_98 : ∀ i ∈ List.range 1, ThresholdAt 12 (98+i) := by decide +kernel

theorem threshold_12_99 : ∀ i ∈ List.range 1, ThresholdAt 12 (99+i) := by decide +kernel

theorem threshold_12_100 : ∀ i ∈ List.range 1, ThresholdAt 12 (100+i) := by decide +kernel

theorem threshold_12_101 : ∀ i ∈ List.range 1, ThresholdAt 12 (101+i) := by decide +kernel

theorem threshold_12_102 : ∀ i ∈ List.range 1, ThresholdAt 12 (102+i) := by decide +kernel

theorem threshold_12_103 : ∀ i ∈ List.range 1, ThresholdAt 12 (103+i) := by decide +kernel

theorem threshold_12_104 : ∀ i ∈ List.range 1, ThresholdAt 12 (104+i) := by decide +kernel

theorem threshold_12_105 : ∀ i ∈ List.range 1, ThresholdAt 12 (105+i) := by decide +kernel

theorem threshold_12_106 : ∀ i ∈ List.range 1, ThresholdAt 12 (106+i) := by decide +kernel

theorem threshold_12_107 : ∀ i ∈ List.range 1, ThresholdAt 12 (107+i) := by decide +kernel

theorem threshold_12_108 : ∀ i ∈ List.range 1, ThresholdAt 12 (108+i) := by decide +kernel

theorem threshold_12_109 : ∀ i ∈ List.range 1, ThresholdAt 12 (109+i) := by decide +kernel

theorem threshold_12_110 : ∀ i ∈ List.range 1, ThresholdAt 12 (110+i) := by decide +kernel

theorem threshold_12_111 : ∀ i ∈ List.range 1, ThresholdAt 12 (111+i) := by decide +kernel

theorem threshold_12_112 : ∀ i ∈ List.range 1, ThresholdAt 12 (112+i) := by decide +kernel

theorem threshold_12_113 : ∀ i ∈ List.range 1, ThresholdAt 12 (113+i) := by decide +kernel

theorem threshold_12_114 : ∀ i ∈ List.range 1, ThresholdAt 12 (114+i) := by decide +kernel

theorem threshold_12_115 : ∀ i ∈ List.range 1, ThresholdAt 12 (115+i) := by decide +kernel

theorem threshold_12_116 : ∀ i ∈ List.range 1, ThresholdAt 12 (116+i) := by decide +kernel

theorem threshold_12_117 : ∀ i ∈ List.range 1, ThresholdAt 12 (117+i) := by decide +kernel

theorem threshold_12_118 : ∀ i ∈ List.range 1, ThresholdAt 12 (118+i) := by decide +kernel

theorem threshold_12_119 : ∀ i ∈ List.range 1, ThresholdAt 12 (119+i) := by decide +kernel

theorem threshold_12_120 : ∀ i ∈ List.range 1, ThresholdAt 12 (120+i) := by decide +kernel

theorem threshold_12_121 : ∀ i ∈ List.range 1, ThresholdAt 12 (121+i) := by decide +kernel

theorem threshold_12_122 : ∀ i ∈ List.range 1, ThresholdAt 12 (122+i) := by decide +kernel

theorem threshold_12_123 : ∀ i ∈ List.range 1, ThresholdAt 12 (123+i) := by decide +kernel

theorem threshold_12_124 : ∀ i ∈ List.range 1, ThresholdAt 12 (124+i) := by decide +kernel

theorem threshold_12_125 : ∀ i ∈ List.range 1, ThresholdAt 12 (125+i) := by decide +kernel

theorem threshold_12_126 : ∀ i ∈ List.range 1, ThresholdAt 12 (126+i) := by decide +kernel

theorem threshold_12_127 : ∀ i ∈ List.range 1, ThresholdAt 12 (127+i) := by decide +kernel

theorem threshold_12_128 : ∀ i ∈ List.range 1, ThresholdAt 12 (128+i) := by decide +kernel

theorem threshold_12_129 : ∀ i ∈ List.range 1, ThresholdAt 12 (129+i) := by decide +kernel

theorem threshold_12_130 : ∀ i ∈ List.range 1, ThresholdAt 12 (130+i) := by decide +kernel

theorem threshold_12_131 : ∀ i ∈ List.range 1, ThresholdAt 12 (131+i) := by decide +kernel

theorem threshold_12_132 : ∀ i ∈ List.range 1, ThresholdAt 12 (132+i) := by decide +kernel

theorem threshold_12_133 : ∀ i ∈ List.range 1, ThresholdAt 12 (133+i) := by decide +kernel

theorem threshold_12_134 : ∀ i ∈ List.range 1, ThresholdAt 12 (134+i) := by decide +kernel

theorem threshold_12 (v : ℕ) (hv : v ∈ List.range 135) : ThresholdAt 12 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 12 v)
  have h := (join 0 67 68 (join 0 33 34 (join 0 16 17 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_12_0 threshold_12_1) (join 2 1 1 threshold_12_2 threshold_12_3)) (join 4 2 2 (join 4 1 1 threshold_12_4 threshold_12_5) (join 6 1 1 threshold_12_6 threshold_12_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_12_8 threshold_12_9) (join 10 1 1 threshold_12_10 threshold_12_11)) (join 12 2 2 (join 12 1 1 threshold_12_12 threshold_12_13) (join 14 1 1 threshold_12_14 threshold_12_15)))) (join 16 8 9 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_12_16 threshold_12_17) (join 18 1 1 threshold_12_18 threshold_12_19)) (join 20 2 2 (join 20 1 1 threshold_12_20 threshold_12_21) (join 22 1 1 threshold_12_22 threshold_12_23))) (join 24 4 5 (join 24 2 2 (join 24 1 1 threshold_12_24 threshold_12_25) (join 26 1 1 threshold_12_26 threshold_12_27)) (join 28 2 3 (join 28 1 1 threshold_12_28 threshold_12_29) (join 30 1 2 threshold_12_30 (join 31 1 1 threshold_12_31 threshold_12_32)))))) (join 33 17 17 (join 33 8 9 (join 33 4 4 (join 33 2 2 (join 33 1 1 threshold_12_33 threshold_12_34) (join 35 1 1 threshold_12_35 threshold_12_36)) (join 37 2 2 (join 37 1 1 threshold_12_37 threshold_12_38) (join 39 1 1 threshold_12_39 threshold_12_40))) (join 41 4 5 (join 41 2 2 (join 41 1 1 threshold_12_41 threshold_12_42) (join 43 1 1 threshold_12_43 threshold_12_44)) (join 45 2 3 (join 45 1 1 threshold_12_45 threshold_12_46) (join 47 1 2 threshold_12_47 (join 48 1 1 threshold_12_48 threshold_12_49))))) (join 50 8 9 (join 50 4 4 (join 50 2 2 (join 50 1 1 threshold_12_50 threshold_12_51) (join 52 1 1 threshold_12_52 threshold_12_53)) (join 54 2 2 (join 54 1 1 threshold_12_54 threshold_12_55) (join 56 1 1 threshold_12_56 threshold_12_57))) (join 58 4 5 (join 58 2 2 (join 58 1 1 threshold_12_58 threshold_12_59) (join 60 1 1 threshold_12_60 threshold_12_61)) (join 62 2 3 (join 62 1 1 threshold_12_62 threshold_12_63) (join 64 1 2 threshold_12_64 (join 65 1 1 threshold_12_65 threshold_12_66))))))) (join 67 34 34 (join 67 17 17 (join 67 8 9 (join 67 4 4 (join 67 2 2 (join 67 1 1 threshold_12_67 threshold_12_68) (join 69 1 1 threshold_12_69 threshold_12_70)) (join 71 2 2 (join 71 1 1 threshold_12_71 threshold_12_72) (join 73 1 1 threshold_12_73 threshold_12_74))) (join 75 4 5 (join 75 2 2 (join 75 1 1 threshold_12_75 threshold_12_76) (join 77 1 1 threshold_12_77 threshold_12_78)) (join 79 2 3 (join 79 1 1 threshold_12_79 threshold_12_80) (join 81 1 2 threshold_12_81 (join 82 1 1 threshold_12_82 threshold_12_83))))) (join 84 8 9 (join 84 4 4 (join 84 2 2 (join 84 1 1 threshold_12_84 threshold_12_85) (join 86 1 1 threshold_12_86 threshold_12_87)) (join 88 2 2 (join 88 1 1 threshold_12_88 threshold_12_89) (join 90 1 1 threshold_12_90 threshold_12_91))) (join 92 4 5 (join 92 2 2 (join 92 1 1 threshold_12_92 threshold_12_93) (join 94 1 1 threshold_12_94 threshold_12_95)) (join 96 2 3 (join 96 1 1 threshold_12_96 threshold_12_97) (join 98 1 2 threshold_12_98 (join 99 1 1 threshold_12_99 threshold_12_100)))))) (join 101 17 17 (join 101 8 9 (join 101 4 4 (join 101 2 2 (join 101 1 1 threshold_12_101 threshold_12_102) (join 103 1 1 threshold_12_103 threshold_12_104)) (join 105 2 2 (join 105 1 1 threshold_12_105 threshold_12_106) (join 107 1 1 threshold_12_107 threshold_12_108))) (join 109 4 5 (join 109 2 2 (join 109 1 1 threshold_12_109 threshold_12_110) (join 111 1 1 threshold_12_111 threshold_12_112)) (join 113 2 3 (join 113 1 1 threshold_12_113 threshold_12_114) (join 115 1 2 threshold_12_115 (join 116 1 1 threshold_12_116 threshold_12_117))))) (join 118 8 9 (join 118 4 4 (join 118 2 2 (join 118 1 1 threshold_12_118 threshold_12_119) (join 120 1 1 threshold_12_120 threshold_12_121)) (join 122 2 2 (join 122 1 1 threshold_12_122 threshold_12_123) (join 124 1 1 threshold_12_124 threshold_12_125))) (join 126 4 5 (join 126 2 2 (join 126 1 1 threshold_12_126 threshold_12_127) (join 128 1 1 threshold_12_128 threshold_12_129)) (join 130 2 3 (join 130 1 1 threshold_12_130 threshold_12_131) (join 132 1 2 threshold_12_132 (join 133 1 1 threshold_12_133 threshold_12_134))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_12_0 : ∀ i ∈ List.range 4, LedgerAt 12 (0+i) := by decide +kernel

theorem ledger_12_4 : ∀ i ∈ List.range 4, LedgerAt 12 (4+i) := by decide +kernel

theorem ledger_12_8 : ∀ i ∈ List.range 4, LedgerAt 12 (8+i) := by decide +kernel

theorem ledger_12_12 : ∀ i ∈ List.range 4, LedgerAt 12 (12+i) := by decide +kernel

theorem ledger_12_16 : ∀ i ∈ List.range 4, LedgerAt 12 (16+i) := by decide +kernel

theorem ledger_12_20 : ∀ i ∈ List.range 4, LedgerAt 12 (20+i) := by decide +kernel

theorem ledger_12_24 : ∀ i ∈ List.range 4, LedgerAt 12 (24+i) := by decide +kernel

theorem ledger_12_28 : ∀ i ∈ List.range 4, LedgerAt 12 (28+i) := by decide +kernel

theorem ledger_12_32 : ∀ i ∈ List.range 4, LedgerAt 12 (32+i) := by decide +kernel

theorem ledger_12_36 : ∀ i ∈ List.range 4, LedgerAt 12 (36+i) := by decide +kernel

theorem ledger_12_40 : ∀ i ∈ List.range 4, LedgerAt 12 (40+i) := by decide +kernel

theorem ledger_12_44 : ∀ i ∈ List.range 4, LedgerAt 12 (44+i) := by decide +kernel

theorem ledger_12_48 : ∀ i ∈ List.range 4, LedgerAt 12 (48+i) := by decide +kernel

theorem ledger_12_52 : ∀ i ∈ List.range 4, LedgerAt 12 (52+i) := by decide +kernel

theorem ledger_12_56 : ∀ i ∈ List.range 4, LedgerAt 12 (56+i) := by decide +kernel

theorem ledger_12_60 : ∀ i ∈ List.range 4, LedgerAt 12 (60+i) := by decide +kernel

theorem ledger_12_64 : ∀ i ∈ List.range 4, LedgerAt 12 (64+i) := by decide +kernel

theorem ledger_12_68 : ∀ i ∈ List.range 4, LedgerAt 12 (68+i) := by decide +kernel

theorem ledger_12_72 : ∀ i ∈ List.range 4, LedgerAt 12 (72+i) := by decide +kernel

theorem ledger_12_76 : ∀ i ∈ List.range 4, LedgerAt 12 (76+i) := by decide +kernel

theorem ledger_12_80 : ∀ i ∈ List.range 4, LedgerAt 12 (80+i) := by decide +kernel

theorem ledger_12_84 : ∀ i ∈ List.range 4, LedgerAt 12 (84+i) := by decide +kernel

theorem ledger_12_88 : ∀ i ∈ List.range 4, LedgerAt 12 (88+i) := by decide +kernel

theorem ledger_12_92 : ∀ i ∈ List.range 4, LedgerAt 12 (92+i) := by decide +kernel

theorem ledger_12_96 : ∀ i ∈ List.range 4, LedgerAt 12 (96+i) := by decide +kernel

theorem ledger_12_100 : ∀ i ∈ List.range 4, LedgerAt 12 (100+i) := by decide +kernel

theorem ledger_12_104 : ∀ i ∈ List.range 4, LedgerAt 12 (104+i) := by decide +kernel

theorem ledger_12_108 : ∀ i ∈ List.range 4, LedgerAt 12 (108+i) := by decide +kernel

theorem ledger_12_112 : ∀ i ∈ List.range 4, LedgerAt 12 (112+i) := by decide +kernel

theorem ledger_12_116 : ∀ i ∈ List.range 4, LedgerAt 12 (116+i) := by decide +kernel

theorem ledger_12_120 : ∀ i ∈ List.range 4, LedgerAt 12 (120+i) := by decide +kernel

theorem ledger_12_124 : ∀ i ∈ List.range 4, LedgerAt 12 (124+i) := by decide +kernel

theorem ledger_12_128 : ∀ i ∈ List.range 4, LedgerAt 12 (128+i) := by decide +kernel

theorem ledger_12_132 : ∀ i ∈ List.range 3, LedgerAt 12 (132+i) := by decide +kernel

theorem ledger_12 (v : ℕ) (hv : v ∈ List.range 135) : LedgerAt 12 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 12 v)
  have h := (join 0 68 67 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_12_0 ledger_12_4) (join 8 4 4 ledger_12_8 ledger_12_12)) (join 16 8 8 (join 16 4 4 ledger_12_16 ledger_12_20) (join 24 4 4 ledger_12_24 ledger_12_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_12_32 ledger_12_36) (join 40 4 4 ledger_12_40 ledger_12_44)) (join 48 8 12 (join 48 4 4 ledger_12_48 ledger_12_52) (join 56 4 8 ledger_12_56 (join 60 4 4 ledger_12_60 ledger_12_64))))) (join 68 32 35 (join 68 16 16 (join 68 8 8 (join 68 4 4 ledger_12_68 ledger_12_72) (join 76 4 4 ledger_12_76 ledger_12_80)) (join 84 8 8 (join 84 4 4 ledger_12_84 ledger_12_88) (join 92 4 4 ledger_12_92 ledger_12_96))) (join 100 16 19 (join 100 8 8 (join 100 4 4 ledger_12_100 ledger_12_104) (join 108 4 4 ledger_12_108 ledger_12_112)) (join 116 8 11 (join 116 4 4 ledger_12_116 ledger_12_120) (join 124 4 7 ledger_12_124 (join 128 4 3 ledger_12_128 ledger_12_132))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
