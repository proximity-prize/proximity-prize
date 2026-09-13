import ProximityPrize.SubmissionLower.BoundaryTailCheckedR136807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_14_0 : ∀ i ∈ List.range 4, GeometryAt 14 (0+i) := by decide +kernel

theorem geometry_14_4 : ∀ i ∈ List.range 4, GeometryAt 14 (4+i) := by decide +kernel

theorem geometry_14_8 : ∀ i ∈ List.range 4, GeometryAt 14 (8+i) := by decide +kernel

theorem geometry_14_12 : ∀ i ∈ List.range 4, GeometryAt 14 (12+i) := by decide +kernel

theorem geometry_14_16 : ∀ i ∈ List.range 4, GeometryAt 14 (16+i) := by decide +kernel

theorem geometry_14_20 : ∀ i ∈ List.range 4, GeometryAt 14 (20+i) := by decide +kernel

theorem geometry_14_24 : ∀ i ∈ List.range 4, GeometryAt 14 (24+i) := by decide +kernel

theorem geometry_14_28 : ∀ i ∈ List.range 4, GeometryAt 14 (28+i) := by decide +kernel

theorem geometry_14_32 : ∀ i ∈ List.range 4, GeometryAt 14 (32+i) := by decide +kernel

theorem geometry_14_36 : ∀ i ∈ List.range 4, GeometryAt 14 (36+i) := by decide +kernel

theorem geometry_14_40 : ∀ i ∈ List.range 4, GeometryAt 14 (40+i) := by decide +kernel

theorem geometry_14_44 : ∀ i ∈ List.range 4, GeometryAt 14 (44+i) := by decide +kernel

theorem geometry_14_48 : ∀ i ∈ List.range 4, GeometryAt 14 (48+i) := by decide +kernel

theorem geometry_14_52 : ∀ i ∈ List.range 4, GeometryAt 14 (52+i) := by decide +kernel

theorem geometry_14_56 : ∀ i ∈ List.range 4, GeometryAt 14 (56+i) := by decide +kernel

theorem geometry_14_60 : ∀ i ∈ List.range 4, GeometryAt 14 (60+i) := by decide +kernel

theorem geometry_14_64 : ∀ i ∈ List.range 4, GeometryAt 14 (64+i) := by decide +kernel

theorem geometry_14_68 : ∀ i ∈ List.range 4, GeometryAt 14 (68+i) := by decide +kernel

theorem geometry_14_72 : ∀ i ∈ List.range 4, GeometryAt 14 (72+i) := by decide +kernel

theorem geometry_14_76 : ∀ i ∈ List.range 4, GeometryAt 14 (76+i) := by decide +kernel

theorem geometry_14_80 : ∀ i ∈ List.range 4, GeometryAt 14 (80+i) := by decide +kernel

theorem geometry_14_84 : ∀ i ∈ List.range 4, GeometryAt 14 (84+i) := by decide +kernel

theorem geometry_14_88 : ∀ i ∈ List.range 4, GeometryAt 14 (88+i) := by decide +kernel

theorem geometry_14_92 : ∀ i ∈ List.range 4, GeometryAt 14 (92+i) := by decide +kernel

theorem geometry_14_96 : ∀ i ∈ List.range 4, GeometryAt 14 (96+i) := by decide +kernel

theorem geometry_14_100 : ∀ i ∈ List.range 4, GeometryAt 14 (100+i) := by decide +kernel

theorem geometry_14_104 : ∀ i ∈ List.range 4, GeometryAt 14 (104+i) := by decide +kernel

theorem geometry_14_108 : ∀ i ∈ List.range 4, GeometryAt 14 (108+i) := by decide +kernel

theorem geometry_14_112 : ∀ i ∈ List.range 4, GeometryAt 14 (112+i) := by decide +kernel

theorem geometry_14_116 : ∀ i ∈ List.range 4, GeometryAt 14 (116+i) := by decide +kernel

theorem geometry_14_120 : ∀ i ∈ List.range 4, GeometryAt 14 (120+i) := by decide +kernel

theorem geometry_14_124 : ∀ i ∈ List.range 4, GeometryAt 14 (124+i) := by decide +kernel

theorem geometry_14_128 : ∀ i ∈ List.range 4, GeometryAt 14 (128+i) := by decide +kernel

theorem geometry_14_132 : ∀ i ∈ List.range 1, GeometryAt 14 (132+i) := by decide +kernel

theorem geometry_14 (v : ℕ) (hv : v ∈ List.range 133) : GeometryAt 14 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 14 v)
  have h := (join 0 68 65 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_14_0 geometry_14_4) (join 8 4 4 geometry_14_8 geometry_14_12)) (join 16 8 8 (join 16 4 4 geometry_14_16 geometry_14_20) (join 24 4 4 geometry_14_24 geometry_14_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 geometry_14_32 geometry_14_36) (join 40 4 4 geometry_14_40 geometry_14_44)) (join 48 8 12 (join 48 4 4 geometry_14_48 geometry_14_52) (join 56 4 8 geometry_14_56 (join 60 4 4 geometry_14_60 geometry_14_64))))) (join 68 32 33 (join 68 16 16 (join 68 8 8 (join 68 4 4 geometry_14_68 geometry_14_72) (join 76 4 4 geometry_14_76 geometry_14_80)) (join 84 8 8 (join 84 4 4 geometry_14_84 geometry_14_88) (join 92 4 4 geometry_14_92 geometry_14_96))) (join 100 16 17 (join 100 8 8 (join 100 4 4 geometry_14_100 geometry_14_104) (join 108 4 4 geometry_14_108 geometry_14_112)) (join 116 8 9 (join 116 4 4 geometry_14_116 geometry_14_120) (join 124 4 5 geometry_14_124 (join 128 4 1 geometry_14_128 geometry_14_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_14_0 : ∀ i ∈ List.range 4, StrictAt 14 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (0+i)) 14 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_4 : ∀ i ∈ List.range 4, StrictAt 14 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (4+i)) 14 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_8 : ∀ i ∈ List.range 4, StrictAt 14 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (8+i)) 14 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_12 : ∀ i ∈ List.range 4, StrictAt 14 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (12+i)) 14 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_16 : ∀ i ∈ List.range 4, StrictAt 14 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (16+i)) 14 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_20 : ∀ i ∈ List.range 4, StrictAt 14 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (20+i)) 14 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_24 : ∀ i ∈ List.range 4, StrictAt 14 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (24+i)) 14 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_28 : ∀ i ∈ List.range 4, StrictAt 14 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (28+i)) 14 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_32 : ∀ i ∈ List.range 4, StrictAt 14 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (32+i)) 14 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_36 : ∀ i ∈ List.range 4, StrictAt 14 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (36+i)) 14 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_40 : ∀ i ∈ List.range 4, StrictAt 14 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (40+i)) 14 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_44 : ∀ i ∈ List.range 4, StrictAt 14 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (44+i)) 14 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_48 : ∀ i ∈ List.range 4, StrictAt 14 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (48+i)) 14 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_52 : ∀ i ∈ List.range 4, StrictAt 14 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (52+i)) 14 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_56 : ∀ i ∈ List.range 4, StrictAt 14 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (56+i)) 14 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_60 : ∀ i ∈ List.range 4, StrictAt 14 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (60+i)) 14 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_64 : ∀ i ∈ List.range 4, StrictAt 14 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (64+i)) 14 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_68 : ∀ i ∈ List.range 4, StrictAt 14 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (68+i)) 14 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_72 : ∀ i ∈ List.range 4, StrictAt 14 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (72+i)) 14 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_76 : ∀ i ∈ List.range 4, StrictAt 14 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (76+i)) 14 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_80 : ∀ i ∈ List.range 4, StrictAt 14 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (80+i)) 14 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_84 : ∀ i ∈ List.range 4, StrictAt 14 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (84+i)) 14 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_88 : ∀ i ∈ List.range 4, StrictAt 14 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (88+i)) 14 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_92 : ∀ i ∈ List.range 4, StrictAt 14 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (92+i)) 14 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_96 : ∀ i ∈ List.range 4, StrictAt 14 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (96+i)) 14 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_100 : ∀ i ∈ List.range 4, StrictAt 14 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (100+i)) 14 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_104 : ∀ i ∈ List.range 4, StrictAt 14 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (104+i)) 14 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_108 : ∀ i ∈ List.range 4, StrictAt 14 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (108+i)) 14 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_112 : ∀ i ∈ List.range 4, StrictAt 14 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (112+i)) 14 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_116 : ∀ i ∈ List.range 4, StrictAt 14 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (116+i)) 14 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_120 : ∀ i ∈ List.range 4, StrictAt 14 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (120+i)) 14 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_124 : ∀ i ∈ List.range 4, StrictAt 14 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (124+i)) 14 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_128 : ∀ i ∈ List.range 4, StrictAt 14 (128+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (128+i)) 14 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14_132 : ∀ i ∈ List.range 1, StrictAt 14 (132+i) := by
  have h : ∀ i ∈ List.range 1, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 14 (132+i)) 14 (132+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_14 (v : ℕ) (hv : v ∈ List.range 133) : StrictAt 14 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 14 v)
  have h := (join 0 68 65 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_14_0 strict_14_4) (join 8 4 4 strict_14_8 strict_14_12)) (join 16 8 8 (join 16 4 4 strict_14_16 strict_14_20) (join 24 4 4 strict_14_24 strict_14_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 strict_14_32 strict_14_36) (join 40 4 4 strict_14_40 strict_14_44)) (join 48 8 12 (join 48 4 4 strict_14_48 strict_14_52) (join 56 4 8 strict_14_56 (join 60 4 4 strict_14_60 strict_14_64))))) (join 68 32 33 (join 68 16 16 (join 68 8 8 (join 68 4 4 strict_14_68 strict_14_72) (join 76 4 4 strict_14_76 strict_14_80)) (join 84 8 8 (join 84 4 4 strict_14_84 strict_14_88) (join 92 4 4 strict_14_92 strict_14_96))) (join 100 16 17 (join 100 8 8 (join 100 4 4 strict_14_100 strict_14_104) (join 108 4 4 strict_14_108 strict_14_112)) (join 116 8 9 (join 116 4 4 strict_14_116 strict_14_120) (join 124 4 5 strict_14_124 (join 128 4 1 strict_14_128 strict_14_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_14_0 : ∀ i ∈ List.range 4, PhaseAt 14 (0+i) := by decide +kernel

theorem phase_14_4 : ∀ i ∈ List.range 4, PhaseAt 14 (4+i) := by decide +kernel

theorem phase_14_8 : ∀ i ∈ List.range 4, PhaseAt 14 (8+i) := by decide +kernel

theorem phase_14_12 : ∀ i ∈ List.range 4, PhaseAt 14 (12+i) := by decide +kernel

theorem phase_14_16 : ∀ i ∈ List.range 4, PhaseAt 14 (16+i) := by decide +kernel

theorem phase_14_20 : ∀ i ∈ List.range 4, PhaseAt 14 (20+i) := by decide +kernel

theorem phase_14_24 : ∀ i ∈ List.range 4, PhaseAt 14 (24+i) := by decide +kernel

theorem phase_14_28 : ∀ i ∈ List.range 4, PhaseAt 14 (28+i) := by decide +kernel

theorem phase_14_32 : ∀ i ∈ List.range 4, PhaseAt 14 (32+i) := by decide +kernel

theorem phase_14_36 : ∀ i ∈ List.range 4, PhaseAt 14 (36+i) := by decide +kernel

theorem phase_14_40 : ∀ i ∈ List.range 4, PhaseAt 14 (40+i) := by decide +kernel

theorem phase_14_44 : ∀ i ∈ List.range 4, PhaseAt 14 (44+i) := by decide +kernel

theorem phase_14_48 : ∀ i ∈ List.range 4, PhaseAt 14 (48+i) := by decide +kernel

theorem phase_14_52 : ∀ i ∈ List.range 4, PhaseAt 14 (52+i) := by decide +kernel

theorem phase_14_56 : ∀ i ∈ List.range 4, PhaseAt 14 (56+i) := by decide +kernel

theorem phase_14_60 : ∀ i ∈ List.range 4, PhaseAt 14 (60+i) := by decide +kernel

theorem phase_14_64 : ∀ i ∈ List.range 4, PhaseAt 14 (64+i) := by decide +kernel

theorem phase_14_68 : ∀ i ∈ List.range 4, PhaseAt 14 (68+i) := by decide +kernel

theorem phase_14_72 : ∀ i ∈ List.range 4, PhaseAt 14 (72+i) := by decide +kernel

theorem phase_14_76 : ∀ i ∈ List.range 4, PhaseAt 14 (76+i) := by decide +kernel

theorem phase_14_80 : ∀ i ∈ List.range 4, PhaseAt 14 (80+i) := by decide +kernel

theorem phase_14_84 : ∀ i ∈ List.range 4, PhaseAt 14 (84+i) := by decide +kernel

theorem phase_14_88 : ∀ i ∈ List.range 4, PhaseAt 14 (88+i) := by decide +kernel

theorem phase_14_92 : ∀ i ∈ List.range 4, PhaseAt 14 (92+i) := by decide +kernel

theorem phase_14_96 : ∀ i ∈ List.range 4, PhaseAt 14 (96+i) := by decide +kernel

theorem phase_14_100 : ∀ i ∈ List.range 4, PhaseAt 14 (100+i) := by decide +kernel

theorem phase_14_104 : ∀ i ∈ List.range 4, PhaseAt 14 (104+i) := by decide +kernel

theorem phase_14_108 : ∀ i ∈ List.range 4, PhaseAt 14 (108+i) := by decide +kernel

theorem phase_14_112 : ∀ i ∈ List.range 4, PhaseAt 14 (112+i) := by decide +kernel

theorem phase_14_116 : ∀ i ∈ List.range 4, PhaseAt 14 (116+i) := by decide +kernel

theorem phase_14_120 : ∀ i ∈ List.range 4, PhaseAt 14 (120+i) := by decide +kernel

theorem phase_14_124 : ∀ i ∈ List.range 4, PhaseAt 14 (124+i) := by decide +kernel

theorem phase_14_128 : ∀ i ∈ List.range 4, PhaseAt 14 (128+i) := by decide +kernel

theorem phase_14_132 : ∀ i ∈ List.range 1, PhaseAt 14 (132+i) := by decide +kernel

theorem phase_14 (v : ℕ) (hv : v ∈ List.range 133) : PhaseAt 14 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 14 v)
  have h := (join 0 68 65 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_14_0 phase_14_4) (join 8 4 4 phase_14_8 phase_14_12)) (join 16 8 8 (join 16 4 4 phase_14_16 phase_14_20) (join 24 4 4 phase_14_24 phase_14_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_14_32 phase_14_36) (join 40 4 4 phase_14_40 phase_14_44)) (join 48 8 12 (join 48 4 4 phase_14_48 phase_14_52) (join 56 4 8 phase_14_56 (join 60 4 4 phase_14_60 phase_14_64))))) (join 68 32 33 (join 68 16 16 (join 68 8 8 (join 68 4 4 phase_14_68 phase_14_72) (join 76 4 4 phase_14_76 phase_14_80)) (join 84 8 8 (join 84 4 4 phase_14_84 phase_14_88) (join 92 4 4 phase_14_92 phase_14_96))) (join 100 16 17 (join 100 8 8 (join 100 4 4 phase_14_100 phase_14_104) (join 108 4 4 phase_14_108 phase_14_112)) (join 116 8 9 (join 116 4 4 phase_14_116 phase_14_120) (join 124 4 5 phase_14_124 (join 128 4 1 phase_14_128 phase_14_132))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_14_0 : ∀ i ∈ List.range 1, ThresholdAt 14 (0+i) := by decide +kernel

theorem threshold_14_1 : ∀ i ∈ List.range 1, ThresholdAt 14 (1+i) := by decide +kernel

theorem threshold_14_2 : ∀ i ∈ List.range 1, ThresholdAt 14 (2+i) := by decide +kernel

theorem threshold_14_3 : ∀ i ∈ List.range 1, ThresholdAt 14 (3+i) := by decide +kernel

theorem threshold_14_4 : ∀ i ∈ List.range 1, ThresholdAt 14 (4+i) := by decide +kernel

theorem threshold_14_5 : ∀ i ∈ List.range 1, ThresholdAt 14 (5+i) := by decide +kernel

theorem threshold_14_6 : ∀ i ∈ List.range 1, ThresholdAt 14 (6+i) := by decide +kernel

theorem threshold_14_7 : ∀ i ∈ List.range 1, ThresholdAt 14 (7+i) := by decide +kernel

theorem threshold_14_8 : ∀ i ∈ List.range 1, ThresholdAt 14 (8+i) := by decide +kernel

theorem threshold_14_9 : ∀ i ∈ List.range 1, ThresholdAt 14 (9+i) := by decide +kernel

theorem threshold_14_10 : ∀ i ∈ List.range 1, ThresholdAt 14 (10+i) := by decide +kernel

theorem threshold_14_11 : ∀ i ∈ List.range 1, ThresholdAt 14 (11+i) := by decide +kernel

theorem threshold_14_12 : ∀ i ∈ List.range 1, ThresholdAt 14 (12+i) := by decide +kernel

theorem threshold_14_13 : ∀ i ∈ List.range 1, ThresholdAt 14 (13+i) := by decide +kernel

theorem threshold_14_14 : ∀ i ∈ List.range 1, ThresholdAt 14 (14+i) := by decide +kernel

theorem threshold_14_15 : ∀ i ∈ List.range 1, ThresholdAt 14 (15+i) := by decide +kernel

theorem threshold_14_16 : ∀ i ∈ List.range 1, ThresholdAt 14 (16+i) := by decide +kernel

theorem threshold_14_17 : ∀ i ∈ List.range 1, ThresholdAt 14 (17+i) := by decide +kernel

theorem threshold_14_18 : ∀ i ∈ List.range 1, ThresholdAt 14 (18+i) := by decide +kernel

theorem threshold_14_19 : ∀ i ∈ List.range 1, ThresholdAt 14 (19+i) := by decide +kernel

theorem threshold_14_20 : ∀ i ∈ List.range 1, ThresholdAt 14 (20+i) := by decide +kernel

theorem threshold_14_21 : ∀ i ∈ List.range 1, ThresholdAt 14 (21+i) := by decide +kernel

theorem threshold_14_22 : ∀ i ∈ List.range 1, ThresholdAt 14 (22+i) := by decide +kernel

theorem threshold_14_23 : ∀ i ∈ List.range 1, ThresholdAt 14 (23+i) := by decide +kernel

theorem threshold_14_24 : ∀ i ∈ List.range 1, ThresholdAt 14 (24+i) := by decide +kernel

theorem threshold_14_25 : ∀ i ∈ List.range 1, ThresholdAt 14 (25+i) := by decide +kernel

theorem threshold_14_26 : ∀ i ∈ List.range 1, ThresholdAt 14 (26+i) := by decide +kernel

theorem threshold_14_27 : ∀ i ∈ List.range 1, ThresholdAt 14 (27+i) := by decide +kernel

theorem threshold_14_28 : ∀ i ∈ List.range 1, ThresholdAt 14 (28+i) := by decide +kernel

theorem threshold_14_29 : ∀ i ∈ List.range 1, ThresholdAt 14 (29+i) := by decide +kernel

theorem threshold_14_30 : ∀ i ∈ List.range 1, ThresholdAt 14 (30+i) := by decide +kernel

theorem threshold_14_31 : ∀ i ∈ List.range 1, ThresholdAt 14 (31+i) := by decide +kernel

theorem threshold_14_32 : ∀ i ∈ List.range 1, ThresholdAt 14 (32+i) := by decide +kernel

theorem threshold_14_33 : ∀ i ∈ List.range 1, ThresholdAt 14 (33+i) := by decide +kernel

theorem threshold_14_34 : ∀ i ∈ List.range 1, ThresholdAt 14 (34+i) := by decide +kernel

theorem threshold_14_35 : ∀ i ∈ List.range 1, ThresholdAt 14 (35+i) := by decide +kernel

theorem threshold_14_36 : ∀ i ∈ List.range 1, ThresholdAt 14 (36+i) := by decide +kernel

theorem threshold_14_37 : ∀ i ∈ List.range 1, ThresholdAt 14 (37+i) := by decide +kernel

theorem threshold_14_38 : ∀ i ∈ List.range 1, ThresholdAt 14 (38+i) := by decide +kernel

theorem threshold_14_39 : ∀ i ∈ List.range 1, ThresholdAt 14 (39+i) := by decide +kernel

theorem threshold_14_40 : ∀ i ∈ List.range 1, ThresholdAt 14 (40+i) := by decide +kernel

theorem threshold_14_41 : ∀ i ∈ List.range 1, ThresholdAt 14 (41+i) := by decide +kernel

theorem threshold_14_42 : ∀ i ∈ List.range 1, ThresholdAt 14 (42+i) := by decide +kernel

theorem threshold_14_43 : ∀ i ∈ List.range 1, ThresholdAt 14 (43+i) := by decide +kernel

theorem threshold_14_44 : ∀ i ∈ List.range 1, ThresholdAt 14 (44+i) := by decide +kernel

theorem threshold_14_45 : ∀ i ∈ List.range 1, ThresholdAt 14 (45+i) := by decide +kernel

theorem threshold_14_46 : ∀ i ∈ List.range 1, ThresholdAt 14 (46+i) := by decide +kernel

theorem threshold_14_47 : ∀ i ∈ List.range 1, ThresholdAt 14 (47+i) := by decide +kernel

theorem threshold_14_48 : ∀ i ∈ List.range 1, ThresholdAt 14 (48+i) := by decide +kernel

theorem threshold_14_49 : ∀ i ∈ List.range 1, ThresholdAt 14 (49+i) := by decide +kernel

theorem threshold_14_50 : ∀ i ∈ List.range 1, ThresholdAt 14 (50+i) := by decide +kernel

theorem threshold_14_51 : ∀ i ∈ List.range 1, ThresholdAt 14 (51+i) := by decide +kernel

theorem threshold_14_52 : ∀ i ∈ List.range 1, ThresholdAt 14 (52+i) := by decide +kernel

theorem threshold_14_53 : ∀ i ∈ List.range 1, ThresholdAt 14 (53+i) := by decide +kernel

theorem threshold_14_54 : ∀ i ∈ List.range 1, ThresholdAt 14 (54+i) := by decide +kernel

theorem threshold_14_55 : ∀ i ∈ List.range 1, ThresholdAt 14 (55+i) := by decide +kernel

theorem threshold_14_56 : ∀ i ∈ List.range 1, ThresholdAt 14 (56+i) := by decide +kernel

theorem threshold_14_57 : ∀ i ∈ List.range 1, ThresholdAt 14 (57+i) := by decide +kernel

theorem threshold_14_58 : ∀ i ∈ List.range 1, ThresholdAt 14 (58+i) := by decide +kernel

theorem threshold_14_59 : ∀ i ∈ List.range 1, ThresholdAt 14 (59+i) := by decide +kernel

theorem threshold_14_60 : ∀ i ∈ List.range 1, ThresholdAt 14 (60+i) := by decide +kernel

theorem threshold_14_61 : ∀ i ∈ List.range 1, ThresholdAt 14 (61+i) := by decide +kernel

theorem threshold_14_62 : ∀ i ∈ List.range 1, ThresholdAt 14 (62+i) := by decide +kernel

theorem threshold_14_63 : ∀ i ∈ List.range 1, ThresholdAt 14 (63+i) := by decide +kernel

theorem threshold_14_64 : ∀ i ∈ List.range 1, ThresholdAt 14 (64+i) := by decide +kernel

theorem threshold_14_65 : ∀ i ∈ List.range 1, ThresholdAt 14 (65+i) := by decide +kernel

theorem threshold_14_66 : ∀ i ∈ List.range 1, ThresholdAt 14 (66+i) := by decide +kernel

theorem threshold_14_67 : ∀ i ∈ List.range 1, ThresholdAt 14 (67+i) := by decide +kernel

theorem threshold_14_68 : ∀ i ∈ List.range 1, ThresholdAt 14 (68+i) := by decide +kernel

theorem threshold_14_69 : ∀ i ∈ List.range 1, ThresholdAt 14 (69+i) := by decide +kernel

theorem threshold_14_70 : ∀ i ∈ List.range 1, ThresholdAt 14 (70+i) := by decide +kernel

theorem threshold_14_71 : ∀ i ∈ List.range 1, ThresholdAt 14 (71+i) := by decide +kernel

theorem threshold_14_72 : ∀ i ∈ List.range 1, ThresholdAt 14 (72+i) := by decide +kernel

theorem threshold_14_73 : ∀ i ∈ List.range 1, ThresholdAt 14 (73+i) := by decide +kernel

theorem threshold_14_74 : ∀ i ∈ List.range 1, ThresholdAt 14 (74+i) := by decide +kernel

theorem threshold_14_75 : ∀ i ∈ List.range 1, ThresholdAt 14 (75+i) := by decide +kernel

theorem threshold_14_76 : ∀ i ∈ List.range 1, ThresholdAt 14 (76+i) := by decide +kernel

theorem threshold_14_77 : ∀ i ∈ List.range 1, ThresholdAt 14 (77+i) := by decide +kernel

theorem threshold_14_78 : ∀ i ∈ List.range 1, ThresholdAt 14 (78+i) := by decide +kernel

theorem threshold_14_79 : ∀ i ∈ List.range 1, ThresholdAt 14 (79+i) := by decide +kernel

theorem threshold_14_80 : ∀ i ∈ List.range 1, ThresholdAt 14 (80+i) := by decide +kernel

theorem threshold_14_81 : ∀ i ∈ List.range 1, ThresholdAt 14 (81+i) := by decide +kernel

theorem threshold_14_82 : ∀ i ∈ List.range 1, ThresholdAt 14 (82+i) := by decide +kernel

theorem threshold_14_83 : ∀ i ∈ List.range 1, ThresholdAt 14 (83+i) := by decide +kernel

theorem threshold_14_84 : ∀ i ∈ List.range 1, ThresholdAt 14 (84+i) := by decide +kernel

theorem threshold_14_85 : ∀ i ∈ List.range 1, ThresholdAt 14 (85+i) := by decide +kernel

theorem threshold_14_86 : ∀ i ∈ List.range 1, ThresholdAt 14 (86+i) := by decide +kernel

theorem threshold_14_87 : ∀ i ∈ List.range 1, ThresholdAt 14 (87+i) := by decide +kernel

theorem threshold_14_88 : ∀ i ∈ List.range 1, ThresholdAt 14 (88+i) := by decide +kernel

theorem threshold_14_89 : ∀ i ∈ List.range 1, ThresholdAt 14 (89+i) := by decide +kernel

theorem threshold_14_90 : ∀ i ∈ List.range 1, ThresholdAt 14 (90+i) := by decide +kernel

theorem threshold_14_91 : ∀ i ∈ List.range 1, ThresholdAt 14 (91+i) := by decide +kernel

theorem threshold_14_92 : ∀ i ∈ List.range 1, ThresholdAt 14 (92+i) := by decide +kernel

theorem threshold_14_93 : ∀ i ∈ List.range 1, ThresholdAt 14 (93+i) := by decide +kernel

theorem threshold_14_94 : ∀ i ∈ List.range 1, ThresholdAt 14 (94+i) := by decide +kernel

theorem threshold_14_95 : ∀ i ∈ List.range 1, ThresholdAt 14 (95+i) := by decide +kernel

theorem threshold_14_96 : ∀ i ∈ List.range 1, ThresholdAt 14 (96+i) := by decide +kernel

theorem threshold_14_97 : ∀ i ∈ List.range 1, ThresholdAt 14 (97+i) := by decide +kernel

theorem threshold_14_98 : ∀ i ∈ List.range 1, ThresholdAt 14 (98+i) := by decide +kernel

theorem threshold_14_99 : ∀ i ∈ List.range 1, ThresholdAt 14 (99+i) := by decide +kernel

theorem threshold_14_100 : ∀ i ∈ List.range 1, ThresholdAt 14 (100+i) := by decide +kernel

theorem threshold_14_101 : ∀ i ∈ List.range 1, ThresholdAt 14 (101+i) := by decide +kernel

theorem threshold_14_102 : ∀ i ∈ List.range 1, ThresholdAt 14 (102+i) := by decide +kernel

theorem threshold_14_103 : ∀ i ∈ List.range 1, ThresholdAt 14 (103+i) := by decide +kernel

theorem threshold_14_104 : ∀ i ∈ List.range 1, ThresholdAt 14 (104+i) := by decide +kernel

theorem threshold_14_105 : ∀ i ∈ List.range 1, ThresholdAt 14 (105+i) := by decide +kernel

theorem threshold_14_106 : ∀ i ∈ List.range 1, ThresholdAt 14 (106+i) := by decide +kernel

theorem threshold_14_107 : ∀ i ∈ List.range 1, ThresholdAt 14 (107+i) := by decide +kernel

theorem threshold_14_108 : ∀ i ∈ List.range 1, ThresholdAt 14 (108+i) := by decide +kernel

theorem threshold_14_109 : ∀ i ∈ List.range 1, ThresholdAt 14 (109+i) := by decide +kernel

theorem threshold_14_110 : ∀ i ∈ List.range 1, ThresholdAt 14 (110+i) := by decide +kernel

theorem threshold_14_111 : ∀ i ∈ List.range 1, ThresholdAt 14 (111+i) := by decide +kernel

theorem threshold_14_112 : ∀ i ∈ List.range 1, ThresholdAt 14 (112+i) := by decide +kernel

theorem threshold_14_113 : ∀ i ∈ List.range 1, ThresholdAt 14 (113+i) := by decide +kernel

theorem threshold_14_114 : ∀ i ∈ List.range 1, ThresholdAt 14 (114+i) := by decide +kernel

theorem threshold_14_115 : ∀ i ∈ List.range 1, ThresholdAt 14 (115+i) := by decide +kernel

theorem threshold_14_116 : ∀ i ∈ List.range 1, ThresholdAt 14 (116+i) := by decide +kernel

theorem threshold_14_117 : ∀ i ∈ List.range 1, ThresholdAt 14 (117+i) := by decide +kernel

theorem threshold_14_118 : ∀ i ∈ List.range 1, ThresholdAt 14 (118+i) := by decide +kernel

theorem threshold_14_119 : ∀ i ∈ List.range 1, ThresholdAt 14 (119+i) := by decide +kernel

theorem threshold_14_120 : ∀ i ∈ List.range 1, ThresholdAt 14 (120+i) := by decide +kernel

theorem threshold_14_121 : ∀ i ∈ List.range 1, ThresholdAt 14 (121+i) := by decide +kernel

theorem threshold_14_122 : ∀ i ∈ List.range 1, ThresholdAt 14 (122+i) := by decide +kernel

theorem threshold_14_123 : ∀ i ∈ List.range 1, ThresholdAt 14 (123+i) := by decide +kernel

theorem threshold_14_124 : ∀ i ∈ List.range 1, ThresholdAt 14 (124+i) := by decide +kernel

theorem threshold_14_125 : ∀ i ∈ List.range 1, ThresholdAt 14 (125+i) := by decide +kernel

theorem threshold_14_126 : ∀ i ∈ List.range 1, ThresholdAt 14 (126+i) := by decide +kernel

theorem threshold_14_127 : ∀ i ∈ List.range 1, ThresholdAt 14 (127+i) := by decide +kernel

theorem threshold_14_128 : ∀ i ∈ List.range 1, ThresholdAt 14 (128+i) := by decide +kernel

theorem threshold_14_129 : ∀ i ∈ List.range 1, ThresholdAt 14 (129+i) := by decide +kernel

theorem threshold_14_130 : ∀ i ∈ List.range 1, ThresholdAt 14 (130+i) := by decide +kernel

theorem threshold_14_131 : ∀ i ∈ List.range 1, ThresholdAt 14 (131+i) := by decide +kernel

theorem threshold_14_132 : ∀ i ∈ List.range 1, ThresholdAt 14 (132+i) := by decide +kernel

theorem threshold_14 (v : ℕ) (hv : v ∈ List.range 133) : ThresholdAt 14 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 14 v)
  have h := (join 0 66 67 (join 0 33 33 (join 0 16 17 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_14_0 threshold_14_1) (join 2 1 1 threshold_14_2 threshold_14_3)) (join 4 2 2 (join 4 1 1 threshold_14_4 threshold_14_5) (join 6 1 1 threshold_14_6 threshold_14_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_14_8 threshold_14_9) (join 10 1 1 threshold_14_10 threshold_14_11)) (join 12 2 2 (join 12 1 1 threshold_14_12 threshold_14_13) (join 14 1 1 threshold_14_14 threshold_14_15)))) (join 16 8 9 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_14_16 threshold_14_17) (join 18 1 1 threshold_14_18 threshold_14_19)) (join 20 2 2 (join 20 1 1 threshold_14_20 threshold_14_21) (join 22 1 1 threshold_14_22 threshold_14_23))) (join 24 4 5 (join 24 2 2 (join 24 1 1 threshold_14_24 threshold_14_25) (join 26 1 1 threshold_14_26 threshold_14_27)) (join 28 2 3 (join 28 1 1 threshold_14_28 threshold_14_29) (join 30 1 2 threshold_14_30 (join 31 1 1 threshold_14_31 threshold_14_32)))))) (join 33 16 17 (join 33 8 8 (join 33 4 4 (join 33 2 2 (join 33 1 1 threshold_14_33 threshold_14_34) (join 35 1 1 threshold_14_35 threshold_14_36)) (join 37 2 2 (join 37 1 1 threshold_14_37 threshold_14_38) (join 39 1 1 threshold_14_39 threshold_14_40))) (join 41 4 4 (join 41 2 2 (join 41 1 1 threshold_14_41 threshold_14_42) (join 43 1 1 threshold_14_43 threshold_14_44)) (join 45 2 2 (join 45 1 1 threshold_14_45 threshold_14_46) (join 47 1 1 threshold_14_47 threshold_14_48)))) (join 49 8 9 (join 49 4 4 (join 49 2 2 (join 49 1 1 threshold_14_49 threshold_14_50) (join 51 1 1 threshold_14_51 threshold_14_52)) (join 53 2 2 (join 53 1 1 threshold_14_53 threshold_14_54) (join 55 1 1 threshold_14_55 threshold_14_56))) (join 57 4 5 (join 57 2 2 (join 57 1 1 threshold_14_57 threshold_14_58) (join 59 1 1 threshold_14_59 threshold_14_60)) (join 61 2 3 (join 61 1 1 threshold_14_61 threshold_14_62) (join 63 1 2 threshold_14_63 (join 64 1 1 threshold_14_64 threshold_14_65))))))) (join 66 33 34 (join 66 16 17 (join 66 8 8 (join 66 4 4 (join 66 2 2 (join 66 1 1 threshold_14_66 threshold_14_67) (join 68 1 1 threshold_14_68 threshold_14_69)) (join 70 2 2 (join 70 1 1 threshold_14_70 threshold_14_71) (join 72 1 1 threshold_14_72 threshold_14_73))) (join 74 4 4 (join 74 2 2 (join 74 1 1 threshold_14_74 threshold_14_75) (join 76 1 1 threshold_14_76 threshold_14_77)) (join 78 2 2 (join 78 1 1 threshold_14_78 threshold_14_79) (join 80 1 1 threshold_14_80 threshold_14_81)))) (join 82 8 9 (join 82 4 4 (join 82 2 2 (join 82 1 1 threshold_14_82 threshold_14_83) (join 84 1 1 threshold_14_84 threshold_14_85)) (join 86 2 2 (join 86 1 1 threshold_14_86 threshold_14_87) (join 88 1 1 threshold_14_88 threshold_14_89))) (join 90 4 5 (join 90 2 2 (join 90 1 1 threshold_14_90 threshold_14_91) (join 92 1 1 threshold_14_92 threshold_14_93)) (join 94 2 3 (join 94 1 1 threshold_14_94 threshold_14_95) (join 96 1 2 threshold_14_96 (join 97 1 1 threshold_14_97 threshold_14_98)))))) (join 99 17 17 (join 99 8 9 (join 99 4 4 (join 99 2 2 (join 99 1 1 threshold_14_99 threshold_14_100) (join 101 1 1 threshold_14_101 threshold_14_102)) (join 103 2 2 (join 103 1 1 threshold_14_103 threshold_14_104) (join 105 1 1 threshold_14_105 threshold_14_106))) (join 107 4 5 (join 107 2 2 (join 107 1 1 threshold_14_107 threshold_14_108) (join 109 1 1 threshold_14_109 threshold_14_110)) (join 111 2 3 (join 111 1 1 threshold_14_111 threshold_14_112) (join 113 1 2 threshold_14_113 (join 114 1 1 threshold_14_114 threshold_14_115))))) (join 116 8 9 (join 116 4 4 (join 116 2 2 (join 116 1 1 threshold_14_116 threshold_14_117) (join 118 1 1 threshold_14_118 threshold_14_119)) (join 120 2 2 (join 120 1 1 threshold_14_120 threshold_14_121) (join 122 1 1 threshold_14_122 threshold_14_123))) (join 124 4 5 (join 124 2 2 (join 124 1 1 threshold_14_124 threshold_14_125) (join 126 1 1 threshold_14_126 threshold_14_127)) (join 128 2 3 (join 128 1 1 threshold_14_128 threshold_14_129) (join 130 1 2 threshold_14_130 (join 131 1 1 threshold_14_131 threshold_14_132))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_14_0 : ∀ i ∈ List.range 4, LedgerAt 14 (0+i) := by decide +kernel

theorem ledger_14_4 : ∀ i ∈ List.range 4, LedgerAt 14 (4+i) := by decide +kernel

theorem ledger_14_8 : ∀ i ∈ List.range 4, LedgerAt 14 (8+i) := by decide +kernel

theorem ledger_14_12 : ∀ i ∈ List.range 4, LedgerAt 14 (12+i) := by decide +kernel

theorem ledger_14_16 : ∀ i ∈ List.range 4, LedgerAt 14 (16+i) := by decide +kernel

theorem ledger_14_20 : ∀ i ∈ List.range 4, LedgerAt 14 (20+i) := by decide +kernel

theorem ledger_14_24 : ∀ i ∈ List.range 4, LedgerAt 14 (24+i) := by decide +kernel

theorem ledger_14_28 : ∀ i ∈ List.range 4, LedgerAt 14 (28+i) := by decide +kernel

theorem ledger_14_32 : ∀ i ∈ List.range 4, LedgerAt 14 (32+i) := by decide +kernel

theorem ledger_14_36 : ∀ i ∈ List.range 4, LedgerAt 14 (36+i) := by decide +kernel

theorem ledger_14_40 : ∀ i ∈ List.range 4, LedgerAt 14 (40+i) := by decide +kernel

theorem ledger_14_44 : ∀ i ∈ List.range 4, LedgerAt 14 (44+i) := by decide +kernel

theorem ledger_14_48 : ∀ i ∈ List.range 4, LedgerAt 14 (48+i) := by decide +kernel

theorem ledger_14_52 : ∀ i ∈ List.range 4, LedgerAt 14 (52+i) := by decide +kernel

theorem ledger_14_56 : ∀ i ∈ List.range 4, LedgerAt 14 (56+i) := by decide +kernel

theorem ledger_14_60 : ∀ i ∈ List.range 4, LedgerAt 14 (60+i) := by decide +kernel

theorem ledger_14_64 : ∀ i ∈ List.range 4, LedgerAt 14 (64+i) := by decide +kernel

theorem ledger_14_68 : ∀ i ∈ List.range 4, LedgerAt 14 (68+i) := by decide +kernel

theorem ledger_14_72 : ∀ i ∈ List.range 4, LedgerAt 14 (72+i) := by decide +kernel

theorem ledger_14_76 : ∀ i ∈ List.range 4, LedgerAt 14 (76+i) := by decide +kernel

theorem ledger_14_80 : ∀ i ∈ List.range 4, LedgerAt 14 (80+i) := by decide +kernel

theorem ledger_14_84 : ∀ i ∈ List.range 4, LedgerAt 14 (84+i) := by decide +kernel

theorem ledger_14_88 : ∀ i ∈ List.range 4, LedgerAt 14 (88+i) := by decide +kernel

theorem ledger_14_92 : ∀ i ∈ List.range 4, LedgerAt 14 (92+i) := by decide +kernel

theorem ledger_14_96 : ∀ i ∈ List.range 4, LedgerAt 14 (96+i) := by decide +kernel

theorem ledger_14_100 : ∀ i ∈ List.range 4, LedgerAt 14 (100+i) := by decide +kernel

theorem ledger_14_104 : ∀ i ∈ List.range 4, LedgerAt 14 (104+i) := by decide +kernel

theorem ledger_14_108 : ∀ i ∈ List.range 4, LedgerAt 14 (108+i) := by decide +kernel

theorem ledger_14_112 : ∀ i ∈ List.range 4, LedgerAt 14 (112+i) := by decide +kernel

theorem ledger_14_116 : ∀ i ∈ List.range 4, LedgerAt 14 (116+i) := by decide +kernel

theorem ledger_14_120 : ∀ i ∈ List.range 4, LedgerAt 14 (120+i) := by decide +kernel

theorem ledger_14_124 : ∀ i ∈ List.range 4, LedgerAt 14 (124+i) := by decide +kernel

theorem ledger_14_128 : ∀ i ∈ List.range 4, LedgerAt 14 (128+i) := by decide +kernel

theorem ledger_14_132 : ∀ i ∈ List.range 1, LedgerAt 14 (132+i) := by decide +kernel

theorem ledger_14 (v : ℕ) (hv : v ∈ List.range 133) : LedgerAt 14 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 14 v)
  have h := (join 0 68 65 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_14_0 ledger_14_4) (join 8 4 4 ledger_14_8 ledger_14_12)) (join 16 8 8 (join 16 4 4 ledger_14_16 ledger_14_20) (join 24 4 4 ledger_14_24 ledger_14_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_14_32 ledger_14_36) (join 40 4 4 ledger_14_40 ledger_14_44)) (join 48 8 12 (join 48 4 4 ledger_14_48 ledger_14_52) (join 56 4 8 ledger_14_56 (join 60 4 4 ledger_14_60 ledger_14_64))))) (join 68 32 33 (join 68 16 16 (join 68 8 8 (join 68 4 4 ledger_14_68 ledger_14_72) (join 76 4 4 ledger_14_76 ledger_14_80)) (join 84 8 8 (join 84 4 4 ledger_14_84 ledger_14_88) (join 92 4 4 ledger_14_92 ledger_14_96))) (join 100 16 17 (join 100 8 8 (join 100 4 4 ledger_14_100 ledger_14_104) (join 108 4 4 ledger_14_108 ledger_14_112)) (join 116 8 9 (join 116 4 4 ledger_14_116 ledger_14_120) (join 124 4 5 ledger_14_124 (join 128 4 1 ledger_14_128 ledger_14_132))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
