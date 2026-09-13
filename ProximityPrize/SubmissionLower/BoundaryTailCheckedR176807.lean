import ProximityPrize.SubmissionLower.BoundaryTailCheckedR166807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_17_0 : ∀ i ∈ List.range 4, GeometryAt 17 (0+i) := by decide +kernel

theorem geometry_17_4 : ∀ i ∈ List.range 4, GeometryAt 17 (4+i) := by decide +kernel

theorem geometry_17_8 : ∀ i ∈ List.range 4, GeometryAt 17 (8+i) := by decide +kernel

theorem geometry_17_12 : ∀ i ∈ List.range 4, GeometryAt 17 (12+i) := by decide +kernel

theorem geometry_17_16 : ∀ i ∈ List.range 4, GeometryAt 17 (16+i) := by decide +kernel

theorem geometry_17_20 : ∀ i ∈ List.range 4, GeometryAt 17 (20+i) := by decide +kernel

theorem geometry_17_24 : ∀ i ∈ List.range 4, GeometryAt 17 (24+i) := by decide +kernel

theorem geometry_17_28 : ∀ i ∈ List.range 4, GeometryAt 17 (28+i) := by decide +kernel

theorem geometry_17_32 : ∀ i ∈ List.range 4, GeometryAt 17 (32+i) := by decide +kernel

theorem geometry_17_36 : ∀ i ∈ List.range 4, GeometryAt 17 (36+i) := by decide +kernel

theorem geometry_17_40 : ∀ i ∈ List.range 4, GeometryAt 17 (40+i) := by decide +kernel

theorem geometry_17_44 : ∀ i ∈ List.range 4, GeometryAt 17 (44+i) := by decide +kernel

theorem geometry_17_48 : ∀ i ∈ List.range 4, GeometryAt 17 (48+i) := by decide +kernel

theorem geometry_17_52 : ∀ i ∈ List.range 4, GeometryAt 17 (52+i) := by decide +kernel

theorem geometry_17_56 : ∀ i ∈ List.range 4, GeometryAt 17 (56+i) := by decide +kernel

theorem geometry_17_60 : ∀ i ∈ List.range 4, GeometryAt 17 (60+i) := by decide +kernel

theorem geometry_17_64 : ∀ i ∈ List.range 4, GeometryAt 17 (64+i) := by decide +kernel

theorem geometry_17_68 : ∀ i ∈ List.range 4, GeometryAt 17 (68+i) := by decide +kernel

theorem geometry_17_72 : ∀ i ∈ List.range 4, GeometryAt 17 (72+i) := by decide +kernel

theorem geometry_17_76 : ∀ i ∈ List.range 4, GeometryAt 17 (76+i) := by decide +kernel

theorem geometry_17_80 : ∀ i ∈ List.range 4, GeometryAt 17 (80+i) := by decide +kernel

theorem geometry_17_84 : ∀ i ∈ List.range 4, GeometryAt 17 (84+i) := by decide +kernel

theorem geometry_17_88 : ∀ i ∈ List.range 4, GeometryAt 17 (88+i) := by decide +kernel

theorem geometry_17_92 : ∀ i ∈ List.range 4, GeometryAt 17 (92+i) := by decide +kernel

theorem geometry_17_96 : ∀ i ∈ List.range 4, GeometryAt 17 (96+i) := by decide +kernel

theorem geometry_17_100 : ∀ i ∈ List.range 4, GeometryAt 17 (100+i) := by decide +kernel

theorem geometry_17_104 : ∀ i ∈ List.range 4, GeometryAt 17 (104+i) := by decide +kernel

theorem geometry_17_108 : ∀ i ∈ List.range 4, GeometryAt 17 (108+i) := by decide +kernel

theorem geometry_17_112 : ∀ i ∈ List.range 4, GeometryAt 17 (112+i) := by decide +kernel

theorem geometry_17_116 : ∀ i ∈ List.range 4, GeometryAt 17 (116+i) := by decide +kernel

theorem geometry_17_120 : ∀ i ∈ List.range 4, GeometryAt 17 (120+i) := by decide +kernel

theorem geometry_17_124 : ∀ i ∈ List.range 4, GeometryAt 17 (124+i) := by decide +kernel

theorem geometry_17_128 : ∀ i ∈ List.range 2, GeometryAt 17 (128+i) := by decide +kernel

theorem geometry_17 (v : ℕ) (hv : v ∈ List.range 130) : GeometryAt 17 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 17 v)
  have h := (join 0 64 66 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_17_0 geometry_17_4) (join 8 4 4 geometry_17_8 geometry_17_12)) (join 16 8 8 (join 16 4 4 geometry_17_16 geometry_17_20) (join 24 4 4 geometry_17_24 geometry_17_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 geometry_17_32 geometry_17_36) (join 40 4 4 geometry_17_40 geometry_17_44)) (join 48 8 8 (join 48 4 4 geometry_17_48 geometry_17_52) (join 56 4 4 geometry_17_56 geometry_17_60)))) (join 64 32 34 (join 64 16 16 (join 64 8 8 (join 64 4 4 geometry_17_64 geometry_17_68) (join 72 4 4 geometry_17_72 geometry_17_76)) (join 80 8 8 (join 80 4 4 geometry_17_80 geometry_17_84) (join 88 4 4 geometry_17_88 geometry_17_92))) (join 96 16 18 (join 96 8 8 (join 96 4 4 geometry_17_96 geometry_17_100) (join 104 4 4 geometry_17_104 geometry_17_108)) (join 112 8 10 (join 112 4 4 geometry_17_112 geometry_17_116) (join 120 4 6 geometry_17_120 (join 124 4 2 geometry_17_124 geometry_17_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_17_0 : ∀ i ∈ List.range 4, StrictAt 17 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (0+i)) 17 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_4 : ∀ i ∈ List.range 4, StrictAt 17 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (4+i)) 17 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_8 : ∀ i ∈ List.range 4, StrictAt 17 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (8+i)) 17 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_12 : ∀ i ∈ List.range 4, StrictAt 17 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (12+i)) 17 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_16 : ∀ i ∈ List.range 4, StrictAt 17 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (16+i)) 17 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_20 : ∀ i ∈ List.range 4, StrictAt 17 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (20+i)) 17 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_24 : ∀ i ∈ List.range 4, StrictAt 17 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (24+i)) 17 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_28 : ∀ i ∈ List.range 4, StrictAt 17 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (28+i)) 17 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_32 : ∀ i ∈ List.range 4, StrictAt 17 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (32+i)) 17 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_36 : ∀ i ∈ List.range 4, StrictAt 17 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (36+i)) 17 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_40 : ∀ i ∈ List.range 4, StrictAt 17 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (40+i)) 17 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_44 : ∀ i ∈ List.range 4, StrictAt 17 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (44+i)) 17 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_48 : ∀ i ∈ List.range 4, StrictAt 17 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (48+i)) 17 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_52 : ∀ i ∈ List.range 4, StrictAt 17 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (52+i)) 17 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_56 : ∀ i ∈ List.range 4, StrictAt 17 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (56+i)) 17 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_60 : ∀ i ∈ List.range 4, StrictAt 17 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (60+i)) 17 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_64 : ∀ i ∈ List.range 4, StrictAt 17 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (64+i)) 17 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_68 : ∀ i ∈ List.range 4, StrictAt 17 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (68+i)) 17 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_72 : ∀ i ∈ List.range 4, StrictAt 17 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (72+i)) 17 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_76 : ∀ i ∈ List.range 4, StrictAt 17 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (76+i)) 17 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_80 : ∀ i ∈ List.range 4, StrictAt 17 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (80+i)) 17 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_84 : ∀ i ∈ List.range 4, StrictAt 17 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (84+i)) 17 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_88 : ∀ i ∈ List.range 4, StrictAt 17 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (88+i)) 17 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_92 : ∀ i ∈ List.range 4, StrictAt 17 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (92+i)) 17 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_96 : ∀ i ∈ List.range 4, StrictAt 17 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (96+i)) 17 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_100 : ∀ i ∈ List.range 4, StrictAt 17 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (100+i)) 17 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_104 : ∀ i ∈ List.range 4, StrictAt 17 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (104+i)) 17 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_108 : ∀ i ∈ List.range 4, StrictAt 17 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (108+i)) 17 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_112 : ∀ i ∈ List.range 4, StrictAt 17 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (112+i)) 17 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_116 : ∀ i ∈ List.range 4, StrictAt 17 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (116+i)) 17 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_120 : ∀ i ∈ List.range 4, StrictAt 17 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (120+i)) 17 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_124 : ∀ i ∈ List.range 4, StrictAt 17 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (124+i)) 17 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17_128 : ∀ i ∈ List.range 2, StrictAt 17 (128+i) := by
  have h : ∀ i ∈ List.range 2, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 17 (128+i)) 17 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_17 (v : ℕ) (hv : v ∈ List.range 130) : StrictAt 17 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 17 v)
  have h := (join 0 64 66 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_17_0 strict_17_4) (join 8 4 4 strict_17_8 strict_17_12)) (join 16 8 8 (join 16 4 4 strict_17_16 strict_17_20) (join 24 4 4 strict_17_24 strict_17_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 strict_17_32 strict_17_36) (join 40 4 4 strict_17_40 strict_17_44)) (join 48 8 8 (join 48 4 4 strict_17_48 strict_17_52) (join 56 4 4 strict_17_56 strict_17_60)))) (join 64 32 34 (join 64 16 16 (join 64 8 8 (join 64 4 4 strict_17_64 strict_17_68) (join 72 4 4 strict_17_72 strict_17_76)) (join 80 8 8 (join 80 4 4 strict_17_80 strict_17_84) (join 88 4 4 strict_17_88 strict_17_92))) (join 96 16 18 (join 96 8 8 (join 96 4 4 strict_17_96 strict_17_100) (join 104 4 4 strict_17_104 strict_17_108)) (join 112 8 10 (join 112 4 4 strict_17_112 strict_17_116) (join 120 4 6 strict_17_120 (join 124 4 2 strict_17_124 strict_17_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_17_0 : ∀ i ∈ List.range 4, PhaseAt 17 (0+i) := by decide +kernel

theorem phase_17_4 : ∀ i ∈ List.range 4, PhaseAt 17 (4+i) := by decide +kernel

theorem phase_17_8 : ∀ i ∈ List.range 4, PhaseAt 17 (8+i) := by decide +kernel

theorem phase_17_12 : ∀ i ∈ List.range 4, PhaseAt 17 (12+i) := by decide +kernel

theorem phase_17_16 : ∀ i ∈ List.range 4, PhaseAt 17 (16+i) := by decide +kernel

theorem phase_17_20 : ∀ i ∈ List.range 4, PhaseAt 17 (20+i) := by decide +kernel

theorem phase_17_24 : ∀ i ∈ List.range 4, PhaseAt 17 (24+i) := by decide +kernel

theorem phase_17_28 : ∀ i ∈ List.range 4, PhaseAt 17 (28+i) := by decide +kernel

theorem phase_17_32 : ∀ i ∈ List.range 4, PhaseAt 17 (32+i) := by decide +kernel

theorem phase_17_36 : ∀ i ∈ List.range 4, PhaseAt 17 (36+i) := by decide +kernel

theorem phase_17_40 : ∀ i ∈ List.range 4, PhaseAt 17 (40+i) := by decide +kernel

theorem phase_17_44 : ∀ i ∈ List.range 4, PhaseAt 17 (44+i) := by decide +kernel

theorem phase_17_48 : ∀ i ∈ List.range 4, PhaseAt 17 (48+i) := by decide +kernel

theorem phase_17_52 : ∀ i ∈ List.range 4, PhaseAt 17 (52+i) := by decide +kernel

theorem phase_17_56 : ∀ i ∈ List.range 4, PhaseAt 17 (56+i) := by decide +kernel

theorem phase_17_60 : ∀ i ∈ List.range 4, PhaseAt 17 (60+i) := by decide +kernel

theorem phase_17_64 : ∀ i ∈ List.range 4, PhaseAt 17 (64+i) := by decide +kernel

theorem phase_17_68 : ∀ i ∈ List.range 4, PhaseAt 17 (68+i) := by decide +kernel

theorem phase_17_72 : ∀ i ∈ List.range 4, PhaseAt 17 (72+i) := by decide +kernel

theorem phase_17_76 : ∀ i ∈ List.range 4, PhaseAt 17 (76+i) := by decide +kernel

theorem phase_17_80 : ∀ i ∈ List.range 4, PhaseAt 17 (80+i) := by decide +kernel

theorem phase_17_84 : ∀ i ∈ List.range 4, PhaseAt 17 (84+i) := by decide +kernel

theorem phase_17_88 : ∀ i ∈ List.range 4, PhaseAt 17 (88+i) := by decide +kernel

theorem phase_17_92 : ∀ i ∈ List.range 4, PhaseAt 17 (92+i) := by decide +kernel

theorem phase_17_96 : ∀ i ∈ List.range 4, PhaseAt 17 (96+i) := by decide +kernel

theorem phase_17_100 : ∀ i ∈ List.range 4, PhaseAt 17 (100+i) := by decide +kernel

theorem phase_17_104 : ∀ i ∈ List.range 4, PhaseAt 17 (104+i) := by decide +kernel

theorem phase_17_108 : ∀ i ∈ List.range 4, PhaseAt 17 (108+i) := by decide +kernel

theorem phase_17_112 : ∀ i ∈ List.range 4, PhaseAt 17 (112+i) := by decide +kernel

theorem phase_17_116 : ∀ i ∈ List.range 4, PhaseAt 17 (116+i) := by decide +kernel

theorem phase_17_120 : ∀ i ∈ List.range 4, PhaseAt 17 (120+i) := by decide +kernel

theorem phase_17_124 : ∀ i ∈ List.range 4, PhaseAt 17 (124+i) := by decide +kernel

theorem phase_17_128 : ∀ i ∈ List.range 2, PhaseAt 17 (128+i) := by decide +kernel

theorem phase_17 (v : ℕ) (hv : v ∈ List.range 130) : PhaseAt 17 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 17 v)
  have h := (join 0 64 66 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_17_0 phase_17_4) (join 8 4 4 phase_17_8 phase_17_12)) (join 16 8 8 (join 16 4 4 phase_17_16 phase_17_20) (join 24 4 4 phase_17_24 phase_17_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_17_32 phase_17_36) (join 40 4 4 phase_17_40 phase_17_44)) (join 48 8 8 (join 48 4 4 phase_17_48 phase_17_52) (join 56 4 4 phase_17_56 phase_17_60)))) (join 64 32 34 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_17_64 phase_17_68) (join 72 4 4 phase_17_72 phase_17_76)) (join 80 8 8 (join 80 4 4 phase_17_80 phase_17_84) (join 88 4 4 phase_17_88 phase_17_92))) (join 96 16 18 (join 96 8 8 (join 96 4 4 phase_17_96 phase_17_100) (join 104 4 4 phase_17_104 phase_17_108)) (join 112 8 10 (join 112 4 4 phase_17_112 phase_17_116) (join 120 4 6 phase_17_120 (join 124 4 2 phase_17_124 phase_17_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_17_0 : ∀ i ∈ List.range 1, ThresholdAt 17 (0+i) := by decide +kernel

theorem threshold_17_1 : ∀ i ∈ List.range 1, ThresholdAt 17 (1+i) := by decide +kernel

theorem threshold_17_2 : ∀ i ∈ List.range 1, ThresholdAt 17 (2+i) := by decide +kernel

theorem threshold_17_3 : ∀ i ∈ List.range 1, ThresholdAt 17 (3+i) := by decide +kernel

theorem threshold_17_4 : ∀ i ∈ List.range 1, ThresholdAt 17 (4+i) := by decide +kernel

theorem threshold_17_5 : ∀ i ∈ List.range 1, ThresholdAt 17 (5+i) := by decide +kernel

theorem threshold_17_6 : ∀ i ∈ List.range 1, ThresholdAt 17 (6+i) := by decide +kernel

theorem threshold_17_7 : ∀ i ∈ List.range 1, ThresholdAt 17 (7+i) := by decide +kernel

theorem threshold_17_8 : ∀ i ∈ List.range 1, ThresholdAt 17 (8+i) := by decide +kernel

theorem threshold_17_9 : ∀ i ∈ List.range 1, ThresholdAt 17 (9+i) := by decide +kernel

theorem threshold_17_10 : ∀ i ∈ List.range 1, ThresholdAt 17 (10+i) := by decide +kernel

theorem threshold_17_11 : ∀ i ∈ List.range 1, ThresholdAt 17 (11+i) := by decide +kernel

theorem threshold_17_12 : ∀ i ∈ List.range 1, ThresholdAt 17 (12+i) := by decide +kernel

theorem threshold_17_13 : ∀ i ∈ List.range 1, ThresholdAt 17 (13+i) := by decide +kernel

theorem threshold_17_14 : ∀ i ∈ List.range 1, ThresholdAt 17 (14+i) := by decide +kernel

theorem threshold_17_15 : ∀ i ∈ List.range 1, ThresholdAt 17 (15+i) := by decide +kernel

theorem threshold_17_16 : ∀ i ∈ List.range 1, ThresholdAt 17 (16+i) := by decide +kernel

theorem threshold_17_17 : ∀ i ∈ List.range 1, ThresholdAt 17 (17+i) := by decide +kernel

theorem threshold_17_18 : ∀ i ∈ List.range 1, ThresholdAt 17 (18+i) := by decide +kernel

theorem threshold_17_19 : ∀ i ∈ List.range 1, ThresholdAt 17 (19+i) := by decide +kernel

theorem threshold_17_20 : ∀ i ∈ List.range 1, ThresholdAt 17 (20+i) := by decide +kernel

theorem threshold_17_21 : ∀ i ∈ List.range 1, ThresholdAt 17 (21+i) := by decide +kernel

theorem threshold_17_22 : ∀ i ∈ List.range 1, ThresholdAt 17 (22+i) := by decide +kernel

theorem threshold_17_23 : ∀ i ∈ List.range 1, ThresholdAt 17 (23+i) := by decide +kernel

theorem threshold_17_24 : ∀ i ∈ List.range 1, ThresholdAt 17 (24+i) := by decide +kernel

theorem threshold_17_25 : ∀ i ∈ List.range 1, ThresholdAt 17 (25+i) := by decide +kernel

theorem threshold_17_26 : ∀ i ∈ List.range 1, ThresholdAt 17 (26+i) := by decide +kernel

theorem threshold_17_27 : ∀ i ∈ List.range 1, ThresholdAt 17 (27+i) := by decide +kernel

theorem threshold_17_28 : ∀ i ∈ List.range 1, ThresholdAt 17 (28+i) := by decide +kernel

theorem threshold_17_29 : ∀ i ∈ List.range 1, ThresholdAt 17 (29+i) := by decide +kernel

theorem threshold_17_30 : ∀ i ∈ List.range 1, ThresholdAt 17 (30+i) := by decide +kernel

theorem threshold_17_31 : ∀ i ∈ List.range 1, ThresholdAt 17 (31+i) := by decide +kernel

theorem threshold_17_32 : ∀ i ∈ List.range 1, ThresholdAt 17 (32+i) := by decide +kernel

theorem threshold_17_33 : ∀ i ∈ List.range 1, ThresholdAt 17 (33+i) := by decide +kernel

theorem threshold_17_34 : ∀ i ∈ List.range 1, ThresholdAt 17 (34+i) := by decide +kernel

theorem threshold_17_35 : ∀ i ∈ List.range 1, ThresholdAt 17 (35+i) := by decide +kernel

theorem threshold_17_36 : ∀ i ∈ List.range 1, ThresholdAt 17 (36+i) := by decide +kernel

theorem threshold_17_37 : ∀ i ∈ List.range 1, ThresholdAt 17 (37+i) := by decide +kernel

theorem threshold_17_38 : ∀ i ∈ List.range 1, ThresholdAt 17 (38+i) := by decide +kernel

theorem threshold_17_39 : ∀ i ∈ List.range 1, ThresholdAt 17 (39+i) := by decide +kernel

theorem threshold_17_40 : ∀ i ∈ List.range 1, ThresholdAt 17 (40+i) := by decide +kernel

theorem threshold_17_41 : ∀ i ∈ List.range 1, ThresholdAt 17 (41+i) := by decide +kernel

theorem threshold_17_42 : ∀ i ∈ List.range 1, ThresholdAt 17 (42+i) := by decide +kernel

theorem threshold_17_43 : ∀ i ∈ List.range 1, ThresholdAt 17 (43+i) := by decide +kernel

theorem threshold_17_44 : ∀ i ∈ List.range 1, ThresholdAt 17 (44+i) := by decide +kernel

theorem threshold_17_45 : ∀ i ∈ List.range 1, ThresholdAt 17 (45+i) := by decide +kernel

theorem threshold_17_46 : ∀ i ∈ List.range 1, ThresholdAt 17 (46+i) := by decide +kernel

theorem threshold_17_47 : ∀ i ∈ List.range 1, ThresholdAt 17 (47+i) := by decide +kernel

theorem threshold_17_48 : ∀ i ∈ List.range 1, ThresholdAt 17 (48+i) := by decide +kernel

theorem threshold_17_49 : ∀ i ∈ List.range 1, ThresholdAt 17 (49+i) := by decide +kernel

theorem threshold_17_50 : ∀ i ∈ List.range 1, ThresholdAt 17 (50+i) := by decide +kernel

theorem threshold_17_51 : ∀ i ∈ List.range 1, ThresholdAt 17 (51+i) := by decide +kernel

theorem threshold_17_52 : ∀ i ∈ List.range 1, ThresholdAt 17 (52+i) := by decide +kernel

theorem threshold_17_53 : ∀ i ∈ List.range 1, ThresholdAt 17 (53+i) := by decide +kernel

theorem threshold_17_54 : ∀ i ∈ List.range 1, ThresholdAt 17 (54+i) := by decide +kernel

theorem threshold_17_55 : ∀ i ∈ List.range 1, ThresholdAt 17 (55+i) := by decide +kernel

theorem threshold_17_56 : ∀ i ∈ List.range 1, ThresholdAt 17 (56+i) := by decide +kernel

theorem threshold_17_57 : ∀ i ∈ List.range 1, ThresholdAt 17 (57+i) := by decide +kernel

theorem threshold_17_58 : ∀ i ∈ List.range 1, ThresholdAt 17 (58+i) := by decide +kernel

theorem threshold_17_59 : ∀ i ∈ List.range 1, ThresholdAt 17 (59+i) := by decide +kernel

theorem threshold_17_60 : ∀ i ∈ List.range 1, ThresholdAt 17 (60+i) := by decide +kernel

theorem threshold_17_61 : ∀ i ∈ List.range 1, ThresholdAt 17 (61+i) := by decide +kernel

theorem threshold_17_62 : ∀ i ∈ List.range 1, ThresholdAt 17 (62+i) := by decide +kernel

theorem threshold_17_63 : ∀ i ∈ List.range 1, ThresholdAt 17 (63+i) := by decide +kernel

theorem threshold_17_64 : ∀ i ∈ List.range 1, ThresholdAt 17 (64+i) := by decide +kernel

theorem threshold_17_65 : ∀ i ∈ List.range 1, ThresholdAt 17 (65+i) := by decide +kernel

theorem threshold_17_66 : ∀ i ∈ List.range 1, ThresholdAt 17 (66+i) := by decide +kernel

theorem threshold_17_67 : ∀ i ∈ List.range 1, ThresholdAt 17 (67+i) := by decide +kernel

theorem threshold_17_68 : ∀ i ∈ List.range 1, ThresholdAt 17 (68+i) := by decide +kernel

theorem threshold_17_69 : ∀ i ∈ List.range 1, ThresholdAt 17 (69+i) := by decide +kernel

theorem threshold_17_70 : ∀ i ∈ List.range 1, ThresholdAt 17 (70+i) := by decide +kernel

theorem threshold_17_71 : ∀ i ∈ List.range 1, ThresholdAt 17 (71+i) := by decide +kernel

theorem threshold_17_72 : ∀ i ∈ List.range 1, ThresholdAt 17 (72+i) := by decide +kernel

theorem threshold_17_73 : ∀ i ∈ List.range 1, ThresholdAt 17 (73+i) := by decide +kernel

theorem threshold_17_74 : ∀ i ∈ List.range 1, ThresholdAt 17 (74+i) := by decide +kernel

theorem threshold_17_75 : ∀ i ∈ List.range 1, ThresholdAt 17 (75+i) := by decide +kernel

theorem threshold_17_76 : ∀ i ∈ List.range 1, ThresholdAt 17 (76+i) := by decide +kernel

theorem threshold_17_77 : ∀ i ∈ List.range 1, ThresholdAt 17 (77+i) := by decide +kernel

theorem threshold_17_78 : ∀ i ∈ List.range 1, ThresholdAt 17 (78+i) := by decide +kernel

theorem threshold_17_79 : ∀ i ∈ List.range 1, ThresholdAt 17 (79+i) := by decide +kernel

theorem threshold_17_80 : ∀ i ∈ List.range 1, ThresholdAt 17 (80+i) := by decide +kernel

theorem threshold_17_81 : ∀ i ∈ List.range 1, ThresholdAt 17 (81+i) := by decide +kernel

theorem threshold_17_82 : ∀ i ∈ List.range 1, ThresholdAt 17 (82+i) := by decide +kernel

theorem threshold_17_83 : ∀ i ∈ List.range 1, ThresholdAt 17 (83+i) := by decide +kernel

theorem threshold_17_84 : ∀ i ∈ List.range 1, ThresholdAt 17 (84+i) := by decide +kernel

theorem threshold_17_85 : ∀ i ∈ List.range 1, ThresholdAt 17 (85+i) := by decide +kernel

theorem threshold_17_86 : ∀ i ∈ List.range 1, ThresholdAt 17 (86+i) := by decide +kernel

theorem threshold_17_87 : ∀ i ∈ List.range 1, ThresholdAt 17 (87+i) := by decide +kernel

theorem threshold_17_88 : ∀ i ∈ List.range 1, ThresholdAt 17 (88+i) := by decide +kernel

theorem threshold_17_89 : ∀ i ∈ List.range 1, ThresholdAt 17 (89+i) := by decide +kernel

theorem threshold_17_90 : ∀ i ∈ List.range 1, ThresholdAt 17 (90+i) := by decide +kernel

theorem threshold_17_91 : ∀ i ∈ List.range 1, ThresholdAt 17 (91+i) := by decide +kernel

theorem threshold_17_92 : ∀ i ∈ List.range 1, ThresholdAt 17 (92+i) := by decide +kernel

theorem threshold_17_93 : ∀ i ∈ List.range 1, ThresholdAt 17 (93+i) := by decide +kernel

theorem threshold_17_94 : ∀ i ∈ List.range 1, ThresholdAt 17 (94+i) := by decide +kernel

theorem threshold_17_95 : ∀ i ∈ List.range 1, ThresholdAt 17 (95+i) := by decide +kernel

theorem threshold_17_96 : ∀ i ∈ List.range 1, ThresholdAt 17 (96+i) := by decide +kernel

theorem threshold_17_97 : ∀ i ∈ List.range 1, ThresholdAt 17 (97+i) := by decide +kernel

theorem threshold_17_98 : ∀ i ∈ List.range 1, ThresholdAt 17 (98+i) := by decide +kernel

theorem threshold_17_99 : ∀ i ∈ List.range 1, ThresholdAt 17 (99+i) := by decide +kernel

theorem threshold_17_100 : ∀ i ∈ List.range 1, ThresholdAt 17 (100+i) := by decide +kernel

theorem threshold_17_101 : ∀ i ∈ List.range 1, ThresholdAt 17 (101+i) := by decide +kernel

theorem threshold_17_102 : ∀ i ∈ List.range 1, ThresholdAt 17 (102+i) := by decide +kernel

theorem threshold_17_103 : ∀ i ∈ List.range 1, ThresholdAt 17 (103+i) := by decide +kernel

theorem threshold_17_104 : ∀ i ∈ List.range 1, ThresholdAt 17 (104+i) := by decide +kernel

theorem threshold_17_105 : ∀ i ∈ List.range 1, ThresholdAt 17 (105+i) := by decide +kernel

theorem threshold_17_106 : ∀ i ∈ List.range 1, ThresholdAt 17 (106+i) := by decide +kernel

theorem threshold_17_107 : ∀ i ∈ List.range 1, ThresholdAt 17 (107+i) := by decide +kernel

theorem threshold_17_108 : ∀ i ∈ List.range 1, ThresholdAt 17 (108+i) := by decide +kernel

theorem threshold_17_109 : ∀ i ∈ List.range 1, ThresholdAt 17 (109+i) := by decide +kernel

theorem threshold_17_110 : ∀ i ∈ List.range 1, ThresholdAt 17 (110+i) := by decide +kernel

theorem threshold_17_111 : ∀ i ∈ List.range 1, ThresholdAt 17 (111+i) := by decide +kernel

theorem threshold_17_112 : ∀ i ∈ List.range 1, ThresholdAt 17 (112+i) := by decide +kernel

theorem threshold_17_113 : ∀ i ∈ List.range 1, ThresholdAt 17 (113+i) := by decide +kernel

theorem threshold_17_114 : ∀ i ∈ List.range 1, ThresholdAt 17 (114+i) := by decide +kernel

theorem threshold_17_115 : ∀ i ∈ List.range 1, ThresholdAt 17 (115+i) := by decide +kernel

theorem threshold_17_116 : ∀ i ∈ List.range 1, ThresholdAt 17 (116+i) := by decide +kernel

theorem threshold_17_117 : ∀ i ∈ List.range 1, ThresholdAt 17 (117+i) := by decide +kernel

theorem threshold_17_118 : ∀ i ∈ List.range 1, ThresholdAt 17 (118+i) := by decide +kernel

theorem threshold_17_119 : ∀ i ∈ List.range 1, ThresholdAt 17 (119+i) := by decide +kernel

theorem threshold_17_120 : ∀ i ∈ List.range 1, ThresholdAt 17 (120+i) := by decide +kernel

theorem threshold_17_121 : ∀ i ∈ List.range 1, ThresholdAt 17 (121+i) := by decide +kernel

theorem threshold_17_122 : ∀ i ∈ List.range 1, ThresholdAt 17 (122+i) := by decide +kernel

theorem threshold_17_123 : ∀ i ∈ List.range 1, ThresholdAt 17 (123+i) := by decide +kernel

theorem threshold_17_124 : ∀ i ∈ List.range 1, ThresholdAt 17 (124+i) := by decide +kernel

theorem threshold_17_125 : ∀ i ∈ List.range 1, ThresholdAt 17 (125+i) := by decide +kernel

theorem threshold_17_126 : ∀ i ∈ List.range 1, ThresholdAt 17 (126+i) := by decide +kernel

theorem threshold_17_127 : ∀ i ∈ List.range 1, ThresholdAt 17 (127+i) := by decide +kernel

theorem threshold_17_128 : ∀ i ∈ List.range 1, ThresholdAt 17 (128+i) := by decide +kernel

theorem threshold_17_129 : ∀ i ∈ List.range 1, ThresholdAt 17 (129+i) := by decide +kernel

theorem threshold_17 (v : ℕ) (hv : v ∈ List.range 130) : ThresholdAt 17 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 17 v)
  have h := (join 0 65 65 (join 0 32 33 (join 0 16 16 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_17_0 threshold_17_1) (join 2 1 1 threshold_17_2 threshold_17_3)) (join 4 2 2 (join 4 1 1 threshold_17_4 threshold_17_5) (join 6 1 1 threshold_17_6 threshold_17_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_17_8 threshold_17_9) (join 10 1 1 threshold_17_10 threshold_17_11)) (join 12 2 2 (join 12 1 1 threshold_17_12 threshold_17_13) (join 14 1 1 threshold_17_14 threshold_17_15)))) (join 16 8 8 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_17_16 threshold_17_17) (join 18 1 1 threshold_17_18 threshold_17_19)) (join 20 2 2 (join 20 1 1 threshold_17_20 threshold_17_21) (join 22 1 1 threshold_17_22 threshold_17_23))) (join 24 4 4 (join 24 2 2 (join 24 1 1 threshold_17_24 threshold_17_25) (join 26 1 1 threshold_17_26 threshold_17_27)) (join 28 2 2 (join 28 1 1 threshold_17_28 threshold_17_29) (join 30 1 1 threshold_17_30 threshold_17_31))))) (join 32 16 17 (join 32 8 8 (join 32 4 4 (join 32 2 2 (join 32 1 1 threshold_17_32 threshold_17_33) (join 34 1 1 threshold_17_34 threshold_17_35)) (join 36 2 2 (join 36 1 1 threshold_17_36 threshold_17_37) (join 38 1 1 threshold_17_38 threshold_17_39))) (join 40 4 4 (join 40 2 2 (join 40 1 1 threshold_17_40 threshold_17_41) (join 42 1 1 threshold_17_42 threshold_17_43)) (join 44 2 2 (join 44 1 1 threshold_17_44 threshold_17_45) (join 46 1 1 threshold_17_46 threshold_17_47)))) (join 48 8 9 (join 48 4 4 (join 48 2 2 (join 48 1 1 threshold_17_48 threshold_17_49) (join 50 1 1 threshold_17_50 threshold_17_51)) (join 52 2 2 (join 52 1 1 threshold_17_52 threshold_17_53) (join 54 1 1 threshold_17_54 threshold_17_55))) (join 56 4 5 (join 56 2 2 (join 56 1 1 threshold_17_56 threshold_17_57) (join 58 1 1 threshold_17_58 threshold_17_59)) (join 60 2 3 (join 60 1 1 threshold_17_60 threshold_17_61) (join 62 1 2 threshold_17_62 (join 63 1 1 threshold_17_63 threshold_17_64))))))) (join 65 32 33 (join 65 16 16 (join 65 8 8 (join 65 4 4 (join 65 2 2 (join 65 1 1 threshold_17_65 threshold_17_66) (join 67 1 1 threshold_17_67 threshold_17_68)) (join 69 2 2 (join 69 1 1 threshold_17_69 threshold_17_70) (join 71 1 1 threshold_17_71 threshold_17_72))) (join 73 4 4 (join 73 2 2 (join 73 1 1 threshold_17_73 threshold_17_74) (join 75 1 1 threshold_17_75 threshold_17_76)) (join 77 2 2 (join 77 1 1 threshold_17_77 threshold_17_78) (join 79 1 1 threshold_17_79 threshold_17_80)))) (join 81 8 8 (join 81 4 4 (join 81 2 2 (join 81 1 1 threshold_17_81 threshold_17_82) (join 83 1 1 threshold_17_83 threshold_17_84)) (join 85 2 2 (join 85 1 1 threshold_17_85 threshold_17_86) (join 87 1 1 threshold_17_87 threshold_17_88))) (join 89 4 4 (join 89 2 2 (join 89 1 1 threshold_17_89 threshold_17_90) (join 91 1 1 threshold_17_91 threshold_17_92)) (join 93 2 2 (join 93 1 1 threshold_17_93 threshold_17_94) (join 95 1 1 threshold_17_95 threshold_17_96))))) (join 97 16 17 (join 97 8 8 (join 97 4 4 (join 97 2 2 (join 97 1 1 threshold_17_97 threshold_17_98) (join 99 1 1 threshold_17_99 threshold_17_100)) (join 101 2 2 (join 101 1 1 threshold_17_101 threshold_17_102) (join 103 1 1 threshold_17_103 threshold_17_104))) (join 105 4 4 (join 105 2 2 (join 105 1 1 threshold_17_105 threshold_17_106) (join 107 1 1 threshold_17_107 threshold_17_108)) (join 109 2 2 (join 109 1 1 threshold_17_109 threshold_17_110) (join 111 1 1 threshold_17_111 threshold_17_112)))) (join 113 8 9 (join 113 4 4 (join 113 2 2 (join 113 1 1 threshold_17_113 threshold_17_114) (join 115 1 1 threshold_17_115 threshold_17_116)) (join 117 2 2 (join 117 1 1 threshold_17_117 threshold_17_118) (join 119 1 1 threshold_17_119 threshold_17_120))) (join 121 4 5 (join 121 2 2 (join 121 1 1 threshold_17_121 threshold_17_122) (join 123 1 1 threshold_17_123 threshold_17_124)) (join 125 2 3 (join 125 1 1 threshold_17_125 threshold_17_126) (join 127 1 2 threshold_17_127 (join 128 1 1 threshold_17_128 threshold_17_129))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_17_0 : ∀ i ∈ List.range 4, LedgerAt 17 (0+i) := by decide +kernel

theorem ledger_17_4 : ∀ i ∈ List.range 4, LedgerAt 17 (4+i) := by decide +kernel

theorem ledger_17_8 : ∀ i ∈ List.range 4, LedgerAt 17 (8+i) := by decide +kernel

theorem ledger_17_12 : ∀ i ∈ List.range 4, LedgerAt 17 (12+i) := by decide +kernel

theorem ledger_17_16 : ∀ i ∈ List.range 4, LedgerAt 17 (16+i) := by decide +kernel

theorem ledger_17_20 : ∀ i ∈ List.range 4, LedgerAt 17 (20+i) := by decide +kernel

theorem ledger_17_24 : ∀ i ∈ List.range 4, LedgerAt 17 (24+i) := by decide +kernel

theorem ledger_17_28 : ∀ i ∈ List.range 4, LedgerAt 17 (28+i) := by decide +kernel

theorem ledger_17_32 : ∀ i ∈ List.range 4, LedgerAt 17 (32+i) := by decide +kernel

theorem ledger_17_36 : ∀ i ∈ List.range 4, LedgerAt 17 (36+i) := by decide +kernel

theorem ledger_17_40 : ∀ i ∈ List.range 4, LedgerAt 17 (40+i) := by decide +kernel

theorem ledger_17_44 : ∀ i ∈ List.range 4, LedgerAt 17 (44+i) := by decide +kernel

theorem ledger_17_48 : ∀ i ∈ List.range 4, LedgerAt 17 (48+i) := by decide +kernel

theorem ledger_17_52 : ∀ i ∈ List.range 4, LedgerAt 17 (52+i) := by decide +kernel

theorem ledger_17_56 : ∀ i ∈ List.range 4, LedgerAt 17 (56+i) := by decide +kernel

theorem ledger_17_60 : ∀ i ∈ List.range 4, LedgerAt 17 (60+i) := by decide +kernel

theorem ledger_17_64 : ∀ i ∈ List.range 4, LedgerAt 17 (64+i) := by decide +kernel

theorem ledger_17_68 : ∀ i ∈ List.range 4, LedgerAt 17 (68+i) := by decide +kernel

theorem ledger_17_72 : ∀ i ∈ List.range 4, LedgerAt 17 (72+i) := by decide +kernel

theorem ledger_17_76 : ∀ i ∈ List.range 4, LedgerAt 17 (76+i) := by decide +kernel

theorem ledger_17_80 : ∀ i ∈ List.range 4, LedgerAt 17 (80+i) := by decide +kernel

theorem ledger_17_84 : ∀ i ∈ List.range 4, LedgerAt 17 (84+i) := by decide +kernel

theorem ledger_17_88 : ∀ i ∈ List.range 4, LedgerAt 17 (88+i) := by decide +kernel

theorem ledger_17_92 : ∀ i ∈ List.range 4, LedgerAt 17 (92+i) := by decide +kernel

theorem ledger_17_96 : ∀ i ∈ List.range 4, LedgerAt 17 (96+i) := by decide +kernel

theorem ledger_17_100 : ∀ i ∈ List.range 4, LedgerAt 17 (100+i) := by decide +kernel

theorem ledger_17_104 : ∀ i ∈ List.range 4, LedgerAt 17 (104+i) := by decide +kernel

theorem ledger_17_108 : ∀ i ∈ List.range 4, LedgerAt 17 (108+i) := by decide +kernel

theorem ledger_17_112 : ∀ i ∈ List.range 4, LedgerAt 17 (112+i) := by decide +kernel

theorem ledger_17_116 : ∀ i ∈ List.range 4, LedgerAt 17 (116+i) := by decide +kernel

theorem ledger_17_120 : ∀ i ∈ List.range 4, LedgerAt 17 (120+i) := by decide +kernel

theorem ledger_17_124 : ∀ i ∈ List.range 4, LedgerAt 17 (124+i) := by decide +kernel

theorem ledger_17_128 : ∀ i ∈ List.range 2, LedgerAt 17 (128+i) := by decide +kernel

theorem ledger_17 (v : ℕ) (hv : v ∈ List.range 130) : LedgerAt 17 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 17 v)
  have h := (join 0 64 66 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_17_0 ledger_17_4) (join 8 4 4 ledger_17_8 ledger_17_12)) (join 16 8 8 (join 16 4 4 ledger_17_16 ledger_17_20) (join 24 4 4 ledger_17_24 ledger_17_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_17_32 ledger_17_36) (join 40 4 4 ledger_17_40 ledger_17_44)) (join 48 8 8 (join 48 4 4 ledger_17_48 ledger_17_52) (join 56 4 4 ledger_17_56 ledger_17_60)))) (join 64 32 34 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_17_64 ledger_17_68) (join 72 4 4 ledger_17_72 ledger_17_76)) (join 80 8 8 (join 80 4 4 ledger_17_80 ledger_17_84) (join 88 4 4 ledger_17_88 ledger_17_92))) (join 96 16 18 (join 96 8 8 (join 96 4 4 ledger_17_96 ledger_17_100) (join 104 4 4 ledger_17_104 ledger_17_108)) (join 112 8 10 (join 112 4 4 ledger_17_112 ledger_17_116) (join 120 4 6 ledger_17_120 (join 124 4 2 ledger_17_124 ledger_17_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
