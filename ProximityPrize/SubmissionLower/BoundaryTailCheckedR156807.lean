import ProximityPrize.SubmissionLower.BoundaryTailCheckedR146807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_15_0 : ∀ i ∈ List.range 4, GeometryAt 15 (0+i) := by decide +kernel

theorem geometry_15_4 : ∀ i ∈ List.range 4, GeometryAt 15 (4+i) := by decide +kernel

theorem geometry_15_8 : ∀ i ∈ List.range 4, GeometryAt 15 (8+i) := by decide +kernel

theorem geometry_15_12 : ∀ i ∈ List.range 4, GeometryAt 15 (12+i) := by decide +kernel

theorem geometry_15_16 : ∀ i ∈ List.range 4, GeometryAt 15 (16+i) := by decide +kernel

theorem geometry_15_20 : ∀ i ∈ List.range 4, GeometryAt 15 (20+i) := by decide +kernel

theorem geometry_15_24 : ∀ i ∈ List.range 4, GeometryAt 15 (24+i) := by decide +kernel

theorem geometry_15_28 : ∀ i ∈ List.range 4, GeometryAt 15 (28+i) := by decide +kernel

theorem geometry_15_32 : ∀ i ∈ List.range 4, GeometryAt 15 (32+i) := by decide +kernel

theorem geometry_15_36 : ∀ i ∈ List.range 4, GeometryAt 15 (36+i) := by decide +kernel

theorem geometry_15_40 : ∀ i ∈ List.range 4, GeometryAt 15 (40+i) := by decide +kernel

theorem geometry_15_44 : ∀ i ∈ List.range 4, GeometryAt 15 (44+i) := by decide +kernel

theorem geometry_15_48 : ∀ i ∈ List.range 4, GeometryAt 15 (48+i) := by decide +kernel

theorem geometry_15_52 : ∀ i ∈ List.range 4, GeometryAt 15 (52+i) := by decide +kernel

theorem geometry_15_56 : ∀ i ∈ List.range 4, GeometryAt 15 (56+i) := by decide +kernel

theorem geometry_15_60 : ∀ i ∈ List.range 4, GeometryAt 15 (60+i) := by decide +kernel

theorem geometry_15_64 : ∀ i ∈ List.range 4, GeometryAt 15 (64+i) := by decide +kernel

theorem geometry_15_68 : ∀ i ∈ List.range 4, GeometryAt 15 (68+i) := by decide +kernel

theorem geometry_15_72 : ∀ i ∈ List.range 4, GeometryAt 15 (72+i) := by decide +kernel

theorem geometry_15_76 : ∀ i ∈ List.range 4, GeometryAt 15 (76+i) := by decide +kernel

theorem geometry_15_80 : ∀ i ∈ List.range 4, GeometryAt 15 (80+i) := by decide +kernel

theorem geometry_15_84 : ∀ i ∈ List.range 4, GeometryAt 15 (84+i) := by decide +kernel

theorem geometry_15_88 : ∀ i ∈ List.range 4, GeometryAt 15 (88+i) := by decide +kernel

theorem geometry_15_92 : ∀ i ∈ List.range 4, GeometryAt 15 (92+i) := by decide +kernel

theorem geometry_15_96 : ∀ i ∈ List.range 4, GeometryAt 15 (96+i) := by decide +kernel

theorem geometry_15_100 : ∀ i ∈ List.range 4, GeometryAt 15 (100+i) := by decide +kernel

theorem geometry_15_104 : ∀ i ∈ List.range 4, GeometryAt 15 (104+i) := by decide +kernel

theorem geometry_15_108 : ∀ i ∈ List.range 4, GeometryAt 15 (108+i) := by decide +kernel

theorem geometry_15_112 : ∀ i ∈ List.range 4, GeometryAt 15 (112+i) := by decide +kernel

theorem geometry_15_116 : ∀ i ∈ List.range 4, GeometryAt 15 (116+i) := by decide +kernel

theorem geometry_15_120 : ∀ i ∈ List.range 4, GeometryAt 15 (120+i) := by decide +kernel

theorem geometry_15_124 : ∀ i ∈ List.range 4, GeometryAt 15 (124+i) := by decide +kernel

theorem geometry_15_128 : ∀ i ∈ List.range 4, GeometryAt 15 (128+i) := by decide +kernel

theorem geometry_15 (v : ℕ) (hv : v ∈ List.range 132) : GeometryAt 15 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 15 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_15_0 geometry_15_4) (join 8 4 4 geometry_15_8 geometry_15_12)) (join 16 8 8 (join 16 4 4 geometry_15_16 geometry_15_20) (join 24 4 4 geometry_15_24 geometry_15_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 geometry_15_32 geometry_15_36) (join 40 4 4 geometry_15_40 geometry_15_44)) (join 48 8 8 (join 48 4 4 geometry_15_48 geometry_15_52) (join 56 4 4 geometry_15_56 geometry_15_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 geometry_15_64 geometry_15_68) (join 72 4 4 geometry_15_72 geometry_15_76)) (join 80 8 8 (join 80 4 4 geometry_15_80 geometry_15_84) (join 88 4 4 geometry_15_88 geometry_15_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 geometry_15_96 geometry_15_100) (join 104 4 4 geometry_15_104 geometry_15_108)) (join 112 8 12 (join 112 4 4 geometry_15_112 geometry_15_116) (join 120 4 8 geometry_15_120 (join 124 4 4 geometry_15_124 geometry_15_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_15_0 : ∀ i ∈ List.range 4, StrictAt 15 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (0+i)) 15 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_4 : ∀ i ∈ List.range 4, StrictAt 15 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (4+i)) 15 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_8 : ∀ i ∈ List.range 4, StrictAt 15 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (8+i)) 15 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_12 : ∀ i ∈ List.range 4, StrictAt 15 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (12+i)) 15 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_16 : ∀ i ∈ List.range 4, StrictAt 15 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (16+i)) 15 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_20 : ∀ i ∈ List.range 4, StrictAt 15 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (20+i)) 15 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_24 : ∀ i ∈ List.range 4, StrictAt 15 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (24+i)) 15 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_28 : ∀ i ∈ List.range 4, StrictAt 15 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (28+i)) 15 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_32 : ∀ i ∈ List.range 4, StrictAt 15 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (32+i)) 15 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_36 : ∀ i ∈ List.range 4, StrictAt 15 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (36+i)) 15 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_40 : ∀ i ∈ List.range 4, StrictAt 15 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (40+i)) 15 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_44 : ∀ i ∈ List.range 4, StrictAt 15 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (44+i)) 15 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_48 : ∀ i ∈ List.range 4, StrictAt 15 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (48+i)) 15 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_52 : ∀ i ∈ List.range 4, StrictAt 15 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (52+i)) 15 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_56 : ∀ i ∈ List.range 4, StrictAt 15 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (56+i)) 15 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_60 : ∀ i ∈ List.range 4, StrictAt 15 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (60+i)) 15 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_64 : ∀ i ∈ List.range 4, StrictAt 15 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (64+i)) 15 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_68 : ∀ i ∈ List.range 4, StrictAt 15 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (68+i)) 15 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_72 : ∀ i ∈ List.range 4, StrictAt 15 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (72+i)) 15 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_76 : ∀ i ∈ List.range 4, StrictAt 15 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (76+i)) 15 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_80 : ∀ i ∈ List.range 4, StrictAt 15 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (80+i)) 15 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_84 : ∀ i ∈ List.range 4, StrictAt 15 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (84+i)) 15 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_88 : ∀ i ∈ List.range 4, StrictAt 15 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (88+i)) 15 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_92 : ∀ i ∈ List.range 4, StrictAt 15 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (92+i)) 15 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_96 : ∀ i ∈ List.range 4, StrictAt 15 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (96+i)) 15 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_100 : ∀ i ∈ List.range 4, StrictAt 15 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (100+i)) 15 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_104 : ∀ i ∈ List.range 4, StrictAt 15 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (104+i)) 15 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_108 : ∀ i ∈ List.range 4, StrictAt 15 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (108+i)) 15 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_112 : ∀ i ∈ List.range 4, StrictAt 15 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (112+i)) 15 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_116 : ∀ i ∈ List.range 4, StrictAt 15 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (116+i)) 15 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_120 : ∀ i ∈ List.range 4, StrictAt 15 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (120+i)) 15 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_124 : ∀ i ∈ List.range 4, StrictAt 15 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (124+i)) 15 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15_128 : ∀ i ∈ List.range 4, StrictAt 15 (128+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 15 (128+i)) 15 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_15 (v : ℕ) (hv : v ∈ List.range 132) : StrictAt 15 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 15 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_15_0 strict_15_4) (join 8 4 4 strict_15_8 strict_15_12)) (join 16 8 8 (join 16 4 4 strict_15_16 strict_15_20) (join 24 4 4 strict_15_24 strict_15_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 strict_15_32 strict_15_36) (join 40 4 4 strict_15_40 strict_15_44)) (join 48 8 8 (join 48 4 4 strict_15_48 strict_15_52) (join 56 4 4 strict_15_56 strict_15_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 strict_15_64 strict_15_68) (join 72 4 4 strict_15_72 strict_15_76)) (join 80 8 8 (join 80 4 4 strict_15_80 strict_15_84) (join 88 4 4 strict_15_88 strict_15_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 strict_15_96 strict_15_100) (join 104 4 4 strict_15_104 strict_15_108)) (join 112 8 12 (join 112 4 4 strict_15_112 strict_15_116) (join 120 4 8 strict_15_120 (join 124 4 4 strict_15_124 strict_15_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_15_0 : ∀ i ∈ List.range 4, PhaseAt 15 (0+i) := by decide +kernel

theorem phase_15_4 : ∀ i ∈ List.range 4, PhaseAt 15 (4+i) := by decide +kernel

theorem phase_15_8 : ∀ i ∈ List.range 4, PhaseAt 15 (8+i) := by decide +kernel

theorem phase_15_12 : ∀ i ∈ List.range 4, PhaseAt 15 (12+i) := by decide +kernel

theorem phase_15_16 : ∀ i ∈ List.range 4, PhaseAt 15 (16+i) := by decide +kernel

theorem phase_15_20 : ∀ i ∈ List.range 4, PhaseAt 15 (20+i) := by decide +kernel

theorem phase_15_24 : ∀ i ∈ List.range 4, PhaseAt 15 (24+i) := by decide +kernel

theorem phase_15_28 : ∀ i ∈ List.range 4, PhaseAt 15 (28+i) := by decide +kernel

theorem phase_15_32 : ∀ i ∈ List.range 4, PhaseAt 15 (32+i) := by decide +kernel

theorem phase_15_36 : ∀ i ∈ List.range 4, PhaseAt 15 (36+i) := by decide +kernel

theorem phase_15_40 : ∀ i ∈ List.range 4, PhaseAt 15 (40+i) := by decide +kernel

theorem phase_15_44 : ∀ i ∈ List.range 4, PhaseAt 15 (44+i) := by decide +kernel

theorem phase_15_48 : ∀ i ∈ List.range 4, PhaseAt 15 (48+i) := by decide +kernel

theorem phase_15_52 : ∀ i ∈ List.range 4, PhaseAt 15 (52+i) := by decide +kernel

theorem phase_15_56 : ∀ i ∈ List.range 4, PhaseAt 15 (56+i) := by decide +kernel

theorem phase_15_60 : ∀ i ∈ List.range 4, PhaseAt 15 (60+i) := by decide +kernel

theorem phase_15_64 : ∀ i ∈ List.range 4, PhaseAt 15 (64+i) := by decide +kernel

theorem phase_15_68 : ∀ i ∈ List.range 4, PhaseAt 15 (68+i) := by decide +kernel

theorem phase_15_72 : ∀ i ∈ List.range 4, PhaseAt 15 (72+i) := by decide +kernel

theorem phase_15_76 : ∀ i ∈ List.range 4, PhaseAt 15 (76+i) := by decide +kernel

theorem phase_15_80 : ∀ i ∈ List.range 4, PhaseAt 15 (80+i) := by decide +kernel

theorem phase_15_84 : ∀ i ∈ List.range 4, PhaseAt 15 (84+i) := by decide +kernel

theorem phase_15_88 : ∀ i ∈ List.range 4, PhaseAt 15 (88+i) := by decide +kernel

theorem phase_15_92 : ∀ i ∈ List.range 4, PhaseAt 15 (92+i) := by decide +kernel

theorem phase_15_96 : ∀ i ∈ List.range 4, PhaseAt 15 (96+i) := by decide +kernel

theorem phase_15_100 : ∀ i ∈ List.range 4, PhaseAt 15 (100+i) := by decide +kernel

theorem phase_15_104 : ∀ i ∈ List.range 4, PhaseAt 15 (104+i) := by decide +kernel

theorem phase_15_108 : ∀ i ∈ List.range 4, PhaseAt 15 (108+i) := by decide +kernel

theorem phase_15_112 : ∀ i ∈ List.range 4, PhaseAt 15 (112+i) := by decide +kernel

theorem phase_15_116 : ∀ i ∈ List.range 4, PhaseAt 15 (116+i) := by decide +kernel

theorem phase_15_120 : ∀ i ∈ List.range 4, PhaseAt 15 (120+i) := by decide +kernel

theorem phase_15_124 : ∀ i ∈ List.range 4, PhaseAt 15 (124+i) := by decide +kernel

theorem phase_15_128 : ∀ i ∈ List.range 4, PhaseAt 15 (128+i) := by decide +kernel

theorem phase_15 (v : ℕ) (hv : v ∈ List.range 132) : PhaseAt 15 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 15 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_15_0 phase_15_4) (join 8 4 4 phase_15_8 phase_15_12)) (join 16 8 8 (join 16 4 4 phase_15_16 phase_15_20) (join 24 4 4 phase_15_24 phase_15_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_15_32 phase_15_36) (join 40 4 4 phase_15_40 phase_15_44)) (join 48 8 8 (join 48 4 4 phase_15_48 phase_15_52) (join 56 4 4 phase_15_56 phase_15_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_15_64 phase_15_68) (join 72 4 4 phase_15_72 phase_15_76)) (join 80 8 8 (join 80 4 4 phase_15_80 phase_15_84) (join 88 4 4 phase_15_88 phase_15_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 phase_15_96 phase_15_100) (join 104 4 4 phase_15_104 phase_15_108)) (join 112 8 12 (join 112 4 4 phase_15_112 phase_15_116) (join 120 4 8 phase_15_120 (join 124 4 4 phase_15_124 phase_15_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_15_0 : ∀ i ∈ List.range 1, ThresholdAt 15 (0+i) := by decide +kernel

theorem threshold_15_1 : ∀ i ∈ List.range 1, ThresholdAt 15 (1+i) := by decide +kernel

theorem threshold_15_2 : ∀ i ∈ List.range 1, ThresholdAt 15 (2+i) := by decide +kernel

theorem threshold_15_3 : ∀ i ∈ List.range 1, ThresholdAt 15 (3+i) := by decide +kernel

theorem threshold_15_4 : ∀ i ∈ List.range 1, ThresholdAt 15 (4+i) := by decide +kernel

theorem threshold_15_5 : ∀ i ∈ List.range 1, ThresholdAt 15 (5+i) := by decide +kernel

theorem threshold_15_6 : ∀ i ∈ List.range 1, ThresholdAt 15 (6+i) := by decide +kernel

theorem threshold_15_7 : ∀ i ∈ List.range 1, ThresholdAt 15 (7+i) := by decide +kernel

theorem threshold_15_8 : ∀ i ∈ List.range 1, ThresholdAt 15 (8+i) := by decide +kernel

theorem threshold_15_9 : ∀ i ∈ List.range 1, ThresholdAt 15 (9+i) := by decide +kernel

theorem threshold_15_10 : ∀ i ∈ List.range 1, ThresholdAt 15 (10+i) := by decide +kernel

theorem threshold_15_11 : ∀ i ∈ List.range 1, ThresholdAt 15 (11+i) := by decide +kernel

theorem threshold_15_12 : ∀ i ∈ List.range 1, ThresholdAt 15 (12+i) := by decide +kernel

theorem threshold_15_13 : ∀ i ∈ List.range 1, ThresholdAt 15 (13+i) := by decide +kernel

theorem threshold_15_14 : ∀ i ∈ List.range 1, ThresholdAt 15 (14+i) := by decide +kernel

theorem threshold_15_15 : ∀ i ∈ List.range 1, ThresholdAt 15 (15+i) := by decide +kernel

theorem threshold_15_16 : ∀ i ∈ List.range 1, ThresholdAt 15 (16+i) := by decide +kernel

theorem threshold_15_17 : ∀ i ∈ List.range 1, ThresholdAt 15 (17+i) := by decide +kernel

theorem threshold_15_18 : ∀ i ∈ List.range 1, ThresholdAt 15 (18+i) := by decide +kernel

theorem threshold_15_19 : ∀ i ∈ List.range 1, ThresholdAt 15 (19+i) := by decide +kernel

theorem threshold_15_20 : ∀ i ∈ List.range 1, ThresholdAt 15 (20+i) := by decide +kernel

theorem threshold_15_21 : ∀ i ∈ List.range 1, ThresholdAt 15 (21+i) := by decide +kernel

theorem threshold_15_22 : ∀ i ∈ List.range 1, ThresholdAt 15 (22+i) := by decide +kernel

theorem threshold_15_23 : ∀ i ∈ List.range 1, ThresholdAt 15 (23+i) := by decide +kernel

theorem threshold_15_24 : ∀ i ∈ List.range 1, ThresholdAt 15 (24+i) := by decide +kernel

theorem threshold_15_25 : ∀ i ∈ List.range 1, ThresholdAt 15 (25+i) := by decide +kernel

theorem threshold_15_26 : ∀ i ∈ List.range 1, ThresholdAt 15 (26+i) := by decide +kernel

theorem threshold_15_27 : ∀ i ∈ List.range 1, ThresholdAt 15 (27+i) := by decide +kernel

theorem threshold_15_28 : ∀ i ∈ List.range 1, ThresholdAt 15 (28+i) := by decide +kernel

theorem threshold_15_29 : ∀ i ∈ List.range 1, ThresholdAt 15 (29+i) := by decide +kernel

theorem threshold_15_30 : ∀ i ∈ List.range 1, ThresholdAt 15 (30+i) := by decide +kernel

theorem threshold_15_31 : ∀ i ∈ List.range 1, ThresholdAt 15 (31+i) := by decide +kernel

theorem threshold_15_32 : ∀ i ∈ List.range 1, ThresholdAt 15 (32+i) := by decide +kernel

theorem threshold_15_33 : ∀ i ∈ List.range 1, ThresholdAt 15 (33+i) := by decide +kernel

theorem threshold_15_34 : ∀ i ∈ List.range 1, ThresholdAt 15 (34+i) := by decide +kernel

theorem threshold_15_35 : ∀ i ∈ List.range 1, ThresholdAt 15 (35+i) := by decide +kernel

theorem threshold_15_36 : ∀ i ∈ List.range 1, ThresholdAt 15 (36+i) := by decide +kernel

theorem threshold_15_37 : ∀ i ∈ List.range 1, ThresholdAt 15 (37+i) := by decide +kernel

theorem threshold_15_38 : ∀ i ∈ List.range 1, ThresholdAt 15 (38+i) := by decide +kernel

theorem threshold_15_39 : ∀ i ∈ List.range 1, ThresholdAt 15 (39+i) := by decide +kernel

theorem threshold_15_40 : ∀ i ∈ List.range 1, ThresholdAt 15 (40+i) := by decide +kernel

theorem threshold_15_41 : ∀ i ∈ List.range 1, ThresholdAt 15 (41+i) := by decide +kernel

theorem threshold_15_42 : ∀ i ∈ List.range 1, ThresholdAt 15 (42+i) := by decide +kernel

theorem threshold_15_43 : ∀ i ∈ List.range 1, ThresholdAt 15 (43+i) := by decide +kernel

theorem threshold_15_44 : ∀ i ∈ List.range 1, ThresholdAt 15 (44+i) := by decide +kernel

theorem threshold_15_45 : ∀ i ∈ List.range 1, ThresholdAt 15 (45+i) := by decide +kernel

theorem threshold_15_46 : ∀ i ∈ List.range 1, ThresholdAt 15 (46+i) := by decide +kernel

theorem threshold_15_47 : ∀ i ∈ List.range 1, ThresholdAt 15 (47+i) := by decide +kernel

theorem threshold_15_48 : ∀ i ∈ List.range 1, ThresholdAt 15 (48+i) := by decide +kernel

theorem threshold_15_49 : ∀ i ∈ List.range 1, ThresholdAt 15 (49+i) := by decide +kernel

theorem threshold_15_50 : ∀ i ∈ List.range 1, ThresholdAt 15 (50+i) := by decide +kernel

theorem threshold_15_51 : ∀ i ∈ List.range 1, ThresholdAt 15 (51+i) := by decide +kernel

theorem threshold_15_52 : ∀ i ∈ List.range 1, ThresholdAt 15 (52+i) := by decide +kernel

theorem threshold_15_53 : ∀ i ∈ List.range 1, ThresholdAt 15 (53+i) := by decide +kernel

theorem threshold_15_54 : ∀ i ∈ List.range 1, ThresholdAt 15 (54+i) := by decide +kernel

theorem threshold_15_55 : ∀ i ∈ List.range 1, ThresholdAt 15 (55+i) := by decide +kernel

theorem threshold_15_56 : ∀ i ∈ List.range 1, ThresholdAt 15 (56+i) := by decide +kernel

theorem threshold_15_57 : ∀ i ∈ List.range 1, ThresholdAt 15 (57+i) := by decide +kernel

theorem threshold_15_58 : ∀ i ∈ List.range 1, ThresholdAt 15 (58+i) := by decide +kernel

theorem threshold_15_59 : ∀ i ∈ List.range 1, ThresholdAt 15 (59+i) := by decide +kernel

theorem threshold_15_60 : ∀ i ∈ List.range 1, ThresholdAt 15 (60+i) := by decide +kernel

theorem threshold_15_61 : ∀ i ∈ List.range 1, ThresholdAt 15 (61+i) := by decide +kernel

theorem threshold_15_62 : ∀ i ∈ List.range 1, ThresholdAt 15 (62+i) := by decide +kernel

theorem threshold_15_63 : ∀ i ∈ List.range 1, ThresholdAt 15 (63+i) := by decide +kernel

theorem threshold_15_64 : ∀ i ∈ List.range 1, ThresholdAt 15 (64+i) := by decide +kernel

theorem threshold_15_65 : ∀ i ∈ List.range 1, ThresholdAt 15 (65+i) := by decide +kernel

theorem threshold_15_66 : ∀ i ∈ List.range 1, ThresholdAt 15 (66+i) := by decide +kernel

theorem threshold_15_67 : ∀ i ∈ List.range 1, ThresholdAt 15 (67+i) := by decide +kernel

theorem threshold_15_68 : ∀ i ∈ List.range 1, ThresholdAt 15 (68+i) := by decide +kernel

theorem threshold_15_69 : ∀ i ∈ List.range 1, ThresholdAt 15 (69+i) := by decide +kernel

theorem threshold_15_70 : ∀ i ∈ List.range 1, ThresholdAt 15 (70+i) := by decide +kernel

theorem threshold_15_71 : ∀ i ∈ List.range 1, ThresholdAt 15 (71+i) := by decide +kernel

theorem threshold_15_72 : ∀ i ∈ List.range 1, ThresholdAt 15 (72+i) := by decide +kernel

theorem threshold_15_73 : ∀ i ∈ List.range 1, ThresholdAt 15 (73+i) := by decide +kernel

theorem threshold_15_74 : ∀ i ∈ List.range 1, ThresholdAt 15 (74+i) := by decide +kernel

theorem threshold_15_75 : ∀ i ∈ List.range 1, ThresholdAt 15 (75+i) := by decide +kernel

theorem threshold_15_76 : ∀ i ∈ List.range 1, ThresholdAt 15 (76+i) := by decide +kernel

theorem threshold_15_77 : ∀ i ∈ List.range 1, ThresholdAt 15 (77+i) := by decide +kernel

theorem threshold_15_78 : ∀ i ∈ List.range 1, ThresholdAt 15 (78+i) := by decide +kernel

theorem threshold_15_79 : ∀ i ∈ List.range 1, ThresholdAt 15 (79+i) := by decide +kernel

theorem threshold_15_80 : ∀ i ∈ List.range 1, ThresholdAt 15 (80+i) := by decide +kernel

theorem threshold_15_81 : ∀ i ∈ List.range 1, ThresholdAt 15 (81+i) := by decide +kernel

theorem threshold_15_82 : ∀ i ∈ List.range 1, ThresholdAt 15 (82+i) := by decide +kernel

theorem threshold_15_83 : ∀ i ∈ List.range 1, ThresholdAt 15 (83+i) := by decide +kernel

theorem threshold_15_84 : ∀ i ∈ List.range 1, ThresholdAt 15 (84+i) := by decide +kernel

theorem threshold_15_85 : ∀ i ∈ List.range 1, ThresholdAt 15 (85+i) := by decide +kernel

theorem threshold_15_86 : ∀ i ∈ List.range 1, ThresholdAt 15 (86+i) := by decide +kernel

theorem threshold_15_87 : ∀ i ∈ List.range 1, ThresholdAt 15 (87+i) := by decide +kernel

theorem threshold_15_88 : ∀ i ∈ List.range 1, ThresholdAt 15 (88+i) := by decide +kernel

theorem threshold_15_89 : ∀ i ∈ List.range 1, ThresholdAt 15 (89+i) := by decide +kernel

theorem threshold_15_90 : ∀ i ∈ List.range 1, ThresholdAt 15 (90+i) := by decide +kernel

theorem threshold_15_91 : ∀ i ∈ List.range 1, ThresholdAt 15 (91+i) := by decide +kernel

theorem threshold_15_92 : ∀ i ∈ List.range 1, ThresholdAt 15 (92+i) := by decide +kernel

theorem threshold_15_93 : ∀ i ∈ List.range 1, ThresholdAt 15 (93+i) := by decide +kernel

theorem threshold_15_94 : ∀ i ∈ List.range 1, ThresholdAt 15 (94+i) := by decide +kernel

theorem threshold_15_95 : ∀ i ∈ List.range 1, ThresholdAt 15 (95+i) := by decide +kernel

theorem threshold_15_96 : ∀ i ∈ List.range 1, ThresholdAt 15 (96+i) := by decide +kernel

theorem threshold_15_97 : ∀ i ∈ List.range 1, ThresholdAt 15 (97+i) := by decide +kernel

theorem threshold_15_98 : ∀ i ∈ List.range 1, ThresholdAt 15 (98+i) := by decide +kernel

theorem threshold_15_99 : ∀ i ∈ List.range 1, ThresholdAt 15 (99+i) := by decide +kernel

theorem threshold_15_100 : ∀ i ∈ List.range 1, ThresholdAt 15 (100+i) := by decide +kernel

theorem threshold_15_101 : ∀ i ∈ List.range 1, ThresholdAt 15 (101+i) := by decide +kernel

theorem threshold_15_102 : ∀ i ∈ List.range 1, ThresholdAt 15 (102+i) := by decide +kernel

theorem threshold_15_103 : ∀ i ∈ List.range 1, ThresholdAt 15 (103+i) := by decide +kernel

theorem threshold_15_104 : ∀ i ∈ List.range 1, ThresholdAt 15 (104+i) := by decide +kernel

theorem threshold_15_105 : ∀ i ∈ List.range 1, ThresholdAt 15 (105+i) := by decide +kernel

theorem threshold_15_106 : ∀ i ∈ List.range 1, ThresholdAt 15 (106+i) := by decide +kernel

theorem threshold_15_107 : ∀ i ∈ List.range 1, ThresholdAt 15 (107+i) := by decide +kernel

theorem threshold_15_108 : ∀ i ∈ List.range 1, ThresholdAt 15 (108+i) := by decide +kernel

theorem threshold_15_109 : ∀ i ∈ List.range 1, ThresholdAt 15 (109+i) := by decide +kernel

theorem threshold_15_110 : ∀ i ∈ List.range 1, ThresholdAt 15 (110+i) := by decide +kernel

theorem threshold_15_111 : ∀ i ∈ List.range 1, ThresholdAt 15 (111+i) := by decide +kernel

theorem threshold_15_112 : ∀ i ∈ List.range 1, ThresholdAt 15 (112+i) := by decide +kernel

theorem threshold_15_113 : ∀ i ∈ List.range 1, ThresholdAt 15 (113+i) := by decide +kernel

theorem threshold_15_114 : ∀ i ∈ List.range 1, ThresholdAt 15 (114+i) := by decide +kernel

theorem threshold_15_115 : ∀ i ∈ List.range 1, ThresholdAt 15 (115+i) := by decide +kernel

theorem threshold_15_116 : ∀ i ∈ List.range 1, ThresholdAt 15 (116+i) := by decide +kernel

theorem threshold_15_117 : ∀ i ∈ List.range 1, ThresholdAt 15 (117+i) := by decide +kernel

theorem threshold_15_118 : ∀ i ∈ List.range 1, ThresholdAt 15 (118+i) := by decide +kernel

theorem threshold_15_119 : ∀ i ∈ List.range 1, ThresholdAt 15 (119+i) := by decide +kernel

theorem threshold_15_120 : ∀ i ∈ List.range 1, ThresholdAt 15 (120+i) := by decide +kernel

theorem threshold_15_121 : ∀ i ∈ List.range 1, ThresholdAt 15 (121+i) := by decide +kernel

theorem threshold_15_122 : ∀ i ∈ List.range 1, ThresholdAt 15 (122+i) := by decide +kernel

theorem threshold_15_123 : ∀ i ∈ List.range 1, ThresholdAt 15 (123+i) := by decide +kernel

theorem threshold_15_124 : ∀ i ∈ List.range 1, ThresholdAt 15 (124+i) := by decide +kernel

theorem threshold_15_125 : ∀ i ∈ List.range 1, ThresholdAt 15 (125+i) := by decide +kernel

theorem threshold_15_126 : ∀ i ∈ List.range 1, ThresholdAt 15 (126+i) := by decide +kernel

theorem threshold_15_127 : ∀ i ∈ List.range 1, ThresholdAt 15 (127+i) := by decide +kernel

theorem threshold_15_128 : ∀ i ∈ List.range 1, ThresholdAt 15 (128+i) := by decide +kernel

theorem threshold_15_129 : ∀ i ∈ List.range 1, ThresholdAt 15 (129+i) := by decide +kernel

theorem threshold_15_130 : ∀ i ∈ List.range 1, ThresholdAt 15 (130+i) := by decide +kernel

theorem threshold_15_131 : ∀ i ∈ List.range 1, ThresholdAt 15 (131+i) := by decide +kernel

theorem threshold_15 (v : ℕ) (hv : v ∈ List.range 132) : ThresholdAt 15 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 15 v)
  have h := (join 0 66 66 (join 0 33 33 (join 0 16 17 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_15_0 threshold_15_1) (join 2 1 1 threshold_15_2 threshold_15_3)) (join 4 2 2 (join 4 1 1 threshold_15_4 threshold_15_5) (join 6 1 1 threshold_15_6 threshold_15_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_15_8 threshold_15_9) (join 10 1 1 threshold_15_10 threshold_15_11)) (join 12 2 2 (join 12 1 1 threshold_15_12 threshold_15_13) (join 14 1 1 threshold_15_14 threshold_15_15)))) (join 16 8 9 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_15_16 threshold_15_17) (join 18 1 1 threshold_15_18 threshold_15_19)) (join 20 2 2 (join 20 1 1 threshold_15_20 threshold_15_21) (join 22 1 1 threshold_15_22 threshold_15_23))) (join 24 4 5 (join 24 2 2 (join 24 1 1 threshold_15_24 threshold_15_25) (join 26 1 1 threshold_15_26 threshold_15_27)) (join 28 2 3 (join 28 1 1 threshold_15_28 threshold_15_29) (join 30 1 2 threshold_15_30 (join 31 1 1 threshold_15_31 threshold_15_32)))))) (join 33 16 17 (join 33 8 8 (join 33 4 4 (join 33 2 2 (join 33 1 1 threshold_15_33 threshold_15_34) (join 35 1 1 threshold_15_35 threshold_15_36)) (join 37 2 2 (join 37 1 1 threshold_15_37 threshold_15_38) (join 39 1 1 threshold_15_39 threshold_15_40))) (join 41 4 4 (join 41 2 2 (join 41 1 1 threshold_15_41 threshold_15_42) (join 43 1 1 threshold_15_43 threshold_15_44)) (join 45 2 2 (join 45 1 1 threshold_15_45 threshold_15_46) (join 47 1 1 threshold_15_47 threshold_15_48)))) (join 49 8 9 (join 49 4 4 (join 49 2 2 (join 49 1 1 threshold_15_49 threshold_15_50) (join 51 1 1 threshold_15_51 threshold_15_52)) (join 53 2 2 (join 53 1 1 threshold_15_53 threshold_15_54) (join 55 1 1 threshold_15_55 threshold_15_56))) (join 57 4 5 (join 57 2 2 (join 57 1 1 threshold_15_57 threshold_15_58) (join 59 1 1 threshold_15_59 threshold_15_60)) (join 61 2 3 (join 61 1 1 threshold_15_61 threshold_15_62) (join 63 1 2 threshold_15_63 (join 64 1 1 threshold_15_64 threshold_15_65))))))) (join 66 33 33 (join 66 16 17 (join 66 8 8 (join 66 4 4 (join 66 2 2 (join 66 1 1 threshold_15_66 threshold_15_67) (join 68 1 1 threshold_15_68 threshold_15_69)) (join 70 2 2 (join 70 1 1 threshold_15_70 threshold_15_71) (join 72 1 1 threshold_15_72 threshold_15_73))) (join 74 4 4 (join 74 2 2 (join 74 1 1 threshold_15_74 threshold_15_75) (join 76 1 1 threshold_15_76 threshold_15_77)) (join 78 2 2 (join 78 1 1 threshold_15_78 threshold_15_79) (join 80 1 1 threshold_15_80 threshold_15_81)))) (join 82 8 9 (join 82 4 4 (join 82 2 2 (join 82 1 1 threshold_15_82 threshold_15_83) (join 84 1 1 threshold_15_84 threshold_15_85)) (join 86 2 2 (join 86 1 1 threshold_15_86 threshold_15_87) (join 88 1 1 threshold_15_88 threshold_15_89))) (join 90 4 5 (join 90 2 2 (join 90 1 1 threshold_15_90 threshold_15_91) (join 92 1 1 threshold_15_92 threshold_15_93)) (join 94 2 3 (join 94 1 1 threshold_15_94 threshold_15_95) (join 96 1 2 threshold_15_96 (join 97 1 1 threshold_15_97 threshold_15_98)))))) (join 99 16 17 (join 99 8 8 (join 99 4 4 (join 99 2 2 (join 99 1 1 threshold_15_99 threshold_15_100) (join 101 1 1 threshold_15_101 threshold_15_102)) (join 103 2 2 (join 103 1 1 threshold_15_103 threshold_15_104) (join 105 1 1 threshold_15_105 threshold_15_106))) (join 107 4 4 (join 107 2 2 (join 107 1 1 threshold_15_107 threshold_15_108) (join 109 1 1 threshold_15_109 threshold_15_110)) (join 111 2 2 (join 111 1 1 threshold_15_111 threshold_15_112) (join 113 1 1 threshold_15_113 threshold_15_114)))) (join 115 8 9 (join 115 4 4 (join 115 2 2 (join 115 1 1 threshold_15_115 threshold_15_116) (join 117 1 1 threshold_15_117 threshold_15_118)) (join 119 2 2 (join 119 1 1 threshold_15_119 threshold_15_120) (join 121 1 1 threshold_15_121 threshold_15_122))) (join 123 4 5 (join 123 2 2 (join 123 1 1 threshold_15_123 threshold_15_124) (join 125 1 1 threshold_15_125 threshold_15_126)) (join 127 2 3 (join 127 1 1 threshold_15_127 threshold_15_128) (join 129 1 2 threshold_15_129 (join 130 1 1 threshold_15_130 threshold_15_131))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_15_0 : ∀ i ∈ List.range 4, LedgerAt 15 (0+i) := by decide +kernel

theorem ledger_15_4 : ∀ i ∈ List.range 4, LedgerAt 15 (4+i) := by decide +kernel

theorem ledger_15_8 : ∀ i ∈ List.range 4, LedgerAt 15 (8+i) := by decide +kernel

theorem ledger_15_12 : ∀ i ∈ List.range 4, LedgerAt 15 (12+i) := by decide +kernel

theorem ledger_15_16 : ∀ i ∈ List.range 4, LedgerAt 15 (16+i) := by decide +kernel

theorem ledger_15_20 : ∀ i ∈ List.range 4, LedgerAt 15 (20+i) := by decide +kernel

theorem ledger_15_24 : ∀ i ∈ List.range 4, LedgerAt 15 (24+i) := by decide +kernel

theorem ledger_15_28 : ∀ i ∈ List.range 4, LedgerAt 15 (28+i) := by decide +kernel

theorem ledger_15_32 : ∀ i ∈ List.range 4, LedgerAt 15 (32+i) := by decide +kernel

theorem ledger_15_36 : ∀ i ∈ List.range 4, LedgerAt 15 (36+i) := by decide +kernel

theorem ledger_15_40 : ∀ i ∈ List.range 4, LedgerAt 15 (40+i) := by decide +kernel

theorem ledger_15_44 : ∀ i ∈ List.range 4, LedgerAt 15 (44+i) := by decide +kernel

theorem ledger_15_48 : ∀ i ∈ List.range 4, LedgerAt 15 (48+i) := by decide +kernel

theorem ledger_15_52 : ∀ i ∈ List.range 4, LedgerAt 15 (52+i) := by decide +kernel

theorem ledger_15_56 : ∀ i ∈ List.range 4, LedgerAt 15 (56+i) := by decide +kernel

theorem ledger_15_60 : ∀ i ∈ List.range 4, LedgerAt 15 (60+i) := by decide +kernel

theorem ledger_15_64 : ∀ i ∈ List.range 4, LedgerAt 15 (64+i) := by decide +kernel

theorem ledger_15_68 : ∀ i ∈ List.range 4, LedgerAt 15 (68+i) := by decide +kernel

theorem ledger_15_72 : ∀ i ∈ List.range 4, LedgerAt 15 (72+i) := by decide +kernel

theorem ledger_15_76 : ∀ i ∈ List.range 4, LedgerAt 15 (76+i) := by decide +kernel

theorem ledger_15_80 : ∀ i ∈ List.range 4, LedgerAt 15 (80+i) := by decide +kernel

theorem ledger_15_84 : ∀ i ∈ List.range 4, LedgerAt 15 (84+i) := by decide +kernel

theorem ledger_15_88 : ∀ i ∈ List.range 4, LedgerAt 15 (88+i) := by decide +kernel

theorem ledger_15_92 : ∀ i ∈ List.range 4, LedgerAt 15 (92+i) := by decide +kernel

theorem ledger_15_96 : ∀ i ∈ List.range 4, LedgerAt 15 (96+i) := by decide +kernel

theorem ledger_15_100 : ∀ i ∈ List.range 4, LedgerAt 15 (100+i) := by decide +kernel

theorem ledger_15_104 : ∀ i ∈ List.range 4, LedgerAt 15 (104+i) := by decide +kernel

theorem ledger_15_108 : ∀ i ∈ List.range 4, LedgerAt 15 (108+i) := by decide +kernel

theorem ledger_15_112 : ∀ i ∈ List.range 4, LedgerAt 15 (112+i) := by decide +kernel

theorem ledger_15_116 : ∀ i ∈ List.range 4, LedgerAt 15 (116+i) := by decide +kernel

theorem ledger_15_120 : ∀ i ∈ List.range 4, LedgerAt 15 (120+i) := by decide +kernel

theorem ledger_15_124 : ∀ i ∈ List.range 4, LedgerAt 15 (124+i) := by decide +kernel

theorem ledger_15_128 : ∀ i ∈ List.range 4, LedgerAt 15 (128+i) := by decide +kernel

theorem ledger_15 (v : ℕ) (hv : v ∈ List.range 132) : LedgerAt 15 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 15 v)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_15_0 ledger_15_4) (join 8 4 4 ledger_15_8 ledger_15_12)) (join 16 8 8 (join 16 4 4 ledger_15_16 ledger_15_20) (join 24 4 4 ledger_15_24 ledger_15_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_15_32 ledger_15_36) (join 40 4 4 ledger_15_40 ledger_15_44)) (join 48 8 8 (join 48 4 4 ledger_15_48 ledger_15_52) (join 56 4 4 ledger_15_56 ledger_15_60)))) (join 64 32 36 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_15_64 ledger_15_68) (join 72 4 4 ledger_15_72 ledger_15_76)) (join 80 8 8 (join 80 4 4 ledger_15_80 ledger_15_84) (join 88 4 4 ledger_15_88 ledger_15_92))) (join 96 16 20 (join 96 8 8 (join 96 4 4 ledger_15_96 ledger_15_100) (join 104 4 4 ledger_15_104 ledger_15_108)) (join 112 8 12 (join 112 4 4 ledger_15_112 ledger_15_116) (join 120 4 8 ledger_15_120 (join 124 4 4 ledger_15_124 ledger_15_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
