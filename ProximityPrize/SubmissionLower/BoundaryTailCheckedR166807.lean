import ProximityPrize.SubmissionLower.BoundaryTailCheckedR156807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_16_0 : ∀ i ∈ List.range 4, GeometryAt 16 (0+i) := by decide +kernel

theorem geometry_16_4 : ∀ i ∈ List.range 4, GeometryAt 16 (4+i) := by decide +kernel

theorem geometry_16_8 : ∀ i ∈ List.range 4, GeometryAt 16 (8+i) := by decide +kernel

theorem geometry_16_12 : ∀ i ∈ List.range 4, GeometryAt 16 (12+i) := by decide +kernel

theorem geometry_16_16 : ∀ i ∈ List.range 4, GeometryAt 16 (16+i) := by decide +kernel

theorem geometry_16_20 : ∀ i ∈ List.range 4, GeometryAt 16 (20+i) := by decide +kernel

theorem geometry_16_24 : ∀ i ∈ List.range 4, GeometryAt 16 (24+i) := by decide +kernel

theorem geometry_16_28 : ∀ i ∈ List.range 4, GeometryAt 16 (28+i) := by decide +kernel

theorem geometry_16_32 : ∀ i ∈ List.range 4, GeometryAt 16 (32+i) := by decide +kernel

theorem geometry_16_36 : ∀ i ∈ List.range 4, GeometryAt 16 (36+i) := by decide +kernel

theorem geometry_16_40 : ∀ i ∈ List.range 4, GeometryAt 16 (40+i) := by decide +kernel

theorem geometry_16_44 : ∀ i ∈ List.range 4, GeometryAt 16 (44+i) := by decide +kernel

theorem geometry_16_48 : ∀ i ∈ List.range 4, GeometryAt 16 (48+i) := by decide +kernel

theorem geometry_16_52 : ∀ i ∈ List.range 4, GeometryAt 16 (52+i) := by decide +kernel

theorem geometry_16_56 : ∀ i ∈ List.range 4, GeometryAt 16 (56+i) := by decide +kernel

theorem geometry_16_60 : ∀ i ∈ List.range 4, GeometryAt 16 (60+i) := by decide +kernel

theorem geometry_16_64 : ∀ i ∈ List.range 4, GeometryAt 16 (64+i) := by decide +kernel

theorem geometry_16_68 : ∀ i ∈ List.range 4, GeometryAt 16 (68+i) := by decide +kernel

theorem geometry_16_72 : ∀ i ∈ List.range 4, GeometryAt 16 (72+i) := by decide +kernel

theorem geometry_16_76 : ∀ i ∈ List.range 4, GeometryAt 16 (76+i) := by decide +kernel

theorem geometry_16_80 : ∀ i ∈ List.range 4, GeometryAt 16 (80+i) := by decide +kernel

theorem geometry_16_84 : ∀ i ∈ List.range 4, GeometryAt 16 (84+i) := by decide +kernel

theorem geometry_16_88 : ∀ i ∈ List.range 4, GeometryAt 16 (88+i) := by decide +kernel

theorem geometry_16_92 : ∀ i ∈ List.range 4, GeometryAt 16 (92+i) := by decide +kernel

theorem geometry_16_96 : ∀ i ∈ List.range 4, GeometryAt 16 (96+i) := by decide +kernel

theorem geometry_16_100 : ∀ i ∈ List.range 4, GeometryAt 16 (100+i) := by decide +kernel

theorem geometry_16_104 : ∀ i ∈ List.range 4, GeometryAt 16 (104+i) := by decide +kernel

theorem geometry_16_108 : ∀ i ∈ List.range 4, GeometryAt 16 (108+i) := by decide +kernel

theorem geometry_16_112 : ∀ i ∈ List.range 4, GeometryAt 16 (112+i) := by decide +kernel

theorem geometry_16_116 : ∀ i ∈ List.range 4, GeometryAt 16 (116+i) := by decide +kernel

theorem geometry_16_120 : ∀ i ∈ List.range 4, GeometryAt 16 (120+i) := by decide +kernel

theorem geometry_16_124 : ∀ i ∈ List.range 4, GeometryAt 16 (124+i) := by decide +kernel

theorem geometry_16_128 : ∀ i ∈ List.range 3, GeometryAt 16 (128+i) := by decide +kernel

theorem geometry_16 (v : ℕ) (hv : v ∈ List.range 131) : GeometryAt 16 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 16 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_16_0 geometry_16_4) (join 8 4 4 geometry_16_8 geometry_16_12)) (join 16 8 8 (join 16 4 4 geometry_16_16 geometry_16_20) (join 24 4 4 geometry_16_24 geometry_16_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 geometry_16_32 geometry_16_36) (join 40 4 4 geometry_16_40 geometry_16_44)) (join 48 8 8 (join 48 4 4 geometry_16_48 geometry_16_52) (join 56 4 4 geometry_16_56 geometry_16_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 geometry_16_64 geometry_16_68) (join 72 4 4 geometry_16_72 geometry_16_76)) (join 80 8 8 (join 80 4 4 geometry_16_80 geometry_16_84) (join 88 4 4 geometry_16_88 geometry_16_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 geometry_16_96 geometry_16_100) (join 104 4 4 geometry_16_104 geometry_16_108)) (join 112 8 11 (join 112 4 4 geometry_16_112 geometry_16_116) (join 120 4 7 geometry_16_120 (join 124 4 3 geometry_16_124 geometry_16_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_16_0 : ∀ i ∈ List.range 4, StrictAt 16 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (0+i)) 16 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_4 : ∀ i ∈ List.range 4, StrictAt 16 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (4+i)) 16 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_8 : ∀ i ∈ List.range 4, StrictAt 16 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (8+i)) 16 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_12 : ∀ i ∈ List.range 4, StrictAt 16 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (12+i)) 16 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_16 : ∀ i ∈ List.range 4, StrictAt 16 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (16+i)) 16 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_20 : ∀ i ∈ List.range 4, StrictAt 16 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (20+i)) 16 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_24 : ∀ i ∈ List.range 4, StrictAt 16 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (24+i)) 16 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_28 : ∀ i ∈ List.range 4, StrictAt 16 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (28+i)) 16 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_32 : ∀ i ∈ List.range 4, StrictAt 16 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (32+i)) 16 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_36 : ∀ i ∈ List.range 4, StrictAt 16 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (36+i)) 16 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_40 : ∀ i ∈ List.range 4, StrictAt 16 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (40+i)) 16 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_44 : ∀ i ∈ List.range 4, StrictAt 16 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (44+i)) 16 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_48 : ∀ i ∈ List.range 4, StrictAt 16 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (48+i)) 16 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_52 : ∀ i ∈ List.range 4, StrictAt 16 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (52+i)) 16 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_56 : ∀ i ∈ List.range 4, StrictAt 16 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (56+i)) 16 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_60 : ∀ i ∈ List.range 4, StrictAt 16 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (60+i)) 16 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_64 : ∀ i ∈ List.range 4, StrictAt 16 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (64+i)) 16 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_68 : ∀ i ∈ List.range 4, StrictAt 16 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (68+i)) 16 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_72 : ∀ i ∈ List.range 4, StrictAt 16 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (72+i)) 16 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_76 : ∀ i ∈ List.range 4, StrictAt 16 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (76+i)) 16 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_80 : ∀ i ∈ List.range 4, StrictAt 16 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (80+i)) 16 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_84 : ∀ i ∈ List.range 4, StrictAt 16 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (84+i)) 16 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_88 : ∀ i ∈ List.range 4, StrictAt 16 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (88+i)) 16 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_92 : ∀ i ∈ List.range 4, StrictAt 16 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (92+i)) 16 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_96 : ∀ i ∈ List.range 4, StrictAt 16 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (96+i)) 16 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_100 : ∀ i ∈ List.range 4, StrictAt 16 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (100+i)) 16 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_104 : ∀ i ∈ List.range 4, StrictAt 16 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (104+i)) 16 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_108 : ∀ i ∈ List.range 4, StrictAt 16 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (108+i)) 16 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_112 : ∀ i ∈ List.range 4, StrictAt 16 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (112+i)) 16 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_116 : ∀ i ∈ List.range 4, StrictAt 16 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (116+i)) 16 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_120 : ∀ i ∈ List.range 4, StrictAt 16 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (120+i)) 16 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_124 : ∀ i ∈ List.range 4, StrictAt 16 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (124+i)) 16 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16_128 : ∀ i ∈ List.range 3, StrictAt 16 (128+i) := by
  have h : ∀ i ∈ List.range 3, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 16 (128+i)) 16 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_16 (v : ℕ) (hv : v ∈ List.range 131) : StrictAt 16 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 16 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_16_0 strict_16_4) (join 8 4 4 strict_16_8 strict_16_12)) (join 16 8 8 (join 16 4 4 strict_16_16 strict_16_20) (join 24 4 4 strict_16_24 strict_16_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 strict_16_32 strict_16_36) (join 40 4 4 strict_16_40 strict_16_44)) (join 48 8 8 (join 48 4 4 strict_16_48 strict_16_52) (join 56 4 4 strict_16_56 strict_16_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 strict_16_64 strict_16_68) (join 72 4 4 strict_16_72 strict_16_76)) (join 80 8 8 (join 80 4 4 strict_16_80 strict_16_84) (join 88 4 4 strict_16_88 strict_16_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 strict_16_96 strict_16_100) (join 104 4 4 strict_16_104 strict_16_108)) (join 112 8 11 (join 112 4 4 strict_16_112 strict_16_116) (join 120 4 7 strict_16_120 (join 124 4 3 strict_16_124 strict_16_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_16_0 : ∀ i ∈ List.range 4, PhaseAt 16 (0+i) := by decide +kernel

theorem phase_16_4 : ∀ i ∈ List.range 4, PhaseAt 16 (4+i) := by decide +kernel

theorem phase_16_8 : ∀ i ∈ List.range 4, PhaseAt 16 (8+i) := by decide +kernel

theorem phase_16_12 : ∀ i ∈ List.range 4, PhaseAt 16 (12+i) := by decide +kernel

theorem phase_16_16 : ∀ i ∈ List.range 4, PhaseAt 16 (16+i) := by decide +kernel

theorem phase_16_20 : ∀ i ∈ List.range 4, PhaseAt 16 (20+i) := by decide +kernel

theorem phase_16_24 : ∀ i ∈ List.range 4, PhaseAt 16 (24+i) := by decide +kernel

theorem phase_16_28 : ∀ i ∈ List.range 4, PhaseAt 16 (28+i) := by decide +kernel

theorem phase_16_32 : ∀ i ∈ List.range 4, PhaseAt 16 (32+i) := by decide +kernel

theorem phase_16_36 : ∀ i ∈ List.range 4, PhaseAt 16 (36+i) := by decide +kernel

theorem phase_16_40 : ∀ i ∈ List.range 4, PhaseAt 16 (40+i) := by decide +kernel

theorem phase_16_44 : ∀ i ∈ List.range 4, PhaseAt 16 (44+i) := by decide +kernel

theorem phase_16_48 : ∀ i ∈ List.range 4, PhaseAt 16 (48+i) := by decide +kernel

theorem phase_16_52 : ∀ i ∈ List.range 4, PhaseAt 16 (52+i) := by decide +kernel

theorem phase_16_56 : ∀ i ∈ List.range 4, PhaseAt 16 (56+i) := by decide +kernel

theorem phase_16_60 : ∀ i ∈ List.range 4, PhaseAt 16 (60+i) := by decide +kernel

theorem phase_16_64 : ∀ i ∈ List.range 4, PhaseAt 16 (64+i) := by decide +kernel

theorem phase_16_68 : ∀ i ∈ List.range 4, PhaseAt 16 (68+i) := by decide +kernel

theorem phase_16_72 : ∀ i ∈ List.range 4, PhaseAt 16 (72+i) := by decide +kernel

theorem phase_16_76 : ∀ i ∈ List.range 4, PhaseAt 16 (76+i) := by decide +kernel

theorem phase_16_80 : ∀ i ∈ List.range 4, PhaseAt 16 (80+i) := by decide +kernel

theorem phase_16_84 : ∀ i ∈ List.range 4, PhaseAt 16 (84+i) := by decide +kernel

theorem phase_16_88 : ∀ i ∈ List.range 4, PhaseAt 16 (88+i) := by decide +kernel

theorem phase_16_92 : ∀ i ∈ List.range 4, PhaseAt 16 (92+i) := by decide +kernel

theorem phase_16_96 : ∀ i ∈ List.range 4, PhaseAt 16 (96+i) := by decide +kernel

theorem phase_16_100 : ∀ i ∈ List.range 4, PhaseAt 16 (100+i) := by decide +kernel

theorem phase_16_104 : ∀ i ∈ List.range 4, PhaseAt 16 (104+i) := by decide +kernel

theorem phase_16_108 : ∀ i ∈ List.range 4, PhaseAt 16 (108+i) := by decide +kernel

theorem phase_16_112 : ∀ i ∈ List.range 4, PhaseAt 16 (112+i) := by decide +kernel

theorem phase_16_116 : ∀ i ∈ List.range 4, PhaseAt 16 (116+i) := by decide +kernel

theorem phase_16_120 : ∀ i ∈ List.range 4, PhaseAt 16 (120+i) := by decide +kernel

theorem phase_16_124 : ∀ i ∈ List.range 4, PhaseAt 16 (124+i) := by decide +kernel

theorem phase_16_128 : ∀ i ∈ List.range 3, PhaseAt 16 (128+i) := by decide +kernel

theorem phase_16 (v : ℕ) (hv : v ∈ List.range 131) : PhaseAt 16 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 16 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_16_0 phase_16_4) (join 8 4 4 phase_16_8 phase_16_12)) (join 16 8 8 (join 16 4 4 phase_16_16 phase_16_20) (join 24 4 4 phase_16_24 phase_16_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_16_32 phase_16_36) (join 40 4 4 phase_16_40 phase_16_44)) (join 48 8 8 (join 48 4 4 phase_16_48 phase_16_52) (join 56 4 4 phase_16_56 phase_16_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_16_64 phase_16_68) (join 72 4 4 phase_16_72 phase_16_76)) (join 80 8 8 (join 80 4 4 phase_16_80 phase_16_84) (join 88 4 4 phase_16_88 phase_16_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 phase_16_96 phase_16_100) (join 104 4 4 phase_16_104 phase_16_108)) (join 112 8 11 (join 112 4 4 phase_16_112 phase_16_116) (join 120 4 7 phase_16_120 (join 124 4 3 phase_16_124 phase_16_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_16_0 : ∀ i ∈ List.range 1, ThresholdAt 16 (0+i) := by decide +kernel

theorem threshold_16_1 : ∀ i ∈ List.range 1, ThresholdAt 16 (1+i) := by decide +kernel

theorem threshold_16_2 : ∀ i ∈ List.range 1, ThresholdAt 16 (2+i) := by decide +kernel

theorem threshold_16_3 : ∀ i ∈ List.range 1, ThresholdAt 16 (3+i) := by decide +kernel

theorem threshold_16_4 : ∀ i ∈ List.range 1, ThresholdAt 16 (4+i) := by decide +kernel

theorem threshold_16_5 : ∀ i ∈ List.range 1, ThresholdAt 16 (5+i) := by decide +kernel

theorem threshold_16_6 : ∀ i ∈ List.range 1, ThresholdAt 16 (6+i) := by decide +kernel

theorem threshold_16_7 : ∀ i ∈ List.range 1, ThresholdAt 16 (7+i) := by decide +kernel

theorem threshold_16_8 : ∀ i ∈ List.range 1, ThresholdAt 16 (8+i) := by decide +kernel

theorem threshold_16_9 : ∀ i ∈ List.range 1, ThresholdAt 16 (9+i) := by decide +kernel

theorem threshold_16_10 : ∀ i ∈ List.range 1, ThresholdAt 16 (10+i) := by decide +kernel

theorem threshold_16_11 : ∀ i ∈ List.range 1, ThresholdAt 16 (11+i) := by decide +kernel

theorem threshold_16_12 : ∀ i ∈ List.range 1, ThresholdAt 16 (12+i) := by decide +kernel

theorem threshold_16_13 : ∀ i ∈ List.range 1, ThresholdAt 16 (13+i) := by decide +kernel

theorem threshold_16_14 : ∀ i ∈ List.range 1, ThresholdAt 16 (14+i) := by decide +kernel

theorem threshold_16_15 : ∀ i ∈ List.range 1, ThresholdAt 16 (15+i) := by decide +kernel

theorem threshold_16_16 : ∀ i ∈ List.range 1, ThresholdAt 16 (16+i) := by decide +kernel

theorem threshold_16_17 : ∀ i ∈ List.range 1, ThresholdAt 16 (17+i) := by decide +kernel

theorem threshold_16_18 : ∀ i ∈ List.range 1, ThresholdAt 16 (18+i) := by decide +kernel

theorem threshold_16_19 : ∀ i ∈ List.range 1, ThresholdAt 16 (19+i) := by decide +kernel

theorem threshold_16_20 : ∀ i ∈ List.range 1, ThresholdAt 16 (20+i) := by decide +kernel

theorem threshold_16_21 : ∀ i ∈ List.range 1, ThresholdAt 16 (21+i) := by decide +kernel

theorem threshold_16_22 : ∀ i ∈ List.range 1, ThresholdAt 16 (22+i) := by decide +kernel

theorem threshold_16_23 : ∀ i ∈ List.range 1, ThresholdAt 16 (23+i) := by decide +kernel

theorem threshold_16_24 : ∀ i ∈ List.range 1, ThresholdAt 16 (24+i) := by decide +kernel

theorem threshold_16_25 : ∀ i ∈ List.range 1, ThresholdAt 16 (25+i) := by decide +kernel

theorem threshold_16_26 : ∀ i ∈ List.range 1, ThresholdAt 16 (26+i) := by decide +kernel

theorem threshold_16_27 : ∀ i ∈ List.range 1, ThresholdAt 16 (27+i) := by decide +kernel

theorem threshold_16_28 : ∀ i ∈ List.range 1, ThresholdAt 16 (28+i) := by decide +kernel

theorem threshold_16_29 : ∀ i ∈ List.range 1, ThresholdAt 16 (29+i) := by decide +kernel

theorem threshold_16_30 : ∀ i ∈ List.range 1, ThresholdAt 16 (30+i) := by decide +kernel

theorem threshold_16_31 : ∀ i ∈ List.range 1, ThresholdAt 16 (31+i) := by decide +kernel

theorem threshold_16_32 : ∀ i ∈ List.range 1, ThresholdAt 16 (32+i) := by decide +kernel

theorem threshold_16_33 : ∀ i ∈ List.range 1, ThresholdAt 16 (33+i) := by decide +kernel

theorem threshold_16_34 : ∀ i ∈ List.range 1, ThresholdAt 16 (34+i) := by decide +kernel

theorem threshold_16_35 : ∀ i ∈ List.range 1, ThresholdAt 16 (35+i) := by decide +kernel

theorem threshold_16_36 : ∀ i ∈ List.range 1, ThresholdAt 16 (36+i) := by decide +kernel

theorem threshold_16_37 : ∀ i ∈ List.range 1, ThresholdAt 16 (37+i) := by decide +kernel

theorem threshold_16_38 : ∀ i ∈ List.range 1, ThresholdAt 16 (38+i) := by decide +kernel

theorem threshold_16_39 : ∀ i ∈ List.range 1, ThresholdAt 16 (39+i) := by decide +kernel

theorem threshold_16_40 : ∀ i ∈ List.range 1, ThresholdAt 16 (40+i) := by decide +kernel

theorem threshold_16_41 : ∀ i ∈ List.range 1, ThresholdAt 16 (41+i) := by decide +kernel

theorem threshold_16_42 : ∀ i ∈ List.range 1, ThresholdAt 16 (42+i) := by decide +kernel

theorem threshold_16_43 : ∀ i ∈ List.range 1, ThresholdAt 16 (43+i) := by decide +kernel

theorem threshold_16_44 : ∀ i ∈ List.range 1, ThresholdAt 16 (44+i) := by decide +kernel

theorem threshold_16_45 : ∀ i ∈ List.range 1, ThresholdAt 16 (45+i) := by decide +kernel

theorem threshold_16_46 : ∀ i ∈ List.range 1, ThresholdAt 16 (46+i) := by decide +kernel

theorem threshold_16_47 : ∀ i ∈ List.range 1, ThresholdAt 16 (47+i) := by decide +kernel

theorem threshold_16_48 : ∀ i ∈ List.range 1, ThresholdAt 16 (48+i) := by decide +kernel

theorem threshold_16_49 : ∀ i ∈ List.range 1, ThresholdAt 16 (49+i) := by decide +kernel

theorem threshold_16_50 : ∀ i ∈ List.range 1, ThresholdAt 16 (50+i) := by decide +kernel

theorem threshold_16_51 : ∀ i ∈ List.range 1, ThresholdAt 16 (51+i) := by decide +kernel

theorem threshold_16_52 : ∀ i ∈ List.range 1, ThresholdAt 16 (52+i) := by decide +kernel

theorem threshold_16_53 : ∀ i ∈ List.range 1, ThresholdAt 16 (53+i) := by decide +kernel

theorem threshold_16_54 : ∀ i ∈ List.range 1, ThresholdAt 16 (54+i) := by decide +kernel

theorem threshold_16_55 : ∀ i ∈ List.range 1, ThresholdAt 16 (55+i) := by decide +kernel

theorem threshold_16_56 : ∀ i ∈ List.range 1, ThresholdAt 16 (56+i) := by decide +kernel

theorem threshold_16_57 : ∀ i ∈ List.range 1, ThresholdAt 16 (57+i) := by decide +kernel

theorem threshold_16_58 : ∀ i ∈ List.range 1, ThresholdAt 16 (58+i) := by decide +kernel

theorem threshold_16_59 : ∀ i ∈ List.range 1, ThresholdAt 16 (59+i) := by decide +kernel

theorem threshold_16_60 : ∀ i ∈ List.range 1, ThresholdAt 16 (60+i) := by decide +kernel

theorem threshold_16_61 : ∀ i ∈ List.range 1, ThresholdAt 16 (61+i) := by decide +kernel

theorem threshold_16_62 : ∀ i ∈ List.range 1, ThresholdAt 16 (62+i) := by decide +kernel

theorem threshold_16_63 : ∀ i ∈ List.range 1, ThresholdAt 16 (63+i) := by decide +kernel

theorem threshold_16_64 : ∀ i ∈ List.range 1, ThresholdAt 16 (64+i) := by decide +kernel

theorem threshold_16_65 : ∀ i ∈ List.range 1, ThresholdAt 16 (65+i) := by decide +kernel

theorem threshold_16_66 : ∀ i ∈ List.range 1, ThresholdAt 16 (66+i) := by decide +kernel

theorem threshold_16_67 : ∀ i ∈ List.range 1, ThresholdAt 16 (67+i) := by decide +kernel

theorem threshold_16_68 : ∀ i ∈ List.range 1, ThresholdAt 16 (68+i) := by decide +kernel

theorem threshold_16_69 : ∀ i ∈ List.range 1, ThresholdAt 16 (69+i) := by decide +kernel

theorem threshold_16_70 : ∀ i ∈ List.range 1, ThresholdAt 16 (70+i) := by decide +kernel

theorem threshold_16_71 : ∀ i ∈ List.range 1, ThresholdAt 16 (71+i) := by decide +kernel

theorem threshold_16_72 : ∀ i ∈ List.range 1, ThresholdAt 16 (72+i) := by decide +kernel

theorem threshold_16_73 : ∀ i ∈ List.range 1, ThresholdAt 16 (73+i) := by decide +kernel

theorem threshold_16_74 : ∀ i ∈ List.range 1, ThresholdAt 16 (74+i) := by decide +kernel

theorem threshold_16_75 : ∀ i ∈ List.range 1, ThresholdAt 16 (75+i) := by decide +kernel

theorem threshold_16_76 : ∀ i ∈ List.range 1, ThresholdAt 16 (76+i) := by decide +kernel

theorem threshold_16_77 : ∀ i ∈ List.range 1, ThresholdAt 16 (77+i) := by decide +kernel

theorem threshold_16_78 : ∀ i ∈ List.range 1, ThresholdAt 16 (78+i) := by decide +kernel

theorem threshold_16_79 : ∀ i ∈ List.range 1, ThresholdAt 16 (79+i) := by decide +kernel

theorem threshold_16_80 : ∀ i ∈ List.range 1, ThresholdAt 16 (80+i) := by decide +kernel

theorem threshold_16_81 : ∀ i ∈ List.range 1, ThresholdAt 16 (81+i) := by decide +kernel

theorem threshold_16_82 : ∀ i ∈ List.range 1, ThresholdAt 16 (82+i) := by decide +kernel

theorem threshold_16_83 : ∀ i ∈ List.range 1, ThresholdAt 16 (83+i) := by decide +kernel

theorem threshold_16_84 : ∀ i ∈ List.range 1, ThresholdAt 16 (84+i) := by decide +kernel

theorem threshold_16_85 : ∀ i ∈ List.range 1, ThresholdAt 16 (85+i) := by decide +kernel

theorem threshold_16_86 : ∀ i ∈ List.range 1, ThresholdAt 16 (86+i) := by decide +kernel

theorem threshold_16_87 : ∀ i ∈ List.range 1, ThresholdAt 16 (87+i) := by decide +kernel

theorem threshold_16_88 : ∀ i ∈ List.range 1, ThresholdAt 16 (88+i) := by decide +kernel

theorem threshold_16_89 : ∀ i ∈ List.range 1, ThresholdAt 16 (89+i) := by decide +kernel

theorem threshold_16_90 : ∀ i ∈ List.range 1, ThresholdAt 16 (90+i) := by decide +kernel

theorem threshold_16_91 : ∀ i ∈ List.range 1, ThresholdAt 16 (91+i) := by decide +kernel

theorem threshold_16_92 : ∀ i ∈ List.range 1, ThresholdAt 16 (92+i) := by decide +kernel

theorem threshold_16_93 : ∀ i ∈ List.range 1, ThresholdAt 16 (93+i) := by decide +kernel

theorem threshold_16_94 : ∀ i ∈ List.range 1, ThresholdAt 16 (94+i) := by decide +kernel

theorem threshold_16_95 : ∀ i ∈ List.range 1, ThresholdAt 16 (95+i) := by decide +kernel

theorem threshold_16_96 : ∀ i ∈ List.range 1, ThresholdAt 16 (96+i) := by decide +kernel

theorem threshold_16_97 : ∀ i ∈ List.range 1, ThresholdAt 16 (97+i) := by decide +kernel

theorem threshold_16_98 : ∀ i ∈ List.range 1, ThresholdAt 16 (98+i) := by decide +kernel

theorem threshold_16_99 : ∀ i ∈ List.range 1, ThresholdAt 16 (99+i) := by decide +kernel

theorem threshold_16_100 : ∀ i ∈ List.range 1, ThresholdAt 16 (100+i) := by decide +kernel

theorem threshold_16_101 : ∀ i ∈ List.range 1, ThresholdAt 16 (101+i) := by decide +kernel

theorem threshold_16_102 : ∀ i ∈ List.range 1, ThresholdAt 16 (102+i) := by decide +kernel

theorem threshold_16_103 : ∀ i ∈ List.range 1, ThresholdAt 16 (103+i) := by decide +kernel

theorem threshold_16_104 : ∀ i ∈ List.range 1, ThresholdAt 16 (104+i) := by decide +kernel

theorem threshold_16_105 : ∀ i ∈ List.range 1, ThresholdAt 16 (105+i) := by decide +kernel

theorem threshold_16_106 : ∀ i ∈ List.range 1, ThresholdAt 16 (106+i) := by decide +kernel

theorem threshold_16_107 : ∀ i ∈ List.range 1, ThresholdAt 16 (107+i) := by decide +kernel

theorem threshold_16_108 : ∀ i ∈ List.range 1, ThresholdAt 16 (108+i) := by decide +kernel

theorem threshold_16_109 : ∀ i ∈ List.range 1, ThresholdAt 16 (109+i) := by decide +kernel

theorem threshold_16_110 : ∀ i ∈ List.range 1, ThresholdAt 16 (110+i) := by decide +kernel

theorem threshold_16_111 : ∀ i ∈ List.range 1, ThresholdAt 16 (111+i) := by decide +kernel

theorem threshold_16_112 : ∀ i ∈ List.range 1, ThresholdAt 16 (112+i) := by decide +kernel

theorem threshold_16_113 : ∀ i ∈ List.range 1, ThresholdAt 16 (113+i) := by decide +kernel

theorem threshold_16_114 : ∀ i ∈ List.range 1, ThresholdAt 16 (114+i) := by decide +kernel

theorem threshold_16_115 : ∀ i ∈ List.range 1, ThresholdAt 16 (115+i) := by decide +kernel

theorem threshold_16_116 : ∀ i ∈ List.range 1, ThresholdAt 16 (116+i) := by decide +kernel

theorem threshold_16_117 : ∀ i ∈ List.range 1, ThresholdAt 16 (117+i) := by decide +kernel

theorem threshold_16_118 : ∀ i ∈ List.range 1, ThresholdAt 16 (118+i) := by decide +kernel

theorem threshold_16_119 : ∀ i ∈ List.range 1, ThresholdAt 16 (119+i) := by decide +kernel

theorem threshold_16_120 : ∀ i ∈ List.range 1, ThresholdAt 16 (120+i) := by decide +kernel

theorem threshold_16_121 : ∀ i ∈ List.range 1, ThresholdAt 16 (121+i) := by decide +kernel

theorem threshold_16_122 : ∀ i ∈ List.range 1, ThresholdAt 16 (122+i) := by decide +kernel

theorem threshold_16_123 : ∀ i ∈ List.range 1, ThresholdAt 16 (123+i) := by decide +kernel

theorem threshold_16_124 : ∀ i ∈ List.range 1, ThresholdAt 16 (124+i) := by decide +kernel

theorem threshold_16_125 : ∀ i ∈ List.range 1, ThresholdAt 16 (125+i) := by decide +kernel

theorem threshold_16_126 : ∀ i ∈ List.range 1, ThresholdAt 16 (126+i) := by decide +kernel

theorem threshold_16_127 : ∀ i ∈ List.range 1, ThresholdAt 16 (127+i) := by decide +kernel

theorem threshold_16_128 : ∀ i ∈ List.range 1, ThresholdAt 16 (128+i) := by decide +kernel

theorem threshold_16_129 : ∀ i ∈ List.range 1, ThresholdAt 16 (129+i) := by decide +kernel

theorem threshold_16_130 : ∀ i ∈ List.range 1, ThresholdAt 16 (130+i) := by decide +kernel

theorem threshold_16 (v : ℕ) (hv : v ∈ List.range 131) : ThresholdAt 16 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 16 v)
  have h := (join 0 65 66 (join 0 32 33 (join 0 16 16 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_16_0 threshold_16_1) (join 2 1 1 threshold_16_2 threshold_16_3)) (join 4 2 2 (join 4 1 1 threshold_16_4 threshold_16_5) (join 6 1 1 threshold_16_6 threshold_16_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_16_8 threshold_16_9) (join 10 1 1 threshold_16_10 threshold_16_11)) (join 12 2 2 (join 12 1 1 threshold_16_12 threshold_16_13) (join 14 1 1 threshold_16_14 threshold_16_15)))) (join 16 8 8 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_16_16 threshold_16_17) (join 18 1 1 threshold_16_18 threshold_16_19)) (join 20 2 2 (join 20 1 1 threshold_16_20 threshold_16_21) (join 22 1 1 threshold_16_22 threshold_16_23))) (join 24 4 4 (join 24 2 2 (join 24 1 1 threshold_16_24 threshold_16_25) (join 26 1 1 threshold_16_26 threshold_16_27)) (join 28 2 2 (join 28 1 1 threshold_16_28 threshold_16_29) (join 30 1 1 threshold_16_30 threshold_16_31))))) (join 32 16 17 (join 32 8 8 (join 32 4 4 (join 32 2 2 (join 32 1 1 threshold_16_32 threshold_16_33) (join 34 1 1 threshold_16_34 threshold_16_35)) (join 36 2 2 (join 36 1 1 threshold_16_36 threshold_16_37) (join 38 1 1 threshold_16_38 threshold_16_39))) (join 40 4 4 (join 40 2 2 (join 40 1 1 threshold_16_40 threshold_16_41) (join 42 1 1 threshold_16_42 threshold_16_43)) (join 44 2 2 (join 44 1 1 threshold_16_44 threshold_16_45) (join 46 1 1 threshold_16_46 threshold_16_47)))) (join 48 8 9 (join 48 4 4 (join 48 2 2 (join 48 1 1 threshold_16_48 threshold_16_49) (join 50 1 1 threshold_16_50 threshold_16_51)) (join 52 2 2 (join 52 1 1 threshold_16_52 threshold_16_53) (join 54 1 1 threshold_16_54 threshold_16_55))) (join 56 4 5 (join 56 2 2 (join 56 1 1 threshold_16_56 threshold_16_57) (join 58 1 1 threshold_16_58 threshold_16_59)) (join 60 2 3 (join 60 1 1 threshold_16_60 threshold_16_61) (join 62 1 2 threshold_16_62 (join 63 1 1 threshold_16_63 threshold_16_64))))))) (join 65 33 33 (join 65 16 17 (join 65 8 8 (join 65 4 4 (join 65 2 2 (join 65 1 1 threshold_16_65 threshold_16_66) (join 67 1 1 threshold_16_67 threshold_16_68)) (join 69 2 2 (join 69 1 1 threshold_16_69 threshold_16_70) (join 71 1 1 threshold_16_71 threshold_16_72))) (join 73 4 4 (join 73 2 2 (join 73 1 1 threshold_16_73 threshold_16_74) (join 75 1 1 threshold_16_75 threshold_16_76)) (join 77 2 2 (join 77 1 1 threshold_16_77 threshold_16_78) (join 79 1 1 threshold_16_79 threshold_16_80)))) (join 81 8 9 (join 81 4 4 (join 81 2 2 (join 81 1 1 threshold_16_81 threshold_16_82) (join 83 1 1 threshold_16_83 threshold_16_84)) (join 85 2 2 (join 85 1 1 threshold_16_85 threshold_16_86) (join 87 1 1 threshold_16_87 threshold_16_88))) (join 89 4 5 (join 89 2 2 (join 89 1 1 threshold_16_89 threshold_16_90) (join 91 1 1 threshold_16_91 threshold_16_92)) (join 93 2 3 (join 93 1 1 threshold_16_93 threshold_16_94) (join 95 1 2 threshold_16_95 (join 96 1 1 threshold_16_96 threshold_16_97)))))) (join 98 16 17 (join 98 8 8 (join 98 4 4 (join 98 2 2 (join 98 1 1 threshold_16_98 threshold_16_99) (join 100 1 1 threshold_16_100 threshold_16_101)) (join 102 2 2 (join 102 1 1 threshold_16_102 threshold_16_103) (join 104 1 1 threshold_16_104 threshold_16_105))) (join 106 4 4 (join 106 2 2 (join 106 1 1 threshold_16_106 threshold_16_107) (join 108 1 1 threshold_16_108 threshold_16_109)) (join 110 2 2 (join 110 1 1 threshold_16_110 threshold_16_111) (join 112 1 1 threshold_16_112 threshold_16_113)))) (join 114 8 9 (join 114 4 4 (join 114 2 2 (join 114 1 1 threshold_16_114 threshold_16_115) (join 116 1 1 threshold_16_116 threshold_16_117)) (join 118 2 2 (join 118 1 1 threshold_16_118 threshold_16_119) (join 120 1 1 threshold_16_120 threshold_16_121))) (join 122 4 5 (join 122 2 2 (join 122 1 1 threshold_16_122 threshold_16_123) (join 124 1 1 threshold_16_124 threshold_16_125)) (join 126 2 3 (join 126 1 1 threshold_16_126 threshold_16_127) (join 128 1 2 threshold_16_128 (join 129 1 1 threshold_16_129 threshold_16_130))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_16_0 : ∀ i ∈ List.range 4, LedgerAt 16 (0+i) := by decide +kernel

theorem ledger_16_4 : ∀ i ∈ List.range 4, LedgerAt 16 (4+i) := by decide +kernel

theorem ledger_16_8 : ∀ i ∈ List.range 4, LedgerAt 16 (8+i) := by decide +kernel

theorem ledger_16_12 : ∀ i ∈ List.range 4, LedgerAt 16 (12+i) := by decide +kernel

theorem ledger_16_16 : ∀ i ∈ List.range 4, LedgerAt 16 (16+i) := by decide +kernel

theorem ledger_16_20 : ∀ i ∈ List.range 4, LedgerAt 16 (20+i) := by decide +kernel

theorem ledger_16_24 : ∀ i ∈ List.range 4, LedgerAt 16 (24+i) := by decide +kernel

theorem ledger_16_28 : ∀ i ∈ List.range 4, LedgerAt 16 (28+i) := by decide +kernel

theorem ledger_16_32 : ∀ i ∈ List.range 4, LedgerAt 16 (32+i) := by decide +kernel

theorem ledger_16_36 : ∀ i ∈ List.range 4, LedgerAt 16 (36+i) := by decide +kernel

theorem ledger_16_40 : ∀ i ∈ List.range 4, LedgerAt 16 (40+i) := by decide +kernel

theorem ledger_16_44 : ∀ i ∈ List.range 4, LedgerAt 16 (44+i) := by decide +kernel

theorem ledger_16_48 : ∀ i ∈ List.range 4, LedgerAt 16 (48+i) := by decide +kernel

theorem ledger_16_52 : ∀ i ∈ List.range 4, LedgerAt 16 (52+i) := by decide +kernel

theorem ledger_16_56 : ∀ i ∈ List.range 4, LedgerAt 16 (56+i) := by decide +kernel

theorem ledger_16_60 : ∀ i ∈ List.range 4, LedgerAt 16 (60+i) := by decide +kernel

theorem ledger_16_64 : ∀ i ∈ List.range 4, LedgerAt 16 (64+i) := by decide +kernel

theorem ledger_16_68 : ∀ i ∈ List.range 4, LedgerAt 16 (68+i) := by decide +kernel

theorem ledger_16_72 : ∀ i ∈ List.range 4, LedgerAt 16 (72+i) := by decide +kernel

theorem ledger_16_76 : ∀ i ∈ List.range 4, LedgerAt 16 (76+i) := by decide +kernel

theorem ledger_16_80 : ∀ i ∈ List.range 4, LedgerAt 16 (80+i) := by decide +kernel

theorem ledger_16_84 : ∀ i ∈ List.range 4, LedgerAt 16 (84+i) := by decide +kernel

theorem ledger_16_88 : ∀ i ∈ List.range 4, LedgerAt 16 (88+i) := by decide +kernel

theorem ledger_16_92 : ∀ i ∈ List.range 4, LedgerAt 16 (92+i) := by decide +kernel

theorem ledger_16_96 : ∀ i ∈ List.range 4, LedgerAt 16 (96+i) := by decide +kernel

theorem ledger_16_100 : ∀ i ∈ List.range 4, LedgerAt 16 (100+i) := by decide +kernel

theorem ledger_16_104 : ∀ i ∈ List.range 4, LedgerAt 16 (104+i) := by decide +kernel

theorem ledger_16_108 : ∀ i ∈ List.range 4, LedgerAt 16 (108+i) := by decide +kernel

theorem ledger_16_112 : ∀ i ∈ List.range 4, LedgerAt 16 (112+i) := by decide +kernel

theorem ledger_16_116 : ∀ i ∈ List.range 4, LedgerAt 16 (116+i) := by decide +kernel

theorem ledger_16_120 : ∀ i ∈ List.range 4, LedgerAt 16 (120+i) := by decide +kernel

theorem ledger_16_124 : ∀ i ∈ List.range 4, LedgerAt 16 (124+i) := by decide +kernel

theorem ledger_16_128 : ∀ i ∈ List.range 3, LedgerAt 16 (128+i) := by decide +kernel

theorem ledger_16 (v : ℕ) (hv : v ∈ List.range 131) : LedgerAt 16 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 16 v)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_16_0 ledger_16_4) (join 8 4 4 ledger_16_8 ledger_16_12)) (join 16 8 8 (join 16 4 4 ledger_16_16 ledger_16_20) (join 24 4 4 ledger_16_24 ledger_16_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_16_32 ledger_16_36) (join 40 4 4 ledger_16_40 ledger_16_44)) (join 48 8 8 (join 48 4 4 ledger_16_48 ledger_16_52) (join 56 4 4 ledger_16_56 ledger_16_60)))) (join 64 32 35 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_16_64 ledger_16_68) (join 72 4 4 ledger_16_72 ledger_16_76)) (join 80 8 8 (join 80 4 4 ledger_16_80 ledger_16_84) (join 88 4 4 ledger_16_88 ledger_16_92))) (join 96 16 19 (join 96 8 8 (join 96 4 4 ledger_16_96 ledger_16_100) (join 104 4 4 ledger_16_104 ledger_16_108)) (join 112 8 11 (join 112 4 4 ledger_16_112 ledger_16_116) (join 120 4 7 ledger_16_120 (join 124 4 3 ledger_16_124 ledger_16_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
