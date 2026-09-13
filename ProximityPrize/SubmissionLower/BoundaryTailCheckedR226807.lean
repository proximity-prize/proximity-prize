import ProximityPrize.SubmissionLower.BoundaryTailCheckedR216807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_22_0 : ∀ i ∈ List.range 4, GeometryAt 22 (0+i) := by decide +kernel

theorem geometry_22_4 : ∀ i ∈ List.range 4, GeometryAt 22 (4+i) := by decide +kernel

theorem geometry_22_8 : ∀ i ∈ List.range 4, GeometryAt 22 (8+i) := by decide +kernel

theorem geometry_22_12 : ∀ i ∈ List.range 4, GeometryAt 22 (12+i) := by decide +kernel

theorem geometry_22_16 : ∀ i ∈ List.range 4, GeometryAt 22 (16+i) := by decide +kernel

theorem geometry_22_20 : ∀ i ∈ List.range 4, GeometryAt 22 (20+i) := by decide +kernel

theorem geometry_22_24 : ∀ i ∈ List.range 4, GeometryAt 22 (24+i) := by decide +kernel

theorem geometry_22_28 : ∀ i ∈ List.range 4, GeometryAt 22 (28+i) := by decide +kernel

theorem geometry_22_32 : ∀ i ∈ List.range 4, GeometryAt 22 (32+i) := by decide +kernel

theorem geometry_22_36 : ∀ i ∈ List.range 4, GeometryAt 22 (36+i) := by decide +kernel

theorem geometry_22_40 : ∀ i ∈ List.range 4, GeometryAt 22 (40+i) := by decide +kernel

theorem geometry_22_44 : ∀ i ∈ List.range 4, GeometryAt 22 (44+i) := by decide +kernel

theorem geometry_22_48 : ∀ i ∈ List.range 4, GeometryAt 22 (48+i) := by decide +kernel

theorem geometry_22_52 : ∀ i ∈ List.range 4, GeometryAt 22 (52+i) := by decide +kernel

theorem geometry_22_56 : ∀ i ∈ List.range 4, GeometryAt 22 (56+i) := by decide +kernel

theorem geometry_22_60 : ∀ i ∈ List.range 4, GeometryAt 22 (60+i) := by decide +kernel

theorem geometry_22_64 : ∀ i ∈ List.range 4, GeometryAt 22 (64+i) := by decide +kernel

theorem geometry_22_68 : ∀ i ∈ List.range 4, GeometryAt 22 (68+i) := by decide +kernel

theorem geometry_22_72 : ∀ i ∈ List.range 4, GeometryAt 22 (72+i) := by decide +kernel

theorem geometry_22_76 : ∀ i ∈ List.range 4, GeometryAt 22 (76+i) := by decide +kernel

theorem geometry_22_80 : ∀ i ∈ List.range 4, GeometryAt 22 (80+i) := by decide +kernel

theorem geometry_22_84 : ∀ i ∈ List.range 4, GeometryAt 22 (84+i) := by decide +kernel

theorem geometry_22_88 : ∀ i ∈ List.range 4, GeometryAt 22 (88+i) := by decide +kernel

theorem geometry_22_92 : ∀ i ∈ List.range 4, GeometryAt 22 (92+i) := by decide +kernel

theorem geometry_22_96 : ∀ i ∈ List.range 4, GeometryAt 22 (96+i) := by decide +kernel

theorem geometry_22_100 : ∀ i ∈ List.range 4, GeometryAt 22 (100+i) := by decide +kernel

theorem geometry_22_104 : ∀ i ∈ List.range 4, GeometryAt 22 (104+i) := by decide +kernel

theorem geometry_22_108 : ∀ i ∈ List.range 4, GeometryAt 22 (108+i) := by decide +kernel

theorem geometry_22_112 : ∀ i ∈ List.range 4, GeometryAt 22 (112+i) := by decide +kernel

theorem geometry_22_116 : ∀ i ∈ List.range 4, GeometryAt 22 (116+i) := by decide +kernel

theorem geometry_22_120 : ∀ i ∈ List.range 4, GeometryAt 22 (120+i) := by decide +kernel

theorem geometry_22_124 : ∀ i ∈ List.range 1, GeometryAt 22 (124+i) := by decide +kernel

theorem geometry_22 (v : ℕ) (hv : v ∈ List.range 125) : GeometryAt 22 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 22 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_22_0 geometry_22_4) (join 8 4 4 geometry_22_8 geometry_22_12)) (join 16 8 8 (join 16 4 4 geometry_22_16 geometry_22_20) (join 24 4 4 geometry_22_24 geometry_22_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 geometry_22_32 geometry_22_36) (join 40 4 4 geometry_22_40 geometry_22_44)) (join 48 8 8 (join 48 4 4 geometry_22_48 geometry_22_52) (join 56 4 4 geometry_22_56 geometry_22_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 geometry_22_64 geometry_22_68) (join 72 4 4 geometry_22_72 geometry_22_76)) (join 80 8 8 (join 80 4 4 geometry_22_80 geometry_22_84) (join 88 4 4 geometry_22_88 geometry_22_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 geometry_22_96 geometry_22_100) (join 104 4 4 geometry_22_104 geometry_22_108)) (join 112 8 5 (join 112 4 4 geometry_22_112 geometry_22_116) (join 120 4 1 geometry_22_120 geometry_22_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_22_0 : ∀ i ∈ List.range 4, StrictAt 22 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (0+i)) 22 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_4 : ∀ i ∈ List.range 4, StrictAt 22 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (4+i)) 22 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_8 : ∀ i ∈ List.range 4, StrictAt 22 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (8+i)) 22 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_12 : ∀ i ∈ List.range 4, StrictAt 22 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (12+i)) 22 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_16 : ∀ i ∈ List.range 4, StrictAt 22 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (16+i)) 22 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_20 : ∀ i ∈ List.range 4, StrictAt 22 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (20+i)) 22 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_24 : ∀ i ∈ List.range 4, StrictAt 22 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (24+i)) 22 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_28 : ∀ i ∈ List.range 4, StrictAt 22 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (28+i)) 22 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_32 : ∀ i ∈ List.range 4, StrictAt 22 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (32+i)) 22 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_36 : ∀ i ∈ List.range 4, StrictAt 22 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (36+i)) 22 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_40 : ∀ i ∈ List.range 4, StrictAt 22 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (40+i)) 22 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_44 : ∀ i ∈ List.range 4, StrictAt 22 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (44+i)) 22 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_48 : ∀ i ∈ List.range 4, StrictAt 22 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (48+i)) 22 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_52 : ∀ i ∈ List.range 4, StrictAt 22 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (52+i)) 22 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_56 : ∀ i ∈ List.range 4, StrictAt 22 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (56+i)) 22 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_60 : ∀ i ∈ List.range 4, StrictAt 22 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (60+i)) 22 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_64 : ∀ i ∈ List.range 4, StrictAt 22 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (64+i)) 22 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_68 : ∀ i ∈ List.range 4, StrictAt 22 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (68+i)) 22 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_72 : ∀ i ∈ List.range 4, StrictAt 22 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (72+i)) 22 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_76 : ∀ i ∈ List.range 4, StrictAt 22 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (76+i)) 22 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_80 : ∀ i ∈ List.range 4, StrictAt 22 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (80+i)) 22 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_84 : ∀ i ∈ List.range 4, StrictAt 22 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (84+i)) 22 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_88 : ∀ i ∈ List.range 4, StrictAt 22 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (88+i)) 22 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_92 : ∀ i ∈ List.range 4, StrictAt 22 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (92+i)) 22 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_96 : ∀ i ∈ List.range 4, StrictAt 22 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (96+i)) 22 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_100 : ∀ i ∈ List.range 4, StrictAt 22 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (100+i)) 22 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_104 : ∀ i ∈ List.range 4, StrictAt 22 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (104+i)) 22 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_108 : ∀ i ∈ List.range 4, StrictAt 22 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (108+i)) 22 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_112 : ∀ i ∈ List.range 4, StrictAt 22 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (112+i)) 22 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_116 : ∀ i ∈ List.range 4, StrictAt 22 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (116+i)) 22 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_120 : ∀ i ∈ List.range 4, StrictAt 22 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (120+i)) 22 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22_124 : ∀ i ∈ List.range 1, StrictAt 22 (124+i) := by
  have h : ∀ i ∈ List.range 1, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 22 (124+i)) 22 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_22 (v : ℕ) (hv : v ∈ List.range 125) : StrictAt 22 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 22 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_22_0 strict_22_4) (join 8 4 4 strict_22_8 strict_22_12)) (join 16 8 8 (join 16 4 4 strict_22_16 strict_22_20) (join 24 4 4 strict_22_24 strict_22_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 strict_22_32 strict_22_36) (join 40 4 4 strict_22_40 strict_22_44)) (join 48 8 8 (join 48 4 4 strict_22_48 strict_22_52) (join 56 4 4 strict_22_56 strict_22_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 strict_22_64 strict_22_68) (join 72 4 4 strict_22_72 strict_22_76)) (join 80 8 8 (join 80 4 4 strict_22_80 strict_22_84) (join 88 4 4 strict_22_88 strict_22_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 strict_22_96 strict_22_100) (join 104 4 4 strict_22_104 strict_22_108)) (join 112 8 5 (join 112 4 4 strict_22_112 strict_22_116) (join 120 4 1 strict_22_120 strict_22_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_22_0 : ∀ i ∈ List.range 4, PhaseAt 22 (0+i) := by decide +kernel

theorem phase_22_4 : ∀ i ∈ List.range 4, PhaseAt 22 (4+i) := by decide +kernel

theorem phase_22_8 : ∀ i ∈ List.range 4, PhaseAt 22 (8+i) := by decide +kernel

theorem phase_22_12 : ∀ i ∈ List.range 4, PhaseAt 22 (12+i) := by decide +kernel

theorem phase_22_16 : ∀ i ∈ List.range 4, PhaseAt 22 (16+i) := by decide +kernel

theorem phase_22_20 : ∀ i ∈ List.range 4, PhaseAt 22 (20+i) := by decide +kernel

theorem phase_22_24 : ∀ i ∈ List.range 4, PhaseAt 22 (24+i) := by decide +kernel

theorem phase_22_28 : ∀ i ∈ List.range 4, PhaseAt 22 (28+i) := by decide +kernel

theorem phase_22_32 : ∀ i ∈ List.range 4, PhaseAt 22 (32+i) := by decide +kernel

theorem phase_22_36 : ∀ i ∈ List.range 4, PhaseAt 22 (36+i) := by decide +kernel

theorem phase_22_40 : ∀ i ∈ List.range 4, PhaseAt 22 (40+i) := by decide +kernel

theorem phase_22_44 : ∀ i ∈ List.range 4, PhaseAt 22 (44+i) := by decide +kernel

theorem phase_22_48 : ∀ i ∈ List.range 4, PhaseAt 22 (48+i) := by decide +kernel

theorem phase_22_52 : ∀ i ∈ List.range 4, PhaseAt 22 (52+i) := by decide +kernel

theorem phase_22_56 : ∀ i ∈ List.range 4, PhaseAt 22 (56+i) := by decide +kernel

theorem phase_22_60 : ∀ i ∈ List.range 4, PhaseAt 22 (60+i) := by decide +kernel

theorem phase_22_64 : ∀ i ∈ List.range 4, PhaseAt 22 (64+i) := by decide +kernel

theorem phase_22_68 : ∀ i ∈ List.range 4, PhaseAt 22 (68+i) := by decide +kernel

theorem phase_22_72 : ∀ i ∈ List.range 4, PhaseAt 22 (72+i) := by decide +kernel

theorem phase_22_76 : ∀ i ∈ List.range 4, PhaseAt 22 (76+i) := by decide +kernel

theorem phase_22_80 : ∀ i ∈ List.range 4, PhaseAt 22 (80+i) := by decide +kernel

theorem phase_22_84 : ∀ i ∈ List.range 4, PhaseAt 22 (84+i) := by decide +kernel

theorem phase_22_88 : ∀ i ∈ List.range 4, PhaseAt 22 (88+i) := by decide +kernel

theorem phase_22_92 : ∀ i ∈ List.range 4, PhaseAt 22 (92+i) := by decide +kernel

theorem phase_22_96 : ∀ i ∈ List.range 4, PhaseAt 22 (96+i) := by decide +kernel

theorem phase_22_100 : ∀ i ∈ List.range 4, PhaseAt 22 (100+i) := by decide +kernel

theorem phase_22_104 : ∀ i ∈ List.range 4, PhaseAt 22 (104+i) := by decide +kernel

theorem phase_22_108 : ∀ i ∈ List.range 4, PhaseAt 22 (108+i) := by decide +kernel

theorem phase_22_112 : ∀ i ∈ List.range 4, PhaseAt 22 (112+i) := by decide +kernel

theorem phase_22_116 : ∀ i ∈ List.range 4, PhaseAt 22 (116+i) := by decide +kernel

theorem phase_22_120 : ∀ i ∈ List.range 4, PhaseAt 22 (120+i) := by decide +kernel

theorem phase_22_124 : ∀ i ∈ List.range 1, PhaseAt 22 (124+i) := by decide +kernel

theorem phase_22 (v : ℕ) (hv : v ∈ List.range 125) : PhaseAt 22 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 22 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_22_0 phase_22_4) (join 8 4 4 phase_22_8 phase_22_12)) (join 16 8 8 (join 16 4 4 phase_22_16 phase_22_20) (join 24 4 4 phase_22_24 phase_22_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_22_32 phase_22_36) (join 40 4 4 phase_22_40 phase_22_44)) (join 48 8 8 (join 48 4 4 phase_22_48 phase_22_52) (join 56 4 4 phase_22_56 phase_22_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_22_64 phase_22_68) (join 72 4 4 phase_22_72 phase_22_76)) (join 80 8 8 (join 80 4 4 phase_22_80 phase_22_84) (join 88 4 4 phase_22_88 phase_22_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 phase_22_96 phase_22_100) (join 104 4 4 phase_22_104 phase_22_108)) (join 112 8 5 (join 112 4 4 phase_22_112 phase_22_116) (join 120 4 1 phase_22_120 phase_22_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_22_0 : ∀ i ∈ List.range 1, ThresholdAt 22 (0+i) := by decide +kernel

theorem threshold_22_1 : ∀ i ∈ List.range 1, ThresholdAt 22 (1+i) := by decide +kernel

theorem threshold_22_2 : ∀ i ∈ List.range 1, ThresholdAt 22 (2+i) := by decide +kernel

theorem threshold_22_3 : ∀ i ∈ List.range 1, ThresholdAt 22 (3+i) := by decide +kernel

theorem threshold_22_4 : ∀ i ∈ List.range 1, ThresholdAt 22 (4+i) := by decide +kernel

theorem threshold_22_5 : ∀ i ∈ List.range 1, ThresholdAt 22 (5+i) := by decide +kernel

theorem threshold_22_6 : ∀ i ∈ List.range 1, ThresholdAt 22 (6+i) := by decide +kernel

theorem threshold_22_7 : ∀ i ∈ List.range 1, ThresholdAt 22 (7+i) := by decide +kernel

theorem threshold_22_8 : ∀ i ∈ List.range 1, ThresholdAt 22 (8+i) := by decide +kernel

theorem threshold_22_9 : ∀ i ∈ List.range 1, ThresholdAt 22 (9+i) := by decide +kernel

theorem threshold_22_10 : ∀ i ∈ List.range 1, ThresholdAt 22 (10+i) := by decide +kernel

theorem threshold_22_11 : ∀ i ∈ List.range 1, ThresholdAt 22 (11+i) := by decide +kernel

theorem threshold_22_12 : ∀ i ∈ List.range 1, ThresholdAt 22 (12+i) := by decide +kernel

theorem threshold_22_13 : ∀ i ∈ List.range 1, ThresholdAt 22 (13+i) := by decide +kernel

theorem threshold_22_14 : ∀ i ∈ List.range 1, ThresholdAt 22 (14+i) := by decide +kernel

theorem threshold_22_15 : ∀ i ∈ List.range 1, ThresholdAt 22 (15+i) := by decide +kernel

theorem threshold_22_16 : ∀ i ∈ List.range 1, ThresholdAt 22 (16+i) := by decide +kernel

theorem threshold_22_17 : ∀ i ∈ List.range 1, ThresholdAt 22 (17+i) := by decide +kernel

theorem threshold_22_18 : ∀ i ∈ List.range 1, ThresholdAt 22 (18+i) := by decide +kernel

theorem threshold_22_19 : ∀ i ∈ List.range 1, ThresholdAt 22 (19+i) := by decide +kernel

theorem threshold_22_20 : ∀ i ∈ List.range 1, ThresholdAt 22 (20+i) := by decide +kernel

theorem threshold_22_21 : ∀ i ∈ List.range 1, ThresholdAt 22 (21+i) := by decide +kernel

theorem threshold_22_22 : ∀ i ∈ List.range 1, ThresholdAt 22 (22+i) := by decide +kernel

theorem threshold_22_23 : ∀ i ∈ List.range 1, ThresholdAt 22 (23+i) := by decide +kernel

theorem threshold_22_24 : ∀ i ∈ List.range 1, ThresholdAt 22 (24+i) := by decide +kernel

theorem threshold_22_25 : ∀ i ∈ List.range 1, ThresholdAt 22 (25+i) := by decide +kernel

theorem threshold_22_26 : ∀ i ∈ List.range 1, ThresholdAt 22 (26+i) := by decide +kernel

theorem threshold_22_27 : ∀ i ∈ List.range 1, ThresholdAt 22 (27+i) := by decide +kernel

theorem threshold_22_28 : ∀ i ∈ List.range 1, ThresholdAt 22 (28+i) := by decide +kernel

theorem threshold_22_29 : ∀ i ∈ List.range 1, ThresholdAt 22 (29+i) := by decide +kernel

theorem threshold_22_30 : ∀ i ∈ List.range 1, ThresholdAt 22 (30+i) := by decide +kernel

theorem threshold_22_31 : ∀ i ∈ List.range 1, ThresholdAt 22 (31+i) := by decide +kernel

theorem threshold_22_32 : ∀ i ∈ List.range 1, ThresholdAt 22 (32+i) := by decide +kernel

theorem threshold_22_33 : ∀ i ∈ List.range 1, ThresholdAt 22 (33+i) := by decide +kernel

theorem threshold_22_34 : ∀ i ∈ List.range 1, ThresholdAt 22 (34+i) := by decide +kernel

theorem threshold_22_35 : ∀ i ∈ List.range 1, ThresholdAt 22 (35+i) := by decide +kernel

theorem threshold_22_36 : ∀ i ∈ List.range 1, ThresholdAt 22 (36+i) := by decide +kernel

theorem threshold_22_37 : ∀ i ∈ List.range 1, ThresholdAt 22 (37+i) := by decide +kernel

theorem threshold_22_38 : ∀ i ∈ List.range 1, ThresholdAt 22 (38+i) := by decide +kernel

theorem threshold_22_39 : ∀ i ∈ List.range 1, ThresholdAt 22 (39+i) := by decide +kernel

theorem threshold_22_40 : ∀ i ∈ List.range 1, ThresholdAt 22 (40+i) := by decide +kernel

theorem threshold_22_41 : ∀ i ∈ List.range 1, ThresholdAt 22 (41+i) := by decide +kernel

theorem threshold_22_42 : ∀ i ∈ List.range 1, ThresholdAt 22 (42+i) := by decide +kernel

theorem threshold_22_43 : ∀ i ∈ List.range 1, ThresholdAt 22 (43+i) := by decide +kernel

theorem threshold_22_44 : ∀ i ∈ List.range 1, ThresholdAt 22 (44+i) := by decide +kernel

theorem threshold_22_45 : ∀ i ∈ List.range 1, ThresholdAt 22 (45+i) := by decide +kernel

theorem threshold_22_46 : ∀ i ∈ List.range 1, ThresholdAt 22 (46+i) := by decide +kernel

theorem threshold_22_47 : ∀ i ∈ List.range 1, ThresholdAt 22 (47+i) := by decide +kernel

theorem threshold_22_48 : ∀ i ∈ List.range 1, ThresholdAt 22 (48+i) := by decide +kernel

theorem threshold_22_49 : ∀ i ∈ List.range 1, ThresholdAt 22 (49+i) := by decide +kernel

theorem threshold_22_50 : ∀ i ∈ List.range 1, ThresholdAt 22 (50+i) := by decide +kernel

theorem threshold_22_51 : ∀ i ∈ List.range 1, ThresholdAt 22 (51+i) := by decide +kernel

theorem threshold_22_52 : ∀ i ∈ List.range 1, ThresholdAt 22 (52+i) := by decide +kernel

theorem threshold_22_53 : ∀ i ∈ List.range 1, ThresholdAt 22 (53+i) := by decide +kernel

theorem threshold_22_54 : ∀ i ∈ List.range 1, ThresholdAt 22 (54+i) := by decide +kernel

theorem threshold_22_55 : ∀ i ∈ List.range 1, ThresholdAt 22 (55+i) := by decide +kernel

theorem threshold_22_56 : ∀ i ∈ List.range 1, ThresholdAt 22 (56+i) := by decide +kernel

theorem threshold_22_57 : ∀ i ∈ List.range 1, ThresholdAt 22 (57+i) := by decide +kernel

theorem threshold_22_58 : ∀ i ∈ List.range 1, ThresholdAt 22 (58+i) := by decide +kernel

theorem threshold_22_59 : ∀ i ∈ List.range 1, ThresholdAt 22 (59+i) := by decide +kernel

theorem threshold_22_60 : ∀ i ∈ List.range 1, ThresholdAt 22 (60+i) := by decide +kernel

theorem threshold_22_61 : ∀ i ∈ List.range 1, ThresholdAt 22 (61+i) := by decide +kernel

theorem threshold_22_62 : ∀ i ∈ List.range 1, ThresholdAt 22 (62+i) := by decide +kernel

theorem threshold_22_63 : ∀ i ∈ List.range 1, ThresholdAt 22 (63+i) := by decide +kernel

theorem threshold_22_64 : ∀ i ∈ List.range 1, ThresholdAt 22 (64+i) := by decide +kernel

theorem threshold_22_65 : ∀ i ∈ List.range 1, ThresholdAt 22 (65+i) := by decide +kernel

theorem threshold_22_66 : ∀ i ∈ List.range 1, ThresholdAt 22 (66+i) := by decide +kernel

theorem threshold_22_67 : ∀ i ∈ List.range 1, ThresholdAt 22 (67+i) := by decide +kernel

theorem threshold_22_68 : ∀ i ∈ List.range 1, ThresholdAt 22 (68+i) := by decide +kernel

theorem threshold_22_69 : ∀ i ∈ List.range 1, ThresholdAt 22 (69+i) := by decide +kernel

theorem threshold_22_70 : ∀ i ∈ List.range 1, ThresholdAt 22 (70+i) := by decide +kernel

theorem threshold_22_71 : ∀ i ∈ List.range 1, ThresholdAt 22 (71+i) := by decide +kernel

theorem threshold_22_72 : ∀ i ∈ List.range 1, ThresholdAt 22 (72+i) := by decide +kernel

theorem threshold_22_73 : ∀ i ∈ List.range 1, ThresholdAt 22 (73+i) := by decide +kernel

theorem threshold_22_74 : ∀ i ∈ List.range 1, ThresholdAt 22 (74+i) := by decide +kernel

theorem threshold_22_75 : ∀ i ∈ List.range 1, ThresholdAt 22 (75+i) := by decide +kernel

theorem threshold_22_76 : ∀ i ∈ List.range 1, ThresholdAt 22 (76+i) := by decide +kernel

theorem threshold_22_77 : ∀ i ∈ List.range 1, ThresholdAt 22 (77+i) := by decide +kernel

theorem threshold_22_78 : ∀ i ∈ List.range 1, ThresholdAt 22 (78+i) := by decide +kernel

theorem threshold_22_79 : ∀ i ∈ List.range 1, ThresholdAt 22 (79+i) := by decide +kernel

theorem threshold_22_80 : ∀ i ∈ List.range 1, ThresholdAt 22 (80+i) := by decide +kernel

theorem threshold_22_81 : ∀ i ∈ List.range 1, ThresholdAt 22 (81+i) := by decide +kernel

theorem threshold_22_82 : ∀ i ∈ List.range 1, ThresholdAt 22 (82+i) := by decide +kernel

theorem threshold_22_83 : ∀ i ∈ List.range 1, ThresholdAt 22 (83+i) := by decide +kernel

theorem threshold_22_84 : ∀ i ∈ List.range 1, ThresholdAt 22 (84+i) := by decide +kernel

theorem threshold_22_85 : ∀ i ∈ List.range 1, ThresholdAt 22 (85+i) := by decide +kernel

theorem threshold_22_86 : ∀ i ∈ List.range 1, ThresholdAt 22 (86+i) := by decide +kernel

theorem threshold_22_87 : ∀ i ∈ List.range 1, ThresholdAt 22 (87+i) := by decide +kernel

theorem threshold_22_88 : ∀ i ∈ List.range 1, ThresholdAt 22 (88+i) := by decide +kernel

theorem threshold_22_89 : ∀ i ∈ List.range 1, ThresholdAt 22 (89+i) := by decide +kernel

theorem threshold_22_90 : ∀ i ∈ List.range 1, ThresholdAt 22 (90+i) := by decide +kernel

theorem threshold_22_91 : ∀ i ∈ List.range 1, ThresholdAt 22 (91+i) := by decide +kernel

theorem threshold_22_92 : ∀ i ∈ List.range 1, ThresholdAt 22 (92+i) := by decide +kernel

theorem threshold_22_93 : ∀ i ∈ List.range 1, ThresholdAt 22 (93+i) := by decide +kernel

theorem threshold_22_94 : ∀ i ∈ List.range 1, ThresholdAt 22 (94+i) := by decide +kernel

theorem threshold_22_95 : ∀ i ∈ List.range 1, ThresholdAt 22 (95+i) := by decide +kernel

theorem threshold_22_96 : ∀ i ∈ List.range 1, ThresholdAt 22 (96+i) := by decide +kernel

theorem threshold_22_97 : ∀ i ∈ List.range 1, ThresholdAt 22 (97+i) := by decide +kernel

theorem threshold_22_98 : ∀ i ∈ List.range 1, ThresholdAt 22 (98+i) := by decide +kernel

theorem threshold_22_99 : ∀ i ∈ List.range 1, ThresholdAt 22 (99+i) := by decide +kernel

theorem threshold_22_100 : ∀ i ∈ List.range 1, ThresholdAt 22 (100+i) := by decide +kernel

theorem threshold_22_101 : ∀ i ∈ List.range 1, ThresholdAt 22 (101+i) := by decide +kernel

theorem threshold_22_102 : ∀ i ∈ List.range 1, ThresholdAt 22 (102+i) := by decide +kernel

theorem threshold_22_103 : ∀ i ∈ List.range 1, ThresholdAt 22 (103+i) := by decide +kernel

theorem threshold_22_104 : ∀ i ∈ List.range 1, ThresholdAt 22 (104+i) := by decide +kernel

theorem threshold_22_105 : ∀ i ∈ List.range 1, ThresholdAt 22 (105+i) := by decide +kernel

theorem threshold_22_106 : ∀ i ∈ List.range 1, ThresholdAt 22 (106+i) := by decide +kernel

theorem threshold_22_107 : ∀ i ∈ List.range 1, ThresholdAt 22 (107+i) := by decide +kernel

theorem threshold_22_108 : ∀ i ∈ List.range 1, ThresholdAt 22 (108+i) := by decide +kernel

theorem threshold_22_109 : ∀ i ∈ List.range 1, ThresholdAt 22 (109+i) := by decide +kernel

theorem threshold_22_110 : ∀ i ∈ List.range 1, ThresholdAt 22 (110+i) := by decide +kernel

theorem threshold_22_111 : ∀ i ∈ List.range 1, ThresholdAt 22 (111+i) := by decide +kernel

theorem threshold_22_112 : ∀ i ∈ List.range 1, ThresholdAt 22 (112+i) := by decide +kernel

theorem threshold_22_113 : ∀ i ∈ List.range 1, ThresholdAt 22 (113+i) := by decide +kernel

theorem threshold_22_114 : ∀ i ∈ List.range 1, ThresholdAt 22 (114+i) := by decide +kernel

theorem threshold_22_115 : ∀ i ∈ List.range 1, ThresholdAt 22 (115+i) := by decide +kernel

theorem threshold_22_116 : ∀ i ∈ List.range 1, ThresholdAt 22 (116+i) := by decide +kernel

theorem threshold_22_117 : ∀ i ∈ List.range 1, ThresholdAt 22 (117+i) := by decide +kernel

theorem threshold_22_118 : ∀ i ∈ List.range 1, ThresholdAt 22 (118+i) := by decide +kernel

theorem threshold_22_119 : ∀ i ∈ List.range 1, ThresholdAt 22 (119+i) := by decide +kernel

theorem threshold_22_120 : ∀ i ∈ List.range 1, ThresholdAt 22 (120+i) := by decide +kernel

theorem threshold_22_121 : ∀ i ∈ List.range 1, ThresholdAt 22 (121+i) := by decide +kernel

theorem threshold_22_122 : ∀ i ∈ List.range 1, ThresholdAt 22 (122+i) := by decide +kernel

theorem threshold_22_123 : ∀ i ∈ List.range 1, ThresholdAt 22 (123+i) := by decide +kernel

theorem threshold_22_124 : ∀ i ∈ List.range 1, ThresholdAt 22 (124+i) := by decide +kernel

theorem threshold_22 (v : ℕ) (hv : v ∈ List.range 125) : ThresholdAt 22 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 22 v)
  have h := (join 0 62 63 (join 0 31 31 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_22_0 (join 1 1 1 threshold_22_1 threshold_22_2)) (join 3 2 2 (join 3 1 1 threshold_22_3 threshold_22_4) (join 5 1 1 threshold_22_5 threshold_22_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_22_7 threshold_22_8) (join 9 1 1 threshold_22_9 threshold_22_10)) (join 11 2 2 (join 11 1 1 threshold_22_11 threshold_22_12) (join 13 1 1 threshold_22_13 threshold_22_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_22_15 threshold_22_16) (join 17 1 1 threshold_22_17 threshold_22_18)) (join 19 2 2 (join 19 1 1 threshold_22_19 threshold_22_20) (join 21 1 1 threshold_22_21 threshold_22_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_22_23 threshold_22_24) (join 25 1 1 threshold_22_25 threshold_22_26)) (join 27 2 2 (join 27 1 1 threshold_22_27 threshold_22_28) (join 29 1 1 threshold_22_29 threshold_22_30))))) (join 31 15 16 (join 31 7 8 (join 31 3 4 (join 31 1 2 threshold_22_31 (join 32 1 1 threshold_22_32 threshold_22_33)) (join 34 2 2 (join 34 1 1 threshold_22_34 threshold_22_35) (join 36 1 1 threshold_22_36 threshold_22_37))) (join 38 4 4 (join 38 2 2 (join 38 1 1 threshold_22_38 threshold_22_39) (join 40 1 1 threshold_22_40 threshold_22_41)) (join 42 2 2 (join 42 1 1 threshold_22_42 threshold_22_43) (join 44 1 1 threshold_22_44 threshold_22_45)))) (join 46 8 8 (join 46 4 4 (join 46 2 2 (join 46 1 1 threshold_22_46 threshold_22_47) (join 48 1 1 threshold_22_48 threshold_22_49)) (join 50 2 2 (join 50 1 1 threshold_22_50 threshold_22_51) (join 52 1 1 threshold_22_52 threshold_22_53))) (join 54 4 4 (join 54 2 2 (join 54 1 1 threshold_22_54 threshold_22_55) (join 56 1 1 threshold_22_56 threshold_22_57)) (join 58 2 2 (join 58 1 1 threshold_22_58 threshold_22_59) (join 60 1 1 threshold_22_60 threshold_22_61)))))) (join 62 31 32 (join 62 15 16 (join 62 7 8 (join 62 3 4 (join 62 1 2 threshold_22_62 (join 63 1 1 threshold_22_63 threshold_22_64)) (join 65 2 2 (join 65 1 1 threshold_22_65 threshold_22_66) (join 67 1 1 threshold_22_67 threshold_22_68))) (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_22_69 threshold_22_70) (join 71 1 1 threshold_22_71 threshold_22_72)) (join 73 2 2 (join 73 1 1 threshold_22_73 threshold_22_74) (join 75 1 1 threshold_22_75 threshold_22_76)))) (join 77 8 8 (join 77 4 4 (join 77 2 2 (join 77 1 1 threshold_22_77 threshold_22_78) (join 79 1 1 threshold_22_79 threshold_22_80)) (join 81 2 2 (join 81 1 1 threshold_22_81 threshold_22_82) (join 83 1 1 threshold_22_83 threshold_22_84))) (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_22_85 threshold_22_86) (join 87 1 1 threshold_22_87 threshold_22_88)) (join 89 2 2 (join 89 1 1 threshold_22_89 threshold_22_90) (join 91 1 1 threshold_22_91 threshold_22_92))))) (join 93 16 16 (join 93 8 8 (join 93 4 4 (join 93 2 2 (join 93 1 1 threshold_22_93 threshold_22_94) (join 95 1 1 threshold_22_95 threshold_22_96)) (join 97 2 2 (join 97 1 1 threshold_22_97 threshold_22_98) (join 99 1 1 threshold_22_99 threshold_22_100))) (join 101 4 4 (join 101 2 2 (join 101 1 1 threshold_22_101 threshold_22_102) (join 103 1 1 threshold_22_103 threshold_22_104)) (join 105 2 2 (join 105 1 1 threshold_22_105 threshold_22_106) (join 107 1 1 threshold_22_107 threshold_22_108)))) (join 109 8 8 (join 109 4 4 (join 109 2 2 (join 109 1 1 threshold_22_109 threshold_22_110) (join 111 1 1 threshold_22_111 threshold_22_112)) (join 113 2 2 (join 113 1 1 threshold_22_113 threshold_22_114) (join 115 1 1 threshold_22_115 threshold_22_116))) (join 117 4 4 (join 117 2 2 (join 117 1 1 threshold_22_117 threshold_22_118) (join 119 1 1 threshold_22_119 threshold_22_120)) (join 121 2 2 (join 121 1 1 threshold_22_121 threshold_22_122) (join 123 1 1 threshold_22_123 threshold_22_124)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_22_0 : ∀ i ∈ List.range 4, LedgerAt 22 (0+i) := by decide +kernel

theorem ledger_22_4 : ∀ i ∈ List.range 4, LedgerAt 22 (4+i) := by decide +kernel

theorem ledger_22_8 : ∀ i ∈ List.range 4, LedgerAt 22 (8+i) := by decide +kernel

theorem ledger_22_12 : ∀ i ∈ List.range 4, LedgerAt 22 (12+i) := by decide +kernel

theorem ledger_22_16 : ∀ i ∈ List.range 4, LedgerAt 22 (16+i) := by decide +kernel

theorem ledger_22_20 : ∀ i ∈ List.range 4, LedgerAt 22 (20+i) := by decide +kernel

theorem ledger_22_24 : ∀ i ∈ List.range 4, LedgerAt 22 (24+i) := by decide +kernel

theorem ledger_22_28 : ∀ i ∈ List.range 4, LedgerAt 22 (28+i) := by decide +kernel

theorem ledger_22_32 : ∀ i ∈ List.range 4, LedgerAt 22 (32+i) := by decide +kernel

theorem ledger_22_36 : ∀ i ∈ List.range 4, LedgerAt 22 (36+i) := by decide +kernel

theorem ledger_22_40 : ∀ i ∈ List.range 4, LedgerAt 22 (40+i) := by decide +kernel

theorem ledger_22_44 : ∀ i ∈ List.range 4, LedgerAt 22 (44+i) := by decide +kernel

theorem ledger_22_48 : ∀ i ∈ List.range 4, LedgerAt 22 (48+i) := by decide +kernel

theorem ledger_22_52 : ∀ i ∈ List.range 4, LedgerAt 22 (52+i) := by decide +kernel

theorem ledger_22_56 : ∀ i ∈ List.range 4, LedgerAt 22 (56+i) := by decide +kernel

theorem ledger_22_60 : ∀ i ∈ List.range 4, LedgerAt 22 (60+i) := by decide +kernel

theorem ledger_22_64 : ∀ i ∈ List.range 4, LedgerAt 22 (64+i) := by decide +kernel

theorem ledger_22_68 : ∀ i ∈ List.range 4, LedgerAt 22 (68+i) := by decide +kernel

theorem ledger_22_72 : ∀ i ∈ List.range 4, LedgerAt 22 (72+i) := by decide +kernel

theorem ledger_22_76 : ∀ i ∈ List.range 4, LedgerAt 22 (76+i) := by decide +kernel

theorem ledger_22_80 : ∀ i ∈ List.range 4, LedgerAt 22 (80+i) := by decide +kernel

theorem ledger_22_84 : ∀ i ∈ List.range 4, LedgerAt 22 (84+i) := by decide +kernel

theorem ledger_22_88 : ∀ i ∈ List.range 4, LedgerAt 22 (88+i) := by decide +kernel

theorem ledger_22_92 : ∀ i ∈ List.range 4, LedgerAt 22 (92+i) := by decide +kernel

theorem ledger_22_96 : ∀ i ∈ List.range 4, LedgerAt 22 (96+i) := by decide +kernel

theorem ledger_22_100 : ∀ i ∈ List.range 4, LedgerAt 22 (100+i) := by decide +kernel

theorem ledger_22_104 : ∀ i ∈ List.range 4, LedgerAt 22 (104+i) := by decide +kernel

theorem ledger_22_108 : ∀ i ∈ List.range 4, LedgerAt 22 (108+i) := by decide +kernel

theorem ledger_22_112 : ∀ i ∈ List.range 4, LedgerAt 22 (112+i) := by decide +kernel

theorem ledger_22_116 : ∀ i ∈ List.range 4, LedgerAt 22 (116+i) := by decide +kernel

theorem ledger_22_120 : ∀ i ∈ List.range 4, LedgerAt 22 (120+i) := by decide +kernel

theorem ledger_22_124 : ∀ i ∈ List.range 1, LedgerAt 22 (124+i) := by decide +kernel

theorem ledger_22 (v : ℕ) (hv : v ∈ List.range 125) : LedgerAt 22 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 22 v)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_22_0 ledger_22_4) (join 8 4 4 ledger_22_8 ledger_22_12)) (join 16 8 8 (join 16 4 4 ledger_22_16 ledger_22_20) (join 24 4 4 ledger_22_24 ledger_22_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_22_32 ledger_22_36) (join 40 4 4 ledger_22_40 ledger_22_44)) (join 48 8 8 (join 48 4 4 ledger_22_48 ledger_22_52) (join 56 4 4 ledger_22_56 ledger_22_60)))) (join 64 32 29 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_22_64 ledger_22_68) (join 72 4 4 ledger_22_72 ledger_22_76)) (join 80 8 8 (join 80 4 4 ledger_22_80 ledger_22_84) (join 88 4 4 ledger_22_88 ledger_22_92))) (join 96 16 13 (join 96 8 8 (join 96 4 4 ledger_22_96 ledger_22_100) (join 104 4 4 ledger_22_104 ledger_22_108)) (join 112 8 5 (join 112 4 4 ledger_22_112 ledger_22_116) (join 120 4 1 ledger_22_120 ledger_22_124)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
