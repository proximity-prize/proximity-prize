import ProximityPrize.SubmissionLower.BoundaryTailCheckedR176807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_18_0 : ∀ i ∈ List.range 4, GeometryAt 18 (0+i) := by decide +kernel

theorem geometry_18_4 : ∀ i ∈ List.range 4, GeometryAt 18 (4+i) := by decide +kernel

theorem geometry_18_8 : ∀ i ∈ List.range 4, GeometryAt 18 (8+i) := by decide +kernel

theorem geometry_18_12 : ∀ i ∈ List.range 4, GeometryAt 18 (12+i) := by decide +kernel

theorem geometry_18_16 : ∀ i ∈ List.range 4, GeometryAt 18 (16+i) := by decide +kernel

theorem geometry_18_20 : ∀ i ∈ List.range 4, GeometryAt 18 (20+i) := by decide +kernel

theorem geometry_18_24 : ∀ i ∈ List.range 4, GeometryAt 18 (24+i) := by decide +kernel

theorem geometry_18_28 : ∀ i ∈ List.range 4, GeometryAt 18 (28+i) := by decide +kernel

theorem geometry_18_32 : ∀ i ∈ List.range 4, GeometryAt 18 (32+i) := by decide +kernel

theorem geometry_18_36 : ∀ i ∈ List.range 4, GeometryAt 18 (36+i) := by decide +kernel

theorem geometry_18_40 : ∀ i ∈ List.range 4, GeometryAt 18 (40+i) := by decide +kernel

theorem geometry_18_44 : ∀ i ∈ List.range 4, GeometryAt 18 (44+i) := by decide +kernel

theorem geometry_18_48 : ∀ i ∈ List.range 4, GeometryAt 18 (48+i) := by decide +kernel

theorem geometry_18_52 : ∀ i ∈ List.range 4, GeometryAt 18 (52+i) := by decide +kernel

theorem geometry_18_56 : ∀ i ∈ List.range 4, GeometryAt 18 (56+i) := by decide +kernel

theorem geometry_18_60 : ∀ i ∈ List.range 4, GeometryAt 18 (60+i) := by decide +kernel

theorem geometry_18_64 : ∀ i ∈ List.range 4, GeometryAt 18 (64+i) := by decide +kernel

theorem geometry_18_68 : ∀ i ∈ List.range 4, GeometryAt 18 (68+i) := by decide +kernel

theorem geometry_18_72 : ∀ i ∈ List.range 4, GeometryAt 18 (72+i) := by decide +kernel

theorem geometry_18_76 : ∀ i ∈ List.range 4, GeometryAt 18 (76+i) := by decide +kernel

theorem geometry_18_80 : ∀ i ∈ List.range 4, GeometryAt 18 (80+i) := by decide +kernel

theorem geometry_18_84 : ∀ i ∈ List.range 4, GeometryAt 18 (84+i) := by decide +kernel

theorem geometry_18_88 : ∀ i ∈ List.range 4, GeometryAt 18 (88+i) := by decide +kernel

theorem geometry_18_92 : ∀ i ∈ List.range 4, GeometryAt 18 (92+i) := by decide +kernel

theorem geometry_18_96 : ∀ i ∈ List.range 4, GeometryAt 18 (96+i) := by decide +kernel

theorem geometry_18_100 : ∀ i ∈ List.range 4, GeometryAt 18 (100+i) := by decide +kernel

theorem geometry_18_104 : ∀ i ∈ List.range 4, GeometryAt 18 (104+i) := by decide +kernel

theorem geometry_18_108 : ∀ i ∈ List.range 4, GeometryAt 18 (108+i) := by decide +kernel

theorem geometry_18_112 : ∀ i ∈ List.range 4, GeometryAt 18 (112+i) := by decide +kernel

theorem geometry_18_116 : ∀ i ∈ List.range 4, GeometryAt 18 (116+i) := by decide +kernel

theorem geometry_18_120 : ∀ i ∈ List.range 4, GeometryAt 18 (120+i) := by decide +kernel

theorem geometry_18_124 : ∀ i ∈ List.range 4, GeometryAt 18 (124+i) := by decide +kernel

theorem geometry_18_128 : ∀ i ∈ List.range 1, GeometryAt 18 (128+i) := by decide +kernel

theorem geometry_18 (v : ℕ) (hv : v ∈ List.range 129) : GeometryAt 18 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 18 v)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_18_0 geometry_18_4) (join 8 4 4 geometry_18_8 geometry_18_12)) (join 16 8 8 (join 16 4 4 geometry_18_16 geometry_18_20) (join 24 4 4 geometry_18_24 geometry_18_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 geometry_18_32 geometry_18_36) (join 40 4 4 geometry_18_40 geometry_18_44)) (join 48 8 8 (join 48 4 4 geometry_18_48 geometry_18_52) (join 56 4 4 geometry_18_56 geometry_18_60)))) (join 64 32 33 (join 64 16 16 (join 64 8 8 (join 64 4 4 geometry_18_64 geometry_18_68) (join 72 4 4 geometry_18_72 geometry_18_76)) (join 80 8 8 (join 80 4 4 geometry_18_80 geometry_18_84) (join 88 4 4 geometry_18_88 geometry_18_92))) (join 96 16 17 (join 96 8 8 (join 96 4 4 geometry_18_96 geometry_18_100) (join 104 4 4 geometry_18_104 geometry_18_108)) (join 112 8 9 (join 112 4 4 geometry_18_112 geometry_18_116) (join 120 4 5 geometry_18_120 (join 124 4 1 geometry_18_124 geometry_18_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_18_0 : ∀ i ∈ List.range 4, StrictAt 18 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (0+i)) 18 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_4 : ∀ i ∈ List.range 4, StrictAt 18 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (4+i)) 18 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_8 : ∀ i ∈ List.range 4, StrictAt 18 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (8+i)) 18 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_12 : ∀ i ∈ List.range 4, StrictAt 18 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (12+i)) 18 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_16 : ∀ i ∈ List.range 4, StrictAt 18 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (16+i)) 18 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_20 : ∀ i ∈ List.range 4, StrictAt 18 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (20+i)) 18 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_24 : ∀ i ∈ List.range 4, StrictAt 18 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (24+i)) 18 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_28 : ∀ i ∈ List.range 4, StrictAt 18 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (28+i)) 18 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_32 : ∀ i ∈ List.range 4, StrictAt 18 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (32+i)) 18 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_36 : ∀ i ∈ List.range 4, StrictAt 18 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (36+i)) 18 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_40 : ∀ i ∈ List.range 4, StrictAt 18 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (40+i)) 18 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_44 : ∀ i ∈ List.range 4, StrictAt 18 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (44+i)) 18 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_48 : ∀ i ∈ List.range 4, StrictAt 18 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (48+i)) 18 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_52 : ∀ i ∈ List.range 4, StrictAt 18 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (52+i)) 18 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_56 : ∀ i ∈ List.range 4, StrictAt 18 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (56+i)) 18 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_60 : ∀ i ∈ List.range 4, StrictAt 18 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (60+i)) 18 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_64 : ∀ i ∈ List.range 4, StrictAt 18 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (64+i)) 18 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_68 : ∀ i ∈ List.range 4, StrictAt 18 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (68+i)) 18 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_72 : ∀ i ∈ List.range 4, StrictAt 18 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (72+i)) 18 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_76 : ∀ i ∈ List.range 4, StrictAt 18 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (76+i)) 18 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_80 : ∀ i ∈ List.range 4, StrictAt 18 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (80+i)) 18 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_84 : ∀ i ∈ List.range 4, StrictAt 18 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (84+i)) 18 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_88 : ∀ i ∈ List.range 4, StrictAt 18 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (88+i)) 18 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_92 : ∀ i ∈ List.range 4, StrictAt 18 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (92+i)) 18 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_96 : ∀ i ∈ List.range 4, StrictAt 18 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (96+i)) 18 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_100 : ∀ i ∈ List.range 4, StrictAt 18 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (100+i)) 18 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_104 : ∀ i ∈ List.range 4, StrictAt 18 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (104+i)) 18 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_108 : ∀ i ∈ List.range 4, StrictAt 18 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (108+i)) 18 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_112 : ∀ i ∈ List.range 4, StrictAt 18 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (112+i)) 18 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_116 : ∀ i ∈ List.range 4, StrictAt 18 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (116+i)) 18 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_120 : ∀ i ∈ List.range 4, StrictAt 18 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (120+i)) 18 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_124 : ∀ i ∈ List.range 4, StrictAt 18 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (124+i)) 18 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18_128 : ∀ i ∈ List.range 1, StrictAt 18 (128+i) := by
  have h : ∀ i ∈ List.range 1, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 18 (128+i)) 18 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_18 (v : ℕ) (hv : v ∈ List.range 129) : StrictAt 18 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 18 v)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_18_0 strict_18_4) (join 8 4 4 strict_18_8 strict_18_12)) (join 16 8 8 (join 16 4 4 strict_18_16 strict_18_20) (join 24 4 4 strict_18_24 strict_18_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 strict_18_32 strict_18_36) (join 40 4 4 strict_18_40 strict_18_44)) (join 48 8 8 (join 48 4 4 strict_18_48 strict_18_52) (join 56 4 4 strict_18_56 strict_18_60)))) (join 64 32 33 (join 64 16 16 (join 64 8 8 (join 64 4 4 strict_18_64 strict_18_68) (join 72 4 4 strict_18_72 strict_18_76)) (join 80 8 8 (join 80 4 4 strict_18_80 strict_18_84) (join 88 4 4 strict_18_88 strict_18_92))) (join 96 16 17 (join 96 8 8 (join 96 4 4 strict_18_96 strict_18_100) (join 104 4 4 strict_18_104 strict_18_108)) (join 112 8 9 (join 112 4 4 strict_18_112 strict_18_116) (join 120 4 5 strict_18_120 (join 124 4 1 strict_18_124 strict_18_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_18_0 : ∀ i ∈ List.range 4, PhaseAt 18 (0+i) := by decide +kernel

theorem phase_18_4 : ∀ i ∈ List.range 4, PhaseAt 18 (4+i) := by decide +kernel

theorem phase_18_8 : ∀ i ∈ List.range 4, PhaseAt 18 (8+i) := by decide +kernel

theorem phase_18_12 : ∀ i ∈ List.range 4, PhaseAt 18 (12+i) := by decide +kernel

theorem phase_18_16 : ∀ i ∈ List.range 4, PhaseAt 18 (16+i) := by decide +kernel

theorem phase_18_20 : ∀ i ∈ List.range 4, PhaseAt 18 (20+i) := by decide +kernel

theorem phase_18_24 : ∀ i ∈ List.range 4, PhaseAt 18 (24+i) := by decide +kernel

theorem phase_18_28 : ∀ i ∈ List.range 4, PhaseAt 18 (28+i) := by decide +kernel

theorem phase_18_32 : ∀ i ∈ List.range 4, PhaseAt 18 (32+i) := by decide +kernel

theorem phase_18_36 : ∀ i ∈ List.range 4, PhaseAt 18 (36+i) := by decide +kernel

theorem phase_18_40 : ∀ i ∈ List.range 4, PhaseAt 18 (40+i) := by decide +kernel

theorem phase_18_44 : ∀ i ∈ List.range 4, PhaseAt 18 (44+i) := by decide +kernel

theorem phase_18_48 : ∀ i ∈ List.range 4, PhaseAt 18 (48+i) := by decide +kernel

theorem phase_18_52 : ∀ i ∈ List.range 4, PhaseAt 18 (52+i) := by decide +kernel

theorem phase_18_56 : ∀ i ∈ List.range 4, PhaseAt 18 (56+i) := by decide +kernel

theorem phase_18_60 : ∀ i ∈ List.range 4, PhaseAt 18 (60+i) := by decide +kernel

theorem phase_18_64 : ∀ i ∈ List.range 4, PhaseAt 18 (64+i) := by decide +kernel

theorem phase_18_68 : ∀ i ∈ List.range 4, PhaseAt 18 (68+i) := by decide +kernel

theorem phase_18_72 : ∀ i ∈ List.range 4, PhaseAt 18 (72+i) := by decide +kernel

theorem phase_18_76 : ∀ i ∈ List.range 4, PhaseAt 18 (76+i) := by decide +kernel

theorem phase_18_80 : ∀ i ∈ List.range 4, PhaseAt 18 (80+i) := by decide +kernel

theorem phase_18_84 : ∀ i ∈ List.range 4, PhaseAt 18 (84+i) := by decide +kernel

theorem phase_18_88 : ∀ i ∈ List.range 4, PhaseAt 18 (88+i) := by decide +kernel

theorem phase_18_92 : ∀ i ∈ List.range 4, PhaseAt 18 (92+i) := by decide +kernel

theorem phase_18_96 : ∀ i ∈ List.range 4, PhaseAt 18 (96+i) := by decide +kernel

theorem phase_18_100 : ∀ i ∈ List.range 4, PhaseAt 18 (100+i) := by decide +kernel

theorem phase_18_104 : ∀ i ∈ List.range 4, PhaseAt 18 (104+i) := by decide +kernel

theorem phase_18_108 : ∀ i ∈ List.range 4, PhaseAt 18 (108+i) := by decide +kernel

theorem phase_18_112 : ∀ i ∈ List.range 4, PhaseAt 18 (112+i) := by decide +kernel

theorem phase_18_116 : ∀ i ∈ List.range 4, PhaseAt 18 (116+i) := by decide +kernel

theorem phase_18_120 : ∀ i ∈ List.range 4, PhaseAt 18 (120+i) := by decide +kernel

theorem phase_18_124 : ∀ i ∈ List.range 4, PhaseAt 18 (124+i) := by decide +kernel

theorem phase_18_128 : ∀ i ∈ List.range 1, PhaseAt 18 (128+i) := by decide +kernel

theorem phase_18 (v : ℕ) (hv : v ∈ List.range 129) : PhaseAt 18 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 18 v)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_18_0 phase_18_4) (join 8 4 4 phase_18_8 phase_18_12)) (join 16 8 8 (join 16 4 4 phase_18_16 phase_18_20) (join 24 4 4 phase_18_24 phase_18_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_18_32 phase_18_36) (join 40 4 4 phase_18_40 phase_18_44)) (join 48 8 8 (join 48 4 4 phase_18_48 phase_18_52) (join 56 4 4 phase_18_56 phase_18_60)))) (join 64 32 33 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_18_64 phase_18_68) (join 72 4 4 phase_18_72 phase_18_76)) (join 80 8 8 (join 80 4 4 phase_18_80 phase_18_84) (join 88 4 4 phase_18_88 phase_18_92))) (join 96 16 17 (join 96 8 8 (join 96 4 4 phase_18_96 phase_18_100) (join 104 4 4 phase_18_104 phase_18_108)) (join 112 8 9 (join 112 4 4 phase_18_112 phase_18_116) (join 120 4 5 phase_18_120 (join 124 4 1 phase_18_124 phase_18_128))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_18_0 : ∀ i ∈ List.range 1, ThresholdAt 18 (0+i) := by decide +kernel

theorem threshold_18_1 : ∀ i ∈ List.range 1, ThresholdAt 18 (1+i) := by decide +kernel

theorem threshold_18_2 : ∀ i ∈ List.range 1, ThresholdAt 18 (2+i) := by decide +kernel

theorem threshold_18_3 : ∀ i ∈ List.range 1, ThresholdAt 18 (3+i) := by decide +kernel

theorem threshold_18_4 : ∀ i ∈ List.range 1, ThresholdAt 18 (4+i) := by decide +kernel

theorem threshold_18_5 : ∀ i ∈ List.range 1, ThresholdAt 18 (5+i) := by decide +kernel

theorem threshold_18_6 : ∀ i ∈ List.range 1, ThresholdAt 18 (6+i) := by decide +kernel

theorem threshold_18_7 : ∀ i ∈ List.range 1, ThresholdAt 18 (7+i) := by decide +kernel

theorem threshold_18_8 : ∀ i ∈ List.range 1, ThresholdAt 18 (8+i) := by decide +kernel

theorem threshold_18_9 : ∀ i ∈ List.range 1, ThresholdAt 18 (9+i) := by decide +kernel

theorem threshold_18_10 : ∀ i ∈ List.range 1, ThresholdAt 18 (10+i) := by decide +kernel

theorem threshold_18_11 : ∀ i ∈ List.range 1, ThresholdAt 18 (11+i) := by decide +kernel

theorem threshold_18_12 : ∀ i ∈ List.range 1, ThresholdAt 18 (12+i) := by decide +kernel

theorem threshold_18_13 : ∀ i ∈ List.range 1, ThresholdAt 18 (13+i) := by decide +kernel

theorem threshold_18_14 : ∀ i ∈ List.range 1, ThresholdAt 18 (14+i) := by decide +kernel

theorem threshold_18_15 : ∀ i ∈ List.range 1, ThresholdAt 18 (15+i) := by decide +kernel

theorem threshold_18_16 : ∀ i ∈ List.range 1, ThresholdAt 18 (16+i) := by decide +kernel

theorem threshold_18_17 : ∀ i ∈ List.range 1, ThresholdAt 18 (17+i) := by decide +kernel

theorem threshold_18_18 : ∀ i ∈ List.range 1, ThresholdAt 18 (18+i) := by decide +kernel

theorem threshold_18_19 : ∀ i ∈ List.range 1, ThresholdAt 18 (19+i) := by decide +kernel

theorem threshold_18_20 : ∀ i ∈ List.range 1, ThresholdAt 18 (20+i) := by decide +kernel

theorem threshold_18_21 : ∀ i ∈ List.range 1, ThresholdAt 18 (21+i) := by decide +kernel

theorem threshold_18_22 : ∀ i ∈ List.range 1, ThresholdAt 18 (22+i) := by decide +kernel

theorem threshold_18_23 : ∀ i ∈ List.range 1, ThresholdAt 18 (23+i) := by decide +kernel

theorem threshold_18_24 : ∀ i ∈ List.range 1, ThresholdAt 18 (24+i) := by decide +kernel

theorem threshold_18_25 : ∀ i ∈ List.range 1, ThresholdAt 18 (25+i) := by decide +kernel

theorem threshold_18_26 : ∀ i ∈ List.range 1, ThresholdAt 18 (26+i) := by decide +kernel

theorem threshold_18_27 : ∀ i ∈ List.range 1, ThresholdAt 18 (27+i) := by decide +kernel

theorem threshold_18_28 : ∀ i ∈ List.range 1, ThresholdAt 18 (28+i) := by decide +kernel

theorem threshold_18_29 : ∀ i ∈ List.range 1, ThresholdAt 18 (29+i) := by decide +kernel

theorem threshold_18_30 : ∀ i ∈ List.range 1, ThresholdAt 18 (30+i) := by decide +kernel

theorem threshold_18_31 : ∀ i ∈ List.range 1, ThresholdAt 18 (31+i) := by decide +kernel

theorem threshold_18_32 : ∀ i ∈ List.range 1, ThresholdAt 18 (32+i) := by decide +kernel

theorem threshold_18_33 : ∀ i ∈ List.range 1, ThresholdAt 18 (33+i) := by decide +kernel

theorem threshold_18_34 : ∀ i ∈ List.range 1, ThresholdAt 18 (34+i) := by decide +kernel

theorem threshold_18_35 : ∀ i ∈ List.range 1, ThresholdAt 18 (35+i) := by decide +kernel

theorem threshold_18_36 : ∀ i ∈ List.range 1, ThresholdAt 18 (36+i) := by decide +kernel

theorem threshold_18_37 : ∀ i ∈ List.range 1, ThresholdAt 18 (37+i) := by decide +kernel

theorem threshold_18_38 : ∀ i ∈ List.range 1, ThresholdAt 18 (38+i) := by decide +kernel

theorem threshold_18_39 : ∀ i ∈ List.range 1, ThresholdAt 18 (39+i) := by decide +kernel

theorem threshold_18_40 : ∀ i ∈ List.range 1, ThresholdAt 18 (40+i) := by decide +kernel

theorem threshold_18_41 : ∀ i ∈ List.range 1, ThresholdAt 18 (41+i) := by decide +kernel

theorem threshold_18_42 : ∀ i ∈ List.range 1, ThresholdAt 18 (42+i) := by decide +kernel

theorem threshold_18_43 : ∀ i ∈ List.range 1, ThresholdAt 18 (43+i) := by decide +kernel

theorem threshold_18_44 : ∀ i ∈ List.range 1, ThresholdAt 18 (44+i) := by decide +kernel

theorem threshold_18_45 : ∀ i ∈ List.range 1, ThresholdAt 18 (45+i) := by decide +kernel

theorem threshold_18_46 : ∀ i ∈ List.range 1, ThresholdAt 18 (46+i) := by decide +kernel

theorem threshold_18_47 : ∀ i ∈ List.range 1, ThresholdAt 18 (47+i) := by decide +kernel

theorem threshold_18_48 : ∀ i ∈ List.range 1, ThresholdAt 18 (48+i) := by decide +kernel

theorem threshold_18_49 : ∀ i ∈ List.range 1, ThresholdAt 18 (49+i) := by decide +kernel

theorem threshold_18_50 : ∀ i ∈ List.range 1, ThresholdAt 18 (50+i) := by decide +kernel

theorem threshold_18_51 : ∀ i ∈ List.range 1, ThresholdAt 18 (51+i) := by decide +kernel

theorem threshold_18_52 : ∀ i ∈ List.range 1, ThresholdAt 18 (52+i) := by decide +kernel

theorem threshold_18_53 : ∀ i ∈ List.range 1, ThresholdAt 18 (53+i) := by decide +kernel

theorem threshold_18_54 : ∀ i ∈ List.range 1, ThresholdAt 18 (54+i) := by decide +kernel

theorem threshold_18_55 : ∀ i ∈ List.range 1, ThresholdAt 18 (55+i) := by decide +kernel

theorem threshold_18_56 : ∀ i ∈ List.range 1, ThresholdAt 18 (56+i) := by decide +kernel

theorem threshold_18_57 : ∀ i ∈ List.range 1, ThresholdAt 18 (57+i) := by decide +kernel

theorem threshold_18_58 : ∀ i ∈ List.range 1, ThresholdAt 18 (58+i) := by decide +kernel

theorem threshold_18_59 : ∀ i ∈ List.range 1, ThresholdAt 18 (59+i) := by decide +kernel

theorem threshold_18_60 : ∀ i ∈ List.range 1, ThresholdAt 18 (60+i) := by decide +kernel

theorem threshold_18_61 : ∀ i ∈ List.range 1, ThresholdAt 18 (61+i) := by decide +kernel

theorem threshold_18_62 : ∀ i ∈ List.range 1, ThresholdAt 18 (62+i) := by decide +kernel

theorem threshold_18_63 : ∀ i ∈ List.range 1, ThresholdAt 18 (63+i) := by decide +kernel

theorem threshold_18_64 : ∀ i ∈ List.range 1, ThresholdAt 18 (64+i) := by decide +kernel

theorem threshold_18_65 : ∀ i ∈ List.range 1, ThresholdAt 18 (65+i) := by decide +kernel

theorem threshold_18_66 : ∀ i ∈ List.range 1, ThresholdAt 18 (66+i) := by decide +kernel

theorem threshold_18_67 : ∀ i ∈ List.range 1, ThresholdAt 18 (67+i) := by decide +kernel

theorem threshold_18_68 : ∀ i ∈ List.range 1, ThresholdAt 18 (68+i) := by decide +kernel

theorem threshold_18_69 : ∀ i ∈ List.range 1, ThresholdAt 18 (69+i) := by decide +kernel

theorem threshold_18_70 : ∀ i ∈ List.range 1, ThresholdAt 18 (70+i) := by decide +kernel

theorem threshold_18_71 : ∀ i ∈ List.range 1, ThresholdAt 18 (71+i) := by decide +kernel

theorem threshold_18_72 : ∀ i ∈ List.range 1, ThresholdAt 18 (72+i) := by decide +kernel

theorem threshold_18_73 : ∀ i ∈ List.range 1, ThresholdAt 18 (73+i) := by decide +kernel

theorem threshold_18_74 : ∀ i ∈ List.range 1, ThresholdAt 18 (74+i) := by decide +kernel

theorem threshold_18_75 : ∀ i ∈ List.range 1, ThresholdAt 18 (75+i) := by decide +kernel

theorem threshold_18_76 : ∀ i ∈ List.range 1, ThresholdAt 18 (76+i) := by decide +kernel

theorem threshold_18_77 : ∀ i ∈ List.range 1, ThresholdAt 18 (77+i) := by decide +kernel

theorem threshold_18_78 : ∀ i ∈ List.range 1, ThresholdAt 18 (78+i) := by decide +kernel

theorem threshold_18_79 : ∀ i ∈ List.range 1, ThresholdAt 18 (79+i) := by decide +kernel

theorem threshold_18_80 : ∀ i ∈ List.range 1, ThresholdAt 18 (80+i) := by decide +kernel

theorem threshold_18_81 : ∀ i ∈ List.range 1, ThresholdAt 18 (81+i) := by decide +kernel

theorem threshold_18_82 : ∀ i ∈ List.range 1, ThresholdAt 18 (82+i) := by decide +kernel

theorem threshold_18_83 : ∀ i ∈ List.range 1, ThresholdAt 18 (83+i) := by decide +kernel

theorem threshold_18_84 : ∀ i ∈ List.range 1, ThresholdAt 18 (84+i) := by decide +kernel

theorem threshold_18_85 : ∀ i ∈ List.range 1, ThresholdAt 18 (85+i) := by decide +kernel

theorem threshold_18_86 : ∀ i ∈ List.range 1, ThresholdAt 18 (86+i) := by decide +kernel

theorem threshold_18_87 : ∀ i ∈ List.range 1, ThresholdAt 18 (87+i) := by decide +kernel

theorem threshold_18_88 : ∀ i ∈ List.range 1, ThresholdAt 18 (88+i) := by decide +kernel

theorem threshold_18_89 : ∀ i ∈ List.range 1, ThresholdAt 18 (89+i) := by decide +kernel

theorem threshold_18_90 : ∀ i ∈ List.range 1, ThresholdAt 18 (90+i) := by decide +kernel

theorem threshold_18_91 : ∀ i ∈ List.range 1, ThresholdAt 18 (91+i) := by decide +kernel

theorem threshold_18_92 : ∀ i ∈ List.range 1, ThresholdAt 18 (92+i) := by decide +kernel

theorem threshold_18_93 : ∀ i ∈ List.range 1, ThresholdAt 18 (93+i) := by decide +kernel

theorem threshold_18_94 : ∀ i ∈ List.range 1, ThresholdAt 18 (94+i) := by decide +kernel

theorem threshold_18_95 : ∀ i ∈ List.range 1, ThresholdAt 18 (95+i) := by decide +kernel

theorem threshold_18_96 : ∀ i ∈ List.range 1, ThresholdAt 18 (96+i) := by decide +kernel

theorem threshold_18_97 : ∀ i ∈ List.range 1, ThresholdAt 18 (97+i) := by decide +kernel

theorem threshold_18_98 : ∀ i ∈ List.range 1, ThresholdAt 18 (98+i) := by decide +kernel

theorem threshold_18_99 : ∀ i ∈ List.range 1, ThresholdAt 18 (99+i) := by decide +kernel

theorem threshold_18_100 : ∀ i ∈ List.range 1, ThresholdAt 18 (100+i) := by decide +kernel

theorem threshold_18_101 : ∀ i ∈ List.range 1, ThresholdAt 18 (101+i) := by decide +kernel

theorem threshold_18_102 : ∀ i ∈ List.range 1, ThresholdAt 18 (102+i) := by decide +kernel

theorem threshold_18_103 : ∀ i ∈ List.range 1, ThresholdAt 18 (103+i) := by decide +kernel

theorem threshold_18_104 : ∀ i ∈ List.range 1, ThresholdAt 18 (104+i) := by decide +kernel

theorem threshold_18_105 : ∀ i ∈ List.range 1, ThresholdAt 18 (105+i) := by decide +kernel

theorem threshold_18_106 : ∀ i ∈ List.range 1, ThresholdAt 18 (106+i) := by decide +kernel

theorem threshold_18_107 : ∀ i ∈ List.range 1, ThresholdAt 18 (107+i) := by decide +kernel

theorem threshold_18_108 : ∀ i ∈ List.range 1, ThresholdAt 18 (108+i) := by decide +kernel

theorem threshold_18_109 : ∀ i ∈ List.range 1, ThresholdAt 18 (109+i) := by decide +kernel

theorem threshold_18_110 : ∀ i ∈ List.range 1, ThresholdAt 18 (110+i) := by decide +kernel

theorem threshold_18_111 : ∀ i ∈ List.range 1, ThresholdAt 18 (111+i) := by decide +kernel

theorem threshold_18_112 : ∀ i ∈ List.range 1, ThresholdAt 18 (112+i) := by decide +kernel

theorem threshold_18_113 : ∀ i ∈ List.range 1, ThresholdAt 18 (113+i) := by decide +kernel

theorem threshold_18_114 : ∀ i ∈ List.range 1, ThresholdAt 18 (114+i) := by decide +kernel

theorem threshold_18_115 : ∀ i ∈ List.range 1, ThresholdAt 18 (115+i) := by decide +kernel

theorem threshold_18_116 : ∀ i ∈ List.range 1, ThresholdAt 18 (116+i) := by decide +kernel

theorem threshold_18_117 : ∀ i ∈ List.range 1, ThresholdAt 18 (117+i) := by decide +kernel

theorem threshold_18_118 : ∀ i ∈ List.range 1, ThresholdAt 18 (118+i) := by decide +kernel

theorem threshold_18_119 : ∀ i ∈ List.range 1, ThresholdAt 18 (119+i) := by decide +kernel

theorem threshold_18_120 : ∀ i ∈ List.range 1, ThresholdAt 18 (120+i) := by decide +kernel

theorem threshold_18_121 : ∀ i ∈ List.range 1, ThresholdAt 18 (121+i) := by decide +kernel

theorem threshold_18_122 : ∀ i ∈ List.range 1, ThresholdAt 18 (122+i) := by decide +kernel

theorem threshold_18_123 : ∀ i ∈ List.range 1, ThresholdAt 18 (123+i) := by decide +kernel

theorem threshold_18_124 : ∀ i ∈ List.range 1, ThresholdAt 18 (124+i) := by decide +kernel

theorem threshold_18_125 : ∀ i ∈ List.range 1, ThresholdAt 18 (125+i) := by decide +kernel

theorem threshold_18_126 : ∀ i ∈ List.range 1, ThresholdAt 18 (126+i) := by decide +kernel

theorem threshold_18_127 : ∀ i ∈ List.range 1, ThresholdAt 18 (127+i) := by decide +kernel

theorem threshold_18_128 : ∀ i ∈ List.range 1, ThresholdAt 18 (128+i) := by decide +kernel

theorem threshold_18 (v : ℕ) (hv : v ∈ List.range 129) : ThresholdAt 18 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 18 v)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_18_0 threshold_18_1) (join 2 1 1 threshold_18_2 threshold_18_3)) (join 4 2 2 (join 4 1 1 threshold_18_4 threshold_18_5) (join 6 1 1 threshold_18_6 threshold_18_7))) (join 8 4 4 (join 8 2 2 (join 8 1 1 threshold_18_8 threshold_18_9) (join 10 1 1 threshold_18_10 threshold_18_11)) (join 12 2 2 (join 12 1 1 threshold_18_12 threshold_18_13) (join 14 1 1 threshold_18_14 threshold_18_15)))) (join 16 8 8 (join 16 4 4 (join 16 2 2 (join 16 1 1 threshold_18_16 threshold_18_17) (join 18 1 1 threshold_18_18 threshold_18_19)) (join 20 2 2 (join 20 1 1 threshold_18_20 threshold_18_21) (join 22 1 1 threshold_18_22 threshold_18_23))) (join 24 4 4 (join 24 2 2 (join 24 1 1 threshold_18_24 threshold_18_25) (join 26 1 1 threshold_18_26 threshold_18_27)) (join 28 2 2 (join 28 1 1 threshold_18_28 threshold_18_29) (join 30 1 1 threshold_18_30 threshold_18_31))))) (join 32 16 16 (join 32 8 8 (join 32 4 4 (join 32 2 2 (join 32 1 1 threshold_18_32 threshold_18_33) (join 34 1 1 threshold_18_34 threshold_18_35)) (join 36 2 2 (join 36 1 1 threshold_18_36 threshold_18_37) (join 38 1 1 threshold_18_38 threshold_18_39))) (join 40 4 4 (join 40 2 2 (join 40 1 1 threshold_18_40 threshold_18_41) (join 42 1 1 threshold_18_42 threshold_18_43)) (join 44 2 2 (join 44 1 1 threshold_18_44 threshold_18_45) (join 46 1 1 threshold_18_46 threshold_18_47)))) (join 48 8 8 (join 48 4 4 (join 48 2 2 (join 48 1 1 threshold_18_48 threshold_18_49) (join 50 1 1 threshold_18_50 threshold_18_51)) (join 52 2 2 (join 52 1 1 threshold_18_52 threshold_18_53) (join 54 1 1 threshold_18_54 threshold_18_55))) (join 56 4 4 (join 56 2 2 (join 56 1 1 threshold_18_56 threshold_18_57) (join 58 1 1 threshold_18_58 threshold_18_59)) (join 60 2 2 (join 60 1 1 threshold_18_60 threshold_18_61) (join 62 1 1 threshold_18_62 threshold_18_63)))))) (join 64 32 33 (join 64 16 16 (join 64 8 8 (join 64 4 4 (join 64 2 2 (join 64 1 1 threshold_18_64 threshold_18_65) (join 66 1 1 threshold_18_66 threshold_18_67)) (join 68 2 2 (join 68 1 1 threshold_18_68 threshold_18_69) (join 70 1 1 threshold_18_70 threshold_18_71))) (join 72 4 4 (join 72 2 2 (join 72 1 1 threshold_18_72 threshold_18_73) (join 74 1 1 threshold_18_74 threshold_18_75)) (join 76 2 2 (join 76 1 1 threshold_18_76 threshold_18_77) (join 78 1 1 threshold_18_78 threshold_18_79)))) (join 80 8 8 (join 80 4 4 (join 80 2 2 (join 80 1 1 threshold_18_80 threshold_18_81) (join 82 1 1 threshold_18_82 threshold_18_83)) (join 84 2 2 (join 84 1 1 threshold_18_84 threshold_18_85) (join 86 1 1 threshold_18_86 threshold_18_87))) (join 88 4 4 (join 88 2 2 (join 88 1 1 threshold_18_88 threshold_18_89) (join 90 1 1 threshold_18_90 threshold_18_91)) (join 92 2 2 (join 92 1 1 threshold_18_92 threshold_18_93) (join 94 1 1 threshold_18_94 threshold_18_95))))) (join 96 16 17 (join 96 8 8 (join 96 4 4 (join 96 2 2 (join 96 1 1 threshold_18_96 threshold_18_97) (join 98 1 1 threshold_18_98 threshold_18_99)) (join 100 2 2 (join 100 1 1 threshold_18_100 threshold_18_101) (join 102 1 1 threshold_18_102 threshold_18_103))) (join 104 4 4 (join 104 2 2 (join 104 1 1 threshold_18_104 threshold_18_105) (join 106 1 1 threshold_18_106 threshold_18_107)) (join 108 2 2 (join 108 1 1 threshold_18_108 threshold_18_109) (join 110 1 1 threshold_18_110 threshold_18_111)))) (join 112 8 9 (join 112 4 4 (join 112 2 2 (join 112 1 1 threshold_18_112 threshold_18_113) (join 114 1 1 threshold_18_114 threshold_18_115)) (join 116 2 2 (join 116 1 1 threshold_18_116 threshold_18_117) (join 118 1 1 threshold_18_118 threshold_18_119))) (join 120 4 5 (join 120 2 2 (join 120 1 1 threshold_18_120 threshold_18_121) (join 122 1 1 threshold_18_122 threshold_18_123)) (join 124 2 3 (join 124 1 1 threshold_18_124 threshold_18_125) (join 126 1 2 threshold_18_126 (join 127 1 1 threshold_18_127 threshold_18_128))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_18_0 : ∀ i ∈ List.range 4, LedgerAt 18 (0+i) := by decide +kernel

theorem ledger_18_4 : ∀ i ∈ List.range 4, LedgerAt 18 (4+i) := by decide +kernel

theorem ledger_18_8 : ∀ i ∈ List.range 4, LedgerAt 18 (8+i) := by decide +kernel

theorem ledger_18_12 : ∀ i ∈ List.range 4, LedgerAt 18 (12+i) := by decide +kernel

theorem ledger_18_16 : ∀ i ∈ List.range 4, LedgerAt 18 (16+i) := by decide +kernel

theorem ledger_18_20 : ∀ i ∈ List.range 4, LedgerAt 18 (20+i) := by decide +kernel

theorem ledger_18_24 : ∀ i ∈ List.range 4, LedgerAt 18 (24+i) := by decide +kernel

theorem ledger_18_28 : ∀ i ∈ List.range 4, LedgerAt 18 (28+i) := by decide +kernel

theorem ledger_18_32 : ∀ i ∈ List.range 4, LedgerAt 18 (32+i) := by decide +kernel

theorem ledger_18_36 : ∀ i ∈ List.range 4, LedgerAt 18 (36+i) := by decide +kernel

theorem ledger_18_40 : ∀ i ∈ List.range 4, LedgerAt 18 (40+i) := by decide +kernel

theorem ledger_18_44 : ∀ i ∈ List.range 4, LedgerAt 18 (44+i) := by decide +kernel

theorem ledger_18_48 : ∀ i ∈ List.range 4, LedgerAt 18 (48+i) := by decide +kernel

theorem ledger_18_52 : ∀ i ∈ List.range 4, LedgerAt 18 (52+i) := by decide +kernel

theorem ledger_18_56 : ∀ i ∈ List.range 4, LedgerAt 18 (56+i) := by decide +kernel

theorem ledger_18_60 : ∀ i ∈ List.range 4, LedgerAt 18 (60+i) := by decide +kernel

theorem ledger_18_64 : ∀ i ∈ List.range 4, LedgerAt 18 (64+i) := by decide +kernel

theorem ledger_18_68 : ∀ i ∈ List.range 4, LedgerAt 18 (68+i) := by decide +kernel

theorem ledger_18_72 : ∀ i ∈ List.range 4, LedgerAt 18 (72+i) := by decide +kernel

theorem ledger_18_76 : ∀ i ∈ List.range 4, LedgerAt 18 (76+i) := by decide +kernel

theorem ledger_18_80 : ∀ i ∈ List.range 4, LedgerAt 18 (80+i) := by decide +kernel

theorem ledger_18_84 : ∀ i ∈ List.range 4, LedgerAt 18 (84+i) := by decide +kernel

theorem ledger_18_88 : ∀ i ∈ List.range 4, LedgerAt 18 (88+i) := by decide +kernel

theorem ledger_18_92 : ∀ i ∈ List.range 4, LedgerAt 18 (92+i) := by decide +kernel

theorem ledger_18_96 : ∀ i ∈ List.range 4, LedgerAt 18 (96+i) := by decide +kernel

theorem ledger_18_100 : ∀ i ∈ List.range 4, LedgerAt 18 (100+i) := by decide +kernel

theorem ledger_18_104 : ∀ i ∈ List.range 4, LedgerAt 18 (104+i) := by decide +kernel

theorem ledger_18_108 : ∀ i ∈ List.range 4, LedgerAt 18 (108+i) := by decide +kernel

theorem ledger_18_112 : ∀ i ∈ List.range 4, LedgerAt 18 (112+i) := by decide +kernel

theorem ledger_18_116 : ∀ i ∈ List.range 4, LedgerAt 18 (116+i) := by decide +kernel

theorem ledger_18_120 : ∀ i ∈ List.range 4, LedgerAt 18 (120+i) := by decide +kernel

theorem ledger_18_124 : ∀ i ∈ List.range 4, LedgerAt 18 (124+i) := by decide +kernel

theorem ledger_18_128 : ∀ i ∈ List.range 1, LedgerAt 18 (128+i) := by decide +kernel

theorem ledger_18 (v : ℕ) (hv : v ∈ List.range 129) : LedgerAt 18 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 18 v)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_18_0 ledger_18_4) (join 8 4 4 ledger_18_8 ledger_18_12)) (join 16 8 8 (join 16 4 4 ledger_18_16 ledger_18_20) (join 24 4 4 ledger_18_24 ledger_18_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_18_32 ledger_18_36) (join 40 4 4 ledger_18_40 ledger_18_44)) (join 48 8 8 (join 48 4 4 ledger_18_48 ledger_18_52) (join 56 4 4 ledger_18_56 ledger_18_60)))) (join 64 32 33 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_18_64 ledger_18_68) (join 72 4 4 ledger_18_72 ledger_18_76)) (join 80 8 8 (join 80 4 4 ledger_18_80 ledger_18_84) (join 88 4 4 ledger_18_88 ledger_18_92))) (join 96 16 17 (join 96 8 8 (join 96 4 4 ledger_18_96 ledger_18_100) (join 104 4 4 ledger_18_104 ledger_18_108)) (join 112 8 9 (join 112 4 4 ledger_18_112 ledger_18_116) (join 120 4 5 ledger_18_120 (join 124 4 1 ledger_18_124 ledger_18_128))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
