import ProximityPrize.SubmissionLower.BoundaryTailCheckedR226807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_23_0 : ∀ i ∈ List.range 4, GeometryAt 23 (0+i) := by decide +kernel

theorem geometry_23_4 : ∀ i ∈ List.range 4, GeometryAt 23 (4+i) := by decide +kernel

theorem geometry_23_8 : ∀ i ∈ List.range 4, GeometryAt 23 (8+i) := by decide +kernel

theorem geometry_23_12 : ∀ i ∈ List.range 4, GeometryAt 23 (12+i) := by decide +kernel

theorem geometry_23_16 : ∀ i ∈ List.range 4, GeometryAt 23 (16+i) := by decide +kernel

theorem geometry_23_20 : ∀ i ∈ List.range 4, GeometryAt 23 (20+i) := by decide +kernel

theorem geometry_23_24 : ∀ i ∈ List.range 4, GeometryAt 23 (24+i) := by decide +kernel

theorem geometry_23_28 : ∀ i ∈ List.range 4, GeometryAt 23 (28+i) := by decide +kernel

theorem geometry_23_32 : ∀ i ∈ List.range 4, GeometryAt 23 (32+i) := by decide +kernel

theorem geometry_23_36 : ∀ i ∈ List.range 4, GeometryAt 23 (36+i) := by decide +kernel

theorem geometry_23_40 : ∀ i ∈ List.range 4, GeometryAt 23 (40+i) := by decide +kernel

theorem geometry_23_44 : ∀ i ∈ List.range 4, GeometryAt 23 (44+i) := by decide +kernel

theorem geometry_23_48 : ∀ i ∈ List.range 4, GeometryAt 23 (48+i) := by decide +kernel

theorem geometry_23_52 : ∀ i ∈ List.range 4, GeometryAt 23 (52+i) := by decide +kernel

theorem geometry_23_56 : ∀ i ∈ List.range 4, GeometryAt 23 (56+i) := by decide +kernel

theorem geometry_23_60 : ∀ i ∈ List.range 4, GeometryAt 23 (60+i) := by decide +kernel

theorem geometry_23_64 : ∀ i ∈ List.range 4, GeometryAt 23 (64+i) := by decide +kernel

theorem geometry_23_68 : ∀ i ∈ List.range 4, GeometryAt 23 (68+i) := by decide +kernel

theorem geometry_23_72 : ∀ i ∈ List.range 4, GeometryAt 23 (72+i) := by decide +kernel

theorem geometry_23_76 : ∀ i ∈ List.range 4, GeometryAt 23 (76+i) := by decide +kernel

theorem geometry_23_80 : ∀ i ∈ List.range 4, GeometryAt 23 (80+i) := by decide +kernel

theorem geometry_23_84 : ∀ i ∈ List.range 4, GeometryAt 23 (84+i) := by decide +kernel

theorem geometry_23_88 : ∀ i ∈ List.range 4, GeometryAt 23 (88+i) := by decide +kernel

theorem geometry_23_92 : ∀ i ∈ List.range 4, GeometryAt 23 (92+i) := by decide +kernel

theorem geometry_23_96 : ∀ i ∈ List.range 4, GeometryAt 23 (96+i) := by decide +kernel

theorem geometry_23_100 : ∀ i ∈ List.range 4, GeometryAt 23 (100+i) := by decide +kernel

theorem geometry_23_104 : ∀ i ∈ List.range 4, GeometryAt 23 (104+i) := by decide +kernel

theorem geometry_23_108 : ∀ i ∈ List.range 4, GeometryAt 23 (108+i) := by decide +kernel

theorem geometry_23_112 : ∀ i ∈ List.range 4, GeometryAt 23 (112+i) := by decide +kernel

theorem geometry_23_116 : ∀ i ∈ List.range 4, GeometryAt 23 (116+i) := by decide +kernel

theorem geometry_23_120 : ∀ i ∈ List.range 4, GeometryAt 23 (120+i) := by decide +kernel

theorem geometry_23 (v : ℕ) (hv : v ∈ List.range 124) : GeometryAt 23 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 23 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 geometry_23_0 (join 4 4 4 geometry_23_4 geometry_23_8)) (join 12 8 8 (join 12 4 4 geometry_23_12 geometry_23_16) (join 20 4 4 geometry_23_20 geometry_23_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 geometry_23_28 geometry_23_32) (join 36 4 4 geometry_23_36 geometry_23_40)) (join 44 8 8 (join 44 4 4 geometry_23_44 geometry_23_48) (join 52 4 4 geometry_23_52 geometry_23_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 geometry_23_60 geometry_23_64) (join 68 4 4 geometry_23_68 geometry_23_72)) (join 76 8 8 (join 76 4 4 geometry_23_76 geometry_23_80) (join 84 4 4 geometry_23_84 geometry_23_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 geometry_23_92 geometry_23_96) (join 100 4 4 geometry_23_100 geometry_23_104)) (join 108 8 8 (join 108 4 4 geometry_23_108 geometry_23_112) (join 116 4 4 geometry_23_116 geometry_23_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_23_0 : ∀ i ∈ List.range 4, StrictAt 23 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (0+i)) 23 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_4 : ∀ i ∈ List.range 4, StrictAt 23 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (4+i)) 23 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_8 : ∀ i ∈ List.range 4, StrictAt 23 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (8+i)) 23 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_12 : ∀ i ∈ List.range 4, StrictAt 23 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (12+i)) 23 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_16 : ∀ i ∈ List.range 4, StrictAt 23 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (16+i)) 23 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_20 : ∀ i ∈ List.range 4, StrictAt 23 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (20+i)) 23 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_24 : ∀ i ∈ List.range 4, StrictAt 23 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (24+i)) 23 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_28 : ∀ i ∈ List.range 4, StrictAt 23 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (28+i)) 23 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_32 : ∀ i ∈ List.range 4, StrictAt 23 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (32+i)) 23 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_36 : ∀ i ∈ List.range 4, StrictAt 23 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (36+i)) 23 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_40 : ∀ i ∈ List.range 4, StrictAt 23 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (40+i)) 23 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_44 : ∀ i ∈ List.range 4, StrictAt 23 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (44+i)) 23 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_48 : ∀ i ∈ List.range 4, StrictAt 23 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (48+i)) 23 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_52 : ∀ i ∈ List.range 4, StrictAt 23 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (52+i)) 23 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_56 : ∀ i ∈ List.range 4, StrictAt 23 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (56+i)) 23 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_60 : ∀ i ∈ List.range 4, StrictAt 23 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (60+i)) 23 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_64 : ∀ i ∈ List.range 4, StrictAt 23 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (64+i)) 23 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_68 : ∀ i ∈ List.range 4, StrictAt 23 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (68+i)) 23 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_72 : ∀ i ∈ List.range 4, StrictAt 23 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (72+i)) 23 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_76 : ∀ i ∈ List.range 4, StrictAt 23 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (76+i)) 23 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_80 : ∀ i ∈ List.range 4, StrictAt 23 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (80+i)) 23 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_84 : ∀ i ∈ List.range 4, StrictAt 23 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (84+i)) 23 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_88 : ∀ i ∈ List.range 4, StrictAt 23 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (88+i)) 23 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_92 : ∀ i ∈ List.range 4, StrictAt 23 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (92+i)) 23 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_96 : ∀ i ∈ List.range 4, StrictAt 23 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (96+i)) 23 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_100 : ∀ i ∈ List.range 4, StrictAt 23 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (100+i)) 23 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_104 : ∀ i ∈ List.range 4, StrictAt 23 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (104+i)) 23 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_108 : ∀ i ∈ List.range 4, StrictAt 23 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (108+i)) 23 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_112 : ∀ i ∈ List.range 4, StrictAt 23 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (112+i)) 23 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_116 : ∀ i ∈ List.range 4, StrictAt 23 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (116+i)) 23 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23_120 : ∀ i ∈ List.range 4, StrictAt 23 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 23 (120+i)) 23 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_23 (v : ℕ) (hv : v ∈ List.range 124) : StrictAt 23 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 23 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 strict_23_0 (join 4 4 4 strict_23_4 strict_23_8)) (join 12 8 8 (join 12 4 4 strict_23_12 strict_23_16) (join 20 4 4 strict_23_20 strict_23_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 strict_23_28 strict_23_32) (join 36 4 4 strict_23_36 strict_23_40)) (join 44 8 8 (join 44 4 4 strict_23_44 strict_23_48) (join 52 4 4 strict_23_52 strict_23_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 strict_23_60 strict_23_64) (join 68 4 4 strict_23_68 strict_23_72)) (join 76 8 8 (join 76 4 4 strict_23_76 strict_23_80) (join 84 4 4 strict_23_84 strict_23_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 strict_23_92 strict_23_96) (join 100 4 4 strict_23_100 strict_23_104)) (join 108 8 8 (join 108 4 4 strict_23_108 strict_23_112) (join 116 4 4 strict_23_116 strict_23_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_23_0 : ∀ i ∈ List.range 4, PhaseAt 23 (0+i) := by decide +kernel

theorem phase_23_4 : ∀ i ∈ List.range 4, PhaseAt 23 (4+i) := by decide +kernel

theorem phase_23_8 : ∀ i ∈ List.range 4, PhaseAt 23 (8+i) := by decide +kernel

theorem phase_23_12 : ∀ i ∈ List.range 4, PhaseAt 23 (12+i) := by decide +kernel

theorem phase_23_16 : ∀ i ∈ List.range 4, PhaseAt 23 (16+i) := by decide +kernel

theorem phase_23_20 : ∀ i ∈ List.range 4, PhaseAt 23 (20+i) := by decide +kernel

theorem phase_23_24 : ∀ i ∈ List.range 4, PhaseAt 23 (24+i) := by decide +kernel

theorem phase_23_28 : ∀ i ∈ List.range 4, PhaseAt 23 (28+i) := by decide +kernel

theorem phase_23_32 : ∀ i ∈ List.range 4, PhaseAt 23 (32+i) := by decide +kernel

theorem phase_23_36 : ∀ i ∈ List.range 4, PhaseAt 23 (36+i) := by decide +kernel

theorem phase_23_40 : ∀ i ∈ List.range 4, PhaseAt 23 (40+i) := by decide +kernel

theorem phase_23_44 : ∀ i ∈ List.range 4, PhaseAt 23 (44+i) := by decide +kernel

theorem phase_23_48 : ∀ i ∈ List.range 4, PhaseAt 23 (48+i) := by decide +kernel

theorem phase_23_52 : ∀ i ∈ List.range 4, PhaseAt 23 (52+i) := by decide +kernel

theorem phase_23_56 : ∀ i ∈ List.range 4, PhaseAt 23 (56+i) := by decide +kernel

theorem phase_23_60 : ∀ i ∈ List.range 4, PhaseAt 23 (60+i) := by decide +kernel

theorem phase_23_64 : ∀ i ∈ List.range 4, PhaseAt 23 (64+i) := by decide +kernel

theorem phase_23_68 : ∀ i ∈ List.range 4, PhaseAt 23 (68+i) := by decide +kernel

theorem phase_23_72 : ∀ i ∈ List.range 4, PhaseAt 23 (72+i) := by decide +kernel

theorem phase_23_76 : ∀ i ∈ List.range 4, PhaseAt 23 (76+i) := by decide +kernel

theorem phase_23_80 : ∀ i ∈ List.range 4, PhaseAt 23 (80+i) := by decide +kernel

theorem phase_23_84 : ∀ i ∈ List.range 4, PhaseAt 23 (84+i) := by decide +kernel

theorem phase_23_88 : ∀ i ∈ List.range 4, PhaseAt 23 (88+i) := by decide +kernel

theorem phase_23_92 : ∀ i ∈ List.range 4, PhaseAt 23 (92+i) := by decide +kernel

theorem phase_23_96 : ∀ i ∈ List.range 4, PhaseAt 23 (96+i) := by decide +kernel

theorem phase_23_100 : ∀ i ∈ List.range 4, PhaseAt 23 (100+i) := by decide +kernel

theorem phase_23_104 : ∀ i ∈ List.range 4, PhaseAt 23 (104+i) := by decide +kernel

theorem phase_23_108 : ∀ i ∈ List.range 4, PhaseAt 23 (108+i) := by decide +kernel

theorem phase_23_112 : ∀ i ∈ List.range 4, PhaseAt 23 (112+i) := by decide +kernel

theorem phase_23_116 : ∀ i ∈ List.range 4, PhaseAt 23 (116+i) := by decide +kernel

theorem phase_23_120 : ∀ i ∈ List.range 4, PhaseAt 23 (120+i) := by decide +kernel

theorem phase_23 (v : ℕ) (hv : v ∈ List.range 124) : PhaseAt 23 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 23 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_23_0 (join 4 4 4 phase_23_4 phase_23_8)) (join 12 8 8 (join 12 4 4 phase_23_12 phase_23_16) (join 20 4 4 phase_23_20 phase_23_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_23_28 phase_23_32) (join 36 4 4 phase_23_36 phase_23_40)) (join 44 8 8 (join 44 4 4 phase_23_44 phase_23_48) (join 52 4 4 phase_23_52 phase_23_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 phase_23_60 phase_23_64) (join 68 4 4 phase_23_68 phase_23_72)) (join 76 8 8 (join 76 4 4 phase_23_76 phase_23_80) (join 84 4 4 phase_23_84 phase_23_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 phase_23_92 phase_23_96) (join 100 4 4 phase_23_100 phase_23_104)) (join 108 8 8 (join 108 4 4 phase_23_108 phase_23_112) (join 116 4 4 phase_23_116 phase_23_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_23_0 : ∀ i ∈ List.range 1, ThresholdAt 23 (0+i) := by decide +kernel

theorem threshold_23_1 : ∀ i ∈ List.range 1, ThresholdAt 23 (1+i) := by decide +kernel

theorem threshold_23_2 : ∀ i ∈ List.range 1, ThresholdAt 23 (2+i) := by decide +kernel

theorem threshold_23_3 : ∀ i ∈ List.range 1, ThresholdAt 23 (3+i) := by decide +kernel

theorem threshold_23_4 : ∀ i ∈ List.range 1, ThresholdAt 23 (4+i) := by decide +kernel

theorem threshold_23_5 : ∀ i ∈ List.range 1, ThresholdAt 23 (5+i) := by decide +kernel

theorem threshold_23_6 : ∀ i ∈ List.range 1, ThresholdAt 23 (6+i) := by decide +kernel

theorem threshold_23_7 : ∀ i ∈ List.range 1, ThresholdAt 23 (7+i) := by decide +kernel

theorem threshold_23_8 : ∀ i ∈ List.range 1, ThresholdAt 23 (8+i) := by decide +kernel

theorem threshold_23_9 : ∀ i ∈ List.range 1, ThresholdAt 23 (9+i) := by decide +kernel

theorem threshold_23_10 : ∀ i ∈ List.range 1, ThresholdAt 23 (10+i) := by decide +kernel

theorem threshold_23_11 : ∀ i ∈ List.range 1, ThresholdAt 23 (11+i) := by decide +kernel

theorem threshold_23_12 : ∀ i ∈ List.range 1, ThresholdAt 23 (12+i) := by decide +kernel

theorem threshold_23_13 : ∀ i ∈ List.range 1, ThresholdAt 23 (13+i) := by decide +kernel

theorem threshold_23_14 : ∀ i ∈ List.range 1, ThresholdAt 23 (14+i) := by decide +kernel

theorem threshold_23_15 : ∀ i ∈ List.range 1, ThresholdAt 23 (15+i) := by decide +kernel

theorem threshold_23_16 : ∀ i ∈ List.range 1, ThresholdAt 23 (16+i) := by decide +kernel

theorem threshold_23_17 : ∀ i ∈ List.range 1, ThresholdAt 23 (17+i) := by decide +kernel

theorem threshold_23_18 : ∀ i ∈ List.range 1, ThresholdAt 23 (18+i) := by decide +kernel

theorem threshold_23_19 : ∀ i ∈ List.range 1, ThresholdAt 23 (19+i) := by decide +kernel

theorem threshold_23_20 : ∀ i ∈ List.range 1, ThresholdAt 23 (20+i) := by decide +kernel

theorem threshold_23_21 : ∀ i ∈ List.range 1, ThresholdAt 23 (21+i) := by decide +kernel

theorem threshold_23_22 : ∀ i ∈ List.range 1, ThresholdAt 23 (22+i) := by decide +kernel

theorem threshold_23_23 : ∀ i ∈ List.range 1, ThresholdAt 23 (23+i) := by decide +kernel

theorem threshold_23_24 : ∀ i ∈ List.range 1, ThresholdAt 23 (24+i) := by decide +kernel

theorem threshold_23_25 : ∀ i ∈ List.range 1, ThresholdAt 23 (25+i) := by decide +kernel

theorem threshold_23_26 : ∀ i ∈ List.range 1, ThresholdAt 23 (26+i) := by decide +kernel

theorem threshold_23_27 : ∀ i ∈ List.range 1, ThresholdAt 23 (27+i) := by decide +kernel

theorem threshold_23_28 : ∀ i ∈ List.range 1, ThresholdAt 23 (28+i) := by decide +kernel

theorem threshold_23_29 : ∀ i ∈ List.range 1, ThresholdAt 23 (29+i) := by decide +kernel

theorem threshold_23_30 : ∀ i ∈ List.range 1, ThresholdAt 23 (30+i) := by decide +kernel

theorem threshold_23_31 : ∀ i ∈ List.range 1, ThresholdAt 23 (31+i) := by decide +kernel

theorem threshold_23_32 : ∀ i ∈ List.range 1, ThresholdAt 23 (32+i) := by decide +kernel

theorem threshold_23_33 : ∀ i ∈ List.range 1, ThresholdAt 23 (33+i) := by decide +kernel

theorem threshold_23_34 : ∀ i ∈ List.range 1, ThresholdAt 23 (34+i) := by decide +kernel

theorem threshold_23_35 : ∀ i ∈ List.range 1, ThresholdAt 23 (35+i) := by decide +kernel

theorem threshold_23_36 : ∀ i ∈ List.range 1, ThresholdAt 23 (36+i) := by decide +kernel

theorem threshold_23_37 : ∀ i ∈ List.range 1, ThresholdAt 23 (37+i) := by decide +kernel

theorem threshold_23_38 : ∀ i ∈ List.range 1, ThresholdAt 23 (38+i) := by decide +kernel

theorem threshold_23_39 : ∀ i ∈ List.range 1, ThresholdAt 23 (39+i) := by decide +kernel

theorem threshold_23_40 : ∀ i ∈ List.range 1, ThresholdAt 23 (40+i) := by decide +kernel

theorem threshold_23_41 : ∀ i ∈ List.range 1, ThresholdAt 23 (41+i) := by decide +kernel

theorem threshold_23_42 : ∀ i ∈ List.range 1, ThresholdAt 23 (42+i) := by decide +kernel

theorem threshold_23_43 : ∀ i ∈ List.range 1, ThresholdAt 23 (43+i) := by decide +kernel

theorem threshold_23_44 : ∀ i ∈ List.range 1, ThresholdAt 23 (44+i) := by decide +kernel

theorem threshold_23_45 : ∀ i ∈ List.range 1, ThresholdAt 23 (45+i) := by decide +kernel

theorem threshold_23_46 : ∀ i ∈ List.range 1, ThresholdAt 23 (46+i) := by decide +kernel

theorem threshold_23_47 : ∀ i ∈ List.range 1, ThresholdAt 23 (47+i) := by decide +kernel

theorem threshold_23_48 : ∀ i ∈ List.range 1, ThresholdAt 23 (48+i) := by decide +kernel

theorem threshold_23_49 : ∀ i ∈ List.range 1, ThresholdAt 23 (49+i) := by decide +kernel

theorem threshold_23_50 : ∀ i ∈ List.range 1, ThresholdAt 23 (50+i) := by decide +kernel

theorem threshold_23_51 : ∀ i ∈ List.range 1, ThresholdAt 23 (51+i) := by decide +kernel

theorem threshold_23_52 : ∀ i ∈ List.range 1, ThresholdAt 23 (52+i) := by decide +kernel

theorem threshold_23_53 : ∀ i ∈ List.range 1, ThresholdAt 23 (53+i) := by decide +kernel

theorem threshold_23_54 : ∀ i ∈ List.range 1, ThresholdAt 23 (54+i) := by decide +kernel

theorem threshold_23_55 : ∀ i ∈ List.range 1, ThresholdAt 23 (55+i) := by decide +kernel

theorem threshold_23_56 : ∀ i ∈ List.range 1, ThresholdAt 23 (56+i) := by decide +kernel

theorem threshold_23_57 : ∀ i ∈ List.range 1, ThresholdAt 23 (57+i) := by decide +kernel

theorem threshold_23_58 : ∀ i ∈ List.range 1, ThresholdAt 23 (58+i) := by decide +kernel

theorem threshold_23_59 : ∀ i ∈ List.range 1, ThresholdAt 23 (59+i) := by decide +kernel

theorem threshold_23_60 : ∀ i ∈ List.range 1, ThresholdAt 23 (60+i) := by decide +kernel

theorem threshold_23_61 : ∀ i ∈ List.range 1, ThresholdAt 23 (61+i) := by decide +kernel

theorem threshold_23_62 : ∀ i ∈ List.range 1, ThresholdAt 23 (62+i) := by decide +kernel

theorem threshold_23_63 : ∀ i ∈ List.range 1, ThresholdAt 23 (63+i) := by decide +kernel

theorem threshold_23_64 : ∀ i ∈ List.range 1, ThresholdAt 23 (64+i) := by decide +kernel

theorem threshold_23_65 : ∀ i ∈ List.range 1, ThresholdAt 23 (65+i) := by decide +kernel

theorem threshold_23_66 : ∀ i ∈ List.range 1, ThresholdAt 23 (66+i) := by decide +kernel

theorem threshold_23_67 : ∀ i ∈ List.range 1, ThresholdAt 23 (67+i) := by decide +kernel

theorem threshold_23_68 : ∀ i ∈ List.range 1, ThresholdAt 23 (68+i) := by decide +kernel

theorem threshold_23_69 : ∀ i ∈ List.range 1, ThresholdAt 23 (69+i) := by decide +kernel

theorem threshold_23_70 : ∀ i ∈ List.range 1, ThresholdAt 23 (70+i) := by decide +kernel

theorem threshold_23_71 : ∀ i ∈ List.range 1, ThresholdAt 23 (71+i) := by decide +kernel

theorem threshold_23_72 : ∀ i ∈ List.range 1, ThresholdAt 23 (72+i) := by decide +kernel

theorem threshold_23_73 : ∀ i ∈ List.range 1, ThresholdAt 23 (73+i) := by decide +kernel

theorem threshold_23_74 : ∀ i ∈ List.range 1, ThresholdAt 23 (74+i) := by decide +kernel

theorem threshold_23_75 : ∀ i ∈ List.range 1, ThresholdAt 23 (75+i) := by decide +kernel

theorem threshold_23_76 : ∀ i ∈ List.range 1, ThresholdAt 23 (76+i) := by decide +kernel

theorem threshold_23_77 : ∀ i ∈ List.range 1, ThresholdAt 23 (77+i) := by decide +kernel

theorem threshold_23_78 : ∀ i ∈ List.range 1, ThresholdAt 23 (78+i) := by decide +kernel

theorem threshold_23_79 : ∀ i ∈ List.range 1, ThresholdAt 23 (79+i) := by decide +kernel

theorem threshold_23_80 : ∀ i ∈ List.range 1, ThresholdAt 23 (80+i) := by decide +kernel

theorem threshold_23_81 : ∀ i ∈ List.range 1, ThresholdAt 23 (81+i) := by decide +kernel

theorem threshold_23_82 : ∀ i ∈ List.range 1, ThresholdAt 23 (82+i) := by decide +kernel

theorem threshold_23_83 : ∀ i ∈ List.range 1, ThresholdAt 23 (83+i) := by decide +kernel

theorem threshold_23_84 : ∀ i ∈ List.range 1, ThresholdAt 23 (84+i) := by decide +kernel

theorem threshold_23_85 : ∀ i ∈ List.range 1, ThresholdAt 23 (85+i) := by decide +kernel

theorem threshold_23_86 : ∀ i ∈ List.range 1, ThresholdAt 23 (86+i) := by decide +kernel

theorem threshold_23_87 : ∀ i ∈ List.range 1, ThresholdAt 23 (87+i) := by decide +kernel

theorem threshold_23_88 : ∀ i ∈ List.range 1, ThresholdAt 23 (88+i) := by decide +kernel

theorem threshold_23_89 : ∀ i ∈ List.range 1, ThresholdAt 23 (89+i) := by decide +kernel

theorem threshold_23_90 : ∀ i ∈ List.range 1, ThresholdAt 23 (90+i) := by decide +kernel

theorem threshold_23_91 : ∀ i ∈ List.range 1, ThresholdAt 23 (91+i) := by decide +kernel

theorem threshold_23_92 : ∀ i ∈ List.range 1, ThresholdAt 23 (92+i) := by decide +kernel

theorem threshold_23_93 : ∀ i ∈ List.range 1, ThresholdAt 23 (93+i) := by decide +kernel

theorem threshold_23_94 : ∀ i ∈ List.range 1, ThresholdAt 23 (94+i) := by decide +kernel

theorem threshold_23_95 : ∀ i ∈ List.range 1, ThresholdAt 23 (95+i) := by decide +kernel

theorem threshold_23_96 : ∀ i ∈ List.range 1, ThresholdAt 23 (96+i) := by decide +kernel

theorem threshold_23_97 : ∀ i ∈ List.range 1, ThresholdAt 23 (97+i) := by decide +kernel

theorem threshold_23_98 : ∀ i ∈ List.range 1, ThresholdAt 23 (98+i) := by decide +kernel

theorem threshold_23_99 : ∀ i ∈ List.range 1, ThresholdAt 23 (99+i) := by decide +kernel

theorem threshold_23_100 : ∀ i ∈ List.range 1, ThresholdAt 23 (100+i) := by decide +kernel

theorem threshold_23_101 : ∀ i ∈ List.range 1, ThresholdAt 23 (101+i) := by decide +kernel

theorem threshold_23_102 : ∀ i ∈ List.range 1, ThresholdAt 23 (102+i) := by decide +kernel

theorem threshold_23_103 : ∀ i ∈ List.range 1, ThresholdAt 23 (103+i) := by decide +kernel

theorem threshold_23_104 : ∀ i ∈ List.range 1, ThresholdAt 23 (104+i) := by decide +kernel

theorem threshold_23_105 : ∀ i ∈ List.range 1, ThresholdAt 23 (105+i) := by decide +kernel

theorem threshold_23_106 : ∀ i ∈ List.range 1, ThresholdAt 23 (106+i) := by decide +kernel

theorem threshold_23_107 : ∀ i ∈ List.range 1, ThresholdAt 23 (107+i) := by decide +kernel

theorem threshold_23_108 : ∀ i ∈ List.range 1, ThresholdAt 23 (108+i) := by decide +kernel

theorem threshold_23_109 : ∀ i ∈ List.range 1, ThresholdAt 23 (109+i) := by decide +kernel

theorem threshold_23_110 : ∀ i ∈ List.range 1, ThresholdAt 23 (110+i) := by decide +kernel

theorem threshold_23_111 : ∀ i ∈ List.range 1, ThresholdAt 23 (111+i) := by decide +kernel

theorem threshold_23_112 : ∀ i ∈ List.range 1, ThresholdAt 23 (112+i) := by decide +kernel

theorem threshold_23_113 : ∀ i ∈ List.range 1, ThresholdAt 23 (113+i) := by decide +kernel

theorem threshold_23_114 : ∀ i ∈ List.range 1, ThresholdAt 23 (114+i) := by decide +kernel

theorem threshold_23_115 : ∀ i ∈ List.range 1, ThresholdAt 23 (115+i) := by decide +kernel

theorem threshold_23_116 : ∀ i ∈ List.range 1, ThresholdAt 23 (116+i) := by decide +kernel

theorem threshold_23_117 : ∀ i ∈ List.range 1, ThresholdAt 23 (117+i) := by decide +kernel

theorem threshold_23_118 : ∀ i ∈ List.range 1, ThresholdAt 23 (118+i) := by decide +kernel

theorem threshold_23_119 : ∀ i ∈ List.range 1, ThresholdAt 23 (119+i) := by decide +kernel

theorem threshold_23_120 : ∀ i ∈ List.range 1, ThresholdAt 23 (120+i) := by decide +kernel

theorem threshold_23_121 : ∀ i ∈ List.range 1, ThresholdAt 23 (121+i) := by decide +kernel

theorem threshold_23_122 : ∀ i ∈ List.range 1, ThresholdAt 23 (122+i) := by decide +kernel

theorem threshold_23_123 : ∀ i ∈ List.range 1, ThresholdAt 23 (123+i) := by decide +kernel

theorem threshold_23 (v : ℕ) (hv : v ∈ List.range 124) : ThresholdAt 23 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 23 v)
  have h := (join 0 62 62 (join 0 31 31 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_23_0 (join 1 1 1 threshold_23_1 threshold_23_2)) (join 3 2 2 (join 3 1 1 threshold_23_3 threshold_23_4) (join 5 1 1 threshold_23_5 threshold_23_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_23_7 threshold_23_8) (join 9 1 1 threshold_23_9 threshold_23_10)) (join 11 2 2 (join 11 1 1 threshold_23_11 threshold_23_12) (join 13 1 1 threshold_23_13 threshold_23_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_23_15 threshold_23_16) (join 17 1 1 threshold_23_17 threshold_23_18)) (join 19 2 2 (join 19 1 1 threshold_23_19 threshold_23_20) (join 21 1 1 threshold_23_21 threshold_23_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_23_23 threshold_23_24) (join 25 1 1 threshold_23_25 threshold_23_26)) (join 27 2 2 (join 27 1 1 threshold_23_27 threshold_23_28) (join 29 1 1 threshold_23_29 threshold_23_30))))) (join 31 15 16 (join 31 7 8 (join 31 3 4 (join 31 1 2 threshold_23_31 (join 32 1 1 threshold_23_32 threshold_23_33)) (join 34 2 2 (join 34 1 1 threshold_23_34 threshold_23_35) (join 36 1 1 threshold_23_36 threshold_23_37))) (join 38 4 4 (join 38 2 2 (join 38 1 1 threshold_23_38 threshold_23_39) (join 40 1 1 threshold_23_40 threshold_23_41)) (join 42 2 2 (join 42 1 1 threshold_23_42 threshold_23_43) (join 44 1 1 threshold_23_44 threshold_23_45)))) (join 46 8 8 (join 46 4 4 (join 46 2 2 (join 46 1 1 threshold_23_46 threshold_23_47) (join 48 1 1 threshold_23_48 threshold_23_49)) (join 50 2 2 (join 50 1 1 threshold_23_50 threshold_23_51) (join 52 1 1 threshold_23_52 threshold_23_53))) (join 54 4 4 (join 54 2 2 (join 54 1 1 threshold_23_54 threshold_23_55) (join 56 1 1 threshold_23_56 threshold_23_57)) (join 58 2 2 (join 58 1 1 threshold_23_58 threshold_23_59) (join 60 1 1 threshold_23_60 threshold_23_61)))))) (join 62 31 31 (join 62 15 16 (join 62 7 8 (join 62 3 4 (join 62 1 2 threshold_23_62 (join 63 1 1 threshold_23_63 threshold_23_64)) (join 65 2 2 (join 65 1 1 threshold_23_65 threshold_23_66) (join 67 1 1 threshold_23_67 threshold_23_68))) (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_23_69 threshold_23_70) (join 71 1 1 threshold_23_71 threshold_23_72)) (join 73 2 2 (join 73 1 1 threshold_23_73 threshold_23_74) (join 75 1 1 threshold_23_75 threshold_23_76)))) (join 77 8 8 (join 77 4 4 (join 77 2 2 (join 77 1 1 threshold_23_77 threshold_23_78) (join 79 1 1 threshold_23_79 threshold_23_80)) (join 81 2 2 (join 81 1 1 threshold_23_81 threshold_23_82) (join 83 1 1 threshold_23_83 threshold_23_84))) (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_23_85 threshold_23_86) (join 87 1 1 threshold_23_87 threshold_23_88)) (join 89 2 2 (join 89 1 1 threshold_23_89 threshold_23_90) (join 91 1 1 threshold_23_91 threshold_23_92))))) (join 93 15 16 (join 93 7 8 (join 93 3 4 (join 93 1 2 threshold_23_93 (join 94 1 1 threshold_23_94 threshold_23_95)) (join 96 2 2 (join 96 1 1 threshold_23_96 threshold_23_97) (join 98 1 1 threshold_23_98 threshold_23_99))) (join 100 4 4 (join 100 2 2 (join 100 1 1 threshold_23_100 threshold_23_101) (join 102 1 1 threshold_23_102 threshold_23_103)) (join 104 2 2 (join 104 1 1 threshold_23_104 threshold_23_105) (join 106 1 1 threshold_23_106 threshold_23_107)))) (join 108 8 8 (join 108 4 4 (join 108 2 2 (join 108 1 1 threshold_23_108 threshold_23_109) (join 110 1 1 threshold_23_110 threshold_23_111)) (join 112 2 2 (join 112 1 1 threshold_23_112 threshold_23_113) (join 114 1 1 threshold_23_114 threshold_23_115))) (join 116 4 4 (join 116 2 2 (join 116 1 1 threshold_23_116 threshold_23_117) (join 118 1 1 threshold_23_118 threshold_23_119)) (join 120 2 2 (join 120 1 1 threshold_23_120 threshold_23_121) (join 122 1 1 threshold_23_122 threshold_23_123)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_23_0 : ∀ i ∈ List.range 4, LedgerAt 23 (0+i) := by decide +kernel

theorem ledger_23_4 : ∀ i ∈ List.range 4, LedgerAt 23 (4+i) := by decide +kernel

theorem ledger_23_8 : ∀ i ∈ List.range 4, LedgerAt 23 (8+i) := by decide +kernel

theorem ledger_23_12 : ∀ i ∈ List.range 4, LedgerAt 23 (12+i) := by decide +kernel

theorem ledger_23_16 : ∀ i ∈ List.range 4, LedgerAt 23 (16+i) := by decide +kernel

theorem ledger_23_20 : ∀ i ∈ List.range 4, LedgerAt 23 (20+i) := by decide +kernel

theorem ledger_23_24 : ∀ i ∈ List.range 4, LedgerAt 23 (24+i) := by decide +kernel

theorem ledger_23_28 : ∀ i ∈ List.range 4, LedgerAt 23 (28+i) := by decide +kernel

theorem ledger_23_32 : ∀ i ∈ List.range 4, LedgerAt 23 (32+i) := by decide +kernel

theorem ledger_23_36 : ∀ i ∈ List.range 4, LedgerAt 23 (36+i) := by decide +kernel

theorem ledger_23_40 : ∀ i ∈ List.range 4, LedgerAt 23 (40+i) := by decide +kernel

theorem ledger_23_44 : ∀ i ∈ List.range 4, LedgerAt 23 (44+i) := by decide +kernel

theorem ledger_23_48 : ∀ i ∈ List.range 4, LedgerAt 23 (48+i) := by decide +kernel

theorem ledger_23_52 : ∀ i ∈ List.range 4, LedgerAt 23 (52+i) := by decide +kernel

theorem ledger_23_56 : ∀ i ∈ List.range 4, LedgerAt 23 (56+i) := by decide +kernel

theorem ledger_23_60 : ∀ i ∈ List.range 4, LedgerAt 23 (60+i) := by decide +kernel

theorem ledger_23_64 : ∀ i ∈ List.range 4, LedgerAt 23 (64+i) := by decide +kernel

theorem ledger_23_68 : ∀ i ∈ List.range 4, LedgerAt 23 (68+i) := by decide +kernel

theorem ledger_23_72 : ∀ i ∈ List.range 4, LedgerAt 23 (72+i) := by decide +kernel

theorem ledger_23_76 : ∀ i ∈ List.range 4, LedgerAt 23 (76+i) := by decide +kernel

theorem ledger_23_80 : ∀ i ∈ List.range 4, LedgerAt 23 (80+i) := by decide +kernel

theorem ledger_23_84 : ∀ i ∈ List.range 4, LedgerAt 23 (84+i) := by decide +kernel

theorem ledger_23_88 : ∀ i ∈ List.range 4, LedgerAt 23 (88+i) := by decide +kernel

theorem ledger_23_92 : ∀ i ∈ List.range 4, LedgerAt 23 (92+i) := by decide +kernel

theorem ledger_23_96 : ∀ i ∈ List.range 4, LedgerAt 23 (96+i) := by decide +kernel

theorem ledger_23_100 : ∀ i ∈ List.range 4, LedgerAt 23 (100+i) := by decide +kernel

theorem ledger_23_104 : ∀ i ∈ List.range 4, LedgerAt 23 (104+i) := by decide +kernel

theorem ledger_23_108 : ∀ i ∈ List.range 4, LedgerAt 23 (108+i) := by decide +kernel

theorem ledger_23_112 : ∀ i ∈ List.range 4, LedgerAt 23 (112+i) := by decide +kernel

theorem ledger_23_116 : ∀ i ∈ List.range 4, LedgerAt 23 (116+i) := by decide +kernel

theorem ledger_23_120 : ∀ i ∈ List.range 4, LedgerAt 23 (120+i) := by decide +kernel

theorem ledger_23 (v : ℕ) (hv : v ∈ List.range 124) : LedgerAt 23 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 23 v)
  have h := (join 0 60 64 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_23_0 (join 4 4 4 ledger_23_4 ledger_23_8)) (join 12 8 8 (join 12 4 4 ledger_23_12 ledger_23_16) (join 20 4 4 ledger_23_20 ledger_23_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_23_28 ledger_23_32) (join 36 4 4 ledger_23_36 ledger_23_40)) (join 44 8 8 (join 44 4 4 ledger_23_44 ledger_23_48) (join 52 4 4 ledger_23_52 ledger_23_56)))) (join 60 32 32 (join 60 16 16 (join 60 8 8 (join 60 4 4 ledger_23_60 ledger_23_64) (join 68 4 4 ledger_23_68 ledger_23_72)) (join 76 8 8 (join 76 4 4 ledger_23_76 ledger_23_80) (join 84 4 4 ledger_23_84 ledger_23_88))) (join 92 16 16 (join 92 8 8 (join 92 4 4 ledger_23_92 ledger_23_96) (join 100 4 4 ledger_23_100 ledger_23_104)) (join 108 8 8 (join 108 4 4 ledger_23_108 ledger_23_112) (join 116 4 4 ledger_23_116 ledger_23_120)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
