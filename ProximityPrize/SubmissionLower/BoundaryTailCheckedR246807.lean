import ProximityPrize.SubmissionLower.BoundaryTailCheckedR236807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_24_0 : ∀ i ∈ List.range 4, GeometryAt 24 (0+i) := by decide +kernel

theorem geometry_24_4 : ∀ i ∈ List.range 4, GeometryAt 24 (4+i) := by decide +kernel

theorem geometry_24_8 : ∀ i ∈ List.range 4, GeometryAt 24 (8+i) := by decide +kernel

theorem geometry_24_12 : ∀ i ∈ List.range 4, GeometryAt 24 (12+i) := by decide +kernel

theorem geometry_24_16 : ∀ i ∈ List.range 4, GeometryAt 24 (16+i) := by decide +kernel

theorem geometry_24_20 : ∀ i ∈ List.range 4, GeometryAt 24 (20+i) := by decide +kernel

theorem geometry_24_24 : ∀ i ∈ List.range 4, GeometryAt 24 (24+i) := by decide +kernel

theorem geometry_24_28 : ∀ i ∈ List.range 4, GeometryAt 24 (28+i) := by decide +kernel

theorem geometry_24_32 : ∀ i ∈ List.range 4, GeometryAt 24 (32+i) := by decide +kernel

theorem geometry_24_36 : ∀ i ∈ List.range 4, GeometryAt 24 (36+i) := by decide +kernel

theorem geometry_24_40 : ∀ i ∈ List.range 4, GeometryAt 24 (40+i) := by decide +kernel

theorem geometry_24_44 : ∀ i ∈ List.range 4, GeometryAt 24 (44+i) := by decide +kernel

theorem geometry_24_48 : ∀ i ∈ List.range 4, GeometryAt 24 (48+i) := by decide +kernel

theorem geometry_24_52 : ∀ i ∈ List.range 4, GeometryAt 24 (52+i) := by decide +kernel

theorem geometry_24_56 : ∀ i ∈ List.range 4, GeometryAt 24 (56+i) := by decide +kernel

theorem geometry_24_60 : ∀ i ∈ List.range 4, GeometryAt 24 (60+i) := by decide +kernel

theorem geometry_24_64 : ∀ i ∈ List.range 4, GeometryAt 24 (64+i) := by decide +kernel

theorem geometry_24_68 : ∀ i ∈ List.range 4, GeometryAt 24 (68+i) := by decide +kernel

theorem geometry_24_72 : ∀ i ∈ List.range 4, GeometryAt 24 (72+i) := by decide +kernel

theorem geometry_24_76 : ∀ i ∈ List.range 4, GeometryAt 24 (76+i) := by decide +kernel

theorem geometry_24_80 : ∀ i ∈ List.range 4, GeometryAt 24 (80+i) := by decide +kernel

theorem geometry_24_84 : ∀ i ∈ List.range 4, GeometryAt 24 (84+i) := by decide +kernel

theorem geometry_24_88 : ∀ i ∈ List.range 4, GeometryAt 24 (88+i) := by decide +kernel

theorem geometry_24_92 : ∀ i ∈ List.range 4, GeometryAt 24 (92+i) := by decide +kernel

theorem geometry_24_96 : ∀ i ∈ List.range 4, GeometryAt 24 (96+i) := by decide +kernel

theorem geometry_24_100 : ∀ i ∈ List.range 4, GeometryAt 24 (100+i) := by decide +kernel

theorem geometry_24_104 : ∀ i ∈ List.range 4, GeometryAt 24 (104+i) := by decide +kernel

theorem geometry_24_108 : ∀ i ∈ List.range 4, GeometryAt 24 (108+i) := by decide +kernel

theorem geometry_24_112 : ∀ i ∈ List.range 4, GeometryAt 24 (112+i) := by decide +kernel

theorem geometry_24_116 : ∀ i ∈ List.range 4, GeometryAt 24 (116+i) := by decide +kernel

theorem geometry_24_120 : ∀ i ∈ List.range 3, GeometryAt 24 (120+i) := by decide +kernel

theorem geometry_24 (v : ℕ) (hv : v ∈ List.range 123) : GeometryAt 24 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 24 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 geometry_24_0 (join 4 4 4 geometry_24_4 geometry_24_8)) (join 12 8 8 (join 12 4 4 geometry_24_12 geometry_24_16) (join 20 4 4 geometry_24_20 geometry_24_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 geometry_24_28 geometry_24_32) (join 36 4 4 geometry_24_36 geometry_24_40)) (join 44 8 8 (join 44 4 4 geometry_24_44 geometry_24_48) (join 52 4 4 geometry_24_52 geometry_24_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 geometry_24_60 geometry_24_64) (join 68 4 4 geometry_24_68 geometry_24_72)) (join 76 8 8 (join 76 4 4 geometry_24_76 geometry_24_80) (join 84 4 4 geometry_24_84 geometry_24_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 geometry_24_92 geometry_24_96) (join 100 4 4 geometry_24_100 geometry_24_104)) (join 108 8 7 (join 108 4 4 geometry_24_108 geometry_24_112) (join 116 4 3 geometry_24_116 geometry_24_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_24_0 : ∀ i ∈ List.range 4, StrictAt 24 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (0+i)) 24 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_4 : ∀ i ∈ List.range 4, StrictAt 24 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (4+i)) 24 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_8 : ∀ i ∈ List.range 4, StrictAt 24 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (8+i)) 24 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_12 : ∀ i ∈ List.range 4, StrictAt 24 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (12+i)) 24 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_16 : ∀ i ∈ List.range 4, StrictAt 24 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (16+i)) 24 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_20 : ∀ i ∈ List.range 4, StrictAt 24 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (20+i)) 24 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_24 : ∀ i ∈ List.range 4, StrictAt 24 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (24+i)) 24 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_28 : ∀ i ∈ List.range 4, StrictAt 24 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (28+i)) 24 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_32 : ∀ i ∈ List.range 4, StrictAt 24 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (32+i)) 24 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_36 : ∀ i ∈ List.range 4, StrictAt 24 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (36+i)) 24 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_40 : ∀ i ∈ List.range 4, StrictAt 24 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (40+i)) 24 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_44 : ∀ i ∈ List.range 4, StrictAt 24 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (44+i)) 24 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_48 : ∀ i ∈ List.range 4, StrictAt 24 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (48+i)) 24 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_52 : ∀ i ∈ List.range 4, StrictAt 24 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (52+i)) 24 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_56 : ∀ i ∈ List.range 4, StrictAt 24 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (56+i)) 24 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_60 : ∀ i ∈ List.range 4, StrictAt 24 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (60+i)) 24 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_64 : ∀ i ∈ List.range 4, StrictAt 24 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (64+i)) 24 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_68 : ∀ i ∈ List.range 4, StrictAt 24 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (68+i)) 24 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_72 : ∀ i ∈ List.range 4, StrictAt 24 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (72+i)) 24 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_76 : ∀ i ∈ List.range 4, StrictAt 24 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (76+i)) 24 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_80 : ∀ i ∈ List.range 4, StrictAt 24 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (80+i)) 24 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_84 : ∀ i ∈ List.range 4, StrictAt 24 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (84+i)) 24 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_88 : ∀ i ∈ List.range 4, StrictAt 24 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (88+i)) 24 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_92 : ∀ i ∈ List.range 4, StrictAt 24 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (92+i)) 24 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_96 : ∀ i ∈ List.range 4, StrictAt 24 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (96+i)) 24 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_100 : ∀ i ∈ List.range 4, StrictAt 24 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (100+i)) 24 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_104 : ∀ i ∈ List.range 4, StrictAt 24 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (104+i)) 24 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_108 : ∀ i ∈ List.range 4, StrictAt 24 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (108+i)) 24 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_112 : ∀ i ∈ List.range 4, StrictAt 24 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (112+i)) 24 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_116 : ∀ i ∈ List.range 4, StrictAt 24 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (116+i)) 24 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24_120 : ∀ i ∈ List.range 3, StrictAt 24 (120+i) := by
  have h : ∀ i ∈ List.range 3, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 24 (120+i)) 24 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_24 (v : ℕ) (hv : v ∈ List.range 123) : StrictAt 24 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 24 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 strict_24_0 (join 4 4 4 strict_24_4 strict_24_8)) (join 12 8 8 (join 12 4 4 strict_24_12 strict_24_16) (join 20 4 4 strict_24_20 strict_24_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 strict_24_28 strict_24_32) (join 36 4 4 strict_24_36 strict_24_40)) (join 44 8 8 (join 44 4 4 strict_24_44 strict_24_48) (join 52 4 4 strict_24_52 strict_24_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 strict_24_60 strict_24_64) (join 68 4 4 strict_24_68 strict_24_72)) (join 76 8 8 (join 76 4 4 strict_24_76 strict_24_80) (join 84 4 4 strict_24_84 strict_24_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 strict_24_92 strict_24_96) (join 100 4 4 strict_24_100 strict_24_104)) (join 108 8 7 (join 108 4 4 strict_24_108 strict_24_112) (join 116 4 3 strict_24_116 strict_24_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_24_0 : ∀ i ∈ List.range 4, PhaseAt 24 (0+i) := by decide +kernel

theorem phase_24_4 : ∀ i ∈ List.range 4, PhaseAt 24 (4+i) := by decide +kernel

theorem phase_24_8 : ∀ i ∈ List.range 4, PhaseAt 24 (8+i) := by decide +kernel

theorem phase_24_12 : ∀ i ∈ List.range 4, PhaseAt 24 (12+i) := by decide +kernel

theorem phase_24_16 : ∀ i ∈ List.range 4, PhaseAt 24 (16+i) := by decide +kernel

theorem phase_24_20 : ∀ i ∈ List.range 4, PhaseAt 24 (20+i) := by decide +kernel

theorem phase_24_24 : ∀ i ∈ List.range 4, PhaseAt 24 (24+i) := by decide +kernel

theorem phase_24_28 : ∀ i ∈ List.range 4, PhaseAt 24 (28+i) := by decide +kernel

theorem phase_24_32 : ∀ i ∈ List.range 4, PhaseAt 24 (32+i) := by decide +kernel

theorem phase_24_36 : ∀ i ∈ List.range 4, PhaseAt 24 (36+i) := by decide +kernel

theorem phase_24_40 : ∀ i ∈ List.range 4, PhaseAt 24 (40+i) := by decide +kernel

theorem phase_24_44 : ∀ i ∈ List.range 4, PhaseAt 24 (44+i) := by decide +kernel

theorem phase_24_48 : ∀ i ∈ List.range 4, PhaseAt 24 (48+i) := by decide +kernel

theorem phase_24_52 : ∀ i ∈ List.range 4, PhaseAt 24 (52+i) := by decide +kernel

theorem phase_24_56 : ∀ i ∈ List.range 4, PhaseAt 24 (56+i) := by decide +kernel

theorem phase_24_60 : ∀ i ∈ List.range 4, PhaseAt 24 (60+i) := by decide +kernel

theorem phase_24_64 : ∀ i ∈ List.range 4, PhaseAt 24 (64+i) := by decide +kernel

theorem phase_24_68 : ∀ i ∈ List.range 4, PhaseAt 24 (68+i) := by decide +kernel

theorem phase_24_72 : ∀ i ∈ List.range 4, PhaseAt 24 (72+i) := by decide +kernel

theorem phase_24_76 : ∀ i ∈ List.range 4, PhaseAt 24 (76+i) := by decide +kernel

theorem phase_24_80 : ∀ i ∈ List.range 4, PhaseAt 24 (80+i) := by decide +kernel

theorem phase_24_84 : ∀ i ∈ List.range 4, PhaseAt 24 (84+i) := by decide +kernel

theorem phase_24_88 : ∀ i ∈ List.range 4, PhaseAt 24 (88+i) := by decide +kernel

theorem phase_24_92 : ∀ i ∈ List.range 4, PhaseAt 24 (92+i) := by decide +kernel

theorem phase_24_96 : ∀ i ∈ List.range 4, PhaseAt 24 (96+i) := by decide +kernel

theorem phase_24_100 : ∀ i ∈ List.range 4, PhaseAt 24 (100+i) := by decide +kernel

theorem phase_24_104 : ∀ i ∈ List.range 4, PhaseAt 24 (104+i) := by decide +kernel

theorem phase_24_108 : ∀ i ∈ List.range 4, PhaseAt 24 (108+i) := by decide +kernel

theorem phase_24_112 : ∀ i ∈ List.range 4, PhaseAt 24 (112+i) := by decide +kernel

theorem phase_24_116 : ∀ i ∈ List.range 4, PhaseAt 24 (116+i) := by decide +kernel

theorem phase_24_120 : ∀ i ∈ List.range 3, PhaseAt 24 (120+i) := by decide +kernel

theorem phase_24 (v : ℕ) (hv : v ∈ List.range 123) : PhaseAt 24 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 24 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_24_0 (join 4 4 4 phase_24_4 phase_24_8)) (join 12 8 8 (join 12 4 4 phase_24_12 phase_24_16) (join 20 4 4 phase_24_20 phase_24_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_24_28 phase_24_32) (join 36 4 4 phase_24_36 phase_24_40)) (join 44 8 8 (join 44 4 4 phase_24_44 phase_24_48) (join 52 4 4 phase_24_52 phase_24_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 phase_24_60 phase_24_64) (join 68 4 4 phase_24_68 phase_24_72)) (join 76 8 8 (join 76 4 4 phase_24_76 phase_24_80) (join 84 4 4 phase_24_84 phase_24_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 phase_24_92 phase_24_96) (join 100 4 4 phase_24_100 phase_24_104)) (join 108 8 7 (join 108 4 4 phase_24_108 phase_24_112) (join 116 4 3 phase_24_116 phase_24_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_24_0 : ∀ i ∈ List.range 1, ThresholdAt 24 (0+i) := by decide +kernel

theorem threshold_24_1 : ∀ i ∈ List.range 1, ThresholdAt 24 (1+i) := by decide +kernel

theorem threshold_24_2 : ∀ i ∈ List.range 1, ThresholdAt 24 (2+i) := by decide +kernel

theorem threshold_24_3 : ∀ i ∈ List.range 1, ThresholdAt 24 (3+i) := by decide +kernel

theorem threshold_24_4 : ∀ i ∈ List.range 1, ThresholdAt 24 (4+i) := by decide +kernel

theorem threshold_24_5 : ∀ i ∈ List.range 1, ThresholdAt 24 (5+i) := by decide +kernel

theorem threshold_24_6 : ∀ i ∈ List.range 1, ThresholdAt 24 (6+i) := by decide +kernel

theorem threshold_24_7 : ∀ i ∈ List.range 1, ThresholdAt 24 (7+i) := by decide +kernel

theorem threshold_24_8 : ∀ i ∈ List.range 1, ThresholdAt 24 (8+i) := by decide +kernel

theorem threshold_24_9 : ∀ i ∈ List.range 1, ThresholdAt 24 (9+i) := by decide +kernel

theorem threshold_24_10 : ∀ i ∈ List.range 1, ThresholdAt 24 (10+i) := by decide +kernel

theorem threshold_24_11 : ∀ i ∈ List.range 1, ThresholdAt 24 (11+i) := by decide +kernel

theorem threshold_24_12 : ∀ i ∈ List.range 1, ThresholdAt 24 (12+i) := by decide +kernel

theorem threshold_24_13 : ∀ i ∈ List.range 1, ThresholdAt 24 (13+i) := by decide +kernel

theorem threshold_24_14 : ∀ i ∈ List.range 1, ThresholdAt 24 (14+i) := by decide +kernel

theorem threshold_24_15 : ∀ i ∈ List.range 1, ThresholdAt 24 (15+i) := by decide +kernel

theorem threshold_24_16 : ∀ i ∈ List.range 1, ThresholdAt 24 (16+i) := by decide +kernel

theorem threshold_24_17 : ∀ i ∈ List.range 1, ThresholdAt 24 (17+i) := by decide +kernel

theorem threshold_24_18 : ∀ i ∈ List.range 1, ThresholdAt 24 (18+i) := by decide +kernel

theorem threshold_24_19 : ∀ i ∈ List.range 1, ThresholdAt 24 (19+i) := by decide +kernel

theorem threshold_24_20 : ∀ i ∈ List.range 1, ThresholdAt 24 (20+i) := by decide +kernel

theorem threshold_24_21 : ∀ i ∈ List.range 1, ThresholdAt 24 (21+i) := by decide +kernel

theorem threshold_24_22 : ∀ i ∈ List.range 1, ThresholdAt 24 (22+i) := by decide +kernel

theorem threshold_24_23 : ∀ i ∈ List.range 1, ThresholdAt 24 (23+i) := by decide +kernel

theorem threshold_24_24 : ∀ i ∈ List.range 1, ThresholdAt 24 (24+i) := by decide +kernel

theorem threshold_24_25 : ∀ i ∈ List.range 1, ThresholdAt 24 (25+i) := by decide +kernel

theorem threshold_24_26 : ∀ i ∈ List.range 1, ThresholdAt 24 (26+i) := by decide +kernel

theorem threshold_24_27 : ∀ i ∈ List.range 1, ThresholdAt 24 (27+i) := by decide +kernel

theorem threshold_24_28 : ∀ i ∈ List.range 1, ThresholdAt 24 (28+i) := by decide +kernel

theorem threshold_24_29 : ∀ i ∈ List.range 1, ThresholdAt 24 (29+i) := by decide +kernel

theorem threshold_24_30 : ∀ i ∈ List.range 1, ThresholdAt 24 (30+i) := by decide +kernel

theorem threshold_24_31 : ∀ i ∈ List.range 1, ThresholdAt 24 (31+i) := by decide +kernel

theorem threshold_24_32 : ∀ i ∈ List.range 1, ThresholdAt 24 (32+i) := by decide +kernel

theorem threshold_24_33 : ∀ i ∈ List.range 1, ThresholdAt 24 (33+i) := by decide +kernel

theorem threshold_24_34 : ∀ i ∈ List.range 1, ThresholdAt 24 (34+i) := by decide +kernel

theorem threshold_24_35 : ∀ i ∈ List.range 1, ThresholdAt 24 (35+i) := by decide +kernel

theorem threshold_24_36 : ∀ i ∈ List.range 1, ThresholdAt 24 (36+i) := by decide +kernel

theorem threshold_24_37 : ∀ i ∈ List.range 1, ThresholdAt 24 (37+i) := by decide +kernel

theorem threshold_24_38 : ∀ i ∈ List.range 1, ThresholdAt 24 (38+i) := by decide +kernel

theorem threshold_24_39 : ∀ i ∈ List.range 1, ThresholdAt 24 (39+i) := by decide +kernel

theorem threshold_24_40 : ∀ i ∈ List.range 1, ThresholdAt 24 (40+i) := by decide +kernel

theorem threshold_24_41 : ∀ i ∈ List.range 1, ThresholdAt 24 (41+i) := by decide +kernel

theorem threshold_24_42 : ∀ i ∈ List.range 1, ThresholdAt 24 (42+i) := by decide +kernel

theorem threshold_24_43 : ∀ i ∈ List.range 1, ThresholdAt 24 (43+i) := by decide +kernel

theorem threshold_24_44 : ∀ i ∈ List.range 1, ThresholdAt 24 (44+i) := by decide +kernel

theorem threshold_24_45 : ∀ i ∈ List.range 1, ThresholdAt 24 (45+i) := by decide +kernel

theorem threshold_24_46 : ∀ i ∈ List.range 1, ThresholdAt 24 (46+i) := by decide +kernel

theorem threshold_24_47 : ∀ i ∈ List.range 1, ThresholdAt 24 (47+i) := by decide +kernel

theorem threshold_24_48 : ∀ i ∈ List.range 1, ThresholdAt 24 (48+i) := by decide +kernel

theorem threshold_24_49 : ∀ i ∈ List.range 1, ThresholdAt 24 (49+i) := by decide +kernel

theorem threshold_24_50 : ∀ i ∈ List.range 1, ThresholdAt 24 (50+i) := by decide +kernel

theorem threshold_24_51 : ∀ i ∈ List.range 1, ThresholdAt 24 (51+i) := by decide +kernel

theorem threshold_24_52 : ∀ i ∈ List.range 1, ThresholdAt 24 (52+i) := by decide +kernel

theorem threshold_24_53 : ∀ i ∈ List.range 1, ThresholdAt 24 (53+i) := by decide +kernel

theorem threshold_24_54 : ∀ i ∈ List.range 1, ThresholdAt 24 (54+i) := by decide +kernel

theorem threshold_24_55 : ∀ i ∈ List.range 1, ThresholdAt 24 (55+i) := by decide +kernel

theorem threshold_24_56 : ∀ i ∈ List.range 1, ThresholdAt 24 (56+i) := by decide +kernel

theorem threshold_24_57 : ∀ i ∈ List.range 1, ThresholdAt 24 (57+i) := by decide +kernel

theorem threshold_24_58 : ∀ i ∈ List.range 1, ThresholdAt 24 (58+i) := by decide +kernel

theorem threshold_24_59 : ∀ i ∈ List.range 1, ThresholdAt 24 (59+i) := by decide +kernel

theorem threshold_24_60 : ∀ i ∈ List.range 1, ThresholdAt 24 (60+i) := by decide +kernel

theorem threshold_24_61 : ∀ i ∈ List.range 1, ThresholdAt 24 (61+i) := by decide +kernel

theorem threshold_24_62 : ∀ i ∈ List.range 1, ThresholdAt 24 (62+i) := by decide +kernel

theorem threshold_24_63 : ∀ i ∈ List.range 1, ThresholdAt 24 (63+i) := by decide +kernel

theorem threshold_24_64 : ∀ i ∈ List.range 1, ThresholdAt 24 (64+i) := by decide +kernel

theorem threshold_24_65 : ∀ i ∈ List.range 1, ThresholdAt 24 (65+i) := by decide +kernel

theorem threshold_24_66 : ∀ i ∈ List.range 1, ThresholdAt 24 (66+i) := by decide +kernel

theorem threshold_24_67 : ∀ i ∈ List.range 1, ThresholdAt 24 (67+i) := by decide +kernel

theorem threshold_24_68 : ∀ i ∈ List.range 1, ThresholdAt 24 (68+i) := by decide +kernel

theorem threshold_24_69 : ∀ i ∈ List.range 1, ThresholdAt 24 (69+i) := by decide +kernel

theorem threshold_24_70 : ∀ i ∈ List.range 1, ThresholdAt 24 (70+i) := by decide +kernel

theorem threshold_24_71 : ∀ i ∈ List.range 1, ThresholdAt 24 (71+i) := by decide +kernel

theorem threshold_24_72 : ∀ i ∈ List.range 1, ThresholdAt 24 (72+i) := by decide +kernel

theorem threshold_24_73 : ∀ i ∈ List.range 1, ThresholdAt 24 (73+i) := by decide +kernel

theorem threshold_24_74 : ∀ i ∈ List.range 1, ThresholdAt 24 (74+i) := by decide +kernel

theorem threshold_24_75 : ∀ i ∈ List.range 1, ThresholdAt 24 (75+i) := by decide +kernel

theorem threshold_24_76 : ∀ i ∈ List.range 1, ThresholdAt 24 (76+i) := by decide +kernel

theorem threshold_24_77 : ∀ i ∈ List.range 1, ThresholdAt 24 (77+i) := by decide +kernel

theorem threshold_24_78 : ∀ i ∈ List.range 1, ThresholdAt 24 (78+i) := by decide +kernel

theorem threshold_24_79 : ∀ i ∈ List.range 1, ThresholdAt 24 (79+i) := by decide +kernel

theorem threshold_24_80 : ∀ i ∈ List.range 1, ThresholdAt 24 (80+i) := by decide +kernel

theorem threshold_24_81 : ∀ i ∈ List.range 1, ThresholdAt 24 (81+i) := by decide +kernel

theorem threshold_24_82 : ∀ i ∈ List.range 1, ThresholdAt 24 (82+i) := by decide +kernel

theorem threshold_24_83 : ∀ i ∈ List.range 1, ThresholdAt 24 (83+i) := by decide +kernel

theorem threshold_24_84 : ∀ i ∈ List.range 1, ThresholdAt 24 (84+i) := by decide +kernel

theorem threshold_24_85 : ∀ i ∈ List.range 1, ThresholdAt 24 (85+i) := by decide +kernel

theorem threshold_24_86 : ∀ i ∈ List.range 1, ThresholdAt 24 (86+i) := by decide +kernel

theorem threshold_24_87 : ∀ i ∈ List.range 1, ThresholdAt 24 (87+i) := by decide +kernel

theorem threshold_24_88 : ∀ i ∈ List.range 1, ThresholdAt 24 (88+i) := by decide +kernel

theorem threshold_24_89 : ∀ i ∈ List.range 1, ThresholdAt 24 (89+i) := by decide +kernel

theorem threshold_24_90 : ∀ i ∈ List.range 1, ThresholdAt 24 (90+i) := by decide +kernel

theorem threshold_24_91 : ∀ i ∈ List.range 1, ThresholdAt 24 (91+i) := by decide +kernel

theorem threshold_24_92 : ∀ i ∈ List.range 1, ThresholdAt 24 (92+i) := by decide +kernel

theorem threshold_24_93 : ∀ i ∈ List.range 1, ThresholdAt 24 (93+i) := by decide +kernel

theorem threshold_24_94 : ∀ i ∈ List.range 1, ThresholdAt 24 (94+i) := by decide +kernel

theorem threshold_24_95 : ∀ i ∈ List.range 1, ThresholdAt 24 (95+i) := by decide +kernel

theorem threshold_24_96 : ∀ i ∈ List.range 1, ThresholdAt 24 (96+i) := by decide +kernel

theorem threshold_24_97 : ∀ i ∈ List.range 1, ThresholdAt 24 (97+i) := by decide +kernel

theorem threshold_24_98 : ∀ i ∈ List.range 1, ThresholdAt 24 (98+i) := by decide +kernel

theorem threshold_24_99 : ∀ i ∈ List.range 1, ThresholdAt 24 (99+i) := by decide +kernel

theorem threshold_24_100 : ∀ i ∈ List.range 1, ThresholdAt 24 (100+i) := by decide +kernel

theorem threshold_24_101 : ∀ i ∈ List.range 1, ThresholdAt 24 (101+i) := by decide +kernel

theorem threshold_24_102 : ∀ i ∈ List.range 1, ThresholdAt 24 (102+i) := by decide +kernel

theorem threshold_24_103 : ∀ i ∈ List.range 1, ThresholdAt 24 (103+i) := by decide +kernel

theorem threshold_24_104 : ∀ i ∈ List.range 1, ThresholdAt 24 (104+i) := by decide +kernel

theorem threshold_24_105 : ∀ i ∈ List.range 1, ThresholdAt 24 (105+i) := by decide +kernel

theorem threshold_24_106 : ∀ i ∈ List.range 1, ThresholdAt 24 (106+i) := by decide +kernel

theorem threshold_24_107 : ∀ i ∈ List.range 1, ThresholdAt 24 (107+i) := by decide +kernel

theorem threshold_24_108 : ∀ i ∈ List.range 1, ThresholdAt 24 (108+i) := by decide +kernel

theorem threshold_24_109 : ∀ i ∈ List.range 1, ThresholdAt 24 (109+i) := by decide +kernel

theorem threshold_24_110 : ∀ i ∈ List.range 1, ThresholdAt 24 (110+i) := by decide +kernel

theorem threshold_24_111 : ∀ i ∈ List.range 1, ThresholdAt 24 (111+i) := by decide +kernel

theorem threshold_24_112 : ∀ i ∈ List.range 1, ThresholdAt 24 (112+i) := by decide +kernel

theorem threshold_24_113 : ∀ i ∈ List.range 1, ThresholdAt 24 (113+i) := by decide +kernel

theorem threshold_24_114 : ∀ i ∈ List.range 1, ThresholdAt 24 (114+i) := by decide +kernel

theorem threshold_24_115 : ∀ i ∈ List.range 1, ThresholdAt 24 (115+i) := by decide +kernel

theorem threshold_24_116 : ∀ i ∈ List.range 1, ThresholdAt 24 (116+i) := by decide +kernel

theorem threshold_24_117 : ∀ i ∈ List.range 1, ThresholdAt 24 (117+i) := by decide +kernel

theorem threshold_24_118 : ∀ i ∈ List.range 1, ThresholdAt 24 (118+i) := by decide +kernel

theorem threshold_24_119 : ∀ i ∈ List.range 1, ThresholdAt 24 (119+i) := by decide +kernel

theorem threshold_24_120 : ∀ i ∈ List.range 1, ThresholdAt 24 (120+i) := by decide +kernel

theorem threshold_24_121 : ∀ i ∈ List.range 1, ThresholdAt 24 (121+i) := by decide +kernel

theorem threshold_24_122 : ∀ i ∈ List.range 1, ThresholdAt 24 (122+i) := by decide +kernel

theorem threshold_24 (v : ℕ) (hv : v ∈ List.range 123) : ThresholdAt 24 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 24 v)
  have h := (join 0 61 62 (join 0 30 31 (join 0 15 15 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_24_0 (join 1 1 1 threshold_24_1 threshold_24_2)) (join 3 2 2 (join 3 1 1 threshold_24_3 threshold_24_4) (join 5 1 1 threshold_24_5 threshold_24_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_24_7 threshold_24_8) (join 9 1 1 threshold_24_9 threshold_24_10)) (join 11 2 2 (join 11 1 1 threshold_24_11 threshold_24_12) (join 13 1 1 threshold_24_13 threshold_24_14)))) (join 15 7 8 (join 15 3 4 (join 15 1 2 threshold_24_15 (join 16 1 1 threshold_24_16 threshold_24_17)) (join 18 2 2 (join 18 1 1 threshold_24_18 threshold_24_19) (join 20 1 1 threshold_24_20 threshold_24_21))) (join 22 4 4 (join 22 2 2 (join 22 1 1 threshold_24_22 threshold_24_23) (join 24 1 1 threshold_24_24 threshold_24_25)) (join 26 2 2 (join 26 1 1 threshold_24_26 threshold_24_27) (join 28 1 1 threshold_24_28 threshold_24_29))))) (join 30 15 16 (join 30 7 8 (join 30 3 4 (join 30 1 2 threshold_24_30 (join 31 1 1 threshold_24_31 threshold_24_32)) (join 33 2 2 (join 33 1 1 threshold_24_33 threshold_24_34) (join 35 1 1 threshold_24_35 threshold_24_36))) (join 37 4 4 (join 37 2 2 (join 37 1 1 threshold_24_37 threshold_24_38) (join 39 1 1 threshold_24_39 threshold_24_40)) (join 41 2 2 (join 41 1 1 threshold_24_41 threshold_24_42) (join 43 1 1 threshold_24_43 threshold_24_44)))) (join 45 8 8 (join 45 4 4 (join 45 2 2 (join 45 1 1 threshold_24_45 threshold_24_46) (join 47 1 1 threshold_24_47 threshold_24_48)) (join 49 2 2 (join 49 1 1 threshold_24_49 threshold_24_50) (join 51 1 1 threshold_24_51 threshold_24_52))) (join 53 4 4 (join 53 2 2 (join 53 1 1 threshold_24_53 threshold_24_54) (join 55 1 1 threshold_24_55 threshold_24_56)) (join 57 2 2 (join 57 1 1 threshold_24_57 threshold_24_58) (join 59 1 1 threshold_24_59 threshold_24_60)))))) (join 61 31 31 (join 61 15 16 (join 61 7 8 (join 61 3 4 (join 61 1 2 threshold_24_61 (join 62 1 1 threshold_24_62 threshold_24_63)) (join 64 2 2 (join 64 1 1 threshold_24_64 threshold_24_65) (join 66 1 1 threshold_24_66 threshold_24_67))) (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_24_68 threshold_24_69) (join 70 1 1 threshold_24_70 threshold_24_71)) (join 72 2 2 (join 72 1 1 threshold_24_72 threshold_24_73) (join 74 1 1 threshold_24_74 threshold_24_75)))) (join 76 8 8 (join 76 4 4 (join 76 2 2 (join 76 1 1 threshold_24_76 threshold_24_77) (join 78 1 1 threshold_24_78 threshold_24_79)) (join 80 2 2 (join 80 1 1 threshold_24_80 threshold_24_81) (join 82 1 1 threshold_24_82 threshold_24_83))) (join 84 4 4 (join 84 2 2 (join 84 1 1 threshold_24_84 threshold_24_85) (join 86 1 1 threshold_24_86 threshold_24_87)) (join 88 2 2 (join 88 1 1 threshold_24_88 threshold_24_89) (join 90 1 1 threshold_24_90 threshold_24_91))))) (join 92 15 16 (join 92 7 8 (join 92 3 4 (join 92 1 2 threshold_24_92 (join 93 1 1 threshold_24_93 threshold_24_94)) (join 95 2 2 (join 95 1 1 threshold_24_95 threshold_24_96) (join 97 1 1 threshold_24_97 threshold_24_98))) (join 99 4 4 (join 99 2 2 (join 99 1 1 threshold_24_99 threshold_24_100) (join 101 1 1 threshold_24_101 threshold_24_102)) (join 103 2 2 (join 103 1 1 threshold_24_103 threshold_24_104) (join 105 1 1 threshold_24_105 threshold_24_106)))) (join 107 8 8 (join 107 4 4 (join 107 2 2 (join 107 1 1 threshold_24_107 threshold_24_108) (join 109 1 1 threshold_24_109 threshold_24_110)) (join 111 2 2 (join 111 1 1 threshold_24_111 threshold_24_112) (join 113 1 1 threshold_24_113 threshold_24_114))) (join 115 4 4 (join 115 2 2 (join 115 1 1 threshold_24_115 threshold_24_116) (join 117 1 1 threshold_24_117 threshold_24_118)) (join 119 2 2 (join 119 1 1 threshold_24_119 threshold_24_120) (join 121 1 1 threshold_24_121 threshold_24_122)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_24_0 : ∀ i ∈ List.range 4, LedgerAt 24 (0+i) := by decide +kernel

theorem ledger_24_4 : ∀ i ∈ List.range 4, LedgerAt 24 (4+i) := by decide +kernel

theorem ledger_24_8 : ∀ i ∈ List.range 4, LedgerAt 24 (8+i) := by decide +kernel

theorem ledger_24_12 : ∀ i ∈ List.range 4, LedgerAt 24 (12+i) := by decide +kernel

theorem ledger_24_16 : ∀ i ∈ List.range 4, LedgerAt 24 (16+i) := by decide +kernel

theorem ledger_24_20 : ∀ i ∈ List.range 4, LedgerAt 24 (20+i) := by decide +kernel

theorem ledger_24_24 : ∀ i ∈ List.range 4, LedgerAt 24 (24+i) := by decide +kernel

theorem ledger_24_28 : ∀ i ∈ List.range 4, LedgerAt 24 (28+i) := by decide +kernel

theorem ledger_24_32 : ∀ i ∈ List.range 4, LedgerAt 24 (32+i) := by decide +kernel

theorem ledger_24_36 : ∀ i ∈ List.range 4, LedgerAt 24 (36+i) := by decide +kernel

theorem ledger_24_40 : ∀ i ∈ List.range 4, LedgerAt 24 (40+i) := by decide +kernel

theorem ledger_24_44 : ∀ i ∈ List.range 4, LedgerAt 24 (44+i) := by decide +kernel

theorem ledger_24_48 : ∀ i ∈ List.range 4, LedgerAt 24 (48+i) := by decide +kernel

theorem ledger_24_52 : ∀ i ∈ List.range 4, LedgerAt 24 (52+i) := by decide +kernel

theorem ledger_24_56 : ∀ i ∈ List.range 4, LedgerAt 24 (56+i) := by decide +kernel

theorem ledger_24_60 : ∀ i ∈ List.range 4, LedgerAt 24 (60+i) := by decide +kernel

theorem ledger_24_64 : ∀ i ∈ List.range 4, LedgerAt 24 (64+i) := by decide +kernel

theorem ledger_24_68 : ∀ i ∈ List.range 4, LedgerAt 24 (68+i) := by decide +kernel

theorem ledger_24_72 : ∀ i ∈ List.range 4, LedgerAt 24 (72+i) := by decide +kernel

theorem ledger_24_76 : ∀ i ∈ List.range 4, LedgerAt 24 (76+i) := by decide +kernel

theorem ledger_24_80 : ∀ i ∈ List.range 4, LedgerAt 24 (80+i) := by decide +kernel

theorem ledger_24_84 : ∀ i ∈ List.range 4, LedgerAt 24 (84+i) := by decide +kernel

theorem ledger_24_88 : ∀ i ∈ List.range 4, LedgerAt 24 (88+i) := by decide +kernel

theorem ledger_24_92 : ∀ i ∈ List.range 4, LedgerAt 24 (92+i) := by decide +kernel

theorem ledger_24_96 : ∀ i ∈ List.range 4, LedgerAt 24 (96+i) := by decide +kernel

theorem ledger_24_100 : ∀ i ∈ List.range 4, LedgerAt 24 (100+i) := by decide +kernel

theorem ledger_24_104 : ∀ i ∈ List.range 4, LedgerAt 24 (104+i) := by decide +kernel

theorem ledger_24_108 : ∀ i ∈ List.range 4, LedgerAt 24 (108+i) := by decide +kernel

theorem ledger_24_112 : ∀ i ∈ List.range 4, LedgerAt 24 (112+i) := by decide +kernel

theorem ledger_24_116 : ∀ i ∈ List.range 4, LedgerAt 24 (116+i) := by decide +kernel

theorem ledger_24_120 : ∀ i ∈ List.range 3, LedgerAt 24 (120+i) := by decide +kernel

theorem ledger_24 (v : ℕ) (hv : v ∈ List.range 123) : LedgerAt 24 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 24 v)
  have h := (join 0 60 63 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_24_0 (join 4 4 4 ledger_24_4 ledger_24_8)) (join 12 8 8 (join 12 4 4 ledger_24_12 ledger_24_16) (join 20 4 4 ledger_24_20 ledger_24_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_24_28 ledger_24_32) (join 36 4 4 ledger_24_36 ledger_24_40)) (join 44 8 8 (join 44 4 4 ledger_24_44 ledger_24_48) (join 52 4 4 ledger_24_52 ledger_24_56)))) (join 60 32 31 (join 60 16 16 (join 60 8 8 (join 60 4 4 ledger_24_60 ledger_24_64) (join 68 4 4 ledger_24_68 ledger_24_72)) (join 76 8 8 (join 76 4 4 ledger_24_76 ledger_24_80) (join 84 4 4 ledger_24_84 ledger_24_88))) (join 92 16 15 (join 92 8 8 (join 92 4 4 ledger_24_92 ledger_24_96) (join 100 4 4 ledger_24_100 ledger_24_104)) (join 108 8 7 (join 108 4 4 ledger_24_108 ledger_24_112) (join 116 4 3 ledger_24_116 ledger_24_120)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
