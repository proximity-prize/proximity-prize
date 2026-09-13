import ProximityPrize.SubmissionLower.BoundaryTailCheckedR246807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_25_0 : ∀ i ∈ List.range 4, GeometryAt 25 (0+i) := by decide +kernel

theorem geometry_25_4 : ∀ i ∈ List.range 4, GeometryAt 25 (4+i) := by decide +kernel

theorem geometry_25_8 : ∀ i ∈ List.range 4, GeometryAt 25 (8+i) := by decide +kernel

theorem geometry_25_12 : ∀ i ∈ List.range 4, GeometryAt 25 (12+i) := by decide +kernel

theorem geometry_25_16 : ∀ i ∈ List.range 4, GeometryAt 25 (16+i) := by decide +kernel

theorem geometry_25_20 : ∀ i ∈ List.range 4, GeometryAt 25 (20+i) := by decide +kernel

theorem geometry_25_24 : ∀ i ∈ List.range 4, GeometryAt 25 (24+i) := by decide +kernel

theorem geometry_25_28 : ∀ i ∈ List.range 4, GeometryAt 25 (28+i) := by decide +kernel

theorem geometry_25_32 : ∀ i ∈ List.range 4, GeometryAt 25 (32+i) := by decide +kernel

theorem geometry_25_36 : ∀ i ∈ List.range 4, GeometryAt 25 (36+i) := by decide +kernel

theorem geometry_25_40 : ∀ i ∈ List.range 4, GeometryAt 25 (40+i) := by decide +kernel

theorem geometry_25_44 : ∀ i ∈ List.range 4, GeometryAt 25 (44+i) := by decide +kernel

theorem geometry_25_48 : ∀ i ∈ List.range 4, GeometryAt 25 (48+i) := by decide +kernel

theorem geometry_25_52 : ∀ i ∈ List.range 4, GeometryAt 25 (52+i) := by decide +kernel

theorem geometry_25_56 : ∀ i ∈ List.range 4, GeometryAt 25 (56+i) := by decide +kernel

theorem geometry_25_60 : ∀ i ∈ List.range 4, GeometryAt 25 (60+i) := by decide +kernel

theorem geometry_25_64 : ∀ i ∈ List.range 4, GeometryAt 25 (64+i) := by decide +kernel

theorem geometry_25_68 : ∀ i ∈ List.range 4, GeometryAt 25 (68+i) := by decide +kernel

theorem geometry_25_72 : ∀ i ∈ List.range 4, GeometryAt 25 (72+i) := by decide +kernel

theorem geometry_25_76 : ∀ i ∈ List.range 4, GeometryAt 25 (76+i) := by decide +kernel

theorem geometry_25_80 : ∀ i ∈ List.range 4, GeometryAt 25 (80+i) := by decide +kernel

theorem geometry_25_84 : ∀ i ∈ List.range 4, GeometryAt 25 (84+i) := by decide +kernel

theorem geometry_25_88 : ∀ i ∈ List.range 4, GeometryAt 25 (88+i) := by decide +kernel

theorem geometry_25_92 : ∀ i ∈ List.range 4, GeometryAt 25 (92+i) := by decide +kernel

theorem geometry_25_96 : ∀ i ∈ List.range 4, GeometryAt 25 (96+i) := by decide +kernel

theorem geometry_25_100 : ∀ i ∈ List.range 4, GeometryAt 25 (100+i) := by decide +kernel

theorem geometry_25_104 : ∀ i ∈ List.range 4, GeometryAt 25 (104+i) := by decide +kernel

theorem geometry_25_108 : ∀ i ∈ List.range 4, GeometryAt 25 (108+i) := by decide +kernel

theorem geometry_25_112 : ∀ i ∈ List.range 4, GeometryAt 25 (112+i) := by decide +kernel

theorem geometry_25_116 : ∀ i ∈ List.range 4, GeometryAt 25 (116+i) := by decide +kernel

theorem geometry_25_120 : ∀ i ∈ List.range 2, GeometryAt 25 (120+i) := by decide +kernel

theorem geometry_25 (v : ℕ) (hv : v ∈ List.range 122) : GeometryAt 25 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 25 v)
  have h := (join 0 60 62 (join 0 28 32 (join 0 12 16 (join 0 4 8 geometry_25_0 (join 4 4 4 geometry_25_4 geometry_25_8)) (join 12 8 8 (join 12 4 4 geometry_25_12 geometry_25_16) (join 20 4 4 geometry_25_20 geometry_25_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 geometry_25_28 geometry_25_32) (join 36 4 4 geometry_25_36 geometry_25_40)) (join 44 8 8 (join 44 4 4 geometry_25_44 geometry_25_48) (join 52 4 4 geometry_25_52 geometry_25_56)))) (join 60 32 30 (join 60 16 16 (join 60 8 8 (join 60 4 4 geometry_25_60 geometry_25_64) (join 68 4 4 geometry_25_68 geometry_25_72)) (join 76 8 8 (join 76 4 4 geometry_25_76 geometry_25_80) (join 84 4 4 geometry_25_84 geometry_25_88))) (join 92 16 14 (join 92 8 8 (join 92 4 4 geometry_25_92 geometry_25_96) (join 100 4 4 geometry_25_100 geometry_25_104)) (join 108 8 6 (join 108 4 4 geometry_25_108 geometry_25_112) (join 116 4 2 geometry_25_116 geometry_25_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_25_0 : ∀ i ∈ List.range 4, StrictAt 25 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (0+i)) 25 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_4 : ∀ i ∈ List.range 4, StrictAt 25 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (4+i)) 25 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_8 : ∀ i ∈ List.range 4, StrictAt 25 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (8+i)) 25 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_12 : ∀ i ∈ List.range 4, StrictAt 25 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (12+i)) 25 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_16 : ∀ i ∈ List.range 4, StrictAt 25 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (16+i)) 25 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_20 : ∀ i ∈ List.range 4, StrictAt 25 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (20+i)) 25 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_24 : ∀ i ∈ List.range 4, StrictAt 25 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (24+i)) 25 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_28 : ∀ i ∈ List.range 4, StrictAt 25 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (28+i)) 25 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_32 : ∀ i ∈ List.range 4, StrictAt 25 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (32+i)) 25 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_36 : ∀ i ∈ List.range 4, StrictAt 25 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (36+i)) 25 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_40 : ∀ i ∈ List.range 4, StrictAt 25 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (40+i)) 25 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_44 : ∀ i ∈ List.range 4, StrictAt 25 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (44+i)) 25 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_48 : ∀ i ∈ List.range 4, StrictAt 25 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (48+i)) 25 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_52 : ∀ i ∈ List.range 4, StrictAt 25 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (52+i)) 25 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_56 : ∀ i ∈ List.range 4, StrictAt 25 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (56+i)) 25 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_60 : ∀ i ∈ List.range 4, StrictAt 25 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (60+i)) 25 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_64 : ∀ i ∈ List.range 4, StrictAt 25 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (64+i)) 25 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_68 : ∀ i ∈ List.range 4, StrictAt 25 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (68+i)) 25 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_72 : ∀ i ∈ List.range 4, StrictAt 25 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (72+i)) 25 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_76 : ∀ i ∈ List.range 4, StrictAt 25 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (76+i)) 25 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_80 : ∀ i ∈ List.range 4, StrictAt 25 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (80+i)) 25 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_84 : ∀ i ∈ List.range 4, StrictAt 25 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (84+i)) 25 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_88 : ∀ i ∈ List.range 4, StrictAt 25 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (88+i)) 25 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_92 : ∀ i ∈ List.range 4, StrictAt 25 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (92+i)) 25 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_96 : ∀ i ∈ List.range 4, StrictAt 25 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (96+i)) 25 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_100 : ∀ i ∈ List.range 4, StrictAt 25 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (100+i)) 25 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_104 : ∀ i ∈ List.range 4, StrictAt 25 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (104+i)) 25 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_108 : ∀ i ∈ List.range 4, StrictAt 25 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (108+i)) 25 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_112 : ∀ i ∈ List.range 4, StrictAt 25 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (112+i)) 25 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_116 : ∀ i ∈ List.range 4, StrictAt 25 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (116+i)) 25 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25_120 : ∀ i ∈ List.range 2, StrictAt 25 (120+i) := by
  have h : ∀ i ∈ List.range 2, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 25 (120+i)) 25 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_25 (v : ℕ) (hv : v ∈ List.range 122) : StrictAt 25 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 25 v)
  have h := (join 0 60 62 (join 0 28 32 (join 0 12 16 (join 0 4 8 strict_25_0 (join 4 4 4 strict_25_4 strict_25_8)) (join 12 8 8 (join 12 4 4 strict_25_12 strict_25_16) (join 20 4 4 strict_25_20 strict_25_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 strict_25_28 strict_25_32) (join 36 4 4 strict_25_36 strict_25_40)) (join 44 8 8 (join 44 4 4 strict_25_44 strict_25_48) (join 52 4 4 strict_25_52 strict_25_56)))) (join 60 32 30 (join 60 16 16 (join 60 8 8 (join 60 4 4 strict_25_60 strict_25_64) (join 68 4 4 strict_25_68 strict_25_72)) (join 76 8 8 (join 76 4 4 strict_25_76 strict_25_80) (join 84 4 4 strict_25_84 strict_25_88))) (join 92 16 14 (join 92 8 8 (join 92 4 4 strict_25_92 strict_25_96) (join 100 4 4 strict_25_100 strict_25_104)) (join 108 8 6 (join 108 4 4 strict_25_108 strict_25_112) (join 116 4 2 strict_25_116 strict_25_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_25_0 : ∀ i ∈ List.range 4, PhaseAt 25 (0+i) := by decide +kernel

theorem phase_25_4 : ∀ i ∈ List.range 4, PhaseAt 25 (4+i) := by decide +kernel

theorem phase_25_8 : ∀ i ∈ List.range 4, PhaseAt 25 (8+i) := by decide +kernel

theorem phase_25_12 : ∀ i ∈ List.range 4, PhaseAt 25 (12+i) := by decide +kernel

theorem phase_25_16 : ∀ i ∈ List.range 4, PhaseAt 25 (16+i) := by decide +kernel

theorem phase_25_20 : ∀ i ∈ List.range 4, PhaseAt 25 (20+i) := by decide +kernel

theorem phase_25_24 : ∀ i ∈ List.range 4, PhaseAt 25 (24+i) := by decide +kernel

theorem phase_25_28 : ∀ i ∈ List.range 4, PhaseAt 25 (28+i) := by decide +kernel

theorem phase_25_32 : ∀ i ∈ List.range 4, PhaseAt 25 (32+i) := by decide +kernel

theorem phase_25_36 : ∀ i ∈ List.range 4, PhaseAt 25 (36+i) := by decide +kernel

theorem phase_25_40 : ∀ i ∈ List.range 4, PhaseAt 25 (40+i) := by decide +kernel

theorem phase_25_44 : ∀ i ∈ List.range 4, PhaseAt 25 (44+i) := by decide +kernel

theorem phase_25_48 : ∀ i ∈ List.range 4, PhaseAt 25 (48+i) := by decide +kernel

theorem phase_25_52 : ∀ i ∈ List.range 4, PhaseAt 25 (52+i) := by decide +kernel

theorem phase_25_56 : ∀ i ∈ List.range 4, PhaseAt 25 (56+i) := by decide +kernel

theorem phase_25_60 : ∀ i ∈ List.range 4, PhaseAt 25 (60+i) := by decide +kernel

theorem phase_25_64 : ∀ i ∈ List.range 4, PhaseAt 25 (64+i) := by decide +kernel

theorem phase_25_68 : ∀ i ∈ List.range 4, PhaseAt 25 (68+i) := by decide +kernel

theorem phase_25_72 : ∀ i ∈ List.range 4, PhaseAt 25 (72+i) := by decide +kernel

theorem phase_25_76 : ∀ i ∈ List.range 4, PhaseAt 25 (76+i) := by decide +kernel

theorem phase_25_80 : ∀ i ∈ List.range 4, PhaseAt 25 (80+i) := by decide +kernel

theorem phase_25_84 : ∀ i ∈ List.range 4, PhaseAt 25 (84+i) := by decide +kernel

theorem phase_25_88 : ∀ i ∈ List.range 4, PhaseAt 25 (88+i) := by decide +kernel

theorem phase_25_92 : ∀ i ∈ List.range 4, PhaseAt 25 (92+i) := by decide +kernel

theorem phase_25_96 : ∀ i ∈ List.range 4, PhaseAt 25 (96+i) := by decide +kernel

theorem phase_25_100 : ∀ i ∈ List.range 4, PhaseAt 25 (100+i) := by decide +kernel

theorem phase_25_104 : ∀ i ∈ List.range 4, PhaseAt 25 (104+i) := by decide +kernel

theorem phase_25_108 : ∀ i ∈ List.range 4, PhaseAt 25 (108+i) := by decide +kernel

theorem phase_25_112 : ∀ i ∈ List.range 4, PhaseAt 25 (112+i) := by decide +kernel

theorem phase_25_116 : ∀ i ∈ List.range 4, PhaseAt 25 (116+i) := by decide +kernel

theorem phase_25_120 : ∀ i ∈ List.range 2, PhaseAt 25 (120+i) := by decide +kernel

theorem phase_25 (v : ℕ) (hv : v ∈ List.range 122) : PhaseAt 25 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 25 v)
  have h := (join 0 60 62 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_25_0 (join 4 4 4 phase_25_4 phase_25_8)) (join 12 8 8 (join 12 4 4 phase_25_12 phase_25_16) (join 20 4 4 phase_25_20 phase_25_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_25_28 phase_25_32) (join 36 4 4 phase_25_36 phase_25_40)) (join 44 8 8 (join 44 4 4 phase_25_44 phase_25_48) (join 52 4 4 phase_25_52 phase_25_56)))) (join 60 32 30 (join 60 16 16 (join 60 8 8 (join 60 4 4 phase_25_60 phase_25_64) (join 68 4 4 phase_25_68 phase_25_72)) (join 76 8 8 (join 76 4 4 phase_25_76 phase_25_80) (join 84 4 4 phase_25_84 phase_25_88))) (join 92 16 14 (join 92 8 8 (join 92 4 4 phase_25_92 phase_25_96) (join 100 4 4 phase_25_100 phase_25_104)) (join 108 8 6 (join 108 4 4 phase_25_108 phase_25_112) (join 116 4 2 phase_25_116 phase_25_120)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_25_0 : ∀ i ∈ List.range 1, ThresholdAt 25 (0+i) := by decide +kernel

theorem threshold_25_1 : ∀ i ∈ List.range 1, ThresholdAt 25 (1+i) := by decide +kernel

theorem threshold_25_2 : ∀ i ∈ List.range 1, ThresholdAt 25 (2+i) := by decide +kernel

theorem threshold_25_3 : ∀ i ∈ List.range 1, ThresholdAt 25 (3+i) := by decide +kernel

theorem threshold_25_4 : ∀ i ∈ List.range 1, ThresholdAt 25 (4+i) := by decide +kernel

theorem threshold_25_5 : ∀ i ∈ List.range 1, ThresholdAt 25 (5+i) := by decide +kernel

theorem threshold_25_6 : ∀ i ∈ List.range 1, ThresholdAt 25 (6+i) := by decide +kernel

theorem threshold_25_7 : ∀ i ∈ List.range 1, ThresholdAt 25 (7+i) := by decide +kernel

theorem threshold_25_8 : ∀ i ∈ List.range 1, ThresholdAt 25 (8+i) := by decide +kernel

theorem threshold_25_9 : ∀ i ∈ List.range 1, ThresholdAt 25 (9+i) := by decide +kernel

theorem threshold_25_10 : ∀ i ∈ List.range 1, ThresholdAt 25 (10+i) := by decide +kernel

theorem threshold_25_11 : ∀ i ∈ List.range 1, ThresholdAt 25 (11+i) := by decide +kernel

theorem threshold_25_12 : ∀ i ∈ List.range 1, ThresholdAt 25 (12+i) := by decide +kernel

theorem threshold_25_13 : ∀ i ∈ List.range 1, ThresholdAt 25 (13+i) := by decide +kernel

theorem threshold_25_14 : ∀ i ∈ List.range 1, ThresholdAt 25 (14+i) := by decide +kernel

theorem threshold_25_15 : ∀ i ∈ List.range 1, ThresholdAt 25 (15+i) := by decide +kernel

theorem threshold_25_16 : ∀ i ∈ List.range 1, ThresholdAt 25 (16+i) := by decide +kernel

theorem threshold_25_17 : ∀ i ∈ List.range 1, ThresholdAt 25 (17+i) := by decide +kernel

theorem threshold_25_18 : ∀ i ∈ List.range 1, ThresholdAt 25 (18+i) := by decide +kernel

theorem threshold_25_19 : ∀ i ∈ List.range 1, ThresholdAt 25 (19+i) := by decide +kernel

theorem threshold_25_20 : ∀ i ∈ List.range 1, ThresholdAt 25 (20+i) := by decide +kernel

theorem threshold_25_21 : ∀ i ∈ List.range 1, ThresholdAt 25 (21+i) := by decide +kernel

theorem threshold_25_22 : ∀ i ∈ List.range 1, ThresholdAt 25 (22+i) := by decide +kernel

theorem threshold_25_23 : ∀ i ∈ List.range 1, ThresholdAt 25 (23+i) := by decide +kernel

theorem threshold_25_24 : ∀ i ∈ List.range 1, ThresholdAt 25 (24+i) := by decide +kernel

theorem threshold_25_25 : ∀ i ∈ List.range 1, ThresholdAt 25 (25+i) := by decide +kernel

theorem threshold_25_26 : ∀ i ∈ List.range 1, ThresholdAt 25 (26+i) := by decide +kernel

theorem threshold_25_27 : ∀ i ∈ List.range 1, ThresholdAt 25 (27+i) := by decide +kernel

theorem threshold_25_28 : ∀ i ∈ List.range 1, ThresholdAt 25 (28+i) := by decide +kernel

theorem threshold_25_29 : ∀ i ∈ List.range 1, ThresholdAt 25 (29+i) := by decide +kernel

theorem threshold_25_30 : ∀ i ∈ List.range 1, ThresholdAt 25 (30+i) := by decide +kernel

theorem threshold_25_31 : ∀ i ∈ List.range 1, ThresholdAt 25 (31+i) := by decide +kernel

theorem threshold_25_32 : ∀ i ∈ List.range 1, ThresholdAt 25 (32+i) := by decide +kernel

theorem threshold_25_33 : ∀ i ∈ List.range 1, ThresholdAt 25 (33+i) := by decide +kernel

theorem threshold_25_34 : ∀ i ∈ List.range 1, ThresholdAt 25 (34+i) := by decide +kernel

theorem threshold_25_35 : ∀ i ∈ List.range 1, ThresholdAt 25 (35+i) := by decide +kernel

theorem threshold_25_36 : ∀ i ∈ List.range 1, ThresholdAt 25 (36+i) := by decide +kernel

theorem threshold_25_37 : ∀ i ∈ List.range 1, ThresholdAt 25 (37+i) := by decide +kernel

theorem threshold_25_38 : ∀ i ∈ List.range 1, ThresholdAt 25 (38+i) := by decide +kernel

theorem threshold_25_39 : ∀ i ∈ List.range 1, ThresholdAt 25 (39+i) := by decide +kernel

theorem threshold_25_40 : ∀ i ∈ List.range 1, ThresholdAt 25 (40+i) := by decide +kernel

theorem threshold_25_41 : ∀ i ∈ List.range 1, ThresholdAt 25 (41+i) := by decide +kernel

theorem threshold_25_42 : ∀ i ∈ List.range 1, ThresholdAt 25 (42+i) := by decide +kernel

theorem threshold_25_43 : ∀ i ∈ List.range 1, ThresholdAt 25 (43+i) := by decide +kernel

theorem threshold_25_44 : ∀ i ∈ List.range 1, ThresholdAt 25 (44+i) := by decide +kernel

theorem threshold_25_45 : ∀ i ∈ List.range 1, ThresholdAt 25 (45+i) := by decide +kernel

theorem threshold_25_46 : ∀ i ∈ List.range 1, ThresholdAt 25 (46+i) := by decide +kernel

theorem threshold_25_47 : ∀ i ∈ List.range 1, ThresholdAt 25 (47+i) := by decide +kernel

theorem threshold_25_48 : ∀ i ∈ List.range 1, ThresholdAt 25 (48+i) := by decide +kernel

theorem threshold_25_49 : ∀ i ∈ List.range 1, ThresholdAt 25 (49+i) := by decide +kernel

theorem threshold_25_50 : ∀ i ∈ List.range 1, ThresholdAt 25 (50+i) := by decide +kernel

theorem threshold_25_51 : ∀ i ∈ List.range 1, ThresholdAt 25 (51+i) := by decide +kernel

theorem threshold_25_52 : ∀ i ∈ List.range 1, ThresholdAt 25 (52+i) := by decide +kernel

theorem threshold_25_53 : ∀ i ∈ List.range 1, ThresholdAt 25 (53+i) := by decide +kernel

theorem threshold_25_54 : ∀ i ∈ List.range 1, ThresholdAt 25 (54+i) := by decide +kernel

theorem threshold_25_55 : ∀ i ∈ List.range 1, ThresholdAt 25 (55+i) := by decide +kernel

theorem threshold_25_56 : ∀ i ∈ List.range 1, ThresholdAt 25 (56+i) := by decide +kernel

theorem threshold_25_57 : ∀ i ∈ List.range 1, ThresholdAt 25 (57+i) := by decide +kernel

theorem threshold_25_58 : ∀ i ∈ List.range 1, ThresholdAt 25 (58+i) := by decide +kernel

theorem threshold_25_59 : ∀ i ∈ List.range 1, ThresholdAt 25 (59+i) := by decide +kernel

theorem threshold_25_60 : ∀ i ∈ List.range 1, ThresholdAt 25 (60+i) := by decide +kernel

theorem threshold_25_61 : ∀ i ∈ List.range 1, ThresholdAt 25 (61+i) := by decide +kernel

theorem threshold_25_62 : ∀ i ∈ List.range 1, ThresholdAt 25 (62+i) := by decide +kernel

theorem threshold_25_63 : ∀ i ∈ List.range 1, ThresholdAt 25 (63+i) := by decide +kernel

theorem threshold_25_64 : ∀ i ∈ List.range 1, ThresholdAt 25 (64+i) := by decide +kernel

theorem threshold_25_65 : ∀ i ∈ List.range 1, ThresholdAt 25 (65+i) := by decide +kernel

theorem threshold_25_66 : ∀ i ∈ List.range 1, ThresholdAt 25 (66+i) := by decide +kernel

theorem threshold_25_67 : ∀ i ∈ List.range 1, ThresholdAt 25 (67+i) := by decide +kernel

theorem threshold_25_68 : ∀ i ∈ List.range 1, ThresholdAt 25 (68+i) := by decide +kernel

theorem threshold_25_69 : ∀ i ∈ List.range 1, ThresholdAt 25 (69+i) := by decide +kernel

theorem threshold_25_70 : ∀ i ∈ List.range 1, ThresholdAt 25 (70+i) := by decide +kernel

theorem threshold_25_71 : ∀ i ∈ List.range 1, ThresholdAt 25 (71+i) := by decide +kernel

theorem threshold_25_72 : ∀ i ∈ List.range 1, ThresholdAt 25 (72+i) := by decide +kernel

theorem threshold_25_73 : ∀ i ∈ List.range 1, ThresholdAt 25 (73+i) := by decide +kernel

theorem threshold_25_74 : ∀ i ∈ List.range 1, ThresholdAt 25 (74+i) := by decide +kernel

theorem threshold_25_75 : ∀ i ∈ List.range 1, ThresholdAt 25 (75+i) := by decide +kernel

theorem threshold_25_76 : ∀ i ∈ List.range 1, ThresholdAt 25 (76+i) := by decide +kernel

theorem threshold_25_77 : ∀ i ∈ List.range 1, ThresholdAt 25 (77+i) := by decide +kernel

theorem threshold_25_78 : ∀ i ∈ List.range 1, ThresholdAt 25 (78+i) := by decide +kernel

theorem threshold_25_79 : ∀ i ∈ List.range 1, ThresholdAt 25 (79+i) := by decide +kernel

theorem threshold_25_80 : ∀ i ∈ List.range 1, ThresholdAt 25 (80+i) := by decide +kernel

theorem threshold_25_81 : ∀ i ∈ List.range 1, ThresholdAt 25 (81+i) := by decide +kernel

theorem threshold_25_82 : ∀ i ∈ List.range 1, ThresholdAt 25 (82+i) := by decide +kernel

theorem threshold_25_83 : ∀ i ∈ List.range 1, ThresholdAt 25 (83+i) := by decide +kernel

theorem threshold_25_84 : ∀ i ∈ List.range 1, ThresholdAt 25 (84+i) := by decide +kernel

theorem threshold_25_85 : ∀ i ∈ List.range 1, ThresholdAt 25 (85+i) := by decide +kernel

theorem threshold_25_86 : ∀ i ∈ List.range 1, ThresholdAt 25 (86+i) := by decide +kernel

theorem threshold_25_87 : ∀ i ∈ List.range 1, ThresholdAt 25 (87+i) := by decide +kernel

theorem threshold_25_88 : ∀ i ∈ List.range 1, ThresholdAt 25 (88+i) := by decide +kernel

theorem threshold_25_89 : ∀ i ∈ List.range 1, ThresholdAt 25 (89+i) := by decide +kernel

theorem threshold_25_90 : ∀ i ∈ List.range 1, ThresholdAt 25 (90+i) := by decide +kernel

theorem threshold_25_91 : ∀ i ∈ List.range 1, ThresholdAt 25 (91+i) := by decide +kernel

theorem threshold_25_92 : ∀ i ∈ List.range 1, ThresholdAt 25 (92+i) := by decide +kernel

theorem threshold_25_93 : ∀ i ∈ List.range 1, ThresholdAt 25 (93+i) := by decide +kernel

theorem threshold_25_94 : ∀ i ∈ List.range 1, ThresholdAt 25 (94+i) := by decide +kernel

theorem threshold_25_95 : ∀ i ∈ List.range 1, ThresholdAt 25 (95+i) := by decide +kernel

theorem threshold_25_96 : ∀ i ∈ List.range 1, ThresholdAt 25 (96+i) := by decide +kernel

theorem threshold_25_97 : ∀ i ∈ List.range 1, ThresholdAt 25 (97+i) := by decide +kernel

theorem threshold_25_98 : ∀ i ∈ List.range 1, ThresholdAt 25 (98+i) := by decide +kernel

theorem threshold_25_99 : ∀ i ∈ List.range 1, ThresholdAt 25 (99+i) := by decide +kernel

theorem threshold_25_100 : ∀ i ∈ List.range 1, ThresholdAt 25 (100+i) := by decide +kernel

theorem threshold_25_101 : ∀ i ∈ List.range 1, ThresholdAt 25 (101+i) := by decide +kernel

theorem threshold_25_102 : ∀ i ∈ List.range 1, ThresholdAt 25 (102+i) := by decide +kernel

theorem threshold_25_103 : ∀ i ∈ List.range 1, ThresholdAt 25 (103+i) := by decide +kernel

theorem threshold_25_104 : ∀ i ∈ List.range 1, ThresholdAt 25 (104+i) := by decide +kernel

theorem threshold_25_105 : ∀ i ∈ List.range 1, ThresholdAt 25 (105+i) := by decide +kernel

theorem threshold_25_106 : ∀ i ∈ List.range 1, ThresholdAt 25 (106+i) := by decide +kernel

theorem threshold_25_107 : ∀ i ∈ List.range 1, ThresholdAt 25 (107+i) := by decide +kernel

theorem threshold_25_108 : ∀ i ∈ List.range 1, ThresholdAt 25 (108+i) := by decide +kernel

theorem threshold_25_109 : ∀ i ∈ List.range 1, ThresholdAt 25 (109+i) := by decide +kernel

theorem threshold_25_110 : ∀ i ∈ List.range 1, ThresholdAt 25 (110+i) := by decide +kernel

theorem threshold_25_111 : ∀ i ∈ List.range 1, ThresholdAt 25 (111+i) := by decide +kernel

theorem threshold_25_112 : ∀ i ∈ List.range 1, ThresholdAt 25 (112+i) := by decide +kernel

theorem threshold_25_113 : ∀ i ∈ List.range 1, ThresholdAt 25 (113+i) := by decide +kernel

theorem threshold_25_114 : ∀ i ∈ List.range 1, ThresholdAt 25 (114+i) := by decide +kernel

theorem threshold_25_115 : ∀ i ∈ List.range 1, ThresholdAt 25 (115+i) := by decide +kernel

theorem threshold_25_116 : ∀ i ∈ List.range 1, ThresholdAt 25 (116+i) := by decide +kernel

theorem threshold_25_117 : ∀ i ∈ List.range 1, ThresholdAt 25 (117+i) := by decide +kernel

theorem threshold_25_118 : ∀ i ∈ List.range 1, ThresholdAt 25 (118+i) := by decide +kernel

theorem threshold_25_119 : ∀ i ∈ List.range 1, ThresholdAt 25 (119+i) := by decide +kernel

theorem threshold_25_120 : ∀ i ∈ List.range 1, ThresholdAt 25 (120+i) := by decide +kernel

theorem threshold_25_121 : ∀ i ∈ List.range 1, ThresholdAt 25 (121+i) := by decide +kernel

theorem threshold_25 (v : ℕ) (hv : v ∈ List.range 122) : ThresholdAt 25 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 25 v)
  have h := (join 0 61 61 (join 0 30 31 (join 0 15 15 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_25_0 (join 1 1 1 threshold_25_1 threshold_25_2)) (join 3 2 2 (join 3 1 1 threshold_25_3 threshold_25_4) (join 5 1 1 threshold_25_5 threshold_25_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_25_7 threshold_25_8) (join 9 1 1 threshold_25_9 threshold_25_10)) (join 11 2 2 (join 11 1 1 threshold_25_11 threshold_25_12) (join 13 1 1 threshold_25_13 threshold_25_14)))) (join 15 7 8 (join 15 3 4 (join 15 1 2 threshold_25_15 (join 16 1 1 threshold_25_16 threshold_25_17)) (join 18 2 2 (join 18 1 1 threshold_25_18 threshold_25_19) (join 20 1 1 threshold_25_20 threshold_25_21))) (join 22 4 4 (join 22 2 2 (join 22 1 1 threshold_25_22 threshold_25_23) (join 24 1 1 threshold_25_24 threshold_25_25)) (join 26 2 2 (join 26 1 1 threshold_25_26 threshold_25_27) (join 28 1 1 threshold_25_28 threshold_25_29))))) (join 30 15 16 (join 30 7 8 (join 30 3 4 (join 30 1 2 threshold_25_30 (join 31 1 1 threshold_25_31 threshold_25_32)) (join 33 2 2 (join 33 1 1 threshold_25_33 threshold_25_34) (join 35 1 1 threshold_25_35 threshold_25_36))) (join 37 4 4 (join 37 2 2 (join 37 1 1 threshold_25_37 threshold_25_38) (join 39 1 1 threshold_25_39 threshold_25_40)) (join 41 2 2 (join 41 1 1 threshold_25_41 threshold_25_42) (join 43 1 1 threshold_25_43 threshold_25_44)))) (join 45 8 8 (join 45 4 4 (join 45 2 2 (join 45 1 1 threshold_25_45 threshold_25_46) (join 47 1 1 threshold_25_47 threshold_25_48)) (join 49 2 2 (join 49 1 1 threshold_25_49 threshold_25_50) (join 51 1 1 threshold_25_51 threshold_25_52))) (join 53 4 4 (join 53 2 2 (join 53 1 1 threshold_25_53 threshold_25_54) (join 55 1 1 threshold_25_55 threshold_25_56)) (join 57 2 2 (join 57 1 1 threshold_25_57 threshold_25_58) (join 59 1 1 threshold_25_59 threshold_25_60)))))) (join 61 30 31 (join 61 15 15 (join 61 7 8 (join 61 3 4 (join 61 1 2 threshold_25_61 (join 62 1 1 threshold_25_62 threshold_25_63)) (join 64 2 2 (join 64 1 1 threshold_25_64 threshold_25_65) (join 66 1 1 threshold_25_66 threshold_25_67))) (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_25_68 threshold_25_69) (join 70 1 1 threshold_25_70 threshold_25_71)) (join 72 2 2 (join 72 1 1 threshold_25_72 threshold_25_73) (join 74 1 1 threshold_25_74 threshold_25_75)))) (join 76 7 8 (join 76 3 4 (join 76 1 2 threshold_25_76 (join 77 1 1 threshold_25_77 threshold_25_78)) (join 79 2 2 (join 79 1 1 threshold_25_79 threshold_25_80) (join 81 1 1 threshold_25_81 threshold_25_82))) (join 83 4 4 (join 83 2 2 (join 83 1 1 threshold_25_83 threshold_25_84) (join 85 1 1 threshold_25_85 threshold_25_86)) (join 87 2 2 (join 87 1 1 threshold_25_87 threshold_25_88) (join 89 1 1 threshold_25_89 threshold_25_90))))) (join 91 15 16 (join 91 7 8 (join 91 3 4 (join 91 1 2 threshold_25_91 (join 92 1 1 threshold_25_92 threshold_25_93)) (join 94 2 2 (join 94 1 1 threshold_25_94 threshold_25_95) (join 96 1 1 threshold_25_96 threshold_25_97))) (join 98 4 4 (join 98 2 2 (join 98 1 1 threshold_25_98 threshold_25_99) (join 100 1 1 threshold_25_100 threshold_25_101)) (join 102 2 2 (join 102 1 1 threshold_25_102 threshold_25_103) (join 104 1 1 threshold_25_104 threshold_25_105)))) (join 106 8 8 (join 106 4 4 (join 106 2 2 (join 106 1 1 threshold_25_106 threshold_25_107) (join 108 1 1 threshold_25_108 threshold_25_109)) (join 110 2 2 (join 110 1 1 threshold_25_110 threshold_25_111) (join 112 1 1 threshold_25_112 threshold_25_113))) (join 114 4 4 (join 114 2 2 (join 114 1 1 threshold_25_114 threshold_25_115) (join 116 1 1 threshold_25_116 threshold_25_117)) (join 118 2 2 (join 118 1 1 threshold_25_118 threshold_25_119) (join 120 1 1 threshold_25_120 threshold_25_121)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_25_0 : ∀ i ∈ List.range 4, LedgerAt 25 (0+i) := by decide +kernel

theorem ledger_25_4 : ∀ i ∈ List.range 4, LedgerAt 25 (4+i) := by decide +kernel

theorem ledger_25_8 : ∀ i ∈ List.range 4, LedgerAt 25 (8+i) := by decide +kernel

theorem ledger_25_12 : ∀ i ∈ List.range 4, LedgerAt 25 (12+i) := by decide +kernel

theorem ledger_25_16 : ∀ i ∈ List.range 4, LedgerAt 25 (16+i) := by decide +kernel

theorem ledger_25_20 : ∀ i ∈ List.range 4, LedgerAt 25 (20+i) := by decide +kernel

theorem ledger_25_24 : ∀ i ∈ List.range 4, LedgerAt 25 (24+i) := by decide +kernel

theorem ledger_25_28 : ∀ i ∈ List.range 4, LedgerAt 25 (28+i) := by decide +kernel

theorem ledger_25_32 : ∀ i ∈ List.range 4, LedgerAt 25 (32+i) := by decide +kernel

theorem ledger_25_36 : ∀ i ∈ List.range 4, LedgerAt 25 (36+i) := by decide +kernel

theorem ledger_25_40 : ∀ i ∈ List.range 4, LedgerAt 25 (40+i) := by decide +kernel

theorem ledger_25_44 : ∀ i ∈ List.range 4, LedgerAt 25 (44+i) := by decide +kernel

theorem ledger_25_48 : ∀ i ∈ List.range 4, LedgerAt 25 (48+i) := by decide +kernel

theorem ledger_25_52 : ∀ i ∈ List.range 4, LedgerAt 25 (52+i) := by decide +kernel

theorem ledger_25_56 : ∀ i ∈ List.range 4, LedgerAt 25 (56+i) := by decide +kernel

theorem ledger_25_60 : ∀ i ∈ List.range 4, LedgerAt 25 (60+i) := by decide +kernel

theorem ledger_25_64 : ∀ i ∈ List.range 4, LedgerAt 25 (64+i) := by decide +kernel

theorem ledger_25_68 : ∀ i ∈ List.range 4, LedgerAt 25 (68+i) := by decide +kernel

theorem ledger_25_72 : ∀ i ∈ List.range 4, LedgerAt 25 (72+i) := by decide +kernel

theorem ledger_25_76 : ∀ i ∈ List.range 4, LedgerAt 25 (76+i) := by decide +kernel

theorem ledger_25_80 : ∀ i ∈ List.range 4, LedgerAt 25 (80+i) := by decide +kernel

theorem ledger_25_84 : ∀ i ∈ List.range 4, LedgerAt 25 (84+i) := by decide +kernel

theorem ledger_25_88 : ∀ i ∈ List.range 4, LedgerAt 25 (88+i) := by decide +kernel

theorem ledger_25_92 : ∀ i ∈ List.range 4, LedgerAt 25 (92+i) := by decide +kernel

theorem ledger_25_96 : ∀ i ∈ List.range 4, LedgerAt 25 (96+i) := by decide +kernel

theorem ledger_25_100 : ∀ i ∈ List.range 4, LedgerAt 25 (100+i) := by decide +kernel

theorem ledger_25_104 : ∀ i ∈ List.range 4, LedgerAt 25 (104+i) := by decide +kernel

theorem ledger_25_108 : ∀ i ∈ List.range 4, LedgerAt 25 (108+i) := by decide +kernel

theorem ledger_25_112 : ∀ i ∈ List.range 4, LedgerAt 25 (112+i) := by decide +kernel

theorem ledger_25_116 : ∀ i ∈ List.range 4, LedgerAt 25 (116+i) := by decide +kernel

theorem ledger_25_120 : ∀ i ∈ List.range 2, LedgerAt 25 (120+i) := by decide +kernel

theorem ledger_25 (v : ℕ) (hv : v ∈ List.range 122) : LedgerAt 25 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 25 v)
  have h := (join 0 60 62 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_25_0 (join 4 4 4 ledger_25_4 ledger_25_8)) (join 12 8 8 (join 12 4 4 ledger_25_12 ledger_25_16) (join 20 4 4 ledger_25_20 ledger_25_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_25_28 ledger_25_32) (join 36 4 4 ledger_25_36 ledger_25_40)) (join 44 8 8 (join 44 4 4 ledger_25_44 ledger_25_48) (join 52 4 4 ledger_25_52 ledger_25_56)))) (join 60 32 30 (join 60 16 16 (join 60 8 8 (join 60 4 4 ledger_25_60 ledger_25_64) (join 68 4 4 ledger_25_68 ledger_25_72)) (join 76 8 8 (join 76 4 4 ledger_25_76 ledger_25_80) (join 84 4 4 ledger_25_84 ledger_25_88))) (join 92 16 14 (join 92 8 8 (join 92 4 4 ledger_25_92 ledger_25_96) (join 100 4 4 ledger_25_100 ledger_25_104)) (join 108 8 6 (join 108 4 4 ledger_25_108 ledger_25_112) (join 116 4 2 ledger_25_116 ledger_25_120)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
