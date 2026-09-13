import ProximityPrize.SubmissionLower.BoundaryTailCheckedR296807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_30_0 : ∀ i ∈ List.range 4, GeometryAt 30 (0+i) := by decide +kernel

theorem geometry_30_4 : ∀ i ∈ List.range 4, GeometryAt 30 (4+i) := by decide +kernel

theorem geometry_30_8 : ∀ i ∈ List.range 4, GeometryAt 30 (8+i) := by decide +kernel

theorem geometry_30_12 : ∀ i ∈ List.range 4, GeometryAt 30 (12+i) := by decide +kernel

theorem geometry_30_16 : ∀ i ∈ List.range 4, GeometryAt 30 (16+i) := by decide +kernel

theorem geometry_30_20 : ∀ i ∈ List.range 4, GeometryAt 30 (20+i) := by decide +kernel

theorem geometry_30_24 : ∀ i ∈ List.range 4, GeometryAt 30 (24+i) := by decide +kernel

theorem geometry_30_28 : ∀ i ∈ List.range 4, GeometryAt 30 (28+i) := by decide +kernel

theorem geometry_30_32 : ∀ i ∈ List.range 4, GeometryAt 30 (32+i) := by decide +kernel

theorem geometry_30_36 : ∀ i ∈ List.range 4, GeometryAt 30 (36+i) := by decide +kernel

theorem geometry_30_40 : ∀ i ∈ List.range 4, GeometryAt 30 (40+i) := by decide +kernel

theorem geometry_30_44 : ∀ i ∈ List.range 4, GeometryAt 30 (44+i) := by decide +kernel

theorem geometry_30_48 : ∀ i ∈ List.range 4, GeometryAt 30 (48+i) := by decide +kernel

theorem geometry_30_52 : ∀ i ∈ List.range 4, GeometryAt 30 (52+i) := by decide +kernel

theorem geometry_30_56 : ∀ i ∈ List.range 4, GeometryAt 30 (56+i) := by decide +kernel

theorem geometry_30_60 : ∀ i ∈ List.range 4, GeometryAt 30 (60+i) := by decide +kernel

theorem geometry_30_64 : ∀ i ∈ List.range 4, GeometryAt 30 (64+i) := by decide +kernel

theorem geometry_30_68 : ∀ i ∈ List.range 4, GeometryAt 30 (68+i) := by decide +kernel

theorem geometry_30_72 : ∀ i ∈ List.range 4, GeometryAt 30 (72+i) := by decide +kernel

theorem geometry_30_76 : ∀ i ∈ List.range 4, GeometryAt 30 (76+i) := by decide +kernel

theorem geometry_30_80 : ∀ i ∈ List.range 4, GeometryAt 30 (80+i) := by decide +kernel

theorem geometry_30_84 : ∀ i ∈ List.range 4, GeometryAt 30 (84+i) := by decide +kernel

theorem geometry_30_88 : ∀ i ∈ List.range 4, GeometryAt 30 (88+i) := by decide +kernel

theorem geometry_30_92 : ∀ i ∈ List.range 4, GeometryAt 30 (92+i) := by decide +kernel

theorem geometry_30_96 : ∀ i ∈ List.range 4, GeometryAt 30 (96+i) := by decide +kernel

theorem geometry_30_100 : ∀ i ∈ List.range 4, GeometryAt 30 (100+i) := by decide +kernel

theorem geometry_30_104 : ∀ i ∈ List.range 4, GeometryAt 30 (104+i) := by decide +kernel

theorem geometry_30_108 : ∀ i ∈ List.range 4, GeometryAt 30 (108+i) := by decide +kernel

theorem geometry_30_112 : ∀ i ∈ List.range 4, GeometryAt 30 (112+i) := by decide +kernel

theorem geometry_30_116 : ∀ i ∈ List.range 1, GeometryAt 30 (116+i) := by decide +kernel

theorem geometry_30 (v : ℕ) (hv : v ∈ List.range 117) : GeometryAt 30 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 30 v)
  have h := (join 0 60 57 (join 0 28 32 (join 0 12 16 (join 0 4 8 geometry_30_0 (join 4 4 4 geometry_30_4 geometry_30_8)) (join 12 8 8 (join 12 4 4 geometry_30_12 geometry_30_16) (join 20 4 4 geometry_30_20 geometry_30_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 geometry_30_28 geometry_30_32) (join 36 4 4 geometry_30_36 geometry_30_40)) (join 44 8 8 (join 44 4 4 geometry_30_44 geometry_30_48) (join 52 4 4 geometry_30_52 geometry_30_56)))) (join 60 28 29 (join 60 12 16 (join 60 4 8 geometry_30_60 (join 64 4 4 geometry_30_64 geometry_30_68)) (join 72 8 8 (join 72 4 4 geometry_30_72 geometry_30_76) (join 80 4 4 geometry_30_80 geometry_30_84))) (join 88 16 13 (join 88 8 8 (join 88 4 4 geometry_30_88 geometry_30_92) (join 96 4 4 geometry_30_96 geometry_30_100)) (join 104 8 5 (join 104 4 4 geometry_30_104 geometry_30_108) (join 112 4 1 geometry_30_112 geometry_30_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_30_0 : ∀ i ∈ List.range 4, StrictAt 30 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (0+i)) 30 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_4 : ∀ i ∈ List.range 4, StrictAt 30 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (4+i)) 30 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_8 : ∀ i ∈ List.range 4, StrictAt 30 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (8+i)) 30 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_12 : ∀ i ∈ List.range 4, StrictAt 30 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (12+i)) 30 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_16 : ∀ i ∈ List.range 4, StrictAt 30 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (16+i)) 30 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_20 : ∀ i ∈ List.range 4, StrictAt 30 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (20+i)) 30 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_24 : ∀ i ∈ List.range 4, StrictAt 30 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (24+i)) 30 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_28 : ∀ i ∈ List.range 4, StrictAt 30 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (28+i)) 30 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_32 : ∀ i ∈ List.range 4, StrictAt 30 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (32+i)) 30 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_36 : ∀ i ∈ List.range 4, StrictAt 30 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (36+i)) 30 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_40 : ∀ i ∈ List.range 4, StrictAt 30 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (40+i)) 30 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_44 : ∀ i ∈ List.range 4, StrictAt 30 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (44+i)) 30 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_48 : ∀ i ∈ List.range 4, StrictAt 30 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (48+i)) 30 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_52 : ∀ i ∈ List.range 4, StrictAt 30 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (52+i)) 30 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_56 : ∀ i ∈ List.range 4, StrictAt 30 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (56+i)) 30 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_60 : ∀ i ∈ List.range 4, StrictAt 30 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (60+i)) 30 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_64 : ∀ i ∈ List.range 4, StrictAt 30 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (64+i)) 30 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_68 : ∀ i ∈ List.range 4, StrictAt 30 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (68+i)) 30 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_72 : ∀ i ∈ List.range 4, StrictAt 30 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (72+i)) 30 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_76 : ∀ i ∈ List.range 4, StrictAt 30 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (76+i)) 30 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_80 : ∀ i ∈ List.range 4, StrictAt 30 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (80+i)) 30 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_84 : ∀ i ∈ List.range 4, StrictAt 30 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (84+i)) 30 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_88 : ∀ i ∈ List.range 4, StrictAt 30 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (88+i)) 30 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_92 : ∀ i ∈ List.range 4, StrictAt 30 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (92+i)) 30 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_96 : ∀ i ∈ List.range 4, StrictAt 30 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (96+i)) 30 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_100 : ∀ i ∈ List.range 4, StrictAt 30 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (100+i)) 30 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_104 : ∀ i ∈ List.range 4, StrictAt 30 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (104+i)) 30 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_108 : ∀ i ∈ List.range 4, StrictAt 30 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (108+i)) 30 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_112 : ∀ i ∈ List.range 4, StrictAt 30 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (112+i)) 30 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30_116 : ∀ i ∈ List.range 1, StrictAt 30 (116+i) := by
  have h : ∀ i ∈ List.range 1, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 30 (116+i)) 30 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_30 (v : ℕ) (hv : v ∈ List.range 117) : StrictAt 30 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 30 v)
  have h := (join 0 60 57 (join 0 28 32 (join 0 12 16 (join 0 4 8 strict_30_0 (join 4 4 4 strict_30_4 strict_30_8)) (join 12 8 8 (join 12 4 4 strict_30_12 strict_30_16) (join 20 4 4 strict_30_20 strict_30_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 strict_30_28 strict_30_32) (join 36 4 4 strict_30_36 strict_30_40)) (join 44 8 8 (join 44 4 4 strict_30_44 strict_30_48) (join 52 4 4 strict_30_52 strict_30_56)))) (join 60 28 29 (join 60 12 16 (join 60 4 8 strict_30_60 (join 64 4 4 strict_30_64 strict_30_68)) (join 72 8 8 (join 72 4 4 strict_30_72 strict_30_76) (join 80 4 4 strict_30_80 strict_30_84))) (join 88 16 13 (join 88 8 8 (join 88 4 4 strict_30_88 strict_30_92) (join 96 4 4 strict_30_96 strict_30_100)) (join 104 8 5 (join 104 4 4 strict_30_104 strict_30_108) (join 112 4 1 strict_30_112 strict_30_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_30_0 : ∀ i ∈ List.range 4, PhaseAt 30 (0+i) := by decide +kernel

theorem phase_30_4 : ∀ i ∈ List.range 4, PhaseAt 30 (4+i) := by decide +kernel

theorem phase_30_8 : ∀ i ∈ List.range 4, PhaseAt 30 (8+i) := by decide +kernel

theorem phase_30_12 : ∀ i ∈ List.range 4, PhaseAt 30 (12+i) := by decide +kernel

theorem phase_30_16 : ∀ i ∈ List.range 4, PhaseAt 30 (16+i) := by decide +kernel

theorem phase_30_20 : ∀ i ∈ List.range 4, PhaseAt 30 (20+i) := by decide +kernel

theorem phase_30_24 : ∀ i ∈ List.range 4, PhaseAt 30 (24+i) := by decide +kernel

theorem phase_30_28 : ∀ i ∈ List.range 4, PhaseAt 30 (28+i) := by decide +kernel

theorem phase_30_32 : ∀ i ∈ List.range 4, PhaseAt 30 (32+i) := by decide +kernel

theorem phase_30_36 : ∀ i ∈ List.range 4, PhaseAt 30 (36+i) := by decide +kernel

theorem phase_30_40 : ∀ i ∈ List.range 4, PhaseAt 30 (40+i) := by decide +kernel

theorem phase_30_44 : ∀ i ∈ List.range 4, PhaseAt 30 (44+i) := by decide +kernel

theorem phase_30_48 : ∀ i ∈ List.range 4, PhaseAt 30 (48+i) := by decide +kernel

theorem phase_30_52 : ∀ i ∈ List.range 4, PhaseAt 30 (52+i) := by decide +kernel

theorem phase_30_56 : ∀ i ∈ List.range 4, PhaseAt 30 (56+i) := by decide +kernel

theorem phase_30_60 : ∀ i ∈ List.range 4, PhaseAt 30 (60+i) := by decide +kernel

theorem phase_30_64 : ∀ i ∈ List.range 4, PhaseAt 30 (64+i) := by decide +kernel

theorem phase_30_68 : ∀ i ∈ List.range 4, PhaseAt 30 (68+i) := by decide +kernel

theorem phase_30_72 : ∀ i ∈ List.range 4, PhaseAt 30 (72+i) := by decide +kernel

theorem phase_30_76 : ∀ i ∈ List.range 4, PhaseAt 30 (76+i) := by decide +kernel

theorem phase_30_80 : ∀ i ∈ List.range 4, PhaseAt 30 (80+i) := by decide +kernel

theorem phase_30_84 : ∀ i ∈ List.range 4, PhaseAt 30 (84+i) := by decide +kernel

theorem phase_30_88 : ∀ i ∈ List.range 4, PhaseAt 30 (88+i) := by decide +kernel

theorem phase_30_92 : ∀ i ∈ List.range 4, PhaseAt 30 (92+i) := by decide +kernel

theorem phase_30_96 : ∀ i ∈ List.range 4, PhaseAt 30 (96+i) := by decide +kernel

theorem phase_30_100 : ∀ i ∈ List.range 4, PhaseAt 30 (100+i) := by decide +kernel

theorem phase_30_104 : ∀ i ∈ List.range 4, PhaseAt 30 (104+i) := by decide +kernel

theorem phase_30_108 : ∀ i ∈ List.range 4, PhaseAt 30 (108+i) := by decide +kernel

theorem phase_30_112 : ∀ i ∈ List.range 4, PhaseAt 30 (112+i) := by decide +kernel

theorem phase_30_116 : ∀ i ∈ List.range 1, PhaseAt 30 (116+i) := by decide +kernel

theorem phase_30 (v : ℕ) (hv : v ∈ List.range 117) : PhaseAt 30 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 30 v)
  have h := (join 0 60 57 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_30_0 (join 4 4 4 phase_30_4 phase_30_8)) (join 12 8 8 (join 12 4 4 phase_30_12 phase_30_16) (join 20 4 4 phase_30_20 phase_30_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_30_28 phase_30_32) (join 36 4 4 phase_30_36 phase_30_40)) (join 44 8 8 (join 44 4 4 phase_30_44 phase_30_48) (join 52 4 4 phase_30_52 phase_30_56)))) (join 60 28 29 (join 60 12 16 (join 60 4 8 phase_30_60 (join 64 4 4 phase_30_64 phase_30_68)) (join 72 8 8 (join 72 4 4 phase_30_72 phase_30_76) (join 80 4 4 phase_30_80 phase_30_84))) (join 88 16 13 (join 88 8 8 (join 88 4 4 phase_30_88 phase_30_92) (join 96 4 4 phase_30_96 phase_30_100)) (join 104 8 5 (join 104 4 4 phase_30_104 phase_30_108) (join 112 4 1 phase_30_112 phase_30_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_30_0 : ∀ i ∈ List.range 1, ThresholdAt 30 (0+i) := by decide +kernel

theorem threshold_30_1 : ∀ i ∈ List.range 1, ThresholdAt 30 (1+i) := by decide +kernel

theorem threshold_30_2 : ∀ i ∈ List.range 1, ThresholdAt 30 (2+i) := by decide +kernel

theorem threshold_30_3 : ∀ i ∈ List.range 1, ThresholdAt 30 (3+i) := by decide +kernel

theorem threshold_30_4 : ∀ i ∈ List.range 1, ThresholdAt 30 (4+i) := by decide +kernel

theorem threshold_30_5 : ∀ i ∈ List.range 1, ThresholdAt 30 (5+i) := by decide +kernel

theorem threshold_30_6 : ∀ i ∈ List.range 1, ThresholdAt 30 (6+i) := by decide +kernel

theorem threshold_30_7 : ∀ i ∈ List.range 1, ThresholdAt 30 (7+i) := by decide +kernel

theorem threshold_30_8 : ∀ i ∈ List.range 1, ThresholdAt 30 (8+i) := by decide +kernel

theorem threshold_30_9 : ∀ i ∈ List.range 1, ThresholdAt 30 (9+i) := by decide +kernel

theorem threshold_30_10 : ∀ i ∈ List.range 1, ThresholdAt 30 (10+i) := by decide +kernel

theorem threshold_30_11 : ∀ i ∈ List.range 1, ThresholdAt 30 (11+i) := by decide +kernel

theorem threshold_30_12 : ∀ i ∈ List.range 1, ThresholdAt 30 (12+i) := by decide +kernel

theorem threshold_30_13 : ∀ i ∈ List.range 1, ThresholdAt 30 (13+i) := by decide +kernel

theorem threshold_30_14 : ∀ i ∈ List.range 1, ThresholdAt 30 (14+i) := by decide +kernel

theorem threshold_30_15 : ∀ i ∈ List.range 1, ThresholdAt 30 (15+i) := by decide +kernel

theorem threshold_30_16 : ∀ i ∈ List.range 1, ThresholdAt 30 (16+i) := by decide +kernel

theorem threshold_30_17 : ∀ i ∈ List.range 1, ThresholdAt 30 (17+i) := by decide +kernel

theorem threshold_30_18 : ∀ i ∈ List.range 1, ThresholdAt 30 (18+i) := by decide +kernel

theorem threshold_30_19 : ∀ i ∈ List.range 1, ThresholdAt 30 (19+i) := by decide +kernel

theorem threshold_30_20 : ∀ i ∈ List.range 1, ThresholdAt 30 (20+i) := by decide +kernel

theorem threshold_30_21 : ∀ i ∈ List.range 1, ThresholdAt 30 (21+i) := by decide +kernel

theorem threshold_30_22 : ∀ i ∈ List.range 1, ThresholdAt 30 (22+i) := by decide +kernel

theorem threshold_30_23 : ∀ i ∈ List.range 1, ThresholdAt 30 (23+i) := by decide +kernel

theorem threshold_30_24 : ∀ i ∈ List.range 1, ThresholdAt 30 (24+i) := by decide +kernel

theorem threshold_30_25 : ∀ i ∈ List.range 1, ThresholdAt 30 (25+i) := by decide +kernel

theorem threshold_30_26 : ∀ i ∈ List.range 1, ThresholdAt 30 (26+i) := by decide +kernel

theorem threshold_30_27 : ∀ i ∈ List.range 1, ThresholdAt 30 (27+i) := by decide +kernel

theorem threshold_30_28 : ∀ i ∈ List.range 1, ThresholdAt 30 (28+i) := by decide +kernel

theorem threshold_30_29 : ∀ i ∈ List.range 1, ThresholdAt 30 (29+i) := by decide +kernel

theorem threshold_30_30 : ∀ i ∈ List.range 1, ThresholdAt 30 (30+i) := by decide +kernel

theorem threshold_30_31 : ∀ i ∈ List.range 1, ThresholdAt 30 (31+i) := by decide +kernel

theorem threshold_30_32 : ∀ i ∈ List.range 1, ThresholdAt 30 (32+i) := by decide +kernel

theorem threshold_30_33 : ∀ i ∈ List.range 1, ThresholdAt 30 (33+i) := by decide +kernel

theorem threshold_30_34 : ∀ i ∈ List.range 1, ThresholdAt 30 (34+i) := by decide +kernel

theorem threshold_30_35 : ∀ i ∈ List.range 1, ThresholdAt 30 (35+i) := by decide +kernel

theorem threshold_30_36 : ∀ i ∈ List.range 1, ThresholdAt 30 (36+i) := by decide +kernel

theorem threshold_30_37 : ∀ i ∈ List.range 1, ThresholdAt 30 (37+i) := by decide +kernel

theorem threshold_30_38 : ∀ i ∈ List.range 1, ThresholdAt 30 (38+i) := by decide +kernel

theorem threshold_30_39 : ∀ i ∈ List.range 1, ThresholdAt 30 (39+i) := by decide +kernel

theorem threshold_30_40 : ∀ i ∈ List.range 1, ThresholdAt 30 (40+i) := by decide +kernel

theorem threshold_30_41 : ∀ i ∈ List.range 1, ThresholdAt 30 (41+i) := by decide +kernel

theorem threshold_30_42 : ∀ i ∈ List.range 1, ThresholdAt 30 (42+i) := by decide +kernel

theorem threshold_30_43 : ∀ i ∈ List.range 1, ThresholdAt 30 (43+i) := by decide +kernel

theorem threshold_30_44 : ∀ i ∈ List.range 1, ThresholdAt 30 (44+i) := by decide +kernel

theorem threshold_30_45 : ∀ i ∈ List.range 1, ThresholdAt 30 (45+i) := by decide +kernel

theorem threshold_30_46 : ∀ i ∈ List.range 1, ThresholdAt 30 (46+i) := by decide +kernel

theorem threshold_30_47 : ∀ i ∈ List.range 1, ThresholdAt 30 (47+i) := by decide +kernel

theorem threshold_30_48 : ∀ i ∈ List.range 1, ThresholdAt 30 (48+i) := by decide +kernel

theorem threshold_30_49 : ∀ i ∈ List.range 1, ThresholdAt 30 (49+i) := by decide +kernel

theorem threshold_30_50 : ∀ i ∈ List.range 1, ThresholdAt 30 (50+i) := by decide +kernel

theorem threshold_30_51 : ∀ i ∈ List.range 1, ThresholdAt 30 (51+i) := by decide +kernel

theorem threshold_30_52 : ∀ i ∈ List.range 1, ThresholdAt 30 (52+i) := by decide +kernel

theorem threshold_30_53 : ∀ i ∈ List.range 1, ThresholdAt 30 (53+i) := by decide +kernel

theorem threshold_30_54 : ∀ i ∈ List.range 1, ThresholdAt 30 (54+i) := by decide +kernel

theorem threshold_30_55 : ∀ i ∈ List.range 1, ThresholdAt 30 (55+i) := by decide +kernel

theorem threshold_30_56 : ∀ i ∈ List.range 1, ThresholdAt 30 (56+i) := by decide +kernel

theorem threshold_30_57 : ∀ i ∈ List.range 1, ThresholdAt 30 (57+i) := by decide +kernel

theorem threshold_30_58 : ∀ i ∈ List.range 1, ThresholdAt 30 (58+i) := by decide +kernel

theorem threshold_30_59 : ∀ i ∈ List.range 1, ThresholdAt 30 (59+i) := by decide +kernel

theorem threshold_30_60 : ∀ i ∈ List.range 1, ThresholdAt 30 (60+i) := by decide +kernel

theorem threshold_30_61 : ∀ i ∈ List.range 1, ThresholdAt 30 (61+i) := by decide +kernel

theorem threshold_30_62 : ∀ i ∈ List.range 1, ThresholdAt 30 (62+i) := by decide +kernel

theorem threshold_30_63 : ∀ i ∈ List.range 1, ThresholdAt 30 (63+i) := by decide +kernel

theorem threshold_30_64 : ∀ i ∈ List.range 1, ThresholdAt 30 (64+i) := by decide +kernel

theorem threshold_30_65 : ∀ i ∈ List.range 1, ThresholdAt 30 (65+i) := by decide +kernel

theorem threshold_30_66 : ∀ i ∈ List.range 1, ThresholdAt 30 (66+i) := by decide +kernel

theorem threshold_30_67 : ∀ i ∈ List.range 1, ThresholdAt 30 (67+i) := by decide +kernel

theorem threshold_30_68 : ∀ i ∈ List.range 1, ThresholdAt 30 (68+i) := by decide +kernel

theorem threshold_30_69 : ∀ i ∈ List.range 1, ThresholdAt 30 (69+i) := by decide +kernel

theorem threshold_30_70 : ∀ i ∈ List.range 1, ThresholdAt 30 (70+i) := by decide +kernel

theorem threshold_30_71 : ∀ i ∈ List.range 1, ThresholdAt 30 (71+i) := by decide +kernel

theorem threshold_30_72 : ∀ i ∈ List.range 1, ThresholdAt 30 (72+i) := by decide +kernel

theorem threshold_30_73 : ∀ i ∈ List.range 1, ThresholdAt 30 (73+i) := by decide +kernel

theorem threshold_30_74 : ∀ i ∈ List.range 1, ThresholdAt 30 (74+i) := by decide +kernel

theorem threshold_30_75 : ∀ i ∈ List.range 1, ThresholdAt 30 (75+i) := by decide +kernel

theorem threshold_30_76 : ∀ i ∈ List.range 1, ThresholdAt 30 (76+i) := by decide +kernel

theorem threshold_30_77 : ∀ i ∈ List.range 1, ThresholdAt 30 (77+i) := by decide +kernel

theorem threshold_30_78 : ∀ i ∈ List.range 1, ThresholdAt 30 (78+i) := by decide +kernel

theorem threshold_30_79 : ∀ i ∈ List.range 1, ThresholdAt 30 (79+i) := by decide +kernel

theorem threshold_30_80 : ∀ i ∈ List.range 1, ThresholdAt 30 (80+i) := by decide +kernel

theorem threshold_30_81 : ∀ i ∈ List.range 1, ThresholdAt 30 (81+i) := by decide +kernel

theorem threshold_30_82 : ∀ i ∈ List.range 1, ThresholdAt 30 (82+i) := by decide +kernel

theorem threshold_30_83 : ∀ i ∈ List.range 1, ThresholdAt 30 (83+i) := by decide +kernel

theorem threshold_30_84 : ∀ i ∈ List.range 1, ThresholdAt 30 (84+i) := by decide +kernel

theorem threshold_30_85 : ∀ i ∈ List.range 1, ThresholdAt 30 (85+i) := by decide +kernel

theorem threshold_30_86 : ∀ i ∈ List.range 1, ThresholdAt 30 (86+i) := by decide +kernel

theorem threshold_30_87 : ∀ i ∈ List.range 1, ThresholdAt 30 (87+i) := by decide +kernel

theorem threshold_30_88 : ∀ i ∈ List.range 1, ThresholdAt 30 (88+i) := by decide +kernel

theorem threshold_30_89 : ∀ i ∈ List.range 1, ThresholdAt 30 (89+i) := by decide +kernel

theorem threshold_30_90 : ∀ i ∈ List.range 1, ThresholdAt 30 (90+i) := by decide +kernel

theorem threshold_30_91 : ∀ i ∈ List.range 1, ThresholdAt 30 (91+i) := by decide +kernel

theorem threshold_30_92 : ∀ i ∈ List.range 1, ThresholdAt 30 (92+i) := by decide +kernel

theorem threshold_30_93 : ∀ i ∈ List.range 1, ThresholdAt 30 (93+i) := by decide +kernel

theorem threshold_30_94 : ∀ i ∈ List.range 1, ThresholdAt 30 (94+i) := by decide +kernel

theorem threshold_30_95 : ∀ i ∈ List.range 1, ThresholdAt 30 (95+i) := by decide +kernel

theorem threshold_30_96 : ∀ i ∈ List.range 1, ThresholdAt 30 (96+i) := by decide +kernel

theorem threshold_30_97 : ∀ i ∈ List.range 1, ThresholdAt 30 (97+i) := by decide +kernel

theorem threshold_30_98 : ∀ i ∈ List.range 1, ThresholdAt 30 (98+i) := by decide +kernel

theorem threshold_30_99 : ∀ i ∈ List.range 1, ThresholdAt 30 (99+i) := by decide +kernel

theorem threshold_30_100 : ∀ i ∈ List.range 1, ThresholdAt 30 (100+i) := by decide +kernel

theorem threshold_30_101 : ∀ i ∈ List.range 1, ThresholdAt 30 (101+i) := by decide +kernel

theorem threshold_30_102 : ∀ i ∈ List.range 1, ThresholdAt 30 (102+i) := by decide +kernel

theorem threshold_30_103 : ∀ i ∈ List.range 1, ThresholdAt 30 (103+i) := by decide +kernel

theorem threshold_30_104 : ∀ i ∈ List.range 1, ThresholdAt 30 (104+i) := by decide +kernel

theorem threshold_30_105 : ∀ i ∈ List.range 1, ThresholdAt 30 (105+i) := by decide +kernel

theorem threshold_30_106 : ∀ i ∈ List.range 1, ThresholdAt 30 (106+i) := by decide +kernel

theorem threshold_30_107 : ∀ i ∈ List.range 1, ThresholdAt 30 (107+i) := by decide +kernel

theorem threshold_30_108 : ∀ i ∈ List.range 1, ThresholdAt 30 (108+i) := by decide +kernel

theorem threshold_30_109 : ∀ i ∈ List.range 1, ThresholdAt 30 (109+i) := by decide +kernel

theorem threshold_30_110 : ∀ i ∈ List.range 1, ThresholdAt 30 (110+i) := by decide +kernel

theorem threshold_30_111 : ∀ i ∈ List.range 1, ThresholdAt 30 (111+i) := by decide +kernel

theorem threshold_30_112 : ∀ i ∈ List.range 1, ThresholdAt 30 (112+i) := by decide +kernel

theorem threshold_30_113 : ∀ i ∈ List.range 1, ThresholdAt 30 (113+i) := by decide +kernel

theorem threshold_30_114 : ∀ i ∈ List.range 1, ThresholdAt 30 (114+i) := by decide +kernel

theorem threshold_30_115 : ∀ i ∈ List.range 1, ThresholdAt 30 (115+i) := by decide +kernel

theorem threshold_30_116 : ∀ i ∈ List.range 1, ThresholdAt 30 (116+i) := by decide +kernel

theorem threshold_30 (v : ℕ) (hv : v ∈ List.range 117) : ThresholdAt 30 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 30 v)
  have h := (join 0 58 59 (join 0 29 29 (join 0 14 15 (join 0 7 7 (join 0 3 4 (join 0 1 2 threshold_30_0 (join 1 1 1 threshold_30_1 threshold_30_2)) (join 3 2 2 (join 3 1 1 threshold_30_3 threshold_30_4) (join 5 1 1 threshold_30_5 threshold_30_6))) (join 7 3 4 (join 7 1 2 threshold_30_7 (join 8 1 1 threshold_30_8 threshold_30_9)) (join 10 2 2 (join 10 1 1 threshold_30_10 threshold_30_11) (join 12 1 1 threshold_30_12 threshold_30_13)))) (join 14 7 8 (join 14 3 4 (join 14 1 2 threshold_30_14 (join 15 1 1 threshold_30_15 threshold_30_16)) (join 17 2 2 (join 17 1 1 threshold_30_17 threshold_30_18) (join 19 1 1 threshold_30_19 threshold_30_20))) (join 21 4 4 (join 21 2 2 (join 21 1 1 threshold_30_21 threshold_30_22) (join 23 1 1 threshold_30_23 threshold_30_24)) (join 25 2 2 (join 25 1 1 threshold_30_25 threshold_30_26) (join 27 1 1 threshold_30_27 threshold_30_28))))) (join 29 14 15 (join 29 7 7 (join 29 3 4 (join 29 1 2 threshold_30_29 (join 30 1 1 threshold_30_30 threshold_30_31)) (join 32 2 2 (join 32 1 1 threshold_30_32 threshold_30_33) (join 34 1 1 threshold_30_34 threshold_30_35))) (join 36 3 4 (join 36 1 2 threshold_30_36 (join 37 1 1 threshold_30_37 threshold_30_38)) (join 39 2 2 (join 39 1 1 threshold_30_39 threshold_30_40) (join 41 1 1 threshold_30_41 threshold_30_42)))) (join 43 7 8 (join 43 3 4 (join 43 1 2 threshold_30_43 (join 44 1 1 threshold_30_44 threshold_30_45)) (join 46 2 2 (join 46 1 1 threshold_30_46 threshold_30_47) (join 48 1 1 threshold_30_48 threshold_30_49))) (join 50 4 4 (join 50 2 2 (join 50 1 1 threshold_30_50 threshold_30_51) (join 52 1 1 threshold_30_52 threshold_30_53)) (join 54 2 2 (join 54 1 1 threshold_30_54 threshold_30_55) (join 56 1 1 threshold_30_56 threshold_30_57)))))) (join 58 29 30 (join 58 14 15 (join 58 7 7 (join 58 3 4 (join 58 1 2 threshold_30_58 (join 59 1 1 threshold_30_59 threshold_30_60)) (join 61 2 2 (join 61 1 1 threshold_30_61 threshold_30_62) (join 63 1 1 threshold_30_63 threshold_30_64))) (join 65 3 4 (join 65 1 2 threshold_30_65 (join 66 1 1 threshold_30_66 threshold_30_67)) (join 68 2 2 (join 68 1 1 threshold_30_68 threshold_30_69) (join 70 1 1 threshold_30_70 threshold_30_71)))) (join 72 7 8 (join 72 3 4 (join 72 1 2 threshold_30_72 (join 73 1 1 threshold_30_73 threshold_30_74)) (join 75 2 2 (join 75 1 1 threshold_30_75 threshold_30_76) (join 77 1 1 threshold_30_77 threshold_30_78))) (join 79 4 4 (join 79 2 2 (join 79 1 1 threshold_30_79 threshold_30_80) (join 81 1 1 threshold_30_81 threshold_30_82)) (join 83 2 2 (join 83 1 1 threshold_30_83 threshold_30_84) (join 85 1 1 threshold_30_85 threshold_30_86))))) (join 87 15 15 (join 87 7 8 (join 87 3 4 (join 87 1 2 threshold_30_87 (join 88 1 1 threshold_30_88 threshold_30_89)) (join 90 2 2 (join 90 1 1 threshold_30_90 threshold_30_91) (join 92 1 1 threshold_30_92 threshold_30_93))) (join 94 4 4 (join 94 2 2 (join 94 1 1 threshold_30_94 threshold_30_95) (join 96 1 1 threshold_30_96 threshold_30_97)) (join 98 2 2 (join 98 1 1 threshold_30_98 threshold_30_99) (join 100 1 1 threshold_30_100 threshold_30_101)))) (join 102 7 8 (join 102 3 4 (join 102 1 2 threshold_30_102 (join 103 1 1 threshold_30_103 threshold_30_104)) (join 105 2 2 (join 105 1 1 threshold_30_105 threshold_30_106) (join 107 1 1 threshold_30_107 threshold_30_108))) (join 109 4 4 (join 109 2 2 (join 109 1 1 threshold_30_109 threshold_30_110) (join 111 1 1 threshold_30_111 threshold_30_112)) (join 113 2 2 (join 113 1 1 threshold_30_113 threshold_30_114) (join 115 1 1 threshold_30_115 threshold_30_116)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_30_0 : ∀ i ∈ List.range 4, LedgerAt 30 (0+i) := by decide +kernel

theorem ledger_30_4 : ∀ i ∈ List.range 4, LedgerAt 30 (4+i) := by decide +kernel

theorem ledger_30_8 : ∀ i ∈ List.range 4, LedgerAt 30 (8+i) := by decide +kernel

theorem ledger_30_12 : ∀ i ∈ List.range 4, LedgerAt 30 (12+i) := by decide +kernel

theorem ledger_30_16 : ∀ i ∈ List.range 4, LedgerAt 30 (16+i) := by decide +kernel

theorem ledger_30_20 : ∀ i ∈ List.range 4, LedgerAt 30 (20+i) := by decide +kernel

theorem ledger_30_24 : ∀ i ∈ List.range 4, LedgerAt 30 (24+i) := by decide +kernel

theorem ledger_30_28 : ∀ i ∈ List.range 4, LedgerAt 30 (28+i) := by decide +kernel

theorem ledger_30_32 : ∀ i ∈ List.range 4, LedgerAt 30 (32+i) := by decide +kernel

theorem ledger_30_36 : ∀ i ∈ List.range 4, LedgerAt 30 (36+i) := by decide +kernel

theorem ledger_30_40 : ∀ i ∈ List.range 4, LedgerAt 30 (40+i) := by decide +kernel

theorem ledger_30_44 : ∀ i ∈ List.range 4, LedgerAt 30 (44+i) := by decide +kernel

theorem ledger_30_48 : ∀ i ∈ List.range 4, LedgerAt 30 (48+i) := by decide +kernel

theorem ledger_30_52 : ∀ i ∈ List.range 4, LedgerAt 30 (52+i) := by decide +kernel

theorem ledger_30_56 : ∀ i ∈ List.range 4, LedgerAt 30 (56+i) := by decide +kernel

theorem ledger_30_60 : ∀ i ∈ List.range 4, LedgerAt 30 (60+i) := by decide +kernel

theorem ledger_30_64 : ∀ i ∈ List.range 4, LedgerAt 30 (64+i) := by decide +kernel

theorem ledger_30_68 : ∀ i ∈ List.range 4, LedgerAt 30 (68+i) := by decide +kernel

theorem ledger_30_72 : ∀ i ∈ List.range 4, LedgerAt 30 (72+i) := by decide +kernel

theorem ledger_30_76 : ∀ i ∈ List.range 4, LedgerAt 30 (76+i) := by decide +kernel

theorem ledger_30_80 : ∀ i ∈ List.range 4, LedgerAt 30 (80+i) := by decide +kernel

theorem ledger_30_84 : ∀ i ∈ List.range 4, LedgerAt 30 (84+i) := by decide +kernel

theorem ledger_30_88 : ∀ i ∈ List.range 4, LedgerAt 30 (88+i) := by decide +kernel

theorem ledger_30_92 : ∀ i ∈ List.range 4, LedgerAt 30 (92+i) := by decide +kernel

theorem ledger_30_96 : ∀ i ∈ List.range 4, LedgerAt 30 (96+i) := by decide +kernel

theorem ledger_30_100 : ∀ i ∈ List.range 4, LedgerAt 30 (100+i) := by decide +kernel

theorem ledger_30_104 : ∀ i ∈ List.range 4, LedgerAt 30 (104+i) := by decide +kernel

theorem ledger_30_108 : ∀ i ∈ List.range 4, LedgerAt 30 (108+i) := by decide +kernel

theorem ledger_30_112 : ∀ i ∈ List.range 4, LedgerAt 30 (112+i) := by decide +kernel

theorem ledger_30_116 : ∀ i ∈ List.range 1, LedgerAt 30 (116+i) := by decide +kernel

theorem ledger_30 (v : ℕ) (hv : v ∈ List.range 117) : LedgerAt 30 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 30 v)
  have h := (join 0 60 57 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_30_0 (join 4 4 4 ledger_30_4 ledger_30_8)) (join 12 8 8 (join 12 4 4 ledger_30_12 ledger_30_16) (join 20 4 4 ledger_30_20 ledger_30_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_30_28 ledger_30_32) (join 36 4 4 ledger_30_36 ledger_30_40)) (join 44 8 8 (join 44 4 4 ledger_30_44 ledger_30_48) (join 52 4 4 ledger_30_52 ledger_30_56)))) (join 60 28 29 (join 60 12 16 (join 60 4 8 ledger_30_60 (join 64 4 4 ledger_30_64 ledger_30_68)) (join 72 8 8 (join 72 4 4 ledger_30_72 ledger_30_76) (join 80 4 4 ledger_30_80 ledger_30_84))) (join 88 16 13 (join 88 8 8 (join 88 4 4 ledger_30_88 ledger_30_92) (join 96 4 4 ledger_30_96 ledger_30_100)) (join 104 8 5 (join 104 4 4 ledger_30_104 ledger_30_108) (join 112 4 1 ledger_30_112 ledger_30_116)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
