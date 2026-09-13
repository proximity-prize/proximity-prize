import ProximityPrize.SubmissionLower.BoundaryTailCheckedR286807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_29_0 : ∀ i ∈ List.range 4, GeometryAt 29 (0+i) := by decide +kernel

theorem geometry_29_4 : ∀ i ∈ List.range 4, GeometryAt 29 (4+i) := by decide +kernel

theorem geometry_29_8 : ∀ i ∈ List.range 4, GeometryAt 29 (8+i) := by decide +kernel

theorem geometry_29_12 : ∀ i ∈ List.range 4, GeometryAt 29 (12+i) := by decide +kernel

theorem geometry_29_16 : ∀ i ∈ List.range 4, GeometryAt 29 (16+i) := by decide +kernel

theorem geometry_29_20 : ∀ i ∈ List.range 4, GeometryAt 29 (20+i) := by decide +kernel

theorem geometry_29_24 : ∀ i ∈ List.range 4, GeometryAt 29 (24+i) := by decide +kernel

theorem geometry_29_28 : ∀ i ∈ List.range 4, GeometryAt 29 (28+i) := by decide +kernel

theorem geometry_29_32 : ∀ i ∈ List.range 4, GeometryAt 29 (32+i) := by decide +kernel

theorem geometry_29_36 : ∀ i ∈ List.range 4, GeometryAt 29 (36+i) := by decide +kernel

theorem geometry_29_40 : ∀ i ∈ List.range 4, GeometryAt 29 (40+i) := by decide +kernel

theorem geometry_29_44 : ∀ i ∈ List.range 4, GeometryAt 29 (44+i) := by decide +kernel

theorem geometry_29_48 : ∀ i ∈ List.range 4, GeometryAt 29 (48+i) := by decide +kernel

theorem geometry_29_52 : ∀ i ∈ List.range 4, GeometryAt 29 (52+i) := by decide +kernel

theorem geometry_29_56 : ∀ i ∈ List.range 4, GeometryAt 29 (56+i) := by decide +kernel

theorem geometry_29_60 : ∀ i ∈ List.range 4, GeometryAt 29 (60+i) := by decide +kernel

theorem geometry_29_64 : ∀ i ∈ List.range 4, GeometryAt 29 (64+i) := by decide +kernel

theorem geometry_29_68 : ∀ i ∈ List.range 4, GeometryAt 29 (68+i) := by decide +kernel

theorem geometry_29_72 : ∀ i ∈ List.range 4, GeometryAt 29 (72+i) := by decide +kernel

theorem geometry_29_76 : ∀ i ∈ List.range 4, GeometryAt 29 (76+i) := by decide +kernel

theorem geometry_29_80 : ∀ i ∈ List.range 4, GeometryAt 29 (80+i) := by decide +kernel

theorem geometry_29_84 : ∀ i ∈ List.range 4, GeometryAt 29 (84+i) := by decide +kernel

theorem geometry_29_88 : ∀ i ∈ List.range 4, GeometryAt 29 (88+i) := by decide +kernel

theorem geometry_29_92 : ∀ i ∈ List.range 4, GeometryAt 29 (92+i) := by decide +kernel

theorem geometry_29_96 : ∀ i ∈ List.range 4, GeometryAt 29 (96+i) := by decide +kernel

theorem geometry_29_100 : ∀ i ∈ List.range 4, GeometryAt 29 (100+i) := by decide +kernel

theorem geometry_29_104 : ∀ i ∈ List.range 4, GeometryAt 29 (104+i) := by decide +kernel

theorem geometry_29_108 : ∀ i ∈ List.range 4, GeometryAt 29 (108+i) := by decide +kernel

theorem geometry_29_112 : ∀ i ∈ List.range 4, GeometryAt 29 (112+i) := by decide +kernel

theorem geometry_29_116 : ∀ i ∈ List.range 2, GeometryAt 29 (116+i) := by decide +kernel

theorem geometry_29 (v : ℕ) (hv : v ∈ List.range 118) : GeometryAt 29 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 29 v)
  have h := (join 0 60 58 (join 0 28 32 (join 0 12 16 (join 0 4 8 geometry_29_0 (join 4 4 4 geometry_29_4 geometry_29_8)) (join 12 8 8 (join 12 4 4 geometry_29_12 geometry_29_16) (join 20 4 4 geometry_29_20 geometry_29_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 geometry_29_28 geometry_29_32) (join 36 4 4 geometry_29_36 geometry_29_40)) (join 44 8 8 (join 44 4 4 geometry_29_44 geometry_29_48) (join 52 4 4 geometry_29_52 geometry_29_56)))) (join 60 28 30 (join 60 12 16 (join 60 4 8 geometry_29_60 (join 64 4 4 geometry_29_64 geometry_29_68)) (join 72 8 8 (join 72 4 4 geometry_29_72 geometry_29_76) (join 80 4 4 geometry_29_80 geometry_29_84))) (join 88 16 14 (join 88 8 8 (join 88 4 4 geometry_29_88 geometry_29_92) (join 96 4 4 geometry_29_96 geometry_29_100)) (join 104 8 6 (join 104 4 4 geometry_29_104 geometry_29_108) (join 112 4 2 geometry_29_112 geometry_29_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_29_0 : ∀ i ∈ List.range 4, StrictAt 29 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (0+i)) 29 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_4 : ∀ i ∈ List.range 4, StrictAt 29 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (4+i)) 29 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_8 : ∀ i ∈ List.range 4, StrictAt 29 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (8+i)) 29 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_12 : ∀ i ∈ List.range 4, StrictAt 29 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (12+i)) 29 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_16 : ∀ i ∈ List.range 4, StrictAt 29 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (16+i)) 29 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_20 : ∀ i ∈ List.range 4, StrictAt 29 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (20+i)) 29 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_24 : ∀ i ∈ List.range 4, StrictAt 29 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (24+i)) 29 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_28 : ∀ i ∈ List.range 4, StrictAt 29 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (28+i)) 29 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_32 : ∀ i ∈ List.range 4, StrictAt 29 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (32+i)) 29 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_36 : ∀ i ∈ List.range 4, StrictAt 29 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (36+i)) 29 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_40 : ∀ i ∈ List.range 4, StrictAt 29 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (40+i)) 29 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_44 : ∀ i ∈ List.range 4, StrictAt 29 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (44+i)) 29 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_48 : ∀ i ∈ List.range 4, StrictAt 29 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (48+i)) 29 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_52 : ∀ i ∈ List.range 4, StrictAt 29 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (52+i)) 29 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_56 : ∀ i ∈ List.range 4, StrictAt 29 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (56+i)) 29 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_60 : ∀ i ∈ List.range 4, StrictAt 29 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (60+i)) 29 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_64 : ∀ i ∈ List.range 4, StrictAt 29 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (64+i)) 29 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_68 : ∀ i ∈ List.range 4, StrictAt 29 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (68+i)) 29 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_72 : ∀ i ∈ List.range 4, StrictAt 29 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (72+i)) 29 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_76 : ∀ i ∈ List.range 4, StrictAt 29 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (76+i)) 29 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_80 : ∀ i ∈ List.range 4, StrictAt 29 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (80+i)) 29 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_84 : ∀ i ∈ List.range 4, StrictAt 29 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (84+i)) 29 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_88 : ∀ i ∈ List.range 4, StrictAt 29 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (88+i)) 29 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_92 : ∀ i ∈ List.range 4, StrictAt 29 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (92+i)) 29 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_96 : ∀ i ∈ List.range 4, StrictAt 29 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (96+i)) 29 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_100 : ∀ i ∈ List.range 4, StrictAt 29 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (100+i)) 29 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_104 : ∀ i ∈ List.range 4, StrictAt 29 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (104+i)) 29 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_108 : ∀ i ∈ List.range 4, StrictAt 29 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (108+i)) 29 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_112 : ∀ i ∈ List.range 4, StrictAt 29 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (112+i)) 29 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29_116 : ∀ i ∈ List.range 2, StrictAt 29 (116+i) := by
  have h : ∀ i ∈ List.range 2, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 29 (116+i)) 29 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_29 (v : ℕ) (hv : v ∈ List.range 118) : StrictAt 29 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 29 v)
  have h := (join 0 60 58 (join 0 28 32 (join 0 12 16 (join 0 4 8 strict_29_0 (join 4 4 4 strict_29_4 strict_29_8)) (join 12 8 8 (join 12 4 4 strict_29_12 strict_29_16) (join 20 4 4 strict_29_20 strict_29_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 strict_29_28 strict_29_32) (join 36 4 4 strict_29_36 strict_29_40)) (join 44 8 8 (join 44 4 4 strict_29_44 strict_29_48) (join 52 4 4 strict_29_52 strict_29_56)))) (join 60 28 30 (join 60 12 16 (join 60 4 8 strict_29_60 (join 64 4 4 strict_29_64 strict_29_68)) (join 72 8 8 (join 72 4 4 strict_29_72 strict_29_76) (join 80 4 4 strict_29_80 strict_29_84))) (join 88 16 14 (join 88 8 8 (join 88 4 4 strict_29_88 strict_29_92) (join 96 4 4 strict_29_96 strict_29_100)) (join 104 8 6 (join 104 4 4 strict_29_104 strict_29_108) (join 112 4 2 strict_29_112 strict_29_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_29_0 : ∀ i ∈ List.range 4, PhaseAt 29 (0+i) := by decide +kernel

theorem phase_29_4 : ∀ i ∈ List.range 4, PhaseAt 29 (4+i) := by decide +kernel

theorem phase_29_8 : ∀ i ∈ List.range 4, PhaseAt 29 (8+i) := by decide +kernel

theorem phase_29_12 : ∀ i ∈ List.range 4, PhaseAt 29 (12+i) := by decide +kernel

theorem phase_29_16 : ∀ i ∈ List.range 4, PhaseAt 29 (16+i) := by decide +kernel

theorem phase_29_20 : ∀ i ∈ List.range 4, PhaseAt 29 (20+i) := by decide +kernel

theorem phase_29_24 : ∀ i ∈ List.range 4, PhaseAt 29 (24+i) := by decide +kernel

theorem phase_29_28 : ∀ i ∈ List.range 4, PhaseAt 29 (28+i) := by decide +kernel

theorem phase_29_32 : ∀ i ∈ List.range 4, PhaseAt 29 (32+i) := by decide +kernel

theorem phase_29_36 : ∀ i ∈ List.range 4, PhaseAt 29 (36+i) := by decide +kernel

theorem phase_29_40 : ∀ i ∈ List.range 4, PhaseAt 29 (40+i) := by decide +kernel

theorem phase_29_44 : ∀ i ∈ List.range 4, PhaseAt 29 (44+i) := by decide +kernel

theorem phase_29_48 : ∀ i ∈ List.range 4, PhaseAt 29 (48+i) := by decide +kernel

theorem phase_29_52 : ∀ i ∈ List.range 4, PhaseAt 29 (52+i) := by decide +kernel

theorem phase_29_56 : ∀ i ∈ List.range 4, PhaseAt 29 (56+i) := by decide +kernel

theorem phase_29_60 : ∀ i ∈ List.range 4, PhaseAt 29 (60+i) := by decide +kernel

theorem phase_29_64 : ∀ i ∈ List.range 4, PhaseAt 29 (64+i) := by decide +kernel

theorem phase_29_68 : ∀ i ∈ List.range 4, PhaseAt 29 (68+i) := by decide +kernel

theorem phase_29_72 : ∀ i ∈ List.range 4, PhaseAt 29 (72+i) := by decide +kernel

theorem phase_29_76 : ∀ i ∈ List.range 4, PhaseAt 29 (76+i) := by decide +kernel

theorem phase_29_80 : ∀ i ∈ List.range 4, PhaseAt 29 (80+i) := by decide +kernel

theorem phase_29_84 : ∀ i ∈ List.range 4, PhaseAt 29 (84+i) := by decide +kernel

theorem phase_29_88 : ∀ i ∈ List.range 4, PhaseAt 29 (88+i) := by decide +kernel

theorem phase_29_92 : ∀ i ∈ List.range 4, PhaseAt 29 (92+i) := by decide +kernel

theorem phase_29_96 : ∀ i ∈ List.range 4, PhaseAt 29 (96+i) := by decide +kernel

theorem phase_29_100 : ∀ i ∈ List.range 4, PhaseAt 29 (100+i) := by decide +kernel

theorem phase_29_104 : ∀ i ∈ List.range 4, PhaseAt 29 (104+i) := by decide +kernel

theorem phase_29_108 : ∀ i ∈ List.range 4, PhaseAt 29 (108+i) := by decide +kernel

theorem phase_29_112 : ∀ i ∈ List.range 4, PhaseAt 29 (112+i) := by decide +kernel

theorem phase_29_116 : ∀ i ∈ List.range 2, PhaseAt 29 (116+i) := by decide +kernel

theorem phase_29 (v : ℕ) (hv : v ∈ List.range 118) : PhaseAt 29 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 29 v)
  have h := (join 0 60 58 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_29_0 (join 4 4 4 phase_29_4 phase_29_8)) (join 12 8 8 (join 12 4 4 phase_29_12 phase_29_16) (join 20 4 4 phase_29_20 phase_29_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_29_28 phase_29_32) (join 36 4 4 phase_29_36 phase_29_40)) (join 44 8 8 (join 44 4 4 phase_29_44 phase_29_48) (join 52 4 4 phase_29_52 phase_29_56)))) (join 60 28 30 (join 60 12 16 (join 60 4 8 phase_29_60 (join 64 4 4 phase_29_64 phase_29_68)) (join 72 8 8 (join 72 4 4 phase_29_72 phase_29_76) (join 80 4 4 phase_29_80 phase_29_84))) (join 88 16 14 (join 88 8 8 (join 88 4 4 phase_29_88 phase_29_92) (join 96 4 4 phase_29_96 phase_29_100)) (join 104 8 6 (join 104 4 4 phase_29_104 phase_29_108) (join 112 4 2 phase_29_112 phase_29_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_29_0 : ∀ i ∈ List.range 1, ThresholdAt 29 (0+i) := by decide +kernel

theorem threshold_29_1 : ∀ i ∈ List.range 1, ThresholdAt 29 (1+i) := by decide +kernel

theorem threshold_29_2 : ∀ i ∈ List.range 1, ThresholdAt 29 (2+i) := by decide +kernel

theorem threshold_29_3 : ∀ i ∈ List.range 1, ThresholdAt 29 (3+i) := by decide +kernel

theorem threshold_29_4 : ∀ i ∈ List.range 1, ThresholdAt 29 (4+i) := by decide +kernel

theorem threshold_29_5 : ∀ i ∈ List.range 1, ThresholdAt 29 (5+i) := by decide +kernel

theorem threshold_29_6 : ∀ i ∈ List.range 1, ThresholdAt 29 (6+i) := by decide +kernel

theorem threshold_29_7 : ∀ i ∈ List.range 1, ThresholdAt 29 (7+i) := by decide +kernel

theorem threshold_29_8 : ∀ i ∈ List.range 1, ThresholdAt 29 (8+i) := by decide +kernel

theorem threshold_29_9 : ∀ i ∈ List.range 1, ThresholdAt 29 (9+i) := by decide +kernel

theorem threshold_29_10 : ∀ i ∈ List.range 1, ThresholdAt 29 (10+i) := by decide +kernel

theorem threshold_29_11 : ∀ i ∈ List.range 1, ThresholdAt 29 (11+i) := by decide +kernel

theorem threshold_29_12 : ∀ i ∈ List.range 1, ThresholdAt 29 (12+i) := by decide +kernel

theorem threshold_29_13 : ∀ i ∈ List.range 1, ThresholdAt 29 (13+i) := by decide +kernel

theorem threshold_29_14 : ∀ i ∈ List.range 1, ThresholdAt 29 (14+i) := by decide +kernel

theorem threshold_29_15 : ∀ i ∈ List.range 1, ThresholdAt 29 (15+i) := by decide +kernel

theorem threshold_29_16 : ∀ i ∈ List.range 1, ThresholdAt 29 (16+i) := by decide +kernel

theorem threshold_29_17 : ∀ i ∈ List.range 1, ThresholdAt 29 (17+i) := by decide +kernel

theorem threshold_29_18 : ∀ i ∈ List.range 1, ThresholdAt 29 (18+i) := by decide +kernel

theorem threshold_29_19 : ∀ i ∈ List.range 1, ThresholdAt 29 (19+i) := by decide +kernel

theorem threshold_29_20 : ∀ i ∈ List.range 1, ThresholdAt 29 (20+i) := by decide +kernel

theorem threshold_29_21 : ∀ i ∈ List.range 1, ThresholdAt 29 (21+i) := by decide +kernel

theorem threshold_29_22 : ∀ i ∈ List.range 1, ThresholdAt 29 (22+i) := by decide +kernel

theorem threshold_29_23 : ∀ i ∈ List.range 1, ThresholdAt 29 (23+i) := by decide +kernel

theorem threshold_29_24 : ∀ i ∈ List.range 1, ThresholdAt 29 (24+i) := by decide +kernel

theorem threshold_29_25 : ∀ i ∈ List.range 1, ThresholdAt 29 (25+i) := by decide +kernel

theorem threshold_29_26 : ∀ i ∈ List.range 1, ThresholdAt 29 (26+i) := by decide +kernel

theorem threshold_29_27 : ∀ i ∈ List.range 1, ThresholdAt 29 (27+i) := by decide +kernel

theorem threshold_29_28 : ∀ i ∈ List.range 1, ThresholdAt 29 (28+i) := by decide +kernel

theorem threshold_29_29 : ∀ i ∈ List.range 1, ThresholdAt 29 (29+i) := by decide +kernel

theorem threshold_29_30 : ∀ i ∈ List.range 1, ThresholdAt 29 (30+i) := by decide +kernel

theorem threshold_29_31 : ∀ i ∈ List.range 1, ThresholdAt 29 (31+i) := by decide +kernel

theorem threshold_29_32 : ∀ i ∈ List.range 1, ThresholdAt 29 (32+i) := by decide +kernel

theorem threshold_29_33 : ∀ i ∈ List.range 1, ThresholdAt 29 (33+i) := by decide +kernel

theorem threshold_29_34 : ∀ i ∈ List.range 1, ThresholdAt 29 (34+i) := by decide +kernel

theorem threshold_29_35 : ∀ i ∈ List.range 1, ThresholdAt 29 (35+i) := by decide +kernel

theorem threshold_29_36 : ∀ i ∈ List.range 1, ThresholdAt 29 (36+i) := by decide +kernel

theorem threshold_29_37 : ∀ i ∈ List.range 1, ThresholdAt 29 (37+i) := by decide +kernel

theorem threshold_29_38 : ∀ i ∈ List.range 1, ThresholdAt 29 (38+i) := by decide +kernel

theorem threshold_29_39 : ∀ i ∈ List.range 1, ThresholdAt 29 (39+i) := by decide +kernel

theorem threshold_29_40 : ∀ i ∈ List.range 1, ThresholdAt 29 (40+i) := by decide +kernel

theorem threshold_29_41 : ∀ i ∈ List.range 1, ThresholdAt 29 (41+i) := by decide +kernel

theorem threshold_29_42 : ∀ i ∈ List.range 1, ThresholdAt 29 (42+i) := by decide +kernel

theorem threshold_29_43 : ∀ i ∈ List.range 1, ThresholdAt 29 (43+i) := by decide +kernel

theorem threshold_29_44 : ∀ i ∈ List.range 1, ThresholdAt 29 (44+i) := by decide +kernel

theorem threshold_29_45 : ∀ i ∈ List.range 1, ThresholdAt 29 (45+i) := by decide +kernel

theorem threshold_29_46 : ∀ i ∈ List.range 1, ThresholdAt 29 (46+i) := by decide +kernel

theorem threshold_29_47 : ∀ i ∈ List.range 1, ThresholdAt 29 (47+i) := by decide +kernel

theorem threshold_29_48 : ∀ i ∈ List.range 1, ThresholdAt 29 (48+i) := by decide +kernel

theorem threshold_29_49 : ∀ i ∈ List.range 1, ThresholdAt 29 (49+i) := by decide +kernel

theorem threshold_29_50 : ∀ i ∈ List.range 1, ThresholdAt 29 (50+i) := by decide +kernel

theorem threshold_29_51 : ∀ i ∈ List.range 1, ThresholdAt 29 (51+i) := by decide +kernel

theorem threshold_29_52 : ∀ i ∈ List.range 1, ThresholdAt 29 (52+i) := by decide +kernel

theorem threshold_29_53 : ∀ i ∈ List.range 1, ThresholdAt 29 (53+i) := by decide +kernel

theorem threshold_29_54 : ∀ i ∈ List.range 1, ThresholdAt 29 (54+i) := by decide +kernel

theorem threshold_29_55 : ∀ i ∈ List.range 1, ThresholdAt 29 (55+i) := by decide +kernel

theorem threshold_29_56 : ∀ i ∈ List.range 1, ThresholdAt 29 (56+i) := by decide +kernel

theorem threshold_29_57 : ∀ i ∈ List.range 1, ThresholdAt 29 (57+i) := by decide +kernel

theorem threshold_29_58 : ∀ i ∈ List.range 1, ThresholdAt 29 (58+i) := by decide +kernel

theorem threshold_29_59 : ∀ i ∈ List.range 1, ThresholdAt 29 (59+i) := by decide +kernel

theorem threshold_29_60 : ∀ i ∈ List.range 1, ThresholdAt 29 (60+i) := by decide +kernel

theorem threshold_29_61 : ∀ i ∈ List.range 1, ThresholdAt 29 (61+i) := by decide +kernel

theorem threshold_29_62 : ∀ i ∈ List.range 1, ThresholdAt 29 (62+i) := by decide +kernel

theorem threshold_29_63 : ∀ i ∈ List.range 1, ThresholdAt 29 (63+i) := by decide +kernel

theorem threshold_29_64 : ∀ i ∈ List.range 1, ThresholdAt 29 (64+i) := by decide +kernel

theorem threshold_29_65 : ∀ i ∈ List.range 1, ThresholdAt 29 (65+i) := by decide +kernel

theorem threshold_29_66 : ∀ i ∈ List.range 1, ThresholdAt 29 (66+i) := by decide +kernel

theorem threshold_29_67 : ∀ i ∈ List.range 1, ThresholdAt 29 (67+i) := by decide +kernel

theorem threshold_29_68 : ∀ i ∈ List.range 1, ThresholdAt 29 (68+i) := by decide +kernel

theorem threshold_29_69 : ∀ i ∈ List.range 1, ThresholdAt 29 (69+i) := by decide +kernel

theorem threshold_29_70 : ∀ i ∈ List.range 1, ThresholdAt 29 (70+i) := by decide +kernel

theorem threshold_29_71 : ∀ i ∈ List.range 1, ThresholdAt 29 (71+i) := by decide +kernel

theorem threshold_29_72 : ∀ i ∈ List.range 1, ThresholdAt 29 (72+i) := by decide +kernel

theorem threshold_29_73 : ∀ i ∈ List.range 1, ThresholdAt 29 (73+i) := by decide +kernel

theorem threshold_29_74 : ∀ i ∈ List.range 1, ThresholdAt 29 (74+i) := by decide +kernel

theorem threshold_29_75 : ∀ i ∈ List.range 1, ThresholdAt 29 (75+i) := by decide +kernel

theorem threshold_29_76 : ∀ i ∈ List.range 1, ThresholdAt 29 (76+i) := by decide +kernel

theorem threshold_29_77 : ∀ i ∈ List.range 1, ThresholdAt 29 (77+i) := by decide +kernel

theorem threshold_29_78 : ∀ i ∈ List.range 1, ThresholdAt 29 (78+i) := by decide +kernel

theorem threshold_29_79 : ∀ i ∈ List.range 1, ThresholdAt 29 (79+i) := by decide +kernel

theorem threshold_29_80 : ∀ i ∈ List.range 1, ThresholdAt 29 (80+i) := by decide +kernel

theorem threshold_29_81 : ∀ i ∈ List.range 1, ThresholdAt 29 (81+i) := by decide +kernel

theorem threshold_29_82 : ∀ i ∈ List.range 1, ThresholdAt 29 (82+i) := by decide +kernel

theorem threshold_29_83 : ∀ i ∈ List.range 1, ThresholdAt 29 (83+i) := by decide +kernel

theorem threshold_29_84 : ∀ i ∈ List.range 1, ThresholdAt 29 (84+i) := by decide +kernel

theorem threshold_29_85 : ∀ i ∈ List.range 1, ThresholdAt 29 (85+i) := by decide +kernel

theorem threshold_29_86 : ∀ i ∈ List.range 1, ThresholdAt 29 (86+i) := by decide +kernel

theorem threshold_29_87 : ∀ i ∈ List.range 1, ThresholdAt 29 (87+i) := by decide +kernel

theorem threshold_29_88 : ∀ i ∈ List.range 1, ThresholdAt 29 (88+i) := by decide +kernel

theorem threshold_29_89 : ∀ i ∈ List.range 1, ThresholdAt 29 (89+i) := by decide +kernel

theorem threshold_29_90 : ∀ i ∈ List.range 1, ThresholdAt 29 (90+i) := by decide +kernel

theorem threshold_29_91 : ∀ i ∈ List.range 1, ThresholdAt 29 (91+i) := by decide +kernel

theorem threshold_29_92 : ∀ i ∈ List.range 1, ThresholdAt 29 (92+i) := by decide +kernel

theorem threshold_29_93 : ∀ i ∈ List.range 1, ThresholdAt 29 (93+i) := by decide +kernel

theorem threshold_29_94 : ∀ i ∈ List.range 1, ThresholdAt 29 (94+i) := by decide +kernel

theorem threshold_29_95 : ∀ i ∈ List.range 1, ThresholdAt 29 (95+i) := by decide +kernel

theorem threshold_29_96 : ∀ i ∈ List.range 1, ThresholdAt 29 (96+i) := by decide +kernel

theorem threshold_29_97 : ∀ i ∈ List.range 1, ThresholdAt 29 (97+i) := by decide +kernel

theorem threshold_29_98 : ∀ i ∈ List.range 1, ThresholdAt 29 (98+i) := by decide +kernel

theorem threshold_29_99 : ∀ i ∈ List.range 1, ThresholdAt 29 (99+i) := by decide +kernel

theorem threshold_29_100 : ∀ i ∈ List.range 1, ThresholdAt 29 (100+i) := by decide +kernel

theorem threshold_29_101 : ∀ i ∈ List.range 1, ThresholdAt 29 (101+i) := by decide +kernel

theorem threshold_29_102 : ∀ i ∈ List.range 1, ThresholdAt 29 (102+i) := by decide +kernel

theorem threshold_29_103 : ∀ i ∈ List.range 1, ThresholdAt 29 (103+i) := by decide +kernel

theorem threshold_29_104 : ∀ i ∈ List.range 1, ThresholdAt 29 (104+i) := by decide +kernel

theorem threshold_29_105 : ∀ i ∈ List.range 1, ThresholdAt 29 (105+i) := by decide +kernel

theorem threshold_29_106 : ∀ i ∈ List.range 1, ThresholdAt 29 (106+i) := by decide +kernel

theorem threshold_29_107 : ∀ i ∈ List.range 1, ThresholdAt 29 (107+i) := by decide +kernel

theorem threshold_29_108 : ∀ i ∈ List.range 1, ThresholdAt 29 (108+i) := by decide +kernel

theorem threshold_29_109 : ∀ i ∈ List.range 1, ThresholdAt 29 (109+i) := by decide +kernel

theorem threshold_29_110 : ∀ i ∈ List.range 1, ThresholdAt 29 (110+i) := by decide +kernel

theorem threshold_29_111 : ∀ i ∈ List.range 1, ThresholdAt 29 (111+i) := by decide +kernel

theorem threshold_29_112 : ∀ i ∈ List.range 1, ThresholdAt 29 (112+i) := by decide +kernel

theorem threshold_29_113 : ∀ i ∈ List.range 1, ThresholdAt 29 (113+i) := by decide +kernel

theorem threshold_29_114 : ∀ i ∈ List.range 1, ThresholdAt 29 (114+i) := by decide +kernel

theorem threshold_29_115 : ∀ i ∈ List.range 1, ThresholdAt 29 (115+i) := by decide +kernel

theorem threshold_29_116 : ∀ i ∈ List.range 1, ThresholdAt 29 (116+i) := by decide +kernel

theorem threshold_29_117 : ∀ i ∈ List.range 1, ThresholdAt 29 (117+i) := by decide +kernel

theorem threshold_29 (v : ℕ) (hv : v ∈ List.range 118) : ThresholdAt 29 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 29 v)
  have h := (join 0 59 59 (join 0 29 30 (join 0 14 15 (join 0 7 7 (join 0 3 4 (join 0 1 2 threshold_29_0 (join 1 1 1 threshold_29_1 threshold_29_2)) (join 3 2 2 (join 3 1 1 threshold_29_3 threshold_29_4) (join 5 1 1 threshold_29_5 threshold_29_6))) (join 7 3 4 (join 7 1 2 threshold_29_7 (join 8 1 1 threshold_29_8 threshold_29_9)) (join 10 2 2 (join 10 1 1 threshold_29_10 threshold_29_11) (join 12 1 1 threshold_29_12 threshold_29_13)))) (join 14 7 8 (join 14 3 4 (join 14 1 2 threshold_29_14 (join 15 1 1 threshold_29_15 threshold_29_16)) (join 17 2 2 (join 17 1 1 threshold_29_17 threshold_29_18) (join 19 1 1 threshold_29_19 threshold_29_20))) (join 21 4 4 (join 21 2 2 (join 21 1 1 threshold_29_21 threshold_29_22) (join 23 1 1 threshold_29_23 threshold_29_24)) (join 25 2 2 (join 25 1 1 threshold_29_25 threshold_29_26) (join 27 1 1 threshold_29_27 threshold_29_28))))) (join 29 15 15 (join 29 7 8 (join 29 3 4 (join 29 1 2 threshold_29_29 (join 30 1 1 threshold_29_30 threshold_29_31)) (join 32 2 2 (join 32 1 1 threshold_29_32 threshold_29_33) (join 34 1 1 threshold_29_34 threshold_29_35))) (join 36 4 4 (join 36 2 2 (join 36 1 1 threshold_29_36 threshold_29_37) (join 38 1 1 threshold_29_38 threshold_29_39)) (join 40 2 2 (join 40 1 1 threshold_29_40 threshold_29_41) (join 42 1 1 threshold_29_42 threshold_29_43)))) (join 44 7 8 (join 44 3 4 (join 44 1 2 threshold_29_44 (join 45 1 1 threshold_29_45 threshold_29_46)) (join 47 2 2 (join 47 1 1 threshold_29_47 threshold_29_48) (join 49 1 1 threshold_29_49 threshold_29_50))) (join 51 4 4 (join 51 2 2 (join 51 1 1 threshold_29_51 threshold_29_52) (join 53 1 1 threshold_29_53 threshold_29_54)) (join 55 2 2 (join 55 1 1 threshold_29_55 threshold_29_56) (join 57 1 1 threshold_29_57 threshold_29_58)))))) (join 59 29 30 (join 59 14 15 (join 59 7 7 (join 59 3 4 (join 59 1 2 threshold_29_59 (join 60 1 1 threshold_29_60 threshold_29_61)) (join 62 2 2 (join 62 1 1 threshold_29_62 threshold_29_63) (join 64 1 1 threshold_29_64 threshold_29_65))) (join 66 3 4 (join 66 1 2 threshold_29_66 (join 67 1 1 threshold_29_67 threshold_29_68)) (join 69 2 2 (join 69 1 1 threshold_29_69 threshold_29_70) (join 71 1 1 threshold_29_71 threshold_29_72)))) (join 73 7 8 (join 73 3 4 (join 73 1 2 threshold_29_73 (join 74 1 1 threshold_29_74 threshold_29_75)) (join 76 2 2 (join 76 1 1 threshold_29_76 threshold_29_77) (join 78 1 1 threshold_29_78 threshold_29_79))) (join 80 4 4 (join 80 2 2 (join 80 1 1 threshold_29_80 threshold_29_81) (join 82 1 1 threshold_29_82 threshold_29_83)) (join 84 2 2 (join 84 1 1 threshold_29_84 threshold_29_85) (join 86 1 1 threshold_29_86 threshold_29_87))))) (join 88 15 15 (join 88 7 8 (join 88 3 4 (join 88 1 2 threshold_29_88 (join 89 1 1 threshold_29_89 threshold_29_90)) (join 91 2 2 (join 91 1 1 threshold_29_91 threshold_29_92) (join 93 1 1 threshold_29_93 threshold_29_94))) (join 95 4 4 (join 95 2 2 (join 95 1 1 threshold_29_95 threshold_29_96) (join 97 1 1 threshold_29_97 threshold_29_98)) (join 99 2 2 (join 99 1 1 threshold_29_99 threshold_29_100) (join 101 1 1 threshold_29_101 threshold_29_102)))) (join 103 7 8 (join 103 3 4 (join 103 1 2 threshold_29_103 (join 104 1 1 threshold_29_104 threshold_29_105)) (join 106 2 2 (join 106 1 1 threshold_29_106 threshold_29_107) (join 108 1 1 threshold_29_108 threshold_29_109))) (join 110 4 4 (join 110 2 2 (join 110 1 1 threshold_29_110 threshold_29_111) (join 112 1 1 threshold_29_112 threshold_29_113)) (join 114 2 2 (join 114 1 1 threshold_29_114 threshold_29_115) (join 116 1 1 threshold_29_116 threshold_29_117)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_29_0 : ∀ i ∈ List.range 4, LedgerAt 29 (0+i) := by decide +kernel

theorem ledger_29_4 : ∀ i ∈ List.range 4, LedgerAt 29 (4+i) := by decide +kernel

theorem ledger_29_8 : ∀ i ∈ List.range 4, LedgerAt 29 (8+i) := by decide +kernel

theorem ledger_29_12 : ∀ i ∈ List.range 4, LedgerAt 29 (12+i) := by decide +kernel

theorem ledger_29_16 : ∀ i ∈ List.range 4, LedgerAt 29 (16+i) := by decide +kernel

theorem ledger_29_20 : ∀ i ∈ List.range 4, LedgerAt 29 (20+i) := by decide +kernel

theorem ledger_29_24 : ∀ i ∈ List.range 4, LedgerAt 29 (24+i) := by decide +kernel

theorem ledger_29_28 : ∀ i ∈ List.range 4, LedgerAt 29 (28+i) := by decide +kernel

theorem ledger_29_32 : ∀ i ∈ List.range 4, LedgerAt 29 (32+i) := by decide +kernel

theorem ledger_29_36 : ∀ i ∈ List.range 4, LedgerAt 29 (36+i) := by decide +kernel

theorem ledger_29_40 : ∀ i ∈ List.range 4, LedgerAt 29 (40+i) := by decide +kernel

theorem ledger_29_44 : ∀ i ∈ List.range 4, LedgerAt 29 (44+i) := by decide +kernel

theorem ledger_29_48 : ∀ i ∈ List.range 4, LedgerAt 29 (48+i) := by decide +kernel

theorem ledger_29_52 : ∀ i ∈ List.range 4, LedgerAt 29 (52+i) := by decide +kernel

theorem ledger_29_56 : ∀ i ∈ List.range 4, LedgerAt 29 (56+i) := by decide +kernel

theorem ledger_29_60 : ∀ i ∈ List.range 4, LedgerAt 29 (60+i) := by decide +kernel

theorem ledger_29_64 : ∀ i ∈ List.range 4, LedgerAt 29 (64+i) := by decide +kernel

theorem ledger_29_68 : ∀ i ∈ List.range 4, LedgerAt 29 (68+i) := by decide +kernel

theorem ledger_29_72 : ∀ i ∈ List.range 4, LedgerAt 29 (72+i) := by decide +kernel

theorem ledger_29_76 : ∀ i ∈ List.range 4, LedgerAt 29 (76+i) := by decide +kernel

theorem ledger_29_80 : ∀ i ∈ List.range 4, LedgerAt 29 (80+i) := by decide +kernel

theorem ledger_29_84 : ∀ i ∈ List.range 4, LedgerAt 29 (84+i) := by decide +kernel

theorem ledger_29_88 : ∀ i ∈ List.range 4, LedgerAt 29 (88+i) := by decide +kernel

theorem ledger_29_92 : ∀ i ∈ List.range 4, LedgerAt 29 (92+i) := by decide +kernel

theorem ledger_29_96 : ∀ i ∈ List.range 4, LedgerAt 29 (96+i) := by decide +kernel

theorem ledger_29_100 : ∀ i ∈ List.range 4, LedgerAt 29 (100+i) := by decide +kernel

theorem ledger_29_104 : ∀ i ∈ List.range 4, LedgerAt 29 (104+i) := by decide +kernel

theorem ledger_29_108 : ∀ i ∈ List.range 4, LedgerAt 29 (108+i) := by decide +kernel

theorem ledger_29_112 : ∀ i ∈ List.range 4, LedgerAt 29 (112+i) := by decide +kernel

theorem ledger_29_116 : ∀ i ∈ List.range 2, LedgerAt 29 (116+i) := by decide +kernel

theorem ledger_29 (v : ℕ) (hv : v ∈ List.range 118) : LedgerAt 29 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 29 v)
  have h := (join 0 60 58 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_29_0 (join 4 4 4 ledger_29_4 ledger_29_8)) (join 12 8 8 (join 12 4 4 ledger_29_12 ledger_29_16) (join 20 4 4 ledger_29_20 ledger_29_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_29_28 ledger_29_32) (join 36 4 4 ledger_29_36 ledger_29_40)) (join 44 8 8 (join 44 4 4 ledger_29_44 ledger_29_48) (join 52 4 4 ledger_29_52 ledger_29_56)))) (join 60 28 30 (join 60 12 16 (join 60 4 8 ledger_29_60 (join 64 4 4 ledger_29_64 ledger_29_68)) (join 72 8 8 (join 72 4 4 ledger_29_72 ledger_29_76) (join 80 4 4 ledger_29_80 ledger_29_84))) (join 88 16 14 (join 88 8 8 (join 88 4 4 ledger_29_88 ledger_29_92) (join 96 4 4 ledger_29_96 ledger_29_100)) (join 104 8 6 (join 104 4 4 ledger_29_104 ledger_29_108) (join 112 4 2 ledger_29_112 ledger_29_116)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
