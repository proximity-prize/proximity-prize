import ProximityPrize.SubmissionLower.BoundaryTailCheckedR276807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_28_0 : ∀ i ∈ List.range 4, GeometryAt 28 (0+i) := by decide +kernel

theorem geometry_28_4 : ∀ i ∈ List.range 4, GeometryAt 28 (4+i) := by decide +kernel

theorem geometry_28_8 : ∀ i ∈ List.range 4, GeometryAt 28 (8+i) := by decide +kernel

theorem geometry_28_12 : ∀ i ∈ List.range 4, GeometryAt 28 (12+i) := by decide +kernel

theorem geometry_28_16 : ∀ i ∈ List.range 4, GeometryAt 28 (16+i) := by decide +kernel

theorem geometry_28_20 : ∀ i ∈ List.range 4, GeometryAt 28 (20+i) := by decide +kernel

theorem geometry_28_24 : ∀ i ∈ List.range 4, GeometryAt 28 (24+i) := by decide +kernel

theorem geometry_28_28 : ∀ i ∈ List.range 4, GeometryAt 28 (28+i) := by decide +kernel

theorem geometry_28_32 : ∀ i ∈ List.range 4, GeometryAt 28 (32+i) := by decide +kernel

theorem geometry_28_36 : ∀ i ∈ List.range 4, GeometryAt 28 (36+i) := by decide +kernel

theorem geometry_28_40 : ∀ i ∈ List.range 4, GeometryAt 28 (40+i) := by decide +kernel

theorem geometry_28_44 : ∀ i ∈ List.range 4, GeometryAt 28 (44+i) := by decide +kernel

theorem geometry_28_48 : ∀ i ∈ List.range 4, GeometryAt 28 (48+i) := by decide +kernel

theorem geometry_28_52 : ∀ i ∈ List.range 4, GeometryAt 28 (52+i) := by decide +kernel

theorem geometry_28_56 : ∀ i ∈ List.range 4, GeometryAt 28 (56+i) := by decide +kernel

theorem geometry_28_60 : ∀ i ∈ List.range 4, GeometryAt 28 (60+i) := by decide +kernel

theorem geometry_28_64 : ∀ i ∈ List.range 4, GeometryAt 28 (64+i) := by decide +kernel

theorem geometry_28_68 : ∀ i ∈ List.range 4, GeometryAt 28 (68+i) := by decide +kernel

theorem geometry_28_72 : ∀ i ∈ List.range 4, GeometryAt 28 (72+i) := by decide +kernel

theorem geometry_28_76 : ∀ i ∈ List.range 4, GeometryAt 28 (76+i) := by decide +kernel

theorem geometry_28_80 : ∀ i ∈ List.range 4, GeometryAt 28 (80+i) := by decide +kernel

theorem geometry_28_84 : ∀ i ∈ List.range 4, GeometryAt 28 (84+i) := by decide +kernel

theorem geometry_28_88 : ∀ i ∈ List.range 4, GeometryAt 28 (88+i) := by decide +kernel

theorem geometry_28_92 : ∀ i ∈ List.range 4, GeometryAt 28 (92+i) := by decide +kernel

theorem geometry_28_96 : ∀ i ∈ List.range 4, GeometryAt 28 (96+i) := by decide +kernel

theorem geometry_28_100 : ∀ i ∈ List.range 4, GeometryAt 28 (100+i) := by decide +kernel

theorem geometry_28_104 : ∀ i ∈ List.range 4, GeometryAt 28 (104+i) := by decide +kernel

theorem geometry_28_108 : ∀ i ∈ List.range 4, GeometryAt 28 (108+i) := by decide +kernel

theorem geometry_28_112 : ∀ i ∈ List.range 4, GeometryAt 28 (112+i) := by decide +kernel

theorem geometry_28_116 : ∀ i ∈ List.range 3, GeometryAt 28 (116+i) := by decide +kernel

theorem geometry_28 (v : ℕ) (hv : v ∈ List.range 119) : GeometryAt 28 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 28 v)
  have h := (join 0 60 59 (join 0 28 32 (join 0 12 16 (join 0 4 8 geometry_28_0 (join 4 4 4 geometry_28_4 geometry_28_8)) (join 12 8 8 (join 12 4 4 geometry_28_12 geometry_28_16) (join 20 4 4 geometry_28_20 geometry_28_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 geometry_28_28 geometry_28_32) (join 36 4 4 geometry_28_36 geometry_28_40)) (join 44 8 8 (join 44 4 4 geometry_28_44 geometry_28_48) (join 52 4 4 geometry_28_52 geometry_28_56)))) (join 60 28 31 (join 60 12 16 (join 60 4 8 geometry_28_60 (join 64 4 4 geometry_28_64 geometry_28_68)) (join 72 8 8 (join 72 4 4 geometry_28_72 geometry_28_76) (join 80 4 4 geometry_28_80 geometry_28_84))) (join 88 16 15 (join 88 8 8 (join 88 4 4 geometry_28_88 geometry_28_92) (join 96 4 4 geometry_28_96 geometry_28_100)) (join 104 8 7 (join 104 4 4 geometry_28_104 geometry_28_108) (join 112 4 3 geometry_28_112 geometry_28_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_28_0 : ∀ i ∈ List.range 4, StrictAt 28 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (0+i)) 28 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_4 : ∀ i ∈ List.range 4, StrictAt 28 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (4+i)) 28 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_8 : ∀ i ∈ List.range 4, StrictAt 28 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (8+i)) 28 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_12 : ∀ i ∈ List.range 4, StrictAt 28 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (12+i)) 28 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_16 : ∀ i ∈ List.range 4, StrictAt 28 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (16+i)) 28 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_20 : ∀ i ∈ List.range 4, StrictAt 28 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (20+i)) 28 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_24 : ∀ i ∈ List.range 4, StrictAt 28 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (24+i)) 28 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_28 : ∀ i ∈ List.range 4, StrictAt 28 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (28+i)) 28 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_32 : ∀ i ∈ List.range 4, StrictAt 28 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (32+i)) 28 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_36 : ∀ i ∈ List.range 4, StrictAt 28 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (36+i)) 28 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_40 : ∀ i ∈ List.range 4, StrictAt 28 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (40+i)) 28 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_44 : ∀ i ∈ List.range 4, StrictAt 28 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (44+i)) 28 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_48 : ∀ i ∈ List.range 4, StrictAt 28 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (48+i)) 28 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_52 : ∀ i ∈ List.range 4, StrictAt 28 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (52+i)) 28 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_56 : ∀ i ∈ List.range 4, StrictAt 28 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (56+i)) 28 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_60 : ∀ i ∈ List.range 4, StrictAt 28 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (60+i)) 28 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_64 : ∀ i ∈ List.range 4, StrictAt 28 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (64+i)) 28 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_68 : ∀ i ∈ List.range 4, StrictAt 28 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (68+i)) 28 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_72 : ∀ i ∈ List.range 4, StrictAt 28 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (72+i)) 28 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_76 : ∀ i ∈ List.range 4, StrictAt 28 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (76+i)) 28 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_80 : ∀ i ∈ List.range 4, StrictAt 28 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (80+i)) 28 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_84 : ∀ i ∈ List.range 4, StrictAt 28 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (84+i)) 28 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_88 : ∀ i ∈ List.range 4, StrictAt 28 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (88+i)) 28 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_92 : ∀ i ∈ List.range 4, StrictAt 28 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (92+i)) 28 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_96 : ∀ i ∈ List.range 4, StrictAt 28 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (96+i)) 28 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_100 : ∀ i ∈ List.range 4, StrictAt 28 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (100+i)) 28 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_104 : ∀ i ∈ List.range 4, StrictAt 28 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (104+i)) 28 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_108 : ∀ i ∈ List.range 4, StrictAt 28 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (108+i)) 28 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_112 : ∀ i ∈ List.range 4, StrictAt 28 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (112+i)) 28 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28_116 : ∀ i ∈ List.range 3, StrictAt 28 (116+i) := by
  have h : ∀ i ∈ List.range 3, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 28 (116+i)) 28 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_28 (v : ℕ) (hv : v ∈ List.range 119) : StrictAt 28 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 28 v)
  have h := (join 0 60 59 (join 0 28 32 (join 0 12 16 (join 0 4 8 strict_28_0 (join 4 4 4 strict_28_4 strict_28_8)) (join 12 8 8 (join 12 4 4 strict_28_12 strict_28_16) (join 20 4 4 strict_28_20 strict_28_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 strict_28_28 strict_28_32) (join 36 4 4 strict_28_36 strict_28_40)) (join 44 8 8 (join 44 4 4 strict_28_44 strict_28_48) (join 52 4 4 strict_28_52 strict_28_56)))) (join 60 28 31 (join 60 12 16 (join 60 4 8 strict_28_60 (join 64 4 4 strict_28_64 strict_28_68)) (join 72 8 8 (join 72 4 4 strict_28_72 strict_28_76) (join 80 4 4 strict_28_80 strict_28_84))) (join 88 16 15 (join 88 8 8 (join 88 4 4 strict_28_88 strict_28_92) (join 96 4 4 strict_28_96 strict_28_100)) (join 104 8 7 (join 104 4 4 strict_28_104 strict_28_108) (join 112 4 3 strict_28_112 strict_28_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_28_0 : ∀ i ∈ List.range 4, PhaseAt 28 (0+i) := by decide +kernel

theorem phase_28_4 : ∀ i ∈ List.range 4, PhaseAt 28 (4+i) := by decide +kernel

theorem phase_28_8 : ∀ i ∈ List.range 4, PhaseAt 28 (8+i) := by decide +kernel

theorem phase_28_12 : ∀ i ∈ List.range 4, PhaseAt 28 (12+i) := by decide +kernel

theorem phase_28_16 : ∀ i ∈ List.range 4, PhaseAt 28 (16+i) := by decide +kernel

theorem phase_28_20 : ∀ i ∈ List.range 4, PhaseAt 28 (20+i) := by decide +kernel

theorem phase_28_24 : ∀ i ∈ List.range 4, PhaseAt 28 (24+i) := by decide +kernel

theorem phase_28_28 : ∀ i ∈ List.range 4, PhaseAt 28 (28+i) := by decide +kernel

theorem phase_28_32 : ∀ i ∈ List.range 4, PhaseAt 28 (32+i) := by decide +kernel

theorem phase_28_36 : ∀ i ∈ List.range 4, PhaseAt 28 (36+i) := by decide +kernel

theorem phase_28_40 : ∀ i ∈ List.range 4, PhaseAt 28 (40+i) := by decide +kernel

theorem phase_28_44 : ∀ i ∈ List.range 4, PhaseAt 28 (44+i) := by decide +kernel

theorem phase_28_48 : ∀ i ∈ List.range 4, PhaseAt 28 (48+i) := by decide +kernel

theorem phase_28_52 : ∀ i ∈ List.range 4, PhaseAt 28 (52+i) := by decide +kernel

theorem phase_28_56 : ∀ i ∈ List.range 4, PhaseAt 28 (56+i) := by decide +kernel

theorem phase_28_60 : ∀ i ∈ List.range 4, PhaseAt 28 (60+i) := by decide +kernel

theorem phase_28_64 : ∀ i ∈ List.range 4, PhaseAt 28 (64+i) := by decide +kernel

theorem phase_28_68 : ∀ i ∈ List.range 4, PhaseAt 28 (68+i) := by decide +kernel

theorem phase_28_72 : ∀ i ∈ List.range 4, PhaseAt 28 (72+i) := by decide +kernel

theorem phase_28_76 : ∀ i ∈ List.range 4, PhaseAt 28 (76+i) := by decide +kernel

theorem phase_28_80 : ∀ i ∈ List.range 4, PhaseAt 28 (80+i) := by decide +kernel

theorem phase_28_84 : ∀ i ∈ List.range 4, PhaseAt 28 (84+i) := by decide +kernel

theorem phase_28_88 : ∀ i ∈ List.range 4, PhaseAt 28 (88+i) := by decide +kernel

theorem phase_28_92 : ∀ i ∈ List.range 4, PhaseAt 28 (92+i) := by decide +kernel

theorem phase_28_96 : ∀ i ∈ List.range 4, PhaseAt 28 (96+i) := by decide +kernel

theorem phase_28_100 : ∀ i ∈ List.range 4, PhaseAt 28 (100+i) := by decide +kernel

theorem phase_28_104 : ∀ i ∈ List.range 4, PhaseAt 28 (104+i) := by decide +kernel

theorem phase_28_108 : ∀ i ∈ List.range 4, PhaseAt 28 (108+i) := by decide +kernel

theorem phase_28_112 : ∀ i ∈ List.range 4, PhaseAt 28 (112+i) := by decide +kernel

theorem phase_28_116 : ∀ i ∈ List.range 3, PhaseAt 28 (116+i) := by decide +kernel

theorem phase_28 (v : ℕ) (hv : v ∈ List.range 119) : PhaseAt 28 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 28 v)
  have h := (join 0 60 59 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_28_0 (join 4 4 4 phase_28_4 phase_28_8)) (join 12 8 8 (join 12 4 4 phase_28_12 phase_28_16) (join 20 4 4 phase_28_20 phase_28_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_28_28 phase_28_32) (join 36 4 4 phase_28_36 phase_28_40)) (join 44 8 8 (join 44 4 4 phase_28_44 phase_28_48) (join 52 4 4 phase_28_52 phase_28_56)))) (join 60 28 31 (join 60 12 16 (join 60 4 8 phase_28_60 (join 64 4 4 phase_28_64 phase_28_68)) (join 72 8 8 (join 72 4 4 phase_28_72 phase_28_76) (join 80 4 4 phase_28_80 phase_28_84))) (join 88 16 15 (join 88 8 8 (join 88 4 4 phase_28_88 phase_28_92) (join 96 4 4 phase_28_96 phase_28_100)) (join 104 8 7 (join 104 4 4 phase_28_104 phase_28_108) (join 112 4 3 phase_28_112 phase_28_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_28_0 : ∀ i ∈ List.range 1, ThresholdAt 28 (0+i) := by decide +kernel

theorem threshold_28_1 : ∀ i ∈ List.range 1, ThresholdAt 28 (1+i) := by decide +kernel

theorem threshold_28_2 : ∀ i ∈ List.range 1, ThresholdAt 28 (2+i) := by decide +kernel

theorem threshold_28_3 : ∀ i ∈ List.range 1, ThresholdAt 28 (3+i) := by decide +kernel

theorem threshold_28_4 : ∀ i ∈ List.range 1, ThresholdAt 28 (4+i) := by decide +kernel

theorem threshold_28_5 : ∀ i ∈ List.range 1, ThresholdAt 28 (5+i) := by decide +kernel

theorem threshold_28_6 : ∀ i ∈ List.range 1, ThresholdAt 28 (6+i) := by decide +kernel

theorem threshold_28_7 : ∀ i ∈ List.range 1, ThresholdAt 28 (7+i) := by decide +kernel

theorem threshold_28_8 : ∀ i ∈ List.range 1, ThresholdAt 28 (8+i) := by decide +kernel

theorem threshold_28_9 : ∀ i ∈ List.range 1, ThresholdAt 28 (9+i) := by decide +kernel

theorem threshold_28_10 : ∀ i ∈ List.range 1, ThresholdAt 28 (10+i) := by decide +kernel

theorem threshold_28_11 : ∀ i ∈ List.range 1, ThresholdAt 28 (11+i) := by decide +kernel

theorem threshold_28_12 : ∀ i ∈ List.range 1, ThresholdAt 28 (12+i) := by decide +kernel

theorem threshold_28_13 : ∀ i ∈ List.range 1, ThresholdAt 28 (13+i) := by decide +kernel

theorem threshold_28_14 : ∀ i ∈ List.range 1, ThresholdAt 28 (14+i) := by decide +kernel

theorem threshold_28_15 : ∀ i ∈ List.range 1, ThresholdAt 28 (15+i) := by decide +kernel

theorem threshold_28_16 : ∀ i ∈ List.range 1, ThresholdAt 28 (16+i) := by decide +kernel

theorem threshold_28_17 : ∀ i ∈ List.range 1, ThresholdAt 28 (17+i) := by decide +kernel

theorem threshold_28_18 : ∀ i ∈ List.range 1, ThresholdAt 28 (18+i) := by decide +kernel

theorem threshold_28_19 : ∀ i ∈ List.range 1, ThresholdAt 28 (19+i) := by decide +kernel

theorem threshold_28_20 : ∀ i ∈ List.range 1, ThresholdAt 28 (20+i) := by decide +kernel

theorem threshold_28_21 : ∀ i ∈ List.range 1, ThresholdAt 28 (21+i) := by decide +kernel

theorem threshold_28_22 : ∀ i ∈ List.range 1, ThresholdAt 28 (22+i) := by decide +kernel

theorem threshold_28_23 : ∀ i ∈ List.range 1, ThresholdAt 28 (23+i) := by decide +kernel

theorem threshold_28_24 : ∀ i ∈ List.range 1, ThresholdAt 28 (24+i) := by decide +kernel

theorem threshold_28_25 : ∀ i ∈ List.range 1, ThresholdAt 28 (25+i) := by decide +kernel

theorem threshold_28_26 : ∀ i ∈ List.range 1, ThresholdAt 28 (26+i) := by decide +kernel

theorem threshold_28_27 : ∀ i ∈ List.range 1, ThresholdAt 28 (27+i) := by decide +kernel

theorem threshold_28_28 : ∀ i ∈ List.range 1, ThresholdAt 28 (28+i) := by decide +kernel

theorem threshold_28_29 : ∀ i ∈ List.range 1, ThresholdAt 28 (29+i) := by decide +kernel

theorem threshold_28_30 : ∀ i ∈ List.range 1, ThresholdAt 28 (30+i) := by decide +kernel

theorem threshold_28_31 : ∀ i ∈ List.range 1, ThresholdAt 28 (31+i) := by decide +kernel

theorem threshold_28_32 : ∀ i ∈ List.range 1, ThresholdAt 28 (32+i) := by decide +kernel

theorem threshold_28_33 : ∀ i ∈ List.range 1, ThresholdAt 28 (33+i) := by decide +kernel

theorem threshold_28_34 : ∀ i ∈ List.range 1, ThresholdAt 28 (34+i) := by decide +kernel

theorem threshold_28_35 : ∀ i ∈ List.range 1, ThresholdAt 28 (35+i) := by decide +kernel

theorem threshold_28_36 : ∀ i ∈ List.range 1, ThresholdAt 28 (36+i) := by decide +kernel

theorem threshold_28_37 : ∀ i ∈ List.range 1, ThresholdAt 28 (37+i) := by decide +kernel

theorem threshold_28_38 : ∀ i ∈ List.range 1, ThresholdAt 28 (38+i) := by decide +kernel

theorem threshold_28_39 : ∀ i ∈ List.range 1, ThresholdAt 28 (39+i) := by decide +kernel

theorem threshold_28_40 : ∀ i ∈ List.range 1, ThresholdAt 28 (40+i) := by decide +kernel

theorem threshold_28_41 : ∀ i ∈ List.range 1, ThresholdAt 28 (41+i) := by decide +kernel

theorem threshold_28_42 : ∀ i ∈ List.range 1, ThresholdAt 28 (42+i) := by decide +kernel

theorem threshold_28_43 : ∀ i ∈ List.range 1, ThresholdAt 28 (43+i) := by decide +kernel

theorem threshold_28_44 : ∀ i ∈ List.range 1, ThresholdAt 28 (44+i) := by decide +kernel

theorem threshold_28_45 : ∀ i ∈ List.range 1, ThresholdAt 28 (45+i) := by decide +kernel

theorem threshold_28_46 : ∀ i ∈ List.range 1, ThresholdAt 28 (46+i) := by decide +kernel

theorem threshold_28_47 : ∀ i ∈ List.range 1, ThresholdAt 28 (47+i) := by decide +kernel

theorem threshold_28_48 : ∀ i ∈ List.range 1, ThresholdAt 28 (48+i) := by decide +kernel

theorem threshold_28_49 : ∀ i ∈ List.range 1, ThresholdAt 28 (49+i) := by decide +kernel

theorem threshold_28_50 : ∀ i ∈ List.range 1, ThresholdAt 28 (50+i) := by decide +kernel

theorem threshold_28_51 : ∀ i ∈ List.range 1, ThresholdAt 28 (51+i) := by decide +kernel

theorem threshold_28_52 : ∀ i ∈ List.range 1, ThresholdAt 28 (52+i) := by decide +kernel

theorem threshold_28_53 : ∀ i ∈ List.range 1, ThresholdAt 28 (53+i) := by decide +kernel

theorem threshold_28_54 : ∀ i ∈ List.range 1, ThresholdAt 28 (54+i) := by decide +kernel

theorem threshold_28_55 : ∀ i ∈ List.range 1, ThresholdAt 28 (55+i) := by decide +kernel

theorem threshold_28_56 : ∀ i ∈ List.range 1, ThresholdAt 28 (56+i) := by decide +kernel

theorem threshold_28_57 : ∀ i ∈ List.range 1, ThresholdAt 28 (57+i) := by decide +kernel

theorem threshold_28_58 : ∀ i ∈ List.range 1, ThresholdAt 28 (58+i) := by decide +kernel

theorem threshold_28_59 : ∀ i ∈ List.range 1, ThresholdAt 28 (59+i) := by decide +kernel

theorem threshold_28_60 : ∀ i ∈ List.range 1, ThresholdAt 28 (60+i) := by decide +kernel

theorem threshold_28_61 : ∀ i ∈ List.range 1, ThresholdAt 28 (61+i) := by decide +kernel

theorem threshold_28_62 : ∀ i ∈ List.range 1, ThresholdAt 28 (62+i) := by decide +kernel

theorem threshold_28_63 : ∀ i ∈ List.range 1, ThresholdAt 28 (63+i) := by decide +kernel

theorem threshold_28_64 : ∀ i ∈ List.range 1, ThresholdAt 28 (64+i) := by decide +kernel

theorem threshold_28_65 : ∀ i ∈ List.range 1, ThresholdAt 28 (65+i) := by decide +kernel

theorem threshold_28_66 : ∀ i ∈ List.range 1, ThresholdAt 28 (66+i) := by decide +kernel

theorem threshold_28_67 : ∀ i ∈ List.range 1, ThresholdAt 28 (67+i) := by decide +kernel

theorem threshold_28_68 : ∀ i ∈ List.range 1, ThresholdAt 28 (68+i) := by decide +kernel

theorem threshold_28_69 : ∀ i ∈ List.range 1, ThresholdAt 28 (69+i) := by decide +kernel

theorem threshold_28_70 : ∀ i ∈ List.range 1, ThresholdAt 28 (70+i) := by decide +kernel

theorem threshold_28_71 : ∀ i ∈ List.range 1, ThresholdAt 28 (71+i) := by decide +kernel

theorem threshold_28_72 : ∀ i ∈ List.range 1, ThresholdAt 28 (72+i) := by decide +kernel

theorem threshold_28_73 : ∀ i ∈ List.range 1, ThresholdAt 28 (73+i) := by decide +kernel

theorem threshold_28_74 : ∀ i ∈ List.range 1, ThresholdAt 28 (74+i) := by decide +kernel

theorem threshold_28_75 : ∀ i ∈ List.range 1, ThresholdAt 28 (75+i) := by decide +kernel

theorem threshold_28_76 : ∀ i ∈ List.range 1, ThresholdAt 28 (76+i) := by decide +kernel

theorem threshold_28_77 : ∀ i ∈ List.range 1, ThresholdAt 28 (77+i) := by decide +kernel

theorem threshold_28_78 : ∀ i ∈ List.range 1, ThresholdAt 28 (78+i) := by decide +kernel

theorem threshold_28_79 : ∀ i ∈ List.range 1, ThresholdAt 28 (79+i) := by decide +kernel

theorem threshold_28_80 : ∀ i ∈ List.range 1, ThresholdAt 28 (80+i) := by decide +kernel

theorem threshold_28_81 : ∀ i ∈ List.range 1, ThresholdAt 28 (81+i) := by decide +kernel

theorem threshold_28_82 : ∀ i ∈ List.range 1, ThresholdAt 28 (82+i) := by decide +kernel

theorem threshold_28_83 : ∀ i ∈ List.range 1, ThresholdAt 28 (83+i) := by decide +kernel

theorem threshold_28_84 : ∀ i ∈ List.range 1, ThresholdAt 28 (84+i) := by decide +kernel

theorem threshold_28_85 : ∀ i ∈ List.range 1, ThresholdAt 28 (85+i) := by decide +kernel

theorem threshold_28_86 : ∀ i ∈ List.range 1, ThresholdAt 28 (86+i) := by decide +kernel

theorem threshold_28_87 : ∀ i ∈ List.range 1, ThresholdAt 28 (87+i) := by decide +kernel

theorem threshold_28_88 : ∀ i ∈ List.range 1, ThresholdAt 28 (88+i) := by decide +kernel

theorem threshold_28_89 : ∀ i ∈ List.range 1, ThresholdAt 28 (89+i) := by decide +kernel

theorem threshold_28_90 : ∀ i ∈ List.range 1, ThresholdAt 28 (90+i) := by decide +kernel

theorem threshold_28_91 : ∀ i ∈ List.range 1, ThresholdAt 28 (91+i) := by decide +kernel

theorem threshold_28_92 : ∀ i ∈ List.range 1, ThresholdAt 28 (92+i) := by decide +kernel

theorem threshold_28_93 : ∀ i ∈ List.range 1, ThresholdAt 28 (93+i) := by decide +kernel

theorem threshold_28_94 : ∀ i ∈ List.range 1, ThresholdAt 28 (94+i) := by decide +kernel

theorem threshold_28_95 : ∀ i ∈ List.range 1, ThresholdAt 28 (95+i) := by decide +kernel

theorem threshold_28_96 : ∀ i ∈ List.range 1, ThresholdAt 28 (96+i) := by decide +kernel

theorem threshold_28_97 : ∀ i ∈ List.range 1, ThresholdAt 28 (97+i) := by decide +kernel

theorem threshold_28_98 : ∀ i ∈ List.range 1, ThresholdAt 28 (98+i) := by decide +kernel

theorem threshold_28_99 : ∀ i ∈ List.range 1, ThresholdAt 28 (99+i) := by decide +kernel

theorem threshold_28_100 : ∀ i ∈ List.range 1, ThresholdAt 28 (100+i) := by decide +kernel

theorem threshold_28_101 : ∀ i ∈ List.range 1, ThresholdAt 28 (101+i) := by decide +kernel

theorem threshold_28_102 : ∀ i ∈ List.range 1, ThresholdAt 28 (102+i) := by decide +kernel

theorem threshold_28_103 : ∀ i ∈ List.range 1, ThresholdAt 28 (103+i) := by decide +kernel

theorem threshold_28_104 : ∀ i ∈ List.range 1, ThresholdAt 28 (104+i) := by decide +kernel

theorem threshold_28_105 : ∀ i ∈ List.range 1, ThresholdAt 28 (105+i) := by decide +kernel

theorem threshold_28_106 : ∀ i ∈ List.range 1, ThresholdAt 28 (106+i) := by decide +kernel

theorem threshold_28_107 : ∀ i ∈ List.range 1, ThresholdAt 28 (107+i) := by decide +kernel

theorem threshold_28_108 : ∀ i ∈ List.range 1, ThresholdAt 28 (108+i) := by decide +kernel

theorem threshold_28_109 : ∀ i ∈ List.range 1, ThresholdAt 28 (109+i) := by decide +kernel

theorem threshold_28_110 : ∀ i ∈ List.range 1, ThresholdAt 28 (110+i) := by decide +kernel

theorem threshold_28_111 : ∀ i ∈ List.range 1, ThresholdAt 28 (111+i) := by decide +kernel

theorem threshold_28_112 : ∀ i ∈ List.range 1, ThresholdAt 28 (112+i) := by decide +kernel

theorem threshold_28_113 : ∀ i ∈ List.range 1, ThresholdAt 28 (113+i) := by decide +kernel

theorem threshold_28_114 : ∀ i ∈ List.range 1, ThresholdAt 28 (114+i) := by decide +kernel

theorem threshold_28_115 : ∀ i ∈ List.range 1, ThresholdAt 28 (115+i) := by decide +kernel

theorem threshold_28_116 : ∀ i ∈ List.range 1, ThresholdAt 28 (116+i) := by decide +kernel

theorem threshold_28_117 : ∀ i ∈ List.range 1, ThresholdAt 28 (117+i) := by decide +kernel

theorem threshold_28_118 : ∀ i ∈ List.range 1, ThresholdAt 28 (118+i) := by decide +kernel

theorem threshold_28 (v : ℕ) (hv : v ∈ List.range 119) : ThresholdAt 28 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 28 v)
  have h := (join 0 59 60 (join 0 29 30 (join 0 14 15 (join 0 7 7 (join 0 3 4 (join 0 1 2 threshold_28_0 (join 1 1 1 threshold_28_1 threshold_28_2)) (join 3 2 2 (join 3 1 1 threshold_28_3 threshold_28_4) (join 5 1 1 threshold_28_5 threshold_28_6))) (join 7 3 4 (join 7 1 2 threshold_28_7 (join 8 1 1 threshold_28_8 threshold_28_9)) (join 10 2 2 (join 10 1 1 threshold_28_10 threshold_28_11) (join 12 1 1 threshold_28_12 threshold_28_13)))) (join 14 7 8 (join 14 3 4 (join 14 1 2 threshold_28_14 (join 15 1 1 threshold_28_15 threshold_28_16)) (join 17 2 2 (join 17 1 1 threshold_28_17 threshold_28_18) (join 19 1 1 threshold_28_19 threshold_28_20))) (join 21 4 4 (join 21 2 2 (join 21 1 1 threshold_28_21 threshold_28_22) (join 23 1 1 threshold_28_23 threshold_28_24)) (join 25 2 2 (join 25 1 1 threshold_28_25 threshold_28_26) (join 27 1 1 threshold_28_27 threshold_28_28))))) (join 29 15 15 (join 29 7 8 (join 29 3 4 (join 29 1 2 threshold_28_29 (join 30 1 1 threshold_28_30 threshold_28_31)) (join 32 2 2 (join 32 1 1 threshold_28_32 threshold_28_33) (join 34 1 1 threshold_28_34 threshold_28_35))) (join 36 4 4 (join 36 2 2 (join 36 1 1 threshold_28_36 threshold_28_37) (join 38 1 1 threshold_28_38 threshold_28_39)) (join 40 2 2 (join 40 1 1 threshold_28_40 threshold_28_41) (join 42 1 1 threshold_28_42 threshold_28_43)))) (join 44 7 8 (join 44 3 4 (join 44 1 2 threshold_28_44 (join 45 1 1 threshold_28_45 threshold_28_46)) (join 47 2 2 (join 47 1 1 threshold_28_47 threshold_28_48) (join 49 1 1 threshold_28_49 threshold_28_50))) (join 51 4 4 (join 51 2 2 (join 51 1 1 threshold_28_51 threshold_28_52) (join 53 1 1 threshold_28_53 threshold_28_54)) (join 55 2 2 (join 55 1 1 threshold_28_55 threshold_28_56) (join 57 1 1 threshold_28_57 threshold_28_58)))))) (join 59 30 30 (join 59 15 15 (join 59 7 8 (join 59 3 4 (join 59 1 2 threshold_28_59 (join 60 1 1 threshold_28_60 threshold_28_61)) (join 62 2 2 (join 62 1 1 threshold_28_62 threshold_28_63) (join 64 1 1 threshold_28_64 threshold_28_65))) (join 66 4 4 (join 66 2 2 (join 66 1 1 threshold_28_66 threshold_28_67) (join 68 1 1 threshold_28_68 threshold_28_69)) (join 70 2 2 (join 70 1 1 threshold_28_70 threshold_28_71) (join 72 1 1 threshold_28_72 threshold_28_73)))) (join 74 7 8 (join 74 3 4 (join 74 1 2 threshold_28_74 (join 75 1 1 threshold_28_75 threshold_28_76)) (join 77 2 2 (join 77 1 1 threshold_28_77 threshold_28_78) (join 79 1 1 threshold_28_79 threshold_28_80))) (join 81 4 4 (join 81 2 2 (join 81 1 1 threshold_28_81 threshold_28_82) (join 83 1 1 threshold_28_83 threshold_28_84)) (join 85 2 2 (join 85 1 1 threshold_28_85 threshold_28_86) (join 87 1 1 threshold_28_87 threshold_28_88))))) (join 89 15 15 (join 89 7 8 (join 89 3 4 (join 89 1 2 threshold_28_89 (join 90 1 1 threshold_28_90 threshold_28_91)) (join 92 2 2 (join 92 1 1 threshold_28_92 threshold_28_93) (join 94 1 1 threshold_28_94 threshold_28_95))) (join 96 4 4 (join 96 2 2 (join 96 1 1 threshold_28_96 threshold_28_97) (join 98 1 1 threshold_28_98 threshold_28_99)) (join 100 2 2 (join 100 1 1 threshold_28_100 threshold_28_101) (join 102 1 1 threshold_28_102 threshold_28_103)))) (join 104 7 8 (join 104 3 4 (join 104 1 2 threshold_28_104 (join 105 1 1 threshold_28_105 threshold_28_106)) (join 107 2 2 (join 107 1 1 threshold_28_107 threshold_28_108) (join 109 1 1 threshold_28_109 threshold_28_110))) (join 111 4 4 (join 111 2 2 (join 111 1 1 threshold_28_111 threshold_28_112) (join 113 1 1 threshold_28_113 threshold_28_114)) (join 115 2 2 (join 115 1 1 threshold_28_115 threshold_28_116) (join 117 1 1 threshold_28_117 threshold_28_118)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_28_0 : ∀ i ∈ List.range 4, LedgerAt 28 (0+i) := by decide +kernel

theorem ledger_28_4 : ∀ i ∈ List.range 4, LedgerAt 28 (4+i) := by decide +kernel

theorem ledger_28_8 : ∀ i ∈ List.range 4, LedgerAt 28 (8+i) := by decide +kernel

theorem ledger_28_12 : ∀ i ∈ List.range 4, LedgerAt 28 (12+i) := by decide +kernel

theorem ledger_28_16 : ∀ i ∈ List.range 4, LedgerAt 28 (16+i) := by decide +kernel

theorem ledger_28_20 : ∀ i ∈ List.range 4, LedgerAt 28 (20+i) := by decide +kernel

theorem ledger_28_24 : ∀ i ∈ List.range 4, LedgerAt 28 (24+i) := by decide +kernel

theorem ledger_28_28 : ∀ i ∈ List.range 4, LedgerAt 28 (28+i) := by decide +kernel

theorem ledger_28_32 : ∀ i ∈ List.range 4, LedgerAt 28 (32+i) := by decide +kernel

theorem ledger_28_36 : ∀ i ∈ List.range 4, LedgerAt 28 (36+i) := by decide +kernel

theorem ledger_28_40 : ∀ i ∈ List.range 4, LedgerAt 28 (40+i) := by decide +kernel

theorem ledger_28_44 : ∀ i ∈ List.range 4, LedgerAt 28 (44+i) := by decide +kernel

theorem ledger_28_48 : ∀ i ∈ List.range 4, LedgerAt 28 (48+i) := by decide +kernel

theorem ledger_28_52 : ∀ i ∈ List.range 4, LedgerAt 28 (52+i) := by decide +kernel

theorem ledger_28_56 : ∀ i ∈ List.range 4, LedgerAt 28 (56+i) := by decide +kernel

theorem ledger_28_60 : ∀ i ∈ List.range 4, LedgerAt 28 (60+i) := by decide +kernel

theorem ledger_28_64 : ∀ i ∈ List.range 4, LedgerAt 28 (64+i) := by decide +kernel

theorem ledger_28_68 : ∀ i ∈ List.range 4, LedgerAt 28 (68+i) := by decide +kernel

theorem ledger_28_72 : ∀ i ∈ List.range 4, LedgerAt 28 (72+i) := by decide +kernel

theorem ledger_28_76 : ∀ i ∈ List.range 4, LedgerAt 28 (76+i) := by decide +kernel

theorem ledger_28_80 : ∀ i ∈ List.range 4, LedgerAt 28 (80+i) := by decide +kernel

theorem ledger_28_84 : ∀ i ∈ List.range 4, LedgerAt 28 (84+i) := by decide +kernel

theorem ledger_28_88 : ∀ i ∈ List.range 4, LedgerAt 28 (88+i) := by decide +kernel

theorem ledger_28_92 : ∀ i ∈ List.range 4, LedgerAt 28 (92+i) := by decide +kernel

theorem ledger_28_96 : ∀ i ∈ List.range 4, LedgerAt 28 (96+i) := by decide +kernel

theorem ledger_28_100 : ∀ i ∈ List.range 4, LedgerAt 28 (100+i) := by decide +kernel

theorem ledger_28_104 : ∀ i ∈ List.range 4, LedgerAt 28 (104+i) := by decide +kernel

theorem ledger_28_108 : ∀ i ∈ List.range 4, LedgerAt 28 (108+i) := by decide +kernel

theorem ledger_28_112 : ∀ i ∈ List.range 4, LedgerAt 28 (112+i) := by decide +kernel

theorem ledger_28_116 : ∀ i ∈ List.range 3, LedgerAt 28 (116+i) := by decide +kernel

theorem ledger_28 (v : ℕ) (hv : v ∈ List.range 119) : LedgerAt 28 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 28 v)
  have h := (join 0 60 59 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_28_0 (join 4 4 4 ledger_28_4 ledger_28_8)) (join 12 8 8 (join 12 4 4 ledger_28_12 ledger_28_16) (join 20 4 4 ledger_28_20 ledger_28_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_28_28 ledger_28_32) (join 36 4 4 ledger_28_36 ledger_28_40)) (join 44 8 8 (join 44 4 4 ledger_28_44 ledger_28_48) (join 52 4 4 ledger_28_52 ledger_28_56)))) (join 60 28 31 (join 60 12 16 (join 60 4 8 ledger_28_60 (join 64 4 4 ledger_28_64 ledger_28_68)) (join 72 8 8 (join 72 4 4 ledger_28_72 ledger_28_76) (join 80 4 4 ledger_28_80 ledger_28_84))) (join 88 16 15 (join 88 8 8 (join 88 4 4 ledger_28_88 ledger_28_92) (join 96 4 4 ledger_28_96 ledger_28_100)) (join 104 8 7 (join 104 4 4 ledger_28_104 ledger_28_108) (join 112 4 3 ledger_28_112 ledger_28_116)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
