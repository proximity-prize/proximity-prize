import ProximityPrize.SubmissionLower.BoundaryTailCheckedR266807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_27_0 : ∀ i ∈ List.range 4, GeometryAt 27 (0+i) := by decide +kernel

theorem geometry_27_4 : ∀ i ∈ List.range 4, GeometryAt 27 (4+i) := by decide +kernel

theorem geometry_27_8 : ∀ i ∈ List.range 4, GeometryAt 27 (8+i) := by decide +kernel

theorem geometry_27_12 : ∀ i ∈ List.range 4, GeometryAt 27 (12+i) := by decide +kernel

theorem geometry_27_16 : ∀ i ∈ List.range 4, GeometryAt 27 (16+i) := by decide +kernel

theorem geometry_27_20 : ∀ i ∈ List.range 4, GeometryAt 27 (20+i) := by decide +kernel

theorem geometry_27_24 : ∀ i ∈ List.range 4, GeometryAt 27 (24+i) := by decide +kernel

theorem geometry_27_28 : ∀ i ∈ List.range 4, GeometryAt 27 (28+i) := by decide +kernel

theorem geometry_27_32 : ∀ i ∈ List.range 4, GeometryAt 27 (32+i) := by decide +kernel

theorem geometry_27_36 : ∀ i ∈ List.range 4, GeometryAt 27 (36+i) := by decide +kernel

theorem geometry_27_40 : ∀ i ∈ List.range 4, GeometryAt 27 (40+i) := by decide +kernel

theorem geometry_27_44 : ∀ i ∈ List.range 4, GeometryAt 27 (44+i) := by decide +kernel

theorem geometry_27_48 : ∀ i ∈ List.range 4, GeometryAt 27 (48+i) := by decide +kernel

theorem geometry_27_52 : ∀ i ∈ List.range 4, GeometryAt 27 (52+i) := by decide +kernel

theorem geometry_27_56 : ∀ i ∈ List.range 4, GeometryAt 27 (56+i) := by decide +kernel

theorem geometry_27_60 : ∀ i ∈ List.range 4, GeometryAt 27 (60+i) := by decide +kernel

theorem geometry_27_64 : ∀ i ∈ List.range 4, GeometryAt 27 (64+i) := by decide +kernel

theorem geometry_27_68 : ∀ i ∈ List.range 4, GeometryAt 27 (68+i) := by decide +kernel

theorem geometry_27_72 : ∀ i ∈ List.range 4, GeometryAt 27 (72+i) := by decide +kernel

theorem geometry_27_76 : ∀ i ∈ List.range 4, GeometryAt 27 (76+i) := by decide +kernel

theorem geometry_27_80 : ∀ i ∈ List.range 4, GeometryAt 27 (80+i) := by decide +kernel

theorem geometry_27_84 : ∀ i ∈ List.range 4, GeometryAt 27 (84+i) := by decide +kernel

theorem geometry_27_88 : ∀ i ∈ List.range 4, GeometryAt 27 (88+i) := by decide +kernel

theorem geometry_27_92 : ∀ i ∈ List.range 4, GeometryAt 27 (92+i) := by decide +kernel

theorem geometry_27_96 : ∀ i ∈ List.range 4, GeometryAt 27 (96+i) := by decide +kernel

theorem geometry_27_100 : ∀ i ∈ List.range 4, GeometryAt 27 (100+i) := by decide +kernel

theorem geometry_27_104 : ∀ i ∈ List.range 4, GeometryAt 27 (104+i) := by decide +kernel

theorem geometry_27_108 : ∀ i ∈ List.range 4, GeometryAt 27 (108+i) := by decide +kernel

theorem geometry_27_112 : ∀ i ∈ List.range 4, GeometryAt 27 (112+i) := by decide +kernel

theorem geometry_27_116 : ∀ i ∈ List.range 4, GeometryAt 27 (116+i) := by decide +kernel

theorem geometry_27 (v : ℕ) (hv : v ∈ List.range 120) : GeometryAt 27 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 27 v)
  have h := (join 0 60 60 (join 0 28 32 (join 0 12 16 (join 0 4 8 geometry_27_0 (join 4 4 4 geometry_27_4 geometry_27_8)) (join 12 8 8 (join 12 4 4 geometry_27_12 geometry_27_16) (join 20 4 4 geometry_27_20 geometry_27_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 geometry_27_28 geometry_27_32) (join 36 4 4 geometry_27_36 geometry_27_40)) (join 44 8 8 (join 44 4 4 geometry_27_44 geometry_27_48) (join 52 4 4 geometry_27_52 geometry_27_56)))) (join 60 28 32 (join 60 12 16 (join 60 4 8 geometry_27_60 (join 64 4 4 geometry_27_64 geometry_27_68)) (join 72 8 8 (join 72 4 4 geometry_27_72 geometry_27_76) (join 80 4 4 geometry_27_80 geometry_27_84))) (join 88 16 16 (join 88 8 8 (join 88 4 4 geometry_27_88 geometry_27_92) (join 96 4 4 geometry_27_96 geometry_27_100)) (join 104 8 8 (join 104 4 4 geometry_27_104 geometry_27_108) (join 112 4 4 geometry_27_112 geometry_27_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_27_0 : ∀ i ∈ List.range 4, StrictAt 27 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (0+i)) 27 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_4 : ∀ i ∈ List.range 4, StrictAt 27 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (4+i)) 27 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_8 : ∀ i ∈ List.range 4, StrictAt 27 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (8+i)) 27 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_12 : ∀ i ∈ List.range 4, StrictAt 27 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (12+i)) 27 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_16 : ∀ i ∈ List.range 4, StrictAt 27 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (16+i)) 27 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_20 : ∀ i ∈ List.range 4, StrictAt 27 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (20+i)) 27 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_24 : ∀ i ∈ List.range 4, StrictAt 27 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (24+i)) 27 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_28 : ∀ i ∈ List.range 4, StrictAt 27 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (28+i)) 27 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_32 : ∀ i ∈ List.range 4, StrictAt 27 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (32+i)) 27 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_36 : ∀ i ∈ List.range 4, StrictAt 27 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (36+i)) 27 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_40 : ∀ i ∈ List.range 4, StrictAt 27 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (40+i)) 27 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_44 : ∀ i ∈ List.range 4, StrictAt 27 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (44+i)) 27 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_48 : ∀ i ∈ List.range 4, StrictAt 27 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (48+i)) 27 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_52 : ∀ i ∈ List.range 4, StrictAt 27 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (52+i)) 27 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_56 : ∀ i ∈ List.range 4, StrictAt 27 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (56+i)) 27 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_60 : ∀ i ∈ List.range 4, StrictAt 27 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (60+i)) 27 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_64 : ∀ i ∈ List.range 4, StrictAt 27 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (64+i)) 27 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_68 : ∀ i ∈ List.range 4, StrictAt 27 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (68+i)) 27 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_72 : ∀ i ∈ List.range 4, StrictAt 27 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (72+i)) 27 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_76 : ∀ i ∈ List.range 4, StrictAt 27 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (76+i)) 27 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_80 : ∀ i ∈ List.range 4, StrictAt 27 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (80+i)) 27 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_84 : ∀ i ∈ List.range 4, StrictAt 27 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (84+i)) 27 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_88 : ∀ i ∈ List.range 4, StrictAt 27 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (88+i)) 27 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_92 : ∀ i ∈ List.range 4, StrictAt 27 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (92+i)) 27 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_96 : ∀ i ∈ List.range 4, StrictAt 27 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (96+i)) 27 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_100 : ∀ i ∈ List.range 4, StrictAt 27 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (100+i)) 27 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_104 : ∀ i ∈ List.range 4, StrictAt 27 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (104+i)) 27 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_108 : ∀ i ∈ List.range 4, StrictAt 27 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (108+i)) 27 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_112 : ∀ i ∈ List.range 4, StrictAt 27 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (112+i)) 27 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27_116 : ∀ i ∈ List.range 4, StrictAt 27 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 27 (116+i)) 27 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_27 (v : ℕ) (hv : v ∈ List.range 120) : StrictAt 27 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 27 v)
  have h := (join 0 60 60 (join 0 28 32 (join 0 12 16 (join 0 4 8 strict_27_0 (join 4 4 4 strict_27_4 strict_27_8)) (join 12 8 8 (join 12 4 4 strict_27_12 strict_27_16) (join 20 4 4 strict_27_20 strict_27_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 strict_27_28 strict_27_32) (join 36 4 4 strict_27_36 strict_27_40)) (join 44 8 8 (join 44 4 4 strict_27_44 strict_27_48) (join 52 4 4 strict_27_52 strict_27_56)))) (join 60 28 32 (join 60 12 16 (join 60 4 8 strict_27_60 (join 64 4 4 strict_27_64 strict_27_68)) (join 72 8 8 (join 72 4 4 strict_27_72 strict_27_76) (join 80 4 4 strict_27_80 strict_27_84))) (join 88 16 16 (join 88 8 8 (join 88 4 4 strict_27_88 strict_27_92) (join 96 4 4 strict_27_96 strict_27_100)) (join 104 8 8 (join 104 4 4 strict_27_104 strict_27_108) (join 112 4 4 strict_27_112 strict_27_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_27_0 : ∀ i ∈ List.range 4, PhaseAt 27 (0+i) := by decide +kernel

theorem phase_27_4 : ∀ i ∈ List.range 4, PhaseAt 27 (4+i) := by decide +kernel

theorem phase_27_8 : ∀ i ∈ List.range 4, PhaseAt 27 (8+i) := by decide +kernel

theorem phase_27_12 : ∀ i ∈ List.range 4, PhaseAt 27 (12+i) := by decide +kernel

theorem phase_27_16 : ∀ i ∈ List.range 4, PhaseAt 27 (16+i) := by decide +kernel

theorem phase_27_20 : ∀ i ∈ List.range 4, PhaseAt 27 (20+i) := by decide +kernel

theorem phase_27_24 : ∀ i ∈ List.range 4, PhaseAt 27 (24+i) := by decide +kernel

theorem phase_27_28 : ∀ i ∈ List.range 4, PhaseAt 27 (28+i) := by decide +kernel

theorem phase_27_32 : ∀ i ∈ List.range 4, PhaseAt 27 (32+i) := by decide +kernel

theorem phase_27_36 : ∀ i ∈ List.range 4, PhaseAt 27 (36+i) := by decide +kernel

theorem phase_27_40 : ∀ i ∈ List.range 4, PhaseAt 27 (40+i) := by decide +kernel

theorem phase_27_44 : ∀ i ∈ List.range 4, PhaseAt 27 (44+i) := by decide +kernel

theorem phase_27_48 : ∀ i ∈ List.range 4, PhaseAt 27 (48+i) := by decide +kernel

theorem phase_27_52 : ∀ i ∈ List.range 4, PhaseAt 27 (52+i) := by decide +kernel

theorem phase_27_56 : ∀ i ∈ List.range 4, PhaseAt 27 (56+i) := by decide +kernel

theorem phase_27_60 : ∀ i ∈ List.range 4, PhaseAt 27 (60+i) := by decide +kernel

theorem phase_27_64 : ∀ i ∈ List.range 4, PhaseAt 27 (64+i) := by decide +kernel

theorem phase_27_68 : ∀ i ∈ List.range 4, PhaseAt 27 (68+i) := by decide +kernel

theorem phase_27_72 : ∀ i ∈ List.range 4, PhaseAt 27 (72+i) := by decide +kernel

theorem phase_27_76 : ∀ i ∈ List.range 4, PhaseAt 27 (76+i) := by decide +kernel

theorem phase_27_80 : ∀ i ∈ List.range 4, PhaseAt 27 (80+i) := by decide +kernel

theorem phase_27_84 : ∀ i ∈ List.range 4, PhaseAt 27 (84+i) := by decide +kernel

theorem phase_27_88 : ∀ i ∈ List.range 4, PhaseAt 27 (88+i) := by decide +kernel

theorem phase_27_92 : ∀ i ∈ List.range 4, PhaseAt 27 (92+i) := by decide +kernel

theorem phase_27_96 : ∀ i ∈ List.range 4, PhaseAt 27 (96+i) := by decide +kernel

theorem phase_27_100 : ∀ i ∈ List.range 4, PhaseAt 27 (100+i) := by decide +kernel

theorem phase_27_104 : ∀ i ∈ List.range 4, PhaseAt 27 (104+i) := by decide +kernel

theorem phase_27_108 : ∀ i ∈ List.range 4, PhaseAt 27 (108+i) := by decide +kernel

theorem phase_27_112 : ∀ i ∈ List.range 4, PhaseAt 27 (112+i) := by decide +kernel

theorem phase_27_116 : ∀ i ∈ List.range 4, PhaseAt 27 (116+i) := by decide +kernel

theorem phase_27 (v : ℕ) (hv : v ∈ List.range 120) : PhaseAt 27 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 27 v)
  have h := (join 0 60 60 (join 0 28 32 (join 0 12 16 (join 0 4 8 phase_27_0 (join 4 4 4 phase_27_4 phase_27_8)) (join 12 8 8 (join 12 4 4 phase_27_12 phase_27_16) (join 20 4 4 phase_27_20 phase_27_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 phase_27_28 phase_27_32) (join 36 4 4 phase_27_36 phase_27_40)) (join 44 8 8 (join 44 4 4 phase_27_44 phase_27_48) (join 52 4 4 phase_27_52 phase_27_56)))) (join 60 28 32 (join 60 12 16 (join 60 4 8 phase_27_60 (join 64 4 4 phase_27_64 phase_27_68)) (join 72 8 8 (join 72 4 4 phase_27_72 phase_27_76) (join 80 4 4 phase_27_80 phase_27_84))) (join 88 16 16 (join 88 8 8 (join 88 4 4 phase_27_88 phase_27_92) (join 96 4 4 phase_27_96 phase_27_100)) (join 104 8 8 (join 104 4 4 phase_27_104 phase_27_108) (join 112 4 4 phase_27_112 phase_27_116)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_27_0 : ∀ i ∈ List.range 1, ThresholdAt 27 (0+i) := by decide +kernel

theorem threshold_27_1 : ∀ i ∈ List.range 1, ThresholdAt 27 (1+i) := by decide +kernel

theorem threshold_27_2 : ∀ i ∈ List.range 1, ThresholdAt 27 (2+i) := by decide +kernel

theorem threshold_27_3 : ∀ i ∈ List.range 1, ThresholdAt 27 (3+i) := by decide +kernel

theorem threshold_27_4 : ∀ i ∈ List.range 1, ThresholdAt 27 (4+i) := by decide +kernel

theorem threshold_27_5 : ∀ i ∈ List.range 1, ThresholdAt 27 (5+i) := by decide +kernel

theorem threshold_27_6 : ∀ i ∈ List.range 1, ThresholdAt 27 (6+i) := by decide +kernel

theorem threshold_27_7 : ∀ i ∈ List.range 1, ThresholdAt 27 (7+i) := by decide +kernel

theorem threshold_27_8 : ∀ i ∈ List.range 1, ThresholdAt 27 (8+i) := by decide +kernel

theorem threshold_27_9 : ∀ i ∈ List.range 1, ThresholdAt 27 (9+i) := by decide +kernel

theorem threshold_27_10 : ∀ i ∈ List.range 1, ThresholdAt 27 (10+i) := by decide +kernel

theorem threshold_27_11 : ∀ i ∈ List.range 1, ThresholdAt 27 (11+i) := by decide +kernel

theorem threshold_27_12 : ∀ i ∈ List.range 1, ThresholdAt 27 (12+i) := by decide +kernel

theorem threshold_27_13 : ∀ i ∈ List.range 1, ThresholdAt 27 (13+i) := by decide +kernel

theorem threshold_27_14 : ∀ i ∈ List.range 1, ThresholdAt 27 (14+i) := by decide +kernel

theorem threshold_27_15 : ∀ i ∈ List.range 1, ThresholdAt 27 (15+i) := by decide +kernel

theorem threshold_27_16 : ∀ i ∈ List.range 1, ThresholdAt 27 (16+i) := by decide +kernel

theorem threshold_27_17 : ∀ i ∈ List.range 1, ThresholdAt 27 (17+i) := by decide +kernel

theorem threshold_27_18 : ∀ i ∈ List.range 1, ThresholdAt 27 (18+i) := by decide +kernel

theorem threshold_27_19 : ∀ i ∈ List.range 1, ThresholdAt 27 (19+i) := by decide +kernel

theorem threshold_27_20 : ∀ i ∈ List.range 1, ThresholdAt 27 (20+i) := by decide +kernel

theorem threshold_27_21 : ∀ i ∈ List.range 1, ThresholdAt 27 (21+i) := by decide +kernel

theorem threshold_27_22 : ∀ i ∈ List.range 1, ThresholdAt 27 (22+i) := by decide +kernel

theorem threshold_27_23 : ∀ i ∈ List.range 1, ThresholdAt 27 (23+i) := by decide +kernel

theorem threshold_27_24 : ∀ i ∈ List.range 1, ThresholdAt 27 (24+i) := by decide +kernel

theorem threshold_27_25 : ∀ i ∈ List.range 1, ThresholdAt 27 (25+i) := by decide +kernel

theorem threshold_27_26 : ∀ i ∈ List.range 1, ThresholdAt 27 (26+i) := by decide +kernel

theorem threshold_27_27 : ∀ i ∈ List.range 1, ThresholdAt 27 (27+i) := by decide +kernel

theorem threshold_27_28 : ∀ i ∈ List.range 1, ThresholdAt 27 (28+i) := by decide +kernel

theorem threshold_27_29 : ∀ i ∈ List.range 1, ThresholdAt 27 (29+i) := by decide +kernel

theorem threshold_27_30 : ∀ i ∈ List.range 1, ThresholdAt 27 (30+i) := by decide +kernel

theorem threshold_27_31 : ∀ i ∈ List.range 1, ThresholdAt 27 (31+i) := by decide +kernel

theorem threshold_27_32 : ∀ i ∈ List.range 1, ThresholdAt 27 (32+i) := by decide +kernel

theorem threshold_27_33 : ∀ i ∈ List.range 1, ThresholdAt 27 (33+i) := by decide +kernel

theorem threshold_27_34 : ∀ i ∈ List.range 1, ThresholdAt 27 (34+i) := by decide +kernel

theorem threshold_27_35 : ∀ i ∈ List.range 1, ThresholdAt 27 (35+i) := by decide +kernel

theorem threshold_27_36 : ∀ i ∈ List.range 1, ThresholdAt 27 (36+i) := by decide +kernel

theorem threshold_27_37 : ∀ i ∈ List.range 1, ThresholdAt 27 (37+i) := by decide +kernel

theorem threshold_27_38 : ∀ i ∈ List.range 1, ThresholdAt 27 (38+i) := by decide +kernel

theorem threshold_27_39 : ∀ i ∈ List.range 1, ThresholdAt 27 (39+i) := by decide +kernel

theorem threshold_27_40 : ∀ i ∈ List.range 1, ThresholdAt 27 (40+i) := by decide +kernel

theorem threshold_27_41 : ∀ i ∈ List.range 1, ThresholdAt 27 (41+i) := by decide +kernel

theorem threshold_27_42 : ∀ i ∈ List.range 1, ThresholdAt 27 (42+i) := by decide +kernel

theorem threshold_27_43 : ∀ i ∈ List.range 1, ThresholdAt 27 (43+i) := by decide +kernel

theorem threshold_27_44 : ∀ i ∈ List.range 1, ThresholdAt 27 (44+i) := by decide +kernel

theorem threshold_27_45 : ∀ i ∈ List.range 1, ThresholdAt 27 (45+i) := by decide +kernel

theorem threshold_27_46 : ∀ i ∈ List.range 1, ThresholdAt 27 (46+i) := by decide +kernel

theorem threshold_27_47 : ∀ i ∈ List.range 1, ThresholdAt 27 (47+i) := by decide +kernel

theorem threshold_27_48 : ∀ i ∈ List.range 1, ThresholdAt 27 (48+i) := by decide +kernel

theorem threshold_27_49 : ∀ i ∈ List.range 1, ThresholdAt 27 (49+i) := by decide +kernel

theorem threshold_27_50 : ∀ i ∈ List.range 1, ThresholdAt 27 (50+i) := by decide +kernel

theorem threshold_27_51 : ∀ i ∈ List.range 1, ThresholdAt 27 (51+i) := by decide +kernel

theorem threshold_27_52 : ∀ i ∈ List.range 1, ThresholdAt 27 (52+i) := by decide +kernel

theorem threshold_27_53 : ∀ i ∈ List.range 1, ThresholdAt 27 (53+i) := by decide +kernel

theorem threshold_27_54 : ∀ i ∈ List.range 1, ThresholdAt 27 (54+i) := by decide +kernel

theorem threshold_27_55 : ∀ i ∈ List.range 1, ThresholdAt 27 (55+i) := by decide +kernel

theorem threshold_27_56 : ∀ i ∈ List.range 1, ThresholdAt 27 (56+i) := by decide +kernel

theorem threshold_27_57 : ∀ i ∈ List.range 1, ThresholdAt 27 (57+i) := by decide +kernel

theorem threshold_27_58 : ∀ i ∈ List.range 1, ThresholdAt 27 (58+i) := by decide +kernel

theorem threshold_27_59 : ∀ i ∈ List.range 1, ThresholdAt 27 (59+i) := by decide +kernel

theorem threshold_27_60 : ∀ i ∈ List.range 1, ThresholdAt 27 (60+i) := by decide +kernel

theorem threshold_27_61 : ∀ i ∈ List.range 1, ThresholdAt 27 (61+i) := by decide +kernel

theorem threshold_27_62 : ∀ i ∈ List.range 1, ThresholdAt 27 (62+i) := by decide +kernel

theorem threshold_27_63 : ∀ i ∈ List.range 1, ThresholdAt 27 (63+i) := by decide +kernel

theorem threshold_27_64 : ∀ i ∈ List.range 1, ThresholdAt 27 (64+i) := by decide +kernel

theorem threshold_27_65 : ∀ i ∈ List.range 1, ThresholdAt 27 (65+i) := by decide +kernel

theorem threshold_27_66 : ∀ i ∈ List.range 1, ThresholdAt 27 (66+i) := by decide +kernel

theorem threshold_27_67 : ∀ i ∈ List.range 1, ThresholdAt 27 (67+i) := by decide +kernel

theorem threshold_27_68 : ∀ i ∈ List.range 1, ThresholdAt 27 (68+i) := by decide +kernel

theorem threshold_27_69 : ∀ i ∈ List.range 1, ThresholdAt 27 (69+i) := by decide +kernel

theorem threshold_27_70 : ∀ i ∈ List.range 1, ThresholdAt 27 (70+i) := by decide +kernel

theorem threshold_27_71 : ∀ i ∈ List.range 1, ThresholdAt 27 (71+i) := by decide +kernel

theorem threshold_27_72 : ∀ i ∈ List.range 1, ThresholdAt 27 (72+i) := by decide +kernel

theorem threshold_27_73 : ∀ i ∈ List.range 1, ThresholdAt 27 (73+i) := by decide +kernel

theorem threshold_27_74 : ∀ i ∈ List.range 1, ThresholdAt 27 (74+i) := by decide +kernel

theorem threshold_27_75 : ∀ i ∈ List.range 1, ThresholdAt 27 (75+i) := by decide +kernel

theorem threshold_27_76 : ∀ i ∈ List.range 1, ThresholdAt 27 (76+i) := by decide +kernel

theorem threshold_27_77 : ∀ i ∈ List.range 1, ThresholdAt 27 (77+i) := by decide +kernel

theorem threshold_27_78 : ∀ i ∈ List.range 1, ThresholdAt 27 (78+i) := by decide +kernel

theorem threshold_27_79 : ∀ i ∈ List.range 1, ThresholdAt 27 (79+i) := by decide +kernel

theorem threshold_27_80 : ∀ i ∈ List.range 1, ThresholdAt 27 (80+i) := by decide +kernel

theorem threshold_27_81 : ∀ i ∈ List.range 1, ThresholdAt 27 (81+i) := by decide +kernel

theorem threshold_27_82 : ∀ i ∈ List.range 1, ThresholdAt 27 (82+i) := by decide +kernel

theorem threshold_27_83 : ∀ i ∈ List.range 1, ThresholdAt 27 (83+i) := by decide +kernel

theorem threshold_27_84 : ∀ i ∈ List.range 1, ThresholdAt 27 (84+i) := by decide +kernel

theorem threshold_27_85 : ∀ i ∈ List.range 1, ThresholdAt 27 (85+i) := by decide +kernel

theorem threshold_27_86 : ∀ i ∈ List.range 1, ThresholdAt 27 (86+i) := by decide +kernel

theorem threshold_27_87 : ∀ i ∈ List.range 1, ThresholdAt 27 (87+i) := by decide +kernel

theorem threshold_27_88 : ∀ i ∈ List.range 1, ThresholdAt 27 (88+i) := by decide +kernel

theorem threshold_27_89 : ∀ i ∈ List.range 1, ThresholdAt 27 (89+i) := by decide +kernel

theorem threshold_27_90 : ∀ i ∈ List.range 1, ThresholdAt 27 (90+i) := by decide +kernel

theorem threshold_27_91 : ∀ i ∈ List.range 1, ThresholdAt 27 (91+i) := by decide +kernel

theorem threshold_27_92 : ∀ i ∈ List.range 1, ThresholdAt 27 (92+i) := by decide +kernel

theorem threshold_27_93 : ∀ i ∈ List.range 1, ThresholdAt 27 (93+i) := by decide +kernel

theorem threshold_27_94 : ∀ i ∈ List.range 1, ThresholdAt 27 (94+i) := by decide +kernel

theorem threshold_27_95 : ∀ i ∈ List.range 1, ThresholdAt 27 (95+i) := by decide +kernel

theorem threshold_27_96 : ∀ i ∈ List.range 1, ThresholdAt 27 (96+i) := by decide +kernel

theorem threshold_27_97 : ∀ i ∈ List.range 1, ThresholdAt 27 (97+i) := by decide +kernel

theorem threshold_27_98 : ∀ i ∈ List.range 1, ThresholdAt 27 (98+i) := by decide +kernel

theorem threshold_27_99 : ∀ i ∈ List.range 1, ThresholdAt 27 (99+i) := by decide +kernel

theorem threshold_27_100 : ∀ i ∈ List.range 1, ThresholdAt 27 (100+i) := by decide +kernel

theorem threshold_27_101 : ∀ i ∈ List.range 1, ThresholdAt 27 (101+i) := by decide +kernel

theorem threshold_27_102 : ∀ i ∈ List.range 1, ThresholdAt 27 (102+i) := by decide +kernel

theorem threshold_27_103 : ∀ i ∈ List.range 1, ThresholdAt 27 (103+i) := by decide +kernel

theorem threshold_27_104 : ∀ i ∈ List.range 1, ThresholdAt 27 (104+i) := by decide +kernel

theorem threshold_27_105 : ∀ i ∈ List.range 1, ThresholdAt 27 (105+i) := by decide +kernel

theorem threshold_27_106 : ∀ i ∈ List.range 1, ThresholdAt 27 (106+i) := by decide +kernel

theorem threshold_27_107 : ∀ i ∈ List.range 1, ThresholdAt 27 (107+i) := by decide +kernel

theorem threshold_27_108 : ∀ i ∈ List.range 1, ThresholdAt 27 (108+i) := by decide +kernel

theorem threshold_27_109 : ∀ i ∈ List.range 1, ThresholdAt 27 (109+i) := by decide +kernel

theorem threshold_27_110 : ∀ i ∈ List.range 1, ThresholdAt 27 (110+i) := by decide +kernel

theorem threshold_27_111 : ∀ i ∈ List.range 1, ThresholdAt 27 (111+i) := by decide +kernel

theorem threshold_27_112 : ∀ i ∈ List.range 1, ThresholdAt 27 (112+i) := by decide +kernel

theorem threshold_27_113 : ∀ i ∈ List.range 1, ThresholdAt 27 (113+i) := by decide +kernel

theorem threshold_27_114 : ∀ i ∈ List.range 1, ThresholdAt 27 (114+i) := by decide +kernel

theorem threshold_27_115 : ∀ i ∈ List.range 1, ThresholdAt 27 (115+i) := by decide +kernel

theorem threshold_27_116 : ∀ i ∈ List.range 1, ThresholdAt 27 (116+i) := by decide +kernel

theorem threshold_27_117 : ∀ i ∈ List.range 1, ThresholdAt 27 (117+i) := by decide +kernel

theorem threshold_27_118 : ∀ i ∈ List.range 1, ThresholdAt 27 (118+i) := by decide +kernel

theorem threshold_27_119 : ∀ i ∈ List.range 1, ThresholdAt 27 (119+i) := by decide +kernel

theorem threshold_27 (v : ℕ) (hv : v ∈ List.range 120) : ThresholdAt 27 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 27 v)
  have h := (join 0 60 60 (join 0 30 30 (join 0 15 15 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_27_0 (join 1 1 1 threshold_27_1 threshold_27_2)) (join 3 2 2 (join 3 1 1 threshold_27_3 threshold_27_4) (join 5 1 1 threshold_27_5 threshold_27_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_27_7 threshold_27_8) (join 9 1 1 threshold_27_9 threshold_27_10)) (join 11 2 2 (join 11 1 1 threshold_27_11 threshold_27_12) (join 13 1 1 threshold_27_13 threshold_27_14)))) (join 15 7 8 (join 15 3 4 (join 15 1 2 threshold_27_15 (join 16 1 1 threshold_27_16 threshold_27_17)) (join 18 2 2 (join 18 1 1 threshold_27_18 threshold_27_19) (join 20 1 1 threshold_27_20 threshold_27_21))) (join 22 4 4 (join 22 2 2 (join 22 1 1 threshold_27_22 threshold_27_23) (join 24 1 1 threshold_27_24 threshold_27_25)) (join 26 2 2 (join 26 1 1 threshold_27_26 threshold_27_27) (join 28 1 1 threshold_27_28 threshold_27_29))))) (join 30 15 15 (join 30 7 8 (join 30 3 4 (join 30 1 2 threshold_27_30 (join 31 1 1 threshold_27_31 threshold_27_32)) (join 33 2 2 (join 33 1 1 threshold_27_33 threshold_27_34) (join 35 1 1 threshold_27_35 threshold_27_36))) (join 37 4 4 (join 37 2 2 (join 37 1 1 threshold_27_37 threshold_27_38) (join 39 1 1 threshold_27_39 threshold_27_40)) (join 41 2 2 (join 41 1 1 threshold_27_41 threshold_27_42) (join 43 1 1 threshold_27_43 threshold_27_44)))) (join 45 7 8 (join 45 3 4 (join 45 1 2 threshold_27_45 (join 46 1 1 threshold_27_46 threshold_27_47)) (join 48 2 2 (join 48 1 1 threshold_27_48 threshold_27_49) (join 50 1 1 threshold_27_50 threshold_27_51))) (join 52 4 4 (join 52 2 2 (join 52 1 1 threshold_27_52 threshold_27_53) (join 54 1 1 threshold_27_54 threshold_27_55)) (join 56 2 2 (join 56 1 1 threshold_27_56 threshold_27_57) (join 58 1 1 threshold_27_58 threshold_27_59)))))) (join 60 30 30 (join 60 15 15 (join 60 7 8 (join 60 3 4 (join 60 1 2 threshold_27_60 (join 61 1 1 threshold_27_61 threshold_27_62)) (join 63 2 2 (join 63 1 1 threshold_27_63 threshold_27_64) (join 65 1 1 threshold_27_65 threshold_27_66))) (join 67 4 4 (join 67 2 2 (join 67 1 1 threshold_27_67 threshold_27_68) (join 69 1 1 threshold_27_69 threshold_27_70)) (join 71 2 2 (join 71 1 1 threshold_27_71 threshold_27_72) (join 73 1 1 threshold_27_73 threshold_27_74)))) (join 75 7 8 (join 75 3 4 (join 75 1 2 threshold_27_75 (join 76 1 1 threshold_27_76 threshold_27_77)) (join 78 2 2 (join 78 1 1 threshold_27_78 threshold_27_79) (join 80 1 1 threshold_27_80 threshold_27_81))) (join 82 4 4 (join 82 2 2 (join 82 1 1 threshold_27_82 threshold_27_83) (join 84 1 1 threshold_27_84 threshold_27_85)) (join 86 2 2 (join 86 1 1 threshold_27_86 threshold_27_87) (join 88 1 1 threshold_27_88 threshold_27_89))))) (join 90 15 15 (join 90 7 8 (join 90 3 4 (join 90 1 2 threshold_27_90 (join 91 1 1 threshold_27_91 threshold_27_92)) (join 93 2 2 (join 93 1 1 threshold_27_93 threshold_27_94) (join 95 1 1 threshold_27_95 threshold_27_96))) (join 97 4 4 (join 97 2 2 (join 97 1 1 threshold_27_97 threshold_27_98) (join 99 1 1 threshold_27_99 threshold_27_100)) (join 101 2 2 (join 101 1 1 threshold_27_101 threshold_27_102) (join 103 1 1 threshold_27_103 threshold_27_104)))) (join 105 7 8 (join 105 3 4 (join 105 1 2 threshold_27_105 (join 106 1 1 threshold_27_106 threshold_27_107)) (join 108 2 2 (join 108 1 1 threshold_27_108 threshold_27_109) (join 110 1 1 threshold_27_110 threshold_27_111))) (join 112 4 4 (join 112 2 2 (join 112 1 1 threshold_27_112 threshold_27_113) (join 114 1 1 threshold_27_114 threshold_27_115)) (join 116 2 2 (join 116 1 1 threshold_27_116 threshold_27_117) (join 118 1 1 threshold_27_118 threshold_27_119)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_27_0 : ∀ i ∈ List.range 4, LedgerAt 27 (0+i) := by decide +kernel

theorem ledger_27_4 : ∀ i ∈ List.range 4, LedgerAt 27 (4+i) := by decide +kernel

theorem ledger_27_8 : ∀ i ∈ List.range 4, LedgerAt 27 (8+i) := by decide +kernel

theorem ledger_27_12 : ∀ i ∈ List.range 4, LedgerAt 27 (12+i) := by decide +kernel

theorem ledger_27_16 : ∀ i ∈ List.range 4, LedgerAt 27 (16+i) := by decide +kernel

theorem ledger_27_20 : ∀ i ∈ List.range 4, LedgerAt 27 (20+i) := by decide +kernel

theorem ledger_27_24 : ∀ i ∈ List.range 4, LedgerAt 27 (24+i) := by decide +kernel

theorem ledger_27_28 : ∀ i ∈ List.range 4, LedgerAt 27 (28+i) := by decide +kernel

theorem ledger_27_32 : ∀ i ∈ List.range 4, LedgerAt 27 (32+i) := by decide +kernel

theorem ledger_27_36 : ∀ i ∈ List.range 4, LedgerAt 27 (36+i) := by decide +kernel

theorem ledger_27_40 : ∀ i ∈ List.range 4, LedgerAt 27 (40+i) := by decide +kernel

theorem ledger_27_44 : ∀ i ∈ List.range 4, LedgerAt 27 (44+i) := by decide +kernel

theorem ledger_27_48 : ∀ i ∈ List.range 4, LedgerAt 27 (48+i) := by decide +kernel

theorem ledger_27_52 : ∀ i ∈ List.range 4, LedgerAt 27 (52+i) := by decide +kernel

theorem ledger_27_56 : ∀ i ∈ List.range 4, LedgerAt 27 (56+i) := by decide +kernel

theorem ledger_27_60 : ∀ i ∈ List.range 4, LedgerAt 27 (60+i) := by decide +kernel

theorem ledger_27_64 : ∀ i ∈ List.range 4, LedgerAt 27 (64+i) := by decide +kernel

theorem ledger_27_68 : ∀ i ∈ List.range 4, LedgerAt 27 (68+i) := by decide +kernel

theorem ledger_27_72 : ∀ i ∈ List.range 4, LedgerAt 27 (72+i) := by decide +kernel

theorem ledger_27_76 : ∀ i ∈ List.range 4, LedgerAt 27 (76+i) := by decide +kernel

theorem ledger_27_80 : ∀ i ∈ List.range 4, LedgerAt 27 (80+i) := by decide +kernel

theorem ledger_27_84 : ∀ i ∈ List.range 4, LedgerAt 27 (84+i) := by decide +kernel

theorem ledger_27_88 : ∀ i ∈ List.range 4, LedgerAt 27 (88+i) := by decide +kernel

theorem ledger_27_92 : ∀ i ∈ List.range 4, LedgerAt 27 (92+i) := by decide +kernel

theorem ledger_27_96 : ∀ i ∈ List.range 4, LedgerAt 27 (96+i) := by decide +kernel

theorem ledger_27_100 : ∀ i ∈ List.range 4, LedgerAt 27 (100+i) := by decide +kernel

theorem ledger_27_104 : ∀ i ∈ List.range 4, LedgerAt 27 (104+i) := by decide +kernel

theorem ledger_27_108 : ∀ i ∈ List.range 4, LedgerAt 27 (108+i) := by decide +kernel

theorem ledger_27_112 : ∀ i ∈ List.range 4, LedgerAt 27 (112+i) := by decide +kernel

theorem ledger_27_116 : ∀ i ∈ List.range 4, LedgerAt 27 (116+i) := by decide +kernel

theorem ledger_27 (v : ℕ) (hv : v ∈ List.range 120) : LedgerAt 27 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 27 v)
  have h := (join 0 60 60 (join 0 28 32 (join 0 12 16 (join 0 4 8 ledger_27_0 (join 4 4 4 ledger_27_4 ledger_27_8)) (join 12 8 8 (join 12 4 4 ledger_27_12 ledger_27_16) (join 20 4 4 ledger_27_20 ledger_27_24))) (join 28 16 16 (join 28 8 8 (join 28 4 4 ledger_27_28 ledger_27_32) (join 36 4 4 ledger_27_36 ledger_27_40)) (join 44 8 8 (join 44 4 4 ledger_27_44 ledger_27_48) (join 52 4 4 ledger_27_52 ledger_27_56)))) (join 60 28 32 (join 60 12 16 (join 60 4 8 ledger_27_60 (join 64 4 4 ledger_27_64 ledger_27_68)) (join 72 8 8 (join 72 4 4 ledger_27_72 ledger_27_76) (join 80 4 4 ledger_27_80 ledger_27_84))) (join 88 16 16 (join 88 8 8 (join 88 4 4 ledger_27_88 ledger_27_92) (join 96 4 4 ledger_27_96 ledger_27_100)) (join 104 8 8 (join 104 4 4 ledger_27_104 ledger_27_108) (join 112 4 4 ledger_27_112 ledger_27_116)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
