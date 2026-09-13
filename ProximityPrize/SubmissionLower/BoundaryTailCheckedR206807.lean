import ProximityPrize.SubmissionLower.BoundaryTailCheckedR196807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_20_0 : ∀ i ∈ List.range 4, GeometryAt 20 (0+i) := by decide +kernel

theorem geometry_20_4 : ∀ i ∈ List.range 4, GeometryAt 20 (4+i) := by decide +kernel

theorem geometry_20_8 : ∀ i ∈ List.range 4, GeometryAt 20 (8+i) := by decide +kernel

theorem geometry_20_12 : ∀ i ∈ List.range 4, GeometryAt 20 (12+i) := by decide +kernel

theorem geometry_20_16 : ∀ i ∈ List.range 4, GeometryAt 20 (16+i) := by decide +kernel

theorem geometry_20_20 : ∀ i ∈ List.range 4, GeometryAt 20 (20+i) := by decide +kernel

theorem geometry_20_24 : ∀ i ∈ List.range 4, GeometryAt 20 (24+i) := by decide +kernel

theorem geometry_20_28 : ∀ i ∈ List.range 4, GeometryAt 20 (28+i) := by decide +kernel

theorem geometry_20_32 : ∀ i ∈ List.range 4, GeometryAt 20 (32+i) := by decide +kernel

theorem geometry_20_36 : ∀ i ∈ List.range 4, GeometryAt 20 (36+i) := by decide +kernel

theorem geometry_20_40 : ∀ i ∈ List.range 4, GeometryAt 20 (40+i) := by decide +kernel

theorem geometry_20_44 : ∀ i ∈ List.range 4, GeometryAt 20 (44+i) := by decide +kernel

theorem geometry_20_48 : ∀ i ∈ List.range 4, GeometryAt 20 (48+i) := by decide +kernel

theorem geometry_20_52 : ∀ i ∈ List.range 4, GeometryAt 20 (52+i) := by decide +kernel

theorem geometry_20_56 : ∀ i ∈ List.range 4, GeometryAt 20 (56+i) := by decide +kernel

theorem geometry_20_60 : ∀ i ∈ List.range 4, GeometryAt 20 (60+i) := by decide +kernel

theorem geometry_20_64 : ∀ i ∈ List.range 4, GeometryAt 20 (64+i) := by decide +kernel

theorem geometry_20_68 : ∀ i ∈ List.range 4, GeometryAt 20 (68+i) := by decide +kernel

theorem geometry_20_72 : ∀ i ∈ List.range 4, GeometryAt 20 (72+i) := by decide +kernel

theorem geometry_20_76 : ∀ i ∈ List.range 4, GeometryAt 20 (76+i) := by decide +kernel

theorem geometry_20_80 : ∀ i ∈ List.range 4, GeometryAt 20 (80+i) := by decide +kernel

theorem geometry_20_84 : ∀ i ∈ List.range 4, GeometryAt 20 (84+i) := by decide +kernel

theorem geometry_20_88 : ∀ i ∈ List.range 4, GeometryAt 20 (88+i) := by decide +kernel

theorem geometry_20_92 : ∀ i ∈ List.range 4, GeometryAt 20 (92+i) := by decide +kernel

theorem geometry_20_96 : ∀ i ∈ List.range 4, GeometryAt 20 (96+i) := by decide +kernel

theorem geometry_20_100 : ∀ i ∈ List.range 4, GeometryAt 20 (100+i) := by decide +kernel

theorem geometry_20_104 : ∀ i ∈ List.range 4, GeometryAt 20 (104+i) := by decide +kernel

theorem geometry_20_108 : ∀ i ∈ List.range 4, GeometryAt 20 (108+i) := by decide +kernel

theorem geometry_20_112 : ∀ i ∈ List.range 4, GeometryAt 20 (112+i) := by decide +kernel

theorem geometry_20_116 : ∀ i ∈ List.range 4, GeometryAt 20 (116+i) := by decide +kernel

theorem geometry_20_120 : ∀ i ∈ List.range 4, GeometryAt 20 (120+i) := by decide +kernel

theorem geometry_20_124 : ∀ i ∈ List.range 3, GeometryAt 20 (124+i) := by decide +kernel

theorem geometry_20 (v : ℕ) (hv : v ∈ List.range 127) : GeometryAt 20 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 20 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_20_0 geometry_20_4) (join 8 4 4 geometry_20_8 geometry_20_12)) (join 16 8 8 (join 16 4 4 geometry_20_16 geometry_20_20) (join 24 4 4 geometry_20_24 geometry_20_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 geometry_20_32 geometry_20_36) (join 40 4 4 geometry_20_40 geometry_20_44)) (join 48 8 8 (join 48 4 4 geometry_20_48 geometry_20_52) (join 56 4 4 geometry_20_56 geometry_20_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 geometry_20_64 geometry_20_68) (join 72 4 4 geometry_20_72 geometry_20_76)) (join 80 8 8 (join 80 4 4 geometry_20_80 geometry_20_84) (join 88 4 4 geometry_20_88 geometry_20_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 geometry_20_96 geometry_20_100) (join 104 4 4 geometry_20_104 geometry_20_108)) (join 112 8 7 (join 112 4 4 geometry_20_112 geometry_20_116) (join 120 4 3 geometry_20_120 geometry_20_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_20_0 : ∀ i ∈ List.range 4, StrictAt 20 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (0+i)) 20 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_4 : ∀ i ∈ List.range 4, StrictAt 20 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (4+i)) 20 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_8 : ∀ i ∈ List.range 4, StrictAt 20 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (8+i)) 20 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_12 : ∀ i ∈ List.range 4, StrictAt 20 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (12+i)) 20 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_16 : ∀ i ∈ List.range 4, StrictAt 20 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (16+i)) 20 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_20 : ∀ i ∈ List.range 4, StrictAt 20 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (20+i)) 20 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_24 : ∀ i ∈ List.range 4, StrictAt 20 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (24+i)) 20 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_28 : ∀ i ∈ List.range 4, StrictAt 20 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (28+i)) 20 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_32 : ∀ i ∈ List.range 4, StrictAt 20 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (32+i)) 20 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_36 : ∀ i ∈ List.range 4, StrictAt 20 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (36+i)) 20 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_40 : ∀ i ∈ List.range 4, StrictAt 20 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (40+i)) 20 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_44 : ∀ i ∈ List.range 4, StrictAt 20 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (44+i)) 20 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_48 : ∀ i ∈ List.range 4, StrictAt 20 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (48+i)) 20 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_52 : ∀ i ∈ List.range 4, StrictAt 20 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (52+i)) 20 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_56 : ∀ i ∈ List.range 4, StrictAt 20 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (56+i)) 20 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_60 : ∀ i ∈ List.range 4, StrictAt 20 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (60+i)) 20 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_64 : ∀ i ∈ List.range 4, StrictAt 20 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (64+i)) 20 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_68 : ∀ i ∈ List.range 4, StrictAt 20 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (68+i)) 20 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_72 : ∀ i ∈ List.range 4, StrictAt 20 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (72+i)) 20 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_76 : ∀ i ∈ List.range 4, StrictAt 20 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (76+i)) 20 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_80 : ∀ i ∈ List.range 4, StrictAt 20 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (80+i)) 20 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_84 : ∀ i ∈ List.range 4, StrictAt 20 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (84+i)) 20 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_88 : ∀ i ∈ List.range 4, StrictAt 20 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (88+i)) 20 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_92 : ∀ i ∈ List.range 4, StrictAt 20 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (92+i)) 20 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_96 : ∀ i ∈ List.range 4, StrictAt 20 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (96+i)) 20 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_100 : ∀ i ∈ List.range 4, StrictAt 20 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (100+i)) 20 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_104 : ∀ i ∈ List.range 4, StrictAt 20 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (104+i)) 20 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_108 : ∀ i ∈ List.range 4, StrictAt 20 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (108+i)) 20 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_112 : ∀ i ∈ List.range 4, StrictAt 20 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (112+i)) 20 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_116 : ∀ i ∈ List.range 4, StrictAt 20 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (116+i)) 20 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_120 : ∀ i ∈ List.range 4, StrictAt 20 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (120+i)) 20 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20_124 : ∀ i ∈ List.range 3, StrictAt 20 (124+i) := by
  have h : ∀ i ∈ List.range 3, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 20 (124+i)) 20 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_20 (v : ℕ) (hv : v ∈ List.range 127) : StrictAt 20 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 20 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_20_0 strict_20_4) (join 8 4 4 strict_20_8 strict_20_12)) (join 16 8 8 (join 16 4 4 strict_20_16 strict_20_20) (join 24 4 4 strict_20_24 strict_20_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 strict_20_32 strict_20_36) (join 40 4 4 strict_20_40 strict_20_44)) (join 48 8 8 (join 48 4 4 strict_20_48 strict_20_52) (join 56 4 4 strict_20_56 strict_20_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 strict_20_64 strict_20_68) (join 72 4 4 strict_20_72 strict_20_76)) (join 80 8 8 (join 80 4 4 strict_20_80 strict_20_84) (join 88 4 4 strict_20_88 strict_20_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 strict_20_96 strict_20_100) (join 104 4 4 strict_20_104 strict_20_108)) (join 112 8 7 (join 112 4 4 strict_20_112 strict_20_116) (join 120 4 3 strict_20_120 strict_20_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_20_0 : ∀ i ∈ List.range 4, PhaseAt 20 (0+i) := by decide +kernel

theorem phase_20_4 : ∀ i ∈ List.range 4, PhaseAt 20 (4+i) := by decide +kernel

theorem phase_20_8 : ∀ i ∈ List.range 4, PhaseAt 20 (8+i) := by decide +kernel

theorem phase_20_12 : ∀ i ∈ List.range 4, PhaseAt 20 (12+i) := by decide +kernel

theorem phase_20_16 : ∀ i ∈ List.range 4, PhaseAt 20 (16+i) := by decide +kernel

theorem phase_20_20 : ∀ i ∈ List.range 4, PhaseAt 20 (20+i) := by decide +kernel

theorem phase_20_24 : ∀ i ∈ List.range 4, PhaseAt 20 (24+i) := by decide +kernel

theorem phase_20_28 : ∀ i ∈ List.range 4, PhaseAt 20 (28+i) := by decide +kernel

theorem phase_20_32 : ∀ i ∈ List.range 4, PhaseAt 20 (32+i) := by decide +kernel

theorem phase_20_36 : ∀ i ∈ List.range 4, PhaseAt 20 (36+i) := by decide +kernel

theorem phase_20_40 : ∀ i ∈ List.range 4, PhaseAt 20 (40+i) := by decide +kernel

theorem phase_20_44 : ∀ i ∈ List.range 4, PhaseAt 20 (44+i) := by decide +kernel

theorem phase_20_48 : ∀ i ∈ List.range 4, PhaseAt 20 (48+i) := by decide +kernel

theorem phase_20_52 : ∀ i ∈ List.range 4, PhaseAt 20 (52+i) := by decide +kernel

theorem phase_20_56 : ∀ i ∈ List.range 4, PhaseAt 20 (56+i) := by decide +kernel

theorem phase_20_60 : ∀ i ∈ List.range 4, PhaseAt 20 (60+i) := by decide +kernel

theorem phase_20_64 : ∀ i ∈ List.range 4, PhaseAt 20 (64+i) := by decide +kernel

theorem phase_20_68 : ∀ i ∈ List.range 4, PhaseAt 20 (68+i) := by decide +kernel

theorem phase_20_72 : ∀ i ∈ List.range 4, PhaseAt 20 (72+i) := by decide +kernel

theorem phase_20_76 : ∀ i ∈ List.range 4, PhaseAt 20 (76+i) := by decide +kernel

theorem phase_20_80 : ∀ i ∈ List.range 4, PhaseAt 20 (80+i) := by decide +kernel

theorem phase_20_84 : ∀ i ∈ List.range 4, PhaseAt 20 (84+i) := by decide +kernel

theorem phase_20_88 : ∀ i ∈ List.range 4, PhaseAt 20 (88+i) := by decide +kernel

theorem phase_20_92 : ∀ i ∈ List.range 4, PhaseAt 20 (92+i) := by decide +kernel

theorem phase_20_96 : ∀ i ∈ List.range 4, PhaseAt 20 (96+i) := by decide +kernel

theorem phase_20_100 : ∀ i ∈ List.range 4, PhaseAt 20 (100+i) := by decide +kernel

theorem phase_20_104 : ∀ i ∈ List.range 4, PhaseAt 20 (104+i) := by decide +kernel

theorem phase_20_108 : ∀ i ∈ List.range 4, PhaseAt 20 (108+i) := by decide +kernel

theorem phase_20_112 : ∀ i ∈ List.range 4, PhaseAt 20 (112+i) := by decide +kernel

theorem phase_20_116 : ∀ i ∈ List.range 4, PhaseAt 20 (116+i) := by decide +kernel

theorem phase_20_120 : ∀ i ∈ List.range 4, PhaseAt 20 (120+i) := by decide +kernel

theorem phase_20_124 : ∀ i ∈ List.range 3, PhaseAt 20 (124+i) := by decide +kernel

theorem phase_20 (v : ℕ) (hv : v ∈ List.range 127) : PhaseAt 20 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 20 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_20_0 phase_20_4) (join 8 4 4 phase_20_8 phase_20_12)) (join 16 8 8 (join 16 4 4 phase_20_16 phase_20_20) (join 24 4 4 phase_20_24 phase_20_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 phase_20_32 phase_20_36) (join 40 4 4 phase_20_40 phase_20_44)) (join 48 8 8 (join 48 4 4 phase_20_48 phase_20_52) (join 56 4 4 phase_20_56 phase_20_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 phase_20_64 phase_20_68) (join 72 4 4 phase_20_72 phase_20_76)) (join 80 8 8 (join 80 4 4 phase_20_80 phase_20_84) (join 88 4 4 phase_20_88 phase_20_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 phase_20_96 phase_20_100) (join 104 4 4 phase_20_104 phase_20_108)) (join 112 8 7 (join 112 4 4 phase_20_112 phase_20_116) (join 120 4 3 phase_20_120 phase_20_124)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_20_0 : ∀ i ∈ List.range 1, ThresholdAt 20 (0+i) := by decide +kernel

theorem threshold_20_1 : ∀ i ∈ List.range 1, ThresholdAt 20 (1+i) := by decide +kernel

theorem threshold_20_2 : ∀ i ∈ List.range 1, ThresholdAt 20 (2+i) := by decide +kernel

theorem threshold_20_3 : ∀ i ∈ List.range 1, ThresholdAt 20 (3+i) := by decide +kernel

theorem threshold_20_4 : ∀ i ∈ List.range 1, ThresholdAt 20 (4+i) := by decide +kernel

theorem threshold_20_5 : ∀ i ∈ List.range 1, ThresholdAt 20 (5+i) := by decide +kernel

theorem threshold_20_6 : ∀ i ∈ List.range 1, ThresholdAt 20 (6+i) := by decide +kernel

theorem threshold_20_7 : ∀ i ∈ List.range 1, ThresholdAt 20 (7+i) := by decide +kernel

theorem threshold_20_8 : ∀ i ∈ List.range 1, ThresholdAt 20 (8+i) := by decide +kernel

theorem threshold_20_9 : ∀ i ∈ List.range 1, ThresholdAt 20 (9+i) := by decide +kernel

theorem threshold_20_10 : ∀ i ∈ List.range 1, ThresholdAt 20 (10+i) := by decide +kernel

theorem threshold_20_11 : ∀ i ∈ List.range 1, ThresholdAt 20 (11+i) := by decide +kernel

theorem threshold_20_12 : ∀ i ∈ List.range 1, ThresholdAt 20 (12+i) := by decide +kernel

theorem threshold_20_13 : ∀ i ∈ List.range 1, ThresholdAt 20 (13+i) := by decide +kernel

theorem threshold_20_14 : ∀ i ∈ List.range 1, ThresholdAt 20 (14+i) := by decide +kernel

theorem threshold_20_15 : ∀ i ∈ List.range 1, ThresholdAt 20 (15+i) := by decide +kernel

theorem threshold_20_16 : ∀ i ∈ List.range 1, ThresholdAt 20 (16+i) := by decide +kernel

theorem threshold_20_17 : ∀ i ∈ List.range 1, ThresholdAt 20 (17+i) := by decide +kernel

theorem threshold_20_18 : ∀ i ∈ List.range 1, ThresholdAt 20 (18+i) := by decide +kernel

theorem threshold_20_19 : ∀ i ∈ List.range 1, ThresholdAt 20 (19+i) := by decide +kernel

theorem threshold_20_20 : ∀ i ∈ List.range 1, ThresholdAt 20 (20+i) := by decide +kernel

theorem threshold_20_21 : ∀ i ∈ List.range 1, ThresholdAt 20 (21+i) := by decide +kernel

theorem threshold_20_22 : ∀ i ∈ List.range 1, ThresholdAt 20 (22+i) := by decide +kernel

theorem threshold_20_23 : ∀ i ∈ List.range 1, ThresholdAt 20 (23+i) := by decide +kernel

theorem threshold_20_24 : ∀ i ∈ List.range 1, ThresholdAt 20 (24+i) := by decide +kernel

theorem threshold_20_25 : ∀ i ∈ List.range 1, ThresholdAt 20 (25+i) := by decide +kernel

theorem threshold_20_26 : ∀ i ∈ List.range 1, ThresholdAt 20 (26+i) := by decide +kernel

theorem threshold_20_27 : ∀ i ∈ List.range 1, ThresholdAt 20 (27+i) := by decide +kernel

theorem threshold_20_28 : ∀ i ∈ List.range 1, ThresholdAt 20 (28+i) := by decide +kernel

theorem threshold_20_29 : ∀ i ∈ List.range 1, ThresholdAt 20 (29+i) := by decide +kernel

theorem threshold_20_30 : ∀ i ∈ List.range 1, ThresholdAt 20 (30+i) := by decide +kernel

theorem threshold_20_31 : ∀ i ∈ List.range 1, ThresholdAt 20 (31+i) := by decide +kernel

theorem threshold_20_32 : ∀ i ∈ List.range 1, ThresholdAt 20 (32+i) := by decide +kernel

theorem threshold_20_33 : ∀ i ∈ List.range 1, ThresholdAt 20 (33+i) := by decide +kernel

theorem threshold_20_34 : ∀ i ∈ List.range 1, ThresholdAt 20 (34+i) := by decide +kernel

theorem threshold_20_35 : ∀ i ∈ List.range 1, ThresholdAt 20 (35+i) := by decide +kernel

theorem threshold_20_36 : ∀ i ∈ List.range 1, ThresholdAt 20 (36+i) := by decide +kernel

theorem threshold_20_37 : ∀ i ∈ List.range 1, ThresholdAt 20 (37+i) := by decide +kernel

theorem threshold_20_38 : ∀ i ∈ List.range 1, ThresholdAt 20 (38+i) := by decide +kernel

theorem threshold_20_39 : ∀ i ∈ List.range 1, ThresholdAt 20 (39+i) := by decide +kernel

theorem threshold_20_40 : ∀ i ∈ List.range 1, ThresholdAt 20 (40+i) := by decide +kernel

theorem threshold_20_41 : ∀ i ∈ List.range 1, ThresholdAt 20 (41+i) := by decide +kernel

theorem threshold_20_42 : ∀ i ∈ List.range 1, ThresholdAt 20 (42+i) := by decide +kernel

theorem threshold_20_43 : ∀ i ∈ List.range 1, ThresholdAt 20 (43+i) := by decide +kernel

theorem threshold_20_44 : ∀ i ∈ List.range 1, ThresholdAt 20 (44+i) := by decide +kernel

theorem threshold_20_45 : ∀ i ∈ List.range 1, ThresholdAt 20 (45+i) := by decide +kernel

theorem threshold_20_46 : ∀ i ∈ List.range 1, ThresholdAt 20 (46+i) := by decide +kernel

theorem threshold_20_47 : ∀ i ∈ List.range 1, ThresholdAt 20 (47+i) := by decide +kernel

theorem threshold_20_48 : ∀ i ∈ List.range 1, ThresholdAt 20 (48+i) := by decide +kernel

theorem threshold_20_49 : ∀ i ∈ List.range 1, ThresholdAt 20 (49+i) := by decide +kernel

theorem threshold_20_50 : ∀ i ∈ List.range 1, ThresholdAt 20 (50+i) := by decide +kernel

theorem threshold_20_51 : ∀ i ∈ List.range 1, ThresholdAt 20 (51+i) := by decide +kernel

theorem threshold_20_52 : ∀ i ∈ List.range 1, ThresholdAt 20 (52+i) := by decide +kernel

theorem threshold_20_53 : ∀ i ∈ List.range 1, ThresholdAt 20 (53+i) := by decide +kernel

theorem threshold_20_54 : ∀ i ∈ List.range 1, ThresholdAt 20 (54+i) := by decide +kernel

theorem threshold_20_55 : ∀ i ∈ List.range 1, ThresholdAt 20 (55+i) := by decide +kernel

theorem threshold_20_56 : ∀ i ∈ List.range 1, ThresholdAt 20 (56+i) := by decide +kernel

theorem threshold_20_57 : ∀ i ∈ List.range 1, ThresholdAt 20 (57+i) := by decide +kernel

theorem threshold_20_58 : ∀ i ∈ List.range 1, ThresholdAt 20 (58+i) := by decide +kernel

theorem threshold_20_59 : ∀ i ∈ List.range 1, ThresholdAt 20 (59+i) := by decide +kernel

theorem threshold_20_60 : ∀ i ∈ List.range 1, ThresholdAt 20 (60+i) := by decide +kernel

theorem threshold_20_61 : ∀ i ∈ List.range 1, ThresholdAt 20 (61+i) := by decide +kernel

theorem threshold_20_62 : ∀ i ∈ List.range 1, ThresholdAt 20 (62+i) := by decide +kernel

theorem threshold_20_63 : ∀ i ∈ List.range 1, ThresholdAt 20 (63+i) := by decide +kernel

theorem threshold_20_64 : ∀ i ∈ List.range 1, ThresholdAt 20 (64+i) := by decide +kernel

theorem threshold_20_65 : ∀ i ∈ List.range 1, ThresholdAt 20 (65+i) := by decide +kernel

theorem threshold_20_66 : ∀ i ∈ List.range 1, ThresholdAt 20 (66+i) := by decide +kernel

theorem threshold_20_67 : ∀ i ∈ List.range 1, ThresholdAt 20 (67+i) := by decide +kernel

theorem threshold_20_68 : ∀ i ∈ List.range 1, ThresholdAt 20 (68+i) := by decide +kernel

theorem threshold_20_69 : ∀ i ∈ List.range 1, ThresholdAt 20 (69+i) := by decide +kernel

theorem threshold_20_70 : ∀ i ∈ List.range 1, ThresholdAt 20 (70+i) := by decide +kernel

theorem threshold_20_71 : ∀ i ∈ List.range 1, ThresholdAt 20 (71+i) := by decide +kernel

theorem threshold_20_72 : ∀ i ∈ List.range 1, ThresholdAt 20 (72+i) := by decide +kernel

theorem threshold_20_73 : ∀ i ∈ List.range 1, ThresholdAt 20 (73+i) := by decide +kernel

theorem threshold_20_74 : ∀ i ∈ List.range 1, ThresholdAt 20 (74+i) := by decide +kernel

theorem threshold_20_75 : ∀ i ∈ List.range 1, ThresholdAt 20 (75+i) := by decide +kernel

theorem threshold_20_76 : ∀ i ∈ List.range 1, ThresholdAt 20 (76+i) := by decide +kernel

theorem threshold_20_77 : ∀ i ∈ List.range 1, ThresholdAt 20 (77+i) := by decide +kernel

theorem threshold_20_78 : ∀ i ∈ List.range 1, ThresholdAt 20 (78+i) := by decide +kernel

theorem threshold_20_79 : ∀ i ∈ List.range 1, ThresholdAt 20 (79+i) := by decide +kernel

theorem threshold_20_80 : ∀ i ∈ List.range 1, ThresholdAt 20 (80+i) := by decide +kernel

theorem threshold_20_81 : ∀ i ∈ List.range 1, ThresholdAt 20 (81+i) := by decide +kernel

theorem threshold_20_82 : ∀ i ∈ List.range 1, ThresholdAt 20 (82+i) := by decide +kernel

theorem threshold_20_83 : ∀ i ∈ List.range 1, ThresholdAt 20 (83+i) := by decide +kernel

theorem threshold_20_84 : ∀ i ∈ List.range 1, ThresholdAt 20 (84+i) := by decide +kernel

theorem threshold_20_85 : ∀ i ∈ List.range 1, ThresholdAt 20 (85+i) := by decide +kernel

theorem threshold_20_86 : ∀ i ∈ List.range 1, ThresholdAt 20 (86+i) := by decide +kernel

theorem threshold_20_87 : ∀ i ∈ List.range 1, ThresholdAt 20 (87+i) := by decide +kernel

theorem threshold_20_88 : ∀ i ∈ List.range 1, ThresholdAt 20 (88+i) := by decide +kernel

theorem threshold_20_89 : ∀ i ∈ List.range 1, ThresholdAt 20 (89+i) := by decide +kernel

theorem threshold_20_90 : ∀ i ∈ List.range 1, ThresholdAt 20 (90+i) := by decide +kernel

theorem threshold_20_91 : ∀ i ∈ List.range 1, ThresholdAt 20 (91+i) := by decide +kernel

theorem threshold_20_92 : ∀ i ∈ List.range 1, ThresholdAt 20 (92+i) := by decide +kernel

theorem threshold_20_93 : ∀ i ∈ List.range 1, ThresholdAt 20 (93+i) := by decide +kernel

theorem threshold_20_94 : ∀ i ∈ List.range 1, ThresholdAt 20 (94+i) := by decide +kernel

theorem threshold_20_95 : ∀ i ∈ List.range 1, ThresholdAt 20 (95+i) := by decide +kernel

theorem threshold_20_96 : ∀ i ∈ List.range 1, ThresholdAt 20 (96+i) := by decide +kernel

theorem threshold_20_97 : ∀ i ∈ List.range 1, ThresholdAt 20 (97+i) := by decide +kernel

theorem threshold_20_98 : ∀ i ∈ List.range 1, ThresholdAt 20 (98+i) := by decide +kernel

theorem threshold_20_99 : ∀ i ∈ List.range 1, ThresholdAt 20 (99+i) := by decide +kernel

theorem threshold_20_100 : ∀ i ∈ List.range 1, ThresholdAt 20 (100+i) := by decide +kernel

theorem threshold_20_101 : ∀ i ∈ List.range 1, ThresholdAt 20 (101+i) := by decide +kernel

theorem threshold_20_102 : ∀ i ∈ List.range 1, ThresholdAt 20 (102+i) := by decide +kernel

theorem threshold_20_103 : ∀ i ∈ List.range 1, ThresholdAt 20 (103+i) := by decide +kernel

theorem threshold_20_104 : ∀ i ∈ List.range 1, ThresholdAt 20 (104+i) := by decide +kernel

theorem threshold_20_105 : ∀ i ∈ List.range 1, ThresholdAt 20 (105+i) := by decide +kernel

theorem threshold_20_106 : ∀ i ∈ List.range 1, ThresholdAt 20 (106+i) := by decide +kernel

theorem threshold_20_107 : ∀ i ∈ List.range 1, ThresholdAt 20 (107+i) := by decide +kernel

theorem threshold_20_108 : ∀ i ∈ List.range 1, ThresholdAt 20 (108+i) := by decide +kernel

theorem threshold_20_109 : ∀ i ∈ List.range 1, ThresholdAt 20 (109+i) := by decide +kernel

theorem threshold_20_110 : ∀ i ∈ List.range 1, ThresholdAt 20 (110+i) := by decide +kernel

theorem threshold_20_111 : ∀ i ∈ List.range 1, ThresholdAt 20 (111+i) := by decide +kernel

theorem threshold_20_112 : ∀ i ∈ List.range 1, ThresholdAt 20 (112+i) := by decide +kernel

theorem threshold_20_113 : ∀ i ∈ List.range 1, ThresholdAt 20 (113+i) := by decide +kernel

theorem threshold_20_114 : ∀ i ∈ List.range 1, ThresholdAt 20 (114+i) := by decide +kernel

theorem threshold_20_115 : ∀ i ∈ List.range 1, ThresholdAt 20 (115+i) := by decide +kernel

theorem threshold_20_116 : ∀ i ∈ List.range 1, ThresholdAt 20 (116+i) := by decide +kernel

theorem threshold_20_117 : ∀ i ∈ List.range 1, ThresholdAt 20 (117+i) := by decide +kernel

theorem threshold_20_118 : ∀ i ∈ List.range 1, ThresholdAt 20 (118+i) := by decide +kernel

theorem threshold_20_119 : ∀ i ∈ List.range 1, ThresholdAt 20 (119+i) := by decide +kernel

theorem threshold_20_120 : ∀ i ∈ List.range 1, ThresholdAt 20 (120+i) := by decide +kernel

theorem threshold_20_121 : ∀ i ∈ List.range 1, ThresholdAt 20 (121+i) := by decide +kernel

theorem threshold_20_122 : ∀ i ∈ List.range 1, ThresholdAt 20 (122+i) := by decide +kernel

theorem threshold_20_123 : ∀ i ∈ List.range 1, ThresholdAt 20 (123+i) := by decide +kernel

theorem threshold_20_124 : ∀ i ∈ List.range 1, ThresholdAt 20 (124+i) := by decide +kernel

theorem threshold_20_125 : ∀ i ∈ List.range 1, ThresholdAt 20 (125+i) := by decide +kernel

theorem threshold_20_126 : ∀ i ∈ List.range 1, ThresholdAt 20 (126+i) := by decide +kernel

theorem threshold_20 (v : ℕ) (hv : v ∈ List.range 127) : ThresholdAt 20 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 20 v)
  have h := (join 0 63 64 (join 0 31 32 (join 0 15 16 (join 0 7 8 (join 0 3 4 (join 0 1 2 threshold_20_0 (join 1 1 1 threshold_20_1 threshold_20_2)) (join 3 2 2 (join 3 1 1 threshold_20_3 threshold_20_4) (join 5 1 1 threshold_20_5 threshold_20_6))) (join 7 4 4 (join 7 2 2 (join 7 1 1 threshold_20_7 threshold_20_8) (join 9 1 1 threshold_20_9 threshold_20_10)) (join 11 2 2 (join 11 1 1 threshold_20_11 threshold_20_12) (join 13 1 1 threshold_20_13 threshold_20_14)))) (join 15 8 8 (join 15 4 4 (join 15 2 2 (join 15 1 1 threshold_20_15 threshold_20_16) (join 17 1 1 threshold_20_17 threshold_20_18)) (join 19 2 2 (join 19 1 1 threshold_20_19 threshold_20_20) (join 21 1 1 threshold_20_21 threshold_20_22))) (join 23 4 4 (join 23 2 2 (join 23 1 1 threshold_20_23 threshold_20_24) (join 25 1 1 threshold_20_25 threshold_20_26)) (join 27 2 2 (join 27 1 1 threshold_20_27 threshold_20_28) (join 29 1 1 threshold_20_29 threshold_20_30))))) (join 31 16 16 (join 31 8 8 (join 31 4 4 (join 31 2 2 (join 31 1 1 threshold_20_31 threshold_20_32) (join 33 1 1 threshold_20_33 threshold_20_34)) (join 35 2 2 (join 35 1 1 threshold_20_35 threshold_20_36) (join 37 1 1 threshold_20_37 threshold_20_38))) (join 39 4 4 (join 39 2 2 (join 39 1 1 threshold_20_39 threshold_20_40) (join 41 1 1 threshold_20_41 threshold_20_42)) (join 43 2 2 (join 43 1 1 threshold_20_43 threshold_20_44) (join 45 1 1 threshold_20_45 threshold_20_46)))) (join 47 8 8 (join 47 4 4 (join 47 2 2 (join 47 1 1 threshold_20_47 threshold_20_48) (join 49 1 1 threshold_20_49 threshold_20_50)) (join 51 2 2 (join 51 1 1 threshold_20_51 threshold_20_52) (join 53 1 1 threshold_20_53 threshold_20_54))) (join 55 4 4 (join 55 2 2 (join 55 1 1 threshold_20_55 threshold_20_56) (join 57 1 1 threshold_20_57 threshold_20_58)) (join 59 2 2 (join 59 1 1 threshold_20_59 threshold_20_60) (join 61 1 1 threshold_20_61 threshold_20_62)))))) (join 63 32 32 (join 63 16 16 (join 63 8 8 (join 63 4 4 (join 63 2 2 (join 63 1 1 threshold_20_63 threshold_20_64) (join 65 1 1 threshold_20_65 threshold_20_66)) (join 67 2 2 (join 67 1 1 threshold_20_67 threshold_20_68) (join 69 1 1 threshold_20_69 threshold_20_70))) (join 71 4 4 (join 71 2 2 (join 71 1 1 threshold_20_71 threshold_20_72) (join 73 1 1 threshold_20_73 threshold_20_74)) (join 75 2 2 (join 75 1 1 threshold_20_75 threshold_20_76) (join 77 1 1 threshold_20_77 threshold_20_78)))) (join 79 8 8 (join 79 4 4 (join 79 2 2 (join 79 1 1 threshold_20_79 threshold_20_80) (join 81 1 1 threshold_20_81 threshold_20_82)) (join 83 2 2 (join 83 1 1 threshold_20_83 threshold_20_84) (join 85 1 1 threshold_20_85 threshold_20_86))) (join 87 4 4 (join 87 2 2 (join 87 1 1 threshold_20_87 threshold_20_88) (join 89 1 1 threshold_20_89 threshold_20_90)) (join 91 2 2 (join 91 1 1 threshold_20_91 threshold_20_92) (join 93 1 1 threshold_20_93 threshold_20_94))))) (join 95 16 16 (join 95 8 8 (join 95 4 4 (join 95 2 2 (join 95 1 1 threshold_20_95 threshold_20_96) (join 97 1 1 threshold_20_97 threshold_20_98)) (join 99 2 2 (join 99 1 1 threshold_20_99 threshold_20_100) (join 101 1 1 threshold_20_101 threshold_20_102))) (join 103 4 4 (join 103 2 2 (join 103 1 1 threshold_20_103 threshold_20_104) (join 105 1 1 threshold_20_105 threshold_20_106)) (join 107 2 2 (join 107 1 1 threshold_20_107 threshold_20_108) (join 109 1 1 threshold_20_109 threshold_20_110)))) (join 111 8 8 (join 111 4 4 (join 111 2 2 (join 111 1 1 threshold_20_111 threshold_20_112) (join 113 1 1 threshold_20_113 threshold_20_114)) (join 115 2 2 (join 115 1 1 threshold_20_115 threshold_20_116) (join 117 1 1 threshold_20_117 threshold_20_118))) (join 119 4 4 (join 119 2 2 (join 119 1 1 threshold_20_119 threshold_20_120) (join 121 1 1 threshold_20_121 threshold_20_122)) (join 123 2 2 (join 123 1 1 threshold_20_123 threshold_20_124) (join 125 1 1 threshold_20_125 threshold_20_126)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_20_0 : ∀ i ∈ List.range 4, LedgerAt 20 (0+i) := by decide +kernel

theorem ledger_20_4 : ∀ i ∈ List.range 4, LedgerAt 20 (4+i) := by decide +kernel

theorem ledger_20_8 : ∀ i ∈ List.range 4, LedgerAt 20 (8+i) := by decide +kernel

theorem ledger_20_12 : ∀ i ∈ List.range 4, LedgerAt 20 (12+i) := by decide +kernel

theorem ledger_20_16 : ∀ i ∈ List.range 4, LedgerAt 20 (16+i) := by decide +kernel

theorem ledger_20_20 : ∀ i ∈ List.range 4, LedgerAt 20 (20+i) := by decide +kernel

theorem ledger_20_24 : ∀ i ∈ List.range 4, LedgerAt 20 (24+i) := by decide +kernel

theorem ledger_20_28 : ∀ i ∈ List.range 4, LedgerAt 20 (28+i) := by decide +kernel

theorem ledger_20_32 : ∀ i ∈ List.range 4, LedgerAt 20 (32+i) := by decide +kernel

theorem ledger_20_36 : ∀ i ∈ List.range 4, LedgerAt 20 (36+i) := by decide +kernel

theorem ledger_20_40 : ∀ i ∈ List.range 4, LedgerAt 20 (40+i) := by decide +kernel

theorem ledger_20_44 : ∀ i ∈ List.range 4, LedgerAt 20 (44+i) := by decide +kernel

theorem ledger_20_48 : ∀ i ∈ List.range 4, LedgerAt 20 (48+i) := by decide +kernel

theorem ledger_20_52 : ∀ i ∈ List.range 4, LedgerAt 20 (52+i) := by decide +kernel

theorem ledger_20_56 : ∀ i ∈ List.range 4, LedgerAt 20 (56+i) := by decide +kernel

theorem ledger_20_60 : ∀ i ∈ List.range 4, LedgerAt 20 (60+i) := by decide +kernel

theorem ledger_20_64 : ∀ i ∈ List.range 4, LedgerAt 20 (64+i) := by decide +kernel

theorem ledger_20_68 : ∀ i ∈ List.range 4, LedgerAt 20 (68+i) := by decide +kernel

theorem ledger_20_72 : ∀ i ∈ List.range 4, LedgerAt 20 (72+i) := by decide +kernel

theorem ledger_20_76 : ∀ i ∈ List.range 4, LedgerAt 20 (76+i) := by decide +kernel

theorem ledger_20_80 : ∀ i ∈ List.range 4, LedgerAt 20 (80+i) := by decide +kernel

theorem ledger_20_84 : ∀ i ∈ List.range 4, LedgerAt 20 (84+i) := by decide +kernel

theorem ledger_20_88 : ∀ i ∈ List.range 4, LedgerAt 20 (88+i) := by decide +kernel

theorem ledger_20_92 : ∀ i ∈ List.range 4, LedgerAt 20 (92+i) := by decide +kernel

theorem ledger_20_96 : ∀ i ∈ List.range 4, LedgerAt 20 (96+i) := by decide +kernel

theorem ledger_20_100 : ∀ i ∈ List.range 4, LedgerAt 20 (100+i) := by decide +kernel

theorem ledger_20_104 : ∀ i ∈ List.range 4, LedgerAt 20 (104+i) := by decide +kernel

theorem ledger_20_108 : ∀ i ∈ List.range 4, LedgerAt 20 (108+i) := by decide +kernel

theorem ledger_20_112 : ∀ i ∈ List.range 4, LedgerAt 20 (112+i) := by decide +kernel

theorem ledger_20_116 : ∀ i ∈ List.range 4, LedgerAt 20 (116+i) := by decide +kernel

theorem ledger_20_120 : ∀ i ∈ List.range 4, LedgerAt 20 (120+i) := by decide +kernel

theorem ledger_20_124 : ∀ i ∈ List.range 3, LedgerAt 20 (124+i) := by decide +kernel

theorem ledger_20 (v : ℕ) (hv : v ∈ List.range 127) : LedgerAt 20 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 20 v)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_20_0 ledger_20_4) (join 8 4 4 ledger_20_8 ledger_20_12)) (join 16 8 8 (join 16 4 4 ledger_20_16 ledger_20_20) (join 24 4 4 ledger_20_24 ledger_20_28))) (join 32 16 16 (join 32 8 8 (join 32 4 4 ledger_20_32 ledger_20_36) (join 40 4 4 ledger_20_40 ledger_20_44)) (join 48 8 8 (join 48 4 4 ledger_20_48 ledger_20_52) (join 56 4 4 ledger_20_56 ledger_20_60)))) (join 64 32 31 (join 64 16 16 (join 64 8 8 (join 64 4 4 ledger_20_64 ledger_20_68) (join 72 4 4 ledger_20_72 ledger_20_76)) (join 80 8 8 (join 80 4 4 ledger_20_80 ledger_20_84) (join 88 4 4 ledger_20_88 ledger_20_92))) (join 96 16 15 (join 96 8 8 (join 96 4 4 ledger_20_96 ledger_20_100) (join 104 4 4 ledger_20_104 ledger_20_108)) (join 112 8 7 (join 112 4 4 ledger_20_112 ledger_20_116) (join 120 4 3 ledger_20_120 ledger_20_124)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
