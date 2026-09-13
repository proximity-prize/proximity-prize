import ProximityPrize.SubmissionLower.BoundaryTailCheckedR096807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_10_0 : ∀ i ∈ List.range 4, GeometryAt 10 (0+i) := by decide +kernel

theorem geometry_10_4 : ∀ i ∈ List.range 4, GeometryAt 10 (4+i) := by decide +kernel

theorem geometry_10_8 : ∀ i ∈ List.range 4, GeometryAt 10 (8+i) := by decide +kernel

theorem geometry_10_12 : ∀ i ∈ List.range 4, GeometryAt 10 (12+i) := by decide +kernel

theorem geometry_10_16 : ∀ i ∈ List.range 4, GeometryAt 10 (16+i) := by decide +kernel

theorem geometry_10_20 : ∀ i ∈ List.range 4, GeometryAt 10 (20+i) := by decide +kernel

theorem geometry_10_24 : ∀ i ∈ List.range 4, GeometryAt 10 (24+i) := by decide +kernel

theorem geometry_10_28 : ∀ i ∈ List.range 4, GeometryAt 10 (28+i) := by decide +kernel

theorem geometry_10_32 : ∀ i ∈ List.range 4, GeometryAt 10 (32+i) := by decide +kernel

theorem geometry_10_36 : ∀ i ∈ List.range 4, GeometryAt 10 (36+i) := by decide +kernel

theorem geometry_10_40 : ∀ i ∈ List.range 4, GeometryAt 10 (40+i) := by decide +kernel

theorem geometry_10_44 : ∀ i ∈ List.range 4, GeometryAt 10 (44+i) := by decide +kernel

theorem geometry_10_48 : ∀ i ∈ List.range 4, GeometryAt 10 (48+i) := by decide +kernel

theorem geometry_10_52 : ∀ i ∈ List.range 4, GeometryAt 10 (52+i) := by decide +kernel

theorem geometry_10_56 : ∀ i ∈ List.range 4, GeometryAt 10 (56+i) := by decide +kernel

theorem geometry_10_60 : ∀ i ∈ List.range 4, GeometryAt 10 (60+i) := by decide +kernel

theorem geometry_10_64 : ∀ i ∈ List.range 4, GeometryAt 10 (64+i) := by decide +kernel

theorem geometry_10_68 : ∀ i ∈ List.range 4, GeometryAt 10 (68+i) := by decide +kernel

theorem geometry_10_72 : ∀ i ∈ List.range 4, GeometryAt 10 (72+i) := by decide +kernel

theorem geometry_10_76 : ∀ i ∈ List.range 4, GeometryAt 10 (76+i) := by decide +kernel

theorem geometry_10_80 : ∀ i ∈ List.range 4, GeometryAt 10 (80+i) := by decide +kernel

theorem geometry_10_84 : ∀ i ∈ List.range 4, GeometryAt 10 (84+i) := by decide +kernel

theorem geometry_10_88 : ∀ i ∈ List.range 4, GeometryAt 10 (88+i) := by decide +kernel

theorem geometry_10_92 : ∀ i ∈ List.range 4, GeometryAt 10 (92+i) := by decide +kernel

theorem geometry_10_96 : ∀ i ∈ List.range 4, GeometryAt 10 (96+i) := by decide +kernel

theorem geometry_10_100 : ∀ i ∈ List.range 4, GeometryAt 10 (100+i) := by decide +kernel

theorem geometry_10_104 : ∀ i ∈ List.range 4, GeometryAt 10 (104+i) := by decide +kernel

theorem geometry_10_108 : ∀ i ∈ List.range 4, GeometryAt 10 (108+i) := by decide +kernel

theorem geometry_10_112 : ∀ i ∈ List.range 4, GeometryAt 10 (112+i) := by decide +kernel

theorem geometry_10_116 : ∀ i ∈ List.range 4, GeometryAt 10 (116+i) := by decide +kernel

theorem geometry_10_120 : ∀ i ∈ List.range 4, GeometryAt 10 (120+i) := by decide +kernel

theorem geometry_10_124 : ∀ i ∈ List.range 4, GeometryAt 10 (124+i) := by decide +kernel

theorem geometry_10_128 : ∀ i ∈ List.range 4, GeometryAt 10 (128+i) := by decide +kernel

theorem geometry_10_132 : ∀ i ∈ List.range 4, GeometryAt 10 (132+i) := by decide +kernel

theorem geometry_10_136 : ∀ i ∈ List.range 1, GeometryAt 10 (136+i) := by decide +kernel

theorem geometry_10 (v : ℕ) (hv : v ∈ List.range 137) : GeometryAt 10 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 10 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_10_0 geometry_10_4) (join 8 4 4 geometry_10_8 geometry_10_12)) (join 16 8 8 (join 16 4 4 geometry_10_16 geometry_10_20) (join 24 4 4 geometry_10_24 geometry_10_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 geometry_10_32 geometry_10_36) (join 40 4 4 geometry_10_40 geometry_10_44)) (join 48 8 12 (join 48 4 4 geometry_10_48 geometry_10_52) (join 56 4 8 geometry_10_56 (join 60 4 4 geometry_10_60 geometry_10_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 geometry_10_68 geometry_10_72) (join 76 4 4 geometry_10_76 geometry_10_80)) (join 84 8 12 (join 84 4 4 geometry_10_84 geometry_10_88) (join 92 4 8 geometry_10_92 (join 96 4 4 geometry_10_96 geometry_10_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 geometry_10_104 geometry_10_108) (join 112 4 4 geometry_10_112 geometry_10_116)) (join 120 8 9 (join 120 4 4 geometry_10_120 geometry_10_124) (join 128 4 5 geometry_10_128 (join 132 4 1 geometry_10_132 geometry_10_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_10_0 : ∀ i ∈ List.range 4, StrictAt 10 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (0+i)) 10 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_4 : ∀ i ∈ List.range 4, StrictAt 10 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (4+i)) 10 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_8 : ∀ i ∈ List.range 4, StrictAt 10 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (8+i)) 10 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_12 : ∀ i ∈ List.range 4, StrictAt 10 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (12+i)) 10 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_16 : ∀ i ∈ List.range 4, StrictAt 10 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (16+i)) 10 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_20 : ∀ i ∈ List.range 4, StrictAt 10 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (20+i)) 10 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_24 : ∀ i ∈ List.range 4, StrictAt 10 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (24+i)) 10 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_28 : ∀ i ∈ List.range 4, StrictAt 10 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (28+i)) 10 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_32 : ∀ i ∈ List.range 4, StrictAt 10 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (32+i)) 10 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_36 : ∀ i ∈ List.range 4, StrictAt 10 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (36+i)) 10 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_40 : ∀ i ∈ List.range 4, StrictAt 10 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (40+i)) 10 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_44 : ∀ i ∈ List.range 4, StrictAt 10 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (44+i)) 10 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_48 : ∀ i ∈ List.range 4, StrictAt 10 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (48+i)) 10 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_52 : ∀ i ∈ List.range 4, StrictAt 10 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (52+i)) 10 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_56 : ∀ i ∈ List.range 4, StrictAt 10 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (56+i)) 10 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_60 : ∀ i ∈ List.range 4, StrictAt 10 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (60+i)) 10 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_64 : ∀ i ∈ List.range 4, StrictAt 10 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (64+i)) 10 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_68 : ∀ i ∈ List.range 4, StrictAt 10 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (68+i)) 10 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_72 : ∀ i ∈ List.range 4, StrictAt 10 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (72+i)) 10 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_76 : ∀ i ∈ List.range 4, StrictAt 10 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (76+i)) 10 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_80 : ∀ i ∈ List.range 4, StrictAt 10 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (80+i)) 10 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_84 : ∀ i ∈ List.range 4, StrictAt 10 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (84+i)) 10 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_88 : ∀ i ∈ List.range 4, StrictAt 10 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (88+i)) 10 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_92 : ∀ i ∈ List.range 4, StrictAt 10 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (92+i)) 10 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_96 : ∀ i ∈ List.range 4, StrictAt 10 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (96+i)) 10 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_100 : ∀ i ∈ List.range 4, StrictAt 10 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (100+i)) 10 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_104 : ∀ i ∈ List.range 4, StrictAt 10 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (104+i)) 10 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_108 : ∀ i ∈ List.range 4, StrictAt 10 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (108+i)) 10 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_112 : ∀ i ∈ List.range 4, StrictAt 10 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (112+i)) 10 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_116 : ∀ i ∈ List.range 4, StrictAt 10 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (116+i)) 10 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_120 : ∀ i ∈ List.range 4, StrictAt 10 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (120+i)) 10 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_124 : ∀ i ∈ List.range 4, StrictAt 10 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (124+i)) 10 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_128 : ∀ i ∈ List.range 4, StrictAt 10 (128+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (128+i)) 10 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_132 : ∀ i ∈ List.range 4, StrictAt 10 (132+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (132+i)) 10 (132+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10_136 : ∀ i ∈ List.range 1, StrictAt 10 (136+i) := by
  have h : ∀ i ∈ List.range 1, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 10 (136+i)) 10 (136+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_10 (v : ℕ) (hv : v ∈ List.range 137) : StrictAt 10 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 10 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_10_0 strict_10_4) (join 8 4 4 strict_10_8 strict_10_12)) (join 16 8 8 (join 16 4 4 strict_10_16 strict_10_20) (join 24 4 4 strict_10_24 strict_10_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 strict_10_32 strict_10_36) (join 40 4 4 strict_10_40 strict_10_44)) (join 48 8 12 (join 48 4 4 strict_10_48 strict_10_52) (join 56 4 8 strict_10_56 (join 60 4 4 strict_10_60 strict_10_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 strict_10_68 strict_10_72) (join 76 4 4 strict_10_76 strict_10_80)) (join 84 8 12 (join 84 4 4 strict_10_84 strict_10_88) (join 92 4 8 strict_10_92 (join 96 4 4 strict_10_96 strict_10_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 strict_10_104 strict_10_108) (join 112 4 4 strict_10_112 strict_10_116)) (join 120 8 9 (join 120 4 4 strict_10_120 strict_10_124) (join 128 4 5 strict_10_128 (join 132 4 1 strict_10_132 strict_10_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_10_0 : ∀ i ∈ List.range 4, PhaseAt 10 (0+i) := by decide +kernel

theorem phase_10_4 : ∀ i ∈ List.range 4, PhaseAt 10 (4+i) := by decide +kernel

theorem phase_10_8 : ∀ i ∈ List.range 4, PhaseAt 10 (8+i) := by decide +kernel

theorem phase_10_12 : ∀ i ∈ List.range 4, PhaseAt 10 (12+i) := by decide +kernel

theorem phase_10_16 : ∀ i ∈ List.range 4, PhaseAt 10 (16+i) := by decide +kernel

theorem phase_10_20 : ∀ i ∈ List.range 4, PhaseAt 10 (20+i) := by decide +kernel

theorem phase_10_24 : ∀ i ∈ List.range 4, PhaseAt 10 (24+i) := by decide +kernel

theorem phase_10_28 : ∀ i ∈ List.range 4, PhaseAt 10 (28+i) := by decide +kernel

theorem phase_10_32 : ∀ i ∈ List.range 4, PhaseAt 10 (32+i) := by decide +kernel

theorem phase_10_36 : ∀ i ∈ List.range 4, PhaseAt 10 (36+i) := by decide +kernel

theorem phase_10_40 : ∀ i ∈ List.range 4, PhaseAt 10 (40+i) := by decide +kernel

theorem phase_10_44 : ∀ i ∈ List.range 4, PhaseAt 10 (44+i) := by decide +kernel

theorem phase_10_48 : ∀ i ∈ List.range 4, PhaseAt 10 (48+i) := by decide +kernel

theorem phase_10_52 : ∀ i ∈ List.range 4, PhaseAt 10 (52+i) := by decide +kernel

theorem phase_10_56 : ∀ i ∈ List.range 4, PhaseAt 10 (56+i) := by decide +kernel

theorem phase_10_60 : ∀ i ∈ List.range 4, PhaseAt 10 (60+i) := by decide +kernel

theorem phase_10_64 : ∀ i ∈ List.range 4, PhaseAt 10 (64+i) := by decide +kernel

theorem phase_10_68 : ∀ i ∈ List.range 4, PhaseAt 10 (68+i) := by decide +kernel

theorem phase_10_72 : ∀ i ∈ List.range 4, PhaseAt 10 (72+i) := by decide +kernel

theorem phase_10_76 : ∀ i ∈ List.range 4, PhaseAt 10 (76+i) := by decide +kernel

theorem phase_10_80 : ∀ i ∈ List.range 4, PhaseAt 10 (80+i) := by decide +kernel

theorem phase_10_84 : ∀ i ∈ List.range 4, PhaseAt 10 (84+i) := by decide +kernel

theorem phase_10_88 : ∀ i ∈ List.range 4, PhaseAt 10 (88+i) := by decide +kernel

theorem phase_10_92 : ∀ i ∈ List.range 4, PhaseAt 10 (92+i) := by decide +kernel

theorem phase_10_96 : ∀ i ∈ List.range 4, PhaseAt 10 (96+i) := by decide +kernel

theorem phase_10_100 : ∀ i ∈ List.range 4, PhaseAt 10 (100+i) := by decide +kernel

theorem phase_10_104 : ∀ i ∈ List.range 4, PhaseAt 10 (104+i) := by decide +kernel

theorem phase_10_108 : ∀ i ∈ List.range 4, PhaseAt 10 (108+i) := by decide +kernel

theorem phase_10_112 : ∀ i ∈ List.range 4, PhaseAt 10 (112+i) := by decide +kernel

theorem phase_10_116 : ∀ i ∈ List.range 4, PhaseAt 10 (116+i) := by decide +kernel

theorem phase_10_120 : ∀ i ∈ List.range 4, PhaseAt 10 (120+i) := by decide +kernel

theorem phase_10_124 : ∀ i ∈ List.range 4, PhaseAt 10 (124+i) := by decide +kernel

theorem phase_10_128 : ∀ i ∈ List.range 4, PhaseAt 10 (128+i) := by decide +kernel

theorem phase_10_132 : ∀ i ∈ List.range 4, PhaseAt 10 (132+i) := by decide +kernel

theorem phase_10_136 : ∀ i ∈ List.range 1, PhaseAt 10 (136+i) := by decide +kernel

theorem phase_10 (v : ℕ) (hv : v ∈ List.range 137) : PhaseAt 10 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 10 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_10_0 phase_10_4) (join 8 4 4 phase_10_8 phase_10_12)) (join 16 8 8 (join 16 4 4 phase_10_16 phase_10_20) (join 24 4 4 phase_10_24 phase_10_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_10_32 phase_10_36) (join 40 4 4 phase_10_40 phase_10_44)) (join 48 8 12 (join 48 4 4 phase_10_48 phase_10_52) (join 56 4 8 phase_10_56 (join 60 4 4 phase_10_60 phase_10_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 phase_10_68 phase_10_72) (join 76 4 4 phase_10_76 phase_10_80)) (join 84 8 12 (join 84 4 4 phase_10_84 phase_10_88) (join 92 4 8 phase_10_92 (join 96 4 4 phase_10_96 phase_10_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 phase_10_104 phase_10_108) (join 112 4 4 phase_10_112 phase_10_116)) (join 120 8 9 (join 120 4 4 phase_10_120 phase_10_124) (join 128 4 5 phase_10_128 (join 132 4 1 phase_10_132 phase_10_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_10_0 : ∀ i ∈ List.range 1, ThresholdAt 10 (0+i) := by decide +kernel

theorem threshold_10_1 : ∀ i ∈ List.range 1, ThresholdAt 10 (1+i) := by decide +kernel

theorem threshold_10_2 : ∀ i ∈ List.range 1, ThresholdAt 10 (2+i) := by decide +kernel

theorem threshold_10_3 : ∀ i ∈ List.range 1, ThresholdAt 10 (3+i) := by decide +kernel

theorem threshold_10_4 : ∀ i ∈ List.range 1, ThresholdAt 10 (4+i) := by decide +kernel

theorem threshold_10_5 : ∀ i ∈ List.range 1, ThresholdAt 10 (5+i) := by decide +kernel

theorem threshold_10_6 : ∀ i ∈ List.range 1, ThresholdAt 10 (6+i) := by decide +kernel

theorem threshold_10_7 : ∀ i ∈ List.range 1, ThresholdAt 10 (7+i) := by decide +kernel

theorem threshold_10_8 : ∀ i ∈ List.range 1, ThresholdAt 10 (8+i) := by decide +kernel

theorem threshold_10_9 : ∀ i ∈ List.range 1, ThresholdAt 10 (9+i) := by decide +kernel

theorem threshold_10_10 : ∀ i ∈ List.range 1, ThresholdAt 10 (10+i) := by decide +kernel

theorem threshold_10_11 : ∀ i ∈ List.range 1, ThresholdAt 10 (11+i) := by decide +kernel

theorem threshold_10_12 : ∀ i ∈ List.range 1, ThresholdAt 10 (12+i) := by decide +kernel

theorem threshold_10_13 : ∀ i ∈ List.range 1, ThresholdAt 10 (13+i) := by decide +kernel

theorem threshold_10_14 : ∀ i ∈ List.range 1, ThresholdAt 10 (14+i) := by decide +kernel

theorem threshold_10_15 : ∀ i ∈ List.range 1, ThresholdAt 10 (15+i) := by decide +kernel

theorem threshold_10_16 : ∀ i ∈ List.range 1, ThresholdAt 10 (16+i) := by decide +kernel

theorem threshold_10_17 : ∀ i ∈ List.range 1, ThresholdAt 10 (17+i) := by decide +kernel

theorem threshold_10_18 : ∀ i ∈ List.range 1, ThresholdAt 10 (18+i) := by decide +kernel

theorem threshold_10_19 : ∀ i ∈ List.range 1, ThresholdAt 10 (19+i) := by decide +kernel

theorem threshold_10_20 : ∀ i ∈ List.range 1, ThresholdAt 10 (20+i) := by decide +kernel

theorem threshold_10_21 : ∀ i ∈ List.range 1, ThresholdAt 10 (21+i) := by decide +kernel

theorem threshold_10_22 : ∀ i ∈ List.range 1, ThresholdAt 10 (22+i) := by decide +kernel

theorem threshold_10_23 : ∀ i ∈ List.range 1, ThresholdAt 10 (23+i) := by decide +kernel

theorem threshold_10_24 : ∀ i ∈ List.range 1, ThresholdAt 10 (24+i) := by decide +kernel

theorem threshold_10_25 : ∀ i ∈ List.range 1, ThresholdAt 10 (25+i) := by decide +kernel

theorem threshold_10_26 : ∀ i ∈ List.range 1, ThresholdAt 10 (26+i) := by decide +kernel

theorem threshold_10_27 : ∀ i ∈ List.range 1, ThresholdAt 10 (27+i) := by decide +kernel

theorem threshold_10_28 : ∀ i ∈ List.range 1, ThresholdAt 10 (28+i) := by decide +kernel

theorem threshold_10_29 : ∀ i ∈ List.range 1, ThresholdAt 10 (29+i) := by decide +kernel

theorem threshold_10_30 : ∀ i ∈ List.range 1, ThresholdAt 10 (30+i) := by decide +kernel

theorem threshold_10_31 : ∀ i ∈ List.range 1, ThresholdAt 10 (31+i) := by decide +kernel

theorem threshold_10_32 : ∀ i ∈ List.range 1, ThresholdAt 10 (32+i) := by decide +kernel

theorem threshold_10_33 : ∀ i ∈ List.range 1, ThresholdAt 10 (33+i) := by decide +kernel

theorem threshold_10_34 : ∀ i ∈ List.range 1, ThresholdAt 10 (34+i) := by decide +kernel

theorem threshold_10_35 : ∀ i ∈ List.range 1, ThresholdAt 10 (35+i) := by decide +kernel

theorem threshold_10_36 : ∀ i ∈ List.range 1, ThresholdAt 10 (36+i) := by decide +kernel

theorem threshold_10_37 : ∀ i ∈ List.range 1, ThresholdAt 10 (37+i) := by decide +kernel

theorem threshold_10_38 : ∀ i ∈ List.range 1, ThresholdAt 10 (38+i) := by decide +kernel

theorem threshold_10_39 : ∀ i ∈ List.range 1, ThresholdAt 10 (39+i) := by decide +kernel

theorem threshold_10_40 : ∀ i ∈ List.range 1, ThresholdAt 10 (40+i) := by decide +kernel

theorem threshold_10_41 : ∀ i ∈ List.range 1, ThresholdAt 10 (41+i) := by decide +kernel

theorem threshold_10_42 : ∀ i ∈ List.range 1, ThresholdAt 10 (42+i) := by decide +kernel

theorem threshold_10_43 : ∀ i ∈ List.range 1, ThresholdAt 10 (43+i) := by decide +kernel

theorem threshold_10_44 : ∀ i ∈ List.range 1, ThresholdAt 10 (44+i) := by decide +kernel

theorem threshold_10_45 : ∀ i ∈ List.range 1, ThresholdAt 10 (45+i) := by decide +kernel

theorem threshold_10_46 : ∀ i ∈ List.range 1, ThresholdAt 10 (46+i) := by decide +kernel

theorem threshold_10_47 : ∀ i ∈ List.range 1, ThresholdAt 10 (47+i) := by decide +kernel

theorem threshold_10_48 : ∀ i ∈ List.range 1, ThresholdAt 10 (48+i) := by decide +kernel

theorem threshold_10_49 : ∀ i ∈ List.range 1, ThresholdAt 10 (49+i) := by decide +kernel

theorem threshold_10_50 : ∀ i ∈ List.range 1, ThresholdAt 10 (50+i) := by decide +kernel

theorem threshold_10_51 : ∀ i ∈ List.range 1, ThresholdAt 10 (51+i) := by decide +kernel

theorem threshold_10_52 : ∀ i ∈ List.range 1, ThresholdAt 10 (52+i) := by decide +kernel

theorem threshold_10_53 : ∀ i ∈ List.range 1, ThresholdAt 10 (53+i) := by decide +kernel

theorem threshold_10_54 : ∀ i ∈ List.range 1, ThresholdAt 10 (54+i) := by decide +kernel

theorem threshold_10_55 : ∀ i ∈ List.range 1, ThresholdAt 10 (55+i) := by decide +kernel

theorem threshold_10_56 : ∀ i ∈ List.range 1, ThresholdAt 10 (56+i) := by decide +kernel

theorem threshold_10_57 : ∀ i ∈ List.range 1, ThresholdAt 10 (57+i) := by decide +kernel

theorem threshold_10_58 : ∀ i ∈ List.range 1, ThresholdAt 10 (58+i) := by decide +kernel

theorem threshold_10_59 : ∀ i ∈ List.range 1, ThresholdAt 10 (59+i) := by decide +kernel

theorem threshold_10_60 : ∀ i ∈ List.range 1, ThresholdAt 10 (60+i) := by decide +kernel

theorem threshold_10_61 : ∀ i ∈ List.range 1, ThresholdAt 10 (61+i) := by decide +kernel

theorem threshold_10_62 : ∀ i ∈ List.range 1, ThresholdAt 10 (62+i) := by decide +kernel

theorem threshold_10_63 : ∀ i ∈ List.range 1, ThresholdAt 10 (63+i) := by decide +kernel

theorem threshold_10_64 : ∀ i ∈ List.range 1, ThresholdAt 10 (64+i) := by decide +kernel

theorem threshold_10_65 : ∀ i ∈ List.range 1, ThresholdAt 10 (65+i) := by decide +kernel

theorem threshold_10_66 : ∀ i ∈ List.range 1, ThresholdAt 10 (66+i) := by decide +kernel

theorem threshold_10_67 : ∀ i ∈ List.range 1, ThresholdAt 10 (67+i) := by decide +kernel

theorem threshold_10_68 : ∀ i ∈ List.range 1, ThresholdAt 10 (68+i) := by decide +kernel

theorem threshold_10_69 : ∀ i ∈ List.range 1, ThresholdAt 10 (69+i) := by decide +kernel

theorem threshold_10_70 : ∀ i ∈ List.range 1, ThresholdAt 10 (70+i) := by decide +kernel

theorem threshold_10_71 : ∀ i ∈ List.range 1, ThresholdAt 10 (71+i) := by decide +kernel

theorem threshold_10_72 : ∀ i ∈ List.range 1, ThresholdAt 10 (72+i) := by decide +kernel

theorem threshold_10_73 : ∀ i ∈ List.range 1, ThresholdAt 10 (73+i) := by decide +kernel

theorem threshold_10_74 : ∀ i ∈ List.range 1, ThresholdAt 10 (74+i) := by decide +kernel

theorem threshold_10_75 : ∀ i ∈ List.range 1, ThresholdAt 10 (75+i) := by decide +kernel

theorem threshold_10_76 : ∀ i ∈ List.range 1, ThresholdAt 10 (76+i) := by decide +kernel

theorem threshold_10_77 : ∀ i ∈ List.range 1, ThresholdAt 10 (77+i) := by decide +kernel

theorem threshold_10_78 : ∀ i ∈ List.range 1, ThresholdAt 10 (78+i) := by decide +kernel

theorem threshold_10_79 : ∀ i ∈ List.range 1, ThresholdAt 10 (79+i) := by decide +kernel

theorem threshold_10_80 : ∀ i ∈ List.range 1, ThresholdAt 10 (80+i) := by decide +kernel

theorem threshold_10_81 : ∀ i ∈ List.range 1, ThresholdAt 10 (81+i) := by decide +kernel

theorem threshold_10_82 : ∀ i ∈ List.range 1, ThresholdAt 10 (82+i) := by decide +kernel

theorem threshold_10_83 : ∀ i ∈ List.range 1, ThresholdAt 10 (83+i) := by decide +kernel

theorem threshold_10_84 : ∀ i ∈ List.range 1, ThresholdAt 10 (84+i) := by decide +kernel

theorem threshold_10_85 : ∀ i ∈ List.range 1, ThresholdAt 10 (85+i) := by decide +kernel

theorem threshold_10_86 : ∀ i ∈ List.range 1, ThresholdAt 10 (86+i) := by decide +kernel

theorem threshold_10_87 : ∀ i ∈ List.range 1, ThresholdAt 10 (87+i) := by decide +kernel

theorem threshold_10_88 : ∀ i ∈ List.range 1, ThresholdAt 10 (88+i) := by decide +kernel

theorem threshold_10_89 : ∀ i ∈ List.range 1, ThresholdAt 10 (89+i) := by decide +kernel

theorem threshold_10_90 : ∀ i ∈ List.range 1, ThresholdAt 10 (90+i) := by decide +kernel

theorem threshold_10_91 : ∀ i ∈ List.range 1, ThresholdAt 10 (91+i) := by decide +kernel

theorem threshold_10_92 : ∀ i ∈ List.range 1, ThresholdAt 10 (92+i) := by decide +kernel

theorem threshold_10_93 : ∀ i ∈ List.range 1, ThresholdAt 10 (93+i) := by decide +kernel

theorem threshold_10_94 : ∀ i ∈ List.range 1, ThresholdAt 10 (94+i) := by decide +kernel

theorem threshold_10_95 : ∀ i ∈ List.range 1, ThresholdAt 10 (95+i) := by decide +kernel

theorem threshold_10_96 : ∀ i ∈ List.range 1, ThresholdAt 10 (96+i) := by decide +kernel

theorem threshold_10_97 : ∀ i ∈ List.range 1, ThresholdAt 10 (97+i) := by decide +kernel

theorem threshold_10_98 : ∀ i ∈ List.range 1, ThresholdAt 10 (98+i) := by decide +kernel

theorem threshold_10_99 : ∀ i ∈ List.range 1, ThresholdAt 10 (99+i) := by decide +kernel

theorem threshold_10_100 : ∀ i ∈ List.range 1, ThresholdAt 10 (100+i) := by decide +kernel

theorem threshold_10_101 : ∀ i ∈ List.range 1, ThresholdAt 10 (101+i) := by decide +kernel

theorem threshold_10_102 : ∀ i ∈ List.range 1, ThresholdAt 10 (102+i) := by decide +kernel

theorem threshold_10_103 : ∀ i ∈ List.range 1, ThresholdAt 10 (103+i) := by decide +kernel

theorem threshold_10_104 : ∀ i ∈ List.range 1, ThresholdAt 10 (104+i) := by decide +kernel

theorem threshold_10_105 : ∀ i ∈ List.range 1, ThresholdAt 10 (105+i) := by decide +kernel

theorem threshold_10_106 : ∀ i ∈ List.range 1, ThresholdAt 10 (106+i) := by decide +kernel

theorem threshold_10_107 : ∀ i ∈ List.range 1, ThresholdAt 10 (107+i) := by decide +kernel

theorem threshold_10_108 : ∀ i ∈ List.range 1, ThresholdAt 10 (108+i) := by decide +kernel

theorem threshold_10_109 : ∀ i ∈ List.range 1, ThresholdAt 10 (109+i) := by decide +kernel

theorem threshold_10_110 : ∀ i ∈ List.range 1, ThresholdAt 10 (110+i) := by decide +kernel

theorem threshold_10_111 : ∀ i ∈ List.range 1, ThresholdAt 10 (111+i) := by decide +kernel

theorem threshold_10_112 : ∀ i ∈ List.range 1, ThresholdAt 10 (112+i) := by decide +kernel

theorem threshold_10_113 : ∀ i ∈ List.range 1, ThresholdAt 10 (113+i) := by decide +kernel

theorem threshold_10_114 : ∀ i ∈ List.range 1, ThresholdAt 10 (114+i) := by decide +kernel

theorem threshold_10_115 : ∀ i ∈ List.range 1, ThresholdAt 10 (115+i) := by decide +kernel

theorem threshold_10_116 : ∀ i ∈ List.range 1, ThresholdAt 10 (116+i) := by decide +kernel

theorem threshold_10_117 : ∀ i ∈ List.range 1, ThresholdAt 10 (117+i) := by decide +kernel

theorem threshold_10_118 : ∀ i ∈ List.range 1, ThresholdAt 10 (118+i) := by decide +kernel

theorem threshold_10_119 : ∀ i ∈ List.range 1, ThresholdAt 10 (119+i) := by decide +kernel

theorem threshold_10_120 : ∀ i ∈ List.range 1, ThresholdAt 10 (120+i) := by decide +kernel

theorem threshold_10_121 : ∀ i ∈ List.range 1, ThresholdAt 10 (121+i) := by decide +kernel

theorem threshold_10_122 : ∀ i ∈ List.range 1, ThresholdAt 10 (122+i) := by decide +kernel

theorem threshold_10_123 : ∀ i ∈ List.range 1, ThresholdAt 10 (123+i) := by decide +kernel

theorem threshold_10_124 : ∀ i ∈ List.range 1, ThresholdAt 10 (124+i) := by decide +kernel

theorem threshold_10_125 : ∀ i ∈ List.range 1, ThresholdAt 10 (125+i) := by decide +kernel

theorem threshold_10_126 : ∀ i ∈ List.range 1, ThresholdAt 10 (126+i) := by decide +kernel

theorem threshold_10_127 : ∀ i ∈ List.range 1, ThresholdAt 10 (127+i) := by decide +kernel

theorem threshold_10_128 : ∀ i ∈ List.range 1, ThresholdAt 10 (128+i) := by decide +kernel

theorem threshold_10_129 : ∀ i ∈ List.range 1, ThresholdAt 10 (129+i) := by decide +kernel

theorem threshold_10_130 : ∀ i ∈ List.range 1, ThresholdAt 10 (130+i) := by decide +kernel

theorem threshold_10_131 : ∀ i ∈ List.range 1, ThresholdAt 10 (131+i) := by decide +kernel

theorem threshold_10_132 : ∀ i ∈ List.range 1, ThresholdAt 10 (132+i) := by decide +kernel

theorem threshold_10_133 : ∀ i ∈ List.range 1, ThresholdAt 10 (133+i) := by decide +kernel

theorem threshold_10_134 : ∀ i ∈ List.range 1, ThresholdAt 10 (134+i) := by decide +kernel

theorem threshold_10_135 : ∀ i ∈ List.range 1, ThresholdAt 10 (135+i) := by decide +kernel

theorem threshold_10_136 : ∀ i ∈ List.range 1, ThresholdAt 10 (136+i) := by decide +kernel

theorem threshold_10 (v : ℕ) (hv : v ∈ List.range 137) : ThresholdAt 10 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 10 v)
  have h := (join 0 68 69 (join 0 34 34 (join 0 17 17 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_10_0 threshold_10_1) (join 2 1 1 threshold_10_2 threshold_10_3)) (join 4 2 2 (join 4 1 1 threshold_10_4 threshold_10_5) (join 6 1 1 threshold_10_6 threshold_10_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_10_8 threshold_10_9) (join 10 1 1 threshold_10_10 threshold_10_11)) (join 12 2 3 (join 12 1 1 threshold_10_12 threshold_10_13) (join 14 1 2 threshold_10_14 (join 15 1 1 threshold_10_15 threshold_10_16))))) (join 17 8 9 (join 17 4 4 (join 17 2 2 (join 17 1 1 threshold_10_17 threshold_10_18) (join 19 1 1 threshold_10_19 threshold_10_20)) (join 21 2 2 (join 21 1 1 threshold_10_21 threshold_10_22) (join 23 1 1 threshold_10_23 threshold_10_24))) (join 25 4 5 (join 25 2 2 (join 25 1 1 threshold_10_25 threshold_10_26) (join 27 1 1 threshold_10_27 threshold_10_28)) (join 29 2 3 (join 29 1 1 threshold_10_29 threshold_10_30) (join 31 1 2 threshold_10_31 (join 32 1 1 threshold_10_32 threshold_10_33)))))) (join 34 17 17 (join 34 8 9 (join 34 4 4 (join 34 2 2 (join 34 1 1 threshold_10_34 threshold_10_35) (join 36 1 1 threshold_10_36 threshold_10_37)) (join 38 2 2 (join 38 1 1 threshold_10_38 threshold_10_39) (join 40 1 1 threshold_10_40 threshold_10_41))) (join 42 4 5 (join 42 2 2 (join 42 1 1 threshold_10_42 threshold_10_43) (join 44 1 1 threshold_10_44 threshold_10_45)) (join 46 2 3 (join 46 1 1 threshold_10_46 threshold_10_47) (join 48 1 2 threshold_10_48 (join 49 1 1 threshold_10_49 threshold_10_50))))) (join 51 8 9 (join 51 4 4 (join 51 2 2 (join 51 1 1 threshold_10_51 threshold_10_52) (join 53 1 1 threshold_10_53 threshold_10_54)) (join 55 2 2 (join 55 1 1 threshold_10_55 threshold_10_56) (join 57 1 1 threshold_10_57 threshold_10_58))) (join 59 4 5 (join 59 2 2 (join 59 1 1 threshold_10_59 threshold_10_60) (join 61 1 1 threshold_10_61 threshold_10_62)) (join 63 2 3 (join 63 1 1 threshold_10_63 threshold_10_64) (join 65 1 2 threshold_10_65 (join 66 1 1 threshold_10_66 threshold_10_67))))))) (join 68 34 35 (join 68 17 17 (join 68 8 9 (join 68 4 4 (join 68 2 2 (join 68 1 1 threshold_10_68 threshold_10_69) (join 70 1 1 threshold_10_70 threshold_10_71)) (join 72 2 2 (join 72 1 1 threshold_10_72 threshold_10_73) (join 74 1 1 threshold_10_74 threshold_10_75))) (join 76 4 5 (join 76 2 2 (join 76 1 1 threshold_10_76 threshold_10_77) (join 78 1 1 threshold_10_78 threshold_10_79)) (join 80 2 3 (join 80 1 1 threshold_10_80 threshold_10_81) (join 82 1 2 threshold_10_82 (join 83 1 1 threshold_10_83 threshold_10_84))))) (join 85 8 9 (join 85 4 4 (join 85 2 2 (join 85 1 1 threshold_10_85 threshold_10_86) (join 87 1 1 threshold_10_87 threshold_10_88)) (join 89 2 2 (join 89 1 1 threshold_10_89 threshold_10_90) (join 91 1 1 threshold_10_91 threshold_10_92))) (join 93 4 5 (join 93 2 2 (join 93 1 1 threshold_10_93 threshold_10_94) (join 95 1 1 threshold_10_95 threshold_10_96)) (join 97 2 3 (join 97 1 1 threshold_10_97 threshold_10_98) (join 99 1 2 threshold_10_99 (join 100 1 1 threshold_10_100 threshold_10_101)))))) (join 102 17 18 (join 102 8 9 (join 102 4 4 (join 102 2 2 (join 102 1 1 threshold_10_102 threshold_10_103) (join 104 1 1 threshold_10_104 threshold_10_105)) (join 106 2 2 (join 106 1 1 threshold_10_106 threshold_10_107) (join 108 1 1 threshold_10_108 threshold_10_109))) (join 110 4 5 (join 110 2 2 (join 110 1 1 threshold_10_110 threshold_10_111) (join 112 1 1 threshold_10_112 threshold_10_113)) (join 114 2 3 (join 114 1 1 threshold_10_114 threshold_10_115) (join 116 1 2 threshold_10_116 (join 117 1 1 threshold_10_117 threshold_10_118))))) (join 119 9 9 (join 119 4 5 (join 119 2 2 (join 119 1 1 threshold_10_119 threshold_10_120) (join 121 1 1 threshold_10_121 threshold_10_122)) (join 123 2 3 (join 123 1 1 threshold_10_123 threshold_10_124) (join 125 1 2 threshold_10_125 (join 126 1 1 threshold_10_126 threshold_10_127)))) (join 128 4 5 (join 128 2 2 (join 128 1 1 threshold_10_128 threshold_10_129) (join 130 1 1 threshold_10_130 threshold_10_131)) (join 132 2 3 (join 132 1 1 threshold_10_132 threshold_10_133) (join 134 1 2 threshold_10_134 (join 135 1 1 threshold_10_135 threshold_10_136))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_10_0 : ∀ i ∈ List.range 4, LedgerAt 10 (0+i) := by decide +kernel

theorem ledger_10_4 : ∀ i ∈ List.range 4, LedgerAt 10 (4+i) := by decide +kernel

theorem ledger_10_8 : ∀ i ∈ List.range 4, LedgerAt 10 (8+i) := by decide +kernel

theorem ledger_10_12 : ∀ i ∈ List.range 4, LedgerAt 10 (12+i) := by decide +kernel

theorem ledger_10_16 : ∀ i ∈ List.range 4, LedgerAt 10 (16+i) := by decide +kernel

theorem ledger_10_20 : ∀ i ∈ List.range 4, LedgerAt 10 (20+i) := by decide +kernel

theorem ledger_10_24 : ∀ i ∈ List.range 4, LedgerAt 10 (24+i) := by decide +kernel

theorem ledger_10_28 : ∀ i ∈ List.range 4, LedgerAt 10 (28+i) := by decide +kernel

theorem ledger_10_32 : ∀ i ∈ List.range 4, LedgerAt 10 (32+i) := by decide +kernel

theorem ledger_10_36 : ∀ i ∈ List.range 4, LedgerAt 10 (36+i) := by decide +kernel

theorem ledger_10_40 : ∀ i ∈ List.range 4, LedgerAt 10 (40+i) := by decide +kernel

theorem ledger_10_44 : ∀ i ∈ List.range 4, LedgerAt 10 (44+i) := by decide +kernel

theorem ledger_10_48 : ∀ i ∈ List.range 4, LedgerAt 10 (48+i) := by decide +kernel

theorem ledger_10_52 : ∀ i ∈ List.range 4, LedgerAt 10 (52+i) := by decide +kernel

theorem ledger_10_56 : ∀ i ∈ List.range 4, LedgerAt 10 (56+i) := by decide +kernel

theorem ledger_10_60 : ∀ i ∈ List.range 4, LedgerAt 10 (60+i) := by decide +kernel

theorem ledger_10_64 : ∀ i ∈ List.range 4, LedgerAt 10 (64+i) := by decide +kernel

theorem ledger_10_68 : ∀ i ∈ List.range 4, LedgerAt 10 (68+i) := by decide +kernel

theorem ledger_10_72 : ∀ i ∈ List.range 4, LedgerAt 10 (72+i) := by decide +kernel

theorem ledger_10_76 : ∀ i ∈ List.range 4, LedgerAt 10 (76+i) := by decide +kernel

theorem ledger_10_80 : ∀ i ∈ List.range 4, LedgerAt 10 (80+i) := by decide +kernel

theorem ledger_10_84 : ∀ i ∈ List.range 4, LedgerAt 10 (84+i) := by decide +kernel

theorem ledger_10_88 : ∀ i ∈ List.range 4, LedgerAt 10 (88+i) := by decide +kernel

theorem ledger_10_92 : ∀ i ∈ List.range 4, LedgerAt 10 (92+i) := by decide +kernel

theorem ledger_10_96 : ∀ i ∈ List.range 4, LedgerAt 10 (96+i) := by decide +kernel

theorem ledger_10_100 : ∀ i ∈ List.range 4, LedgerAt 10 (100+i) := by decide +kernel

theorem ledger_10_104 : ∀ i ∈ List.range 4, LedgerAt 10 (104+i) := by decide +kernel

theorem ledger_10_108 : ∀ i ∈ List.range 4, LedgerAt 10 (108+i) := by decide +kernel

theorem ledger_10_112 : ∀ i ∈ List.range 4, LedgerAt 10 (112+i) := by decide +kernel

theorem ledger_10_116 : ∀ i ∈ List.range 4, LedgerAt 10 (116+i) := by decide +kernel

theorem ledger_10_120 : ∀ i ∈ List.range 4, LedgerAt 10 (120+i) := by decide +kernel

theorem ledger_10_124 : ∀ i ∈ List.range 4, LedgerAt 10 (124+i) := by decide +kernel

theorem ledger_10_128 : ∀ i ∈ List.range 4, LedgerAt 10 (128+i) := by decide +kernel

theorem ledger_10_132 : ∀ i ∈ List.range 4, LedgerAt 10 (132+i) := by decide +kernel

theorem ledger_10_136 : ∀ i ∈ List.range 1, LedgerAt 10 (136+i) := by decide +kernel

theorem ledger_10 (v : ℕ) (hv : v ∈ List.range 137) : LedgerAt 10 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 10 v)
  have h := (join 0 68 69 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_10_0 ledger_10_4) (join 8 4 4 ledger_10_8 ledger_10_12)) (join 16 8 8 (join 16 4 4 ledger_10_16 ledger_10_20) (join 24 4 4 ledger_10_24 ledger_10_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_10_32 ledger_10_36) (join 40 4 4 ledger_10_40 ledger_10_44)) (join 48 8 12 (join 48 4 4 ledger_10_48 ledger_10_52) (join 56 4 8 ledger_10_56 (join 60 4 4 ledger_10_60 ledger_10_64))))) (join 68 36 33 (join 68 16 20 (join 68 8 8 (join 68 4 4 ledger_10_68 ledger_10_72) (join 76 4 4 ledger_10_76 ledger_10_80)) (join 84 8 12 (join 84 4 4 ledger_10_84 ledger_10_88) (join 92 4 8 ledger_10_92 (join 96 4 4 ledger_10_96 ledger_10_100)))) (join 104 16 17 (join 104 8 8 (join 104 4 4 ledger_10_104 ledger_10_108) (join 112 4 4 ledger_10_112 ledger_10_116)) (join 120 8 9 (join 120 4 4 ledger_10_120 ledger_10_124) (join 128 4 5 ledger_10_128 (join 132 4 1 ledger_10_132 ledger_10_136))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
