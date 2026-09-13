import ProximityPrize.SubmissionLower.BoundaryTailCheckedR086807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_9_0 : ∀ i ∈ List.range 4, GeometryAt 9 (0+i) := by decide +kernel

theorem geometry_9_4 : ∀ i ∈ List.range 4, GeometryAt 9 (4+i) := by decide +kernel

theorem geometry_9_8 : ∀ i ∈ List.range 4, GeometryAt 9 (8+i) := by decide +kernel

theorem geometry_9_12 : ∀ i ∈ List.range 4, GeometryAt 9 (12+i) := by decide +kernel

theorem geometry_9_16 : ∀ i ∈ List.range 4, GeometryAt 9 (16+i) := by decide +kernel

theorem geometry_9_20 : ∀ i ∈ List.range 4, GeometryAt 9 (20+i) := by decide +kernel

theorem geometry_9_24 : ∀ i ∈ List.range 4, GeometryAt 9 (24+i) := by decide +kernel

theorem geometry_9_28 : ∀ i ∈ List.range 4, GeometryAt 9 (28+i) := by decide +kernel

theorem geometry_9_32 : ∀ i ∈ List.range 4, GeometryAt 9 (32+i) := by decide +kernel

theorem geometry_9_36 : ∀ i ∈ List.range 4, GeometryAt 9 (36+i) := by decide +kernel

theorem geometry_9_40 : ∀ i ∈ List.range 4, GeometryAt 9 (40+i) := by decide +kernel

theorem geometry_9_44 : ∀ i ∈ List.range 4, GeometryAt 9 (44+i) := by decide +kernel

theorem geometry_9_48 : ∀ i ∈ List.range 4, GeometryAt 9 (48+i) := by decide +kernel

theorem geometry_9_52 : ∀ i ∈ List.range 4, GeometryAt 9 (52+i) := by decide +kernel

theorem geometry_9_56 : ∀ i ∈ List.range 4, GeometryAt 9 (56+i) := by decide +kernel

theorem geometry_9_60 : ∀ i ∈ List.range 4, GeometryAt 9 (60+i) := by decide +kernel

theorem geometry_9_64 : ∀ i ∈ List.range 4, GeometryAt 9 (64+i) := by decide +kernel

theorem geometry_9_68 : ∀ i ∈ List.range 4, GeometryAt 9 (68+i) := by decide +kernel

theorem geometry_9_72 : ∀ i ∈ List.range 4, GeometryAt 9 (72+i) := by decide +kernel

theorem geometry_9_76 : ∀ i ∈ List.range 4, GeometryAt 9 (76+i) := by decide +kernel

theorem geometry_9_80 : ∀ i ∈ List.range 4, GeometryAt 9 (80+i) := by decide +kernel

theorem geometry_9_84 : ∀ i ∈ List.range 4, GeometryAt 9 (84+i) := by decide +kernel

theorem geometry_9_88 : ∀ i ∈ List.range 4, GeometryAt 9 (88+i) := by decide +kernel

theorem geometry_9_92 : ∀ i ∈ List.range 4, GeometryAt 9 (92+i) := by decide +kernel

theorem geometry_9_96 : ∀ i ∈ List.range 4, GeometryAt 9 (96+i) := by decide +kernel

theorem geometry_9_100 : ∀ i ∈ List.range 4, GeometryAt 9 (100+i) := by decide +kernel

theorem geometry_9_104 : ∀ i ∈ List.range 4, GeometryAt 9 (104+i) := by decide +kernel

theorem geometry_9_108 : ∀ i ∈ List.range 4, GeometryAt 9 (108+i) := by decide +kernel

theorem geometry_9_112 : ∀ i ∈ List.range 4, GeometryAt 9 (112+i) := by decide +kernel

theorem geometry_9_116 : ∀ i ∈ List.range 4, GeometryAt 9 (116+i) := by decide +kernel

theorem geometry_9_120 : ∀ i ∈ List.range 4, GeometryAt 9 (120+i) := by decide +kernel

theorem geometry_9_124 : ∀ i ∈ List.range 4, GeometryAt 9 (124+i) := by decide +kernel

theorem geometry_9_128 : ∀ i ∈ List.range 4, GeometryAt 9 (128+i) := by decide +kernel

theorem geometry_9_132 : ∀ i ∈ List.range 4, GeometryAt 9 (132+i) := by decide +kernel

theorem geometry_9_136 : ∀ i ∈ List.range 2, GeometryAt 9 (136+i) := by decide +kernel

theorem geometry_9 (v : ℕ) (hv : v ∈ List.range 138) : GeometryAt 9 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 9 v)
  have h := (join 0 68 70 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 geometry_9_0 geometry_9_4) (join 8 4 4 geometry_9_8 geometry_9_12)) (join 16 8 8 (join 16 4 4 geometry_9_16 geometry_9_20) (join 24 4 4 geometry_9_24 geometry_9_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 geometry_9_32 geometry_9_36) (join 40 4 4 geometry_9_40 geometry_9_44)) (join 48 8 12 (join 48 4 4 geometry_9_48 geometry_9_52) (join 56 4 8 geometry_9_56 (join 60 4 4 geometry_9_60 geometry_9_64))))) (join 68 36 34 (join 68 16 20 (join 68 8 8 (join 68 4 4 geometry_9_68 geometry_9_72) (join 76 4 4 geometry_9_76 geometry_9_80)) (join 84 8 12 (join 84 4 4 geometry_9_84 geometry_9_88) (join 92 4 8 geometry_9_92 (join 96 4 4 geometry_9_96 geometry_9_100)))) (join 104 16 18 (join 104 8 8 (join 104 4 4 geometry_9_104 geometry_9_108) (join 112 4 4 geometry_9_112 geometry_9_116)) (join 120 8 10 (join 120 4 4 geometry_9_120 geometry_9_124) (join 128 4 6 geometry_9_128 (join 132 4 2 geometry_9_132 geometry_9_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_9_0 : ∀ i ∈ List.range 4, StrictAt 9 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (0+i)) 9 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_4 : ∀ i ∈ List.range 4, StrictAt 9 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (4+i)) 9 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_8 : ∀ i ∈ List.range 4, StrictAt 9 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (8+i)) 9 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_12 : ∀ i ∈ List.range 4, StrictAt 9 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (12+i)) 9 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_16 : ∀ i ∈ List.range 4, StrictAt 9 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (16+i)) 9 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_20 : ∀ i ∈ List.range 4, StrictAt 9 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (20+i)) 9 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_24 : ∀ i ∈ List.range 4, StrictAt 9 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (24+i)) 9 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_28 : ∀ i ∈ List.range 4, StrictAt 9 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (28+i)) 9 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_32 : ∀ i ∈ List.range 4, StrictAt 9 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (32+i)) 9 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_36 : ∀ i ∈ List.range 4, StrictAt 9 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (36+i)) 9 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_40 : ∀ i ∈ List.range 4, StrictAt 9 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (40+i)) 9 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_44 : ∀ i ∈ List.range 4, StrictAt 9 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (44+i)) 9 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_48 : ∀ i ∈ List.range 4, StrictAt 9 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (48+i)) 9 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_52 : ∀ i ∈ List.range 4, StrictAt 9 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (52+i)) 9 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_56 : ∀ i ∈ List.range 4, StrictAt 9 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (56+i)) 9 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_60 : ∀ i ∈ List.range 4, StrictAt 9 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (60+i)) 9 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_64 : ∀ i ∈ List.range 4, StrictAt 9 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (64+i)) 9 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_68 : ∀ i ∈ List.range 4, StrictAt 9 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (68+i)) 9 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_72 : ∀ i ∈ List.range 4, StrictAt 9 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (72+i)) 9 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_76 : ∀ i ∈ List.range 4, StrictAt 9 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (76+i)) 9 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_80 : ∀ i ∈ List.range 4, StrictAt 9 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (80+i)) 9 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_84 : ∀ i ∈ List.range 4, StrictAt 9 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (84+i)) 9 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_88 : ∀ i ∈ List.range 4, StrictAt 9 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (88+i)) 9 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_92 : ∀ i ∈ List.range 4, StrictAt 9 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (92+i)) 9 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_96 : ∀ i ∈ List.range 4, StrictAt 9 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (96+i)) 9 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_100 : ∀ i ∈ List.range 4, StrictAt 9 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (100+i)) 9 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_104 : ∀ i ∈ List.range 4, StrictAt 9 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (104+i)) 9 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_108 : ∀ i ∈ List.range 4, StrictAt 9 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (108+i)) 9 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_112 : ∀ i ∈ List.range 4, StrictAt 9 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (112+i)) 9 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_116 : ∀ i ∈ List.range 4, StrictAt 9 (116+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (116+i)) 9 (116+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_120 : ∀ i ∈ List.range 4, StrictAt 9 (120+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (120+i)) 9 (120+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_124 : ∀ i ∈ List.range 4, StrictAt 9 (124+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (124+i)) 9 (124+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_128 : ∀ i ∈ List.range 4, StrictAt 9 (128+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (128+i)) 9 (128+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_132 : ∀ i ∈ List.range 4, StrictAt 9 (132+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (132+i)) 9 (132+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9_136 : ∀ i ∈ List.range 2, StrictAt 9 (136+i) := by
  have h : ∀ i ∈ List.range 2, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 9 (136+i)) 9 (136+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_9 (v : ℕ) (hv : v ∈ List.range 138) : StrictAt 9 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 9 v)
  have h := (join 0 68 70 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 strict_9_0 strict_9_4) (join 8 4 4 strict_9_8 strict_9_12)) (join 16 8 8 (join 16 4 4 strict_9_16 strict_9_20) (join 24 4 4 strict_9_24 strict_9_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 strict_9_32 strict_9_36) (join 40 4 4 strict_9_40 strict_9_44)) (join 48 8 12 (join 48 4 4 strict_9_48 strict_9_52) (join 56 4 8 strict_9_56 (join 60 4 4 strict_9_60 strict_9_64))))) (join 68 36 34 (join 68 16 20 (join 68 8 8 (join 68 4 4 strict_9_68 strict_9_72) (join 76 4 4 strict_9_76 strict_9_80)) (join 84 8 12 (join 84 4 4 strict_9_84 strict_9_88) (join 92 4 8 strict_9_92 (join 96 4 4 strict_9_96 strict_9_100)))) (join 104 16 18 (join 104 8 8 (join 104 4 4 strict_9_104 strict_9_108) (join 112 4 4 strict_9_112 strict_9_116)) (join 120 8 10 (join 120 4 4 strict_9_120 strict_9_124) (join 128 4 6 strict_9_128 (join 132 4 2 strict_9_132 strict_9_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_9_0 : ∀ i ∈ List.range 4, PhaseAt 9 (0+i) := by decide +kernel

theorem phase_9_4 : ∀ i ∈ List.range 4, PhaseAt 9 (4+i) := by decide +kernel

theorem phase_9_8 : ∀ i ∈ List.range 4, PhaseAt 9 (8+i) := by decide +kernel

theorem phase_9_12 : ∀ i ∈ List.range 4, PhaseAt 9 (12+i) := by decide +kernel

theorem phase_9_16 : ∀ i ∈ List.range 4, PhaseAt 9 (16+i) := by decide +kernel

theorem phase_9_20 : ∀ i ∈ List.range 4, PhaseAt 9 (20+i) := by decide +kernel

theorem phase_9_24 : ∀ i ∈ List.range 4, PhaseAt 9 (24+i) := by decide +kernel

theorem phase_9_28 : ∀ i ∈ List.range 4, PhaseAt 9 (28+i) := by decide +kernel

theorem phase_9_32 : ∀ i ∈ List.range 4, PhaseAt 9 (32+i) := by decide +kernel

theorem phase_9_36 : ∀ i ∈ List.range 4, PhaseAt 9 (36+i) := by decide +kernel

theorem phase_9_40 : ∀ i ∈ List.range 4, PhaseAt 9 (40+i) := by decide +kernel

theorem phase_9_44 : ∀ i ∈ List.range 4, PhaseAt 9 (44+i) := by decide +kernel

theorem phase_9_48 : ∀ i ∈ List.range 4, PhaseAt 9 (48+i) := by decide +kernel

theorem phase_9_52 : ∀ i ∈ List.range 4, PhaseAt 9 (52+i) := by decide +kernel

theorem phase_9_56 : ∀ i ∈ List.range 4, PhaseAt 9 (56+i) := by decide +kernel

theorem phase_9_60 : ∀ i ∈ List.range 4, PhaseAt 9 (60+i) := by decide +kernel

theorem phase_9_64 : ∀ i ∈ List.range 4, PhaseAt 9 (64+i) := by decide +kernel

theorem phase_9_68 : ∀ i ∈ List.range 4, PhaseAt 9 (68+i) := by decide +kernel

theorem phase_9_72 : ∀ i ∈ List.range 4, PhaseAt 9 (72+i) := by decide +kernel

theorem phase_9_76 : ∀ i ∈ List.range 4, PhaseAt 9 (76+i) := by decide +kernel

theorem phase_9_80 : ∀ i ∈ List.range 4, PhaseAt 9 (80+i) := by decide +kernel

theorem phase_9_84 : ∀ i ∈ List.range 4, PhaseAt 9 (84+i) := by decide +kernel

theorem phase_9_88 : ∀ i ∈ List.range 4, PhaseAt 9 (88+i) := by decide +kernel

theorem phase_9_92 : ∀ i ∈ List.range 4, PhaseAt 9 (92+i) := by decide +kernel

theorem phase_9_96 : ∀ i ∈ List.range 4, PhaseAt 9 (96+i) := by decide +kernel

theorem phase_9_100 : ∀ i ∈ List.range 4, PhaseAt 9 (100+i) := by decide +kernel

theorem phase_9_104 : ∀ i ∈ List.range 4, PhaseAt 9 (104+i) := by decide +kernel

theorem phase_9_108 : ∀ i ∈ List.range 4, PhaseAt 9 (108+i) := by decide +kernel

theorem phase_9_112 : ∀ i ∈ List.range 4, PhaseAt 9 (112+i) := by decide +kernel

theorem phase_9_116 : ∀ i ∈ List.range 4, PhaseAt 9 (116+i) := by decide +kernel

theorem phase_9_120 : ∀ i ∈ List.range 4, PhaseAt 9 (120+i) := by decide +kernel

theorem phase_9_124 : ∀ i ∈ List.range 4, PhaseAt 9 (124+i) := by decide +kernel

theorem phase_9_128 : ∀ i ∈ List.range 4, PhaseAt 9 (128+i) := by decide +kernel

theorem phase_9_132 : ∀ i ∈ List.range 4, PhaseAt 9 (132+i) := by decide +kernel

theorem phase_9_136 : ∀ i ∈ List.range 2, PhaseAt 9 (136+i) := by decide +kernel

theorem phase_9 (v : ℕ) (hv : v ∈ List.range 138) : PhaseAt 9 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 9 v)
  have h := (join 0 68 70 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 phase_9_0 phase_9_4) (join 8 4 4 phase_9_8 phase_9_12)) (join 16 8 8 (join 16 4 4 phase_9_16 phase_9_20) (join 24 4 4 phase_9_24 phase_9_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 phase_9_32 phase_9_36) (join 40 4 4 phase_9_40 phase_9_44)) (join 48 8 12 (join 48 4 4 phase_9_48 phase_9_52) (join 56 4 8 phase_9_56 (join 60 4 4 phase_9_60 phase_9_64))))) (join 68 36 34 (join 68 16 20 (join 68 8 8 (join 68 4 4 phase_9_68 phase_9_72) (join 76 4 4 phase_9_76 phase_9_80)) (join 84 8 12 (join 84 4 4 phase_9_84 phase_9_88) (join 92 4 8 phase_9_92 (join 96 4 4 phase_9_96 phase_9_100)))) (join 104 16 18 (join 104 8 8 (join 104 4 4 phase_9_104 phase_9_108) (join 112 4 4 phase_9_112 phase_9_116)) (join 120 8 10 (join 120 4 4 phase_9_120 phase_9_124) (join 128 4 6 phase_9_128 (join 132 4 2 phase_9_132 phase_9_136))))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_9_0 : ∀ i ∈ List.range 1, ThresholdAt 9 (0+i) := by decide +kernel

theorem threshold_9_1 : ∀ i ∈ List.range 1, ThresholdAt 9 (1+i) := by decide +kernel

theorem threshold_9_2 : ∀ i ∈ List.range 1, ThresholdAt 9 (2+i) := by decide +kernel

theorem threshold_9_3 : ∀ i ∈ List.range 1, ThresholdAt 9 (3+i) := by decide +kernel

theorem threshold_9_4 : ∀ i ∈ List.range 1, ThresholdAt 9 (4+i) := by decide +kernel

theorem threshold_9_5 : ∀ i ∈ List.range 1, ThresholdAt 9 (5+i) := by decide +kernel

theorem threshold_9_6 : ∀ i ∈ List.range 1, ThresholdAt 9 (6+i) := by decide +kernel

theorem threshold_9_7 : ∀ i ∈ List.range 1, ThresholdAt 9 (7+i) := by decide +kernel

theorem threshold_9_8 : ∀ i ∈ List.range 1, ThresholdAt 9 (8+i) := by decide +kernel

theorem threshold_9_9 : ∀ i ∈ List.range 1, ThresholdAt 9 (9+i) := by decide +kernel

theorem threshold_9_10 : ∀ i ∈ List.range 1, ThresholdAt 9 (10+i) := by decide +kernel

theorem threshold_9_11 : ∀ i ∈ List.range 1, ThresholdAt 9 (11+i) := by decide +kernel

theorem threshold_9_12 : ∀ i ∈ List.range 1, ThresholdAt 9 (12+i) := by decide +kernel

theorem threshold_9_13 : ∀ i ∈ List.range 1, ThresholdAt 9 (13+i) := by decide +kernel

theorem threshold_9_14 : ∀ i ∈ List.range 1, ThresholdAt 9 (14+i) := by decide +kernel

theorem threshold_9_15 : ∀ i ∈ List.range 1, ThresholdAt 9 (15+i) := by decide +kernel

theorem threshold_9_16 : ∀ i ∈ List.range 1, ThresholdAt 9 (16+i) := by decide +kernel

theorem threshold_9_17 : ∀ i ∈ List.range 1, ThresholdAt 9 (17+i) := by decide +kernel

theorem threshold_9_18 : ∀ i ∈ List.range 1, ThresholdAt 9 (18+i) := by decide +kernel

theorem threshold_9_19 : ∀ i ∈ List.range 1, ThresholdAt 9 (19+i) := by decide +kernel

theorem threshold_9_20 : ∀ i ∈ List.range 1, ThresholdAt 9 (20+i) := by decide +kernel

theorem threshold_9_21 : ∀ i ∈ List.range 1, ThresholdAt 9 (21+i) := by decide +kernel

theorem threshold_9_22 : ∀ i ∈ List.range 1, ThresholdAt 9 (22+i) := by decide +kernel

theorem threshold_9_23 : ∀ i ∈ List.range 1, ThresholdAt 9 (23+i) := by decide +kernel

theorem threshold_9_24 : ∀ i ∈ List.range 1, ThresholdAt 9 (24+i) := by decide +kernel

theorem threshold_9_25 : ∀ i ∈ List.range 1, ThresholdAt 9 (25+i) := by decide +kernel

theorem threshold_9_26 : ∀ i ∈ List.range 1, ThresholdAt 9 (26+i) := by decide +kernel

theorem threshold_9_27 : ∀ i ∈ List.range 1, ThresholdAt 9 (27+i) := by decide +kernel

theorem threshold_9_28 : ∀ i ∈ List.range 1, ThresholdAt 9 (28+i) := by decide +kernel

theorem threshold_9_29 : ∀ i ∈ List.range 1, ThresholdAt 9 (29+i) := by decide +kernel

theorem threshold_9_30 : ∀ i ∈ List.range 1, ThresholdAt 9 (30+i) := by decide +kernel

theorem threshold_9_31 : ∀ i ∈ List.range 1, ThresholdAt 9 (31+i) := by decide +kernel

theorem threshold_9_32 : ∀ i ∈ List.range 1, ThresholdAt 9 (32+i) := by decide +kernel

theorem threshold_9_33 : ∀ i ∈ List.range 1, ThresholdAt 9 (33+i) := by decide +kernel

theorem threshold_9_34 : ∀ i ∈ List.range 1, ThresholdAt 9 (34+i) := by decide +kernel

theorem threshold_9_35 : ∀ i ∈ List.range 1, ThresholdAt 9 (35+i) := by decide +kernel

theorem threshold_9_36 : ∀ i ∈ List.range 1, ThresholdAt 9 (36+i) := by decide +kernel

theorem threshold_9_37 : ∀ i ∈ List.range 1, ThresholdAt 9 (37+i) := by decide +kernel

theorem threshold_9_38 : ∀ i ∈ List.range 1, ThresholdAt 9 (38+i) := by decide +kernel

theorem threshold_9_39 : ∀ i ∈ List.range 1, ThresholdAt 9 (39+i) := by decide +kernel

theorem threshold_9_40 : ∀ i ∈ List.range 1, ThresholdAt 9 (40+i) := by decide +kernel

theorem threshold_9_41 : ∀ i ∈ List.range 1, ThresholdAt 9 (41+i) := by decide +kernel

theorem threshold_9_42 : ∀ i ∈ List.range 1, ThresholdAt 9 (42+i) := by decide +kernel

theorem threshold_9_43 : ∀ i ∈ List.range 1, ThresholdAt 9 (43+i) := by decide +kernel

theorem threshold_9_44 : ∀ i ∈ List.range 1, ThresholdAt 9 (44+i) := by decide +kernel

theorem threshold_9_45 : ∀ i ∈ List.range 1, ThresholdAt 9 (45+i) := by decide +kernel

theorem threshold_9_46 : ∀ i ∈ List.range 1, ThresholdAt 9 (46+i) := by decide +kernel

theorem threshold_9_47 : ∀ i ∈ List.range 1, ThresholdAt 9 (47+i) := by decide +kernel

theorem threshold_9_48 : ∀ i ∈ List.range 1, ThresholdAt 9 (48+i) := by decide +kernel

theorem threshold_9_49 : ∀ i ∈ List.range 1, ThresholdAt 9 (49+i) := by decide +kernel

theorem threshold_9_50 : ∀ i ∈ List.range 1, ThresholdAt 9 (50+i) := by decide +kernel

theorem threshold_9_51 : ∀ i ∈ List.range 1, ThresholdAt 9 (51+i) := by decide +kernel

theorem threshold_9_52 : ∀ i ∈ List.range 1, ThresholdAt 9 (52+i) := by decide +kernel

theorem threshold_9_53 : ∀ i ∈ List.range 1, ThresholdAt 9 (53+i) := by decide +kernel

theorem threshold_9_54 : ∀ i ∈ List.range 1, ThresholdAt 9 (54+i) := by decide +kernel

theorem threshold_9_55 : ∀ i ∈ List.range 1, ThresholdAt 9 (55+i) := by decide +kernel

theorem threshold_9_56 : ∀ i ∈ List.range 1, ThresholdAt 9 (56+i) := by decide +kernel

theorem threshold_9_57 : ∀ i ∈ List.range 1, ThresholdAt 9 (57+i) := by decide +kernel

theorem threshold_9_58 : ∀ i ∈ List.range 1, ThresholdAt 9 (58+i) := by decide +kernel

theorem threshold_9_59 : ∀ i ∈ List.range 1, ThresholdAt 9 (59+i) := by decide +kernel

theorem threshold_9_60 : ∀ i ∈ List.range 1, ThresholdAt 9 (60+i) := by decide +kernel

theorem threshold_9_61 : ∀ i ∈ List.range 1, ThresholdAt 9 (61+i) := by decide +kernel

theorem threshold_9_62 : ∀ i ∈ List.range 1, ThresholdAt 9 (62+i) := by decide +kernel

theorem threshold_9_63 : ∀ i ∈ List.range 1, ThresholdAt 9 (63+i) := by decide +kernel

theorem threshold_9_64 : ∀ i ∈ List.range 1, ThresholdAt 9 (64+i) := by decide +kernel

theorem threshold_9_65 : ∀ i ∈ List.range 1, ThresholdAt 9 (65+i) := by decide +kernel

theorem threshold_9_66 : ∀ i ∈ List.range 1, ThresholdAt 9 (66+i) := by decide +kernel

theorem threshold_9_67 : ∀ i ∈ List.range 1, ThresholdAt 9 (67+i) := by decide +kernel

theorem threshold_9_68 : ∀ i ∈ List.range 1, ThresholdAt 9 (68+i) := by decide +kernel

theorem threshold_9_69 : ∀ i ∈ List.range 1, ThresholdAt 9 (69+i) := by decide +kernel

theorem threshold_9_70 : ∀ i ∈ List.range 1, ThresholdAt 9 (70+i) := by decide +kernel

theorem threshold_9_71 : ∀ i ∈ List.range 1, ThresholdAt 9 (71+i) := by decide +kernel

theorem threshold_9_72 : ∀ i ∈ List.range 1, ThresholdAt 9 (72+i) := by decide +kernel

theorem threshold_9_73 : ∀ i ∈ List.range 1, ThresholdAt 9 (73+i) := by decide +kernel

theorem threshold_9_74 : ∀ i ∈ List.range 1, ThresholdAt 9 (74+i) := by decide +kernel

theorem threshold_9_75 : ∀ i ∈ List.range 1, ThresholdAt 9 (75+i) := by decide +kernel

theorem threshold_9_76 : ∀ i ∈ List.range 1, ThresholdAt 9 (76+i) := by decide +kernel

theorem threshold_9_77 : ∀ i ∈ List.range 1, ThresholdAt 9 (77+i) := by decide +kernel

theorem threshold_9_78 : ∀ i ∈ List.range 1, ThresholdAt 9 (78+i) := by decide +kernel

theorem threshold_9_79 : ∀ i ∈ List.range 1, ThresholdAt 9 (79+i) := by decide +kernel

theorem threshold_9_80 : ∀ i ∈ List.range 1, ThresholdAt 9 (80+i) := by decide +kernel

theorem threshold_9_81 : ∀ i ∈ List.range 1, ThresholdAt 9 (81+i) := by decide +kernel

theorem threshold_9_82 : ∀ i ∈ List.range 1, ThresholdAt 9 (82+i) := by decide +kernel

theorem threshold_9_83 : ∀ i ∈ List.range 1, ThresholdAt 9 (83+i) := by decide +kernel

theorem threshold_9_84 : ∀ i ∈ List.range 1, ThresholdAt 9 (84+i) := by decide +kernel

theorem threshold_9_85 : ∀ i ∈ List.range 1, ThresholdAt 9 (85+i) := by decide +kernel

theorem threshold_9_86 : ∀ i ∈ List.range 1, ThresholdAt 9 (86+i) := by decide +kernel

theorem threshold_9_87 : ∀ i ∈ List.range 1, ThresholdAt 9 (87+i) := by decide +kernel

theorem threshold_9_88 : ∀ i ∈ List.range 1, ThresholdAt 9 (88+i) := by decide +kernel

theorem threshold_9_89 : ∀ i ∈ List.range 1, ThresholdAt 9 (89+i) := by decide +kernel

theorem threshold_9_90 : ∀ i ∈ List.range 1, ThresholdAt 9 (90+i) := by decide +kernel

theorem threshold_9_91 : ∀ i ∈ List.range 1, ThresholdAt 9 (91+i) := by decide +kernel

theorem threshold_9_92 : ∀ i ∈ List.range 1, ThresholdAt 9 (92+i) := by decide +kernel

theorem threshold_9_93 : ∀ i ∈ List.range 1, ThresholdAt 9 (93+i) := by decide +kernel

theorem threshold_9_94 : ∀ i ∈ List.range 1, ThresholdAt 9 (94+i) := by decide +kernel

theorem threshold_9_95 : ∀ i ∈ List.range 1, ThresholdAt 9 (95+i) := by decide +kernel

theorem threshold_9_96 : ∀ i ∈ List.range 1, ThresholdAt 9 (96+i) := by decide +kernel

theorem threshold_9_97 : ∀ i ∈ List.range 1, ThresholdAt 9 (97+i) := by decide +kernel

theorem threshold_9_98 : ∀ i ∈ List.range 1, ThresholdAt 9 (98+i) := by decide +kernel

theorem threshold_9_99 : ∀ i ∈ List.range 1, ThresholdAt 9 (99+i) := by decide +kernel

theorem threshold_9_100 : ∀ i ∈ List.range 1, ThresholdAt 9 (100+i) := by decide +kernel

theorem threshold_9_101 : ∀ i ∈ List.range 1, ThresholdAt 9 (101+i) := by decide +kernel

theorem threshold_9_102 : ∀ i ∈ List.range 1, ThresholdAt 9 (102+i) := by decide +kernel

theorem threshold_9_103 : ∀ i ∈ List.range 1, ThresholdAt 9 (103+i) := by decide +kernel

theorem threshold_9_104 : ∀ i ∈ List.range 1, ThresholdAt 9 (104+i) := by decide +kernel

theorem threshold_9_105 : ∀ i ∈ List.range 1, ThresholdAt 9 (105+i) := by decide +kernel

theorem threshold_9_106 : ∀ i ∈ List.range 1, ThresholdAt 9 (106+i) := by decide +kernel

theorem threshold_9_107 : ∀ i ∈ List.range 1, ThresholdAt 9 (107+i) := by decide +kernel

theorem threshold_9_108 : ∀ i ∈ List.range 1, ThresholdAt 9 (108+i) := by decide +kernel

theorem threshold_9_109 : ∀ i ∈ List.range 1, ThresholdAt 9 (109+i) := by decide +kernel

theorem threshold_9_110 : ∀ i ∈ List.range 1, ThresholdAt 9 (110+i) := by decide +kernel

theorem threshold_9_111 : ∀ i ∈ List.range 1, ThresholdAt 9 (111+i) := by decide +kernel

theorem threshold_9_112 : ∀ i ∈ List.range 1, ThresholdAt 9 (112+i) := by decide +kernel

theorem threshold_9_113 : ∀ i ∈ List.range 1, ThresholdAt 9 (113+i) := by decide +kernel

theorem threshold_9_114 : ∀ i ∈ List.range 1, ThresholdAt 9 (114+i) := by decide +kernel

theorem threshold_9_115 : ∀ i ∈ List.range 1, ThresholdAt 9 (115+i) := by decide +kernel

theorem threshold_9_116 : ∀ i ∈ List.range 1, ThresholdAt 9 (116+i) := by decide +kernel

theorem threshold_9_117 : ∀ i ∈ List.range 1, ThresholdAt 9 (117+i) := by decide +kernel

theorem threshold_9_118 : ∀ i ∈ List.range 1, ThresholdAt 9 (118+i) := by decide +kernel

theorem threshold_9_119 : ∀ i ∈ List.range 1, ThresholdAt 9 (119+i) := by decide +kernel

theorem threshold_9_120 : ∀ i ∈ List.range 1, ThresholdAt 9 (120+i) := by decide +kernel

theorem threshold_9_121 : ∀ i ∈ List.range 1, ThresholdAt 9 (121+i) := by decide +kernel

theorem threshold_9_122 : ∀ i ∈ List.range 1, ThresholdAt 9 (122+i) := by decide +kernel

theorem threshold_9_123 : ∀ i ∈ List.range 1, ThresholdAt 9 (123+i) := by decide +kernel

theorem threshold_9_124 : ∀ i ∈ List.range 1, ThresholdAt 9 (124+i) := by decide +kernel

theorem threshold_9_125 : ∀ i ∈ List.range 1, ThresholdAt 9 (125+i) := by decide +kernel

theorem threshold_9_126 : ∀ i ∈ List.range 1, ThresholdAt 9 (126+i) := by decide +kernel

theorem threshold_9_127 : ∀ i ∈ List.range 1, ThresholdAt 9 (127+i) := by decide +kernel

theorem threshold_9_128 : ∀ i ∈ List.range 1, ThresholdAt 9 (128+i) := by decide +kernel

theorem threshold_9_129 : ∀ i ∈ List.range 1, ThresholdAt 9 (129+i) := by decide +kernel

theorem threshold_9_130 : ∀ i ∈ List.range 1, ThresholdAt 9 (130+i) := by decide +kernel

theorem threshold_9_131 : ∀ i ∈ List.range 1, ThresholdAt 9 (131+i) := by decide +kernel

theorem threshold_9_132 : ∀ i ∈ List.range 1, ThresholdAt 9 (132+i) := by decide +kernel

theorem threshold_9_133 : ∀ i ∈ List.range 1, ThresholdAt 9 (133+i) := by decide +kernel

theorem threshold_9_134 : ∀ i ∈ List.range 1, ThresholdAt 9 (134+i) := by decide +kernel

theorem threshold_9_135 : ∀ i ∈ List.range 1, ThresholdAt 9 (135+i) := by decide +kernel

theorem threshold_9_136 : ∀ i ∈ List.range 1, ThresholdAt 9 (136+i) := by decide +kernel

theorem threshold_9_137 : ∀ i ∈ List.range 1, ThresholdAt 9 (137+i) := by decide +kernel

theorem threshold_9 (v : ℕ) (hv : v ∈ List.range 138) : ThresholdAt 9 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 9 v)
  have h := (join 0 69 69 (join 0 34 35 (join 0 17 17 (join 0 8 9 (join 0 4 4 (join 0 2 2 (join 0 1 1 threshold_9_0 threshold_9_1) (join 2 1 1 threshold_9_2 threshold_9_3)) (join 4 2 2 (join 4 1 1 threshold_9_4 threshold_9_5) (join 6 1 1 threshold_9_6 threshold_9_7))) (join 8 4 5 (join 8 2 2 (join 8 1 1 threshold_9_8 threshold_9_9) (join 10 1 1 threshold_9_10 threshold_9_11)) (join 12 2 3 (join 12 1 1 threshold_9_12 threshold_9_13) (join 14 1 2 threshold_9_14 (join 15 1 1 threshold_9_15 threshold_9_16))))) (join 17 8 9 (join 17 4 4 (join 17 2 2 (join 17 1 1 threshold_9_17 threshold_9_18) (join 19 1 1 threshold_9_19 threshold_9_20)) (join 21 2 2 (join 21 1 1 threshold_9_21 threshold_9_22) (join 23 1 1 threshold_9_23 threshold_9_24))) (join 25 4 5 (join 25 2 2 (join 25 1 1 threshold_9_25 threshold_9_26) (join 27 1 1 threshold_9_27 threshold_9_28)) (join 29 2 3 (join 29 1 1 threshold_9_29 threshold_9_30) (join 31 1 2 threshold_9_31 (join 32 1 1 threshold_9_32 threshold_9_33)))))) (join 34 17 18 (join 34 8 9 (join 34 4 4 (join 34 2 2 (join 34 1 1 threshold_9_34 threshold_9_35) (join 36 1 1 threshold_9_36 threshold_9_37)) (join 38 2 2 (join 38 1 1 threshold_9_38 threshold_9_39) (join 40 1 1 threshold_9_40 threshold_9_41))) (join 42 4 5 (join 42 2 2 (join 42 1 1 threshold_9_42 threshold_9_43) (join 44 1 1 threshold_9_44 threshold_9_45)) (join 46 2 3 (join 46 1 1 threshold_9_46 threshold_9_47) (join 48 1 2 threshold_9_48 (join 49 1 1 threshold_9_49 threshold_9_50))))) (join 51 9 9 (join 51 4 5 (join 51 2 2 (join 51 1 1 threshold_9_51 threshold_9_52) (join 53 1 1 threshold_9_53 threshold_9_54)) (join 55 2 3 (join 55 1 1 threshold_9_55 threshold_9_56) (join 57 1 2 threshold_9_57 (join 58 1 1 threshold_9_58 threshold_9_59)))) (join 60 4 5 (join 60 2 2 (join 60 1 1 threshold_9_60 threshold_9_61) (join 62 1 1 threshold_9_62 threshold_9_63)) (join 64 2 3 (join 64 1 1 threshold_9_64 threshold_9_65) (join 66 1 2 threshold_9_66 (join 67 1 1 threshold_9_67 threshold_9_68))))))) (join 69 34 35 (join 69 17 17 (join 69 8 9 (join 69 4 4 (join 69 2 2 (join 69 1 1 threshold_9_69 threshold_9_70) (join 71 1 1 threshold_9_71 threshold_9_72)) (join 73 2 2 (join 73 1 1 threshold_9_73 threshold_9_74) (join 75 1 1 threshold_9_75 threshold_9_76))) (join 77 4 5 (join 77 2 2 (join 77 1 1 threshold_9_77 threshold_9_78) (join 79 1 1 threshold_9_79 threshold_9_80)) (join 81 2 3 (join 81 1 1 threshold_9_81 threshold_9_82) (join 83 1 2 threshold_9_83 (join 84 1 1 threshold_9_84 threshold_9_85))))) (join 86 8 9 (join 86 4 4 (join 86 2 2 (join 86 1 1 threshold_9_86 threshold_9_87) (join 88 1 1 threshold_9_88 threshold_9_89)) (join 90 2 2 (join 90 1 1 threshold_9_90 threshold_9_91) (join 92 1 1 threshold_9_92 threshold_9_93))) (join 94 4 5 (join 94 2 2 (join 94 1 1 threshold_9_94 threshold_9_95) (join 96 1 1 threshold_9_96 threshold_9_97)) (join 98 2 3 (join 98 1 1 threshold_9_98 threshold_9_99) (join 100 1 2 threshold_9_100 (join 101 1 1 threshold_9_101 threshold_9_102)))))) (join 103 17 18 (join 103 8 9 (join 103 4 4 (join 103 2 2 (join 103 1 1 threshold_9_103 threshold_9_104) (join 105 1 1 threshold_9_105 threshold_9_106)) (join 107 2 2 (join 107 1 1 threshold_9_107 threshold_9_108) (join 109 1 1 threshold_9_109 threshold_9_110))) (join 111 4 5 (join 111 2 2 (join 111 1 1 threshold_9_111 threshold_9_112) (join 113 1 1 threshold_9_113 threshold_9_114)) (join 115 2 3 (join 115 1 1 threshold_9_115 threshold_9_116) (join 117 1 2 threshold_9_117 (join 118 1 1 threshold_9_118 threshold_9_119))))) (join 120 9 9 (join 120 4 5 (join 120 2 2 (join 120 1 1 threshold_9_120 threshold_9_121) (join 122 1 1 threshold_9_122 threshold_9_123)) (join 124 2 3 (join 124 1 1 threshold_9_124 threshold_9_125) (join 126 1 2 threshold_9_126 (join 127 1 1 threshold_9_127 threshold_9_128)))) (join 129 4 5 (join 129 2 2 (join 129 1 1 threshold_9_129 threshold_9_130) (join 131 1 1 threshold_9_131 threshold_9_132)) (join 133 2 3 (join 133 1 1 threshold_9_133 threshold_9_134) (join 135 1 2 threshold_9_135 (join 136 1 1 threshold_9_136 threshold_9_137))))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_9_0 : ∀ i ∈ List.range 4, LedgerAt 9 (0+i) := by decide +kernel

theorem ledger_9_4 : ∀ i ∈ List.range 4, LedgerAt 9 (4+i) := by decide +kernel

theorem ledger_9_8 : ∀ i ∈ List.range 4, LedgerAt 9 (8+i) := by decide +kernel

theorem ledger_9_12 : ∀ i ∈ List.range 4, LedgerAt 9 (12+i) := by decide +kernel

theorem ledger_9_16 : ∀ i ∈ List.range 4, LedgerAt 9 (16+i) := by decide +kernel

theorem ledger_9_20 : ∀ i ∈ List.range 4, LedgerAt 9 (20+i) := by decide +kernel

theorem ledger_9_24 : ∀ i ∈ List.range 4, LedgerAt 9 (24+i) := by decide +kernel

theorem ledger_9_28 : ∀ i ∈ List.range 4, LedgerAt 9 (28+i) := by decide +kernel

theorem ledger_9_32 : ∀ i ∈ List.range 4, LedgerAt 9 (32+i) := by decide +kernel

theorem ledger_9_36 : ∀ i ∈ List.range 4, LedgerAt 9 (36+i) := by decide +kernel

theorem ledger_9_40 : ∀ i ∈ List.range 4, LedgerAt 9 (40+i) := by decide +kernel

theorem ledger_9_44 : ∀ i ∈ List.range 4, LedgerAt 9 (44+i) := by decide +kernel

theorem ledger_9_48 : ∀ i ∈ List.range 4, LedgerAt 9 (48+i) := by decide +kernel

theorem ledger_9_52 : ∀ i ∈ List.range 4, LedgerAt 9 (52+i) := by decide +kernel

theorem ledger_9_56 : ∀ i ∈ List.range 4, LedgerAt 9 (56+i) := by decide +kernel

theorem ledger_9_60 : ∀ i ∈ List.range 4, LedgerAt 9 (60+i) := by decide +kernel

theorem ledger_9_64 : ∀ i ∈ List.range 4, LedgerAt 9 (64+i) := by decide +kernel

theorem ledger_9_68 : ∀ i ∈ List.range 4, LedgerAt 9 (68+i) := by decide +kernel

theorem ledger_9_72 : ∀ i ∈ List.range 4, LedgerAt 9 (72+i) := by decide +kernel

theorem ledger_9_76 : ∀ i ∈ List.range 4, LedgerAt 9 (76+i) := by decide +kernel

theorem ledger_9_80 : ∀ i ∈ List.range 4, LedgerAt 9 (80+i) := by decide +kernel

theorem ledger_9_84 : ∀ i ∈ List.range 4, LedgerAt 9 (84+i) := by decide +kernel

theorem ledger_9_88 : ∀ i ∈ List.range 4, LedgerAt 9 (88+i) := by decide +kernel

theorem ledger_9_92 : ∀ i ∈ List.range 4, LedgerAt 9 (92+i) := by decide +kernel

theorem ledger_9_96 : ∀ i ∈ List.range 4, LedgerAt 9 (96+i) := by decide +kernel

theorem ledger_9_100 : ∀ i ∈ List.range 4, LedgerAt 9 (100+i) := by decide +kernel

theorem ledger_9_104 : ∀ i ∈ List.range 4, LedgerAt 9 (104+i) := by decide +kernel

theorem ledger_9_108 : ∀ i ∈ List.range 4, LedgerAt 9 (108+i) := by decide +kernel

theorem ledger_9_112 : ∀ i ∈ List.range 4, LedgerAt 9 (112+i) := by decide +kernel

theorem ledger_9_116 : ∀ i ∈ List.range 4, LedgerAt 9 (116+i) := by decide +kernel

theorem ledger_9_120 : ∀ i ∈ List.range 4, LedgerAt 9 (120+i) := by decide +kernel

theorem ledger_9_124 : ∀ i ∈ List.range 4, LedgerAt 9 (124+i) := by decide +kernel

theorem ledger_9_128 : ∀ i ∈ List.range 4, LedgerAt 9 (128+i) := by decide +kernel

theorem ledger_9_132 : ∀ i ∈ List.range 4, LedgerAt 9 (132+i) := by decide +kernel

theorem ledger_9_136 : ∀ i ∈ List.range 2, LedgerAt 9 (136+i) := by decide +kernel

theorem ledger_9 (v : ℕ) (hv : v ∈ List.range 138) : LedgerAt 9 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 9 v)
  have h := (join 0 68 70 (join 0 32 36 (join 0 16 16 (join 0 8 8 (join 0 4 4 ledger_9_0 ledger_9_4) (join 8 4 4 ledger_9_8 ledger_9_12)) (join 16 8 8 (join 16 4 4 ledger_9_16 ledger_9_20) (join 24 4 4 ledger_9_24 ledger_9_28))) (join 32 16 20 (join 32 8 8 (join 32 4 4 ledger_9_32 ledger_9_36) (join 40 4 4 ledger_9_40 ledger_9_44)) (join 48 8 12 (join 48 4 4 ledger_9_48 ledger_9_52) (join 56 4 8 ledger_9_56 (join 60 4 4 ledger_9_60 ledger_9_64))))) (join 68 36 34 (join 68 16 20 (join 68 8 8 (join 68 4 4 ledger_9_68 ledger_9_72) (join 76 4 4 ledger_9_76 ledger_9_80)) (join 84 8 12 (join 84 4 4 ledger_9_84 ledger_9_88) (join 92 4 8 ledger_9_92 (join 96 4 4 ledger_9_96 ledger_9_100)))) (join 104 16 18 (join 104 8 8 (join 104 4 4 ledger_9_104 ledger_9_108) (join 112 4 4 ledger_9_112 ledger_9_116)) (join 120 8 10 (join 120 4 4 ledger_9_120 ledger_9_124) (join 128 4 6 ledger_9_128 (join 132 4 2 ledger_9_132 ledger_9_136))))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
