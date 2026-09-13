import ProximityPrize.SubmissionLower.BoundaryTailCheckedR306807

namespace ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
open BoundaryTailFiniteChecks6807
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem geometry_31_0 : ∀ i ∈ List.range 4, GeometryAt 31 (0+i) := by decide +kernel

theorem geometry_31_4 : ∀ i ∈ List.range 4, GeometryAt 31 (4+i) := by decide +kernel

theorem geometry_31_8 : ∀ i ∈ List.range 4, GeometryAt 31 (8+i) := by decide +kernel

theorem geometry_31_12 : ∀ i ∈ List.range 4, GeometryAt 31 (12+i) := by decide +kernel

theorem geometry_31_16 : ∀ i ∈ List.range 4, GeometryAt 31 (16+i) := by decide +kernel

theorem geometry_31_20 : ∀ i ∈ List.range 4, GeometryAt 31 (20+i) := by decide +kernel

theorem geometry_31_24 : ∀ i ∈ List.range 4, GeometryAt 31 (24+i) := by decide +kernel

theorem geometry_31_28 : ∀ i ∈ List.range 4, GeometryAt 31 (28+i) := by decide +kernel

theorem geometry_31_32 : ∀ i ∈ List.range 4, GeometryAt 31 (32+i) := by decide +kernel

theorem geometry_31_36 : ∀ i ∈ List.range 4, GeometryAt 31 (36+i) := by decide +kernel

theorem geometry_31_40 : ∀ i ∈ List.range 4, GeometryAt 31 (40+i) := by decide +kernel

theorem geometry_31_44 : ∀ i ∈ List.range 4, GeometryAt 31 (44+i) := by decide +kernel

theorem geometry_31_48 : ∀ i ∈ List.range 4, GeometryAt 31 (48+i) := by decide +kernel

theorem geometry_31_52 : ∀ i ∈ List.range 4, GeometryAt 31 (52+i) := by decide +kernel

theorem geometry_31_56 : ∀ i ∈ List.range 4, GeometryAt 31 (56+i) := by decide +kernel

theorem geometry_31_60 : ∀ i ∈ List.range 4, GeometryAt 31 (60+i) := by decide +kernel

theorem geometry_31_64 : ∀ i ∈ List.range 4, GeometryAt 31 (64+i) := by decide +kernel

theorem geometry_31_68 : ∀ i ∈ List.range 4, GeometryAt 31 (68+i) := by decide +kernel

theorem geometry_31_72 : ∀ i ∈ List.range 4, GeometryAt 31 (72+i) := by decide +kernel

theorem geometry_31_76 : ∀ i ∈ List.range 4, GeometryAt 31 (76+i) := by decide +kernel

theorem geometry_31_80 : ∀ i ∈ List.range 4, GeometryAt 31 (80+i) := by decide +kernel

theorem geometry_31_84 : ∀ i ∈ List.range 4, GeometryAt 31 (84+i) := by decide +kernel

theorem geometry_31_88 : ∀ i ∈ List.range 4, GeometryAt 31 (88+i) := by decide +kernel

theorem geometry_31_92 : ∀ i ∈ List.range 4, GeometryAt 31 (92+i) := by decide +kernel

theorem geometry_31_96 : ∀ i ∈ List.range 4, GeometryAt 31 (96+i) := by decide +kernel

theorem geometry_31_100 : ∀ i ∈ List.range 4, GeometryAt 31 (100+i) := by decide +kernel

theorem geometry_31_104 : ∀ i ∈ List.range 4, GeometryAt 31 (104+i) := by decide +kernel

theorem geometry_31_108 : ∀ i ∈ List.range 4, GeometryAt 31 (108+i) := by decide +kernel

theorem geometry_31_112 : ∀ i ∈ List.range 4, GeometryAt 31 (112+i) := by decide +kernel

theorem geometry_31 (v : ℕ) (hv : v ∈ List.range 116) : GeometryAt 31 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => GeometryAt 31 v)
  have h := (join 0 56 60 (join 0 28 28 (join 0 12 16 (join 0 4 8 geometry_31_0 (join 4 4 4 geometry_31_4 geometry_31_8)) (join 12 8 8 (join 12 4 4 geometry_31_12 geometry_31_16) (join 20 4 4 geometry_31_20 geometry_31_24))) (join 28 12 16 (join 28 4 8 geometry_31_28 (join 32 4 4 geometry_31_32 geometry_31_36)) (join 40 8 8 (join 40 4 4 geometry_31_40 geometry_31_44) (join 48 4 4 geometry_31_48 geometry_31_52)))) (join 56 28 32 (join 56 12 16 (join 56 4 8 geometry_31_56 (join 60 4 4 geometry_31_60 geometry_31_64)) (join 68 8 8 (join 68 4 4 geometry_31_68 geometry_31_72) (join 76 4 4 geometry_31_76 geometry_31_80))) (join 84 16 16 (join 84 8 8 (join 84 4 4 geometry_31_84 geometry_31_88) (join 92 4 4 geometry_31_92 geometry_31_96)) (join 100 8 8 (join 100 4 4 geometry_31_100 geometry_31_104) (join 108 4 4 geometry_31_108 geometry_31_112)))))
  simpa only [Nat.zero_add] using h v hv

theorem strict_31_0 : ∀ i ∈ List.range 4, StrictAt 31 (0+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (0+i)) 31 (0+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_4 : ∀ i ∈ List.range 4, StrictAt 31 (4+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (4+i)) 31 (4+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_8 : ∀ i ∈ List.range 4, StrictAt 31 (8+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (8+i)) 31 (8+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_12 : ∀ i ∈ List.range 4, StrictAt 31 (12+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (12+i)) 31 (12+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_16 : ∀ i ∈ List.range 4, StrictAt 31 (16+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (16+i)) 31 (16+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_20 : ∀ i ∈ List.range 4, StrictAt 31 (20+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (20+i)) 31 (20+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_24 : ∀ i ∈ List.range 4, StrictAt 31 (24+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (24+i)) 31 (24+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_28 : ∀ i ∈ List.range 4, StrictAt 31 (28+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (28+i)) 31 (28+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_32 : ∀ i ∈ List.range 4, StrictAt 31 (32+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (32+i)) 31 (32+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_36 : ∀ i ∈ List.range 4, StrictAt 31 (36+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (36+i)) 31 (36+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_40 : ∀ i ∈ List.range 4, StrictAt 31 (40+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (40+i)) 31 (40+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_44 : ∀ i ∈ List.range 4, StrictAt 31 (44+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (44+i)) 31 (44+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_48 : ∀ i ∈ List.range 4, StrictAt 31 (48+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (48+i)) 31 (48+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_52 : ∀ i ∈ List.range 4, StrictAt 31 (52+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (52+i)) 31 (52+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_56 : ∀ i ∈ List.range 4, StrictAt 31 (56+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (56+i)) 31 (56+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_60 : ∀ i ∈ List.range 4, StrictAt 31 (60+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (60+i)) 31 (60+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_64 : ∀ i ∈ List.range 4, StrictAt 31 (64+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (64+i)) 31 (64+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_68 : ∀ i ∈ List.range 4, StrictAt 31 (68+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (68+i)) 31 (68+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_72 : ∀ i ∈ List.range 4, StrictAt 31 (72+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (72+i)) 31 (72+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_76 : ∀ i ∈ List.range 4, StrictAt 31 (76+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (76+i)) 31 (76+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_80 : ∀ i ∈ List.range 4, StrictAt 31 (80+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (80+i)) 31 (80+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_84 : ∀ i ∈ List.range 4, StrictAt 31 (84+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (84+i)) 31 (84+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_88 : ∀ i ∈ List.range 4, StrictAt 31 (88+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (88+i)) 31 (88+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_92 : ∀ i ∈ List.range 4, StrictAt 31 (92+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (92+i)) 31 (92+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_96 : ∀ i ∈ List.range 4, StrictAt 31 (96+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (96+i)) 31 (96+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_100 : ∀ i ∈ List.range 4, StrictAt 31 (100+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (100+i)) 31 (100+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_104 : ∀ i ∈ List.range 4, StrictAt 31 (104+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (104+i)) 31 (104+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_108 : ∀ i ∈ List.range 4, StrictAt 31 (108+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (108+i)) 31 (108+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31_112 : ∀ i ∈ List.range 4, StrictAt 31 (112+i) := by
  have h : ∀ i ∈ List.range 4, BoundaryTailConvexity6807.strictCornersBool
      (BoundaryTailBaseFastData6807.row 31 (112+i)) 31 (112+i) = true := by decide +kernel
  intro i hi
  exact BoundaryTailConvexity6807.strictCornersBool_sound _ _ _ (h i hi)

theorem strict_31 (v : ℕ) (hv : v ∈ List.range 116) : StrictAt 31 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => StrictAt 31 v)
  have h := (join 0 56 60 (join 0 28 28 (join 0 12 16 (join 0 4 8 strict_31_0 (join 4 4 4 strict_31_4 strict_31_8)) (join 12 8 8 (join 12 4 4 strict_31_12 strict_31_16) (join 20 4 4 strict_31_20 strict_31_24))) (join 28 12 16 (join 28 4 8 strict_31_28 (join 32 4 4 strict_31_32 strict_31_36)) (join 40 8 8 (join 40 4 4 strict_31_40 strict_31_44) (join 48 4 4 strict_31_48 strict_31_52)))) (join 56 28 32 (join 56 12 16 (join 56 4 8 strict_31_56 (join 60 4 4 strict_31_60 strict_31_64)) (join 68 8 8 (join 68 4 4 strict_31_68 strict_31_72) (join 76 4 4 strict_31_76 strict_31_80))) (join 84 16 16 (join 84 8 8 (join 84 4 4 strict_31_84 strict_31_88) (join 92 4 4 strict_31_92 strict_31_96)) (join 100 8 8 (join 100 4 4 strict_31_100 strict_31_104) (join 108 4 4 strict_31_108 strict_31_112)))))
  simpa only [Nat.zero_add] using h v hv

theorem phase_31_0 : ∀ i ∈ List.range 4, PhaseAt 31 (0+i) := by decide +kernel

theorem phase_31_4 : ∀ i ∈ List.range 4, PhaseAt 31 (4+i) := by decide +kernel

theorem phase_31_8 : ∀ i ∈ List.range 4, PhaseAt 31 (8+i) := by decide +kernel

theorem phase_31_12 : ∀ i ∈ List.range 4, PhaseAt 31 (12+i) := by decide +kernel

theorem phase_31_16 : ∀ i ∈ List.range 4, PhaseAt 31 (16+i) := by decide +kernel

theorem phase_31_20 : ∀ i ∈ List.range 4, PhaseAt 31 (20+i) := by decide +kernel

theorem phase_31_24 : ∀ i ∈ List.range 4, PhaseAt 31 (24+i) := by decide +kernel

theorem phase_31_28 : ∀ i ∈ List.range 4, PhaseAt 31 (28+i) := by decide +kernel

theorem phase_31_32 : ∀ i ∈ List.range 4, PhaseAt 31 (32+i) := by decide +kernel

theorem phase_31_36 : ∀ i ∈ List.range 4, PhaseAt 31 (36+i) := by decide +kernel

theorem phase_31_40 : ∀ i ∈ List.range 4, PhaseAt 31 (40+i) := by decide +kernel

theorem phase_31_44 : ∀ i ∈ List.range 4, PhaseAt 31 (44+i) := by decide +kernel

theorem phase_31_48 : ∀ i ∈ List.range 4, PhaseAt 31 (48+i) := by decide +kernel

theorem phase_31_52 : ∀ i ∈ List.range 4, PhaseAt 31 (52+i) := by decide +kernel

theorem phase_31_56 : ∀ i ∈ List.range 4, PhaseAt 31 (56+i) := by decide +kernel

theorem phase_31_60 : ∀ i ∈ List.range 4, PhaseAt 31 (60+i) := by decide +kernel

theorem phase_31_64 : ∀ i ∈ List.range 4, PhaseAt 31 (64+i) := by decide +kernel

theorem phase_31_68 : ∀ i ∈ List.range 4, PhaseAt 31 (68+i) := by decide +kernel

theorem phase_31_72 : ∀ i ∈ List.range 4, PhaseAt 31 (72+i) := by decide +kernel

theorem phase_31_76 : ∀ i ∈ List.range 4, PhaseAt 31 (76+i) := by decide +kernel

theorem phase_31_80 : ∀ i ∈ List.range 4, PhaseAt 31 (80+i) := by decide +kernel

theorem phase_31_84 : ∀ i ∈ List.range 4, PhaseAt 31 (84+i) := by decide +kernel

theorem phase_31_88 : ∀ i ∈ List.range 4, PhaseAt 31 (88+i) := by decide +kernel

theorem phase_31_92 : ∀ i ∈ List.range 4, PhaseAt 31 (92+i) := by decide +kernel

theorem phase_31_96 : ∀ i ∈ List.range 4, PhaseAt 31 (96+i) := by decide +kernel

theorem phase_31_100 : ∀ i ∈ List.range 4, PhaseAt 31 (100+i) := by decide +kernel

theorem phase_31_104 : ∀ i ∈ List.range 4, PhaseAt 31 (104+i) := by decide +kernel

theorem phase_31_108 : ∀ i ∈ List.range 4, PhaseAt 31 (108+i) := by decide +kernel

theorem phase_31_112 : ∀ i ∈ List.range 4, PhaseAt 31 (112+i) := by decide +kernel

theorem phase_31 (v : ℕ) (hv : v ∈ List.range 116) : PhaseAt 31 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => PhaseAt 31 v)
  have h := (join 0 56 60 (join 0 28 28 (join 0 12 16 (join 0 4 8 phase_31_0 (join 4 4 4 phase_31_4 phase_31_8)) (join 12 8 8 (join 12 4 4 phase_31_12 phase_31_16) (join 20 4 4 phase_31_20 phase_31_24))) (join 28 12 16 (join 28 4 8 phase_31_28 (join 32 4 4 phase_31_32 phase_31_36)) (join 40 8 8 (join 40 4 4 phase_31_40 phase_31_44) (join 48 4 4 phase_31_48 phase_31_52)))) (join 56 28 32 (join 56 12 16 (join 56 4 8 phase_31_56 (join 60 4 4 phase_31_60 phase_31_64)) (join 68 8 8 (join 68 4 4 phase_31_68 phase_31_72) (join 76 4 4 phase_31_76 phase_31_80))) (join 84 16 16 (join 84 8 8 (join 84 4 4 phase_31_84 phase_31_88) (join 92 4 4 phase_31_92 phase_31_96)) (join 100 8 8 (join 100 4 4 phase_31_100 phase_31_104) (join 108 4 4 phase_31_108 phase_31_112)))))
  simpa only [Nat.zero_add] using h v hv

theorem threshold_31_0 : ∀ i ∈ List.range 1, ThresholdAt 31 (0+i) := by decide +kernel

theorem threshold_31_1 : ∀ i ∈ List.range 1, ThresholdAt 31 (1+i) := by decide +kernel

theorem threshold_31_2 : ∀ i ∈ List.range 1, ThresholdAt 31 (2+i) := by decide +kernel

theorem threshold_31_3 : ∀ i ∈ List.range 1, ThresholdAt 31 (3+i) := by decide +kernel

theorem threshold_31_4 : ∀ i ∈ List.range 1, ThresholdAt 31 (4+i) := by decide +kernel

theorem threshold_31_5 : ∀ i ∈ List.range 1, ThresholdAt 31 (5+i) := by decide +kernel

theorem threshold_31_6 : ∀ i ∈ List.range 1, ThresholdAt 31 (6+i) := by decide +kernel

theorem threshold_31_7 : ∀ i ∈ List.range 1, ThresholdAt 31 (7+i) := by decide +kernel

theorem threshold_31_8 : ∀ i ∈ List.range 1, ThresholdAt 31 (8+i) := by decide +kernel

theorem threshold_31_9 : ∀ i ∈ List.range 1, ThresholdAt 31 (9+i) := by decide +kernel

theorem threshold_31_10 : ∀ i ∈ List.range 1, ThresholdAt 31 (10+i) := by decide +kernel

theorem threshold_31_11 : ∀ i ∈ List.range 1, ThresholdAt 31 (11+i) := by decide +kernel

theorem threshold_31_12 : ∀ i ∈ List.range 1, ThresholdAt 31 (12+i) := by decide +kernel

theorem threshold_31_13 : ∀ i ∈ List.range 1, ThresholdAt 31 (13+i) := by decide +kernel

theorem threshold_31_14 : ∀ i ∈ List.range 1, ThresholdAt 31 (14+i) := by decide +kernel

theorem threshold_31_15 : ∀ i ∈ List.range 1, ThresholdAt 31 (15+i) := by decide +kernel

theorem threshold_31_16 : ∀ i ∈ List.range 1, ThresholdAt 31 (16+i) := by decide +kernel

theorem threshold_31_17 : ∀ i ∈ List.range 1, ThresholdAt 31 (17+i) := by decide +kernel

theorem threshold_31_18 : ∀ i ∈ List.range 1, ThresholdAt 31 (18+i) := by decide +kernel

theorem threshold_31_19 : ∀ i ∈ List.range 1, ThresholdAt 31 (19+i) := by decide +kernel

theorem threshold_31_20 : ∀ i ∈ List.range 1, ThresholdAt 31 (20+i) := by decide +kernel

theorem threshold_31_21 : ∀ i ∈ List.range 1, ThresholdAt 31 (21+i) := by decide +kernel

theorem threshold_31_22 : ∀ i ∈ List.range 1, ThresholdAt 31 (22+i) := by decide +kernel

theorem threshold_31_23 : ∀ i ∈ List.range 1, ThresholdAt 31 (23+i) := by decide +kernel

theorem threshold_31_24 : ∀ i ∈ List.range 1, ThresholdAt 31 (24+i) := by decide +kernel

theorem threshold_31_25 : ∀ i ∈ List.range 1, ThresholdAt 31 (25+i) := by decide +kernel

theorem threshold_31_26 : ∀ i ∈ List.range 1, ThresholdAt 31 (26+i) := by decide +kernel

theorem threshold_31_27 : ∀ i ∈ List.range 1, ThresholdAt 31 (27+i) := by decide +kernel

theorem threshold_31_28 : ∀ i ∈ List.range 1, ThresholdAt 31 (28+i) := by decide +kernel

theorem threshold_31_29 : ∀ i ∈ List.range 1, ThresholdAt 31 (29+i) := by decide +kernel

theorem threshold_31_30 : ∀ i ∈ List.range 1, ThresholdAt 31 (30+i) := by decide +kernel

theorem threshold_31_31 : ∀ i ∈ List.range 1, ThresholdAt 31 (31+i) := by decide +kernel

theorem threshold_31_32 : ∀ i ∈ List.range 1, ThresholdAt 31 (32+i) := by decide +kernel

theorem threshold_31_33 : ∀ i ∈ List.range 1, ThresholdAt 31 (33+i) := by decide +kernel

theorem threshold_31_34 : ∀ i ∈ List.range 1, ThresholdAt 31 (34+i) := by decide +kernel

theorem threshold_31_35 : ∀ i ∈ List.range 1, ThresholdAt 31 (35+i) := by decide +kernel

theorem threshold_31_36 : ∀ i ∈ List.range 1, ThresholdAt 31 (36+i) := by decide +kernel

theorem threshold_31_37 : ∀ i ∈ List.range 1, ThresholdAt 31 (37+i) := by decide +kernel

theorem threshold_31_38 : ∀ i ∈ List.range 1, ThresholdAt 31 (38+i) := by decide +kernel

theorem threshold_31_39 : ∀ i ∈ List.range 1, ThresholdAt 31 (39+i) := by decide +kernel

theorem threshold_31_40 : ∀ i ∈ List.range 1, ThresholdAt 31 (40+i) := by decide +kernel

theorem threshold_31_41 : ∀ i ∈ List.range 1, ThresholdAt 31 (41+i) := by decide +kernel

theorem threshold_31_42 : ∀ i ∈ List.range 1, ThresholdAt 31 (42+i) := by decide +kernel

theorem threshold_31_43 : ∀ i ∈ List.range 1, ThresholdAt 31 (43+i) := by decide +kernel

theorem threshold_31_44 : ∀ i ∈ List.range 1, ThresholdAt 31 (44+i) := by decide +kernel

theorem threshold_31_45 : ∀ i ∈ List.range 1, ThresholdAt 31 (45+i) := by decide +kernel

theorem threshold_31_46 : ∀ i ∈ List.range 1, ThresholdAt 31 (46+i) := by decide +kernel

theorem threshold_31_47 : ∀ i ∈ List.range 1, ThresholdAt 31 (47+i) := by decide +kernel

theorem threshold_31_48 : ∀ i ∈ List.range 1, ThresholdAt 31 (48+i) := by decide +kernel

theorem threshold_31_49 : ∀ i ∈ List.range 1, ThresholdAt 31 (49+i) := by decide +kernel

theorem threshold_31_50 : ∀ i ∈ List.range 1, ThresholdAt 31 (50+i) := by decide +kernel

theorem threshold_31_51 : ∀ i ∈ List.range 1, ThresholdAt 31 (51+i) := by decide +kernel

theorem threshold_31_52 : ∀ i ∈ List.range 1, ThresholdAt 31 (52+i) := by decide +kernel

theorem threshold_31_53 : ∀ i ∈ List.range 1, ThresholdAt 31 (53+i) := by decide +kernel

theorem threshold_31_54 : ∀ i ∈ List.range 1, ThresholdAt 31 (54+i) := by decide +kernel

theorem threshold_31_55 : ∀ i ∈ List.range 1, ThresholdAt 31 (55+i) := by decide +kernel

theorem threshold_31_56 : ∀ i ∈ List.range 1, ThresholdAt 31 (56+i) := by decide +kernel

theorem threshold_31_57 : ∀ i ∈ List.range 1, ThresholdAt 31 (57+i) := by decide +kernel

theorem threshold_31_58 : ∀ i ∈ List.range 1, ThresholdAt 31 (58+i) := by decide +kernel

theorem threshold_31_59 : ∀ i ∈ List.range 1, ThresholdAt 31 (59+i) := by decide +kernel

theorem threshold_31_60 : ∀ i ∈ List.range 1, ThresholdAt 31 (60+i) := by decide +kernel

theorem threshold_31_61 : ∀ i ∈ List.range 1, ThresholdAt 31 (61+i) := by decide +kernel

theorem threshold_31_62 : ∀ i ∈ List.range 1, ThresholdAt 31 (62+i) := by decide +kernel

theorem threshold_31_63 : ∀ i ∈ List.range 1, ThresholdAt 31 (63+i) := by decide +kernel

theorem threshold_31_64 : ∀ i ∈ List.range 1, ThresholdAt 31 (64+i) := by decide +kernel

theorem threshold_31_65 : ∀ i ∈ List.range 1, ThresholdAt 31 (65+i) := by decide +kernel

theorem threshold_31_66 : ∀ i ∈ List.range 1, ThresholdAt 31 (66+i) := by decide +kernel

theorem threshold_31_67 : ∀ i ∈ List.range 1, ThresholdAt 31 (67+i) := by decide +kernel

theorem threshold_31_68 : ∀ i ∈ List.range 1, ThresholdAt 31 (68+i) := by decide +kernel

theorem threshold_31_69 : ∀ i ∈ List.range 1, ThresholdAt 31 (69+i) := by decide +kernel

theorem threshold_31_70 : ∀ i ∈ List.range 1, ThresholdAt 31 (70+i) := by decide +kernel

theorem threshold_31_71 : ∀ i ∈ List.range 1, ThresholdAt 31 (71+i) := by decide +kernel

theorem threshold_31_72 : ∀ i ∈ List.range 1, ThresholdAt 31 (72+i) := by decide +kernel

theorem threshold_31_73 : ∀ i ∈ List.range 1, ThresholdAt 31 (73+i) := by decide +kernel

theorem threshold_31_74 : ∀ i ∈ List.range 1, ThresholdAt 31 (74+i) := by decide +kernel

theorem threshold_31_75 : ∀ i ∈ List.range 1, ThresholdAt 31 (75+i) := by decide +kernel

theorem threshold_31_76 : ∀ i ∈ List.range 1, ThresholdAt 31 (76+i) := by decide +kernel

theorem threshold_31_77 : ∀ i ∈ List.range 1, ThresholdAt 31 (77+i) := by decide +kernel

theorem threshold_31_78 : ∀ i ∈ List.range 1, ThresholdAt 31 (78+i) := by decide +kernel

theorem threshold_31_79 : ∀ i ∈ List.range 1, ThresholdAt 31 (79+i) := by decide +kernel

theorem threshold_31_80 : ∀ i ∈ List.range 1, ThresholdAt 31 (80+i) := by decide +kernel

theorem threshold_31_81 : ∀ i ∈ List.range 1, ThresholdAt 31 (81+i) := by decide +kernel

theorem threshold_31_82 : ∀ i ∈ List.range 1, ThresholdAt 31 (82+i) := by decide +kernel

theorem threshold_31_83 : ∀ i ∈ List.range 1, ThresholdAt 31 (83+i) := by decide +kernel

theorem threshold_31_84 : ∀ i ∈ List.range 1, ThresholdAt 31 (84+i) := by decide +kernel

theorem threshold_31_85 : ∀ i ∈ List.range 1, ThresholdAt 31 (85+i) := by decide +kernel

theorem threshold_31_86 : ∀ i ∈ List.range 1, ThresholdAt 31 (86+i) := by decide +kernel

theorem threshold_31_87 : ∀ i ∈ List.range 1, ThresholdAt 31 (87+i) := by decide +kernel

theorem threshold_31_88 : ∀ i ∈ List.range 1, ThresholdAt 31 (88+i) := by decide +kernel

theorem threshold_31_89 : ∀ i ∈ List.range 1, ThresholdAt 31 (89+i) := by decide +kernel

theorem threshold_31_90 : ∀ i ∈ List.range 1, ThresholdAt 31 (90+i) := by decide +kernel

theorem threshold_31_91 : ∀ i ∈ List.range 1, ThresholdAt 31 (91+i) := by decide +kernel

theorem threshold_31_92 : ∀ i ∈ List.range 1, ThresholdAt 31 (92+i) := by decide +kernel

theorem threshold_31_93 : ∀ i ∈ List.range 1, ThresholdAt 31 (93+i) := by decide +kernel

theorem threshold_31_94 : ∀ i ∈ List.range 1, ThresholdAt 31 (94+i) := by decide +kernel

theorem threshold_31_95 : ∀ i ∈ List.range 1, ThresholdAt 31 (95+i) := by decide +kernel

theorem threshold_31_96 : ∀ i ∈ List.range 1, ThresholdAt 31 (96+i) := by decide +kernel

theorem threshold_31_97 : ∀ i ∈ List.range 1, ThresholdAt 31 (97+i) := by decide +kernel

theorem threshold_31_98 : ∀ i ∈ List.range 1, ThresholdAt 31 (98+i) := by decide +kernel

theorem threshold_31_99 : ∀ i ∈ List.range 1, ThresholdAt 31 (99+i) := by decide +kernel

theorem threshold_31_100 : ∀ i ∈ List.range 1, ThresholdAt 31 (100+i) := by decide +kernel

theorem threshold_31_101 : ∀ i ∈ List.range 1, ThresholdAt 31 (101+i) := by decide +kernel

theorem threshold_31_102 : ∀ i ∈ List.range 1, ThresholdAt 31 (102+i) := by decide +kernel

theorem threshold_31_103 : ∀ i ∈ List.range 1, ThresholdAt 31 (103+i) := by decide +kernel

theorem threshold_31_104 : ∀ i ∈ List.range 1, ThresholdAt 31 (104+i) := by decide +kernel

theorem threshold_31_105 : ∀ i ∈ List.range 1, ThresholdAt 31 (105+i) := by decide +kernel

theorem threshold_31_106 : ∀ i ∈ List.range 1, ThresholdAt 31 (106+i) := by decide +kernel

theorem threshold_31_107 : ∀ i ∈ List.range 1, ThresholdAt 31 (107+i) := by decide +kernel

theorem threshold_31_108 : ∀ i ∈ List.range 1, ThresholdAt 31 (108+i) := by decide +kernel

theorem threshold_31_109 : ∀ i ∈ List.range 1, ThresholdAt 31 (109+i) := by decide +kernel

theorem threshold_31_110 : ∀ i ∈ List.range 1, ThresholdAt 31 (110+i) := by decide +kernel

theorem threshold_31_111 : ∀ i ∈ List.range 1, ThresholdAt 31 (111+i) := by decide +kernel

theorem threshold_31_112 : ∀ i ∈ List.range 1, ThresholdAt 31 (112+i) := by decide +kernel

theorem threshold_31_113 : ∀ i ∈ List.range 1, ThresholdAt 31 (113+i) := by decide +kernel

theorem threshold_31_114 : ∀ i ∈ List.range 1, ThresholdAt 31 (114+i) := by decide +kernel

theorem threshold_31_115 : ∀ i ∈ List.range 1, ThresholdAt 31 (115+i) := by decide +kernel

theorem threshold_31 (v : ℕ) (hv : v ∈ List.range 116) : ThresholdAt 31 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => ThresholdAt 31 v)
  have h := (join 0 58 58 (join 0 29 29 (join 0 14 15 (join 0 7 7 (join 0 3 4 (join 0 1 2 threshold_31_0 (join 1 1 1 threshold_31_1 threshold_31_2)) (join 3 2 2 (join 3 1 1 threshold_31_3 threshold_31_4) (join 5 1 1 threshold_31_5 threshold_31_6))) (join 7 3 4 (join 7 1 2 threshold_31_7 (join 8 1 1 threshold_31_8 threshold_31_9)) (join 10 2 2 (join 10 1 1 threshold_31_10 threshold_31_11) (join 12 1 1 threshold_31_12 threshold_31_13)))) (join 14 7 8 (join 14 3 4 (join 14 1 2 threshold_31_14 (join 15 1 1 threshold_31_15 threshold_31_16)) (join 17 2 2 (join 17 1 1 threshold_31_17 threshold_31_18) (join 19 1 1 threshold_31_19 threshold_31_20))) (join 21 4 4 (join 21 2 2 (join 21 1 1 threshold_31_21 threshold_31_22) (join 23 1 1 threshold_31_23 threshold_31_24)) (join 25 2 2 (join 25 1 1 threshold_31_25 threshold_31_26) (join 27 1 1 threshold_31_27 threshold_31_28))))) (join 29 14 15 (join 29 7 7 (join 29 3 4 (join 29 1 2 threshold_31_29 (join 30 1 1 threshold_31_30 threshold_31_31)) (join 32 2 2 (join 32 1 1 threshold_31_32 threshold_31_33) (join 34 1 1 threshold_31_34 threshold_31_35))) (join 36 3 4 (join 36 1 2 threshold_31_36 (join 37 1 1 threshold_31_37 threshold_31_38)) (join 39 2 2 (join 39 1 1 threshold_31_39 threshold_31_40) (join 41 1 1 threshold_31_41 threshold_31_42)))) (join 43 7 8 (join 43 3 4 (join 43 1 2 threshold_31_43 (join 44 1 1 threshold_31_44 threshold_31_45)) (join 46 2 2 (join 46 1 1 threshold_31_46 threshold_31_47) (join 48 1 1 threshold_31_48 threshold_31_49))) (join 50 4 4 (join 50 2 2 (join 50 1 1 threshold_31_50 threshold_31_51) (join 52 1 1 threshold_31_52 threshold_31_53)) (join 54 2 2 (join 54 1 1 threshold_31_54 threshold_31_55) (join 56 1 1 threshold_31_56 threshold_31_57)))))) (join 58 29 29 (join 58 14 15 (join 58 7 7 (join 58 3 4 (join 58 1 2 threshold_31_58 (join 59 1 1 threshold_31_59 threshold_31_60)) (join 61 2 2 (join 61 1 1 threshold_31_61 threshold_31_62) (join 63 1 1 threshold_31_63 threshold_31_64))) (join 65 3 4 (join 65 1 2 threshold_31_65 (join 66 1 1 threshold_31_66 threshold_31_67)) (join 68 2 2 (join 68 1 1 threshold_31_68 threshold_31_69) (join 70 1 1 threshold_31_70 threshold_31_71)))) (join 72 7 8 (join 72 3 4 (join 72 1 2 threshold_31_72 (join 73 1 1 threshold_31_73 threshold_31_74)) (join 75 2 2 (join 75 1 1 threshold_31_75 threshold_31_76) (join 77 1 1 threshold_31_77 threshold_31_78))) (join 79 4 4 (join 79 2 2 (join 79 1 1 threshold_31_79 threshold_31_80) (join 81 1 1 threshold_31_81 threshold_31_82)) (join 83 2 2 (join 83 1 1 threshold_31_83 threshold_31_84) (join 85 1 1 threshold_31_85 threshold_31_86))))) (join 87 14 15 (join 87 7 7 (join 87 3 4 (join 87 1 2 threshold_31_87 (join 88 1 1 threshold_31_88 threshold_31_89)) (join 90 2 2 (join 90 1 1 threshold_31_90 threshold_31_91) (join 92 1 1 threshold_31_92 threshold_31_93))) (join 94 3 4 (join 94 1 2 threshold_31_94 (join 95 1 1 threshold_31_95 threshold_31_96)) (join 97 2 2 (join 97 1 1 threshold_31_97 threshold_31_98) (join 99 1 1 threshold_31_99 threshold_31_100)))) (join 101 7 8 (join 101 3 4 (join 101 1 2 threshold_31_101 (join 102 1 1 threshold_31_102 threshold_31_103)) (join 104 2 2 (join 104 1 1 threshold_31_104 threshold_31_105) (join 106 1 1 threshold_31_106 threshold_31_107))) (join 108 4 4 (join 108 2 2 (join 108 1 1 threshold_31_108 threshold_31_109) (join 110 1 1 threshold_31_110 threshold_31_111)) (join 112 2 2 (join 112 1 1 threshold_31_112 threshold_31_113) (join 114 1 1 threshold_31_114 threshold_31_115)))))))
  simpa only [Nat.zero_add] using h v hv

theorem ledger_31_0 : ∀ i ∈ List.range 4, LedgerAt 31 (0+i) := by decide +kernel

theorem ledger_31_4 : ∀ i ∈ List.range 4, LedgerAt 31 (4+i) := by decide +kernel

theorem ledger_31_8 : ∀ i ∈ List.range 4, LedgerAt 31 (8+i) := by decide +kernel

theorem ledger_31_12 : ∀ i ∈ List.range 4, LedgerAt 31 (12+i) := by decide +kernel

theorem ledger_31_16 : ∀ i ∈ List.range 4, LedgerAt 31 (16+i) := by decide +kernel

theorem ledger_31_20 : ∀ i ∈ List.range 4, LedgerAt 31 (20+i) := by decide +kernel

theorem ledger_31_24 : ∀ i ∈ List.range 4, LedgerAt 31 (24+i) := by decide +kernel

theorem ledger_31_28 : ∀ i ∈ List.range 4, LedgerAt 31 (28+i) := by decide +kernel

theorem ledger_31_32 : ∀ i ∈ List.range 4, LedgerAt 31 (32+i) := by decide +kernel

theorem ledger_31_36 : ∀ i ∈ List.range 4, LedgerAt 31 (36+i) := by decide +kernel

theorem ledger_31_40 : ∀ i ∈ List.range 4, LedgerAt 31 (40+i) := by decide +kernel

theorem ledger_31_44 : ∀ i ∈ List.range 4, LedgerAt 31 (44+i) := by decide +kernel

theorem ledger_31_48 : ∀ i ∈ List.range 4, LedgerAt 31 (48+i) := by decide +kernel

theorem ledger_31_52 : ∀ i ∈ List.range 4, LedgerAt 31 (52+i) := by decide +kernel

theorem ledger_31_56 : ∀ i ∈ List.range 4, LedgerAt 31 (56+i) := by decide +kernel

theorem ledger_31_60 : ∀ i ∈ List.range 4, LedgerAt 31 (60+i) := by decide +kernel

theorem ledger_31_64 : ∀ i ∈ List.range 4, LedgerAt 31 (64+i) := by decide +kernel

theorem ledger_31_68 : ∀ i ∈ List.range 4, LedgerAt 31 (68+i) := by decide +kernel

theorem ledger_31_72 : ∀ i ∈ List.range 4, LedgerAt 31 (72+i) := by decide +kernel

theorem ledger_31_76 : ∀ i ∈ List.range 4, LedgerAt 31 (76+i) := by decide +kernel

theorem ledger_31_80 : ∀ i ∈ List.range 4, LedgerAt 31 (80+i) := by decide +kernel

theorem ledger_31_84 : ∀ i ∈ List.range 4, LedgerAt 31 (84+i) := by decide +kernel

theorem ledger_31_88 : ∀ i ∈ List.range 4, LedgerAt 31 (88+i) := by decide +kernel

theorem ledger_31_92 : ∀ i ∈ List.range 4, LedgerAt 31 (92+i) := by decide +kernel

theorem ledger_31_96 : ∀ i ∈ List.range 4, LedgerAt 31 (96+i) := by decide +kernel

theorem ledger_31_100 : ∀ i ∈ List.range 4, LedgerAt 31 (100+i) := by decide +kernel

theorem ledger_31_104 : ∀ i ∈ List.range 4, LedgerAt 31 (104+i) := by decide +kernel

theorem ledger_31_108 : ∀ i ∈ List.range 4, LedgerAt 31 (108+i) := by decide +kernel

theorem ledger_31_112 : ∀ i ∈ List.range 4, LedgerAt 31 (112+i) := by decide +kernel

theorem ledger_31 (v : ℕ) (hv : v ∈ List.range 116) : LedgerAt 31 v := by
  let join := @BoundaryTailBaseFast6807.range_join (fun v => LedgerAt 31 v)
  have h := (join 0 56 60 (join 0 28 28 (join 0 12 16 (join 0 4 8 ledger_31_0 (join 4 4 4 ledger_31_4 ledger_31_8)) (join 12 8 8 (join 12 4 4 ledger_31_12 ledger_31_16) (join 20 4 4 ledger_31_20 ledger_31_24))) (join 28 12 16 (join 28 4 8 ledger_31_28 (join 32 4 4 ledger_31_32 ledger_31_36)) (join 40 8 8 (join 40 4 4 ledger_31_40 ledger_31_44) (join 48 4 4 ledger_31_48 ledger_31_52)))) (join 56 28 32 (join 56 12 16 (join 56 4 8 ledger_31_56 (join 60 4 4 ledger_31_60 ledger_31_64)) (join 68 8 8 (join 68 4 4 ledger_31_68 ledger_31_72) (join 76 4 4 ledger_31_76 ledger_31_80))) (join 84 16 16 (join 84 8 8 (join 84 4 4 ledger_31_84 ledger_31_88) (join 92 4 4 ledger_31_92 ledger_31_96)) (join 100 8 8 (join 100 4 4 ledger_31_100 ledger_31_104) (join 108 4 4 ledger_31_108 ledger_31_112)))))
  simpa only [Nat.zero_add] using h v hv

end ProximityPrize.SubmissionLower.BoundaryTailRowsChecked6807
