import ProximityPrize.SubmissionLower.BoundaryTailStrictConvex

namespace ProximityPrize.SubmissionLower.BoundaryTailStrictConvex

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem curvature1 : Curvature 1 := by decide +kernel

theorem curvature2 : Curvature 2 := by decide +kernel

theorem curvature3 : Curvature 3 := by decide +kernel

theorem curvature4 : Curvature 4 := by decide +kernel

theorem curvature5 : Curvature 5 := by decide +kernel

theorem curvature6 : Curvature 6 := by decide +kernel

theorem curvature7 : Curvature 7 := by decide +kernel

theorem curvature8 : Curvature 8 := by decide +kernel

theorem curvature9 : Curvature 9 := by decide +kernel

theorem curvature10 : Curvature 10 := by decide +kernel

theorem curvature11 : Curvature 11 := by decide +kernel

theorem curvature12 : Curvature 12 := by decide +kernel

theorem curvature13 : Curvature 13 := by decide +kernel

theorem curvature14 : Curvature 14 := by decide +kernel

theorem curvature15 : Curvature 15 := by decide +kernel

theorem curvature16 : Curvature 16 := by decide +kernel

theorem curvature17 : Curvature 17 := by decide +kernel

theorem curvature18 : Curvature 18 := by decide +kernel

theorem curvature19 : Curvature 19 := by decide +kernel

theorem curvature20 : Curvature 20 := by decide +kernel

theorem curvature21 : Curvature 21 := by decide +kernel

theorem curvature22 : Curvature 22 := by decide +kernel

theorem curvature23 : Curvature 23 := by decide +kernel

theorem curvature24 : Curvature 24 := by decide +kernel

theorem curvature25 : Curvature 25 := by decide +kernel

theorem curvature26 : Curvature 26 := by decide +kernel

theorem curvature27 : Curvature 27 := by decide +kernel

theorem curvature28 : Curvature 28 := by decide +kernel

theorem curvature29 : Curvature 29 := by decide +kernel

theorem curvature30 : Curvature 30 := by decide +kernel

theorem curvature31 : Curvature 31 := by decide +kernel

theorem curvatureAll : ∀ r ∈ List.range 32, 1 ≤ r → Curvature r := by
  intro r hr hpos
  have hlt := List.mem_range.mp hr
  interval_cases r
  · exact curvature1
  · exact curvature2
  · exact curvature3
  · exact curvature4
  · exact curvature5
  · exact curvature6
  · exact curvature7
  · exact curvature8
  · exact curvature9
  · exact curvature10
  · exact curvature11
  · exact curvature12
  · exact curvature13
  · exact curvature14
  · exact curvature15
  · exact curvature16
  · exact curvature17
  · exact curvature18
  · exact curvature19
  · exact curvature20
  · exact curvature21
  · exact curvature22
  · exact curvature23
  · exact curvature24
  · exact curvature25
  · exact curvature26
  · exact curvature27
  · exact curvature28
  · exact curvature29
  · exact curvature30
  · exact curvature31

end ProximityPrize.SubmissionLower.BoundaryTailStrictConvex
