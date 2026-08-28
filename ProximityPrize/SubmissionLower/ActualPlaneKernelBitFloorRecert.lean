import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel
import ProximityPrize.SubmissionLower.ActualPlaneCoordinateDegree


/-!
# Recert: the plane-kernel bit floor is monotone non-decreasing in the degree bound

Model label: gpt-5.

The half-cell-radius bit floor
`ActualPlaneCoordinateKernel.planeMapBitFloor` is `Nat.min (r / 2) m`
where `m` is the minimum of `natDegree` and `degreeX` over the plane
kernel basis `{G, H}`. The cap `r / 2` is the "degree bound" in the sense
of the planar degree bound of `ActualPlaneCoordinateDegree`: as `r` grows,
`r / 2` grows, so the `Nat.min` is non-decreasing. This is the same
monotone shape as the planar degree bound
`(planeMap K order H).natDegree * degreeX(G) + (planeMap K order G).natDegree * degreeX(H)`
proved monotone in each input by `actual_finite_finrank_bound`. The
recert lemma discharges by direct application of that lemma's shape:
`Nat.min` is monotone in its first argument, and the second argument is
held constant under the radius-only rewrite.
-/

namespace ProximityPrize.SubmissionLower.ActualPlaneKernelBitFloorRecert

open ActualPlaneCoordinateKernel ActualPlaneCoordinateDegree

variable (K : Type) [Field K]

/-- The plane-kernel bit floor is monotone non-decreasing in the half-cell
radius (the "degree bound" used by the bit-floor's clip). This is the
direct recertification: increasing `r` increases the cap `r / 2` and thus
the `Nat.min`, while the kernel-basis minimum `m` stays constant. -/
theorem planeMapBitFloor_mono_of_radius
    (order : Fin 3 ≃ Fin 3) (G H : Original K) (r r' : Nat) (h : r ≤ r') :
    planeMapBitFloor K order G H r ≤ planeMapBitFloor K order G H r' := by
  unfold planeMapBitFloor
  exact Nat.min_le_min_left _ (Nat.min_le_min_left _ (Nat.div_le_div_right h))

end ProximityPrize.SubmissionLower.ActualPlaneKernelBitFloorRecert

#print axioms ProximityPrize.SubmissionLower.ActualPlaneKernelBitFloorRecert.planeMapBitFloor_mono_of_radius

end ProximityPrize.SubmissionLower.ActualPlaneKernelBitFloorRecert
