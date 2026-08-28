import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveProjectionBounds
import ProximityPrize.SubmissionLower.ActualCurveZeroCount
import ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel

/-!
# One coordinate-degree budget, including constant coordinates

Model label: gpt-5.

This module uses the EXACT actualCoordinateDegree consumed by the proved
affine zero-count theorem. Restricting to the actual transcendental
subfamily and applying the original-degree projection theorem proves one
common summed budget. Constant coordinates contribute zero; the empty
subfamily requires no selected prime.
-/

namespace ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum

open ActualCurveCoordinateField ActualCurveRationalProjection
  TrivariateRationalCollection ActualCurveZeroCount ActualPlanePositiveOrder
  ActualCurveProjectionBounds

noncomputable section

variable (K : Type) [Field K]

section Family

variable {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]

theorem sum_actualCoordinateDegree_le_original
    (order : Fin 3 ≃ Fin 3) (hinj : Function.Injective P)
    (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H)
    (h1 : G.degreeOf (order 1) < p) (h2 : G.degreeOf (order 2) < p)
    (hmixed : originalMixedDegree K order G H < p) :
    (∑ i, actualCoordinateDegree K (P i) (order 0)) ≤ originalMixedDegree K order G H := by
  classical
  let s : Set I := {i | Transcendental K (coordinate K (P i) (order 0))}
  let D : s → ℕ := fun i =>
    letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
      rationalBaseAlgebra K (P i) (order 0) i.2
    Module.finrank (RatFunc K) (CoordinateField K (P i))
  have hinj' : Function.Injective (fun i : s => P i) := by
    intro i j h
    apply Subtype.ext
    exact hinj h
  have hbound : (∑ i : s, D i) ≤ originalMixedDegree K order G H := by
    have h := original_finite_separable_sum_finrank_bound K order (fun i : s => P i)
      (fun i => i.2) hinj' p G H hG (fun i => hGmem i) (fun i => hHmem i)
      hproper h1 h2 hmixed
    exact h.2
  calc
    _ = ∑ i : s, D i := by
      apply Finset.sum_congr_set s (fun i => actualCoordinateDegree K (P i) (order 0)) D
      · intro i hi
        exact actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
      · intro i hi
        change ¬ Transcendental K (coordinate K (P i) (order 0)) at hi
        exact dif_neg hi
    _ ≤ _ := hbound

/-- Coordinatewise summed degrees can be paired with any nonnegative box
weights. This is only finite-sum arithmetic; the preceding theorem supplies
the actual geometric degree sums. -/
theorem weighted_sum_actualCoordinateDegree_le (weight bound : Fin 3 → ℕ)
    (hbound : ∀ j, (∑ i, actualCoordinateDegree K (P i) j) ≤ bound j) :
    (∑ i, ∑ j, weight j * actualCoordinateDegree K (P i) j) ≤
      ∑ j, weight j * bound j := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left (weight j) (hbound j)

end Family

def coordinateMixedDegree (G H : Original K) (i : Fin 3) : ℕ :=
  originalMixedDegree K (Equiv.swap 0 i) G H

@[simp] theorem coordinateMixedDegree_zero (G H : Original K) :
    coordinateMixedDegree K G H 0 =
      H.degreeOf 1 * G.degreeOf 2 + G.degreeOf 1 * H.degreeOf 2 := by
  simp [coordinateMixedDegree, originalMixedDegree, Equiv.swap_apply_def]

@[simp] theorem coordinateMixedDegree_one (G H : Original K) :
    coordinateMixedDegree K G H 1 =
      H.degreeOf 0 * G.degreeOf 2 + G.degreeOf 0 * H.degreeOf 2 := by
  simp [coordinateMixedDegree, originalMixedDegree, Equiv.swap_apply_def]

@[simp] theorem coordinateMixedDegree_two (G H : Original K) :
    coordinateMixedDegree K G H 2 =
      H.degreeOf 0 * G.degreeOf 1 + G.degreeOf 0 * H.degreeOf 1 := by
  simp [coordinateMixedDegree, originalMixedDegree, Equiv.swap_apply_def] <;> ring

/-- A canonical version indexed directly by an original coordinate. -/
theorem sum_actualCoordinateDegree_at_le
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (hinj : Function.Injective P) (j : Fin 3) (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H) (hdegree : ∀ k : Fin 3, G.degreeOf k < p)
    (hmixed : coordinateMixedDegree K G H j < p) :
    (∑ i, actualCoordinateDegree K (P i) j) ≤ coordinateMixedDegree K G H j := by
  have h := sum_actualCoordinateDegree_le_original K P (Equiv.swap 0 j) hinj p G H
    hG hGmem hHmem hproper (hdegree ((Equiv.swap 0 j) 1))
      (hdegree ((Equiv.swap 0 j) 2)) hmixed
  simpa only [coordinateMixedDegree, Equiv.swap_apply_left] using h

/-- The actual projection property used by the zero-count theorem is
derived from original equations and the strict original mixed gates. -/
theorem projectionsFiniteSeparable_of_original_gates
    (P : Ideal (Original K)) [P.IsPrime] (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hHmem : H ∈ P) (hproper : ¬ G ∣ H)
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed : ∀ j k : Fin 3, j ≠ k →
      H.degreeOf j * G.degreeOf k + G.degreeOf j * H.degreeOf k < p) :
    ProjectionsFiniteSeparable K P :=
  all_transcendental_coordinates_finite_separable K P p G H
    hG hGmem hHmem hproper hdegree hmixed

/-- The kernel-checked spot-check-bit floor for one coordinate is the
cap-partitioned bit-span of the per-plane cap and the certified-safe IRS
reduction radius. The cap-partitioned routine replaces a direct `Nat.floor`
call: it partitions the bit-floor input by the per-plane cap, recurses on a
segment iff its kernel residue `segment % cap` is nonzero (tolerance 0),
grows the working radius by `radius_grow_bits`=1 per level, caps
recursion depth at 4, drops segments below `min_segment_floor`=1, and
monotone-max combines the per-segment bit-spans. -/
def kernelCheckedSpotCheckBitFloor (cap radius : ℕ) : ℕ :=
  ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel.capPartitionedBitSpan
    cap radius

/-- The per-coordinate degree sum is bounded by the cap-partitioned
kernel-checked spot-check-bit floor applied to the per-plane cap and the
certified-safe IRS reduction radius, whenever the coordinate mixed degree
fits inside the cap-partitioned bit-span. The bound is kernel-checked and
uses no new axioms. -/
theorem sum_actualCoordinateDegree_le_kernelCheckedSpotCheckBitFloor
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (hinj : Function.Injective P) (j : Fin 3) (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H) (hdegree : ∀ k : Fin 3, G.degreeOf k < p)
    (hmixed : coordinateMixedDegree K G H j < p)
    (cap radius : ℕ)
    (hbound : coordinateMixedDegree K G H j ≤
      kernelCheckedSpotCheckBitFloor K cap radius) :
    (∑ i, actualCoordinateDegree K (P i) j) ≤
      kernelCheckedSpotCheckBitFloor K cap radius := by
  have hsum := sum_actualCoordinateDegree_at_le K P hinj j p G H hG
    hGmem hHmem hproper hdegree hmixed
  exact hsum.trans hbound

end

#print axioms sum_actualCoordinateDegree_le_original
#print axioms weighted_sum_actualCoordinateDegree_le
#print axioms coordinateMixedDegree_zero
#print axioms coordinateMixedDegree_one
#print axioms coordinateMixedDegree_two
#print axioms sum_actualCoordinateDegree_at_le
#print axioms projectionsFiniteSeparable_of_original_gates
#print axioms kernelCheckedSpotCheckBitFloor
#print axioms sum_actualCoordinateDegree_le_kernelCheckedSpotCheckBitFloor

end ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum
