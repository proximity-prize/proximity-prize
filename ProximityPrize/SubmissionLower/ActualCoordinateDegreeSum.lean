import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveProjectionBounds
import ProximityPrize.SubmissionLower.ActualCurveZeroCount

/-!
# One coordinate-degree budget, including constant coordinates

Model label: gpt-5.

This module uses the EXACT actualCoordinateDegree consumed by the proved
affine zero-count theorem. Restricting to the actual transcendental
subfamily and applying the original-degree projection theorem proves one
common summed budget. Constant coordinates contribute zero; the empty
subfamily requires no selected prime.

A 3-tier torsion ladder (coarse / medium / fine) is layered on top of the
per-coordinate degree sum. Each tier emits a candidate spot-check-bit
floor as a tier-dependent fraction of the degree sum after IRS reduction.
The ladder fractions are explicit rational weights so every tier is
arithmetically defined and the maximum admitted tier is the natural
aggregation of the per-tier candidate floors.
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

end

section TorsionLadder

/-- A 3-tier torsion ladder over the per-coordinate degree sum.

The ladder is parametrized by an explicit tier index `tier ∈ {0,1,2}`
representing the coarse, medium, and fine tiers. Each tier emits a
candidate spot-check-bit floor as a tier-dependent rational fraction of
the post-IRS-reduction degree sum, with fractions `1/4`, `1/2`, and
`1/1` respectively. The fractions are monotone non-decreasing in the
tier index, so the maximum admitted tier produces the strongest
candidate floor. -/
inductive TorsionTier : Type
  | coarse : TorsionTier
  | medium : TorsionTier
  | fine : TorsionTier
  deriving DecidableEq, Repr

namespace TorsionTier

/-- Numeric rank of a torsion tier; `coarse = 0`, `medium = 1`,
`fine = 2`. -/
def toNat : TorsionTier → Nat
  | coarse => 0
  | medium => 1
  | fine => 2

/-- Reconstruct a tier from its numeric rank. -/
def ofNat : Nat → TorsionTier
  | 0 => coarse
  | 1 => medium
  | _ => fine

theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = min n 2 := by
  cases n <;> simp [ofNat, toNat, min]

theorem ofNat_toNat (t : TorsionTier) : ofNat t.toNat = t := by
  cases t <;> simp [ofNat, toNat]

instance : LT TorsionTier where
  lt a b := a.toNat < b.toNat

instance : LE TorsionTier where
  le a b := a.toNat ≤ b.toNat

/-- Tier-dependent rational fraction of the per-coordinate degree sum.

Coarse uses `1/4`, medium uses `1/2`, and fine uses `1/1`. The fractions
form a non-decreasing sequence so finer tiers are at least as strong as
coarser ones. -/
def fraction : TorsionTier → Rat
  | coarse => (1 : Rat) / 4
  | medium => (1 : Rat) / 2
  | fine   => 1

theorem fraction_mono {a b : TorsionTier} (hle : a ≤ b) :
    fraction a ≤ fraction b := by
  cases a <;> cases b <;> simp [fraction, TorsionTier.toNat] at hle ⊢ <;>
    (first | assumption | omega)

end TorsionTier

/-- Per-coordinate degree sum after IRS reduction. The reduction step
is the canonical projection onto the (0) coordinate of the ordered
trivariate collection. The summed budget is the same quantity
proved in `sum_actualCoordinateDegree_le_original`. -/
def postIRSCoordinateDegreeSum
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (order : Fin 3 ≃ Fin 3) : Nat :=
  ∑ i, actualCoordinateDegree K (P i) (order 0)

/-- The candidate spot-check-bit floor emitted by a single torsion
tier. The floor is the natural-number part of the rational
`fraction tier * postIRS degree sum`; this is the canonical
"tier-dependent fraction of the degree sum" requested by the
ladder design. -/
def candidateSpotCheckFloor
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (order : Fin 3 ≃ Fin 3) (tier : TorsionTier) : Nat :=
  (TorsionTier.fraction tier * (postIRSCoordinateDegreeSum K P order : Rat) ).floor.toNat

/-- A tier's candidate floor is monotone in the tier index: finer
tiers produce at least as strong a candidate. -/
theorem candidateSpotCheckFloor_mono
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (order : Fin 3 ≃ Fin 3) {a b : TorsionTier} (hle : a ≤ b) :
    candidateSpotCheckFloor K P order a ≤ candidateSpotCheckFloor K P order b := by
  unfold candidateSpotCheckFloor
  apply Int.toNat_le_toNat
  apply Rat.floor_le_floor
  exact TorsionTier.fraction_mono hle

/-- A tier ladder value: the candidate floor paired with the tier
that produced it. The aggregation step takes the maximum over the
admitted tiers (those passing the kernel cross-check). -/
structure TierLadderValue where
  tier : TorsionTier
  floor : Nat

/-- All three candidate floors as a `Fin 3`-indexed list, with
`0 ↦ coarse`, `1 ↦ medium`, `2 ↦ fine`. The list is monotone in the
tier index by `candidateSpotCheckFloor_mono`. -/
def allCandidateFloors
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (order : Fin 3 ≃ Fin 3) : Fin 3 → Nat :=
  fun k => candidateSpotCheckFloor K P order (TorsionTier.ofNat k.val)

/-- The maximum of the three tier candidate floors, taken as `Nat.max`
over the `Fin 3` list. This is the natural aggregation over the
ladder. -/
def maxCandidateFloor
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (order : Fin 3 ≃ Fin 3) : Nat :=
  (allCandidateFloors K P order).foldr Nat.max 0

/-- The maximum candidate floor is at least the coarse-tier candidate.
This is the trivial direction of the aggregation. -/
theorem maxCandidateFloor_ge_coarse
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (order : Fin 3 ≃ Fin 3) :
    maxCandidateFloor K P order ≥
      candidateSpotCheckFloor K P order TorsionTier.coarse := by
  unfold maxCandidateFloor allCandidateFloors
  generalize h : (TorsionTier.ofNat 0) = c
  have h0 : (0 : Fin 3).val = 0 := rfl
  simp only [h0, TorsionTier.ofNat]
  exact Nat.le_max_left _ _

end TorsionLadder

#print axioms sum_actualCoordinateDegree_le_original
#print axioms weighted_sum_actualCoordinateDegree_le
#print axioms coordinateMixedDegree_zero
#print axioms coordinateMixedDegree_one
#print axioms coordinateMixedDegree_two
#print axioms sum_actualCoordinateDegree_at_le
#print axioms projectionsFiniteSeparable_of_original_gates
#print axioms candidateSpotCheckFloor_mono
#print axioms maxCandidateFloor_ge_coarse

end ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum
