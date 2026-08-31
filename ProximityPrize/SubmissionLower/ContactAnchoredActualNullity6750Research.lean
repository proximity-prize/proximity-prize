import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredOneFamilySelector6750Research

 








namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredActualNullity6750Research

open scoped BigOperators
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactAnchoredOneFamilySelector6750Research

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

 

def productionWidth (i j : Nat) : Nat :=
  familyMultiplicity * agreements - contactSlope * i - (contactSlope - 1) * j

def productionCoefficientSlope : Nat :=
  ∑ i ∈ Finset.range 110, ∑ j ∈ Finset.range 25, productionWidth i j

 

theorem coefficientCount_eq_truncated
    {L : Nat} (hL : 109 ≤ L) :
    coefficientCount (familyMultiplicity * agreements) contactSlope L
        familySlopeCap =
      ∑ i ∈ Finset.range 110, ∑ j ∈ Finset.range 25,
        (L + 1 - i - j) * productionWidth i j := by
  unfold coefficientCount productionWidth
  norm_num [familySlopeCap]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i hiL hi110
  have hi : 110 ≤ i := by
    simp only [Finset.mem_range, not_lt] at hi110
    exact hi110
  have hzero :
      familyMultiplicity * agreements - contactSlope * i -
        (contactSlope - 1) * 0 = 0 := by
    norm_num [familyMultiplicity, agreements, contactSlope]
    omega
  apply Finset.sum_eq_zero
  intro j hj
  have hfirst :
      familyMultiplicity * agreements - contactSlope * i = 0 := by
    norm_num [familyMultiplicity, agreements, contactSlope]
    omega
  simp [hfirst]

theorem productionCoefficientSlope_eq :
    productionCoefficientSlope = 15858937975 := by
  norm_num [productionCoefficientSlope, productionWidth,
    familyMultiplicity, agreements, contactSlope, Finset.sum_range_succ]

 

theorem production_coefficientCount_succ
    {L : Nat} (hL : 133 ≤ L) :
    coefficientCount (familyMultiplicity * agreements) contactSlope (L + 1)
        familySlopeCap =
      coefficientCount (familyMultiplicity * agreements) contactSlope L
        familySlopeCap + productionCoefficientSlope := by
  rw [coefficientCount_eq_truncated (by omega),
    coefficientCount_eq_truncated (by omega)]
  unfold productionCoefficientSlope
  calc
    (∑ i ∈ Finset.range 110, ∑ j ∈ Finset.range 25,
        (L + 1 + 1 - i - j) * productionWidth i j) =
      ∑ i ∈ Finset.range 110, ∑ j ∈ Finset.range 25,
        ((L + 1 - i - j) * productionWidth i j +
          productionWidth i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hstep : L + 1 + 1 - i - j = (L + 1 - i - j) + 1 := by
        omega
      rw [hstep, Nat.add_mul, one_mul]
    _ =
      (∑ i ∈ Finset.range 110, ∑ j ∈ Finset.range 25,
        (L + 1 - i - j) * productionWidth i j) +
      ∑ i ∈ Finset.range 110, ∑ j ∈ Finset.range 25,
        productionWidth i j := by
      simp only [Finset.sum_add_distrib]

 

def productionContactSlope (M h : Nat) : Nat :=
  (M + 1) * 25 - (M + 1 - h) * (25 - h)

def productionLocalRankSlope : Nat :=
  ∑ r ∈ Finset.range familyMultiplicity,
    productionContactSlope r (min (r + 1) (familyMultiplicity - r))

theorem blockInputCount_succ
    {M L s : Nat} (hstable : M + s ≤ L) :
    blockInputCount M (L + 1) s =
      blockInputCount M L s + (M + 1) * (s + 1) := by
  unfold blockInputCount
  calc
    (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (s + 1),
        (L + 1 + 1 - i - j)) =
      ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (s + 1),
        ((L + 1 - i - j) + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      omega
    _ =
      (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (s + 1),
        (L + 1 - i - j)) + (M + 1) * (s + 1) := by
      simp only [Finset.sum_add_distrib]
      simp

theorem blockKernelLowerBound_succ
    {M L s h : Nat} (hstable : M + s ≤ L) :
    blockKernelLowerBound M (L + 1) s h =
      blockKernelLowerBound M L s h + (M + 1 - h) * (s + 1 - h) := by
  unfold blockKernelLowerBound
  calc
    (∑ i ∈ Finset.range (M + 1 - h),
        ∑ j ∈ Finset.range (s + 1 - h),
          (L + 1 + 1 - h - i - j)) =
      ∑ i ∈ Finset.range (M + 1 - h),
        ∑ j ∈ Finset.range (s + 1 - h),
          ((L + 1 - h - i - j) + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      omega
    _ =
      (∑ i ∈ Finset.range (M + 1 - h),
        ∑ j ∈ Finset.range (s + 1 - h),
          (L + 1 - h - i - j)) +
        (M + 1 - h) * (s + 1 - h) := by
      simp only [Finset.sum_add_distrib]
      simp

theorem blockKernelLowerBound_le_blockInputCount
    (M L s h : Nat) :
    blockKernelLowerBound M L s h ≤ blockInputCount M L s := by
  unfold blockKernelLowerBound blockInputCount
  calc
    (∑ i ∈ Finset.range (M + 1 - h),
        ∑ j ∈ Finset.range (s + 1 - h),
          (L + 1 - h - i - j)) ≤
      ∑ i ∈ Finset.range (M + 1 - h),
        ∑ j ∈ Finset.range (s + 1 - h),
          (L + 1 - i - j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      omega
    _ ≤
      ∑ i ∈ Finset.range (M + 1 - h),
        ∑ j ∈ Finset.range (s + 1), (L + 1 - i - j) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ ≤
      ∑ i ∈ Finset.range (M + 1),
        ∑ j ∈ Finset.range (s + 1), (L + 1 - i - j) := by
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

theorem productionContactSlope_le_input (M h : Nat) :
    (M + 1 - h) * (25 - h) ≤ (M + 1) * 25 := by
  exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem production_contactRankBound_succ
    {M L h : Nat} (hstable : M + 24 ≤ L) :
    contactRankBound M (L + 1) 24 h =
      contactRankBound M L 24 h + productionContactSlope M h := by
  unfold contactRankBound
  rw [blockInputCount_succ hstable,
    blockKernelLowerBound_succ hstable]
  have hk := blockKernelLowerBound_le_blockInputCount M L 24 h
  have hs := productionContactSlope_le_input M h
  unfold productionContactSlope
  norm_num at hs ⊢
  omega

theorem productionLocalRankSlope_eq :
    productionLocalRankSlope = 60200 := by
  norm_num [productionLocalRankSlope, productionContactSlope,
    familyMultiplicity, Finset.sum_range_succ]

theorem production_localRankBound_succ
    {L : Nat} (hL : 102 ≤ L) :
    localRankBound familyMultiplicity (L + 1) familySlopeCap =
      localRankBound familyMultiplicity L familySlopeCap +
        productionLocalRankSlope := by
  unfold localRankBound productionLocalRankSlope
  norm_num only [familyMultiplicity, familySlopeCap]
  calc
    (∑ r ∈ Finset.range 79,
        contactRankBound (min r (L + 1)) (L + 1) 24
          (min (r + 1) (79 - r))) =
      ∑ r ∈ Finset.range 79,
        contactRankBound r (L + 1) 24 (min (r + 1) (79 - r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' := Finset.mem_range.mp hr
      have hmin : min r (L + 1) = r := Nat.min_eq_left (by omega)
      rw [hmin]
    _ =
      ∑ r ∈ Finset.range 79,
        (contactRankBound r L 24 (min (r + 1) (79 - r)) +
          productionContactSlope r (min (r + 1) (79 - r))) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' := Finset.mem_range.mp hr
      exact production_contactRankBound_succ (by omega)
    _ =
      (∑ r ∈ Finset.range 79,
        contactRankBound r L 24 (min (r + 1) (79 - r))) +
      ∑ r ∈ Finset.range 79,
        productionContactSlope r (min (r + 1) (79 - r)) := by
      simp only [Finset.sum_add_distrib]
    _ =
      (∑ r ∈ Finset.range 79,
        contactRankBound (min r L) L 24 (min (r + 1) (79 - r))) +
      ∑ r ∈ Finset.range 79,
        productionContactSlope r (min (r + 1) (79 - r)) := by
      apply congrArg (fun x : Nat => x +
        ∑ r ∈ Finset.range 79,
          productionContactSlope r (min (r + 1) (79 - r)))
      apply Finset.sum_congr rfl
      intro r hr
      have hr' := Finset.mem_range.mp hr
      have hmin : min r L = r := Nat.min_eq_left (by omega)
      rw [hmin]

 

theorem production_coefficientCount_base :
    coefficientCount (familyMultiplicity * agreements) contactSlope
      familyBaseTotal familySlopeCap = 27427944752800 := by
  rw [coefficientCount_eq_truncated (by norm_num [familyBaseTotal])]
  norm_num [productionWidth, familyMultiplicity, agreements, contactSlope,
    familyBaseTotal, Finset.sum_range_succ]

theorem production_localRankBound_base :
    localRankBound familyMultiplicity familyBaseTotal familySlopeCap =
      104629300 := by
  norm_num (config := { maxSteps := 1000000 })
    [localRankBound, contactRankBound, blockInputCount,
    blockKernelLowerBound, familyMultiplicity, familyBaseTotal,
    familySlopeCap, Finset.sum_range_succ]

theorem actualNullity_base_exact :
    actualNullity familyBaseTotal = affineNullity familyBaseTotal := by
  rw [affineNullity_base]
  unfold actualNullity
  rw [production_coefficientCount_base, production_localRankBound_base]
  norm_num [domainSize]

theorem actualNullity_succ
    {L : Nat} (hL : familyBaseTotal ≤ L)
    (hrank : domainSize * localRankBound familyMultiplicity L familySlopeCap ≤
      coefficientCount (familyMultiplicity * agreements) contactSlope L
        familySlopeCap) :
    actualNullity (L + 1) = actualNullity L + nullitySlope := by
  unfold actualNullity
  rw [production_coefficientCount_succ (by
        norm_num [familyBaseTotal] at hL ⊢
        omega),
    production_localRankBound_succ (by
        norm_num [familyBaseTotal] at hL ⊢
        omega),
    productionCoefficientSlope_eq, productionLocalRankSlope_eq]
  norm_num [domainSize, nullitySlope] at *
  omega

 

theorem actualNullity_eq_affine_base_add (k : Nat) :
    actualNullity (familyBaseTotal + k) =
      affineNullity (familyBaseTotal + k) := by
  induction k with
  | zero => simpa using actualNullity_base_exact
  | succ k ih =>
      have hpositive : 0 < actualNullity (familyBaseTotal + k) := by
        rw [ih, affineNullity_base_add]
        norm_num [affineNullity_base, nullitySlope]
      have hrank :
          domainSize * localRankBound familyMultiplicity
              (familyBaseTotal + k) familySlopeCap ≤
            coefficientCount (familyMultiplicity * agreements) contactSlope
              (familyBaseTotal + k) familySlopeCap := by
        unfold actualNullity at hpositive
        exact (Nat.sub_pos_iff_lt.mp hpositive).le
      calc
        actualNullity (familyBaseTotal + Nat.succ k) =
            actualNullity ((familyBaseTotal + k) + 1) := by
          rfl
        _ = actualNullity (familyBaseTotal + k) + nullitySlope :=
          actualNullity_succ (Nat.le_add_right _ _) hrank
        _ = affineNullity (familyBaseTotal + k) + nullitySlope := by rw [ih]
        _ = affineNullity (familyBaseTotal + Nat.succ k) := by
          rw [affineNullity_base_add, affineNullity_base_add]
          simp only [Nat.mul_succ]
          omega

theorem affineNullity_le_actualNullity_of_base_le
    {L : Nat} (hL : familyBaseTotal ≤ L) :
    affineNullity L ≤ actualNullity L := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hL
  exact (actualNullity_eq_affine_base_add k).ge

theorem affineNullity_le_actualNullity_selected_range
    {L : Nat} (hL : 1772 ≤ L) (hmax : L ≤ 2154) :
    affineNullity L ≤ actualNullity L := by
  apply affineNullity_le_actualNullity_of_base_le
  norm_num [familyBaseTotal] at *
  omega

end ContactAnchoredActualNullity6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredActualNullity6750Research.actualNullity_eq_affine_base_add
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredActualNullity6750Research.affineNullity_le_actualNullity_of_base_le
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredActualNullity6750Research.affineNullity_le_actualNullity_selected_range
