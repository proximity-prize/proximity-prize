import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research

 







namespace ProximityPrize.SubmissionLower.ContactNestedFiveCapSlab6750Research

open scoped Classical BigOperators
open ContactNestedFiveCapCoefficientBox6750Research

set_option autoImplicit false
set_option maxHeartbeats 2000000

 
theorem nestedFiveCap_channel_term_sub
    {Dlow Dhigh w T y r : Nat} (hD : Dlow ≤ Dhigh)
    (hwidth : w * y + (w - 1) * r < Dlow) :
    (T + 1 - y - r) * (Dhigh - w * y - (w - 1) * r) -
        (T + 1 - y - r) * (Dlow - w * y - (w - 1) * r) =
      (Dhigh - Dlow) * (T + 1 - y - r) := by
  rw [← Nat.mul_sub_left_distrib]
  have hinner :
      (Dhigh - w * y - (w - 1) * r) -
          (Dlow - w * y - (w - 1) * r) = Dhigh - Dlow := by
    omega
  rw [hinner, Nat.mul_comm]

 
theorem nestedFiveCapCoefficientCount_sub_eq_slab
    {Dlow Dhigh w T YS S : Nat} (hD : Dlow ≤ Dhigh)
    (hwidth : ∀ y r,
      y < min T YS + 1 →
      r < min S (min (T - y) (YS - y)) + 1 →
      w * y + (w - 1) * r < Dlow) :
    nestedFiveCapCoefficientCount Dhigh w T YS S -
        nestedFiveCapCoefficientCount Dlow w T YS S =
      (Dhigh - Dlow) * nestedFiveCapChannelCount T YS S := by
  unfold nestedFiveCapCoefficientCount nestedFiveCapChannelCount
  rw [← Finset.sum_tsub_distrib]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [← Finset.sum_tsub_distrib]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      exact nestedFiveCap_channel_term_sub hD
        (hwidth y r (Finset.mem_range.mp hy) (Finset.mem_range.mp hr))
    · intro r hr
      exact Nat.mul_le_mul_left _ <|
        Nat.sub_le_sub_right (Nat.sub_le_sub_right hD _) _
  · intro y hy
    apply Finset.sum_le_sum
    intro r hr
    exact Nat.mul_le_mul_left _ <|
      Nat.sub_le_sub_right (Nat.sub_le_sub_right hD _) _

 


theorem nestedFiveCapCoefficientCount_sub_le_slab
    {Dlow Dhigh w T YS S : Nat} (hD : Dlow ≤ Dhigh) :
    nestedFiveCapCoefficientCount Dhigh w T YS S -
        nestedFiveCapCoefficientCount Dlow w T YS S ≤
      (Dhigh - Dlow) * nestedFiveCapChannelCount T YS S := by
  have htotal :
      nestedFiveCapCoefficientCount Dhigh w T YS S ≤
        nestedFiveCapCoefficientCount Dlow w T YS S +
          (Dhigh - Dlow) * nestedFiveCapChannelCount T YS S := by
    unfold nestedFiveCapCoefficientCount nestedFiveCapChannelCount
    rw [Finset.mul_sum]
    calc
      (∑ y ∈ Finset.range (min T YS + 1),
          ∑ r ∈ Finset.range
            (min S (min (T - y) (YS - y)) + 1),
            (T + 1 - y - r) *
              (Dhigh - w * y - (w - 1) * r)) ≤
        ∑ y ∈ Finset.range (min T YS + 1),
          ∑ r ∈ Finset.range
            (min S (min (T - y) (YS - y)) + 1),
            ((T + 1 - y - r) *
                (Dlow - w * y - (w - 1) * r) +
              (Dhigh - Dlow) * (T + 1 - y - r)) := by
        apply Finset.sum_le_sum
        intro y hy
        apply Finset.sum_le_sum
        intro r hr
        rw [Nat.mul_comm (Dhigh - Dlow), ← Nat.mul_add]
        apply Nat.mul_le_mul_left
        omega
      _ =
        (∑ y ∈ Finset.range (min T YS + 1),
          ∑ r ∈ Finset.range
            (min S (min (T - y) (YS - y)) + 1),
            (T + 1 - y - r) *
              (Dlow - w * y - (w - 1) * r)) +
        ∑ y ∈ Finset.range (min T YS + 1),
          ∑ r ∈ Finset.range
            (min S (min (T - y) (YS - y)) + 1),
            (Dhigh - Dlow) * (T + 1 - y - r) := by
        simp only [Finset.sum_add_distrib]
      _ =
        (∑ y ∈ Finset.range (min T YS + 1),
          ∑ r ∈ Finset.range
            (min S (min (T - y) (YS - y)) + 1),
            (T + 1 - y - r) *
              (Dlow - w * y - (w - 1) * r)) +
        ∑ y ∈ Finset.range (min T YS + 1),
          (Dhigh - Dlow) *
            ∑ r ∈ Finset.range
              (min S (min (T - y) (YS - y)) + 1),
              (T + 1 - y - r) := by
        apply congrArg ((∑ y ∈ Finset.range (min T YS + 1),
          ∑ r ∈ Finset.range
            (min S (min (T - y) (YS - y)) + 1),
            (T + 1 - y - r) *
              (Dlow - w * y - (w - 1) * r)) + ·)
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
  apply Nat.sub_le_iff_le_add.mpr
  simpa only [Nat.add_comm] using htotal

 
theorem nestedFiveCap_old_cut_slab_exact :
    nestedFiveCapCoefficientCount 1120251 131071 3884 8 2 -
        nestedFiveCapCoefficientCount 1069437 131071 3884 8 2 =
      4732460262 := by
  rw [nestedFiveCapCoefficientCount_sub_eq_slab (by norm_num)]
  · rw [nestedFiveCapChannelCount_3884_8_2]
  · intro y r hy hr
    omega

 
theorem nestedFiveCap_old_cut_low_count_exact :
    nestedFiveCapCoefficientCount 1069437 131071 3884 8 2 =
      45194486521 := by
  norm_num [nestedFiveCapCoefficientCount, Finset.sum_range_succ]

 
theorem nestedFiveCap_old_cut_low_finrank_exact
    (F : Type*) [Field F] :
    Module.finrank F
        (nestedFiveCapCoefficientBox F 1069437 131071 3884 8 2) =
      45194486521 := by
  rw [nestedFiveCapCoefficientBox_finrank_eq_count,
    nestedFiveCap_old_cut_low_count_exact]

end ProximityPrize.SubmissionLower.ContactNestedFiveCapSlab6750Research

#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapSlab6750Research.nestedFiveCapCoefficientCount_sub_eq_slab
#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapSlab6750Research.nestedFiveCapCoefficientCount_sub_le_slab
#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapSlab6750Research.nestedFiveCap_old_cut_slab_exact
#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapSlab6750Research.nestedFiveCap_old_cut_low_count_exact
#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapSlab6750Research.nestedFiveCap_old_cut_low_finrank_exact
