import ProximityPrize.SubmissionLower.RelativeTwoResidueCounts6814
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open scoped BigOperators
open RCN100
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem coefficientCount_mono_caps (D w : ℕ) {L L' s s' : ℕ}
    (hL : L≤L') (hs : s≤s') : coefficientCount D w L s≤coefficientCount D w L' s' := by
  unfold coefficientCount
  calc
    _≤∑ i∈Finset.range (L+1), ∑ j∈Finset.range (s+1),
        (L'+1-i-j)*(D-w*i-(w-1)*j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_right _ (by omega)
    _≤∑ i∈Finset.range (L+1), ∑ j∈Finset.range (s'+1),
        (L'+1-i-j)*(D-w*i-(w-1)*j) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
    _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)

theorem coefficientCount_strictMono_cutoff (w L s : ℕ) :
    StrictMono (fun D => coefficientCount D w L s) := by
  intro D D' hD
  unfold coefficientCount
  apply Finset.sum_lt_sum
  · intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.sub_le_sub_right hD.le _) _)
  · refine ⟨0,by simp,?_⟩
    apply Finset.sum_lt_sum
    · intro j _
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.sub_le_sub_right hD.le _) _)
    · refine ⟨0,by simp,?_⟩
      simpa using Nat.mul_lt_mul_of_pos_left hD (by omega : 0<L+1)

theorem multiple_count_lt_source (D w L s nu T R : ℕ) (hD : 0<D) (hnu : 0<nu) :
    coefficientCount (D-nu) w (L-T) (s-R)<coefficientCount D w L s :=
  (coefficientCount_mono_caps (D-nu) w (Nat.sub_le _ _) (Nat.sub_le _ _)).trans_lt
    (coefficientCount_strictMono_cutoff w L s (by omega))

theorem row_test_of_rearranged (source multiple outer inner n : ℕ)
    (hbase : multiple<source) (h : multiple+n*outer<source+n*inner) :
    multiple+n*(outer-inner)<source := by
  by_cases hio : inner≤outer
  · have he := congrArg (fun v : ℕ => n*v) (Nat.sub_add_cancel hio)
    rw [Nat.mul_add] at he
    omega
  · rw [Nat.sub_eq_zero_of_le (by omega : outer ≤ inner),mul_zero,add_zero]
    exact hbase

end ProximityPrize.SubmissionLower.RelativeCertificate6814
