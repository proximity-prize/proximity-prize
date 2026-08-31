import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
private theorem blockInputCount_succ_large (M L s:ℕ) (h:M+s≤L):
    RCN119.blockInputCount M (L+1) s=
      RCN119.blockInputCount M L s+(M+1)*(s+1):=by
  unfold RCN119.blockInputCount
  calc
    (∑ i∈Finset.range (M+1),∑ j∈Finset.range (s+1),(L+1+1-i-j))=
        ∑ i∈Finset.range (M+1),∑ j∈Finset.range (s+1),
          ((L+1-i-j)+1):=by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hi hj
      omega
    _=(∑ i∈Finset.range (M+1),∑ j∈Finset.range (s+1),(L+1-i-j))+
        (∑ i∈Finset.range (M+1),∑ _j∈Finset.range (s+1),1):=by
      simp only [Finset.sum_add_distrib]
    _=(∑ i∈Finset.range (M+1),∑ j∈Finset.range (s+1),(L+1-i-j))+
        (M+1)*(s+1):=by simp
private theorem blockKernelLowerBound_succ_large (M L s h:ℕ) (hML:M+s≤L):
    RCN119.blockKernelLowerBound M (L+1) s h=
      RCN119.blockKernelLowerBound M L s h+(M+1-h)*(s+1-h):=by
  unfold RCN119.blockKernelLowerBound
  calc
    (∑ i∈Finset.range (M+1-h),∑ j∈Finset.range (s+1-h),
      (L+1+1-h-i-j))=
        ∑ i∈Finset.range (M+1-h),∑ j∈Finset.range (s+1-h),
          ((L+1-h-i-j)+1):=by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hi hj
      omega
    _=(∑ i∈Finset.range (M+1-h),∑ j∈Finset.range (s+1-h),
        (L+1-h-i-j))+
        (∑ i∈Finset.range (M+1-h),∑ _j∈Finset.range (s+1-h),1):=by
      simp only [Finset.sum_add_distrib]
    _=(∑ i∈Finset.range (M+1-h),∑ j∈Finset.range (s+1-h),
        (L+1-h-i-j))+(M+1-h)*(s+1-h):=by simp
private theorem blockKernelLowerBound_le_blockInputCount (M L s h:ℕ):
    RCN119.blockKernelLowerBound M L s h≤RCN119.blockInputCount M L s:=by
  unfold RCN119.blockKernelLowerBound RCN119.blockInputCount
  calc
    (∑ i∈Finset.range (M+1-h),∑ j∈Finset.range (s+1-h),(L+1-h-i-j))≤
      ∑ i∈Finset.range (M+1-h),∑ j∈Finset.range (s+1-h),(L+1-i-j):=by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        omega
    _≤∑ i∈Finset.range (M+1-h),∑ j∈Finset.range (s+1),(L+1-i-j):=by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum_of_subset
        (Finset.range_mono (Nat.sub_le (s+1) h))
    _≤∑ i∈Finset.range (M+1),∑ j∈Finset.range (s+1),(L+1-i-j):=by
      exact Finset.sum_le_sum_of_subset
        (Finset.range_mono (Nat.sub_le (M+1) h))
private theorem contactRankBound_succ_large (M L s h:ℕ) (hML:M+s≤L):
    RCN119.contactRankBound M (L+1) s h=
      RCN119.contactRankBound M L s h+
        ((M+1)*(s+1)-(M+1-h)*(s+1-h)):=by
  rw [RCN119.contactRankBound,RCN119.contactRankBound,
    blockInputCount_succ_large M L s hML,
    blockKernelLowerBound_succ_large M L s h hML]
  have hki:=blockKernelLowerBound_le_blockInputCount M L s h
  have hks:=blockKernelLowerBound_le_blockInputCount M (L+1) s h
  have hinc:(M+1-h)*(s+1-h)≤(M+1)*(s+1):=
    Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  omega
private def rankStep (m s:ℕ):ℕ:=
  ∑ r∈Finset.range m,((r+1)*(s+1)-
    (r+1-min (r+1) (m-r))*(s+1-min (r+1) (m-r)))
private theorem localRankBound_succ_large (m L s:ℕ) (hml:m+s≤L):
    RCN119.localRankBound m (L+1) s=RCN119.localRankBound m L s+rankStep m s:=by
  unfold RCN119.localRankBound rankStep
  calc
    (∑ r∈Finset.range m,RCN119.contactRankBound (min r (L+1)) (L+1) s
      (min (r+1) (m-r)))=
      ∑ r∈Finset.range m,
        (RCN119.contactRankBound (min r L) L s (min (r+1) (m-r))+
          ((r+1)*(s+1)-(r+1-min (r+1) (m-r))*(s+1-min (r+1) (m-r)))):=by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_range] at hr
      have hrL:r≤L:=by omega
      have hrLs:r+s≤L:=by omega
      rw [Nat.min_eq_left hrL,Nat.min_eq_left (hrL.trans (Nat.le_add_right L 1))]
      exact contactRankBound_succ_large r L s (min (r+1) (m-r)) hrLs
    _=(∑ r∈Finset.range m,RCN119.contactRankBound (min r L) L s
        (min (r+1) (m-r)))+
      ∑ r∈Finset.range m,
        ((r+1)*(s+1)-(r+1-min (r+1) (m-r))*(s+1-min (r+1) (m-r))):=by
      simp only [Finset.sum_add_distrib]
private def coefficientStep (D w s t:ℕ):ℕ:=
  ∑ i∈Finset.range t,∑ j∈Finset.range (s+1),(D-w*i-(w-1)*j)
private theorem coefficientCount_succ_large (D w L s t:ℕ)
    (ht:t≤L+1) (hD:D≤w*t) (hroom:t+s≤L+2):
    RCN100.coefficientCount D w (L+1) s=
      RCN100.coefficientCount D w L s+coefficientStep D w s t:=by
  rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
      D w (L+1) s t (by omega) hD,
    RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff D w L s t ht hD]
  unfold coefficientStep
  calc
    (∑ i∈Finset.range t,∑ j∈Finset.range (s+1),
      (L+1+1-i-j)*(D-w*i-(w-1)*j))=
      ∑ i∈Finset.range t,∑ j∈Finset.range (s+1),
        ((L+1-i-j)*(D-w*i-(w-1)*j)+(D-w*i-(w-1)*j)):=by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hi hj
      have hstep:L+1+1-i-j=(L+1-i-j)+1:=by omega
      rw [hstep,Nat.add_mul,one_mul]
    _=(∑ i∈Finset.range t,∑ j∈Finset.range (s+1),
        (L+1-i-j)*(D-w*i-(w-1)*j))+
      ∑ i∈Finset.range t,∑ j∈Finset.range (s+1),
        (D-w*i-(w-1)*j):=by simp only [Finset.sum_add_distrib]
private theorem rankStep72:rankStep 72 21=44495:=by decide
private theorem coefficientStep72:
    coefficientStep 13084992 131071 21 100=11692586477:=by decide
private theorem baseRank72:RCN119.localRankBound 72 3257 21=143563596:=by decide
private theorem baseGap72:
    RCN100.coefficientCount 13084992 131071 3257 21-
      262144*RCN119.localRankBound 72 3257 21=3737327:=by
  rw [baseRank72,RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
    13084992 131071 3257 21 100 (by decide) (by decide)]
  decide
theorem auxiliary72_gap_affine (L:ℕ) (hL:3257≤L):
    RCN100.coefficientCount 13084992 131071 L 21-
      262144*RCN119.localRankBound 72 L 21=28489197*L-92785577302:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hL
  induction d with
  | zero=>simpa using baseGap72
  | succ d ih=>
    have hc:=coefficientCount_succ_large 13084992 131071 (3257+d) 21 100
      (by omega) (by decide) (by omega)
    have hr:=localRankBound_succ_large 72 (3257+d) 21 (by omega)
    rw [coefficientStep72] at hc
    rw [rankStep72] at hr
    rw [Nat.add_succ,hc,hr]
    omega
private theorem rankStep126:rankStep 126 39=242300:=by decide
private theorem coefficientStep126:
    coefficientStep 22898736 131071 39 175=63902996360:=by decide
private theorem baseRank126:RCN119.localRankBound 126 2299 39=543664060:=by decide
private theorem baseGap126:
    RCN100.coefficientCount 22898736 131071 2299 39-
      262144*RCN119.localRankBound 126 2299 39=252987610:=by
  rw [baseRank126,RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
    22898736 131071 2299 39 175 (by decide) (by decide)]
  decide
theorem auxiliary126_gap_affine (L:ℕ) (hL:2299≤L):
    RCN100.coefficientCount 22898736 131071 L 39-
      262144*RCN119.localRankBound 126 L 39=385505160*L-886023375230:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hL
  induction d with
  | zero=>simpa using baseGap126
  | succ d ih=>
    have hc:=coefficientCount_succ_large 22898736 131071 (2299+d) 39 175
      (by omega) (by decide) (by omega)
    have hr:=localRankBound_succ_large 126 (2299+d) 39 (by omega)
    rw [coefficientStep126] at hc
    rw [rankStep126] at hr
    rw [Nat.add_succ,hc,hr]
    omega
theorem auxiliary72_shape:13084992 + 21 ≤ 131071 * (99 + 1):=by decide
theorem auxiliary72_capacity:
    13084992 - 50666 ≤ (72 - 1) * 181736 + (131071 - 1):=by decide
theorem auxiliary126_shape:22898736 + 39 ≤ 131071 * (174 + 1):=by decide
theorem auxiliary126_capacity:
    22898736 - 50666 ≤ (126 - 1) * 181736 + (131071 - 1):=by decide
theorem auxiliary126_double_capacity:
    22898736 - 2 * 50666 ≤
      (126 - 2) * 181736 + 2 * (131071 - 1):=by decide
end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
