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
    coefficientStep 13079376 131071 21 100=11681528573:=by decide
private theorem baseRank72:RCN119.localRankBound 72 5289 21=233977436:=by decide
private theorem baseGap72:
    RCN100.coefficientCount 13079376 131071 5289 21-
      262144*RCN119.localRankBound 72 5289 21=407231:=by
  rw [baseRank72,RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
    13079376 131071 5289 21 100 (by decide) (by decide)]
  decide
theorem auxiliary72_gap_affine (L:ℕ) (hL:5289≤L):
    RCN100.coefficientCount 13079376 131071 L 21-
      262144*RCN119.localRankBound 72 L 21=17431293*L-92193701446:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hL
  induction d with
  | zero=>simpa using baseGap72
  | succ d ih=>
    have hc:=coefficientCount_succ_large 13079376 131071 (5289+d) 21 100
      (by omega) (by decide) (by omega)
    have hr:=localRankBound_succ_large 72 (5289+d) 21 (by omega)
    rw [coefficientStep72] at hc
    rw [rankStep72] at hr
    rw [Nat.add_succ,hc,hr]
    omega
theorem auxiliary72_nullity:
    RCN100.coefficientCount 13079376 131071 36564 21-
      262144*RCN119.localRankBound 72 36564 21=545164095806:=by
  rw [auxiliary72_gap_affine 36564 (by decide)]
private theorem rankStep150:rankStep 163 48=501270:=by decide
private theorem coefficientStep150:
    coefficientStep 29610254 131071 48 226=132205845373:=by decide
private theorem baseRank150:RCN119.localRankBound 163 3016 48=1476331290:=by decide
private theorem baseGap150:
    RCN100.coefficientCount 29610254 131071 3016 48-
      262144*RCN119.localRankBound 163 3016 48=164552682:=by
  rw [baseRank150,RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
    29610254 131071 3016 48 226 (by decide) (by decide)]
  decide
theorem auxiliary150_gap_affine (L:ℕ) (hL:3016≤L):
    RCN100.coefficientCount 29610254 131071 L 48-
      262144*RCN119.localRankBound 163 L 48=800922493*L-2415417686206:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hL
  induction d with
  | zero=>simpa using baseGap150
  | succ d ih=>
    have hc:=coefficientCount_succ_large 29610254 131071 (3016+d) 48 226
      (by omega) (by decide) (by omega)
    have hr:=localRankBound_succ_large 163 (3016+d) 48 (by omega)
    rw [coefficientStep150] at hc
    rw [rankStep150] at hr
    rw [Nat.add_succ,hc,hr]
    omega
theorem auxiliary72_shape:13079376 + 21 ≤ 131071 * (99 + 1):=by decide
theorem auxiliary72_capacity:
    13079376 - 50588 ≤ (72 - 1) * 181658 + (131071 - 1):=by decide
theorem auxiliary150_shape:29610254 + 48 ≤ 131071 * (225 + 1):=by decide
theorem auxiliary150_capacity:
    29610254 - 50588 ≤ (163 - 1) * 181658 + (131071 - 1):=by decide
theorem auxiliary150_double_capacity:
    29610254 - 2 * 50588 ≤
      (163 - 2) * 181658 + 2 * (131071 - 1):=by decide
end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
