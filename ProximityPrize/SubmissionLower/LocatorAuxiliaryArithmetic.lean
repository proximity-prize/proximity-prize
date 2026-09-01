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

theorem smallBox_coefficientCount (L s:ℕ):
    RCN100.coefficientCount 50637 131071 L s=(L+1)*50637:=by
  rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
    50637 131071 L s 1 (by omega) (by decide)]
  rw [show Finset.range 1={0} by decide]
  simp only [Finset.sum_singleton,Nat.sub_zero]
  apply Finset.sum_eq_single 0
  · intro j hj hj0
    have hj1:1≤j:=Nat.one_le_iff_ne_zero.mpr hj0
    have hz:50637-131070*j=0:=Nat.sub_eq_zero_of_le (by omega)
    simp only [hz,Nat.mul_zero]
  · simp

private theorem rankStep93:rankStep 93 27=94164:=by decide
private theorem coefficientStep93:
    coefficientStep 16898751 131071 27 129=24780570234:=by decide
private theorem baseRank93:RCN119.localRankBound 93 2671 27=247773596:=by decide
private theorem baseGap93:
    RCN100.coefficientCount 16898751 131071 2671 27-
      262144*RCN119.localRankBound 93 2671 27=82546527:=by
  rw [baseRank93,RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
    16898751 131071 2671 27 129 (by decide) (by decide)]
  decide
theorem source93_gap_affine (L:ℕ) (hL:2671≤L):
    RCN100.coefficientCount 16898751 131071 L 27-
      262144*RCN119.localRankBound 93 L 27=
        96042618*L-256447286151:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hL
  induction d with
  | zero=>simpa using baseGap93
  | succ d ih=>
    have hc:=coefficientCount_succ_large 16898751 131071 (2671+d) 27 129
      (by omega) (by decide) (by omega)
    have hr:=localRankBound_succ_large 93 (2671+d) 27 (by omega)
    rw [coefficientStep93] at hc
    rw [rankStep93] at hr
    rw [Nat.add_succ,hc,hr]
    omega
theorem source93_shape:16898751+27≤131071*(128+1):=by decide
theorem source93_capacity_one:
    16898751-50637≤(93-1)*181707+(131071-1):=by decide
theorem source93_capacity_two:
    16898751-2*50637≤(93-2)*181707+2*(131071-1):=by decide

private theorem rankStep126:rankStep 126 39=242300:=by decide
private theorem coefficientStep126:
    coefficientStep 22895082 131071 39 175=63880268480:=by decide
private theorem baseRank126:RCN119.localRankBound 126 2600 39=616596360:=by decide
private theorem baseGap126:
    RCN100.coefficientCount 22895082 131071 2600 39-
      262144*RCN119.localRankBound 126 2600 39=59364009370:=by
  rw [baseRank126,RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
    22895082 131071 2600 39 175 (by decide) (by decide)]
  decide
theorem source126_gap_affine (L:ℕ) (hL:2600≤L):
    RCN100.coefficientCount 22895082 131071 L 39-
      262144*RCN119.localRankBound 126 L 39=
        362777280*L-883856918630:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hL
  induction d with
  | zero=>simpa using baseGap126
  | succ d ih=>
    have hc:=coefficientCount_succ_large 22895082 131071 (2600+d) 39 175
      (by omega) (by decide) (by omega)
    have hr:=localRankBound_succ_large 126 (2600+d) 39 (by omega)
    rw [coefficientStep126] at hc
    rw [rankStep126] at hr
    rw [Nat.add_succ,hc,hr]
    omega
theorem source126_shape:22895082+39≤131071*(174+1):=by decide
theorem source126_capacity_one:
    22895082-50637≤(126-1)*181707+(131071-1):=by decide
theorem source126_capacity_two:
    22895082-2*50637≤(126-2)*181707+2*(131071-1):=by decide
theorem source126_capacity_three:
    22895082-3*50637=(126-3)*181707+3*(131071-1):=by decide
theorem source126_capacity_four:
    22895082-4*50637=(126-4)*181707+4*(131071-1):=by decide
end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
