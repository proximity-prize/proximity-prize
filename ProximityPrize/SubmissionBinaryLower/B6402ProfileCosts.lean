import ProximityPrize.SubmissionBinaryLower.B6402DimensionBudget

/-! Replace individual local orders by the four Table 4 bins and their
total order above three, including the seed-degree terms in the local cost. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402ProfileCosts
open B6401ContactKerD B6401QuotInterp B6402FilteredJets B6402Moments
open B6402LocalMoments B6402DimensionBudget
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem moment_mono {m n : ℕ} (hm : m≤n) (s : ℕ) : localMoment m s≤localMoment n s := by
  rw [←local_moment,←local_moment,Finset.sum_coe_sort,Finset.sum_coe_sort]
  apply Finset.sum_le_sum_of_subset
  rintro ⟨u,j,a,b⟩ h
  have hi := (mem_localBasisFinset_iff m s u j a b).mp h
  exact (mem_localBasisFinset_iff n s u j a b).mpr ⟨hi.1,by omega,hi.2.2⟩

theorem global_moment_mono (w W W' s : ℕ) (hw : 0<w) (he : W≤W') :
    gMoment w W s≤gMoment w W' s := by
  unfold gMoment
  rw [←global_moment _ _ _ hw,←global_moment _ _ _ hw,Finset.sum_coe_sort,Finset.sum_coe_sort]
  apply Finset.sum_le_sum_of_subset
  rintro ⟨k,r,b,a⟩ h
  have hi := (mem_kerDIdxFinset_iff w W s hw k r b a).mp h
  exact (mem_kerDIdxFinset_iff w W' s hw k r b a).mpr ⟨hi.1,hi.2.1,hi.2.2.trans he⟩

def fee (m s q T H k : ℕ) : ℤ := localSize m s q T-localSize (m-k) (s-1) q (T-H)
def inc (m s T : ℕ) : ℤ := (rankKerD (m-2) (s-1)-rankKerD (m-3) (s-1) : ℕ)*(T+1 : ℤ)

theorem fee_formula (m s q T H k : ℕ) (ht : H≤T) :
    fee m s q T H k =
     ((rankKerD m s : ℤ)-rankKerD (m-k) (s-1))*(T+1)+(H:ℤ)*rankKerD (m-k) (s-1)-
      (q:ℤ)*((localMoment m s:ℤ)-localMoment (m-k) (s-1)) := by
  unfold fee localSize; rw [Nat.cast_sub ht]; ring

theorem tail (m s q T H k : ℕ) (ht : H≤T) (hk : 3≤k) :
    fee m s q T H k ≤ fee m s q T H 3 + (k-3 : ℕ)*inc m s T := by
  let R (i:ℕ) := rankKerD (m-i) (s-1)
  have htop (i : ℕ) : R i≤rankKerD m s := (rankKerD_mono_left (s-1) (Nat.sub_le _ _)).trans (rankKerD_mono_right m (Nat.sub_le _ _))
  have hr : R k≤R 3 := rankKerD_mono_left _ (by omega)
  have hs : R 3≤R 2 := rankKerD_mono_left _ (by omega)
  have b := rankKerD_diff_le_linear_tail m s 1 3 k (by decide) hk
  change rankKerD m s - R k ≤ rankKerD m s - R 3 + (k-3)*((rankKerD m s-R 3)-(rankKerD m s-R 2)) at b
  have he : (rankKerD m s-R 3)-(rankKerD m s-R 2)=R 2-R 3 := by have := htop 2; omega
  rw [he] at b
  have hb := Int.ofNat_le.mpr b
  push_cast [Nat.cast_sub (htop k),Nat.cast_sub (htop 3),Nat.cast_sub hs] at hb
  have rle := Int.ofNat_le.mpr hr
  have ml := Int.ofNat_le.mpr (moment_mono (by omega : m-k≤m-3) (s-1))
  rw [fee_formula _ _ _ _ _ _ ht,fee_formula _ _ _ _ _ _ ht]
  unfold inc; rw [Nat.cast_sub hs]
  dsimp only [R] at hb rle
  have hT : (0:ℤ)≤T+1 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hb hT,
    mul_le_mul_of_nonneg_left rle (Int.natCast_nonneg H),
    mul_le_mul_of_nonneg_left ml (Int.natCast_nonneg q)]

#print axioms tail
end ProximityPrize.SubmissionBinaryLower.B6402ProfileCosts
