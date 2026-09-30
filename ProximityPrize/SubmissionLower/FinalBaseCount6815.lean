import ProximityPrize.SubmissionLower.FinalBaseCheck6815
import ProximityPrize.SubmissionLower.PackingOwnData6815
namespace ProximityPrize.SubmissionLower.FinalBaseCount6815
open scoped BigOperators
open FinalBaseCheck6815 PackingData6815 PackingSemantics6815
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem count {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r v z count : ι → ℕ) (cap : ℕ)
    (hr : ∀ i∈s, 1≤r i)
    (hR : (∑ i∈s,r i)≤39) (hy : (∑ i∈s,r i)+(∑ i∈s,v i)≤182)
    (ht : (∑ i∈s,r i)+(∑ i∈s,v i)+(∑ i∈s,z i)≤11192)
    (hsingle : ∀ i∈s, count i≤SingletonData6815.cap (r i) (v i) (z i))
    (hb : BaseBound (∑ i∈s,r i) (∑ i∈s,v i) (∑ i∈s,z i) cap) :
    (∑ i∈s,count i)≤cap := by
  have individual (i : ι) (hi : i∈s) :
      r i≤39 ∧ r i+v i≤182 ∧ r i+v i+z i≤11192 := by
    have hri := Finset.single_le_sum (fun k _ => Nat.zero_le (r k)) hi
    have hvi := Finset.single_le_sum (fun k _ => Nat.zero_le (v k)) hi
    have hzi := Finset.single_le_sum (fun k _ => Nat.zero_le (z k)) hi
    omega
  rcases hb with ⟨j,hj,hbudget⟩ | ⟨hr10,hr19,hv70,hzero,hheavy⟩
  · apply (AffineFactorAggregate6808.sum_count_le 39 182 (full_slope j)
      (lookup (full_own j)) (lookup (full_packed j)) (full_bellman j hj)
      s r v z count hr hR hy ?_).trans hbudget
    intro i hi
    have h := individual i hi
    exact (hsingle i hi).trans (PackingOwnCheck6815.full_sound (r i) (v i) (z i)
      (hr i hi) h.1 h.2.1 h.2.2 (PackingOwnData6815.checked _ _ (hr i hi) h.1 h.2.1) j hj)
  · apply RectangularPacking6815.one_heavy 10 19 70 cap s r v z count
      (fun j : Fin 14 => light_slope j.val)
      (fun j : Fin 14 => lookup (light_own j.val))
      (fun j : Fin 14 => lookup (light_packed j.val)) SingletonData6815.cap
      hr hr19 hv70 (by omega) (fun j => light_bellman j.val j.isLt) ?_ hsingle ?_ ?_
    · intro i hi hlight j
      have h := individual i hi
      have hvi := Finset.single_le_sum (fun k _ => Nat.zero_le (v k)) hi
      exact (hsingle i hi).trans (PackingOwnCheck6815.light_sound (r i) (v i) (z i)
        (hr i hi) hlight (by omega) h.2.2 (PackingOwnData6815.checked _ _ (hr i hi) h.1 h.2.1) j.val j.isLt)
    · obtain ⟨j,hj,hbudget⟩ := hzero
      exact ⟨⟨j,hj⟩,hbudget⟩
    · intro q u hq hqr hu
      obtain ⟨j,hj,hbudget⟩ := hheavy q u hq hqr hu
      exact ⟨⟨j,hj⟩,hbudget⟩

end ProximityPrize.SubmissionLower.FinalBaseCount6815
