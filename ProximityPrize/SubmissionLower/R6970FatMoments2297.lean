import ProximityPrize.SubmissionLower.R6970FatMomentsBase

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace R6970FatMoments2297
open R6970FatMoments
open Finset K1_13_4_2 K1_13_4_2_1

theorem total_room : sumJets (fun k j i => 6820-(i+j+k)) = 21445461275685 := by
  have reflect : sumJets (fun k j i => 6820-(i+j+k)) = sumJets (fun _ _ i => i) := by
    unfold sumJets
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    convert Finset.sum_range_reflect (fun i : ℕ => i) (6821-k-j) using 1
    apply Finset.sum_congr rfl
    intro i hi
    change 6820 - (i+j+k) = 6821 - k - j - 1 - i
    omega
  apply reflect.trans
  simpa only [Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add] using
    from_moment 0 0 1 0 21445461275685 (by decide +kernel)

private theorem add_three (f g h : ℕ → ℕ → ℕ → ℕ)
    (value : ∀ k < 1151, ∀ j < 2301-2*k, ∀ i < 6821-k-j, f k j i + g k j i = h k j i) :
    sumJets f + sumJets g = sumJets h := by
  unfold sumJets
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    value k (mem_range.mp hk) j (mem_range.mp hj) i (mem_range.mp hi)

private theorem complement (k j : ℕ) (hk : k < 1151) (hj : j < 2301-2*k) :
    2300-(j+2*k)+(j+2*k)=2300 := by omega

private theorem index_add :
    sumJets (fun k j _ => 2300-(j+2*k)) + sumJets (fun k j _ => j+2*k)
      = sumJets (fun _ _ _ => 2300) :=
  add_three (fun k j _ => 2300-(j+2*k)) (fun k j _ => j+2*k) (fun _ _ _ => 2300)
    (fun k hk j hj _ _ => complement k j hk hj)

private theorem index_spent : sumJets (fun k j _ => j+2*k) = 11226084124875 := by
  simpa only [Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add] using
    from_moment 0 1 0 0 11226084124875 (by decide +kernel)

private theorem left_of_total {a b c u v : ℕ} (h : a+b=c) (hb : b=u) (hc : c=v+u) :
    a=v := by omega

theorem index_room : sumJets (fun k j _ => 2300-(j+2*k)) = 6053692758425 :=
  left_of_total (a := sumJets (fun k j _ => 2300-(j+2*k)))
    (b := sumJets (fun k j _ => j+2*k)) (c := sumJets (fun _ _ _ => 2300))
    (u := 11226084124875) (v := 6053692758425) index_add index_spent
    (const_moment 2300 (6053692758425+11226084124875) (by decide +kernel))

theorem seed_room : sumJets (fun _ _ _ => ∑ z ∈ range 35201, (35200 - z)) =
    4654552825571809600 := by
  have reflect := Finset.sum_range_reflect (fun z : ℕ => z) 35201
  change (∑ z ∈ range 35201, (35200-z)) = ∑ z ∈ range 35201, z at reflect
  have subtotal : (∑ z ∈ range 35201, (35200-z)) = 619537600 :=
    reflect.trans ((Finset.sum_range_id 35201).trans (by decide))
  exact (congrArg (fun n : ℕ => sumJets (fun _ _ _ => n)) subtotal).trans
    (const_moment 619537600 4654552825571809600 (by decide +kernel))

theorem with_seed (f : ℕ → ℕ → ℕ → ℕ) :
    (∑ k ∈ range 1151, ∑ j ∈ range (2301-2*k), ∑ i ∈ range (6821-k-j),
       ∑ _z ∈ range 35201, f k j i) = 35201 * sumJets f := by
  simp only [sumJets, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Finset.mul_sum]

end R6970FatMoments2297

#print axioms R6970FatMoments2297.total_room
#print axioms R6970FatMoments2297.index_room
#print axioms R6970FatMoments2297.seed_room
