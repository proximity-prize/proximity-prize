import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Research6966.HelperWindowMoments

open Finset P1_7_1 P1_7_1_3

private theorem product_sum (n a b : ℕ) :
    6 * (∑ i ∈ range n, (a+i)*(b+i)) = productSum6 n a b := by
  induction n with
  | zero => simp [productSum6]
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add, ih]
    cases n with
    | zero => simp [productSum6, Nat.mul_assoc]
    | succ m => simp only [productSum6, Nat.succ_sub_one]; ring

private theorem weight_sum (N a : ℕ) :
    6 * (∑ q ∈ range N, q * ramp a q) = rampWeight6 N a := by
  rw [sum_after (fun q => q * ramp a q) N a
    (fun q hq => by rw [show ramp a q = 0 by unfold ramp; omega, mul_zero])]
  unfold rampWeight6
  rw [← product_sum]
  congr 1
  exact sum_congr rfl fun i _ => by rw [show ramp a (a+i) = 1+i by unfold ramp; omega]

private theorem excess_sum (N k a : ℕ) :
    6 * (∑ q ∈ range N, (q-k) * ramp a q) = rampExcess6 N k a := by
  let s := max (k+1) a
  have hs₁ : k+1 ≤ s := le_max_left _ _
  have hs₂ : a ≤ s := le_max_right _ _
  have hz (q : ℕ) (hq : q < s) : (q-k) * ramp a q = 0 := by
    by_cases h : q ≤ k
    · rw [Nat.sub_eq_zero_of_le h, zero_mul]
    · rw [show ramp a q = 0 by dsimp [s, ramp] at *; omega, mul_zero]
  rw [sum_after (fun q => (q-k) * ramp a q) N s hz]
  change _ = productSum6 (N-s) (s-k) (s+1-a)
  rw [← product_sum]
  congr 1
  exact sum_congr rfl fun i _ => by
    rw [show s+i-k = s-k+i by omega, show ramp a (s+i) = s+1-a+i by unfold ramp; omega]

private theorem prod_cast (n a b : ℕ) :
    (productSum6 n a b : ℤ) =
      6*(n:ℤ)*a*b + 3*((a:ℤ)+b)*n*(n-1) + (n:ℤ)*(n-1)*(2*(n-1)+1) := by
  cases n <;> simp [productSum6, Nat.cast_succ]

private theorem affine_algebra (N H k : ℕ) (hH : H ≤ N) (hk : k < N)
    (r w e : ℤ)
    (hr : r + (rampCount6 N H : ℤ) + rampCount6 N (N-k) =
      (rampCount6 N 0 : ℤ) + 3*((k-H:ℕ):ℤ)*(((k-H:ℕ):ℤ)+1))
    (hw : w + (rampWeight6 N H : ℤ) + rampWeight6 N (N-k) =
      (rampWeight6 N 0 : ℤ) +
        (productSum6 (k-H) (N+H-k) 1 : ℤ))
    (he : e + (rampExcess6 N k H : ℤ) = rampExcess6 N k 0) :
    r*k + e - w =
      3*((N:ℤ)-k)*min k H*(2*(k:ℤ)+1-min k H) := by
  have h₁ : k+1 ≤ N := by omega
  have h₃ : k ≤ N+H := by omega
  have reduce : N - (N-k) = k := by omega
  simp only [rampCount6, rampWeight6, rampExcess6, Nat.sub_zero, max_eq_left (Nat.zero_le (k+1)),
    reduce, prod_cast] at hr hw he
  push_cast [Nat.cast_sub hH, Nat.cast_sub h₁, Nat.cast_sub h₃,
    Nat.cast_sub (Nat.le_of_lt hk)] at hr hw he
  have hR := congrArg (fun x : ℤ => x*k) hr
  clear hr
  by_cases lh : H ≤ k
  · simp only [min_eq_right lh, max_eq_left (show H ≤ k+1 by omega)] at he ⊢
    push_cast [Nat.cast_sub h₁, Nat.cast_sub lh,
      Nat.cast_sub (show H ≤ k+1+1 by omega),
      Nat.cast_sub (show k ≤ k+1 by omega)] at hR hw he
    linear_combination hR + he - hw
  · have kl : k ≤ H := by omega
    simp only [min_eq_left kl, max_eq_right (show k+1 ≤ H by omega),
      Nat.sub_eq_zero_of_le kl] at hR hw he ⊢
    push_cast [Nat.cast_sub hH, Nat.cast_sub kl,
      Nat.cast_sub (show H ≤ H+1 by omega),
      Nat.cast_sub (show k ≤ k+1 by omega)] at hR hw he
    linear_combination hR + he - hw

theorem cutOffset_affine (B J t k : ℕ) (lower : J ≤ t) (upper : t < B)
    (cut : k = t-J+1) :
    6 * cutOffset B J t k =
      3 * (B+1-k) * min k (J+1) * (2*k+1-min k (J+1)) := by
  let N := B+1
  let H := J+1
  have hN : H ≤ N := by dsimp [H,N]; omega
  have hk : k < N := by dsimp [N]; omega
  have hrow (q : ℕ) :
      pivotCount B J t q + ramp H q + ramp (N-k) q =
        ramp 0 q + ramp (N+H-k) q := by
    unfold pivotCount columnCount ramp
    dsimp [N,H]
    omega
  have hcolumn (q : ℕ) : columnCount B J t q + ramp H q = ramp 0 q := by
    unfold columnCount ramp
    dsimp [H]
    omega
  have pivot (f stat : ℕ → ℕ) (hs : ∀ a,
      6 * (∑ q ∈ range N, f q * ramp a q) = stat a) :
      6 * (∑ q ∈ range N, f q * pivotCount B J t q) + stat H + stat (N-k) =
        stat 0 + stat (N+H-k) := by
    simp only [← hs, ← Nat.mul_add, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun q _ => by simp only [hrow]
  have rank := pivot (fun _ => 1) (rampCount6 N) (by intro a; simpa only [one_mul] using ramp_count N a)
  simp only [one_mul, N, pivot_rank] at rank
  have weight := pivot id (rampWeight6 N) (weight_sum N)
  simp only [id_eq, N, pivot_weight] at weight
  have ex : excess6 B J t k + rampExcess6 N k H = rampExcess6 N k 0 := by
    rw [← column_excess, ← excess_sum, ← excess_sum, ← Nat.mul_add, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun q _ => by rw [← Nat.mul_add, hcolumn]
  have drop₁ : N - (N+H-k) = k-H := by omega
  have rankZ := congrArg (fun x : ℕ => (x:ℤ)) rank
  have weightZ := congrArg (fun x : ℕ => (x:ℤ)) weight
  have excessZ := congrArg (fun x : ℕ => (x:ℤ)) ex
  push_cast at rankZ weightZ excessZ
  have rankZ' : (pivotRank6 B J t : ℤ) + (rampCount6 N H : ℤ) + rampCount6 N (N-k) =
      (rampCount6 N 0 : ℤ) + 3*((k-H:ℕ):ℤ)*(((k-H:ℕ):ℤ)+1) := by
    have last : (rampCount6 N (N+H-k) : ℤ) = 3*((k-H:ℕ):ℤ)*(((k-H:ℕ):ℤ)+1) := by
      unfold rampCount6
      rw [drop₁]
      push_cast
      rfl
    rw [← last]
    exact rankZ
  have weightZ' : (pivotWeight6 B J t : ℤ) + (rampWeight6 N H : ℤ) + rampWeight6 N (N-k) =
      (rampWeight6 N 0 : ℤ) + (productSum6 (k-H) (N+H-k) 1 : ℤ) := by
    have last : (rampWeight6 N (N+H-k) : ℤ) = (productSum6 (k-H) (N+H-k) 1 : ℤ) := by
      unfold rampWeight6
      rw [drop₁]
    rw [← last]
    exact weightZ
  have formula := affine_algebra N H k hN hk _ _ _ rankZ' weightZ' excessZ
  let target := 3 * (N-k) * min k H * (2*k+1-min k H)
  have hm : min k H ≤ 2*k+1 := by have := min_le_left k H; omega
  have signed : (pivotRank6 B J t : ℤ)*k + excess6 B J t k - pivotWeight6 B J t =
      (target : ℤ) := by
    simpa [target, Nat.cast_sub (Nat.le_of_lt hk), Nat.cast_sub hm] using formula
  have order : pivotWeight6 B J t ≤ pivotRank6 B J t*k+excess6 B J t k := by
    have hnon : (0 : ℤ) ≤ target := by positivity
    exact_mod_cast (show (pivotWeight6 B J t : ℤ) ≤ (pivotRank6 B J t : ℤ)*k + excess6 B J t k by omega)
  unfold cutOffset
  rw [← pivot_rank, ← pivot_weight, ← column_excess]
  rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_sub_left_distrib, Nat.mul_div_cancel_left _ (by decide)]
  rw [Nat.mul_sub_left_distrib, Nat.mul_add, ← Nat.mul_assoc, pivot_rank, pivot_weight, column_excess]
  exact_mod_cast (by simpa [Nat.cast_sub order] using signed :
    ((pivotRank6 B J t*k+excess6 B J t k-pivotWeight6 B J t : ℕ):ℤ) = target)

end Research6966.HelperWindowMoments
