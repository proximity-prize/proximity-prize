import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1

set_option Elab.async false

namespace Research6966.HelperWindowMoments

open P1_7_1_3

private theorem late_ramp_count (N a : ℕ) (ha : a ≤ N) :
    (rampCount6 N a : ℤ) = 3*((N : ℤ)-a)*((N : ℤ)-a+1) := by
  simp only [rampCount6, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_sub ha]

private theorem late_ramp_weight_diff (a d : ℕ) :
    (productSum6 d a 1 : ℤ) =
      3*(a : ℤ)*d*(d+1) + 2*(d : ℤ)*(d-1)*(d+1) := by
  cases d with
  | zero => simp [productSum6]
  | succ d =>
    simp only [productSum6, Nat.succ_sub_one, Nat.cast_add, Nat.cast_mul, Nat.cast_succ]
    ring

private theorem late_ramp_weight (N a : ℕ) (ha : a ≤ N) :
    (rampWeight6 N a : ℤ) =
      3*(a : ℤ)*((N : ℤ)-a)*((N : ℤ)-a+1) +
        2*((N : ℤ)-a)*((N : ℤ)-a-1)*((N : ℤ)-a+1) := by
  unfold rampWeight6
  rw [late_ramp_weight_diff, Nat.cast_sub ha]

private theorem late_pivot_rank (N e p : ℕ) (hN : e+1 ≤ N) (hp : p ≤ e+1) :
    rampCount6 N 0 + rampCount6 N (e+1) -
      (rampCount6 N p + rampCount6 N (e+1-p)) = 6*(p*(e+1-p)) := by
  have h : rampCount6 N 0 + rampCount6 N (e+1) =
      rampCount6 N p + rampCount6 N (e+1-p) + 6*(p*(e+1-p)) := by
    have hcast : ((rampCount6 N 0 + rampCount6 N (e+1) : ℕ) : ℤ) =
        ((rampCount6 N p + rampCount6 N (e+1-p) + 6*(p*(e+1-p)) : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [late_ramp_count N 0 (Nat.zero_le _), late_ramp_count N (e+1) hN,
        late_ramp_count N p (hp.trans hN),
        late_ramp_count N (e+1-p) ((Nat.sub_le _ _).trans hN), Nat.cast_sub hp]
      push_cast
      ring
    exact_mod_cast hcast
  rw [h, Nat.add_sub_cancel_left]

private theorem late_pivot_weight (N e p : ℕ) (he : 1 ≤ e) (hN : e+1 ≤ N) (hp : p ≤ e+1) :
    rampWeight6 N 0 + rampWeight6 N (e+1) -
      (rampWeight6 N p + rampWeight6 N (e+1-p)) = 3*(p*(e+1-p))*(e-1) := by
  have h : rampWeight6 N 0 + rampWeight6 N (e+1) =
      rampWeight6 N p + rampWeight6 N (e+1-p) + 3*(p*(e+1-p))*(e-1) := by
    have hcast : ((rampWeight6 N 0 + rampWeight6 N (e+1) : ℕ) : ℤ) =
        ((rampWeight6 N p + rampWeight6 N (e+1-p) + 3*(p*(e+1-p))*(e-1) : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [late_ramp_weight N 0 (Nat.zero_le _), late_ramp_weight N (e+1) hN,
        late_ramp_weight N p (hp.trans hN),
        late_ramp_weight N (e+1-p) ((Nat.sub_le _ _).trans hN), Nat.cast_sub hp, Nat.cast_sub he]
      push_cast
      ring
    exact_mod_cast hcast
  rw [h, Nat.add_sub_cancel_left]

private theorem late_product_shift (n b w : ℕ) :
    productSum6 n 1 (b+w) = productSum6 n 1 b + 3*w*n*(n+1) := by
  cases n with
  | zero => simp [productSum6]
  | succ n =>
    simp only [productSum6, Nat.succ_sub_one]
    ring

private theorem late_excess (B k w : ℕ) (hw : w ≤ k+1) :
    rampExcess6 (B+1) k 0 - rampExcess6 (B+1) k w =
      3*w*(B-k)*(B-k+1) := by
  unfold rampExcess6
  rw [max_eq_left (Nat.zero_le _), max_eq_left hw]
  have hd : B+1-(k+1) = B-k := by omega
  have h1 : k+1-k = 1 := by omega
  have h2 : k+1+1 = (k+1+1-w)+w := by omega
  simp only [hd, h1, Nat.sub_zero]
  conv_lhs => arg 1; arg 3; rw [h2]
  rw [late_product_shift, Nat.add_sub_cancel_left]

theorem cutOffset_late_value (B J t k : ℕ) (hshape : 2*J ≤ B) (hlo : B ≤ t)
    (hhi : t < B+2*J) (_hk : k ≤ B) (hw : min (J+1) (B+2*J-t) ≤ k+1) :
    let e := B+2*J-t
    let w := min (J+1) e
    let p := (e+1)/2
    let R := p*(e+1-p)
    cutOffset B J t k = (2*R*k + w*(B-k)*(B-k+1) - R*(e-1))/2 := by
  let e := B+2*J-t
  let w := min (J+1) e
  let p := (e+1)/2
  let R := p*(e+1-p)
  change cutOffset B J t k = (2*R*k + w*(B-k)*(B-k+1) - R*(e-1))/2
  have he : 1 ≤ e := by dsimp [e]; omega
  have hN : e+1 ≤ B+1 := by dsimp [e]; omega
  have hp : p ≤ e+1 := by dsimp [p]; omega
  have low_eq : low J t = 0 := by unfold low; omega
  have width_eq : width B J t = w := by unfold width high; rw [low_eq]; dsimp [w, e]; omega
  have peak_eq : peak B J t = p := by
    unfold peak
    rw [width_eq, low_eq, Nat.sub_zero]
    change min w p = p
    apply min_eq_right
    dsimp [w, p, e]
    omega
  have hRank : pivotRank6 B J t = 6*R := by
    simp only [pivotRank6, pivotVolume6, low_eq, peak_eq, Nat.zero_add]
    exact late_pivot_rank (B+1) e p hN hp
  have hWeight : pivotWeight6 B J t = 3*R*(e-1) := by
    simp only [pivotWeight6, pivotVolume6, low_eq, peak_eq, Nat.zero_add]
    exact late_pivot_weight (B+1) e p he hN hp
  have hExcess : excess6 B J t k = 3*w*(B-k)*(B-k+1) := by
    simp only [excess6, columnVolume6, low_eq, width_eq, Nat.zero_add]
    exact late_excess B k w hw
  unfold cutOffset
  rw [hRank, hWeight, hExcess]
  have hnumerator : 6*R*k + 3*w*(B-k)*(B-k+1) - 3*R*(e-1) =
      3*(2*R*k + w*(B-k)*(B-k+1) - R*(e-1)) := by
    calc
      _ = 3*(2*R*k + w*(B-k)*(B-k+1)) - 3*(R*(e-1)) := by congr 1 <;> ring
      _ = _ := by conv_rhs => rw [Nat.mul_sub_left_distrib]
  rw [hnumerator]
  omega

end Research6966.HelperWindowMoments
