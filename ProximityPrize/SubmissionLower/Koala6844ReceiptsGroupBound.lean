import ProximityPrize.SubmissionLower.Koala6844ReceiptsConvexity

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

theorem le_rounded_mul (D n : Nat) (hD : 0 < D) :
    n ≤ D * ((n + D - 1) / D) := by
  have h := Nat.mod_add_div (n + D - 1) D
  have hmod := Nat.mod_lt (n + D - 1) hD
  omega

private theorem counts_le_rounded (d e c c' n n' : Nat)
    (hd : 0 < d) (he : 0 < e) (hbound : (d * e) * (c+c') ≤ e*n+d*n') :
    c+c' ≤ (n+d-1)/d + (n'+e-1)/e := by
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos hd he)
  calc
    _ ≤ e*n+d*n' := hbound
    _ ≤ e*(d*((n+d-1)/d)) + d*(e*((n'+e-1)/e)) :=
      Nat.add_le_add (Nat.mul_le_mul_left e (le_rounded_mul d n hd))
        (Nat.mul_le_mul_left d (le_rounded_mul e n' he))
    _ = _ := by rw [Nat.mul_add]; ac_rfl

theorem count_le_rateBill (f : Flag) (rate : Rates) (count : Nat)
    (hden : 0 < rate.denominator)
    (hbound : rate.denominator * count ≤ dot f.increments rate.numerator) :
    count ≤ rate.bill f :=
  Nat.le_of_mul_le_mul_left
    (Nat.le_trans hbound (le_rounded_mul _ _ hden)) hden

private theorem weighted_count_pair (d e c c' n n' : Nat)
    (hc : d*c ≤ n) (hc' : e*c' ≤ n') :
    (d*e)*(c+c') ≤ e*n+d*n' := by
  calc
    _ = e*(d*c)+d*(e*c') := by rw [Nat.mul_add]; ac_rfl
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left e hc) (Nat.mul_le_mul_left d hc')

theorem counts_le_endpoint_bills (f : Flag) (left right : Rates)
    (r y otherR otherY lo t hi c c' : Nat)
    (hy : y ≤ lo) (hlo : lo ≤ t) (hhi : t ≤ hi) (hfit : hi + otherY ≤ f.t)
    (hd : 0 < left.denominator) (he : 0 < right.denominator)
    (hleft : left.denominator * c ≤ dot (Flag.mk r y t).increments left.numerator)
    (hright : right.denominator * c' ≤
      dot (Flag.mk otherR otherY (f.t-t)).increments right.numerator) :
    c+c' ≤ max (shortSplitCharge f left right r y otherR otherY lo)
      (shortSplitCharge f left right r y otherR otherY hi) := by
  let leftFixed := (y-r) * left.numerator.middle + r * left.numerator.slope
  let rightFixed := (otherY-otherR) * right.numerator.middle + otherR * right.numerator.slope
  let T := f.t-y-otherY
  let X₀ (s : Nat) := dot (Flag.mk r y s).increments left.numerator
  let X₁ (s : Nat) := dot (Flag.mk otherR otherY (f.t-s)).increments right.numerator
  let X (s : Nat) := right.denominator * X₀ s + left.denominator * X₁ s
  have e₀ (s : Nat) : X₀ s = leftFixed + left.numerator.total*(s-y) := by
    simp only [X₀, dot, Flag.increments, leftFixed]
    ac_rfl
  have e₁ (s : Nat) (hs : y ≤ s) (hs' : s+otherY ≤ f.t) :
      X₁ s = rightFixed + right.numerator.total*(T-(s-y)) := by
    have hsub : f.t-s-otherY = T-(s-y) := by dsimp only [T]; omega
    simp only [X₁, dot, Flag.increments, rightFixed, hsub]
    ac_rfl
  have hzlo : y ≤ lo := hy
  have hzhi : y ≤ hi := by omega
  have hzt : y ≤ t := by omega
  have htt : t+otherY ≤ f.t := by omega
  have htlo : lo+otherY ≤ f.t := by omega
  have hUp : X t ≤ max (X lo) (X hi) := by
    dsimp only [X]
    rw [e₀ t, e₀ lo, e₀ hi, e₁ t hzt htt, e₁ lo hzlo htlo, e₁ hi hzhi hfit]
    apply scaled_affine_sum_le_endpoint
    · omega
    · omega
    · dsimp only [T]; omega
  have hnum : (left.denominator*right.denominator)*(c+c') ≤ X t :=
    weighted_count_pair _ _ _ _ _ _ hleft hright
  rcases Nat.le_total (X lo) (X hi) with hx | hx
  · apply Nat.le_trans _ (Nat.le_max_right _ _)
    have hbound : (left.denominator*right.denominator)*(c+c') ≤ X hi :=
      Nat.le_trans hnum (by simpa only [Nat.max_eq_right hx] using hUp)
    exact counts_le_rounded left.denominator right.denominator c c' (X₀ hi) (X₁ hi)
      hd he hbound
  · apply Nat.le_trans _ (Nat.le_max_left _ _)
    have hbound : (left.denominator*right.denominator)*(c+c') ≤ X lo :=
      Nat.le_trans hnum (by simpa only [Nat.max_eq_left hx] using hUp)
    exact counts_le_rounded left.denominator right.denominator c c' (X₀ lo) (X₁ lo)
      hd he hbound

end ProximityPrize.SubmissionLower.Koala6844Receipts
