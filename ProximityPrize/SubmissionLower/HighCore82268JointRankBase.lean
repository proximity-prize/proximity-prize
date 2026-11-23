import ProximityPrize.SubmissionLower.UpperBranch4

set_option Elab.async false

namespace HighCore82268JointRank

open Finset
open K1_14_2 (Ambient)
open P1_7_4 (Mass dotQ massQ weightedBill bill_bound)




/-- Linear bound for the nonlinear fixed-jet fee. -/
theorem fixed_fee_linear (L mu tau pivot : ℚ) (hL : 0 ≤ L) (hmu : 0 ≤ mu)
    (htau : 0 ≤ tau) (htau' : tau ≤ 1) {B J Bmax Jmax : ℕ}
    (hJB : J ≤ B) (hB : B ≤ Bmax) (hJ : J ≤ Jmax) :
    let a := mu + 2*L*(B-1 : ℕ)
    let v := min a (L*(2*J-1 : ℕ))
    ((((B-J : ℕ) : ℚ)*v + J*a).ceil.toNat + B^2 : ℕ) ≤
      ((4*L*Bmax*tau+mu-4*L*pivot)*J + (4*L*Jmax*(1-tau)+Bmax)*B+2*L*pivot^2+1 : ℚ) := by
  dsimp only
  let a := mu + 2*L*(B-1 : ℕ)
  let v := min a (L*(2*J-1 : ℕ))
  let q : ℚ := ((B-J : ℕ) : ℚ)*v + J*a
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hv : 0 ≤ v := le_min ha (by positivity)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb0 : (0 : ℚ) ≤ B := Nat.cast_nonneg _
  have hj0 : (0 : ℚ) ≤ J := Nat.cast_nonneg _
  have hb : (B : ℚ) ≤ Bmax := by exact_mod_cast hB
  have hj : (J : ℚ) ≤ Jmax := by exact_mod_cast hJ
  have hqceil : 0 ≤ q.ceil := by
    have h : (0 : ℚ) ≤ (q.ceil : ℚ) := hq.trans Rat.le_ceil
    exact_mod_cast h
  have hc : ((q.ceil.toNat : ℕ) : ℚ) ≤ q + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hqceil]
    exact Rat.ceil_lt.le
  have hva : v ≤ 2*L*J := by
    have hd : ((2*J-1 : ℕ) : ℚ) ≤ 2*J := by exact_mod_cast Nat.sub_le (2*J) 1
    exact (min_le_right _ _).trans (by nlinarith only [mul_le_mul_of_nonneg_left hd hL])
  have haa : a ≤ mu + 2*L*B := by
    have hd : ((B-1 : ℕ) : ℚ) ≤ B := by exact_mod_cast Nat.sub_le B 1
    dsimp [a]
    nlinarith only [mul_le_mul_of_nonneg_left hd hL]
  have hfirst : ((B-J : ℕ) : ℚ)*v ≤ ((B : ℚ)-J)*(2*L*J) := by
    rw [Nat.cast_sub hJB]
    exact mul_le_mul_of_nonneg_left hva (sub_nonneg.mpr (by exact_mod_cast hJB))
  have hsecond := mul_le_mul_of_nonneg_left haa hj0
  have hq' : q ≤ 4*L*B*J + mu*J - 2*L*J^2 := by
    dsimp [q]
    linarith only [hfirst,hsecond]
  have hleft := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*L*tau*J by positivity)
  have hright := mul_le_mul_of_nonneg_left hj
    (show 0 ≤ 4*L*(1-tau)*B by positivity)
  have hsq := mul_le_mul_of_nonneg_left hb hb0
  have htan : -2*L*(J : ℚ)^2 ≤ -4*L*pivot*J + 2*L*pivot^2 := by
    nlinarith only [mul_nonneg hL (sq_nonneg ((J : ℚ)-pivot))]
  change ((q.ceil.toNat + B^2 : ℕ) : ℚ) ≤ _
  push_cast
  nlinarith only [hq', hc, hleft, hright, hsq, htan]

#print axioms fixed_fee_linear

end HighCore82268JointRank
