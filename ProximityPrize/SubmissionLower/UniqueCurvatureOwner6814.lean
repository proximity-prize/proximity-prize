import ProximityPrize.SubmissionLower.ContactPencilDirection6814
namespace ProximityPrize.SubmissionLower.UniqueCurvatureOwner6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial

variable {E : Type*} [Field E]

theorem rootMultiplicity_power (j : Polynomial E) (t : E) (e : ℕ)
    (hj : j ≠ 0) : (j^e).rootMultiplicity t = e * j.rootMultiplicity t := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hj) hj), ih]
    ring

theorem unique_owner_order_le (j q : Polynomial E) (t : E) (d e : ℕ)
    (hj : j ≠ 0) (hq : q.eval t ≠ 0)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ j^e*q) :
    d ≤ e*j.rootMultiplicity t := by
  have hq0 : q ≠ 0 := by
    intro hz
    exact hq (by rw [hz]; simp)
  have hprod : j^e*q ≠ 0 := mul_ne_zero (pow_ne_zero _ hj) hq0
  have hm := (Polynomial.le_rootMultiplicity_iff hprod).mpr hd
  rw [Polynomial.rootMultiplicity_mul hprod,rootMultiplicity_power j t e hj,
    Polynomial.rootMultiplicity_eq_zero hq,add_zero] at hm
  exact hm

open RCN095

end
end ProximityPrize.SubmissionLower.UniqueCurvatureOwner6814
