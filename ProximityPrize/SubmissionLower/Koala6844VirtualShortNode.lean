import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

theorem isCoprime_local_leading_X_pow (L : Polynomial K) (m : ℕ)
    (hL : L.eval 0 ≠ 0) : IsCoprime L (X^m) := by
  have hd : X ∣ L-C (L.eval 0) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    simp
  obtain ⟨Q,hQ⟩ := hd
  have hc : IsCoprime L (X : Polynomial K) := by
    refine ⟨C (L.eval 0)⁻¹,-C (L.eval 0)⁻¹*Q,?_⟩
    calc
      _ = C (L.eval 0)⁻¹*(L-X*Q) := by ring
      _ = C (L.eval 0)⁻¹*C (L.eval 0) := by rw [← hQ, sub_sub_cancel]
      _ = 1 := by rw [← Polynomial.C_mul, inv_mul_cancel₀ hL, map_one]
  exact hc.pow_right

theorem translated_germ_coefficient_dvd (d0 shift A : Polynomial K)
    (x u v : K) (heq : d0.eval x*u+shift.eval x = v*A.eval x) :
    X ∣ taylor x (d0*C u+shift-C v*A) := by
  rw [Polynomial.X_dvd_iff, Polynomial.taylor_coeff_zero]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C]
  exact sub_eq_zero.mpr heq


end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
