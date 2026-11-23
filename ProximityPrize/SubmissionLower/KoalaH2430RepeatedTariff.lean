import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

namespace SplitCut.TwoCutCoverage

theorem repeated_tariff_2430 {s ell k L : ℕ} (hs : s ≤ 133766) (he₀ : 128376 ≤ ell)
    (he₁:ell≤L) (he₂:L≤128642) (hk:k≤5390) :
    (262144-s)*(ell-s+k)≤(179876-s)*(2*(L+2+k)):=by
  have ha:s≤179876:=by omega
  by_cases hse:s≤ell
  · have hsmall : 179876*(ell-s+k) ≤ (179876-s)*(ell+k) := by
      zify [hse,ha]
      nlinarith only [mul_nonneg (show (0 : ℤ) ≤ s by positivity)
        (show (0:ℤ)≤179876-ell-k by omega)]
    refine Nat.le_of_mul_le_mul_left ?_ (by decide:0 < 179876)
    calc
      179876*((262144-s)*(ell-s+k))=(262144-s)*(179876*(ell-s+k)):=by ring
      _≤(262144-s)*((179876-s)*(ell+k)):=Nat.mul_le_mul_left _ hsmall
      _=(179876-s)*((262144-s)*(ell+k)):=by ring
      _ ≤ (179876-s)*((179876*2)*(L+2+k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      _=179876*((179876-s)*(2*(L+2+k))):=by ring
  · rw [Nat.sub_eq_zero_of_le (by omega : ell ≤ s), zero_add]
    have hn:262144-s≤6*(179876-s):=by omega
    calc
      _≤(6*(179876-s))*k:=Nat.mul_le_mul_right _ hn
      _=(179876-s)*(6*k):=by ring
      _≤_:=Nat.mul_le_mul_left _ (by omega)

#print axioms repeated_tariff_2430
end SplitCut.TwoCutCoverage
