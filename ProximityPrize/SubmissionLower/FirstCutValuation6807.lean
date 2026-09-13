import ProximityPrize.SubmissionLower.ActualSliceMultiplicity6807
/-
UNCOMPILED. First-tail valuation lemma without a first-tail-zero premise.
The coefficients are those of BoundaryTail.refinedMonomial after H-division.
Unlike the later-tail lemma, this is meant for a generic slice, not for a
first-tail curve on which the function is identically zero.
-/
import ProximityPrize.SubmissionLower.BoundaryTailValuation
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field

namespace ProximityPrize.SubmissionLower.FirstCutValuation6807
open scoped BigOperators
set_option autoImplicit false
variable {L : Type*} [Field L]

def normalizedMonomial (n j : ℕ) (sigma J C : L) : L :=
  sigma^(n-1-j)*J^(n-2-2*j)*C

theorem divide_monomial (H G Q : L) (hH : H ≠ 0) (j k : ℕ) :
    (H^j*G^k*Q)/H^(j+k) = (G/H)^k*Q := by
  rw [pow_add,div_pow]
  field_simp [hH]
  <;> ring

theorem divide_refined_sum (n : ℕ) (H G J : L) (C : Fin n → L)
    (hH : H ≠ 0) :
    (∑ j : Fin n, BoundaryTail.refinedMonomial n j.val H G J (C j))/H^(n-1) =
      ∑ j : Fin n, normalizedMonomial n j.val (G/H) J (C j) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val+(n-1-j.val) = n-1 := by omega
  simpa only [hj,BoundaryTail.refinedMonomial,normalizedMonomial,mul_assoc]
    using divide_monomial H G (J^(n-2-2*j.val)*C j) hH j.val (n-1-j.val)

theorem monomial_value_le
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n j : ℕ} (hn : 2 ≤ n) (hj : j < n)
    (sigma J C : L) (delta D M : ℤ) (hdelta : delta ≤ M)
    (hsigma : v sigma ≤ WithZero.exp M) (hJ : v J ≤ WithZero.exp D)
    (hC : v C ≤ WithZero.exp ((j : ℤ)*delta +
      ((min (2*j) (n-2) : ℕ) : ℤ)*D)) :
    v (normalizedMonomial n j sigma J C) ≤
      WithZero.exp (((n-2 : ℕ) : ℤ)*D+((n-1 : ℕ) : ℤ)*M) := by
  have hp (x : L) (e : ℤ) (hx : v x ≤ WithZero.exp e) (k : ℕ) :
      v x^k ≤ WithZero.exp ((k : ℤ)*e) := by
    rw [← nsmul_eq_mul,WithZero.exp_nsmul]
    exact pow_le_pow_left₀ zero_le hx k
  have hsub : ((n-1-j : ℕ) : ℤ)+(j : ℤ) = ((n-1 : ℕ) : ℤ) := by omega
  have hmin : ((n-2-2*j : ℕ) : ℤ)+((min (2*j) (n-2) : ℕ) : ℤ) =
      ((n-2 : ℕ) : ℤ) := by omega
  have hjdelta : (j : ℤ)*delta ≤ (j : ℤ)*M :=
    mul_le_mul_of_nonneg_left hdelta (Nat.cast_nonneg j)
  unfold normalizedMonomial
  simp only [map_mul,map_pow]
  calc
    _ ≤ WithZero.exp (((n-1-j : ℕ) : ℤ)*M)*
        WithZero.exp (((n-2-2*j : ℕ) : ℤ)*D)*
        WithZero.exp ((j : ℤ)*delta+((min (2*j) (n-2) : ℕ) : ℤ)*D) :=
      mul_le_mul' (mul_le_mul' (hp sigma M hsigma _) (hp J D hJ _)) hC
    _ ≤ _ := by
      rw [← WithZero.exp_add,← WithZero.exp_add]
      apply WithZero.exp_le_exp.mpr
      nlinarith [congrArg (fun a : ℤ => a*M) hsub,
        congrArg (fun a : ℤ => a*D) hmin]

theorem first_sum_value_le
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n : ℕ} (hn : 2 ≤ n) (sigma J : L) (C : Fin n → L)
    (delta D M : ℤ) (hdelta : delta ≤ M)
    (hsigma : v sigma ≤ WithZero.exp M) (hJ : v J ≤ WithZero.exp D)
    (hC : ∀ j, v (C j) ≤ WithZero.exp ((j.val : ℤ)*delta+
      ((min (2*j.val) (n-2) : ℕ) : ℤ)*D)) :
    v (∑ j : Fin n, normalizedMonomial n j.val sigma J (C j)) ≤
      WithZero.exp (((n-2 : ℕ) : ℤ)*D+((n-1 : ℕ) : ℤ)*M) := by
  apply v.map_sum_le
  intro j _
  exact monomial_value_le v hn j.isLt sigma J (C j) delta D M
    hdelta hsigma hJ (hC j)

/-- This rewrite has no geometry in it: it identifies the first pure flag. -/
theorem first_pole_flag_identity (w r v z «Z» U T M : ℤ) :
    (w-1)*(z*«Z»+v*T+(r-2)*U)+w*M =
    ((w-1)*z*«Z»+((w-1)*v-w)*T+(w-1)*(r-2)*U)+w*(T+M) := by
  ring

end ProximityPrize.SubmissionLower.FirstCutValuation6807
