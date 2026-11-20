import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc


namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped BigOperators

noncomputable section

private theorem map_trunc {L M : Type*} [Field L] [Field M]
    (f : L →+* M) (n : ℕ) (P : PowerSeries L) :
    (PowerSeries.trunc n P).map f = PowerSeries.trunc n (PowerSeries.map f P) := by
  ext i
  simp only [Polynomial.coeff_map, PowerSeries.coeff_trunc, PowerSeries.coeff_map]
  split_ifs <;> simp

private theorem trunc_mul_eval_eq_sum {L : Type*} [Field L]
    (H : PowerSeries L) (P : Polynomial L) (x : L) (n : ℕ) :
    (PowerSeries.trunc n (H * (P : PowerSeries L))).eval x =
      ∑ j ∈ Finset.range n, P.coeff j * (PowerSeries.trunc n (H * PowerSeries.X ^ j)).eval x := by
  classical
  let ev := Polynomial.evalRingHom x
  let incl : Polynomial L →+* PowerSeries L := Polynomial.coeToPowerSeries.ringHom
  have htrunc : PowerSeries.trunc n (P : PowerSeries L) =
      ∑ j ∈ Finset.range n, Polynomial.monomial j (P.coeff j) := by
    rw [PowerSeries.trunc_apply, Nat.Ico_zero_eq_range]
    simp only [Polynomial.coeff_coe]
  calc
    _ = ev (PowerSeries.trunc n (H * incl (PowerSeries.trunc n (P : PowerSeries L)))) := by
      exact congrArg ev (PowerSeries.trunc_mul_trunc H (P : PowerSeries L)).symm
    _ = ∑ j ∈ Finset.range n, ev
        (PowerSeries.trunc n (H * incl (Polynomial.monomial j (P.coeff j)))) := by
      rw [htrunc, map_sum, Finset.mul_sum, map_sum, map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      change (PowerSeries.trunc n (H * (Polynomial.monomial j (P.coeff j) : PowerSeries L))).eval x = _
      rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow,
        show H * (PowerSeries.C (P.coeff j) * PowerSeries.X ^ j) =
          PowerSeries.C (P.coeff j) * (H * PowerSeries.X ^ j) by ring,
        PowerSeries.trunc_C_mul, Polynomial.eval_mul, Polynomial.eval_C]

universe v

theorem exists_taylor_division_weights {L : Type*} [Field L]
    (locator : Polynomial L) (center target : L) (u : ℕ)
    (hcenter : locator.eval center ≠ 0) :
    ∃ c : ℕ → L, ∀ {M : Type v} [Field M] (f : L →+* M) (Q : Polynomial M),
      Q.natDegree ≤ u →
      Q.eval (f target) = ∑ j ∈ Finset.range (u + 1), f (c j) *
        (Polynomial.taylor (f center) (locator.map f * Q)).coeff j := by
  let H : PowerSeries L := (Polynomial.taylor center locator : Polynomial L)
  let V := H⁻¹
  have hH : PowerSeries.constantCoeff H ≠ 0 := by
    simpa only [H, Polynomial.constantCoeff_coe, Polynomial.taylor_coeff_zero] using hcenter
  have hInv : V * H = 1 := PowerSeries.inv_mul_cancel H hH
  refine ⟨fun j => (PowerSeries.trunc (u + 1) (V * PowerSeries.X ^ j)).eval (target - center), ?_⟩
  intro M _ f Q hQ
  let Qshift := Polynomial.taylor (f center) Q
  let P := Polynomial.taylor (f center) (locator.map f * Q)
  have hP : (P : PowerSeries M) = PowerSeries.map f H * (Qshift : PowerSeries M) := by
    simp only [P, Qshift, H, Polynomial.taylor_mul, Polynomial.coe_mul,
      ← Polynomial.polynomial_map_coe, Polynomial.map_taylor]
  have hRecovered : PowerSeries.map f V * (P : PowerSeries M) = (Qshift : PowerSeries M) := by
    rw [hP, ← mul_assoc, ← map_mul, hInv, map_one, one_mul]
  calc
    _ = Qshift.eval (f target - f center) := (Polynomial.taylor_eval_sub _ _ _).symm
    _ = (PowerSeries.trunc (u + 1) (PowerSeries.map f V * (P : PowerSeries M))).eval
        (f target - f center) := by
      rw [hRecovered, PowerSeries.trunc_coe_eq_self]
      simpa only [Qshift, Polynomial.natDegree_taylor] using Nat.lt_succ_of_le hQ
    _ = ∑ j ∈ Finset.range (u + 1), P.coeff j *
        (PowerSeries.trunc (u + 1) (PowerSeries.map f V * PowerSeries.X ^ j)).eval
          (f target - f center) := trunc_mul_eval_eq_sum _ _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have hweight : f ((PowerSeries.trunc (u + 1) (V * PowerSeries.X ^ j)).eval
          (target - center)) = (PowerSeries.trunc (u + 1) (PowerSeries.map f V * PowerSeries.X ^ j)).eval
            (f target - f center) := by
        rw [← Polynomial.eval_map_apply, map_trunc, map_mul, map_pow, PowerSeries.map_X, map_sub]
      rw [hweight, mul_comm]

theorem exists_shortened_affine_weights {L : Type*} [Field L]
    (locator baseline₀ baseline₁ : Polynomial L) (center target target₀ target₁ : L)
    (u : ℕ) (hcenter : locator.eval center ≠ 0) :
    ∃ (weights : ℕ → L) (a b : L),
      ∀ {M : Type v} [Field M] (f : L →+* M) (seed : M) (Φ Q : Polynomial M),
        Q.natDegree ≤ u →
        Φ = baseline₀.map f + Polynomial.C seed * baseline₁.map f + locator.map f * Q →
        (∑ j ∈ Finset.range (u + 1), f (weights j) *
          (Polynomial.taylor (f center) Φ).coeff j) - (f a + seed * f b) =
          Φ.eval (f target) - (f target₀ + seed * f target₁) := by
  obtain ⟨weights, hweights⟩ := exists_taylor_division_weights.{v} locator center target u hcenter
  let evalLocator := locator.eval target
  let baseForm (P : Polynomial L) :=
    ∑ j ∈ Finset.range (u + 1), weights j * (Polynomial.taylor center P).coeff j
  let a := target₀ - baseline₀.eval target + evalLocator * baseForm baseline₀
  let b := target₁ - baseline₁.eval target + evalLocator * baseForm baseline₁
  refine ⟨fun j => evalLocator * weights j, a, b, ?_⟩
  intro M _ f seed Φ Q hQ hΦ
  let form (P : Polynomial M) :=
    ∑ j ∈ Finset.range (u + 1), f (weights j) * (Polynomial.taylor (f center) P).coeff j
  have hform_add (P R : Polynomial M) : form (P + R) = form P + form R := by
    simp only [form, map_add, Polynomial.coeff_add, mul_add, Finset.sum_add_distrib]
  have hform_smul (r : M) (P : Polynomial M) : form (Polynomial.C r * P) = r * form P := by
    simp only [form, Polynomial.taylor_mul, Polynomial.taylor_C, Polynomial.coeff_C_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hform_map (P : Polynomial L) : form (P.map f) = f (baseForm P) := by
    simp only [form, baseForm, map_sum, map_mul, ← Polynomial.map_taylor, Polynomial.coeff_map]
  have hformΦ : form Φ = f (baseForm baseline₀) + seed * f (baseForm baseline₁) +
      Q.eval (f target) := by
    have htail := hweights f Q hQ
    change Q.eval (f target) = form (locator.map f * Q) at htail
    rw [hΦ, hform_add, hform_add, hform_smul, hform_map, hform_map, ← htail]
  have hEvalΦ : Φ.eval (f target) = f (baseline₀.eval target) +
      seed * f (baseline₁.eval target) + f evalLocator * Q.eval (f target) := by
    rw [hΦ]
    simp only [evalLocator, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_map_apply]
  have hscale : (∑ j ∈ Finset.range (u + 1), f (evalLocator * weights j) *
        (Polynomial.taylor (f center) Φ).coeff j) = f evalLocator * form Φ := by
    simp only [form, map_mul, Finset.mul_sum, mul_assoc]
  rw [hscale, hformΦ, hEvalΦ]
  simp only [a, b, map_add, map_sub, map_mul]
  ring

end

end ProximityPrize.SubmissionLower.Koala6831Moving
