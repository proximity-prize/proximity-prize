import ProximityPrize.SubmissionLower.BCHKSRationalRootVanishing
import ProximityPrize.SubmissionLower.BCHKSHenselSetup
import ProximityPrize.SubmissionLower.BCHKSFiniteHensel

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open RationalFunctions

variable {F : Type} [Field F]

lemma evalEval_monicize_at_leadingCoeff_mul
    (H : F[X][Y]) (hH : 0 < H.natDegree) (z y : F) :
    Polynomial.evalEval z (H.leadingCoeff.eval z * y) (monicize H) =
      (H.leadingCoeff.eval z) ^ (H.natDegree - 1) * Polynomial.evalEval z y H := by
  classical
  let d := H.natDegree
  let W : F := H.leadingCoeff.eval z
  have hdeg : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  have hEvalH : Polynomial.evalEval z y H =
      ∑ i ∈ Finset.range (d + 1), (H.coeff i).eval z * y ^ i := by
    calc
      Polynomial.evalEval z y H = Polynomial.evalEval z y
          (∑ i ∈ Finset.range (H.natDegree + 1),
            Polynomial.monomial i (H.coeff i)) :=
        congrArg (Polynomial.evalEval z y) H.as_sum_range
      _ = ∑ i ∈ Finset.range (d + 1), (H.coeff i).eval z * y ^ i := by
        rw [Polynomial.evalEval_finsetSum]
        simp [Polynomial.evalEval, Polynomial.eval_monomial, d]
  rw [monicize, if_neg hdeg]
  rw [Polynomial.evalEval_add, Polynomial.evalEval_pow, Polynomial.evalEval_X]
  rw [Polynomial.evalEval_finsetSum]
  simp only [Polynomial.evalEval_mul, Polynomial.evalEval_C,
    Polynomial.evalEval_pow, Polynomial.evalEval_X]
  rw [hEvalH, Finset.sum_range_succ]
  change (W * y) ^ d +
      (∑ i ∈ Finset.range d,
        ((H.coeff i * H.leadingCoeff ^ (d - 1 - i)).eval z) * (W * y) ^ i) =
    W ^ (d - 1) *
      ((∑ i ∈ Finset.range d, (H.coeff i).eval z * y ^ i) +
        (H.coeff d).eval z * y ^ d)
  rw [mul_add, Finset.mul_sum]
  have hWcoeff : (H.coeff d).eval z = W := by
    simp [d, W, Polynomial.coeff_natDegree]
  have hsum :
      (∑ i ∈ Finset.range d,
        ((H.coeff i * H.leadingCoeff ^ (d - 1 - i)).eval z) * (W * y) ^ i) =
      ∑ i ∈ Finset.range d, W ^ (d - 1) * ((H.coeff i).eval z * y ^ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hid : i < d := Finset.mem_range.mp hi
    simp only [Polynomial.eval_mul, Polynomial.eval_pow]
    rw [mul_pow]
    have hpow : W ^ (d - 1 - i) * W ^ i = W ^ (d - 1) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    change (H.coeff i).eval z * W ^ (d - 1 - i) * (W ^ i * y ^ i) =
      W ^ (d - 1) * ((H.coeff i).eval z * y ^ i)
    rw [← hpow]
    ring
  have hlead : (W * y) ^ d = W ^ (d - 1) * ((H.coeff d).eval z * y ^ d) := by
    rw [hWcoeff, mul_pow]
    have hpow : W ^ d = W ^ (d - 1) * W := by
      conv_lhs => rw [show d = d - 1 + 1 by omega, pow_add, pow_one]
    rw [hpow]
    ring
  rw [hsum, hlead]
  ring


/-- A common root `(z,y)` of `H` gives the rational root of the integral
monicization used by `piZ`; the monicized coordinate is `W(z) * y`. -/
noncomputable def rationalRootOfPair
    (H : F[X][Y]) (hH : 0 < H.natDegree) (z y : F)
    (hroot : Polynomial.evalEval z y H = 0) :
    RationalFunctions.rationalRoot (monicize H) z :=
  ⟨H.leadingCoeff.eval z * y, by
    rw [evalEval_monicize_at_leadingCoeff_mul H hH z y, hroot, mul_zero]⟩

@[simp] theorem rationalRootOfPair_val
    (H : F[X][Y]) (hH : 0 < H.natDegree) (z y : F)
    (hroot : Polynomial.evalEval z y H = 0) :
    (rationalRootOfPair H hH z y hroot).1 = H.leadingCoeff.eval z * y :=
  rfl

/-- `piZ` sends the polynomial variable `T` in a regular representative to
`W(z)y`. -/
theorem piZ_mk_X_rationalRootOfPair
    (H : F[X][Y]) (hH : 0 < H.natDegree) (z y : F)
    (hroot : Polynomial.evalEval z y H = 0) :
    piZ z (rationalRootOfPair H hH z y hroot)
      (Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X : 𝒪 H) =
      H.leadingCoeff.eval z * y := by
  simp [piZ, piZLift, rationalRootOfPair]


/-- The regular representative used above is exactly `functionFieldT` after
embedding into the function field. -/
theorem embedding_mk_X_eq_functionFieldT (H : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H
      (Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X : 𝒪 H) =
      functionFieldT (H := H) := by
  rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_X]

/-- Consequently the function-field coordinate `T/W`, presented through
`piZOfDiv`, specializes to the original root `y` whenever `W(z) ≠ 0`. -/
theorem piZOfDiv_T_over_W_rationalRootOfPair
    (H : F[X][Y]) (hH : 0 < H.natDegree) (z y : F)
    (hroot : Polynomial.evalEval z y H = 0)
    (hWz : H.leadingCoeff.eval z ≠ 0) :
    piZOfDiv z (rationalRootOfPair H hH z y hroot)
      (Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X : 𝒪 H)
      H.leadingCoeff = y := by
  rw [piZOfDiv, piZ_mk_X_rationalRootOfPair]
  exact mul_div_cancel_left₀ y hWz

/-- Lifted coefficient polynomials specialize by ordinary evaluation. -/
theorem piZOfDiv_mk_C_rationalRootOfPair
    (H : F[X][Y]) (hH : 0 < H.natDegree) (z y : F)
    (hroot : Polynomial.evalEval z y H = 0) (C : F[X]) :
    piZOfDiv z (rationalRootOfPair H hH z y hroot)
      (Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C C) : 𝒪 H) 1 =
      C.eval z := by
  rw [piZOfDiv_one, piZ_mk_C]


/-- The concrete regular representative `xiPre` specializes by direct pair
evaluation; this is the `ξ` numerator used in denominator-cleared lifts. -/
theorem piZ_xi_eq_evalEval
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (monicize H) z) :
    piZ z root (HenselNumerators.xi x₀ R H hHyp) =
      Polynomial.evalEval z root.1 (HenselNumerators.xiPre x₀ R H) := by
  simp [HenselNumerators.xi, piZ, piZLift, Polynomial.evalEval]

/-- Explicit specialization formula for the polynomial denominators occurring
in `ξ`/`β` presentations. -/
theorem piZOfDiv_pow_denominators
    {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z)
    (β : 𝒪 H) (W ξ : F[X]) (a b : ℕ) :
    piZOfDiv z root β (W ^ a * ξ ^ b) =
      piZ z root β / ((W.eval z) ^ a * (ξ.eval z) ^ b) := by
  simp [piZOfDiv, Polynomial.eval_mul, Polynomial.eval_pow]

/-- Powers of the `W` and `ξ` denominators stay away from poles at a good
specialization. -/
theorem eval_pow_denominators_ne_zero
    (W ξ : F[X]) (z : F) (a b : ℕ)
    (hW : W.eval z ≠ 0) (hξ : ξ.eval z ≠ 0) :
    (W ^ a * ξ ^ b).eval z ≠ 0 := by
  simp [Polynomial.eval_mul, Polynomial.eval_pow, hW, hξ]

/-- Exact bridge from specialized `piZOfDiv` coefficients to ordinary Taylor
coefficients.  The finite Hensel uniqueness theorem supplies the final equality
once the specialized cleared presentations form a vanishing lift sequence. -/
theorem piZOfDiv_finiteLift_eq_TaylorCoeff
    {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z)
    (β : ℕ → 𝒪 H) (C : ℕ → F[X])
    (R : F[X][Y]) (P : F[X]) (x₀ y₀ : F) (k : ℕ)
    (hdeg : P.natDegree ≤ k) (hExact : Polynomial.eval P R = 0)
    (hsimple : FiniteHensel.IsSimpleRootAt R x₀ y₀)
    (ha0 : piZOfDiv z root (β 0) (C 0) = y₀)
    (hP0 : P.eval x₀ = y₀)
    (hvanish : FiniteHensel.VanishesThrough
      (FiniteHensel.residual R x₀ (fun n => piZOfDiv z root (β n) (C n)) k) k)
    (n : ℕ) (hn : n ≤ k) :
    piZOfDiv z root (β n) (C n) = FiniteHensel.TaylorCoeff P x₀ n := by
  exact FiniteHensel.lift_eq_TaylorCoeff R P x₀ y₀
    (fun i => piZOfDiv z root (β i) (C i)) k hdeg hExact hsimple ha0 hP0 hvanish n hn

end ProximityPrize.SubmissionLower
