import ProximityPrize.SubmissionLower.BCHKSConcreteNumerators
import ProximityPrize.SubmissionLower.BCHKSPairLiftVanishing
import ProximityPrize.SubmissionLower.BCHKSRationalRootBridge

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]

/-- The concrete regular numerator, extended by zero outside the finite lift
range so it can be supplied to the simultaneous root-vanishing theorem. -/
noncomputable def concreteBetaUpTo
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0) (N t : ℕ) : 𝒪 H :=
  if ht : t ≤ N then betaRegular x₀ R H hHyp hzeta N t ht else 0

lemma concreteBetaUpTo_eq_betaRegular
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0) (N t : ℕ) (ht : t ≤ N) :
    concreteBetaUpTo x₀ R hHyp hzeta N t =
      betaRegular x₀ R H hHyp hzeta N t ht := by
  simp only [concreteBetaUpTo, dif_pos ht]

/-- Exact middle-coefficient vanishing for the concrete finite Hensel lift at
BCHKS's numerical cutoffs.  Numerator regularity is supplied by
`betaRegular`; only the denominator presentation and its weight bound remain
explicit inputs. -/
theorem concreteFiniteAlpha_middle_vanish
    [Fintype F] {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d e : ℕ) (hD : Bivariate.totalDegree H ≤ D)
    (C : ℕ → F[X])
    (hembed : ∀ t, 131071 < t → t < 111624646 →
      embeddingOf𝒪Into𝕃 H (concreteBetaUpTo x₀ R hHyp hzeta 111624646 t) =
        finiteAlpha (R := R) (H := H) x₀ 111624646 t *
          liftToFunctionField (H := H) (C t))
    (hC : ∀ t, 131071 < t → t < 111624646 → C t ≠ 0)
    (hweight : ∀ t, 131071 < t → t < 111624646 →
      regularWeight (Fact.out : 0 < H.natDegree)
          (concreteBetaUpTo x₀ R hHyp hzeta 111624646 t) D ≤
        (WithBot.some ((2 * t + 1) * d * D) : WithBot ℕ))
    (T : Finset F)
    (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (hden : ∀ t, 131071 < t → t < 111624646 →
      ∀ z : T, (C t).eval (z : F) ≠ 0)
    (hspecialize : ∀ t, 131071 < t → t < 111624646 → ∀ z : T,
      piZOfDiv (z : F) (root z)
        (concreteBetaUpTo x₀ R hHyp hzeta 111624646 t) (C t) = 0)
    (hcard : 2 * 111624646 * H.natDegree * d * D + e + 1 < T.card) :
    ∀ t, 131071 < t → t < 111624646 →
      finiteAlpha (R := R) (H := H) x₀ 111624646 t = 0 := by
  exact functionField_middle_coefficients_eq_zero_of_many_pair_roots
    (Fact.out : 0 < H.natDegree) D d 131071 111624646 e hD
    (finiteAlpha (R := R) (H := H) x₀ 111624646)
    (concreteBetaUpTo x₀ R hHyp hzeta 111624646) C
    hembed hC hweight T root hden hspecialize hcard

/-- A polynomial of degree `< DX` is zero if its coefficients agree below
`DX` with a finite residual that vanishes through `DX`.  This is the final
weighted-X-cap step after replacing the middle lift coefficients by zero. -/
theorem eval_truncSeries_eq_zero_of_residual_match_and_cap
    {L : Type} [Field L] (Q : L[X]) (res : L[X]) (DX : ℕ)
    (hres : FiniteHensel.VanishesThrough res DX)
    (hmatch : ∀ n, n < DX → Q.coeff n = res.coeff n)
    (hcap : Q.natDegree < DX) : Q = 0 := by
  ext n
  by_cases hn : n < DX
  · rw [hmatch n hn, hres n hn.le]
    simp
  · have hQ : Q.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hcap.trans_le (Nat.le_of_not_gt hn))
    simp [hQ]

/-- Form the truncated BCHKS lift `γ` and conclude that it is an exact root of
the mapped relation.  `hmatch` is the support/weighted-X-cap interface: below
`DX`, evaluation at `γ` has the same coefficients as the finite residual. -/
theorem concreteFiniteLift_trunc_exact
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (α : ℕ → 𝕃 H)
    (hres : FiniteHensel.VanishesThrough
      (FiniteHensel.residual (liftedR (R := R) (H := H))
        (fieldTo𝕃 (H := H) x₀) α 111624646) 111624646)
    (hmatch : ∀ n, n < 111624646 →
      ((liftedR (R := R) (H := H)).eval
        (FiniteHensel.truncSeries α 131071)).coeff n =
      (FiniteHensel.residual (liftedR (R := R) (H := H))
        (fieldTo𝕃 (H := H) x₀) α 111624646).coeff n)
    (hcap : ((liftedR (R := R) (H := H)).eval
      (FiniteHensel.truncSeries α 131071)).natDegree < 111624646) :
    (liftedR (R := R) (H := H)).eval
      (FiniteHensel.truncSeries α 131071) = 0 := by
  exact eval_truncSeries_eq_zero_of_residual_match_and_cap _ _ 111624646
    hres hmatch hcap


/-- Concrete specialization of `concreteFiniteLift_trunc_exact` to the
coefficients produced by `FiniteHensel.liftCoeff`. -/
theorem concreteFiniteAlpha_trunc_exact
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hres : FiniteHensel.VanishesThrough
      (FiniteHensel.residual (liftedR (R := R) (H := H))
        (fieldTo𝕃 (H := H) x₀)
        (finiteAlpha (R := R) (H := H) x₀ 111624646) 111624646) 111624646)
    (hmatch : ∀ n, n < 111624646 →
      ((liftedR (R := R) (H := H)).eval
        (FiniteHensel.truncSeries
          (finiteAlpha (R := R) (H := H) x₀ 111624646) 131071)).coeff n =
      (FiniteHensel.residual (liftedR (R := R) (H := H))
        (fieldTo𝕃 (H := H) x₀)
        (finiteAlpha (R := R) (H := H) x₀ 111624646) 111624646).coeff n)
    (hcap : ((liftedR (R := R) (H := H)).eval
      (FiniteHensel.truncSeries
        (finiteAlpha (R := R) (H := H) x₀ 111624646) 131071)).natDegree < 111624646) :
    (liftedR (R := R) (H := H)).eval
      (FiniteHensel.truncSeries
        (finiteAlpha (R := R) (H := H) x₀ 111624646) 131071) = 0 := by
  exact concreteFiniteLift_trunc_exact x₀ R
    (finiteAlpha (R := R) (H := H) x₀ 111624646) hres hmatch hcap

/-- On a good specialization, finite-Hensel uniqueness identifies the
specialized cleared lift with ordinary Taylor coefficients; truncating through
`k` therefore gives the shifted polynomial itself. -/
theorem specialized_truncSeries_eq_shift
    {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z)
    (β : ℕ → 𝒪 H) (C : ℕ → F[X])
    (R : F[X][Y]) (P : F[X]) (x₀ y₀ : F) (k : ℕ)
    (hdeg : P.natDegree ≤ k) (hExact : R.eval P = 0)
    (hsimple : FiniteHensel.IsSimpleRootAt R x₀ y₀)
    (ha0 : piZOfDiv z root (β 0) (C 0) = y₀)
    (hP0 : P.eval x₀ = y₀)
    (hvanish : FiniteHensel.VanishesThrough
      (FiniteHensel.residual R x₀ (fun n => piZOfDiv z root (β n) (C n)) k) k) :
    FiniteHensel.truncSeries (fun n => piZOfDiv z root (β n) (C n)) k =
      P.comp (Polynomial.C x₀ + Polynomial.X) := by
  rw [← FiniteHensel.truncSeries_TaylorCoeff_eq_shift P x₀ k hdeg]
  ext n
  by_cases hn : n ≤ k
  · rw [FiniteHensel.coeff_truncSeries _ _ _ hn,
      FiniteHensel.coeff_truncSeries _ _ _ hn]
    exact piZOfDiv_finiteLift_eq_TaylorCoeff z root β C R P x₀ y₀ k
      hdeg hExact hsimple ha0 hP0 hvanish n hn
  · simp [FiniteHensel.truncSeries, hn]

end ProximityPrize.SubmissionLower
