import ProximityPrize.SubmissionLower.BCHKSResidualSpecialization
import ProximityPrize.SubmissionLower.BCHKSRegularDenSpecialization
import ProximityPrize.SubmissionLower.BCHKSDoubleCounting
import ProximityPrize.SubmissionLower.BCHKSAffineConclusion
import ProximityPrize.SubmissionLower.BCHKSPairSetup

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- End-to-end Hensel/alignment core after factor and good-pair selection.
All geometric selection assumptions are explicit.  In particular, coefficient
specialization is *not* an assumption: it is derived from the synchronized
residual specialization and finite-Hensel uniqueness.  `hfiber` is only the
final quotient/adjoin-root specialization plumbing. -/
theorem hensel_alignment_core
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    [Fact (Irreducible (mapBivariateToRatFunc H))]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX e : ℕ) (hkDX : k ≤ DX) (hHD : Bivariate.totalDegree H ≤ D)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (P : T → F[X])
    (hPdeg : ∀ z : T, (P z).natDegree ≤ k)
    (hx : ∀ z : T, GoodAt (z:F) (root z)
      (fieldTo𝕃 (H:=H) x₀) x₀)
    (hy : ∀ z : T, GoodAt (z:F) (root z) (initialValue (H:=H))
      ((P z).eval x₀))
    (hsL : FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
      (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) ≠ 0)
    (hsimple : ∀ z : T, FiniteHensel.IsSimpleRootAt
      (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀))
    (hExact : ∀ z : T, (triSpecializeZ R (z:F)).eval (P z) = 0)
    (hslope : ∀ z : T, GoodAt (z:F) (root z)
      (FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
        (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
      (FiniteHensel.ySlope (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀)))
    (hW : ∀ z : T, H.leadingCoeff.eval (z:F) ≠ 0)
    (hxi : ∀ z : T,
      Polynomial.evalEval (z:F) (root z).1 (HenselNumerators.xiPre x₀ R H) ≠ 0)
    (hden : ∀ t, k < t → t < DX → ∀ z : T,
      piZ (z:F) (root z) (concreteDenRegularBridge x₀ R hHyp t) ≠ 0)
    (hweight : ∀ t, k < t → t < DX →
      regularWeight (Fact.out : 0 < H.natDegree)
        (concreteBetaUpTo x₀ R hHyp hzeta DX t) D ≤
          (WithBot.some ((2*t+1)*d*D) : WithBot ℕ))
    (hcard : 2*DX*H.natDegree*d*D + e + 1 < T.card)
    (γ : (AdjoinedRootField H)[X]) (A : Finset F)
    (hAcard : k+1 ≤ A.card) (U₀ U₁ : F → F)
    (hγdeg : γ.natDegree ≤ k)
    (hγeval : ∀ x ∈ A, γ.eval (baseToAdjoined H x) =
      baseToAdjoined H (U₀ x) + adjoinedAlpha H * baseToAdjoined H (U₁ x))
    (hfiber : ∀ p₀ p₁ : F[X], p₀.natDegree ≤ k → p₁.natDegree ≤ k →
      γ = p₀.map (baseToAdjoined H) +
        Polynomial.C (adjoinedAlpha H) * p₁.map (baseToAdjoined H) →
      ∀ z : T, P z = p₀ + Polynomial.C (z:F) * p₁) :
    (∀ t, k < t → t < DX → finiteAlpha (R:=R) (H:=H) x₀ DX t = 0) ∧
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      γ = p₀.map (baseToAdjoined H) +
        Polynomial.C (adjoinedAlpha H) * p₁.map (baseToAdjoined H) ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z:F) * p₁ := by
  have hspecializes : ∀ z : T, ∀ n, n ≤ DX →
      concreteSpecializedAlpha x₀ R hHyp hzeta DX (z:F) (root z) n =
        FiniteHensel.TaylorCoeff (P z) x₀ n := by
    intro z n hn
    apply concreteSpecializedAlpha_eq_TaylorCoeff x₀ R hHyp hzeta DX
      (z:F) (root z) x₀ ((P z).eval x₀) (P z)
      (hx z) (hy z) hsL (hsimple z) rfl
      (hPdeg z |>.trans hkDX) (hExact z) (hslope z) (hW z) (hxi z) n hn
  have hmiddle : ∀ t, k < t → t < DX →
      finiteAlpha (R:=R) (H:=H) x₀ DX t = 0 := by
    apply concreteFiniteAlpha_middle_vanish_regularDen x₀ R hHyp hzeta
      D d k DX e hHD T root P (fun _ => x₀) hPdeg hspecializes hden hweight hcard
  refine ⟨hmiddle, ?_⟩
  obtain ⟨E, hEA, hEcard, hp₀deg, hp₁deg, hγ⟩ :=
    adjoinedRoot_polynomial_eq_affine_of_many_evals H γ k A hAcard U₀ U₁ hγdeg hγeval
  let p₀ : F[X] := Lagrange.interpolate E id U₀
  let p₁ : F[X] := Lagrange.interpolate E id U₁
  exact ⟨p₀, p₁, hp₀deg, hp₁deg, hγ, hfiber p₀ p₁ hp₀deg hp₁deg hγ⟩

end ProximityPrize.SubmissionLower
