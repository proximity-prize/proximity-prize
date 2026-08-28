import ProximityPrize.SubmissionLower.BCHKSResidualSpecialization
import ProximityPrize.SubmissionLower.BCHKSRationalRootBridge

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The data furnished by a selected BCHKS pair, in precisely the form used by
`hensel_initial_value_alignment_final`.  Keeping this package separate makes
clear that no choice of rational roots is left in the alignment argument. -/
structure SelectedHenselData
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX : ℕ) (T : Finset F) (P : T → F[X]) where
  root : ∀ z : T, rationalRoot (monicize H) (z : F)
  hx : ∀ z : T, GoodAt (z:F) (root z) (fieldTo𝕃 (H:=H) x₀) x₀
  hyroot : ∀ z : T, (root z).1 = H.leadingCoeff.eval (z:F) * (P z).eval x₀
  hy : ∀ z : T, GoodAt (z:F) (root z) (initialValue (H:=H)) ((P z).eval x₀)
  hsL : FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
    (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) ≠ 0
  hsimple : ∀ z : T, FiniteHensel.IsSimpleRootAt
    (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀)
  hExact : ∀ z : T, (triSpecializeZ R (z:F)).eval (P z) = 0
  hslope : ∀ z : T, GoodAt (z:F) (root z)
    (FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
      (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
    (FiniteHensel.ySlope (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀))
  hW : ∀ z : T, H.leadingCoeff.eval (z:F) ≠ 0
  hxi : ∀ z : T, Polynomial.evalEval (z:F) (root z).1
    (HenselNumerators.xiPre x₀ R H) ≠ 0
  hden : ∀ t, k < t → t < DX → ∀ z : T,
    piZ (z:F) (root z) (concreteDenRegularBridge x₀ R hHyp t) ≠ 0
  hweight : ∀ t, k < t → t < DX →
    regularWeight (Fact.out : 0 < H.natDegree)
      (concreteBetaUpTo x₀ R hHyp hzeta DX t) D ≤
        (WithBot.some ((2*t+1)*d*D) : WithBot ℕ)

/-- Build selected Hensel data from a factor vanishing and the genuinely
non-pole hypotheses.  The rational root, both elementary good specializations,
simplicity, and the concrete numerator weight are derived here. -/
noncomputable def selectedHenselData_of_pair
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX : ℕ) (T : Finset F) (P : T → F[X])
    (hfactor : ∀ z : T, Polynomial.evalEval (z:F) ((P z).eval x₀) H = 0)
    (hExact : ∀ z : T, (triSpecializeZ R (z:F)).eval (P z) = 0)
    (hsimpleSlope : ∀ z : T, FiniteHensel.ySlope
      (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀) ≠ 0)
    (hsL : FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
      (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) ≠ 0)
    (hslope : ∀ z : T, GoodAt (z:F)
      (rationalRootOfPair H (Fact.out : 0 < H.natDegree) (z:F) ((P z).eval x₀)
        (hfactor z))
      (FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
        (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
      (FiniteHensel.ySlope (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀)))
    (hW : ∀ z : T, H.leadingCoeff.eval (z:F) ≠ 0)
    (hxi : ∀ z : T, Polynomial.evalEval (z:F)
      (H.leadingCoeff.eval (z:F) * (P z).eval x₀)
      (HenselNumerators.xiPre x₀ R H) ≠ 0)
    (hden : ∀ t, k < t → t < DX → ∀ z : T,
      piZ (z:F)
        (rationalRootOfPair H (Fact.out : 0 < H.natDegree) (z:F) ((P z).eval x₀)
          (hfactor z)) (concreteDenRegularBridge x₀ R hHyp t) ≠ 0)
    (hHD : Bivariate.totalDegree H ≤ D)
    (hRD : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (hRdeg_d : Bivariate.natDegreeY R ≤ d) :
    SelectedHenselData x₀ R H hHyp hzeta D d k DX T P := by
  let root : ∀ z : T, rationalRoot (monicize H) (z:F) := fun z =>
    rationalRootOfPair H (Fact.out : 0 < H.natDegree) (z:F) ((P z).eval x₀) (hfactor z)
  have hx : ∀ z : T, GoodAt (z:F) (root z) (fieldTo𝕃 (H:=H) x₀) x₀ :=
    fun z => GoodAt.fieldTo𝕃 (H:=H) (z:F) (root z) x₀
  have hy : ∀ z : T, GoodAt (z:F) (root z) (initialValue (H:=H)) ((P z).eval x₀) := by
    intro z
    have hT : GoodAt (z:F) (root z) (functionFieldT (H:=H))
        (H.leadingCoeff.eval (z:F) * (P z).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X, 1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using (piZ_mk_X_rationalRootOfPair H
          (Fact.out : 0 < H.natDegree) (z:F) ((P z).eval x₀) (hfactor z)).symm
    have hWgood := GoodAt.liftToFunctionField (H:=H) (z:F) (root z) H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ (hW z)] using
      GoodAt.div hT hWgood (hW z)
  refine ⟨root, hx, ?_, hy, hsL, ?_, hExact, hslope, hW, ?_, hden, ?_⟩
  · intro z; rfl
  · intro z
    refine ⟨?_, hsimpleSlope z⟩
    have hz := congrArg (fun q : F[X] => q.eval x₀) (hExact z)
    calc
      _ = (Polynomial.evalRingHom x₀)
          (Polynomial.eval (P z) (triSpecializeZ R (z:F))) := by
        change Polynomial.eval₂ ((Polynomial.evalRingHom x₀).comp (RingHom.id F[X]))
            ((Polynomial.evalRingHom x₀) (P z)) (triSpecializeZ R (z:F)) =
          (Polynomial.evalRingHom x₀)
            (Polynomial.eval₂ (RingHom.id F[X]) (P z) (triSpecializeZ R (z:F)))
        exact (Polynomial.hom_eval₂ (triSpecializeZ R (z:F)) (RingHom.id F[X])
          (Polynomial.evalRingHom x₀) (P z)).symm
      _ = 0 := by simpa using hz
  · intro z; simpa [root] using hxi z
  · intro t _ ht
    rw [concreteBetaUpTo_eq_betaRegular x₀ R hHyp hzeta DX t (Nat.le_of_lt ht)]
    exact ((betaRegular_weight_sharp_yz x₀ R H hHyp hzeta
      (Fact.out : 0 < H.natDegree) hHD hRD hRdeg DX t (Nat.le_of_lt ht)).trans
        (by
          exact_mod_cast (numeratorShapeSharp_le_loose x₀ R H hHyp
            (Fact.out : 0 < H.natDegree) hHD t))).trans
      (WithBot.coe_le_coe.mpr (by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          Nat.mul_le_mul_left ((2*t+1)*D) hRdeg_d))

end ProximityPrize.SubmissionLower
