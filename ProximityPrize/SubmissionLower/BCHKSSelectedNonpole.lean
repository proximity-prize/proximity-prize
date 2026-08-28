import ProximityPrize.SubmissionLower.BCHKSSelectedHenselData

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

lemma PolyGoodAt.derivative {H : F[X][Y]} [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] {z : F} {root : rationalRoot (monicize H) z}
    {p : (𝕃 H)[X]} {q : F[X]} (h : PolyGoodAt z root p q) :
    PolyGoodAt z root p.derivative q.derivative := by
  intro i
  simpa [Polynomial.coeff_derivative] using
    (GoodAt.mul (h (i+1))
      (GoodAt.liftToFunctionField (H:=H) z root (Polynomial.C (i+1))))


lemma BiPolyGoodAt.derivative {H : F[X][Y]} [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] {z : F} {root : rationalRoot (monicize H) z}
    {p : (𝕃 H)[X][Y]} {q : F[X][Y]} (h : BiPolyGoodAt z root p q) :
    BiPolyGoodAt z root p.derivative q.derivative := by
  intro j
  simpa [Polynomial.coeff_derivative] using
    (PolyGoodAt.mul (h (j+1))
      (PolyGoodAt.C (GoodAt.liftToFunctionField (H:=H) z root (Polynomial.C (j+1)))))

/-- The lifted `Y`-slope specializes to the finite `Y`-slope at any
pair of good specialization values. -/
lemma selectedSlopeGoodAt
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (z : F)
    (root : rationalRoot (monicize H) z) (x y : F)
    (hx : GoodAt z root (fieldTo𝕃 (H:=H) x₀) x)
    (hy : GoodAt z root (initialValue (H:=H)) y) :
    GoodAt z root
      (FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
        (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
      (FiniteHensel.ySlope (triSpecializeZ R z) x y) := by
  unfold FiniteHensel.ySlope
  have he := PolyGoodAt.comp
    (BiPolyGoodAt.eval
      (BiPolyGoodAt.derivative (liftedR_goodAt_triSpecializeZ R z root))
      (PolyGoodAt.C hy)) (PolyGoodAt.C hx)
  have hcommL : Polynomial.eval₂ (Polynomial.evalRingHom (fieldTo𝕃 (H:=H) x₀))
        (initialValue (H:=H)) (Polynomial.derivative (liftedR (R:=R) (H:=H))) =
      Polynomial.eval (fieldTo𝕃 (H:=H) x₀)
        (Polynomial.eval (Polynomial.C (initialValue (H:=H)))
          (Polynomial.derivative (liftedR (R:=R) (H:=H)))) := by
    induction Polynomial.derivative (liftedR (R:=R) (H:=H)) using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a => simp
  have hcomm : Polynomial.eval₂ (Polynomial.evalRingHom x) y
        (Polynomial.derivative (triSpecializeZ R z)) =
      Polynomial.eval x (Polynomial.eval (Polynomial.C y)
        (Polynomial.derivative (triSpecializeZ R z))) := by
    induction Polynomial.derivative (triSpecializeZ R z) using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a => simp
  rw [hcommL, hcomm]
  simpa using he 0

/-- A nonzero finite specialized slope forces the generic slope scalar `zeta`
to be nonzero. -/
theorem zeta_ne_zero_of_selected_slope
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (z : F)
    (root : rationalRoot (monicize H) z) (x y : F)
    (hx : GoodAt z root (fieldTo𝕃 (H:=H) x₀) x)
    (hy : GoodAt z root (initialValue (H:=H)) y)
    (hsimple : FiniteHensel.ySlope (triSpecializeZ R z) x y ≠ 0) :
    zeta R x₀ H ≠ 0 := by
  intro hzeta
  have hslope := selectedSlopeGoodAt x₀ R z root x y hx hy
  rw [ySlope_liftedR_eq_zeta, hzeta] at hslope
  have hzero := GoodAt.zero (H:=H) z root
  have := GoodAt.value_unique hslope hzero
  exact hsimple this

/-- All non-pole facts attached to one selected ordinary simple root. -/
structure SelectedNonpoleData
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (z : F)
    (root : rationalRoot (monicize H) z) (x y : F) : Prop where
  hsL : FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
    (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) ≠ 0
  hslope : GoodAt z root
    (FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
      (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
    (FiniteHensel.ySlope (triSpecializeZ R z) x y)
  hxi : Polynomial.evalEval z root.1 (xiPre x₀ R H) ≠ 0
  hden : ∀ t, piZ z root (concreteDenRegularBridge x₀ R hHyp t) ≠ 0

/-- Simplicity and avoidance of the leading coefficient automatically imply
all selected non-pole hypotheses. -/
theorem selectedNonpoleData
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H)
    (hzeta : zeta R x₀ H ≠ 0) (z : F)
    (root : rationalRoot (monicize H) z) (x y : F)
    (hx : GoodAt z root (fieldTo𝕃 (H:=H) x₀) x)
    (hy : GoodAt z root (initialValue (H:=H)) y)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hsimple : FiniteHensel.ySlope (triSpecializeZ R z) x y ≠ 0) :
    SelectedNonpoleData x₀ R H hHyp z root x y := by
  have hsL : FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
      (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) ≠ 0 := by
    simpa [ySlope_liftedR_eq_zeta] using hzeta
  have hslope := selectedSlopeGoodAt x₀ R z root x y hx hy
  have hxi : Polynomial.evalEval z root.1 (xiPre x₀ R H) ≠ 0 := by
    have hWgood := GoodAt.liftToFunctionField (H:=H) z root H.leadingCoeff
    have hp : GoodAt z root
        ((liftToFunctionField (H:=H) H.leadingCoeff) ^ (R.natDegree - 2) *
          FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
            (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
        ((H.leadingCoeff.eval z) ^ (R.natDegree - 2) *
          FiniteHensel.ySlope (triSpecializeZ R z) x y) :=
      GoodAt.mul (GoodAt.pow hWgood _) hslope
    have hmk : GoodAt z root
        (embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk _ (xiPre x₀ R H) : 𝒪 H))
        (Polynomial.evalEval z root.1 (xiPre x₀ R H)) := by
      refine ⟨Ideal.Quotient.mk _ (xiPre x₀ R H), 1, by simp, by simp, ?_⟩
      simp [piZ, piZLift, Polynomial.evalEval]
    have hp' := hp
    rw [ySlope_liftedR_eq_zeta,
      ← embeddingOf𝒪Into𝕃_mk_xiPre x₀ R H hHyp] at hp'
    have hv := GoodAt.value_unique hmk hp'
    rw [hv]
    exact mul_ne_zero (pow_ne_zero _ hW) hsimple
  refine ⟨hsL, hslope, hxi, ?_⟩
  intro t
  have hW' : piZ z root (Ideal.Quotient.mk (Ideal.span {monicize H})
      (Polynomial.C H.leadingCoeff) : 𝒪 H) ≠ 0 := by
    simpa [piZ, piZLift] using hW
  have hxi' : piZ z root (HenselNumerators.xi x₀ R H hHyp) ≠ 0 := by
    simpa [HenselNumerators.xi, piZ, piZLift, Polynomial.evalEval] using hxi
  simp only [concreteDenRegularBridge, map_mul, map_pow]
  exact mul_ne_zero (pow_ne_zero _ hW') (pow_ne_zero _ hxi')

end ProximityPrize.SubmissionLower
