import ProximityPrize.SubmissionLower.BCHKSFixedTransportOwner6400
import ProximityPrize.SubmissionLower.BCHKSUniversalNumerator
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteObstruction

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {L : Type} [Field L]

/-- The concrete function-field coefficient sequence is the genuine finite
Hensel lift: its full residual vanishes through the requested order. -/
theorem finiteAlpha_residual_vanishesThrough
    {F : Type} [Field F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0) (N : ℕ) :
    FiniteHensel.VanishesThrough
      (FiniteHensel.residual (liftedR (R := R) (H := H))
        (fieldTo𝕃 (H := H) x₀)
        (finiteAlpha (R := R) (H := H) x₀ N) N) N := by
  have hHd : H ∣ triSpecializeX R x₀ := by
    simpa [triSpecializeX, Polynomial.Bivariate.evalX_eq_map] using
      hHyp.dvd_evalX
  have hrootSpecialized : Polynomial.eval₂ (liftToFunctionField (H := H))
      (initialValue (H := H)) (triSpecializeX R x₀) = 0 :=
    eval₂_lift_initialValue_eq_zero_of_dvd
      (triSpecializeX R x₀) H hHd
  have hroot : Polynomial.eval₂
      (Polynomial.evalRingHom (fieldTo𝕃 (H := H) x₀))
      (initialValue (H := H)) (liftedR (R := R) (H := H)) = 0 := by
    rw [UniversalNumerator.liftedR_eval_at_initial_eq_specialization x₀ R]
    exact hrootSpecialized
  have hsimple : FiniteHensel.IsSimpleRootAt
      (liftedR (R := R) (H := H))
      (fieldTo𝕃 (H := H) x₀) (initialValue (H := H)) := by
    refine ⟨hroot, ?_⟩
    rw [ySlope_liftedR_eq_zeta]
    exact hzeta
  unfold finiteAlpha
  exact FiniteHensel.liftCoeff_vanishesThrough
    (liftedR (R := R) (H := H))
    (fieldTo𝕃 (H := H) x₀) (initialValue (H := H)) N hsimple

/-- The inherited weighted `X` support bound is exactly the degree cap needed
by the strict exact-root adapter. -/
theorem liftedR_eval_canonicalGamma_natDegree_lt_of_weighted_cap
    {F : Type} [Field F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (N k : ℕ) (hN : 0 < N)
    (hweighted : ∀ j a, (R.coeff j).coeff a ≠ 0 → a + k * j < N) :
    ((liftedR (R := R) (H := H)).eval
      (canonicalFunctionFieldGamma H x₀ R N k)).natDegree < N := by
  let gamma : (𝕃 H)[X] := canonicalFunctionFieldGamma H x₀ R N k
  have hgamma : gamma.natDegree ≤ k :=
    canonicalFunctionFieldGamma_natDegree_le x₀ R N k
  rw [Polynomial.eval_eq_sum]
  have hsum := Polynomial.natDegree_sum_le_of_forall_le
    (s := (liftedR (R := R) (H := H)).support)
    (f := fun j => (liftedR (R := R) (H := H)).coeff j * gamma ^ j)
    (n := N - 1)
  apply (hsum ?_).trans_lt
  · omega
  intro j hj
  let A : (𝕃 H)[X] := (liftedR (R := R) (H := H)).coeff j
  have hA0 : A ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hlead : A.coeff A.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hA0
  have horig : (R.coeff j).coeff A.natDegree ≠ 0 := by
    intro horig0
    have hAeq : A = (R.coeff j).map (liftToFunctionField (H := H)) := by
      simp [A, liftedR, Polynomial.coeff_map]
    have hcoeff : A.coeff A.natDegree = 0 := by
      calc
        A.coeff A.natDegree =
            ((R.coeff j).map (liftToFunctionField (H := H))).coeff A.natDegree :=
          congrArg (fun p : (𝕃 H)[X] => p.coeff A.natDegree) hAeq
        _ = liftToFunctionField (H := H)
            ((R.coeff j).coeff A.natDegree) := by
          simp only [Polynomial.coeff_map]
        _ = 0 := by rw [horig0, map_zero]
    exact hlead hcoeff
  have hAdeg : A.natDegree + k * j < N := hweighted j A.natDegree horig
  have hterm : (A * gamma ^ j).natDegree ≤ A.natDegree + j * k := by
    calc
      _ ≤ A.natDegree + (gamma ^ j).natDegree := Polynomial.natDegree_mul_le
      _ ≤ A.natDegree + j * gamma.natDegree :=
        Nat.add_le_add_left Polynomial.natDegree_pow_le _
      _ ≤ A.natDegree + j * k := Nat.add_le_add_left
        (Nat.mul_le_mul_left j hgamma) _
  change ((liftedR (R := R) (H := H)).coeff j * gamma ^ j).natDegree ≤ N - 1
  change (A * gamma ^ j).natDegree ≤ N - 1
  have hterm' : (A * gamma ^ j).natDegree ≤ A.natDegree + k * j := by
    simpa [Nat.mul_comm] using hterm
  omega

/-- Translation by `x₀`, followed by translation by `-x₀`, is the
identity on polynomials. -/
theorem shiftMap_comp_unshift (x₀ : L) (p : L[X]) :
    (FiniteHensel.shiftMap x₀ p).comp
        (Polynomial.X - Polynomial.C x₀) = p := by
  rw [FiniteHensel.shiftMap_apply, Polynomial.comp_assoc]
  have hi :
      (Polynomial.C x₀ + Polynomial.X).comp
          (Polynomial.X - Polynomial.C x₀) = (Polynomial.X : L[X]) := by
    simp
  rw [hi, Polynomial.comp_X]

/-- Undoing the centering translation after forming a Hensel residual gives
evaluation at the correspondingly unshifted candidate root. -/
theorem residual_comp_unshift
    (R : L[X][X]) (x₀ : L) (p : L[X]) :
    (R.eval₂ (FiniteHensel.shiftMap x₀) p).comp
        (Polynomial.X - Polynomial.C x₀) =
      R.eval (p.comp (Polynomial.X - Polynomial.C x₀)) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      simp only [Polynomial.eval₂_add, Polynomial.eval_add]
      rw [Polynomial.add_comp, hR, hS]
  | monomial n a =>
      simp only [Polynomial.eval₂_monomial, Polynomial.eval_monomial]
      rw [Polynomial.mul_comp, Polynomial.pow_comp, shiftMap_comp_unshift]

/-- Exact-root adapter for the canonical shifted Hensel truncation.  Choosing
the lift order `N` one below the weighted degree cutoff makes middle
coefficient vanishing inclusive, avoiding any unproved top-coefficient
congruence. -/
theorem canonicalFunctionFieldGamma_is_root_of_middle
    {F : Type} [Field F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (N k : ℕ) (hkN : k ≤ N)
    (hmiddle : ∀ t, k < t → t ≤ N →
      finiteAlpha (R := R) (H := H) x₀ N t = 0)
    (hres : FiniteHensel.VanishesThrough
      (FiniteHensel.residual (liftedR (R := R) (H := H))
        (fieldTo𝕃 (H := H) x₀)
        (finiteAlpha (R := R) (H := H) x₀ N) N) N)
    (hcap : ((liftedR (R := R) (H := H)).eval
      (canonicalFunctionFieldGamma H x₀ R N k)).natDegree ≤ N) :
    (liftedR (R := R) (H := H)).eval
      (canonicalFunctionFieldGamma H x₀ R N k) = 0 := by
  let alpha : ℕ → 𝕃 H := finiteAlpha (R := R) (H := H) x₀ N
  let short : (𝕃 H)[X] := FiniteHensel.truncSeries alpha k
  let full : (𝕃 H)[X] := FiniteHensel.truncSeries alpha N
  have htrunc : full = short := by
    ext i
    by_cases hik : i ≤ k
    · rw [FiniteHensel.coeff_truncSeries alpha N i (hik.trans hkN),
        FiniteHensel.coeff_truncSeries alpha k i hik]
    · by_cases hiN : i ≤ N
      · rw [FiniteHensel.coeff_truncSeries alpha N i hiN]
        have hzero : alpha i = 0 := hmiddle i (Nat.lt_of_not_ge hik) hiN
        rw [hzero]
        simp [short, FiniteHensel.truncSeries, hik]
      · simp [full, short, FiniteHensel.truncSeries, hik, hiN]
  let res : (𝕃 H)[X] :=
    FiniteHensel.residual (liftedR (R := R) (H := H))
      (fieldTo𝕃 (H := H) x₀) alpha N
  have hres' : FiniteHensel.VanishesThrough res N := by
    simpa [res, alpha] using hres
  have hres_short : res =
      (liftedR (R := R) (H := H)).eval₂
        (FiniteHensel.shiftMap (fieldTo𝕃 (H := H) x₀)) short := by
    unfold res FiniteHensel.residual
    rw [show FiniteHensel.truncSeries alpha N = short from htrunc]
  have hundo := residual_comp_unshift
    (liftedR (R := R) (H := H))
    (fieldTo𝕃 (H := H) x₀) short
  have hundo' :
      res.comp (Polynomial.X -
          Polynomial.C (fieldTo𝕃 (H := H) x₀)) =
        (liftedR (R := R) (H := H)).eval
          (canonicalFunctionFieldGamma H x₀ R N k) := by
    rw [hres_short]
    simpa [canonicalFunctionFieldGamma, short] using hundo
  have hinner :
      (Polynomial.X -
        Polynomial.C (fieldTo𝕃 (H := H) x₀) : (𝕃 H)[X]).natDegree = 1 := by
    exact Polynomial.natDegree_X_sub_C _
  have hrescap : res.natDegree ≤ N := by
    have hdegrees := congrArg Polynomial.natDegree hundo'
    rw [Polynomial.natDegree_comp, hinner, Nat.mul_one] at hdegrees
    rw [hdegrees]
    exact hcap
  have hreszero : res = 0 := by
    ext i
    by_cases hi : i ≤ N
    · simpa using hres' i hi
    · have hlt : res.natDegree < i := hrescap.trans_lt (Nat.lt_of_not_ge hi)
      simpa using Polynomial.coeff_eq_zero_of_natDegree_lt hlt
  rw [hreszero] at hundo'
  simpa using hundo'.symm

/-- Exact-root adapter with the strict middle range furnished by the BCHKS
simultaneous-vanishing theorem.  Below `N`, the full and shortened Hensel
inputs have identical coefficients, hence so do their shifted residuals.
The strict weighted degree cap then turns finite residual vanishing into an
exact root after undoing the centering translation. -/
theorem canonicalFunctionFieldGamma_is_root_of_strict_middle
    {F : Type} [Field F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (N k : ℕ) (hkN : k ≤ N)
    (hmiddle : ∀ t, k < t → t < N →
      finiteAlpha (R := R) (H := H) x₀ N t = 0)
    (hres : FiniteHensel.VanishesThrough
      (FiniteHensel.residual (liftedR (R := R) (H := H))
        (fieldTo𝕃 (H := H) x₀)
        (finiteAlpha (R := R) (H := H) x₀ N) N) N)
    (hcap : ((liftedR (R := R) (H := H)).eval
      (canonicalFunctionFieldGamma H x₀ R N k)).natDegree < N) :
    (liftedR (R := R) (H := H)).eval
      (canonicalFunctionFieldGamma H x₀ R N k) = 0 := by
  let alpha : ℕ → 𝕃 H := finiteAlpha (R := R) (H := H) x₀ N
  let short : (𝕃 H)[X] := FiniteHensel.truncSeries alpha k
  let full : (𝕃 H)[X] := FiniteHensel.truncSeries alpha N
  let Rshift : (𝕃 H)[X][X] :=
    (liftedR (R := R) (H := H)).map
      (FiniteHensel.shiftMap (fieldTo𝕃 (H := H) x₀))
  let resShort : (𝕃 H)[X] :=
    (liftedR (R := R) (H := H)).eval₂
      (FiniteHensel.shiftMap (fieldTo𝕃 (H := H) x₀)) short
  let resFull : (𝕃 H)[X] :=
    (liftedR (R := R) (H := H)).eval₂
      (FiniteHensel.shiftMap (fieldTo𝕃 (H := H) x₀)) full
  have hinput : ∀ i, i < N → short.coeff i = full.coeff i := by
    intro i hiN
    by_cases hik : i ≤ k
    · rw [FiniteHensel.coeff_truncSeries alpha k i hik,
        FiniteHensel.coeff_truncSeries alpha N i (Nat.le_trans hik hkN)]
    · have hzero : alpha i = 0 := hmiddle i (Nat.lt_of_not_ge hik) hiN
      rw [FiniteHensel.coeff_truncSeries alpha N i hiN.le, hzero]
      simp [short, FiniteHensel.truncSeries, hik]
  have hmatch : ∀ i, i < N → resShort.coeff i = resFull.coeff i := by
    intro i hi
    have heq := UniversalNumerator.coeff_eval_eq_of_coeff_eq_up_to
      Rshift short full i (by
        intro j hj
        exact hinput j (hj.trans_lt hi))
    simpa [resShort, resFull, Rshift, Polynomial.eval₂_eq_eval_map] using heq
  have hresFull : FiniteHensel.VanishesThrough resFull N := by
    simpa [resFull, full, alpha, FiniteHensel.residual] using hres
  have hundo := residual_comp_unshift
    (liftedR (R := R) (H := H))
    (fieldTo𝕃 (H := H) x₀) short
  have hundo' :
      resShort.comp (Polynomial.X -
          Polynomial.C (fieldTo𝕃 (H := H) x₀)) =
        (liftedR (R := R) (H := H)).eval
          (canonicalFunctionFieldGamma H x₀ R N k) := by
    simpa [resShort, canonicalFunctionFieldGamma, short] using hundo
  have hinner :
      (Polynomial.X -
        Polynomial.C (fieldTo𝕃 (H := H) x₀) : (𝕃 H)[X]).natDegree = 1 :=
    Polynomial.natDegree_X_sub_C _
  have hshortCap : resShort.natDegree < N := by
    have hdegrees := congrArg Polynomial.natDegree hundo'
    rw [Polynomial.natDegree_comp, hinner, Nat.mul_one] at hdegrees
    rw [hdegrees]
    exact hcap
  have hshortZero : resShort = 0 := by
    exact eval_truncSeries_eq_zero_of_residual_match_and_cap
      resShort resFull N hresFull hmatch hshortCap
  rw [hshortZero] at hundo'
  simpa using hundo'.symm

/-- Closed exact-root interface used by the score-64 selector.  The Hensel
residual and the strict degree cap are discharged from the selected simple
root and weighted-support data, so callers only retain the middle-range
vanishing theorem furnished by the global selection step. -/
theorem canonicalFunctionFieldGamma_is_root_of_score_data
    {F : Type} [Field F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) (hN : 0 < N)
    (hmiddle : ∀ t, k < t → t < N →
      finiteAlpha (R := R) (H := H) x₀ N t = 0)
    (hweighted : ∀ j a, (R.coeff j).coeff a ≠ 0 →
      a + k * j < N) :
    (liftedR (R := R) (H := H)).eval
      (canonicalFunctionFieldGamma H x₀ R N k) = 0 := by
  apply canonicalFunctionFieldGamma_is_root_of_strict_middle
    x₀ R N k hkN hmiddle
  · exact finiteAlpha_residual_vanishesThrough x₀ R hHyp hzeta N
  · exact liftedR_eval_canonicalGamma_natDegree_lt_of_weighted_cap
      x₀ R N k hN hweighted

end ProximityPrize.SubmissionLower
