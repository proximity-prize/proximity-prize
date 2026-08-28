import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteObstruction
import ProximityPrize.SubmissionLower.BCHKSUniversalResultantSelection

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

namespace UniversalNumerator

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- Bounded form of `numerators_eq_slope_pow_mul_coeff`: only the diagonal
residual equations actually used up to the requested cutoff are needed. -/
theorem numerators_eq_slope_pow_mul_coeff_upto
    {L : Type*} [Field L]
    (Rshift : L[X][X]) (s : L) (hs : s ≠ 0) (d N : ℕ)
    (c : ℕ → L) (hc0 : c 0 = 0)
    (hdeg : Rshift.natDegree ≤ d)
    (hslope : FiniteHensel.ySlope Rshift 0 0 = s)
    (hvanish : ∀ n, 1 ≤ n → n ≤ N →
      (FiniteHensel.residual Rshift 0 c n).coeff n = 0) :
    ∀ n, 1 ≤ n → n ≤ N →
      numerators Rshift s d n = s ^ (2 * n - 1) * c n := by
  intro n hn hnN
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [numerators_succ]
      apply numeratorStep_eq_slope_pow_mul_coeff
        Rshift s hs d (t + 1)
          (fun i => if i ≤ t then numerators Rshift s d i else 0)
          c (by omega) hc0 hdeg hslope (hvanish (t + 1) (by omega) hnN)
      intro i hi0 hit
      have hit' : i ≤ t := by omega
      rw [if_pos hit']
      exact ih i (by omega) hi0 (by omega)

/-- Shifting the root to zero turns the finite Hensel coefficients into the
coefficient sequence consumed by the universal positive-index recurrence. -/
theorem rootedNumerators_shifted_eq_liftCoeff_mul_slope_pow
    {L : Type*} [Field L]
    (R : L[X][X]) (x₀ y₀ : L) (d N n : ℕ)
    (hRdeg : R.natDegree ≤ d)
    (hsimple : FiniteHensel.IsSimpleRootAt R x₀ y₀)
    (hnN : n ≤ N) :
    rootedNumerators y₀
        ((R.map (FiniteHensel.shiftMap x₀)).comp
          (Polynomial.C (Polynomial.C y₀) + Polynomial.X : L[X][X]))
        (FiniteHensel.ySlope R x₀ y₀) d n =
      FiniteHensel.liftCoeff R x₀ y₀ N n *
        FiniteHensel.ySlope R x₀ y₀ ^
          FiniteHenselWeight.denominatorExponent n := by
  let a : ℕ → L := FiniteHensel.liftCoeff R x₀ y₀ N
  let c : ℕ → L := fun i => if i = 0 then 0 else a i
  let Rshift : L[X][X] :=
    (R.map (FiniteHensel.shiftMap x₀)).comp
      (Polynomial.C (Polynomial.C y₀) + Polynomial.X : L[X][X])
  let s : L := FiniteHensel.ySlope R x₀ y₀
  have hs : s ≠ 0 := hsimple.2
  have hc0 : c 0 = 0 := by simp [c]
  have hdeg : Rshift.natDegree ≤ d := by
    dsimp [Rshift]
    rw [Polynomial.natDegree_comp]
    have hinner :
        (Polynomial.C (Polynomial.C y₀) + Polynomial.X : L[X][X]).natDegree = 1 := by
      simp [add_comm]
    rw [hinner, mul_one]
    exact Polynomial.natDegree_map_le.trans hRdeg
  have hslope : FiniteHensel.ySlope Rshift 0 0 = s := by
    simp [Rshift, FiniteHensel.ySlope, FiniteHensel.shiftMap,
      Polynomial.derivative_comp]
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
      add_zero]
    rw [Polynomial.eval_map]
    change (Polynomial.evalRingHom 0)
      (Polynomial.eval₂ (FiniteHensel.shiftMap x₀) (Polynomial.C y₀)
        R.derivative) = _
    rw [Polynomial.hom_eval₂]
    have hcomp : (Polynomial.evalRingHom 0).comp
        (FiniteHensel.shiftMap x₀) = Polynomial.evalRingHom x₀ := by
      ext a <;> simp [FiniteHensel.shiftMap, RingHom.comp_apply]
    rw [hcomp]
    simp [s, FiniteHensel.ySlope]
  have hvanish : ∀ m, 1 ≤ m → m ≤ N →
      (FiniteHensel.residual Rshift 0 c m).coeff m = 0 := by
    intro m hm hmN
    have hcoeff : ∀ i, i ≤ m →
        (Polynomial.C y₀ + FiniteHensel.truncSeries c m).coeff i =
          (FiniteHensel.truncSeries a N).coeff i := by
      intro i hi
      rw [Polynomial.coeff_add,
        FiniteHensel.coeff_truncSeries c m i hi,
        FiniteHensel.coeff_truncSeries a N i (hi.trans hmN)]
      by_cases hi0 : i = 0
      · subst i
        simp [a, c]
      · simp [Polynomial.coeff_C, hi0, c]
    have heval := coeff_eval_eq_of_coeff_eq_up_to
      (R.map (FiniteHensel.shiftMap x₀))
      (Polynomial.C y₀ + FiniteHensel.truncSeries c m)
      (FiniteHensel.truncSeries a N) m hcoeff
    have hres :
        (FiniteHensel.residual Rshift 0 c m).coeff m =
          (FiniteHensel.residual R x₀ a N).coeff m := by
      unfold FiniteHensel.residual
      rw [shiftMap_zero_eq]
      change (Rshift.eval (FiniteHensel.truncSeries c m)).coeff m = _
      dsimp [Rshift]
      rw [Polynomial.eval_comp]
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      rw [Polynomial.eval₂_eq_eval_map]
      exact heval
    rw [hres]
    exact FiniteHensel.liftCoeff_vanishesThrough R x₀ y₀ N hsimple m hmN
  by_cases hn0 : n = 0
  · subst n
    simp [FiniteHenselWeight.denominatorExponent]
  · rw [rootedNumerators_of_pos _ _ _ _ _ (Nat.pos_of_ne_zero hn0)]
    have hrepr := numerators_eq_slope_pow_mul_coeff_upto
      Rshift s hs d N c hc0 hdeg hslope hvanish n
        (Nat.one_le_iff_ne_zero.mpr hn0) hnN
    have hc : c n = a n := by simp [c, hn0]
    rw [hrepr, hc]
    rw [show FiniteHenselWeight.denominatorExponent n = 2 * n - 1 by
      simp [FiniteHenselWeight.denominatorExponent]]
    ring

/-- The branch-independent rooted universal numerators evaluate at the generic
root of `H` to the canonical finite-Hensel coefficients, cleared by the exact
odd power of the generic slope. -/
theorem eval₂_universalRootedNumerators_eq_finiteAlpha_mul_zeta_pow
    {F : Type} [Field F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N n : ℕ) (hnN : n ≤ N) :
    Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) (universalRootedNumerators x₀ R n) =
      finiteAlpha (R := R) (H := H) x₀ N n *
        HenselNumerators.zeta R x₀ H ^
          FiniteHenselWeight.denominatorExponent n := by
  let RL : (𝕃 H)[X][Y] := liftedR (R := R) (H := H)
  let xL : 𝕃 H := fieldTo𝕃 (H := H) x₀
  let yL : 𝕃 H := initialValue (H := H)
  have hroot0 : Polynomial.eval₂ (liftToFunctionField (H := H))
      (initialValue (H := H))
        (Polynomial.Bivariate.evalX (Polynomial.C x₀) R) = 0 :=
    eval₂_lift_initialValue_eq_zero_of_dvd
      (Polynomial.Bivariate.evalX (Polynomial.C x₀) R) H hHyp.dvd_evalX
  have hcomp :
      (Polynomial.evalRingHom
          (liftToFunctionField (H := H) (Polynomial.C x₀))).comp
          (Polynomial.mapRingHom (liftToFunctionField (H := H))) =
        (liftToFunctionField (H := H)).comp
          (Polynomial.evalRingHom (Polynomial.C x₀)) := by
    ext p <;> simp [RingHom.comp_apply]
  have hroot : Polynomial.eval₂ (Polynomial.evalRingHom xL) yL RL = 0 := by
    dsimp [RL, xL, yL, liftedR, fieldTo𝕃]
    rw [Polynomial.eval₂_map, hcomp]
    simpa [Polynomial.Bivariate.evalX_eq_map, Polynomial.eval₂_map] using hroot0
  have hsimple : FiniteHensel.IsSimpleRootAt RL xL yL := by
    refine ⟨hroot, ?_⟩
    dsimp [RL, xL, yL]
    rw [ySlope_liftedR_eq_zeta]
    exact hzeta
  change evalUniversal (liftToFunctionField (H := H)) yL
      (universalRootedNumerators x₀ R n) = _
  unfold universalRootedNumerators
  rw [rootedNumerators_map]
  rw [universalShift_map_evalUniversal, universalSlope_evalUniversal]
  have hslopeMap : FiniteHensel.ySlope
      (R.map (Polynomial.mapRingHom (liftToFunctionField (H := H))))
      (liftToFunctionField (H := H) (Polynomial.C x₀))
      (initialValue (H := H)) = HenselNumerators.zeta R x₀ H := by
    simpa [liftedR, fieldTo𝕃] using
      (ySlope_liftedR_eq_zeta (R := R) (H := H) x₀)
  rw [hslopeMap]
  have hgen := rootedNumerators_shifted_eq_liftCoeff_mul_slope_pow
    RL xL yL R.natDegree N n Polynomial.natDegree_map_le hsimple hnN
  rw [show FiniteHensel.ySlope RL xL yL =
      HenselNumerators.zeta R x₀ H by
    simpa [RL, xL, yL, liftedR, fieldTo𝕃] using hslopeMap] at hgen
  simpa [evalUniversal, finiteAlpha, RL, xL, yL, liftedR, fieldTo𝕃] using hgen

end

end UniversalNumerator

end ProximityPrize.SubmissionLower
