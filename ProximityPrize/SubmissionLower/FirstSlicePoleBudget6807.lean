/-
UNCOMPILED. First-cut pole mass from the ORIGINAL finite-set source theorem.
A slice component does not need its own moving projection construction:
SecondJetRelaxedFlag.moving_bound already bounds every finite theta sum.
-/
import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.ActualFirstCutPole6807

namespace ProximityPrize.SubmissionLower.FirstSlicePoleBudget6807
open scoped Classical BigOperators WithZero
open RCN057 (WeightBound)
open RCN002 RCN005 RCN006 RCN026 RCN055 RCN341 RCN095 RCN136 RCN156 RCN187 RCN204 RCN234 RCN313
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

/-- Finite-place arithmetic; uses integer sums so no componentwise floors occur. -/
theorem sum_first_poles_scaled {V : Type*}
    (S : Finset V) (d w : ℕ) (J theta pole : V → ℤ) (CJ CV : ℤ)
    (hlocal : ∀ v ∈ S, pole v ≤ J v + (w : ℤ)*theta v)
    (hJ : (∑ v ∈ S, J v) ≤ CJ)
    (hsource : (d : ℤ)*(∑ v ∈ S, theta v) ≤ CV) :
    (d : ℤ)*(∑ v ∈ S, pole v) ≤ (d : ℤ)*CJ+(w : ℤ)*CV := by
  have hsum : (∑ v ∈ S, pole v) ≤
      (∑ v ∈ S, J v)+(w : ℤ)*(∑ v ∈ S, theta v) := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using
      Finset.sum_le_sum hlocal
  have hscaled := mul_le_mul_of_nonneg_left hsum (Int.natCast_nonneg d)
  have hscaledJ := mul_le_mul_of_nonneg_left hJ (Int.natCast_nonneg d)
  have hscaledSource := mul_le_mul_of_nonneg_left hsource (Int.natCast_nonneg w)
  nlinarith

section ActualSource
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

/-- Actual normalized first tail and actual helper-root source on an arbitrary
prime slice component. The assumptions are source divisibility/support and pure
flag pole budgets, not a first-cut intersection inequality. -/
theorem actual_first_source_pole_mass
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hF : surfaceMap phi F ∈ C)
    (hH : surfaceMap phi (polyH K F) ∉ C)
    (hlead : surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (m r v z : ℕ) (hm : 1 ≤ m) (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (CJ CV : ℕ)
    (hJbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C) (firstBaseFlag m r v z)) ≤ (CJ : ℤ))
    (hVbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0)) ≤ (CV : ℤ))
    (W : Finset (Place E (CoordinateField E C))) :
    let ev := SecondJetComponentRoots.coefficientMap phi C
    ((k+1 : ℕ) : ℤ) * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (ev (baseNumerator F m)/ev (polyH K F)^(m+1))) ≤
      ((k+1 : ℕ) : ℤ)*(CJ : ℤ)+((m+1 : ℕ) : ℤ)*(CV : ℤ) := by
  letI := polynomialBaseAlgebra E C base.index
  letI := rationalBaseAlgebra E C base.index base.transcendental
  letI := polynomialBaseScalarTower E C base.index
  letI := polynomialRationalScalarTower E C base.index base.transcendental
  letI := rationalBaseScalarTower E C base.index base.transcendental
  letI : FiniteDimensional (RatFunc E) (CoordinateField E C) := base.finite
  letI : Algebra.IsSeparable (RatFunc E) (CoordinateField E C) := base.separable
  let ev := SecondJetComponentRoots.coefficientMap phi C
  let H := ev (polyH K F)
  let G := ev (polyG K F)
  let sigma := G/H
  let theta := fun nu : Place E (CoordinateField E C) =>
    max (2*flagPole nu.val (coordinate E C) unitAllFlag)
      (flagPole nu.val (coordinate E C) unitYZFlag + poleOrder nu.val sigma)
  have hHne : H ≠ 0 := by
    intro hz
    apply hH
    exact (SecondJetComponentRoots.evaluation_zero_iff C _).mp hz
  have hdeg := SecondJetComponentRoots.degree_retained phi C P hlead
  have hroot := SecondJetComponentRoots.roots_retained phi C P F s k hS
    hF hH hlead hdiv h2 hfact
  have hdegree : n0 ≤ (SecondJetComponentRoots.componentPolynomial phi C P).natDegree := by
    rw [hdeg.2]
    exact hn
  have hs := SecondJetRelaxedFlag.moving_bound
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X)
    B U T (k+1) n0 hBU hUT hdn hB
    (SecondJetSurfaceMap.mapped_support_bounds _ P B U T hP)
    (coordinate E C) (SecondJetComponentRoots.componentPolynomial phi C P)
    (SecondJetComponentRoots.coefficients phi C P) hdeg.1 hdegree
    (RCN064.movingRatio C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F))/2) hroot (CV : ℤ) hVbudget W
  have hsource : ((k+1 : ℕ) : ℤ)*(∑ nu ∈ W, theta nu) ≤ (CV : ℤ) := by
    simpa only [SecondJetPoleScaling.pole_half _ h2, theta, sigma, G, H, ev,
      SecondJetComponentRoots.coefficientMap, RCN064.movingRatio,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hs
  have hlocal : ∀ nu ∈ W, poleOrder nu.val
      (ev (baseNumerator F m)/H^(m+1)) ≤
        flagPole nu.val (coordinate E C) (firstBaseFlag m r v z)+
          ((m+1 : ℕ) : ℤ)*theta nu := by
    intro nu _
    have ha := actual_first_normalized_value_le nu.val
      (algebraMap E (CoordinateField E C))
      (RCN344.constant_value_le_one E (CoordinateField E C) nu)
      (coordinate E C) phi F m r v z hm hr hv hR hYR hAll
      (by simpa only [H, ev, SecondJetComponentRoots.coefficientMap,
        coordinateEvaluation_eq_aeval, MvPolynomial.aeval_eq_eval₂Hom,
        RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hHne)
    apply pole_le_of_value_le nu.val _ _
    · have hj0 := flagPole_nonneg nu.val (coordinate E C) (firstBaseFlag m r v z)
      have ht0 : 0 ≤ theta nu := by
        exact (mul_nonneg (by norm_num) (flagPole_nonneg _ _ unitAllFlag)).trans
          (le_max_left _ _)
      positivity
    · simpa only [theta, sigma, G, H, ev, SecondJetComponentRoots.coefficientMap,
        coordinateEvaluation_eq_aeval, MvPolynomial.aeval_eq_eval₂Hom,
        RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using ha
  exact sum_first_poles_scaled W (k+1) (m+1)
    (fun nu => flagPole nu.val (coordinate E C) (firstBaseFlag m r v z)) theta
    (fun nu => poleOrder nu.val (ev (baseNumerator F m)/H^(m+1)))
    (CJ : ℤ) (CV : ℤ) hlocal (hJbudget W) hsource

end ActualSource
end
end ProximityPrize.SubmissionLower.FirstSlicePoleBudget6807
