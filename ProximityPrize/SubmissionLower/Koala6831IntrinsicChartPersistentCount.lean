import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartAgreement
import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartCoefficients

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped BigOperators WithZero
open RCN002 RCN005 RCN065 RCN135 RCN136 RCN257 RCN271 RCN341 RCN344

noncomputable section

set_option maxHeartbeats 4400000
set_option maxRecDepth 22000
set_option linter.style.haveILetI false

variable {K : Type} [Field K]

theorem persistent_curve_regular_agreement_bound
    (F : Carrier K) (w t z : ℕ)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (d₀ d₁ : ℕ)
    (hd₀ : ∀ W : Finset (Place (GenericField K) (CoordinateField (GenericField K) C)),
      (∑ v ∈ W, RCN346.poleOrder (GenericField K) (CoordinateField (GenericField K) C) v
        (coordinate (GenericField K) C 1)) ≤ (d₀ : ℤ))
    (hd₁ : ∀ W : Finset (Place (GenericField K) (CoordinateField (GenericField K) C)),
      (∑ v ∈ W, RCN346.poleOrder (GenericField K) (CoordinateField (GenericField K) C) v
        (coordinate (GenericField K) C 2)) ≤ (d₁ : ℤ))
    (hS : surfaceMap (polynomialEmbedding K) (implicitRegularity F) ∉ C)
    (ht : ∀ d ∈ F.support, d 2 ≤ t) (hz : ∀ d ∈ F.support, d 3 ≤ z)
    (P : Polynomial (CoordinateField (GenericField K) C))
    (hGraph : MvPolynomial.eval₂Hom (Polynomial.C.comp (componentCoefficients (polynomialEmbedding K) C))
        ![Polynomial.X, P, Polynomial.C (coordinate (GenericField K) C 1),
          Polynomial.C (coordinate (GenericField K) C 2)] F = 0)
    (x u₀ u₁ : K)
    (hAgreement :
      coordinateEvaluation (GenericField K) C
          (surfaceMap (polynomialEmbedding K) (persistentAgreementNumerator F w x u₀ u₁)) /
        (coordinateEvaluation (GenericField K) C
          (surfaceMap (polynomialEmbedding K) (implicitRegularity F))) ^ (2 * w) =
        P.eval (componentCoefficients (polynomialEmbedding K) C x) -
          componentCoefficients (polynomialEmbedding K) C u₀ -
          componentCoefficients (polynomialEmbedding K) C u₁ * coordinate (GenericField K) C 1)
    (hproper : P.eval (componentCoefficients (polynomialEmbedding K) C x) -
        componentCoefficients (polynomialEmbedding K) C u₀ -
        componentCoefficients (polynomialEmbedding K) C u₁ * coordinate (GenericField K) C 1 ≠ 0) :
    ∃ B : MvPolynomial (Fin 3) (GenericField K), B ∉ C ∧
      FiniteRegularZeroSetBound C (surfaceMap (polynomialEmbedding K) (implicitRegularity F))
        (B * surfaceMap (polynomialEmbedding K) (persistentAgreementNumerator F w x u₀ u₁))
        ((t + 1) * d₀ + z * d₁) := by
  classical
  let Ω := GenericField K
  let E := CoordinateField Ω C
  let φ := polynomialEmbedding K
  let coeff := componentCoefficients φ C
  let z₀ := coordinate Ω C 1
  let z₁ := coordinate Ω C 2
  let D := seedGraphEquation coeff z₀ z₁ F
  let H := surfaceMap φ (implicitRegularity F)
  let raw := surfaceMap φ (persistentAgreementNumerator F w x u₀ u₁)
  let Avalue := P.eval (coeff x) - coeff u₀ - coeff u₁ * z₀
  let degree := (t + 1) * d₀ + z * d₁
  have hD : D ≠ 0 := by
    apply seedGraphEquation_ne_zero_of_regular coeff (componentPoint φ C) F
    intro hzero
    exact hS ((component_evaluation_zero_iff φ C _).1 hzero)
  have hDroot : D.eval P = 0 := (seedGraphEquation_eval coeff z₀ z₁ F P).trans hGraph
  let j := D.leadingCoeff.natDegree
  let a := D.leadingCoeff.coeff j
  let B := seedCoefficientOnSurface (φ.comp Polynomial.C) F D.natDegree j
  have ha : a ≠ 0 := by
    change D.leadingCoeff.leadingCoeff ≠ 0
    exact Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hD)
  have hB : coordinateEvaluation Ω C B = a := by
    rw [coordinateEvaluation_eq_aeval]
    change MvPolynomial.eval₂Hom (algebraMap Ω E) (coordinate Ω C) B = a
    exact seedCoefficientOnSurface_eval (φ.comp Polynomial.C) (algebraMap Ω E)
      (coordinate Ω C) F D.natDegree j
  have hBproper : B ∉ C := by
    intro hb
    have hzero : coordinateEvaluation Ω C B = 0 := by
      change B ∈ RingHom.ker (coordinateEvaluation Ω C).toRingHom
      rwa [coordinateEvaluation_ker]
    exact ha (hB.symm.trans hzero)
  let cut := B * raw
  have hratio : coordinateEvaluation Ω C cut / (coordinateEvaluation Ω C H) ^ (2 * w) =
      a * Avalue := by
    change coordinateEvaluation Ω C (B * raw) / _ = _
    rw [map_mul, mul_div_assoc, hB, hAgreement]
  have hcut : cut ∉ C := by
    intro hmem
    have hzero : coordinateEvaluation Ω C cut = 0 := by
      change cut ∈ RingHom.ker (coordinateEvaluation Ω C).toRingHom
      rwa [coordinateEvaluation_ker]
    exact mul_ne_zero ha hproper (by rw [← hratio, hzero, zero_div])
  refine ⟨B, hBproper, ?_⟩
  apply finite_regular_zero_bound_of_separator Ω C base H cut (2 * w) degree hcut hS
  letI : Algebra (RatFunc Ω) E := rationalBaseAlgebra Ω C base.index base.transcendental
  letI : FiniteDimensional (RatFunc Ω) E := base.finite
  letI : Algebra.IsSeparable (RatFunc Ω) E := base.separable
  intro W
  simp only [← coordinateEvaluation_eq_aeval, hratio]
  have hpole (v : Place Ω E) : RCN346.poleOrder Ω E v (a * Avalue) ≤
      (t + 1 : ℤ) * RCN346.poleOrder Ω E v z₀ + (z : ℤ) * RCN346.poleOrder Ω E v z₁ := by
    have hconst (k : K) : v.val (coeff k) ≤ 1 := constant_value_le_one Ω E v (φ (Polynomial.C k))
    exact seedGraphEquation_agreement_pole_le v.val coeff z₀ z₁ F t z j P (coeff x) (coeff u₀)
      (coeff u₁) hconst ht hz (hconst x) (hconst u₀) (hconst u₁) hDroot
  calc
    ∑ v ∈ W, RCN346.poleOrder Ω E v (a * Avalue) ≤
        ∑ v ∈ W, ((t + 1 : ℤ) * RCN346.poleOrder Ω E v z₀ + (z : ℤ) * RCN346.poleOrder Ω E v z₁) :=
      Finset.sum_le_sum fun v _ => hpole v
    _ = (t + 1 : ℤ) * (∑ v ∈ W, RCN346.poleOrder Ω E v z₀) +
        (z : ℤ) * (∑ v ∈ W, RCN346.poleOrder Ω E v z₁) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (degree : ℤ) := by
      push_cast [degree]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hd₀ W) (by positivity))
        (mul_le_mul_of_nonneg_left (hd₁ W) (by positivity))

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
