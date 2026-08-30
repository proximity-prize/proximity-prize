import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactOrderBridge
import ProximityPrize.SubmissionLower.ResidualOrderMoments
/-!
Residual-mass bridge for the regular-colon lower-bound candidate.

These proofs actually supply the derivative-degree and local-root inputs to
ResidualOrderMoments. They do NOT posit a residual-mass inequality. The
quotient width remains the actual m*A - contactDegree(F), even in the IRS
specializations below. No theorem replaces it by the uniform upper cap.

The equation F(X,P,P',gamma)=0 is not needed for this particular inequality:
agreement plus the nonzero specialized R derivative suffices. A regular
selected solution supplies these hypotheses in the intended application.
-/
namespace ProximityPrize.SubmissionLower.RegularColonMass

open scoped BigOperators
open ProximityPrize.Benchmark
open RCN081 ContactOrderBridge
open RCN122

section General
variable {K : Type*} [Field K]

theorem factor_ne_zero_of_regular_derivative
    (F : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (hregular : specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    F ≠ 0 := by
  intro hz
  apply hregular
  simp [hz]

theorem mass_on_points [DecidableEq K]
    (points selected : Finset K) (u₀ u₁ : K → K)
    (m w A gap : ℕ) (F : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (hsub : selected ⊆ points) (hA : A ≤ selected.card)
    (hm : 1 ≤ m) (hgap : A = w + gap) (hP : P.natDegree ≤ w)
    (hvalues : ∀ x ∈ selected, P.eval x = u₀ x + γ * u₁ x)
    (hregular : specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    m * A - MvPolynomial.weightedTotalDegree (contactWeights w) F ≤
      (∑ x ∈ points, (m - contactOrder K x (u₀ x) (u₁ x) F)) + gap + 1 := by
  let d := MvPolynomial.weightedTotalDegree (contactWeights w) F
  by_cases hd : d ≤ m * A
  · have hF := factor_ne_zero_of_regular_derivative F P γ hregular
    exact ResidualOrderMoments.mass_of_regular_polynomial
      points selected (fun x => contactOrder K x (u₀ x) (u₁ x) F)
      m w A d (m * A - d) gap
      (specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F))
      hregular hsub hA hm (Nat.sub_add_cancel hd) hgap
      (specialized_R_derivative_degree K F P γ w d hP le_rfl hregular)
      (fun x hx => specialized_R_derivative_dvd K F hF P x (u₀ x) (u₁ x) γ
        (hvalues x hx))
  · have hzero : m * A - d = 0 := Nat.sub_eq_zero_of_le (by omega)
    change m * A - d ≤ _
    rw [hzero]
    exact Nat.zero_le _

theorem mass_on_indexed_nodes [DecidableEq K]
    {I : Type*} [Fintype I] (nodes : I ↪ K) (selected : Finset I) (u₀ u₁ : I → K)
    (m w A gap : ℕ) (F : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (hA : A ≤ selected.card) (hm : 1 ≤ m) (hgap : A = w + gap) (hP : P.natDegree ≤ w)
    (hvalues : ∀ i ∈ selected, P.eval (nodes i) = u₀ i + γ * u₁ i)
    (hregular : specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    m * A - MvPolynomial.weightedTotalDegree (contactWeights w) F ≤
      (∑ i : I, (m - contactOrder K (nodes i) (u₀ i) (u₁ i) F)) + gap + 1 := by
  let d := MvPolynomial.weightedTotalDegree (contactWeights w) F
  by_cases hd : d ≤ m * A
  · have hF := factor_ne_zero_of_regular_derivative F P γ hregular
    exact ResidualOrderMoments.mass_of_regular_polynomial_indexed
      nodes selected (fun i => contactOrder K (nodes i) (u₀ i) (u₁ i) F)
      m w A d (m * A - d) gap
      (specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F))
      hregular hA hm (Nat.sub_add_cancel hd) hgap
      (specialized_R_derivative_degree K F P γ w d hP le_rfl hregular)
      (fun i hi => specialized_R_derivative_dvd K F hF P (nodes i) (u₀ i) (u₁ i) γ
        (hvalues i hi))
  · have hzero : m * A - d = 0 := Nat.sub_eq_zero_of_le (by omega)
    change m * A - d ≤ _
    rw [hzero]
    exact Nat.zero_le _

end General

section IRS6735

/-- Finset-of-field-points API used by the quotient projection. Neither its
    input nor its conclusion replaces the actual quotient width by a cap. -/
theorem irs_mass_on_points
    (points selected : Finset IRSProfile.Field)
    (u₀ u₁ : IRSProfile.Field → IRSProfile.Field)
    (F : MvPolynomial (Fin 4) IRSProfile.Field) (P : Polynomial IRSProfile.Field)
    (γ : IRSProfile.Field) (hsub : selected ⊆ points) (hA : 182032 ≤ selected.card)
    (hP : P.natDegree ≤ 131071)
    (hvalues : ∀ x ∈ selected, P.eval x = u₀ x + γ * u₁ x)
    (hregular : specialization IRSProfile.Field P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    7645344 - MvPolynomial.weightedTotalDegree (contactWeights 131071) F ≤
      (∑ x ∈ points, (42 - contactOrder IRSProfile.Field x (u₀ x) (u₁ x) F)) + 50962 := by
  classical
  have h := mass_on_points points selected u₀ u₁ 42 131071 182032 50961 F P γ
    hsub hA (by norm_num) (by norm_num) hP hvalues hregular
  norm_num [Nat.add_assoc] at h
  omega

/-- Actual IRS.domain API. `selected` is a set of indices of genuine
    agreement nodes, and the residual sum is over every IRS index. -/
theorem irs_mass_on_domain
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field)
    (F : MvPolynomial (Fin 4) IRSProfile.Field) (P : Polynomial IRSProfile.Field)
    (γ : IRSProfile.Field) (selected : Finset IRSProfile.Index)
    (hA : 182032 ≤ selected.card) (hP : P.natDegree ≤ 131071)
    (hvalues : ∀ i ∈ selected, P.eval (IRSProfile.domain i) = u₀ i + γ * u₁ i)
    (hregular : specialization IRSProfile.Field P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    7645344 - MvPolynomial.weightedTotalDegree (contactWeights 131071) F ≤
      (∑ i : IRSProfile.Index,
        (42 - contactOrder IRSProfile.Field (IRSProfile.domain i) (u₀ i) (u₁ i) F)) + 50962 := by
  classical
  have h := mass_on_indexed_nodes IRSProfile.domain selected u₀ u₁
    42 131071 182032 50961 F P γ hA (by norm_num) (by norm_num) hP hvalues hregular
  norm_num [Nat.add_assoc] at h
  omega

end IRS6735
end ProximityPrize.SubmissionLower.RegularColonMass
