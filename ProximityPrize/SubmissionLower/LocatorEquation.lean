import ProximityPrize.SubmissionLower.LocatorFixed

/- A fixed quotient equation on regular seeds of one original factor.
   No coprimality or irreducibility assumption is imposed on the quotient.
   The quotient's singular seeds belong to its whole-equation count; the
   original common polynomial's singular seeds are not added by this module. -/
namespace ProximityPrize.SubmissionLower.LocatorEquation

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN319 RCN174 RCN140 RCN266 RCN238
open RCN095 RCN130 RCN234 RCN156 RCN275
open LocatorFactorAggregate

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 1500000

/-- First-order original-R elimination.  The only cancellation is by the
nonzero specialized derivative in the integral domain of polynomials. -/
theorem specialization_quotient_zero_of_regular_product
    {K : Type*} [Field K]
    (F Q : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K)
    (hF : specialization K P gamma F = 0)
    (hregular : specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hproduct : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (F * Q)) = 0) :
    specialization K P gamma Q = 0 := by
  have hmul : specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F) *
      specialization K P gamma Q = 0 := by
    simpa only [MvPolynomial.pderiv_mul, map_add, map_mul,
      hF, zero_mul, add_zero] using hproduct
  exact (mul_eq_zero.mp hmul).resolve_left hregular

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

abbrev equationCost (D T YS S : ℕ) : ℕ := LocatorFixed.equationCost D T YS S

/-- The factor F may share factors with Q.  Its regular seeds still satisfy
the fixed quotient equation whenever the product derivative vanishes. -/
theorem regularSeeds_quotient_equation
    (H Q : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (F : RegularIndex H)
    (hproduct : ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (F.1 * Q)) = 0) :
    ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma Q = 0 := by
  intro gamma hgamma
  have hreg := (Finset.mem_filter.mp hgamma).2
  exact specialization_quotient_zero_of_regular_product F.1 Q
    (selected gamma) gamma hreg.1 hreg.2 (hproduct gamma hgamma)

/-- This replacement count includes all regular and singular solutions of Q.
Only the regular seed subset belonging to F is being bounded. -/
theorem regularSeeds_count_le_equation
    (D T YS S : ℕ)
    (hDlow : 131072 ≤ D) (hDhigh : D ≤ 12488265)
    (hSpos : 1 ≤ S) (hSY : S ≤ YS) (hYT : YS ≤ T) (hYpos : 2 ≤ YS)
    (hS : S ≤ 15) (hY : YS ≤ 95) (hT : T ≤ 10000)
    (H Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K D 131071 T S)
    (hcaps : wt residualSWeights Q ≤ S ∧ wt residualYSWeights Q ≤ YS ∧
      wt residualTotalWeights Q ≤ T)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181845 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80299)
    (F : RegularIndex H)
    (hproduct : ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (F.1 * Q)) = 0) :
    (regularSeeds H selected Gamma F).card ≤ equationCost D T YS S := by
  have hsub := regularSeeds_subset H selected Gamma F
  exact LocatorFixed.whole_equation_count D T YS S hDlow hDhigh
    hSpos hSY hYT hYpos hS hY hT Q hQ hbox hcaps
    selected (regularSeeds H selected Gamma F) u0 u1
    (regularSeeds_quotient_equation H Q selected Gamma F hproduct)
    (fun gamma hgamma => hdegree gamma (hsub hgamma))
    (fun gamma hgamma => hagreement gamma (hsub hgamma))
    (RCN243.noLargeSelectedPencil_mono selected Gamma _ 131071 80299 hsub hno)

/-- A compositional minimum bridge when the original factor's already-proved
own-support count is available to the caller. -/
theorem regularSeeds_count_le_min
    (D T YS S : ℕ)
    (hDlow : 131072 ≤ D) (hDhigh : D ≤ 12488265)
    (hSpos : 1 ≤ S) (hSY : S ≤ YS) (hYT : YS ≤ T) (hYpos : 2 ≤ YS)
    (hS : S ≤ 15) (hY : YS ≤ 95) (hT : T ≤ 10000)
    (H Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K D 131071 T S)
    (hcaps : wt residualSWeights Q ≤ S ∧ wt residualYSWeights Q ≤ YS ∧
      wt residualTotalWeights Q ≤ T)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181845 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80299)
    (F : RegularIndex H)
    (hproduct : ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (F.1 * Q)) = 0)
    (hown : (regularSeeds H selected Gamma F).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤
      min (paddedCost 131072 131073 (regularCumulativeFlag H F))
        (equationCost D T YS S) := by
  exact Nat.le_min_of_le_of_le hown
    (regularSeeds_count_le_equation D T YS S hDlow hDhigh
      hSpos hSY hYT hYpos hS hY hT H Q hQ hbox hcaps
      selected Gamma u0 u1 hdegree hagreement hno F hproduct)

/-- Complete single-factor minimum, deriving the own-support branch rather
than introducing a separate counting hypothesis. -/
theorem regular_factor_count_le_min_equation
    (DH : ℕ) (PH : ResidualSupportParameters)
    (hDHlow : 131072 ≤ DH) (hDHhigh : DH ≤ 12488265)
    (hHS : PH.s ≤ 15) (hHY : PH.ys ≤ 95) (hHT : PH.total ≤ 10000)
    (H : P4) (hH : H ≠ 0)
    (hHbox : H ∈ RCN174.globalCoefficientBox K DH 131071 PH.total PH.s)
    (hHcaps : ResidualSupportData PH H)
    (D T YS S : ℕ)
    (hDlow : 131072 ≤ D) (hDhigh : D ≤ 12488265)
    (hSpos : 1 ≤ S) (hSY : S ≤ YS) (hYT : YS ≤ T) (hYpos : 2 ≤ YS)
    (hS : S ≤ 15) (hY : YS ≤ 95) (hT : T ≤ 10000)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K D 131071 T S)
    (hcaps : wt residualSWeights Q ≤ S ∧ wt residualYSWeights Q ≤ YS ∧
      wt residualTotalWeights Q ≤ T)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181845 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80299)
    (F : RegularIndex H)
    (hproduct : ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (F.1 * Q)) = 0) :
    (regularSeeds H selected Gamma F).card ≤
      min (paddedCost 131072 131073 (regularCumulativeFlag H F))
        (equationCost D T YS S) := by
  apply regularSeeds_count_le_min D T YS S hDlow hDhigh
    hSpos hSY hYT hYpos hS hY hT H Q hQ hbox hcaps
    selected Gamma u0 u1 hdegree hagreement hno F hproduct
  exact LocatorFixed.regular_factor_count DH PH hDHlow hDHhigh hHS hHY hHT
    H hH hHbox hHcaps selected Gamma u0 u1 hdegree hagreement hno F

end
end ProximityPrize.SubmissionLower.LocatorEquation
