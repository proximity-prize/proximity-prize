import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSimultaneousOccurrenceLedger6750Research
import ProximityPrize.SubmissionLower.ContactTwoTailFixedSelected6733Research

 








namespace ProximityPrize.SubmissionLower.ContactSimultaneousFixedCost6750Research

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactFlagBezout6543Research ContactGCDCumulativeFlagsResearch
open ContactResidualSupportParametersResearch
open ContactTwoTailParameters6733Research
open ContactTwoTailFixedSelected6733Research
open ContactSimultaneousOccurrenceLedger6750Research
open ContactGlobalSelectedFamilies6600Research ContactRegularFactorFlag6600Research
open ContactImplicitContactLift ContactPrimeSeedIncidence

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600

 



theorem occurrence_regular_factor_seed_bound
    (proper : ProperStageProvider6733)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (u0 u1 : I -> K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : NormalizedOccurrence Q) :
    (occurrenceRegularSeeds Q selected Gamma R).card ≤
      flagMixed (occurrenceCumulativeFlag Q R)
        (tailFlag (w + 1)) (tailFlag (w + 2)) := by
  by_cases hRpos : 0 < (occurrenceFactor Q R).degreeOf 2
  · have hactive : occurrenceFactor Q R ∈ ContactFactorCover.activeFactors Q := by
      apply Finset.mem_filter.mpr
      refine ⟨Multiset.mem_toFinset.mpr (occurrenceFactor_mem Q R), ?_⟩
      omega
    let Rdistinct : RegularIndex Q :=
      ⟨occurrenceFactor Q R, Finset.mem_filter.mpr ⟨hactive, hRpos⟩⟩
    have hbound := regular_factor_seed_bound proper Q hQ hbox Hsupport
      selected Gamma u0 u1 hdegree hagreement hnoPencil Rdistinct
    simpa [occurrenceRegularSeeds, occurrenceCumulativeFlag, occurrenceFactor,
      ContactGlobalSelectedFamilies6600Research.regularSeeds,
      ContactGCDCumulativeFlagsResearch.regularCumulativeFlag,
      Rdistinct] using hbound
  · have hRzero : (occurrenceFactor Q R).degreeOf 2 = 0 :=
      Nat.eq_zero_of_not_pos hRpos
    have hpzero : MvPolynomial.pderiv (2 : Fin 4) (occurrenceFactor Q R) = 0 :=
      ContactRegularFactorGate.pderiv_zero_of_degree_zero
        (2 : Fin 4) (occurrenceFactor Q R) hRzero
    have hempty : occurrenceRegularSeeds Q selected Gamma R = ∅ := by
      ext gamma
      simp [occurrenceRegularSeeds, RegularSolution, hpzero]
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

 

theorem fixed_simultaneous_regular_card_le_half
    (proper : ProperStageProvider6733)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (u0 u1 : I -> K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hderivative : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) Q) = 0)
    (haux : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card ≤ fixedRegularCost / 2 := by
  have hc := occurrenceCumulativeFlag_budgets Q hQ Hsupport
  have hhalf := occurrence_regular_card_le_half_flagMixed Q hQ selected Gamma
    fixedFlag (tailFlag (w + 1)) (tailFlag (w + 2))
    hsolution hderivative haux
    (occurrence_regular_factor_seed_bound proper Q hQ hbox Hsupport selected
      Gamma u0 u1 hdegree hagreement hnoPencil)
    (hc.1.trans_eq (by decide))
    (hc.2.1.trans_eq (by decide))
    (hc.2.2.trans_eq (by decide))
  simpa [fixedRegularCost] using hhalf

end

end ProximityPrize.SubmissionLower.ContactSimultaneousFixedCost6750Research

#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousFixedCost6750Research.occurrence_regular_factor_seed_bound
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousFixedCost6750Research.fixed_simultaneous_regular_card_le_half
