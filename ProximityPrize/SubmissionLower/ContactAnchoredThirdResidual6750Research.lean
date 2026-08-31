import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedResidualCells6656Research
import ProximityPrize.SubmissionLower.ContactAsymmetricResidualStageResearch
import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import ProximityPrize.SubmissionLower.ContactFrozenAlignment6600Research

 









namespace ProximityPrize.SubmissionLower.ContactAnchoredThirdResidual6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactPrimeSeedIncidence
open ContactProperCutSeedCount ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch ContactSingularLedger6600Research
open ContactAsymmetricResidualStageResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev Poly4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

def n : Nat := 262144
def w : Nat := 131071
def agreements : Nat := 181874
def errors : Nat := 80270
def prime : Nat := 2130706433

local instance : CharP K prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600

 



def thirdStage (t y r : Nat) : UnequalParameters :=
  ⟨n, w, agreements,
    66, 15 - r, 1699 - t,
    (79 * agreements - (w * (y - 1) - r) - 1) / w,
    25 - r, 2155 - t⟩

 

def thirdPivot (t r : Nat) : TightParameters :=
  ⟨n, w, agreements, 48 * agreements, 1699 - t, 15 - r⟩

 



structure ResidualValidity
    (P : UnequalParameters) (S : TightParameters) : Prop where
  P_n : P.n = n
  S_n : S.n = n
  w_eq : P.w = S.w
  a_eq : P.a = S.a
  s_one : 1 ≤ S.s
  s_small : S.s < prime
  w_one : 1 ≤ S.w
  w_small : S.w < prime
  kD : S.w < S.kappa * S.D
  algebraic_pos : 1 ≤ S.algebraicCap
  implicit_small : S.implicitYCap < prime
  algebraic_small : S.algebraicCap < prime
  mixed_small : 2 * S.implicitYCap * S.algebraicCap < prime
  wa : S.w < S.a
  an : S.a ≤ S.n
  gap_pos : 0 < P.gap
  gap_eq : S.gap = P.gap
  qY : (S.D - 1) / S.w ≤ P.leftY
  qR : S.s ≤ P.leftR
  qZ : S.L ≤ P.leftZ
  leftR_pos : 1 ≤ P.leftR
  leftY_small : P.leftY < prime
  leftR_small : P.leftR < prime
  leftZ_small : P.leftZ < prime
  mixedY_small : P.mixedCost.y < prime
  mixedR_small : P.mixedCost.r < prime
  mixedZ_small : P.mixedCost.z < prime

 

theorem residual_count_lt
    (P : UnequalParameters) (S : TightParameters)
    (valid : ResidualValidity P S)
    (Q T : Poly4) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (hQbox : Q ∈ globalCoefficientBox K S.D S.w S.L S.s)
    (hTcaps : T.degreeOf 1 ≤ P.rightY ∧ T.degreeOf 2 ≤ P.rightR ∧
      T.degreeOf 3 ≤ P.rightZ)
    (selected : K → Polynomial K) (Delta : Finset K)
    (u0 u1 : I → K)
    (hQsolution : ∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma T = 0)
    (hdegree : ∀ gamma ∈ Delta, (selected gamma).natDegree ≤ S.w)
    (hagreement : ∀ gamma ∈ Delta, S.a ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Delta S.w S.errors) :
    Delta.card < P.regularCountCap + S.countCap + 1 := by
  apply ProximityPrize.SubmissionLower.ContactStackedResidualCells6656Research.asymmetric_stage_count_lt_of_regular_factors
      P S Q T hQ prime valid.s_one valid.s_small valid.w_one valid.w_small
      valid.kD valid.algebraic_pos valid.implicit_small valid.algebraic_small
      valid.mixed_small valid.wa valid.an hQbox valid.gap_pos valid.gap_eq
      valid.qY valid.qR valid.qZ selected Delta (Finset.univ : Finset I)
      IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      (by rw [valid.S_n]; norm_num [I, IRSProfile.Index, n])
      hdegree hQsolution hTsolution hagreement hnoPencil
  exact all_regularPairSeeds_bound P Q T hQ hrel S.D S.w S.L S.s prime
    hQbox valid.w_one valid.qY valid.qR valid.qZ hTcaps.1 hTcaps.2.1
    hTcaps.2.2 valid.leftR_pos valid.leftY_small valid.leftR_small
    valid.leftZ_small valid.mixedY_small valid.mixedR_small valid.mixedZ_small
    selected Delta (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by rw [valid.P_n]; norm_num [I, IRSProfile.Index, n])
    (by rw [valid.w_eq]; exact valid.w_one)
    (by rw [valid.w_eq]; exact valid.w_small)
    (by rw [valid.w_eq, valid.a_eq]; exact valid.wa)
    (by
      rw [valid.a_eq, valid.P_n]
      have hh := valid.an
      rw [valid.S_n] at hh
      exact hh)
    (by rw [valid.w_eq]; exact hdegree)
    (by rw [valid.a_eq]; exact hagreement)
    (by
      have herr : P.errors = S.errors := by
        simp only [UnequalParameters.errors, TightParameters.errors,
          valid.P_n, valid.S_n, valid.a_eq]
      simpa only [valid.w_eq, herr] using hnoPencil)

 


theorem third_residual_count_lt
    (t y r : Nat)
    (valid : ResidualValidity (thirdStage t y r) (thirdPivot t r))
    (Q T : Poly4) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (hQbox : Q ∈ globalCoefficientBox K
      (thirdPivot t r).D (thirdPivot t r).w
      (thirdPivot t r).L (thirdPivot t r).s)
    (hTcaps : T.degreeOf 1 ≤ (thirdStage t y r).rightY ∧
      T.degreeOf 2 ≤ (thirdStage t y r).rightR ∧
      T.degreeOf 3 ≤ (thirdStage t y r).rightZ)
    (selected : K → Polynomial K) (Delta : Finset K)
    (u0 u1 : I → K)
    (hQsolution : ∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma T = 0)
    (hdegree : ∀ gamma ∈ Delta, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Delta, agreements ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Delta w errors) :
    Delta.card < (thirdStage t y r).regularCountCap +
      (thirdPivot t r).countCap + 1 := by
  have hdegree' : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ (thirdPivot t r).w := by
    simpa only [thirdPivot, w] using hdegree
  have hagreement' : ∀ gamma ∈ Delta, (thirdPivot t r).a ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card := by
    simpa only [thirdPivot, agreements] using hagreement
  have hnoPencil' : NoLargeSelectedPencil selected Delta
      (thirdPivot t r).w (thirdPivot t r).errors := by
    simpa only [thirdPivot, TightParameters.errors, n, w, agreements,
      errors] using hnoPencil
  exact residual_count_lt (thirdStage t y r) (thirdPivot t r) valid
    Q T hQ hrel hQbox hTcaps selected Delta u0 u1
    hQsolution hTsolution hdegree' hagreement' hnoPencil'

 



theorem third_validity_of_full_old_core_bounds
    {t y r : Nat} (hthi : t ≤ 1698) (hyhi : y ≤ 65) (hrhi : r ≤ 14) :
    ResidualValidity (thirdStage t y r) (thirdPivot t r) := by
  constructor <;>
    simp only [thirdStage, thirdPivot, n, w, agreements, prime,
      UnequalParameters.gap, UnequalParameters.mixedCost,
      TightParameters.gap, TightParameters.kappa,
      TightParameters.implicitYCap, TightParameters.algebraicCap] <;>
    try omega
  all_goals interval_cases r <;> interval_cases y <;> omega

 
theorem third_validity_of_hostile_bounds
    {t y r : Nat}
    (_htlo : 897 ≤ t) (hthi : t ≤ 1692)
    (_hylo : 38 ≤ y) (hyhi : y ≤ 65)
    (_hrlo : 8 ≤ r) (hrhi : r ≤ 14) :
    ResidualValidity (thirdStage t y r) (thirdPivot t r) :=
  third_validity_of_full_old_core_bounds (hthi.trans (by omega)) hyhi hrhi

end

end ProximityPrize.SubmissionLower.ContactAnchoredThirdResidual6750Research

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredThirdResidual6750Research.residual_count_lt
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredThirdResidual6750Research.third_residual_count_lt
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredThirdResidual6750Research.third_validity_of_full_old_core_bounds
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredThirdResidual6750Research.third_validity_of_hostile_bounds
