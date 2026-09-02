import ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
import ProximityPrize.SubmissionLower.BF

namespace ProximityPrize.SubmissionLower.LocatorHelperFactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- The score-67.77 long interpolation source used only by the local factor
switch. -/
abbrev LongKernel (u₀ u₁ : I → K) :=
  ConstraintKernel (K := K) 43769938 131071 457347 71 241
    IRSProfile.domain u₀ u₁

/-- Unequal-pair parameters for a factor with the long helper polynomial on
the right. -/
def helperPair (leftY leftR leftZ : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181589, leftY, leftR, leftZ, 333, 71, 457347⟩

/-- The characteristic hypotheses required by the unequal-pair theorem,
kept independent of the replacement-grid module to avoid an import cycle. -/
def HelperPairGates (leftY leftR leftZ : ℕ) : Prop :=
  let P := helperPair leftY leftR leftZ
  1 ≤ P.leftR ∧ P.leftY < 2130706433 ∧ P.leftR < 2130706433 ∧
    P.leftZ < 2130706433 ∧ P.mixedCost.y < 2130706433 ∧
    P.mixedCost.r < 2130706433 ∧ P.mixedCost.z < 2130706433

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- For each irreducible regular factor, either the factor divides every
member of the long interpolation kernel (enabling the long C8 quotient), or a
single witness reconstruction is coprime to the factor and the existing
unequal-pair incidence theorem gives the helper cost. -/
theorem long_divisor_or_helper_count
    {u₀ u₁ : I → K} {H : P4}
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u₀ i + gamma * u₁ i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (leftY leftR leftZ : ℕ)
    (hFY : F.1.degreeOf 1 ≤ leftY)
    (hFR : F.1.degreeOf 2 ≤ leftR)
    (hFZ : F.1.degreeOf 3 ≤ leftZ)
    (hgates : HelperPairGates leftY leftR leftZ) :
    (∀ v : LongKernel u₀ u₁,
      F.1 ∣ reconstruct K 43769938 131071 457347 71 v.1) ∨
      (regularSeeds H selected Gamma F).card ≤
        (helperPair leftY leftR leftZ).regularCountCap := by
  classical
  by_cases hdiv : ∀ v : LongKernel u₀ u₁,
      F.1 ∣ reconstruct K 43769938 131071 457347 71 v.1
  · exact Or.inl hdiv
  · right
    push Not at hdiv
    obtain ⟨v, hv⟩ := hdiv
    let Q := reconstruct K 43769938 131071 457347 71 v.1
    have hF := RCN167.positiveRFactors_spec H F.1 F.2
    have hrel : IsRelPrime F.1 Q :=
      hF.1.isRelPrime_iff_not_dvd.mpr hv
    have hQbox : Q ∈ globalCoefficientBox K 43769938 131071 457347 71 :=
      reconstruct_mem_globalCoefficientBox K 43769938 131071 457347 71 v.1
    have hQYS : wt residualYSWeights Q ≤ 333 := by
      apply flag_box_ys_bound 43769938 131071 457347 71 333
        (by decide) (by decide) Q hQbox
    have hweights := (mem_flagGlobalCoefficientBox_iff Q
      43769938 131071 457347 71 (by decide)).mp hQbox
    have hQY : Q.degreeOf 1 ≤ 333 :=
      (degreeY_le_ysWeight Q).trans hQYS
    have hQR : Q.degreeOf 2 ≤ 71 :=
      (degreeR_le_sWeight Q).trans hweights.2.1
    have hQZ : Q.degreeOf 3 ≤ 457347 :=
      (degreeZ_le_totalWeight Q).trans hweights.1
    obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
    apply regularSeeds_count_le_intersection
      (helperPair leftY leftR leftZ) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ : Finset I) IRSProfile.domain u₀ u₁
      IRSProfile.domain.injective.injOn
      (by
        change (Finset.univ : Finset I).card = 262144
        rw [Finset.card_univ]
        norm_num [I, IRSProfile.Index])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by simpa only [helperPair] using hdegree)
      (by simpa only [helperPair] using hagreement)
      (by simpa only [helperPair, UnequalParameters.errors, Nat.reduceSub] using hno)
    intro gamma hgamma
    dsimp only [Q]
    apply specialization_eq_zero_of_agreements K
      43769938 131071 457347 71 241 181589 IRSProfile.domain u₀ u₁
      v.1 v.2 (by decide) (by decide) (selected gamma) gamma
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u₀ i + gamma * u₁ i))
    · exact hdegree gamma (Finset.mem_filter.mp hgamma).1
    · exact hagreement gamma (Finset.mem_filter.mp hgamma).1
    · intro i hi
      exact (Finset.mem_filter.mp hi).2

end

end ProximityPrize.SubmissionLower.LocatorHelperFactorSwitch
