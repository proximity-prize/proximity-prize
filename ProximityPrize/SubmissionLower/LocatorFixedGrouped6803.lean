import ProximityPrize.SubmissionLower.LocatorResidualGrouped6803

/-!
# Branch-free grouped cover for the selected gcd

The positive derivative chains and all slope-free factors are charged once,
through a single aggregate terminal product.  The terminal product is counted
in the full, unspent selected-gcd contact box; this is valid whether or not a
positive-R factor exists.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedGrouped6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN095 RCN100 RCN130 RCN135 RCN136 RCN137 RCN138
  RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN286 RCN318
  RCN319
open LocatorDerivativeChain LocatorGroupedDerivativeFactor6803
  LocatorPositiveFactorGroupedAggregate6803
  LocatorAggregateTerminalProduct6803
  LocatorGroupedDerivativeUniformCaps6803
  LocatorGroupedNonRegularAssembly6803
  LocatorGroupedNonRegularCardinality6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- Exact unspent contact box for the aggregate fixed-gcd tail. -/
def fixedExactTailStage : TightParameters :=
  ⟨262144, 131071, 181363, 20131293, 6676, 1⟩

theorem fixedExactTailStage_countCap :
    fixedExactTailStage.countCap = 2093635209007 := by
  native_decide

private theorem allPositiveExactChainSeeds_subset
    (Q : P4) (selected : K → Polynomial K) (Gamma : Finset K) :
    allPositiveExactChainSeeds Q selected Gamma ⊆ Gamma := by
  intro gamma hgamma
  rw [allPositiveExactChainSeeds, Finset.mem_biUnion] at hgamma
  obtain ⟨F, _hF, hgammaF⟩ := hgamma
  exact exactChainUnion_subset F selected Gamma hgammaF

/-- Uniform R-free counter for the unspent fixed tail box. -/
theorem fixed_exact_tail_counter
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (J : P4) (hJ : J ≠ 0) (hJR : J.degreeOf 2 = 0)
    (hJbox : J ∈ RCN174.globalCoefficientBox K
      20131293 131071 6676 1) :
    (Gamma.filter fun gamma ↦
      specialization K (selected gamma) gamma J = 0).card ≤
        fixedExactTailStage.countCap := by
  let S := fixedExactTailStage
  apply rfree_seed_count_le S J hJ 2130706433 hJbox hJR
    (by simp [S, fixedExactTailStage])
    (by decide) (by simp [S, fixedExactTailStage])
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by simp [S, fixedExactTailStage])
    selected (Gamma.filter fun gamma ↦
      specialization K (selected gamma) gamma J = 0)
    (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by simp [S, fixedExactTailStage, I, IRSProfile.Index])
    (fun gamma hgamma ↦ hdegree gamma (Finset.filter_subset _ _ hgamma))
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2)
    (fun gamma hgamma ↦ hagreement gamma (Finset.filter_subset _ _ hgamma))
    (by
      simpa [S, fixedExactTailStage, TightParameters.errors] using
        RCN243.noLargeSelectedPencil_mono selected Gamma
          (Gamma.filter fun gamma ↦
            specialization K (selected gamma) gamma J = 0)
          131071 80781 (Finset.filter_subset _ _) hno)

/-- The aggregate terminal product remains in the full selected-gcd tail
box.  No derivative spend or positivity branch is needed. -/
theorem aggregateTerminalProduct_mem_fixed_exact_tail_box
    (Q : P4) (hQ : Q ≠ 0)
    (hRsmall : Q.degreeOf (2 : Fin 4) < 2130706433)
    (hL : wt residualTotalWeights Q ≤ 6676)
    (hcontact : wt (contactWeights 131071) Q ≤ 20131292) :
    aggregateTerminalProduct Q ∈ RCN174.globalCoefficientBox K
      20131293 131071 6676 1 := by
  apply (mem_globalCoefficientBox_iff (aggregateTerminalProduct Q)
    20131293 131071 6676 1 (by decide)).mpr
  refine ⟨?_, ?_, ?_⟩
  · have htotal := aggregateTerminalProduct_total_add_chainLength_le
      Q hQ 2130706433 hRsmall
    exact (seedWeight_le_residualTotalWeight
      (aggregateTerminalProduct Q)).trans (by omega)
  · have hslope : slopeWeights = Pi.single (2 : Fin 4) 1 := by
      funext i
      fin_cases i <;> simp [slopeWeights, Pi.single_apply]
    rw [hslope, MvPolynomial.weightedTotalDegree_piSingle,
      aggregateTerminalProduct_R_degree]
    omega
  · have hterminal := aggregateTerminalProduct_contact_add_scaledChainLength_le
      131071 Q hQ 2130706433 hRsmall
    change MvPolynomial.weightedTotalDegree (contactWeights 131071)
      (aggregateTerminalProduct Q) +
        (131071 - 1) * (∑ F ∈ positiveRFactors Q, chainLength F) ≤
          MvPolynomial.weightedTotalDegree (contactWeights 131071) Q at hterminal
    change MvPolynomial.weightedTotalDegree (contactWeights 131071)
      (aggregateTerminalProduct Q) ≤ 20131293 - 1
    have hcontact' :
        MvPolynomial.weightedTotalDegree (contactWeights 131071) Q ≤
          20131292 := by
      simpa only [RCN234.wt] using hcontact
    omega

/-- Complete branch-free grouped charge for the selected gcd. -/
theorem fixed_allGroupedNonRegularSeeds_card_le
    (Q : P4) (hQ : Q ≠ 0)
    (hY : wt residualYSWeights Q ≤ 153)
    (hS : wt residualSWeights Q ≤ 34)
    (hL : wt residualTotalWeights Q ≤ 6676)
    (hcontact : wt (contactWeights 131071) Q ≤ 20131292)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781) :
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      fixedHGroupedStage.regularCountCap + fixedHEscapeDot +
        fixedExactTailStage.countCap := by
  have hsub := allPositiveExactChainSeeds_subset Q selected Gamma
  have hRsmall : Q.degreeOf (2 : Fin 4) < 2130706433 := by
    have hdegreeR : Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
      apply MvPolynomial.degreeOf_le_iff.mpr
      intro d hd
      have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
      rw [weight_fin4] at h
      change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
        MvPolynomial.weightedTotalDegree residualSWeights Q at h
      simpa only [Nat.mul_zero, Nat.mul_one, Nat.add_zero,
        Nat.zero_add, RCN234.wt] using h
    exact (hdegreeR.trans hS).trans_lt (by decide)
  have hscaled :
      (allPositiveExactChainSeeds Q selected Gamma).card *
          (181363 - 131071) ≤
        groupedDerivativeNumerator 262144 131071 181363
          (262144 - 181363) 153 34 6676 := by
    have hraw := allPositiveExactChainSeeds_grouped_of_cumulativeCaps
      Q hQ selected Gamma (Finset.univ : Finset I)
      IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      2130706433 131071 181363 80781 153 34 6676
      (by decide) (by decide) (by decide)
      (by norm_num [I, IRSProfile.Index]) (by decide)
      hY hS hL (by decide) (by decide) (by decide)
      Concrete.fixed_pair_characteristic_gate
      (fun gamma hgamma ↦ hdegree gamma (hsub hgamma))
      (fun gamma hgamma ↦ hagreement gamma (hsub hgamma))
      (RCN243.noLargeSelectedPencil_mono selected Gamma _
        131071 80781 hsub hno)
    have hnodes : (Finset.univ : Finset I).card = 262144 := by
      norm_num [I, IRSProfile.Index]
    rw [hnodes] at hraw
    exact hraw
  have hJbox := aggregateTerminalProduct_mem_fixed_exact_tail_box
    Q hQ hRsmall hL hcontact
  have htail : (aggregateTerminalSeeds Q selected Gamma).card ≤
      fixedExactTailStage.countCap := by
    exact fixed_exact_tail_counter selected Gamma u0 u1 hdegree hagreement hno
      (aggregateTerminalProduct Q)
      (aggregateTerminalProduct_ne_zero Q hQ 2130706433 hRsmall)
      (aggregateTerminalProduct_R_degree Q) hJbox
  exact allGroupedNonRegularSeeds_card_le_adjacent_add_tail
    Q selected Gamma 262144 131071 181363 153 34 6676
      fixedExactTailStage.countCap (by decide) hscaled htail

theorem fixed_allGroupedNonRegularSeeds_card_le_numeric
    (Q : P4) (hQ : Q ≠ 0)
    (hY : wt residualYSWeights Q ≤ 153)
    (hS : wt residualSWeights Q ≤ 34)
    (hL : wt residualTotalWeights Q ≤ 6676)
    (hcontact : wt (contactWeights 131071) Q ≤ 20131292)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781) :
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      142046491699954 := by
  have h := fixed_allGroupedNonRegularSeeds_card_le Q hQ hY hS hL hcontact
    selected Gamma u0 u1 hdegree hagreement hno
  rw [fixedHGroupedStage_exact, fixedHEscapeDot_exact,
    fixedExactTailStage_countCap] at h
  norm_num at h ⊢
  exact h

end

end ProximityPrize.SubmissionLower.LocatorFixedGrouped6803
