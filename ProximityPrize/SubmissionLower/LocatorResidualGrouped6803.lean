import ProximityPrize.SubmissionLower.LocatorRetainedResidualBridge6803
import ProximityPrize.SubmissionLower.LocatorGroupedNonRegularCardinality6803

/-!
The grouped non-regular half of the retained residual locator, in the
positive-`R` branch.  The empty positive-factor branch is intentionally kept
separate for the final cover assembly.
-/

namespace ProximityPrize.SubmissionLower.LocatorResidualGrouped6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN095 RCN100 RCN130 RCN135 RCN136 RCN137 RCN138
  RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN286 RCN318 RCN319
open LocatorDerivativeChain LocatorGroupedDerivativeFactor6803
  LocatorPositiveFactorGroupedAggregate6803
  LocatorAggregateTerminalProduct6803
  LocatorGroupedDerivativeUniformCaps6803
  LocatorGroupedNonRegularAssembly6803
  LocatorGroupedNonRegularCardinality6803
  LocatorRetainedQuotient6803

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

private theorem allPositiveExactChainSeeds_subset
    (Q : P4) (selected : K → Polynomial K) (Gamma : Finset K) :
    allPositiveExactChainSeeds Q selected Gamma ⊆ Gamma := by
  intro gamma hgamma
  rw [allPositiveExactChainSeeds, Finset.mem_biUnion] at hgamma
  obtain ⟨F, _hF, hgammaF⟩ := hgamma
  exact exactChainUnion_subset F selected Gamma hgammaF

private theorem sub_pair_characteristic_gate (p : FlagDegree) :
    ∀ j k : Fin 3, j ≠ k →
      firstDerivativeSurfaceCap (153 - middle p) (34 - p.all)
          (14261 - total p) j *
          originalSurfaceCap (153 - middle p) (34 - p.all)
            (14261 - total p) k +
        originalSurfaceCap (153 - middle p) (34 - p.all)
            (14261 - total p) j *
          firstDerivativeSurfaceCap (153 - middle p) (34 - p.all)
            (14261 - total p) k < 2130706433 := by
  intro j k hjk
  have hfirst (i : Fin 3) :
      firstDerivativeSurfaceCap (153 - middle p) (34 - p.all)
          (14261 - total p) i ≤
        firstDerivativeSurfaceCap 153 34 14261 i := by
    fin_cases i <;> simp [firstDerivativeSurfaceCap] <;> omega
  have horiginal (i : Fin 3) :
      originalSurfaceCap (153 - middle p) (34 - p.all)
          (14261 - total p) i ≤
        originalSurfaceCap 153 34 14261 i := by
    fin_cases i <;> simp [originalSurfaceCap] <;> omega
  exact (Nat.add_le_add
    (Nat.mul_le_mul (hfirst j) (horiginal k))
    (Nat.mul_le_mul (horiginal j) (hfirst k))).trans_lt
      (Concrete.residualB_pair_characteristic_gate j k hjk)

/-- The exact quotient-contact box.  Unlike `residualBTailStage`, this stage
does not spend a derivative before counting the aggregate terminal product.
It is therefore also valid when the quotient has no positive-`R` factor. -/
def residualBExactTailStage (p : FlagDegree) : TightParameters :=
  ⟨262144, 131071, 181363,
    20131293 - retainedContact 131071 p, 14261 - total p, 1⟩

private theorem exact_tail_implicitYCap_eq (p : FlagDegree)
    (hs : p.all ≤ 29) (hy : middle p ≤ 135) :
    (residualBExactTailStage p).implicitYCap = 153 - middle p := by
  have hord := LocatorResidualRegular6803.flag_order p
  have hyraw : p.yz + p.all ≤ 135 := by
    simpa only [middle] using hy
  have hret : retainedContact 131071 p ≤ 20131293 := by
    unfold retainedContact middle
    omega
  have hformula :
      20131293 - retainedContact 131071 p =
        131071 * (153 - middle p) + 77430 + p.all := by
    unfold retainedContact middle at hret ⊢
    omega
  simp only [residualBExactTailStage, TightParameters.implicitYCap,
    TightParameters.kappa, Nat.reduceMul, Nat.reduceSub, one_mul]
  rw [hformula]
  apply Nat.div_eq_of_lt_le <;> omega

/-- Uniform counter for the exact retained residual-B contact box. -/
theorem residual_exact_tail_counter
    (p : FlagDegree) (hs : p.all ≤ 29) (hy : middle p ≤ 135)
    (ht : total p ≤ 6676)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (J : P4) (hJ : J ≠ 0) (hJR : J.degreeOf 2 = 0)
    (hJbox : J ∈ RCN174.globalCoefficientBox K
      (20131293 - retainedContact 131071 p) 131071
        (14261 - total p) 1) :
    (Gamma.filter fun gamma ↦
      specialization K (selected gamma) gamma J = 0).card ≤
        (residualBExactTailStage p).countCap := by
  let S := residualBExactTailStage p
  have hyraw : p.yz + p.all ≤ 135 := by
    simpa only [middle] using hy
  have himp : S.implicitYCap = 153 - middle p :=
    exact_tail_implicitYCap_eq p hs hy
  have halg : S.algebraicCap = 14261 - total p := by
    simp [S, residualBExactTailStage, TightParameters.algebraicCap,
      TightParameters.kappa]
  apply rfree_seed_count_le S J hJ 2130706433 hJbox hJR
    (by simp [S, residualBExactTailStage])
    (by decide) (by simp [S, residualBExactTailStage])
    (by simp [S, residualBExactTailStage])
    (by
      simp only [S, residualBExactTailStage, TightParameters.kappa,
        Nat.reduceMul, Nat.reduceSub, one_mul]
      unfold retainedContact middle
      omega)
    (by rw [halg]; omega)
    (by rw [himp]; exact (Nat.sub_le _ _).trans_lt (by decide))
    (by rw [halg]; omega)
    (by
      rw [himp, halg]
      calc
        2 * (153 - middle p) * (14261 - total p) ≤
            2 * 153 * 14261 := by gcongr <;> omega
        _ < 2130706433 := by decide)
    (by simp [S, residualBExactTailStage])
    (by simp [S, residualBExactTailStage])
    selected (Gamma.filter fun gamma ↦
      specialization K (selected gamma) gamma J = 0)
    (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by simp [S, residualBExactTailStage, I, IRSProfile.Index])
    (fun gamma hgamma ↦ hdegree gamma (Finset.filter_subset _ _ hgamma))
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2)
    (fun gamma hgamma ↦ hagreement gamma (Finset.filter_subset _ _ hgamma))
    (by
      simpa [S, residualBExactTailStage, TightParameters.errors] using
        RCN243.noLargeSelectedPencil_mono selected Gamma
          (Gamma.filter fun gamma ↦
            specialization K (selected gamma) gamma J = 0)
          131071 80781 (Finset.filter_subset _ _) hno)

private theorem tail_implicitYCap_le (p : FlagDegree) :
    (residualBTailStage p).implicitYCap ≤ 153 - middle p := by
  simp only [residualBTailStage, TightParameters.implicitYCap,
    TightParameters.kappa, Nat.reduceMul, Nat.reduceSub, one_mul]
  apply (Nat.div_le_iff_le_mul (by decide)).2
  omega

/-- Uniform tail counter for the retained residual-B box. -/
theorem residual_tail_counter
    (p : FlagDegree) (hy : middle p ≤ 135) (ht : total p ≤ 6676)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (J : P4) (hJ : J ≠ 0) (hJR : J.degreeOf 2 = 0)
    (hJbox : J ∈ RCN174.globalCoefficientBox K
      (131071 * (153 - middle p)) 131071 (14261 - total p) 1) :
    (Gamma.filter fun gamma ↦
      specialization K (selected gamma) gamma J = 0).card ≤
        (residualBTailStage p).countCap := by
  let S := residualBTailStage p
  have himp := tail_implicitYCap_le p
  have halg : S.algebraicCap = 14261 - total p := by
    simp [S, residualBTailStage, TightParameters.algebraicCap,
      TightParameters.kappa]
  apply rfree_seed_count_le S J hJ 2130706433 hJbox hJR
    (by simp [S, residualBTailStage])
    (by decide) (by simp [S, residualBTailStage])
    (by simp [S, residualBTailStage])
    (by
      simp only [S, residualBTailStage, TightParameters.kappa,
        Nat.reduceMul, Nat.reduceSub, one_mul]
      omega)
    (by rw [halg]; omega)
    (by exact himp.trans_lt ((Nat.sub_le _ _).trans_lt (by decide)))
    (by rw [halg]; omega)
    (by
      calc
        2 * S.implicitYCap * S.algebraicCap ≤
            2 * 153 * 14261 := by
          apply Nat.mul_le_mul
          · exact Nat.mul_le_mul_left 2 (himp.trans (Nat.sub_le _ _))
          · rw [halg]
            exact Nat.sub_le _ _
        _ < 2130706433 := by decide)
    (by simp [S, residualBTailStage])
    (by simp [S, residualBTailStage])
    selected (Gamma.filter fun gamma ↦
      specialization K (selected gamma) gamma J = 0)
    (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by simp [S, residualBTailStage, I, IRSProfile.Index])
    (fun gamma hgamma ↦ hdegree gamma (Finset.filter_subset _ _ hgamma))
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2)
    (fun gamma hgamma ↦ hagreement gamma (Finset.filter_subset _ _ hgamma))
    (by
      simpa [S, residualBTailStage, TightParameters.errors] using
        RCN243.noLargeSelectedPencil_mono selected Gamma
          (Gamma.filter fun gamma ↦
            specialization K (selected gamma) gamma J = 0)
          131071 80781 (Finset.filter_subset _ _) hno)

/-- Without assuming a positive `R`-factor, the aggregate terminal product
fits the exact retained contact box.  This is the box needed by the empty
positive-factor branch. -/
theorem aggregateTerminalProduct_mem_exact_residual_tail_box
    (p : FlagDegree) (hy : middle p ≤ 135) (Q : P4) (hQ : Q ≠ 0)
    (hRsmall : Q.degreeOf (2 : Fin 4) < 2130706433)
    (hL : wt residualTotalWeights Q ≤ 14261 - total p)
    (hcontact : wt (contactWeights 131071) Q ≤
      20131293 - retainedContact 131071 p - 1) :
    aggregateTerminalProduct Q ∈ RCN174.globalCoefficientBox K
      (20131293 - retainedContact 131071 p) 131071
        (14261 - total p) 1 := by
  have hyraw : p.yz + p.all ≤ 135 := by
    simpa only [middle] using hy
  have hD : 0 < 20131293 - retainedContact 131071 p := by
    unfold retainedContact middle
    omega
  apply (mem_globalCoefficientBox_iff (aggregateTerminalProduct Q)
    (20131293 - retainedContact 131071 p) 131071
      (14261 - total p) 1 hD).mpr
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
    have hcontact' : MvPolynomial.weightedTotalDegree (contactWeights 131071) Q ≤
        20131293 - retainedContact 131071 p - 1 := by
      simpa only [wt] using hcontact
    change MvPolynomial.weightedTotalDegree (contactWeights 131071)
      (aggregateTerminalProduct Q) +
        (131071 - 1) * (∑ F ∈ positiveRFactors Q, chainLength F) ≤
          MvPolynomial.weightedTotalDegree (contactWeights 131071) Q at hterminal
    change MvPolynomial.weightedTotalDegree (contactWeights 131071)
      (aggregateTerminalProduct Q) ≤
        20131293 - retainedContact 131071 p - 1
    omega

/-- Positive-factor branch of the residual grouped bound. -/
theorem residual_grouped_positive
    (p : FlagDegree) (hs : p.all ≤ 29) (hy : middle p ≤ 135)
    (ht : total p ≤ 6676)
    (Q : P4) (hQ : Q ≠ 0)
    (hpositive : (positiveRFactors Q).Nonempty)
    (hY : wt residualYSWeights Q ≤ 153 - middle p)
    (hS : wt residualSWeights Q ≤ 34 - p.all)
    (hL : wt residualTotalWeights Q ≤ 14261 - total p)
    (hcontact : wt (contactWeights 131071) Q ≤
      20131293 - retainedContact 131071 p - 1)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781) :
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      (residualBGroupedStage p).regularCountCap + residualBMaxEscapeDot +
        (residualBTailStage p).countCap := by
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
    exact (hdegreeR.trans hS).trans_lt
      ((Nat.sub_le _ _).trans_lt (by decide))
  have hscaled :
      (allPositiveExactChainSeeds Q selected Gamma).card *
          (181363 - 131071) ≤
        groupedDerivativeNumerator 262144 131071 181363
          (262144 - 181363) (153 - middle p) (34 - p.all)
          (14261 - total p) := by
    have hraw := allPositiveExactChainSeeds_grouped_of_cumulativeCaps
        Q hQ selected Gamma (Finset.univ : Finset I)
        IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
        2130706433 131071 181363 80781
        (153 - middle p) (34 - p.all) (14261 - total p)
        (by decide) (by decide) (by decide)
        (by norm_num [I, IRSProfile.Index]) (by omega)
        hY hS hL
        (by exact (Nat.sub_le _ _).trans_lt (by decide))
        (by exact (Nat.sub_le _ _).trans_lt (by decide))
        (by exact (Nat.sub_le _ _).trans_lt (by decide))
        (sub_pair_characteristic_gate p)
        (fun gamma hgamma ↦ hdegree gamma (hsub hgamma))
        (fun gamma hgamma ↦ hagreement gamma (hsub hgamma))
        (RCN243.noLargeSelectedPencil_mono selected Gamma _
          131071 80781 hsub hno)
    have hnodes : (Finset.univ : Finset I).card = 262144 := by
      norm_num [I, IRSProfile.Index]
    rw [hnodes] at hraw
    exact hraw
  have hterminalSmall := aggregateTerminalProduct_mem_tail_box
    131071 (20131293 - retainedContact 131071 p)
      (14261 - total p) Q hQ 2130706433 hRsmall hpositive
      (hcontact.trans (Nat.sub_le _ _)) hL
  have hDmono :
      20131293 - retainedContact 131071 p - (131071 - 1) + 1 ≤
        131071 * (153 - middle p) := by
    have hord := LocatorResidualRegular6803.flag_order p
    have hraw : p.all ≤ 131071 * middle p := by
      calc
        p.all ≤ middle p := hord.1
        _ = 1 * middle p := by omega
        _ ≤ 131071 * middle p := Nat.mul_le_mul_right _ (by decide)
    have hret := Nat.sub_add_cancel hraw
    have hretSmall : retainedContact 131071 p ≤ 20131293 := by
      unfold retainedContact
      omega
    unfold retainedContact at hret ⊢
    omega
  have hterminalBox : aggregateTerminalProduct Q ∈
      RCN174.globalCoefficientBox K
        (131071 * (153 - middle p)) 131071 (14261 - total p) 1 := by
    intro d hd
    have h := hterminalSmall hd
    exact ⟨h.1.trans (Nat.sub_le _ _), h.2.1,
      h.2.2.trans_le hDmono⟩
  have htail : (aggregateTerminalSeeds Q selected Gamma).card ≤
      (residualBTailStage p).countCap := by
    exact residual_tail_counter p hy ht selected Gamma u0 u1
      hdegree hagreement hno (aggregateTerminalProduct Q)
      (aggregateTerminalProduct_ne_zero Q hQ 2130706433 hRsmall)
      (aggregateTerminalProduct_R_degree Q) hterminalBox
  exact residualB_allGroupedNonRegularSeeds_card_le_maxEscape
    p Q selected Gamma hscaled htail

/-- Branch-free residual grouped bound.  Charging the exact retained contact
tail makes the theorem valid even when `positiveRFactors Q` is empty. -/
theorem residual_grouped_exact
    (p : FlagDegree) (hs : p.all ≤ 29) (hy : middle p ≤ 135)
    (ht : total p ≤ 6676)
    (Q : P4) (hQ : Q ≠ 0)
    (hY : wt residualYSWeights Q ≤ 153 - middle p)
    (hS : wt residualSWeights Q ≤ 34 - p.all)
    (hL : wt residualTotalWeights Q ≤ 14261 - total p)
    (hcontact : wt (contactWeights 131071) Q ≤
      20131293 - retainedContact 131071 p - 1)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781) :
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      (residualBGroupedStage p).regularCountCap + residualBMaxEscapeDot +
        (residualBExactTailStage p).countCap := by
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
    exact (hdegreeR.trans hS).trans_lt
      ((Nat.sub_le _ _).trans_lt (by decide))
  have hscaled :
      (allPositiveExactChainSeeds Q selected Gamma).card *
          (181363 - 131071) ≤
        groupedDerivativeNumerator 262144 131071 181363
          (262144 - 181363) (153 - middle p) (34 - p.all)
          (14261 - total p) := by
    have hraw := allPositiveExactChainSeeds_grouped_of_cumulativeCaps
        Q hQ selected Gamma (Finset.univ : Finset I)
        IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
        2130706433 131071 181363 80781
        (153 - middle p) (34 - p.all) (14261 - total p)
        (by decide) (by decide) (by decide)
        (by norm_num [I, IRSProfile.Index]) (by omega)
        hY hS hL
        (by exact (Nat.sub_le _ _).trans_lt (by decide))
        (by exact (Nat.sub_le _ _).trans_lt (by decide))
        (by exact (Nat.sub_le _ _).trans_lt (by decide))
        (sub_pair_characteristic_gate p)
        (fun gamma hgamma ↦ hdegree gamma (hsub hgamma))
        (fun gamma hgamma ↦ hagreement gamma (hsub hgamma))
        (RCN243.noLargeSelectedPencil_mono selected Gamma _
          131071 80781 hsub hno)
    have hnodes : (Finset.univ : Finset I).card = 262144 := by
      norm_num [I, IRSProfile.Index]
    rw [hnodes] at hraw
    exact hraw
  have hterminalBox := aggregateTerminalProduct_mem_exact_residual_tail_box
    p hy Q hQ hRsmall hL hcontact
  have htail : (aggregateTerminalSeeds Q selected Gamma).card ≤
      (residualBExactTailStage p).countCap := by
    exact residual_exact_tail_counter p hs hy ht selected Gamma u0 u1
      hdegree hagreement hno (aggregateTerminalProduct Q)
      (aggregateTerminalProduct_ne_zero Q hQ 2130706433 hRsmall)
      (aggregateTerminalProduct_R_degree Q) hterminalBox
  have hbase : (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      (residualBGroupedStage p).regularCountCap + residualBEscapeDot p +
        (residualBExactTailStage p).countCap := by
    exact allGroupedNonRegularSeeds_card_le_adjacent_add_tail
      Q selected Gamma 262144 131071 181363
        (153 - middle p) (34 - p.all) (14261 - total p)
        (residualBExactTailStage p).countCap (by omega) hscaled htail
  exact hbase.trans (Nat.add_le_add_right
    (Nat.add_le_add_left (residualBEscapeDot_le_max p) _) _)

end

end ProximityPrize.SubmissionLower.LocatorResidualGrouped6803
