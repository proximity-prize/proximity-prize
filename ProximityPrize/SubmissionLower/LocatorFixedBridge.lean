import ProximityPrize.SubmissionLower.LocatorFixedConsumer
import ProximityPrize.SubmissionLower.LocatorSelectedCaps
import ProximityPrize.SubmissionLower.LocatorAuxiliarySelection
import ProximityPrize.SubmissionLower.LocatorQuotientReplacement
import ProximityPrize.SubmissionLower.LocatorCover

/- The whole Y50/R50/B97 divisor has actual T/YS/R budgets 1796/66/14.
Each high regular factor is replaced, when needed, by one fixed low-contact
A77/2567 quotient. The original singular set is counted only once. -/
namespace ProximityPrize.SubmissionLower.LocatorFixedBridge
open ProximityPrize.Benchmark
open scoped Classical
open RCN180 RCN101 RCN234 RCN156 RCN275 RCN238 RCN243 RCN259 RCN319
open RCN266 RCN130 RCN140
open LocatorSelection LocatorFactorAggregate
open LocatorReplacementGrid LocatorReplacementData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

theorem gcd_fixed_count_le
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181845 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80299) :
    (LocatorCover.fixed
      (fun gamma => (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      271500000000000000 + LocatorArithmetic.fixedSingular.countCap := by
  classical
  let H : P4 := gcd12 S.QA S.QB
  let phi : K → P4 →+* Polynomial K :=
    fun gamma => (specialization K (selected gamma) gamma).toRingHom
  let Delta : Finset K := LocatorCover.fixed phi Gamma S.QA S.QB
  have hH : H ≠ 0 := gcd_ne_zero_of_left S.QA_ne
  have hHflagC : H ∈ RCN100.globalCoefficientBox K 9092250 131071 100000 14 :=
    S.common_C_flag
  have hHcaps := (mem_flagGlobalCoefficientBox_iff H
    9092250 131071 100000 14 (by decide)).mp hHflagC
  have hT : wt residualTotalWeights H ≤ 1796 := S.common_total_le
  have hYS : wt residualYSWeights H ≤ 66 := S.common_ys_le
  have hS : wt residualSWeights H ≤ 14 := S.common_slope_le
  have hflag : H ∈ RCN100.globalCoefficientBox K 9092250 131071 1796 14 :=
    (mem_flagGlobalCoefficientBox_iff H 9092250 131071 1796 14 (by decide)).mpr
      ⟨hT, hS, hHcaps.2.2⟩
  have hbox := flag_box_to_ordinary K 9092250 131071 1796 14 H hflag
  have hsupport : ResidualSupportData LocatorFixedConsumer.wholeSupport H :=
    ⟨hS, hYS, hT⟩
  have hsub : Delta ⊆ Gamma := by
    intro gamma hg
    have hm : gamma ∈ Gamma ∧ (phi gamma) (gcd12 S.QA S.QB) = 0 := by
      simpa only [Delta, LocatorCover.fixed, Finset.mem_filter] using hg
    exact hm.1
  have hsolution : ∀ gamma ∈ Delta, specialization K (selected gamma) gamma H = 0 := by
    intro gamma hg
    exact LocatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hg
  have hdegreeD : ∀ gamma ∈ Delta, (selected gamma).natDegree ≤ 131071 :=
    fun gamma hg => hdegree gamma (hsub hg)
  have hagreementD : ∀ gamma ∈ Delta, 181845 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card :=
    fun gamma hg => hagreement gamma (hsub hg)
  have hnoD : NoLargeSelectedPencil selected Delta 131071 80299 :=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80299 hsub hno
  let p := regularCumulativeFlag H
  have hfcaps (F : RegularIndex H) :
      (p F).all ≤ 14 ∧ middle (p F) ≤ 66 ∧ total (p F) ≤ 1796 := by
    have hf := LocatorFixed.factor_support H hH hsupport F
    have hc := originalCumulativeFlag_cumulative F.1
    refine ⟨?_, ?_, ?_⟩
    · simpa only [p, regularCumulativeFlag, hc.1,
        LocatorFixedConsumer.wholeSupport] using hf.s_weight
    · simpa only [p, regularCumulativeFlag, middle, hc.2.1,
        LocatorFixedConsumer.wholeSupport] using hf.ys_weight
    · simpa only [p, regularCumulativeFlag, total, hc.2.2,
        LocatorFixedConsumer.wholeSupport] using hf.total_weight
  let qCost : RegularIndex H → ℕ := fun F =>
    if hh : 7 ≤ (p F).all then
      chosenCost (cellOf (p F) hh (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2)
    else 0
  have hqCost (F : RegularIndex H) (h8 : 7 ≤ (p F).all) :
      (regularSeeds H selected Delta F).card ≤ qCost F := by
    dsimp only [qCost]
    rw [dif_pos h8]
    have hf := RCN167.positiveRFactors_spec H F.1 F.2
    have hdiv : ∀ v : RCN180.ConstraintKernel (K := K)
        14002065 131071 2567 23 77 IRSProfile.domain u0 u1,
        F.1 ∣ RCN100.reconstruct K 14002065 131071 2567 23 v.1 := by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A77_small S 2567 (by decide) v)
    have hown := LocatorFixed.regular_factor_count 9092250
      LocatorFixedConsumer.wholeSupport (by decide) (by decide)
      (by decide) (by decide) (by decide)
      H hH hbox hsupport selected Delta u0 u1 hdegreeD hagreementD hnoD F
    exact LocatorQuotientReplacement.regularSeeds_count_le_chosen
      u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero hdiv
      (cellOf (p F) h8 (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2)
      (cellOf_bounds (p F) h8 (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2) hown
  have hcell (F : RegularIndex H) (h8 : 7 ≤ (p F).all) :
      LocatorFactorReplacement.cellCost 1796 66 14 131072 131073
        (p F) (qCost F) ≤ 271500000000000000 := by
    dsimp only [qCost]
    rw [dif_pos h8]
    exact cellCost_le_of_choice chosenCost chosenCost_with_rest
      (p F) h8 (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
  exact LocatorFixedConsumer.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD qCost hqCost hcell

end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
