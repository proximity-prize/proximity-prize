import ProximityPrize.SubmissionLower.RegularColonFixed
import ProximityPrize.SubmissionLower.RegularColonExclusion
import ProximityPrize.SubmissionLower.TwoInterpolatorCover

/- The fixed count below concerns the actual
   gcd of the selected interpolants.  In particular, the full-slope regular
   exclusion is proved from the whole A-kernel divisibility, not assumed as
   a numerical or factor-wise counting hypothesis. -/
namespace ProximityPrize.SubmissionLower.RegularColonFixedBridge
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open RCN081 RCN319 RCN286
open RCN180 RCN101
open RCN234 RCN156
open RCN275 RCN130
open RCN266 RCN140
open RCN238 RCN243 RCN259
open TwoKernelSelection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

/- This is deliberately the same plain-GCD instance as SelectedPair.  The
   normalized GCD used internally by factor enumeration is not substituted
   for the gcd in the fixed/residual partition. -/
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

theorem gcd_fixed_count_le
    (T : ℕ) (hT : T = 1280 ∨ T = 1282)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (htotal : wt residualTotalWeights (gcd12 S.QA S.QB) ≤ T)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 182032 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80112) :
    (TwoInterpolatorCover.fixed
      (fun gamma => (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      RegularColonArithmetic.fixedCost (T - 53) 40 10 +
        (RegularColonArithmetic.fixedSingular T).countCap := by
  classical
  let H : P4 := gcd12 S.QA S.QB
  let phi : K → P4 →+* Polynomial K :=
    fun gamma => (specialization K (selected gamma) gamma).toRingHom
  let Delta : Finset K := TwoInterpolatorCover.fixed phi Gamma S.QA S.QB
  have hTlo : 56 ≤ T := by rcases hT with rfl | rfl <;> decide
  have hH : H ≠ 0 := gcd_ne_zero_of_left S.QA_ne
  have hHdivA : H ∣ S.QA := gcd_dvd_left S.QA S.QB
  have hHflagA : H ∈ RCN100.globalCoefficientBox
      K 7645344 131071 240000 12 :=
    mem_flagGlobalCoefficientBox_of_dvd H S.QA
      7645344 131071 240000 12 S.QA_ne hHdivA S.QA_flag
  have hHcaps := (mem_flagGlobalCoefficientBox_iff H
    7645344 131071 240000 12 (by decide)).mp hHflagA
  have hHflagT : H ∈ RCN100.globalCoefficientBox
      K 7645344 131071 T 12 :=
    (mem_flagGlobalCoefficientBox_iff H 7645344 131071 T 12 (by decide)).mpr
      ⟨htotal, hHcaps.2.1, hHcaps.2.2⟩
  have hbox : H ∈ RCN174.globalCoefficientBox K 7645344 131071 T 12 :=
    flag_box_to_ordinary K 7645344 131071 T 12 H hHflagT
  have hYS : wt residualYSWeights H ≤ 56 :=
    (TwoKernelCaps.SelectedPair.common_caps S).1
  have hsupport : ResidualSupportData (RegularColonFixed.wholeSupport T hTlo) H :=
    ⟨hHcaps.2.1, hYS, htotal⟩
  have hsub : Delta ⊆ Gamma := by
    intro gamma hg
    have hm : gamma ∈ Gamma ∧ (phi gamma) (gcd12 S.QA S.QB) = 0 := by
      simpa only [Delta, TwoInterpolatorCover.fixed, Finset.mem_filter] using hg
    exact hm.1
  have hsolution : ∀ gamma ∈ Delta, specialization K (selected gamma) gamma H = 0 := by
    intro gamma hgamma
    exact TwoInterpolatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hgamma
  have hdegreeD : ∀ gamma ∈ Delta, (selected gamma).natDegree ≤ 131071 :=
    fun gamma hgamma => hdegree gamma (hsub hgamma)
  have hagreementD : ∀ gamma ∈ Delta, 182032 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card :=
    fun gamma hgamma => hagreement gamma (hsub hgamma)
  have hnoD : NoLargeSelectedPencil selected Delta 131071 80112 :=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80112 hsub hno

  /- For an active factor, its one regular seed provides all the business
     inputs required by the colon exclusion.  Factor divisibility is lifted
     to every A-kernel element through SelectedPair.common_divides_A. -/
  have hfull : ∀ R : RegularIndex H, (regularSeeds H selected Delta R).Nonempty →
      (regularCumulativeFlag H R).all = 12 →
        FactorAggregate.middle (regularCumulativeFlag H R) ≤ 53 := by
    intro R hactive hslope
    obtain ⟨gamma, hgamma⟩ := hactive
    have hgammaD : gamma ∈ Delta := (regularSeeds_subset H selected Delta R) hgamma
    have hregular : RegularSolution R.1 (selected gamma) gamma :=
      (Finset.mem_filter.mp hgamma).2
    have hRdata := RCN167.positiveRFactors_spec H R.1 R.2
    have hRne : R.1 ≠ 0 := hRdata.1.ne_zero
    have hRdiv : ∀ v : AKernel u0 u1,
        R.1 ∣ RCN100.reconstruct
          K 7645344 131071 240000 12 v.1 := by
      intro v
      exact hRdata.2.1.trans (S.common_divides_A v)
    have hRdegree : R.1.degreeOf (2 : Fin 4) = 12 := by
      simpa only [regularCumulativeFlag, originalCumulativeFlag_all] using hslope
    let nodes : Finset I := (Finset.univ : Finset I).filter (fun i =>
      (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
    have hnodes : 182032 ≤ nodes.card := hagreementD gamma hgammaD
    have hvalues : ∀ i ∈ nodes,
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hbound := RegularColonExclusion.full_slope_regular_factor_ys_le
      u0 u1 R.1 hRne hRdiv hRdegree (selected gamma) gamma nodes
      (hdegreeD gamma hgammaD) hnodes hvalues hregular
    change (originalCumulativeFlag R.1).yz + (originalCumulativeFlag R.1).all ≤ 53
    rw [(originalCumulativeFlag_cumulative R.1).2.1]
    exact hbound
  exact RegularColonFixed.fixed_count_le T hT H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD hfull

end
end ProximityPrize.SubmissionLower.RegularColonFixedBridge
