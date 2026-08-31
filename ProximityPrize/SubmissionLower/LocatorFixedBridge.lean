import ProximityPrize.SubmissionLower.LocatorFixedConsumer
import ProximityPrize.SubmissionLower.LocatorSelectedCaps
import ProximityPrize.SubmissionLower.LocatorAuxiliarySelection
import ProximityPrize.SubmissionLower.LocatorQuotientReplacement
import ProximityPrize.SubmissionLower.LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorFixedBridge
open ProximityPrize.Benchmark
open scoped Classical
open RCN095 RCN180 RCN101 RCN234 RCN156 RCN275 RCN238 RCN243 RCN259 RCN319
open RCN266 RCN130 RCN140
open LocatorSelection LocatorFactorAggregate LocatorFactorReplacement
open LocatorReplacementGrid LocatorReplacementData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
private abbrev regularBound:ℕ:=271423674026155232
private def specialChosenCost (p:FlagDegree):ℕ:=
  if total p≤ 1311 then
    paddedCost 131072 131073 (LocatorFactorAggregate.cap 1311 49 10)
  else if middle p≤ 48 then
    paddedCost 131072 131073 (LocatorFactorAggregate.cap 1407 48 10)
  else
    paddedCost 131072 131073 (LocatorFactorAggregate.cap 1407 49 10)
private def specialRestCost (p:FlagDegree):ℕ:=
  if total p≤ 1311 then
    paddedCost 131072 131073 (LocatorFactorAggregate.cap 904 27 6)
  else if middle p≤ 48 then
    paddedCost 131072 131073 (LocatorFactorAggregate.cap 872 27 6)
  else
    paddedCost 131072 131073 (LocatorFactorAggregate.cap 872 24 6)
private theorem special_geometry (p:FlagDegree) (c:Cell)
    (hc:InCell p c) (hspecial:Special c):
    p.all=10∧ 46≤ middle p∧ middle p≤ 49∧
      1280≤ total p∧ total p≤ 1407:=by
  have hs:=special_coordinates c hspecial
  have hyhi:yhi c=49:=by
    norm_num [yhi,hs.2.1]
  have hthi:thi c=1407:=by
    norm_num [thi,hs.2.2]
  exact ⟨hc.all_eq.trans hs.1,hs.2.1 ▸ hc.ylo_le,
    hyhi ▸ hc.middle_le_yhi,hs.2.2 ▸ hc.tlo_le,
    hthi ▸ hc.total_le_thi⟩
private theorem special_count_le (p:FlagDegree) (c:Cell)
    (hc:InCell p c) (hspecial:Special c) (count:ℕ)
    (hcount:count≤ paddedCost 131072 131073 p):
    count≤ specialChosenCost p:=by
  have hg:=special_geometry p c hc hspecial
  by_cases ht:total p≤ 1311
  · have hb:Below p (LocatorFactorAggregate.cap 1311 49 10):=
      below_cap_of_bounds p 1311 49 10 (by decide) (by decide)
        (by omega) (by omega) ht
    exact hcount.trans (by
      simpa only [specialChosenCost,if_pos ht] using
        paddedCost_mono 131072 131073 hb)
  · by_cases hy:middle p≤ 48
    · have hb:Below p (LocatorFactorAggregate.cap 1407 48 10):=
        below_cap_of_bounds p 1407 48 10 (by decide) (by decide)
          (by omega) hy hg.2.2.2.2
      exact hcount.trans (by
        simpa only [specialChosenCost,if_neg ht,if_pos hy] using
          paddedCost_mono 131072 131073 hb)
    · have hb:Below p (LocatorFactorAggregate.cap 1407 49 10):=
        below_cap_of_bounds p 1407 49 10 (by decide) (by decide)
          (by omega) hg.2.2.1 hg.2.2.2.2
      exact hcount.trans (by
        simpa only [specialChosenCost,if_neg ht,if_neg hy] using
          paddedCost_mono 131072 131073 hb)
private theorem remainingCost_le_cap (p q:FlagDegree) (h:Below
    (remainingCap 2184 73 16 p) q):
    remainingCost 2184 73 16 131072 131073 p≤
      paddedCost 131072 131073 q:=by
  by_cases hz:(remainingCap 2184 73 16 p).all=0
  · rw [remainingCost,if_pos hz]
    exact Nat.zero_le _
  · rw [remainingCost,if_neg hz]
    exact paddedCost_mono 131072 131073 h
private theorem special_remaining_le (p:FlagDegree) (c:Cell)
    (hc:InCell p c) (hspecial:Special c):
    remainingCost 2184 73 16 131072 131073 p≤ specialRestCost p:=by
  have hg:=special_geometry p c hc hspecial
  have hr:=remainingCap_cumulative 2184 73 16 p
  by_cases ht:total p≤ 1311
  · have hb:Below (remainingCap 2184 73 16 p)
        (LocatorFactorAggregate.cap 904 27 6):=by
      apply below_cap_of_bounds _ 904 27 6 (by decide) (by decide)
      · rw [hr.1]
        exact (Nat.min_le_left _ _).trans (by omega)
      · rw [hr.2.1]
        exact (Nat.min_le_left _ _).trans (by omega)
      · rw [hr.2.2]
        omega
    simpa only [specialRestCost,if_pos ht] using remainingCost_le_cap p _ hb
  · by_cases hy:middle p≤ 48
    · have hb:Below (remainingCap 2184 73 16 p)
          (LocatorFactorAggregate.cap 872 27 6):=by
        apply below_cap_of_bounds _ 872 27 6 (by decide) (by decide)
        · rw [hr.1]
          exact (Nat.min_le_left _ _).trans (by omega)
        · rw [hr.2.1]
          exact (Nat.min_le_left _ _).trans (by omega)
        · rw [hr.2.2]
          omega
      simpa only [specialRestCost,if_neg ht,if_pos hy] using
        remainingCost_le_cap p _ hb
    · have hb:Below (remainingCap 2184 73 16 p)
          (LocatorFactorAggregate.cap 872 24 6):=by
        apply below_cap_of_bounds _ 872 24 6 (by decide) (by decide)
        · rw [hr.1]
          exact (Nat.min_le_left _ _).trans (by omega)
        · rw [hr.2.1]
          exact (Nat.min_le_left _ _).trans (by omega)
        · rw [hr.2.2]
          omega
      simpa only [specialRestCost,if_neg ht,if_neg hy] using
        remainingCost_le_cap p _ hb
private theorem special_cost_fits (p:FlagDegree):
    specialChosenCost p+specialRestCost p≤ regularBound:=by
  by_cases ht:total p≤ 1311
  · simp only [specialChosenCost,specialRestCost,if_pos ht]
    decide
  · by_cases hy:middle p≤ 48
    · simp only [specialChosenCost,specialRestCost,if_neg ht,if_pos hy]
      decide
    · simp only [specialChosenCost,specialRestCost,if_neg ht,if_neg hy]
      decide
theorem gcd_fixed_count_le
    (u0 u1:I→ K) (S:SelectedPair u0 u1)
    (selected:K→ Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈ Gamma,(selected gamma).natDegree≤ 131071)
    (hagreement:∀ gamma∈ Gamma,181756≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80388):
    (LocatorCover.fixed
      (fun gamma => (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card≤
      regularBound+LocatorArithmetic.fixedSingular.countCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K→ P4→+* Polynomial K:=
    fun gamma => (specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  have hH:H≠ 0:=gcd_ne_zero_of_left S.QA_ne
  have hHflagA:H∈ RCN100.globalCoefficientBox K 9996580 131071 79970 16:=
    LocatorCaps.full_A_divisor_mem_box u0 u1 H hH S.common_divides_A
  have hHcaps:=(mem_flagGlobalCoefficientBox_iff H
    9996580 131071 79970 16 (by decide)).mp hHflagA
  have hT:wt residualTotalWeights H≤ 2184:=S.common_total_le
  have hYS:wt residualYSWeights H≤ 73:=S.common_ys_le
  have hS:wt residualSWeights H≤ 16:=S.common_slope_le
  have hflag:H∈ RCN100.globalCoefficientBox K 9996580 131071 2184 16:=
    (mem_flagGlobalCoefficientBox_iff H 9996580 131071 2184 16 (by decide)).mpr
      ⟨hT,hS,hHcaps.2.2⟩
  have hbox:=flag_box_to_ordinary K 9996580 131071 2184 16 H hflag
  have hsupport:ResidualSupportData LocatorFixedConsumer.wholeSupport H:=
    ⟨hS,hYS,hT⟩
  have hsub:Delta ⊆ Gamma:=by
    intro gamma hg
    have hm:gamma∈ Gamma∧ (phi gamma) (gcd12 S.QA S.QB)=0:=by
      simpa only [Delta,LocatorCover.fixed,Finset.mem_filter] using hg
    exact hm.1
  have hsolution:∀ gamma∈ Delta,specialization K (selected gamma) gamma H=0:=by
    intro gamma hg
    exact LocatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hg
  have hdegreeD:∀ gamma∈ Delta,(selected gamma).natDegree≤ 131071:=
    fun gamma hg => hdegree gamma (hsub hg)
  have hagreementD:∀ gamma∈ Delta,181756≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma * u1 i)).card:=
    fun gamma hg => hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80388:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80388 hsub hno
  let p:=regularCumulativeFlag H
  have hfcaps (F:RegularIndex H):
      (p F).all≤ 16∧ middle (p F)≤ 73∧ total (p F)≤ 2184:=by
    have hf:=LocatorFixed.factor_support H hH hsupport F
    have hc:=originalCumulativeFlag_cumulative F.1
    refine ⟨?_,?_,?_⟩
    · simpa only [p,regularCumulativeFlag,hc.1,
        LocatorFixedConsumer.wholeSupport] using hf.s_weight
    · simpa only [p,regularCumulativeFlag,middle,hc.2.1,
        LocatorFixedConsumer.wholeSupport] using hf.ys_weight
    · simpa only [p,regularCumulativeFlag,total,hc.2.2,
        LocatorFixedConsumer.wholeSupport] using hf.total_weight
  have hfpos (F:RegularIndex H):1≤ (p F).all:=by
    have hne:(regularCumulativeFlag H F).all≠ 0:=
      Nat.ne_of_gt (regularCumulativeFlag_positive H F)
    simpa only [p] using Nat.one_le_iff_ne_zero.mpr hne
  let qCost:RegularIndex H→ ℕ:=fun F =>
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    if Special c then specialChosenCost (p F) else chosenCost c
  have hqCost (F:RegularIndex H)
      (hbad:Bad 2184 131072 131073 regularBound (p F)):
      (regularSeeds H selected Delta F).card≤ qCost F:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=
      cellOf_bounds (p F) (hfpos F) (hfcaps F).1
        (hfcaps F).2.1 (hfcaps F).2.2
    have hown:=LocatorFixed.regular_factor_count 9996580
      LocatorFixedConsumer.wholeSupport (by decide) (by decide)
      (by decide) (by decide) (by decide)
      H hH hbox hsupport selected Delta u0 u1 hdegreeD hagreementD hnoD F
    by_cases hspecial:Special c
    · simpa only [qCost,c,if_pos hspecial] using
        special_count_le (p F) c hc hspecial _ hown
    · have hf:=RCN167.positiveRFactors_spec H F.1 F.2
      have hdiv95:∀ v:RCN180.ConstraintKernel (K:=K)
          17266820 131071 3200 29 95 IRSProfile.domain u0 u1,
          F.1 ∣ RCN100.reconstruct K 17266820 131071 3200 29 v.1:=by
        intro v
        exact hf.2.1.trans
          (LocatorAuxiliarySelection.common_divides_A95_small S 3200 (by decide) v)
      have hdiv72:∀ v:RCN180.ConstraintKernel (K:=K)
          13086432 131071 24000 21 72 IRSProfile.domain u0 u1,
          F.1 ∣ RCN100.reconstruct K 13086432 131071 24000 21 v.1:=by
        intro v
        exact hf.2.1.trans
          (LocatorAuxiliarySelection.common_divides_A72_small S 24000 (by decide) v)
      have hdiv126:∀ v:RCN180.ConstraintKernel (K:=K)
          22901256 131071 2814 39 126 IRSProfile.domain u0 u1,
          F.1 ∣ RCN100.reconstruct K 22901256 131071 2814 39 v.1:=by
        intro v
        exact hf.2.1.trans
          (LocatorAuxiliarySelection.common_divides_A126_small S 2814 (by decide) v)
      have h:=LocatorQuotientReplacement.regularSeeds_count_le_chosen
        u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
        hdiv95 hdiv72 hdiv126 c hc hspecial hbad hown
      simpa only [qCost,c,if_neg hspecial] using h
  have hcell (F:RegularIndex H)
      (hbad:Bad 2184 131072 131073 regularBound (p F)):
      cellCost 2184 73 16 131072 131073 (p F) (qCost F)≤
        regularBound:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=
      cellOf_bounds (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    by_cases hspecial:Special c
    · calc
        cellCost 2184 73 16 131072 131073 (p F) (qCost F)=
            min (paddedCost 131072 131073 (p F)) (specialChosenCost (p F))+
              remainingCost 2184 73 16 131072 131073 (p F):=by
                simp only [cellCost,qCost,c,if_pos hspecial]
        _≤ specialChosenCost (p F)+specialRestCost (p F):=
          Nat.add_le_add (Nat.min_le_right _ _)
            (special_remaining_le (p F) c hc hspecial)
        _≤ regularBound:=special_cost_fits (p F)
    · have hv:Valid c:=valid_of_inCell (p F) c hc
      have hnr:¬ RateFits c:=by
        intro hrate
        have hglobal:=LocatorRateCover.global_rate_of_endpoints
          (p F) 2184 (yhi c) (r c) regularBound
          (by dsimp [c,r];omega) hc.all_eq hc.middle_le_yhi
          (by dsimp [c,yhi];omega) (hfcaps F).2.2 hrate.1 hrate.2
        exact (not_lt_of_ge hglobal) hbad
      exact cellCost_le_of_grid_bound (p F) c (qCost F) hc
        (by simpa only [qCost,c,if_neg hspecial] using
          chosenCost_with_rest c hv hnr hspecial)
  exact LocatorFixedConsumer.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD qCost hqCost hcell
end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
