import ProximityPrize.SubmissionLower.MergedInfra6815_12
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_13
import ProximityPrize.SubmissionLower.LowerGeometry
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.ExactInitialCharge6815
open scoped BigOperators
open RCN260 AsymmetricHelper
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000

def num (L U S r y t : ℕ) : ℕ :=
  leftRegularNumerator (PhasePotential6815.pair L U S r y t)
def cost (L U S r y t : ℕ) : ℕ :=
  leftRegularCountCap (PhasePotential6815.pair L U S r y t)

theorem num_formula (L U S r y t : ℕ) :
    num L U S r y t =
      131073*((1+2*131071*y)*(r*L+t*S)+131071*(2*r-1)*(y*L+t*U)+
        (1+2*131071*t)*(y*S+r*U))+80900*50174*(y*S+r*U) := by
  simp only [num,leftRegularNumerator,PhasePotential6815.pair,
    UnequalParameters.errors,UnequalParameters.gap,UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost,RCN294.dot]
  norm_num only [Nat.reduceSub,Nat.reduceAdd,Nat.reduceMul]
  ring

theorem cost_eq (L U S r y t : ℕ) : cost L U S r y t=num L U S r y t/50174 := by
  simp only [cost,num,leftRegularCountCap,PhasePotential6815.pair,UnequalParameters.gap,Nat.reduceSub]

theorem num_mono (L U S r y t capR capY capT : ℕ) (hr : r≤capR) (hy : y≤capY) (ht : t≤capT) :
    num L U S r y t≤num L U S capR capY capT := by
  rw [num_formula,num_formula]
  gcongr

theorem cost_mono (L U S r y t capR capY capT : ℕ) (hr : r≤capR) (hy : y≤capY) (ht : t≤capT) :
    cost L U S r y t≤cost L U S capR capY capT := by
  rw [cost_eq,cost_eq]
  exact Nat.div_le_div_right (num_mono L U S r y t capR capY capT hr hy ht)

theorem sum_num_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (L U S : ℕ) (r y t : ι → ℕ) :
    (∑ i∈s, num L U S (r i) (y i) (t i))≤
      num L U S (∑ i∈s, r i) (∑ i∈s, y i) (∑ i∈s, t i) := by
  have hterm (i : ι) (hi : i∈s) :
      num L U S (r i) (y i) (t i)≤
        131073*((1+2*131071*(∑ j∈s,y j))*(r i*L+t i*S)+
          131071*(2*(∑ j∈s,r j)-1)*(y i*L+t i*U)+
          (1+2*131071*(∑ j∈s,t j))*(y i*S+r i*U))+
          80900*50174*(y i*S+r i*U) := by
    have hr := Finset.single_le_sum (fun j (_ : j∈s) => Nat.zero_le (r j)) hi
    have hy := Finset.single_le_sum (fun j (_ : j∈s) => Nat.zero_le (y j)) hi
    have ht := Finset.single_le_sum (fun j (_ : j∈s) => Nat.zero_le (t j)) hi
    rw [num_formula]
    gcongr
  calc
    _≤∑ i∈s, (131073*((1+2*131071*(∑ j∈s,y j))*(r i*L+t i*S)+
          131071*(2*(∑ j∈s,r j)-1)*(y i*L+t i*U)+
          (1+2*131071*(∑ j∈s,t j))*(y i*S+r i*U))+
          80900*50174*(y i*S+r i*U)) := Finset.sum_le_sum hterm
    _=_ := by
      rw [num_formula]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]

theorem sum_cost_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (L U S : ℕ) (r y t : ι → ℕ) :
    (∑ i∈s, cost L U S (r i) (y i) (t i))≤
      cost L U S (∑ i∈s, r i) (∑ i∈s, y i) (∑ i∈s, t i) := by
  conv_rhs => rw [cost_eq]
  apply (Nat.le_div_iff_mul_le (by decide : 0<50174)).mpr
  calc
    _=∑ i∈s, cost L U S (r i) (y i) (t i)*50174 := by rw [Finset.sum_mul]
    _≤∑ i∈s, num L U S (r i) (y i) (t i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [cost_eq]
      exact Nat.div_mul_le_self _ _
    _≤_ := sum_num_le s L U S r y t

theorem helpers_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (L U S capR capY capT : ℕ) (r y t helper : ι → ℕ)
    (hhelper : ∀ i∈s, helper i≤cost L U S (r i) (y i) (t i))
    (hr : (∑ i∈s, r i)≤capR) (hy : (∑ i∈s, y i)≤capY) (ht : (∑ i∈s, t i)≤capT) :
    (∑ i∈s, helper i)≤cost L U S capR capY capT :=
  (Finset.sum_le_sum hhelper).trans ((sum_cost_le s L U S r y t).trans
    (cost_mono L U S _ _ _ capR capY capT hr hy ht))

theorem initial_helpers_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (pr py pt : ℕ) (r y t helper : ι → ℕ)
    (hhelper : ∀ i∈s, helper i≤cost 76330 182 39 (r i) (y i) (t i))
    (hrpos : ∀ i∈s, 1≤r i)
    (hry : ∀ i∈s, r i≤y i) (hyt : ∀ i∈s, y i≤t i)
    (hr : pr+(∑ i∈s, r i)≤50)
    (hy : py+(∑ i∈s, y i)≤229)
    (ht : pt+(∑ i∈s, t i)≤11192) :
    (∑ i∈s, helper i)≤
      let remT := 11192-pt
      let remY := min remT (229-py)
      let remR := min remY (50-pr)
      if remR=0 then 0 else cost 76330 182 39 remR remY remT := by
  have hrySum := Finset.sum_le_sum hry
  have hytSum := Finset.sum_le_sum hyt
  have ht' : (∑ i∈s,t i)≤11192-pt := by omega
  have hy' : (∑ i∈s,y i)≤min (11192-pt) (229-py) := by omega
  have hr' : (∑ i∈s,r i)≤min (min (11192-pt) (229-py)) (50-pr) := by omega
  dsimp only
  split_ifs with hz
  · have hs : s=∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      have hiSum := Finset.single_le_sum (fun j (_ : j∈s) => Nat.zero_le (r j)) hi
      have hiPos := hrpos i hi
      omega
    simp [hs]
  · exact helpers_sum_le s 76330 182 39 _ _ _ r y t helper hhelper hr' hy' ht'

end ProximityPrize.SubmissionLower.ExactInitialCharge6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.TerminalCharge6815
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem exists_terminal {ι : Type*} [DecidableEq ι]
    (count charge : ι → ℕ) (routeable : Finset ι → Prop) (ambient : Finset ι)
    (hroute : ∀ B, B ⊆ ambient → routeable B →
      ∃ U, U ⊂ B ∧ ∀ i ∈ B \ U, count i ≤ charge i) :
    ∃ U, U ⊆ ambient ∧ ¬ routeable U ∧
      ∀ i ∈ ambient \ U, count i ≤ charge i := by
  classical
  have aux : ∀ B : Finset ι, B ⊆ ambient →
      ∃ U, U ⊆ B ∧ ¬ routeable U ∧
        ∀ i ∈ B \ U, count i ≤ charge i := by
    intro B
    induction B using Finset.strongInduction with
    | H B ih =>
      intro hB
      by_cases hr : routeable B
      · obtain ⟨V, hV, hexit⟩ := hroute B hB hr
        obtain ⟨U, hU, hstop, hrest⟩ := ih V hV (hV.subset.trans hB)
        refine ⟨U, hU.trans hV.subset, hstop, ?_⟩
        intro i hi
        obtain ⟨hiB, hiU⟩ := Finset.mem_sdiff.mp hi
        by_cases hiV : i ∈ V
        · exact hrest i (Finset.mem_sdiff.mpr ⟨hiV, hiU⟩)
        · exact hexit i (Finset.mem_sdiff.mpr ⟨hiB, hiV⟩)
      · exact ⟨B, Finset.Subset.refl _, hr, by simp⟩
  exact aux ambient (Finset.Subset.refl _)

end ProximityPrize.SubmissionLower.TerminalCharge6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.ExactRemovalPhase6815
open scoped BigOperators
open ExactInitialCharge6815 TerminalCharge6815
set_option autoImplicit false
set_option maxHeartbeats 1000000

def tSlope (_L U S r y : ℕ) : ℕ :=
  131073*((1+2*131071*y)*S+131071*(2*r-1)*U+2*131071*(y*S+r*U))

theorem num_shift (L U S r y z : ℕ) :
    num L U S r y (y+z)=num L U S r y y+tSlope L U S r y*z := by
  rw [num_formula,num_formula]
  unfold tSlope
  ring

end ProximityPrize.SubmissionLower.ExactRemovalPhase6815
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.Lower80899.ActualExactPhase6815

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance LocatorBatchProductRoute Lower80899.BatchPowerRoute Lower80899.FactorSwitch Lower80899.Oracle

open LocatorPhase6800Oracle (Potential sumFlag sumFlag_all sumFlag_middle sumFlag_total RawBelow RawStrictSlopeBelow)
open LocatorBatchPhase6800 (regularAggregateFlag regularAggregateFlag_all
  regularAggregateFlag_middle regularAggregateFlag_total regularAggregateFlag_mono
  regularAggregateFlag_all_lt_of_ssubset regularAggregateFlag_raw_mono sum_phasePotential_eval)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

private theorem sourceFuel_pos (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) (ht : total p ≤ s.totalCap)
    (hy : middle p ≤ s.middleCap) (hs : p.all ≤ s.slopeCap) :
    1 ≤ s.fuel p := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  apply le_min
  · exact (Nat.le_div_iff_mul_le htotal).mpr (by simpa using ht)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hmiddle).mpr (by simpa using hy)
    · exact (Nat.le_div_iff_mul_le hr).mpr (by simpa using hs)

private theorem sourceFuel_feasible (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.fuel p * total p ≤ s.totalCap ∧
      s.fuel p * middle p ≤ s.middleCap ∧
      s.fuel p * p.all ≤ s.slopeCap := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  refine ⟨?_, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le htotal).mp
    exact min_le_left _ _
  · apply (Nat.le_div_iff_mul_le hmiddle).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  · apply (Nat.le_div_iff_mul_le hr).mp
    exact (min_le_right _ _).trans (min_le_right _ _)

private theorem div_remainder_lt (a b : ℕ) (hb : 0 < b) :
    a - (a / b) * b < b := by
  have hm := Nat.mod_lt a hb
  have heq := Nat.mod_add_div' a b
  omega

private theorem sourceFuel_terminal (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.totalCap - s.fuel p * total p < total p ∨
      s.middleCap - s.fuel p * middle p < middle p ∨
      s.slopeCap - s.fuel p * p.all < p.all := by
  have hall : 0 < p.all := by omega
  have hmiddle : 0 < middle p := hall.trans_le (all_le_middle p)
  have htotal : 0 < total p := hmiddle.trans_le (middle_le_total p)
  unfold SourceNumbers.fuel
  by_cases hT : s.totalCap / total p ≤
      min (s.middleCap / middle p) (s.slopeCap / p.all)
  · left
    rw [min_eq_left hT]
    exact div_remainder_lt s.totalCap (total p) htotal
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY : s.middleCap / middle p ≤ s.slopeCap / p.all
    · right; left
      rw [min_eq_left hY]
      exact div_remainder_lt s.middleCap (middle p) hmiddle
    · right; right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact div_remainder_lt s.slopeCap p.all hr

theorem charged_split
    (sound : PhaseSourceSound) (charge : FlagDegree → ℕ)
    (hpay : ∀ (p : FlagDegree) (j : ℕ),
      1≤p.all → p.all≤39 → middle p≤182 → total p≤11192 → j≤sound.source.fuel p →
      PowerRoute.stageCost sound.source.totalCap sound.source.middleCap sound.source.slopeCap
        (Oracle.exactRouteBox p) j≤charge p)
    (D m : ℕ)
    (hweighted : D = m * 181245)
    (hshape : D + sound.source.slopeCap ≤
      131071 * (sound.source.middleCap + 1))
    (hslopeM : sound.source.slopeCap ≤ m)
    (hmChar : m < 2130706433)
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181245 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (hgap : sound.source.gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A : Finset (RegularIndex H))
    (hroute : sound.source.Routeable (regularAggregateFlag H A))
    (hnarrowS : (regularAggregateFlag H A).all ≤ 39)
    (hnarrowY : middle (regularAggregateFlag H A) ≤ 182)
    (hnarrowT : total (regularAggregateFlag H A) ≤ 11192) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤
        charge (regularCumulativeFlag H F) := by
  classical
  let p := regularAggregateFlag H A
  have hr : 1 ≤ p.all := hroute.1
  have hA : A.Nonempty := by
    by_contra hzero
    have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hzero
    subst A
    simp [p, regularAggregateFlag, sumFlag] at hr
  have hfuel : 1 ≤ sound.source.fuel p :=
    sourceFuel_pos sound.source p hr hroute.2.1 hroute.2.2.1
      hroute.2.2.2.1
  have hfeasibleP := sourceFuel_feasible sound.source p hr
  have hterminalP := sourceFuel_terminal sound.source p hr
  have hfuelSlope : sound.source.fuel p ≤ sound.source.slopeCap := by
    calc
      sound.source.fuel p ≤ sound.source.slopeCap / p.all :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ sound.source.slopeCap := Nat.div_le_self _ _
  have hfuelM : sound.source.fuel p ≤ m := hfuelSlope.trans hslopeM
  have hfuelChar : sound.source.fuel p < 2130706433 :=
    hfuelM.trans_lt hmChar
  have hlowpos : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      0 < D - j * 50175 := by
    intro j hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hcapacity : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      D - j * 50175 ≤
        (m - j) * 181245 + j * (131071 - 1) := by
    intro j _hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hfield : A.card < ENat.card K := by
    have hcard : A.card ≤ p.all := by
      calc
        A.card = ∑ F ∈ A, 1 := by simp
        _ ≤ ∑ F ∈ A, (regularCumulativeFlag H F).all :=
          Finset.sum_le_sum (fun F _ => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (regularCumulativeFlag_positive H F)))
        _ = p.all := by simp only [p, regularAggregateFlag, sumFlag_all]
    calc
      (A.card : ENat) ≤ (39 : ℕ) := by
        exact_mod_cast hcard.trans hnarrowS
      _ < ENat.card K := by
        rw [ENat.card_eq_coe_fintype_card, RCN183.field_cardinality]
        norm_num
  have factor_le_aggregate (F : RegularIndex H) (hFA : F ∈ A) :
      (regularCumulativeFlag H F).all ≤ p.all ∧
      middle (regularCumulativeFlag H F) ≤ middle p ∧
      total (regularCumulativeFlag H F) ≤ total p := by
    have hsub : ({F} : Finset (RegularIndex H)) ⊆ A :=
      Finset.singleton_subset_iff.mpr hFA
    simpa [p, regularAggregateFlag, sumFlag, middle, total] using
      regularAggregateFlag_mono H hsub
  have factorFuel (F : RegularIndex H) (hFA : F ∈ A) (j : ℕ)
      (hj : j ≤ sound.source.fuel p) :
      j ≤ sound.source.fuel (regularCumulativeFlag H F) := by
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hFm : 1 ≤ middle (regularCumulativeFlag H F) :=
      hFr.trans (all_le_middle _)
    have hFt : 1 ≤ total (regularCumulativeFlag H F) :=
      hFm.trans (middle_le_total _)
    have hjT : j * total (regularCumulativeFlag H F) ≤
        sound.source.totalCap := by
      calc
        j * total (regularCumulativeFlag H F) ≤ j * total p :=
          Nat.mul_le_mul_left j hle.2.2
        _ ≤ sound.source.fuel p * total p :=
          Nat.mul_le_mul_right (total p) hj
        _ ≤ sound.source.totalCap := hfeasibleP.1
    have hjY : j * middle (regularCumulativeFlag H F) ≤
        sound.source.middleCap := by
      calc
        j * middle (regularCumulativeFlag H F) ≤ j * middle p :=
          Nat.mul_le_mul_left j hle.2.1
        _ ≤ sound.source.fuel p * middle p :=
          Nat.mul_le_mul_right (middle p) hj
        _ ≤ sound.source.middleCap := hfeasibleP.2.1
    have hjS : j * (regularCumulativeFlag H F).all ≤
        sound.source.slopeCap := by
      calc
        j * (regularCumulativeFlag H F).all ≤ j * p.all :=
          Nat.mul_le_mul_left j hle.1
        _ ≤ sound.source.fuel p * p.all :=
          Nat.mul_le_mul_right p.all hj
        _ ≤ sound.source.slopeCap := hfeasibleP.2.2
    unfold SourceNumbers.fuel
    apply le_min
    · exact (Nat.le_div_iff_mul_le hFt).mpr hjT
    · apply le_min
      · exact (Nat.le_div_iff_mul_le hFm).mpr hjY
      · exact (Nat.le_div_iff_mul_le hFr).mpr hjS
  have hgates : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      HelperPairGates
        (sound.source.totalCap - j * wt residualTotalWeights F.1)
        (sound.source.middleCap - j * wt residualYSWeights F.1)
        (sound.source.slopeCap - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := sound.stageGates (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [hR, hY, hT] using hs
  have hcharge : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      Lower80899.PowerRoute.stageCost sound.source.totalCap
        sound.source.middleCap sound.source.slopeCap
        (Lower80899.BatchPowerRoute.exactRouteBox F) j ≤
          charge (regularCumulativeFlag H F) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := hpay (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [Lower80899.BatchPowerRoute.exactRouteBox,
      Lower80899.Oracle.exactRouteBox, hR, hY, hT] using hs
  have hmpos : 0 < m := by omega
  have hDpos : 0 < D := by
    rw [hweighted]
    exact Nat.mul_pos hmpos (by decide)
  have hDa : D ≤ m * 181245 := hweighted.le
  have hP : regularProduct H A ≠ 0 := regularProduct_ne_zero H A
  have hcP : contactDec p ≤ wt (contactWeights 131071) (regularProduct H A) := by
    have h := LocatorArbitraryPowerAvoidance.contact_ge_ys 131071 (by decide)
      (regularProduct H A) hP
    simpa only [contactDec, p, regularAggregateFlag_middle,
      regularAggregateFlag_all] using h
  have hDcap : D - wt (contactWeights 131071) (regularProduct H A) ≤
      sound.source.contactCap p := by
    unfold SourceNumbers.contactCap
    omega
  have hbandThin : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
      (D - wt (contactWeights 131071) (regularProduct H A)) 50175
      (wt (contactWeights 131071) (regularProduct H A))
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
      (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
      (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
      (sound.source.fuel p) < sound.source.gap := by
    rcases hroute.2.2.2.2 with hold | hthin
    · have hold' : powerBandBudget 50175
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
          (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
          (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
          (sound.source.fuel p) < sound.source.gap := by
        simpa only [SourceNumbers.band, p, regularAggregateFlag_total,
          regularAggregateFlag_middle, regularAggregateFlag_all] using hold
      exact (LocatorArbitraryPowerAvoidance.powerBandBudgetThin_le
        _ _ _ _ _ _ _ _ _ _ _).trans_lt hold'
    · have hthin' : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
          (sound.source.contactCap p) 50175 (contactDec p)
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
          (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
          (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
          (sound.source.fuel p) < sound.source.gap := by
        simpa only [SourceNumbers.bandThin, p, regularAggregateFlag_total,
          regularAggregateFlag_middle, regularAggregateFlag_all] using hthin
      exact (LocatorArbitraryPowerAvoidance.powerBandBudgetThin_mono 131071 50175
        (sound.source.fuel p) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hDcap hcP le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl).trans_lt hthin'
  apply exists_strict_helper_split_of_batch_source_thin D
    sound.source.totalCap sound.source.slopeCap m sound.source.middleCap
    sound.source.gap 50175 (sound.source.fuel p)
  · exact hDpos
  · exact hDa
  · exact hshape
  · exact hfuel
  · exact hfuelChar
  · exact hlowpos
  · exact hcapacity
  · exact hdegree
  · exact hagreement
  · exact hno
  · exact hA
  · exact hbandThin
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hterminalP
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hfeasibleP
  · exact hgap
  · exact hfield
  · exact hgates
  · exact hcharge

theorem exact_split
    (sound : PhaseSourceSound) (D m : ℕ)
    (hweighted : D = m * 181245)
    (hshape : D + sound.source.slopeCap ≤
      131071 * (sound.source.middleCap + 1))
    (hslopeM : sound.source.slopeCap ≤ m)
    (hmChar : m < 2130706433)
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181245 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (hgap : sound.source.gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A : Finset (RegularIndex H))
    (hroute : sound.source.Routeable (regularAggregateFlag H A))
    (hnarrowS : (regularAggregateFlag H A).all ≤ 39)
    (hnarrowY : middle (regularAggregateFlag H A) ≤ 182)
    (hnarrowT : total (regularAggregateFlag H A) ≤ 11192) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤
        ExactInitialCharge6815.cost sound.source.totalCap sound.source.middleCap sound.source.slopeCap
          (regularCumulativeFlag H F).all (middle (regularCumulativeFlag H F)) (total (regularCumulativeFlag H F)) := by
  apply charged_split sound
    (fun p => ExactInitialCharge6815.cost sound.source.totalCap sound.source.middleCap sound.source.slopeCap
      p.all (middle p) (total p)) _ D m hweighted hshape hslopeM hmChar u0 u1 H selected Gamma
    hdegree hagreement hno hgap A hroute hnarrowS hnarrowY hnarrowT
  intro p j _hr _hs _hy _ht _hj
  simpa only [PowerRoute.stageCost,PowerRoute.stagePair,Oracle.exactRouteBox,
    FactorSwitch.helperPair,ExactInitialCharge6815.cost,PhasePotential6815.pair] using
    PhasePotential6815.count_mono_right
      (sound.source.totalCap-j*total p) (sound.source.middleCap-j*middle p) (sound.source.slopeCap-j*p.all)
      sound.source.totalCap sound.source.middleCap sound.source.slopeCap p.all (middle p) (total p)
      (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)

end
end ProximityPrize.SubmissionLower.Lower80899.ActualExactPhase6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.TerminalPotentials6815
open BalancedPhasePotential6815 PhasePotential6815 RCN260 AsymmetricHelper
theorem count0 (r y t : ℕ) (hr : 1≤r) (hR : r≤39) (hY : y≤182) (hT : t≤11192) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤0*t+4690861953401*y+43345274666350*r := by
  simpa only [Nat.zero_mul,Nat.zero_add] using final_pass_count r y t hr hY hT
theorem count1 (r y t : ℕ) (hr : 1≤r) (hR : r≤28) (hY : y≤131) (hT : t≤8092) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤53657045892*t+3381036458565*y+15633886130566*r := by
  exact count_le 88902 1382 308 28 131 8092 53657045892 3381036458565 15633886130566 r y t (by decide +kernel) hr hR hY hT
theorem count2 (r y t : ℕ) (hr : 1≤r) (hR : r≤26) (hY : y≤124) (hT : t≤7692) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤50287772707*t+3174905420834*y+14829154405166*r := by
  exact count_le 88902 1382 308 26 124 7692 50287772707 3174905420834 14829154405166 r y t (by decide +kernel) hr hR hY hT
theorem count3 (r y t : ℕ) (hr : 1≤r) (hR : r≤25) (hY : y≤117) (hT : t≤7692) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤47864909186*t+3114024297937*y+14402986544890*r := by
  exact count_le 88902 1382 308 25 117 7692 47864909186 3114024297937 14402986544890 r y t (by decide +kernel) hr hR hY hT
theorem count4 (r y t : ℕ) (hr : 1≤r) (hR : r≤24) (hY : y≤114) (hT : t≤7692) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤46285733583*t+3053143175041*y+14220343176200*r := by
  exact count_le 88902 1382 308 24 114 7692 46285733583 3053143175041 14220343176200 r y t (by decide +kernel) hr hR hY hT
end ProximityPrize.SubmissionLower.TerminalPotentials6815
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.Lower80899.TenPhase
open ProximityPrize.Benchmark RCN095 RCN140 RCN156 RCN234 RCN238 RCN266 RCN319
open Lower80899.Oracle Lower80899.BatchPhase
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

def sound : ℕ → PhaseSourceSound
  | 0 => SourceSound.Phase00.sound
  | 1 => SourceSound.Phase01.sound
  | 2 => SourceSound.Phase02.sound
  | 3 => SourceSound.Phase03.sound
  | 4 => SourceSound.Phase04.sound
  | 5 => SourceSound.Phase05.sound
  | 6 => SourceSound.Phase06.sound
  | 7 => SourceSound.Phase03.sound
  | 8 => SourceSound.Phase04.sound
  | _+9 => SourceSound.PhaseFinal.sound

def kernel (u0 u1 : I → K) (j : ℕ) : PhaseKernelRealization (sound j) u0 u1 :=
  match j with
  | 0 => SourceSound.Phase00.kernel u0 u1
  | 1 => SourceSound.Phase01.kernel u0 u1
  | 2 => SourceSound.Phase02.kernel u0 u1
  | 3 => SourceSound.Phase03.kernel u0 u1
  | 4 => SourceSound.Phase04.kernel u0 u1
  | 5 => SourceSound.Phase05.kernel u0 u1
  | 6 => SourceSound.Phase06.kernel u0 u1
  | 7 => SourceSound.Phase03.kernel u0 u1
  | 8 => SourceSound.Phase04.kernel u0 u1
  | _+9 => SourceSound.PhaseFinal.kernel u0 u1

end
end ProximityPrize.SubmissionLower.Lower80899.TenPhase
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem rounded_affine_positive
    (p q L0 L1 T0 T1 L T a b c : ℤ)
    (hp : 0≤p) (hq : 0≤q) (hn : 0<p+q)
    (hT : (p+q)*T=p*T0+q*T1)
    (hlo : p*L0+q*L1≤(p+q)*L)
    (hhi : (p+q)*L≤p*L0+q*L1+(p+q))
    (h0 : max 0 (-a)<a*L0+b*T0+c)
    (h1 : max 0 (-a)<a*L1+b*T1+c) :
    0<a*L+b*T+c := by
  let e := (p+q)*L-(p*L0+q*L1)
  let d := max 0 (-a)
  have he0 : 0≤e := by dsimp [e]; omega
  have he1 : e≤p+q := by dsimp [e]; omega
  have h0' : d+1≤a*L0+b*T0+c := by dsimp [d]; omega
  have h1' : d+1≤a*L1+b*T1+c := by dsimp [d]; omega
  have hsum := add_le_add (mul_le_mul_of_nonneg_left h0' hp) (mul_le_mul_of_nonneg_left h1' hq)
  have hround : -(p+q)*d≤a*e := by
    by_cases ha : 0≤a
    · have hd : d=0 := by dsimp [d]; omega
      rw [hd,mul_zero]
      exact mul_nonneg ha he0
    · have hd : d= -a := by dsimp [d]; omega
      have hh := mul_le_mul_of_nonpos_left he1 (show a≤0 by omega)
      rw [hd]
      nlinarith only [hh]
  have hidentity : (p+q)*(a*L+b*T+c)=
      p*(a*L0+b*T0+c)+q*(a*L1+b*T1+c)+a*e := by
    dsimp [e]
    have hh := congrArg (fun x : ℤ => b*x) hT
    nlinarith only [hh]
  have hpositive : 0<(p+q)*(a*L+b*T+c) := by
    nlinarith only [hsum,hround,hidentity,hn]
  exact pos_of_mul_pos_right hpositive (le_of_lt hn)

def ceilBlend (T0 T1 L0 L1 T : ℕ) : ℕ :=
  ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1)/(T1-T0)

theorem ceilBlend_bounds (T0 T1 L0 L1 T : ℕ)
    (h01 : T0<T1) (h0 : T0≤T) (h1 : T≤T1) :
    (T1-T)*L0+(T-T0)*L1≤(T1-T0)*ceilBlend T0 T1 L0 L1 T ∧
    (T1-T0)*ceilBlend T0 T1 L0 L1 T <
      (T1-T)*L0+(T-T0)*L1+(T1-T0) := by
  have hn : 0<T1-T0 := by omega
  have hq := Nat.div_add_mod ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1) (T1-T0)
  have hm := Nat.mod_lt ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1) hn
  unfold ceilBlend
  omega

theorem total_blend_identity (T0 T1 T : ℕ) (h0 : T0≤T) (h1 : T≤T1) :
    (T1-T0)*T=(T1-T)*T0+(T-T0)*T1 := by
  have h01 : T0≤T1 := by omega
  have ha := Nat.sub_add_cancel h0
  have hb := Nat.sub_add_cancel h1
  have hc := Nat.sub_add_cancel h01
  nlinarith

theorem ceilBlend_affine_lower (T0 T1 L0 L1 T k : ℕ)
    (h01 : T0<T1) (h0 : T0≤T) (h1 : T≤T1)
    (hL0 : T0+k≤L0) (hL1 : T1+k≤L1) :
    T+k≤ceilBlend T0 T1 L0 L1 T := by
  have hn : 0<T1-T0 := by omega
  have hsum : (T1-T)+(T-T0)=T1-T0 := by omega
  have hT := total_blend_identity T0 T1 T h0 h1
  have hL := (ceilBlend_bounds T0 T1 L0 L1 T h01 h0 h1).1
  have hscale := Nat.add_le_add (Nat.mul_le_mul_left (T1-T) hL0) (Nat.mul_le_mul_left (T-T0) hL1)
  have hk := congrArg (fun n : ℕ => n*k) hsum
  have hp : (T1-T0)*(T+k)≤(T1-T0)*ceilBlend T0 T1 L0 L1 T := by
    nlinarith only [hT,hL,hscale,hk]
  exact Nat.le_of_mul_le_mul_left hp hn

theorem ceilBlend_const_lower (T0 T1 L0 L1 T k : ℕ)
    (h01 : T0<T1) (h0 : T0≤T) (h1 : T≤T1) (hL0 : k≤L0) (hL1 : k≤L1) :
    k≤ceilBlend T0 T1 L0 L1 T := by
  have hn : 0<T1-T0 := by omega
  have hsum : (T1-T)+(T-T0)=T1-T0 := by omega
  have hL := (ceilBlend_bounds T0 T1 L0 L1 T h01 h0 h1).1
  have hscale := Nat.add_le_add (Nat.mul_le_mul_left (T1-T) hL0) (Nat.mul_le_mul_left (T-T0) hL1)
  have hp : (T1-T0)*k≤(T1-T0)*ceilBlend T0 T1 L0 L1 T := by
    nlinarith only [hL,hscale,congrArg (fun n : ℕ => n*k) hsum]
  exact Nat.le_of_mul_le_mul_left hp hn

theorem ceilBlend_upper (T0 T1 L0 L1 T : ℕ)
    (h01 : T0<T1) (h0 : T0≤T) (h1 : T≤T1) :
    ceilBlend T0 T1 L0 L1 T≤max L0 L1 := by
  have hn : 0<T1-T0 := by omega
  have hsum : (T1-T)+(T-T0)=T1-T0 := by omega
  have hL := (ceilBlend_bounds T0 T1 L0 L1 T h01 h0 h1).2
  have hscale := Nat.add_le_add (Nat.mul_le_mul_left (T1-T) (le_max_left L0 L1))
    (Nat.mul_le_mul_left (T-T0) (le_max_right L0 L1))
  have hp : (T1-T0)*ceilBlend T0 T1 L0 L1 T<(T1-T0)*(max L0 L1+1) := by
    nlinarith only [hL,hscale,congrArg (fun n : ℕ => n*max L0 L1) hsum]
  have hh := Nat.lt_of_mul_lt_mul_left hp
  omega

end ProximityPrize.SubmissionLower.RelativeCertificate6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open scoped BigOperators
open RCN100 LocatorFastKernelArithmetic
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 20000

theorem coefficientCount_split_slope (D w L s h : ℕ)
    (hh : 0<h) (hs : h≤s) (hL : h≤L) :
    coefficientCount D w L s=
      coefficientCount D w L (h-1)+coefficientCount (D-(w-1)*h) w (L-h) (s-h) := by
  have hc (D L s : ℕ) : coefficientCount D w L s=
      ∑ j∈Finset.range (s+1), ∑ i∈Finset.range (L+1), (L+1-i-j)*(D-w*i-(w-1)*j) := by
    unfold coefficientCount
    exact Finset.sum_comm
  rw [hc D L s,hc D L (h-1),hc (D-(w-1)*h) (L-h) (s-h)]
  have he : s+1=h+(s-h+1) := by omega
  conv_lhs => rw [he,Finset.sum_range_add]
  rw [show h-1+1=h by omega]
  apply congrArg₂ (fun a b : ℕ => a+b)
  · rfl
  · apply Finset.sum_congr rfl
    intro j hj
    have htrim :
        (∑ i∈Finset.range (L-h+1), (L+1-i-(h+j))*(D-w*i-(w-1)*(h+j)))=
        ∑ i∈Finset.range (L+1), (L+1-i-(h+j))*(D-w*i-(w-1)*(h+j)) := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i hi hn
      have hi' := Finset.mem_range.mp hi
      have hn' : L-h+1 ≤ i := by simpa using hn
      have hz : L+1-i-(h+j)=0 := by omega
      simp only [hz,zero_mul]
    rw [←htrim]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    · omega
    · rw [Nat.mul_add]
      omega

def twoResidueCoefficientCount (q r w L s : ℕ) : ℕ :=
  if r+s≤w then oneResidueCoefficientCount q r w L s else
    oneResidueCoefficientCount q r w L (w-r-1)+
    oneResidueCoefficientCount (q+1-(w-r)) 0 w (L-(w-r)) (s-(w-r))

theorem coefficientCount_eq_twoResidue (q r w L s : ℕ)
    (hw : 2≤w) (hr : r<w) (hs : s<w) (hsq : s≤q) (hL : q+1≤L) :
    coefficientCount (q*w+r) w L s=twoResidueCoefficientCount q r w L s := by
  unfold twoResidueCoefficientCount
  split_ifs with hfirst
  · exact coefficientCount_eq_oneResidueCoefficientCount q r w L s hw hsq (by omega) hfirst
  · have hh : 0<w-r := by omega
    have hhs : w-r≤s := by omega
    have hhq : w-r≤q := by omega
    have hprod : (w-1)*(w-r)≤q*w+r := by
      have h := Nat.mul_le_mul (show w-1≤w by omega) hhq
      nlinarith
    have hcut : q*w+r-(w-1)*(w-r)=(q+1-(w-r))*w := by
      have h1 := Nat.sub_add_cancel hprod
      have h2 := Nat.sub_add_cancel (show w-r≤q+1 by omega)
      have h3 := Nat.sub_add_cancel (show r≤w by omega)
      have h4 : w-1+1=w := by omega
      nlinarith
    rw [coefficientCount_split_slope (q*w+r) w L s (w-r) hh hhs (by omega),hcut]
    rw [coefficientCount_eq_oneResidueCoefficientCount q r w L (w-r-1) hw (by omega) (by omega) (by omega)]
    simpa only [Nat.add_zero] using congrArg
      (fun x => oneResidueCoefficientCount q r w L (w-r-1)+x)
      (coefficientCount_eq_oneResidueCoefficientCount (q+1-(w-r)) 0 w (L-(w-r)) (s-(w-r))
        hw (by omega) (by omega) (by omega))

end ProximityPrize.SubmissionLower.RelativeCertificate6814
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open LocatorFastKernelArithmetic RCN100
set_option autoImplicit false
set_option maxHeartbeats 700000

def oneSlope (q r w s : ℕ) : ℕ :=
  (r+q)*(smallChoose (q+2) 2-smallChoose (q+1-s) 2)+
    (w-2)*(smallChoose (q+2) 3-smallChoose (q+1-s) 3)

def oneIntercept (q r w s : ℕ) : ℤ :=
  (oneResidueCoefficientCount q r w q s : ℤ)-(oneSlope q r w s : ℤ)*q

theorem oneResidue_affine_nat (q r w L s : ℕ) (hL : q≤L) :
    oneResidueCoefficientCount q r w L s+oneSlope q r w s*q=
      oneResidueCoefficientCount q r w q s+oneSlope q r w s*L := by
  have hU := Nat.sub_add_cancel (show q≤L+1 by omega)
  have hh := congrArg (fun x : ℕ => oneSlope q r w s*x) hU
  unfold oneResidueCoefficientCount oneSlope at *
  simp only [show q+1-q=1 by omega,one_mul] at *
  nlinarith only [hh]

theorem oneResidue_affine (q r w L s : ℕ) (hL : q≤L) :
    (oneResidueCoefficientCount q r w L s : ℤ)=
      (oneSlope q r w s : ℤ)*L+oneIntercept q r w s := by
  have hh : (oneResidueCoefficientCount q r w L s : ℤ)+(oneSlope q r w s : ℤ)*q=
      (oneResidueCoefficientCount q r w q s : ℤ)+(oneSlope q r w s : ℤ)*L := by
    exact_mod_cast oneResidue_affine_nat q r w L s hL
  unfold oneIntercept
  omega

def coefficientSlope (q r w s : ℕ) : ℕ :=
  if r+s≤w then oneSlope q r w s else
    oneSlope q r w (w-r-1)+oneSlope (q+1-(w-r)) 0 w (s-(w-r))

def coefficientIntercept (q r w s : ℕ) : ℤ :=
  if r+s≤w then oneIntercept q r w s else
    oneIntercept q r w (w-r-1)+oneIntercept (q+1-(w-r)) 0 w (s-(w-r))-
      (oneSlope (q+1-(w-r)) 0 w (s-(w-r)) : ℤ)*(w-r)

theorem coefficientCount_affine (q r w L s : ℕ)
    (hw : 2≤w) (hr : r<w) (hs : s<w) (hsq : s≤q) (hL : q+1≤L) :
    (coefficientCount (q*w+r) w L s : ℤ)=
      (coefficientSlope q r w s : ℤ)*L+coefficientIntercept q r w s := by
  rw [coefficientCount_eq_twoResidue q r w L s hw hr hs hsq hL]
  unfold twoResidueCoefficientCount coefficientSlope coefficientIntercept
  split_ifs with hfirst
  · exact oneResidue_affine q r w L s (by omega)
  · rw [Nat.cast_add,oneResidue_affine q r w L (w-r-1) (by omega),
      oneResidue_affine (q+1-(w-r)) 0 w (L-(w-r)) (s-(w-r)) (by omega),
      Nat.cast_sub (show w-r≤L by omega),Nat.cast_sub (show r≤w by omega),Nat.cast_add]
    ring

end ProximityPrize.SubmissionLower.RelativeCertificate6814
end MergedPart8
