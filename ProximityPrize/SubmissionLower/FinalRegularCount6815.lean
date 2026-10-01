import ProximityPrize.SubmissionLower.FinalFamilyAlgebra6815
import ProximityPrize.SubmissionLower.SingletonCount6815
namespace ProximityPrize.SubmissionLower.FinalRegularCount6815
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266
open LocatorFactorAggregate LocatorPhase6800Oracle LocatorBatchPhase6800
open Lower80899.Oracle Lower80899.BatchPhase FinalPayment6815 FinalPrefixSound6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem count_of_rules
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072≤D) (hDchar : D<2130706433)
    (Q : P4) (hQ : Q≠0) (hbox : Q∈globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g∈Gamma, (selected g).natDegree≤131071)
    (hagreement : ∀ g∈Gamma, 181245≤((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (A : Finset (RegularIndex Q))
    (hR : (regularAggregateFlag Q A).all≤39) (hy : middle (regularAggregateFlag Q A)≤182)
    (ht : total (regularAggregateFlag Q A)≤11192)
    (rules : ∀ capR capV capZ, 1≤capR → capR≤39 → capR+capV≤182 → capR+capV+capZ≤11192 →
      FinalRuleCheck6815.RuleBound capR capV capZ (FinalLedgerData6815.cap capR capV capZ)) :
    (∑ F∈A,(regularSeeds Q selected Gamma F).card)≤FinalLedgerData6815.cap
      (regularAggregateFlag Q A).all (regularAggregateFlag Q A).yz (regularAggregateFlag Q A).zOnly := by
  let rr := fun F : RegularIndex Q => (regularCumulativeFlag Q F).all
  let vv := fun F : RegularIndex Q => (regularCumulativeFlag Q F).yz
  let zz := fun F : RegularIndex Q => (regularCumulativeFlag Q F).zOnly
  let cnt := fun F : RegularIndex Q => (regularSeeds Q selected Gamma F).card
  have hY' : (∑ F∈A,rr F)+(∑ F∈A,vv F)≤182 := by
    simpa only [regularAggregateFlag,sumFlag,middle,rr,vv,Nat.add_comm] using hy
  have hT' : (∑ F∈A,rr F)+(∑ F∈A,vv F)+(∑ F∈A,zz F)≤11192 := by
    simpa only [regularAggregateFlag,sumFlag,total,rr,vv,zz,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
  apply FinalFamilyAlgebra6815.family_count A rr vv zz cnt
    (fun F _ => regularCumulativeFlag_positive Q F) hR hY' hT' ?_ ?_ rules
  · intro F hFA
    have hm := regularAggregateFlag_mono Q (Finset.singleton_subset_iff.mpr hFA)
    simp only [regularAggregateFlag,sumFlag,Finset.sum_singleton] at hm
    exact SingletonCount6815.count D P hDlow hDchar Q hQ hbox selected Gamma u0 u1
      hdegree hagreement hno F (hm.1.trans hR) (hm.2.1.trans hy) (hm.2.2.trans ht)
  · intro j s hs hpos hcut
    let p := regularAggregateFlag Q s
    have hm := regularAggregateFlag_mono Q hs
    have hRs : p.all≤39 := hm.1.trans hR
    have hYs : middle p≤182 := hm.2.1.trans hy
    have hTs : total p≤11192 := hm.2.2.trans ht
    have hY : p.all+p.yz≤182 := by simpa only [middle,Nat.add_comm] using hYs
    have hT : p.all+p.yz+p.zOnly≤11192 := by simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hTs
    have hpos' : 1≤p.all := hpos
    have hthreshold := SingletonCertificate6815.check_thresholds p.all p.yz _
      (SingletonData6815.checked p.all p.yz hpos' hRs hY) j.val j.isLt
    have hroute := Lower80899.ThresholdFast.sufficient_route (src j.val) p.all p.yz (cut p.all p.yz j.val) p.zOnly
      (MovingFiberSingletonGeometry6815.source_total j.val j.isLt) hT hcut hthreshold
    have heta : rawFlag p.all p.yz p.zOnly=p := by cases p; rfl
    rw [heta] at hroute
    let kernel := Lower80899.TenPhase.kernel u0 u1 j.val
    obtain ⟨U,hU,hcharged⟩ := Lower80899.ActualExactPhase6815.exact_split (Lower80899.TenPhase.sound j.val)
      kernel.D kernel.m kernel.weighted kernel.shape kernel.slope_le_m kernel.m_lt_char
      u0 u1 Q selected Gamma hdegree hagreement hno kernel.gap_le_finrank s hroute hRs hYs hTs
    refine ⟨U,hU,?_⟩
    intro F hF
    simpa only [cost,src,rr,vv,zz,middle,total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hcharged F hF

end
end ProximityPrize.SubmissionLower.FinalRegularCount6815
