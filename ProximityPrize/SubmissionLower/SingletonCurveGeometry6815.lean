import ProximityPrize.SubmissionLower.SingletonCurveChecks6815
import ProximityPrize.SubmissionLower.MovingFiberCarrier6815
import ProximityPrize.SubmissionLower.MovingFiberSingleCore6815
import ProximityPrize.SubmissionLower.MovingFiberPhaseCore6815
import ProximityPrize.SubmissionLower.AffineFactorAggregate6808
namespace ProximityPrize.SubmissionLower.SingletonCurveGeometry6815
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open LocatorFactorAggregate LocatorPhase6800Oracle LocatorBatchPhase6800
open Lower80899.Oracle Lower80899.BatchPhase
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

open MovingFiberSingletonGeometry6815
theorem count_of_choice
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0) (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181245 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (F : RegularIndex Q) (hr : (regularCumulativeFlag Q F).all≤39)
    (hy : middle (regularCumulativeFlag Q F)≤182) (ht : total (regularCumulativeFlag Q F)≤11192)
    (c : MovingFiberSingleCore6815.Carrier) (th : Array ℕ) (who : ℕ)
    (hc : c.Correct (regularCumulativeFlag Q F).all (regularCumulativeFlag Q F).yz)
    (hactive : MovingFiberSingleCore6815.Active th who (regularCumulativeFlag Q F).all
      (regularCumulativeFlag Q F).yz (regularCumulativeFlag Q F).zOnly (regularCumulativeFlag Q F).zOnly)
    (hthreshold : ∀ j, j<7 → Lower80899.ThresholdFast.FastSourceThresholdSufficient
      (Lower80899.TenPhase.sound j).source (regularCumulativeFlag Q F).all
      (regularCumulativeFlag Q F).yz (MovingFiberSingleCore6815.thresholdAt th j)) :
    (regularSeeds Q selected Gamma F).card≤MovingFiberSingleCore6815.choice c who
      (regularCumulativeFlag Q F).all (regularCumulativeFlag Q F).yz (regularCumulativeFlag Q F).zOnly := by
  let p := regularCumulativeFlag Q F
  have hr1 : 1≤p.all := regularCumulativeFlag_positive Q F
  have ht' : p.all+p.yz+p.zOnly≤11192 := by
    simpa only [p,total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
  by_cases hn : 32≤who
  · have ha : who≤252 ∧
        CertifiedRegularChoice6815.Active (MovingFiberSingleCore6815.extraChoice who) p.all p.yz p.zOnly ∧
        CertifiedRegularChoice6815.Active (MovingFiberSingleCore6815.extraChoice who) p.all p.yz p.zOnly := by
      simpa only [MovingFiberSingleCore6815.Active,if_pos hn] using hactive
    have hF := directFactor_data Q F.val hQ D 131071 P.total P.s hbox F.property
    have hh := CertifiedRegularChoice6815.count IRSProfile.domain u0 u1
      (by norm_num [IRSProfile.Index]) selected Gamma ⟨hdegree,hagreement,hno⟩
      F hDlow hDchar hF.2.2 (MovingFiberSingleCore6815.extraChoice who) ha.2.1
    simpa only [MovingFiberSingleCore6815.choice,if_pos hn] using hh
  by_cases h0 : who=0
  · subst who
    simp only [MovingFiberSingleCore6815.choice,MovingFiberSingleCore6815.Active,if_neg hn,if_pos] at hactive ⊢
    rw [MovingFiberSingleCore6815.Carrier.eval_correct c _ _ _ hr1 hc]
    have hh := raw_count D P hDlow hDchar Q hQ hbox selected Gamma u0 u1 hdegree hagreement hno F
      hactive.1 (by simpa only [middle,Nat.add_comm] using hactive.2.1)
      (by simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hactive.2.2.1)
      (by simpa only [middle,Nat.add_comm] using hactive.2.2.2)
    exact hh
  by_cases h16 : who≤21
  · simp only [MovingFiberSingleCore6815.choice,if_neg hn,if_neg h0,if_pos h16]
    exact root_count D P hDlow hDchar Q hQ hbox selected Gamma u0 u1 hdegree hagreement hno F th who
      (by omega) h16 hactive
  · have ha : who-22<7 ∧ MovingFiberSingleCore6815.thresholdAt th (who-22)≤p.zOnly := by
      simpa only [MovingFiberSingleCore6815.Active,if_neg hn,if_neg h0,if_neg h16] using hactive
    have hroute := Lower80899.ThresholdFast.sufficient_route (Lower80899.TenPhase.sound (who-22)).source
      p.all p.yz (MovingFiberSingleCore6815.thresholdAt th (who-22)) p.zOnly
      (source_total _ ha.1) ht' ha.2 (hthreshold _ ha.1)
    have hh := source_count (Lower80899.TenPhase.sound (who-22)) u0 u1
      (Lower80899.TenPhase.kernel u0 u1 (who-22)) Q selected Gamma hdegree hagreement hno F hr hy ht hroute
    simpa only [MovingFiberSingleCore6815.choice,if_neg hn,if_neg h0,if_neg h16,
      MovingFiberSingleCore6815.phasePotential,rawFlag,p] using hh

theorem count_of_curve
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0) (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181245 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (F : RegularIndex Q) (hr : (regularCumulativeFlag Q F).all≤39)
    (hy : middle (regularCumulativeFlag Q F)≤182) (ht : total (regularCumulativeFlag Q F)≤11192)
    (th : Array ℕ) (curve runs : List FinalCurves6815.Piece)
    (hcheck : SingletonCurveChecks6815.check (regularCumulativeFlag Q F).all
      (regularCumulativeFlag Q F).yz th curve runs=true)
    (hthreshold : ∀ j, j<7 → Lower80899.ThresholdFast.FastSourceThresholdSufficient
      (Lower80899.TenPhase.sound j).source (regularCumulativeFlag Q F).all
      (regularCumulativeFlag Q F).yz (MovingFiberSingleCore6815.thresholdAt th j)) :
    (regularSeeds Q selected Gamma F).card≤FinalCurves6815.eval curve (regularCumulativeFlag Q F).zOnly := by
  let p := regularCumulativeFlag Q F
  have hz : p.zOnly<11193-p.all-p.yz := by
    have h : p.all+p.yz+p.zOnly≤11192 := by
      simpa only [p,total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
    omega
  obtain ⟨who,ha,hb⟩ := SingletonCurveChecks6815.check_sound p.all p.yz th curve runs hcheck p.zOnly hz
  exact (count_of_choice D P hDlow hDchar Q hQ hbox selected Gamma u0 u1 hdegree hagreement hno
    F hr hy ht (SingletonCurveChecks6815.carrier p.all p.yz) th who
    (SingletonCurveChecks6815.carrier_correct _ _) ha hthreshold).trans hb

end
end ProximityPrize.SubmissionLower.SingletonCurveGeometry6815
