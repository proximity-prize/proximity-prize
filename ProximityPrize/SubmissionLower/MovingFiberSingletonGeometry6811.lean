import ProximityPrize.SubmissionLower.MovingFiberCarrier6811
import ProximityPrize.SubmissionLower.MovingFiberSingleCore6811
import ProximityPrize.SubmissionLower.MovingFiberPhaseCore6811
import ProximityPrize.SubmissionLower.AffineFactorAggregate6808

namespace ProximityPrize.SubmissionLower.MovingFiberSingletonGeometry6811
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open LocatorFactorAggregate LocatorPhase6800Oracle LocatorBatchPhase6800
open Lower80860.Oracle Lower80860.BatchPhase
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

theorem source_count
    (sound : Lower80860.Oracle.PhaseSourceSound) (u0 u1 : I → K)
    (kernel : PhaseKernelRealization sound u0 u1)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181275 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80869)
    (F : RegularIndex H)
    (hR : (regularCumulativeFlag H F).all ≤ 35)
    (hY : middle (regularCumulativeFlag H F) ≤ 163)
    (hT : total (regularCumulativeFlag H F) ≤ 9678)
    (hroute : sound.source.Routeable (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤ sound.potential.eval (regularCumulativeFlag H F) := by
  have he : regularAggregateFlag H ({F} : Finset (RegularIndex H)) = regularCumulativeFlag H F := by
    simp [regularAggregateFlag,sumFlag]
  have hs := routeable_exists_strict_helper_split sound kernel.D kernel.m kernel.weighted
    kernel.shape kernel.slope_le_m kernel.m_lt_char u0 u1 H selected Gamma
    hdegree hagreement hno kernel.gap_le_finrank {F}
    (by rw [he]; exact hroute) (by rw [he]; exact hR)
    (by rw [he]; exact hY) (by rw [he]; exact hT)
  exact AffineFactorAggregate6808.singleton_helper F
    (fun f => (regularSeeds H selected Gamma f).card)
    (fun f => sound.potential.eval (regularCumulativeFlag H f)) hs

theorem raw_count
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181275 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80869)
    (F : RegularIndex Q)
    (hr : (regularCumulativeFlag Q F).all ≤ 32)
    (hy : middle (regularCumulativeFlag Q F) ≤ 149)
    (ht : total (regularCumulativeFlag Q F) ≤ 8121)
    (hsafe : BoundaryTailGates6808.Safe (regularCumulativeFlag Q F).all
      (middle (regularCumulativeFlag Q F))) :
    (regularSeeds Q selected Gamma F).card ≤
      MovingFiberOrdinary6811.rawCost (regularCumulativeFlag Q F) := by
  have hF := directFactor_data Q F.1 hQ D 131071 P.total P.s hbox F.2
  let p := originalCumulativeFlag F.1
  let Pown := RCN198.support (MovingFiberOrdinary6811.padA p)
    (MovingFiberOrdinary6811.padB p) (MovingFiberOrdinary6811.padSlope p)
  have hcaps := MovingFiberOrdinary6811.own_parameter_caps p hr hy ht
  have hb := MovingFiberOrdinary6811.own_box F.1 D 131071 P.total P.s hF.2.2
  let Fself := LocatorCoprimeQuotient.regularIndexSelf Q F
  have hs : BoundaryTailGates6808.Safe (regularCumulativeFlag F.1 Fself).all
      (middle (regularCumulativeFlag F.1 Fself)) := by
    simpa only [regularCumulativeFlag,Fself,LocatorCoprimeQuotient.regularIndexSelf_val] using hsafe
  have hc := MovingFiberOrdinary6811.regular_factor_count_raw D Pown hDlow hDchar
    hcaps.1 hcaps.2.1 hcaps.2.2 F.1 hF.1.ne_zero hb
    (MovingFiberOrdinary6811.own_support F.1) selected Gamma u0 u1
    hdegree hagreement hno Fself hs
  simpa only [RCN140.regularSeeds,regularCumulativeFlag,Fself,
    LocatorCoprimeQuotient.regularIndexSelf_val] using hc

theorem root_count_group (g : Fin 20)
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181275 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80869)
    (F : RegularIndex Q)
    (hr : (regularCumulativeFlag Q F).all ≤ 31)
    (hy : middle (regularCumulativeFlag Q F) ≤ 142)
    (ht : total (regularCumulativeFlag Q F) ≤ 7501)
    (ha : MovingFiberCarrier6811.Active g (regularCumulativeFlag Q F)) :
    (regularSeeds Q selected Gamma F).card ≤
      MovingFiberCarrier6811.ledgerCap g (regularCumulativeFlag Q F) := by
  have hF := directFactor_data Q F.1 hQ D 131071 P.total P.s hbox F.2
  have hsub := regularSeeds_subset Q selected Gamma F
  have hcum := originalCumulativeFlag_cumulative F.1
  have hsmallT : wt residualTotalWeights F.1 ≤ 7501 := by
    simpa only [regularCumulativeFlag,total,hcum.2.2] using ht
  have hsmallY : wt residualYSWeights F.1 ≤ 142 := by
    simpa only [regularCumulativeFlag,middle,hcum.2.1] using hy
  have hcount := MovingFiberCarrier6811.carrier_count_le_ledger g
    (nodes := IRSProfile.domain) (u0 := u0) (u1 := u1)
    D P.total P.s F.1 hDlow hDchar hF.1 hF.2.1 hF.2.2 hsmallT hsmallY hr
    selected (regularSeeds Q selected Gamma F)
    (fun g hg => hdegree g (hsub hg)) (fun g hg => hagreement g (hsub hg))
    (fun g hg => (Finset.mem_filter.mp hg).2.1)
    (fun g hg => (Finset.mem_filter.mp hg).2.2)
    (noLargeSelectedPencil_mono selected Gamma _ 131071 80869 hsub hno)
    (by norm_num [I,IRSProfile.Index]) ha
  exact hcount

theorem root_count
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0) (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181275 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80869) (F : RegularIndex Q)
    (th : Array ℕ) (w : ℕ) (hw : 1≤w) (hw16 : w≤20)
    (ha : MovingFiberSingleCore6811.Active th w (regularCumulativeFlag Q F).all
      (regularCumulativeFlag Q F).yz (regularCumulativeFlag Q F).zOnly
      (regularCumulativeFlag Q F).zOnly) :
    (regularSeeds Q selected Gamma F).card ≤ MovingFiberSingleCore6811.rootUpper w
      (regularCumulativeFlag Q F).all (regularCumulativeFlag Q F).yz (regularCumulativeFlag Q F).zOnly := by
  have h := ha
  simp only [MovingFiberSingleCore6811.Active,if_neg (show w≠0 by omega),if_pos hw16] at h
  rcases h with ⟨hr3,hr31,hv2,hz3,hL,hy,ht⟩
  have hc := root_count_group (MovingFiberSingleCore6811.rootIndex w) D P hDlow hDchar Q hQ hbox
    selected Gamma u0 u1 hdegree hagreement hno F hr31
    (by simpa only [middle,Nat.add_comm] using hy)
    (by simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht)
    ⟨hr3,hv2,hz3,hL⟩
  simpa only [MovingFiberCarrier6811.ledgerCap,MovingFiberCount6811.roundedCaps,
    MovingFiberCount6811.Receipt.rounded_formula,MovingFiberSingleCore6811.rootUpper,
    MovingFiberSingleCore6811.rootSlope,MovingFiberSingleCore6811.rootIntercept] using hc

theorem source_total (j : ℕ) (hj : j<7) : 9678 ≤ (Lower80860.TenPhase.sound j).source.totalCap := by
  interval_cases j <;> decide +kernel

theorem factor_count_of_cover
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0) (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181275 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80869)
    (F : RegularIndex Q) (hr : (regularCumulativeFlag Q F).all≤35)
    (hy : middle (regularCumulativeFlag Q F)≤163) (ht : total (regularCumulativeFlag Q F)≤9678)
    (c : MovingFiberSingleCore6811.Carrier) (slope intercept : ℕ) (th : Array ℕ)
    (runs : List MovingFiberSingleCore6811.Run)
    (hc : c.Correct (regularCumulativeFlag Q F).all (regularCumulativeFlag Q F).yz)
    (hcover : MovingFiberSingleCore6811.Cover c slope intercept
      (regularCumulativeFlag Q F).all (regularCumulativeFlag Q F).yz th
      (9679-((regularCumulativeFlag Q F).all+(regularCumulativeFlag Q F).yz)) 0 runs)
    (hthreshold : ∀ j, j<7 → Lower80860.ThresholdFast.FastSourceThresholdSufficient
      (Lower80860.TenPhase.sound j).source (regularCumulativeFlag Q F).all
      (regularCumulativeFlag Q F).yz (MovingFiberSingleCore6811.thresholdAt th j)) :
    (regularSeeds Q selected Gamma F).card ≤
      MovingFiberSingleCore6811.cap slope intercept (regularCumulativeFlag Q F).zOnly := by
  let p := regularCumulativeFlag Q F
  have hr1 : 1≤p.all := regularCumulativeFlag_positive Q F
  have ht' : p.all+p.yz+p.zOnly≤9678 := by
    simpa only [p,total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
  obtain ⟨who,hactive,hbound⟩ := MovingFiberSingleCore6811.cover_sound c slope intercept p.all p.yz th
    (9679-(p.all+p.yz)) 0 runs hcover p.zOnly (Nat.zero_le _) (by omega)
  apply le_trans (b := MovingFiberSingleCore6811.choice c who p.all p.yz p.zOnly) ?_ hbound
  by_cases h0 : who=0
  · subst who
    simp only [MovingFiberSingleCore6811.choice,if_pos,MovingFiberSingleCore6811.Active] at hactive ⊢
    rw [MovingFiberSingleCore6811.Carrier.eval_correct c _ _ _ hr1 hc]
    have hh := raw_count D P hDlow hDchar Q hQ hbox selected Gamma u0 u1 hdegree hagreement hno F
      hactive.1 (by simpa only [middle,Nat.add_comm] using hactive.2.1)
      (by simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hactive.2.2.1)
      (by simpa only [middle,Nat.add_comm] using hactive.2.2.2)
    exact hh
  by_cases h16 : who≤20
  · simp only [MovingFiberSingleCore6811.choice,if_neg h0,if_pos h16]
    exact root_count D P hDlow hDchar Q hQ hbox selected Gamma u0 u1 hdegree hagreement hno F th who
      (by omega) h16 hactive
  · have ha : who-21<7 ∧ MovingFiberSingleCore6811.thresholdAt th (who-21)≤p.zOnly := by
      simpa only [MovingFiberSingleCore6811.Active,if_neg h0,if_neg h16] using hactive
    have hroute := Lower80860.ThresholdFast.sufficient_route (Lower80860.TenPhase.sound (who-21)).source
      p.all p.yz (MovingFiberSingleCore6811.thresholdAt th (who-21)) p.zOnly
      (source_total _ ha.1) ht' ha.2 (hthreshold _ ha.1)
    have hh := source_count (Lower80860.TenPhase.sound (who-21)) u0 u1
      (Lower80860.TenPhase.kernel u0 u1 (who-21)) Q selected Gamma hdegree hagreement hno F hr hy ht hroute
    simpa only [MovingFiberSingleCore6811.choice,if_neg h0,if_neg h16,
      MovingFiberSingleCore6811.phasePotential,rawFlag,p] using hh

#print axioms factor_count_of_cover
end
end ProximityPrize.SubmissionLower.MovingFiberSingletonGeometry6811
