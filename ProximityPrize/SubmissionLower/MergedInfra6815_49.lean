import ProximityPrize.SubmissionLower.MergedInfra6815_28
import ProximityPrize.SubmissionLower.MergedInfra6815_48
import ProximityPrize.SubmissionLower.MergedInfra6815_13
import ProximityPrize.SubmissionLower.MergedInfra6815_0
import ProximityPrize.SubmissionLower.MergedInfra6815_3
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingFiberSingletonGeometry6815
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

theorem source_count
    (sound : Lower80899.Oracle.PhaseSourceSound) (u0 u1 : I → K)
    (kernel : PhaseKernelRealization sound u0 u1)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181245 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (F : RegularIndex H)
    (hR : (regularCumulativeFlag H F).all ≤ 39)
    (hY : middle (regularCumulativeFlag H F) ≤ 182)
    (hT : total (regularCumulativeFlag H F) ≤ 11192)
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
    (hagreement : ∀ g ∈ Gamma, 181245 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (F : RegularIndex Q)
    (hr : (regularCumulativeFlag Q F).all ≤ 32)
    (hy : middle (regularCumulativeFlag Q F) ≤ 149)
    (ht : total (regularCumulativeFlag Q F) ≤ 8121)
    (hsafe : BoundaryTailGates6808.Safe (regularCumulativeFlag Q F).all
      (middle (regularCumulativeFlag Q F))) :
    (regularSeeds Q selected Gamma F).card ≤
      MovingFiberOrdinary6815.rawCost (regularCumulativeFlag Q F) := by
  have hF := directFactor_data Q F.1 hQ D 131071 P.total P.s hbox F.2
  let p := originalCumulativeFlag F.1
  let Pown := RCN198.support (MovingFiberOrdinary6815.padA p)
    (MovingFiberOrdinary6815.padB p) (MovingFiberOrdinary6815.padSlope p)
  have hcaps := MovingFiberOrdinary6815.own_parameter_caps p hr hy ht
  have hb := MovingFiberOrdinary6815.own_box F.1 D 131071 P.total P.s hF.2.2
  let Fself := LocatorCoprimeQuotient.regularIndexSelf Q F
  have hs : BoundaryTailGates6808.Safe (regularCumulativeFlag F.1 Fself).all
      (middle (regularCumulativeFlag F.1 Fself)) := by
    simpa only [regularCumulativeFlag,Fself,LocatorCoprimeQuotient.regularIndexSelf_val] using hsafe
  have hc := MovingFiberOrdinary6815.regular_factor_count_raw D Pown hDlow hDchar
    hcaps.1 hcaps.2.1 hcaps.2.2 F.1 hF.1.ne_zero hb
    (MovingFiberOrdinary6815.own_support F.1) selected Gamma u0 u1
    hdegree hagreement hno Fself hs
  simpa only [RCN140.regularSeeds,regularCumulativeFlag,Fself,
    LocatorCoprimeQuotient.regularIndexSelf_val] using hc

theorem root_count_group (g : Fin 21)
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181245 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (F : RegularIndex Q)
    (hr : (regularCumulativeFlag Q F).all ≤ 31)
    (hy : middle (regularCumulativeFlag Q F) ≤ 142)
    (ht : total (regularCumulativeFlag Q F) ≤ 7501)
    (ha : MovingFiberCarrier6815.Active g (regularCumulativeFlag Q F)) :
    (regularSeeds Q selected Gamma F).card ≤
      MovingFiberCarrier6815.ledgerCap g (regularCumulativeFlag Q F) := by
  have hF := directFactor_data Q F.1 hQ D 131071 P.total P.s hbox F.2
  have hsub := regularSeeds_subset Q selected Gamma F
  have hcum := originalCumulativeFlag_cumulative F.1
  have hsmallT : wt residualTotalWeights F.1 ≤ 7501 := by
    simpa only [regularCumulativeFlag,total,hcum.2.2] using ht
  have hsmallY : wt residualYSWeights F.1 ≤ 142 := by
    simpa only [regularCumulativeFlag,middle,hcum.2.1] using hy
  have hcount := MovingFiberCarrier6815.carrier_count_le_ledger g
    (nodes := IRSProfile.domain) (u0 := u0) (u1 := u1)
    D P.total P.s F.1 hDlow hDchar hF.1 hF.2.1 hF.2.2 hsmallT hsmallY hr
    selected (regularSeeds Q selected Gamma F)
    (fun g hg => hdegree g (hsub hg)) (fun g hg => hagreement g (hsub hg))
    (fun g hg => (Finset.mem_filter.mp hg).2.1)
    (fun g hg => (Finset.mem_filter.mp hg).2.2)
    (noLargeSelectedPencil_mono selected Gamma _ 131071 80899 hsub hno)
    (by norm_num [I,IRSProfile.Index]) ha
  exact hcount

theorem root_count
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0) (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181245 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899) (F : RegularIndex Q)
    (th : Array ℕ) (w : ℕ) (hw : 1≤w) (hw16 : w≤21)
    (ha : MovingFiberSingleCore6815.Active th w (regularCumulativeFlag Q F).all
      (regularCumulativeFlag Q F).yz (regularCumulativeFlag Q F).zOnly
      (regularCumulativeFlag Q F).zOnly) :
    (regularSeeds Q selected Gamma F).card ≤ MovingFiberSingleCore6815.rootUpper w
      (regularCumulativeFlag Q F).all (regularCumulativeFlag Q F).yz (regularCumulativeFlag Q F).zOnly := by
  have h := ha
  simp only [MovingFiberSingleCore6815.Active,if_neg (show ¬32≤w by omega),
    if_neg (show w≠0 by omega),if_pos hw16] at h
  rcases h with ⟨hr3,hr31,hv2,hz3,hL,hy,ht⟩
  have hc := root_count_group (MovingFiberSingleCore6815.rootIndex w) D P hDlow hDchar Q hQ hbox
    selected Gamma u0 u1 hdegree hagreement hno F hr31
    (by simpa only [middle,Nat.add_comm] using hy)
    (by simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht)
    ⟨hr3,hv2,hz3,hL⟩
  simpa only [MovingFiberCarrier6815.ledgerCap,MovingFiberCount6815.roundedCaps,
    MovingFiberCount6815.Receipt.rounded_formula,MovingFiberSingleCore6815.rootUpper,
    MovingFiberSingleCore6815.rootSlope,MovingFiberSingleCore6815.rootIntercept] using hc

theorem source_total (j : ℕ) (hj : j<7) : 11192 ≤ (Lower80899.TenPhase.sound j).source.totalCap := by
  interval_cases j <;> decide +kernel

end
end ProximityPrize.SubmissionLower.MovingFiberSingletonGeometry6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.SingletonCurveChecks6815
open FinalCurves6815 MovingFiberSingleCore6815
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 50000

def carrier (r v : ℕ) : Carrier :=
  ⟨MovingFiberShape6815.cost r v 0,MovingFiberShape6815.cost r v 1,MovingFiberShape6815.cost r v 2,
    MovingFiberShape6815.cost r v 3,MovingFiberShape6815.cost r v 4⟩
theorem carrier_correct (r v : ℕ) : (carrier r v).Correct r v := ⟨rfl,rfl,rfl,rfl,rfl⟩

def pointCheck (r v w lo hi z : ℕ) (start : ℕ) (p : Piece) : Bool :=
  if lo≤z ∧ z≤hi then Nat.ble (choice (carrier r v) w r v z) (value p start z) else true

theorem pointCheck_sound (r v w lo hi z start : ℕ) (p : Piece)
    (h : pointCheck r v w lo hi z start p=true) (hl : lo≤z) (hh : z≤hi) :
    choice (carrier r v) w r v z≤value p start z := by
  simpa only [pointCheck,if_pos (show lo≤z ∧ z≤hi from ⟨hl,hh⟩),Nat.ble_eq] using h

def high (r v w lo hi : ℕ) (start : ℕ) (p : Piece) : Bool :=
  let a := max lo 3
  if a≤hi then Nat.ble (choice (carrier r v) w r v a) (value p start a) &&
    Nat.ble (choice (carrier r v) w r v hi) (value p start hi) else true

def checkPair (r v : ℕ) (th : Array ℕ) (start : ℕ) (p : Piece) (runStart : ℕ) (run : Piece) : Bool :=
  let lo := max start runStart
  let stop := min p.stop run.stop
  if lo<stop then
    decide (Active th run.base r v lo (stop-1)) &&
    pointCheck r v run.base lo (stop-1) 0 start p && pointCheck r v run.base lo (stop-1) 1 start p &&
    pointCheck r v run.base lo (stop-1) 2 start p && high r v run.base lo (stop-1) start p
  else true

theorem checkPair_sound (r v : ℕ) (th : Array ℕ) (start : ℕ) (p : Piece)
    (runStart : ℕ) (run : Piece) (z : ℕ)
    (hc : checkPair r v th start p runStart run=true)
    (hp : start≤z) (hp' : z<p.stop) (hr : runStart≤z) (hr' : z<run.stop) :
    Active th run.base r v z z ∧ choice (carrier r v) run.base r v z≤value p start z := by
  let lo := max start runStart
  let hi := min p.stop run.stop-1
  have hn : max start runStart<min p.stop run.stop := by omega
  simp only [checkPair,if_pos hn,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ha,h0⟩,h1⟩,h2⟩,hh⟩ := hc
  have hlo : lo≤z := by dsimp only [lo]; omega
  have hhi : z≤hi := by dsimp only [hi]; omega
  have hzActive : Active th run.base r v z z := by
    exact active_at th run.base r v lo hi z ha hlo hhi
  refine ⟨hzActive,?_⟩
  by_cases hz3 : 3≤z
  · have ha3 : max lo 3≤hi := by omega
    change high r v run.base lo hi start p=true at hh
    simp only [high,if_pos ha3,Bool.and_eq_true,Nat.ble_eq] at hh
    have hl3 : start≤max lo 3 := by dsimp only [lo]; omega
    have hbound := TriangularAffine6815.shifted_between (max lo 3) hi z (max lo 3) start
      (choice (carrier r v) run.base r v (max lo 3)) p.base
      (choiceSlope (carrier r v) run.base r v) p.slope le_rfl hl3 (by omega) hhi
      (by simpa only [value,Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hh.1)
      (by rw [←choice_affine (carrier r v) run.base r v (max lo 3) hi (le_max_right _ _) ha3]; exact hh.2)
    rwa [←choice_affine (carrier r v) run.base r v (max lo 3) z (le_max_right _ _) (by omega)] at hbound
  · have hpoint : z=0 ∨ z=1 ∨ z=2 := by omega
    rcases hpoint with rfl | rfl | rfl
    · exact pointCheck_sound r v run.base lo hi 0 start p h0 hlo hhi
    · exact pointCheck_sound r v run.base lo hi 1 start p h1 hlo hhi
    · exact pointCheck_sound r v run.base lo hi 2 start p h2 hlo hhi

def check (r v : ℕ) (th : Array ℕ) (curve runs : List Piece) : Bool :=
  validFrom (11193-r-v) 0 curve && validFrom (11193-r-v) 0 runs &&
    allCells (fun lo p => allCells (checkPair r v th lo p) 0 runs) 0 curve

theorem check_sound (r v : ℕ) (th : Array ℕ) (curve runs : List Piece)
    (hc : check r v th curve runs=true) (z : ℕ) (hz : z<11193-r-v) :
    ∃ w, Active th w r v z z ∧ choice (carrier r v) w r v z≤FinalCurves6815.eval curve z := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨lo,p,hlo,hhi,he,hp⟩ := cell_at _ 0 _ curve hc.1.1 (allCells_sound _ 0 curve hc.2) z (Nat.zero_le _) hz
  obtain ⟨rlo,run,hrlo,hrhi,_,hcheck⟩ := cell_at _ 0 _ runs hc.1.2 (allCells_sound _ 0 runs hp) z (Nat.zero_le _) hz
  have h := checkPair_sound r v th lo p rlo run z hcheck hlo hhi hrlo hrhi
  exact ⟨run.base,h.1,by simpa only [FinalCurves6815.eval,he] using h.2⟩

end ProximityPrize.SubmissionLower.SingletonCurveChecks6815
end MergedPart1
section MergedPart2
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
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.SingletonCertificate6815
open FinalCurves6815 SingletonCurveChecks6815 FinalThreshold6815
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

structure Header where
  cut : ℕ
  runs : List Lower80899.CompressedBand.Run
  deriving Inhabited

def decodeRuns : ℕ → ℕ → List Lower80899.CompressedBand.Run
  | 0, _ => []
  | n+1, code => ⟨code%16384,code/16384%16⟩ :: decodeRuns n (code/262144)

def decodeHeaders : ℕ → ℕ → List Header
  | 0, _ => []
  | n+1, code =>
    let count := code/16384%16
    ⟨code%16384,decodeRuns count (code/262144)⟩ ::
      decodeHeaders n (code/(262144*262144^count))

structure Row where
  curve : List Piece
  choices : List Piece
  headers : Array Header
  deriving Inhabited

def thresholds (d : Row) : Array ℕ := d.headers.map Header.cut

def allN (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => allN p n && p n

theorem allN_sound (p : ℕ → Bool) (n : ℕ) (h : allN p n=true) :
    ∀ j, j<n → p j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allN,Bool.and_eq_true] at h
    intro j hj
    by_cases he : j=n
    · simpa only [he] using h.2
    · exact ih h.1 j (by omega)

def thresholdCheck (r v : ℕ) (d : Row) (j : ℕ) : Bool :=
  thresholdK (Lower80899.TenPhase.sound j).source r v
    (MovingFiberSingleCore6815.thresholdAt (thresholds d) j)
    ((d.headers[j]?).getD default).runs

def check (r v : ℕ) (d : Row) : Bool :=
  allN (thresholdCheck r v d) 7 && SingletonCurveChecks6815.check r v (thresholds d) d.curve d.choices

theorem check_thresholds (r v : ℕ) (d : Row) (h : check r v d=true) :
    ∀ j, j<7 → Lower80899.ThresholdFast.FastSourceThresholdSufficient
      (Lower80899.TenPhase.sound j).source r v (MovingFiberSingleCore6815.thresholdAt (thresholds d) j) := by
  simp only [check,Bool.and_eq_true] at h
  intro j hj
  exact thresholdK_sound _ _ _ _ _ (allN_sound _ 7 h.1 j hj)

theorem check_curve (r v : ℕ) (d : Row) (h : check r v d=true) :
    SingletonCurveChecks6815.check r v (thresholds d) d.curve d.choices=true := by
  simp only [check,Bool.and_eq_true] at h
  exact h.2

end ProximityPrize.SubmissionLower.SingletonCertificate6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.CompactAllN6815
open SingletonCertificate6815
set_option autoImplicit false

theorem allN_block (p : ℕ → Bool) (k : ℕ) (h : allN (fun j => p (16*k+j)) 16=true)
    (v : ℕ) (h0 : 16*k≤v) (h1 : v<16*k+16) : p v=true := by
  have := allN_sound _ 16 h (v-16*k) (by omega)
  simpa only [Nat.add_sub_cancel' h0] using this

theorem allN_blockN (p : ℕ → Bool) (B k : ℕ) (h : allN (fun j => p (B*k+j)) B=true)
    (v : ℕ) (h0 : B*k≤v) (h1 : v<B*k+B) : p v=true := by
  have := allN_sound _ B h (v-B*k) (by omega)
  simpa only [Nat.add_sub_cancel' h0] using this

theorem allN_zero (p : ℕ → Bool) : allN p 0=true := rfl

theorem allN_snoc (p : ℕ → Bool) (n : ℕ) (h : allN p n=true) (h' : p n=true) : allN p (n+1)=true := by
  simp only [allN,h,h',Bool.and_self]

end ProximityPrize.SubmissionLower.CompactAllN6815
end MergedPart4
