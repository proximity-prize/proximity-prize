import ProximityPrize.SubmissionLower.MovingFiberCarrier6815
import ProximityPrize.SubmissionLower.MovingFiberSingleCore6815
import ProximityPrize.SubmissionLower.MovingFiberPhaseCore6815
import ProximityPrize.SubmissionLower.AffineFactorAggregate6808
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
