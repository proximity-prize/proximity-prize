import ProximityPrize.SubmissionLower.AffineSingleton6808
import ProximityPrize.SubmissionLower.BoundaryTailTenPhase6808

namespace ProximityPrize.SubmissionLower.AffineSingletonGeometry6808
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open LocatorFactorAggregate LocatorPhase6800Oracle LocatorBatchPhase6800
open Lower80840.Oracle Lower80840.BatchPhase
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
    (sound : Lower80840.Oracle.PhaseSourceSound) (u0 u1 : I → K)
    (kernel : PhaseKernelRealization sound u0 u1)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181304 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80840)
    (F : RegularIndex H)
    (hR : (regularCumulativeFlag H F).all ≤ 33)
    (hY : middle (regularCumulativeFlag H F) ≤ 152)
    (hT : total (regularCumulativeFlag H F) ≤ 8483)
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

theorem root_count
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181304 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80840)
    (F : RegularIndex Q)
    (hr : (regularCumulativeFlag Q F).all ≤ 31)
    (hy : middle (regularCumulativeFlag Q F) ≤ 142)
    (ht : total (regularCumulativeFlag Q F) ≤ 7501)
    (ha : BoundaryTailCarrier6808.Active (regularCumulativeFlag Q F)) :
    (regularSeeds Q selected Gamma F).card ≤
      BoundaryTailAffineRounding6808.rootUpper (regularCumulativeFlag Q F).all
        (regularCumulativeFlag Q F).yz (regularCumulativeFlag Q F).zOnly := by
  have hF := directFactor_data Q F.1 hQ D 131071 P.total P.s hbox F.2
  have hsub := regularSeeds_subset Q selected Gamma F
  have hcum := originalCumulativeFlag_cumulative F.1
  have hsmallT : wt residualTotalWeights F.1 ≤ 7501 := by
    simpa only [regularCumulativeFlag,total,hcum.2.2] using ht
  have hsmallY : wt residualYSWeights F.1 ≤ 142 := by
    simpa only [regularCumulativeFlag,middle,hcum.2.1] using hy
  have hcount := BoundaryTailCarrier6808.carrier_count_le_ledger
    (nodes := IRSProfile.domain) (u0 := u0) (u1 := u1)
    D P.total P.s F.1 hDlow hDchar hF.1 hF.2.1 hF.2.2 hsmallT hsmallY hr
    selected (regularSeeds Q selected Gamma F)
    (fun g hg => hdegree g (hsub hg)) (fun g hg => hagreement g (hsub hg))
    (fun g hg => (Finset.mem_filter.mp hg).2.1)
    (fun g hg => (Finset.mem_filter.mp hg).2.2)
    (noLargeSelectedPencil_mono selected Gamma _ 131071 80840 hsub hno)
    (by norm_num [I,IRSProfile.Index]) ha
  exact hcount.trans (BoundaryTailAffineRounding6808.ledger_le_rootUpper _ _ _ ha.1 ha.2.1)

end
end ProximityPrize.SubmissionLower.AffineSingletonGeometry6808
