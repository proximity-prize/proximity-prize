import ProximityPrize.SubmissionLower.PortfolioPacketIntervals6815
import ProximityPrize.SubmissionLower.LegacyPacketIntervals6815
import ProximityPrize.SubmissionLower.RelativeCertifiedOffers6815
import ProximityPrize.SubmissionLower.CertifiedFactorInputs6815
namespace ProximityPrize.SubmissionLower.CertifiedRegularOffers6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
open MvPolynomial RCN156 RCN234 RCN238
open RelativeCertificate6815 CertifiedFactorInputs6815
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

structure Input (nodes : I ↪ K) (u0 u1 : I → K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Prop where
  degree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071
  agreement : ∀ gamma∈Gamma, 181245≤
    ((Finset.univ : Finset I).filter (fun i =>
      (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card
  noPencil : NoLargeSelectedPencil selected Gamma 131071 80899

variable (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I=262144)
  (selected : K → Polynomial K) (Gamma : Finset K)
  (inp : Input nodes u0 u1 selected Gamma)
include inp hI

theorem relative_count (i : Fin 190) {D L s : ℕ} {H : MvPolynomial (Fin 4) K}
    (F : RCN266.RegularIndex H)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (hR : wt residualSWeights F.val=(RelativeCertifiedOffers6815.offer i).R)
    (hB : wt residualYSWeights F.val=(RelativeCertifiedOffers6815.offer i).B)
    (hlo : (RelativeCertifiedOffers6815.offer i).T0≤wt residualTotalWeights F.val)
    (hhi : wt residualTotalWeights F.val≤(RelativeCertifiedOffers6815.offer i).T1) :
    (RCN140.regularSeeds H selected Gamma F).card≤(RelativeCertifiedOffers6815.offer i).count := by
  apply RelativeCertifiedOffers6815.regular_count K I i F
    (relative_box_of_carrier_box F.val D L s _ _ hbox le_rfl hR.le)
    rfl le_rfl hR.ge hB.le hlo hhi
    (code_weight_lower F.val (RCN167.positiveRFactors_spec H F.val F.property).1.ne_zero
      _ _ hB hR.le)
    nodes u0 u1 hI selected Gamma inp.degree inp.agreement inp.noPencil

def packetOffer (i : Fin 31) : Band := ![
  ⟨11,58,3599,3724,271000000000000000⟩,
  ⟨12,58,3347,3774,271000000000000000⟩,
  ⟨12,59,3294,3774,271000000000000000⟩,
  ⟨13,55,3322,3699,271000000000000000⟩,
  ⟨13,56,3266,3699,271000000000000000⟩,
  ⟨13,57,3213,3456,271000000000000000⟩,
  ⟨13,57,3457,3699,271000000000000000⟩,
  ⟨13,58,3161,3378,271000000000000000⟩,
  ⟨13,58,3379,3543,271000000000000000⟩,
  ⟨13,58,3544,3560,271000000000000000⟩,
  ⟨13,58,3561,3618,271000000000000000⟩,
  ⟨13,58,3619,3680,273041644927340992⟩,
  ⟨13,58,3681,3684,273200000000000000⟩,
  ⟨13,59,3106,3146,271000000000000000⟩,
  ⟨13,59,3147,3378,271000000000000000⟩,
  ⟨13,59,3379,3543,271000000000000000⟩,
  ⟨13,59,3544,3560,271115740514048768⟩,
  ⟨13,59,3561,3599,272690523638300300⟩,
  ⟨12,55,3394,3571,248630000000000000⟩,
  ⟨12,55,3572,3749,258500000000000000⟩,
  ⟨12,56,3338,3543,245390000000000000⟩,
  ⟨12,56,3544,3749,260000000000000000⟩,
  ⟨12,57,3283,3399,246230000000000000⟩,
  ⟨12,57,3400,3516,257680000000000000⟩,
  ⟨12,57,3517,3749,263340000000000000⟩,
  ⟨13,53,3318,3533,245800000000000000⟩,
  ⟨13,53,3534,3749,256910000000000000⟩,
  ⟨13,54,3261,3383,246600000000000000⟩,
  ⟨13,54,3384,3505,252660000000000000⟩,
  ⟨13,54,3506,3627,259580000000000000⟩,
  ⟨13,54,3628,3749,265790000000000000⟩] i
theorem packet_count (i : Fin 31) {D L s : ℕ} {H : MvPolynomial (Fin 4) K}
    (F : RCN266.RegularIndex H) (hDlow : 131072≤D) (hDchar : D<2130706433)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (hR : wt residualSWeights F.val≤(packetOffer i).R)
    (hB : wt residualYSWeights F.val≤(packetOffer i).B)
    (hlo : (packetOffer i).T0≤wt residualTotalWeights F.val)
    (hhi : wt residualTotalWeights F.val≤(packetOffer i).T1) :
    (RCN140.regularSeeds H selected Gamma F).card≤(packetOffer i).count := by
  have gates : 4≤(packetOffer i).R ∧ (packetOffer i).R≤13 ∧
      (packetOffer i).R+2≤(packetOffer i).B ∧ (packetOffer i).B≤59 ∧
      (packetOffer i).B≤(packetOffer i).T1 ∧ (packetOffer i).T1≤4100 := by
    fin_cases i <;> decide
  let P := factorPacket F D L s (packetOffer i).T1 (packetOffer i).B (packetOffer i).R
    hDlow hDchar hbox gates.1 gates.2.1 gates.2.2.1 gates.2.2.2.1
    gates.2.2.2.2.1 gates.2.2.2.2.2 hR hB hhi
    nodes u0 u1 hI selected Gamma inp.degree inp.agreement inp.noPencil
  change P.seeds.card≤(packetOffer i).count
  have hlow : (packetOffer i).T0≤wt residualTotalWeights P.F := hlo
  fin_cases i
  · exact PortfolioPacketIntervals6815.count0 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count1 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count2 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count3 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count4 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count5 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count6 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count7 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count8 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count9 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count10 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count11 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count12 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count13 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count14 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count15 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count16 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count17 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count0 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count1 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count2 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count3 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count4 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count5 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count6 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count7 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count8 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count9 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count10 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count11 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count12 nodes hI P hlow
end
end ProximityPrize.SubmissionLower.CertifiedRegularOffers6815
