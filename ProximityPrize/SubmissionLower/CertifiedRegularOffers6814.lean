import ProximityPrize.SubmissionLower.RelativeCertifiedOffers6814
import ProximityPrize.SubmissionLower.CertifiedFactorInputs6814

/-! The certified offers consume ordinary regular factors, with their actual
weights. The caller supplies no interpolation helper or desired count. -/
namespace ProximityPrize.SubmissionLower.CertifiedRegularOffers6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
open MvPolynomial RCN156 RCN234 RCN238
open RelativeCertificate6814 CertifiedFactorInputs6814
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

structure Input (nodes : I ↪ K) (u0 u1 : I → K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Prop where
  degree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071
  agreement : ∀ gamma∈Gamma, 181255≤
    ((Finset.univ : Finset I).filter (fun i =>
      (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card
  noPencil : NoLargeSelectedPencil selected Gamma 131071 80889

variable (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I=262144)
  (selected : K → Polynomial K) (Gamma : Finset K)
  (inp : Input nodes u0 u1 selected Gamma)
include inp hI

theorem relative_count (i : Fin 74) {D L s : ℕ} {H : MvPolynomial (Fin 4) K}
    (F : RCN266.RegularIndex H)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (hR : wt residualSWeights F.val=(RelativeCertifiedOffers6814.offer i).R)
    (hB : wt residualYSWeights F.val=(RelativeCertifiedOffers6814.offer i).B)
    (hlo : (RelativeCertifiedOffers6814.offer i).T0≤wt residualTotalWeights F.val)
    (hhi : wt residualTotalWeights F.val≤(RelativeCertifiedOffers6814.offer i).T1) :
    (RCN140.regularSeeds H selected Gamma F).card≤(RelativeCertifiedOffers6814.offer i).count := by
  apply RelativeCertifiedOffers6814.regular_count K I i F
    (relative_box_of_carrier_box F.val D L s _ _ hbox le_rfl hR.le)
    rfl le_rfl hR.ge hB.le hlo hhi
    (code_weight_lower F.val (RCN167.positiveRFactors_spec H F.val F.property).1.ne_zero
      _ _ hB hR.le)
    nodes u0 u1 hI selected Gamma inp.degree inp.agreement inp.noPencil

def packetOffer (i : Fin 5) : Band := ![
  ⟨12,55,3494,3568,270000000000000000⟩,
  ⟨12,56,3436,3578,270000000000000000⟩,
  ⟨12,57,3348,3561,270000000000000000⟩,
  ⟨13,53,3416,3560,270000000000000000⟩,
  ⟨13,54,3325,3428,270000000000000000⟩] i

theorem packet_count (i : Fin 5) {D L s : ℕ} {H : MvPolynomial (Fin 4) K}
    (F : RCN266.RegularIndex H) (hDlow : 131072≤D) (hDchar : D<2130706433)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (hR : wt residualSWeights F.val≤(packetOffer i).R)
    (hB : wt residualYSWeights F.val≤(packetOffer i).B)
    (hlo : (packetOffer i).T0≤wt residualTotalWeights F.val)
    (hhi : wt residualTotalWeights F.val≤(packetOffer i).T1) :
    (RCN140.regularSeeds H selected Gamma F).card≤(packetOffer i).count := by
  have gates : 4≤(packetOffer i).R ∧ (packetOffer i).R≤13 ∧
      (packetOffer i).R+2≤(packetOffer i).B ∧ (packetOffer i).B≤57 ∧
      (packetOffer i).B≤(packetOffer i).T1 ∧ (packetOffer i).T1≤3578 := by
    fin_cases i <;> decide
  let P := factorPacket F D L s (packetOffer i).T1 (packetOffer i).B (packetOffer i).R
    hDlow hDchar hbox gates.1 gates.2.1 gates.2.2.1 gates.2.2.2.1
    gates.2.2.2.2.1 gates.2.2.2.2.2 hR hB hhi
    nodes u0 u1 hI selected Gamma inp.degree inp.agreement inp.noPencil
  change P.seeds.card≤(packetOffer i).count
  have hlow : (packetOffer i).T0≤wt residualTotalWeights P.F := hlo
  fin_cases i
  · exact (MovingSourceFiveBands6814.band12_55_count nodes hI P hlow).le
  · exact (MovingSourceFiveBands6814.band12_56_count nodes hI P hlow).le
  · exact (MovingSourceFiveBands6814.band12_57_count nodes hI P hlow).le
  · exact (MovingSourceFiveBands6814.band13_53_count nodes hI P hlow).le
  · exact (MovingSourceFiveBands6814.band13_54_count nodes hI P hlow).le

#print axioms relative_count
#print axioms packet_count
end
end ProximityPrize.SubmissionLower.CertifiedRegularOffers6814
