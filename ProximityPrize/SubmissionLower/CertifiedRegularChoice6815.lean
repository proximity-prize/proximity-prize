import ProximityPrize.SubmissionLower.CertifiedRegularOffers6815
namespace ProximityPrize.SubmissionLower.CertifiedRegularChoice6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open RCN156 RCN234 RCN095 RCN266 LocatorPhase6800Oracle
open CertifiedRegularOffers6815

inductive Choice where
  | relative (i : Fin 190)
  | packet (i : Fin 31)
  deriving DecidableEq

def price : Choice → ℕ
  | .relative i => (RelativeCertifiedOffers6815.offer i).count
  | .packet i => (packetOffer i).count

def Active : Choice → ℕ → ℕ → ℕ → Prop
  | .relative i,r,v,z =>
      r=(RelativeCertifiedOffers6815.offer i).R ∧
      r+v=(RelativeCertifiedOffers6815.offer i).B ∧
      (RelativeCertifiedOffers6815.offer i).T0≤r+v+z ∧
      r+v+z≤(RelativeCertifiedOffers6815.offer i).T1
  | .packet i,r,v,z =>
      r≤(packetOffer i).R ∧ r+v≤(packetOffer i).B ∧
      (packetOffer i).T0≤r+v+z ∧ r+v+z≤(packetOffer i).T1

instance (c : Choice) (r v z : ℕ) : Decidable (Active c r v z) := by
  cases c <;> unfold Active <;> infer_instance

theorem active_between (c : Choice) (r v lo hi z : ℕ)
    (ha : Active c r v lo) (hb : Active c r v hi) (hl : lo≤z) (hh : z≤hi) :
    Active c r v z := by
  cases c <;> simp only [Active] at ha hb ⊢ <;> omega

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem count (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (inp : Input nodes u0 u1 selected Gamma)
    {D L s : ℕ} {H : MvPolynomial (Fin 4) K} (F : RegularIndex H)
    (hDlow : 131072≤D) (hDchar : D<2130706433)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (c : Choice)
    (ha : Active c (RCN130.regularCumulativeFlag H F).all
      (RCN130.regularCumulativeFlag H F).yz (RCN130.regularCumulativeFlag H F).zOnly) :
    (RCN140.regularSeeds H selected Gamma F).card≤price c := by
  have hc := RCN130.originalCumulativeFlag_cumulative F.val
  have hr : (RCN130.regularCumulativeFlag H F).all=wt residualSWeights F.val := hc.1
  have hy : (RCN130.regularCumulativeFlag H F).all+(RCN130.regularCumulativeFlag H F).yz=
      wt residualYSWeights F.val := by
    simpa only [RCN130.regularCumulativeFlag,Nat.add_comm] using hc.2.1
  have ht : (RCN130.regularCumulativeFlag H F).all+(RCN130.regularCumulativeFlag H F).yz+
      (RCN130.regularCumulativeFlag H F).zOnly=wt residualTotalWeights F.val := by
    simpa only [RCN130.regularCumulativeFlag,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hc.2.2
  cases c with
  | relative i =>
    simp only [Active] at ha
    rw [ht,hy,hr] at ha
    exact relative_count nodes u0 u1 hI selected Gamma inp i F hbox ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  | packet i =>
    simp only [Active] at ha
    rw [ht,hy,hr] at ha
    exact packet_count nodes u0 u1 hI selected Gamma inp i F hDlow hDchar hbox ha.1 ha.2.1 ha.2.2.1 ha.2.2.2

end
end ProximityPrize.SubmissionLower.CertifiedRegularChoice6815
