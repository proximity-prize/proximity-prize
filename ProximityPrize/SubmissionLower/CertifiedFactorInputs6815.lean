import ProximityPrize.SubmissionLower.MovingSourceBandGeometry6815
import ProximityPrize.SubmissionLower.RelativeRecordCover6815
namespace ProximityPrize.SubmissionLower.CertifiedFactorInputs6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped Classical
open MvPolynomial RCN081 RCN095 RCN135 RCN136 RCN156 RCN174 RCN234 RCN238 RCN243 RCN260 RCN275 RCN319
open LocatorHybridCells MovingSourceBandGeometry6815
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem code_weight_lower (F : MvPolynomial (Fin 4) K) (hF : F≠0) (B R : ℕ)
    (hB : wt residualYSWeights F=B) (hR : wt residualSWeights F≤R) :
    131071*B-R≤wt (RCN081.contactWeights 131071) F := by
  have hc := RCN180.residualYS_mul_le_contact_add_slope F 131071 (by decide)
  rw [hB] at hc
  omega

theorem relative_box_of_carrier_box (F : MvPolynomial (Fin 4) K) (D L s T R : ℕ)
    (hbox : F∈RCN174.globalCoefficientBox K D 131071 L s)
    (hT : wt residualTotalWeights F≤T) (hR : wt residualSWeights F≤R) :
    F∈RCN100.globalCoefficientBox K D 1 T R := by
  intro e he
  have ht := (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans hT
  have hr := (MvPolynomial.le_weightedTotalDegree residualSWeights he).trans hR
  have hc := (hbox he).2.2
  rw [RCN081.weight_fin4] at ht hr
  simp [residualTotalWeights,residualSWeights] at ht hr
  change e 1+e 2+e 3≤T ∧ e 2≤R ∧ e 0+1*e 1+(1-1)*e 2<D
  omega

def factorPacket {H : MvPolynomial (Fin 4) K} (F : RCN266.RegularIndex H)
    (D L s t y r : ℕ) (hDlow : 131072≤D) (hDchar : D<2130706433)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (hrlo : 4≤r) (hrhi : r≤13) (hylo : r+2≤y) (hyhi : y≤59) (hyt : y≤t) (hthi : t≤4100)
    (hR : wt residualSWeights F.val≤r) (hY : wt residualYSWeights F.val≤y)
    (hT : wt residualTotalWeights F.val≤t)
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899) : Packet (nodes : I → K) t y r where
  rlow := hrlo
  rhigh := hrhi
  ylow := hylo
  yhigh := hyhi
  yt := hyt
  thigh := hthi
  D := D
  Dlow := hDlow
  Dchar := hDchar
  F := F.val
  irreducible := (RCN167.positiveRFactors_spec H F.val F.property).1
  rdegree := (RCN167.positiveRFactors_spec H F.val F.property).2.2
  box := by
    intro e he
    have ht := (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans hT
    have hr := (MvPolynomial.le_weightedTotalDegree residualSWeights he).trans hR
    rw [RCN081.weight_fin4] at ht hr
    simp [residualTotalWeights,residualSWeights] at ht hr
    exact ⟨by omega,by omega,(hbox he).2.2⟩
  support := by
    constructor <;> dsimp [cellSupport,RCN198.support,cellA,cellB,cellS] <;> omega
  selected := selected
  seeds := RCN140.regularSeeds H selected Gamma F
  nodes := Finset.univ
  u0 := u0
  u1 := u1
  injective := nodes.injective.injOn
  nodeCount := by simpa only [Finset.card_univ] using hI
  degree := fun gamma hg => hdegree gamma (RCN140.regularSeeds_subset H selected Gamma F hg)
  agreement := fun gamma hg => hagreement gamma (RCN140.regularSeeds_subset H selected Gamma F hg)
  solution := fun _ hg => (Finset.mem_filter.mp hg).2.1
  regular := fun _ hg => (Finset.mem_filter.mp hg).2.2
  noPencil := noLargeSelectedPencil_mono selected Gamma _ 131071 80899
    (RCN140.regularSeeds_subset H selected Gamma F) hno

end
end ProximityPrize.SubmissionLower.CertifiedFactorInputs6815
