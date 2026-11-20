/- Apache-2.0. The same physical regular fibre is priced across all available
   packet windows and by the incumbent raw bound, at 81,105 errors. -/
import ProximityPrize.SubmissionLower.Night6836ActualFactor
import ProximityPrize.SubmissionLower.Night6836OfferPlan
import ProximityPrize.SubmissionLower.P33Base
import ProximityPrize.SubmissionLower.Night6836PacketFibre
namespace ProximityPrize.SubmissionLower.Raw6836
open scoped Classical
open RCN081 RCN095 RCN130 RCN156 RCN167 RCN174 RCN234 RCN238 RCN266 RCN275 RCN286 RCN313
open LocatorFactorAggregate Koala6831Moving Koala6831MovingPaid
open Koala6835.Offers
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]

def offer_of_window (W:P33.Window) : Offer := ⟨W.r,W.y,W.t,W.low,W.cap⟩
def admissible (W:P33.Window) : Prop :=
  5≤W.r ∧ W.r≤18 ∧ W.r+2≤W.y ∧ W.y≤76 ∧ W.y≤W.t ∧ W.t≤9352

theorem actual_cost {x:I ↪ K} {H:MvPolynomial (Fin 4) K} {S:Finset K} {sel:K→Polynomial K}
    {u v:I→K} {D:ℕ} (A:Original x H S sel u v D)
    (F:RegularIndex H) {r e z:ℕ} (eq:contactFlag F.1=⟨z,e,r⟩)
    (cap:r≤18 ∧ r+e≤76 ∧ r+e+z≤9352)
    (W:ℕ→P33.Window) (good:∀i,P33.WindowCount (W i)) (shape:∀i,admissible (W i)) :
    let t := r+e+z
    (regularFiber H S sel F).card≤rowRaw r e (t-(r+e)) ∧
    ∀i, valid (offer_of_window (W i)) r e t t →
        (regularFiber H S sel F).card≤(offer_of_window (W i)).fee := by
  classical
  obtain ⟨raw,box⟩ := regular_row A F eq cap
  dsimp only
  refine ⟨by simpa only [Nat.add_sub_cancel_left] using raw,?_⟩
  intro i h
  obtain ⟨hr,hy,hl,ht⟩ := h
  obtain ⟨rlo,rhi,ylo,yhi,tlo,thi⟩ := shape i
  have fw : wt residualSWeights F.1 = r := by rw [← contactFlag_all,eq]
  have mw : wt residualYSWeights F.1 = r+e := by rw [← contactFlag_middle,eq];change e+r=r+e;omega
  have tw : wt residualTotalWeights F.1 = r+e+z := by rw [← contactFlag_total,eq];change z+e+r=r+e+z;omega
  exact Night6836PacketFibre.window_fibre_le x H D _ _ A.dlow A.dhigh S sel u v A.hn A.deg A.hits A.pencil
    (W i).r (W i).y (W i).t (W i).low (W i).cap ((good i) x A.hn) rlo rhi ylo yhi tlo thi F box
    (by rw [fw];exact hr) (by rw [mw];exact hy) (by rw [tw];exact ht) (by rw [tw];exact hl)

end ProximityPrize.SubmissionLower.Raw6836
#print axioms ProximityPrize.SubmissionLower.Raw6836.actual_cost

