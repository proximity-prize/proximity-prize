import ProximityPrize.SubmissionLower.R6966ProofPhysicalHelperTariff
import ProximityPrize.SubmissionLower.R6966ProofQuadraticBudget

set_option Elab.async false

namespace Research6966.QuadraticHelper6966
open Polynomial Finset
open K1 (I K p)
open QuadraticBudget (band budget price fee votes from_votes)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)

noncomputable section
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 18
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 5000

/-- The low-physical-degree helper receives its paid twelve-quadrillion
word bound throughout the transition. This includes exceptional labels. -/
theorem low_count {u deleted maxHeight} {anchor:P1.ModelAt maxHeight u deleted} {Γ T:Finset K}
    (fam:P1.FamilyAt 179769 anchor Γ) (sub:T⊆Γ) {h:ℕ} (lo:2330≤h) (hi:h≤2499)
    {D:PoleData h} {Crt:CRTLift D} {N:Jet} (M:HelperPhysicalModel.Model Crt N)
    (prime:Prime N) (ns:N.natDegree=1) (quad:K1_14_2_2_2_1.jetDegree N=2)
    (width:ℕ) (sm:width≤92) (cap:∀ j i,((N.coeff j).coeff i).totalDegree≤width)
    (low:RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw<(band width).2)
    (height:anchor.overhead≤(h:ℤ))
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K K1_14.L (K1.node i))≠0)
    (res:∀ γ∈T,MarkResidues D (anchor.label γ) (fam.scalar γ))
    (belongs:∀ γ∈T,jetAt N (anchor.label γ) (fam.scalar γ)=0) :
    T.card≤budget := by
  obtain ⟨hp,hl,ch,dp,gap,maxD⟩:=QuadraticBudget.numeric lo hi sm
  have height' : (131071:ℤ)+anchor.overhead≤((131071+h:ℕ):ℤ) := by
    rw [Nat.cast_add]
    exact add_le_add (le_refl (131071:ℤ)) height
  apply QuadraticBudget.from_family (length:=Fintype.card I) (char:=p)
    ProximityPrize.Benchmark.IRSProfile.card_index rfl hi sm maxD low
  exact PhysicalHelperTariff.price (a:=179769) fam sub hp hl M prime ns quad width (131071+h)
    cap ch height' le_rfl dp gap nodes res belongs

#print axioms low_count
end
end Research6966.QuadraticHelper6966
