import ProximityPrize.SubmissionLower.R6961Low6961AllocTotal
import ProximityPrize.SubmissionLower.R6961Low6961RetainedCount
import ProximityPrize.SubmissionLower.R6961Low6961RetainedPrimary
import ProximityPrize.SubmissionLower.R6961Low6961Leading
import ProximityPrize.SubmissionLower.R6961Low6961FatCount
import ProximityPrize.SubmissionLower.R6961Low6961WeightedProof

set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6961.Low
noncomputable section
open Finset Polynomial
open P3 (K)
open K1_13 (Row shape extend OnFactor atJet)
open Low6961Prices (ActiveFits)
open Low6961Allocation (Band Receipt budget)
open Low6961AllocTotal (retainedShape)
open Low6961RetainedCut (Bank)
open scoped BigOperators Polynomial

private theorem allocation (receipts : ∀ k : Band, Receipt k) :
    Low6961RetainedCut.Allocation budget 165 := by
  intro w Γ s hmsg top htop E d
  let f := d.f
  let l := d.orders
  let parts := d.pieces
  have hz : d.zeros = Finset.univ.filter (fun i => l i = 0) := by
    ext i
    simp [d.zero_iff,l]
  have hr : Low6961RetainedCut.sumShape d.zeros (fun i=>shape (f i)) =
      retainedShape (fun i=>shape (f i)) l := by
    rw [hz]
    rfl
  have active (i : Fin d.n) : ActiveFits (f i) 165 := (Final50GeoCover.activeFits_iff _ _).mpr
    ((Finset.single_le_sum (fun j _=>Nat.zero_le (Final50GeoCover.activeDegree (f j)))
      (Finset.mem_univ i)).trans d.active_budget)
  have count : (∑ i,(parts i).card)≤Low6961Allocation.factorCap top := by
    apply Low6961AllocTotal.total receipts top htop d.n (fun i=>shape (f i)) l (fun i=>(parts i).card)
      d.fits d.layers
    · intro i m hm hml k hk
      have hi : 0<l i := hm.trans_le hml
      have hn : i∉d.zeros := fun h=>(Nat.ne_of_gt hi) ((d.zero_iff i).mp h)
      have floor : K1_13.InBox (Low6961Allocation.start k)
          (Low6961RetainedCut.sumShape d.zeros (fun j=>shape (f j))) :=
        hr.symm ▸ Low6961Allocation.admits_floor hk
      exact d.contracted i hn m hm hml 165 (active i) _ floor
    · intro i m u hm hml allowed
      obtain ⟨Q,proper,box,weight,ha,horder⟩ := d.proper i (hm.trans_le hml)
      have cut : ProperCut (f i) (parts i) s m :=
        ⟨Q,proper,box,weight,ha,fun γ hγ e he=>hml.trans (horder γ (d.subset i hγ) e he)⟩
      by_cases stock : Low6961SharedPrice.RateFits (shape (f i)) u
      · exact Low6961SharedCount.proof w (parts i) s (hmsg.mono (d.subset i)) (f i)
          (d.small i) 165 (active i) (d.on_factor i) m hm cut u stock
      · exact Low6961WeightedProof.count (hmsg.mono (d.subset i)) (f i) (d.small i)
          (active i) (d.on_factor i) m hm cut u allowed stock
    · intro i eligible
      exact Low6961FatCount.proof w (parts i) s (hmsg.mono (d.subset i)) (f i) (d.small i)
        (d.on_factor i) eligible E (d.fat i)
  have low : Low6961Prices.lowerCap top ≤ budget := by interval_cases top <;> decide +kernel
  change (∑ i,(parts i).card)≤budget-Low6961Prices.lowerCap top at count
  change Low6961Prices.lowerCap top+(∑ i,(parts i).card)≤budget
  omega

/-- Native low count from the finite group certificates, with the actual
analytic pricing theorems supplied by the guarded 69.60 modules. -/
theorem count_with_receipts (receipts : ∀ k : Band, Receipt k) {cap u del Γ}
    (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179818 M Γ)
    (lo : 1≤M.overhead) (hi : M.overhead≤2326) :
    Γ.card≤265959947636540641 := by
  have messages := Low6961Order.messages_of_family M F hi
  obtain ⟨P,nz,box,active,weight,zero⟩ := Low6961Anchor.anchor_of_family M F hi
  have hw : TrueWeightLE P anchorCutoff := by
    apply (trueWeight_iff P).mpr
    rw [←differentialWeight_eq,←PolynomialDifferential.differentialWeightedDegree]
    exact weight
  obtain ⟨book,E,booked,fat⟩ := fat_of_family M F lo hi
  exact Low6961RetainedCut.count_of_data (allocation receipts) messages
    (Bank.of_messages messages) (Bank.of_messages_ranked messages)
    P nz box hw active zero (fun _ ht=>Low6961Leading.lower_count ht) book E booked fat

#print axioms count_with_receipts
end
end Lower6961.Low
