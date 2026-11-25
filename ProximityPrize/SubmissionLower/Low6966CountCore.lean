import ProximityPrize.SubmissionLower.Low6966VariableSelect
import ProximityPrize.SubmissionLower.Low6966WeightedTally
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966RetainedCount
import ProximityPrize.SubmissionLower.Low6966RetainedPrimary
import ProximityPrize.SubmissionLower.Low6966Leading
import ProximityPrize.SubmissionLower.Low6966FatCount

set_option Elab.async false

-- merged module R6960Low6966CountCore
section Merged_R6960Low6966CountCore

set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace LowProfile6966
noncomputable section
open Finset Polynomial
open P3 (K)
open K1_13 (Row Shape shape extend OnFactor atJet)
open Low6966Prices (ActiveFits)
open Low6966Allocation (Band Receipt budget GateTable start)
open Low6966Gate (floorShape Gated)
open Low6966AllocTotal (retainedShape)
open Low6966RetainedCut (Bank)
open scoped BigOperators Polynomial

private theorem start_floor (k : Band) (hk : k.val < 13) : floorShape k.val = start k := by
  fin_cases k <;> first | (exfalso; revert hk; decide) | decide +kernel

private theorem allocation (receipts : ∀ k : Band, Receipt k) {G : Shape → ℕ}
    (htab : GateTable (fun k => (receipts k).orders) G) :
    Low6966RetainedCut.Allocation budget 178 G := by
  intro w Γ s hmsg top htop E d
  let f := d.f
  let l := d.orders
  let parts := d.pieces
  have hz : d.zeros = Finset.univ.filter (fun i => l i = 0) := by
    ext i
    simp [d.zero_iff,l]
  have hr : Low6966RetainedCut.sumShape d.zeros (fun i=>shape (f i)) =
      retainedShape (fun i=>shape (f i)) l := by
    rw [hz]
    rfl
  have active (i : Fin d.n) : ActiveFits (f i) 178 := (Final50GeoCover.activeFits_iff _ _).mpr
    ((Finset.single_le_sum (fun j _=>Nat.zero_le (Final50GeoCover.activeDegree (f j)))
      (Finset.mem_univ i)).trans d.active_budget)
  have count : (∑ i,(parts i).card)≤Low6966Allocation.factorCap top := by
    apply Low6966AllocTotal.total receipts G htab top htop d.n (fun i=>shape (f i)) l (fun i=>(parts i).card)
      d.fits d.layers
    · intro i m hm hml k hk
      have hi : 0<l i := hm.trans_le hml
      have hn : i∉d.zeros := fun h=>(Nat.ne_of_gt hi) ((d.zero_iff i).mp h)
      have floor : K1_13.InBox (Low6966Allocation.start k)
          (Low6966RetainedCut.sumShape d.zeros (fun j=>shape (f j))) :=
        hr.symm ▸ Low6966Allocation.admits_floor hk
      exact d.contracted i hn m hm hml 178 (active i) _ floor
    · intro i m u hm hml allowed
      obtain ⟨Q,proper,box,weight,ha,horder⟩ := d.proper i (hm.trans_le hml)
      have cut : ProperCut (f i) (parts i) s m :=
        ⟨Q,proper,box,weight,ha,fun γ hγ e he=>hml.trans (horder γ (d.subset i hγ) e he)⟩
      by_cases stock : Low6966SharedPrice.RateFits (shape (f i)) u
      · exact Low6966SharedCount.proof w (parts i) s (hmsg.mono (d.subset i)) (f i)
          (d.small i) 178 (active i) (d.on_factor i) m hm cut u stock
      · exact absurd allowed stock
    · intro i m hm hml k hk hg
      have hi : 0<l i := hm.trans_le hml
      have hn : i∉d.zeros := fun h=>(Nat.ne_of_gt hi) ((d.zero_iff i).mp h)
      have floor : K1_13.InBox (Low6966Allocation.start k)
          (Low6966RetainedCut.sumShape d.zeros (fun j=>shape (f j))) :=
        hr.symm ▸ Low6966Allocation.admits_floor hk
      exact d.gated i hn m hm hml 178 (active i) k.val
        (by rw [start_floor k hg.1]; exact floor) hg
    · intro i eligible
      exact Low6966FatCount.proof w (parts i) s (hmsg.mono (d.subset i)) (f i) (d.small i)
        (d.on_factor i) eligible E (d.fat i)
  have low : Low6966Prices.lowerCap top ≤ budget := by interval_cases top <;> decide +kernel
  change (∑ i,(parts i).card)≤budget-Low6966Prices.lowerCap top at count
  change Low6966Prices.lowerCap top+(∑ i,(parts i).card)≤budget
  omega

/-- Native low count from the finite group certificates, with the actual
analytic pricing theorems supplied by the guarded 69.60 modules. -/
theorem count_with_receipts (receipts : ∀ k : Band, Receipt k) {G : Shape → ℕ}
    (htab : GateTable (fun k => (receipts k).orders) G) (gate : Low6966RetainedCut.GateBank G)
    {cap u del Γ}
    (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179769 M Γ)
    (lo : 1≤M.overhead) (hi : M.overhead≤2329) :
    Γ.card≤274790602290452470 := by
  have messages := Low6966Order.messages_of_family M F hi
  obtain ⟨P,nz,box,active,weight,zero⟩ := Anchor6966.anchor_of_family M F hi
  have hw : TrueWeightLE P anchorCutoff := by
    apply (trueWeight_iff P).mpr
    rw [←differentialWeight_eq,←PolynomialDifferential.differentialWeightedDegree]
    exact weight
  obtain ⟨book,E,booked,fat⟩ := fat_of_family M F lo hi
  exact Low6966RetainedCut.count_of_data gate (allocation receipts htab) messages
    (Bank.of_messages messages) (Bank.of_messages_ranked messages)
    P nz box hw active zero (fun _ ht=>Low6966Leading.lower_count ht) book E booked fat

#print axioms count_with_receipts
end
end LowProfile6966

end Merged_R6960Low6966CountCore
