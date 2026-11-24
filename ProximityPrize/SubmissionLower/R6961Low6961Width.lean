import ProximityPrize.SubmissionLower.R6961Low6961RetainedFees

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6961.Low
open Finset Polynomial
open P3 (K)
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)
open Low6961Retained (Box combined)
open Final50FatReserve (degreeCap)
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty)
open scoped Classical BigOperators

theorem degree_bound {r : Shape} (hr : Valid r) (hx : Box r) :
    r.b ≤ degreeCap r.j := by
  have hjl : 3≤r.j := (Nat.mul_le_mul_left 3 hr.1).trans hr.2.1
  have hju := hx.2.1
  have hj : r.j=3 ∨ r.j=4 ∨ r.j=5 ∨ r.j=6 ∨ r.j=7 := by omega
  rcases hj with hj | hj | hj | hj | hj <;> rw [hj] <;> simp only [degreeCap]
  · exact hx.1
  · exact hx.2.2.1 (by omega)
  · exact hx.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2 (by omega)

/-- The retained factors selected by the actual primary bank spend the
finite charge for their exact total width, before the positive-order allocation. -/
theorem Inventory.retained_charge {Γ : Finset K} {s : K→(Polynomial K)} (d : Inventory Γ s) :
    let r := combined (fun i=>shape (d.factor i)) d.zeros
    (∑ i∈d.zeros,fatPrice (shape (d.factor i))) ≤ retainedTariff r.b r.j r.t := by
  let q i := shape (d.factor i)
  let r := combined q d.zeros
  change (∑ i∈d.zeros,fatPrice (q i)) ≤ retainedTariff r.b r.j r.t
  by_cases empty : d.zeros=∅
  · simp [empty,r,combined,P3_6_8.shapeSum_empty,zeroShape,retainedTariff,retainedTariffs]
  · have box := (d.retained.resolve_left empty).1
    have hv : Valid r := (P3_6_8.shapeSum_valid_or_empty d.fits.1 d.zeros).resolve_left empty
    let e := d.zeros.equivFin.symm
    let ar : Fin d.zeros.card→Shape := fun i=>q (e i).val
    have sums (g : Shape→ℕ) : (∑ i,g (ar i)) = ∑ i∈d.zeros,g (q i) := by
      rw [←sum_attach d.zeros (fun i=>g (q i))]
      exact Fintype.sum_equiv e _ _ (fun _=>rfl)
    have hj : (∑ i,(ar i).j)≤7 := by rw [sums]; exact box.2.1
    have hb : (∑ i,(ar i).b)≤degreeCap (∑ i,(ar i).j) := by
      rw [sums,sums]
      exact degree_bound hv box
    have h := retained_family_fee d.zeros.card ar (fun i=>d.fits.1 (e i).val) hj hb
    rw [sums,sums,sums,sums] at h
    exact h

#print axioms Inventory.retained_charge
end Lower6961.Low
