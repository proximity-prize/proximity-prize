import ProximityPrize.SubmissionLower.MovingFiberPackingCheck6811
import ProximityPrize.SubmissionLower.AffineFactorAggregate6808

namespace ProximityPrize.SubmissionLower.MovingFiberPackingSemantics6811
open MovingFiberPackingCheck6811
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def lookup (rows : Nat → Array Nat) (r v : Nat) : Nat := ((rows r)[v]?).getD 0

theorem direct_bellman (own packed : Nat → Array Nat)
    (hown : ∀ r, 1≤r → r≤35 → (own r).size=164-r)
    (hpacked : ∀ r, r≤35 → (packed r).size=164-r)
    (hchecks : ∀ R r, 1≤r → r≤R → R≤35 →
      convolution (own r).toList (packed (R-r)).toList (packed R).toList=true) :
    AffineFactorAggregate6808.BellmanRows 35 163 (lookup own) (lookup packed) := by
  intro r v R V hr hR hV
  have he : r+R-r=R := by omega
  have hc := hchecks (r+R) r hr (by omega) hR
  rw [he] at hc
  have h := convolution_sound (own r).toList (packed R).toList (packed (r+R)).toList hc v V
    (by rw [Array.length_toList,hown r hr (by omega)]; omega)
    (by rw [Array.length_toList,hpacked R (by omega)]; omega)
    (by rw [Array.length_toList,hpacked (r+R) hR]; omega)
  simpa only [Array.getElem?_toList,lookup] using h

theorem symmetric_bellman (own packed : Nat → Array Nat)
    (hown : ∀ r, 1≤r → r≤35 → (own r).size=164-r)
    (hpacked : ∀ r, r≤35 → (packed r).size=164-r)
    (hunder : ∀ r, 1≤r → r≤35 → shifted 0 (own r).toList (packed r).toList=true)
    (hchecks : ∀ R r, 2*r≤R → R≤35 →
      convolution (packed r).toList (packed (R-r)).toList (packed R).toList=true) :
    AffineFactorAggregate6808.BellmanRows 35 163 (lookup own) (lookup packed) := by
  intro r v R V hr hR hV
  have hu := shifted_sound 0 (own r).toList (packed r).toList (hunder r hr (by omega)) v
    (by rw [Array.length_toList,hown r hr (by omega)]; omega)
    (by rw [Array.length_toList,hpacked r (by omega)]; omega)
  have hle : lookup own r v ≤ lookup packed r v := by
    simpa only [Array.getElem?_toList,lookup,Nat.zero_add] using hu
  apply (Nat.add_le_add_right hle _).trans
  by_cases hsplit : r≤R
  · have he : r+R-r=R := by omega
    have hc := hchecks (r+R) r (by omega) hR
    rw [he] at hc
    have h := convolution_sound (packed r).toList (packed R).toList (packed (r+R)).toList hc v V
      (by rw [Array.length_toList,hpacked r (by omega)]; omega)
      (by rw [Array.length_toList,hpacked R (by omega)]; omega)
      (by rw [Array.length_toList,hpacked (r+R) hR]; omega)
    simpa only [Array.getElem?_toList,lookup] using h
  · have he : r+R-R=r := by omega
    have hc := hchecks (r+R) R (by omega) hR
    rw [he] at hc
    have h := convolution_sound (packed R).toList (packed r).toList (packed (r+R)).toList hc V v
      (by rw [Array.length_toList,hpacked R (by omega)]; omega)
      (by rw [Array.length_toList,hpacked r (by omega)]; omega)
      (by rw [Array.length_toList,hpacked (r+R) hR]; omega)
    simpa only [Array.getElem?_toList,lookup,Nat.add_comm] using h

#print axioms direct_bellman
#print axioms symmetric_bellman
end ProximityPrize.SubmissionLower.MovingFiberPackingSemantics6811
