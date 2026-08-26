import ProximityPrize.SubmissionLower.BCHKSFixedCoreAnchorJohnson6401

/-!
# A global rich-overlap graph forces a million-scale secant fan at 6401

This file isolates the exact graph-to-source consequence of the new
degree-three Johnson-scheme certificate.  The certified independence cap is
`89184234`, while the refined high-error owner mass is
`185800471298159157`.  A maximum independent set is dominating, so its
closed neighborhoods cover the graph.  Exact division therefore forces one
owner to have at least `2083333151` rich neighbors.

At a fixed owner, equal polynomial secants form one literal affine owner
line.  Under failure of the requested `1183`-owner curve, one secant label
can carry at most `1181` nonanchor owners.  Hence the rich neighborhood
contains at least `1764042` distinct source-faithful polynomial slopes.

The final ledger records the present obstruction: the strongest existing
fixed-word/spherical cap is `17045844`, more than nine times the forced fan.
Thus the global graph is a real structural amplification, but a score-6401
closure still needs either a sharper anchored label cap or an additional
post-density identity coupling different incident slopes.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalSecantFan6401

open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSFixedCoreAnchorJohnson6401

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

def refinedHighErrorOwnerMass6401 : Nat := 185800471298159157
def coupledOverlapIndependenceCap6401 : Nat := 89184234
def coupledCriticalDegree6401 : Nat := 2083333151
def forcedDistinctSecantFan6401 : Nat := 1764042

/-- The exact quotient interval behind the graph amplification. -/
theorem refinedMass_criticalDegree_ledger6401 :
    coupledOverlapIndependenceCap6401 * coupledCriticalDegree6401 <
        refinedHighErrorOwnerMass6401 ∧
      refinedHighErrorOwnerMass6401 ≤
        coupledOverlapIndependenceCap6401 *
          (coupledCriticalDegree6401 + 1) := by
  native_decide

/-- `1764042` is the exact ceiling of the critical degree divided by the
no-curve nonanchor fibre capacity `1181`. -/
theorem forcedDistinctSecantFan_exact6401 :
    1181 * (forcedDistinctSecantFan6401 - 1) <
        coupledCriticalDegree6401 ∧
      coupledCriticalDegree6401 ≤
        1181 * forcedDistinctSecantFan6401 := by
  native_decide

/-- Pure covering form of the maximum-independent-set argument.  In the
graph application `I` is a maximum independent set, `N r` is the open
neighborhood of `r`, and maximality gives `hcover`. -/
theorem exists_large_neighbor_family_of_dominating_cap6401
    {V : Type*} [DecidableEq V]
    (S I : Finset V) (N : V → Finset V)
    (hmass : refinedHighErrorOwnerMass6401 ≤ S.card)
    (hIcard : I.card ≤ coupledOverlapIndependenceCap6401)
    (hcover : S ⊆ I.biUnion fun r => insert r (N r)) :
    ∃ r ∈ I, coupledCriticalDegree6401 ≤ (N r).card := by
  by_contra hnone
  have hsmall : ∀ r ∈ I, (N r).card < coupledCriticalDegree6401 := by
    intro r hr
    by_contra hnot
    exact hnone ⟨r, hr, Nat.le_of_not_gt hnot⟩
  have hclosed : ∀ r ∈ I,
      (insert r (N r)).card ≤ coupledCriticalDegree6401 := by
    intro r hr
    exact (Finset.card_insert_le r (N r)).trans (by
      have := hsmall r hr
      omega)
  have hcovered : S.card ≤
      I.card * coupledCriticalDegree6401 := by
    exact (Finset.card_le_card hcover).trans
      (Finset.card_biUnion_le_card_mul I
        (fun r => insert r (N r)) coupledCriticalDegree6401 hclosed)
  have hcap : S.card ≤
      coupledOverlapIndependenceCap6401 * coupledCriticalDegree6401 :=
    hcovered.trans
      (Nat.mul_le_mul_right coupledCriticalDegree6401 hIcard)
  have himpossible : refinedHighErrorOwnerMass6401 ≤
      coupledOverlapIndependenceCap6401 * coupledCriticalDegree6401 :=
    hmass.trans hcap
  exact (not_le_of_gt refinedMass_criticalDegree_ledger6401.1) himpossible

/-- If every label fibre has the exact no-curve capacity `1181`, a critical
neighborhood has at least `1764042` distinct labels. -/
theorem distinct_labels_card_ge_forcedFan6401
    {Owner Label : Type*} [DecidableEq Owner] [DecidableEq Label]
    (H : Finset Owner) (label : Owner → Label)
    (hH : coupledCriticalDegree6401 ≤ H.card)
    (hfibre : ∀ q ∈ H.image label,
      (H.filter fun z => label z = q).card ≤ 1181) :
    forcedDistinctSecantFan6401 ≤ (H.image label).card := by
  let Q := H.image label
  let fibre : Label → Finset Owner := fun q =>
    H.filter fun z => label z = q
  have hcover : Q.biUnion fibre = H := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, _hq, hzq⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_filter.mp hzq).1
    · intro hz
      exact Finset.mem_biUnion.mpr
        ⟨label z, Finset.mem_image.mpr ⟨z, hz, rfl⟩,
          Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  have hHcap : H.card ≤ Q.card * 1181 := by
    rw [← hcover]
    apply Finset.card_biUnion_le_card_mul Q fibre 1181
    intro q hq
    exact hfibre q hq
  by_contra hnot
  have hQsmall : Q.card ≤ forcedDistinctSecantFan6401 - 1 := by
    have : Q.card < forcedDistinctSecantFan6401 := Nat.lt_of_not_ge hnot
    omega
  have hproduct : H.card ≤
      1181 * (forcedDistinctSecantFan6401 - 1) := by
    apply hHcap.trans
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_right 1181 hQsmall)
  have himpossible : coupledCriticalDegree6401 ≤
      1181 * (forcedDistinctSecantFan6401 - 1) := hH.trans hproduct
  exact (not_le_of_gt forcedDistinctSecantFan_exact6401.1) himpossible

section PolynomialSecants

variable {F : Type*} [Field F] [DecidableEq F]

/-- The polynomial slope from the anchor `r` to the owner `z`. -/
noncomputable def incidentSecantSlope6401
    (P : F → F[X]) (r z : F) : F[X] :=
  Polynomial.C (z - r)⁻¹ * (P z - P r)

theorem incidentSecantSlope_natDegree_le6401
    (P : F → F[X]) (r z : F)
    (hr : (P r).natDegree ≤ ownerDegreeCap6401)
    (hz : (P z).natDegree ≤ ownerDegreeCap6401) :
    (incidentSecantSlope6401 P r z).natDegree ≤ ownerDegreeCap6401 := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_sub_le _ _).trans (max_le hz hr))

/-- A nonanchor owner is reconstructed from its anchored secant label. -/
theorem owner_eq_anchor_add_incidentSecant6401
    (P : F → F[X]) (r z : F) (hz : z ≠ r) :
    P z = P r + Polynomial.C (z - r) * incidentSecantSlope6401 P r z := by
  have hzr : z - r ≠ 0 := sub_ne_zero.mpr hz
  calc
    P z = P r + (P z - P r) := by abel
    _ = P r + Polynomial.C (z - r) *
        (Polynomial.C (z - r)⁻¹ * (P z - P r)) := by
      rw [← mul_assoc, ← Polynomial.C_mul]
      simp [hzr]
    _ = P r + Polynomial.C (z - r) *
        incidentSecantSlope6401 P r z := by
      rfl

/-- Under weak-curve failure, one incident secant label carries at most
`1181` vertices of a nonanchor neighborhood. -/
theorem incidentSecantSlope_fibre_card_le_1181_6401
    (S N : Finset F) (P : F → F[X]) (r : F) (q : F[X])
    (hrS : r ∈ S) (hNsub : N ⊆ S) (hrN : r ∉ N)
    (hPr : (P r).natDegree ≤ ownerDegreeCap6401)
    (hq : q.natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    (N.filter fun z => incidentSecantSlope6401 P r z = q).card ≤ 1181 := by
  let E := N.filter fun z => incidentSecantSlope6401 P r z = q
  have hsub : E ⊆ anchoredSecantOwners6401 S P r q := by
    intro z hz
    have hzN : z ∈ N := (Finset.mem_filter.mp hz).1
    have hzq : incidentSecantSlope6401 P r z = q :=
      (Finset.mem_filter.mp hz).2
    have hzr : z ≠ r := fun h => hrN (h ▸ hzN)
    exact Finset.mem_filter.mpr
      ⟨hNsub hzN, hzr,
        (owner_eq_anchor_add_incidentSecant6401 P r z hzr).trans (by
          rw [hzq])⟩
  exact (Finset.card_le_card hsub).trans
    (anchoredSecantOwners_card_le_1181_6401
      S P r q hrS hPr hq hfail)

/-- Source-facing fixed-anchor consequence of the global graph degree. -/
theorem noCurve_largeNeighborhood_forces_distinctSecantFan6401
    (S N : Finset F) (P : F → F[X]) (r : F)
    (hrS : r ∈ S) (hNsub : N ⊆ S) (hrN : r ∉ N)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P)
    (hNcard : coupledCriticalDegree6401 ≤ N.card) :
    forcedDistinctSecantFan6401 ≤
      (N.image (incidentSecantSlope6401 P r)).card := by
  apply distinct_labels_card_ge_forcedFan6401 N
    (incidentSecantSlope6401 P r) hNcard
  intro q hq
  obtain ⟨z, hzN, hzq⟩ := Finset.mem_image.mp hq
  have hzS : z ∈ S := hNsub hzN
  have hqDegree : q.natDegree ≤ ownerDegreeCap6401 := by
    rw [← hzq]
    exact incidentSecantSlope_natDegree_le6401 P r z
      (hPdegree r hrS) (hPdegree z hzS)
  exact incidentSecantSlope_fibre_card_le_1181_6401
    S N P r q hrS hNsub hrN (hPdegree r hrS) hqDegree hfail

/-- Combined graph/source interface.  A Delsarte-bounded dominating family
and no affine curve force a concrete anchor with both giant rich degree and
at least `1764042` distinct polynomial secants. -/
theorem noCurve_dominatingOverlapGraph_forces_anchorFan6401
    (S I : Finset F) (N : F → Finset F) (P : F → F[X])
    (hmass : refinedHighErrorOwnerMass6401 ≤ S.card)
    (hIcard : I.card ≤ coupledOverlapIndependenceCap6401)
    (hIS : I ⊆ S)
    (hNsub : ∀ r ∈ I, N r ⊆ S)
    (hrN : ∀ r ∈ I, r ∉ N r)
    (hcover : S ⊆ I.biUnion fun r => insert r (N r))
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    ∃ r ∈ I,
      coupledCriticalDegree6401 ≤ (N r).card ∧
        forcedDistinctSecantFan6401 ≤
          ((N r).image (incidentSecantSlope6401 P r)).card := by
  obtain ⟨r, hrI, hrDegree⟩ :=
    exists_large_neighbor_family_of_dominating_cap6401
      S I N hmass hIcard hcover
  refine ⟨r, hrI, hrDegree, ?_⟩
  exact noCurve_largeNeighborhood_forces_distinctSecantFan6401
    S (N r) P r (hIS hrI) (hNsub r hrI) (hrN r hrI)
      hPdegree hfail hrDegree

end PolynomialSecants

/-- The present fixed-word/spherical list theorem is not yet small enough
to contradict the forced fan.  It exceeds nine complete fan floors. -/
theorem existingSphericalCap_exceeds_forcedSecantFan6401 :
    forcedDistinctSecantFan6401 < BCHKSList6401.listBound6401 ∧
      9 * forcedDistinctSecantFan6401 < BCHKSList6401.listBound6401 ∧
      BCHKSList6401.listBound6401 -
        9 * forcedDistinctSecantFan6401 = 1169466 := by
  native_decide

end BCHKSGlobalSecantFan6401
end ProximityPrize.SubmissionLower
