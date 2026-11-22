import ProximityPrize.SubmissionLower.Peer653High53FamilyInterfaces

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
noncomputable section
open Polynomial
open Peer653High53 (Band AnchorModel AnchoredFamily K)
open K1_14 (Banks Equation SeedBound atMark graphEval)
open K1_14_3 (ProjectedProduct)
open K1_14_4 (seedDegree seedDegree_le_iff)
theorem of_children (h1 : CRTSourceExists) (h2 : c2) (h3 : c3)
    (hRetained : ∀ b, RetainedCountAt b) : Peer653High53.HighStatement := by
  classical
  intro b u del M Γ F hlo hhi
  have hw : InBand b M.overhead := ⟨hlo,hhi⟩
  let regular := Γ.erase M.shift
  have hreg : regular ⊆ Γ := Finset.erase_subset _ _
  have hshift : M.shift ∉ regular := Finset.notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar, fun γ hγ => F.mark γ (hreg hγ), F.distinct.mono hreg⟩
  suffices hc : regular.card ≤ (prefixFee b) + (retainedCap b) by
    have herase : Γ.card - 1 ≤ regular.card := Finset.pred_card_le_card_erase
    omega
  obtain ⟨H,hH⟩ := High53Model.adjacent_chart M G
  obtain ⟨C⟩ := h1 b u del M regular G hw hshift H hH
  let rows := C.rows
  have src : Source b M G rows := C.source
  obtain ⟨pairs⟩ := h2 b u del M regular G hw hshift rows src
  obtain ⟨Q⟩ := h3 b u del M regular G hw hshift H hH
    (fun _ => persistent_curve M G hw) rows src pairs
  let keep := regular \ Q.books.union
  have hk : keep ⊆ regular := Finset.sdiff_subset
  have hpaid : (regular \ keep).card ≤ (prefixFee b) := by
    apply (Finset.card_le_card ?_).trans Q.books.card_union
    intro γ hγ
    obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have cover : ∀ γ ∈ keep, ∃ q ∈ Q.parents, MarkOn M G q γ := fun γ hγ =>
    (Q.covers γ (hk hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  suffices hkept : keep.card ≤ (retainedCap b) by
    have hpart := Finset.card_sdiff_add_card_eq_card hk
    omega
  by_cases hm : keep.Nonempty
  · obtain ⟨γ,hγ⟩ := hm
    obtain ⟨q,hq,_⟩ := cover γ hγ
    obtain ⟨f,hf⟩ := K1_14_3_7.proof Q.parents ⟨q,hq⟩ Q.geometric
    have hred : Reduced f := ⟨hf.positive, hf.primitive, hf.separable⟩
    apply hRetained b u del M regular G hw hshift H hH C pairs Q f hred hf keep hk
    intro η hη
    obtain ⟨q',hq',hon⟩ := cover η hη
    have hz := RingHom.mem_ker.mp (hon (hf.vanishes q' hq'))
    simpa only [coe_eval₂RingHom, eval₂_C, atMark] using hz
  · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
end
end Peer653High53
end
