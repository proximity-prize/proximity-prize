-- Ported from public PR657, e07f14a81dfe2cf1bda985e67040ad4d31fe81ab, Pr657High6955Finish.lean.
import ProximityPrize.SubmissionLower.Pr657High6955
import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry
import ProximityPrize.SubmissionLower.HighCore82258Ledger
import ProximityPrize.SubmissionLower.Pr657Rect2435Bank
import ProximityPrize.SubmissionLower.KoalaTwoCutProof

set_option Elab.async false
set_option autoImplicit false

namespace Pr657High6955
open Polynomial HighCore82258
open K1_14 (atMark)

private abbrev b:Band := .h2367

theorem retained (hbank : P3_7_1.BankOK (terminal b)) :
    KoalaRect.GradedRetainedCount :=
  KoalaRect.retained_of_price hbank
    (KoalaTwoSectionPrice.rect_price SplitCut.TwoCut.two_cut_count)

private theorem ordinary_with_prefix
    (hSource:CRTSourceExists) (hPrefix:HighCore82258.GradedC3)
    (hRetained:KoalaRect.GradedRetainedCount)
    {u:P1.Words} {del:Finset P1.I} {Γ:Finset P1.K}
    (M:AnchorModel u del) (F:AnchoredFamily M Γ)
    (hlo:(start b:ℤ)≤(effectiveHeight M)) (hhi:(effectiveHeight M)≤(finish b:ℤ)) :
    Γ.card≤273002714226794744:=by
  classical
  have hw:InBand b (effectiveHeight M):=⟨hlo,hhi⟩
  let regular:=Γ.erase M.shift
  have hreg:regular ⊆ Γ:=Finset.erase_subset _ _
  have hshift:M.shift ∉ regular:=Finset.notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar,fun γ hγ => F.mark γ (hreg hγ),F.distinct.mono hreg⟩
  suffices hc : regular.card + 1 ≤ 273002714226794744 by
    have herase:Γ.card - 1≤regular.card:=Finset.pred_card_le_card_erase
    omega
  obtain ⟨H,hH⟩:=FrontCore82258.adjacent_chart M G
  obtain ⟨C⟩:=hSource b u del M regular G hw hshift H hH
  let rows:=C.rows
  have src:Source b M G rows:=C.source
  obtain ⟨pairs⟩:=buffered_pairs b M G hw src
  obtain ⟨I⟩ := hPrefix b u del M regular G hw hshift H hH
    (fun _ => persistent_curve M G hw) rows src pairs
  let Q:=I.inventory
  let f:=I.equation
  let keep:=regular \ Q.books.union
  have hk:keep ⊆ regular:=Finset.sdiff_subset
  have hpaid : (regular \ keep).card ≤ gradedPrefix b f.natDegree := by
    apply (Finset.card_le_card ?_).trans (Q.books.card_union_graded I.loss_paid)
    intro γ hγ
    obtain ⟨ha,hn⟩:=Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have cover : ∀ γ ∈ keep, ∃ q ∈ Q.parents, MarkOn M G q γ := fun γ hγ =>
    (Q.covers γ (hk hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  have hkept : keep.card ≤ gradedRetained f.natDegree := by
    by_cases hm:keep.Nonempty
    · obtain ⟨γ,hγ⟩ := hm
      obtain ⟨q,hq,_⟩:=cover γ hγ
      have hf:=I.projected ⟨q,hq⟩
      have hred:Reduced f:=⟨hf.positive,hf.primitive,hf.separable⟩
      apply hRetained u del M regular G hw hshift H hH C pairs Q f hred hf keep hk
      intro η hη
      obtain ⟨q',hq',hon⟩:=cover η hη
      have hz:=RingHom.mem_ker.mp (hon (hf.vanishes q' hq'))
      simpa only [coe_eval₂RingHom,eval₂_C,atMark] using hz
    · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
  have hpart:=Finset.card_sdiff_add_card_eq_card hk
  have hbudget:=graded_budget f.natDegree
  change gradedPrefix b f.natDegree + gradedRetained f.natDegree + 1 ≤ 273002714226794744 at hbudget
  omega

theorem count_of_receipts
    (hSource:CRTSourceExists) (hPrefix:HighCore82258.GradedC3)
    (hbank:P3_7_1.BankOK (terminal b)):Count:=by
  intro u del Γ M F lo hi
  have heq := FrontCore82258.effective_eq_overhead M (show (2430 : ℤ) ≤ M.overhead by omega)
  apply ordinary_with_prefix hSource hPrefix (retained hbank) M F
  · rw [heq]
    change (2431 : ℤ) ≤ M.overhead
    exact lo
  · rw [heq]
    change M.overhead ≤ (2695 : ℤ)
    exact hi

theorem count : Count :=
  count_of_receipts HighCore82258BankProof.interpolation_sources_for_crt
    (HighCore82258_3.of_children HighCore82258_3_1.proof HighCore82258_3_2.proof
      schedule graded_ledger)
    Pr657Rect2435Receipts.terminal_ok

#print axioms retained
#print axioms count
end Pr657High6955
