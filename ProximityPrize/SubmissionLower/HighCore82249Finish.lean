import ProximityPrize.SubmissionLower.HighCore82219Finish
import ProximityPrize.SubmissionLower.KoalaTwoCutProof


namespace HighCore82249

open HighCore82219

/-- Recount the ordinary high range at 179,895 agreements. -/
theorem count {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (lo : 2391 ≤ M.overhead) (hi : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 272966371768711151 := by
  have hb := HighCore82219BankProof.listed_ok .h2367 (terminal .h2367) (Or.inl rfl)
  have hret := KoalaRect.retained_of_price hb
    (KoalaTwoSectionPrice.rect_price SplitCut.TwoCut.two_cut_count)
  exact ordinary_high hret M F lo hi

end HighCore82249
