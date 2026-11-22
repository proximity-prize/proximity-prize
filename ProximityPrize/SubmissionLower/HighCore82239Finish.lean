import ProximityPrize.SubmissionLower.HighCore82219Finish
import ProximityPrize.SubmissionLower.KoalaTwoCutProof

set_option Elab.async false

namespace HighCore82239

open HighCore82219

/-- Recount the ordinary high range at 179,905 agreements. -/
theorem count {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (lo : 2378 ≤ M.overhead) (hi : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 272100187954834303 := by
  have hb := HighCore82219BankProof.listed_ok .h2367 (terminal .h2367) (Or.inl rfl)
  have hret := KoalaRect.retained_of_price hb
    (KoalaTwoSectionPrice.rect_price SplitCut.TwoCut.two_cut_count)
  exact ordinary_high hret M F lo hi

#print axioms count
end HighCore82239
