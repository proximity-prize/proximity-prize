import ProximityPrize.SubmissionLower.HighCore82258Finish
import ProximityPrize.SubmissionLower.KoalaTwoCutProof

set_option autoImplicit false

namespace KoalaHigh6954
open HighCore82258

theorem count {u : P1.Words} {del : Finset P1.I} (M : AnchorModel u del)
    {Γ : Finset P1.K} (F : AnchoredFamily M Γ)
    (lo : 2414 ≤ M.overhead) (hi : M.overhead ≤ (33443 : ℤ)) :
    Γ.card ≤ 267872462194200158 := by
  have hbank := HighCore82258BankProof.listed_ok .h2367 (terminal .h2367) (Or.inl rfl)
  have hretained := KoalaRect.retained_of_price hbank
    (KoalaTwoSectionPrice.rect_price SplitCut.TwoCut.two_cut_count)
  exact HighCore82258.ordinary_high hretained M F lo hi

#print axioms count
end KoalaHigh6954
