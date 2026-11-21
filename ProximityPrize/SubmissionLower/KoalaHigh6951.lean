import ProximityPrize.SubmissionLower.HighCore82229Finish
import ProximityPrize.SubmissionLower.KoalaTwoCutProof

set_option autoImplicit false

namespace KoalaHigh6951
open HighCore82229

theorem count {u : P1.Words} {del : Finset P1.I} (M : AnchorModel u del)
    {Γ : Finset P1.K} (F : AnchoredFamily M Γ)
    (lo : 2356 ≤ M.overhead) (hi : M.overhead ≤ (33385 : ℤ)) :
    Γ.card ≤ 268265986140156442 := by
  have hbank := HighCore82229BankProof.listed_ok .h2367 (terminal .h2367) (Or.inl rfl)
  have hretained := KoalaRect.retained_of_price hbank
    (KoalaTwoSectionPrice.rect_price SplitCut.TwoCut.two_cut_count)
  exact HighCore82229.ordinary_high hretained M F lo hi

#print axioms count
end KoalaHigh6951
