import ProximityPrize.SubmissionLower.High55Wide2524Finish
import ProximityPrize.SubmissionLower.HighCore82268Finish

set_option Elab.async false

namespace High55Wide

theorem ordinary_high_from2524 {u del} (M : FrontCore82268.AnchorModel u del)
    {Γ} (F : FrontCore82268.AnchoredFamily M Γ)
    (hl : 2524 ≤ M.overhead) (hu : M.overhead ≤ (HighCore82268.heightCap : ℤ)) :
    Γ.card ≤ 271937844038970720 := by
  by_cases old : 2527 ≤ M.overhead
  · exact (HighCore82268.ordinary_high_from2527 M F old hu).trans (by decide)
  · exact High55Wide2524.ordinary_high_2524_2526 M F hl (by omega)

#print axioms ordinary_high_from2524
end High55Wide
