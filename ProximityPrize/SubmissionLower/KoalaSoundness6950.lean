import ProximityPrize.SubmissionLower.FrontAssembly82200
import ProximityPrize.SubmissionLower.Low48GeometryFinish
import ProximityPrize.SubmissionLower.HighCore82219Finish
import ProximityPrize.SubmissionLower.KoalaTwoSectionCount

set_option Elab.async false

namespace KoalaSoundness6950
open ProximityPrize.Benchmark

theorem of_two_cut (incidence : KoalaTwoSectionPrice.TwoCutIncidence) :
    ProtocolClaim 6950 2892859073143766509 9223372036854774115 := by
  have hbank := HighCore82219BankProof.listed_ok .h2367 (HighCore82219.terminal .h2367)
    (Or.inl rfl)
  have hretained := KoalaRect.retained_of_price hbank (KoalaTwoSectionPrice.rect_price incidence)
  apply Front82200.of_core_counts_at_maximal_radius
  · intro _ _ M _ F lo hi
    exact Low48Geometry.count M F lo hi
  · intro _ _ M _ F lo hi
    exact HighCore82219.ordinary_high hretained M F lo hi

#print axioms of_two_cut
end KoalaSoundness6950
