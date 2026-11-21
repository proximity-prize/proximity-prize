import ProximityPrize.SubmissionLower.FrontAssembly82200
import ProximityPrize.SubmissionLower.Low48GeometryFinish
import ProximityPrize.SubmissionLower.HighCore82209Finish
import ProximityPrize.SubmissionLower.KoalaDiagonalCount

set_option Elab.async false

namespace KoalaSoundness6949
open ProximityPrize.Benchmark

theorem of_incidence (incidence : KoalaDiagonalPrice.RawIncidence) :
    ProtocolClaim 6949 2892507229422860772 9223372036854718577 := by
  have hbank := HighCore82209BankProof.listed_ok .h2367 (HighCore82209.terminal .h2367)
    (Or.inl rfl)
  have hretained := KoalaRect.retained_of_price hbank (KoalaDiagonalPrice.rect_price incidence)
  apply Front82200.of_core_counts_at_maximal_radius
  · intro _ _ M _ F lo hi
    exact Low48Geometry.count M F lo hi
  · intro _ _ M _ F lo hi
    exact (HighCore82209.ordinary_high hretained M F lo hi).trans (by decide)

#print axioms of_incidence
end KoalaSoundness6949
