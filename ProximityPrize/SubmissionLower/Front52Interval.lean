import ProximityPrize.SubmissionLower.FrontIntermediateProtocol
import ProximityPrize.SubmissionLower.High52Finish
import ProximityPrize.SubmissionLower.Low52At2390GeoCount

set_option Elab.async false
namespace Front52Interval
open ProximityPrize.Benchmark

/-- The low and high counts leave the closed interval from 2391 to 2451. -/
theorem of_interval
    (middle : ∀ u del (M : P1.ModelAt 33463 u del) Γ, P1.FamilyAt 179905 M Γ →
      2391 ≤ M.overhead → M.overhead ≤ 2451 → Γ.card ≤ FrontIntermediate.coreBudget) :
    ProtocolClaim 6952 2893562760585543664 9223372036854775757 := by
  apply FrontIntermediate.of_core_count .s52
  intro u del M Γ F lo hi
  by_cases low : M.overhead ≤ 2390
  · exact Low52At2390Geo.ordinary_count M F lo low
  by_cases high : 2452 ≤ M.overhead
  · exact (High52.ordinary_high M F high hi).trans (by decide)
  · have hl : 2391 ≤ M.overhead := by omega
    have hu : M.overhead ≤ 2451 := by omega
    exact middle u del M Γ F hl hu

#print axioms of_interval
end Front52Interval
