import ProximityPrize.SubmissionLower.KoalaH2430PrefixProduction
import ProximityPrize.SubmissionLower.Pr657Weighted6955At2429
import ProximityPrize.SubmissionLower.KoalaAnchor2428Transport
import ProximityPrize.SubmissionLower.H2429Minimum

set_option Elab.async false
set_option autoImplicit false

namespace ProximityPrize.Benchmark

/- The weighted low and high h2367 geometry adapt public PR657 at
e07f14a81dfe2cf1bda985e67040ad4d31fe81ab. -/
theorem candidate : ProtocolClaim 6955 336973823 1073741824 := by
  apply Front6955On6960.of_bands _ (KoalaH2430.singleton KoalaH2430.prefix_geometry)
    Pr657High6955.count
  intro u del M Γ F lo hi
  by_cases small : M.overhead ≤ 2428
  · exact Pr657Weighted6955At2429.count M F lo hi (KoalaAnchor2428Transport.anchor M F small)
  · have height : M.overhead = 2429 := by omega
    by_cases room : 2430 ≤ M.E.natDegree
    · exact KoalaH2430.effective_singleton KoalaH2430.prefix_geometry M F (hi.trans (by decide)) room
    · have pole : M.E.natDegree = 2429 := by
        change (M.E.natDegree : ℤ) - M.factor.natDegree -
          P1.amplitudeDegree M.A₀ M.A₁ = 2429 at height
        omega
      exact H2429Minimum.count M F height pole

#print axioms candidate
end ProximityPrize.Benchmark
