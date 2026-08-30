import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A
section ProximityFlatProofPort
noncomputable section
universe v
variable {R α:Type*} [Small.{v} α] [CommSemiring R]
namespace Shrink
instance [Semiring α] [Algebra R α]:Algebra R (Shrink.{v} α):=(equivShrink α).symm.algebra _
variable (R α) in
@[simps!]
def algEquiv [Semiring α] [Algebra R α]:Shrink.{v} α ≃ₐ[R] α:=
 (equivShrink α).symm.algEquiv _
end Shrink
