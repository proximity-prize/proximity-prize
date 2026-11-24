import ProximityPrize.SubmissionLower.Low48BentVolume
import ProximityPrize.SubmissionLower.Low48Price

set_option autoImplicit false

namespace Low48BentVolume
open Low48BentVolume (coeff5)
theorem cast_price_integral (a : Low48BentLattice.Cap) :
    (Low48Price.bentIntegral a.1.b a.1.j a.1.t a.2 : ℚ) =
      bentIntegral a.1.b a.1.j a.1.t a.2 := by
  unfold Low48Price.bentIntegral bentIntegral coeff5
  push_cast
  ring
end Low48BentVolume
