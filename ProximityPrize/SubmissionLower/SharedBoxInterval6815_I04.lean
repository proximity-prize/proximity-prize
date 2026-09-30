import ProximityPrize.SubmissionLower.SharedBoxInterval6815_I03
import ProximityPrize.SubmissionLower.SharedTreeCheck6815
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I04
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3266 3699 56 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3266 3699 56 13 271000000000000000 12 0x130d00000000000000d9130d032b00000000006900000000000003ab0069130d00000000000015dd000000000004026b0049000015dd02ab00690000000002ab00000000103d00000000103d02ab0069130d032b00a100000000000000f90add000000000add03ab000000000add000000000add03ab00d90002084d000000000a9d000000000a9d02ab000000000a9d000202ab00d9000207cd032b0000000003ab0002084d000200690002032b00a10d6d0000000000d9000000000000159d00d9016b0000000000000f7d00d90000000000000f7d00d9016b128d00000000159d000000000004016b00890000159d01ab0000000401eb00040049000000020049159d000601ab0069000000000f7d000201ab00020069128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3266 3699 56 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3699 56 13 1*38+coefficient 3699 56 13 2*136)/2) 3699 56 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3699 56 13 1*38+coefficient 3699 56 13 2*136)/3) 3699 56 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3699 56 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3699 56 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I04
