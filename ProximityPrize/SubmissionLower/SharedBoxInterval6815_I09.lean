import ProximityPrize.SubmissionLower.SharedBoxInterval6815_I08
import ProximityPrize.SubmissionLower.SharedTreeCheck6815
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I09
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3544 3560 58 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3544 3560 58 13 271000000000000000 12 0x130d00000000000000d9130d032b000000000000000003ab0069130d00000000000015dd0000000015dd02ab006900000000000202ab0069130d032b00a1000000000add000000000add03ab000000000add000003ab00d90002084d000000000a9d000000000a9d02ab0000000002ab00d9000207cd032b0000000003ab0002084d000200690002032b00a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d000000000004016b00890000159d01ab0000000200490002159d000201ab00690000000201ab00020069128d00040002159d000200690002128d012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3544 3560 58 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3560 58 13 1*38+coefficient 3560 58 13 2*136)/2) 3560 58 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3560 58 13 1*38+coefficient 3560 58 13 2*136)/3) 3560 58 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3560 58 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3560 58 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I09
