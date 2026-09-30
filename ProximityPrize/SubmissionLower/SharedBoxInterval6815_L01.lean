import ProximityPrize.SubmissionLower.SharedBoxInterval6815_L00
import ProximityPrize.SubmissionLower.SharedTreeCheck6815
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L01
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3572 3749 55 12 258500000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3572 3749 55 12 258500000000000000 11 0x130d00000000130d032b00000000130d000000000000000015dd02ab0069000000000069130d032b00a10000000000d90002084d0000000000d9000207cd032b000200a10d6d00000000000000d9016b00000000000000d9016b128d000000000000159d01ab0000000000490000159d000201ab00690002128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3572 3749 55 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3749 55 12 1*38+coefficient 3749 55 12 2*136)/2) 3749 55 12≤258500000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3749 55 12 1*38+coefficient 3749 55 12 2*136)/3) 3749 55 12≤258500000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3749 55 12 258500000000000000 := by decide +kernel
theorem identity : identityPrice 3749 55 12≤258500000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L01
