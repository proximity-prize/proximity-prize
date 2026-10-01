import ProximityPrize.SubmissionLower.MergedInfra6815_47
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L00
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3394 3571 55 12 248630000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3394 3571 55 12 248630000000000000 11 0x130d00000000130d032b0000000000000069130d000000000000000015dd02ab0069000000000069130d032b00a10000000003ab000000d90002084d0000000000d9000207cd032b000200a10d6d0000000000000000159d00d9016b00000000000000d9016b128d000000000000159d01ab0000000200490000159d000201ab00690002128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3394 3571 55 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3571 55 12 1*38+coefficient 3571 55 12 2*136)/2) 3571 55 12≤248630000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3571 55 12 1*38+coefficient 3571 55 12 2*136)/3) 3571 55 12≤248630000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3571 55 12 248630000000000000 := by decide +kernel
theorem identity : identityPrice 3571 55 12≤248630000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L00
end MergedPart0
section MergedPart1
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
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L02
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3338 3543 56 12 245390000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3338 3543 56 12 245390000000000000 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab0000000015dd00000000000017450004026b0049000000000002026b004915dd02ab006900000000103d00000000103d02ab00000000103d0000000000490000103d02ab0069130d032b00a100000008000800000000099503eb00f90add000000000000036b000200f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000000a9d000000000a9d02ab00d9000207cd032b0000000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d00000000010b00000f7d00d9016b128d0000000000890000159d0000000000001725016b0000000017250004016b0089000000000002016b0089159d01ab000000001725000401eb000400490000000201eb00020049159d000601ab0069000000000f7d000201ab00020069128d000400040089000400cb0006159d000200690002128d012b00a10000000009ad000201cb000200d9000206ed0002016b000200a10c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3338 3543 56 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3543 56 12 1*38+coefficient 3543 56 12 2*136)/2) 3543 56 12≤245390000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3543 56 12 1*38+coefficient 3543 56 12 2*136)/3) 3543 56 12≤245390000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3543 56 12 245390000000000000 := by decide +kernel
theorem identity : identityPrice 3543 56 12≤245390000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L02
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L03
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3544 3749 56 12 260000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3544 3749 56 12 260000000000000000 11 0x130d00000000130d032b0000000000000069130d000000000000000015dd02ab006900000000000002ab0069130d032b00a1000000000add000003ab0000000003ab00d90002084d0000000002ab0000000002ab00d9000207cd032b000200a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d00000000159d01ab0000000200490002159d000201ab00690000000001ab00020069128d00000002159d000200690002128d012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3544 3749 56 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3749 56 12 1*38+coefficient 3749 56 12 2*136)/2) 3749 56 12≤260000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3749 56 12 1*38+coefficient 3749 56 12 2*136)/3) 3749 56 12≤260000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3749 56 12 260000000000000000 := by decide +kernel
theorem identity : identityPrice 3749 56 12≤260000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L03
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L04
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3283 3399 57 12 246230000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3283 3399 57 12 246230000000000000 11 0x130d00000000130d032b0000000000000069130d000000000000000015dd02ab006900000000000002ab0069130d032b00a1000000000add000003ab0000000003ab00d90002084d0000000002ab0000000002ab00d9000207cd032b000200a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d00000000159d01ab0000000200490002159d000201ab00690000000001ab00020069128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3283 3399 57 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3399 57 12 1*38+coefficient 3399 57 12 2*136)/2) 3399 57 12≤246230000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3399 57 12 1*38+coefficient 3399 57 12 2*136)/3) 3399 57 12≤246230000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3399 57 12 246230000000000000 := by decide +kernel
theorem identity : identityPrice 3399 57 12≤246230000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L04
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L05
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3400 3516 57 12 257680000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3400 3516 57 12 257680000000000000 8 0x130d032b00000000130d00000000130d032b00a100000002084d0000000207cd032b000200a10d6d000000000000016b128d0000000200690002128d0002012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3400 3516 57 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3516 57 12 1*38+coefficient 3516 57 12 2*136)/2) 3516 57 12≤257680000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3516 57 12 1*38+coefficient 3516 57 12 2*136)/3) 3516 57 12≤257680000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3516 57 12 257680000000000000 := by decide +kernel
theorem identity : identityPrice 3516 57 12≤257680000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L05
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L06
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3517 3749 57 12 263340000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3517 3749 57 12 263340000000000000 12 0x130d00000000000000d9130d032b00000000006900000000000003ab0069130d00000000000015dd000000000049000015dd02ab006900000000000202ab0069130d032b00a100000000000000f90add000000000add03ab000000000add000003ab00d90002084d000000000a9d000000000a9d02ab000000000a9d000002ab00d9000207cd032b0000000003ab0002084d000200690002032b00a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d000000000004016b00890000159d01ab0000000401eb000200490002159d000201ab00690000000201ab00020069128d00040002159d000200690002128d012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3517 3749 57 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3749 57 12 1*38+coefficient 3749 57 12 2*136)/2) 3749 57 12≤263340000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3749 57 12 1*38+coefficient 3749 57 12 2*136)/3) 3749 57 12≤263340000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3749 57 12 263340000000000000 := by decide +kernel
theorem identity : identityPrice 3749 57 12≤263340000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L06
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L07
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3318 3533 53 13 245800000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3318 3533 53 13 245800000000000000 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab0000000015dd0000000000001745000000001745026b0049000000000004026b004915dd02ab006900000000103d00000000103d02ab00000000103d00000000103d02ab0069130d032b00a1000000080008000803eb00f90add000000080000036b00000000036b00f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000020a9d000000000a9d02ab00d9000207cd032b000000000add000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d00000000000000c1010b00000f7d00d9016b128d0000000000000000172501eb00890000159d0000000000001725016b0000000017250004016b0089000000040002016b0089159d01ab000000001725000401eb000400490000000401eb00020049159d000601ab0069000000000f7d000201ab00020069128d00040006159d000200690002128d012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3318 3533 53 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3533 53 13 1*38+coefficient 3533 53 13 2*136)/2) 3533 53 13≤245800000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3533 53 13 1*38+coefficient 3533 53 13 2*136)/3) 3533 53 13≤245800000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3533 53 13 245800000000000000 := by decide +kernel
theorem identity : identityPrice 3533 53 13≤245800000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L07
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L08
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3534 3749 53 13 256910000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3534 3749 53 13 256910000000000000 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab0000000015dd0000000000001745000000001745026b0049000000000004026b004915dd02ab006900000000103d00000000103d02ab00000000103d00000000103d02ab0069130d032b00a100000008000800000000099503eb00f90add000000080000036b00000000036b00f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000020a9d000000000a9d02ab00d9000207cd032b000000000add000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d00000000000000c1010b00000f7d00d9016b128d0000000000000000172501eb00890000159d0000000000001725016b0000000017250004016b0089000000040002016b0089159d01ab000000001725000401eb000600490000000401eb00020049159d000601ab0069000000000f7d000201ab00020069128d00040006159d000200690002128d012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3534 3749 53 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3749 53 13 1*38+coefficient 3749 53 13 2*136)/2) 3749 53 13≤256910000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3749 53 13 1*38+coefficient 3749 53 13 2*136)/3) 3749 53 13≤256910000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3749 53 13 256910000000000000 := by decide +kernel
theorem identity : identityPrice 3749 53 13≤256910000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L08
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L09
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3261 3383 54 13 246600000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3261 3383 54 13 246600000000000000 11 0x130d00000000130d032b0000000000000069130d000000000000000015dd02ab006900000000000002ab0069130d032b00a10008000003ab0000000003ab00d90002084d0000000002ab0000000002ab00d9000207cd032b0000000003ab0002084d000200690002032b00a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d00000000159d01ab0000000200490000159d000201ab00690000000001ab00020069128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3261 3383 54 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3383 54 13 1*38+coefficient 3383 54 13 2*136)/2) 3383 54 13≤246600000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3383 54 13 1*38+coefficient 3383 54 13 2*136)/3) 3383 54 13≤246600000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3383 54 13 246600000000000000 := by decide +kernel
theorem identity : identityPrice 3383 54 13≤246600000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L09
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L10
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3384 3505 54 13 252660000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3384 3505 54 13 252660000000000000 11 0x130d00000000130d032b0000000000000069130d000000000000000015dd02ab006900000000000002ab0069130d032b00a1000000000add000003ab0000000003ab00d90002084d0000000002ab0000000002ab00d9000207cd032b0000000003ab0002084d000200690002032b00a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d00000000159d01ab0000000200490000159d000201ab00690000000001ab00020069128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3384 3505 54 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3505 54 13 1*38+coefficient 3505 54 13 2*136)/2) 3505 54 13≤252660000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3505 54 13 1*38+coefficient 3505 54 13 2*136)/3) 3505 54 13≤252660000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3505 54 13 252660000000000000 := by decide +kernel
theorem identity : identityPrice 3505 54 13≤252660000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L10
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L11
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3506 3627 54 13 259580000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3506 3627 54 13 259580000000000000 11 0x130d00000000130d032b0000000000000069130d000000000000000015dd02ab006900000000000002ab0069130d032b00a1000000000add000003ab0000000003ab00d90002084d0000000002ab0000000002ab00d9000207cd032b0000000003ab0002084d000200690002032b00a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d00000000159d01ab0000000200490000159d000201ab00690000000001ab00020069128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3506 3627 54 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3627 54 13 1*38+coefficient 3627 54 13 2*136)/2) 3627 54 13≤259580000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3627 54 13 1*38+coefficient 3627 54 13 2*136)/3) 3627 54 13≤259580000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3627 54 13 259580000000000000 := by decide +kernel
theorem identity : identityPrice 3627 54 13≤259580000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L11
end MergedPart11
section MergedPart12
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L12
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 3628 3749 54 13 265790000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3628 3749 54 13 265790000000000000 11 0x130d00000000130d032b0000000000000069130d000000000000000015dd02ab006900000000000002ab0069130d032b00a1000000000add000003ab0000000003ab00d90002084d0000000002ab0000000002ab00d9000207cd032b0000000003ab0002084d000200690002032b00a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d00000000159d01ab0000000200490000159d000201ab00690000000001ab00020069128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3628 3749 54 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3749 54 13 1*38+coefficient 3749 54 13 2*136)/2) 3749 54 13≤265790000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3749 54 13 1*38+coefficient 3749 54 13 2*136)/3) 3749 54 13≤265790000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3749 54 13 265790000000000000 := by decide +kernel
theorem identity : identityPrice 3749 54 13≤265790000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L12
end MergedPart12
