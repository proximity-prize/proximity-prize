import ProximityPrize.SubmissionLower.MergedInfra6815_47
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I00
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3599 3724 58 11 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3599 3724 58 11 271000000000000000 7 0x32b00a100020d6d000000000000128d0002012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3599 3724 58 11 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3724 58 11 1*38+coefficient 3724 58 11 2*136)/2) 3724 58 11≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3724 58 11 1*38+coefficient 3724 58 11 2*136)/3) 3724 58 11≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3724 58 11 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3724 58 11≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I00
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I01
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3347 3774 58 12 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3347 3774 58 12 271000000000000000 11 0x130d00000000130d032b0000000000000069130d00000000000015dd0000000015dd02ab006900000000000202ab0069130d032b00a1000000000add000003ab0000000003ab00d90002084d000000000a9d000002ab0000000002ab00d9000207cd032b000200a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d00000000159d01ab0000000200490002159d000201ab00690000000201ab00020069128d00040002159d000200690002128d012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3347 3774 58 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3774 58 12 1*38+coefficient 3774 58 12 2*136)/2) 3774 58 12≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3774 58 12 1*38+coefficient 3774 58 12 2*136)/3) 3774 58 12≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3774 58 12 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3774 58 12≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I01
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I02
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3294 3774 59 12 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3294 3774 59 12 271000000000000000 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab000000000049000015dd00000000000017450004026b0049000000000002026b004915dd02ab0069000000000000103d02ab00000000103d0000000000490000103d02ab0069130d032b00a1000000080008000003eb00f90add000000000000036b000000f90add03ab000000020add000000000add03ab00d90002084d000000020a9d000000020a9d02ab000000000a9d000000000a9d02ab00d9000207cd032b0000000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d90000000000000000000000c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d000000000f7d00d9016b128d00000000159d00000000000017250004016b0089000000040089159d01ab000000001725000401eb00040049000400020049159d000601ab0069000000000f7d000201ab00020069128d000400040089000400cb0006159d000200690002128d012b00a10000000009ad000201cb000200d9000206ed0002016b000200a10c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3294 3774 59 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3774 59 12 1*38+coefficient 3774 59 12 2*136)/2) 3774 59 12≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3774 59 12 1*38+coefficient 3774 59 12 2*136)/3) 3774 59 12≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3774 59 12 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3774 59 12≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I02
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I03
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3322 3699 55 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3322 3699 55 13 271000000000000000 11 0x130d00000000130d032b00000000130d000000000000000015dd02ab0069000000000069130d032b00a10000000003ab000000d90002084d0000000000d9000207cd032b000200a10d6d0000000000000000159d00d9016b00000000000000d9016b128d000000000000159d01ab0000000200490000159d000201ab00690002128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3322 3699 55 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3699 55 13 1*38+coefficient 3699 55 13 2*136)/2) 3699 55 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3699 55 13 1*38+coefficient 3699 55 13 2*136)/3) 3699 55 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3699 55 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3699 55 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I03
end MergedPart3
section MergedPart4
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
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I05
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3213 3456 57 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3213 3456 57 13 271000000000000000 8 0x32b00000000130d00000000130d032b00a100000002084d0000000207cd032b000200a10d6d00000000128d0000000200690002128d0002012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3213 3456 57 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3456 57 13 1*38+coefficient 3456 57 13 2*136)/2) 3456 57 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3456 57 13 1*38+coefficient 3456 57 13 2*136)/3) 3456 57 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3456 57 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3456 57 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I05
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I06
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3457 3699 57 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3457 3699 57 13 271000000000000000 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab0000000015dd0000000000001745000000041745026b0049000000000004026b004915dd02ab006900000000103d00000000103d02ab00000000103d0000000000490000103d02ab0069130d032b00a100000008000800000002099503eb00f90add000000080000036b0000000009950000036b00f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000020a9d000000000a9d02ab00d9000207cd032b000000000add000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d00000000000000c1010b00000f7d00d9016b128d0000000000000000172501eb00890000159d0000000000001725016b0000000017250004016b008900000000000014150004016b0089159d01ab000000001725000401eb00040049000000001415000401eb00020049159d000601ab0069000000000f7d00000000008900000f7d01ab00020069128d000400040089000400cb0006159d000200690002128d012b00a10000000209ad000201cb000200d9000206ed0002016b000200a10c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3457 3699 57 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3699 57 13 1*38+coefficient 3699 57 13 2*136)/2) 3699 57 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3699 57 13 1*38+coefficient 3699 57 13 2*136)/3) 3699 57 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3699 57 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3699 57 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I06
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I07
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3161 3378 58 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3161 3378 58 13 271000000000000000 8 0x32b00000000130d00000000130d032b00a100000002084d0002032b000200a10d6d00000000128d0000000200690000128d0002012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3161 3378 58 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3378 58 13 1*38+coefficient 3378 58 13 2*136)/2) 3378 58 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3378 58 13 1*38+coefficient 3378 58 13 2*136)/3) 3378 58 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3378 58 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3378 58 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I07
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I08
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3379 3543 58 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3379 3543 58 13 271000000000000000 11 0x130d00000000130d032b0000000000000069130d00000000000015dd0000000015dd02ab006900000000000202ab0069130d032b00a1000000000add000000000add03ab000000000add000003ab00d90002084d000000000a9d000002ab0000000002ab00d9000207cd032b0000000003ab0002084d000200690002032b00a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d0000000000890000159d01ab0000000200490002159d000201ab00690000000201ab00020069128d00040002159d000200690002128d012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3379 3543 58 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3543 58 13 1*38+coefficient 3543 58 13 2*136)/2) 3543 58 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3543 58 13 1*38+coefficient 3543 58 13 2*136)/3) 3543 58 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3543 58 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3543 58 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I08
end MergedPart8
section MergedPart9
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
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I10
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3561 3618 58 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3561 3618 58 13 271000000000000000 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab0000000015dd0000000000001745000000001745026b0049000000000004026b004915dd02ab0069000000000000103d02ab00000000103d00000000103d02ab0069130d032b00a1000000080008000003eb00f90add000000000000036b000000f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000000a9d000000000a9d02ab00d9000207cd032b0000000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d000000000f7d00d9016b128d00000000159d00000000000017250004016b0089000000000002016b0089159d01ab000000001725000401eb000400490000000201eb00020049159d000601ab0069000000000f7d000201ab00020069128d000400040089000400cb0006159d000200690002128d012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3561 3618 58 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3618 58 13 1*38+coefficient 3618 58 13 2*136)/2) 3618 58 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3618 58 13 1*38+coefficient 3618 58 13 2*136)/3) 3618 58 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3618 58 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3618 58 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I10
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I11
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 3619 3680 58 13 273041644927340992
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3619 3680 58 13 273041644927340992 13 0xd9130d00000000000000000000103d02ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab0000000000000000174502eb0049000015dd0000000000001745026b000000001745000000041745026b004900000000000014750004026b004915dd02ab006900000000103d00000000103d02ab00000000103d0000000000490000103d02ab0069130d032b00a100000008000800000002099503eb00f90add00000008000000000995036b0000000009950000036b00f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000020a9d000000000a9d02ab00d9000207cd032b000000000add000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d00000000000000c1010b00020f7d00d9016b128d0000000000000000172501eb0089000000000089159d0000000000001725016b0000000017250004016b008900000000000014150004016b0089159d01ab00000000172500000004172501eb00060049000000001415000401eb00020049159d000601ab0069000000000f7d00000002008900000f7d01ab00020069128d000400040089000400cb0006159d000200690002128d012b00a10000000209ad000201cb000200d9000206ed0002016b000200a10c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3619 3680 58 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3680 58 13 1*38+coefficient 3680 58 13 2*136)/2) 3680 58 13≤273041644927340992 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3680 58 13 1*38+coefficient 3680 58 13 2*136)/3) 3680 58 13≤273041644927340992 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3680 58 13 273041644927340992 := by decide +kernel
theorem identity : identityPrice 3680 58 13≤273041644927340992 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I11
end MergedPart11
section MergedPart12
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I12
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,175,3680,6,8⟩
def valid : Box → Prop := Valid fixed 3681 3684 58 13 273200000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3681 3684 58 13 273200000000000000 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab00000000000002eb0049000015dd0000000000001745026b000000001745000000041745026b004900000000000014750004026b004915dd02ab006900000000103d00000000103d02ab00000000103d0000000000490000103d02ab0069130d032b00a100000008000800000002099503eb00f90add00000008000000000995036b0000000009950000036b00f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000020a9d000000000a9d02ab00d9000207cd032b000000000add000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d00000000000000c1010b00020f7d00d9016b128d0000000000000000172501eb0089000000000089159d0000000000001725016b0000000017250004016b008900000000000014150004016b0089159d01ab00000000172500000004172501eb00060049000000001415000401eb00020049159d000601ab0069000000000f7d00000002008900000f7d01ab00020069128d000400040089000400cb0006159d000200690002128d012b00a10000000209ad000201cb000200d9000206ed0002016b000200a10c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3681 3684 58 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3684 58 13 1*38+coefficient 3684 58 13 2*136)/2) 3684 58 13≤273200000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3684 58 13 1*38+coefficient 3684 58 13 2*136)/3) 3684 58 13≤273200000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3684 58 13 273200000000000000 := by decide +kernel
theorem identity : identityPrice 3684 58 13≤273200000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I12
end MergedPart12
section MergedPart13
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I13
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨42,136,2306,4,5⟩
def valid : Box → Prop := Valid fixed 3106 3146 59 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3106 3146 59 13 271000000000000000 8 0x130d00000000130d032b00a100000002084d0002032b000200a10d6d00000000128d0000000000690000128d0002012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3106 3146 59 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3146 59 13 1*38+coefficient 3146 59 13 2*136)/2) 3146 59 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3146 59 13 1*38+coefficient 3146 59 13 2*136)/3) 3146 59 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3146 59 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3146 59 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I13
end MergedPart13
section MergedPart14
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I14
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3147 3378 59 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3147 3378 59 13 271000000000000000 10 0x130d032b00000000130d000000000069000000000069130d032b00a10000000000d90002084d0000000000d9000207cd032b000200a10d6d00000000000000d9016b00000000000000d9016b128d0000000001ab00000000159d000201ab00690002128d0002012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3147 3378 59 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3378 59 13 1*38+coefficient 3378 59 13 2*136)/2) 3378 59 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3378 59 13 1*38+coefficient 3378 59 13 2*136)/3) 3378 59 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3378 59 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3378 59 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I14
end MergedPart14
section MergedPart15
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I15
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3379 3543 59 13 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3379 3543 59 13 271000000000000000 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab0000000015dd00000000000017450004026b0049000000000002026b004915dd02ab0069000000000000103d02ab00000000103d00000000103d02ab0069130d032b00a100000008000800000000099503eb00f90add000000000000036b000000f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000000a9d000000000a9d02ab00d9000207cd032b0000000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d000000000f7d00d9016b128d00000000159d00000000000017250004016b0089000000000002016b0089159d01ab000000001725000401eb000400490000000201eb00020049159d000601ab0069000000000f7d000201ab00020069128d000400040089000400cb0006159d000200690002128d012b00a10000000009ad000201cb000200d9000206ed0002016b000200a10c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3379 3543 59 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3543 59 13 1*38+coefficient 3543 59 13 2*136)/2) 3543 59 13≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3543 59 13 1*38+coefficient 3543 59 13 2*136)/3) 3543 59 13≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3543 59 13 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3543 59 13≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I15
end MergedPart15
section MergedPart16
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I16
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3544 3560 59 13 271115740514048768
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3544 3560 59 13 271115740514048768 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab0000000015dd0000000000001745000000041745026b0049000000000004026b004915dd02ab006900000000103d00000000103d02ab00000000103d0000000000490000103d02ab0069130d032b00a100000008000800000000099503eb00f90add000000080000036b000200f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000000a9d000000000a9d02ab00d9000207cd032b000000000add000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d00000000010b00000f7d00d9016b128d00000000000001eb00890000159d0000000000001725016b0000000017250004016b0089000000000002016b0089159d01ab000000001725000401eb000400490000000201eb00020049159d000601ab0069000000000f7d00000000008900000f7d01ab00020069128d000400040089000400cb0006159d000200690002128d012b00a10000000009ad000201cb000200d9000206ed0002016b000200a10c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3544 3560 59 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3560 59 13 1*38+coefficient 3560 59 13 2*136)/2) 3560 59 13≤271115740514048768 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3560 59 13 1*38+coefficient 3560 59 13 2*136)/3) 3560 59 13≤271115740514048768 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3560 59 13 271115740514048768 := by decide +kernel
theorem identity : identityPrice 3560 59 13≤271115740514048768 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I16
end MergedPart16
section MergedPart17
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I17
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3561 3599 59 13 272690523638300300
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3561 3599 59 13 272690523638300300 13 0xd9130d000000000000000002ab00d9130d032b000000000000000015dd03ab00690000000003ab000000000000103d03ab0069130d00000000000015dd02ab0000000000000000174502eb0049000015dd0000000000001745026b000000001745000000041745026b004900000000000014750004026b004915dd02ab006900000000103d00000000103d02ab00000000103d0000000000490000103d02ab0069130d032b00a100000008000800000002099503eb00f90add00000008000000000995036b0000000009950000036b00f90add03ab000000020add000000020add03ab00d90002084d000000020a9d000000020a9d02ab000000020a9d000000000a9d02ab00d9000207cd032b000000000add000000000add03ab0002084d000200690002032b00a10d6d000000000000159d00d900000000159d00000000000000000000141500c1010b159d00d9016b000000000f7d000000000f7d00d9000000000f7d00000000000000c1010b00000f7d00d9016b128d0000000000000000172501eb0089000000000089159d0000000000001725016b0000000017250004016b008900000000000014150004016b0089159d01ab00000000172500000004172501eb00060049000000001415000401eb00020049159d000601ab0069000000000f7d00000000008900000f7d01ab00020069128d000400040089000400cb0006159d000200690002128d012b00a10000000209ad000201cb000200d9000206ed0002016b000200a10c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3561 3599 59 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3599 59 13 1*38+coefficient 3599 59 13 2*136)/2) 3599 59 13≤272690523638300300 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3599 59 13 1*38+coefficient 3599 59 13 2*136)/3) 3599 59 13≤272690523638300300 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3599 59 13 272690523638300300 := by decide +kernel
theorem identity : identityPrice 3599 59 13≤272690523638300300 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I17
end MergedPart17
