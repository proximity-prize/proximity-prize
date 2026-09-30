import ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L00
import ProximityPrize.SubmissionLower.OwnerTreeCheck6815
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L01M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 1 3572 3749 55 12 258500000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3572 3749 55 12 258500000000000000 15 0xe006000f5000e0076005e0053005e071700f500190006000000000070005c00dc00e5079700110000012c01300797001100cd00000033000000dc005c00ac00e506970011000000dc0000003b000000bd00b8000000bd0697001100cd000000330717001900f50043000e006000f5000e005e00f5001900060000004c000000b8000000bd00ac0000003b000000bd0597001100cd0000003300ac000000ac0000003b000000bd00ac0000003b000000bd0497001100cd000000330517001900f50043061700000076004c0053007600ac00530717004c006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5006200190062025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd000002cf001100cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f0043000000d2004c006d001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L01M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L01M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 2 3572 3749 55 12 258500000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3572 3749 55 12 258500000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L01M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L01M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3 3572 3749 55 12 258500000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3572 3749 55 12 258500000000000000 7 0x2200360002123f000200c3005900000002005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L01M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L01M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 4 3572 3749 55 12 258500000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3572 3749 55 12 258500000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L01M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L01M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 5 3572 3749 55 12 258500000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3572 3749 55 12 258500000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L01M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L01M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 6 3572 3749 55 12 258500000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3572 3749 55 12 258500000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L01M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L01
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,177,3543,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3572 3749 55 12 258500000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L01M1.covered
  · exact OwnerBox6815_L01M2.covered
  · exact OwnerBox6815_L01M3.covered
  · exact OwnerBox6815_L01M4.covered
  · exact OwnerBox6815_L01M5.covered
  · exact OwnerBox6815_L01M6.covered
theorem linear : LinearChecks 12 39 258 3749 55 12 258500000000000000 := by decide +kernel
theorem high : Gates 3749 55 12 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3749 55 12/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3749 55 12≤258500000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 55 12) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3572≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3749 55 12) 258500000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3572 258500000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L01
