import ProximityPrize.SubmissionLower.MergedInfra6815_47
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L00M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 1 3394 3571 55 12 248630000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3394 3571 55 12 248630000000000000 15 0xe006000f5000e0076005e0053005e071700f500190006000000000070005c00dc00e5079700110000012c01300797001100cd00000033000000dc005c00ac00e506970011000000dc0000003b000000bd00b8000000bd0697001100cd000000330717001900f50043000e006000f5000e005e00f50019000600000000004c0011000000b8000000bd00ac0000003b000000bd0597001100cd0000003300ac000000ac0000003b000000bd00000497001100cd000000330517001900f50043061700000076004c0053007600ac00530717007800000053004c0717006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f500190062025f0006000000ac000000cd00ac000000cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f00430000007600d4005300d20317004c006d001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L00M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L00M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 2 3394 3571 55 12 248630000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3394 3571 55 12 248630000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L00M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L00M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3 3394 3571 55 12 248630000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3394 3571 55 12 248630000000000000 7 0x2200360002123f000200c3005900000002005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L00M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L00M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 4 3394 3571 55 12 248630000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3394 3571 55 12 248630000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L00M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L00M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 5 3394 3571 55 12 248630000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3394 3571 55 12 248630000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L00M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L00M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 6 3394 3571 55 12 248630000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3394 3571 55 12 248630000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L00M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L00
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨46,153,3378,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3394 3571 55 12 248630000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L00M1.covered
  · exact OwnerBox6815_L00M2.covered
  · exact OwnerBox6815_L00M3.covered
  · exact OwnerBox6815_L00M4.covered
  · exact OwnerBox6815_L00M5.covered
  · exact OwnerBox6815_L00M6.covered
theorem linear : LinearChecks 12 39 258 3571 55 12 248630000000000000 := by decide +kernel
theorem high : Gates 3571 55 12 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3571 55 12/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3571 55 12≤248630000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3571 55 12) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3394≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3571 55 12) 248630000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3394 248630000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L00
end MergedPart0
section MergedPart1
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
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L02M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3338 3543 56 12 245390000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3338 3543 56 12 245390000000000000 17 0xe007800000053007800000053071700f5000e0076005c000e000a005c004b00e50052005a00e5079700110060005a006000bd005a006000bd0797001100cd00530076005c005a00110060005e001100cd0053071700f50019000600000000005c007000e5005c006000dc003b00e507970011000000dc0000003b012000bd00dc0000003b012c00ac013000b507570000003b00bd0797001100cd00ac000000cd00330000005c005000dc003b00e5005c005000ac003b00e506970011000000dc0000003b00ac009800b500a406d70000003b00bd00ac0000003b00980000003b00bd0697001100cd00ac000000cd00330717001900f50043000e0078000000530060051700f5000e0076005a005e00cd00530076005e0053051700f50019000600000000005c005000ac003b00e5005c004c00e505970011000000ac0000003b00a40000003b00bd00ac0000003b00a40000003b00bd0597001100cd00ac000000cd00330000005c00ac00e5005c00ac00e504970011000000ac0000003b00ec0000003b00bd00ac0000003b000000bd0497001100cd000000330517001900f5004306170000007600000064004c008d006400ac008d07970011005300760000006400ac008d006400ac008d06970011005307170078000000530078000000530717006d001900000043000000760000004c00110053007600d400530517007800000053004c0517006d001900000043061700a5000e006400f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f00060000000000ac0011000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00000033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L02M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L02M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3338 3543 56 12 245390000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3338 3543 56 12 245390000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L02M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L02M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3338 3543 56 12 245390000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3338 3543 56 12 245390000000000000 12 0x880038034d00860072034d0071003a153f003800fb003802dd0022123f00860072034d0036153f003600fb00860072034d0036153f003600fb00410072003800fb0036004102dd0036000202dd123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L02M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L02M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3338 3543 56 12 245390000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3338 3543 56 12 245390000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L02M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L02M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3338 3543 56 12 245390000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3338 3543 56 12 245390000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L02M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L02M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3338 3543 56 12 245390000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3338 3543 56 12 245390000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L02M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L02
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3338 3543 56 12 245390000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L02M1.covered
  · exact OwnerBox6815_L02M2.covered
  · exact OwnerBox6815_L02M3.covered
  · exact OwnerBox6815_L02M4.covered
  · exact OwnerBox6815_L02M5.covered
  · exact OwnerBox6815_L02M6.covered
theorem linear : LinearChecks 12 39 258 3543 56 12 245390000000000000 := by decide +kernel
theorem high : Gates 3543 56 12 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3543 56 12/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3543 56 12≤245390000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3543 56 12) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3338≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3543 56 12) 245390000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3338 245390000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L02
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L03M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 1 3544 3749 56 12 260000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3544 3749 56 12 260000000000000000 15 0xe0078000000530060071700f5000e0076005a005e00cd00530076005e0053071700f500190006000000000070005c00dc00e5079700110000012c00dc0000003b013000bd0797001100cd00ac000000cd00330000005c00dc00e5005c00ac00e506970011000000dc0000003b00980000003b00bd00ac0000003b00980000003b00bd0697001100cd00ac000000cd00330717001900f50043000e006000f5000e005e00f50019000600000000005c00ac00e5005c00ac00e505970011000000b800ec0000003b00bd00ac0000003b00ec0000003b00bd0597001100cd00000033004c000000ac0000003b000000bd00ac0000003b000000bd0497001100cd000000330517001900f5004306170000007600000064012c008d004c0797001100530076004c005307170078000000530078000000530717006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f500190062025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00000033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d4005300d20317004c006d001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L03M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L03M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 2 3544 3749 56 12 260000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3544 3749 56 12 260000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L03M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L03M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3 3544 3749 56 12 260000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3544 3749 56 12 260000000000000000 7 0x2200360002123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L03M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L03M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 4 3544 3749 56 12 260000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3544 3749 56 12 260000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L03M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L03M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 5 3544 3749 56 12 260000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3544 3749 56 12 260000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L03M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L03M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 6 3544 3749 56 12 260000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3544 3749 56 12 260000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L03M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L03
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,177,3543,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3544 3749 56 12 260000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L03M1.covered
  · exact OwnerBox6815_L03M2.covered
  · exact OwnerBox6815_L03M3.covered
  · exact OwnerBox6815_L03M4.covered
  · exact OwnerBox6815_L03M5.covered
  · exact OwnerBox6815_L03M6.covered
theorem linear : LinearChecks 12 39 258 3749 56 12 260000000000000000 := by decide +kernel
theorem high : Gates 3749 56 12 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3749 56 12/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3749 56 12≤260000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 56 12) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3544≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3749 56 12) 260000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3544 260000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L03
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L04M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3283 3399 57 12 246230000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3283 3399 57 12 246230000000000000 15 0xe0078000000530060071700f5000e0076005a005e00cd00530076005e0053071700f500190006000000000070005c00dc00e5079700110000012c00dc0000003b000000bd0797001100cd00000033000000dc005c00ac00e506970011000000dc0000003b000000bd00ac0000003b000000bd0697001100cd000000330717001900f50043000e006000f5000e005e00f50019000600000000004c0011000000cd0000003300ac000000cd000000330517001900f500430617000000760000004c001100530076004c00530717007800000053004c0717006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f500190062025f0006000000ac000000cd00ac000000cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f00430000007600d4005300d20317004c006d001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L04M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L04M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3283 3399 57 12 246230000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3283 3399 57 12 246230000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L04M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L04M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3283 3399 57 12 246230000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3283 3399 57 12 246230000000000000 7 0x2200360002123f003a0002123f00c300590000003a0002123f000000c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L04M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L04M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3283 3399 57 12 246230000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3283 3399 57 12 246230000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L04M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L04M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3283 3399 57 12 246230000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3283 3399 57 12 246230000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L04M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L04M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3283 3399 57 12 246230000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3283 3399 57 12 246230000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L04M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L04
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3283 3399 57 12 246230000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L04M1.covered
  · exact OwnerBox6815_L04M2.covered
  · exact OwnerBox6815_L04M3.covered
  · exact OwnerBox6815_L04M4.covered
  · exact OwnerBox6815_L04M5.covered
  · exact OwnerBox6815_L04M6.covered
theorem linear : LinearChecks 12 39 258 3399 57 12 246230000000000000 := by decide +kernel
theorem high : Gates 3399 57 12 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3399 57 12/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3399 57 12≤246230000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3399 57 12) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3283≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3399 57 12) 246230000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3283 246230000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L04
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L05M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 1 3400 3516 57 12 257680000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3400 3516 57 12 257680000000000000 11 0xe006000f5000e005e00f500190006000000dc000000cd0000003300ac000000cd000000330717001900f50043005e0006000000ac000000cd0000003300ac000000cd000000330517001900f5004306170000007600ac0053007600ac00530717004c006d0019000000430000007600ac005300d20517004c006d001900000043061700a500620006000000ac000000cd00ac000000cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f0043004a00000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L05M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L05M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 2 3400 3516 57 12 257680000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3400 3516 57 12 257680000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L05M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L05M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3 3400 3516 57 12 257680000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3400 3516 57 12 257680000000000000 7 0x2200360002123f000200c30059000201f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L05M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L05M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 4 3400 3516 57 12 257680000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3400 3516 57 12 257680000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L05M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L05M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 5 3400 3516 57 12 257680000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3400 3516 57 12 257680000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L05M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L05M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 6 3400 3516 57 12 257680000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3400 3516 57 12 257680000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L05M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L05
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨46,153,3378,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3400 3516 57 12 257680000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L05M1.covered
  · exact OwnerBox6815_L05M2.covered
  · exact OwnerBox6815_L05M3.covered
  · exact OwnerBox6815_L05M4.covered
  · exact OwnerBox6815_L05M5.covered
  · exact OwnerBox6815_L05M6.covered
theorem linear : LinearChecks 12 39 258 3516 57 12 257680000000000000 := by decide +kernel
theorem high : Gates 3516 57 12 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3516 57 12/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3516 57 12≤257680000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3516 57 12) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3400≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3516 57 12) 257680000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3400 257680000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L05
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L06M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 1 3517 3749 57 12 263340000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3517 3749 57 12 263340000000000000 15 0xe0078000000530060071700f5000e0076005a005e00cd00530076005e0053071700f500190006000000000070005c00dc00e507970011000000dc0000003b012c00bd00dc0000003b013000bd0797001100cd00ac000000cd00330000005c00dc00e5005c004c00e506970011000000dc0000003b00980000003b00bd00ac0000003b00980000003b00bd0697001100cd00ac000000cd00330717001900f50043000e006000f5000e0076005e0053005e051700f50019000600000000005c00ac00e5005c00ac00e505970011000000ac0000003b00a40000003b00bd00ac0000003b00ec0000003b00bd0597001100cd000000330000004c0011000000ac0000003b00ec0000003b00bd00ac0000003b000000bd0497001100cd000000330517001900f50043061700000076000000640120008d006400ac008d07970011005300760000004c0011005307170078000000530078000000530717006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f50019000e006400f500620019025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00000033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000004a001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L06M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L06M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 2 3517 3749 57 12 263340000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3517 3749 57 12 263340000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L06M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L06M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3 3517 3749 57 12 263340000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3517 3749 57 12 263340000000000000 7 0x360022123f00360002123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L06M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L06M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 4 3517 3749 57 12 263340000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3517 3749 57 12 263340000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L06M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L06M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 5 3517 3749 57 12 263340000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3517 3749 57 12 263340000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L06M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L06M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 6 3517 3749 57 12 263340000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3517 3749 57 12 263340000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L06M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L06
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨46,153,3378,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3517 3749 57 12 263340000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L06M1.covered
  · exact OwnerBox6815_L06M2.covered
  · exact OwnerBox6815_L06M3.covered
  · exact OwnerBox6815_L06M4.covered
  · exact OwnerBox6815_L06M5.covered
  · exact OwnerBox6815_L06M6.covered
theorem linear : LinearChecks 12 39 258 3749 57 12 263340000000000000 := by decide +kernel
theorem high : Gates 3749 57 12 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3749 57 12/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3749 57 12≤263340000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 57 12) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3517≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3749 57 12) 263340000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3517 263340000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L06
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L07M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3318 3533 53 13 245800000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3318 3533 53 13 245800000000000000 17 0xe007800600053007800000053071700f5000e0076005c000e000a005c004b00e50052000a005c004b00e5079700110060005a006000bd005a006000bd0797001100cd00530076005c005a00110060005e001100cd0053071700f500190006000000dc005c007000e5005c006000dc003b00e507970011000000dc012c003b00e0012c07d70000003b00bd00dc00b4003b012c00ac013000b507570000003b00bd0797001100cd000000440000002b00ac07970011000000cd0033004c005c005000dc003b00e5005c005000ac003b00e506970011000000dc00b4000006d7003b00ac009800b500d4009800b506d70000003b00bd00ac0000003b00980000003b00bd0697001100cd00ac000000cd00330717001900f50043000e0078000000530060051700f5000e0076005a005e00cd00530076005e0053051700f500190006000000ac005c005000ac003b00e5005c005000ac003b00e505970011000000ac0000003b00a40000003b00bd00ac0000003b00a40000003b00bd0597001100cd00ac000000cd003300ac005c004c00e5005c00ac00e504970011000000ac0000003b00a40000003b00bd00ac0000003b00a400b4000000b504570000003b00bd0497001100cd00ac000000cd00330517001900f500430617000000760000006400ac008d006400ac008d07970011005300760000006400ac008d004c06970011005307170078000000530078000000530717006d00190000004300000076004c0053007600d400530517004c006d001900000043061700a5000e006400f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f000600000000005c00ac00e5005c00ac00e503af0011000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00ac000000cd00ac000000cd033f0033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L07M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L07M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3318 3533 53 13 245800000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3318 3533 53 13 245800000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L07M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L07M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3318 3533 53 13 245800000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3318 3533 53 13 245800000000000000 12 0x820038034d00860072034d00710072153f00860038034d0036153f00fb003802dd0022123f00860072034d0036153f00860036034d0036153f00fb00860072034d0036153f00860036034d0036153f00fb00410072003800fb0036004102dd0036000202dd123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L07M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L07M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3318 3533 53 13 245800000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3318 3533 53 13 245800000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L07M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L07M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3318 3533 53 13 245800000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3318 3533 53 13 245800000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L07M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L07M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3318 3533 53 13 245800000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3318 3533 53 13 245800000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L07M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L07
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3318 3533 53 13 245800000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L07M1.covered
  · exact OwnerBox6815_L07M2.covered
  · exact OwnerBox6815_L07M3.covered
  · exact OwnerBox6815_L07M4.covered
  · exact OwnerBox6815_L07M5.covered
  · exact OwnerBox6815_L07M6.covered
theorem linear : LinearChecks 12 39 258 3533 53 13 245800000000000000 := by decide +kernel
theorem high : Gates 3533 53 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3533 53 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3533 53 13≤245800000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3533 53 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3318≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3533 53 13) 245800000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3318 245800000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L07
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L08M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 1 3534 3749 53 13 256910000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3534 3749 53 13 256910000000000000 19 0xe007800600053007800600053071700f5000e00760010005c00e5005c0797000e000a005a004b00e50052000a005a004b00e5079700110060005a006000bd005a006000bd0797001100cd00530076005c005a00110060005e001100cd0053071700f5001900060000007000dc0797005c006000dc003b00e5005c006000dc003b00e507970011000000dc012c003b00e0012c07d70000003b00bd00dc00b4003b012c00ac013000b507570000003b00bd0797001100cd00000044012c002b00ac07970011000000cd0033004c005c005000dc003b00e5005c005000ac003b00e506970011000000dc00b400b806d7003b00ac009800b500d4009800b506d70000003b00bd00ac00b8003b00a40000003b00bd0697001100cd00ac000000cd00330717001900f50043000e0078006000530060051700f5000e0076005a005e00cd00530076005e0053051700f500190006000000ac005c005000ac003b00e5005c005000ac003b00e505970011000000ac00b8003b00a40000003b00bd00ac00ec00c8000000c500c8000000c505370557003b00a40000003b00bd0597001100cd00ac000000cd003300ac005c005000ac003b00e5005c00ac00e504970011000000ac00c8000000c500c8000000c504f700c8000000c500c8000000c504b704d7003b00a40000003b00bd00ac00a0000000c500a0000000c5047700a0000000c500a0000000c504370457003b00a400b400a40098000000ad043700b504570000003b00bd0497001100cd00ac000000cd00330517001900f500430617000000760000006400ac008d006400ac008d07970011005300760000006400ac008d006400ac008d06970011005307170078000000530078000000530717006d00190000004300000076004c0053007600d400530517004c006d001900000043061700a5000e006400f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f0006000000ac005c00ac00e5005c00ac00e503af0011000000ac00a0000000c500a0000000c5000003cf03e7003b00b40098000000ad00b500b40098000000ad0098000000ad03cf00b503e70000003b00bd00ac0000003b00b40098000000ad0098000000ad039700b500b40098000000ad0000035f00b503770000003b00bd03af001100cd00ac00ac0011000000d40000003b00b4000000b500b4000000b503070000003b00bd00d40000003b00b4000000b500b4000000b502970000003b00bd02cf001100cd033f00ac000000cd00ac000000cd033f0033001900f50006000000ac000000d40000003b00b4000000b500b4000000b5022f0000003b00bd00d40000003b00b4000000b500c4000000b501bf0000003b00bd01f7001100cd00ac000000d40000003b00c4000000b500c4000000b5014f0000003b00bd00d40000003b00c4000000b5000000df0000003b00bd0117001100cd018700ac000000cd00a0000000cd01870033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L08M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L08M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 2 3534 3749 53 13 256910000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3534 3749 53 13 256910000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L08M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L08M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3 3534 3749 53 13 256910000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3534 3749 53 13 256910000000000000 12 0x860038034d00860072034d00710072153f00860038034d0036153f00fb0074000400fb02dd0022123f00860072034d0036153f00860036034d0036153f00fb00860072034d0036153f00860036034d0036153f00fb00410072003800fb0036004102dd0036000202dd123f003a0002123f00c300590004003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L08M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L08M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 4 3534 3749 53 13 256910000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3534 3749 53 13 256910000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L08M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L08M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 5 3534 3749 53 13 256910000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3534 3749 53 13 256910000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L08M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L08M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 6 3534 3749 53 13 256910000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3534 3749 53 13 256910000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L08M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L08
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨46,153,3378,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3534 3749 53 13 256910000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L08M1.covered
  · exact OwnerBox6815_L08M2.covered
  · exact OwnerBox6815_L08M3.covered
  · exact OwnerBox6815_L08M4.covered
  · exact OwnerBox6815_L08M5.covered
  · exact OwnerBox6815_L08M6.covered
theorem linear : LinearChecks 12 39 258 3749 53 13 256910000000000000 := by decide +kernel
theorem high : Gates 3749 53 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3749 53 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3749 53 13≤256910000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 53 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3534≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3749 53 13) 256910000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3534 256910000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L08
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L09M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3261 3383 54 13 246600000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3261 3383 54 13 246600000000000000 15 0xe0078000000530060071700f5000e0076005a005e00cd00530076005e0053071700f500190006000000000070005c00dc00e5079700110000012c00dc0000003b000000bd0797001100cd000000330000005c00dc00e5005c00ac00e506970011000000dc0000003b000000bd00ac0000003b000000bd0697001100cd000000330717001900f50043000e006000f5000e005e00f50019000600000000005c00ac00e5005c00ac00e505970011000000b8000000bd00000597001100cd0000003300ac000000cd000000330517001900f50043061700000076004c0053007600ac00530717004c006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f500190062025f0006000000ac000000cd00ac000000cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f00430000007600d4005300d20317004c006d001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L09M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L09M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3261 3383 54 13 246600000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3261 3383 54 13 246600000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L09M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L09M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3261 3383 54 13 246600000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3261 3383 54 13 246600000000000000 7 0x2200360002123f003a0002123f00c300590000003a0002123f000000c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L09M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L09M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3261 3383 54 13 246600000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3261 3383 54 13 246600000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L09M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L09M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3261 3383 54 13 246600000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3261 3383 54 13 246600000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L09M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L09M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3261 3383 54 13 246600000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3261 3383 54 13 246600000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L09M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L09
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3261 3383 54 13 246600000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L09M1.covered
  · exact OwnerBox6815_L09M2.covered
  · exact OwnerBox6815_L09M3.covered
  · exact OwnerBox6815_L09M4.covered
  · exact OwnerBox6815_L09M5.covered
  · exact OwnerBox6815_L09M6.covered
theorem linear : LinearChecks 12 39 258 3383 54 13 246600000000000000 := by decide +kernel
theorem high : Gates 3383 54 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3383 54 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3383 54 13≤246600000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3383 54 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3261≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3383 54 13) 246600000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3261 246600000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L09
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L10M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 1 3384 3505 54 13 252660000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3384 3505 54 13 252660000000000000 15 0xe0078000000530060071700f5000e0076005a005e00cd00530076005e0053071700f500190006000000000070005c00dc00e5079700110000012c00dc0000003b000000bd0797001100cd00ac000000cd00330000005c00dc00e5005c004c00e506970011000000dc0000003b000000bd00ac0000003b000000bd0697001100cd00ac000000cd00330717001900f50043000e006000f5000e005e00f50019000600000000005c00ac00e5005c00ac00e505970011000000ac0000003b000000bd00ac0000003b000000bd0597001100cd000000330000004c0011000000ac0000003b000000bd00ac0000003b000000bd0497001100cd000000330517001900f500430617000000760000004c00110053007600ac00530717004c006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f500190062025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f00430000007600d4005300d20317004c006d001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L10M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L10M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 2 3384 3505 54 13 252660000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3384 3505 54 13 252660000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L10M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L10M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3 3384 3505 54 13 252660000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3384 3505 54 13 252660000000000000 7 0x2200360002123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L10M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L10M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 4 3384 3505 54 13 252660000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3384 3505 54 13 252660000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L10M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L10M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 5 3384 3505 54 13 252660000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3384 3505 54 13 252660000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L10M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L10M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 6 3384 3505 54 13 252660000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3384 3505 54 13 252660000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L10M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L10
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨46,153,3378,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3384 3505 54 13 252660000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L10M1.covered
  · exact OwnerBox6815_L10M2.covered
  · exact OwnerBox6815_L10M3.covered
  · exact OwnerBox6815_L10M4.covered
  · exact OwnerBox6815_L10M5.covered
  · exact OwnerBox6815_L10M6.covered
theorem linear : LinearChecks 12 39 258 3505 54 13 252660000000000000 := by decide +kernel
theorem high : Gates 3505 54 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3505 54 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3505 54 13≤252660000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3505 54 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3384≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3505 54 13) 252660000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3384 252660000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L10
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L11M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 1 3506 3627 54 13 259580000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3506 3627 54 13 259580000000000000 15 0xe0078000000530060071700f5000e0076005a005e00cd00530076005e0053071700f500190006000000dc0070005c00dc00e5079700110000012c00dc0000003b013000bd0797001100cd00ac000000cd00330000005c00dc00e5005c004c00e506970011000000dc0000003b00980000003b00bd00ac0000003b000000bd0697001100cd00ac000000cd00330717001900f50043000e006000f5000e005e00f50019000600000000005c00ac00e5005c00ac00e505970011000000b8000000bd00ac0000003b000000bd0597001100cd00ac000000cd00330000004c0011000000ac0000003b000000bd00ac0000003b000000bd0497001100cd000000330517001900f50043061700000076004c0053007600ac00530717004c006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f500190062025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00000033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000cd018700000033001900f5025f00430000007600d4005300d20317004c006d001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L11M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L11M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 2 3506 3627 54 13 259580000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3506 3627 54 13 259580000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L11M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L11M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3 3506 3627 54 13 259580000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3506 3627 54 13 259580000000000000 7 0x2200360002123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L11M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L11M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 4 3506 3627 54 13 259580000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3506 3627 54 13 259580000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L11M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L11M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 5 3506 3627 54 13 259580000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3506 3627 54 13 259580000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L11M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L11M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 6 3506 3627 54 13 259580000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3506 3627 54 13 259580000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L11M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L11
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨46,153,3378,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3506 3627 54 13 259580000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L11M1.covered
  · exact OwnerBox6815_L11M2.covered
  · exact OwnerBox6815_L11M3.covered
  · exact OwnerBox6815_L11M4.covered
  · exact OwnerBox6815_L11M5.covered
  · exact OwnerBox6815_L11M6.covered
theorem linear : LinearChecks 12 39 258 3627 54 13 259580000000000000 := by decide +kernel
theorem high : Gates 3627 54 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3627 54 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3627 54 13≤259580000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3627 54 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3506≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3627 54 13) 259580000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3506 259580000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L11
end MergedPart11
section MergedPart12
namespace ProximityPrize.SubmissionLower.OwnerBox6815_L12M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 1 3628 3749 54 13 265790000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3628 3749 54 13 265790000000000000 15 0xe0078000000530060071700f5000e0076005a005e00cd00530076005e0053071700f500190006000000dc005c007000e5005c00dc00e5079700110000012000dc0000003b013000bd0797001100cd00ac000000cd003300ac005c00dc00e5005c004c00e506970011000000dc0000003b00980000003b00bd00ac0000003b00980000003b00bd0697001100cd00ac000000cd00330717001900f50043000e006000f5000e005e00f500190006000000ac005c00ac00e5005c00ac00e505970011000000ac0000003b00ec0000003b00bd00ac0000003b00ec0000003b00bd0597001100cd00ac000000cd00330000005c00ac00e500ac04970011000000ac0000003b00ec0000003b00bd00ac0000003b000000bd0497001100cd00ac000000cd00330517001900f500430617000000760000004c00110053007600ac00530717004c006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f500190062025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00ac000000cd0000033f0033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d4005300d20317004c006d001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L12M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L12M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 2 3628 3749 54 13 265790000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3628 3749 54 13 265790000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L12M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L12M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 3 3628 3749 54 13 265790000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3628 3749 54 13 265790000000000000 7 0x2200360002123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L12M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L12M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 4 3628 3749 54 13 265790000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3628 3749 54 13 265790000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L12M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L12M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 5 3628 3749 54 13 265790000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3628 3749 54 13 265790000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L12M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_L12M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 6 3628 3749 54 13 265790000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3628 3749 54 13 265790000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_L12M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L12
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,176,3618,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3628 3749 54 13 265790000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_L12M1.covered
  · exact OwnerBox6815_L12M2.covered
  · exact OwnerBox6815_L12M3.covered
  · exact OwnerBox6815_L12M4.covered
  · exact OwnerBox6815_L12M5.covered
  · exact OwnerBox6815_L12M6.covered
theorem linear : LinearChecks 12 39 258 3749 54 13 265790000000000000 := by decide +kernel
theorem high : Gates 3749 54 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3749 54 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3749 54 13≤265790000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 54 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3628≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3749 54 13) 265790000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3628 265790000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L12
end MergedPart12
