import ProximityPrize.SubmissionLower.MergedInfra6815_47
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I00M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 1 3599 3724 58 11 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3599 3724 58 11 271000000000000000 7 0x5e0006000000f50043005e0006000000f500430617004a00000043004a00000043061700a500620006000000f50006000000f5025f0043004a00000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I00M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I00M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 2 3599 3724 58 11 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3599 3724 58 11 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I00M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I00M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3 3599 3724 58 11 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3599 3724 58 11 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I00M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I00M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 4 3599 3724 58 11 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3599 3724 58 11 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I00M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I00M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 5 3599 3724 58 11 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3599 3724 58 11 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I00M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I00M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 6 3599 3724 58 11 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3599 3724 58 11 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I00M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I00
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,177,3543,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3599 3724 58 11 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I00M1.covered
  · exact OwnerBox6815_I00M2.covered
  · exact OwnerBox6815_I00M3.covered
  · exact OwnerBox6815_I00M4.covered
  · exact OwnerBox6815_I00M5.covered
  · exact OwnerBox6815_I00M6.covered
theorem linear : LinearChecks 12 39 258 3724 58 11 271000000000000000 := by decide +kernel
theorem high : Gates 3724 58 11 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3724 58 11/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3724 58 11≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3724 58 11) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3599≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3724 58 11) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3599 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I00
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I01M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3347 3774 58 12 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3347 3774 58 12 271000000000000000 15 0xe0078000000530060071700f5000e0076005a005e00cd00530076005e0053071700f500190006000000000070005c00dc00e5079700110000012c00dc0000003b013000bd0797001100cd01300033000000dc005c00ac00e506970011000000dc0000003b00980000003b00bd00b800980000003b00bd0697001100cd000000330717001900f50043000e006000f5000e0076005e0053005e051700f50019000600000000004c0011000000b800ec0000003b00bd00ac0000003b000000bd0597001100cd0000003300ac000000ac0000003b000000bd00ac0000003b000000bd0497001100cd000000330517001900f5004306170000007600000064012c008d004c0797001100530076004c005307170078000000530078000000530717006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f500190062025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00000033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000cd018700000033001900f5025f00430000007600d4005300d20317004c006d0019000000430000004a001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I01M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I01M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3347 3774 58 12 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3347 3774 58 12 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I01M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I01M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3347 3774 58 12 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3347 3774 58 12 271000000000000000 7 0x2200360002123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I01M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I01M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3347 3774 58 12 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3347 3774 58 12 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I01M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I01M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3347 3774 58 12 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3347 3774 58 12 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I01M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I01M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3347 3774 58 12 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3347 3774 58 12 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I01M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I01
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3347 3774 58 12 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I01M1.covered
  · exact OwnerBox6815_I01M2.covered
  · exact OwnerBox6815_I01M3.covered
  · exact OwnerBox6815_I01M4.covered
  · exact OwnerBox6815_I01M5.covered
  · exact OwnerBox6815_I01M6.covered
theorem linear : LinearChecks 12 39 258 3774 58 12 271000000000000000 := by decide +kernel
theorem high : Gates 3774 58 12 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3774 58 12/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3774 58 12≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3774 58 12) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3347≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3774 58 12) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3347 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I01
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I02M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3294 3774 59 12 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3294 3774 59 12 271000000000000000 17 0xe007800000053007800000053071700f5000e0076005c000e000a005c004b00e50052005a00e5079700110060005a006000bd005a006000bd0797001100cd00530076005a0060005e001100cd0053071700f500190006000000dc005c007000e5005c006000dc003b00e507970011000000dc012c003b012c00bd00dc0130003b012c013007570000003b00bd0797001100cd00ac000000cd00330000005c00dc00e5005c005000ac003b00e506970011000000dc0000003b00980000003b00bd00ac0000003b00980000003b00bd0697001100cd00ac000000cd00330717001900f50043000e006000f5000e0076005a005e00cd00530076005e0053051700f50019000600000000005c004c00e5005c00ac00e505970011000000ac0000003b00a40000003b00bd00ac0000003b00a40000003b00bd0597001100cd00ac000000cd00330000005c00ac00e5005c00ac00e504970011000000ac0000003b00ec0000003b00bd00ac0000003b00a400b4000000b504570000003b00bd0497001100cd00ac000000cd00330517001900f5004306170000007600000064004c008d006400ac008d07970011005300760000006400ac008d006400ac008d0697001100530717007800d400530078004c00530717006d001900000043000000760000004c00110053007600d4005305170078000000530078000000530517006d001900000043061700a5000e006400f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f0006000000ac000000ac0000003b00b4000000b500b4000000b503e70000003b00bd00ac0000003b00b4000000b500b4000000b503770000003b00bd03af001100cd00ac000000d40000003b00b4000000b500b4000000b503070000003b00bd00d40000003b00b4000000b5000002970000003b00bd02cf001100cd033f00000033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I02M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I02M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3294 3774 59 12 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3294 3774 59 12 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I02M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I02M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3294 3774 59 12 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3294 3774 59 12 271000000000000000 12 0x7400860072034d00710036153f003800fb003802dd0022123f00860072034d0036153f003600fb0072003600fb0041003602dd0036000202dd123f003a0002123f00c300590004003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I02M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I02M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3294 3774 59 12 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3294 3774 59 12 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I02M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I02M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3294 3774 59 12 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3294 3774 59 12 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I02M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I02M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3294 3774 59 12 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3294 3774 59 12 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I02M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I02
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3294 3774 59 12 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I02M1.covered
  · exact OwnerBox6815_I02M2.covered
  · exact OwnerBox6815_I02M3.covered
  · exact OwnerBox6815_I02M4.covered
  · exact OwnerBox6815_I02M5.covered
  · exact OwnerBox6815_I02M6.covered
theorem linear : LinearChecks 12 39 258 3774 59 12 271000000000000000 := by decide +kernel
theorem high : Gates 3774 59 12 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3774 59 12/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3774 59 12≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3774 59 12) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3294≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3774 59 12) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3294 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I02
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I03M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3322 3699 55 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3322 3699 55 13 271000000000000000 15 0xe006000f5000e0076005e0053005e071700f500190006000000000070005c00dc00e5079700110000012c01300797001100cd01300033000000dc005c00ac00e506970011000000b8000000bd00b8000000bd0697001100cd000000330717001900f50043000e006000f5000e005e00f5001900060000004c000000b8000000bd00ac0000003b000000bd0597001100cd0000003300ac000000ac0000003b000000bd00ac0000003b000000bd0497001100cd000000330517001900f5004306170000007600ac0053007600ac00530717004c006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f500190062025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f0043000000d2004c006d001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I03M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I03M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3322 3699 55 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3322 3699 55 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I03M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I03M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3322 3699 55 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3322 3699 55 13 271000000000000000 7 0x2200360002123f003a0002123f00c3005900000002005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I03M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I03M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3322 3699 55 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3322 3699 55 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I03M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I03M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3322 3699 55 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3322 3699 55 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I03M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I03M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3322 3699 55 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3322 3699 55 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I03M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I03
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3322 3699 55 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I03M1.covered
  · exact OwnerBox6815_I03M2.covered
  · exact OwnerBox6815_I03M3.covered
  · exact OwnerBox6815_I03M4.covered
  · exact OwnerBox6815_I03M5.covered
  · exact OwnerBox6815_I03M6.covered
theorem linear : LinearChecks 12 39 258 3699 55 13 271000000000000000 := by decide +kernel
theorem high : Gates 3699 55 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3699 55 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3699 55 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3699 55 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3322≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3699 55 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3322 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I03
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I04M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3266 3699 56 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3266 3699 56 13 271000000000000000 15 0xe007800000053007800000053071700f5000e0076005c005a00110060005e001100cd00530076005a005e00cd0053071700f500190006000000dc005c007000e5005c006000dc003b00e507970011000000dc012c003b012c00bd00dc0000003b013000bd0797001100cd00ac000000cd003300ac005c00dc00e5005c004c00e506970011000000dc0000003b00980000003b00bd00ac0000003b00980000003b00bd0697001100cd00ac000000cd00330717001900f50043000e006000f5000e0076005e0053005e051700f50019000600000000005c00ac00e5005c00ac00e505970011000000ac0000003b00a40000003b00bd00ac0000003b00ec0000003b00bd0597001100cd00ac000000cd00330000005c00ac00e500ac04970011000000ac0000003b00ec0000003b00bd00ac0000003b000000bd0497001100cd00ac000000cd00330517001900f5004306170000007600000064012c008d004c0797001100530076004c00530717007800000053004c0717006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f50019000e006400f5000e006200f50019025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00000033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d40053007600d400530317004c006d001900000043000000d2004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I04M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I04M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3266 3699 56 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3266 3699 56 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I04M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I04M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3266 3699 56 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3266 3699 56 13 271000000000000000 10 0x72003600fb003802dd0022123f0072003600fb00360041003602dd0002123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I04M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I04M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3266 3699 56 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3266 3699 56 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I04M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I04M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3266 3699 56 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3266 3699 56 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I04M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I04M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3266 3699 56 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3266 3699 56 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I04M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I04
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3266 3699 56 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I04M1.covered
  · exact OwnerBox6815_I04M2.covered
  · exact OwnerBox6815_I04M3.covered
  · exact OwnerBox6815_I04M4.covered
  · exact OwnerBox6815_I04M5.covered
  · exact OwnerBox6815_I04M6.covered
theorem linear : LinearChecks 12 39 258 3699 56 13 271000000000000000 := by decide +kernel
theorem high : Gates 3699 56 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3699 56 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3699 56 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3699 56 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3266≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3699 56 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3266 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I04
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I05M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3213 3456 57 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3213 3456 57 13 271000000000000000 11 0xe006000f5000e005e00f500190006000000dc000000cd0000003300ac000000cd000000330717001900f50043005e0006000000ac000000cd0000003300ac000000cd000000330517001900f5004306170000007600ac0053007600ac00530717004c006d0019000000430000004a001900000043061700a500620006000000ac000000cd00ac000000cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f0043004a00000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I05M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I05M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3213 3456 57 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3213 3456 57 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I05M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I05M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3213 3456 57 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3213 3456 57 13 271000000000000000 6 0x220012000200c30059000201f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I05M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I05M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3213 3456 57 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3213 3456 57 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I05M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I05M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3213 3456 57 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3213 3456 57 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I05M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I05M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3213 3456 57 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3213 3456 57 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I05M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I05
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3213 3456 57 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I05M1.covered
  · exact OwnerBox6815_I05M2.covered
  · exact OwnerBox6815_I05M3.covered
  · exact OwnerBox6815_I05M4.covered
  · exact OwnerBox6815_I05M5.covered
  · exact OwnerBox6815_I05M6.covered
theorem linear : LinearChecks 12 39 258 3456 57 13 271000000000000000 := by decide +kernel
theorem high : Gates 3456 57 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3456 57 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3456 57 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3456 57 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3213≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3456 57 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3213 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I05
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I06M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 1 3457 3699 57 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3457 3699 57 13 271000000000000000 19 0xe007800600053007800600053071700f5000e00760010005c00e5005c0797000e000a005a004b00e5000e0052004b000a005a004b00e5079700110060000a005c004b00540060004b00bd005a006000bd0797001100cd00530076005c0052005a00e5005a069700110060005a006000bd005e0697001100cd0053071700f500190006000000dc005c006000dc003b00e5005c006000dc003b00e507970011000000e000dc07d7012c003b00e0012007d70000003b00bd00dc00b4003b012c00ac012c0130073700b507570000003b00bd0797001100cd000000ac0011000000cd0033004c005c005000dc003b00e5005c005000ac003b00e506970011000000dc00b400b806d7003b00ac009800b500d4009800b506d70000003b00bd00ac00b8003b00d4009800b5009806570000003b00bd0697001100cd00ac000000cd00330717001900f50043000e0078006000530060051700f5000e0076005a005e00cd00530076005e0053051700f500190006000000ac005c005000ac003b00e5005c005000ac003b00e505970011000000ac00b8003b00a40000003b00bd00ac00ec00c8000000c500c8000000c505370557003b00a40000003b00bd0597001100cd00ac000000cd003300ac005c005000ac003b00e5005c00ac00e504970011000000ac00c8000000c500c8000000c504f700c8000000c500c8000000c504b704d7003b00a40000003b00bd00ac0000003b00a400b400a40098000000ad043700b504570000003b00bd0497001100cd00ac000000cd00330517001900f5004306170000007600000064004c008d0064004c008d07970011005300760000006400ac008d006400ac008d06970011005307170078000000530078000000530717006d001900000043000000760000006400ac008d004c059700110053007600d400530517007800000053004c0517006d001900000043061700a5000e0078000000530064033f00f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f0006000000ac005c00ac00e5005c00ac00e503af0011000000ac0000003b00b40098000000ad00b500b40098000000ad0098000000ad03cf00b503e70000003b00bd00ac0000003b00b40098000000ad0098000000ad039700b500b4000000b503770000003b00bd03af001100cd000000ac0011000000d40000003b00b4000000b500b4000000b503070000003b00bd00d40000003b00b4000000b500b4000000b502970000003b00bd02cf001100cd033f00ac000000cd00ac000000cd033f0033001900f50006000000ac000000d40000003b00b4000000b500b4000000b5022f0000003b00bd00d40000003b00b4000000b500c4000000b501bf0000003b00bd01f7001100cd00ac000000d40000003b00c4000000b500c4000000b5014f0000003b00bd00d40000003b000000bd0117001100cd018700ac000000cd00a0000000cd01870033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I06M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I06M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 2 3457 3699 57 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3457 3699 57 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I06M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I06M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3 3457 3699 57 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3457 3699 57 13 271000000000000000 13 0x9a0088011b008616bf0038034d009200860072011b007216bf034d00710072153f00860038034d0036153f00fb0074000400fb02dd0022123f00860072034d003a153f00860036034d0036153f00fb00860072034d0036153f00860036034d0036153f00fb00410072003800fb0072003600fb004102dd0036000202dd123f003a0002123f00c300590004003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I06M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I06M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 4 3457 3699 57 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3457 3699 57 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I06M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I06M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 5 3457 3699 57 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3457 3699 57 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I06M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I06M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 6 3457 3699 57 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3457 3699 57 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I06M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I06
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨46,153,3378,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3457 3699 57 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I06M1.covered
  · exact OwnerBox6815_I06M2.covered
  · exact OwnerBox6815_I06M3.covered
  · exact OwnerBox6815_I06M4.covered
  · exact OwnerBox6815_I06M5.covered
  · exact OwnerBox6815_I06M6.covered
theorem linear : LinearChecks 12 39 258 3699 57 13 271000000000000000 := by decide +kernel
theorem high : Gates 3699 57 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3699 57 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3699 57 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3699 57 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3457≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3699 57 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3457 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I06
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I07M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3161 3378 58 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3161 3378 58 13 271000000000000000 11 0xe006000f5000e005e00f500190006000000dc000000cd0000003300ac000000cd000000330717001900f50043005e0006000000ac000000cd0000003300ac000000cd000000330517001900f50043061700000076000000530076000000530717004c006d0019000000430000004a001900000043061700a500620006000000ac000000cd00ac000000cd033f00000033001900f50006000000ac000000cd0000018700000033001900f5025f0043004a00000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I07M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I07M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3161 3378 58 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3161 3378 58 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I07M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I07M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3161 3378 58 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3161 3378 58 13 271000000000000000 6 0x220012000200c30059000201f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I07M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I07M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3161 3378 58 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3161 3378 58 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I07M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I07M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3161 3378 58 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3161 3378 58 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I07M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I07M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3161 3378 58 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3161 3378 58 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I07M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I07
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3161 3378 58 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I07M1.covered
  · exact OwnerBox6815_I07M2.covered
  · exact OwnerBox6815_I07M3.covered
  · exact OwnerBox6815_I07M4.covered
  · exact OwnerBox6815_I07M5.covered
  · exact OwnerBox6815_I07M6.covered
theorem linear : LinearChecks 12 39 258 3378 58 13 271000000000000000 := by decide +kernel
theorem high : Gates 3378 58 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3378 58 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3378 58 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3378 58 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3161≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3378 58 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3161 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I07
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I08M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 1 3379 3543 58 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3379 3543 58 13 271000000000000000 15 0xe0078000000530060071700f5000e0076005a005e00cd00530076005e0053071700f500190006000000000070005c00dc00e507970011000000dc0000003b012c00bd00dc0000003b013000bd0797001100cd00ac000000cd00330000005c00dc00e5005c004c00e506970011000000dc0000003b00980000003b00bd00ac0000003b000000bd0697001100cd000000330717001900f50043000e006000f5000e0076005e0053005e051700f50019000600000000005c00ac00e5005c00ac00e505970011000000ac0000003b000000bd00ac0000003b000000bd0597001100cd000000330000004c0011000000ac0000003b000000bd00ac0000003b000000bd0497001100cd000000330517001900f5004306170000007600000064012c008d004c0797001100530076004c00530717007800000053004c0717006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f50019000e006400f500620019025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f00430000007600d4005300d20317004c006d0019000000430000004a001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I08M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I08M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 2 3379 3543 58 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3379 3543 58 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I08M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I08M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3 3379 3543 58 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3379 3543 58 13 271000000000000000 7 0x2200360002123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I08M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I08M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 4 3379 3543 58 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3379 3543 58 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I08M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I08M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 5 3379 3543 58 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3379 3543 58 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I08M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I08M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 6 3379 3543 58 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3379 3543 58 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I08M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I08
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨46,153,3378,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3379 3543 58 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I08M1.covered
  · exact OwnerBox6815_I08M2.covered
  · exact OwnerBox6815_I08M3.covered
  · exact OwnerBox6815_I08M4.covered
  · exact OwnerBox6815_I08M5.covered
  · exact OwnerBox6815_I08M6.covered
theorem linear : LinearChecks 12 39 258 3543 58 13 271000000000000000 := by decide +kernel
theorem high : Gates 3543 58 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3543 58 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3543 58 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3543 58 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3379≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3543 58 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3379 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I08
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I09M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 1 3544 3560 58 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3544 3560 58 13 271000000000000000 15 0xe007800000053007800000053071700f5000e0076005a005e00cd00530076005e0053071700f50019000600000000005c007000e5005c006000dc003b00e507970011000000dc0000003b012c00bd00dc0000003b013000bd0797001100cd00ac000000cd00330000005c00dc00e5005c005000ac003b00e506970011000000dc0000003b00980000003b00bd00ac0000003b00980000003b00bd0697001100cd00ac000000cd00330717001900f50043000e006000f5000e0076005e0053005e051700f50019000600000000005c004c00e5005c00ac00e505970011000000ac0000003b00a40000003b00bd00ac0000003b000000bd0597001100cd000000330000005c00ac00e500ac04970011000000ac0000003b000000bd00ac0000003b000000bd0497001100cd000000330517001900f50043061700000076000000640120008d006400ac008d07970011005300760000004c0011005307170078000000530078000000530717006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a5000e006400f5000e006200f50019000e006400f500620019025f0006000000ac000000ac0000003b000000bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00000033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000cd018700000033001900f5025f00430000007600d4005300d20317004c006d0019000000430000004a001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I09M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I09M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 2 3544 3560 58 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3544 3560 58 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I09M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I09M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3 3544 3560 58 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3544 3560 58 13 271000000000000000 7 0x360022123f00360002123f003a0002123f00c300590000003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I09M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I09M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 4 3544 3560 58 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3544 3560 58 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I09M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I09M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 5 3544 3560 58 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3544 3560 58 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I09M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I09M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 6 3544 3560 58 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3544 3560 58 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I09M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I09
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,177,3543,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3544 3560 58 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I09M1.covered
  · exact OwnerBox6815_I09M2.covered
  · exact OwnerBox6815_I09M3.covered
  · exact OwnerBox6815_I09M4.covered
  · exact OwnerBox6815_I09M5.covered
  · exact OwnerBox6815_I09M6.covered
theorem linear : LinearChecks 12 39 258 3560 58 13 271000000000000000 := by decide +kernel
theorem high : Gates 3560 58 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3560 58 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3560 58 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3560 58 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3544≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3560 58 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3544 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I09
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I10M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 1 3561 3618 58 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3561 3618 58 13 271000000000000000 17 0xe007800600053007800000053071700f5000e00760010005c00e5005c0797000e000a005a004b00e50052005a00e5079700110060005a006000bd005a006000bd0797001100cd00530076005a005e00cd0053071700f500190006000000dc005c007000e5005c006000dc003b00e507970011000000dc012c003b00e0012c07d70000003b00bd00dc00b4003b012c00ac013000b507570000003b00bd0797001100cd00ac000000cd0033004c005c005000dc003b00e5005c005000ac003b00e506970011000000dc00b8003b00ac009800b500d4009800b506d70000003b00bd00ac00b8003b00d4009800b5009806570000003b00bd0697001100cd00ac000000cd00330717001900f50043000e0078000000530060051700f5000e0076005e00530076005e0053051700f500190006000000ac005c005000ac003b00e5005c005000ac003b00e505970011000000ac00b8003b00a40000003b00bd00ac0000003b00a40000003b00bd0597001100cd00ac000000cd00330000005c004c00e5005c00ac00e504970011000000ac0000003b00a40000003b00bd00ac0000003b00a400b4000000b504570000003b00bd0497001100cd00ac000000cd00330517001900f5004306170000007600000064004c008d0064004c008d07970011005300760000006400ac008d006400ac008d06970011005307170078000000530078000000530717006d001900000043000000760000006400ac008d004c059700110053007600d400530517007800000053004c0517006d001900000043061700a5000e006400f5000e0076006200530062033f00f50019000e006400f5000e006200f50019025f000600000000005c00ac00e5005c00ac00e503af0011000000ac0000003b00b4000000b500b4000000b503e70000003b00bd00ac0000003b00b4000000b500b4000000b503770000003b00bd03af001100cd00ac000000d40000003b00b4000000b500b4000000b503070000003b00bd00d40000003b00b4000000b5000002970000003b00bd02cf001100cd033f00ac000000cd00ac000000cd033f0033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I10M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I10M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 2 3561 3618 58 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3561 3618 58 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I10M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I10M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3 3561 3618 58 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3561 3618 58 13 271000000000000000 12 0x860038034d00860072034d00710036153f00860038034d0036153f00fb0072000400fb02dd0022123f00860072034d0036153f003600fb0072003600fb0041003602dd0036000202dd123f003a0002123f00c300590004003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I10M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I10M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 4 3561 3618 58 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3561 3618 58 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I10M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I10M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 5 3561 3618 58 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3561 3618 58 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I10M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I10M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 6 3561 3618 58 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3561 3618 58 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I10M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I10
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,177,3543,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3561 3618 58 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I10M1.covered
  · exact OwnerBox6815_I10M2.covered
  · exact OwnerBox6815_I10M3.covered
  · exact OwnerBox6815_I10M4.covered
  · exact OwnerBox6815_I10M5.covered
  · exact OwnerBox6815_I10M6.covered
theorem linear : LinearChecks 12 39 258 3618 58 13 271000000000000000 := by decide +kernel
theorem high : Gates 3618 58 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3618 58 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3618 58 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3618 58 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3561≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3618 58 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3561 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I10
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I11M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 1 3619 3680 58 13 273041644927340992
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3619 3680 58 13 273041644927340992 19 0xe007800600053007800600053071700f5000e00760010005c00e50054005c00e50797000e000a00de005a07d7004b00e5000e0052004b000a005a004b00e5079700110060000a005c004b00540060004b00bd005a00540060004b00bd0797001100cd00530076005c0052005a00e5005a069700110060005a006000bd005e0697001100cd0053071700f5001900060000007000dc0797005c00600070003b00e5005c006000dc003b00e507970011000000e000e000dc07b707d7012c003b00e000ac012c00b507d70000003b00bd00dc012c00b40757003b012c00ac012c00d4013000ad073700b507570000003b00bd0797001100cd000000440000002b00ac07970011000000cd0033004c005c005000dc003b00e5005c005000ac003b00e506970011000000dc00b400ac00b800c500ac00b800c506b706d7003b00ac013000d4009800ad06f700b500d400b4009800ad009806b700b506d70000003b00bd004c00b8003b00d4009800b500d4009800b506570000003b00bd0697001100cd00ac000000cd00330717001900f50043000e007800600053007800000053051700f5000e0076005a005e00cd00530076005e0053051700f500190006000000ac005c005000ac003b00e5005c005000ac003b00e505970011000000ac00b8003b00d400a400b500a405d70000003b00bd00ac00b800c8000000c500c8000000c505370557003b00a40000003b00bd0597001100cd00ac000000cd003300ac005c005000ac003b00e5005c005000ac003b00e504970011000000ac00c8000000c500c8000000c504f700c8000000c500c8000000c504b704d7003b00a40000003b00bd00ac00a0000000c500a0000000c5047700a0000000c500a0000000c504370457003b00a400b400a40098000000ad043700b504570000003b00bd0497001100cd00ac000000cd00330517001900f500430617000000760000006400d8012c004b008d0064004c008d079700110053007600000064004c008d006400ac008d0697001100530717007800d400530078000000530717006d001900000000012c01300797001100000085000000330000071700190000005d0043000000760000006400ac008d006400ac008d05970011005300760000004c0011005305170078000000530078000000530517006d001900000043061700a5000e0078000000530064033f00f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f0006000000ac005c00ac00e5005c00ac00e503af0011000000ac0000003b00b40098000000ad00b500b40098000000ad0098000000ad03cf00b503e70000003b00bd00ac0000003b00b40098000000ad0098000000ad039700b500b40098000000ad0098000000ad035f00b503770000003b00bd03af001100cd00ac005c00ac00e500ac02cf0011000000d40000003b00b40098000000ad0098000000ad032700b500b40098000000ad0098000000ad02ef00b503070000003b00bd00d40000003b00b4000000b500b4000000b502970000003b00bd02cf001100cd033f00ac000000cd00ac000000cd033f0033001900f50006000000ac000000d40000003b00b4000000b500b4000000b5022f0000003b00bd00d40000003b00b4000000b500c4000000b501bf0000003b00bd01f7001100cd00ac000000d40000003b00c4000000b500c4000000b5014f0000003b00bd00d40000003b00c4000000b500c4000000b500df0000003b00bd0117001100cd018700ac000000cd00a0000000cd01870033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I11M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I11M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 2 3619 3680 58 13 273041644927340992
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3619 3680 58 13 273041644927340992 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I11M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I11M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 3 3619 3680 58 13 273041644927340992
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3619 3680 58 13 273041644927340992 14 0xba0088011b008616bf0038034d009a0086011b008616bf00860072011b007216bf034d00710072153f00860038034d0036153f00fb0072000400fb02dd0022123f009200860072011b007216bf034d0072153f00860036034d0036153f00fb00860072034d003a153f00860036034d0036153f00fb00410072003600fb0072003600fb004102dd0036000202dd123f003a0002123f00c300590004003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I11M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I11M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 4 3619 3680 58 13 273041644927340992
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3619 3680 58 13 273041644927340992 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I11M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I11M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 5 3619 3680 58 13 273041644927340992
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3619 3680 58 13 273041644927340992 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I11M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I11M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,176,3618,6,8⟩
def valid : Box → Prop := Valid fixed 6 3619 3680 58 13 273041644927340992
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3619 3680 58 13 273041644927340992 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I11M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I11
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,176,3618,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3619 3680 58 13 273041644927340992) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I11M1.covered
  · exact OwnerBox6815_I11M2.covered
  · exact OwnerBox6815_I11M3.covered
  · exact OwnerBox6815_I11M4.covered
  · exact OwnerBox6815_I11M5.covered
  · exact OwnerBox6815_I11M6.covered
theorem linear : LinearChecks 12 39 258 3680 58 13 273041644927340992 := by decide +kernel
theorem high : Gates 3680 58 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3680 58 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3680 58 13≤273041644927340992 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3680 58 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3619≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3680 58 13) 273041644927340992 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3619 273041644927340992
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I11
end MergedPart11
section MergedPart12
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I12M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,175,3680,6,8⟩
def valid : Box → Prop := Valid fixed 1 3681 3684 58 13 273200000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3681 3684 58 13 273200000000000000 19 0xe007800600053007800600053071700f5000e00760010005c00e50054005c00e50797000e000a00de005a07d7004b00e5000e0052004b000a005a004b00e5079700110060000a005c004b00540060004b00bd005a00540060004b00bd0797001100cd00530076005c0052005a00e5005a069700110060005a006000bd005e0697001100cd0053071700f5001900060000007000dc0797005c00600070003b00e5005c006000dc003b00e507970011000000e000e000dc07b707d7012c003b00e0004c012c00b507d70000003b00bd00dc012c00b40757003b012000ac012c00d4013000ad073700b507570000003b00bd0797001100cd000000440000002b00ac07970011000000cd003300dc004c0697005c005000dc003b00e5005c005000ac003b00e506970011000000dc00b400ac00b800c500ac00b800c506b706d7003b00ac013000d4009800ad06f700b500d400b4009800ad00a406b700b506d70000003b00bd004c00b8003b00d4009800b500d4009800b506570000003b00bd0697001100cd00ac000000cd00330717001900f50043000e007800600053007800000053051700f5000e0076005a005e00cd00530076005e0053051700f500190006000000ac005c005000ac003b00e5005c005000ac003b00e505970011000000ac00b8003b00d400a400b500a405d70000003b00bd00ac00b800c8000000c500c8000000c505370557003b00a40000003b00bd0597001100cd00ac000000cd003300ac005c005000ac003b00e5005c005000ac003b00e504970011000000ac00c8000000c500c8000000c504f700c8000000c500c8000000c504b704d7003b00a40000003b00bd00ac00a0000000c500a0000000c5047700a0000000c500a0000000c504370457003b00a400b400a40098000000ad043700b504570000003b00bd0497001100cd00ac000000cd00330517001900f500430617000000760000006400d8012c004b008d0064004c008d079700110053007600000064004c008d006400ac008d0697001100530717007800d400530078004c00530717006d001900000000012c01300797001100000085000000330000071700190000005d0043000000760000006400ac008d006400ac008d05970011005300760000004c0011005305170078000000530078000000530517006d001900000043061700a5000e0078000000530064033f00f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f0006000000ac005c00ac00e5005c00ac00e503af0011000000ac00a0000000c5000003e7003b00b40098000000ad00b500b40098000000ad0098000000ad03cf00b503e70000003b00bd00ac0000003b00b40098000000ad0098000000ad039700b500b40098000000ad0098000000ad035f00b503770000003b00bd03af001100cd00ac005c00ac00e500ac02cf0011000000d40000003b00b40098000000ad0098000000ad032700b500b40098000000ad0098000000ad02ef00b503070000003b00bd00d40000003b00b40098000000ad000002b700b500b4000000b502970000003b00bd02cf001100cd033f00ac000000cd00ac000000cd033f0033001900f50006000000ac000000d40000003b00b4000000b500b4000000b5022f0000003b00bd00d40000003b00b4000000b500c4000000b501bf0000003b00bd01f7001100cd00ac000000d40000003b00c4000000b500c4000000b5014f0000003b00bd00d40000003b00c4000000b500c4000000b500df0000003b00bd0117001100cd018700ac000000cd00a0000000cd01870033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I12M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I12M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,175,3680,6,8⟩
def valid : Box → Prop := Valid fixed 2 3681 3684 58 13 273200000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3681 3684 58 13 273200000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I12M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I12M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,175,3680,6,8⟩
def valid : Box → Prop := Valid fixed 3 3681 3684 58 13 273200000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3681 3684 58 13 273200000000000000 14 0x9a0088011b008616bf0038034d009200860072011b007216bf034d00710072153f00860038034d0036153f00fb0072000400fb02dd0022123f008600860072011b007216bf034d0072153f00860036034d0036153f00fb00860072034d0036153f00860036034d0036153f00fb00410072003600fb0072003600fb004102dd0036000202dd123f003a0002123f00c300590004003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I12M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I12M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,175,3680,6,8⟩
def valid : Box → Prop := Valid fixed 4 3681 3684 58 13 273200000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3681 3684 58 13 273200000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I12M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I12M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,175,3680,6,8⟩
def valid : Box → Prop := Valid fixed 5 3681 3684 58 13 273200000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3681 3684 58 13 273200000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I12M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I12M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,175,3680,6,8⟩
def valid : Box → Prop := Valid fixed 6 3681 3684 58 13 273200000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3681 3684 58 13 273200000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I12M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I12
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,175,3680,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3681 3684 58 13 273200000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I12M1.covered
  · exact OwnerBox6815_I12M2.covered
  · exact OwnerBox6815_I12M3.covered
  · exact OwnerBox6815_I12M4.covered
  · exact OwnerBox6815_I12M5.covered
  · exact OwnerBox6815_I12M6.covered
theorem linear : LinearChecks 12 39 258 3684 58 13 273200000000000000 := by decide +kernel
theorem high : Gates 3684 58 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3684 58 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3684 58 13≤273200000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3684 58 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3681≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3684 58 13) 273200000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3681 273200000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I12
end MergedPart12
section MergedPart13
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I13M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨42,136,2306,4,5⟩
def valid : Box → Prop := Valid fixed 1 3106 3146 59 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3106 3146 59 13 271000000000000000 7 0x5e0006000000f50043005e0006000000f500430617004c00000043004c00000043061700a500620006000000f50006000000f5025f0043000000a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I13M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I13M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨42,136,2306,4,5⟩
def valid : Box → Prop := Valid fixed 2 3106 3146 59 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3106 3146 59 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I13M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I13M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨42,136,2306,4,5⟩
def valid : Box → Prop := Valid fixed 3 3106 3146 59 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3106 3146 59 13 271000000000000000 6 0x220012000200c30059000201f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I13M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I13M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨42,136,2306,4,5⟩
def valid : Box → Prop := Valid fixed 4 3106 3146 59 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3106 3146 59 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I13M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I13M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨42,136,2306,4,5⟩
def valid : Box → Prop := Valid fixed 5 3106 3146 59 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3106 3146 59 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I13M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I13M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨42,136,2306,4,5⟩
def valid : Box → Prop := Valid fixed 6 3106 3146 59 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3106 3146 59 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I13M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I13
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨42,136,2306,4,5⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3106 3146 59 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I13M1.covered
  · exact OwnerBox6815_I13M2.covered
  · exact OwnerBox6815_I13M3.covered
  · exact OwnerBox6815_I13M4.covered
  · exact OwnerBox6815_I13M5.covered
  · exact OwnerBox6815_I13M6.covered
theorem linear : LinearChecks 12 39 258 3146 59 13 271000000000000000 := by decide +kernel
theorem high : Gates 3146 59 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3146 59 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3146 59 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3146 59 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3106≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3146 59 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3106 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I13
end MergedPart13
section MergedPart14
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I14M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 1 3147 3378 59 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3147 3378 59 13 271000000000000000 11 0xe006000f5000e0076005e0053005e071700f500190006000000dc000000cd00000033004c000000cd000000330717001900f50043000e006000f5000e005e00f500190006000000ac000000cd0000003300ac000000cd000000330517001900f5004306170000007600ac0053007600ac00530717004c006d0019000000430000007600ac0053007600d400530517004c006d001900000043061700a500620006000000ac000000cd00ac000000cd033f00000033001900f50006000000ac000000cd00ac000000cd018700000033001900f5025f00430000004a001900000043004a00000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I14M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I14M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 2 3147 3378 59 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3147 3378 59 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I14M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I14M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3 3147 3378 59 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3147 3378 59 13 271000000000000000 7 0x2200360002123f000200c30059000201f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I14M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I14M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 4 3147 3378 59 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3147 3378 59 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I14M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I14M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 5 3147 3378 59 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3147 3378 59 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I14M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I14M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 6 3147 3378 59 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3147 3378 59 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I14M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I14
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨47,154,3146,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3147 3378 59 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I14M1.covered
  · exact OwnerBox6815_I14M2.covered
  · exact OwnerBox6815_I14M3.covered
  · exact OwnerBox6815_I14M4.covered
  · exact OwnerBox6815_I14M5.covered
  · exact OwnerBox6815_I14M6.covered
theorem linear : LinearChecks 12 39 258 3378 59 13 271000000000000000 := by decide +kernel
theorem high : Gates 3378 59 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3378 59 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3378 59 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3378 59 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3147≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3378 59 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3147 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I14
end MergedPart14
section MergedPart15
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I15M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 1 3379 3543 59 13 271000000000000000
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3379 3543 59 13 271000000000000000 17 0xe007800000053007800000053071700f5000e0076005c000e000a005a004b00e50052005a00e5079700110060005a006000bd005a006000bd0797001100cd00530076005a005e00cd0053071700f500190006000000dc005c007000e5005c006000dc003b00e507970011000000dc012c003b00e0012c07d70000003b00bd00dc0130003b012c00ac013000b507570000003b00bd0797001100cd00ac000000cd003300ac005c005000dc003b00e5005c005000ac003b00e506970011000000dc0000003b00ac009800b500d4009800b506d70000003b00bd00ac0000003b00d4009800b5009806570000003b00bd0697001100cd00ac000000cd00330717001900f50043000e0078000000530060051700f5000e0076005a005e00cd00530076005e0053051700f50019000600000000005c005000ac003b00e5005c005000ac003b00e505970011000000ac0000003b00a40000003b00bd00ac0000003b00a40000003b00bd0597001100cd00ac000000cd00330000005c00ac00e5005c00ac00e504970011000000ac0000003b00a40000003b00bd00ac0000003b00a400b4000000b504570000003b00bd0497001100cd00ac000000cd00330517001900f5004306170000007600000064004c008d0064004c008d07970011005300760000006400ac008d006400ac008d06970011005307170078000000530078000000530717006d001900000043000000760000006400ac008d004c059700110053007600d400530517007800000053004c0517006d001900000043061700a5000e006400f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f000600000000005c00ac00e500ac03af0011000000ac0000003b00b4000000b500b4000000b503e70000003b00bd00ac0000003b000000bd03af001100cd00ac000000d40000003b000000bd00d40000003b000000bd02cf001100cd033f00000033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I15M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I15M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 2 3379 3543 59 13 271000000000000000
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3379 3543 59 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I15M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I15M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3 3379 3543 59 13 271000000000000000
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3379 3543 59 13 271000000000000000 12 0x860038034d00860072034d00710036153f00860038034d0036153f00fb0074000400fb02dd0022123f00860072034d0036153f003600fb00860072034d0036153f003600fb0041003602dd0036000202dd123f003a0002123f00c300590004003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I15M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I15M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 4 3379 3543 59 13 271000000000000000
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3379 3543 59 13 271000000000000000 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I15M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I15M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 5 3379 3543 59 13 271000000000000000
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3379 3543 59 13 271000000000000000 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I15M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I15M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 6 3379 3543 59 13 271000000000000000
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3379 3543 59 13 271000000000000000 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I15M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I15
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨46,153,3378,5,7⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3379 3543 59 13 271000000000000000) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I15M1.covered
  · exact OwnerBox6815_I15M2.covered
  · exact OwnerBox6815_I15M3.covered
  · exact OwnerBox6815_I15M4.covered
  · exact OwnerBox6815_I15M5.covered
  · exact OwnerBox6815_I15M6.covered
theorem linear : LinearChecks 12 39 258 3543 59 13 271000000000000000 := by decide +kernel
theorem high : Gates 3543 59 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3543 59 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3543 59 13≤271000000000000000 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3543 59 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3379≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3543 59 13) 271000000000000000 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3379 271000000000000000
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I15
end MergedPart15
section MergedPart16
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I16M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 1 3544 3560 59 13 271115740514048768
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3544 3560 59 13 271115740514048768 18 0xe007800600053007800000053071700f5000e00760010005c00e5005c0797000e000a005a004b00e50052000a005a004b00e5079700110060005a00540060004b00bd005a006000bd0797001100cd00530076005c005a00110060005e001100cd0053071700f500190006000000dc005c006000dc003b00e5005c006000dc003b00e507970011000000e000dc07d7012c003b00e000ac012c00b507d70000003b00bd00dc00b4003b012c00ac012c0130073700b507570000003b00bd0797001100cd000000ac0011000000cd0033004c005c005000dc003b00e5005c005000ac003b00e506970011000000dc00b400b806d7003b00ac013000a406f700b500d4009800b506d70000003b00bd00ac00b8003b00d4009800b500d4009800b506570000003b00bd0697001100cd00ac000000cd00330717001900f50043000e0078000000530060051700f5000e0076005a005e00cd00530076005e0053051700f500190006000000ac005c005000ac003b00e5005c005000ac003b00e505970011000000ac0000003b00a40000003b00bd00ac0000003b00a40000003b00bd0597001100cd00ac000000cd00330000005c005000ac003b00e5005c00ac00e504970011000000ac0000003b00a40000003b00bd00ac0000003b00a400b4000000b504570000003b00bd0497001100cd00ac000000cd00330517001900f5004306170000007600000064004c008d0064004c008d07970011005300760000006400ac008d006400ac008d06970011005307170078000000530078000000530717006d001900000043000000760000006400ac008d006400ac008d0597001100530076004c005305170078000000530078000000530517006d001900000043061700a5000e0078000000530064033f00f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f000600000000005c00ac00e5005c00ac00e503af0011000000ac0000003b00b4000000b500b4000000b503e70000003b00bd00ac0000003b00b4000000b500b4000000b503770000003b00bd03af001100cd00ac000000d40000003b00b4000000b500b4000000b503070000003b00bd00d40000003b000000bd02cf001100cd033f00ac000000cd0000033f0033001900f50006000000ac000000d40000003b000000bd00d40000003b000000bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I16M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I16M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 2 3544 3560 59 13 271115740514048768
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3544 3560 59 13 271115740514048768 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I16M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I16M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3 3544 3560 59 13 271115740514048768
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3544 3560 59 13 271115740514048768 12 0x860038034d00860072034d00710072153f00860038034d0036153f00fb0074000400fb02dd0022123f00860072034d0036153f00860036034d0036153f00fb00860072034d0036153f003600fb00410072003800fb0036004102dd0036000202dd123f003a0002123f00c300590004003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I16M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I16M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 4 3544 3560 59 13 271115740514048768
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3544 3560 59 13 271115740514048768 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I16M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I16M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 5 3544 3560 59 13 271115740514048768
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3544 3560 59 13 271115740514048768 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I16M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I16M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 6 3544 3560 59 13 271115740514048768
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3544 3560 59 13 271115740514048768 2 0x0 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I16M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I16
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,177,3543,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3544 3560 59 13 271115740514048768) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I16M1.covered
  · exact OwnerBox6815_I16M2.covered
  · exact OwnerBox6815_I16M3.covered
  · exact OwnerBox6815_I16M4.covered
  · exact OwnerBox6815_I16M5.covered
  · exact OwnerBox6815_I16M6.covered
theorem linear : LinearChecks 12 39 258 3560 59 13 271115740514048768 := by decide +kernel
theorem high : Gates 3560 59 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3560 59 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3560 59 13≤271115740514048768 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3560 59 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3544≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3560 59 13) 271115740514048768 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3544 271115740514048768
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I16
end MergedPart16
section MergedPart17
namespace ProximityPrize.SubmissionLower.OwnerBox6815_I17M1
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 1 3561 3599 59 13 272690523638300300
theorem covered : Covered 1 valid ⟨2,5,4,12,0,39,0,258⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 1 3561 3599 59 13 272690523638300300 19 0xe007800600053007800600053071700f5000e00760010005c00e50054005c00e50797000e000a00de005a07d7004b00e5000e0052004b000a005a004b00e5079700110060000a005c004b00540060004b00bd005a006000bd0797001100cd00530076005c0052005a00e5005a069700110060005a006000bd005e0697001100cd0053071700f5001900060000007000dc0797005c006000dc003b00e5005c006000dc003b00e507970011000000e000e000dc07b707d7012c003b00e000ac012c00b507d70000003b00bd00dc00c4003b012c00ac012c00d4013000ad073700b507570000003b00bd0797001100cd000000440000002b00ac07970011000000cd0033004c005c005000dc003b00e5005c005000ac003b00e506970011000000dc00b400ac000000c500ac000000c506b706d7003b00ac013000d4009800ad06f700b500d400b4009800ad009806b700b506d70000003b00bd004c00b8003b00d4009800b500d4009800b506570000003b00bd0697001100cd00ac000000cd00330717001900f50043000e007800000053007800000053051700f5000e0076005a005e00cd00530076005e0053051700f500190006000000ac005c005000ac003b00e5005c005000ac003b00e505970011000000ac00b8003b00d400a400b500a405d70000003b00bd00ac00b800000557003b00a40000003b00bd0597001100cd00ac000000cd003300ac005c005000ac003b00e5005c00ac00e504970011000000ac0000003b00a40000003b00bd00ac0000003b00a400b400a40098000000ad043700b504570000003b00bd0497001100cd00ac000000cd00330517001900f500430617000000760000006400d8012c004b008d0064004c008d079700110053007600000064004c008d006400ac008d0697001100530717007800d400530078000000530717006d001900000043000000760000006400ac008d006400ac008d05970011005300760000004c0011005305170078000000530078000000530517006d001900000043061700a5000e0078000000530064033f00f5000e007600620053007600620053033f00f50019000e006400f5000e006200f50019025f000600000000005c00ac00e5005c00ac00e503af0011000000ac0000003b00b40098000000ad00b500b4000000b503e70000003b00bd00ac0000003b00b4000000b500b4000000b503770000003b00bd03af001100cd000000ac0011000000d40000003b00b4000000b500b4000000b503070000003b00bd00d40000003b00b4000000b500b4000000b502970000003b00bd02cf001100cd033f00ac000000cd00ac000000cd033f0033001900f50006000000ac000000d40000003b00b4000000b500b4000000b5022f0000003b00bd00d40000003b00b4000000b5000001bf0000003b00bd01f7001100cd00ac000000d40000003b000000bd00d40000003b000000bd0117001100cd018700000033001900f5025f00430000007600d40053007600d400530317004c006d0019000000430000007600d4005300d20147004c006d001900000043021700a50417 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I17M1

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I17M2
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 2 3561 3599 59 13 272690523638300300
theorem covered : Covered 2 valid ⟨2,8,4,19,0,59,0,387⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 2 3561 3599 59 13 272690523638300300 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I17M2

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I17M3
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3 3561 3599 59 13 272690523638300300
theorem covered : Covered 3 valid ⟨3,17,6,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 3 3561 3599 59 13 272690523638300300 14 0x9a0088011b008616bf0038034d009200860072011b007216bf034d00710072153f00860038034d0036153f00fb0074000400fb02dd0022123f008600860072011b007216bf034d0072153f00860036034d0036153f00fb00860072034d0036153f00860036034d0036153f00fb00410072003800fb0072003600fb004102dd0036000202dd123f003a0002123f00c300590004003a0002123f000400c3005901f500020c37 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I17M3

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I17M4
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 4 3561 3599 59 13 272690523638300300
theorem covered : Covered 4 valid ⟨4,17,8,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 4 3561 3599 59 13 272690523638300300 2 0x2 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I17M4

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I17M5
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 5 3561 3599 59 13 272690523638300300
theorem covered : Covered 5 valid ⟨5,17,10,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 5 3561 3599 59 13 272690523638300300 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I17M5

namespace ProximityPrize.SubmissionLower.OwnerBox6815_I17M6
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 6 3561 3599 59 13 272690523638300300
theorem covered : Covered 6 valid ⟨6,17,12,38,0,119,0,775⟩ :=
  OwnerTreeCheck6815.covered_of_run fixed 6 3561 3599 59 13 272690523638300300 2 0x4 _ (by decide +kernel)
end ProximityPrize.SubmissionLower.OwnerBox6815_I17M6

namespace ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I17
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioCost6815 PortfolioUniqueCount6815
open MovingSourceBandLeading6815 MovingSourceNativeEnvelope6814
def fixed : Degrees := ⟨53,177,3543,6,8⟩
theorem low_covers (m : ℕ) (hm : 0<m) (hh : m≤6) :
    Covered m (Valid fixed m 3561 3599 59 13 272690523638300300) (rootBox 38 119 775 17 m) := by
  interval_cases m
  · exact OwnerBox6815_I17M1.covered
  · exact OwnerBox6815_I17M2.covered
  · exact OwnerBox6815_I17M3.covered
  · exact OwnerBox6815_I17M4.covered
  · exact OwnerBox6815_I17M5.covered
  · exact OwnerBox6815_I17M6.covered
theorem linear : LinearChecks 12 39 258 3599 59 13 272690523638300300 := by decide +kernel
theorem high : Gates 3599 59 13 24 112 768 ∧
  nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) 3599 59 13/21+
    leading (PortfolioHighOwner6815.degrees 38 119 775) 3599 59 13≤272690523638300300 := by
  unfold Gates
  decide +kernel
open WholeSpaceCube6814 MovingSourceCoupledClearing6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 SecondJetCarrierDichotomy
open RCN234 RCN156
theorem unique_count {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3599 59 13) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ fixed)
    (hFT : 3561≤wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P) :
    P.seeds.card≤max (identityPrice 3599 59 13) 272690523638300300 :=
  PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS fixed hZ 3561 272690523638300300
    (by decide) hFT (by decide) (by decide) (by decide) (by decide) (by decide)
    J hJ hJS hroot hunique linear high low_covers
end ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I17
end MergedPart17
