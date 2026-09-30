import ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L04
import ProximityPrize.SubmissionLower.OwnerTreeCheck6815
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
