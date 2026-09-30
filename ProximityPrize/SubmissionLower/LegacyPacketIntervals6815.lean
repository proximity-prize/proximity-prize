import ProximityPrize.SubmissionLower.OwnerBoxInterval6815_L12
import ProximityPrize.SubmissionLower.SharedBoxInterval6815_L12
import ProximityPrize.SubmissionLower.PortfolioPacketReceipt6815
import ProximityPrize.SubmissionLower.MovingSourceBandPairCount6815
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.LegacyPacketIntervals6815
open PortfolioPacketReceipt6815 MovingSourceBandGeometry6815 RCN234 RCN156
set_option maxHeartbeats 1500000
set_option maxRecDepth 40000
def receipt0 : Receipt 3571 55 12 3394 248630000000000000 where
  z := OwnerBoxInterval6815_L00.fixed
  sourceID := ⟨61,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L00.common
  unique_linear := OwnerBoxInterval6815_L00.linear
  small_linear := SharedBoxInterval6815_L00.linear
  high := OwnerBoxInterval6815_L00.high
  unique_cover := OwnerBoxInterval6815_L00.low_covers
  ramified_cover := SharedBoxInterval6815_L00.covered
  repeated := SharedBoxInterval6815_L00.repeated
  triple := SharedBoxInterval6815_L00.triple
  identity := SharedBoxInterval6815_L00.identity
theorem count0 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3571 55 12)
    (hFT : 3394≤wt residualTotalWeights P.F) : P.seeds.card≤248630000000000000 :=
  packet_count receipt0 nodes hI P hFT
def receipt1 : Receipt 3749 55 12 3572 258500000000000000 where
  z := OwnerBoxInterval6815_L01.fixed
  sourceID := ⟨67,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L01.common
  unique_linear := OwnerBoxInterval6815_L01.linear
  small_linear := SharedBoxInterval6815_L01.linear
  high := OwnerBoxInterval6815_L01.high
  unique_cover := OwnerBoxInterval6815_L01.low_covers
  ramified_cover := SharedBoxInterval6815_L01.covered
  repeated := SharedBoxInterval6815_L01.repeated
  triple := SharedBoxInterval6815_L01.triple
  identity := SharedBoxInterval6815_L01.identity
theorem count1 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 55 12)
    (hFT : 3572≤wt residualTotalWeights P.F) : P.seeds.card≤258500000000000000 :=
  packet_count receipt1 nodes hI P hFT
def receipt2 : Receipt 3543 56 12 3338 245390000000000000 where
  z := OwnerBoxInterval6815_L02.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L02.common
  unique_linear := OwnerBoxInterval6815_L02.linear
  small_linear := SharedBoxInterval6815_L02.linear
  high := OwnerBoxInterval6815_L02.high
  unique_cover := OwnerBoxInterval6815_L02.low_covers
  ramified_cover := SharedBoxInterval6815_L02.covered
  repeated := SharedBoxInterval6815_L02.repeated
  triple := SharedBoxInterval6815_L02.triple
  identity := SharedBoxInterval6815_L02.identity
theorem count2 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3543 56 12)
    (hFT : 3338≤wt residualTotalWeights P.F) : P.seeds.card≤245390000000000000 :=
  packet_count receipt2 nodes hI P hFT
def receipt3 : Receipt 3749 56 12 3544 260000000000000000 where
  z := OwnerBoxInterval6815_L03.fixed
  sourceID := ⟨67,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L03.common
  unique_linear := OwnerBoxInterval6815_L03.linear
  small_linear := SharedBoxInterval6815_L03.linear
  high := OwnerBoxInterval6815_L03.high
  unique_cover := OwnerBoxInterval6815_L03.low_covers
  ramified_cover := SharedBoxInterval6815_L03.covered
  repeated := SharedBoxInterval6815_L03.repeated
  triple := SharedBoxInterval6815_L03.triple
  identity := SharedBoxInterval6815_L03.identity
theorem count3 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 56 12)
    (hFT : 3544≤wt residualTotalWeights P.F) : P.seeds.card≤260000000000000000 :=
  packet_count receipt3 nodes hI P hFT
def receipt4 : Receipt 3399 57 12 3283 246230000000000000 where
  z := OwnerBoxInterval6815_L04.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L04.common
  unique_linear := OwnerBoxInterval6815_L04.linear
  small_linear := SharedBoxInterval6815_L04.linear
  high := OwnerBoxInterval6815_L04.high
  unique_cover := OwnerBoxInterval6815_L04.low_covers
  ramified_cover := SharedBoxInterval6815_L04.covered
  repeated := SharedBoxInterval6815_L04.repeated
  triple := SharedBoxInterval6815_L04.triple
  identity := SharedBoxInterval6815_L04.identity
theorem count4 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3399 57 12)
    (hFT : 3283≤wt residualTotalWeights P.F) : P.seeds.card≤246230000000000000 :=
  packet_count receipt4 nodes hI P hFT
def receipt5 : Receipt 3516 57 12 3400 257680000000000000 where
  z := OwnerBoxInterval6815_L05.fixed
  sourceID := ⟨61,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L05.common
  unique_linear := OwnerBoxInterval6815_L05.linear
  small_linear := SharedBoxInterval6815_L05.linear
  high := OwnerBoxInterval6815_L05.high
  unique_cover := OwnerBoxInterval6815_L05.low_covers
  ramified_cover := SharedBoxInterval6815_L05.covered
  repeated := SharedBoxInterval6815_L05.repeated
  triple := SharedBoxInterval6815_L05.triple
  identity := SharedBoxInterval6815_L05.identity
theorem count5 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3516 57 12)
    (hFT : 3400≤wt residualTotalWeights P.F) : P.seeds.card≤257680000000000000 :=
  packet_count receipt5 nodes hI P hFT
def receipt6 : Receipt 3749 57 12 3517 263340000000000000 where
  z := OwnerBoxInterval6815_L06.fixed
  sourceID := ⟨61,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L06.common
  unique_linear := OwnerBoxInterval6815_L06.linear
  small_linear := SharedBoxInterval6815_L06.linear
  high := OwnerBoxInterval6815_L06.high
  unique_cover := OwnerBoxInterval6815_L06.low_covers
  ramified_cover := SharedBoxInterval6815_L06.covered
  repeated := SharedBoxInterval6815_L06.repeated
  triple := SharedBoxInterval6815_L06.triple
  identity := SharedBoxInterval6815_L06.identity
theorem count6 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 57 12)
    (hFT : 3517≤wt residualTotalWeights P.F) : P.seeds.card≤263340000000000000 :=
  packet_count receipt6 nodes hI P hFT
def receipt7 : Receipt 3533 53 13 3318 245800000000000000 where
  z := OwnerBoxInterval6815_L07.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L07.common
  unique_linear := OwnerBoxInterval6815_L07.linear
  small_linear := SharedBoxInterval6815_L07.linear
  high := OwnerBoxInterval6815_L07.high
  unique_cover := OwnerBoxInterval6815_L07.low_covers
  ramified_cover := SharedBoxInterval6815_L07.covered
  repeated := SharedBoxInterval6815_L07.repeated
  triple := SharedBoxInterval6815_L07.triple
  identity := SharedBoxInterval6815_L07.identity
theorem count7 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3533 53 13)
    (hFT : 3318≤wt residualTotalWeights P.F) : P.seeds.card≤245800000000000000 :=
  packet_count receipt7 nodes hI P hFT
def receipt8 : Receipt 3749 53 13 3534 256910000000000000 where
  z := OwnerBoxInterval6815_L08.fixed
  sourceID := ⟨61,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L08.common
  unique_linear := OwnerBoxInterval6815_L08.linear
  small_linear := SharedBoxInterval6815_L08.linear
  high := OwnerBoxInterval6815_L08.high
  unique_cover := OwnerBoxInterval6815_L08.low_covers
  ramified_cover := SharedBoxInterval6815_L08.covered
  repeated := SharedBoxInterval6815_L08.repeated
  triple := SharedBoxInterval6815_L08.triple
  identity := SharedBoxInterval6815_L08.identity
theorem count8 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 53 13)
    (hFT : 3534≤wt residualTotalWeights P.F) : P.seeds.card≤256910000000000000 :=
  packet_count receipt8 nodes hI P hFT
def receipt9 : Receipt 3383 54 13 3261 246600000000000000 where
  z := OwnerBoxInterval6815_L09.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L09.common
  unique_linear := OwnerBoxInterval6815_L09.linear
  small_linear := SharedBoxInterval6815_L09.linear
  high := OwnerBoxInterval6815_L09.high
  unique_cover := OwnerBoxInterval6815_L09.low_covers
  ramified_cover := SharedBoxInterval6815_L09.covered
  repeated := SharedBoxInterval6815_L09.repeated
  triple := SharedBoxInterval6815_L09.triple
  identity := SharedBoxInterval6815_L09.identity
theorem count9 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3383 54 13)
    (hFT : 3261≤wt residualTotalWeights P.F) : P.seeds.card≤246600000000000000 :=
  packet_count receipt9 nodes hI P hFT
def receipt10 : Receipt 3505 54 13 3384 252660000000000000 where
  z := OwnerBoxInterval6815_L10.fixed
  sourceID := ⟨61,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L10.common
  unique_linear := OwnerBoxInterval6815_L10.linear
  small_linear := SharedBoxInterval6815_L10.linear
  high := OwnerBoxInterval6815_L10.high
  unique_cover := OwnerBoxInterval6815_L10.low_covers
  ramified_cover := SharedBoxInterval6815_L10.covered
  repeated := SharedBoxInterval6815_L10.repeated
  triple := SharedBoxInterval6815_L10.triple
  identity := SharedBoxInterval6815_L10.identity
theorem count10 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3505 54 13)
    (hFT : 3384≤wt residualTotalWeights P.F) : P.seeds.card≤252660000000000000 :=
  packet_count receipt10 nodes hI P hFT
def receipt11 : Receipt 3627 54 13 3506 259580000000000000 where
  z := OwnerBoxInterval6815_L11.fixed
  sourceID := ⟨61,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L11.common
  unique_linear := OwnerBoxInterval6815_L11.linear
  small_linear := SharedBoxInterval6815_L11.linear
  high := OwnerBoxInterval6815_L11.high
  unique_cover := OwnerBoxInterval6815_L11.low_covers
  ramified_cover := SharedBoxInterval6815_L11.covered
  repeated := SharedBoxInterval6815_L11.repeated
  triple := SharedBoxInterval6815_L11.triple
  identity := SharedBoxInterval6815_L11.identity
theorem count11 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3627 54 13)
    (hFT : 3506≤wt residualTotalWeights P.F) : P.seeds.card≤259580000000000000 :=
  packet_count receipt11 nodes hI P hFT
def receipt12 : Receipt 3749 54 13 3628 265790000000000000 where
  z := OwnerBoxInterval6815_L12.fixed
  sourceID := ⟨66,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_L12.common
  unique_linear := OwnerBoxInterval6815_L12.linear
  small_linear := SharedBoxInterval6815_L12.linear
  high := OwnerBoxInterval6815_L12.high
  unique_cover := OwnerBoxInterval6815_L12.low_covers
  ramified_cover := SharedBoxInterval6815_L12.covered
  repeated := SharedBoxInterval6815_L12.repeated
  triple := SharedBoxInterval6815_L12.triple
  identity := SharedBoxInterval6815_L12.identity
theorem count12 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3749 54 13)
    (hFT : 3628≤wt residualTotalWeights P.F) : P.seeds.card≤265790000000000000 :=
  packet_count receipt12 nodes hI P hFT
end ProximityPrize.SubmissionLower.LegacyPacketIntervals6815
