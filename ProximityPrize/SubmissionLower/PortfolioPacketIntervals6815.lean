import ProximityPrize.SubmissionLower.OwnerBoxInterval6815_I17
import ProximityPrize.SubmissionLower.SharedBoxInterval6815_I17
import ProximityPrize.SubmissionLower.PortfolioPacketReceipt6815
import ProximityPrize.SubmissionLower.MovingSourceBandPairCount6815
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioPacketIntervals6815
open PortfolioPacketReceipt6815 MovingSourceBandGeometry6815 RCN234 RCN156
set_option maxHeartbeats 1500000
set_option maxRecDepth 40000
def receipt0 : Receipt 3724 58 11 3599 271000000000000000 where
  z := OwnerBoxInterval6815_I00.fixed
  sourceID := ⟨67,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I00.common
  unique_linear := OwnerBoxInterval6815_I00.linear
  small_linear := SharedBoxInterval6815_I00.linear
  high := OwnerBoxInterval6815_I00.high
  unique_cover := OwnerBoxInterval6815_I00.low_covers
  ramified_cover := SharedBoxInterval6815_I00.covered
  repeated := SharedBoxInterval6815_I00.repeated
  triple := SharedBoxInterval6815_I00.triple
  identity := SharedBoxInterval6815_I00.identity
theorem count0 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3724 58 11)
    (hFT : 3599≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt0 nodes hI P hFT
def receipt1 : Receipt 3774 58 12 3347 271000000000000000 where
  z := OwnerBoxInterval6815_I01.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I01.common
  unique_linear := OwnerBoxInterval6815_I01.linear
  small_linear := SharedBoxInterval6815_I01.linear
  high := OwnerBoxInterval6815_I01.high
  unique_cover := OwnerBoxInterval6815_I01.low_covers
  ramified_cover := SharedBoxInterval6815_I01.covered
  repeated := SharedBoxInterval6815_I01.repeated
  triple := SharedBoxInterval6815_I01.triple
  identity := SharedBoxInterval6815_I01.identity
theorem count1 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3774 58 12)
    (hFT : 3347≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt1 nodes hI P hFT
def receipt2 : Receipt 3774 59 12 3294 271000000000000000 where
  z := OwnerBoxInterval6815_I02.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I02.common
  unique_linear := OwnerBoxInterval6815_I02.linear
  small_linear := SharedBoxInterval6815_I02.linear
  high := OwnerBoxInterval6815_I02.high
  unique_cover := OwnerBoxInterval6815_I02.low_covers
  ramified_cover := SharedBoxInterval6815_I02.covered
  repeated := SharedBoxInterval6815_I02.repeated
  triple := SharedBoxInterval6815_I02.triple
  identity := SharedBoxInterval6815_I02.identity
theorem count2 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3774 59 12)
    (hFT : 3294≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt2 nodes hI P hFT
def receipt3 : Receipt 3699 55 13 3322 271000000000000000 where
  z := OwnerBoxInterval6815_I03.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I03.common
  unique_linear := OwnerBoxInterval6815_I03.linear
  small_linear := SharedBoxInterval6815_I03.linear
  high := OwnerBoxInterval6815_I03.high
  unique_cover := OwnerBoxInterval6815_I03.low_covers
  ramified_cover := SharedBoxInterval6815_I03.covered
  repeated := SharedBoxInterval6815_I03.repeated
  triple := SharedBoxInterval6815_I03.triple
  identity := SharedBoxInterval6815_I03.identity
theorem count3 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3699 55 13)
    (hFT : 3322≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt3 nodes hI P hFT
def receipt4 : Receipt 3699 56 13 3266 271000000000000000 where
  z := OwnerBoxInterval6815_I04.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I04.common
  unique_linear := OwnerBoxInterval6815_I04.linear
  small_linear := SharedBoxInterval6815_I04.linear
  high := OwnerBoxInterval6815_I04.high
  unique_cover := OwnerBoxInterval6815_I04.low_covers
  ramified_cover := SharedBoxInterval6815_I04.covered
  repeated := SharedBoxInterval6815_I04.repeated
  triple := SharedBoxInterval6815_I04.triple
  identity := SharedBoxInterval6815_I04.identity
theorem count4 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3699 56 13)
    (hFT : 3266≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt4 nodes hI P hFT
def receipt5 : Receipt 3456 57 13 3213 271000000000000000 where
  z := OwnerBoxInterval6815_I05.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I05.common
  unique_linear := OwnerBoxInterval6815_I05.linear
  small_linear := SharedBoxInterval6815_I05.linear
  high := OwnerBoxInterval6815_I05.high
  unique_cover := OwnerBoxInterval6815_I05.low_covers
  ramified_cover := SharedBoxInterval6815_I05.covered
  repeated := SharedBoxInterval6815_I05.repeated
  triple := SharedBoxInterval6815_I05.triple
  identity := SharedBoxInterval6815_I05.identity
theorem count5 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3456 57 13)
    (hFT : 3213≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt5 nodes hI P hFT
def receipt6 : Receipt 3699 57 13 3457 271000000000000000 where
  z := OwnerBoxInterval6815_I06.fixed
  sourceID := ⟨61,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I06.common
  unique_linear := OwnerBoxInterval6815_I06.linear
  small_linear := SharedBoxInterval6815_I06.linear
  high := OwnerBoxInterval6815_I06.high
  unique_cover := OwnerBoxInterval6815_I06.low_covers
  ramified_cover := SharedBoxInterval6815_I06.covered
  repeated := SharedBoxInterval6815_I06.repeated
  triple := SharedBoxInterval6815_I06.triple
  identity := SharedBoxInterval6815_I06.identity
theorem count6 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3699 57 13)
    (hFT : 3457≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt6 nodes hI P hFT
def receipt7 : Receipt 3378 58 13 3161 271000000000000000 where
  z := OwnerBoxInterval6815_I07.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I07.common
  unique_linear := OwnerBoxInterval6815_I07.linear
  small_linear := SharedBoxInterval6815_I07.linear
  high := OwnerBoxInterval6815_I07.high
  unique_cover := OwnerBoxInterval6815_I07.low_covers
  ramified_cover := SharedBoxInterval6815_I07.covered
  repeated := SharedBoxInterval6815_I07.repeated
  triple := SharedBoxInterval6815_I07.triple
  identity := SharedBoxInterval6815_I07.identity
theorem count7 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3378 58 13)
    (hFT : 3161≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt7 nodes hI P hFT
def receipt8 : Receipt 3543 58 13 3379 271000000000000000 where
  z := OwnerBoxInterval6815_I08.fixed
  sourceID := ⟨61,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I08.common
  unique_linear := OwnerBoxInterval6815_I08.linear
  small_linear := SharedBoxInterval6815_I08.linear
  high := OwnerBoxInterval6815_I08.high
  unique_cover := OwnerBoxInterval6815_I08.low_covers
  ramified_cover := SharedBoxInterval6815_I08.covered
  repeated := SharedBoxInterval6815_I08.repeated
  triple := SharedBoxInterval6815_I08.triple
  identity := SharedBoxInterval6815_I08.identity
theorem count8 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3543 58 13)
    (hFT : 3379≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt8 nodes hI P hFT
def receipt9 : Receipt 3560 58 13 3544 271000000000000000 where
  z := OwnerBoxInterval6815_I09.fixed
  sourceID := ⟨67,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I09.common
  unique_linear := OwnerBoxInterval6815_I09.linear
  small_linear := SharedBoxInterval6815_I09.linear
  high := OwnerBoxInterval6815_I09.high
  unique_cover := OwnerBoxInterval6815_I09.low_covers
  ramified_cover := SharedBoxInterval6815_I09.covered
  repeated := SharedBoxInterval6815_I09.repeated
  triple := SharedBoxInterval6815_I09.triple
  identity := SharedBoxInterval6815_I09.identity
theorem count9 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3560 58 13)
    (hFT : 3544≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt9 nodes hI P hFT
def receipt10 : Receipt 3618 58 13 3561 271000000000000000 where
  z := OwnerBoxInterval6815_I10.fixed
  sourceID := ⟨67,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I10.common
  unique_linear := OwnerBoxInterval6815_I10.linear
  small_linear := SharedBoxInterval6815_I10.linear
  high := OwnerBoxInterval6815_I10.high
  unique_cover := OwnerBoxInterval6815_I10.low_covers
  ramified_cover := SharedBoxInterval6815_I10.covered
  repeated := SharedBoxInterval6815_I10.repeated
  triple := SharedBoxInterval6815_I10.triple
  identity := SharedBoxInterval6815_I10.identity
theorem count10 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3618 58 13)
    (hFT : 3561≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt10 nodes hI P hFT
def receipt11 : Receipt 3680 58 13 3619 273041644927340992 where
  z := OwnerBoxInterval6815_I11.fixed
  sourceID := ⟨66,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I11.common
  unique_linear := OwnerBoxInterval6815_I11.linear
  small_linear := SharedBoxInterval6815_I11.linear
  high := OwnerBoxInterval6815_I11.high
  unique_cover := OwnerBoxInterval6815_I11.low_covers
  ramified_cover := SharedBoxInterval6815_I11.covered
  repeated := SharedBoxInterval6815_I11.repeated
  triple := SharedBoxInterval6815_I11.triple
  identity := SharedBoxInterval6815_I11.identity
theorem count11 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3680 58 13)
    (hFT : 3619≤wt residualTotalWeights P.F) : P.seeds.card≤273041644927340992 :=
  packet_count receipt11 nodes hI P hFT
def receipt12 : Receipt 3684 58 13 3681 273200000000000000 where
  z := OwnerBoxInterval6815_I12.fixed
  sourceID := ⟨65,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I12.common
  unique_linear := OwnerBoxInterval6815_I12.linear
  small_linear := SharedBoxInterval6815_I12.linear
  high := OwnerBoxInterval6815_I12.high
  unique_cover := OwnerBoxInterval6815_I12.low_covers
  ramified_cover := SharedBoxInterval6815_I12.covered
  repeated := SharedBoxInterval6815_I12.repeated
  triple := SharedBoxInterval6815_I12.triple
  identity := SharedBoxInterval6815_I12.identity
theorem count12 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3684 58 13)
    (hFT : 3681≤wt residualTotalWeights P.F) : P.seeds.card≤273200000000000000 :=
  packet_count receipt12 nodes hI P hFT
def receipt13 : Receipt 3146 59 13 3106 271000000000000000 where
  z := OwnerBoxInterval6815_I13.fixed
  sourceID := ⟨57,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I13.common
  unique_linear := OwnerBoxInterval6815_I13.linear
  small_linear := SharedBoxInterval6815_I13.linear
  high := OwnerBoxInterval6815_I13.high
  unique_cover := OwnerBoxInterval6815_I13.low_covers
  ramified_cover := SharedBoxInterval6815_I13.covered
  repeated := SharedBoxInterval6815_I13.repeated
  triple := SharedBoxInterval6815_I13.triple
  identity := SharedBoxInterval6815_I13.identity
theorem count13 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3146 59 13)
    (hFT : 3106≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt13 nodes hI P hFT
def receipt14 : Receipt 3378 59 13 3147 271000000000000000 where
  z := OwnerBoxInterval6815_I14.fixed
  sourceID := ⟨62,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I14.common
  unique_linear := OwnerBoxInterval6815_I14.linear
  small_linear := SharedBoxInterval6815_I14.linear
  high := OwnerBoxInterval6815_I14.high
  unique_cover := OwnerBoxInterval6815_I14.low_covers
  ramified_cover := SharedBoxInterval6815_I14.covered
  repeated := SharedBoxInterval6815_I14.repeated
  triple := SharedBoxInterval6815_I14.triple
  identity := SharedBoxInterval6815_I14.identity
theorem count14 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3378 59 13)
    (hFT : 3147≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt14 nodes hI P hFT
def receipt15 : Receipt 3543 59 13 3379 271000000000000000 where
  z := OwnerBoxInterval6815_I15.fixed
  sourceID := ⟨61,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I15.common
  unique_linear := OwnerBoxInterval6815_I15.linear
  small_linear := SharedBoxInterval6815_I15.linear
  high := OwnerBoxInterval6815_I15.high
  unique_cover := OwnerBoxInterval6815_I15.low_covers
  ramified_cover := SharedBoxInterval6815_I15.covered
  repeated := SharedBoxInterval6815_I15.repeated
  triple := SharedBoxInterval6815_I15.triple
  identity := SharedBoxInterval6815_I15.identity
theorem count15 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3543 59 13)
    (hFT : 3379≤wt residualTotalWeights P.F) : P.seeds.card≤271000000000000000 :=
  packet_count receipt15 nodes hI P hFT
def receipt16 : Receipt 3560 59 13 3544 271115740514048768 where
  z := OwnerBoxInterval6815_I16.fixed
  sourceID := ⟨67,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I16.common
  unique_linear := OwnerBoxInterval6815_I16.linear
  small_linear := SharedBoxInterval6815_I16.linear
  high := OwnerBoxInterval6815_I16.high
  unique_cover := OwnerBoxInterval6815_I16.low_covers
  ramified_cover := SharedBoxInterval6815_I16.covered
  repeated := SharedBoxInterval6815_I16.repeated
  triple := SharedBoxInterval6815_I16.triple
  identity := SharedBoxInterval6815_I16.identity
theorem count16 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3560 59 13)
    (hFT : 3544≤wt residualTotalWeights P.F) : P.seeds.card≤271115740514048768 :=
  packet_count receipt16 nodes hI P hFT
def receipt17 : Receipt 3599 59 13 3561 272690523638300300 where
  z := OwnerBoxInterval6815_I17.fixed
  sourceID := ⟨67,by decide⟩
  source_eq := by decide +kernel
  low_bound := by decide
  cap_bound := by decide
  common := SharedBoxInterval6815_I17.common
  unique_linear := OwnerBoxInterval6815_I17.linear
  small_linear := SharedBoxInterval6815_I17.linear
  high := OwnerBoxInterval6815_I17.high
  unique_cover := OwnerBoxInterval6815_I17.low_covers
  ramified_cover := SharedBoxInterval6815_I17.covered
  repeated := SharedBoxInterval6815_I17.repeated
  triple := SharedBoxInterval6815_I17.triple
  identity := SharedBoxInterval6815_I17.identity
theorem count17 {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3599 59 13)
    (hFT : 3561≤wt residualTotalWeights P.F) : P.seeds.card≤272690523638300300 :=
  packet_count receipt17 nodes hI P hFT
end ProximityPrize.SubmissionLower.PortfolioPacketIntervals6815
