import ProximityPrize.SubmissionLower.MovingSourceBandLowPackets6814
import ProximityPrize.SubmissionLower.MovingSourceBandRetotal6814

/-! The five exact packet-count obligations of SIX_GAP_TARGETS_6814.
Source selection uses ACTUAL carrier total degree, not a loose envelope.
All interpolation, owner and helper alternatives are discharged. -/
namespace ProximityPrize.SubmissionLower.MovingSourceFiveBands6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open RCN135 RCN136 RCN156 RCN234
open MovingSourceBandGeometry6814 MovingSourceBandHighPackets6814 MovingSourceBandLowPackets6814
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]

theorem band12_55_count (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3568 55 12) (hlo : 3494≤wt residualTotalWeights P.F) :
    P.seeds.card<270000000000000000 :=
  high_packet_count 0 nodes hI P (by omega)

theorem band12_56_count (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3578 56 12) (hlo : 3436≤wt residualTotalWeights P.F) :
    P.seeds.card<270000000000000000 :=
  high_packet_count 1 nodes hI P (by omega)

theorem band12_57_count (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3561 57 12) (hlo : 3348≤wt residualTotalWeights P.F) :
    P.seeds.card<270000000000000000 := by
  by_cases h3382 : wt residualTotalWeights P.F≤3382
  · let Q := P.retotal 3382 h3382 (by decide) (by decide)
    exact low_packet_count 0 nodes hI Q (by change 3043<wt residualTotalWeights P.F; omega)
  by_cases h3411 : wt residualTotalWeights P.F≤3411
  · let Q := P.retotal 3411 h3411 (by decide) (by decide)
    exact low_packet_count 1 nodes hI Q (by change 3382<wt residualTotalWeights P.F; omega)
  by_cases h3429 : wt residualTotalWeights P.F≤3429
  · let Q := P.retotal 3429 h3429 (by decide) (by decide)
    exact low_packet_count 2 nodes hI Q (by change 3411<wt residualTotalWeights P.F; omega)
  exact high_packet_count 2 nodes hI P (by omega)

theorem band13_53_count (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3560 53 13) (hlo : 3416≤wt residualTotalWeights P.F) :
    P.seeds.card<270000000000000000 := by
  by_cases h3429 : wt residualTotalWeights P.F≤3429
  · let Q := P.retotal 3429 h3429 (by decide) (by decide)
    exact low_packet_count 3 nodes hI Q (by change 3411<wt residualTotalWeights P.F; omega)
  exact high_packet_count 3 nodes hI P (by omega)

theorem band13_54_count (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) 3428 54 13) (hlo : 3325≤wt residualTotalWeights P.F) :
    P.seeds.card<270000000000000000 := by
  by_cases h3382 : wt residualTotalWeights P.F≤3382
  · let Q := P.retotal 3382 h3382 (by decide) (by decide)
    exact low_packet_count 4 nodes hI Q (by change 3043<wt residualTotalWeights P.F; omega)
  by_cases h3411 : wt residualTotalWeights P.F≤3411
  · let Q := P.retotal 3411 h3411 (by decide) (by decide)
    exact low_packet_count 5 nodes hI Q (by change 3382<wt residualTotalWeights P.F; omega)
  exact low_packet_count 6 nodes hI P (by change 3411<wt residualTotalWeights P.F; omega)

#print axioms band12_55_count
#print axioms band12_56_count
#print axioms band12_57_count
#print axioms band13_53_count
#print axioms band13_54_count
end
end ProximityPrize.SubmissionLower.MovingSourceFiveBands6814
