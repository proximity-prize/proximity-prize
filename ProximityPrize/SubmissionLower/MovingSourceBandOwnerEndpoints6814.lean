import ProximityPrize.SubmissionLower.MovingSourceBandSameOwners6814
import ProximityPrize.SubmissionLower.MovingSourceBandReceipts6814

/-! Concrete <270e15 seed counts for the two-owner branch at all eleven
eligibility endpoints. The actual owner polynomials are supplied by the
small-source exhaustive split; no numerical count is a hypothesis. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandOwnerEndpoints6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6814 MovingSourceBandSameOwners6814 MovingSourceBandReceipts6814
open MovingSourceBandLeading6814 MovingSourceBandPairArithmetic6814
open MovingSourceCarrierField6814 MovingSourceOwnerSplit6814 SecondJetCarrierDichotomy
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K}

theorem same_owner_endpoint_count (i : Fin 11)
    (P : Packet x (cell i).total (cell i).middle (cell i).slope)
    [Fact (Irreducible P.F)]
    (small SZ : Source P.F) (hsmall : Profile small 31 98 995 14 2 3)
    (hSZ : Profile SZ (cell i).B (cell i).U (cell i).L (cell i).s (cell i).k (cell i).n0)
    (hFT : (cell i).L<wt residualTotalWeights P.F)
    (J D : Poly (K:=K)) (hJ : J≠0) (hD : D≠0) (hcop : IsRelPrime J D)
    (hJdiv : J∣small.P) (hDdiv : D∣small.P)
    (hJroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hDroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) D=0) :
    P.seeds.card<270000000000000000 := by
  have hrec := receipts i
  have hL : 1700<(cell i).L := hrec.2.2.1
  have hk : SZ.k<2130706433 := by rw [hSZ.2.2.2.2.1]; exact hrec.2.2.2.1
  have hgates : Gates (cell i).total (cell i).middle (cell i).slope
      (SZ.B-2*SZ.n0) (SZ.U-SZ.n0) (SZ.T-SZ.n0) := by
    rw [hSZ.1,hSZ.2.1,hSZ.2.2.1,hSZ.2.2.2.2.2]
    exact hrec.2.1
  have hh := packet_same_source_owners P (hL.trans hFT) small SZ hsmall
    (by rwa [hSZ.2.2.1]) hk hgates hrec.1 J D hJ hD hcop hJdiv hDdiv hJroot hDroot
  rw [pricedPair_of_profile SZ (cell i) hSZ,leadingPrice_of_profile SZ (cell i) hSZ] at hh
  exact hh.trans_lt hrec.2.2.2.2

#print axioms same_owner_endpoint_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandOwnerEndpoints6814
