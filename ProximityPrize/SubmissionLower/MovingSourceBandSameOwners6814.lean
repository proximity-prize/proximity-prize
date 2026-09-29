import ProximityPrize.SubmissionLower.MovingSourceBandPairCount6814
import ProximityPrize.SubmissionLower.MovingSourceBandPairArithmetic6814
import ProximityPrize.SubmissionLower.MovingSourceReservedOwnerAlternative6814

/-! Actual two-owner packet count with the new coupled pair price. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandSameOwners6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 30000
open scoped Classical
open RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingSourceBandGeometry6814 MovingSourceBandPairCount6814 MovingSourceBandPairArithmetic6814
open MovingSourceBandLeading6814 MovingSourceBandIdentity6814 MovingSourcePairStageSupplier6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCarrierField6814
open MovingSourceOwnerSplit6814 MovingSourceOwnerRouting6814 MovingSourceSameSourceBudget6814
open MovingSourceCoupledClearing6814 MovingSourceNativeEnvelope6814 MovingSourceUniformPairBudget6814
open WholeSpaceUniqueOwnerAlternative6814 WholeSpacePowerSourcePair6814
open SecondJetCoefficients SecondJetCarrierDichotomy
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}

theorem packet_same_source_owners
    (P : Packet x t y r) [Fact (Irreducible P.F)] (hsmallT : 1700<wt residualTotalWeights P.F)
    (small SZ : Source P.F) (hsmall : Profile small 31 98 995 14 2 3)
    (hFT : SZ.T<wt residualTotalWeights P.F) (hZd : SZ.k<2130706433)
    (hgates : Gates t y r (SZ.B-2*SZ.n0) (SZ.U-SZ.n0) (SZ.T-SZ.n0))
    (hc : coefficient t y r 1≤5*coefficient t y r 2)
    (J D : Poly (K:=K)) (hJ : J≠0) (hD : D≠0) (hcop : IsRelPrime J D) (hJdiv : J∣small.P) (hDdiv : D∣small.P)
    (hJroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hDroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) D=0) :
    P.seeds.card≤max (identityPrice t y r) (pricedPair SZ 1 26233 98890 t y r+leadingPrice SZ t y r) := by
  have hFchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega : r<2130706433)
  have hpower := canonical_source_power P.F small (by rw [hsmall.2.2.1]; omega) P.rdegree hFchar
    (by rw [hsmall.2.2.2.2.1]; decide)
  have hjpos := factor_order_pos_of_root (carrierMap P.F) _ small.P J hpower.1 hJdiv hJroot
  have hdpos := factor_order_pos_of_root (carrierMap P.F) _ small.P D hpower.1 hDdiv hDroot
  have hprices := same_source_pair_prices P.F small hsmall J D hJ hD hcop hJdiv hDdiv hjpos hdpos
  have hdegree := pair_degrees_le small.P J D (source_nonzero P.F small) hJ hD hcop hJdiv hDdiv
  have hT := (hdegree.1 totalWeights).trans (source_caps P.F small).2.2.1
  rw [hsmall.2.2.1] at hT
  have hJpow : (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS J).map (carrierMap P.F) := by
    rw [pow_one]
    change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))∣rootPolynomialMap (carrierMap P.F) J
    exact Polynomial.dvd_iff_isRoot.mpr hJroot
  have hDpow : (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS D).map (carrierMap P.F) := by
    rw [pow_one]
    change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))∣rootPolynomialMap (carrierMap P.F) D
    exact Polynomial.dvd_iff_isRoot.mpr hDroot
  obtain ⟨SJ,hSJ,hJd⟩ := source_of_small_power P.F (by omega) P.rdegree hFchar J hJ
    (by change MvPolynomial.weightedTotalDegree totalWeights J≤1700; omega) 1 (by decide) hJpow
  obtain ⟨SD,hSD,hDd⟩ := source_of_small_power P.F (by omega) P.rdegree hFchar D hD
    (by change MvPolynomial.weightedTotalDegree totalWeights D≤1700; omega) 1 (by decide) hDpow

  have hcount := pair_packet_count P SZ SJ SD hFT hZd hgates (by rwa [hSJ,hSD]) 1
    (by decide) (by decide) hJd hDd
    (by rw [hSJ,hSD]; exact hprices.1.trans (by decide))
    (by simpa only [hSJ,hSD,one_mul] using hprices.2.1)
  obtain ⟨hj,hd,hb,hu,ht⟩ := same_source_flag_budgets P.F small hsmall J D hJ hD hcop hJdiv hDdiv hjpos hdpos
  have hcost := pairStageCost_le_joint SZ SJ SD t y r
    (by simpa only [hSJ] using hj) (by simpa only [hSD] using hd)
    (by simpa only [hSJ,hSD] using hb) (by simpa only [hSJ,hSD] using hu)
    (by simpa only [hSJ,hSD] using ht) hc
  exact hcount.trans (max_le_max le_rfl (Nat.add_le_add_right hcost _))

#print axioms packet_same_source_owners
end
end ProximityPrize.SubmissionLower.MovingSourceBandSameOwners6814
