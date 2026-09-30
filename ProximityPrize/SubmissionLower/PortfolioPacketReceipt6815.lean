import ProximityPrize.SubmissionLower.PortfolioUniqueCount6815
import ProximityPrize.SubmissionLower.PortfolioRamifiedBoxes6815
namespace ProximityPrize.SubmissionLower.PortfolioPacketReceipt6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 50000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceOwnerSplit6814
open MovingSourceMixedOwnerRouting6814 MovingSourceSameSourceBudget6814
open MovingSourceBandPairArithmetic6814 PortfolioCost6815 PortfolioSource6815
open PortfolioUniqueCount6815 PortfolioSharedCount6815 PortfolioRootFactors6815

def sourceDegrees (i : Fin 75) : Degrees :=
  let p := PortfolioSourceCatalogue6815.profile i
  ⟨p.B,p.U,p.L,p.k,p.n0⟩

structure Receipt (t y r low cap : ℕ) where
  z : Degrees
  sourceID : Fin 75
  source_eq : z=sourceDegrees sourceID
  low_bound : 2985<low
  cap_bound : 1000000000000000≤cap
  common : PortfolioChoice6815.Common z low t y r
  unique_linear : LinearChecks 12 39 258 t y r cap
  small_linear : LinearChecks 3 119 775 t y r cap
  high : Gates t y r 24 112 768 ∧
    nativeScalar (PortfolioHighOwner6815.degrees 38 119 775) t y r/21+
      leading (PortfolioHighOwner6815.degrees 38 119 775) t y r≤cap
  unique_cover : ∀ m, 0<m → m≤6 → PortfolioBoxes6815.Covered m
    (PortfolioBoxCover6815.Valid z m low t y r cap) (rootBox 38 119 775 17 m)
  ramified_cover : PortfolioRamifiedBoxes6815.Covered
    (PortfolioRamifiedBoxes6815.Valid z low t y r cap) PortfolioRamifiedBoxes6815.initialBox
  repeated : weightedPrice z (792*(coefficient t y r 1*38+coefficient t y r 2*136)/2) t y r≤cap
  triple : weightedPrice z (792*(coefficient t y r 1*38+coefficient t y r 2*136)/3) t y r≤cap
  identity : identityPrice t y r≤cap

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r low cap : ℕ}

theorem small_slope_count {x : I → K} (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (hJ : J≠0) (hpos : 0<order J) (hb : slope J≤3)
    (hu : middle J≤119) (ht : total J≤775) (hFT : 775<wt residualTotalWeights P.F)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hc : LinearChecks 3 119 775 t y r cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hn := source_nested J
  have hs : order J=1 := by omega
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤3 ∧ e 1+e 2+e 3≤119 ∧ e 1+e 2+e 3+e 4≤775 := by
    intro e he
    have hb' := (le_weightedTotalDegree slopeWeights he).trans hb
    have hu' := (le_weightedTotalDegree middleWeights he).trans hu
    have ht' := (le_weightedTotalDegree totalWeights he).trans ht
    refine ⟨?_,?_,?_⟩
    · simpa [weight_coords,slopeWeights,Nat.mul_comm] using hb'
    · simpa [weight_coords,middleWeights] using hu'
    · simpa [weight_coords,totalWeights] using ht'
  exact (PortfolioLinearShape6815.packet_count_of_shape P J hJ hs 3 119 775
    (by decide) (by decide) (by decide) hshape hFT hroot hc.1 hc.2.1).trans (max_le_max le_rfl hc.2.2)

theorem shared_count {x : I → K} (C : Receipt t y r low cap)
    (P : Packet x t y r) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ C.z)
    (hFT : low≤wt residualTotalWeights P.F)
    (hne : rootPolynomialMap (carrierMap P.F) S.P≠0)
    (hpow : (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^3∣rootPolynomialMap (carrierMap P.F) S.P)
    (J D : Poly (K:=K)) (hJ : Irreducible J) (hD : Irreducible D)
    (hJS : J∣S.P) (hDS : D∣S.P) (hcop : IsRelPrime J D)
    (hJroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hDroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) D=0) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hF775 : 775<wt residualTotalWeights P.F := by have := C.low_bound; omega
  have hST : S.T=775 := hS.2.2.1
  obtain ⟨hJne,hmJ,hmJs,hJb,hJu,hJt,hJs⟩ := root_factor_data P.F S (by omega) J hJ hJS hJroot
  obtain ⟨hDne,hmD,hmDs,hDb,hDu,hDt,hDs⟩ := root_factor_data P.F S (by omega) D hD hDS hDroot
  rw [hS.1] at hJb hDb
  rw [hS.2.1] at hJu hDu
  rw [hS.2.2.1] at hJt hDt
  rw [hS.2.2.2.1] at hJs hDs
  by_cases hsmallJ : slope J≤3
  · exact small_slope_count P J hJ.ne_zero (by omega) hsmallJ hJu hJt hF775 hJroot C.small_linear
  by_cases hsmallD : slope D≤3
  · exact small_slope_count P D hD.ne_zero (by omega) hsmallD hDu hDt hF775 hDroot C.small_linear
  have hP := source_nonzero P.F S
  have hc := MovingSourceOwnerRouting6814.source_caps P.F S
  rw [hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.1] at hc
  have hp := pair_degrees_le S.P J D hP hJ.ne_zero hD.ne_zero hcop hJS hDS
  have hb : slope J+slope D≤38 := (hp.1 slopeWeights).trans hc.1
  have hu0 : middle J+middle D≤119 := (hp.1 middleWeights).trans hc.2.1
  have ht0 : total J+total D≤775 := (hp.1 totalWeights).trans hc.2.2.1
  have hs0 : order J+order D≤17 := hp.2.trans hc.2.2.2
  have hu : middle J+order J+(middle D+order D)≤136 := by omega
  have ht : total J+order J+(total D+order D)≤792 := by omega
  by_cases hramJ : 2≤PortfolioOwners6815.multiplicity P.F J
  · have hsJ := ramified_order_ge_three P.F S (by omega) (C.low_bound.trans_le hFT) J hJ hJS hJroot hramJ
    exact PortfolioRamifiedBoxes6815.count_of_covered P SZ C.z hZ J D hJ hD hcop
      _ _ hramJ hmD hsJ (by omega) hJs hJt hDt (by omega) rfl rfl hJroot hDroot hb hu ht
      low cap hFT (by have := C.low_bound; omega) C.ramified_cover
  by_cases hramD : 2≤PortfolioOwners6815.multiplicity P.F D
  · have hsD := ramified_order_ge_three P.F S (by omega) (C.low_bound.trans_le hFT) D hD hDS hDroot hramD
    exact PortfolioRamifiedBoxes6815.count_of_covered P SZ C.z hZ D J hD hJ hcop.symm
      _ _ hramD hmJ hsD (by omega) hDs hDt hJt (by omega) rfl rfl hDroot hJroot
      (by omega) (by omega) (by omega) low cap hFT (by have := C.low_bound; omega) C.ramified_cover
  have hmJ1 : (rootPolynomialMap (carrierMap P.F) J).rootMultiplicity (ratio (carrierMap P.F) P.F)=1 := by
    change PortfolioOwners6815.multiplicity P.F J=1; omega
  have hmD1 : (rootPolynomialMap (carrierMap P.F) D).rootMultiplicity (ratio (carrierMap P.F) P.F)=1 := by
    change PortfolioOwners6815.multiplicity P.F D=1; omega
  have hzFT := C.common.1.trans_le hFT
  rcases third_root_cases (rootPolynomialMap (carrierMap P.F)) (ratio (carrierMap P.F) P.F)
    S.P J D hne hJ hD hcop hJS hDS hmJ1 hmD1 hpow with hrep | hrep | ⟨E,hE,hEr,hJE,hDE,hdiv⟩
  · exact repeated_count P SZ C.z hZ hzFT C.common.2.1 C.common.2.2 J D S.P
      hJ.ne_zero hD.ne_zero hP hcop hrep 38 119 775 17 cap hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      hF775 (by decide) hJroot hDroot C.repeated
  · exact repeated_count P SZ C.z hZ hzFT C.common.2.1 C.common.2.2 D J S.P
      hD.ne_zero hJ.ne_zero hP hcop.symm hrep 38 119 775 17 cap hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      hF775 (by decide) hDroot hJroot C.repeated
  · exact triple_count P SZ C.z hZ hzFT C.common.2.1 C.common.2.2 J D E S.P
      hJ.ne_zero hD.ne_zero hE.ne_zero hP hcop hJE hDE hdiv 38 119 775 17 cap hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      hF775 (by decide) hJroot hDroot hEr C.triple

theorem count_from_sources (C : Receipt t y r low cap) (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (hS : Profile S 38 119 775 17 2 3) (hZ : Fits SZ C.z)
    (hFT : low≤wt residualTotalWeights P.F) : P.seeds.card≤cap := by
  have hFchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  have h775 : 775<wt residualTotalWeights P.F := by have := C.low_bound; omega
  have hs := canonical_source_power P.F S (by rw [hS.2.2.1]; exact h775) P.rdegree hFchar
    (by rw [hS.2.2.2.2.1]; decide)
  have hpow : (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^3∣rootPolynomialMap (carrierMap P.F) S.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^3∣(asS S.P).map (carrierMap P.F)
    simpa only [Source.d,hS.2.2.2.2.1] using hs.2
  have hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) S.P=0 :=
    Polynomial.dvd_iff_isRoot.mp ((dvd_pow_self _ (by decide : 3≠0)).trans hpow)
  obtain ⟨J,hJ,hJS,hJroot,hcases⟩ := small_source_first_split
    (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) S.P (source_nonzero P.F S) hroot
  have hmax : max (identityPrice t y r) cap≤cap := max_le C.identity le_rfl
  rcases hcases with huni | ⟨D,hD,hDS,hDr,hcop⟩
  · exact (PortfolioUniqueCount6815.packet_count nodes hI P S SZ 38 119 775 17 hS C.z hZ low cap
      (by decide) hFT C.low_bound (by decide) (by decide) (by decide) C.cap_bound J hJ hJS hJroot huni
      C.unique_linear C.high C.unique_cover).trans hmax
  · exact (shared_count C P S SZ hS hZ hFT hs.1 hpow J D hJ hD hJS hDS hcop hJroot hDr).trans hmax

theorem source_or_count (i : Fin 75) (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r)
    (hFT : (PortfolioSourceCatalogue6815.profile i).L<wt residualTotalWeights P.F) :
    P.seeds.card<1000000000000000 ∨ ∃ S : Source P.F,
      Profile S (PortfolioSourceCatalogue6815.profile i).B (PortfolioSourceCatalogue6815.profile i).U
        (PortfolioSourceCatalogue6815.profile i).L (PortfolioSourceCatalogue6815.profile i).s
        (PortfolioSourceCatalogue6815.profile i).k (PortfolioSourceCatalogue6815.profile i).n0 := by
  let p := PortfolioSourceCatalogue6815.profile i
  rcases exists_helper_or_source p (PortfolioSourceCatalogue6815.shape i) (PortfolioSourceCatalogue6815.kernel i)
    (PortfolioSourceCatalogue6815.positive i) (PortfolioSourceCatalogue6815.dimension i)
    nodes P.u0 P.u1 hI P.F P.irreducible hFT r y t (by have := P.rlow; omega)
    (by have := P.rlow; have := P.ylow; omega) (by have := P.yt; have := P.ylow; have := P.rlow; omega)
    ⟨P.r_weight,P.y_weight,P.total_weight⟩ with ⟨Q,hQ⟩ | hs
  · have small := PortfolioSourceCatalogue6815.small i
    exact Or.inl (PortfolioUniformBudgets6815.helper_count p nodes P small.1 small.2.1 small.2.2.1 small.2.2.2.1 Q hQ)
  · exact Or.inr hs

theorem packet_count (C : Receipt t y r low cap) (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) (hFT : low≤wt residualTotalWeights P.F) : P.seeds.card≤cap := by
  letI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  have h775 : 775<wt residualTotalWeights P.F := by have := C.low_bound; omega
  have primary_eq : PortfolioSourceCatalogue6815.profile ⟨49,by decide⟩=⟨87,775,38,17,119,2,3⟩ := by decide +kernel
  rcases source_or_count ⟨49,by decide⟩ nodes hI P (by rw [primary_eq]; exact h775) with hsmall | ⟨S,hS⟩
  · exact hsmall.le.trans C.cap_bound
  rw [primary_eq] at hS
  have hz : (PortfolioSourceCatalogue6815.profile C.sourceID).L<wt residualTotalWeights P.F := by
    have h := C.common.1.trans_le hFT
    rwa [C.source_eq] at h
  rcases source_or_count C.sourceID nodes hI P hz with hsmall | ⟨SZ,hZ⟩
  · exact hsmall.le.trans C.cap_bound
  apply count_from_sources C nodes hI P S SZ hS _ hFT
  rw [C.source_eq]
  exact ⟨hZ.1,hZ.2.1,hZ.2.2.1,hZ.2.2.2.2.1,hZ.2.2.2.2.2⟩

end
end ProximityPrize.SubmissionLower.PortfolioPacketReceipt6815
