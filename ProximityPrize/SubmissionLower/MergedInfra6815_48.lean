import ProximityPrize.SubmissionLower.MergedInfra6815_47
import ProximityPrize.SubmissionLower.MergedOwnerBoxL6815_0
import ProximityPrize.SubmissionLower.MergedSharedBoxL6815_0
import ProximityPrize.SubmissionLower.MergedInfra6815_44
import ProximityPrize.SubmissionLower.MergedOwnerBoxI6815_0
import ProximityPrize.SubmissionLower.MergedSharedBoxI6815_0
import ProximityPrize.SubmissionLower.MergedInfra6815_38
import ProximityPrize.SubmissionLower.MergedInfra6815_42
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_28
import ProximityPrize.SubmissionLower.MergedInfra6815_11
import ProximityPrize.SubmissionLower.MergedInfra6815_20
set_option Elab.async false
section MergedPart0
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
end MergedPart0
section MergedPart1
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
end MergedPart1
section MergedPart2
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
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.CertifiedRegularOffers6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
open MvPolynomial RCN156 RCN234 RCN238
open RelativeCertificate6815 CertifiedFactorInputs6815
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

structure Input (nodes : I ↪ K) (u0 u1 : I → K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Prop where
  degree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071
  agreement : ∀ gamma∈Gamma, 181245≤
    ((Finset.univ : Finset I).filter (fun i =>
      (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card
  noPencil : NoLargeSelectedPencil selected Gamma 131071 80899

variable (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I=262144)
  (selected : K → Polynomial K) (Gamma : Finset K)
  (inp : Input nodes u0 u1 selected Gamma)
include inp hI

theorem relative_count (i : Fin 190) {D L s : ℕ} {H : MvPolynomial (Fin 4) K}
    (F : RCN266.RegularIndex H)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (hR : wt residualSWeights F.val=(RelativeCertifiedOffers6815.offer i).R)
    (hB : wt residualYSWeights F.val=(RelativeCertifiedOffers6815.offer i).B)
    (hlo : (RelativeCertifiedOffers6815.offer i).T0≤wt residualTotalWeights F.val)
    (hhi : wt residualTotalWeights F.val≤(RelativeCertifiedOffers6815.offer i).T1) :
    (RCN140.regularSeeds H selected Gamma F).card≤(RelativeCertifiedOffers6815.offer i).count := by
  apply RelativeCertifiedOffers6815.regular_count K I i F
    (relative_box_of_carrier_box F.val D L s _ _ hbox le_rfl hR.le)
    rfl le_rfl hR.ge hB.le hlo hhi
    (code_weight_lower F.val (RCN167.positiveRFactors_spec H F.val F.property).1.ne_zero
      _ _ hB hR.le)
    nodes u0 u1 hI selected Gamma inp.degree inp.agreement inp.noPencil

def packetOffer (i : Fin 31) : Band := ![
  ⟨11,58,3599,3724,271000000000000000⟩,
  ⟨12,58,3347,3774,271000000000000000⟩,
  ⟨12,59,3294,3774,271000000000000000⟩,
  ⟨13,55,3322,3699,271000000000000000⟩,
  ⟨13,56,3266,3699,271000000000000000⟩,
  ⟨13,57,3213,3456,271000000000000000⟩,
  ⟨13,57,3457,3699,271000000000000000⟩,
  ⟨13,58,3161,3378,271000000000000000⟩,
  ⟨13,58,3379,3543,271000000000000000⟩,
  ⟨13,58,3544,3560,271000000000000000⟩,
  ⟨13,58,3561,3618,271000000000000000⟩,
  ⟨13,58,3619,3680,273041644927340992⟩,
  ⟨13,58,3681,3684,273200000000000000⟩,
  ⟨13,59,3106,3146,271000000000000000⟩,
  ⟨13,59,3147,3378,271000000000000000⟩,
  ⟨13,59,3379,3543,271000000000000000⟩,
  ⟨13,59,3544,3560,271115740514048768⟩,
  ⟨13,59,3561,3599,272690523638300300⟩,
  ⟨12,55,3394,3571,248630000000000000⟩,
  ⟨12,55,3572,3749,258500000000000000⟩,
  ⟨12,56,3338,3543,245390000000000000⟩,
  ⟨12,56,3544,3749,260000000000000000⟩,
  ⟨12,57,3283,3399,246230000000000000⟩,
  ⟨12,57,3400,3516,257680000000000000⟩,
  ⟨12,57,3517,3749,263340000000000000⟩,
  ⟨13,53,3318,3533,245800000000000000⟩,
  ⟨13,53,3534,3749,256910000000000000⟩,
  ⟨13,54,3261,3383,246600000000000000⟩,
  ⟨13,54,3384,3505,252660000000000000⟩,
  ⟨13,54,3506,3627,259580000000000000⟩,
  ⟨13,54,3628,3749,265790000000000000⟩] i
theorem packet_count (i : Fin 31) {D L s : ℕ} {H : MvPolynomial (Fin 4) K}
    (F : RCN266.RegularIndex H) (hDlow : 131072≤D) (hDchar : D<2130706433)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (hR : wt residualSWeights F.val≤(packetOffer i).R)
    (hB : wt residualYSWeights F.val≤(packetOffer i).B)
    (hlo : (packetOffer i).T0≤wt residualTotalWeights F.val)
    (hhi : wt residualTotalWeights F.val≤(packetOffer i).T1) :
    (RCN140.regularSeeds H selected Gamma F).card≤(packetOffer i).count := by
  have gates : 4≤(packetOffer i).R ∧ (packetOffer i).R≤13 ∧
      (packetOffer i).R+2≤(packetOffer i).B ∧ (packetOffer i).B≤59 ∧
      (packetOffer i).B≤(packetOffer i).T1 ∧ (packetOffer i).T1≤4100 := by
    fin_cases i <;> decide
  let P := factorPacket F D L s (packetOffer i).T1 (packetOffer i).B (packetOffer i).R
    hDlow hDchar hbox gates.1 gates.2.1 gates.2.2.1 gates.2.2.2.1
    gates.2.2.2.2.1 gates.2.2.2.2.2 hR hB hhi
    nodes u0 u1 hI selected Gamma inp.degree inp.agreement inp.noPencil
  change P.seeds.card≤(packetOffer i).count
  have hlow : (packetOffer i).T0≤wt residualTotalWeights P.F := hlo
  fin_cases i
  · exact PortfolioPacketIntervals6815.count0 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count1 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count2 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count3 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count4 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count5 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count6 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count7 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count8 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count9 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count10 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count11 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count12 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count13 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count14 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count15 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count16 nodes hI P hlow
  · exact PortfolioPacketIntervals6815.count17 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count0 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count1 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count2 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count3 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count4 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count5 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count6 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count7 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count8 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count9 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count10 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count11 nodes hI P hlow
  · exact LegacyPacketIntervals6815.count12 nodes hI P hlow
end
end ProximityPrize.SubmissionLower.CertifiedRegularOffers6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.CertifiedRegularChoice6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open RCN156 RCN234 RCN095 RCN266 LocatorPhase6800Oracle
open CertifiedRegularOffers6815

inductive Choice where
  | relative (i : Fin 190)
  | packet (i : Fin 31)
  deriving DecidableEq

def price : Choice → ℕ
  | .relative i => (RelativeCertifiedOffers6815.offer i).count
  | .packet i => (packetOffer i).count

def Active : Choice → ℕ → ℕ → ℕ → Prop
  | .relative i,r,v,z =>
      r=(RelativeCertifiedOffers6815.offer i).R ∧
      r+v=(RelativeCertifiedOffers6815.offer i).B ∧
      (RelativeCertifiedOffers6815.offer i).T0≤r+v+z ∧
      r+v+z≤(RelativeCertifiedOffers6815.offer i).T1
  | .packet i,r,v,z =>
      r≤(packetOffer i).R ∧ r+v≤(packetOffer i).B ∧
      (packetOffer i).T0≤r+v+z ∧ r+v+z≤(packetOffer i).T1

instance (c : Choice) (r v z : ℕ) : Decidable (Active c r v z) := by
  cases c <;> unfold Active <;> infer_instance

theorem active_between (c : Choice) (r v lo hi z : ℕ)
    (ha : Active c r v lo) (hb : Active c r v hi) (hl : lo≤z) (hh : z≤hi) :
    Active c r v z := by
  cases c <;> simp only [Active] at ha hb ⊢ <;> omega

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem count (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (inp : Input nodes u0 u1 selected Gamma)
    {D L s : ℕ} {H : MvPolynomial (Fin 4) K} (F : RegularIndex H)
    (hDlow : 131072≤D) (hDchar : D<2130706433)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (c : Choice)
    (ha : Active c (RCN130.regularCumulativeFlag H F).all
      (RCN130.regularCumulativeFlag H F).yz (RCN130.regularCumulativeFlag H F).zOnly) :
    (RCN140.regularSeeds H selected Gamma F).card≤price c := by
  have hc := RCN130.originalCumulativeFlag_cumulative F.val
  have hr : (RCN130.regularCumulativeFlag H F).all=wt residualSWeights F.val := hc.1
  have hy : (RCN130.regularCumulativeFlag H F).all+(RCN130.regularCumulativeFlag H F).yz=
      wt residualYSWeights F.val := by
    simpa only [RCN130.regularCumulativeFlag,Nat.add_comm] using hc.2.1
  have ht : (RCN130.regularCumulativeFlag H F).all+(RCN130.regularCumulativeFlag H F).yz+
      (RCN130.regularCumulativeFlag H F).zOnly=wt residualTotalWeights F.val := by
    simpa only [RCN130.regularCumulativeFlag,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hc.2.2
  cases c with
  | relative i =>
    simp only [Active] at ha
    rw [ht,hy,hr] at ha
    exact relative_count nodes u0 u1 hI selected Gamma inp i F hbox ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  | packet i =>
    simp only [Active] at ha
    rw [ht,hy,hr] at ha
    exact packet_count nodes u0 u1 hI selected Gamma inp i F hDlow hDchar hbox ha.1 ha.2.1 ha.2.2.1 ha.2.2.2

end
end ProximityPrize.SubmissionLower.CertifiedRegularChoice6815
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingFiberSingleCore6815
open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open MovingFiberShape6815 Lower80899.TenPhase
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def cap (slope intercept z : ℕ) : ℕ := slope*z+intercept
def rootIndex (w : ℕ) : Fin 21 := ⟨(w-1)%21,Nat.mod_lt _ (by decide)⟩
def phasePotential (j : ℕ) : Potential := (Lower80899.TenPhase.sound j).potential
def thresholdAt (q : Array ℕ) (j : ℕ) : ℕ := (q[j]?).getD 11193

def Carrier.Correct (c : Carrier) (r v : ℕ) : Prop :=
  c.c0=cost r v 0 ∧ c.c1=cost r v 1 ∧ c.c2=cost r v 2 ∧
  c.c3=cost r v 3 ∧ c.c4=cost r v 4
instance (c : Carrier) (r v : ℕ) : Decidable (c.Correct r v) := by
  unfold Carrier.Correct; infer_instance

def Carrier.eval (c : Carrier) (z : ℕ) : ℕ :=
  if z=0 then c.c0 else if z=1 then c.c1 else if z=2 then c.c2
  else c.c3+(c.c4-c.c3)*(z-3)

theorem Carrier.eval_correct (c : Carrier) (r v z : ℕ)
    (hr : 1 ≤ r) (hc : c.Correct r v) : c.eval z = cost r v z := by
  rcases hc with ⟨h0,h1,h2,h3,h4⟩
  unfold Carrier.eval
  split_ifs with hz0 hz1 hz2
  · simpa only [hz0] using h0
  · simpa only [hz1] using h1
  · simpa only [hz2] using h2
  · rw [h3,h4,raw_affine r v z hr (by omega)]

theorem Carrier.eval_affine (c : Carrier) (lo z : ℕ) (hl : 3 ≤ lo) (hz : lo ≤ z) :
    c.eval z = c.eval lo+(c.c4-c.c3)*(z-lo) := by
  simp only [Carrier.eval,if_neg (show z≠0 by omega),if_neg (show z≠1 by omega),
    if_neg (show z≠2 by omega),if_neg (show lo≠0 by omega),
    if_neg (show lo≠1 by omega),if_neg (show lo≠2 by omega)]
  rw [show z-3=(lo-3)+(z-lo) by omega,Nat.mul_add]
  omega

def rootSlope (w r v : ℕ) : ℕ :=
  (MovingFiberCount6815.receipt (rootIndex w)).slope (r-3) (v-2)
def rootIntercept (w r v : ℕ) : ℕ :=
  (MovingFiberCount6815.receipt (rootIndex w)).intercept (r-3) (v-2)
def rootL (w : ℕ) : ℕ := MovingFiberCount6815.sourceLimit (rootIndex w)
def rootUpper (w r v z : ℕ) : ℕ := rootSlope w r v*z+rootIntercept w r v

def extraChoice (w : ℕ) : CertifiedRegularChoice6815.Choice :=
  if w<222 then .relative ⟨(w-32)%190,Nat.mod_lt _ (by decide)⟩
  else .packet ⟨(w-222)%31,Nat.mod_lt _ (by decide)⟩

def choice (c : Carrier) (w r v z : ℕ) : ℕ :=
  if 32≤w then CertifiedRegularChoice6815.price (extraChoice w)
  else if w=0 then c.eval z else if w≤21 then rootUpper w r v z
  else (phasePotential (w-22)).eval (rawFlag r v z)

def Active (thresholds : Array ℕ) (w r v lo hi : ℕ) : Prop :=
  if 32≤w then w≤252 ∧ CertifiedRegularChoice6815.Active (extraChoice w) r v lo ∧
    CertifiedRegularChoice6815.Active (extraChoice w) r v hi
  else if w=0 then r≤32 ∧ r+v≤149 ∧ r+v+hi≤8121 ∧ BoundaryTailGates6808.Safe r (r+v)
  else if w≤21 then 3 ≤ r ∧ r ≤ 31 ∧ 2 ≤ v ∧ 3 ≤ lo ∧
    rootL w < r+v+lo ∧ r+v ≤ 142 ∧ r+v+hi ≤ 7501
  else w-22 < 7 ∧ thresholdAt thresholds (w-22) ≤ lo
instance (thresholds : Array ℕ) (w r v lo hi : ℕ) : Decidable (Active thresholds w r v lo hi) := by
  unfold Active; infer_instance

def choiceSlope (c : Carrier) (w r v : ℕ) : ℕ :=
  if 32≤w then 0
  else if w=0 then c.c4-c.c3 else if w≤21 then rootSlope w r v
  else (phasePotential (w-22)).totalCoeff

theorem choice_affine (c : Carrier) (w r v lo z : ℕ)
    (hlo : 3 ≤ lo) (hz : lo ≤ z) :
    choice c w r v z = choice c w r v lo + choiceSlope c w r v*(z-lo) := by
  by_cases hn : 32≤w
  · simp only [choice,choiceSlope,if_pos hn,Nat.zero_mul,Nat.add_zero]
  by_cases hw0 : w=0
  · simpa only [choice,choiceSlope,if_neg hn,if_pos hw0] using c.eval_affine lo z hlo hz
  by_cases hw1 : w≤21
  · simp only [choice,choiceSlope,if_neg hn,if_neg hw0,if_pos hw1,rootUpper]
    conv_lhs => rw [show z=lo+(z-lo) by omega]
    ring
  · simp only [choice,choiceSlope,if_neg hn,if_neg hw0,if_neg hw1,Potential.eval,
      rawFlag_total,rawFlag_middle,rawFlag_all]
    conv_lhs => rw [show z=lo+(z-lo) by omega]
    ring

def Cover (c : Carrier) (slope intercept r v : ℕ) (thresholds : Array ℕ) (finish : ℕ) :
    ℕ → List Run → Prop
  | lo,[] => lo=finish
  | lo,x::xs => lo<x.stop ∧ x.stop≤finish ∧ (3≤lo ∨ x.stop=lo+1) ∧
    Active thresholds x.who r v lo (x.stop-1) ∧
    choice c x.who r v lo ≤ cap slope intercept lo ∧
    choice c x.who r v (x.stop-1) ≤ cap slope intercept (x.stop-1) ∧
    Cover c slope intercept r v thresholds finish x.stop xs
instance (c : Carrier) (slope intercept r v : ℕ) (thresholds : Array ℕ) (finish lo : ℕ) (xs : List Run) :
    Decidable (Cover c slope intercept r v thresholds finish lo xs) := by
  induction xs generalizing lo with
  | nil => simp only [Cover]; infer_instance
  | cons x xs ih => simp only [Cover]; infer_instance

theorem active_at (th : Array ℕ) (w r v lo hi z : ℕ)
    (h : Active th w r v lo hi) (hz : lo ≤ z) (hzi : z ≤ hi) : Active th w r v z z := by
  unfold Active at h ⊢
  by_cases hn : 32≤w
  · simp only [if_pos hn] at h ⊢
    have ha := CertifiedRegularChoice6815.active_between (extraChoice w) r v lo hi z h.2.1 h.2.2 hz hzi
    exact ⟨h.1,ha,ha⟩
  simp only [if_neg hn] at h ⊢
  by_cases h0 : w=0
  · simp only [if_pos h0] at h ⊢
    exact ⟨h.1,h.2.1,by omega,h.2.2.2⟩
  · simp only [if_neg h0] at h ⊢
    split_ifs at h ⊢ <;> omega

end ProximityPrize.SubmissionLower.MovingFiberSingleCore6815
end MergedPart5
