import ProximityPrize.SubmissionLower.PortfolioSharedArithmetic6815
import ProximityPrize.SubmissionLower.PortfolioRootFactors6815
namespace ProximityPrize.SubmissionLower.PortfolioSharedCount6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 40000
open scoped BigOperators
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingFiberThreeSources6811 MovingSourcePairEnvelope6814 MovingSourceOwnerSplit6814
open MovingSourceBandPairArithmetic6814 PortfolioCost6815

def weightedPrice (z : Degrees) (bound t y r : ℕ) :=
  (z.d*fixedNumerator t y r (parent t y r)+
    coefficient t y r 0*flagMixed (parent t y r) unitZFlag z.flag+
    z.d*bound)/(3*z.d)+leading z t y r

theorem weighted_price_le (z : Degrees) (p q : FlagDegree) (bound t y r : ℕ)
    (h : PortfolioSharedArithmetic6815.weighted (coefficient t y r 1) (coefficient t y r 2) p q≤bound) :
    pairCost z 1 p q t y r+leading z t y r≤weightedPrice z bound t y r := by
  unfold pairCost weightedPrice
  simp only [mul_one,one_mul,pairNumerator_eq]
  apply Nat.add_le_add_right
  apply Nat.div_le_div_right
  have hh := Nat.mul_le_mul_left z.d h
  unfold PortfolioSharedArithmetic6815.weighted at hh
  nlinarith only [hh]

variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}

theorem root_source (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (hJ : J≠0) (L : ℕ) (hL : total J≤L)
    (hFT : L<wt residualTotalWeights P.F)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0) :
    ∃ S : Source P.F, S.P=J ∧ 1≤S.d := by
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  apply CarrierSizedSource6815.source_of_power_below_carrier P.F L hFT P.rdegree hchar J hJ hL 1 (by decide)
  rw [pow_one]
  change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))∣rootPolynomialMap (carrierMap P.F) J
  exact Polynomial.dvd_iff_isRoot.mpr hroot

theorem pair_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (SZ : Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hZFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (J D : Poly (K:=K)) (hJ : J≠0) (hD : D≠0) (hcop : IsRelPrime J D)
    (L : ℕ) (hJL : total J≤L) (hDL : total D≤L) (hL : L<wt residualTotalWeights P.F)
    (hJroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hDroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) D=0)
    (hJT : (ordinaryFlag J).zOnly+(ordinaryFlag J).yz+(ordinaryFlag J).all≤8192)
    (hDT : (ordinaryFlag D).zOnly+(ordinaryFlag D).yz+(ordinaryFlag D).all≤8192)
    (bound cap : ℕ)
    (hweight : PortfolioSharedArithmetic6815.weighted (coefficient t y r 1) (coefficient t y r 2)
      (ordinaryFlag J) (ordinaryFlag D)≤bound)
    (hfit : weightedPrice z bound t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  obtain ⟨SJ,hSJ,hJd⟩ := root_source P J hJ L hJL hL hJroot
  obtain ⟨SD,hSD,hDd⟩ := root_source P D hD L hDL hL hDroot
  have hp : CumulativeLe (ordinaryFlag SJ.P) (ordinaryFlag J) := by rw [hSJ]; exact ⟨le_rfl,le_rfl,le_rfl⟩
  have hq : CumulativeLe (ordinaryFlag SD.P) (ordinaryFlag D) := by rw [hSD]; exact ⟨le_rfl,le_rfl,le_rfl⟩
  have hcop' : IsRelPrime SJ.P SD.P := by rwa [hSJ,hSD]
  have hc := PortfolioPacketHelpers6815.pair_characteristic_gates _ _ hJT hDT
  exact (pair_count_of_bounds P SZ SJ SD z hZ hZFT hk hg hcop' 1 (by decide) (by decide)
    hJd hDd _ _ hp hq hc.1 hc.2).trans
    (max_le_max le_rfl ((weighted_price_le z _ _ bound t y r hweight).trans hfit))

theorem repeated_weights (J D Q : Poly (K:=K)) (hQ : Q≠0) (hJ : J≠0) (hD : D≠0)
    (hdiv : J^2*D∣Q) (B U L s : ℕ)
    (hB : slope Q≤B) (hU : middle Q≤U) (hL : total Q≤L) (hs : order Q≤s) :
    2*slope J+slope D≤B ∧ 2*middle J+middle D≤U ∧
    2*total J+total D≤L ∧ 2*order J+order D≤s := by
  obtain ⟨E,he⟩ := hdiv
  have hE : E≠0 := by intro hz; exact hQ (by rw [he,hz,mul_zero])
  have hJD := mul_ne_zero (pow_ne_zero 2 hJ) hD
  dsimp only [slope,middle,total,order] at *
  rw [he,weight_mul _ _ _ hJD hE,weight_mul _ _ _ (pow_ne_zero 2 hJ) hD,weight_pow _ _ hJ] at hB hU hL
  rw [he,degreeOf_mul_eq hJD hE,degreeOf_mul_eq (pow_ne_zero 2 hJ) hD,degreeOf_pow_eq _ _ _ hJ] at hs
  omega

theorem triple_weights (J D E Q : Poly (K:=K)) (hQ : Q≠0) (hJ : J≠0) (hD : D≠0) (hE : E≠0)
    (hdiv : J*D*E∣Q) (B U L s : ℕ)
    (hB : slope Q≤B) (hU : middle Q≤U) (hL : total Q≤L) (hs : order Q≤s) :
    slope J+slope D+slope E≤B ∧ middle J+middle D+middle E≤U ∧
    total J+total D+total E≤L ∧ order J+order D+order E≤s := by
  obtain ⟨G,he⟩ := hdiv
  have hG : G≠0 := by intro hz; exact hQ (by rw [he,hz,mul_zero])
  have hJD := mul_ne_zero hJ hD
  have hJDE := mul_ne_zero hJD hE
  dsimp only [slope,middle,total,order] at *
  rw [he,weight_mul _ _ _ hJDE hG,weight_mul _ _ _ hJD hE,weight_mul _ _ _ hJ hD] at hB hU hL
  rw [he,degreeOf_mul_eq hJDE hG,degreeOf_mul_eq hJD hE,degreeOf_mul_eq hJ hD] at hs
  omega

theorem repeated_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (SZ : Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hZFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (J D Q : Poly (K:=K)) (hJ : J≠0) (hD : D≠0) (hQ : Q≠0) (hcop : IsRelPrime J D)
    (hdiv : J^2*D∣Q) (B U L s cap : ℕ)
    (hB : slope Q≤B) (hU : middle Q≤U) (hL : total Q≤L) (hs : order Q≤s)
    (hFT : L<wt residualTotalWeights P.F) (hsize : L+s≤8192)
    (hJroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hDroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) D=0)
    (hfit : weightedPrice z ((L+s)*(coefficient t y r 1*B+coefficient t y r 2*(U+s))/2) t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  obtain ⟨hb,hu,ht,hs'⟩ := repeated_weights J D Q hQ hJ hD hdiv B U L s hB hU hL hs
  have hj := ordinaryFlag_cumulative J
  have hd := ordinaryFlag_cumulative D
  have hw := PortfolioSharedArithmetic6815.repeated_pair (ordinaryFlag J) (ordinaryFlag D)
    (coefficient t y r 1) (coefficient t y r 2) B (U+s) (L+s)
    (by omega) (by unfold PortfolioSharedArithmetic6815.middle; omega)
    (by unfold PortfolioSharedArithmetic6815.total; omega)
  exact pair_count P SZ z hZ hZFT hk hg J D hJ hD hcop L (by omega) (by omega) hFT
    hJroot hDroot (by omega) (by omega) _ cap (by omega) hfit

theorem triple_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (SZ : Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hZFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (J D E Q : Poly (K:=K)) (hJ : J≠0) (hD : D≠0) (hE : E≠0) (hQ : Q≠0)
    (hJD : IsRelPrime J D) (hJE : IsRelPrime J E) (hDE : IsRelPrime D E)
    (hdiv : J*D*E∣Q) (B U L s cap : ℕ)
    (hB : slope Q≤B) (hU : middle Q≤U) (hL : total Q≤L) (hs : order Q≤s)
    (hFT : L<wt residualTotalWeights P.F) (hsize : L+s≤8192)
    (hJroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hDroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) D=0)
    (hEroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) E=0)
    (hfit : weightedPrice z ((L+s)*(coefficient t y r 1*B+coefficient t y r 2*(U+s))/3) t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  obtain ⟨hb,hu,ht,hs'⟩ := triple_weights J D E Q hQ hJ hD hE hdiv B U L s hB hU hL hs
  have hj := ordinaryFlag_cumulative J
  have hd := ordinaryFlag_cumulative D
  have he := ordinaryFlag_cumulative E
  have hw := PortfolioSharedArithmetic6815.triple_pair (ordinaryFlag J) (ordinaryFlag D) (ordinaryFlag E)
    (coefficient t y r 1) (coefficient t y r 2) B (U+s) (L+s)
    (by omega) (by unfold PortfolioSharedArithmetic6815.middle; omega)
    (by unfold PortfolioSharedArithmetic6815.total; omega)
  rcases hw with h | h | h
  · exact pair_count P SZ z hZ hZFT hk hg J D hJ hD hJD L (by omega) (by omega) hFT
      hJroot hDroot (by omega) (by omega) _ cap h hfit
  · exact pair_count P SZ z hZ hZFT hk hg J E hJ hE hJE L (by omega) (by omega) hFT
      hJroot hEroot (by omega) (by omega) _ cap h hfit
  · exact pair_count P SZ z hZ hZFT hk hg D E hD hE hDE L (by omega) (by omega) hFT
      hDroot hEroot (by omega) (by omega) _ cap h hfit

end
end ProximityPrize.SubmissionLower.PortfolioSharedCount6815
