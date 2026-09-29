import ProximityPrize.SubmissionLower.MovingSourceGeneralPair6814

/-! Actual same-source mixed owners supply a shared moving projection and
isolated-point count. The generic cuts, memberships, and finite/separable
projections are constructed. This is not yet a full packet/seed count. -/
namespace ProximityPrize.SubmissionLower.MovingSourceSameSourceCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open RCN002 RCN046 RCN084 RCN095 RCN135 RCN136 RCN207 RCN264 RCN313 RCN341
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceOwnerSplit6814
open MovingSourceCarrierField6814 MovingSourceCarrierZeros6814 MovingSourceCoupledClearing6814
open MovingSourceSameSourceBudget6814 MovingSourceGeneralPair6814 MovingSourceAutomaticProjection6814
open MovingSourceWholeCarrier6814 MovingSourceGeometricBudget6814 MovingSourceRegularRestriction6814
variable {K : Type} [Field K] [CharP K 2130706433]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField Omega
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT
local notation "phi" => RingHom.comp (coefficientEmbedding Omega) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding Omega)

theorem same_source_projection
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (hFT : 995<RCN234.wt RCN156.residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J D : WholeSpaceCube6814.Poly (K:=K)) (hJ : J≠0) (hD : D≠0)
    (hcop : IsRelPrime J D) (hJP : J∣S.P) (hDP : D∣S.P)
    (hJroot : rootEvaluation (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F) J=0)
    (hDroot : rootEvaluation (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F) D=0)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    ∃ base : ∀ C : WholeMovingFamily F Q A, SeparableLiteralCoordinate C.1,
      ∃ unit : AdaptiveUnitProjectionFamily base (ordinaryFlag J) (ordinaryFlag D),
        flagMixed (ordinaryFlag J) (ordinaryFlag D) unitZFlag≤2407 ∧
        flagMixed (ordinaryFlag J) (ordinaryFlag D) unitYZFlag≤28420 ∧
        flagMixed (ordinaryFlag J) (ordinaryFlag D) unitAllFlag≤98890 := by
  have hs := canonical_source_power F S (by rw [hS.2.2.1]; exact hFT) hpos hsmall
    (by rw [hS.2.2.2.2.1]; decide)
  have hjpos := factor_order_pos_of_root (carrierMap F) _ S.P J hs.1 hJP hJroot
  have hdpos := factor_order_pos_of_root (carrierMap F) _ S.P D hs.1 hDP hDroot
  have prices := same_source_pair_prices F S hS J D hJ hD hcop hJP hDP hjpos hdpos
  have hjdiv := helper_dvd_of_generic_root J F (carrierMap F) (carrierMap_zero_iff F)
    (order J) (MvPolynomial.degreeOf_le_iff.mp le_rfl) (carrier_H_nonzero F hpos hsmall) hJroot
  have hddiv := helper_dvd_of_generic_root D F (carrierMap F) (carrierMap_zero_iff F)
    (order D) (MvPolynomial.degreeOf_le_iff.mp le_rfl) (carrier_H_nonzero F hpos hsmall) hDroot
  obtain ⟨B,C,hB,hC,hrel,hBflag,hCflag,hzero⟩ := exists_general_generic_pair J D hJ hD hcop Q A hden hQ hA
  have hmem (V : WholeMovingFamily F Q A) : B∈V.1 ∧ C∈V.1 := by
    let ev := (coordinateEvaluation OmegaT V.1).toRingHom
    have hR : ev (regularDenominator F A)≠0 := by
      intro hz
      exact regularComponent_H_not_mem OmegaT (wholeCarrier F) (regularEquation F Q A)
        (regularDenominator F A) V ((SecondJetComponentRoots.evaluation_zero_iff V.1 _).mp hz)
    have hregular : ev (surfaceMap phi (2*polyH K F))≠0 ∧ ev (lift (2*A))≠0 := by
      simpa only [regularDenominator,map_mul,mul_ne_zero_iff] using hR
    have hF : ev (surfaceMap phi F)=0 :=
      (SecondJetComponentRoots.evaluation_zero_iff V.1 _).mpr
        (regularComponent_G_mem OmegaT (wholeCarrier F) (regularEquation F Q A) (regularDenominator F A) V)
    have hM : ev (regularEquation F Q A)=0 :=
      (SecondJetComponentRoots.evaluation_zero_iff V.1 _).mpr
        (regularComponent_T_mem OmegaT (wholeCarrier F) (regularEquation F Q A) (regularDenominator F A) V)
    have hJraw := movingCut_zero_of_helper_dvd phi ev J F (order J)
      (MvPolynomial.degreeOf_le_iff.mp le_rfl) hjdiv hF hregular.1
      (lift Q) (lift A) (initialCoordinate Omega) hM
    have hDraw := movingCut_zero_of_helper_dvd phi ev D F (order D)
      (MvPolynomial.degreeOf_le_iff.mp le_rfl) hddiv hF hregular.1
      (lift Q) (lift A) (initialCoordinate Omega) hM
    have hz := hzero (CoordinateField OmegaT V.1) ev hregular.2
    exact ⟨(SecondJetComponentRoots.evaluation_zero_iff V.1 B).mp (hz.1.mpr hJraw),
      (SecondJetComponentRoots.evaluation_zero_iff V.1 C).mp (hz.2.mpr hDraw)⟩
  obtain ⟨base,⟨unit⟩⟩ := exists_whole_projection_family (wholeCarrier F) (regularEquation F Q A)
    (regularDenominator F A) B C hB hC hrel (fun V => (hmem V).1) (fun V => (hmem V).2)
    (ordinaryFlag J) (ordinaryFlag D) hBflag hCflag 2130706433
    (prices.1.trans_lt (by decide)) (prices.2.1.trans_lt (by decide))
    (wholeCarrier_derivative_nonzero F hpos hsmall)
  exact ⟨base,unit,prices⟩

theorem same_source_isolated_point_count
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (hFT : 995<RCN234.wt RCN156.residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J D : WholeSpaceCube6814.Poly (K:=K)) (hJ : J≠0) (hD : D≠0)
    (hcop : IsRelPrime J D) (hJP : J∣S.P) (hDP : D∣S.P)
    (hJroot : rootEvaluation (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F) J=0)
    (hDroot : rootEvaluation (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F) D=0)
    (SZ : Source F) (hd : SZ.d=7) (hs : SZ.flag=⟨3252,132,51⟩) (hk : SZ.k=6)
    (p : FlagDegree) (hp : PolynomialInFlag p (wholeCarrier F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (W : FlagDegree) (cut : Poly3T) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → OmegaT))
    (hG : ∀ v∈points, MvPolynomial.eval v (wholeCarrier F)=0)
    (hM : ∀ v∈points, MvPolynomial.eval v (regularEquation F Q A)=0)
    (hregular : ∀ v∈points, MvPolynomial.eval v (regularDenominator F A*SZ.leading phi)≠0)
    (hzero : ∀ v∈points, MvPolynomial.aeval v cut=0)
    (hisolated : ∀ v∈points, IsolatedPoint (wholeCarrier F) (regularEquation F Q A) cut v) :
    7*points.card≤W.zOnly*flagMixed p unitZFlag ⟨3252,132,51⟩+
      7*(W.yz*28420+W.all*98890) := by
  obtain ⟨base,unit,prices⟩ := same_source_projection F S hS hFT hpos hsmall J D hJ hD hcop hJP hDP
    hJroot hDroot Q A hden hQ hA
  have hne : wholeCarrier F≠0 := by
    intro hz
    exact (Fact.out : Irreducible F).ne_zero (wholeCarrier_injective (by simpa only [wholeCarrier,map_zero] using hz))
  have hHdiv : surfaceMap phi (polyH K F)∣regularDenominator F A := by
    apply dvd_mul_of_dvd_left
    rw [map_mul]
    exact dvd_mul_left _ _
  have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
  have hfact : (SZ.k.factorial : OmegaT)≠0 := by
    rw [hk]
    exact SecondJetOwnShape.factorial_ne 6 (by decide)
  have hb := restricted_source_point_count phi F SZ (wholeCarrier F) p hne (dvd_refl _) hp
    2130706433 hunit h2 hfact (lift Q) (lift A) (initialCoordinate Omega)
    (inFlag_map _ hQ) (inFlag_map _ hA) (regularDenominator F A) hHdiv base
    (ordinaryFlag J) (ordinaryFlag D) unit W cut hcut points hG hM hregular hzero hisolated
  rw [hd,hs] at hb
  exact hb.trans (Nat.add_le_add le_rfl (Nat.mul_le_mul_left 7 (Nat.add_le_add
    (Nat.mul_le_mul_left W.yz prices.2.1) (Nat.mul_le_mul_left W.all prices.2.2))))

#print axioms same_source_projection
#print axioms same_source_isolated_point_count
end
end ProximityPrize.SubmissionLower.MovingSourceSameSourceCount6814
