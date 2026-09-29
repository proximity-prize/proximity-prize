import ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814

/-! Use the full specialized carrier, without selecting or separately
charging its geometric irreducible factors. One constructed source pair
contains every regular moving curve and supplies one shared budget. -/
namespace ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN002 RCN046 RCN095 RCN135 RCN136 RCN207 RCN234 RCN156 RCN264 RCN313 RCN341
open SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceGenericCuts6814 MovingSourceCarrierZeros6814 MovingSourceCarrierField6814
open MovingSourceGeometricBudget6814 MovingSourceAutomaticProjection6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))

def wholeCarrier (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 3) OmegaT := surfaceMap phi F

abbrev WholeMovingFamily (F : MvPolynomial (Fin 4) K)
    (quadratic A : MvPolynomial (Fin 3) Omega) := MovingFamily F (wholeCarrier F) quadratic A

theorem wholeCarrier_injective : Function.Injective (wholeCarrier (K:=K)) :=
  surfaceMap_injective phi ((coefficientEmbedding Omega).injective.comp (polynomialEmbedding_injective K))

theorem wholeCarrier_derivative_nonzero [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433) :
    MvPolynomial.pderiv (1 : Fin 3) (wholeCarrier F)≠0 := by
  rw [wholeCarrier,RCN267.surfaceMap_pderiv_R]
  intro hz
  apply RCN267.R_derivative_nonzero F 2130706433 hpos hsmall
  apply wholeCarrier_injective
  simpa only [wholeCarrier,map_zero] using hz

theorem exists_whole_moving_projection [CharP K 2130706433]
    (J Q : WholeSpaceCube6814.Poly (K:=K))
    (hJ : J≠0) (hQ : Q≠0) (hrel : IsRelPrime J Q)
    (hJdegree : J.degreeOf 1≤2) (hQdegree : Q.degreeOf 1≤14)
    (U T : ℕ) (hU : 25≤U) (hUmax : U≤30) (hUT : U≤T) (hT : T≤331)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (hQbounds : ∀ e ∈ Q.support, 2*e 1+e 3≤31 ∧ e 1+e 2+e 3≤98 ∧ e 1+e 2+e 3+e 4≤1700)
    (F : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hJdiv : F∣helper J F 2 0) (hQdiv : F∣helper Q F 14 0)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A) :
    ∃ base : ∀ C : WholeMovingFamily F quadratic A, SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩) := by
  obtain ⟨B,C,hB,hC,hcop,hBflag,hCflag,hzero⟩ := exists_bounded_generic_pair
    J Q hJ hQ hrel hJdegree hQdegree U T (by omega) hUT hJbounds hQbounds
    quadratic A hden hquadratic hA
  have hmem (D : WholeMovingFamily F quadratic A) : B∈D.1 ∧ C∈D.1 := by
    let ev := (coordinateEvaluation OmegaT D.1).toRingHom
    have hR : ev (regularDenominator F A)≠0 := by
      intro hz
      exact regularComponent_H_not_mem OmegaT (wholeCarrier F) (regularEquation F quadratic A)
        (regularDenominator F A) D ((SecondJetComponentRoots.evaluation_zero_iff D.1 _).mp hz)
    have hregular : ev (surfaceMap phi (2*polyH K F))≠0 ∧ ev (lift (2*A))≠0 := by
      simpa only [regularDenominator,map_mul,mul_ne_zero_iff] using hR
    have hF : ev (surfaceMap phi F)=0 :=
      (SecondJetComponentRoots.evaluation_zero_iff D.1 _).mpr
        (regularComponent_G_mem OmegaT (wholeCarrier F) (regularEquation F quadratic A)
          (regularDenominator F A) D)
    have hM : ev (regularEquation F quadratic A)=0 :=
      (SecondJetComponentRoots.evaluation_zero_iff D.1 _).mpr
        (regularComponent_T_mem OmegaT (wholeCarrier F) (regularEquation F quadratic A)
          (regularDenominator F A) D)
    have hJraw := movingCut_zero_of_helper_dvd phi ev J F 2
      (MvPolynomial.degreeOf_le_iff.mp hJdegree) hJdiv hF hregular.1
      (lift quadratic) (lift A) (initialCoordinate Omega) hM
    have hQraw := movingCut_zero_of_helper_dvd phi ev Q F 14
      (MvPolynomial.degreeOf_le_iff.mp hQdegree) hQdiv hF hregular.1
      (lift quadratic) (lift A) (initialCoordinate Omega) hM
    have hz := hzero (CoordinateField OmegaT D.1) ev hregular.2
    exact ⟨(SecondJetComponentRoots.evaluation_zero_iff D.1 B).mp (hz.1.mpr hJraw),
      (SecondJetComponentRoots.evaluation_zero_iff D.1 C).mp (hz.2.mpr hQraw)⟩
  have hc := MovingSourcePrimeFamily6814.source_pair_directional_prices U T hU hUmax hUT hT
  exact exists_whole_projection_family (wholeCarrier F) (regularEquation F quadratic A)
    (regularDenominator F A) B C hB hC hcop (fun D => (hmem D).1) (fun D => (hmem D).2)
    ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ hBflag hCflag 2130706433
    (hc.1.trans_lt (by decide)) (hc.2.1.trans_lt (by decide))
    (wholeCarrier_derivative_nonzero F hpos hsmall)

/-- Actual source selection and the shared WHOLE-carrier budget. No
irreducible geometric carrier or per-geometric-factor price is an input. -/
theorem helper_or_whole_projection [CharP K 2130706433]
    {N : Type} [Fintype N] (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJi : Irreducible J)
    (hmid : 25≤MvPolynomial.weightedTotalDegree middleWeights J)
    (hB : MvPolynomial.weightedTotalDegree slopeWeights J=9) (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hU : 25≤U) (hUmax : U≤30) (hUT : U≤T) (hT : T≤331)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      ∃ base : ∀ C : WholeMovingFamily F quadratic A, SeparableLiteralCoordinate C.1,
        Nonempty (AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩) := by
  rcases exists_helper_or_global_pair nodes u0 u1 hN J hJi hmid hB hJdegree U T hJbounds
    (by omega) F hFT r y t hr hy ht hF hpos hsmall hroot with hhelp | hpair
  · exact Or.inl hhelp
  obtain ⟨Q,hQ,hcop,hJdiv,hQdiv,hQbounds,hQdegree⟩ := hpair
  exact Or.inr (exists_whole_moving_projection J Q hJi.ne_zero hQ hcop hJdegree hQdegree
    U T hU hUmax hUT hT hJbounds hQbounds F hpos hsmall hJdiv hQdiv
    quadratic A hden hquadratic hA)

#print axioms exists_whole_moving_projection
#print axioms helper_or_whole_projection
end
end ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814
