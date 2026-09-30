import ProximityPrize.SubmissionLower.MovingSourceExtendedCoefficients6814
namespace ProximityPrize.SubmissionLower.MovingSourceExtendedThickPair6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open MvPolynomial RCN095 RCN135 RCN136 RCN207 RCN259
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceClearing6814 MovingSourceCoprimeCuts6814 MovingSourceGenericCuts6814
open MovingSourceCoupledClearing6814 MovingSourceThickCuts6814
open MovingSourceExtendedCoefficients6814

variable {K E : Type} [Field K] [CharP K 2130706433] [Field E]
variable (f : GenericField K →+* E)
local notation "Omega" => E
local notation "OmegaT" => GenericField E
local notation "Poly3" => MvPolynomial (Fin 3) E
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT
local notation "phi" => RingHom.comp (coefficientEmbedding E) (codeMap f)
local notation "lift" => MvPolynomial.map (coefficientEmbedding E)

def extendedCarrier (F : MvPolynomial (Fin 4) K) : Poly3T := surfaceMap phi F
def extendedEquation (F : MvPolynomial (Fin 4) K) (Q A : Poly3) : Poly3T :=
  movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F))
    (lift Q) (lift A) (initialCoordinate E)
def extendedDenominator (F : MvPolynomial (Fin 4) K) (A : Poly3) : Poly3T :=
  surfaceMap phi (2*RCN313.polyH K F)*lift (2*A)

theorem extendedCarrier_injective : Function.Injective (extendedCarrier f) :=
  surfaceMap_injective phi ((coefficientEmbedding E).injective.comp (codeMap_injective f))

theorem extendedCarrier_derivative_nonzero
    (F : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433) :
    MvPolynomial.pderiv (1 : Fin 3) (extendedCarrier f F)≠0 := by
  rw [extendedCarrier,RCN267.surfaceMap_pderiv_R]
  intro hz
  apply RCN267.R_derivative_nonzero F 2130706433 hpos hsmall
  apply extendedCarrier_injective f
  simpa only [extendedCarrier,map_zero] using hz

theorem extended_target_ordinaryFlag
    (J : WholeSpaceCube6814.Poly (K:=K)) (Q A : Poly3)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag (ordinaryFlag J)
      (genericTargetMap E (targetPolynomial (coefficients (codeMap f) J) (order J) (2*A) Q)) := by
  rw [generic_target_is_movingCut]
  exact movingCut_ordinaryFlag phi J (lift Q) (lift A) (initialCoordinate E)
    (inFlag_map _ hQ) (inFlag_map _ hA)

theorem exists_extended_thick_pair
    (F : MvPolynomial (Fin 4) K) (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    ∃ B C : Poly3T, B≠0 ∧ C≠0 ∧ IsRelPrime B C ∧
      PolynomialInFlag (ordinaryFlag S.P) B ∧ PolynomialInFlag (ordinaryFlag T.P) C ∧
      ∀ (R : Type) [CommRing R] (ev : Poly3T →+* R) (J : Ideal R) [J.IsMaximal] (surface : R),
        ev (extendedCarrier f F)∈Ideal.span {surface} →
        ev (surfaceMap phi (2*RCN313.polyH K F))∉J →
        ev (lift (2*A))∉J → ev (extendedEquation f F Q A)∈J →
        ev B∈Ideal.span {surface} ⊔ J^d ∧ ev C∈Ideal.span {surface} ⊔ J^d := by
  letI : StrongNormalizationMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  let P := coefficients (codeMap f) S.P
  let U := coefficients (codeMap f) T.P
  let rawP := targetPolynomial P (order S.P) (2*A) Q
  let rawU := targetPolynomial U (order T.P) (2*A) Q
  let B0 := leftGCDQuotient rawP rawU
  let C0 := rightGCDQuotient rawP rawU
  have hp : P≠0 := extended_coefficients_ne_zero f S.P (source_nonzero F S)
  have hu : U≠0 := extended_coefficients_ne_zero f T.P (source_nonzero F T)
  have hnp : P.natDegree≤order S.P := extended_coefficients_degree f S.P
  have hnu : U.natDegree≤order T.P := extended_coefficients_degree f T.P
  have hPU : IsRelPrime P U := extended_coefficients_relPrime f
    S.P T.P (source_nonzero F S) hcop
  have hrawP : rawP≠0 := MovingSourceProperness6814.targetPolynomial_ne_zero P _ (2*A) Q hp hnp hden
  have hrawU : rawU≠0 := MovingSourceProperness6814.targetPolynomial_ne_zero U _ (2*A) Q hu hnu hden
  have hPB : rawP=gcd rawP rawU*B0 := left_eq_gcd_mul_leftGCDQuotient rawP rawU
  have hUC : rawU=gcd rawP rawU*C0 := right_eq_gcd_mul_rightGCDQuotient rawP rawU
  have hB0 : B0≠0 := fun hz => hrawP (by rw [hPB,hz,mul_zero])
  have hC0 : C0≠0 := fun hz => hrawU (by rw [hUC,hz,mul_zero])
  have hBdiv : B0∣rawP := ⟨gcd rawP rawU,hPB.trans (mul_comm _ _)⟩
  have hCdiv : C0∣rawU := ⟨gcd rawP rawU,hUC.trans (mul_comm _ _)⟩
  have hmapne {V : Polynomial Poly3} (hV : V≠0) : genericTargetMap Omega V≠0 :=
    fun hz => hV (genericTargetMap_injective Omega (by simpa only [map_zero] using hz))
  refine ⟨genericTargetMap Omega B0,genericTargetMap Omega C0,hmapne hB0,hmapne hC0,
    genericTargetMap_relPrime Omega B0 C0 hB0 (gcdQuotients_isRelPrime hrawP),?_,?_,?_⟩
  · exact flag_of_dvd OmegaT _ _ _ (map_dvd (genericTargetMap Omega) hBdiv)
      (hmapne hrawP) (extended_target_ordinaryFlag f S.P Q A hQ hA)
  · exact flag_of_dvd OmegaT _ _ _ (map_dvd (genericTargetMap Omega) hCdiv)
      (hmapne hrawU) (extended_target_ordinaryFlag f T.P Q A hQ hA)
  · intro R _ ev J _ surface hF hH hdenJ hM
    let ev0 := ev.comp (genericTargetMap Omega)
    have hden0 : ev0 (Polynomial.C (2*A))∉J := by
      simpa only [ev0,RingHom.comp_apply,genericTargetMap_C] using hdenJ
    have hAprime : ev (2*lift A)∉J := by
      simpa only [map_mul,map_ofNat] using hdenJ
    have hleft := source_cut_at_degree_mem_primary phi ev F S (lift Q) (lift A)
      (initialCoordinate Omega) J surface d (order S.P) le_rfl hS hchar hF hH hAprime hM
    have hright := source_cut_at_degree_mem_primary phi ev F T (lift Q) (lift A)
      (initialCoordinate Omega) J surface d (order T.P) le_rfl hT hchar hF hH hAprime hM
    have hl : ev0 rawP∈Ideal.span {surface} ⊔ J^d := by
      simpa only [ev0,rawP,P,RingHom.comp_apply,generic_target_is_movingCut] using hleft
    have hr : ev0 rawU∈Ideal.span {surface} ⊔ J^d := by
      simpa only [ev0,rawU,U,RingHom.comp_apply,generic_target_is_movingCut] using hright
    exact normalized_pair_mem_primary P U _ _ (2*A) Q hp hnp hnu hden hPU ev0 J surface d hden0 hl hr

end
end ProximityPrize.SubmissionLower.MovingSourceExtendedThickPair6814
