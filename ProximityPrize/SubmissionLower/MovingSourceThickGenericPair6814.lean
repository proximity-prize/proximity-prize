import ProximityPrize.SubmissionLower.MovingSourcePairResultant6814

/-! Actual generic-target coprime cuts with their primary-thickness
property. The same cuts carry the ordinary flags; no desired weighted
count or post-clearing multiplicity is assumed. -/
namespace ProximityPrize.SubmissionLower.MovingSourceThickGenericPair6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open MvPolynomial RCN095 RCN135 RCN136 RCN207 RCN259
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceClearing6814 MovingSourceCoprimeCuts6814 MovingSourceGenericCuts6814
open MovingSourceGeneralPair6814 MovingSourceCoupledClearing6814 MovingSourceThickCuts6814
open MovingSourceGeometricBudget6814 MovingSourceWholeCarrier6814
variable {K : Type} [Field K] [CharP K 2130706433]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField Omega
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT
local notation "phi" => RingHom.comp (coefficientEmbedding Omega) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding Omega)

theorem exists_thick_generic_pair
    (F : MvPolynomial (Fin 4) K) (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    ∃ B C : Poly3T, B≠0 ∧ C≠0 ∧ IsRelPrime B C ∧
      PolynomialInFlag (ordinaryFlag S.P) B ∧ PolynomialInFlag (ordinaryFlag T.P) C ∧
      ∀ (R : Type) [CommRing R] (ev : Poly3T →+* R) (J : Ideal R) [J.IsMaximal] (surface : R),
        ev (wholeCarrier F)∈Ideal.span {surface} →
        ev (surfaceMap phi (2*RCN313.polyH K F))∉J →
        ev (lift (2*A))∉J → ev (regularEquation F Q A)∈J →
        ev B∈Ideal.span {surface} ⊔ J^d ∧ ev C∈Ideal.span {surface} ⊔ J^d := by
  letI : StrongNormalizationMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  let P := coefficients (polynomialEmbedding K) S.P
  let U := coefficients (polynomialEmbedding K) T.P
  let rawP := targetPolynomial P (order S.P) (2*A) Q
  let rawU := targetPolynomial U (order T.P) (2*A) Q
  let B0 := leftGCDQuotient rawP rawU
  let C0 := rightGCDQuotient rawP rawU
  have hp : P≠0 := generic_coefficients_ne_zero K S.P (source_nonzero F S)
  have hu : U≠0 := generic_coefficients_ne_zero K T.P (source_nonzero F T)
  have hnp : P.natDegree≤order S.P := generic_coefficients_degree K S.P (order S.P) le_rfl
  have hnu : U.natDegree≤order T.P := generic_coefficients_degree K T.P (order T.P) le_rfl
  have hPU : IsRelPrime P U := MovingSourceGenericField6814.generic_coefficients_relPrime K
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
      (hmapne hrawP) (generic_target_ordinaryFlag S.P Q A hQ hA)
  · exact flag_of_dvd OmegaT _ _ _ (map_dvd (genericTargetMap Omega) hCdiv)
      (hmapne hrawU) (generic_target_ordinaryFlag T.P Q A hQ hA)
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

#print axioms exists_thick_generic_pair
end
end ProximityPrize.SubmissionLower.MovingSourceThickGenericPair6814
