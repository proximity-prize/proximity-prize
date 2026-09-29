import ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814

/-! Gcd-normalized generic moving cuts for arbitrary coprime source
factors. The flags are derived from each factor's actual weights and
therefore retain the same-source coupling proved in the previous module. -/
namespace ProximityPrize.SubmissionLower.MovingSourceGeneralPair6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open MvPolynomial RCN095 RCN135 RCN136 RCN207
open MovingSourceClearing6814 MovingSourceCoprimeCuts6814 MovingSourceGenericCuts6814
open MovingSourceCoupledClearing6814
variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField Omega
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT
local notation "phi" => RingHom.comp (coefficientEmbedding Omega) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding Omega)

theorem generic_target_ordinaryFlag
    (J : WholeSpaceCube6814.Poly (K:=K)) (Q A : Poly3)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag (ordinaryFlag J)
      (genericTargetMap Omega (targetPolynomial (coefficients (polynomialEmbedding K) J) (order J) (2*A) Q)) := by
  rw [generic_target_is_movingCut]
  exact movingCut_ordinaryFlag phi J (lift Q) (lift A) (initialCoordinate Omega)
    (inFlag_map _ hQ) (inFlag_map _ hA)

theorem exists_general_generic_pair
    (J D : WholeSpaceCube6814.Poly (K:=K)) (hJ : J≠0) (hD : D≠0) (hcop : IsRelPrime J D)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    ∃ B C : Poly3T, B≠0 ∧ C≠0 ∧ IsRelPrime B C ∧
      PolynomialInFlag (ordinaryFlag J) B ∧ PolynomialInFlag (ordinaryFlag D) C ∧
      ∀ (E : Type*) [Field E] (ev : Poly3T →+* E), ev (lift (2*A))≠0 →
        ((ev B=0 ↔ ev (movingCut phi J (order J) (lift Q) (lift A) (initialCoordinate Omega))=0) ∧
         (ev C=0 ↔ ev (movingCut phi D (order D) (lift Q) (lift A) (initialCoordinate Omega))=0)) := by
  letI : StrongNormalizationMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  have hj := generic_coefficients_ne_zero K J hJ
  have hd := generic_coefficients_ne_zero K D hD
  have hnj := generic_coefficients_degree K J (order J) le_rfl
  have hnd := generic_coefficients_degree K D (order D) le_rfl
  have hc := MovingSourceGenericField6814.generic_coefficients_relPrime K J D hJ hcop
  obtain ⟨B0,C0,hB0,hC0,hrel0,hBdiv,hCdiv,hzero⟩ := MovingSourceSaturation6814.exists_coprime_cleared_pair
    (coefficients (polynomialEmbedding K) J) (coefficients (polynomialEmbedding K) D)
    (order J) (order D) (2*A) Q hj hd hnj hnd hden hc
  have hjraw := MovingSourceProperness6814.targetPolynomial_ne_zero _ (order J) (2*A) Q hj hnj hden
  have hdraw := MovingSourceProperness6814.targetPolynomial_ne_zero _ (order D) (2*A) Q hd hnd hden
  have hrawne {P : Polynomial Poly3} (hp : P≠0) : genericTargetMap Omega P≠0 :=
    fun hz => hp (genericTargetMap_injective Omega (by simpa only [map_zero] using hz))
  refine ⟨genericTargetMap Omega B0,genericTargetMap Omega C0,hrawne hB0,hrawne hC0,
    genericTargetMap_relPrime Omega B0 C0 hB0 hrel0,?_,?_,?_⟩
  · exact flag_of_dvd OmegaT _ _ _ (map_dvd (genericTargetMap Omega) hBdiv)
      (hrawne hjraw) (generic_target_ordinaryFlag J Q A hQ hA)
  · exact flag_of_dvd OmegaT _ _ _ (map_dvd (genericTargetMap Omega) hCdiv)
      (hrawne hdraw) (generic_target_ordinaryFlag D Q A hQ hA)
  · intro E _ ev hev
    have hh := hzero E (ev.comp (genericTargetMap Omega)) (by
      simpa only [RingHom.comp_apply,genericTargetMap_C] using hev)
    change (ev (genericTargetMap Omega B0)=0 ↔ ev (genericTargetMap Omega
        (targetPolynomial (coefficients (polynomialEmbedding K) J) (order J) (2*A) Q))=0) ∧
      (ev (genericTargetMap Omega C0)=0 ↔ ev (genericTargetMap Omega
        (targetPolynomial (coefficients (polynomialEmbedding K) D) (order D) (2*A) Q))=0) at hh
    rw [generic_target_is_movingCut,generic_target_is_movingCut] at hh
    exact hh

#print axioms exists_general_generic_pair
end
end ProximityPrize.SubmissionLower.MovingSourceGeneralPair6814
