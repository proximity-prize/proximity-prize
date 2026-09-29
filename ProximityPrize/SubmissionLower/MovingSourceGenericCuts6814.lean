import ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814

/-! The generic moving target is the actual affine target substitution.
Its ordinary clearing flags survive coefficient extension and gcd removal. -/
namespace ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial RCN095 RCN135 RCN136 RCN207
open MovingSourceClearing6814 MovingSourceCoprimeCuts6814

variable (E : Type*) [Field E]

theorem genericTargetMap_C_X (i : Fin 3) :
    genericTargetMap E (Polynomial.C (MvPolynomial.X i))=MvPolynomial.X i := by
  have hi : (MvPolynomial.finSuccEquiv E 3).symm (Polynomial.C (MvPolynomial.X i))=
      MvPolynomial.X i.succ := by
    apply (MvPolynomial.finSuccEquiv E 3).injective
    rw [AlgEquiv.apply_symm_apply,MvPolynomial.finSuccEquiv_X_succ]
  change surfaceMap (polynomialEmbedding E) ((MvPolynomial.finSuccEquiv E 3).symm _)=_
  rw [hi,surfaceMap_X_succ]

theorem genericTargetMap_C (P : MvPolynomial (Fin 3) E) :
    genericTargetMap E (Polynomial.C P)=MvPolynomial.map (coefficientEmbedding E) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hc : (MvPolynomial.finSuccEquiv E 3).symm (Polynomial.C (MvPolynomial.C c))=
        MvPolynomial.C c := by
      apply (MvPolynomial.finSuccEquiv E 3).injective
      simp [MvPolynomial.finSuccEquiv_apply]
    change surfaceMap (polynomialEmbedding E) ((MvPolynomial.finSuccEquiv E 3).symm _)=_
    rw [hc,surfaceMap_C,MvPolynomial.map_C]
    rfl
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => simp only [map_mul,hP,genericTargetMap_C_X,MvPolynomial.map_X]

theorem genericTargetMap_X :
    genericTargetMap E Polynomial.X=MvPolynomial.C (initialCoordinate E) := by
  have hx : (MvPolynomial.finSuccEquiv E 3).symm Polynomial.X=MvPolynomial.X 0 := by
    apply (MvPolynomial.finSuccEquiv E 3).injective
    rw [AlgEquiv.apply_symm_apply,MvPolynomial.finSuccEquiv_X_zero]
  change surfaceMap (polynomialEmbedding E) ((MvPolynomial.finSuccEquiv E 3).symm _)=_
  rw [hx,surfaceMap_X_zero]
  rfl

theorem genericTargetMap_eq_eval :
    genericTargetMap E=Polynomial.eval₂RingHom (MvPolynomial.map (coefficientEmbedding E))
      (MvPolynomial.C (initialCoordinate E)) := by
  apply Polynomial.ringHom_ext
  · intro P
    change genericTargetMap E (Polynomial.C P)=Polynomial.eval₂ _ _ (Polynomial.C P)
    rw [Polynomial.eval₂_C]
    exact genericTargetMap_C E P
  · change genericTargetMap E Polynomial.X=Polynomial.eval₂ _ _ Polynomial.X
    rw [Polynomial.eval₂_X]
    exact genericTargetMap_X E

section Sources
variable {K : Type*} [Field K]

theorem map_coefficients {L : Type*} [Field L] (f : E →+* L)
    (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K)) :
    (coefficients phi P).map (MvPolynomial.map f)=coefficients (f.comp phi) P := by
  have he : (MvPolynomial.map f).comp (surfaceMap phi)=surfaceMap (f.comp phi) := by
    apply RingHom.ext
    intro A
    simp only [surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]
  rw [coefficients,Polynomial.map_map,he]
  rfl

theorem generic_target_is_movingCut
    (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (s : ℕ) (quadratic A : MvPolynomial (Fin 3) E) :
    genericTargetMap E (targetPolynomial (coefficients phi P) s (2*A) quadratic)=
      movingCut ((coefficientEmbedding E).comp phi) P s
        (MvPolynomial.map (coefficientEmbedding E) quadratic)
        (MvPolynomial.map (coefficientEmbedding E) A) (initialCoordinate E) := by
  rw [genericTargetMap_eq_eval]
  change Polynomial.eval₂ _ _ (targetPolynomial _ _ _ _)=_
  rw [eval_targetPolynomial,map_coefficients]
  simp only [map_mul,map_ofNat,movingCut]

theorem generic_target_flag
    (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (B U T s : ℕ) (hBU : B ≤ U) (hUT : U ≤ T) (hsB : 2*s ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T)
    (quadratic A : MvPolynomial (Fin 3) E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag ⟨T-U,U-B+s,B⟩
      (genericTargetMap E (targetPolynomial (coefficients phi P) s (2*A) quadratic)) := by
  rw [generic_target_is_movingCut]
  exact movingCut_flag _ P B U T s hBU hUT hsB hP _ _ _
    (inFlag_map _ hQ) (inFlag_map _ hA)

end Sources

theorem flag_of_dvd (P Q : MvPolynomial (Fin 3) E) (p : FlagDegree)
    (hdiv : P ∣ Q) (hQ : Q≠0) (hflag : PolynomialInFlag p Q) : PolynomialInFlag p P := by
  have hw (w : Fin 3 → ℕ) (c : ℕ)
      (hc : ∀ e ∈ Q.support, Finsupp.weight w e ≤ c) :
      ∀ e ∈ P.support, Finsupp.weight w e ≤ c := by
    intro e he
    have h1 : Finsupp.weight w e ≤ weightedTotalDegree w P := Finset.le_sup he
    have h2 := RCN071.weightedTotalDegree_le_of_dvd_fin3 w P Q hdiv hQ
    have h3 : weightedTotalDegree w Q ≤ c := Finset.sup_le hc
    exact h1.trans (h2.trans h3)
  intro e he
  refine ⟨?_,?_,?_⟩
  · have hh := hw flagSWeights p.all (by
      intro d hd
      simpa [flag_weight_fin3,flagSWeights] using (hflag d hd).1) e he
    simpa [flag_weight_fin3,flagSWeights] using hh
  · have hh := hw flagYSWeights (p.yz+p.all) (by
      intro d hd
      simpa [flag_weight_fin3,flagYSWeights] using (hflag d hd).2.1) e he
    simpa [flag_weight_fin3,flagYSWeights] using hh
  · have hh := hw flagTotalWeights (p.zOnly+p.yz+p.all) (by
      intro d hd
      simpa [flag_weight_fin3,flagTotalWeights] using (hflag d hd).2.2) e he
    simpa [flag_weight_fin3,flagTotalWeights] using hh

/-- Gcd-normalized cuts inherit the same flags after the generic target
extension, by divisibility; no additional degree cost is charged. -/
theorem normalized_target_flag {K : Type*} [Field K]
    (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (B U T s : ℕ) (hBU : B ≤ U) (hUT : U ≤ T) (hsB : 2*s ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T)
    (quadratic A : MvPolynomial (Fin 3) E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (V : Polynomial (MvPolynomial (Fin 3) E))
    (hdiv : V ∣ targetPolynomial (coefficients phi P) s (2*A) quadratic)
    (hne : targetPolynomial (coefficients phi P) s (2*A) quadratic≠0) :
    PolynomialInFlag ⟨T-U,U-B+s,B⟩ (genericTargetMap E V) := by
  apply flag_of_dvd (GenericField E) _ _ _ (map_dvd (genericTargetMap E) hdiv)
  · intro hz
    exact hne (genericTargetMap_injective E (by simpa only [map_zero] using hz))
  · exact generic_target_flag E phi P B U T s hBU hUT hsB hP quadratic A hQ hA

section ActualPair
variable {K : Type*} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField Omega
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT

/-- Actual nonzero coprime generic moving cuts, with the claimed flags
and the exact regular-locus zero correspondence. This is the algebraic
input to the remaining shared curve-family degree/pole count. -/
theorem exists_bounded_generic_pair
    (J Q : WholeSpaceCube6814.Poly (K := K))
    (hJ : J≠0) (hQ : Q≠0) (hrel : IsRelPrime J Q)
    (hJdegree : J.degreeOf 1 ≤ 2) (hQdegree : Q.degreeOf 1 ≤ 14)
    (U T : ℕ) (hJU : 9 ≤ U) (hUT : U ≤ T)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3 ≤ 9 ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T)
    (hQbounds : ∀ e ∈ Q.support, 2*e 1+e 3 ≤ 31 ∧ e 1+e 2+e 3 ≤ 98 ∧ e 1+e 2+e 3+e 4 ≤ 1700)
    (quadratic A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic)
    (hAflag : PolynomialInFlag unitYZFlag A) :
    ∃ B C : Poly3T, B≠0 ∧ C≠0 ∧ IsRelPrime B C ∧
      PolynomialInFlag ⟨T-U,U-9+2,9⟩ B ∧ PolynomialInFlag ⟨1602,81,31⟩ C ∧
      ∀ (L : Type*) [Field L] (ev : Poly3T →+* L),
        ev (MvPolynomial.map (coefficientEmbedding Omega) (2*A))≠0 →
        ((ev B=0 ↔ ev (movingCut ((coefficientEmbedding Omega).comp (polynomialEmbedding K)) J 2
            (MvPolynomial.map (coefficientEmbedding Omega) quadratic)
            (MvPolynomial.map (coefficientEmbedding Omega) A) (initialCoordinate Omega))=0) ∧
         (ev C=0 ↔ ev (movingCut ((coefficientEmbedding Omega).comp (polynomialEmbedding K)) Q 14
            (MvPolynomial.map (coefficientEmbedding Omega) quadratic)
            (MvPolynomial.map (coefficientEmbedding Omega) A) (initialCoordinate Omega))=0)) := by
  letI : StrongNormalizationMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  have hj := generic_coefficients_ne_zero K J hJ
  have hq := generic_coefficients_ne_zero K Q hQ
  have hnj := generic_coefficients_degree K J 2 hJdegree
  have hnq := generic_coefficients_degree K Q 14 hQdegree
  have hcop := MovingSourceGenericField6814.generic_coefficients_relPrime K J Q hJ hrel
  obtain ⟨B0,C0,hB0,hC0,hrel0,hBdiv,hCdiv,hzero⟩ := MovingSourceSaturation6814.exists_coprime_cleared_pair
    (coefficients (polynomialEmbedding K) J) (coefficients (polynomialEmbedding K) Q)
    2 14 (2*A) quadratic hj hq hnj hnq hden hcop
  have hjraw := MovingSourceProperness6814.targetPolynomial_ne_zero _ 2 (2*A) quadratic hj hnj hden
  have hqraw := MovingSourceProperness6814.targetPolynomial_ne_zero _ 14 (2*A) quadratic hq hnq hden
  refine ⟨genericTargetMap Omega B0,genericTargetMap Omega C0,?_,?_,
    genericTargetMap_relPrime Omega B0 C0 hB0 hrel0,?_,?_,?_⟩
  · intro hz
    exact hB0 (genericTargetMap_injective Omega (by simpa only [map_zero] using hz))
  · intro hz
    exact hC0 (genericTargetMap_injective Omega (by simpa only [map_zero] using hz))
  · exact normalized_target_flag Omega (polynomialEmbedding K) J 9 U T 2 hJU hUT
      (by omega) hJbounds quadratic A hquadratic hAflag B0 hBdiv hjraw
  · exact normalized_target_flag Omega (polynomialEmbedding K) Q 31 98 1700 14
      (by omega) (by omega) (by omega) hQbounds quadratic A hquadratic hAflag C0 hCdiv hqraw
  · intro L _ ev hev
    have hh := hzero L (ev.comp (genericTargetMap Omega)) (by
      simpa only [RingHom.comp_apply,genericTargetMap_C] using hev)
    change (ev (genericTargetMap Omega B0)=0 ↔ ev (genericTargetMap Omega
        (targetPolynomial (coefficients (polynomialEmbedding K) J) 2 (2*A) quadratic))=0) ∧
      (ev (genericTargetMap Omega C0)=0 ↔ ev (genericTargetMap Omega
        (targetPolynomial (coefficients (polynomialEmbedding K) Q) 14 (2*A) quadratic))=0) at hh
    rw [generic_target_is_movingCut,generic_target_is_movingCut] at hh
    exact hh

end ActualPair

#print axioms generic_target_is_movingCut
#print axioms normalized_target_flag
#print axioms exists_bounded_generic_pair
end
end ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814
