import ProximityPrize.SubmissionLower.MovingSourceGenericField6814
import ProximityPrize.SubmissionLower.MovingSourceSaturation6814

/-! Compose the algebraic clearing step for the actual source pair.
The moving target remains indeterminate; specialization is expressed by
an arbitrary coefficient evaluation and target value. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial RCN135 RCN136 SecondJetCoefficients SecondJetClearedHelper
open MovingSourceClearing6814 MovingSourceGenericField6814 MovingSourceSaturation6814

variable (K : Type*) [Field K]
local notation "Omega" => GenericField K
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local instance : StrongNormalizationMonoid (Polynomial Poly3) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : NormalizedGCDMonoid (Polynomial Poly3) :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid _

def collectTarget (E : Type*) [Field E] :
    Polynomial (MvPolynomial (Fin 3) E) ≃ₐ[E] MvPolynomial (Fin 3) (Polynomial E) :=
  (MvPolynomial.finSuccEquiv E 3).symm.trans (RCN136.collectX E)

def genericTargetMap (E : Type*) [Field E] :
    Polynomial (MvPolynomial (Fin 3) E) →+* MvPolynomial (Fin 3) (GenericField E) :=
  (RCN136.surfaceMap (polynomialEmbedding E)).comp (MvPolynomial.finSuccEquiv E 3).symm.toRingHom

theorem genericTargetMap_injective (E : Type*) [Field E] :
    Function.Injective (genericTargetMap E) :=
  (RCN136.surfaceMap_injective (polynomialEmbedding E) (polynomialEmbedding_injective E)).comp
    (MvPolynomial.finSuccEquiv E 3).symm.injective

theorem genericTargetMap_relPrime (E : Type*) [Field E]
    (U V : Polynomial (MvPolynomial (Fin 3) E)) (hU : U≠0) (hrel : IsRelPrime U V) :
    IsRelPrime (genericTargetMap E U) (genericTargetMap E V) := by
  have hU' : collectTarget E U≠0 := by
    intro hz
    exact hU ((collectTarget E).injective (by simpa only [map_zero] using hz))
  exact generic_coefficient_map_relPrime E _ _ hU'
    (MovingSourceFlatBaseChange6814.isRelPrime_equiv (collectTarget E).toRingEquiv U V hrel)

theorem generic_coefficients_ne_zero (P : WholeSpaceCube6814.Poly (K := K)) (hP : P≠0) :
    coefficients (polynomialEmbedding K) P≠0 := by
  intro hz
  apply hP
  apply (asS (K := K)).injective
  apply Polynomial.map_injective (surfaceMap (polynomialEmbedding K))
    (surfaceMap_injective (polynomialEmbedding K) (polynomialEmbedding_injective K))
  simpa only [coefficients,map_zero,Polynomial.map_zero] using hz

theorem generic_coefficients_degree (P : WholeSpaceCube6814.Poly (K := K)) (s : ℕ)
    (hS : P.degreeOf 1 ≤ s) : (coefficients (polynomialEmbedding K) P).natDegree ≤ s := by
  apply Polynomial.natDegree_map_le.trans
  simpa using SecondJetHelperWeights.asS_derivative_degree P s 0
    (MvPolynomial.degreeOf_le_iff.mp hS)

/-- The two returned cuts are nonzero and coprime before moving-target
specialization. On the regular denominator locus their zeros agree with
the actual cleared source equations, uniformly in every field evaluation.
No post-clearing properness or zero-set equivalence is a premise. -/
theorem exists_regular_coprime_target_cuts
    (J Q : WholeSpaceCube6814.Poly (K := K))
    (hJ : J≠0) (hQ : Q≠0) (hrel : IsRelPrime J Q)
    (hJdegree : J.degreeOf 1 ≤ 2) (hQdegree : Q.degreeOf 1 ≤ 14)
    (quadratic A : Poly3) (hA : (2 : Poly3)*A≠0) :
    ∃ U V : Polynomial Poly3, U≠0 ∧ V≠0 ∧ IsRelPrime U V ∧
      U ∣ targetPolynomial (coefficients (polynomialEmbedding K) J) 2 (2*A) quadratic ∧
      V ∣ targetPolynomial (coefficients (polynomialEmbedding K) Q) 14 (2*A) quadratic ∧
      ∀ (L : Type*) [Field L] (ev : Poly3 →+* L) (target : L), ev (2*A)≠0 →
        ((Polynomial.eval₂ ev target U=0 ↔
          cleared ((coefficients (polynomialEmbedding K) J).map ev) 2 (ev (2*A))
            (target-ev quadratic)=0) ∧
         (Polynomial.eval₂ ev target V=0 ↔
          cleared ((coefficients (polynomialEmbedding K) Q).map ev) 14 (ev (2*A))
            (target-ev quadratic)=0)) := by
  obtain ⟨U,V,hU,hV,hcop,hUdiv,hVdiv,hzero⟩ := exists_coprime_cleared_pair
    (coefficients (polynomialEmbedding K) J) (coefficients (polynomialEmbedding K) Q)
    2 14 (2*A) quadratic (generic_coefficients_ne_zero K J hJ)
    (generic_coefficients_ne_zero K Q hQ) (generic_coefficients_degree K J 2 hJdegree)
    (generic_coefficients_degree K Q 14 hQdegree) hA (generic_coefficients_relPrime K J Q hJ hrel)
  refine ⟨U,V,hU,hV,hcop,hUdiv,hVdiv,?_⟩
  intro L _ ev target hden
  have hz := hzero L (Polynomial.eval₂RingHom ev target) (by simpa using hden)
  change (Polynomial.eval₂ ev target U=0 ↔ Polynomial.eval₂ ev target
      (targetPolynomial (coefficients (polynomialEmbedding K) J) 2 (2*A) quadratic)=0) ∧
    (Polynomial.eval₂ ev target V=0 ↔ Polynomial.eval₂ ev target
      (targetPolynomial (coefficients (polynomialEmbedding K) Q) 14 (2*A) quadratic)=0) at hz
  rw [eval_targetPolynomial,eval_targetPolynomial] at hz
  exact hz

#print axioms generic_coefficients_ne_zero
#print axioms exists_regular_coprime_target_cuts
#print axioms genericTargetMap_relPrime
end
end ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814
