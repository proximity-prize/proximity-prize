import ProximityPrize.SubmissionLower.MovingSourcePairResultant6814
namespace ProximityPrize.SubmissionLower.MovingSourceExtendedCoefficients6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 20000
open MvPolynomial RCN135 RCN136
open MovingSourceClearing6814 MovingSourceGenericField6814 MovingSourceFlatBaseChange6814
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K E : Type} [Field K] [Field E]

def codeMap (f : GenericField K →+* E) : Polynomial K →+* E :=
  f.comp (polynomialEmbedding K)

theorem codeMap_injective (f : GenericField K →+* E) : Function.Injective (codeMap f) :=
  f.injective.comp (polynomialEmbedding_injective K)

theorem extended_sourceMap (f : GenericField K →+* E) (P : WholeSpaceCube6814.Poly (K:=K)) :
    sourceMap K (codeMap f) P=MvPolynomial.map f (genericSourceMap K P) := by
  simp only [sourceMap,genericSourceMap,codeMap,RingHom.comp_apply,MvPolynomial.map_map]

theorem extended_coefficients_ne_zero (f : GenericField K →+* E)
    (P : WholeSpaceCube6814.Poly (K:=K)) (hP : P≠0) : coefficients (codeMap f) P≠0 := by
  intro hz
  apply hP
  apply (SecondJetCoefficients.asS (K:=K)).injective
  apply Polynomial.map_injective (surfaceMap (codeMap f))
    (surfaceMap_injective (codeMap f) (codeMap_injective f))
  simpa only [coefficients,map_zero,Polynomial.map_zero] using hz

theorem extended_coefficients_degree (f : GenericField K →+* E)
    (P : WholeSpaceCube6814.Poly (K:=K)) :
    (coefficients (codeMap f) P).natDegree≤P.degreeOf 1 := by
  exact Polynomial.natDegree_map_le.trans_eq (MovingSourceNativeFactor6814.asS_natDegree P)

theorem extended_coefficients_relPrime (f : GenericField K →+* E)
    (P Q : WholeSpaceCube6814.Poly (K:=K)) (hP : P≠0) (hrel : IsRelPrime P Q) :
    IsRelPrime (coefficients (codeMap f) P) (coefficients (codeMap f) Q) := by
  letI : Algebra (GenericField K) E := f.toAlgebra
  letI : Module.Flat (MvPolynomial (Fin 4) (GenericField K)) (MvPolynomial (Fin 4) E) := coefficient_map_flat
  have hsource : genericSourceMap K P≠0 := by
    intro hz
    have hv := view_sourceMap K (polynomialEmbedding K) P
    change MvPolynomial.finSuccEquiv (GenericField K) 3 (genericSourceMap K P)=
      coefficients (polynomialEmbedding K) P at hv
    rw [hz,map_zero] at hv
    exact MovingSourceCoprimeCuts6814.generic_coefficients_ne_zero K P hP hv.symm
  have hc := map_isRelPrime_of_flat
    (MvPolynomial.map_injective (algebraMap (GenericField K) E) (algebraMap (GenericField K) E).injective)
    (genericSourceMap K P) (genericSourceMap K Q) hsource (genericSourceMap_relPrime K P Q hP hrel)
  have hc' : IsRelPrime (sourceMap K (codeMap f) P) (sourceMap K (codeMap f) Q) := by
    rw [extended_sourceMap,extended_sourceMap]
    exact hc
  have hv := isRelPrime_equiv (MvPolynomial.finSuccEquiv E 3).toRingEquiv _ _ hc'
  change IsRelPrime (MvPolynomial.finSuccEquiv E 3 (sourceMap K (codeMap f) P))
    (MvPolynomial.finSuccEquiv E 3 (sourceMap K (codeMap f) Q)) at hv
  simpa only [view_sourceMap] using hv

end
end ProximityPrize.SubmissionLower.MovingSourceExtendedCoefficients6814
