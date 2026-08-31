import ProximityPrize.SubmissionLower.ContactFirstTailCertificate6731Research
import ProximityPrize.SubmissionLower.ContactBaseIdealAlgebra6676Research
import ProximityPrize.SubmissionLower.ContactRegularComponentCover
namespace ProximityPrize.SubmissionLower.ContactTwoTailRecurrence6731Research
open scoped Classical
open ContactTaylorNumerators ContactPolynomialSolutions ContactGenericSurface
open ContactPrimeSeedIncidence ContactFirstTailCertificate6731Research
open ContactBaseIdealAlgebra6676Research ContactRegularComponentCover
open ContactProperCutSeedCount
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K Ω:Type} [Field K] [Field Ω]
theorem selected_globalTailCut_zero_of_lt
    (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
    (selected:K → Polynomial K) (γ:K) (w d:ℕ)
    (hdegree:(selected γ).natDegree ≤ w)
    (hsolution:ContactTranslation.specialization K (selected γ) γ F=0)
    (hwd:w < d):
    MvPolynomial.aeval (selectedPoint φ selected γ)
      (globalTailCut φ F d)=0:=by
  rw [globalTailCut_eq,map_mul]
  have hzero:MvPolynomial.eval (selectedPoint φ selected γ)
      (surfaceMap φ (numerator K F d))=0:=by
    rw [eval_surfaceMap]
    have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
        polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
          (φ Polynomial.X):=by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact polynomialPoint_numerator_zero (φ.comp Polynomial.C) F
      (selected γ) γ (φ Polynomial.X) hsolution d
      (hdegree.trans_lt hwd)
  change MvPolynomial.eval (selectedPoint φ selected γ)
      (surfaceMap φ (numerator K F d))*_=0
  rw [hzero,zero_mul]
theorem selected_secondTail_zero
    (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
    (selected:K → Polynomial K) (γ:K) (w:ℕ)
    (hdegree:(selected γ).natDegree ≤ w)
    (hsolution:ContactTranslation.specialization K (selected γ) γ F=0):
    MvPolynomial.aeval (selectedPoint φ selected γ)
      (globalTailCut φ F (w+2))=0:=by
  exact selected_globalTailCut_zero_of_lt φ F selected γ w (w+2)
    hdegree hsolution (by omega)
theorem surface_numerator_succ
    (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K) (b:ℕ):
    surfaceMap φ (numerator K F (b+1))=
      surfaceMap φ (polyH K F)*
          surfaceMap φ (baseDerivation F (numerator K F b))-
        (2*b:MvPolynomial (Fin 3) Ω)*
          surfaceMap φ (numerator K F b)*
          surfaceMap φ (baseDerivation F (polyH K F)):=by
  rw [numerator_succ,numeratorStep_eq]
  simp only [map_sub,map_mul,map_natCast]
  push_cast
  rfl
theorem mapped_baseDerivation_mem_of_two_numerators
    (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K) (b:ℕ)
    (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (hH:surfaceMap φ (polyH K F)∉P)
    (hN:surfaceMap φ (numerator K F b)∈P)
    (hNnext:surfaceMap φ (numerator K F (b+1))∈P):
    surfaceMap φ (baseDerivation F (numerator K F b))∈P:=by
  have hsecond:(2*b:MvPolynomial (Fin 3) Ω)*
      surfaceMap φ (numerator K F b)*
      surfaceMap φ (baseDerivation F (polyH K F))∈P:=by
    exact P.mul_mem_right _ (P.mul_mem_left _ hN)
  rw [surface_numerator_succ φ F b] at hNnext
  have hfirst:surfaceMap φ (polyH K F)*
      surfaceMap φ (baseDerivation F (numerator K F b))∈P:=by
    have:=P.add_mem hNnext hsecond
    simpa only [sub_add_cancel] using this
  exact (((inferInstance:P.IsPrime).mem_or_mem hfirst).resolve_left hH)
theorem globalTailCut_mem_iff
    (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
    (F:MvPolynomial (Fin 4) K) (d:ℕ)
    (P:Ideal (MvPolynomial (Fin 3) Ω)):
    globalTailCut φ F d∈P ↔ surfaceMap φ (numerator K F d)∈P:=by
  rw [globalTailCut_eq]
  have hc:(-φ Polynomial.X)^d≠0:=tail_scalar_ne_zero φ hφ d
  have hu:IsUnit
      (MvPolynomial.C ((-φ Polynomial.X)^d):MvPolynomial (Fin 3) Ω):=
    (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  exact P.mul_unit_mem_iff_mem hu
theorem mapped_baseDerivation_mem_of_two_globalTails
    (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
    (F:MvPolynomial (Fin 4) K) (b:ℕ)
    (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (hH:surfaceMap φ (polyH K F)∉P)
    (hT:globalTailCut φ F b∈P)
    (hTnext:globalTailCut φ F (b+1)∈P):
    surfaceMap φ (baseDerivation F (numerator K F b))∈P:=by
  apply mapped_baseDerivation_mem_of_two_numerators φ F b P hH
  · exact (globalTailCut_mem_iff φ hφ F b P).mp hT
  · exact (globalTailCut_mem_iff φ hφ F (b+1) P).mp hTnext
theorem regularComponent_two_tail_dichotomy
    (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
    (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Ω) (w:ℕ)
    (C:RegularComponent Ω G (globalTailCut φ F (w+1))
      (regularitySurface φ F)):
    globalTailCut φ F (w+2)∉C.1∨
      (globalTailCut φ F (w+2)∈C.1∧
        surfaceMap φ
          (baseDerivation F (numerator K F (w+1)))∈C.1):=by
  by_cases hT2:globalTailCut φ F (w+2)∈C.1
  · right
    refine ⟨hT2,?_⟩
    apply mapped_baseDerivation_mem_of_two_globalTails φ hφ F (w+1) C.1
    · exact regularComponent_H_not_mem Ω G
        (globalTailCut φ F (w+1)) (regularitySurface φ F) C
    · exact regularComponent_T_mem Ω G
        (globalTailCut φ F (w+1)) (regularitySurface φ F) C
    · simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hT2
  · exact Or.inl hT2
end
end ProximityPrize.SubmissionLower.ContactTwoTailRecurrence6731Research
