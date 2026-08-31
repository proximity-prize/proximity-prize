import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research
import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch

 










namespace ProximityPrize.SubmissionLower
namespace ContactFlagNestedSpanSpecialization6750Research

open scoped Classical BigOperators
open ContactFlagInterpolation6641Research
open ContactFlagKernelUniversalityResearch
open ContactFlagKernelZeroExtension6750Research
open ContactFlagNestedKernelCommonGCD6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

universe u v w x

variable {K : Type u} [Field K]
variable {I : Type v} [Fintype I]
variable {ι : Type w}

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

 

def reconstructSpecializationLinear
    (D w0 Lmax s : Nat) (P : Polynomial K) (gamma : K) :
    (CoefficientIndex D w0 Lmax s → K) →ₗ[K] Polynomial K :=
  (ContactTranslation.specialization K P gamma).toLinearMap.comp
    (flagReconstructLinear (K := K) D w0 Lmax s)

 

def reconstructionSpecializationKernel
    (D w0 Lmax s : Nat) (P : Polynomial K) (gamma : K) :
    Submodule K (CoefficientIndex D w0 Lmax s → K) :=
  LinearMap.ker (reconstructSpecializationLinear D w0 Lmax s P gamma)

theorem mem_reconstructionSpecializationKernel_iff
    (D w0 Lmax s : Nat) (P : Polynomial K) (gamma : K)
    (theta : CoefficientIndex D w0 Lmax s → K) :
    theta ∈ reconstructionSpecializationKernel D w0 Lmax s P gamma ↔
      ContactTranslation.specialization K P gamma
        (reconstruct K D w0 Lmax s theta) = 0 := by
  rfl

 

theorem embeddedSelectedKernelFamilySum_le_specializationKernel
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker (constraintMap K D w0 (cap i) s m nodes u0 u1)))
    (P : Polynomial K) (gamma : K)
    (hselected : ∀ (i : ι) (theta : Selected i),
      ContactTranslation.specialization K P gamma
        (reconstruct K D w0 (cap i) s theta.1.1) = 0) :
    embeddedSelectedKernelFamilySum D w0 Lmax s m nodes u0 u1
        cap hcap Selected ≤
      reconstructionSpecializationKernel D w0 Lmax s P gamma := by
  apply iSup_le
  intro i
  rintro thetaMax ⟨theta, rfl⟩
  apply (mem_reconstructionSpecializationKernel_iff
    D w0 Lmax s P gamma _).mpr
  rw [LinearMap.comp_apply,
    zeroExtendConstraintKernelToArray_apply,
    reconstruct_zeroExtendTotal]
  exact hselected i theta

 


theorem specialization_eq_zero_of_mem_adjoinedSelectedFamily
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker (constraintMap K D w0 (cap i) s m nodes u0 u1)))
    (g : CoefficientIndex D w0 Lmax s → K)
    (P : Polynomial K) (gamma : K)
    (hfixed : ContactTranslation.specialization K P gamma
      (reconstruct K D w0 Lmax s g) = 0)
    (hselected : ∀ (i : ι) (theta : Selected i),
      ContactTranslation.specialization K P gamma
        (reconstruct K D w0 (cap i) s theta.1.1) = 0)
    (v : adjoinFixedArray g
      (embeddedSelectedKernelFamilySum D w0 Lmax s m nodes u0 u1
        cap hcap Selected)) :
    ContactTranslation.specialization K P gamma
      (reconstruct K D w0 Lmax s v.1) = 0 := by
  let zKernel := reconstructionSpecializationKernel D w0 Lmax s P gamma
  have hfixedSpan : K ∙ g ≤ zKernel := by
    apply Submodule.span_le.mpr
    intro q hq
    have hqg : q = g := Set.mem_singleton_iff.mp hq
    subst q
    exact (mem_reconstructionSpecializationKernel_iff
      D w0 Lmax s P gamma g).mpr hfixed
  have hfamily :
      embeddedSelectedKernelFamilySum D w0 Lmax s m nodes u0 u1
          cap hcap Selected ≤ zKernel :=
    embeddedSelectedKernelFamilySum_le_specializationKernel
      D w0 Lmax s m nodes u0 u1 cap hcap Selected P gamma hselected
  exact (mem_reconstructionSpecializationKernel_iff
    D w0 Lmax s P gamma v.1).mp
      ((sup_le hfixedSpan hfamily) v.2)

 


theorem quotient_specialization_eq_zero_of_mul_eq
    (P : Polynomial K) (gamma : K) (D H Q : Poly4 K)
    (hfactor : D = H * Q)
    (hD : ContactTranslation.specialization K P gamma D = 0)
    (hH : ContactTranslation.specialization K P gamma H ≠ 0) :
    ContactTranslation.specialization K P gamma Q = 0 := by
  rw [hfactor, map_mul] at hD
  exact (mul_eq_zero.mp hD).resolve_left hH

 

theorem exists_quotient_specialization_eq_zero_of_dvd
    (P : Polynomial K) (gamma : K) (H D : Poly4 K)
    (hdiv : H ∣ D)
    (hD : ContactTranslation.specialization K P gamma D = 0)
    (hH : ContactTranslation.specialization K P gamma H ≠ 0) :
    ∃ Q : Poly4 K, D = H * Q ∧
      ContactTranslation.specialization K P gamma Q = 0 := by
  obtain ⟨Q, hfactor⟩ := hdiv
  exact ⟨Q, hfactor,
    quotient_specialization_eq_zero_of_mul_eq
      P gamma D H Q hfactor hD hH⟩

 


theorem exists_commonGCDAtMax_quotient_specializes_zero
    {D w0 Lmax s : Nat}
    (V : Submodule K (CoefficientIndex D w0 Lmax s → K))
    {β : Type x} [Fintype β] (b : Module.Basis β K V)
    (P : Polynomial K) (gamma : K)
    (hall : ∀ v : V, ContactTranslation.specialization K P gamma
      (reconstruct K D w0 Lmax s v.1) = 0)
    (hcore : ContactTranslation.specialization K P gamma
      (commonGCDAtMax V b) ≠ 0)
    (v : V) :
    ∃ Q : Poly4 K,
      reconstruct K D w0 Lmax s v.1 = commonGCDAtMax V b * Q ∧
      ContactTranslation.specialization K P gamma Q = 0 := by
  exact exists_quotient_specialization_eq_zero_of_dvd P gamma
    (commonGCDAtMax V b) (reconstruct K D w0 Lmax s v.1)
      (commonGCDAtMax_dvd V b v) (hall v) hcore

 

theorem selected_m61_kernel_member_specializes_zero
    [DecidableEq K] [DecidableEq I]
    (Lmax : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker
        (constraintMap K 11044110 131071 (cap i) 18 61 nodes u0 u1)))
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ 131071)
    (hcard : 181884 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    ∀ (i : ι) (theta : Selected i),
      ContactTranslation.specialization K P gamma
        (reconstruct K 11044110 131071 (cap i) 18 theta.1.1) = 0 := by
  intro i theta
  have hflag := specialization_eq_zero_of_mem_ker K
    11044110 131071 (cap i) 18 61 nodes u0 u1 theta.1.1 theta.1.2
      P gamma support (by norm_num) hP (by omega) hvalues
  simpa only [specialization_eq_ordinary] using hflag

 
theorem specialization_eq_zero_of_mem_m61_adjoinedSelectedFamily
    [DecidableEq K] [DecidableEq I]
    (Lmax : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker
        (constraintMap K 11044110 131071 (cap i) 18 61 nodes u0 u1)))
    (g : CoefficientIndex 11044110 131071 Lmax 18 → K)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ 131071)
    (hcard : 181884 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i)
    (hfixed : ContactTranslation.specialization K P gamma
      (reconstruct K 11044110 131071 Lmax 18 g) = 0)
    (v : adjoinFixedArray g
      (embeddedSelectedKernelFamilySum 11044110 131071 Lmax 18 61
        nodes u0 u1 cap hcap Selected)) :
    ContactTranslation.specialization K P gamma
      (reconstruct K 11044110 131071 Lmax 18 v.1) = 0 := by
  exact specialization_eq_zero_of_mem_adjoinedSelectedFamily
    11044110 131071 Lmax 18 61 nodes u0 u1 cap hcap Selected
      g P gamma hfixed
      (selected_m61_kernel_member_specializes_zero
        Lmax nodes u0 u1 cap hcap Selected P gamma support
          hP hcard hvalues) v

 


theorem exists_m61_commonGCDAtMax_quotient_specializes_zero
    [DecidableEq K] [DecidableEq I]
    (Lmax : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker
        (constraintMap K 11044110 131071 (cap i) 18 61 nodes u0 u1)))
    (g : CoefficientIndex 11044110 131071 Lmax 18 → K)
    {β : Type x} [Fintype β]
    (b : Module.Basis β K
      (adjoinFixedArray g
        (embeddedSelectedKernelFamilySum 11044110 131071 Lmax 18 61
          nodes u0 u1 cap hcap Selected)))
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ 131071)
    (hcard : 181884 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i)
    (hfixed : ContactTranslation.specialization K P gamma
      (reconstruct K 11044110 131071 Lmax 18 g) = 0)
    (hcore : ContactTranslation.specialization K P gamma
      (commonGCDAtMax
        (adjoinFixedArray g
          (embeddedSelectedKernelFamilySum 11044110 131071 Lmax 18 61
            nodes u0 u1 cap hcap Selected)) b) ≠ 0)
    (v : adjoinFixedArray g
      (embeddedSelectedKernelFamilySum 11044110 131071 Lmax 18 61
        nodes u0 u1 cap hcap Selected)) :
    ∃ Q : Poly4 K,
      reconstruct K 11044110 131071 Lmax 18 v.1 =
        commonGCDAtMax
          (adjoinFixedArray g
            (embeddedSelectedKernelFamilySum 11044110 131071 Lmax 18 61
              nodes u0 u1 cap hcap Selected)) b * Q ∧
      ContactTranslation.specialization K P gamma Q = 0 := by
  apply exists_commonGCDAtMax_quotient_specializes_zero
    (adjoinFixedArray g
      (embeddedSelectedKernelFamilySum 11044110 131071 Lmax 18 61
        nodes u0 u1 cap hcap Selected)) b P gamma
  · intro q
    exact specialization_eq_zero_of_mem_m61_adjoinedSelectedFamily
      Lmax nodes u0 u1 cap hcap Selected g P gamma support
        hP hcard hvalues hfixed q
  · exact hcore

end

end ContactFlagNestedSpanSpecialization6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFlagNestedSpanSpecialization6750Research.specialization_eq_zero_of_mem_adjoinedSelectedFamily
#print axioms ProximityPrize.SubmissionLower.ContactFlagNestedSpanSpecialization6750Research.exists_commonGCDAtMax_quotient_specializes_zero
#print axioms ProximityPrize.SubmissionLower.ContactFlagNestedSpanSpecialization6750Research.specialization_eq_zero_of_mem_m61_adjoinedSelectedFamily
#print axioms ProximityPrize.SubmissionLower.ContactFlagNestedSpanSpecialization6750Research.exists_m61_commonGCDAtMax_quotient_specializes_zero
