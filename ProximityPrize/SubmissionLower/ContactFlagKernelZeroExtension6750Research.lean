import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch

 














namespace ProximityPrize.SubmissionLower.ContactFlagKernelZeroExtension6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactFlagTranslation6641Research
open ContactFlagKernelUniversalityResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

universe u v

variable {K : Type u} [Field K]

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

 
def flagReconstructLinear (D w L s : Nat) :
    (CoefficientIndex D w L s → K) →ₗ[K] Poly4 K where
  toFun := reconstruct K D w L s
  map_add' theta eta := by
    classical
    simp [reconstruct, Finset.sum_add_distrib]
  map_smul' a theta := by
    classical
    simp only [reconstruct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    rw [MvPolynomial.smul_monomial]
    rfl

 

def flagReconstructIntoBox (D w L s : Nat) :
    (CoefficientIndex D w L s → K) →ₗ[K]
      globalCoefficientBox K D w L s :=
  LinearMap.codRestrict (globalCoefficientBox K D w L s)
    (flagReconstructLinear (K := K) D w L s)
    (reconstruct_mem_globalCoefficientBox K D w L s)

 
def columnIndexOfExponent {D w L s : Nat} (d : Fin 4 →₀ Nat)
    (hd : d ∈ globalExponents D w L s) : CoefficientIndex D w L s := by
  rcases hd with ⟨hL, hs, hD⟩
  have hi : d 1 < L + 1 := by omega
  have hj : d 2 < s + 1 := by omega
  have hz : d 3 < L + 1 - d 1 - d 2 := by omega
  have hx : d 0 < D - w * d 1 - (w - 1) * d 2 := by omega
  exact ⟨⟨d 1, hi⟩, ⟨⟨d 2, hj⟩, ⟨⟨d 3, hz⟩, ⟨d 0, hx⟩⟩⟩⟩

theorem columnExponent_columnIndexOfExponent {D w L s : Nat}
    (d : Fin 4 →₀ Nat) (hd : d ∈ globalExponents D w L s) :
    columnExponent (columnIndexOfExponent d hd) = d := by
  rcases hd with ⟨hL, hs, hD⟩
  ext i
  fin_cases i <;> simp [columnIndexOfExponent]

 
def encodeFlagBox {D w L s : Nat} (Q : globalCoefficientBox K D w L s) :
    CoefficientIndex D w L s → K :=
  fun c ↦ MvPolynomial.coeff (columnExponent c) Q.1

theorem reconstruct_encodeFlagBox {D w L s : Nat}
    (Q : globalCoefficientBox K D w L s) :
    reconstruct K D w L s (encodeFlagBox Q) = Q.1 := by
  classical
  ext d
  by_cases hd : d ∈ globalExponents D w L s
  · let c := columnIndexOfExponent d hd
    have hc : columnExponent c = d :=
      columnExponent_columnIndexOfExponent d hd
    rw [← hc, reconstruct_coeff]
    rfl
  · have hQ : MvPolynomial.coeff d Q.1 = 0 := by
      by_contra hn
      exact hd (Q.2 (MvPolynomial.mem_support_iff.mpr hn))
    have hRmem := reconstruct_mem_globalCoefficientBox K D w L s
      (encodeFlagBox Q)
    have hR : MvPolynomial.coeff d
        (reconstruct K D w L s (encodeFlagBox Q)) = 0 := by
      by_contra hn
      exact hd (hRmem (MvPolynomial.mem_support_iff.mpr hn))
    rw [hQ, hR]

 
def encodeFlagBoxLinear (D w L s : Nat) :
    globalCoefficientBox K D w L s →ₗ[K]
      (CoefficientIndex D w L s → K) where
  toFun := encodeFlagBox
  map_add' Q R := by
    funext c
    simp [encodeFlagBox]
  map_smul' a Q := by
    funext c
    simp [encodeFlagBox]

 
theorem globalCoefficientBox_mono_total
    {D w L Lmax s : Nat} (hL : L ≤ Lmax) :
    globalCoefficientBox K D w L s ≤
      globalCoefficientBox K D w Lmax s := by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  exact ⟨hd.1.trans hL, hd.2.1, hd.2.2⟩

 
def includeFlagBoxTotal {D w L Lmax s : Nat} (hL : L ≤ Lmax) :
    globalCoefficientBox K D w L s →ₗ[K]
      globalCoefficientBox K D w Lmax s :=
  Submodule.inclusion (globalCoefficientBox_mono_total (K := K) hL)

 


def zeroExtendTotal {D w L Lmax s : Nat} (hL : L ≤ Lmax) :
    (CoefficientIndex D w L s → K) →ₗ[K]
      (CoefficientIndex D w Lmax s → K) :=
  (encodeFlagBoxLinear (K := K) D w Lmax s).comp
    ((includeFlagBoxTotal (K := K) hL).comp
      (flagReconstructIntoBox (K := K) D w L s))

 
@[simp] theorem reconstruct_zeroExtendTotal
    {D w L Lmax s : Nat} (hL : L ≤ Lmax)
    (theta : CoefficientIndex D w L s → K) :
    reconstruct K D w Lmax s (zeroExtendTotal (K := K) hL theta) =
      reconstruct K D w L s theta := by
  unfold zeroExtendTotal
  simp only [LinearMap.comp_apply]
  exact reconstruct_encodeFlagBox _

 
theorem zeroExtendTotal_injective
    {D w L Lmax s : Nat} (hL : L ≤ Lmax) :
    Function.Injective
      (zeroExtendTotal (K := K) (D := D) (w := w) (s := s) hL) := by
  intro theta eta h
  apply reconstruct_injective K D w L s
  rw [← reconstruct_zeroExtendTotal (K := K) hL theta,
    ← reconstruct_zeroExtendTotal (K := K) hL eta, h]

 

theorem zeroExtendTotal_mem_constraintKernel
    {I : Type v} [Fintype I]
    {D w L Lmax s m : Nat} (hL : L ≤ Lmax)
    (nodes u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K D w L s m nodes u0 u1)) :
    zeroExtendTotal (K := K) hL theta ∈ LinearMap.ker
      (constraintMap K D w Lmax s m nodes u0 u1) := by
  rw [LinearMap.mem_ker]
  funext i r
  apply Subtype.ext
  change contactJet K (m - r.val)
      ((extractBlock K D w Lmax s (nodes i) (u0 i) (u1 i) r.val
        (zeroExtendTotal (K := K) hL theta)) : Poly K) = 0
  rw [← translation_reconstruct_coeff,
    reconstruct_zeroExtendTotal (K := K) hL,
    translation_reconstruct_coeff]
  exact block_equations_of_mem_ker K D w L s m nodes u0 u1
    theta htheta i r

 
def zeroExtendConstraintKernel
    {I : Type v} [Fintype I]
    {D w L Lmax s m : Nat} (hL : L ≤ Lmax)
    (nodes u0 u1 : I → K) :
    LinearMap.ker (constraintMap K D w L s m nodes u0 u1) →ₗ[K]
      LinearMap.ker (constraintMap K D w Lmax s m nodes u0 u1) :=
  LinearMap.codRestrict
    (LinearMap.ker (constraintMap K D w Lmax s m nodes u0 u1))
    ((zeroExtendTotal (K := K) hL).comp
      (LinearMap.ker (constraintMap K D w L s m nodes u0 u1)).subtype)
    (fun theta ↦ zeroExtendTotal_mem_constraintKernel
      (K := K) hL nodes u0 u1 theta.1 theta.2)

@[simp] theorem zeroExtendConstraintKernel_coe
    {I : Type v} [Fintype I]
    {D w L Lmax s m : Nat} (hL : L ≤ Lmax)
    (nodes u0 u1 : I → K)
    (theta : LinearMap.ker (constraintMap K D w L s m nodes u0 u1)) :
    (zeroExtendConstraintKernel (K := K) hL nodes u0 u1 theta).1 =
      zeroExtendTotal (K := K) hL theta.1 := rfl

theorem zeroExtendConstraintKernel_injective
    {I : Type v} [Fintype I]
    {D w L Lmax s m : Nat} (hL : L ≤ Lmax)
    (nodes u0 u1 : I → K) :
    Function.Injective
      (zeroExtendConstraintKernel (K := K) (D := D) (w := w)
        (s := s) (m := m) hL nodes u0 u1) := by
  intro theta eta h
  apply Subtype.ext
  exact zeroExtendTotal_injective (K := K) hL
    (congrArg Subtype.val h)

 


def zeroExtendConstraintKernelToArray
    {I : Type v} [Fintype I]
    {D w L Lmax s m : Nat} (hL : L ≤ Lmax)
    (nodes u0 u1 : I → K) :
    LinearMap.ker (constraintMap K D w L s m nodes u0 u1) →ₗ[K]
      (CoefficientIndex D w Lmax s → K) :=
  (LinearMap.ker
    (constraintMap K D w Lmax s m nodes u0 u1)).subtype.comp
      (zeroExtendConstraintKernel (K := K) hL nodes u0 u1)

@[simp] theorem zeroExtendConstraintKernelToArray_apply
    {I : Type v} [Fintype I]
    {D w L Lmax s m : Nat} (hL : L ≤ Lmax)
    (nodes u0 u1 : I → K)
    (theta : LinearMap.ker (constraintMap K D w L s m nodes u0 u1)) :
    zeroExtendConstraintKernelToArray (K := K) hL nodes u0 u1 theta =
      zeroExtendTotal (K := K) hL theta.1 := rfl

theorem zeroExtendConstraintKernelToArray_injective
    {I : Type v} [Fintype I]
    {D w L Lmax s m : Nat} (hL : L ≤ Lmax)
    (nodes u0 u1 : I → K) :
    Function.Injective
      (zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w)
        (s := s) (m := m) hL nodes u0 u1) := by
  intro theta eta h
  apply Subtype.ext
  exact zeroExtendTotal_injective (K := K) hL h

 

@[simp] theorem reconstruct_zeroExtendConstraintKernel
    {I : Type v} [Fintype I]
    {D w L Lmax s m : Nat} (hL : L ≤ Lmax)
    (nodes u0 u1 : I → K)
    (theta : LinearMap.ker (constraintMap K D w L s m nodes u0 u1)) :
    reconstruct K D w Lmax s
        (zeroExtendConstraintKernel (K := K) hL nodes u0 u1 theta).1 =
      reconstruct K D w L s theta.1 := by
  exact reconstruct_zeroExtendTotal (K := K) hL theta.1

end

end ProximityPrize.SubmissionLower.ContactFlagKernelZeroExtension6750Research

#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelZeroExtension6750Research.reconstruct_zeroExtendTotal
#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelZeroExtension6750Research.zeroExtendTotal_mem_constraintKernel
#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelZeroExtension6750Research.zeroExtendConstraintKernel_injective
#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelZeroExtension6750Research.zeroExtendConstraintKernelToArray_injective
