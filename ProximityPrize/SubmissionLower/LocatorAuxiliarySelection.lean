import ProximityPrize.SubmissionLower.LocatorSelection

/-! Small-total auxiliary kernels embed in the already selected whole kernels.
The extension changes only the coefficient array: the reconstructed polynomial,
and hence every contact equation, stays unchanged. -/
namespace ProximityPrize.SubmissionLower.LocatorAuxiliarySelection

open RCN100 RCN119 RCN101 RCN122 RCN180

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

section Generic
variable {E J : Type*} [Field E] [Fintype J]
local instance : DecidableEq E := Classical.decEq E

theorem globalCoefficientBox_mono_total {D w L Lmax s : ℕ} (hL : L ≤ Lmax) :
    globalCoefficientBox E D w L s ≤ globalCoefficientBox E D w Lmax s := by
  intro P hP d hd
  exact ⟨(hP hd).1.trans hL, (hP hd).2⟩

def zeroExtendTotal {D w L Lmax s : ℕ} (_hL : L ≤ Lmax) :
    (CoefficientIndex D w L s → E) →ₗ[E] (CoefficientIndex D w Lmax s → E) :=
  LocatorSelection.polynomialCoefficientsLinear D w Lmax s
    (reconstructLinear (K := E) D w L s)

@[simp] theorem zeroExtendTotal_apply {D w L Lmax s : ℕ} (hL : L ≤ Lmax)
    (a : CoefficientIndex D w L s → E) (c : CoefficientIndex D w Lmax s) :
    zeroExtendTotal (E := E) hL a c =
      MvPolynomial.coeff (columnExponent c) (reconstruct E D w L s a) :=
  LocatorSelection.polynomialCoefficientsLinear_apply D w Lmax s
    (reconstructLinear (K := E) D w L s) a c

@[simp] theorem reconstruct_zeroExtendTotal {D w L Lmax s : ℕ} (hL : L ≤ Lmax)
    (a : CoefficientIndex D w L s → E) :
    reconstruct E D w Lmax s (zeroExtendTotal (E := E) hL a) =
      reconstruct E D w L s a := by
  apply LocatorSelection.reconstruct_polynomialCoefficientsLinear
    D w Lmax s (reconstructLinear (K := E) D w L s) a
  exact globalCoefficientBox_mono_total hL
    (reconstruct_mem_globalCoefficientBox E D w L s a)

theorem zeroExtendTotal_injective {D w L Lmax s : ℕ} (hL : L ≤ Lmax) :
    Function.Injective (zeroExtendTotal (E := E) (D := D) (w := w) (s := s) hL) := by
  intro a b hab
  apply reconstruct_injective E D w L s
  rw [← reconstruct_zeroExtendTotal hL a, ← reconstruct_zeroExtendTotal hL b, hab]

theorem zeroExtendTotal_mem_constraintKernel
    {D w L Lmax s m : ℕ} (hL : L ≤ Lmax) (nodes u0 u1 : J → E)
    (a : CoefficientIndex D w L s → E)
    (ha : a ∈ LinearMap.ker (constraintMap E D w L s m nodes u0 u1)) :
    zeroExtendTotal (E := E) hL a ∈
      LinearMap.ker (constraintMap E D w Lmax s m nodes u0 u1) := by
  rw [LinearMap.mem_ker]
  funext i r
  apply Subtype.ext
  change contactJet E (m - r.val)
    ((extractBlock E D w Lmax s (nodes i) (u0 i) (u1 i) r.val
      (zeroExtendTotal (E := E) hL a)) : RCN119.Poly E) = 0
  rw [← translation_reconstruct_coeff, reconstruct_zeroExtendTotal,
    translation_reconstruct_coeff]
  exact block_equations_of_mem_ker E D w L s m nodes u0 u1 a ha i r

def zeroExtendConstraintKernel {D w L Lmax s m : ℕ} (hL : L ≤ Lmax)
    (nodes u0 u1 : J → E) :
    ConstraintKernel (K := E) D w L s m nodes u0 u1 →ₗ[E]
      ConstraintKernel (K := E) D w Lmax s m nodes u0 u1 :=
  LinearMap.codRestrict
    (ConstraintKernel (K := E) D w Lmax s m nodes u0 u1)
    ((zeroExtendTotal (E := E) hL).comp
      (ConstraintKernel (K := E) D w L s m nodes u0 u1).subtype)
    (fun a => zeroExtendTotal_mem_constraintKernel hL nodes u0 u1 a.1 a.2)

@[simp] theorem zeroExtendConstraintKernel_coe {D w L Lmax s m : ℕ}
    (hL : L ≤ Lmax) (nodes u0 u1 : J → E)
    (a : ConstraintKernel (K := E) D w L s m nodes u0 u1) :
    (zeroExtendConstraintKernel hL nodes u0 u1 a).1 =
      zeroExtendTotal (E := E) hL a.1 := rfl

@[simp] theorem reconstruct_zeroExtendConstraintKernel {D w L Lmax s m : ℕ}
    (hL : L ≤ Lmax) (nodes u0 u1 : J → E)
    (a : ConstraintKernel (K := E) D w L s m nodes u0 u1) :
    reconstruct E D w Lmax s (zeroExtendConstraintKernel hL nodes u0 u1 a).1 =
      reconstruct E D w L s a.1 :=
  reconstruct_zeroExtendTotal hL a.1

theorem zeroExtendConstraintKernel_injective {D w L Lmax s m : ℕ}
    (hL : L ≤ Lmax) (nodes u0 u1 : J → E) :
    Function.Injective
      (zeroExtendConstraintKernel (E := E) (D := D) (w := w) (s := s) (m := m)
        hL nodes u0 u1) := by
  intro a b hab
  apply Subtype.ext
  exact zeroExtendTotal_injective hL (congrArg Subtype.val hab)

theorem full_kernel_divisor_small {D w L Lmax s m : ℕ} (hL : L ≤ Lmax)
    (nodes u0 u1 : J → E) (F : MvPolynomial (Fin 4) E)
    (hdiv : ∀ a : ConstraintKernel (K := E) D w Lmax s m nodes u0 u1,
      F ∣ reconstruct E D w Lmax s a.1) :
    ∀ a : ConstraintKernel (K := E) D w L s m nodes u0 u1,
      F ∣ reconstruct E D w L s a.1 := by
  intro a
  have h := hdiv (zeroExtendConstraintKernel hL nodes u0 u1 a)
  simpa only [reconstruct_zeroExtendConstraintKernel] using h

end Generic

section Selected
open ProximityPrize.Benchmark
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

/-- A68 at any L ≤ 10000 is already contained in Selection.AKernel (L=67500). -/
theorem common_divides_A68_small {u0 u1 : I → K}
    (S : LocatorSelection.SelectedPair u0 u1) (L : ℕ) (hL : L ≤ 10000) :
    ∀ a : ConstraintKernel (K := K) 13456530 131071 L 22 74
      IRSProfile.domain u0 u1,
      gcd S.QA S.QB ∣ reconstruct K 13456530 131071 L 22 a.1 := by
  exact full_kernel_divisor_small (E := K) (Lmax := 67500) (by omega)
    IRSProfile.domain u0 u1 (gcd S.QA S.QB) S.common_divides_A

/-- The same extension for the joined A51 Y-source family. -/
theorem common_divides_A51_small {u0 u1 : I → K}
    (S : LocatorSelection.SelectedPair u0 u1) (L : ℕ) (hL : L ≤ 67500) :
    ∀ a : ConstraintKernel (K := K) 9092250 131071 L 15 50
      IRSProfile.domain u0 u1,
      gcd S.QA S.QB ∣ reconstruct K 9092250 131071 L 15 a.1 := by
  exact full_kernel_divisor_small (E := K) (Lmax := 67500) hL
    IRSProfile.domain u0 u1 (gcd S.QA S.QB) S.common_divides_Aux

end Selected
end
end ProximityPrize.SubmissionLower.LocatorAuxiliarySelection
