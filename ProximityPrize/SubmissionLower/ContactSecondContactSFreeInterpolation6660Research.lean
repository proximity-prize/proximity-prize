import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSecondContactLocalDivisibility6660Research

 




















namespace ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research

open ProximityPrize.Benchmark
open scoped BigOperators

set_option autoImplicit false

noncomputable section

variable (K : Type*) [Field K]

 

abbrev CoefficientIndex (D w C rCap : ℕ) :=
  (y : Fin (C + 1)) × (r : Fin (rCap + 1)) ×
    (Fin (C + 1 - y.val - r.val) ×
      Fin (D - w * y.val - (w - 1) * r.val))

 
def columnExponent {D w C rCap : ℕ}
    (c : CoefficientIndex D w C rCap) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 c.2.2.2.val + Finsupp.single 1 c.1.val +
    Finsupp.single 2 c.2.1.val + Finsupp.single 3 c.2.2.1.val

@[simp] theorem columnExponent_x {D w C rCap : ℕ}
    (c : CoefficientIndex D w C rCap) : columnExponent c 0 = c.2.2.2.val := by
  simp [columnExponent]

@[simp] theorem columnExponent_y {D w C rCap : ℕ}
    (c : CoefficientIndex D w C rCap) : columnExponent c 1 = c.1.val := by
  simp [columnExponent]

@[simp] theorem columnExponent_r {D w C rCap : ℕ}
    (c : CoefficientIndex D w C rCap) : columnExponent c 2 = c.2.1.val := by
  simp [columnExponent]

@[simp] theorem columnExponent_z {D w C rCap : ℕ}
    (c : CoefficientIndex D w C rCap) : columnExponent c 3 = c.2.2.1.val := by
  simp [columnExponent]

theorem columnExponent_injective (D w C rCap : ℕ) :
    Function.Injective
      (columnExponent (D := D) (w := w) (C := C) (rCap := rCap)) := by
  intro c d h
  have hx := congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
  have hy := congrArg (fun e : Fin 4 →₀ ℕ => e 1) h
  have hr := congrArg (fun e : Fin 4 →₀ ℕ => e 2) h
  have hz := congrArg (fun e : Fin 4 →₀ ℕ => e 3) h
  rcases c with ⟨⟨cy, hcy⟩, ⟨⟨cr, hcr⟩, ⟨⟨cz, hcz⟩, ⟨cx, hcx⟩⟩⟩⟩
  rcases d with ⟨⟨dy, hdy⟩, ⟨⟨dr, hdr⟩, ⟨⟨dz, hdz⟩, ⟨dx, hdx⟩⟩⟩⟩
  simp only [columnExponent_x] at hx
  simp only [columnExponent_y] at hy
  simp only [columnExponent_r] at hr
  simp only [columnExponent_z] at hz
  subst dy
  subst dr
  subst dz
  subst dx
  rfl

def globalExponents (D w C rCap : ℕ) : Set (Fin 4 →₀ ℕ) :=
  {d | d 1 + d 2 + d 3 ≤ C ∧ d 2 ≤ rCap ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D}

def globalCoefficientBox (D w C rCap : ℕ) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  MvPolynomial.restrictSupport K (globalExponents D w C rCap)

theorem columnMonomial_mem (D w C rCap : ℕ)
    (c : CoefficientIndex D w C rCap) (a : K) :
    MvPolynomial.monomial (columnExponent c) a ∈
      globalCoefficientBox K D w C rCap := by
  apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
  left
  have hy := c.1.isLt
  have hr := c.2.1.isLt
  have hz := c.2.2.1.isLt
  have hx := c.2.2.2.isLt
  simp only [globalExponents, Set.mem_setOf_eq, columnExponent_x,
    columnExponent_y, columnExponent_r, columnExponent_z]
  omega

def reconstruct (D w C rCap : ℕ)
    (θ : CoefficientIndex D w C rCap → K) : MvPolynomial (Fin 4) K :=
  ∑ c : CoefficientIndex D w C rCap,
    MvPolynomial.monomial (columnExponent c) (θ c)

theorem reconstruct_coeff (D w C rCap : ℕ)
    (θ : CoefficientIndex D w C rCap → K)
    (c : CoefficientIndex D w C rCap) :
    MvPolynomial.coeff (columnExponent c) (reconstruct K D w C rCap θ) = θ c := by
  classical
  simp [reconstruct, MvPolynomial.coeff_sum,
    (columnExponent_injective D w C rCap).eq_iff]

@[simp] theorem reconstruct_zero (D w C rCap : ℕ) :
    reconstruct K D w C rCap (0 : CoefficientIndex D w C rCap → K) = 0 := by
  simp [reconstruct]

theorem reconstruct_injective (D w C rCap : ℕ) :
    Function.Injective (reconstruct K D w C rCap) := by
  intro θ η h
  funext c
  have hh := congrArg (MvPolynomial.coeff (columnExponent c)) h
  simpa only [reconstruct_coeff] using hh

theorem reconstruct_ne_zero (D w C rCap : ℕ)
    (θ : CoefficientIndex D w C rCap → K) (θne : θ ≠ 0) :
    reconstruct K D w C rCap θ ≠ 0 := by
  intro hzero
  apply θne
  apply reconstruct_injective K D w C rCap
  simpa only [reconstruct_zero] using hzero

theorem reconstruct_mem_globalCoefficientBox (D w C rCap : ℕ)
    (θ : CoefficientIndex D w C rCap → K) :
    reconstruct K D w C rCap θ ∈ globalCoefficientBox K D w C rCap := by
  classical
  unfold reconstruct
  apply Submodule.sum_mem
  intro c hc
  exact columnMonomial_mem K D w C rCap c (θ c)

theorem reconstruct_support_caps (D w C rCap : ℕ)
    (θ : CoefficientIndex D w C rCap → K) :
    ∀ d ∈ (reconstruct K D w C rCap θ).support,
      d 1 + d 2 + d 3 ≤ C ∧ d 2 ≤ rCap ∧
        d 0 + w * d 1 + (w - 1) * d 2 < D :=
  reconstruct_mem_globalCoefficientBox K D w C rCap θ

def coefficientCount (D w C rCap : ℕ) : ℕ :=
  ∑ y ∈ Finset.range (C + 1),
    ∑ r ∈ Finset.range (rCap + 1),
      (C + 1 - y - r) * (D - w * y - (w - 1) * r)

theorem coefficient_index_card (D w C rCap : ℕ) :
    Fintype.card (CoefficientIndex D w C rCap) =
      coefficientCount D w C rCap := by
  simp [CoefficientIndex, coefficientCount, Fintype.card_sigma,
    Finset.sum_range]

 



abbrev UVSpanIndex (m C rCap : ℕ) :=
  (d : Fin (C + 1)) × (β : Fin (min d.val rCap + 1)) ×
    (Fin (C + 1 - d.val) ×
      Fin (m - (d.val - rCap) - 2 * β.val))

def localUVRankBound (m C rCap : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (C + 1),
    ∑ β ∈ Finset.range (min d rCap + 1),
      (C + 1 - d) * (m - (d - rCap) - 2 * β)

theorem uv_span_index_card (m C rCap : ℕ) :
    Fintype.card (UVSpanIndex m C rCap) = localUVRankBound m C rCap := by
  simp [UVSpanIndex, localUVRankBound, Fintype.card_sigma, Finset.sum_range,
    mul_comm]

theorem row6660_coefficient_count_exact :
    coefficientCount 5848704 131071 717 9 = 761584486200 := by
  norm_num [coefficientCount]

theorem row6660_local_uv_rank_exact :
    localUVRankBound 32 717 9 = 2905210 := by
  unfold localUVRankBound
  norm_num only [Nat.reduceAdd]
  rw [show 718 = 41 + 677 by decide, Finset.sum_range_add]
  have htail :
      ∑ d ∈ Finset.range 677,
        ∑ β ∈ Finset.range (min (41 + d) 9 + 1),
          (718 - (41 + d)) * (32 - ((41 + d) - 9) - 2 * β) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    apply Finset.sum_eq_zero
    intro β hβ
    have hdlt : d < 677 := Finset.mem_range.mp hd
    rw [show 32 - ((41 + d) - 9) - 2 * β = 0 by omega, mul_zero]
  rw [htail, add_zero]
  norm_num [Finset.sum_range_succ]

theorem row6660_kernel_gate :
    262144 * localUVRankBound 32 717 9 <
      coefficientCount 5848704 131071 717 9 := by
  rw [row6660_coefficient_count_exact, row6660_local_uv_rank_exact]
  norm_num

 
abbrev LocalCoefficientPolynomial := MvPolynomial (Fin 4) K

abbrev LocalPolynomial := Polynomial (LocalCoefficientPolynomial K)

def seedAffine (u₀ u₁ : K) : LocalCoefficientPolynomial K :=
  MvPolynomial.C u₀ + MvPolynomial.X 3 * MvPolynomial.C u₁

def translationVariables (x u₀ u₁ : K) : Fin 4 → LocalPolynomial K :=
  ![Polynomial.X + Polynomial.C (MvPolynomial.C x),
    Polynomial.C (seedAffine K u₀ u₁) +
      Polynomial.X * Polynomial.C (MvPolynomial.X 1) -
      Polynomial.C (MvPolynomial.C ((2 : K)⁻¹)) * Polynomial.X ^ 2 *
        Polynomial.C (MvPolynomial.X 2) +
      Polynomial.X ^ 3 * Polynomial.C (MvPolynomial.X 0),
    Polynomial.C (MvPolynomial.X 1),
    Polynomial.C (MvPolynomial.X 3)]

def secondContactTranslation (x u₀ u₁ : K) :
    MvPolynomial (Fin 4) K →ₐ[K] LocalPolynomial K :=
  MvPolynomial.aeval (translationVariables K x u₀ u₁)

def specialization (P : Polynomial K) (γ : K) :
    MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval
    ![Polynomial.X, P, Polynomial.derivative P, Polynomial.C γ]

def localEvaluation (B R S : Polynomial K) (γ : K) :
    LocalCoefficientPolynomial K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![B, R, S, Polynomial.C γ]

def outerEvaluation (B R S : Polynomial K) (γ : K) :
    LocalPolynomial K →+* Polynomial K :=
  Polynomial.eval₂RingHom (localEvaluation K B R S γ).toRingHom Polynomial.X

 
theorem outerEvaluation_translation
    (Q : MvPolynomial (Fin 4) K) (P : Polynomial K)
    (x u₀ u₁ γ : K) (B : Polynomial K)
    (hP : Polynomial.taylor x P =
      Polynomial.C (u₀ + γ * u₁) +
        Polynomial.X * Polynomial.taylor x (Polynomial.derivative P) -
        Polynomial.C ((2 : K)⁻¹) * Polynomial.X ^ 2 *
          Polynomial.taylor x (Polynomial.derivative (Polynomial.derivative P)) +
        Polynomial.X ^ 3 * B) :
    outerEvaluation K B (Polynomial.taylor x (Polynomial.derivative P))
        (Polynomial.taylor x (Polynomial.derivative (Polynomial.derivative P))) γ
        (secondContactTranslation K x u₀ u₁ Q) =
      Polynomial.taylor x (specialization K P γ Q) := by
  have hhom :
      (outerEvaluation K B (Polynomial.taylor x (Polynomial.derivative P))
        (Polynomial.taylor x (Polynomial.derivative (Polynomial.derivative P))) γ).comp
          (secondContactTranslation K x u₀ u₁).toRingHom =
      (Polynomial.taylorAlgHom x).toRingHom.comp (specialization K P γ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply, outerEvaluation, localEvaluation,
        secondContactTranslation, specialization, Polynomial.algebraMap_apply,
        MvPolynomial.algebraMap_eq]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, outerEvaluation, localEvaluation,
          secondContactTranslation, translationVariables, specialization, seedAffine,
          MvPolynomial.aeval_monomial, Polynomial.algebraMap_apply,
          MvPolynomial.algebraMap_eq, hP] <;> ring
  exact DFunLike.congr_fun hhom Q

 

def HasSecondContactEquations (Q : MvPolynomial (Fin 4) K)
    (x u₀ u₁ : K) (m : ℕ) : Prop :=
  ∀ j < m, (secondContactTranslation K x u₀ u₁ Q).coeff j = 0

theorem X_pow_dvd_taylor_specialization
    (Q : MvPolynomial (Fin 4) K) (P : Polynomial K)
    (x u₀ u₁ γ : K) (m : ℕ)
    (h2 : (2 : K) ≠ 0)
    (hvalue : P.eval x = u₀ + γ * u₁)
    (hequations : HasSecondContactEquations K Q x u₀ u₁ m) :
    (Polynomial.X : Polynomial K) ^ m ∣
      Polynomial.taylor x (specialization K P γ Q) := by
  obtain ⟨B, hB⟩ :=
    ContactSecondContactLocalDivisibility6660Research.exists_secondContactQuotient P x h2
  rw [hvalue] at hB
  have htranslated : (Polynomial.X : LocalPolynomial K) ^ m ∣
      secondContactTranslation K x u₀ u₁ Q :=
    Polynomial.X_pow_dvd_iff.mpr hequations
  obtain ⟨A, hA⟩ := htranslated
  have hmapped : (Polynomial.X : Polynomial K) ^ m ∣
      outerEvaluation K B (Polynomial.taylor x (Polynomial.derivative P))
        (Polynomial.taylor x (Polynomial.derivative (Polynomial.derivative P))) γ
        (secondContactTranslation K x u₀ u₁ Q) := by
    refine ⟨outerEvaluation K B (Polynomial.taylor x (Polynomial.derivative P))
      (Polynomial.taylor x (Polynomial.derivative (Polynomial.derivative P))) γ A, ?_⟩
    rw [hA, map_mul, map_pow]
    simp [outerEvaluation]
  rw [outerEvaluation_translation K Q P x u₀ u₁ γ B hB] at hmapped
  exact hmapped

theorem specialization_monomial_natDegree_le
    (P : Polynomial K) (γ : K) (w : ℕ) (hP : P.natDegree ≤ w)
    (d : Fin 4 →₀ ℕ) (a : K) :
    (specialization K P γ (MvPolynomial.monomial d a)).natDegree ≤
      d 0 + w * d 1 + (w - 1) * d 2 := by
  have hmonomial : MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 *
        MvPolynomial.X 2 ^ d 2 * MvPolynomial.X 3 ^ d 3 := by
    have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
        Finsupp.single 2 (d 2) + Finsupp.single 3 (d 3) := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hd]
    rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
      MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial]
  have hspecialization :
      specialization K P γ (MvPolynomial.monomial d a) =
        Polynomial.C a * Polynomial.X ^ d 0 * P ^ d 1 *
          Polynomial.derivative P ^ d 2 * Polynomial.C γ ^ d 3 := by
    rw [hmonomial]
    simp [specialization, Polynomial.algebraMap_eq]
  rw [hspecialization]
  have hc : (Polynomial.C a : Polynomial K).natDegree ≤ 0 := by simp
  have hx : ((Polynomial.X : Polynomial K) ^ d 0).natDegree ≤ d 0 := by simp
  have hy : (P ^ d 1).natDegree ≤ d 1 * w :=
    Polynomial.natDegree_pow_le_of_le (d 1) hP
  have hderiv : (Polynomial.derivative P).natDegree ≤ w - 1 :=
    (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1)
  have hr : (Polynomial.derivative P ^ d 2).natDegree ≤ d 2 * (w - 1) :=
    Polynomial.natDegree_pow_le_of_le (d 2) hderiv
  have hz : ((Polynomial.C γ : Polynomial K) ^ d 3).natDegree ≤ 0 := by
    simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 3)
      (show (Polynomial.C γ : Polynomial K).natDegree ≤ 0 by simp)
  have hh := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_mul_le_of_le hc hx) hy) hr) hz
  simpa only [Nat.zero_add, Nat.add_zero, Nat.mul_comm] using hh

theorem specialization_natDegree_lt
    (D w C rCap : ℕ) (Q : MvPolynomial (Fin 4) K)
    (P : Polynomial K) (γ : K) (hD : 0 < D)
    (hcaps : Q ∈ globalCoefficientBox K D w C rCap)
    (hP : P.natDegree ≤ w) :
    (specialization K P γ Q).natDegree < D := by
  classical
  have hsupport : ∀ d ∈ Q.support,
      d 1 + d 2 + d 3 ≤ C ∧ d 2 ≤ rCap ∧
        d 0 + w * d 1 + (w - 1) * d 2 < D := hcaps
  have hterms : ∀ d ∈ Q.support,
      (specialization K P γ
        (MvPolynomial.monomial d (MvPolynomial.coeff d Q))).natDegree ≤ D - 1 := by
    intro d hd
    have hweight := (hsupport d hd).2.2
    have hh := specialization_monomial_natDegree_le K P γ w hP d
      (MvPolynomial.coeff d Q)
    omega
  rw [MvPolynomial.as_sum Q, map_sum]
  have hh := Polynomial.natDegree_sum_le_of_forall_le Q.support
    (fun d => specialization K P γ
      (MvPolynomial.monomial d (MvPolynomial.coeff d Q))) hterms
  exact lt_of_le_of_lt hh (by omega)

 

theorem specialization_eq_zero_of_secondContactEquations
    [DecidableEq K] {I : Type*} [DecidableEq I]
    (Q : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (nodes : I ↪ K) (u₀ u₁ : I → K) (support : Finset I) (m : ℕ)
    (h2 : (2 : K) ≠ 0)
    (hequations : ∀ i ∈ support,
      HasSecondContactEquations K Q (nodes i) (u₀ i) (u₁ i) m)
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u₀ i + γ * u₁ i)
    (hdegree : (specialization K P γ Q).natDegree < m * support.card) :
    specialization K P γ Q = 0 := by
  by_contra hnonzero
  have hmult : ∀ i ∈ support,
      m ≤ (specialization K P γ Q).rootMultiplicity (nodes i) := by
    intro i hi
    have hlocal := X_pow_dvd_taylor_specialization K Q P (nodes i)
      (u₀ i) (u₁ i) γ m h2 (hvalues i hi) (hequations i hi)
    have hshifted : (Polynomial.X - Polynomial.C (nodes i)) ^ m ∣
        specialization K P γ Q :=
      (ContactLocalDivisibility.shifted_power_dvd_iff_taylor_coeff_zero
        (specialization K P γ Q) (nodes i) m).mpr
          (Polynomial.X_pow_dvd_iff.mp hlocal)
    exact (Polynomial.le_rootMultiplicity_iff hnonzero).mpr hshifted
  have hbound := BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
    (specialization K P γ Q) nodes support m hmult
  exact (Nat.not_le_of_gt hdegree) hbound

 


theorem row6660_specialization_eq_zero
    (Q : MvPolynomial (Fin 4) IRSProfile.Field)
    (P : Polynomial IRSProfile.Field) (γ : IRSProfile.Field)
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field)
    (support : Finset IRSProfile.Index)
    (h2 : (2 : IRSProfile.Field) ≠ 0)
    (hcaps : Q ∈ globalCoefficientBox IRSProfile.Field 5848704 131071 717 9)
    (hequations : ∀ i : IRSProfile.Index,
      HasSecondContactEquations IRSProfile.Field Q
        (IRSProfile.domain i) (u₀ i) (u₁ i) 32)
    (hP : P.natDegree ≤ 131071)
    (hcard : 182772 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (IRSProfile.domain i) = u₀ i + γ * u₁ i) :
    specialization IRSProfile.Field P γ Q = 0 := by
  apply specialization_eq_zero_of_secondContactEquations
    IRSProfile.Field Q P γ IRSProfile.domain u₀ u₁ support 32 h2
  · intro i hi
    exact hequations i
  · exact hvalues
  · have hdegree := specialization_natDegree_lt IRSProfile.Field
      5848704 131071 717 9 Q P γ (by decide) hcaps hP
    have hbound : 5848704 ≤ 32 * support.card := by omega
    exact hdegree.trans_le hbound

end

end ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research

#print axioms ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research.reconstruct_ne_zero
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research.row6660_kernel_gate
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research.outerEvaluation_translation
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research.X_pow_dvd_taylor_specialization
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research.specialization_eq_zero_of_secondContactEquations
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research.row6660_specialization_eq_zero
