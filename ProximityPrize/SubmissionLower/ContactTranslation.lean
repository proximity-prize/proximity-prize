import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactInterpolation
import ProximityPrize.SubmissionLower.ContactLocalDivisibility



/-!
# Actual binomial translation of the contact interpolant

Model label: gpt-5.

The new variable T is the outer univariate polynomial variable. Inner
variables 0,1,2 are Y,R,Z. This file identifies the explicit coefficient-array
equations with the coefficients of an actual algebra-homomorphic translation
of the reconstructed polynomial. No received derivative is assumed.

The coefficient divisibilities specialize to genuine contact multiplicities.
The weighted support caps give the required degree inequality, hence universal
polynomial vanishing on sufficiently large agreement supports for the frozen
profile. The geometric alignment bound is not asserted in this module.
-/

namespace ProximityPrize.SubmissionLower.ContactTranslation

open ContactRankKernel ContactInterpolation
open ProximityPrize.Benchmark
open scoped BigOperators

noncomputable section

variable (K : Type*) [Field K]

abbrev LocalPolynomial := Polynomial (Poly K)

def translationVariables (x u₀ u₁ : K) : Fin 4 → LocalPolynomial K :=
  ![Polynomial.X + Polynomial.C (MvPolynomial.C x),
    Polynomial.X * Polynomial.C (MvPolynomial.X 0) +
      Polynomial.C (seedAffine K u₀ u₁),
    Polynomial.C (MvPolynomial.X 1),
    Polynomial.C (MvPolynomial.X 2)]

/-- X maps to x+T and Y maps to u0+Z*u1+T*Y. -/
def homogenizedTranslation (x u₀ u₁ : K) :
    MvPolynomial (Fin 4) K →ₐ[K] LocalPolynomial K :=
  MvPolynomial.aeval (translationVariables K x u₀ u₁)

theorem columnMonomial_eq (D w L s : ℕ)
    (c : CoefficientIndex D w L s) (a : K) :
    MvPolynomial.monomial (columnExponent c) a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ c.2.2.2.val *
        MvPolynomial.X 1 ^ c.1.val * MvPolynomial.X 2 ^ c.2.1.val *
        MvPolynomial.X 3 ^ c.2.2.1.val := by
  rw [columnExponent, MvPolynomial.monomial_add_single,
    MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem localMonomial_eq (f j z : ℕ) :
    localMonomial K f j z =
      MvPolynomial.X 0 ^ f * MvPolynomial.X 1 ^ j * MvPolynomial.X 2 ^ z := by
  rw [localMonomial, MvPolynomial.monomial_add_single,
    MvPolynomial.monomial_add_single, ← MvPolynomial.X_pow_eq_monomial]

/-- A coefficient identity over an arbitrary commutative ring. Expanding
only the second affine power avoids a convolution reindexing argument. -/
theorem coeff_shifted_affine_product
    {A : Type*} [CommRing A] (x a y b : A) (e i r : ℕ) :
    (((Polynomial.X + Polynomial.C x) ^ e *
        (Polynomial.X * Polynomial.C y + Polynomial.C a) ^ i *
        Polynomial.C b) : Polynomial A).coeff r =
      ∑ f : Fin (i + 1), if f.val ≤ r then
        (x ^ (e - (r - f.val)) * (e.choose (r - f.val) : A)) *
          (y ^ f.val * a ^ (i - f.val) * (i.choose f.val : A) * b)
      else 0 := by
  rw [add_pow (Polynomial.X * Polynomial.C y) (Polynomial.C a) i,
    Finset.mul_sum, Finset.sum_mul, Polynomial.finsetSum_coeff]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro f hf
  have hfactor :
      (((Polynomial.X + Polynomial.C x) ^ e *
        ((Polynomial.X * Polynomial.C y) ^ f.val *
          Polynomial.C a ^ (i - f.val) * (i.choose f.val : Polynomial A))) *
          Polynomial.C b) =
        (((Polynomial.X + Polynomial.C x) ^ e *
          Polynomial.C (y ^ f.val * a ^ (i - f.val) * (i.choose f.val : A) * b)) *
          Polynomial.X ^ f.val) := by
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [hfactor, Polynomial.coeff_mul_X_pow']
  split_ifs with hfr
  · rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_add_C_pow]
  · rfl

theorem translation_column (D w L s : ℕ) (x u₀ u₁ : K)
    (c : CoefficientIndex D w L s) (a : K) :
    homogenizedTranslation K x u₀ u₁ (MvPolynomial.monomial (columnExponent c) a) =
      Polynomial.C (MvPolynomial.C a) *
        (Polynomial.X + Polynomial.C (MvPolynomial.C x)) ^ c.2.2.2.val *
        (Polynomial.X * Polynomial.C (MvPolynomial.X 0) +
          Polynomial.C (seedAffine K u₀ u₁)) ^ c.1.val *
        Polynomial.C (MvPolynomial.X 1) ^ c.2.1.val *
        Polynomial.C (MvPolynomial.X 2) ^ c.2.2.1.val := by
  rw [columnMonomial_eq K D w L s c a]
  simp [homogenizedTranslation, translationVariables,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

/-- The explicit binomial entry is the actual coefficient of a translated
column, including its arbitrary field coefficient. -/
theorem translation_column_coeff (D w L s : ℕ) (x u₀ u₁ : K)
    (c : CoefficientIndex D w L s) (a : K) (r : ℕ) :
    (homogenizedTranslation K x u₀ u₁
      (MvPolynomial.monomial (columnExponent c) a)).coeff r =
        a • blockEntry K D w L s x u₀ u₁ c r := by
  have hfactor :
      homogenizedTranslation K x u₀ u₁
        (MvPolynomial.monomial (columnExponent c) a) =
      Polynomial.C (MvPolynomial.C a) *
        ((Polynomial.X + Polynomial.C (MvPolynomial.C x)) ^ c.2.2.2.val *
          (Polynomial.X * Polynomial.C (MvPolynomial.X 0) +
            Polynomial.C (seedAffine K u₀ u₁)) ^ c.1.val *
          Polynomial.C (MvPolynomial.X 1 ^ c.2.1.val *
            MvPolynomial.X 2 ^ c.2.2.1.val)) := by
    rw [translation_column K D w L s x u₀ u₁ c a]
    simp only [map_mul, map_pow]
    ring
  rw [hfactor, Polynomial.coeff_C_mul, coeff_shifted_affine_product]
  unfold blockEntry
  rw [Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs with hfr
  · simp only [localMonomial_eq, MvPolynomial.smul_eq_C_mul,
      map_mul, map_pow, map_natCast]
    ring
  · simp

/-- The array map is now identified with an actual polynomial translation,
not just a matrix carrying the expected labels. -/
theorem translation_reconstruct_coeff (D w L s : ℕ) (x u₀ u₁ : K)
    (θ : CoefficientIndex D w L s → K) (r : ℕ) :
    (homogenizedTranslation K x u₀ u₁ (reconstruct K D w L s θ)).coeff r =
      ((extractBlock K D w L s x u₀ u₁ r θ) : Poly K) := by
  rw [reconstruct, map_sum, Polynomial.finsetSum_coeff]
  simp only [translation_column_coeff]
  change (∑ c : CoefficientIndex D w L s,
    θ c • blockEntry K D w L s x u₀ u₁ c r) =
      (((∑ c : CoefficientIndex D w L s,
        θ c • boundedBlockEntry K D w L s x u₀ u₁ c r) :
          coefficientBox K (min r L) L s) : Poly K)
  simp [boundedBlockEntry]

/-- A genuine nonzero interpolant whose actual translated coefficient at
every node and every block is divisible by the required contact power. -/
theorem exists_frozen_translated_contact_interpolant
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧ Q ∈ globalCoefficientBox IRSProfile.Field 3504835 131071 170 6 ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        slopeDifference IRSProfile.Field ^ (19 - r) ∣
          (homogenizedTranslation IRSProfile.Field
            (IRSProfile.domain i) (u₀ i) (u₁ i) Q).coeff r := by
  obtain ⟨Q, θ, hQ, hcaps, hreconstruct, hequations⟩ :=
    exists_frozen_nonzero_polynomial_and_equations u₀ u₁
  refine ⟨Q, hQ, hcaps, ?_⟩
  intro i r
  rw [hreconstruct, translation_reconstruct_coeff]
  exact all_blocks_divisible_of_equations IRSProfile.Field 3504835 131071 170 6 19
    (IRSProfile.domain i) (u₀ i) (u₁ i) θ (hequations i) r

/-- Local Y is the candidate derivative plus T times a residual quotient. -/
def contactEvaluation (R B : Polynomial K) (γ : K) : Poly K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![R + Polynomial.X * B, R, Polynomial.C γ]

def outerEvaluation (R B : Polynomial K) (γ : K) :
    LocalPolynomial K →+* Polynomial K :=
  Polynomial.eval₂RingHom (contactEvaluation K R B γ).toRingHom Polynomial.X

@[simp] theorem contactEvaluation_slopeDifference (R B : Polynomial K) (γ : K) :
    contactEvaluation K R B γ (slopeDifference K) = Polynomial.X * B := by
  simp [contactEvaluation, slopeDifference]

theorem contactEvaluation_seedAffine (R B : Polynomial K) (γ u₀ u₁ : K) :
    contactEvaluation K R B γ (seedAffine K u₀ u₁) =
      Polynomial.C (u₀ + γ * u₁) := by
  rw [seedAffine, ← MvPolynomial.C_mul_X_eq_monomial]
  simp [contactEvaluation, Polynomial.algebraMap_eq, mul_comm]

/-- Coefficient contact divisibility supplies true order after substitution.
The full exponent m-r makes this valid uniformly, also for r≥m. -/
theorem outerEvaluation_contact_dvd
    (H : LocalPolynomial K) (m : ℕ) (R B : Polynomial K) (γ : K)
    (hcoeff : ∀ r : ℕ, slopeDifference K ^ (m - r) ∣ H.coeff r) :
    (Polynomial.X : Polynomial K) ^ m ∣ outerEvaluation K R B γ H := by
  classical
  change (Polynomial.X : Polynomial K) ^ m ∣
    H.eval₂ (contactEvaluation K R B γ).toRingHom Polynomial.X
  rw [Polynomial.eval₂_eq_sum]
  change (Polynomial.X : Polynomial K) ^ m ∣
    ∑ r ∈ H.support, contactEvaluation K R B γ (H.coeff r) * Polynomial.X ^ r
  apply Finset.dvd_sum
  intro r hr
  have hlocal : (Polynomial.X : Polynomial K) ^ (m - r) ∣
      contactEvaluation K R B γ (H.coeff r) := by
    obtain ⟨q, hq⟩ := hcoeff r
    refine ⟨B ^ (m - r) * contactEvaluation K R B γ q, ?_⟩
    simp only [hq, map_mul, map_pow, contactEvaluation_slopeDifference,
      mul_pow, mul_assoc]
  have hprod := mul_dvd_mul hlocal
    (dvd_refl ((Polynomial.X : Polynomial K) ^ r))
  have htotal : (Polynomial.X : Polynomial K) ^ ((m - r) + r) ∣
      contactEvaluation K R B γ (H.coeff r) * Polynomial.X ^ r := by
    simpa only [pow_add] using hprod
  exact (pow_dvd_pow Polynomial.X (show m ≤ (m - r) + r by omega)).trans htotal

def specialization (P : Polynomial K) (γ : K) :
    MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, P, P.derivative, Polynomial.C γ]

/-- The two actual substitution maps agree whenever the second-order
contact residual has been written as T²B. -/
theorem outerEvaluation_translation
    (Q : MvPolynomial (Fin 4) K) (P : Polynomial K)
    (x u₀ u₁ γ : K) (B : Polynomial K)
    (hP : Polynomial.taylor x P =
      Polynomial.C (u₀ + γ * u₁) + Polynomial.X *
        (Polynomial.taylor x P.derivative + Polynomial.X * B)) :
    outerEvaluation K (Polynomial.taylor x P.derivative) B γ
        (homogenizedTranslation K x u₀ u₁ Q) =
      Polynomial.taylor x (specialization K P γ Q) := by
  have hhom :
      (outerEvaluation K (Polynomial.taylor x P.derivative) B γ).comp
        (homogenizedTranslation K x u₀ u₁).toRingHom =
      (Polynomial.taylorAlgHom x).toRingHom.comp
        (specialization K P γ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply, outerEvaluation, contactEvaluation,
        homogenizedTranslation, specialization, Polynomial.algebraMap_apply,
        MvPolynomial.algebraMap_eq]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, outerEvaluation, contactEvaluation,
          homogenizedTranslation, translationVariables, specialization,
          seedAffine, MvPolynomial.aeval_monomial, Polynomial.algebraMap_apply,
          MvPolynomial.algebraMap_eq, hP] <;> ring
  exact DFunLike.congr_fun hhom Q

/-- Agreement of values alone, not derivative data, gives order m in the
specialized interpolant at the chosen node. -/
theorem X_pow_dvd_taylor_specialization
    (Q : MvPolynomial (Fin 4) K) (P : Polynomial K)
    (x u₀ u₁ γ : K) (m : ℕ)
    (hvalue : P.eval x = u₀ + γ * u₁)
    (hcoeff : ∀ r : ℕ, slopeDifference K ^ (m - r) ∣
      (homogenizedTranslation K x u₀ u₁ Q).coeff r) :
    (Polynomial.X : Polynomial K) ^ m ∣
      Polynomial.taylor x (specialization K P γ Q) := by
  obtain ⟨B, hB⟩ := ContactLocalDivisibility.X_sq_dvd_contactResidual P x
  have hP : Polynomial.taylor x P =
      Polynomial.C (u₀ + γ * u₁) + Polynomial.X *
        (Polynomial.taylor x P.derivative + Polynomial.X * B) := by
    change Polynomial.taylor x P - Polynomial.C (P.eval x) -
      Polynomial.X * Polynomial.taylor x P.derivative = Polynomial.X ^ 2 * B at hB
    rw [hvalue] at hB
    linear_combination hB
  have hh := outerEvaluation_contact_dvd K
    (homogenizedTranslation K x u₀ u₁ Q) m (Polynomial.taylor x P.derivative) B γ hcoeff
  rw [outerEvaluation_translation K Q P x u₀ u₁ γ B hP] at hh
  exact hh

/-- The generic many-root finish. Its explicit degree input is discharged
from the weighted support caps in the lemmas below. -/
theorem specialization_eq_zero_of_contact_and_degree
    [DecidableEq K] {I : Type*} [DecidableEq I]
    (Q : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (nodes : I ↪ K) (u₀ u₁ : I → K) (support : Finset I) (m : ℕ)
    (hcontact : ∀ i ∈ support, ∀ r : ℕ, slopeDifference K ^ (m - r) ∣
      (homogenizedTranslation K (nodes i) (u₀ i) (u₁ i) Q).coeff r)
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u₀ i + γ * u₁ i)
    (hdegree : (specialization K P γ Q).natDegree < m * support.card) :
    specialization K P γ Q = 0 := by
  by_contra hnonzero
  have hmult : ∀ i ∈ support,
      m ≤ (specialization K P γ Q).rootMultiplicity (nodes i) := by
    intro i hi
    have hlocal := X_pow_dvd_taylor_specialization K Q P
      (nodes i) (u₀ i) (u₁ i) γ m (hvalues i hi) (hcontact i hi)
    have hshifted : (Polynomial.X - Polynomial.C (nodes i)) ^ m ∣
        specialization K P γ Q :=
      (ContactLocalDivisibility.shifted_power_dvd_iff_taylor_coeff_zero
        (specialization K P γ Q) (nodes i) m).mpr (Polynomial.X_pow_dvd_iff.mp hlocal)
    exact (Polynomial.le_rootMultiplicity_iff hnonzero).mpr hshifted
  have hh := BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
    (specialization K P γ Q) nodes support m hmult
  exact (Nat.not_le_of_gt hdegree) hh

theorem monomial_eq (d : Fin 4 →₀ ℕ) (a : K) :
    MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 *
        MvPolynomial.X 2 ^ d 2 * MvPolynomial.X 3 ^ d 3 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) + Finsupp.single 3 (d 3) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hd]
  rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem specialization_monomial
    (P : Polynomial K) (γ : K) (d : Fin 4 →₀ ℕ) (a : K) :
    specialization K P γ (MvPolynomial.monomial d a) =
      Polynomial.C a * Polynomial.X ^ d 0 * P ^ d 1 * P.derivative ^ d 2 *
        Polynomial.C γ ^ d 3 := by
  rw [monomial_eq K d a]
  simp [specialization, Polynomial.algebraMap_eq]

/-- Derivatives cost at most w-1 in degree, including constants and zero.
No characteristic or separability assumption is needed for this estimate. -/
theorem specialization_monomial_natDegree_le
    (P : Polynomial K) (γ : K) (w : ℕ) (hP : P.natDegree ≤ w)
    (d : Fin 4 →₀ ℕ) (a : K) :
    (specialization K P γ (MvPolynomial.monomial d a)).natDegree ≤
      d 0 + w * d 1 + (w - 1) * d 2 := by
  rw [specialization_monomial]
  have hc : (Polynomial.C a : Polynomial K).natDegree ≤ 0 := by simp
  have hx : ((Polynomial.X : Polynomial K) ^ d 0).natDegree ≤ d 0 := by simp
  have hy : (P ^ d 1).natDegree ≤ d 1 * w :=
    Polynomial.natDegree_pow_le_of_le (d 1) hP
  have hderiv : P.derivative.natDegree ≤ w - 1 :=
    (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1)
  have hr : (P.derivative ^ d 2).natDegree ≤ d 2 * (w - 1) :=
    Polynomial.natDegree_pow_le_of_le (d 2) hderiv
  have hz : ((Polynomial.C γ : Polynomial K) ^ d 3).natDegree ≤ 0 := by
    simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 3)
      (show (Polynomial.C γ : Polynomial K).natDegree ≤ 0 by simp)
  have hh := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_mul_le_of_le hc hx) hy) hr) hz
  simpa only [Nat.zero_add, Nat.add_zero, Nat.mul_comm] using hh

/-- The actual support inequalities imply the actual specialized degree cap;
the assertion remains true when specialization produces the zero polynomial. -/
theorem specialization_natDegree_lt
    (D w L s : ℕ) (Q : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (hD : 0 < D) (hcaps : Q ∈ globalCoefficientBox K D w L s)
    (hP : P.natDegree ≤ w) :
    (specialization K P γ Q).natDegree < D := by
  classical
  have hsupport : ∀ d ∈ Q.support,
      d 1 + d 3 ≤ L ∧ d 2 ≤ s ∧ d 0 + w * d 1 + (w - 1) * d 2 < D := hcaps
  have hterms : ∀ d ∈ Q.support,
      (specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))).natDegree ≤
        D - 1 := by
    intro d hd
    have hweight := (hsupport d hd).2.2
    have hh := specialization_monomial_natDegree_le K P γ w hP d (MvPolynomial.coeff d Q)
    omega
  rw [MvPolynomial.as_sum Q, map_sum]
  have hh := Polynomial.natDegree_sum_le_of_forall_le Q.support
    (fun d => specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))) hterms
  exact lt_of_le_of_lt hh (by omega)

/-- The full interpolation/vanishing front end for the frozen challenge
profile. The same nonzero Q works for every seed, polynomial, and sufficiently
large agreement support. This is not the remaining geometric seed count. -/
theorem exists_frozen_universal_vanishing_interpolant
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧ Q ∈ globalCoefficientBox IRSProfile.Field 3504835 131071 170 6 ∧
      ∀ (γ : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ 131071 → 184465 ≤ support.card →
        (∀ i ∈ support, P.eval (IRSProfile.domain i) = u₀ i + γ * u₁ i) →
        specialization IRSProfile.Field P γ Q = 0 := by
  classical
  obtain ⟨Q, hQ, hcaps, hcontact⟩ := exists_frozen_translated_contact_interpolant u₀ u₁
  refine ⟨Q, hQ, hcaps, ?_⟩
  intro γ P support hP hcard hvalues
  apply specialization_eq_zero_of_contact_and_degree IRSProfile.Field Q P γ
    IRSProfile.domain u₀ u₁ support 19
  · intro i hi r
    exact hcontact i r
  · exact hvalues
  · have hdegree := specialization_natDegree_lt IRSProfile.Field
      3504835 131071 170 6 Q P γ (by decide) hcaps hP
    have hbound : 3504835 ≤ 19 * support.card := by omega
    exact hdegree.trans_le hbound

end

end ProximityPrize.SubmissionLower.ContactTranslation

#print axioms ProximityPrize.SubmissionLower.ContactTranslation.coeff_shifted_affine_product
#print axioms ProximityPrize.SubmissionLower.ContactTranslation.translation_column_coeff
#print axioms ProximityPrize.SubmissionLower.ContactTranslation.translation_reconstruct_coeff
#print axioms ProximityPrize.SubmissionLower.ContactTranslation.exists_frozen_translated_contact_interpolant
#print axioms ProximityPrize.SubmissionLower.ContactTranslation.outerEvaluation_contact_dvd
#print axioms ProximityPrize.SubmissionLower.ContactTranslation.X_pow_dvd_taylor_specialization
#print axioms ProximityPrize.SubmissionLower.ContactTranslation.specialization_eq_zero_of_contact_and_degree
#print axioms ProximityPrize.SubmissionLower.ContactTranslation.specialization_natDegree_lt
#print axioms ProximityPrize.SubmissionLower.ContactTranslation.exists_frozen_universal_vanishing_interpolant
