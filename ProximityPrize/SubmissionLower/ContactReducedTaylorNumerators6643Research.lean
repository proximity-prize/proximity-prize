import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSingularDegreeBounds
import ProximityPrize.SubmissionLower.ContactJointTaylorMiddleCap6631Research

/-!
# Polynomially reduced contact-Taylor numerators

The reduction subtracts explicit multiples of the defining surface.  No
division by a leading coefficient, monicity, or genericity is involved.
-/

namespace ProximityPrize.SubmissionLower.ContactReducedTaylorNumerators6643Research

open scoped BigOperators
open ContactDifferentialRing ContactTaylorNumerators ContactSingularDegreeBounds
open ContactPost6464MinkowskiRecurrenceResearch ContactJointTaylorMiddleCap6631Research

noncomputable section

variable {K : Type*} [Field K]

abbrev Poly (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The contact vector field with its single denominator cleared. -/
def vectorNumerator (F P : Poly K) : Poly K :=
  polyH K F * MvPolynomial.pderiv (0 : Fin 4) P +
    MvPolynomial.X (2 : Fin 4) * polyH K F * MvPolynomial.pderiv (1 : Fin 4) P +
    polyG K F * MvPolynomial.pderiv (2 : Fin 4) P

theorem vectorNumerator_surface (F : Poly K) : vectorNumerator F F = 0 := by
  unfold vectorNumerator polyG polyH
  ring

theorem vectorNumerator_mul (F P Q : Poly K) :
    vectorNumerator F (P * Q) = P * vectorNumerator F Q + Q * vectorNumerator F P := by
  simp only [vectorNumerator, MvPolynomial.pderiv_mul]
  ring

theorem vectorNumerator_sub (F P Q : Poly K) :
    vectorNumerator F (P - Q) = vectorNumerator F P - vectorNumerator F Q := by
  simp only [vectorNumerator, map_sub]
  ring

theorem numeratorStep_eq_vector (F P : Poly K) (b : ℕ) :
    numeratorStep K F b P =
      polyH K F * vectorNumerator F P -
        ((2 * b : ℕ) : Poly K) * P * vectorNumerator F (polyH K F) := by
  unfold numeratorStep clearedStep vectorNumerator
  ring

theorem numeratorStep_sub (F P Q : Poly K) (b : ℕ) :
    numeratorStep K F b (P - Q) = numeratorStep K F b P - numeratorStep K F b Q := by
  simp only [numeratorStep_eq_vector, vectorNumerator_sub]
  ring

/-- The recurrence preserves the principal surface ideal exactly. -/
theorem numeratorStep_mul_surface (F Q : Poly K) (b : ℕ) :
    numeratorStep K F b (F * Q) = F * numeratorStep K F b Q := by
  simp only [numeratorStep_eq_vector, vectorNumerator_mul, vectorNumerator_surface,
    mul_zero, add_zero]
  ring

theorem numeratorStep_congr (F P Q : Poly K) (b : ℕ) (h : F ∣ P - Q) :
    F ∣ numeratorStep K F b P - numeratorStep K F b Q := by
  obtain ⟨T, hT⟩ := h
  refine ⟨numeratorStep K F b T, ?_⟩
  rw [← numeratorStep_sub, hT, numeratorStep_mul_surface]

theorem vectorNumerator_R_degree_bound (F P : Poly K) (a s : ℕ)
    (hs : 1 ≤ s) (hF : F.degreeOf (2 : Fin 4) ≤ s)
    (hP : P.degreeOf (2 : Fin 4) ≤ a) :
    (vectorNumerator F P).degreeOf (2 : Fin 4) ≤ a + s := by
  let H := polyH K F
  let G := polyG K F
  let R : Poly K := MvPolynomial.X (2 : Fin 4)
  have hR : R.degreeOf (2 : Fin 4) ≤ 1 := by simp [R]
  have hH : H.degreeOf (2 : Fin 4) ≤ s - 1 :=
    pderiv_same_degree_bound (2 : Fin 4) F s hF
  have hG : G.degreeOf (2 : Fin 4) ≤ s + 1 :=
    polyG_degree_bound (2 : Fin 4) F s 1 hF hR
  have hPX := pderiv_degree_bound (0 : Fin 4) (2 : Fin 4) P a hP
  have hPY := pderiv_degree_bound (1 : Fin 4) (2 : Fin 4) P a hP
  have hPR := pderiv_same_degree_bound (2 : Fin 4) P a hP
  have hx : (H * MvPolynomial.pderiv (0 : Fin 4) P).degreeOf (2 : Fin 4) ≤ a + s := by
    have h := degree_mul_bound (2 : Fin 4) hH hPX
    omega
  have hy : (R * H * MvPolynomial.pderiv (1 : Fin 4) P).degreeOf (2 : Fin 4) ≤ a + s := by
    have h := degree_mul_bound (2 : Fin 4) (degree_mul_bound (2 : Fin 4) hR hH) hPY
    omega
  have hr : (G * MvPolynomial.pderiv (2 : Fin 4) P).degreeOf (2 : Fin 4) ≤ a + s := by
    by_cases ha : a = 0
    · have hz := pderiv_eq_zero_of_degree_bound_zero (2 : Fin 4) P (by simpa [ha] using hP)
      simp [hz]
    · have h := degree_mul_bound (2 : Fin 4) hG hPR
      omega
  exact degree_add_bound (2 : Fin 4) (degree_add_bound (2 : Fin 4) hx hy) hr

/-- A positive-weight derivative really vanishes below that weight. -/
theorem pderiv_eq_zero_of_wt_lt (weights : Fin 4 → ℕ) (P : Poly K) (i : Fin 4)
    (hP : wt weights P < weights i) : MvPolynomial.pderiv i P = 0 := by
  apply MvPolynomial.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hh := MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i P d hd)
  simp only [map_add, Finsupp.weight_single, one_nsmul] at hh
  change Finsupp.weight weights d + weights i ≤ wt weights P at hh
  omega

/-- The explicit factor of the unique possible excess coefficient. -/
def excessFactor (F P : Poly K) (s b : ℕ) : Poly K :=
  (s : Poly K) *
    ((s : Poly K) * liftedCoefficient F s *
        MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient P (2 * b * (s - 1))) -
      ((2 * b * (s - 1) + 2 * b : ℕ) : Poly K) *
        MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient F s) *
          liftedCoefficient P (2 * b * (s - 1)))

def reductionMultiplier (F P : Poly K) (s b : ℕ) : Poly K :=
  excessFactor F P s b * MvPolynomial.X (2 : Fin 4) ^ ((2 * b + 1) * (s - 1))

def reducedStep (F P : Poly K) (s b : ℕ) : Poly K :=
  numeratorStep K F b P - reductionMultiplier F P s b * F

def reducedNumerator (F : Poly K) (s : ℕ) : ℕ → Poly K
  | 0 => MvPolynomial.X (1 : Fin 4)
  | b + 1 => reducedStep F (reducedNumerator F s b) s b

@[simp] theorem reducedNumerator_zero (F : Poly K) (s : ℕ) :
    reducedNumerator F s 0 = MvPolynomial.X (1 : Fin 4) := rfl

@[simp] theorem reducedNumerator_succ (F : Poly K) (s b : ℕ) :
    reducedNumerator F s (b + 1) = reducedStep F (reducedNumerator F s b) s b := rfl

/-- The reduction is valid even when the nominal leading coefficient vanishes. -/
theorem numerator_sub_reduced_dvd (F : Poly K) (s b : ℕ) :
    F ∣ numerator K F b - reducedNumerator F s b := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hstep := numeratorStep_congr F (numerator K F b) (reducedNumerator F s b) b ih
      obtain ⟨T, hT⟩ := hstep
      refine ⟨T + reductionMultiplier F (reducedNumerator F s b) s b, ?_⟩
      rw [numerator_succ, reducedNumerator_succ, reducedStep]
      linear_combination hT

def reducedCommonNumeratorTerm (F : Poly K) (s w : ℕ) (c : ℕ → K) (x : K)
    (j : ℕ) : Poly K :=
  MvPolynomial.C (c j) * reducedNumerator F s j *
    polyH K F ^ (2 * (w - j)) *
      (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j

def reducedClearedTaylorNumerator (F : Poly K) (s w : ℕ) (c : ℕ → K) (x : K) :
    Poly K :=
  ∑ j ∈ Finset.range (w + 1), reducedCommonNumeratorTerm F s w c x j

def reducedAgreementNumerator (F : Poly K) (s w : ℕ) (c : ℕ → K) (x u₀ u₁ : K) :
    Poly K :=
  reducedClearedTaylorNumerator F s w c x -
    affineSeedPolynomial u₀ u₁ * polyH K F ^ (2 * w)

theorem commonNumeratorTerm_sub_reduced_dvd (F : Poly K) (s w j : ℕ)
    (c : ℕ → K) (x : K) :
    F ∣ commonNumeratorTerm F w c x j - reducedCommonNumeratorTerm F s w c x j := by
  obtain ⟨T, hT⟩ := numerator_sub_reduced_dvd F s j
  refine ⟨MvPolynomial.C (c j) * T * polyH K F ^ (2 * (w - j)) *
    (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j, ?_⟩
  unfold commonNumeratorTerm reducedCommonNumeratorTerm
  linear_combination MvPolynomial.C (c j) * polyH K F ^ (2 * (w - j)) *
    (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j * hT

theorem clearedTaylorNumerator_sub_reduced_dvd (F : Poly K) (s w : ℕ)
    (c : ℕ → K) (x : K) :
    F ∣ clearedTaylorNumerator F w c x - reducedClearedTaylorNumerator F s w c x := by
  unfold clearedTaylorNumerator reducedClearedTaylorNumerator
  rw [← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun j _ => commonNumeratorTerm_sub_reduced_dvd F s w j c x

/-- Original and reduced agreement polynomials define the same section on F. -/
theorem agreementNumerator_sub_reduced_dvd (F : Poly K) (s w : ℕ)
    (c : ℕ → K) (x u₀ u₁ : K) :
    F ∣ agreementNumerator F w c x u₀ u₁ -
      reducedAgreementNumerator F s w c x u₀ u₁ := by
  unfold agreementNumerator reducedAgreementNumerator
  simpa only [sub_sub_sub_cancel_right] using
    clearedTaylorNumerator_sub_reduced_dvd F s w c x

end


end ProximityPrize.SubmissionLower.ContactReducedTaylorNumerators6643Research
