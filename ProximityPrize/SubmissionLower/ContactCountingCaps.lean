import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
import ProximityPrize.SubmissionLower.ContactFactorCaps
namespace ProximityPrize.SubmissionLower.ContactCountingCaps

open scoped Classical
open ContactAlignmentParameters ContactTaylorNumerators ContactGenericSurface ContactInterpolation
open ContactPolynomialSolutions ContactPrimeSeedIncidence

noncomputable section

def capAt (v : DegreeVector) : Fin 3 → ℕ := ![v.y, v.r, v.z]

def agreementCaps (ell s L w : ℕ) : DegreeVector :=
  ⟨1 + 2 * w * ell, w * (2 * s - 1), 2 * w * L + 1⟩

variable {K Ω : Type} [Field K] [Field Ω]

def HasCaps (Q : MvPolynomial (Fin 3) Ω) (v : DegreeVector) : Prop :=
  ∀ i, Q.degreeOf i ≤ capAt v i

variable (φ : Polynomial K →+* Ω)

def firstTailSurface (F : MvPolynomial (Fin 4) K) (w : ℕ) : MvPolynomial (Fin 3) Ω :=
  surfaceMap φ (numerator K F (w + 1))

theorem surface_agreement_caps
    (F : MvPolynomial (Fin 4) K) (ell s L : ℕ) (hs : 1 ≤ s)
    (hY : F.degreeOf 1 ≤ ell) (hR : F.degreeOf 2 ≤ s) (hZ : F.degreeOf 3 ≤ L)
    (w : ℕ) (c : ℕ → K) (x u₀ u₁ : K) :
    HasCaps (surfaceMap φ (agreementNumerator F w c x u₀ u₁))
      (agreementCaps ell s L w) := by
  obtain ⟨hy, hr, hz⟩ := agreementNumerator_degree_bounds F ell s L hs hY hR hZ w c x u₀ u₁
  intro i
  fin_cases i
  · exact (surfaceMap_degreeOf_le φ _ 0).trans hy
  · exact (surfaceMap_degreeOf_le φ _ 1).trans hr
  · exact (surfaceMap_degreeOf_le φ _ 2).trans hz

theorem selected_firstTail_zero
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (γ : K) (w : ℕ) (hdegree : (selected γ).natDegree ≤ w)
    (hsolution : ContactTranslation.specialization K (selected γ) γ F = 0) :
    MvPolynomial.aeval (selectedPoint φ selected γ) (firstTailSurface φ F w) = 0 := by
  change MvPolynomial.eval (selectedPoint φ selected γ)
    (surfaceMap φ (numerator K F (w + 1))) = 0
  rw [eval_surfaceMap]
  have hv : Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ) =
      polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact polynomialPoint_numerator_zero (φ.comp Polynomial.C) F (selected γ) γ
    (φ Polynomial.X) hsolution (w + 1) (Nat.lt_succ_of_le hdegree)

section MixedGates

variable (G T : MvPolynomial (Fin 3) Ω) (g t : DegreeVector)

theorem actual_pair_degree_le (hG : HasCaps G g) (hT : HasCaps T t) (j k : Fin 3) :
    T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k ≤
      capAt t j * capAt g k + capAt g j * capAt t k :=
  Nat.add_le_add (Nat.mul_le_mul (hT j) (hG k)) (Nat.mul_le_mul (hG j) (hT k))

theorem pair_caps_below_of_mixed (p : ℕ)
    (hY : mixed g t unitY < p) (hR : mixed g t unitR < p) (hZ : mixed g t unitZ < p) :
    ∀ j k : Fin 3, j ≠ k →
      capAt t j * capAt g k + capAt g j * capAt t k < p := by
  intro j k hne
  fin_cases j <;> fin_cases k
  all_goals try exact (hne rfl).elim
  all_goals first
    | simpa [capAt, mixed, unitY, Nat.mul_comm, Nat.add_comm] using hY
    | simpa [capAt, mixed, unitR, Nat.mul_comm, Nat.add_comm] using hR
    | simpa [capAt, mixed, unitZ, Nat.mul_comm, Nat.add_comm] using hZ

theorem actual_characteristic_gates (p : ℕ)
    (hG : HasCaps G g) (hT : HasCaps T t)
    (hg : ∀ j, capAt g j < p)
    (hY : mixed g t unitY < p) (hR : mixed g t unitR < p) (hZ : mixed g t unitZ < p) :
    (∀ j, G.degreeOf j < p) ∧
      ∀ j k : Fin 3, j ≠ k →
        T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < p := by
  refine ⟨fun j ↦ (hG j).trans_lt (hg j), ?_⟩
  intro j k hjk
  exact (actual_pair_degree_le G T g t hG hT j k).trans_lt
    (pair_caps_below_of_mixed g t p hY hR hZ j k hjk)

end MixedGates

end

end ProximityPrize.SubmissionLower.ContactCountingCaps
