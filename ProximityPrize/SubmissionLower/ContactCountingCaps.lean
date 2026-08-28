import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
import ProximityPrize.SubmissionLower.ContactProjectionParameters
import ProximityPrize.SubmissionLower.ContactImplicitLiftParameters
import ProximityPrize.SubmissionLower.ContactRefinedAgreementY

/-!
# Actual first-tail and agreement caps for the fixed counting witness

Model label: gpt-5.

The concrete recurrence and agreement-polynomial degree theorems are
transported through the actual generic-surface map. Generic monotonicity
then turns coordinate caps into the original pairwise mixed-degree gates
needed by the actual projection pipeline. The already checked normal and
implicit fixed-witness certificates supply the strict characteristic gates.

The selected first-tail vanishing theorem uses the actual polynomial
solution identity and its degree bound only. No all-tail or generic
polynomiality hypothesis is assumed.
-/

namespace ProximityPrize.SubmissionLower.ContactCountingCaps

open scoped Classical
open ContactAlignmentParameters ContactTaylorNumerators ContactGenericSurface
open ContactPolynomialSolutions ContactPrimeSeedIncidence
open ContactRefinedAgreementY

noncomputable section

def capAt (v : DegreeVector) : Fin 3 → ℕ := ![v.y, v.r, v.z]

def numeratorCaps (ell s L b : ℕ) : DegreeVector :=
  ⟨1 + 2 * b * ell, b * (2 * s - 1), 2 * b * L⟩

def agreementCaps (ell s L w : ℕ) : DegreeVector :=
  ⟨1 + 2 * w * ell, w * (2 * s - 1), 2 * w * L + 1⟩

variable {K Ω : Type} [Field K] [Field Ω]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω

def HasCaps (Q : MvPolynomial (Fin 3) Ω) (v : DegreeVector) : Prop :=
  ∀ i, Q.degreeOf i ≤ capAt v i

variable (φ : Polynomial K →+* Ω)

def firstTailSurface (F : MvPolynomial (Fin 4) K) (w : ℕ) : MvPolynomial (Fin 3) Ω :=
  surfaceMap φ (numerator K F (w + 1))

/-- Separated bounds for the actual surface image of every recurrence
numerator, including zero and derivative-zero boundary cases. -/
theorem surface_numerator_caps
    (F : MvPolynomial (Fin 4) K) (ell s L : ℕ) (hs : 1 ≤ s)
    (hY : F.degreeOf 1 ≤ ell) (hR : F.degreeOf 2 ≤ s) (hZ : F.degreeOf 3 ≤ L)
    (b : ℕ) : HasCaps (surfaceMap φ (numerator K F b)) (numeratorCaps ell s L b) := by
  obtain ⟨hy, hr, hz⟩ := numerator_degree_bounds F ell s L hs hY hR hZ b
  intro i
  fin_cases i
  · exact (surfaceMap_degreeOf_le φ _ 0).trans hy
  · exact (surfaceMap_degreeOf_le φ _ 1).trans hr
  · exact (surfaceMap_degreeOf_le φ _ 2).trans hz

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

/-- The exact first-tail vector in the frozen arithmetic ledger bounds
the actual first-tail surface polynomial. -/
theorem fixed_firstTail_caps (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ yCap) (hR : F.degreeOf 2 ≤ slopeCap)
    (hZ : F.degreeOf 3 ≤ seedTotalCap) :
    HasCaps (firstTailSurface φ F w) firstTail := by
  exact surface_numerator_caps φ F yCap slopeCap seedTotalCap (by decide)
    hY hR hZ (w + 1)

/-- Uniform actual agreement caps at every original evaluation node;
the scalars may vary arbitrarily and need no nonvanishing assumption. -/
theorem fixed_agreement_caps (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ yCap) (hR : F.degreeOf 2 ≤ slopeCap)
    (hZ : F.degreeOf 3 ≤ seedTotalCap)
    (hHY : (polyH K F).degreeOf (1 : Fin 4) ≤ yCap - 1)
    (x u₀ u₁ : K) :
    HasCaps (agreementPolynomial φ F w x u₀ u₁) agreementVector := by
  have hold := surface_agreement_caps φ F yCap slopeCap seedTotalCap (by decide)
    hY hR hZ w (fun j ↦ (j.factorial : K)⁻¹) x u₀ u₁
  intro i
  fin_cases i
  · exact (surfaceMap_degreeOf_le φ _ 0).trans
      (agreementNumerator_Y_degree_bound_of_polyH F yCap (yCap - 1) w
        hY hHY (by omega) (fun j ↦ (j.factorial : K)⁻¹) x u₀ u₁)
  · exact hold 1
  · exact hold 2

/-- A genuine degree-w selected solution vanishes on the actual first
tail. This needs neither regularity nor a characteristic bound. -/
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

theorem fixed_implicit_agreement_caps (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ ContactImplicitLiftParameters.implicitYCap)
    (hR : F.degreeOf 2 ≤ 1) (hZ : F.degreeOf 3 ≤ algebraicCap)
    (x u₀ u₁ : K) :
    HasCaps (agreementPolynomial φ F w x u₀ u₁)
      ContactImplicitLiftParameters.liftedAgreement := by
  have h := surface_agreement_caps φ F ContactImplicitLiftParameters.implicitYCap 1
    algebraicCap (by decide) hY hR hZ w (fun j ↦ (j.factorial : K)⁻¹) x u₀ u₁
  simpa [agreementPolynomial, agreementCaps, ContactImplicitLiftParameters.liftedAgreement] using h

section MixedGates

variable (G T : MvPolynomial (Fin 3) Ω) (g t : DegreeVector)

/-- Monotonicity applies to the actual original polynomial degrees,
before any rational projection or resultant is introduced. -/
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

/-- Generic original-degree characteristic gates from proved box caps. -/
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

/-- Each coordinate cap of the frozen normal surface is strictly below
the actual characteristic; this is exact closed arithmetic. -/
theorem fixed_surface_caps_below_characteristic :
    ∀ j, capAt ContactProjectionParameters.surfaceVector j < prime := by
  intro j
  fin_cases j <;>
    norm_num [capAt, ContactProjectionParameters.surfaceVector, yCap, weightedCap,
      ContactAlignmentParameters.multiplicity, agreements, w, slopeCap, seedTotalCap, prime]

theorem fixed_agreement_characteristic_gates (G T : MvPolynomial (Fin 3) Ω)
    (hG : HasCaps G ContactProjectionParameters.surfaceVector) (hT : HasCaps T agreementVector)
    (hRgate : mixed ContactProjectionParameters.surfaceVector agreementVector unitR < prime) :
    (∀ j, G.degreeOf j < prime) ∧
      ∀ j k : Fin 3, j ≠ k →
        T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < prime := by
  rcases ContactProjectionParameters.projection_caps_below_characteristic with
    ⟨_, _, hY, hZ, _⟩
  exact actual_characteristic_gates G T _ _ prime hG hT
    fixed_surface_caps_below_characteristic hY hRgate hZ

theorem fixed_implicit_surface_caps_below_characteristic :
    ∀ j, capAt ContactImplicitLiftParameters.liftedSurface j < prime := by
  intro j
  fin_cases j <;>
    norm_num [capAt, ContactImplicitLiftParameters.liftedSurface,
      ContactImplicitLiftParameters.implicitYCap, ContactImplicitLiftParameters.implicitWeightedCap,
      algebraicCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements,
      w, slopeCap, seedTotalCap, prime]

/-- The implicit-equation lift uses its original fixed implicit cut,
not a presumed separability of an arbitrary test-function map. -/
theorem fixed_implicit_characteristic_gates (G T : MvPolynomial (Fin 3) Ω)
    (hG : HasCaps G ContactImplicitLiftParameters.liftedSurface)
    (hT : HasCaps T ContactImplicitLiftParameters.implicitCut) :
    (∀ j, G.degreeOf j < prime) ∧
      ∀ j k : Fin 3, j ≠ k →
        T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < prime := by
  rcases ContactImplicitLiftParameters.lifted_projection_characteristic_gates with
    ⟨_, hY, hR, hZ⟩
  exact actual_characteristic_gates G T _ _ prime hG hT
    fixed_implicit_surface_caps_below_characteristic hY hR hZ

end

end ProximityPrize.SubmissionLower.ContactCountingCaps

#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.surface_numerator_caps
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.surface_agreement_caps
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.fixed_firstTail_caps
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.fixed_agreement_caps
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.selected_firstTail_zero
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.fixed_implicit_agreement_caps
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.actual_pair_degree_le
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.pair_caps_below_of_mixed
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.actual_characteristic_gates
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.fixed_agreement_characteristic_gates
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps.fixed_implicit_characteristic_gates
