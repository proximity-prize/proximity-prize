import ProximityPrize.SubmissionLower.BCHKSInterpolationShell6400

/-!
# Error-locator form of the score-64 shell residual

If `A` is a selected agreement set, its complement has at most `76780`
coordinates.  Multiplying the accepted-interpolant factorization by the
powered complement locator replaces the moving, very large agreement
locator by the fixed full-domain locator:

`E_A^3733 * Q(X,z,P) = V^3733 * Cof`.

On the genuinely new shell the complement has between `76771` and `76780`
coordinates, while the nonzero cofactor has the sharper defect-sensitive
degree bound

`deg Cof < 3733 * (185374 - #A)`.
-/

open scoped BigOperators Classical

noncomputable section

namespace ProximityPrize.SubmissionLower.BCHKSErrorLocatorKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSConcreteGS6399
open BCHKSSubstitutionVanish
open BCHKSInterpolationShell6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 500000

universe u v

/-- Coordinates outside a selected agreement set. -/
def selectedErrorSet {I : Type u} [Fintype I] [DecidableEq I]
    (A : Finset I) : Finset I :=
  Finset.univ \ A

/-- Nodal locator of the coordinates outside a selected agreement set. -/
noncomputable def selectedErrorLocator
    {F : Type u} [Field F] {I : Type v}
    [Fintype I] [DecidableEq I]
    (omega : I ↪ F) (A : Finset I) : F[X] :=
  Lagrange.nodal (selectedErrorSet A) fun i ↦ omega i

/-- Fixed nodal polynomial of the entire evaluation domain. -/
noncomputable def fullDomainLocator
    {F : Type u} [Field F] {I : Type v}
    [Fintype I] [DecidableEq I]
    (omega : I ↪ F) : F[X] :=
  Lagrange.nodal Finset.univ fun i ↦ omega i

@[simp]
theorem selectedErrorSet_card
    {I : Type u} [Fintype I] [DecidableEq I]
    (A : Finset I) :
    (selectedErrorSet A).card = Fintype.card I - A.card := by
  simp only [selectedErrorSet, Finset.card_sdiff, Finset.card_univ,
    Finset.inter_univ]

@[simp]
theorem selectedErrorLocator_natDegree
    {F : Type u} [Field F] {I : Type v}
    [Fintype I] [DecidableEq I]
    (omega : I ↪ F) (A : Finset I) :
    (selectedErrorLocator omega A).natDegree =
      Fintype.card I - A.card := by
  simp only [selectedErrorLocator, Lagrange.natDegree_nodal,
    selectedErrorSet_card]

@[simp]
theorem fullDomainLocator_natDegree
    {F : Type u} [Field F] {I : Type v}
    [Fintype I] [DecidableEq I]
    (omega : I ↪ F) :
    (fullDomainLocator omega).natDegree = Fintype.card I := by
  simp only [fullDomainLocator, Lagrange.natDegree_nodal,
    Finset.card_univ]

/-- The selected error and agreement locators partition the full-domain
locator exactly. -/
theorem selectedErrorLocator_mul_agreementLocator
    {F : Type u} [Field F] {I : Type v}
    [Fintype I] [DecidableEq I]
    (omega : I ↪ F) (A : Finset I) :
    selectedErrorLocator omega A *
        Lagrange.nodal A (fun i ↦ omega i) =
      fullDomainLocator omega := by
  simp only [selectedErrorLocator, selectedErrorSet, fullDomainLocator,
    Lagrange.nodal]
  exact Finset.prod_sdiff (Finset.subset_univ A)

/-- Turn an agreement-locator residual factorization into the fixed-domain
key equation. -/
theorem errorLocator_keyEquation_of_residual
    {F : Type u} [Field F] {I : Type v}
    [Fintype I] [DecidableEq I]
    (omega : I ↪ F) (A : Finset I) (m : ℕ) (R Cof : F[X])
    (hfactor : agreementMultiplicityLocator omega A m * Cof = R) :
    selectedErrorLocator omega A ^ m * R =
      fullDomainLocator omega ^ m * Cof := by
  rw [← hfactor]
  simp only [agreementMultiplicityLocator]
  calc
    selectedErrorLocator omega A ^ m *
          (Lagrange.nodal A (fun i ↦ omega i) ^ m * Cof) =
        (selectedErrorLocator omega A ^ m *
            Lagrange.nodal A (fun i ↦ omega i) ^ m) * Cof := by
          rw [mul_assoc]
    _ = (selectedErrorLocator omega A *
          Lagrange.nodal A (fun i ↦ omega i)) ^ m * Cof := by
          rw [mul_pow]
    _ = fullDomainLocator omega ^ m * Cof := by
          rw [selectedErrorLocator_mul_agreementLocator]

/-- Exact complement-size range on a genuinely new score-64 shell witness. -/
theorem score6400_selectedErrorSet_card_bounds
    (A : Finset IRSProfile.Index)
    (hlower : 185364 ≤ A.card) (hupper : A.card < 185374) :
    76771 ≤ (selectedErrorSet A).card ∧
      (selectedErrorSet A).card ≤ 76780 := by
  rw [selectedErrorSet_card]
  norm_num [IRSProfile.Index]
  omega

/-- Exact arithmetic converting the accepted weighted-degree cap and the
factorization degree identity into the shell-defect bound. -/
theorem cofactor_degree_lt_shell_defect
    (a c r : ℕ) (hexact : 3733 * a + c = r)
    (hr : r < 692001142) :
    c < 3733 * (185374 - a) := by
  omega

/-- The accepted interpolant supplies a defect-sensitive key equation for
one new-shell witness.  The zero specialization is retained separately;
otherwise the cofactor degree scales with the exact ten-level shell defect. -/
theorem exists_score6400_shell_keyEquation
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (z : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
    (A : Finset IRSProfile.Index)
    (U₀ U₁ : IRSProfile.Index → IRSProfile.Field)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < 3733 →
      ((((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (U₀ i) + Polynomial.X * Polynomial.C (U₁ i))).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (IRSProfile.domain i) P = U₀ i + z * U₁ i)
    (hPdegree : P.natDegree ≤ 131071)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 692001142)
    (hAcardLower : 185364 ≤ A.card)
    (hAcardUpper : A.card < 185374) :
    ∃ Cof : Polynomial IRSProfile.Field,
      selectedErrorLocator IRSProfile.domain A ^ 3733 * triEval Q z P =
          fullDomainLocator IRSProfile.domain ^ 3733 * Cof ∧
      76771 ≤ (selectedErrorSet A).card ∧
      (selectedErrorSet A).card ≤ 76780 ∧
      (triEval Q z P = 0 ∨
        (Cof ≠ 0 ∧
          Cof.natDegree < 3733 * (185374 - A.card))) := by
  have herrors := score6400_selectedErrorSet_card_bounds
    A hAcardLower hAcardUpper
  obtain ⟨Cof, hfactor, hresidual⟩ :=
    exists_score6400_shell_residual Q z P A U₀ U₁
      hvan hmatch hPdegree hcap hAcardLower
  refine ⟨Cof,
    errorLocator_keyEquation_of_residual
      IRSProfile.domain A 3733 (triEval Q z P) Cof hfactor,
    herrors.1, herrors.2, ?_⟩
  rcases hresidual with hzero | ⟨hCof, _hcoarse, hexact⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨hCof, ?_⟩
    apply cofactor_degree_lt_shell_defect
      A.card Cof.natDegree (triEval Q z P).natDegree hexact
    have hRdegree : (triEval Q z P).natDegree ≤ 692001141 := by
      apply triEval_natDegree_le_of_weighted_X_cap Q z P 131071 692001141
      · exact hPdegree
      · intro j a hja
        have hja' := hcap j a hja
        omega
    exact Nat.lt_succ_iff.mpr hRdegree

end ProximityPrize.SubmissionLower.BCHKSErrorLocatorKeyEquation6400
