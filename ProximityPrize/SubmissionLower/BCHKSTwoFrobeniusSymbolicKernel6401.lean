import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRankTwoSpecialization6401

/-!
# The balanced symbolic two-Frobenius kernel at score 64.01

This is the common, moving-challenge interpolation kernel.  Its coefficients
are in the challenge field and its entries are polynomials in `F[Z][X]`.
The three coefficient boxes have `Z` depths `L`, `L-1`, and `L-q`, so the
three-term semilinear received relation always has `Z` degree below `L`.

There are exactly three more variables than equations.  We therefore select
three linearly independent coefficient vectors and map them injectively to
three symbolic rows.  This is the denominator-free input to the determinant,
rank-two, and rank-one fork; no generic-rank assertion is made.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusSymbolicKernel6401

open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

def symbolicDepth6401 : ℕ := 31031608504777
def symbolicDepthOne6401 : ℕ := 31031608504776
def symbolicDepthFrobenius6401 : ℕ := 31029477798344

abbrev Box0 := Fin a0XSlots6401 × Fin symbolicDepth6401
abbrev Box1 := Fin a1XSlots6401 × Fin symbolicDepthOne6401
abbrev Box2 := Fin a2XSlots6401 × Fin symbolicDepthFrobenius6401

/-- The three rectangular coefficient arrays. -/
abbrev SymbolicCoefficients (F : Type*) [Field F] :=
  (Box0 → F) × (Box1 → F) × (Box2 → F)

/-- Turn a rectangular coefficient array into a polynomial in `F[Z][X]`.
The first index is the outer `X` exponent and the second the coefficient
`Z` exponent. -/
noncomputable def boxPolynomialMap {F : Type*} [Field F]
    (xDepth zDepth : ℕ) :
    (Fin xDepth × Fin zDepth → F) →ₗ[F] XOverZ F :=
  Finsupp.linearCombination F (fun q : Fin xDepth × Fin zDepth =>
    Polynomial.monomial (q.1 : ℕ)
      (Polynomial.monomial (q.2 : ℕ) 1)) ∘ₗ
    (Finsupp.linearEquivFunOnFinite F F
      (Fin xDepth × Fin zDepth)).symm.toLinearMap

open scoped BigOperators in
theorem boxPolynomialMap_eq_sum {F : Type*} [Field F]
    (xDepth zDepth : ℕ) (c : Fin xDepth × Fin zDepth → F) :
    boxPolynomialMap xDepth zDepth c =
      ∑ q : Fin xDepth × Fin zDepth, c q •
        Polynomial.monomial (q.1 : ℕ)
          (Polynomial.monomial (q.2 : ℕ) 1) := by
  unfold boxPolynomialMap
  rw [Finsupp.linearCombination_eq_fintype_linearCombination,
    Fintype.linearCombination_apply]

open scoped BigOperators in
theorem boxPolynomialMap_coeff_index {F : Type*} [Field F]
    (xDepth zDepth : ℕ) (c : Fin xDepth × Fin zDepth → F)
    (q : Fin xDepth × Fin zDepth) :
    ((boxPolynomialMap xDepth zDepth c).coeff (q.1 : ℕ)).coeff
        (q.2 : ℕ) = c q := by
  classical
  rw [boxPolynomialMap_eq_sum, Polynomial.finsetSum_coeff,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single q]
  · simp [Polynomial.coeff_smul, Polynomial.coeff_monomial]
  · intro r _hr hrq
    by_cases hx : (r.1 : ℕ) = (q.1 : ℕ)
    · have hz : (r.2 : ℕ) ≠ (q.2 : ℕ) := by
        intro hz
        apply hrq
        exact Prod.ext (Fin.ext hx) (Fin.ext hz)
      simp [Polynomial.coeff_smul, Polynomial.coeff_monomial, hx, hz]
    · simp [Polynomial.coeff_smul, Polynomial.coeff_monomial, hx]
  · simp

theorem boxPolynomialMap_injective {F : Type*} [Field F]
    (xDepth zDepth : ℕ) :
    Function.Injective (boxPolynomialMap (F := F) xDepth zDepth) := by
  intro c d hcd
  funext q
  have h := congrArg
    (fun P : XOverZ F => (P.coeff (q.1 : ℕ)).coeff (q.2 : ℕ)) hcd
  simpa [boxPolynomialMap_coeff_index] using h

/-- Map the three coefficient boxes to a symbolic row. -/
noncomputable def coefficientRowMap {F : Type*} [Field F] :
    SymbolicCoefficients F →ₗ[F] SymbolicRow F where
  toFun c := ![
    boxPolynomialMap a0XSlots6401 symbolicDepth6401 c.1,
    boxPolynomialMap a1XSlots6401 symbolicDepthOne6401 c.2.1,
    boxPolynomialMap a2XSlots6401 symbolicDepthFrobenius6401 c.2.2]
  map_add' c d := by
    funext j
    fin_cases j <;> simp
  map_smul' a c := by
    funext j
    fin_cases j <;> simp

theorem coefficientRowMap_injective {F : Type*} [Field F] :
    Function.Injective (coefficientRowMap (F := F)) := by
  intro c d hcd
  apply Prod.ext
  · apply boxPolynomialMap_injective a0XSlots6401 symbolicDepth6401
    have := congrFun hcd (0 : Fin 3)
    simpa [coefficientRowMap] using this
  · apply Prod.ext
    · apply boxPolynomialMap_injective a1XSlots6401
          symbolicDepthOne6401
      have := congrFun hcd (1 : Fin 3)
      simpa [coefficientRowMap] using this
    · apply boxPolynomialMap_injective a2XSlots6401
          symbolicDepthFrobenius6401
      have := congrFun hcd (2 : Fin 3)
      simpa [coefficientRowMap] using this

/-- The affine received polynomial in the moving challenge. -/
noncomputable def receivedZ {F : Type*} [Field F]
    (u₀ u₁ : F) : Polynomial F :=
  Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁

/-- Its coefficient-Frobenius image, using `sigma(z)=z^q`. -/
noncomputable def receivedFrobeniusZ {F : Type*} [Field F]
    (sigma : F →+* F) (u₀ u₁ : F) : Polynomial F :=
  Polynomial.C (sigma u₀) +
    Polynomial.monomial q6401 (sigma u₁)

/-- Evaluate one symbolic row at a locator and insert the two received
polynomials. -/
noncomputable def symbolicCoordinateRelation {F : Type*} [Field F]
    (sigma : F →+* F) (x u₀ u₁ : F) (q : SymbolicRow F) :
    Polynomial F :=
  evalOuterAt x (q 0) +
    evalOuterAt x (q 1) * receivedZ u₀ u₁ +
    evalOuterAt x (q 2) * receivedFrobeniusZ sigma u₀ u₁

noncomputable def symbolicCoordinateRelationMap
    {F : Type*} [Field F] (sigma : F →+* F) (x u₀ u₁ : F) :
    SymbolicRow F →ₗ[F] Polynomial F where
  toFun q := symbolicCoordinateRelation sigma x u₀ u₁ q
  map_add' q r := by
    simp [symbolicCoordinateRelation, evalOuterAt]
    ring
  map_smul' a q := by
    simp [symbolicCoordinateRelation, evalOuterAt]

@[simp] theorem symbolicCoordinateRelationMap_apply
    {F : Type*} [Field F] (sigma : F →+* F) (x u₀ u₁ : F)
    (q : SymbolicRow F) :
    symbolicCoordinateRelationMap sigma x u₀ u₁ q =
      symbolicCoordinateRelation sigma x u₀ u₁ q := rfl

/-- The balanced coefficient constraints: every coefficient below depth
`L` of every coordinate relation vanishes. -/
noncomputable def symbolicConstraintMap {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u₀ u₁ : Fin n6401 → F) :
    SymbolicCoefficients F →ₗ[F]
      (Fin n6401 × Fin symbolicDepth6401 → F) :=
  LinearMap.pi fun id =>
    (Polynomial.lcoeff F (id.2 : ℕ)).comp <|
      (symbolicCoordinateRelationMap sigma (alpha id.1)
        (u₀ id.1) (u₁ id.1)).comp coefficientRowMap

noncomputable abbrev SymbolicKernel {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u₀ u₁ : Fin n6401 → F) :=
  LinearMap.ker (symbolicConstraintMap sigma alpha u₀ u₁)

theorem symbolicCoefficients_finrank {F : Type*} [Field F] :
    Module.finrank F (SymbolicCoefficients F) =
      8134749979876261891 := by
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin]
  norm_num [a0XSlots6401, a1XSlots6401, a2XSlots6401,
    symbolicDepth6401, symbolicDepthOne6401,
    symbolicDepthFrobenius6401]

theorem symbolicConstraintTarget_finrank {F : Type*} [Field F] :
    Module.finrank F
        (Fin n6401 × Fin symbolicDepth6401 → F) =
      8134749979876261888 := by
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
    Fintype.card_fin]
  norm_num [n6401, symbolicDepth6401]

/-- The balanced symbolic kernel has dimension at least three. -/
theorem symbolicKernel_finrank_ge_three
    {F : Type*} [Field F] (sigma : F →+* F)
    (alpha : Fin n6401 → F) (u₀ u₁ : Fin n6401 → F) :
    3 ≤ Module.finrank F (SymbolicKernel sigma alpha u₀ u₁) := by
  change 3 ≤ Module.finrank F
    (LinearMap.ker (symbolicConstraintMap sigma alpha u₀ u₁))
  have hrange : Module.finrank F
      (LinearMap.range (symbolicConstraintMap sigma alpha u₀ u₁)) ≤
      8134749979876261888 := by
    calc
      _ ≤ Module.finrank F
          (Fin n6401 × Fin symbolicDepth6401 → F) :=
        Submodule.finrank_le _
      _ = _ := symbolicConstraintTarget_finrank
  have hranknull := LinearMap.finrank_range_add_finrank_ker
    (symbolicConstraintMap sigma alpha u₀ u₁)
  rw [symbolicCoefficients_finrank] at hranknull
  omega

/-- Three linearly independent balanced coefficient vectors exist. -/
theorem exists_three_independent_symbolicKernel_coefficients
    {F : Type*} [Field F] (sigma : F →+* F)
    (alpha : Fin n6401 → F) (u₀ u₁ : Fin n6401 → F) :
    ∃ c : Fin 3 → SymbolicKernel sigma alpha u₀ u₁,
      LinearIndependent F c :=
  exists_linearIndependent_of_le_finrank
    (symbolicKernel_finrank_ge_three sigma alpha u₀ u₁)

end BCHKSTwoFrobeniusSymbolicKernel6401
end ProximityPrize.SubmissionLower
