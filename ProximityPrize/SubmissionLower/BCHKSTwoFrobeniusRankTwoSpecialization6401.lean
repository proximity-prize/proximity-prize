import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRank6401
import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401

/-!
# Polynomial specialization for the two-Frobenius rank-two branch

Rows in this file have coefficients in `F[Z]` and outer variable `X`.
Consequently specialization at a challenge value is an ordinary polynomial
ring homomorphism; no evaluation of a rational function at a possible pole
is used.  A nonzero `(A₁,A₂)` minor gives a unique owner after every
specialization where that minor remains a nonzero polynomial in `X`.

For each coordinate, the owner-agreement condition is then a root of one
explicit polynomial in `Z`.  The zero-polynomial coordinates are retained as
the separate identity branch; all other coordinates are ready for the
finite root-incidence charge.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusRankTwoSpecialization6401

open Polynomial
open BCHKSTwoFrobeniusRank6401

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- Bivariate polynomials with outer variable `X` and coefficient variable
`Z`. -/
abbrev XOverZ (F : Type*) [Field F] := Polynomial (Polynomial F)

/-- Specialize the coefficient variable `Z`, retaining the outer `X`. -/
noncomputable def specializeCoeffZ {F : Type*} [Field F] (z : F) :
    XOverZ F →+* Polynomial F :=
  Polynomial.mapRingHom (Polynomial.evalRingHom z)

@[simp] theorem specializeCoeffZ_apply {F : Type*} [Field F]
    (z : F) (P : XOverZ F) :
    specializeCoeffZ z P = P.map (Polynomial.evalRingHom z) := rfl

/-- A symbolic three-component interpolation row. -/
abbrev SymbolicRow (F : Type*) [Field F] := Fin 3 → XOverZ F

noncomputable def symbolicRelation {F : Type*} [Field F] (sigma : F →+* F)
    (q : Fin 3 → Polynomial F) (P : Polynomial F) : Polynomial F :=
  q 0 + q 1 * P + q 2 * P.map sigma

noncomputable def specializeRow {F : Type*} [Field F] (z : F)
    (q : SymbolicRow F) : Fin 3 → Polynomial F :=
  fun j => specializeCoeffZ z (q j)

noncomputable def symbolicMinor01 {F : Type*} [Field F]
    (q r : SymbolicRow F) : XOverZ F :=
  q 0 * r 1 - r 0 * q 1

noncomputable def symbolicRankTwoNumerator {F : Type*} [Field F]
    (q r : SymbolicRow F) : XOverZ F :=
  q 0 * r 2 - r 0 * q 2

noncomputable def symbolicRankTwoDenominator {F : Type*} [Field F]
    (q r : SymbolicRow F) : XOverZ F :=
  q 1 * r 2 - r 1 * q 2

theorem specialize_symbolicRankTwoNumerator {F : Type*} [Field F]
    (z : F) (q r : SymbolicRow F) :
    specializeCoeffZ z (symbolicRankTwoNumerator q r) =
      (specializeRow z q 0) * (specializeRow z r 2) -
        (specializeRow z r 0) * (specializeRow z q 2) := by
  simp [symbolicRankTwoNumerator, specializeRow]

theorem specialize_symbolicRankTwoDenominator {F : Type*} [Field F]
    (z : F) (q r : SymbolicRow F) :
    specializeCoeffZ z (symbolicRankTwoDenominator q r) =
      (specializeRow z q 1) * (specializeRow z r 2) -
        (specializeRow z r 1) * (specializeRow z q 2) := by
  simp [symbolicRankTwoDenominator, specializeRow]

/-- Pointwise rank-two elimination after polynomial specialization. -/
theorem specialized_rankTwo_owner_identity
    {F : Type*} [Field F] (sigma : F →+* F)
    (z : F) (q r : SymbolicRow F) (P : Polynomial F)
    (hq : symbolicRelation sigma (specializeRow z q) P = 0)
    (hr : symbolicRelation sigma (specializeRow z r) P = 0) :
    specializeCoeffZ z (symbolicRankTwoDenominator q r) * P =
      -specializeCoeffZ z (symbolicRankTwoNumerator q r) := by
  rw [specialize_symbolicRankTwoDenominator,
    specialize_symbolicRankTwoNumerator]
  unfold symbolicRelation at hq hr
  linear_combination
    (specializeRow z r 2) * hq - (specializeRow z q 2) * hr

/-- A nonzero specialized denominator makes the polynomial owner unique. -/
theorem specialized_rankTwo_owner_unique
    {F : Type*} [Field F] (z : F) (q r : SymbolicRow F)
    (P Q : Polynomial F)
    (hden : specializeCoeffZ z (symbolicRankTwoDenominator q r) ≠ 0)
    (hP : specializeCoeffZ z (symbolicRankTwoDenominator q r) * P =
      -specializeCoeffZ z (symbolicRankTwoNumerator q r))
    (hQ : specializeCoeffZ z (symbolicRankTwoDenominator q r) * Q =
      -specializeCoeffZ z (symbolicRankTwoNumerator q r)) :
    P = Q := by
  apply mul_left_cancel₀ hden
  exact hP.trans hQ.symm

/-- The affine received value at one coordinate, as a polynomial in `Z`. -/
noncomputable def affineValuePolynomial {F : Type*} [Field F]
    (u₀ u₁ : F) : Polynomial F :=
  Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁

/-- Evaluate the outer `X` variable at a constant locator, leaving a
polynomial in `Z`. -/
noncomputable def evalOuterAt {F : Type*} [Field F]
    (x : F) (P : XOverZ F) : Polynomial F :=
  P.eval (Polynomial.C x)

/-- The challenge polynomial whose roots are precisely the rank-two branch
agreements at one coordinate. -/
noncomputable def coordinateMismatch {F : Type*} [Field F]
    (q r : SymbolicRow F) (x u₀ u₁ : F) : Polynomial F :=
  evalOuterAt x (symbolicRankTwoDenominator q r) *
      affineValuePolynomial u₀ u₁ +
    evalOuterAt x (symbolicRankTwoNumerator q r)

theorem eval_specializeCoeffZ_comm {F : Type*} [Field F]
    (z x : F) (P : XOverZ F) :
    Polynomial.eval x (specializeCoeffZ z P) =
      Polynomial.eval z (evalOuterAt x P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      unfold specializeCoeffZ evalOuterAt at hP hQ ⊢
      simp only [map_add, Polynomial.eval_add]
      rw [hP, hQ]
  | monomial n a =>
      simp [specializeCoeffZ, evalOuterAt]

theorem coordinateMismatch_eval {F : Type*} [Field F]
    (z : F) (q r : SymbolicRow F) (x u₀ u₁ : F) :
    Polynomial.eval z (coordinateMismatch q r x u₀ u₁) =
      Polynomial.eval x
          (specializeCoeffZ z (symbolicRankTwoDenominator q r)) *
        (u₀ + z * u₁) +
      Polynomial.eval x
          (specializeCoeffZ z (symbolicRankTwoNumerator q r)) := by
  unfold coordinateMismatch affineValuePolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [← eval_specializeCoeffZ_comm z x
      (symbolicRankTwoDenominator q r),
    ← eval_specializeCoeffZ_comm z x
      (symbolicRankTwoNumerator q r)]

/-- Every owner agreement is a root of its coordinate mismatch polynomial.
This is the exact pointwise bridge used by the later incidence count. -/
theorem coordinateMismatch_eval_eq_zero_of_owner
    {F : Type*} [Field F] (sigma : F →+* F)
    (z : F) (q r : SymbolicRow F) (x u₀ u₁ : F)
    (P : Polynomial F)
    (hq : symbolicRelation sigma (specializeRow z q) P = 0)
    (hr : symbolicRelation sigma (specializeRow z r) P = 0)
    (howner : Polynomial.eval x P = u₀ + z * u₁) :
    Polynomial.eval z (coordinateMismatch q r x u₀ u₁) = 0 := by
  have hid := specialized_rankTwo_owner_identity sigma z q r P hq hr
  have heval := congrArg (Polynomial.eval x) hid
  simp only [Polynomial.eval_mul, Polynomial.eval_neg] at heval
  rw [coordinateMismatch_eval, ← howner]
  linear_combination heval

/-- The identity coordinates are deliberately kept separate from the
nonzero mismatch polynomials charged by root counting. -/
noncomputable def identityCoordinates
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (x u₀ u₁ : ι → F) (I : Finset ι) : Finset ι := by
  classical
  exact I.filter fun i => coordinateMismatch q r (x i) (u₀ i) (u₁ i) = 0

/-! ## The symbolic rank fork -/

/-- Put three symbolic rows into one polynomial matrix. -/
noncomputable def symbolicRowMatrix {F : Type*} [Field F]
    (q : Fin 3 → SymbolicRow F) : Matrix (Fin 3) (Fin 3) (XOverZ F) :=
  fun i j => q i j

/-- The moving-challenge determinant.  It lives in `F[Z][X]`; a nonzero
coefficient in `X` is therefore an ordinary polynomial obstruction in `Z`.
-/
noncomputable def symbolicDeterminant {F : Type*} [Field F]
    (q : Fin 3 → SymbolicRow F) : XOverZ F :=
  (symbolicRowMatrix q).det

noncomputable def specializedSymbolicMatrix {F : Type*} [Field F]
    (z : F) (q : Fin 3 → SymbolicRow F) :
    Matrix (Fin 3) (Fin 3) (Polynomial F) :=
  fun i j => specializeRow z (q i) j

theorem specialize_symbolicDeterminant {F : Type*} [Field F]
    (z : F) (q : Fin 3 → SymbolicRow F) :
    specializeCoeffZ z (symbolicDeterminant q) =
      (specializedSymbolicMatrix z q).det := by
  rw [symbolicDeterminant, (specializeCoeffZ z).map_det]
  congr 1

/-- The owner kernel vector after specialization. -/
noncomputable def specializedOwnerVector {F : Type*} [Field F]
    (sigma : F →+* F) (P : Polynomial F) : Fin 3 → Polynomial F :=
  ![1, P, P.map sigma]

theorem specializedRowMatrix_mulVec_owner_apply
    {F : Type*} [Field F] (sigma : F →+* F) (z : F)
    (q : Fin 3 → SymbolicRow F) (P : Polynomial F) (i : Fin 3) :
    ((specializedSymbolicMatrix z q).mulVec
        (specializedOwnerVector sigma P)) i =
      symbolicRelation sigma (specializeRow z (q i)) P := by
  simp [specializedSymbolicMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, specializedOwnerVector, symbolicRelation]

/-- If all three specialized rows annihilate an owner, the specialized
symbolic determinant vanishes. -/
theorem specialize_symbolicDeterminant_eq_zero_of_owner
    {F : Type*} [Field F] (sigma : F →+* F) (z : F)
    (q : Fin 3 → SymbolicRow F) (P : Polynomial F)
    (hrel : ∀ i, symbolicRelation sigma (specializeRow z (q i)) P = 0) :
    specializeCoeffZ z (symbolicDeterminant q) = 0 := by
  rw [specialize_symbolicDeterminant]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
      (i := (0 : Fin 3))
  · funext i
    rw [specializedRowMatrix_mulVec_owner_apply]
    exact hrel i
  · exact mem_nonZeroDivisors_of_ne_zero (by
      simp [specializedOwnerVector])

/-- A pair has symbolic rank two when one exterior coordinate is nonzero.
This is the denominator-free analogue of `RowPairIndependent`. -/
def SymbolicRowPairIndependent {F : Type*} [Field F]
    (q r : SymbolicRow F) : Prop :=
  symbolicMinor01 q r ≠ 0 ∨
    symbolicRankTwoNumerator q r ≠ 0 ∨
      symbolicRankTwoDenominator q r ≠ 0

/-- The exact rank-one residual for three selected symbolic rows. -/
def SymbolicRankOneBranch {F : Type*} [Field F]
    (q : Fin 3 → SymbolicRow F) : Prop :=
  ∀ i j, ¬ SymbolicRowPairIndependent (q i) (q j)

/-- Exhaustive symbolic determinant/rank-two/rank-one fork.  No generic-rank
claim is hidden here. -/
theorem symbolic_rankThree_or_rankTwo_or_rankOne
    {F : Type*} [Field F] (q : Fin 3 → SymbolicRow F) :
    symbolicDeterminant q ≠ 0 ∨
      (∃ i j, SymbolicRowPairIndependent (q i) (q j)) ∨
        SymbolicRankOneBranch q := by
  classical
  by_cases hdet : symbolicDeterminant q ≠ 0
  · exact Or.inl hdet
  · right
    by_cases hpair : ∃ i j, SymbolicRowPairIndependent (q i) (q j)
    · exact Or.inl hpair
    · right
      intro i j hij
      exact hpair ⟨i, j, hij⟩

/-! ## Root-count interfaces used by both non-periodic branches -/

/-- The challenges on which a nonzero coefficient polynomial vanishes are
bounded by its degree. -/
theorem card_filter_eval_eq_zero_le_natDegree
    {F : Type*} [Field F] [DecidableEq F]
    (S : Finset F) (P : Polynomial F) (hP : P ≠ 0) :
    (S.filter fun z => Polynomial.eval z P = 0).card ≤ P.natDegree := by
  have hsub : S.filter (fun z => Polynomial.eval z P = 0) ⊆
      P.roots.toFinset := by
    intro z hz
    rw [Finset.mem_filter] at hz
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hP).2 hz.2)
  calc
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-- A nonzero bivariate polynomial has a nonzero outer coefficient.  Every
specialization to the zero polynomial is a root of that one coefficient.
-/
theorem card_zero_specializations_le_coefficient_degree
    {F : Type*} [Field F] [DecidableEq F]
    (S : Finset F) (P : XOverZ F) (hP : P ≠ 0) :
    ∃ a : ℕ, P.coeff a ≠ 0 ∧
      (S.filter fun z => specializeCoeffZ z P = 0).card ≤
        (P.coeff a).natDegree := by
  have hcoeff : P.coeff P.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP
  refine ⟨P.natDegree, hcoeff, ?_⟩
  have hsub : S.filter (fun z => specializeCoeffZ z P = 0) ⊆
      S.filter (fun z => Polynomial.eval z (P.coeff P.natDegree) = 0) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    have hc := congrArg (fun Q : Polynomial F => Q.coeff P.natDegree) hz.2
    simpa [specializeCoeffZ] using hc
  exact (Finset.card_le_card hsub).trans
    (card_filter_eval_eq_zero_le_natDegree S _
      hcoeff)

end BCHKSTwoFrobeniusRankTwoSpecialization6401
end ProximityPrize.SubmissionLower
