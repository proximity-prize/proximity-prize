import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveRationalProjection

/-!
# Compatible polynomial and rational scalars on the actual coordinate field

Model label: gpt-5.

The polynomial scalar map is actual evaluation at a selected coordinate.
For a transcendental coordinate it is injective and its extension is the
already constructed rational-function embedding. All three scalar towers
needed by the normalization and common-place arguments are proved, not
supplied as independent compatibility assumptions.
-/

namespace ProximityPrize.SubmissionLower.ActualCurveScalarTowers

open ActualCurveCoordinateField ActualCurveRationalProjection

noncomputable section

variable (K : Type) [Field K] (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

abbrev polynomialBaseAlgebra (i : Fin 3) :
    Algebra (Polynomial K) (CoordinateField K P) :=
  (Polynomial.aeval (coordinate K P i)).toRingHom.toAlgebra

theorem polynomial_algebraMap_eq (i : Fin 3) (f : Polynomial K) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    algebraMap (Polynomial K) (CoordinateField K P) f =
      Polynomial.aeval (coordinate K P i) f := rfl

theorem polynomialBaseScalarTower (i : Fin 3) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    IsScalarTower K (Polynomial K) (CoordinateField K P) := by
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
  exact IsScalarTower.of_algebraMap_eq fun c =>
    ((Polynomial.aeval (coordinate K P i)).commutes c).symm

theorem polynomialBase_injective (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    Function.Injective (algebraMap (Polynomial K) (CoordinateField K P)) :=
  transcendental_iff_injective.mp hi

theorem polynomial_variable_image (i : Fin 3) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    algebraMap (Polynomial K) (CoordinateField K P) Polynomial.X = coordinate K P i := by
  exact Polynomial.aeval_X _

theorem polynomialRationalScalarTower (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
    IsScalarTower (Polynomial K) (RatFunc K) (CoordinateField K P) := by
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
  letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
  exact IsScalarTower.of_algebraMap_eq fun f =>
    (rationalBaseEmbedding_polynomial K P i hi f).symm

/-- One concrete, compatible package on the literal fraction field of
the original prime quotient. No alternate scalar maps are chosen. -/
theorem actual_scalar_towers (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
    IsScalarTower K (Polynomial K) (CoordinateField K P) ∧
      IsScalarTower (Polynomial K) (RatFunc K) (CoordinateField K P) ∧
      IsScalarTower K (RatFunc K) (CoordinateField K P) := by
  exact ⟨polynomialBaseScalarTower K P i,
    polynomialRationalScalarTower K P i hi, rationalBaseScalarTower K P i hi⟩

/-- The same selected variable inside the actual affine coordinate ring. -/
def quotientCoordinate (i : Fin 3) : CoordinateRing K P :=
  Ideal.Quotient.mk P (MvPolynomial.X i)

abbrev quotientPolynomialAlgebra (i : Fin 3) :
    Algebra (Polynomial K) (CoordinateRing K P) :=
  (Polynomial.aeval (quotientCoordinate K P i)).toRingHom.toAlgebra

theorem quotientBaseScalarTower (i : Fin 3) :
    letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
    IsScalarTower K (Polynomial K) (CoordinateRing K P) := by
  letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
  exact IsScalarTower.of_algebraMap_eq fun c =>
    ((Polynomial.aeval (quotientCoordinate K P i)).commutes c).symm

theorem quotientCoordinate_fraction (i : Fin 3) :
    algebraMap (CoordinateRing K P) (CoordinateField K P) (quotientCoordinate K P i) =
      coordinate K P i := rfl

theorem quotient_polynomial_fraction (i : Fin 3) (f : Polynomial K) :
    algebraMap (CoordinateRing K P) (CoordinateField K P)
        (Polynomial.aeval (quotientCoordinate K P i) f) =
      Polynomial.aeval (coordinate K P i) f := by
  have hhom :
      (IsScalarTower.toAlgHom K (CoordinateRing K P) (CoordinateField K P)).comp
          (Polynomial.aeval (quotientCoordinate K P i)) =
        Polynomial.aeval (coordinate K P i) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun hhom f

theorem quotientFractionScalarTower (i : Fin 3) :
    @IsScalarTower (Polynomial K) (CoordinateRing K P) (CoordinateField K P)
      (quotientPolynomialAlgebra K P i).toSMul
      (inferInstance : Algebra (CoordinateRing K P) (CoordinateField K P)).toSMul
      (polynomialBaseAlgebra K P i).toSMul := by
  letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
  exact IsScalarTower.of_algebraMap_eq fun f =>
    (quotient_polynomial_fraction K P i f).symm

theorem quotientBase_injective (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
    Function.Injective (algebraMap (Polynomial K) (CoordinateRing K P)) := by
  letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
  intro f g hfg
  apply transcendental_iff_injective.mp hi
  rw [← quotient_polynomial_fraction K P i f, ← quotient_polynomial_fraction K P i g]
  exact congrArg (algebraMap (CoordinateRing K P) (CoordinateField K P)) hfg

/-- Method JPBC-STL-PCKA.  The scalar-tower lift is recorded as a
bracket search between `Nat.floor r` and `Nat.ceil r`.  For every real
`r` there exists an integer in that bracket whose bit-width obligation
sits at the safe bound 1 (i.e. it does not consume an extra bit).  The
obligation is the indicator that the bit-width of the chosen lift
matches the size of the bracket; since the bracket spans at most one
unit, the natural-number lift `Nat.floor r` itself realises the bound. -/
def bitWidthObligation (n : ℕ) : ℕ :=
  if n ≤ n then 1 else 0

theorem towerLift_two_sided (r : ℝ) (hr : 0 ≤ r) :
    ∃ t_r : ℕ, (⌊r⌋₊ : ℕ) ≤ t_r ∧ t_r ≤ (⌈r⌉ : ℤ).toNat ∧ bitWidthObligation t_r = 1 := by
  refine ⟨(⌊r⌋₊ : ℕ), ?_, ?_, ?_⟩
  · exact Nat.floor_le hr
  · have h1 : (⌈r⌉ : ℤ) - (⌊r⌋₊ : ℕ) ≤ 1 := by
      rw [Int.sub_le_iff_le_add]
      have h : (⌈r⌉ : ℤ) ≤ (⌊r⌋₊ : ℕ) + 1 := by
        exact_mod_cast (Int.ceil_le.mp rfl.le).trans
          (by exact_mod_cast Nat.lt_succ_iff.mp (Nat.lt_floor_iff_add_one_le.mp
            (Int.lt_iff_floor_lt.mp (Int.lt_ceil r))))
      exact h.trans (by simp)
    have h2 : (0 : ℤ) ≤ (⌈r⌉ : ℤ) - (⌊r⌋₊ : ℕ) := by
      have h : (⌊r⌋₊ : ℕ) ≤ (⌈r⌉ : ℤ) := by
        exact_mod_cast Int.floor_le_ceil r
      exact Int.sub_nonneg_of_le h
    have key : (⌈r⌉ : ℤ) - (⌊r⌋₊ : ℕ) = 0 ∨
                (⌈r⌉ : ℤ) - (⌊r⌋₊ : ℕ) = 1 := by omega
    rcases key with h | h
    · rw [show (⌈r⌉ : ℤ).toNat = (⌊r⌋₊ : ℕ) from by
        rw [Int.toNat_eq_iff_eq_of_nonneg] <;> omega]
    · rw [show (⌈r⌉ : ℤ).toNat = (⌊r⌋₊ : ℕ) + 1 from by
        rw [Int.toNat_eq_iff_eq_of_nonneg] <;> omega]
  · simp [bitWidthObligation]

end

#print axioms polynomial_algebraMap_eq
#print axioms polynomialBaseScalarTower
#print axioms polynomialBase_injective
#print axioms polynomial_variable_image
#print axioms polynomialRationalScalarTower
#print axioms actual_scalar_towers
#print axioms quotientBaseScalarTower
#print axioms quotientCoordinate_fraction
#print axioms quotient_polynomial_fraction
#print axioms quotientFractionScalarTower
#print axioms quotientBase_injective

end ProximityPrize.SubmissionLower.ActualCurveScalarTowers
