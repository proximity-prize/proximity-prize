import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.GlobalSeparableShearResearch
import ProximityPrize.SubmissionLower.CharacteristicFreeInseparableDichotomyResearch
import ProximityPrize.SubmissionLower.ContactRegularComponentCover

/-!
# The regular-component split for one global separating shear

This module turns a characteristic-free summed Z-degree budget smaller than
the characteristic into componentwise separability of every transcendental
Z projection.  It then instantiates the dependent-family global shear theorem
on exactly those components.  Components with algebraic Z are intentionally
left to the separate singleton-seed lemma.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalShearComponentSplitResearch

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveZeroCount
open CharacteristicFreeInseparableDichotomyResearch
open ContactRegularComponentCover
open GlobalSeparableShearResearch
open ArbitraryRationalProjectionResearch

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable (K : Type) [Field K] [IsAlgClosed K]

section AbstractFamily

variable {I : Type} [Fintype I]
variable (P : I → Ideal (MvPolynomial (Fin 3) K))
variable [∀ i, (P i).IsPrime]

/-- A summed full-degree budget below the positive characteristic forces
every transcendental projection in that coordinate to be separable. -/
theorem family_coordinate_isSeparable_of_sum_degree_lt_char
    (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (hfinite : ∀ i, ProjectionsFinite K (P i))
    (j : Fin 3) (B : ℕ)
    (hsum : (∑ i, actualCoordinateDegree K (P i) j) ≤ B)
    (hBp : B < p) (i : I)
    (hi : Transcendental K (coordinate K (P i) j)) :
    letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
      rationalBaseAlgebra K (P i) j hi
    Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)) := by
  by_contra hnotsep
  have hpdeg : p ≤ actualCoordinateDegree K (P i) j :=
    char_le_actualCoordinateDegree_of_not_isSeparable
      K (P i) (hfinite i) p hp j hi hnotsep
  have hterm : actualCoordinateDegree K (P i) j ≤
      ∑ k, actualCoordinateDegree K (P k) j := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun k ↦ actualCoordinateDegree K (P k) j)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  omega

end AbstractFamily

section RegularComponents

variable (G T H : MvPolynomial (Fin 3) K)

/-- The subtype of regular components on which the seed coordinate is a
genuine rational parameter. -/
abbrev SeedTranscendentalComponent :=
  {C : RegularComponent K G T H //
    Transcendental K (coordinate K C.1 2)}

/-- One common coefficient and all of its componentwise finite-separable
projection data, obtained solely from finite projections and a summed
Z-degree budget below the characteristic. -/
theorem exists_common_regularComponent_finite_separable_shear
    (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (hfinite : ∀ C : RegularComponent K G T H, ProjectionsFinite K C.1)
    (BZ : ℕ)
    (hZsum : (∑ C : RegularComponent K G T H,
      actualCoordinateDegree K C.1 2) ≤ BZ)
    (hBZp : BZ < p) :
    ∃ a : K, a ≠ 0 ∧
      ∀ C : SeedTranscendentalComponent K G T H,
        ∃ hS : Transcendental K
            (coordinate K C.1.1 1 + a • coordinate K C.1.1 2),
          (letI : Algebra (RatFunc K) (CoordinateField K C.1.1) :=
              (elementEmbedding K (CoordinateField K C.1.1)
                (coordinate K C.1.1 1 + a • coordinate K C.1.1 2)
                hS).toRingHom.toAlgebra;
            FiniteDimensional (RatFunc K) (CoordinateField K C.1.1)) ∧
          (letI : Algebra (RatFunc K) (CoordinateField K C.1.1) :=
              (elementEmbedding K (CoordinateField K C.1.1)
                (coordinate K C.1.1 1 + a • coordinate K C.1.1 2)
                hS).toRingHom.toAlgebra;
            Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1.1)) := by
  let E : SeedTranscendentalComponent K G T H → Type :=
    fun C ↦ CoordinateField K C.1.1
  let r : ∀ C, E C := fun C ↦ coordinate K C.1.1 1
  let z : ∀ C, E C := fun C ↦ coordinate K C.1.1 2
  let embeddingZ : ∀ C, RatFunc K →ₐ[K] E C :=
    fun C ↦ rationalBaseEmbedding K C.1.1 2 C.2
  have hvalueZ : ∀ C, embeddingZ C
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = z C := by
    intro C
    exact rationalBaseEmbedding_polynomial K C.1.1 2 C.2 Polynomial.X
      |>.trans (Polynomial.aeval_X _)
  have hfiniteZ : ∀ C,
      letI : Algebra (RatFunc K) (E C) :=
        (embeddingZ C).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) (E C) := by
    intro C
    exact hfinite C.1 2 C.2
  have hsepZ : ∀ C,
      letI : Algebra (RatFunc K) (E C) :=
        (embeddingZ C).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) (E C) := by
    intro C
    exact family_coordinate_isSeparable_of_sum_degree_lt_char
      K (fun D : RegularComponent K G T H ↦ D.1)
      p hp hfinite 2 BZ hZsum hBZp C.1 C.2
  simpa only [E, r, z, embeddingZ] using
    (exists_common_finite_separable_shear K E r z
      embeddingZ hvalueZ hfiniteZ hsepZ)

end RegularComponents

end

end ProximityPrize.SubmissionLower.ContactGlobalShearComponentSplitResearch

#print axioms ProximityPrize.SubmissionLower.ContactGlobalShearComponentSplitResearch.family_coordinate_isSeparable_of_sum_degree_lt_char
#print axioms ProximityPrize.SubmissionLower.ContactGlobalShearComponentSplitResearch.exists_common_regularComponent_finite_separable_shear
