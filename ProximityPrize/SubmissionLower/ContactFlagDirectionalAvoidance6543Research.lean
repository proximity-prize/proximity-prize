import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagExactSeparableProjection6543Research

/-!
# Avoiding the final directional cancellation in the 65.43 flag projection

The common coefficient used by the nested `V = S + mu * U` projection must
already avoid finitely many differential and leading-pole cancellations.
Positive `S` derivative implies that at most one additional value of `mu`
can kill the transformed `U` derivative `G_Y - mu G_S`.  This file folds
that value into the same finite avoidance argument and removes the final
positivity exception from the three-projection construction.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagDirectionalAvoidance6543Research

open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential IsDedekindDomain
open ArbitraryRationalProjectionResearch GlobalSeparableShearResearch
open CoordinateBoxZeroCount ContactSparsePoleSupportResearch
open ContactDependentGenericity6543Research
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
open ContactRegularComponentCover
open ContactFlagAffineFamilyDegree6543Research
open ContactFlagExactSeparableProjection6543Research

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000

/-- If the `S` partial derivative is nonzero, at most one scalar kills the
directional derivative `G_Y - mu G_S`. -/
theorem directional_bad_coefficient_subsingleton
    {K : Type*} [Field K] (G : MvPolynomial (Fin 3) K)
    (hS : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0) :
    ∀ {a b : K},
      MvPolynomial.pderiv (0 : Fin 3) G -
          MvPolynomial.C a * MvPolynomial.pderiv (1 : Fin 3) G = 0 →
      MvPolynomial.pderiv (0 : Fin 3) G -
          MvPolynomial.C b * MvPolynomial.pderiv (1 : Fin 3) G = 0 →
      a = b := by
  intro a b ha hb
  have ha' : MvPolynomial.pderiv (0 : Fin 3) G =
      MvPolynomial.C a * MvPolynomial.pderiv (1 : Fin 3) G :=
    sub_eq_zero.mp ha
  have hb' : MvPolynomial.pderiv (0 : Fin 3) G =
      MvPolynomial.C b * MvPolynomial.pderiv (1 : Fin 3) G :=
    sub_eq_zero.mp hb
  have habmul : MvPolynomial.C a * MvPolynomial.pderiv (1 : Fin 3) G =
      MvPolynomial.C b * MvPolynomial.pderiv (1 : Fin 3) G :=
    ha'.symm.trans hb'
  have hfactor : (MvPolynomial.C a - MvPolynomial.C b) *
      MvPolynomial.pderiv (1 : Fin 3) G = 0 := by
    rw [sub_mul, habmul, sub_self]
  have hCsub : MvPolynomial.C a - MvPolynomial.C b = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hS
  apply MvPolynomial.C_injective
  exact sub_eq_zero.mp hCsub

section FiniteFamily

variable {K : Type*} [Field K] [IsAlgClosed K]
variable {I : Type*} [Fintype I]
variable (E : I → Type*) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
variable (r z : ∀ i, E i)
variable (W : ∀ i,
  Finset (CoordinatePlaceClassification.NormalizedValuation K (E i)))

/-- The common exact finite-separable shear can additionally avoid any
finite family of bad predicates whose fibers contain at most one scalar. -/
theorem exists_common_exact_finite_separable_shear_avoiding
    {J : Type*} [Finite J]
    (Extra : J → K → Prop)
    (hextra : ∀ j {a b}, Extra j a → Extra j b → a = b)
    (embeddingZ : ∀ i, RatFunc K →ₐ[K] E i)
    (hvalueZ : ∀ i, embeddingZ i
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = z i)
    (hfiniteZ : ∀ i,
      letI : Algebra (RatFunc K) (E i) :=
        (embeddingZ i).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) (E i))
    (hsepZ : ∀ i,
      letI : Algebra (RatFunc K) (E i) :=
        (embeddingZ i).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) (E i)) :
    ∃ a : K, a ≠ 0 ∧ (∀ j, ¬ Extra j a) ∧ ∀ i,
      ∃ hs : Transcendental K (r i + a • z i),
        (letI : Algebra (RatFunc K) (E i) :=
            (elementEmbedding K (E i) (r i + a • z i) hs).toRingHom.toAlgebra;
          FiniteDimensional (RatFunc K) (E i)) ∧
        (letI : Algebra (RatFunc K) (E i) :=
            (elementEmbedding K (E i) (r i + a • z i) hs).toRingHom.toAlgebra;
          Algebra.IsSeparable (RatFunc K) (E i)) ∧
        (∀ v ∈ W i, v.val (r i + a • z i) =
          max (v.val (r i)) (v.val (z i))) := by
  have hdz : ∀ i, D K (E i) (z i) ≠ 0 := by
    intro i
    have h := parameterDifferential_ne_zero_of_isSeparable
      K (E i) (embeddingZ i) (hfiniteZ i) (hsepZ i)
    unfold SeparableShearKaehlerResearch.parameterDifferential at h
    rwa [hvalueZ i] at h
  let Q := J ⊕ (I ⊕ Σ i : I, {v // v ∈ W i})
  let Bad : Q → K → Prop
    | Sum.inl j, a => Extra j a
    | Sum.inr (Sum.inl i), a =>
        D K (E i) (r i) + a • D K (E i) (z i) = 0
    | Sum.inr (Sum.inr iv), a =>
        iv.2.1.val (r iv.1 + a • z iv.1) <
          max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
  have hsingle : ∀ q {a b}, Bad q a → Bad q b → a = b := by
    intro q a b ha hb
    rcases q with j | i | ⟨i, v⟩
    · exact hextra j ha hb
    · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
        (hdz i) ha hb
    · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
  obtain ⟨a, ha0, havoid⟩ :=
    exists_nonzero_avoiding_finite_subsingleton Bad hsingle
  refine ⟨a, ha0, ?_, fun i ↦ ?_⟩
  · intro j
    exact havoid (Sum.inl j)
  · have hdiff : D K (E i) (r i) + a • D K (E i) (z i) ≠ 0 := by
      exact havoid (Sum.inr (Sum.inl i))
    obtain ⟨hs, hfinite, hsep⟩ :=
      shear_transcendental_finite_separable_of_differential_ne_zero
        K (E i) (embeddingZ i) (r i) (z i) a
          (hvalueZ i) (hfiniteZ i) (hsepZ i) hdiff
    refine ⟨hs, hfinite, hsep, ?_⟩
    intro v hv
    have hnotlt := havoid (Sum.inr (Sum.inr ⟨i, ⟨v, hv⟩⟩))
    have hupper := v.val.map_add (r i) (a • z i)
    have haz : v.val (a • z i) = v.val (z i) := by
      letI : v.val.IsTrivialOn K := v.property.2
      rw [Algebra.smul_def, map_mul,
        Valuation.IsTrivialOn.eq_one a ha0, one_mul]
    rw [haz] at hupper
    exact le_antisymm hupper (le_of_not_gt hnotlt)

end FiniteFamily

section RegularComponents

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}

/-- One nested flag projection simultaneously has exact pole maxima,
finite-separable projection fields, and a nonzero transformed `U` derivative.
This is the coefficient-choice theorem needed by the 65.43 positivity seam. -/
theorem exists_nestedFlagProjectionData_directional
    (hseparator : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (coordinate Omega C.1 2))
    (hproj : ∀ C : RegularComponent Omega G T H,
      ProjectionsFiniteSeparable Omega C.1)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0) :
    ∃ D : NestedFlagProjectionData hseparator hproj,
      MvPolynomial.pderiv (0 : Fin 3) G -
        MvPolynomial.C D.mu * MvPolynomial.pderiv (1 : Fin 3) G ≠ 0 := by
  classical
  let E : RegularComponent Omega G T H → Type :=
    fun C ↦ CoordinateField Omega C.1
  let rY : ∀ C, E C := fun C ↦ coordinate Omega C.1 0
  let z : ∀ C, E C := fun C ↦ coordinate Omega C.1 2
  let W : ∀ C, Finset
      (CoordinatePlaceClassification.NormalizedValuation Omega (E C)) :=
    fun C ↦ componentRelevantPlaces hseparator hproj C
  let embeddingZ : ∀ C, RatFunc Omega →ₐ[Omega] E C :=
    fun C ↦ rationalBaseEmbedding Omega C.1 2 (hseparator C)
  have hvalueZ : ∀ C, embeddingZ C
      (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X) = z C := by
    intro C
    exact rationalBaseEmbedding_polynomial Omega C.1 2 (hseparator C) Polynomial.X
      |>.trans (Polynomial.aeval_X _)
  have hfiniteZ : ∀ C,
      letI : Algebra (RatFunc Omega) (E C) :=
        (embeddingZ C).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Omega) (E C) := by
    intro C
    exact (hproj C 2 (hseparator C)).1
  have hsepZ : ∀ C,
      letI : Algebra (RatFunc Omega) (E C) :=
        (embeddingZ C).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Omega) (E C) := by
    intro C
    exact (hproj C 2 (hseparator C)).2
  obtain ⟨lam, hlam0, hlam⟩ :=
    exists_common_exact_finite_separable_shear E rY z W
      embeddingZ hvalueZ hfiniteZ hsepZ
  let hU : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (affineU Omega C.1 lam) :=
    fun C ↦ Classical.choose (hlam C)
  have hUdata : ∀ C,
      (letI : Algebra (RatFunc Omega) (E C) :=
          (elementEmbedding Omega (E C) (affineU Omega C.1 lam)
            (hU C)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Omega) (E C)) ∧
      (letI : Algebra (RatFunc Omega) (E C) :=
          (elementEmbedding Omega (E C) (affineU Omega C.1 lam)
            (hU C)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Omega) (E C)) ∧
      ∀ v ∈ W C, v.val (affineU Omega C.1 lam) =
        max (v.val (coordinate Omega C.1 0))
          (v.val (coordinate Omega C.1 2)) := by
    intro C
    have hp : hU C = Classical.choose (hlam C) := Subsingleton.elim _ _
    cases hp
    simpa only [E, rY, z, affineU, hU] using! Classical.choose_spec (hlam C)
  let rS : ∀ C, E C := fun C ↦ coordinate Omega C.1 1
  let u : ∀ C, E C := fun C ↦ affineU Omega C.1 lam
  let embeddingU : ∀ C, RatFunc Omega →ₐ[Omega] E C := fun C ↦
    elementEmbedding Omega (E C) (u C) (hU C)
  have hvalueU : ∀ C, embeddingU C
      (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X) = u C := by
    intro C
    exact elementEmbedding_variable Omega (E C) (u C) (hU C)
  have hfiniteU : ∀ C,
      letI : Algebra (RatFunc Omega) (E C) :=
        (embeddingU C).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Omega) (E C) := fun C ↦ (hUdata C).1
  have hsepU : ∀ C,
      letI : Algebra (RatFunc Omega) (E C) :=
        (embeddingU C).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Omega) (E C) := fun C ↦ (hUdata C).2.1
  let Extra : PUnit → Omega → Prop := fun _ mu ↦
    MvPolynomial.pderiv (0 : Fin 3) G -
      MvPolynomial.C mu * MvPolynomial.pderiv (1 : Fin 3) G = 0
  have hextra : ∀ j {a b}, Extra j a → Extra j b → a = b := by
    intro j a b ha hb
    exact directional_bad_coefficient_subsingleton G hSderiv ha hb
  obtain ⟨mu, hmu0, hmudir, hmu⟩ :=
    exists_common_exact_finite_separable_shear_avoiding E rS u W
      Extra hextra embeddingU hvalueU hfiniteU hsepU
  let hV : ∀ C : RegularComponent Omega G T H, Transcendental Omega
      (coordinate Omega C.1 1 + mu • affineU Omega C.1 lam) :=
    fun C ↦ Classical.choose (hmu C)
  have hVdata : ∀ C,
      (letI : Algebra (RatFunc Omega) (E C) :=
          (elementEmbedding Omega (E C)
            (coordinate Omega C.1 1 + mu • affineU Omega C.1 lam)
            (hV C)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Omega) (E C)) ∧
      (letI : Algebra (RatFunc Omega) (E C) :=
          (elementEmbedding Omega (E C)
            (coordinate Omega C.1 1 + mu • affineU Omega C.1 lam)
            (hV C)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Omega) (E C)) ∧
      ∀ v ∈ W C,
        v.val (coordinate Omega C.1 1 + mu • affineU Omega C.1 lam) =
          max (v.val (coordinate Omega C.1 1))
            (v.val (affineU Omega C.1 lam)) := by
    intro C
    have hp : hV C = Classical.choose (hmu C) := Subsingleton.elim _ _
    cases hp
    simpa only [E, rS, u, hV] using! Classical.choose_spec (hmu C)
  let D : NestedFlagProjectionData hseparator hproj :=
    ⟨lam, hlam0, hU,
      (fun C ↦ (hUdata C).1), (fun C ↦ (hUdata C).2.1),
      (fun C ↦ (hUdata C).2.2),
      mu, hmu0, hV,
      (fun C ↦ (hVdata C).1), (fun C ↦ (hVdata C).2.1),
      (fun C ↦ (hVdata C).2.2)⟩
  refine ⟨D, ?_⟩
  exact hmudir PUnit.unit

end RegularComponents

end

end ProximityPrize.SubmissionLower.ContactFlagDirectionalAvoidance6543Research
