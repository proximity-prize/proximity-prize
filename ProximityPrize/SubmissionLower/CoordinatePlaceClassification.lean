import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.NormalizedPlaceClassification
import ProximityPrize.SubmissionLower.FixedCurveNormSum

import ProximityPrize.SubmissionLower.LocalMathlib_NumberTheory_RamificationInertia_Valuation


/-! .














 -/

namespace ProximityPrize.SubmissionLower.CoordinatePlaceClassification

open scoped Classical BigOperators WithZero
open IsDedekindDomain

noncomputable section

variable (K L : Type*) [Field K] [Field L]
variable [Algebra K L] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L]
variable [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq L := Classical.decEq L

abbrev FiniteNormalization := FixedCurveNormSum.FiniteNormalization K L
abbrev InfinityBase := FixedCurveNormSum.InfinityBase K

local instance : IsFractionRing (InfinityBase K) (RatFunc K) :=
  InfinityValuationRing.infinityRing_isFractionRing K

local instance (priority := 100) : Algebra (InfinityBase K) L :=
  ((algebraMap (RatFunc K) L).comp
    (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra

local instance : IsScalarTower (InfinityBase K) (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

abbrev InfiniteNormalization := FixedCurveNormSum.InfiniteNormalization K L

def parameter : L := algebraMap (Polynomial K) L Polynomial.X

theorem parameter_eq_ratFunc :
    parameter K L = algebraMap (RatFunc K) L (RatFunc.X : RatFunc K) := by
  change algebraMap (Polynomial K) L Polynomial.X =
    algebraMap (RatFunc K) L (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
  exact IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L Polynomial.X

theorem aeval_parameter (f : Polynomial K) :
    Polynomial.aeval (parameter K L) f = algebraMap (Polynomial K) L f := by
  rw [parameter, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]

theorem polynomial_C_map (c : K) :
    algebraMap (Polynomial K) L (Polynomial.C c) = algebraMap K L c :=
  (IsScalarTower.algebraMap_apply K (Polynomial K) L c).symm

section GivenValuation

variable (v : Valuation L ℤᵐ⁰) [htriv : v.IsTrivialOn K]

theorem coefficient_le_one (c : K) : v (algebraMap K L c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [htriv.eq_one c hc]

/-- .
 -/
theorem polynomial_le_one (ht : v (parameter K L) ≤ 1) (f : Polynomial K) :
    v (algebraMap (Polynomial K) L f) ≤ 1 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [map_add]
      exact (v.map_add _ _).trans (max_le hf hg)
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        map_mul, map_pow, polynomial_C_map]
      exact mul_le_one₀ (coefficient_le_one K L v c) zero_le
        (pow_le_one₀ zero_le ht)

/-- .
 -/
theorem finiteNormalization_le_one (ht : v (parameter K L) ≤ 1)
    (s : FiniteNormalization K L) :
    v (algebraMap (FiniteNormalization K L) L s) ≤ 1 := by
  exact NormalizedPlaceClassification.integral_le_one (Polynomial K) L v
    (polynomial_le_one K L v ht) s.property

theorem polynomial_value_of_parameter_gt_one (ht : 1 < v (parameter K L))
    (f : Polynomial K) (hf : f ≠ 0) :
    v (algebraMap (Polynomial K) L f) = v (parameter K L) ^ f.natDegree := by
  rw [← aeval_parameter K L f]
  exact Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
    (v := v) (parameter K L) ht hf

/-- .

 -/
theorem infinityBase_le_one (ht : 1 < v (parameter K L)) (r : InfinityBase K) :
    v (algebraMap (InfinityBase K) L r) ≤ 1 := by
  change v (algebraMap (RatFunc K) L r.val) ≤ 1
  by_cases hr : r.val = 0
  · simp [hr]
  have hdegree : r.val.num.natDegree ≤ r.val.denom.natDegree := by
    have hmem : RatFunc.inftyValuation K r.val ≤ 1 := r.property
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hr,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
    dsimp [RatFunc.intDegree] at hmem
    omega
  have hnum := polynomial_value_of_parameter_gt_one K L v ht
    r.val.num (RatFunc.num_ne_zero hr)
  have hden := polynomial_value_of_parameter_gt_one K L v ht
    r.val.denom r.val.denom_ne_zero
  rw [← RatFunc.num_div_denom r.val, map_div₀, map_div₀,
    ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
    ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
    hnum, hden]
  apply (div_le_one₀ (pow_pos (zero_lt_one.trans ht) _)).mpr
  exact pow_le_pow_right₀ ht.le hdegree

theorem infiniteNormalization_le_one (ht : 1 < v (parameter K L))
    (s : InfiniteNormalization K L) :
    v (algebraMap (InfiniteNormalization K L) L s) ≤ 1 := by
  exact NormalizedPlaceClassification.integral_le_one (InfinityBase K) L v
    (infinityBase_le_one K L v ht) s.property

theorem exists_unique_finite_place (hv : Function.Surjective v)
    (ht : v (parameter K L) ≤ 1) :
    ∃! p : HeightOneSpectrum (FiniteNormalization K L), v = p.valuation L :=
  NormalizedPlaceClassification.exists_unique_place (FiniteNormalization K L) L v
    (finiteNormalization_le_one K L v ht) hv

theorem exists_unique_infinite_place (hv : Function.Surjective v)
    (ht : 1 < v (parameter K L)) :
    ∃! q : HeightOneSpectrum (InfiniteNormalization K L), v = q.valuation L :=
  NormalizedPlaceClassification.exists_unique_place (InfiniteNormalization K L) L v
    (infiniteNormalization_le_one K L v ht) hv

/-- .
 -/
theorem finite_or_infinite_place (hv : Function.Surjective v) :
    (∃ p : HeightOneSpectrum (FiniteNormalization K L), v = p.valuation L) ∨
    (∃ q : HeightOneSpectrum (InfiniteNormalization K L), v = q.valuation L) := by
  by_cases ht : v (parameter K L) ≤ 1
  · exact Or.inl (exists_unique_finite_place K L v hv ht).exists
  · exact Or.inr (exists_unique_infinite_place K L v hv (lt_of_not_ge ht)).exists

end GivenValuation

/-- .
 -/
theorem infinitePlace_liesOver
    (q : HeightOneSpectrum (InfiniteNormalization K L)) :
    q.asIdeal.LiesOver (FixedCurveNormSum.infinityPlace K).asIdeal := by
  have hbase : HeightOneSpectrum.under (InfinityBase K) q =
      FixedCurveNormSum.infinityPlace K := by
    apply HeightOneSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal
      ((HeightOneSpectrum.under (InfinityBase K) q).isPrime.isMaximal
        (HeightOneSpectrum.under (InfinityBase K) q).ne_bot)
  have hq : q.asIdeal.LiesOver
      (HeightOneSpectrum.under (InfinityBase K) q).asIdeal := by
    change q.asIdeal.LiesOver (q.asIdeal.under (InfinityBase K))
    infer_instance
  rwa [hbase] at hq

theorem finitePlace_parameter_le_one
    (p : HeightOneSpectrum (FiniteNormalization K L)) :
    p.valuation L (parameter K L) ≤ 1 := by
  rw [parameter, IsScalarTower.algebraMap_apply (Polynomial K) (FiniteNormalization K L) L]
  exact p.valuation_le_one _

/-- . -/
theorem infinitePlace_parameter_value
    (q : HeightOneSpectrum (InfiniteNormalization K L)) :
    q.valuation L (parameter K L) =
      WithZero.exp ((FixedCurveNormSum.infinityPlace K).asIdeal.ramificationIdx'
        q.asIdeal : ℤ) := by
  letI := infinitePlace_liesOver K L q
  have h := HeightOneSpectrum.valuation_liesOver (K := RatFunc K) L
    (FixedCurveNormSum.infinityPlace K) q (RatFunc.X : RatFunc K)
  rw [FixedCurveNormSum.infinityPlace, InfinityValuationRing.infinity_valuation_eq,
    RatFunc.inftyValuation.X] at h
  rw [parameter_eq_ratFunc]
  simpa [FixedCurveNormSum.infinityPlace] using h.symm

theorem infinitePlace_parameter_gt_one
    (q : HeightOneSpectrum (InfiniteNormalization K L)) :
    1 < q.valuation L (parameter K L) := by
  letI := infinitePlace_liesOver K L q
  rw [infinitePlace_parameter_value, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  exact_mod_cast Nat.pos_iff_ne_zero.mpr
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q.asIdeal
      (FixedCurveNormSum.infinityPlace K).ne_bot)

theorem finitePlace_trivial
    (p : HeightOneSpectrum (FiniteNormalization K L)) :
    (p.valuation L).IsTrivialOn K := by
  constructor
  intro c hc
  let cS : FiniteNormalization K L :=
    algebraMap (Polynomial K) (FiniteNormalization K L) (Polynomial.C c)
  have hunit : IsUnit cS :=
    ((isUnit_iff_ne_zero.mpr hc).map Polynomial.C).map
      (algebraMap (Polynomial K) (FiniteNormalization K L))
  have hval : p.valuation L (algebraMap (FiniteNormalization K L) L cS) = 1 :=
    Valuation.Integers.one_of_isUnit' hunit (p.valuation_le_one (K := L))
  change p.valuation L (algebraMap (FiniteNormalization K L) L
    (algebraMap (Polynomial K) (FiniteNormalization K L) (Polynomial.C c))) = 1 at hval
  rw [← IsScalarTower.algebraMap_apply (Polynomial K) (FiniteNormalization K L) L,
    polynomial_C_map] at hval
  exact hval

theorem infinitePlace_trivial
    (q : HeightOneSpectrum (InfiniteNormalization K L)) :
    (q.valuation L).IsTrivialOn K := by
  constructor
  intro c hc
  letI := infinitePlace_liesOver K L q
  have h := HeightOneSpectrum.valuation_liesOver (K := RatFunc K) L
    (FixedCurveNormSum.infinityPlace K) q (algebraMap K (RatFunc K) c)
  rw [FixedCurveNormSum.infinityPlace, InfinityValuationRing.infinity_valuation_eq] at h
  have hC : RatFunc.inftyValuation K (algebraMap K (RatFunc K) c) = 1 :=
    RatFunc.inftyValuation.C K hc
  rw [hC, one_pow, ← IsScalarTower.algebraMap_apply K (RatFunc K) L] at h
  exact h.symm

abbrev ChartPlace :=
  Sum (HeightOneSpectrum (FiniteNormalization K L))
    (HeightOneSpectrum (InfiniteNormalization K L))

def chartValuation : ChartPlace K L → Valuation L ℤᵐ⁰ :=
  Sum.elim (fun p ↦ p.valuation L) (fun q ↦ q.valuation L)

theorem chartValuation_surjective (p : ChartPlace K L) :
    Function.Surjective (chartValuation K L p) := by
  rcases p with p | q
  · exact p.valuation_surjective L
  · exact q.valuation_surjective L

theorem chartValuation_trivial (p : ChartPlace K L) :
    (chartValuation K L p).IsTrivialOn K := by
  rcases p with p | q
  · exact finitePlace_trivial K L p
  · exact infinitePlace_trivial K L q

theorem chartValuation_injective : Function.Injective (chartValuation K L) := by
  intro p q h
  rcases p with p | p <;> rcases q with q | q
  · congr 1
    exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      (K := L) (Valuation.IsEquiv.of_eq h)
  · have hp := finitePlace_parameter_le_one K L p
    have hq := infinitePlace_parameter_gt_one K L q
    change p.valuation L = q.valuation L at h
    rw [h] at hp
    exact False.elim (not_lt_of_ge hp hq)
  · have hp := infinitePlace_parameter_gt_one K L p
    have hq := finitePlace_parameter_le_one K L q
    change p.valuation L = q.valuation L at h
    rw [h] at hp
    exact False.elim (not_lt_of_ge hq hp)
  · congr 1
    exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      (K := L) (Valuation.IsEquiv.of_eq h)

/-- .
 -/
def NormalizedValuation :=
  {v : Valuation L ℤᵐ⁰ // Function.Surjective v ∧ v.IsTrivialOn K}

def chartMap (p : ChartPlace K L) : NormalizedValuation K L :=
  ⟨chartValuation K L p, chartValuation_surjective K L p, chartValuation_trivial K L p⟩

theorem chartMap_bijective : Function.Bijective (chartMap K L) := by
  constructor
  · intro p q h
    exact chartValuation_injective K L (congrArg Subtype.val h)
  · intro v
    letI : v.val.IsTrivialOn K := v.property.2
    rcases finite_or_infinite_place K L v.val v.property.1 with ⟨p, hp⟩ | ⟨q, hq⟩
    · refine ⟨Sum.inl p, ?_⟩
      apply Subtype.ext
      exact hp.symm
    · refine ⟨Sum.inr q, ?_⟩
      apply Subtype.ext
      exact hq.symm

/-- .

 -/
def chartEquiv : ChartPlace K L ≃ NormalizedValuation K L :=
  Equiv.ofBijective (chartMap K L) (chartMap_bijective K L)

end

end ProximityPrize.SubmissionLower.CoordinatePlaceClassification
