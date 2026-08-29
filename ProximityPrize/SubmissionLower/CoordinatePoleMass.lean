import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.NormalizationUnitWeights
import ProximityPrize.SubmissionLower.ContactLocalPoleBound
import ProximityPrize.SubmissionLower.LocalMathlib_NumberTheory_RamificationInertia_Basic

/-! .















 -/

namespace ProximityPrize.SubmissionLower.CoordinatePoleMass

open scoped Classical BigOperators WithZero
open IsDedekindDomain

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

abbrev Place := CoordinatePlaceClassification.NormalizedValuation K L

def poleOrder (v : Place K L) (x : L) : ℤ :=
  ContactLocalPoleBound.poleOrder v.val x

theorem poleOrder_nonneg (v : Place K L) (x : L) : 0 ≤ poleOrder K L v x :=
  le_max_left _ _

theorem poleOrder_eq_zero_of_le_one (v : Place K L) (x : L) (h : v.val x ≤ 1) :
    poleOrder K L v x = 0 := by
  change max 0 (v.val x).log = 0
  rw [← ContactLocalPoleBound.log_max_one, max_eq_left h, WithZero.log_one]

variable [IsAlgClosed K]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (Place K L) := Classical.decEq _

abbrev InfinityBase := FixedCurveNormSum.InfinityBase K

local instance : IsFractionRing (InfinityBase K) (RatFunc K) :=
  InfinityValuationRing.infinityRing_isFractionRing K

local instance (priority := 100) : Algebra (InfinityBase K) L :=
  ((algebraMap (RatFunc K) L).comp
    (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra

local instance : IsScalarTower (InfinityBase K) (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

abbrev InfiniteNormalization := FixedCurveNormSum.InfiniteNormalization K L

def infinityFiber : Finset (Ideal (InfiniteNormalization K L)) :=
  IsDedekindDomain.primesOverFinset (FixedCurveNormSum.infinityPlace K).asIdeal
    (InfiniteNormalization K L)

def infinityPlace
    (Q : {Q : Ideal (InfiniteNormalization K L) // Q ∈ infinityFiber K L}) :
    HeightOneSpectrum (InfiniteNormalization K L) :=
  NormValuationTransport.placeAbove (InfinityBase K) (InfiniteNormalization K L)
    (FixedCurveNormSum.infinityPlace K) Q

def infinityValuation
    (Q : {Q : Ideal (InfiniteNormalization K L) // Q ∈ infinityFiber K L}) :
    Place K L :=
  CoordinatePlaceClassification.chartMap K L (Sum.inr (infinityPlace K L Q))

theorem infinityValuation_injective : Function.Injective (infinityValuation K L) := by
  intro P Q h
  apply Subtype.ext
  have hc := (CoordinatePlaceClassification.chartMap_bijective K L).1 h
  have hp := Sum.inr.inj hc
  exact congrArg (fun p : HeightOneSpectrum (InfiniteNormalization K L) ↦ p.asIdeal) hp

theorem infinity_pole_eq_ramification
    (Q : {Q : Ideal (InfiniteNormalization K L) // Q ∈ infinityFiber K L}) :
    poleOrder K L (infinityValuation K L Q) (CoordinatePlaceClassification.parameter K L) =
      ((FixedCurveNormSum.infinityPlace K).asIdeal.ramificationIdx' Q.1 : ℤ) := by
  change max 0 (((infinityPlace K L Q).valuation L)
    (CoordinatePlaceClassification.parameter K L)).log = _
  rw [CoordinatePlaceClassification.infinitePlace_parameter_value,
    WithZero.log_exp, max_eq_right (Int.natCast_nonneg _)]
  rfl

/-- .
 -/
theorem sum_infinity_ramification_eq_finrank :
    (∑ Q ∈ (infinityFiber K L).attach,
      (FixedCurveNormSum.infinityPlace K).asIdeal.ramificationIdx' Q.1) =
      Module.finrank (RatFunc K) L := by
  have h := Ideal.sum_ramification_inertia (InfiniteNormalization K L) (RatFunc K) L
    (FixedCurveNormSum.infinityPlace K).ne_bot
  calc
    (∑ Q ∈ (infinityFiber K L).attach,
        (FixedCurveNormSum.infinityPlace K).asIdeal.ramificationIdx' Q.1) =
      ∑ Q ∈ infinityFiber K L,
        (FixedCurveNormSum.infinityPlace K).asIdeal.ramificationIdx' Q *
          (FixedCurveNormSum.infinityPlace K).asIdeal.inertiaDeg' Q := by
      rw [← Finset.sum_attach (infinityFiber K L)
        (fun Q : Ideal (InfiniteNormalization K L) ↦
          (FixedCurveNormSum.infinityPlace K).asIdeal.ramificationIdx' Q *
            (FixedCurveNormSum.infinityPlace K).asIdeal.inertiaDeg' Q)]
      apply Finset.sum_congr rfl
      intro Q _
      have hf := NormalizationUnitWeights.infinitePlace_inertia'_one K L (infinityPlace K L Q)
      change (FixedCurveNormSum.infinityPlace K).asIdeal.inertiaDeg' Q.1 = 1 at hf
      rw [hf, mul_one]
    _ = Module.finrank (RatFunc K) L := h

theorem sum_infinity_poles_eq_finrank :
    (∑ Q ∈ (infinityFiber K L).attach,
      poleOrder K L (infinityValuation K L Q) (CoordinatePlaceClassification.parameter K L)) =
      (Module.finrank (RatFunc K) L : ℤ) := by
  simp_rw [infinity_pole_eq_ramification]
  exact_mod_cast sum_infinity_ramification_eq_finrank K L

def infinityValues : Finset (Place K L) :=
  (infinityFiber K L).attach.image (infinityValuation K L)

theorem sum_poles_infinityValues_eq_finrank :
    (∑ v ∈ infinityValues K L,
      poleOrder K L v (CoordinatePlaceClassification.parameter K L)) =
      (Module.finrank (RatFunc K) L : ℤ) := by
  rw [infinityValues, Finset.sum_image (fun _ _ _ _ h ↦ infinityValuation_injective K L h)]
  exact sum_infinity_poles_eq_finrank K L

/-- .
 -/
theorem poleOrder_eq_zero_of_not_mem_infinity (v : Place K L)
    (hv : v ∉ infinityValues K L) :
    poleOrder K L v (CoordinatePlaceClassification.parameter K L) = 0 := by
  by_contra hnonzero
  have ht : 1 < v.val (CoordinatePlaceClassification.parameter K L) :=
    lt_of_not_ge fun hle ↦ hnonzero (poleOrder_eq_zero_of_le_one K L v _ hle)
  letI : v.val.IsTrivialOn K := v.property.2
  obtain ⟨q, hq, _⟩ :=
    CoordinatePlaceClassification.exists_unique_infinite_place K L v.val v.property.1 ht
  have hmem : q.asIdeal ∈ infinityFiber K L :=
    (IsDedekindDomain.mem_primesOverFinset_iff
      (FixedCurveNormSum.infinityPlace K).ne_bot (InfiniteNormalization K L)).mpr
      ⟨q.isPrime, CoordinatePlaceClassification.infinitePlace_liesOver K L q⟩
  let Q : {Q : Ideal (InfiniteNormalization K L) // Q ∈ infinityFiber K L} := ⟨q.asIdeal, hmem⟩
  have hplace : infinityPlace K L Q = q := by
    apply HeightOneSpectrum.ext
    rfl
  have hvmap : infinityValuation K L Q = v := by
    apply Subtype.ext
    change (infinityPlace K L Q).valuation L = v.val
    rw [hplace]
    exact hq.symm
  apply hv
  rw [← hvmap]
  exact Finset.mem_image.mpr ⟨Q, Finset.mem_attach _ Q, rfl⟩

/-- .
 -/
theorem finite_sum_pole_le_finrank (W : Finset (Place K L)) :
    (∑ v ∈ W, poleOrder K L v (CoordinatePlaceClassification.parameter K L)) ≤
      (Module.finrank (RatFunc K) L : ℤ) := by
  have htrim :
      (∑ v ∈ W, poleOrder K L v (CoordinatePlaceClassification.parameter K L)) =
      ∑ v ∈ W ∩ infinityValues K L,
        poleOrder K L v (CoordinatePlaceClassification.parameter K L) := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro v hvW hvnot
    apply poleOrder_eq_zero_of_not_mem_infinity K L v
    intro hvI
    exact hvnot (Finset.mem_inter.mpr ⟨hvW, hvI⟩)
  calc
    _ = ∑ v ∈ W ∩ infinityValues K L,
        poleOrder K L v (CoordinatePlaceClassification.parameter K L) := htrim
    _ ≤ ∑ v ∈ infinityValues K L,
        poleOrder K L v (CoordinatePlaceClassification.parameter K L) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro v _ _
      exact poleOrder_nonneg K L v _
    _ = (Module.finrank (RatFunc K) L : ℤ) := sum_poles_infinityValues_eq_finrank K L

theorem finite_indexed_sum_pole_le_finrank
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → Place K L)
    (hv : Set.InjOn v (s : Set ι)) :
    (∑ i ∈ s, poleOrder K L (v i) (CoordinatePlaceClassification.parameter K L)) ≤
      (Module.finrank (RatFunc K) L : ℤ) := by
  have h := finite_sum_pole_le_finrank K L (s.image v)
  rwa [Finset.sum_image (fun _ hx _ hy heq ↦ hv hx hy heq)] at h

end

end ProximityPrize.SubmissionLower.CoordinatePoleMass
