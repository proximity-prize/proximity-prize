import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CoordinatePoleMass


/-! .










 -/

namespace ProximityPrize.SubmissionLower.CommonPlaceBalance

open scoped Classical BigOperators WithZero
open IsDedekindDomain

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

abbrev Place := CoordinatePlaceClassification.NormalizedValuation K L

def order (v : Place K L) (x : L) : ℤ := -(v.val x).log

def zeroOrder (v : Place K L) (x : L) : ℤ := max 0 (order K L v x)

theorem zeroOrder_nonneg (v : Place K L) (x : L) : 0 ≤ zeroOrder K L v x :=
  le_max_left _ _

theorem zeroOrder_sub_poleOrder (v : Place K L) (x : L) :
    zeroOrder K L v x - CoordinatePoleMass.poleOrder K L v x = order K L v x := by
  unfold zeroOrder order CoordinatePoleMass.poleOrder ContactLocalPoleBound.poleOrder
  omega

variable [IsAlgClosed K]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (Place K L) := Classical.decEq _

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

variable (s : Finset (Polynomial K)) (hs : ∀ p ∈ s, Irreducible p ∧ p.Monic)

def finiteFiber (p : {p : Polynomial K // p ∈ s}) :
    Finset (Ideal (FiniteNormalization K L)) :=
  IsDedekindDomain.primesOverFinset
    (RatFuncProductFormula.primePlace K p.1 (hs p.1 p.2).1).asIdeal
    (FiniteNormalization K L)

abbrev FiniteIndex :=
  Σ p : {p : Polynomial K // p ∈ s},
    {Q : Ideal (FiniteNormalization K L) // Q ∈ finiteFiber K L s hs p}

def finitePlace (i : FiniteIndex K L s hs) :
    HeightOneSpectrum (FiniteNormalization K L) :=
  NormValuationTransport.placeAbove (Polynomial K) (FiniteNormalization K L)
    (RatFuncProductFormula.primePlace K i.1.1 (hs i.1.1 i.1.2).1) i.2

/-- .
 -/
theorem finitePlace_injective : Function.Injective (finitePlace K L s hs) := by
  rintro ⟨p, P⟩ ⟨q, Q⟩ h
  have hI : P.1 = Q.1 := congrArg HeightOneSpectrum.asIdeal h
  let pbase := RatFuncProductFormula.primePlace K p.1 (hs p.1 p.2).1
  let qbase := RatFuncProductFormula.primePlace K q.1 (hs q.1 q.2).1
  letI : P.1.LiesOver pbase.asIdeal :=
    ((IsDedekindDomain.mem_primesOverFinset_iff pbase.ne_bot
      (FiniteNormalization K L)).mp P.2).2
  letI : Q.1.LiesOver qbase.asIdeal :=
    ((IsDedekindDomain.mem_primesOverFinset_iff qbase.ne_bot
      (FiniteNormalization K L)).mp Q.2).2
  have hbase : pbase = qbase := by
    apply HeightOneSpectrum.ext
    calc
      pbase.asIdeal = P.1.under (Polynomial K) := Ideal.over_def P.1 pbase.asIdeal
      _ = Q.1.under (Polynomial K) := congrArg (Ideal.under (Polynomial K)) hI
      _ = qbase.asIdeal := (Ideal.over_def Q.1 qbase.asIdeal).symm
  have hpq : p = q := Subtype.ext <|
    RatFuncProductFormula.primePlace_injective K p.1 q.1
      (hs p.1 p.2).1 (hs q.1 q.2).1 (hs p.1 p.2).2 (hs q.1 q.2).2 hbase
  subst q
  have hPQ : P = Q := Subtype.ext hI
  cases hPQ
  rfl

abbrev InfinityIndex :=
  {Q : Ideal (InfiniteNormalization K L) // Q ∈ CoordinatePoleMass.infinityFiber K L}

abbrev FamilyIndex := FiniteIndex K L s hs ⊕ InfinityIndex K L

def familyChart : FamilyIndex K L s hs → CoordinatePlaceClassification.ChartPlace K L :=
  Sum.elim (fun i ↦ Sum.inl (finitePlace K L s hs i))
    (fun Q ↦ Sum.inr (CoordinatePoleMass.infinityPlace K L Q))

def familyValuation (i : FamilyIndex K L s hs) : Place K L :=
  CoordinatePlaceClassification.chartMap K L (familyChart K L s hs i)

theorem familyValuation_injective : Function.Injective (familyValuation K L s hs) := by
  intro i j h
  have hc := (CoordinatePlaceClassification.chartMap_bijective K L).1 h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact congrArg Sum.inl (finitePlace_injective K L s hs (Sum.inl.inj hc))
    | inr j => cases hc
  | inr i =>
    cases j with
    | inl j => cases hc
    | inr j =>
      have hI : i.1 = j.1 := congrArg HeightOneSpectrum.asIdeal (Sum.inr.inj hc)
      exact congrArg Sum.inr (Subtype.ext hI)

theorem finiteContribution_eq_sum (x : L) :
    FixedCurveNormSum.finiteContribution K L s hs x =
      ∑ i : FiniteIndex K L s hs,
        NormValuationTransport.fieldOrder (FiniteNormalization K L) L
          (finitePlace K L s hs i) x := by
  rw [Fintype.sum_sigma]
  unfold FixedCurveNormSum.finiteContribution
  simp only [Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro p _
  rw [NormalizationUnitWeights.finiteBase_natDegree_eq_one K p.1 (hs p.1 p.2).1]
  simp only [Nat.cast_one, one_mul]
  apply Finset.sum_congr rfl
  intro Q _
  have hweight := NormalizationUnitWeights.finitePlace_inertia_one K L
    (finitePlace K L s hs ⟨p, Q⟩)
  change Q.1.inertiaDeg (Polynomial K) = 1 at hweight
  rw [hweight]
  simp only [Nat.cast_one, one_mul]
  rfl

theorem infinityContribution_eq_sum (x : L) :
    FixedCurveNormSum.infinityContribution K L x =
      ∑ Q : InfinityIndex K L,
        NormValuationTransport.fieldOrder (InfiniteNormalization K L) L
          (CoordinatePoleMass.infinityPlace K L Q) x := by
  unfold FixedCurveNormSum.infinityContribution
  simp only [Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro Q _
  rw [NormalizationUnitWeights.infiniteFiber_weight_one K L Q, one_mul]
  rfl

/-- .
 -/
theorem sum_family_order_eq_contributions (x : L) :
    (∑ i : FamilyIndex K L s hs, order K L (familyValuation K L s hs i) x) =
      FixedCurveNormSum.finiteContribution K L s hs x +
        FixedCurveNormSum.infinityContribution K L x := by
  rw [Fintype.sum_sum_type]
  change
    (∑ i : FiniteIndex K L s hs,
      NormValuationTransport.fieldOrder (FiniteNormalization K L) L
        (finitePlace K L s hs i) x) +
    (∑ Q : InfinityIndex K L,
      NormValuationTransport.fieldOrder (InfiniteNormalization K L) L
        (CoordinatePoleMass.infinityPlace K L Q) x) = _
  rw [← finiteContribution_eq_sum K L s hs x, ← infinityContribution_eq_sum K L x]

def familyValues : Finset (Place K L) :=
  Finset.univ.image (familyValuation K L s hs)

theorem sum_familyValues_order_eq_contributions (x : L) :
    (∑ v ∈ familyValues K L s hs, order K L v x) =
      FixedCurveNormSum.finiteContribution K L s hs x +
        FixedCurveNormSum.infinityContribution K L x := by
  rw [familyValues, Finset.sum_image
    (fun _ _ _ _ h ↦ familyValuation_injective K L s hs h)]
  exact sum_family_order_eq_contributions K L s hs x

variable {s hs}

/-- .
 -/
def placesFor (x : L) (hx : x ≠ 0) : Finset (Place K L) :=
  familyValues K L (FixedCurveNormSum.basePrimesFor K L x hx)
    (FixedCurveNormSum.basePrimesFor_primes K L x hx)

theorem sum_placesFor_order_zero (x : L) (hx : x ≠ 0) :
    (∑ v ∈ placesFor K L x hx, order K L v x) = 0 := by
  rw [placesFor, sum_familyValues_order_eq_contributions]
  exact FixedCurveNormSum.projective_curve_order_sum K L x hx

/-- .
 -/
theorem placesFor_covers (x : L) (hx : x ≠ 0) (v : Place K L)
    (hv : order K L v x ≠ 0) : v ∈ placesFor K L x hx := by
  obtain ⟨c, rfl⟩ := (CoordinatePlaceClassification.chartMap_bijective K L).2 v
  let s := FixedCurveNormSum.basePrimesFor K L x hx
  let hs := FixedCurveNormSum.basePrimesFor_primes K L x hx
  change CoordinatePlaceClassification.chartMap K L c ∈ familyValues K L s hs
  rcases c with q | q
  · have hq : NormValuationTransport.fieldOrder (FiniteNormalization K L) L q x ≠ 0 := hv
    obtain ⟨p, hp, hirred, hQ⟩ := FixedCurveNormSum.basePrimesFor_covers K L x hx q hq
    let pindex : {p : Polynomial K // p ∈ s} := ⟨p, hp⟩
    let Q : {Q : Ideal (FiniteNormalization K L) // Q ∈ finiteFiber K L s hs pindex} :=
      ⟨q.asIdeal, hQ⟩
    let i : FamilyIndex K L s hs := Sum.inl ⟨pindex, Q⟩
    have heq : familyValuation K L s hs i =
        CoordinatePlaceClassification.chartMap K L (Sum.inl q) := by
      have hplace : finitePlace K L s hs ⟨pindex, Q⟩ = q := by
        apply HeightOneSpectrum.ext
        rfl
      change CoordinatePlaceClassification.chartMap K L
        (Sum.inl (finitePlace K L s hs ⟨pindex, Q⟩)) = _
      rw [hplace]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
  · have hQ : q.asIdeal ∈ CoordinatePoleMass.infinityFiber K L :=
      (IsDedekindDomain.mem_primesOverFinset_iff
        (FixedCurveNormSum.infinityPlace K).ne_bot (InfiniteNormalization K L)).mpr
        ⟨q.isPrime, CoordinatePlaceClassification.infinitePlace_liesOver K L q⟩
    let Q : InfinityIndex K L := ⟨q.asIdeal, hQ⟩
    let i : FamilyIndex K L s hs := Sum.inr Q
    have heq : familyValuation K L s hs i =
        CoordinatePlaceClassification.chartMap K L (Sum.inr q) := by
      have hplace : CoordinatePoleMass.infinityPlace K L Q = q := by
        apply HeightOneSpectrum.ext
        rfl
      change CoordinatePlaceClassification.chartMap K L
        (Sum.inr (CoordinatePoleMass.infinityPlace K L Q)) = _
      rw [hplace]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩

theorem sum_placesFor_zero_eq_pole (x : L) (hx : x ≠ 0) :
    (∑ v ∈ placesFor K L x hx, zeroOrder K L v x) =
      ∑ v ∈ placesFor K L x hx, CoordinatePoleMass.poleOrder K L v x := by
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simp_rw [zeroOrder_sub_poleOrder]
  exact sum_placesFor_order_zero K L x hx

/-- .
 -/
theorem finite_zero_places_le_poleMass (x : L) (hx : x ≠ 0)
    (U : Finset (Place K L)) (hU : ∀ v ∈ U, 1 ≤ order K L v x) :
    (U.card : ℤ) ≤
      ∑ v ∈ placesFor K L x hx, CoordinatePoleMass.poleOrder K L v x := by
  have hsub : U ⊆ placesFor K L x hx := by
    intro v hv
    apply placesFor_covers K L x hx v
    have h := hU v hv
    omega
  calc
    (U.card : ℤ) = ∑ _v ∈ U, (1 : ℤ) := by simp
    _ ≤ ∑ v ∈ U, zeroOrder K L v x := by
      apply Finset.sum_le_sum
      intro v hv
      exact (hU v hv).trans (le_max_right _ _)
    _ ≤ ∑ v ∈ placesFor K L x hx, zeroOrder K L v x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro v _ _
      exact zeroOrder_nonneg K L v x
    _ = _ := sum_placesFor_zero_eq_pole K L x hx

end

end ProximityPrize.SubmissionLower.CommonPlaceBalance
