import ProximityPrize.SubmissionLower.BCHKSPrimitiveEffective6399
import ProximityPrize.SubmissionLower.BCHKSUniversalX0Avoidance6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open scoped BigOperators

set_option maxHeartbeats 100000

namespace UniversalPrimitiveX0Avoidance6399

local instance concreteUniversalChar :
    CharP IRSProfile.Field 2130706433 :=
  charP_of_injective_algebraMap' KoalaBear.Field 2130706433

abbrev F := IRSProfile.Field
abbrev TriPoly := Polynomial (Polynomial (Polynomial F))

def primitiveObstructionBudget : ℕ := 96013043303953399344
def totalX0ObstructionBudget : ℕ := 96013057916249513816

theorem totalX0ObstructionBudget_lt_field :
    totalX0ObstructionBudget < Fintype.card F := by
  rw [CompPoly.Extension.Ext.card_ext]
  norm_num [totalX0ObstructionBudget, F, IRSProfile.Field, KoalaBear.Ext6,
    KoalaBear.fieldSize]

private theorem eval_C_ne_zero_of_ratfunc_map_eval_ne_zero
    (P : Polynomial (Polynomial F)) (x : F)
    (h : Polynomial.eval (algebraMap F (RatFunc F) x)
      (P.map (algebraMap F[X] (RatFunc F))) ≠ 0) :
    Polynomial.eval (Polynomial.C x) P ≠ 0 := by
  intro hz
  apply h
  rw [← Polynomial.eval₂_eq_eval_map]
  have hx : (algebraMap F[X] (RatFunc F)) (Polynomial.C x) =
      algebraMap F (RatFunc F) x := by simp
  rw [← hx, Polynomial.eval₂_hom, hz]
  exact map_zero _

private theorem factorXObstruction_ne_zero_of_outer
    (Q R : TriPoly) (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hRpos : 0 < R.natDegree)
    (hQdeg : Q.natDegree ≤ UniversalX0Avoidance6399.M) :
    factorXObstruction R ≠ 0 := by
  have hRirr :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
  have hRdeg : R.natDegree ≤ Q.natDegree :=
    Polynomial.natDegree_le_of_dvd
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hQ
  have hRlt : R.natDegree < 2130706433 :=
    lt_of_le_of_lt (hRdeg.trans hQdeg)
      (by norm_num [UniversalX0Avoidance6399.M])
  apply _root_.mul_ne_zero
  · exact Polynomial.leadingCoeff_ne_zero.mpr hRirr.ne_zero
  · exact rawSepResultant_ne_zero_of_irreducible 2130706433 R
      hRirr hRpos hRlt

/-- Simultaneously avoid the primitive-content obstruction and the
leading/separability obstruction for every positive normalized outer factor.
The entire cost is paid against the huge choice field, never the seed ledger. -/
theorem exists_x0_primitive_and_factor_good
    (Q : TriPoly) (hQ : Q ≠ 0)
    (hQdeg : Q.natDegree ≤ UniversalX0Avoidance6399.M)
    (hZ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q, ∀ j,
      (Polynomial.Bivariate.swap (R.coeff j)).natDegree ≤ bchksZCap6399)
    (hXswap : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q, ∀ j,
      Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (R.coeff j)) ≤
        bchksXCap6399)
    (hX : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      degreeX (mapZToRatFunc R) ≤ UniversalX0Avoidance6399.DX)
    (hlead : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.leadingCoeff.natDegree ≤ UniversalX0Avoidance6399.DX) :
    ∃ x₀ : F,
      ∀ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        (triSpecializeX R x₀).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) ≠ 0 := by
  classical
  let Outer := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun R => 0 < R.natDegree)
  let T := Outer.attach
  let cert : ∀ r : ↥Outer, EffectivePrimitiveObstruction F (r : TriPoly) := fun r =>
    Classical.choose (effectivePrimitiveObstruction_of_irreducible6399
      (r : TriPoly)
      (UniqueFactorizationMonoid.prime_of_normalized_factor (r : TriPoly)
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1)).irreducible
      (Finset.mem_filter.mp r.property).2
      (hZ (r : TriPoly)
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1))
      (hXswap (r : TriPoly)
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1)))
  have hcertDegree : ∀ r : ↥Outer, (cert r).obstruction.natDegree ≤
      2 * (bchksZCap6399 + 1) * bchksXCap6399 := by
    intro r
    exact Classical.choose_spec (effectivePrimitiveObstruction_of_irreducible6399
      (r : TriPoly)
      (UniqueFactorizationMonoid.prime_of_normalized_factor (r : TriPoly)
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1)).irreducible
      (Finset.mem_filter.mp r.property).2
      (hZ (r : TriPoly)
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1))
      (hXswap (r : TriPoly)
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1)))
  let g : Polynomial F →+* RatFunc F := algebraMap _ _
  let primRat : ↥Outer → Polynomial (RatFunc F) := fun r =>
    (cert r).obstruction.map (algebraMap F (RatFunc F))
  let factorRat : ↥Outer → Polynomial (RatFunc F) := fun r =>
    (factorXObstruction (r : TriPoly)).map g
  let combined : ↥Outer → Polynomial (RatFunc F) := fun r =>
    primRat r * factorRat r
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hf : Function.Injective (algebraMap F (RatFunc F)) :=
    FaithfulSMul.algebraMap_injective F (RatFunc F)
  have hcombined : ∀ r ∈ T, combined r ≠ 0 := by
    intro r hr
    exact mul_ne_zero
      ((Polynomial.map_ne_zero_iff hf).mpr (cert r).ne)
      ((Polynomial.map_ne_zero_iff hg).mpr (by
        have hmem := Finset.mem_filter.mp r.property
        have hRQ := Multiset.mem_toFinset.mp hmem.1
        exact factorXObstruction_ne_zero_of_outer Q (r : TriPoly) hQ hRQ
          hmem.2 hQdeg))
  have hOuterCard : Outer.card ≤ UniversalX0Avoidance6399.M := by
    have hsum := UniversalX0Avoidance6399.positive_outer_factor_degree_sum_le
      Q hQ UniversalX0Avoidance6399.M hQdeg
    dsimp only at hsum
    calc
      Outer.card = Outer.card • (1 : ℕ) := by simp
      _ ≤ ∑ R ∈ Outer, R.natDegree := by
        apply Finset.card_nsmul_le_sum
        intro R hR
        exact (Finset.mem_filter.mp hR).2
      _ ≤ UniversalX0Avoidance6399.M := by simpa [Outer] using hsum
  have hprimSum : (∑ r ∈ T, (cert r).obstruction.natDegree) ≤
      primitiveObstructionBudget := by
    calc
      (∑ r ∈ T, (cert r).obstruction.natDegree) ≤
          ∑ _r ∈ T, 2 * (bchksZCap6399 + 1) * bchksXCap6399 :=
        Finset.sum_le_sum (fun r hr => hcertDegree r)
      _ = T.card * (2 * (bchksZCap6399 + 1) * bchksXCap6399) := by simp
      _ ≤ UniversalX0Avoidance6399.M *
          (2 * (bchksZCap6399 + 1) * bchksXCap6399) := by
        exact Nat.mul_le_mul_right _ (by simpa [T] using hOuterCard)
      _ = primitiveObstructionBudget := by
        norm_num [UniversalX0Avoidance6399.M, bchksZCap6399,
          bchksXCap6399, primitiveObstructionBudget]
  have hfactorSum : (∑ r ∈ T,
      (factorXObstruction (r : TriPoly)).natDegree) ≤
      UniversalX0Avoidance6399.xObstructionBudget := by
    have hb :=
      UniversalX0Avoidance6399.positive_outer_factorXObstruction_sum_le_6399
        Q hQ hQdeg hX hlead
    dsimp only at hb
    rw [← Finset.sum_attach] at hb
    simpa only [T, Outer] using hb
  have hdegree : (∑ r ∈ T, (combined r).natDegree) < Fintype.card F := by
    have hle : (∑ r ∈ T, (combined r).natDegree) ≤
        primitiveObstructionBudget +
          UniversalX0Avoidance6399.xObstructionBudget := by
      calc
        (∑ r ∈ T, (combined r).natDegree) ≤
            ∑ r ∈ T, ((cert r).obstruction.natDegree +
              (factorXObstruction (r : TriPoly)).natDegree) := by
          apply Finset.sum_le_sum
          intro r hr
          exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add
            (by simpa [primRat] using
              (Polynomial.natDegree_map_le (p := (cert r).obstruction)
                (f := algebraMap F (RatFunc F))))
            (by simpa [factorRat] using
              (Polynomial.natDegree_map_le
                (p := factorXObstruction (r : TriPoly)) (f := g))))
        _ = (∑ r ∈ T, (cert r).obstruction.natDegree) +
            ∑ r ∈ T, (factorXObstruction (r : TriPoly)).natDegree := by
          rw [Finset.sum_add_distrib]
        _ ≤ primitiveObstructionBudget +
            UniversalX0Avoidance6399.xObstructionBudget :=
          Nat.add_le_add hprimSum hfactorSum
    have hbudget : primitiveObstructionBudget +
        UniversalX0Avoidance6399.xObstructionBudget = totalX0ObstructionBudget := by
      norm_num [primitiveObstructionBudget, UniversalX0Avoidance6399.xObstructionBudget,
        totalX0ObstructionBudget]
    rw [hbudget] at hle
    exact hle.trans_lt totalX0ObstructionBudget_lt_field
  obtain ⟨x₀, hx⟩ := exists_base_point_avoiding_ratfunc_polynomials
    T combined hcombined hdegree
  refine ⟨x₀, ?_⟩
  intro R hR
  let r : ↥Outer := ⟨R, by simpa [Outer] using hR⟩
  have hprod := hx r (by simpa [T] using r.property)
  have hprod' : Polynomial.eval (algebraMap F (RatFunc F) x₀) (primRat r) *
      Polynomial.eval (algebraMap F (RatFunc F) x₀) (factorRat r) ≠ 0 := by
    simpa [combined, Polynomial.eval_mul] using hprod
  have hpRat : Polynomial.eval (algebraMap F (RatFunc F) x₀) (primRat r) ≠ 0 :=
    left_ne_zero_of_mul hprod'
  have hoRat : Polynomial.eval (algebraMap F (RatFunc F) x₀) (factorRat r) ≠ 0 :=
    right_ne_zero_of_mul hprod'
  have hp : Polynomial.eval x₀ (cert r).obstruction ≠ 0 := by
    intro hp0
    apply hpRat
    simpa [primRat, Polynomial.eval_map, hp0]
  have ho : Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 :=
    eval_C_ne_zero_of_ratfunc_map_eval_ne_zero _ _ (by
      change Polynomial.eval (algebraMap F (RatFunc F) x₀)
        ((factorXObstruction R).map g) ≠ 0
      simpa only [factorRat, r] using hoRat)
  have hlead0 : Polynomial.eval (Polynomial.C x₀) R.leadingCoeff ≠ 0 := by
    intro hz
    apply ho
    rw [factorXObstruction, Polynomial.eval_mul, hz, zero_mul]
  have hraw : Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) ≠ 0 := by
    intro hz
    apply ho
    rw [factorXObstruction, Polynomial.eval_mul, hz, mul_zero]
  have hR0 : triSpecializeX R x₀ ≠ 0 := by
    intro hz
    apply hlead0
    have hc := congrArg
      (fun B : Polynomial (Polynomial F) => B.coeff R.natDegree) hz
    simpa only [triSpecializeX, Polynomial.coeff_map, Polynomial.coeff_zero,
      Polynomial.coe_evalRingHom, Polynomial.leadingCoeff] using hc
  have hdeg : (triSpecializeX R x₀).natDegree = R.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (Polynomial.evalRingHom (Polynomial.C x₀)) hlead0
  exact ⟨(cert r).property x₀ hp, ho, hR0, hdeg, hraw⟩

end UniversalPrimitiveX0Avoidance6399

end ProximityPrize.SubmissionLower
