import ProximityPrize.SubmissionLower.BCHKSFactorXDegree

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open scoped BigOperators

set_option maxHeartbeats 2000000

namespace UniversalX0Avoidance6399

local instance concreteUniversalChar :
    CharP IRSProfile.Field 2130706433 :=
  charP_of_injective_algebraMap' KoalaBear.Field 2130706433

def DX : ℕ := 692001142
def M : ℕ := 5279
def xObstructionBudget : ℕ := 14612296114472

/-- Generic first-factor aggregation. Positivity bounds the number of outer
factors by their total `Y`-degree, so the `+2` in each obstruction costs only
one additional copy of the same total-degree budget. -/
theorem sum_factorXObstruction_natDegree_le_four_mul
    {F ρ : Type} [Field F] [DecidableEq ρ]
    (Rs : Finset ρ)
    (R : ρ → Polynomial (Polynomial (Polynomial F)))
    (DX M : ℕ)
    (hpos : ∀ r ∈ Rs, 0 < (R r).natDegree)
    (hsum : (∑ r ∈ Rs, (R r).natDegree) ≤ M)
    (hdegree : ∀ r ∈ Rs,
      (factorXObstruction (R r)).natDegree ≤
        (2 * (R r).natDegree + 2) * DX) :
    (∑ r ∈ Rs, (factorXObstruction (R r)).natDegree) ≤ 4 * DX * M := by
  have hcard : Rs.card ≤ ∑ r ∈ Rs, (R r).natDegree := by
    calc
      Rs.card = Rs.card • (1 : ℕ) := by simp
      _ ≤ ∑ r ∈ Rs, (R r).natDegree :=
        Finset.card_nsmul_le_sum Rs (fun r => (R r).natDegree) 1 hpos
  have hsumFormula : ∀ T : Finset ρ,
      (∑ r ∈ T, (2 * (R r).natDegree + 2) * DX) =
        2 * DX * ((∑ r ∈ T, (R r).natDegree) + T.card) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert r T hr ih =>
        simp only [Finset.sum_insert hr, Finset.card_insert_of_notMem hr]
        rw [ih]
        ring
  calc
    (∑ r ∈ Rs, (factorXObstruction (R r)).natDegree) ≤
        ∑ r ∈ Rs, (2 * (R r).natDegree + 2) * DX :=
      Finset.sum_le_sum hdegree
    _ = 2 * DX * ((∑ r ∈ Rs, (R r).natDegree) + Rs.card) := by
      exact hsumFormula Rs
    _ ≤ 2 * DX * (M + M) := by
      exact Nat.mul_le_mul_left (2 * DX) (Nat.add_le_add hsum (hcard.trans hsum))
    _ = 4 * DX * M := by ring

/-- The positive first factors of `Q` have total outer degree at most `M`. -/
theorem positive_outer_factor_degree_sum_le
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (M : ℕ)
    (hQdeg : Q.natDegree ≤ M) :
    let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R => 0 < R.natDegree)
    (∑ R ∈ Rs, R.natDegree) ≤ M := by
  dsimp only
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)).trans
    ((normalizedFactors_toFinset_sum_natDegree_le Q hQ).trans hQdeg)

/-- Exact 6399 aggregation for all positive first factors. The two exposed
support hypotheses are the narrow interface needed from the new interpolation
factor-cap module. -/
theorem positive_outer_factorXObstruction_sum_le_6399
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hQ : Q ≠ 0) (hQdeg : Q.natDegree ≤ M)
    (hX : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      degreeX (mapZToRatFunc R) ≤ DX)
    (hlead : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.leadingCoeff.natDegree ≤ DX) :
    let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R => 0 < R.natDegree)
    (∑ R ∈ Rs, (factorXObstruction R).natDegree) ≤ xObstructionBudget := by
  classical
  dsimp only
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun R => 0 < R.natDegree)
  have hsum : (∑ R ∈ Rs, R.natDegree) ≤ M := by
    simpa [Rs] using positive_outer_factor_degree_sum_le Q hQ M hQdeg
  have hdeg : ∀ R ∈ Rs, (factorXObstruction R).natDegree ≤
      (2 * R.natDegree + 2) * DX := by
    intro R hR
    have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hR).1
    exact factorXObstruction_natDegree_le R DX (hX R hRQ) (hlead R hRQ)
  have h := sum_factorXObstruction_natDegree_le_four_mul Rs id DX M
    (by intro R hR; exact (Finset.mem_filter.mp hR).2) hsum (by simpa using hdeg)
  change (∑ R ∈ Rs, (factorXObstruction R).natDegree) ≤ xObstructionBudget
  norm_num [DX, M, xObstructionBudget] at h ⊢
  exact h

theorem xObstructionBudget_lt_field :
    xObstructionBudget < Fintype.card IRSProfile.Field := by
  rw [CompPoly.Extension.Ext.card_ext]
  norm_num [xObstructionBudget, IRSProfile.Field, KoalaBear.Ext6,
    KoalaBear.fieldSize]

/-- A nonzero rational-function obstruction at the embedded constant `x`
forces the original `F[Z][X]` obstruction to remain nonzero after `X=x`. -/
private theorem eval_C_ne_zero_of_ratfunc_map_eval_ne_zero
    {F : Type*} [Field F] (P : Polynomial (Polynomial F)) (x : F)
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

/-- Concrete simultaneous Taylor-center selection for the 6399 parameters.
No `<852` hypothesis and no `10^12` budget occur. The conclusion exposes
the exact leading/slope facts consumed by factorization and the universal
implicit-numerator specialization. -/
theorem exists_x0_avoiding_positive_factor_obstructions_6399
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hQ : Q ≠ 0) (hQdeg : Q.natDegree ≤ M)
    (hX : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      degreeX (mapZToRatFunc R) ≤ DX)
    (hlead : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.leadingCoeff.natDegree ≤ DX) :
    ∃ x₀ : IRSProfile.Field,
      ∀ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) ≠ 0 := by
  classical
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun R => 0 < R.natDegree)
  let g : Polynomial IRSProfile.Field →+* RatFunc IRSProfile.Field := algebraMap _ _
  let obsRat : Polynomial (Polynomial (Polynomial IRSProfile.Field)) →
      Polynomial (RatFunc IRSProfile.Field) := fun R => (factorXObstruction R).map g
  have hobs : ∀ R ∈ Rs, factorXObstruction R ≠ 0 := by
    intro R hR
    have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hR).1
    have hRirr :=
      (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
    have hRpos : 0 < R.natDegree := (Finset.mem_filter.mp hR).2
    have hRdeg : R.natDegree ≤ Q.natDegree :=
      Polynomial.natDegree_le_of_dvd
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hQ
    have hRlt : R.natDegree < 2130706433 := by
      exact lt_of_le_of_lt (hRdeg.trans hQdeg) (by norm_num [M])
    apply _root_.mul_ne_zero
    · exact Polynomial.leadingCoeff_ne_zero.mpr hRirr.ne_zero
    · exact rawSepResultant_ne_zero_of_irreducible 2130706433 R hRirr hRpos hRlt
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hobsRat : ∀ R ∈ Rs, obsRat R ≠ 0 := by
    intro R hR
    exact (Polynomial.map_ne_zero_iff hg).mpr (hobs R hR)
  have hdegRaw : (∑ R ∈ Rs, (factorXObstruction R).natDegree) ≤
      xObstructionBudget := by
    simpa [Rs] using positive_outer_factorXObstruction_sum_le_6399
      Q hQ hQdeg hX hlead
  have hdeg : (∑ R ∈ Rs, (obsRat R).natDegree) < Fintype.card IRSProfile.Field := by
    have heq : (∑ R ∈ Rs, (obsRat R).natDegree) =
        ∑ R ∈ Rs, (factorXObstruction R).natDegree := by
      apply Finset.sum_congr rfl
      intro R hR
      exact Polynomial.natDegree_map_eq_of_injective hg _
    rw [heq]
    exact hdegRaw.trans_lt xObstructionBudget_lt_field
  obtain ⟨x₀, hxRat⟩ := exists_base_point_avoiding_ratfunc_polynomials
    Rs obsRat hobsRat hdeg
  refine ⟨x₀, ?_⟩
  intro R hR
  have hxObs : Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 :=
    eval_C_ne_zero_of_ratfunc_map_eval_ne_zero _ _ (hxRat R hR)
  have hxLead : Polynomial.eval (Polynomial.C x₀) R.leadingCoeff ≠ 0 := by
    intro hz
    apply hxObs
    rw [factorXObstruction, Polynomial.eval_mul, hz, zero_mul]
  have hxRaw : Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) ≠ 0 := by
    intro hz
    apply hxObs
    rw [factorXObstruction, Polynomial.eval_mul, hz, mul_zero]
  have hxR : triSpecializeX R x₀ ≠ 0 := by
    intro hzero
    apply hxLead
    have hcoeff := congrArg
      (fun P : Polynomial (Polynomial IRSProfile.Field) => P.coeff R.natDegree) hzero
    simpa only [triSpecializeX, Polynomial.coeff_map, Polynomial.coeff_zero,
      Polynomial.coe_evalRingHom, Polynomial.leadingCoeff] using hcoeff
  have hxdeg : (triSpecializeX R x₀).natDegree = R.natDegree := by
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (Polynomial.evalRingHom (Polynomial.C x₀)) hxLead
  exact ⟨hxObs, hxR, hxdeg, hxRaw⟩

end UniversalX0Avoidance6399

end ProximityPrize.SubmissionLower
