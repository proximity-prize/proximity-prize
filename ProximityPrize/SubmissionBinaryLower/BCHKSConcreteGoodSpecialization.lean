import ProximityPrize.SubmissionBinaryLower.BCHKSFactorPigeon
import ProximityPrize.SubmissionBinaryLower.BCHKSSeparableFactors
import ProximityPrize.SubmissionBinaryLower.BCHKSParameters
import ProximityPrize.SubmissionBinaryLower.BCHKSConcreteGS

namespace ProximityPrize.SubmissionBinaryLower

open Polynomial Polynomial.Bivariate
open scoped BigOperators

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

/-- First invert the `Z`-polynomials, leaving `X` and `Y` polynomial. -/
noncomputable def mapZToRatFunc {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial (RatFunc F)) :=
  R.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))

/-- The `Y`-discriminant after passing from `F[Z]` to `F(Z)`, as a
polynomial in `X`. -/
noncomputable def ratDiscr {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) : Polynomial (RatFunc F) :=
  (mapZToRatFunc R).discr


/-- Map the raw `Y`-discriminant (a polynomial in `X` over `F[Z]`) into
`F(Z)[X]`.  Unlike `ratDiscr`, this definition makes coefficient-map
injectivity immediate. -/
noncomputable def rawDiscrRat {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) : Polynomial (RatFunc F) :=
  R.discr.map (algebraMap F[X] (RatFunc F))


/-- Root counting restricted to the embedded constants `C x`, rather than all
points of the rational-function field. -/
theorem exists_base_point_avoiding_ratfunc_polynomials
    {F ρ : Type} [Field F] [Fintype F] [DecidableEq ρ]
    (T : Finset ρ) (p : ρ → Polynomial (RatFunc F))
    (hne : ∀ r ∈ T, p r ≠ 0)
    (hdeg : (∑ r ∈ T, (p r).natDegree) < Fintype.card F) :
    ∃ x₀ : F, ∀ r ∈ T, Polynomial.eval (algebraMap F (RatFunc F) x₀) (p r) ≠ 0 := by
  classical
  let P : Polynomial (RatFunc F) := ∏ r ∈ T, p r
  have hPne : P ≠ 0 := by
    change (∏ r ∈ T, p r) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    exact hne
  have hPdeg : P.natDegree < Fintype.card F :=
    (Polynomial.natDegree_prod_le T p).trans_lt hdeg
  by_contra hgood
  push Not at hgood
  have hPeval : ∀ x : F, P.eval (algebraMap F (RatFunc F) x) = 0 := by
    intro x
    obtain ⟨r, hr, hz⟩ := hgood x
    change Polynomial.eval (algebraMap F (RatFunc F) x) (∏ r ∈ T, p r) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hr hz
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    P (FaithfulSMul.algebraMap_injective F (RatFunc F)) hPeval hPdeg
  exact hPne hzero


/-- Union of the roots of a finite family of nonzero obstruction
polynomials. -/
noncomputable def badRootUnion {F ρ : Type} [Field F] [DecidableEq F]
    (T : Finset ρ) (p : ρ → F[X]) : Finset F :=
  T.biUnion fun r => (p r).roots.toFinset

/-- The bad-root union costs at most the sum of the obstruction degrees. -/
theorem badRootUnion_card_le_sum_natDegree
    {F ρ : Type} [Field F] [DecidableEq F] [DecidableEq ρ]
    (T : Finset ρ) (p : ρ → F[X]) (hne : ∀ r ∈ T, p r ≠ 0) :
    (badRootUnion T p).card ≤ ∑ r ∈ T, (p r).natDegree := by
  classical
  calc
    (badRootUnion T p).card ≤ ∑ r ∈ T, (p r).roots.toFinset.card := by
      unfold badRootUnion
      exact Finset.card_biUnion_le
    _ ≤ ∑ r ∈ T, (p r).roots.card := by
      apply Finset.sum_le_sum
      intro r hr
      exact Multiset.toFinset_card_le _
    _ ≤ ∑ r ∈ T, (p r).natDegree := by
      apply Finset.sum_le_sum
      intro r hr
      exact Polynomial.card_roots' (p r)

/-- Outside the union, every obstruction evaluates nontrivially. -/
theorem eval_ne_zero_of_not_mem_badRootUnion
    {F ρ : Type} [Field F] [DecidableEq F] [DecidableEq ρ]
    (T : Finset ρ) (p : ρ → F[X]) (hne : ∀ r ∈ T, p r ≠ 0)
    {z : F} (hz : z ∉ badRootUnion T p) :
    ∀ r ∈ T, Polynomial.eval z (p r) ≠ 0 := by
  intro r hr hzero
  apply hz
  unfold badRootUnion
  rw [Finset.mem_biUnion]
  refine ⟨r, hr, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hne r hr)]
  exact hzero

/-- Intersecting an arbitrary challenge set with the global bad union cannot
increase its cardinality. -/
theorem inter_badRootUnion_card_le_budget
    {F ρ : Type} [Field F] [DecidableEq F] [DecidableEq ρ]
    (S : Finset F) (T : Finset ρ) (p : ρ → F[X])
    (hne : ∀ r ∈ T, p r ≠ 0)
    (hdeg : (∑ r ∈ T, (p r).natDegree) ≤ bchksBadBudget) :
    (S ∩ badRootUnion T p).card ≤ bchksBadBudget := by
  exact (Finset.card_le_card Finset.inter_subset_right).trans
    ((badRootUnion_card_le_sum_natDegree T p hne).trans hdeg)

/-- The very coarse all-factor accounting is already far below the reserved
budget.  It allows 6902 factors, one degree-21907324 survival obstruction and one
`(2·6902-1)·21907324` resultant/discriminant obstruction per factor. -/
theorem crude_concrete_bad_degree_budget :
    6902 * (21907324 + (2 * 6902 - 1) * 21907324) ≤ bchksBadBudget := by
  norm_num [bchksBadBudget]


/-- Turning the per-factor coarse estimate into the explicit global budget. -/
theorem rat_discriminants_sum_degree_le_badBudget
    {ρ : Type} [DecidableEq ρ]
    (T : Finset ρ)
    (R : ρ → Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.BinaryIRSProfile.Field)))
    (hcard : T.card ≤ 6902)
    (hdeg : ∀ r ∈ T,
      (ratDiscr (R r)).natDegree ≤ 21907324 + (2 * 6902 - 1) * 21907324) :
    (∑ r ∈ T, (ratDiscr (R r)).natDegree) ≤ bchksBadBudget := by
  calc
    (∑ r ∈ T, (ratDiscr (R r)).natDegree) ≤
        ∑ _r ∈ T, (21907324 + (2 * 6902 - 1) * 21907324) :=
      Finset.sum_le_sum hdeg
    _ = T.card * (21907324 + (2 * 6902 - 1) * 21907324) := by simp
    _ ≤ 6902 * (21907324 + (2 * 6902 - 1) * 21907324) := by
      exact Nat.mul_le_mul_right _ hcard
    _ ≤ bchksBadBudget := crude_concrete_bad_degree_budget

/-- The raw padded separability resultant of a positive-degree irreducible
factor. -/
noncomputable def rawSepResultant {A : Type} [CommRing A]
    (R : A[X]) : A :=
  Polynomial.resultant R R.derivative R.natDegree (R.natDegree - 1)

/-- No monicity assumption is needed: pass a primitive irreducible to the full
fraction field, use separability (nonzero derivative), and descend nonvanishing
by injectivity. The padded degree `natDegree - 1` is handled by
`resultant_add_right_deg`, so the derivative may have smaller degree, as it
does in characteristic two. -/
theorem rawSepResultant_ne_zero_of_irreducible
    {A : Type} [CommRing A] [IsDomain A] [IsGCDMonoid A]
    (R : A[X]) (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hsep : R.derivative ≠ 0) : rawSepResultant R ≠ 0 := by
  let K := FractionRing A
  let f : A →+* K := algebraMap A K
  let RK : K[X] := R.map f
  have hf : Function.Injective f := IsFractionRing.injective A K
  have hRKdeg : RK.natDegree = R.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf R
  have hirrK : Irreducible RK := by
    exact (hirr.isPrimitive (ne_of_gt hpos)).irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hsepK : RK.derivative ≠ 0 := by
    dsimp [RK]
    rw [Polynomial.derivative_map]
    exact (Polynomial.map_ne_zero_iff hf).mpr hsep
  have hcop := irreducible_isCoprime_derivative_of_derivative_ne_zero RK hirrK hsepK
  have hresK : RK.resultant RK.derivative ≠ 0 :=
    Polynomial.resultant_ne_zero RK RK.derivative hcop
  have hdle : RK.derivative.natDegree ≤ RK.natDegree - 1 :=
    Polynomial.natDegree_derivative_le RK
  have hfixedK : RK.resultant RK.derivative R.natDegree (R.natDegree - 1) ≠ 0 := by
    have hsplit : R.natDegree - 1 =
        RK.derivative.natDegree + (RK.natDegree - 1 - RK.derivative.natDegree) := by
      omega
    rw [hsplit, ← hRKdeg, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl,
      Polynomial.coeff_natDegree]
    exact mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hirrK.ne_zero)) hresK
  intro hraw
  apply hfixedK
  dsimp [RK]
  rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
  unfold rawSepResultant at hraw
  rw [hraw]
  exact map_zero _

/-- Fixed-degree common-root vanishing.  This padded form remains valid when
specialization lowers one of the degrees. -/
theorem fixed_resultant_eq_zero_of_common_root
    {F : Type} [Field F] {P H : F[X]} {m n : ℕ} {y : F}
    (hPdeg : P.natDegree ≤ m) (hHdeg : H.natDegree ≤ n)
    (hsize : 0 < m + n) (hP : P.eval y = 0) (hH : H.eval y = 0) :
    Polynomial.resultant P H m n = 0 := by
  by_cases hne : P ≠ 0 ∨ H ≠ 0
  · have hstd : Polynomial.resultant P H = 0 := by
      rw [Polynomial.resultant_eq_zero_iff]
      refine ⟨hne, ?_⟩
      rintro ⟨a, b, hab⟩
      have heval := congrArg (fun q : F[X] => q.eval y) hab
      simp [Polynomial.eval_add, Polynomial.eval_mul, hP, hH] at heval
    have hm : P.natDegree + (m - P.natDegree) = m := Nat.add_sub_of_le hPdeg
    have hn : H.natDegree + (n - H.natDegree) = n := Nat.add_sub_of_le hHdeg
    rw [← hm, ← hn, Polynomial.resultant_add_left_deg]
    · rw [Polynomial.resultant_add_right_deg]
      · simp [hstd]
      · exact le_rfl
    · exact le_rfl
  · push Not at hne
    rcases hne with ⟨rfl, rfl⟩
    rcases m with _ | m <;> rcases n with _ | n <;> simp_all

/-- A nonzero specialized fixed resultant certifies that every rational root
is simple.  This is the pointwise derivative conclusion used after removing
`Bad`. -/
theorem simple_root_of_fixed_resultant_eval_ne_zero
    {F : Type} [Field F] (B : F[X][Y]) (z y : F)
    (hpos : 0 < B.natDegree)
    (hres : Polynomial.eval z
      (Polynomial.resultant B B.derivative B.natDegree (B.natDegree - 1)) ≠ 0)
    (hy : Polynomial.eval y (biSpecializeZ B z) = 0) :
    Polynomial.eval y (biSpecializeZ B.derivative z) ≠ 0 := by
  intro hyder
  apply hres
  rw [show Polynomial.eval z
      (Polynomial.resultant B B.derivative B.natDegree (B.natDegree - 1)) =
      Polynomial.resultant (biSpecializeZ B z) (biSpecializeZ B.derivative z)
        B.natDegree (B.natDegree - 1) by simp [biSpecializeZ]]
  apply fixed_resultant_eq_zero_of_common_root
  · exact Polynomial.natDegree_map_le
  · exact Polynomial.natDegree_map_le.trans (Polynomial.natDegree_derivative_le B)
  · omega
  · exact hy
  · exact hyder

/-- Package the two finite-union conclusions.  Callers instantiate `p` with a
survival coefficient for `Q` and every factor, plus each fixed
resultant/discriminant. -/
theorem exists_concrete_bad_union
    {ρ : Type} [DecidableEq ρ]
    (S : Finset ProximityPrize.Benchmark.BinaryIRSProfile.Field)
    (T : Finset ρ)
    (p : ρ → Polynomial ProximityPrize.Benchmark.BinaryIRSProfile.Field)
    (hne : ∀ r ∈ T, p r ≠ 0)
    (hdeg : (∑ r ∈ T, (p r).natDegree) ≤ bchksBadBudget) :
    ∃ Bad : Finset ProximityPrize.Benchmark.BinaryIRSProfile.Field,
      (S ∩ Bad).card ≤ bchksBadBudget ∧
      ∀ z ∉ Bad, ∀ r ∈ T, Polynomial.eval z (p r) ≠ 0 := by
  refine ⟨badRootUnion T p, inter_badRootUnion_card_le_budget S T p hne hdeg, ?_⟩
  intro z hz
  exact eval_ne_zero_of_not_mem_badRootUnion T p hne hz


/-- The two raw `X`-obstructions attached to a factor are combined into one:
its leading `Y`-coefficient and its separability resultant. -/
noncomputable def factorXObstruction {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial F) :=
  R.leadingCoeff * rawSepResultant R

end ProximityPrize.SubmissionBinaryLower
