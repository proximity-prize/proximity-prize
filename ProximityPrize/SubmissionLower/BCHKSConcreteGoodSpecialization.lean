import ProximityPrize.SubmissionLower.BCHKSFactorPigeon
import ProximityPrize.SubmissionLower.BCHKSSeparableFactors
import ProximityPrize.SubmissionLower.BCHKSParameters
import ProximityPrize.SubmissionLower.BCHKSConcreteGS

namespace ProximityPrize.SubmissionLower

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

local instance concreteGoodSpecChar :
    CharP ProximityPrize.Benchmark.IRSProfile.Field 2130706433 :=
  charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- A monic irreducible positive-`Y` factor with `Y`-degree below 852 has
nonzero raw discriminant.  The cap hypotheses are explicit so the factor-cap
API can discharge them directly. -/
theorem concrete_monic_factor_discr_ne_zero
    (R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hmonic : R.Monic) (hirr : Irreducible R)
    (hpos : 0 < R.natDegree) (hdeg : R.natDegree < 852) : R.discr ≠ 0 := by
  let A := Polynomial (Polynomial ProximityPrize.Benchmark.IRSProfile.Field)
  let K := FractionRing A
  have hirrK : Irreducible (R.map (algebraMap A K)) :=
    hmonic.irreducible_iff_irreducible_map_fraction_map.mp hirr
  apply monic_discr_ne_zero_of_fraction_irreducible
    (A := A) (K := K) 2130706433 R hmonic hirrK hpos
  omega

/-- The rational-function image of the raw discriminant is nonzero and keeps
exactly its `X`-degree. -/
theorem rawDiscrRat_ne_zero_and_natDegree
    (R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hmonic : R.Monic) (hirr : Irreducible R)
    (hpos : 0 < R.natDegree) (hdeg : R.natDegree < 852) :
    rawDiscrRat R ≠ 0 ∧ (rawDiscrRat R).natDegree = R.discr.natDegree := by
  let f : Polynomial ProximityPrize.Benchmark.IRSProfile.Field →+*
      RatFunc ProximityPrize.Benchmark.IRSProfile.Field :=
    algebraMap _ _
  have hf : Function.Injective f := IsFractionRing.injective _ _
  constructor
  · exact (Polynomial.map_ne_zero_iff hf).mpr
      (concrete_monic_factor_discr_ne_zero R hmonic hirr hpos hdeg)
  · exact Polynomial.natDegree_map_eq_of_injective hf R.discr

private theorem raw_discr_specialization_ne_zero_of_rat_eval
    {F : Type} [Field F] (P : Polynomial (Polynomial F)) (x : F)
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


/-- Full first-stage factor theorem with the factor cap assumptions exposed:
one base point leaves every raw discriminant nonzero after specializing `X`. -/
theorem exists_x0_raw_factor_discriminants
    {ρ : Type} [DecidableEq ρ]
    (T : Finset ρ)
    (R : ρ → Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hmonic : ∀ r ∈ T, (R r).Monic)
    (hirr : ∀ r ∈ T, Irreducible (R r))
    (hpos : ∀ r ∈ T, 0 < (R r).natDegree)
    (hY : ∀ r ∈ T, (R r).natDegree < 852)
    (hbudget : (∑ r ∈ T, (R r).discr.natDegree) ≤ bchksBadBudget) :
    ∃ x₀ : ProximityPrize.Benchmark.IRSProfile.Field,
      ∀ r ∈ T,
        Polynomial.eval (Polynomial.C x₀) (R r).discr ≠ 0 := by
  have hne : ∀ r ∈ T, rawDiscrRat (R r) ≠ 0 := by
    intro r hr
    exact (rawDiscrRat_ne_zero_and_natDegree (R r)
      (hmonic r hr) (hirr r hr) (hpos r hr) (hY r hr)).1
  have hdeg : (∑ r ∈ T, (rawDiscrRat (R r)).natDegree) <
      Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := by
    have heq : (∑ r ∈ T, (rawDiscrRat (R r)).natDegree) =
        ∑ r ∈ T, (R r).discr.natDegree := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (rawDiscrRat_ne_zero_and_natDegree (R r)
        (hmonic r hr) (hirr r hr) (hpos r hr) (hY r hr)).2
    rw [heq]
    exact hbudget.trans_lt bchksBadBudget_lt_field
  obtain ⟨x₀, hx₀⟩ := exists_base_point_avoiding_ratfunc_polynomials
    T (fun r => rawDiscrRat (R r)) hne hdeg
  refine ⟨x₀, ?_⟩
  intro r hr
  exact raw_discr_specialization_ne_zero_of_rat_eval (R r).discr x₀ (hx₀ r hr)

/-- Concrete wrapper using the reserved `6.8·10^13` bad-specialization
budget and the proven cardinal lower bound for the sextic field. -/
theorem exists_concrete_x0_avoiding_rat_discriminants
    {ρ : Type} [DecidableEq ρ]
    (T : Finset ρ)
    (R : ρ → Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hne : ∀ r ∈ T, ratDiscr (R r) ≠ 0)
    (hdeg : (∑ r ∈ T, (ratDiscr (R r)).natDegree) ≤ bchksBadBudget) :
    ∃ x₀ : ProximityPrize.Benchmark.IRSProfile.Field,
      ∀ r ∈ T,
        Polynomial.eval (algebraMap ProximityPrize.Benchmark.IRSProfile.Field
          (RatFunc ProximityPrize.Benchmark.IRSProfile.Field) x₀) (ratDiscr (R r)) ≠ 0 := by
  apply exists_base_point_avoiding_ratfunc_polynomials T (fun r => ratDiscr (R r)) hne
  exact hdeg.trans_lt bchksBadBudget_lt_field

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
budget.  It allows 852 factors, one degree-519143 survival obstruction and one
`(2·852-1)·519143` resultant/discriminant obstruction per factor. -/
theorem crude_concrete_bad_degree_budget :
    852 * (519143 + (2 * 852 - 1) * 519143) ≤ bchksBadBudget := by
  norm_num [bchksBadBudget]


/-- Turning the per-factor coarse estimate into the explicit global budget. -/
theorem rat_discriminants_sum_degree_le_badBudget
    {ρ : Type} [DecidableEq ρ]
    (T : Finset ρ)
    (R : ρ → Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hcard : T.card ≤ 852)
    (hdeg : ∀ r ∈ T,
      (ratDiscr (R r)).natDegree ≤ 519143 + (2 * 852 - 1) * 519143) :
    (∑ r ∈ T, (ratDiscr (R r)).natDegree) ≤ bchksBadBudget := by
  calc
    (∑ r ∈ T, (ratDiscr (R r)).natDegree) ≤
        ∑ _r ∈ T, (519143 + (2 * 852 - 1) * 519143) :=
      Finset.sum_le_sum hdeg
    _ = T.card * (519143 + (2 * 852 - 1) * 519143) := by simp
    _ ≤ 852 * (519143 + (2 * 852 - 1) * 519143) := by
      exact Nat.mul_le_mul_right _ hcard
    _ ≤ bchksBadBudget := crude_concrete_bad_degree_budget

/-- Concrete first-stage result requested by the specialization argument:
all mapped discriminants survive at one base-field point. -/
theorem exists_concrete_x0_of_factor_discriminant_bounds
    {ρ : Type} [DecidableEq ρ]
    (T : Finset ρ)
    (R : ρ → Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hcard : T.card ≤ 852)
    (hne : ∀ r ∈ T, ratDiscr (R r) ≠ 0)
    (hdeg : ∀ r ∈ T,
      (ratDiscr (R r)).natDegree ≤ 519143 + (2 * 852 - 1) * 519143) :
    ∃ x₀ : ProximityPrize.Benchmark.IRSProfile.Field,
      ∀ r ∈ T,
        Polynomial.eval
          (algebraMap ProximityPrize.Benchmark.IRSProfile.Field
            (RatFunc ProximityPrize.Benchmark.IRSProfile.Field) x₀)
          (ratDiscr (R r)) ≠ 0 := by
  apply exists_concrete_x0_avoiding_rat_discriminants T R hne
  exact rat_discriminants_sum_degree_le_badBudget T R hcard hdeg


/-- The raw padded separability resultant of a positive-degree irreducible
factor. -/
noncomputable def rawSepResultant {A : Type} [CommRing A]
    (R : A[X]) : A :=
  Polynomial.resultant R R.derivative R.natDegree (R.natDegree - 1)

/-- No monicity assumption is needed: pass a primitive irreducible to the full
fraction field, use degree below the characteristic, and descend nonvanishing
by injectivity. -/
theorem rawSepResultant_ne_zero_of_irreducible
    {A : Type} [CommRing A] [IsDomain A] [IsGCDMonoid A]
    (p : ℕ) [CharP A p] (R : A[X])
    (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hlt : R.natDegree < p) : rawSepResultant R ≠ 0 := by
  let K := FractionRing A
  let f : A →+* K := algebraMap A K
  let RK : K[X] := R.map f
  letI : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective A K) p
  have hf : Function.Injective f := IsFractionRing.injective A K
  have hRKdeg : RK.natDegree = R.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf R
  have hirrK : Irreducible RK := by
    exact (hirr.isPrimitive (ne_of_gt hpos)).irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hposK : 0 < RK.natDegree := by simpa [hRKdeg]
  have hltK : RK.natDegree < p := by simpa [hRKdeg]
  have hresK : RK.resultant RK.derivative ≠ 0 :=
    irreducible_resultant_derivative_ne_zero_of_natDegree_lt_char
      p RK hirrK hposK hltK
  have hddegK : RK.derivative.natDegree = RK.natDegree - 1 := by
    apply le_antisymm (Polynomial.natDegree_derivative_le RK)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.coeff_derivative]
    have hs : RK.natDegree - 1 + 1 = RK.natDegree := by omega
    rw [hs]
    have hcastSucc : ((RK.natDegree - 1 : ℕ) : K) + 1 = (RK.natDegree : K) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun z : ℕ => (z : K)) hs
    rw [hcastSucc, Polynomial.coeff_natDegree]
    have hcast : (RK.natDegree : K) ≠ 0 := by
      intro hz
      exact (Nat.not_dvd_of_pos_of_lt hposK hltK)
        ((CharP.cast_eq_zero_iff K p RK.natDegree).mp hz)
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hirrK.ne_zero) hcast
  have hfixedK : RK.resultant RK.derivative R.natDegree (R.natDegree - 1) ≠ 0 := by
    simpa [hRKdeg, hddegK] using hresK
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
    (S : Finset ProximityPrize.Benchmark.IRSProfile.Field)
    (T : Finset ρ)
    (p : ρ → Polynomial ProximityPrize.Benchmark.IRSProfile.Field)
    (hne : ∀ r ∈ T, p r ≠ 0)
    (hdeg : (∑ r ∈ T, (p r).natDegree) ≤ bchksBadBudget) :
    ∃ Bad : Finset ProximityPrize.Benchmark.IRSProfile.Field,
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

/-- Conditional-on-caps integration theorem.  This is deliberately stated
with the two aggregate degree estimates exposed; the factor-cap theorem plugs
into precisely `hxBudget` and `hzBudget`. -/
theorem concrete_good_specialization_of_factor_caps
    {ρ : Type} [DecidableEq ρ]
    (Q : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (T : Finset ρ)
    (R : ρ → Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hirr : ∀ r ∈ T, Irreducible (R r))
    (hpos : ∀ r ∈ T, 0 < (R r).natDegree)
    (hY : ∀ r ∈ T, (R r).natDegree < 852)
    (jQ aQ : ℕ)
    (hcQ : (Q.coeff jQ).coeff aQ ≠ 0)
    (hxBudget : (∑ r ∈ T, (factorXObstruction (R r)).natDegree) ≤
      bchksBadBudget)
    (hzBudget : ∀ x : ProximityPrize.Benchmark.IRSProfile.Field,
      ((Q.coeff jQ).coeff aQ).natDegree +
        ∑ r ∈ T,
          (Polynomial.eval (Polynomial.C x) (factorXObstruction (R r))).natDegree ≤
        bchksBadBudget)
    (S : Finset ProximityPrize.Benchmark.IRSProfile.Field) :
    ∃ x₀ : ProximityPrize.Benchmark.IRSProfile.Field,
      ∃ Bad : Finset ProximityPrize.Benchmark.IRSProfile.Field,
        (S ∩ Bad).card ≤ bchksBadBudget ∧
        (∀ r ∈ T, triSpecializeX (R r) x₀ ≠ 0) ∧
        (∀ z ∉ Bad, triSpecializeZ Q z ≠ 0) ∧
        (∀ z ∉ Bad, ∀ r ∈ T,
          biSpecializeZ (triSpecializeX (R r) x₀) z ≠ 0) ∧
        (∀ z ∉ Bad, ∀ r ∈ T, ∀ y,
          Polynomial.eval y (biSpecializeZ (triSpecializeX (R r) x₀) z) = 0 →
          Polynomial.eval y
            (biSpecializeZ (triSpecializeX (R r).derivative x₀) z) ≠ 0) := by
  classical
  let F := ProximityPrize.Benchmark.IRSProfile.Field
  let g : Polynomial F →+* RatFunc F := algebraMap _ _
  let obsRat : ρ → Polynomial (RatFunc F) := fun r =>
    (factorXObstruction (R r)).map g
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hrawres : ∀ r ∈ T, rawSepResultant (R r) ≠ 0 := by
    intro r hr
    exact rawSepResultant_ne_zero_of_irreducible 2130706433 (R r)
      (hirr r hr) (hpos r hr) (by have := hY r hr; omega)
  have hobs : ∀ r ∈ T, factorXObstruction (R r) ≠ 0 := by
    intro r hr
    apply _root_.mul_ne_zero
    · exact Polynomial.leadingCoeff_ne_zero.mpr (hirr r hr).ne_zero
    · exact hrawres r hr
  have hobsRat : ∀ r ∈ T, obsRat r ≠ 0 := by
    intro r hr
    exact (Polynomial.map_ne_zero_iff hg).mpr (hobs r hr)
  have hobsDeg : (∑ r ∈ T, (obsRat r).natDegree) < Fintype.card F := by
    have heq : (∑ r ∈ T, (obsRat r).natDegree) =
        ∑ r ∈ T, (factorXObstruction (R r)).natDegree := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Polynomial.natDegree_map_eq_of_injective hg _
    rw [heq]
    exact hxBudget.trans_lt bchksBadBudget_lt_field
  obtain ⟨x₀, hxRat⟩ := exists_base_point_avoiding_ratfunc_polynomials
    T obsRat hobsRat hobsDeg
  have hxObs : ∀ r ∈ T,
      Polynomial.eval (Polynomial.C x₀) (factorXObstruction (R r)) ≠ 0 := by
    intro r hr
    exact raw_discr_specialization_ne_zero_of_rat_eval
      (factorXObstruction (R r)) x₀ (hxRat r hr)
  let cQ : Polynomial F := (Q.coeff jQ).coeff aQ
  let zObs : ρ → Polynomial F := fun r =>
    Polynomial.eval (Polynomial.C x₀) (factorXObstruction (R r))
  let Bad : Finset F := cQ.roots.toFinset ∪ badRootUnion T zObs
  have hzObs : ∀ r ∈ T, zObs r ≠ 0 := by
    intro r hr
    exact hxObs r hr
  have hBadcard : (S ∩ Bad).card ≤ bchksBadBudget := by
    apply le_trans (Finset.card_le_card Finset.inter_subset_right)
    apply le_trans (Finset.card_union_le cQ.roots.toFinset (badRootUnion T zObs))
    have hcroot : cQ.roots.toFinset.card ≤ cQ.natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' cQ)
    have hrest := badRootUnion_card_le_sum_natDegree T zObs hzObs
    exact (Nat.add_le_add hcroot hrest).trans (by simpa [cQ, zObs] using hzBudget x₀)
  have hxR : ∀ r ∈ T, triSpecializeX (R r) x₀ ≠ 0 := by
    intro r hr hzero
    have hcoeff := congrArg
      (fun P : Polynomial (Polynomial F) => P.coeff (R r).natDegree) hzero
    have hleadzero : Polynomial.eval (Polynomial.C x₀) (R r).leadingCoeff = 0 := by
      simpa only [triSpecializeX, Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_evalRingHom,
        Polynomial.leadingCoeff] using hcoeff
    have hprod := hxObs r hr
    apply hprod
    rw [factorXObstruction, Polynomial.eval_mul, hleadzero, zero_mul]
  refine ⟨x₀, Bad, hBadcard, hxR, ?_, ?_, ?_⟩
  · intro z hzBad hQzero
    have hzC : Polynomial.eval z cQ ≠ 0 := by
      intro hz0
      apply hzBad
      simp only [Bad, Finset.mem_union]
      left
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (by simpa [cQ] using hcQ)]
      exact hz0
    apply hzC
    have hcoeff := congrArg
      (fun P : Polynomial (Polynomial F) => (P.coeff jQ).coeff aQ) hQzero
    simpa [triSpecializeZ, cQ] using hcoeff
  · intro z hzBad r hr hzero
    have hzNotUnion : z ∉ badRootUnion T zObs := by
      intro hzmem
      apply hzBad
      simp [Bad, hzmem]
    have hzO : Polynomial.eval z (zObs r) ≠ 0 :=
      eval_ne_zero_of_not_mem_badRootUnion T zObs hzObs hzNotUnion r hr
    apply hzO
    have hcoeff := congrArg
      (fun P : Polynomial F => P.coeff (R r).natDegree) hzero
    have hlead : Polynomial.eval z
        (Polynomial.eval (Polynomial.C x₀) (R r).leadingCoeff) = 0 := by
      simpa only [biSpecializeZ, triSpecializeX, Polynomial.coeff_map,
        Polynomial.coeff_zero, Polynomial.coe_evalRingHom,
        Polynomial.leadingCoeff] using hcoeff
    dsimp [zObs]
    rw [factorXObstruction, Polynomial.eval_mul, Polynomial.eval_mul, hlead, zero_mul]
  · intro z hzBad r hr y hy
    have hzNotUnion : z ∉ badRootUnion T zObs := by
      intro hzmem
      apply hzBad
      simp [Bad, hzmem]
    have hzO : Polynomial.eval z (zObs r) ≠ 0 :=
      eval_ne_zero_of_not_mem_badRootUnion T zObs hzObs hzNotUnion r hr
    have hresEval : Polynomial.eval z
        (Polynomial.eval (Polynomial.C x₀) (rawSepResultant (R r))) ≠ 0 := by
      intro hzres
      apply hzO
      dsimp [zObs]
      rw [factorXObstruction, Polynomial.eval_mul, Polynomial.eval_mul, hzres, mul_zero]
    have hle := triSpecializeX_natDegree_le (R r) x₀
    have hleadne : Polynomial.eval (Polynomial.C x₀) (R r).leadingCoeff ≠ 0 := by
      intro hlead
      apply hxObs r hr
      rw [factorXObstruction, Polynomial.eval_mul, hlead, zero_mul]
    have hdegEq : (triSpecializeX (R r) x₀).natDegree = (R r).natDegree := by
      apply le_antisymm hle
      apply Polynomial.le_natDegree_of_ne_zero
      simpa only [triSpecializeX, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
        Polynomial.leadingCoeff] using hleadne
    have hresX : Polynomial.eval (Polynomial.C x₀) (rawSepResultant (R r)) =
        Polynomial.resultant (triSpecializeX (R r) x₀)
          (triSpecializeX (R r).derivative x₀)
          (R r).natDegree ((R r).natDegree - 1) := by
      simp [rawSepResultant, triSpecializeX, Polynomial.derivative_map]
    have hder : triSpecializeX (R r).derivative x₀ =
        (triSpecializeX (R r) x₀).derivative := by
      simp [triSpecializeX, Polynomial.derivative_map]
    have hresB : Polynomial.eval z
        (Polynomial.resultant (triSpecializeX (R r) x₀)
          (triSpecializeX (R r) x₀).derivative
          (triSpecializeX (R r) x₀).natDegree
          ((triSpecializeX (R r) x₀).natDegree - 1)) ≠ 0 := by
      rw [hdegEq, ← hder, ← hresX]
      exact hresEval
    have hsimple := simple_root_of_fixed_resultant_eval_ne_zero
      (triSpecializeX (R r) x₀) z y (by rw [hdegEq]; exact hpos r hr) hresB hy
    rw [← hder] at hsimple
    exact hsimple

end ProximityPrize.SubmissionLower
