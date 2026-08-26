import ProximityPrize.SubmissionLower.BCHKSTopEdgeMixedJetStableAudit6400
import ProximityPrize.SubmissionLower.BCHKSUniversalFactorSums
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteShiftCaps
import ProximityPrize.SubmissionLower.BCHKSJ0Interpolation6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSHybridHighDegreeAudit6400

/-!
Arithmetic audit for the proposed degree-partitioned 64.00 cover.

Factors of `Y`-degree at most 53 use the layer-sensitive top-edge mixed-Gao
minor.  Factors of degree 54 through `M` use the existing universal-Hensel
ordinary-resultant obstruction.  If `d_R` is the actual `Y`-degree and `z_R`
is the actual `Y+Z` support degree of a factor, the latter charge is

`(bchksIncidenceCoefficient6400 + 2) * d_R * z_R`.

The incidence coefficient contains the fused finite-Hensel resultant cost;
the extra two units are the factor leading/separability bad-fibre cover.  The
support degree is the minimal cap needed by `YZCap`; it also dominates the
ordinary coefficient-variable (`Z`) degree used by the low determinant.
Unlike arbitrary per-factor caps, these actual support degrees add under
products and hence aggregate across the distinct normalized factors.  The
sum is taken over the actual products `d_R*z_R`, not a padded determinant for
every factor.  Bounding `d_R <= M` only at the last step gives

`sum_R d_R*z_R <= M*sum_R z_R`.

For `M=128`, the universal coefficient is `162011264`, still slightly below
the degree-53 top-edge expensive-row coefficient `162224689`.  Degree 129 is
the first point where the universal coefficient dominates.

Two corrections to the preliminary scratch ledger are essential:

* `159107504` is the degree-52 unrestricted-Gao coefficient and cannot cover
  the stated degree-53 low branch;
* a fixed generic mixed-Gao minor needs the independent order-stability cover
  `442776953815040`.

After both corrections the hybrid still fits through degree 128, but only by
`6414780862720`.  The file proves arithmetic and generic finite-sum bounds;
it does not supply the missing mixed selector which combines the Gao and
universal-Hensel branches challenge-by-challenge.

Dependency audit (all items named "compiled" contain no local
`sorry`/`axiom`/`admit`):

* `BCHKSUniversalFactorSums.sum_resultant_natDegree_le_actual` and
  `positiveNormalizedFactors_sum_natDegree_degreeX_le` are compiled,
  unconditional actual-degree ledgers.
* `YZFactorCap.yzSupportDegree_mul` is compiled and unconditional.  The
  finite-product and normalized-factor aggregate consequences needed here
  are proved below; this removes the ambiguity between ordinary `Z` degree
  and the stronger `Y+Z` cap consumed by the concrete Hensel obstruction.
* `BCHKSConcreteGSJ06400.exists_interpolant` and
  `exists_bchks_j0_interpolant_vanishing6400` are compiled concrete theorems
  at `m=59826`, `DX=11089586663`, `DY=84608`, `DZ=1688975429`.  They now
  supply the previously experimental support cap and its root-count wrapper.
* `BCHKSUniversalGlobalCapacity.exists_pair_fiber_of_fused_resultant_ledger`
  is a compiled, unconditional combinatorial selector.
* `BCHKSFactorXDegree.factorXObstruction_eval_natDegree_le` is the compiled
  per-factor `2*d_R*z_R` leading/separability cover.
* `BCHKSParameters6400.bchks6400_incidence_rounding` is compiled exact
  arithmetic and is rescaled below without a per-factor ceiling.
* The complete universal selection/alignment chain
  `exists_concrete_selected_pair6399` / `bchksPolynomialAlignment6399` is
  compiled and unconditional, but its concrete wrappers are hard-coded to
  the 63.99 interpolant caps.  It is evidence for the technique, not yet a
  64.00 instantiation.
* `aggregate_topEdgeLayerCost_le6400` and
  `orderWitnessBadValues_card_le_aggregate` are compiled abstract ledgers.
  The sparse Gao rank-specialization theorem, concrete order-witness wiring,
  and simultaneous geometric good-reduction bridge remain unproved.
* No compiled theorem currently performs the heterogeneous cover: a challenge
  owned by a low factor must enter the Gao candidate family, while one owned
  by a high factor must enter the nested universal-factor-pair family, all
  after the same global exceptional-set deletion and center choice.
-/

def bchksHybridLowDegreeCap6400 : ℕ := 53
def bchksHybridHighDegreeCap6400 : ℕ := 128
def bchksHybridUniversalUnitCoefficient6400 : ℕ := 1265713
def bchksHybridLowZCoefficient6400 : ℕ := 162224689
def bchksHybridUniversalZCoefficient128_6400 : ℕ := 162011264
def bchksHybridZMass6400 : ℕ := 1688975428
def bchksHybridYMass6400 : ℕ := 84607

def bchksHybridZCover128_6400 : ℕ := 273993513535941892
def bchksHybridCheapCover6400 : ℕ := 29110868822445
def bchksHybridRadicalCover6400 : ℕ := 285798288073592
def bchksHybridFullCoreCover6400 : ℕ := 221377387298816
def bchksHybridOrderStabilityCover6400 : ℕ := 442776953815040
def bchksHybridPairCardCover6400 : ℕ := 6496210067
def bchksHybridQBadCover6400 : ℕ := 1688975428
def bchksHybridUniversalExtras6400 : ℕ := 8185185495
def bchksHybridTotal128_6400 : ℕ := 274972585219137280

def bchksHybridUniversalZCoefficient129_6400 : ℕ := 163276977
def bchksHybridZCover129_6400 : ℕ := 275770802111121156
def bchksHybridTotal129_6400 : ℕ := 276749873794316544

/-- The mass supplied by the older compiled stable interpolant, retained as
a comparison with the sharper compiled `j0` interpolant. -/
def bchksHybridCompiledStableZMass6400 : ℕ := 1786469528
def bchksHybridCompiledStableTotal128_6400 : ℕ := 290788535270972180

/-! ## Actual-product aggregation -/

private theorem trivariate_finset_prod_id_ne_zero
    {F : Type} [Field F]
    (S : Finset (Polynomial (Polynomial (Polynomial F))))
    (hne : ∀ R ∈ S, R ≠ 0) : S.prod id ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert R S hRS ih =>
      rw [Finset.prod_insert hRS]
      simp only [id_eq]
      exact mul_ne_zero (hne R (by simp))
        (ih (fun H hH ↦ hne H (by simp [hH])))

/-- The actual `Y+Z` support cap is additive on a finite product of nonzero
trivariate polynomials. -/
theorem yzSupportDegree_finset_prod
    {F : Type} [Field F]
    (S : Finset (Polynomial (Polynomial (Polynomial F)))) (k : ℕ)
    (hne : ∀ R ∈ S, R ≠ 0) :
    YZFactorCap.yzSupportDegree (S.prod id) k =
      ∑ R ∈ S, YZFactorCap.yzSupportDegree R k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      apply Nat.eq_zero_of_le_zero
      unfold YZFactorCap.yzSupportDegree
      apply Finset.sup_le
      intro i hi
      have hi0 : i = 0 := by
        by_contra hine
        exact (Polynomial.mem_support_iff.mp hi)
          (by simp [Polynomial.coeff_one, hine])
      subst i
      simp only [Nat.mul_zero, Nat.add_zero]
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro a ha
      have ha0 : a = 0 := by
        by_contra hane
        exact (Polynomial.mem_support_iff.mp ha)
          (by simp [Polynomial.coeff_one, hane])
      subst a
      simp
  | @insert R S hRS ih =>
      have hR : R ≠ 0 := hne R (by simp)
      have hprod : S.prod id ≠ 0 :=
        trivariate_finset_prod_id_ne_zero S
          (fun H hH ↦ hne H (by simp [hH]))
      rw [Finset.prod_insert hRS, Finset.sum_insert hRS]
      simp only [id_eq]
      calc
        YZFactorCap.yzSupportDegree (R * ∏ H ∈ S, H) k =
            YZFactorCap.yzSupportDegree R k +
              YZFactorCap.yzSupportDegree (∏ H ∈ S, H) k := by
          simpa only [Finset.prod_apply, id_eq] using
            YZFactorCap.yzSupportDegree_mul R (S.prod id) k hR hprod
        _ = YZFactorCap.yzSupportDegree R k +
              ∑ H ∈ S, YZFactorCap.yzSupportDegree H k := by
          congr 1
          simpa only [Finset.prod_apply, id_eq] using
            ih (fun H hH ↦ hne H (by simp [hH]))

/-- A `YZCap` is supplied by the polynomial's actual support degree, rather
than by a padded global bound. -/
theorem YZCap_yzSupportDegree
    {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) :
    RationalFunctions.HenselNumerators.ConcreteFiniteNumerators.YZCap R
      (YZFactorCap.yzSupportDegree R 1) := by
  intro j a ha
  have hj : R.coeff j ≠ 0 := by
    intro hz
    exact ha (by simp [hz])
  have hcoeff := Polynomial.Bivariate.coeff_natDegree_le_degreeX
    (R.coeff j) a
  have hsupport := YZFactorCap.coeffWeight_le_of_ne R 1 j hj
  omega

/-- A coefficientwise `Y+Z` cap also bounds the actual support degree. -/
theorem yzSupportDegree_le_of_YZCap
    {F : Type} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (D : ℕ)
    (hcap :
      RationalFunctions.HenselNumerators.ConcreteFiniteNumerators.YZCap Q D) :
    YZFactorCap.yzSupportDegree Q 1 ≤ D := by
  classical
  unfold YZFactorCap.yzSupportDegree
  apply Finset.sup_le
  intro j hj
  have hj0 : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  obtain ⟨a, ha, hadeg, -⟩ :=
    Polynomial.Bivariate.exists_max_index_degreeX (Q.coeff j) hj0
  have hca : (Q.coeff j).coeff a ≠ 0 :=
    Polynomial.mem_support_iff.mp ha
  have hc := hcap j a hca
  simpa [hadeg] using hc

/-- Across all distinct positive normalized outer factors, the sum of the
actual `Y+Z` support degrees is at most that of the original interpolant.
This is the algebraic justification for the aggregate `z_R` mass. -/
theorem positiveNormalizedFactors_sum_yzSupportDegree_le
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) :
    let S := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R ↦ 0 < R.natDegree)
    (∑ R ∈ S, YZFactorCap.yzSupportDegree R 1) ≤
      YZFactorCap.yzSupportDegree Q 1 := by
  classical
  dsimp only
  let M := UniqueFactorizationMonoid.normalizedFactors Q
  let T := M.toFinset
  let S := T.filter (fun R ↦ 0 < R.natDegree)
  have hS0 : ∀ R ∈ S, R ≠ 0 := by
    intro R hR
    exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hR).1)
  have hST : S.prod id ∣ T.prod id :=
    Finset.prod_dvd_prod_of_subset S T id (Finset.filter_subset _ _)
  have hTM : T.prod id ∣ M.prod := by
    simpa [T] using Multiset.toFinset_prod_dvd_prod M
  have hMQ : M.prod ∣ Q :=
    (UniqueFactorizationMonoid.prod_normalizedFactors hQ).dvd
  have hSQ : S.prod id ∣ Q := hST.trans (hTM.trans hMQ)
  obtain ⟨C, hQC⟩ := hSQ
  have hprod0 : S.prod id ≠ 0 :=
    trivariate_finset_prod_id_ne_zero S hS0
  have hC0 : C ≠ 0 := by
    intro hC
    apply hQ
    rw [hQC, hC, mul_zero]
  have hsum := yzSupportDegree_finset_prod S 1 hS0
  have hmul := YZFactorCap.yzSupportDegree_mul (S.prod id) C 1 hprod0 hC0
  change (∑ R ∈ S, YZFactorCap.yzSupportDegree R 1) ≤
    YZFactorCap.yzSupportDegree Q 1
  rw [← hsum, hQC, hmul]
  exact Nat.le_add_right _ _

/-- Concrete composition of the previous two facts: a global actual
`Y+Z` cap gives the aggregate mass hypothesis used by the hybrid ledger. -/
theorem positiveNormalizedFactors_sum_yzSupportDegree_le_of_YZCap
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (D : ℕ)
    (hcap :
      RationalFunctions.HenselNumerators.ConcreteFiniteNumerators.YZCap Q D) :
    let S := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R ↦ 0 < R.natDegree)
    (∑ R ∈ S, YZFactorCap.yzSupportDegree R 1) ≤ D := by
  dsimp only
  exact (positiveNormalizedFactors_sum_yzSupportDegree_le Q hQ).trans
    (yzSupportDegree_le_of_YZCap Q D hcap)

/-- The precise strict support hypothesis needed to obtain mass
`1688975428`.  `exists_bchks_j0_interpolant_vanishing6400` now supplies this
hypothesis concretely. -/
theorem positiveNormalizedFactors_sum_yzSupportDegree_le_hybridMass
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (hcap : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 1688975429) :
    let S := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R ↦ 0 < R.natDegree)
    (∑ R ∈ S, YZFactorCap.yzSupportDegree R 1) ≤
      bchksHybridZMass6400 := by
  apply positiveNormalizedFactors_sum_yzSupportDegree_le_of_YZCap
    Q hQ bchksHybridZMass6400
  intro j a ha
  have hh := hcap j a ha
  norm_num [bchksHybridZMass6400] at hh ⊢
  omega

/-- End-to-end witness that the concrete `j0` interpolation output has the
aggregate actual support mass consumed by this audit. -/
theorem exists_bchks_j0_interpolant_factorSupportMass6400
    (U : Fin 2 → ProximityPrize.Benchmark.IRSProfile.Index →
      ProximityPrize.Benchmark.IRSProfile.Field)
    (S : Finset ProximityPrize.Benchmark.IRSProfile.Field)
    (A : ProximityPrize.Benchmark.IRSProfile.Field →
      Finset ProximityPrize.Benchmark.IRSProfile.Index)
    (hA : ∀ z ∈ S, 185364 ≤ (A z).card)
    (hcomb : ∀ z ∈ S,
      LinearCode.projectedWord (fun i ↦ U 0 i + z * U 1 i) (A z) ∈
        LinearCode.projectedCodeSubmod
          ProximityPrize.Benchmark.IRSProfile.baseCode (A z)) :
    ∃ (P : ↥S → Polynomial ProximityPrize.Benchmark.IRSProfile.Field)
      (Q : Polynomial (Polynomial
        (Polynomial ProximityPrize.Benchmark.IRSProfile.Field))),
      Q ≠ 0 ∧
      (∀ z : ↥S, (P z).natDegree ≤ 131071) ∧
      (∀ z : ↥S,
        BCHKSSubstitutionVanish.triEval Q z.1 (P z) = 0) ∧
      (∀ j a, (Q.coeff j).coeff a ≠ 0 →
        j < 84608 ∧ a + 131071 * j < 11089586663 ∧
          ((Q.coeff j).coeff a).natDegree + j < 1688975429) ∧
      (let Rs :=
        (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R ↦ 0 < R.natDegree)
       (∑ R ∈ Rs, YZFactorCap.yzSupportDegree R 1) ≤
        bchksHybridZMass6400) := by
  obtain ⟨P, Q, hQ, hPdeg, _hPagree, hvan, hcaps⟩ :=
    exists_bchks_j0_interpolant_vanishing6400 U S A hA hcomb
  refine ⟨P, Q, hQ, hPdeg, hvan, hcaps, ?_⟩
  exact positiveNormalizedFactors_sum_yzSupportDegree_le_hybridMass
    Q hQ (fun j a ha ↦ (hcaps j a ha).2.2)

/-- The universal-Hensel charge retains the actual product `d_R*z_R` for
each factor. -/
theorem sum_universalCharge_le_actual_degreeZProduct
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (degree zDegree charge : R → ℕ)
    (hcharge : ∀ r ∈ Rs,
      charge r ≤ bchksHybridUniversalUnitCoefficient6400 *
        degree r * zDegree r) :
    (∑ r ∈ Rs, charge r) ≤
      bchksHybridUniversalUnitCoefficient6400 *
        (∑ r ∈ Rs, degree r * zDegree r) := by
  calc
    (∑ r ∈ Rs, charge r) ≤
        ∑ r ∈ Rs,
          bchksHybridUniversalUnitCoefficient6400 * degree r * zDegree r :=
      Finset.sum_le_sum hcharge
    _ = bchksHybridUniversalUnitCoefficient6400 *
        (∑ r ∈ Rs, degree r * zDegree r) := by
      simp only [Finset.mul_sum, mul_assoc]

/-- Only after summing actual products do we use a maximum factor-degree
cap. -/
theorem sum_degree_mul_zDegree_le_max_mul_sum
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (degree zDegree : R → ℕ) (M : ℕ)
    (hdegree : ∀ r ∈ Rs, degree r ≤ M) :
    (∑ r ∈ Rs, degree r * zDegree r) ≤
      M * (∑ r ∈ Rs, zDegree r) := by
  calc
    (∑ r ∈ Rs, degree r * zDegree r) ≤
        ∑ r ∈ Rs, M * zDegree r := by
      apply Finset.sum_le_sum
      intro r hr
      exact Nat.mul_le_mul_right (zDegree r) (hdegree r hr)
    _ = M * (∑ r ∈ Rs, zDegree r) := by
      rw [Finset.mul_sum]

/-- The compiled 64.00 incidence rounding scales the exact aggregate
`sum d_R*z_R`; no factorwise ceiling is needed. -/
theorem bchksHybrid_fused_actualProduct6400 (productMass : ℕ) :
    (262144 - 131071) *
        (2 * bchksUniversalExponent6400 * productMass) ≤
      (262144 - bchksErrors6400 - 131071) *
        (bchksIncidenceCoefficient6400 * productMass) := by
  have h := Nat.mul_le_mul_right productMass bchks6400_incidence_rounding
  simpa [bchksUniversalExponent6400, mul_assoc, mul_left_comm, mul_comm]
    using h

/-- Combined low/high aggregation.  The low branch pays the top-edge
expensive-row coefficient.  The high branch pays the universal coefficient
against its actual degree.  Since both coefficients are below
`162224689` through degree 128, only the aggregate `Z`-degree is needed at
the final step. -/
theorem hybrid_expensiveCharge_le_degree128
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (degree zDegree charge : R → ℕ)
    (hdegree : ∀ r ∈ Rs, degree r ≤ 128)
    (hlow : ∀ r ∈ Rs, degree r ≤ 53 →
      charge r ≤ bchksHybridLowZCoefficient6400 * zDegree r)
    (hhigh : ∀ r ∈ Rs, 53 < degree r →
      charge r ≤ bchksHybridUniversalUnitCoefficient6400 *
        degree r * zDegree r)
    (hzMass : (∑ r ∈ Rs, zDegree r) ≤ bchksHybridZMass6400) :
    (∑ r ∈ Rs, charge r) ≤ bchksHybridZCover128_6400 := by
  have hterm : ∀ r ∈ Rs,
      charge r ≤ bchksHybridLowZCoefficient6400 * zDegree r := by
    intro r hr
    by_cases hd : degree r ≤ 53
    · exact hlow r hr hd
    · have hd128 : degree r ≤ 128 := hdegree r hr
      have hcoeff :
          bchksHybridUniversalUnitCoefficient6400 * degree r ≤
            bchksHybridLowZCoefficient6400 := by
        calc
          bchksHybridUniversalUnitCoefficient6400 * degree r ≤
              bchksHybridUniversalUnitCoefficient6400 * 128 :=
            Nat.mul_le_mul_left _ hd128
          _ ≤ bchksHybridLowZCoefficient6400 := by
            norm_num [bchksHybridUniversalUnitCoefficient6400,
              bchksHybridLowZCoefficient6400]
      exact (hhigh r hr (by omega)).trans
        (Nat.mul_le_mul_right (zDegree r) hcoeff)
  calc
    (∑ r ∈ Rs, charge r) ≤
        ∑ r ∈ Rs, bchksHybridLowZCoefficient6400 * zDegree r :=
      Finset.sum_le_sum hterm
    _ = bchksHybridLowZCoefficient6400 *
        (∑ r ∈ Rs, zDegree r) := by
      rw [Finset.mul_sum]
    _ ≤ bchksHybridLowZCoefficient6400 * bchksHybridZMass6400 :=
      Nat.mul_le_mul_left _ hzMass
    _ = bchksHybridZCover128_6400 := by
      norm_num [bchksHybridLowZCoefficient6400,
        bchksHybridZMass6400, bchksHybridZCover128_6400]

/-! ## Exact boundary ledger -/

lemma bchksHybrid_coefficients_exact6400 :
    bchksHybridUniversalUnitCoefficient6400 =
        bchksIncidenceCoefficient6400 + 2 ∧
      bchksHybridUniversalZCoefficient128_6400 =
        bchksHybridUniversalUnitCoefficient6400 * 128 ∧
      bchksHybridUniversalZCoefficient128_6400 <
        bchksHybridLowZCoefficient6400 ∧
      bchksHybridUniversalZCoefficient129_6400 =
        bchksHybridUniversalUnitCoefficient6400 * 129 ∧
      bchksHybridLowZCoefficient6400 <
        bchksHybridUniversalZCoefficient129_6400 := by
  norm_num [bchksHybridUniversalUnitCoefficient6400,
    bchksIncidenceCoefficient6400,
    bchksHybridUniversalZCoefficient128_6400,
    bchksHybridLowZCoefficient6400,
    bchksHybridUniversalZCoefficient129_6400]

lemma bchksHybrid_componentLedger_exact6400 :
    bchksHybridZCover128_6400 =
        bchksHybridLowZCoefficient6400 * bchksHybridZMass6400 ∧
      bchksHybridCheapCover6400 =
        BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeAggregateJetCover6400 ∧
      bchksHybridRadicalCover6400 =
        BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedPureRadicalCover6400 ∧
      bchksHybridFullCoreCover6400 =
        BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedFullCoreBadCover6400 ∧
      bchksHybridOrderStabilityCover6400 =
        BCHKSOrderStabilityAudit6400.bchksOrderStabilityCover6400 ∧
      bchksHybridPairCardCover6400 =
        (bchksErrors6400 + 1) * bchksHybridYMass6400 ∧
      bchksHybridQBadCover6400 = bchksHybridZMass6400 ∧
      bchksHybridUniversalExtras6400 =
        bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 := by
  constructor
  · norm_num [bchksHybridZCover128_6400,
      bchksHybridLowZCoefficient6400, bchksHybridZMass6400]
  constructor
  · norm_num [bchksHybridCheapCover6400,
      BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeAggregateJetCover6400]
  constructor
  · norm_num [bchksHybridRadicalCover6400,
      BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedPureRadicalCover6400]
  constructor
  · norm_num [bchksHybridFullCoreCover6400,
      BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedFullCoreBadCover6400]
  constructor
  · norm_num [bchksHybridOrderStabilityCover6400,
      BCHKSOrderStabilityAudit6400.bchksOrderStabilityCover6400]
  constructor
  · norm_num [bchksHybridPairCardCover6400, bchksErrors6400,
      bchksHybridYMass6400]
  constructor
  · rfl
  · norm_num [bchksHybridUniversalExtras6400,
      bchksHybridPairCardCover6400, bchksHybridQBadCover6400]

lemma bchksHybrid_total128_exact6400 :
    bchksHybridTotal128_6400 =
      bchksHybridZCover128_6400 +
      bchksHybridCheapCover6400 +
      bchksHybridRadicalCover6400 +
      bchksHybridFullCoreCover6400 +
      bchksHybridOrderStabilityCover6400 +
      bchksHybridPairCardCover6400 +
      bchksHybridQBadCover6400 := by
  norm_num [bchksHybridTotal128_6400, bchksHybridZCover128_6400,
    bchksHybridCheapCover6400, bchksHybridRadicalCover6400,
    bchksHybridFullCoreCover6400, bchksHybridOrderStabilityCover6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400]

lemma bchksHybrid_degree128_fieldBudget6400 :
    bchksHybridTotal128_6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksHybridTotal128_6400 =
        6414780862720 ∧
      2 ^ (128 : ℕ) *
          (bchksHybridTotal128_6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksHybridTotal128_6400,
    bchksWeightedNumerator6400, bchksListBound6400]

/-- Substituting the older stable support mass misses the 64.00 field budget
by about `1.58e16`.  This records why the sharper `j0` instantiation above
was necessary. -/
lemma bchksHybrid_compiledStableCap_noGo6400 :
    bchksHybridCompiledStableZMass6400 = 1786469529 - 1 ∧
      bchksHybridCompiledStableTotal128_6400 =
        bchksHybridLowZCoefficient6400 *
            bchksHybridCompiledStableZMass6400 +
          bchksHybridCheapCover6400 + bchksHybridRadicalCover6400 +
          bchksHybridFullCoreCover6400 +
          bchksHybridOrderStabilityCover6400 +
          bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 ∧
      bchksWeightedNumerator6400 <
        bchksHybridCompiledStableTotal128_6400 ∧
      bchksHybridCompiledStableTotal128_6400 -
          bchksWeightedNumerator6400 = 15809535270972180 := by
  norm_num [bchksHybridCompiledStableZMass6400,
    bchksHybridCompiledStableTotal128_6400,
    bchksHybridLowZCoefficient6400, bchksHybridCheapCover6400,
    bchksHybridRadicalCover6400, bchksHybridFullCoreCover6400,
    bchksHybridOrderStabilityCover6400, bchksHybridPairCardCover6400,
    bchksHybridQBadCover6400, bchksWeightedNumerator6400]

/-- Degree 129 is the first coefficient crossover and it misses the safe
numerator by about `1.77e15`.  This is a no-go for this exact aggregate
ledger, not an impossibility theorem for degree 129. -/
lemma bchksHybrid_degree129_noGo6400 :
    bchksHybridZCover129_6400 =
        bchksHybridUniversalZCoefficient129_6400 * bchksHybridZMass6400 ∧
      bchksHybridTotal129_6400 =
        bchksHybridZCover129_6400 +
        bchksHybridCheapCover6400 +
        bchksHybridRadicalCover6400 +
        bchksHybridFullCoreCover6400 +
        bchksHybridOrderStabilityCover6400 +
        bchksHybridPairCardCover6400 +
        bchksHybridQBadCover6400 ∧
      bchksWeightedNumerator6400 < bchksHybridTotal129_6400 ∧
      bchksHybridTotal129_6400 - bchksWeightedNumerator6400 =
        1770873794316544 := by
  norm_num [bchksHybridZCover129_6400,
    bchksHybridUniversalZCoefficient129_6400, bchksHybridZMass6400,
    bchksHybridTotal129_6400, bchksHybridCheapCover6400,
    bchksHybridRadicalCover6400, bchksHybridFullCoreCover6400,
    bchksHybridOrderStabilityCover6400, bchksHybridPairCardCover6400,
    bchksHybridQBadCover6400, bchksWeightedNumerator6400]

/-! ## How much a degree-129 resultant refinement would have to save -/

def bchksHybridExactFusedCoefficient129_6400 : ℕ := 163276900
def bchksHybridOneUnitSavedCoefficient129_6400 : ℕ := 162644045
def bchksHybridTwoUnitsSavedCoefficient129_6400 : ℕ := 162011189
def bchksHybridOneUnitSavedTotal129_6400 : ℕ := 275680867198721648

/-- Using the exact fused floor rather than `(I+2)*d` saves only 77 units of
`Z`-coefficient and still misses badly.  Even a hypothetical reduction of
the inner resultant degree from `E*(2d)` to `E*(2d-1)` misses.  A full
two-unit reduction to `E*(2d-2)` would cross below the degree-53 Gao
coefficient and recover the degree-128 total.

The existing actual-resultant theorem does not provide either strict unit:
an inner specialization that stays irreducible may have its single factor
saturate both degree sums. -/
lemma bchksHybrid_degree129_saving_threshold6400 :
    bchksHybridExactFusedCoefficient129_6400 =
        ((262144 - 131071) *
            (bchksUniversalExponent6400 * (2 * 129)) +
          (262144 - bchksErrors6400 - 131071) - 1) /
          (262144 - bchksErrors6400 - 131071) + 2 * 129 ∧
      bchksHybridLowZCoefficient6400 <
        bchksHybridExactFusedCoefficient129_6400 ∧
      bchksHybridOneUnitSavedCoefficient129_6400 =
        ((262144 - 131071) *
            (bchksUniversalExponent6400 * (2 * 129 - 1)) +
          (262144 - bchksErrors6400 - 131071) - 1) /
          (262144 - bchksErrors6400 - 131071) + 2 * 129 ∧
      bchksHybridLowZCoefficient6400 <
        bchksHybridOneUnitSavedCoefficient129_6400 ∧
      bchksHybridTwoUnitsSavedCoefficient129_6400 =
        ((262144 - 131071) *
            (bchksUniversalExponent6400 * (2 * 129 - 2)) +
          (262144 - bchksErrors6400 - 131071) - 1) /
          (262144 - bchksErrors6400 - 131071) + 2 * 129 ∧
      bchksHybridTwoUnitsSavedCoefficient129_6400 <
        bchksHybridLowZCoefficient6400 ∧
      bchksHybridOneUnitSavedTotal129_6400 =
        bchksHybridOneUnitSavedCoefficient129_6400 * bchksHybridZMass6400 +
          bchksHybridCheapCover6400 + bchksHybridRadicalCover6400 +
          bchksHybridFullCoreCover6400 +
          bchksHybridOrderStabilityCover6400 +
          bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 ∧
      bchksWeightedNumerator6400 < bchksHybridOneUnitSavedTotal129_6400 ∧
      bchksHybridOneUnitSavedTotal129_6400 - bchksWeightedNumerator6400 =
        701867198721648 := by
  norm_num [bchksHybridExactFusedCoefficient129_6400,
    bchksHybridOneUnitSavedCoefficient129_6400,
    bchksHybridTwoUnitsSavedCoefficient129_6400,
    bchksHybridOneUnitSavedTotal129_6400,
    bchksUniversalExponent6400, bchksErrors6400,
    bchksHybridLowZCoefficient6400, bchksHybridZMass6400,
    bchksHybridCheapCover6400, bchksHybridRadicalCover6400,
    bchksHybridFullCoreCover6400, bchksHybridOrderStabilityCover6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksWeightedNumerator6400]

/-! ## Audit of the discarded preliminary number -/

def bchksHybridPreliminaryTotal128_6400 : ℕ := 274181350831704189

/-- This reproduces the optimistic scratch total exactly and exposes its two
incompatible inputs: the degree-52 coefficient/cheap cover and no
order-stability term. -/
lemma bchksHybrid_preliminaryTotal_reconstructed6400 :
    bchksHybridPreliminaryTotal128_6400 =
      bchksHybridUniversalZCoefficient128_6400 * bchksHybridZMass6400 +
      BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedAggregateJetCover6400 +
      bchksHybridRadicalCover6400 + bchksHybridFullCoreCover6400 +
      bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 := by
  norm_num [bchksHybridPreliminaryTotal128_6400,
    bchksHybridUniversalZCoefficient128_6400, bchksHybridZMass6400,
    BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedAggregateJetCover6400,
    bchksHybridRadicalCover6400, bchksHybridFullCoreCover6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400]

end BCHKSHybridHighDegreeAudit6400
end ProximityPrize.SubmissionLower
