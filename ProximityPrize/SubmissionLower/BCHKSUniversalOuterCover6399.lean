import ProximityPrize.SubmissionLower.BCHKSUniversalPrimitiveX0Avoidance6399
import ProximityPrize.SubmissionLower.BCHKSUniversalPositivePairCard
import ProximityPrize.SubmissionLower.BCHKSWeightedFactorCaps
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap
import ProximityPrize.SubmissionLower.BCHKSParameters6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open scoped BigOperators

set_option maxHeartbeats 2000000

namespace UniversalOuterCover6399

abbrev F := IRSProfile.Field
abbrev TriPoly := Polynomial (Polynomial (Polynomial F))
abbrev BiPoly := Polynomial (Polynomial F)
abbrev Pair := TriPoly × BiPoly

noncomputable def outerFactors (Q : TriPoly) : Finset TriPoly :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun R => 0 < R.natDegree)

noncomputable def qBad (S : Finset F) (Q : TriPoly) : Finset F :=
  badZSpecializations Q S

noncomputable def outerBad (x₀ : F) (R : TriPoly) : Finset F :=
  (Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)).roots.toFinset

noncomputable def pairs (Q : TriPoly) (x₀ : F) : Finset Pair :=
  positiveNormalizedFactorPairs Q x₀

/-- The relation retained by global pigeonholing.  Besides the two root
identities, it records the one-time outer obstruction and nonvanishing of the
specialized outer polynomial at this seed. -/
def pairRel (Pz : F → Polynomial F) (x₀ z : F) (RH : Pair) : Prop :=
  triEval RH.1 z (Pz z) = 0 ∧
  biEval RH.2 (Polynomial.eval x₀ (Pz z)) z = 0 ∧
  Polynomial.eval z
      (Polynomial.eval (Polynomial.C x₀) (factorXObstruction RH.1)) ≠ 0 ∧
  biSpecializeZ (triSpecializeX RH.1 x₀) z ≠ 0

/-- The 6399 support contract, kept as a named predicate so the concrete cover
has the same single hypothesis as the interpolation module. -/
def SupportCaps (Q : TriPoly) : Prop :=
  ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
    j < 5280 ∧ a + 131071 * j < 692001142 ∧
      ((Q.coeff j).coeff a).natDegree + j < 13141403

theorem natDegree_le_factorMass
    (Q : TriPoly) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    Q.natDegree ≤ bchksFactorMass6399 := by
  have hlead : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlead
  have hcoeff : (Q.coeff Q.natDegree).coeff a ≠ 0 :=
    Polynomial.mem_support_iff.mp ha
  have hj := (hcaps Q.natDegree a hcoeff).1
  norm_num [bchksFactorMass6399] at hj ⊢
  omega

/-- Derive precisely the two X-degree hypotheses consumed by simultaneous
`x₀` avoidance from the weighted interpolation support cap. -/
theorem normalizedFactor_X_caps
    (Q : TriPoly) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    (∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      degreeX (mapZToRatFunc R) ≤ UniversalX0Avoidance6399.DX) ∧
    (∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.leadingCoeff.natDegree ≤ UniversalX0Avoidance6399.DX) := by
  constructor
  · intro R hRQ
    have hRW := WeightedFactorCaps.normalizedFactor_weightedX_cap
      Q R 131071 692001142 hQ hRQ (fun j a h => (hcaps j a h).2.1)
    unfold degreeX
    apply Finset.sup_le
    intro j hj
    simp only [mapZToRatFunc, Polynomial.coeff_map]
    apply Polynomial.natDegree_map_le.trans
    by_cases hz : R.coeff j = 0
    · simp [hz]
    · have hne : (R.coeff j).coeff (R.coeff j).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz
      have hw := hRW j (R.coeff j).natDegree hne
      norm_num [UniversalX0Avoidance6399.DX] at hw ⊢
      omega
  · intro R hRQ
    by_cases hz : R.leadingCoeff = 0
    · simp [hz]
    · have hRW := WeightedFactorCaps.normalizedFactor_weightedX_cap
        Q R 131071 692001142 hQ hRQ (fun j a h => (hcaps j a h).2.1)
      have hne : (R.coeff R.natDegree).coeff R.leadingCoeff.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree, Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz
      have hw := hRW R.natDegree R.leadingCoeff.natDegree hne
      norm_num [UniversalX0Avoidance6399.DX] at hw ⊢
      omega

/-- Coefficient caps in the swapped orientation required by the effective
primitive-specialization obstruction. -/
theorem normalizedFactor_swap_caps
    (Q : TriPoly) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    (∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q, ∀ j,
      (Polynomial.Bivariate.swap (R.coeff j)).natDegree ≤ bchksZCap6399) ∧
    (∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q, ∀ j,
      Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (R.coeff j)) ≤
        bchksXCap6399) := by
  constructor
  · intro R hRQ j
    have hRYZ := YZFactorCap.normalizedFactor_YZ_cap
      Q R 13141403 hQ hRQ (fun j a h => (hcaps j a h).2.2)
    rw [show (Polynomial.Bivariate.swap (R.coeff j)).natDegree =
        Polynomial.Bivariate.natDegreeY
          (Polynomial.Bivariate.swap (R.coeff j)) from rfl,
      Polynomial.Bivariate.natDegreeY_swap]
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    have h := hRYZ j a (Polynomial.mem_support_iff.mp ha)
    norm_num [bchksZCap6399] at h ⊢
    omega
  · intro R hRQ j
    have hRW := WeightedFactorCaps.normalizedFactor_weightedX_cap
      Q R 131071 692001142 hQ hRQ (fun j a h => (hcaps j a h).2.1)
    rw [Polynomial.Bivariate.degreeX_swap]
    change (R.coeff j).natDegree ≤ bchksXCap6399
    by_cases hz : R.coeff j = 0
    · simp [hz]
    · have hl := Polynomial.leadingCoeff_ne_zero.mpr hz
      have hw := hRW j (R.coeff j).natDegree (by
        rw [Polynomial.coeff_natDegree]
        exact hl)
      norm_num [bchksXCap6399] at hw ⊢
      omega
/-- A single surviving coefficient of `Q` controls the whole-Q bad set. -/
theorem qBad_card_le
    (S : Finset F) (Q : TriPoly) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    (qBad S Q).card ≤ bchksZCap6399 := by
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hQ
  have hj0 : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hj0
  have ha0 : (Q.coeff j).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
  have hdeg : ((Q.coeff j).coeff a).natDegree < bchksZCap6399 := by
    have h := (hcaps j a ha0).2.2
    norm_num [bchksZCap6399] at h ⊢
    omega
  exact (badZSpecializations_card_lt Q S j a bchksZCap6399 ha0 hdeg).le

/-- Evaluating the middle variable cannot increase the coefficient-variable
degree inherited from the sharp `Z+Y` support cap. -/
private theorem factor_eval_Z_caps
    (Q R : TriPoly) (x₀ : F) (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hcaps : SupportCaps Q) :
    degreeX (triSpecializeX R x₀) ≤ bchksZCap6399 ∧
    (Polynomial.eval (Polynomial.C x₀) R.leadingCoeff).natDegree ≤
      bchksZCap6399 := by
  have hRYZ := YZFactorCap.normalizedFactor_YZ_cap Q R 13141403 hQ hRQ
    (fun j a h => (hcaps j a h).2.2)
  have hcoeffCap : ∀ j, degreeX (R.coeff j) ≤ bchksZCap6399 := by
    intro j
    unfold degreeX
    apply Finset.sup_le
    intro a ha
    have h := hRYZ j a (Polynomial.mem_support_iff.mp ha)
    norm_num [bchksZCap6399] at h ⊢
    omega
  have hevalCap : ∀ p : Polynomial (Polynomial F),
      degreeX p ≤ bchksZCap6399 →
      (Polynomial.eval (Polynomial.C x₀) p).natDegree ≤ bchksZCap6399 := by
    intro p hp
    have heq : (Polynomial.Bivariate.swap p).map
        (Polynomial.evalRingHom x₀) = Polynomial.eval (Polynomial.C x₀) p := by
      rw [← Polynomial.Bivariate.evalX_eq_map]
      exact (Polynomial.Bivariate.evalY_eq_evalX_swap x₀ p).symm
    rw [← heq]
    exact Polynomial.natDegree_map_le.trans (by
      rw [show (Polynomial.Bivariate.swap p).natDegree =
        Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap p) from rfl,
        Polynomial.Bivariate.natDegreeY_swap]
      exact hp)
  constructor
  · unfold degreeX
    apply Finset.sup_le
    intro j hj
    simp only [triSpecializeX, Polynomial.coeff_map]
    exact hevalCap (R.coeff j) (hcoeffCap j)
  · exact hevalCap R.leadingCoeff (by
      rw [← Polynomial.coeff_natDegree]
      exact hcoeffCap R.natDegree)

/-- The sum of all one-time outer leading/slope bad sets is exactly charged by
`2 * DZ * M`; it is not multiplied by the number of nested factors. -/
theorem outerBad_sum_card_le
    (Q : TriPoly) (x₀ : F) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    (∑ R ∈ outerFactors Q, (outerBad x₀ R).card) ≤
      2 * bchksZCap6399 * bchksFactorMass6399 := by
  have hQdeg := natDegree_le_factorMass Q hQ hcaps
  have hsum : (∑ R ∈ outerFactors Q, R.natDegree) ≤
      bchksFactorMass6399 := by
    simpa [outerFactors, UniversalX0Avoidance6399.M, bchksFactorMass6399] using
      UniversalX0Avoidance6399.positive_outer_factor_degree_sum_le
        Q hQ UniversalX0Avoidance6399.M (by
          simpa [UniversalX0Avoidance6399.M, bchksFactorMass6399] using hQdeg)
  have hone : ∀ R ∈ outerFactors Q, (outerBad x₀ R).card ≤
      2 * R.natDegree * bchksZCap6399 := by
    intro R hR
    have hmem := Finset.mem_filter.mp hR
    have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
      Multiset.mem_toFinset.mp hmem.1
    have hcap := factor_eval_Z_caps Q R x₀ hQ hRQ hcaps
    calc
      (outerBad x₀ R).card ≤
          (Polynomial.eval (Polynomial.C x₀)
            (factorXObstruction R)).roots.card := Multiset.toFinset_card_le _
      _ ≤ (Polynomial.eval (Polynomial.C x₀)
            (factorXObstruction R)).natDegree := Polynomial.card_roots' _
      _ ≤ 2 * R.natDegree * bchksZCap6399 :=
        factorXObstruction_eval_natDegree_le R x₀ R.natDegree
          bchksZCap6399 hmem.2 (le_refl _) hcap.1 hcap.2
  calc
    (∑ R ∈ outerFactors Q, (outerBad x₀ R).card) ≤
        ∑ R ∈ outerFactors Q, 2 * R.natDegree * bchksZCap6399 :=
      Finset.sum_le_sum hone
    _ = 2 * bchksZCap6399 * (∑ R ∈ outerFactors Q, R.natDegree) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro R hR
      ring
    _ ≤ 2 * bchksZCap6399 * bchksFactorMass6399 :=
      Nat.mul_le_mul_left _ hsum

/-- Membership in the concrete pair finset exposes the exact normalized-factor
and divisibility facts required by the fixed-pair consumer. -/
theorem pair_mem_facts
    (Q : TriPoly) (x₀ : F) (RH : Pair) (hRH : RH ∈ pairs Q x₀) :
    RH.1 ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
    0 < RH.1.natDegree ∧
    RH.2 ∈ UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX RH.1 x₀) ∧
    0 < RH.2.natDegree ∧ RH.2 ∣ triSpecializeX RH.1 x₀ := by
  simp only [pairs, positiveNormalizedFactorPairs, Finset.mem_biUnion,
    Multiset.mem_toFinset, Finset.mem_image, Finset.mem_filter] at hRH
  obtain ⟨R, hRQ, H, ⟨hHB, hHpos⟩, heq⟩ := hRH
  cases heq
  have hB : triSpecializeX R x₀ ≠ 0 := by
    intro hz
    simpa [hz] using hHB
  have hHdeg : H.natDegree ≤ (triSpecializeX R x₀).natDegree := by
    calc
      H.natDegree ≤ ∑ J ∈
          (UniqueFactorizationMonoid.normalizedFactors
            (triSpecializeX R x₀)).toFinset, J.natDegree :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simpa using hHB)
      _ ≤ (triSpecializeX R x₀).natDegree :=
        normalizedFactors_toFinset_sum_natDegree_le _ hB
  have hRpos : 0 < R.natDegree := by
    have := hHdeg.trans (triSpecializeX_natDegree_le R x₀)
    omega
  exact ⟨hRQ, hRpos, hHB, hHpos,
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hHB⟩

/-- Complete concrete global cover for the 6399 universal-numerator route. -/
theorem exists_outer_pair_cover
    (S : Finset F) (Pz : F → Polynomial F) (Q : TriPoly)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (Pz z) = 0)
    (hcaps : SupportCaps Q) :
    ∃ x₀ : F,
      (qBad S Q).card ≤ bchksZCap6399 ∧
      (∑ R ∈ outerFactors Q, (outerBad x₀ R).card) ≤
        2 * bchksZCap6399 * bchksFactorMass6399 ∧
      (pairs Q x₀).card ≤ bchksFactorMass6399 ∧
      (∀ R ∈ outerFactors Q,
        (triSpecializeX R x₀).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) ≠ 0) ∧
      ∀ z ∈ S \ (qBad S Q ∪
          (outerFactors Q).biUnion (outerBad x₀)),
        ∃ RH ∈ pairs Q x₀, pairRel Pz x₀ z RH := by
  classical
  have hQdeg := natDegree_le_factorMass Q hQ hcaps
  obtain ⟨hX, hlead⟩ := normalizedFactor_X_caps Q hQ hcaps
  obtain ⟨hZ, hXswap⟩ := normalizedFactor_swap_caps Q hQ hcaps
  have hQdeg' : Q.natDegree ≤ UniversalX0Avoidance6399.M := by
    simpa [UniversalX0Avoidance6399.M, bchksFactorMass6399] using hQdeg
  obtain ⟨x₀, hx⟩ :=
    UniversalPrimitiveX0Avoidance6399.exists_x0_primitive_and_factor_good
      Q hQ hQdeg' hZ hXswap hX hlead
  refine ⟨x₀, qBad_card_le S Q hQ hcaps,
    outerBad_sum_card_le Q x₀ hQ hcaps,
    positiveNormalizedFactorPairs_card_le_unconditional Q hQ x₀
      bchksFactorMass6399 hQdeg, ?_, ?_⟩
  · simpa [outerFactors] using hx
  · intro z hz
    have hzS := (Finset.mem_sdiff.mp hz).1
    have hzNot := (Finset.mem_sdiff.mp hz).2
    have hzQBad : z ∉ qBad S Q := by
      intro hbad
      exact hzNot (Finset.mem_union_left _ hbad)
    have hQz : triSpecializeZ Q z ≠ 0 := by
      intro hzero
      apply hzQBad
      exact Finset.mem_filter.mpr ⟨hzS, hzero⟩
    have hzOuter : z ∉ (outerFactors Q).biUnion (outerBad x₀) := by
      intro hbad
      exact hzNot (Finset.mem_union_right _ hbad)
    have hsecond : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
        0 < R.natDegree → triEval R z (Pz z) = 0 →
        biSpecializeZ (triSpecializeX R x₀) z ≠ 0 := by
      intro R hRQ hRpos hRroot
      have hRouter : R ∈ outerFactors Q := by
        exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hRQ, hRpos⟩
      have hzNotBad : z ∉ outerBad x₀ R := by
        intro hbad
        exact hzOuter (Finset.mem_biUnion.mpr ⟨R, hRouter, hbad⟩)
      have hzObs : Polynomial.eval z
          (Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)) ≠ 0 := by
        intro hzero
        apply hzNotBad
        rw [outerBad, Multiset.mem_toFinset,
          Polynomial.mem_roots (hx R
            (by simpa [outerFactors] using hRouter)).2.1]
        exact hzero
      intro hzero
      apply hzObs
      have hcoeff := congrArg
        (fun B : Polynomial F => B.coeff R.natDegree) hzero
      have hleadzero : Polynomial.eval z
          (Polynomial.eval (Polynomial.C x₀) R.leadingCoeff) = 0 := by
        simpa only [biSpecializeZ, triSpecializeX, Polynomial.coeff_map,
          Polynomial.coeff_zero, Polynomial.coe_evalRingHom,
          Polynomial.leadingCoeff] using hcoeff
      rw [factorXObstruction, Polynomial.eval_mul, Polynomial.eval_mul,
        hleadzero, zero_mul]
    obtain ⟨RH, hRHpairs, hRroot, hHroot⟩ :=
      exists_positive_normalizedFactorPair Q z (Pz z) x₀ hQz
        (hQeval z hzS) hsecond
    have hmem := pair_mem_facts Q x₀ RH (by simpa [pairs] using hRHpairs)
    refine ⟨RH, ?_, hRroot, hHroot, ?_, ?_⟩
    · simpa [pairs] using hRHpairs
    · have hRouter : RH.1 ∈ outerFactors Q :=
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hmem.1, hmem.2.1⟩
      have hzNotBad : z ∉ outerBad x₀ RH.1 := by
        intro hbad
        exact hzOuter (Finset.mem_biUnion.mpr ⟨RH.1, hRouter, hbad⟩)
      intro hzero
      apply hzNotBad
      rw [outerBad, Multiset.mem_toFinset,
        Polynomial.mem_roots (hx RH.1
          (by simpa [outerFactors] using hRouter)).2.1]
      exact hzero
    · exact hsecond RH.1 hmem.1 hmem.2.1 hRroot

end UniversalOuterCover6399

end ProximityPrize.SubmissionLower
