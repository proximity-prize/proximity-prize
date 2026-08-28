import ProximityPrize.SubmissionLower.BCHKSUniversalGlobalCapacity
import ProximityPrize.SubmissionLower.BCHKSUniversalFactorSums
import ProximityPrize.SubmissionLower.BCHKSParameters6399
import ProximityPrize.SubmissionLower.BCHKSDoubleCounting

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial
open scoped BigOperators

set_option maxHeartbeats 2000000

/-- Convert the exact selected-pair incidence inequality into `k+1` concrete
RS coordinates whose selected-seed fibers are larger than the pair's actual
resultant degree. -/
theorem exists_large_universal_coordinates_6399
    (T : Finset IRSProfile.Field)
    (Arow : IRSProfile.Field → Finset IRSProfile.Index)
    (resultantDegree : ℕ)
    (hrow : ∀ z ∈ T, 262144 - bchksErrors6399 ≤ (Arow z).card)
    (hincidence : (262144 - 131071) * resultantDegree <
      (262144 - bchksErrors6399 - 131071) * T.card) :
    ∃ Coord : Finset IRSProfile.Index,
      131072 ≤ Coord.card ∧
      ∀ i ∈ Coord, resultantDegree <
        (T.filter fun z => i ∈ Arow z).card := by
  classical
  let Coord : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    resultantDegree < (T.filter fun z => i ∈ Arow z).card
  have hcard : 131072 ≤ Coord.card := by
    simpa [Coord] using many_large_fibers T Arow 262144 bchksErrors6399
      131071 resultantDegree (by norm_num [IRSProfile.Index]) hrow
      (by simpa [Nat.mul_comm] using hincidence)
  refine ⟨Coord, hcard, ?_⟩
  intro i hi
  exact (Finset.mem_filter.mp hi).2

/-- Root counting on each large coordinate fiber forces its ordinary
resultant obstruction to vanish identically in `Z`. -/
theorem universal_coordinate_obstructions_eq_zero
    (T : Finset IRSProfile.Field)
    (Arow : IRSProfile.Field → Finset IRSProfile.Index)
    (Coord : Finset IRSProfile.Index) (resultantDegree : ℕ)
    (obstruction : IRSProfile.Index → IRSProfile.Field[X])
    (hlarge : ∀ i ∈ Coord, resultantDegree <
      (T.filter fun z => i ∈ Arow z).card)
    (hdegree : ∀ i ∈ Coord, (obstruction i).natDegree ≤ resultantDegree)
    (hroot : ∀ i ∈ Coord, ∀ z ∈ T, i ∈ Arow z →
      (obstruction i).eval z = 0) :
    ∀ i ∈ Coord, obstruction i = 0 := by
  intro i hi
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (obstruction i) (T.filter fun z => i ∈ Arow z)
  · intro z hz
    exact hroot i hi z (Finset.mem_filter.mp hz).1
      (Finset.mem_filter.mp hz).2
  · exact (hdegree i hi).trans_lt (hlarge i hi)

/-- The exact aggregate capacity over the concrete nested-factor finset.  The
inner sum uses the actual `Y`- and `Z`-degree masses of the distinct factors;
the outer sum then uses only the total `Y`-degree mass of `Q`. -/
noncomputable def universalPairResultantCapacity (E D : ℕ)
    (RH : Polynomial (Polynomial (Polynomial IRSProfile.Field)) ×
      Polynomial (Polynomial IRSProfile.Field)) : ℕ :=
  RH.2.natDegree * (E * D) +
    (E * RH.1.natDegree) * Bivariate.degreeX RH.2

/-- Sharp coefficient-variable cap after specializing the middle variable of
a normalized outer factor.  A strict `Z+Y < D+1` support cap gives `≤ D`,
with no lost unit. -/
theorem normalizedFactor_triSpecializeX_degreeX_le
    (Q R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (x₀ : IRSProfile.Field) (D : ℕ) (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < D + 1) :
    Bivariate.degreeX (triSpecializeX R x₀) ≤ D := by
  have hRYZ := YZFactorCap.normalizedFactor_YZ_cap Q R (D + 1) hQ hRQ hcap
  have hcoeffCap : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D := by
    intro j
    unfold Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    have h := hRYZ j a (Polynomial.mem_support_iff.mp ha)
    omega
  have hevalCap : ∀ p : Polynomial (Polynomial IRSProfile.Field),
      Bivariate.degreeX p ≤ D →
      (Polynomial.eval (Polynomial.C x₀) p).natDegree ≤ D := by
    intro p hp
    have heq : (Bivariate.swap p).map (Polynomial.evalRingHom x₀) =
        Polynomial.eval (Polynomial.C x₀) p := by
      rw [← Bivariate.evalX_eq_map]
      exact (Bivariate.evalY_eq_evalX_swap x₀ p).symm
    rw [← heq]
    exact Polynomial.natDegree_map_le.trans (by
      rw [show (Bivariate.swap p).natDegree =
        Bivariate.natDegreeY (Bivariate.swap p) from rfl,
        Bivariate.natDegreeY_swap]
      exact hp)
  unfold Bivariate.degreeX
  apply Finset.sup_le
  intro j hj
  simp only [triSpecializeX, Polynomial.coeff_map]
  exact hevalCap (R.coeff j) (hcoeffCap j)

theorem positiveNormalizedFactorPairs_universal_capacity_le
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hQ : Q ≠ 0) (x₀ : IRSProfile.Field)
    (E D M : ℕ) (hQdeg : Q.natDegree ≤ M)
    (hBZ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      Bivariate.degreeX (triSpecializeX R x₀) ≤ D) :
    (∑ RH ∈ positiveNormalizedFactorPairs Q x₀,
      universalPairResultantCapacity E D RH) ≤
      2 * E * M * D := by
  classical
  let Outer := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
  let Inner := fun R : Polynomial (Polynomial (Polynomial IRSProfile.Field)) =>
    (UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX R x₀)).toFinset.filter fun H => 0 < H.natDegree
  let PairSet := fun R : Polynomial (Polynomial (Polynomial IRSProfile.Field)) =>
    (Inner R).image fun H => (R, H)
  let cost := universalPairResultantCapacity E D
  have hdisj : Set.PairwiseDisjoint (↑Outer) PairSet := by
    intro R hR J hJ hne
    change Disjoint (PairSet R) (PairSet J)
    rw [Finset.disjoint_left]
    intro RH hRHp hJHp
    obtain ⟨HR, hHR, hRHeq⟩ := Finset.mem_image.mp hRHp
    obtain ⟨HJ, hHJ, hJHeq⟩ := Finset.mem_image.mp hJHp
    have hfirst : R = J := by
      simpa only [Prod.mk.injEq] using congrArg Prod.fst (hRHeq.trans hJHeq.symm)
    exact hne hfirst
  have hinner : ∀ R ∈ Outer,
      (∑ RH ∈ PairSet R, cost RH) ≤ 2 * E * R.natDegree * D := by
    intro R hR
    let B := triSpecializeX R x₀
    by_cases hB : B = 0
    · simp [PairSet, Inner, B, hB]
    · have hsums := positiveNormalizedFactors_sum_natDegree_degreeX_le B hB
      dsimp only at hsums
      have hsumY : (∑ H ∈ Inner R, H.natDegree) ≤ R.natDegree := by
        exact hsums.1.trans (triSpecializeX_natDegree_le R x₀)
      have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
        Multiset.mem_toFinset.mp hR
      have hsumZ : (∑ H ∈ Inner R, Bivariate.degreeX H) ≤ D := by
        exact hsums.2.trans (hBZ R hRQ)
      let innerCost : Polynomial (Polynomial IRSProfile.Field) → ℕ := fun H =>
        H.natDegree * (E * D) +
          (E * R.natDegree) * Bivariate.degreeX H
      calc
        (∑ RH ∈ PairSet R, cost RH) =
            (∑ H ∈ Inner R, innerCost H) := by
          simp [PairSet, cost, innerCost, universalPairResultantCapacity]
        _ = (∑ H ∈ Inner R, H.natDegree) * (E * D) +
              (E * R.natDegree) *
                (∑ H ∈ Inner R, Bivariate.degreeX H) := by
          simp [innerCost, Finset.sum_add_distrib, Finset.sum_mul,
            Finset.mul_sum]
        _ ≤ R.natDegree * (E * D) + (E * R.natDegree) * D := by
          gcongr
        _ = 2 * E * R.natDegree * D := by ring
  calc
    (∑ RH ∈ positiveNormalizedFactorPairs Q x₀,
        universalPairResultantCapacity E D RH) =
        ∑ R ∈ Outer, ∑ RH ∈ PairSet R, cost RH := by
      change (∑ RH ∈ Outer.biUnion PairSet, cost RH) = _
      rw [Finset.sum_biUnion hdisj]
    _ ≤ ∑ R ∈ Outer, 2 * E * R.natDegree * D :=
      Finset.sum_le_sum hinner
    _ = 2 * E * (∑ R ∈ Outer, R.natDegree) * D := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ 2 * E * M * D := by
      gcongr
      exact (normalizedFactors_toFinset_sum_natDegree_le Q hQ).trans hQdeg

/-- The numerical all-pair selection step for the universal-numerator route.

The exceptional `Z`-specializations of the interpolant are charged once, and
the outer-factor exceptional sets are charged once per outer factor.  The
ordinary-resultant degree capacities are summed before the exact floor
conversion.  The selected pair retains both the incidence inequality and the
`errors+1` cardinality inequality.  Its coordinate-dependent resultants are
handled only after the subsequent row-to-column double count. -/
theorem exists_large_universal_pair_6399
    {A P : Type*} [DecidableEq A] [DecidableEq P]
    (S QBad : Finset IRSProfile.Field)
    (Outer : Finset A) (OuterBad : A → Finset IRSProfile.Field)
    (Pairs : Finset P) (Rel : IRSProfile.Field → P → Prop) [DecidableRel Rel]
    (resultantDegree : P → ℕ)
    (hS : bchksNumerator6399 < S.card)
    (hQ : QBad.card ≤ bchksZCap6399)
    (hOuter : (∑ a ∈ Outer, (OuterBad a).card) ≤
      2 * bchksZCap6399 * bchksFactorMass6399)
    (hresult : (∑ p ∈ Pairs, resultantDegree p) ≤
      2 * bchksUniversalExponent6399 * bchksFactorMass6399 *
        bchksFactorZMass6399 + bchksFactorMass6399)
    (hpairs : Pairs.card ≤ bchksFactorMass6399)
    (hcover : ∀ z ∈ S \ (QBad ∪ Outer.biUnion OuterBad),
      ∃ p ∈ Pairs, Rel z p) :
    ∃ p ∈ Pairs,
      (262144 - 131071) * resultantDegree p <
        (262144 - bchksErrors6399 - 131071) *
          ((S \ (QBad ∪ Outer.biUnion OuterBad)).filter
            fun z => Rel z p).card ∧
      bchksErrors6399 + 1 <
        ((S \ (QBad ∪ Outer.biUnion OuterBad)).filter
          fun z => Rel z p).card := by
  classical
  let resultCap :=
    2 * bchksUniversalExponent6399 * bchksFactorMass6399 *
      bchksFactorZMass6399 + bchksFactorMass6399
  let fusedCap :=
    bchksIncidenceCoefficient6399 * bchksFactorMass6399 *
      bchksFactorZMass6399
  let gap := 262144 - bchksErrors6399 - 131071
  have hlarge :
      bchksZCap6399 +
          2 * bchksZCap6399 * bchksFactorMass6399 +
        (fusedCap + (bchksErrors6399 + 1) * bchksFactorMass6399) <
          S.card := by
    have hbudget :
        bchksZCap6399 +
            2 * bchksZCap6399 * bchksFactorMass6399 +
          (fusedCap + (bchksErrors6399 + 1) * bchksFactorMass6399) <
            bchksNumerator6399 := by
      norm_num [fusedCap, bchksZCap6399, bchksFactorMass6399,
        bchksFactorZMass6399, bchksIncidenceCoefficient6399,
        bchksErrors6399, bchksNumerator6399]
    exact hbudget.trans hS
  have hfused : (262144 - 131071) * resultCap ≤ gap * fusedCap := by
    simpa [resultCap, fusedCap, gap] using bchks6399_fused_incidence
  obtain ⟨p, hp, hpLarge⟩ :=
    exists_pair_fiber_of_fused_resultant_ledger
      S QBad Outer OuterBad Pairs Rel resultantDegree
      (262144 - 131071) gap bchksErrors6399 bchksZCap6399
      (2 * bchksZCap6399 * bchksFactorMass6399) resultCap
      bchksFactorMass6399 fusedCap hQ hOuter (by simpa [resultCap] using hresult)
      hpairs hfused hcover hlarge
  let Fib : Finset IRSProfile.Field :=
    (S \ (QBad ∪ Outer.biUnion OuterBad)).filter fun z => Rel z p
  have hpLarge' :
      ((262144 - 131071) * resultantDegree p) / gap +
          (bchksErrors6399 + 1) < Fib.card := by
    simpa [Fib] using hpLarge
  have hbounds := scaled_pair_capacity_implies_incidence
    (262144 - 131071) gap (resultantDegree p)
    bchksErrors6399 Fib.card
    (by simpa [gap] using bchks6399_gap_pos) hpLarge'
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [Fib, gap] using hbounds.1
  · simpa [Fib] using hbounds.2

end ProximityPrize.SubmissionLower
