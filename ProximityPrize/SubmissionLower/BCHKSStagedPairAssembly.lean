import ProximityPrize.SubmissionLower.BCHKSStagedConcrete
import ProximityPrize.SubmissionLower.BCHKSStagedSelection
import ProximityPrize.SubmissionLower.BCHKSStagedArithmetic
import ProximityPrize.SubmissionLower.BCHKSPairSetupConcrete

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Concrete normalized-factor selection with a pair budget chosen after the
first-stage factor is known. -/
theorem exists_concrete_staged_factor_selection_by_factor
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (x₀ : Polynomial (Polynomial (Polynomial F)) → F)
    (Bad : Polynomial (Polynomial (Polynomial F)) → Finset F)
    (badCap pairCost : Polynomial (Polynomial (Polynomial F)) → Nat)
    (e : Nat)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hx : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → triSpecializeX R (x₀ R) ≠ 0)
    (hBadCap : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → (Bad R).card ≤ badCap R)
    (hsecond : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → ∀ z ∈ S \ Bad R,
        biSpecializeZ (triSpecializeX R (x₀ R)) z ≠ 0)
    (hglobal :
      (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        (pairCost R * R.natDegree + e * R.natDegree + badCap R)) < S.card) :
    ∃ R H T,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R (x₀ R)) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ Bad R) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval (x₀ R) (P z)) z = 0) ∧
      pairCost R * H.natDegree + e < T.card := by
  classical
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    fun R => 0 < R.natDegree
  let Hs : Polynomial (Polynomial (Polynomial F)) → Finset (Polynomial (Polynomial F)) :=
    fun R => (UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX R (x₀ R))).toFinset.filter fun H => 0 < H.natDegree
  let RelR : F → Polynomial (Polynomial (Polynomial F)) → Prop :=
    fun z R => triEval R z (P z) = 0
  let RelH : F → Polynomial (Polynomial (Polynomial F)) →
      Polynomial (Polynomial F) → Prop :=
    fun z R H => biEval H (Polynomial.eval (x₀ R) (P z)) z = 0
  have hRcover : ∀ z ∈ S, ∃ R ∈ Rs, RelR z R := by
    intro z hz
    obtain ⟨R, hRQ, hRpos, hzero⟩ :=
      exists_positive_normalizedFactor_triEval_eq_zero Q z (P z)
        (hQz z hz) (hQeval z hz)
    exact ⟨R, by simp [Rs, hRQ, hRpos], hzero⟩
  have hHpos : ∀ R ∈ Rs, ∀ H ∈ Hs R, 0 < H.natDegree := by
    intro R hR H hH
    exact (Finset.mem_filter.mp hH).2
  have hHsum : ∀ R ∈ Rs, (∑ H ∈ Hs R, H.natDegree) ≤ R.natDegree := by
    intro R hR
    have hRm := Finset.mem_filter.mp hR
    have hRX := hx R (by simpa [Rs] using hRm.1) hRm.2
    calc
      (∑ H ∈ Hs R, H.natDegree) ≤
          ∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors
            (triSpecializeX R (x₀ R))).toFinset, H.natDegree := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ (triSpecializeX R (x₀ R)).natDegree :=
        normalizedFactors_toFinset_sum_natDegree_le _ hRX
      _ ≤ R.natDegree := triSpecializeX_natDegree_le R (x₀ R)
  have hHcover : ∀ R ∈ Rs, ∀ z ∈ (S.filter fun z => RelR z R) \ Bad R,
      ∃ H ∈ Hs R, RelH z R H := by
    intro R hR z hz
    have hRm := Finset.mem_filter.mp hR
    have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
      simpa [Rs] using hRm.1
    have hzS : z ∈ S := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1
    have hzgood : z ∈ S \ Bad R :=
      Finset.mem_sdiff.mpr ⟨hzS, (Finset.mem_sdiff.mp hz).2⟩
    have hRzero : RelR z R := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2
    have hpoint : biEval (triSpecializeX R (x₀ R))
        (Polynomial.eval (x₀ R) (P z)) z = 0 := by
      rw [← eval_triEval_eq_biEval_triSpecializeX, hRzero]
      simp
    obtain ⟨H, hHR, hHp, hHzero⟩ :=
      exists_positive_normalizedFactor_biEval_eq_zero
        (triSpecializeX R (x₀ R)) z (Polynomial.eval (x₀ R) (P z))
        (hsecond R hRQ hRm.2 z hzgood) hpoint
    exact ⟨H, by simp [Hs, hHR, hHp], hHzero⟩
  have hBad : ∀ R ∈ Rs,
      ((S.filter fun z => RelR z R) ∩ Bad R).card ≤ badCap R := by
    intro R hR
    apply (Finset.card_le_card Finset.inter_subset_right).trans
    have hm := Finset.mem_filter.mp hR
    exact hBadCap R (by simpa [Rs] using hm.1) hm.2
  obtain ⟨R, hRs, H, hHs, T, hTS, hTbad, hrel, hmargin⟩ :=
    exists_staged_weighted_selection_by_factor S Rs Hs Polynomial.natDegree
      Polynomial.natDegree badCap pairCost e RelR RelH Bad hRcover
      (by simpa [Rs] using hglobal) hBad hHpos hHsum hHcover
  have hRm := Finset.mem_filter.mp hRs
  have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
    simpa [Rs] using hRm.1
  have hHm := Finset.mem_filter.mp hHs
  have hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX R (x₀ R)) := by simpa [Hs] using hHm.1
  exact ⟨R, H, T, hRQ, hRm.2, hHR, hHm.2, hTS, hTbad, hrel, hmargin⟩

/-- Uniform good-specialization data for the positive normalized factors of
`Q`, relative to the source set on which staged selection is performed. -/
structure StagedGoodFamily
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (S : Finset F) where
  x₀ : Polynomial (Polynomial (Polynomial F)) → F
  Bad : Polynomial (Polynomial (Polynomial F)) → Finset F
  badCap : Polynomial (Polynomial (Polynomial F)) → Nat
  specialize_ne_zero : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree → triSpecializeX R (x₀ R) ≠ 0
  primitive : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree →
      (Polynomial.Bivariate.evalX (Polynomial.C (x₀ R)) R).IsPrimitive
  bad_card : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree → (Bad R).card ≤ badCap R
  bad_cap : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree → badCap R ≤ 2 * R.natDegree * 519143
  second_ne_zero : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree → ∀ z ∈ S \ Bad R,
      biSpecializeZ (triSpecializeX R (x₀ R)) z ≠ 0

/-- Staged selection, arithmetic accounting, and pair setup in one theorem. -/
theorem exists_staged_pair_with_setup
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (G : StagedGoodFamily Q S)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hQY : Q.natDegree ≤ 851)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 519143)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 111624646)
    (hcard : 632176 * 519142 * 851 ^ 2 +
      (bchksErrors + 1) * 851 + 2 * 519143 * 851 < S.card) :
    ∃ R H T,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R (G.x₀ R)) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ G.Bad R) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval (G.x₀ R) (P z)) z = 0) ∧
      (if R.natDegree = 1 then 2 * 111624646 * 519142
        else 632176 * 519142 * R.natDegree) * H.natDegree +
        (bchksErrors + 1) < T.card ∧
      Irreducible R ∧ Irreducible H ∧ H ∣ triSpecializeX R (G.x₀ R) ∧
      R.natDegree ≤ 852 ∧ H.natDegree ≤ 852 ∧
      Polynomial.Bivariate.totalDegree H ≤ 519142 ∧
      Polynomial.Bivariate.totalDegree (triSpecializeX R (G.x₀ R)) ≤ 519142 ∧
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
        a + 131071 * j < 111624646) ∧
      RationalFunctions.HenselNumerators.Hypotheses (G.x₀ R) R H := by
  let pairCost : Polynomial (Polynomial (Polynomial F)) → Nat := fun R =>
    if R.natDegree = 1 then 2 * 111624646 * 519142
    else 632176 * 519142 * R.natDegree
  have hsum :
      (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        (pairCost R * R.natDegree +
          (bchksErrors + 1) * R.natDegree + G.badCap R)) ≤
        632176 * 519142 * 851 ^ 2 +
          (bchksErrors + 1) * 851 + 2 * 519143 * 851 := by
    simpa [pairCost] using positive_normalizedFactors_mixed_cap_le
      Q hQ G.badCap (2 * 111624646 * 519142) (632176 * 519142)
      (bchksErrors + 1) 519143 851 hQY (by norm_num)
      (by
        intro R hR
        have hm := Finset.mem_filter.mp hR
        exact G.bad_cap R (by simpa using hm.1) hm.2)
  have hglobal :
      (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        (pairCost R * R.natDegree +
          (bchksErrors + 1) * R.natDegree + G.badCap R)) < S.card :=
    hsum.trans_lt hcard
  obtain ⟨R, H, T, hRQ, hRpos, hHR, hHpos, hTS, hTbad, hvan, hmargin⟩ :=
    exists_concrete_staged_factor_selection_by_factor S P Q G.x₀ G.Bad G.badCap
      pairCost (bchksErrors + 1) hQ hQeval hQz
      G.specialize_ne_zero G.bad_card G.second_ne_zero hglobal
  have hp := bchks_pair_setup_of_selected_factors Q R H (G.x₀ R)
    hQ hRQ hHR hHpos (hQY.trans (by omega)) hQYZ hQweightedX
      (G.primitive R hRQ hRpos)
  rcases hp with ⟨hRirr, hHirr, -, hHd, hRdeg, hHdeg, hHtot, hRXtot, hweight, hHyp⟩
  exact ⟨R, H, T, hRQ, hRpos, hHR, hHpos, hTS, hTbad, hvan,
    by simpa [pairCost] using hmargin,
    hRirr, hHirr, hHd, hRdeg, hHdeg, hHtot, hRXtot, hweight, hHyp⟩

end ProximityPrize.SubmissionLower
