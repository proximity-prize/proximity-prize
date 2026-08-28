import ProximityPrize.SubmissionLower.BCHKSYZFactorCap
import ProximityPrize.SubmissionLower.BCHKSResultantDegree

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate

set_option maxHeartbeats 2000000

variable {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]

/-- The product of the distinct normalized factors divides the original
polynomial.  This is the squarefree-support divisibility used by the universal
resultant ledger. -/
theorem normalizedFactors_toFinset_prod_dvd
    (B : F[X][Y]) (hB : B ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors B).toFinset.prod id ∣ B := by
  let M := UniqueFactorizationMonoid.normalizedFactors B
  have hset : M.toFinset.prod id ∣ M.prod := Multiset.toFinset_prod_dvd_prod M
  have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hB
  change M.toFinset.prod id ∣ B
  exact hset.trans hassoc.dvd

/-- Every distinct normalized factor is nonzero. -/
theorem normalizedFactor_toFinset_ne_zero
    (B H : F[X][Y])
    (hH : H ∈ (UniqueFactorizationMonoid.normalizedFactors B).toFinset) : H ≠ 0 := by
  have hm : H ∈ UniqueFactorizationMonoid.normalizedFactors B :=
    Multiset.mem_toFinset.mp hH
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor H hm).ne_zero

/-- `degreeX` is additive on a finite product of nonzero bivariate
polynomials. -/
theorem degreeX_finset_prod
    {S : Finset (F[X][Y])} (hS : ∀ H ∈ S, H ≠ 0) :
    Polynomial.Bivariate.degreeX (S.prod id) =
      ∑ H ∈ S, Polynomial.Bivariate.degreeX H := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      apply Nat.eq_zero_of_le_zero
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro i hi
      have hi0 : i = 0 := by
        by_contra hine
        exact (Polynomial.mem_support_iff.mp hi) (by simp [Polynomial.coeff_one, hine])
      subst i
      simp
  | @insert H S hHS ih =>
      have hH0 : H ≠ 0 := hS H (by simp)
      have hprod0 : S.prod id ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro J hJ
        exact hS J (by simp [hJ])
      rw [Finset.prod_insert hHS, Finset.sum_insert hHS]
      simp only [id_eq]
      calc
        Polynomial.Bivariate.degreeX (H * ∏ J ∈ S, J) =
            Polynomial.Bivariate.degreeX H +
              Polynomial.Bivariate.degreeX (∏ J ∈ S, J) := by
          apply Polynomial.Bivariate.degreeX_mul
          · exact hH0
          · simpa only [Finset.prod_apply, id_eq] using hprod0
        _ = Polynomial.Bivariate.degreeX H +
              ∑ J ∈ S, Polynomial.Bivariate.degreeX J := by
          congr 1
          simpa only [Finset.prod_apply, id_eq] using
            ih (fun J hJ ↦ hS J (by simp [hJ]))

/-- The sum of actual `Y`-degrees and the sum of actual coefficient-variable
(`Z`) degrees across all distinct normalized factors are separately bounded
by the corresponding degrees of the original bivariate polynomial. -/
theorem normalizedFactors_toFinset_sum_natDegree_degreeX_le
    (B : F[X][Y]) (hB : B ≠ 0) :
    (∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors B).toFinset,
        H.natDegree) ≤ B.natDegree ∧
    (∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors B).toFinset,
        Polynomial.Bivariate.degreeX H) ≤
      Polynomial.Bivariate.degreeX B := by
  classical
  let S := (UniqueFactorizationMonoid.normalizedFactors B).toFinset
  have hy : (∑ H ∈ S, H.natDegree) ≤ B.natDegree := by
    simpa [S] using normalizedFactors_toFinset_sum_natDegree_le B hB
  have hprod0 : S.prod id ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro H hH
    exact normalizedFactor_toFinset_ne_zero B H (by simpa [S] using hH)
  obtain ⟨C, hBC⟩ := normalizedFactors_toFinset_prod_dvd B hB
  have hC0 : C ≠ 0 := by
    intro hC
    apply hB
    rw [hBC, hC, mul_zero]
  have hzprod : Polynomial.Bivariate.degreeX (S.prod id) ≤
      Polynomial.Bivariate.degreeX B := by
    rw [hBC, Polynomial.Bivariate.degreeX_mul _ _ hprod0 hC0]
    exact Nat.le_add_right _ _
  have hzsum : (∑ H ∈ S, Polynomial.Bivariate.degreeX H) ≤
      Polynomial.Bivariate.degreeX B := by
    rw [← degreeX_finset_prod (S := S)]
    · exact hzprod
    · intro H hH
      exact normalizedFactor_toFinset_ne_zero B H (by simpa [S] using hH)
  exact ⟨hy, hzsum⟩

/-- Restricting to the positive-`Y` factors preserves both sum bounds. -/
theorem positiveNormalizedFactors_sum_natDegree_degreeX_le
    (B : F[X][Y]) (hB : B ≠ 0) :
    let S := (UniqueFactorizationMonoid.normalizedFactors B).toFinset.filter
      (fun H ↦ 0 < H.natDegree)
    (∑ H ∈ S, H.natDegree) ≤ B.natDegree ∧
    (∑ H ∈ S, Polynomial.Bivariate.degreeX H) ≤
      Polynomial.Bivariate.degreeX B := by
  classical
  dsimp only
  have hall := normalizedFactors_toFinset_sum_natDegree_degreeX_le B hB
  constructor
  · exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (by simp)).trans hall.1
  · exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (by simp)).trans hall.2

/-! ## Ordinary-resultant degree ledger -/

/-- Sum the standard bivariate degree bound while retaining each factor's
actual pre-specialization `Y`-degree. -/
theorem sum_resultant_natDegree_le_actual
    (N : F[X][Y]) (S : Finset (F[X][Y])) :
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
      (∑ H ∈ S, H.natDegree) * Polynomial.Bivariate.degreeX N +
        N.natDegree * (∑ H ∈ S, Polynomial.Bivariate.degreeX H) := by
  classical
  calc
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
        ∑ H ∈ S, (H.natDegree * Polynomial.Bivariate.degreeX N +
          N.natDegree * Polynomial.Bivariate.degreeX H) := by
      apply Finset.sum_le_sum
      intro H hH
      exact bivariate_resultant_natDegree_le N H N.natDegree H.natDegree
    _ = (∑ H ∈ S, H.natDegree) * Polynomial.Bivariate.degreeX N +
        N.natDegree * (∑ H ∈ S, Polynomial.Bivariate.degreeX H) := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

/-- Across the distinct positive normalized factors of `B`, ordinary raw
resultants against one branch-independent numerator cost at most `2*e*d*D`.
The theorem uses actual resultants; `nY` and `zN` are only upper bounds and do
not pad the Sylvester determinants. -/
theorem positiveNormalizedFactors_sum_resultant_natDegree_le_two_mul
    (B N : F[X][Y]) (hB : B ≠ 0) (d D e : ℕ)
    (hBY : B.natDegree ≤ d)
    (hBZ : Polynomial.Bivariate.degreeX B ≤ D)
    (hNY : N.natDegree ≤ e * d)
    (hNZ : Polynomial.Bivariate.degreeX N ≤ e * D) :
    let S := (UniqueFactorizationMonoid.normalizedFactors B).toFinset.filter
      (fun H ↦ 0 < H.natDegree)
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
      2 * e * d * D := by
  classical
  dsimp only
  let S := (UniqueFactorizationMonoid.normalizedFactors B).toFinset.filter
    (fun H ↦ 0 < H.natDegree)
  have hsums := positiveNormalizedFactors_sum_natDegree_degreeX_le B hB
  dsimp only at hsums
  have hsumY : (∑ H ∈ S, H.natDegree) ≤ d := hsums.1.trans hBY
  have hsumZ : (∑ H ∈ S, Polynomial.Bivariate.degreeX H) ≤ D :=
    hsums.2.trans hBZ
  calc
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
        (∑ H ∈ S, H.natDegree) * Polynomial.Bivariate.degreeX N +
          N.natDegree * (∑ H ∈ S, Polynomial.Bivariate.degreeX H) :=
      sum_resultant_natDegree_le_actual N S
    _ ≤ d * (e * D) + (e * d) * D := by gcongr
    _ = 2 * e * d * D := by ring

/-- Affine-numerator variant.  The term `s^E * Z * u₁(x)` contributes one
additional coefficient-variable degree, so `degreeX N ≤ e*D+1` yields the
exact ledger `2*e*d*D+d`. -/
theorem positiveNormalizedFactors_sum_resultant_natDegree_le_affine
    (B N : F[X][Y]) (hB : B ≠ 0) (d D e : ℕ)
    (hBY : B.natDegree ≤ d)
    (hBZ : Polynomial.Bivariate.degreeX B ≤ D)
    (hNY : N.natDegree ≤ e * d)
    (hNZ : Polynomial.Bivariate.degreeX N ≤ e * D + 1) :
    let S := (UniqueFactorizationMonoid.normalizedFactors B).toFinset.filter
      (fun H ↦ 0 < H.natDegree)
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
      2 * e * d * D + d := by
  classical
  dsimp only
  let S := (UniqueFactorizationMonoid.normalizedFactors B).toFinset.filter
    (fun H ↦ 0 < H.natDegree)
  have hsums := positiveNormalizedFactors_sum_natDegree_degreeX_le B hB
  dsimp only at hsums
  have hsumY : (∑ H ∈ S, H.natDegree) ≤ d := hsums.1.trans hBY
  have hsumZ : (∑ H ∈ S, Polynomial.Bivariate.degreeX H) ≤ D :=
    hsums.2.trans hBZ
  calc
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
        (∑ H ∈ S, H.natDegree) * Polynomial.Bivariate.degreeX N +
          N.natDegree * (∑ H ∈ S, Polynomial.Bivariate.degreeX H) :=
      sum_resultant_natDegree_le_actual N S
    _ ≤ d * (e * D + 1) + (e * d) * D := by gcongr
    _ = 2 * e * d * D + d := by ring

/-- A version with explicit finite factors and explicit sum caps, convenient
for summing one universal numerator ledger over several outer factors. -/
theorem sum_resultant_natDegree_le_two_mul_of_sum_caps
    (N : F[X][Y]) (S : Finset (F[X][Y])) (d D e : ℕ)
    (hSY : (∑ H ∈ S, H.natDegree) ≤ d)
    (hSZ : (∑ H ∈ S, Polynomial.Bivariate.degreeX H) ≤ D)
    (hNY : N.natDegree ≤ e * d)
    (hNZ : Polynomial.Bivariate.degreeX N ≤ e * D) :
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
      2 * e * d * D := by
  calc
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
        (∑ H ∈ S, H.natDegree) * Polynomial.Bivariate.degreeX N +
          N.natDegree * (∑ H ∈ S, Polynomial.Bivariate.degreeX H) :=
      sum_resultant_natDegree_le_actual N S
    _ ≤ d * (e * D) + (e * d) * D := by gcongr
    _ = 2 * e * d * D := by ring

/-- Explicit-sum-cap affine variant of the universal resultant ledger. -/
theorem sum_resultant_natDegree_le_affine_of_sum_caps
    (N : F[X][Y]) (S : Finset (F[X][Y])) (d D e : ℕ)
    (hSY : (∑ H ∈ S, H.natDegree) ≤ d)
    (hSZ : (∑ H ∈ S, Polynomial.Bivariate.degreeX H) ≤ D)
    (hNY : N.natDegree ≤ e * d)
    (hNZ : Polynomial.Bivariate.degreeX N ≤ e * D + 1) :
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
      2 * e * d * D + d := by
  calc
    (∑ H ∈ S, (Polynomial.resultant N H).natDegree) ≤
        (∑ H ∈ S, H.natDegree) * Polynomial.Bivariate.degreeX N +
          N.natDegree * (∑ H ∈ S, Polynomial.Bivariate.degreeX H) :=
      sum_resultant_natDegree_le_actual N S
    _ ≤ d * (e * D + 1) + (e * d) * D := by gcongr
    _ = 2 * e * d * D + d := by ring

/-- Sum the per-outer-factor universal resultant ledgers using only the
additive sum of actual outer `Y`-degrees. -/
theorem sum_universal_inner_ledgers_le
    {ι : Type*} [DecidableEq ι]
    (Outer : Finset ι) (dR ledger : ι → ℕ) (e D M : ℕ)
    (hledger : ∀ R ∈ Outer, ledger R ≤ 2 * e * dR R * D)
    (hdegree : (∑ R ∈ Outer, dR R) ≤ M) :
    (∑ R ∈ Outer, ledger R) ≤ 2 * e * M * D := by
  calc
    (∑ R ∈ Outer, ledger R) ≤
        ∑ R ∈ Outer, 2 * e * dR R * D := Finset.sum_le_sum hledger
    _ = 2 * e * (∑ R ∈ Outer, dR R) * D := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ 2 * e * M * D := by gcongr

/-- Aggregate the corrected affine ledgers `2*e*dR*D+dR`. -/
theorem sum_universal_inner_affine_ledgers_le
    {ι : Type*} [DecidableEq ι]
    (Outer : Finset ι) (dR ledger : ι → ℕ) (e D M : ℕ)
    (hledger : ∀ R ∈ Outer, ledger R ≤ 2 * e * dR R * D + dR R)
    (hdegree : (∑ R ∈ Outer, dR R) ≤ M) :
    (∑ R ∈ Outer, ledger R) ≤ 2 * e * M * D + M := by
  calc
    (∑ R ∈ Outer, ledger R) ≤
        ∑ R ∈ Outer, (2 * e * dR R * D + dR R) :=
      Finset.sum_le_sum hledger
    _ = 2 * e * (∑ R ∈ Outer, dR R) * D +
        (∑ R ∈ Outer, dR R) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ ≤ 2 * e * M * D + M := by gcongr

/-! ## Zero-obstruction-as-good relational capacity -/

/-- A summed relational capacity selects a branch whose obstruction is
identically zero.  Nonzero obstructions cannot be the selected branch because
all points in its fiber are distinct roots and its capacity strictly dominates
its actual degree.  The conclusion retains the large-fiber inequality needed
by the subsequent aggregate-incidence step. -/
theorem exists_zero_obstruction_with_large_fiber
    {π : Type*} [DecidableEq π]
    (S : Finset F) (P : Finset π) (Rel : F → π → Prop) [DecidableRel Rel]
    (obstruction : π → F[X]) (incidence errors : ℕ)
    (hincidence : 1 ≤ incidence)
    (hcover : ∀ z ∈ S, ∃ p ∈ P, Rel z p)
    (hroot : ∀ z ∈ S, ∀ p ∈ P, Rel z p → (obstruction p).eval z = 0)
    (hlarge :
      (∑ p ∈ P, (incidence * (obstruction p).natDegree + (errors + 1))) <
        S.card) :
    ∃ p ∈ P,
      obstruction p = 0 ∧
      incidence * (obstruction p).natDegree + (errors + 1) <
        (S.filter fun z ↦ Rel z p).card := by
  classical
  obtain ⟨p, hpP, hpLarge⟩ := exists_rel_fiber_gt_capacity S P Rel
    (fun p ↦ incidence * (obstruction p).natDegree + (errors + 1))
    hcover hlarge
  refine ⟨p, hpP, ?_, hpLarge⟩
  by_contra hp0
  have hsub : (S.filter fun z ↦ Rel z p) ⊆ (obstruction p).roots.toFinset := by
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    have hzRel := (Finset.mem_filter.mp hz).2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact hroot z hzS p hpP hzRel
  have hcard : (S.filter fun z ↦ Rel z p).card ≤ (obstruction p).natDegree := by
    calc
      (S.filter fun z ↦ Rel z p).card ≤
          (obstruction p).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (obstruction p).roots.card := Multiset.toFinset_card_le _
      _ ≤ (obstruction p).natDegree := Polynomial.card_roots' _
  have hdeg_lt_cap : (obstruction p).natDegree <
      incidence * (obstruction p).natDegree + (errors + 1) := by
    have hmul : (obstruction p).natDegree ≤
        incidence * (obstruction p).natDegree := by
      simpa [Nat.one_mul] using
        Nat.mul_le_mul_right (obstruction p).natDegree hincidence
    omega
  omega

/-- Exact fused-floor companion: once the global capacity theorem has selected
a branch above `(nminus * deg)/gap + errors+1`, root counting forces its
obstruction to be identically zero whenever `gap ≤ nminus`. -/
theorem obstruction_eq_zero_of_fused_floor_large_fiber
    {π : Type*}
    (S : Finset F) (Rel : F → π → Prop) [DecidableRel Rel]
    (obstruction : π → F[X]) (p : π) (nminus gap errors : ℕ)
    (hgap : 0 < gap) (hgap_le : gap ≤ nminus)
    (hroot : ∀ z ∈ S, Rel z p → (obstruction p).eval z = 0)
    (hlarge : (nminus * (obstruction p).natDegree) / gap + (errors + 1) <
      (S.filter fun z ↦ Rel z p).card) :
    obstruction p = 0 := by
  classical
  by_contra hp0
  have hsub : (S.filter fun z ↦ Rel z p) ⊆ (obstruction p).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact hroot z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2
  have hcard : (S.filter fun z ↦ Rel z p).card ≤ (obstruction p).natDegree := by
    calc
      (S.filter fun z ↦ Rel z p).card ≤
          (obstruction p).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (obstruction p).roots.card := Multiset.toFinset_card_le _
      _ ≤ (obstruction p).natDegree := Polynomial.card_roots' _
  have hdeg_div : (obstruction p).natDegree ≤
      (nminus * (obstruction p).natDegree) / gap := by
    rw [Nat.le_div_iff_mul_le hgap]
    have hm := Nat.mul_le_mul_right (obstruction p).natDegree hgap_le
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm
  omega

end ProximityPrize.SubmissionLower


