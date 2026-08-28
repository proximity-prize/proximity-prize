import ProximityPrize.SubmissionLower.BCHKSYZFactorCap
import ProximityPrize.SubmissionLower.BCHKSParameters6400
import ProximityPrize.SubmissionLower.BCHKSConcreteNumerators

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

/-- The exact score-64 ledger after deleting the disappearing `Z`-fibers and
reserving one sparse-quadratic threshold for every possible positive-`Y`
factor. -/
lemma bchks_fixed_factor_seed_budget6400 :
    63521 * (1133 * 2 * 1898945373 + 1) + 1898945373 <
      bchksNumerator6400 := by
  norm_num [bchksNumerator6400]

/-- The factor-specific `Z+Y` ledger is dramatically sharper than charging
the global `YZ` cap once for every positive factor. -/
lemma bchks_factor_specific_yz_seed_budget6400 :
    144802557 * 1898945373 + 63521 + 1898945373 <
      bchksNumerator6400 := by
  norm_num [bchksNumerator6400]

/-- The concrete support cap bounds the additive `Z+Y` support degree used by
the factor-specific selector. -/
theorem yzSupportDegree_le_1898945373_of_caps6400
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (hcaps : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      j < 63522 ∧ a + 131071 * j < 8325809424 ∧
        ((Q.coeff j).coeff a).natDegree + j < 1898945374) :
    YZFactorCap.yzSupportDegree Q 1 ≤ 1898945373 := by
  classical
  unfold YZFactorCap.yzSupportDegree
  apply Finset.sup_le
  intro j hj
  have hj0 : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  obtain ⟨a, ha, hadeg, -⟩ :=
    Polynomial.Bivariate.exists_max_index_degreeX (Q.coeff j) hj0
  have hca : (Q.coeff j).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
  have hcap := (hcaps j a hca).2.2
  rw [← hadeg]
  norm_num
  omega

/-- A positive outer factor has `Y`-degree at most its own `Z+Y` support
degree. -/
theorem natDegree_le_yzSupportDegree_one
    {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (hR : R ≠ 0) :
    R.natDegree ≤ YZFactorCap.yzSupportDegree R 1 := by
  have hlead : R.coeff R.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hR
  have hh := YZFactorCap.coeffWeight_le_of_ne R 1 R.natDegree hlead
  norm_num at hh
  exact (Nat.le_add_left _ _).trans hh

/-- A trivariate polynomial satisfies the coefficientwise `YZCap` at its
own additive `Z+Y` support degree. -/
theorem yzCap_yzSupportDegree_one
    {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) :
    RationalFunctions.HenselNumerators.ConcreteFiniteNumerators.YZCap R
      (YZFactorCap.yzSupportDegree R 1) := by
  intro j a ha
  have hj : R.coeff j ≠ 0 := by
    intro hj0
    exact ha (by simp [hj0])
  have hweight := YZFactorCap.coeffWeight_le_of_ne R 1 j hj
  have hcoeff := Polynomial.Bivariate.coeff_natDegree_le_degreeX
    (R.coeff j) a
  norm_num at hweight
  omega

/-- Strong score-64 fixed-factor selection using each factor's actual
`Z+Y` support degree.  Additivity across the normalized factorization means
the global degree cap is paid once, yielding a coefficient over sixty-three
thousand times larger than the uniform-cap selector above. -/
theorem exists_fixed_positive_factor_factorYZ6400
    (S : Finset IRSProfile.Field)
    (P : ↑S → Polynomial IRSProfile.Field)
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (hcaps : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      j < 63522 ∧ a + 131071 * j < 8325809424 ∧
        ((Q.coeff j).coeff a).natDegree + j < 1898945374)
    (hQeval : ∀ z : ↑S, triEval Q z.1 (P z) = 0)
    (hS : bchksNumerator6400 < S.card) :
    ∃ R : Polynomial (Polynomial (Polynomial IRSProfile.Field)),
      ∃ T : Finset IRSProfile.Field,
        R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        0 < R.natDegree ∧
        144802557 * YZFactorCap.yzSupportDegree R 1 < T.card ∧
        144802557 * R.natDegree < T.card ∧
        ∃ hTsub : T ⊆ S,
          (∀ z ∈ T, triSpecializeZ Q z ≠ 0) ∧
          ∀ z, ∀ hz : z ∈ T,
            triEval R z (P ⟨z, hTsub hz⟩) = 0 := by
  classical
  let Candidates :=
    (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R => 0 < R.natDegree)
  have hQdeg : Q.natDegree ≤ 63521 := by
    have hlead : Q.coeff Q.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hQ
    obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlead
    have ha0 : (Q.coeff Q.natDegree).coeff a ≠ 0 :=
      Polynomial.mem_support_iff.mp ha
    have := (hcaps Q.natDegree a ha0).1
    omega
  have hCandidates : Candidates.card ≤ 63521 := by
    calc
      Candidates.card = ∑ _R ∈ Candidates, 1 := by simp
      _ ≤ ∑ R ∈ Candidates, R.natDegree := by
        apply Finset.sum_le_sum
        intro R hR
        exact (Finset.mem_filter.mp hR).2
      _ ≤ ∑ R ∈
          (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          R.natDegree := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        simp
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 63521 := hQdeg
  have hYZsum :
      (∑ R ∈ Candidates, YZFactorCap.yzSupportDegree R 1) ≤
        1898945373 := by
    calc
      (∑ R ∈ Candidates, YZFactorCap.yzSupportDegree R 1) ≤
          ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
            YZFactorCap.yzSupportDegree R 1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        simp
      _ ≤ YZFactorCap.yzSupportDegree Q 1 :=
        YZFactorCap.normalizedFactors_toFinset_sum_yzSupportDegree_le Q 1 hQ
      _ ≤ 1898945373 :=
        yzSupportDegree_le_1898945373_of_caps6400 Q hQ hcaps
  let Bad := badZSpecializations Q S
  let Good := S \ Bad
  have hBadSub : Bad ⊆ S := Finset.filter_subset _ _
  have hBad : Bad.card ≤ 1898945373 := by
    have hlt : Bad.card < 1898945374 := by
      apply badZSpecializations_card_lt_of_forall_coeff Q hQ S 1898945374
      intro j a hja
      have hh := (hcaps j a hja).2.2
      omega
    omega
  have hGoodLarge :
      144802557 * 1898945373 + 63521 < Good.card := by
    have hGoodCard : Good.card = S.card - Bad.card := by
      dsimp [Good]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBadSub]
    rw [hGoodCard]
    apply Nat.lt_sub_of_add_lt
    exact (Nat.add_le_add_left hBad _).trans_lt
      (bchks_factor_specific_yz_seed_budget6400.trans hS)
  have hCapacitySum :
      (∑ R ∈ Candidates,
        (144802557 * YZFactorCap.yzSupportDegree R 1 + 1)) ≤
          144802557 * 1898945373 + 63521 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left 144802557 hYZsum)
      (by simpa using hCandidates)
  let PAt : IRSProfile.Field → Polynomial IRSProfile.Field :=
    fun z => if hz : z ∈ S then P ⟨z, hz⟩ else 0
  let Rel : IRSProfile.Field →
      Polynomial (Polynomial (Polynomial IRSProfile.Field)) → Prop :=
    fun z R => triEval R z (PAt z) = 0
  have hcover : ∀ z ∈ Good, ∃ R ∈ Candidates, Rel z R := by
    intro z hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hzNotBad : z ∉ Bad := (Finset.mem_sdiff.mp hz).2
    have hQz : triSpecializeZ Q z ≠ 0 := by
      intro hzero
      apply hzNotBad
      exact Finset.mem_filter.mpr ⟨hzS, hzero⟩
    obtain ⟨R, hRQ, hRpos, hRzero⟩ :=
      exists_positive_normalizedFactor_triEval_eq_zero Q z (P ⟨z, hzS⟩)
        hQz (hQeval ⟨z, hzS⟩)
    refine ⟨R, Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hRQ, hRpos⟩, ?_⟩
    simpa [Rel, PAt, hzS] using hRzero
  obtain ⟨R, hRCandidates, hRlarge⟩ :=
    exists_rel_fiber_gt_capacity Good Candidates Rel
      (fun R => 144802557 * YZFactorCap.yzSupportDegree R 1 + 1)
      hcover (hCapacitySum.trans_lt hGoodLarge)
  let T := Good.filter fun z => Rel z R
  have hTsub : T ⊆ S := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hRdata := Finset.mem_filter.mp hRCandidates
  have hR0 : R ≠ 0 :=
    UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hRdata.1)
  refine ⟨R, T, Multiset.mem_toFinset.mp hRdata.1, hRdata.2, ?_, ?_,
    hTsub, ?_, ?_⟩
  · have : 144802557 * YZFactorCap.yzSupportDegree R 1 + 1 < T.card := by
      simpa [T] using hRlarge
    omega
  · have hdeg := natDegree_le_yzSupportDegree_one R hR0
    have hmul : 144802557 * R.natDegree ≤
        144802557 * YZFactorCap.yzSupportDegree R 1 :=
      Nat.mul_le_mul_left 144802557 hdeg
    exact hmul.trans_lt (by
      have : 144802557 * YZFactorCap.yzSupportDegree R 1 + 1 < T.card := by
        simpa [T] using hRlarge
      omega)
  · intro z hz
    have hzGood := (Finset.mem_filter.mp hz).1
    have hzNotBad := (Finset.mem_sdiff.mp hzGood).2
    intro hzero
    apply hzNotBad
    exact Finset.mem_filter.mpr ⟨hTsub hz, hzero⟩
  · intro z hz
    have hrel := (Finset.mem_filter.mp hz).2
    simpa [Rel, PAt, hTsub hz] using hrel

/-- A score-64 interpolant has one fixed positive-`Y` irreducible factor that
vanishes on more than the sparse-quadratic threshold of challenge rows.

The point of selecting only positive-`Y` factors is that coefficient/content
factors cost nothing in this pigeonhole: the number of candidates is bounded
by the sum of their positive outer degrees, hence by `deg_Y Q`. -/
theorem exists_fixed_positive_factor6400
    (S : Finset IRSProfile.Field)
    (P : ↑S → Polynomial IRSProfile.Field)
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (hcaps : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      j < 63522 ∧ a + 131071 * j < 8325809424 ∧
        ((Q.coeff j).coeff a).natDegree + j < 1898945374)
    (hQeval : ∀ z : ↑S, triEval Q z.1 (P z) = 0)
    (hS : bchksNumerator6400 < S.card) :
    ∃ R : Polynomial (Polynomial (Polynomial IRSProfile.Field)),
      ∃ T : Finset IRSProfile.Field,
        R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        0 < R.natDegree ∧
        1133 * 2 * 1898945373 * R.natDegree < T.card ∧
        1133 * 2 * 1898945373 < T.card ∧
        ∃ hTsub : T ⊆ S,
          (∀ z ∈ T, triSpecializeZ Q z ≠ 0) ∧
          ∀ z, ∀ hz : z ∈ T,
            triEval R z (P ⟨z, hTsub hz⟩) = 0 := by
  classical
  have hQdeg : Q.natDegree ≤ 63521 := by
    have hlead : Q.coeff Q.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hQ
    obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlead
    have ha0 : (Q.coeff Q.natDegree).coeff a ≠ 0 :=
      Polynomial.mem_support_iff.mp ha
    have := (hcaps Q.natDegree a ha0).1
    omega
  let Candidates :=
    (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R => 0 < R.natDegree)
  have hCandidates : Candidates.card ≤ 63521 := by
    calc
      Candidates.card = ∑ _R ∈ Candidates, 1 := by simp
      _ ≤ ∑ R ∈ Candidates, R.natDegree := by
        apply Finset.sum_le_sum
        intro R hR
        exact (Finset.mem_filter.mp hR).2
      _ ≤ ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          R.natDegree := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        simp
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 63521 := hQdeg
  have hDegreeSum : (∑ R ∈ Candidates, R.natDegree) ≤ 63521 := by
    calc
      (∑ R ∈ Candidates, R.natDegree) ≤
          ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
            R.natDegree := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        simp
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 63521 := hQdeg
  let Bad := badZSpecializations Q S
  let Good := S \ Bad
  have hBadSub : Bad ⊆ S := by
    exact Finset.filter_subset _ _
  have hBad : Bad.card ≤ 1898945373 := by
    have hlt : Bad.card < 1898945374 := by
      apply badZSpecializations_card_lt_of_forall_coeff Q hQ S 1898945374
      intro j a hja
      have := (hcaps j a hja).2.2
      omega
    omega
  have hGoodLarge :
      63521 * (1133 * 2 * 1898945373 + 1) < Good.card := by
    have hGoodCard : Good.card = S.card - Bad.card := by
      dsimp [Good]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBadSub]
    rw [hGoodCard]
    apply Nat.lt_sub_of_add_lt
    have hledger :
        63521 * (1133 * 2 * 1898945373 + 1) + Bad.card <
          bchksNumerator6400 := by
      exact (Nat.add_le_add_left hBad _).trans_lt
        bchks_fixed_factor_seed_budget6400
    exact hledger.trans hS
  have hCapacitySum :
      (∑ R ∈ Candidates,
        (1133 * 2 * 1898945373 * R.natDegree + 1)) ≤
          63521 * (1133 * 2 * 1898945373 + 1) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      1133 * 2 * 1898945373 * (∑ R ∈ Candidates, R.natDegree) +
            Candidates.card * 1 ≤
          1133 * 2 * 1898945373 * 63521 + 63521 * 1 := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left (1133 * 2 * 1898945373) hDegreeSum)
          (Nat.mul_le_mul_right 1 hCandidates)
      _ = 63521 * (1133 * 2 * 1898945373 + 1) := by ring
  let PAt : IRSProfile.Field → Polynomial IRSProfile.Field :=
    fun z => if hz : z ∈ S then P ⟨z, hz⟩ else 0
  let Rel : IRSProfile.Field →
      Polynomial (Polynomial (Polynomial IRSProfile.Field)) → Prop :=
    fun z R => triEval R z (PAt z) = 0
  have hcover : ∀ z ∈ Good, ∃ R ∈ Candidates, Rel z R := by
    intro z hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hzNotBad : z ∉ Bad := (Finset.mem_sdiff.mp hz).2
    have hQz : triSpecializeZ Q z ≠ 0 := by
      intro hzero
      apply hzNotBad
      exact Finset.mem_filter.mpr ⟨hzS, hzero⟩
    obtain ⟨R, hRQ, hRpos, hRzero⟩ :=
      exists_positive_normalizedFactor_triEval_eq_zero Q z (P ⟨z, hzS⟩)
        hQz (hQeval ⟨z, hzS⟩)
    refine ⟨R, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hRQ, hRpos⟩, ?_⟩
    simpa [Rel, PAt, hzS] using hRzero
  obtain ⟨R, hRCandidates, hRlarge⟩ :=
    exists_rel_fiber_gt_capacity Good Candidates Rel
      (fun R => 1133 * 2 * 1898945373 * R.natDegree + 1)
      hcover (hCapacitySum.trans_lt hGoodLarge)
  let T := Good.filter fun z => Rel z R
  have hTsub : T ⊆ S := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hRdata := Finset.mem_filter.mp hRCandidates
  refine ⟨R, T, Multiset.mem_toFinset.mp hRdata.1, hRdata.2, ?_, ?_, hTsub, ?_, ?_⟩
  · have : 1133 * 2 * 1898945373 * R.natDegree + 1 < T.card := by
      simpa [T] using hRlarge
    omega
  · have hRone : 1 ≤ R.natDegree := hRdata.2
    have hweighted :
        1133 * 2 * 1898945373 ≤
          1133 * 2 * 1898945373 * R.natDegree := by
      simpa using Nat.mul_le_mul_left (1133 * 2 * 1898945373) hRone
    exact hweighted.trans_lt (by
      have : 1133 * 2 * 1898945373 * R.natDegree + 1 < T.card := by
        simpa [T] using hRlarge
      omega)
  · intro z hz
    have hzGood := (Finset.mem_filter.mp hz).1
    have hzNotBad := (Finset.mem_sdiff.mp hzGood).2
    intro hzero
    apply hzNotBad
    exact Finset.mem_filter.mpr ⟨hTsub hz, hzero⟩
  · intro z hz
    have hrel := (Finset.mem_filter.mp hz).2
    simpa [Rel, PAt, hTsub hz] using hrel

end ProximityPrize.SubmissionLower
