import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusSymbolicKernel6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusRankTwoIdentityFork6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusRankTwoSpecialization6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
noncomputable def activeIdentityCoordinates
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F) (I : Finset ι) :
    Finset ι := by
  classical
  exact (identityCoordinates q r alpha u₀ u₁ I).filter fun i =>
    evalOuterAt (alpha i) (symbolicRankTwoDenominator q r) ≠ 0
noncomputable def commonLocatorCoordinates
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F) (I : Finset ι) :
    Finset ι := by
  classical
  exact (identityCoordinates q r alpha u₀ u₁ I).filter fun i =>
    evalOuterAt (alpha i) (symbolicRankTwoDenominator q r) = 0
theorem identityCoordinates_eq_active_union_common
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F) (I : Finset ι) :
    identityCoordinates q r alpha u₀ u₁ I =
      activeIdentityCoordinates q r alpha u₀ u₁ I ∪
        commonLocatorCoordinates q r alpha u₀ u₁ I := by
  classical
  ext i
  simp only [activeIdentityCoordinates, commonLocatorCoordinates,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hi
    by_cases hD :
        evalOuterAt (alpha i) (symbolicRankTwoDenominator q r) = 0
    · exact Or.inr ⟨hi, hD⟩
    · exact Or.inl ⟨hi, hD⟩
  · rintro (hi | hi) <;> exact hi.1
theorem active_disjoint_common
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F) (I : Finset ι) :
    Disjoint (activeIdentityCoordinates q r alpha u₀ u₁ I)
      (commonLocatorCoordinates q r alpha u₀ u₁ I) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiA hiC
  exact (Finset.mem_filter.mp hiA).2 (Finset.mem_filter.mp hiC).2
theorem identityCoordinates_card_eq_active_add_common
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F) (I : Finset ι) :
    (identityCoordinates q r alpha u₀ u₁ I).card =
      (activeIdentityCoordinates q r alpha u₀ u₁ I).card +
        (commonLocatorCoordinates q r alpha u₀ u₁ I).card := by
  rw [identityCoordinates_eq_active_union_common]
  exact Finset.card_union_of_disjoint
    (active_disjoint_common q r alpha u₀ u₁ I)
noncomputable def outerLocatorProduct
    {F ι : Type*} [Field F]
    (alpha : ι → F) (J : Finset ι) : XOverZ F :=
  ∏ i ∈ J,
    (Polynomial.X - Polynomial.C (Polynomial.C (alpha i)))
theorem outerLocatorProduct_natDegree
    {F ι : Type*} [Field F]
    (alpha : ι → F) (J : Finset ι) :
    (outerLocatorProduct alpha J).natDegree = J.card := by
  classical
  simpa [outerLocatorProduct] using
    (Polynomial.natDegree_finsetProd_X_sub_C_eq_card J
      (fun i => Polynomial.C (alpha i)))
theorem outerLocatorProduct_monic
    {F ι : Type*} [Field F]
    (alpha : ι → F) (J : Finset ι) :
    (outerLocatorProduct alpha J).Monic := by
  classical
  simpa [outerLocatorProduct] using
    (Polynomial.monic_prod_X_sub_C
      (fun i => Polynomial.C (alpha i)) J)
theorem outerLocatorProduct_dvd_of_eval_zero
    {F ι : Type*} [Field F] [DecidableEq ι]
    (alpha : ι ↪ F) (J : Finset ι) (P : XOverZ F)
    (hzero : ∀ i ∈ J, evalOuterAt (alpha i) P = 0) :
    outerLocatorProduct alpha J ∣ P := by
  classical
  unfold outerLocatorProduct
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    have hne : alpha i ≠ alpha j := fun h => hij (alpha.injective h)
    have hunit : IsUnit
        ((Polynomial.C (alpha i) : Polynomial F) -
          Polynomial.C (alpha j)) := by
      rw [← Polynomial.C_sub]
      exact Polynomial.isUnit_C.mpr (sub_ne_zero.mpr hne).isUnit
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hzero i hi
theorem commonCoordinate_numerator_eval_eq_zero
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F) (I : Finset ι)
    (i : ι)
    (hi : i ∈ commonLocatorCoordinates q r alpha u₀ u₁ I) :
    evalOuterAt (alpha i) (symbolicRankTwoNumerator q r) = 0 := by
  classical
  have hi' := Finset.mem_filter.mp hi
  have hidentity := (Finset.mem_filter.mp hi'.1).2
  have hden := hi'.2
  unfold coordinateMismatch at hidentity
  rw [hden, zero_mul, zero_add] at hidentity
  exact hidentity
theorem commonLocatorProduct_dvd_both
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (I : Finset ι) :
    outerLocatorProduct alpha
        (commonLocatorCoordinates q r alpha u₀ u₁ I) ∣
          symbolicRankTwoDenominator q r ∧
      outerLocatorProduct alpha
        (commonLocatorCoordinates q r alpha u₀ u₁ I) ∣
          symbolicRankTwoNumerator q r := by
  classical
  constructor
  · apply outerLocatorProduct_dvd_of_eval_zero alpha
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · apply outerLocatorProduct_dvd_of_eval_zero alpha
    intro i hi
    exact commonCoordinate_numerator_eval_eq_zero q r alpha u₀ u₁ I i hi
theorem exists_cancelled_commonLocator_reduction
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (I : Finset ι)
    (hden : symbolicRankTwoDenominator q r ≠ 0) :
    ∃ Dred Nred : XOverZ F,
      symbolicRankTwoDenominator q r =
        outerLocatorProduct alpha
          (commonLocatorCoordinates q r alpha u₀ u₁ I) * Dred ∧
      symbolicRankTwoNumerator q r =
        outerLocatorProduct alpha
          (commonLocatorCoordinates q r alpha u₀ u₁ I) * Nred ∧
      Dred ≠ 0 ∧
      (symbolicRankTwoDenominator q r).natDegree =
        (commonLocatorCoordinates q r alpha u₀ u₁ I).card +
          Dred.natDegree := by
  classical
  obtain ⟨Dred, hDred⟩ :=
    (commonLocatorProduct_dvd_both q r alpha u₀ u₁ I).1
  obtain ⟨Nred, hNred⟩ :=
    (commonLocatorProduct_dvd_both q r alpha u₀ u₁ I).2
  have hDredne : Dred ≠ 0 := by
    intro hzero
    apply hden
    rw [hDred, hzero, mul_zero]
  refine ⟨Dred, Nred, hDred, hNred, hDredne, ?_⟩
  rw [hDred, Polynomial.natDegree_mul
      (outerLocatorProduct_monic alpha _).ne_zero hDredne,
    outerLocatorProduct_natDegree]
theorem active_frame_or_commonLocator_gcd
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (I : Finset ι) (k : ℕ)
    (hden : symbolicRankTwoDenominator q r ≠ 0) :
    k < (activeIdentityCoordinates q r alpha u₀ u₁ I).card ∨
      ((identityCoordinates q r alpha u₀ u₁ I).card - k ≤
          (commonLocatorCoordinates q r alpha u₀ u₁ I).card ∧
        (commonLocatorCoordinates q r alpha u₀ u₁ I).card ≤
          (symbolicRankTwoDenominator q r).natDegree ∧
        outerLocatorProduct alpha
            (commonLocatorCoordinates q r alpha u₀ u₁ I) ∣
              symbolicRankTwoDenominator q r ∧
        outerLocatorProduct alpha
            (commonLocatorCoordinates q r alpha u₀ u₁ I) ∣
              symbolicRankTwoNumerator q r) := by
  classical
  by_cases hactive : k <
      (activeIdentityCoordinates q r alpha u₀ u₁ I).card
  · exact Or.inl hactive
  · right
    have hsplit := identityCoordinates_card_eq_active_add_common
      q r alpha u₀ u₁ I
    have hdvd := commonLocatorProduct_dvd_both q r alpha u₀ u₁ I
    have hdegree := Polynomial.natDegree_le_of_dvd hdvd.1 hden
    rw [outerLocatorProduct_natDegree] at hdegree
    refine ⟨by omega, hdegree, hdvd.1, hdvd.2⟩
noncomputable def activeDenominatorBadChallenges
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) : Finset F := by
  classical
  exact (activeIdentityCoordinates q r alpha u₀ u₁ I).biUnion fun i =>
    S.filter fun z =>
      Polynomial.eval z
        (evalOuterAt (alpha i) (symbolicRankTwoDenominator q r)) = 0
theorem activeDenominatorBadChallenges_card_le
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) :
    (activeDenominatorBadChallenges q r alpha u₀ u₁ I S).card ≤
      ∑ i ∈ activeIdentityCoordinates q r alpha u₀ u₁ I,
        (evalOuterAt (alpha i)
          (symbolicRankTwoDenominator q r)).natDegree := by
  classical
  calc
    _ ≤ ∑ i ∈ activeIdentityCoordinates q r alpha u₀ u₁ I,
        (S.filter fun z => Polynomial.eval z
          (evalOuterAt (alpha i)
            (symbolicRankTwoDenominator q r)) = 0).card :=
      Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      exact card_filter_eval_eq_zero_le_natDegree S _
        (Finset.mem_filter.mp hi).2
noncomputable def activeDenominatorGoodChallenges
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) : Finset F := by
  classical
  exact S \ activeDenominatorBadChallenges q r alpha u₀ u₁ I S
theorem denominator_eval_ne_zero_of_good
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) (z : F)
    (hz : z ∈ activeDenominatorGoodChallenges q r alpha u₀ u₁ I S)
    (i : ι) (hi : i ∈ activeIdentityCoordinates q r alpha u₀ u₁ I) :
    Polynomial.eval z
      (evalOuterAt (alpha i) (symbolicRankTwoDenominator q r)) ≠ 0 := by
  classical
  have hz' : z ∈ S \
      activeDenominatorBadChallenges q r alpha u₀ u₁ I S := by
    simpa [activeDenominatorGoodChallenges] using hz
  intro hzero
  have hzbad : z ∈ activeDenominatorBadChallenges q r alpha u₀ u₁ I S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨(Finset.mem_sdiff.mp hz').1, hzero⟩
  exact (Finset.mem_sdiff.mp hz').2 hzbad
theorem owner_eval_eq_affine_of_active_identity
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) (z : F) (P : Polynomial F)
    (hz : z ∈ activeDenominatorGoodChallenges q r alpha u₀ u₁ I S)
    (hbranch : specializeCoeffZ z (symbolicRankTwoDenominator q r) * P =
      -specializeCoeffZ z (symbolicRankTwoNumerator q r))
    (i : ι) (hi : i ∈ activeIdentityCoordinates q r alpha u₀ u₁ I) :
    Polynomial.eval (alpha i) P = u₀ i + z * u₁ i := by
  classical
  have hden := denominator_eval_ne_zero_of_good
    q r alpha u₀ u₁ I S z hz i hi
  have howner := congrArg (Polynomial.eval (alpha i)) hbranch
  simp only [Polynomial.eval_mul, Polynomial.eval_neg] at howner
  have hden' :
      Polynomial.eval (alpha i)
        (specializeCoeffZ z (symbolicRankTwoDenominator q r)) ≠ 0 := by
    rwa [eval_specializeCoeffZ_comm]
  have hidentity := (Finset.mem_filter.mp hi).1
  have hmismatch := (Finset.mem_filter.mp hidentity).2
  have hreceived := coordinateMismatch_eval z q r (alpha i) (u₀ i) (u₁ i)
  rw [hmismatch, Polynomial.eval_zero] at hreceived
  apply mul_left_cancel₀ hden'
  linear_combination howner + hreceived
theorem exists_affine_family_on_activeDenominatorGood
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) (P : F → Polynomial F) (k : ℕ)
    (hactive : k <
      (activeIdentityCoordinates q r alpha u₀ u₁ I).card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hbranch : ∀ z ∈ S,
      specializeCoeffZ z (symbolicRankTwoDenominator q r) * P z =
        -specializeCoeffZ z (symbolicRankTwoNumerator q r)) :
    ∃ p₀ p₁ : Polynomial F,
      p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z ∈ activeDenominatorGoodChallenges q r alpha u₀ u₁ I S,
        P z = p₀ + Polynomial.C z * p₁ := by
  classical
  obtain ⟨E, hEsub, hEcard⟩ :=
    Finset.exists_subset_card_eq (show k + 1 ≤
      (activeIdentityCoordinates q r alpha u₀ u₁ I).card by omega)
  let p₀ : Polynomial F := Lagrange.interpolate E alpha u₀
  let p₁ : Polynomial F := Lagrange.interpolate E alpha u₁
  have hpDegree (u : ι → F) :
      (Lagrange.interpolate E alpha u).natDegree ≤ k := by
    let p := Lagrange.interpolate E alpha u
    by_cases hp : p = 0
    · simp [p, hp]
    · have hd : p.degree < (E.card : WithBot ℕ) :=
        Lagrange.degree_interpolate_lt u alpha.injective.injOn
      have hn : p.natDegree < E.card :=
        (Polynomial.natDegree_lt_iff_degree_lt hp).2 hd
      simpa [p, hEcard] using hn
  have hp₀ : p₀.natDegree ≤ k := hpDegree u₀
  have hp₁ : p₁.natDegree ≤ k := hpDegree u₁
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  intro z hz
  have hz' : z ∈ S \
      activeDenominatorBadChallenges q r alpha u₀ u₁ I S := by
    simpa [activeDenominatorGoodChallenges] using hz
  have hzS : z ∈ S := (Finset.mem_sdiff.mp hz').1
  let Q := p₀ + Polynomial.C z * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) Q
      (f := fun i : {i // i ∈ E} => alpha i.1)
      (alpha.injective.comp Subtype.val_injective)
  · intro i
    have hiActive : i.1 ∈ activeIdentityCoordinates q r alpha u₀ u₁ I :=
      hEsub i.2
    have howner := owner_eval_eq_affine_of_active_identity
      q r alpha u₀ u₁ I S z (P z) hz (hbranch z hzS) i.1 hiActive
    have h0 : Polynomial.eval (alpha i.1) p₀ = u₀ i.1 := by
      exact Lagrange.eval_interpolate_at_node u₀
        alpha.injective.injOn i.2
    have h1 : Polynomial.eval (alpha i.1) p₁ = u₁ i.1 := by
      exact Lagrange.eval_interpolate_at_node u₁
        alpha.injective.injOn i.2
    rw [howner]
    simp [Q, h0, h1]
  · have hQ : Q.natDegree ≤ k :=
      (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le z p₁).trans hp₁))
    rw [Fintype.card_coe, hEcard]
    exact max_lt ((hPdegree z hzS).trans_lt (Nat.lt_succ_self k))
      (hQ.trans_lt (Nat.lt_succ_self k))
theorem ownerFamily_affine_or_commonLocator_gcd
    {F ι : Type*} [Field F] [DecidableEq ι]
    (sigma : F →+* F)
    (q r : SymbolicRow F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) (P : F → Polynomial F) (k : ℕ)
    (hden : symbolicRankTwoDenominator q r ≠ 0)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hq : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z q) (P z) = 0)
    (hr : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z r) (P z) = 0) :
    (∃ p₀ p₁ : Polynomial F,
      p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z ∈ activeDenominatorGoodChallenges q r alpha u₀ u₁ I S,
        P z = p₀ + Polynomial.C z * p₁) ∨
      ((identityCoordinates q r alpha u₀ u₁ I).card - k ≤
          (commonLocatorCoordinates q r alpha u₀ u₁ I).card ∧
        (commonLocatorCoordinates q r alpha u₀ u₁ I).card ≤
          (symbolicRankTwoDenominator q r).natDegree ∧
        outerLocatorProduct alpha
            (commonLocatorCoordinates q r alpha u₀ u₁ I) ∣
              symbolicRankTwoDenominator q r ∧
        outerLocatorProduct alpha
            (commonLocatorCoordinates q r alpha u₀ u₁ I) ∣
              symbolicRankTwoNumerator q r) := by
  rcases active_frame_or_commonLocator_gcd
      q r alpha u₀ u₁ I k hden with hactive | hcommon
  · left
    apply exists_affine_family_on_activeDenominatorGood
      q r alpha u₀ u₁ I S P k hactive hPdegree
    intro z hz
    exact specialized_rankTwo_owner_identity sigma z q r (P z)
      (hq z hz) (hr z hz)
  · exact Or.inr hcommon
theorem nonidentity_coordinate_challenge_card_le
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) (i : ι)
    (hi : i ∈ I)
    (hnonidentity : i ∉ identityCoordinates q r alpha u₀ u₁ I) :
    (S.filter fun z => Polynomial.eval z
      (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)) = 0).card ≤
        (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)).natDegree := by
  classical
  apply card_filter_eval_eq_zero_le_natDegree
  intro hzero
  apply hnonidentity
  simp only [identityCoordinates, Finset.mem_filter]
  exact ⟨hi, hzero⟩
theorem sum_nonidentity_coordinate_challenge_cards_le
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) :
    (∑ i ∈ I.filter fun i =>
        i ∉ identityCoordinates q r alpha u₀ u₁ I,
      (S.filter fun z => Polynomial.eval z
        (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)) = 0).card) ≤
      ∑ i ∈ I.filter fun i =>
        i ∉ identityCoordinates q r alpha u₀ u₁ I,
        (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)).natDegree := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_filter.mp hi
  exact nonidentity_coordinate_challenge_card_le
    q r alpha u₀ u₁ I S i hi'.1 hi'.2
end BCHKSTwoFrobeniusRankTwoIdentityFork6401
end ProximityPrize.SubmissionLower
