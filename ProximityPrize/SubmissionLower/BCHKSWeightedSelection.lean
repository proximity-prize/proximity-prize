import ProximityPrize.SubmissionLower.BCHKSFactorPigeon
import ProximityPrize.SubmissionLower.BCHKSParameters
import ProximityPrize.SubmissionLower.BCHKSInterpolation

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

/-- Optimized positive-factor selection on the good specialization set. -/
theorem exists_bchks_weighted_factor_selection
    (S Bad : Finset IRSProfile.Field)
    (P : ↥S → Polynomial IRSProfile.Field)
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (hcaps : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      j < 852 ∧ a + 131071 * j < 111624646 ∧
        ((Q.coeff j).coeff a).natDegree + j < 519143)
    (hQeval : ∀ z : ↥S, triEval Q z.1 (P z) = 0)
    (hS : bchksNumerator < S.card)
    (hBad : (S ∩ Bad).card ≤ bchksBadBudget)
    (x₀ : IRSProfile.Field)
    (hQz : ∀ z ∈ S \ Bad, triSpecializeZ Q z ≠ 0)
    (hsecond : ∀ z ∈ S \ Bad,
      ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
        biSpecializeZ (triSpecializeX R x₀) z ≠ 0) :
    ∃ R : Polynomial (Polynomial (Polynomial IRSProfile.Field)),
      ∃ H : Polynomial (Polynomial IRSProfile.Field), ∃ T : Finset IRSProfile.Field,
        R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
        H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) ∧
          0 < H.natDegree ∧
        632176 * 519143 * (R.natDegree * H.natDegree) +
            (bchksErrors + 1) < T.card ∧
        ∃ hTsub : T ⊆ S \ Bad,
          ∀ z, ∀ hz : z ∈ T,
            triEval R z (P ⟨z, (Finset.mem_sdiff.mp (hTsub hz)).1⟩) = 0 ∧
            biEval H
              (Polynomial.eval x₀ (P ⟨z, (Finset.mem_sdiff.mp (hTsub hz)).1⟩)) z = 0 := by
  classical
  let Good := S \ Bad
  have hGoodLarge :
      632176 * 519143 * 852 ^ 2 + (bchksErrors + 1) * 852 < Good.card := by
    simpa [Good] using card_sdiff_large_for_bchks S Bad hS hBad
  have hGoodNonempty : Good.Nonempty := by
    apply Finset.card_pos.mp
    exact (by norm_num : 0 <
      632176 * 519143 * 852 ^ 2 + (bchksErrors + 1) * 852).trans hGoodLarge
  obtain ⟨z₀, hz₀⟩ := hGoodNonempty
  have hQdeg : Q.natDegree ≤ 852 := by
    have hlead : Q.coeff Q.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hQ
    have ha : ∃ a, (Q.coeff Q.natDegree).coeff a ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hlead
      apply Polynomial.ext
      intro a
      exact hn a
    obtain ⟨a, ha⟩ := ha
    exact Nat.le_of_lt (hcaps Q.natDegree a ha).1
  have hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0 := by
    intro R hR hzero
    exact hsecond z₀ hz₀ R hR (by simp [hzero, biSpecializeZ])
  let Candidates := (positiveNormalizedFactorPairs Q x₀).filter
    fun RH => 0 < RH.1.natDegree
  have hCandidates : Candidates.card ≤ 852 := by
    exact (Finset.card_filter_le _ _).trans
      (positiveNormalizedFactorPairs_card_le' Q hQ x₀ 852 hQdeg hx₀)
  have hRXdeg : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      (triSpecializeX R x₀).natDegree ≤ 852 := by
    intro R hR
    exact (triSpecializeX_natDegree_le R x₀).trans
      ((Polynomial.natDegree_le_of_dvd
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hR) hQ).trans hQdeg)
  have hweighted :
      (∑ RH ∈ Candidates, RH.1.natDegree * RH.2.natDegree) ≤ 852 ^ 2 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)).trans
    exact positiveNormalizedFactorPairs_sum_mul_natDegree_le_sq
      Q hQ x₀ 852 hQdeg hx₀ hRXdeg
  let Rel : ↥Good →
      (Polynomial (Polynomial (Polynomial IRSProfile.Field)) ×
        Polynomial (Polynomial IRSProfile.Field)) → Prop :=
    fun z RH =>
      triEval RH.1 z.1 (P ⟨z.1, (Finset.mem_sdiff.mp z.2).1⟩) = 0 ∧
      biEval RH.2 (Polynomial.eval x₀ (P ⟨z.1, (Finset.mem_sdiff.mp z.2).1⟩)) z.1 = 0
  have hcover : ∀ z ∈ Good.attach, ∃ RH ∈ Candidates, Rel z RH := by
    intro z hz
    let zs : ↥S := ⟨z.1, (Finset.mem_sdiff.mp z.2).1⟩
    obtain ⟨R, hRQ, hRpos, hRzero⟩ :=
      exists_positive_normalizedFactor_triEval_eq_zero Q z.1 (P zs)
        (hQz z.1 z.2) (hQeval zs)
    have hpoint :
        biEval (triSpecializeX R x₀) (Polynomial.eval x₀ (P zs)) z.1 = 0 := by
      rw [← eval_triEval_eq_biEval_triSpecializeX]
      rw [hRzero]
      simp
    obtain ⟨H, hHR, hHpos, hHzero⟩ :=
      exists_positive_normalizedFactor_biEval_eq_zero
        (triSpecializeX R x₀) z.1 (Polynomial.eval x₀ (P zs))
        (hsecond z.1 z.2 R hRQ) hpoint
    have hpair : (R, H) ∈ positiveNormalizedFactorPairs Q x₀ := by
      simp only [positiveNormalizedFactorPairs, Finset.mem_biUnion,
        Multiset.mem_toFinset, Finset.mem_image, Finset.mem_filter]
      exact ⟨R, hRQ, H, ⟨hHR, hHpos⟩, rfl⟩
    exact ⟨(R, H), Finset.mem_filter.mpr ⟨hpair, hRpos⟩, hRzero, hHzero⟩
  have hCapacityLarge :
      632176 * 519143 * 852 ^ 2 +
          (bchksErrors + 1) * Candidates.card < Good.attach.card := by
    rw [Finset.card_attach]
    exact (Nat.add_le_add_left
      (Nat.mul_le_mul_left (bchksErrors + 1) hCandidates)
      (632176 * 519143 * 852 ^ 2)).trans_lt hGoodLarge
  obtain ⟨RH, hRHcand, hRHlarge⟩ :=
    exists_pair_fiber_gt_BCHKS_capacity Good.attach Candidates Rel
      Polynomial.natDegree Polynomial.natDegree
      316088 519143 852 bchksErrors hcover hweighted hCapacityLarge
  have hRposRH : 0 < RH.1.natDegree := (Finset.mem_filter.mp hRHcand).2
  have hmem := (Finset.mem_filter.mp hRHcand).1
  simp only [positiveNormalizedFactorPairs, Finset.mem_biUnion,
    Multiset.mem_toFinset, Finset.mem_image, Finset.mem_filter] at hmem
  obtain ⟨R, hRQ, H, ⟨hHR, hHpos⟩, heq⟩ := hmem
  have hReq : R = RH.1 := congrArg Prod.fst heq
  have hHeq : H = RH.2 := congrArg Prod.snd heq
  have hRpos : 0 < R.natDegree := by simpa [hReq] using hRposRH
  let U := Good.attach.filter fun z => Rel z RH
  let emb : ↥Good ↪ IRSProfile.Field := Function.Embedding.subtype fun z => z ∈ Good
  let T : Finset IRSProfile.Field := U.map emb
  have hTsub : T ⊆ S \ Bad := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hz
    exact u.2
  refine ⟨R, H, T, hRQ, hRpos, hHR, hHpos, ?_, hTsub, ?_⟩
  · simpa [T, U, hReq, hHeq] using hRHlarge
  · intro z hz
    obtain ⟨u, hu, huz⟩ := Finset.mem_map.mp hz
    have huv : u.1 = z := by simpa [emb] using huz
    subst z
    have hrel := (Finset.mem_filter.mp hu).2
    simpa [Rel, emb, hReq, hHeq] using hrel

end ProximityPrize.SubmissionLower
