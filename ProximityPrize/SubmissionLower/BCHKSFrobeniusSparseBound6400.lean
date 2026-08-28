import ProximityPrize.SubmissionLower.BCHKSFrobeniusOwnerCounting6400

/-!
# Uniform sparse MCA bound at score 64

The small-support branch is an ordinary Reed--Solomon root count.  In the
large-support branch, too many bad slopes first construct one Frobenius
amplitude atom; the coordinate-owner theorem then bounds every bad slope for
that fixed atom.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Below the scroll threshold, every noncancelling MCA witness would be a
nonzero degree-`<131072` polynomial with at least `131072` distinct roots. -/
theorem not_score6400_mcaBad_of_small_support_of_not_cancellation
    (e₀ e₁ : Score6400Index → Score6400Field)
    (w : Score6400Field)
    (hsmall : (pairSupport e₀ e₁).card ≤ 54292)
    (hnoncancel : w ∉ cancellationSlopes e₀ e₁ (pairSupport e₀ e₁)) :
    ¬MCABad IRSProfile.baseCode e₀ e₁ 185364 w := by
  classical
  intro hbad
  have hbadRS : MCABad
      (ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension)
      e₀ e₁ 185364 w := by
    simpa only [IRSProfile.baseCode] using hbad
  obtain ⟨A, P, hA, hPdegree, hPagree, i, hiA, hiSupport⟩ :=
    exists_rs_polynomial_data_of_mcaBad
      IRSProfile.domain IRSProfile.baseDimension 185364 e₀ e₁ w hbadRS
  have hlineNe : e₀ i + w * e₁ i ≠ 0 :=
    affine_error_ne_zero_on_support_of_not_cancellation
      e₀ e₁ (pairSupport e₀ e₁) (fun _ hi ↦ hi)
      w hnoncancel i hiSupport
  have hPne : P ≠ 0 := by
    intro hzero
    have hi := hPagree i hiA
    rw [hzero, Polynomial.eval_zero] at hi
    exact hlineNe hi.symm
  have hPnat : P.natDegree < 131072 := by
    have hlt : P.natDegree < IRSProfile.baseDimension :=
      (Polynomial.natDegree_lt_iff_degree_lt hPne).2 hPdegree
    norm_num [IRSProfile.baseDimension] at hlt ⊢
    exact hlt
  let Outside := A \ pairSupport e₀ e₁
  have hOutsideCard : 131072 ≤ Outside.card := by
    have hinter : (A ∩ pairSupport e₀ e₁).card ≤
        (pairSupport e₀ e₁).card :=
      Finset.card_le_card Finset.inter_subset_right
    have hsplit := Finset.card_sdiff_add_card_inter A (pairSupport e₀ e₁)
    dsimp only [Outside]
    omega
  let Roots := Outside.map IRSProfile.domain
  have hRootsCard : Roots.card = Outside.card := by
    simp only [Roots, Finset.card_map]
  have hroot : ∀ x ∈ Roots, P.eval x = 0 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
    have hjA : j ∈ A := (Finset.mem_sdiff.mp hj).1
    have hjSupport : j ∉ pairSupport e₀ e₁ :=
      (Finset.mem_sdiff.mp hj).2
    obtain ⟨hj₀, hj₁⟩ := pairSupport_values_eq_zero_of_not_mem
      e₀ e₁ hjSupport
    rw [hPagree j hjA, hj₀, hj₁, mul_zero, add_zero]
  have hdegreeRoots : P.natDegree < Roots.card := by
    rw [hRootsCard]
    omega
  exact hPne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    P Roots hroot hdegreeRoots)

theorem card_score6400_small_support_mcaBad_slopes_le
    (e₀ e₁ : Score6400Index → Score6400Field)
    (Gamma : Finset Score6400Field)
    (hsmall : (pairSupport e₀ e₁).card ≤ 54292) :
    (restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364).card ≤
      54292 := by
  classical
  let Bad := restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364
  let Cancel := cancellationSlopes e₀ e₁ (pairSupport e₀ e₁)
  have hsubset : Bad ⊆ Cancel := by
    intro w hw
    by_contra hnoncancel
    have hbad : MCABad IRSProfile.baseCode e₀ e₁ 185364 w := by
      have hw' := (Finset.mem_filter.mp hw).2
      simpa only [Bad, restrictedMCABadSlopes] using hw'
    exact (not_score6400_mcaBad_of_small_support_of_not_cancellation
      e₀ e₁ w hsmall hnoncancel) hbad
  have hcancel : Cancel.card ≤ (pairSupport e₀ e₁).card := by
    simpa only [Cancel] using card_cancellationSlopes_le
      e₀ e₁ (pairSupport e₀ e₁)
  have hbadCard : Bad.card ≤ Cancel.card := Finset.card_le_card hsubset
  simpa only [Bad] using (show Bad.card ≤ 54292 by omega)

/-- In the large-support branch, a hypothetical excess of bad slopes leaves
enough noncancelling slopes to build one amplitude atom.  That atom's uniform
coordinate-owner bound contradicts the excess. -/
theorem card_score6400_large_support_sparse_mcaBad_slopes_le
    (e₀ e₁ : Score6400Index → Score6400Field)
    (Gamma : Finset Score6400Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hlarge : 54292 < (pairSupport e₀ e₁).card) :
    (restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364).card ≤
      48000000000000 := by
  classical
  let Bad := restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364
  let Cancel := cancellationSlopes e₀ e₁ (pairSupport e₀ e₁)
  let Seed := Bad \ Cancel
  by_contra hnot
  have hBadLarge : 48000000000000 < Bad.card := by
    simpa only [Bad] using Nat.lt_of_not_ge hnot
  have hsupport : (pairSupport e₀ e₁).card ≤ 76780 := by
    have hs := hsparse
    change (pairSupport e₀ e₁).card ≤
      Fintype.card Score6400Index - 185364 at hs
    norm_num [Score6400Index, IRSProfile.Index] at hs
    exact hs
  have hcancelCard : Cancel.card ≤ 76780 := by
    have hc := card_cancellationSlopes_le
      e₀ e₁ (pairSupport e₀ e₁)
    change Cancel.card ≤ (pairSupport e₀ e₁).card at hc
    exact hc.trans hsupport
  have hinterCard : (Bad ∩ Cancel).card ≤ Cancel.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hpartition : Seed.card + (Bad ∩ Cancel).card = Bad.card := by
    simpa only [Seed] using Finset.card_sdiff_add_card_inter Bad Cancel
  have hh : (pairSupport e₀ e₁).card - 54292 ≤ 22488 := by omega
  have hSeedLarge :
      ((pairSupport e₀ e₁).card - 54292) +
          2130706433 * ((pairSupport e₀ e₁).card - 54292) <
        Seed.card := by
    omega
  have hSeedBad : ∀ z ∈ Seed,
      MCABad IRSProfile.baseCode e₀ e₁ 185364 z := by
    intro z hz
    have hzBad : z ∈ Bad := (Finset.mem_sdiff.mp hz).1
    change z ∈ restrictedMCABadSlopes Gamma IRSProfile.baseCode
      e₀ e₁ 185364 at hzBad
    exact (Finset.mem_filter.mp hzBad).2
  have hSeedNoncancel : ∀ z ∈ Seed,
      z ∉ cancellationSlopes e₀ e₁ (pairSupport e₀ e₁) := by
    intro z hz
    have hzCancel : z ∉ Cancel := (Finset.mem_sdiff.mp hz).2
    simpa only [Cancel] using hzCancel
  obtain ⟨z₀, atom⟩ :=
    score6400_frobeniusAmplitudeAtom_of_many_sparse_mcaBad
      e₀ e₁ Seed hsparse hSeedBad hSeedNoncancel hlarge hSeedLarge
  let normalized := atom.semilinearPair
  have hbound := card_score6400_sparse_mcaBad_slopes_le
    e₀ e₁ atom normalized Gamma hsparse hlarge
  exact (Nat.not_lt_of_ge hbound) (by simpa only [Bad] using hBadLarge)

/-- Final fixed-pair sparse MCA bound, covering both support regimes. -/
theorem card_score6400_sparse_mcaBad_slopes_uniform
    (e₀ e₁ : Score6400Index → Score6400Field)
    (Gamma : Finset Score6400Field)
    (hsparse : SparseAt e₀ e₁ 185364) :
    (restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364).card ≤
      48000000000000 := by
  by_cases hsmall : (pairSupport e₀ e₁).card ≤ 54292
  · exact (card_score6400_small_support_mcaBad_slopes_le
      e₀ e₁ Gamma hsmall).trans (by norm_num)
  · exact card_score6400_large_support_sparse_mcaBad_slopes_le
      e₀ e₁ Gamma hsparse (Nat.lt_of_not_ge hsmall)

end ProximityPrize.SubmissionLower
