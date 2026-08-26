import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRankOne6401
import ProximityPrize.SubmissionLower.BCHKSSphericalL3Bound6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusRankOneSpherical6401
open Polynomial
open BCHKSTwoFrobeniusRank6401
open BCHKSTwoFrobeniusRankOne6401
open BCHKSSphericalL3Bound6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
noncomputable def scaleZeroSet
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (h : Polynomial K) : Finset ι :=
  Finset.univ.filter fun i => Polynomial.eval (alpha i) h = 0
noncomputable def augmentedScaleGoodSet
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (A : Finset ι) (h : Polynomial K) : Finset ι :=
  scaleGoodSet alpha A h ∪ scaleZeroSet alpha h
theorem scaleZeroSet_card_le_natDegree
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (h : Polynomial K) (hh : h ≠ 0) :
    (scaleZeroSet alpha h).card ≤ h.natDegree := by
  let roots : Finset K := (scaleZeroSet alpha h).map alpha
  have hsub : roots ⊆ h.roots.toFinset := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hh).2
    exact (Finset.mem_filter.mp hi).2
  calc
    (scaleZeroSet alpha h).card = roots.card := (Finset.card_map alpha).symm
    _ ≤ h.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ h.roots.card := Multiset.toFinset_card_le _
    _ ≤ h.natDegree := Polynomial.card_roots' h
theorem subset_augmentedScaleGoodSet
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (A : Finset ι) (h : Polynomial K) :
    A ⊆ augmentedScaleGoodSet alpha A h := by
  intro i hi
  by_cases hz : Polynomial.eval (alpha i) h = 0
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hz⟩)
theorem scaleGoodSet_disjoint_scaleZeroSet
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (A : Finset ι) (h : Polynomial K) :
    Disjoint (scaleGoodSet alpha A h) (scaleZeroSet alpha h) := by
  rw [Finset.disjoint_left]
  intro i hi hz
  exact (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hz).2
theorem augmented_inter_subset
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (A B : Finset ι) (h : Polynomial K) :
    augmentedScaleGoodSet alpha A h ∩ augmentedScaleGoodSet alpha B h ⊆
      (scaleGoodSet alpha A h ∩ scaleGoodSet alpha B h) ∪
        scaleZeroSet alpha h := by
  intro i hi
  rcases Finset.mem_inter.mp hi with ⟨hiA, hiB⟩
  rcases Finset.mem_union.mp hiA with hiA | hiZ
  · rcases Finset.mem_union.mp hiB with hiB | hiZ
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hiA, hiB⟩)
    · exact Finset.mem_union_right _ hiZ
  · exact Finset.mem_union_right _ hiZ
theorem scaleGoodSet_inter_card_le
    {F K ι : Type*} [Field F] [Field K] [Fintype ι]
    [DecidableEq K] [DecidableEq ι]
    (embed : F →+* K) (beta : ι ↪ F) (alpha : ι ↪ K)
    (A B : Finset ι) (received : ι → K)
    (P₀ h : Polynomial K) (R S : Polynomial F) (degreeCap : ℕ)
    (hRne : R ≠ S)
    (hRdeg : R.natDegree ≤ degreeCap)
    (hSdeg : S.natDegree ≤ degreeCap)
    (hRA : ∀ i ∈ scaleGoodSet alpha A h,
      embed (Polynomial.eval (beta i) R) =
        (received i - Polynomial.eval (alpha i) P₀) /
          Polynomial.eval (alpha i) h)
    (hSB : ∀ i ∈ scaleGoodSet alpha B h,
      embed (Polynomial.eval (beta i) S) =
        (received i - Polynomial.eval (alpha i) P₀) /
          Polynomial.eval (alpha i) h) :
    (scaleGoodSet alpha A h ∩ scaleGoodSet alpha B h).card ≤ degreeCap := by
  classical
  by_contra hnot
  have hlt : degreeCap <
      (scaleGoodSet alpha A h ∩ scaleGoodSet alpha B h).card := by
    omega
  let roots : Finset F :=
    (scaleGoodSet alpha A h ∩ scaleGoodSet alpha B h).map beta
  have hzero : R - S = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (R - S) roots
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      have hiA := (Finset.mem_inter.mp hi).1
      have hiB := (Finset.mem_inter.mp hi).2
      have hembed : embed (Polynomial.eval (beta i) R) =
          embed (Polynomial.eval (beta i) S) :=
        (hRA i hiA).trans (hSB i hiB).symm
      have heq : Polynomial.eval (beta i) R =
          Polynomial.eval (beta i) S := embed.injective hembed
      simp [Polynomial.eval_sub, heq]
    · rw [Finset.card_map]
      exact (Polynomial.natDegree_sub_le R S).trans_lt
        (lt_of_le_of_lt (max_le hRdeg hSdeg) hlt)
  apply hRne
  exact sub_eq_zero.mp hzero
theorem augmentedScaleGoodSet_inter_card_le
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (A B : Finset ι) (h : Polynomial K)
    (degreeCap : ℕ) (hh : h ≠ 0)
    (hgood : (scaleGoodSet alpha A h ∩ scaleGoodSet alpha B h).card ≤
      degreeCap) :
    (augmentedScaleGoodSet alpha A h ∩
        augmentedScaleGoodSet alpha B h).card ≤
      degreeCap + h.natDegree := by
  calc
    _ ≤ ((scaleGoodSet alpha A h ∩ scaleGoodSet alpha B h) ∪
        scaleZeroSet alpha h).card :=
      Finset.card_le_card (augmented_inter_subset alpha A B h)
    _ ≤ (scaleGoodSet alpha A h ∩ scaleGoodSet alpha B h).card +
        (scaleZeroSet alpha h).card := Finset.card_union_le _ _
    _ ≤ degreeCap + h.natDegree :=
      Nat.add_le_add hgood (scaleZeroSet_card_le_natDegree alpha h hh)
theorem commonGenerator_family_card_le_17045844
    {K J : Type*} [Field K] [DecidableEq K] [Fintype J]
    (sigma : K →+* K)
    (alpha : Fin domainSize ↪ K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (P₀ h : Polynomial K) (P : J → Polynomial K)
    (A : J → Finset (Fin domainSize))
    (received : Fin domainSize → K)
    (hh : h ≠ 0) (hhdeg : h.natDegree ≤ messageDegree)
    (hPdistinct : Function.Injective P)
    (hAcard : ∀ j, agreementSize ≤ (A j).card)
    (hdata : ∀ j, Nonempty
      (ShortenedScaledBaseRSOwnerData sigma alpha hfixed
        (A j) received P₀ h (P j) messageDegree)) :
    Fintype.card J ≤ 17045844 := by
  classical
  let D (j : J) : ShortenedScaledBaseRSOwnerData sigma alpha hfixed
      (A j) received P₀ h (P j) messageDegree := Classical.choice (hdata j)
  let U (j : J) : Finset (Fin domainSize) :=
    augmentedScaleGoodSet alpha (A j) h
  have hUcard (j : J) : agreementSize ≤ (U j).card := by
    exact (hAcard j).trans
      (Finset.card_le_card (subset_augmentedScaleGoodSet alpha (A j) h))
  choose E hEU hEcard using fun j => Finset.exists_subset_card_eq (hUcard j)
  apply exactAgreementFamily_card_le_17045844_of_card
    (owners := J) (coords := Fin domainSize)
    (by norm_num [domainSize]) E
  · intro j
    simpa [agreementSize] using hEcard j
  · intro j l hjl
    have hRne : (D j).Rbase ≠ (D l).Rbase := by
      intro hEq
      apply hjl
      apply hPdistinct
      rw [(D j).factorization, (D l).factorization, hEq]
    have hgood :
        (scaleGoodSet alpha (A j) h ∩
          scaleGoodSet alpha (A l) h).card ≤
            messageDegree - h.natDegree :=
      scaleGoodSet_inter_card_le
        (fixedCoefficientField sigma).subtype
        (fixedLocatorEmbedding sigma alpha hfixed) alpha
        (A j) (A l) received P₀ h (D j).Rbase (D l).Rbase
        (messageDegree - h.natDegree) hRne
        (D j).degree_bound (D l).degree_bound
        (D j).normalized_agreement (D l).normalized_agreement
    have haug : (U j ∩ U l).card ≤ messageDegree := by
      have := augmentedScaleGoodSet_inter_card_le alpha (A j) (A l) h
        (messageDegree - h.natDegree) hh hgood
      simpa [U, Nat.sub_add_cancel hhdeg] using this
    exact (Finset.card_le_card (by
      intro i hi
      exact Finset.mem_inter.mpr
        ⟨hEU j (Finset.mem_inter.mp hi).1,
          hEU l (Finset.mem_inter.mp hi).2⟩)).trans
      (by simpa [messageDegree] using haug)
theorem rankOne_family_card_le_17045844
    {K J : Type*} [Field K] [DecidableEq K] [Fintype J]
    (sigma : K →+* K)
    (alpha : Fin domainSize ↪ K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (q : BoundedTriple K)
    (hgen : BoundedFixedGenerator sigma (q.2.1 : Polynomial K)
      (q.2.2 : Polynomial K) messageDegree)
    (P₀ : Polynomial K)
    (hP₀deg : P₀.natDegree ≤ messageDegree)
    (hP₀rel : relationPolynomial sigma q P₀ = 0)
    (P : J → Polynomial K)
    (A : J → Finset (Fin domainSize))
    (received : Fin domainSize → K)
    (hPdeg : ∀ j, (P j).natDegree ≤ messageDegree)
    (hPrel : ∀ j, relationPolynomial sigma q (P j) = 0)
    (howner : ∀ j, ∀ i ∈ A j,
      Polynomial.eval (alpha i) (P j) = received i)
    (hAcard : ∀ j, agreementSize ≤ (A j).card)
    (hPdistinct : Function.Injective P) :
    Fintype.card J ≤ 17045844 := by
  obtain ⟨h, hh, hhdeg, _hhrel, _hsplit, hdata⟩ :=
    rankOne_family_reduces_to_baseRS_or_smallGenerator6401
      sigma alpha hfixed q hgen P₀ hP₀deg hP₀rel P A
        (fun _ => received) hPdeg hPrel
        (by
          intro j i hi
          exact howner j i hi)
        hAcard
  exact commonGenerator_family_card_le_17045844
    sigma alpha hfixed P₀ h P A received hh hhdeg hPdistinct hAcard hdata
theorem rankOne_family_card_le_17045844_of_nontrivial
    {K J : Type*} [Field K] [DecidableEq K] [Fintype J]
    (sigma : K →+* K)
    (alpha : Fin domainSize ↪ K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (q : BoundedTriple K)
    (hnontrivial : (q.2.1 : Polynomial K) ≠ 0 ∨
      (q.2.2 : Polynomial K) ≠ 0)
    (P₀ : Polynomial K)
    (hP₀deg : P₀.natDegree ≤ messageDegree)
    (hP₀rel : relationPolynomial sigma q P₀ = 0)
    (P : J → Polynomial K)
    (A : J → Finset (Fin domainSize))
    (received : Fin domainSize → K)
    (hPdeg : ∀ j, (P j).natDegree ≤ messageDegree)
    (hPrel : ∀ j, relationPolynomial sigma q (P j) = 0)
    (howner : ∀ j, ∀ i ∈ A j,
      Polynomial.eval (alpha i) (P j) = received i)
    (hAcard : ∀ j, agreementSize ≤ (A j).card)
    (hPdistinct : Function.Injective P) :
    Fintype.card J ≤ 17045844 := by
  by_cases hsmall : Fintype.card J ≤ 1
  · omega
  · have htwo : 1 < Fintype.card J := by omega
    obtain ⟨j, l, hjl⟩ := Fintype.one_lt_card_iff.mp htwo
    have hPlj : P l ≠ P j := by
      intro heq
      exact hjl (hPdistinct heq.symm)
    have hgen :=
      BCHKSTwoFrobeniusRankOne6401.boundedFixedGenerator_of_distinct_affine_solutions
      sigma q messageDegree hnontrivial (P j) (P l)
        (hPdeg j) (hPdeg l) (hPrel j) (hPrel l) hPlj
    exact rankOne_family_card_le_17045844 sigma alpha hfixed q hgen
      P₀ hP₀deg hP₀rel P A received hPdeg hPrel howner hAcard
      hPdistinct
end BCHKSTwoFrobeniusRankOneSpherical6401
end ProximityPrize.SubmissionLower
