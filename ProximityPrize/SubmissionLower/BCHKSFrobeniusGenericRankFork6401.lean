import ProximityPrize.SubmissionLower.BCHKSFrobeniusDualGRSKernel6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusGenericRankFork6401
open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSGaoSpecializationCore6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
theorem fullTwoLaneSupportKeyMatrix_ordinaryBlock
    {F : Type*} [Field F] {s rows : Nat}
    (sigma : F →+* F) (alpha : Fin s → F) (beta E : Fin s → F) :
    (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).submatrix Sum.inl id =
      supportSyndromeMatrix rows s alpha (fun i => beta i * E i) := by
  rfl
theorem supportSize_eq_rank_or_failureRelation
    {F : Type*} [Field F] {s rho : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F) (beta E : Fin s → F)
    (hs : s ≤ keyErrors6401)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hrank :
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        alpha beta E).rank = rho) :
    s = rho ∨
      (rho < s ∧
        ∃ W₀ W₁ : F[X],
          W₀ ≠ 0 ∧
          W₀.degree < (s - keyFirstLaneRows6401 : Nat) ∧
          W₁.degree < (s - keyFirstLaneRows6401 : Nat) ∧
          TwoLaneFailureRelation sigma alpha E W₀ W₁) := by
  let M := fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
    alpha beta E
  have hrho_le_s : rho ≤ s := by
    rw [← hrank]
    simpa using Matrix.rank_le_card_width M
  by_cases hsrho : s = rho
  · exact Or.inl hsrho
  right
  have hrho_lt_s : rho < s := lt_of_le_of_ne hrho_le_s (Ne.symm hsrho)
  have hm_le_s : keyFirstLaneRows6401 ≤ s := by
    by_contra hms
    have hs_lt_m : s < keyFirstLaneRows6401 := by omega
    let O := supportSyndromeMatrix keyFirstLaneRows6401 s alpha
      (fun i => beta i * E i)
    have hOrank : O.rank = s := by
      dsimp [O]
      rw [supportSyndromeMatrix_rank_eq_min alpha
        (fun i => beta i * E i) alpha.injective
        (fun i => mul_ne_zero (hbeta i) (hE i)), Nat.min_eq_right hs_lt_m.le]
    have hO_le_M : O.rank ≤ M.rank := by
      have hsub := Matrix.rank_submatrix_le M Sum.inl
        (id : Fin s → Fin s)
      rw [fullTwoLaneSupportKeyMatrix_ordinaryBlock] at hsub
      exact hsub
    have : s ≤ rho := by
      rw [hOrank] at hO_le_M
      simpa [M, hrank] using hO_le_M
    omega
  refine ⟨hrho_lt_s, ?_⟩
  exact exists_failureRelation_of_fullTwoLane_rank_lt
    sigma alpha beta E hm_le_s hbeta hE (by
      simpa [M, hrank] using hrho_lt_s)
theorem supportSize_eq_rank_or_sharpFailureRelation6401
    {F : Type*} [Field F] {s rho : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F) (beta E : Fin s → F)
    (hs : s ≤ keyErrors6401)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hrank :
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        alpha beta E).rank = rho) :
    s = rho ∨
      (rho < s ∧
        ∃ W₀ W₁ : F[X],
          W₀ ≠ 0 ∧
          W₀.natDegree ≤ 22507 ∧
          W₁.natDegree ≤ 22507 ∧
          TwoLaneFailureRelation sigma alpha E W₀ W₁) := by
  rcases supportSize_eq_rank_or_failureRelation
      sigma alpha beta E hs hbeta hE hrank with hEq | hFail
  · exact Or.inl hEq
  right
  rcases hFail with ⟨hrhos, W₀, W₁, hW₀ne, hW₀deg, hW₁deg, hrel⟩
  refine ⟨hrhos, W₀, W₁, hW₀ne, ?_, ?_, hrel⟩
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hW₀ne] at hW₀deg
    have hwindow := Nat.sub_le_sub_right hs keyFirstLaneRows6401
    rw [fullTwoLane_degree_window_exact6401] at hwindow
    have hnum : keySecondLaneRows6401 = 22508 := by native_decide
    rw [hnum] at hwindow
    omega
  · by_cases hW₁zero : W₁ = 0
    · simp [hW₁zero]
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hW₁zero] at hW₁deg
      have hwindow := Nat.sub_le_sub_right hs keyFirstLaneRows6401
      rw [fullTwoLane_degree_window_exact6401] at hwindow
      have hnum : keySecondLaneRows6401 = 22508 := by native_decide
      rw [hnum] at hwindow
      omega
theorem fixedPolynomial_goodChallenges_card
    {F : Type*} [Field F] [DecidableEq F]
    (challenges : Finset F) (Delta : F[X]) (D : Nat)
    (hDelta : Delta ≠ 0) (hdegree : Delta.natDegree ≤ D) :
    challenges.card - D ≤
      (challenges.filter fun z => Polynomial.eval z Delta ≠ 0).card := by
  have hB : (challenges.filter fun z =>
      Polynomial.eval z Delta = 0).card ≤ D := by
    exact (card_filter_eval_eq_zero_le_natDegree
      challenges Delta hDelta).trans hdegree
  have hpartition :
      (challenges.filter fun z => Polynomial.eval z Delta ≠ 0).card +
        (challenges.filter fun z => Polynomial.eval z Delta = 0).card =
          challenges.card := by
    simpa only [not_not] using
      (Finset.card_filter_add_card_filter_not
        (s := challenges) (fun z => Polynomial.eval z Delta ≠ 0))
  omega
theorem fixedMinor_exactSupport_rootIncidence6401
    {F iota : Type} [Field F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (challenges : Finset F) (Delta : F[X])
    (A : F → Finset iota) (L : iota → F[X])
    (hambient : Fintype.card iota = n6401)
    (hZ : weakCurveSeedInput6401 ≤ challenges.card)
    (hDelta : Delta ≠ 0)
    (hDeltaDegree : Delta.natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hcard : ∀ z ∈ (challenges.filter fun z => Polynomial.eval z Delta ≠ 0),
      (A z).card = rho)
    (hroot : ∀ z ∈ (challenges.filter fun z => Polynomial.eval z Delta ≠ 0),
      ∀ i ∈ A z, Polynomial.eval z (L i) = 0)
    (hdegree : ∀ i,
      (L i).natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hfixed : ∀ z ∈ (challenges.filter fun z => Polynomial.eval z Delta ≠ 0),
      fixedLocatorCoordinates L ⊆ A z) :
    let S := challenges.filter fun z => Polynomial.eval z Delta ≠ 0
    let c := rho - (fixedLocatorCoordinates L).card
    c ≤ keyVariableErrorCap6401 ∧
      (S.biUnion A).card ≤ rho + (S.card - 1) * c := by
  classical
  dsimp only
  let S := challenges.filter fun z => Polynomial.eval z Delta ≠ 0
  let H := fixedLocatorCoordinates L
  let c := rho - H.card
  let D := genericRankMinorDegreeCap6401 rho
  have hSfloor : weakCurveSeedInput6401 - D ≤ S.card := by
    have hgood := fixedPolynomial_goodChallenges_card challenges Delta D
      hDelta hDeltaDegree
    exact (Nat.sub_le_sub_right hZ D).trans hgood
  have hSnonempty : S.Nonempty := by
    have hden : 0 < weakCurveSeedInput6401 - 2 * D := by
      let r : Fin (keyErrors6401 + 1) :=
        ⟨rho, Nat.lt_succ_iff.mpr hrho⟩
      simpa [D, r] using genericRank_incidenceDenominator_pos_scan6401 r
    have : 0 < weakCurveSeedInput6401 - D := by omega
    exact Finset.card_pos.mp (this.trans_le hSfloor)
  have hHrho : H.card ≤ rho := by
    obtain ⟨z, hz⟩ := hSnonempty
    rw [← hcard z hz]
    exact Finset.card_le_card (hfixed z hz)
  have hinc0 : S.card * c ≤ (Fintype.card iota - H.card) * D := by
    exact locator_root_incidence S A L rho D
      (fun z hz => (hcard z hz).ge) hroot hdegree
  have hambient' : H.card ≤ n6401 := by
    rw [← hambient]
    exact Finset.card_le_univ H
  have hrho_n : rho ≤ n6401 := by
    exact hrho.trans (by native_decide)
  have hrewrite : Fintype.card iota - H.card = n6401 - rho + c := by
    rw [hambient]
    dsimp [c]
    exact (Nat.sub_add_sub_cancel hrho_n hHrho).symm
  have hinc : c * (weakCurveSeedInput6401 - D) ≤
      (n6401 - rho + c) * D := by
    calc
      c * (weakCurveSeedInput6401 - D) ≤ c * S.card :=
        Nat.mul_le_mul_left c hSfloor
      _ = S.card * c := Nat.mul_comm _ _
      _ ≤ (Fintype.card iota - H.card) * D := hinc0
      _ = (n6401 - rho + c) * D := by rw [hrewrite]
  have hc : c ≤ keyVariableErrorCap6401 :=
    variableErrors_le_32_of_genericRankIncidence6401 rho c hrho hinc
  refine ⟨hc, ?_⟩
  exact errorSupport_union_card_le S A H rho c hSnonempty hfixed hcard
    (by simp [c, H])
theorem fixedMinor_exactSupport_commonCore6401
    {F iota : Type} [Field F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (challenges owners : Finset F) (Delta : F[X])
    (A : F → Finset iota) (L : iota → F[X])
    (hambient : Fintype.card iota = n6401)
    (hZ : weakCurveSeedInput6401 ≤ challenges.card)
    (hDelta : Delta ≠ 0)
    (hDeltaDegree : Delta.natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hcard : ∀ z ∈ (challenges.filter fun z => Polynomial.eval z Delta ≠ 0),
      (A z).card = rho)
    (hroot : ∀ z ∈ (challenges.filter fun z => Polynomial.eval z Delta ≠ 0),
      ∀ i ∈ A z, Polynomial.eval z (L i) = 0)
    (hdegree : ∀ i,
      (L i).natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hfixed : ∀ z ∈ (challenges.filter fun z => Polynomial.eval z Delta ≠ 0),
      fixedLocatorCoordinates L ⊆ A z)
    (hownersSubset : owners ⊆
      challenges.filter fun z => Polynomial.eval z Delta ≠ 0)
    (hownersCard : owners.card = weakCurveOutput6401) :
    147530 ≤ (Finset.univ \ owners.biUnion A).card ∧
      ownerDegreeCap6401 + 1 ≤
        (Finset.univ \ owners.biUnion A).card := by
  classical
  let S := challenges.filter fun z => Polynomial.eval z Delta ≠ 0
  let H := fixedLocatorCoordinates L
  let c := rho - H.card
  have hfork := fixedMinor_exactSupport_rootIncidence6401 rho hrho challenges Delta A L
    hambient hZ hDelta hDeltaDegree hcard hroot hdegree hfixed
  change c ≤ keyVariableErrorCap6401 ∧
      (S.biUnion A).card ≤ rho + (S.card - 1) * c at hfork
  have hfloor := genericRank_commonCore_floor6401 rho c hrho hfork.1
  have hownersNonempty : owners.Nonempty := by
    apply Finset.card_pos.mp
    rw [hownersCard]
    native_decide
  have hfixedOwners : ∀ z ∈ owners, H ⊆ A z := by
    intro z hz
    exact hfixed z (hownersSubset hz)
  have hcardOwners : ∀ z ∈ owners, (A z).card = rho := by
    intro z hz
    exact hcard z (hownersSubset hz)
  have hunionOwners : (owners.biUnion A).card ≤
      rho + (weakCurveOutput6401 - 1) * c := by
    have h := errorSupport_union_card_le owners A H rho c
      hownersNonempty hfixedOwners hcardOwners (by simp [c, H])
    simpa [hownersCard] using h
  have hsub : owners.biUnion A ⊆ (Finset.univ : Finset iota) := by simp
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, hambient]
  exact ⟨hfloor.1.trans (Nat.sub_le_sub_left hunionOwners n6401),
    hfloor.2.trans (Nat.sub_le_sub_left hunionOwners n6401)⟩
end BCHKSFrobeniusGenericRankFork6401
end ProximityPrize.SubmissionLower
