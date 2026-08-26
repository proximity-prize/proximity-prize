import ProximityPrize.SubmissionLower.BCHKSFrobeniusGenericMinor6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusGlobalMaxRankFork6401
open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusGenericRankFork6401
open BCHKSFrobeniusGenericMinor6401
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
def fullOwnerThreshold45_6401 : Nat := 193291351284887140
def defectOwnerFloor6401 : Nat := 80251890117475683
theorem fullOwnerThreshold45_scan6401 :
    ∀ rho : Fin (keyErrors6401 + 1),
      (n6401 - rho.1) * genericRankMinorDegreeCap6401 rho.1 <
        46 * (fullOwnerThreshold45_6401 -
          genericRankMinorDegreeCap6401 rho.1) := by
  native_decide
theorem fullOwnerThreshold45_endpoint_margin6401 :
    46 * (fullOwnerThreshold45_6401 -
        genericRankMinorDegreeCap6401 keyErrors6401) -
      (n6401 - keyErrors6401) *
        genericRankMinorDegreeCap6401 keyErrors6401 = 40 := by
  native_decide
theorem incidence_rearrange_on_good_pool6401
    (c N D a : Nat) (hD : D ≤ N)
    (h : c * N ≤ (a + c) * D) :
    c * (N - D) ≤ a * D := by
  have hbig : c * (N - D) + c * D ≤ a * D + c * D := by
    calc
      c * (N - D) + c * D = c * N := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hD]
      _ ≤ (a + c) * D := h
      _ = a * D + c * D := by ring
  exact Nat.le_of_add_le_add_right hbig
theorem variableRoots_le_45_of_fullOwnerIncidence6401
    (rho c : Nat) (hrho : rho ≤ keyErrors6401)
    (hinc : c * fullOwnerThreshold45_6401 ≤
      (n6401 - rho + c) * genericRankMinorDegreeCap6401 rho) :
    c ≤ 45 := by
  let r : Fin (keyErrors6401 + 1) :=
    ⟨rho, Nat.lt_succ_iff.mpr hrho⟩
  have hdom :
      (n6401 - rho) * genericRankMinorDegreeCap6401 rho <
        46 * (fullOwnerThreshold45_6401 -
          genericRankMinorDegreeCap6401 rho) := by
    simpa [r] using fullOwnerThreshold45_scan6401 r
  have hpos : 0 < fullOwnerThreshold45_6401 -
      genericRankMinorDegreeCap6401 rho := by
    by_contra hzero
    have : fullOwnerThreshold45_6401 -
        genericRankMinorDegreeCap6401 rho = 0 := Nat.eq_zero_of_not_pos hzero
    rw [this, mul_zero] at hdom
    omega
  have hrearranged : c *
        (fullOwnerThreshold45_6401 - genericRankMinorDegreeCap6401 rho) ≤
      (n6401 - rho) * genericRankMinorDegreeCap6401 rho :=
    incidence_rearrange_on_good_pool6401 c fullOwnerThreshold45_6401
      (genericRankMinorDegreeCap6401 rho) (n6401 - rho)
      (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hpos)) hinc
  by_contra hc
  have hc46 : 46 ≤ c := by omega
  have hlower :
      46 * (fullOwnerThreshold45_6401 -
          genericRankMinorDegreeCap6401 rho) ≤
        c * (fullOwnerThreshold45_6401 -
          genericRankMinorDegreeCap6401 rho) :=
    Nat.mul_le_mul_right _ hc46
  exact (Nat.not_lt_of_ge (hlower.trans hrearranged)) hdom
theorem fixedMinor_goodExactOwners_rootIncidence45_6401
    {F iota : Type} [Field F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (owners : Finset F) (A : F → Finset iota) (L : iota → F[X])
    (hambient : Fintype.card iota = n6401)
    (howners : fullOwnerThreshold45_6401 ≤ owners.card)
    (hcard : ∀ z ∈ owners, (A z).card = rho)
    (hroot : ∀ z ∈ owners, ∀ i ∈ A z,
      Polynomial.eval z (L i) = 0)
    (hdegree : ∀ i,
      (L i).natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hfixed : ∀ z ∈ owners, fixedLocatorCoordinates L ⊆ A z) :
    let H := fixedLocatorCoordinates L
    let c := rho - H.card
    c ≤ 45 ∧
      (owners.biUnion A).card ≤ rho + (owners.card - 1) * c := by
  classical
  dsimp only
  let H := fixedLocatorCoordinates L
  let c := rho - H.card
  let D := genericRankMinorDegreeCap6401 rho
  have hownersNonempty : owners.Nonempty := by
    apply Finset.card_pos.mp
    have hthresholdPos : 0 < fullOwnerThreshold45_6401 := by native_decide
    exact hthresholdPos.trans_le howners
  have hHrho : H.card ≤ rho := by
    obtain ⟨z, hz⟩ := hownersNonempty
    rw [← hcard z hz]
    exact Finset.card_le_card (hfixed z hz)
  have hinc0 : owners.card * c ≤
      (Fintype.card iota - H.card) * D :=
    locator_root_incidence owners A L rho D
      (fun z hz => (hcard z hz).ge) hroot hdegree
  have hrho_n : rho ≤ n6401 := hrho.trans (by native_decide)
  have hrewrite : Fintype.card iota - H.card = n6401 - rho + c := by
    rw [hambient]
    dsimp [c]
    exact (Nat.sub_add_sub_cancel hrho_n hHrho).symm
  have hinc : c * fullOwnerThreshold45_6401 ≤
      (n6401 - rho + c) * D := by
    calc
      c * fullOwnerThreshold45_6401 ≤ c * owners.card :=
        Nat.mul_le_mul_left c howners
      _ = owners.card * c := Nat.mul_comm _ _
      _ ≤ (Fintype.card iota - H.card) * D := hinc0
      _ = (n6401 - rho + c) * D := by rw [hrewrite]
  have hc := variableRoots_le_45_of_fullOwnerIncidence6401 rho c hrho hinc
  refine ⟨hc, ?_⟩
  exact errorSupport_union_card_le owners A H rho c hownersNonempty
    hfixed hcard (by simp [c, H])
theorem fixedMinor_goodExactOwners_commonCore45_6401
    {F iota : Type} [Field F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (owners chosen : Finset F) (A : F → Finset iota) (L : iota → F[X])
    (hambient : Fintype.card iota = n6401)
    (howners : fullOwnerThreshold45_6401 ≤ owners.card)
    (hcard : ∀ z ∈ owners, (A z).card = rho)
    (hroot : ∀ z ∈ owners, ∀ i ∈ A z,
      Polynomial.eval z (L i) = 0)
    (hdegree : ∀ i,
      (L i).natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hfixed : ∀ z ∈ owners, fixedLocatorCoordinates L ⊆ A z)
    (hchosen : chosen ⊆ owners)
    (hchosenCard : chosen.card = weakCurveOutput6401) :
    132164 ≤ (Finset.univ \ chosen.biUnion A).card ∧
      ownerDegreeCap6401 + 1 ≤
        (Finset.univ \ chosen.biUnion A).card := by
  classical
  let H := fixedLocatorCoordinates L
  let c := rho - H.card
  have hfork := fixedMinor_goodExactOwners_rootIncidence45_6401
    rho hrho owners A L hambient howners hcard hroot hdegree hfixed
  change c ≤ 45 ∧
      (owners.biUnion A).card ≤ rho + (owners.card - 1) * c at hfork
  have hchosenNonempty : chosen.Nonempty := by
    apply Finset.card_pos.mp
    rw [hchosenCard]
    native_decide
  have hfixedChosen : ∀ z ∈ chosen, H ⊆ A z := by
    intro z hz
    exact hfixed z (hchosen hz)
  have hcardChosen : ∀ z ∈ chosen, (A z).card = rho := by
    intro z hz
    exact hcard z (hchosen hz)
  have hunion : (chosen.biUnion A).card ≤
      rho + (weakCurveOutput6401 - 1) * c := by
    have h := errorSupport_union_card_le chosen A H rho c
      hchosenNonempty hfixedChosen hcardChosen (by simp [c, H])
    simpa [hchosenCard] using h
  have hcap : rho + (weakCurveOutput6401 - 1) * c ≤ 129980 := by
    norm_num [weakCurveOutput6401,
      BCHKSSphericalL3Radius76855Audit6401.targetSeedOutput,
      keyErrors6401, n6401, ownerDegreeCap6401, bchksErrors6401]
      at hrho hfork ⊢
    omega
  have hunionCap : (chosen.biUnion A).card ≤ 129980 :=
    hunion.trans hcap
  have hsub : chosen.biUnion A ⊆ (Finset.univ : Finset iota) := by simp
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, hambient]
  norm_num [n6401, ownerDegreeCap6401]
  omega
def determinantGoodOwners
    {F : Type*} [Field F] [DecidableEq F]
    (owners : Finset F) (Delta : F[X]) : Finset F :=
  owners.filter fun z => Polynomial.eval z Delta ≠ 0
def exactRankSupportOwners
    {F : Type*} [DecidableEq F]
    (good : Finset F) (supportSize : F → Nat) (rho : Nat) : Finset F :=
  good.filter fun z => supportSize z = rho
def rankDefectSupportOwners
    {F : Type*} [DecidableEq F]
    (good : Finset F) (supportSize : F → Nat) (rho : Nat) : Finset F :=
  good.filter fun z => rho < supportSize z
theorem genericRankMinorDegreeCap_le_endpoint6401 :
    ∀ rho : Fin (keyErrors6401 + 1),
      genericRankMinorDegreeCap6401 rho.1 ≤
        genericRankMinorDegreeCap6401 keyErrors6401 := by
  native_decide
theorem globalGoodPoolFloor6401 :
    weakCurveSeedInput6401 -
      genericRankMinorDegreeCap6401 keyErrors6401 =
        273543241402362822 := by
  native_decide
theorem goodPool_fullOrDefectMass6401
    {F : Type*} [Field F] [DecidableEq F]
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (owners : Finset F) (Delta : F[X]) (supportSize : F → Nat)
    (howners : weakCurveSeedInput6401 ≤ owners.card)
    (hDelta : Delta ≠ 0)
    (hdegree : Delta.natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hsize : ∀ z ∈ determinantGoodOwners owners Delta,
      rho ≤ supportSize z) :
    fullOwnerThreshold45_6401 ≤
        (exactRankSupportOwners (determinantGoodOwners owners Delta)
          supportSize rho).card ∨
      defectOwnerFloor6401 ≤
        (rankDefectSupportOwners (determinantGoodOwners owners Delta)
          supportSize rho).card := by
  classical
  let G := determinantGoodOwners owners Delta
  let Exact := exactRankSupportOwners G supportSize rho
  let Defect := rankDefectSupportOwners G supportSize rho
  have hgoodRaw := fixedPolynomial_goodChallenges_card owners Delta
    (genericRankMinorDegreeCap6401 rho) hDelta hdegree
  have hDle : genericRankMinorDegreeCap6401 rho ≤
      genericRankMinorDegreeCap6401 keyErrors6401 := by
    let r : Fin (keyErrors6401 + 1) :=
      ⟨rho, Nat.lt_succ_iff.mpr hrho⟩
    simpa [r] using genericRankMinorDegreeCap_le_endpoint6401 r
  have hGfloor : 273543241402362822 ≤ G.card := by
    rw [← globalGoodPoolFloor6401]
    have hsub : weakCurveSeedInput6401 -
        genericRankMinorDegreeCap6401 keyErrors6401 ≤
      weakCurveSeedInput6401 - genericRankMinorDegreeCap6401 rho :=
      Nat.sub_le_sub_left hDle weakCurveSeedInput6401
    exact hsub.trans ((Nat.sub_le_sub_right howners _).trans hgoodRaw)
  have hpartition : Exact.card + Defect.card = G.card := by
    have hnot : G.filter (fun z => ¬ supportSize z = rho) = Defect := by
      ext z
      simp only [Finset.mem_filter, Defect, rankDefectSupportOwners]
      constructor
      · rintro ⟨hz, hne⟩
        have hzDet : z ∈ determinantGoodOwners owners Delta := by
          simpa [G] using hz
        exact ⟨hz, lt_of_le_of_ne (hsize z hzDet) (Ne.symm hne)⟩
      · rintro ⟨hz, hlt⟩
        exact ⟨hz, ne_of_gt hlt⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := G) (fun z => supportSize z = rho)
    simpa [Exact, exactRankSupportOwners, hnot] using hsplit
  by_cases hfull : fullOwnerThreshold45_6401 ≤ Exact.card
  · exact Or.inl hfull
  · right
    have hfullLt : Exact.card < fullOwnerThreshold45_6401 :=
      Nat.lt_of_not_ge hfull
    change defectOwnerFloor6401 ≤ Defect.card
    dsimp only [defectOwnerFloor6401, fullOwnerThreshold45_6401] at hfullLt ⊢
    omega
theorem goodPool_fullOrManyFailureRelations6401
    {F : Type*} [Field F] [DecidableEq F]
    (sigma : F →+* F) (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (owners : Finset F) (Delta : F[X])
    (supportSize : F → Nat)
    (alphaS : (z : F) → Fin (supportSize z) ↪ F)
    (beta E : (z : F) → Fin (supportSize z) → F)
    (howners : weakCurveSeedInput6401 ≤ owners.card)
    (hDelta : Delta ≠ 0)
    (hdegree : Delta.natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hsize : ∀ z ∈ determinantGoodOwners owners Delta,
      supportSize z ≤ keyErrors6401)
    (hbeta : ∀ z ∈ determinantGoodOwners owners Delta, ∀ i,
      beta z i ≠ 0)
    (hE : ∀ z ∈ determinantGoodOwners owners Delta, ∀ i,
      E z i ≠ 0)
    (hrank : ∀ z ∈ determinantGoodOwners owners Delta,
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (alphaS z) (beta z) (E z)).rank = rho) :
    fullOwnerThreshold45_6401 ≤
        (exactRankSupportOwners (determinantGoodOwners owners Delta)
          supportSize rho).card ∨
      (defectOwnerFloor6401 ≤
          (rankDefectSupportOwners (determinantGoodOwners owners Delta)
            supportSize rho).card ∧
        ∀ z ∈ rankDefectSupportOwners
            (determinantGoodOwners owners Delta) supportSize rho,
          ∃ W₀ W₁ : F[X],
            W₀ ≠ 0 ∧
            W₀.degree < (supportSize z - keyFirstLaneRows6401 : Nat) ∧
            W₁.degree < (supportSize z - keyFirstLaneRows6401 : Nat) ∧
            TwoLaneFailureRelation sigma (alphaS z) (E z) W₀ W₁) := by
  let G := determinantGoodOwners owners Delta
  have hrhoSize : ∀ z ∈ G, rho ≤ supportSize z := by
    intro z hz
    rw [← hrank z hz]
    simpa using Matrix.rank_le_card_width
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (alphaS z) (beta z) (E z))
  rcases goodPool_fullOrDefectMass6401 rho hrho owners Delta supportSize
      howners hDelta hdegree hrhoSize with hfull | hdefect
  · exact Or.inl hfull
  right
  refine ⟨hdefect, ?_⟩
  intro z hz
  have hzG : z ∈ G := (Finset.mem_filter.mp hz).1
  have hrhos : rho < supportSize z := (Finset.mem_filter.mp hz).2
  rcases supportSize_eq_rank_or_failureRelation sigma (alphaS z)
      (beta z) (E z) (hsize z hzG) (hbeta z hzG) (hE z hzG)
      (hrank z hzG) with heq | hfailure
  · omega
  · exact hfailure.2
theorem goodPool_commonCoreOrManyFailureRelations6401
    {F iota : Type} [Field F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (owners : Finset F) (Delta : F[X])
    (supportSize : F → Nat) (A : F → Finset iota) (L : iota → F[X])
    (alphaS : (z : F) → Fin (supportSize z) ↪ F)
    (beta E : (z : F) → Fin (supportSize z) → F)
    (hambient : Fintype.card iota = n6401)
    (howners : weakCurveSeedInput6401 ≤ owners.card)
    (hDelta : Delta ≠ 0)
    (hdegreeDelta : Delta.natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hsize : ∀ z ∈ determinantGoodOwners owners Delta,
      supportSize z ≤ keyErrors6401)
    (hbeta : ∀ z ∈ determinantGoodOwners owners Delta, ∀ i,
      beta z i ≠ 0)
    (hE : ∀ z ∈ determinantGoodOwners owners Delta, ∀ i,
      E z i ≠ 0)
    (hrank : ∀ z ∈ determinantGoodOwners owners Delta,
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (alphaS z) (beta z) (E z)).rank = rho)
    (hcard : ∀ z ∈ exactRankSupportOwners
        (determinantGoodOwners owners Delta) supportSize rho,
      (A z).card = rho)
    (hroot : ∀ z ∈ exactRankSupportOwners
        (determinantGoodOwners owners Delta) supportSize rho,
      ∀ i ∈ A z, Polynomial.eval z (L i) = 0)
    (hdegreeL : ∀ i,
      (L i).natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hfixed : ∀ z ∈ exactRankSupportOwners
        (determinantGoodOwners owners Delta) supportSize rho,
      fixedLocatorCoordinates L ⊆ A z) :
    (∃ chosen : Finset F,
        chosen ⊆ exactRankSupportOwners
          (determinantGoodOwners owners Delta) supportSize rho ∧
        chosen.card = weakCurveOutput6401 ∧
        132164 ≤ (Finset.univ \ chosen.biUnion A).card ∧
        ownerDegreeCap6401 + 1 ≤
          (Finset.univ \ chosen.biUnion A).card) ∨
      (defectOwnerFloor6401 ≤
          (rankDefectSupportOwners (determinantGoodOwners owners Delta)
            supportSize rho).card ∧
        ∀ z ∈ rankDefectSupportOwners
            (determinantGoodOwners owners Delta) supportSize rho,
          ∃ W₀ W₁ : F[X],
            W₀ ≠ 0 ∧
            W₀.degree < (supportSize z - keyFirstLaneRows6401 : Nat) ∧
            W₁.degree < (supportSize z - keyFirstLaneRows6401 : Nat) ∧
            TwoLaneFailureRelation sigma (alphaS z) (E z) W₀ W₁) := by
  let Exact := exactRankSupportOwners
    (determinantGoodOwners owners Delta) supportSize rho
  rcases goodPool_fullOrManyFailureRelations6401 sigma rho hrho owners Delta
      supportSize alphaS beta E howners hDelta hdegreeDelta hsize hbeta hE
      hrank with hfull | hdefect
  · have hchoose : weakCurveOutput6401 ≤ Exact.card := by
      have hsmall : weakCurveOutput6401 ≤ fullOwnerThreshold45_6401 := by
        native_decide
      exact hsmall.trans hfull
    obtain ⟨chosen, hchosen, hchosenCard⟩ :=
      Finset.exists_subset_card_eq hchoose
    have hcore := fixedMinor_goodExactOwners_commonCore45_6401
      rho hrho Exact chosen A L hambient hfull hcard hroot hdegreeL hfixed
      hchosen hchosenCard
    exact Or.inl ⟨chosen, hchosen, hchosenCard, hcore⟩
  · exact Or.inr hdefect
end BCHKSFrobeniusGlobalMaxRankFork6401
end ProximityPrize.SubmissionLower
