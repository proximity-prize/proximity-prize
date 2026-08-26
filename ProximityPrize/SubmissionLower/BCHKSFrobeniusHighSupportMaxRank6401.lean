import ProximityPrize.SubmissionLower.BCHKSJ0LinearYLowSupport6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusGlobalMaxRankIRS6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusPrimitiveDegreeDrop6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusHighSupportMaxRank6401
open Polynomial
open ProximityPrize.Benchmark
open BCHKSJ0ConcreteGlobalInput6400
open BCHKSJ0LinearYLowSupport6401
open BCHKSLinearYLowSupport6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusGenericRankFork6401
open BCHKSFrobeniusGenericMinor6401
open BCHKSFrobeniusGlobalMaxRankFork6401
open BCHKSFrobeniusGlobalMaxRankIRS6401
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSFrobeniusKernelPairSpace6401
open BCHKSFrobeniusPrimitiveDegreeDrop6401
open BCHKSFrobeniusPrimitiveZeroExtraction6401
open BCHKSFrobeniusPrimitiveZeroIRS6401
open BCHKSFrobeniusSupportStratification6401
open BCHKSFrobeniusConstantPairClosure6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
abbrev BenchmarkField := IRSProfile.Field
abbrev Index := IRSProfile.Index
def lowActualSupportOwners6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X])
    (S : Finset BenchmarkField) : Finset BenchmarkField :=
  S.filter fun z ↦
    (actualErrorSupport6401 u0 u1 P z).card ≤ 65536
def highActualSupportOwners6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X])
    (S : Finset BenchmarkField) : Finset BenchmarkField :=
  S.filter fun z ↦
    65537 ≤ (actualErrorSupport6401 u0 u1 P z).card
def restrictActualAgreements6401
    {received : Fin 2 → Index → BenchmarkField}
    {S : Finset BenchmarkField}
    {agreements : BenchmarkField → Finset Index}
    (J : J0BenchmarkInterpolant received S agreements)
    (T : Finset BenchmarkField) (hTS : T ⊆ S) :
    J0BenchmarkInterpolant received T
      (actualAgreementSet6401 (received 0) (received 1) J.P) where
  P := J.P
  Q := J.Q
  Q_ne := J.Q_ne
  root_degree := fun z hz ↦ J.root_degree z (hTS hz)
  agrees := by
    intro z hz i hi
    exact (Finset.mem_filter.mp hi).2
  vanishing := fun z hz ↦ J.vanishing z (hTS hz)
  support_caps := J.support_caps
theorem polynomialAffineCurveWitness_mono6401
    {F : Type*} [Field F] {T S : Finset F}
    {P : F → Polynomial F} (hTS : T ⊆ S)
    (hcurve : PolynomialAffineCurveWitness6401 T P) :
    PolynomialAffineCurveWitness6401 S P := by
  rcases hcurve with ⟨p0, p1, hp0, hp1, U, hUT, hUcard, hline⟩
  exact ⟨p0, p1, hp0, hp1, U, hUT.trans hTS, hUcard, hline⟩
theorem curve_or_lowActualSupport_card_le6401
    {received : Fin 2 → Index → BenchmarkField}
    {S : Finset BenchmarkField}
    {agreements : BenchmarkField → Finset Index}
    (J : J0BenchmarkInterpolant received S agreements) :
    PolynomialAffineCurveWitness6401 S J.P ∨
      (lowActualSupportOwners6401
        (received 0) (received 1) J.P S).card ≤
          linearYMinorDegreeCap6401 := by
  classical
  let T := lowActualSupportOwners6401
    (received 0) (received 1) J.P S
  have hTS : T ⊆ S := Finset.filter_subset _ _
  let JT := restrictActualAgreements6401 J T hTS
  have hmany : ∀ z ∈ T,
      196608 ≤
        (actualAgreementSet6401 (received 0) (received 1) J.P z).card := by
    intro z hz
    have herr : (actualErrorSupport6401
        (received 0) (received 1) J.P z).card ≤ 65536 :=
      (Finset.mem_filter.mp hz).2
    have hsum := actualAgreement_add_error_card6401
      (received 0) (received 1) J.P z
    norm_num [n6401] at hsum ⊢
    omega
  have hfork := ProximityPrize.SubmissionLower.BCHKSJ0LinearYLowSupport6401.J0BenchmarkInterpolant.lowSupportOwners_curve_or_cap6401 JT hmany
  rcases hfork with hcurve | hcap
  · exact Or.inl (polynomialAffineCurveWitness_mono6401 hTS hcurve)
  · exact Or.inr hcap
def retainedHighSupportOwnerFloor6401 : Nat :=
  weakCurveSeedInput6401 - linearYMinorDegreeCap6401
theorem retainedHighSupportOwnerFloor_exact6401 :
    retainedHighSupportOwnerFloor6401 = 273591190752810939 := by
  native_decide
theorem highActualSupport_card_lower6401
    {received : Fin 2 → Index → BenchmarkField}
    {S : Finset BenchmarkField}
    {agreements : BenchmarkField → Finset Index}
    (J : J0BenchmarkInterpolant received S agreements)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S J.P) :
    retainedHighSupportOwnerFloor6401 ≤
      (highActualSupportOwners6401
        (received 0) (received 1) J.P S).card := by
  classical
  have hlow := (curve_or_lowActualSupport_card_le6401 J).resolve_left hfail
  let L := lowActualSupportOwners6401
    (received 0) (received 1) J.P S
  let H := highActualSupportOwners6401
    (received 0) (received 1) J.P S
  have hHnot : S.filter (fun z ↦
      ¬ (actualErrorSupport6401
        (received 0) (received 1) J.P z).card ≤ 65536) = H := by
    ext z
    simp only [Finset.mem_filter, H, highActualSupportOwners6401]
    constructor <;> rintro ⟨hz, hs⟩
    · exact ⟨hz, by omega⟩
    · exact ⟨hz, by omega⟩
  have hpartition : L.card + H.card = S.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S) (fun z ↦
        (actualErrorSupport6401
          (received 0) (received 1) J.P z).card ≤ 65536)
    rw [hHnot] at hsplit
    simpa [L, lowActualSupportOwners6401] using hsplit
  change retainedHighSupportOwnerFloor6401 ≤ H.card
  change L.card ≤ linearYMinorDegreeCap6401 at hlow
  dsimp [retainedHighSupportOwnerFloor6401]
  omega
theorem actualErrorSupportFullStack_rank_ge_rows_of_highSupport6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X])
    (z : BenchmarkField)
    (hhigh : 65537 ≤
      (actualErrorSupport6401 u0 u1 P z).card) :
    keyFirstLaneRows6401 ≤
      (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank := by
  classical
  let support := actualErrorSupportEmbedding6401 u0 u1 P z
  let locators := support.trans IRSProfile.domain
  let E : Fin (actualErrorSupport6401 u0 u1 P z).card →
      BenchmarkField := fun j ↦
    u0 (support j) + z * u1 (support j) -
      Polynomial.eval (IRSProfile.domain (support j)) (P z)
  let beta : Fin (actualErrorSupport6401 u0 u1 P z).card →
      BenchmarkField := fun j ↦ syndromeWeight locators j
  have hE : ∀ j, E j ≠ 0 := by
    intro j
    apply (ownerError_ne_zero_iff_mem_actualErrorSupport6401
      u0 u1 P z (support j)).2
    exact (mem_range_actualErrorSupportEmbedding6401
      u0 u1 P z (support j)).1 ⟨j, rfl⟩
  have hordinary :
      (supportSyndromeMatrix keyFirstLaneRows6401
        (actualErrorSupport6401 u0 u1 P z).card locators
        (fun j ↦ beta j * E j)).rank = keyFirstLaneRows6401 := by
    apply supportSyndromeMatrix_rank_eq_rows
    · exact locators.injective
    · intro j
      exact mul_ne_zero (syndromeWeight_ne_zero locators j) (hE j)
    · exact (show keyFirstLaneRows6401 ≤ 65537 by native_decide).trans
        hhigh
  have hsub := Matrix.rank_submatrix_le
    (actualErrorSupportFullStack6401 sigma u0 u1 P z) Sum.inl
      (id : Fin (actualErrorSupport6401 u0 u1 P z).card →
        Fin (actualErrorSupport6401 u0 u1 P z).card)
  change (supportSyndromeMatrix keyFirstLaneRows6401
      (actualErrorSupport6401 u0 u1 P z).card locators
      (fun j ↦ beta j * E j)).rank ≤
        (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank at hsub
  rwa [hordinary] at hsub
theorem highSupport_rankRows_card_le_constantPrimitiveCap6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hsigma : ∀ z, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    {received : Fin 2 → Index → BenchmarkField}
    {S : Finset BenchmarkField}
    {agreements : BenchmarkField → Finset Index}
    (J : J0BenchmarkInterpolant received S agreements)
    (hrow : ∀ z ∈ S, a6401 ≤ (agreements z).card)
    (hrank : ∀ z ∈ highActualSupportOwners6401
      (received 0) (received 1) J.P S,
      (actualErrorSupportFullStack6401 sigma
        (received 0) (received 1) J.P z).rank = keyFirstLaneRows6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S J.P) :
    (highActualSupportOwners6401
      (received 0) (received 1) J.P S).card ≤
        constantPrimitiveFamilyCap6401 := by
  classical
  let H := highActualSupportOwners6401
    (received 0) (received 1) J.P S
  have hHS : H ⊆ S := Finset.filter_subset _ _
  have hfailH : ¬ PolynomialAffineCurveWitness6401 H J.P := by
    intro hcurve
    exact hfail (polynomialAffineCurveWitness_mono6401 hHS hcurve)
  apply rankEqualFirstLaneRowsOwners_card_le_cap6401_of_no_curve
    sigma IRSProfile.domain hfixed
      (frobeniusFixedScalars_card_le_q6401_of_pow sigma hsigma)
      (received 0) (received 1) H agreements J.P
      (supportSize := fun z ↦ (actualErrorSupport6401
        (received 0) (received 1) J.P z).card)
      (support := actualErrorSupportEmbedding6401
        (received 0) (received 1) J.P)
      (hfail := hfailH)
  · intro z hz
    exact J.root_degree z (hHS hz)
  · intro z hz
    exact hrow z (hHS hz)
  · intro z hz i hi
    exact J.agrees z (hHS hz) i hi
  · intro z hz i
    exact (ownerError_ne_zero_iff_mem_actualErrorSupport6401
      (received 0) (received 1) J.P z i).trans
        (mem_range_actualErrorSupportEmbedding6401
          (received 0) (received 1) J.P z i).symm
  · intro z hz
    have hs := (Finset.mem_filter.mp hz).2
    exact (show keyFirstLaneRows6401 < 65537 by native_decide).trans_le hs
  · intro z hz
    exact actualErrorSupport_card_le_target6401
      (received 0) (received 1) J.P agreements z
        (hrow z (hHS hz)) (J.agrees z (hHS hz))
  · intro z hz
    exact hrank z hz
theorem highSupport_maxRank_ge_rows_add_one6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hsigma : ∀ z, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    {received : Fin 2 → Index → BenchmarkField}
    {S : Finset BenchmarkField}
    {agreements : BenchmarkField → Finset Index}
    (J : J0BenchmarkInterpolant received S agreements)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hrow : ∀ z ∈ S, a6401 ≤ (agreements z).card)
    (rho : Nat)
    (hrankUpper : ∀ z ∈ highActualSupportOwners6401
      (received 0) (received 1) J.P S,
      (actualErrorSupportFullStack6401 sigma
        (received 0) (received 1) J.P z).rank ≤ rho)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S J.P) :
    keyFirstLaneRows6401 + 1 ≤ rho := by
  classical
  by_contra hnot
  have hrho : rho ≤ keyFirstLaneRows6401 := by omega
  let H := highActualSupportOwners6401
    (received 0) (received 1) J.P S
  have hrank : ∀ z ∈ H,
      (actualErrorSupportFullStack6401 sigma
        (received 0) (received 1) J.P z).rank = keyFirstLaneRows6401 := by
    intro z hz
    have hge := actualErrorSupportFullStack_rank_ge_rows_of_highSupport6401
      sigma (received 0) (received 1) J.P z (Finset.mem_filter.mp hz).2
    exact Nat.le_antisymm ((hrankUpper z hz).trans hrho) hge
  have hcap := highSupport_rankRows_card_le_constantPrimitiveCap6401
    sigma hsigma hfixed J hrow hrank hfail
  have hfloor := highActualSupport_card_lower6401 J hlarge hfail
  change retainedHighSupportOwnerFloor6401 ≤ H.card at hfloor
  change H.card ≤ constantPrimitiveFamilyCap6401 at hcap
  have hnum : constantPrimitiveFamilyCap6401 <
      retainedHighSupportOwnerFloor6401 := by native_decide
  omega
def retainedHighGoodPoolFloor6401 : Nat :=
  retainedHighSupportOwnerFloor6401 -
    genericRankMinorDegreeCap6401 keyErrors6401
def retainedHighDefectFloor6401 : Nat :=
  retainedHighGoodPoolFloor6401 - (fullOwnerThreshold45_6401 - 1)
theorem retainedHighMass_constants_exact6401 :
    retainedHighGoodPoolFloor6401 = 273543232812362693 ∧
      retainedHighDefectFloor6401 = 80251881527475554 := by
  native_decide
theorem retainedHigh_goodPool_massFork6401
    {F : Type*} [Field F] [DecidableEq F]
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (owners : Finset F) (Delta : F[X])
    (supportSize : F → Nat)
    (howners : retainedHighSupportOwnerFloor6401 ≤ owners.card)
    (hDelta : Delta ≠ 0)
    (hdegree : Delta.natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hhigh : ∀ z ∈ owners, 65537 ≤ supportSize z)
    (hsize : ∀ z ∈ determinantGoodOwners owners Delta,
      rho ≤ supportSize z) :
    (rho < 65537 →
      retainedHighGoodPoolFloor6401 ≤
        (rankDefectSupportOwners
          (determinantGoodOwners owners Delta) supportSize rho).card) ∧
      (fullOwnerThreshold45_6401 ≤
          (exactRankSupportOwners
            (determinantGoodOwners owners Delta) supportSize rho).card ∨
        retainedHighDefectFloor6401 ≤
          (rankDefectSupportOwners
            (determinantGoodOwners owners Delta) supportSize rho).card) := by
  classical
  let G := determinantGoodOwners owners Delta
  let Exact := exactRankSupportOwners G supportSize rho
  let Defect := rankDefectSupportOwners G supportSize rho
  have hDle : genericRankMinorDegreeCap6401 rho ≤
      genericRankMinorDegreeCap6401 keyErrors6401 := by
    let r : Fin (keyErrors6401 + 1) :=
      ⟨rho, Nat.lt_succ_iff.mpr hrho⟩
    simpa [r] using genericRankMinorDegreeCap_le_endpoint6401 r
  have hgoodRaw := fixedPolynomial_goodChallenges_card owners Delta
    (genericRankMinorDegreeCap6401 rho) hDelta hdegree
  have hGfloor : retainedHighGoodPoolFloor6401 ≤ G.card := by
    dsimp [retainedHighGoodPoolFloor6401]
    have hsub : retainedHighSupportOwnerFloor6401 -
        genericRankMinorDegreeCap6401 keyErrors6401 ≤
      retainedHighSupportOwnerFloor6401 -
        genericRankMinorDegreeCap6401 rho :=
      Nat.sub_le_sub_left hDle retainedHighSupportOwnerFloor6401
    exact hsub.trans ((Nat.sub_le_sub_right howners _).trans hgoodRaw)
  have hpartition : Exact.card + Defect.card = G.card := by
    have hnot : G.filter (fun z ↦ ¬ supportSize z = rho) = Defect := by
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
      (s := G) (fun z ↦ supportSize z = rho)
    simpa [Exact, exactRankSupportOwners, hnot] using hsplit
  constructor
  · intro hrhoSmall
    have hExactEmpty : Exact = ∅ := by
      ext z
      constructor
      · intro hz
        have hzG := (Finset.mem_filter.mp hz).1
        have hzEq := (Finset.mem_filter.mp hz).2
        have hzOwner : z ∈ owners := (Finset.mem_filter.mp hzG).1
        have hzHigh := hhigh z hzOwner
        omega
      · simp
    rw [hExactEmpty, Finset.card_empty, Nat.zero_add] at hpartition
    change retainedHighGoodPoolFloor6401 ≤ Defect.card
    rw [hpartition]
    exact hGfloor
  · by_cases hfull : fullOwnerThreshold45_6401 ≤ Exact.card
    · exact Or.inl hfull
    · right
      have hfullLt : Exact.card < fullOwnerThreshold45_6401 :=
        Nat.lt_of_not_ge hfull
      change retainedHighDefectFloor6401 ≤ Defect.card
      dsimp [retainedHighDefectFloor6401]
      omega
theorem retainedHigh_smallExcess_allGoodDefect6401
    {F : Type*} [Field F] [DecidableEq F]
    (rho h : Nat) (hrho : rho ≤ keyErrors6401)
    (hrhoEq : rho = keyFirstLaneRows6401 + h) (hh : h ≤ 11254)
    (owners : Finset F) (Delta : F[X])
    (supportSize : F → Nat)
    (howners : retainedHighSupportOwnerFloor6401 ≤ owners.card)
    (hDelta : Delta ≠ 0)
    (hdegree : Delta.natDegree ≤ genericRankMinorDegreeCap6401 rho)
    (hhigh : ∀ z ∈ owners, 65537 ≤ supportSize z)
    (hsize : ∀ z ∈ determinantGoodOwners owners Delta,
      rho ≤ supportSize z) :
    retainedHighGoodPoolFloor6401 ≤
      (rankDefectSupportOwners
        (determinantGoodOwners owners Delta) supportSize rho).card := by
  have hrhoSmall : rho < 65537 := by
    rw [hrhoEq]
    norm_num [keyFirstLaneRows6401, keyRedundancy6401,
      keyErrors6401, n6401, ownerDegreeCap6401,
      ProximityPrize.SubmissionLower.bchksErrors6401]
    omega
  exact (retainedHigh_goodPool_massFork6401 rho hrho owners Delta
    supportSize howners hDelta hdegree hhigh hsize).1 hrhoSmall
theorem highSupport_defect_kernelProfile6401
    {F : Type*} [Field F] {s rho h : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F)
    (beta E : Fin s → F)
    (hsupport : 65537 ≤ s) (hsupper : s ≤ keyErrors6401)
    (hrhoEq : rho = keyFirstLaneRows6401 + h)
    (hdefect : rho < s)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hrank :
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        alpha beta E).rank = rho) :
    let delta := s - rho
    Module.finrank F
        (LinearMap.ker
          (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
            alpha beta E).mulVecLin) = delta ∧
      11255 ≤ h + delta ∧
      (5628 ≤ h ∨ 5628 ≤ delta) ∧
      ∃ A B : F[X],
        (A ≠ 0 ∨ B ≠ 0) ∧ IsCoprime A B ∧
        max A.natDegree B.natDegree ≤ h ∧
        ∀ v : LinearMap.ker
            (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
              alpha beta E).mulVecLin,
          ∃ H : F[X],
            (fullKernelFailurePairLinear sigma alpha
              keyFirstLaneRows6401 (by omega) beta E v).1.1 = H * A ∧
            (fullKernelFailurePairLinear sigma alpha
              keyFirstLaneRows6401 (by omega) beta E v).2.1 = H * B := by
  dsimp only
  let M := fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
    alpha beta E
  let delta := s - rho
  have hrows : keyFirstLaneRows6401 ≤ s := by
    rw [hrhoEq] at hdefect
    omega
  have hfin : Module.finrank F (LinearMap.ker M.mulVecLin) = delta := by
    rw [fullTwoLane_kernel_finrank_eq_sub_rank]
    simpa [M, delta, hrank]
  have hdelta : 0 < delta := by
    dsimp [delta]
    omega
  have hsum : 11255 ≤ h + delta := by
    dsimp [delta]
    rw [hrhoEq]
    norm_num [keyFirstLaneRows6401, keyRedundancy6401,
      keyErrors6401, n6401, ownerDegreeCap6401,
      ProximityPrize.SubmissionLower.bchksErrors6401] at hsupport ⊢
    omega
  have hbalanced : 5628 ≤ h ∨ 5628 ≤ delta := by
    omega
  have hwindow : 0 < s - keyFirstLaneRows6401 := by omega
  have hmass :
      (s - keyFirstLaneRows6401 - 1) +
          (s - keyFirstLaneRows6401 - 1) < s := by
    norm_num [keyFirstLaneRows6401, keyRedundancy6401,
      keyErrors6401, n6401, ownerDegreeCap6401,
      ProximityPrize.SubmissionLower.bchksErrors6401] at hsupper ⊢
    omega
  have hnull : 0 < Module.finrank F (LinearMap.ker M.mulVecLin) := by
    rw [hfin]
    exact hdelta
  obtain ⟨A, B, hAB, hcop, hdegree, hfactor⟩ :=
    exists_ownerwise_primitive_pair_of_fullTwoLane_kernel
      sigma alpha beta E hrows hbeta hE hnull hwindow hmass
  have hdegree' : max A.natDegree B.natDegree ≤ h := by
    change max A.natDegree B.natDegree ≤
      (s - keyFirstLaneRows6401) -
        Module.finrank F (LinearMap.ker M.mulVecLin) at hdegree
    rw [hfin] at hdegree
    dsimp [delta] at hdegree
    rw [hrhoEq] at hdegree
    omega
  refine ⟨hfin, hsum, hbalanced, A, B, hAB, hcop, hdegree', ?_⟩
  intro v
  exact hfactor v
theorem smallExcess_forces_kernel_finrank_ge_5628_6401
    (h delta : Nat) (hsum : 11255 ≤ h + delta) (hh : h ≤ 5627) :
    5628 ≤ delta := by
  omega
end BCHKSFrobeniusHighSupportMaxRank6401
end ProximityPrize.SubmissionLower
