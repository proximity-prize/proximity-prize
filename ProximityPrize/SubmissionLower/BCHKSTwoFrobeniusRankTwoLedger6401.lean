import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRankTwoIdentityFork6401
import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRankTwoDegreeCaps6401
import ProximityPrize.SubmissionLower.BCHKSDoubleCounting
import ProximityPrize.SubmissionLower.BCHKSFinalConditional6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusRankTwoLedger6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoIdentityFork6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusSymbolicKernel6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
noncomputable def chargedAgreements
    {F ι : Type*} [Field F] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (I : Finset ι) (A : F → Finset ι) (z : F) : Finset ι := by
  classical
  exact A z \ identityCoordinates q r alpha u₀ u₁ I
theorem owner_card_mul_agreement_sub_identity_le
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (S : Finset F) (A : F → Finset ι) (a mismatchCap : ℕ)
    (hrow : ∀ z ∈ S, a ≤ (A z).card)
    (hroot : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval z
        (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)) = 0)
    (hdegree : ∀ i : ι,
      (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)).natDegree ≤
        mismatchCap) :
    S.card *
        (a - (identityCoordinates q r alpha u₀ u₁ Finset.univ).card) ≤
      Fintype.card ι * mismatchCap := by
  classical
  let H : Finset ι :=
    identityCoordinates q r alpha u₀ u₁ Finset.univ
  let E : F → Finset ι := fun z => A z \ H
  let fib : ι → ℕ := fun i => (S.filter fun z => i ∈ E z).card
  have hrow' : ∀ z ∈ S, a - H.card ≤ (E z).card := by
    intro z hz
    have hdiff := Finset.le_card_sdiff H (A z)
    dsimp [E]
    exact (Nat.sub_le_sub_right (hrow z hz) H.card).trans hdiff
  have hlower : S.card * (a - H.card) ≤
      ∑ z ∈ S, (E z).card := by
    calc
      S.card * (a - H.card) = ∑ _z ∈ S, (a - H.card) := by
        simp
      _ ≤ ∑ z ∈ S, (E z).card := Finset.sum_le_sum hrow'
  have hswap : (∑ z ∈ S, (E z).card) = ∑ i : ι, fib i := by
    exact sum_card_eq_sum_fiber_card S E
  have hfib : ∀ i : ι, fib i ≤ mismatchCap := by
    intro i
    by_cases hi : i ∈ H
    · have hempty : S.filter (fun z => i ∈ E z) = ∅ := by
        ext z
        simp [E, hi]
      simp [fib, hempty]
    · have hsub : S.filter (fun z => i ∈ E z) ⊆
          S.filter fun z => Polynomial.eval z
            (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)) = 0 := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        refine ⟨hz.1, ?_⟩
        exact hroot z hz.1 i (Finset.mem_sdiff.mp hz.2).1
      calc
        fib i ≤ (S.filter fun z => Polynomial.eval z
              (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)) = 0).card :=
          Finset.card_le_card hsub
        _ ≤ (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)).natDegree := by
          apply nonidentity_coordinate_challenge_card_le
            q r alpha u₀ u₁ Finset.univ S i
          · simp
          · simpa [H] using hi
        _ ≤ mismatchCap := hdegree i
  calc
    S.card *
        (a - (identityCoordinates q r alpha u₀ u₁ Finset.univ).card) =
        S.card * (a - H.card) := by rfl
    _ ≤ ∑ z ∈ S, (E z).card := hlower
    _ = ∑ i : ι, fib i := hswap
    _ ≤ ∑ _i : ι, mismatchCap := Finset.sum_le_sum fun i _ => hfib i
    _ = Fintype.card ι * mismatchCap := by simp
theorem owner_card_mul_agreement_sub_identity_le_of_relations
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F)
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (S : Finset F) (A : F → Finset ι) (P : F → Polynomial F)
    (a mismatchCap : ℕ)
    (hrow : ∀ z ∈ S, a ≤ (A z).card)
    (hq : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z q) (P z) = 0)
    (hr : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z r) (P z) = 0)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hdegree : ∀ i : ι,
      (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)).natDegree ≤
        mismatchCap) :
    S.card *
        (a - (identityCoordinates q r alpha u₀ u₁ Finset.univ).card) ≤
      Fintype.card ι * mismatchCap := by
  apply owner_card_mul_agreement_sub_identity_le
    q r alpha u₀ u₁ S A a mismatchCap hrow
  · intro z hz i hi
    exact coordinateMismatch_eval_eq_zero_of_owner sigma z q r
      (alpha i) (u₀ i) (u₁ i) (P z)
      (hq z hz) (hr z hz) (howner z hz i hi)
  · exact hdegree
def rankTwoIdentityIncidenceCutoff6401 : ℕ := 185294
def rankTwoIncidenceOwnerCap6401 : ℕ :=
  (n6401 * rankTwoMismatchZCap6401) / 60
def RankTwoLargeIdentityResidual6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F) : Prop :=
  185295 ≤
    (identityCoordinates q r alpha u₀ u₁ Finset.univ).card
theorem rankTwo_identity_incidence_ledger_exact6401 :
    rankTwoIdentityIncidenceCutoff6401 = 185294 ∧
      a6401 - rankTwoIdentityIncidenceCutoff6401 = 60 ∧
      rankTwoIncidenceOwnerCap6401 = 271149023464080452 ∧
      rankTwoIncidenceOwnerCap6401 <
        BCHKSFinalConditional6401.mcaNumerator6401 ∧
      BCHKSFinalConditional6401.mcaNumerator6401 -
          rankTwoIncidenceOwnerCap6401 = 3831704630268791 ∧
      (n6401 * rankTwoMismatchZCap6401) / 59 =
        275744769624488595 ∧
      BCHKSFinalConditional6401.mcaNumerator6401 <
        (n6401 * rankTwoMismatchZCap6401) / 59 ∧
      (n6401 * rankTwoMismatchZCap6401) / 59 -
          BCHKSFinalConditional6401.mcaNumerator6401 = 764041530139352 := by
  norm_num [rankTwoIdentityIncidenceCutoff6401,
    rankTwoIncidenceOwnerCap6401, n6401, rankTwoMismatchZCap6401,
    balancedDepth6401, balancedThreshold6401, moduleIndexSum6401,
    a1XSlots6401, q6401, a6401,
    BCHKSFinalConditional6401.mcaNumerator6401,
    BCHKSList6401.maxMCANumeratorAfterList6401,
    BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
    BCHKSList6401.listBound6401]
theorem owner_card_le_rankTwoIncidenceOwnerCap6401
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F)
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (S : Finset F) (A : F → Finset ι) (P : F → Polynomial F)
    (hcardι : Fintype.card ι = n6401)
    (hidentity :
      (identityCoordinates q r alpha u₀ u₁ Finset.univ).card ≤
        rankTwoIdentityIncidenceCutoff6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hq : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z q) (P z) = 0)
    (hr : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z r) (P z) = 0)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hdegree : ∀ i : ι,
      (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)).natDegree ≤
        rankTwoMismatchZCap6401) :
    S.card ≤ rankTwoIncidenceOwnerCap6401 := by
  have hinc := owner_card_mul_agreement_sub_identity_le_of_relations
    sigma q r alpha u₀ u₁ S A P a6401 rankTwoMismatchZCap6401
    hrow hq hr howner hdegree
  have hgap : 60 ≤
      a6401 -
        (identityCoordinates q r alpha u₀ u₁ Finset.univ).card := by
    norm_num [a6401, rankTwoIdentityIncidenceCutoff6401] at hidentity ⊢
    omega
  rw [hcardι] at hinc
  rw [rankTwoIncidenceOwnerCap6401, Nat.le_div_iff_mul_le (by norm_num : 0 < 60)]
  calc
    S.card * 60 ≤ S.card *
        (a6401 -
          (identityCoordinates q r alpha u₀ u₁ Finset.univ).card) :=
      Nat.mul_le_mul_left S.card hgap
    _ ≤ n6401 * rankTwoMismatchZCap6401 := hinc
theorem rankTwo_owner_cap_or_largeIdentityResidual6401
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F)
    (q r : SymbolicRow F) (alpha u₀ u₁ : ι → F)
    (S : Finset F) (A : F → Finset ι) (P : F → Polynomial F)
    (hcardι : Fintype.card ι = n6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hq : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z q) (P z) = 0)
    (hr : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z r) (P z) = 0)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hdegree : ∀ i : ι,
      (coordinateMismatch q r (alpha i) (u₀ i) (u₁ i)).natDegree ≤
        rankTwoMismatchZCap6401) :
    S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401 ∨
      RankTwoLargeIdentityResidual6401 q r alpha u₀ u₁ := by
  by_cases hsmall :
      (identityCoordinates q r alpha u₀ u₁ Finset.univ).card ≤
        rankTwoIdentityIncidenceCutoff6401
  · left
    exact (owner_card_le_rankTwoIncidenceOwnerCap6401
      sigma q r alpha u₀ u₁ S A P hcardι hsmall hrow hq hr howner
      hdegree).trans (Nat.le_of_lt rankTwo_identity_incidence_ledger_exact6401.2.2.2.1)
  · right
    norm_num [RankTwoLargeIdentityResidual6401,
      rankTwoIdentityIncidenceCutoff6401] at hsmall ⊢
    omega
theorem coefficientRows_owner_cap_or_largeIdentityResidual6401
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F)
    (c d : SymbolicCoefficients F) (alpha u₀ u₁ : ι → F)
    (S : Finset F) (A : F → Finset ι) (P : F → Polynomial F)
    (hcardι : Fintype.card ι = n6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hc : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap c)) (P z) = 0)
    (hd : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap d)) (P z) = 0)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i) :
    S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401 ∨
      RankTwoLargeIdentityResidual6401
        (coefficientRowMap c) (coefficientRowMap d) alpha u₀ u₁ := by
  apply rankTwo_owner_cap_or_largeIdentityResidual6401
    sigma (coefficientRowMap c) (coefficientRowMap d)
      alpha u₀ u₁ S A P hcardι hrow hc hd howner
  intro i
  exact coordinateMismatch_coefficientRowMap_natDegree_le
    c d (alpha i) (u₀ i) (u₁ i)
theorem coefficientRows_owner_cap_or_largeIdentity_structuralFork6401
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F)
    (c d : SymbolicCoefficients F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (S : Finset F) (A : F → Finset ι) (P : F → Polynomial F)
    (hcardι : Fintype.card ι = n6401)
    (hden : symbolicRankTwoDenominator
      (coefficientRowMap c) (coefficientRowMap d) ≠ 0)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hc : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap c)) (P z) = 0)
    (hd : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap d)) (P z) = 0)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i) :
    S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401 ∨
      (RankTwoLargeIdentityResidual6401
          (coefficientRowMap c) (coefficientRowMap d) alpha u₀ u₁ ∧
        ((∃ p₀ p₁ : Polynomial F,
            p₀.natDegree ≤ ownerDegreeCap6401 ∧
            p₁.natDegree ≤ ownerDegreeCap6401 ∧
            ∀ z ∈ activeDenominatorGoodChallenges
              (coefficientRowMap c) (coefficientRowMap d)
                alpha u₀ u₁ Finset.univ S,
              P z = p₀ + Polynomial.C z * p₁) ∨
          ((identityCoordinates (coefficientRowMap c) (coefficientRowMap d)
                alpha u₀ u₁ Finset.univ).card - ownerDegreeCap6401 ≤
              (commonLocatorCoordinates (coefficientRowMap c)
                (coefficientRowMap d) alpha u₀ u₁ Finset.univ).card ∧
            (commonLocatorCoordinates (coefficientRowMap c)
                (coefficientRowMap d) alpha u₀ u₁ Finset.univ).card ≤
              (symbolicRankTwoDenominator
                (coefficientRowMap c) (coefficientRowMap d)).natDegree ∧
            outerLocatorProduct alpha
                (commonLocatorCoordinates (coefficientRowMap c)
                  (coefficientRowMap d) alpha u₀ u₁ Finset.univ) ∣
              symbolicRankTwoDenominator
                (coefficientRowMap c) (coefficientRowMap d) ∧
            outerLocatorProduct alpha
                (commonLocatorCoordinates (coefficientRowMap c)
                  (coefficientRowMap d) alpha u₀ u₁ Finset.univ) ∣
              symbolicRankTwoNumerator
                (coefficientRowMap c) (coefficientRowMap d)))) := by
  rcases coefficientRows_owner_cap_or_largeIdentityResidual6401
      sigma c d alpha u₀ u₁ S A P hcardι hrow hc hd howner with
    hcap | hlarge
  · exact Or.inl hcap
  · right
    refine ⟨hlarge, ?_⟩
    exact ownerFamily_affine_or_commonLocator_gcd sigma
      (coefficientRowMap c) (coefficientRowMap d)
      alpha u₀ u₁ Finset.univ S P ownerDegreeCap6401 hden
      hPdegree hc hd
theorem commonLocator_card_interval_of_largeIdentity6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (c d : SymbolicCoefficients F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (hlarge : RankTwoLargeIdentityResidual6401
      (coefficientRowMap c) (coefficientRowMap d) alpha u₀ u₁)
    (hlower :
      (identityCoordinates (coefficientRowMap c) (coefficientRowMap d)
          alpha u₀ u₁ Finset.univ).card - ownerDegreeCap6401 ≤
        (commonLocatorCoordinates (coefficientRowMap c)
          (coefficientRowMap d) alpha u₀ u₁ Finset.univ).card)
    (hupper :
      (commonLocatorCoordinates (coefficientRowMap c)
          (coefficientRowMap d) alpha u₀ u₁ Finset.univ).card ≤
        (symbolicRankTwoDenominator
          (coefficientRowMap c) (coefficientRowMap d)).natDegree) :
    54224 ≤
        (commonLocatorCoordinates (coefficientRowMap c)
          (coefficientRowMap d) alpha u₀ u₁ Finset.univ).card ∧
      (commonLocatorCoordinates (coefficientRowMap c)
          (coefficientRowMap d) alpha u₀ u₁ Finset.univ).card ≤
        87382 := by
  constructor
  · unfold RankTwoLargeIdentityResidual6401 at hlarge
    norm_num [ownerDegreeCap6401] at hlower ⊢
    omega
  · exact hupper.trans
      (coefficientRowMap_denominator_outer_natDegree_le c d)
end BCHKSTwoFrobeniusRankTwoLedger6401
end ProximityPrize.SubmissionLower
