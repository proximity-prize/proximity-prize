import ProximityPrize.SubmissionLower.BCHKSExtremePairLedger6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremeThreeRectangleProducer6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusRankTwoLedger6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusPrimitiveFrame6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000
theorem primitiveExtremePair_owner_card_lt_weakSeed_of_smallIdentity6401
    {F : Type} [Field F] [DecidableEq F]
    {D N : XOverZ F} (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F) (s t : Fin 3) (hst : s ≠ t)
    (R : PrimitiveRationalFrame D N alpha Finset.univ)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hDswap : (Polynomial.Bivariate.swap D).natDegree ≤
      extremePairDenominatorCap6401 s t)
    (hNswap : (Polynomial.Bivariate.swap N).natDegree ≤
      extremePairMismatchCap6401 s t)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hbranch : ∀ z ∈ S,
      specializeCoeffZ z R.denominator * P z =
        -specializeCoeffZ z R.numerator)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hsmall : (rationalIdentityCoordinates R.denominator R.numerator
      alpha u0 u1 Finset.univ).card ≤
        extremePairIdentityCutoff6401 s t) :
    S.card < weakCurveSeedInput6401 := by
  classical
  by_contra hnotLarge
  have hSlarge : weakCurveSeedInput6401 ≤ S.card := by omega
  have hmismatch : ∀ i : Fin n6401,
      (rationalCoordinateMismatch R.denominator R.numerator
        (alpha i) (u0 i) (u1 i)).natDegree ≤
          extremePairMismatchCap6401 s t := by
    intro i
    have h := R.rationalCoordinateMismatch_natDegree_le
      (alpha i) (u0 i) (u1 i)
        (extremePairDenominatorCap6401 s t)
        (extremePairMismatchCap6401 s t) hDswap hNswap
    simpa [extremePairMismatchCap6401] using h
  let B := rationalIdentityCoordinates R.denominator R.numerator
    alpha u0 u1 Finset.univ
  change B.card ≤ extremePairIdentityCutoff6401 s t at hsmall
  have hledger := extremePairLedgers_exact6401 s t hst
  have hinc : S.card * (a6401 - B.card) ≤
      n6401 * extremePairMismatchCap6401 s t := by
    simpa only [Fintype.card_fin] using
      (rational_owner_card_mul_agreement_sub_identity_le
        (F := F) (ι := Fin n6401)
        R.denominator R.numerator alpha u0 u1 S A P a6401
          (extremePairMismatchCap6401 s t) hrow hbranch howner hmismatch)
  have hgap :
      a6401 - extremePairIdentityCutoff6401 s t ≤
        a6401 - B.card := Nat.sub_le_sub_left hsmall a6401
  have hcontra :
      weakCurveSeedInput6401 *
          (a6401 - extremePairIdentityCutoff6401 s t) ≤
        n6401 * extremePairMismatchCap6401 s t := by
    calc
      weakCurveSeedInput6401 *
          (a6401 - extremePairIdentityCutoff6401 s t) ≤
          S.card *
            (a6401 - extremePairIdentityCutoff6401 s t) :=
        Nat.mul_le_mul_right _ hSlarge
      _ ≤ S.card * (a6401 - B.card) :=
        Nat.mul_le_mul_left _ hgap
      _ ≤ n6401 * extremePairMismatchCap6401 s t := hinc
  exact (Nat.not_lt_of_ge hcontra) hledger.1
end BCHKSExtremeThreeRectangleProducer6401
end ProximityPrize.SubmissionLower
