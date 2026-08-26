import ProximityPrize.SubmissionLower.BCHKSExtremePairSmallConsumer6401
import ProximityPrize.SubmissionLower.BCHKSExtremePairLargeConsumer6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremeThreeRectangleProducer6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusPrimitiveFrame6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
theorem primitiveExtremePair_owner_card_lt_weakSeed6401
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
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hbranch : ∀ z ∈ S,
      specializeCoeffZ z R.denominator * P z =
        -specializeCoeffZ z R.numerator)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    S.card < weakCurveSeedInput6401 := by
  classical
  by_cases hsmall :
      (rationalIdentityCoordinates R.denominator R.numerator
        alpha u0 u1 Finset.univ).card ≤
          extremePairIdentityCutoff6401 s t
  · exact primitiveExtremePair_owner_card_lt_weakSeed_of_smallIdentity6401
      alpha u0 u1 s t hst R S A P hDswap hNswap hrow hbranch howner hsmall
  · exact primitiveExtremePair_owner_card_lt_weakSeed_of_largeIdentity6401
      alpha u0 u1 s t hst R S P hDswap hPdegree hbranch hfail
        (Nat.lt_of_not_ge hsmall)
end BCHKSExtremeThreeRectangleProducer6401
end ProximityPrize.SubmissionLower
