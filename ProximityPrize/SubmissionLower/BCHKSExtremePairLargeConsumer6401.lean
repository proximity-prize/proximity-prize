import ProximityPrize.SubmissionLower.BCHKSExtremePairLedger6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremeThreeRectangleProducer6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusRankTwoLedger6401
open BCHKSTwoFrobeniusPrimitiveFrame6401
open BCHKSTwoFrobeniusTripleLight6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000
theorem primitiveExtremePair_owner_card_lt_weakSeed_of_largeIdentity6401
    {F : Type} [Field F] [DecidableEq F]
    {D N : XOverZ F} (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F) (s t : Fin 3) (hst : s ≠ t)
    (R : PrimitiveRationalFrame D N alpha Finset.univ)
    (S : Finset F) (P : F → Polynomial F)
    (hDswap : (Polynomial.Bivariate.swap D).natDegree ≤
      extremePairDenominatorCap6401 s t)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hbranch : ∀ z ∈ S,
      specializeCoeffZ z R.denominator * P z =
        -specializeCoeffZ z R.numerator)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P)
    (hlarge : extremePairIdentityCutoff6401 s t <
      (rationalIdentityCoordinates R.denominator R.numerator
        alpha u0 u1 Finset.univ).card) :
    S.card < weakCurveSeedInput6401 := by
  classical
  by_contra hnotLarge
  have hSlarge : weakCurveSeedInput6401 ≤ S.card := by omega
  let B := rationalIdentityCoordinates R.denominator R.numerator
    alpha u0 u1 Finset.univ
  change extremePairIdentityCutoff6401 s t < B.card at hlarge
  have hBlarge : extremePairIdentityCutoff6401 s t + 1 ≤ B.card := by
    omega
  have hledger := extremePairLedgers_exact6401 s t hst
  have hactive : ∀ i ∈ B,
      evalOuterAt (alpha i) R.denominator ≠ 0 := by
    intro i hi hdenzero
    have hmismatchZero :
        rationalCoordinateMismatch R.denominator R.numerator
          (alpha i) (u0 i) (u1 i) = 0 := by
      simpa [B, rationalIdentityCoordinates] using hi
    unfold rationalCoordinateMismatch at hmismatchZero
    rw [hdenzero, zero_mul, zero_add] at hmismatchZero
    exact R.primitive_at_coordinates i (Finset.mem_univ i)
      ⟨hdenzero, hmismatchZero⟩
  let L := lightChallenges R.denominator alpha B S
    (extremePairLightThreshold6401 s t)
  let H := heavyChallenges R.denominator alpha B S
    (extremePairLightThreshold6401 s t)
  have hHcap : H.card ≤
      (n6401 * extremePairDenominatorCap6401 s t) /
        (extremePairLightThreshold6401 s t + 1) := by
    apply heavyChallenges_card_le (F := F) (ι := Fin n6401)
      R.denominator alpha B S
      (extremePairLightThreshold6401 s t) n6401
        (extremePairDenominatorCap6401 s t)
    · simp
    · exact hactive
    · intro i hi
      exact R.evalOuterAt_denominator_natDegree_le
        (alpha i) (extremePairDenominatorCap6401 s t) hDswap
  have hLcap : L.card ≤ 1182 := by
    by_cases hLsmall : L.card ≤ 1
    · omega
    · have hLtwo : 1 < L.card := by omega
      obtain ⟨p0, p1, hp0, hp1, halign⟩ :=
        exists_affine_family_on_lightChallenges (F := F) (ι := Fin n6401)
          R.denominator R.numerator alpha u0 u1 Finset.univ S P
            ownerDegreeCap6401 (extremePairLightThreshold6401 s t)
            (by
              change ownerDegreeCap6401 +
                  3 * extremePairLightThreshold6401 s t < B.card
              exact hledger.2.1.trans_le hBlarge)
            (by simpa [L] using hLtwo) hPdegree hbranch
      apply affineFamily_card_le_1182_of_no_curveWitness6401 (F := F)
        S L P p0 p1 hfail hp0 hp1
      · intro z hz
        exact (Finset.mem_filter.mp hz).1
      · simpa [L] using halign
  have hpartition : L ∪ H = S := by
    simpa [L, H] using light_union_heavy R.denominator alpha B S
      (extremePairLightThreshold6401 s t)
  have hdisjoint : Disjoint L H := by
    simpa [L, H] using light_disjoint_heavy R.denominator alpha B S
      (extremePairLightThreshold6401 s t)
  have hfamily : S.card ≤ extremePairLargeOwnerCap6401 s t := by
    rw [← hpartition, Finset.card_union_of_disjoint hdisjoint,
      extremePairLargeOwnerCap6401]
    omega
  exact (Nat.not_lt_of_ge hSlarge) (hfamily.trans_lt hledger.2.2.2)
end BCHKSExtremeThreeRectangleProducer6401
end ProximityPrize.SubmissionLower
