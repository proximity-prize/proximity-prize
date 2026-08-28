import ProximityPrize.SubmissionLower.BCHKSCramerMultiplierFamilyData6400
import ProximityPrize.SubmissionLower.BCHKSLocatorAffineMultiplierFixedRoot6400

/-! # Affine compatibility and fixed roots for selected Cramer multipliers -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneCramerMultiplierFamily6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSPrimitiveTripleRelation6400
open BCHKSGlobalInhomogeneousKeyEquation6400
open BCHKSLocatorAffineMultiplierCompatibility6400
open BCHKSMultiplierDefectAbstract6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem score6400_selectedCramer_affine_factor
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (selection : Score6400BoundedCramerFamilyData f₀ f₁ L)
    (q₀ : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (family : Score6400CramerMultiplierFamilyData
      f₀ f₁ L selection A B)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q₀).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q₀).2.1 = H * B)
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q₀ = H * C)
    (hFixed : Fixed = fixedCoordinateDefect H)
    (hFixedCard : Fixed.card ≤ 22488)
    (hCdegree : C.natDegree < 185363)
    (j : SelectedColumnComplement selection.cols) :
    (score6400PolynomialLocatorPairToCode f₀ f₁
        (score6400SelectedLocatorCramerVector f₀ f₁ selection.rows
          selection.cols selection.hcols j)).map
          score6400ChallengeIota =
      family.multipliers j * C.map score6400ChallengeIota := by
  have hfield :
      76779 * 2130706433 + 2130706433 <
        Fintype.card IRSProfile.Field := by
    rw [CompPoly.Extension.Ext.card_ext]
    norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]
  have hMdegree : (family.multipliers j).natDegree < 22489 := by
    have hj := family.degree j
    norm_num [locatorFrobeniusRows6400] at hj ⊢
    omega
  apply score6400_affineLane_map_eq_multiplier
    f₀ f₁ q₀
    (score6400SelectedLocatorCramerVector f₀ f₁ selection.rows
      selection.cols selection.hcols j)
    H A B C Fixed (family.multipliers j)
    hAfactor hBfactor hCfactor hFixed hFixedCard
    (selection.kernel j) (76779 * 2130706433)
    (selection.degree j) hfield
  · simpa only [score6400ChallengeIota,
      score6400SelectedLocatorCramerOrdinary] using family.firstFactor j
  · simpa only [score6400ChallengeIota,
      score6400SelectedLocatorCramerFrobenius] using family.secondFactor j
  · exact hMdegree
  · exact hCdegree

theorem score6400_selectedCramer_multiplier_fixed_root
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (selection : Score6400BoundedCramerFamilyData f₀ f₁ L)
    (q₀ : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C K : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (family : Score6400CramerMultiplierFamilyData
      f₀ f₁ L selection A B)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q₀).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q₀).2.1 = H * B)
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q₀ = H * C)
    (hFixed : Fixed = fixedCoordinateDefect H)
    (hFixedCard : Fixed.card ≤ 22488)
    (hCdegree : C.natDegree < 185363)
    (hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
            (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C)
    (j : SelectedColumnComplement selection.cols)
    (i : IRSProfile.Index) (hi : i ∈ Fixed) :
    (family.multipliers j * K.map score6400ChallengeIota).eval
        (score6400ChallengeFractionDomain i) = 0 := by
  apply score6400_affineMultiplier_globalQuotient_fixed_root
    f₀ f₁
    (score6400SelectedLocatorCramerVector f₀ f₁ selection.rows
      selection.cols selection.hcols j)
    Fixed A B C K (family.multipliers j) hglobal
  · simpa only [score6400ChallengeIota,
      score6400SelectedLocatorCramerOrdinary] using family.firstFactor j
  · simpa only [score6400ChallengeIota,
      score6400SelectedLocatorCramerFrobenius] using family.secondFactor j
  · exact score6400_selectedCramer_affine_factor
      f₀ f₁ L selection q₀ H A B C Fixed family
      hAfactor hBfactor hCfactor hFixed hFixedCard hCdegree j
  · exact hi

/-- Every selected multiplier contains the locator of the effective fixed
defect, namely the fixed nodes where the global quotient is nonzero. -/
theorem score6400_selectedCramer_effectiveLocator_dvd
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (selection : Score6400BoundedCramerFamilyData f₀ f₁ L)
    (q₀ : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C K : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (family : Score6400CramerMultiplierFamilyData
      f₀ f₁ L selection A B)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q₀).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q₀).2.1 = H * B)
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q₀ = H * C)
    (hFixed : Fixed = fixedCoordinateDefect H)
    (hFixedCard : Fixed.card ≤ 22488)
    (hCdegree : C.natDegree < 185363)
    (hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
            (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C)
    (j : SelectedColumnComplement selection.cols) :
    Lagrange.nodal
        (effectiveNodalDefect score6400ChallengeFractionDomain Fixed
          (K.map score6400ChallengeIota))
        (fun i ↦ score6400ChallengeFractionDomain i) ∣
      family.multipliers j := by
  apply score6400_effectiveNodalLocator_dvd_multiplier
    Fixed K (family.multipliers j)
  intro i hi
  exact score6400_selectedCramer_multiplier_fixed_root
    f₀ f₁ L selection q₀ H A B C K Fixed family
    hAfactor hBfactor hCfactor hFixed hFixedCard hCdegree hglobal
    j i hi

/-- Main multiplier-family rebate.  The effective fixed defect and primitive
Frobenius degree share the same `22489-L` budget. -/
theorem score6400_effectiveDefect_add_frobeniusDegree_le_sub_nullity
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (hLtwo : 2 ≤ L)
    (selection : Score6400BoundedCramerFamilyData f₀ f₁ L)
    (q₀ : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C K : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (family : Score6400CramerMultiplierFamilyData
      f₀ f₁ L selection A B)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q₀).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q₀).2.1 = H * B)
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q₀ = H * C)
    (hFixed : Fixed = fixedCoordinateDefect H)
    (hFixedCard : Fixed.card ≤ 22488)
    (hCdegree : C.natDegree < 185363)
    (hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
            (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C) :
    (effectiveNodalDefect score6400ChallengeFractionDomain Fixed
        (K.map score6400ChallengeIota)).card + B.natDegree ≤
      locatorFrobeniusRows6400 - L := by
  let R : Score6400ChallengeFraction[X] :=
    Lagrange.nodal
      (effectiveNodalDefect score6400ChallengeFractionDomain Fixed
        (K.map score6400ChallengeIota))
      (fun i ↦ score6400ChallengeFractionDomain i)
  have hJcard :
      Fintype.card (SelectedColumnComplement selection.cols) = L := by
    rw [← Nat.card_eq_fintype_card]
    exact selection.card_eq
  letI : Nonempty (SelectedColumnComplement selection.cols) :=
    Fintype.card_pos_iff.mp (by rw [hJcard]; omega)
  have hR : R ≠ 0 := by
    exact Lagrange.nodal_ne_zero
  have hdiv : ∀ j, R ∣ family.multipliers j := by
    intro j
    exact score6400_selectedCramer_effectiveLocator_dvd
      f₀ f₁ L selection q₀ H A B C K Fixed family
      hAfactor hBfactor hCfactor hFixed hFixedCard hCdegree hglobal j
  have hdimension := card_add_natDegree_le_of_linearIndependent_dvd
    family.multipliers R
    (locatorFrobeniusRows6400 - B.natDegree)
    family.linearIndependent hR family.degree hdiv
  have hRdegree : R.natDegree =
      (effectiveNodalDefect score6400ChallengeFractionDomain Fixed
        (K.map score6400ChallengeIota)).card := by
    exact Lagrange.natDegree_nodal
  rw [hJcard, hRdegree] at hdimension
  omega

end BCHKSRankOneCramerMultiplierFamily6400
end ProximityPrize.SubmissionLower
