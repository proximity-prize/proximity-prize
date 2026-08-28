import ProximityPrize.SubmissionLower.BCHKSLocatorGenericRankDrop6400
import ProximityPrize.SubmissionLower.BCHKSBoundedPairMultipleMap6400
import ProximityPrize.SubmissionLower.BCHKSEffectiveFixedScaledRelation6400
import ProximityPrize.SubmissionLower.BCHKSRankOneEffectiveDefectProduction6400

/-!
# Effective-locator multiples force local nullity

At a retained owner, multiply the primitive homogeneous relation by the
effective fixed-node locator.  Every further polynomial multiplier that fits
inside the two locator degree caps is a genuine specialized locator-kernel
vector.  When the specialized Frobenius lane is nonzero, these vectors are
independent and give a sharp lower bound on local nullity.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSEffectiveLocatorLocalNullity6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSEffectiveFixedRelation6400
open BCHKSRankOneEffectiveDefectProduction6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Specializing away from a root of the outer leading coefficient preserves
the outer degree exactly. -/
theorem natDegree_map_eval_eq_of_leadingCoeff_eval_ne_zero
    {F : Type} [Field F] (Q : F[X][X]) (z : F)
    (hlead : Q.leadingCoeff.eval z ≠ 0) :
    (Q.map (Polynomial.evalRingHom z)).natDegree = Q.natDegree := by
  apply le_antisymm Polynomial.natDegree_map_le
  apply Polynomial.le_natDegree_of_ne_zero
  rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
  change Q.leadingCoeff.eval z ≠ 0
  exact hlead

/-- The effective degree room injects into the specialized production
locator kernel at every owner where the primitive Frobenius lane keeps its
generic outer degree. -/
theorem Score6400RankOneEffectiveDefectData.effectiveRoom_le_localNullity
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (z : IRSProfile.Field) (hz : z ∈ T)
    (Agreement : Finset IRSProfile.Index) (P : IRSProfile.Field[X])
    (hAgreement : 185364 ≤ Agreement.card)
    (hPdegree : P.natDegree ≤ 131071)
    (hagree : ∀ i ∈ Agreement,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i)
    (hBleading : data.B.leadingCoeff.eval z ≠ 0)
    (hroomPositive : 0 < locatorFrobeniusRows6400 -
      (score6400EffectiveFixedDefect data.Fixed data.K).card -
        data.B.natDegree) :
    locatorFrobeniusRows6400 -
        (score6400EffectiveFixedDefect data.Fixed data.K).card -
          data.B.natDegree ≤
      Module.finrank IRSProfile.Field
        (LinearMap.ker
          (twoBlockSpecialization
            (score6400LocatorStackPart f₀)
            (score6400LocatorStackPart f₁)
            z (z ^ 2130706433)).mulVecLin) := by
  let FixedEff := score6400EffectiveFixedDefect data.Fixed data.K
  let LF := score6400EffectiveFixedLocator data.Fixed data.K
  let Az := data.A.map (Polynomial.evalRingHom z)
  let Bz := data.B.map (Polynomial.evalRingHom z)
  let U := LF * Az
  let V := LF * Bz
  let room := locatorFrobeniusRows6400 - FixedEff.card -
    data.B.natDegree
  have hLFne : LF ≠ 0 := by
    simpa only [LF] using
      score6400EffectiveFixedLocator_ne_zero data.Fixed data.K
  have hLFdegree : LF.natDegree = FixedEff.card := by
    simpa only [LF, FixedEff] using
      score6400EffectiveFixedLocator_natDegree data.Fixed data.K
  have hBzne : Bz ≠ 0 := by
    have hcoeff : Bz.coeff data.B.natDegree ≠ 0 := by
      dsimp only [Bz]
      rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
      change data.B.leadingCoeff.eval z ≠ 0
      exact hBleading
    intro hzero
    apply hcoeff
    rw [hzero, Polynomial.coeff_zero]
  have hBzdegree : Bz.natDegree = data.B.natDegree := by
    simpa only [Bz] using
      natDegree_map_eval_eq_of_leadingCoeff_eval_ne_zero data.B z hBleading
  have hAzdegree : Az.natDegree ≤ data.A.natDegree := by
    exact Polynomial.natDegree_map_le
  have hVne : V ≠ 0 := mul_ne_zero hLFne hBzne
  have hVdegree : V.natDegree = FixedEff.card + data.B.natDegree := by
    dsimp only [V]
    rw [Polynomial.natDegree_mul hLFne hBzne, hLFdegree, hBzdegree]
  have hUdegree : U.natDegree ≤ FixedEff.card + data.B.natDegree := by
    calc
      U.natDegree ≤ LF.natDegree + Az.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ FixedEff.card + data.A.natDegree := by
        rw [hLFdegree]
        exact Nat.add_le_add_left hAzdegree _
      _ ≤ FixedEff.card + data.B.natDegree :=
        Nat.add_le_add_left hAdirection _
  have hrebate : FixedEff.card + data.B.natDegree ≤
      locatorFrobeniusRows6400 - L := by
    simpa only [FixedEff, score6400EffectiveFixedDefect] using
      data.effective_rebate
  have hVroom : room + V.natDegree ≤ locatorFrobeniusRows6400 := by
    rw [hVdegree]
    dsimp only [room]
    omega
  have hUroom : room + U.natDegree ≤ locatorOrdinaryRows6400 := by
    have hcap : locatorFrobeniusRows6400 ≤ locatorOrdinaryRows6400 := by
      norm_num [locatorFrobeniusRows6400, locatorOrdinaryRows6400]
    dsimp only [room]
    omega
  have hroom : 0 < room := by
    simpa only [room, FixedEff] using hroomPositive
  have howner :=
    (data.owners z hz Agreement P hAgreement hPdegree hagree).1
  have houtside : ∀ i,
      i ∉ score6400EffectiveFixedDefect data.Fixed data.K →
      (data.A.map (Polynomial.evalRingHom z)).eval
              (IRSProfile.domain i) *
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
          (data.B.map (Polynomial.evalRingHom z)).eval
              (IRSProfile.domain i) *
            (koalaSexticFrobenius (f₀ i + z * f₁ i) -
              (P.map koalaSexticFrobenius.toRingHom).eval
                (IRSProfile.domain i)) = 0 := by
    intro i hi
    exact score6400_homogeneous_error_relation_outside_effective
      f₀ f₁ data.q data.H data.A data.B data.C data.K data.Fixed
      data.A_factor data.B_factor data.C_factor data.Fixed_eq data.global
      z P howner i hi
  have hscaled := score6400_effectiveLocator_scaled_relation_everywhere
    f₀ f₁ data.Fixed data.K data.A data.B z P houtside
  have hUshape :
      (score6400EffectiveFixedLocatorLift data.Fixed data.K * data.A).map
          (Polynomial.evalRingHom z) = U := by
    rw [Polynomial.map_mul,
      score6400EffectiveFixedLocatorLift_map_eval]
  have hVshape :
      (score6400EffectiveFixedLocatorLift data.Fixed data.K * data.B).map
          (Polynomial.evalRingHom z) = V := by
    rw [Polynomial.map_mul,
      score6400EffectiveFixedLocatorLift_map_eval]
  have hbaseRelation : ∀ i,
      U.eval (IRSProfile.domain i) *
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
        V.eval (IRSProfile.domain i) *
          koalaSexticFrobenius
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) = 0 := by
    intro i
    have hi := hscaled i
    rw [hUshape, hVshape] at hi
    have herrorMap :
        koalaSexticFrobenius
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) =
          koalaSexticFrobenius (f₀ i + z * f₁ i) -
            (P.map koalaSexticFrobenius.toRingHom).eval
              (IRSProfile.domain i) := by
      rw [map_sub,
        polynomial_map_eval_of_fixed_locator koalaSexticFrobenius P
          (IRSProfile.domain i) (koalaSexticFrobenius_fixed_domain i)]
    rw [herrorMap]
    exact hi
  have hker : ∀ M : Polynomial.degreeLT IRSProfile.Field room,
      boundedPairMultipleCoordinateMap
          locatorOrdinaryRows6400 locatorFrobeniusRows6400 room hroom
          U V hUroom hVroom M ∈
        LinearMap.ker
          (twoBlockSpecialization
            (score6400LocatorStackPart f₀)
            (score6400LocatorStackPart f₁)
            z (z ^ 2130706433)).mulVecLin := by
    intro M
    have hpoint : ∀ i,
        (boundedPairMultipleMap
              locatorOrdinaryRows6400 locatorFrobeniusRows6400 room hroom
              U V hUroom hVroom M).1.1.eval (IRSProfile.domain i) *
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
          (boundedPairMultipleMap
              locatorOrdinaryRows6400 locatorFrobeniusRows6400 room hroom
              U V hUroom hVroom M).2.1.eval (IRSProfile.domain i) *
            koalaSexticFrobenius
              ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) = 0 := by
      intro i
      have hi := hbaseRelation i
      simp only [boundedPairMultipleMap_fst, boundedPairMultipleMap_snd,
        Polynomial.eval_mul]
      calc
        (M.1.eval (IRSProfile.domain i) * U.eval (IRSProfile.domain i)) *
                ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
            (M.1.eval (IRSProfile.domain i) * V.eval
                (IRSProfile.domain i)) *
              koalaSexticFrobenius
                ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) =
            M.1.eval (IRSProfile.domain i) *
              (U.eval (IRSProfile.domain i) *
                    ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
                V.eval (IRSProfile.domain i) *
                  koalaSexticFrobenius
                    ((f₀ i + z * f₁ i) - P.eval
                      (IRSProfile.domain i))) := by ring
        _ = 0 := by rw [hi, mul_zero]
    have hmem := score6400_mem_locatorKernel_of_pointwise_error_relation
      f₀ f₁ z
      (boundedPairMultipleMap
        locatorOrdinaryRows6400 locatorFrobeniusRows6400 room hroom
        U V hUroom hVroom M)
      P hPdegree hpoint
    simpa only [boundedPairMultipleCoordinateMap,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using hmem
  exact room_le_finrank_ker_of_boundedPairMultiples
    locatorOrdinaryRows6400 locatorFrobeniusRows6400 room hroom
    U V hUroom hVroom hVne
    (twoBlockSpecialization
      (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
      z (z ^ 2130706433)).mulVecLin hker

end BCHKSEffectiveLocatorLocalNullity6400
end ProximityPrize.SubmissionLower
