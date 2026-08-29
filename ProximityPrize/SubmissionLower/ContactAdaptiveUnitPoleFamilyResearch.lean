import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactWeakPrimeFlagBudgetResearch
import ProximityPrize.SubmissionLower.ContactAdaptiveProjectionCoordinateResearch

/-! .






 -/

namespace ProximityPrize.SubmissionLower.ContactAdaptiveUnitPoleFamilyResearch

open scoped Classical BigOperators WithZero
open ActualCurveCoordinateField
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactFlagBezout6543Research
open ContactWeakSeparableSeparatorResearch
open ContactWeakPrimeFlagBudgetResearch
open ContactPrimeFlagBudgetFamilyResearch
open ContactSparsePoleSupportResearch
open ContactAdaptiveProjectionCoordinateResearch

noncomputable section

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}

/-- .

 -/
structure AdaptiveUnitProjectionFamily
    (base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) where
  zProjection : ∀ C : RegularComponent Omega G T H,
    Coordinate Omega (CoordinateField Omega C.1)
  yzProjection : ∀ C : RegularComponent Omega G T H,
    Coordinate Omega (CoordinateField Omega C.1)
  allProjection : ∀ C : RegularComponent Omega G T H,
    Coordinate Omega (CoordinateField Omega C.1)
  zValue : ∀ C : RegularComponent Omega G T H,
    coordinateValue Omega (CoordinateField Omega C.1) (zProjection C) =
      coordinate Omega C.1 2
  allTranscendental : ∀ C : RegularComponent Omega G T H,
    Transcendental Omega
      (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
  zPole_eq : ∀ (C : RegularComponent Omega G T H)
      (v : Place Omega (CoordinateField Omega C.1)),
    exponentSetPoleWeight v.val (coordinate Omega C.1)
        (flagSupport unitZFlag) =
      CoordinatePoleMass.poleOrder Omega (CoordinateField Omega C.1) v
        (coordinateValue Omega (CoordinateField Omega C.1) (zProjection C))
  yzPole_eq : ∀ (C : RegularComponent Omega G T H)
      (v : Place Omega (CoordinateField Omega C.1)),
    exponentSetPoleWeight v.val (coordinate Omega C.1)
        (flagSupport unitYZFlag) =
      CoordinatePoleMass.poleOrder Omega (CoordinateField Omega C.1) v
        (coordinateValue Omega (CoordinateField Omega C.1) (yzProjection C))
  allPole_eq : ∀ (C : RegularComponent Omega G T H)
      (v : Place Omega (CoordinateField Omega C.1)),
    exponentSetPoleWeight v.val (coordinate Omega C.1)
        (flagSupport unitAllFlag) =
      CoordinatePoleMass.poleOrder Omega (CoordinateField Omega C.1) v
        (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
  sum_zDegree_le :
    (∑ C : RegularComponent Omega G T H,
      coordinateDegree Omega (CoordinateField Omega C.1) (zProjection C)) ≤
      flagMixed p q unitZFlag
  sum_yzDegree_le :
    (∑ C : RegularComponent Omega G T H,
      coordinateDegree Omega (CoordinateField Omega C.1) (yzProjection C)) ≤
      flagMixed p q unitYZFlag
  sum_allDegree_le :
    (∑ C : RegularComponent Omega G T H,
      coordinateDegree Omega (CoordinateField Omega C.1) (allProjection C)) ≤
      flagMixed p q unitAllFlag

/-- .
 -/
def AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget
    {base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1}
    {p q : FlagDegree} (P : AdaptiveUnitProjectionFamily base p q) :
    AdaptiveUnitPoleBudget base p q where
  zCost := fun C => coordinateDegree Omega (CoordinateField Omega C.1)
    (P.zProjection C)
  yzCost := fun C => coordinateDegree Omega (CoordinateField Omega C.1)
    (P.yzProjection C)
  allCost := fun C => coordinateDegree Omega (CoordinateField Omega C.1)
    (P.allProjection C)
  sum_zCost_le := P.sum_zDegree_le
  sum_yzCost_le := P.sum_yzDegree_le
  sum_allCost_le := P.sum_allDegree_le
  zPole := by
    intro C
    unfold LiteralSupportPoleBound
    dsimp only
    intro W
    calc
      (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
          (flagSupport unitZFlag)) =
          ∑ v ∈ W, CoordinatePoleMass.poleOrder Omega
            (CoordinateField Omega C.1) v
            (coordinateValue Omega (CoordinateField Omega C.1)
              (P.zProjection C)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact P.zPole_eq C v
      _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
          (P.zProjection C) : ℤ) :=
        finite_sum_coordinate_pole_le_degree Omega
          (CoordinateField Omega C.1) (P.zProjection C) W
  yzPole := by
    intro C
    unfold LiteralSupportPoleBound
    dsimp only
    intro W
    calc
      (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
          (flagSupport unitYZFlag)) =
          ∑ v ∈ W, CoordinatePoleMass.poleOrder Omega
            (CoordinateField Omega C.1) v
            (coordinateValue Omega (CoordinateField Omega C.1)
              (P.yzProjection C)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact P.yzPole_eq C v
      _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
          (P.yzProjection C) : ℤ) :=
        finite_sum_coordinate_pole_le_degree Omega
          (CoordinateField Omega C.1) (P.yzProjection C) W
  allPole := by
    intro C
    unfold LiteralSupportPoleBound
    dsimp only
    intro W
    calc
      (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
          (flagSupport unitAllFlag)) =
          ∑ v ∈ W, CoordinatePoleMass.poleOrder Omega
            (CoordinateField Omega C.1) v
            (coordinateValue Omega (CoordinateField Omega C.1)
              (P.allProjection C)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact P.allPole_eq C v
      _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
          (P.allProjection C) : ℤ) :=
        finite_sum_coordinate_pole_le_degree Omega
          (CoordinateField Omega C.1) (P.allProjection C) W

/-- .

 -/
def AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily
    {base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1}
    {p q : FlagDegree} (P : AdaptiveUnitProjectionFamily base p q) :
    PrimeFlagBudgetFamily (G := G) (T := T) (H := H) p q :=
  P.toAdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily

/-- .
 -/
theorem AdaptiveUnitProjectionFamily.one_le_zDegree_of_transcendental
    {base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1}
    {p q : FlagDegree} (P : AdaptiveUnitProjectionFamily base p q)
    (C : RegularComponent Omega G T H)
    (hZ : Transcendental Omega (coordinate Omega C.1 2)) :
    1 ≤ coordinateDegree Omega (CoordinateField Omega C.1)
      (P.zProjection C) := by
  apply one_le_coordinateDegree_of_transcendental_value
  rwa [P.zValue C]

/-- .

 -/
theorem AdaptiveUnitProjectionFamily.one_le_toPrimeFlagBudgetFamily_zCost
    {base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1}
    {p q : FlagDegree} (P : AdaptiveUnitProjectionFamily base p q)
    (C : RegularComponent Omega G T H)
    (hZ : Transcendental Omega (coordinate Omega C.1 2)) :
    1 ≤ P.toPrimeFlagBudgetFamily.zCost C :=
  P.one_le_zDegree_of_transcendental C hZ

/-- .
 -/
theorem AdaptiveUnitProjectionFamily.one_le_allDegree
    {base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1}
    {p q : FlagDegree} (P : AdaptiveUnitProjectionFamily base p q)
    (C : RegularComponent Omega G T H) :
    1 ≤ coordinateDegree Omega (CoordinateField Omega C.1)
      (P.allProjection C) :=
  one_le_coordinateDegree_of_transcendental_value
    (P.allProjection C) (P.allTranscendental C)

/-- . -/
theorem AdaptiveUnitProjectionFamily.one_le_toPrimeFlagBudgetFamily_allCost
    {base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1}
    {p q : FlagDegree} (P : AdaptiveUnitProjectionFamily base p q)
    (C : RegularComponent Omega G T H) :
    1 ≤ P.toPrimeFlagBudgetFamily.allCost C :=
  P.one_le_allDegree C

end


end ProximityPrize.SubmissionLower.ContactAdaptiveUnitPoleFamilyResearch
