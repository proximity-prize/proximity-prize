import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingCurveBudget6719Research
import ProximityPrize.SubmissionLower.ContactMovingProjectionFamily6719Research
namespace ProximityPrize.SubmissionLower.ContactMovingCurveFamily6719Research
open scoped Classical BigOperators WithZero
open ActualCurveCoordinateField ContactRegularComponentCover CoordinateBoxZeroCount
open ContactWeakSeparableSeparatorResearch ContactAdaptiveUnitPoleFamilyResearch
open ContactFlagBezout6543Research ContactSparsePoleSupportResearch
open ContactLocalPoleBound ContactMovingProjection6676Research
open ContactCommonProjectionChoice6676Research ContactMovingProjectionFamily6719Research
open ContactMovingCurveBudget6719Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K] [IsAlgClosed K]
local notation "Poly" => MvPolynomial (Fin 3) K
def budgetOfProjections (F A H G:Poly)
    {base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1}
    {p q:FlagDegree} (unit:AdaptiveUnitProjectionFamily base p q)
    (J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1))
    (hJ:∀ (C:RegularComponent K F A H) (v:Place K (CoordinateField K C.1)),
      poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
        movingPoleTarget C.1 H G v) (C:RegularComponent K F A H):
    MovingPoleBudget C.1 H G where
  zCost:=coordinateDegree K (CoordinateField K C.1) (unit.zProjection C)
  yzCost:=coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C)
  allCost:=coordinateDegree K (CoordinateField K C.1) (unit.allProjection C)
  movingCost:=SeparableCoordinate.degree K (CoordinateField K C.1) (J C)
  zPole:=unit.toAdaptiveUnitPoleBudget.zPole C
  yzPole:=unit.toAdaptiveUnitPoleBudget.yzPole C
  allPole:=unit.toAdaptiveUnitPoleBudget.allPole C
  movingPole:=by
    intro W
    calc
      (∑ v∈W,movingPoleTarget C.1 H G v)=
          ∑ v∈W,CoordinatePoleMass.poleOrder K (CoordinateField K C.1) v
            (SeparableCoordinate.value K (CoordinateField K C.1) (J C)):=by
        apply Finset.sum_congr rfl
        intro v _
        exact (hJ C v).symm
      _ ≤ (SeparableCoordinate.degree K (CoordinateField K C.1) (J C):ℤ):=
        SeparableCoordinate.finite_sum_pole_le_degree K (CoordinateField K C.1) (J C) W
variable {E:Type} [Field E] [IsAlgClosed E]
variable [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
theorem exists_moving_pole_budget_family (F H G:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
    (base:∀ C:RegularComponent K F (filteredCut k B H G) H,SeparableLiteralCoordinate C.1)
    (p firstCutFlag:FlagDegree) (unit:AdaptiveUnitProjectionFamily base p firstCutFlag)
    (hF:F≠0)
    (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
    (hFp:PolynomialInFlag p F) (a b s:ℕ) (C0:FlagDegree)
    (hH:PolynomialInFlag (⟨a,b+1,s+1⟩:FlagDegree) H)
    (hG:PolynomialInFlag (⟨a,b,s+3⟩:FlagDegree) G)
    (c:Fin (k+1) → FlagDegree) (hB:∀ j,PolynomialInFlag (c j) (B j))
    (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
      j.val • (⟨a,b,s+3⟩:FlagDegree)=C0+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
    (pchar:ℕ) [CharP E pchar]
    (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < pchar):
    ∃ budget:∀ C:RegularComponent K F (filteredCut k B H G) H,MovingPoleBudget C.1 H G,
      (∀ C,(budget C).zCost=coordinateDegree K (CoordinateField K C.1) (unit.zProjection C)∧
        (budget C).yzCost=coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C)∧
        (budget C).allCost=coordinateDegree K (CoordinateField K C.1) (unit.allProjection C))∧
      (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).zCost) ≤
        flagMixed p firstCutFlag unitZFlag∧
      (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).yzCost) ≤
        flagMixed p firstCutFlag unitYZFlag∧
      (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).allCost) ≤
        flagMixed p firstCutFlag unitAllFlag∧
      (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).movingCost) ≤
        flagMixed p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree)):=by
  obtain ⟨J,hJ,hdegree⟩:=exists_moving_projection_family (E:=E) F H G k B base
    hF hderiv p hFp a b s C0 hH hG c hB hc pchar hmix
  refine ⟨budgetOfProjections F (filteredCut k B H G) H G unit J hJ,?_,?_,?_,?_,?_⟩
  · exact fun C↦⟨rfl,rfl,rfl⟩
  · exact unit.sum_zDegree_le
  · exact unit.sum_yzDegree_le
  · exact unit.sum_allDegree_le
  · exact hdegree
end
end ProximityPrize.SubmissionLower.ContactMovingCurveFamily6719Research
