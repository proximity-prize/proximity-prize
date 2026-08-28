import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingPoleLocal6719Research
import ProximityPrize.SubmissionLower.ContactRationalRegularZero6676Research

/-! .
 -/
namespace ProximityPrize.SubmissionLower.ContactMovingCurveBudget6719Research
open scoped Classical BigOperators WithZero
open ActualCurveCoordinateField CoordinateBoxZeroCount ContactWeakSeparableSeparatorResearch
open ContactFlagBezout6543Research ContactFlagPoleInequality6543Research
open ContactSparsePoleSupportResearch ContactLocalPoleBound
open ContactMovingProjection6676Research ContactCommonProjectionChoice6676Research
open ContactMovingPoleLocal6719Research ContactRegularZeroBudget6676Research
open ContactRationalRegularZero6676Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K

structure MovingPoleBudget (P : Ideal Poly) [P.IsPrime] (H G : Poly) where
  zCost : ℕ
  yzCost : ℕ
  allCost : ℕ
  movingCost : ℕ
  zPole : ∀ W : Finset (Place K (CoordinateField K P)),
    (∑ v ∈ W,exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitZFlag)) ≤ (zCost : ℤ)
  yzPole : ∀ W : Finset (Place K (CoordinateField K P)),
    (∑ v ∈ W,exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitYZFlag)) ≤ (yzCost : ℤ)
  allPole : ∀ W : Finset (Place K (CoordinateField K P)),
    (∑ v ∈ W,exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitAllFlag)) ≤ (allCost : ℤ)
  movingPole : ∀ W : Finset (Place K (CoordinateField K P)),
    (∑ v ∈ W,movingPoleTarget P H G v) ≤ (movingCost : ℤ)

namespace MovingPoleBudget
variable {P : Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
variable {H G : MvPolynomial (Fin 3) K}

def weightedCost (budget : MovingPoleBudget P H G) (r : FlagDegree) : ℕ :=
  r.zOnly*budget.zCost+r.yz*budget.yzCost+r.all*budget.allCost

theorem sum_flagPole_le (budget : MovingPoleBudget P H G) (r : FlagDegree)
    (W : Finset (Place K (CoordinateField K P))) :
    (∑ v ∈ W,flagPole v.val (coordinate K P) r) ≤ (budget.weightedCost r : ℤ) := by
  have hz := budget.zPole W
  have hy := budget.yzPole W
  have ha := budget.allPole W
  simp only [exponentSetPoleWeight_unitZ] at hz
  simp only [exponentSetPoleWeight_unitYZ] at hy
  simp only [exponentSetPoleWeight_unitAll] at ha
  have h := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg r.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg r.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg r.all))
  simpa only [flagPole,Finset.sum_add_distrib,← Finset.mul_sum,
    weightedCost,Nat.cast_add,Nat.cast_mul] using h

/-- .
 -/
theorem sum_filteredCut_pole_le (budget : MovingPoleBudget P H G)
    (a b s k : ℕ) (C : FlagDegree) (B : Fin (k+1) → Poly)
    (c : Fin (k+1) → FlagDegree) (hH : H ∉ P)
    (hB : ∀ j,PolynomialInFlag (c j) (B j))
    (hc : ∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree))
    (W : Finset (Place K (CoordinateField K P))) :
    (∑ v ∈ W,poleOrder v.val (coordinateEvaluation K P (filteredCut k B H G)/
      (coordinateEvaluation K P H)^k)) ≤
      (budget.weightedCost C+k*(budget.weightedCost (⟨a,b,s⟩ : FlagDegree)+budget.movingCost) : ℕ) := by
  have hHne : coordinateEvaluation K P H ≠ 0 := by
    intro hz
    apply hH
    rw [← coordinateEvaluation_ker K P]
    exact hz
  have hloc := Finset.sum_le_sum (s := W) (fun v _ ↦
    coordinate_filteredCut_pole_le P v a b s k C B H G c hHne hB hc)
  have hflagC := budget.sum_flagPole_le C W
  have hflagN := budget.sum_flagPole_le (⟨a,b,s⟩ : FlagDegree) W
  have hmoving := budget.movingPole W
  calc
    _ ≤ ∑ v ∈ W,(flagPole v.val (coordinate K P) C+(k : ℤ)*
        (flagPole v.val (coordinate K P) (⟨a,b,s⟩ : FlagDegree)+movingPoleTarget P H G v)) := hloc
    _ = (∑ v ∈ W,flagPole v.val (coordinate K P) C)+(k : ℤ)*
        ((∑ v ∈ W,flagPole v.val (coordinate K P) (⟨a,b,s⟩ : FlagDegree))+
          ∑ v ∈ W,movingPoleTarget P H G v) := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    _ ≤ (budget.weightedCost C : ℤ)+(k : ℤ)*
        ((budget.weightedCost (⟨a,b,s⟩ : FlagDegree) : ℤ)+budget.movingCost) :=
      add_le_add hflagC (mul_le_mul_of_nonneg_left (add_le_add hflagN hmoving) (Int.natCast_nonneg k))
    _ = _ := by push_cast; rfl

/-- .
 -/
theorem zero_le [IsAlgClosed K] (budget : MovingPoleBudget P H G)
    (base : SeparableLiteralCoordinate P) (a b s k : ℕ) (C : FlagDegree)
    (B : Fin (k+1) → Poly) (c : Fin (k+1) → FlagDegree)
    (hH : H ∉ P) (hA : filteredCut k B H G ∉ P)
    (hB : ∀ j,PolynomialInFlag (c j) (B j))
    (hc : ∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree)) :
    FiniteRegularZeroSetBound P H (filteredCut k B H G)
      (budget.weightedCost C+k*(budget.weightedCost (⟨a,b,s⟩ : FlagDegree)+budget.movingCost)) := by
  apply finite_regular_zero_bound_of_separator K P base H (filteredCut k B H G) k _ hA hH
  intro W
  simpa only [CoordinatePoleMass.poleOrder,coordinateEvaluation_eq_aeval] using
    budget.sum_filteredCut_pole_le a b s k C B c hH hB hc W

end MovingPoleBudget
end
end ProximityPrize.SubmissionLower.ContactMovingCurveBudget6719Research
