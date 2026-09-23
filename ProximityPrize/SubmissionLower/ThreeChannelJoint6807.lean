/-
UNCOMPILED. All THREE unit cuts are supplied by the actual generic-channel
construction; none is a theorem premise here. The remaining pointwise moving
inequality is the original actual-source output, consumed at the Stage entry.
-/
import ProximityPrize.SubmissionLower.ActualGenericChannel6807
import ProximityPrize.SubmissionLower.CommonLinearChannels6807
import ProximityPrize.SubmissionLower.JointBudgetArithmetic6807

namespace ProximityPrize.SubmissionLower.ThreeChannelJoint6807
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN095 RCN135 RCN136 RCN156 RCN207 RCN244 RCN264 RCN313
open RCN341 RCN344 RCN046 RCN237
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807 CommonLinearChannels6807
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "w" => RCN326.w

theorem joint_for_actual_unit_family
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1)
    (tailFlag : FlagDegree) (unit : AdaptiveUnitProjectionFamily base flag tailFlag)
    (common : CommonLinearValues unit) (active : Finset (FirstTailComponent S))
    (moving : FirstTailComponent S → ℕ)
    (P : Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hlead : ∀ C ∈ active, surfaceMap (polynomialEmbedding K) (asS P).leadingCoeff ∉ C.1)
    (hdiv : ∀ j ≤ k, S.F ∣ helper P S.F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (hdeg : flag.zOnly+flag.yz+flag.all < p)
    (hlinear : 2*(flag.zOnly+flag.yz+flag.all) < p)
    (hmoving : ∀ C ∈ active, (k+1)*moving C ≤
      unit.toPrimeFlagBudgetFamily.weightedCost
        (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) C)
    (normal : FlagDegree) (beta : ℕ) :
    (∑ C ∈ active,
      (localMultiplicity S (canonicalLocalDVRFamily S hp) C *
        unit.toPrimeFlagBudgetFamily.weightedCost normal C + beta*moving C)) ≤
      flagMixed flag
        ((k+1) • firstBaseFlag (w-1) r v z +
          w • SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)
        ((k+1) • normal + beta • SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)
        / (k+1)^2 := by
  classical
  let mu := fun C : FirstTailComponent S => localMultiplicity S (canonicalLocalDVRFamily S hp) C
  let V := SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0
  let D1 := (k+1) • firstBaseFlag (w-1) r v z + w • V
  let D2 := (k+1) • normal + beta • V
  let Cfam := unit.toPrimeFlagBudgetFamily
  let old : ↥active → FirstTailComponent S := Subtype.val
  have hold : Function.Injective old := Subtype.val_injective
  have htail (q : FlagDegree) (ell : MvPolynomial (Fin 3) Ω)
      (hell : PolynomialInFlag q ell)
      (projection : ∀ C : FirstTailComponent S, Coordinate Ω (CoordinateField Ω C.1))
      (hvalue : ∀ C : FirstTailComponent S, coordinateValue Ω (CoordinateField Ω C.1) (projection C) =
        coordinateEvaluation Ω C.1 ell)
      (hq : q.zOnly+q.yz+q.all = 1) :
      (k+1)*(∑ C : ↥active, mu C.1 * coordinateDegree Ω
        (CoordinateField Ω C.1.1) (projection C.1)) ≤ flagMixed flag D1 q := by
    have hm : 2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all) < p := by
      simpa only [hq,Nat.mul_one] using hlinear
    have hh := ActualGenericChannel6807.first_cut_for_coordinate_channel (E := E)
      S hp old hold ell q hell (fun C => projection C.1) (fun C => hvalue C.1)
      hdeg hm _ (fun C => hlead C.1 C.2) (k+1) (k+1) w _ _
      (ActiveSliceAssembly6807.first_slice_charge S hp _ P B U L s k n0 hS hP hBU hUL hdn hB hn
        hdiv h2 hfact r v z hr hv hR hYR hAll)
    simpa only [old,mu,D1,V,flagMixed_swap_last flag q D1] using hh
  have hz := htail unitZFlag linearZ linearZ_in_flag unit.zProjection
    (common_z_value unit) (by decide)
  have hy := htail unitYZFlag (linearU common.lam) (linearU_in_flag _)
    unit.yzProjection (common_u_value unit common) (by decide)
  have ha := htail unitAllFlag (linearA common.mu common.lam) (linearA_in_flag _ _)
    unit.allProjection (common_a_value unit common) (by decide)
  have hcut := JointBudgetArithmetic6807.three_unit_cuts (k+1)
    (fun C : ↥active => mu C.1)
    (fun C : ↥active => Cfam.zCost C.1)
    (fun C : ↥active => Cfam.yzCost C.1)
    (fun C : ↥active => Cfam.allCost C.1) flag D1 D2 hz hy ha
  have hlinear_cost (C : FirstTailComponent S) :
      Cfam.weightedCost D2 C = (k+1)*Cfam.weightedCost normal C +
        beta*Cfam.weightedCost V C := by
    simp only [Cfam,D2,PrimeFlagBudgetFamily.weightedCost,
      add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
    ring
  have hcut' : (k+1)*(∑ C : ↥active, mu C.1 *
      ((k+1)*Cfam.weightedCost normal C.1 + beta*Cfam.weightedCost V C.1)) ≤
        flagMixed flag D1 D2 := by
    change (k+1)*(∑ C : ↥active, mu C.1 * Cfam.weightedCost D2 C.1) ≤ _ at hcut
    simpa only [hlinear_cost] using hcut
  have result := JointBudgetArithmetic6807.joint_floor (k+1) beta
    (flagMixed flag D1 D2) (by omega)
    (fun C : ↥active => mu C.1)
    (fun C : ↥active => Cfam.weightedCost normal C.1)
    (fun C : ↥active => moving C.1)
    (fun C : ↥active => Cfam.weightedCost V C.1)
    (fun C => one_le_localMultiplicity S hp C.1)
    (fun C => hmoving C.1 C.2) hcut'
  rw [← Finset.sum_coe_sort active]
  exact result

end
end ProximityPrize.SubmissionLower.ThreeChannelJoint6807
