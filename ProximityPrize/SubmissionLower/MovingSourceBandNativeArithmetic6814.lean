import ProximityPrize.SubmissionLower.MovingSourceBandNativeForms6814
import ProximityPrize.SubmissionLower.MovingSourceBandNativeCount6814

/-! Identify the actual native packet numerator with the affine forms
used by the finite cover. Constants are checked, not trusted from Python. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandNativeArithmetic6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 25000
open scoped BigOperators
open RCN095 MovingSourceBandReceipts6814 MovingSourceBandPairArithmetic6814
open MovingSourceBandNativeCount6814 MovingSourceBandNativeForms6814
open MovingFiberThreeSources6811 MovingFiberRetainedStage6811 HFreeDir6813

def scalar (i : Fin 11) (m s b u t : ℕ) : ℕ :=
  m*fixedNumerator (cell i).total (cell i).middle (cell i).slope
      ⟨(cell i).total-(cell i).middle,(cell i).middle-(cell i).slope,(cell i).slope⟩+
    ∑ j : Fin 3, coefficient (cell i).total (cell i).middle (cell i).slope j*
      flagMixed ⟨(cell i).total-(cell i).middle,(cell i).middle-(cell i).slope,(cell i).slope⟩
        (direction j) (SecondJetRelaxedFlag.budgetFlag b u t m s)

theorem native_numerator_eq {K : Type} [Field K] [CharP K 2130706433]
    {F : MvPolynomial (Fin 4) K} (source : Source F) (i : Fin 11) (m s b u t : ℕ)
    (hm : 0<m) (hd : source.d=m) (hf : source.flag=SecondJetRelaxedFlag.budgetFlag b u t m s) :
    nativeNumerator source (cell i).total (cell i).middle (cell i).slope
      ⟨(cell i).total-(cell i).middle,(cell i).middle-(cell i).slope,(cell i).slope⟩=
      scalar i m s b u t := by
  unfold nativeNumerator numeratorDir scalar
  simp only [hd,hf,Nat.mul_div_cancel_left m (by decide : 0<3),
    Nat.div_self (by omega : 0<3*m),Nat.mul_div_cancel 3 hm,mul_one,Finset.sum_add_distrib]
  refine congrArg₂ (fun a b : ℕ => a+b) ?_ ?_
  · unfold fixedNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    unfold coefficient
    simp only [RCN326.w,RCN327.w]
    ring

theorem scalar_linear (i : Fin 11) (m s b u t : ℕ)
    (hms : m≤s) (hsb : 2*s≤b) (hbu : b≤u) (hut : u≤t) :
    scalar i m s b u t+(form i).s*s=
      (form i).b*b+(form i).u*u+(form i).t*t+(form i).m*m := by
  fin_cases i <;>
    norm_num [scalar,cell,form,fixedNumerator,coefficient,Fin.sum_univ_three,
      weight,direction,BoundaryTailProvider.cellNormal,BoundaryTailAlgebra.normalFlag,
      rawFirstFlag,hfreeFirstDir,hfreeFlagDir,cuspFlag,flagMixed,
      LocatorHybridCells.cellA,LocatorHybridCells.cellB,LocatorHybridCells.cellS,RCN198.center,RCN198.direction,
      SecondJetRelaxedFlag.budgetFlag,RCN326.w,RCN327.w,
      unitZFlag,unitYZFlag,unitAllFlag,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ] <;> omega

theorem failure_iff (i : Fin 11) (m s b u t : ℕ)
    (hms : m≤s) (hsb : 2*s≤b) (hbu : b≤u) (hut : u≤t) :
    Failure i m s b u t ↔ 3*269880000000000000*m≤scalar i m s b u t := by
  have h := scalar_linear i m s b u t hms hsb hbu hut
  have hp := positive i
  have he := Nat.sub_add_cancel (show (form i).m≤3*269880000000000000 by omega)
  have heM := congrArg (fun n : ℕ => n*m) he
  simp only [Nat.add_mul] at heM
  unfold Failure
  constructor <;> intro hf <;> omega

#print axioms native_numerator_eq
#print axioms scalar_linear
#print axioms failure_iff
end
end ProximityPrize.SubmissionLower.MovingSourceBandNativeArithmetic6814
