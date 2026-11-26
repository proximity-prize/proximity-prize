import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Nilpotent
import ProximityPrize.SubmissionLower.Near6967LargeRank19g5
import ProximityPrize.SubmissionLower.R6960HornerNative
import ProximityPrize.SubmissionLower.R6960Low6960WeightedRow
import ProximityPrize.SubmissionLower.R6966ProofFixedNodeTariff

section Merged6967_R6966ProofPhysicalOriginal
set_option Elab.async false





set_option Elab.async false

namespace Research6966.PhysicalOriginal
open Polynomial Finset Module
open K1_14 (L FX Seeds Jet graphEval atX liftPoly seedEmbedding)
open K1_14_1 (PoleData CRTLift Source seedPair jetConstant)
open K1_14_1_4 (doubleMap centerBase)
open PhysicalPrimitiveCoeffs (R transpose)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

def evalSeed (t:Fin 2→L) : R→+*L[X]:=mapRingHom (MvPolynomial.eval t)
def param (t:Fin 2→L) : Fin 2→FX:=fun i=>algebraMap L FX (t i)
def atWord (t:Fin 2→L) (S:L[X]): R[X]→+*L[X] := eval₂RingHom (evalSeed t) S
def integralA (P:Source) : FixedNodeRows.Row (Fin 2) L:=(P.coeff 1).map transpose.toRingHom
def integralB (P:Source) : FixedNodeRows.Row (Fin 2) L:=-(P.coeff 0).map transpose.toRingHom

theorem transpose_eval (t:Fin 2→L) :
    (MvPolynomial.eval (fun i=>C (t i))).comp transpose.toRingHom=evalSeed t := by
  apply Polynomial.ringHom_ext'
  · apply MvPolynomial.ringHom_ext
    · intro c
      have k:(MvPolynomial.optionEquivLeft L (Fin 2)).symm (C (MvPolynomial.C c))=MvPolynomial.C c :=
        (MvPolynomial.optionEquivLeft L (Fin 2)).symm_apply_eq.mpr (MvPolynomial.optionEquivLeft_C L _ c).symm
      change MvPolynomial.eval _ ((MvPolynomial.optionEquivRight L _) ((MvPolynomial.optionEquivLeft L _).symm (C (MvPolynomial.C c))))=_
      rw [k,MvPolynomial.optionEquivRight_C,MvPolynomial.eval_C]
      simp [evalSeed]
    · intro i
      change MvPolynomial.eval _ ((MvPolynomial.optionEquivRight L _) ((MvPolynomial.optionEquivLeft L _).symm (C (MvPolynomial.X i))))=_
      rw [MvPolynomial.optionEquivLeft_symm_C_X,MvPolynomial.optionEquivRight_X_some,MvPolynomial.eval_X]
      simp [evalSeed]
  · change MvPolynomial.eval _ ((MvPolynomial.optionEquivRight L _) ((MvPolynomial.optionEquivLeft L _).symm Polynomial.X))=_
    rw [MvPolynomial.optionEquivLeft_symm_X,MvPolynomial.optionEquivRight_X_none,MvPolynomial.eval_C]
    simp [evalSeed]

theorem integral_slope (P:Source) (t:Fin 2→L) (S:L[X]) :
    FixedNodeRows.evaluate t S (integralA P)=atWord t S (P.coeff 1) := by
  change ((P.coeff 1).map transpose.toRingHom).eval₂ _ S=_
  rw [eval₂_map,transpose_eval];rfl

theorem integral_rhs (P:Source) (t:Fin 2→L) (S:L[X]) :
    FixedNodeRows.evaluate t S (integralB P) = -atWord t S (P.coeff 0) := by
  change (-((P.coeff 0).map transpose.toRingHom)).eval₂ _ S=_
  rw [eval₂_neg,eval₂_map,transpose_eval];rfl

private theorem at_fraction (t:Fin 2→L) :
    (algebraMap L[X] FX).comp (evalSeed t)=(MvPolynomial.eval (param t)).comp centerBase := by
  have move:(algebraMap L[X] FX).comp (MvPolynomial.eval (fun i=>C (t i)))=
      (MvPolynomial.eval (param t)).comp (MvPolynomial.map (algebraMap L[X] FX)) := by
    apply MvPolynomial.ringHom_ext
    · intro c;simp
    · intro i;simp [param,IsScalarTower.algebraMap_apply L L[X] FX]
  apply RingHom.ext
  intro x
  change algebraMap L[X] FX (evalSeed t x)=MvPolynomial.eval (param t) (centerBase x)
  rw [←PhysicalPrimitiveCoeffs.transpose_agrees]
  have a:=RingHom.congr_fun move (transpose x)
  rw [←transpose_eval]
  exact a

private theorem pair_map {A B:Type*} [CommRing A] [CommRing B] (f:A→+*B) (x:A) (n:ℕ) :
    (fun i=>f ((![x,x^n]:Fin 2→A) i))=![f x,(f x)^n] := by
  funext i;fin_cases i
  · rfl
  · exact map_pow f x n

private theorem pair (z:K1.K) : MvPolynomial.eval (param (seedPair z))=graphEval z := by
  apply congrArg MvPolynomial.eval
  have e:algebraMap L FX (algebraMap K1.K L z)=seedEmbedding z:=
    IsScalarTower.algebraMap_apply L L[X] FX _
  exact (pair_map (algebraMap L FX) (algebraMap K1.K L z) K1.p).trans
    (congrArg (fun x:FX=>(![x,x^K1.p]:Fin 2→FX)) e)

theorem evaluates_at_mark (z:K1.K) (S:L[X]) (P:R[X]) :
    algebraMap L[X] FX (atWord (seedPair z) S P)=
    (P.map centerBase).eval₂ (graphEval z) (algebraMap L[X] FX S) := by
  have compare:(algebraMap L[X] FX).comp (atWord (seedPair z) S)=
      (eval₂RingHom (graphEval z) (algebraMap L[X] FX S)).comp (mapRingHom centerBase) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,atWord,coe_eval₂RingHom,eval₂_C,coe_mapRingHom,Polynomial.map_C]
      have eq:=RingHom.congr_fun (at_fraction (seedPair z)) c
      rwa [pair] at eq
    · simp [atWord]
  exact RingHom.congr_fun compare P

theorem word_law {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} {M:HelperPhysicalModel.Model Crt N}
    (data:IntegralGraphModels.Model M) (z:K1.K) (S:K1.K[X])
    (law:(N.coeff 1).eval₂ (graphEval z) (atX S)*atX S.derivative=
      (-N.coeff 0).eval₂ (graphEval z) (atX S)) :
    FixedNodeRows.evaluate (seedPair z) (liftPoly S) (integralA data.original)*(liftPoly S).derivative=
      FixedNodeRows.evaluate (seedPair z) (liftPoly S) (integralB data.original) := by
  obtain ⟨c,_,rel⟩:=data.native_scalar
  have coefficients (j:ℕ):(data.original.coeff j).map centerBase=C c*N.coeff j := by
    simpa only [doubleMap,jetConstant,coe_mapRingHom,RingHom.comp_apply,coeff_map,coeff_C_mul]
      using congrArg (fun P:Jet=>P.coeff j) rel
  rw [integral_slope,integral_rhs]
  apply IsFractionRing.injective L[X] FX
  rw [map_mul,map_neg,evaluates_at_mark,evaluates_at_mark,coefficients,coefficients,eval₂_mul,eval₂_C,eval₂_mul,eval₂_C]
  have der:algebraMap L[X] FX (liftPoly S).derivative=atX S.derivative:=by rw [liftPoly,derivative_map];rfl
  rw [der,eval₂_neg] at *
  change (graphEval z c)*(N.coeff 1).eval₂ (graphEval z) (atX S)*atX S.derivative=
    -((graphEval z c)*(N.coeff 0).eval₂ (graphEval z) (atX S))
  linear_combination (graphEval z c)*law

theorem generically_regular {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} {M:HelperPhysicalModel.Model Crt N}
    (data:IntegralGraphModels.Model M) (z:K1.K) (S:K1.K[X])
    (reg:(N.coeff 1).eval₂ (graphEval z) (atX S)≠0) :
    atWord (seedPair z) (liftPoly S) (data.original.coeff 1)≠0 := by
  obtain ⟨c,unit,id⟩:=data.native_scalar
  have co:(data.original.coeff 1).map centerBase=C c*N.coeff 1 := by
    simpa only [doubleMap,jetConstant,coe_mapRingHom,RingHom.comp_apply,coeff_map,coeff_C_mul]
      using congrArg (fun P:Jet=>P.coeff 1) id
  intro zero
  have eq:=evaluates_at_mark z (liftPoly S) (data.original.coeff 1)
  rw [zero,map_zero,co,eval₂_mul,eval₂_C] at eq
  exact (mul_ne_zero (unit.map (graphEval z)).ne_zero reg) eq.symm

theorem coefficient_height {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} {M:HelperPhysicalModel.Model Crt N}
    (data:IntegralGraphModels.Model M) (j i:ℕ) :
    (transpose ((data.original.coeff j).coeff i)).totalDegree≤((N.coeff j).coeff i).totalDegree := by
  obtain ⟨c,unit,id⟩:=data.native_scalar
  have co:centerBase ((data.original.coeff j).coeff i)=c*((N.coeff j).coeff i) := by
    simpa only [doubleMap,jetConstant,coe_mapRingHom,RingHom.comp_apply,coeff_map,coeff_C_mul]
      using congrArg (fun P:Jet=>(P.coeff j).coeff i) id
  let T:=transpose ((data.original.coeff j).coeff i)
  have inj:=IsFractionRing.injective L[X] FX
  have deg:(MvPolynomial.map (algebraMap L[X] FX) T).totalDegree=T.totalDegree:=by
    unfold MvPolynomial.totalDegree;rw [MvPolynomial.support_map_of_injective _ inj]
  rw [←PhysicalPrimitiveCoeffs.transpose_agrees] at co
  change T.totalDegree≤_
  rw [←deg,show MvPolynomial.map (algebraMap L[X] FX) T=_ from co]
  exact (MvPolynomial.totalDegree_mul ..).trans (by rw [(MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp unit).2,zero_add])

#print axioms word_law
#print axioms generically_regular
#print axioms coefficient_height
end
end Research6966.PhysicalOriginal

end Merged6967_R6966ProofPhysicalOriginal

section Merged6967_R6966ProofSpreadReceipts0
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.SpreadCatalogue
private theorem edge19_7_18_2317_2522_cost : SpreadInterval.costSum shape 179759 19 7 18 2317 2522 ≤ 3263347300 := by decide +kernel
theorem edge19_7_18_2317_2522 : SpreadInterval.Positive shape 179759 19 7 18 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_7_18_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge19_8_19_2317_2522_cost : SpreadInterval.costSum shape 179759 19 8 19 2317 2522 ≤ 3174059208 := by decide +kernel
theorem edge19_8_19_2317_2522 : SpreadInterval.Positive shape 179759 19 8 19 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_8_19_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge19_10_19_2317_2522_cost : SpreadInterval.costSum shape 179759 19 10 19 2317 2522 ≤ 3234530788 := by decide +kernel
theorem edge19_10_19_2317_2522 : SpreadInterval.Positive shape 179759 19 10 19 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_10_19_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge19_11_19_2317_2341_cost : SpreadInterval.costSum shape 179759 19 11 19 2317 2341 ≤ 3291529060 := by decide +kernel
theorem edge19_11_19_2317_2341 : SpreadInterval.Positive shape 179759 19 11 19 nodes moment 2317 2341 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_11_19_2317_2341_cost) _).trans_lt <;> decide +kernel
private theorem edge19_11_19_2342_2522_cost : SpreadInterval.costSum shape 179759 19 11 19 2342 2522 ≤ 3299617197 := by decide +kernel
theorem edge19_11_19_2342_2522 : SpreadInterval.Positive shape 179759 19 11 19 nodes moment 2342 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_11_19_2342_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge21_6_19_2317_2522_cost : SpreadInterval.costSum shape 179759 21 6 19 2317 2522 ≤ 3245601513 := by decide +kernel
theorem edge21_6_19_2317_2522 : SpreadInterval.Positive shape 179759 21 6 19 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_6_19_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge21_7_20_2317_2522_cost : SpreadInterval.costSum shape 179759 21 7 20 2317 2522 ≤ 3118943927 := by decide +kernel
theorem edge21_7_20_2317_2522 : SpreadInterval.Positive shape 179759 21 7 20 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_7_20_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge21_8_21_2317_2522_cost : SpreadInterval.costSum shape 179759 21 8 21 2317 2522 ≤ 3026428592 := by decide +kernel
theorem edge21_8_21_2317_2522 : SpreadInterval.Positive shape 179759 21 8 21 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_8_21_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge21_11_21_2317_2522_cost : SpreadInterval.costSum shape 179759 21 11 21 2317 2522 ≤ 3103886580 := by decide +kernel
theorem edge21_11_21_2317_2522 : SpreadInterval.Positive shape 179759 21 11 21 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_11_21_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge21_12_21_2317_2522_cost : SpreadInterval.costSum shape 179759 21 12 21 2317 2522 ≤ 3169915828 := by decide +kernel
theorem edge21_12_21_2317_2522 : SpreadInterval.Positive shape 179759 21 12 21 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_12_21_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge21_13_21_2317_2522_cost : SpreadInterval.costSum shape 179759 21 13 21 2317 2522 ≤ 3249437368 := by decide +kernel
theorem edge21_13_21_2317_2522 : SpreadInterval.Positive shape 179759 21 13 21 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_13_21_2317_2522_cost) _).trans_lt <;> decide +kernel
end Research6966.SpreadCatalogue

end Merged6967_R6966ProofSpreadReceipts0

section Merged6967_R6966ProofSpreadReceipts1
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.SpreadCatalogue
private theorem edge24_5_21_2317_2522_cost : SpreadInterval.costSum shape 179759 24 5 21 2317 2522 ≤ 3260049040 := by decide +kernel
theorem edge24_5_21_2317_2522 : SpreadInterval.Positive shape 179759 24 5 21 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge24_5_21_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge24_6_22_2317_2522_cost : SpreadInterval.costSum shape 179759 24 6 22 2317 2522 ≤ 3082474588 := by decide +kernel
theorem edge24_6_22_2317_2522 : SpreadInterval.Positive shape 179759 24 6 22 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge24_6_22_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge24_7_23_2317_2522_cost : SpreadInterval.costSum shape 179759 24 7 23 2317 2522 ≤ 2948837103 := by decide +kernel
theorem edge24_7_23_2317_2522 : SpreadInterval.Positive shape 179759 24 7 23 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge24_7_23_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge24_8_24_2317_2522_cost : SpreadInterval.costSum shape 179759 24 8 24 2317 2522 ≤ 2851043046 := by decide +kernel
theorem edge24_8_24_2317_2522 : SpreadInterval.Positive shape 179759 24 8 24 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge24_8_24_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge24_13_24_2317_2522_cost : SpreadInterval.costSum shape 179759 24 13 24 2317 2522 ≤ 2976817363 := by decide +kernel
theorem edge24_13_24_2317_2522 : SpreadInterval.Positive shape 179759 24 13 24 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge24_13_24_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge24_14_24_2317_2522_cost : SpreadInterval.costSum shape 179759 24 14 24 2317 2522 ≤ 3047369438 := by decide +kernel
theorem edge24_14_24_2317_2522 : SpreadInterval.Positive shape 179759 24 14 24 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge24_14_24_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge24_15_24_2317_2522_cost : SpreadInterval.costSum shape 179759 24 15 24 2317 2522 ≤ 3126829782 := by decide +kernel
theorem edge24_15_24_2317_2522 : SpreadInterval.Positive shape 179759 24 15 24 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge24_15_24_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge24_16_24_2317_2522_cost : SpreadInterval.costSum shape 179759 24 16 24 2317 2522 ≤ 3213672483 := by decide +kernel
theorem edge24_16_24_2317_2522 : SpreadInterval.Positive shape 179759 24 16 24 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge24_16_24_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge25_5_23_2317_2522_cost : SpreadInterval.costSum shape 179759 25 5 23 2317 2522 ≤ 3182228876 := by decide +kernel
theorem edge25_5_23_2317_2522 : SpreadInterval.Positive shape 179759 25 5 23 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_5_23_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge25_6_24_2317_2522_cost : SpreadInterval.costSum shape 179759 25 6 24 2317 2522 ≤ 2999205210 := by decide +kernel
theorem edge25_6_24_2317_2522 : SpreadInterval.Positive shape 179759 25 6 24 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_6_24_2317_2522_cost) _).trans_lt <;> decide +kernel
end Research6966.SpreadCatalogue

end Merged6967_R6966ProofSpreadReceipts1

section Merged6967_R6966ProofSpreadReceipts2
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.SpreadCatalogue
private theorem edge25_7_25_2317_2522_cost : SpreadInterval.costSum shape 179759 25 7 25 2317 2522 ≤ 2860451521 := by decide +kernel
theorem edge25_7_25_2317_2522 : SpreadInterval.Positive shape 179759 25 7 25 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_7_25_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge25_13_25_2317_2522_cost : SpreadInterval.costSum shape 179759 25 13 25 2317 2522 ≤ 2900460566 := by decide +kernel
theorem edge25_13_25_2317_2522 : SpreadInterval.Positive shape 179759 25 13 25 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_13_25_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge25_14_25_2317_2522_cost : SpreadInterval.costSum shape 179759 25 14 25 2317 2522 ≤ 2965439687 := by decide +kernel
theorem edge25_14_25_2317_2522 : SpreadInterval.Positive shape 179759 25 14 25 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_14_25_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge25_15_25_2317_2522_cost : SpreadInterval.costSum shape 179759 25 15 25 2317 2522 ≤ 3039306894 := by decide +kernel
theorem edge25_15_25_2317_2522 : SpreadInterval.Positive shape 179759 25 15 25 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_15_25_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge25_16_25_2317_2522_cost : SpreadInterval.costSum shape 179759 25 16 25 2317 2522 ≤ 3120541800 := by decide +kernel
theorem edge25_16_25_2317_2522 : SpreadInterval.Positive shape 179759 25 16 25 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_16_25_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge25_17_25_2317_2522_cost : SpreadInterval.costSum shape 179759 25 17 25 2317 2522 ≤ 3207941993 := by decide +kernel
theorem edge25_17_25_2317_2522 : SpreadInterval.Positive shape 179759 25 17 25 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_17_25_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge25_18_25_2317_2328_cost : SpreadInterval.costSum shape 179759 25 18 25 2317 2328 ≤ 3291565378 := by decide +kernel
theorem edge25_18_25_2317_2328 : SpreadInterval.Positive shape 179759 25 18 25 nodes moment 2317 2328 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_18_25_2317_2328_cost) _).trans_lt <;> decide +kernel
private theorem edge25_18_25_2329_2522_cost : SpreadInterval.costSum shape 179759 25 18 25 2329 2522 ≤ 3300322465 := by decide +kernel
theorem edge25_18_25_2329_2522 : SpreadInterval.Positive shape 179759 25 18 25 nodes moment 2329 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_18_25_2329_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_4_26_2317_2522_cost : SpreadInterval.costSum shape 179759 29 4 26 2317 2522 ≤ 3277027878 := by decide +kernel
theorem edge29_4_26_2317_2522 : SpreadInterval.Positive shape 179759 29 4 26 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_4_26_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_5_27_2317_2522_cost : SpreadInterval.costSum shape 179759 29 5 27 2317 2522 ≤ 3051988156 := by decide +kernel
theorem edge29_5_27_2317_2522 : SpreadInterval.Positive shape 179759 29 5 27 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_5_27_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_6_28_2317_2522_cost : SpreadInterval.costSum shape 179759 29 6 28 2317 2522 ≤ 2861017541 := by decide +kernel
theorem edge29_6_28_2317_2522 : SpreadInterval.Positive shape 179759 29 6 28 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_6_28_2317_2522_cost) _).trans_lt <;> decide +kernel
end Research6966.SpreadCatalogue

end Merged6967_R6966ProofSpreadReceipts2

section Merged6967_R6966ProofSpreadReceipts3
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.SpreadCatalogue
private theorem edge29_7_29_2317_2522_cost : SpreadInterval.costSum shape 179759 29 7 29 2317 2522 ≤ 2714925007 := by decide +kernel
theorem edge29_7_29_2317_2522 : SpreadInterval.Positive shape 179759 29 7 29 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_7_29_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_15_29_2317_2522_cost : SpreadInterval.costSum shape 179759 29 15 29 2317 2522 ≤ 2749448082 := by decide +kernel
theorem edge29_15_29_2317_2522 : SpreadInterval.Positive shape 179759 29 15 29 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_15_29_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_16_29_2317_2522_cost : SpreadInterval.costSum shape 179759 29 16 29 2317 2522 ≤ 2812107513 := by decide +kernel
theorem edge29_16_29_2317_2522 : SpreadInterval.Positive shape 179759 29 16 29 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_16_29_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_17_29_2317_2522_cost : SpreadInterval.costSum shape 179759 29 17 29 2317 2522 ≤ 2880888485 := by decide +kernel
theorem edge29_17_29_2317_2522 : SpreadInterval.Positive shape 179759 29 17 29 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_17_29_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_18_29_2317_2522_cost : SpreadInterval.costSum shape 179759 29 18 29 2317 2522 ≤ 2954874034 := by decide +kernel
theorem edge29_18_29_2317_2522 : SpreadInterval.Positive shape 179759 29 18 29 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_18_29_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_19_29_2317_2522_cost : SpreadInterval.costSum shape 179759 29 19 29 2317 2522 ≤ 3033289923 := by decide +kernel
theorem edge29_19_29_2317_2522 : SpreadInterval.Positive shape 179759 29 19 29 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_19_29_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_20_29_2317_2522_cost : SpreadInterval.costSum shape 179759 29 20 29 2317 2522 ≤ 3115526945 := by decide +kernel
theorem edge29_20_29_2317_2522 : SpreadInterval.Positive shape 179759 29 20 29 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_20_29_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_21_29_2317_2522_cost : SpreadInterval.costSum shape 179759 29 21 29 2317 2522 ≤ 3201059910 := by decide +kernel
theorem edge29_21_29_2317_2522 : SpreadInterval.Positive shape 179759 29 21 29 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_21_29_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge29_22_29_2317_2522_cost : SpreadInterval.costSum shape 179759 29 22 29 2317 2522 ≤ 3289470104 := by decide +kernel
theorem edge29_22_29_2317_2522 : SpreadInterval.Positive shape 179759 29 22 29 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge29_22_29_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_4_37_2317_2522_cost : SpreadInterval.costSum shape 179759 41 4 37 2317 2522 ≤ 3071285516 := by decide +kernel
theorem edge41_4_37_2317_2522 : SpreadInterval.Positive shape 179759 41 4 37 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_4_37_2317_2522_cost) _).trans_lt <;> decide +kernel
end Research6966.SpreadCatalogue

end Merged6967_R6966ProofSpreadReceipts3

section Merged6967_R6966ProofSpreadReceipts4
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.SpreadCatalogue
private theorem edge41_5_38_2317_2522_cost : SpreadInterval.costSum shape 179759 41 5 38 2317 2522 ≤ 2832392170 := by decide +kernel
theorem edge41_5_38_2317_2522 : SpreadInterval.Positive shape 179759 41 5 38 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_5_38_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_6_39_2317_2522_cost : SpreadInterval.costSum shape 179759 41 6 39 2317 2522 ≤ 2625565475 := by decide +kernel
theorem edge41_6_39_2317_2522 : SpreadInterval.Positive shape 179759 41 6 39 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_6_39_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_7_40_2317_2522_cost : SpreadInterval.costSum shape 179759 41 7 40 2317 2522 ≤ 2464064671 := by decide +kernel
theorem edge41_7_40_2317_2522 : SpreadInterval.Positive shape 179759 41 7 40 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_7_40_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_8_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 8 41 2317 2522 ≤ 2341545913 := by decide +kernel
theorem edge41_8_41_2317_2522 : SpreadInterval.Positive shape 179759 41 8 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_8_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_21_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 21 41 2317 2522 ≤ 2465240243 := by decide +kernel
theorem edge41_21_41_2317_2522 : SpreadInterval.Positive shape 179759 41 21 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_21_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_22_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 22 41 2317 2522 ≤ 2519307840 := by decide +kernel
theorem edge41_22_41_2317_2522 : SpreadInterval.Positive shape 179759 41 22 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_22_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_23_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 23 41 2317 2522 ≤ 2575885653 := by decide +kernel
theorem edge41_23_41_2317_2522 : SpreadInterval.Positive shape 179759 41 23 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_23_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_24_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 24 41 2317 2522 ≤ 2634634210 := by decide +kernel
theorem edge41_24_41_2317_2522 : SpreadInterval.Positive shape 179759 41 24 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_24_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_25_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 25 41 2317 2522 ≤ 2695319782 := by decide +kernel
theorem edge41_25_41_2317_2522 : SpreadInterval.Positive shape 179759 41 25 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_25_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_26_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 26 41 2317 2522 ≤ 2757819304 := by decide +kernel
theorem edge41_26_41_2317_2522 : SpreadInterval.Positive shape 179759 41 26 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_26_41_2317_2522_cost) _).trans_lt <;> decide +kernel
end Research6966.SpreadCatalogue

end Merged6967_R6966ProofSpreadReceipts4

section Merged6967_R6966ProofSpreadReceipts5
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.SpreadCatalogue
private theorem edge41_27_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 27 41 2317 2522 ≤ 2821787245 := by decide +kernel
theorem edge41_27_41_2317_2522 : SpreadInterval.Positive shape 179759 41 27 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_27_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_28_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 28 41 2317 2522 ≤ 2887220249 := by decide +kernel
theorem edge41_28_41_2317_2522 : SpreadInterval.Positive shape 179759 41 28 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_28_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_29_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 29 41 2317 2522 ≤ 2953869714 := by decide +kernel
theorem edge41_29_41_2317_2522 : SpreadInterval.Positive shape 179759 41 29 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_29_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_30_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 30 41 2317 2522 ≤ 3021659117 := by decide +kernel
theorem edge41_30_41_2317_2522 : SpreadInterval.Positive shape 179759 41 30 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_30_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_31_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 31 41 2317 2522 ≤ 3090497591 := by decide +kernel
theorem edge41_31_41_2317_2522 : SpreadInterval.Positive shape 179759 41 31 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_31_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_32_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 32 41 2317 2522 ≤ 3160248916 := by decide +kernel
theorem edge41_32_41_2317_2522 : SpreadInterval.Positive shape 179759 41 32 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_32_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge41_33_41_2317_2522_cost : SpreadInterval.costSum shape 179759 41 33 41 2317 2522 ≤ 3230931691 := by decide +kernel
theorem edge41_33_41_2317_2522 : SpreadInterval.Positive shape 179759 41 33 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_33_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_3_38_2317_2322_cost : SpreadInterval.costSum shape 179759 43 3 38 2317 2322 ≤ 3291541837 := by decide +kernel
theorem edge43_3_38_2317_2322 : SpreadInterval.Positive shape 179759 43 3 38 nodes moment 2317 2322 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_3_38_2317_2322_cost) _).trans_lt <;> decide +kernel
private theorem edge43_3_38_2323_2522_cost : SpreadInterval.costSum shape 179759 43 3 38 2323 2522 ≤ 3300370522 := by decide +kernel
theorem edge43_3_38_2323_2522 : SpreadInterval.Positive shape 179759 43 3 38 nodes moment 2323 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_3_38_2323_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_4_39_2317_2522_cost : SpreadInterval.costSum shape 179759 43 4 39 2317 2522 ≤ 3046368744 := by decide +kernel
theorem edge43_4_39_2317_2522 : SpreadInterval.Positive shape 179759 43 4 39 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_4_39_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_5_40_2317_2522_cost : SpreadInterval.costSum shape 179759 43 5 40 2317 2522 ≤ 2805536005 := by decide +kernel
theorem edge43_5_40_2317_2522 : SpreadInterval.Positive shape 179759 43 5 40 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_5_40_2317_2522_cost) _).trans_lt <;> decide +kernel
end Research6966.SpreadCatalogue

end Merged6967_R6966ProofSpreadReceipts5

section Merged6967_R6966ProofSpreadReceipts6
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.SpreadCatalogue
private theorem edge43_6_41_2317_2522_cost : SpreadInterval.costSum shape 179759 43 6 41 2317 2522 ≤ 2596467666 := by decide +kernel
theorem edge43_6_41_2317_2522 : SpreadInterval.Positive shape 179759 43 6 41 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_6_41_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_7_42_2317_2522_cost : SpreadInterval.costSum shape 179759 43 7 42 2317 2522 ≤ 2432717011 := by decide +kernel
theorem edge43_7_42_2317_2522 : SpreadInterval.Positive shape 179759 43 7 42 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_7_42_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_8_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 8 43 2317 2522 ≤ 2308065390 := by decide +kernel
theorem edge43_8_43_2317_2522 : SpreadInterval.Positive shape 179759 43 8 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_8_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_22_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 22 43 2317 2522 ≤ 2432668294 := by decide +kernel
theorem edge43_22_43_2317_2522 : SpreadInterval.Positive shape 179759 43 22 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_22_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_23_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 23 43 2317 2522 ≤ 2485375809 := by decide +kernel
theorem edge43_23_43_2317_2522 : SpreadInterval.Positive shape 179759 43 23 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_23_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_24_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 24 43 2317 2522 ≤ 2540252528 := by decide +kernel
theorem edge43_24_43_2317_2522 : SpreadInterval.Positive shape 179759 43 24 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_24_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_25_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 25 43 2317 2522 ≤ 2597063550 := by decide +kernel
theorem edge43_25_43_2317_2522 : SpreadInterval.Positive shape 179759 43 25 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_25_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_26_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 26 43 2317 2522 ≤ 2655684965 := by decide +kernel
theorem edge43_26_43_2317_2522 : SpreadInterval.Positive shape 179759 43 26 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_26_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_27_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 27 43 2317 2522 ≤ 2715775034 := by decide +kernel
theorem edge43_27_43_2317_2522 : SpreadInterval.Positive shape 179759 43 27 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_27_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_28_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 28 43 2317 2522 ≤ 2777328686 := by decide +kernel
theorem edge43_28_43_2317_2522 : SpreadInterval.Positive shape 179759 43 28 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_28_43_2317_2522_cost) _).trans_lt <;> decide +kernel
end Research6966.SpreadCatalogue

end Merged6967_R6966ProofSpreadReceipts6

section Merged6967_R6966ProofSpreadReceipts7
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.SpreadCatalogue
private theorem edge43_29_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 29 43 2317 2522 ≤ 2840095987 := by decide +kernel
theorem edge43_29_43_2317_2522 : SpreadInterval.Positive shape 179759 43 29 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_29_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_30_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 30 43 2317 2522 ≤ 2904002575 := by decide +kernel
theorem edge43_30_43_2317_2522 : SpreadInterval.Positive shape 179759 43 30 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_30_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_31_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 31 43 2317 2522 ≤ 2968956991 := by decide +kernel
theorem edge43_31_43_2317_2522 : SpreadInterval.Positive shape 179759 43 31 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_31_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_32_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 32 43 2317 2522 ≤ 3034825751 := by decide +kernel
theorem edge43_32_43_2317_2522 : SpreadInterval.Positive shape 179759 43 32 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_32_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_33_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 33 43 2317 2522 ≤ 3101625068 := by decide +kernel
theorem edge43_33_43_2317_2522 : SpreadInterval.Positive shape 179759 43 33 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_33_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_34_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 34 43 2317 2522 ≤ 3169160729 := by decide +kernel
theorem edge43_34_43_2317_2522 : SpreadInterval.Positive shape 179759 43 34 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_34_43_2317_2522_cost) _).trans_lt <;> decide +kernel
private theorem edge43_35_43_2317_2522_cost : SpreadInterval.costSum shape 179759 43 35 43 2317 2522 ≤ 3237369268 := by decide +kernel
theorem edge43_35_43_2317_2522 : SpreadInterval.Positive shape 179759 43 35 43 nodes moment 2317 2522 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;> apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge43_35_43_2317_2522_cost) _).trans_lt <;> decide +kernel
end Research6966.SpreadCatalogue

end Merged6967_R6966ProofSpreadReceipts7
