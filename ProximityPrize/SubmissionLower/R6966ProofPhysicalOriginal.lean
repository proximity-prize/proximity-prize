import ProximityPrize.SubmissionLower.R6966ProofIntegralGraphModels
import ProximityPrize.SubmissionLower.R6966ProofNativeGraphExceptional
import ProximityPrize.SubmissionLower.R6966ProofFixedNodeTariff
import Mathlib.Algebra.MvPolynomial.Nilpotent

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
