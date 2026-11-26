import ProximityPrize.SubmissionLower.R6966ProofNativeGraphMarks
import ProximityPrize.SubmissionLower.R6960ThirdPole

set_option Elab.async false

namespace Research6966.NativeGraphExceptional
open Polynomial Finset
open K1_14 (Seeds Equation FX seedEmbedding graphEval atX)
open K1_14_3 (SeedField SeedClosure)
open PadeNativeQuotient (Native)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private abbrev φ:=K1_14_3.seedGeneric
private abbrev f:=algebraMap SeedField SeedClosure
def den {G:Pade.Row SeedField} (N:Native G) : Equation := N.poly.coeff 1
def rhs {G:Pade.Row SeedField} (N:Native G) : Equation := -N.poly.coeff 0

theorem den_ne {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) : den N≠0 := by
  change N.poly.coeff 1≠0
  rw [←NativeGraphMarks.slope_degree N gp,coeff_natDegree]
  exact leadingCoeff_ne_zero.mpr N.primitive.ne_zero

theorem coprime_generic {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) :
    IsCoprime ((den N).map φ) ((rhs N).map φ) := by
  have A:(den N).map φ=C N.scalar*(G.map f).a := by
    have eq:=congrArg (fun P:SeedClosure[X][X]=>P.coeff 1) N.eq
    simpa [K1_14_3.fibreRow,K1_14_1.jetConstant,Pade.Row.polynomial,coeff_C_mul,den] using eq
  have B:(rhs N).map φ=C N.scalar*(G.map f).b := by
    have eq:=congrArg (fun P:SeedClosure[X][X]=> -(P.coeff 0)) N.eq
    simpa [K1_14_3.fibreRow,K1_14_1.jetConstant,Pade.Row.polynomial,coeff_C_mul,rhs] using eq
  obtain ⟨l,w,bez⟩:=((G.primitive_map f).mpr gp).2
  have cop:IsCoprime ((den N).map φ) ((rhs N).map φ) := by
    refine ⟨C N.scalar⁻¹*l,C N.scalar⁻¹*w,?_⟩
    rw [A,B]
    calc
      _ = (C N.scalar⁻¹*C N.scalar)*(l*(G.map f).a+w*(G.map f).b) := by ring
      _ = 1 := by rw [bez,←C_mul,inv_mul_cancel₀ N.nonzero,map_one,one_mul]
  exact cop

theorem proper {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) :
    (den N).resultant (rhs N)≠0 := by
  have inj:Function.Injective φ:=f.injective.comp (IsFractionRing.injective Seeds SeedField)
  have nonzero:=Polynomial.resultant_ne_zero _ _ (coprime_generic N gp)
  intro zero
  apply nonzero
  rw [natDegree_map_eq_of_injective inj,natDegree_map_eq_of_injective inj,
    Polynomial.resultant_map_map,zero,map_zero]

/-- Count the actual labels at which the differential denominator vanishes
identically in physical X. The mixed axis price uses the Frobenius curve
only once. -/
theorem singular_count {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (width:Fin 2→ℕ)
    (axes:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (small:(2*G.graphDegree-1)*width 0<K1.p) (T:Finset K1.K) (label:K1.K→K1.K)
    (inject:Set.InjOn label (T:Set K1.K)) (y:K1.K→FX)
    (zero:∀ γ∈T,(den N).eval₂ (graphEval (label γ)) (y γ)=0)
    (law:∀ γ∈T,(rhs N).eval₂ (graphEval (label γ)) (y γ)=0) :
    T.card≤(2*G.graphDegree-1)*(width 0+K1.p*width 1) := by
  classical
  let e:=2*G.graphDegree-1
  let z (γ:K1.K):=seedEmbedding (label γ)
  let marks:=T.image z
  have inj:Set.InjOn z (T:Set K1.K):=fun _ hx _ hy eq=>inject hx hy (seedEmbedding.injective eq)
  have size:marks.card=T.card:=Finset.card_image_iff.mpr inj
  have capA (i:ℕ) (j:Fin 2):((den N).coeff i).degreeOf j≤width j:=axes 1 i j
  have capB (i:ℕ) (j:Fin 2):((rhs N).coeff i).degreeOf j≤width j:=by
    simpa [rhs,coeff_neg] using axes 0 i j
  obtain ⟨ac,bc⟩:=NativeGraphMarks.equation_degrees N gp
  have pos:0<G.graphDegree:=by unfold Pade.Row.graphDegree;omega
  have combined:(den N).natDegree+(rhs N).natDegree≤e:=by dsimp only [den,rhs,e];omega
  have sumCap (j:Fin 2):(rhs N).natDegree*width j+(den N).natDegree*width j≤e*width j:=by
    rw [←Nat.add_mul,Nat.add_comm];exact Nat.mul_le_mul_right _ combined
  rw [←size]
  by_cases ord:(den N).natDegree≠0 ∨ (rhs N).natDegree≠0
  · have count:=Lower6960.ThirdPole.count_common K1.p (by decide) (den N) (rhs N)
      (width 0) (width 1) (width 0) (width 1) (fun i=>⟨capA i 0,capA i 1⟩)
      (fun i=>⟨capB i 0,capB i 1⟩) ord (proper N gp) ((sumCap 0).trans_lt small) marks (by
        rintro _ hx;obtain ⟨γ,mem,rfl⟩:=mem_image.mp hx
        refine ⟨y γ,?_,?_⟩
        · rw [eval_map];exact zero γ mem
        · rw [eval_map];exact law γ mem)
    exact count.trans ((Nat.add_le_add (sumCap 0) (Nat.mul_le_mul_left K1.p (sumCap 1))).trans_eq (by dsimp [e];ring))
  · have d0:(den N).natDegree=0:=by tauto
    let C₀:Seeds:=(den N).coeff 0
    have cne:C₀≠0:=by
      change (den N).coeff 0≠0;rw [←d0,coeff_natDegree];exact leadingCoeff_ne_zero.mpr (den_ne N gp)
    have ep:1≤e:=by dsimp [e];omega
    have short:width 0≤e*width 0:=by simpa only [one_mul] using Nat.mul_le_mul_right (width 0) ep
    have count:=K1_10.frobenius_coefficient_exception_count K1.p (width 0) (width 1) (by decide) C₀ cne
      (capA 0 0) (short.trans_lt small) (capA 0 1) marks (by
        rintro _ hx;obtain ⟨γ,mem,rfl⟩:=mem_image.mp hx
        have eq:den N=C C₀:=eq_C_of_natDegree_eq_zero d0
        have root:=zero γ mem
        rw [eq,eval₂_C] at root
        exact root)
    exact count.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (width 0+K1.p*width 1) ep)

end
end Research6966.NativeGraphExceptional
