import ProximityPrize.SubmissionLower.R6960MonicChartLocal

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2900000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial Differential

abbrev paddedRes {A : Type*} [CommRing A] (f : A[X]) : A :=
  f.resultant f.derivative f.natDegree (f.natDegree-1)

theorem derivative_degree {R : Type*} [CommRing R] [NoZeroDivisors R] (f : R[X])
    (pos : 0<f.natDegree) (tame : (f.natDegree:R)≠0) :
    f.derivative.natDegree=f.natDegree-1 := by
  have e : f.natDegree-1+1=f.natDegree := Nat.sub_add_cancel pos
  apply le_antisymm (natDegree_derivative_le _)
  apply le_natDegree_of_ne_zero
  rw [coeff_derivative,←Nat.cast_add_one,e,coeff_natDegree]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr (fun h=>by rw [h,natDegree_zero] at pos; omega)) tame

theorem scaleRoots_derivative {R : Type*} [CommRing R] (f : R[X]) (r : R)
    (degree : f.derivative.natDegree=f.natDegree-1) :
    (f.scaleRoots r).derivative=f.derivative.scaleRoots r := by
  ext i
  rw [coeff_derivative,coeff_scaleRoots,coeff_scaleRoots,coeff_derivative,degree,
    show f.natDegree-(i+1)=f.natDegree-1-i by omega]
  ring

section Scaled

variable {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Algebra.IsSeparable F E] [FiniteDimensional F E]

/-- The reciprocal chart after scaling its generator by the evaluation
value. This equation is monic over the original base, even when the
evaluation value is a nonunit there. -/
def scaled (f : A[X]) (c : A) : A[X] := (f.taylor c).reverse.integralNormalization

private theorem reversed_lead (f : A[X]) (c : A) (un : f.eval c≠0) :
    (f.taylor c).reverse.leadingCoeff=f.eval c := by
  have co : (f.taylor c).coeff 0≠0 := by rwa [taylor_coeff_zero]
  rw [reverse_leadingCoeff,trailingCoeff_eq_coeff_zero co,taylor_coeff_zero]

theorem scaled_degree (f : A[X]) (c : A) (un : f.eval c≠0) :
    (scaled f c).natDegree=f.natDegree := by
  have co : (f.taylor c).coeff 0≠0 := by rwa [taylor_coeff_zero]
  rw [scaled,natDegree_integralNormalization,reverse_natDegree,
    natTrailingDegree_eq_zero.mpr (Or.inr co),Nat.sub_zero,natDegree_taylor]

private theorem scaled_basis (b : PowerBasis F E) (f : A[X]) (c : A)
    (un : f.eval c≠0) (pos : 0<f.natDegree) (degree : f.natDegree=b.dim)
    (root : aeval b.gen f=0) :
    ∃ v : PowerBasis F E, IsIntegral A v.gen ∧ minpoly A v.gen=scaled f c := by
  let i := algebraMap A E
  let j := algebraMap A F
  have ji : Function.Injective j := IsFractionRing.injective A F
  have ii : Function.Injective i := by
    rw [show (i : A→+*E)=(algebraMap F E).comp j from IsScalarTower.algebraMap_eq A F E]
    exact (algebraMap F E).injective.comp ji
  let u := f.eval c
  let w := b.gen-i c
  have wn : w≠0 := by
    intro h
    have eq : b.gen=i c := sub_eq_zero.mp h
    have root' : f.eval₂ i b.gen=0 := root
    rw [eq,eval₂_at_apply] at root'
    exact un (ii (root'.trans (map_zero i).symm))
  let β := w⁻¹
  let γ := i u*β
  let T := f.taylor c
  let r := T.reverse
  letI : Invertible w := invertibleOfNonzero wn
  have evalT : T.eval₂ i w=0 := by
    change (f.taylor c).eval₂ i (b.gen-i c)=0
    rw [taylor_apply,eval₂_comp,eval₂_add,eval₂_X,eval₂_C,sub_add_cancel]
    exact root
  have evalR := (eval₂_reverse_eq_zero_iff i w T).mpr evalT
  rw [invOf_eq_inv] at evalR
  have lead : r.leadingCoeff=u := reversed_lead f c un
  have rootG : aeval γ (scaled f c)=0 := by
    change r.integralNormalization.eval₂ i (i u*β)=0
    rw [← lead]
    exact integralNormalization_eval₂_eq_zero i evalR (fun a h => ii (h.trans (map_zero i).symm))
  have monicG : (scaled f c).Monic := monic_integralNormalization
    (leadingCoeff_ne_zero.mp (lead.symm ▸ un))
  have integral : IsIntegral A γ := ⟨scaled f c,monicG,rootG⟩
  let Cg := IntermediateField.adjoin F ({γ} : Set E)
  have memγ : γ∈Cg := IntermediateField.subset_adjoin F _ (Set.mem_singleton _)
  have memu : (i u)⁻¹ ∈ Cg := by
    apply Cg.inv_mem
    rw [show i u=algebraMap F E (j u) from IsScalarTower.algebraMap_apply A F E _]
    exact Cg.algebraMap_mem _
  have un' : i u≠0 := (map_ne_zero_iff _ ii).mpr un
  have beta : (i u)⁻¹*γ=β := by dsimp [γ]; rw [←mul_assoc,inv_mul_cancel₀ un',one_mul]
  have memβ : β∈Cg := beta ▸ Cg.mul_mem memu memγ
  have memc : i c∈Cg := by
    rw [show i c=algebraMap F E (j c) from IsScalarTower.algebraMap_apply A F E _]
    exact Cg.algebraMap_mem _
  have old_gen : b.gen∈Cg := by
    have h : β⁻¹+i c=b.gen := by simp [β,w]
    exact h ▸ Cg.add_mem (Cg.inv_mem memβ) memc
  have all : Cg=⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.top_toSubalgebra]
    apply le_antisymm le_top
    rw [←b.adjoin_gen_eq_top]
    exact Algebra.adjoin_le (fun _ hx=>Set.mem_singleton_iff.mp hx ▸ old_gen)
  let equiv : Cg ≃ₐ[F] E := (IntermediateField.equivOfEq all).trans IntermediateField.topEquiv
  let v := (IntermediateField.adjoin.powerBasis (K:=F) (x:=γ) (Algebra.IsIntegral.isIntegral γ)).map equiv
  have vg : v.gen=γ := rfl
  have vi : IsIntegral A v.gen := vg.symm ▸ integral
  have dim : v.dim=b.dim := v.finrank.symm.trans b.finrank
  let g := (scaled f c).map j
  have gm : g.Monic := monicG.map j
  have rooted : aeval v.gen g=0 := by rw [aeval_map_algebraMap,vg]; exact rootG
  have gdeg : g.natDegree=v.dim := by rw [natDegree_map_eq_of_injective ji,scaled_degree f c un,degree,dim]
  have minimal : g=minpoly F v.gen := by
    apply minpoly.unique_of_degree_le_degree_minpoly F v.gen gm rooted
    rw [degree_eq_natDegree gm.ne_zero,degree_eq_natDegree (minpoly.ne_zero v.isIntegral_gen),
      gdeg,v.natDegree_minpoly]
  refine ⟨v,vi,?_⟩
  apply Polynomial.map_injective _ ji
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' F vi]
  exact minimal.symm

private theorem map_reverse {B : Type*} [CommRing B] (j : A→+*B)
    (inj : Function.Injective j) (f : A[X]) : f.reverse.map j=(f.map j).reverse := by
  rw [reverse,reverse,reflect_map,natDegree_map_eq_of_injective inj]

/-- The scaled chart resultant divides the raw resultant after a power
of the evaluation value. The multiplier is a unit at every place
where the reciprocal chart was chosen. -/
theorem scaled_resultant_eq (b : PowerBasis F E) (f : A[X]) (c : A)
    (un : f.eval c≠0) (e2 : 2≤f.natDegree) (degree : f.natDegree=b.dim)
    (tame : (f.natDegree:F)≠0) (root : aeval b.gen f=0) :
    f.leadingCoeff*paddedRes (scaled f c)=(f.eval c)^((f.natDegree-1)*(f.natDegree-2))*paddedRes f := by
  let j := algebraMap A F
  have ji : Function.Injective j := IsFractionRing.injective A F
  let e := f.natDegree
  let a := j (f.eval c)
  have an : a≠0 := (map_ne_zero_iff _ ji).mpr un
  let U : Fˣ := Units.mk0 a an
  let P := f.map j
  let r := (f.taylor c).reverse
  let g := scaled f c
  let m := equation P (j c) U
  letI : IsFractionRing F F := IsFractionRing.idem A F
  have dP : P.natDegree=e := natDegree_map_eq_of_injective ji _
  have vP : P.eval (j c)=(U:F) := eval_map_apply j _
  have rP : aeval b.gen P=0 := by rw [aeval_map_algebraMap]; exact root
  have base := resultant_eq_chart (A:=F) b P (j c) U vP (dP.trans degree)
    (dP.symm ▸ e2) rP
  have base' : paddedRes P=j f.leadingCoeff*a^(2*e-2)*paddedRes m := by
    have lead : P.leadingCoeff=j f.leadingCoeff := leadingCoeff_map_of_injective ji _
    simpa only [Algebra.algebraMap_self,RingHom.id_apply,lead,dP,paddedRes,m,U,Units.val_mk0] using base
  have mr : m=C a⁻¹*(r.map j) := by
    unfold m equation
    change _ = C a⁻¹*(r.map j)
    rw [map_reverse j ji,map_taylor]
    rfl
  have rl : r.leadingCoeff=f.eval c := reversed_lead f c un
  have map_g : g.map j=m.scaleRoots a := by
    apply mul_right_cancel₀ (C_ne_zero.mpr an)
    calc
      _ = (r.scaleRoots r.leadingCoeff).map j := by
        change g.map j*C (j (f.eval c))=_
        rw [←rl,←Polynomial.map_C,←Polynomial.map_mul]
        exact congrArg (Polynomial.map j) (integralNormalization_mul_C_leadingCoeff r)
      _ = _ := by
        rw [map_scaleRoots _ _ _ (by rw [rl]; exact an),mr,mul_scaleRoots_of_noZeroDivisors,
          scaleRoots_C,rl]
        rw [mul_comm (C a⁻¹),mul_assoc,←C_mul,inv_mul_cancel₀ an,C_1,mul_one]
  have md : m.natDegree=e := (equation_degree P (j c) U vP).trans dP
  have der : m.derivative.natDegree=m.natDegree-1 :=
    derivative_degree m (md.symm ▸ (by omega : 0<e)) (md.symm ▸ tame)
  have res_g : j (paddedRes g)=a^(e*(e-1))*paddedRes m := by
    change j (g.resultant g.derivative g.natDegree (g.natDegree-1))=_
    rw [← resultant_map_map,← derivative_map,scaled_degree f c un,map_g,
      scaleRoots_derivative _ _ der]
    have eq := resultant_scaleRoots m m.derivative a
    rw [natDegree_scaleRoots,natDegree_scaleRoots,der,md] at eq
    simpa only [paddedRes,md,e] using eq
  have e_arith : e*(e-1)=(e-1)*(e-2)+(2*e-2) := by
    obtain ⟨k,h⟩ := Nat.exists_eq_add_of_le (show 2≤e from e2)
    rw [h,show 2+k-1=k+1 by omega,show 2+k-2=k by omega,
      show 2*(2+k)-2=2*k+2 by omega]
    ring
  apply ji
  rw [map_mul,map_mul,map_pow,res_g]
  have up : j (paddedRes f)=paddedRes P := by
    change j (f.resultant f.derivative f.natDegree (f.natDegree-1))=_
    rw [←resultant_map_map,←derivative_map]
    change P.resultant P.derivative f.natDegree (f.natDegree-1)=paddedRes P
    simp only [paddedRes,dP,e]
  rw [up,base',e_arith,pow_add]
  ring

section Differential
variable [Differential A] [Differential E] [DifferentialAlgebra A E]

theorem scaled_raw_square_clears (b : PowerBasis F E) (f : A[X]) (c : A)
    (un : f.eval c≠0) (e2 : 2≤f.natDegree) (degree : f.natDegree=b.dim)
    (tame : (f.natDegree:F)≠0) (root : aeval b.gen f=0)
    (x : E) (hx : IsIntegral A x) :
    IsIntegral A (algebraMap A E
      ((f.eval c)^(2*((f.natDegree-1)*(f.natDegree-2)))*(paddedRes f)^2)*x′) := by
  obtain ⟨v,vi,vg⟩ := scaled_basis b f c un (by omega) degree root
  have clear := DifferentialPoles.square_clears v vi x hx
  change IsIntegral A (algebraMap A E ((paddedRes (minpoly A v.gen))^2)*x′) at clear
  rw [vg] at clear
  rw [Nat.mul_comm 2 ((f.natDegree-1)*(f.natDegree-2)),pow_mul,←mul_pow]
  have identity := scaled_resultant_eq b f c un e2 degree tame root
  change IsIntegral A (algebraMap A E (((f.eval c)^((f.natDegree-1)*(f.natDegree-2))*
    paddedRes f)^2)*x′)
  rw [←identity,mul_pow,map_mul,mul_assoc]
  exact isIntegral_algebraMap.mul clear
end Differential

#print axioms scaled_resultant_eq
#print axioms scaled_raw_square_clears
end Scaled
end
end Lower6960.MonicChart
