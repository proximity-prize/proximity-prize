import ProximityPrize.SubmissionLower.R6960MarkedScalarPlace
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

-- merged module R6960DifferentialPoles
section Merged_R6960DifferentialPoles
noncomputable section
set_option Elab.async false
namespace Lower6960.DifferentialPoles
open Polynomial Algebra Module
open scoped Polynomial Differential
theorem resultant_norm {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] (b : PowerBasis F E) (g : (Polynomial F))
    (n : ℕ) (bound : g.natDegree≤n) :
    (minpoly F b.gen).resultant g (minpoly F b.gen).natDegree n=Algebra.norm F (aeval b.gen g) := by
  classical
  let Ω:=AlgebraicClosure E
  let a:=algebraMap F Ω
  have inj:=a.injective
  let roots := (minpoly F b.gen).aroots Ω
  have nodup : roots.Nodup := nodup_roots (Separable.map (Algebra.IsSeparable.isSeparable F b.gen))
  let R : Finset Ω := ⟨roots,nodup⟩
  let e : (E→ₐ[F]Ω)≃↥R := b.liftEquiv'
  have monic := (minpoly.monic b.isIntegral_gen).map a
  apply inj
  rw [←resultant_map_map,←natDegree_map_eq_of_injective inj (minpoly F b.gen),
    resultant_eq_prod_eval _ _ _ (natDegree_map_le.trans bound) (IsAlgClosed.splits _),
    monic.leadingCoeff,one_pow,one_mul,Algebra.norm_eq_prod_embeddings]
  change (roots.map (g.map a).eval).prod=_
  calc _ = ∏ r∈R,(g.map a).eval r := rfl
       _ = ∏ r : R,(g.map a).eval (r:Ω) := (Finset.prod_coe_sort ..).symm
       _ = ∏ σ : E→ₐ[F]Ω,(g.map a).eval ((e σ):Ω) := (e.prod_comp _).symm
       _ = _ := by
         apply Finset.prod_congr rfl
         intro σ _
         change (g.map a).eval (σ b.gen)=σ (aeval b.gen g)
         rw [eval_map_algebraMap,aeval_algHom_apply]
section Local
variable {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Algebra.IsSeparable F E] [FiniteDimensional F E]
    [Differential A] [Differential E] [DifferentialAlgebra A E]
omit [IsDomain A] [IsIntegrallyClosed A] [Differential A] [Differential E] [DifferentialAlgebra A E] in
private theorem eval_integral {u : E} (hu : IsIntegral A u) (q : (Polynomial A)) :
    IsIntegral A (aeval u q) := by
  apply adjoin_le_integralClosure hu
  rw [adjoin_singleton_eq_range_aeval]
  exact ⟨q,rfl⟩
omit [IsDomain A] [IsIntegrallyClosed A] in
theorem root_derivative {y : E} (integral : IsIntegral A y) (f : (Polynomial A))
    (positive : 0<f.natDegree) (root : aeval y f=0) :
    IsIntegral A (algebraMap A E (f.resultant f.derivative f.natDegree (f.natDegree-1))*y′) := by
  let Δ:=f.resultant f.derivative f.natDegree (f.natDegree-1)
  obtain ⟨g,q,_,_,bez⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative le_rfl
    (natDegree_derivative_le _) (Or.inl positive.ne')
  have clearing := congrArg (aeval y) bez
  simp only [map_add,map_mul,root,zero_mul,zero_add,aeval_C] at clearing
  have derivative := Differential.deriv_aeval_eq y f
  rw [root,map_zero] at derivative
  have eq : algebraMap A E Δ*y′ = -(aeval y q)*(aeval y (Differential.mapCoeffs f)) := by
    rw [←clearing]
    linear_combination (aeval y q)*derivative.symm
  rw [eq]
  exact (eval_integral integral q).neg.mul (eval_integral integral _)
omit [IsDomain A] in
theorem integral_derivative (b : PowerBasis F E) (integral : IsIntegral A b.gen)
    (f : (Polynomial A)) (positive : 0<f.natDegree) (root : aeval b.gen f=0)
    (d : A) (hd : algebraMap A F d=Algebra.discr F b.basis) (x : E) (hx : IsIntegral A x) :
    IsIntegral A (algebraMap A E (d*(f.resultant f.derivative f.natDegree (f.natDegree-1)))*x′) := by
  let r:=f.resultant f.derivative f.natDegree (f.natDegree-1)
  have native := Algebra.discr_mul_isIntegral_mem_adjoin F (B:=b) integral hx
  rw [←hd,Algebra.smul_def,←IsScalarTower.algebraMap_apply,adjoin_singleton_eq_range_aeval] at native
  obtain ⟨q,eq⟩ := native
  have diff:=Differential.deriv_aeval_eq b.gen q
  change aeval b.gen q=algebraMap A E d*x at eq
  rw [eq,Differential.deriv.leibniz,DifferentialAlgebra.deriv_algebraMap] at diff
  have eq' : algebraMap A E (d*r)*x′=
      algebraMap A E r*aeval b.gen (Differential.mapCoeffs q)+
      aeval b.gen q.derivative*(algebraMap A E r*b.gen′)-
      algebraMap A E r*(algebraMap A E d′*x) := by
    rw [map_mul]
    simp only [smul_eq_mul] at diff
    linear_combination algebraMap A E r * diff
  rw [eq']
  exact (((isIntegral_algebraMap).mul (eval_integral integral _)).add
    ((eval_integral integral _).mul (root_derivative integral f positive root))).sub
      (isIntegral_algebraMap.mul (isIntegral_algebraMap.mul hx))
theorem square_clears (b : PowerBasis F E) (integral : IsIntegral A b.gen)
    (x : E) (hx : IsIntegral A x) :
    let f:=minpoly A b.gen
    let Δ:=f.resultant f.derivative f.natDegree (f.natDegree-1)
    IsIntegral A (algebraMap A E (Δ^2)*x′) := by
  let f:=minpoly A b.gen
  let Δ:=f.resultant f.derivative f.natDegree (f.natDegree-1)
  let n:=Module.finrank F E*(Module.finrank F E-1)/2
  let s : A := (-1)^n
  let ι:=algebraMap A F
  have inj : Function.Injective ι := IsFractionRing.injective A F
  have agree : minpoly F b.gen=f.map ι := minpoly.isIntegrallyClosed_eq_field_fractions' F integral
  have pos : 0<f.natDegree := minpoly.natDegree_pos integral
  have norm : ι Δ=Algebra.norm F (aeval b.gen (minpoly F b.gen).derivative) := by
    rw [←resultant_norm b _ ((minpoly F b.gen).natDegree-1) (natDegree_derivative_le _)]
    rw [agree,derivative_map,natDegree_map_eq_of_injective inj,resultant_map_map]
  have disc : algebraMap A F (s*Δ)=Algebra.discr F b.basis := by
    rw [Algebra.discr_powerBasis_eq_norm,map_mul]
    simpa [s,n,ι] using congrArg (fun y=>(-1:F)^n*y) norm
  have raw := integral_derivative b integral f pos (minpoly.aeval A b.gen) (s*Δ) disc x hx
  have cancel : s*s=1 := by
    dsimp [s]; rw [←mul_pow]; simp
  have eq : algebraMap A E s*(algebraMap A E ((s*Δ)*Δ)*x′)=algebraMap A E (Δ^2)*x′ := by
    rw [←mul_assoc,←map_mul,show s*((s*Δ)*Δ)=(s*s)*Δ^2 by ring,cancel,one_mul]
  change IsIntegral A (algebraMap A E (Δ^2)*x′)
  rw [←eq]
  exact isIntegral_algebraMap.mul raw
end Local
theorem negative_twist {K E : Type*} [Field K] [DecidableEq (RatFunc K)] [Field E]
    [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Algebra (Polynomial K) E] [IsScalarTower (Polynomial K) (RatFunc K) E]
    [Algebra (SheetNorm.Infinity K) E] [IsScalarTower (SheetNorm.Infinity K) (RatFunc K) E]
    (x : E) (finite : IsIntegral (Polynomial K) x)
    (infty : IsIntegral (SheetNorm.Infinity K) (algebraMap (RatFunc K) E RatFunc.X*x)) : x=0 := by
  by_contra ne
  let y:=algebraMap (RatFunc K) E RatFunc.X*x
  have xn : algebraMap (RatFunc K) E (RatFunc.X : RatFunc K)≠0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc K) E).injective).mpr RatFunc.X_ne_zero
  have ni : IsIntegral (Polynomial K) (algebraMap (RatFunc K) E RatFunc.X) := by
    rw [←RatFunc.algebraMap_X,←IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap
  obtain ⟨P,pn,norm,deg⟩ := SheetNorm.polynomial_norm y (mul_ne_zero xn ne) (ni.mul finite) 0 (by simpa [y] using infty)
  obtain ⟨Q,qeq⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (RatFunc K) finite)
  have eq : P=(Polynomial.X : (Polynomial K))^Module.finrank (RatFunc K) E*Q := by
    apply IsFractionRing.injective (Polynomial K) (RatFunc K)
    change algebraMap (Polynomial K) (RatFunc K) P=algebraMap (Polynomial K) (RatFunc K) _
    rw [norm]
    simp only [y,map_mul,map_pow,RatFunc.algebraMap_X,qeq,Algebra.norm_algebraMap]
  have qn : Q≠0 := fun z=>pn (by rw [eq,z,mul_zero])
  have pos := Module.finrank_pos (R:=RatFunc K) (M:=E)
  rw [eq,natDegree_mul (pow_ne_zero _ X_ne_zero) qn,natDegree_pow,natDegree_X] at deg
  omega
#print axioms integral_derivative
#print axioms square_clears
#print axioms negative_twist
theorem pole_budget {K E : Type*} [Field K] [DecidableEq (RatFunc K)] [Field E]
    [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Algebra (Polynomial K) E] [IsScalarTower (Polynomial K) (RatFunc K) E]
    [Algebra (SheetNorm.Infinity K) E] [IsScalarTower (SheetNorm.Infinity K) (RatFunc K) E]
    (Δ : (Polynomial K)) (nz : Δ≠0) (p : ℕ) (fit : 2*Δ.natDegree<p) (v : E)
    (finite : IsIntegral (Polynomial K) (algebraMap (Polynomial K) E (Δ^2)*v))
    (atInf : IsIntegral (SheetNorm.Infinity K) ((algebraMap (RatFunc K) E RatFunc.X)^p*v)) : v=0 := by
  let a:=algebraMap (Polynomial K) (RatFunc K)
  let ι:=algebraMap (RatFunc K) E
  let D:=a (Δ^2)
  let t:=RatFunc.X (K:=K)
  let k:=p-1
  let cval:=D/t^k
  have xn : t≠0 := RatFunc.X_ne_zero
  have den : (RatFunc.inftyValuation K) (t^k)≠0 := (_root_.map_ne_zero _).mpr (pow_ne_zero _ xn)
  have atMost : (RatFunc.inftyValuation K) cval≤1 := by
    change (RatFunc.inftyValuation K) (D/t^k)≤1
    rw [map_div₀,div_le_one₀ (zero_lt_iff.mpr den)]
    have dx : (RatFunc.inftyValuation K) D=WithZero.exp ((Δ^2).natDegree : ℤ) :=
      RatFunc.inftyValuation.polynomial _ (pow_ne_zero _ nz)
    rw [dx,←zpow_natCast,RatFunc.inftyValuation.X_zpow,WithZero.exp_le_exp,natDegree_pow]
    dsimp [k]; omega
  let c : SheetNorm.Infinity K := ⟨cval,atMost⟩
  have ci : IsIntegral (SheetNorm.Infinity K) (ι cval) := by
    change IsIntegral _ (algebraMap (RatFunc K) E (algebraMap (SheetNorm.Infinity K) (RatFunc K) c))
    rw [←IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap
  have eq : ι cval*((ι t)^p*v) = ι t*(algebraMap (Polynomial K) E (Δ^2)*v) := by
    have cancel : ι cval*(ι t)^p=ι t*(ι D) := by
      change ι (D/t^k)*(ι t)^p=_
      rw [map_div₀,map_pow,show p=k+1 by dsimp [k]; omega,pow_succ]
      have tn : ι t≠0 := (map_ne_zero_iff _ ι.injective).mpr xn
      field_simp [tn]
    rw [←mul_assoc,cancel,mul_assoc]
    rw [show ι D=algebraMap (Polynomial K) E (Δ^2) from (IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) E _).symm]
  have zero := negative_twist _ finite (eq ▸ ci.mul atInf)
  exact (mul_eq_zero.mp zero).resolve_left ((map_ne_zero_iff _
    ((IsScalarTower.algebraMap_eq (Polynomial K) (RatFunc K) E) ▸
      ι.injective.comp (IsFractionRing.injective (Polynomial K) (RatFunc K)))).mpr (pow_ne_zero _ nz))
#print axioms pole_budget
private def rawDegree (e : ℕ) :=
  let m:=e+1
  let H:=164650*(10*(2*e)*(2*e+1)-9*m*(m-1))/(18*m)
  (2*e-2)*H-e*(e-1)*164650
theorem profile_room :
    (∀ e : Fin 48,3≤e.val → 2*rawDegree e.val≤1707353296) ∧
    rawDegree 47=853676648 ∧ 1707353296+423353137=K1.p := by decide +kernel
theorem coarse_room : ∀ e : Fin 48,3≤e.val →
    2*((e.val-1)*(3*e.val-2)*164650+(e.val-1))≤2105544292 ∧
    2105544292+25162141=K1.p := by decide +kernel
#print axioms profile_room
end Lower6960.DifferentialPoles

end
end Merged_R6960DifferentialPoles

-- merged module R6960MonicChartReverse
section Merged_R6960MonicChartReverse
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2400000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial
section Euler
variable {R : Type*} [CommRing R]
private theorem coeff_mul_X_derivative (f : (Polynomial R)) (i : ℕ) :
    (Polynomial.X*f.derivative).coeff i=f.coeff i*(i:R) := by
  cases i with
  | zero => simp
  | succ i => rw [coeff_X_mul,coeff_derivative,Nat.cast_succ]
theorem reflect_derivative (f : (Polynomial R)) (e : ℕ) (he : 0<e) (bound : f.natDegree≤e) :
    Polynomial.X*(f.reflect e).derivative =
      C (e:R)*f.reflect e-f.derivative.reflect (e-1) := by
  ext i
  rw [coeff_mul_X_derivative,coeff_sub,coeff_C_mul,coeff_reflect,coeff_reflect,
    coeff_derivative]
  by_cases fit : i<e
  · have b₁ : i≤e := fit.le
    have b₂ : i≤e-1 := by omega
    rw [revAt_le b₁,revAt_le b₂]
    have eq : e-1-i+1=e-i := by omega
    rw [eq]
    have scalar : (((e-1-i : ℕ) : R) + 1) = ((e-i : ℕ):R) := by
      simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun n : ℕ => (n:R)) eq
    rw [scalar,Nat.cast_sub b₁]
    ring
  · have ld : e ≤ i := Nat.le_of_not_gt fit
    rw [revAt_eq_self_of_lt (show e - 1 < i from by omega),
      coeff_eq_zero_of_natDegree_lt (bound.trans_lt (by omega : e < i+1)),zero_mul,sub_zero]
    rcases eq_or_lt_of_le ld with rfl | lt
    · ring
    · rw [revAt_eq_self_of_lt lt,coeff_eq_zero_of_natDegree_lt (bound.trans_lt lt),mul_zero,zero_mul]
end Euler
section Basic
variable {A : Type*} [CommRing A] [IsDomain A]
def equation (f : (Polynomial A)) (c : A) (u : Aˣ) : (Polynomial A) :=
  C ((↑u⁻¹ : A))*(f.taylor c).reverse
theorem equation_degree (f : (Polynomial A)) (c : A) (u : Aˣ) (hu : f.eval c=(u:A)) :
    (equation f c u).natDegree=f.natDegree := by
  have nn : (f.taylor c).coeff 0≠0 := by rw [taylor_coeff_zero,hu]; exact u.ne_zero
  rw [equation,natDegree_C_mul (Units.ne_zero _),reverse_natDegree,
    natTrailingDegree_eq_zero.mpr (Or.inr nn),Nat.sub_zero,natDegree_taylor]
theorem equation_monic (f : (Polynomial A)) (c : A) (u : Aˣ) (hu : f.eval c=(u:A)) :
    (equation f c u).Monic := by
  have nn : (f.taylor c).coeff 0≠0 := by rw [taylor_coeff_zero,hu]; exact u.ne_zero
  unfold Monic equation
  rw [leadingCoeff_mul,leadingCoeff_C,reverse_leadingCoeff,trailingCoeff_eq_coeff_zero nn,
    taylor_coeff_zero,hu,Units.inv_mul]
theorem equation_coeff_zero (f : (Polynomial A)) (c : A) (u : Aˣ) :
    (equation f c u).coeff 0=(↑u⁻¹:A)*f.leadingCoeff := by
  rw [equation,coeff_C_mul,coeff_zero_reverse,leadingCoeff_taylor]
end Basic
section Evaluation
variable {A E : Type*} [CommRing A] [IsDomain A] [Field E]
private theorem taylor_root_eval (i : A→+*E) (f : (Polynomial A)) (c : A) (α : E) :
    (f.taylor c).eval₂ i (α-i c)=f.eval₂ i α := by
  rw [taylor_apply,eval₂_comp,eval₂_add,eval₂_X,eval₂_C,sub_add_cancel]
private theorem derivative_taylor (f : (Polynomial A)) (c : A) :
    (f.taylor c).derivative=f.derivative.taylor c := by
  simp [taylor_apply,derivative_comp]
theorem sub_ne_at_root (i : A→+*E) {f : (Polynomial A)} {c : A} {u : Aˣ}
    (hu : f.eval c=(u:A)) {α : E} (root : f.eval₂ i α=0) : α-i c≠0 := by
  intro h
  have e : α=i c := sub_eq_zero.mp h
  rw [e,eval₂_at_apply,hu] at root
  exact (u.isUnit.map i).ne_zero root
theorem equation_root (i : A→+*E) (f : (Polynomial A)) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) {α : E} (root : f.eval₂ i α=0) :
    (equation f c u).eval₂ i (α-i c)⁻¹=0 := by
  let w := α-i c
  have wn : w≠0 := sub_ne_at_root i hu root
  letI : Invertible w := invertibleOfNonzero wn
  have eq : (f.taylor c).eval₂ i w=0 := (taylor_root_eval i f c α).trans root
  have go := (eval₂_reverse_eq_zero_iff i w (f.taylor c)).mpr eq
  rw [invOf_eq_inv] at go
  rw [equation,eval₂_mul,eval₂_C,go,mul_zero]
theorem equation_derivative (i : A→+*E) (f : (Polynomial A)) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) (degree : 2≤f.natDegree)
    {α : E} (root : f.eval₂ i α=0) :
    f.derivative.eval₂ i α*((α-i c)⁻¹)^(f.natDegree-2)=
      -(i (u:A))*((equation f c u).derivative.eval₂ i (α-i c)⁻¹) := by
  let w := α-i c
  let β := w⁻¹
  let p := f.taylor c
  let e := f.natDegree
  have wn : w≠0 := sub_ne_at_root i hu root
  have bne : β≠0 := inv_ne_zero wn
  letI : Invertible w := invertibleOfNonzero wn
  have rdegree : p.natDegree=e := natDegree_taylor f c
  have reverse_eq : p.reflect e=p.reverse := by rw [reverse,rdegree]
  have hroot := (eval₂_reverse_eq_zero_iff i w p).mpr ((taylor_root_eval i f c α).trans root)
  rw [invOf_eq_inv] at hroot
  have hroot' : p.reverse.eval₂ i β=0 := hroot
  have exp := reflect_derivative p e (by omega) rdegree.le
  have hom := congrArg (eval₂RingHom i β) exp
  simp only [map_mul,map_sub,coe_eval₂RingHom,eval₂_X,eval₂_C,reverse_eq,hroot',mul_zero,zero_sub] at hom
  have reverse_d : (p.derivative.reflect (e-1)).eval₂ i β * w^(e-1)=f.derivative.eval₂ i α := by
    have h := eval₂_reflect_mul_pow i w (e-1) p.derivative
      ((natDegree_derivative_le p).trans_eq (by rw [rdegree]))
    rw [invOf_eq_inv,derivative_taylor,taylor_root_eval] at h
    simpa only [β,p,derivative_taylor] using h
  have evalD : (p.reverse.derivative).eval₂ i β =
      -(f.derivative.eval₂ i α*β^(e-2)) := by
    have step : (p.derivative.reflect (e-1)).eval₂ i β=f.derivative.eval₂ i α*β^(e-1) := by
      apply mul_right_cancel₀ (pow_ne_zero _ wn)
      rw [reverse_d,mul_assoc,← mul_pow,inv_mul_cancel₀ wn,one_pow,mul_one]
    apply mul_left_cancel₀ bne
    rw [hom,step,show e-1=(e-2)+1 by omega,pow_succ]
    ring
  change f.derivative.eval₂ i α*β^(e-2)=-i (u:A)*(equation f c u).derivative.eval₂ i β
  rw [equation,derivative_C_mul,eval₂_mul,eval₂_C,show (f.taylor c).reverse=p.reverse from rfl,
    evalD]
  have cancel : i (u:A)*i ((↑u⁻¹:A))=1 := by rw [← map_mul,Units.mul_inv,map_one]
  calc
    _ = (i (u:A)*i ((↑u⁻¹:A)))*(f.derivative.eval₂ i α*β^(e-2)) := by rw [cancel,one_mul]
    _ = _ := by ring
#print axioms reflect_derivative
#print axioms equation_derivative
end Evaluation
end
end Lower6960.MonicChart

end Merged_R6960MonicChartReverse

-- merged module R6960MonicChartBasis
section Merged_R6960MonicChartBasis

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2200000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial

section Basis

variable {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E]

abbrev reciprocal (b : PowerBasis F E) (c : A) : E :=
  (b.gen-algebraMap A E c)⁻¹

private theorem reciprocal_generates (b : PowerBasis F E) (c : A) :
    IntermediateField.adjoin F ({reciprocal b c} : Set E)=⊤ := by
  let K := IntermediateField.adjoin F ({reciprocal b c} : Set E)
  have rb : reciprocal b c∈K := IntermediateField.subset_adjoin F _ (Set.mem_singleton _)
  have off : algebraMap A E c∈K := by
    rw [IsScalarTower.algebraMap_apply A F E]
    exact K.algebraMap_mem _
  have eq : (reciprocal b c)⁻¹+algebraMap A E c=b.gen := by
    simp [reciprocal]
  have gen : b.gen∈K := eq ▸ K.add_mem (K.inv_mem rb) off
  have le : Algebra.adjoin F ({b.gen} : Set E) ≤ K.toSubalgebra := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact gen
  rw [b.adjoin_gen_eq_top] at le
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.top_toSubalgebra]
  exact le_antisymm le_top le

/-- The reciprocal generator gives a power basis for the original root
field, with the transformed integral equation as its minimal polynomial. -/
theorem chart_basis (b : PowerBasis F E) (f : (Polynomial A)) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) (degree : f.natDegree=b.dim) (root : aeval b.gen f=0) :
    ∃ v : PowerBasis F E, v.gen=reciprocal b c ∧
      IsIntegral A v.gen ∧ minpoly A v.gen=equation f c u := by
  let s := IntermediateField.adjoin F ({reciprocal b c} : Set E)
  let β := reciprocal b c
  have root' : aeval β (equation f c u)=0 :=
    equation_root (algebraMap A E) f c u hu root
  have monic := equation_monic f c u hu
  have hA : IsIntegral A β := ⟨equation f c u,monic,root'⟩
  letI : FiniteDimensional F E := b.finite
  let e : s ≃ₐ[F] E :=
    (IntermediateField.equivOfEq (reciprocal_generates b c)).trans IntermediateField.topEquiv
  let v : PowerBasis F E :=
    (IntermediateField.adjoin.powerBasis (K:=F) (x:=β) (Algebra.IsIntegral.isIntegral β)).map e
  have vg : v.gen=β := rfl
  have integ : IsIntegral A v.gen := vg.symm ▸ hA
  have dimension : v.dim=b.dim := v.finrank.symm.trans b.finrank
  let j := algebraMap A F
  have ji : Function.Injective j := IsFractionRing.injective _ _
  let g := (equation f c u).map j
  have gm : g.Monic := monic.map j
  have rootF : aeval v.gen g=0 := by
    rw [aeval_map_algebraMap,vg]
    exact root'
  have gdeg : g.natDegree=v.dim := by
    rw [natDegree_map_eq_of_injective ji,equation_degree f c u hu,degree,dimension]
  have equal : g=minpoly F v.gen := by
    apply minpoly.unique_of_degree_le_degree_minpoly F v.gen gm rootF
    rw [degree_eq_natDegree gm.ne_zero,degree_eq_natDegree (minpoly.ne_zero v.isIntegral_gen),
      gdeg,v.natDegree_minpoly]
  refine ⟨v,vg,integ,?_⟩
  apply Polynomial.map_injective _ ji
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' F integ]
  exact equal.symm

theorem original_equation (b : PowerBasis F E) (f : (Polynomial A))
    (degree : f.natDegree=b.dim) (positive : 0<f.natDegree) (root : aeval b.gen f=0) :
    f.map (algebraMap A F)=C (algebraMap A F f.leadingCoeff)*minpoly F b.gen := by
  let j := algebraMap A F
  have ji : Function.Injective j := IsFractionRing.injective _ _
  have positive' : f≠0 := by rintro rfl; simp at positive
  let P := f.map j
  let l := j f.leadingCoeff
  have ln : l≠0 := (map_ne_zero_iff _ ji).mpr (leadingCoeff_ne_zero.mpr positive')
  let g := C l⁻¹*P
  have monic : g.Monic := by
    unfold Monic g P
    rw [leadingCoeff_mul,leadingCoeff_C,leadingCoeff_map_of_injective ji]
    exact inv_mul_cancel₀ ln
  have rooted : aeval b.gen g=0 := by
    rw [map_mul,show P=f.map j from rfl,aeval_map_algebraMap,root,mul_zero]
  have gdeg : g.natDegree=b.dim := by
    rw [natDegree_C_mul (inv_ne_zero ln),natDegree_map_eq_of_injective ji,degree]
  have minimal : g=minpoly F b.gen := by
    apply minpoly.unique_of_degree_le_degree_minpoly F b.gen monic rooted
    rw [degree_eq_natDegree monic.ne_zero,degree_eq_natDegree (minpoly.ne_zero b.isIntegral_gen),
      gdeg,b.natDegree_minpoly]
  rw [← minimal]
  change P=C l*(C l⁻¹*P)
  rw [← mul_assoc,← C_mul,mul_inv_cancel₀ ln,C_1,one_mul]

#print axioms chart_basis
end Basis
end
end Lower6960.MonicChart

end Merged_R6960MonicChartBasis

-- merged module R6960MonicChartClearing
section Merged_R6960MonicChartClearing
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra Module
open scoped Polynomial Differential
open Lower6960.DifferentialPoles (resultant_norm)
section Comparison
variable {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Algebra.IsSeparable F E] [FiniteDimensional F E]
private theorem original_norm (b : PowerBasis F E) (f : (Polynomial A))
    (degree : f.natDegree=b.dim) (positive : 0<f.natDegree) (root : aeval b.gen f=0) :
    algebraMap A F (f.resultant f.derivative f.natDegree (f.natDegree-1))=
    (algebraMap A F f.leadingCoeff)^(f.natDegree-1)*Algebra.norm F (aeval b.gen f.derivative) := by
  let j := algebraMap A F
  let D := f.derivative.map j
  have bounded : D.natDegree≤f.natDegree-1 := natDegree_map_le.trans (natDegree_derivative_le _)
  have N := Lower6960.DifferentialPoles.resultant_norm b D (f.natDegree-1) bounded
  rw [b.natDegree_minpoly,← degree] at N
  show j (f.resultant f.derivative f.natDegree (f.natDegree-1))=_
  rw [← resultant_map_map,original_equation b f degree positive root,resultant_C_mul_left]
  change _*resultant (minpoly F b.gen) D f.natDegree (f.natDegree-1)=_
  rw [N,aeval_map_algebraMap]
private theorem monic_norm (v : PowerBasis F E) (g : (Polynomial A))
    (integral : IsIntegral A v.gen) (poly : minpoly A v.gen=g) :
    algebraMap A F (g.resultant g.derivative g.natDegree (g.natDegree-1))=
      Algebra.norm F (aeval v.gen g.derivative) := by
  let j := algebraMap A F
  have ji : Function.Injective j := IsFractionRing.injective A F
  have field : minpoly F v.gen=g.map j := by rw [←poly]; exact minpoly.isIntegrallyClosed_eq_field_fractions' F integral
  have N := Lower6960.DifferentialPoles.resultant_norm v (g.derivative.map j) (g.natDegree-1)
    (natDegree_map_le.trans (natDegree_derivative_le _))
  rw [field,natDegree_map_eq_of_injective ji,resultant_map_map,aeval_map_algebraMap] at N
  exact N
private theorem chart_scaling {K : Type*} [Field K] (e : ℕ) (he : 2≤e)
    (l u D G : K) (un : u≠0)
    (identity : D*((-1)^e*(u⁻¹*l))^(e-2)=(-u)^e*G) :
    l^(e-1)*D=l*u^(2*e-2)*G := by
  let k := e-2
  let s : K := (-1)^e
  have h₁ : e-1=k+1 := by dsimp [k]; omega
  have h₂ : e+k=2*e-2 := by dsimp [k]; omega
  have signsquare : s*s=1 := by
    dsimp [s]
    rw [← mul_pow,neg_mul_neg,one_mul,one_pow]
  have sign : s^(k+1)=1 := by
    dsimp [s]
    rw [← pow_mul,← h₁]
    exact (Nat.even_mul_pred_self e).neg_one_pow
  have single : (s*u)*(s*(u⁻¹*l))=l := by
    calc
      _ = (s*s)*(u*u⁻¹)*l := by ring
      _ = _ := by rw [signsquare,mul_inv_cancel₀ un,one_mul,one_mul]
  have scaled := congrArg (fun v : K => (l*(s*u)^k)*v) identity
  change (l*(s*u)^k)*(D*(s*(u⁻¹*l))^k)=(l*(s*u)^k)*((-u)^e*G) at scaled
  calc
    l^(e-1)*D = (l*(s*u)^k)*(D*(s*(u⁻¹*l))^k) := by
      calc
        _ = l*D*((s*u)*(s*(u⁻¹*l)))^k := by rw [single,h₁,pow_succ]; ring
        _ = _ := by rw [mul_pow]; ring
    _ = (l*(s*u)^k)*((-u)^e*G) := scaled
    _ = l*(s^(k+1))*u^(e+k)*G := by
      rw [neg_pow,mul_pow,pow_succ,pow_add]
      change l*(s^k*u^k)*(s*u^e*G)=_
      ring
    _ = _ := by rw [sign,h₂,mul_one]
theorem resultant_eq_chart (b : PowerBasis F E) (f : (Polynomial A)) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) (degree : f.natDegree=b.dim) (positive : 2≤f.natDegree)
    (root : aeval b.gen f=0) :
    f.resultant f.derivative f.natDegree (f.natDegree-1)=
      f.leadingCoeff*(u:A)^(2*f.natDegree-2)*
        (equation f c u).resultant (equation f c u).derivative
          (equation f c u).natDegree ((equation f c u).natDegree-1) := by
  obtain ⟨v,vg,integral,minimal⟩ := chart_basis b f c u hu degree root
  let g := equation f c u
  let j := algebraMap A F
  let i := algebraMap A E
  let e := f.natDegree
  let l := j f.leadingCoeff
  let a := j (u:A)
  have an : a≠0 := (u.isUnit.map j).ne_zero
  have dim : Module.finrank F E=e := b.finrank.trans degree.symm
  have vd : v.dim=e := v.finrank.symm.trans dim
  have gi : minpoly F v.gen=g.map j := by
    change minpoly F v.gen=(equation f c u).map j
    rw [←minimal]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' F integral
  have uj : j (↑u⁻¹:A)=a⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul,Units.inv_mul,map_one]
  have norm_v : Algebra.norm F v.gen=(-1)^e*(a⁻¹*l) := by
    rw [v.norm_gen_eq_coeff_zero_minpoly,vd,gi,coeff_map,equation_coeff_zero,map_mul,uj]
  have derivative : aeval b.gen f.derivative*v.gen^(e-2)=(-i (u:A))*aeval v.gen g.derivative := by
    rw [vg]
    exact equation_derivative i f c u hu positive root
  have norm_deriv := congrArg (Algebra.norm F) derivative
  have nu : Algebra.norm F (-i (u:A))=(-a)^e := by
    rw [IsScalarTower.algebraMap_apply A F E,←map_neg,Algebra.norm_algebraMap,dim]
  simp only [map_mul,map_pow,norm_v,nu] at norm_deriv
  have scale := chart_scaling e positive l a _ _ an norm_deriv
  apply IsFractionRing.injective A F
  rw [original_norm b f degree (by omega) root,map_mul,map_mul,map_pow,
    monic_norm v g integral minimal]
  exact scale
theorem chart_resultant_dvd (b : PowerBasis F E) (f : (Polynomial A)) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) (degree : f.natDegree=b.dim) (positive : 2≤f.natDegree)
    (root : aeval b.gen f=0) :
    (equation f c u).resultant (equation f c u).derivative
      (equation f c u).natDegree ((equation f c u).natDegree-1) ∣
      f.resultant f.derivative f.natDegree (f.natDegree-1) := by
  refine ⟨f.leadingCoeff*(u:A)^(2*f.natDegree-2),?_⟩
  rw [resultant_eq_chart b f c u hu degree positive root,mul_comm]
theorem discriminant_dvd (b : PowerBasis F E) (f : (Polynomial A)) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) (degree : f.natDegree=b.dim) (positive : 2≤f.natDegree)
    (root : aeval b.gen f=0) :
    ∃ (v : PowerBasis F E) (d : A), v.gen=reciprocal b c ∧ IsIntegral A v.gen ∧
      algebraMap A F d=Algebra.discr F v.basis ∧
      d∣f.resultant f.derivative f.natDegree (f.natDegree-1) := by
  obtain ⟨v,gen,integral,minimal⟩ := chart_basis b f c u hu degree root
  let g := equation f c u
  let r := g.resultant g.derivative g.natDegree (g.natDegree-1)
  let n := Module.finrank F E*(Module.finrank F E-1)/2
  let s : A := (-1)^n
  have sz : IsUnit s := (isUnit_one.neg).pow _
  have repr : algebraMap A F (s*r)=Algebra.discr F v.basis := by
    rw [Algebra.discr_powerBasis_eq_norm,map_mul,monic_norm v g integral minimal]
    simp only [s,n,map_pow,map_neg,map_one]
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F integral,minimal,derivative_map,
      aeval_map_algebraMap]
  refine ⟨v,s*r,gen,integral,repr,?_⟩
  exact (sz.mul_left_dvd.mpr dvd_rfl).trans (chart_resultant_dvd b f c u hu degree positive root)
section Differential
variable [Differential A] [Differential E] [DifferentialAlgebra A E]
theorem raw_square_clears (b : PowerBasis F E) (f : (Polynomial A)) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) (degree : f.natDegree=b.dim) (positive : 2≤f.natDegree)
    (root : aeval b.gen f=0) (x : E) (hx : IsIntegral A x) :
    IsIntegral A (algebraMap A E ((f.resultant f.derivative f.natDegree (f.natDegree-1))^2)*x′) := by
  obtain ⟨v,gen,integral,minimal⟩ := chart_basis b f c u hu degree root
  have native := DifferentialPoles.square_clears v integral x hx
  change IsIntegral A (algebraMap A E (((minpoly A v.gen).resultant (minpoly A v.gen).derivative
    (minpoly A v.gen).natDegree ((minpoly A v.gen).natDegree-1))^2)*x′) at native
  rw [minimal] at native
  obtain ⟨a,ha⟩ := chart_resultant_dvd b f c u hu degree positive root
  rw [ha,mul_pow,map_mul,mul_right_comm]
  exact native.mul (isIntegral_algebraMap (x:=a^2))
end Differential
#print axioms resultant_eq_chart
#print axioms discriminant_dvd
#print axioms raw_square_clears
end Comparison
end
end Lower6960.MonicChart

end Merged_R6960MonicChartClearing

-- merged module R6960MonicChartLocal
section Merged_R6960MonicChartLocal
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2200000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial Differential
theorem exists_unit_evaluation {A : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] (f : (Polynomial A))
    (primitive : ∃ i, IsUnit (f.coeff i)) : ∃ c : A, IsUnit (f.eval c) := by
  let residue := IsLocalRing.residue A
  by_contra! no
  have all (x : IsLocalRing.ResidueField A) : (f.map residue).IsRoot x := by
    obtain ⟨c,rfl⟩ := IsLocalRing.residue_surjective (R:=A) x
    change (f.map residue).eval (residue c)=0
    rw [eval_map_apply]
    exact not_ne_iff.mp (fun h => no c ((IsLocalRing.residue_ne_zero_iff_isUnit (f.eval c)).mp h))
  have zero : f.map residue=0 := by
    apply eq_zero_of_infinite_isRoot
    simpa only [all, Set.setOf_true] using
      (Set.infinite_univ : (Set.univ : Set (IsLocalRing.ResidueField A)).Infinite)
  obtain ⟨i,h⟩ := primitive
  have eq := congrArg (fun p : (Polynomial (IsLocalRing.ResidueField A)) => p.coeff i) zero
  rw [coeff_map,coeff_zero] at eq
  exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr h) eq
theorem raw_square_clears_local {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Algebra.IsSeparable F E] [FiniteDimensional F E]
    [Differential A] [Differential E] [DifferentialAlgebra A E]
    (b : PowerBasis F E) (f : (Polynomial A)) (primitive : ∃ i,IsUnit (f.coeff i))
    (degree : f.natDegree=b.dim) (positive : 2≤f.natDegree) (root : aeval b.gen f=0)
    (x : E) (hx : IsIntegral A x) :
    IsIntegral A (algebraMap A E ((f.resultant f.derivative f.natDegree (f.natDegree-1))^2)*x′) := by
  obtain ⟨c,u,h⟩ := exists_unit_evaluation f primitive
  exact raw_square_clears b f c u h.symm degree positive root x hx
#print axioms exists_unit_evaluation
#print axioms raw_square_clears_local
end
end Lower6960.MonicChart

end Merged_R6960MonicChartLocal

-- merged module R6960MonicChartScaled
section Merged_R6960MonicChartScaled
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2900000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial Differential
abbrev paddedRes {A : Type*} [CommRing A] (f : (Polynomial A)) : A :=
  f.resultant f.derivative f.natDegree (f.natDegree-1)
theorem derivative_degree {R : Type*} [CommRing R] [NoZeroDivisors R] (f : (Polynomial R))
    (pos : 0<f.natDegree) (tame : (f.natDegree:R)≠0) :
    f.derivative.natDegree=f.natDegree-1 := by
  have e : f.natDegree-1+1=f.natDegree := Nat.sub_add_cancel pos
  apply le_antisymm (natDegree_derivative_le _)
  apply le_natDegree_of_ne_zero
  rw [coeff_derivative,←Nat.cast_add_one,e,coeff_natDegree]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr (fun h=>by rw [h,natDegree_zero] at pos; omega)) tame
theorem scaleRoots_derivative {R : Type*} [CommRing R] (f : (Polynomial R)) (r : R)
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
def scaled (f : (Polynomial A)) (c : A) : (Polynomial A) := (f.taylor c).reverse.integralNormalization
private theorem reversed_lead (f : (Polynomial A)) (c : A) (un : f.eval c≠0) :
    (f.taylor c).reverse.leadingCoeff=f.eval c := by
  have co : (f.taylor c).coeff 0≠0 := by rwa [taylor_coeff_zero]
  rw [reverse_leadingCoeff,trailingCoeff_eq_coeff_zero co,taylor_coeff_zero]
theorem scaled_degree (f : (Polynomial A)) (c : A) (un : f.eval c≠0) :
    (scaled f c).natDegree=f.natDegree := by
  have co : (f.taylor c).coeff 0≠0 := by rwa [taylor_coeff_zero]
  rw [scaled,natDegree_integralNormalization,reverse_natDegree,
    natTrailingDegree_eq_zero.mpr (Or.inr co),Nat.sub_zero,natDegree_taylor]
private theorem scaled_basis (b : PowerBasis F E) (f : (Polynomial A)) (c : A)
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
    (inj : Function.Injective j) (f : (Polynomial A)) : f.reverse.map j=(f.map j).reverse := by
  rw [reverse,reverse,reflect_map,natDegree_map_eq_of_injective inj]
theorem scaled_resultant_eq (b : PowerBasis F E) (f : (Polynomial A)) (c : A)
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
theorem scaled_raw_square_clears (b : PowerBasis F E) (f : (Polynomial A)) (c : A)
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

end Merged_R6960MonicChartScaled

-- merged module R6960MonicChartInfinityPolynomial
section Merged_R6960MonicChartInfinityPolynomial
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 3100000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial BigOperators
variable {K : Type*} [Field K]
abbrev AtInfinity (K : Type*) [Field K] : (Polynomial K)→+*RatFunc K :=
  (aeval ((RatFunc.X : RatFunc K)⁻¹)).toRingHom
theorem atInfinity_injective : Function.Injective (AtInfinity K) := by
  have tx := RatFunc.transcendental_X (K:=K)
  have ti : Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := by
    simpa only [Transcendental,IsAlgebraic.inv_iff] using tx
  exact transcendental_iff_injective.mp ti
theorem reverse_atInfinity (g : (Polynomial K)) (n : ℕ) (ng : g.natDegree≤n) :
    AtInfinity K (g.reflect n) =
      algebraMap (Polynomial K) (RatFunc K) g*((RatFunc.X : RatFunc K)⁻¹)^n := by
  let x : RatFunc K := RatFunc.X
  have xn : x≠0 := RatFunc.X_ne_zero
  letI : Invertible x := invertibleOfNonzero xn
  have h := eval₂_reflect_mul_pow (algebraMap K (RatFunc K)) x n g ng
  have evalX : g.eval₂ (algebraMap K (RatFunc K)) x=algebraMap (Polynomial K) (RatFunc K) g :=
    RatFunc.aeval_X_left_eq_algebraMap g
  rw [invOf_eq_inv,evalX] at h
  apply mul_right_cancel₀ (pow_ne_zero _ xn)
  change (g.reflect n).eval₂ (algebraMap K (RatFunc K)) x⁻¹*x^n=_
  rw [h,mul_assoc,←mul_pow,inv_mul_cancel₀ xn,one_pow,mul_one]
def weightedInfinity (f : (Polynomial (Polynomial K))) (H d : ℕ) : (Polynomial (Polynomial K)) :=
  ∑ i∈f.support, monomial i ((f.coeff i).reflect (H-d*i))
theorem coeff_weightedInfinity (f : (Polynomial (Polynomial K))) (H d i : ℕ) :
    (weightedInfinity f H d).coeff i=(f.coeff i).reflect (H-d*i) := by
  classical
  by_cases mem : i∈f.support
  · rw [weightedInfinity,Polynomial.finsetSum_coeff,Finset.sum_eq_single_of_mem i mem]
    · simp
    · intro j _ neq; simp [coeff_monomial,neq]
  · rw [weightedInfinity,Polynomial.finsetSum_coeff,notMem_support_iff.mp mem,Polynomial.reflect_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : j ≠ i := fun h => mem (h ▸ hj)
    simp [Polynomial.coeff_monomial, hj']
theorem infinity_degree (f : (Polynomial (Polynomial K))) (H d : ℕ) : (weightedInfinity f H d).natDegree=f.natDegree := by
  by_cases fn : f=0
  · simp [fn,weightedInfinity]
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_weightedInfinity,coeff_eq_zero_of_natDegree_lt hj,reflect_zero]
  · apply le_natDegree_of_ne_zero
    rw [coeff_weightedInfinity,coeff_natDegree]
    intro zero
    let b := f.leadingCoeff
    have nz : b≠0 := leadingCoeff_ne_zero.mpr fn
    apply nz
    apply Polynomial.ext
    intro j
    have req := congrArg (fun q : (Polynomial K) => q.coeff (revAt (H-d*f.natDegree) j)) zero
    simp only [coeff_reflect,revAt_invol,coeff_zero] at req
    exact req
theorem infinity_leading (f : (Polynomial (Polynomial K))) (H d : ℕ) :
    (weightedInfinity f H d).leadingCoeff=f.leadingCoeff.reflect (H-d*f.natDegree) := by
  rw [leadingCoeff,infinity_degree,coeff_weightedInfinity,coeff_natDegree]
theorem infinity_field (f : (Polynomial (Polynomial K))) (H d : ℕ)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H) :
    (weightedInfinity f H d).map (AtInfinity K)=
      C (((RatFunc.X : RatFunc K)⁻¹)^(H-d*f.natDegree))*
        ((f.map (algebraMap (Polynomial K) (RatFunc K))).scaleRoots (((RatFunc.X : RatFunc K)⁻¹)^d)) := by
  let j := algebraMap (Polynomial K) (RatFunc K)
  let t := ((RatFunc.X : RatFunc K)⁻¹)
  let e := f.natDegree
  have hf : (f.map j).natDegree=e := natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _
  have de : d*e ≤ H := (Nat.le_add_left ..).trans (weights _ le_rfl)
  apply Polynomial.ext
  intro i
  rw [coeff_map,coeff_weightedInfinity,coeff_C_mul,coeff_scaleRoots,coeff_map,hf]
  change AtInfinity K ((f.coeff i).reflect (H-d*i))=t^(H-d*e)*(j (f.coeff i)*(t^d)^(e-i))
  by_cases small : i≤e
  · have hi := weights i small
    have eq : H-d*i=(H-d*e)+d*(e-i) := by
      have hd : d*(e-i)+d*i=d*e := by rw [← Nat.mul_add,Nat.sub_add_cancel small]
      omega
    rw [reverse_atInfinity _ _ (by omega),eq,pow_add,pow_mul]
    ring
  · have large : f.natDegree < i := Nat.lt_of_not_ge small
    rw [coeff_eq_zero_of_natDegree_lt large,reflect_zero,map_zero,map_zero,zero_mul,mul_zero]
def resultantWidth (e H d : ℕ) : ℕ :=
  (H-d*e)*(e+(e-1))+d*(e*(e-1))
theorem resultantWidth_eq {e H d : ℕ} (pos : 0<e) (fit : d*e≤H) :
    resultantWidth e H d+d*e^2=(2*e-1)*H := by
  let a := H-d*e
  have eqH : H=a+d*e := (Nat.sub_add_cancel fit).symm
  obtain ⟨k,eq⟩ := Nat.exists_eq_add_of_le (show 1≤e from pos)
  unfold resultantWidth
  change a*(e+(e-1))+d*(e*(e-1))+d*e^2=(2*e-1)*H
  rw [eqH,eq,show 1+k-1=k by omega,show 2*(1+k)-1=2*k+1 by omega]
  ring
theorem infinity_resultant (f : (Polynomial (Polynomial K))) (H d : ℕ) (pos : 0<f.natDegree)
    (tame : (f.natDegree:K)≠0)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (resBound : (paddedRes f).natDegree≤resultantWidth f.natDegree H d) :
    paddedRes (weightedInfinity f H d)=
      (paddedRes f).reflect (resultantWidth f.natDegree H d) := by
  let e := f.natDegree
  let t := ((RatFunc.X : RatFunc K)⁻¹)
  let j := algebraMap (Polynomial K) (RatFunc K)
  let g := weightedInfinity f H d
  let P := f.map j
  have pdeg : P.natDegree=e := natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _
  have tn : t≠0 := inv_ne_zero RatFunc.X_ne_zero
  have etame : (e : RatFunc K)≠0 := by
    simpa only [map_natCast,e] using
      (map_ne_zero_iff (algebraMap K (RatFunc K)) (algebraMap K (RatFunc K)).injective).mpr tame
  have pder : P.derivative.natDegree=P.natDegree-1 := derivative_degree P
    (pdeg ▸ pos) (pdeg ▸ etame)
  have fromFinite : j (paddedRes f)=P.resultant P.derivative e (e-1) := by
    unfold paddedRes
    rw [←resultant_map_map,←derivative_map]
  have power := resultant_scaleRoots P P.derivative (t^d)
  have scale : (P.scaleRoots (t^d)).resultant (P.derivative.scaleRoots (t^d)) e (e-1)=
      t^(d*(e*(e-1)))*j (paddedRes f) := by
    rw [natDegree_scaleRoots,natDegree_scaleRoots,pder,pdeg,←pow_mul,←fromFinite] at power
    exact power
  apply atInfinity_injective (K:=K)
  change AtInfinity K (paddedRes g)=_
  rw [reverse_atInfinity _ _ resBound]
  change AtInfinity K (g.resultant g.derivative g.natDegree (g.natDegree-1))=_
  rw [←resultant_map_map,←derivative_map,infinity_degree,
    infinity_field f H d weights,derivative_C_mul,scaleRoots_derivative _ _ pder,
    resultant_C_mul_left,resultant_C_mul_right]
  change (t^(H-d*e))^(e-1)*((t^(H-d*e))^e*
      (P.scaleRoots (t^d)).resultant (P.derivative.scaleRoots (t^d)) e (e-1))=_
  rw [scale,←mul_assoc,←pow_add,←pow_mul,←mul_assoc,←pow_add]
  unfold resultantWidth
  ring
#print axioms infinity_resultant
end
end Lower6960.MonicChart

end Merged_R6960MonicChartInfinityPolynomial

-- merged module R6960MonicChartInfinityRing
section Merged_R6960MonicChartInfinityRing
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2700000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial
variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
abbrev Infinity (K : Type*) [Field K] [DecidableEq (RatFunc K)] := SheetNorm.Infinity K
private theorem valuation_reciprocal_pow (n : ℕ) :
    RatFunc.inftyValuation K (((RatFunc.X : RatFunc K)⁻¹)^n)=WithZero.exp (-(n:ℤ)) := by
  rw [show ((RatFunc.X : RatFunc K)⁻¹)^n=RatFunc.X^(-(n:ℤ)) by rw [zpow_neg,zpow_natCast,inv_pow],
    RatFunc.inftyValuation.X_zpow]
private theorem invert_poly (p : (Polynomial K)) :
    AtInfinity K p=algebraMap (Polynomial K) (RatFunc K) p.reverse * ((RatFunc.X : RatFunc K)⁻¹)^p.natDegree := by
  have reflect_twice : p.reverse.reflect p.natDegree=p := by
    apply Polynomial.ext
    intro i
    rw [coeff_reflect,coeff_reverse,revAt_invol]
  have eq := reverse_atInfinity p.reverse p.natDegree (reverse_natDegree_le p)
  rwa [reflect_twice] at eq
theorem val_poly_infinity (p : (Polynomial K)) (pn : p≠0) :
    RatFunc.inftyValuation K (AtInfinity K p)=WithZero.exp (-(p.natTrailingDegree:ℤ)) := by
  rw [invert_poly,map_mul,valuation_reciprocal_pow]
  change RatFunc.inftyValuationDef K (algebraMap (Polynomial K) (RatFunc K) p.reverse) * _ = _
  rw [RatFunc.inftyValuation.polynomial _ (reverse_eq_zero.not.mpr pn),←WithZero.exp_add]
  have d := congrArg (fun n : ℕ => (n:ℤ)) (natDegree_eq_reverse_natDegree_add_natTrailingDegree p)
  push_cast at d
  congr 1
  omega
def inftyRingEval (K : Type*) [Field K] [DecidableEq (RatFunc K)] : (Polynomial K)→+*Infinity K where
  toFun p := ⟨AtInfinity K p,by
    change RatFunc.inftyValuation K (AtInfinity K p)≤1
    by_cases h : p=0
    · simp [h]
    rw [val_poly_infinity p h,←WithZero.exp_zero,WithZero.exp_le_exp]
    omega⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' p q := Subtype.ext (map_add _ _ _)
  map_mul' p q := Subtype.ext (map_mul _ _ _)
theorem inftyRingEval_injective : Function.Injective (inftyRingEval K) :=
  fun a b eq => atInfinity_injective (K:=K) (congrArg Subtype.val eq)
theorem inftyRingEval_isUnit (p : (Polynomial K)) (co : p.coeff 0≠0) :
    IsUnit (inftyRingEval K p) := by
  let a := inftyRingEval K p
  have pn : p≠0 := fun h=>co (by rw [h,coeff_zero])
  have val : RatFunc.inftyValuation K (a:RatFunc K)=1 := by
    change RatFunc.inftyValuation K (AtInfinity K p)=1
    rw [val_poly_infinity p pn,natTrailingDegree_eq_zero.mpr (Or.inr co)]
    simp
  have an : (a:RatFunc K)≠0 :=
    (map_ne_zero_iff _ (atInfinity_injective (K:=K))).mpr pn
  let inv : Infinity K := ⟨(a:RatFunc K)⁻¹,by
    change RatFunc.inftyValuation K (a:RatFunc K)⁻¹≤1
    rw [map_inv₀,val,inv_one]⟩
  exact ⟨⟨a,inv,Subtype.ext (mul_inv_cancel₀ an),Subtype.ext (inv_mul_cancel₀ an)⟩,rfl⟩
theorem mapped_X_infty :
    ((inftyRingEval K (Polynomial.X : (Polynomial K))):RatFunc K)=RatFunc.X⁻¹ := by
  change (AtInfinity K) (Polynomial.X : (Polynomial K))=_
  exact aeval_X _
theorem reflected_local_factor (p : (Polynomial K)) (d : ℕ) (fit : p.natDegree≤d) :
    inftyRingEval K (p.reflect d)=
      (inftyRingEval K (Polynomial.X : (Polynomial K)))^(d-p.natDegree)*inftyRingEval K p.reverse := by
  apply Subtype.ext
  change AtInfinity K (p.reflect d) =
    ((inftyRingEval K (Polynomial.X : (Polynomial K))):RatFunc K)^(d-p.natDegree)*AtInfinity K p.reverse
  have tail : AtInfinity K p.reverse=
      algebraMap (Polynomial K) (RatFunc K) p*((RatFunc.X : RatFunc K)⁻¹)^p.natDegree :=
    reverse_atInfinity p p.natDegree le_rfl
  have eq : ((RatFunc.X : RatFunc K)⁻¹)^d =
      ((RatFunc.X : RatFunc K)⁻¹)^(d-p.natDegree)*((RatFunc.X : RatFunc K)⁻¹)^p.natDegree := by
    rw [←pow_add,Nat.sub_add_cancel fit]
  rw [mapped_X_infty,reverse_atInfinity _ _ fit,tail,eq]
  ring
#print axioms reflected_local_factor
end
end Lower6960.MonicChart

end Merged_R6960MonicChartInfinityRing
