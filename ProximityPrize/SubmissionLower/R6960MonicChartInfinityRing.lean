import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdZeLOjNb
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Discriminant
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0
import ProximityPrize.SubmissionLower.R6960MarkedScalarPlace

section Merged6967_R6960MonicChartInfinityRing
set_option Elab.async false










set_option Elab.async false

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

end Merged6967_R6960MonicChartInfinityRing

section Merged6967_R6960RetainedCompressionDiscriminant
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2200000

namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Matrix Finset
open K1_14 (L)
open scoped Polynomial BigOperators

private theorem resultant_weighted_add_le {R : Type*} [CommRing R]
    (P Q : Polynomial (Polynomial R)) (m n a b d : ℕ)
    (hp : ∀ i≤m, (P.coeff i).natDegree+d*i≤a)
    (hq : ∀ i≤n, (Q.coeff i).natDegree+d*i≤b) :
    (resultant P Q m n).natDegree+d*(m*n)≤n*a+m*b := by
  classical
  let M := sylvester P Q m n
  let w : Fin (m+n) → ℕ := Fin.addCases (fun j : Fin m => b+d*j.val)
    (fun j : Fin n => a+d*j.val)
  have entry (σ : Equiv.Perm (Fin (m+n))) (i : Fin (m+n)) (ne : M (σ i) i≠0) :
      (M (σ i) i).natDegree+d*(σ i).val≤w i := by
    cases i using Fin.addCases with
    | left j =>
      have eq : M (σ (j.castAdd n)) (j.castAdd n) =
          if (σ (j.castAdd n)).val ∈ Set.Icc j.val (j.val+n) then
            Q.coeff ((σ (j.castAdd n)).val-j.val) else 0 := by simp [M,sylvester]
      rw [eq] at ne ⊢
      split_ifs at ne ⊢ with h
      · have low : j.val≤(σ (j.castAdd n)).val := h.1
        have small : (σ (j.castAdd n)).val-j.val≤n := by have := h.2; omega
        have c := hq _ small
        have step : d*((σ (j.castAdd n)).val-j.val)+d*j.val=d*(σ (j.castAdd n)).val := by
          rw [← Nat.mul_add,Nat.sub_add_cancel low]
        simp only [w,Fin.addCases_left]
        omega
      · exact (ne rfl).elim
    | right j =>
      have eq : M (σ (j.natAdd m)) (j.natAdd m) =
          if (σ (j.natAdd m)).val ∈ Set.Icc j.val (j.val+m) then
            P.coeff ((σ (j.natAdd m)).val-j.val) else 0 := by simp [M,sylvester]
      rw [eq] at ne ⊢
      split_ifs at ne ⊢ with h
      · have low : j.val≤(σ (j.natAdd m)).val := h.1
        have small : (σ (j.natAdd m)).val-j.val≤m := by have := h.2; omega
        have c := hp _ small
        have step : d*((σ (j.natAdd m)).val-j.val)+d*j.val=d*(σ (j.natAdd m)).val := by
          rw [← Nat.mul_add,Nat.sub_add_cancel low]
        simp only [w,Fin.addCases_right]
        omega
      · exact (ne rfl).elim
  let s := (∑ j : Fin m, d*j.val) + ∑ j : Fin n, d*j.val
  have ws : ∑ i,w i = n*a+m*b+s := by
    simp only [w,s,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,Finset.sum_add_distrib,
      Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    ring
  have pos : d*(m*n)≤n*a+m*b := by
    have h : d*m≤a := (Nat.le_add_left ..).trans (hp m le_rfl)
    calc
      _ = (d*m)*n := by ring
      _ ≤ a*n := Nat.mul_le_mul_right n h
      _ ≤ _ := by rw [Nat.mul_comm a n]; exact Nat.le_add_right ..
  have idx : (∑ i : Fin (m+n), d*i.val)=d*(m*n)+s := by
    simp only [s,Fin.sum_univ_add,Fin.val_castAdd,Fin.val_natAdd,Nat.mul_add,
      Finset.sum_add_distrib,Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    ring
  have terms (σ : Equiv.Perm (Fin (m+n))) :
      (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree≤n*a+m*b-d*(m*n) := by
    apply (Polynomial.natDegree_smul_le _ _).trans
    by_cases exists_zero : ∃ i, M (σ i) i=0
    · obtain ⟨i,h⟩ := exists_zero
      have zero : (∏ j : Fin (m+n), M (σ j) j)=0 :=
        Finset.prod_eq_zero (f := fun j => M (σ j) j) (Finset.mem_univ i) h
      rw [zero,natDegree_zero]
      exact Nat.zero_le _
    · push Not at exists_zero
      have bound := natDegree_prod_le Finset.univ (fun i=>M (σ i) i)
      have sum : (∑ i, ((M (σ i) i).natDegree+d*(σ i).val))≤∑ i,w i :=
        Finset.sum_le_sum (fun i _ => entry σ i (exists_zero i))
      have perm : (∑ i, d*(σ i).val) = ∑ i : Fin (m+n), d*i.val :=
        Equiv.sum_comp σ (fun i=>d*i.val)
      rw [Finset.sum_add_distrib,perm,ws,idx] at sum
      omega
  have det := natDegree_sum_le_of_forall_le (Finset.univ : Finset (Equiv.Perm (Fin (m+n)))) _
    (fun σ _ => terms σ)
  rw [← Matrix.det_apply] at det
  change M.det.natDegree+d*(m*n)≤_
  omega

theorem derivative_weighted_add_le {R : Type*} [CommRing R]
    (P : Polynomial (Polynomial R)) (e H d : ℕ) (he : 0<e)
    (cap : ∀ i≤e,(P.coeff i).natDegree+d*i≤H) :
    (P.resultant P.derivative e (e-1)).natDegree+d*e^2≤(2*e-1)*H := by
  have dh : d≤H := by have h := cap 1 he; simp at h; omega
  have der (i : ℕ) (hi : i≤e-1) :
      (P.derivative.coeff i).natDegree+d*i≤H-d := by
    have h := cap (i+1) (by omega)
    rw [Nat.mul_add,Nat.mul_one] at h
    have q := Polynomial.coeff_derivative_natDegree_le P i
    omega
  have bound := resultant_weighted_add_le P P.derivative e (e-1) H (H-d) d cap der
  have sum : (e-1)*H+e*(H-d)+e*d=(2*e-1)*H := by
    rw [add_assoc,← Nat.mul_add e (H-d) d,Nat.sub_add_cancel dh,← add_mul]
    have same : e-1+e=2*e-1 := by omega
    rw [same]
  have quad : d*(e*(e-1))+e*d=d*e^2 := by
    have delta : e-1+1=e := Nat.sub_add_cancel he
    calc
      _ = d*e*(e-1+1) := by ring
      _ = _ := by rw [delta]; ring
  have h := Nat.add_le_add_right bound (e*d)
  rw [sum,add_assoc,quad] at h
  exact h

/-- The padded derivative resultant satisfies the doubled tame-abscissa
degree bound, including the separate contribution at infinity. -/
theorem derivative_resultant_tame (f : Curve (Polynomial L)) (d : ℕ)
    (lo : 2≤f.degreeOf ordinate) (hi : f.degreeOf ordinate≤47) (degree : d≤164650)
    (bounded : height d f≤heightCap (f.degreeOf ordinate) d) :
    2*((view f).resultant (view f).derivative (f.degreeOf ordinate)
      (f.degreeOf ordinate-1)).natDegree+2*(f.degreeOf ordinate-1)<2130706433 := by
  let e := f.degreeOf ordinate
  let P := view f
  have caps (i : ℕ) (hi : i≤e) : (P.coeff i).natDegree+d*i≤(2*e-1)*d := by
    by_cases nz : P.coeff i=0
    · rw [nz,natDegree_zero,zero_add,mul_comm d i]
      exact Nat.mul_le_mul_right _ (by omega)
    exact (abscissa_coeff_height f d i nz).trans bounded
  have bound := derivative_weighted_add_le P e ((2*e-1)*d) d (by omega) caps
  have compensation : (2*e-1)*((2*e-1)*d)=d*e^2+(3*e-1)*(e-1)*d := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 1≤e from by omega)
    rw [hk, show 2*(1+k)-1=2*k+1 by omega, show 3*(1+k)-1=3*k+2 by omega,
      show 1+k-1=k by omega]
    ring
  rw [compensation] at bound
  have R : (P.resultant P.derivative e (e-1)).natDegree≤(3*e-1)*(e-1)*d := by omega
  have numerics : 2*((3*e-1)*(e-1)*d)+2*(e-1)<2130706433 := by
    apply LT.lt.trans_le' _ (Nat.add_le_add
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 hi) 1) (Nat.sub_le_sub_right hi 1)) degree))
      (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hi 1)))
    decide +kernel
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 R) _).trans_lt numerics

theorem derivative_resultant_nonzero (f : Curve (Polynomial L)) (ir : Irreducible f)
    (pos : 0<f.degreeOf ordinate) (small : f.degreeOf ordinate<K1.p) :
    (view f).resultant (view f).derivative (f.degreeOf ordinate)
      (f.degreeOf ordinate-1)≠0 := by
  let P := view f
  have ip : Irreducible P := (MulEquiv.irreducible_iff view).mpr ir
  have dP : P.natDegree=f.degreeOf ordinate := view_y f
  have ne : ((P.natDegree : ℕ) : Polynomial (Polynomial L)) ≠0 := by
    intro zero
    have dvd := (CharP.cast_eq_zero_iff (Polynomial (Polynomial L)) K1.p P.natDegree).mp zero
    exact (Nat.ne_of_gt (dP.symm ▸ pos)) (Nat.eq_zero_of_dvd_of_lt dvd (dP.symm ▸ small))
  have der : P.derivative≠0 := by
    intro zero
    have base : P.natDegree-1+1=P.natDegree := Nat.sub_add_cancel (dP.symm ▸ pos)
    have h := congrArg (fun Q => Q.coeff (P.natDegree-1)) zero
    rw [coeff_derivative,← Nat.cast_add_one,base,coeff_natDegree,coeff_zero] at h
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr ip.ne_zero) ne h
  have result := Polynomial.resultant_derivative_ne_zero_of_irreducible P ip der
  rwa [dP] at result

#print axioms derivative_resultant_nonzero
#print axioms derivative_resultant_tame
end
end Lower6960.RetainedCompression

end Merged6967_R6960RetainedCompressionDiscriminant

section Merged6967_R6966ProofFarPure
set_option Elab.async false


set_option Elab.async false

namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K I node)
open K1_14 (L liftPoly)
open CurvatureSquares (Ordinate zView coeff_caps)
open RetainedShortening (Word)
open RescueGeometry (Model Family)
open scoped Polynomial
open Lower6960.RetainedCompression (rate_mono)
open CurvatureSquares (node_eval node_height node_ne root_count)
private abbrev embed := algebraMap K L
private theorem node_coefficient (P : Ordinate) (i : I) (j : ℕ) :
    ((atNode P i).coeff j).natDegree≤(zView P).natDegree := by
  rw [atNode,coeff_map,coe_evalRingHom]
  exact (CurvatureSquares.node_height ..).trans (coeff_caps P j).2
private theorem root_at_node {P : Ordinate} {z : L} {S : (Polynomial K)}
    (mark : MarkedFiber P z (liftPoly S)) (i : I) :
    ((atNode P i).map (evalRingHom z)).eval (embed (S.eval (node i)))=0 := by
  let x := embed (node i)
  have commute : (specialize P z).map (evalRingHom x)=(atNode P i).map (evalRingHom z) := by
    apply Polynomial.ext
    intro n
    simp only [specialize,atNode,x,coeff_map,coe_mapRingHom,coe_evalRingHom]
    exact (CurvatureSquares.node_eval (P.coeff n) (embed (node i)) z).symm
  have value : (liftPoly S).eval x=embed (S.eval (node i)) := by
    rw [liftPoly,show x=embed (node i) from rfl,Polynomial.eval_map_apply]
  have h := congrArg (Polynomial.eval x) mark.root
  have eq := Polynomial.eval_map_apply (f:=evalRingHom x)
    (p:=specialize P z) (x:=liftPoly S)
  rw [commute,coe_evalRingHom,value] at eq
  exact eq.trans (h.trans eval_zero)
theorem pure_node_price_far {w s T} (W : Word 179759 164768 w s T)
    (z : K → L) (inj : Set.InjOn z (T:Set K)) (P : Ordinate) (irr : Irreducible P)
    (pos : 0<P.natDegree) (pure : PureNodes w P)
    (marks : ∀ γ∈T, MarkedFiber P (z γ) (liftPoly (s γ))) :
    T.card≤18*(zView P).natDegree+1 := by
  classical
  apply CurvatureVotes.minority_count W (by decide) (Or.inl (by decide))
  intro i
  let Q := atNode P i
  let a := Q.leadingCoeff
  let g := Q.eval (C (embed (w i)))
  have cn (j : ℕ) : (Q.coeff j).natDegree≤(zView P).natDegree := node_coefficient P i j
  have fits : g.natDegree≤(zView P).natDegree := by
    dsimp only [g]
    rw [eval_eq_sum,Polynomial.sum_def]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    rw [← C_pow]
    exact (natDegree_mul_C_le ..).trans (cn j)
  by_cases nonzero : g≠0
  · left
    apply (CurvatureSquares.root_count (inj.mono (filter_subset _ _)) g nonzero _).trans fits
    intro γ hγ
    obtain ⟨active,hit⟩ := mem_filter.mp hγ
    have hz := root_at_node (marks γ active) i
    have eq := Polynomial.eval_map_apply (f:=evalRingHom (z γ))
      (p:=Q) (x:=C (embed (w i)))
    rw [coe_evalRingHom,eval_C] at eq
    rw [hit] at hz
    exact eq.symm.trans hz
  · right
    have qn : Q≠0 := CurvatureSquares.node_ne P irr pos _
    have an : a≠0 := leadingCoeff_ne_zero.mpr qn
    apply (CurvatureSquares.root_count (inj.mono (filter_subset _ _)) a an _).trans
      (by simpa only [a,coeff_natDegree] using cn Q.natDegree)
    intro γ hγ
    obtain ⟨active,miss⟩ := mem_filter.mp hγ
    have hz := root_at_node (marks γ active) i
    have packed := pure i (not_ne_iff.mp nonzero)
    change Q=C a*(Polynomial.X-C (C (embed (w i))))^P.natDegree at packed
    change (Q.map (evalRingHom (z γ))).eval (embed ((s γ).eval (node i)))=0 at hz
    rw [packed,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_sub,
      Polynomial.map_X,Polynomial.map_C,eval_mul,eval_pow,eval_sub,eval_X,eval_C,
      eval_C,coe_evalRingHom,eval_C] at hz
    exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ (sub_ne_zero.mpr (embed.injective.ne miss)))

#print axioms pure_node_price_far
end
end Lower6960.RetainedCompression

end Merged6967_R6966ProofFarPure

section Merged6967_R6966ProofHelperWeightCap
set_option Elab.async false



set_option Elab.async false

namespace Research6966.HelperWeightCap
open Polynomial Finset Module
open K1_14 (Jet Seeds FX)
open K1_14_1 (PoleData CRTLift jetConstant)
open K1_14_1_4 (doubleMap specialized evalRaw)
open K1_14_2_2_2_1 (jetDegree jetDegree_le)
open Pade (totalJet)
open PadeRank (Plane box)
open scoped Polynomial
noncomputable section
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false

private theorem total_constant {K:Type*} [Field K] (c:K) : totalJet (jetConstant c)=0 := by
  apply Nat.eq_zero_of_le_zero
  apply (Pade.totalJet_le _ _).mpr
  intro j i ne
  by_cases hj:j=0
  · subst j;by_cases hi:i=0
    · omega
    · exact False.elim (ne (by simp [jetConstant,coeff_C,hi]))
  · exact False.elim (ne (by simp [jetConstant,coeff_C,hj]))

theorem native_total {F:Type*} [Field F] (f:Seeds→+*F) (inj:Function.Injective f) (N:Jet) :
    totalJet (doubleMap f N)=jetDegree N := by
  have eq (b:ℕ) : totalJet (doubleMap f N)≤b ↔ jetDegree N≤b := by
    rw [Pade.totalJet_le,jetDegree_le]
    simp only [doubleMap,coe_mapRingHom,coeff_map,map_ne_zero_iff _ inj]
  exact le_antisymm ((eq _).mpr le_rfl) ((eq _).mp le_rfl)

private theorem chart_total {K:Type*} [Field K] (a b u d:K) (an:a≠0) {Q:Plane K} (qn:Q≠0) :
    totalJet (PadeChart.chart a b u d Q)=totalJet Q := by
  let T:=PadeChart.chart a b u d
  have inj:Function.Injective T:=(PadeChart.chart_equiv a b u d an).1
  have after:T Q≠0:=(map_ne_zero_iff _ inj).mpr qn
  let j:=Q.natDegree+(T Q).natDegree+1
  have source:Q.natDegree<j:=by dsimp only [j];omega
  have target:(T Q).natDegree<j:=by dsimp only [j];omega
  have rel (c:ℕ):totalJet Q<c ↔ totalJet (T Q)<c := by
    let V:=box K c j
    let r:↥V→ₗ[K]V:=T.toLinearMap.restrict (fun _ q=>PadeChart.chart_box a b u d _ _ q)
    have ri:Function.Injective r:=fun _ _ eq=>Subtype.ext (inj (congrArg Subtype.val eq))
    have onto:Function.Surjective r:=LinearMap.surjective_of_injective (K:=K) (V:=↥V) (f:=r) ri
    constructor
    · intro low
      exact ((PadeRank.mem_box after).mp (PadeChart.chart_box a b u d _ _ ((PadeRank.mem_box qn).mpr ⟨low,source⟩))).1
    · intro low
      obtain ⟨R,eq⟩:=onto ⟨T Q,(PadeRank.mem_box after).mpr ⟨low,target⟩⟩
      have id:R.val=Q:=inj (congrArg Subtype.val eq)
      exact ((PadeRank.mem_box qn).mp (id ▸ R.property)).1
  exact le_antisymm (Nat.le_of_lt_succ ((rel _).mp (Nat.lt_succ_self _)))
    (Nat.le_of_lt_succ ((rel _).mpr (Nat.lt_succ_self _)))

/-- The physical model pays w times total jet degree, with at most the
slope degree lost on the top diagonal. This holds for any positive-slope
prime and for products. -/
theorem weight_lower {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} (M:HelperPhysicalModel.Model Crt N)
    (nn:N≠0) (w:ℕ) (wp:0<w) :
    w*jetDegree N≤RawPhysicalDegree.weight w (w-1) M.raw+N.natDegree := by
  let f:=algebraMap Seeds K1_14_3.SeedField
  let R:=doubleMap evalRaw M.raw
  obtain ⟨a,b,u,d,an,form⟩:=K1_14_1_4.specialized_affine_form Crt
  have chart:specialized Crt N=PadeChart.chart a b u d (doubleMap f N) := by
    have id:=RingHom.congr_fun form N;change specialized Crt N=_ at id
    rw [id]
    change _=(K1_14_1_4.substitute (RingHom.id _) _ _).comp (doubleMap f) N
    rw [K1_14_1_4.substitute_map,RingHom.id_comp]
  have fi:=IsFractionRing.injective Seeds K1_14_3.SeedField
  have nz:doubleMap f N≠0:=(map_ne_zero_iff (doubleMap f) (map_injective _ (map_injective _ fi))).mpr nn
  have spec:=K1_14_1_4.specialized_leading Crt nn
  have cn: (jetConstant M.c:Plane K1_14_3.SeedField)≠0:=C_ne_zero.mpr (C_ne_zero.mpr M.unit_c)
  have total:totalJet R=jetDegree N := by
    dsimp only [R];rw [M.eq,Pade.totalJet_mul cn spec.2.2,total_constant,zero_add,chart,
      chart_total a b u d an nz,native_total f fi]
  have slope:R.natDegree=N.natDegree := by
    dsimp only [R];rw [M.eq,natDegree_mul cn spec.2.2,spec.1]
    simp [jetConstant]
  let Lw:=RawPhysicalDegree.weight w (w-1) M.raw
  have bounded:K1_14_1_4.Bounded w (w-1) Lw M.raw:=(RawPhysicalDegree.bounded_iff ..).mpr le_rfl
  by_contra! no
  have pos:0<jetDegree N:=by by_contra! z;rw [Nat.eq_zero_of_le_zero z,mul_zero] at no;omega
  have reduced:totalJet R≤jetDegree N-1 := (Pade.totalJet_le ..).mpr (by
    intro j i ne
    have raw:(M.raw.coeff j).coeff i≠0:=by
      intro z;apply ne;simp only [R,doubleMap,coe_mapRingHom,coeff_map,z,map_zero]
    have js:j≤N.natDegree:=slope ▸ le_natDegree_of_ne_zero (show R.coeff j≠0 from fun z=>ne (by rw [z,coeff_zero]))
    have phys:=bounded j i ((M.raw.coeff j).coeff i).natDegree (leadingCoeff_ne_zero.mpr raw)
    have charge:(w-1)*j+j=w*j:=by rw [←Nat.succ_mul];congr 1;omega
    have small:w*(i+j)<w*jetDegree N := by rw [Nat.mul_add];change Lw+N.natDegree<w*jetDegree N at no;omega
    have lt:=Nat.lt_of_mul_lt_mul_left small
    omega)
  omega

theorem slope_cost {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} (M:HelperPhysicalModel.Model Crt N)
    (nn:N≠0) (v:0<N.natDegree) {w:ℕ} (wp:0<w) :
    w-1≤RawPhysicalDegree.weight w (w-1) M.raw := by
  have j:N.natDegree≤jetDegree N := by
    have total:=(jetDegree_le N _).mp le_rfl N.natDegree N.leadingCoeff.natDegree
      (by rw [coeff_natDegree,coeff_natDegree];exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nn))
    omega
  have spent:= (Nat.mul_le_mul_left w j).trans (weight_lower M nn w wp)
  have rt:(w-1)*N.natDegree+N.natDegree=w*N.natDegree:=by rw [←Nat.succ_mul];congr 1;omega
  have once:w-1≤(w-1)*N.natDegree:=by simpa only [mul_one] using Nat.mul_le_mul_left (w-1) (show 1≤N.natDegree from v)
  omega

theorem native_degree {G:Pade.Row K1_14_3.SeedField} (N:PadeNativeQuotient.Native G) (gp:G.primitive) :
    jetDegree N.poly=G.graphDegree := by
  let f:=algebraMap K1_14_3.SeedField K1_14_3.SeedClosure
  have inj:=f.injective.comp (IsFractionRing.injective Seeds K1_14_3.SeedField)
  have eq:=native_total K1_14_3.seedGeneric inj N.poly
  change totalJet (K1_14_3.fibreRow N.poly)=jetDegree N.poly at eq
  rw [←eq,N.eq]
  change totalJet (jetConstant N.scalar*(G.map f).polynomial)=_
  rw [Pade.totalJet_mul (show (jetConstant N.scalar:Plane K1_14_3.SeedClosure)≠0 from
    C_ne_zero.mpr (C_ne_zero.mpr N.nonzero)) ((G.map f).polynomial_ne ((G.primitive_map f).mpr gp)),
    total_constant,zero_add,(G.map f).total_polynomial ((G.primitive_map f).mpr gp),Pade.Row.degree_map]

#print axioms weight_lower
#print axioms slope_cost
end
end Research6966.HelperWeightCap

end Merged6967_R6966ProofHelperWeightCap

section Merged6967_R6966ProofHelperWindowIntervals
set_option Elab.async false


set_option Elab.async false

-- merged module R6966ProofHelperWindowPrefix
section Merged_R6966ProofHelperWindowPrefix

namespace Research6966.HelperWindowPrefix
open Finset
open K1_14 (Shape shapeSum)
open PadeFiltered (physicalWindow)
set_option maxHeartbeats 1100000

private theorem grade_sum (stop B J w : ℕ) (hw : 0 < w) :
    (∑ W ∈ range stop, (physicalWindow B J w W).card) =
      ∑ q ∈ range (B+1), ∑ j ∈ range (min q J+1), (stop+j-w*q) := by
  let s : Shape := ⟨0,B,J,0⟩
  have point (t : ℕ × ℕ) :
      (∑ W ∈ range stop, if w*t.2+(w-1)*t.1 ≤ W then 1 else 0) =
        stop+t.1-w*(t.1+t.2) := by
    have hj : t.1 ≤ w*(t.1+t.2) := by
      have h := Nat.mul_le_mul_right (t.1+t.2) (show 1 ≤ w from hw)
      omega
    have eq := K1_14_4.sum_interval stop t.1 (w*(t.1+t.2)) 0 1 hj
    rw [Nat.sub_zero, Nat.one_mul] at eq
    rw [← eq]
    apply sum_congr rfl
    intro W hW
    simp only [Nat.add_zero, mem_range.mp hW, and_true]
    have rel : w*(t.1+t.2) = w*t.2+(w-1)*t.1+t.1 := by
      rw [Nat.mul_add]
      have exp := congrArg (fun v => v*t.1) (Nat.sub_add_cancel hw : w-1+1=w)
      rw [Nat.add_mul, Nat.one_mul] at exp
      omega
    simp only [rel, Nat.add_le_add_iff_right]
  calc
    _ = ∑ W ∈ range stop, ∑ t ∈ PadeRank.positions (B+1) (J+1),
          if w*t.2+(w-1)*t.1 ≤ W then 1 else 0 := by
      apply sum_congr rfl
      intro W _
      rw [physicalWindow, card_filter]
    _ = ∑ t ∈ PadeRank.positions (B+1) (J+1), (stop+t.1-w*(t.1+t.2)) := by
      rw [sum_comm]; exact sum_congr rfl (fun t _ => point t)
    _ = ∑ j ∈ range (J+1), ∑ q ∈ Ico j (B+1), (stop+j-w*q) := by
      rw [PadeRank.positions, sum_filter, sum_product]
      apply sum_congr rfl
      intro j _
      rw [← sum_filter]
      have range_eq : (range (B+1)).filter (fun i => j+i < B+1) = range (B+1-j) := by
        ext i; simp only [mem_filter, mem_range]; omega
      rw [range_eq, sum_Ico_eq_sum_range]
    _ = _ := K1_14_4.shapeSum_swap s (fun q j => stop+j-w*q)

private def trianglePart (stop n w : ℕ) : ℕ :=
  let moment := n*(n+1)*(n+2)
  (3*stop*(n+1)*(n+2)+moment-2*w*moment)/6

private def tailPart (stop n r J w : ℕ) : ℕ :=
  let length := r-n
  (length*(2*stop*(J+1)+J*(J+1))-w*(J+1)*(r+n+1)*length)/2

/-- Cumulative physical-window volume below an exclusive weight cutoff.
The complete triangle, the complete strip, and one partial grade are
evaluated with natural arithmetic. The equality requires `J < w`. -/
def volume (stop B J w : ℕ) : ℕ :=
  if stop = 0 then 0 else
    let last := min B ((stop-1)/w)
    let n := min last J
    let length := min (last+1) J - (w*(last+1)-stop)
    trianglePart stop n w + tailPart stop n last J w +
      if last < B then length*(length+1)/2 else 0

private theorem row_scaled (stop q J w : ℕ) (live : w*q ≤ stop) :
    2*(∑ j ∈ range (J+1), (stop+j-w*q))+2*w*q*(J+1) =
      2*stop*(J+1)+J*(J+1) := by
  have move (j : ℕ) : stop+j-w*q = (stop-w*q)+j := by omega
  simp_rw [move]
  rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]
  have hs := sum_range_id_mul_two (J+1)
  rw [Nat.add_sub_cancel] at hs
  have ht := Nat.sub_add_cancel live
  nlinarith only [hs, congrArg (fun x => 2*(J+1)*x) ht]

private theorem triangle_scaled (stop n w : ℕ) (live : w*n ≤ stop) :
    6*(∑ q ∈ range (n+1), ∑ j ∈ range (q+1), (stop+j-w*q))+2*w*n*(n+1)*(n+2) =
      3*stop*(n+1)*(n+2)+n*(n+1)*(n+2) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [sum_range_succ]
    have prev := ih ((Nat.mul_le_mul_left w (Nat.le_succ n)).trans live)
    have row := row_scaled stop (n+1) (n+1) w live
    nlinarith only [prev, congrArg (3*·) row]

private theorem triangle_eq (stop n w : ℕ) (live : w*n ≤ stop) :
    (∑ q ∈ range (n+1), ∑ j ∈ range (q+1), (stop+j-w*q)) = trianglePart stop n w := by
  have eq := triangle_scaled stop n w live
  unfold trianglePart
  dsimp only
  rw [show 2*w*(n*(n+1)*(n+2)) = 2*w*n*(n+1)*(n+2) by ring, ← eq,
    Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by decide : 0 < 6)]

private theorem tail_scaled (stop n count J w : ℕ) (live : w*(n+count) ≤ stop) :
    2*(∑ i ∈ range count, ∑ j ∈ range (J+1), (stop+j-w*(n+1+i)))+
      w*(J+1)*(2*n+count+1)*count = count*(2*stop*(J+1)+J*(J+1)) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [sum_range_succ]
    have prev := ih ((Nat.mul_le_mul_left w (Nat.add_le_add_left (Nat.le_succ count) n)).trans live)
    have flip : n+(count+1)=n+1+count := by omega
    have row := row_scaled stop (n+1+count) J w (flip ▸ live)
    nlinarith only [prev,row]

private theorem tail_eq (stop n r J w : ℕ) (nr : n ≤ r) (live : w*r ≤ stop) :
    (∑ q ∈ Ico (n+1) (r+1), ∑ j ∈ range (J+1), (stop+j-w*q)) =
      tailPart stop n r J w := by
  rw [sum_Ico_eq_sum_range, show r+1-(n+1)=r-n by omega]
  have live' : w*(n+(r-n)) ≤ stop := by rwa [Nat.add_sub_of_le nr]
  have eq := tail_scaled stop n (r-n) J w live'
  have h := (show 2*n+(r-n)+1=r+n+1 by omega)
  rw [h] at eq
  unfold tailPart
  dsimp only
  rw [← eq, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

private theorem partial_scaled (J gap : ℕ) :
    2*(∑ j ∈ range (J+1), (j-gap)) = (J-gap)*(J-gap+1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, Nat.mul_add, ih]
    by_cases h : gap ≤ J
    · rw [show J+1-gap = J-gap+1 by omega]
      ring
    · rw [show J-gap=0 by omega, show J+1-gap=0 by omega]

private theorem partial_eq (stop q J w : ℕ) (dead : stop ≤ w*q) :
    (∑ j ∈ range (J+1), (stop+j-w*q)) =
      (J-(w*q-stop))*(J-(w*q-stop)+1)/2 := by
  have move (j : ℕ) : stop+j-w*q = j-(w*q-stop) := by omega
  simp_rw [move]
  rw [← partial_scaled, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

/-- The closed form computes the same cumulative dimension as summing
every physical weight. A positive slope exponent can add only one
partial grade when the slope cap is below the physical step. -/
theorem volume_eq_sum (stop B J w : ℕ) (narrow : J < w) :
    volume stop B J w = ∑ W ∈ range stop, (physicalWindow B J w W).card := by
  classical
  have hw : 0 < w := by omega
  rw [grade_sum stop B J w hw]
  by_cases z : stop = 0
  · subst stop
    rw [volume, ite_eq_left rfl]
    symm
    apply sum_eq_zero
    intro q _
    apply sum_eq_zero
    intro j hj
    have jle : j ≤ q := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_left _ _)
    have qle := Nat.mul_le_mul_right q (show 1 ≤ w from hw)
    omega
  rw [volume, ite_eq_right z]
  dsimp only
  let last := min B ((stop-1)/w)
  let n := min last J
  let grade (q : ℕ) := ∑ j ∈ range (min q J+1), (stop+j-w*q)
  have lB : last ≤ B := min_le_left _ _
  have nl : n ≤ last := min_le_left _ _
  have nJ : n ≤ J := min_le_right _ _
  have live : w*last ≤ stop := by
    have h := (Nat.le_div_iff_mul_le hw).mp (show last ≤ (stop-1)/w from min_le_right _ _)
    rw [Nat.mul_comm last w] at h
    omega
  have complete : (∑ q ∈ range (last+1), grade q) =
      trianglePart stop n w+tailPart stop n last J w := by
    rw [← sum_range_add_sum_Ico grade (Nat.succ_le_succ nl)]
    congr 1
    · rw [← triangle_eq stop n w ((Nat.mul_le_mul_left w nl).trans live)]
      apply sum_congr rfl
      intro q hq
      unfold grade
      rw [min_eq_left ((Nat.lt_succ_iff.mp (mem_range.mp hq)).trans nJ)]
    · rw [← tail_eq stop n last J w nl live]
      apply sum_congr rfl
      intro q hq
      have jle : J ≤ q := by
        have lo := (mem_Ico.mp hq).1
        have hi := (mem_Ico.mp hq).2
        dsimp only [n] at lo
        omega
      unfold grade
      rw [min_eq_right jle]
  change trianglePart stop n w+tailPart stop n last J w+
    (if last < B then
      (min (last+1) J-(w*(last+1)-stop))*(min (last+1) J-(w*(last+1)-stop)+1)/2
    else 0) = ∑ q ∈ range (B+1), grade q
  rw [← sum_range_add_sum_Ico grade (Nat.succ_le_succ lB), complete]
  congr 1
  by_cases more : last < B
  · rw [ite_eq_left more]
    have exactLast : last = (stop-1)/w := by
      dsimp only [last] at more ⊢
      omega
    have dead : stop ≤ w*(last+1) := by
      have h := (Nat.div_lt_iff_lt_mul hw).mp (show (stop-1)/w < last+1 by omega)
      rw [Nat.mul_comm (last+1) w] at h
      omega
    rw [sum_eq_single (last+1)]
    · exact (partial_eq _ _ _ _ dead).symm
    · intro q hq ne
      have lo := (mem_Ico.mp hq).1
      have paid := Nat.mul_le_mul_left w (show last+2 ≤ q by omega)
      rw [show last+2=(last+1)+1 by omega, Nat.mul_add, Nat.mul_one] at paid
      apply sum_eq_zero
      intro j hj
      have jle := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_right q J)
      omega
    · intro notMem
      exact (notMem (mem_Ico.mpr ⟨le_rfl, Nat.succ_lt_succ more⟩)).elim
  · rw [ite_eq_right more, show last=B by omega, Ico_self, sum_empty]

/-- The same closed form is the leading term in the helper rank floor. -/
theorem volume_eq_shapeSum (s : Shape) (stop w : ℕ) (narrow : s.J < w) :
    volume stop s.B s.J w = shapeSum s (fun q j => stop+j-w*q) := by
  exact (volume_eq_sum stop s.B s.J w narrow).trans (grade_sum stop s.B s.J w (by omega))

#print axioms volume_eq_sum
#print axioms volume_eq_shapeSum
end Research6966.HelperWindowPrefix

end Merged_R6966ProofHelperWindowPrefix

-- merged module R6966ProofHelperWindowGrouping
section Merged_R6966ProofHelperWindowGrouping

namespace Research6966.HelperWindowGrouping
open Finset
open K1_14 (Shape)
open HelperAvoidance (power debitAt rectSlots triSlots)
open HelperBankRank (cells)
open HelperWindowPrefix (volume)
open PadeFiltered (physicalWindow)
set_option maxHeartbeats 850000

def sumCount (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumCount f n + f n

theorem sumCount_eq (f : ℕ → ℕ) (n : ℕ) :
    sumCount f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih => rw [sumCount, ih, sum_range_succ]

/-- One physical layer for the divisor power `k+1`. The start and stop are
exclusive prefixes in the residual window after paying the divisor. -/
def layer (s : Shape) (h N k a b wt : ℕ) : ℕ :=
  if (k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J then
    let hi := N-2*h*k-(k+1)*wt
    let lo := hi-2*h
    let B := s.B-(k+1)*a
    let J := s.J-(k+1)*b
    volume hi B J (131071-h) - volume lo B J (131071-h)
  else 0

def grouped (s : Shape) (h N a b wt limit : ℕ) (slots : ℕ → ℕ) : ℕ :=
  sumCount (fun k => layer s h N k a b wt * slots (k+1)) limit

private theorem power_eq_window {N h W k : ℕ} (hp : 0 < h) (mem : W < N) :
    power N h W = k+1 ↔ N-2*h*(k+1) ≤ W ∧ W < N-2*h*k := by
  have hs : 0 < 2*h := by omega
  have lo := K1_14_4.power_threshold N (2*h) W 0 k mem hs
  have hi := K1_14_4.power_threshold N (2*h) W 0 (k+1) mem hs
  simp only [Nat.zero_add, Nat.sub_zero] at lo hi
  change k < power N h W ↔ W+2*h*k < N at lo
  change k+1 < power N h W ↔ W+2*h*(k+1) < N at hi
  omega

private theorem shifted_prefix (f : ℕ → ℕ) (stop paid : ℕ) :
    (∑ W ∈ range stop, if paid ≤ W then f (W-paid) else 0) =
      ∑ W ∈ range (stop-paid), f W := by
  classical
  by_cases live : paid ≤ stop
  · rw [← sum_range_add_sum_Ico (fun W => if paid ≤ W then f (W-paid) else 0) live]
    have early : (∑ W ∈ range paid, if paid ≤ W then f (W-paid) else 0) = 0 := by
      apply sum_eq_zero
      intro W hw
      rw [ite_eq_right (Nat.not_le.mpr (mem_range.mp hw))]
    rw [early, Nat.zero_add]
    rw [sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro W _
    simp only [Nat.le_add_right paid W, ite_true, Nat.add_sub_cancel_left]
  · rw [Nat.sub_eq_zero_of_le (by omega), range_zero, sum_empty]
    apply sum_eq_zero
    intro W hw
    have := mem_range.mp hw
    rw [ite_eq_right (by omega)]

private theorem shifted_interval (f : ℕ → ℕ) (lo hi paid : ℕ) (range_ok : lo ≤ hi) :
    (∑ W ∈ Ico lo hi, if paid ≤ W then f (W-paid) else 0) =
      (∑ W ∈ range (hi-paid), f W)-(∑ W ∈ range (lo-paid), f W) := by
  have eq := sum_range_add_sum_Ico (fun W => if paid ≤ W then f (W-paid) else 0) range_ok
  rw [shifted_prefix, shifted_prefix] at eq
  omega

theorem layer_eq (s : Shape) (h N k a b wt : ℕ) (hp : 0 < h) (narrow : s.J < 131071-h) :
    layer s h N k a b wt =
      ∑ W ∈ range N, if power N h W = k+1 then (cells s h W (k+1) a b wt).card else 0 := by
  classical
  unfold layer
  by_cases room : (k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J
  · rw [ite_eq_left room]
    dsimp only
    let endW := N-2*h*k
    let startW := N-2*h*(k+1)
    let paid := (k+1)*wt
    let B := s.B-(k+1)*a
    let J := s.J-(k+1)*b
    let f (W : ℕ) := (physicalWindow B J (131071-h) W).card
    have filter_eq : (range N).filter (fun W => power N h W = k+1) = Ico startW endW := by
      ext W
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · rintro ⟨mem,eq⟩
        exact (power_eq_window hp mem).mp eq
      · intro interval
        have mem : W < N := interval.2.trans_le (Nat.sub_le _ _)
        exact ⟨mem,(power_eq_window hp mem).mpr interval⟩
    have order : startW ≤ endW := by
      dsimp only [startW,endW]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have lo : endW-paid-2*h = startW-paid := by
      dsimp only [startW,endW,paid]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    change volume (endW-paid) B J (131071-h)-volume (endW-paid-2*h) B J (131071-h) = _
    have nJ : J < 131071-h := (Nat.sub_le _ _).trans_lt narrow
    rw [lo, HelperWindowPrefix.volume_eq_sum _ _ _ _ nJ, HelperWindowPrefix.volume_eq_sum _ _ _ _ nJ,
      ← sum_filter, filter_eq, ← shifted_interval f startW endW paid order]
    apply sum_congr rfl
    intro W _
    by_cases full : paid ≤ W
    · rw [ite_eq_left full, cells, ite_eq_left ⟨room.1,room.2,full⟩]
    · rw [ite_eq_right full, cells, ite_eq_right (fun all => full all.2.2), card_empty]
  · rw [ite_eq_right room]
    symm
    apply sum_eq_zero
    intro W _
    have no : ¬ ((k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J ∧ (k+1)*wt ≤ W) :=
      fun all => room ⟨all.1,all.2.1⟩
    rw [cells, ite_eq_right no, card_empty]
    split <;> rfl

/-- Group the raw-weight debit into disjoint divisor powers. The caller may
cut off any powers that have zero slot count or cannot fit the degree box. -/
theorem grouped_eq_debit_of_cutoff (s : Shape) (h N a b wt limit : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (narrow : s.J < 131071-h)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b ∨ N ≤ 2*h*(k-1)+k*wt) :
    grouped s h N a b wt limit slots = ∑ W ∈ range N, debitAt s h N W a b wt slots := by
  classical
  rw [grouped, sumCount_eq]
  calc
    _ = ∑ k ∈ range limit, ∑ W ∈ range N,
        if power N h W = k+1 then (cells s h W (k+1) a b wt).card*slots (k+1) else 0 := by
      apply sum_congr rfl
      intro k _
      rw [layer_eq s h N k a b wt hp narrow, sum_mul]
      apply sum_congr rfl
      intro W _
      split <;> simp_all
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro W hW
      let t := power N h W
      have pos : 0 < t := (show 0 < 1 by decide).trans_le (Nat.le_add_right _ _)
      change (∑ k ∈ range limit, if t = k+1 then (cells s h W (k+1) a b wt).card*slots (k+1) else 0) =
        (cells s h W t a b wt).card*slots t
      by_cases active : t ≤ limit
      · have live : t-1 ∈ range limit := mem_range.mpr (by omega)
        rw [sum_eq_single_of_mem (t-1) live]
        · rw [Nat.sub_add_cancel pos, ite_eq_left rfl]
        · intro k _ ne
          rw [ite_eq_right (by omega)]
      · have zero : (cells s h W t a b wt).card*slots t = 0 := by
          rcases tail t (by omega) with fee | aLarge | bLarge | closed
          · rw [fee, Nat.mul_zero]
          · rw [cells, ite_eq_right (fun live => (Nat.not_le.mpr aLarge) live.1), card_empty, Nat.zero_mul]
          · rw [cells, ite_eq_right (fun live => (Nat.not_le.mpr bLarge) live.2.1), card_empty, Nat.zero_mul]
          · have inWindow := (@power_eq_window N h W (t-1) hp (mem_range.mp hW)).mp
                (show power N h W = t-1+1 from (Nat.sub_add_cancel pos).symm)
            have stale : ¬ t*wt ≤ W := by omega
            rw [cells, ite_eq_right (fun live => stale live.2.2), card_empty, Nat.zero_mul]
        rw [zero]
        apply sum_eq_zero
        intro k hk
        have kin := mem_range.mp hk
        rw [ite_eq_right (by omega)]

theorem grouped_eq_debit (s : Shape) (h N a b wt limit : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (narrow : s.J < 131071-h)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b) :
    grouped s h N a b wt limit slots = ∑ W ∈ range N, debitAt s h N W a b wt slots := by
  apply grouped_eq_debit_of_cutoff s h N a b wt limit slots hp narrow
  intro k large
  rcases tail k large with fee | width | slope
  · exact Or.inl fee
  · exact Or.inr (Or.inl width)
  · exact Or.inr (Or.inr (Or.inl slope))

theorem grouped_by_slope (s : Shape) (h N a b wt : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (bp : 0 < b) (narrow : s.J < 131071-h) :
    grouped s h N a b wt (s.J/b) slots = ∑ W ∈ range N, debitAt s h N W a b wt slots := by
  apply grouped_eq_debit s h N a b wt (s.J/b) slots hp narrow
  intro k large
  exact Or.inr (Or.inr ((Nat.div_lt_iff_lt_mul bp).mp large))

#print axioms grouped_eq_debit
#print axioms grouped_by_slope
end Research6966.HelperWindowGrouping

end Merged_R6966ProofHelperWindowGrouping

-- merged module R6966ProofHelperWindowIntervals
section Merged_R6966ProofHelperWindowIntervals

namespace Research6966.HelperWindowIntervals
open Finset
open K1_14 (Shape shapeSum triangle)
open HelperAvoidance (debitAt rectSlots triSlots)
open HelperWindowGrouping (sumCount sumCount_eq grouped layer)
open HelperWindowPrefix (volume volume_eq_shapeSum)
set_option maxHeartbeats 850000

private theorem shape_mono (s : Shape) (f g : ℕ → ℕ → ℕ)
    (cap : ∀ q ≤ s.B, ∀ j ≤ min q s.J, f q j ≤ g q j) : shapeSum s f ≤ shapeSum s g := by
  unfold shapeSum
  exact sum_le_sum (fun q hq => sum_le_sum (fun j hj =>
    cap q (Nat.lt_succ_iff.mp (mem_range.mp hq)) j (Nat.lt_succ_iff.mp (mem_range.mp hj))))

theorem volume_mono (s : Shape) {lo hi wLo wHi : ℕ}
    (stop : lo ≤ hi) (step : wLo ≤ wHi) (narrow : s.J < wLo) :
    volume lo s.B s.J wHi ≤ volume hi s.B s.J wLo := by
  rw [volume_eq_shapeSum s _ _ (narrow.trans_le step), volume_eq_shapeSum s _ _ narrow]
  exact shape_mono s _ _ (fun q _ j _ =>
    (Nat.sub_le_sub_right (Nat.add_le_add_right stop j) _).trans
      (Nat.sub_le_sub_left (Nat.mul_le_mul_right q step) _))

private theorem slice_eq (s : Shape) (stop w span : ℕ) (narrow : s.J < w) :
    volume stop s.B s.J w-volume (stop-span) s.B s.J w =
      shapeSum s (fun q j => min span (stop+j-w*q)) := by
  have pieces : volume stop s.B s.J w =
      shapeSum s (fun q j => min span (stop+j-w*q))+volume (stop-span) s.B s.J w := by
    rw [volume_eq_shapeSum s _ _ narrow, volume_eq_shapeSum s _ _ narrow]
    unfold shapeSum
    simp only [← sum_add_distrib]
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro j hj
    have jle := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_left q s.J)
    have qw := Nat.mul_le_mul_right q (show 1 ≤ w by omega)
    omega
  omega

theorem slice_mono (B J : ℕ) {lo hi wLo wHi spanLo spanHi : ℕ}
    (stop : lo ≤ hi) (step : wLo ≤ wHi) (span : spanLo ≤ spanHi) (narrow : J < wLo) :
    volume lo B J wHi-volume (lo-spanLo) B J wHi ≤
      volume hi B J wLo-volume (hi-spanHi) B J wLo := by
  let s : Shape := ⟨0,B,J,0⟩
  change volume lo s.B s.J wHi-volume (lo-spanLo) s.B s.J wHi ≤
    volume hi s.B s.J wLo-volume (hi-spanHi) s.B s.J wLo
  rw [slice_eq s _ _ _ (narrow.trans_le step), slice_eq s _ _ _ narrow]
  exact shape_mono s _ _ (fun q _ j _ => min_le_min span
    ((Nat.sub_le_sub_right (Nat.add_le_add_right stop j) _).trans
      (Nat.sub_le_sub_left (Nat.mul_le_mul_right q step) _)))

def cutoff (s : Shape) (agreement h reserve : ℕ) : ℕ := s.m*agreement-2*h*reserve

def layerBound (s : Shape) (agreement reserve lo hi k a b wt : ℕ) : ℕ :=
  if (k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J then
    let stop := cutoff s agreement lo reserve-2*lo*k-(k+1)*wt
    let B := s.B-(k+1)*a
    let J := s.J-(k+1)*b
    volume stop B J (131071-hi)-volume (stop-2*hi) B J (131071-hi)
  else 0

def bound (s : Shape) (agreement reserve lo hi a b wt limit : ℕ) (slots : ℕ → ℕ) : ℕ :=
  sumCount (fun k => layerBound s agreement reserve lo hi k a b wt * slots (k+1)) limit

theorem debit_le (s : Shape) (agreement reserve lo hi h a b wt limit : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (hl : lo ≤ h) (hh : h ≤ hi) (narrow : s.J < 131071-hi)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b) :
    (∑ W ∈ range (cutoff s agreement h reserve), debitAt s h (cutoff s agreement h reserve) W a b wt slots) ≤
      bound s agreement reserve lo hi a b wt limit slots := by
  have narrow' : s.J < 131071-h := narrow.trans_le (Nat.sub_le_sub_left hh _)
  rw [← HelperWindowGrouping.grouped_eq_debit s h _ a b wt limit slots hp narrow' tail]
  unfold grouped bound
  rw [sumCount_eq, sumCount_eq]
  apply sum_le_sum
  intro k hk
  apply Nat.mul_le_mul_right
  unfold layer layerBound
  split
  · dsimp only
    have cut : cutoff s agreement h reserve ≤ cutoff s agreement lo reserve :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_right reserve (Nat.mul_le_mul_left 2 hl)) _
    have stop : cutoff s agreement h reserve-2*h*k-(k+1)*wt ≤
        cutoff s agreement lo reserve-2*lo*k-(k+1)*wt :=
      Nat.sub_le_sub_right ((Nat.sub_le_sub_right cut _).trans
        (Nat.sub_le_sub_left (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 hl)) _)) _
    exact slice_mono _ _ stop (Nat.sub_le_sub_left hh _) (Nat.mul_le_mul_left 2 hh)
      ((Nat.sub_le _ _).trans_lt narrow)
  · exact le_rfl

/-- A bank inequality certified at the two ends of an interval applies at
each integer height in it. The residual debit is bounded as a single
clipped window, preserving the cancellation between its two prefixes. -/
theorem positive (s : Shape) (agreement reserve lo hi h a b wt limit width rate nodes moment : ℕ)
    (slots : ℕ → ℕ) (hp : 0 < h) (hl : lo ≤ h) (hh : h ≤ hi) (narrow : s.J < 131071-hi)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b)
    (cert : width*nodes+hi*rate*moment+bound s agreement reserve lo hi a b wt limit slots <
      width*volume (cutoff s agreement hi reserve) s.B s.J (131071-lo)) :
    width*nodes+h*rate*moment+
        (∑ W ∈ range (cutoff s agreement h reserve), debitAt s h (cutoff s agreement h reserve) W a b wt slots) <
      width*shapeSum s (fun q j => cutoff s agreement h reserve+j-q*(131071-h)) := by
  have pay := debit_le s agreement reserve lo hi h a b wt limit slots hp hl hh narrow tail
  have pole := Nat.mul_le_mul_right moment (Nat.mul_le_mul_right rate hh)
  have cut : cutoff s agreement hi reserve ≤ cutoff s agreement h reserve :=
    Nat.sub_le_sub_left (Nat.mul_le_mul_right reserve (Nat.mul_le_mul_left 2 hh)) _
  have n := narrow.trans_le (Nat.sub_le_sub_left hh 131071)
  have src := volume_mono s cut (Nat.sub_le_sub_left hl _) n
  rw [volume_eq_shapeSum s (cutoff s agreement h reserve) (131071-h) n] at src
  have agree : shapeSum s (fun q j => cutoff s agreement h reserve+j-(131071-h)*q) =
      shapeSum s (fun q j => cutoff s agreement h reserve+j-q*(131071-h)) := by
    simp only [Nat.mul_comm (131071-h)]
  exact ((Nat.add_le_add (Nat.add_le_add_left pole _) pay).trans_lt cert).trans_le
    (Nat.mul_le_mul_left _ (src.trans_eq agree))

def slotLimit (s : Shape) (U u : ℕ) : ℕ := if u = 0 then s.J else min s.J (U/u)

private theorem slot_limit {s : Shape} {U u k : ℕ} (large : slotLimit s U u < k) :
    U < k*u ∨ s.J < k := by
  unfold slotLimit at large
  split at large
  · exact Or.inr large
  · rename_i nz
    by_cases h : s.J < k
    · exact Or.inr h
    · exact Or.inl ((Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero nz)).mp (by omega))

theorem triangle_tail (s : Shape) (a U u : ℕ) :
    ∀ k > slotLimit s U u, triSlots U u k = 0 ∨ s.B < k*a ∨ s.J < k*1 := by
  intro k large
  rcases slot_limit large with cap | slope
  · exact Or.inl (ite_eq_right (Nat.not_le.mpr cap))
  · exact Or.inr (Or.inr (by simpa only [Nat.mul_one] using slope))

def box (CAP v : ℕ) : Fin 2 → ℕ := ![CAP-v,v]
def axis (u : ℕ) : Fin 2 → ℕ := ![0,u]

theorem rectangle_tail (s : Shape) (a CAP v u : ℕ) :
    ∀ k > slotLimit s v u, rectSlots (box CAP v) (axis u) k = 0 ∨ s.B < k*a ∨ s.J < k*1 := by
  intro k large
  rcases slot_limit large with cap | slope
  · apply Or.inl
    apply ite_eq_right
    intro room
    exact (Nat.not_le.mpr cap) (room 1)
  · exact Or.inr (Or.inr (by simpa only [Nat.mul_one] using slope))

#print axioms positive
end Research6966.HelperWindowIntervals

end Merged_R6966ProofHelperWindowIntervals

end Merged6967_R6966ProofHelperWindowIntervals

section Merged6967_R6966ProofNativeSeedDegree
set_option Elab.async false



set_option Elab.async false

namespace Research6966.NativeSeedDegree
open Polynomial Finset
open K1_14 (FX Seeds Equation)
open K1_14_2 (Ambient toJet generic SeedField)
open K1_14_2_2 (Active sectionDegree mass)
open K1_14_3 (ProjectedProduct Surface)
open K1_14_2_3_2 (genericSeedLineMap genericSeedLine_degree)
open NativeSeedSlice (B Lift z back backBase scalar parameters send)
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

def seed : Seeds →+* B[X] :=
  MvPolynomial.eval₂Hom (C.comp MvPolynomial.C)
    ![(C (MvPolynomial.X 2)-C (MvPolynomial.X 0)*Polynomial.X (R:=B) : B[X]),Polynomial.X (R:=B)]
def native : Equation →+* B[X] := eval₂RingHom seed (C (MvPolynomial.X 3))
def forward : Lift →+* B[X] := MvPolynomial.eval₂Hom native ![C (MvPolynomial.X 0),C (MvPolynomial.X 1)]

theorem inverse (f:B[X]) : forward (back f)=f := by
  have eq : forward.comp back=RingHom.id _ := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [forward,back,backBase,scalar,native,seed]
      · intro i
        fin_cases i <;> simp [forward,back,backBase,parameters,z,native,seed]
    · simp [forward,back,z,native,seed]
  exact DFunLike.congr_fun eq f

private def spec (v:FX) : B →+* SeedField :=
  MvPolynomial.eval₂Hom (algebraMap FX SeedField)
    ![generic 0,0,generic 1,algebraMap FX SeedField v]

private theorem line (v:FX) (H:Equation) :
    (native H).map (spec v)=genericSeedLineMap (H.eval (MvPolynomial.C v)) := by
  have eq : (mapRingHom (spec v)).comp native=
      genericSeedLineMap.comp (evalRingHom (MvPolynomial.C v)) := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [native,seed,spec]
      · intro i
        fin_cases i <;> simp [native,seed,spec]
    · simp [native,spec]
  exact DFunLike.congr_fun eq H

private def column (H:Equation) (m:Fin 2→₀ℕ) : FX[X] :=
  ∑ j∈H.support, monomial j ((H.coeff j).coeff m)

private theorem column_coeff (H:Equation) (m:Fin 2→₀ℕ) (i:ℕ) :
    (column H m).coeff i=(H.coeff i).coeff m := by
  classical
  by_cases hi:i∈H.support
  · simp [column,finsetSum_coeff,coeff_monomial,Finsupp.single_apply,hi]
  · have hz:H.coeff i=0:=by simpa using hi
    simp [column,finsetSum_coeff,coeff_monomial,Finsupp.single_apply,hi,hz]

private theorem column_eval (H:Equation) (m:Fin 2→₀ℕ) (v:FX) :
    (column H m).eval v=(H.eval (MvPolynomial.C v)).coeff m := by
  rw [column,eval_finsetSum]
  conv_rhs => rw [eval_eq_sum,Polynomial.sum]
  rw [MvPolynomial.coeff_sum]
  apply sum_congr rfl
  intro i _
  rw [eval_monomial,←map_pow,mul_comm (H.coeff i),MvPolynomial.coeff_C_mul,mul_comm]

theorem coeff_degree (H:Equation) (i:ℕ) : (H.coeff i).totalDegree≤(native H).natDegree := by
  classical
  letI : Infinite FX := Infinite.of_injective (algebraMap (Polynomial K1_14.L) FX)
    (IsFractionRing.injective (Polynomial K1_14.L) FX)
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro m hm
  have cn:column H m≠0:=by
    intro eq
    have hz:=column_coeff H m i
    rw [eq,coeff_zero] at hz
    exact (MvPolynomial.mem_support_iff.mp hm) hz.symm
  obtain ⟨v,hv⟩ : ∃ v:FX,(column H m).eval v≠0 := by
    by_contra! all
    exact cn (Polynomial.funext (by intro x; simpa using all x))
  have mem:m∈(H.eval (MvPolynomial.C v)).support :=
    MvPolynomial.mem_support_iff.mpr ((column_eval H m v) ▸ hv)
  have ne:H.eval (MvPolynomial.C v)≠0:=by intro eq;simpa [eq] using mem
  apply (MvPolynomial.le_totalDegree mem).trans
  rw [←genericSeedLine_degree _ ne,←line]
  exact natDegree_map_le

#print axioms inverse
#print axioms coeff_degree

/-- Seed mass of the squarefree projection on any subset of the terminal
parents. The annihilator's numerator survives clearing on the generic
ordinate section, including when a particular localized ring is zero. -/
theorem projected_seed {parents:Finset Surface} {H:Equation} (proj:ProjectedProduct parents H)
    (sources:Finset (Ideal Ambient)) (active:∀ J∈sources,Active J)
    (origins:∀ q∈parents,∃ J∈sources,q.asIdeal=J.comap toJet) (i:ℕ) :
    (H.coeff i).totalDegree≤mass sources 1 := by
  classical
  obtain ⟨D,dn,deg,mult⟩:=NativeSeedSlice.common_relation proj sources active origins
  have div := map_dvd forward mult
  rw [inverse] at div
  have eq:forward (MvPolynomial.C H)=native H:=by simp [forward]
  rw [eq] at div
  exact (coeff_degree H i).trans ((natDegree_le_of_dvd div dn).trans deg)

#print axioms projected_seed
end
end Research6966.NativeSeedDegree

end Merged6967_R6966ProofNativeSeedDegree
