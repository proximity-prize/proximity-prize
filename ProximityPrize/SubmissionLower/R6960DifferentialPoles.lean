import ProximityPrize.SubmissionLower.R6960SheetNorm
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Polynomial.Resultant.Basic

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
/-- The derivative of the root is cleared by the native resultant.
The cofactors are obtained from the Sylvester identity over the base. -/
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
/-- One resultant and one power-basis discriminant clear the derivative of
every element of the normalization. The powers do not depend on the element. -/
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

/-- On a monic power-basis chart it is the square of the *same* base
discriminant that clears the derivatives of all integral elements. -/
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

/-- A function integral on the finite abscissa chart whose product with X
is integral at infinity vanishes, by the norm degree on the base line. -/
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

/-- A common pole divisor of degree at most twice the raw discriminant is
too small to support a nonzero coefficient vanishing to Frobenius order at
an unbranched infinity. This is a function-field statement on both charts. -/
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

/-- For the 69.60 height-compression parameters the largest permitted
abscissa discriminant degree occurs at ordinate degree 47. Its square has
423,539,713 degrees of room below the characteristic. -/
private def rawDegree (e : ℕ) :=
  let m:=e+1
  let H:=164632*(10*(2*e)*(2*e+1)-9*m*(m-1))/(18*m)
  (2*e-2)*H-e*(e-1)*164632

theorem profile_room :
    (∀ e : Fin 48,3≤e.val → 2*rawDegree e.val≤1707166720) ∧
    rawDegree 47=853583360 ∧ 1707166720+423539713=K1.p := by decide +kernel

/-- The simpler polynomial-weight cap used by the compression producer
also pays twice the discriminant, including the separate infinity allowance. -/
theorem coarse_room : ∀ e : Fin 48,3≤e.val →
    2*((e.val-1)*(3*e.val-2)*164632+(e.val-1))≤2105314108 ∧
    2105314108+25392325=K1.p := by decide +kernel

#print axioms profile_room
end Lower6960.DifferentialPoles
