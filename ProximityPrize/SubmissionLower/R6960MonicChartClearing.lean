import ProximityPrize.SubmissionLower.R6960MonicChartBasis

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra Module
open scoped Polynomial Differential
open private Lower6960.DifferentialPoles.resultant_norm from ProximityPrize.SubmissionLower.R6960DifferentialPoles

section Comparison

variable {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Algebra.IsSeparable F E] [FiniteDimensional F E]

/-- The original derivative resultant has the extra leading-coefficient
factor appropriate to a nonmonic polynomial. -/
private theorem original_norm (b : PowerBasis F E) (f : A[X])
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

private theorem monic_norm (v : PowerBasis F E) (g : A[X])
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

/-- The padded raw resultant is the monic chart resultant times the raw
leading coefficient and a power of the unit used in the chart. -/
theorem resultant_eq_chart (b : PowerBasis F E) (f : A[X]) (c : A) (u : Aˣ)
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

theorem chart_resultant_dvd (b : PowerBasis F E) (f : A[X]) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) (degree : f.natDegree=b.dim) (positive : 2≤f.natDegree)
    (root : aeval b.gen f=0) :
    (equation f c u).resultant (equation f c u).derivative
      (equation f c u).natDegree ((equation f c u).natDegree-1) ∣
      f.resultant f.derivative f.natDegree (f.natDegree-1) := by
  refine ⟨f.leadingCoeff*(u:A)^(2*f.natDegree-2),?_⟩
  rw [resultant_eq_chart b f c u hu degree positive root,mul_comm]

/-- The discriminant of the reciprocal power basis is represented by a
divisor of the original padded derivative resultant in the base domain. -/
theorem discriminant_dvd (b : PowerBasis F E) (f : A[X]) (c : A) (u : Aˣ)
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

/-- The square of the original padded resultant clears the derivative of
every integral element at any reciprocal chart with unit value. -/
theorem raw_square_clears (b : PowerBasis F E) (f : A[X]) (c : A) (u : Aˣ)
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
