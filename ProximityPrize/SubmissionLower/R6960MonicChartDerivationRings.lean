import ProximityPrize.SubmissionLower.R6960MonicChartPlane

set_option Elab.async false
set_option maxHeartbeats 2900000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial Lower6960.MonicChart

scoped instance (priority := 2000) chartPolyIntAlgebra : Algebra ℤ (Polynomial Scalar) :=
  Ring.toIntAlgebra _

private theorem derivation_restrict {R F : Type*} [CommRing R] [CommRing F]
    (j : R →+* F) (inj : Function.Injective j) (D : Derivation ℤ F F)
    (closed : ∀ r,∃ s,D (j r)=j s) :
    ∃ d : Derivation ℤ R R,∀ r,D (j r)=j (d r) := by
  classical
  choose d hd using closed
  let add : R →+ R := {
    toFun := d
    map_zero' := inj (by rw [←hd,map_zero,map_zero])
    map_add' r s := inj (by rw [←hd,map_add,map_add,map_add,hd,hd]) }
  let out : Derivation ℤ R R := {
    add.toIntLinearMap with
    map_one_eq_zero' := inj (by change j (d 1)=j 0; rw [←hd,map_one,D.map_one_eq_zero,map_zero])
    leibniz' r s := inj (by
      change j (d (r*s)) = j (r*d s+s*d r)
      rw [←hd,map_mul,D.leibniz,smul_eq_mul,smul_eq_mul,hd,hd,map_add,map_mul,map_mul]) }
  exact ⟨out,hd⟩

private theorem derivation_polynomial_image {K R F : Type*} [CommRing K] [CommRing R]
    [CommRing F] (g : (Polynomial K) →+* R) (j : R →+* F) (D : Derivation ℤ F F)
    (coeffs : ∀ a,∃ b,D (j (g (C a)))=j b) (gen : ∃ t,D (j (g (Polynomial.X (R:=K))))=j t)
    (p : (Polynomial K)) : ∃ q,D (j (g p))=j q := by
  obtain ⟨t,ht⟩ := gen
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p',ep⟩ := hp
    obtain ⟨q',eq⟩ := hq
    exact ⟨p'+q',by rw [map_add,map_add,map_add,ep,eq,map_add]⟩
  | monomial n a =>
    obtain ⟨a',ha⟩ := coeffs a
    refine ⟨g (C a) * ((n:R)*(g (Polynomial.X (R:=K)))^(n-1)*t) + (g (Polynomial.X (R:=K)))^n*a',?_⟩
    rw [←C_mul_X_pow_eq_monomial,map_mul,map_mul,D.leibniz,map_pow,map_pow,
      D.leibniz_pow,ha,ht]
    simp only [smul_eq_mul,nsmul_eq_mul,map_mul,map_pow,map_add,map_natCast,mul_assoc]

/-- Each coordinate derivation restricts to the finite abscissa chart. -/
theorem finite_derivation (D : Derivation ℤ ChartField ChartField)
    (on_scalars : ∀ a : Scalar,∃ b : Scalar,D (RatFunc.C a)=RatFunc.C b)
    (on_X : D RatFunc.X=1 ∨ D RatFunc.X=0) :
    ∃ d : Derivation ℤ (Polynomial Scalar) (Polynomial Scalar),∀ r,
      D (algebraMap (Polynomial Scalar) ChartField r)=algebraMap (Polynomial Scalar) ChartField (d r) := by
  let j := algebraMap (Polynomial Scalar) ChartField
  apply derivation_restrict j (IsFractionRing.injective _ _) D
  apply derivation_polynomial_image (RingHom.id _) j D
  · intro a
    obtain ⟨b,hb⟩ := on_scalars a
    exact ⟨C b,by simpa only [j,RingHom.id_apply,RatFunc.algebraMap_C] using hb⟩
  · rcases on_X with eq|eq
    · exact ⟨1,by simpa only [j,RingHom.id_apply,RatFunc.algebraMap_X,map_one] using eq⟩
    · exact ⟨0,by simpa only [j,RingHom.id_apply,RatFunc.algebraMap_X,map_zero] using eq⟩

/-- Every element of the infinity ring is a ratio of polynomials in
inverse abscissa whose denominator has nonzero constant term. -/
theorem infinity_ratio {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Infinity K) :
    ∃ p q : (Polynomial K), q.coeff 0≠0 ∧
      algebraMap (Infinity K) (RatFunc K) v = AtInfinity K p / AtInfinity K q := by
  let j := algebraMap (Polynomial K) (RatFunc K)
  obtain ⟨a,b,bmem,eq⟩ := IsFractionRing.div_surjective (Polynomial K) (v:RatFunc K)
  have bn : b≠0 := mem_nonZeroDivisors_iff_ne_zero.mp bmem
  by_cases an : a=0
  · refine ⟨0,1,by simp,?_⟩
    change (v:RatFunc K)=_
    rw [←eq,an]
    simp
  have fit : a.natDegree≤b.natDegree := by
    have val : RatFunc.inftyValuation K (j a/j b)≤1 := eq ▸ v.property
    rw [map_div₀,div_le_one₀] at val
    · change RatFunc.inftyValuationDef K (j a)≤RatFunc.inftyValuationDef K (j b) at val
      rwa [RatFunc.inftyValuation.polynomial _ an,RatFunc.inftyValuation.polynomial _ bn,
        WithZero.exp_le_exp,Int.ofNat_le] at val
    · exact (RatFunc.inftyValuation K).pos_iff.mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mpr bn)
  refine ⟨a.reflect b.natDegree,b.reverse,by rw [coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr bn,?_⟩
  change (v:RatFunc K)=_
  rw [reverse_atInfinity _ _ fit,Polynomial.reverse,reverse_atInfinity _ _ le_rfl,
    mul_div_mul_right _ _ (pow_ne_zero _ (inv_ne_zero RatFunc.X_ne_zero))]
  exact eq.symm

/-- The two derivations also restrict to the infinity valuation ring.
The abscissa derivative acts there by `-T^2` on `T = 1/X`. -/
theorem infinity_derivation [DecidableEq ChartField] (D : Derivation ℤ ChartField ChartField)
    (on_scalars : ∀ a : Scalar,∃ b : Scalar,D (RatFunc.C a)=RatFunc.C b)
    (on_X : D RatFunc.X=1 ∨ D RatFunc.X=0) :
    ∃ d : Derivation ℤ (Infinity Scalar) (Infinity Scalar),∀ r,
      D (algebraMap (Infinity Scalar) ChartField r)=algebraMap (Infinity Scalar) ChartField (d r) := by
  let j := algebraMap (Infinity Scalar) ChartField
  let g := inftyRingEval Scalar
  have Cmap (a : Scalar) : j (g (C a))=RatFunc.C a := aeval_C _ _
  have Xmap : j (g (Polynomial.X : (Polynomial Scalar)))=RatFunc.X⁻¹ := mapped_X_infty
  have hpoly : ∀ p : (Polynomial Scalar),∃ q,D (j (g p))=j q := by
    apply derivation_polynomial_image g j D
    · intro a
      obtain ⟨b,hb⟩ := on_scalars a
      exact ⟨g (C b),by rw [Cmap,Cmap,hb]⟩
    · rw [Xmap,D.leibniz_inv,smul_eq_mul]
      rcases on_X with eq|eq
      · exact ⟨-(g (Polynomial.X : (Polynomial Scalar)))^2,by rw [map_neg,map_pow,Xmap,eq,mul_one]⟩
      · exact ⟨0,by rw [eq,mul_zero,map_zero]⟩
  apply derivation_restrict j (ValuationSubring.algebraMap_injective _ ChartField) D
  intro v
  obtain ⟨p,q,qnz,eq⟩ := infinity_ratio v
  change j v=j (g p)/j (g q) at eq
  obtain ⟨a,ha⟩ := hpoly p
  obtain ⟨b,hb⟩ := hpoly q
  obtain ⟨u,hu⟩ := inftyRingEval_isUnit q qnz
  change (u : Infinity Scalar)=g q at hu
  refine ⟨(↑u⁻¹:Infinity Scalar)^2*(g q*a-g p*b),?_⟩
  rw [eq,D.leibniz_div,smul_eq_mul,smul_eq_mul,smul_eq_mul,ha,hb]
  simp only [map_mul,map_pow,map_sub,map_units_inv,hu]

#print axioms infinity_derivation
end
end Lower6960.MonicChart
