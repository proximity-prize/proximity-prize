import ProximityPrize.SubmissionLower.R6960MarkedGenericRuling
import ProximityPrize.SubmissionLower.R6961MarkedNativeNorm

set_option Elab.async false

-- merged module R6961MarkedVerticalFunctions
section Merged_R6961MarkedVerticalFunctions
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace Lower6961.MarkedEvaluation
open Lower6960.MarkedEvaluation
open Lower6960.LineEuler Lower6960.Horner LaurentPolynomial Polynomial Module Matrix Algebra Submodule
open scoped Polynomial Matrix BigOperators Lower6960.Horner
variable {k E J:Type} [Field k] [Field E] [Algebra (RatFunc k) E] [Algebra k E] [IsScalarTower k (RatFunc k) E]
  [Fintype J] [DecidableEq J]
local notation "Ord" => chartOrder (k:=k) (E:=E)
local notation "jF" => algebraMap (RatFunc k) E

def decodeLinear (bf:Basis J (Polynomial k) (Ord false)) : (J→Laurent k)→ₗ[k]E where
  toFun:=decode bf
  map_add' x y:=congrArg Subtype.val ((localBasis false bf).equivFun.symm.map_add x y)
  map_smul' a v:=by
    rw [show a • v=(LaurentPolynomial.C a) • v from funext (fun i=>LaurentPolynomial.smul_eq_C_mul a (v i))]
    change ((localBasis false bf).equivFun.symm ((LaurentPolynomial.C a) • v)).val=_
    rw [map_smul,Subalgebra.coe_smul,Algebra.smul_def,Algebra.smul_def]
    change jF (rationalLaurent (LaurentPolynomial.C a))*_=(algebraMap k E a)*_
    rw [rationalLaurent,LaurentPolynomial.eval₂_C,IsScalarTower.algebraMap_apply k (RatFunc k) E]
    rfl

/-- The actual rational section space in the root field represented by
the Laurent transition at twist a. -/
theorem decode_range (bf:Basis J (Polynomial k) (Ord false)) (bi:Basis J (Polynomial k) (Ord true))
    (a:ℤ) (v:E) :
    (∃u:H0 (twist a (normalizedTransition bf bi)),decode bf u.val=v) ↔
      v∈Ord false ∧ (jF RatFunc.X)^(-a)*v∈Ord true := by
  constructor
  · rintro ⟨u,rfl⟩;exact ⟨(decode_finite bf _).mp u.property.1,(decode_infinity bf bi a _).mp u.property.2⟩
  · rintro ⟨hf,hi⟩
    let w:Ord false:=⟨v,hf⟩
    let u:=(localBasis false bf).equivFun (chartOrderMap false w)
    have value:decode bf u=v := by unfold decode;rw [show (localBasis false bf).equivFun.symm u=chartOrderMap false w
      from (localBasis false bf).equivFun.symm_apply_apply _];rfl
    exact ⟨⟨u,(decode_finite bf u).mpr (value.symm ▸ hf),(decode_infinity bf bi a u).mpr (value.symm ▸ hi)⟩,value⟩

theorem span_le_global (bf:Basis J (Polynomial k) (Ord false)) (bi:Basis J (Polynomial k) (Ord true))
    (a:ℤ) {I:Type} (v:I→E) (h:∀i,v i∈Ord false ∧ (jF RatFunc.X)^(-a)*v i∈Ord true) :
    finrank k (span k (Set.range v))≤finrank k (H0 (twist a (normalizedTransition bf bi))) := by
  let G:=twist a (normalizedTransition bf bi)
  let U:=finiteLattice k J⊓transitionLattice G
  let d:= (decodeLinear bf).domRestrict U
  have fd:= (euler_index G (by
    rw [Matrix.isUnit_iff_isUnit_det,show G.det=(T (R:=k) a)^Fintype.card J*(normalizedTransition bf bi).det from Matrix.det_smul ..]
    exact ((isUnit_T a).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).mp (normalizedTransition_unit bf bi)))).1
  have : FiniteDimensional k U := fd
  have le:span k (Set.range v)≤d.range := span_le.mpr (fun _ ⟨i,eq⟩=>eq ▸ (decode_range bf bi a _).mpr (h i))
  exact (Submodule.finrank_mono le).trans (LinearMap.finrank_range_le d)

#print axioms span_le_global
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedVerticalFunctions

-- merged module R6961MarkedGenericRuling
section Merged_R6961MarkedGenericRuling
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1550000
namespace Lower6961.MarkedEvaluation
open Lower6960.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (Scalar ChartField)
open Lower6960.LineEuler Lower6960.Horner MonicFourChartDescent RetainedSurfaceClass RetainedRestrictionTorus RetainedTwistedRestriction
open Polynomial LaurentPolynomial Algebra Module Submodule Finset
open scoped Polynomial BigOperators Lower6960.Horner Lower6960.MarkedEvaluation Lower6961.MarkedEvaluation
local instance rulingScalarDecidable : DecidableEq Scalar := Classical.decEq _
local instance rulingFieldDecidable : DecidableEq ChartField := Classical.decEq _
local instance (priority:=2300) rulingScalarBase : Algebra Scalar ChartField := RatFunc.instAlgebraOfPolynomial Scalar Scalar
variable {E J:Type} [Field E] [Algebra ChartField E]
local notation "λx" => (algebraMap (Laurent Scalar) E)
local notation "aE" => algebraMap ChartField E
local notation "Ord" => chartOrder (k:=Scalar) (E:=E)

private theorem chart_constant_integral (b:Bool) (c:Scalar) :
    aE (RatFunc.C c)∈Ord b := by
  -- The affine abscissa algebra is chosen explicitly for either orientation.
  let j:(Polynomial Scalar)→+*E:= (algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom
  have co : j (Polynomial.C c)=aE (RatFunc.C c) := by
    have cc:chartEmbedding b (Polynomial.C c)=LaurentPolynomial.C c := by
      cases b <;> simp [chartEmbedding,infinityEmbedding_apply,Polynomial.toLaurent_C,invert_C]
    change aE (rationalLaurent (chartEmbedding b (Polynomial.C c)))=_
    rw [cc,rationalLaurent,LaurentPolynomial.eval₂_C]
  letI := j.toAlgebra
  exact co ▸ (isIntegral_algebraMap (A:=E) (x:=Polynomial.C c))

private theorem chart_generators (b:Bool) (p:baseChart (b,false)) :
    aE (p:ChartField)∈Ord b := by
  letI : Algebra (Polynomial Scalar) E:=((algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom).toAlgebra
  let A:Subring ChartField:=(Ord b).toSubring.comap (algebraMap ChartField E)
  have le:baseChart (b,false)≤A := by
    apply Subring.closure_le.mpr
    rintro _ (⟨r,rfl⟩ | eq | eq)
    · exact chart_constant_integral (E:=E) b (inner r)
    · change _=chartCoordinate b RatFunc.X at eq;subst_vars
      let j:(Polynomial Scalar)→+*E:= (algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom
      letI := j.toAlgebra
      have x : j Polynomial.X=aE (chartCoordinate b RatFunc.X) := by
        change aE (rationalLaurent (chartEmbedding b Polynomial.X))=_
        apply congrArg (algebraMap ChartField E)
        cases b
        · exact (RingHom.congr_fun Lower6960.Horner.rationalLaurent_finite _).trans RatFunc.algebraMap_X
        · exact (RingHom.congr_fun Lower6960.Horner.rationalLaurent_infinity _).trans (aeval_X _)
      change aE (chartCoordinate b RatFunc.X)∈Ord b
      rw [←x];exact isIntegral_algebraMap (A:=E) (x:=(Polynomial.X:(Polynomial Scalar)))
    · change _=chartCoordinate false scalarCoordinate at eq;subst_vars
      exact chart_constant_integral (E:=E) b _
  exact le p.property

private theorem enlarge_chart (b:Bool) {v:E} (reg:IsIntegral (baseChart (b,false)) v) :
    v∈Ord b := by
  let j:(Polynomial Scalar)→+*E:=(algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom
  letI := j.toAlgebra
  let R:=Ord b
  let l:(baseChart (b,false))→+*R:=((algebraMap (baseChart (b,false)) E).codRestrict R.toSubring (chart_generators b))
  obtain ⟨p,mon,root⟩:=reg
  have overR:IsIntegral R v:=⟨p.map l,mon.map _,by rw [eval₂_map];exact root⟩
  exact isIntegral_trans _ overR

private theorem seed_denom (T:Finset L) (b:Bool) :
    chartDenom E T (b,false)=aE (RatFunc.C ((algebraMap (Polynomial L) Scalar) (∏z∈T,(Polynomial.X-Polynomial.C z)))) := by
  classical
  rw [chartDenom,map_prod,map_prod,map_prod]
  apply Finset.prod_congr rfl;intro z _
  change aE (zcut (b,false) z:ChartField)=_
  rw [zcut_value,show localFrame (b,false) true=1 from rfl,div_one]
  change aE (scalarCoordinate-constants z)=_
  simp only [map_sub];rfl

theorem generic_membership (i:ℕ) (T:Finset L) (v:E) (regular:controlled E i T v) :
    v∈Ord false ∧ (aE RatFunc.X)^(-(i:ℤ))*v∈Ord true := by
  classical
  let d:=(algebraMap (Polynomial L) Scalar) (∏z∈T,(Polynomial.X-Polynomial.C z))
  have dn:d≠0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) Scalar)).mpr
    (Finset.prod_ne_zero_iff.mpr (fun z _=>X_sub_C_ne_zero z))
  have both (b:Bool) : (fr (b,false):E)⁻¹^i*v∈Ord b := by
    letI : Algebra (Polynomial Scalar) E:=((algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom).toAlgebra
    have h:=regular (b,false)
    change IsIntegral _ ((fr (b,false):E)⁻¹^i*(chartDenom E T (b,false)*v)) at h
    rw [seed_denom,mul_left_comm] at h
    have src:=enlarge_chart b h
    have result:=(Ord b).mul_mem (chart_constant_integral b d⁻¹) src
    change aE (RatFunc.C d⁻¹)*(aE (RatFunc.C d)*_ )∈_ at result
    rwa [←mul_assoc,←map_mul,←map_mul,inv_mul_cancel₀ dn,map_one,map_one,one_mul] at result
  constructor
  · simpa [fr,localFrame,axisBit] using both false
  · rw [zpow_neg,zpow_natCast,←inv_pow];exact both true

theorem actual_vertical_rank [FiniteDimensional ChartField E] [Fintype J] [DecidableEq J]
    (bf:Basis J (Polynomial Scalar) (Ord false)) (bi:Basis J (Polynomial Scalar) (Ord true))
    (s:ℕ) (positive:0<s) (deg:(normalizedTransition bf bi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ))
    (U:Finset L) (m:ℕ) (v:Fin m→E) (regular:∀j,controlled E (s-1) U (v j)) :
    finrank Scalar (span Scalar (Set.range v))+s≤Fintype.card J*s := by
  have sub:=span_le_global bf bi ((s-1:ℕ):ℤ) v (fun j=>generic_membership (s-1) U _ (regular j))
  rw [show ((s-1:ℕ):ℤ)=(s:ℤ)-1 by omega] at sub
  exact (Nat.add_le_add_right sub s).trans_eq (normalized_rank bf bi s deg)

#print axioms generic_membership
#print axioms actual_vertical_rank
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedGenericRuling
