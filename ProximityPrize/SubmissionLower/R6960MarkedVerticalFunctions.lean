import ProximityPrize.SubmissionLower.R6960MarkedVerticalCharts
import ProximityPrize.SubmissionLower.R6960MarkedNativeNorm
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace Lower6960.MarkedEvaluation
open LineEuler Horner LaurentPolynomial Polynomial Module Matrix Algebra Submodule
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
end Lower6960.MarkedEvaluation
