import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactCoefficientFieldTrdeg6731Research
import ProximityPrize.SubmissionLower.ContactCoefficientCurveTrdegAtMostOne6731Research
import ProximityPrize.SubmissionLower.ContactMovingPoleTransport6719Research
namespace ProximityPrize.SubmissionLower.ContactCoefficientBaseChange6731Research
open ContactCoefficientFieldTrdeg6731Research
open ContactCoefficientCurveTrdegAtMostOne6731Research ContactLocalPoleBound
open ContactMovingPoleTransport6719Research ActualCurveCoordinateField
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000
variable {K k L:Type} [Field K] [Field k] [Field L]
  [Algebra K k] [Algebra K L] [Algebra k L] [IsScalarTower K k L]
theorem baseCoefficientField_trdeg_le_one_of_algebraic_constants
    [Algebra.IsAlgebraic K k] (P:Polynomial L) (γ:L)
    (htr:Algebra.trdeg K (baseCoefficientField (k:=K) P γ) ≤ 1):
    Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
  let S:Set L:=insert γ (Set.range (fun j:ℕ => P.coeff j))
  let BK:IntermediateField K L:=baseCoefficientField (k:=K) P γ
  let Bk:IntermediateField k L:=baseCoefficientField (k:=k) P γ
  let BkK:IntermediateField K L:=Bk.restrictScalars K
  have hBK:BK ≤ BkK:=by
    change IntermediateField.adjoin K S ≤ BkK
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    change z∈Bk
    exact IntermediateField.subset_adjoin k S hz
  let inc:BK →ₐ[K] Bk:={
    toFun:=fun z => ⟨z,hBK z.2⟩
    map_one':=rfl
    map_mul':=fun _ _ => rfl
    map_zero':=rfl
    map_add':=fun _ _ => rfl
    commutes':=fun _ => rfl}
  letI:Algebra BK Bk:=inc.toRingHom.toAlgebra
  letI:IsScalarTower K BK Bk:=
    IsScalarTower.of_algebraMap_eq fun c => (inc.commutes c).symm
  letI:IsScalarTower BK Bk L:=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ACL:IntermediateField BK L:=algebraicClosure BK L
  have hkACL (c:k):algebraMap k L c∈ACL:=by
    apply mem_algebraicClosure_iff.mpr
    have hcK:IsAlgebraic K (algebraMap k L c):=
      (Algebra.IsAlgebraic.isAlgebraic c).algebraMap
    exact hcK.tower_top BK
  let ACLk:IntermediateField k L:=
    ACL.toSubfield.toIntermediateField hkACL
  have hBkACL:Bk ≤ ACLk:=by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    change z∈ACL
    have hzBK:z∈BK:=IntermediateField.subset_adjoin K S hz
    simpa only [IntermediateField.algebraMap_apply] using
      ACL.algebraMap_mem (⟨z,hzBK⟩:BK)
  letI:Algebra.IsAlgebraic BK Bk:=⟨fun z => by
    apply (isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom BK Bk L) (algebraMap Bk L).injective).mp
    apply mem_algebraicClosure_iff.mp
    exact hBkACL z.2⟩
  have hzeroE:Algebra.trdeg BK Bk=0:=trdeg_eq_zero
  have hsumE:Algebra.trdeg K BK+Algebra.trdeg BK Bk=Algebra.trdeg K Bk:=
    trdeg_add_eq K BK
  have hKBk:Algebra.trdeg K Bk ≤ 1:=by
    rw [←hsumE,hzeroE,add_zero]
    exact htr
  have hzerok:Algebra.trdeg K k=0:=trdeg_eq_zero
  have hsumk:Algebra.trdeg K k+Algebra.trdeg k Bk=Algebra.trdeg K Bk:=
    trdeg_add_eq K k
  rw [hzerok,zero_add] at hsumk
  exact hsumk.symm ▸ hKBk
theorem coefficient_pole_le_of_trdeg_le_one
    {Ω:Type} [Field Ω] [IsAlgClosed k]
    [Algebra k Ω] [Algebra Ω L] [IsScalarTower k Ω L]
    (P:Polynomial L) (γ:L) (w:ℕ) (hP:P.natDegree ≤ w)
    (htr:Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1)
    (x:Ω) (hx:Transcendental k x) (y:L)
    (hy:P.eval (algebraMap Ω L x)=y)
    (v:CoordinatePoleMass.Place Ω L) (j:ℕ):
    poleOrder v.val (P.coeff j) ≤ poleOrder v.val y:=by
  letI:v.val.IsTrivialOn Ω:=v.property.2
  let B:IntermediateField k L:=baseCoefficientField (k:=k) P γ
  have hcoeff (n:ℕ):P.coeff n∈B:=by
    exact IntermediateField.subset_adjoin k _ (Or.inr ⟨n,rfl⟩)
  by_cases hj:j < w+1
  · let i:Fin (w+1):=⟨j,hj⟩
    let a:Fin (w+1) → B:=fun n => ⟨P.coeff n,hcoeff n⟩
    let φ:B →+*L:=B.val.toRingHom
    have hcompat:∀ c:k,φ (algebraMap k B c)=
        algebraMap Ω L (algebraMap k Ω c):=by
      intro c
      exact IsScalarTower.algebraMap_apply k Ω L c
    have hsum:(∑ n,φ (a n)*(algebraMap Ω L x)^(n:ℕ))=
        P.eval (algebraMap Ω L x):=by
      rw [P.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
      rw [←Fin.sum_univ_eq_sum_range]
      change (∑ n:Fin (w+1),P.coeff (n:ℕ)*
        (algebraMap Ω L x)^(n:ℕ))=_
      rfl
    have hle:=coefficient_pole_le_generic_evaluation_of_trdeg_le_one
      v.val φ hcompat htr x hx a i
    change poleOrder v.val (P.coeff i) ≤
      poleOrder v.val (∑ n,φ (a n)*(algebraMap Ω L x)^(n:ℕ)) at hle
    rw [hsum,hy] at hle
    simpa only [i] using hle
  · have hz:P.coeff j=0:=Polynomial.coeff_eq_zero_of_natDegree_lt
      (hP.trans_lt (by omega))
    rw [hz]
    simp only [poleOrder,map_zero,WithZero.log_zero,max_self]
    exact le_max_left _ _
end
end ProximityPrize.SubmissionLower.ContactCoefficientBaseChange6731Research
