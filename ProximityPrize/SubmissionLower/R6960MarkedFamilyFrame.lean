import ProximityPrize.SubmissionLower.R6960MarkedPrimitiveMinor
import ProximityPrize.SubmissionLower.R6960MarkedScalarAxis

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.MarkedEvaluation
open Polynomial Module Matrix Submodule Algebra
open scoped Polynomial Matrix BigOperators
variable {k E J:Type} [Field k] [Field E] [Fintype J]
local notation "F" => FractionRing (Polynomial k)
variable [Algebra (FractionRing (Polynomial k)) E] [Algebra k E] [IsScalarTower k (FractionRing (Polynomial k)) E]
local notation "ι" => algebraMap (Polynomial k) F

/-- The primitive polynomial frame of the actual functions. Both directions
are identities in their field, so they survive every horizontal embedding. -/
theorem function_frame (v:J→E) (li:LinearIndependent k v) :
    ∃ r:ℕ, r=finrank F (span F (Set.range v)) ∧
      ∃ (w:Fin r→E) (Q:Matrix (Fin r) J (Polynomial k)) (T:Matrix J (Fin r) (Polynomial k)) (pick:Fin r↪J),
        LinearIndependent F w ∧
        (∀j,v j=∑i,ι (Q i j) • w i) ∧ (∀i,w i=∑j,ι (T j i) • v j) ∧
        (Q.submatrix _root_.id pick).det≠0 ∧ Fintype.card J≤r+(Q.submatrix _root_.id pick).det.natDegree := by
  classical
  obtain ⟨I,σ,inj,sp,ind⟩:=exists_linearIndependent' F v
  letI : Finite I:=Finite.of_injective σ inj
  letI : Fintype I:=Fintype.ofFinite I
  let r:=Fintype.card I
  let e:Fin r≃I:=(Fintype.equivFin I).symm
  let sel:Fin r↪J:=e.toEmbedding.trans ⟨σ,inj⟩
  have il:LinearIndependent F (fun i=>v (sel i)):=ind.comp e e.injective
  let U:=span F (Set.range (fun i=>v (sel i)))
  have same : U=span F (Set.range v) := by
    rw [←sp];exact congrArg (span F) (e.surjective.range_comp (v ∘ σ))
  let b : Basis (Fin r) F U:=Basis.span il
  let f (j:J):U:=⟨v j,same ▸ subset_span ⟨j,rfl⟩⟩
  let M:Matrix (Fin r) J F:=fun i j=>b.equivFun (f j) i
  let synth:(Fin r→F)→ₗ[F]E:=U.subtype.comp b.equivFun.symm.toLinearMap
  have evaluation (j:J):synth (M.col j)=v j := by
    change ((b.equivFun.symm (b.equivFun (f j)):U):E)=_
    rw [LinearEquiv.symm_apply_apply]
  have base : M.submatrix _root_.id sel=1 := by
    ext i j
    change b.repr (f (sel j)) i=_
    have ej : f (sel j)=b j := Subtype.ext (Basis.coe_span_apply il j).symm
    rw [ej,b.repr_self,Matrix.one_apply,Finsupp.single_apply]
    simp only [eq_comm]
  have liM : LinearIndependent k M.col :=
    LinearIndependent.of_comp (synth.restrictScalars k) (show LinearIndependent k (synth∘M.col) from
      (show synth∘M.col=v from funext evaluation).symm ▸ li)
  obtain ⟨Q,T,B,pick,_,rep,back,nz,sz⟩ := primitive_minor M ⟨sel,by rw [base,Matrix.det_one];exact one_ne_zero⟩ liM
  have detB:B.det≠0 := by
    have eq:1 = B.det*((Q.map ι).submatrix _root_.id sel).det := by
      have h:=congrArg Matrix.det base.symm
      rw [rep,Matrix.submatrix_mul _ _ _root_.id _root_.id sel Function.bijective_id,Matrix.submatrix_id_id,Matrix.det_mul,Matrix.det_one] at h
      exact h
    exact fun h=>one_ne_zero (eq.trans (by rw [h,zero_mul]))
  let w (j:Fin r):E:=synth (B.col j)
  have sx:Function.Injective synth:=Subtype.val_injective.comp b.equivFun.symm.injective
  have ilB:LinearIndependent F B.col:=Matrix.linearIndependent_cols_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr detB))
  have sin {A D C:Type} [Fintype D] (N:Matrix A D F) (U':Matrix D C F) (j:C) :
      (N*U').col j=∑l:D,U' l j • N.col l := by
    ext i;rw [Finset.sum_apply];simp only [Matrix.col_apply,Matrix.mul_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  refine ⟨r,?_,w,Q,T,pick,ilB.map' synth (LinearMap.ker_eq_bot_of_injective sx),?_,?_,nz,?_⟩
  · rw [←same,finrank_eq_card_basis b,Fintype.card_fin]
  · intro j
    calc v j=synth (M.col j):=(evaluation j).symm
         _ = _ := by rw [rep,sin,map_sum];simp only [map_smul,Matrix.map_apply,w]
  · intro i
    change synth (B.col i)=_
    rw [back,sin,map_sum];simp only [map_smul,Matrix.map_apply,evaluation]
  · simpa only [Fintype.card_fin] using sz

#print axioms function_frame
end Lower6960.MarkedEvaluation
