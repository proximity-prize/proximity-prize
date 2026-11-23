import ProximityPrize.SubmissionLower.R6960CollisionTamePlaneDiscriminant
import Mathlib.RingTheory.Trace.Basic

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open CollisionTame Module Algebra Matrix Polynomial

variable {A B F K E : Type*}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B]
    [Field F] [Field K] [Field E]
    [Algebra A F] [IsFractionRing A F] [Algebra B K] [IsFractionRing B K]
    [Algebra A E] [Algebra B E] [Algebra F E] [Algebra K E]
    [IsScalarTower A F E] [IsScalarTower B K E]
    [FiniteDimensional F E] [FiniteDimensional K E]
    [Algebra.IsSeparable F E] [Algebra.IsSeparable K E]

/-- The same normalized surface has the same trace-discriminant ideal
in different coordinates, under the literal base-ring isomorphism. -/
theorem discriminant_transport (e:A≃+*B) (f:F≃+*K)
    (base : ∀ a,algebraMap B K (e a)=f (algebraMap A F a))
    (root : ∀ x,algebraMap K E (f x)=algebraMap F E x) :
    (normalizationDiscriminant (A:=A) (E:=E) F).map e.toRingHom =
      normalizationDiscriminant (A:=B) (E:=E) K := by
  classical
  have hbase (a:A) : algebraMap B E (e a)=algebraMap A E a := by
    rw [IsScalarTower.algebraMap_apply B K E,base,root,←IsScalarTower.algebraMap_apply]
  have int (x:E) : IsIntegral A x↔IsIntegral B x := by
    constructor
    · rintro ⟨p,pm,hp⟩
      refine ⟨p.map e.toRingHom,pm.map _,?_⟩
      rw [eval₂_map,show (algebraMap B E).comp e.toRingHom=algebraMap A E from RingHom.ext hbase]
      exact hp
    · rintro ⟨p,pm,hp⟩
      have back (b:B) : algebraMap A E (e.symm b)=algebraMap B E b := by rw [←hbase,e.apply_symm_apply]
      refine ⟨p.map e.symm.toRingHom,pm.map _,?_⟩
      rw [eval₂_map,show (algebraMap A E).comp e.symm.toRingHom=algebraMap B E from RingHom.ext back]
      exact hp
  let Q : integralClosure A E≃integralClosure B E := {
    toFun := fun a=>⟨a,(int _).mp a.property⟩
    invFun := fun b=>⟨b,(int _).mpr b.property⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }
  let b := Module.finBasis F E
  let c := b.mapCoeffs f (fun a x=>by simp only [Algebra.smul_def,root])
  have eq : finrank K E=finrank F E :=
    (finrank_eq_card_basis c).trans (Fintype.card_fin _)
  have tr (x:E) : f (Algebra.trace F E x)=Algebra.trace K E x := by
    have same : (algebraMap K E).comp f.toRingHom=
      (RingEquiv.refl E).toRingHom.comp (algebraMap F E) := RingHom.ext root
    have h := Algebra.trace_eq_of_equiv_equiv f (RingEquiv.refl E) same x
    exact (congrArg f h).trans (f.apply_symm_apply _)
  let u := integralTraceForm (A:=A) (E:=E) F
  let v := integralTraceForm (A:=B) (E:=E) K
  have fm (a b:integralClosure A E) : e (u a b)=v (Q a) (Q b) := by
    apply IsFractionRing.injective B K
    rw [base]
    change f (algebraMap A F (integralTraceForm (A:=A) (E:=E) F a b)) =
      algebraMap B K (integralTraceForm (A:=B) (E:=E) K (Q a) (Q b))
    rw [integralTraceForm_map,integralTraceForm_map]
    exact tr _
  let I := Fin (finrank F E)
  have det (a:I→integralClosure A E) : e ((tupleGram u a).det) = (tupleGram v (Q ∘ a)).det := by
    have mat : (tupleGram u a).map e=(tupleGram v (Q ∘ a)) := by
      apply Matrix.ext
      intro i l
      exact fm (a i) (a l)
    exact (e.toRingHom.map_det _).trans (congrArg Matrix.det mat)
  unfold normalizationDiscriminant
  rw [eq]
  change (gramIdeal (ι:=I) u).map e.toRingHom=gramIdeal (ι:=I) v
  apply le_antisymm
  · apply (Ideal.map_le_iff_le_comap).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change e (tupleGram u a).det∈gramIdeal (ι:=I) v
    rw [det]
    exact gramIdeal_mem v _
  · apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    have h : Q ∘ (Q.symm ∘ a)=a := by funext i; exact Q.apply_symm_apply (a i)
    have hd := det (Q.symm ∘ a)
    rw [h] at hd
    change (tupleGram v a).det∈(gramIdeal (ι:=I) u).map e.toRingHom
    rw [←hd]
    exact Ideal.mem_map_of_mem e.toRingHom (gramIdeal_mem u (Q.symm ∘ a))

#print axioms discriminant_transport
end
end Lower6960.CollisionMarked
