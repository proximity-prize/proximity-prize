import ProximityPrize.SubmissionLower.R6960RetainedGlobalEvaluation
import ProximityPrize.SubmissionLower.R6960RetainedTwoLineBound

set_option Elab.async false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open Module Submodule LinearMap Polynomial LineEuler
open scoped Lower6960.RetainedSurfaceClass Polynomial
open Lower6960.RetainedSurfaceClass (nodeRing eval_subtype)
open Lower6960.RetainedSurfaceClass (cut_running through)
open Lower6960.RetainedSurfaceClass (evalX evalZ)
open Lower6960.RetainedTwoLineBound (diagonal image)
variable (E:Type) [Field E] [Algebra ChartField E]
theorem point_polynomial (j:Bool) (x z:L) (p:(Polynomial L)) :
    Lower6960.RetainedSurfaceClass.nodeRing E j x z (polyMap E j (atCoord j x z) false p) =
      algebraMap L (Crossing E x z) (p.eval (atCoord (!j) x z)) := by
  let a:=atCoord (!j) x z
  let f := (Lower6960.RetainedSurfaceClass.nodeRing E j x z).toRingHom.comp (polyMap E j (atCoord j x z) false)
  let g := (algebraMap L (Crossing E x z)).comp (evalRingHom a)
  have co (r:L) : f (C r)=algebraMap L _ r := by
    have eq : along E j false (C r)=algebraMap L (Tor E) r := eval₂_C _ _
    change Lower6960.RetainedSurfaceClass.nodeRing E j x z (Ideal.Quotient.mk _ (along E j false (C r)))=_
    rw [eq]
    exact (Lower6960.RetainedSurfaceClass.nodeRing E j x z).commutes r
  have eq : f=g := by
    apply Polynomial.ringHom_ext
    · intro r; simpa [g] using co r
    · have van : f (Polynomial.X-C a)=0 := by
        have e:=Lower6960.RetainedSurfaceClass.cut_running E j a
        change Lower6960.RetainedSurfaceClass.nodeRing E j x z (Ideal.Quotient.mk _ (along E j false (Polynomial.X-C a)))=0
        rw [e]
        cases j
        · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
        · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _)))
      rw [map_sub,co,sub_eq_zero] at van
      simpa [g] using van
  exact DFunLike.congr_fun eq p
theorem node_rank_le (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0) {n:ℕ}
    (bf:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) false)) :
    finrank L (Crossing E x z)≤n := by
  let c:=atCoord j x z
  let F:=(nodeMap E j x z).comp (chartImage E j c false).subtype
  let v (i:Fin n):=F (bf i)
  let generate := (Pi.basisFun L (Fin n)).constr L v
  have action (r:(Polynomial L)) (u:chartImage E j c false) :
      F (r • u) = (r.eval (atCoord (!j) x z)) • F u := by
    change nodeMap E j x z (polyMap E j c false r*u.val)=_
    have eq:=map_mul (Lower6960.RetainedSurfaceClass.nodeRing E j x z) (polyMap E j c false r) u.val
    rw [point_polynomial] at eq
    cases j <;> exact eq
  have onto : Function.Surjective generate := by
    intro y
    obtain ⟨u,eu⟩:=onto_at_node E j x z nx nz y
    refine ⟨fun i=>(bf.repr u i).eval (atCoord (!j) x z),?_⟩
    have rep:=congrArg F (bf.sum_repr u)
    rw [map_sum] at rep
    simp_rw [action] at rep
    simpa [generate,Basis.constr_apply_fintype,v] using rep.trans eu
  have bound:=LinearMap.finrank_le_finrank_of_surjective (f:=generate) onto
  simpa only [Module.finrank_pi,Fintype.card_fin] using bound
def transition (j:Bool) (c:L) (nc:c≠0) {n:ℕ} (bf:Basis (Fin n) (Polynomial L) (chartImage E j c false))
    (bi:Basis (Fin n) (Polynomial L) (chartImage E j c true)) : Matrix (Fin n) (Fin n) (Laurent L) := by
  let : Module (Laurent L) (Axis E j c) := (axisAlgebra E j c).toModule
  exact freeTransition (M:=Axis E j c) bf bi (nativeMap E j c false) (nativeMap E j c true)
    (native_localization E j c nc false) (native_localization E j c nc true)
theorem paired_bound (x z:L) (nx:x≠0) (nz:z≠0) [IsReduced (Crossing E x z)]
    [FiniteDimensional L (Crossing E x z)] {m n:ℕ}
    (xf:Basis (Fin m) (Polynomial L) (chartImage E false x false)) (xi:Basis (Fin m) (Polynomial L) (chartImage E false x true))
    (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true)) :
    FiniteDimensional L (Paired E x z) ∧ ∃ s t:ℕ,
      (transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ) ∧
      (transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) ∧
      finrank L (Paired E x z)≤s+t := by
  obtain ⟨fx,f1x,tx,xt,ex⟩:=native_euler E false x nx xf xi
  obtain ⟨fz,f1z,tz,zt,ez⟩:=native_euler E true z nz zf zi
  let C:=Crossing E x z
  let dx:=difference E false x
  let dz:=difference E true z
  let exv:=Lower6960.RetainedSurfaceClass.evalX E x z
  let ezv:=Lower6960.RetainedSurfaceClass.evalZ E x z
  have rx : dx.range=chartImage E false x false⊔chartImage E false x true := Lower6960.RetainedTwoLineBound.image ..
  have rz : dz.range=chartImage E true z false⊔chartImage E true z true := Lower6960.RetainedTwoLineBound.image ..
  have : FiniteDimensional L ((Axis E false x) ⧸ dx.range) := rx ▸ f1x
  have : FiniteDimensional L ((Axis E true z) ⧸ dz.range) := rz ▸ f1z
  obtain ⟨finite,bound⟩:=RetainedNodalIndex.dimension dx dz exv ezv
  let W:=dx.ker.map exv ⊔ dz.ker.map ezv
  have : FiniteDimensional L C := (inferInstance : FiniteDimensional L (Crossing E x z))
  have : FiniteDimensional L W := FiniteDimensional.of_injective
    (W.subtype : W→ₗ[L]C) Subtype.val_injective
  let hz:LineGlobals E true z→ₗ[L] C := (nodeMap E true x z).comp (chartImage E true z false⊓chartImage E true z true).subtype
  have : FiniteDimensional L (LineGlobals E true (atCoord true x z)) := fz
  have : FiniteDimensional L (LineGlobals E false (atCoord false x z)) := fx
  have injz :=global_eval_injective E true x z nx nz zf
  have lift (v:LineGlobals E true z) : hz v∈W := Submodule.mem_sup_right
    ⟨(Lower6960.RetainedTwoLineBound.diagonal _ _ v).val,(Lower6960.RetainedTwoLineBound.diagonal _ _ v).property,rfl⟩
  let into:=hz.codRestrict W lift
  have covered:=LinearMap.finrank_le_finrank_of_injective (f:=into)
    (fun u v eq=>injz (congrArg (fun w:W=>(w:C)) eq))
  have hx:=LinearMap.finrank_le_finrank_of_injective (global_eval_injective E false x z nx nz xf)
  have hz':=LinearMap.finrank_le_finrank_of_injective injz
  have rankx:=node_rank_le E false x z nx nz xf
  have rankz:=node_rank_le E true x z nx nz zf
  rw [rx,rz] at bound
  change finrank L (Paired E x z)+finrank L W ≤finrank L (LineObstructions E false x)+finrank L (LineObstructions E true z)+finrank L C at bound
  change finrank L (LineGlobals E false x)≤finrank L C at hx
  change finrank L (LineGlobals E true z)≤finrank L C at hz'
  change finrank L (LineGlobals E true z)≤finrank L W at covered
  change finrank L C≤m at rankx
  change finrank L C≤n at rankz
  let s:=(-tz).toNat
  let t:=(-tx).toNat
  have ds:tz= -(s:ℤ) := by dsimp [s]; omega
  have dt:tx= -(t:ℤ) := by dsimp [t]; omega
  exact ⟨finite,s,t,dt ▸ xt,ds ▸ zt,by omega⟩
open RetainedCompression (Curve ordinate view height heightCap)




















end Lower6960.RetainedSurfaceClass
