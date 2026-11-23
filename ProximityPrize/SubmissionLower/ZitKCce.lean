import ProximityPrize.SubmissionLower.ZHTtOyb
import ProximityPrize.SubmissionLower.ZInx8Od
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qG7TGJa
noncomputable section
open Polynomial
open cu (L)
open P5 (p)
open qZu9hjc (atPair jacobian gauge)
open q8Z6NHc (jo Generic form genericF genericG UniversalValue)
open scoped nonZeroDivisors
def c1 :Prop :=
  ∀ (d s a :ℕ),2≤d→d<p→d*s≤a→Finite (Zk d s a)
def c2 :Prop :=
  ∀ (d s a :ℕ),2≤d→d<p→d*s≤a →
    ∀ (b c:L),c≠0 → ∀ q:Zk d s a,
      jacobian (RingHom.id _) q.val.1 q.val.2 (genericF d s a) (genericG d s a)≠0 ∧
      gauge b c q.val.2≠0
def c3:Prop :=
  ∀ (d s a :ℕ),2≤d→d<p→d*s≤a →
    ∀ (b c:L),c≠0 → ∀ q:Zk d s a,
      jacobian (RingHom.id _) q.val.1 q.val.2 (genericF d s a) (genericG d s a)≠0 →
      gauge b c q.val.2≠0 →
      IsSeparable (aFB d s a) (value b c q.val)
private theorem atPair_hom {E F:Type} [Field E] [Field F] (j:E →+* F)
    (x y :E) (f :E[X][X]) :
    j (atPair (RingHom.id E) x y f) =
      atPair (RingHom.id F) (j x) (j y) (f.map (mapRingHom j)) := by
  rw [atPair,atPair,hom_eval₂,eval₂_map]
  apply congrArg (fun g:E[X] →+* F=>f.eval₂ g (j y))
  apply RingHom.ext
  intro q
  change j (q.eval₂ (RingHom.id E) x)=(q.map j).eval₂ (RingHom.id F) (j x)
  rw [hom_eval₂,eval₂_map,RingHom.comp_id,RingHom.id_comp]
variable {d s a :ℕ}
local notation "D" => jo d s a
local notation "K₀" => aFB d s a
local notation "GG" => Generic d s a
private theorem fixes {A K E :Type} [CommSemiring A] [Field K] [Field E]
    [Algebra A K] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
    (σ:E ≃ₐ[K] E) (v :A) :σ (algebraMap A E v)=algebraMap A E v := by
  have h:=IsScalarTower.algebraMap_apply A K E v
  exact (congrArg (fun z :E=>σ z) h).trans ((σ.commutes _).trans h.symm)
private theorem form_fixed {n:ℕ} (σ:GG ≃ₐ[K₀] GG)
    (v :q8Z6NHc.Slot d s n→D) :
    (form (fun i=>algebraMap D GG (v i))).map (mapRingHom σ.toRingHom) =
      form (fun i=>algebraMap D GG (v i)) := by
  simp only [form,Polynomial.map_sum,map_monomial,coe_mapRingHom]
  apply Finset.sum_congr rfl
  intro i _
  rw [show σ.toRingHom (algebraMap D GG (v i))=σ (algebraMap D GG (v i)) from rfl,fixes]
private def move (σ:GG ≃ₐ[K₀] GG) (q:Zk d s a) :Zk d s a :=
  ⟨(σ q.val.1,σ q.val.2),by
    have hf :=atPair_hom σ.toRingHom q.val.1 q.val.2 (genericF d s a)
    have hg:=atPair_hom σ.toRingHom q.val.1 q.val.2 (genericG d s a)
    rw [show (genericF d s a).map (mapRingHom σ.toRingHom)= _ from form_fixed σ _] at hf
    rw [show (genericG d s a).map (mapRingHom σ.toRingHom)= _ from form_fixed σ _] at hg
    rw [q.prop.1,map_zero] at hf
    rw [q.prop.2,map_zero] at hg
    exact ⟨hf.symm,hg.symm⟩⟩
private theorem value_move (σ:GG ≃ₐ[K₀] GG) (b c:L) (q:Zk d s a) :
    σ (value b c q.val)=value b c (move σ q).val := by
  change σ (value b c q.val)=value b c (σ q.val.1,σ q.val.2)
  have hf :=atPair_hom σ.toRingHom q.val.1 q.val.2 (genericF d s a).derivative
  rw [← derivative_map,
    show (genericF d s a).map (mapRingHom σ.toRingHom)= _ from form_fixed σ _] at hf
  simp only [value,qZu9hjc.gauge,map_div₀,map_pow,map_add,map_mul,fixes]
  exact congrArg (fun z :GG=>z/(qZu9hjc.gauge b c (σ q.val.2)^(d-2))) hf
private theorem descend [Fintype (Zk d s a)] (b c:L)
    (h : ∀ q:Zk d s a,IsSeparable K₀ (value b c q.val)) :
    ∃ Q:K₀[X],Q.map (algebraMap K₀ GG) =
      ∏ q:Zk d s a,((Polynomial.X:GG[X]) - C (value b c q.val)) := by
  let S:=separableClosure K₀ GG
  let v (q:Zk d s a) :S:=⟨value b c q.val,mem_separableClosure_iff.mpr (h q)⟩
  let P:S[X] := ∏ q:Zk d s a,((Polynomial.X:S[X]) - C (v q))
  have hfixed (σ:S ≃ₐ[K₀] S) :P.map σ.toRingHom=P:= by
    let τ:GG ≃ₐ[K₀] GG:=σ.liftNormal GG
    have hv (q:Zk d s a) :σ (v q)=v (move τ q) := by
      apply Subtype.ext
      exact (σ.liftNormal_commutes GG (v q)).symm.trans (value_move τ b c q)
    have hbij:Function.Bijective (move τ) :=Finite.injective_iff_bijective.mp (by
      intro q r hqr
      apply Subtype.ext
      exact Prod.ext (τ.injective (congrArg (fun t:Zk d s a=>t.val.1) hqr))
        (τ.injective (congrArg (fun t:Zk d s a=>t.val.2) hqr)))
    simp only [P,Polynomial.map_prod,Polynomial.map_sub,map_X,map_C]
    simp_rw [show ∀ z :S,σ.toRingHom z=σ z from fun _=>rfl,hv]
    exact hbij.prod_comp (fun q:Zk d s a=>(Polynomial.X:S[X]) - C (v q))
  obtain ⟨Q,hQ⟩:=(mem_lifts (f :=algebraMap K₀ S) P).mp
    ((lifts_iff_coeff_lifts P).mpr fun n =>
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (P.coeff n)).mpr fun σ=> by
        change σ.toRingHom (P.coeff n)=P.coeff n
        simpa only [coeff_map] using congrArg (fun f :S[X]=>f.coeff n) (hfixed σ))
  refine ⟨Q,?_⟩
  rw [IsScalarTower.algebraMap_eq K₀ S GG,← map_map,hQ]
  simp only [P,Polynomial.map_prod,Polynomial.map_sub,map_X,map_C]
  rfl
private theorem normalize (Q:K₀[X]) (hQ:Q≠0) :
    ∃ (R:D[X]) (t:GG),R.IsPrimitive∧t≠0 ∧
      R.map (algebraMap D GG)=C t*Q.map (algebraMap K₀ GG) := by
  let:StrongNormalizationMonoid D:=UniqueFactorizationMonoid.strongNormalizationMonoid
  let:NormalizedGCDMonoid D:=UniqueFactorizationMonoid.toNormalizedGCDMonoid D
  obtain ⟨m,hm,h⟩:=IsLocalization.integerNormalization_spec D⁰ Q
  let A:=IsLocalization.integerNormalization D⁰ Q
  let j:=algebraMap D K₀
  have hj:Function.Injective j:=IsFractionRing.injective D K₀
  have hm' : j m≠0:=(map_ne_zero_iff j hj).mpr (nonZeroDivisors.ne_zero hm)
  rw [← algebraMap_smul K₀,Polynomial.smul_eq_C_mul] at h
  change A.map j=C (j m)*Q at h
  have hA:A≠0:= fun hz=>(mul_ne_zero (C_ne_zero.mpr hm') hQ) (by
    simpa only [hz,Polynomial.map_zero] using h.symm)
  have hc:j A.content≠0 :=
    (map_ne_zero_iff j hj).mpr (fun hz=>hA (content_eq_zero_iff.mp hz))
  let u:=j m/j A.content
  have hu:u≠0:=div_ne_zero hm' hc
  have hu' : j A.content*u=j m:= by
    rw [show u=j m/j A.content from rfl,← mul_div_assoc,mul_div_cancel_left₀ _ hc]
  have hprim:A.primPart.map j=C u*Q:= by
    apply mul_left_cancel₀ (C_ne_zero.mpr hc)
    calc
      _=A.map j:= by
        simpa only [Polynomial.map_mul,Polynomial.map_C] using
          congrArg (Polynomial.map j) A.eq_C_content_mul_primPart.symm
      _=C (j m)*Q:=h
      _ = _:= by rw [← mul_assoc,← C_mul,hu']
  change A.primPart.map (algebraMap D K₀)=C u*Q at hprim
  refine ⟨A.primPart,algebraMap K₀ GG u,A.isPrimitive_primPart,
    (map_ne_zero_iff _ (algebraMap K₀ GG).injective).mpr hu,?_⟩
  simpa only [map_map,Polynomial.map_mul,Polynomial.map_C,
    ← IsScalarTower.algebraMap_eq D K₀ GG] using
    congrArg (Polynomial.map (algebraMap K₀ GG)) hprim
theorem of_children (hfinite :c1) (hgeometry :c2) (hsep:c3) :q8Z6NHc.c1 := by
  classical
  intro d s a hd hp ha b c hc
  let:=hfinite d s a hd hp ha
  let:=Fintype.ofFinite (Zk d s a)
  let e :=(Fintype.equivFin (Zk d s a)).symm
  have hg:=hgeometry d s a hd hp ha b c hc
  obtain ⟨Q,hQ⟩:=descend b c (fun q=>hsep d s a hd hp ha b c hc q (hg q).1 (hg q).2)
  have hne :Q≠0:= fun hz=>(Finset.prod_ne_zero_iff.mpr fun (q:Zk d s a) _ =>
    X_sub_C_ne_zero (value b c q.val)) (by simpa only [hz,Polynomial.map_zero] using hQ.symm)
  obtain ⟨R,t,hR,ht,hnorm⟩:=normalize Q hne
  let V:UniversalValue d s a b c :=
    { size :=Fintype.card (Zk d s a)
      pt:= fun i=>(e i).val
      distinct :=Subtype.val_injective.comp e.injective
      f_zero := fun i=>(e i).prop.1
      g_zero := fun i=>(e i).prop.2
      all_roots := fun x y hx hy =>
        ⟨e.symm ⟨(x,y),hx,hy⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩
      simple := fun i=>(hg (e i)).1
      gauge_ne := fun i=>(hg (e i)).2
      R:=R
      primitive :=hR
      scalar :=t
      scalar_ne :=ht
      product := by
        change R.map (algebraMap (jo d s a) (Generic d s a))=C t *
          ∏ i,((Polynomial.X: (Generic d s a)[X]) - C (value b c (e i).val))
        rw [e.prod_comp (fun (q:Zk d s a)=>Polynomial.X - C (value b c q.val)),hnorm,hQ] }
  exact ⟨V⟩
end
end qG7TGJa
