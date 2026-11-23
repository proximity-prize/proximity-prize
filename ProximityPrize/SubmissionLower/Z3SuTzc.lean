import ProximityPrize.SubmissionLower.C
import ProximityPrize.SubmissionLower.Y
import ProximityPrize.SubmissionLower.Znc9Sbd
import ProximityPrize.SubmissionLower.ZJBzH3c
import ProximityPrize.SubmissionLower.ZeHk2sb
import ProximityPrize.SubmissionLower.ZPahZ1a
import ProximityPrize.SubmissionLower.ZwL8pvd
import ProximityPrize.SubmissionLower.Zk4hYrb
import ProximityPrize.SubmissionLower.ZVybVna
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.algebraMapSubmonoid → zTz, Algebra.rank_eq_of_equiv_equiv → zjL, Field → zrb, Fin.sum_univ_four → zmL, Function.Injective → zq4, Ideal → znc, Ideal.Quotient.isDomain_iff_prime → zMn, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.Quotient.mkₐ → zvR, Ideal.comap_map_of_surjective → zEk, Ideal.map_map → z0L, Ideal.map_span → zlN, Ideal.map_sup → zXe, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_right → zs0, Ideal.span → zye, Ideal.span_insert → zf9, IsDomain → ztn, IsFractionRing.injective → zxb, IsFractionRing.ringEquivOfRingEquiv → zDt, IsFractionRing.ringEquivOfRingEquiv_algebraMap → zNB, IsLocalization → zNo, IsLocalization.Away.lift → ztx, IsLocalization.Away.lift_eq → zaz, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algebraMap_eq → zsL, Module → zeq, Module.Finite → zAa, Module.Finite.of_surjective → zIU, Module.finrank → zsE, Module.finrank_eq_rank → z3E, Module.rank → z1x, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.X_ne_zero → zch, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.map → zDK, MvPolynomial.map_C → zpw, MvPolynomial.map_X → z7N, MvPolynomial.ringHom_ext → zXT, Nat.cast_sub → zjK, Nat.mul_le_mul_left → zBI
open _root_ renaming Nat.mul_le_mul_right → ztf, Polynomial → zM1, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.aeval → zEU, Polynomial.coe_evalRingHom → zBR, Polynomial.coe_eval₂RingHom → z4Q, Polynomial.eval → zng, Polynomial.evalRingHom → zhy, Polynomial.eval_C → zFf, Polynomial.eval_X → zB5, Polynomial.eval₂_C → zJU, Polynomial.eval₂_X → zC9, RingHom.congr_fun → zLs, RingHom.ext → zz4, RingHom.ker → zdq, RingHom.toAlgebra → z9T, Set.image_singleton → zyk
set_option maxHeartbeats 1200000
section
set_option autoImplicit true
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace qW7uFTb
noncomputable section
open gT (gk)
open ac4 (CS)
open baB
open scoped nonZeroDivisors
open private wW a1C bb3 bse from ProximityPrize.SubmissionLower.Y
open private nested gRh gRi gRj from ProximityPrize.SubmissionLower.C
abbrev B6 {k :Type} [zrb k] (H :znc (Ambient k)) (g h:Ambient k) :=
  gk (TY H g h)
abbrev parameterCardinal {k :Type} [zrb k] (H :znc (Ambient k)) (g h:Ambient k) :Cardinal :=
  @z1x (Parameters k) (zM1 (gk H)) _ _
    (pD H g h).toAlgebra.toModule
set_option backward.isDefEq.respectTransparency true in
theorem fibre_rank_domain {k :Type} [zrb k] (H :znc (Ambient k)) (g h:Ambient k) :
    z1x (CS k) (B6 H g h)=parameterCardinal H g h ∧
    (ztn (gk H)→zq4 (pD H g h) →
      ztn (B6 H g h)) := by
  let R:=Parameters k
  let S:=CS k
  let D:=zM1 (gk H)
  let B:=B6 H g h
  let f :Ambient R →+* D:=wW H g h
  let q:Ambient S →+* B:=zVv (TY H g h)
  let:zZE (Ambient R) (Ambient S) :=MvPolynomial.algebraMvPolynomial
  let M:Submonoid (Ambient R) :=R⁰.map znf
  let:zNo M (Ambient S) :=MvPolynomial.isLocalization R⁰ S
  let aRD:zZE R D :=
    @z9T R D inferInstance inferInstance (pD H g h)
  let:zeq R D:=aRD.toModule
  let:SMul R D:=aRD.toSMul
  have hk :zdq q=(zdq f).map (algebraMap (Ambient R) (Ambient S)) := by
    rw [Ideal.mk_ker,← bb3 H g h,bse]
  let q' : { p:Ambient R →+* B // zdq f≤zdq p } :=
    ⟨q.comp (algebraMap (Ambient R) (Ambient S)),by
      rw [← RingHom.comap_ker,hk]
      exact Ideal.le_comap_map⟩
  let φ:D →+* B:=f.liftOfSurjective (a1C H g h) q'
  have hφ:φ.comp f=q.comp (algebraMap (Ambient R) (Ambient S)) :=
    f.liftOfSurjective_comp (a1C H g h) q'
  let aDB:zZE D B:=φ.toAlgebra
  let:SMul D B:=aDB.toSMul
  let aRB:zZE R B:=((algebraMap S B).comp (algebraMap R S)).toAlgebra
  let:zeq R B:=aRB.toModule
  let:SMul R B:=aRB.toSMul
  let:SMul R S:=(inferInstance :zZE R S).toSMul
  let:SMul S B:=(inferInstance :zZE S B).toSMul
  let:zsf R S B:=zsL (R:=R) (S:=S) (A:=B) fun _=>rfl
  let:zsf R D B:=zsL (R:=R) (S:=D) (A:=B) fun a=> by
    change q (znf (algebraMap R S a))=φ (pD H g h a)
    have ht:=zLs hφ (znf a)
    change φ (wW H g h (znf a)) =
      q (zDK (algebraMap R S) (znf a)) at ht
    simpa only [wW,zTv,zpw] using ht.symm
  have hloc:zNo (M.map f.toMonoidHom) B :=
    IsLocalization.of_surjective M (Ambient S) f (a1C H g h) q
      zld hφ.symm hk.le
  have hparams : (M.map f.toMonoidHom)=zTz D R⁰:= by
    change (R⁰.map (znf (σ:=Fin 4)).toMonoidHom).map f.toMonoidHom =
      R⁰.map (pD H g h).toMonoidHom
    rw [Submonoid.map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    exact zTv _ _ _
  let:zNo (zTz D R⁰) B:=hparams ▸ hloc
  refine ⟨(IsFractionRing.rank_right_eq R S B).trans
    (IsLocalizedModule.rank_eq R⁰ le_rfl (IsScalarTower.toAlgHom R D B).toLinearMap),?_⟩
  intro hD hi
  let:ztn (gk H) :=hD
  refine IsLocalization.isDomain_of_le_nonZeroDivisors
    (M:=zTz D R⁰) B ?_
  exact map_le_nonZeroDivisors_of_injective (algebraMap R D) hi le_rfl
theorem axis_le_pencil {k :Type} [zrb k] (H :znc (Ambient k)) [H.IsPrime]
    (g h:Ambient k) (n:ℕ)
    (hbound:z1x (CS k) (B6 H g h)≤(n:Cardinal)) :
    zsE (CS k) (B6 H g 0)≤n:= by
  let D:=gk H
  let R:=zM1 k
  let e :=nested k
  let ρ:zM1 (zM1 k) →+* zM1 (gk H) :=
    (pD H g h).comp e.symm.toRingHom
  let τ:=Polynomial.eval₂RingHom (algebraMap k D) (zVv H g)
  let s :=zhy (0:D)
  let aRD:zZE R D:=τ.toAlgebra
  let:zeq R D:=aRD.toModule
  let:SMul R D:=aRD.toSMul
  let aPD:zZE (zM1 R) (zM1 D) :=
    @z9T (zM1 R) (zM1 D) inferInstance inferInstance ρ
  let:zeq (zM1 R) (zM1 D) :=aPD.toModule
  let aMD:zZE (Parameters k) (zM1 D) :=
    @z9T (Parameters k) (zM1 D) inferInstance inferInstance (pD H g h)
  let:zeq (Parameters k) (zM1 D) :=aMD.toModule
  have hρ (p:Parameters k) :ρ (e p)=pD H g h p:= by
    change pD H g h (e.symm (e p))= _
    rw [e.symm_apply_apply]
  have hx :ρ z7y=Polynomial.X:= by
    rw [← show e (z9v 0)=z7y from gRi,hρ,cbh]
  have hs :s.comp ρ=τ.comp (zhy 0) := by
    apply (RingHom.cancel_right (f :=e.toRingHom) e.surjective).mp
    apply zXT
    · intro a
      change s (ρ (e (znf a)))=τ (zng 0 (e (znf a)))
      rw [hρ,btq,show e (znf a)= _ from gRh a]
      simp only [s,τ,zBR,zFf,
        z4Q,zJU]
      exact zFf
    · intro i
      fin_cases i
      · change s (ρ (e (z9v 0)))=τ (zng 0 (e (z9v 0)))
        rw [hρ,cbh,show e (z9v 0)=z7y from gRi]
        simp only [s,zBR,zB5,map_zero]
      · change s (ρ (e (z9v 1)))=τ (zng 0 (e (z9v 1)))
        rw [hρ,bKf,show e (z9v 1)= _ from gRj]
        simp only [s,τ,Yn,zBR,map_add,map_mul,
          zFf,zB5,zero_mul,add_zero,
          z4Q,zC9]
        exact zFf
  have he :parameterCardinal H g h=z1x (zM1 R) (zM1 D) := by
    apply zjL e (RingEquiv.refl _)
    exact zz4 hρ
  rw [(fibre_rank_domain H g h).1,he] at hbound
  have hr :=axd.fTi ρ τ s (hx ▸ Polynomial.X_ne_zero) hs
    (fun d=>⟨z1z d,zFf⟩) n
    hbound
  let aPoly :zZE (zM1 R) (zM1 D) :=Polynomial.algebra R D
  let:zeq (zM1 R) (zM1 D) :=aPoly.toModule
  let aM0:zZE (Parameters k) (zM1 D) :=
    @z9T (Parameters k) (zM1 D) inferInstance inferInstance (pD H g 0)
  let:zeq (Parameters k) (zM1 D) :=aM0.toModule
  have h0:parameterCardinal H g 0=z1x (zM1 R) (zM1 D) := by
    apply zjL e (RingEquiv.refl _)
    apply zXT
    · intro a
      change (e (znf a)).map τ=pD H g 0 (znf a)
      rw [show e (znf a)= _ from gRh a,Polynomial.map_C,btq]
      exact congrArg z1z (zJU _ _)
    · intro i
      fin_cases i
      · change (e (z9v 0)).map τ=pD H g 0 (z9v 0)
        rw [show e (z9v 0)=z7y from gRi,Polynomial.map_X,cbh]
      · change (e (z9v 1)).map τ=pD H g 0 (z9v 1)
        rw [show e (z9v 1)= _ from gRj,Polynomial.map_C,bKf]
        simp only [τ,Yn,z4Q,zC9,map_zero,
          mul_zero,add_zero]
        rfl
  have hb:z1x (CS k) (B6 H g 0)≤(n:Cardinal) := by
    rw [(fibre_rank_domain H g 0).1,h0,rank_polynomial_polynomial R D]
    exact hr
  simpa only [zsE,Cardinal.toNat_natCast] using
    Cardinal.toNat_le_toNat hb Cardinal.natCast_lt_aleph0
end
end qW7uFTb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qW7uFTb
noncomputable section
open MvPolynomial
open gT (gk)
open ac4 (CS arW)
open scoped nonZeroDivisors
theorem quotient_rank_map {F G:Type} [zrb F] [zrb G] (e :F ≃+* G)
    (I:znc (z3y (Fin 4) F)) :
    z1x F (gk I) =
      z1x G (gk (I.map (zDK e.toRingHom))) := by
  apply zjL e (Ideal.quotientEquiv _ _ (MvPolynomial.mapEquiv _ e) rfl)
  ext x
  change zVv _ (C (e x))=zVv _
    (zDK e.toRingHom (C x))
  rw [zpw]
  rfl
theorem reverse_parameters (k :Type) [zrb k] :
    ∃ e :CS k ≃+* CS k,
      (∀ c,e (algebraMap k (CS k) c)=algebraMap k (CS k) c) ∧
      e (arW k 0)=(arW k 0)⁻¹ ∧
      e (arW k 1)=(arW k 0)⁻¹*arW k 1 := by
  let P:=z3y (Fin 2) k
  let s :P:=z9v 0
  let t:P:=z9v 1
  let L:=Localization.Away s
  let F:=CS k
  let i:=algebraMap P L
  let j:=algebraMap P F
  have hunit :IsUnit (i s) :=IsLocalization.Away.algebraMap_isUnit s
  let u:=hunit.unit
  have hu: (u:L)=i s :=hunit.unit_spec
  let g:P →+* L:=MvPolynomial.eval₂Hom (i.comp C) ![(↑u⁻¹:L),(↑u⁻¹:L)*i t]
  have gs :g s=(↑u⁻¹:L) :=zrD _ _ _
  have gt:g t=(↑u⁻¹:L)*i t:=zrD _ _ _
  have hg:IsUnit (g s) :=gs ▸ (u⁻¹).isUnit
  let f :L →+* L:=ztx s hg
  have hf (p:P) :f (i p)=g p:=zaz s hg p
  have hfu:f (↑u:L)=(↑u⁻¹:L) := by rw [hu,hf,gs]
  have hfinv :f (↑u⁻¹:L)=i s := by
    have hp:=congrArg f u.inv_mul
    simp only [map_mul,map_one,hfu] at hp
    calc
      _=f (↑u⁻¹:L)*((↑u⁻¹:L)*(↑u:L)) := by rw [u.inv_mul,mul_one]
      _ = _:= by rw [← mul_assoc,hp,one_mul,hu]
  have hff :f.comp f=RingHom.id L:= by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    apply zXT
    · intro a
      change f (f (i (C a)))=i (C a)
      have h (b:k) :f (i (C b))=i (C b) := by
        rw [hf]; exact zTv _ _ _
      rw [h,h]
    · intro a
      fin_cases a
      · change f (f (i s))=i s
        rw [hf,gs,hfinv]
      · change f (f (i t))=i t
        rw [hf,gt,map_mul,hfinv,hf,gt,← hu,← mul_assoc,u.mul_inv,one_mul]
  let eL:L ≃+* L := { f with
    invFun:=f
    left_inv :=zLs hff
    right_inv :=zLs hff }
  have hj:IsUnit (j s) :=
    isUnit_iff_ne_zero.mpr (by
      simpa only [map_zero] using (zxb P F).ne (zch (0:Fin 2)))
  let aLF:zZE L F:=(ztx s hj:L →+* F).toAlgebra
  let:SMul L F:=aLF.toSMul
  let:SMul P F:=(inferInstance :zZE P F).toSMul
  let:SMul P L:=(inferInstance :zZE P L).toSMul
  let:zsf P L F:=zsL (R:=P) (S:=L) (A:=F) fun x =>
    (zaz s hj x).symm
  let:IsFractionRing L F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers s) L F
  let e :F ≃+* F:=zDt eL
  have he (p:P) :e (j p)=algebraMap L F (g p) := by
    change e (algebraMap P F p)= _
    rw [zG3 P L F,zNB]
    change algebraMap L F (f (i p))= _
    rw [hf]
  have heinv :algebraMap L F (↑u⁻¹:L)=(j s)⁻¹:= by
    rw [map_units_inv (algebraMap L F) u,hu,← zG3 P L F]
  refine ⟨e,?_,?_,?_⟩
  · intro a
    change e (j (C a))=j (C a)
    rw [he,show g (C a)=i (C a) from zTv _ _ _]
    exact (zG3 P L F _).symm
  · change e (j s)=(j s)⁻¹
    exact (he s).trans (by rw [gs,heinv])
  · change e (j t)=(j s)⁻¹*j t
    exact (he t).trans (by rw [gt,map_mul,heinv,← zG3 P L F])
end
end qW7uFTb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qW7uFTb
noncomputable section
open MvPolynomial
open cu (FX)
open gT (Ambient gk aQ ek)
open pI (dV PI kz AU)
open ac4 (CS arW Cl)
open baB (TY a3W)
open private alK dML cGv cGu from ProximityPrize.SubmissionLower.U
private theorem map_fibreEquation {k F G:Type} [zrb k] [zrb F] [zrb G]
    (f :k →+* F) (e :F →+* G) (s t:F) (g h:z3y (Fin 4) k) :
    zDK e (a3W f s t g h) =
      a3W (e.comp f) (e s) (e t) g h:= by
  simp only [a3W,map_sub,map_add,map_mul,map_C,map_map]
private theorem map_comp {k F G:Type} [zrb k] [zrb F] [zrb G]
    (f :k →+* F) (e :F →+* G) :
    (zDK e (σ:=Fin 4)).comp (zDK f) =
      zDK (e.comp f) :=
  zz4 (MvPolynomial.map_map f e)
abbrev aHV (q:znc Ambient) (g h u v :Ambient) :znc PI :=
  q.map AU ⊔ zye
    {a3W (algebraMap FX dV) (kz 0) (kz 2) g h,
      a3W (algebraMap FX dV) (kz 1) (kz 3) u v}
abbrev iteratedIdeal (q:znc Ambient) (g h u v :Ambient) :=
  TY (TY q u v) (Cl FX g) (Cl FX h)
theorem flat_rank (q:znc Ambient) (g h u v :Ambient) :
    z1x dV (gk (aHV q g h u v)) =
      z1x (CS aQ) (gk (iteratedIdeal q g h u v)) := by
  let e :=alK
  let i:=algebraMap FX aQ
  let j:=algebraMap aQ (CS aQ)
  have hc:e.toRingHom.comp (algebraMap FX dV)=j.comp i :=
    zz4 dML
  have h0:e.toRingHom (kz 0)=arW aQ 0:=cGv 0
  have h2 :e.toRingHom (kz 2)=arW aQ 1 :=cGv 1
  have h1 :e.toRingHom (kz 1)=j (ek 0) :=cGu 0
  have h3:e.toRingHom (kz 3)=j (ek 1) :=cGu 1
  refine (quotient_rank_map e (aHV q g h u v)).trans ?_
  suffices hm: (aHV q g h u v).map (zDK e.toRingHom) =
      iteratedIdeal q g h u v by rw [hm]
  simp only [aHV,iteratedIdeal,TY,AU,Cl,
    zf9,zXe,zlN,zyk,
    z0L,map_comp,map_fibreEquation,hc,h0,h2,h1,h3]
  have he :a3W (j.comp i) (arW aQ 0) (arW aQ 1) g h =
      a3W j (arW aQ 0) (arW aQ 1)
        (zDK i g) (zDK i h) := by
    simp only [a3W,map_map]
  rw [he]
  ac_rfl
private def swapBlocks :Fin 4 ≃ Fin 4 where
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
private def swapCoefficients :dV ≃+* dV :=
  zDt (MvPolynomial.renameEquiv FX swapBlocks).toRingEquiv
private theorem swapCoefficients_parameter (i:Fin 4) :
    swapCoefficients (kz i)=kz (swapBlocks i) := by
  rw [swapCoefficients,kz,zNB]
  simp [kz]
private theorem swapCoefficients_ground (c:FX) :
    swapCoefficients (algebraMap FX dV c)=algebraMap FX dV c:= by
  change swapCoefficients (algebraMap (z3y (Fin 4) FX) dV (C c))= _
  rw [swapCoefficients,zNB]
  simp only [AlgEquiv.coe_ringEquiv,renameEquiv_apply,rename_C]
  rfl
theorem iterated_rank_comm (q:znc Ambient) (g h u v :Ambient) :
    z1x (CS aQ) (gk (iteratedIdeal q g h u v)) =
      z1x (CS aQ) (gk (iteratedIdeal q u v g h)) := by
  rw [← flat_rank q g h u v,← flat_rank q u v g h]
  refine (quotient_rank_map swapCoefficients (aHV q g h u v)).trans ?_
  suffices hm: (aHV q g h u v).map (zDK swapCoefficients.toRingHom) =
      aHV q u v g h by rw [hm]
  have hc:swapCoefficients.toRingHom.comp (algebraMap FX dV)=algebraMap FX dV :=
    zz4 swapCoefficients_ground
  have hp (i:Fin 4) :
      swapCoefficients.toRingHom (kz i)=kz (swapBlocks i) :=
    swapCoefficients_parameter i
  simp only [aHV,AU,zf9,zXe,zlN,
    zyk,z0L,map_comp,map_fibreEquation,hc,hp]
  change q.map AU ⊔
      (zye {a3W _ (kz 1) (kz 3) g h} ⊔
       zye {a3W _ (kz 0) (kz 2) u v})= _
  ac_rfl
theorem fibre_rank_reverse {k :Type} [zrb k] (H :znc (z3y (Fin 4) k)) :
    z1x (CS k) (gk (TY H (z9v 0) (z9v 1))) =
    z1x (CS k) (gk (TY H (z9v 1) (z9v 0))) := by
  obtain ⟨e,hc,hs,ht⟩:=reverse_parameters k
  refine (quotient_rank_map e (TY H (z9v 0) (z9v 1))).trans ?_
  suffices hm: (TY H (z9v 0) (z9v 1)).map
      (zDK e.toRingHom)=TY H (z9v 1) (z9v 0) by rw [hm]
  have hbase :e.toRingHom.comp (algebraMap k (CS k))=algebraMap k (CS k) :=
    zz4 hc
  simp only [TY,Cl,zXe,zlN,zyk,
    z0L,map_comp,map_fibreEquation,hbase]
  rw [show e.toRingHom (arW k 0)= _ from hs,
    show e.toRingHom (arW k 1)= _ from ht]
  have hnonzero :arW k 0≠0:= by
    simpa only [arW,map_zero] using
      (zxb (z3y (Fin 2) k) (CS k)).ne
        (zch (0:Fin 2))
  have he :a3W (algebraMap k (CS k)) (arW k 0)⁻¹
        ((arW k 0)⁻¹*arW k 1) (z9v 0) (z9v 1) =
      C ((arW k 0)⁻¹) *
        a3W (algebraMap k (CS k)) (arW k 0) (arW k 1)
          (z9v 1) (z9v 0) := by
    simp only [a3W,map_X,map_mul]
    have huv :C ((arW k 0)⁻¹)*C (arW k 0) =
        (1 :z3y (Fin 4) (CS k)) := by
      rw [← map_mul,inv_mul_cancel₀ hnonzero,map_one]
    rw [mul_sub,mul_add,← mul_assoc _ (C (arW k 0)),huv,one_mul]
    ring
  rw [he,Ideal.span_singleton_mul_left_unit
    ((isUnit_iff_ne_zero.mpr (inv_ne_zero hnonzero)).map C)]
end
end qW7uFTb
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace qW7uFTb
noncomputable section
open cu (FX L)
open gT (Ambient gk aQ Pp ek)
open pI (dV xN pN F7 ani Ik AU kz JN Z6)
open OH (Q6 aHf bfe)
open ac4 (CS arW Cl)
open baB (TY a3W cRS gLa eKX pD)
open q3rjQGe (AxisSection)
open qgscZIa (fixedAxis axisIdeal axisCoord)
open aeF (ajJ)
private abbrev jetTerm (kK:Bool) :Ambient:=if kK then z9v 3 else 0
private theorem old_degree (k E :Type) [zrb k] [zrb E] [zZE k E] (z :E) :
    aeF.FZ k z=OH.FZ k E z := by
  classical
  by_cases h:IsAlgebraic k z <;>
    simp [aeF.FZ,OH.FZ,Transcendental,h]
section
open scoped RatFunc
attribute [local instance] Polynomial.algebra
open private ad4 from ProximityPrize.SubmissionLower.C
private theorem pencil_algebra_eq (k E :Type) [zrb k] [zrb E] [zZE k E] :
    aeF.Os k (F:=E)=RatFunc.liftAlgebra k (RatFunc E) := by
  apply Algebra.algebra_ext
  suffices he : (aeF.Os k (F:=E)).algebraMap =
      (RatFunc.liftAlgebra k (RatFunc E)).algebraMap from zLs he
  apply IsFractionRing.ringHom_ext (A:=zM1 k)
  intro p
  exact (ad4 (F:=E) p).trans
    ((IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective (zM1 k) (RatFunc E)) p).symm)
private theorem line_degree_eq (k E :Type) [zrb k] [zrb E] [zZE k E] (y v :E) :
    ajJ k y v=OH.FZ (RatFunc k) (RatFunc E)
      (RatFunc.C y+RatFunc.X*RatFunc.C v) := by
  unfold ajJ
  rw [pencil_algebra_eq]
  simp only [RatFunc.algebraMap_eq_C]
  exact old_degree _ _ _
end
private theorem axis_length (q:znc Ambient) (a :Fin 2) [ztn (AxisSection q a)]
    (kK:Bool) :
    (if kK then bfe aQ (AxisSection q a) (axisCoord q a 2) (axisCoord q a 3)
      else aHf aQ (AxisSection q a) (axisCoord q a 2)) =
    zsE (CS aQ) (B6 (TY q (z9v 2) (jetTerm kK))
      (z9v (fixedAxis a)) 0) := by
  have haxis :TY q (z9v (fixedAxis a)) 0=axisIdeal q a := by
    simp only [TY,a3W,z7N,map_zero,mul_zero,add_zero,
      axisIdeal,Pp,Q6,Cl,arW,ek]
  have hcomm:=congrArg Cardinal.toNat
    (iterated_rank_comm q (z9v (fixedAxis a)) 0 (z9v 2) (jetTerm kK))
  have h:iteratedIdeal q (z9v 2) (jetTerm kK) (z9v (fixedAxis a)) 0 =
      TY (axisIdeal q a) (z9v 2)
        (if kK then z9v 3 else 0) := by
    rw [iteratedIdeal,haxis]
    cases kK <;> simp [jetTerm,Cl]
  have ht:iteratedIdeal q (z9v (fixedAxis a)) 0 (z9v 2) (jetTerm kK) =
      TY (TY q (z9v 2) (jetTerm kK)) (z9v (fixedAxis a)) 0:= by
    simp [iteratedIdeal,Cl]
  rw [h,ht] at hcomm
  refine ((show _=zsE (CS aQ)
      (B6 (axisIdeal q a) (z9v 2) (if kK then z9v 3 else 0)) from ?_)).trans
    hcomm.symm
  let: (axisIdeal q a).IsPrime :=(zMn _).mp
    (inferInstance :ztn (AxisSection q a))
  cases kK
  · simp only [Bool.false_eq_true,ite_false,cRS,gLa]
    exact (old_degree _ _ _).symm
  · simp only [ite_true,cRS,eKX]
    unfold bfe
    exact (line_degree_eq aQ (FractionRing (AxisSection q a)) _ _).symm
private theorem jet_prime (q:znc Ambient) (ha :xN q) (kK:Bool) :
    (TY q (z9v 2) (jetTerm kK)).IsPrime := by
  let:q.IsPrime :=ha.prime
  let A:=gk q
  let y :A:=zVv q (z9v 2)
  let v :A:=zVv q (jetTerm kK)
  have hy :Transcendental FX y := by
    apply transcendental_iff_injective.mpr
    have h: (zEU y :zM1 FX →ₐ[FX] A).toRingHom =
        (zVv q).comp F7:= by
      apply Polynomial.ringHom_ext
      · intro c
        change zEU y (z1z c) =
          zVv q (Polynomial.eval₂ znf (z9v 2) (z1z c))
        rw [Polynomial.aeval_C,zJU,← MvPolynomial.algebraMap_eq,
          Ideal.Quotient.mk_algebraMap]
      · change zEU y z7y =
          zVv q (Polynomial.eval₂ znf (z9v 2) z7y)
        rw [Polynomial.aeval_X,zC9]
    change zq4 ((zEU y :zM1 FX →ₐ[FX] A).toRingHom)
    rw [h]
    exact ha.ordinate_dominant
  let:Infinite FX:=Infinite.of_injective _ (zxb (zM1 L) FX)
  have hi:zq4 (pD q (z9v 2) (jetTerm kK)) :=
    bzV.eJ4 y v (Or.inl hy)
  exact (zMn _).mp
    ((fibre_rank_domain q (z9v 2) (jetTerm kK)).2 inferInstance hi)
private theorem full_rank (q:znc Ambient) (ha :xN q) (kK:Bool) :
    z1x (CS aQ) (gk
      (iteratedIdeal q (z9v 0) (z9v 1) (z9v 2) (jetTerm kK))) ≤
      (pN q (if kK then 2 else 1) :Cardinal) := by
  rw [← flat_rank]
  cases kK
  · let:zAa dV (ani q) :=ha.a6j
    change z1x dV (gk
      (aHV q (z9v 0) (z9v 1) (z9v 2) 0)) ≤
        (zsE dV (ani q) :Cardinal)
    rw [z3E]
    apply le_of_eq
    suffices h:aHV q (z9v 0) (z9v 1) (z9v 2) 0 =
        q.map AU ⊔ zye {JN,z9v 2 - znf (kz 3)} by rw [h]
    simp [aHV,a3W,JN]
  · let:zAa dV (Ik q) :=ha.bfE
    change z1x dV (gk
      (aHV q (z9v 0) (z9v 1) (z9v 2) (z9v 3))) ≤
        (zsE dV (Ik q) :Cardinal)
    rw [z3E]
    apply le_of_eq
    suffices h:aHV q (z9v 0) (z9v 1) (z9v 2) (z9v 3) =
        q.map AU ⊔ zye {JN,Z6} by rw [h]
    simp [aHV,a3W,JN,Z6]
private theorem axis_bound (q:znc Ambient) (a :Fin 2) [ztn (AxisSection q a)]
    (ha :xN q) (kK:Bool) :
    (if kK then bfe aQ (AxisSection q a) (axisCoord q a 2) (axisCoord q a 3)
      else aHf aQ (AxisSection q a) (axisCoord q a 2)) ≤
      pN q (if kK then 2 else 1) := by
  rw [axis_length]
  let H :=TY q (z9v 2) (jetTerm kK)
  let:H.IsPrime :=jet_prime q ha kK
  have hr :z1x (CS aQ) (B6 H (z9v 0) (z9v 1)) ≤
      (pN q (if kK then 2 else 1) :Cardinal) := by
    have hx (i:Fin 4) :Cl FX (z9v i) =
        (z9v i:z3y (Fin 4) aQ) :=z7N _ _
    have he :iteratedIdeal q (z9v 0) (z9v 1) (z9v 2) (jetTerm kK) =
        TY H (z9v 0) (z9v 1) := by
      simp only [iteratedIdeal,hx,H]
    exact (congrArg (fun I:znc (z3y (Fin 4) (CS aQ)) =>
      z1x (CS aQ) (gk I)) he).ge.trans (full_rank q ha kK)
  fin_cases a
  · change zsE (CS aQ) (B6 H (z9v 1) 0)≤_
    exact axis_le_pencil H (z9v 1) (z9v 0) _
      (by rwa [← fibre_rank_reverse H])
  · change zsE (CS aQ) (B6 H (z9v 0) 0)≤_
    exact axis_le_pencil H (z9v 0) (z9v 1) _ hr
theorem proof :qgscZIa.c2 := by
  intro q a _ ha _ _
  exact ⟨axis_bound q a ha false,axis_bound q a ha true⟩
end
end qW7uFTb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace q3SuTzc
theorem proof :qTplN5b.c1 := by
  intro Q _ J T z s e H g c W M F he3 heP _
  exact qeHk2sb.amplified Q J T z s P6_7_1.degree e H g c W M F he3 heP
end q3SuTzc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qdam3Tb
theorem proof :qvCjzac.c1 := by
  intro Q _ J T z s e H g c W M F he3 heP
  exact qeHk2sb.amplified Q J T z s P6_7_3.degree e H g c W M F he3 heP
end qdam3Tb
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qPeZmsc
noncomputable section
open Finset
open K1 (p)
open cu (FX Shape jz)
open gT (Ambient aQ ek Pp)
open pI (xN dual pN)
open OH
open qu56FMb
open qPP0zte (slice bR length budget plane_length budget_small)
open qpmLJKb (coord freeIdx)
open P6_7_2_3 (sectionMass Tl)
open TD (FP)
open private slice_prime component_le length_le rational_weighted from ProximityPrize.SubmissionLower.ZPYr4Qd
open private ea0 from ProximityPrize.SubmissionLower.U
open private ep8 from ProximityPrize.SubmissionLower.U
section pole
variable {A:Type} [CommRing A] [zZE aQ A]
private theorem po_zero (d:ak7 aQ A) :d.order 0=0:= by
  simpa using d.constant (0:aQ)
private theorem po_one (d:ak7 aQ A) :d.order 1=0:= by
  simpa using d.constant (1 :aQ)
private theorem po_pow (d:ak7 aQ A) (a :A) (n:ℕ) :
    d.order (a^n)≤n*d.order a := by
  induction n with
  | zero=>simp [po_one d]
  | succ n ih =>
    rw [pow_succ,Nat.succ_mul]
    exact (d.mul_le _ _).trans (Nat.add_le_add_right ih _)
private theorem po_sum (d:ak7 aQ A) {ι:Type*}
    (t:Finset ι) (f :ι→A) (N :ℕ) (h : ∀ i∈t,d.order (f i)≤N) :
    d.order (∑ i∈t,f i)≤N := by
  classical
  induction t using Finset.induction_on with
  | empty=>simp [po_zero d]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (d.add_le _ _).trans (max_le
      (h i (Finset.mem_insert_self _ _)) (ih fun j hj=>h j (Finset.mem_insert_of_mem hj)))
private theorem po_mono (d:ak7 aQ A) (z :Fin 4→A) (a :Fin 4 →₀ ℕ)
    (c:aQ) :
    d.order (algebraMap aQ A c * ∏ i,z i^a i) ≤ ∑ i,a i*d.order (z i) := by
  rw [Fin.prod_univ_four,zmL]
  have e0:=po_pow d (z 0) (a 0)
  have e1 :=po_pow d (z 1) (a 1)
  have e2 :=po_pow d (z 2) (a 2)
  have e3:=po_pow d (z 3) (a 3)
  have m0:=d.mul_le (algebraMap aQ A c)
    (z 0^a 0*z 1^a 1*z 2 ^ a 2*z 3^a 3)
  have m1 :=d.mul_le (z 0^a 0*z 1^a 1*z 2 ^ a 2) (z 3^a 3)
  have m2 :=d.mul_le (z 0^a 0*z 1^a 1) (z 2 ^ a 2)
  have m3:=d.mul_le (z 0^a 0) (z 1^a 1)
  rw [d.constant] at m0
  omega
end pole
private theorem arith {U B J a0 a1 a2 a3 o0 o1 o2 o3 ox :ℕ} (hJB:J≤B)
    (h0:a0≤U) (h1 :a1≤U) (h2 :a2+a3≤B) (h3:a3≤J)
    (hx : (o0=ox∧o1=0)∨(o0=0∧o1=ox)) :
    a0*o0+a1*o1+a2*o2+a3*o3≤U*ox+(B-J)*o2+J*max o2 o3:= by
  have hm:=ep8 hJB h2 h3 (a :=o2) (b:=o3)
  have hh:a0*o0+a1*o1≤U*ox := by
    rcases hx with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa using ztf o0 h0
    · simpa using ztf o1 h1
  omega
private theorem mk_seedBase (k :Fin 3) (Q:znc Ambient) (f :Ambient) :
    zVv (slice k Q) (Q6 f) =
      ∑ a∈f.support,algebraMap aQ (N8 ⧸ slice k Q)
        (algebraMap FX aQ (f.coeff a)) * ∏ i,coord k Q i^a i:= by
  conv_lhs=>rw [f.as_sum]
  rw [map_sum,map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Q6,MvPolynomial.map_monomial,MvPolynomial.monomial_eq,map_mul,
    Finsupp.prod_fintype _ _ (fun i=>pow_zero _),map_prod]
  simp only [map_pow]
  rfl
private theorem coord_fix (k :Fin 3) (hk :k=0∨k=1) (Q:znc Ambient) :
    coord k Q (if k=0 then 1 else 0) =
      algebraMap aQ (N8 ⧸ slice k Q) (ek 1) := by
  have h:zVv (slice k Q) (qPP0zte.direction k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (zs0 (z5J _))
  have hd:qPP0zte.direction k=z9v (if k=0 then 1 else 0) -
      znf (ek 1) := by
    rcases hk with rfl | rfl <;> simp [qPP0zte.direction,Pp]
  rw [hd,map_sub,sub_eq_zero] at h
  exact h
private theorem pole_le {k :Fin 3} (hk :k=0∨k=1) {Q:znc Ambient} {f :Ambient}
    {s :Shape} (hs :s.J≤ s.B) (hc:RectCaps s f)
    (d:ak7 aQ (N8 ⧸ slice k Q)) :
    d.order (zVv (slice k Q) (Q6 f)) ≤
      s.U*d.order (coord k Q (freeIdx k))+(s.B - s.J)*d.order (coord k Q 2) +
        s.J*max (d.order (coord k Q 2)) (d.order (coord k Q 3)) := by
  rw [mk_seedBase]
  apply po_sum
  intro a ha
  refine (po_mono d _ a _).trans ?_
  obtain ⟨h0,h1,h2,h3⟩:=hc a ha
  rw [zmL]
  have hfix :=coord_fix k hk Q
  refine arith hs h0 h1 h2 h3 ?_
  rcases hk with rfl | rfl
  · left
    refine ⟨by simp [freeIdx],?_⟩
    have :=hfix
    simp only [ite_true] at this
    rw [this,d.constant]
  · right
    have Kr : (1 :Fin 3)≠0:= by decide
    refine ⟨?_,by simp [freeIdx]⟩
    have :=hfix
    simp only [Kr,ite_false] at this
    rw [this,d.constant]
private def bDI {R:Type} [CommRing R] [zZE aQ R] (I:znc R) (a :R) :
    PrincipalCut (zVv I a) ≃ₐ[aQ] (R ⧸ (I ⊔ zye {a})) := by
  have hm: (zye {a}).map (zvR aQ I) =
      zye {zVv I a} := by
    rw [zlN,zyk]
    rfl
  let C (L:znc (R ⧸ I)) :=((R ⧸ I) ⧸ L) ≃ₐ[aQ] (R ⧸ (I ⊔ zye {a}))
  exact (congrArg C hm).mp (DoubleQuot.quotQuotEquivQuotSupₐ aQ I (zye {a}))
private theorem facts (k :Fin 3) (hk :k=0∨k=1) (Q:znc Ambient) (ha :xN Q)
    (hh:Q.height=2) (hd:dual Q) :
    (slice k Q ≠ ⊤ ∧ ringKrullDim (N8 ⧸ slice k Q)=1) ∧
      ∀ [ztn (N8 ⧸ slice k Q)],
        aHf aQ (N8 ⧸ slice k Q) (coord k Q (freeIdx k)) =
          pN Q 0 ∧
        aHf aQ (N8 ⧸ slice k Q) (coord k Q 2)≤pN Q 1 ∧
        bfe aQ (N8 ⧸ slice k Q) (coord k Q 2) (coord k Q 3) ≤
          pN Q 2 := by
  rcases hk with rfl | rfl
  · obtain ⟨hp,hn,hx⟩:=qJVcWac.proof Q 0 ha
    exact ⟨⟨hp.ne_top,hn⟩,fun {i} => ⟨@hx i,@qW7uFTb.proof Q 0 i ha hh hd⟩⟩
  · obtain ⟨hp,hn,hx⟩:=qJVcWac.proof Q 1 ha
    exact ⟨⟨hp.ne_top,hn⟩,fun {i} => ⟨@hx i,@qW7uFTb.proof Q 1 i ha hh hd⟩⟩
private theorem slice_len (s :Shape) (Q:znc Ambient) (f :Ambient) (k :Fin 3)
    (hk :k=0∨k=1) (hs :s.J≤ s.B) (ha :xN Q) (hh:Q.height=2) (hd:dual Q)
    (hf :f∉Q) (hc:RectCaps s f) :
    zAa aQ (N8 ⧸ bR k Q f) ∧
    (length (bR k Q f) :ℚ)≤budget s Q k := by
  obtain ⟨⟨hne,hdim⟩,hrest⟩:=facts k hk Q ha hh hd
  obtain ⟨hprime,hcomap⟩:=slice_prime k ha.prime hne
  have : (slice k Q).IsPrime :=hprime
  have :ztn (N8 ⧸ slice k Q) :=Ideal.Quotient.isDomain _
  obtain ⟨hx,hy,hz⟩:=hrest
  let g:N8 ⧸ slice k Q:=zVv (slice k Q) (Q6 f)
  have hg:g≠0:= by
    intro h0
    have hm:Q6 f∈slice k Q:=Ideal.Quotient.eq_zero_iff_mem.mp h0
    have hm' : f∈(slice k Q).comap Q6:=hm
    exact hf (hcomap ▸ hm')
  have eq :PrincipalCut g ≃ₐ[aQ] (N8 ⧸ bR k Q f) :=
    bDI (slice k Q) (Q6 f)
  have :zAa aQ (PrincipalCut g) :=ea0 aQ _ hdim hg
  refine ⟨zIU eq.toLinearMap eq.surjective,?_⟩
  have :CharP aQ p:=charP_of_injective_ringHom
    ((algebraMap FX aQ).comp jz).injective p
  obtain ⟨D⟩:=bzU.proof p aQ (N8 ⧸ slice k Q) hdim
    (coord k Q (freeIdx k)) (coord k Q 2) (coord k Q 3)
    (by rw [hx]; exact ha.seed_size.1) (by rw [hx]; exact ha.seed_size.2)
  have hdeg:aHf aQ (N8 ⧸ slice k Q) g ≤
      s.U*pN Q 0+(s.B - s.J)*pN Q 1+s.J*pN Q 2 := by
    refine le_trans ?_ (Nat.add_le_add (Nat.add_le_add
      (zBI s.U hx.le) (zBI (s.B - s.J) hy))
      (zBI s.J hz))
    rw [D.degree_eq g,D.degree_eq (coord k Q (freeIdx k)),D.degree_eq (coord k Q 2),
      D.line_eq]
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q _
    have hp:=ztf (D.QZ q) (pole_le hk hs hc (D.place q))
    refine hp.trans_eq ?_
    ring
  have hlength:=(cy9.proof aQ (N8 ⧸ slice k Q) hdim g hg).trans hdeg
  rw [eq.toLinearEquiv.finrank_eq] at hlength
  have hk2 :k≠2 := by rcases hk with rfl | rfl <;> decide
  have :=(Nat.cast_le (α:=ℚ)).mpr hlength
  simpa [budget,Tl,FP,sectionMass,zmL,hk2,Nat.cast_add,
    Nat.cast_mul,zjK hs,mul_assoc] using this
private theorem HE :qPP0zte.c3:= by
  intro k R _ _ _ _ Q f A w hQ hf hfin hA
  classical
  have :=hQ
  have :=hfin
  have hz {x :R} : zvR k Q x=0↔x∈Q:=Ideal.Quotient.eq_zero_iff_mem
  have hπ:Function.Surjective (zvR k Q) := fun y=>zld y
  have hQI {I:znc R} (hI:I∈A) :Q≤I:=le_sup_left.trans (hA I hI).2.1
  have hbot:Ideal.comap (zvR k Q) ⊥ = Q :=
    Ideal.ext fun x=>Ideal.mem_comap.trans (Ideal.mem_bot.trans hz)
  have hspan: (zye {f}).map (zvR k Q) =
      ⊥ ⊔ zye {zvR k Q f} := by
    rw [zlN,zyk,bot_sup_eq]
  let E :=DoubleQuot.quotQuotEquivQuotSupₐ k Q (zye {f})
  have :zAa k ((R ⧸ Q) ⧸ (⊥ ⊔ zye {zvR k Q f})) := by
    rw [← hspan]
    exact zIU E.symm.toLinearMap E.symm.surjective
  have hb:=qcYgGze.dlW (k :=k) (ι:=A) Ideal.isPrime_bot
    (fun h=>hf (hz.mp (Ideal.mem_bot.mp h)))
    (fun i=>i.val.map (zvR k Q)) (fun i=>w i.val)
    (fun i=>Or.inr (Ideal.map_isPrime_of_surjective hπ (H :=(hA _ i.2).1.isPrime)
      (fun x hx=>hQI i.2 (hz.mp (RingHom.mem_ker.mp hx)))))
    (fun i j hij _ _ he=>hij (Subtype.ext (by
      have h:=congrArg (Ideal.comap (zvR k Q)) he
      rwa [zEk _ hπ,zEk _ hπ,hbot,
        sup_eq_left.mpr (hQI i.2),sup_eq_left.mpr (hQI j.2)] at h)))
    (fun i=>sup_le bot_le ((Ideal.span_singleton_le_iff_mem _).mpr (z7X _
      ((hA _ i.2).2.1 (zs0 (z5J f))))))
    (fun i=>(hA _ i.2).2.2.1)
    (fun i hi=> by
      refine ⟨1,fun h=>hi ((Ideal.eq_top_iff_one _).mpr h),?_⟩
      obtain ⟨q,hq,m,hm,hqm⟩:=Submodule.mem_sup.mp (hA _ i.2).2.2.2
      rw [one_mul,← hqm,map_add,hz.mpr hq,zero_add,← Ideal.map_pow]
      exact z7X _ hm)
  rw [← Finset.sum_coe_sort A]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans_le (hb.trans_eq ?_)
  · rw [(DoubleQuot.quotQuotEquivQuotOfLEₐ k (hQI i.2)).toLinearEquiv.finrank_eq]
  · rw [← hspan,E.toLinearEquiv.finrank_eq]
theorem proof :qu56FMb.c1 := by
  have h2 :=q36SZud.proof
  have h3:=HE
  intro b x o Q ha hh hd hf F
  have hs : (s b).J≤(s b).B:= by cases b <;> decide
  have hlen (k :Fin 3) :zAa aQ (N8 ⧸ bR k Q F.row) ∧
      (length (bR k Q F.row) :ℚ)≤budget (s b) Q k := by
    fin_cases k
    · exact slice_len _ Q _ 0 (Or.inl rfl) hs ha hh hd F.proper F.caps
    · exact slice_len _ Q _ 1 (Or.inr rfl) hs ha hh hd F.proper F.caps
    · exact plane_length hs ha F.proper F.caps
  have hsmall (k :Fin 3) :length (bR k Q F.row)<p:= by
    exact_mod_cast (hlen k).2.trans_lt (budget_small hf k)
  have hist (k :Fin 3) :divisorMass Q F.row (r b) (fun I=>length (slice k I)) ≤
      budget (s b) Q k := by
    let:zAa aQ (N8 ⧸ bR k Q F.row) :=(hlen k).1
    exact (rational_weighted h2 h3 k ha F.proper (r b) (hsmall k)).trans (hlen k).2
  refine ⟨?_,?_,?_⟩
  · intro k hk
    rcases hk with rfl | rfl
    · change divisorMass Q F.row (r b) (fun I=>length (slice 0 I))≤_
      simpa [budget,firstMass,firstWeight,Tl,zjK hs] using hist 0
    · change divisorMass Q F.row (r b) (fun I=>length (slice 1 I))≤_
      simpa [budget,firstMass,firstWeight,Tl,zjK hs] using hist 1
  · change divisorMass Q F.row (r b) (fun I=>length (slice 2 I))≤_
    simpa [budget] using hist 2
  · intro I hi
    let:zAa aQ (N8 ⧸ bR 2 Q F.row) :=(hlen 2).1
    exact (length_le (component_le hi 2)).trans_lt (hsmall 2)
end
end qPeZmsc
end
