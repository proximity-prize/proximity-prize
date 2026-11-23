import ProximityPrize.SubmissionLower.Zsty7Cb
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Z0SAUab
import ProximityPrize.SubmissionLower.Zl6SIrc
import ProximityPrize.SubmissionLower.Zqop1Ec
set_option Elab.async false
open _root_ renaming Fin.lastCases_last → zTz, Ideal → znc, Ideal.Quotient.mk → zVv, Ideal.comap_comap → zg6, Ideal.comap_isPrime → zG1, Ideal.comap_mono → zOS, Ideal.map_le_iff_le_comap → zo0, Ideal.map_mono → zi2, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_right → zs0, Ideal.span_singleton_le_iff_mem → zvl, IsLocalization.Away.invSelf → zdx, IsLocalization.Away.lift → ztx, IsLocalization.Away.lift_comp → zOe, IsLocalization.map_under → zvH, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.ringHom_ext → zXT, RingHom.congr_fun → zLs, Submonoid.powers → zSL
section
set_option autoImplicit true
namespace qEAwGBc
noncomputable section
open aR (af)
open dN (GeoField GeoJets pK bC)
open vS (g9)
open B8 (cylinder qK cak i9)
open qCj6p1d (ChartRing qR graph yu sigma)
open qsnQ6jb (Iu)
open private aRT.four_ne_zero aQB cqK from ProximityPrize.SubmissionLower.BI
open private bEj from ProximityPrize.SubmissionLower.A1
variable (g:af 4)
private theorem on_old: (yu g).comp qK=qR g:= by
  apply zXT
  · intro a
    simp [qK,yu]
  · intro i
    simp [qK,yu]
private theorem on_old_apply (D:GeoJets) :yu g (qK D)=qR g D :=
  zLs (on_old g) D
private theorem bHD:graph g=qK (bC (pK g)) +
    qK (znf (4 :GeoField)*sigma g)*z9v (Fin.last 4) := by
  simp [graph,qK]
private theorem on_graph:yu g (graph g)=0:= by
  rw [bHD,map_add,map_mul,on_old_apply,on_old_apply,map_mul]
  have hx :yu g (z9v (Fin.last 4)) =
      qR g (znf (-(4 :GeoField)⁻¹)*bC (pK g)) *
        zdx (sigma g) := by
    rw [yu,zrD,zTz]
  have hs :qR g (sigma g)* zdx (sigma g)=1 :=
    IsLocalization.Away.mul_invSelf (sigma g)
  have h4 :qR g (znf (4 :GeoField)) *
      qR g (znf (-(4 :GeoField)⁻¹)) = -1 := by
    rw [← map_mul,← map_mul,mul_neg,mul_inv_cancel₀ aRT.four_ne_zero,
      map_neg,map_one,map_neg,map_one]
  rw [hx,map_mul]
  calc
    _=qR g (bC (pK g)) +
        (qR g (znf (4 :GeoField)) *
          qR g (znf (-(4 :GeoField)⁻¹))) *
        (qR g (sigma g)* zdx (sigma g)) *
        qR g (bC (pK g)) := by ac_rfl
    _=0:= by rw [h4,hs,mul_one,neg_one_mul,add_neg_cancel]
private theorem d5Y {A:Type*} [CommRing A] (k :g9 →+* A)
    (hs :IsUnit (k (qK (sigma g)))) (hg:k (graph g)=0) :
    k=(ztx (sigma g) (g:=k.comp qK) hs).comp (yu g) := by
  let φ:ChartRing g →+* A:=ztx (sigma g) (g:=k.comp qK) hs
  let ψ:=φ.comp (yu g)
  have hold (D:GeoJets) :ψ (qK D)=k (qK D) := by
    change φ (yu g (qK D))= _
    rw [on_old_apply]
    exact IsLocalization.Away.lift_eq (sigma g) hs D
  have hψ:ψ (graph g)=0:= by simp [ψ,on_graph]
  change k=ψ
  apply zXT
  · intro a
    simpa [qK] using (hold (znf a)).symm
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [bHD,map_add,map_mul] at hg hψ
      rw [hold,hold] at hψ
      have hu:IsUnit (k (qK (znf (4 :GeoField)*sigma g))) := by
        rw [map_mul,map_mul]
        exact ((isUnit_iff_ne_zero.mpr aRT.four_ne_zero).map
          (k.comp (qK.comp znf))).mul hs
      exact hu.mul_right_inj.mp (add_left_cancel (hg.trans hψ.symm))
    · simpa [qK] using (hold (z9v j)).symm
private theorem lift_comap (P:znc GeoJets) (hP:P.IsPrime) (hs :sigma g∉P) :
    (Iu g P).comap qK=P:= by
  rw [Iu,zg6,on_old]
  ext D
  change qR g D∈P.map (qR g)↔D∈P
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (zSL (sigma g)) (ChartRing g)]
  constructor
  · rintro ⟨m,⟨n,rfl⟩,hm⟩
    exact (hP.mem_or_mem hm).resolve_left (fun h=>hs (hP.mem_of_pow_mem n h))
  · intro hD
    exact ⟨1,(zSL (sigma g)).one_mem,by simpa using hD⟩
private theorem lift_prime (P:znc GeoJets) (hP:P.IsPrime) (hs :sigma g∉P) :
    (Iu g P).IsPrime := by
  have hdis :Disjoint (↑(zSL (sigma g)) :Set GeoJets) P:= by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨n,rfl⟩ hn
    exact hs (hP.mem_of_pow_mem n hn)
  let: (P.map (qR g)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (zSL (sigma g)) (ChartRing g) P hP hdis
  exact zG1 (yu g) _
private theorem lift_contains (P:znc GeoJets) :graph g∈Iu g P:= by
  change yu g (graph g)∈P.map (qR g)
  rw [on_graph]
  exact Ideal.zero_mem _
private theorem cylinder_le (P:znc GeoJets) :cylinder P≤Iu g P:= by
  rw [cylinder,zo0,Iu,zg6,on_old]
  exact Ideal.le_comap_map
private theorem eq_lift (J:znc g9) (hJ:J.IsPrime) (hs :qK (sigma g)∉J)
    (hg:graph g∈J) :J=Iu g (J.comap qK) := by
  let:=hJ
  let A:=FractionRing (g9 ⧸ J)
  let k :=(algebraMap (g9 ⧸ J) A).comp (zVv J)
  have hk (x :g9) :k x=0↔x∈J:= by
    change algebraMap (g9 ⧸ J) A (zVv J x)=0↔_
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _),Ideal.Quotient.eq_zero_iff_mem]
  have hs' : IsUnit (k (qK (sigma g))) :=isUnit_iff_ne_zero.mpr (mt (hk _).mp hs)
  let φ:ChartRing g →+* A:=ztx (sigma g) (g:=k.comp qK) hs'
  have hφ:φ.comp (qR g)=k.comp qK:=zOe (sigma g) hs'
  have hker : (RingHom.ker φ).comap (qR g)=J.comap qK:= by
    ext x
    change φ (qR g x)=0↔qK x∈J
    rw [show φ (qR g x)=k (qK x) from zLs hφ x,hk]
  rw [Iu,← hker,zvH (zSL (sigma g)) (ChartRing g)]
  ext D
  change D∈J↔φ (yu g D)=0
  exact (hk D).symm.trans (Iff.of_eq (congrArg (fun j:g9 →+* A=>j D =0)
    (d5Y g k hs' ((hk _).mpr hg))))
private theorem eky (P:znc GeoJets) (hP:P.IsPrime) (hs :sigma g∉P) :
    graph g∉cylinder P:= by
  intro h
  have hm (x :GeoJets) :aQB x (graph g)∈P:= by
    have hle :cylinder P≤P.comap (aQB x) := by
      rw [cylinder,zo0,zg6,cqK,Ideal.comap_id]
    exact hle h
  have evalGraph (x :GeoJets) :aQB x (graph g) =
      bC (pK g)+(znf (4 :GeoField)*sigma g)*x := by
    have ho (D:GeoJets) :aQB x (qK D)=D :=
      zLs (cqK x) D
    rw [bHD,map_add,map_mul,ho,ho]
    rw [aQB,zrD,zTz]
  have h0:=hm 0
  have h1 :=hm 1
  rw [evalGraph,mul_zero,add_zero] at h0
  rw [evalGraph,mul_one] at h1
  have hmem:=(P.add_mem_iff_right h0).mp h1
  have hu:IsUnit (znf (4 :GeoField) :GeoJets) :=
    (isUnit_iff_ne_zero.mpr aRT.four_ne_zero).map znf
  exact hs ((hP.mem_or_mem hmem).resolve_left (fun hc=>hP.ne_top (P.eq_top_of_isUnit_mem hc hu)))
private theorem eku (P:znc GeoJets) (hP:P.IsPrime) (hs :sigma g∉P) :
    (i9 (cylinder P) (graph g)).IsMinimalPrime (Iu g P) := by
  refine ⟨⟨lift_prime g P hP hs,sup_le (cylinder_le g P)
    ((zvl _).mpr (lift_contains g P))⟩,?_⟩
  intro J hJ hJG
  have hsJ:qK (sigma g)∉J:= by
    intro h
    have hm:sigma g∈(Iu g P).comap qK:=hJG h
    rw [lift_comap g P hP hs] at hm
    exact hs hm
  have hg:graph g∈J:=hJ.2 (zs0 (z5J _))
  have hle :P≤J.comap qK:=Ideal.map_le_iff_le_comap.mp (le_sup_left.trans hJ.2)
  rw [eq_lift g J hJ.1 hsJ hg]
  exact zOS (zi2 hle)
theorem proof :qsnQ6jb.c1 := by
  intro g
  refine ⟨on_old g,lift_comap g,lift_prime g,lift_contains g,cylinder_le g,eq_lift g,?_⟩
  intro P hP hs hZ hd
  have hp:=eky g P hP hs
  have hm:=eku g P hP hs
  exact ⟨hp,⟨hm,cak hm⟩,bEj (d:=2) hZ hd hp hm⟩
end
end qEAwGBc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qfClb8d
noncomputable section
open qAzl5me (memberTest)
open qCj6p1d (Branch ChartRing qR yu sigma)
open qsnQ6jb (GraphLaws Iu)
open aR (af)
open dN (GeoJets oA AX bC)
open vS (g9)
open Dr (AN a9B aFq)
open B8 (Ro qK i9)
open private cXr bEj from ProximityPrize.SubmissionLower.A1
private theorem mem_lift_iff {g:af 4} (laws :GraphLaws g) {P:znc GeoJets}
    (hp:P.IsPrime) (hs :sigma g∉P) {E :g9}
    (hE :Associated (yu g E) (qR g (bC (memberTest g)))) :
    E∈Iu g P↔bC (memberTest g)∈P:= by
  let D:=bC (memberTest g)
  calc
    E∈Iu g P↔qK D∈Iu g P:= by
      change yu g E∈P.map (qR g)↔yu g (qK D)∈P.map (qR g)
      rw [show yu g (qK D)=qR g D from zLs laws.onOld D]
      exact ⟨(P.map (qR g)).mem_of_dvd hE.dvd,
        (P.map (qR g)).mem_of_dvd hE.dvd'⟩
    _↔D∈P:= by
      change D∈(Iu g P).comap qK↔D∈P
      rw [laws.comap P hp hs]
private theorem b85 {R G ell} (b:Branch R G ell) (laws :GraphLaws b.g) {E :g9}
    (hE :Associated (yu b.g E) (qR b.g (bC (memberTest b.g)))) :
    (i9 (Iu b.g b.aI) E).IsMinimalPrime (Iu b.g b.curve) := by
  have hSC:b.aI≤b.curve :=le_sup_left.trans b.member.minimal.le
  have hm:bC (memberTest b.g)∈b.curve :=
    b.member.minimal.le (zs0 (z5J _))
  refine ⟨⟨laws.prime b.curve b.member.minimal.isPrime b.regular,
    sup_le (zOS (zi2 hSC)) ((zvl _).mpr
      ((mem_lift_iff laws b.member.minimal.isPrime b.regular hE).mpr hm))⟩,?_⟩
  intro T hT hTC
  let P:=T.comap qK
  have hP:P.IsPrime := by
    let:=hT.1
    exact zG1 qK _
  have hPC:P≤b.curve := by
    have hle :=zOS (f :=qK) hTC
    rwa [laws.comap b.curve b.member.minimal.isPrime b.regular] at hle
  have hS:b.aI≤P :=
    Ideal.map_le_iff_le_comap.mp ((laws.cylinder_le _).trans (le_sup_left.trans hT.2))
  have hs :sigma b.g∉P:= fun h=>b.regular (hPC h)
  have hEq:T=Iu b.g P:=laws.eq_lift T hT.1 hs
    (hT.2 (Ideal.mem_sup_left (laws.contains _)))
  have hEmem:E∈T:=hT.2 (zs0 (z5J _))
  have hmP:=(mem_lift_iff laws hP hs hE).mp (hEq ▸ hEmem)
  have hCP:b.curve≤P :=
    b.member.minimal.2 ⟨hP,sup_le hS ((zvl _).mpr hmP)⟩ hPC
  rw [hEq]
  exact zOS (zi2 hCP)
private theorem eAj {R G ell} (b:Branch R G ell) (laws :GraphLaws b.g) {E :g9}
    (hE :Associated (yu b.g E) (qR b.g (bC (memberTest b.g)))) :
    oA (AX b.aI (memberTest b.g)) b.curve b.member.minimal.isPrime ≤
      Ro (i9 (Iu b.g b.aI) E) (Iu b.g b.curve)
        (b85 b laws hE).isPrime := by
  let C:=Iu b.g b.curve
  let:C.IsPrime :=(b85 b laws hE).isPrime
  let:b.curve.IsPrime :=b.member.minimal.isPrime
  let A:=Localization.AtPrime C
  let B:=Localization.AtPrime b.curve
  let M:=IsLocalRing.maximalIdeal B
  let I:=i9 (Iu b.g b.aI) E
  let J:=AX b.aI (memberTest b.g)
  let L:=J.map (algebraMap GeoJets B)
  have hσ:IsUnit (algebraMap GeoJets B (sigma b.g)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff B b.curve (sigma b.g)).mpr b.regular
  let φ:ChartRing b.g →+* B:=ztx (sigma b.g) hσ
  let θ:=φ.comp (yu b.g)
  have hφ:φ.comp (qR b.g)=algebraMap GeoJets B :=
    zOe (sigma b.g) hσ
  have hφM:M.comap φ=b.curve.map (qR b.g) := by
    have hco: (M.comap φ).comap (qR b.g)=b.curve := by
      rw [zg6,hφ]
      exact IsLocalization.AtPrime.under_maximalIdeal B b.curve
    calc
      M.comap φ=((M.comap φ).comap (qR b.g)).map (qR b.g) :=
        (zvH (zSL (sigma b.g)) (ChartRing b.g) (M.comap φ)).symm
      _ = _:=congrArg (Ideal.map (qR b.g)) hco
  have hθM:M.comap θ=C:= by
    change M.comap (φ.comp (yu b.g))=(b.curve.map (qR b.g)).comap (yu b.g)
    rw [← zg6,hφM]
  have hθold:θ.comp qK=algebraMap GeoJets B:= by
    change (φ.comp (yu b.g)).comp qK= _
    rw [RingHom.comp_assoc,laws.onOld,hφ]
  have hθunit (x :C.primeCompl) :IsUnit (θ x) := by
    have hn:θ x∉M:= by
      intro hm
      have hh: (x :g9)∈M.comap θ:=hm
      rw [hθM] at hh
      exact x.2 hh
    simpa only [M,IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,not_not] using hn
  let ψ:A →+* B:=IsLocalization.lift hθunit
  have hψ:ψ.comp (algebraMap g9 A)=θ:=IsLocalization.lift_comp hθunit
  have hsurj:Function.Surjective ψ:= by
    apply (IsLocalization.lift_surjective_iff hθunit).mpr
    intro v
    obtain ⟨⟨num,den⟩,hv⟩:=IsLocalization.surj b.curve.primeCompl v
    have hden:qK den∈C.primeCompl:= by
      change qK den∉C
      intro hd
      have hm: (den:GeoJets)∈(Iu b.g b.curve).comap qK:=hd
      rw [laws.comap b.curve b.member.minimal.isPrime b.regular] at hm
      exact den.2 hm
    refine ⟨⟨qK num,⟨qK den,hden⟩⟩,?_⟩
    change v*θ (qK den)=θ (qK num)
    have hold (x :GeoJets) :θ (qK x)=algebraMap GeoJets B x :=
      zLs hθold x
    simpa only [hold] using hv
  have hI:I≤L.comap θ:= by
    apply sup_le
    · change (b.aI.map (qR b.g)).comap (yu b.g)≤L.comap (φ.comp (yu b.g))
      rw [← zg6]
      apply zOS
      apply Ideal.map_le_iff_le_comap.mp
      rw [Ideal.map_map,hφ]
      exact zi2 le_sup_left
    · apply (zvl _).mpr
      change φ (yu b.g E)∈L
      have hm:bC (memberTest b.g)∈J :=
        zs0 (z5J _)
      refine L.mem_of_dvd (map_dvd φ hE.dvd') ?_
      rw [show φ (qR b.g (bC (memberTest b.g))) =
          algebraMap GeoJets B (bC (memberTest b.g)) from zLs hφ _]
      exact Ideal.mem_map_of_mem _ hm
  have hIL:I.map (algebraMap g9 A)≤L.comap ψ:= by
    rwa [zo0,zg6,hψ]
  exact cXr ψ hsurj hIL
private theorem demand_le {R G ell} (b:Branch R G ell) :
    (b.demandWeight:ℕ∞) ≤
      oA (AX b.aI (memberTest b.g)) b.curve b.member.minimal.isPrime := by
  classical
  let J:=AX b.aI (memberTest b.g)
  have hcast:=a9B b.member.minimal
  have hpos :0<AN J b.curve :=aFq b.member.minimal
  rw [← hcast]
  apply ENat.natCast_le_natCast.mpr
  change b.demandWeight≤AN J b.curve
  by_cases hs :b.Simple
  · simpa only [Branch.demandWeight,ite_eq_left hs] using Nat.succ_le_of_lt hpos
  · rw [Branch.demandWeight,ite_eq_right hs]
    have hne :AN J b.curve≠1 := by
      intro h
      apply hs
      exact hcast.symm.trans (congrArg (fun n:ℕ=>(n:ℕ∞)) h)
    omega
theorem proof :qsnQ6jb.c2 := by
  intro R G ell b E laws hprime hdim hE
  have hSC:b.aI≤b.curve :=le_sup_left.trans b.member.minimal.le
  have hproper :E∉Iu b.g b.aI :=
    mt (mem_lift_iff laws b.base.isPrime (fun h=>b.regular (hSC h)) hE).mp b.member.proper
  have hC:=b85 b laws hE
  exact ⟨hproper,⟨hC,(demand_le b).trans (eAj b laws hE)⟩,
    bEj hprime hdim hproper hC⟩
end
end qfClb8d
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qKVjhPa
noncomputable section
open Polynomial Finset
open P5 (K)
open qH0Nw9c (LineRow LineCaps)
open qaySLPd (ConstantFibre RS)
open cu (FX Jet kr rD)
open DP (Source U4 Fg)
open q89hPdc (linePoint regular_line)
open MvPolynomial (pderiv)
open private flat rawFlat center_flat flat_scalar lift_factor expand weight bounded_iff from ProximityPrize.SubmissionLower.Zl6SIrc
open private base restrict witness JX witness_eval restrict_caps restrict_eval restrict_derivative nonzero_projection curve from ProximityPrize.SubmissionLower.Z0SAUab
theorem lift_of_raw {h:ℕ} (hh:h≤2534) {raw:Source} (hraw:U4 raw≠0)
    (hc : ∀ j i a e,Fg raw j i a e≠0 →
      i+j≤115∧a+(i+j)*(131071+h)≤83*P6.dw-1+140*(2*h)+j)
    {f :Jet} (hf :Irreducible f) (hd:f∣U4 raw) :
    qCQTZAc.LiftAt qCQTZAc.degreeBound qCQTZAc.liftHeight f := by
  have hmap :=map_dvd (flat FX).toRingHom hd
  change flat FX f∣flat FX (U4 raw) at hmap
  rw [center_flat] at hmap
  have hr :rawFlat raw≠0:= by
    intro hz
    have he :=center_flat raw
    rw [hz,map_zero] at he
    exact hraw ((flat FX).toRingEquiv.map_eq_zero_iff.mp he)
  have hfi:Irreducible (flat FX f) :=(MulEquiv.irreducible_iff (flat FX).toRingEquiv).mpr hf
  obtain ⟨q,hq,u,hu,he⟩:=lift_factor hfi (rawFlat raw) hr hmap
  let A:=rawFlat.symm q
  have hA:rawFlat A=q:=rawFlat.apply_symm_apply q
  refine ⟨A,u,hu,(flat FX).injective ?_,?_⟩
  · rw [center_flat,hA,he,map_mul,flat_scalar]
  · have hbound: (expand (rawFlat raw)).weightedTotalDegree
        (weight qCQTZAc.degreeBound (qCQTZAc.degreeBound-1))≤qCQTZAc.liftHeight :=
      (bounded_iff _ _ _ _).mpr fun j i a e hce=> by
        obtain ⟨hb,hw⟩:=hc j i a e hce
        change _≤14925640+140*(2*h)+j at hw
        change a+133774*i+133773*j≤100000000
        omega
    apply (bounded_iff _ _ _ _).mp
    rw [hA]
    exact (MvPolynomial.weightedTotalDegree_le_of_dvd _ (map_dvd expand.toRingHom hq)
      ((map_ne_zero_iff _ expand.injective).mpr hr)).trans hbound
theorem line_of_scalars (z :K→K) (S:K→K[X]) (f :Jet) (T:Finset K)
    (hT : ∀ γ∈T,¬ rD f.derivative (z γ) (S γ)=0∧ConstantFibre f (z γ) (S γ)) :
    ∃ row:LineRow,LineCaps f row ∧ ∀ γ∈T,∃ a :cu.L,
      zY9 ![algebraMap cu.L FX a,kr (S γ),kr (S γ).derivative] row=0 ∧
      zY9 ![algebraMap cu.L FX a,kr (S γ),kr (S γ).derivative]
        (pderiv 2 row)≠0:= by
  classical
  choose q hq hqz hqd using fun i:T=>curve f (z i) (S i) (hT i i.property).2
  have hsep (i:T) :JX (witness (z i)) (RS f.derivative (S i))≠0:= by
    rw [witness_eval]
    exact (hT i i.property).1
  choose g hg hg' using fun i:T=>nonzero_projection _ _ (hsep i)
  obtain ⟨s,b,hline⟩:=regular_line q g (fun i:T=>witness (z i)) hq hqz hg
  refine ⟨restrict s b f,restrict_caps s b f,?_⟩
  intro γ hγ
  let i:T:=⟨γ,hγ⟩
  obtain ⟨a,ha,hb⟩:=hline i
  refine ⟨a,?_,?_⟩
  · change zY9 ![base a,kr (S i),kr (S i).derivative] (restrict s b f)=0
    rw [restrict_eval]
    have hd:=map_dvd (JX (linePoint s b a)) (hqd i)
    have hz :JX (linePoint s b a) (MvPolynomial.map base (q i))=0:= by
      rw [JX,← MvPolynomial.map_eval,ha,map_zero]
    rwa [hz,zero_dvd_iff] at hd
  · change zY9 ![base a,kr (S i),kr (S i).derivative]
      (pderiv 2 (restrict s b f))≠0
    rw [restrict_derivative,restrict_eval]
    exact hg' i _ hb
end
end qKVjhPa
end
