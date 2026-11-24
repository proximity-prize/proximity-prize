import ProximityPrize.SubmissionLower.Zpj8DDa
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.EssFiniteType → zl5, Algebra.IsAlgebraic → zjH, Algebra.IsSeparable → zw7, CommRing → za6, DirectSum.Decomposition.decompose'_eq → zRt, Field → zrb, Function.Surjective → zpX, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algebraMap_eq → zsL, Module.Finite → zAa, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.IsHomogeneous.map → zYM, MvPolynomial.X → z9v, MvPolynomial.coeff_C_mul → z06, MvPolynomial.coeff_map → zS3, MvPolynomial.map → zDK, MvPolynomial.ringHom_ext → zXT, Polynomial.X → z7y, Polynomial.monomial → zdM, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, RingHom.ker → zdq
section
namespace qBMP0Kd
noncomputable section
open Polynomial Algebra
open scoped WithZero
open P5 (K)
open cu (L)
open qb0hmCe (CurveModel)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb (seedRing)
open q9uVqha (Generic seedResidue seedResidue_apply zp)
private theorem primitive {E k σ:Type} [zrb E] [zrb k]
   (v :Valuation E ℤᵐ⁰) (r :v.valuationSubring →+* k)
   (g:z3y σ E) (hg:g≠0) :
   ∃ (a :E) (q:z3y σ v.valuationSubring),
     zDK v.valuationSubring.subtype q=znf a*g ∧
     zDK r q≠0:= by
 classical
 obtain ⟨m,hm,hmax⟩:=Finset.exists_max_image g.support (fun i=>v (g.coeff i))
   (MvPolynomial.support_nonempty.mpr hg)
 have hm0:=MvPolynomial.mem_support_iff.mp hm
 let a :=(g.coeff m)⁻¹
 let b:=znf a*g
 have hb:b∈Set.range (zDK v.valuationSubring.subtype) := by
   apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
   intro c hc
   obtain ⟨i,hi,rfl⟩:=MvPolynomial.mem_coeffs_iff.mp (Finset.mem_coe.mp hc)
   have hi' : i∈g.support := by
     apply MvPolynomial.mem_support_iff.mpr
     intro hz
     exact (MvPolynomial.mem_support_iff.mp hi) (by simp [b,z06,hz])
   refine ⟨⟨b.coeff i,?_⟩,rfl⟩
   change v (b.coeff i)≤1
   rw [show b.coeff i=g.coeff i/g.coeff m by
     change (znf a*g).coeff i= _
     rw [z06,div_eq_mul_inv,mul_comm],v.map_div]
   exact (div_le_one₀ (v.pos_iff.mpr hm0)).mpr (hmax i hi')
 obtain ⟨q,hq⟩:=hb
 have hqm:q.coeff m=1 := by
   apply Subtype.ext
   change v.valuationSubring.subtype (q.coeff m)=1
   rw [← zS3,hq]
   simp [b,a,z06,hm0]
 refine ⟨a,q,hq,fun h => ?_⟩
 have he :=congrArg (fun f :z3y σ k=>f.coeff m) h
 simp [zS3,hqm] at he
private theorem specialDim {E M k :Type} [zrb E] [zrb M] [zrb k] [zZE E M]
   (v :Valuation E ℤᵐ⁰) (r :v.valuationSubring →+* k) (hr :zpX r)
   (w:Fin 4→M) (hd:trdeg E M[X]≤2) :
   ringKrullDim (z3y (Fin 4) k ⧸ Ideal.map (zDK r)
     (zdq (zp ((algebraMap E M).comp v.valuationSubring.subtype) w)))≤2 := by
 classical
 let j:=zp ((algebraMap E M).comp v.valuationSubring.subtype) w
 let I:=Ideal.map (zDK r) (zdq j)
 change ringKrullDim (z3y (Fin 4) k ⧸ I)≤2
 by_cases hI:I = ⊤
 · have :Subsingleton (z3y (Fin 4) k ⧸ I) :=
     not_nontrivial_iff_subsingleton.mp (fun hn=>(Ideal.Quotient.nontrivial_iff.mp hn) hI)
   rw [ringKrullDim_eq_bot_of_subsingleton]
   exact bot_le
 obtain ⟨n,-,g,hg,hInt⟩:=exists_integral_inj_algHom_of_quotient I hI
 let π:=Ideal.Quotient.mk I
 have hs :zpX (π.comp (zDK r)) :=
   Ideal.Quotient.mk_surjective.comp (MvPolynomial.map_surjective r hr)
 choose t ht using fun i:Fin n=>hs (g (z9v i))
 let a :=MvPolynomial.eval₂Hom znf t
 let b:z3y (Fin n) E →ₐ[E] M[X] :=MvPolynomial.aeval (fun i=>j (t i))
 have hb:b.toRingHom.comp (zDK v.valuationSubring.subtype)=j.comp a := by
   apply zXT
   · intro c
     simp [a,b,j,zp]
   · intro i
     simp [a,b]
 have ha :g.toRingHom.comp (zDK r)=π.comp ((zDK r).comp a) := by
   apply zXT
   · intro c
     simp [a,π]
     rfl
   · intro i
     simpa [a] using (ht i).symm
 have hinj:Function.Injective b:= by
   apply (injective_iff_map_eq_zero b).mpr
   intro f hf
   by_contra hne
   obtain ⟨c,q,hq,hqne⟩:=primitive v r f hne
   have hv :j (a q)=0:= by
     have hh:=(zLs hb q).symm
     change j (a q)=b (zDK v.valuationSubring.subtype q) at hh
     rw [hh,hq,map_mul,hf,mul_zero]
   have hqz :π (zDK r (a q))=0 :=
     Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr hv))
   exact hqne ((injective_iff_map_eq_zero g).mp hg _ ((zLs ha q).trans hqz))
 have hn:n≤2 := by
   have hh:=(trdeg_le_of_injective b hinj).trans hd
   rw [MvPolynomial.trdeg_of_isDomain,Cardinal.lift_id,Cardinal.mk_fin] at hh
   exact_mod_cast hh
 let N :=z3y (Fin n) k
 let:zZE N (z3y (Fin 4) k ⧸ I) :=g.toRingHom.toAlgebra
 let:Algebra.IsIntegral N (z3y (Fin 4) k ⧸ I) :=
   algebraMap_isIntegral_iff.mp hInt
 have hd' : ringKrullDim N=n:= by simp [N,ringKrullDim_eq_zero_of_field]
 have hdN :ringKrullDim N≤2 := by rw [hd']; exact_mod_cast hn
 have hm:StrictMono (PrimeSpectrum.comap (algebraMap N (z3y (Fin 4) k ⧸ I))) := by
   intro x y hxy
   let:x.asIdeal.IsPrime :=x.2
   exact Ideal.IsIntegral.under_lt_under (R:=N) hxy
 exact (Order.krullDim_le_of_strictMono _ hm).trans hdN
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S}
private theorem residue_surjective (γ:K) (hγ:γ∈F.marks) :
  zpX (seedResidue F γ hγ) := by
 intro c
 let k :seedRing F γ:=⟨algebraMap L Cq.E c,by
  change (F.place γ).value (algebraMap L Cq.E c)≤1
  obtain rfl | hc:=eq_or_ne c 0
  · simp
  · exact le_of_eq ((F.place γ).on_constants c hc)⟩
 refine ⟨k,?_⟩
 rw [seedResidue_apply]
 change ((F.atPlace γ hγ) (algebraMap L Cq.E c)).coeff 0=c
 rw [AlgHom.commutes,LaurentSeries.algebraMap_apply]
 simp
private theorem generic_trdeg (G:Generic F) :trdeg Cq.E G.M[X]≤2 := by
 let B:=IntermediateField.adjoin Cq.E ({G.x} : Set G.M)
 let:zAa B G.M:=G.finite
 let:zjH B G.M:=Algebra.IsAlgebraic.of_finite B G.M
 let x :Unit→G.M:= fun _=>G.x
 have hx :AlgebraicIndependent Cq.E x :=
  (algebraicIndependent_singleton_iff ()).mpr G.independent
 have hr :Set.range x = {G.x} := by ext a; simp [x]
 have hb:IsTranscendenceBasis Cq.E x := by
  apply hx.isTranscendenceBasis_iff_isAlgebraic.mpr
  rw [hr,← IntermediateField.isAlgebraic_adjoin_iff_top]
  infer_instance
 have hm:trdeg Cq.E G.M=1 := by simpa using hb.cardinalMk_eq_trdeg.symm
 rw [← trdeg_add_eq Cq.E G.M (A:=G.M[X]),hm,Polynomial.trdeg_of_isDomain]
 norm_num
theorem proof :q9uVqha.c3:= by
 intro q Cq z S F G γ hγ
 exact specialDim (F.place γ).value (seedResidue F γ hγ)
  (residue_surjective γ hγ) G.point (generic_trdeg G)
end
end qBMP0Kd
end
section
namespace q2ANK6b
noncomputable section
open Polynomial IntermediateField
open qLXroAb (tu)

open XX (adp)
open aKx (bql bqn)
variable {k M:Type} [zrb k] [zrb M] [zZE k M]
private theorem derivation_eq_zero {V:Type} [AddCommGroup V]
    [Module M V] [Module k V] [zsf k M V] {x :M}
    (hs :zw7 (adjoin k {x}) M)
    (d:Derivation k M V) (hx :d x=0) :d=0:= by
  let T:=adjoin k ({x} : Set M)
  have hz (a :T) :d (a :M)=0:= by
    obtain ⟨a,ha⟩:=a
    refine adjoin_induction k (p:= fun v _=>d v=0) ?_ d.map_algebraMap ?_ ?_ ?_ ha
    · intro v hv
      obtain rfl :=Set.mem_singleton_iff.mp hv
      exact hx
    · intro a b _ _ ha hb
      rw [d.map_add,ha,hb,add_zero]
    · intro a _ ha
      rw [d.leibniz_inv,ha,smul_zero]
    · intro a b _ _ ha hb
      rw [d.leibniz,ha,hb,smul_zero,smul_zero,add_zero]
  let:Module T V:=Module.compHom V (algebraMap T M)
  have :zsf T M V:=IsScalarTower.of_compHom T M V
  let δ:Derivation T M V :=
    { toLinearMap :=
        { toFun:=d
          map_add' := d.map_add
          map_smul' := fun a b=> by
            change d ((a :M)*b)=(a :M)•d b
            rw [d.leibniz,hz,smul_zero,add_zero] }
      map_one_eq_zero' := d.map_one_eq_zero
      leibniz' := d.leibniz }
  apply Derivation.ext
  intro v
  have hv :aeval v (minpoly T v)=0:=minpoly.aeval T v
  have hd:=δ.map_aeval (minpoly T v) v
  rw [hv,δ.map_zero] at hd
  have :zw7 T M:=hs
  have hn:=(Algebra.IsSeparable.isSeparable T v).aeval_derivative_ne_zero hv
  exact (smul_eq_zero.mp hd.symm).resolve_left hn
private theorem separating_adjoin [zl5 k M] {x u:M}
   (hs :zw7 (adjoin k {x}) M) (hx :Transcendental k x)
   (D:Derivation k M M) (hDx :D x=1) (hDu:D u≠0) :
   Transcendental k u∧zAa (adjoin k {u}) M ∧
     zw7 (adjoin k {u}) M:= by
 let T:=adjoin k ({u} : Set M)
 let V:=KaehlerDifferential T M
 let d:=KaehlerDifferential.D T M
 let d₀:Derivation k M V:=d.restrictScalars k
 let b:=LinearMap.toSpanSingleton M V (d₀ x)
 have he :d₀ - b.compDer D =0:= by
   apply derivation_eq_zero hs
   change d₀ x - D x•d₀ x=0
   rw [hDx,one_smul,sub_self]
 have hdu:d₀ u=0:=d.map_algebraMap (⟨u,mem_adjoin_simple_self k u⟩:T)
 have hh:=Derivation.congr_fun he u
 change d₀ u - D u•d₀ x=0 at hh
 rw [hdu,zero_sub,neg_eq_zero] at hh
 have hdx :=(smul_eq_zero.mp hh).resolve_left hDu
 have hzero (v :M) :d v=0:= by
   have hv :=Derivation.congr_fun he v
   change d₀ v - D v•d₀ x=0 at hv
   change d₀ v=0
   simpa only [hdx,smul_zero,sub_zero] using hv
 have :zl5 T M:=Algebra.EssFiniteType.of_comp k T M
 have :Algebra.FormallyUnramified T M:=⟨(subsingleton_iff_forall_eq (0:V)).mpr (by
   intro v
   have hspan:Submodule.span M (Set.range d) = ⊥ :=
     Submodule.span_eq_bot.mpr (by rintro _ ⟨a,rfl⟩; exact hzero a)
   rw [KaehlerDifferential.span_range_derivation T M] at hspan
   exact hspan.le (show v∈(⊤ : Submodule M V) from trivial))⟩
 have hf :zAa T M:=Algebra.FormallyUnramified.finite_of_free T M
 have hsep:zw7 T M:=Algebra.FormallyUnramified.isSeparable T M
 refine ⟨?_,hf,hsep⟩
 intro hu
 have :zjH k T:=isAlgebraic_adjoin_simple hu.isIntegral
 have :zw7 T M:=hsep
 have :zjH k M:=Algebra.IsAlgebraic.trans k T M
 exact hx (Algebra.IsAlgebraic.isAlgebraic x)
theorem proof :q9uVqha.c5:= by
 intro q Cq z S F G u hu
 let k :=Cq.E
 let M:=G.M
 have :zl5 k M:=fg_top_iff.mp (G.generates ▸
   fg_adjoin_of_finite ((Set.finite_singleton G.y).insert G.x))
 obtain ⟨ht,hf,hs⟩:=separating_adjoin G.separable G.independent G.deriv G.deriv_x hu
 let T:=adjoin k ({u} : Set M)
 let:zZE k[X] M:=adp u
 let:zZE k[X] T:=bql u ht
 have :IsFractionRing k[X] T:=(bqn ht).1
 have :zsf k[X] T M:=(bqn ht).2
 let e :tu k ≃ₐ[k[X]] T:=FractionRing.algEquiv k[X] T
 let j:tu k →+* M:=T.val.toRingHom.comp e.toRingEquiv.toRingHom
 let:zZE (tu k) M:=j.toAlgebra
 have hj (a :k[X]) :j (algebraMap k[X] (tu k) a)=aeval u a := by
   change algebraMap T M (e (algebraMap k[X] (tu k) a))= _
   rw [e.commutes,← zG3 k[X] T M]
   rfl
 have :zsf k (tu k) M:=zsL fun a=> by
   change algebraMap k M a=j (algebraMap k (tu k) a)
   rw [zG3 k k[X] (tu k),hj]
   exact (aeval u).commutes a |>.symm
 have he : (algebraMap (tu k) M).comp e.symm.toRingEquiv.toRingHom =
     (RingEquiv.refl M).toRingHom.comp (algebraMap T M) := by
   apply RingHom.ext
   intro a
   change (e (e.symm a) :M)=(a :M)
   rw [e.apply_symm_apply]
 have :zAa T M:=hf
 have :zw7 T M:=hs
 exact ⟨{ base :=inferInstance
          tower :=inferInstance
          finite :=Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl M) he
          separable :=Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl M) he
          parameter :=(hj z7y).trans (aeval_X u) }⟩
end
end q2ANK6b
end
section
namespace qk9SLHb
noncomputable section
open Finset MvPolynomial
open Polynomial (eval₂RingHom evalRingHom)
open cu (L)
open qLXroAb (Pencil linear seedRing coords)
open q9uVqha
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
private abbrev P (R:Type) [za6 R] :=z3y (Fin 4) R
private def form {R:Type} [za6 R] (k :L →+* R) (a :Fin 4→L) :P R :=
 ∑ i,znf (k (a i))*z9v i
private theorem form_hom {R:Type} [za6 R] (k :L →+* R) (a :Fin 4→L) :
   (form k a).IsHomogeneous 1 :=
 (homogeneousSubmodule (Fin 4) R 1).sum_mem
   (fun i _=>(isHomogeneous_X R i).C_mul _)
private theorem map_form {R:Type} [za6 R] (k :L →+* R) (r :R →+* L)
  (h : ∀ c,r (k c)=c) (a :Fin 4→L) :
  zDK r (form k a)=P5 a := by
 simp only [form,P5,map_sum,map_mul,map_C,map_X,h]
private theorem ekw {R M:Type} [za6 R] [zrb M]
   (j:R →+* M) (v :Fin 4→M) (s :Fin 4 →₀ ℕ) (c:R) :
   zp j v (monomial s c) =
     zdM s.degree (j c*s.prod fun i n=>v i^n) := by
 change (monomial s c).eval₂ (Polynomial.C.comp j)
   (fun i=>Polynomial.C (v i)*z7y)= _
 rw [eval₂_monomial,zQb]
 simp only [Finsupp.prod,mul_pow,← Polynomial.C.map_pow]
 rw [Finset.prod_mul_distrib,← map_prod,Finset.prod_pow_eq_pow_sum,
   ← Finsupp.degree_apply,← mul_assoc,← map_mul,Polynomial.C_mul_X_pow_eq_monomial]
private theorem graph_component {R M:Type} [za6 R] [zrb M]
   (j:R →+* M) (v :Fin 4→M) (n:ℕ) (f :P R) :
   zp j v (homogeneousComponent n f) =
     zdM n ((zp j v f).coeff n) := by
 classical
 induction f using MvPolynomial.induction_on' with
 | monomial s c =>
   rw [homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
   by_cases h:n=s.degree
   · subst n
     simp [ekw]
   · simp [ekw,Polynomial.coeff_monomial,h,Ne.symm h]
 | add f g hf hg =>
   simp only [map_add,hf,hg,Polynomial.coeff_add]
private theorem graph_hom {R M:Type} [za6 R] [zrb M]
  (j:R →+* M) (v :Fin 4→M) :
  (zdq (zp j v)).IsHomogeneous (homogeneousSubmodule (Fin 4) R) := by
 intro n f hf
 rw [← zRt,MvPolynomial.decomposition.decompose'_apply]
 rw [RingHom.mem_ker,graph_component,RingHom.mem_ker.mp hf]
 simp
private theorem bIT {R:Type} [za6 R] (r :R →+* L) (n:ℕ) (f :P R) :
   zDK r (homogeneousComponent n f) =
     homogeneousComponent n (zDK r f) := by
 ext s
 simp only [coeff_map,coeff_homogeneousComponent]
 split_ifs <;> simp
private theorem b7G {R:Type} [za6 R] [IsLocalRing R]
   (r :R →+* L) (hr :zpX r) (J:Ideal (P R))
   (hJ:J.IsHomogeneous (homogeneousSubmodule (Fin 4) R)) (n:ℕ)
   (h : ∀ f :P L,f.IsHomogeneous n→f∈J.map (zDK r)) :
   homogeneousSubmodule (Fin 4) R n≤J.restrictScalars R:= by
 classical
 have hrad:zdq r≤Ideal.jacobson (⊥ : Ideal R) := by
   rw [IsLocalRing.ker_eq_maximalIdeal r hr,IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
 apply Submodule.le_of_le_smul_of_le_jacobson_bot (homogeneousSubmodule_fg _ _ n) hrad
 intro f hf
 obtain ⟨g,hg,he⟩ :=
   (Ideal.mem_map_iff_of_surjective _ (map_surjective r hr)).mp
     (h _ (zYM hf r))
 let gₙ:=homogeneousComponent n g
 have hgₙ:gₙ∈J:=homogeneousComponent_mem_of_mem hJ hg n
 let d:=f - gₙ
 have hd:d.IsHomogeneous n:=(mem_homogeneousSubmodule n f).mp hf |>.sub
   (homogeneousComponent_isHomogeneous n g)
 have hd0:zDK r d=0:= by
   simp only [d,gₙ,map_sub,bIT,he,homogeneousComponent_eq_self
     (zYM hf r),sub_self]
 have hmem:d∈zdq r•homogeneousSubmodule (Fin 4) R n:= by
   rw [as_sum d]
   refine Submodule.sum_mem _ fun s hs => ?_
   have hc:d.coeff s∈zdq r := by
     rw [RingHom.mem_ker,← coeff_map,hd0]
     simp
   have hm: (monomial s (1 :R)).IsHomogeneous n :=
     isHomogeneous_monomial _ (hd.degree_eq_sum_deg_support hs).symm
   simpa only [smul_monomial,smul_eq_mul,mul_one] using
     Submodule.smul_mem_smul hc (show monomial s (1 :R)∈homogeneousSubmodule _ _ n from hm)
 have hgd:gₙ+d=f := by simp [d]
 rw [← hgd]
 exact Submodule.add_mem_sup (S:=J.restrictScalars R) hgₙ hmem
private theorem cut_pieces {R M:Type} [za6 R] [IsLocalRing R] [zrb M]
   (j:R →+* M) (v :Fin 4→M) (k :L →+* R) (r :R →+* L)
   (hr : ∀ c,r (k c)=c) (a b:Fin 4→L)
   (h:GraphCut (TY j r v) a b) :
   ∃ N,∀ n≥N,∀ f :P R,f.IsHomogeneous n →
     f∈zdq (zp j v)+Ideal.span {form k a,form k b} := by
 let I:=zdq (zp j v)
 let J:=I+Ideal.span {form k a,form k b}
 have hJ:J.IsHomogeneous (homogeneousSubmodule (Fin 4) R) := by
   change (I ⊔ Ideal.span {form k a,form k b}).IsHomogeneous _
   apply (graph_hom j v).sup
   apply Ideal.homogeneous_span
   intro x hx
   rcases Set.mem_insert_iff.mp hx with he | he
   · exact ⟨1,he ▸ form_hom k a⟩
   · exact ⟨1,(Set.mem_singleton_iff.mp he) ▸ form_hom k b⟩
 have hmap :J.map (zDK r) =
     TY j r v+Ideal.span {P5 a,P5 b} := by
   simp only [J,I,TY,Ideal.add_eq_sup,Ideal.map_sup,Ideal.map_span,
     Set.image_insert_eq,Set.image_singleton,map_form k r hr]
 have hvars :idealOfVars (Fin 4) L≤(J.map (zDK r)).radical:= by
   rw [hmap,Ideal.span_le]
   rintro _ ⟨i,rfl⟩
   exact h i
 obtain ⟨N,hN⟩:=Ideal.exists_pow_le_of_le_radical_of_fg hvars (idealOfVars_fg _ _)
 refine ⟨N,fun n hn f hf => ?_⟩
 apply b7G r (fun c=>⟨k c,hr c⟩) J hJ n _ hf
 intro g hg
 apply hN (Ideal.pow_le_pow_right hn ?_)
 exact (mem_pow_idealOfVars_iff n g).mpr fun s hs=>(hg.degree_eq_sum_deg_support hs).le
private theorem Zy {R:Type} [za6 R] (n:ℕ)
    (f l:P R) (hl:l.IsHomogeneous 1) :
    homogeneousComponent (n+1) (f*l)=homogeneousComponent n f*l:= by
  simpa only [← zRt,
    MvPolynomial.decomposition.decompose'_apply,show n+1 - 1=n by omega] using
    (DirectSum.coe_decompose_mul_of_right_mem_of_le (homogeneousSubmodule (Fin 4) R)
      (a :=f) (n:=n+1) (show l∈homogeneousSubmodule _ _ 1 from hl) (by omega))
private theorem finite_chart {R T:Type} [za6 R] [za6 T]
    (j:R →+* T) (v :Fin 4→T) (u:T)
    (I:Ideal (P R)) (f₀ f₁:P R) (N :ℕ)
    (h₀:f₀.IsHomogeneous 1) (h₁:f₁.IsHomogeneous 1)
    (hp : ∀ n≥N,∀ f :P R,f.IsHomogeneous n→f∈I+Ideal.span {f₀,f₁})
    (hI:I.IsHomogeneous (homogeneousSubmodule (Fin 4) R))
    (hk :I≤zdq (eval₂Hom j v))
    (hu₀:eval₂Hom j v f₀=1)
    (hu₁:eval₂Hom j v f₁=u)
    (hs :zpX (eval₂Hom j v)) :
    letI:=(eval₂RingHom j u).toAlgebra
    zAa R[X] T:= by
  classical
  let:zZE R T:=j.toAlgebra
  let:zZE R[X] T:=(eval₂RingHom j u).toAlgebra
  let:zsf R R[X] T:=zsL fun c=> by
    change j c=eval₂RingHom j u (Polynomial.C c)
    simp
  let e :P R →ₐ[R] T:=aeval v
  let D (n:ℕ) :=Submodule.span R[X]
    ((homogeneousSubmodule (Fin 4) R n).map e.toLinearMap:Set T)
  let V:=(range (N+1)).sup D
  have hfg:V.FG:=Submodule.fg_finset_sup _ _ fun n _ =>
    ((homogeneousSubmodule_fg _ _ n).map e.toLinearMap).span
  have hsmall {n:ℕ} (hn:n<N+1) {f :P R} (hf :f.IsHomogeneous n) :e f∈V :=
    (Finset.le_sup (f :=D) (mem_range.mpr hn)) (Submodule.subset_span ⟨f,hf,rfl⟩)
  have hall (n:ℕ) (f :P R) (hf :f.IsHomogeneous n) :e f∈V:= by
    induction n generalizing f with
    | zero=>exact hsmall (Nat.zero_lt_succ _) hf
    | succ n ih =>
      by_cases hn:n+1<N+1
      · exact hsmall hn hf
      · obtain ⟨g,hg,w,hw,he⟩ :=
          Submodule.mem_sup.mp (hp (n+1) (by omega) f hf)
        obtain ⟨s,t,rfl⟩:=Ideal.mem_span_pair.mp hw
        have hg' : e (homogeneousComponent (n+1) g)=0 :=
          RingHom.mem_ker.mp (hk (homogeneousComponent_mem_of_mem hI hg _))
        have he' := congrArg (fun x=>e (homogeneousComponent (n+1) x)) he
        have h₀' : e f₀=1 :=hu₀
        have h₁' : e f₁=u:=hu₁
        simp only [map_add,Zy n _ _ h₀,Zy n _ _ h₁,
          map_mul,hg',h₀',h₁',mul_one,zero_add,homogeneousComponent_eq_self hf] at he'
        rw [← he',mul_comm _ u]
        apply V.add_mem (ih _ (homogeneousComponent_isHomogeneous _ _))
        have hsm: (z7y:R[X])•e (homogeneousComponent n t)∈V :=
          V.smul_mem _ (ih _ (homogeneousComponent_isHomogeneous _ _))
        simpa only [Algebra.smul_def,show algebraMap R[X] T z7y=u from
          Polynomial.eval₂_X j u] using hsm
  apply Module.Finite.of_fg_top
  suffices V = ⊤ by rwa [← this]
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨f,rfl⟩:=hs x
  change e f∈V
  rw [← sum_homogeneousComponent f,map_sum]
  exact V.sum_mem fun n _=>hall n _ (homogeneousComponent_isHomogeneous _ _)
theorem proof :q9uVqha.c6:= by
  intro q Cq z S F A γ hγ hcut u hu
  let R:=seedRing F γ
  let k :L →+* R:=(algebraMap L Cq.E).codRestrict _ fun c=> by
    obtain rfl | hc:=eq_or_ne c 0
    · simp
    · exact le_of_eq ((F.place γ).on_constants c hc)
  have hr (c:L) :seedResidue F γ hγ (k c)=c:= by
    rw [seedResidue_apply]
    change ((F.atPlace γ hγ) (algebraMap L Cq.E c)).coeff 0=c
    rw [AlgHom.commutes,LaurentSeries.algebraMap_apply]
    simp
  let j:=A.pO γ
  let v :=coords F.f A.x A.y
  let I:=zdq (zp j v)
  let e :=eval₂Hom (A.inChart γ) (A.chartRatio γ)
  let g:=linear ((algebraMap Cq.E A.M).comp (algebraMap L Cq.E)) A.a v
  have hg:g≠0:=A.gauge_ne
  have hseed (c:R) : (A.bY γ).subtype (A.inChart γ c)=j c:=rfl
  have hratio (i:Fin 4) : (A.bY γ).subtype (A.chartRatio γ i)=v i*g⁻¹:= by
    change A.ratio i= _
    rw [Pencil.ratio,div_eq_mul_inv]
  obtain ⟨N,hN⟩:=cut_pieces j v k (seedResidue F γ hγ) hr A.a A.b hcut
  have hcomp: (A.bY γ).subtype.comp e =
      (evalRingHom g⁻¹).comp (zp j v) := by
    apply ringHom_ext
    · intro c
      simp [e,zp]
      rfl
    · intro i
      simp only [e,zQb,eval₂Hom_X',graphMap_X,map_mul,
        Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.eval_X,hratio]
  have he (c:Fin 4→L) : (e (form k c) :A.M) =
      linear ((algebraMap Cq.E A.M).comp (algebraMap L Cq.E)) c v/g:= by
    change ((A.bY γ).subtype.comp e) (form k c)= _
    simp only [zQb,e,form,map_sum,map_mul,eval₂Hom_C,
      eval₂Hom_X',hseed,hratio,div_eq_mul_inv,linear,Finset.sum_mul,mul_assoc]
    rfl
  refine finite_chart (A.inChart γ) (A.chartRatio γ) u I (form k A.a) (form k A.b)
    N (form_hom k A.a) (form_hom k A.b) hN (graph_hom j v) ?_ ?_ ?_ ?_
  · intro f hf
    apply RingHom.mem_ker.mpr
    apply Subtype.val_injective
    change ((A.bY γ).subtype.comp e) f=0
    rw [hcomp,zQb,RingHom.mem_ker.mp hf,map_zero]
  · apply Subtype.val_injective
    change (e (form k A.a) :A.M)=1
    rw [he,div_self hg]
  · apply Subtype.val_injective
    change (e (form k A.b) :A.M)=(u:A.M)
    rw [he,hu,div_eq_iff hg]
    exact A.value
  · intro x
    have hle :A.bY γ≤((A.bY γ).subtype.comp e).range := by
      apply Subring.closure_le.mpr
      rintro _ (⟨c,rfl⟩ | ⟨i,rfl⟩)
      · exact ⟨znf c,by simp [e]; rfl⟩
      · exact ⟨z9v i,by simp [e,Pencil.chartRatio]⟩
    obtain ⟨f,hf⟩:=hle x.property
    exact ⟨f,Subtype.val_injective hf⟩
end
end qk9SLHb
end
