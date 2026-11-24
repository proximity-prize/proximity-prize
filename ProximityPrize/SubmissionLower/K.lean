import ProximityPrize.SubmissionLower.AG
import ProximityPrize.SubmissionLower.G
import ProximityPrize.SubmissionLower.H
set_option Elab.async false
open _root_ renaming AddCommGroup→Nr,AddCommGrpCat.subsingleton_of_isZero→zap,AlgHom.toLinearMap_apply→PD,Algebra→t7,Algebra.algebraMap→c9,CategoryTheory.ShortComplex.Exact.isZero_of_both_zeros→zfe,CommRing→lV,DFunLike.congr_fun→zmU,EquivLike.apply_eq_iff_eq→Zh,Field→lz,Filter.Tendsto→t4,Filter.atTop→qx,Filter.eventually_ge_atTop→G0,Fin.last→EP,Fin.lastCases→UY,Fin.range_succAbove→zQu,Finset→vh,Finset.add_sum_erase→zT2,Finset.induction_on→zcw,Finset.le_sup→Ee,Finset.mem_univ→wB,Finset.sum_add_distrib→SU,Finset.sum_apply→TI,Finset.sum_congr→vw,Finset.sum_eq_single→LO,Finset.sum_insert→NY,Finset.sum_le_sum→zQk,Finset.sum_le_sum_of_subset_of_nonneg→zlp,Finsupp.add_apply→J4,Finsupp.induction_linear→WY,Finsupp.single→S1,Finsupp.weight→uJ,Finsupp.weight_single→Kh,Fintype→yU,Fintype.card→KI,FractionRing→Df,Function.Injective→sI,Function.LeftInverse→X8,Function.Surjective→vZ,Function.comp_apply→G7,Function.comp_def→ZK,Function.iterate_one→zS5,Function.iterate_succ_apply'→Zf,Function.update→vG,Function.update_of_ne→XB,Ideal→cy,Ideal.IsMaximal→RP,Ideal.IsMaximal.of_liesOver_isMaximal→zvA
open _root_ renaming Ideal.Quotient.lift→Zi,Ideal.Quotient.mk→ oy,Ideal.Quotient.mk_eq_mk_iff_sub_mem→zdf,Ideal.Quotient.mk_surjective→zf,Ideal.Quotient.mkₐ→zh,Ideal.annihilator_quotient→Ml,Ideal.comap_isMaximal_of_surjective→Xg,Ideal.comap_map_of_surjective→ Iw,Ideal.comap_mono→Qw,Ideal.exists_le_maximal→zsl,Ideal.exists_minimalPrimes_le→zXL,Ideal.isPrime_bot→Ob,Ideal.map_le_iff_le_comap→Ts,Ideal.map_map→Nq,Ideal.map_mono→S2,Ideal.map_span→qy,Ideal.mem_bot→TH,Ideal.mem_map_of_mem→xW,Ideal.mem_span_singleton_self→WD,Ideal.mem_sup_right→UP,Ideal.mk_ker→Eg,Ideal.mul_top→FU,Ideal.ofList→sS,Ideal.ofList_cons→G6,Ideal.primesOver→Gj,Ideal.quotientKerAlgEquivOfSurjective→X4,Ideal.quotientMap→Wm,Ideal.quotientMap_mk→FK,Ideal.radical_mono→zks,Ideal.smul_eq_mul→FV,Ideal.smul_top_eq_map→zde,Ideal.span→lI,Ideal.span_mono→N0,Ideal.span_singleton_le_iff_mem→yJ,Ideal.subset_span→qJ,Infinite→Fz,Int.toNat_natCast→zQg,IntermediateField.adjoin→EK,IntermediateField.mem_adjoin_simple_self→zl2,IntervalIntegrable→zve,Irreducible→zm,IsAssociatedPrime→P7,IsClosed→yQ,IsClosed.inter→Pj,IsDedekindDomain→PA,IsFractionRing.injective→zi,IsIntegral→Mz,IsLeftRegular→SC
open _root_ renaming IsLocalRing→Au,IsLocalRing.ResidueField→Lf,IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal→Mj,IsLocalRing.maximalIdeal→pL,IsLocalRing.maximalIdeal.isMaximal→Pv,IsLocalRing.residue→SL,IsLocalization→C9,IsLocalization.Away.lift→MO,IsLocalization.algebraMap_mem_map_algebraMap_iff→Ar,IsLocalization.lift→zvq,IsLocalization.lift_eq→zX4,IsLocalization.map_under→Vl,IsLocalization.map_units→C4,IsLocalization.ringHom_ext→UZ,IsLocalization.surj→zg4,IsNoetherianRing→zS,IsSMulRegular→qU,IsScalarTower.algebraMap_apply→Pr,IsScalarTower.toAlgHom→XJ,IsUnit→Dz,LinearMap.finrank_range_of_inj→VO,List.map_ofFn→VC,List.mem_cons_of_mem→Mk,List.mem_cons_self→zYY,List.mem_ofFn'→RJ,List.ofFn→zc,List.perm_append_comm→ztu,List.perm_append_singleton→zfI,Localization.AtPrime→qM,Localization.Away→zUF,MM.poleOrder→Av,Matrix.cons_val_zero→zbs,MeasurableEquiv.piFinSuccAbove→Wl,MeasurableEquiv.prodComm→Y4,MeasurableEquiv.refl→zjQ,MeasureTheory.MeasureSpace.volume→ oZ,MeasureTheory.volume_preserving_piFinSuccAbove→zYs,Module.Finite→ ov,Module.Finite.of_surjective→Yo,Module.Flat→LQ,Module.IsTorsionFree→zYo,Module.annihilator→p7,Module.finrank→ oz,Module.support_eq_zeroLocus→zpq,ModuleCat→FR,ModuleCat.homAddEquiv→Xp,ModuleCat.of→yl,ModuleCat.subsingleton_ext_of_exists_isRegular→zw0
open _root_ renaming MvPolynomial→lJ,MvPolynomial.C→qz,MvPolynomial.X→mD,MvPolynomial.X_pow_eq_monomial→zp9,MvPolynomial.aeval→vk,MvPolynomial.aeval_X→Dw,MvPolynomial.affineDegree→Gi,MvPolynomial.affineHilbertFunction→G2,MvPolynomial.affineHilbertPolynomial→u9,MvPolynomial.algHom_ext→zpJ,MvPolynomial.algebraMvPolynomial→WW,MvPolynomial.basisMonomials→ IT,MvPolynomial.coeff_mul_X'→VS,MvPolynomial.eval→Gn,MvPolynomial.eval₂Hom→pC,MvPolynomial.eval₂Hom_C→Dv,MvPolynomial.eval₂Hom_X'→yo,MvPolynomial.exists_eval_affineHilbertPolynomial→Z0,MvPolynomial.homogeneousComponent→G4,MvPolynomial.induction_on'→Zg,MvPolynomial.isLocalization→Pc,MvPolynomial.isWeightedHomogeneous_monomial→LP,MvPolynomial.ker_map→RC,MvPolynomial.map→ oY,MvPolynomial.map_C→TZ,MvPolynomial.map_surjective→G9,MvPolynomial.monomial→ oK,MvPolynomial.monomial_mul_monomial→Ok,MvPolynomial.natDegree_affineHilbertPolynomial_bot→Vs,MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le→zy5,MvPolynomial.pderiv→Kl,MvPolynomial.renameEquiv_apply→Vz,MvPolynomial.ringHom_ext→th,MvPolynomial.weightedHomogeneousComponent→wR,MvPolynomial.weightedHomogeneousComponent_eq_self→zfp,MvPolynomial.weightedHomogeneousComponent_mem→zbF,MvPolynomial.weightedHomogeneousComponent_of_mem→Hw,MvPolynomial.zeroLocus→Gk,Nat.card_coe_set_eq→Zt,Nat.cast_add→NZ,Nat.cast_mul→NI,Nat.cast_ofNat→Sv,Nat.cast_one→G8,Nat.le_mul_of_pos_right→ziA,Nat.le_succ→Un,Nat.mul_le_mul_left→HZ,Nat.sub_add_cancel→Vq,Nat.zero_le→ In
open _root_ renaming Pi.add_apply→Qy,Pi.single→sH,Pi.single_apply→Qx,Pi.single_eq_of_ne→SW,Pi.smul_apply→FQ,Polynomial→ ox,Polynomial.C→ oj,Polynomial.C_mul_X_pow_eq_monomial→zoT,Polynomial.X→p9,Polynomial.derivative→pQ,Polynomial.evalRingHom→zd,Polynomial.eval_C→ II,Polynomial.eval₂RingHom→Bf,Polynomial.eval₂_C_X→Xu,Polynomial.eval₂_map→KA,Polynomial.hasseDeriv→t3,Polynomial.hom_eval₂→Et,Polynomial.ker_mapRingHom→SM,Polynomial.mapRingHom→pU,Polynomial.map_id→zeh,Polynomial.map_injective→zTo,Polynomial.monomial→SD,Polynomial.ringHom_ext→v8,Polynomial.ringHom_ext'→Ww,PrimeSpectrum.zeroLocus→Xo,Prod.mk→Ef,QuotSMulTop→Du,RingHom.comap_ker→zR,RingHom.comp_apply→x7,RingHom.congr_fun→qm,RingHom.ext→yL,RingHom.id→zk,RingHom.ker→nX,RingHom.ker_eq_comap_bot→JM,RingHom.ker_isPrime→zgL,RingHom.mem_ker→Cy,RingTheory.Sequence.IsWeaklyRegular→pG,RingTheory.Sequence.IsWeaklyRegular.cons→Pk,RingTheory.Sequence.isWeaklyRegular_append_iff→Aa,RingTheory.Sequence.isWeaklyRegular_singleton_iff→xL,Set.Subset.antisymm→zkG,Set.add_subset_add→KH,Set.image_congr→F9,Set.image_image→z8,Set.image_singleton→G5,Set.inter_subset_inter_left→zSk,Set.mem_iUnion₂_of_mem→WX,Set.mem_insert_iff→QL
open _root_ renaming Set.mem_ofPred_eq→Mw,Set.mem_singleton_iff→LR,Set.ncard_le_ncard→XG,Set.range→uW,Set.range_comp→NX,Set.range_comp'→Nj,Submodule→vH,Submodule.Quotient.mk→ IU,Submodule.Quotient.mk_eq_zero→ziM,Submodule.annihilator_top→Ze,Submodule.ideal_span_singleton_smul→Rm,Submodule.map_mono→VH,Submodule.mem_sup_left→Ye,Submodule.mem_sup_right→Yc,Submodule.mem_top→Xx,Submodule.mkQ_surjective→zUn,Submodule.quotEquivOfEq→RD,Submodule.span→PM,Submodule.sum_mem→zo3,Submonoid.powers→JW,Subsingleton→wA,Subtype.ext→u8,Subtype.val→Np,Transcendental→wY,UH.Exponent→zE,UH.lattice→ oD,WithZero.exp→MS,aR.Shape→aU,aR.Shape.plus→vi,aR.Shape.scale→t6,abG.Total→pz,abG.reduce→n5,add_right_cancel_iff→ZJ,add_sub_cancel_left→zYK,add_sub_cancel_right→Kv,add_zero→Fa,akO.Degree→u5,akO.shift→uh,associatedPrimes→vl,associatedPrimes.finite→Up,biUnion_associatedPrimes_eq_compl_regular→ Il,congrArg→ oq,continuous_const→Kp,dN.GeoField→qG,dN.GeoJets→nq,div_le_div_of_nonneg_right→zrZ,finSuccEquiv→G3,gT.Ambient→p6
open _root_ renaming ge_of_tendsto'→Sd,inferInstance→Ea,intervalIntegral.integral_const_mul→zsY,intervalIntegral.integral_of_le→zxr,inv_mul_cancel₀→Re,isClosed_le→z9,isSMulRegular_quotient_iff_mem_of_smul_mem→Yi,lB.TaylorChart→GR,le_antisymm→vj,le_max_left→Oc,le_rfl→xu,le_sup_left→z7,le_sup_right→MK,le_total→GF,map_add→uz,map_mul→nI,map_pow→t8,map_prod→JQ,map_sub→xm,map_sum→t5,map_zero→p5,min_eq_left→GB,min_eq_right→GY,min_le_left→Kz,min_le_right→JK,mul_assoc→xI,mul_comm→v9,mul_div_cancel_right₀→WK,mul_le_mul_of_nonneg_left→y5,mul_left_comm→Gr,mul_nonneg→NW,mul_one→zg,nsmul_eq_mul→R9,oR.separant→yB,one_mul→ze,one_smul→OJ,pow_ne_zero→Te,smul_eq_mul→G1,sub_eq_zero→Pf,sub_zero→Kc,succ_nsmul→C5,sup_le→t9,tendsto_nhds_unique→zt0
set_option autoImplicit true
section
namespace UH
open aR lB YV ap7
open MvPolynomial MeasureTheory Filter
open scoped Pointwise Topology
def c1 :Prop :=
  ∀ (k :Type) [lz k] (f :Fin 4→ gQ k),
    ov k (Rh f) →
    ov k (Rh (fun i=>f i^2)) ∧
      oz k (Rh (fun i=>f i^2)) =
        16*oz k (Rh f)
def c2 :Prop :=
  ∀ (k :Type) [lz k] (P:Fin 4→aU) (f :Fin 4→ gQ k),
    (∀ i,(↑(f i).support :Set zE)⊆oD (P i)) →
    ov k (Rh f) →
    ov (fZ k P) (ap1 k P) →
    oz k (Rh f) ≤
      oz (fZ k P) (ap1 k P)
def c3:Prop :=
  ∀ (k :Type) [lz k] (P:Fin 4→aU),
    (∀ i,bF (P i)∧Even (P i).j∧Even (P i).t) →
    ov (fZ k P) (ap1 k P) ∧
      ∃ R:aU,bF R ∧ ∀ n:ℕ,
        (oz (fZ k P) (ap1 k P) :ℝ)*(n:ℝ)^4 =
          cSW (fun x=>((oD x).ncard:ℝ)) (fun i=>(P i).scale n) R
private theorem bNh (p q:aU) (n:ℕ) :
  (p.plus q).scale n=(p.scale n).plus (q.scale n) := by
 cases p
 cases q
 simp [vi ,t6,Nat.mul_add]
private theorem bEg {R p:aU} {F:ℕ→aU→ℝ} {G:Set M5→ℝ}
    (h : ∀ x :aU,bF x →
      t4 (fun n:ℕ=>F n (R.plus (x.scale n))/(n:ℝ)^4)
        qx (𝓝 (G (cap x)))) (hp:bF p)
    (x :aU) (hx :bF x) :
    t4 (fun n:ℕ=>aAk (F n) (p.scale n) (R.plus (x.scale n))/(n:ℝ)^4)
      qx (𝓝 (ahk G (cap p) (cap x))) := by
  rw [ahk,← anN hx hp]
  apply ((h _ (Nc hx hp)).sub (h x hx)).congr
  intro n
  have he :R.plus ((x.plus p).scale n)=(R.plus (x.scale n)).plus (p.scale n) := by
    rw [bNh]
    cases R
    cases x
    cases p
    simp [vi ,Nat.add_assoc]
  rw [aAk,sub_div,he]
private theorem efT (h3:c3) (k :Type) [lz k] (P:Fin 4→aU)
    (hP : ∀ i,bF (P i)∧Even (P i).j∧Even (P i).t) :
    ov (fZ k P) (ap1 k P) ∧
      (oz (fZ k P) (ap1 k P) :ℝ) =
        avz (cap (P 0)) (cap (P 1)) (cap (P 2)) (cap (P 3)) := by
  obtain ⟨hfin,R,hR,hRdef⟩:=h3 k P hP
  refine ⟨hfin,?_⟩
  let F₀ (_:ℕ) (x :aU) :=((oD x).ncard:ℝ)
  let F₁ (n:ℕ) :=aAk (F₀ n) ((P 0).scale n)
  let F₂ (n:ℕ) :=aAk (F₁ n) ((P 1).scale n)
  let F₃ (n:ℕ) :=aAk (F₂ n) ((P 2).scale n)
  let G₀ (B:Set M5) :=(oZ B).toReal
  let G₁:=ahk G₀ (cap (P 0))
  let G₂:=ahk G₁ (cap (P 1))
  let G₃:=ahk G₂ (cap (P 2))
  have h₀ (x :aU) (hx :bF x) :=euN R x hR hx
  have h₁:=bEg (R:=R) (F:=F₀) (G:=G₀) h₀ (hP 0).1
  have h₂:=bEg (R:=R) (F:=F₁) (G:=G₁) h₁ (hP 1).1
  have h₃:=bEg (R:=R) (F:=F₂) (G:=G₂) h₂ (hP 2).1
  have hlim:=bEg (R:=R) (F:=F₃) (G:=G₃) h₃ (hP 3).1
    ⟨0,0,0⟩ (⟨by decide,by decide⟩)
  rw [auw] at hlim
  have hz (n:ℕ) :R.plus ((⟨0,0,0⟩:aU).scale n)=R:= by
    cases R
    simp [vi ,t6]
  simp only [hz] at hlim
  change t4 (fun n:ℕ =>
    cSW (fun x=>((oD x).ncard:ℝ)) (fun i=>(P i).scale n) R/(n:ℝ)^4)
      qx (𝓝 (avz (cap (P 0)) (cap (P 1)) (cap (P 2)) (cap (P 3)))) at hlim
  refine zt0 (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [G0 (1 :ℕ)] with n hn
  have hn0: (n:ℝ)^4≠0:=Te _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
  rw [← hRdef n,WK _ hn0]
private theorem ase {F:Set M5→ℝ} {G:aU→ℤ}
  (heq : ∀ x :aU,bF x→32*F (cap x)=(G x :ℝ))
  {a :aU} (ha :bF a) (x :aU) (hx :bF x) :
  32*ahk F (cap a) (cap x)=(gI G a x :ℝ) := by
 rw [ahk,gI,Int.cast_sub,mul_sub,← anN hx ha,
  heq _ (Nc hx ha),heq _ hx]
private def Q9 (p q a h:aU) :ℤ :=
 gI (gI (gI (gI Dn p) q) a) h ⟨0,0,0⟩
private theorem aVX (p q a h:aU)
  (hp:bF p) (hq:bF q) (ha :bF a) (hh:bF h) :
  32*avz (cap p) (cap q) (cap a) (cap h)=(Q9 p q a h:ℝ) := by
 have hv :=ase
  (F:= fun P=>(oZ P).toReal) (G:=Dn) bWq hp
 have hm:=ase (ase (ase hv hq) ha) hh
  ⟨0,0,0⟩ (⟨by decide,by decide⟩)
 rw [auw] at hm
 exact hm
private theorem eAZ (p q a h:aU)
   (hp:bF p) (hq:bF q) (ha :bF a) (hh:bF h) :
   avz (cap (p.scale 2)) (cap (q.scale 2)) (cap (a.scale 2)) (cap (h.scale 2)) =
     16*avz (cap p) (cap q) (cap a) (cap h) := by
 have hs :Q9 (p.scale 2) (q.scale 2) (a.scale 2) (h.scale 2) =
     16*Q9 p q a h:= by
   simp only [Q9,gI,Dn,vi ,t6,
     NZ,NI,Sv,Nat.cast_zero]
   ring
 have hb:=aVX _ _ _ _ (BP hp 2) (BP hq 2)
   (BP ha 2) (BP hh 2)
 rw [hs,Int.cast_mul,Int.cast_ofNat] at hb
 linarith only [hb,aVX p q a h hp hq ha hh]
private theorem gus {k :Type} [lz k] {f :gQ k} {p:aU}
  (hp:bF p) (hf :aJ9 f p) :aJ9 (f^2) (p.scale 2) := by
 intro e he
 rw [pow_two] at he
 obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_add.mp (support_mul f f he)
 have hshape :p.scale 2=p.plus p:= by
  cases p
  simp [t6,vi ,two_mul]
 rw [hshape,anN hp hp]
 exact Set.mem_add.mpr ⟨_,hf u hu,_,hf v hv,by ext i; simp [J4]⟩
private theorem gEF {k :Type} [lz k] (F G U V:gQ k) :
   Su ![F,G,U,V]=lI {F,G,U,V} := by
 apply oq lI
 ext e
 constructor
 · rintro ⟨i,rfl⟩
   fin_cases i <;> simp
 · intro he
   simp only [QL,LR] at he
   rcases he with rfl | rfl | rfl | rfl
   · exact ⟨0,rfl⟩
   · exact ⟨1,rfl⟩
   · exact ⟨2,rfl⟩
   · exact ⟨3,rfl⟩
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :ap7.c3:= by
 intro p q a h hp hq ha hh F G U V hF hG hU hV hfin
 let k :=GJ.VM a h
 let P:Fin 4→Shape := ![p,q,a,h]
 let f :Fin 4→ gQ k := ![F,G,U,V]
 have hP (i:Fin 4) :bF (P i) := by
   fin_cases i <;> assumption
 have hf (i:Fin 4) :aJ9 (f i) (P i) := by
   fin_cases i <;> assumption
 have hJ:Su f=lI {F,G,U,V} := gEF F G U V
 have hfinit :ov k (Rh f) := by
   change ov k (gQ k ⧸ Su f)
   rw [hJ]
   exact hfin
 obtain ⟨hsq,hlen⟩:=h1 k f hfinit
 let Q:= fun i=>(P i).scale 2
 have heven (i:Fin 4) :bF (Q i)∧Even (Q i).j∧Even (Q i).t:= by
   refine ⟨BP (hP i) 2,⟨(P i).j,?_⟩,⟨(P i).t,?_⟩⟩ <;>
     simp [Q,t6,two_mul]
 obtain ⟨hgfin,hglen⟩:=efT h3 k Q heven
 have hsupp (i:Fin 4) : (↑(f i^2).support :Set zE)⊆oD (Q i) := by
   intro e he
   exact aON.mpr (gus (hP i) (hf i) e he)
 have hcompare :=h2 k Q (fun i=>f i^2) hsupp hsq hgfin
 have hcomp: (16:ℝ)*(oz k (Rh f) :ℝ) ≤
     (oz (fZ k Q) (ap1 k Q) :ℝ) := by
   rw [hlen] at hcompare
   exact_mod_cast hcompare
 have hm:avz (cap (Q 0)) (cap (Q 1)) (cap (Q 2)) (cap (Q 3)) =
     16*avz (cap p) (cap q) (cap a) (cap h) :=eAZ p q a h hp hq ha hh
 rw [hglen,hm] at hcomp
 have hbound:=le_of_mul_le_mul_left hcomp (by norm_num : (0:ℝ)<16)
 change (oz k (gQ k ⧸ Su f) :ℝ)≤_ at hbound
 rw [hJ] at hbound
 exact hbound
end UH
end
section
namespace akO
noncomputable section
open aR lB UH MvPolynomial
def c1 :Prop :=
  ∀ (k :Type) [lz k] (P:Fin 4→aU) (i:Fin 4) (p:Qm k P),
    ve k P i*p∈mo k P i.val→p∈mo k P i.val
def c2 :Prop :=
  ∀ (k :Type) [lz k] (P:Fin 4→aU),
    (∀ i,bF (P i)∧Even (P i).j∧Even (P i).t) →
    ∃ q:ℕ,∀ (b:ℕ) (d:u5) (i:Fin 4),q≤b→(∀ j,q≤d j) →
      ∀ p∈dO k P b (uh d i 1),p∈mo k P (i.val+1) →
        ∃ r∈dO k P b d,p - ve k P i*r∈mo k P i.val
variable {k :Type} [lz k] {P:Fin 4→aU}
private def Jw (r :ℕ) :Qm k P →ₐ[fZ k P]
  Qm k P ⧸ mo k P r :=
 zh (fZ k P) (mo k P r)
private def ZY (r b:ℕ) (d:u5) :
   vH (fZ k P) (Qm k P ⧸ mo k P r) :=
 (dO k P b d).map (Jw r).toLinearMap
private instance (r b:ℕ) (d:u5) :ov (fZ k P)
  (ZY (k :=k) (P:=P) r b d) := by
 unfold ZY
 infer_instance
private def lO (r b:ℕ) (d:u5) :ℕ :=
 oz (fZ k P) (ZY (k :=k) (P:=P) r b d)
private theorem aCc (r :ℕ) (p:Qm k P) :
 Jw r p=0↔p∈mo k P r :=Ideal.Quotient.eq_zero_iff_mem
private theorem bll (r :ℕ) (p s :Qm k P) :
  Jw r p=Jw r s↔p - s∈mo k P r := by
 rw [← aCc,xm,Pf]
private theorem a6N {r s :ℕ} (h:r≤ s) :
  mo k P r≤ mo k P s :=
 N0 (Set.image_mono fun _ hi=>lt_of_lt_of_le hi h)
private theorem b1K (i:Fin 4) :
  ve k P i∈mo k P (i.val+1) :=
 qJ ⟨i,Nat.lt_succ_self _,rfl⟩
private theorem b50 (b:ℕ) (d:u5) :
  lO (k :=k) (P:=P) 0 b d=(oD (eG P b d)).ncard:= by
 have hbot:mo k P 0 = ⊥ := by simp [mo]
 let f :=(Jw 0).toLinearMap.comp (dO k P b d).subtype
 have hrange :LinearMap.range f=ZY (k :=k) (P:=P) 0 b d:= by
  simp [f,ZY,LinearMap.range_comp]
 have hinj:sI f := by
  intro p s he
  apply u8
  change Jw 0 (p:Qm k P)=Jw 0 (s :Qm k P) at he
  have hm:=(bll 0 _ _).mp he
  rw [hbot,TH] at hm
  exact sub_eq_zero.mp hm
 unfold lO
 rw [← hrange,VO hinj,b3c]
private theorem bt1 :mo k P 4=Su (ve k P) := by
 have h : {i:Fin 4 | (i:ℕ)<4} = Set.univ :=Set.eq_univ_of_forall fun i=>i.isLt
 rw [mo,h,Set.image_univ]
private theorem b5Y (hfinite :ov (fZ k P) (ap1 k P)) :
    ∃ q:ℕ,∀ b (d:u5),q≤b →
      lO (k :=k) (P:=P) 4 b d =
        oz (fZ k P) (ap1 k P) := by
  let hfin:ov (fZ k P) (Qm k P ⧸ mo k P 4) := by
    rw [bt1]; exact hfinite
  let N :ℕ →o vH (fZ k P) (Qm k P ⧸ mo k P 4) :=
    ⟨fun n=>ZY 4 n (fun _=>0),
      fun _ _ h=>VH (a6w h xu)⟩
  have hsup: (⨆ n,N n) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨p,rfl⟩:=Ideal.Quotient.mkₐ_surjective (fZ k P) (mo k P 4) x
    obtain ⟨n,hn⟩:=btB p
    exact le_iSup N n (Submodule.mem_map_of_mem hn)
  obtain ⟨q,hq⟩:=hfin.fg_top.stabilizes_of_iSup_eq N hsup
  refine ⟨q,?_⟩
  intro b d hb
  have hqd:ZY (k :=k) (P:=P) 4 b d = ⊤ := top_unique (by
    rw [hq]
    exact VH (a6w hb fun _=>In _))
  unfold lO
  rw [hqd,finrank_top,bt1]
private theorem cev
    (hP : ∀ i,bF (P i)∧Even (P i).j∧Even (P i).t)
    (i:Fin 4) (b:ℕ) (d:u5)
    (hinj : ∀ p:Qm k P,ve k P i*p∈mo k P i.val →
      p∈mo k P i.val)
    (hlift : ∀ p∈dO k P b (uh d i 1),p∈mo k P (i.val+1) →
      ∃ r∈dO k P b d,p - ve k P i*r∈mo k P i.val) :
    lO (k :=k) (P:=P) (i.val+1) b (uh d i 1)+lO (k :=k) (P:=P) i.val b d =
      lO (k :=k) (P:=P) i.val b (uh d i 1) := by
  let f :=Ideal.Quotient.factorₐ (fZ k P)
    (a6N (k :=k) (P:=P) (Un i.val))
  have hf (p:Qm k P) :f (Jw i.val p)=Jw (i.val+1) p:=rfl
  let cut:ZY (k :=k) (P:=P) i.val b (uh d i 1) →ₗ[fZ k P]
      ZY (k :=k) (P:=P) (i.val+1) b (uh d i 1) :=
    f.toLinearMap.restrict (by
      rintro _ ⟨p,hp,rfl⟩
      exact ⟨p,hp,(hf p).symm⟩)
  let mul :ZY (k :=k) (P:=P) i.val b d →ₗ[fZ k P]
      ZY (k :=k) (P:=P) i.val b (uh d i 1) :=
    (LinearMap.mulLeft (fZ k P) (Jw i.val (ve k P i))).restrict (by
      rintro _ ⟨p,hp,rfl⟩
      exact ⟨_,bFi hP b d i hp,nI (Jw i.val) _ _⟩)
  have hsurj:vZ cut:= by
    intro y
    obtain ⟨p,hp,he⟩:=y.property
    exact ⟨⟨Jw i.val p,⟨p,hp,rfl⟩⟩,u8 ((hf p).trans he)⟩
  have hmul :sI mul := by
    apply (LinearMap.ker_eq_bot (f :=mul)).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨p,_,hp⟩:=x.property
    change Jw i.val (p:Qm k P)=(x :Qm k P ⧸ mo k P i.val) at hp
    have hz :Jw i.val (ve k P i*p)=0:= by
      rw [nI]
      have h:=oq Np hx
      change Jw i.val (ve k P i)*(x :Qm k P ⧸ mo k P i.val)=0 at h
      rwa [hp]
    have hpI:=hinj p ((aCc _ _).mp hz)
    exact u8 (hp.symm.trans ((aCc _ _).mpr hpI))
  have hk :LinearMap.range mul=LinearMap.ker cut:= by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      apply LinearMap.mem_ker.mpr
      apply u8
      change f (Jw i.val (ve k P i)*(x :Qm k P ⧸ mo k P i.val))=0
      rw [nI,hf,(aCc _ _).mpr (b1K i),zero_mul]
    · intro hy
      obtain ⟨p,hp,he⟩:=y.property
      change Jw i.val p=(y :Qm k P ⧸ mo k P i.val) at he
      have hz :=oq Np (LinearMap.mem_ker.mp hy)
      change f (y :Qm k P ⧸ mo k P i.val)=0 at hz
      rw [← he,hf] at hz
      obtain ⟨r,hr,hrel⟩:=hlift p hp ((aCc _ _).mp hz)
      refine ⟨⟨Jw i.val r,⟨r,hr,rfl⟩⟩,u8 ?_⟩
      change Jw i.val (ve k P i)*Jw i.val r =
        (y :Qm k P ⧸ mo k P i.val)
      rw [← he,← nI]
      exact ((bll _ _ _).mpr hrel).symm
  have hdim:=LinearMap.finrank_range_add_finrank_ker cut
  rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,← hk,
    VO hmul] at hdim
  exact hdim
theorem of_children (h1 :c1) (h2 :c2) :UH.c3:= by
 intro k _ P hP
 have hfinite :=b4E k P
 obtain ⟨q1,hq1⟩:=h2 k P hP
 obtain ⟨q2,hq2⟩:=b5Y hfinite
 let q:=max q1 q2
 let d:Degree := fun _=>q
 refine ⟨hfinite,eG P q d,(ddE hP _ _).1,fun n => ?_⟩
 let H (r :ℕ) (e :u5) :ℝ:=lO (k :=k) (P:=P) r q e
 have hstep (i:Fin 4) (e :u5) (he : ∀ j,q≤e j) :
     H i.val (uh e i 1) - H i.val e=H (i.val+1) (uh e i 1) := by
   have hrank :=cev hP i q e (h1 k P i) (hq1 q e i (Oc _ _) fun j =>
     (Oc _ _).trans (he j))
   dsimp only [H]
   rw [sub_eq_iff_eq_add]
   exact_mod_cast hrank.symm
 let C:ℝ:=oz (fZ k P) (ap1 k P)
 have htop (e :u5) (_ : ∀ j,q≤e j) :H 4 e=C:= by
   dsimp only [H,C]
   rw [hq2 q e (le_max_right _ _)]
 have hbox :=b3Q H C q hstep htop n d (fun _=>xu)
 have hun:H 0=fun e=>((oD (eG P q e)).ncard:ℝ) := by
   funext e
   exact oq Nat.cast (b50 (k :=k) (P:=P) q e)
 rw [hun,gp1 P q n (fun x=>((oD x).ncard:ℝ)) d [0,1, 2,3]] at hbox
 exact hbox.symm
end
end akO
end
section
namespace aFS
noncomputable section
open aR lB UH akO MvPolynomial
open scoped Pointwise
abbrev SlotIndex :=Option (Fin 4)
abbrev X0:=SlotIndex→ℕ
def Vu (P:Fin 4→aU) :SlotIndex→Set zE
 | none=>lattice auxiliary
 | some i=>lattice (P i)
instance (P:Fin 4→aU) (i:SlotIndex) :yU (Vu P i) :=
 match i with
 | none=>(afS auxiliary).fintype
 | some i=>(afS (P i)).fintype
abbrev Slot (P:Fin 4→aU) :=Σ i:SlotIndex,Vu P i
abbrev Chart (P:Fin 4→aU) :=(i:SlotIndex)→Vu P i
abbrev vJ (k :Type) [lz k] (P:Fin 4→aU) :=
 lJ (Slot P) (fZ k P)
def anU (b:ℕ) (d:u5) :X0
 | none=>b
 | some i=>d i
def jT (P:Fin 4→aU) (v :Slot P) :X0 :=
 sH v.1 1
abbrev Kx (k :Type) [lz k] (P:Fin 4→aU) (d:X0) :=
 weightedHomogeneousSubmodule (fZ k P) (jT P) d
def ew (k :Type) [lz k] (P:Fin 4→aU) :
    vJ k P →ₐ[fZ k P] Qm k P :=
  vk fun v=>oK v.2.val 1
def aEy (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ) :
    Set (vJ k P) :=
  {f | (∃ d,f∈Kx k P d)∧ew k P f∈mo k P r}
def Se (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ) :
    cy (vJ k P) :=
  lI (aEy k P r)
def T2 (k :Type) [lz k] (P:Fin 4→aU) (i:Fin 4) :
    vJ k P:= by
  classical
  letI:=(afS (P i)).fintype
  exact ∑ a :oD (P i),
    C (c9 (xB k P) (fZ k P) (mD ⟨i,a⟩)) *
      mD ⟨some i,a⟩
def ke (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ) :cy (vJ k P) :=
 Se k P 0 ⊔ lI (T2 k P '' {i:Fin 4 | i.val< r})
def GW (k :Type) [lz k] (P:Fin 4→aU) (a :Chart P) :vJ k P :=
 ∏ i:SlotIndex,mD (⟨i,a i⟩:Slot P)
def bP9 (P:Fin 4→aU) :Chart P
 | none=>⟨0,asK auxiliary⟩
 | some i=>⟨0,asK (P i)⟩
def ab5 (k :Type) [lz k] (P:Fin 4→aU) :vJ k P :=
 GW k P (bP9 P)
private def alq (P:Fin 4→aU) (v :Slot P) :Exponent :=
 v.2.val
private def Bc (P:Fin 4→aU) (d:X0) :Set Exponent :=
 ∑ i:SlotIndex,d i•Vu P i
private def afB (P:Fin 4→aU) (d:X0) :Set Exponent :=
 {a | ∃ e :Slot P →₀ ℕ,
   uJ (jT P) e=d∧uJ (alq P) e=a}
private theorem aC6 (P:Fin 4→aU) (d e :X0) :
  Bc P (d+e)=Bc P d+Bc P e := by
 simp only [Bc,Qy ,add_nsmul,SU]
private theorem aUt (P:Fin 4→aU) (i:SlotIndex) :
   Bc P (sH i 1)=Vu P i:= by
 classical
 unfold Bc
 rw [LO i]
 · simp
 · intro j _ hj
   rw [SW hj,zero_nsmul]
 · simp
private theorem bOD (P:Fin 4→aU) (d:X0) :
    Bc P d=afB P d:= by
  classical
  have hadd (d e :X0) :
      afB P d+afB P e⊆afB P (d+e) := by
    intro m hm
    obtain ⟨a,⟨u,hu,rfl⟩,b,⟨v,hv,rfl⟩,rfl⟩:=Set.mem_add.mp hm
    exact ⟨u+v,by rw [uz ,hu,hv],uz _ _ _⟩
  have hzero : (0:zE)∈afB P 0 :=
    ⟨0,p5 _,p5 _⟩
  have hsingle (i:SlotIndex) :Vu P i⊆afB P (sH i 1) := by
    intro a ha
    let v :Slot P:=⟨i,⟨a,ha⟩⟩
    exact ⟨Finsupp.single v 1,by rw [Finsupp.weight_single,one_smul]; rfl,
      by rw [Kh ,OJ ]; rfl⟩
  have hscale (i:SlotIndex) (n:ℕ) :
      n•Vu P i⊆afB P (n•sH i 1) := by
    induction n with
    | zero=>simpa using hzero
    | succ n ih =>
      rw [C5 ,C5]
      exact (KH ih (hsingle i)).trans (hadd _ _)
  have hsum (s :vh SlotIndex) :
      (∑ i∈s,d i•Vu P i) ⊆
        afB P (∑ i∈s,d i•sH i 1) := by
    induction s using zcw with
    | empty=>simpa using hzero
    | @insert i s hi ih =>
      rw [NY hi,NY hi]
      exact (KH (hscale i _) ih).trans (hadd _ _)
  apply zkG
  · have hdeg: (∑ i:SlotIndex,d i•sH i (1 :ℕ))=d:= by
      funext j
      simp [TI,Qx]
    simpa only [Bc,hdeg] using hsum Finset.univ
  · clear hsum
    rintro _ ⟨e,rfl,rfl⟩
    induction e using WY with
    | zero=>simp [Bc]
    | add e f he hf =>
      rw [uz ,uz ,aC6]
      exact Set.mem_add.mpr ⟨_,he,_,hf,rfl⟩
    | single v n =>
      rw [Kh,Kh]
      have hv :alq P v∈Bc P (jT P v) := by
        rw [jT,aUt]
        exact v.2.property
      induction n with
      | zero=>simp [Bc]
      | succ n ih =>
        rw [C5 ,C5 ,aC6]
        exact Set.mem_add.mpr ⟨_,ih,_,hv,rfl⟩
variable {k :Type} [lz k] {P:Fin 4→aU}
private theorem aT6 (e :Slot P →₀ ℕ) :
   ew k P (oK e 1)=oK (uJ (alq P) e) 1 := by
 induction e using WY with
 | zero=>simp [monomial_zero']
 | add e f he hf =>
   rw [← ze (1 :fZ k P),← Ok,nI,he,hf,
    Ok,ze,uz]
 | single v n =>
   rw [← zp9,t8 ,ew,Dw]
   change (oK (alq P v) (1 :fZ k P))^n= _
   rw [monomial_pow,one_pow,Kh]
theorem aOJ
   (hP : ∀ i,bF (P i)∧Even (P i).j∧Even (P i).t) (b:ℕ) (d:u5) :
   (Kx k P (anU b d)).map (ew k P).toLinearMap=dO k P b d:= by
 have hset :oD (eG P b d)=afB P (anU b d) := by
   rw [← bOD,euO hP,Bc,Fintype.sum_option,Fin.sum_univ_four]
   simp only [Vu,anU]
   ac_rfl
 have hS:Kx k P (anU b d)=restrictSupport (fZ k P)
     {e | uJ (jT P) e=anU b d} :=
   weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
 rw [hS,restrictSupport_eq_span,Submodule.map_span,dO,hset,restrictSupport_eq_span]
 congr 1
 ext p
 constructor
 · rintro ⟨_,⟨e,he,rfl⟩,rfl⟩
   rw [PD,aT6]
   exact ⟨_,⟨e,he,rfl⟩,rfl⟩
 · rintro ⟨a,ha,rfl⟩
   obtain ⟨e,he,hea⟩:=ha
   exact ⟨_,⟨e,he,rfl⟩,by rw [PD,aT6,hea]⟩
theorem dNZ (d:X0) :
  anU (d none) (fun i=>d (some i))=d:= by
 funext i
 cases i <;> rfl
theorem dNY (b:ℕ) (d:u5) (i:Fin 4) :
   anU b (uh d i 1)=anU b d+Pi.single (some i) 1 := by
 funext j
 cases j with
 | none=>simp [anU]
 | some j=>simp [anU,shift,Pi.single_apply]
theorem aN7 (i:Fin 4) :
  T2 k P i∈Kx k P (sH (some i) 1) := by
 classical
 apply zo3
 intro a _
 have hC:=isWeightedHomogeneous_C (jT P)
  (c9 (xB k P) (fZ k P) (mD ⟨i,a⟩))
 have hX:=isWeightedHomogeneous_X (fZ k P) (jT P) (⟨some i,a⟩:Slot P)
 simpa only [mem_weightedHomogeneousSubmodule,zero_add,jT] using hC.mul hX
theorem aNd (i:Fin 4) :
  ew k P (T2 k P i)=ve k P i:= by
 classical
 simp only [T2,ve,t5 ,nI,ew,aeval_C,
  algebraMap_eq,Dw ,C_mul_monomial,zg]
end
end aFS
end
section
namespace aFS
noncomputable section
open aR lB UH akO MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 :Prop :=
  ∀ (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ),
    (∀ g∈aEy k P r,∀ a :Chart P,
      ∃ n:ℕ,GW k P a^n*g∈ke k P r) →
    ∃ q:ℕ,∀ d:X0,(∀ j,q≤d j) →
      ∀ f∈Kx k P d,f∈Se k P r→f∈ke k P r
def c2 :Prop :=
  ∀ (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ) (a :Chart P)
    (f :vJ k P) (n:ℕ),
    ab5 k P^n*f∈ke k P r →
      ∃ m:ℕ,GW k P a^m*f∈ke k P r
variable {k :Type} [lz k] {P:Fin 4→aU}
private theorem b0c :
  ew k P (ab5 k P)=1 := by
 classical
 rw [ab5,GW,JQ]
 apply Finset.prod_eq_one
 intro j _
 cases j <;> simp [bP9,ew,monomial_zero']
private theorem bYC :
  (ab5 k P).IsWeightedHomogeneous (jT P) (fun _=>1) := by
 classical
 have hweight: (∑ j:SlotIndex,(sH j 1 :X0))=fun _=>1 := by
  funext j
  simp [TI,Qx]
 rw [← hweight,ab5,GW]
 exact IsWeightedHomogeneous.prod _ _ _ fun j _ =>
  isWeightedHomogeneous_X (fZ k P) (jT P) (⟨j,bP9 P j⟩:Slot P)
private theorem fVZ
   (hP : ∀ i,bF (P i)∧Even (P i).j∧Even (P i).t)
   (r :ℕ) (f :vJ k P) (hf :f∈aEy k P r) :
   ∃ n:ℕ,ab5 k P^n*f∈ke k P r := by
 classical
 obtain ⟨⟨d,hfd⟩,hfI⟩:=hf
 let s :vh (Fin 4) :=Finset.univ.filter fun j=>j.val< r
 have hs : (↑s :Set (Fin 4)) = {j | j.val< r} := by
   ext j
   simp [s]
 have hfspan:ew k P f∈PM (Qm k P) (ve k P '' ↑s) := by
   rw [hs]
   exact hfI
 rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hfspan
 obtain ⟨c,hc⟩:=hfspan
 simp only [G1] at hc
 choose q hq using fun j=>btB (c j)
 let n:=Finset.univ.sup q+1
 let D:X0:=(fun _=>n)+d
 have hsingle (j:Fin 4) (l:SlotIndex) : (sH (some j) 1 :X0) l≤1 := by
   by_cases h:l=some j
   · simp [h]
   · simp [SW h]
 have hdegree (j:Fin 4) :D - sH (some j) 1+Pi.single (some j) 1=D:= by
   funext l
   have hj:=hsingle j l
   change D l-(sH (some j) 1 :X0) l+(sH (some j) 1 :X0) l=D l
   apply Vq
   change (sH (some j) 1 :X0) l≤Finset.univ.sup q+1+d l
   omega
 have hlift (j:Fin 4) : ∃ u∈Kx k P (D - sH (some j) 1),ew k P u=c j:= by
   let E :=D - sH (some j) 1
   have hpad:q j≤E none := by
     have hqj:q j≤Finset.univ.sup q:=Ee (wB j)
     have hj:=hsingle j none
     change q j≤Finset.univ.sup q+1+d none-(sH (some j) 1 :X0) none
     omega
   have hm:=a6w hpad (show (fun _:Fin 4=>0)≤fun l=>E (some l) from
     fun _=>In _) (hq j)
   rw [← aOJ hP,dNZ] at hm
   exact hm
 choose u hu hud using hlift
 let g := ∑ j∈s,u j*T2 k P j
 have hgd:g∈Kx k P D:= by
   apply zo3
   intro j _
   rw [← hdegree j]
   exact (show (u j).IsWeightedHomogeneous _ _ from hu j).mul
     (show (T2 k P j).IsWeightedHomogeneous _ _ from aN7 j)
 have hg:ew k P g=ew k P f := by
   simpa only [g,t5 ,nI,hud,aNd] using hc
 have hgcut:g∈lI (T2 k P '' {j:Fin 4 | j.val< r}) := by
   apply Ideal.sum_mem
   intro j hj
   exact Ideal.mul_mem_left _ _ (qJ ⟨j,(Finset.mem_filter.mp hj).2,rfl⟩)
 have hweight:n•(fun _=>1 :X0)=fun _=>n:= by
   funext j
   simp [FQ]
 have hpower :=(bYC (k :=k) (P:=P)).pow n
 rw [hweight] at hpower
 have hprod: (ab5 k P^n*f).IsWeightedHomogeneous (jT P) D :=
   hpower.mul hfd
 have hrel :ab5 k P^n*f - g∈Se k P 0:= by
   apply qJ
   refine ⟨⟨D,hprod.sub hgd⟩,?_⟩
   rw [xm,nI,t8 ,b0c,one_pow,ze,hg,sub_self]
   exact (mo k P 0).zero_mem
 have hrem:ab5 k P^n*f - g∈ke k P r :=
   Ye hrel
 have hcut:g∈ke k P r :=Yc hgcut
 exact ⟨n,by simpa only [sub_add_cancel] using (ke k P r).add_mem hrem hcut⟩
private theorem Zy {g:vJ k P} {e :X0}
   (hg:g∈Kx k P e) (f :vJ k P) (d:X0) :
   wR (jT P) (d+e) (f * g) =
     wR (jT P) d f * g:= by
 classical
 induction f using Zg with
 | monomial a c =>
   have ha :=LP (jT P) a c rfl
   have hg' : g.IsWeightedHomogeneous (jT P) e :=hg
   simp only [Hw (ha.mul hg'),
     Hw ha,ZJ]
   split <;> simp_all
 | add p r hp hr=>simp [add_mul,hp,hr]
private theorem ce4 (r :ℕ) :
  Se k P r≤(mo k P r).comap (ew k P).toRingHom :=
 Ideal.span_le.mpr fun _ h=>h.2
private theorem ce3 (r :ℕ) :
  (Se k P r).IsHomogeneous (Kx k P) :=
 Ideal.homogeneous_span _ _ fun _ h=>h.1
private theorem a6N {r s :ℕ} (h:r≤ s) :
  mo k P r≤ mo k P s :=
 N0 (Set.image_mono fun _ hj=>lt_of_lt_of_le hj h)
private theorem bZm (i:Fin 4) :
   ke k P (i.val+1)≤Se k P i.val ⊔ lI {T2 k P i} := by
 have hzero :Se k P 0≤Se k P i.val := by
   apply N0
   intro f hf
   exact ⟨hf.1,a6N (In i.val) hf.2⟩
 apply t9 (hzero.trans z7)
 apply Ideal.span_le.mpr
 rintro _ ⟨j,hj,rfl⟩
 change j.val< i.val+1 at hj
 by_cases hji:j=i
 · subst j
   exact Yc (WD _)
 · have hlt:j.val< i.val := by
    have hn:j.val≠i.val := fun he=>hji (Fin.ext he)
    omega
   apply Ye
   apply qJ
   exact ⟨⟨_,aN7 j⟩,by
    rw [aNd]
    exact qJ ⟨j,hlt,rfl⟩⟩
theorem of_children (h1 :c1) (h2 :c2) :akO.c2 := by
 classical
 intro k _ P hP
 have hlocal (r :ℕ) (f :vJ k P) (hf :f∈aEy k P r) (a :Chart P) :
     ∃ n:ℕ,GW k P a^n*f∈ke k P r := by
   obtain ⟨n,hn⟩:=fVZ hP r f hf
   exact h2 k P r a f n hn
 choose q hq using fun i:Fin 4=>h1 k P (i.val+1) (hlocal (i.val+1))
 refine ⟨Finset.univ.sup q,?_⟩
 intro b d i hb hd p hp hpI
 rw [← aOJ hP] at hp
 obtain ⟨f,hf,hfp⟩:=hp
 change ew k P f=p at hfp
 have hfI:f∈Se k P (i.val+1) :=
   qJ ⟨⟨_,hf⟩,hfp ▸ hpI⟩
 have hqi:q i≤Finset.univ.sup q:=Ee (wB i)
 have hqd : ∀ j,q i≤anU b (uh d i 1) j:= by
   intro j
   cases j with
   | none=>exact hqi.trans hb
   | some j=>exact hqi.trans ((hd j).trans (Nat.le_add_right _ _))
 have hJ:=bZm i (hq i _ hqd f hf hfI)
 rw [sup_comm] at hJ
 obtain ⟨m,g,hg,hsum⟩:=Ideal.mem_span_singleton_sup.mp hJ
 let u:=wR (jT P) (anU b d) m
 let s :=wR (jT P) (anU b (uh d i 1)) g
 have hs :s∈Se k P i.val :=
   weightedHomogeneousComponent_mem_of_mem _ _ (ce3 i.val) hg _
 have hfg:u*T2 k P i+s=f := by
   have he :=oq (wR (jT P) (anU b (uh d i 1))) hsum
   rw [uz ,zfp (show f.IsWeightedHomogeneous _ _ from hf)]
     at he
   change wR (jT P) (anU b (uh d i 1))
     (m*T2 k P i)+s=f at he
   conv at he=>lhs; lhs; rw [dNY,Zy (aN7 i)]
   exact he
 have hsI:ew k P s∈mo k P i.val :=ce4 i.val hs
 refine ⟨ew k P u,?_,?_⟩
 · rw [← aOJ hP]
   exact ⟨u,zbF _ _ _,rfl⟩
 · have he :=oq (ew k P) hfg
   rw [uz ,nI,aNd,hfp] at he
   rw [← he,v9 (ve k P i),zYK]
   exact hsI
end
end aFS
end
section
namespace cym
noncomputable section
open aR UH akO MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance euF (p:aU) :yU (oD p) :=
 (afS p).fintype
private abbrev Index (P:Fin 4→aU) :=Σ i:Fin 4,oD (P i)
private abbrev aRH (k :Type) [lz k] (P:Fin 4→aU) :=
 lJ (Fin 4) (xB k P)
private abbrev X5 (k :Type) [lz k] {P:Fin 4→aU} (v :Index P) :=
 lJ {w:Index P // w≠v} (gQ k)
variable {k :Type} [lz k] {P:Fin 4→aU}
private def cHN (i:Fin 4) :oD (P i) :=⟨0,asK _⟩
private def bcQ (i:Fin 4) :Index P:=⟨i,cHN i⟩
private def Tg (v :Index P) :aRH k P ≃+* ox (X5 k v) := by
 classical
 exact (commAlgEquiv k (Fin 4) (Index P)).toRingEquiv.trans
  ((renameEquiv (gQ k) (Equiv.optionSubtypeNe v).symm).toRingEquiv.trans
    (optionEquivLeft (gQ k) {w:Index P // w≠v}).toRingEquiv)
private theorem cbM (v :Index P) :
  Tg (k :=k) v (C (mD v))=Polynomial.X:= by
 classical
 simp [Tg,Vz]
private theorem cbL (v w:Index P) (h:w≠v) :
  Tg (k :=k) v (C (mD w))=oj (mD ⟨w,h⟩) := by
 classical
 simp [Tg,Vz ,Equiv.optionSubtypeNe_symm_of_ne h]
private theorem cbI (v :Index P) (j:Fin 4) :
  Tg (k :=k) v (mD j)=oj (C (mD j)) := by
 classical
 simp [Tg,Vz]
private theorem cbK (v :Index P) (a :zE) :
  Tg (k :=k) v (oK a 1)=oj (C (oK a 1)) := by
 simp only [monic_monomial_eq,Finsupp.prod,JQ,t8 ,cbI]
private def ava (k :Type) [lz k] (P:Fin 4→aU) (j:Fin 4)
   (a :oD (P j)) :aRH k P :=
 C (mD (⟨j,a⟩:Index P))*oK a.1 1
private def Nk (k :Type) [lz k] (P:Fin 4→aU) (j:Fin 4) :
   aRH k P :=
 ∑ a :oD (P j),ava k P j a
private def aol (k :Type) [lz k] (P:Fin 4→aU) (i:Fin 4) :
  cy (aRH k P) :=
 lI (Nk k P '' {j:Fin 4 | j.val< i.val})
private def awd (v :Index P) (j:Fin 4) (a :oD (P j)) :X5 k v := by
 classical
 exact if h: (⟨j,a⟩:Index P)=v then 0
  else mD ⟨⟨j,a⟩,h⟩*C (oK a.1 1)
private def akf (v :Index P) (j:Fin 4) :X5 k v :=
 ∑ a :oD (P j),awd v j a
private theorem btC (v :Index P) (j:Fin 4) (a :oD (P j))
  (h: (⟨j,a⟩:Index P)≠v) :
  Tg v (ava k P j a)=oj (awd v j a) := by
 simp [ava,awd,h,cbL v _ h,cbK]
private theorem cbN (i j:Fin 4) (hji:j.val< i.val) :
   Tg (bcQ i) (Nk k P j) =
     oj (akf (bcQ i) j) := by
 rw [Nk,akf,t5 ,t5]
 refine vw rfl fun a _=>btC _ _ _ ?_
 exact fun h=>(ne_of_lt hji) (oq (fun w:Index P=>w.1.val) h)
private theorem cbJ (i:Fin 4) :
   Tg (bcQ i) (Nk k P i) =
     p9+Polynomial.C (akf (bcQ i) i) := by
 classical
 let a₀:oD (P i) :=cHN i
 let v :Index P:=bcQ i
 change Tg v (Nk k P i)=p9+Polynomial.C (akf v i)
 have hterm :ava k P i a₀=C (mD v) := by
   change C (mD v)*oK (0:zE) 1=C (mD v)
   rw [monomial_zero',C_1,zg]
 have h₀:Tg v (ava k P i a₀)=Polynomial.X:= by
   rw [hterm,cbM]
 have hr₀:awd (k :=k) v i a₀=0:= by
   unfold awd
   exact dite_eq_left (show (⟨i,a₀⟩:Index P)=v from rfl)
 rw [Nk,akf,t5 ,t5 ,
   ← zT2 _ _ (wB a₀),
   ← zT2 _ _ (wB a₀),h₀,hr₀,p5 ,zero_add]
 congr 1
 refine vw rfl fun a ha=>btC _ _ _ ?_
 intro h
 apply (Finset.mem_erase.mp ha).1
 exact u8 (oq (fun w:Index P=>(w.2 :zE)) h)
private theorem bWb {B:Type*} [lV B] (J:cy B) (b:B)
  (q:ox B) (h: (p9+Polynomial.C b)*q∈J.map oj) :
  q∈J.map Polynomial.C:= by
 let f :=pU (oy J)
 have hf :nX f=J.map Polynomial.C:= by
  dsimp only [f]
  rw [SM,Eg]
 rw [← hf,Cy ,nI] at h
 rw [← hf,Cy]
 apply (Polynomial.monic_X_add_C (oy J b)).mul_right_eq_zero_iff.mp
 simpa [f] using h
private theorem bra (i:Fin 4) (q:aRH k P)
  (h:Nk k P i*q∈aol k P i) :
  q∈aol k P i:= by
 let v :Index P:=bcQ i
 let e :=Tg (k :=k) v
 let J:cy (X5 k v) :=lI (akf v '' {j:Fin 4 | j.val< i.val})
 have hJ: (aol k P i).map e.toRingHom=J.map Polynomial.C:= by
  dsimp only [J]
  rw [aol,qy ,qy ,z8 ,z8]
  exact oq lI (F9 fun j hj=>cbN (k :=k) i j hj)
 have hq:=xW e.toRingHom h
 change e (Nk k P i*q)∈(aol k P i).map e.toRingHom at hq
 rw [hJ,nI,show e (Nk k P i) =
  p9+Polynomial.C (akf v i) from cbJ (k :=k) i] at hq
 have hq' := bWb J (akf v i) (e q) hq
 rw [← hJ] at hq'
 obtain ⟨r,hr,he⟩:=(Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hq'
 exact (e.injective he) ▸ hr
private theorem bsl (j:Fin 4) :
  c9 (aRH k P) (Qm k P) (Nk k P j) =
   ve k P j:= by
 simp only [Nk,ava,ve,MvPolynomial.algebraMap_def,
  t5 ,MvPolynomial.map_monomial,C_mul_monomial,zg]
theorem proof :akO.c1 := by
 intro k _ P i p hp
 let M:Submonoid (aRH k P) :=(xB k P)⁰.map (C (σ:=Fin 4))
 let J:=aol k P i
 let f :=c9 (aRH k P) (Qm k P)
 have hJ:J.map f=mo k P i.val := by
   dsimp only [J]
   rw [aol,mo,qy ,z8]
   exact oq lI (F9 fun j _=>bsl j)
 obtain ⟨⟨q,s⟩,hs⟩:=zg4 M p
 change p*f s=f q at hs
 have h:f (Nk k P i*q)∈J.map f := by
   rw [nI,show f (Nk k P i)=ve k P i from
     bsl i,← hs,← xI,hJ]
   exact (mo k P i.val).mul_mem_right _ hp
 obtain ⟨t,ht,htq⟩ :=
   (Ar M (Qm k P) J _).mp h
 have hq:t*q∈J:= by
   apply bra i
   rw [Gr]
   exact htq
 have hfp:f q∈J.map f :=
   (Ar M (Qm k P) J q).mpr ⟨t,ht,hq⟩
 rw [hJ,← hs] at hfp
 exact (Ideal.mul_unit_mem_iff_mem _ (C4 (Qm k P) s)).mp hfp
end
end cym
end
section
namespace baq
noncomputable section
open aR UH akO aFS MvPolynomial
abbrev aiy (P:Fin 4→aU) :=Σ i:Fin 4,oD (P i)
private abbrev a3r :X0 ≃+ (SlotIndex →₀ ℕ) :=
 Finsupp.addEquivFunOnFinite.symm
private def aaB (P:Fin 4→aU) : (Slot P →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
 uJ fun v=>v.2.val
private def XE (P:Fin 4→aU) : (Slot P →₀ ℕ) →+ ((SlotIndex ⊕ Fin 4) →₀ ℕ) :=
 Finsupp.sumFinsuppAddEquivProdFinsupp.symm.toAddMonoidHom.comp
  ((a3r.toAddMonoidHom.comp (uJ (jT P))).prod (aaB P))
private theorem bxp {P:Fin 4→aU} {e f :Slot P →₀ ℕ} :
    XE P e=XE P f ↔
      uJ (jT P) e=uJ (jT P) f ∧
        aaB P e=aaB P f := by
  change Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_,_) =
    Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_,_)↔_
  rw [Zh,Prod.ext_iff]
  change (a3r (uJ (jT P) e) =
    a3r (uJ (jT P) f)∧_)↔_
  rw [Zh]
private def avB {R σ τ:Type*} [lV R] (w: (σ →₀ ℕ) →+ (τ →₀ ℕ)) :
  lJ σ R →ₐ[R] lJ τ R :=
 AddMonoidAlgebra.mapDomainAlgHom R R w
private theorem ajT {R σ τ:Type*} [lV R]
  (w: (σ →₀ ℕ) →+ (τ →₀ ℕ)) (e :σ →₀ ℕ) (c:R) :
  avB w (oK e c)=oK (w e) c:= by
 change AddMonoidAlgebra.mapDomain w (AddMonoidAlgebra.single e c)= _
 rw [AddMonoidAlgebra.mapDomain_single]
 rfl
def Nb (P:Fin 4→aU) (R:Type*) [lV R] :cy (lJ (Slot P) R) :=
  lI {p | ∃ e f :Slot P →₀ ℕ,XE P e=XE P f ∧
    p=oK e 1 - oK f 1}
theorem bsj {R S:Type*} [lV R] [lV S]
   (P:Fin 4→aU) (g:R →+* S) :
   (Nb P R).map (oY g)=Nb P S:= by
 rw [Nb,qy ,Nb]
 congr 1
 ext p
 constructor
 · rintro ⟨_,⟨e,f,h,rfl⟩,rfl⟩
   exact ⟨e,f,h,by simp⟩
 · rintro ⟨e,f,h,rfl⟩
   exact ⟨_,⟨e,f,h,rfl⟩,by simp⟩
private theorem brR {P:Fin 4→aU} {R τ:Type*} [lV R]
   (s :Set (Slot P →₀ ℕ)) (w: (Slot P →₀ ℕ)→(τ →₀ ℕ))
   (h : ∀ e∈s,∀ f∈s,w e=w f→XE P e=XE P f) :
   ∃ l:lJ τ R →ₗ[R] (lJ (Slot P) R ⧸ Nb P R),
     ∀ e∈s,l (oK (w e) 1)=oy _ (oK e 1) := by
 classical
 let J:=Nb P R
 let g (a :τ →₀ ℕ) :lJ (Slot P) R ⧸ J :=
   if ha : ∃ e∈s,w e=a then oy J (oK ha.choose 1) else 0
 refine ⟨(IT τ R).constr R g,fun e he => ?_⟩
 change (IT τ R).constr R g ((IT τ R) (w e))= _
 rw [Module.Basis.constr_basis]
 let he' : ∃ f∈s,w f=w e :=⟨e,he,rfl⟩
 dsimp only [g]
 rw [dite_eq_left he',zdf]
 exact qJ ⟨_,_,h _ he'.choose_spec.1 e he he'.choose_spec.2,rfl⟩
private theorem bxs (P:Fin 4→aU) (R:Type*) [lV R] :
   nX (avB (R:=R) (XE P)).toRingHom=Nb P R:= by
 let J:=Nb P R
 let φ:=avB (R:=R) (XE P)
 obtain ⟨l,hl⟩:=brR (R:=R) Set.univ (XE P)
   (fun _ _ _ _ h=>h)
 have hfac:l.comp φ.toLinearMap=(zh R J).toLinearMap:= by
   apply (IT (Slot P) R).ext
   intro e
   simp only [coe_basisMonomials,LinearMap.comp_apply,PD]
   rw [show φ (oK e 1)=oK (XE P e) 1 from ajT _ _ _]
   exact hl e (Set.mem_univ _)
 apply vj
 · intro p hp
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   have h:=zmU hfac p
   change l (φ p)=oy J p at h
   change φ p=0 at hp
   simpa [hp] using h.symm
 · apply Ideal.span_le.mpr
   rintro _ ⟨e,f,h,rfl⟩
   change avB (R:=R) (XE P) (oK e 1 - oK f 1)=0
   rw [xm,ajT,ajT,h,sub_self]
private theorem boT (k :Type) [lz k] (P:Fin 4→aU) :
  ew k P=avB (aaB P) := by
 apply zpJ
 intro v
 rw [ew,Dw ,mD,ajT,aaB,Kh,OJ]
theorem ce5 (k :Type) [lz k] (P:Fin 4→aU) :
    Se k P 0=Nb P (fZ k P) := by
  classical
  have hprefix :mo k P 0 = ⊥ := by simp [mo]
  apply vj
  · apply Ideal.span_le.mpr
    rintro p ⟨⟨d,hd⟩,hp⟩
    have hz :ew k P p=0:= by simpa [hprefix] using hp
    let J:=Nb P (fZ k P)
    obtain ⟨l,hl⟩:=brR (R:=fZ k P)
      {e | uJ (jT P) e=d} (aaB P)
      (fun e he f hf h=>bxp.mpr ⟨he.trans hf.symm,h⟩)
    let q:=zh (fZ k P) J
    have hfac:l (ew k P p)=q p:= by
      calc
        l (ew k P p)=l (ew k P (∑ e∈p.support,oK e (p.coeff e))) :=
          oq (fun r=>l (ew k P r)) p.as_sum
        _=q (∑ e∈p.support,oK e (p.coeff e)) := by
          simp only [t5]
          apply vw rfl
          intro e he
          rw [show oK e (p.coeff e)=p.coeff e•oK e 1 by
            simp [smul_monomial]]
          simp only [map_smul,boT,ajT,
            hl e (hd (mem_support_iff.mp he))]
          rfl
        _=q p:=(oq q p.as_sum).symm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p=0
    rw [← hfac,hz,p5]
  · apply Ideal.span_le.mpr
    rintro _ ⟨e,f,h,rfl⟩
    obtain ⟨hd,ha⟩:=bxp.mp h
    apply qJ
    refine ⟨⟨_,Submodule.sub_mem (Kx k P (uJ (jT P) e)) ?_ ?_⟩,?_⟩
    · exact LP _ _ _ rfl
    · exact LP _ _ _ hd.symm
    · rw [hprefix,TH,xm,boT,
        ajT,ajT,ha,sub_self]
abbrev aqn (k :Type) [lz k] (P:Fin 4→aU) :=
 lJ (Slot P) k ⧸ Nb P k
instance (k :Type) [lz k] (P:Fin 4→aU) :IsDomain (aqn k P) := by
 have : (Nb P k).IsPrime := by
  rw [← bxs]
  exact zgL _
 infer_instance
theorem b9p {k :Type} [lz k] {P:Fin 4→aU} (v :Slot P) :
  oy (Nb P k) (mD v)≠0:= by
 intro h
 have hm:=Ideal.Quotient.eq_zero_iff_mem.mp h
 rw [← bxs] at hm
 change avB (R:=k) (XE P) (mD v)=0 at hm
 rw [mD,ajT,monomial_eq_zero] at hm
 exact one_ne_zero hm
end
end baq
end
section
namespace aA4
open UH Ideal IsLocalRing RingTheory.Sequence
def c1 :Prop :=
  ∀ (k :Type) [lz k] (p:cy (gQ k)) [p.IsMaximal],
    ∃ s :List (qM p),s.length=4 ∧
      (∀ x∈s,x∈pL (qM p)) ∧
      IsRegular (qM p) s
def c2 :Prop :=
  ∀ (R:Type) [lV R] [zS R] [Au R] (f :Fin 4→R),
    (∃ s :List R,s.length=4∧(∀ x∈s,x∈pL R)∧IsRegular R s) →
    (lI (uW f)).radical=pL R →
    ∀ (i:Fin 4) (x :R),f i*x∈aoC f i→x∈aoC f i
private theorem eOc {k R:Type*}
   [lz k] [lV R] [t7 k R] (J P:cy R) [P.IsPrime]
   [ov k (R ⧸ J)] (hle :J≤P) :P.IsMaximal:= by
 let m:=oy J
 let Q:=P.map m
 have :IsArtinianRing (R ⧸ J) :=IsArtinianRing.of_finite k _
 have :Q.IsPrime :=Ideal.map_isPrime_of_surjective
   zf (by simpa only [m,Eg] using hle)
 have he :Q.comap m=P:= by
   rw [show Q=P.map m from rfl,Iw m zf ,
     ← JM,show nX m=J from Eg ,
     sup_eq_left.mpr hle]
 rw [← he]
 exact Xg m zf
private theorem fSR {k R:Type*}
    [lz k] [lV R] [t7 k R] (J p:cy R) [p.IsMaximal]
    [ov k (R ⧸ J)] (hle :J≤p) :
    (J.map (c9 R (qM p))).radical =
      pL (qM p) := by
  let S:=qM p
  let φ:=c9 R S
  have hp:p.map φ=pL S:=Localization.AtPrime.map_eq_maximalIdeal (I:=p)
  apply vj
  · exact (Pv S).isPrime.radical_le_iff.mpr
      ((S2 (f :=φ) hle).trans_eq hp)
  · intro y hy
    rw [Ideal.radical_eq_sInf,Ideal.mem_sInf]
    intro Q hQ
    have :Q.IsPrime :=hQ.2
    let P:= Q.comap φ
    have :P.IsPrime :=Ideal.comap_isPrime φ Q
    have hJP:J≤P:=Ideal.map_le_iff_le_comap.mp hQ.1
    have hPp:P≤p:= by
      have hQmax :=IsLocalRing.le_maximalIdeal (J:= Q) hQ.2.ne_top
      exact (Qw (f :=φ) hQmax).trans_eq
        (Localization.AtPrime.under_maximalIdeal (I:=p))
    have hP:P=p :=
      (eOc (k :=k) J P hJP).eq_of_le
        (show p ≠ ⊤ from Ideal.IsMaximal.ne_top Ea) hPp
    have hQp:Q=pL S:= by
      calc
        Q=P.map φ:=(Vl p.primeCompl S Q).symm
        _=pL S:=(oq (Ideal.map φ) hP).trans hp
    exact hQp.symm ▸ hy
private theorem dEk {k :Type} [lz k] (h₁:c1) (h₂:c2)
   (f :Fin 4→ gQ k) [ov k (Rh f)]
   (i:Fin 4) (x :gQ k) (hx :f i*x∈aoC f i) :
   x∈aoC f i:= by
 by_contra h
 let I:=aoC f i
 let T:=I.colon {x}
 have hT:T ≠ ⊤ := by
   intro ht
   have ht' : (1 :gQ k)∈T:= by simp [ht]
   have hx' := Submodule.mem_colon_singleton.mp ht'
   exact h (by simpa only [OJ] using hx')
 obtain ⟨p,hp,hTp⟩:=zsl T hT
 have hIp:I≤p:=Ideal.le_colon.trans hTp
 have hfp:Su f≤p:= by
   apply Ideal.span_le.mpr
   rintro _ ⟨j,rfl⟩
   by_cases hj:j=i
   · subst j
     exact hTp (Submodule.mem_colon_singleton.mpr hx)
   · exact hIp (qJ ⟨j,hj,rfl⟩)
 let S:=qM p
 let φ:=c9 (gQ k) S
 have hJ: (Su f).map φ=lI (uW (φ ∘ f)) := by
   rw [qy ,NX]
 have hI:I.map φ=aoC (φ ∘ f) i:= by
   change (lI (f '' {j | j≠i})).map φ=lI ((φ ∘ f) '' {j | j≠i})
   rw [qy ,z8]
   rfl
 have hrad: (lI (uW (φ ∘ f))).radical=pL S:= by
   rw [← hJ]
   exact fSR (k :=k) _ _ hfp
 have hmul : (φ ∘ f) i*φ x∈aoC (φ ∘ f) i:= by
   rw [← hI]
   change φ (f i)*φ x∈I.map φ
   rw [← nI]
   exact xW φ hx
 have hloc:=h₂ S (φ ∘ f) (h₁ k p) hrad i (φ x) hmul
 rw [← hI] at hloc
 obtain ⟨m,hm,hmx⟩ :=
   (Ar p.primeCompl S I x).mp hloc
 exact (Ideal.mem_primeCompl_iff.mp hm) (hTp (Submodule.mem_colon_singleton.mpr hmx))
private theorem deW {R:Type*} [lV R] (f :Fin 4→R) (i:Fin 4) (a :R) :
   lI (uW (vG f i a))=aoC f i ⊔ lI {a} := by
 classical
 rw [aoC,← Ideal.span_union]
 congr 1
 ext x
 constructor
 · rintro ⟨j,rfl⟩
   by_cases hj:j=i
   · subst j
     exact Or.inr (by simp)
   · exact Or.inl ⟨j,hj,(XB hj a f).symm⟩
 · rintro (⟨j,hj,rfl⟩ | h)
   · exact ⟨j,XB hj a f⟩
   · obtain rfl :=Set.mem_singleton_iff.mp h
     exact ⟨i,by simp⟩
private theorem bOl {k :Type} [lz k] (h₁:c1) (h₂:c2) (f :Fin 4→ gQ k)
    [ov k (Rh f)] (i:Fin 4) :
    ov k (Rh (vG f i (f i^2))) ∧
      oz k (Rh (vG f i (f i^2))) =
        2*oz k (Rh f) := by
  classical
  have hJ:Su f=aoC f i ⊔ lI {f i} := by
    simpa only [Function.update_eq_self] using deW f i (f i)
  have :ov k (gQ k ⧸ (aoC f i ⊔ lI {f i})) := by
    rw [← hJ]
    infer_instance
  change ov k (gQ k ⧸ Su (vG f i (f i^2))) ∧
    oz k (gQ k ⧸ Su (vG f i (f i^2))) =
      2*oz k (gQ k ⧸ Su f)
  have hJ₂:Su (vG f i (f i^2)) =
      aoC f i ⊔ lI {f i^2} := deW f i (f i^2)
  rw [hJ₂,hJ]
  exact gup (k :=k) _ _ (dEk h₁ h₂ f i)
theorem of_children (h₁:c1) (h₂:c2) :UH.c1 := by
 classical
 intro k _ f hf
 let f₁:=vG f 0 (f 0^2)
 let f₂:=vG f₁ 1 (f₁ 1^2)
 let f₃:=vG f₂ 2 (f₂ 2^2)
 let f₄:=vG f₃ 3 (f₃ 3^2)
 obtain ⟨hf₁,hlen₁⟩:=bOl h₁ h₂ f 0
 change ov k (Rh f₁) at hf₁
 obtain ⟨hf₂,hlen₂⟩:=bOl h₁ h₂ f₁ 1
 change ov k (Rh f₂) at hf₂
 obtain ⟨hf₃,hlen₃⟩:=bOl h₁ h₂ f₂ 2
 change ov k (Rh f₃) at hf₃
 obtain ⟨hf₄,hlen₄⟩:=bOl h₁ h₂ f₃ 3
 have he :f₄=fun i=>f i^2 := by
  funext i
  fin_cases i <;> simp [f₄,f₃,f₂,f₁,vG]
 rw [← he]
 refine ⟨hf₄,?_⟩
 change oz k (Rh f₄)= _
 change oz k (Rh f₄)=2*oz k (Rh f₃) at hlen₄
 change oz k (Rh f₃)=2*oz k (Rh f₂) at hlen₃
 change oz k (Rh f₂)=2*oz k (Rh f₁) at hlen₂
 change oz k (Rh f₁)=2*oz k (Rh f) at hlen₁
 omega
end aA4
end
section
namespace aKo
noncomputable section
open aR UH abG MvPolynomial
open scoped nonZeroDivisors
def c1 :Prop :=
  ∀ (L:Type) [lz L] (g:Fin 4→pz L),
    ov L (Rh (fun i=>n5 (g i))) →
    ∀ (m:cy (pz L)) [m.IsMaximal],aAo g≤ m →
      ∃ rs :List (qM m),
        rs.length=5 ∧
        (∀ r∈rs,r∈(aAo g).map (c9 (pz L) (qM m))) ∧
        pG (qM m) rs
def c2 :Prop :=
  ∀ (L R:Type) [lz L] [Fz L] [lV R] [Au R]
    [zS R] [t7 L R] (u:Fin 4→R) (t:R),
    let J:=lI (uW u)
    let I:=J ⊔ lI {t}
    I≤pL R →
    (∃ rs :List R,rs.length=5∧(∀ r∈rs,r∈I) ∧
      pG R rs) →
    qU (R ⧸ J) (oy J t)
section Relations
variable {L:Type} [lz L]
private theorem ar6:vZ (n5 (L:=L)) := by
 apply G9
 intro a
 exact ⟨oj a,II⟩
private theorem cMB (g:Fin 4→pz L) :
  (H8 g).map n5=Su (fun i=>n5 (g i)) := by
 simp only [H8,qy ,← Nj]
private theorem bXh (g:Fin 4→pz L) (p:pz L)
   (h:aNY g p=0) :
   ∃ d:ox L,d≠0∧C d*p∈H8 g:= by
 let:t7 (pz L) (Affine (sU L)) :=WW
 let S:=(ox L)⁰.map (C (σ:=Fin 4))
 have :C9 S (Affine (sU L)) :=
   Pc (ox L)⁰ (sU L)
 have hmem:c9 (pz L) (Affine (sU L)) p ∈
     (H8 g).map (c9 (pz L) (Affine (sU L))) :=
   Ideal.Quotient.eq_zero_iff_mem.mp h
 obtain ⟨_,⟨d,hd,rfl⟩,hp⟩ :=
   (Ar S _ (H8 g) p).mp hmem
 exact ⟨d,mem_nonZeroDivisors_iff_ne_zero.mp hd,hp⟩
private theorem exM [Fz L] (h1 :c1) (h2 :c2)
    (g:Fin 4→pz L) (hfinite :ov L (Rh (fun i=>n5 (g i))))
    (m:cy (pz L)) [m.IsMaximal] (hm:aAo g≤ m) :
    qU (qM m ⧸
      (H8 g).map (c9 (pz L) (qM m)))
      (oy ((H8 g).map (c9 (pz L) (qM m)))
        (c9 (pz L) (qM m) (C p9))) := by
  let R:=qM m
  let loc:=c9 (pz L) R
  let:t7 L R:=(loc.comp (c9 L (pz L))).toAlgebra
  let u (i:Fin 4) :=loc (g i)
  let t:=loc (C p9)
  have hJ: (H8 g).map loc=lI (uW u) := by
    simp only [H8,qy ,← Nj,u]
  have hI: (aAo g).map loc=lI (uW u) ⊔ lI {t} := by
    rw [aAo,Ideal.map_sup,hJ,qy ,G5]
  have hle : (aAo g).map loc≤pL R:= by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m R]
    exact S2 hm
  have hrs :=h1 L g hfinite m hm
  change ∃ rs :List R,rs.length=5∧(∀ r∈rs,r∈(aAo g).map loc) ∧
    pG R rs at hrs
  rw [hI] at hle hrs
  have hreg:=h2 L R u t hle hrs
  change qU (R ⧸ (H8 g).map loc)
    (oy ((H8 g).map loc) t)
  rw [hJ]
  exact hreg
private theorem fV0 [Fz L] (h1 :c1) (h2 :c2)
   (g:Fin 4→pz L) (hfinite :ov L (Rh (fun i=>n5 (g i))))
   (p:pz L) (hp:aNY g p=0) :
   n5 p∈Su (fun i=>n5 (g i)) := by
 let J:=H8 g
 let J₀:=Su (fun i=>n5 (g i))
 change n5 p∈J₀
 by_contra hnot
 let I:=J₀.colon {n5 p}
 have hone : (1 :Affine L)∉I:= by
   intro h
   exact hnot (by simpa only [OJ] using Submodule.mem_colon_singleton.mp h)
 obtain ⟨m₀,hm₀,hI⟩:=zsl I (mt (Ideal.eq_top_iff_one I).mp hone)
 let m:=m₀.comap n5
 have :m.IsMaximal:=Xg n5 ar6
 have hm:aAo g≤ m:= by
   apply t9
   · rw [show m=m₀.comap n5 from rfl,← Ts ,cMB]
     exact le_trans (fun a ha=>Submodule.mem_colon_singleton.mpr (J₀.mul_mem_right _ ha)) hI
   · apply (yJ m).mpr
     change n5 (C p9)∈m₀
     simp [n5]
 let R:=qM m
 let loc:=c9 (pz L) R
 let mk :pz L →+* (R ⧸ J.map loc) :=(oy _).comp loc
 let t:=mk (C p9)
 have hreg:qU (R ⧸ J.map loc) t :=
   exM h1 h2 g hfinite m hm
 obtain ⟨d,hd,hdp⟩:=bXh g p hp
 obtain ⟨q,hfactor,hq⟩:=d.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hd (0:L)
 rw [Polynomial.C_0,Kc] at hfactor hq
 have hq0:q.eval 0≠0:= by
   rwa [Polynomial.X_dvd_iff,Polynomial.coeff_zero_eq_eval_zero] at hq
 have hqu: (C q:pz L)∉m:= by
   change n5 (C q)∉m₀
   rw [show n5 (C q)=C (q.eval 0) by simp [n5]]
   exact m₀.notMem_of_isUnit ((Ne.isUnit hq0).map C)
 have hunit :Dz (mk (C q)) :=
   (C4 R (⟨C q,hqu⟩:m.primeCompl)).map (oy _)
 have hzero :mk (C d*p)=0 :=
   Ideal.Quotient.eq_zero_iff_mem.mpr (xW _ hdp)
 have hzero' : t^d.rootMultiplicity 0*(mk (C q)*mk p)=0:= by
   rw [hfactor] at hzero
   simpa only [nI,t8 ,xI,t] using hzero
 have hcancel:mk (C q)*mk p=0 :=
   (hreg.pow (d.rootMultiplicity 0)) (by simpa only [G1 ,mul_zero] using hzero')
 have hmk :mk p=0 :=
   hunit.mul_left_cancel (by simpa only [mul_zero] using hcancel)
 have hmem:loc p∈J.map loc:=Ideal.Quotient.eq_zero_iff_mem.mp hmk
 obtain ⟨s,hs,hsp⟩:=(Ar m.primeCompl R J p).mp hmem
 have hprod:=xW n5 hsp
 rw [show J.map n5=J₀ from cMB g,nI] at hprod
 exact hs (hI (Submodule.mem_colon_singleton.mpr hprod))
end Relations
theorem of_children (h1 :c1) (h2 :c2) :UH.c2 := by
 classical
 intro k _ P f hs hf hg
 let L:=fZ k P
 let:Nonempty (Σ i:Fin 4,oD (P i)) :=⟨⟨0,⟨0,by simp [oD]⟩⟩⟩
 have :Fz L:=Infinite.of_injective (c9 (xB k P) L)
   (zi (xB k P) L)
 let g:=ahx P f
 have hI:Su (fun i=>n5 (g i)) =
     (Su f).map (oY (c9 k L)) := by
   simp only [Su,qy ,← Nj,g,
     bZ0 P f hs]
   rfl
 have :=hf
 obtain ⟨hsfinite,hsrank⟩:=bGF (L:=L) (Su f)
 rw [← hI] at hsfinite hsrank
 obtain ⟨hgfinite,hgrank⟩:=bZZ P f hg
 have :ov (sU L) (aw3 g) :=hgfinite
 let s :=zh L (Su (fun i=>n5 (g i)))
 have hr :=de2 g s.toLinearMap zf (fun p hp =>
   Ideal.Quotient.eq_zero_iff_mem.mpr (fV0 h1 h2 g hsfinite p hp))
 rw [← hsrank,← hgrank]
 exact hr
end
end aKo
end
section
namespace cyn
noncomputable section
open aR UH aFS MvPolynomial
variable {k :Type} [lz k] {P:Fin 4→aU}
private theorem weight_apply (e :Slot P →₀ ℕ) (i:SlotIndex) :
   uJ (jT P) e i = ∑ a :Vu P i,e ⟨i,a⟩:= by
 classical
 rw [Finsupp.weight_eq_sum,TI,Fintype.sum_sigma]
 rw [LO i]
 · simp [jT,FQ]
 · intro j _ hj
   simp [jT,FQ,SW (Ne.symm hj)]
 · simp
private theorem b9r (J:cy (vJ k P)) (g:vJ k P) (N :ℕ)
    (hkill : ∀ a :Chart P,GW k P a^N*g∈J)
    (e :Slot P →₀ ℕ) (c:fZ k P)
    (he : ∀ i,KI (Vu P i)*N< uJ (jT P) e i) :
    oK e c*g∈J:= by
  classical
  have hpick (i:SlotIndex) : ∃ a :Vu P i,N≤e ⟨i,a⟩:= by
    by_contra! h
    have hsum: (∑ a :Vu P i,e ⟨i,a⟩)≤KI (Vu P i)*N := by
      calc
        _ ≤ ∑ _a :Vu P i,N :=zQk fun a _=>(h a).le
        _ = _:= by simp
    exact (not_le_of_gt (he i)) ((weight_apply e i).trans_le hsum)
  choose a ha using hpick
  let v :Slot P →₀ ℕ := ∑ i:SlotIndex,S1 ⟨i,a i⟩ N
  have hv :v≤e := by
    rintro ⟨i,b⟩
    rw [show v ⟨i,b⟩=S1 (⟨i,a i⟩:Slot P) N ⟨i,b⟩ by
      simp only [v,Finsupp.finsetSum_apply]
      apply LO i
      · intro j _ hj
        apply Finsupp.single_eq_of_ne
        intro h
        exact hj (oq Sigma.fst h).symm
      · simp]
    by_cases hab:a i=b
    · subst b
      simpa using ha i
    · simp [Ne.symm hab]
  have hchart:GW k P a^N=oK v (1 :fZ k P) := by
    unfold GW
    rw [← Finset.prod_pow]
    simp only [zp9,v,monomial_sum_one]
  have hfactor :oK e c*g=oK (e - v) c*(GW k P a^N*g) := by
    rw [hchart,← xI,Ok,zg ,add_comm (e - v),
      add_tsub_cancel_of_le hv]
  rw [hfactor]
  exact J.mul_mem_left _ (hkill a)
private theorem b53 (J:cy (vJ k P)) (g:vJ k P) (N :ℕ)
  (hkill : ∀ a :Chart P,GW k P a^N*g∈J)
  {f :vJ k P} {d:X0} (hf :f∈Kx k P d)
  (hd : ∀ i,KI (Vu P i)*N<d i) :f * g∈J:= by
 classical
 rw [f.as_sum,Finset.sum_mul]
 exact J.sum_mem fun e he=>b9r J g N hkill e _ (by
  have hdeg:=hf (mem_support_iff.mp he)
  intro i
  simpa only [hdeg] using hd i)
private theorem Zy {g:vJ k P} {e :X0}
   (hg:g∈Kx k P e) (f :vJ k P) (d:X0) :
   wR (jT P) (d+e) (f * g) =
     wR (jT P) d f * g:= by
 classical
 induction f using Zg with
 | monomial a c =>
   have ha :=LP (jT P) a c rfl
   have hg' : g.IsWeightedHomogeneous (jT P) e :=hg
   simp only [Hw (ha.mul hg'),
     Hw ha,ZJ]
   split <;> simp_all
 | add p r hp hr=>simp [add_mul,hp,hr]
theorem proof :aFS.c1 := by
  classical
  intro k _ P r hlocal
  obtain ⟨G,hG,hspan⟩:=(Submodule.fg_span_iff_fg_span_finset_subset
    (R:=vJ k P) (aEy k P r)).mp (IsNoetherian.noetherian _)
  have hspan' : Se k P r=lI (↑G:Set (vJ k P)) :=hspan
  choose D hD using fun g:G=>(hG g.property).1
  choose n hn using fun g:G=>hlocal g (hG g.property)
  let N (g:G) :=Finset.univ.sup (n g)
  have hN (g:G) (a :Chart P) :GW k P a^N g*(g:vJ k P)∈ke k P r := by
    have hle :n g a≤N g:=Ee (f :=n g) (wB a)
    have hpow:GW k P a^N g*(g:vJ k P) =
        GW k P a^(N g - n g a)*(GW k P a^n g a*(g:vJ k P)) := by
      rw [← xI,← pow_add,Vq hle]
    rw [hpow]
    exact (ke k P r).mul_mem_left _ (hn g a)
  let bound (g:G) (i:SlotIndex) :=D g i+Fintype.card (Vu P i)*N g+1
  let q:=Finset.univ.sup fun g:G=>Finset.univ.sup (bound g)
  refine ⟨q,?_⟩
  intro d hd f hf hrel
  rw [hspan'] at hrel
  obtain ⟨c,hc⟩:=Submodule.mem_span_finset'.mp hrel
  have hsum:=oq (wR (jT P) d) hc
  rw [t5 ,zfp (show f.IsWeightedHomogeneous _ d from hf)]
    at hsum
  rw [← hsum]
  refine (ke k P r).sum_mem fun g _ => ?_
  have hgd (i:SlotIndex) :bound g i≤d i :=
    (Ee (f :=bound g) (wB i)).trans
      ((Ee (f := fun x :G=>Finset.univ.sup (bound x)) (wB g)).trans (hd i))
  have hdiff (i:SlotIndex) :KI (Vu P i)*N g<(d - D g) i:= by
    have hh:=hgd i
    change D g i+Fintype.card (Vu P i)*N g+1≤d i at hh
    change _<d i - D g i
    omega
  have heq :d - D g+D g=d:= by
    funext i
    exact Vq (by
      have hh:=hgd i
      dsimp [bound] at hh
      omega)
  change wR (jT P) d (c g*(g:vJ k P))∈ke k P r
  rw [← heq,Zy (hD g)]
  exact b53 (ke k P r) g (N g) (hN g)
    (zbF _ _ _) hdiff
end
end cyn
end
section
namespace baq
noncomputable section
open aR UH aFS MvPolynomial
local instance euF (p:aU) :yU (oD p) :=
 (afS p).fintype
variable {k :Type} [lz k] {P:Fin 4→aU}
abbrev adl (k :Type) [lz k] (P:Fin 4→aU) :=
 lJ (aiy P) (aqn k P)
def coordinate (v :Slot P) :aqn k P :=
 oy (Nb P k) (mD v)
def avA (k :Type) [lz k] (P:Fin 4→aU) (b:Chart P) :aqn k P :=
 ∏ j:SlotIndex,coordinate ⟨j,b j⟩
theorem bsI (b:Chart P) :avA k P b≠0 :=
 Finset.prod_ne_zero_iff.mpr fun j _=>b9p ⟨j,b j⟩
def a5P (k :Type) [lz k] (P:Fin 4→aU) (i:Fin 4) :adl k P :=
 ∑ a :oD (P i),C (coordinate ⟨some i,a⟩)*mD ⟨i,a⟩
def Wd (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ) :cy (adl k P) :=
 lI (a5P k P '' {i:Fin 4 | i.val< r})
private theorem cqN {L:Type*} [lV L] (P:Fin 4→aU) (r :ℕ)
    (b: (j:Fin 4)→ oD (P j)) (z :aiy P→L) (w:Fin 4→L)
    (hw : ∀ j,w j*z ⟨j,b j⟩=1) :
    ∃ E :lJ (aiy P) L →ₐ[L] lJ (aiy P) L,
      nX E.toRingHom =
        lI ((fun j:Fin 4 => ∑ a :oD (P j),C (z ⟨j,a⟩)*mD ⟨j,a⟩) ''
          {j:Fin 4 | j.val< r}) := by
  classical
  let terms (j:Fin 4) (a :oD (P j)) :lJ (aiy P) L :=
    C (z ⟨j,a⟩)*mD ⟨j,a⟩
  let equation (j:Fin 4) := ∑ a,terms j a
  let rest (j:Fin 4) := ∑ a∈Finset.univ.erase (b j),terms j a
  let value (v :aiy P) :lJ (aiy P) L :=
    if v.1.val< r∧v.2=b v.1 then-(C (w v.1)*rest v.1) else mD v
  let E :lJ (aiy P) L →ₐ[L] lJ (aiy P) L:=vk value
  let J:=lI (equation '' {j:Fin 4 | j.val< r})
  have hsum (j:Fin 4) :equation j=rest j+terms j (b j) :=
    (Finset.sum_erase_add _ _ (wB (b j))).symm
  have hrest (j:Fin 4) :E (rest j)=rest j:= by
    simp only [rest,t5]
    apply vw rfl
    intro a ha
    have hne :=(Finset.mem_erase.mp ha).1
    simp [terms,E,value,hne]
  have hpivot (j:Fin 4) (hj:j.val< r) :
      E (mD ⟨j,b j⟩) = - (C (w j)*rest j) := by
    simp [E,value,hj]
  have hunit (j:Fin 4) :C (w j)*C (z ⟨j,b j⟩)=(1 :lJ (aiy P) L) := by
    rw [← nI,hw,map_one]
  refine ⟨E,show nX E.toRingHom=J from vj ?_ ?_⟩
  · let q:=zh L J
    have hq:q.comp E=q:= by
      apply zpJ
      rintro ⟨j,a⟩
      change q (E (mD ⟨j,a⟩))=q (mD ⟨j,a⟩)
      by_cases h:j.val< r∧a=b j
      · obtain ⟨hj,rfl⟩:=h
        rw [hpivot j hj,Ideal.Quotient.mkₐ_eq_mk,zdf]
        rw [show-(C (w j)*rest j)-MvPolynomial.X ⟨j,b j⟩ =
          -(C (w j)*rest j+MvPolynomial.X ⟨j,b j⟩) by abel]
        apply J.neg_mem
        have he :equation j∈J:=qJ ⟨j,hj,rfl⟩
        have hm:=J.mul_mem_left (C (w j)) he
        simpa only [hsum j,terms,mul_add,← xI,hunit j,ze] using hm
      · simp [E,value,h]
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p=0
    have hh:=zmU hq p
    change q (E p)=q p at hh
    change E p=0 at hp
    simpa only [hp,p5] using hh.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    change E (equation j)=0
    rw [hsum,uz ,hrest]
    simp only [terms,nI,hpivot j hj,mul_neg]
    rw [show E (C (z ⟨j,b j⟩))=C (z ⟨j,b j⟩) by simp [E]]
    rw [← xI,v9 (C (z ⟨j,b j⟩)),hunit,ze,add_neg_cancel]
theorem b9l (r :ℕ) (b:Chart P)
    {a :aqn k P} (ha :a≠0) (u:adl k P) (n:ℕ)
    (hu:C a^n*u∈Wd k P r) :
    ∃ m:ℕ,C (avA k P b)^m*u∈Wd k P r := by
  classical
  let x :=avA k P b
  let L:=zUF x
  have hx :x≠0:=bsI b
  let:IsDomain L:=Localization.Away.isDomain hx
  let g:=c9 (aqn k P) L
  let z (v :aiy P) :=g (coordinate ⟨some v.1,v.2⟩)
  have hux :Dz (∏ j:SlotIndex,g (coordinate ⟨j,b j⟩)) := by
    rw [← JQ]
    exact IsLocalization.Away.algebraMap_isUnit (S:=L) x
  have hz (j:Fin 4) :Dz (z ⟨j,b (some j)⟩) :=
    isUnit_of_dvd_unit
      (Finset.dvd_prod_of_mem (fun i:SlotIndex=>g (coordinate ⟨i,b i⟩))
        (wB (some j))) hux
  choose w hw using fun j=>isUnit_iff_exists_inv.mp (hz j)
  obtain ⟨E,hE⟩:=cqN P r (fun j=>b (some j)) z w
    (fun j=>(v9 _ _).trans (hw j))
  let:t7 (adl k P) (lJ (aiy P) L) :=
    WW
  let incl:=c9 (adl k P) (lJ (aiy P) L)
  let M:=(JW x).map (C (σ:=aiy P))
  have :C9 M (lJ (aiy P) L) :=
    Pc (JW x) L
  have hincl:incl=oY g:=rfl
  have hJ: (Wd k P r).map incl=nX E.toRingHom:= by
    rw [hE,Wd,qy ,z8]
    congr 1
    apply F9
    intro i _
    simp [hincl,a5P,z]
  have hmem:=xW incl hu
  rw [hJ] at hmem
  change E (incl (C a^n*u))=0 at hmem
  have hga :g a≠0:= by
    have hinj:sI g:=IsLocalization.injective (S:=L)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
    exact fun h=>ha (hinj (h.trans (p5 g).symm))
  have hEa :E (incl (C a))=C (g a) := by simp [hincl]
  have heu:E (incl u)=0:= by
    rw [nI,t8 ,nI,t8 ,hEa] at hmem
    exact (mul_eq_zero.mp hmem).resolve_left (Te _ (C_ne_zero.mpr hga))
  have hu' : incl u∈(Wd k P r).map incl:= by rw [hJ]; exact heu
  obtain ⟨_,⟨_,⟨m,rfl⟩,rfl⟩,hm⟩ :=
    (Ar M _ (Wd k P r) u).mp hu'
  exact ⟨m,by simpa only [t8] using hm⟩
end
end baq
end
section
namespace cyj
open CategoryTheory Abelian Ideal IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u
variable {R:Type u} [lV R] [zS R]
private theorem d4J {M:Type u} [Nr M] [Module R M]
    [ov R M] (a :R) (J:cy R)
    (h : ∀ p∈vl R M,¬ span {a} ⊔ J≤p) :
    ∃ b∈J,qU M (a+b) := by
  classical
  let S:=(Up R M).toFinset
  let T:=S.filter (fun p=>Maximal (· ∈ S) p)
  let G:=T.filter (fun p=>a∉p)
  let B:=T.filter (fun p=>a∈p)
  let K:=J ⊓ G.inf id
  have hS (p:cy R) :p∈S↔p∈vl R M :=
    Set.Finite.mem_toFinset _
  have hT {p:cy R} (hp:p∈T) :Maximal (· ∈ S) p :=
    (Finset.mem_filter.mp hp).2
  have hprime {p:cy R} (hp:p∈T) :p.IsPrime :=
    (hS p |>.mp (hT hp).1).isPrime
  have hK {p:cy R} (hp:p∈B) : ¬ K≤p:= by
    obtain ⟨hpT,hpa⟩:=Finset.mem_filter.mp hp
    intro hle
    rcases (hprime hpT).inf_le.mp hle with hJ | hG
    · exact h p ((hS p).mp (hT hpT).1)
        (t9 ((yJ p).mpr hpa) hJ)
    · obtain ⟨q,hqG,hqp⟩:=(hprime hpT).inf_le'.mp hG
      obtain ⟨hqT,hqa⟩:=Finset.mem_filter.mp hqG
      have hEq:p=q:=vj ((hT hqT).2 (hT hpT).1 hqp) hqp
      exact hqa (hEq ▸ hpa)
  have hb : ∃ b∈K,∀ p∈B,b∉p:= by
    by_contra! hh
    have hin: ((K:Set R) ⊆ ⋃ p∈(↑B:Set (cy R)),(p:Set R)) := by
      intro b hb
      obtain ⟨p,hp,hbp⟩:=hh b hb
      exact WX hp hbp
    obtain ⟨p,hp,hle⟩ :=
      (Ideal.subset_union_prime (f :=id) ⊤ ⊤
        (fun p hp _ _=>hprime (Finset.mem_filter.mp hp).1)).mp hin
    exact hK hp hle
  obtain ⟨b,hbK,hbB⟩:=hb
  refine ⟨b,(inf_le_left:K≤J) hbK,?_⟩
  have havoid :a+b ∉ ⋃ p∈vl R M,(p:Set R) := by
    intro ha
    obtain ⟨p,hp,hap⟩:=Set.mem_iUnion₂.mp ha
    obtain ⟨q,hpq,hq⟩:=S.exists_le_maximal ((hS p).mpr hp)
    have hqT:q∈T:=Finset.mem_filter.mpr ⟨hq.1,hq⟩
    have haq:=hpq hap
    by_cases ham:a∈q
    · exact hbB q (Finset.mem_filter.mpr ⟨hqT,ham⟩) (zYK a b ▸ q.sub_mem haq ham)
    · have hqG:q∈G:=Finset.mem_filter.mpr ⟨hqT,ham⟩
      have hbq:b∈q:=((inf_le_right:K≤G.inf id).trans (Finset.inf_le hqG)) hbK
      exact ham (Kv a b ▸ q.sub_mem haq hbq)
  rwa [Il,Set.mem_compl_iff,Mw ,not_not]
    at havoid
omit [zS R] in
private theorem aHM (N M:FR.{u} R) {a :R} (ha :qU M a)
  {n:ℕ} (h : ∀ i<n+1,wA (Ext N M i)) :
  ∀ i<n,wA (Ext N (yl R (Du a M)) i) := by
 intro i hi
 have h₀:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
 have h₁:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i+1) (by omega))
 exact zap <| zfe
  (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i+1) rfl)
  (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)
omit [zS R] in
private theorem fVE {M:Type u} [Nr M] [Module R M]
   (J:cy R) {a b:R} (hb:b∈J) :
   qU (M ⧸ (J • ⊤ : vH R M)) (a+b) →
     qU (M ⧸ (J • ⊤ : vH R M)) a := by
 let Q:=J•(⊤ : vH R M)
 have hzero (x :M ⧸ Q) :b•x=0:= by
   induction x using Submodule.Quotient.induction_on with
   | _ x =>
     change (IU (b•x) :M ⧸ Q)=0
     exact (ziM Q).mpr (Submodule.smul_mem_smul hb Xx)
 intro h x y hxy
 exact h (by simpa only [add_smul,hzero,Fa] using hxy)
variable [Au R]
private abbrev residue (R:Type u) [lV R] [Au R] :FR.{u} R :=
 yl R (R ⧸ pL R)
private theorem eKb (rs :List R) (M:FR.{u} R)
    [ov R M]
    (hmem : ∀ r∈rs,r∈pL R)
    (hrad:pL R≤(sS rs ⊔ p7 R M).radical)
    (hExt : ∀ i< rs.length,wA (Ext (residue R) M i)) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil=>exact IsWeaklyRegular.nil R M
  | cons a rs ih =>
    let J:=sS rs
    have ha :a∈pL R:=hmem a zYY
    have htail (r :R) (hr :r∈rs) :r∈pL R :=
      hmem r (Mk _ hr)
    have hHom:wA (residue R →ₗ[R] M) :=
      (Ext.addEquiv₀.trans Xp).subsingleton_congr.mp (hExt 0 (by simp))
    obtain ⟨r,hr,hrReg⟩:=IsSMulRegular.subsingleton_linearMap_iff.mp hHom
    have hrm:r∈pL R:= by
      change r∈p7 R (R ⧸ pL R) at hr
      rwa [Ml] at hr
    have hnot (p:cy R) (hp:p∈vl R M) : ¬ span {a} ⊔ J≤p:= by
      intro h
      have hle :sS (a :: rs) ⊔ p7 R M≤p :=
        t9 (G6 a rs ▸ h)
          (Ze (R:=R) (M:=M) ▸ hp.annihilator_le)
      have hpr :p.IsPrime :=hp.isPrime
      have hmr :=hrad.trans (hpr.radical_le_iff.mpr hle) hrm
      have hbad:r ∈ ⋃ q∈vl R M,(q:Set R) :=
        WX hp hmr
      rw [Il] at hbad
      exact hbad hrReg
    obtain ⟨b,hb,hab⟩:=d4J a J hnot
    have habm:a+b∈pL R:=(pL R).add_mem ha (span_le.mpr htail hb)
    let Q:=(a+b)•(⊤ : vH R M)
    let M' := yl R (M ⧸ Q)
    have hAnn:p7 R M≤p7 R M' :=
      Q.mkQ.annihilator_le_of_surjective Q.mkQ_surjective
    have habAnn:a+b∈p7 R M' := by
      rw [Module.mem_annihilator]
      intro y
      obtain ⟨x,rfl⟩:= Q.mkQ_surjective y
      rw [← map_smul]
      exact (ziM Q).mpr
        ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x,Xx ,rfl⟩)
    have hrad' : pL R≤(J ⊔ p7 R M').radical:= by
      apply hrad.trans (zks ?_)
      rw [G6]
      refine t9 (t9 ((yJ _).mpr ?_) z7)
        (hAnn.trans MK)
      have he :a=(a+b) - b:=(Kv a b).symm
      rw [he]
      exact (J ⊔ p7 R M').sub_mem
        ((MK:p7 R M' ≤ J ⊔ p7 R M') habAnn)
        ((z7:J≤J ⊔ p7 R M') hb)
    have hExt' : ∀ i< rs.length,wA (Ext (residue R) M' i) :=
      aHM (residue R) M hab (by simpa only [List.length_cons] using hExt)
    have hreg:pG M ((a+b) :: rs) :=
      Pk hab (ih M' htail hrad' hExt')
    have hreg' : pG M (rs ++ [a+b]) :=
      Mj hreg
        (zfI _ _).symm (by simpa using ⟨habm,htail⟩)
    rw [Aa ,xL] at hreg'
    have hreg'' : pG M (rs ++ [a]) :=
      (Aa M rs [a]).mpr
        ⟨hreg'.1,(xL _ _).mpr
          (fVE J hb hreg'.2)⟩
    apply Mj hreg''
      (zfI _ _)
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact htail z hz
    · obtain rfl :=List.mem_singleton.mp hz
      exact ha
theorem proof :aA4.c2 := by
 classical
 intro R _ _ _ f href hrad i x hx
 obtain ⟨s,hlen,hs,hreg⟩:=href
 let M:=yl R R
 have hSupp:Module.support R (residue R)⊆Xo (pL R) := by
   rw [zpq,Ml]
 have hlt:pL R•(⊤ : vH R M) < ⊤ := by
   change pL R•(⊤ : cy R) < ⊤
   rw [FV,FU]
   exact (Pv R).ne_top.lt_top
 have hExt : ∀ j<4,wA (Ext (residue R) M j) := by
   rw [← hlen]
   exact zw0 _ _ hSupp _ hlt s hs hreg
 let rs :List R:=zc (f ∘ i.succAbove)
 have hother :sS rs=aA4.aoC f i:= by
   unfold aA4.aoC
   change span {r | r∈rs} = _
   congr 1
   ext r
   change r∈rs↔_
   rw [RJ,NX ,zQu]
   rfl
 have hall:sS (rs ++ [f i])=span (uW f) := by
   change span {r | r∈rs ++ [f i]} = _
   congr 1
   ext r
   change r∈rs ++ [f i]↔r∈uW f
   rw [List.mem_append,List.mem_singleton,RJ,NX ,zQu]
   constructor
   · rintro (⟨j,_,rfl⟩ | rfl)
     · exact ⟨j,rfl⟩
     · exact ⟨i,rfl⟩
   · rintro ⟨j,rfl⟩
     by_cases h:j=i
     · exact Or.inr (oq f h)
     · exact Or.inl ⟨j,h,rfl⟩
 have hmem (r :R) (hr :r∈rs ++ [f i]) :r∈pL R:= by
   have hfull:r∈(sS (rs ++ [f i])).radical:=Ideal.le_radical (qJ hr)
   rwa [hall,hrad] at hfull
 have hparam:=eKb (rs ++ [f i]) M hmem
   (by rw [hall,← hrad]; exact zks z7)
   (by simpa only [rs,List.length_append,List.length_ofFn,List.length_singleton] using hExt)
 rw [Aa ,xL] at hparam
 have he : (sS rs•(⊤ : vH R R))=aA4.aoC f i:= by
   rw [FV,FU,hother]
 have hcancel :=
   ((RD _ _ he).isSMulRegular_congr (f i)).mp hparam.2
 exact mem_of_isSMulRegular_quotient_of_smul_mem hcancel hx
end cyj
end
section
namespace cyk
noncomputable section
open abG UH aKo
open MvPolynomial RingTheory.Sequence
open scoped Pointwise nonZeroDivisors
private def ajG {R σ:Type} [lV R] (i:σ) (p:ox R) :
  lJ σ R :=
 p.eval₂ C (mD i)
private theorem ey1 {R S σ:Type} [lV R] [lV S]
  (f :R →+* S) (i:σ) (p:ox R) :
  oY f (ajG i p)=ajG i (p.map f) := by
 rw [ajG,Et,map_X,ajG,KA,map_comp_C]
private theorem c7R {R S:Type} [lV R] [lV S]
   (f :R →+* S) (hf :vZ f) (x :R)
   (hk :nX f=lI {x}) (hx :qU R x)
   (rs :List R) (hrs :pG S (rs.map f)) :
   pG R (x :: rs) := by
 let e₀:Du x R ≃ₗ[R] R ⧸ lI {x} :=
   RD _ _ (by
     rw [← Rm,zde]
     exact Ideal.map_id _)
 let e₁:R ⧸ lI {x} ≃+* S :=
   (Ideal.quotEquivOfEq hk.symm).trans (f.quotientKerEquivOfSurjective hf)
 let e :=e₀.toAddEquiv.trans e₁.toAddEquiv
 have he (z :R) :e (IU z)=f z := by
   change f.quotientKerEquivOfSurjective hf (oy _ z)=f z
   exact RingHom.quotientKerEquivOfSurjective_apply_mk hf z
 apply Pk hx
 refine (e.isWeaklyRegular_congr (List.forall₂_map_right_iff.mpr
   (List.forall₂_same.mpr ?_))).mpr hrs
 intro y _ z
 obtain ⟨z,rfl⟩:=zUn _ z
 change e (y•IU z)=f y*e (IU z)
 rw [← Submodule.Quotient.mk_smul,he,he]
 exact nI f y z
private theorem fVJ {R S:Type} [lV R] [lV S]
  (e :R ≃+* S) (rs :List R) :
  pG R rs↔pG S (rs.map e) := by
 apply e.toAddEquiv.isWeaklyRegular_congr
 apply List.forall₂_map_right_iff.mpr
 exact List.forall₂_same.mpr fun y _ z=>nI e y z
private theorem c7P {R σ:Type} [lV R] (p:ox R)
  (hp:p.Monic) :qU (lJ σ (ox R))
    (C p:lJ σ (ox R)) := by
 intro f g hfg
 have h:C p*(f - g)=0:= by
  rw [mul_sub,Pf]
  exact hfg
 have hdiff :f - g=0:= by
  apply MvPolynomial.ext
  intro a
  change (f - g).coeff a=0
  apply mem_nonZeroDivisors_iff_left.mp hp.mem_nonZeroDivisors
  simpa only [coeff_C_mul,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using
    oq (fun v :lJ σ (ox R)=>v.coeff a) h
 exact sub_eq_zero.mp hdiff
private theorem fVK (n:ℕ) : ∀ (R:Type) [lV R]
    (p:Fin n→ ox R),(∀ i,(p i).Monic) →
    pG (lJ (Fin n) R) (zc fun i=>ajG i (p i)) := by
  induction n with
  | zero =>
    intro R _ p hp
    simp
  | succ n ih =>
    intro R _ p hp
    let e :lJ (Fin (n+1)) R ≃ₐ[R] lJ (Fin n) (ox R) :=
      (renameEquiv R (G3 n)).trans (optionEquivRight R (Fin n))
    have heC:e.toRingHom.comp C=(C:ox R →+* _).comp Polynomial.C:= by
      apply yL
      intro a
      change optionEquivRight R (Fin n) (rename (G3 n) (C a)) =
        C (oj a)
      rw [rename_C,optionEquivRight_C]
    have heX (i:Fin (n+1)) :
        e (mD i)=(G3 n i).elim (C p9) MvPolynomial.X:= by
      change optionEquivRight R (Fin n) (rename (G3 n) (mD i))= _
      rw [rename_X]
      cases G3 n i with
      | none=>exact optionEquivRight_X_none R (Fin n)
      | some j=>exact optionEquivRight_X_some R (Fin n) j
    have hevar (i:Fin (n+1)) :
        e (ajG i (p i)) =
          (p i).eval₂ ((C:ox R →+* _).comp oj) (e (mD i)) := by
      change e.toRingHom ((p i).eval₂ C (mD i))= _
      rw [Et,heC]
      rfl
    have hhead:e (ajG 0 (p 0))=C (p 0) := by
      rw [hevar,heX,finSuccEquiv_zero,Option.elim_none,← Et,
        Xu]
    let B:=ox R ⧸ lI {p 0}
    let q:ox R →+* B:=oy (lI {p 0})
    let f :lJ (Fin n) (ox R) →+* lJ (Fin n) B :=
      oY q
    let tail:=zc fun i:Fin n=>e (ajG i.succ (p i.succ))
    have ht:tail.map f=zc
        (fun i:Fin n=>ajG i ((p i.succ).map (q.comp oj))) := by
      rw [VC]
      congr 1
      funext i
      change f (e (ajG i.succ (p i.succ)))= _
      rw [hevar,heX,finSuccEquiv_succ]
      simp only [f,Option.elim_some,Et,map_X,ajG,
        KA,← RingHom.comp_assoc,map_comp_C]
    let x :lJ (Fin n) (ox R) :=C (p 0)
    have hkq:nX q=lI {p 0} := Eg
    have hk :nX f=lI {x} := by
      change nX (oY (σ:=Fin n) q)= _
      rw [RC,hkq,qy ,G5]
    have hf :vZ f :=
      G9 (σ:=Fin n) q zf
    have htail:pG (lJ (Fin n) B) (tail.map f) := by
      rw [ht]
      exact ih B _ fun i=>(hp i.succ).map _
    have hx :qU (lJ (Fin n) (ox R)) x :=
      c7P (σ:=Fin n) (p 0) (hp 0)
    have hreg:pG (lJ (Fin n) (ox R)) (x :: tail) :=
      @c7R (lJ (Fin n) (ox R)) (lJ (Fin n) B)
        Ea Ea f hf x hk hx tail htail
    apply (fVJ e.toRingEquiv _).mpr
    rw [List.ofFn_succ,List.map_cons,VC]
    change pG _ (e (ajG 0 (p 0)) :: tail)
    rw [hhead]
    exact hreg
private theorem a4S (L:Type) [lz L] :
  nX (n5 (L:=L))=lI {C p9} := by
 simp only [n5 ,RC,Polynomial.ker_evalRingHom,p5 ,Kc,
  qy ,G5]
private theorem ar6 (L:Type) [lz L] :
  vZ (n5 (L:=L)) :=
 G9 _ fun a=>⟨oj a,II⟩
private theorem dNQ {L:Type} [lz L] (g:Fin 4→pz L) :
  (Su (fun i=>n5 (g i))).comap n5=aAo g:= by
 have hmap : (H8 g).map n5=Su (fun i=>n5 (g i)) := by
  simp only [H8,qy ,← Nj]
 rw [← hmap,Iw _ (ar6 L),
  ← JM,a4S,aAo]
private theorem eaj {L:Type} [lz L] (g:Fin 4→pz L)
   [ov L (Rh (fun i=>n5 (g i)))] :
   ∃ p:Fin 4→ ox L,(∀ i,(p i).Monic) ∧
     (∀ i,ajG i (p i)∈Su (fun j=>n5 (g j))) := by
 let J:=Su (fun i=>n5 (g i))
 let q:=oy J
 have h (i:Fin 4) :Mz L (q (mD i)) :=
   IsIntegral.of_finite L (q (mD i))
 choose p hp hroot using h
 refine ⟨p,hp,fun i=>Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
 change q ((p i).eval₂ C (mD i))=0
 rw [Et]
 exact hroot i
theorem proof :aKo.c1 := by
  intro L _ g hfinite m _ _
  let:=hfinite
  obtain ⟨p,hp,hmem⟩:=eaj g
  let rs :List (pz L) :=zc fun i=>ajG i ((p i).map oj)
  let t:pz L:=C p9
  have hred (i:Fin 4) :
      n5 (ajG i ((p i).map oj) :pz L)=ajG i (p i) := by
    have hcomp: (zd 0).comp (oj (R:=L))=zk L:= by
      ext a
      exact II
    simp only [n5 ,ey1,Polynomial.map_map,hcomp,zeh]
  have hrs :rs.map n5=zc (fun i=>ajG i (p i)) := by
    simp only [rs,VC]
    exact oq zc (funext hred)
  have hregular :pG (pz L) (t :: rs) := by
    refine c7R n5 (ar6 L) t (a4S L)
      (c7P _ Polynomial.monic_X) rs ?_
    rw [hrs]
    exact fVK 4 L p hp
  have hspecial : ∀ r∈t :: rs,r∈aAo g:= by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (MK:lI {t} ≤ aAo g)
        (qJ (Set.mem_singleton t))
    · obtain ⟨i,hi⟩:=List.mem_ofFn.mp hr
      rw [← hi,← dNQ g,Ideal.mem_comap,hred]
      exact hmem i
  let R:=qM m
  let loc:=c9 (pz L) R
  refine ⟨(t :: rs).map loc,by simp [rs],?_,hregular.of_isLocalization R m.primeCompl⟩
  intro r hr
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr
  exact xW loc (hspecial a ha)
end
end cyk
end
section
namespace cyl
open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise
universe u v
section Local
variable {k :Type v} [lz k] [Fz k]
variable {R:Type u} [lV R] [zS R] [Au R] [t7 k R]
include k in
omit [Au R] in
private theorem buW {M:Type u} [Nr M] [Module R M] [ov R M]
    (a :R) (J:cy R)
    (h : ∀ P∈vl R M,a∈P → ¬ J≤P) :
    ∃ b∈J,qU M (a+b) := by
  classical
  let A := {P∈vl R M | a∈P}
  have hA:A.Finite :=(Up R M).subset fun _ hP=>hP.1
  have hav : ¬ ((J:Set R) ⊆ ⋃ P∈A,(P:Set R)) := by
    intro hall
    obtain ⟨P,hP,hJP⟩ :=
      (J.subset_union_prime_finite hA (f :=id) ⊥ ⊥
        (fun P hP _ _=>(show P7 P M from hP.1).isPrime)).mp hall
    exact h P hP.1 hP.2 hJP
  obtain ⟨b,hb,hbA⟩:=Set.not_subset.mp hav
  have hb' (P:cy R) (hP:P∈vl R M) (haP:a∈P) :
      b∉P:= fun hbP=>hbA (Set.mem_iUnion₂.mpr ⟨P,⟨hP,haP⟩,hbP⟩)
  let bad (P:cy R) := {t:k | a+algebraMap k R t*b∈P}
  have hbad (P:cy R) (hP:P∈vl R M) : (bad P).Finite := by
    apply Set.Subsingleton.finite
    intro s hs t ht
    by_contra hst
    have hp:P.IsPrime :=(show P7 P M from hP).isPrime
    have hd:c9 k R (s - t)*b∈P:= by
      rw [xm,sub_mul]
      simpa only [add_sub_add_left_eq_sub] using P.sub_mem hs ht
    have hbP:b∈P:=(hp.mem_or_mem hd).resolve_left fun hz =>
      hp.ne_top (P.eq_top_of_isUnit_mem hz ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hst)).map
        (c9 k R)))
    have haP:a∈P:= by
      simpa only [Kv] using P.sub_mem hs (P.mul_mem_left (c9 k R s) hbP)
    exact hb' P hP haP hbP
  have hfinite :=(Up R M).biUnion hbad
  obtain ⟨t,ht⟩:=hfinite.exists_notMem
  refine ⟨c9 k R t*b,J.mul_mem_left _ hb,?_⟩
  by_contra hreg
  have hh:a+algebraMap k R t*b ∈ ⋃ P∈vl R M,(P:Set R) := by
    rwa [Il R M]
  obtain ⟨P,hP,hhP⟩:=Set.mem_iUnion₂.mp hh
  exact ht (Set.mem_iUnion₂.mpr ⟨P,hP,hhP⟩)
private abbrev bAO (I:cy R) :=yl R (R ⧸ I)
omit [zS R] [Au R] in
private theorem aHM (N M:FR.{u} R) {a :R}
  (ha :qU M a) {n:ℕ} (h : ∀ i<n+1,wA (Ext N M i)) :
  ∀ i<n,wA (Ext N (yl R (Du a M)) i) := by
 intro i hi
 have h₀:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
 have h₁:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i+1) (by omega))
 exact zap <| zfe
  (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i+1) rfl)
  (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)
include k in
private theorem byD (I:cy R) (rs :List R) (M:FR.{u} R) [ov R M]
    (hm : ∀ a∈rs,a∈pL R)
    (hI:I≤ sS rs ⊔ p7 R M)
    (hext : ∀ i< rs.length,wA (Ext (bAO I) M i)) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil=>exact IsWeaklyRegular.nil R M
  | cons a rs ih =>
    have hHom:wA (bAO I →ₗ[R] M) :=
      (Ext.addEquiv₀.trans Xp).subsingleton_congr.mp
        (hext 0 (by simp))
    obtain ⟨r,hr,hreg⟩:=IsSMulRegular.subsingleton_linearMap_iff.mp hHom
    have hAnn:p7 R (bAO I)=I:=Ml
    have hrI:r∈I:=hAnn ▸ hr
    let J:=sS rs
    have hJm:J≤ pL R:=Ideal.span_le.mpr
      (fun z hz=>hm z (Mk _ hz))
    obtain ⟨b,hb,hab⟩:=buW (k :=k) (M:=M) a J (by
      intro P hP haP hJP
      have hassoc:P7 P M:=hP
      have hle :sS (a :: rs) ⊔ p7 R M≤P:= by
        rw [G6]
        exact t9 (t9 ((yJ P).mpr haP) hJP)
          (by simpa only [Ze] using hassoc.annihilator_le)
      have hrP:=hle (hI hrI)
      have hru:r ∈ ⋃ P∈vl R M,(P:Set R) :=
        Set.mem_iUnion₂.mpr ⟨P,hP,hrP⟩
      rw [Il R M] at hru
      exact hru hreg)
    let M' := yl R (Du (a+b) M)
    have habann:a+b∈p7 R M' := QuotSMulTop.mem_annihilator M (a+b)
    have hann:p7 R M≤p7 R M' :=
      (Submodule.mkQ _).annihilator_le_of_surjective (zUn _)
    have hle :sS (a :: rs) ⊔ p7 R M ≤
        J ⊔ p7 R M' := by
      rw [G6]
      refine t9 (t9 ((yJ _).mpr ?_) z7)
        (hann.trans MK)
      have hsum:a+b∈J ⊔ p7 R M' := UP habann
      have hb' : b∈J ⊔ p7 R M' := Ideal.mem_sup_left hb
      simpa only [Kv] using (J ⊔ p7 R M').sub_mem hsum hb'
    have htail:=ih M' (fun z hz=>hm z (Mk _ hz))
      (hI.trans hle) (aHM _ M hab hext)
    have hcons :pG M ((a+b) :: rs) :=Pk hab htail
    have happ:pG M (rs ++ [a+b]) :=
      Mj hcons
        (show List.Perm ([a+b] ++ rs) (rs ++ [a+b]) from ztu) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Ideal.add_mem _ (hm a zYY) (hJm hb)
        · exact hm z (Mk _ hz))
    obtain ⟨hrs,hlast⟩:=(Aa M rs [a+b]).mp happ
    let T:vH R M:=J • ⊤
    have hlast' : qU (M ⧸ T) (a+b) :=(xL _ _).mp hlast
    have ha :qU (M ⧸ T) a := by
      rw [Yi] at hlast' ⊢
      intro x hx
      apply hlast'
      have hbT:b•x∈T:= by
        apply (Submodule.smul_mono_left ((yJ J).mpr hb) :
          lI {b} • (⊤ : vH R M)≤T)
        rw [Rm]
        exact Submodule.smul_mem_pointwise_smul x b ⊤ trivial
      rw [add_smul]
      exact T.add_mem hx hbT
    have hnew :pG M (rs ++ [a]) :=
      (Aa M rs [a]).mpr
        ⟨hrs,(xL _ _).mpr ha⟩
    have hp:List.Perm (a :: rs) (rs ++ [a]) :=
      show List.Perm ([a] ++ rs) (rs ++ [a]) from ztu
    exact Mj hnew hp.symm
      (fun z hz=>hm z (hp.mem_iff.mpr hz))
include k in
private theorem gL0 (ref rs :List R) (hlen:ref.length=rs.length)
  (hI:sS rs≤ pL R)
  (hmem : ∀ a∈ref,a∈sS rs) (href :pG R ref) :
  IsWeaklyRegular R rs := by
 let I:=sS rs
 let N :=bAO I
 have hAnn:p7 R N=I:=Ml
 have hSupp:Module.support R N⊆Xo I:= by
  rw [zpq,hAnn]
 have hlt:I•(⊤ : vH R R) < ⊤ := by
  change I•(⊤ : cy R) < ⊤
  rw [FV,FU]
  exact lt_of_le_of_lt hI (Pv R).ne_top.lt_top
 have hreg:IsRegular R ref :=
  IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R (fun a ha=>hI (hmem a ha)) href
 have hext:=zw0 I N hSupp
  (yl R R) hlt ref hmem hreg
 exact byD (k :=k) I rs (yl R R)
  (fun a ha=>hI (qJ ha)) z7 (fun i hi=>hext i (hlen ▸ hi))
end Local
theorem proof :aKo.c2 := by
 intro L R _ _ _ _ _ _ u t
 dsimp only
 intro hI ⟨ref,hlen,hmem,href⟩
 let front:=zc u
 have hfront:sS front=lI (uW u) :=
   oq lI (Set.ext (RJ u))
 have hfull:sS (front ++ [t]) =
     lI (uW u) ⊔ lI {t} := by
   rw [Ideal.ofList_append,Ideal.ofList_singleton,hfront]
 have hparams :=gL0 (k :=L) ref (front ++ [t])
   (by simpa [front] using hlen) (hfull.symm ▸ hI) (hfull.symm ▸ hmem) href
 have hlast :=((Aa R front [t]).mp hparams).2
 have hc:=(xL _ _).mp hlast
 rw [FV,FU,hfront] at hc
 exact hc
end cyl
end
section
namespace cyi
open Ideal IsLocalRing RingTheory.Sequence
open scoped Pointwise
private theorem eDS {R:Type*} [lV R]
  (I:cy R) {f :ox R} (hf :f.Monic) :
  qU (ox R ⧸ I.map oj) f := by
 let φ:=pU (oy I)
 have hker :nX φ=I.map Polynomial.C:= by
  change nX (pU (oy I))= _
  rw [SM,Eg]
 have hregular :_root_.IsRegular (φ f) :=(hf.map (oy I)).isRegular
 refine (Yi _ _).mpr ?_
 intro g hg
 change f * g∈I.map oj at hg
 rw [← hker,Cy] at hg ⊢
 rw [nI] at hg
 exact hregular.left (hg.trans (mul_zero _).symm)
private theorem dtj {R:Type*} [lV R]
   {s :List R} (hs :pG R s) {f :ox R} (hf :f.Monic) :
   pG (ox R) (s.map oj ++ [f]) := by
 apply (Aa _ _ _).mpr
 refine ⟨?_,(xL _ _).mpr ?_⟩
 · simpa only [Polynomial.algebraMap_eq] using hs.of_flat (S:=ox R)
 · rw [FV,FU,← Ideal.map_ofList]
   exact eDS (sS s) hf
private theorem ezo {R S:Type*} [lV R] [lV S]
  (e :R ≃+* S) {s :List R} (hs :pG R s) :
  pG S (s.map e) := by
 have hc:List.Forall₂ (fun (r :R) (z :S) => ∀ x :R,e (r•x)=z•e x)
    s (s.map e) :=
  List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x=>e.map_mul r x)
 exact (e.toAddEquiv.isWeaklyRegular_congr hc).mp hs
private theorem d42 (k :Type) [lz k] (n:ℕ)
    (p:cy (lJ (Fin n) k)) [p.IsMaximal] :
    ∃ s :List (lJ (Fin n) k),s.length=n ∧
      (∀ x∈s,x∈p)∧pG (lJ (Fin n) k) s := by
  induction n with
  | zero=>exact ⟨[],rfl,by simp,IsWeaklyRegular.nil _ _⟩
  | succ n ih =>
    let R:=lJ (Fin n) k
    let e :lJ (Fin (n+1)) k ≃+* ox R :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let P:=p.map e.toRingHom
    have :P.IsMaximal:=Ideal.map_isMaximal_of_equiv e
    let C:R →+* ox R:=oj
    let q:=P.comap C
    have :q.IsMaximal:=Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    obtain ⟨s,hlen,hmem,hreg⟩:=ih q
    obtain ⟨f,hf,hroot⟩:=Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing P
      (oy P p9)
    have hfP:f∈P:= by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← Xu (p:=f),Et]
      exact hroot
    let t:=s.map C ++ [f]
    have htreg:pG (ox R) t:=dtj hreg hf
    have htmem (y :ox R) (hy :y∈t) :y∈P:= by
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hy
        exact hmem x hx
      · rwa [List.mem_singleton.mp hy]
    have he :P.comap e.toRingHom=p:=Ideal.comap_map_of_bijective _ e.bijective
    refine ⟨t.map e.symm,by simp [t,hlen],?_,ezo e.symm htreg⟩
    intro z hz
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hz
    rw [← he,Ideal.mem_comap]
    change e (e.symm y)∈P
    simpa only [e.apply_symm_apply] using htmem y hy
theorem proof :aA4.c1 := by
 intro k _ p _
 let S:=qM p
 obtain ⟨s,hlen,hmem,hreg⟩:=d42 k 4 p
 refine ⟨s.map (algebraMap _ S),by simpa only [List.length_map] using hlen,?_,
  hreg.isRegular_of_isLocalization_of_mem S p hmem⟩
 intro z hz
 obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hz
 exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p x).mpr (hmem x hx)
end cyi
end
section
namespace baq
noncomputable section
open aR UH aFS MvPolynomial
open scoped nonZeroDivisors
local instance gQa (p:aU) :yU (oD p) :=
 (afS p).fintype
private abbrev as0 (k :Type) [lz k] (P:Fin 4→aU) :=lJ (Slot P) (xB k P)
private def Nk (k :Type) [lz k] (P:Fin 4→aU) (i:Fin 4) :as0 k P :=
 ∑ a :oD (P i),C (mD ⟨i,a⟩)*mD ⟨some i,a⟩
private def Xk (k :Type) [lz k] (P:Fin 4→aU) (b:Chart P) :as0 k P :=
 ∏ j:SlotIndex,mD ⟨j,b j⟩
private def DX (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ) :cy (as0 k P) :=
 lI (Nk k P '' {i:Fin 4 | i.val< r})
private def O6 (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ) :cy (as0 k P) :=
 Nb P (xB k P) ⊔ DX k P r
private abbrev swap (k :Type) [lz k] (P:Fin 4→aU) :=commAlgEquiv k (Slot P) (aiy P)
private def toModel (k :Type) [lz k] (P:Fin 4→aU) :as0 k P →+* adl k P :=
 (oY (oy (Nb P k))).comp (swap k P).toRingHom
private theorem ctG (k :Type) [lz k] (P:Fin 4→aU) :vZ (toModel k P) :=
 (G9 _ zf).comp (swap k P).surjective
private theorem ctF (k :Type) [lz k] (P:Fin 4→aU) :
   nX (toModel k P)=Nb P (xB k P) := by
 have hswap: (swap k P).toRingHom.comp (oY (C (σ:=aiy P)))=C:= by
   apply th
   · intro c
     simp [swap]
   · intro v
     simp [swap]
 have hker :nX (swap k P).toRingHom = ⊥ :=
   (RingHom.injective_iff_ker_eq_bot (swap k P).toRingHom).mp (swap k P).injective
 rw [toModel,← zR,RC,Eg ,← hswap,
   ← Nq,Iw (swap k P).toRingHom (swap k P).surjective,
   ← JM,hker,
   sup_bot_eq,bsj]
private theorem bxM (k :Type) [lz k] (P:Fin 4→aU) (b:Chart P) :
  toModel k P (Xk k P b)=C (avA k P b) := by
 simp [ Xk,toModel,avA,coordinate]
private theorem bq8 (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ) :
  O6 k P r=(Wd k P r).comap (toModel k P) := by
 have hmap : (DX k P r).map (toModel k P)=Wd k P r := by
  rw [DX,Wd,qy ,z8]
  congr 1
  apply F9
  intro i _
  simp [Nk,a5P,toModel,coordinate]
  exact vw rfl (fun _ _=>v9 _ _)
 rw [← hmap,Iw _ (ctG k P),
  ← JM,ctF,O6,sup_comm]
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev ayQ (k :Type) [lz k] (P:Fin 4→aU) :=c9 (as0 k P) (vJ k P)
private theorem bpU (k :Type) [lz k] (P:Fin 4→aU) (b:Chart P) :
  ayQ k P (Xk k P b)=GW k P b:= by
 change oY (c9 (xB k P) (fZ k P))
  (Xk k P b)=GW k P b
 simp only [ Xk,GW,JQ,map_X]
private theorem bFK (k :Type) [lz k] (P:Fin 4→aU) (r :ℕ) :
  (O6 k P r).map (ayQ k P)=ke k P r := by
 change (O6 k P r).map
  (oY (c9 (xB k P) (fZ k P)))=ke k P r
 rw [O6,Ideal.map_sup,bsj,
  ← ce5,ke,DX,qy ,z8]
 congr 2
 apply F9
 intro i _
 simp only [Nk,T2,t5 ,nI,TZ,map_X]
set_option maxHeartbeats 800000 in
theorem proof :aFS.c2 := by
 classical
 intro k _ P r b f n hf
 let b₀:=bP9 P
 let I:=O6 k P r
 let e :=ayQ k P
 let M:=(xB k P)⁰.map (C (σ:=Slot P))
 have :C9 M (vJ k P) :=
  Pc (xB k P)⁰ (fZ k P)
 obtain ⟨⟨p,s⟩,hs⟩:=zg4 M f
 change f*e s=e p at hs
 have hc:e (Xk k P b₀)=ab5 k P:=bpU k P b₀
 have hI:I.map e=ke k P r :=bFK k P r
 have hp:e (Xk k P b₀^n*p)∈I.map e := by
  rw [hI,nI,t8 ,hc,← hs,← xI]
  exact (ke k P r).mul_mem_right _ hf
 obtain ⟨d,hd,hpre⟩:=(Ar M _ I _).mp hp
 have hpre' : Xk k P b₀^n*(d*p)∈I:= by
  rwa [Gr (Xk k P b₀^n) d p]
 have hmod:C (avA k P b₀)^n*toModel k P (d*p)∈Wd k P r := by
  rw [show I=(Wd k P r).comap (toModel k P) from bq8 k P r] at hpre'
  change toModel k P (Xk k P b₀^n*(d*p))∈Wd k P r at hpre'
  simpa only [nI,t8 ,bxM] using hpre'
 obtain ⟨m,hm⟩:=b9l r b (bsI b₀) (toModel k P (d*p)) n hmod
 have hm' : Xk k P b^m*(d*p)∈I:= by
  change _∈O6 k P r
  rw [bq8]
  change toModel k P (Xk k P b^m*(d*p))∈Wd k P r
  simpa only [nI,t8 ,bxM] using hm
 have hresult :=xW e hm'
 rw [hI,nI,t8 ,bpU,nI,← hs] at hresult
 have hds :Dz (e d) :=C4 (vJ k P) ⟨d,hd⟩
 have hss :Dz (e s) :=C4 (vJ k P) s
 refine ⟨m,(Ideal.unit_mul_mem_iff_mem _ (hds.mul hss)).mp ?_⟩
 rw [xI (e d) (e s),Gr (e s) (GW k P b^m),
  Gr (e d) (GW k P b^m),v9 (e s) f]
 exact hresult
end
end baq
end
section
namespace aY2
open aR dN GJ ap7
open scoped BigOperators
theorem proof :ap7.c2 := by
  intro J a h _ _ hfinite uG v hsurfaces
  let F:=VM a h
  let S:=ajd a h
  have hflat :LQ nq S:=gG5 a h
  have hmin (P:cy nq) (hP:P∈uG) :J.IsMinimalPrime P:= by
    obtain ⟨hm,_⟩:=hsurfaces P hP
    exact hm
  have hsum:=gMk S F J uG hmin
  have hlength (P:cy nq) (hP:J≤P) :
      Module.length F (S ⧸ P.map (c9 nq S)) =
        (Ux P a h:ℕ∞) := by
    let IJ:=J.map (EG a h) ⊔ i9 a h
    let IP:=P.map (EG a h) ⊔ i9 a h
    have hIP:IJ≤IP:=sup_le_sup (S2 hP) xu
    let f :axZ J a h →ₐ[F] axZ P a h :=
      ⟨Ideal.Quotient.factor hIP,fun _=>rfl⟩
    have hfinP:ov F (axZ P a h) :=
      Yo f.toLinearMap (Ideal.Quotient.factor_surjective hIP)
    rw [(grS P a h).toLinearEquiv.length_eq,Module.length_eq_finrank]
    rfl
  have hw (P:cy nq) (hP:P∈uG) :AN J P=(v P:ℕ∞) := by
    obtain ⟨hm,hv⟩:=hsurfaces P hP
    let hp:=hm.isPrime
    rw [a5y]
    exact hv
  apply ENat.natCast_le_natCast.mp
  push_cast
  calc
    _ = ∑ P∈uG,AN J P*Module.length F (S ⧸ P.map (c9 nq S)) := by
      apply vw rfl
      intro P hP
      rw [hw P hP,hlength P (hmin P hP).le]
    _≤_:= by
      change _≤(Ux J a h:ℕ∞)
      rw [← hlength J xu]
      exact hsum
end aY2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace ac1
noncomputable section
open aR oR B7
open scoped Polynomial
def Jy (f :af 3) :cy nW:=lI {GZ f}
abbrev ChartRing (f :af 3) :=nW ⧸ Jy f
abbrev WE (f :af 3) :=Df (ChartRing f)
private def cS2 {k σ:Type*} [lz k]
   (I:cy (lJ σ k)) [I.IsPrime] :
   lJ σ k →+* Df (lJ σ k ⧸ I) :=
 (c9 (lJ σ k ⧸ I) (Df (lJ σ k ⧸ I))).comp
   (oy I)
def y3 (f :af 3) [(Jy f).IsPrime] :nW →+* WE f :=
 cS2 (Jy f)
private theorem edQ {k σ:Type*} [lz k]
   (I:cy (lJ σ k)) [I.IsPrime] (v :lJ σ k) :
   cS2 I v=0↔v∈I:= by
 change (c9 (lJ σ k ⧸ I) (Df (lJ σ k ⧸ I)))
   (oy I v)=0↔_
 constructor
 · intro h
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   exact zi (lJ σ k ⧸ I)
     (Df (lJ σ k ⧸ I)) (h.trans (p5 _).symm)
 · intro h
   rw [Ideal.Quotient.eq_zero_iff_mem.mpr h,p5]
theorem aO5 (f :af 3) [(Jy f).IsPrime] (v :nW) :
  y3 f v=0↔v∈Jy f :=
 edQ (Jy f) v
def QM:ao →+* dF :=
 (c9 ao[X] dF).comp oj
def Jb (f :af 3) [(Jy f).IsPrime] :ao →+* WE f :=
 ((y3 f).comp qz).comp QM
def CW (f :af 3) [(Jy f).IsPrime] :WE f :=
 y3 f (qz PV)
def a2l (f :af 3) [(Jy f).IsPrime] (i:Fin 3) :WE f :=
 y3 f (mD i)
def jW {F:Type*} [lV F] (k :ao →+* F) (U:F[X]) :
    af 3 →+* F[X] :=
  pC (pU k) (fun i=>t3 i.val U)
def rD {F:Type*} [lV F] (x :F) (U:F[X]) (i:Fin 3) :F :=
 (t3 i.val U).eval x
def ee {F:Type*} [lV F] (k :ao →+* F) (x :F) (y :Fin 3→F) :
    af 3 →+* F :=
  pC ((zd x).comp (pU k)) y
end
end ac1
end
section
set_option backward.isDefEq.respectTransparency false
namespace ac1
noncomputable section
open aR oR B7
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev Bu:af 3 →+* nW :=
 oY (c9 ao[X] dF)
abbrev bLC:Submonoid (af 3) :=
 (ao[X]⁰).map qz
def bf2 (f :af 3) :cy (af 3) :=lI {f}
theorem bWU (f :af 3) :
  (bf2 f).map Bu=Jy f := by
 simp [bf2,Jy,qy ,GZ,Bu]
theorem fZd:sI Bu :=
 MvPolynomial.map_injective (c9 ao[X] dF)
  (zi ao[X] dF)
private theorem c2X (f :af 3) (hf :0<f.degreeOf 2) :
   Disjoint (bLC:Set (af 3)) (bf2 f :Set (af 3)) := by
 refine Set.disjoint_left.mpr ?_
 rintro _ ⟨a,ha,rfl⟩ hmem
 obtain ⟨g,hg⟩:=Ideal.mem_span_singleton.mp hmem
 have ha' : a≠0:=mem_nonZeroDivisors_iff_ne_zero.mp ha
 have hC: (qz a :af 3)≠0 :=
   fun h=>ha' (MvPolynomial.C_injective (Fin 3) ao[X]
     (h.trans (p5 qz).symm))
 have hn:f≠0:= by
   intro he
   simp [he] at hf
 have hgn:g≠0:= by
   intro he
   exact hC (by simpa [he] using hg)
 have hd:=oq (MvPolynomial.degreeOf (2 :Fin 3)) hg
 rw [MvPolynomial.degreeOf_C,MvPolynomial.degreeOf_mul_eq hn hgn] at hd
 omega
theorem c2Y (f :af 3) (hf :zm f) :
  (bf2 f).IsPrime :=
 Ideal.isPrime_span_singleton_of_prime hf.prime
theorem dIP (f :af 3) (hf :zm f) (hd:0<f.degreeOf 2) :
  (Jy f).IsPrime := by
 rw [← bWU]
 exact IsLocalization.isPrime_of_isPrime_disjoint bLC nW
  _ (c2Y f hf) (c2X f hd)
theorem cFe (f :af 3) (hf :zm f) (hd:0<f.degreeOf 2) :
  (Jy f).comap Bu=bf2 f := by
 rw [← bWU]
 exact IsLocalization.under_map_of_isPrime_disjoint bLC nW
  (c2Y f hf) (c2X f hd)
theorem bvd (f :af 3) [(Jy f).IsPrime] :
    ee (Jb f) (CW f) (a2l f)=(y3 f).comp Bu:= by
  apply th
  · have h: (zd (CW f)).comp
        (pU (Jb f)) =
          ((y3 f).comp qz).comp (c9 ao[X] dF) := by
      apply v8
      · intro a
        simp [Jb,QM]
      · simp [CW,PV]
    intro a
    simpa [ee,Bu] using qm h a
  · intro i
    simp [ee,Bu,a2l]
theorem bdt {F:Type*} [lV F] (k :ao →+* F) (U:F[X])
  (x :F) (b:af 3) :
  (jW k U b).eval x=ee k x (rD x U) b:= by
 simp only [jW,ee,MvPolynomial.coe_eval₂Hom,MvPolynomial.polynomial_eval_eval₂]
 rfl
theorem aVM {F L:Type*} [lV F] [lV L]
  (k :ao →+* F) (a :F →+* L) (U:F[X]) (b:af 3) :
  (jW k U b).map a=jW (a.comp k) (U.map a) b:= by
 have h: (pU a).comp (jW k U) =
    jW (a.comp k) (U.map a) := by
  apply th
  · intro c
    simp [jW]
  · intro i
    simp [jW,Polynomial.hasseDeriv_map]
 exact qm h b
end
end ac1
end
section
set_option backward.isDefEq.respectTransparency false
namespace ac1
noncomputable section
open aR B7
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
section PolynomialCoefficients
variable {k F σ:Type*} [lV k] [lV F]
private def toPolynomial:lJ σ k[X] →+* (lJ σ k)[X] :=
 pC (pU qz) (oj ∘ mD)
private def a4q: (lJ σ k)[X] →+* lJ σ k[X] :=
 Bf (oY oj) (qz p9)
private theorem eeq (p:lJ σ k[X]) :
    a4q (toPolynomial p)=p:= by
  have h: (a4q (k :=k) (σ:=σ)).comp toPolynomial=zk _:= by
    apply th
    · have hc: (a4q (k :=k) (σ:=σ)).comp
          (pU qz)=MvPolynomial.C:= by
        apply v8 <;> simp [a4q]
      intro c
      simpa [toPolynomial] using qm hc c
    · intro i
      simp [toPolynomial,a4q]
  exact qm h p
private theorem etK (kF:k →+* F) (point :σ→F) :
    nX (pC (pU kF) (oj ∘ point)) =
      (nX (pC kF point)).map (oY oj) := by
  let e :=pC kF point
  let e' := pC (pU kF) (oj ∘ point)
  have h: (pU e).comp toPolynomial=e' := by
    apply th
    · intro c
      simp [toPolynomial,e',e]
    · intro i
      simp [toPolynomial,e',e]
  have hc:e'.comp (oY oj)=Polynomial.C.comp e := by
    apply th <;> simp [e',e]
  change nX e' = (nX e).map _
  apply vj
  · intro p hp
    have hp' : toPolynomial p∈(nX e).map Polynomial.C:= by
      rw [← SM]
      exact (qm h p).trans hp
    have hm:=xW a4q hp'
    have hfrom: (a4q (k :=k) (σ:=σ)).comp oj =
        oY Polynomial.C:=Polynomial.eval₂RingHom_comp_C _ _
    rwa [Nq,hfrom,eeq] at hm
  · rw [Ts ,zR,hc]
    intro p hp
    change oj (e p)=0
    rw [show e p=0 from hp,p5]
end PolynomialCoefficients
section dF
variable {F:Type*} [lz F]
abbrev aar (F:Type*) [lz F] :=Df F[X]
def newConstants :F →+* aar F :=
 (c9 F[X] (aar F)).comp oj
def amg:aar F:=c9 F[X] (aar F) p9
def aOV (k :ao →+* F) :dF →+* aar F :=
  IsFractionRing.lift (g:=(c9 F[X] (aar F)).comp (pU k))
    ((zi F[X] (aar F)).comp (zTo k k.injective))
@[simp] theorem gRl (k :ao →+* F) (b:ao[X]) :
    aOV k (c9 ao[X] dF b) =
      c9 F[X] (aar F) (b.map k) := by
  simp [aOV]
@[simp] theorem gRk (k :ao →+* F) (a :ao) :
   aOV k (QM a)=newConstants (k a) := by
  simp [QM,newConstants]
@[simp] theorem eED (k :ao →+* F) :
   aOV k PV=(amg:aar F) := by
  simp [PV,amg]
def ajk (k :ao →+* F) (point :rS→F) :jo →+* F :=
 pC k point
def aHX (k :ao →+* F) (point :rS→F) :
    mK →+* aar F :=
  pC (aOV k) (newConstants ∘ point)
theorem cS8 (k :ao →+* F) (point :rS→F) :
   oV (nX (ajk k point))=nX (aHX k point) := by
 let M:=(ao[X]⁰).map (qz (σ:=rS))
 let e :=pC (pU k) (oj ∘ point)
 let j:lJ rS ao[X] →+* mK :=
   oY (c9 ao[X] dF)
 let inj:=c9 F[X] (aar F)
 let g:=aHX k point
 have h:g.comp j=inj.comp e := by
   apply th
   · intro b
     simp [j,g,aHX,e,inj]
   · intro i
     simp [j,g,aHX,e,inj,newConstants]
 have hc: (nX g).comap j=nX e := by
   rw [zR,h]
   ext b
   simp only [Cy ,RingHom.coe_comp,G7]
   rw [← p5 inj]
   exact (zi F[X] (aar F)).eq_iff
 have he :nX e =
     (nX (ajk k point)).map (oY oj) :=
   etK k point
 have hm:=Vl M mK (nX g)
 change ((nX g).comap j).map j= _ at hm
 have hj:j.comp (oY (σ:=rS) oj) =
     MvPolynomial.map QM:= by
   apply th <;> simp [j,QM]
 rw [hc,he,Nq,hj] at hm
 exact hm
end dF
end
end ac1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace ac1
noncomputable section
open aR oR B7
open scoped Polynomial BigOperators
attribute [local instance] MvPolynomial.algebraMvPolynomial
section Evaluation
variable {F:Type*} [lz F]
theorem epL (k :ao →+* F) (U:F[X]) (hU:U.natDegree<bf) (i:Fin 3) :
   aHX k (fun a=>U.coeff a.val) (KT PV i.val) =
     rD amg (U.map newConstants) i:= by
 have hpoly :=Polynomial.as_sum_range_C_mul_X_pow' U hU
 have he :=oq
   (fun P:F[X]=>(t3 i.val (P.map newConstants)).eval amg) hpoly
 rw [← Fin.sum_univ_eq_sum_range (fun j=>oj (U.coeff j)*p9 ^j)] at he
 simp only [Polynomial.map_sum,zoT,Polynomial.map_monomial,
   t5 ,Polynomial.hasseDeriv_monomial,Polynomial.eval_finsetSum,
   Polynomial.eval_monomial] at he
 simp only [aHX,KT,t5 ,nI,Dv,
   yo ,G7,t8 ,map_natCast,eED]
 rw [rD,he]
 apply vw rfl
 intro a _
 ring
def a4l (k :ao →+* F) (U:F[X]) :nW →+* aar F :=
 (aHX k fun a=>U.coeff a.val).comp tO.toRingHom
theorem ed3 (k :ao →+* F) (U:F[X]) (hU:U.natDegree<bf) :
   a4l k U=pC (aOV k) (rD amg (U.map newConstants)) := by
 apply th
 · intro b
   simp [a4l,tO,aHX]
 · intro i
   change aHX k (fun a=>U.coeff a.val)
    (vk (fun j:Fin 3=>KT PV j.val) (mD i)) =
    pC (aOV k) (rD amg (U.map newConstants)) (mD i)
   rw [Dw ,yo]
   exact epL k U hU i
theorem bJF (k :ao →+* F) (U:F[X]) (b:af 3) :
   ee (newConstants.comp k) amg (rD amg (U.map newConstants)) b =
     c9 F[X] (aar F) (jW k U b) := by
 rw [← bdt,← aVM]
 have h: (zd (amg:aar F)).comp
     (pU newConstants)=c9 F[X] (aar F) := by
   apply v8
   · intro a
     simp [newConstants]
   · simp [amg]
 exact qm h _
theorem fY2 (k :ao →+* F) (y :Fin 3→aar F) :
    ee (newConstants.comp k) amg y=(pC (aOV k) y).comp Bu:= by
  apply th
  · intro b
    have h: (zd (amg:aar F)).comp
        (pU (newConstants.comp k)) =
          (aOV k).comp (c9 ao[X] dF) := by
      apply v8
      · intro a
        simp [newConstants]
      · simp [amg]
    simpa [ee,Bu] using qm h b
  · intro i
    simp [ee,Bu]
theorem bGY (k :ao →+* F) (U:F[X]) (hU:U.natDegree<bf)
  (b:af 3) :
  a4l k U (GZ b)=c9 F[X] (aar F) (jW k U b) := by
 rw [ed3 k U hU,← bJF,fY2]
 rfl
theorem eee (k :ao →+* F) (U:F[X]) (a :rS) (m:ℕ)
   (d v :nW)
   (h:a4l k U d^m*newConstants (U.coeff a.val)=a4l k U v) :
   tO d^m*mD a - tO v ∈
     oV (nX (ajk k (fun j=>U.coeff j.val))) := by
 rw [cS8,Cy]
 let e :=aHX k (fun j=>U.coeff j.val)
 change e (tO d^m*mD a - tO v)=0
 rw [xm e,nI e,t8 e,Pf]
 have he :e (mD a)=newConstants (U.coeff a.val) :=
   yo _ _ _
 rw [he]
 exact h
end Evaluation
theorem ed4 (f :af 3) (hf :zm f) (hd:0<f.degreeOf 2)
    [(Jy f).IsPrime] (U: (WE f)[X]) (hU:U.natDegree<bf)
    (hsol:jW (Jb f) U f=0)
    (hinit :rD (CW f) U=a2l f) :
    nX (a4l (Jb f) U)=Jy f := by
  let eval :=a4l (Jb f) U
  have hc: (nX eval).comap Bu=bf2 f := by
    apply vj
    · intro b hb
      change eval (GZ b)=0 at hb
      rw [bGY _ _ hU] at hb
      have hz :jW (Jb f) U b=0 :=
        (zi (WE f)[X] (aar (WE f))) (hb.trans (p5 _).symm)
      rw [← cFe f hf hd]
      change GZ b∈Jy f
      apply (aO5 f _).mp
      have h:=bdt (Jb f) U (CW f) b
      rw [hinit,bvd,hz,Polynomial.eval_zero] at h
      exact h.symm
    · apply (yJ _).mpr
      change eval (GZ f)=0
      rw [bGY _ _ hU,hsol,p5]
  have hm:=Vl bLC nW (nX eval)
  change ((nX eval).comap Bu).map Bu= _ at hm
  rw [hc,bWU] at hm
  exact hm.symm
end
end ac1
end
section
set_option backward.isDefEq.respectTransparency false
namespace ac1
noncomputable section
open aR B7 oR
open scoped Polynomial
theorem d2y {A R σ:Type*} {F L:Type u}
    [lV A] [lV R] [lz F] [lz L]
    (b:A →+* R) (e :R →+* F) (g:R →+* L)
    (hker :nX e≤nX g) (d:R) (m:ℕ) (v :σ→R)
    (he :e d≠0) (hg:g d≠0) (point :σ→F) (mark :σ→L)
    (hpoint : ∀ i,e d^m*point i=e (v i))
    (hmark : ∀ i,g d^m*mark i=g (v i)) :
    nX (pC (e.comp b) point) ≤
      nX (pC (g.comp b) mark) := by
  let S:=zUF d
  let den:JW d:=⟨d^m,⟨m,rfl⟩⟩
  let l:=pC ((c9 R S).comp b)
    (fun i=>IsLocalization.mk' S (v i) den)
  have ht {D:Type u} [lz D] (t:R →+* D) (h:t d≠0) (p:σ→D)
      (hp : ∀ i,t d^m*p i=t (v i)) :
      (MO (S:=S) d (g:=t) h.isUnit).comp l =
        pC (t.comp b) p:= by
    apply th
    · intro a
      simp [l]
    · intro i
      simp only [l,RingHom.coe_comp,G7,yo]
      apply mul_left_cancel₀ (Te m h)
      have hh:=oq (MO (S:=S) d (g:=t) h.isUnit)
        (IsLocalization.mk'_spec' S (v i) den)
      rw [hp i]
      simpa only [nI,IsLocalization.Away.lift_eq,den,t8] using hh
  let el:=MO (S:=S) d (g:=e) he.isUnit
  let gl:=MO (S:=S) d (g:=g) hg.isUnit
  have hk :nX el≤nX gl:= by
    apply (IsLocalization.under_le_under_iff (JW d) S).mp
    change (nX el).comap (c9 R S) ≤
      (nX gl).comap (c9 R S)
    simpa only [zR,el,gl,IsLocalization.Away.lift_comp] using hker
  have he' : el.comp l=pC (e.comp b) point :=ht e he point hpoint
  have hg' : gl.comp l=pC (g.comp b) mark :=ht g hg mark hmark
  rw [← he',← hg',← zR,← zR]
  exact Qw hk
theorem dhO (S:ao[X]) (b:af 3) :
  jW (zk ao) S b=cK b S:= by
 simp [jW,cK,MvPolynomial.eval₂_id]
 rfl
theorem drX (S:ao[X]) (b:af 3) :
   ee QM PV (rD PV (S.map QM)) b =
     c9 ao[X] dF (cK b S) := by
 rw [← bdt]
 have hm:=aVM (zk ao) QM S b
 rw [dhO,RingHom.comp_id] at hm
 rw [← hm]
 have h: (zd PV).comp (pU QM) =
     c9 ao[X] dF:= by
   apply v8
   · intro a
     simp [QM]
   · simp [PV]
 exact qm h _
theorem bTU (S:ao[X]) :
    (ee QM PV (rD PV (S.map QM))) =
      (Gn (rD PV (S.map QM))).comp Bu:= by
  apply th
  · intro a
    have h: (zd PV).comp (pU QM) =
        c9 ao[X] dF:= by
      apply v8
      · intro c
        simp [QM]
      · simp [PV]
    simpa [ee,Bu] using qm h a
  · intro i
    simp [ee,Bu]
end
end ac1
end
section
namespace bam
noncomputable section
open aR oR ac1 Polynomial
open scoped BigOperators
@[simp] private theorem alJ (P:af 3) (m:Fin 3 →₀ ℕ) :
    (DU P).coeff m=pQ (P.coeff m) := by
  classical
  rw [DU,MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial,Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,p5]
private theorem a2C (p:ao[X]) :
  DU (qz p:af 3)=qz (pQ p) := by
 classical
 apply MvPolynomial.ext
 intro m
 rw [alJ]
 by_cases hm:0=m <;> simp [MvPolynomial.coeff_C,hm]
private theorem a2D (P Q:af 3) :
  DU (P+Q)=DU P+DU Q:= by
 ext m
 simp
private theorem bnc (P:af 3) (j:Fin 3) :
  DU (P*mD j)=DU P*mD j:= by
 classical
 ext m
 rw [alJ,VS ,VS]
 split_ifs <;> simp
section ChainRule
variable {F:Type*} [lV F]
private theorem aNu (k :ao →+* F) (P:af 3) (a :Fin 3→F[X]) :
    let e :=pC (pU k) a
    pQ (e P)=e (DU P) +
      ∑ i,pQ (a i)*e (Kl i P) := by
  classical
  let e :=pC (pU k) a
  change pQ (e P)=e (DU P)+_
  induction P using MvPolynomial.induction_on with
  | C c=>simp [e,a2C,derivative_map]
  | add P Q hP hQ =>
    simp only [uz ,a2D,hP,hQ,mul_add,SU]
    ring
  | mul_X P j ih =>
    have hx :e (mD j)=a j:=yo _ _ _
    rw [nI,hx,derivative_mul,ih,bnc,nI,hx]
    simp only [MvPolynomial.pderiv_mul,uz ,nI,mul_add,SU]
    have left: (∑ i,pQ (a i)*(e (Kl i P)*e (mD j))) =
        (∑ i,pQ (a i)*e (Kl i P))*a j:= by
      simp only [hx,Finset.sum_mul,xI]
    have right: (∑ i,pQ (a i)*(e P*e (Kl i (mD j)))) =
        pQ (a j)*e P:= by
      simp [MvPolynomial.pderiv_X,Qx ,mul_ite]
    rw [left,right]
    ring
private theorem bo0 (U:F[X]) :
  pQ (t3 1 U)=2*t3 2 U:= by
 have h:=LinearMap.congr_fun (hasseDeriv_comp (R:=F) 1 1) U
 simpa [hasseDeriv_one',Nat.choose_one_right,R9] using h
private theorem a3I (k :ao →+* F) (U:F[X]) (P:af 3) :
   pQ (jW k U P)=jW k U (D3 P) +
     pQ (t3 2 U)*jW k U (yB P) := by
 change pQ (pC (pU k)
   (fun i:Fin 3=>t3 i.val U) P)= _
 rw [aNu k P (fun i=>t3 i.val U),Fin.sum_univ_three]
 simp only [D3,yB,uz ,nI,map_ofNat,yo ,
   jW]
 have hsecond:pQ (pQ U)=2*t3 2 U:= by
   simpa only [hasseDeriv_one] using bo0 U
 simp only [show (0:Fin 3).val=0 by rfl,show (1 :Fin 3).val=1 by rfl,
   show (2 :Fin 3).val = 2 by rfl,hasseDeriv_zero,LinearMap.id_apply,
   hasseDeriv_one,hsecond]
 ring
private theorem a3K (k :ao →+* F) (U:F[X]) (f P:af 3)
   (hf :jW k U f=0) :
   jW k U (Ev f P) =
     jW k U (yB f)*pQ (jW k U P) := by
 have hz :jW k U (D3 f) +
     pQ (t3 2 U)*jW k U (yB f)=0:= by
   rw [← a3I,hf,p5]
 rw [Ev,xm,nI,nI]
 change jW k U (yB f)*jW k U (D3 P) -
   jW k U (D3 f)*jW k U (yB P)= _
 rw [a3I]
 linear_combination -jW k U (yB P)*hz
private theorem anS (a :ℕ) (S V:F[X]) :
    S*(S*pQ (S^a*V)) -
      (a :F[X])*(S^a*V)*(S*pQ S) =
        S^(a+2)*pQ V:= by
  cases a with
  | zero=>simp [pow_two,mul_assoc]
  | succ a =>
    rw [derivative_mul,derivative_pow,Nat.succ_sub_one,
      pow_add S (a+1) 2,pow_succ' S a]
    simp only [Nat.cast_succ,C_add,C_1,C_eq_natCast]
    ring
theorem bFn (k :ao →+* F) (U:F[X]) (f :af 3)
    (hf :jW k U f=0) (j:ℕ) :
    jW k U (AR f j) =
      jW k U (yB f)^(2*j+1) *
        (pQ^[j + 1]) (t3 2 U) := by
  induction j with
  | zero =>
    have hz :jW k U (D3 f) +
        pQ (t3 2 U)*jW k U (yB f)=0:= by
      rw [← a3I,hf,p5]
    simp only [AR,map_neg,Nat.mul_zero,Nat.zero_add,pow_one,
      zS5]
    linear_combination -hz
  | succ j ih =>
    rw [AR,xm,nI,nI,nI,map_natCast,
      a3K _ _ _ _ hf,a3K _ _ _ _ hf,ih,
      show 2*(j+1)+1=(2*j+1)+2 by omega,
      Zf pQ (j+1) (t3 2 U)]
    exact anS _ _ _
theorem bPp (U:F[X]) (j:ℕ) :
   2*(pQ^[j + 1]) (t3 2 U)=(pQ^[j+3]) U:= by
 have hsecond: (pQ^[2]) U=2*t3 2 U:= by
   rw [Zf pQ 1 U,zS5]
   simpa only [hasseDeriv_one'] using bo0 U
 rw [show j+3=(j+1)+2 by omega,
   Function.iterate_add_apply pQ  (j+1) 2 U,hsecond]
 simpa only [Sv] using
   (Polynomial.iterate_derivative_natCast_mul (n:=2) (k :=j+1)
     (f :=t3 2 U)).symm
end ChainRule
end
end bam
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace cy5
noncomputable section
open cu gT pI akR Polynomial
open scoped nonZeroDivisors
local notation "PC" => Polynomial.C
local notation "PX" => Polynomial.X
local notation "MP" => MvPolynomial
local notation "MC" => MvPolynomial.C
local notation "MX" => MvPolynomial.X
local notation "E9" => Ideal.Quotient.mk
private abbrev Param:=MP (Fin 4) FX
private abbrev Den:=nonZeroDivisors Param
private abbrev aHW:Param →+* dV:=c9 _ _
private abbrev Local {R:Type} [lV R] (p:Param →+* R) :=
 Localization (Den.map p)
private abbrev Fr {R:Type} [lV R] (p:Param →+* R) :R →+* Local p :=
 c9 _ _
private def coeff {R:Type} [lV R] (p:Param →+* R) :
  dV →+* Local p :=
 zvq (M:=Den) (g:=(Fr p).comp p)
  fun d=>C4 (Local p) (M:=Den.map p) ⟨p d,⟨d,d.prop,rfl⟩⟩
@[simp] private theorem bXL {R:Type} [lV R] (p:Param →+* R) (x :Param) :
   coeff p (aHW x)=Fr p (p x) :=zX4 _ x
private def descend {R T:Type} [lV R] [lV T]
  (p:Param →+* R) (r :R →+* T) (k :dV →+* T)
  (h:r.comp p=k.comp aHW) :Local p →+* T :=
 zvq (M:=Den.map p) (g:=r) <| by
  rintro ⟨_,x,hx,rfl⟩
  change Dz (r (p x))
  rw [show r (p x)=k (aHW x) from qm h x]
  exact (C4 dV (M:=Den) ⟨x,hx⟩).map k
@[simp] private theorem cKA {R T:Type} [lV R] [lV T]
   {p:Param →+* R} {r :R →+* T} {k :dV →+* T}
   (h:r.comp p=k.comp aHW) (x :R) :
   descend p r k h (Fr p x)=r x :=zX4 _ x
private theorem cKz {R T:Type} [lV R] [lV T]
  {p:Param →+* R} {r :R →+* T} {k :dV →+* T}
  (h:r.comp p=k.comp aHW) :
  (descend p r k h).comp (coeff p)=k := by
 apply UZ Den
 apply yL
 intro x
 simpa only [x7,bXL,cKA] using qm h x
private theorem b75 {R T:Type} [lV R] [lV T]
  (p:Param →+* R) (f :R →+* T) :
  C9 ((Den.map p).map f) (Local (f.comp p)) := by
 change C9 ((Den.map p.toMonoidHom).map f.toMonoidHom) _
 rw [Submonoid.map_map]
 exact inferInstanceAs (C9 (Den.map (f.comp p)) (Local (f.comp p)))
private def vN {R T:Type} [lV R] [lV T]
  (p:Param →+* R) (f :R →+* T) :Local p →+* Local (f.comp p) :=
 letI:=b75 p f
 IsLocalization.map _ f (Den.map p).le_comap_map
@[simp] private theorem exD {R T:Type} [lV R] [lV T]
   (p:Param →+* R) (f :R →+* T) (x :R) :
   vN p f (Fr p x)=Fr (f.comp p) (f x) := by
  let:=b75 p f
  unfold vN
  apply IsLocalization.map_eq
private theorem exB {R T:Type} [lV R] [lV T]
  (p:Param →+* R) (f :R →+* T) (hf :sI f) :
  sI (vN p f) := by
 let:=b75 p f
 unfold vN
 apply IsLocalization.map_injective_of_injective
 exact hf
private theorem exA {R T:Type} [lV R] [lV T]
  (p:Param →+* R) (f :R →+* T) :
  (vN p f).comp (coeff p)=coeff (f.comp p) := by
 apply UZ Den
 apply yL
 intro x
 simp only [x7,bXL,exD]
private def slope {R:Type} [Zero R] (b:Bool) (s :R) :R:=if b then s else 0
@[simp] private theorem b8I {R T:Type} [lV R] [lV T]
   (f :R →+* T) (b:Bool) (s :R) :f (slope b s)=slope b (f s) := by
  cases b <;> simp [slope]
private def parameters {R:Type} [lV R] (c:FX →+* R) (b:Bool)
  (a s u y v :R) :Param →+* R :=
 pC c ![a,s,u,y+slope b s*v]
private theorem dOa {R T:Type} [lV R] [lV T]
   (f :R →+* T) (c:FX →+* R) (b:Bool) (a s u y v :R) :
   f.comp (parameters c b a s u y v) =
     parameters (f.comp c) b (f a) (f s) (f u) (f y) (f v) := by
 apply th
 · intro x
   simp [parameters]
 · intro i
   fin_cases i <;> simp [parameters]
private theorem aOg (f :FX[X]) :C7 (PC f)=F7 f := by
 have h: (oi.comp A7).comp (pU MC)=F7:= by
  apply v8
  · intro a
    simp [F7,oi,A7,pZ]
  · simp [F7,oi,A7]
 simpa [C7,iJ,Gw,qQ.Ng] using qm h f
@[simp] private theorem gQf :C7 ((PC (PX:FX[X])) :tK)=MX 2 := by
  simp [aOg,F7]
@[simp] private theorem gQe :C7 (PX:tK)=MX 3:= by
  change ((PX:tK).map (pU MC)).eval₂
   (oi.comp A7) (MX 3)= _
  rw [Polynomial.map_X,Polynomial.eval₂_X]
@[simp] private theorem epS (c:FX) :C7 (PC (PC c) :tK)=MC c:= by
  simp [aOg,F7]
private abbrev Source (I:cy p6) :=MP (Fin 3) (aRM I)
private abbrev N5 (I:cy p6) :=MP (Fin 2) (gk I)
private abbrev aJx (I:cy p6) :tK →+* Source I :=
 MvPolynomial.C.comp (E9 (I.comap C7))
private abbrev acv (I:cy p6) :p6 →+* N5 I :=
 MvPolynomial.C.comp (E9 I)
@[simp] private theorem goj (I:cy p6) (z :tK) :
   apn I (aJx I z)=acv I (C7 z) := by
  change apn I (MC (E9 (I.comap C7) z))= _
  simp only [apn,Dv,x7,FK]
private def apw (I:cy p6) (b:Bool) :Param →+* Source I :=
 parameters ((aJx I).comp (Polynomial.C.comp PC)) b (MX 0) (MX 1) (MX 2)
  (aJx I (PC PX)) (aJx I PX)
private abbrev a6p (I:cy p6) (b:Bool) :Param →+* N5 I :=
 (apn I).comp (apw I b)
private theorem a6q (I:cy p6) (b:Bool) :
   a6p I b=parameters ((acv I).comp MC) b (MX 0) (MX 1)
     (acv I (MX 0)+MX 0*acv I (MX 1))
     (acv I (MX 2)) (acv I (MX 3)) := by
 unfold a6p apw
 rw [dOa]
 have hc: (apn I).comp ((aJx I).comp (Polynomial.C.comp PC)) =
     (acv I).comp MC:= by
   apply yL
   intro x
   exact (goj I (PC (PC x))).trans
     (oq (acv I) (epS x))
 rw [hc]
 simp [apn,acv]
private theorem bGW (x :FX) :aHW (MC x)=c9 FX dV x :=
 (Pr FX Param dV x).symm
private def yZ (b:Bool) :tK →+* dV[X] :=
 Bf (Bf (Polynomial.C.comp (c9 FX dV))
  (PC (kz 3)-PC (slope b (kz 1))*PX)) PX
private theorem epK (G:tK) :yZ false G=bJ2 G:= by
  have h:yZ false=pU
      (Bf (c9 FX dV) (kz 3)) := by
    apply Ww
    · apply v8
      · intro x
        simp [yZ]
      · simp [yZ,slope]
    · simp [yZ]
  exact qm h G
private abbrev akJ (G:tK) (b:Bool) :cy dV[X] :=
 lI {yZ b G}
private def aVl (I:cy p6) (G:tK) (b:Bool)
  (hi:I.comap C7=lI {G}) :
  Source I →+* dV[X] ⧸ akJ G b :=
 pC (Wm (akJ G b) (yZ b) (by
  rw [hi,Ideal.span_le]
  intro z hz
  obtain rfl :=Set.mem_singleton_iff.mp hz
  exact qJ rfl))
  ![c9 _ _ (kz 0),c9 _ _ (kz 1),
    c9 _ _ (kz 2)]
private theorem cUT (I:cy p6) (G:tK) (b:Bool)
    (hi:I.comap C7=lI {G}) :
    (aVl I G b hi).comp (apw I b) =
      (c9 dV (dV[X] ⧸ akJ G b)).comp aHW:= by
  apply th
  · intro x
    simp [apw,parameters,aVl,aJx,FK,yZ,bGW]
    rfl
  · intro i
    fin_cases i
    · simp [apw,parameters,aVl,kz]
    · simp [apw,parameters,aVl,kz]
    · simp [apw,parameters,aVl,kz]
    · cases b <;>
        simp [apw,parameters,aJx,aVl,FK,yZ,
          slope,kz] <;> first | rfl | exact sub_add_cancel _ _
private theorem enN (I:cy p6) (G:tK) (b:Bool)
    (hi:I.comap C7=lI {G}) :
    ∃ f : (dV[X] ⧸ akJ G b) →+* Local (apw I b),
      sI f ∧
      f.comp (c9 dV (dV[X] ⧸ akJ G b)) =
        coeff (apw I b) := by
  let p:=apw I b
  let w:dV[X] →+* Local p :=
    Bf (coeff p) (Fr p (aJx I PX))
  have hw:w.comp (yZ b)=(Fr p).comp (aJx I) := by
    apply Ww
    · apply v8
      · intro x
        simp [w,p,yZ,← bGW,apw,parameters]
      · cases b <;> simp [w,p,yZ,kz,apw,parameters,slope]
    · simp [w,yZ]
  have hzero :w (yZ b G)=0:= by
    change (w.comp (yZ b)) G=0
    rw [hw]
    have hg:G∈I.comap C7:= by rw [hi]; exact qJ rfl
    change Fr p (MC (E9 (I.comap C7) G))=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg,p5 ,p5]
  have hker :akJ G b≤nX w :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (RingHom.mem_ker.mpr hzero))
  let f :=Zi (akJ G b) w (fun z hz=>RingHom.mem_ker.mp (hker hz))
  have hf :f.comp (c9 dV (dV[X] ⧸ akJ G b)) =
      coeff p:= by
    apply yL
    intro x
    change f (E9 (akJ G b) (PC x))=coeff p x
    simp [f,w]
  let r :=descend p (aVl I G b hi) _ (cUT I G b hi)
  have hr :=cKz (cUT I G b hi)
  have hid :r.comp f=zk _:= by
    apply Ideal.Quotient.ringHom_ext
    apply v8
    · intro x
      change (r.comp (f.comp (c9 dV (dV[X] ⧸ akJ G b)))) x= _
      rw [hf]
      exact qm hr x
    · change r (f (E9 (akJ G b) PX))=E9 (akJ G b) PX
      simp [f,w,r,aVl,aJx,FK,yZ]
  have hinv :X8 r f := fun x=>qm hid x
  exact ⟨f,hinv.injective,hf⟩
private def aIh (b:Bool) :PI :=
 MX 2+MC (slope b (kz 1))*MX 3-MC (kz 3)
private abbrev alj (I:cy p6) (b:Bool) :cy PI :=
 I.map AU ⊔ lI {JN,aIh b}
private abbrev Target (I:cy p6) (b:Bool) :=PI ⧸ alj I b
private abbrev aQK (I:cy p6) (b:Bool) :dV →+* Target I b :=
 c9 _ _
private def aX3 (I:cy p6) (b:Bool) :N5 I →+* Target I b :=
 pC
  (Wm (alj I b) AU (Ideal.le_comap_map.trans
    (Qw z7)))
  ![aQK I b (kz 0),aQK I b (kz 1)]
@[simp] private theorem dgO (I:cy p6) (b:Bool) (x :p6) :
   aX3 I b (MC (E9 I x))=E9 (alj I b) (AU x) := by
  simp [aX3,FK]
@[simp] private theorem gAz (I:cy p6) (b:Bool) (i:Fin 2) :
    aX3 I b (MX i) =
      ![aQK I b (kz 0),aQK I b (kz 1)] i :=
  yo _ _ _
private theorem gAA (I:cy p6) (b:Bool) :
    (aX3 I b).comp (a6p I b)=(aQK I b).comp aHW:= by
  apply th
  · intro x
    simp only [x7,a6q,parameters,Dv,
      dgO,AU,TZ,bGW]
    rfl
  · intro i
    fin_cases i
    · simp [a6q,parameters,kz]
    · simp [a6q,parameters,kz]
    · simp [a6q,parameters,AU]
      apply sub_eq_zero.mp
      change (E9 (alj I b) (MX 0)+E9 (alj I b) (MC (kz 0)) *
        E9 (alj I b) (MX 1))-E9 (alj I b) (MC (kz 2))=0
      rw [← nI,← uz ,← xm]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (UP (qJ
        (show JN ∈ {JN,aIh b} by simp)))
    · simp [a6q,parameters,AU]
      rw [← b8I (aQK I b)]
      apply sub_eq_zero.mp
      change (E9 (alj I b) (MX 2) +
        E9 (alj I b) (MC (slope b (kz 1))) *
        E9 (alj I b) (MX 3))-E9 (alj I b) (MC (kz 3))=0
      rw [← nI,← uz ,← xm]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (UP (qJ
        (show aIh b ∈ {JN,aIh b} by simp)))
private theorem cZt {R T:Type} [lV R] [lV T]
  (f :R →+* T) (x a y :R) :f x+f a*f y - f (x+a*y)=0:= by
 simp
private theorem eKe {T:Type} [lV T] (I:cy p6) (b:Bool)
    (n:N5 I →+* T) (k :dV →+* T) (hk :k.comp aHW=n.comp (a6p I b)) :
    ∃ r :Target I b →+* T,r.comp (aX3 I b)=n:= by
  let w:PI →+* T:=pC k (fun i=>n (acv I (MX i)))
  have hw:w.comp AU=n.comp (acv I) := by
    apply th
    · intro x
      simp only [x7,AU,TZ,w,Dv,
        ← bGW]
      simpa only [x7,a6q,parameters,Dv]
        using qm hk (MC x)
    · intro i
      simp [w,AU]
  have hcoeff (i:Fin 4) :k (kz i)=n
      (![MX 0,MX 1,acv I (MX 0)+MX 0*acv I (MX 1),
        acv I (MX 2)+slope b (MX 1)*acv I (MX 3)] i) := by
    change k (aHW (MX i))= _
    simpa only [x7,a6q,parameters,yo]
      using qm hk (MX i)
  have hwC (x :dV) :w (MC x)=k x :=Dv _ _ _
  have hwX (i:Fin 4) :w (MX i)=n (acv I (MX i)) :=yo _ _ _
  have hw_seed :w JN=0:= by
    simp only [JN,w.map_sub,w.map_add,w.map_mul,hwX,hwC]
    rw [hcoeff 0,hcoeff 2]
    simp only [zbs,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    exact cZt n (acv I (MX 0)) (MX 0) (acv I (MX 1))
  have hw_jet:w (aIh b)=0:= by
    simp only [aIh,w.map_sub,w.map_add,w.map_mul,hwX,hwC,b8I k]
    rw [hcoeff 1,hcoeff 3]
    simp only [Matrix.cons_val_one,zbs,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons,← b8I n]
    exact cZt n (acv I (MX 2)) (slope b (MX 1)) (acv I (MX 3))
  have hker :alj I b≤nX w:= by
    apply t9
    · rw [Ts ,zR,hw]
      intro x hx
      apply RingHom.mem_ker.mpr
      change n (MC (E9 I x))=0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx,p5 ,p5]
    · rw [Ideal.span_le]
      intro z hz
      simp only [QL,LR] at hz
      rcases hz with rfl | rfl
      · exact RingHom.mem_ker.mpr hw_seed
      · exact RingHom.mem_ker.mpr hw_jet
  let r :=Zi (alj I b) w (fun z hz=>RingHom.mem_ker.mp (hker hz))
  have hrC (x :dV) :r (aQK I b x)=k x := by
    change r (E9 (alj I b) (MC x))= _
    rw [Ideal.Quotient.lift_mk,hwC]
  refine ⟨r,?_⟩
  apply th
  · intro z
    obtain ⟨x,rfl⟩:=zf z
    change r (aX3 I b (MC (E9 I x)))=n (acv I x)
    rw [dgO]
    exact qm hw x
  · intro i
    rw [x7,gAz]
    fin_cases i
    · exact (hrC (kz 0)).trans (hcoeff 0)
    · exact (hrC (kz 1)).trans (hcoeff 1)
private theorem exP (I:cy p6) (b:Bool) :
   ∃ f :Local (a6p I b) →+* Target I b,
     sI f∧f.comp (coeff (a6p I b))=aQK I b:= by
 let p:=a6p I b
 let f :=descend p (aX3 I b) (aQK I b) (gAA I b)
 obtain ⟨r,hr⟩:=eKe I b (Fr p) (coeff p)
   (yL (bXL p))
 have hid :r.comp f=zk _:= by
   apply UZ (Den.map p)
   apply yL
   intro x
   change r (f (Fr p x))=Fr p x
   rw [show f (Fr p x)=aX3 I b x from cKA _ _]
   exact qm hr x
 have hinv :X8 r f := fun x=>qm hid x
 exact ⟨f,hinv.injective,cKz _⟩
private theorem dcx (I:cy p6) (G:tK) (b:Bool)
    (hi:I.comap C7=lI {G}) (hinj:sI (apn I)) :
    ∃ f : (dV[X] ⧸ akJ G b) →ₗ[dV] Target I b,
      Function.Injective f := by
  obtain ⟨f,hf,hfC⟩:=enN I G b hi
  obtain ⟨g,hg,hgC⟩:=exP I b
  let m:=vN (apw I b) (apn I)
  have hm:=exB (apw I b) (apn I) hinj
  let e : (dV[X] ⧸ akJ G b) →ₐ[dV] Target I b :=
    { g.comp (m.comp f) with
      commutes' := fun x=> by
        change (g.comp (m.comp (f.comp (c9 dV _)))) x= _
        rw [hfC,exA,hgC] }
  exact ⟨e.toLinearMap,hg.comp (hm.comp hf)⟩
theorem proof :akR.c2 := by
  intro I G hi hinj
  constructor
  · let injects (J:cy dV[X]) (L:cy PI) :Prop :=
      ∃ f : (dV[X] ⧸ J) →ₗ[dV] (PI ⧸ L),sI f
    have h:injects (akJ G false) (alj I false) :=
      dcx I G false hi hinj
    have hsource :akJ G false=lI {bJ2 G} :=
      oq (fun z :dV[X]=>lI {z}) (epK G)
    have hline :aIh false=MX 2 - MC (kz 3) := by simp [aIh,slope]
    have htarget :alj I false =
        I.map AU ⊔ lI {JN,MX 2 - MC (kz 3)} :=
      oq (fun z=>I.map AU ⊔ lI {JN,z}) hline
    rw [hsource,htarget] at h
    exact h
  · exact dcx I G true hi hinj
end
end cy5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace czF
noncomputable section
open K1 cu qQ XY Polynomial UniqueFactorizationMonoid
open scoped BigOperators
abbrev aii:aZ →+* Jet:=C.comp C
private theorem c2O {D:Jet} (hi:zm D) (hv :D.natDegree=0)
   (hs :D∉uW aii) :
   C (D.coeff 0)=D ∧zm (D.coeff 0)∧0<(D.coeff 0).natDegree := by
 have hC:=(eq_C_of_natDegree_eq_zero hv).symm
 have hiC:zm (C (D.coeff 0) :Jet) := by rwa [hC]
 refine ⟨hC,⟨fun h=>hiC.not_isUnit (h.map C),?_⟩,?_⟩
 · intro a b hab
   have he : (C (D.coeff 0) :Jet)=C a*C b:= by rw [← C_mul,hab]
   exact (hiC.isUnit_or_isUnit he).imp isUnit_C.mp isUnit_C.mp
 · by_contra! h
   exact hs ⟨(D.coeff 0).coeff 0,by
     change C (C ((D.coeff 0).coeff 0))=D
     rw [← eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h),hC]⟩
theorem ezq (z :K) (S:K[X]) (f :Equation) :
  vf z S (C f)=yq f z S:= by
 change (C f :Jet).eval₂ _ _ = _
 rw [eval₂_C]
 rfl
theorem cZL (z :K) (S:K[X]) (a :aZ) :
  vf z S (aii a)=qD z a := by
 change vf z S (C (C a))= _
 rw [ezq,yq,eval₂_C]
theorem cZK (z :K) (S:K[X]) (g:IW) :
   vf z S (Ng g)=FW g S:= by
 have hgraph: (qD z).comp qz=zk FX:= by
   ext1 a
   exact MvPolynomial.eval_C _
 have hcoeff : (Bf (qD z) (kr S)).comp
     (pU qz)=zd (kr S) := by
   apply yL
   intro f
   change (f.map qz).eval₂ (qD z) (kr S)=f.eval (kr S)
   rw [KA,hgraph,eval₂_id]
 change (g.map (pU qz)).eval₂
   (Bf (qD z) (kr S)) (kr S.derivative)=g.eval₂ _ _
 rw [KA,hcoeff]
end
end czF
end
section
namespace aiJ
noncomputable section
open aR oR we MvPolynomial
open RingTheory.Sequence
open scoped Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem cS5:sI a4j :=
 (zi cH[X] dF).comp
   (zTo _ (RingHom.injective (c9 ao cH)))
theorem cTb {f :af 3} (hf :f≠0) :GZ f≠0:= by
 simpa only [GZ,Ne,map_eq_zero_iff _ (map_injective _ cS5)] using hf
theorem bqq (f :af 3) : (GZ f).totalDegree≤f.totalDegree :=
 Finset.sup_mono (support_map_subset a4j f)
private theorem bgr {R:Type*} [lV R] (a b:R) :
   qU (Du a R) b ↔
     SC (oy (lI {a}) b) := by
 let e :Du a R ≃ₗ[R] R ⧸ (lI {a} : cy R) :=
   RD _ _ (by
     rw [← Rm,zde]
     change ((lI {a}).map (zk R) :cy R)=lI {a}
     rw [Ideal.map_id])
 exact e.isSMulRegular_congr b
private theorem cSG {A B:Type*} [lV A] [PA A]
  [lV B] [IsDomain B] (φ:A →+* B) (hφ:sI φ) :φ.Flat := by
 let:t7 A B:=φ.toAlgebra
 change LQ A B
 have :zYo A B :=
  (Module.isTorsionFree_iff_algebraMap_injective).mpr hφ
 infer_instance
private theorem c7T {A B σ:Type*} [lV A] [lV B]
   (φ:A →+* B) (hφ:φ.Flat) {f g:lJ σ A}
   (hf :qU (lJ σ A) f)
   (hg:SC (oy (lI {f}) g)) :
   SC (oy (lI {oY φ f}) (oY φ g)) := by
 let:t7 A B:=φ.toAlgebra
 have :LQ A B:=hφ
 have hbase :IsBaseChange (lJ σ A)
     (XJ A B (lJ σ B)).toLinearMap :=
   Algebra.IsPushout.out
 have :LQ (lJ σ A) (lJ σ B) :=
   Module.Flat.isBaseChange (R:=A) (S:=lJ σ A) (M:=B)
     (N :=lJ σ B) hbase
 have hseq :pG (lJ σ A) [f,g] := by
   rw [isWeaklyRegular_cons_iff,xL,bgr]
   exact ⟨hf,hg⟩
 have h:=hseq.of_flat (S:=lJ σ B)
 change pG (lJ σ B) [oY φ f,oY φ g] at h
 rw [isWeaklyRegular_cons_iff,xL,bgr] at h
 exact h.2
end
end aiJ
end
section
namespace aiJ
noncomputable section
open aR oR we MvPolynomial Finset
open scoped BigOperators
private theorem cIR {J Q:aYJ} (hQ:Q.IsPrime) (hJQ:J≤Q)
   (hJdim: (u9 J).natDegree≤1)
   (hQdim: (u9 Q).natDegree=1) :
   Q∈J.minimalPrimes := by
 let:=hQ
 obtain ⟨P,hP,hPQ⟩:=zXL hJQ
 rcases eq_or_lt_of_le hPQ with he | hlt
 · exact he ▸ hP
 · obtain ⟨x,hxQ,hxP⟩:=SetLike.exists_of_lt hlt
   have hdimP:=(zy5 hP.le).trans hJdim
   have hle :P ⊔ lI {x} ≤ Q :=
     t9 hPQ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxQ))
   have hdrop:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
     hP.isPrime hxP xu).1
   have hdimQ:=zy5 hle
   omega
theorem aM6 (Q:Bk) (hQ:Q.IsPrime)
  (hdim: (u9 Q).natDegree=1) :
  ∃ d:ℕ,0<d∧Gi Q=(d:ℚ) := by
 let H :=u9 Q
 have hlin:H=oj (H.coeff 0)+Polynomial.C (H.coeff 1)*Polynomial.X:= by
  have hH :H.natDegree<2 := by change (u9 Q).natDegree<2; omega
  simpa [Finset.sum_range_succ] using H.as_sum_range_C_mul_X_pow' hH
 have evalH (u:ℚ) :H.eval u=H.coeff 0+H.coeff 1*u:= by
  conv_lhs=>rw [hlin]
  simp
 obtain ⟨N,hN⟩:=Z0 Q
 let m:=G2 Q (N+1)
 let n:=G2 Q N
 have hdiff :Gi Q=(m:ℚ)-(n:ℚ) := by
  rw [Gi ,hdim,Nat.factorial_one,G8 ,ze,Polynomial.leadingCoeff,hdim]
  dsimp only [m,n]
  rw [← hN (N+1) (Un _),← hN N xu]
  change H.coeff 1=H.eval ((N+1 :ℕ) :ℚ) - H.eval (N :ℚ)
  rw [evalH,evalH,NZ,G8]
  ring
 have hmn:n< m:= by
  have hpos :=affineDegree_pos hQ.ne_top
  rw [hdiff] at hpos
  exact_mod_cast sub_pos.mp hpos
 exact ⟨m - n,Nat.sub_pos_of_lt hmn,hdiff.trans (Nat.cast_sub hmn.le).symm⟩
end
end aiJ
end
section
namespace aiJ
noncomputable section
open aR oR we MvPolynomial Finset
open scoped BigOperators
def c1 :Prop :=
  ∀ f :af 3,
    (∀ Q:Bk,acU f Q→XP f Q) ∧
      Set.InjOn lA {Q:Bk | acU f Q}
def c2 :Prop :=
  ∀ Q:Bk,Q.IsPrime →
    (u9 Q).natDegree=1→(gN Q).IsPrime →
    asY Q →
    (u9 (lA Q)).natDegree=1 ∧
      Gi Q≤Gi (lA Q)
end
end aiJ
end
section
set_option maxRecDepth 2000
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false
namespace YT
noncomputable section
open aR we aiJ NS MvPolynomial
open scoped Polynomial
abbrev abB:=AlgebraicClosure dF
private def aHY:cH[X] →+* abB :=
 (c9 dF abB).comp (c9 cH[X] dF)
private def qK:cH →+* abB:=aHY.comp oj
private theorem aDK {k σ:Type*} [lz k] [yU σ] (c:σ→k) :
   (∑ i:σ,qz (c i)*mD i).IsHomogeneous 1 :=
 (homogeneousSubmodule σ k 1).sum_mem fun i _=>isHomogeneous_C_mul_X _ i
theorem b6H (j:ℕ) : (B7.KT adE j).IsHomogeneous 1 :=
 aDK fun i:Fin bf =>
  (i.val.choose j:dF)*adE^(i.val - j)
private theorem arj {k K σ:Type*} [lz k] [lz K] [yU σ]
   (f :k →+* K) (x :σ→K) (t:K) {p:lJ σ k} {n:ℕ}
   (hp:p.IsHomogeneous n) :eval₂ f (fun i=>t*x i) p=t^n*eval₂ f x p:= by
 classical
 rw [eval₂_eq',eval₂_eq',Finset.mul_sum]
 refine vw rfl fun d hd => ?_
 have hdeg:d.degree=n:= by
   by_contra h
   exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero h)
 rw [show (∏ i:σ,(t*x i)^d i)=t^n * ∏ i:σ,x i^d i by
   simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
     ← Finsupp.degree_eq_sum,hdeg]]
 ring
private theorem dsn {k K σ:Type*} [lz k] [lz K] [t7 k K] [yU σ]
  (x :σ→K) (t:K) {p:lJ σ k} {n:ℕ} (hp:p.IsHomogeneous n)
  (h:vk x p=0) :vk (fun i=>t*x i) p=0:= by
 rw [aeval_def] at h ⊢
 rw [arj _ _ _ hp,h,mul_zero]
private theorem bsk {k K σ:Type*} [lz k] [lz K]
  (f :k →+* K) (I:cy (lJ σ k)) {p:lJ σ k} {n:ℕ}
  (hp:p∈I) (hn:p.totalDegree≤n) :
  oY f (G4 n p)∈lW (I.map (oY f)) := by
 have he :oY f (G4 n p) =
    G4 n (oY f p) := by
  ext d
  by_cases hd:d.degree=n <;>
    simp only [coeff_homogeneousComponent,coeff_map,hd,ite_true,ite_false,p5]
 have hd: (oY f p).totalDegree≤p.totalDegree :=
  Finset.sup_mono (support_map_subset f p)
 exact qJ ⟨oY f p,n,xW _ hp,hd.trans hn,he⟩
private theorem aOX (Q:Bk) {x :Fin bf→abB}
   (hx :x∈Gk abB (lW (gN Q))) {i:Fin bf}
   (hi:x i≠0) :
   letI:t7 cH abB:=qK.toAlgebra
   (fun j=>(x i)⁻¹*x j)∈Gk abB (KL Q i) := by
 change KL Q i≤nX (pC qK (fun j=>(x i)⁻¹*x j))
 apply t9
 · apply Ideal.span_le.mpr
   rintro _ ⟨p,n,hp,hn,rfl⟩
   have he :=hx _ (bsk (c9 cH dF) Q hp hn)
   rw [aeval_def,eval₂_map] at he
   change eval₂ qK x (G4 n p)=0 at he
   change eval₂ qK (fun j=>(x i)⁻¹*x j) (G4 n p)=0
   rw [arj qK x ((x i)⁻¹) (homogeneousComponent_isHomogeneous ..),he,
     mul_zero]
 · apply Ideal.span_le.mpr
   rintro _ (rfl :_=mD i - 1)
   change eval₂ qK (fun j=>(x i)⁻¹*x j) (mD i - 1)=0
   rw [eval₂_sub,eval₂_X,eval₂_one]
   exact sub_eq_zero.mpr (Re hi)
private theorem a4a {k K σ:Type*} [lz k] [lz K] [t7 k K]
  [IsAlgClosed k] [Finite σ] (J:cy (lJ σ k))
  (hJ: (u9 J).natDegree=0)
  {x :σ→K} (hx :x∈Gk K J) (j:σ) : ∃ c:k,c9 k K c=x j:= by
 letI:ov k (lJ σ k ⧸ J) :=
  moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
 let e : (lJ σ k ⧸ J) →ₐ[k] K:=Ideal.Quotient.liftₐ J (vk x) hx
 have h:Mz k (x j) := by
  have hJX:=(Algebra.IsIntegral.isIntegral (R:=k) (oy J (mD j))).map e
  change Mz k (vk x (mD j)) at hJX
  simpa only [Dw] using hJX
 apply h.mem_range_algHom_of_minpoly_splits (K:=k) _ (Algebra.ofId k K)
 simpa only [Algebra.algebraMap_self,zeh] using
  IsAlgClosed.splits (minpoly k (x j))
private theorem eM7 {k σ:Type*} [lz k] [yU σ]
   (d:σ→ℕ) (hd:sI d) (a :σ→k) {i:σ} (hi:a i≠0) :
   (∑ j:σ,SD (d j) (a j))≠0:= by
 classical
 let P:ox k := ∑ j:σ,SD (d j) (a j)
 have hc:P.coeff (d i)=a i:= by
   rw [show P.coeff (d i) = ∑ j:σ,(SD (d j) (a j)).coeff (d i) from
     t5 (Polynomial.lcoeff k (d i)) _ _]
   rw [LO i]
   · exact Polynomial.coeff_monomial_same _ _
   · intro j _ hj
     exact Polynomial.coeff_monomial_of_ne _ (fun h=>hj (hd h.symm))
   · simp
 intro h
 change P=0 at h
 exact hi (by rw [← hc,h,Polynomial.coeff_zero])
private theorem bqr {a :Fin bf→cH} {i:Fin bf}
   (hi:a i≠0) :vk (qK ∘ a) (B7.KT adE 0)≠0:= by
 classical
 have hne :JC a≠0 :=
   eM7 (fun j:Fin bf=>j.val) Fin.val_injective a hi
 have hinj:sI aHY :=
   (c9 dF abB).injective.comp (zi _ _)
 have hval :vk (qK ∘ a) (B7.KT adE 0) =
     aHY (JC a) := by
   unfold B7.KT JC
   rw [t5 ,t5]
   refine vw rfl fun j _ => ?_
   rw [← zoT]
   simp only [nI,aeval_C,Dw ,Nat.choose_zero_right,G8 ,ze,
     Nat.sub_zero,G7,qK,aHY,x7,
     adE,t8 ,v9]
 rw [hval]
 exact fun h=>hne (hinj (h.trans aHY.map_zero.symm))
theorem ed6 (Q:Bk)
  (hd: (u9 Q).natDegree=1) :
  ahc (gN Q) (B7.KT adE 0) := by
 apply bPG (K:=abB) _ (b6H 0)
 intro x hx hval
 funext i
 change x i=0
 by_contra hi
 letI:t7 cH abB:=qK.toAlgebra
 let b:Fin bf→abB:= fun j=>(x i)⁻¹*x j
 have hb:b∈Gk abB (KL Q i) :=aOX Q hx hi
 choose a ha using fun j=>a4a (KL Q i)
  (bmo Q hd i) hb j
 have he :qK ∘ a=b:=funext ha
 have hai:a i≠0:= by
  intro ha₀
  have hz :=ha i
  change qK (a i)=(x i)⁻¹*x i at hz
  rw [ha₀,p5 ,Re hi] at hz
  exact zero_ne_one hz
 apply bqr hai
 rw [he]
 exact dsn (σ:=Fin bf) x ((x i)⁻¹) (b6H 0) hval
end
end YT
end
section
set_option maxHeartbeats 800000
namespace czp
noncomputable section
open MM aFU IsDedekindDomain
open scoped WithZero IntermediateField.algebraAdjoinAdjoin
variable {F K:Type} [lz F] [lz K] [t7 F K]
private theorem adjoin_inv (x :K) :
    EK F ({x⁻¹} : Set K)=EK F {x} := by
  apply vj <;> apply IntermediateField.adjoin_le_iff.mpr
  · exact Set.singleton_subset_iff.mpr
      (IntermediateField.inv_mem _ (zl2 F x))
  · apply Set.singleton_subset_iff.mpr
    change x∈EK F ({x⁻¹} : Set K)
    simpa only [inv_inv] using
      (EK F ({x⁻¹} : Set K)).inv_mem
        (zl2 F x⁻¹)
private theorem cb8 {x :K} (w:zZ F K) (h:w.val x≤1) :
   Av w x=0:= by
 by_cases hx :w.val x=0
 · simp [Av,hx]
 have hlog:=(WithZero.log_le_log hx one_ne_zero).mpr h
 rw [WithZero.log_one] at hlog
 unfold Av
 omega
private theorem cu7 {v w:Valuation K ℤᵐ⁰}
    (hv :vZ v) (hw:vZ w) (h:v.IsEquiv w) :
    v=w:= by
  open WithZero in
  have hsmall {z :ℤᵐ⁰} (hz :z<1) :z≤exp (-1 :ℤ) := by
    apply (lt_mul_exp_iff_le (y :=exp (-1 :ℤ)) exp_ne_zero).mp
    simpa only [← exp_add,neg_add_cancel,exp_zero] using hz
  obtain ⟨π,hπ⟩:=hv (MS (-1 :ℤ))
  obtain ⟨τ,hτ⟩:=hw (MS (-1 :ℤ))
  have hπw:w π=MS (-1 :ℤ) := by
    apply vj
    · apply hsmall
      apply h.lt_one_iff_lt_one.mp
      simp [hπ]
    · rw [← hτ,← h.le_iff_le,hπ]
      apply hsmall
      apply h.lt_one_iff_lt_one.mpr
      simp [hτ]
  ext a
  by_cases ha :a=0
  · simp [ha]
  · have hpow (u:Valuation K ℤᵐ⁰) (hu:u π=MS (-1 :ℤ)) :
        u (π^(-WithZero.log (v a)))=v a := by
      rw [map_zpow₀,hu,← WithZero.exp_zsmul]
      have hs : (-WithZero.log (v a))•(-1 :ℤ)=WithZero.log (v a) := by simp
      rw [hs,WithZero.exp_log (v.ne_zero_iff.mpr ha)]
    exact (hpow w hπw).symm.trans (h.eq_iff.mp (hpow v hπ))
section Chart
variable {t:K}
local notation "A" => DT F K t
local notation "B" => DR F K t
local notation "p" => origin F K t
private abbrev parameter :A:=⟨t,Algebra.self_mem_adjoin_singleton F t⟩
private def bJ5 (ht:wY F t) : (A ⧸ p) ≃ₐ[F] F:= by
  let e :=Polynomial.algEquivOfTranscendental F t ht
  refine (Ideal.quotientEquivAlg (lI {p9}) p e ?_).symm.trans ?_
  · rw [qy ,G5]
    unfold origin
    change lI {parameter} = lI {e p9}
    simp only [e,parameter,Polynomial.algEquivOfTranscendental_apply_X]
  · rw [show (lI {p9} : cy (ox F)) =
        lI {p9-Polynomial.C (0:F)} by rw [p5 ,Kc]]
    exact Polynomial.quotientSpanXSubCAlgEquiv (0:F)
private theorem bW3 (w:zZ F K) (hw:w.val t<1) (a :A) :
   w.val (c9 A K a)≤1 := by
 obtain ⟨a,ha⟩:=a
 change w.val a≤1
 induction ha using Algebra.adjoin_induction with
 | mem y hy =>
   obtain rfl :=Set.mem_singleton_iff.mp hy
   exact hw.le
 | algebraMap c =>
   by_cases hc:c=0
   · simp [hc]
   · exact (w.trivial c hc).le
 | add a b ha hb hwa hwb =>
   exact (w.val.map_add _ _).trans (max_le hwa hwb)
 | mul a b ha hb hwa hwb =>
   rw [nI]
   exact mul_le_one' hwa hwb
private theorem a6a (w:zZ F K) (hw:w.val t<1) (b:B) :
  w.val (c9 B K b)≤1 := by
 let O:=w.val.valuationSubring
 let f :A →+* O:=(c9 A K).codRestrict O.toSubring (bW3 w hw)
 let:t7 A O:=f.toAlgebra
 let:IsScalarTower A O K:=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
 have hb:Mz O (b.val :K) :=IsIntegral.tower_top b.property
 exact (Valuation.valuationSubring.integers w.val).isIntegral_iff_v_le_one.mp hb
private def RG (w:zZ F K) (hw:w.val t<1) :B →ₐ[F] w.val.valuationSubring :=
 { (c9 B K).codRestrict w.val.valuationSubring.toSubring
     (a6a w hw) with
   commutes' := fun c=>u8 ((Pr F B K c).symm) }
private def bLp (w:zZ F K) (hw:w.val t<1) :
   B →ₐ[F] Lf w.val.valuationSubring :=
 (XJ F w.val.valuationSubring _).comp (RG w hw)
private def bcf (w:zZ F K) (hw:w.val t<1) :cy B :=
 nX (bLp w hw)
private theorem bsy (w:zZ F K) (hw:w.val t<1) (b:B) :
  b∈bcf w hw↔w.val (c9 B K b)<1 := by
 change SL _ (RG w hw b)=0↔_
 rw [IsLocalRing.residue_eq_zero_iff]
 exact w.val.mem_maximalIdeal_iff
private def center (ht:wY F t) (w:zZ F K) (hw:w.val t<1) :
  Ideal.primesOver p B:= by
 let P:=bcf w hw
 have :P.IsPrime :=zgL (bLp w hw).toRingHom
 refine ⟨P,Ea ,⟨(a6k ht).eq_of_le
  (Ideal.IsPrime.ne_top Ea) ?_⟩⟩
 change lI {parameter} ≤ P.under A
 apply (yJ _).mpr
 change c9 A B parameter∈bcf w hw
 exact (bsy w hw _).mpr hw
private theorem cUV (ht:wY F t) :
  c9 A B parameter≠0:= by
 intro h
 exact ht.ne_zero (oq Np h)
private def aDm (ht:wY F t) (P:Gj p B) :
  HeightOneSpectrum B:= by
 have :P.val.LiesOver p:=P.property.2
 refine ⟨P.val,P.property.1,?_⟩
 intro h
 have hmem:c9 A B parameter∈P.val :=
  (P.val.mem_of_liesOver p _).mp (WD _)
 rw [h,TH] at hmem
 exact cUV ht hmem
variable [PA (DR F K t)] [IsFractionRing (DR F K t) K]
private theorem bci (ht:wY F t) (w:zZ F K) (hw:w.val t<1) :
    (aDm ht (center ht w hw)).valuation K=w.val := by
  let v :=aDm ht (center ht w hw)
  have hbelow:v.valuationSubringAtPrime K≤w.val.valuationSubring := by
    intro y hy
    rw [v.valuationSubringAtPrime_eq_valuationSubring] at hy
    obtain ⟨a,s,hs⟩:=v.exists_primeCompl_mul_eq_of_integer y hy
    have hsV:w.val (c9 B K s)=1 :=
      vj (a6a w hw s)
        (le_of_not_gt fun h=>s.property ((bsy w hw s).mpr h))
    change w.val y≤1
    have hval :=oq (fun b:K=>w.val b) hs
    rw [nI,hsV,zg] at hval
    exact hval.trans_le (a6a w hw a)
  have hproper :w.val.valuationSubring ≠ ⊤ := by
    rw [ne_eq,Valuation.valuationSubring_eq_top_iff,not_not]
    exact (Valuation.isNontrivial_iff_exists_lt_one w.val).mpr ⟨t,ht.ne_zero,hw⟩
  have hring :=(v.valuationSubringAtPrime_eq_valuationSubring (K:=K)).symm.trans
    (ValuationSubring.eq_of_le_of_ne_top _ hbelow hproper)
  exact cu7 (v.valuation_surjective K) w.surj
    ((Valuation.isEquiv_iff_valuationSubring (v.valuation K) w.val).mpr hring)
private theorem dGy (ht:wY F t) :
  sI (fun w : {w:zZ F K // w.val t<1} => center ht w.1 w.2) := by
 rintro ⟨w,hw⟩ ⟨v,hv⟩ h
 apply u8
 have he :=oq (fun P:Gj p B=>(aDm ht P).valuation K) h
 rw [bci ht w hw,bci ht v hv] at he
 cases w
 cases v
 cases he
 rfl
private theorem dGz (ht:wY F t) (w:zZ F K) (hw:w.val t<1) :
  (-WithZero.log (w.val t)).toNat=(center ht w hw).val.ramificationIdx A:= by
 let P:=center ht w hw
 have :P.val.IsPrime :=P.property.1
 have :P.val.LiesOver p:=P.property.2
 let v :=aDm ht P
 let b:B:=c9 A B parameter
 have hb:b≠0:=cUV ht
 have hspan:Ideal.map (c9 A B) p=lI {b} := by
  simp only [origin,qy ,G5 ,b,parameter]
 have hmap :Ideal.map (c9 A B) p ≠ ⊥ := by
  rw [hspan,ne_eq,Ideal.span_singleton_eq_bot]
  exact hb
 change (-WithZero.log (w.val t)).toNat=P.val.ramificationIdx A
 rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P.val hmap,hspan]
 rw [← bci ht w hw]
 change (-WithZero.log (v.valuation K (c9 B K b))).toNat =
  multiplicity v.asIdeal (lI {b})
 simp only [v.valuation_of_algebraMap,v.intValuation_eq_exp_neg_multiplicity hb,
  WithZero.log_exp,neg_neg,zQg]
private theorem fWL (ht:wY F t)
  (w:zZ F K) (hw:w.val t<1) :vZ (bLp w hw) := by
 let P:=center ht w hw
 have :P.val.LiesOver p:=P.property.2
 have :RP p:=a6k ht
 have :P.val.IsMaximal:=zvA P.val p
 let v :=aDm ht P
 let f :=bLp w hw
 let e : (B ⧸ P.val) →ₐ[F] Lf w.val.valuationSubring :=
  Ideal.kerLiftAlg f
 let:lz (B ⧸ P.val) :=Ideal.Quotient.field P.val
 intro y
 obtain ⟨a,rfl⟩:=IsLocalRing.residue_surjective (R:=w.val.valuationSubring) y
 have ha :v.valuation K (a :K)≤1 := by
  rw [bci ht w hw]
  exact a.property
 obtain ⟨b,d,hbd⟩:=v.exists_primeCompl_mul_eq_of_integer (a :K) ha
 have hd:oy P.val (d:B)≠0 :=
  fun h=>d.property (Ideal.Quotient.eq_zero_iff_mem.mp h)
 obtain ⟨z,hz⟩:=zf ((oy P.val (d:B))⁻¹)
 have hdz :f (d:B)*f z=1 := by
  change e (oy P.val (d:B))*e (oy P.val z)=1
  rw [← nI,hz,mul_inv_cancel₀ hd,map_one]
 have hmul :a*RG w hw d=RG w hw b:=u8 hbd
 have hres :=oq (SL w.val.valuationSubring) hmul
 rw [nI] at hres
 change SL _ a*f d=f b at hres
 refine ⟨b*z,?_⟩
 change f (b*z)= _
 rw [nI,← hres,xI,hdz,zg]
private theorem dGB (ht:wY F t)
  (w:zZ F K) (hw:w.val t<1) :
  QZ w=(center ht w hw).val.inertiaDeg A:= by
 let P:=center ht w hw
 have :P.val.LiesOver p:=P.property.2
 have :RP p:=a6k ht
 have :P.val.IsMaximal:=zvA P.val p
 let e : (B ⧸ P.val) ≃ₐ[F] Lf w.val.valuationSubring :=
  X4 (fWL ht w hw)
 change oz F (Lf w.val.valuationSubring)=P.val.inertiaDeg A
 rw [← e.toLinearEquiv.finrank_eq,Ideal.inertiaDeg_eq_of_isMaximal p P.val]
 let e₀:=(bJ5 ht).symm
 apply Algebra.finrank_eq_of_equiv_equiv e₀.toRingEquiv (RingEquiv.refl (B ⧸ P.val))
 apply yL
 intro c
 change c9 (A ⧸ p) (B ⧸ P.val) (e₀ c)=c9 F (B ⧸ P.val) c
 have he₀:e₀ c=c9 F (A ⧸ p) c:= by
  simpa only [Algebra.algebraMap_self_apply] using e₀.commutes c
 rw [he₀,← Pr F (A ⧸ p) (B ⧸ P.val)]
end Chart
theorem proof :MM.c8:= by
  classical
  intro F K _ _ _ x S hx
  let t:=x⁻¹
  have ht:wY F t:= fun hi=>hx.1 (IsAlgebraic.inv_iff.mp hi)
  let A:=DT F K t
  let B:=DR F K t
  let L:=EK F ({t} : Set K)
  let p:=origin F K t
  have hL:L=EK F ({x} : Set K) :=adjoin_inv x
  have :ov L K:=hL.symm ▸ hx.2.1
  have :Algebra.IsSeparable L K:=hL.symm ▸ hx.2.2
  have :IsPrincipalIdealRing A:=bKh ht
  have :zYo A K := .trans_faithfulSMul A L K
  have :Module.Free A B:=IsIntegralClosure.module_free A L K B
  have :ov A B:=IsIntegralClosure.finite A L K B
  have :PA B:=IsIntegralClosure.isDedekindDomain A L K B
  have :IsFractionRing B K:=integralClosure.isFractionRing_of_finite_extension L K
  have :RP p:=a6k ht
  have :p.IsPrime :=Ideal.IsMaximal.isPrime Ea
  let T:=S.subtype (fun w:zZ F K=>w.val t<1)
  let centerOf : {w:zZ F K // w.val t<1} ↪ (Gj p B) :=
    ⟨fun w=>center ht w.val w.property,dGy ht⟩
  let weight (P:Gj p B) :=P.val.ramificationIdx A*P.val.inertiaDeg A
  calc
    af8 S x = ∑ w∈T,QZ w.val*Av w.val x := by
      dsimp only [T]
      rw [Finset.sum_subtype_eq_sum_filter (fun w:zZ F K=>QZ w*Av w x)]
      unfold af8
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro w hwS hw
      have h:w.val x≤1 := by
        by_contra! h
        exact hw (Finset.mem_filter.mpr ⟨hwS,by
          change w.val x⁻¹<1
          rw [map_inv₀]
          exact inv_lt_one_of_one_lt₀ h⟩)
      simp [cb8 w h]
    _ = ∑ P∈T.map centerOf,weight P:= by
      rw [Finset.sum_map]
      apply vw rfl
      intro w _
      have ho:=dGz ht w.val w.property
      have hlog: (-WithZero.log (w.val.val t)).toNat=Av w.val x := by
        simp [t,Av,map_inv₀,WithZero.log_inv]
      rw [hlog] at ho
      change _=weight (center ht w.val w.property)
      rw [dGB ht w.val w.property,ho]
      exact Nat.mul_comm _ _
    _ ≤ ∑ P:Gj p B,weight P :=
      zlp (Finset.subset_univ _) (fun _ _ _=>In _)
    _=oz A B:=Ideal.sum_ramification_inertia_eq_finrank p B
    _=oz L K:=IsIntegralClosure.rank A L K B
    _ = _:=oq (fun M:IntermediateField F K=>oz M K) hL
end
end czp
end
section
namespace lB
noncomputable section
open Polynomial K1 aR dN wH
def c1 :Prop :=
  ∀ p h:aU,bF p→bF h →
    ∀ f g u v :nq,yy f p→yy g p→yy u h→yy v h →
      ∀ points :vh KE,
        (∀ y∈points,aKn f g u v y) →
        32*points.card≤ iH p p h h
def c2 :Prop :=
  ∀ f g:nq,f≠0→ g≠0→ IsRelPrime f g →
    ∀ (C:GR) (d:ℕ),cAp f g C d →
      ∀ (Γ:vh K) (s :K→K[X]),Set.InjOn s (Γ:Set K) →
        (∀ γ∈Γ,(s γ).natDegree≤133671 ∧
          An (extend (s γ)) f=0∧An (extend (s γ)) g=0 ∧
          C.aay (extend (s γ))) →
        ∃ B:DA Γ,Γ⊆B.union∧B.uG s ∧
          (∀ i,0<B.degree i)∧B.total≤d
end
end lB
end
section
namespace YV
open aR dN lB MeasureTheory
open scoped Pointwise
def c1 :Prop :=
  ∀ p h:aU,bF p→bF h →
    ∀ f g u v :nq,bbu f (cap p)→bbu g (cap p) →
      bbu u (cap h)→bbu v (cap h) →
      ∀ points :vh KE,
        (∀ y∈points,aKn f g u v y ∧ ∀ i,y i≠0) →
        (points.card:ℝ)≤avz (cap p) (cap p) (cap h) (cap h)
def c2 :Prop :=
 ∀ p:aU,bF p→32*(oZ (cap p)).toReal=(Dn p:ℝ)
private theorem ase {F:Set M5→ℝ} {G:aU→ℤ}
  (heq : ∀ x :aU,bF x→32*F (cap x)=(G x :ℝ))
  {a :aU} (ha :bF a) (x :aU) (hx :bF x) :
  32*ahk F (cap a) (cap x)=(gI G a x :ℝ) := by
 rw [ahk,gI,Int.cast_sub,mul_sub,← anN hx ha,
  heq _ (Nc hx ha),heq _ hx]
theorem of_children (h1 :c1) (h2 :c2) :lB.c1 := by
 intro p h hp hh f g u v hf hg hu hv points hpts
 obtain ⟨f',g',u',v',hf',hg',hu',hv',points',hc,hpts'⟩ :=
   eD0 hf hg hu hv points hpts
 have hb:=h1 p h hp hh f' g' u' v' (bxf hf') (bxf hg')
   (bxf hu') (bxf hv') points' hpts'
 rw [hc] at hb
 have hfirst:=ase (F:= fun P=>(oZ P).toReal) (G:=Dn) h2 hp
 have hm:=ase (ase (ase hfirst hp) hh) hh
     ⟨0,0,0⟩ (⟨by decide,by decide⟩:bF ⟨0,0,0⟩)
 rw [auw] at hm
 change 32*avz (cap p) (cap p) (cap h) (cap h)= _ at hm
 have hcast:=y5 hb (by norm_num : (0:ℝ)≤32)
 rw [hm] at hcast
 have hz : (↑(32*points.card) :ℤ) ≤
     gI (gI (gI (gI Dn p) p) h) h ⟨0,0,0⟩:= by
   exact_mod_cast hcast
 simpa only [iH,zQg] using Int.toNat_le_toNat hz
end YV
end
section
namespace XT
noncomputable section
open aR dN lB YV MvPolynomial
open scoped Pointwise
abbrev Exponent:=Fin 4 →₀ ℕ
abbrev GG:=Fin 4→ℕ
def lattice (p:aU) :Set Exponent :=
 {e | e 0+e 1+e 2+e 3≤p.b∧e 1+2*e 2 + 3*e 3≤p.j∧e 3≤p.t}
def aza (A:Fin 4→Set Exponent) (B:Set Exponent)
    (b:ℕ) (w:GG) :Set Exponent :=
  (((b•B+w 0•A 0)+w 1•A 1)+w 2•A 2)+w 3•A 3
def admissible (A:Fin 4→Set Exponent) (B:Set Exponent) :Prop :=
  (∀ i,(A i).Finite∧0∈A i)∧B.Finite∧0∈B ∧
    ∀ i:Fin 4,S1 i 1∈B
abbrev W3 (P:cy nq) :ℕ:=(u9 P).natDegree
def lO (A:Fin 4→Set Exponent) (B:Set Exponent) (P:cy nq)
    (b:ℕ) (w:GG) :ℝ :=
  oz qG ((restrictSupport qG (aza A B b w)).map
    (zh qG P).toLinearMap)
def ZH (F:GG→ℝ) (i:Fin 4) (step:ℕ) (w:GG) :ℝ :=
 F (w+Pi.single i step)-F w
def afK (dirs :List (Fin 4)) (step:ℕ) (F:GG→ℝ) :GG→ℝ :=
 dirs.foldl (fun H i=>ZH H i step) F
def acC (k :ℕ) :List (Fin 4) :=
 (List.finRange 4).drop k
def aAV (A:Fin 4→Set Exponent) (B:Set Exponent)
    (P:cy nq) (k :ℕ) (d:ℝ) :Prop :=
  ∃ N :ℕ,∀ b w step,N≤b→(∀ i,N≤w i) →
    afK (acC k) step (lO A B P b) w =
      (step:ℝ)^(4 - k)*d
abbrev oF (y :KE) :cy GeoJets :=nX (Gn y)
end
end XT
end
section
namespace XT
open aR dN lB YV MvPolynomial
open scoped Pointwise
theorem apr {p q:aU} (hb:p.b=q.b) (hj:p.j=q.j) (ht:p.t=q.t) :p=q:= by
 cases p
 cases q
 simp_all
theorem BP {p:aU} (hp:bF p) (k :ℕ) :bF (p.scale k) := by
 exact ⟨HZ k hp.1,by
  simpa only [t6,Gr 3 k] using HZ k hp.2⟩
theorem b7j (p:aU) :0∈lattice p:= by simp [lattice]
theorem aON {e :Exponent} {p:aU} :
   e∈lattice p↔(fun i=>(e i:ℝ))∈cap p:= by
 change (e 0+e 1+e 2+e 3≤p.b∧e 1+2*e 2 + 3*e 3≤p.j∧e 3≤p.t) ↔
   (∀ i:Fin 4,0≤(e i:ℝ))∧(e 0:ℝ)+e 1+e 2+e 3≤p.b ∧
     (e 1 :ℝ)+2*e 2 + 3*e 3≤p.j∧(e 3:ℝ)≤p.t
 constructor
 · intro ⟨hb,hj,ht⟩
   exact ⟨fun _=>Nat.cast_nonneg _,by exact_mod_cast hb,by exact_mod_cast hj,
     by exact_mod_cast ht⟩
 · intro ⟨_,hb,hj,ht⟩
   exact ⟨by exact_mod_cast hb,by exact_mod_cast hj,by exact_mod_cast ht⟩
theorem afS (p:aU) : (lattice p).Finite := by
 have hbound (e :lattice p) (i:Fin 4) :e.val i<p.b+1 := by
   have hb:e.val 0+e.val 1+e.val 2+e.val 3≤p.b:=e.property.1
   fin_cases i
   · change e.val 0<p.b+1
     omega
   · change e.val 1<p.b+1
     omega
   · change e.val 2<p.b+1
     omega
   · change e.val 3<p.b+1
     omega
 let f (e :lattice p) (i:Fin 4) :Fin (p.b+1) :=⟨e.val i,hbound e i⟩
 let:Finite (lattice p) :=Finite.of_injective f (by
   intro a b h
   apply u8
   ext i
   exact oq (fun z :Fin 4→Fin (p.b+1)=>(z i).val) h)
 exact Set.toFinite _
theorem bOm {p:aU} {f :nq} (hf :bbu f (cap p)) :
  ((f^2).support :Set Exponent)⊆lattice (p.scale 2) := by
 classical
 intro e he
 rw [pow_two] at he
 have h:=support_mul f f he
 obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp h
 have ⟨hab,haj,hat⟩:=aON.mpr (hf a ha)
 have ⟨hbb,hbj,hbt⟩:=aON.mpr (hf b hb)
 change _≤2*p.b∧_≤2*p.j∧_≤2*p.t
 simp only [J4]
 exact ⟨by omega,by omega,by omega⟩
private theorem dfj {x y A B:ℕ} (he :A % 2=0)
   (h:x+2*y≤A+B) :
   ∃ u v :ℕ,u≤x∧v≤y∧u+2*v≤A∧(x - u)+2*(y - v)≤B:= by
 let v :=min y (A/2)
 let u:=min x (A - 2*v)
 have hv :v≤A/2 :=JK _ _
 have hu:u≤A - 2*v :=JK _ _
 refine ⟨u,v,Kz _ _,Kz _ _,by omega,?_⟩
 rcases GF y (A/2) with hsmall | hlarge
 · have hyv :v=y :=GB hsmall
   rcases GF x (A - 2*v) with hsmall' | hlarge'
   · have hxu:u=x :=GB hsmall'
     omega
   · have hxu:u=A - 2*v :=GY hlarge'
     omega
 · have hyv :v=A/2 :=GY hlarge
   omega
private theorem gui {x y A B:ℕ} (he :A % 2=0∨B % 2=0)
   (h:x+2*y≤A+B) :
   ∃ u v :ℕ,u≤x∧v≤y∧u+2*v≤A∧(x - u)+2*(y - v)≤B:= by
 rcases he with he | he
 · exact dfj he h
 · obtain ⟨u,v,hu,hv,hB,hA⟩:=dfj he (show x+2*y≤B+A by omega)
   exact ⟨x - u,y - v,by omega,by omega,hA,by omega⟩
theorem aOn {p q:aU} (hp:bF p) (hq:bF q) :
    lattice ((p.plus q).scale 2)=lattice (p.scale 2)+lattice (q.scale 2) := by
  apply zkG
  · intro e he
    have ⟨hb,hj,ht⟩:e 0+e 1+e 2+e 3≤2*(p.b+q.b) ∧
        e 1+2*e 2 + 3*e 3≤2*(p.j+q.j)∧e 3≤2*(p.t+q.t) :=he
    simp only [t6,vi] at hb hj ht
    let z :=min (e 3) (2*p.t)
    let w:=e 3 - z
    have hz₁:z≤e 3:=Kz _ _
    have hz₂:z≤2*p.t:=JK _ _
    have hw:w≤2*q.t:= by
      rcases GF (e 3) (2*p.t) with hh | hh
      · have hz :z=e 3:=GB hh
        dsimp only [w]
        omega
      · have hz :z=2*p.t:=GY hh
        dsimp only [w]
        omega
    let A:=2*p.j-3*z
    let B:=2*q.j-3*w
    have hp₁:=hp.1
    have hp₂:=hp.2
    have hq₁:=hq.1
    have hq₂:=hq.2
    have hsplit :e 1+2*e 2≤A+B:= by dsimp only [A,B,w]; omega
    have hpar :A % 2=0∨B % 2=0:= by
      rcases GF (e 3) (2*p.t) with hh | hh
      · have hz :z=e 3:=GB hh
        right
        dsimp only [B,w]
        omega
      · have hz :z=2*p.t:=GY hh
        left
        dsimp only [A]
        omega
    obtain ⟨x,y,hx,hy,hxy,hxy'⟩:=gui hpar hsplit
    have hleft:x+y+z≤2*p.b:= by dsimp only [A] at hxy; omega
    have hright: (e 1 - x)+(e 2 - y)+w≤2*q.b:= by dsimp only [B] at hxy'; omega
    let a₀:=min (e 0) (2*p.b - x - y - z)
    have ha₀:a₀≤e 0:=Kz _ _
    have ha₀' : a₀≤2*p.b - x - y - z :=JK _ _
    have hsum: (e 0-a₀)+(e 1 - x)+(e 2 - y)+w≤2*q.b:= by
      rcases GF (e 0) (2*p.b - x - y - z) with hh | hh
      · have heq :a₀=e 0:=GB hh
        omega
      · have heq :a₀=2*p.b - x - y - z :=GY hh
        dsimp only [w] at *
        omega
    let a :Exponent:=Finsupp.equivFunOnFinite.symm ![a₀,x,y,z]
    let b:Exponent:=Finsupp.equivFunOnFinite.symm ![e 0-a₀,e 1 - x,e 2 - y,w]
    apply Set.mem_add.mpr
    refine ⟨a,?_,b,?_,?_⟩
    · change a₀ + x+y+z≤2*p.b∧x+2*y+3*z≤2*p.j∧z≤2*p.t
      dsimp only [A] at hxy
      exact ⟨by omega,by omega,hz₂⟩
    · change (e 0-a₀)+(e 1 - x)+(e 2 - y)+w≤2*q.b ∧
        (e 1 - x)+2*(e 2 - y)+3*w≤2*q.j∧w≤2*q.t
      dsimp only [B] at hxy'
      exact ⟨hsum,by omega,hw⟩
    · ext i
      simp only [J4]
      fin_cases i
      · change a₀+(e 0-a₀)=e 0
        omega
      · change x+(e 1 - x)=e 1
        omega
      · change y+(e 2 - y)=e 2
        omega
      · change z+w=e 3
        dsimp only [w]
        omega
  · intro e he
    obtain ⟨a,⟨ha₁,ha₂,ha₃⟩,b,⟨hb₁,hb₂,hb₃⟩,rfl⟩:=Set.mem_add.mp he
    simp only [t6] at ha₁ ha₂ ha₃ hb₁ hb₂ hb₃
    change _≤2*(p.b+q.b)∧_≤2*(p.j+q.j)∧_≤2*(p.t+q.t)
    simp only [J4]
    exact ⟨by omega,by omega,by omega⟩
private theorem b7i:lattice ⟨0,0,0⟩=0:= by
 ext e
 change e∈lattice ⟨0,0,0⟩↔e=0
 constructor
 · intro he
   have h:=aON.mp he
   rw [auw] at h
   have hz : (fun i=>(e i:ℝ))=0:=h
   ext i
   change e i=0
   have hi: (e i:ℝ)=0:=congrFun hz i
   exact_mod_cast hi
 · rintro rfl
   exact b7j _
theorem brC {p:aU} (hp:bF p) (n:ℕ) :
   n•lattice (p.scale 2)=lattice ((p.scale n).scale 2) := by
 induction n with
 | zero =>
     rw [zero_nsmul,← b7i]
     congr 1
     apply apr <;> simp [t6]
 | succ n ih =>
     rw [C5 ,ih,← aOn (BP hp n) hp]
     congr 1
     apply apr <;> simp [t6,vi ,Nat.add_mul]
def aqO:Shape :=⟨3, 3,1⟩
theorem cCw:bF aqO:= by norm_num [bF,aqO]
theorem dER (S:Fin 4→aU) :
  admissible (fun i=>lattice ((S i).scale 2)) (lattice (aqO.scale 2)) := by
 refine ⟨fun _=>⟨afS _,b7j _⟩,afS _,
  b7j _,?_⟩
 intro i
 fin_cases i <;> norm_num [lattice,aqO,t6,Finsupp.single_apply]
end XT
end
section
namespace XT
noncomputable section
open aR YV MeasureTheory Filter
open scoped Pointwise Topology
private def Ui (b j t:ℝ) :Set M5 :=
 {x | (∀ i,0≤x i)∧x 0 + x 1 + x 2 + x 3≤b ∧
   x 1+2*x 2 + 3*x 3≤j∧x 3≤t}
private theorem ceN (b j t:ℝ) :yQ (Ui b j t) := by
 have hnonneg:yQ {x :M5 | ∀ i,0≤x i} := by
  rw [show {x :M5 | ∀ i,0≤x i} = ⋂ i:Fin 4,{x | 0≤x i} by
   ext x; simp]
  exact isClosed_iInter fun i=>z9 Kp (continuous_apply i)
 have hb:yQ {x :M5 | x 0 + x 1 + x 2 + x 3≤b} :=
  z9 (by fun_prop) Kp
 have hj:yQ {x :M5 | x 1+2*x 2 + 3*x 3≤j} :=
  z9 (by fun_prop) Kp
 have ht:yQ {x :M5 | x 3≤t} := z9 (continuous_apply _) Kp
 exact hnonneg.inter (hb.inter (hj.inter ht))
private theorem buM (b j t:ℝ) :IsCompact (Ui b j t) := by
 apply isCompact_Icc.of_isClosed_subset (ceN b j t)
   (t:=Ui b j t) (s :=Set.Icc (0:M5) (fun _=>b))
 intro x hx
 obtain ⟨hx,hxb,_,_⟩:=hx
 refine ⟨hx,fun i => ?_⟩
 have h₀:=hx 0
 have h₁:=hx 1
 have h₂:=hx 2
 have h₃:=hx 3
 change x i≤b
 fin_cases i
 · change x 0≤b
   linarith
 · change x 1≤b
   linarith
 · change x 2≤b
   linarith
 · change x 3≤b
   linarith
private theorem fUl (b j t:ℝ) :Convex ℝ (Ui b j t) := by
 intro x hx y hy a c ha hc hac
 obtain ⟨hx,hxb,hxj,hxt⟩:=hx
 obtain ⟨hy,hyb,hyj,hyt⟩:=hy
 change (∀ i,0≤(a•x+c•y) i)∧_∧_∧_
 simp only [Qy ,FQ,G1]
 refine ⟨fun i=>add_nonneg (NW ha (hx i)) (NW hc (hy i)),?_,?_,?_⟩
 · nlinarith [y5 hxb ha,y5 hyb hc,
    oq (fun z :ℝ=>z*b) hac]
 · nlinarith [y5 hxj ha,y5 hyj hc,
    oq (fun z :ℝ=>z*j) hac]
 · nlinarith [y5 hxt ha,y5 hyt hc,
    oq (fun z :ℝ=>z*t) hac]
private def CJ (s offset :aU) (r :ℝ) :Set M5 :=
 Ui (s.b+r*offset.b) (s.j+r*offset.j) (s.t+r*offset.t)
private theorem bKc (s offset :aU) :Monotone (CJ s offset) := by
 intro r r' hr x hx
 obtain ⟨hx,hb,hj,ht⟩:=hx
 exact ⟨hx,hb.trans (by gcongr),hj.trans (by gcongr),ht.trans (by gcongr)⟩
private def dX (n:ℕ) :Set M5 :=
 (n:ℝ)⁻¹•(PM ℤ (uW (Pi.basisFun ℝ (Fin 4))) :Set M5)
private theorem cUl {E :Set M5} (hs :Bornology.IsBounded E) {n:ℕ} (hn:0<n) :
    (E∩dX n).Finite := by
  let L:=PM ℤ (uW (Pi.basisFun ℝ (Fin 4)))
  have hn0: (n:ℝ)≠0:= by positivity
  let e : ↑(E∩dX n) ≃ ↑((n:ℝ)•E∩(L:Set M5)) :=
    Equiv.subtypeEquiv (Equiv.smulRight hn0) (fun x=> by
      change (x∈E∧x∈(n:ℝ)⁻¹•(L:Set M5)) ↔
        ((n:ℝ)•x∈(n:ℝ)•E∧(n:ℝ)•x∈(L:Set M5))
      rw [Set.smul_mem_smul_set_iff₀ hn0,← Set.mem_inv_smul_set_iff₀ hn0])
  let:Finite ↑((n:ℝ)•E∩(L:Set M5)) :=(ZSpan.setFinite_inter _ (hs.smul₀ _)).to_subtype
  let:=Finite.of_equiv _ e.symm
  exact Set.toFinite _
private theorem fUm (b j t:ℝ) :
  t4 (fun n:ℕ=>((Ui b j t∩dX n).ncard:ℝ)/(n:ℝ)^4)
   qx (𝓝 (volume (Ui b j t)).toReal) := by
 simpa only [dX,Zt,Fintype.card_fin,measureReal_def] using
  tendsto_card_div_pow_atTop_volume (Ui b j t) (buM b j t).isBounded
   (ceN b j t).measurableSet ((fUl b j t).addHaar_frontier oZ)
private theorem cKU (s offset :aU) {n:ℕ} (hn:0<n) (e :Exponent) :
   (fun i=>(e i:ℝ)/(n:ℝ))∈CJ s offset (n:ℝ)⁻¹ ↔
     e∈lattice ((s.scale n).plus offset) := by
 have hn' : (0:ℝ)<n:= by exact_mod_cast hn
 have h (x c o:ℝ) :
     x/(n:ℝ)≤ c+(n:ℝ)⁻¹*o↔x≤(n:ℝ)*c+o:= by
   rw [div_le_iff₀ hn',add_mul,mul_right_comm ((n:ℝ)⁻¹) o (n:ℝ),
     Re hn'.ne',ze,v9 c (n:ℝ)]
 simp only [CJ,Ui,lattice,t6,vi ,Mw ,
   ← mul_div_assoc,← add_div,h]
 constructor
 · intro ⟨_,hb,hj,ht⟩
   exact ⟨by exact_mod_cast hb,by exact_mod_cast hj,by exact_mod_cast ht⟩
 · intro ⟨hb,hj,ht⟩
   exact ⟨fun _=> by positivity,by exact_mod_cast hb,by exact_mod_cast hj,
     by exact_mod_cast ht⟩
private theorem cIt (s offset :aU) {n:ℕ} (hn:0<n) :
    (lattice ((s.scale n).plus offset)).ncard =
      (CJ s offset (n:ℝ)⁻¹∩dX n).ncard:= by
  classical
  let:NeZero n:=⟨hn.ne'⟩
  have hn' : (0:ℝ)<n:= by exact_mod_cast hn
  let f (e :lattice ((s.scale n).plus offset)) : ↑(CJ s offset (n:ℝ)⁻¹∩dX n) :=
    ⟨fun i=>(e.val i:ℝ)/(n:ℝ),
     (cKU s offset hn e.val).mpr e.property,
     BoxIntegral.unitPartition.mem_smul_span_iff.mpr (fun i=>⟨(e.val i:ℤ),by
       simp [v9 (n:ℝ),hn'.ne']⟩)⟩
  have hi:sI f := by
    intro e e' he
    apply u8
    ext i
    have hv : (e.val i:ℝ)/(n:ℝ)=(e'.val i:ℝ)/(n:ℝ) :=
      congrFun (oq Np he) i
    exact_mod_cast (div_left_inj' hn'.ne').mp hv
  have hs :vZ f := by
    intro x
    have hx :=x.property.1
    have hx' : ∀ i:Fin 4,0≤x.val i:=hx.1
    have hgrid :=BoxIntegral.unitPartition.mem_smul_span_iff.mp x.property.2
    choose a ha using hgrid
    let e :Exponent:=Finsupp.equivFunOnFinite.symm (fun i=>(a i).toNat)
    have he (i:Fin 4) : (e i:ℝ)/(n:ℝ)=x.val i:= by
      have hz : (a i:ℝ)=(n:ℝ)*x.val i:=ha i
      have haz :0≤a i:= by exact_mod_cast (hz.symm ▸ NW hn'.le (hx' i))
      have hr : (e i:ℝ)=(a i:ℝ) := by
        change ((a i).toNat :ℝ)=(a i:ℝ)
        exact_mod_cast Int.toNat_of_nonneg haz
      rw [hr,hz,v9 (n:ℝ),WK _ hn'.ne']
    have hfun: (fun i=>(e i:ℝ)/(n:ℝ))=x.val :=funext he
    have hem:=(cKU s offset hn e).mp (hfun.symm ▸ hx)
    exact ⟨⟨e,hem⟩,u8 hfun⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)
private theorem eJo (s offset :aU) :
    t4 (fun m:ℕ=>(oZ (CJ s offset ((m:ℝ)+1)⁻¹)).toReal)
      qx (𝓝 (volume (cap s)).toReal) := by
  let r (m:ℕ) :ℝ:=((m:ℝ)+1)⁻¹
  let E (m:ℕ) :=CJ s offset (r m)
  have hr :t4 r qx (𝓝 0) := by
    simpa only [r,ZK,NZ,G8] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ)).comp (tendsto_add_atTop_nat 1)
  have hmono:Antitone E := by
    intro a b hab
    apply bKc
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hE : (⋂ m:ℕ,E m)=cap s := by
    ext x
    rw [Set.mem_iInter]
    constructor
    · intro hx
      have h (a :ℕ) :t4 (fun m=>r m*(a :ℝ)) qx (𝓝 0) := by
        simpa only [zero_mul] using hr.mul_const (a :ℝ)
      have hbound (a b:ℕ) :
          t4 (fun m=>(a :ℝ)+r m*(b:ℝ)) qx (𝓝 (a :ℝ)) := by
        simpa only [Fa] using (h b).const_add (a :ℝ)
      exact ⟨(hx 0).1,Sd (hbound s.b offset.b) (fun m=>(hx m).2.1),
        Sd (hbound s.j offset.j) (fun m=>(hx m).2.2.1),
        Sd (hbound s.t offset.t) (fun m=>(hx m).2.2.2)⟩
    · intro hx m
      have h₀:CJ s offset 0=cap s := by simp only [CJ,Ui,cap,zero_mul,Fa]
      exact bKc s offset (show 0≤ r m by positivity) (h₀.symm ▸ hx)
  have ht:=tendsto_measure_iInter_atTop (μ:=oZ)
    (s :=E) (fun m=>(ceN _ _ _).measurableSet.nullMeasurableSet)
    hmono ⟨0,(buM _ _ _).measure_ne_top⟩
  rw [hE] at ht
  have hfin:oZ (cap s) ≠ ⊤ := (buM _ _ _).measure_ne_top
  exact (ENNReal.continuousAt_toReal hfin).tendsto.comp ht
private theorem euM (s offset :aU) :
    t4 (fun n:ℕ=>((lattice ((s.scale n).plus offset)).ncard:ℝ)/(n:ℝ)^4)
      qx (𝓝 (volume (cap s)).toReal) := by
  let E :=CJ s offset
  have hpad:E 0=cap s := by simp only [E,CJ,Ui,cap,zero_mul,Fa]
  have h (r :ℝ) :t4 (fun n:ℕ=>((E r∩dX n).ncard:ℝ)/(n:ℝ)^4)
      qx (𝓝 (volume (E r)).toReal) :=fUm _ _ _
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hlow:=(tendsto_order.mp (h 0)).1 a (by simpa only [hpad] using ha)
    filter_upwards [hlow,eventually_gt_atTop 0] with n hn hn'
    rw [cIt s offset hn']
    refine hn.trans_le (zrZ ?_ (by positivity))
    exact_mod_cast XG
      (zSk _ (bKc s offset (by positivity :0≤(n:ℝ)⁻¹)))
      (cUl (buM _ _ _).isBounded hn')
  · intro a ha
    obtain ⟨m,hm⟩:=((tendsto_order.mp (eJo s offset)).2 a ha).exists
    have hhigh:=(tendsto_order.mp (h ((m:ℝ)+1)⁻¹)).2 a hm
    filter_upwards [hhigh,G0 (m+1)] with n hn hn'
    have hn0:0<n:= by omega
    rw [cIt s offset hn0]
    refine (zrZ ?_ (by positivity)).trans_lt hn
    have hge : ((m:ℝ)+1)≤n:= by exact_mod_cast hn'
    exact_mod_cast XG
      (zSk _ (bKc s offset
        (inv_anti₀ (by positivity) hge)))
      (cUl (buM _ _ _).isBounded hn0)
theorem euJ (s offset :aU) :
  t4 (fun m:ℕ=>((lattice ((s.scale (2*m)).plus offset)).ncard:ℝ) /
   (2*(m:ℝ))^4) qx (𝓝 (volume (cap s)).toReal) := by
 have h:t4 (fun m:ℕ=>2*m) qx atTop:= by
  apply tendsto_atTop.mpr
  intro b
  exact (G0 b).mono (fun m hm=> by omega)
 simpa only [ZK,NI,Sv] using (euM s offset).comp h
end
end XT
end
section
namespace XT
noncomputable section
open aR dN lB YV MvPolynomial MeasureTheory Filter
open scoped Pointwise Topology
private def xl (S:Fin 4→aU) (w:GG) :Shape :=
 ((((S 0).scale (w 0)).plus ((S 1).scale (w 1))).plus ((S 2).scale (w 2))).plus
   ((S 3).scale (w 3))
private theorem gwG {S:Fin 4→aU} (hS : ∀ i,bF (S i)) (w:GG) :
  bF (xl S w) :=
 Nc (Nc (Nc (BP (hS 0) _) (BP (hS 1) _))
  (BP (hS 2) _)) (BP (hS 3) _)
private theorem sum_zero (S:Fin 4→aU) :xl S 0=⟨0,0,0⟩:= by
 apply apr <;> simp [xl,vi ,t6]
private theorem bOA (S:Fin 4→aU) (w:GG) (i:Fin 4) :
  xl S (w+Pi.single i 1)=(xl S w).plus (S i) := by
 fin_cases i <;> apply apr <;>
  simp [xl,vi ,t6,Nat.add_mul] <;> ac_rfl
private theorem cT6 {S:Fin 4→aU} (hS : ∀ i,bF (S i)) (b:ℕ) (w:GG) :
   aza (fun i=>lattice ((S i).scale 2)) (lattice (aqO.scale 2)) b w =
     lattice (((aqO.scale b).plus (xl S w)).scale 2) := by
 have hB:=BP cCw b
 have h0:=BP (hS 0) (w 0)
 have h1 :=BP (hS 1) (w 1)
 have h2 :=BP (hS 2) (w 2)
 have h3:=BP (hS 3) (w 3)
 simp only [aza]
 rw [brC cCw,brC (hS 0),brC (hS 1),
   brC (hS 2),brC (hS 3),
   ← aOn hB h0,← aOn (Nc hB h0) h1,
   ← aOn (Nc (Nc hB h0) h1) h2,
   ← aOn (Nc (Nc (Nc hB h0) h1) h2) h3]
 congr 2
 apply apr <;> simp [xl,vi ,add_assoc]
private theorem eiV (S:Fin 4→aU) (b m:ℕ) (w x :GG) :
  ((aqO.scale b).plus (xl S (x+m•w))).scale 2 =
    ((xl S w).scale (2*m)).plus (((aqO.scale b).plus (xl S x)).scale 2) := by
 apply apr <;>
  simp [xl,vi ,t6,Qy ,R9] <;>
  ring
private theorem em6 {A:Fin 4→Set Exponent} {B:Set Exponent} {b:ℕ} {w:GG}
  (hfin: (aza A B b w).Finite) :
  lO A B ⊥ b w=((aza A B b w).ncard:ℝ) := by
 let e :=(AlgEquiv.quotientBot qG nq).symm.toLinearEquiv
 have he : (zh qG (⊥ : cy nq)).toLinearMap=e.toLinearMap:= by
  ext x
  rfl
 unfold lO
 rw [he,LinearEquiv.finrank_map_eq]
 let:=hfin.fintype
 rw [Module.finrank_eq_card_basis (basisRestrictSupport qG _),
  ← Nat.card_eq_fintype_card,Zt]
private theorem dE1 {S:Fin 4→aU} (hS : ∀ i,bF (S i)) (b:ℕ) (w:GG) :
   lO (fun i=>lattice ((S i).scale 2)) (lattice (aqO.scale 2)) ⊥ b w =
     ((lattice (((aqO.scale b).plus (xl S w)).scale 2)).ncard:ℝ) := by
 rw [em6,cT6 hS]
 rw [cT6 hS]
 exact afS _
private theorem gqy (x w:GG) (m:ℕ) (i:Fin 4) :
  (x+m•w)+Pi.single i m=x+m•(w+Pi.single i 1) := by
 have h:sH i m=m•(sH i 1 :GG) := by
  funext j
  by_cases he :j=i <;> simp [FQ,he]
 rw [h,nsmul_add,add_assoc]
private theorem gAV (dirs :List (Fin 4)) (x :GG)
   (F:ℕ→GG→ℝ) (G:GG→ℝ)
   (h : ∀ w:GG,t4 (fun m:ℕ=>F m (x+m•w)/(2*(m:ℝ))^4)
     qx (𝓝 (G w))) (w:GG) :
   t4 (fun m:ℕ =>
     afK dirs m (F m) (x+m•w)/(2*(m:ℝ))^4)
     qx (𝓝 (afK dirs 1 G w)) := by
 induction dirs generalizing F G with
 | nil=>exact h w
 | cons i dirs ih =>
     apply ih (fun m=>ZH (F m) i m) (ZH G i 1)
     intro y
     simp only [ZH,gqy,sub_div]
     exact (h (y+Pi.single i 1)).sub (h y)
private theorem dE0 {S:Fin 4→aU} (hS : ∀ i,bF (S i))
    (dirs :List (Fin 4)) (V:Set M5→ℝ) (w:GG) :
    afK dirs 1 (fun x=>V (cap (xl S x))) w =
      dirs.foldl (fun H i=>ahk H (cap (S i))) V (cap (xl S w)) := by
  induction dirs generalizing V with
  | nil=>rfl
  | cons i dirs ih =>
      have h:ZH (fun x=>V (cap (xl S x))) i 1 =
          fun x=>ahk V (cap (S i)) (cap (xl S x)) := by
        funext x
        rw [ZH,ahk,bOA,anN (gwG hS _) (hS i)]
      simp only [afK,List.foldl_cons,h]
      exact ih _
theorem dE7 {p h:aU} (hp:bF p) (hh:bF h)
   {d:ℝ}
   (hd:aAV (fun i=>lattice ((![p,p,h,h] i).scale 2))
     (lattice (aqO.scale 2)) ⊥ 0 d) :
   d/ 16=avz (cap p) (cap p) (cap h) (cap h) := by
 let S:Fin 4→Shape := ![p,p,h,h]
 have hS : ∀ i,bF (S i) := by intro i; fin_cases i <;> assumption
 obtain ⟨N,hd⟩:=hd
 let x :GG:= fun _=>N
 let F:GG→ℝ:=lO (fun i=>lattice ((S i).scale 2)) (lattice (aqO.scale 2)) ⊥ N
 let V:Set M5→ℝ:= fun Q=>(oZ Q).toReal
 have hF (w:GG) :t4 (fun m:ℕ=>F (x+m•w)/(2*(m:ℝ))^4)
     qx (𝓝 (V (cap (xl S w)))) := by
   have ht:=euJ (xl S w) (((aqO.scale N).plus (xl S x)).scale 2)
   simpa only [F,V,dE1 hS,eiV] using ht
 have ht:=gAV (acC 0) x (fun _=>F)
   (fun w=>V (cap (xl S w))) hF 0
 simp only [nsmul_zero,Fa] at ht
 rw [dE0 hS,sum_zero,auw] at ht
 change t4 _ qx (𝓝 (avz (cap p) (cap p) (cap h) (cap h))) at ht
 have he : (fun m:ℕ=>(d/ 16:ℝ)) =ᶠ[qx]
     (fun m:ℕ=>afK (acC 0) m F x/(2*(m:ℝ))^4) := by
   filter_upwards [eventually_gt_atTop 0] with m hm
   rw [hd N x m xu (fun _=>xu)]
   have hm0: (m:ℝ)≠0:= by positivity
   field_simp
   ring
 exact zt0 (tendsto_const_nhds.congr' he) ht
end
end XT
end
section
namespace XT
noncomputable section
open dN lB MvPolynomial
private def mo (F:Fin 4→nq) (k :ℕ) :cy GeoJets :=
 lI (F '' {i | i.val<k})
private theorem ccy (F:Fin 4→nq) (i:Fin 4) :
   mo F (i.val+1)=mo F i.val ⊔ lI {F i} := by
 unfold mo
 rw [← Ideal.span_union]
 congr 1
 ext z
 simp only [Set.mem_image,Mw ,Set.mem_union,LR]
 constructor
 · rintro ⟨j,hj,rfl⟩
   by_cases h:j.val< i.val
   · exact Or.inl ⟨j,h,rfl⟩
   · have he :j=i:=Fin.ext (by omega)
     exact Or.inr (oq  F he)
 · rintro (⟨j,hj,rfl⟩ | rfl)
   · exact ⟨j,by omega,rfl⟩
   · exact ⟨i,by omega,rfl⟩
private theorem previous {F:Fin 4→nq} {i:Fin 4} {Q:cy nq}
   (hQ:Q∈(mo F (i.val+1)).minimalPrimes) :
   ∃ P∈(mo F i.val).minimalPrimes,
     Q∈(P ⊔ lI {F i}).minimalPrimes := by
 rw [ccy] at hQ
 let:=hQ.isPrime
 obtain ⟨P,hP,hPQ⟩:=zXL (le_sup_left.trans hQ.le)
 refine ⟨P,hP,⟨⟨hQ.isPrime,t9 hPQ (le_sup_right.trans hQ.le)⟩,?_⟩⟩
 intro J hJ hJQ
 exact hQ.2 ⟨hJ.1,(sup_le_sup_right hP.le _).trans hJ.2⟩ hJQ
private theorem bDH {P Q:cy nq} (hP:P.IsPrime) {f :nq}
   (hQ:Q∈(P ⊔ lI {f}).minimalPrimes) :
   W3 P≤W3 Q+1∧(W3 Q+1=W3 P→f∉P) := by
 let:=hP
 by_cases hf :f∈P
 · have hle :lI {f} ≤ P:=(yJ P).mpr hf
   rw [sup_eq_left.mpr hle] at hQ
   have hQP:Q=P:=vj (hQ.2 ⟨hP,xu⟩ hQ.le) hQ.le
   subst Q
   exact ⟨by omega,by omega⟩
 · have hd:=principalCut_natDegree_affineHilbertPolynomial_add_one hf hQ
   exact ⟨hd.symm.le,fun _=>hf⟩
private theorem eMm (y :KE) :W3 (oF y)=0:= by
 apply natDegree_affineHilbertPolynomial_eq_zero_iff.mpr
 let f :nq →ₐ[qG] GeoField:=vk y
 have hf :vZ f := fun c=>⟨C c,by simp [f]⟩
 let e :=X4 hf
 exact Yo e.symm.toLinearMap e.symm.surjective
theorem a6D:sI oF:= by
 intro y z h
 funext i
 have hf :mD i-MvPolynomial.C (y i)∈oF y := by
  simp [oF,Cy]
 rw [h] at hf
 have hz :z i - y i=0:= by simpa [oF,Cy] using hf
 exact (sub_eq_zero.mp hz).symm
theorem c5K {f g u v :nq} {y :KE} (hy :aKn f g u v y) :
    ∃ P:Fin 5→ cy nq,P 0 = ⊥ ∧ P 4=oF y ∧
      (∀ i,(P i).IsPrime∧W3 (P i)=4 - i.val) ∧
      ∀ i:Fin 4,![f,g,u,v] i∉P i.castSucc ∧
        P i.succ∈(P i.castSucc ⊔ lI {![f,g,u,v] i}).minimalPrimes := by
  classical
  let F:Fin 4→GeoJets := ![f,g,u,v]
  have hF:mo F 4=lI ({f,g,u,v} : Set nq) := by
    unfold mo
    congr 1
    ext x
    simp only [Set.mem_image,Mw ,QL,LR]
    constructor
    · rintro ⟨i,_,rfl⟩
      fin_cases i <;> simp [F]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0,by decide,rfl⟩
      · exact ⟨1,by decide,rfl⟩
      · exact ⟨2,by decide,rfl⟩
      · exact ⟨3,by decide,rfl⟩
  let q:=oF y
  have hq:q∈(mo F 4).minimalPrimes :=hF.symm ▸ hy
  obtain ⟨p3,hp3,hc3⟩:=previous (i:=3) hq
  obtain ⟨p2,hp2,hc2⟩:=previous (i:=2) hp3
  obtain ⟨p1,hp1,hc1⟩:=previous (i:=1) hp2
  obtain ⟨p0,hp0,hc0⟩:=previous (i:=0) hp1
  have hbot:mo F 0 = ⊥ := by simp [mo]
  have hp0eq :p0 = ⊥ := by
    change p0∈(mo F 0).minimalPrimes at hp0
    rw [hbot] at hp0
    exact vj (hp0.2 ⟨Ob ,xu⟩ bot_le) bot_le
  have hd0:W3 p0=4 := by rw [hp0eq,W3,Vs]; simp
  have hd4 :W3 q=0:=eMm y
  have h0:=bDH hp0.isPrime hc0
  have h1 :=bDH hp1.isPrime hc1
  have h2 :=bDH hp2.isPrime hc2
  have h3:=bDH hp3.isPrime hc3
  have hd1 :W3 p1=3:= by omega
  have hd2 :W3 p2=2 := by omega
  have hd3:W3 p3=1 := by omega
  refine ⟨![p0,p1,p2,p3,q],hp0eq,rfl,?_,?_⟩
  · intro i
    fin_cases i
    · exact ⟨hp0.isPrime,hd0⟩
    · exact ⟨hp1.isPrime,hd1⟩
    · exact ⟨hp2.isPrime,hd2⟩
    · exact ⟨hp3.isPrime,hd3⟩
    · exact ⟨hq.isPrime,hd4⟩
  · intro i
    fin_cases i
    · exact ⟨h0.2 (by omega),hc0⟩
    · exact ⟨h1.2 (by omega),hc1⟩
    · exact ⟨h2.2 (by omega),hc2⟩
    · exact ⟨h3.2 (by omega),hc3⟩
end
end XT
end
section
namespace XT
noncomputable section
open aR dN lB YV MvPolynomial MeasureTheory Filter
open scoped Pointwise Topology BigOperators
def c1 :Prop :=
  ∀ (A:Fin 4→Set Exponent) (B:Set Exponent),admissible A B →
    ∃ D:Fin 5→ cy nq→ℝ,
      (∀ i P,P.IsPrime→W3 P=4 - i.val →
        0≤D i P∧aAV A B P i.val (D i P)) ∧
      ∀ y :KE,D 4 (oF y)=1
def c2 :Prop :=
  ∀ (A:Fin 4→Set Exponent) (B:Set Exponent),admissible A B →
    ∀ (i:Fin 4) (P:cy nq),P.IsPrime→W3 P=4 - i.val →
      ∀ f :nq,f∉P→((f^2).support :Set Exponent)⊆A i →
        ∀ Q:vh (cy nq),
          (∀ q∈Q,q∈(P ⊔ lI {f}).minimalPrimes) →
          ∀ (d:ℝ) (e :cy nq→ℝ),aAV A B P i.val d →
            (∀ q∈Q,aAV A B q (i.val+1) (e q)) →
            2 * ∑ q∈Q,e q≤d
private theorem gwE {α β:Type*} [DecidableEq α] [DecidableEq β]
    (S:vh α) (C:α→vh β) (w:β→ℝ)
    (hw : ∀ a∈S,∀ b∈C a,0≤w b) :
    ∑ b∈S.biUnion C,w b ≤ ∑ a∈S,∑ b∈C a,w b:= by
  induction S using zcw with
  | empty=>simp
  | insert a S ha ih =>
      rw [Finset.biUnion_insert,NY ha]
      have ih' := ih (fun x hx=>hw x (Finset.mem_insert_of_mem hx))
      have h:=Finset.sum_union_inter (s₁:=C a) (s₂:=S.biUnion C) (f :=w)
      have hz :0 ≤ ∑ b∈C a∩S.biUnion C,w b :=
        Finset.sum_nonneg fun b hb=>hw a (Finset.mem_insert_self a S) b
          (Finset.mem_inter.mp hb).1
      linarith
private theorem dQA (hcut:c2) {A:Fin 4→Set Exponent} {B:Set Exponent}
    (hAB:admissible A B) (D:Fin 5→ cy nq→ℝ)
    (hD : ∀ i P,P.IsPrime→W3 P=4 - i.val →
        0≤D i P∧aAV A B P i.val (D i P))
    (hpoint : ∀ y :KE,D 4 (oF y)=1)
    {f g u v :nq} (hs : ∀ i:Fin 4,((![f,g,u,v] i^2).support :Set Exponent)⊆A i)
    (points :vh KE) (hpts : ∀ y∈points,aKn f g u v y) :
    16*(points.card:ℝ)≤D 0 ⊥ := by
  classical
  let P (y :points) :=Classical.choose (c5K (hpts y.val y.property))
  have hP (y :points) :P y 0 = ⊥ ∧ P y 4=oF y.val ∧
      (∀ i,(P y i).IsPrime∧W3 (P y i)=4 - i.val) ∧
      ∀ i:Fin 4,![f,g,u,v] i∉P y i.castSucc ∧
        P y i.succ∈(P y i.castSucc ⊔ lI {![f,g,u,v] i}).minimalPrimes :=
    Classical.choose_spec (c5K (hpts y.val y.property))
  let L (k :Fin 5) :vh (cy nq) :=points.attach.image (fun y=>P y k)
  let total (k :Fin 5) :ℝ := ∑ q∈L k,D k q
  have hPrime (k :Fin 5) (q:cy nq) (hq:q∈L k) :
      q.IsPrime∧W3 q=4 - k.val := by
    obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hq
    exact (hP y).2.2.1 k
  have hstep (i:Fin 4) :2*total i.succ≤total i.castSucc:= by
    let C (q:cy nq) :=
      (points.attach.filter (fun y=>P y i.castSucc=q)).image (fun y=>P y i.succ)
    have hu: (L i.castSucc).biUnion C=L i.succ:= by
      ext q
      constructor
      · intro hq
        obtain ⟨p,_,hp⟩:=Finset.mem_biUnion.mp hq
        obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hp
        exact Finset.mem_image.mpr ⟨y,(Finset.mem_filter.mp hy).1,rfl⟩
      · intro hq
        obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hq
        refine Finset.mem_biUnion.mpr ⟨P y i.castSucc,Finset.mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
        exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,rfl⟩,rfl⟩
    have hchild (p q:cy nq) (hq:q∈C p) :
        q∈(p ⊔ lI {![f,g,u,v] i}).minimalPrimes := by
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hq
      have hy' := (Finset.mem_filter.mp hy).2
      simpa only [hy'] using ((hP y).2.2.2 i).2
    have hC (p q:cy nq) (hq:q∈C p) :
        0≤D i.succ q∧aAV A B q (i.val+1) (D i.succ q) := by
      have hqm:q∈L i.succ:= by
        obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hq
        exact Finset.mem_image.mpr ⟨y,(Finset.mem_filter.mp hy).1,rfl⟩
      exact hD _ _ (hPrime _ _ hqm).1 (hPrime _ _ hqm).2
    have hbound (p:cy nq) (hp:p∈L i.castSucc) :
        2 * ∑ q∈C p,D i.succ q≤D i.castSucc p:= by
      have hn : ![f,g,u,v] i∉p:= by
        obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hp
        exact ((hP y).2.2.2 i).1
      obtain ⟨hp',hd⟩:=hPrime _ _ hp
      exact hcut A B hAB i p hp' hd _ hn (hs i) (C p) (hchild p)
        _ _ (hD _ _ hp' hd).2 (fun q hq=>(hC p q hq).2)
    calc
      2*total i.succ≤2 * ∑ p∈L i.castSucc,∑ q∈C p,D i.succ q:= by
        apply y5 _ (by norm_num)
        unfold total
        rw [← hu]
        exact gwE _ _ _ (fun p _ q hq=>(hC p q hq).1)
      _ = ∑ p∈L i.castSucc,2 * ∑ q∈C p,D i.succ q:= by rw [Finset.mul_sum]
      _≤total i.castSucc:=zQk hbound
  have hrootDim:W3 (⊥ : cy nq)=4 := by
    rw [W3,Vs]
    simp
  have hroot :total 0≤D 0 ⊥ := by
    have hL:L 0 ⊆ {⊥} := by
      intro q hq
      obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hq
      simp [(hP y).1]
    unfold total
    calc
      ∑ q∈L 0,D 0 q ≤ ∑ q∈({⊥} : vh (cy nq)),D 0 q:= by
        apply zlp hL
        intro q hq _
        obtain rfl :=Finset.mem_singleton.mp hq
        exact (hD 0 ⊥ Ob hrootDim).1
      _=D 0 ⊥ := Finset.sum_singleton _ _
  have hterm :total 4=(points.card:ℝ) := by
    have hi:sI (fun (y :points)=>P y 4) := by
      intro y z he
      apply u8
      apply a6D
      simpa only [(hP y).2.1,(hP z).2.1] using he
    have hw (q:cy nq) (hq:q∈L 4) :D 4 q=1 := by
      obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hq
      rw [(hP y).2.1,hpoint]
    unfold total
    rw [vw rfl hw,Finset.sum_const,R9,zg]
    change ((points.attach.image _).card:ℝ)= _
    rw [Finset.card_image_of_injective _ hi,Finset.card_attach]
  have h0:=hstep 0
  have h1 :=hstep 1
  have h2 :=hstep 2
  have h3:=hstep 3
  change 2*total 1≤total 0 at h0
  change 2*total 2≤total 1 at h1
  change 2*total 3≤total 2 at h2
  change 2*total 4≤total 3 at h3
  linarith
theorem of_children (h1 :c1) (h2 :c2) :YV.c1 := by
 intro p h hp hh f g u v hf hg hu hv points hpts
 let S:Fin 4→Shape := ![p,p,h,h]
 let A:= fun i=>lattice ((S i).scale 2)
 let B:=lattice (aqO.scale 2)
 have hAB:admissible A B:=dER S
 obtain ⟨D,hD,hpoint⟩:=h1 A B hAB
 have hs (i:Fin 4) : ((![f,g,u,v] i^2).support :Set Exponent)⊆A i:= by
  fin_cases i
  · exact bOm hf
  · exact bOm hg
  · exact bOm hu
  · exact bOm hv
 have hc:=dQA h2 hAB D hD hpoint hs points (fun y hy=>(hpts y hy).1)
 have hd:W3 (⊥ : cy nq)=4 := by
  rw [W3,Vs]
  simp
 rw [← dE7 hp hh (hD 0 ⊥ Ob hd).2]
 linarith
end
end XT
end
section
namespace aA8
noncomputable section
open dN XT MvPolynomial
open Jq (jJ dO)
abbrev aH8 (A:Fin 4→Set Exponent) (B:Set Exponent) (P:cy nq)
  (b:ℕ) (w:GG) :ℕ :=
 oz qG ((restrictSupport qG (aza A B b w)).map
  (zh qG P).toLinearMap)
def Vu (A:Fin 4→Set Exponent) (B:Set Exponent) :Fin 5→Set Exponent :=
 UY B A
abbrev bk8 (A:Fin 4→Set Exponent) (B:Set Exponent) :=
 (j:Fin 5)×Vu A B j
def bOJ (A:Fin 4→Set Exponent) (B:Set Exponent) :bk8 A B→Fin 5 :=
 Sigma.fst
def dgy (A:Fin 4→Set Exponent) (B:Set Exponent) :
    lJ (bk8 A B) qG →ₐ[qG] GeoJets :=
  vk fun v=>oK v.2.val 1
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def csa (A:Fin 4→Set Exponent) (B:Set Exponent) (P:cy nq) :
    cy (lJ (bk8 A B) qG) :=
  ((P.comap (dgy A B)).homogeneousCore (dO (bOJ A B))).toIdeal
def cV (b:ℕ) (w:GG) :jJ :=
 Finsupp.equivFunOnFinite.symm (UY b w)
@[simp] theorem bHv (b:ℕ) (w:GG) :cV b w (EP 4)=b:= by
  change UY b w (EP 4)=b
  rw [Fin.lastCases_last]
@[simp] theorem gP3 (b:ℕ) (w:GG) :cV b w 4=b :=
  bHv b w
@[simp] theorem eiK (b:ℕ) (w:GG) (i:Fin 4) :
   cV b w i.castSucc=w i:= by
  simp [cV]
end
end aA8
end
section
namespace aA8
noncomputable section
open dN lB XT MvPolynomial Filter
open Jq (Form Represents line a5u a9f)
open scoped Pointwise
private def bounded (n:ℕ) :Set Exponent := {e | e.degree≤n}
private theorem a1T (m n:ℕ) :bounded m+bounded n⊆bounded (m+n) := by
 intro e he
 obtain ⟨a,ha,b,hb,rfl⟩:=Set.mem_add.mp he
 change (a+b).degree≤ m+n
 rw [uz]
 exact Nat.add_le_add ha hb
private theorem bmq (S:Set Exponent) {m:ℕ} (h:S⊆bounded m) (n:ℕ) :
   n•S⊆bounded (n*m) := by
 induction n with
 | zero=>simp [bounded]
 | succ n ih =>
   rw [C5 ,Nat.succ_mul]
   exact (KH ih h).trans (a1T _ _)
private theorem cR3 {S:Set Exponent} (h:S.Finite) : ∃ m,S⊆bounded m:= by
 obtain ⟨m,hm⟩:=(h.image Finsupp.degree).bddAbove
 exact ⟨m,fun e he=>hm (Set.mem_image_of_mem _ he)⟩
private theorem bYi {A:Fin 4→Set Exponent} {B:Set Exponent}
   (h:admissible A B) : ∃ m,B⊆bounded m ∧ ∀ i,A i⊆bounded m:= by
 classical
 obtain ⟨n,hn⟩:=cR3 h.2.1
 choose f hf using fun i=>cR3 (h.1 i).1
 refine ⟨max n (Finset.univ.sup f),?_,?_⟩
 · intro e he
   change e.degree≤ max n (Finset.univ.sup f)
   exact (show e.degree≤n from hn he).trans (Oc _ _)
 · intro i e he
   change e.degree≤ max n (Finset.univ.sup f)
   exact (show e.degree≤f i from hf i he).trans
     ((Ee (f :=f) (wB i)).trans (le_max_right _ _))
private theorem em5 {A:Fin 4→Set Exponent} {B:Set Exponent} {m:ℕ}
  (hB:B⊆bounded m) (hA : ∀ i,A i⊆bounded m) (P:cy nq)
  (b:ℕ) (w:GG) :
  aH8 A B P b w≤G2 P
    (b*m+w 0*m+w 1*m+w 2*m+w 3*m) := by
 have hAdd {S T:Set Exponent} {a b:ℕ} (ha :S⊆bounded a) (hb:T⊆bounded b) :
    S+T⊆bounded (a+b) :=(KH ha hb).trans (a1T a b)
 have he :aza A B b w ⊆
    bounded (b*m+w 0*m+w 1*m+w 2*m+w 3*m) :=
  hAdd (hAdd (hAdd (hAdd (bmq B hB b) (bmq _ (hA 0) (w 0)))
    (bmq _ (hA 1) (w 1))) (bmq _ (hA 2) (w 2)))
    (bmq _ (hA 3) (w 3))
 apply Submodule.finrank_mono
 exact VH (restrictSupport_mono qG he)
theorem eM3 {A:Fin 4→Set Exponent} {B:Set Exponent}
    (hAB:admissible A B) (P:cy nq) {p:Form}
    (hp:Represents p (fun t=>(aH8 A B P (t 4) (fun i=>t i.castSucc) :ℚ))) :
    p.totalDegree≤W3 P:= by
  obtain ⟨M,hB,hA⟩:=bYi hAB
  obtain ⟨N,hN⟩:=hp
  apply a9f
  intro t ht
  let L:ℕ:=t 4*M+t 0*M+t 1*M+t 2*M+t 3*M
  have hEval : ∀ᶠ n:ℕ in qx ,(line t p).eval (n:ℚ) =
      (aH8 A B P ((n•t) 4) (fun i=>(n•t) i.castSucc) :ℚ) := by
    filter_upwards [G0 N] with n hn
    rw [a5u]
    exact hN _ (fun j=>hn.trans (ziA n (ht j)))
  have hNonneg : ∀ᶠ n:ℕ in qx ,0≤(line t p).eval (n:ℚ) :=
    hEval.mono fun n hn=>hn.symm ▸ Nat.cast_nonneg _
  have hUpper : ∀ᶠ n:ℕ in qx ,(line t p).eval (n:ℚ) ≤
      ((u9 P).comp (oj ((L+1 :ℕ) :ℚ)*p9)).eval
        (n:ℚ) := by
    obtain ⟨N₁,hN₁⟩:=Z0 P
    filter_upwards [hEval,G0 N₁] with n hn hlarge
    have hnL:N₁≤n*(L+1) :=
      hlarge.trans (ziA _ (Nat.succ_pos L))
    rw [hn,Polynomial.eval_comp,Polynomial.eval_mul,II,Polynomial.eval_X,
      v9 (((L+1 :ℕ) :ℚ)),← NI,hN₁ _ hnL]
    have hb:=em5 hB hA P ((n•t) 4) (fun i=>(n•t) i.castSucc)
    have hscale : (n•t) 4*M+(n•t) 0*M+(n•t) 1*M +
        (n•t) 2*M+(n•t) 3*M=n*L:= by
      simp only [Finsupp.smul_apply,G1 ,L]
      ring
    change aH8 A B P ((n•t) 4) (fun i=>(n•t) i.castSucc) ≤
      G2 P _ at hb
    have hbound:aH8 A B P ((n•t) 4) (fun i=>(n•t) i.castSucc) ≤
        G2 P (n*L) := by
      rw [← hscale]
      exact hb
    exact_mod_cast hbound.trans ((affineHilbertFunction_mono P)
      (HZ n (Un L)))
  have hDegree :=(Polynomial.natDegree_le_of_eventually_eval_natCast_le hNonneg hUpper).1
  refine hDegree.trans (Polynomial.natDegree_comp_le.trans ?_)
  simpa only [zg ,pow_one] using
    HZ (W3 P) (Polynomial.natDegree_C_mul_X_pow_le ((L+1 :ℕ) :ℚ) 1)
end
end aA8
end
section
namespace cyE
open aR lB YV MeasureTheory Set
open scoped ENNReal
local notation "I₀" => Icc (0:ℝ)
private theorem a9x {α:Type*} [MeasureSpace α]
   [SigmaFinite (oZ :Measure α)] {S:Set (ℝ×α)} {C:Set α}
   {d:ℝ} {f :ℝ→ℝ} (hS:MeasurableSet S) (hC:oZ C < ∞)
   (hSC:S⊆I₀ d ×ˢ C)
   (hvol : ∀ x∈I₀ d,(oZ (Ef x ⁻¹' S)).toReal=f x) :
   (oZ S).toReal = ∫ x in I₀ d,f x := by
 have hm:=measurable_measure_prodMk_left (ν:=(oZ :Measure α)) hS
 have hf : ∀ᵐ x ∂(oZ :Measure ℝ),oZ (Ef x ⁻¹' S) < ∞ :=
   ae_of_all _ fun x=>(measure_mono (fun y hy=>(hSC (show (x,y)∈S from hy)).2)).trans_lt hC
 change (((oZ :Measure ℝ).prod (oZ :Measure α)) S).toReal= _
 rw [Measure.prod_apply hS,← integral_toReal hm.aemeasurable hf,
   ← integral_indicator measurableSet_Icc]
 refine integral_congr_ae (ae_of_all _ fun x => ?_)
 by_cases hx :x∈I₀ d
 · simpa only [indicator_of_mem hx] using hvol x hx
 · have he :Ef x ⁻¹' S = ∅ := by
     apply eq_empty_iff_forall_notMem.mpr
     intro y hy
     exact hx (hSC (show (x,y)∈S from hy)).1
   simp [he,hx]
private theorem bq9 (a b d:ℝ) (hd:0≤d) :
    (∫ x in I₀ d,a+b*x)=a*d+b*d^2/2 := by
  have hconst:zve (fun _:ℝ=>a) oZ 0 d :=
    continuous_const.intervalIntegrable _ _
  have hlin:zve (fun x :ℝ=>b*x) oZ 0 d :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc,← zxr hd]
  calc
    (∫ x in 0..d,a+b*x)=(∫ _ in 0..d,a)+(∫ x in 0..d,b*x) :=
      intervalIntegral.integral_add hconst hlin
    _ = _:= by
      rw [intervalIntegral.integral_const,zsY b (fun x=>x),
        integral_id,G1]
      ring
private def strip (A U:ℝ) :Set (ℝ×ℝ) :=
 {v | 0≤v.1∧0≤v.2∧v.1≤U∧v.2+v.1≤A}
private theorem gLo (A U:ℝ) (hU:0≤U) (hUA:U≤A) :
    (oZ (strip A U)).toReal=A*U-U^2/2 := by
  have hS:yQ (strip A U) := by
    simp only [strip,ofPred_and]
    repeat' apply Pj
    all_goals exact z9 (by fun_prop) (by fun_prop)
  have hsub:strip A U⊆I₀ U ×ˢ I₀ A:= by
    rintro ⟨u,x⟩ h
    obtain ⟨hu,hx,huU,hxu⟩:=h
    exact ⟨⟨hu,huU⟩,⟨hx,by linarith⟩⟩
  calc
    (oZ (strip A U)).toReal = ∫ u in I₀ U,A+(-1)*u:= by
      apply a9x hS.measurableSet isCompact_Icc.measure_lt_top hsub
      intro u hu
      have he :Ef u ⁻¹' strip A U=I₀ (A - u) := by
        ext x
        change (0≤u∧0≤x∧u≤U∧x+u≤A)↔_
        exact ⟨fun h=>⟨h.2.1,by linarith [h.2.2.2]⟩,
          fun h=>⟨hu.1,h.1,hu.2,by linarith [h.2]⟩⟩
      rw [he,Real.volume_Icc,Kc,ENNReal.toReal_ofReal (sub_nonneg.mpr (hu.2.trans hUA))]
      ring
    _=A*U-U^2/2 := by rw [bq9 _ _ _ hU]; ring
private def base (B J:ℝ) :Set (ℝ×ℝ×ℝ) :=
 {v | 0≤v.1∧0≤v.2.1∧0≤v.2.2 ∧
   v.2.1+2*v.1≤J∧v.2.2+v.2.1+v.1≤B}
private theorem gLf (B J:ℝ) (hJ:0≤J) (hJB:J≤B) :
    (oZ (base B J)).toReal=J^2*(2*B-J)/8:= by
  have hS:yQ (base B J) := by
    simp only [base,ofPred_and]
    repeat' apply Pj
    all_goals exact z9 (by fun_prop) (by fun_prop)
  have hsub:base B J⊆I₀ (J/2) ×ˢ (I₀ B ×ˢ I₀ B) := by
    rintro ⟨r,u,x⟩ h
    obtain ⟨hr,hu,hx,hj,hb⟩:=h
    exact ⟨⟨hr,by linarith⟩,⟨hu,by linarith⟩,⟨hx,by linarith⟩⟩
  calc
    (oZ (base B J)).toReal =
        ∫ r in I₀ (J/2),(B*J-J^2/2)+(J - 2*B)*r := by
      apply a9x hS.measurableSet
        (isCompact_Icc.prod isCompact_Icc).measure_lt_top hsub
      intro r hr
      have he :Ef r ⁻¹' base B J=strip (B - r) (J - 2*r) := by
        ext ⟨u,x⟩
        change (0≤ r∧0≤u∧0≤x∧u+2*r≤J∧x+u+r≤B) ↔
          (0≤u∧0≤x∧u≤J - 2*r∧x+u≤B - r)
        constructor
        · rintro ⟨_,hu,hx,hj,hb⟩
          exact ⟨hu,hx,by linarith,by linarith⟩
        · rintro ⟨hu,hx,hj,hb⟩
          exact ⟨hr.1,hu,hx,by linarith,by linarith⟩
      rw [he,gLo _ _ (by linarith [hr.2]) (by linarith [hr.1])]
      ring
    _=J^2*(2*B-J)/8:= by
      rw [bq9 _ _ _ (by positivity)]
      ring
private def aD:M5 ≃ᵐ ℝ×ℝ×ℝ×ℝ :=
  (Wl (fun _=>ℝ) (EP 3)).trans
    ((zjQ ℝ).prodCongr
      ((Wl (fun _=>ℝ) (EP 2)).trans
        ((zjQ ℝ).prodCongr
          ((MeasurableEquiv.piFinTwo (fun _=>ℝ)).trans Y4))))
private theorem dPT:MeasurePreserving aD oZ volume := by
 have hswap:MeasurePreserving (Y4 :ℝ×ℝ ≃ᵐ ℝ×ℝ)
    volume volume :=Measure.measurePreserving_swap
 exact ((MeasurePreserving.id (oZ :Measure ℝ)).prod
  (((MeasurePreserving.id (oZ :Measure ℝ)).prod
    (hswap.comp (volume_preserving_piFinTwo fun _=>ℝ))).comp
    (zYs (fun _=>ℝ) (EP 2)))).comp
  (zYs (fun _=>ℝ) (EP 3))
private def body (b j t:ℝ) :Set (ℝ×ℝ×ℝ×ℝ) :=
 {v | 0≤v.1∧v.1≤t∧0≤v.2.1∧0≤v.2.2.1∧0≤v.2.2.2 ∧
   v.2.2.1+2*v.2.1+3*v.1≤j∧v.2.2.2+v.2.2.1+v.2.1+v.1≤b}
private theorem dEW (p:aU) :
   cap p=aD ⁻¹' body p.b p.j p.t:= by
 ext x
 change ((∀ i,0≤x i)∧x 0 + x 1 + x 2 + x 3≤p.b ∧
   x 1+2*x 2 + 3*x 3≤p.j∧x 3≤p.t) ↔
   (0≤x 3∧x 3≤p.t∧0≤x 2∧0≤x 1∧0≤x 0 ∧
     x 1+2*x 2 + 3*x 3≤p.j∧x 0 + x 1 + x 2 + x 3≤p.b)
 constructor
 · rintro ⟨h,hb,hj,ht⟩
   exact ⟨h 3,ht,h 2,h 1,h 0,hj,hb⟩
 · rintro ⟨h3,ht,h2,h1,h0,hj,hb⟩
   exact ⟨by intro i; fin_cases i <;> assumption,hb,hj,ht⟩
private theorem gLg (b j t:ℝ) (hbj:j≤b) (hjt:3*t≤j) :
   (oZ (body b j t)).toReal =
     ∫ s in I₀ t,(j-3*s)^2*(2*b - j+s)/8:= by
 have hS:yQ (body b j t) := by
   simp only [body,ofPred_and]
   repeat' apply Pj
   all_goals exact z9 (by fun_prop) (by fun_prop)
 have hsub:body b j t⊆I₀ t ×ˢ (I₀ b ×ˢ (I₀ b ×ˢ I₀ b)) := by
   rintro ⟨s,r,u,x⟩ h
   obtain ⟨hs,hst,hr,hu,hx,hj,hb⟩:=h
   exact ⟨⟨hs,hst⟩,⟨hr,by linarith⟩,⟨hu,by linarith⟩,⟨hx,by linarith⟩⟩
 apply a9x hS.measurableSet
   (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top hsub
 intro s hs
 have he :Ef s ⁻¹' body b j t=base (b - s) (j-3*s) := by
   ext ⟨r,u,x⟩
   change (0≤ s∧s≤t∧0≤ r∧0≤u∧0≤x ∧
     u+2*r+3*s≤j∧x+u+r+s≤b) ↔
     (0≤ r∧0≤u∧0≤x∧u+2*r≤j-3*s∧x+u+r≤b - s)
   constructor
   · rintro ⟨_,_,hr,hu,hx,hj,hb⟩
     exact ⟨hr,hu,hx,by linarith,by linarith⟩
   · rintro ⟨hr,hu,hx,hj,hb⟩
     exact ⟨hs.1,hs.2,hr,hu,hx,by linarith,by linarith⟩
 rw [he,gLf _ _ (by linarith [hs.2]) (by linarith [hs.1])]
 ring
theorem proof :YV.c2 := by
 intro p hp
 let b:ℝ:=p.b
 let j:ℝ:=p.j
 let t:ℝ:=p.t
 have hbj:j≤b:= by
   dsimp [j,b]
   exact_mod_cast hp.1
 have hjt:3*t≤j:= by
   dsimp [j,t]
   exact_mod_cast hp.2
 have ht:0≤t:=Nat.cast_nonneg _
 rw [dEW,dPT.measure_preimage_equiv,
   gLg b j t hbj hjt,integral_Icc_eq_integral_Ioc,
   ← zxr ht,← zsY]
 let A:=8*b*j^2 - 4*j^3
 let B := -24*b*j+14*j^2
 let C:=24*b - 20*j
 let F:= fun s :ℝ=>A*s+B*s^2+C*s^3+9*s^4
 have hF (s :ℝ) :
     HasDerivAt F (32*((j-3*s)^2*(2*b - j+s)/8)) s := by
   have hid :=hasDerivAt_id s
   have h:=(((hid.const_mul A).add ((hid.pow 2).const_mul B)).add
     ((hid.pow 3).const_mul C)).add ((hid.pow 4).const_mul (9:ℝ))
   convert h using 1
   · funext y
     rfl
   · norm_num [A,B,C]
     ring
 have hc:Continuous (fun s :ℝ=>32*((j-3*s)^2*(2*b - j+s)/8)) := by
   fun_prop
 rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hF s)
   (hc.intervalIntegrable _ _)]
 push_cast [Dn]
 dsimp [F,A,B,C,b,j,t]
 ring
end cyE
end
section
namespace YW
noncomputable section
open aR dN lB
open scoped BigOperators
abbrev PK:=lJ AK qG
abbrev Al:=cy PK
abbrev alk :=AK→qG
abbrev dimension (A:Al) :=(u9 A).natDegree
def Ib (f g:nq) :cy GeoJets :=lI {f,g}
def Z1 (f g:nq) (C:GR) :vh (cy nq) :=
 (Ib f g).retainedMinimalPrimes C.denom
def au8 (i:Fin 4) :AK:=i.castLE (by decide :4≤bf)
def project (z :alk) :KE :=z ∘ au8
def BQ (C:GR) (y :KE) :alk :=
 fun i=>Gn y (C.numerator i)/Gn y C.denom
def ajF (C:GR) (P:cy nq) :Al :=
  MvPolynomial.vanishingIdeal qG
    (BQ C '' {y | y∈Gk qG P ∧
      Gn y C.denom≠0})
def bew (C:GR) :PK:=MvPolynomial.rename au8 C.denom
def adD (a :agy) :PK :=
 qz a.1 + ∑ i,qz (a.2 i)*mD i
end
end YW
end
