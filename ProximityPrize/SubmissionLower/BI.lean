import ProximityPrize.SubmissionLower.S
import ProximityPrize.SubmissionLower.CC
set_option Elab.async false
open _root_ renaming AlgHom.comp_apply→Vz,AlgHom.comp_toLinearMap→PD,Algebra.algebraMap→nq,And.intro→Aa,CharP.cast_eq_zero_iff→LQ,CommRing→vw,DFunLike.congr_fun→Au,DecidableEq→ oq,Equiv.apply_symm_apply→RD,Filter.atTop→pG,Filter.eventually_ge_atTop→WY,Fin.castSucc→uJ,Fin.castSucc_injective→FV,Fin.castSucc_ne_last→VS,Fin.last→pU,Fin.lastCases→yU,Fin.lastCases_castSucc→X8,Fin.lastCases_last→Lf,Fin.snoc→EK,Fin.sum_univ_castSucc→FK,Fin.sum_univ_eq_sum_range→Gk,Fin.sum_univ_four→yo,Fin.val→Gr,Finite→vk,Finset→mD,Finset.card_insert_of_notMem→X4,Finset.erase_insert→WD,Finset.le_sup→Mj,Finset.mem_singleton→RP,Finset.mem_univ→u9,Finset.mul_prod_erase→NW,Finset.mul_sum→uz,Finset.ne_of_mem_erase→QL,Finset.prod_congr→S2,Finset.range→th,Finset.sdiff_sdiff_eq_self→Gi,Finset.sdiff_subset→Wm,Finset.single_le_sum→Mw,Finset.sum_add_distrib→sH,Finset.sum_congr→p5,Finset.sum_eq_single→Vq,Finset.sum_insert→Pf,Finset.sum_ite_eq'→Vl,Finset.sum_le_sum→t6,Finset.sum_range_succ→yB,Finset.sum_sub_distrib→Sd,Finset.univ→Ml,Finsupp.add_apply→KH
open _root_ renaming Finsupp.degree_apply→Bf,Finsupp.degree_eq_sum→t4,Finsupp.degree_mapDomain→SM,Finsupp.degree_single→VO,Finsupp.finite_of_degree_le→OJ,Finsupp.single→qz,Finsupp.single_apply→vj,Finsupp.sum→NX,Finsupp.sum_fintype→Hw,Finsupp.weight→ oK,Finsupp.weight_apply→Fa,Finsupp.weight_eq_sum→Df,Finsupp.weight_single→KI,Finsupp.weight_sub_single_add→WW,Finsupp.zero_apply→Te,Fintype→pL,Fintype.card→GB,Fintype.card_fin→xL,Fintype.card_sigma→Sv,Function.Injective→qx,Function.Surjective→sI,Function.comp_apply→G6,Function.update_of_ne→ Il,Ideal→c9,Ideal.Quotient.eq_zero_iff_mem→wA,Ideal.Quotient.mk→lV,Ideal.Quotient.mk_surjective→Nq,Ideal.Quotient.mkₐ→uh,Ideal.comap→zg,Ideal.comap_map_mk→Pj,Ideal.isPrime_map_quotientMk_of_isPrime→Xx,Ideal.mem_span_singleton_self→Dz,Ideal.quotientKerAlgEquivOfSurjective→Fz,Ideal.quotientMap_injective→Nr,Ideal.quotientMapₐ→G3,Ideal.span→ oY,Ideal.span_singleton_le_iff_mem→G2,Ideal.subset_span→ In,Insert.insert→vh,IsFractionRing.injective→N0,IsLeftCancelMulZero.mul_left_cancel_of_ne_zero→SL,IsLeftRegular→p6,IsLocalRing.maximalIdeal→Xg,IsLocalRing.maximalIdeal.isMaximal→Rm,IsLocalization.Away.invSelf→Up,List.length_cons→HZ,List.mem_cons_self→Ts,Localization.AtPrime→GF
open _root_ renaming Localization.Away→SD,Module.Finite→Et,Module.Finite.of_surjective→JQ,Module.finrank→pz,Module.finrank_eq_nat_card_basis→LO,Module.finrank_self→Pc,Module.length→J4,MulZeroClass.mul_zero→vi,Multiplicative.ofAdd→UZ,MvPolynomial→lJ,MvPolynomial.C→ ov,MvPolynomial.X→lI,MvPolynomial.aeval→t5,MvPolynomial.affineHilbertFunction→p7,MvPolynomial.affineHilbertPolynomial→ oD,MvPolynomial.affineHilbertPolynomial_eq_C_finrank→Xp,MvPolynomial.algebraMap_def→NY,MvPolynomial.basisRestrictSupport→C9,MvPolynomial.coeff_monomial→G4,MvPolynomial.eq_affineHilbertPolynomial_of_eval_eq→WK,MvPolynomial.eval→ oy,MvPolynomial.eval_C→Pv,MvPolynomial.eval_monomial→KA,MvPolynomial.eval₂Hom→zh,MvPolynomial.eventually_eval_affineHilbertPolynomial→z8,MvPolynomial.funext_set→Qx,MvPolynomial.homogeneousComponent→C4,MvPolynomial.induction_on'→Kl,MvPolynomial.isHomogeneous_monomial→ IU,MvPolynomial.isWeightedHomogeneous_X→G0,MvPolynomial.le_totalDegree→F9,MvPolynomial.le_weightedTotalDegree→G8,MvPolynomial.map→ Iw,MvPolynomial.map_C→WX,MvPolynomial.mem_iff_weightedHomogeneousComponent_mem→Ok,MvPolynomial.mk_mem_quotientDegreeLE→Nj,MvPolynomial.monomial→n5,MvPolynomial.monomialMap→nI,MvPolynomial.monomialMap_X→Dv,MvPolynomial.monomialMap_mem_restrictSupport_nsmul→ IT,MvPolynomial.monomialMap_surjective→x7,MvPolynomial.monomial_le_degreeOf→R9,MvPolynomial.monomial_mul_monomial→ II,MvPolynomial.natDegree_affineHilbertPolynomial_comap_of_surjective→G5,MvPolynomial.pderiv→qU,MvPolynomial.quotientDegreeLE→uW,MvPolynomial.rename→zf,MvPolynomial.restrictSupport→qJ
open _root_ renaming MvPolynomial.restrictSupport_eq_span→zm,MvPolynomial.ringHom_ext→xm,MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite→Wl,MvPolynomial.support_X→Qw,MvPolynomial.support_map_subset→Pk,MvPolynomial.support_sub→RC,MvPolynomial.weightedHomogeneousComponent→t7,MvPolynomial.weightedHomogeneousComponent_of_mem→Pr,MvPolynomial.weightedHomogeneousSubmodule→Ee,MvPolynomial.weightedTotalDegree_piSingle→Ea,Nat.add_assoc→LP,Nat.add_comm→Mz,Nat.add_le_add→Eg,Nat.add_le_add_left→Yi,Nat.add_le_add_right→VH,Nat.add_left_comm→S1,Nat.add_mul→FR,Nat.card_coe_set_eq→zi,Nat.card_eq_fintype_card→Gn,Nat.cast_add→zc,Nat.cast_mul→Du,Nat.cast_one→Dw,Nat.cast_sub→vG,Nat.le_add_left→GY,Nat.le_add_right→qy,Nat.le_mul_of_pos_right→Vs,Nat.le_of_lt_succ→UP,Nat.mul_add→NZ,Nat.mul_comm→G7,Nat.mul_le_mul_left→ oz,Nat.mul_le_mul_right→XB,Nat.mul_left_comm→xu,Nat.mul_pos→z9,Nat.pos_of_ne_zero→Kp,Nat.zero_le→EP,Option.some.inj→Np,Pi.single→Av,Pi.single_apply→Kv,Pi.single_eq_of_ne→MS,Polynomial→wB,Polynomial.C→ oZ,Polynomial.X→p9,Polynomial.coeff_C_mul→VC,Polynomial.coeff_C_mul_X_pow→Un,Polynomial.coeff_C_zero→XG,Polynomial.coeff_add→Ef,Polynomial.coeff_eq_zero_of_natDegree_lt→zk,Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le→JW
open _root_ renaming Polynomial.coeff_mul_X_pow'→P7,Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg→RJ,Polynomial.coeff_sub→Xo,Polynomial.coeff_taylor_of_natDegree_le→UY,Polynomial.derivative→pC,Polynomial.eval_C→Re,Polynomial.eval_X→PM,Polynomial.eval_add→XJ,Polynomial.eval_mul→TI,Polynomial.finsetSum_coeff→TH,Polynomial.taylor→Gj,RingHom.id→Ob,RingHom.ker→t9,RingHom.ker_isPrime→MO,RingHom.mapMatrix_apply→TZ,RingHom.mem_ker→NI,Set.infinite_range_of_injective→SC,Set.mem_ofPred_eq→G1,Set.mem_zero→yl,Set.range→v9,Submodule.equivMapOfInjective→SU,Submodule.finrank_mono→Qy,Submodule.map_comp→Oc,Submodule.map_mono→Ye,Submodule.mem_colon_singleton→Xu,Submodule.span_le→Kc,Submodule.sum_mem→Ww,Subtype.ext→vH,Subtype.val→C5,TrivSqZeroExt.ext→FQ,TrivSqZeroExt.fstHom→Yc,TrivSqZeroExt.fst_mk→SW,TrivSqZeroExt.snd_mk→zd,aR.Shape→cy,aR.Shape.plus→qM,aR.Shape.scale→t3,aR.shape→qG,add_comm→FU,add_zero→y5,charP_of_injective_ringHom→MK,congrArg→ ox,congrFun→zR,dN.GeoField→aU,dN.GeoJets→lz,dN.separant→ oj,div_nonneg→Mk,gR.M4.IsPrimitive→u8,ite_eq_left→z7
open _root_ renaming ite_eq_right→Kh,le_antisymm→vl,le_max_left→PA,le_rfl→yL,le_sup_left→Kz,le_sup_right→Cy,map_add→pQ,map_mul→nX,map_natCast→JM,map_one→zS,map_sub→yJ,map_sum→t8,map_zero→qm,mul_add→wY,mul_assoc→v8,mul_comm→u5,mul_one→sS,nonZeroDivisors→xW,not_le_of_gt→GR,one_mul→Ar,pow_two→ze,ringKrullDim→vZ,ringKrullDim_eq_zero_of_field→LR,smul_eq_mul→yQ,sub_eq_zero→JK,succ_nsmul→G9,sup_le→xI,zero_add→wR,zero_smul→zE
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Mc
open K1 Polynomial Matrix
open gR
def c1 :Prop :=
  ∀ (F:Type) [Field F] (h L s :ℕ) (P:Fin 2→F[X][X]),
    h+s=L→0<s →
    (∀ b,(P b).natDegree≤h) →
    u8 (a6n P h) →
    u8 (acq (Sm P L s)) ∧
    ∃ H :ℕ,(∀ b j,((P b).coeff j).natDegree≤H) ∧
      ∃ rows :Fin s→(Fin 2×Fin L),
        (acq (Sm P L s) rows).natDegree=s*H
def c2 :Prop :=
  ∀ (F:Type) [Field F] (L w s p:ℕ)
    (M:Matrix (Fin 2×Fin L) (Fin w) F[X]) (W:Matrix (Fin 2×Fin L) (Fin s) F[X]),
    1≤p →
    Bx.adJ M+s=2*L →
    W.transpose*M=0 →
    (∀ i j,(M i j).natDegree≤ if i.1=0 then 1 else p) →
    u8 (acq W) →
    ∀ rows :Fin s→(Fin 2×Fin L),(acq W rows).natDegree≤L*(p+1) - s
end Mc
end
section
set_option backward.isDefEq.respectTransparency false
namespace czJ
noncomputable section
open Polynomial Matrix gR Mc
private theorem bdA {R E :Type} [vw R] [Field E]
   (P:Fin 2→R[X]) (h s :ℕ) (hdegree : ∀ b,(P b).natDegree≤h)
   (f :R→E) (hf :f 0=0) (b:Fin 2) (j:Fin (h+1))
   (hj:f ((P b).coeff j.val)≠0) :
   ∃ rows :Fin s→Fin 2×Fin (h+s),
     acq ((Sm P (h+s) s).map f) rows≠0:= by
 classical
 let S:=(th (h+1)).filter (fun d=>f ((P b).coeff d)≠0)
 have hS:S.Nonempty :=⟨j.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt,hj⟩⟩
 let d:=S.max' hS
 have hd:d∈S:=S.max'_mem hS
 have hdle :d≤h:=UP (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
 have hdne :f ((P b).coeff d)≠0:=(Finset.mem_filter.mp hd).2
 have hlarge : ∀ k,d<k→f ((P b).coeff k)=0:= by
   intro k hk
   by_cases hkh:k<h+1
   · by_contra hne
     exact (GR hk) (S.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkh,hne⟩))
   · have hk' : (P b).natDegree<k :=(hdegree b).trans_lt (by omega)
     rw [zk  hk',hf]
 let rows (i:Fin s) :Fin 2×Fin (h+s) :=(b,⟨d+i.val,by omega⟩)
 let A:=((Sm P (h+s) s).map f).submatrix rows id
 have htri:A.IsUpperTriangular := by
   intro i j hij
   change j.val< i.val at hij
   change f ((P b*p9 ^j.val).coeff (d+i.val))=0
   rw [P7,z7 (by omega)]
   exact hlarge _ (by omega)
 have hdiag (i:Fin s) :A i i=f ((P b).coeff d) := by
   change f ((P b*p9 ^i.val).coeff (d+i.val))= _
   rw [Polynomial.coeff_mul_X_pow]
 refine ⟨rows,?_⟩
 change A.det≠0
 rw [Matrix.det_of_isUpperTriangular htri]
 simp only [hdiag,Fin.prod_const]
 exact pow_ne_zero _ hdne
private theorem ccG {F:Type} [Field F]
  (P:Fin 2→F[X][X]) (h s :ℕ) (hdegree : ∀ b,(P b).natDegree≤h)
  (hprimitive :u8 (a6n P h)) :
  u8 (acq (Sm P (h+s) s)) := by
 classical
 let W:=Sm P (h+s) s
 let I:=oY (v9 (acq W))
 change I = ⊤
 by_contra hI
 obtain ⟨M,hM,hIM⟩:=Ideal.exists_le_maximal I hI
 let:M.IsMaximal:=hM
 let:Field (F[X] ⧸ M) :=Ideal.Quotient.field M
 let φ:=lV M
 have hsurvives : ∃ i,φ (a6n P h i)≠0:= by
  by_contra hn
  push Not at hn
  obtain ⟨a,ha⟩:=(M4.a6R _).mp hprimitive
  have heq :=ox φ ha
  simp only [t8 ,nX ,hn,vi ,Finset.sum_const_zero,zS] at heq
  exact zero_ne_one heq
 obtain ⟨⟨b,j⟩,hj⟩:=hsurvives
 obtain ⟨rows,hrows⟩:=bdA P h s hdegree φ (qm φ) b j hj
 have hz :φ (acq W rows)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (hIM (In (Set.mem_range_self rows)))
 apply hrows
 have heq :=φ.map_det (W.submatrix rows id)
 rw [TZ] at heq
 exact heq.symm.trans hz
private theorem bXH {F:Type*} [Field F] {s :ℕ}
   (A:Matrix (Fin s) (Fin s) F[X]) (H :ℕ) (hdegree : ∀ i j,(A i j).natDegree≤H) :
   A.det.coeff (s*H)=(A.map (fun q=>q.coeff H)).det:= by
 classical
 rw [Matrix.det_apply,Matrix.det_apply,TH]
 apply p5 rfl
 intro σ hσ
 rw [Polynomial.coeff_smul]
 congr 1
 simpa only [Finset.card_univ,xL,Matrix.map_apply] using
   Polynomial.coeff_prod_of_natDegree_le (Ml :mD (Fin s))
     (fun i=>A (σ i) i) H (fun i _=>hdegree (σ i) i)
private theorem gqj {F:Type} [Field F]
    (P:Fin 2→F[X][X]) (h s :ℕ) (hdegree : ∀ b,(P b).natDegree≤h)
    (hprimitive :u8 (a6n P h)) :
    ∃ H :ℕ,(∀ b j,((P b).coeff j).natDegree≤H) ∧
      ∃ rows :Fin s→Fin 2×Fin (h+s),
        (acq (Sm P (h+s) s) rows).natDegree=s*H := by
  classical
  let q:=a6n P h
  let S:=(Ml :mD (Fin 2×Fin (h+1))).filter (fun i=>q i≠0)
  have hS:S.Nonempty := by
    obtain ⟨i,hi⟩:=M4.cNz q hprimitive 0
    refine ⟨i,Finset.mem_filter.mpr ⟨u9 _,?_⟩⟩
    intro hz
    exact hi (by rw [hz,Polynomial.eval_zero])
  let H :=S.sup (fun i=>(q i).natDegree)
  have hbound : ∀ b j,((P b).coeff j).natDegree≤H := by
    intro b j
    by_cases hj:j<h+1
    · let i:Fin 2×Fin (h+1) :=(b,⟨j,hj⟩)
      change (q i).natDegree≤H
      by_cases hi:q i=0
      · simp [hi]
      · exact Mj (s :=S) (f := fun k=>(q k).natDegree)
          (Finset.mem_filter.mpr ⟨u9 _,hi⟩)
    · have hj' : (P b).natDegree<j:=(hdegree b).trans_lt (by omega)
      rw [zk  hj']
      simp
  obtain ⟨i,hi,hmax⟩:=Finset.exists_mem_eq_sup S hS (fun k=>(q k).natDegree)
  have htop: (q i).coeff H≠0:= by
    change H=(q i).natDegree at hmax
    rw [hmax,Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (Finset.mem_filter.mp hi).2
  obtain ⟨rows,hrows⟩:=bdA P h s hdegree (fun p=>p.coeff H)
    (Polynomial.coeff_zero _) i.1 i.2 htop
  let A:=(Sm P (h+s) s).submatrix rows id
  have hA (i j:Fin s) : (A i j).natDegree≤H := by
    change ((P (rows i).1*p9 ^j.val).coeff (rows i).2.val).natDegree≤H
    rw [P7]
    split_ifs
    · exact hbound _ _
    · simp
  have hcoeff :A.det.coeff (s*H)≠0:= by
    rw [bXH A H hA]
    exact hrows
  have hupper :A.det.natDegree≤ s*H := by
    simpa only [Finset.sum_const,Finset.card_univ,xL,yQ] using
      gR.bsR A (fun _=>H) hA
  exact ⟨H,hbound,rows,Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hupper hcoeff⟩
theorem proof :Mc.c1 := by
 intro F inst h L s P hL _ hdegree hprimitive
 subst L
 exact ⟨ccG P h s hdegree hprimitive,
  gqj P h s hdegree hprimitive⟩
end
end czJ
end
section
set_option backward.isDefEq.respectTransparency false
namespace bz5
open Polynomial Matrix
open gR
open scoped BigOperators
theorem proof :Mc.c2 := by
  intro F _ L w s p M W hp hrank hkernel hdegree hprim rows
  classical
  let E :=Bx.lN F
  let φ:=nq F[X] E
  have hφ:qx φ:=N0 F[X] E
  let r :=Bx.adJ M
  obtain ⟨B⟩:=Bx.d4g M
  have hcard:GB (Fin r ⊕ Fin s)=GB (Fin 2×Fin L) := by
    simpa [Fintype.card_sum,Fintype.card_prod,r] using hrank
  let e : (Fin r ⊕ Fin s) ≃ (Fin 2×Fin L) :=Fintype.equivOfCardEq hcard
  let C:=M.submatrix e B.cols
  let V:=W.submatrix e id
  have hC : ∀ a,(C.map φ).mulVec a=0→a=0:= by
    have hdet: ((M.submatrix B.rows B.cols).map φ).det≠0:= by
      rw [← TZ,← φ.map_det]
      exact fun hz=>B.minor_ne (hφ (hz.trans (qm φ).symm))
    intro a ha
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    have hi:=zR ha (e.symm (B.rows i))
    simpa only [C,Matrix.mulVec,dotProduct,Matrix.map_apply,Matrix.submatrix_apply,
      RD,Pi.zero_apply] using hi
  have hVC: (V.map φ).transpose*(C.map φ)=0:= by
    ext i j
    have hij:=ox φ (zR (zR hkernel i) (B.cols j))
    change (∑ k :Fin r ⊕ Fin s,φ (W (e k) i)*φ (M (e k) (B.cols j)))=0
    rw [Equiv.sum_comp e (fun k=>φ (W k i)*φ (M k (B.cols j)))]
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.zero_apply,
      t8 ,nX ,qm] using hij
  have hminor (I:Fin s→(Fin r ⊕ Fin s)) :
      (V.submatrix I id).det=Mc.acq W (e ∘ I) :=rfl
  have hminor' (J:Fin s→(Fin 2×Fin L)) :
      (V.submatrix (e.symm ∘ J) id).det=Mc.acq W J:= by
    rw [hminor]
    congr 1
    funext i
    simp only [G6,RD]
  have hprimV:u8
      (fun I:Fin s→(Fin r ⊕ Fin s)=>(V.submatrix I id).det) := by
    have hrange :v9 (fun I:Fin s→(Fin r ⊕ Fin s)=>(V.submatrix I id).det) =
        v9 (Mc.acq W) := by
      ext z
      constructor
      · rintro ⟨I,rfl⟩
        exact ⟨e ∘ I,(hminor I).symm⟩
      · rintro ⟨J,rfl⟩
        exact ⟨e.symm ∘ J,hminor' J⟩
    unfold u8 at hprim ⊢
    rwa [hrange]
  let d (i:Fin r ⊕ Fin s) :=if (e i).1=0 then 1 else p
  have hpositive : ∀ i,1≤d i:= by
    intro i
    dsimp [d]
    split_ifs <;> omega
  have hsum: (∑ i,d i)=L*(p+1) := by
    dsimp [d]
    rw [Equiv.sum_comp e (fun i:Fin 2×Fin L=>if i.1=0 then 1 else p)]
    simp [Fintype.sum_prod_type,Fin.sum_univ_two,NZ,Mz]
  have hbound:=eOj φ hφ C V hVC hC hprimV d hpositive
    (fun i j=>hdegree (e i) (B.cols j)) (e.symm ∘ rows)
  rwa [hminor',hsum] at hbound
end bz5
end
section
namespace fP
open aR MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
theorem xH (m:Fin 4 →₀ ℕ) :
  m.weight lP=m 1+2*m 2 + 3*m 3:= by
 simp [Df ,yo ,lP,G7]
theorem oG (m:Fin 4 →₀ ℕ) :
  m.weight m9=3*m 0+m 2+2*m 3:= by
 simp [Df ,yo ,m9,G7]
theorem cF (m:Fin 4 →₀ ℕ) :
  m.degree=m 0+m 1+m 2+m 3:= by
 simp [t4 ,yo]
theorem Qg (n:ℕ) (f :ℕ→ℕ) :qI n f = ∑ i:Fin n,f i:= by
 rw [Gk f,aAs]
private def rU (a b c f :ℕ) :Fin 4 →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm ![a,b,c,f]
@[simp] private theorem OZ (a b c f :ℕ) (j:Fin 4) :
   rU a b c f j = ![a,b,c,f] j:= by simp [rU]
private theorem d5o (m:Fin 4 →₀ ℕ) :
  rU (m 0) (m 1) (m 2) (m 3)=m:= by
 ext i
 fin_cases i <;> simp
private theorem cVv (lo hi:ℤ) (j:ℕ) :
  j<aOb lo hi↔lo+(j:ℤ)≤hi:= by
 unfold aOb
 omega
private abbrev bQi (d:ℕ) (lo hi:ℤ) (top:ℕ) :=
  Σ f :Fin (min d top+1),
    Σ c:Fin (min (d - f.val) ((hi-3*f.val)/2).toNat+1),
      Fin (aOb (max 0 (lo - 2*c.val-3*f.val))
        (min ((d:ℤ) - f.val - c.val) (hi - 2*c.val-3*f.val)))
private def blK (d:ℕ) (lo hi:ℤ) (top:ℕ) (p:bQi d lo hi top) :
  {m:Fin 4 →₀ ℕ // Ew d lo hi top m} := by
 obtain ⟨f,c,j⟩:=p
 let lower :ℤ:=max 0 (lo - 2*c.val-3*f.val)
 let upper :ℤ:=min ((d:ℤ) - f.val - c.val) (hi - 2*c.val-3*f.val)
 let b:=lower.toNat+j.val
 have h0:0≤lower :=PA _ _
 have hj:lower+(j.val :ℤ)≤upper :=(cVv _ _ _).mp j.isLt
 have hb: (b:ℤ)=lower+(j.val :ℤ) := by dsimp [b]; omega
 have hlow:=le_max_right (0:ℤ) (lo - 2*c.val-3*f.val)
 have hf :=f.isLt
 have h:b+c.val+f.val≤d:= by dsimp [upper] at hj; omega
 refine ⟨rU (d-(b+c.val+f.val)) b c f,?_⟩
 simp only [Ew,cF,xH,OZ]
 change d-(b+c.val+f.val)+b+c.val+f.val=d ∧
  lo≤(b+2*c.val+3*f.val :ℕ) ∧
  (b+2*c.val+3*f.val :ℕ)≤hi∧f.val≤top
 dsimp only [upper] at hj
 change lo - 2*c.val-3*f.val≤lower at hlow
 omega
private theorem dyg (d:ℕ) (lo hi:ℤ) (top:ℕ) :
   Function.Bijective (blK d lo hi top) := by
 constructor
 · rintro ⟨⟨f,hf⟩,⟨c,hc⟩,⟨j,hj⟩⟩ ⟨⟨f',hf'⟩,⟨c',hc'⟩,⟨j',hj'⟩⟩ h
   have ef :f=f' := by
    simpa [blK] using ox (fun m=>m.val 3) h
   have ec:c=c' := by
    simpa [blK] using ox (fun m=>m.val 2) h
   subst f'
   subst c'
   have ej:j=j' := by
    simpa [blK] using ox (fun m=>m.val 1) h
   subst j'
   rfl
 · intro m
   obtain ⟨hd,hl,hu,htop⟩:=m.property
   let a :=m.val 0
   let b:=m.val 1
   let c:=m.val 2
   let f :=m.val 3
   change f≤top at htop
   rw [cF] at hd
   change a+b+c+f=d at hd
   rw [xH] at hl hu
   change lo≤(b+2*c+3*f :ℕ) at hl
   change (b+2*c+3*f :ℕ)≤hi at hu
   have hf :f< min d top+1 := by omega
   have hc:c< min (d - f) ((hi-3*f)/2).toNat+1 := by omega
   let lower :ℤ:=max 0 (lo - 2*c-3*f)
   let upper :ℤ:=min ((d:ℤ) - f - c) (hi - 2*c-3*f)
   let j:=b-lower.toNat
   have h0:0≤lower :=PA _ _
   have hb:lower.toNat+j=b:= by
    dsimp [lower,j]
    omega
   have hj:j<aOb lower upper :=(cVv _ _ _).mpr (by
    dsimp [upper] at *
    omega)
   refine ⟨⟨⟨f,hf⟩,⟨c,hc⟩,⟨j,hj⟩⟩,vH ?_⟩
   change rU (d-(lower.toNat+j+c+f)) (lower.toNat+j) c f=m.val
   rw [hb,show d-(b+c+f)=a by omega]
   exact d5o m.val
theorem bGG (d:ℕ) (lo hi:ℤ) (top:ℕ) :
  pz ao (GS d lo hi top)=anJ d lo hi top:= by
 let e :=Equiv.ofBijective (blK d lo hi top) (dyg d lo hi top)
 let b:=C9 ao {m | Ew d lo hi top m}
 calc
  _=GB (bQi d lo hi top) :=Module.finrank_eq_card_basis (b.reindex e.symm)
  _ = _:= by simp only [bQi,anJ,Sv,xL,Qg]
end
end fP
end
section
namespace fP
open aR MvPolynomial
noncomputable section
set_option maxHeartbeats 1000000
@[simp] theorem dxK:Jx (lI 0)=L4 := by
  simp [Jx]
theorem a1u (j:Fin 4) (h:j≠0) :
  Jx (lI j)=lI j:= by
 simp [Jx,h]
theorem aMe {Q:Form} {d:ℕ}
   (hQ:Q.IsWeightedHomogeneous (fun _=>(1 :ℕ)) d) :
   (Jx Q).IsWeightedHomogeneous (fun _=>(1 :ℕ)) d:= by
 apply hQ.bind₁
 intro i
 split_ifs
 · let h:=G0 ao (fun _:Fin 4=>(1 :ℕ))
   exact (((h 0).add (h 1)).sub (h 2)).add (h 3)
 · exact G0 _ _ _
end
end fP
end
section
set_option maxHeartbeats 1200000
namespace axe
noncomputable section
open aR dN BO GJ MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem efu (aI:c9 lz) (a h:cy) :
   bHl (To aI h) a=Ux aI a h:= by
 classical
 let H₀:=lJ (uL h) aU
 let H :=dV h
 let B:=lJ (aav a h) aU
 let N :=lJ (uL a) H₀
 let S:=lJ (uL a) H
 let F:=VM a h
 let T:=Jo H a
 let M:Submonoid N :=(xW H₀).map ov
 have :IsLocalization M S:=MvPolynomial.isLocalization (xW H₀) H
 have hcomap : (xW S).comap (nq N S)=xW N := by
   have hinj:qx (nq N S) :=
     MvPolynomial.map_injective _ (N0 H₀ H)
   ext z
   simp only [Submonoid.mem_comap,mem_nonZeroDivisors_iff_ne_zero,map_ne_zero_iff _ hinj]
 have :IsFractionRing N T:= by
   change IsLocalization (xW N) T
   rw [← hcomap]
   exact IsLocalization.localization_localization_isLocalization_of_has_all_units M
     (xW S) T (fun _ hu=>hu.mem_nonZeroDivisors)
 let s :B ≃+* N :=(sumAlgEquiv aU (uL a) (uL h)).toRingEquiv
 let e :F ≃+* T:=IsFractionRing.ringEquivOfRingEquiv s
 let r :=MvPolynomial.mapEquiv (Fin 4) e
 let mapF:lz →+* lJ (Fin 4) F:=Iw (nq aU F)
 let mapT:adi h →+* lJ (Fin 4) T:=Iw (nq H T)
 have ebase (x :B) :
     e (nq B F x)=nq S T (nq N S (s x)) := by
   rw [← IsScalarTower.algebraMap_apply]
   exact IsFractionRing.ringEquivOfRingEquiv_algebraMap s x
 have eC (c:aU) :
     e (nq aU F c)=nq H T (nq aU H c) := by
   change e (nq B F (ov c))= _
   rw [ebase]
   change nq S T (nq N S (sumAlgEquiv _ _ _ (ov c)))= _
   rw [sumAlgEquiv_C_inl,NY ,WX]
   rfl
 have eX₁ (m:uL a) :
     e (nq B F (lI (Sum.inl m)))=nq S T (lI m) := by
   rw [ebase]
   change nq S T (nq N S (sumAlgEquiv _ _ _ (lI (Sum.inl m))))= _
   rw [sumAlgEquiv_X_inl,NY ,MvPolynomial.map_X]
 have eX₂ (m:uL h) :
     e (nq B F (lI (Sum.inr m)))=nq H T (nq H₀ H (lI m)) := by
   rw [ebase]
   change nq S T (nq N S (sumAlgEquiv _ _ _ (lI (Sum.inr m))))= _
   rw [sumAlgEquiv_X_inr,NY ,WX]
   rfl
 have hr₀:r.toRingHom.comp mapF=mapT.comp (aeg h) := by
   apply xm
   · intro c
     simp [r,mapF,mapT,aeg,eC]
     rfl
   · intro i
     simp [r,mapF,mapT,aeg]
 have hr₁:r.toRingHom (Uq a (Sum.inl:uL a→aav a h)) =
     a3g H a := by
   simp [r,Uq,a3g]
   refine p5 rfl fun m _ => ?_
   exact ox (fun c:T=>ov c * ∏ i:Fin 4,lI i^(m i).val)
     (eX₁ m)
 have hr₂:r.toRingHom (Uq h (Sum.inr :uL h→aav a h)) =
     mapT (adK h) := by
   simp [r,mapT,Uq,adK]
   refine p5 rfl fun m _ => ?_
   exact ox (fun c:T=>ov c * ∏ i:Fin 4,lI i^(m i).val)
     (eX₂ m)
 let J:=aI.map mapF ⊔
   oY {Uq a (Sum.inl:uL a→aav a h),
     Uq h (Sum.inr :uL h→aav a h)}
 let J' := (To aI h).map mapT ⊔ oY {a3g H a}
 have hJ:J' = J.map r.toRingHom:= by
   simp only [J,J',To,Ideal.span_insert,Ideal.map_sup,Ideal.map_span,
     Set.image_singleton,Ideal.map_map,hr₀,hr₁,hr₂]
   let rT:=aI.map (mapT.comp (aeg h))
   let first:=oY {a3g H a}
   let second:=oY {mapT (adK h)}
   change (rT ⊔ second) ⊔ first=rT ⊔ (first ⊔ second)
   calc
     _=rT ⊔ (second ⊔ first) :=sup_assoc _ _ _
     _ = _:=ox (rT ⊔ ·) (sup_comm _ _)
 let j:=Ideal.quotientEquiv J J' r hJ
 have hc: (nq T (lJ (Fin 4) T ⧸ J')).comp e.toRingHom =
     j.toRingHom.comp (nq F (lJ (Fin 4) F ⧸ J)) := by
   apply RingHom.ext
   intro c
   change lV J' (ov (e c))=j (lV J (ov c))
   rw [show j (lV J (ov c))=lV J' (r (ov c)) from rfl]
   simp [r]
 exact (Algebra.finrank_eq_of_equiv_equiv e j hc).symm
end
end axe
end
section
namespace vS
noncomputable section
open Polynomial K1 aR dN
open scoped BigOperators
abbrev oe :=Fin 4→aU
abbrev g9:=lJ (Fin 5) aU
def JV (S:ao[X]) :oe := fun i=>j8 (jet S i)
structure Branch (f Q:af 4) (l:ℕ) where
 aI:c9 lz
 r :ℕ
 base : (kC f Q).IsMinimalPrime aI
 high: (l:ℕ∞)≤oA (kC f Q) aI base.isPrime
 bY:YR f aI r
 invariant:Invariant ((oj^[r]) f) aI
 proper :bC (vU ((oj^[r]) f))∉aI
 curve :c9 lz
 divisor : (AX aI (vU ((oj^[r]) f))).IsMinimalPrime curve
 regularCurve :bC (oj ((oj^[r]) f))∉curve
 terminal :
   oA (AX aI (vU ((oj^[r]) f))) curve
     divisor.isPrime≠1∨bC (ZV ((oj^[r]) f))∉curve
namespace Branch
variable {f Q:af 4} {l:ℕ} (b:Branch f Q l)
def g:af 4 :=(oj^[b.r]) f
def sigma :GeoJets :=bC (oj b.g)
abbrev Local:=SD b.sigma
def vN :lz →+* b.Local:=nq lz b.Local
def yu:g9 →+* b.Local :=
  zh (b.vN.comp ov)
    (yU
      (b.vN (ov (-(4 :aU)⁻¹)*bC (pK b.g)) *
        Up b.sigma)
      (fun i=>b.vN (lI i)))
end Branch
def czQ {n:ℕ} (old:Fin 4→Fin n) (p:cy)
    (D:lJ (Fin n) aU) :Prop :=
  ∀ m∈D.support,
    (∑ i:Fin 4,m (old i))≤p.b ∧
    (∑ i:Fin 4,i.val*m (old i))≤p.j∧m (old 3)≤p.t
abbrev VE :=czQ (id :Fin 4→Fin 4)
def agB (p:cy) (d:ℕ) (D:g9) :Prop :=
 czQ uJ p D ∧ ∀ m∈D.support,m (pU 4)≤d
def tC (p:cy) :Shape :=
 ⟨max p.b (p.j+1),p.j+1,min (p.t+1) ((p.j+1)/3)⟩
end
end vS
end
section
namespace vS
noncomputable section
open Polynomial K1 aR dN
open scoped BigOperators
private theorem SZ:qx j8 :=
 (nq lN aU).injective.comp (N0 ao[X] lN)
theorem bTT:qx JV:= by
 intro S T h
 have h₀:=zR h (0:Fin 4)
 exact SZ (by simpa [JV,jet,hasseDeriv_zero'] using h₀)
private theorem bdl (S:ao[X]) (P:af 4) :
  oy (JV S) (bC P)=j8 (cK P S) := by
 rw [bC,MvPolynomial.eval_map]
 change MvPolynomial.eval₂ j8 (⇑j8 ∘ jet S) P= _
 rw [← MvPolynomial.eval₂_comp]
 rfl
def bzb (A:mD K) (s :K→K[X]) (T:mD K) :Prop := by
  classical
  exact T.card = 1 ∨ ∃ x a,(∃ γ∈A,(s γ).eval x≠a) ∧
    T=A.filter (fun γ=>(s γ).eval x=a)
theorem cZX (A:mD K) (s :K→K[X]) (hA:A.Nonempty) :
   ∃ T⊆A,0<T.card∧agC A s T.card∧bzb A s T:= by
 classical
 let candidates :=A.powerset.filter (bzb A s)
 obtain ⟨γ,hγ⟩:=hA
 have hsingle : {γ} ∈ candidates :=
   Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hγ),
     Or.inl (Finset.card_singleton γ)⟩
 obtain ⟨T,hT,hmax⟩:=Finset.exists_max_image candidates Finset.card ⟨_,hsingle⟩
 have hpositive :1≤T.card:= by simpa using hmax _ hsingle
 refine ⟨T,Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1,hpositive,?_,
   (Finset.mem_filter.mp hT).2⟩
 intro x a ha
 exact hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
   Or.inr ⟨x,a,ha,rfl⟩⟩)
end
end vS
end
section
namespace Dr
noncomputable section
open aR dN
open scoped BigOperators
def ChamberBox (p:cy) :Prop :=p.j≤p.b∧3*p.t≤p.j∧0<p.t
def capExponents (p:cy) :Set (Fin 4 →₀ ℕ) :=
 {m | m.degree≤2*p.b∧(∑ i:Fin 4,i.val*m i)≤2*p.j∧m 3≤2*p.t}
instance (p:cy) :vk (capExponents p) :=
 ((OJ (2*p.b)).subset fun _ hm=>hm.1).to_subtype
abbrev dimension (J:c9 lz) :=(oD J).natDegree
def capCoeff (J:c9 lz) (d:ℕ) (p:cy) :ℚ :=
  (oD
    (J.comap (nI aU (capExponents p)).toRingHom)).coeff d
def BE (H :cy→ℚ) :List cy→cy→ℚ
 | []=>H
 | p :: rest=> fun x=>BE H rest (x.plus p) - BE H rest x
def tW (J:c9 lz) (boxes :List cy) :ℚ :=
 BE (capCoeff J boxes.length) boxes ⟨3, 3,1⟩/2^boxes.length
def AN (J P:c9 lz) :ℕ:= by
 classical
 exact if hp:P.IsPrime then (oA J P hp).toNat else 0
def oF (x :vS.oe) :c9 GeoJets :=t9 (oy x)
end
end Dr
end
section
namespace Dr
noncomputable section
open aR dN vS
open scoped BigOperators
lemma aGY (L:ℕ) (p:cy) (hL:0<L) :ChamberBox (bY L p) := by
 refine ⟨(lB.A9 L p).1,(lB.A9 L p).2,?_⟩
 unfold bY
 have h:3≤2*L*(p.j-3)+L+3:= by omega
 exact lt_min (by omega) (Nat.div_pos h (by decide))
lemma bHn {P:af 4} {p:cy} (hP:aO (qG P) p) :VE p (bC P) := by
 intro m hm
 have hm' := Pk j8 P hm
 have hb:=(F9 hm').trans hP.1
 have hj:=(Mj (f := fun m:Fin 4 →₀ ℕ=>m.sum fun i a=>i.val*a) hm').trans hP.2.1
 refine ⟨?_,?_,(R9 3 hm').trans hP.2.2⟩
 · simpa [Bf ,Hw] using hb
 · simpa [Hw] using hj
lemma aPQ {J:c9 lz} (hJ:J.IsPrime) {D:lz} (hD:D∉J) :
  p6 (lV J D) := by
 have :=hJ
 exact SL (mt Ideal.Quotient.eq_zero_iff_mem.mp hD)
lemma aCR {J:c9 lz} {D:lz} (hD:p6 (lV J D)) :
   dimension (J ⊔ oY {D})≤dimension J - 1 :=
 (MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hD yL).1
lemma bEk :dimension (⊥ : c9 lz)=4 := by
 simp [MvPolynomial.natDegree_affineHilbertPolynomial_bot,Gn]
lemma aIT (f Q:af 4) (h:IsRelPrime (bC f) (bC Q)) :
  p6 (lV (oY {bC f}) (bC Q)) := by
 apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
 intro x hx
 obtain ⟨D,rfl⟩:=Nq x
 rw [← nX ,wA,Ideal.mem_span_singleton] at hx
 exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h.dvd_of_dvd_mul_left hx))
lemma aIc (f Q:af 4) :
  kC f Q=oY {bC f} ⊔ oY {bC Q} := by
 rw [kC,← Ideal.span_union]
 rfl
lemma aQG {f Q:af 4} (hf :bC f≠0)
  (hproper :IsRelPrime (bC f) (bC Q))
  {S:c9 lz} (hZ: (kC f Q).IsMinimalPrime S) :dimension S=2 := by
 have :=hZ.isPrime
 rw [aIc] at hZ
 obtain ⟨P,hP,hPZ⟩:=Ideal.exists_minimalPrimes_le (le_sup_left.trans hZ.le)
 have :=hP.isPrime
 have hPdim:=MvPolynomial.natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hf hP
 rw [Gn,xL] at hPdim
 have hPle :P.height≤1 :=Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP
 have hPbot:P ≠ ⊥ := by
  intro heq
  exact hf (Ideal.mem_bot.mp (heq ▸ hP.le (Dz (bC f))))
 have hPheight:P.height = 1 :=vl hPle (by
  simpa [Ideal.height_bot] using Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hPbot))
 obtain ⟨a,ha⟩:=(UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hPheight).principal
 change P=oY {a} at ha
 have hQ:bC Q∉P:= by
  intro hQ
  have hfa :a∣bC f :=Ideal.mem_span_singleton.mp (ha ▸ hP.le (Dz _))
  have hQa :a∣bC Q:=Ideal.mem_span_singleton.mp (ha ▸ hQ)
  exact Ideal.IsPrime.ne_top' (ha.trans (Ideal.span_singleton_eq_top.mpr (hproper hfa hQa)))
 have hmin:S∈(P ⊔ oY {bC Q}).minimalPrimes := by
  refine ⟨⟨hZ.isPrime,xI hPZ (le_sup_right.trans hZ.le)⟩,fun U hU hUZ => ?_⟩
  exact hZ.2 ⟨hU.1,xI (hP.le.trans (le_sup_left.trans hU.2)) (le_sup_right.trans hU.2)⟩ hUZ
 have h:=MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hQ hmin
 change dimension S+1=dimension P at h
 change dimension P+1=4 at hPdim
 omega
lemma ccl {J P:c9 lz} (hP:J.IsMinimalPrime P) :
    0<oA J P hP.isPrime∧oA J P hP.isPrime ≠ ⊤ := by
  have :=hP.isPrime
  let A:=GF P
  let L:=J.map (nq lz A)
  change 0<J4 A (A ⧸ L)∧J4 A (A ⧸ L) ≠ ⊤
  have hmin:Xg A∈L.minimalPrimes := by
    rw [show L=J.map (nq lz A) from rfl,
      IsLocalization.minimalPrimes_map P.primeCompl A,Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A P]
    exact hP
  have hL:L ≠ ⊤ := fun h=>(Rm A).ne_top (top_le_iff.mp (h ▸ hmin.le))
  have :Nontrivial (A ⧸ L) :=Ideal.Quotient.nontrivial_iff.mpr hL
  have :IsArtinianRing (A ⧸ L) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing L hmin
  exact ⟨Module.length_pos,Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L,
        isArtinian_of_surjective_algebraMap (Nq (I:=L))⟩)⟩
lemma a9B {J P:c9 lz} (hP:J.IsMinimalPrime P) :
  (AN J P:ℕ∞)=oA J P hP.isPrime := by
 rw [AN,dite_eq_left hP.isPrime,ENat.natCast_toNat (ccl hP).2]
lemma aFq {J P:c9 lz} (hP:J.IsMinimalPrime P) :0<AN J P:= by
 exact ENat.natCast_lt_natCast.mp ((a9B hP).symm ▸ (ccl hP).1)
lemma btI:qx oF:= by
 intro x y heq
 funext i
 have hm:lI i-MvPolynomial.C (x i)∈oF x := by
  simp [oF,NI]
 rw [heq] at hm
 exact (sub_eq_zero.mp (by simpa [oF,NI] using hm)).symm
lemma cAT (x :oe) :
  sI (t5 x :lz →ₐ[aU] aU) :=
 fun a=>⟨ov a,by simp⟩
lemma c4m (x :oe) : (oF x).IsPrime :=MO _
lemma eMn (x :oe) :dimension (oF x)=0:= by
 let φ:lz →ₐ[aU] GeoField:=t5 x
 let e :=Fz (f :=φ) (cAT x)
 have :Et aU (lz ⧸ oF x) :=JQ e.symm.toLinearEquiv.toLinearMap e.symm.surjective
 exact MvPolynomial.natDegree_affineHilbertPolynomial_eq_zero_iff.mpr inferInstance
lemma bge (x :oe) :tW (oF x) []=1 := by
 let φ:=nI aU (capExponents ⟨3, 3,1⟩)
 have hsφ:sI φ:= by
  apply x7
  intro i
  fin_cases i <;> simp [capExponents,yo]
 let ψ:=(t5 x).comp φ
 let e :=Fz (f :=ψ) ((cAT x).comp hsφ)
 have :Et aU (_ ⧸ t9 ψ) :=
  JQ e.symm.toLinearEquiv.toLinearMap e.symm.surjective
 change (oD (t9 ψ)).coeff 0/(2 :ℚ)^0=1
 rw [ Xp,XG,
  e.toLinearEquiv.finrank_eq,Pc]
 norm_num
lemma cb6 {C:c9 lz} (hC:dimension C=1) {p:cy}
    (hp:ChamberBox p) (x :oe) (hx :C≤oF x) :
    ∃ D:lz ,VE p D ∧D∉C∧oy x D =0:= by
  have h : ∃ i:Fin 4,lI i-MvPolynomial.C (x i)∉C:= by
    by_contra! hall
    let constants :=(lV C).comp ov
    have heq :constants.comp (oy x)=lV C:= by
      apply xm
      · intro a
        simp [constants]
      · intro i
        have hi:=Ideal.Quotient.eq_zero_iff_mem.mpr (hall i)
        rw [yJ,JK] at hi
        simpa [constants] using hi.symm
    have hincl:oF x≤C:= by
      intro D hD
      have hz :oy x D =0:=hD
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← Au heq D,RingHom.comp_apply,hz,qm]
    have hd:=eMn x
    rw [vl hx hincl,hd] at hC
    omega
  obtain ⟨i,hi⟩:=h
  refine ⟨lI i-MvPolynomial.C (x i),?_,hi,by simp⟩
  intro m hm
  have hm' := RC (Fin 4) (lI i) (ov (x i)) hm
  rw [Finset.mem_union] at hm'
  obtain hX | hConst:=hm'
  · rw [Qw] at hX
    have he :=Finset.mem_singleton.mp hX
    subst m
    have hb:1≤p.b:= by have :=hp.1; have :=hp.2.1; have :=hp.2.2; omega
    have hj:i.val≤p.j:= by have :=i.isLt; have :=hp.2.1; have :=hp.2.2; omega
    refine ⟨?_,?_,?_⟩
    · simpa [vj] using hb
    · simpa [vj] using hj
    · simp only [id_eq,vj]
      split <;> have :=hp.2.2 <;> omega
  · have he :m=0:= by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hConst) (by simp [MvPolynomial.coeff_C,Ne.symm h])
    subst m
    simp
end
end Dr
end
section
namespace Dr
noncomputable section
open aR dN vS
open scoped BigOperators
def c1 :Prop :=
  ∀ p:cy ,ChamberBox p →
    capCoeff (⊥ : c9 lz) 4 p=16*(Dn p:ℚ)/32
def c2 :Prop :=
  ∀ (J:c9 lz) (p:cy) (boxes :List cy),
    ChamberBox p→(∀ q∈boxes,ChamberBox q)→dimension J≤boxes.length+1 →
    ∀ D:lz ,VE p D→ p6 (lV J D) →
      tW (J ⊔ oY {D}) boxes≤tW J (p :: boxes)
def c3:Prop :=
  ∀ (J:c9 lz) (boxes :List cy),
    (∀ q∈boxes,ChamberBox q)→dimension J≤boxes.length →
    ∀ S:mD (c9 lz),(∀ P∈S,J.IsMinimalPrime P) →
      (∑ P∈S,(AN J P:ℚ)*tW P boxes)≤tW J boxes
end
end Dr
end
section
namespace aiK
open aR Dr
open scoped Pointwise
theorem OW (p:cy) (e :Fin 4 →₀ ℕ) :
  e∈capExponents p ↔
    e 0+e 1+e 2+e 3≤2*p.b ∧
    e 1+2*e 2 + 3*e 3≤2*p.j∧e 3≤2*p.t:= by
 unfold capExponents
 simp [t4 ,yo ,add_assoc]
theorem biS (p:cy) :0∈capExponents p:= by
 simp [OW]
theorem anN {p q:cy} (hp:ChamberBox p) (hq:ChamberBox q) :
    capExponents p+capExponents q=capExponents (p.plus q) := by
  ext e
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    simp only [OW,qM,KH] at *
    omega
  · intro he
    obtain ⟨hpb,hpj,_⟩:=hp
    obtain ⟨hqb,hqj,_⟩:=hq
    rw [OW] at he
    simp only [qM] at he
    let z :=min (e 3) (2*p.t)
    let z' := e 3 - z
    have hz :z+z' = e 3∧z≤2*p.t∧z' ≤ 2*q.t:= by dsimp [z,z']; omega
    let w:=2*p.j-3*z
    let w' := 2*q.j-3*z'
    have hw:w+3*z=2*p.j∧w' + 3*z' = 2*q.j:= by
      dsimp [w,w']
      omega
    have hhalf : (w+w')/2=w/2+w' / 2 := by
      by_cases h:e 3≤2*p.t
      · have hz' : z' = 0:= by dsimp [z,z']; omega
        omega
      · have hze :z=2*p.t:=min_eq_right (by omega)
        omega
    let y :=min (e 2) (w/2)
    let y' := e 2 - y
    have hy :y+y' = e 2∧2*y≤w∧2*y' ≤ w' := by dsimp [y,y']; omega
    let x :=min (e 1) (w - 2*y)
    let x' := e 1 - x
    have hx :x + x' = e 1∧x+2*y≤w∧x' + 2*y' ≤ w' := by
      dsimp [x,x']
      omega
    let u:=min (e 0) (2*p.b-(x+y+z))
    let u' := e 0 - u
    have hu:u+u' = e 0∧u + x+y+z≤2*p.b ∧
        u' + x' + y' + z' ≤ 2*q.b:= by
      dsimp [u,u']
      omega
    let a :Fin 4 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![u,x,y,z]
    let b:Fin 4 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![u',x',y',z']
    refine ⟨a,(OW p a).mpr ?_,b,(OW q b).mpr ?_,?_⟩
    · change u + x+y+z≤2*p.b∧x+2*y+3*z≤2*p.j∧z≤2*p.t
      omega
    · change u' + x' + y' + z' ≤ 2*q.b∧x' + 2*y' + 3*z' ≤ 2*q.j∧z' ≤ 2*q.t
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact hz.1
theorem aIH (p:cy) (hp:ChamberBox p) (n:ℕ) :
    n•capExponents p=capExponents (p.scale n) := by
  induction n with
  | zero =>
      rw [zE]
      ext e
      simp only [yl,OW,t3 ,zero_mul,vi]
      constructor
      · rintro rfl
        simp
      · rintro ⟨h,_,_⟩
        ext i
        fin_cases i
        · change e 0=0; omega
        · change e 1=0; omega
        · change e 2=0; omega
        · change e 3=0; omega
  | succ n ih =>
      by_cases hn:n=0
      · subst n
        simp [t3]
      have hscaled:ChamberBox (p.scale n) := by
        obtain ⟨hb,hj,ht⟩:=hp
        refine ⟨oz n hb,?_,z9 (Kp hn) ht⟩
        change 3*(n*p.t)≤n*p.j
        rw [xu 3 n]
        exact oz n hj
      rw [G9,ih,anN hscaled hp]
      congr 1
      cases p
      simp [qM,t3 ,Nat.succ_mul]
end aiK
end
section
namespace aiK
open aR Dr Finset
open scoped BigOperators
noncomputable section
private def akm (b j t:ℕ) :=
 Σ z :Fin (2*t+1),Σ y :Fin ((2*j-3*z.val)/2+1),
   Σ x :Fin (2*j-3*z.val - 2*y.val+1),
     Fin (2*b-(z.val+y.val + x.val)+1)
private def dE9 (p:cy) (hp:ChamberBox p) :
  capExponents p ≃ akm p.b p.j p.t where
 toFun e := by
  have he :=(OW p e.val).mp e.property
  have hb:=he.1
  have hj:=he.2.1
  have ht:=he.2.2
  let z :Fin (2*p.t+1) :=⟨e.val 3,by omega⟩
  let y :Fin ((2*p.j-3*z.val)/2+1) :=⟨e.val 2,by dsimp [z]; omega⟩
  let x :Fin (2*p.j-3*z.val - 2*y.val+1) :=⟨e.val 1,by dsimp [z,y]; omega⟩
  exact ⟨z,y,x,⟨e.val 0,by dsimp [z,y,x]; omega⟩⟩
 invFun a := by
  rcases a with ⟨z,y,x,u⟩
  have hz :=z.isLt
  have hy :=y.isLt
  have hx :=x.isLt
  have hu:=u.isLt
  have hb:=hp.1
  have hj:=hp.2.1
  refine ⟨Finsupp.equivFunOnFinite.symm ![u.val,x.val,y.val,z.val],(OW p _).mpr ?_⟩
  change u.val + x.val+y.val+z.val≤2*p.b ∧
   x.val+2*y.val+3*z.val≤2*p.j∧z.val≤2*p.t
  omega
 left_inv e := by
  apply vH
  ext i
  fin_cases i <;> rfl
 right_inv a := by
  rcases a with ⟨⟨z,hz⟩,⟨y,hy⟩,⟨x,hx⟩,⟨u,hu⟩⟩
  rfl
private theorem bw6 (a d:ℚ) (n:ℕ) :
   (∑ x∈th n,(a+d*(x :ℚ)))=n*a+d*n*((n:ℚ) - 1)/2 := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [yB,ih]
   push_cast
   ring
private def slice (W C:ℕ) :ℚ :=
 ((C:ℚ)+1-(W:ℚ)/2) *
   ((W/2 :ℕ)+(1 :ℚ))*((W/2 :ℕ)+(1 :ℚ)+(W % 2 :ℕ))
private theorem cpR (W C:ℕ) (h:W≤C) :
    (∑ y∈th (W/2+1),∑ x∈th (W - 2*y+1),
      ((C-(y + x)+1 :ℕ) :ℚ))=slice W C:= by
  calc
    _ = ∑ y∈th (W/2+1),
        (((C:ℚ)+1-(W:ℚ)/2)*((W:ℚ)+1 - 2*(y :ℚ))) := by
      apply p5 rfl
      intro y hy
      have hy' := mem_range.mp hy
      calc
        _ = ∑ x∈th (W - 2*y+1),((C:ℚ) - y+1+(-1)*(x :ℚ)) := by
          apply p5 rfl
          intro x hx
          have hx' := mem_range.mp hx
          have hxy :y + x≤C:= by omega
          push_cast [vG hxy]
          ring
        _ = _:= by
          rw [bw6]
          have h2y :2*y≤W:= by omega
          push_cast [vG h2y]
          ring
    _ = _:= by
      rw [← uz]
      have hlin (y :ℕ) : (W:ℚ)+1 - 2*(y :ℚ)=(W:ℚ)+1+(-2)*(y :ℚ) := by
        ring
      simp_rw [hlin]
      rw [bw6]
      have hW: (W:ℚ)=2*((W/2 :ℕ) :ℚ)+((W % 2 :ℕ) :ℚ) := by
        exact_mod_cast (show W=2*(W/2)+W % 2 by omega)
      unfold slice
      push_cast
      rw [hW]
      ring
private theorem dET (p:cy) (hp:ChamberBox p) :
   ((capExponents p).ncard:ℚ) =
     ∑ z∈th (2*p.t+1),slice (2*p.j-3*z) (2*p.b - z) := by
 classical
 let:pL (akm p.b p.j p.t) := by unfold akm; infer_instance
 rw [← zi ,Nat.card_congr (dE9 p hp),Gn]
 change (GB (Σ z :Fin (2*p.t+1),Σ y :Fin ((2*p.j-3*z.val)/2+1),
   Σ x :Fin (2*p.j-3*z.val - 2*y.val+1),
     Fin (2*p.b-(z.val+y.val + x.val)+1)) :ℚ)= _
 simp only [Sv,xL,Nat.cast_sum]
 rw [Gk (fun z => ∑ y :Fin ((2*p.j-3*z)/2+1),
   ∑ x :Fin (2*p.j-3*z - 2*y.val+1),((2*p.b-(z+y.val + x.val)+1 :ℕ) :ℚ))]
 apply p5 rfl
 intro z _
 have hW:2*p.j-3*z≤2*p.b - z := by have :=hp.1; omega
 rw [← cpR _ _ hW]
 rw [Gk (fun y => ∑ x :Fin (2*p.j-3*z - 2*y+1),
   ((2*p.b-(z+y + x.val)+1 :ℕ) :ℚ))]
 apply p5 rfl
 intro y _
 rw [Gk (fun x=>((2*p.b-(z+y + x)+1 :ℕ) :ℚ))]
 simp only [Nat.sub_sub,LP]
private def ayN (b j i:ℚ) :ℚ:=(j-3*i+1)^2*(2*b+1 - j+i)
private def aOY (b j i:ℚ) :ℚ :=
 (j-3*i - 1)*(j-3*i)*(2*b+3/2 - j+i)
private theorem bwz (b j i:ℕ) (hi:3*i≤j) (hb:j≤b) :
  slice (2*j-3*(2*i)) (2*b - 2*i)=ayN b j i:= by
 have hW:2*j-3*(2*i)=2*(j-3*i) := by omega
 have hC:2*i≤2*b:= by omega
 rw [hW]
 simp only [slice,ayN,Nat.mul_div_cancel_left _ (by decide :0<2),
  Nat.mul_mod_right,Nat.cast_zero,y5 ]
 push_cast [vG hi,vG hC]
 ring
private theorem cpT (b j i:ℕ) (hi:3*i+3≤j) (hb:j≤b) :
  slice (2*j-3*(2*i+1)) (2*b-(2*i+1))=aOY b j i:= by
 have hW:3*(2*i+1)≤2*j:= by omega
 have hC:2*i+1≤2*b:= by omega
 have hdiv : (2*j-3*(2*i+1))/2=j-(3*i+2) := by omega
 have hmod: (2*j-3*(2*i+1)) % 2=1 := by omega
 simp only [slice,aOY,hdiv,hmod]
 push_cast [vG hW,vG hC,vG (show 3*i+2≤j by omega)]
 ring
private theorem sum_pair (f :ℕ→ℚ) (n:ℕ) :
   (∑ z∈th (2*n),f z) = ∑ i∈th n,(f (2*i)+f (2*i+1)) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [Nat.mul_succ,show 2*n+2=(2*n+1)+1 by omega]
   rw [yB,yB,ih,yB]
   ring
private def pair (b j i:ℚ) :ℚ:=ayN b j i+aOY b j i
private def aPc (b j n:ℚ) :ℚ :=
 let f :=pair b j
 n*f 0+n*(n - 1)/2*(f 1 - f 0) +
   n*(n - 1)*(n - 2)/6*(f 2 - 2*f 1+f 0) +
   n*(n - 1)*(n - 2)*(n-3)/24*(f 3-3*f 2 + 3*f 1 - f 0)
private theorem cbf (b j:ℚ) (n:ℕ) :
   (∑ i∈th n,pair b j i)=aPc b j n:= by
 induction n with
 | zero=>simp [aPc]
 | succ n ih =>
   rw [yB,ih]
   push_cast
   dsimp [aPc,pair,ayN,aOY]
   ring
private theorem bYW (p:cy) (hp:ChamberBox p) :
  ((capExponents p).ncard:ℚ)=aPc p.b p.j p.t+ayN p.b p.j p.t:= by
 rw [dET p hp,yB,sum_pair,bwz _ _ _ hp.2.1 hp.1,← cbf]
 congr 1
 apply p5 rfl
 intro i hi
 have hi' := mem_range.mp hi
 rw [bwz _ _ _ (by have :=hp.2.1; omega) hp.1,
  cpT _ _ _ (by have :=hp.2.1; omega) hp.1]
 rfl
def aIp (p:cy) :wB ℚ :=
  let b:ℚ:=p.b
  let j:ℚ:=p.j
  let t:ℚ:=p.t
  oZ (16*(Dn p:ℚ)/32)*p9 ^4 +
    oZ (2*b*j^2+2*b*j*t - 3*b*t^2 - j^3+(3/2)*j^2*t -
      (11/2)*j*t^2+(13/2)*t^3)*p9 ^3 +
    oZ (4*b*j - b*t - j^2+2*j*t - (5/2)*t^2)*p9 ^2 +
    oZ (2*b+j - t/2)*p9 ^1+Polynomial.C 1
theorem cWV (p:cy) :
  (aIp p).coeff 4=16*(Dn p:ℚ)/32 := by
 simp only [aIp,Ef ,Un,Polynomial.coeff_C]
 norm_num
theorem cWW (p:cy) (hp:ChamberBox p) (n:ℕ) (hn:0<n) :
  (aIp p).eval (n:ℚ)=((capExponents (p.scale n)).ncard:ℚ) := by
 have hscaled:ChamberBox (p.scale n) := by
  obtain ⟨hb,hj,ht⟩:=hp
  refine ⟨oz n hb,?_,z9 hn ht⟩
  change 3*(n*p.t)≤n*p.j
  rw [xu 3 n]
  exact oz n hj
 rw [bYW _ hscaled]
 simp only [aIp,XJ,TI,Polynomial.eval_pow,
  Re,PM,aPc,pair,ayN,aOY,t3 ,Dn]
 push_cast
 ring
end
end aiK
end
section
namespace aY3
noncomputable section
open Polynomial MvPolynomial aR Ex dN vS lB
open Sr.Weight
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
theorem avh (w:Fin 4→ℕ) (Δ:ℕ)
   (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) {g:af 4} {B:ℕ}
   (hB:w 3≤B) (hg:W w g≤B) (n:ℕ) :
   W w (su g n)≤w 0+n*(2*(B - w 3)+Δ) := by
 induction n with
 | zero=>simpa only [su,zero_mul,add_zero] using abx (R:=ao[X]) w 0
 | succ n ih =>
   simpa only [su,FR,Ar,LP] using
     step_bound w Δ hshift hB hg ih (2*n)
private theorem aDr (w:Fin 4→ℕ) (f :af 4) (r :ℕ) :
   W w ((oj^[r]) f)≤W w f := by
 induction r with
 | zero=>exact le_rfl
 | succ r ih =>
   rw [Function.iterate_succ_apply']
   exact (weightedTotalDegree_pderiv_le w 3 _).trans ih
theorem a6c {P:lz} {p:cy} (h:yy P p) :VE p P:= by
 intro m hm
 have h₁:=G8 (1 :Fin 4→ℕ) hm
 have h₂:=(G8 Gr hm).trans h.2.1
 have h₃:=(G8 (Av (3:Fin 4) (1 :ℕ)) hm).trans
   (by simpa only [Ea] using h.2.2)
 rw [weightedTotalDegree_one] at h₁
 refine ⟨?_,?_,?_⟩
 · have ht:=h₁.trans h.1
   rw [Df] at ht
   simpa only [id_eq,Pi.one_apply,yQ,sS] using ht
 · rw [Df] at h₂
   simpa only [id_eq,yQ,G7] using h₂
 · simpa only [id_eq,Finsupp.weight_single_one_apply] using h₃
private def topWeight:Fin 4→ℕ:=Av 3 1
theorem ecy (P:af 4) (p:cy) (L:ℕ)
   (hb:W 1 P≤1+2*L*(p.b - 1))
   (hj:W Gr P≤2*L*(p.j-3)+L+3)
   (ht:W topWeight P≤2*L*(p.t - 1)+L+1) :
   yy (bC P) (bY L p) := by
 apply abr
 refine ⟨?_,?_,?_⟩
 · change P.totalDegree≤ max _ _
   exact (by simpa only [weightedTotalDegree_one] using hb :
     P.totalDegree≤1+2*L*(p.b - 1)).trans (PA  _ _)
 · change qE P≤_
   rwa [C6]
 · change P.degreeOf 3≤ min _ _
   apply le_min
   · simpa only [topWeight,Ea] using ht
   · have h:=(a9d P).trans hj
     omega
theorem a86 {g P:af 4} {p:cy} {L:ℕ} (hB:aO (qG g) p)
   (hp:bF p) (ht:0<p.t)
   (bound : ∀ (w:Fin 4→ℕ) (Δ d₀ B:ℕ),
     (∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)→(∀ i,w i≤d₀) →
     w 3≤B→W w g≤B→W w P≤d₀+2*L*(B - w 3)+L*Δ) :
   yy (bC P) (bY L p) := by
 have hb:1≤p.b:= by have :=hp.1; have :=hp.2; omega
 have hj:3≤p.j:= by have :=hp.2; omega
 have h₁:W 1 g≤p.b:= by simpa only [qG,weightedTotalDegree_one] using hB.1
 have h₂:W Gr g≤p.j:= by simpa only [qG,C6] using hB.2.1
 have h₃:W topWeight g≤p.t:= by
   simpa only [topWeight,qG,Ea] using hB.2.2
 have hshift : ∀ i:Fin 3,topWeight i.succ≤topWeight i.castSucc+1 := by
   intro i
   fin_cases i <;> decide
 have hw : ∀ i,topWeight i≤1 := by
   intro i
   fin_cases i <;> decide
 have hw3:topWeight 3=1 := by decide
 apply ecy
 · have h:=bound 1 0 1 p.b (fun _=> by simp) (fun _=>le_rfl) hb h₁
   simpa only [Pi.one_apply,vi ,y5 ] using h
 · have h:=bound Fin.val 1 3 p.j (fun _=> by rfl)
     (fun j:Fin 4=>UP  j.isLt) hj h₂
   change W Gr  P≤3+2*L*(p.j-3)+L*1 at h
   simpa only [sS ,S1 ,Mz ,LP ] using h
 · have h:=bound topWeight 1 1 p.t hshift hw (hw3.symm ▸ ht) h₃
   simpa only [hw3,sS ,S1 ,Mz ,LP] using h
theorem aXG (w:Fin 4→ℕ) {g:af 4} {B:ℕ} (hg:W w g≤B) (a :ℕ) :
   W w (oj g^a)≤a*(B - w 3) :=
 (weightedTotalDegree_pow_le _ _ _).trans
   (oz _ ((aAA w g).trans (Nat.sub_le_sub_right hg _)))
theorem bH1 {g:af 4} {p:cy} (hB:aO (qG g) p) (hp:bF p)
  (ht:0<p.t) {n L:ℕ} (hn:n≤L) :
  yy (bC (su g n)) (bY L p) := by
 apply a86 hB hp ht
 intro w Δ d₀ B hshift hw hwB hg
 calc
  _≤w 0+n*(2*(B - w 3)+Δ) :=avh w Δ hshift hwB hg n
  _≤d₀+L*(2*(B - w 3)+Δ) :=
    Eg (hw 0) (XB _ hn)
  _ = _:= by ring
end
end aY3
end
section
namespace aiK
open aR dN Dr MvPolynomial
open scoped Pointwise
noncomputable section
private theorem aDS (S:Set (Fin 4 →₀ ℕ)) (n:ℕ) (e :Fin 4 →₀ ℕ)
   (he :e∈n•S) :
   ∃ P:lJ S aU,P.totalDegree≤n ∧
     nI aU S P=n5 e 1 := by
 induction n generalizing e with
 | zero =>
     simp only [zE,yl] at he
     subst e
     exact ⟨1,by simp,by simp⟩
 | succ n ih =>
     rw [G9] at he
     obtain ⟨a,ha,b,hb,rfl⟩:=he
     obtain ⟨P,hn,hP⟩:=ih a ha
     refine ⟨P*lI ⟨b,hb⟩,(totalDegree_mul _ _).trans ?_,?_⟩
     · simpa only [totalDegree_X] using VH hn 1
     · rw [nX ,hP,Dv,II,sS]
private theorem aCx (p:cy) (hp:ChamberBox p) :
  sI (nI aU (capExponents p)) := by
 apply x7
 intro i
 have ⟨hb,hj,ht⟩:=hp
 fin_cases i <;> norm_num [OW,vj] <;> omega
theorem dE2 (p:cy) (hp:ChamberBox p) (n:ℕ) :
    p7
        ((⊥ : c9 lz).comap (nI aU (capExponents p)).toRingHom) n =
      (capExponents (p.scale n)).ncard:= by
  classical
  let φ:=nI aU (capExponents p)
  let I:=t9 φ.toRingHom
  let g: (lJ (capExponents p) aU ⧸ I) ≃ₐ[aU] GeoJets :=
    Fz (f :=φ) (aCx p hp)
  have hg (P:lJ (capExponents p) aU) :g (lV I P)=φ P :=
    Ideal.quotientKerAlgEquivOfSurjective_mk (f :=φ) (aCx p hp) P
  let M:=qJ aU (capExponents (p.scale n))
  have hmap : (uW I n).map g.toLinearEquiv.toLinearMap=M:= by
    apply vl
    · rintro _ ⟨v,hv,rfl⟩
      obtain ⟨P,hP,rfl⟩:=mem_quotientDegreeLE.mp hv
      change g (lV I P)∈M
      rw [hg]
      dsimp [M]
      rw [← aIH p hp n]
      exact IT (biS p) hP
    · dsimp [M]
      rw [zm,Kc]
      rintro _ ⟨e,he,rfl⟩
      rw [← aIH p hp n] at he
      obtain ⟨P,hN,hP⟩:=aDS _ n e he
      refine ⟨lV I P,Nj hN,?_⟩
      change g (lV I P)=n5 e 1
      rw [hg]
      exact hP
  change p7 I n= _
  calc
    _=pz aU ((uW I n).map g.toLinearEquiv.toLinearMap) :=
      (g.toLinearEquiv.finrank_map_eq _).symm
    _=pz aU M:= by rw [hmap]
    _ = _:= by
      rw [LO (C9 aU _),zi]
theorem proof :Dr.c1 := by
 intro p hp
 let I:=(⊥ : c9 lz).comap (nI aU (capExponents p)).toRingHom
 have hP:oD I=aIp p:= by
   apply Polynomial.eq_of_eventually_atTop_eval_natCast_eq
   filter_upwards [z8 I,WY 1]
     with n hn hn₁
   rw [hn,dE2 p hp n,cWW p hp n hn₁]
 change (oD I).coeff 4= _
 rw [hP,cWV]
end
end aiK
end
section
namespace B8
noncomputable section
open aR dN vS
open scoped BigOperators
abbrev Exponent:=Fin 5 →₀ ℕ
abbrev lS:=Fin 5→cy×ℕ
def bF (p:cy) :Prop :=p.j≤p.b∧3*p.t≤p.j
def Qj (a :cy×ℕ) (m:Exponent) :Prop :=
 (∑ i:Fin 4,m i.castSucc)≤a.1.b ∧
 (∑ i:Fin 4,i.val*m i.castSucc)≤a.1.j ∧
 m (uJ (3:Fin 4))≤a.1.t∧m (pU 4)≤a.2
def Nl (a :cy×ℕ) :Set Exponent :=
 {m | Qj (a.1.scale 2,2*a.2) m}
instance gQj (a :cy×ℕ) :vk (Nl a) := by
 apply Set.Finite.to_subtype
 refine (OJ (2*a.1.b+2*a.2)).subset ?_
 intro m hm
 change m.degree≤_
 rw [t4 ,FK]
 exact Eg hm.1 hm.2.2.2
def Admissible (B:lS) :Prop :=
 (∀ i,bF (B i).1)∧(∀ v :Fin 5,∃ i,qz v 1∈Nl (B i))
def H7 (B:lS) (t:Fin 5→ℕ) :Set Exponent :=
  {m | ∃ u: (i:Fin 5)→Fin (t i)→Exponent,
    (∀ i j,u i j∈Nl (B i))∧m = ∑ i,∑ j,u i j}
instance gPM (B:lS) (t:Fin 5→ℕ) :
   vk (H7 B t) := by
 let addExponents (u: (i:Fin 5)→Fin (t i)→Nl (B i)) :Exponent :=
   ∑ i,∑ j,(u i j).val
 have heq :H7 B t=v9 addExponents := by
   ext m
   constructor
   · rintro ⟨u,hu,rfl⟩
     exact ⟨fun i j=>⟨u i j,hu i j⟩,rfl⟩
   · rintro ⟨u,rfl⟩
     exact ⟨fun i j=>(u i j).val,fun i j=>(u i j).property,rfl⟩
 rw [heq]
 exact (Set.finite_range _).to_subtype
def tW (B:lS) (P:c9 g9) (I:mD (Fin 5)) :ℚ :=
  (∑ J∈I.powerset,(-1 :ℚ)^(I.card-J.card) *
    (oD (zg
      (nI aU (H7 B (fun i=>if i∈J then 2 else 1)))
      P)).coeff I.card)/(2 :ℚ)^I.card
def TB (P:c9 g9) (d:ℕ) :Prop :=
 vZ (g9 ⧸ P)=((d:ℕ∞) :WithBot ℕ∞)
def MH (P:c9 g9) (d:ℕ) :Prop :=
 vZ (g9 ⧸ P)≤((d:ℕ∞) :WithBot ℕ∞)
def i9 (P:c9 g9) (D:g9) :c9 g9 :=
 P ⊔ oY {D}
def Ro (J P:c9 g9) (hp:P.IsPrime) :ℕ∞ :=
 letI:=hp
 let A:=GF P
 J4 A (A ⧸ J.map (nq g9 A))
structure Component (P:c9 g9) (D:g9) (C:c9 g9) (w:ℕ) :Prop where
 minimal: (i9 P D).IsMinimalPrime C
 length_le : (w:ℕ∞)≤Ro (i9 P D) C minimal.isPrime
def bTp:Prop :=
  ∀ (B:lS),Admissible B →
    ∀ (P:c9 g9) (I:mD (Fin 5)) (i:Fin 5),
      i∉I→MH P (I.card+1) →
      ∀ (D:g9),agB (B i).1 (B i).2 D→ p6 (lV P D) →
        tW B (i9 P D) I≤tW B P (vh i I)
def bQI:Prop :=
  ∀ (B:lS),Admissible B →
    ∀ (J:c9 g9) (I:mD (Fin 5)),MH J I.card →
      ∀ {ι:Type} (S:mD ι) (C:ι→ c9 g9) (w:ι→ℕ),
        Set.InjOn C (S:Set ι) →
        (∀ a∈S,∃ h:J.IsMinimalPrime (C a),(w a :ℕ∞)≤Ro J (C a) h.isPrime) →
        (∑ a∈S,(w a :ℚ)*tW B (C a) I)≤tW B J I
def aYC:Prop :=
  ∀ (B:lS),Admissible B →
    ∀ (P:c9 g9) (I:mD (Fin 5)) (i:Fin 5),
      P.IsPrime→i∉I→TB P (I.card+1) →
      ∀ (D:g9),agB (B i).1 (B i).2 D→D∉P →
        ∀ {ι:Type} (S:mD ι) (C:ι→ c9 g9) (w:ι→ℕ),
          Set.InjOn C (S:Set ι)→(∀ a∈S,Component P D (C a) (w a)) →
          (∑ a∈S,(w a :ℚ)*tW B (C a) I)≤tW B P (vh i I)
def qK:lz →+* g9 :=
 (zf uJ).toRingHom
def cylinder (P:c9 lz) :c9 g9:=P.map qK
def oF (z :Fin 5→aU) :c9 g9 :=
 t9 (oy z)
end
end B8
end
section
namespace B8
noncomputable section
open dN vS
open scoped BigOperators
theorem bms {a :cy×ℕ} {D:g9} :
   agB a.1 a.2 D ↔ ∀ m∈D.support,Qj a m:= by
 constructor
 · intro h m hm
   exact ⟨(h.1 m hm).1,(h.1 m hm).2.1,(h.1 m hm).2.2,h.2 m hm⟩
 · intro h
   exact ⟨fun m hm=>⟨(h m hm).1,(h m hm).2.1,(h m hm).2.2.1⟩,
    fun m hm=>(h m hm).2.2.2⟩
theorem cBb (a :cy×ℕ) :Qj a 0:= by
 simp [Qj]
theorem blp {a :cy×ℕ}
   (h:1≤a.1.b∧3≤a.1.j∧1≤a.1.t∧1≤a.2) (i:Fin 5) :
   Qj a (qz i 1) := by
 obtain ⟨hb,hj,ht,hd⟩:=h
 let m:Exponent:=qz i 1
 have hold: (∑ j:Fin 4,m j.castSucc)≤1 := calc
   _ ≤ ∑ j:Fin 5,m j:= by
     rw [FK (n:=4)]
     exact qy _ _
   _=1 := by
     rw [← t4]
     exact VO i 1
 have hindex : (∑ j:Fin 4,j.val*m j.castSucc)≤3:= calc
   _ ≤ ∑ j:Fin 4,3*m j.castSucc:= by
     apply t6
     intro j _
     exact XB _ (by omega)
   _≤3:= by rw [← uz]; omega
 have hsingle (j:Fin 5) :m j≤1 := by
   simp only [m,vj]
   split <;> decide
 exact ⟨hold.trans hb,hindex.trans hj,(hsingle _).trans ht,(hsingle _).trans hd⟩
private theorem cHR (a :cy×ℕ) (s :aU) :
   agB a.1 a.2 (ov s) := by
 classical
 apply bms.mpr
 intro m hm
 by_cases hs :s=0
 · simp [hs] at hm
 · rw [MvPolynomial.support_C,Kh hs,RP] at hm
   exact hm ▸ cBb a
private theorem bYM {a :cy×ℕ}
   (h:1≤a.1.b∧3≤a.1.j∧1≤a.1.t∧1≤a.2)
   (z :Fin 5→aU) (i:Fin 5) :
   agB a.1 a.2 (lI i-MvPolynomial.C (z i)) := by
 apply bms.mpr
 intro m hm
 rcases Finset.mem_union.mp (RC _ _ _ hm) with hX | hC
 · rw [Qw ,RP] at hX
   exact hX ▸ blp h i
 · exact bms.mp (cHR a (z i)) m hC
private theorem eval_surjective (z :Fin 5→aU) :
  sI (oy z) :=
 fun a=>⟨ov a,Pv _⟩
private theorem a6D:qx oF:= by
 intro x y h
 funext i
 have hx :lI i-MvPolynomial.C (x i)∈oF x := by
  simp [oF,NI]
 have hy :=RingHom.mem_ker.mp (h ▸ hx :_∈oF y)
 rw [yJ,MvPolynomial.eval_X,Pv,JK] at hy
 exact hy.symm
private theorem bge (B:lS) (z :Fin 5→aU) :
  tW B (oF z) ∅ = 1 := by
 let A:=H7 B (fun _=>1)
 let φ:=(t5 z).comp (nI aU A)
 have hφ:sI φ:= fun a=>⟨ov a,φ.commutes a⟩
 have heq : (oF z).comap (nI aU A)=t9 φ:=rfl
 let e :=Fz hφ
 let:=JQ e.symm.toLinearMap e.symm.surjective
 unfold tW
 simp only [Finset.powerset_empty,Finset.sum_singleton,Finset.card_empty,tsub_self,
  pow_zero,Ar,div_one]
 change (oD
  ((oF z).comap (nI aU A))).coeff 0=1
 rw [heq,Xp,XG,
  e.toLinearEquiv.finrank_eq,Pc,Dw]
theorem cak {J C:c9 g9} (h:J.IsMinimalPrime C) :
  (1 :ℕ∞)≤Ro J C h.isPrime := by
 let:=h.isPrime
 let A:=GF C
 have hne :J.map (nq g9 A) ≠ ⊤ := by
  have hle :=Ideal.map_mono (f :=nq g9 A) h.le
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal C A] at hle
  exact ne_top_of_le_ne_top (Rm A).ne_top hle
 let:Nontrivial (A ⧸ J.map (nq g9 A)) :=Ideal.Quotient.nontrivial_iff.mpr hne
 exact Order.one_le_iff_ne_zero.mpr Module.length_pos.ne'
private theorem cb3 {C:c9 g9} (hprime :C.IsPrime) (hdim:TB C 1)
   {z :Fin 5→aU} (hz :C≤oF z) {D:g9} (hproper :D∉C)
   (hD:oy z D =0) :Component C D (oF z) 1 := by
 let:=hprime
 let: (oF z).IsPrime :=MO (oy z)
 let:Ring.KrullDimLE 1 (g9 ⧸ C) :=Ring.krullDimLE_iff.mpr (le_of_eq hdim)
 have hmin: (i9 C D).IsMinimalPrime (oF z) := by
   refine ⟨⟨MO _,xI hz ((G2 _).mpr hD)⟩,?_⟩
   intro P hP hPle
   have :=hP.1
   have hCP:C≤P:=le_sup_left.trans hP.2
   have hDJ:D∈i9 C D :=
     (Cy :oY {D} ≤ i9 C D) (In (by simp))
   have hDP:D∈P:=hP.2 hDJ
   let π:=lV C
   have hne :P.map π ≠ ⊥ := by
     intro h
     have hmem:=Ideal.mem_map_of_mem π hDP
     rw [h,Ideal.mem_bot,wA] at hmem
     exact hproper hmem
   have hmax : (P.map π).IsMaximal :=
     (Xx hCP).isMaximal_of_ne_bot hne
   have htop:=(Xx
     (p:=oF z) hz).ne_top
   have hEq:=hmax.eq_of_le htop (Ideal.map_mono (f :=π) hPle)
   have hEq' := ox (zg π) hEq
   rw [Pj hCP,Pj hz] at hEq'
   exact hEq'.ge
 exact ⟨hmin,cak hmin⟩
private theorem bdx {C:c9 g9} {z :Fin 5→aU}
   (h:C<oF z) :
   ∃ i:Fin 5,lI i-MvPolynomial.C (z i)∉C:= by
 by_contra! hmem
 let π:=lV C
 have hmaps :π=π.comp (MvPolynomial.C.comp (oy z)) := by
   apply xm
   · intro a
     simp
   · intro i
     have heq :=Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
     rw [yJ,JK] at heq
     simpa using heq
 apply GR h
 intro D hD
 have hz :oy z D =0:=RingHom.mem_ker.mp hD
 apply Ideal.Quotient.eq_zero_iff_mem.mp
 change π D =0
 calc
   π D =π (ov (oy z D)) :=RingHom.congr_fun hmaps D
   _=0:= by rw [hz,qm,qm]
theorem btG (H :aYC)
    (B:lS) (hB:Admissible B)
    (ha :1≤(B 4).1.b∧3≤(B 4).1.j∧1≤(B 4).1.t∧1≤(B 4).2)
    (C:c9 g9) (hprime :C.IsPrime) (hdim:TB C 1)
    (U:mD (Fin 5→aU)) (hU : ∀ z∈U,C≤oF z)
    (hslice :U.card≤1 ∨ ∃ D,agB (B 4).1 (B 4).2 D ∧D∉C ∧
      ∀ z∈U,oy z D =0) :
    (U.card:ℚ)≤tW B C {4} := by
  classical
  have aM7 (D:g9) (hB' : agB (B 4).1 (B 4).2 D) (hproper :D∉C)
      (hD : ∀ z∈U,oy z D =0) : (U.card:ℚ)≤tW B C {4} := by
    have hb:=H B hB C ∅ 4 hprime (by simp) hdim D hB' hproper U oF (fun _=>1)
      a6D.injOn (fun z hz=>cb3 hprime hdim (hU z hz) hproper (hD z hz))
    simpa [bge] using hb
  rcases hslice with hone | ⟨D,hD,hp,hz⟩
  · by_cases hempty :U = ∅
    · apply aM7 (ov 1) (cHR (B 4) 1)
      · rw [zS]
        exact (Ideal.ne_top_iff_one C).mp hprime.ne_top
      · simp [hempty]
    obtain ⟨z,hz⟩:=Finset.nonempty_iff_ne_empty.mpr hempty
    have hlt:C<oF z := by
      refine lt_of_le_of_ne (hU z hz) ?_
      intro h
      rw [h,TB,oF] at hdim
      have e :=(oy z).quotientKerEquivOfSurjective (eval_surjective z)
      rw [e.ringKrullDim,LR] at hdim
      exact (by decide : (0:WithBot ℕ∞)≠1) hdim
    obtain ⟨i,hi⟩:=bdx hlt
    apply aM7 _ (bYM ha z i) hi
    intro y hy
    have hyz :=Finset.card_le_one.mp hone y hy z hz
    subst y
    simp
  · exact aM7 D hD hp hz
end
end B8
end
section
namespace aA5
noncomputable section
open Polynomial K1 aR dN vS
open scoped BigOperators
abbrev T9:af 4 →ₐ[ao[X]] af 5:=zf uJ
abbrev RT:af 5 →+* g9:=Iw j8
def cGs (P:af 5) :af 5 :=
 ∑ m∈P.support,n5 m (pC (P.coeff m))
def ay1 (P:af 5) :af 5 :=
  cGs P +
    ∑ i:Fin 4,ov (oZ ((i.val+1 :ℕ) :ao)) *
      lI i.succ*qU i.castSucc P
def ao6 (g:af 4) :af 5 :=
  T9 (pK g) +
    ov (4 :ao[X])*T9 (oj g)*lI (pU 4)
def bp7 (g:af 4) :af 5 :=
 ov (oZ (-(4 :ao)⁻¹))*ay1 (ao6 g)
def numerator (g:af 4) :ℕ→af 5
  | 0=>MvPolynomial.C (24 :ao[X])*MvPolynomial.X (Fin.last 4)
  | k+1 =>
    let S:=T9 (oj g)
    let P:=numerator g k
    S*ay1 P+bp7 g*qU (pU 4) P -
      (k :af 5)*ay1 S*P
def denominator (g:af 4) (k :ℕ) :af 5:=T9 (oj g)^k
def CJ (g:af 4) (k i:ℕ) :af 5 :=
  if hi:i<4 then
    ov (oZ (i.factorial:ao)) *
      T9 (lI ⟨i,hi⟩)*denominator g k
  else numerator g (i-4)*denominator g (k-(i-4))
theorem cba (g:af 4) (k :ℕ) :CJ g k (k+4)=numerator g k := by
 rw [CJ,dite_eq_right (by omega : ¬ k+4<4)]
 simp [denominator]
end
end aA5
end
section
namespace aA5
noncomputable section
open Polynomial K1 aR dN vS
open scoped BigOperators
variable {f Q:af 4} {l:ℕ}
@[simp] private theorem cad (b:Branch f Q l) (a :aU) :
   b.yu (ov a)=b.vN (ov a) := by
  simp [Branch.yu]
private abbrev iy (T:ao[X]) (i:ℕ) :GeoField :=
 j8 ((pC (R:=ao))^[i] T)
private theorem ajW (T:ao[X]) (i:ℕ) :
   (pC (R:=ao))^[i] T =
     oZ (i.factorial:ao)*hasseDeriv i T:= by
 ext m
 rw [coeff_iterate_derivative,VC,hasseDeriv_coeff,
   Nat.descFactorial_eq_factorial_mul_choose]
 simp only [nsmul_eq_mul,Du,v8]
private abbrev const:ao →+* GeoField:=j8.comp oZ
private abbrev centre :GeoField:=j8 p9
private def asv (x :ao) (i:ℕ) :GeoField :=
 (i.factorial:aU)⁻¹*(const x - centre)^i
private theorem factorial_ne_zero {i:ℕ} (hi:i<K1.p) : (i.factorial:aU)≠0:= by
  let e :=const.comp aR.embed
  let:CharP aU K1.p:=MK e.injective K1.p
  induction i with
  | zero=>simp
  | succ i ih =>
    have he : ((i+1 :ℕ) :aU)≠0:= by
      intro hz
      exact (GR hi) (Nat.le_of_dvd (Nat.succ_pos i)
        ((LQ aU K1.p (i+1)).mp hz))
    simpa only [Nat.factorial_succ,Du] using
      mul_ne_zero he (ih (Nat.lt_of_succ_lt hi))
end
end aA5
end
section
namespace Kd
noncomputable section
open aR dN vS Dr
open scoped BigOperators
def step {ι:Type} [oq ι] (i:ι) :ι→ℕ:=Av i 1
def aiD {ι σ:Type} [pL ι] [oq ι] (slot:σ→ι)
    (I:c9 (lJ σ aU)) :Prop :=
  ∀ f∈I,∀ a :ι→ℕ,t7 (step ∘ slot) a f∈I
def lO {ι σ:Type} [oq ι] (slot:σ→ι)
    (I:c9 (lJ σ aU)) (a :ι→ℕ) :ℚ :=
  (pz aU
    ((Ee aU (step ∘ slot) a).map
      (uh aU I).toLinearMap) :ℕ)
def uU {ι:Type} [oq ι] :List ι→((ι→ℕ)→ℚ)→(ι→ℕ)→ℚ
 | [],H=>H
 | i :: rest,H=> fun a=>uU rest H (a+step i) - uU rest H a
def zJ {σ:Type} (A:mD (σ →₀ ℕ)) :Set (σ →₀ ℕ) :=
 {e | ∀ b∈A,¬ b≤e}
def DL {ι σ:Type} [oq ι] (slot:σ→ι)
    (A:mD (σ →₀ ℕ)) (a :ι→ℕ) :ℚ :=
  ({e | e∈zJ A∧oK (step ∘ slot) e=a}.ncard:ℕ)
abbrev Kb {ι:Type} (fF:ι→cy) :=(i:ι)× capExponents (fF i)
def Fd {ι:Type} (fF:ι→cy) :Kb fF→ι:=Sigma.fst
def capMap {ι:Type} (fF:ι→cy) (J:c9 lz) :
    lJ (Kb fF) aU →ₐ[aU] lJ ι (lz ⧸ J) :=
  t5 fun v =>
    n5 (qz v.1 1)
     (lV J (n5 v.2.val 1))
def HW {ι:Type} (fF:ι→cy) (J:c9 lz) :
    c9 (lJ (Kb fF) aU) :=
  t9 (capMap fF J).toRingHom
def ku {ι:Type} [pL ι] (fF:ι→cy) (a :ι→ℕ) :Shape :=
 ⟨∑ i,a i*(fF i).b,∑ i,a i*(fF i).j,∑ i,a i*(fF i).t⟩
def Yz {ι:Type} [oq ι] (fF:ι→cy) (a :ι→ℕ) :
    Set (Fin 4 →₀ ℕ) :=
  {m | ∃ e :Kb fF →₀ ℕ,
    oK (step ∘ Fd fF) e=a ∧
    oK (fun v :Kb fF=>v.2.val) e=m}
def Sn (J:c9 lz) (A:Set (Fin 4 →₀ ℕ)) :ℕ :=
  pz aU
    ((qJ aU A).map (uh aU J).toLinearMap)
abbrev cut (J:c9 lz) (D:lz) :c9 GeoJets :=J ⊔ oY {D}
end
end Kd
end
section
namespace B8
noncomputable section
open Polynomial aR dN vS
open scoped BigOperators
theorem bZD:qx cylinder := by
 let retr :g9 →ₐ[aU] GeoJets :=
  MvPolynomial.killCompl (FV 4)
 have hr :retr.toRingHom.comp qK=Ob GeoJets :=
  ox AlgHom.toRingHom (MvPolynomial.killCompl_comp_rename (FV 4))
 intro P Q h
 have hh:=ox (Ideal.map retr.toRingHom) h
 simpa only [cylinder,Ideal.map_map,hr,Ideal.map_id] using hh
theorem bA1 :MH (⊥ : c9 g9) 5:= by
 unfold MH
 rw [(RingEquiv.quotientBot g9).ringKrullDim]
 change vZ (lJ (Fin 5) aU)≤_
 rw [Wl,LR,
  wR,Gn,xL,WithBot.coe_natCast]
theorem bJT {P:af 4} {p:cy} (hP:aO (qG P) p) :
   agB p 0 (qK (bC P)) := by
 apply (bms (a :=(p,0))).mpr
 intro m hm
 change m∈(zf uJ (bC P)).support at hm
 rw [MvPolynomial.support_rename_of_injective (FV 4)] at hm
 obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hm
 have haP:=Pk j8 P ha
 unfold Qj
 simp only [Finsupp.mapDomain_apply_of_injective (FV 4)]
 have hlast :pU 4∉v9 (uJ:Fin 4→Fin 5) := by
   rintro ⟨i,hi⟩
   exact VS i hi
 refine ⟨?_,?_,(R9 _ haP).trans hP.2.2,
   le_of_eq (Finsupp.mapDomain_of_notMem_range _ _ hlast)⟩
 · have hdegree :=F9 haP
   change a.degree≤P.totalDegree at hdegree
   rw [t4] at hdegree
   exact hdegree.trans hP.1
 · have hindex :a.sum (fun i n=>i.val*n)≤(qG P).j :=
     Mj (f := fun m=>m.sum (fun i n=>i.val*n)) haP
   rw [Hw _ _ (fun _=>Nat.mul_zero _)] at hindex
   exact hindex.trans hP.2.1
end
end B8
end
section
namespace B8
noncomputable section
open aR dN vS
open scoped BigOperators nonZeroDivisors
def c1 :Prop :=bTp
def c2 :Prop :=bQI
theorem aC0 {P:c9 g9} {D:g9} {d:ℕ}
  (hr :p6 (lV P D)) (h:MH P (d+1)) :
  MH (i9 P D) d:= by
 have hle :P≤ i9 P D:=Kz
 let π:=Ideal.Quotient.factor hle
 have hπ:π (lV P D)=0:= by
  rw [Ideal.Quotient.factor_mk,wA]
  exact (Cy :oY {D} ≤ i9 P D) (In (by simp))
 have hnd:lV P D∈(g9 ⧸ P)⁰ :=
  mem_nonZeroDivisors_iff_left.mpr fun a ha=>hr (ha.trans (vi _).symm)
 have hd:=ringKrullDim_succ_le_of_surjective π (Ideal.Quotient.factor_surjective hle) hnd hπ
 unfold MH at h ⊢
 apply ENat.WithBot.add_le_add_one_right_iff.mp
 exact hd.trans (by simpa only [zc,Dw ,WithBot.coe_add,WithBot.coe_one] using h)
theorem cKY (hcut:bTp) (hcycle :bQI) :
  aYC:= by
 intro B hB P I i hP hi hd D hD hprop ι S C w hinj hcomp
 let:=hP
 have hr :p6 (lV P D) :=
  SL (mt Ideal.Quotient.eq_zero_iff_mem.mp hprop)
 have hdle :MH P (I.card+1) :=le_of_eq hd
 exact (hcycle B hB (i9 P D) I (aC0 hr hdle) S C w hinj
  (fun a ha=>⟨(hcomp a ha).minimal,(hcomp a ha).length_le⟩)).trans
  (hcut B hB P I i hi hdle D hD hr)
private theorem A9 (L:ℕ) (p:cy) :bF (qP L p) := by
 let H :=4+(L - 5)*(p.j - 2)
 change H≤ max _ H∧3*min _ (H/3)≤H
 refine ⟨le_max_right _ _,?_⟩
 have h:=min_le_right (2+(L - 5)*p.t) (H/3)
 omega
end
end B8
end
section
namespace Kd
noncomputable section
open dN MvPolynomial
theorem aXV {ι σ:Type} [pL ι] [oq ι]
    (slot:σ→ι) (m:MonomialOrder σ) (I:c9 (lJ σ aU))
    (hI:aiD slot I) (a :ι→ℕ) :
    lO slot I a =
      ({e | e∈m.standardExponents I∧oK (step ∘ slot) e=a}.ncard:ℕ) := by
  classical
  let w:=step ∘ slot
  let E :Set (σ →₀ ℕ) := {e | e∈m.standardExponents I∧oK w e=a}
  let S:=qJ aU E
  let T:=Ee aU w a
  let mk :=(uh aU I).toLinearMap
  have hST:S≤T:= by
    intro f hf e he
    exact (hf (mem_support_iff.mpr he)).2
  let φ:S →ₗ[aU] T.map mk :=(mk.domRestrict S).codRestrict (T.map mk)
    (fun f=>Submodule.mem_map.mpr ⟨f,hST f.2,rfl⟩)
  have hinj:qx φ:= by
    intro f g hfg
    have heq :mk f=mk g:=ox C5 hfg
    apply vH
    exact m.eq_of_mem_standardSpace_of_sub_mem
      (fun e he=>(f.2 he).1) (fun e he=>(g.2 he).1) (Ideal.Quotient.eq.mp heq)
  have hsurj:sI φ:= by
    intro x
    obtain ⟨f,hf,heq⟩:=Submodule.mem_map.mp x.2
    obtain ⟨q,hq,hfq,_⟩:=m.exists_mem_standardSpace_sub_mem I f
    let q' := t7 w a q
    have hq' : q' ∈ S:= by
      intro e he
      have hc:=mem_support_iff.mp he
      change (t7 w a q).coeff e≠0 at hc
      rw [coeff_weightedHomogeneousComponent] at hc
      by_cases ha :oK w e=a
      · rw [z7 ha] at hc
        exact ⟨hq (mem_support_iff.mpr hc),ha⟩
      · simp [ha] at hc
    have hproj:t7 w a f=f :=
      IsWeightedHomogeneous.weightedHomogeneousComponent_same hf
    have hsub:f - q' ∈ I:= by
      have h:=hI (f - q) hfq a
      change t7 w a (f - q)∈I at h
      rw [yJ,hproj] at h
      exact h
    exact ⟨⟨q',hq'⟩,vH ((Ideal.Quotient.eq.mpr hsub).symm.trans heq)⟩
  have heq :=(LinearEquiv.ofBijective φ ⟨hinj,hsurj⟩).finrank_eq
  change ((pz aU (T.map mk) :ℕ) :ℚ)=(E.ncard:ℕ)
  rw [← heq,LO (C9 aU E),zi]
end
end Kd
end
section
namespace aKq
noncomputable section
open aR MvPolynomial
open scoped Polynomial
abbrev Dual (A:Type*) [vw A] :=TrivSqZeroExt A A
def dMP {A:Type*} [vw A] (e :ao[X] →+* A) :ao[X] →+* Dual A where
  toFun c:=(e c,e (pC c))
  map_zero' := by apply FQ <;> simp
  map_one' := by apply FQ <;> simp
  map_add' c d:= by
    apply FQ
    · change e (c+d)=e c+e d
      exact pQ _ _ _
    · change e (pC (c+d)) =
        e (pC c)+e (pC d)
      simp only [pQ]
  map_mul' c d:= by
    apply FQ
    · change e (c*d)=e c*e d
      exact nX _ _ _
    · change e (pC (c*d)) =
        e c*e (pC d)+e (pC c)*e d
      rw [Polynomial.derivative_mul,pQ,nX ,nX ,FU]
def aMY {n:ℕ} (P:af n) :af n :=
 ∑ m∈P.support,n5 m (pC (P.coeff m))
@[simp] private theorem cF9 {n:ℕ} (P:af n) (m:Fin n →₀ ℕ) :
    (aMY P).coeff m=pC (P.coeff m) := by
  classical
  rw [aMY,coeff_sum]
  simp only [G4 ,Vl]
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.mp hm,qm]
private theorem dMI {n:ℕ} (c:ao[X]) :
  aMY (C c:af n)=C (pC c) := by
 classical
 ext m
 rw [cF9]
 by_cases hm:0=m <;> simp [coeff_C,hm]
private theorem dMJ {n:ℕ} (P Q:af n) :
  aMY (P+Q)=aMY P+aMY Q:= by
 ext m
 simp
private theorem dMK {n:ℕ} (P:af n) (j:Fin n) :
  aMY (P*lI j)=aMY P*lI j:= by
 classical
 ext m
 rw [cF9,coeff_mul_X',coeff_mul_X']
 split_ifs <;> simp
theorem cLd {n:ℕ} {A:Type*} [vw A]
    (e :af n →+* A) (j:af n →+* Dual A)
    (hfst : ∀ P,(j P).fst=e P)
    (hC : ∀ c,(j (C c)).snd=e (C (pC c))) (P:af n) :
    (j P).snd=e (aMY P) + ∑ i,(j (lI i)).snd*e (qU i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [hC,dMI]
  | add P Q hP hQ =>
    simp only [pQ,TrivSqZeroExt.snd_add,dMJ,hP,hQ,
      wY ,sH]
    ring
  | mul_X P l ih =>
    rw [nX]
    change (j P).fst*(j (lI l)).snd+(j P).snd*(j (lI l)).fst= _
    rw [hfst,hfst,ih,dMK,nX]
    simp only [pderiv_mul,pQ,nX ,wY ,sH]
    have left: (∑ i,(j (lI i)).snd*(e (qU i P)*e (lI l))) =
        (∑ i,(j (lI i)).snd*e (qU i P))*e (lI l) := by
      simp only [Finset.sum_mul,v8]
    have right: (∑ i,(j (lI i)).snd*(e P*e (qU i (lI l)))) =
        (j (lI l)).snd*e P:= by
      simp [pderiv_X,Kv,mul_ite]
    rw [left,right]
    ring
end
end aKq
end
section
namespace Kd
noncomputable section
open aR dN vS Dr Filter
def c1 :Prop :=
  ∀ {ι σ:Type} [pL ι] [oq ι] [vk σ]
    (slot:σ→ι) (A B:mD (σ →₀ ℕ)),zJ B⊆zJ A →
    let H := fun a=>DL slot A a - DL slot B a
    (∃ P:lJ ι ℚ,∀ᶠ a in pG,oy (fun i=>(a i:ℚ)) P=H a) ∧
    ∀ used :List ι,∀ᶠ a in pG,0≤uU used H a
def c2 :Prop :=
  ∀ {ι:Type} [pL ι] [oq ι] (fF:ι→cy),
    (∀ i,ChamberBox (fF i)) → ∀ a :ι→ℕ,
      Yz fF a=capExponents (ku fF a)
def c3:Prop :=
  ∀ {ι:Type} [pL ι] [oq ι] (fF:ι→cy) (J:c9 lz),
    aiD (Fd fF) (HW fF J) ∧ ∀ a :ι→ℕ,
      lO (Fd fF) (HW fF J) a=(Sn J (Yz fF a) :ℚ)
def c4 :Prop :=
  ∀ (J:c9 lz) (p:cy) (n:ℕ),
    p7
      (J.comap (nI aU (capExponents p)).toRingHom) n =
    Sn J (Yz (fun _:Unit=>p) (fun _=>n))
def c5:Prop :=
  ∀ {ι:Type} [pL ι] [oq ι] (fF:ι→cy) (J:c9 lz)
    (base :ι) (used :List ι),
    (∀ i,ChamberBox (fF i))→base∉used→used.Nodup→dimension J≤used.length →
    (∀ q:cy ,ChamberBox q → ∀ n,
      p7
        (J.comap (nI aU (capExponents q)).toRingHom) n =
      Sn J (capExponents (q.scale n))) →
    let H := fun a=>(Sn J (capExponents (ku fF a)) :ℚ)
    ∀ P:lJ ι ℚ,(∀ᶠ a in pG,oy (fun i=>(a i:ℚ)) P=H a) →
      ∀ᶠ a in pG,
        uU used H a=BE (capCoeff J used.length) (used.map fF) (fF base)
def c6:Prop :=
  ∀ {ι:Type} [pL ι] [oq ι] (fF:ι→cy) (i:ι)
    (J:c9 lz) (D:lz),
    VE (fF i) D→ p6 (lV J D) →
    let slot:=Fd fF
    let I:=HW fF J
    let I₁:=HW fF (cut J D)
    let I₂:=HW fF (cut J (D^2))
    aiD slot I→aiD slot I₂ →
    ∃ B C:c9 (lJ (Kb fF) aU),
      aiD slot B∧aiD slot C∧B≤I₂∧C≤I₁ ∧
      (∀ a :ι→ℕ,lO slot B (a+step i)+lO slot I a=lO slot I (a+step i)) ∧
      ∀ a :ι→ℕ,lO slot C (a+step i)+lO slot I₁ a=lO slot I₂ (a+step i)
private lemma boW {ι:Type} [oq ι] (used :List ι)
   (H G: (ι→ℕ)→ℚ) (a :ι→ℕ) :
   uU used (fun b=>H b-G b) a=uU used H a - uU used G a := by
 induction used generalizing a with
 | nil=>rfl
 | cons i rest ih=>simp only [uU,ih]; ring
private lemma boV {ι:Type} [oq ι] (used :List ι)
   (H : (ι→ℕ)→ℚ) (a v :ι→ℕ) :
   uU used (fun b=>H (b+v)) a=uU used H (a+v) := by
 induction used generalizing a with
 | nil=>rfl
 | cons i rest ih=>simp only [uU,ih,add_right_comm a (step i) v]
private lemma auS {ι:Type} {Q: (ι→ℕ)→Prop} (v :ι→ℕ)
  (h : ∀ᶠ a in pG,Q a) : ∀ᶠ a in pG,Q (a+v) := by
 obtain ⟨u,hu⟩:=eventually_atTop.mp h
 exact eventually_atTop.mpr ⟨u,fun a ha=>hu (a+v) (ha.trans (le_add_of_nonneg_right zero_le))⟩
private lemma wD {ι:Type} [oq ι] (used :List ι) (v :ι→ℕ)
  (B C G H : (ι→ℕ)→ℚ) (heq : ∀ a,B (a+v)+H a=G (a+v))
  (hpos : ∀ᶠ a in pG,0≤uU used (fun b=>B b - C b) a) :
  ∀ᶠ a in pG,uU used C (a+v)≤uU used G (a+v) - uU used H a := by
 have hid : (fun a=>B (a+v))=fun a=>G (a+v) - H a := by
  funext a
  linarith [heq a]
 filter_upwards [auS v hpos] with a ha
 rw [boW] at ha
 rw [← boV used B,hid,boW,boV] at ha
 linarith
private lemma b5z {ι σ:Type} [pL ι] [oq ι] (slot:σ→ι) :
  aiD slot (⊤ : c9 (lJ σ aU)) := by
 intro f hf a
 exact Submodule.mem_top
private lemma b5Z {ι σ:Type} [oq ι] (slot:σ→ι) (a :ι→ℕ) :
  lO slot (⊤ : c9 (lJ σ aU)) a=0:= by
 have :Subsingleton (lJ σ aU ⧸ (⊤ : c9 (lJ σ aU))) :=
  (Ideal.Quotient.subsingleton_iff).2 rfl
 simp [lO,Module.finrank_eq_zero_of_subsingleton]
private theorem a4H (h1 :c1)
  {ι σ:Type} [pL ι] [oq ι] [vk σ]
  (slot:σ→ι) (I K:c9 (lJ σ aU))
  (hI:aiD slot I) (hK:aiD slot K) (hle :I≤K) :
  let H := fun a=>lO slot I a-lO slot K a
  (∃ P:lJ ι ℚ,∀ᶠ a in pG,oy (fun i=>(a i:ℚ)) P=H a) ∧
  ∀ used :List ι,∀ᶠ a in pG,0≤uU used H a := by
 classical
 let _:=Fintype.ofFinite σ
 let _:LinearOrder σ:=LinearOrder.lift' _ (Fintype.equivFin σ).injective
 have :WellFoundedGT σ:=Finite.to_wellFoundedGT
 let m:MonomialOrder σ:=MonomialOrder.degLex
 obtain ⟨A,hA⟩:=m.exists_finset_standardExponents_iff I
 obtain ⟨B,hB⟩:=m.exists_finset_standardExponents_iff K
 have hAB:zJ B⊆zJ A:= by
  intro e he
  exact (hA e).mp (fun f hf=>(hB e).mpr he f (hle hf))
 have eqI:lO slot I=DL slot A:= by
  funext a
  rw [aXV slot m I hI a]
  simp only [DL,hA,zJ,G1]
 have eqK:lO slot K=DL slot B:= by
  funext a
  rw [aXV slot m K hK a]
  simp only [DL,hB,zJ,G1]
 rw [eqI,eqK]
 exact h1 slot A B hAB
private theorem c7s (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5)
   {ι:Type} [pL ι] [oq ι] (fF:ι→cy) (J:c9 lz)
   (base :ι) (used :List ι) (hsh : ∀ i,ChamberBox (fF i))
   (hb:base∉used) (hn:used.Nodup) (hd:dimension J≤used.length) :
   ∀ᶠ a in pG,uU used (lO (Fd fF) (HW fF J)) a =
     BE (capCoeff J used.length) (used.map fF) (fF base) := by
 let slot:=Fd fF
 let I:=HW fF J
 have hI:=(h3 fF J).1
 have hall:=(a4H h1 slot I ⊤ hI (b5z slot) le_top).1
 rw [show (fun a=>lO slot I a-lO slot ⊤ a)=lO slot I by
   funext a; simp [b5Z]] at hall
 obtain ⟨P,hP⟩:=hall
 have hrank :lO slot I=fun a=>(Sn J (capExponents (ku fF a)) :ℚ) := by
   funext a
   rw [(h3 fF J).2 a,h2 fF hsh a]
 rw [hrank] at hP ⊢
 refine h5 fF J base used hsh hb hn hd (fun q hq n => ?_) P hP
 rw [h4,h2 (fun _:Unit=>q) (fun _=>hq)]
 simp [ku,t3]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :
    Dr.c2 := by
  classical
  intro J p boxes hp hboxes hdim D hD hreg
  let ι:=Option (Option (Fin boxes.length))
  let base :ι:=none
  let i:ι:=some none
  let emb:Fin boxes.length→ι:= fun k=>some (some k)
  let rest:=(List.finRange boxes.length).map emb
  let fF:ι→cy
    | none=>⟨3, 3,1⟩
    | some none=>p
    | some (some k)=>boxes.get k
  have hsh (k :ι) :ChamberBox (fF k) := by
    cases k with
    | none =>
      change ChamberBox ⟨3, 3,1⟩
      exact ⟨by decide,by decide,by decide⟩
    | some k=>cases k with
      | none=>exact hp
      | some k=>exact hboxes _ (List.get_mem _ _)
  have hbase :base∉rest:= by simp [base,rest,emb]
  have hi:i∉rest:= by
    intro h
    obtain ⟨k,_,hk⟩:=List.mem_map.mp h
    change (some (some k) :Option (Option (Fin boxes.length)))=some none at hk
    have hinner : (some k :Option (Fin boxes.length))=none :=Np hk
    cases hinner
  have hn:rest.Nodup:=(List.nodup_finRange _).map
    (fun _ _ h=>Np (Np h))
  have hbase' : base∉i :: rest:= by simp [base,i,rest,emb]
  have hn' : (i :: rest).Nodup:=List.nodup_cons.mpr ⟨hi,hn⟩
  have hmap :rest.map fF=boxes := by
    simp [rest,List.map_map,Function.comp_def,emb,fF]
  have hlen:rest.length=boxes.length:= by simp [rest]
  let slot:=Fd fF
  let I:=HW fF J
  let I₁:=HW fF (cut J D)
  let I₂:=HW fF (cut J (D^2))
  have hgraded₂:=(h3 fF (cut J (D^2))).1
  obtain ⟨B,C,hB,hC,hBI,hCI,heqB,heqC⟩:=h6 fF i J D hD hreg (h3 fF J).1 hgraded₂
  have hposB:=(a4H h1 slot B I₂ hB hgraded₂ hBI).2 rest
  have hposC:=(a4H h1 slot C I₁ hC (h3 fF (cut J D)).1 hCI).2 rest
  have hspendB:=wD rest (step i) (lO slot B) (lO slot I₂) (lO slot I)
    (lO slot I) heqB hposB
  have hspendC:=wD rest (step i) (lO slot C) (lO slot I₁) (lO slot I₂)
    (lO slot I₁) heqC hposC
  have hd₁:dimension (cut J D)≤ rest.length:= by
    have hdrop:dimension (cut J D)≤dimension J - 1 :=aCR hreg
    omega
  have hd₀:dimension J≤(i :: rest).length:= by simpa [hlen] using hdim
  have hr₀:=c7s h1 h2 h3 h4 h5 fF J base (i :: rest) hsh hbase' hn' hd₀
  have hr₁:=c7s h1 h2 h3 h4 h5 fF (cut J D) base rest hsh hbase hn hd₁
  have hfinal : ∀ᶠ _a in (pG:Filter (ι→ℕ)),
      2*BE (capCoeff (cut J D) boxes.length) boxes ⟨3, 3,1⟩ ≤
        BE (capCoeff J (p :: boxes).length) (p :: boxes) ⟨3, 3,1⟩:= by
    filter_upwards [hspendB,hspendC,hr₀,hr₁,auS (step i) hr₁] with a hb hc h₀ h₁ h₁'
    rw [List.map_cons,hmap,HZ,hlen] at h₀
    rw [hlen,hmap] at h₁ h₁'
    change uU rest (lO slot I) (a+step i) - uU rest (lO slot I) a =
      BE (capCoeff J (boxes.length+1)) (p :: boxes) ⟨3, 3,1⟩ at h₀
    change uU rest (lO slot I₁) a =
      BE (capCoeff (cut J D) boxes.length) boxes ⟨3, 3,1⟩ at h₁
    change uU rest (lO slot I₁) (a+step i) =
      BE (capCoeff (cut J D) boxes.length) boxes ⟨3, 3,1⟩ at h₁'
    simp only [HZ]
    linarith [hb,hc,h₀,h₁,h₁']
  obtain ⟨_,hfinal⟩:=hfinal.exists
  unfold tW
  rw [HZ,pow_succ,u5 ((2 :ℚ)^boxes.length) 2,← div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (le_div_iff₀ (by norm_num : (0:ℚ)<2)).2 (by simpa [u5] using hfinal)
end
end Kd
end
section
namespace aKq
noncomputable section
open aR dN aA5 MvPolynomial
open scoped Polynomial
abbrev Chart (g:af 4) :=SD (oj g)
abbrev incl (g:af 4) :af 4 →+* Chart g:=nq _ _
abbrev S (g:af 4) :Chart g:=incl g (oj g)
abbrev aIf (g:af 4) :Chart g:=Up (oj g)
theorem bbo (g:af 4) :S g*aIf g=1 :=
 IsLocalization.Away.mul_invSelf _
abbrev constants (g:af 4) :ao[X] →+* Chart g:=(incl g).comp C
abbrev azH :ao := -(4 :ao)⁻¹
theorem eEB:azH*(4 :ao) = -1 := by
 let _:CharP ao K1.p:=MK embed.injective K1.p
 have h: (4 :ao)≠0:= by
  intro hz
  have hd:=(LQ ao K1.p 4).mp hz
  exact (by decide : ¬ 4 % K1.p=0) (Nat.dvd_iff_mod_eq_zero.mp hd)
 rw [azH,neg_mul,inv_mul_cancel₀ h]
abbrev q (g:af 4) :Chart g:=constants g (oZ azH)
private theorem c5U (g:af 4) :q g*4 = -1 := by
 let e :=(constants g).comp oZ
 change e azH*4 = -1
 calc
  _=e azH*e 4 := by rw [map_ofNat]
  _=e (azH*4) :=(nX _ _ _).symm
  _ = _:= by rw [eEB,map_neg,zS]
def W (g:af 4) :Chart g:=q g*incl g (pK g)*aIf g
private theorem cSX (g:af 4) :4*W g = -(incl g (pK g)*aIf g) := by
 unfold W
 calc
  _=(q g*4)*(incl g (pK g)*aIf g) := by ring
  _ = _:= by rw [c5U,neg_one_mul]
def zp (g:af 4) :af 5 →+* Chart g :=
 zh (constants g) (yU (W g) (fun i=>incl g (lI i)))
@[simp] theorem bel (g:af 4) (a :ao[X]) :
   zp g (C a)=constants g a :=eval₂Hom_C _ _ _
@[simp] theorem aVb (g:af 4) :
    zp g (lI (pU 4))=W g :=
  (eval₂Hom_X' _ _ _).trans Lf
@[simp] theorem b5B (g:af 4) (i:Fin 4) :
   zp g (lI i.castSucc)=incl g (lI i) := by simp [zp]
@[simp] theorem aN3 (g P:af 4) :zp g (T9 P)=incl g P:= by
  have h: (zp g).comp T9.toRingHom=incl g:= by
    apply xm
    · intro c
      simp
    · intro i
      simp
  exact Au h P
private def aO4 (g:af 4) :af 4 →+* Dual (Chart g) :=
  zh (dMP (constants g))
    (fun i=>(incl g (lI i),
      yU (4*W g)
        (fun j:Fin 3=>(j.val+1 :ℕ)*incl g (lI j.succ)) i))
private theorem b97 (g:af 4) (a :ao[X]) :
  aO4 g (C a)=(constants g a,constants g (pC a)) :=
 eval₂Hom_C _ _ _
private theorem bJQ (g:af 4) (i:Fin 4) :
    aO4 g (lI i)=(incl g (lI i),
      yU (4*W g)
        (fun j:Fin 3=>(j.val+1 :ℕ)*incl g (lI j.succ)) i) :=
  eval₂Hom_X' _ _ _
private theorem b98 (g P:af 4) : (aO4 g P).fst=incl g P:= by
 have h: (Yc (Chart g) (Chart g) (Chart g)).toRingHom.comp
    (aO4 g)=incl g:= by
  apply xm
  · intro a
    change (aO4 g (C a)).fst=incl g (C a)
    rw [b97,SW]
    rfl
  · intro i
    change (aO4 g (lI i)).fst=incl g (lI i)
    rw [bJQ,SW]
 exact Au h P
private def Ub (g:af 4) :Chart g →+* Dual (Chart g) :=
 IsLocalization.Away.lift (oj g) (g:=aO4 g)
  (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by
    rw [b98]
    exact IsLocalization.Away.algebraMap_isUnit _))
@[simp] private theorem br9 (g P:af 4) :
   Ub g (incl g P)=aO4 g P:=IsLocalization.Away.lift_eq _ _ _
private theorem b73 (g:af 4) (a :Chart g) : (Ub g a).fst=a := by
 have h: (Yc (Chart g) (Chart g) (Chart g)).toRingHom.comp
   (Ub g)=Ob _:= by
  apply IsLocalization.ringHom_ext (Submonoid.powers (oj g))
  apply RingHom.ext
  intro P
  change (Ub g (incl g P)).fst=incl g P
  rw [br9,b98]
 exact Au h a
def D (g:af 4) :Chart g →+ Chart g :=
  (TrivSqZeroExt.sndHom (R:=Chart g) (M:=Chart g)).toAddMonoidHom.comp
    (Ub g).toAddMonoidHom
theorem bQM (g:af 4) (a b:Chart g) :D g (a*b)=a*D g b+D g a*b:= by
 change (Ub g (a*b)).snd= _
 rw [nX]
 change (Ub g a).fst*D g b+D g a*(Ub g b).fst= _
 rw [b73,b73]
@[simp] theorem cxr (g:af 4) (n:ℕ) :D g (n:Chart g)=0:= by
  have h:D g 1=0:= by
    change (Ub g 1).snd=0
    rw [zS]
    rfl
  induction n with
  | zero=>simp
  | succ n ih=>rw [Nat.cast_succ,map_add,ih,h,add_zero]
@[simp] theorem bja (g:af 4) (i:Fin 3) :
   D g (incl g (lI i.castSucc))=(i.val+1 :ℕ)*incl g (lI i.succ) := by
  change (Ub g (incl g (lI i.castSucc))).snd= _
  rw [br9,bJQ,zd ,X8]
@[simp] theorem cxq (g:af 4) :
   D g (incl g (lI (pU 3)))=4*W g:= by
  change (Ub g (incl g (lI (pU 3)))).snd= _
  rw [br9,bJQ,zd ,Lf]
theorem bQL (g:af 4) (c:ao[X]) :
  D g (constants g c)=constants g (pC c) := by
 change (Ub g (incl g (C c))).snd= _
 rw [br9,b97,zd]
theorem bQK (g P:af 4) :S g*D g (incl g P)=incl g (u6 g P) := by
 have h:=cLd (incl g) (aO4 g) (b98 g) (by
   intro c
   rw [b97,zd]
   rfl) P
 have hs :D g (incl g P) =
     incl g (pK P)+4*W g*incl g (oj P) := by
   change (Ub g (incl g P)).snd= _
   rw [br9,h,FK]
   simp only [bJQ,zd ,X8 ,Lf ,
     pK,oj,pQ,t8 ,nX ,JM,← add_assoc]
   rfl
 rw [hs,cSX,u6,yJ,nX ,nX ,wY]
 have hm:S g*(incl g (pK g)*aIf g)=incl g (pK g) := by
   rw [← mul_left_comm,bbo,sS]
 linear_combination -incl g (oj P)*hm
private theorem dmP (g:af 4) (i:Fin 4) :
   D g (zp g (lI i.castSucc))=(i.val+1 :ℕ)*zp g (lI i.succ) := by
 refine yU ?_ (fun j => ?_) i
 · change D g (zp g (lI (pU 3).castSucc)) =
     4*zp g (lI (pU 4))
   rw [b5B,aVb,cxq]
 · rw [b5B,Fin.succ_castSucc,b5B,bja]
   rfl
theorem bQJ (g:af 4) (P:af 5) :
   D g (zp g P)=zp g (ay1 P) +
     D g (W g)*zp g (qU (pU 4) P) := by
 have h:=cLd (zp g) ((Ub g).comp (zp g))
   (fun p=>b73 g (zp g p)) (by
     intro c
     change D g (zp g (C c))=zp g (C (pC c))
     rw [bel,bel,bQL]) P
 change D g (zp g P)=zp g (cGs P) +
   ∑ i,D g (zp g (lI i))*zp g (qU i P) at h
 rw [h,FK,aVb,← add_assoc]
 simp only [dmP,ay1,pQ,t8 ,nX ,JM]
private theorem graph_zero (g:af 4) :zp g (ao6 g)=0:= by
 rw [ao6,pQ,nX ,nX ,aN3,aN3,aVb,
  bel,map_ofNat]
 change incl g (pK g)+4*S g*W g=0
 have hm:S g*(incl g (pK g)*aIf g)=incl g (pK g) := by
  rw [← mul_left_comm,bbo,sS]
 rw [u5 (4 :Chart g) (S g),v8 ,cSX,mul_neg,hm,add_neg_cancel]
@[simp] private theorem aWm (P:af 4) :
   qU (pU 4) (T9 P)=0:= by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨i,_,hi⟩:=mem_vars_rename uJ P hv
  exact VS i hi
private theorem eKS (g:af 4) :
  qU (pU 4) (ao6 g)=C (4 :ao[X])*T9 (oj g) := by
 rw [ao6,pQ,aWm,wR,pderiv_mul,pderiv_C_mul,
  aWm,vi ,zero_mul,pderiv_X_self,sS ,wR]
private theorem D_W (g:af 4) :S g*D g (W g)=zp g (bp7 g) := by
 have h:=ox (D g) (graph_zero g)
 rw [qm,bQJ,eKS,nX ,bel,map_ofNat,aN3] at h
 change zp g (ay1 (ao6 g))+D g (W g)*(4*S g)=0 at h
 rw [bp7,nX ,bel]
 change S g*D g (W g)=q g*zp g (ay1 (ao6 g))
 linear_combination -q g*h+S g*D g (W g)*c5U g
theorem dmQ (g:af 4) :
  D g (S g)=zp g (ay1 (T9 (oj g))) := by
 simpa only [aN3,aWm,qm,vi ,y5] using
  bQJ g (T9 (oj g))
theorem ewv (g:af 4) (T:af 5) (n:ℕ) :
  zp g (T9 (oj g)*ay1 T+bp7 g*qU (pU 4) T -
    (n:af 5)*ay1 (T9 (oj g))*T) =
    S g*D g (zp g T)-(n:Chart g)*D g (S g)*zp g T:= by
 simp only [yJ,pQ,nX ,JM,aN3,
  ← dmQ,← D_W,bQJ]
 ring
end
end aKq
end
section
namespace agM
open aR dN vS B8
open scoped BigOperators
def Vw (B:lS) (t:Fin 5→ℕ) :cy×ℕ :=
  (⟨∑ i,t i*(B i).1.b,∑ i,t i*(B i).1.j,∑ i,t i*(B i).1.t⟩,
    ∑ i,t i*(B i).2)
def agj (a :cy×ℕ) (n:ℕ) :cy×ℕ :=
 (a.1.scale n,n*a.2)
theorem bOu (B:lS) (hB : ∀ i,bF (B i).1) (t:Fin 5→ℕ) :
   bF (Vw B t).1 := by
 unfold bF Vw
 dsimp only
 constructor
 · exact t6 (fun i _=>oz _ (hB i).1)
 · rw [uz]
   exact t6 (fun i _=> by
    simpa only [xu] using oz (t i) (hB i).2)
end agM
end
section
namespace axg
noncomputable section
open aR dN vS B8 MvPolynomial
open scoped BigOperators
private theorem dW6 {R S:Type*} [vw R] [vw S]
  (f :R →+* S) (hf :f.IsIntegral) (hinj:qx f) :
  vZ R≤ vZ S:= by
 let:Algebra R S:=f.toAlgebra
 have :Algebra.IsIntegral R S:=⟨hf⟩
 unfold vZ Order.krullDim
 refine iSup_le fun chain => ?_
 obtain ⟨q,hq⟩:=hf.comap_surjective hinj chain.head
 have :q.asIdeal.LiesOver chain.head.asIdeal:=⟨ox PrimeSpectrum.asIdeal hq.symm⟩
 obtain ⟨dR,hlen,_,_⟩:=Ideal.exists_ltSeries_of_hasGoingUp chain q.asIdeal
 exact le_iSup_of_le dR (by rw [hlen])
theorem beu {σ:Type*} [vk σ] {P:c9 (lJ σ aU)} {d:ℕ}
   (hd:vZ (lJ σ aU ⧸ P)≤((d:ℕ∞) :WithBot ℕ∞)) :
   (oD P).natDegree≤d:= by
 by_cases hP:P = ⊤
 · simp [hP,affineHilbertPolynomial_top]
 have :=Ideal.Quotient.nontrivial_iff.mpr hP
 obtain ⟨s,g,hinj,hfin⟩:=exists_finite_inj_algHom_of_fg aU (lJ σ aU ⧸ P)
 rw [natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfin hinj,Nat.card_fin]
 have hdim:=(dW6 g.toRingHom hfin.to_isIntegral hinj).trans hd
 simpa [Wl,LR] using hdim
private theorem dmp (a :cy×ℕ) : (0:Exponent)∈Nl a := by
 change Qj (a.1.scale 2,2*a.2) 0
 simp [Qj]
theorem bEd {B:lS} (hB:Admissible B) {t:Fin 5→ℕ}
    (ht : ∀ i,0<t i) :sI (nI aU (H7 B t)) := by
  classical
  apply x7
  intro v
  obtain ⟨i,hi⟩:=hB.2 v
  let j₀:Fin (t i) :=⟨0,ht i⟩
  let u (k :Fin 5) (j:Fin (t k)) :Exponent :=
    if h:k=i then if h ▸ j=j₀ then qz v 1 else 0 else 0
  refine ⟨u,?_,?_⟩
  · intro k j
    by_cases hk :k=i
    · subst k
      by_cases hj:j=j₀
      · simpa [u,hj] using hi
      · simpa [u,hj] using dmp (B i)
    · simpa [u,hk] using dmp (B k)
  · rw [Vq i]
    · rw [Vq j₀]
      · simp [u]
      · intro j _ hj
        simp [u,hj]
      · simp
    · intro k _ hk
      simp [u,hk]
    · simp
theorem aNi {B:lS} (hB:Admissible B) {P:c9 g9} {d:ℕ}
  (hP:MH P d) {t:Fin 5→ℕ} (ht : ∀ i,0<t i) :
  (oD (P.comap (nI aU (H7 B t)))).natDegree≤d:= by
 let f :=nI aU (H7 B t)
 let g:=(lV P).comp f.toRingHom
 have hg:sI g :=
  Ideal.Quotient.mk_surjective.comp (bEd hB ht)
 have hker :t9 g=P.comap f := by
  ext x
  change lV P (f x)=0↔f x∈P
  exact wA
 apply beu
 rw [← hker,(g.quotientKerEquivOfSurjective hg).ringKrullDim]
 exact hP
end
end axg
end
section
namespace bzB
noncomputable section
open aR dN Dr
open scoped BigOperators
def c1 :Prop :=
  ∀ (J:c9 lz) (d:ℕ),dimension J≤d →
    ∀ p:cy ,ChamberBox p →
      capCoeff J d p =
        ∑ P∈J.minimalPrimesFinset,(AN J P:ℚ)*capCoeff P d p
def c2 :Prop :=
  ∀ (P:c9 lz) (boxes :List cy),P.IsPrime →
    (∀ q∈boxes,ChamberBox q)→dimension P=boxes.length→2≤boxes.length →
      0≤tW P boxes
private abbrev xo:Shape :=⟨3, 3,1⟩
private lemma ax7:ChamberBox xo:=⟨by decide,by decide,by decide⟩
private lemma Nc {p q:cy} (hp:ChamberBox p) (hq:ChamberBox q) :
  ChamberBox (p.plus q) := by
 obtain ⟨hp₁,hp₂,hp₃⟩:=hp
 obtain ⟨hq₁,hq₂,hq₃⟩:=hq
 refine ⟨Eg hp₁ hq₁,?_,Nat.add_pos_left hp₃ _⟩
 change 3*(p.t+q.t)≤p.j+q.j
 omega
private lemma aWr {H G:cy→ℚ} (h : ∀ p,ChamberBox p→H p=G p)
   {boxes :List cy} (hboxes : ∀ q∈boxes,ChamberBox q) {p:cy}
   (hp:ChamberBox p) :BE H boxes p=BE G boxes p:= by
 induction boxes generalizing p with
 | nil=>exact h p hp
 | cons q boxes ih =>
   have hq:=hboxes q Ts
   have hr := fun r hr=>hboxes r (List.mem_cons_of_mem _ hr)
   simp only [BE,ih hr (Nc hp hq),ih hr hp]
private lemma eME {ι:Type*} (S:mD ι) (w:ι→ℚ) (H :ι→cy→ℚ)
   (boxes :List cy) (p:cy) :
   BE (fun x => ∑ i∈S,w i*H i x) boxes p =
     ∑ i∈S,w i*BE (H i) boxes p:= by
 induction boxes generalizing p with
 | nil=>rfl
 | cons q boxes ih =>
   simp only [BE,ih,← Sd ,mul_sub]
private lemma bKA (boxes :List cy) (p:cy) :
   BE (fun _=>0) boxes p=0:= by
 induction boxes generalizing p with
 | nil=>rfl
 | cons q boxes ih=>simp only [BE,ih,sub_self]
private abbrev capMap (p:cy) :=nI aU (capExponents p)
private lemma aye {p:cy} (hp:ChamberBox p) :
  sI (capMap p) := by
 obtain ⟨hb,hj,ht⟩:=hp
 apply x7
 intro i
 fin_cases i <;> simp [capExponents,yo] <;> omega
private lemma cap_dimension (J:c9 lz) {p:cy} (hp:ChamberBox p) :
  (oD (J.comap (capMap p).toRingHom)).natDegree =
    dimension J :=
 G5
  (capMap p) (aye hp) J
private lemma eA2 {J:c9 lz} {boxes :List cy}
  (hboxes : ∀ p∈boxes,ChamberBox p) (hd:dimension J<boxes.length) :
  tW J boxes=0:= by
 have hz (p:cy) (hp:ChamberBox p) :capCoeff J boxes.length p=0 :=
  zk ((cap_dimension J hp).trans_lt hd)
 unfold tW
 rw [aWr hz hboxes ax7,bKA,zero_div]
private lemma capCoeff_le_of_subset (J:c9 lz) {p q:cy}
    (hp:ChamberBox p) (hq:ChamberBox q) (hsub:capExponents p⊆capExponents q)
    {d:ℕ} (hd:dimension J≤d) :
    capCoeff J d p≤ capCoeff J d q:= by
  let incl (i:capExponents p) :capExponents q:=⟨i.val,hsub i.property⟩
  let f :=zf (R:=aU) incl
  have hf : (capMap q).comp f=capMap p:= by
    ext i
    simp [f,incl,Dv]
  let I:=J.comap (capMap p).toRingHom
  let K:=J.comap (capMap q).toRingHom
  have heq :K.comap f.toRingHom=I:= by
    change (J.comap (capMap q).toRingHom).comap f.toRingHom= _
    rw [Ideal.comap_comap]
    change J.comap ((capMap q).comp f).toRingHom=I
    rw [hf]
  let g:=G3 K f heq.ge
  have hg:qx g:=Ideal.quotientMap_injective' (H :=heq.ge) heq.le
  have hgen (i:capExponents p) :
      g (lV I (lI i))∈uW K 1 := by
    rw [show g (lV I (lI i)) =
        lV K (lI (incl i)) by
          change Ideal.quotientMap K f.toRingHom heq.ge
            (lV I (lI i))= _
          rw [Ideal.quotientMap_mk]
          change lV K (zf incl (lI i))= _
          rw [MvPolynomial.rename_X]]
    exact MvPolynomial.mk_X_mem_quotientDegreeLE K _
  change (oD I).coeff d ≤
    (oD K).coeff d
  refine JW
    ((cap_dimension J hp).trans_le hd) ((cap_dimension J hq).trans_le hd) ?_
  filter_upwards [z8 I,
    z8 K] with n hI hK
  rw [hI,hK]
  exact_mod_cast (by simpa only [one_mul] using
    MvPolynomial.affineHilbertFunction_le_of_injective g hg hgen n :
      MvPolynomial.affineHilbertFunction I n≤MvPolynomial.affineHilbertFunction K n)
private lemma b9i (h2 :c2) {P:c9 lz} (hP:P.IsPrime)
    {boxes :List cy} (hboxes : ∀ q∈boxes,ChamberBox q)
    (hd:dimension P≤boxes.length) :
    0≤tW P boxes := by
  rcases hd.lt_or_eq with hlt | heq
  · rw [eA2 hboxes hlt]
  · cases boxes with
    | nil =>
      change 0≤ capCoeff P 0 xo/(2 :ℚ)^0
      apply Mk _ (by norm_num)
      exact RJ
        ((cap_dimension P ax7).trans_le heq.le)
        (MvPolynomial.eventually_eval_affineHilbertPolynomial_nonneg _)
    | cons p boxes =>
      cases boxes with
      | nil =>
        have hp:=hboxes p Ts
        have hsub:capExponents xo⊆capExponents (xo.plus p) := by
          intro m hm
          exact ⟨hm.1.trans (oz 2 (qy _ _)),
            hm.2.1.trans (oz 2 (qy _ _)),
            hm.2.2.trans (oz 2 (qy _ _))⟩
        change 0≤(capCoeff P 1 (xo.plus p) - capCoeff P 1 xo)/(2 :ℚ)^1
        exact Mk (sub_nonneg.mpr
          (capCoeff_le_of_subset P ax7 (Nc ax7 hp) hsub heq.le))
          (by norm_num)
      | cons q boxes =>
        exact h2 P (p :: q :: boxes) hP hboxes heq (by simp)
private lemma eAO (h1 :c1) (J:c9 lz) (boxes :List cy)
   (hboxes : ∀ q∈boxes,ChamberBox q) (hd:dimension J≤boxes.length) :
   tW J boxes =
     ∑ P∈J.minimalPrimesFinset,(AN J P:ℚ)*tW P boxes := by
 unfold tW
 rw [aWr (h1 J boxes.length hd) hboxes ax7,
   eME,Finset.sum_div]
 simp only [mul_div_assoc]
theorem of_children (h1 :c1) (h2 :c2) :Dr.c3:= by
 classical
 intro J boxes hboxes hd S hS
 rw [eAO h1 J boxes hboxes hd]
 refine Finset.sum_le_sum_of_subset_of_nonneg
  (fun P hP=>Ideal.mem_minimalPrimesFinset.mpr (hS P hP)) ?_
 intro P hP _
 have hmin:J.IsMinimalPrime P:=Ideal.mem_minimalPrimesFinset.mp hP
 have hdim:=(MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le hmin.le).trans hd
 exact mul_nonneg (Nat.cast_nonneg _) (b9i h2 hmin.isPrime hboxes hdim)
end
end bzB
end
section
namespace agM
noncomputable section
open aR dN vS B8
open scoped BigOperators
def a1Z (x y :cy×ℕ) :cy×ℕ:=(x.1.plus y.1,x.2+y.2)
def aYe (x :cy×ℕ) :ℚ:=(Dn x.1 :ℚ)*x.2
def diagonal (J:mD (Fin 5)) (i:Fin 5) :ℕ:=if i∈J then 2 else 1
private theorem dWH (w:Fin 5→ℕ) {i:Fin 5} {J:mD (Fin 5)}
    (hi:i∉J) :
    (∑ k,diagonal (vh i J) k*w k) =
      (∑ k,diagonal J k*w k)+w i:= by
  calc
    _ = ∑ k,(diagonal J k*w k+if k=i then w i else 0) := by
      apply p5 rfl
      intro k _
      by_cases h:k=i
      · subst k
        simp [diagonal,hi,two_mul]
      · simp [diagonal,h]
    _ = _:= by simp [sH]
private theorem gwu (B:lS) {i:Fin 5} {J:mD (Fin 5)} (hi:i∉J) :
  Vw B (diagonal (vh i J))=a1Z (Vw B (diagonal J)) (B i) := by
 simp only [Vw,a1Z,qM,dWH _ hi]
private def alt (B:lS) (s :mD (Fin 5)) (F:cy×ℕ→ℚ) :ℚ :=
 ∑ J∈s.powerset,(-1 :ℚ)^(s.card-J.card)*F (Vw B (diagonal J))
private def DB (a :cy×ℕ) (F:cy×ℕ→ℚ) (x :cy×ℕ) :ℚ :=
 F (a1Z x a)-F x
private theorem bT8 (B:lS) (F:cy×ℕ→ℚ) :
  alt B ∅ F=F (Vw B (diagonal ∅)) := by
 simp [alt]
private theorem aCd (B:lS) {s :mD (Fin 5)} {i:Fin 5}
    (hi:i∉s) (F:cy×ℕ→ℚ) :
    alt B (vh i s) F=alt B s (DB (B i) F) := by
  have hJ (J) (hJ:J∈s.powerset) :i∉J :=
    Finset.notMem_of_mem_powerset_of_notMem hJ hi
  have hdisj:Disjoint s.powerset (s.powerset.image (vh i)) := by
    apply Finset.disjoint_left.mpr
    intro J hJs hJi
    obtain ⟨T,_,rfl⟩:=Finset.mem_image.mp hJi
    exact hJ _ hJs (Finset.mem_insert_self _ _)
  have hinj:Set.InjOn (vh i) (s.powerset :Set (mD (Fin 5))) :=
    fun J hJs T hTs h=> by
      simpa [WD (hJ J hJs),WD (hJ T hTs)] using
        ox (fun U:mD (Fin 5)=>U.erase i) h
  unfold alt
  rw [Finset.powerset_insert,Finset.sum_union hdisj,Finset.sum_image hinj,
    ← sH]
  apply p5 rfl
  intro J hJs
  have hcard:=Finset.card_le_card (Finset.mem_powerset.mp hJs)
  have hstep:s.card+1-J.card=s.card-J.card+1 := by omega
  rw [ X4 hi,X4 (hJ J hJs),hstep,
    pow_succ,gwu B (hJ J hJs)]
  simp only [Nat.add_sub_add_right,DB]
  ring
private def aXN (p q r s :cy) :ℤ :=
 gI (gI (gI (gI Dn p) q) r) s ⟨0,0,0⟩
private def cpj (x :cy) :ℚ:=(Dn x :ℚ)
private def bhc (a :cy) (F:cy→ℚ) (x :cy) :ℚ:=F (x.plus a)
private def aAj (a :cy) (F:cy→ℚ) (x :cy) :ℚ:=F (x.plus a)-F x
private theorem gpW (a b:cy) (F:cy→ℚ) :
  aAj b (bhc a F)=bhc a (aAj b F) := by
 funext x
 have h: (x.plus b).plus a=(x.plus a).plus b:= by
  simp [qM,Mz ,S1]
 simp only [aAj,bhc,h]
private def ayr (F:cy→ℚ) (x :cy×ℕ) :ℚ:=F x.1
private def ahP (F:cy→ℚ) (x :cy×ℕ) :ℚ:=F x.1*x.2
private theorem bB8 (a :cy×ℕ) (F G:cy×ℕ→ℚ) :
  DB a (fun x=>F x+G x)=fun x=>DB a F x+DB a G x := by
 funext x
 unfold DB
 ring
private theorem bB9 (a :cy×ℕ) (d:ℚ) (F:cy×ℕ→ℚ) :
  DB a (fun x=>d*F x)=fun x=>d*DB a F x := by
 funext x
 unfold DB
 ring
private theorem dEA (a :cy) (d:ℕ) (F:cy→ℚ) :
 DB (a,d) (ayr F)=ayr (aAj a F) :=rfl
private theorem dEB (a :cy) (d:ℕ) (F:cy→ℚ) :
  DB (a,d) (ahP F) =
   fun x=>ahP (aAj a F) x+(d:ℚ)*ayr (bhc a F) x := by
 funext x
 simp only [DB,ahP,a1Z,zc,ayr,aAj,bhc]
 ring
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 4096 in
private theorem bGV (p q r s :cy) :
  aAj s (aAj r (aAj q (aAj p cpj))) =
   fun _=>(aXN p q r s :ℚ) := by
 funext x
 simp only [aAj,cpj,aXN,gI,Dn,qM]
 push_cast
 ring
private theorem cSx (p q g a b:cy) (d e :ℕ) (x :cy×ℕ) :
    DB (b,e) (DB (a,d) (DB (g,1) (DB (q,0)
      (DB (p,0) aYe)))) x =
      (aXN p q a b:ℚ)+(d:ℚ)*(aXN p q g b:ℚ) +
        (e :ℚ)*(aXN p q g a :ℚ) := by
  change DB (b,e) (DB (a,d) (DB (g,1) (DB (q,0)
    (DB (p,0) (ahP cpj))))) x= _
  simp only [dEB,bB8,bB9,dEA,
    Nat.cast_zero,zero_mul,y5 ,gpW,bGV]
  simp only [ahP,ayr,bhc,aAj,sub_self,zero_mul,
    wR,Dw ,Ar]
  ring
end
end agM
end
section
namespace Jq
noncomputable section
open dN vS B8 MvPolynomial
open scoped Polynomial
abbrev jJ:=Exponent
abbrev Form:=lJ (Fin 5) ℚ
abbrev Generator (B:lS) :=(i:Fin 5)×Nl (B i)
abbrev vJ (B:lS) :=lJ (Generator B) aU
instance (B:lS) :vk (Generator B) := by
 infer_instance
def zY (i:Fin 5) :jJ:=qz i 1
def squarefree (I:mD (Fin 5)) :jJ := ∑ i∈I,zY i
def jT {σ:Type} (slot:σ→Fin 5) (v :σ) :jJ:=zY (slot v)
abbrev dO {σ:Type} (slot:σ→Fin 5) :=
 Ee aU (jT slot)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def KQ {σ:Type} (slot:σ→Fin 5) (J:c9 (lJ σ aU))
    (t:jJ) :ℕ :=
  pz aU ((dO slot t).map (uh aU J).toLinearMap)
def slot (B:lS) :Generator B→Fin 5:=Sigma.fst
def DM (B:lS) :vJ B →ₐ[aU] g9 :=
 t5 fun v=>n5 v.2.val 1
def x8 (B:lS) (P:c9 g9) :c9 (vJ B) :=
 ((P.comap (DM B)).homogeneousCore (dO (slot B))).toIdeal
def RM (B:lS) (P:c9 g9) (t:jJ) :=
 P.comap (nI aU (H7 B t))
def zJ {σ:Type} (A:mD (σ →₀ ℕ)) :Set (σ →₀ ℕ) :=
 {a | ∀ b∈A,¬ b≤a}
def DL {σ:Type} (s :σ→Fin 5) (A:mD (σ →₀ ℕ)) (t:jJ) :ℕ :=
 {a∈zJ A | oK (jT s) a=t}.ncard
def Represents (p:Form) (h:jJ→ℚ) :Prop :=
 ∃ N :ℕ,∀ t:jJ,(∀ j,N≤t j)→eval (fun j=>(t j:ℚ)) p=h t
def OQ (p:Form) :Prop :=
 ∀ a :jJ,p.totalDegree≤a.degree→0≤p.coeff a
def line (t:jJ) :Form →+* ℚ[X] :=
 zh oZ (fun j=>oZ (t j:ℚ)*p9)
def aoL (J:mD (Fin 5)) :jJ :=
 Finsupp.equivFunOnFinite.symm fun i=>if i∈J then 2 else 1
end
end Jq
end
section
namespace Jq
noncomputable section
open aR dN vS B8 MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem afL (B:lS) (P:c9 g9) :
   (x8 B P).IsHomogeneous (dO (slot B)) :=
 ((P.comap (DM B)).homogeneousCore (dO (slot B))).isHomogeneous
theorem bqJ (B:lS) {P Q:c9 g9} (h:P≤Q) :
  x8 B P≤x8 B Q :=
 Ideal.homogeneousCore_mono _ (Ideal.comap_mono h)
theorem avx {B:lS} {P:c9 g9} {a :vJ B}
   {t:jJ} (ha :a∈dO (slot B) t) :
   a∈x8 B P↔DM B a∈P:= by
 constructor
 · intro h
   exact Ideal.toIdeal_homogeneousCore_le (dO (slot B)) (P.comap (DM B)) h
 · intro h
   exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨t,ha⟩ h
theorem bDb {σ:Type} (s :σ→Fin 5)
   {g:lJ σ aU} {e :jJ} (hg:g∈dO s e)
   (a :lJ σ aU) (t:jJ) :
   t7 (jT s) (t+e) (a*g) =
     t7 (jT s) t a*g:= by
 induction a using Kl with
 | monomial b r =>
   have hb:=isWeightedHomogeneous_monomial (jT s) b r rfl
   have hg' : g.IsWeightedHomogeneous (jT s) e :=hg
   simp only [Pr (hb.mul hg'),
     Pr hb,add_right_cancel_iff]
   split <;> simp_all
 | add a b ha hb=>simp [add_mul,ha,hb]
private theorem bqX {σ:Type} (s :σ→Fin 5)
   {J:c9 (lJ σ aU)} (hJ:J.IsHomogeneous (dO s))
   {g:lJ σ aU} {e :jJ} (hg:g∈dO s e) :
   (J.colon {g}).IsHomogeneous (dO s) := by
 intro t a ha
 rw [ Xu,yQ] at ha ⊢
 have hp: (DirectSum.decompose (dO s) a t:lJ σ aU) =
     t7 (jT s) t a :=
   weightedDecomposition.decompose'_apply aU (jT s) a t
 rw [hp,← bDb s hg a t]
 exact weightedHomogeneousComponent_mem_of_mem _ _ hJ ha _
private theorem bqI {B:lS} {P Q:c9 g9} {g:vJ B}
   {e :jJ} (hg:g∈dO (slot B) e)
   (h : ∀ a :g9,a*DM B g∈P↔a∈Q) :
   (x8 B P).colon {g} = x8 B Q:= by
 ext a
 rw [Ok _ _
     (bqX (slot B) (afL B P) hg),
   Ok _ _ (afL B Q)]
 apply forall_congr'
 intro t
 let z :=t7 (jT (slot B)) t a
 have hz :z∈dO (slot B) t:=weightedHomogeneousComponent_mem _ _ _
 have hg' : g.IsWeightedHomogeneous (jT (slot B)) e :=hg
 have hzg:z*g∈dO (slot B) (t+e) :=
   (weightedHomogeneousComponent_isWeightedHomogeneous t a).mul hg'
 change z∈(x8 B P).colon {g} ↔ z∈x8 B Q
 rw [ Xu,yQ,avx hzg,
   avx hz,nX ,h]
private theorem bT7 {a :cy×ℕ} {m:Exponent} (h:Qj a m) :
  m∈Nl a := by
 obtain ⟨h₁,h₂,h₃,h₄⟩:=h
 change Qj (a.1.scale 2,2*a.2) m
 simp only [Qj,t3]
 exact ⟨by omega,by omega,by omega,by omega⟩
private theorem bT6 {a :cy×ℕ} {m n:Exponent}
  (hm:Qj a m) (hn:Qj a n) :m+n∈Nl a := by
 obtain ⟨hm₁,hm₂,hm₃,hm₄⟩:=hm
 obtain ⟨hn₁,hn₂,hn₃,hn₄⟩:=hn
 change Qj (a.1.scale 2,2*a.2) (m+n)
 simp only [Qj,t3 ,KH,NZ,sH]
 exact ⟨by omega,by omega,by omega,by omega⟩
private theorem a3P (B:lS) (i:Fin 5) (D:g9)
   (hD : ∀ m∈D.support,m∈Nl (B i)) :
   ∃ g:vJ B,g∈dO (slot B) (zY i)∧DM B g=D:= by
 classical
 let gen (m:D.support) :Generator B:=⟨i,⟨m,hD m m.property⟩⟩
 refine ⟨∑ m:D.support,C (D.coeff m)*lI (gen m),?_,?_⟩
 · apply Ww
   intro m _
   have hc: (C (D.coeff m) :vJ B).IsWeightedHomogeneous (jT (slot B)) 0 :=
     isWeightedHomogeneous_C _ _
   have hx : (lI (gen m) :vJ B).IsWeightedHomogeneous (jT (slot B)) (zY i) :=
     G0 aU (jT (slot B)) (gen m)
   rw [mem_weightedHomogeneousSubmodule]
   simpa only [wR] using hc.mul hx
 · simp only [t8 ,nX ,DM,aeval_C,algebraMap_eq,aeval_X,
     C_mul_monomial,sS ,gen]
   rw [Finset.sum_coe_sort D.support (fun m=>n5 m (D.coeff m))]
   exact D.support_sum_monomial_coeff
private theorem bLe {P:c9 g9} {D:g9}
   (h:p6 (lV P D)) (a :g9) :
   a*D∈P↔a∈P:= by
 constructor
 · intro ha
   rw [← wA] at ha ⊢
   apply h
   change lV P D * lV P a=lV P D *0
   rw [vi ,u5 ,← nX ,ha]
 · exact P.mul_mem_right D
private theorem bwV {P:c9 g9} {D:g9}
   (h:p6 (lV P D)) (a :g9) :
   a*D∈i9 P (D^2)↔a∈i9 P D:= by
 constructor
 · intro ha
   obtain ⟨x,hx,y,hy,hxy⟩:=Submodule.mem_sup.mp ha
   obtain ⟨c,hc⟩:=Ideal.mem_span_singleton'.mp hy
   have he : (a - c*D)*D =x := by
     rw [sub_mul,← hxy,← hc]
     ring
   have hm:a - c*D∈P:=(bLe h _).mp (by rw [he]; exact hx)
   exact Submodule.mem_sup.mpr
     ⟨a - c*D,hm,c*D,Ideal.mem_span_singleton'.mpr ⟨c,rfl⟩,sub_add_cancel _ _⟩
 · intro ha
   obtain ⟨x,hx,y,hy,hxy⟩:=Submodule.mem_sup.mp ha
   obtain ⟨c,rfl⟩:=Ideal.mem_span_singleton'.mp hy
   exact Submodule.mem_sup.mpr ⟨x*D,P.mul_mem_right D hx,c*D *D,
     Ideal.mem_span_singleton'.mpr ⟨c,by ring⟩,by rw [← add_mul,hxy]⟩
theorem b2l (B:lS) (P:c9 g9) (i:Fin 5) (D:g9)
    (hD:agB (B i).1 (B i).2 D) (hr :p6 (lV P D)) :
    ∃ f g:vJ B,
      f∈dO (slot B) (zY i)∧g∈dO (slot B) (zY i) ∧
      (x8 B P).colon {f} = x8 B P ∧
      x8 B P ⊔ oY {f} ≤ x8 B (i9 P (D^2)) ∧
      (x8 B (i9 P (D^2))).colon {g} = x8 B (i9 P D) ∧
      x8 B (i9 P (D^2)) ⊔ oY {g} ≤ x8 B (i9 P D) := by
  classical
  have hs (m:Exponent) (hm:m∈D.support) :Qj (B i) m :=
    ⟨(hD.1 m hm).1,(hD.1 m hm).2.1,(hD.1 m hm).2.2,hD.2 m hm⟩
  have hs₂ (m:Exponent) (hm:m∈(D^2).support) :m∈Nl (B i) := by
    rw [ze] at hm
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (support_mul D D hm)
    exact bT6 (hs a ha) (hs b hb)
  obtain ⟨f,hf,hfmap⟩:=a3P B i (D^2) hs₂
  obtain ⟨g,hg,hgmap⟩:=a3P B i D (fun m hm=>bT7 (hs m hm))
  refine ⟨f,g,hf,hg,?_,?_,?_,?_⟩
  · apply bqI hf
    intro a
    rw [hfmap]
    have h:p6 (lV P (D^2)) := by
      rw [map_pow]
      exact IsLeftRegular.pow 2 hr
    exact bLe h a
  · refine xI (bqJ B Kz) ((G2 _).mpr ?_)
    rw [avx hf,hfmap]
    exact (Cy :oY {D^2} ≤ i9 P (D^2))
      (Dz _)
  · apply bqI hg
    intro a
    rw [hgmap]
    exact bwV hr a
  · refine xI (bqJ B (xI Kz ?_))
      ((G2 _).mpr ?_)
    · exact ((G2 _).mpr
        (Ideal.mem_span_singleton'.mpr ⟨D,(ze D).symm⟩)).trans Cy
    · rw [avx hg,hgmap]
      exact (Cy :oY {D} ≤ i9 P D) (Dz _)
end
end Jq
end
section
namespace agM
noncomputable section
open aR dN vS B8 MvPolynomial
open scoped BigOperators Pointwise
theorem gNm (a :cy×ℕ) :0∈Nl a := by
 simp [Nl,Qj]
theorem gNk (B:lS) (t:Fin 5→ℕ) :
   0∈H7 B t :=
 ⟨fun _ _=>0,fun i _=>gNm (B i),by simp⟩
private theorem eFA {S:Set Exponent} {n:ℕ} {m:Exponent}
   (hm:m∈n•S) :
   ∃ P:lJ S aU,
     P.totalDegree≤n∧nI aU S P=n5 m 1 := by
 induction n generalizing m with
 | zero =>
   rw [zE,yl] at hm
   subst m
   exact ⟨1,by simp,by simp⟩
 | succ n ih =>
   rw [succ_nsmul'] at hm
   obtain ⟨a,ha,b,hb,rfl⟩:=hm
   obtain ⟨P,hdeg,hP⟩:=ih hb
   refine ⟨lI ⟨a,ha⟩*P,?_,?_⟩
   · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_X]; omega)
   · rw [nX ,Dv,hP,II,Ar]
theorem bJv (S:Set Exponent) (h0:0∈S) (n:ℕ) :
    p7 (zg (nI aU S) ⊥) n=(n•S).ncard:= by
  classical
  let φ:=nI aU S
  let j:=Ideal.kerLiftAlg φ
  let V:=uW (t9 φ) n
  have hmap :V.map j.toLinearMap=qJ aU (n•S) := by
    apply vl
    · rintro _ ⟨v,hv,rfl⟩
      obtain ⟨P,hP,rfl⟩:=mem_quotientDegreeLE.mp hv
      exact IT h0 hP
    · rw [zm,Kc]
      rintro _ ⟨m,hm,rfl⟩
      obtain ⟨P,hP,hφ⟩:=eFA hm
      exact ⟨_,Nj hP,hφ⟩
  rw [← RingHom.ker_eq_comap_bot]
  change pz aU V= _
  calc
    _=pz aU (V.map j.toLinearMap) :=
      (SU _ (Ideal.kerLiftAlg_injective φ) V).finrank_eq
    _ = _:= by
      rw [hmap,LO (C9 aU _),
        zi]
private def aNG:Exponent ≃ (Fin 4 →₀ ℕ)×ℕ :=
  Finsupp.equivFunOnFinite.trans
    ((Fin.snocEquiv (fun _:Fin 5=>ℕ)).symm.trans
      ((Equiv.prodComm ℕ (Fin 4→ℕ)).trans
        (Equiv.prodCongr Finsupp.equivFunOnFinite.symm (Equiv.refl ℕ))))
theorem euK (a :cy×ℕ) :
    (Nl a).ncard=(Dr.capExponents a.1).ncard*(2*a.2+1) := by
  classical
  let e :Nl a ≃ Dr.capExponents a.1×Fin (2*a.2+1) :=
    { toFun:= fun m=>⟨⟨(aNG m).1,by
        simpa [aNG,Dr.capExponents,t4 ,Fin.init,
          t3]
          using Aa m.property.1 (Aa m.property.2.1 m.property.2.2.1)⟩,
        ⟨(aNG m).2,Nat.lt_succ_of_le m.property.2.2.2⟩⟩
      invFun:= fun x=>⟨aNG.symm (x.1,x.2),by
        have hx :=x.1.property
        change (x.1.val.degree≤_)∧_ at hx
        simp only [t4] at hx
        change (∑ i:Fin 4,EK (α:= fun _=>ℕ) x.1.val (x.2 :ℕ) i.castSucc)≤2*a.1.b ∧
          (∑ i:Fin 4,i.val*EK (α:= fun _=>ℕ) x.1.val (x.2 :ℕ) i.castSucc)≤2*a.1.j ∧
          EK (α:= fun _=>ℕ) x.1.val (x.2 :ℕ) (uJ (3:Fin 4))≤2*a.1.t ∧
          EK (α:= fun _=>ℕ) x.1.val (x.2 :ℕ) (pU 4)≤2*a.2
        simpa only [Fin.snoc_castSucc,Fin.snoc_last] using
          Aa hx.1 (Aa hx.2.1 (Aa hx.2.2 (UP x.2.isLt)))⟩
      left_inv := fun m=>vH (aNG.symm_apply_apply m)
      right_inv := fun x=>Prod.ext
        (vH (ox Prod.fst (aNG.apply_symm_apply (x.1,(x.2 :ℕ)))))
        (Fin.ext (ox Prod.snd (aNG.apply_symm_apply (x.1,(x.2 :ℕ))))) }
  simpa only [zi ,Nat.card_prod,Nat.card_fin] using Nat.card_congr e
end
end agM
end
section
namespace aRS
noncomputable section
open aR dN Dr
open scoped BigOperators
def xl {k :ℕ} (boxes :Fin k→cy) (w:Fin k→ℕ) :Shape :=
 ⟨∑ i,w i*(boxes i).b,∑ i,w i*(boxes i).j,∑ i,w i*(boxes i).t⟩
def alz (P:c9 lz) (p:cy) :Submodule aU (lz ⧸ P) :=
  (qJ aU (capExponents p)).map
    (uh aU P).toLinearMap
def aAp {k m:ℕ} (slot:Fin m→Fin k) (bad:mD (Fin m →₀ ℕ))
    (w:Fin k→ℕ) :ℕ :=
  {e :Fin m →₀ ℕ | (∀ b∈bad,¬ b≤e) ∧
    ∀ i,∑ j∈Finset.univ.filter (fun j=>slot j=i),e j=w i}.ncard
end
end aRS
end
section
namespace aRS
noncomputable section
open aR dN Dr aiK MvPolynomial Polynomial Filter
open scoped BigOperators Pointwise
def c1 :Prop :=
  ∀ (P:c9 lz) (k :ℕ) (boxes :Fin k→cy),
    P.IsPrime→(∀ i,ChamberBox (boxes i)) →
    ∃ (m:ℕ) (slot:Fin m→Fin k) (bad:mD (Fin m →₀ ℕ)),
      ∀ w,pz aU (alz P (xl boxes w))=aAp slot bad w
def c2 :Prop :=
  ∀ (k m:ℕ) (slot:Fin m→Fin k) (bad:mD (Fin m →₀ ℕ)),
    ∃ (T r :ℕ) (f :Fin r→Fin k→ℕ→ℚ),
      (∀ a i,Monotone (f a i))∧(∀ a i n,0≤f a i n) ∧
      ∀ (w:Fin k→ℕ),(∀ i,T≤w i) →
        (aAp slot bad w:ℚ) = ∑ a,∏ i,f a i (w i)
private def shift {k :ℕ} (w:Fin k→ℕ) (i:Fin k) (n:ℕ) :Fin k→ℕ :=
 Function.update w i (w i+n)
private def diff {k :ℕ} (F: (Fin k→ℕ)→ℚ) (dirs :List (Fin k)) (n:ℕ)
   (w:Fin k→ℕ) :ℚ :=
 match dirs with
 | []=>F w
 | i :: rest=>diff F rest n (shift w i n) - diff F rest n w
private theorem le_shift {k :ℕ} (w:Fin k→ℕ) (i:Fin k) (n:ℕ) (j:Fin k) :
   w j≤ shift w i n j:= by
 by_cases h:j=i
 · subst j
   simp [shift]
 · simp [shift,Il h]
private theorem diff_congr {k :ℕ} {F G: (Fin k→ℕ)→ℚ} {T:ℕ}
   (h : ∀ w,(∀ i,T≤w i)→F w=G w)
   (dirs :List (Fin k)) (n:ℕ) (w:Fin k→ℕ) (hw : ∀ i,T≤w i) :
   diff F dirs n w=diff G dirs n w:= by
 induction dirs generalizing w with
 | nil=>exact h w hw
 | cons i rest ih =>
   rw [diff,diff,ih w hw,ih (shift w i n) (fun j=>(hw j).trans (le_shift w i n j))]
private theorem dWQ {k r :ℕ} (F:Fin r→(Fin k→ℕ)→ℚ)
   (dirs :List (Fin k)) (n:ℕ) (w:Fin k→ℕ) :
   diff (fun v => ∑ a,F a v) dirs n w = ∑ a,diff (F a) dirs n w:= by
 induction dirs generalizing w with
 | nil=>rfl
 | cons i rest ih =>
   simp only [diff,ih,Sd]
private theorem dWO {k :ℕ} (f :Fin k→ℕ→ℚ) (dirs :List (Fin k))
   (hd:dirs.Nodup) (n:ℕ) (w:Fin k→ℕ) :
   diff (fun v => ∏ i,f i (v i)) dirs n w =
     ∏ i,if i∈dirs then f i (w i+n) - f i (w i) else f i (w i) := by
 induction dirs generalizing w with
 | nil=>simp [diff]
 | cons i rest ih =>
   obtain ⟨hi,hr⟩:=List.nodup_cons.mp hd
   simp only [diff,ih hr]
   let g (v :Fin k→ℕ) (j:Fin k) :=
     if j∈rest then f j (v j+n) - f j (v j) else f j (v j)
   let s :=(Ml :mD (Fin k)).erase i
   have hs : ∏ j∈s,g (shift w i n) j = ∏ j∈s,g w j:= by
     apply S2 rfl
     intro j hj
     simp [g,shift,Il (QL hj)]
   let h (j:Fin k) :=
     if j∈i :: rest then f j (w j+n) - f j (w j) else f j (w j)
   have hh : ∏ j∈s,h j = ∏ j∈s,g w j:= by
     apply S2 rfl
     intro j hj
     simp [h,g,QL hj]
   change (∏ j,g (shift w i n) j)-(∏ j,g w j) = ∏ j,h j
   rw [← NW _ _ (u9 i),
     ← NW _ _ (u9 i),
     ← NW _ _ (u9 i)]
   change g (shift w i n) i*(∏ j∈s,g (shift w i n) j) -
     g w i*(∏ j∈s,g w j)=h i*(∏ j∈s,h j)
   rw [hs,hh,← sub_mul]
   simp [g,h,shift,hi]
private theorem guK (h:c2) {k m:ℕ}
   (slot:Fin m→Fin k) (bad:mD (Fin m →₀ ℕ))
   (dirs :List (Fin k)) (hd:dirs.Nodup) :
   ∃ T:ℕ,∀ n (w:Fin k→ℕ),(∀ i,T≤w i) →
     0≤diff (fun v=>(aAp slot bad v :ℚ)) dirs n w:= by
 obtain ⟨T,r,f,hmono,hnonneg,hcount⟩:=h k m slot bad
 refine ⟨T,fun n w hw => ?_⟩
 rw [diff_congr hcount dirs n w hw,dWQ]
 apply Finset.sum_nonneg
 intro a _
 rw [dWO (f a) dirs hd n w]
 apply Finset.prod_nonneg
 intro i _
 split
 · exact sub_nonneg.mpr (hmono a i (qy _ _))
 · exact hnonneg a i (w i)
private abbrev capMap (p:cy) :=nI aU (capExponents p)
private abbrev HW (P:c9 lz) (p:cy) :=P.comap (capMap p).toRingHom
private lemma cap_dimension (P:c9 lz) {p:cy} (hp:ChamberBox p) :
  (oD (HW P p)).natDegree=dimension P:= by
 have hsurj:sI (capMap p) := by
  apply x7
  obtain ⟨hb,hj,ht⟩:=hp
  intro i
  fin_cases i <;> norm_num [OW,vj] <;> omega
 exact G5 (capMap p) hsurj P
private lemma aDS (S:Set (Fin 4 →₀ ℕ)) (n:ℕ) (e :Fin 4 →₀ ℕ)
   (he :e∈n•S) :
   ∃ f :lJ S aU,f.totalDegree≤n∧nI aU S f=n5 e 1 := by
 induction n generalizing e with
 | zero =>
   rw [zE,yl] at he
   subst e
   exact ⟨1,by simp,by simp⟩
 | succ n ih =>
   rw [G9] at he
   obtain ⟨a,ha,b,hb,rfl⟩:=he
   obtain ⟨f,hn,hf⟩:=ih a ha
   refine ⟨f*lI ⟨b,hb⟩,(totalDegree_mul _ _).trans ?_,?_⟩
   · simpa only [totalDegree_X] using VH hn 1
   · rw [nX ,hf,Dv,II,sS]
private theorem cD0 (P:c9 lz) {p:cy} (hp:ChamberBox p) (n:ℕ) :
    pz aU (alz P (p.scale n))=p7 (HW P p) n:= by
  let I:=HW P p
  let g:=G3 P (capMap p) (yL :I≤HW P p)
  have hg:qx g:=Nr
  let V:=uW I n
  have hmap :V.map g.toLinearMap=alz P (p.scale n) := by
    apply vl
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨f,hf,rfl⟩:=mem_quotientDegreeLE.mp hx
      change lV P (capMap p f)∈alz P (p.scale n)
      refine ⟨capMap p f,?_,rfl⟩
      rw [← aIH p hp n]
      exact IT (biS p) hf
    · unfold alz
      rw [Submodule.map_le_iff_le_comap,zm,Kc]
      rintro _ ⟨e,he,rfl⟩
      rw [← aIH p hp n] at he
      obtain ⟨f,hf,hφ⟩:=aDS _ n e he
      have hmk :lV I f∈V:=Nj hf
      exact ⟨lV I f,hmk,by
        change lV P (capMap p f)=lV P (n5 e 1)
        rw [hφ]⟩
  rw [← hmap]
  exact (SU _ hg V).finrank_eq.symm
private lemma cDZ (P:c9 lz) {p q:cy} (h:aO p q) :
  pz aU (alz P p)≤pz aU (alz P q) := by
 have :=restrictSupport_finite (R:=aU) (Set.toFinite (capExponents q))
 have :Et aU (alz P q) := by unfold alz; infer_instance
 apply Qy
 apply Ye
 apply restrictSupport_mono
 intro e he
 exact ⟨he.1.trans (oz 2 h.1),
  he.2.1.trans (oz 2 h.2.1),he.2.2.trans (oz 2 h.2.2)⟩
private lemma bOv {k :ℕ} (boxes :Fin k→cy) (w:Fin k→ℕ)
   (hb : ∀ i,ChamberBox (boxes i)) (hw : ∃ i,0<w i) :ChamberBox (xl boxes w) := by
 obtain ⟨i,hi⟩:=hw
 refine ⟨?_,?_,?_⟩
 · change (∑ j,w j*(boxes j).j) ≤ ∑ j,w j*(boxes j).b
   exact t6 (fun j _=>oz (w j) (hb j).1)
 · change 3*(∑ j,w j*(boxes j).t) ≤ ∑ j,w j*(boxes j).j
   rw [uz]
   apply t6
   intro j _
   rw [xu]
   exact oz _ (hb j).2.1
 · change 0 < ∑ j,w j*(boxes j).t
   exact (z9 hi (hb i).2.2).trans_le
     (Mw (fun j _=>EP (w j*(boxes j).t)) (u9 i))
private lemma gwB {k :ℕ} (boxes :Fin k→cy) (w:Fin k→ℕ) (i:Fin k) :
    xl boxes (shift w i 1)=(xl boxes w).plus (boxes i) := by
  have h (a :Fin k→ℕ) :
      (∑ j,shift w i 1 j*a j)=(∑ j,w j*a j)+a i:= by
    calc
      _ = ∑ j,(w j*a j+if j=i then a i else 0) := by
        apply p5 rfl
        intro j _
        by_cases hj:j=i
        · subst j
          simp [shift,FR]
        · simp [shift,hj]
      _ = _:= by simp [sH]
  simp only [xl,qM,h]
private lemma gwA {k :ℕ} (boxes :Fin k→cy) (w:Fin k→ℕ) (N T:ℕ) :
  xl boxes (fun i=>N*w i+T) =
   ((xl boxes w).scale N).plus (xl boxes (fun _=>T)) := by
 simp only [xl,t3 ,qM,FR,sH,
  Nat.mul_assoc,uz]
private lemma dGj {k :ℕ} (w:Fin k→ℕ) (i:Fin k) (N T:ℕ) :
   shift (fun j=>N*w j+T) i N=fun j=>N*shift w i 1 j+T:= by
 funext j
 by_cases h:j=i
 · subst j
   simp [shift,NZ,Nat.add_right_comm]
 · simp [shift,Il h]
private lemma dEJ {k :ℕ} (P:c9 lz) (boxes :Fin k→cy)
    (w:Fin k→ℕ) (hp:ChamberBox (xl boxes w)) (T:ℕ) :
    ∃ C:ℕ,∀ N,
      p7 (HW P (xl boxes w)) N ≤
        pz aU (alz P (xl boxes (fun i=>N*w i+T))) ∧
      pz aU (alz P (xl boxes (fun i=>N*w i+T))) ≤
        p7 (HW P (xl boxes w)) (N+C) := by
  let p:=xl boxes w
  let q:=xl boxes (fun _=>T)
  let C:=q.b+q.j+q.t
  have hbox :aO q (p.scale C) := by
    obtain ⟨hb,hj,ht⟩:=hp
    have hj' : 0<p.j:= by change 3*p.t≤p.j at hj; change 0<p.t at ht; omega
    have hb' : 0<p.b:=hj'.trans_le hb
    exact ⟨(show q.b≤C by dsimp [C]; omega).trans (Nat.le_mul_of_pos_right _ hb'),
      (show q.j≤C by dsimp [C]; omega).trans (Vs  _ hj'),
      (show q.t≤C by dsimp [C]; omega).trans (Vs  _ ht)⟩
  refine ⟨C,fun N => ?_⟩
  rw [← cD0 P hp N,← cD0 P hp (N+C),gwA]
  constructor
  · exact cDZ P ⟨qy _ _,qy _ _,qy _ _⟩
  · apply cDZ P
    obtain ⟨hb,hj,ht⟩:=hbox
    exact ⟨by simpa [Shape.scale,Shape.plus,Nat.add_mul] using Nat.add_le_add_left hb (N*p.b),
      by simpa [t3 ,qM ,FR ] using Yi  hj (N*p.j),
      by simpa [t3 ,qM ,FR ] using Yi  ht (N*p.t)⟩
private theorem dWI {k :ℕ} (P:c9 lz) (boxes :Fin k→cy)
    (hb : ∀ i,ChamberBox (boxes i)) (d T:ℕ) (hd:dimension P≤d)
    (dirs :List (Fin k)) (w:Fin k→ℕ) (hw : ∃ i,0<w i) :
    ∃ L U:ℚ[X],L.natDegree≤d∧U.natDegree≤d ∧
      L.coeff d=diff (fun v=>capCoeff P d (xl boxes v)) dirs 1 w ∧
      U.coeff d=diff (fun v=>capCoeff P d (xl boxes v)) dirs 1 w ∧
      ∀ᶠ N :ℕ in pG,
        L.eval (N :ℚ)≤diff (fun v=>(pz aU (alz P (xl boxes v)) :ℚ))
          dirs N (fun i=>N*w i+T) ∧
        diff (fun v=>(pz aU (alz P (xl boxes v)) :ℚ))
          dirs N (fun i=>N*w i+T)≤U.eval (N :ℚ) := by
  induction dirs generalizing w with
  | nil =>
    let p:=xl boxes w
    let I:=HW P p
    let L:=oD I
    have hp:=bOv boxes w hb hw
    have hL:L.natDegree≤d:=(cap_dimension P hp).trans_le hd
    obtain ⟨C,hC⟩:=dEJ P boxes w hp T
    refine ⟨L,Gj (C:ℚ) L,hL,(natDegree_taylor _ _).trans_le hL,rfl,
      UY _ hL,?_⟩
    obtain ⟨N₀,hN₀⟩:=exists_eval_affineHilbertPolynomial I
    filter_upwards [WY N₀] with N hN
    change (oD I).eval (N :ℚ)≤_ ∧
      _≤(Gj (C:ℚ) (oD I)).eval (N :ℚ)
    rw [taylor_eval,← zc,hN₀ N hN,hN₀ (N+C) (hN.trans (qy _ _))]
    simp only [diff]
    exact ⟨by exact_mod_cast (hC N).1,by exact_mod_cast (hC N).2⟩
  | cons i dirs ih =>
    have hwi : ∃ j,0<shift w i 1 j:= by
      obtain ⟨j,hj⟩:=hw
      exact ⟨j,hj.trans_le (le_shift w i 1 j)⟩
    obtain ⟨L₁,U₁,hL₁,hU₁,hcL₁,hcU₁,he₁⟩:=ih (shift w i 1) hwi
    obtain ⟨L₀,U₀,hL₀,hU₀,hcL₀,hcU₀,he₀⟩:=ih w hw
    refine ⟨L₁-U₀,U₁ - L₀,(natDegree_sub_le _ _).trans (max_le hL₁ hU₀),
      (natDegree_sub_le _ _).trans (max_le hU₁ hL₀),?_,?_,?_⟩
    · rw [ Xo ,hcL₁,hcU₀,diff]
    · rw [ Xo ,hcU₁,hcL₀,diff]
    · filter_upwards [he₁,he₀] with N a b
      simp only [diff,dGj,Polynomial.eval_sub]
      exact ⟨sub_le_sub a.1 b.2,sub_le_sub a.2 b.1⟩
private lemma dWN {k :ℕ} (boxes :Fin k→cy) (H :cy→ℚ)
   (dirs :List (Fin k)) (w:Fin k→ℕ) :
   diff (fun v=>H (xl boxes v)) dirs 1 w =
     BE H (dirs.map boxes) (xl boxes w) := by
 induction dirs generalizing w with
 | nil=>rfl
 | cons i rest ih =>
   simp only [diff,ih,List.map_cons,BE,gwB]
theorem of_children (h1 :c1) (h2 :c2) :bzB.c2 := by
 intro P boxes hp hb hd _
 let p:Shape :=⟨3, 3,1⟩
 let B:Fin (boxes.length+1)→Shape :=Fin.cons p boxes.get
 let dirs :List (Fin (boxes.length+1)) :=List.ofFn (fun i:Fin boxes.length=>i.succ)
 let w:Fin (boxes.length+1)→ℕ:=Av 0 1
 have hB (i:Fin (boxes.length+1)) :ChamberBox (B i) := by
   refine Fin.cases ?_ (fun j => ?_) i
   · change ChamberBox p
     exact ⟨by decide,by decide,by decide⟩
   · exact hb _ (List.get_mem _ _)
 have hdirs :dirs.Nodup:=List.nodup_ofFn_ofInjective (Fin.succ_injective _)
 have hmap :dirs.map B=boxes := by
   rw [List.map_ofFn]
   exact List.ofFn_get boxes
 have hw : ∃ i,0<w i:=⟨0,by simp [w]⟩
 have hbase :xl B w=p:= by
   simp [xl,w,Kv,Vl,B]
 obtain ⟨m,slot,bad,hcount⟩:=h1 P _ B hp hB
 obtain ⟨T,hpos⟩:=guK h2 slot bad dirs hdirs
 obtain ⟨_,U,_,hU,_,hc,hu⟩:=dWI P B hB boxes.length T hd.le dirs w hw
 have hnonneg : ∀ᶠ N :ℕ in pG,0≤U.eval (N :ℚ) := by
   filter_upwards [hu] with N hN
   refine le_trans ?_ hN.2
   rw [diff_congr (T:=0) (fun v _=> by rw [hcount]) dirs N _ (fun _=>EP _)]
   exact hpos N _ (fun _=>GY _ _)
 have hcoeff :=RJ hU hnonneg
 rw [hc,dWN,hmap,hbase] at hcoeff
 exact Mk hcoeff (by positivity)
end
end aRS
end
section
namespace bzz
open aR Dr aiK Kd
open scoped BigOperators Pointwise
private theorem bwG {ι:Type} [oq ι] (fF:ι→cy)
   (e :Kb fF →₀ ℕ) (i:ι) :
   oK (step ∘ Fd fF) e i≠0 ↔
     ∃ v :Kb fF,v.1=i∧e v≠0:= by
 classical
 simp only [Fa ,NX ,Finset.sum_apply,G6,
   Fd,step,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,Nat.cast_id]
 rw [← Nat.pos_iff_ne_zero,Finset.sum_pos_iff]
 constructor
 · rintro ⟨v,_,hv⟩
   by_cases hvi:v.1=i
   · exact ⟨v,hvi,Nat.ne_of_gt (by simpa [hvi] using hv)⟩
   · rw [MS (Ne.symm hvi)] at hv
     simp at hv
 · rintro ⟨v,hvi,hv⟩
   exact ⟨v,Finsupp.mem_support_iff.mpr hv,by simpa [hvi] using Kp hv⟩
private theorem bKP {ι:Type} [oq ι] (fF:ι→cy) :
   Yz fF 0=0:= by
 ext m
 simp only [yl,Yz,G1]
 constructor
 · rintro ⟨e,hdeg,hexp⟩
   have he :e=0:= by
     ext v
     rw [Te]
     by_contra hv
     have hslot:=(bwG fF e v.1).mpr ⟨v,rfl,hv⟩
     simp [hdeg] at hslot
   simpa [he] using hexp.symm
 · rintro rfl
   exact ⟨0,qm _,qm _⟩
private theorem ccO {ι:Type} [oq ι] (fF:ι→cy)
    (a :ι→ℕ) (i:ι) :
    Yz fF (a+step i) =
      Yz fF a+capExponents (fF i) := by
  ext m
  constructor
  · rintro ⟨e,hdeg,hexp⟩
    have hne :oK (step ∘ Fd fF) e i≠0:= by
      simp [hdeg,step]
    obtain ⟨v,hvi,hv⟩:=(bwG fF e i).mp hne
    let e' := e-Finsupp.single v 1
    have hdeg' : oK (step ∘ Fd fF) e' + step i=a+step i:= by
      have h:=WW (w:=step ∘ Fd fF) hv
      calc
        _=oK (step ∘ Fd fF) e := by
          simpa only [e',G6,Fd,hvi] using h
        _ = _:=hdeg
    refine ⟨oK (fun u:Kb fF=>u.2.val) e',
      ⟨e',add_right_cancel hdeg',rfl⟩,v.2.val,?_,?_⟩
    · simpa only [hvi] using v.2.property
    · exact (WW hv).trans hexp
  · rintro ⟨m',⟨e,hdeg,hexp⟩,w,hw,rfl⟩
    let v :Kb fF:=⟨i,⟨w,hw⟩⟩
    refine ⟨e+Finsupp.single v 1,?_,?_⟩
    · rw [pQ,KI,one_smul,hdeg] <;> rfl
    · simp only [pQ,KI,one_smul,hexp,v]
private theorem bWh:capExponents ⟨0,0,0⟩=0:= by
 ext m
 simp only [OW,yl,Nat.mul_zero]
 constructor
 · intro hm
   have h:=hm.1
   ext k
   fin_cases k
   · change m 0=0; omega
   · change m 1=0; omega
   · change m 2=0; omega
   · change m 3=0; omega
 · rintro rfl
   simp
private theorem dfP {ι:Type} [pL ι] [oq ι] (a :ι→ℕ)
   (i:ι) (f :ι→ℕ) :
   (∑ k,(a+step i) k*f k)=(∑ k,a k*f k)+f i:= by
 simp only [Pi.add_apply,add_mul,sH]
 congr 1
 rw [Fintype.sum_eq_single i]
 · simp [step]
 · intro k hki
   simp [step,MS hki]
private theorem gpY {ι:Type} [pL ι] [oq ι] (fF:ι→cy)
  (a :ι→ℕ) (i:ι) :
  ku fF (a+step i)=(ku fF a).plus (fF i) := by
 simp only [ku,qM,dfP]
private theorem cND {ι:Type} (a :ι→ℕ) (ha :a≠0) :
  ∃ i,a i≠0:= by
 by_contra! h
 exact ha (funext h)
private theorem dHT {ι:Type} [pL ι] (fF:ι→cy)
    (hsh : ∀ i,ChamberBox (fF i)) (a :ι→ℕ) (ha :a≠0) :
    ChamberBox (ku fF a) := by
  refine ⟨t6 fun i _=>oz (a i) (hsh i).1,?_,?_⟩
  · dsimp [ku]
    rw [uz]
    refine t6 fun i _ => ?_
    rw [xu 3 (a i)]
    exact oz (a i) (hsh i).2.1
  · obtain ⟨i,hi⟩:=cND a ha
    exact (z9 (Kp hi) (hsh i).2.2).trans_le
      (Mw (f := fun k=>a k*(fF k).t)
        (fun _ _=>EP _) (u9 i))
theorem proof :Kd.c2 := by
  intro ι _ _ fF hsh a
  induction a using WellFounded.induction (measure (fun b:ι→ℕ => ∑ i,b i)).wf with
  | h a ih =>
    by_cases ha :a=0
    · rw [ha,bKP]
      simpa [ku] using bWh.symm
    · obtain ⟨i,hi⟩:=cND a ha
      let b:=a - step i
      have hab:b+step i=a := by
        funext k
        change a k - step i k+step i k=a k
        apply Nat.sub_add_cancel
        by_cases hki:k=i
        · subst k
          simpa [step] using Nat.one_le_iff_ne_zero.mpr hi
        · simp [step,MS hki]
      have hsum: (∑ k,a k)=(∑ k,b k)+1 := by
        rw [← hab]
        simpa only [Nat.mul_one] using dfP b i (fun _=>1)
      have hlt: (∑ k,b k) < ∑ k,a k := by omega
      rw [← hab,ccO,gpY]
      by_cases hb:b=0
      · rw [hb,bKP,wR]
        cases fF i
        simp [ku,qM]
      · rw [ih b hlt,anN (dHT fF hsh b hb) (hsh i)]
end bzz
end
section
namespace ap8
noncomputable section
open MvPolynomial Filter
open scoped BigOperators
variable {ι:Type}
def BZ (P:lJ ι ℚ) (u v :ι→ℕ) :wB ℚ :=
  t5 (fun i=>oZ (v i:ℚ)*p9 +
    oZ (u i:ℚ)) P
theorem bgE (P:lJ ι ℚ) (u v :ι→ℕ) (n:ℕ) :
   (BZ P u v).eval (n:ℚ)=oy (fun i=>((u i+n*v i:ℕ) :ℚ)) P:= by
 let φ:wB ℚ →ₐ[ℚ] ℚ:=Polynomial.aeval (n:ℚ)
 change φ (BZ P u v)= _
 rw [BZ,MvPolynomial.comp_aeval_apply,MvPolynomial.aeval_eq_eval]
 have he : (fun i=>φ (oZ (v i:ℚ)*p9 +
     oZ (u i:ℚ)))=(fun i=>((u i+n*v i:ℕ) :ℚ)) := by
   funext i
   simp [φ,Polynomial.aeval_def,u5 ,FU]
 rw [he]
private theorem prod_top (f :ι→wB ℚ) (e :ι →₀ ℕ)
   (h : ∀ i,(f i).natDegree≤1) (s :mD ι) :
   (∏ i∈s,f i^e i).natDegree ≤ ∑ i∈s,e i ∧
   (∏ i∈s,f i^e i).coeff (∑ i∈s,e i) = ∏ i∈s,(f i).coeff 1^e i:= by
 classical
 induction s using Finset.induction_on with
 | empty=>simp
 | insert i s hi ih =>
   simp only [Finset.prod_insert hi,Pf hi]
   have hpow: ((f i)^e i).natDegree≤e i:= by
     simpa using Polynomial.natDegree_pow_le_of_le (e i) (h i)
   refine ⟨(Polynomial.natDegree_mul_le).trans (Eg hpow ih.1),?_⟩
   rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpow ih.1,ih.2]
   rw [show (f i^e i).coeff (e i)=(f i).coeff 1^e i by
     simpa only [sS] using Polynomial.coeff_pow_of_natDegree_le (m:=e i) (h i)]
private theorem dsJ (f :ι→wB ℚ) (h : ∀ i,(f i).natDegree≤1)
   (P:lJ ι ℚ) (d:ℕ) (hd:P.totalDegree≤d) :
   (t5 f P).coeff d =
     oy (fun i=>(f i).coeff 1) (C4 d P) := by
 classical
 conv_lhs=>rw [P.as_sum,t8 ,TH]
 rw [homogeneousComponent_apply,t8 ,Finset.sum_filter]
 apply p5 rfl
 intro e he
 have hle :e.degree≤d:=(F9 he).trans hd
 rw [MvPolynomial.aeval_monomial,← Polynomial.C_eq_algebraMap,VC]
 by_cases hEq:e.degree=d
 · rw [z7 hEq,← hEq,Bf ,KA]
   congr 1
   exact (prod_top f e h e.support).2
 · rw [Kh hEq,zk,vi]
   exact (prod_top f e h e.support).1.trans_lt (lt_of_le_of_ne hle hEq)
theorem buL (P:lJ ι ℚ) (u v :ι→ℕ) {d:ℕ} (hd:P.totalDegree≤d) :
   (BZ P u v).coeff d=oy (fun i=>(v i:ℚ)) (C4 d P) := by
 unfold BZ
 rw [dsJ _ (fun i => ?_) P d hd]
 · simp [Ef]
 · apply (Polynomial.natDegree_add_le _ _).trans
   exact max_le (by simpa using Polynomial.natDegree_C_mul_X_pow_le (v i:ℚ) 1) (by simp)
theorem bO7 (P:lJ ι ℚ) (u:ι→ℕ) (d:ℕ)
   (h : ∀ v :ι→ℕ,(∀ i,0<v i)→(BZ P u v).natDegree≤d) :
   P.totalDegree≤d:= by
 classical
 by_contra! hd
 let f (n:ℕ) :ℚ:=((n+1 :ℕ) :ℚ)
 have hf :qx f := by
   intro m n hmn
   change ((m+1 :ℕ) :ℚ)=((n+1 :ℕ) :ℚ) at hmn
   have hmn' : m+1=n+1 := by exact_mod_cast hmn
   omega
 have hvanish:C4 P.totalDegree P=0:= by
   apply Qx (fun _=>v9 f)
     (fun _=>SC hf)
   intro x hx
   choose w hw using fun i:ι=>hx i (Set.mem_univ i)
   let v :ι→ℕ:= fun i=>w i+1
   have hv : (fun i=>(v i:ℚ))=x := _root_.funext hw
   rw [← hv,← buL P u v yL,qm]
   exact zk ((h v (fun i=>Nat.succ_pos (w i))).trans_lt hd)
 have hlt:P.totalDegree<P.totalDegree := by
   change P.support.sup (fun e=>e.degree)<P.totalDegree
   refine (Finset.sup_lt_iff (Nat.zero_lt_of_lt hd)).2 fun e he' => ?_
   have hz :=ox (fun Q:lJ ι ℚ=>Q.coeff e) hvanish
   by_contra! heq
   have hEq:e.degree=P.totalDegree :=vl (F9 he') heq
   rw [coeff_homogeneousComponent,z7 hEq,AddMonoidAlgebra.coeff_zero,Te] at hz
   exact MvPolynomial.mem_support_iff.mp he' hz
 exact (lt_irrefl _ hlt)
end
end ap8
end
section
namespace bzA
noncomputable section
open aR dN Dr Kd MvPolynomial
open scoped BigOperators
private theorem dlR {α β:Type} (f :α→β) (w:β→Fin 4 →₀ ℕ)
  (e :α →₀ ℕ) :oK w (e.mapDomain f)=oK (w ∘ f) e := by
 simp only [Fa]
 exact Finsupp.sum_mapDomain_index (fun _=>zE _ _) (fun _ _ _=>add_smul ..)
private theorem diF (p:cy) (e :Kb (fun _:Unit=>p) →₀ ℕ) :
  oK (step ∘ Fd (fun _:Unit=>p)) e=fun _=>e.degree := by
 have h:step ∘ Fd (fun _:Unit=>p)=fun _ _=>(1 :ℕ) := by
  funext v i
  obtain ⟨⟨⟩,v⟩:=v
  cases i
  simp [Fd,step]
 rw [h,Fa ,Bf]
 funext i
 simp [NX ,Finset.sum_apply]
private theorem eDU (p:cy) (e :capExponents p →₀ ℕ) :
   nI aU (capExponents p) (n5 e 1) =
     n5 (oK C5 e) 1 := by
 rw [nI,aeval_monomial,zS ,Ar,Fa]
 simp only [Finsupp.prod,NX ,monomial_pow,one_pow]
 let M:=monomialOneHom aU (Fin 4)
 change (∏ i∈e.support,M (UZ (e i•i.val))) =
   M (UZ (∑ i∈e.support,e i•i.val))
 rw [ofAdd_sum,map_prod]
private theorem enO (p:cy) (n:ℕ) :
    oK (fun i:capExponents p=>i.val) '' {e | e.degree≤n} =
      Yz (fun _:Unit=>p) (fun _=>n) := by
  classical
  let tag :capExponents p→Kb (fun _:Unit=>p) := fun i=>⟨(),i⟩
  let untag :Kb (fun _:Unit=>p)→capExponents p:= fun v=>v.2
  let zeroVar :Kb (fun _:Unit=>p) :=⟨(),⟨0,by simp [capExponents]⟩⟩
  ext m
  constructor
  · rintro ⟨e,he,rfl⟩
    change e.degree≤n at he
    refine ⟨e.mapDomain tag+Finsupp.single zeroVar (n-e.degree),?_,?_⟩
    · rw [diF,pQ,SM,VO,
        Nat.add_sub_of_le he]
    · rw [pQ,dlR,KI]
      change oK (fun i:capExponents p=>i.val) e+(n-e.degree) •
        (0:Fin 4 →₀ ℕ)=oK (fun i:capExponents p=>i.val) e
      rw [smul_zero,y5]
  · rintro ⟨e,hdegree,rfl⟩
    refine ⟨e.mapDomain untag,?_,dlR untag C5 e⟩
    change (e.mapDomain untag).degree≤n
    rw [SM]
    rw [diF] at hdegree
    exact (zR hdegree ()).le
private theorem ezb (p:cy) (n:ℕ) :
   (restrictTotalDegree (capExponents p) aU n).map
     (nI aU (capExponents p)).toLinearMap =
     qJ aU (Yz (fun _:Unit=>p) (fun _=>n)) := by
 classical
 let D:Set (capExponents p →₀ ℕ) := {e | e.degree≤n}
 let A:=Yz (fun _:Unit=>p) (fun _=>n)
 let f :=(nI aU (capExponents p)).toLinearMap
 change (qJ aU D).map f=qJ aU A
 have hgens : (fun e=>f (n5 e 1)) '' D =(fun m=>n5 m (1 :aU)) '' A:= by
   rw [show A=oK C5 '' D from (enO p n).symm,
     Set.image_image]
   apply Set.image_congr'
   intro e
   change nI aU (capExponents p) (n5 e 1) =
     n5 (oK C5 e) 1
   exact eDU p e
 rw [zm aU D,zm aU A,
   Submodule.map_span,Set.image_image,hgens]
theorem proof :Kd.c4 := by
  intro J p n
  let f :=nI aU (capExponents p)
  let I:=J.comap f.toRingHom
  let g:lJ (capExponents p) aU ⧸ I →ₐ[aU] lz ⧸ J :=
    G3 J f yL
  let L:=g.toLinearMap.domRestrict (uW I n)
  have hL:qx L:= by
    intro x y hxy
    exact vH (Nr (I:=J) (f :=f.toRingHom) hxy)
  have hcomp:g.comp (uh aU I)=(uh aU J).comp f :=
    Ideal.quotient_map_comp_mkₐ J f yL
  have hmap : (restrictTotalDegree (capExponents p) aU n).map f.toLinearMap =
      qJ aU (Yz (fun _:Unit=>p) (fun _=>n)) :=
    ezb p n
  have hrange :LinearMap.range L =
      (qJ aU (Yz (fun _:Unit=>p) (fun _=>n))).map
        (uh aU J).toLinearMap:= by
    dsimp only [L]
    rw [LinearMap.range_domRestrict,uW,← Oc,
      ← PD,hcomp,PD,Oc,hmap]
  change pz aU (uW I n)= _
  rw [← LinearMap.finrank_range_of_inj hL,hrange,Sn]
end
end bzA
end
section
namespace ap8
noncomputable section
open aR dN Dr Kd MvPolynomial Filter
open scoped BigOperators
variable {ι:Type} [pL ι]
theorem aES (fF:ι→cy) (a b:ι→ℕ) :
  ku fF (a+b)=(ku fF a).plus (ku fF b) := by
 simp [ku,qM,Pi.add_apply,add_mul,sH]
theorem aQe [oq ι] (fF:ι→cy) (i:ι) :
  ku fF (step i)=fF i:= by
 simp [ku,step,Kv,ite_mul]
private theorem cpi (fF:ι→cy) (n:ℕ) (v :ι→ℕ) :
  ku fF (fun i=>n*v i)=(ku fF v).scale n:= by
 simp [ku,t3 ,v8 ,uz]
private theorem awr (fF:ι→cy) (hs : ∀ i,ChamberBox (fF i))
    (v :ι→ℕ) (base :ι) (hv :0<v base) :ChamberBox (ku fF v) := by
  refine ⟨t6 (fun i _=>oz _ (hs i).1),?_,?_⟩
  · change 3*(∑ i,v i*(fF i).t) ≤ ∑ i,v i*(fF i).j
    rw [uz]
    exact t6 fun i _=> by
      rw [xu 3]
      exact oz _ (hs i).2.1
  · exact (z9 hv (hs base).2.2).trans_le
      (Mw (f := fun i=>v i*(fF i).t)
        (fun _ _=>EP _) (u9 base))
private theorem aCx (p:cy) (hp:ChamberBox p) :
  sI (nI aU (capExponents p)) := by
 apply x7
 intro i
 have ⟨hb,hj,ht⟩:=hp
 fin_cases i <;>
  norm_num [aiK.OW,vj] <;> omega
private theorem aXZ (J:c9 lz) {p q:cy} (h:aO p q) :
  Sn J (capExponents p)≤Sn J (capExponents q) := by
 have hsub:capExponents p⊆capExponents q:= fun _ he =>
  ⟨he.1.trans (oz _ h.1),he.2.1.trans (oz _ h.2.1),
    he.2.2.trans (oz _ h.2.2)⟩
 have :Et aU (qJ aU (capExponents q)) :=
  Module.Finite.of_basis (C9 aU _)
 exact Qy (Ye (restrictSupport_mono aU hsub))
private theorem cpk (p q:cy) (hq:ChamberBox q) :
   ∃ C:ℕ,∀ n,aO (q.scale n) (p.plus (q.scale n)) ∧
     aO (p.plus (q.scale n)) (q.scale (n+C)) := by
 let C:=p.b+p.j+p.t
 have ⟨hb,hj,ht⟩:=hq
 have bound (a b:ℕ) (ha :a≤C) (hpos :0<b) (n:ℕ) :
     a+n*b≤(n+C)*b:= by
   rw [FR,FU a]
   exact Yi (ha.trans (Vs _ hpos)) _
 refine ⟨C,fun n=>⟨⟨GY _ _,GY _ _,GY _ _⟩,
   ⟨bound p.b q.b (by dsimp [C]; omega) (by omega) n,
    bound p.j q.j (by dsimp [C]; omega) (by omega) n,
    bound p.t q.t (by dsimp [C]; omega) ht n⟩⟩⟩
theorem fT8 (fF:ι→cy) (J:c9 lz) (base :ι)
    (hs : ∀ i,ChamberBox (fF i))
    (hfil : ∀ q:cy ,ChamberBox q → ∀ n,
      p7
        (J.comap (nI aU (capExponents q)).toRingHom) n =
      Sn J (capExponents (q.scale n)))
    (P:lJ ι ℚ) (u:ι→ℕ)
    (hu : ∀ a≥u,oy (fun i=>(a i:ℚ)) P =
      (Sn J (capExponents (ku fF a)) :ℚ))
    (v :ι→ℕ) (hv :0<v base) (d:ℕ) (hd:dimension J≤d) :
    (BZ P u v).natDegree≤dimension J ∧
    (BZ P u v).coeff d=capCoeff J d (ku fF v) := by
  let q:=ku fF v
  have hq:ChamberBox q:=awr fF hs v base hv
  let I:=J.comap (nI aU (capExponents q)).toRingHom
  let Q:=oD I
  have hQ:Q.natDegree=dimension J :=
    G5 _ (aCx q hq) J
  obtain ⟨C,hC⟩:=cpk (ku fF u) q hq
  have hR (n:ℕ) : (BZ P u v).eval (n:ℚ) =
      (Sn J (capExponents ((ku fF u).plus (q.scale n))) :ℚ) := by
    rw [bgE]
    change oy (fun i=>(((u+fun j=>n*v j) i:ℕ) :ℚ)) P= _
    rw [hu (u+fun i=>n*v i) (fun i=>qy _ _),aES,cpi]
  have hshift:Tendsto (fun n:ℕ=>n+C) pG atTop :=
    tendsto_atTop_mono (fun n=>qy n C) tendsto_id
  have hlo : ∀ᶠ n:ℕ in pG,Q.eval (n:ℚ)≤(BZ P u v).eval (n:ℚ) := by
    filter_upwards [z8 I] with n hn
    rw [show Q.eval (n:ℚ)=(p7 I n:ℚ) from hn,hfil q hq n,hR]
    exact_mod_cast aXZ J (hC n).1
  have hhi : ∀ᶠ n:ℕ in pG,
      (BZ P u v).eval (n:ℚ)≤(Gj (C:ℚ) Q).eval (n:ℚ) := by
    filter_upwards [hshift.eventually (z8 I)] with n hn
    rw [Polynomial.taylor_eval,← zc,show Q.eval ((n+C:ℕ) :ℚ) =
      (p7 I (n+C) :ℚ) from hn,hfil q hq (n+C),hR]
    exact_mod_cast aXZ J (hC n).2
  have hT: (Gj (C:ℚ) Q).natDegree=dimension J :=
    (Polynomial.natDegree_taylor Q _).trans hQ
  have hdeg: (BZ P u v).natDegree≤dimension J :=
    (Polynomial.natDegree_le_of_eventually_eval_natCast_le
      (Eventually.of_forall fun n=> by rw [hR]; positivity) hhi).1.trans_eq hT
  have hl:=JW
    (hQ.trans_le hd) (hdeg.trans hd) hlo
  have hh:=JW
    (hdeg.trans hd) (hT.trans_le hd) hhi
  rw [UY _ (hQ.trans_le hd)] at hh
  exact ⟨hdeg,vl hh hl⟩
end
end ap8
end
section
namespace Jq
noncomputable section
open dN vS B8 MvPolynomial
theorem cMw {p q:Form} {N :ℕ}
    (h : ∀ t:jJ,(∀ j,N≤t j) →
        eval (fun j=>(t j:ℚ)) p=eval (fun j=>(t j:ℚ)) q) :p=q:= by
  let s :Fin 5→Set ℚ:= fun _=>v9 fun n:ℕ=>((N+n:ℕ) :ℚ)
  refine Qx s (fun _=>SC ?_) ?_
  · intro a b hab
    exact Nat.add_left_cancel (Nat.cast_injective hab)
  · intro x hx
    choose n hn using fun j=>hx j (Set.mem_univ j)
    let t:jJ:=Finsupp.equivFunOnFinite.symm fun j=>N+n j
    have hx' : (fun j=>(t j:ℚ))=x :=funext hn
    rw [← hx']
    exact h t (fun j=>qy N (n j))
theorem bOn (I:mD (Fin 5)) (i:Fin 5) :
  squarefree I i=if i∈I then 1 else 0:= by
 classical
 simp [squarefree,zY,Finsupp.finsetSum_apply,vj,eq_comm]
theorem aJC (I:mD (Fin 5)) : (squarefree I).degree=I.card:= by
 classical
 simp [t4 ,bOn]
theorem guw {I:mD (Fin 5)} {i:Fin 5} (hi:i∉I) :
  squarefree (vh i I)=squarefree I+zY i:= by
 simp [squarefree,Pf hi,FU]
theorem a5u (p:Form) (t:jJ) (N :ℕ) :
  (line t p).eval (N :ℚ)=eval (fun j=>((N•t) j:ℚ)) p:= by
 let L:=(Polynomial.evalRingHom (N :ℚ)).comp (line t)
 let R:=eval (fun j=>((N•t) j:ℚ))
 have h:L=R:= by
  ext j
  · simp [L,R,line]
  · simp [L,R,line,Finsupp.smul_apply,Du,u5]
 exact Au h p
theorem brY (B:lS) (P:c9 g9) {p:Form}
   (hp:Represents p (fun t=>KQ (slot B) (x8 B P) t))
   (t:jJ) (ht : ∀ j,0<t j)
   (hdiag : ∀ N,KQ (slot B) (x8 B P) (N•t) =
     p7 (RM B P t) N) :
   line t p=oD (RM B P t) := by
 obtain ⟨N₀,hN₀⟩:=hp
 refine WK (N₀:=N₀) fun N hN => ?_
 rw [a5u,hN₀ _ (fun j=>hN.trans (Vs N (ht j)))]
 exact ox (fun n:ℕ=>(n:ℚ)) (hdiag N)
theorem ewV (t a :jJ) (r :ℚ) :
   line t (n5 a r) =
     oZ (eval (fun j=>(t j:ℚ)) (n5 a r))*p9 ^a.degree := by
 simp only [line,eval₂Hom_monomial,KA,Finsupp.prod,mul_pow,
   Finset.prod_mul_distrib,← map_pow,← map_prod,Finset.prod_pow_eq_pow_sum,
   Bf]
 rw [← v8 ,← nX]
theorem ZP (p:Form) (t:jJ) (d:ℕ) :
   (line t p).coeff d=eval (fun j=>(t j:ℚ)) (C4 d p) := by
 induction p using Kl with
 | monomial a r =>
   rw [ewV,Un]
   by_cases h:a.degree=d
   · subst d
     simp [homogeneousComponent_eq_self (IU r rfl)]
   · simp [Ne.symm h,homogeneousComponent_of_mem (IU r rfl)]
 | add p q hp hq=>simp [map_add,Polynomial.coeff_add,hp,hq]
theorem a9f {p:Form} {d:ℕ}
  (h : ∀ t:jJ,(∀ j,0<t j)→(line t p).natDegree≤d) :
  p.totalDegree≤d:= by
 refine Finset.sup_le fun a ha => ?_
 by_contra! hda
 have hh:C4 a.degree p=0:= by
  refine cMw (N :=1) fun t ht => ?_
  rw [qm,← ZP]
  exact zk ((h t ht).trans_lt hda)
 have hcoeff :=ox (fun q:Form=>q.coeff a) hh
 simp [coeff_homogeneousComponent,Bf] at hcoeff
 exact (mem_support_iff.mp ha) hcoeff
theorem bgh (J:mD (Fin 5)) (j:Fin 5) :
 aoL J j=if j∈J then 2 else 1 :=rfl
private theorem dRM (I:mD (Fin 5)) (f :Fin 5→ℚ) :
   (∑ J∈I.powerset,(-1 :ℚ)^(I.card-J.card) * ∏ j∈J,f j) =
     ∏ j∈I,(f j - 1) := by
 classical
 rw [Finset.prod_sub f (fun _=>(1 :ℚ))]
 refine Finset.sum_bij (fun J _=>I \ J) ?_ ?_ ?_ ?_
 · intro J hJ
   exact Finset.mem_powerset.mpr Wm
 · intro J hJ K hK h
   simpa [Gi (Finset.mem_powerset.mp hJ),
     Gi (Finset.mem_powerset.mp hK)] using
     ox (fun U=>I \ U) h
 · intro J hJ
   exact ⟨I \ J,Finset.mem_powerset.mpr Wm,
     Gi (Finset.mem_powerset.mp hJ)⟩
 · intro J hJ
   simp [Gi (Finset.mem_powerset.mp hJ),
     Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hJ)]
private theorem dRK (I:mD (Fin 5)) (a :jJ) (r :ℚ) :
   (∑ J∈I.powerset,(-1 :ℚ)^(I.card-J.card) *
     eval (fun j=>(aoL J j:ℚ)) (n5 a r)) =
     r * ∏ j∈I,((2 :ℚ)^a j - 1) := by
 rw [← dRM,uz]
 refine p5 rfl fun J _ => ?_
 rw [KA,Finsupp.prod_pow]
 have he (j:Fin 5) : ((aoL J j:ℕ) :ℚ)^a j =
     if j∈J then (2 :ℚ)^a j else 1 := by
   by_cases h:j∈J <;> simp [bgh,h]
 simp_rw [he]
 rw [Finset.prod_ite_mem,Finset.univ_inter]
 ring
private theorem dRL (I:mD (Fin 5)) {a :jJ} (ha :a.degree=I.card)
   (r :ℚ) :
   (∑ J∈I.powerset,(-1 :ℚ)^(I.card-J.card) *
     eval (fun j=>(aoL J j:ℚ)) (n5 a r)) =
     (n5 a r).coeff (squarefree I) := by
 classical
 rw [dRK]
 by_cases h:squarefree I≤a
 · have he :squarefree I=a := by
     obtain ⟨b,hab⟩:=le_iff_exists_add.mp h
     have hd:=ox Finsupp.degree hab
     rw [ha,pQ,aJC] at hd
     have hb:b.degree=0:= by omega
     rw [hab,(Finsupp.degree_eq_zero_iff _).mp hb,y5]
   subst a
   rw [show (∏ j∈I,((2 :ℚ)^squarefree I j - 1))=1 from
     Finset.prod_eq_one (fun j hj=> by norm_num [bOn,hj])]
   simp
 · obtain ⟨j,hj⟩:=not_forall.mp h
   have hm:j∈I∧a j=0:= by
     by_cases hi:j∈I <;> simp [bOn,hi] at hj ⊢
     exact hj
   rw [Finset.prod_eq_zero hm.1 (by simp [hm.2]),vi ,G4]
   exact (Kh (fun he=>h he.ge)).symm
theorem bn8 (I:mD (Fin 5)) (p:Form) :
   (∑ J∈I.powerset,(-1 :ℚ)^(I.card-J.card) *
     (line (aoL J) p).coeff I.card)=p.coeff (squarefree I) := by
 classical
 induction p using Kl with
 | monomial a r =>
   simp_rw [ZP,homogeneousComponent_of_mem (IU r rfl)]
   by_cases h:I.card=a.degree
   · simpa only [z7 h] using dRL I h.symm r
   · have hne :a≠squarefree I:= fun h' => h (by rw [h',aJC])
     simp [h,G4 ,hne]
 | add p q hp hq =>
   simp [pQ,Ef ,wY ,sH,hp,hq]
end
end Jq
end
section
namespace bjA
noncomputable section
open aR dN vS Dr Kd MvPolynomial
def aWM {ι:Type} (fF:ι→cy) :
    lJ (Kb fF) aU →ₐ[aU] lJ ι GeoJets :=
  t5 fun v=>n5 (qz v.1 1) (n5 v.2.val 1)
theorem bsw {ι:Type} (fF:ι→cy) (J:c9 lz)
   (f :lJ (Kb fF) aU) :
   f∈HW fF J ↔ ∀ e,(aWM fF f).coeff e∈J:= by
 have hmap :capMap fF J=(mapAlgHom (uh aU J)).comp
     (aWM fF) := by
   apply algHom_ext
   intro v
   simp only [capMap,aWM,Vz ,aeval_X,mapAlgHom_apply,map_monomial]
   rfl
 change capMap fF J f=0↔_
 rw [hmap,Vz ,mapAlgHom_apply]
 constructor
 · intro h e
   have he :=ox (fun q:lJ ι (lz ⧸ J)=>q.coeff e) h
   rw [coeff_map] at he
   exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using he)
 · intro h
   ext e
   rw [coeff_map]
   simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (h e)
theorem dAn {p:cy} {D:lz} (hD:VE p D) :
  ∀ e∈D.support,e∈capExponents p:= by
 intro e he
 obtain ⟨hb,hj,ht⟩:=hD e he
 simp only [id_eq] at hb hj ht
 change e.degree≤2*p.b∧_∧_
 rw [t4]
 exact ⟨by omega,by omega,by omega⟩
theorem dAl {p:cy} {D:lz} (hD:VE p D) :
  ∀ e∈(D^2).support,e∈capExponents p:= by
 intro e he
 rw [MvPolynomial.mem_support_iff,ze,coeff_mul] at he
 obtain ⟨⟨u,v⟩,huv,hc⟩:=Finset.exists_ne_zero_of_sum_ne_zero he
 have hu:D.coeff u≠0:= fun h=>hc (by simp [h])
 have hv :D.coeff v≠0:= fun h=>hc (by simp [h])
 obtain ⟨hub,huj,hut⟩:=hD u (MvPolynomial.mem_support_iff.mpr hu)
 obtain ⟨hvb,hvj,hvt⟩:=hD v (MvPolynomial.mem_support_iff.mpr hv)
 rw [Finset.HasAntidiagonal.mem_antidiagonal] at huv
 rw [← huv]
 simp only [capExponents,G1 ,t4 ,KH,
  wY ,sH]
 simp only [id_eq] at hub huj hut hvb hvj hvt
 exact ⟨by omega,by omega,by omega⟩
theorem exists_lift {ι:Type} [oq ι] (fF:ι→cy) (i:ι)
   (D:lz) (hD : ∀ e∈D.support,e∈capExponents (fF i)) :
   ∃ L:lJ (Kb fF) aU,
     IsWeightedHomogeneous (step ∘ Fd fF) L (step i) ∧
     aWM fF L=n5 (qz i 1) D:= by
 classical
 let v (e : ↥D.support) :Kb fF:=⟨i,⟨e,hD e e.2⟩⟩
 let L:lJ (Kb fF) GeoField :=
   ∑ e∈D.support.attach,D.coeff e•lI (v e)
 refine ⟨L,?_,?_⟩
 · change L∈Ee aU (step ∘ Fd fF) (step i)
   exact Ww _ fun e _ =>
     Submodule.smul_mem _ _ (G0 aU (step ∘ Fd fF) (v e))
 · simp only [L,t8 ,map_smul,aWM,aeval_X,v,smul_monomial,yQ,sS]
   rw [← t8 (n5 (qz i 1))]
   congr 1
   rw [Finset.sum_attach D.support (fun e=>n5 e (D.coeff e))]
   exact D.as_sum.symm
theorem cDY {ι:Type} (fF:ι→cy) {J K:c9 lz}
  (h:J≤K) :HW fF J≤HW fF K:= by
 intro f hf
 exact (bsw fF K f).mpr fun e=>h ((bsw fF J f).mp hf e)
theorem brQ {ι:Type} {fF:ι→cy} {i:ι} {D:lz}
   {J:c9 lz} {L:lJ (Kb fF) aU}
   (hL:aWM fF L=n5 (qz i 1) D)
   (hD:D∈J) :L∈HW fF J:= by
 classical
 rw [bsw,hL]
 intro e
 rw [G4]
 split_ifs
 · exact hD
 · exact J.zero_mem
theorem cXP {ι:Type} {fF:ι→cy} {i:ι} {D:lz}
   {J K:c9 lz} {L:lJ (Kb fF) aU}
   (hL:aWM fF L=n5 (qz i 1) D)
   (hD : ∀ x,D *x∈J↔x∈K) (f :lJ (Kb fF) aU) :
   L*f∈HW fF J↔f∈HW fF K:= by
 classical
 rw [bsw,bsw,nX ,hL]
 constructor
 · intro h e
   apply (hD _).mp
   rw [← coeff_monomial_mul e (qz i 1) D (aWM fF f)]
   exact h _
 · intro h e
   rw [coeff_monomial_mul']
   split_ifs
   · exact (hD _).mpr (h _)
   · exact J.zero_mem
private theorem ez1 (J:c9 lz) (D x :lz) :
   x∈cut J D ↔ ∃ r :lz ⧸ J,lV J x=lV J D *r := by
 rw [show cut J D =oY {D} ⊔ J from sup_comm _ _,Ideal.mem_span_singleton_sup]
 constructor
 · rintro ⟨r,b,hb,rfl⟩
   exact ⟨lV J r,by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hb,u5]⟩
 · rintro ⟨r,hr⟩
   obtain ⟨a,rfl⟩:=Nq r
   refine ⟨a,x-a*D,Ideal.Quotient.eq.mp ?_,by abel⟩
   rw [nX ,u5]
   exact hr
theorem gur (J:c9 lz) (D:lz)
  (hD:p6 (lV J D)) (x :lz) :
  D^2*x∈J↔x∈J:= by
 simp only [← wA,nX ,ze]
 exact (hD.mul hD).mul_left_eq_zero_iff
theorem dS7 (J:c9 lz) (D:lz)
  (hD:p6 (lV J D)) (x :lz) :
  D *x∈cut J (D^2)↔x∈cut J D:= by
 simp only [ez1,nX ,ze,v8]
 exact exists_congr fun _=>Function.Injective.eq_iff hD
end
end bjA
end
section
namespace aRT
noncomputable section
open aR dN vS B8
private theorem four_ne_zero : (4 :aU)≠0:= by
 let e :=(j8.comp oZ).comp aR.embed
 let:CharP aU K1.p:=MK e.injective K1.p
 intro hz
 have hd:=(LQ aU K1.p 4).mp (by simpa using hz)
 exact (GR (show 4<K1.p by decide)) (Nat.le_of_dvd (by decide) hd)
private def aQB (x :lz) :g9 →+* GeoJets :=
 zh ov (yU x lI)
private theorem cqK (x :lz) :
   (aQB x).comp qK=Ob GeoJets := by
 apply xm
 · intro a
   simp [aQB,qK]
 · intro i
   simp [aQB,qK]
end
end aRT
end
section
namespace agM
noncomputable section
open aR dN vS B8 MvPolynomial
open scoped BigOperators Pointwise
def c1 :Prop :=
  ∀ (B:lS),(∀ i,bF (B i).1) → ∀ (t:Fin 5→ℕ) (n:ℕ),
    n•H7 B t=Nl (agj (Vw B t) n)
def c2 :Prop :=
  ∀ p:cy ,bF p →
    ∃ H :wB ℚ,H.natDegree≤4 ∧
      H.coeff 4=(Dn p:ℚ)/2 ∧
      ∀ n:ℕ,H.eval (n:ℚ)=(Dr.capExponents (p.scale n)).ncard
private theorem bEc (h1 :c1) (h2 :c2)
   (B:lS) (hB : ∀ i,bF (B i).1) (t:Fin 5→ℕ) :
   (oD (zg (nI aU (H7 B t))
     ⊥)).coeff 5=aYe (Vw B t) := by
 let a :=Vw B t
 obtain ⟨H,hdeg,hcoeff,hH⟩:=h2 a.1 (bOu B hB t)
 let F:=H*(oZ (2*(a.2 :ℚ))*p9+1)
 have heq :F=oD
     (zg (nI aU (H7 B t)) ⊥) := by
   apply WK (N₀:=0)
   intro n _
   rw [bJv _ (gNk B t),h1 B hB t n,
     euK]
   simp only [F,agj,a,TI,XJ,Re,
     PM,Polynomial.eval_one,hH,Du,zc,Dw ,
     Nat.cast_ofNat]
   ring
 rw [← heq]
 have h5:=zk (p:=H) (n:=5) (by omega)
 simp only [F,wY ,sS ,Ef ,← v8 ,Polynomial.coeff_mul_X,
   Polynomial.coeff_mul_C,h5,y5 ,hcoeff,aYe,a]
 ring
end
end agM
end
section
namespace Jq
noncomputable section
open dN vS B8 MvPolynomial
theorem aNi (B:lS) (P:c9 g9) (t:jJ) {d:ℕ}
  (hd:MH P d) : (oD (RM B P t)).natDegree≤d:= by
 let f :=nI aU (H7 B t)
 let φ:=G3 P f yL
 exact (natDegree_affineHilbertPolynomial_le_of_injective φ Nr).trans
  (axg.beu hd)
theorem a4y (B:lS) (P:c9 g9) {d:ℕ} (hd:MH P d)
    {p:Form} (hp:Represents p (fun t=>KQ (slot B) (x8 B P) t))
    (hdiag : ∀ t:jJ,(∀ j,0<t j) → ∀ N,
      KQ (slot B) (x8 B P) (N•t) =
        p7 (RM B P t) N) :
    p.totalDegree≤d:= by
  apply a9f
  intro t ht
  rw [brY B P hp t ht (hdiag t ht)]
  exact aNi B P t hd
theorem c0q (B:lS) (P:c9 g9) (I:mD (Fin 5)) {p:Form}
    (hp:Represents p (fun t=>KQ (slot B) (x8 B P) t))
    (hdiag : ∀ t:jJ,(∀ j,0<t j) → ∀ N,
      KQ (slot B) (x8 B P) (N•t) =
        p7 (RM B P t) N) :
    tW B P I=p.coeff (squarefree I)/(2 :ℚ)^I.card:= by
  unfold tW
  rw [← bn8 I p]
  congr 1
  refine p5 rfl fun J _ => ?_
  have ht (j:Fin 5) :0<aoL J j:= by
    rw [bgh]
    split <;> decide
  have he :=brY B P hp (aoL J) ht
    (hdiag (aoL J) ht)
  rw [he]
  rfl
end
end Jq
end
section
namespace agL
noncomputable section
open aR
open scoped BigOperators
def EY {n:ℕ} (a :Fin n →₀ ℕ) :ℕ :=
 a.sum (fun _ k=>k)
def BV {n:ℕ} {A:Type*} [CommSemiring A]
    (a :Fin n →₀ ℕ) (P:lJ (Fin n) A) :lJ (Fin n) A :=
  ∑ m∈P.support,n5 (m-a) (P.coeff m * ∏ i:Fin n,((m i).choose (a i) :A))
def afc {R:Type*} [vw R] (p:c9 R) [p.IsPrime] (f :R) (d:ℕ) :Prop :=
 let L:=GF p
 nq R L f∈Xg L^d
end
end agL
end
