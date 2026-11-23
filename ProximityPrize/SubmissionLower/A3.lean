import ProximityPrize.SubmissionLower.J
import ProximityPrize.SubmissionLower.K
import ProximityPrize.SubmissionLower.B
import ProximityPrize.SubmissionLower.A0
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
open _root_ renaming Algebra→t6,Algebra.IsAlgebraic→G1,Algebra.IsIntegral→XB,Algebra.algebraMap→cy,Algebra.algebraMapSubmonoid→Xp,Algebra.trdeg→pL,CharP.cast_eq_zero_iff→Ok,CommRing→ ox,CommSemiring→vZ,DFunLike.congr_fun→G4,DecidableEq→Nq,Disjoint→Ea,Field→sH,Fin.addCases_left→PD,Fin.addCases_right→JQ,Fin.castLE→Nj,Fin.ext→yU,Fin.last→qx,Fin.sum_univ_three→LO,Finset→ oz,Finset.card_image_of_injective→Yo,Finset.exists_mem_eq_sup→Wl,Finset.mem_coe→qy,Finset.mem_filter→zm,Finset.mem_product→FV,Finset.mem_univ→zS,Finset.mul_sum→Dz,Finset.sum_add_distrib→wR,Finset.sum_comm→N0,Finset.sum_congr→t4,Finset.sum_eq_single→Qw,Finset.sum_eq_zero→Pf,Finset.sum_erase_add→zvm,Finset.sum_le_sum→yo,Finset.sum_le_sum_of_subset_of_nonneg→Z0,Finset.sum_mul→Qx,Finset.sum_nonneg→ZK,Finset.sup_le→yL,Finsupp.add_apply→NI,Finsupp.degree_eq_sum→Up,Finsupp.single_eq_same→Mw,Finsupp.sumFinsuppAddEquivProdFinsupp→Kv,Finsupp.weight→Du,Finsupp.weight_apply→LQ,Finsupp.weight_eq_sum→ IU,Fintype.card_fin→PA
open _root_ renaming Function.Injective→qm,Function.Surjective→zpX,Function.comp_apply→SU,GK.Slice→p5,Ideal→lI,Ideal.Quotient.commRing→ IT,Ideal.Quotient.eq_zero_iff_mem→SL,Ideal.Quotient.factor→Ww,Ideal.Quotient.mk→n5,Ideal.Quotient.mk_algebraMap→Wm,Ideal.Quotient.mk_surjective→uW,Ideal.Quotient.mkₐ→Sd,Ideal.Quotient.mkₐ_eq_mk→Vs,Ideal.annihilator_quotient→Df,Ideal.comap_map_mk→Kl,Ideal.height_add_one_le_of_lt_of_isPrime→Nr,Ideal.isPrime_map_quotientMk_of_isPrime→ztf,Ideal.map_span→yQ,Ideal.mem_map_of_mem→Et,Ideal.mem_span_singleton→G9,Ideal.mem_span_singleton_self→xL,Ideal.mem_span_singleton_sup→Zt,Ideal.mem_sup_left→Vq,Ideal.mem_sup_right→C9,Ideal.mk_ker→Qy,Ideal.mul_mem_left→KA,Ideal.pow_mem_pow→SM,Ideal.quotientMap→JK,Ideal.quotientMap_injective→zmq,Ideal.quotientMapₐ→zwL,Ideal.quotient_map_mkₐ→Zi,Ideal.span→c9,Ideal.span_insert→Zg,Ideal.subset_span→t9,IntermediateField.adjoin→G7,Irreducible→JW,IsAlgebraic→Hw,IsDomain→vH,IsFractionRing.injective→ze,IsLocalRing.ResidueField→Zh,IsLocalRing.maximalIdeal→RP,IsLocalRing.residue→Ze,IsLocalization→MS,IsLocalization.AtPrime.map_eq_maximalIdeal→VH,IsLocalization.algebraMap_mem_map_algebraMap_iff→XJ,IsLocalization.injective→Ml,IsLocalization.isAlgebraic→Sv,IsLocalization.isPrime_of_isPrime_disjoint→QL
open _root_ renaming IsLocalization.lift→zvq,IsLocalization.lift_eq→XG,IsLocalization.map_units→ II,IsLocalization.minimalPrimes_map→VC,IsLocalization.mk'_mem_map_algebraMap_iff→VS,IsLocalization.mul_mk'_eq_mk'_of_mul→WY,IsLocalization.surj→Zf,IsLocalization.under_map_of_isPrime_disjoint→G6,IsSMulRegular→vi,IsScalarTower.algebraMap_apply→zi,K1_13_7_4.br7→Re,K1_13_7_4.pointPrime→Yc,K1_13_7_6.zeroPrime→ oY,LinearMap.ker→EK,LinearMap.mem_ker→Y4,Localization.AtPrime→p9,LocalizedModule.map→UP,LocalizedModule.map_injective→ZJ,LocalizedModule.map_surjective→S2,LocalizedModule.mkLinearMap→Yi,Module.Finite→v8,Module.annihilator→FU,Module.coe_length→Ts,Module.finrank→R9,Module.length_eq_of_surjective→TZ,MulEquiv.irreducible_iff→UY,MvPolynomial→nX,MvPolynomial.C→mD,MvPolynomial.C_dvd_iff_dvd_coeff→Gi,MvPolynomial.C_injective→X8,MvPolynomial.C_mul→S1,MvPolynomial.IsWeightedHomogeneous→Ar,MvPolynomial.X→lz,MvPolynomial.aeval→pz,MvPolynomial.algebraMap_def→zu8,MvPolynomial.algebraMap_eq→zk,MvPolynomial.coeff_C_mul→ In,MvPolynomial.coeff_map→F9,MvPolynomial.coeff_monomial→ Iw,MvPolynomial.coeff_mul→GF,MvPolynomial.coeff_pderiv→Ye,MvPolynomial.coeff_sum→RC,MvPolynomial.coeff_weightedHomogeneousComponent→Vl,MvPolynomial.degreeOf_X_pow_of_ne→PM,MvPolynomial.degreeOf_add_le→G2,MvPolynomial.degreeOf_eq_sup→Gk,MvPolynomial.degreeOf_mul_le→GB,MvPolynomial.degreeOf_rename_of_injective→Xo
open _root_ renaming MvPolynomial.eval→Pc,MvPolynomial.eval₂Hom→vl,MvPolynomial.eval₂Hom_C→z7,MvPolynomial.eval₂Hom_X'→y5,MvPolynomial.ext→LP,MvPolynomial.finSuccEquiv→Fa,MvPolynomial.finSuccEquiv_apply→zyf,MvPolynomial.induction_on→JM,MvPolynomial.induction_on'→VO,MvPolynomial.le_degreeOf_of_mem_support→NZ,MvPolynomial.le_weightedTotalDegree→zh,MvPolynomial.map→p7,MvPolynomial.map_C→C5,MvPolynomial.map_rename→zoD,MvPolynomial.mem_support_iff→Dv,MvPolynomial.monomial→xu,MvPolynomial.pderiv→ oD,MvPolynomial.pderiv_mul→LR,MvPolynomial.rename→ oy,MvPolynomial.renameEquiv→Mj,MvPolynomial.rename_C→zt1,MvPolynomial.ringHom_ext→pU,MvPolynomial.trdeg_of_isDomain→Xx,MvPolynomial.weightedHomogeneousComponent→yJ,MvPolynomial.weightedHomogeneousSubmodule→Kc,MvPolynomial.weightedTotalDegree→Gj,Nat.add_zero→OJ,Nat.cast_add→zg,Nat.cast_succ→G0,Nat.eq_zero_of_le_zero→uz,Nat.le_of_dvd→NY,Nat.lt_succ_of_le→Kz,Nat.lt_succ_of_lt→Lf,Nat.lt_succ_self→NX,Nat.mul_add→Dw,Nat.mul_le_mul_left→KH,Nat.pos_of_ne_zero→WD,Nat.sub_add_cancel→HZ,Nat.zero_add→Pj,Nontrivial→xI,Or.inl→v9,Polynomial→lJ,Polynomial.Bivariate.swap→zd,Polynomial.C→lV,Polynomial.X→nq,Polynomial.coe_eval₂RingHom→SW,Polynomial.coe_mapRingHom→xW,Polynomial.coeff_C_mul→Av
open _root_ renaming Polynomial.coeff_C_mul_X→TH,Polynomial.coeff_X_mul→Xu,Polynomial.coeff_add→Kp,Polynomial.coeff_derivative→MK,Polynomial.coeff_map→vj,Polynomial.coeff_monomial→Np,Polynomial.coeff_mul_X→zwB,Polynomial.coeff_sub→zsl,Polynomial.coeff_zero→wA,Polynomial.commRing→RD,Polynomial.constantCoeff→Cy,Polynomial.evalRingHom→vh,Polynomial.eval₂RingHom→zqf,Polynomial.eval₂_C→UZ,Polynomial.finsetSum_coeff→Gr,Polynomial.hasseDeriv→qM,Polynomial.hasseDeriv_map→G8,Polynomial.hom_eval₂→Bf,Polynomial.induction_on'→FK,Polynomial.mapEquiv→MO,Polynomial.mapRingHom→t7,Polynomial.map_C→RJ,Polynomial.map_eq_zero_iff→X4,Polynomial.map_map→Rm,Polynomial.ringHom_ext→EP,Polynomial.smul_eq_C_mul→WX,Polynomial.sum→P7,Polynomial.sylvester→Pk,Polynomial.taylor→u8,Polynomial.taylorEquiv→G3,PrimeSpectrum→ oj,RingHom.comp_apply→pC,RingHom.congr_fun→ oZ,RingHom.ext→SD,RingHom.id→ Il,RingHom.ker→GY,RingHom.ker_eq_comap_bot→WK,RingHom.mem_ker→xm,Set.image_insert_eq→Kh,Set.image_singleton→zf,Set.insert_subset_iff→J4,Set.singleton_subset_iff→NW,Submodule.mem_bot→Vz,Submodule.mem_colon_singleton→ztS,Subtype.ext→wY,Sum.inl→zR,Sum.inr→C4,Sy.gQ→qU
open _root_ renaming Sy.probe→pQ,aFN.canonical→qJ,aFN.exponent→pG,aKv.minPrimes→z8,aR.Shape→t8,add_comm→vw,add_le_add→Gn,add_zero→u5,aez.denominator→FQ,charP_of_injective_ringHom→z9,congrArg→ ov,dN.GeoField→ oq,faithfulSMul_iff_algebraMap_injective→Xg,finSuccEquivLast→x7,finSuccEquivLast_last→Eg,gT.Ambient→th,inferInstance→Oc,injective_iff_map_eq_zero→Mz,ite_eq_left→wB,ite_eq_right→vk,le_antisymm→Ob,le_min_iff→Pr,le_rfl→sI,le_sup_left→yl,le_sup_right→G5,left_ne_zero_of_mul→Te,map_add→ oK,map_dvd_iff→FR,map_mul→nI,map_natCast→Mk,map_ofNat→GR,map_pow→p6,map_sub→qG,map_sum→vG,map_zero→qz,mul_assoc→sS,mul_comm→t3,mul_le_mul_of_nonneg_left→WW,mul_left_cancel₀→SC,mul_left_comm→Pv,mul_ne_zero→Fz,mul_nonneg→Ee,nonZeroDivisors→u9,not_le_of_gt→Aa,one_mul→Au,pow_succ→yB,smul_eq_mul→zc,sup_le→uJ
open _root_ renaming trdeg_add_eq→Ef,trdeg_eq_zero→KI,wH.Lower→aU,wH.localColength→t5,zP.Exponent→uh,zero_add→zE
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace aez
noncomputable section
open MvPolynomial wT
private def awk :Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
 Equiv.ofBijective ![zR 0,zR 1,C4 0,C4 1] (by decide)
variable {F:Type*} [sH F]
def al3:nX (Fin 4) F ≃+* nX (Fin 2) (nX (Fin 2) F) :=
 (Mj F awk).toRingEquiv.trans (sumRingEquiv F (Fin 2) (Fin 2))
private def aDu (e f :Fin 2 →₀ ℕ) :Fin 4 →₀ ℕ :=
 (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e,f)).mapDomain awk.symm
private theorem b6Y (e f :Fin 2 →₀ ℕ) :
  aDu e f 0=e 0∧aDu e f 1=e 1 ∧
   aDu e f 2=f 0∧aDu e f 3=f 1 := by
 simp [aDu,awk]
private theorem b5N (Q:nX (Fin 4) F) (e f :Fin 2 →₀ ℕ) :
    ((al3 Q).coeff e).coeff f= Q.coeff (aDu e f) := by
  classical
  let g:=Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e,f)
  have hg: (aDu e f).mapDomain awk=g:= by
    have he : (awk :Fin 4→Fin 2 ⊕ Fin 2) ∘ awk.symm=id :=
      funext awk.apply_symm_apply
    rw [aDu,← Finsupp.mapDomain_comp,he,Finsupp.mapDomain_id]
  rw [← coeff_rename_mapDomain awk awk.injective,hg]
  change ((sumRingEquiv F (Fin 2) (Fin 2) (oy awk Q)).coeff e).coeff f =
    (oy awk Q).coeff g
  generalize oy awk Q=P
  induction P using VO with
  | add P R hp hr=>simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hr]
  | monomial a b =>
    change ((AddMonoidAlgebra.curryRingEquiv
        (AddMonoidAlgebra.mapDomainRingEquiv F Kv
          (AddMonoidAlgebra.single a b))).coeff e).coeff f= _
    rw [AddMonoidAlgebra.mapDomainRingEquiv_single]
    generalize hpair :Kv a=pair
    rcases pair with ⟨i,j⟩
    rw [AddMonoidAlgebra.curryRingEquiv_single]
    change ((xu i (xu j b)).coeff e).coeff f=(xu a b).coeff g
    have ha :a=g↔i=e∧j=f := by
      rw [← Finsupp.sumFinsuppAddEquivProdFinsupp.injective.eq_iff,hpair,
        show Kv g=(e,f) from AddEquiv.apply_symm_apply _ _,Prod.mk.injEq]
    by_cases hi:i=e <;> by_cases hj:j=f <;> simp [Iw ,ha,hi,hj]
private theorem b5L (Q:nX (Fin 4) F) (P:lJ F) (s t:F) :
   pz ![nq,P] ((al3 Q).map (eval ![s,t])) =
     pz (D9 P s t) Q:= by
 let lhs :=(pz ![nq,P]).toRingHom.comp
   ((map (eval ![s,t])).comp (al3 (F:=F)).toRingHom)
 have heq :lhs=(pz (D9 P s t)).toRingHom:= by
   apply pU
   · intro a
     simp [lhs,al3]
   · intro i
     fin_cases i <;> simp [lhs,al3,awk,D9]
 exact oZ heq Q
end
end aez
end
section
set_option backward.isDefEq.respectTransparency false
namespace aez
noncomputable section
open K1 BN wT MvPolynomial
def c1 :Prop :=
  ∀ u deleted h U V (W:lK u deleted h U V),
    ∀ j,(aEc U V W.output).weightedTotalDegree (vO 131071 j) =
      GA h j
def c2 :Prop :=
  ∀ u deleted h U V (W:lK u deleted h U V),∀ i∉deleted,
    (RK oH (ddP u i (aEc U V W.output))).natTrailingDegree=1
def c3:Prop :=
  ∀ u deleted h U V (W:lK u deleted h U V),
    (lV (FQ V)*nq-Polynomial.C (numerator U W.output)).IsPrimitive
end
end aez
end
section
set_option backward.isDefEq.respectTransparency false
namespace cxH
noncomputable section
open K1 BN aez wT Qo MvPolynomial
private abbrev aBY:=nX (Fin 5) K
private def iy :lJ K →+* aBY :=
 zqf C (lz 0)
private def azP (A:Fin 2→lJ K) (z :aBY) :aBY :=
 iy (A 0)+z*iy (A 1)
private def btF (O:Fin 2→Fin 2→lJ K) :aBY :=
 azP (fun j=>O j 0) (lz 3) +
  lz 4*azP (fun j=>O j 1) (lz 3)
private theorem gLe (Q:lJ K) :
  xx (iy Q)=lV (Om Q) := by
 have hh: (xx (F:=K)).toRingHom.comp iy =
    Polynomial.C.comp Om:= by
  apply EP
  · intro a
    simp [iy,Om,xx,zyf]
  · simp [iy,Om,aI3]
 exact oZ hh Q
private theorem fVT (U V:Fin 2→lJ K)
  (O:Fin 2→Fin 2→lJ K) :
  aEc U V O =
    azP U (lz 4)*lz 1 +
    azP V (lz 3)*lz 2 - btF O:= by
 apply xx.injective
 simp only [bgd,azP,btF,qG,oK,nI,
  gLe,aI3]
 change _=(lV (Om (U 0)) +
    lV (lz 3)*lV (Om (U 1)))*lV (lz 1) +
    (lV (Om (V 0)) +
    lV (lz 2)*lV (Om (V 1)))*nq -
    ((lV (Om (O 0 0)) +
    lV (lz 2)*lV (Om (O 1 0))) +
    lV (lz 3)*(lV (Om (O 0 1)) +
    lV (lz 2)*lV (Om (O 1 1))))
 simp only [FQ,numerator,qW,qG,oK,nI]
 ring
private theorem caa {P Q:aBY} (hp:yV P) (hq:yV Q) :
   yV (P+Q) := by
 constructor
 · exact uz (by simpa only [hp.1,hq.1,max_self] using G2 1 P Q)
 · exact uz (by simpa only [hp.2,hq.2,max_self] using G2 2 P Q)
private theorem cab {P Q:aBY} (hp:yV P) (hq:yV Q) :
   yV (P*Q) := by
 constructor
 · exact uz (by simpa only [hp.1,hq.1,OJ] using GB 1 P Q)
 · exact uz (by simpa only [hp.2,hq.2,OJ] using GB 2 P Q)
private theorem c2m (Q:lJ K) :yV (iy Q) := by
 induction Q using FK with
 | add P Q hp hq =>
   rw [oK]
   exact caa hp hq
 | monomial n a =>
   rw [← Polynomial.C_mul_X_pow_eq_monomial,nI,p6]
   simp only [iy,SW,UZ,Polynomial.eval₂_X]
   apply cab
   · exact ⟨degreeOf_C _ _,degreeOf_C _ _⟩
   · exact ⟨PM _ (by decide),PM _ (by decide)⟩
private theorem bJV (A:Fin 2→lJ K) {z :aBY}
  (hz :yV z) :yV (azP A z) :=
 caa (c2m _) (cab hz (c2m _))
private theorem c2n (j:Fin 5) (h1 : (1 :Fin 5)≠j) (h2 : (2 :Fin 5)≠j) :
   yV (lz j:aBY) :=
 ⟨degreeOf_X_of_ne h1,degreeOf_X_of_ne h2⟩
private theorem eE3 (x a b c d:K) (Q:lJ K) :
  aa2 x a b c d (iy Q)=C (Q.eval x) := by
 have hh: (aa2 x a b c d).toRingHom.comp iy =
    C.comp (vh x) := by
  apply EP
  · intro r
    simp [iy,aa2]
  · simp [iy,aa2,aDV]
 exact oZ hh Q
private theorem bJI (x a b c d:K) (A:Fin 2→lJ K)
  (j:Fin 5) (hj:j=3∨j=4) :
  aa2 x a b c d (azP A (lz j)) =
    C ((A 0).eval x)+MvPolynomial.X j*C ((A 1).eval x) := by
 simp only [azP,oK,nI,eE3]
 rcases hj with rfl | rfl <;> simp [aa2,aDV]
private theorem eE6 {u:e9} {deleted:oz I} {h:ℕ}
    {U V:Fin 2→lJ K} (W:lK u deleted h U V) (i:I) (hi:i∉deleted) :
    aa2 (node i) (u 0 i) (u 1 i) (u 0 i^p) (u 1 i^p)
      (azP U (lz 4)*lz 1 +
        azP V (lz 3)*lz 2 - btF W.output)=0:= by
  simp only [btF,oK,nI,qG,bJI _ _ _ _ _ _ _ (v9 rfl),
    bJI _ _ _ _ _ _ _ (Or.inr rfl)]
  simp only [aa2,aeval_X,aDV,Matrix.cons_val]
  have hnode (j l:Fin 2) :
      C ((U l).eval (node i))*C (u j i)+C ((V j).eval (node i))*C (u l i^p) =
        (C ((W.output j l).eval (node i)) :aBY) := by
    simpa only [oK,nI] using ov (C:K →+* aBY) (W.nodes i hi j l)
  linear_combination hnode 0 0+MvPolynomial.X 3*hnode 1 0+MvPolynomial.X 4*hnode 0 1 +
    (lz 3*lz 4)*hnode 1 1
private theorem cAZ (j:Fin 5) (a b:K)
  (hz :C a+MvPolynomial.X j*C b=(0:aBY)) :a=0∧b=0:= by
 have ha :a=0:= by
  simpa using ov (Pc (fun _:Fin 5=>(0:K))) hz
 have hb:b=0:= by
  simpa [ha] using ov (Pc (fun _:Fin 5=>(1 :K))) hz
 exact ⟨ha,hb⟩
private theorem eE4 {u:e9} {deleted:oz I} {h:ℕ}
   {U V:Fin 2→lJ K} (W:lK u deleted h U V) (i:I) :
   aa2 (node i) (u 0 i) (u 1 i) (u 0 i^p) (u 1 i^p)
     (azP U (lz 4))≠0 ∨
   aa2 (node i) (u 0 i) (u 1 i) (u 0 i^p) (u 1 i^p)
     (azP V (lz 3))≠0:= by
 by_contra! hz
 rw [bJI _ _ _ _ _ _ _ (Or.inr rfl),bJI _ _ _ _ _ _ _ (v9 rfl)] at hz
 have hu:=cAZ _ _ _ hz.1
 have hv :=cAZ _ _ _ hz.2
 apply Polynomial.not_isUnit_X_sub_C (node i)
 apply W.primitive
 · intro l
   apply Polynomial.dvd_iff_isRoot.mpr
   fin_cases l
   · exact hu.1
   · exact hu.2
 · intro j
   apply Polynomial.dvd_iff_isRoot.mpr
   fin_cases j
   · exact hv.1
   · exact hv.2
theorem proof :aez.c2 := by
 intro u deleted h U V W i hi
 rw [ddP,fVT]
 have hs :=c2n 3 (by decide) (by decide)
 have ht:=c2n 4 (by decide) (by decide)
 apply cYl _ _ _ _ _
   _ _ _ (bJV U ht) (bJV V hs)
   (caa (bJV _ hs) (cab ht (bJV _ hs)))
 · rw [bDh]
   simpa only [btF] using eE6 W i hi
 · simpa only [bDh] using eE4 W i
end
end cxH
end
section
namespace cxI
noncomputable section
open K1 BN aez MvPolynomial
private abbrev R:=nX (Fin 4) K
private theorem cXK (Q:lJ K) {i:Fin 4} (hi:i≠0) :
   (Om Q).degreeOf i=0:= by
 induction Q using FK with
 | monomial n a =>
   change (Polynomial.eval₂ mD (lz 0) (Polynomial.monomial n a)).degreeOf i=0
   rw [Polynomial.eval₂_monomial]
   exact uz ((GB i _ _).trans_eq (by
     rw [degreeOf_C,PM n hi,Pj]))
 | add P Q hP hQ =>
   rw [oK]
   exact uz ((G2 i _ _).trans_eq (by simp [hP,hQ]))
private theorem bKp (A:Fin 2→lJ K) {i j:Fin 4}
  (hi:i≠0) (hij:i≠j) : (qW A (lz j)).degreeOf i=0:= by
 have hm:=GB i (lz j:R) (Om (A 1))
 rw [degreeOf_X_of_ne hij,cXK _ hi,Pj] at hm
 exact uz ((G2 i _ _).trans_eq (by
  rw [cXK _ hi,uz hm,max_self]))
private theorem eval_lift (v :Fin 4→lJ K) (hv :v 0=nq)
  (Q:lJ K) :pz v (Om Q)= Q:= by
 have hh: (pz v).toRingHom.comp Om=Il (lJ K) := by
  apply EP
  · intro a
    simp [Om]
  · simp [Om,hv]
 exact oZ hh Q
private theorem b1f (d:R) (f :lJ K)
   (heval : ∀ v :Fin 4→lJ K,v 0=nq→pz v d=f)
   (A:Fin 2→lJ K) {i:Fin 4} (hi:i≠0)
   (hd:d∣qW A (lz i)) : ∀ j,f∣A j:= by
 have hval (z :lJ K) :f∣A 0+z*A 1 := by
   let v :=Function.update (wT.D9 (F:=K) 0 0 0) i z
   have hv :v 0=Polynomial.X:= by
     simp only [v,Function.update_of_ne (Ne.symm hi)]
     rfl
   have hvi:v i=z :=Function.update_self _ _ _
   have h:=(pz v).toRingHom.map_dvd hd
   change pz v d∣pz v (qW A (lz i)) at h
   simpa only [heval v hv,qW,oK,nI,aeval_X,eval_lift v hv,hvi] using h
 have h0:f∣A 0:= by simpa using hval 0
 have h1 :f∣A 1 := by simpa using dvd_sub (hval 1) h0
 intro j
 fin_cases j
 · exact h0
 · exact h1
private theorem c3V (A:Fin 2→lJ K) (hA : ∃ j,A j≠0)
  {i:Fin 4} (hi:i≠0) :qW A (lz i)≠0:= by
 intro h
 obtain ⟨j,hj⟩:=hA
 apply hj
 have hd: (0:R)∣qW A (lz i) :=zero_dvd_iff.mpr h
 exact zero_dvd_iff.mp (b1f 0 0 (by simp) A hi hd j)
private theorem b06 {d P:R} (hd:d∣P) (hP:P≠0)
  {i:Fin 4} (hi:P.degreeOf i=0) :d.degreeOf i=0:= by
 obtain ⟨q,rfl⟩:=hd
 have he : (d*q).degreeOf i=d.degreeOf i+q.degreeOf i :=
  degreeOf_mul_eq (Te hP) (right_ne_zero_of_mul hP)
 omega
private theorem cKt {d:R} {i:Fin 4}
  (h:d.degreeOf i=0) :oD i d=0 :=
 pderiv_eq_zero_of_notMem_vars (fun hi=>(mem_vars_iff_degreeOf_ne_zero.mp hi) h)
private theorem ewf (d:R) (h : ∀ i≠0,d.degreeOf i=0) :
   ∃ f :lJ K,Om f=d:= by
 let v :=wT.D9 (F:=K) 0 0 0
 refine ⟨pz v d,?_⟩
 change (Om.comp (pz v).toRingHom) d=(Il R) d
 apply hom_congr_vars
 · ext a
   simp [Om]
 · intro i hi _
   have h0:i=0:= by
     by_contra hn
     exact (mem_vars_iff_degreeOf_ne_zero.mp hi) (h i hn)
   subst i
   simp [Om,v,wT.D9]
 · rfl
theorem proof :aez.c3:= by
  intro u deleted h U V W
  apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro d hd
  have hc:=(Polynomial.C_dvd_iff_dvd_coeff d _).mp hd
  have hdV:d∣FQ V:= by
    simpa [zsl,TH] using hc 1
  have hdN :d∣numerator U W.output := by
    simpa [zsl,TH] using hc 0
  have hV:FQ V≠0:=c3V V W.V_ne (by decide)
  have hy :d.degreeOf 1=0 :=
    b06 hdV hV (bKp V (by decide) (by decide))
  have ht:d.degreeOf 3=0 :=
    b06 hdV hV (bKp V (by decide) (by decide))
  have hderiv (A:Fin 2→lJ K) (i:Fin 4) (hi: (1 :Fin 4)≠i) :
      oD 1 (qW A (lz i))=0 :=
    cKt (bKp A (by decide) hi)
  have hdU:d∣qW U (lz 3) := by
    obtain ⟨q,hq⟩:=hdN
    have he : -(qW U (lz 3))=d*oD 1 q:= by
      simpa [numerator,pderiv_mul,hderiv _ 2 (by decide),hderiv _ 3 (by decide),
        pderiv_X_of_ne (by decide : (3:Fin 4)≠1),
        cKt hy] using ov  (oD  (R:=K) (1 :Fin 4)) hq
    exact ⟨-pderiv 1 q,by rw [mul_neg,← he,neg_neg]⟩
  have hU:qW U (lz 3)≠0:=c3V U W.U_ne (by decide)
  have hs :d.degreeOf 2=0 :=
    b06 hdU hU (bKp U (by decide) (by decide))
  obtain ⟨f,hf⟩:=ewf d (by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact hy
    · exact hs
    · exact ht)
  have heval (v :Fin 4→lJ K) (hv :v 0=nq) :
      pz v d=f := by rw [← hf,eval_lift v hv]
  rw [← hf]
  exact (W.primitive f
    (b1f d f heval U (by decide) hdU)
    (b1f d f heval V (by decide) hdV)).map Om
end
end cxI
end
section
namespace aKv
noncomputable section
open wH K1_13_7_6
open scoped BigOperators
def c1 :Prop :=
  ∀ (f g h:aU) (y :Sz) (q:oj aU),
    q.asIdeal=oF y →
    q.asIdeal∈(c9 {f,g,h}).minimalPrimes →
    f≠0∧aB4 q (c9 {f,g}) h ∧
      ∀ r∈ah4 (c9 {f,g}) q,aB4 r (c9 {f}) g
def c2 :Prop :=
  ∀ (J:lI aU) (t:aU) (q:oj aU),
    q.asIdeal∈(J ⊔ c9 {t}).minimalPrimes →
    aB4 q J t →
    (t5 q (J ⊔ c9 {t})).toNat =
      ∑ p∈ah4 J q,
        (t5 p J).toNat*(t5 q (ke p t)).toNat
private theorem gtF (f g:aU) :
  c9 ({f,g} : Set aU)=c9 {f} ⊔ c9 {g} := by
 rw [← Ideal.span_union]
 congr 1
private theorem gtJ (f g h:aU) :
  c9 ({f,g,h} : Set aU)=c9 {f,g} ⊔ c9 {h} := by
 rw [← Ideal.span_union]
 congr 1
 ext t
 simp [or_left_comm,or_comm]
private theorem dSX {J:lI aU} {t:aU}
  {q p:oj aU}
  (hq:q.asIdeal∈(J ⊔ c9 {t}).minimalPrimes)
  (hreg:aB4 q J t) (hp:p∈ah4 J q) :
  t∉p.asIdeal∧q.asIdeal∈(ke p t).minimalPrimes := by
 obtain ⟨hpJ,hpq⟩:=(aID J q p).mp hp
 let A:=p9 q.asIdeal
 let a :aU →+* A:=cy aU A
 have hdisj:Ea (q.asIdeal.primeCompl:Set aU) (p.asIdeal:Set aU) :=
  Set.disjoint_left.mpr (fun _ hx hxp=>hx (hpq hxp))
 have hcomap : (p.asIdeal.map a).under aU=p.asIdeal :=
  G6 q.asIdeal.primeCompl A p.isPrime hdisj
 have hmin:p.asIdeal.map a∈(J.map a).minimalPrimes := by
  change p.asIdeal.map a∈(J.map (cy aU A)).minimalPrimes
  rw [VC q.asIdeal.primeCompl A,Set.mem_preimage,hcomap]
  exact hpJ
 change vi (A ⧸ J.map a) (a t) at hreg
 have hmin' : p.asIdeal.map a∈(FU A (A ⧸ J.map a)).minimalPrimes := by
  rwa [Df]
 refine ⟨fun ht=>(hreg.notMem_of_mem_minimalPrimes hmin') (Et a ht),?_⟩
 have htq:c9 {t} ≤ q.asIdeal:=le_sup_right.trans hq.le
 refine ⟨⟨q.isPrime,uJ hpq htq⟩,?_⟩
 intro s hs hsq
 exact hq.2 ⟨hs.1,uJ (hpJ.le.trans (le_sup_left.trans hs.2))
  (le_sup_right.trans hs.2)⟩ hsq
private theorem pointPrime_injective :qm K1_13_7_4.pointPrime := by
 intro y z hyz
 have heq :oF y=oF z :=ov PrimeSpectrum.asIdeal hyz
 funext i
 have hm:lz i-MvPolynomial.C (y i)∈oF y := by
  simp [oF,xm]
 rw [heq] at hm
 have hz :z i - y i=0:= by
  simpa [oF,xm] using hm
 exact (sub_eq_zero.mp hz).symm
private def step (p:oj aU) (t:aU) (q:oj aU) :ℚ:= by
 classical
 exact if t∉p.asIdeal∧q.asIdeal∈(ke p t).minimalPrimes
  then (t5 q (ke p t)).toNat else 0
private theorem step_nonneg (p:oj aU) (t:aU) (q:oj aU) :
  0≤ step p t q:= by
 unfold step
 split <;> positivity
private theorem step_bound (D:oj aU→ℚ) (hD : ∀ p,0≤D p)
   (p:oj aU) (t:aU)
   (hpay :t∉p.asIdeal → ∀ qs :oz (oj aU),
     (∀ q∈qs,q.asIdeal∈(ke p t).minimalPrimes) →
     (∀ q∈qs,t5 q (ke p t) < ⊤) →
     a3c D p t qs≤D p)
   (qs :oz (oj aU)) :
   ∑ q∈qs,step p t q*D q≤D p:= by
 classical
 by_cases ht:t∈p.asIdeal
 · simpa [step,ht] using hD p
 let qs' := qs.filter (fun q=>q.asIdeal∈(ke p t).minimalPrimes)
 have hmin : ∀ q∈qs',q.asIdeal∈(ke p t).minimalPrimes :=
   fun q hq=>(Finset.mem_filter.mp hq).2
 simpa [qs',a3c,Finset.sum_filter,step,ht,ite_mul] using
   hpay ht qs' hmin (fun q hq=>Re (hmin q hq))
private theorem dfv (hassoc:c2)
   {J:lI aU} {t:aU} {q:oj aU}
   (hq:q.asIdeal∈(J ⊔ c9 {t}).minimalPrimes)
   (hreg:aB4 q J t) :
   ((t5 q (J ⊔ c9 {t})).toNat :ℚ) =
     ∑ p∈ah4 J q,(t5 p J).toNat*step p t q:= by
 classical
 rw [hassoc J t q hq hreg]
 push_cast
 apply t4 rfl
 intro p hp
 simp [step,dSX hq hreg hp]
private theorem point_chain_bound (hregular :c1) (hassoc:c2)
    (f g h:aU) (y :Sz) (q:oj aU)
    (hy :q.asIdeal=oF y) (hq:q.asIdeal∈(c9 {f,g,h}).minimalPrimes) :
    ((t5 q (c9 {f,g,h})).toNat :ℚ) ≤
      ∑ r∈z8 (c9 {f,g}),
        (∑ p∈z8 (c9 {f}),step oY f p*step p g r)*step r h q:= by
  classical
  obtain ⟨hf,hreg,hregs⟩:=hregular f g h y q hy hq
  have hzero :ke oY f=c9 {f} := by simp [ke,oY]
  have hf' : f∉zeroPrime.asIdeal:= by simpa [oY ,Ideal.mem_bot] using hf
  rw [gtJ f g h] at hq ⊢
  rw [dfv hassoc hq hreg]
  calc
    _ ≤ ∑ r∈ah4 (c9 {f,g}) q,
        (∑ p∈z8 (c9 {f}),step oY f p*step p g r)*step r h q:= by
      apply yo
      intro r hr
      apply mul_le_mul_of_nonneg_right _ (step_nonneg r h q)
      have hrmin:=((aID _ _ _).mp hr).1
      rw [gtF f g] at hrmin ⊢
      rw [dfv hassoc hrmin (hregs r hr)]
      have hstart (p:oj aU) (hp:p∈ah4 (c9 {f}) r) :
          ((t5 p (c9 {f})).toNat :ℚ)=step oY f p:= by
        have hpmin:=((aID _ _ _).mp hp).1
        simp [step,hf',hzero,hpmin]
      trans ∑ p∈ah4 (c9 {f}) r,step oY f p*step p g r
      · exact le_of_eq (t4 rfl fun p hp=> by rw [hstart p hp])
      apply Z0
      · intro p hp
        exact (b8X _ _).mpr ((aID _ _ _).mp hp).1
      · intro p _ _
        exact Ee (step_nonneg oY f p) (step_nonneg p g r)
    _≤_:= by
      apply Z0
      · intro r hr
        exact (b8X _ _).mpr ((aID _ _ _).mp hr).1
      · intro r _ _
        exact Ee (ZK fun p _ =>
          Ee (step_nonneg oY f p) (step_nonneg p g r)) (step_nonneg r h q)
theorem of_children (h1 :c1) (h2 :c2) :K1_13_7_6.c2 := by
  classical
  intro f g h D hD hpoint hpay points w hmarks
  let ps :=z8 (c9 {f})
  let rs :=z8 (c9 {f,g})
  let qs :=points.image Yc
  have hcard:qs.card=points.card:=Yo _ pointPrime_injective
  have hq (q:oj aU) (hq:q∈qs) :
      (w:ℚ) ≤ ∑ r∈rs,(∑ p∈ps,step oY f p*step p g r)*(step r h q*D q) := by
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hq
    obtain ⟨q,hp,hm,hw,hfin⟩:=hmarks y hy
    have heq :q=Yc y :=PrimeSpectrum.ext_iff.mpr hp
    subst q
    refine le_trans ?_ (le_trans (point_chain_bound h1 h2 f g h y _ hp hm) ?_)
    · exact_mod_cast (by simpa only [ENat.toNat_natCast] using
        ENat.toNat_le_toNat hw hfin.ne :w≤(localColength
          (K1_13_7_4.pointPrime y) (Ideal.span {f,g,h})).toNat)
    · exact yo fun r _ =>
        WW
          (le_mul_of_one_le_right (step_nonneg r h _) (hpoint y _ hp))
          (ZK fun p _ =>
            Ee (step_nonneg oY f p) (step_nonneg p g r))
  have budget (p:oj aU) (t:aU)
      (ht:t∈({f,g,h} : Set aU)) (s :oz (oj aU)) :
      ∑ q∈s,step p t q*D q≤D p :=
    step_bound D hD p t (hpay t ht p) s
  calc
    (points.card:ℚ)*w = ∑ _∈qs,(w:ℚ) := by simp [hcard]
    _ ≤ ∑ q∈qs,∑ r∈rs,(∑ p∈ps,step oY f p*step p g r) *
        (step r h q*D q) :=yo hq
    _ = ∑ r∈rs,(∑ p∈ps,step oY f p*step p g r) *
        (∑ q∈qs,step r h q*D q) := by rw [N0]; simp_rw [Dz]
    _ ≤ ∑ r∈rs,(∑ p∈ps,step oY f p*step p g r)*D r := by
      apply yo
      intro r _
      exact mul_le_mul_of_nonneg_left (budget r h (by simp) qs)
        (ZK  fun p _ =>
          Ee  (step_nonneg oY  f p) (step_nonneg p g r))
    _ = ∑ p∈ps,step oY f p*(∑ r∈rs,step p g r*D r) := by
      simp_rw [Qx ,sS ,Dz]
      rw [N0]
    _ ≤ ∑ p∈ps,step oY f p*D p:= by
      exact yo fun p _ =>
        WW (budget p g (by simp) rs) (step_nonneg oY f p)
    _≤D zeroPrime :=budget oY f (by simp) ps
end
end aKv
end
section
namespace bzQ
noncomputable section
open wH MvPolynomial
def coordinate (y :Sz) (i:Fin 3) :Lower :=lz i - C (y i)
private def mo (y :Sz) (n:ℕ) :lI Lower :=
 c9 (coordinate y '' {i | i.val<n})
private def specialize (y :Sz) (n:ℕ) :aU →+* Lower :=
 vl C (fun i=>if i.val<n then C (y i) else lz i)
private theorem b63 (y :Sz) (n:ℕ) :
    GY (specialize y n)=mo y n:= by
  let I:=mo y n
  have hmk : (n5 I).comp (specialize y n)=n5 I:= by
    apply pU
    · intro c
      simp [specialize]
    · intro i
      simp only [pC,specialize,y5]
      split_ifs with hi
      · have hm:coordinate y i∈I:=t9 ⟨i,hi,rfl⟩
        have he :=(SL (I:=I)).mpr hm
        rw [coordinate,qG,sub_eq_zero] at he
        exact he.symm
      · rfl
  apply Ob
  · intro f hf
    apply (SL (I:=I)).mp
    have he :=G4 hmk f
    change n5 I (specialize y n f)=n5 I f at he
    rw [RingHom.mem_ker.mp hf,qz] at he
    exact he.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    have hi' : i.val<n:=hi
    simp [xm,coordinate,specialize,hi']
private instance c5f (y :Sz) (n:ℕ) :
  (mo y n).IsPrime := by
 rw [← b63]
 exact RingHom.ker_isPrime _
private theorem cH9 (y :Sz) (i:Fin 3) :
  coordinate y i≠0:= by
 intro he
 have he' := ov (Pc (fun _=>y i+1)) he
 simp [coordinate] at he'
private theorem cIa (y :Sz) (i:Fin 3) {n:ℕ}
  (hi:n≤ i.val) :coordinate y i∉mo y n:= by
 rw [← b63,xm]
 simpa [specialize,coordinate,not_lt.mpr hi] using cH9 y i
private theorem cct (y :Sz) (i:Fin 3) :
   mo y (i.val+1)=c9 {coordinate y i} ⊔ mo y i.val := by
 rw [mo,mo,← Zg]
 congr 1
 ext x
 constructor
 · rintro ⟨j,hj,rfl⟩
   change j.val< i.val+1 at hj
   by_cases hji:j=i
   · exact v9 (ov (coordinate y) hji)
   · have hv :j.val≠i.val := fun he=>hji (yU he)
     exact Or.inr ⟨j,(show j.val< i.val by omega),rfl⟩
 · rintro (rfl | ⟨j,hj,rfl⟩)
   · exact ⟨i,NX _,rfl⟩
   · exact ⟨j,Lf hj,rfl⟩
private theorem ccs (y :Sz) (i:Fin 3) :
  mo y i.val< mo y (i.val+1) := by
 rw [cct]
 refine lt_of_le_of_ne G5 ?_
 intro he
 apply cIa y i sI
 rw [he]
 exact Vq (xL _)
private theorem c5g (y :Sz) :
   mo y 3=oF y := by
 have he :specialize y 3=C.comp (eval y) := by
   apply pU
   · intro c
     simp [specialize]
   · intro i
     simp [specialize]
 rw [← b63,he,oF]
 ext p
 simp [xm]
theorem eMo (y :Sz) :3≤(oF y).height:= by
 have h0:=Nr (ccs y 0)
 have h1 :=Nr (ccs y 1)
 have h2 :=Nr (ccs y 2)
 change (mo y 0).height+1≤(mo y 1).height at h0
 change (mo y 1).height+1≤(mo y 2).height at h1
 change (mo y 2).height+1≤(mo y 3).height at h2
 rw [← c5g]
 calc
   (3:ℕ∞)=((0:ℕ∞)+1)+1+1 := by norm_num
   _≤(mo y 1).height+1+1 :=
     Gn (Gn ((Gn (zero_le :0≤(mo y 0).height) sI).trans h0) sI) sI
   _≤(mo y 2).height+1 :=Gn h1 sI
   _≤(mo y 3).height:=h2
private theorem cYI (y :Sz) (q:oj aU)
  (hy :q.asIdeal=oF y) (i:Fin 3) :
  let A:=p9 q.asIdeal
  let a :=cy aU A
  let I:=(mo y i.val).map a
  I.IsPrime∧a (coordinate y i)∉I:= by
 dsimp only
 let A:=p9 q.asIdeal
 let a :=cy aU A
 let J:=mo y i.val
 have hle :J≤q.asIdeal:= by
  rw [hy,← c5g]
  apply Ideal.span_mono
  rintro _ ⟨j,_,rfl⟩
  exact ⟨j,j.isLt,rfl⟩
 have hd:Ea (q.asIdeal.primeCompl:Set aU) (J:Set aU) :=
  Set.disjoint_left.mpr (fun _ hx hz=>hx (hle hz))
 refine ⟨QL q.asIdeal.primeCompl A J
  (c5f y i.val) hd,?_⟩
 have he :=G6 q.asIdeal.primeCompl A
  (c5f y i.val) hd
 change coordinate y i∉(J.map a).under aU
 rw [he]
 exact cIa y i sI
theorem exX (y :Sz) (q:oj aU)
   (hy :q.asIdeal=oF y) :
   let A:=p9 q.asIdeal
   let a :=cy aU A
   let u:=a (coordinate y 0)
   let v :=a (coordinate y 1)
   let w:=a (coordinate y 2)
   u≠0∧(c9 {u}).IsPrime∧v∉c9 {u} ∧
     (c9 {u,v}).IsPrime∧w∉c9 {u,v} := by
 dsimp only
 have h0:mo y 0 = ⊥ := by simp [mo]
 have h1 :mo y 1=c9 {coordinate y 0} := by
   have h:=cct y 0
   change mo y 1= _ ⊔ mo y 0 at h
   simpa [h0] using h
 have h2 :mo y 2=c9 {coordinate y 0,coordinate y 1} := by
   have h:=cct y 1
   change mo y 2= _ ⊔ mo y 1 at h
   rw [h,h1,Zg ,sup_comm]
 have hp1 :=cYI y q hy 1
 have hp2 :=cYI y q hy 2
 dsimp only at hp1 hp2
 change ((mo y 1).map _).IsPrime∧_∉(mo y 1).map _ at hp1
 change ((mo y 2).map _).IsPrime∧_∉(mo y 2).map _ at hp2
 rw [h1,yQ,zf] at hp1
 rw [h2,yQ,Kh,zf] at hp2
 refine ⟨?_,hp1.1,hp1.2,hp2.1,hp2.2⟩
 simpa only [qz] using (Ml (p9 q.asIdeal)
   q.asIdeal.primeCompl_le_nonZeroDivisors).ne (cH9 y 0)
end
end bzQ
end
section
namespace aRX
noncomputable section
open wH K1_13_7_6 aKv
open scoped Classical
private theorem cI6 {J:lI aU} {t:aU} {q p:oj aU}
  (hq:q.asIdeal∈(J ⊔ c9 {t}).minimalPrimes)
  (hJp:J≤p.asIdeal) (hpq:p.asIdeal≤q.asIdeal) :
  q.asIdeal∈(ke p t).minimalPrimes := by
 have htq:c9 {t} ≤ q.asIdeal:=le_sup_right.trans hq.le
 refine ⟨⟨q.isPrime,uJ hpq htq⟩,?_⟩
 intro s hs hsq
 exact hq.2 ⟨hs.1,uJ (hJp.trans (le_sup_left.trans hs.2))
  (le_sup_right.trans hs.2)⟩ hsq
private theorem d1p {R:Type*} [ox R] [IsNoetherianRing R]
   {P I Q:lI R} {t:R} (hP:P.IsPrime) (hI:I.IsPrime)
   (hQ:Q∈(P ⊔ c9 {t}).minimalPrimes) (hPI:P≤I) (hIQ:I≤Q)
   (hne :I≠Q) :I=P:= by
 let f :R →+* R ⧸ P:=n5 P
 have :=hQ.isPrime
 have hPQ:=hPI.trans hIQ
 have hh: (Q.map f).height≤1 :=Ideal.map_height_le_one_of_mem_minimalPrimes hQ
 have : (Q.map f).IsPrime :=ztf hPQ
 have hi: (I.map f).IsPrime :=ztf hPI
 have hlt:I.map f<Q.map f := by
   refine lt_of_le_of_ne (Ideal.map_mono hIQ) fun he=>hne ?_
   calc
     I=(I.map f).comap f :=(Kl hPI).symm
     _=(Q.map f).comap f :=ov (Ideal.comap f) he
     _= Q:=Kl hPQ
 have hz :=(Ideal.height_le_iff (n:=1)).mp hh (I.map f) hi hlt
 have hbot:=Ideal.height_eq_zero_iff_eq_bot.mp (Order.lt_one_iff.mp hz)
 calc
   I=(I.map f).comap f :=(Kl hPI).symm
   _=GY f := by rw [hbot,WK]
   _=P:= Qy
private theorem eOb {J:lI aU} {t:aU} {q r :oj aU}
   (hq:q.asIdeal∈(J ⊔ c9 {t}).minimalPrimes)
   (hJr :J≤ r.asIdeal) (hrq:r.asIdeal≤q.asIdeal) :
   r=q∨r∈ah4 J q:= by
 by_cases h:r=q
 · exact v9 h
 right
 obtain ⟨P,hP,hPr⟩:=Ideal.exists_minimalPrimes_le hJr
 let p:oj Lower :=⟨P,hP.isPrime⟩
 have hpq:q.asIdeal∈(P ⊔ c9 {t}).minimalPrimes :=
   cI6 (p:=p) hq hP.le (hPr.trans hrq)
 have he :r.asIdeal=P:=d1p hP.isPrime r.isPrime hpq hPr hrq
   (fun he=>h (PrimeSpectrum.ext_iff.mpr he))
 exact (aID J q r).mpr ⟨he.symm ▸ hP,hrq⟩
private theorem dS3 {J:lI aU} {t:aU}
  {q p:oj aU} (hreg:aB4 q J t)
  (hp:p∈ah4 J q) :
  vi (At q ⧸ p.asIdeal.map (cy aU (At q))) (cy aU (At q) t) := by
 obtain ⟨hpJ,hpq⟩:=(aID J q p).mp hp
 let A:=At q
 let a :=cy aU A
 let Q:=p.asIdeal.map a
 have hdisj:Ea (q.asIdeal.primeCompl:Set aU) (p.asIdeal:Set aU) :=
  Set.disjoint_left.mpr (fun _ hx hxp=>hx (hpq hxp))
 let:Q.IsPrime :=
  QL q.asIdeal.primeCompl A p.asIdeal p.isPrime hdisj
 have hcomap :Q.under aU=p.asIdeal :=
  G6 q.asIdeal.primeCompl A p.isPrime hdisj
 have hmin:Q∈(J.map a).minimalPrimes := by
  change Q∈(J.map (cy aU A)).minimalPrimes
  rw [VC q.asIdeal.primeCompl A,Set.mem_preimage,hcomap]
  exact hpJ
 change vi (A ⧸ J.map a) (a t) at hreg
 have hmin' : Q∈(FU A (A ⧸ J.map a)).minimalPrimes := by
  rwa [Df]
 have ha :n5 Q (a t)≠0 :=
  fun he=>(hreg.notMem_of_mem_minimalPrimes hmin') (Ideal.Quotient.eq_zero_iff_mem.mp he)
 change vi (A ⧸ Q) (a t)
 apply IsSMulRegular.of_right_eq_zero_of_smul
 intro x hx
 exact (mul_eq_zero.mp (show n5 Q (a t)*x=0 from hx)).resolve_left ha
theorem exm {J:lI aU} {q p r :oj aU}
   (hp:p∈ah4 J q) (hr :J≤ r.asIdeal) :
   avs p (aU ⧸ r.asIdeal)=if r=p then 1 else 0:= by
 classical
 by_cases he :r=p
 · subst r
   simpa using cYp p
 rw [vk he]
 apply cYo
 intro hrp
 have hm:=((aID J q p).mp hp).1
 have hle :p.asIdeal≤ r.asIdeal:=hm.2 ⟨r.isPrime,hr⟩ hrp
 exact he (PrimeSpectrum.ext_iff.mpr (hrp.antisymm hle))
theorem dS1 {J:lI aU} {t:aU} {q r :oj aU}
    (hq:q.asIdeal∈(J ⊔ c9 {t}).minimalPrimes)
    (hreg:aB4 q J t) (hr :J≤ r.asIdeal) :
    aAR (cy aU (At q) t) (XQ q (aU ⧸ r.asIdeal)) ∧
      auJ (cy aU (At q) t) (XQ q (aU ⧸ r.asIdeal)) =
        if r∈ah4 J q then ((t5 q (ke r t)).toNat :ℤ) else 0:= by
  classical
  by_cases hp:r∈ah4 J q
  · rw [wB hp]
    exact bDL q r.asIdeal t (dS3 hreg hp)
      (Re (cI6 (p:=r) hq hr ((aID J q r).mp hp).2))
  rw [vk hp]
  apply cI7
  change avs q (aU ⧸ r.asIdeal) < ⊤
  by_cases hrq:r.asIdeal≤q.asIdeal
  · rcases eOb hq hr hrq with h | h
    · subst r
      simp [cYp]
    · exact (hp h).elim
  · simp [cYo hrq]
end
end aRX
end
section
namespace bzQ
noncomputable section
open wH aKv
local instance :GCDMonoid Lower :=UniqueFactorizationMonoid.toGCDMonoid aU
private theorem c1O {q:lI aU} (hq:3≤q.height) (a b:aU) :
  q∉(c9 {a,b}).minimalPrimes := by
 intro hp
 have hn: ({a,b} : Set aU).ncard≤2 :=
  (Set.ncard_insert_le _ _).trans (by simp)
 have hle :q.height≤2 :=
  (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hp).trans (by exact_mod_cast hn)
 exact (by norm_num : ¬ (3:ℕ∞)≤2) (hq.trans hle)
private theorem efj {f g h:aU} {q:oj aU}
   (hh:3≤q.asIdeal.height) (hq:q.asIdeal∈(c9 {f,g,h}).minimalPrimes) :
   gcd f g∉q.asIdeal:= by
 intro hd
 apply c1O hh (gcd f g) h
 have ht:h∈q.asIdeal:=hq.le (t9 (by simp))
 refine ⟨⟨q.isPrime,Ideal.span_le.mpr ?_⟩,?_⟩
 · simp only [J4 ,NW]
   exact ⟨hd,ht⟩
 intro p hp hpq
 have hdp:gcd f g∈p:=hp.2 (t9 (by simp))
 have hhp:h∈p:=hp.2 (t9 (by simp))
 have hfp:f∈p:= by
   obtain ⟨k,hk⟩:=gcd_dvd_left f g
   rw [hk]
   exact p.mul_mem_right _ hdp
 have hgp:g∈p:= by
   obtain ⟨k,hk⟩:=gcd_dvd_right f g
   rw [hk]
   exact p.mul_mem_right _ hdp
 apply hq.2 ⟨hp.1,Ideal.span_le.mpr ?_⟩ hpq
 simp only [J4 ,NW]
 exact ⟨hfp,hgp,hhp⟩
private theorem c7X (p:oj aU) {f g:aU}
  (hd:gcd f g∉p.asIdeal) :aB4 p (c9 {f}) g:= by
 let A:=p9 p.asIdeal
 let a :=cy aU A
 let J:lI Lower :=c9 {f}
 change vi (A ⧸ J.map a) (a g)
 apply (isSMulRegular_quotient_iff_mem_of_smul_mem (J.map a) (a g)).mpr
 intro z hz
 change a g*z∈J.map a at hz
 obtain ⟨x,s,rfl⟩:=IsLocalization.exists_mk'_eq p.asIdeal.primeCompl z
 rw [WY ,VS] at hz
 obtain ⟨t,ht,htx⟩:=hz
 rw [← Pv g t x,G9] at htx
 have hdx :t*(gcd f g*x)∈J:= by
  change t*(gcd f g*x)∈c9 {f}
  rw [Pv t,G9]
  exact dvd_gcd_mul_of_dvd_mul htx
 have hmem:a (gcd f g)* IsLocalization.mk' A x s∈J.map a := by
  rw [WY ,VS]
  exact ⟨t,ht,hdx⟩
 exact ((J.map a).unit_mul_mem_iff_mem
  (II A (⟨gcd f g,hd⟩:p.asIdeal.primeCompl))).mp hmem
private theorem cbd {A:Type*} [ox A] [vH A]
  {f g:A} (hf :f≠0) (hg:vi (A ⧸ c9 {f}) g)
  {a b:A} (hab:f*a+g*b=0) :
  ∃ c:A,a=g*c∧b = -(f*c) := by
 have hm:g*b∈c9 {f} := by
  have he :g*b=f*(-a) := by linear_combination hab
  rw [he]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right f (-a))
 have hb:f∣b:=Ideal.mem_span_singleton.mp
  (mem_of_isSMulRegular_quotient_of_smul_mem hg hm)
 obtain ⟨k,hk⟩:=hb
 refine ⟨-k,SC hf ?_,by rw [hk]; ring⟩
 linear_combination hab - g*hk
private theorem eES {A:Type*} [ox A] [vH A]
  {u v w f g z :A} (hu:u≠0)
  (hU: (c9 ({u} : Set A)).IsPrime) (hv :v∉c9 {u})
  (hUV: (c9 ({u,v} : Set A)).IsPrime) (hw:w∉c9 {u,v})
  (hf :f≠0) (hg:vi (A ⧸ c9 {f}) g)
  (hz0:u*z∈c9 {f,g}) (hz1 :v*z∈c9 {f,g})
  (hz2 :w*z∈c9 {f,g}) :
  z∈c9 {f,g} := by
 obtain ⟨a0,b0,h0⟩:=Ideal.mem_span_pair.mp hz0
 obtain ⟨a1,b1,h1⟩:=Ideal.mem_span_pair.mp hz1
 obtain ⟨a2,b2,h2⟩:=Ideal.mem_span_pair.mp hz2
 obtain ⟨c01,ha01,hb01⟩:=cbd hf hg
  (a :=u*a1 - v*a0) (b:=u*b1 - v*b0) (by
    linear_combination u*h1 - v*h0)
 obtain ⟨c02,_,hb02⟩:=cbd hf hg
  (a :=u*a2 - w*a0) (b:=u*b2 - w*b0) (by
    linear_combination u*h2 - w*h0)
 obtain ⟨c12,_,hb12⟩:=cbd hf hg
  (a :=v*a2 - w*a1) (b:=v*b2 - w*b1) (by
    linear_combination v*h2 - w*h1)
 have hc:u*c12 - v*c02+w*c01=0:= by
  apply SC hf
  linear_combination u*hb12 - v*hb02+w*hb01
 have hwc:w*c01∈c9 {u,v} :=
  Ideal.mem_span_pair.mpr ⟨-c12,c02,by linear_combination -hc⟩
 have hc' := (hUV.mem_or_mem hwc).resolve_left hw
 obtain ⟨c,d,hcd⟩:=Ideal.mem_span_pair.mp hc'
 have div_first {x y :A} (he :u*y=v*x) :u∣x := by
  have hm:v*x∈c9 {u} := he ▸
    Ideal.mem_span_singleton.mpr (dvd_mul_right u y)
  exact Ideal.mem_span_singleton.mp ((hU.mem_or_mem hm).resolve_left hv)
 obtain ⟨a,ha⟩:=div_first (x :=a0+g*d) (y :=a1 - g*c)
  (by linear_combination ha01 - g*hcd)
 obtain ⟨b,hb⟩:=div_first (x :=b0 - f*d) (y :=b1+f*c)
  (by linear_combination hb01+f*hcd)
 refine Ideal.mem_span_pair.mpr ⟨a,b,SC hu ?_⟩
 linear_combination h0 - f*ha - g*hb
private theorem fVM {f g h:aU} {y :Sz} {q:oj aU}
    (hy :q.asIdeal=oF y) (hf :f≠0)
    (hg:aB4 q (c9 {f}) g)
    (hq:q.asIdeal∈(c9 {f,g,h}).minimalPrimes) :
    aB4 q (c9 {f,g}) h:= by
  let A:=p9 q.asIdeal
  let a :=cy aU A
  let F:=a f
  let G:=a g
  let H :=a h
  let J:lI A:=c9 {F,G}
  have hMapPair : (c9 ({f,g} : Set aU)).map a=J:= by
    rw [yQ,Kh,zf]
  change vi (A ⧸ (c9 {f,g}).map a) H
  rw [hMapPair]
  change vi (A ⧸ (c9 {f}).map a) G at hg
  rw [yQ,zf] at hg
  have hF:F≠0:= by
    simpa only [qz] using
      (Ml A q.asIdeal.primeCompl_le_nonZeroDivisors).ne hf
  have hrad: (c9 ({F,G,H} : Set A)).radical=RP A:= by
    simpa only [yQ,Kh,zf ,
      VH q.asIdeal A] using
      (IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A:=A) q.asIdeal
        (c9 {f,g,h}) hq)
  by_contra hn
  have hmem:H ∈ ⋃ p∈associatedPrimes A (A ⧸ J),(p:Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hn
  obtain ⟨p,hp,hH⟩:=Set.mem_iUnion₂.mp hmem
  obtain ⟨hpPrime,x,hx⟩:=isAssociatedPrime_iff.mp hp
  have hJ:J≤p:= by
    rw [← Df (I:=J)]
    intro t ht
    rw [hx,ztS,Vz]
    exact Module.mem_annihilator.mp ht x
  have hmp:RP A≤p:= by
    rw [← hrad,← hpPrime.radical]
    apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    simp only [J4 ,NW]
    exact ⟨hJ (t9 (by simp)),hJ (t9 (by simp)),hH⟩
  have hxne :x≠0:= by
    intro he
    exact hpPrime.ne_top' (by simp [hx,he,Submodule.colon_singleton_zero])
  obtain ⟨z,rfl⟩:=uW x
  have hz (i:Fin 3) :a (coordinate y i)*z∈J:= by
    have hm:a (coordinate y i)∈RP A:= by
      rw [← VH q.asIdeal A]
      apply Et
      rw [hy]
      simp [coordinate,oF,xm]
    have hp' := hmp hm
    rw [hx,ztS,Vz] at hp'
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [nI]
    exact hp'
  obtain ⟨hu,hU,hv,hUV,hw⟩:=exX y q hy
  exact hxne (Ideal.Quotient.eq_zero_iff_mem.mpr
    (eES hu hU hv hUV hw hF hg (hz 0) (hz 1) (hz 2)))
theorem proof :aKv.c1 := by
 intro f g h y q hy hq
 have hh:3≤q.asIdeal.height:=hy.symm ▸ eMo y
 have hf :f≠0:= by
  intro he
  subst f
  exact c1O hh g h (by simpa only [Ideal.span_insert_zero] using hq)
 have hd:=efj hh hq
 refine ⟨hf,fVM hy hf (c7X q hd) hq,?_⟩
 intro r hr
 have hrq:=((aID _ _ _).mp hr).2
 exact c7X r (fun hm=>hd (hrq hm))
end
end bzQ
end
section
namespace aRX
noncomputable section
open wH K1_13_7_6 aKv
open scoped BigOperators
private def SS (q:oj aU) (t:aU) (p:oj aU) :ℤ :=
 (t5 q (ke p t)).toNat
private theorem eA9 {J:lI aU} {t:aU} {q:oj aU}
    (hq:q.asIdeal∈(J ⊔ c9 {t}).minimalPrimes)
    (hreg:aB4 q J t)
    (M:Type) [AddCommGroup M] [Module aU M] [v8 aU M]
    (hJ:J≤FU aU M) :
    aAR (cy aU (At q) t) (XQ q M) ∧
      (∀ p∈ah4 J q,avs p M < ⊤) ∧
      auJ (cy aU (At q) t) (XQ q M) =
        ∑ p∈ah4 J q,(avs p M).toNat*SS q t p:= by
  classical
  let u:=cy aU (At q) t
  revert hJ
  induction (Oc :v8 aU M) using
      IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime aU with
  | subsingleton N =>
    intro _
    have h (p:oj aU) :avs p N=0:=Module.length_eq_zero
    have hz :=cI7 u (show avs q N < ⊤ by simp [h])
    refine ⟨hz.1,fun p _=> by simp [h],?_⟩
    simpa [h] using hz.2
  | quotient N r e =>
    intro hJ
    rw [e.annihilator_eq,Df] at hJ
    let E (p:oj aU) :XQ p N ≃ₗ[At p] XQ p (aU ⧸ r.asIdeal) :=
      IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
        (Yi p.asIdeal.primeCompl N)
        (Yi p.asIdeal.primeCompl (aU ⧸ r.asIdeal)) (At p) e
    have hw (p:oj aU) (hp:p∈ah4 J q) :
        avs p N=if r=p then 1 else 0 :=
      (E p).length_eq.trans (exm hp hJ)
    have hc:=dS1 hq hreg hJ
    have he :=cI0 u (E q)
    refine ⟨he.1.mpr hc.1,fun p hp=> by rw [hw p hp]; split <;> simp,?_⟩
    rw [he.2,hc.2]
    by_cases hr :r∈ah4 J q
    · rw [wB hr,Qw r]
      · simp [hw r hr,SS]
      · intro p hp hpr
        simp [hw p hp,Ne.symm hpr]
      · exact fun h=>(h hr).elim
    · rw [vk hr,Pf]
      intro p hp
      have hne :r≠p:= fun h=>hr (h ▸ hp)
      simp [hw p hp,hne]
  | exact N₁ N₂ N₃ f g hf hg hfg ih₁ ih₃ =>
    intro hJ
    have h₁:=ih₁ (hJ.trans (f.annihilator_le_of_injective hf))
    have h₃:=ih₃ (hJ.trans (g.annihilator_le_of_surjective hg))
    have hex (p:oj aU) :
        Function.Exact (UP p.asIdeal.primeCompl f)
          (UP p.asIdeal.primeCompl g) :=
      LocalizedModule.map_exact p.asIdeal.primeCompl f g hfg
    have hl (p:oj aU) :avs p N₂=avs p N₁+avs p N₃ :=
      Module.length_eq_add_of_exact _ _
        (ZJ p.asIdeal.primeCompl f hf)
        (S2 p.asIdeal.primeCompl g hg) (hex p)
    have hc:=dSA u _ _ (ZJ q.asIdeal.primeCompl f hf)
      (S2 q.asIdeal.primeCompl g hg) (hex q) h₁.1 h₃.1
    refine ⟨hc.1,fun p hp=>(hl p).symm ▸ ENat.add_lt_top.mpr ⟨h₁.2.1 p hp,h₃.2.1 p hp⟩,?_⟩
    rw [hc.2,h₁.2.2,h₃.2.2,← wR]
    apply t4 rfl
    intro p hp
    rw [hl p,ENat.toNat_add (h₁.2.1 p hp).ne (h₃.2.1 p hp).ne,zg ,add_mul]
theorem proof :aKv.c2 := by
 intro J t q hq hreg
 have hm:=eA9 hq hreg (aU ⧸ J)
  (show J≤FU aU (aU ⧸ J) by rw [Df])
 have hc:=bDL q J t hreg (Re hq)
 have h:=hm.2.2
 rw [hc.2] at h
 simp only [b70,SS] at h
 exact_mod_cast h
end
end aRX
end
section
namespace aBb
open gT YY
def c1 :Prop :=
  ∀ I:lI th,I.IsPrime→xI (rM I) →
    vH (rM I) ∧
      ∃ (f :aLP (xg I) →ₐ[aQ] abX (Si I))
        (j:abX (Si I) →ₐ[aQ] rM I),
        qm f∧qm j
def c2 :Prop :=
  ∀ I:lI th,
    ∃ j:SI (Si I) →ₐ[aQ] as2 I,qm j
theorem of_children (h1 :c1) (h2 :c2) :YY.c2 :=
 assemble h1 eLN h2
end aBb
end
section
set_option backward.isDefEq.respectTransparency false
namespace czq
noncomputable section
open cu gT YY GK
open scoped Polynomial
local instance (n:ℕ) (I:lI (Raw n)) :ox (gk I)[X] :=
 @RD (gk I) (IT I)
private theorem aG3 {n:ℕ} (I:lI (Raw n)) (i j:Fin n)
    (x :p5 I i j) :
    ∃ (q: (gk I)[X]) (d:aQ),d≠0 ∧
      x*cy aQ (p5 I i j) d=vV I i j q:= by
  let:t6 (nX (Fin n) aZ) (Over n) :=MvPolynomial.algebraMvPolynomial
  obtain ⟨f,rfl⟩:=uW x
  obtain ⟨⟨g,m⟩,hgm⟩:=Zf
    (M:=(u9 aZ).map (mD (σ:=Fin n))) f
  obtain ⟨d,hd,hdm⟩:=m.property
  let lift:nX (Fin n) aZ →+* (gk I)[X] :=
    vl (qw I i j) (fun k=>lV (coord I k))
  have hcomp: (vV I i j).comp lift =
      (n5 (i9 I i j)).comp
        (p7 (cy aZ aQ)) := by
    apply pU
    · intro a
      simp only [pC,lift,z7,C5]
      rw [← zk,Wm]
      exact oZ (aEa I i j) a
    · intro k
      simp [lift,vV,toSlice,pC]
  refine ⟨lift g,cy aZ aQ d,?_,?_⟩
  · exact fun h=>mem_nonZeroDivisors_iff_ne_zero.mp hd
      (ze aZ aQ (h.trans (qz _).symm))
  · have hgm' : f*mD (cy aZ aQ d) =
        p7 (cy aZ aQ) g:= by
      simpa only [zu8,← hdm,C5] using hgm
    calc
      _=n5 (i9 I i j)
          (f*mD (cy aZ aQ d)) :=(nI _ _ _).symm
      _ = _:=(ov (n5 (i9 I i j)) hgm').trans
        (oZ hcomp g).symm
private theorem bV9 {n:ℕ} (I:lI (Raw n)) (i j:Fin n)
   {x :p5 I i j} {d:aQ} (hd:d≠0)
   (h:x*cy aQ (p5 I i j) d=0) :x=0 :=
 ((isUnit_iff_ne_zero.mpr hd).map (cy aQ (p5 I i j))).mul_right_cancel
   (h.trans (zero_mul _).symm)
private theorem gsb {n:ℕ} (I:lI (Raw n)) (i j:Fin n)
   [I.IsPrime] [xI (p5 I i j)] :vH (p5 I i j) := by
 let:NoZeroDivisors (p5 I i j) := by
   constructor
   intro x y hxy
   obtain ⟨q,d,hd,hq⟩:=aG3 I i j x
   obtain ⟨r,e,he,hr⟩:=aG3 I i j y
   let d' : p5 I i j:=cy aQ (p5 I i j) d
   let e' : p5 I i j:=cy aQ (p5 I i j) e
   have hqr :vV I i j (q*r)=0:= calc
     _=vV I i j q*vV I i j r :=nI _ q r
     _=(x*d')*(y*e') :=congrArg₂ (· * ·) hq.symm hr.symm
     _=(x*y)*(d' * e') :=mul_mul_mul_comm x d' y e'
     _=0:= by rw [hxy,zero_mul]
   have hz :q*r=0:=aQr I i j (hqr.trans (qz _).symm)
   rcases mul_eq_zero.mp hz with h | h
   · exact v9 (bV9 I i j hd (by simpa only [h,qz] using hq))
   · exact Or.inr (bV9 I i j he (by simpa only [h,qz] using hr))
 exact NoZeroDivisors.to_isDomain _
private abbrev EG (n:ℕ) :Raw n →+* Over n :=
 p7 (cy FX aQ)
private abbrev contraction {n m:ℕ} (e :Fin n→Fin m) (I:lI (Raw m)) :
  lI (Raw n) :=
 I.comap (oy e).toRingHom
private theorem c8g {n m:ℕ} (e :Fin n→Fin m) :
    ((oy e :Over n →ₐ[aQ] Over m).toRingHom).comp
        (EG n) =
      (EG m).comp (oy e :Raw n →ₐ[FX] Raw m).toRingHom:= by
  apply pU
  · intro a
    simp [pC]
  · intro k
    simp [pC]
private theorem gnu {n m:ℕ} (e :Fin n→Fin m) (I:lI (Raw m))
   (i j:Fin n) :
   i9 (contraction e I) i j ≤
     (i9 I (e i) (e j)).comap (oy e :Over n →ₐ[aQ] Over m) := by
 refine uJ (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
 · intro p hp
   change (((oy e :Over n →ₐ[aQ] Over m).toRingHom).comp
     (EG n)) p∈i9 I (e i) (e j)
   rw [c8g]
   exact (show I.map (EG m)≤ i9 I (e i) (e j) from yl)
     (Et (EG m) hp)
 · intro p hp
   obtain rfl :=Set.mem_singleton_iff.mp hp
   change oy e (B4 i j)∈i9 I (e i) (e j)
   have h:oy e (B4 i j)=B4 (e i) (e j) := by
     simp [B4]
   rw [h]
   exact (show c9 {B4 (e i) (e j)} ≤ i9 I (e i) (e j) from G5)
     (xL _)
private def a8B {n m:ℕ} (e :Fin n→Fin m) (I:lI (Raw m))
  (i j:Fin n) :p5 (contraction e I) i j →ₐ[aQ] p5 I (e i) (e j) :=
 zwL (i9 I (e i) (e j)) (oy e) (gnu e I i j)
private def bKX {n m:ℕ} (e :Fin n→Fin m) (I:lI (Raw m)) :
  gk (contraction e I) →+* gk I :=
 JK I (oy e).toRingHom sI
private theorem gse {n m:ℕ} (e :Fin n→Fin m) (I:lI (Raw m))
   (i j:Fin n) :
   (a8B e I i j).toRingHom.comp (vV (contraction e I) i j) =
     (vV I (e i) (e j)).comp (t7 (bKX e I)) := by
 apply EP
 · intro a
   obtain ⟨a,rfl⟩:=uW a
   simp only [pC,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,vV,
     SW,UZ,xW,RJ,
     toSlice,bKX,Ideal.quotientMap_mk,a8B,Zi ,
     Vs]
   exact ov (n5 (i9 I (e i) (e j)))
     (oZ (c8g e) a)
 · simp [vV,pC]
private theorem dem {n m:ℕ} (e :Fin n→Fin m) (I:lI (Raw m))
  (i j:Fin n) [I.IsPrime] [xI (p5 I (e i) (e j))] :
  qm (a8B e I i j) := by
 apply (Mz (a8B e I i j)).mpr
 intro x hx
 obtain ⟨q,d,hd,hq⟩:=aG3 (contraction e I) i j x
 have hq' : a8B e I i j (vV (contraction e I) i j q)=0:= by
  rw [← hq,nI,hx,zero_mul]
 have hs :vV I (e i) (e j) (Polynomial.map (bKX e I) q)=0 :=
  (oZ (gse e I i j) q).symm.trans hq'
 have hq0:q=0:=(X4
    (show qm (bKX e I) from zmq)).mp
  ((Mz _).mp (aQr I (e i) (e j)) _ hs)
 exact bV9 (contraction e I) i j hd (by simpa only [hq0,qz] using hq)
theorem proof :aBb.c1 := by
 intro I hI hJet
 let e :Fin 2→Fin 3:=Nj (by decide)
 let t:Fin 3→Fin 4 :=Nj (by decide)
 let j:gT.abX (Si I) →ₐ[aQ] rM I :=
  a8B t I 0 1
 have hj:qm j := @dem 3 4 t I 0 1 hI hJet
 have hRootPrime : (Si I).IsPrime :=hI.comap oi
 have hRoot:xI (abX (Si I)) := by
  let:xI (rM I) :=hJet
  exact j.toRingHom.domain_nontrivial
 let f :aBb.aLP (xg I) →ₐ[aQ] abX (Si I) :=
  a8B e (Si I) 0 1
 exact ⟨@gsb 4 I 0 1 hI hJet,f,j,
  @dem 2 3 e (Si I) 0 1 hRootPrime hRoot,hj⟩
end
end czq
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace bzX
noncomputable section
open cu gT
abbrev Raw (n:ℕ) :=nX (Fin n) FX
abbrev Integral (n:ℕ) :=nX (Fin n) aZ
abbrev Over (n:ℕ) :=nX (Fin n) aQ
local instance (n:ℕ) (I:lI (Raw n)) :ox (lJ (gk I)) :=
 @RD (gk I) (IT I)
abbrev buK (n:ℕ) :Raw n →+* Integral n :=
 p7 mD
abbrev relation {n:ℕ} (i:Fin n) :Integral n :=
 lz i-MvPolynomial.C (lz (1 :Fin 2))
abbrev O6 {n:ℕ} (I:lI (Raw n)) (i:Fin n) :lI (Integral n) :=
 I.map (buK n) ⊔ c9 {relation i}
abbrev cVp {n:ℕ} (I:lI (Raw n)) (i:Fin n) :=
 Integral n ⧸ O6 I i
abbrev coord {n:ℕ} (I:lI (Raw n)) (k :Fin n) :gk I :=
 n5 I (lz k)
def parameter {n:ℕ} (I:lI (Raw n)) (i:Fin n) :
    aZ →+* lJ (gk I) :=
  vl (Polynomial.C.comp (cy FX (gk I)))
    ![nq,lV (coord I i)]
def FT {n:ℕ} (I:lI (Raw n)) (i:Fin n) :
    Integral n →+* lJ (gk I) :=
  vl (parameter I i) (fun k=>lV (coord I k))
private theorem d0X {n:ℕ} (I:lI (Raw n)) (i:Fin n) :
   (FT I i).comp (buK n)=Polynomial.C.comp (n5 I) := by
 apply pU
 · intro a
   simp [FT,parameter]
   rfl
 · intro k
   simp [FT]
private def bK8 {n:ℕ} (I:lI (Raw n)) (i:Fin n) :
  gk I →+* cVp I i :=
 JK (O6 I i) (buK n)
  (Ideal.map_le_iff_le_comap.mp yl)
private def restore {n:ℕ} (I:lI (Raw n)) (i:Fin n) :
  lJ (gk I) →+* cVp I i :=
 zqf (bK8 I i)
  (n5 (O6 I i) (mD (lz (0:Fin 2))))
private theorem eoH {n:ℕ} (I:lI (Raw n)) (i:Fin n) :
   n5 (O6 I i) (lz i) =
     n5 (O6 I i) (mD (lz (1 :Fin 2))) := by
 rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
 exact (show c9 {relation i} ≤ O6 I i from G5)
   (xL _)
private theorem fW8 {n:ℕ} (I:lI (Raw n)) (i:Fin n) :
    (restore I i).comp (FT I i)=n5 (O6 I i) := by
  apply pU
  · intro s
    have h: (restore I i).comp (parameter I i) =
        (n5 (O6 I i)).comp MvPolynomial.C:= by
      apply pU
      · intro a
        simp [parameter,restore,bK8,zk]
      · intro k
        fin_cases k
        · simp [parameter,restore]
        · simpa [parameter,restore,bK8] using eoH I i
    simpa [FT] using oZ h s
  · intro k
    simp [FT,restore,bK8]
theorem ez5 {n:ℕ} (I:lI (Raw n)) (i:Fin n) (f :Integral n) :
   f∈O6 I i↔FT I i f=0:= by
 constructor
 · change f∈O6 I i→f∈GY (FT I i)
   apply (show O6 I i≤GY (FT I i) from ?_)
   refine uJ (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
   · intro p hp
     change ((FT I i).comp (buK n)) p=0
     rw [d0X]
     simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
   · rintro p (rfl :p=relation i)
     simp [FT,parameter,xm]
 · intro h
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   rw [← fW8 I i]
   simp [h]
end
end bzX
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace bzX
noncomputable section
open cu gT YY
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance (n:ℕ) (I:lI (Raw n)) :ox (lJ (gk I)) :=
 @RD (gk I) (IT I)
private abbrev keep:Fin 3→Fin 4 :=Nj (by decide :3≤4)
private abbrev incl (R:Type) [ox R] :
  nX (Fin 3) R →ₐ[R] nX (Fin 4) R :=
 oy keep
private abbrev EG (n:ℕ) :Raw n →+* Over n :=
 p7 (cy FX aQ)
private abbrev localize (n:ℕ) :Integral n →+* Over n :=
 cy (Integral n) (Over n)
private abbrev Ek (n:ℕ) :Submonoid (Integral n) :=
 (u9 aZ).map mD
private abbrev i9 {n:ℕ} (I:lI (Raw n)) (i:Fin n) :lI (Over n) :=
 I.map (EG n) ⊔ c9 {Pp i}
private theorem ey2 {n:ℕ} (I:lI (Raw n)) (i:Fin n) :
    (O6 I i).map (localize n)=i9 I i:= by
  rw [O6,Ideal.map_sup,Ideal.map_map,yQ,zf]
  have h: (localize n).comp (buK n)=EG n:= by
    have hbase : (cy aZ aQ).comp (mD:FX →+* aZ) =
        algebraMap FX aQ :=
      (IsScalarTower.algebraMap_eq FX aZ aQ).symm
    apply SD
    intro f
    change p7 (cy aZ aQ) (p7 mD f) =
      p7 (cy FX aQ) f
    rw [MvPolynomial.map_map,hbase]
  rw [h]
  have hr :localize n (relation i)=Pp i:= by
    change p7 (cy aZ aQ) (relation i)=Pp i
    simp only [relation,Pp,qG,MvPolynomial.map_X,C5 ,ek]
  rw [hr]
private def bgy (I:lI th) :gk (Si I) →+* gk I :=
 JK I oi sI
private theorem fTW (I:lI th) :qm (bgy I) :=
 zmq
private theorem c68 (I:lI th) (k :Fin 3) :
  bgy I (coord (Si I) k)=coord I (keep k) := by
 simp [bgy,oi]
private theorem d0V (I:lI th) :
   (FT I 2).comp (incl aZ).toRingHom =
     (t7 (bgy I)).comp (FT (Si I) 2) := by
 have hp: (t7 (bgy I)).comp (parameter (Si I) 2) =
     parameter I 2 := by
   apply pU
   · intro a
     simp [parameter,bgy,oi,zk]
     rfl
   · intro k
     fin_cases k
     · simp [parameter]
     · simpa [parameter,show keep (2 :Fin 3)=(2 :Fin 4) from rfl] using
         ov lV (c68 I 2)
 apply pU
 · intro s
   simpa [FT] using (oZ hp s).symm
 · intro k
   simpa [FT] using (ov lV (c68 I k)).symm
private theorem eoF (I:lI th) (f :Integral 3)
  (hf :incl aZ f∈O6 I 2) :f∈O6 (Si I) 2 := by
 rw [ez5] at hf ⊢
 have h:=oZ (d0V I) f
 exact (X4 (fTW I)).mp (h.symm.trans hf)
private theorem exT (f :Integral 3) :
   incl aQ (localize 3 f)=localize 4 (incl aZ f) :=
 (zoD (cy aZ aQ) keep f).symm
private theorem gnK (I:lI th) :
   i9 (Si I) 2≤(i9 I 2).comap (incl aQ).toRingHom:= by
 refine uJ (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
 · intro p hp
   change incl aQ (EG 3 p)∈i9 I 2
   rw [← zoD]
   exact (show I.map (EG 4)≤ i9 I 2 from yl)
    (Et (EG 4) hp)
 · rintro q (rfl :q=Pp (2 :Fin 3))
   change incl aQ (Pp (2 :Fin 3))∈i9 I 2
   have hy :incl aQ (Pp (2 :Fin 3))=Pp (2 :Fin 4) := by
    simp [Pp,show keep (2 :Fin 3)=(2 :Fin 4) from rfl]
   rw [hy]
   exact (show c9 {Pp (2 :Fin 4)} ≤ i9 I 2 from G5)
    (xL _)
private theorem ex2 (I:lI th) (f :Integral 3)
   (hf :localize 4 (incl aZ f)∈i9 I 2) :
   localize 3 f∈i9 (Si I) 2 := by
 rw [← ey2] at hf ⊢
 obtain ⟨_,⟨d,hd,rfl⟩,hmem⟩ :=
   (XJ (Ek 4)
     (Over 4) (O6 I 2) (incl aZ f)).mp hf
 rw [ XJ (Ek 3)]
 refine ⟨mD d,Submonoid.mem_map_of_mem _ hd,?_⟩
 apply eoF I
 simpa only [nI,zt1] using hmem
private theorem gnL (I:lI th) (f :Over 3)
  (hf :incl aQ f∈i9 I 2) :
  f∈i9 (Si I) 2 := by
 obtain ⟨⟨g,m⟩,hm⟩:=Zf
  (M:=Ek 3) f
 obtain ⟨d,hd,hdm⟩:=m.property
 have heq :f*mD (cy aZ aQ d)=localize 3 g:= by
  simpa only [← hdm,zu8,C5] using hm
 have hg:localize 4 (incl aZ g)∈i9 I 2 := by
  rw [← exT,← heq,nI]
  exact Ideal.mul_mem_right _ _ hf
 have hu:IsUnit (mD (σ:=Fin 3) (cy aZ aQ d)) :=
  (II aQ (⟨d,hd⟩:u9 aZ)).map mD
 apply (Ideal.mul_unit_mem_iff_mem _ hu).mp
 rw [heq]
 exact ex2 I g hg
private def iJ (I:lI th) :SI (Si I) →ₐ[aQ] as2 I :=
 zwL (i9 I 2) (incl aQ) (gnK I)
theorem proof :aBb.c2 := by
 intro I
 refine ⟨iJ I,(Mz _).mpr ?_⟩
 intro x hx
 obtain ⟨f,rfl⟩:=uW x
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 apply gnL I
 apply Ideal.Quotient.eq_zero_iff_mem.mp
 simpa only [iJ,Zi ,Vs] using hx
end
end bzX
end
section
namespace Sy
open aR jA NR aFN
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
noncomputable section
private theorem gsR (a :t8) (q:ℕ) (s :Slot a q) :
  cV (pG a q s)=q:= by
 have h₂:=s.1.isLt
 have h₁:=s.2.isLt
 simp only [Nat.lt_succ_iff,Pr] at h₂ h₁
 simp [cV,pG]
 omega
private theorem cp5 (a :t8) (q:ℕ) (e :Exp) (h:cV e=q)
  (hw:weight e≤a.j) (ht:e 2≤a.t) : ∃ s :Slot a q,pG a q s=e := by
 unfold cV at h
 unfold weight at hw
 let e₂:Fin (min q (min a.t (a.j/2))+1) :=⟨e 2,by
  apply Kz
  simp only [Pr]
  omega⟩
 let e₁:Fin (min (q-e₂.val) (a.j - 2*e₂.val)+1) :=⟨e 1,by
  apply Kz
  simp only [Pr,e₂]
  omega⟩
 refine ⟨⟨e₂,e₁⟩,?_⟩
 ext i
 fin_cases i <;> simp [pG,e₂,e₁]
 omega
private theorem exponent_injective (a :t8) (q:ℕ) :
  qm (pG a q) := by
 rintro ⟨i,j⟩ ⟨i',j'⟩ h
 have hi:=G4 h 2
 have hj:=G4 h 1
 simp [pG] at hi hj
 have he :i=i' := yU hi
 subst i'
 exact ov (Sigma.mk i) (yU hj)
private def aQN (a :t8) (q:ℕ) :
  Test a q ≃ (Fin (a.b+a.j - q)×Slot a q) := by
 apply (Fintype.equivFinOfCardEq ?_).symm
 simp only [Fintype.card_prod,Fintype.card_sigma,PA,ay8]
 rw [Fin.sum_univ_eq_sum_range (fun e :ℕ=>min (q-e) (a.j - 2*e)+1)]
private abbrev part {R:Type*} [ox R] (q:ℕ) :
  qU R →ₗ[R] qU R :=
 MvPolynomial.homogeneousComponent q
private theorem bCX {R:Type*} [ox R] (q:ℕ) (G:qU R) (e :Exp) :
  (part q G).coeff e=if cV e=q then G.coeff e else 0:= by
 rw [MvPolynomial.coeff_homogeneousComponent,Up,LO]
 simp [cV,Nat.add_assoc]
private theorem eKE {R:Type*} [ox R] (t:R) (q:ℕ) (G:qU R) :
    part q (qJ t G)=qJ t (part q G) := by
  classical
  induction G using VO with
  | add P Q hP hQ=>simp [hP,hQ]
  | monomial d r =>
      have hmono (P:qU R) (hP : ∀ e∈P.support,cV e=cV d) :
          part q P=if cV d=q then P else 0:= by
        apply LP
        intro e
        rw [bCX]
        by_cases he :e∈P.support
        · rw [hP e he]
          split <;> simp_all
        · split_ifs <;> simp [MvPolynomial.notMem_support_iff.mp he]
      have hd (e :Exp) (he :e∈(xu d r).support) :cV e=cV d :=
        ov cV (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he))
      rw [hmono _ hd,hmono]
      · split <;> simp
      · intro e he
        obtain ⟨f,hf,h,_⟩:=bB4 _ _ he
        exact h.trans (hd _ hf)
private theorem bKj {a :t8} {R:Type*} [ox R] {q:ℕ} {G:qU R}
  (hG : ∀ e∈G.support,admissible a e) {e :Exp} (he :e∈(part q G).support) :
  cV e=q∧weight e≤a.j∧e 2≤a.t:= by
 rw [Dv,bCX] at he
 split at he
 next h=>exact ⟨h,(hG _ (MvPolynomial.mem_support_iff.mpr he)).2⟩
 next=>contradiction
private def term {R:Type*} [ox R] (a :t8) (q:ℕ) (c:abE a q) :qU R[X] :=
 xu (pG a q c.2) (nq ^c.1.val)
private def trunc {R:Type*} [ox R] (a :t8) (q:ℕ) (G:qU R[X]) :qU R[X] :=
 ∑ c:abE a q,mD (lV ((G.coeff (pG a q c.2)).coeff c.1.val)) *
   term a q c
private theorem dMD {R:Type*} [ox R] {a :t8} {q:ℕ} (G:qU R[X])
    (e :Exp) (n:ℕ) (hn:n<a.b+a.j)
    (hG:G.coeff e≠0 → ∃ s :Slot a q,pG a q s=e) :
    ((trunc a q G).coeff e).coeff n=(G.coeff e).coeff n:= by
  classical
  simp only [trunc,term,RC,In,
    Gr,Av,Iw]
  by_cases he : ∃ s :Slot a q,pG a q s=e
  · obtain ⟨s,rfl⟩:=he
    rw [Qw (⟨⟨n,hn⟩,s⟩:abE a q)]
    · simp
    · rintro ⟨k,f⟩ _ hne
      by_cases hf :f=s
      · subst f
        have hk :n≠k.val := by
          intro h
          exact hne (Prod.ext (yU h.symm) rfl)
        simp [Polynomial.coeff_X_pow,hk]
      · have hne' := (exponent_injective a q).ne hf
        simp [hne']
    · simp
  · have hz :G.coeff e=0:= by
      by_contra h
      exact he (hG h)
    rw [hz,wA]
    apply Pf
    intro c _
    have hne :pG a q c.2≠e := fun h=>he ⟨c.2,h⟩
    simp [hne]
private theorem eOR {R:Type*} [ox R] {a :t8} {q:ℕ} (G:qU R[X])
   (hG : ∀ e∈G.support,cV e=q∧weight e≤a.j∧e 2≤a.t)
   (e :Exp) (i:Fin (a.b+a.j - q)) :
   pQ q e i.val G=pQ q e i.val (trunc a q G) := by
 have hcoeff (f :Exp) (n:ℕ) (hn:n<a.b+a.j) :
     ((trunc a q G).coeff f).coeff n=(G.coeff f).coeff n:= by
   apply dMD _ _ _ hn
   intro hf
   obtain ⟨hg,hw,ht⟩:=hG f (MvPolynomial.mem_support_iff.mpr hf)
   exact cp5 a q f hg hw ht
 have hdiv :mD ((nq:R[X])^(a.b+a.j))∣G - trunc a q G:= by
   rw [Gi]
   intro f
   rw [Polynomial.X_pow_dvd_iff]
   intro n hn
   simp [hcoeff f n hn]
 have himg:=map_dvd (qJ (nq:R[X])) hdiv
 rw [bWf,qG,Gi] at himg
 unfold pQ
 split
 · exact (hcoeff e _ (by have :=i.isLt; omega)).symm
 · have h:=(Polynomial.X_pow_dvd_iff.mp (himg e)) (q+i.val)
     (by have :=i.isLt; omega)
   simpa [sub_eq_zero] using h
private theorem eOO {R:Type*} [ox R] {a :t8} {q:ℕ}
  (G:qU R[X]) (e :Exp) (i:ℕ) :
  pQ q e i (trunc a q G) = ∑ c:abE a q,
    ((G.coeff (pG a q c.2)).coeff c.1.val)*pQ q e i (term a q c) := by
 by_cases h:i<weight e <;>
  simp [pQ,h,trunc,vG,nI,In,
    Gr,Av]
private theorem eOQ (a :t8) (q:ℕ) (c:abE a q) (e :Exp) (i:ℕ) :
   pQ (R:=kS) q e i (term a q c) =
     cy ao kS (pQ q e i (term a q c)) := by
 let f :=t7 (cy ao kS)
 have hterm :p7 f (term a q c)=term a q c:= by simp [term,f]
 have himg:p7 f (qJ nq (term a q c)) =
     qJ nq (term a q c) := by
   rw [cZk,hterm]
   simp [f]
 by_cases h:i<weight e
 · simp only [pQ,wB h]
   rw [← hterm,F9]
   simp [f,vj]
 · simp only [pQ,vk h]
   rw [← himg,F9]
   simp [f,vj]
theorem proof :aFN.c1 := by
  classical
  intro a α
  let L:=a.b+a.j
  let F:=MvPolynomial.mapEquiv (Fin 3)
    (G3 (cy ao kS α)).toRingEquiv
  have hF (G:Lq) (e :Exp) :
      (F G).coeff e=(G.coeff e).taylor (cy ao kS α) := by
    exact F9
      (G3 (cy ao kS α)).toRingEquiv.toRingHom G e
  have hX: (G3 (cy ao kS α)) (O8 α) =
      Polynomial.X:= by
    change u8 (cy ao kS α) (O8 α)= _
    simp [O8]
  refine ⟨fun q i c =>
    let es :=aQN a q.val i
    pQ q.val (pG a q.val es.2) es.1.val (term a q.val c),?_⟩
  intro G hG
  have hcap (e :Exp) (he :e∈(F G).support) :admissible a e := by
    apply hG e
    rw [Dv,hF] at he
    exact MvPolynomial.mem_support_iff.mpr (fun h=>he (by simp [h]))
  have htranslated (H :Lq) :F (qJ (O8 α) H) =
      qJ nq (F H) := by
    simpa [F,hX] using cZk
      (G3 (cy ao kS α)).toRingEquiv.toRingHom
      (O8 α) H
  rw [← FR F,p6,htranslated]
  have hpow:F (mD (O8 α))=mD (nq:kS[X]) := by
    simpa [F] using ov (mD (σ:=Fin 3)) hX
  rw [hpow,← p6]
  have hgrade (q:Fin (a.b+1)) (e :Exp) (he :e∈(part q.val (F G)).support) :
      cV e=q.val∧q.val+weight e≤L:= by
    obtain ⟨hg,hw,_⟩:=bKj hcap he
    exact ⟨hg,Nat.add_le_add (Nat.le_of_lt_succ q.isLt) hw⟩
  have hprobes (q:Fin (a.b+1)) :
      mD ((nq:kS[X])^L) ∣
          part q.val (qJ nq (F G)) ↔
        ∀ i:Test a q.val,
          pQ q.val (pG a q.val (aQN a q.val i).2)
            (aQN a q.val i).1.val (part q.val (F G))=0:= by
    rw [eKE,eiP _ _ _ (hgrade q) (by have :=q.isLt; omega)]
    constructor
    · intro h i
      exact h _ _ (aQN a q.val i).1.isLt
    · intro h e i hi
      let P:=part q.val (F G)
      by_cases he : ∃ s :Slot a q.val,pG a q.val s=e
      · obtain ⟨s,rfl⟩:=he
        simpa using h ((aQN a q.val).symm (⟨i,hi⟩,s))
      · have hP:P.coeff e=0:= by
          apply MvPolynomial.notMem_support_iff.mp
          intro hm
          obtain ⟨hg,hw,ht⟩:=bKj hcap hm
          exact he (cp5 a q.val e hg hw ht)
        have hA: (qJ nq P).coeff e=0:= by
          apply MvPolynomial.notMem_support_iff.mp
          intro hm
          obtain ⟨d,hd,hg,hw,ht⟩:=bB4 _ _ hm
          obtain ⟨hg',hw',ht'⟩:=bKj hcap hd
          exact he (cp5 a q.val e (hg.trans hg') (hw.trans hw') (ht.trans ht'))
        change pQ q.val e i P=0
        simp [pQ,hP,hA]
  have hdot (q:Fin (a.b+1)) (i:Test a q.val) :
      pQ q.val (pG a q.val (aQN a q.val i).2)
        (aQN a q.val i).1.val (part q.val (F G)) =
          dot a α q.val (fun c=>pQ q.val (pG a q.val (aQN a q.val i).2)
            (aQN a q.val i).1.val (term a q.val c)) G:= by
    rw [eOR _ (fun _ he=>bKj hcap he),eOO,dot]
    apply t4 rfl
    intro c _
    rw [eOQ,bCX,gsR a q.val c.2,wB rfl,hF,bfj,t3]
  have hparts :
      mD ((nq:kS[X])^L)∣qJ nq (F G) ↔
        ∀ q:Fin (a.b+1),mD ((nq:kS[X])^L) ∣
          part q.val (qJ nq (F G)) := by
    simp only [Gi ,bCX]
    constructor
    · intro h q e
      split
      · exact h e
      · exact dvd_zero _
    · intro h e
      by_cases he :e∈(qJ nq (F G)).support
      · obtain ⟨d,hd,hg,_⟩:=bB4 _ _ he
        have hb:cV e≤a.b:=hg.le.trans (hcap d hd).1
        simpa using h ⟨cV e,Kz hb⟩ e
      · rw [MvPolynomial.notMem_support_iff.mp he]
        exact dvd_zero _
  rw [hparts]
  simp_rw [hprobes,hdot]
end
end Sy
end
section
namespace cxR
noncomputable section
open aR jA NR aFO Polynomial
open scoped Polynomial BigOperators
private abbrev axU:=nX (Fin 3) I6[X]
private def aft:ao →+* I6 :=
 Polynomial.C.comp (lV:ao →+* ao[X])
private def It (ε:ao) :I6 →+* kS :=
 (cy ao[X] kS).comp (Wv ε)
private def RS (ε:ao) :axU →+* Lq :=
 p7 (t7 (It ε))
@[simp] private theorem cRO (ε c:ao) :
   It ε (aft c)=cy ao kS c:= by
  rw [zi ao ao[X] kS]
  simp [It,aft,Wv]
@[simp] private theorem gPY (ε:ao) :
   (It ε).comp aft=cy ao kS :=
  SD (cRO ε)
private def bqk (H :ao[X]) :I6[X] :=
 H.map aft+Polynomial.C (lV nq)
private theorem edy {H :ao[X]} (hm:H.Monic) (hp:0<H.natDegree) :
  (bqk H).Monic:= by
 apply (hm.map aft).add_of_left
 exact degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp (by
  rwa [hm.natDegree_map]))
@[simp] private theorem cSS (H :ao[X]) (ε:ao) :
    (bqk H).map (It ε)=jH (Q8 H ε) := by
  have h:It ε (lV nq) =
      cy ao kS ε:= by
    rw [zi ao ao[X] kS]
    simp [It,Wv]
  simp [bqk,jH,Q8,Rm,h]
private def abf {A:Type*} [ox A] (a :A) :nX (Fin 3) A[X] :=
 mD (lV a)
@[simp] private theorem bGz (ε:ao) (a :I6) :
   RS ε (abf a)=abf (It ε a) := by
  simp [RS,abf]
private def bqV {A:Type*} [ox A] (B:A[X]) (i:Fin 3) :
   nX (Fin 3) A[X] :=
 ∑ j:Fin 3,if j.val≤ i.val then
   mD (qM (i.val - j.val) B)*lz j
 else 0
@[simp] private theorem eag (ε:ao) (B:I6[X]) (i:Fin 3) :
   RS ε (bqV B i)=bqV (B.map (It ε)) i:= by
  simp [RS,bqV,apply_ite,← G8]
private def abg (H :ao[X]) (R:kS[X]) :jK →+* Lq :=
 vl
  (MvPolynomial.C.comp (t7 (cy ao kS)))
  (fun i:mA=>i.elim
    (abf (cy ao[X] kS nq))
    (fun j=>mD (qM j.val R)+bqV (jH H) j))
private theorem fW3 (H :ao[X]) (R:kS[X]) (F:jK) :
 abg H R F=amA H R F:=rfl
private theorem cRP (ε:ao) {D:I6} (hD:Wv ε D ≠0) :
  It ε D ≠0:= by
 intro hz
 exact hD ((ze ao[X] kS)
  (hz.trans (qz (cy ao[X] kS)).symm))
private theorem fWU (N :I6[X]) (D:I6) (ε:ao) (i:ℕ) :
  qM i (awc N D ε) =
    lV ((It ε D)⁻¹)*(qM i N).map (It ε) := by
 simp only [awc,ahH,Rm,It,pC,
  ← WX ,map_smul,G8]
private theorem fTM {d:kS} (hd:d≠0) (p:kS[X]) :
  abf d*(mD (lV d⁻¹*p) :Lq)=mD p:= by
 have hc:lV d*(lV d⁻¹*p)=p:= by
  rw [← sS ,← Polynomial.C_mul,mul_inv_cancel₀ hd,Polynomial.C_1,Au]
 calc
  _=(mD (lV d*(lV d⁻¹*p)) :Lq) :=
    (S1 (σ:=Fin 3)).symm
  _ = _:=ov (mD:kS[X] →+* Lq) hc
private theorem dLE (H :ao[X]) (N :I6[X]) (D:I6) (i:mA) :
    ∃ (r :ℕ) (P:axU),∀ ε,Wv ε D ≠0 →
      RS ε P=(abf (It ε D))^r *
        abg (Q8 H ε) (awc N D ε) (lz i) := by
  cases i with
  | none =>
    refine ⟨0,abf nq,fun ε _ => ?_⟩
    simp [abg,It,Wv]
  | some i =>
    refine ⟨1,mD (qM i.val N) +
      abf D *bqV (bqk H) i,fun ε hD => ?_⟩
    simp only [oK,nI,bGz,eag,
      cSS,pow_one,abg,y5 ,Option.elim_some,
      fWU,mul_add]
    congr 1
    simpa only [RS,C5 ,xW,S1] using
      (fTM (cRP ε hD)
        ((qM i.val N).map (It ε))).symm
private theorem dLC (H :ao[X]) (N :I6[X]) (D:I6) (F:jK) :
    ∃ (r :ℕ) (P:axU),∀ ε,Wv ε D ≠0 →
      RS ε P=(abf (It ε D))^r *
        abg (Q8 H ε) (awc N D ε) F:= by
  induction F using JM with
  | C p =>
    refine ⟨0,mD (p.map aft),fun ε _ => ?_⟩
    simp [RS,abg,Rm]
  | add p q hp hq =>
    obtain ⟨r,P,hP⟩:=hp
    obtain ⟨s,Q,hQ⟩:=hq
    refine ⟨r+s,abf D^s*P+abf D^r*Q,fun ε hD => ?_⟩
    simp only [oK,nI,p6,bGz,hP ε hD,hQ ε hD,pow_add,mul_add]
    rw [← sS ,← sS ,t3 (abf (It ε D)^s)
      (abf (It ε D)^r)]
  | mul_X p i hp =>
    obtain ⟨r,P,hP⟩:=hp
    obtain ⟨s,Q,hQ⟩:=dLE H N D i
    refine ⟨r+s,P*Q,fun ε hD => ?_⟩
    simp only [nI,hP ε hD,hQ ε hD,pow_add]
    exact mul_mul_mul_comm _ _ _ _
private theorem dLs (H :ao[X]) (N :I6[X]) (D:I6)
    {m:ℕ} (F:Fin m→jK) :
    ∃ (r :ℕ) (P:Fin m→axU),∀ ε,Wv ε D ≠0 → ∀ j,
      RS ε (P j)=(abf (It ε D))^r *
        abg (Q8 H ε) (awc N D ε) (F j) := by
  classical
  choose r P hP using fun j=>dLC H N D (F j)
  let b:=Finset.univ.sup r
  refine ⟨b,fun j=>abf D^(b - r j)*P j,fun ε hD j => ?_⟩
  have hj:r j≤b:=Finset.le_sup (zS j)
  rw [nI,p6,bGz,hP j ε hD,← sS ,← pow_add,
    HZ hj]
private def combine {m:ℕ} (P:Fin m→axU) (v :Fin m→ao) :axU :=
 ∑ j,abf (aft (v j))*P j
private theorem fW4 (H :ao[X]) (R:kS[X]) (a :ao)
   (F:jK) :
   abg H R (a•F)=abf (cy ao kS a)*abg H R F:= by
 have hs :a•F=mD (lV a)*F:= by
   rw [Algebra.smul_def,zi ao ao[X] jK,
     zk,Polynomial.algebraMap_eq]
 rw [hs,nI]
 simp only [abg,z7,pC,
   xW,RJ,abf]
private theorem eac {H :ao[X]} {N :I6[X]} {D:I6}
   {ε:ao} {m r :ℕ} (P:Fin m→axU) (F:Fin m→jK)
   (hP : ∀ j,RS ε (P j)=abf (It ε D)^r *
     abg (Q8 H ε) (awc N D ε) (F j)) (v :Fin m→ao) :
   RS ε (combine P v)=abf (It ε D)^r *
     abg (Q8 H ε) (awc N D ε) (∑ j,v j•F j) := by
 rw [combine,vG,vG,Dz]
 apply t4 rfl
 intro j _
 rw [nI,bGz,cRO,hP j,fW4]
 exact Pv _ _ _
private abbrev by3:=(Fin 3 →₀ ℕ)×ℕ×ℕ
private def entry (B:I6[X]) (P:axU) (u:by3) :ao[X] :=
 (((P.coeff u.1) %ₘ B).coeff u.2.1).coeff u.2.2
private def aD (B:I6[X]) (P:axU) :oz by3:= by
 classical
 exact P.support.biUnion fun a =>
  ((P.coeff a) %ₘ B).support.biUnion fun i =>
    (((P.coeff a) %ₘ B).coeff i).support.image fun j=>(a,i,j)
private theorem ezZ {B:I6[X]} {P:axU} {u:by3}
  (he :entry B P u≠0) :u∈aD B P:= by
 classical
 obtain ⟨a,i,j⟩:=u
 have hi: ((P.coeff a) %ₘ B).coeff i≠0:= by
  intro h
  exact he (by simp [entry,h])
 have ha :P.coeff a≠0:= by
  intro h
  exact hi (by simp [h])
 exact Finset.mem_biUnion.mpr ⟨a,MvPolynomial.mem_support_iff.mpr ha,
  Finset.mem_biUnion.mpr ⟨i,Polynomial.mem_support_iff.mpr hi,
    Finset.mem_image.mpr ⟨j,Polynomial.mem_support_iff.mpr he,rfl⟩⟩⟩
private theorem cMr {m:ℕ} (B:I6[X]) (P:Fin m→axU)
  (v :Fin m→ao) (u:by3) :
  entry B (combine P v) u = ∑ j,lV (v j)*entry B (P j) u:= by
 have h :
    (∑ j,lV (aft (v j))*(P j).coeff u.1) %ₘ B =
    ∑ j,lV (aft (v j))*((P j).coeff u.1 %ₘ B) := by
  simp only [← WX ,← modByMonicHom_apply,vG,map_smul]
 simp only [entry,combine,RC,In,abf,h]
 simp only [
  Gr,Av,aft,pC]
private theorem ead (B:I6[X]) (hB:B.Monic) (P:axU)
    (ε:ao) :
    mD (B.map (It ε))∣RS ε P ↔
      ∀ u,vh ε (entry B P u)=0:= by
  rw [Gi]
  have hcoeff (a :Fin 3 →₀ ℕ) :
      B.map (It ε)∣(RS ε P).coeff a ↔
        ∀ i j,vh ε (entry B P (a,i,j))=0:= by
    rw [← modByMonic_eq_zero_iff_dvd (hB.map (It ε))]
    simp only [RS,F9,xW,← map_modByMonic _ hB,
      Polynomial.ext_iff,vj,wA,It,pC,
      map_eq_zero_iff _ (ze ao[X] kS),Wv]
    rfl
  exact ⟨fun h u=>(hcoeff u.1).mp (h u.1) u.2.1 u.2.2,
    fun h a=>(hcoeff a).mpr (fun i j=>h (a,i,j))⟩
theorem proof :aFO.c2 := by
  classical
  intro H hm hp N D n m F
  obtain ⟨r,P,hP⟩:=dLs H N D F
  let B:=bqk H^n
  have hB:B.Monic:=(edy hm hp).pow n
  let T:=Finset.univ.biUnion fun j:Fin m=>aD B (P j)
  let e :=T.equivFin.symm
  let M:Matrix (Fin T.card) (Fin m) ao[X] := fun i j=>entry B (P j) (e i)
  refine ⟨T.card,M,fun ε hD v => ?_⟩
  have htest (i:Fin T.card) :
      ((M.map (vh ε)).mulVecLin v) i=vh ε (entry B (combine P v) (e i)) := by
    change (∑ j,vh ε (entry B (P j) (e i))*v j)= _
    rw [cMr,vG]
    apply t4 rfl
    intro j _
    rw [nI]
    change _=(lV (v j)).eval ε*_
    rw [eval_C,t3]
  have hmatrix : (M.map (vh ε)).mulVecLin v=0 ↔
      ∀ u,vh ε (entry B (combine P v) u)=0:= by
    constructor
    · intro hz u
      by_cases hu:u∈T
      · let i:=T.equivFin ⟨u,hu⟩
        have hi:=congrFun hz i
        rw [htest] at hi
        simpa [i,e] using hi
      · have hcol (j:Fin m) :entry B (P j) u=0 :=
          not_ne_iff.mp fun h=>hu (Finset.mem_biUnion.mpr
            ⟨j,zS _,ezZ h⟩)
        simp [cMr,hcol]
    · intro hz
      funext i
      exact (htest i).trans (hz (e i))
  have hunit :IsUnit (abf (It ε D)^r) :=
    (((isUnit_iff_ne_zero.mpr (cRP ε hD)).map
      (lV:kS →+* kS[X])).map
      (mD:kS[X] →+* Lq)).pow r
  rw [hmatrix,← ead B hB,eac P F (hP ε hD),
    hunit.dvd_mul_left]
  simp only [B,Polynomial.map_pow,cSS,p6,fW3]
end
end cxR
end
section
namespace cxO
noncomputable section
open aR Rj Finset MvPolynomial
open scoped BigOperators
private def HE (u:ℕ) :oz (ℕ×ℕ) :=
 ((range (u+1)).product (range (u+1))).filter fun p=>p.2+2*p.1≤u
private theorem a5N (u:ℕ) (p:ℕ×ℕ) :
  p∈HE u↔p.2+2*p.1≤u:= by
 simp only [HE,product_eq_sprod,zm,FV,mem_range]
 omega
private theorem dFC (u:ℕ) :
    ((HE u).card:ℤ)=((u:ℤ)+2)^2/4 := by
  let m:=u/2
  let n:=u - m
  have hmn:m≤n∧n≤ m+1∧u=m+n:= by
    dsimp [m,n]
    omega
  have hc: (HE u).card=(m+1)*(n+1) := by
    rw [← card_range (m+1),← card_range (n+1),← card_product]
    apply card_nbij'
      (fun p=>if p.1+p.2≤n then (p.1,p.1+p.2) else (u+1-(p.1+p.2),p.1))
      (fun p=>if p.1≤p.2 then (p.1,p.2 - p.1) else (p.2,u+1 - p.1 - p.2))
    · rintro ⟨c,b⟩ h
      simp only [qy ,a5N] at h
      simp only [qy ,FV,mem_range]
      split <;> dsimp <;> omega
    · rintro ⟨x,y⟩ h
      simp only [qy ,FV,mem_range] at h
      simp only [qy ,a5N]
      split <;> dsimp <;> omega
    · rintro ⟨c,b⟩ h
      simp only [qy ,a5N] at h
      by_cases hcb:c+b≤n
      · have hcc:c≤ c+b:= by omega
        simp [hcb,hcc]
      · have hcc : ¬ u+1-(c+b)≤ c:= by omega
        simp [hcb,hcc]
        omega
    · rintro ⟨x,y⟩ h
      simp only [qy ,FV,mem_range] at h
      by_cases hxy :x≤y
      · simp [hxy]
        omega
      · have hxy' : ¬ y+(u+1 - x - y)≤n:= by omega
        simp [hxy,hxy']
        omega
  simp only [hc,Nat.cast_mul,zg ,Nat.cast_one]
  have hu: (u:ℤ)=(m:ℤ)+n:= by omega
  have hn: (n:ℤ) - m=0∨(n:ℤ) - m=1 := by omega
  have hsq: ((n:ℤ) - m)^2=0∨((n:ℤ) - m)^2=1 := by
    rcases hn with hn | hn <;> simp [hn]
  have hsq' : ((u:ℤ)+2)^2 =
      4*((m+1 :ℤ)*(n+1))+((n:ℤ) - m)^2 := by
    rw [hu]
    ring
  omega
private def triangle (n:ℕ) :oz (Σ _:ℕ,ℕ) :=
 (range n).sigma fun i=>range (i+1)
private theorem b84 (n:ℕ) (p:Σ _:ℕ,ℕ) :
  p∈triangle n↔p.1<n∧p.2≤p.1 := by
 simp [triangle]
private theorem dFB (n:ℕ) :
  ((triangle n).card:ℤ)=sG n:= by
 simp only [triangle,card_sigma,card_range,Nat.cast_sum,zg ,Nat.cast_one]
 have h : ∀ k :ℕ,2*(∑ i∈range k,((i:ℤ)+1))=(k :ℤ)*(k+1) := by
  intro k
  induction k with
  | zero=>simp
  | succ k ih=>rw [sum_range_succ,Nat.cast_succ,mul_add,ih]; ring
 unfold sG
 have hn:=h n
 omega
private theorem dFs (d u:ℕ) (hu:u≤2*d) :
   ((HE u).filter fun p => ¬ p.1+p.2≤d).card=(triangle (u - d)).card:= by
 apply card_nbij'
   (fun p=>⟨u-(p.1+p.2),p.1⟩)
   (fun p=>(p.2,u - p.1 - p.2))
 · rintro ⟨c,b⟩ h
   simp only [qy ,zm,a5N] at h
   simp only [qy ,b84]
   omega
 · rintro ⟨i,c⟩ h
   simp only [qy ,b84] at h
   simp only [qy ,zm,a5N]
   omega
 · rintro ⟨c,b⟩ h
   simp only [qy ,zm,a5N] at h
   change (c,u-(u-(c+b)) - c)=(c,b)
   simp only [Prod.mk.injEq,true_and]
   omega
 · rintro ⟨i,c⟩ h
   simp only [qy ,b84] at h
   have hi:u-(c+(u - i - c))=i:= by omega
   change (⟨u-(c+(u - i - c)),c⟩:Σ _:ℕ,ℕ)=⟨i,c⟩
   rw [hi]
private def aEg (d:ℕ) (w:ℤ) :oz (ℕ×ℕ) :=
 if w<0 then ∅ else
  (HE (min w (2*(d:ℤ))).toNat).filter fun p=>p.1+p.2≤d
private theorem c0e (d:ℕ) (w:ℤ) (p:ℕ×ℕ) :
   p∈aEg d w↔p.1+p.2≤d∧(p.2 :ℤ)+2*p.1≤w:= by
 unfold aEg
 split
 · simp only [notMem_empty,false_iff]
   omega
 · rw [zm,a5N]
   omega
private theorem cEi (d:ℕ) (w:ℤ) :
   ((aEg d w).card:ℤ)=gd d w:= by
 by_cases hw:w<0
 · simp [aEg,gd,hw]
 let u:=(min w (2*(d:ℤ))).toNat
 have hu: (u:ℤ)=min w (2*(d:ℤ)) := by dsimp [u]; omega
 have hud:u≤2*d:= by omega
 have hd: ((u - d:ℕ) :ℤ)=max 0 ((u:ℤ) - d) := by omega
 have h:=card_filter_add_card_filter_not (s :=HE u) (fun p=>p.1+p.2≤d)
 rw [dFs d u hud] at h
 have h' := ov (fun n:ℕ=>(n:ℤ)) h
 simp only [zg ,dFB,dFC,hd] at h'
 simp only [aEg,gd,vk hw]
 change (((HE u).filter fun p=>p.1+p.2≤d).card:ℤ) =
   (min w (2*(d:ℤ))+2)^2/4 - sG (max 0 (min w (2*(d:ℤ)) - d))
 rw [← hu]
 omega
private def vo (d:ℕ) (g:ℤ) :oz (ℕ×ℕ) :=
 aEg d 2300 \ aEg d (min 2300 (-g - 1))
private theorem eAh (d:ℕ) (g:ℤ) (p:ℕ×ℕ) :
  p∈vo d g ↔
    p.1+p.2≤d ∧ -g≤(p.2 :ℤ)+2*p.1∧p.2+2*p.1≤2300:= by
 simp only [vo,mem_sdiff,c0e]
 omega
private theorem dFD (q:ℕ) (g:ℤ) :
  ((vo (iO q) g).card:ℤ)=Bb q g:= by
 have hs :aEg (iO q) (min 2300 (-g - 1))⊆aEg (iO q) 2300:= by
  intro p hp
  rw [c0e] at hp ⊢
  omega
 have hc:=card_sdiff_add_card_eq_card hs
 have h:=ov (fun n:ℕ=>(n:ℤ)) hc
 simp only [zg] at h
 change ((vo (iO q) g).card:ℤ) +
  ((aEg (iO q) (min 2300 (-g - 1))).card:ℤ) =
  ((aEg (iO q) 2300).card:ℤ) at h
 rw [cEi,cEi] at h
 exact eq_sub_of_add_eq h
private def exponent (d:ℕ) (p:ℕ×ℕ) :adf :=
 Finsupp.equivFunOnFinite.symm ![d-(p.1+p.2),p.2,p.1]
private theorem exponent_injective (d:ℕ) :qm (exponent d) := by
 intro p r h
 apply Prod.ext
 · simpa [exponent] using ov (fun e :adf=>e 2) h
 · simpa [exponent] using ov (fun e :adf=>e 1) h
private theorem eLR (e :adf) :
  e.weight (fun _=>1)=e 0+e 1+e 2 := by
 simp [IU,LO,zc,add_assoc]
private theorem eLT (e :adf) :
  e.weight Fin.val=e 1+2*e 2 := by
 simp [IU,LO,zc,Nat.mul_comm]
private theorem bnD (q:ℕ) (g:ℤ) :
   (↑((vo (iO q) g).image (exponent (iO q))) :Set adf) =
     cbQ q g:= by
 ext e
 simp only [qy ,mem_image,eAh]
 change _↔e.weight (fun _=>1)=iO q ∧
   -g≤(e.weight Fin.val :ℤ)∧e.weight Fin.val≤2300∧e 2≤1150
 rw [eLR,eLT]
 constructor
 · rintro ⟨p,hp,rfl⟩
   simp [exponent]
   omega
 · intro he
   refine ⟨(e 2,e 1),?_,?_⟩
   · dsimp
     omega
   · ext j
     fin_cases j <;> simp [exponent]
     omega
private theorem gte (q:ℕ) (g:ℤ) :
  (R9 ao (aqz q g) :ℤ)=Bb q g:= by
 unfold aqz
 rw [← bnD q g,finrank_restrictSupport_finset,
  Yo _ (exponent_injective _),dFD]
theorem proof :Rj.c1 := by
 intro q _ k _
 exact (gte q (offset k)).le
end
end cxO
end
section
namespace bjA
noncomputable section
open aR dN vS Dr Kd MvPolynomial
private theorem Zy {ι σ:Type}
   {w:σ→ι→ℕ} {s :ι→ℕ} {L:nX σ oq}
   (hL:Ar w L s) (f :nX σ oq) (a :ι→ℕ) :
   yJ w (a+s) (L*f) =
     L*yJ w a f := by
 classical
 ext e
 rw [Vl,GF,GF,Finset.ite_sum_zero]
 apply t4 rfl
 rintro ⟨u,v⟩ huv
 rw [Vl]
 by_cases hu:L.coeff u=0
 · simp [hu]
 · have hw:Du w e=a+s↔Du w v=a := by
     rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp huv,oK,hL hu,vw s,add_right_cancel_iff]
   simp only [hw]
   split <;> simp_all
private theorem dOA {ι σ:Type}
  {w:σ→ι→ℕ} {s :ι→ℕ} {L:nX σ oq}
  (hL:Ar w L s) (f :nX σ oq) (b:ι→ℕ)
  (hb : ¬ ∃ a,b=a+s) :
  yJ w b (L*f)=0:= by
 classical
 apply weightedHomogeneousComponent_eq_zero'
 intro e he hdeg
 rw [Dv,GF] at he
 obtain ⟨⟨u,v⟩,huv,hc⟩:=Finset.exists_ne_zero_of_sum_ne_zero he
 have hu:L.coeff u≠0:= fun h=>hc (by simp [h])
 apply hb
 refine ⟨Du w v,?_⟩
 rw [← hdeg,← Finset.HasAntidiagonal.mem_antidiagonal.mp huv,oK,hL hu,vw]
private theorem cT5 {ι σ:Type} [Fintype ι] [Nq ι]
   (slot:σ→ι) {I:lI (nX σ oq)} {L:nX σ oq}
   {s :ι→ℕ} (hI:aiD slot I) (hL:Ar (step ∘ slot) L s) :
   aiD slot (I ⊔ c9 {L}) := by
 intro f hf b
 rw [sup_comm,Zt] at hf
 obtain ⟨g,j,hj,rfl⟩:=hf
 rw [oK,t3 g L]
 apply Ideal.add_mem _
 · by_cases hb : ∃ a,b=a+s
   · obtain ⟨a,rfl⟩:=hb
     rw [Zy hL]
     exact C9 (Ideal.mem_span_singleton.mpr ⟨_,rfl⟩)
   · rw [dOA hL g b hb]
     exact Ideal.zero_mem _
 · exact Vq (hI j hj b)
private theorem cR7 {ι σ:Type} [Fintype ι] [Nq ι] [Finite σ]
   (slot:σ→ι) (a :ι→ℕ) :
   v8 oq (Kc oq (step ∘ slot) a) := by
 classical
 let _:=Fintype.ofFinite σ
 have hd (e :σ →₀ ℕ) :e.degree = ∑ i,Du (step ∘ slot) e i:= by
   simp only [Up,IU,Finset.sum_apply,
     SU,Pi.smul_apply]
   rw [N0]
   apply t4 rfl
   intro x _
   simp [step,Pi.single_apply,mul_ite]
 have :=((Finsupp.finite_of_degree_le (∑ i,a i)).subset
   (show {e | Du (step ∘ slot) e=a} ⊆ _ from
     fun e he=>le_of_eq ((hd e).trans (ov _ he)))).to_subtype
 rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
 exact Module.Finite.of_basis (basisRestrictSupport oq _)
private theorem cUN {ι σ:Type} [Fintype ι] [Nq ι] [Finite σ]
    (slot:σ→ι) (I K:lI (nX σ oq)) (L:nX σ oq)
    (a s :ι→ℕ) (hI:aiD slot I) (hL:Ar (step ∘ slot) L s)
    (hcolon : ∀ f,L*f∈I↔f∈K) :
    lO slot (I ⊔ c9 {L}) (a+s)+lO slot K a=lO slot I (a+s) := by
  classical
  let w:=step ∘ slot
  let S:=Kc oq w a
  let T:=Kc oq w (a+s)
  let B:=I ⊔ c9 {L}
  have hIB:I≤B:=yl
  let V (J:lI (nX σ oq)) :=
    T.map (Sd oq J).toLinearMap
  let src :=(Sd oq K).toLinearMap.domRestrict S
  let multiply :=(Sd oq I).toLinearMap.comp (LinearMap.mulLeft oq L)
  let mul :S →ₗ[oq] V I :=
    (multiply.domRestrict S).codRestrict (V I) (fun g=> by
      have hg:Ar w (g:nX σ oq) a :=g.2
      have hprod:=hL.mul hg
      rw [vw s a] at hprod
      exact Submodule.mem_map.mpr ⟨L*g,hprod,rfl⟩)
  let proj:V I →ₗ[oq] V B :=
    ((Ideal.Quotient.factorₐ oq hIB).toLinearMap.domRestrict (V I)).codRestrict (V B)
      (fun x=> by
        obtain ⟨f,hf,hfx⟩:=Submodule.mem_map.mp x.2
        exact Submodule.mem_map.mpr ⟨f,hf,by
          change n5 B f=Ww hIB x.val
          rw [← hfx]
          rfl⟩)
  have hsurj:zpX proj:= by
    intro x
    obtain ⟨f,hf,hfx⟩:=Submodule.mem_map.mp x.2
    exact ⟨⟨n5 I f,Submodule.mem_map.mpr ⟨f,hf,rfl⟩⟩,wY hfx⟩
  have hker :EK mul=EK src := by
    ext g
    rw [Y4 ,Y4]
    constructor
    · intro hg
      have hz :n5 I (L*(g:nX σ oq))=0 :=
        ov Subtype.val hg
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hcolon _).mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    · intro hg
      exact wY (Ideal.Quotient.eq_zero_iff_mem.mpr ((hcolon _).mpr
        (Ideal.Quotient.eq_zero_iff_mem.mp hg)))
  have hrange :LinearMap.range mul=EK proj:= by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      apply LinearMap.mem_ker.mpr
      apply wY
      change n5 B (L*(g:nX σ oq))=0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (C9 (Ideal.mem_span_singleton.mpr ⟨_,rfl⟩))
    · intro hx
      obtain ⟨f,hf,hfx⟩:=Submodule.mem_map.mp x.2
      have hx0:Ww hIB x.val=0 :=
        ov Subtype.val (LinearMap.mem_ker.mp hx)
      rw [← hfx] at hx0
      have hfB:f∈B:=Ideal.Quotient.eq_zero_iff_mem.mp hx0
      change f∈I ⊔ c9 {L} at hfB
      rw [sup_comm,Zt] at hfB
      obtain ⟨g,j,hj,hgj⟩:=hfB
      let g' := yJ w a g
      have he :=ov (yJ w (a+s)) hgj
      rw [oK,t3 g L,Zy hL,weightedHomogeneousComponent_eq_self hf] at he
      change L*g' + yJ w (a+s) j=f at he
      refine ⟨⟨g',weightedHomogeneousComponent_mem w g a⟩,wY ?_⟩
      change n5 I (L*g')=x.val
      change n5 I f=x.val at hfx
      rw [← hfx,← he,oK,Ideal.Quotient.eq_zero_iff_mem.mpr (hI j hj (a+s)),u5]
  let _:v8 oq S:=cR7 slot a
  let _:v8 oq T:=cR7 slot (a+s)
  let _:v8 oq (V I) :=Module.Finite.map _ _
  have hm:=mul.finrank_range_add_finrank_ker
  have hk :=src.finrank_range_add_finrank_ker
  rw [hrange,hker] at hm
  have hdim:R9 oq (EK proj) =
      R9 oq (LinearMap.range src) := by omega
  have hp:=proj.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,hdim] at hp
  dsimp only [src] at hp
  rw [LinearMap.range_domRestrict] at hp
  unfold lO
  exact_mod_cast hp
theorem proof :Kd.c6:= by
  classical
  intro ι _ _ fF i J D hD hreg
  dsimp only
  intro hI hI₂
  obtain ⟨L,hL,heL⟩:=exists_lift fF i D (dAn hD)
  obtain ⟨M,hM,heM⟩:=exists_lift fF i (D^2) (dAl hD)
  have hle :cut J (D^2)≤ cut J D:= by
    apply uJ yl
    apply Ideal.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    exact C9 (Ideal.mem_span_singleton.mpr ⟨D,pow_two D⟩)
  have :Finite (Kb fF) :=Oc
  refine ⟨HW fF J ⊔ c9 {M},HW fF (cut J (D^2)) ⊔ c9 {L},
    cT5 _ hI hM,cT5 _ hI₂ hL,?_,?_,?_,?_⟩
  · exact uJ (cDY fF yl)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (brQ heM (C9
        (xL _)))))
  · exact uJ (cDY fF hle)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (brQ heL (C9
        (xL _)))))
  · intro a
    exact cUN _ _ _ M a _ hI hM
      (cXP heM (gur J D hreg))
  · intro a
    exact cUN _ _ _ L a _ hI₂ hL
      (cXP heL (dS7 J D hreg))
end
end bjA
end
section
set_option maxSynthPendingDepth 8
namespace bjF
noncomputable section
open cu gT Polynomial
abbrev axC:=nX (Fin 1) FX
abbrev Fixed:=lJ (lJ axC)
private def aAi (i:Fin 2) :Fin 2 ≃ Fin 2 :=Equiv.swap i 0
private theorem co1 (i:Fin 2) :aAi i i=0 :=
 Equiv.swap_apply_left i 0
private def AV (i:Fin 2) :aZ ≃ₐ[FX] lJ axC :=
 (Mj FX (aAi i)).trans (Fa FX 1)
private theorem dc2 (i:Fin 2) (f :aZ) :
  (AV i f).natDegree=f.degreeOf i:= by
 change (Fa FX 1 (oy (aAi i) f)).natDegree= _
 rw [MvPolynomial.natDegree_finSuccEquiv,← co1 i]
 exact Xo (aAi i).injective i
private theorem co3 (i:Fin 2) (a :FX) :
  AV i (mD a)=lV (mD a) := by
 change Fa FX 1 (oy (aAi i) (mD a))= _
 rw [zt1,zyf,z7]
 rfl
private theorem bNH (i j:Fin 2) :
   AV i (lz j) =
     if j=i then nq else lV (lz 0) := by
 change Fa FX 1 (oy (aAi i) (lz j))= _
 rw [MvPolynomial.rename_X]
 by_cases h:j=i
 · subst j
   rw [wB rfl,co1,MvPolynomial.finSuccEquiv_X_zero]
 · have hj:aAi i j≠0:= by
     intro hz
     exact h ((aAi i).injective (hz.trans (co1 i).symm))
   have h1 :aAi i j=(0:Fin 1).succ:= by
     apply yU
     have hjv : (aAi i j).val≠0:= fun hz=>hj (yU hz)
     have hb:=(aAi i j).isLt
     change (aAi i j).val=1
     omega
   rw [vk h,h1,MvPolynomial.finSuccEquiv_X_succ]
private theorem goH (i:Fin 2) (f :aZ) :
   (Vy i f).map (AV i).toRingHom =
     u8 (nq:lJ axC) ((AV i f).map lV) := by
 let lhs :=(t7 (AV i).toRingHom).comp (Vy i)
 let rhs :=(taylorAlgHom (nq:lJ axC)).toRingHom.comp
   ((t7 (lV:axC →+* lJ axC)).comp
     (AV i).toRingHom)
 suffices h:lhs=rhs from oZ h f
 apply pU
 · intro a
   change (Vy i (mD a)).map (AV i).toRingHom =
     u8 _ ((AV i (mD a)).map lV)
   simp [Vy,co3]
 · intro j
   change (Vy i (lz j)).map (AV i).toRingHom =
     u8 _ ((AV i (lz j)).map lV)
   by_cases h:j=i
   · simp [Vy,bNH,h,vw]
   · simp [Vy,bNH,h]
private theorem goF (i:Fin 2) (r :ℕ) (f :aZ) :
  AV i ((Vy i f).coeff r)=qM r (AV i f) := by
 calc
  _=((Vy i f).map (AV i).toRingHom).coeff r :=(vj _ _).symm
  _ = _:= by rw [goH,taylor_coeff,G8 ,eval_map,eval₂_C_X]
private theorem bhI {A:Type*} [vZ A]
   (F:lJ (lJ A)) (i j:ℕ) :
   ((zd F).coeff i).coeff j=(F.coeff j).coeff i:= by
 induction F using FK with
 | add P Q hp hq=>simp [hp,hq]
 | monomial n P =>
   induction P using FK with
   | add P Q hp hq=>simp only [map_add,Polynomial.coeff_add,hp,hq]
   | monomial m c =>
     rw [Bivariate.swap_monomial_monomial]
     by_cases hi:m=i <;> by_cases hj:n=j <;> simp [Np,hi,hj]
def view (i:Fin 2) :Jet ≃+* lJ Fixed :=
  let inner :=((MO (AV i).toRingEquiv).trans
    (zd (R:=axC)).toRingEquiv)
  (MO inner).trans (zd (R:=lJ axC)).toRingEquiv
private theorem bPK (i:Fin 2) (F:Jet) (n j k :ℕ) :
  (((view i F).coeff n).coeff j).coeff k=(AV i ((F.coeff j).coeff k)).coeff n:= by
 let inner :=((MO (AV i).toRingEquiv).trans
  (zd (R:=axC)).toRingEquiv)
 change (((zd (F.map inner.toRingHom)).coeff n).coeff j).coeff k= _
 rw [bhI,vj]
 change ((zd ((F.coeff j).map (AV i).toRingHom)).coeff n).coeff k= _
 rw [bhI,vj]
 rfl
private theorem cGm {A B:Type*} [Semiring A] [Semiring B]
   (F:lJ A) (f :A → B) (h0:f 0=0) (n:ℕ) :
   (F.sum fun k c=>monomial k (f c)).coeff n=f (F.coeff n) := by
 classical
 rw [coeff_sum,P7,Qw n]
 · simp
 · intro k _ hkn
   simp [Np,hkn]
 · intro hn
   rw [notMem_support_iff.mp hn,h0,monomial_zero_right,wA]
private theorem coZ (i:Fin 2) (r :ℕ) (F:Jet) (j k :ℕ) :
   ((A5 i r F).coeff j).coeff k=(Vy i ((F.coeff j).coeff k)).coeff r := by
 unfold A5
 rw [cGm,cGm]
 · simp
 · simp
theorem bPL (i:Fin 2) (r :ℕ) (F:Jet) :
  view i (A5 i r F)=qM r (view i F) := by
 ext n j k :3
 rw [bPK,coZ,goF,hasseDeriv_coeff]
 simp only [hasseDeriv_coeff,coeff_natCast_mul,bPK]
theorem cvg (i:Fin 2) (F:Jet) (U:ℕ)
  (hbound : ∀ j k,((F.coeff j).coeff k).totalDegree≤U) :
  (view i F).natDegree≤U:= by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro n hn
 ext j k :2
 rw [bPK]
 simp only [wA]
 apply coeff_eq_zero_of_natDegree_lt
 rw [dc2]
 exact ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hbound j k)).trans_lt hn
theorem b2m (F:Jet) (hf :alm F) :
  ∃ i:Fin 2,0<(view i F).natDegree := by
 obtain ⟨j,k,h⟩:=hf
 obtain ⟨d,hd,hp⟩:=Finset.lt_sup_iff.mp h
 obtain ⟨i,hi⟩ : ∃ i,0<d i:= by
  by_contra! hzero
  have hz :d=0:=Finsupp.ext fun i=>uz (hzero i)
  simp [hz] at hp
 have hseed :0<(AV i ((F.coeff j).coeff k)).natDegree := by
  rw [dc2]
  exact hi.trans_le (MvPolynomial.monomial_le_degreeOf i hd)
 refine ⟨i,hseed.trans_le (le_natDegree_of_ne_zero ?_)⟩
 intro hz
 have hc:=bPK i F (AV i ((F.coeff j).coeff k)).natDegree j k
 rw [hz,wA,wA] at hc
 have hn:AV i ((F.coeff j).coeff k)≠0:= by
  intro hn
  simp [hn] at hseed
 exact (leadingCoeff_ne_zero.mpr hn) hc.symm
end
end bjF
end
section
set_option maxSynthPendingDepth 8
namespace bjF
noncomputable section
open K1 cu Polynomial
private theorem b1g {A:Type*} [ox A] {g f :lJ A}
    (hg:Prime g) (hd : ¬ g∣g.derivative) (e :ℕ)
    (hall : ∀ r<e,g∣qM r f) :g^e∣f := by
  let I:lI (lJ A) :=c9 ({g} : Set (lJ A))
  let:I.IsPrime :=(Ideal.span_singleton_prime hg.ne_zero).mpr hg
  let q:=n5 I
  have hq (s :lJ A) :q s=0↔g∣s :=
    Ideal.Quotient.eq_zero_iff_mem.trans G9
  let shift:lJ A →+* lJ (lJ A ⧸ I) :=
    (taylorAlgHom (q nq)).toRingHom.comp (t7 (q.comp lV))
  have hcoeff (s :lJ A) (r :ℕ) :
      (shift s).coeff r=q (qM r s) := by
    change (u8 (q nq) (s.map (q.comp lV))).coeff r= _
    rw [taylor_coeff,G8 ,eval_map,← Bf ,eval₂_C_X]
  have hzero (s :lJ A) : (shift s).coeff 0=q s := by
    rw [hcoeff,hasseDeriv_zero']
  have hone : (shift g).coeff 1≠0:= by
    rw [hcoeff,hasseDeriv_one']
    exact mt (hq _).mp hd
  obtain ⟨T,hT⟩: (nq:lJ (lJ A ⧸ I))∣shift g:= by
    rw [Polynomial.X_dvd_iff,hzero]
    exact (hq g).mpr (dvd_refl g)
  have hT0:T.coeff 0≠0:= by
    rw [hT,Xu T 0] at hone
    exact hone
  have horder (a :ℕ) (s :lJ A) :
      (shift (g^a*s)).coeff a=T.coeff 0^a*(shift s).coeff 0:= by
    rw [nI,p6,hT,mul_pow]
    have hprod: (nq ^a*T^a)*shift s =
        (T^a*shift s)*nq ^a := by ac_rfl
    rw [hprod]
    calc
      _=(T^a*shift s).coeff 0:= by
        simpa only [Pj] using Polynomial.coeff_mul_X_pow (T^a*shift s) a 0
      _ = _:= by
        change Cy (T^a*shift s)=Cy T^a*Cy (shift s)
        rw [nI,p6]
  induction e with
  | zero=>simp
  | succ a ih =>
    obtain ⟨s,hs⟩:=ih (fun r hr=>hall r (Lf hr))
    have hz :=(hq _).mpr (hall a (NX a))
    rw [hs,← hcoeff,horder,hzero] at hz
    have hdiv :=(hq s).mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hT0))
    obtain ⟨t,ht⟩:=hdiv
    exact ⟨t,by rw [hs,ht,yB,sS]⟩
private theorem b0u {A:Type*} [ox A] [vH A] {q:ℕ} [CharP A q]
  (g:lJ A) (hpos :0<g.natDegree) (hsmall:g.natDegree<q) :
  ¬ g∣g.derivative := by
 have hc: (g.natDegree :A)≠0:= by
  intro hz
  exact (Aa hsmall) (NY hpos ((Ok A q _).mp hz))
 have hlead:g.leadingCoeff≠0:= by
  apply leadingCoeff_ne_zero.mpr
  intro hz
  simp [hz] at hpos
 have hcoeff :g.derivative.coeff (g.natDegree - 1)≠0:= by
  rw [MK,← Nat.cast_add_one,HZ (Nat.succ_le_of_lt hpos)]
  exact Fz hlead hc
 have hn:g.derivative≠0:= by
  intro hz
  exact hcoeff (by simp [hz])
 intro hdiv
 exact (Aa (natDegree_derivative_lt hpos.ne')) (natDegree_le_of_dvd hdiv hn)
theorem proof :aBa.c1 := by
 intro G P R U e hG _ hmove hP hGP hsmall hcaps hhasse
 obtain ⟨i,hpos⟩:=b2m G hmove
 have hbound: (view i G).natDegree<p :=
   ((natDegree_le_of_dvd ((FR (view i)).mpr hGP)
     ((view i).map_ne_zero_iff.mpr hP)).trans (cvg i P U hcaps)).trans_lt hsmall
 let:CharP FX p:=z9 jz.injective p
 let:CharP axC p:=z9 (X8 (Fin 1) FX) p
 have hirr :JW (view i G) :=(UY (view i)).mpr hG
 have hprime :Prime (view i G) :=UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
 apply (FR (view i)).mp
 rw [p6]
 apply b1g hprime (b0u _ hpos hbound)
 intro r hr
 rw [← bPL]
 exact (FR (view i)).mpr (hhasse i r hr)
end
end bjF
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace cxU
noncomputable section
open we (cH)
open zP MvPolynomial Algebra
open scoped nonZeroDivisors
variable {A:Fin 4→ oz uh}
private abbrev rS (A:Fin 4→ oz uh) :=Σ i:Fin 4,↥(A i)
private abbrev cxz (A:Fin 4→ oz uh) :=
 {v :rS A // v.2.val≠0}
private abbrev bjp (A:Fin 4→ oz uh) :=
 nX (cxz A ⊕ Fin 4) cH
private def pivot (hz : ∀ i,0∈A i) (i:Fin 4) : ↥(A i) :=⟨0,hz i⟩
private def btj (i:Fin 4) (a : ↥(A i)) :bjp A :=
 if h:a.val=0 then 0 else
   lz (zR ⟨⟨i,a⟩,h⟩) *
     a.val.prod (fun j n=>lz (C4 j)^n)
private def bJ6 (A:Fin 4→ oz uh) (i:Fin 4) :bjp A :=
 ∑ a : ↥(A i),btj i a
private def qw (A:Fin 4→ oz uh) :
  xB A →ₐ[cH] bjp A :=
 pz fun v=>if h:v.2.val=0 then -bJ6 A v.1 else lz (zR ⟨v,h⟩)
private def aPx (A:Fin 4→ oz uh) :
  nX (Fin 4) (fZ A) →+* HG A :=
 n5 _
private theorem c5Z (r :fZ A) :
  aPx A (C r)=cy (fZ A) (HG A) r := by
 rw [← zk,aPx,Wm]
private def aWE (A:Fin 4→ oz uh) :
   xB A →+* HG A :=
 (cy (fZ A) (HG A)).comp
   (cy (xB A) (fZ A))
private def projection (A:Fin 4→ oz uh) :bjp A →+* HG A :=
 vl ((aWE A).comp (cy cH (xB A)))
  (Sum.elim (fun v=>aWE A (lz v.val))
    (fun j=>aPx A (lz j)))
private theorem c5F (i:Fin 4) :
  projection A (lz (C4 i))=aPx A (lz i) :=
 y5 _ _ _
private theorem ePq (i:Fin 4) (a : ↥(A i)) (ha :a.val≠0) :
    projection A (btj i a) =
      aPx A (xu a.val
        (cy (xB A) (fZ A) (lz ⟨i,a⟩))) := by
  simp only [btj,dite_eq_right ha,nI,map_finsuppProd,p6,c5F,
    monomial_eq]
  rw [show projection A (lz (zR ⟨⟨i,a⟩,ha⟩)) =
    aWE A (lz ⟨i,a⟩) from y5 _ _ _]
  rfl
private theorem ePr (hz : ∀ i,0∈A i) (i:Fin 4) :
    projection A (bJ6 A i)+aWE A (lz ⟨i,pivot hz i⟩)=0:= by
  classical
  let p:=pivot hz i
  have hzero :projection A (btj i p)=0:= by simp [p,pivot,btj]
  have hterms :projection A (bJ6 A i) =
      ∑ a∈Finset.univ.erase p,aPx A (xu a.val
        (cy (xB A) (fZ A) (lz ⟨i,a⟩))) := by
    rw [bJ6,vG,← zvm _ _ (zS p),hzero,u5]
    apply t4 rfl
    intro a ha
    exact ePq i a (fun he=>(Finset.mem_erase.mp ha).1 (wY he))
  have hrelation :aPx A (ve A i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (t9 ⟨i,rfl⟩)
  rw [ve,vG,← zvm _ _ (zS p),
    ← hterms] at hrelation
  simpa only [p,pivot,monomial_zero',c5Z,aWE,
    pC] using hrelation
private theorem eJ6 (hz : ∀ i,0∈A i) :
   (projection A).comp (qw A).toRingHom=aWE A:= by
 apply pU
 · intro r
   change projection A (qw A (C r))=aWE A (C r)
   rw [show qw A (C r)=C r from (qw A).commutes r]
   exact z7 _ _ _
 · rintro ⟨i,a⟩
   change projection A (qw A (lz ⟨i,a⟩)) =
     aWE A (lz ⟨i,a⟩)
   rw [qw,aeval_X]
   by_cases ha :a.val=0
   · have he :a=pivot hz i:=wY ha
     subst a
     rw [dite_eq_left (show (pivot hz i).val=0 from rfl),map_neg]
     exact neg_eq_iff_add_eq_zero.mpr (ePr hz i)
   · rw [dite_eq_right ha]
     exact y5 _ _ _
private def enU (hz : ∀ i,0∈A i) :cxz A ⊕ Fin 4 ≃ rS A:= by
  classical
  let constants :Fin 4 ≃ {v :rS A // ¬ v.2.val≠0} :=
    { toFun:= fun i=>⟨⟨i,pivot hz i⟩,by simp [pivot]⟩
      invFun:= fun v=>v.val.1
      left_inv := fun _=>rfl
      right_inv := by
        rintro ⟨⟨i,a⟩,ha⟩
        have he :a=pivot hz i:=wY  (not_ne_iff.mp ha)
        subst a
        rfl }
  exact (Equiv.sumCongr (Equiv.refl _) constants).trans (Equiv.sumCompl _)
private theorem bq2 (hz : ∀ i,0∈A i) :
  pL cH (bjp A)=pL cH (xB A) := by
 simpa only [ Xx ,Cardinal.lift_id] using
  Cardinal.mk_congr (enU hz)
private theorem dM6 (A:Fin 4→ oz uh) :
  pL cH (fZ A)<Cardinal.aleph0:= by
 let:G1 (xB A) (fZ A) :=
  Sv _ (u9 (xB A))
 rw [← Ef cH (xB A),KI (R:=xB A),u5 ,
  Xx ,Cardinal.lift_id]
 exact Cardinal.mk_lt_aleph0
private theorem ePp {D:Type} [ox D]
   (g:D →+* HG A) (u:fZ A →+* D)
   (hgu:g.comp u=cy (fZ A) (HG A))
   (coord:Fin 4→D) (hcoord : ∀ i,g (coord i)=aPx A (lz i)) :
   Function.Surjective g:= by
 let eval :nX (Fin 4) (fZ A) →+* D:=vl u coord
 have he :g.comp eval=aPx A:= by
   apply pU
   · intro r
     simp only [pC,eval,z7]
     exact (oZ hgu r).trans (c5Z r).symm
   · intro i
     simp only [pC,eval,y5]
     exact hcoord i
 intro q
 obtain ⟨p,rfl⟩:=uW q
 exact ⟨eval p,oZ he p⟩
private theorem eaN {k R B F Q:Type}
    [sH k] [ox R] [vH R] [t6 k R]
    [ox B] [vH B] [t6 k B]
    [sH F] [t6 R F] [IsFractionRing R F] [t6 k F] [IsScalarTower k R F]
    [ox Q] [xI Q] [t6 F Q] [Algebra.FiniteType F Q]
    (j:R →ₐ[k] B) (p:B →+* Q)
    (hpj:p.comp j.toRingHom=(cy F Q).comp (cy R F))
    (hdeg:pL k B=pL k R) (hfinite :pL k F<Cardinal.aleph0)
    (surjective : ∀ (D:Type) [ox D] (u:F →+* D) (g:D →+* Q) (w:B →+* D),
      g.comp u=cy F Q→ g.comp w=p→zpX g) :
    Module.Finite F Q:= by
  have hinj:qm (p.comp j.toRingHom) := by
    rw [hpj]
    exact (cy F Q).injective.comp (ze R F)
  have hj:qm j:= fun _ _ h=>hinj (ov p h)
  let M:=(u9 R).map j.toRingHom.toMonoidHom
  have hM:M≤u9 B :=
    map_le_nonZeroDivisors_of_injective j.toRingHom hj sI
  let D:=Localization M
  let:vH D:=IsLocalization.isDomain_localization hM
  let:FaithfulSMul B D :=
    (Xg B D).mpr (Ml D hM)
  let u:F →+* D :=
    zvq (M:=u9 R) (g:=(cy B D).comp j.toRingHom)
      (fun x=>II D (⟨j x,⟨x,x.2,rfl⟩⟩:M))
  let:t6 F D:=u.toAlgebra
  let:IsScalarTower k F D:=IsScalarTower.of_algebraMap_eq (by
    intro r
    rw [zi k B D,zi k R F]
    change cy B D (cy k B r)=u (cy R F (cy k R r))
    simp only [u,XG,pC]
    exact ov (cy B D) (j.commutes r).symm)
  have hd:pL k D =pL k F:= by
    let:G1 B D:=Sv D M
    let:G1 R F:=Sv F (u9 R)
    calc
      pL k D =pL k B:= by
        rw [← Ef k B (A:=D),KI (R:=B),u5]
      _=pL k R:=hdeg
      _=pL k F:= by
        rw [← Ef k R (A:=F),KI (R:=R),u5]
  let:FaithfulSMul F D :=
    (Xg F D).mpr u.injective
  have hzero :pL F D =0:= by
    have hle :pL F D ≤0:= by
      apply (Cardinal.add_le_add_iff_of_lt_aleph0 hfinite).mp
      calc
        pL F D + pL k F=pL k D :=
          (vw _ _).trans (Ef k F (A:=D))
        _≤0+trdeg k F:= by rw [hd,zE]
    exact Ob hle bot_le
  let:XB F D :=
    Algebra.isAlgebraic_iff_isIntegral.mp (trdeg_eq_zero_iff.mp hzero)
  have hunits : ∀ x :M,IsUnit (p x) := by
    rintro ⟨_,x,hx,rfl⟩
    change IsUnit ((p.comp j.toRingHom) x)
    rw [hpj,pC]
    have hx' : cy R F x≠0:= by
      simpa only [qz] using (ze R F).ne
        (mem_nonZeroDivisors_iff_ne_zero.mp hx)
    exact (isUnit_iff_ne_zero.mpr hx').map (cy F Q)
  let g:D →+* Q:=zvq hunits
  have hgu:g.comp u=cy F Q:= by
    apply IsLocalization.ringHom_ext (u9 R)
    apply SD
    intro x
    simp only [pC,g,u,XG]
    exact oZ hpj x
  let e :D →ₐ[F] Q:=⟨g,oZ hgu⟩
  have hg:=surjective D u g (cy B D) hgu (IsLocalization.lift_comp hunits)
  let:XB F Q:=⟨fun q=> by
    obtain ⟨d,rfl⟩:=hg q
    exact (Algebra.IsIntegral.isIntegral d).map e⟩
  exact Algebra.IsIntegral.finite
private theorem eaM (hz : ∀ i,0∈A i) [xI (HG A)] :
  v8 (fZ A) (HG A) := by
 apply eaN (qw A) (projection A) (eJ6 hz)
  (bq2 hz) (dM6 A)
 intro D _ u g w hgu hgw
 refine ePp g u hgu (fun i=>w (lz (C4 i))) ?_
 intro i
 exact (oZ hgw _).trans (c5F i)
theorem proof :aaq.c1 := by
 intro A hz
 rcases subsingleton_or_nontrivial (HG A) with hQ | hQ
 · let:=hQ
   exact Module.Finite.of_surjective (Algebra.linearMap (fZ A) (HG A))
    (fun q=>⟨0,Subsingleton.elim _ q⟩)
 · let:=hQ
   exact eaM hz
end
end cxU
end
section
namespace aeA
noncomputable section
open aR oR MvPolynomial
open scoped Polynomial BigOperators
def view {r :ℕ} : af (r+1) ≃ₐ[ao[X]] lJ (af r) :=
 (Mj ao[X] x7).trans (optionEquivLeft ao[X] (Fin r))
theorem gLc {r :ℕ} (f :af (r+1)) :
  (view f).natDegree=f.degreeOf (qx r) := by
 change (optionEquivLeft _ _ (oy x7 f)).natDegree= _
 rw [natDegree_optionEquivLeft]
 simpa only [Eg] using
  Xo (p:=f) finSuccEquivLast.injective (qx r)
theorem gLd {r :ℕ} (f :af (r+1)) :
  view (oD (qx r) f)=(view f).derivative := by
 change optionEquivLeft _ _ (oy x7 (oD (qx r) f))= _
 rw [← pderiv_rename finSuccEquivLast.injective,Eg ,
  optionEquivLeft_pderiv_none]
 rfl
theorem cvh {r :ℕ} (f :af (r+1)) (S:ao[X]) :
   cK f S=((view f).map (eval (jet S))).eval (jet S (qx r)) := by
 rw [cK,view,AlgEquiv.trans_apply,renameEquiv_apply,← optionEquivLeft_elim_eval,
   eval_rename]
 apply ov (fun v=>eval v f)
 funext i
 refine Fin.lastCases ?_ (fun j => ?_) i
 · simp [Eg]
 · simp [jet]
theorem biB {r :ℕ} (w:Fin (r+1)→ℕ)
    (f :af (r+1)) (k :ℕ)
    (hk :k≤(view f).natDegree) :
    ((view f).coeff k).weightedTotalDegree (fun i=>w i.castSucc) +
      w (qx r)*k≤f.weightedTotalDegree w:= by
  classical
  let w' : Option (Fin r)→ℕ:= fun i=>i.elim (w (qx r)) (fun j=>w j.castSucc)
  have hw : ∀ i:Fin (r+1),w' (x7 i)=w i:= by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [w',Eg]
  have hrename : (oy x7 f).weightedTotalDegree w' =
      f.weightedTotalDegree w:= by
    rw [Gj,Gj,support_rename_of_injective
      finSuccEquivLast.injective,Finset.sup_image]
    congr 1
    funext u
    simp only [SU,LQ,zc]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
    simp only [hw]
  have hterm (k :ℕ) (m:Fin r →₀ ℕ) (hm:m∈((view f).coeff k).support) :
      m.weight (fun i=>w i.castSucc)+w (qx r)*k≤f.weightedTotalDegree w:= by
    have hs :=(mem_support_coeff_optionEquivLeft _).mp hm
    have hle :=zh w' hs
    change _≤(oy x7 f).weightedTotalDegree w' at hle
    rw [hrename,Finsupp.weight_optionElim] at hle
    simpa only [w',Nat.add_comm,Nat.mul_comm] using hle
  have hcoeff (j:ℕ) (hj: (view f).coeff j≠0) :
      ((view f).coeff j).weightedTotalDegree (fun i=>w i.castSucc) +
        w (qx r)*j≤f.weightedTotalDegree w:= by
    obtain ⟨m,hm,hmax⟩:=Wl
      _ (support_nonempty.mpr hj) (fun m=>m.weight (fun i:Fin r=>w i.castSucc))
    rw [Gj,hmax]
    exact hterm j m hm
  by_cases hzero : (view f).coeff k=0
  · rw [hzero,weightedTotalDegree_zero,bot_eq_zero,zE]
    by_cases hf :view f=0
    · simp_all
    have h:=hcoeff _ (Polynomial.leadingCoeff_ne_zero.mpr hf)
    exact (KH _ hk).trans ((Nat.le_add_left _ _).trans h)
  · exact hcoeff k hzero
def elimination {r :ℕ} (f :af (r+1)) :af r :=
 let F:=view f
 let c:=F.natDegree
 if c=0 then F.coeff 0 else F.resultant F.derivative c (c - 1)
theorem d0Z {r :ℕ} (f :af (r+1)) (S:ao[X])
    (hf :cK f S=0) :
    cK (elimination f) S=0 ∨
      (0<(view f).natDegree∧qg (qx r) f S) := by
  by_cases hdeg: (view f).natDegree=0
  · left
    rw [cvh,Polynomial.eq_C_of_natDegree_eq_zero hdeg,RJ,
      Polynomial.eval_C] at hf
    simpa [elimination,hdeg,cK] using hf
  · by_cases hder :cK (oD (qx r) f) S=0
    · left
      rw [cvh,gLd] at hder
      rw [cvh] at hf
      simpa only [elimination,vk hdeg,cK] using
        Polynomial.map_resultant_eq_zero_of_common_root (eval (jet S))
          (view f) (view f).derivative sI (Polynomial.natDegree_derivative_le _)
          (v9 hdeg) (jet S (qx r)) hf hder
    · exact Or.inr ⟨WD hdeg,hf,hder⟩
theorem d02 {r :ℕ} {f :af (r+1)} (hf :JW f)
    (hc: (view f).natDegree<K1.p) :elimination f≠0:= by
  let F:=view f
  let c:=F.natDegree
  have hi:JW F:=(UY view.toMulEquiv).mpr hf
  change (if c=0 then F.coeff 0 else F.resultant F.derivative c (c - 1))≠0
  by_cases h:c=0
  · have hnz :=Polynomial.leadingCoeff_ne_zero.mpr hi.ne_zero
    change F.coeff c≠0 at hnz
    rw [h] at hnz
    simpa only [wB h] using hnz
  · have :CharP ao K1.p :=
      z9 (RingHom.injective embed) K1.p
    have hcast: (c:ao)≠0:= by
      intro hz
      exact (Aa hc) (NY (WD h)
        ((Ok ao K1.p c).mp hz))
    have hc' : (c:af r)≠0:= by
      let ι:ao →+* af r :=MvPolynomial.C.comp lV
      have hinj:qm ι :=
        (X8 _ _).comp Polynomial.C_injective
      simpa only [Mk,qz] using (hinj.ne hcast :
        ι (c:ao)≠ι 0)
    have hder :F.derivative≠0:= by
      intro hz
      have hindex :c - 1+1=c:= by omega
      have hz' := ov (fun p:lJ (af r)=>p.coeff (c - 1)) hz
      rw [MK,← G0 ,Nat.succ_eq_add_one,hindex,
        wA] at hz'
      exact (Fz (Polynomial.leadingCoeff_ne_zero.mpr hi.ne_zero) hc') hz'
    simpa only [vk h] using
      Polynomial.resultant_derivative_ne_zero_of_irreducible F hi hder
end
end aeA
end
section
namespace aeA
noncomputable section
open aR MvPolynomial
open scoped Polynomial BigOperators
private theorem fXo {r :ℕ} (w:Fin r→ℕ) (a :ℕ)
    (P Q:lJ (af r)) (m n B D:ℕ)
    (hP : ∀ i≤ m,(P.coeff i).weightedTotalDegree w+a*i≤B)
    (hQ : ∀ i≤n,(Q.coeff i).weightedTotalDegree w+a*i≤D) :
    (P.resultant Q m n).weightedTotalDegree w+a*(m*n)≤n*B+m*D:= by
  classical
  let M:=Pk P Q m n
  let W:Fin (m+n)→ℕ :=
    Fin.addCases (fun j:Fin m=>D + a*j.val) (fun j:Fin n=>B+a*j.val)
  have hentry (σ:Equiv.Perm (Fin (m+n))) (i:Fin (m+n))
      (hne :M (σ i) i≠0) :
      (M (σ i) i).weightedTotalDegree w+a*(σ i).val≤W i:= by
    cases i using Fin.addCases with
    | left j =>
      simp only [M,Pk,Matrix.of_apply,PD] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hj:j.val≤(σ (j.castAdd n)).val :=h.1
        have hh:=hQ ((σ (j.castAdd n)).val - j.val) (by have :=h.2; omega)
        simp only [W,PD]
        have hid :a*((σ (j.castAdd n)).val - j.val)+a*j.val =
            a*(σ (j.castAdd n)).val := by rw [← Dw ,HZ hj]
        omega
      · exact absurd rfl hne
    | right j =>
      simp only [M,Pk,Matrix.of_apply,JQ] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hj:j.val≤(σ (j.natAdd m)).val :=h.1
        have hh:=hP ((σ (j.natAdd m)).val - j.val) (by have :=h.2; omega)
        simp only [W,JQ]
        have hid :a*((σ (j.natAdd m)).val - j.val)+a*j.val =
            a*(σ (j.natAdd m)).val := by rw [← Dw ,HZ hj]
        omega
      · exact absurd rfl hne
  let S:=(∑ j:Fin m,a*j.val) + ∑ j:Fin n,a*j.val
  have hW : ∑ i,W i=m*D + n*B+S:= by
    simp only [W,S,Fin.sum_univ_add,PD,JQ,
      wR,Finset.sum_const,Finset.card_univ,PA,zc]
    ring
  have hsum : ∑ i:Fin (m+n),a*i.val=a*(m*n)+S:= by
    simp only [S,Fin.sum_univ_add,Fin.val_castAdd,Fin.val_natAdd,Dw ,
      wR,Finset.sum_const,Finset.card_univ,PA,zc]
    ring
  have hbase :a*(m*n)≤n*B:= by
    rw [show a*(m*n)=n*(a*m) by ring]
    exact KH n ((Nat.le_add_left _ _).trans (hP m sI))
  have hterm (σ:Equiv.Perm (Fin (m+n))) :
      (∏ i,M (σ i) i).weightedTotalDegree w≤n*B+m*D - a*(m*n) := by
    by_cases hz : ∃ i,M (σ i) i=0
    · obtain ⟨i,hi⟩:=hz
      have hp: (∏ j,M (σ j) j)=0:=Finset.prod_eq_zero (zS i) hi
      rw [hp,weightedTotalDegree_zero]
      exact Nat.zero_le _
    · simp only [not_exists] at hz
      rw [weightedTotalDegree_prod _ _ _ (fun i _=>hz i)]
      have h:=yo (s :=Finset.univ) (fun i _=>hentry σ i (hz i))
      rw [wR,Equiv.sum_comp σ (fun i=>a*i.val),hW,hsum] at h
      omega
  have hdet:M.det.weightedTotalDegree w≤n*B+m*D - a*(m*n) := by
    rw [Matrix.det_apply]
    refine AddMonoidAlgebra.supDegree_sum_le.trans (yL fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs,one_smul]
      exact hterm σ
    · have hsign:Equiv.Perm.sign σ•(∏ i,M (σ i) i) = -(∏ i,M (σ i) i) := by
        simp [hs]
      rw [hsign,AddMonoidAlgebra.supDegree_neg]
      exact hterm σ
  change M.det.weightedTotalDegree w+a*(m*n)≤_
  omega
private theorem dMl {r :ℕ} (w:Fin r→ℕ) (P:lJ (af r))
  (i:ℕ) :
  (P.derivative.coeff i).weightedTotalDegree w≤(P.coeff (i+1)).weightedTotalDegree w:= by
 rw [MK,← G0 ,← Mk (mD:ao[X] →+* af r)]
 exact (weightedTotalDegree_mul_le _ _ _).trans (by rw [weightedTotalDegree_C,OJ])
theorem cLz {r :ℕ} (w:Fin (r+1)→ℕ)
   (f :af (r+1)) (hc:0<(view f).natDegree) :
   let c:=(view f).natDegree
   (elimination f).weightedTotalDegree (fun i=>w i.castSucc) +
     w (qx r)*c^2≤(2*c - 1)*f.weightedTotalDegree w:= by
 let A:=view f
 let a :=w (qx r)
 let v :Fin r→ℕ:= fun i=>w i.castSucc
 let B:=f.weightedTotalDegree w
 change 0<A.natDegree at hc
 obtain ⟨k,hk⟩ : ∃ k,A.natDegree=k+1 :=
   ⟨A.natDegree - 1,by omega⟩
 have hA : ∀ i≤k+1,(A.coeff i).weightedTotalDegree v+a*i≤B :=
   fun i hi=>biB w f i (by rwa [hk])
 have hab:a≤B:= by
   have htop:=hA (k+1) sI
   rw [Dw ,Nat.mul_one] at htop
   omega
 obtain ⟨d,hd⟩:=Nat.exists_eq_add_of_le hab
 have hD : ∀ i≤k,(A.derivative.coeff i).weightedTotalDegree v+a*i≤d:= by
   intro i hi
   have h:=hA (i+1) (by omega)
   rw [Dw ,Nat.mul_one,hd] at h
   have h' := dMl v A i
   omega
 have h:=fXo v a A A.derivative (k+1) k B d hA hD
 have hEq:elimination f=A.resultant A.derivative (k+1) k := by
   change (if A.natDegree=0 then A.coeff 0
     else A.resultant A.derivative A.natDegree (A.natDegree - 1))= _
   simp [hk]
 have hR: (2*(k+1) - 1)*B=k*B+(k+1)*d+(k+1)*a := by
   rw [show 2*(k+1) - 1=2*k+1 by omega,hd]
   ring
 have hL:a*(k+1)^2=a*((k+1)*k)+(k+1)*a := by ring
 change (elimination f).weightedTotalDegree v+a*A.natDegree^2≤(2*A.natDegree - 1)*B
 rw [hk,hEq,hL,hR]
 omega
theorem cLA {r :ℕ} (w:Fin (r+1)→ℕ)
  (f :af (r+1)) (hc: (view f).natDegree=0) :
  (elimination f).weightedTotalDegree (fun i=>w i.castSucc)≤f.weightedTotalDegree w:= by
 simpa [elimination,hc] using biB w f 0 (Nat.zero_le _)
end
end aeA
end
section
namespace aeA
noncomputable section
open scoped BigOperators
private theorem beA {a b c C t d:ℕ} (hc:0<c) (hC:c≤C)
  (ht:a*t≤2*b) (hd:d+a*c^2≤(2*c - 1)*b) :
  d+a*c^2+a*((C - c)*t)≤(2*C - 1)*b:= by
 have hincr :=KH (C - c) ht
 have he :2*C - 1=(2*c - 1)+2*(C - c) := by omega
 rw [he,Nat.add_mul]
 rw [show a*((C - c)*t)=(C - c)*(a*t) by ring,
  show 2*(C - c)*b=(C - c)*(2*b) by ring]
 exact Nat.add_le_add hd hincr
end
end aeA
end
section
namespace dm8
noncomputable section
open aR oR we aA1
open dN (lX pK)
open MvPolynomial
open scoped Polynomial
private theorem cGt (P:af 4) (m:Fin 4 →₀ ℕ) :
   (lX P).coeff m=Polynomial.derivative (P.coeff m) := by
 classical
 rw [lX,RC]
 simp only [Iw ,Finset.sum_ite_eq']
 split_ifs with h
 · rfl
 · rw [MvPolynomial.notMem_support_iff.mp h,qz]
private theorem c9c (P Q:af 4) (m:Fin 4 →₀ ℕ) :
  (P+Q).coeff m=P.coeff m+Q.coeff m :=
 oK (MvPolynomial.coeffAddMonoidHom m) P Q
private theorem aCH (P Q:af 4) :
  lX (P+Q)=lX P+lX Q:= by
 apply LP
 intro m
 simp only [cGt,c9c,Polynomial.derivative_add]
private theorem a2H (P Q:af 4) :
  lX (P*Q)=P*lX Q+lX P*Q:= by
 classical
 apply LP
 intro m
 simp only [cGt,c9c,GF,
  Polynomial.derivative_sum,Polynomial.derivative_mul,wR]
 exact vw _ _
private theorem btt (P Q:af 4) :
  pK (P+Q)=pK P+pK Q:= by
 simp only [pK,aCH,oK,mul_add,wR]
 ring
private theorem a6r (P Q:af 4) :
    pK (P*Q)=P*pK Q+pK P*Q:= by
  let weight (i:Fin 3) :af 4 :=
    mD (lV ((i.val+1 :ℕ) :ao))*lz i.succ
  have hsum :
      (∑ i:Fin 3,weight i*oD i.castSucc (P*Q)) =
        P*(∑ i:Fin 3,weight i*oD i.castSucc Q) +
        (∑ i:Fin 3,weight i*oD i.castSucc P)*Q:= by
    rw [Dz ,Qx ,← wR]
    apply t4 rfl
    intro i _
    rw [LR]
    ring
  change lX (P*Q)+(∑ i:Fin 3,weight i*oD i.castSucc (P*Q)) =
    P*(lX Q+(∑ i:Fin 3,weight i*oD i.castSucc Q)) +
      (lX P+(∑ i:Fin 3,weight i*oD i.castSucc P))*Q
  rw [a2H,hsum]
  ring
private def Z5 (f :af 3) :af 4 →+ af 4 where
 toFun b:=KY f*pK b+apE f*oD 3 b
 map_zero' := by simp [pK,lX]
 map_add' P Q:= by rw [btt,oK]; ring
private theorem bNl (f :af 3) (b:af 4) :
 Z5 f b=KY f*pK b+apE f*oD 3 b:=rfl
private theorem bv1 (f :af 3) (P Q:af 4) :
  Z5 f (P*Q)=P*Z5 f Q+Z5 f P*Q:= by
 simp only [bNl,a6r,LR]
 ring
private theorem gmf (f :af 3) :Z5 f 1=0:= by
 have h:=bv1 f 1 1
 simp only [Au,mul_one] at h
 exact add_left_cancel (show Z5 f 1+Z5 f 1=Z5 f 1+0 by
  rw [u5]; exact h.symm)
private theorem gme (f :af 3) (n:ℕ) :Z5 f (n:af 4)=0:= by
 induction n with
 | zero=>simp
 | succ n ih=>rw [Nat.cast_succ,map_add,ih,gmf,add_zero]
private theorem gmg (f :af 3) (b:af 4) (k :ℕ) :
   Z5 f (b^(k+1))=(↑(k+1) :af 4)*b^k*Z5 f b:= by
 induction k with
 | zero=>simp
 | succ k ih =>
   rw [yB b (k+1),bv1,ih,yB b k]
   simp only [G0]
   ring
private def bOQ:ao[X] :=lV ((3:ao)⁻¹)
private theorem dhg: (3:ao[X])*bOQ=1 := by
 have h: (3:ao)≠0:=bqC (a :=3) (by decide) (by decide)
 change (lV (3:ao))*lV ((3:ao)⁻¹)=1
 rw [← nI,mul_inv_cancel₀ h,map_one]
private theorem gmd (f :af 3) :Z5 f (Xj f)=0:= by
 have h:=ov (mD:ao[X] →+* af 4) dhg
 simp only [nI,GR,map_one] at h
 have hvelocity :3*apE f = -pK (Xj f) := by
   rw [apE,Polynomial.C_neg]
   change 3*(mD (-bOQ)*pK (Xj f))= _
   rw [map_neg]
   calc
     _ = -(3*mD bOQ)*pK (Xj f) := by ring
     _ = _:= by rw [h]; ring
 change KY f*pK (Xj f) +
   apE f*dN.separant (Xj f)=0
 rw [b5I]
 calc
   _=KY f*pK (Xj f)+(3*apE f)*KY f := by ring
   _=0:= by rw [hvelocity]; ring
private abbrev c61 (f :af 3) :lI (af 4) :=c9 {Xj f}
private abbrev aMV (f :af 3) :=n5 (c61 f)
private theorem gmc (f :af 3) {P Q:af 4} (h:aMV f P=aMV f Q) :
  aMV f (Z5 f P)=aMV f (Z5 f Q) := by
 obtain ⟨b,hb⟩:=Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h)
 apply Ideal.Quotient.eq.mpr
 rw [← qG,← hb,bv1,gmd,mul_zero,zE]
 exact Ideal.mem_span_singleton'.mpr ⟨_,rfl⟩
private theorem dce (f b:af 3) :
  aMV f (Z5 f (KX b))=aMV f (KX (Ev f b)) := by
 apply Ideal.Quotient.eq.mpr
 rw [bNl,aWm,mul_zero,u5 ,btu]
 refine Ideal.mem_span_singleton'.mpr ⟨KX (oD 2 b),?_⟩
 simp only [ Xj,Ev,KY,separant,qG,nI]
 ring
private theorem dcf (f :af 3) :
  Z5 f (KY f)=KY f*pK (KY f) := by
 rw [bNl,aWm,mul_zero,u5]
private theorem gmh (f :af 3) (k :ℕ) (b:af 4) :
    Z5 f (3*KY f^(k+1)*b) =
      3*KY f^(k+1)*Z5 f b +
        3*(↑(k+1) :af 4)*KY f^(k+1)*pK (KY f)*b:= by
  have h3:Z5 f 3=0:=gme f 3
  rw [bv1,bv1 f 3,h3,zero_mul,u5 ,gmg,dcf,
    yB (KY f) k]
  ring
private theorem fTL (f :af 3) (k :ℕ) :
    aMV f (3*KY f^(k+1)*YL f k) =
      aMV f (KX (AR f k)) := by
  induction k with
  | zero =>
    apply Ideal.Quotient.eq.mpr
    refine Ideal.mem_span_singleton'.mpr ⟨1,?_⟩
    simp only [Au,YL,AR,zE,pow_one,map_neg,Xj]
    ring
  | succ k ih =>
    let s :=KY f
    let b:=YL f k
    let A:=AR f k
    let q:=aMV f
    have h:q (3*s^(k+1)*b)=q (KX A) :=ih
    have hD:=(gmc f h).trans (dce f A)
    have hs :=dce f (separant f)
    change q (Z5 f (3*s^(k+1)*b))=q (KX (Ev f A)) at hD
    change q (Z5 f s)=q (KX (Ev f (separant f))) at hs
    calc
      q (3*s^(k+1+1)*a5p f k b) =
          q (s*Z5 f (3*s^(k+1)*b) -
            (↑(2*k+1) :af 4)*(3*s^(k+1)*b)*Z5 f s) := by
        congr 1
        rw [a5p,gmh,dcf,bNl,yB s (k+1)]
        push_cast
        ring
      _=q (KX (AR f (k+1))) := by
        rw [qG q,nI q,nI q,nI q,hD,h,hs]
        simp only [AR,qG,nI,Mk]
        rfl
private theorem efD (f :af 3) {P:af 4} (h:P∈c61 f) :
  fW P∈rP f := by
 obtain ⟨b,hb⟩:=Ideal.mem_span_singleton'.mp h
 rw [← hb,fW,nI]
 change fW b*fW (Xj f)∈rP f
 rw [bHp]
 exact KA _ _ (t9 (by simp))
private theorem aEA (f :af 3) (k :ℕ) :
   ag9 f (AR f k) (fW (YL f k)) := by
 have h:=efD f (Ideal.Quotient.eq.mp (fTL f k))
 change p7 qY (_-_)∈rP f at h
 rw [qG,nI,nI,p6,GR] at h
 change 3*fW (KY f)^(k+1)*fW (YL f k) -
   fW (KX (AR f k))∈rP f at h
 rw [beh,beh] at h
 let c:=qY bOQ
 have h3:3*c=1 := by
   simpa only [nI,GR,map_one] using ov qY dhg
 have hc:c≠0:= by
   intro hz
   rw [hz,mul_zero] at h3
   exact zero_ne_one h3
 have hC: (3:eT 4)*mD c=1 := by
   simpa only [nI,GR,map_one] using
     ov (mD:cH →+* eT 4) h3
 refine ⟨0,k+1,c,hc,?_⟩
 simp only [pow_zero,Au]
 convert KA (rP f) (mD c) h using 1
 rw [mul_sub,← sS (mD c),← sS (mD c),t3 (mD c) 3,
   hC,Au]
end
end dm8
end
section
namespace dm6
noncomputable section
open K1 aR jA acZ
open scoped Polynomial BigOperators
private def line {R:Type*} [vZ R] (i:mA) :
  VP R →+* (VP R)[X] :=
 vl (Polynomial.C.comp mD) fun j =>
  lV (lz j)+if j=i then nq else 0
private theorem bIw {R:Type*} [vZ R] (i:mA) (r :R) :
  line i (mD r)=lV (mD r) := by
 simp [line]
private theorem b7L {R:Type*} [vZ R] (i j:mA) :
  line i (lz j:VP R) =
   lV (lz j)+if j=i then nq else 0:= by
 simp [line]
private theorem cYa {R:Type*} [vZ R] (i j:mA) (F:VP R) :
    line i (F*lz j) =
      (if j=i then line i F*nq else 0) +
        lV (lz j)*line i F:= by
  rw [nI,b7L]
  by_cases h:j=i <;> simp [h,mul_add,t3 ,vw]
private theorem b7T {R:Type*} [vZ R] (i:mA) (F:VP R) :
   (line i F).coeff 0=F:= by
 let ev :=(Cy (R:=VP R)).comp (line i)
 change ev F=(Il _) F
 have he :ev=Il _:= by
   apply pU
   · intro c
     simp [ev,bIw]
   · intro j
     by_cases h:j=i <;> simp [ev,b7L,h]
 rw [he]
private theorem ewX {R:Type*} [vZ R] (i:mA) (F:VP R) :
   (line i F).coeff 1=oD i F:= by
 induction F using JM with
 | C c=>simp [bIw]
 | add P Q hp hq=>simp [hp,hq]
 | mul_X P j hp =>
   rw [cYa,Kp,Av,hp,LR]
   by_cases h:j=i
   · subst j
     simp only [ite_true,MvPolynomial.pderiv_X_self,mul_one]
     rw [show (1 :ℕ)=0+1 from rfl,zwB,b7T,t3]
     exact vw _ _
   · simp [h,MvPolynomial.pderiv_X_of_ne h,t3]
private theorem ZP {R:Type*} [vZ R] (i:mA) (F:VP R) (n:ℕ) :
    (line i F).coeff n=Rk.KR (Finsupp.single i n) F:= by
  classical
  induction F using JM generalizing n with
  | C c =>
    cases n <;> simp [bIw,Rk.cbu,Finsupp.single_eq_zero]
  | add P Q hp hq =>
    simp only [oK,Kp,hp,hq,Rk.KR,
      AddMonoidAlgebra.coeff_add,NI]
  | mul_X P j hp =>
    rw [cYa,Kp,Av,hp,Rk.c3J]
    by_cases h:j=i
    · subst j
      cases n with
      | zero=>simp [mul_comm]
      | succ n =>
        have hn:n+1≠0:=Nat.succ_ne_zero n
        simp only [ite_true,zwB,hp,Finsupp.mem_support_iff,
          Mw ,← Finsupp.single_tsub,Nat.succ_sub_one]
        rw [wB hn,t3 (lz i)]
    · simp [h,Finsupp.single_eq_of_ne h,t3]
private theorem cYc (i:mA) (F:jK) (n:ℕ) :
   (line i (bC F)).coeff n=bC (aox (Finsupp.single i n) F) := by
 let g:jK →+* ko:=p7 qV
 let l:=(line i).comp g
 let r :=(t7 g).comp (line i)
 have he :l=r := by
   apply pU
   · intro c
     simp [l,r,g,bIw,xW]
   · intro j
     by_cases h:j=i <;> simp [l,r,g,b7L,h,xW]
 have h:line i (bC F)=(line i F).map g:=G4 he F
 rw [h,vj,ZP,Rk.aIY]
 rfl
private theorem ct4 {f :ko} {i:mA}
    (hpos :0<f.degreeOf i) (hsmall:f.degreeOf i<K1.p) :
    ¬ f∣(line i f).coeff 1 := by
  classical
  rw [ewX]
  have hdeg: (oD i f).degreeOf i≤f.degreeOf i - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    rw [Dv,Ye] at hm
    have hd:=NZ i (MvPolynomial.mem_support_iff.mpr
      (Te hm))
    simp only [NI,Mw] at hd
    omega
  have hnz :oD i f≠0:= by
    have hsup:0<f.support.sup (fun m=>m i) := by
      rwa [← Gk]
    obtain ⟨u,hu,htop⟩:=(Finset.le_sup_iff hsup).mp (le_refl _)
    have hup:0< u i:=hsup.trans_le htop
    have hult:=(NZ i hu).trans_lt hsmall
    let m:=u-Finsupp.single i 1
    have hsum:m+Finsupp.single i 1=u :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hup)
    have hm: (m i).succ=u i:= by
      change m i+1=u i
      simpa only [NI,Mw] using
        ov (fun a :mA →₀ ℕ=>a i) hsum
    let _:CharP ao K1.p:=z9 embed.injective K1.p
    let _:CharP iP K1.p:=z9 DI.injective K1.p
    have hcast: (↑(u i) :iP)≠0:= by
      intro hz
      exact (Aa hult)
        (NY hup ((Ok iP K1.p _).mp hz))
    have hcoeff : (oD i f).coeff m≠0:= by
      rw [Ye,← G0 ,hm,hsum]
      exact Fz (MvPolynomial.mem_support_iff.mp hu) hcast
    intro hz
    exact hcoeff (by simp [hz])
  rintro ⟨g,hg⟩
  have hne :f≠0∧g≠0:= by simpa [hg] using hnz
  rw [hg,MvPolynomial.degreeOf_mul_eq hne.1 hne.2] at hdeg
  omega
private theorem d3G {R:Type*} [ox R]
  (T:R →+* R[X]) (hzero : ∀ G,(T G).coeff 0=G)
  {f P:R} {a :ℕ} (hf :Prime f) (hsep : ¬ f∣(T f).coeff 1)
  (ha :f^a∣P) (hexact : ¬ f^(a+1)∣P) :
  ¬ f∣(T P).coeff a := by
 obtain ⟨U,rfl⟩:=ha
 have hu : ¬ f∣U:= by
  rintro ⟨V,rfl⟩
  exact hexact ⟨V,by rw [yB,sS]⟩
 let J:=c9 ({f} : Set R)
 have :J.IsPrime :=Ideal.isPrime_span_singleton_of_prime hf
 let reduce :=n5 J
 let tr :=(t7 reduce).comp T
 have hz (G:R) :reduce G=0↔f∣G :=
  Ideal.Quotient.eq_zero_iff_mem.trans G9
 have hc (G:R) (n:ℕ) : (tr G).coeff n=reduce ((T G).coeff n) :=
  vj _ _
 have hc₀ (G:R) : (tr G).coeff 0=reduce G:= by rw [hc,hzero]
 obtain ⟨V,hV⟩:=Polynomial.X_dvd_iff.mpr
  (show (tr f).coeff 0=0 by rw [hc₀]; exact (hz _).mpr dvd_rfl)
 have hfirst:V.coeff 0=reduce ((T f).coeff 1) := by
  rw [← hc,hV]
  exact (Xu V 0).symm
 have hr :reduce ((T (f^a*U)).coeff a)=reduce ((T f).coeff 1)^a*reduce U:= by
  rw [← hc,nI,p6,hV,mul_pow,sS]
  have he :=Polynomial.coeff_X_pow_mul (V^a*tr U) a 0
  rw [zE] at he
  rw [he]
  change Cy (V^a*tr U)= _
  rw [nI,p6]
  change (V.coeff 0)^a*(tr U).coeff 0= _
  rw [hfirst,hc₀]
 intro h
 exact (Fz (pow_ne_zero _ ((hz _).not.mpr hsep)) ((hz _).not.mpr hu))
  (hr.symm.trans ((hz _).mpr h))
private theorem c40 {R:Type*} [ox R]
   (T:R →+* R[X]) (hzero : ∀ G,(T G).coeff 0=G)
   {f P:R} (hf :Prime f) (hsep : ¬ f∣(T f).coeff 1)
   (n:ℕ) (htest : ∀ a<n,f∣(T P).coeff a) :f^n∣P:= by
 induction n with
 | zero=>simp
 | succ n ih =>
   have hn:=ih fun a ha=>htest a (Lf ha)
   by_contra hexact
   exact d3G T hzero hf hsep hn hexact (htest n (NX n))
private theorem c4V {f :ko} (hf :0<vC f) :
   ∃ j:Fin 3,0<f.degreeOf (some j) := by
 classical
 by_contra h
 apply (Aa hf)
 rw [vC,Gj]
 apply yL
 intro m hm
 apply le_of_eq
 rw [LQ,Finsupp.sum]
 apply Pf
 intro i _
 cases i with
 | none=>simp
 | some j =>
   have hj₀:f.degreeOf (some j)≤0 :=
     Nat.le_of_not_gt fun hj=>h ⟨j,hj⟩
   have hj:=(NZ (some j) hm).trans hj₀
   simp [uz hj]
end
end dm6
end
section
namespace dnb
noncomputable section
open aR oR we yz aA2 MvPolynomial
private theorem cNE {R:Type*} [ox R] {I P:lI R}
   [P.IsPrime] {s :R} (hIP:I≤P) (hs :s∉P) :
   ∃ q:lI (TC I s),q.IsPrime∧q.comap (ad2 I s)=P:= by
 let p:=P.map (n5 I)
 have hp:p.IsPrime :=
   Ideal.map_isPrime_of_surjective uW (by rwa [Qy])
 have hcomap :p.comap (n5 I)=P:= by
   change (P.map (n5 I)).comap (n5 I)=P
   rw [Ideal.comap_map_of_surjective _ uW,
     ← WK,Qy ,sup_eq_left.mpr hIP]
 let M:=Submonoid.powers (n5 I s)
 have hM:Ea (M:Set (R ⧸ I)) (p:Set (R ⧸ I)) := by
   have hle :M≤p.primeCompl:=Submonoid.powers_le.mpr (by
     change s∉p.comap (n5 I)
     rwa [hcomap])
   exact Set.disjoint_left.mpr fun _ ha hb=>hle ha hb
 let q:=p.map (cy (R ⧸ I) (TC I s))
 refine ⟨q,QL M _ p hp hM,?_⟩
 rw [ad2,← Ideal.comap_comap]
 change (q.under (R ⧸ I)).comap (n5 I)=P
 rw [show q.under (R ⧸ I)=p from
   G6 M _ hp hM,hcomap]
private def cam {R:Type*} [ox R] {I P:lI R}
   [P.IsPrime] {s :R} (q:lI (TC I s)) [q.IsPrime]
   (hP:q.comap (ad2 I s)=P) :
   p9 q ≃+*
     (p9 P ⧸ I.map (cy R (p9 P))) := by
 let p:=q.comap (cy (R ⧸ I) (TC I s))
 letI:p.IsPrime :=Ideal.comap_isPrime _ q
 have hp:p.comap (n5 I)=P:=hP
 let A:=p9 P
 let C:=A ⧸ I.map (cy R A)
 have hmonoid :Xp (R ⧸ I) P.primeCompl=p.primeCompl:= by
   change P.primeCompl.map (n5 I)=p.primeCompl
   simpa only [hp] using
     p.map_primeCompl_comap_of_surjective (n5 I) uW
 letI:MS p.primeCompl C:=hmonoid ▸
   (Oc :MS (Xp (R ⧸ I) P.primeCompl) C)
 letI:MS p.primeCompl (p9 q) := by
   change IsLocalization.AtPrime (p9 q)
     (q.comap (cy (R ⧸ I) (TC I s)))
   infer_instance
 exact (IsLocalization.algEquiv p.primeCompl (p9 q) C).toRingEquiv
private theorem cGQ {A B:Type*} [ox A] [ox B]
  {I:lI A} {J:lI B} (e : (A ⧸ I) ≃+* (B ⧸ J)) :
  Module.length A (A ⧸ I)=Module.length B (B ⧸ J) := by
 rw [TZ (R:=A ⧸ I) uW,
  TZ (R:=B ⧸ J) uW]
 apply WithBot.coe_injective
 rw [Ts ,Ts]
 exact Order.krullDim_eq_of_orderIso (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm
end
end dnb
end
section
namespace cyA
open aR dN rW E7 Polynomial
open scoped Polynomial WithZero
private theorem dsS {k F:Type} [sH k] [sH F] [t6 k F]
   (hF:CurveField k F) {x :F} (hx :Transcendental k x) (y :F) :
   Hw (G7 k {x}) y := by
 obtain ⟨t,ht,hfinite⟩:=hF
 let:=hfinite
 have halg (z :F) :Hw (Algebra.adjoin k {t}) z :=
   IntermediateField.isAlgebraic_adjoin_iff.mp
     (Algebra.IsAlgebraic.isAlgebraic (R:=G7 k {t}) z)
 have ht' : Hw (Algebra.adjoin k {x}) t:= by
   simpa using IsAlgebraic.adjoin_singleton ht hx (halg x)
 rw [IntermediateField.isAlgebraic_adjoin_iff]
 apply IsAlgebraic.adjoin_of_forall_isAlgebraic (s := {t}) (t := {x}) _ (halg y)
 intro z hz
 have hzt:z=t:=hz.1
 simpa only [hzt] using ht'
private theorem bLs {F:Type} [sH F] (w:Valuation F ℤᵐ⁰)
   (x :w.valuationSubring) :
   Ze w.valuationSubring x=0↔w (x :F)<1 :=
 (IsLocalRing.residue_eq_zero_iff x).trans (w.mem_maximalIdeal_iff (a :=x))
private theorem cfl {k F:Type} [sH k] [IsAlgClosed k]
    [sH F] [t6 k F] (hF:CurveField k F) (w:Valuation F ℤᵐ⁰)
    (hk :w.IsTrivialOn k) (hn : ∃ y :F,y≠0∧w y≠1)
    (x :F) (hx :w x≤1) :
    ∃ c:k,w (x-algebraMap k F c)<1 := by
  let:w.IsTrivialOn k :=hk
  let A:=w.valuationSubring
  let ι:k →+* A:=(cy k F).codRestrict A
    (fun c=>Valuation.IsTrivialOn.valuation_algebraMap_le_one w c)
  let ρ:=Ze A
  let:t6 k (Zh A) :=(ρ.comp ι).toAlgebra
  let u:A:=⟨x,hx⟩
  have hres :Hw k (ρ u) := by
    by_contra htrans
    have hpoly (p:k[X]) (hp:p≠0) :w (aeval x p)=1 := by
      let z :=p.eval₂ ι u
      have hz : (z :F)=aeval x p:=Bf p ι A.subtype u
      have hzres :ρ z≠0:= by
        intro hzero
        apply htrans
        refine ⟨p,hp,?_⟩
        change p.eval₂ (ρ.comp ι) (ρ u)=0
        rw [← Bf p ι ρ u]
        exact hzero
      rw [← hz]
      exact Ob z.2 (le_of_not_gt fun hlt=>hzres ((bLs w z).2 hlt))
    have htr :Transcendental k x := by
      rintro ⟨p,hp,hzero⟩
      have he :=hpoly p hp
      rw [hzero,qz] at he
      exact zero_ne_one he
    let B:=G7 k {x}
    let:w.IsTrivialOn B:=⟨by
      intro b hb
      have hb' : (b:F)≠0:= fun h=>hb (wY h)
      obtain ⟨p,q,hpq⟩:=(IntermediateField.mem_adjoin_simple_iff k (b:F)).1 b.2
      have hp:p≠0:= fun h=>hb' (by simp [hpq,h])
      have hq:q≠0:= fun h=>hb' (by simp [hpq,h])
      change w (b:F)=1
      rw [hpq,w.map_div,hpoly p hp,hpoly q hq,div_self one_ne_zero]⟩
    obtain ⟨y,hy,hvy⟩:=hn
    exact (Valuation.transcendental_of_ne_one B (v :=w) y hy hvy)
      (dsS hF htr y)
  let B:=G7 k {ρ u}
  let:G1 k B :=
    IntermediateField.isAlgebraic_adjoin_simple (isAlgebraic_iff_isIntegral.mp hres)
  have hB:=IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic B
  have hu:ρ u∈(⊥ : IntermediateField k (Zh A)) :=
    hB ▸ IntermediateField.mem_adjoin_simple_self k (ρ u)
  obtain ⟨c,hc⟩:=IntermediateField.mem_bot.mp hu
  refine ⟨c,(bLs w (u-ι c)).1 ?_⟩
  rw [qG]
  exact sub_eq_zero.mpr hc.symm
private theorem b4u {k F L:Type} [sH k] [sH F]
   [t6 k F] [sH L] (j:F →+* L) (a :L) (v :Valuation L ℤᵐ⁰)
   (ha :v a=1)
   (hres : ∀ x :F,v (j x)≤1 → ∃ c:k,v (j (x-algebraMap k F c))<1)
   (hfresh : ∀ q:k[X],q≠0→v (q.eval₂ (j.comp (cy k F)) a)=1)
   (g:F[X]) :
   v (g.eval₂ j a)=g.support.sup (fun i=>v (j (g.coeff i))) := by
 classical
 by_cases hg:g=0
 · simp [hg]
 obtain ⟨m,hm,hmax⟩ :=
   Wl g.support (nonempty_support_iff.mpr hg)
     (fun i=>v (j (g.coeff i)))
 let b:=g.coeff m
 have hb:b≠0:=mem_support_iff.mp hm
 have hvb:0<v (j b) :=v.pos_iff.mpr ((map_ne_zero j).2 hb)
 let d (i:ℕ) :=g.coeff i/b
 have hd (i:ℕ) :v (j (d i))≤1 := by
   by_cases hi:i∈g.support
   · dsimp only [d]
     rw [map_div₀,v.map_div,div_le_one₀ hvb]
     change v (j (g.coeff i))≤v (j (g.coeff m))
     rw [← hmax]
     exact Finset.le_sup (f := fun n=>v (j (g.coeff n))) hi
   · simp [d,notMem_support_iff.mp hi]
 choose c hc using fun i=>hres (d i) (hd i)
 have hcm:c m≠0:= by
   intro hz
   have h:=hc m
   simp [d,b,hb,hz] at h
 let q:k[X] := ∑ i∈g.support,monomial i (c i)
 have hqcoeff :q.coeff m=c m:= by
   simp [q,Gr,Np,hm]
 have hq:q≠0:= fun h=>hcm (by simpa [h] using hqcoeff.symm)
 let r :=j.comp (cy k F)
 let s := ∑ i∈g.support,j (d i)*a^i
 have hqeval :q.eval₂ r a = ∑ i∈g.support,r (c i)*a^i:= by
   simp only [q,eval₂_finsetSum,eval₂_monomial]
 have hdiff :v (s - q.eval₂ r a)<1 := by
   dsimp only [s]
   rw [hqeval,← Finset.sum_sub_distrib]
   apply v.map_sum_lt one_ne_zero
   intro i _
   rw [← sub_mul,nI,p6,ha,one_pow,mul_one]
   change v (j (d i) - j (cy k F (c i)))<1
   rw [← qG]
   exact hc i
 have hqv :=hfresh q hq
 have hdom:v (s - q.eval₂ r a)<v (q.eval₂ r a) :=lt_of_lt_of_eq hdiff hqv.symm
 have hs :v s=1 :=(v.map_eq_of_sub_lt hdom).trans hqv
 have hscale :g.eval₂ j a=j b*s := by
   dsimp only [s]
   rw [eval₂_eq_sum,sum_def,Dz]
   apply t4 rfl
   intro i _
   dsimp only [d]
   rw [← sS ,← nI,mul_div_cancel₀ _ hb]
 rw [hscale,nI,hs,mul_one]
 exact hmax.symm
theorem proof :E7.c5:= by
  intro R D v
  unfold a97
  by_cases h : ∀ x :D.Old,x≠0→v.value (D.Fl x)=1
  · exact v9 h
  right
  let w:=v.value.comap D.Fl
  have hk :w.IsTrivialOn ao:=⟨by
    intro c hc
    change v.value ((D.Fl.comp (cy ao D.Old)) c)=1
    rw [D.constants]
    exact v.on_constants (ni c) ((map_ne_zero ni).2 hc)⟩
  have hn : ∃ y :D.Old,y≠0∧w y≠1 := by
    obtain ⟨y,hy⟩:=not_forall.mp h
    exact ⟨y,(Classical.not_imp.mp hy).1,(Classical.not_imp.mp hy).2⟩
  have hfresh (q:ao[X]) (hq:q≠0) :
      v.value (q.eval₂ (D.Fl.comp (cy ao D.Old)) D.center)=1 := by
    have heval :q.eval₂ (D.Fl.comp (cy ao D.Old)) D.center =
        cy oq D.Fresh (j8 q) := by
      rw [D.constants,KD.center,← Bf ,
        ni,rI,← Bf ,eval₂_C_X]
    have hginj:qm j8 :=
      (cy lN oq).injective.comp
        (ze ao[X] lN)
    rw [heval]
    exact v.on_constants _ (map_ne_zero_iff j8 hginj |>.2 hq)
  have ha :v.value D.center=1 := by
    simpa only [eval₂_X] using hfresh nq Polynomial.X_ne_zero
  exact b4u D.Fl D.center v.value ha
    (cfl D.oldCurve w hk hn) hfresh
end cyA
end
section
set_option backward.isDefEq.respectTransparency false
namespace bju
noncomputable section
open MvPolynomial Qo
variable {F:Type*} [sH F]
def Wj (x :F) :nX (Fin 5) F →ₐ[F] nX (Fin 5) F :=
 pz ![C x,0,0,lz 3,lz 4]
theorem bs0 (x a b c d:F) (Q:nX (Fin 5) F)
  (hQ:yV Q) :aa2 x a b c d Q=Wj x Q:= by
 change eval₂ C (aDV x a b c d) Q=eval₂ C ![C x,0,0,lz 3,lz 4] Q
 apply eval₂_congr
 intro i e hi hc
 have ht:=bfT Q hQ e (mem_support_iff.mpr hc)
 have hin:=Finsupp.mem_support_iff.mp hi
 fin_cases i <;> simp_all [aDV]
def XD (q:ℕ) :nX (Fin 5) F →ₐ[F] lJ F :=
 pz ![0,0,0,nq,nq ^q]
theorem bFp (q:ℕ) (x :F) (Q:nX (Fin 5) F) :
  (graph q Q).eval (lV x)=XD q (Wj x Q) := by
 have heq : (vh (lV x)).comp (graph (F:=F) q).toRingHom =
    (XD q).toRingHom.comp (Wj x).toRingHom:= by
  apply pU
  · intro a
    simp [graph,XD,Wj,Polynomial.algebraMap_apply]
  · intro i
    fin_cases i <;> simp [graph,XD,Wj]
 exact oZ heq Q
end
end bju
end
section
namespace baD
open qQ Polynomial
theorem eam (F:bQR) (y v :HR) (k :ℕ)
   (h : ∀ a b:ℕ,a+b<k →
     (qM a ((qM b F).eval (C v))).eval y=0) :
   F∈b20 y v^k := by
 let I:=b20 y v
 let yDiff :=nq (R:=HR) - C y
 let vDiff :=nq (R:=lJ HR) - C (C v)
 have hY:C yDiff∈I:=t9 (by simp [yDiff])
 have hV:vDiff∈I:=t9 (by simp [vDiff])
 suffices hsum: (u8 (C v) F).sum (fun b B=>C B*vDiff^b)∈I ^k by
   simpa only [vDiff,sum_taylor_eq] using hsum
 unfold P7
 apply Ideal.sum_mem
 intro b _
 let B:=(u8 (C v) F).coeff b
 change C B*vDiff^b∈I ^k
 have hB: (u8 y B).sum (fun a c=>C c*yDiff^a)=B :=
   sum_taylor_eq B y
 rw [← hB]
 unfold P7
 rw [vG,Qx]
 apply Ideal.sum_mem
 intro a _
 rw [nI,p6,sS]
 by_cases hab:a+b<k
 · have hc: (u8 y B).coeff a=0:= by
     simpa only [B,taylor_coeff] using h a b hab
   simp [hc]
 · apply KA
   apply Ideal.pow_le_pow_right (le_of_not_gt hab)
   rw [Ideal.IsTwoSided.pow_add]
   exact Ideal.mul_mem_mul (SM hY a) (SM hV b)
end baD
end
