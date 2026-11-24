import ProximityPrize.SubmissionLower.X
import ProximityPrize.SubmissionLower.Y
import ProximityPrize.SubmissionLower.G
set_option Elab.async false
open _root_ renaming AdjoinRoot→zd,AdjoinRoot.mk→MK,AdjoinRoot.of→Kz,Algebra→wB,Algebra.TensorProduct.quotIdealMapEquivTensorQuot→UP,Algebra.algebraMap→lJ,Algebra.smul_def→NX,B8.Exponent→ Iw,CommRing→ ov,CommSemiring→GB,DecidableEq→xL,Derivation→pL,Dr.ChamberBox→pG,Dr.capCoeff→ oZ,Dr.capExponents→ oD,Dr.dimension→ oY,DualNumber→Vz,ENNReal.ofReal→Hw,Equiv.symm_apply_apply→zwn,Field→uJ,Fin.castSucc→xm,Fin.castSucc_ne_last→JK,Fin.last→yJ,Fin.sum_univ_four→JM,Finite→qU,Finite.exists_le→SM,Finite.to_wellFoundedGT→XB,Finset→nX,Finset.induction_on→zcw,Finset.le_sup→TZ,Finset.mem_singleton→Sd,Finset.mem_univ→FR,Finset.mul_sum→zg,Finset.prod_congr→Mz,Finset.prod_nonneg→zni,Finset.single_le_sum→zfK,Finset.sum_add_distrib→wR,Finset.sum_congr→qJ,Finset.sum_empty→TH,Finset.sum_eq_single→ IU,Finset.sum_eq_single_of_mem→VS,Finset.sum_eq_zero→C5,Finset.sum_ite_eq'→Vl,Finset.sum_le_sum→FK,Finset.sum_nonneg→zlo,Finsupp.finite_of_degree_le→XJ,Finsupp.induction_linear→Yi,Finsupp.mapDomain→Zg
open _root_ renaming Finsupp.single→ze,Finsupp.single_apply→OJ,Finsupp.weight→Pj,Finsupp.weight_eq_sum→Xu,Finsupp.weight_single→zTy,Finsupp.weight_sub_single_add→zpI,Fintype→sI,Fintype.card_fin→UZ,Fintype.equivFin→PM,Fintype.ofFinite→FQ,Function.Injective→qz,Function.Surjective→t7,Function.iterate_succ_apply'→G7,Ideal→aU,Ideal.Quotient.eq_zero_iff_mem→t3,Ideal.Quotient.factor→Fz,Ideal.Quotient.factor_mk→Eg,Ideal.Quotient.factor_surjective→WD,Ideal.Quotient.factorₐ→G0,Ideal.Quotient.mk→mD,Ideal.Quotient.mk_surjective→zf,Ideal.Quotient.mkₐ→zvR,Ideal.comap_map_of_bijective→zFA,Ideal.comap_map_of_surjective→G5,Ideal.comap_mono→xu,Ideal.comap_top→Nr,Ideal.eq_of_le_of_height_le→zKE,Ideal.exists_minimalPrimes_le→Cy,Ideal.height_add_one_le_of_lt_of_isPrime→Mk,Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes→zx8,Ideal.height_le_ringKrullDim_of_isPrime→ztp,Ideal.height_under_le_height→zJf,Ideal.le_colon→Rm,Ideal.map_comap_of_surjective→LP,Ideal.map_le_iff_le_comap→JQ,Ideal.map_map→z7,Ideal.map_span→uz,Ideal.map_sup→uW,Ideal.map_top→Nq,Ideal.mem_map_of_mem→yL,Ideal.mem_span_singleton_self→th,Ideal.mem_span_singleton_sup→Gk,Ideal.mem_sup_left→zKg,Ideal.mem_sup_right→u9,Ideal.minimalPrimes_comap_of_surjective→X8,Ideal.quotientMap→X4,Ideal.quotientMapₐ→WX,Ideal.span→cy
open _root_ renaming Ideal.span_singleton_le_iff_mem→Ea,Ideal.subset_span→Re,IsFractionRing.injective→GF,IsLeftRegular→vk,IsLocalRing.maximalIdeal→u8,IsLocalRing.maximalIdeal.isMaximal→G6,IsLocalization.Away.invSelf→Up,IsLocalization.Away.lift→ztx,IsLocalization.Away.lift_eq→zaz,IsLocalization.Away.surj→zQH,IsLocalization.map_units→Kl,IsLocalization.minimalPrimes_map→zMt,IsLocalization.mk'_mem_map_algebraMap_iff→zNj,IsNoetherianRing→LO,IsRelPrime→S1,IsScalarTower.algebraMap_eq→MO,IsSimpleModule→KA,IsUnit→uh,LinearEquiv.ofInjective→zjT,LinearMap.finrank_le_finrank_of_injective→NZ,LinearMap.ker→z8,LinearMap.mem_ker→zeS,LinearMap.mulLeft→zzN,LinearMap.range→v9,LinearMap.smulRight_apply→Xp,LinearOrder.lift'→Z0,List.mem_cons_of_mem→zrw,List.mem_cons_self→TI,Localization.AtPrime→vH,Localization.AtPrime.map_eq_maximalIdeal→ Il,Localization.Away→zUF,MeasurableSet→Mj,Module.Finite→QL,Module.Flat→Pc,Module.finrank→Gr,Module.length→p5,Module.length_eq_add_of_exact→zit,Module.length_eq_one→LR,Module.length_eq_zero→ II,Module.length_pos→Zt,MonomialOrder→KH,MonomialOrder.degLex→zwf,MulZeroClass.mul_zero→u5,MulZeroClass.zero_mul→zi,MvPolynomial→lz,MvPolynomial.C→p7,MvPolynomial.X→nI,MvPolynomial.affineDegree→qx
open _root_ renaming MvPolynomial.affineHilbertFunction→sH,MvPolynomial.affineHilbertPolynomial→lV,MvPolynomial.affineHilbertPolynomial_top→J4,MvPolynomial.algebraMap_eq→SC,MvPolynomial.coeff_C→RD,MvPolynomial.coeff_monomial→Pv,MvPolynomial.coeff_sum→zqN,MvPolynomial.comp_eval₂Hom→zKt,MvPolynomial.degreeOf_eq_sup→zXj,MvPolynomial.eval→ oy,MvPolynomial.eval_map→znM,MvPolynomial.eval_rename→ZJ,MvPolynomial.eval₂→Bf,MvPolynomial.eval₂Hom→Au,MvPolynomial.eval₂Hom_C→S2,MvPolynomial.eval₂Hom_X'→Ww,MvPolynomial.eventually_eval_affineHilbertPolynomial→vl,MvPolynomial.eventually_eval_affineHilbertPolynomial_nonneg→Pk,MvPolynomial.exists_eval_affineHilbertPolynomial→zQf,MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree→PA,MvPolynomial.hom_eval₂→Te,MvPolynomial.homogeneousComponent→Kh,MvPolynomial.homogeneousSubmodule→NI,MvPolynomial.induction_on→Yo,MvPolynomial.map→z9,MvPolynomial.mem_support_iff→zuk,MvPolynomial.mem_vars_rename→zcz,MvPolynomial.mk_mem_quotientDegreeLE→yo,MvPolynomial.monomial→pU,MvPolynomial.monomialMap→vw,MvPolynomial.monomialMap_mem_restrictSupport_nsmul→ZK,MvPolynomial.monomialMap_surjective→Gj,MvPolynomial.monomialPoint→G2,MvPolynomial.monomialPoint_mem_zeroLocus_comap_iff→Zh,MvPolynomial.monomial_mul_monomial→Lf,MvPolynomial.natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton→Ye,MvPolynomial.natDegree_affineHilbertPolynomial_comap_of_surjective→GY,MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le→t9,MvPolynomial.optionEquivLeft→Wl,MvPolynomial.pderiv_eq_zero_of_notMem_vars→zUp,MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one→C9,MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le→zWJ,MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime→KI,MvPolynomial.quotientDegreeLE→pz,MvPolynomial.quotientDegreeLE_mono→ IT,MvPolynomial.rename→zk,MvPolynomial.rename_X→Y4,MvPolynomial.restrictSupport→xI
open _root_ renaming MvPolynomial.restrictSupport_eq_span→ In,MvPolynomial.restrictSupport_mono→VC,MvPolynomial.ringHom_ext→FV,MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite→zmx,MvPolynomial.support_X→RC,MvPolynomial.support_map_subset→Zf,MvPolynomial.totalDegree_eq→zgn,MvPolynomial.zeroLocus→xW,Nat.add_le_add→G1,Nat.add_le_add_right→VH,Nat.add_sub_of_le→zp3,Nat.card_coe_set_eq→zPH,Nat.card_eq_fintype_card→zey,Nat.card_fin→R9,Nat.cast_add→Et,Nat.cast_mul→Kp,Nat.cast_nonneg→Pf,Nat.cast_one→Yc,Nat.eq_zero_of_le_zero→za7,Nat.factorial_succ→WY,Nat.le_add_left→Ok,Nat.le_add_right→yQ,Nat.le_of_lt_succ→UY,Nat.lt_succ_of_le→Zi,Nat.mul_le_mul_left→vi,Pi.add_apply→SL,Pi.single_apply→LQ,Polynomial→vj,Polynomial.C→qm,Polynomial.X→Kv,Polynomial.coeff_eq_zero_of_natDegree_lt→zE,Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le→EP,Polynomial.coeff_map→Ee,Polynomial.coeff_monomial_of_ne→Un,Polynomial.coeff_natDegree→Vq,Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg→RP,Polynomial.coeff_taylor_of_natDegree_le→Ob,Polynomial.derivative→wY,Polynomial.eq_zero_of_hasseDeriv_eq_zero→zHO,Polynomial.evalRingHom→yl,Polynomial.eval_add→WK,Polynomial.eval₂RingHom→zqg,Polynomial.finsetSum_coeff→Np,Polynomial.hasseDeriv→ oz,Polynomial.hasseDeriv_eq_zero_of_lt_natDegree→zrQ,Polynomial.leadingCoeff→PD,Polynomial.mapRingHom→vG,Polynomial.map_id→zei
open _root_ renaming Polynomial.map_sum→zWe,Polynomial.map_taylor→zla,Polynomial.monomial→Df,Polynomial.natDegree_C_mul_X→zK5,Polynomial.natDegree_le_of_eventually_eval_natCast_le→Xo,Polynomial.natDegree_taylor→zm,Polynomial.preHilbertPoly→zcb,Polynomial.ringHom_ext→Qw,Polynomial.taylor→zS,Polynomial.taylor_eval→G3,PrimeSpectrum→nq,PrimeSpectrum.asIdeal→zyo,PrimeSpectrum.ext→Xx,RingHom.comap_ker→G4,RingHom.comp_apply→HZ,RingHom.congr_fun→yU,RingHom.ext→zh,RingHom.id→GR,RingHom.ker→p9,RingHom.ker_isPrime→Oc,Set.Finite.mem_toFinset→zih,Set.InjOn→Kc,Set.image_image→SU,Set.image_singleton→vZ,Set.ncard_insert_le→zGl,SetLike.exists_of_lt→zxV,Submodule→JW,Submodule.add_mem→zcy,Submodule.exists_forall_notMem_of_forall_ne_top→zsi,Submodule.map_mono→Pr,Submodule.map_span→MS,Submodule.mem_bot→zLn,Submodule.mem_colon_singleton→ztS,Submodule.mem_top→Qx,Submodule.span_le→Sv,Submodule.sum_mem→VO,Subtype.ext→t6,Subtype.val→Xg,TrivSqZeroExt.ext→G8,Tx.Supported→pC,WellFounded.induction→EK,aR.Shape→lI,aR.Shape.plus→y5,add_comm→FU,add_le_add→Nj,add_mul→N0,add_zero→v8,associatedPrimes→Ar
open _root_ renaming associatedPrimes.finite→Wm,congrArg→qy,congrFun→Ml,dN.GeoField→ ox,dN.GeoJets→c9,dN.separant→ oj,dite_eq_left→Aa,div_nonneg→NW,finProdFinEquiv→G9,finSuccEquivLast→SD,finSuccEquivLast_last→Ze,finrank_top→Vs,intervalIntegral.integral_congr→P7,ite_eq_left→x7,ite_eq_right→t4,le_add_of_nonneg_right→Qy,le_antisymm→sS,le_rfl→vh,le_sup_left→p6,lt_of_le_of_ne→wA,map_add→t8,map_eq_zero_iff→Ts,map_mul→ oK,map_natCast→RJ,map_ne_zero_iff→WW,map_one→C4,map_pow→Du,map_sub→Dv,map_sum→Gi,map_zero→pQ,measurableSet_Icc→zdy,min_le_left→F9,min_le_right→Fa,mul_add→zR,mul_assoc→yB,mul_comm→qG,mul_le_mul_of_nonneg_left→SW,mul_left_comm→NY,mul_nonneg→XG,mul_one→Dw,nsmul_eq_mul→Mw,one_mul→t5,rW.dimension→ oq,ringKrullDim→Gn,ringKrullDim_eq_zero_of_field→zZT,smul_eq_mul→Dz,sup_comm→Av,sup_le→zc
open _root_ renaming wH.Lower→n5,wH.localColength→qM,wellFounded_gt→Ef
set_option autoImplicit true
section
namespace K1_13_7_6
noncomputable section
open aR wH MvPolynomial
def c1 :Prop :=
  ∀ {σ:Type} [qU σ] (φ:lz σ cH →ₐ[cH] n5),
    t7 φ →
    ∀ (p:nq n5) (L:lz σ cH),
      L.totalDegree≤1→φ L∉p.asIdeal →
      ∀ qs :nX (nq n5),
        (∀ q∈qs,q.asIdeal∈(ke p (φ L)).minimalPrimes) →
        (∀ q∈qs,qM q (ke p (φ L)) < ⊤) →
        a3c (aGW φ) p (φ L) qs≤aGW φ p
def c2 :Prop :=
  ∀ (f g h:n5) (D:nq n5→ℚ),
    (∀ q,0≤D q) →
    (∀ (y :Sz) (q:nq n5),q.asIdeal=oF y→1≤D q) →
    (∀ (t:n5),t∈({f,g,h} : Set n5) →
      ∀ (p:nq n5),t∉p.asIdeal →
        ∀ qs :nX (nq n5),
          (∀ q∈qs,q.asIdeal∈(ke p t).minimalPrimes) →
          (∀ q∈qs,qM q (ke p t) < ⊤) →
          a3c D p t qs≤D p) →
    ∀ (points :nX Sz) (w:ℕ),
      (∀ y∈points,∃ q:nq n5 ,
        q.asIdeal=oF y∧q.asIdeal∈(cy {f,g,h}).minimalPrimes ∧
        (w:ℕ∞)≤qM q (cy {f,g,h}) ∧
        qM q (cy {f,g,h}) < ⊤) →
      (points.card:ℚ)*w≤D zeroPrime
end
end K1_13_7_6
end
section
namespace ML
noncomputable section
variable {R:Type*} [ov R]
theorem bdz [LO R] {J:aU R} (hJ:J ≠ ⊤) :
  ∃ (a :R) (Q:aU R),a∉J∧Q.IsPrime ∧ ∀ x :R,x*a∈J↔x∈Q:= by
 let _:=Ideal.Quotient.nontrivial_iff.mpr hJ
 obtain ⟨Q,hQ,-⟩:=exists_le_isAssociatedPrime_of_isNoetherianRing R
  (1 :R ⧸ J) one_ne_zero
 obtain ⟨hp,z,hz⟩:=isAssociatedPrime_iff.mp hQ
 obtain ⟨a,rfl⟩:=zf z
 have hann (x :R) :x*a∈J↔x∈Q:= by
  rw [hz,ztS,zLn]
  change x*a∈J↔mD J (x*a)=0
  exact Ideal.Quotient.eq_zero_iff_mem.symm
 refine ⟨a,Q,fun ha=>hp.ne_top (Q.eq_top_of_isUnit_mem (hann 1 |>.mp ?_) isUnit_one),
  hp,hann⟩
 simpa only [t5] using ha
variable {k :Type*} [ov k] [wB k R]
def afC {J Q:aU R} {a :R} (ha : ∀ x :R,x*a∈J↔x∈Q) :
    (R ⧸ Q) →ₗ[k] R ⧸ J :=
  (Q.restrictScalars k).liftQ
    ((zvR k J).toLinearMap ∘ₗ zzN k a) fun x hx=> by
      change mD J (a*x)=0
      rw [qG]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((ha x).mpr hx)
@[simp]
theorem aNH {J Q:aU R} {a :R} (ha : ∀ x :R,x*a∈J↔x∈Q) (x :R) :
 afC (k :=k) ha (mD Q x)=mD J (a*x) :=rfl
theorem aUw {J Q:aU R} {a :R} (ha : ∀ x :R,x*a∈J↔x∈Q) :
  qz (afC (k :=k) ha) := by
 refine (LinearMap.ker_eq_bot.mp ?_)
 ext z
 obtain ⟨x,rfl⟩:=zf z
 rw [zeS,aNH,zLn,t3 ,
  t3 ,qG,ha]
theorem bFP {J Q:aU R} {a :R} (ha : ∀ x :R,x*a∈J↔x∈Q) :
   Function.Exact (afC (k :=k) ha)
     (G0 k (p6:J≤J ⊔ cy {a})).toLinearMap:= by
 intro z
 obtain ⟨x,rfl⟩:=zf z
 change mD (J ⊔ cy {a}) x=0 ↔
   mD J x∈v9 (afC (k :=k) ha)
 rw [t3 ,Av J,Gk]
 constructor
 · rintro ⟨y,b,hb,rfl⟩
   exact ⟨mD Q y,by simp [t8 ,Ideal.Quotient.eq_zero_iff_mem.mpr hb,qG]⟩
 · rintro ⟨z,hz⟩
   obtain ⟨y,rfl⟩:=zf z
   rw [aNH,qG] at hz
   have hb:x - y*a∈J:=Ideal.Quotient.eq_zero_iff_mem.mp
     (by rw [Dv,hz,sub_self])
   exact ⟨y,x - y*a,hb,add_sub_cancel _ _⟩
theorem brK {J Q:aU R} {a :R} (ha : ∀ x :R,x*a∈J↔x∈Q) :
  p5 R (R ⧸ J) =
    p5 R (R ⧸ Q)+Module.length R (R ⧸ (J ⊔ cy {a})) :=
 zit _ _ (aUw (k :=R) ha)
  (WD p6) (bFP (k :=R) ha)
end
end ML
end
section
namespace ML
noncomputable section
open Filter MvPolynomial Polynomial
variable {k σ:Type*} [uJ k] [qU σ]
theorem emZ {J K Q:aU (lz σ k)} {a :lz σ k}
   (hJK:J≤K) (haK:a∈K) (ha : ∀ x,x*a∈J↔x∈Q)
   {N :ℕ} (hN :a.totalDegree≤N) :
   sH K N+affineHilbertFunction Q (N-a.totalDegree) ≤
     affineHilbertFunction J N := by
 let π:=((G0 k hJK).toLinearMap.domRestrict (pz J N)).codRestrict
   (pz K N) fun x=> by
     obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp x.2
     change Fz hJK x∈pz K N
     rw [← hpx,Eg]
     exact yo hp
 have hsurj:t7 π:= by
   intro y
   obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.2
   exact ⟨⟨mD J p,yo hp⟩,t6 hpy⟩
 let μ:=((afC (k :=k) ha).domRestrict (pz Q (N-a.totalDegree))).codRestrict
   (pz J N) fun x=> by
     obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp x.2
     change afC ha x∈pz J N
     rw [← hpx,aNH]
     exact yo ((totalDegree_mul a p).trans (by omega))
 have hμ : ∀ x,μ x∈z8 π:= by
   intro x
   obtain ⟨p,-,hpx⟩:=mem_quotientDegreeLE.mp x.2
   rw [zeS]
   apply t6
   change Fz hJK (afC ha x)=0
   rw [← hpx,aNH,Eg]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr (K.mul_mem_right _ haK)
 have hinj:qz (μ.codRestrict (z8 π) hμ) := fun x y hxy =>
   t6 (aUw ha (qy (fun z=>(z.val.val :MvPolynomial σ k ⧸ J)) hxy))
 have hker :=NZ hinj
 have hrank :=π.finrank_range_add_finrank_ker
 rw [LinearMap.range_eq_top.mpr hsurj,Vs] at hrank
 unfold sH
 omega
theorem a4G {J K Q:aU (lz σ k)} {a :lz σ k}
   (hJK:J≤K) (haK:a∈K) (ha : ∀ x,x*a∈J↔x∈Q)
   {d:ℕ} (hd: (lV J).natDegree≤d) :
   (lV K).coeff d+(lV Q).coeff d ≤
     (lV J).coeff d:= by
 have hJQ:J≤Q:= fun x hx=>(ha x).mp (J.mul_mem_right _ hx)
 have hKd:=(t9 hJK).trans hd
 have hQd:=(t9 hJQ).trans hd
 let b:=a.totalDegree
 let P:ℚ[X] :=lV K+taylor (-(b:ℚ)) (lV Q)
 have hPd:P.natDegree≤d :=
   (natDegree_add_le_of_le hKd ((zm _ _).trans_le hQd)).trans (max_self d).le
 have hcoeff :P.coeff d =
     (lV K).coeff d+(lV Q).coeff d:= by
   simp only [P,coeff_add,Ob _ hQd]
 rw [← hcoeff]
 refine EP hPd hd ?_
 obtain ⟨T,hT⟩:=zQf Q
 filter_upwards [vl J,
   vl K,eventually_ge_atTop (T+b)] with N hJ hK hTN
 have hbN :b≤N := by omega
 simp only [P,WK,G3]
 rw [hJ,hK,← sub_eq_add_neg,← Nat.cast_sub hbN,hT _ (by omega)]
 exact_mod_cast emZ hJK haK ha hbN
end
end ML
end
section
namespace ML
noncomputable section
open wH
theorem bdE {R S:Type*} [ov R] [ov S] [wB R S]
  (M:Submonoid R) [IsLocalization M S] {J Q:aU R} {a :R}
  (ha : ∀ x :R,x*a∈J↔x∈Q) (z :S) :
  z*lJ R S a∈J.map (lJ R S)↔z∈Q.map (lJ R S) := by
 obtain ⟨x,s,rfl⟩:=IsLocalization.exists_mk'_eq M z
 rw [← IsLocalization.mk'_one (M:=M) S a,← IsLocalization.mk'_mul,
  zNj,zNj]
 simp only [← yB,ha]
theorem b72 {B J Q:aU n5} (hBJ:B≤J) (hQ:Q.IsPrime)
    {a :n5} (ha : ∀ x :n5 ,x*a∈J↔x∈Q)
    {q:nq n5} (hq:q.asIdeal∈B.minimalPrimes) :
    qM q J=(if Q=q.asIdeal then 1 else 0) +
      qM q (J ⊔ cy {a}) := by
  classical
  let S:=vH q.asIdeal
  let f :n5 →+* S:=lJ n5 S
  have hmul :=brK (bdE (S:=S) q.asIdeal.primeCompl ha)
  change p5 S (S ⧸ J.map f)= _ +
    p5 S (S ⧸ (J ⊔ cy {a}).map f)
  rw [uW,uz ,vZ,hmul]
  congr 1
  by_cases h:Q=q.asIdeal
  · subst Q
    rw [x7 rfl]
    have he :q.asIdeal.map f=u8 S :=
      Il
    rw [he]
    have :KA S (S ⧸ u8 S) :=
      (isSimpleModule_iff_isCoatom.mpr (G6 _).1)
    exact LR S _
  · rw [t4 h]
    have hBQ:B≤Q:= fun x hx=>(ha x).mp (J.mul_mem_right _ (hBJ hx))
    have hnot : ¬ Q≤q.asIdeal:= fun hle=>h (hle.antisymm (hq.2 ⟨hQ,hBQ⟩ hle))
    obtain ⟨s,hs,hsq⟩:=Set.not_subset.mp hnot
    have hmap :Q.map f = ⊤ :=
      (Q.map f).eq_top_of_isUnit_mem (yL f hs)
        (Kl S (⟨s,hsq⟩:q.asIdeal.primeCompl))
    rw [hmap]
    exact II
end
end ML
end
section
namespace axg
noncomputable section
open dN vS B8 MvPolynomial
open scoped BigOperators
def c1 :Prop :=
  ∀ {σ:Type} [qU σ] (J Q:aU (lz σ ox))
    (a :lz σ ox),
    (∀ x,x*a∈J↔x∈Q) →
    ∀ d:ℕ,(lV J).natDegree≤d →
      (lV J).coeff d ≤
        (lV (J ⊔ cy {a})).coeff d +
          (lV Q).coeff d
def c2 :Prop :=
  ∀ (B:lS),Admissible B →
    ∀ (P:aU g9) (I:nX (Fin 5)),P.IsPrime →
      MH P I.card→0≤tW B P I
private theorem a3w {J Q:aU g9} {d:ℕ} (hJQ:J≤Q) (hJ:MH J d) :
   MH Q d :=
 (ringKrullDim_le_of_surjective _ (WD hJQ)).trans hJ
private theorem b9k (hadd:c1) {B:lS} (hB:Admissible B) {I:nX (Fin 5)}
    {J Q:aU g9} (hJ:MH J I.card) {a :g9}
    (ha : ∀ x,x*a∈J↔x∈Q) :
    tW B J I=tW B (i9 J a) I+tW B Q I:= by
  classical
  have hdiag (U:nX (Fin 5)) :
      let f :=vw ox (H7 B (fun i=>if i∈U then 2 else 1))
      (lV (J.comap f)).coeff I.card =
        (lV ((i9 J a).comap f)).coeff I.card +
          (lV (Q.comap f)).coeff I.card:= by
    let t (i:Fin 5) :ℕ:=if i∈U then 2 else 1
    have ht : ∀ i,0<t i:= fun i=> by by_cases hi:i∈U <;> simp [t,hi]
    let f :=vw ox (H7 B t)
    have hf :t7 f :=bEd hB ht
    obtain ⟨A,hA⟩:=hf a
    change (lV (J.comap f)).coeff I.card =
      (lV ((i9 J a).comap f)).coeff I.card +
        (lV (Q.comap f)).coeff I.card
    have hsection : (i9 J a).comap f=J.comap f ⊔ cy {A} := by
      have hk :J.comap f ⊔ cy {A} =
          (J.comap f ⊔ cy {A}) ⊔ Ideal.comap f ⊥ :=
        (sup_eq_left.mpr ((xu bot_le).trans p6)).symm
      calc
        (i9 J a).comap f=((J.comap f ⊔ cy {A}).map f).comap f := by
          rw [uW,LP f hf,uz ,
            vZ,hA,i9]
        _=J.comap f ⊔ cy {A} :=
          (G5 f hf _).trans hk.symm
    have hAann (x :lz (H7 B t) ox) :
        x*A∈J.comap f↔x∈Q.comap f := by
      simp only [Ideal.mem_comap,oK,hA,ha]
    have hd:=aNi hB hJ ht
    have hlow:=ML.a4G
      (J:=J.comap f) (K:=J.comap f ⊔ cy {A})
      p6 (u9 (th A)) hAann hd
    rw [hsection]
    exact sS (hadd _ _ A hAann _ hd) hlow
  unfold tW
  rw [← add_div,← wR]
  congr 1
  apply qJ rfl
  intro U _
  rw [hdiag U,zR]
private theorem b8a {H J Q P:aU g9} (hHJ:H≤J) (hQ:Q.IsPrime)
    {a :g9} (ha : ∀ x,x*a∈J↔x∈Q) (hP:H.IsMinimalPrime P) :
    Ro J P hP.isPrime =
      (if Q=P then 1 else 0)+Ro (i9 J a) P hP.isPrime := by
  classical
  have :=hP.isPrime
  let A:=vH P
  let f :g9 →+* A:=lJ g9 A
  have hf :=ML.brK
    (ML.bdE (S:=A) P.primeCompl ha)
  change p5 A (A ⧸ J.map f)= _ +
    p5 A (A ⧸ (J ⊔ cy {a}).map f)
  rw [uW,uz ,vZ,hf]
  congr 1
  by_cases h:Q=P
  · subst Q
    rw [x7 rfl]
    have he :P.map f=u8 A:=Il
    rw [he]
    have :KA A (A ⧸ u8 A) :=
      isSimpleModule_iff_isCoatom.mpr (G6 A).1
    exact LR A _
  · rw [t4 h]
    have hHQ:H≤Q:= fun x hx=>(ha x).mp (J.mul_mem_right _ (hHJ hx))
    have hnot : ¬ Q≤P:= fun hle=>h (hle.antisymm (hP.2 ⟨hQ,hHQ⟩ hle))
    obtain ⟨s,hs,hsp⟩:=Set.not_subset.mp hnot
    have he :Q.map f = ⊤ :=
      (Q.map f).eq_top_of_isUnit_mem (yL f hs)
        (Kl A (⟨s,hsp⟩:P.primeCompl))
    rw [he]
    exact II
private def weight (J P:aU g9) :ℕ:= by
 classical
 exact if h:P.IsPrime then (Ro J P h).toNat else 0
private theorem VB {J P:aU g9} (h:P.IsPrime) :
  weight J P=(Ro J P h).toNat := by
 rw [weight,Aa h]
private theorem length_top (P:aU g9) (hP:P.IsPrime) :
  Ro ⊤ P hP=0:= by
 have :=hP
 let A:=vH P
 change p5 A (A ⧸ (⊤ : aU g9).map (lJ g9 A))=0
 rw [Nq]
 exact II
private theorem bZA (hadd:c1) (hpos :c2) {B:lS} (hB:Admissible B)
    {H :aU g9} {I:nX (Fin 5)} (hH :MH H I.card)
    {ι:Type} (S:nX ι) {C:ι→ aU g9}
    (hinj:Kc C (S:Set ι)) (hp : ∀ a∈S,H.IsMinimalPrime (C a))
    (J:aU g9) (hHJ:H≤J) :
    (∀ a (ha :a∈S),Ro J (C a) (hp a ha).isPrime ≠ ⊤) ∧
      (∑ a∈S,(weight J (C a) :ℚ)*tW B (C a) I)≤tW B J I:= by
  classical
  let D (P:aU g9) :=tW B P I
  change _∧(∑ a∈S,(weight J (C a) :ℚ)*D (C a))≤D J
  revert hHJ
  induction J using EK (Ef (α:=aU g9)) with
  | h J ih =>
    intro hHJ
    by_cases hJ:J = ⊤
    · subst J
      have hz (a :ι) (ha :a∈S) :Ro ⊤ (C a) (hp a ha).isPrime=0 :=
        length_top _ (hp a ha).isPrime
      constructor
      · intro a ha
        simp [hz a ha]
      · have hs : (∑ a∈S,(weight ⊤ (C a) :ℚ)*D (C a))=0:= by
          apply C5
          intro a ha
          simp [VB (hp a ha).isPrime,hz a ha]
        rw [hs]
        simp [D,tW,J4]
    obtain ⟨a,Q,haJ,hQ,hann⟩:=ML.bdz hJ
    let K:=i9 J a
    have hJK:J≤K:=p6
    have haK:a∈K:=u9 (th a)
    have hlt:J<K:=wA hJK fun he=>haJ (he ▸ haK)
    have hHQ:H≤Q:= fun x hx=>(hann x).mp (J.mul_mem_right _ (hHJ hx))
    obtain ⟨hfinK,hboundK⟩:=ih K hlt (hHJ.trans hJK)
    have hstep (i:ι) (hi:i∈S) :
        Ro J (C i) (hp i hi).isPrime =
          (if Q=C i then 1 else 0)+Ro K (C i) (hp i hi).isPrime :=
      b8a hHJ hQ hann (hp i hi)
    have hDQ:0≤D Q:=hpos B hB Q I hQ (a3w hHQ hH)
    have hweight (i:ι) (hi:i∈S) :
        (weight J (C i) :ℚ)=(weight K (C i) :ℚ)+(if Q=C i then 1 else 0) := by
      rw [VB (hp i hi).isPrime,VB (J:=K) (hp i hi).isPrime,hstep i hi]
      split_ifs with hEq
      · rw [ENat.toNat_add (by simp) (hfinK i hi)]
        simp [FU ]
      · simp
    refine ⟨fun i hi => ?_,?_⟩
    · rw [hstep i hi]
      have hfinite : (if Q=C i then 1 else 0:ℕ∞) ≠ ⊤ := by
        split_ifs <;> simp
      exact WithTop.add_ne_top.mpr ⟨hfinite,hfinK i hi⟩
    · have hindicator : (∑ i∈S,if Q=C i then D Q else 0)≤D Q:= by
        by_cases hex : ∃ i∈S,Q=C i
        · obtain ⟨i,hi,he⟩:=hex
          rw [VS i hi,x7 he]
          intro j hj hji
          exact t4 fun hjQ=>hji (hinj hj hi (hjQ.symm.trans he))
        · rw [C5 (fun i hi=>t4 (fun h=>hex ⟨i,hi,h⟩))]
          exact hDQ
      calc
        _=(∑ i∈S,(weight K (C i) :ℚ)*D (C i)) +
            (∑ i∈S,if Q=C i then D Q else 0) := by
          rw [← wR]
          apply qJ rfl
          intro i hi
          rw [hweight i hi,N0]
          split_ifs with he
          · rw [← he,t5]
          · rw [zi]
        _≤D K+D Q:=Nj hboundK hindicator
        _=D J:=(b9k hadd hB (a3w hHJ hH) hann).symm
theorem of_children (h1 :c1) (h2 :c2) :B8.c2 := by
 intro B hB J I hJ ι S C w hinj h
 have hp (a :ι) (ha :a∈S) :J.IsMinimalPrime (C a) :=Exists.choose (h a ha)
 obtain ⟨hfin,hbudget⟩:=bZA h1 h2 hB hJ S hinj hp J vh
 refine le_trans (FK fun a ha => ?_) hbudget
 have hlen: (w a :ℕ∞)≤Ro J (C a) (hp a ha).isPrime :=Exists.choose_spec (h a ha)
 have hw:w a≤weight J (C a) := by
  rw [VB (hp a ha).isPrime]
  exact ENat.toNat_le_toNat hlen (hfin a ha)
 exact mul_le_mul_of_nonneg_right (by exact_mod_cast hw)
  (h2 B hB (C a) I (hp a ha).isPrime (a3w (hp a ha).le hJ))
end
end axg
end
section
namespace aA6
noncomputable section
open aR dN vS B8 MvPolynomial
abbrev alh (B:lS) :=(i:Fin 5)×Nl (B i)
def aeh {σ:Type} (slot:σ→Fin 5) (e :σ →₀ ℕ) (i:Fin 5) :ℕ :=
 e.sum fun v n=>if slot v=i then n else 0
def DL {σ:Type} (slot:σ→Fin 5) (bad:nX (σ →₀ ℕ))
    (u:Fin 5→ℕ) :ℕ :=
  {e :σ →₀ ℕ | aeh slot e=u ∧ ∀ b∈bad,¬ b≤e}.ncard
def a8E (B:lS) (P:aU g9) :
    lz (alh B) ox →ₐ[ox] lz (Fin 5) (g9 ⧸ P) :=
  MvPolynomial.aeval fun v =>
    pU (ze v.1 1) (mD P (pU v.2.val 1))
def Kx (B:lS) (P:aU g9) (u:Fin 5→ℕ) :
    JW ox (g9 ⧸ P) :=
  (xI ox (H7 B u)).map
    (zvR ox P).toLinearMap
def RM (B:lS) (P:aU g9) (t:Fin 5→ℕ) :
    aU (lz (H7 B t) ox) :=
  P.comap (vw ox (H7 B t))
end
end aA6
end
section
namespace bzM
noncomputable section
open ML
variable {R:Type*} [ov R]
private abbrev At (p:nq R) :=vH p.asIdeal
abbrev yC (p:nq R) (J:aU R) :ℕ∞ :=
 p5 (At p) (At p ⧸ J.map (lJ R (At p)))
private theorem fVL {J Q:aU R} {a d:R}
  (hfactor : ∀ x,x*a∈J↔x∈Q)
  (hdQ : ∀ x,d*x∈Q→x∈Q)
  (hdK : ∀ x,d*x∈J ⊔ cy {a} → x∈J ⊔ cy {a})
  (x :R) (hx :d*x∈J) :x∈J:= by
 have hxK:=hdK x (zKg hx)
 rw [Av J,Gk] at hxK
 obtain ⟨t,b,hb,rfl⟩:=hxK
 have hdt: (d*t)*a∈J:= by
  rw [show (d*t)*a=d*(t*a+b) - d*b by ring]
  exact J.sub_mem hx (J.mul_mem_left d hb)
 exact J.add_mem ((hfactor t).mpr (hdQ t ((hfactor (d*t)).mp hdt))) hb
private theorem dSD {J Q:aU R} {a d:R}
    (hfactor : ∀ x,x*a∈J↔x∈Q)
    (hdK : ∀ x,d*x∈J ⊔ cy {a} → x∈J ⊔ cy {a})
    (x :R) :x*a∈J ⊔ cy {d} ↔ x∈Q ⊔ cy {d} := by
  rw [Av J,Av Q,Gk,Gk]
  constructor
  · rintro ⟨t,b,hb,he⟩
    have ht:d*t∈J ⊔ cy {a} := by
      rw [show d*t=x*a - b by rw [← he]; ring]
      exact sub_mem (u9 (Ideal.mul_mem_left _ _ (th a)))
        (zKg hb)
    have htK:=hdK t ht
    rw [Av J,Gk] at htK
    obtain ⟨u,c,hc,rfl⟩:=htK
    refine ⟨u,x - u*d,(hfactor _).mp ?_,by ring⟩
    rw [show (x - u*d)*a=x*a - u*d*a by ring,← he,
      show (u*a+c)*d+b - u*d*a=c*d+b by ring]
    exact J.add_mem (J.mul_mem_right d hc) hb
  · rintro ⟨t,b,hb,rfl⟩
    exact ⟨t*a,b*a,(hfactor b).mpr hb,by ring⟩
private theorem cZg {J Q:aU R} {a s :R}
  (hfactor : ∀ x,x*a∈J↔x∈Q)
  (p:nq R) (hsQ:s∈Q) (hsp:s∉p.asIdeal) :
  (J ⊔ cy {a}).map (lJ R (At p))=J.map (lJ R (At p)) := by
 let f :R →+* At p:=lJ R (At p)
 change (J ⊔ cy {a}).map f=J.map f
 rw [uW,uz ,vZ,sup_eq_left,
  Ea]
 have hunit :uh (f s) :=
  Kl (At p) (⟨s,hsp⟩:p.asIdeal.primeCompl)
 apply ((J.map f).unit_mul_mem_iff_mem hunit).mp
 exact (bdE p.asIdeal.primeCompl hfactor (f s)).mpr
  (yL f hsQ)
private theorem dNr (r :nq R) {J:aU R} {a :R}
  (hfactor : ∀ x,x*a∈J↔x∈r.asIdeal) :
  yC r J=1+yC r (J ⊔ cy {a}) := by
 let S:=At r
 let f :R →+* S:=lJ R S
 change p5 S (S ⧸ J.map f) =
  1+Module.length S (S ⧸ (J ⊔ cy {a}).map f)
 rw [uW,uz ,vZ,
  brK (bdE r.asIdeal.primeCompl hfactor)]
 congr 1
 have he :r.asIdeal.map f=u8 S :=
  Il
 rw [he]
 let:KA S (S ⧸ u8 S) :=
  isSimpleModule_iff_isCoatom.mpr (G6 S).1
 exact LR S _
private theorem gnO (r p:nq R) (hrp:r.asIdeal≤p.asIdeal)
    {J:aU R} {a D:R} (hfactor : ∀ x,x*a∈J↔x∈r.asIdeal)
    (hD:D∉r.asIdeal)
    (hreg : ∀ x :At p,lJ R (At p) D *x ∈
      (J ⊔ cy {a}).map (lJ R (At p)) →
        x∈(J ⊔ cy {a}).map (lJ R (At p))) :
    (∀ x :At p,lJ R (At p) D *x∈J.map (lJ R (At p)) →
      x∈J.map (lJ R (At p))) ∧
    (D∈p.asIdeal→1+yC p ((J ⊔ cy {a}) ⊔ cy {D}) ≤
      yC p (J ⊔ cy {D})) := by
  let S:=At p
  let f :R →+* S:=lJ R S
  let L:=J.map f
  let Q:=r.asIdeal.map f
  let K:=L ⊔ cy {f a}
  have hmap (I:aU R) (z :R) :
      (I ⊔ cy {z}).map f=I.map f ⊔ cy {f z} := by
    rw [uW,uz ,vZ]
  have hann : ∀ x :S,x*f a∈L↔x∈Q :=
    bdE p.asIdeal.primeCompl hfactor
  have hQprime :Q.IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime p.asIdeal hrp
  have hdQ:f D∉Q:= by
    change D∉(r.asIdeal.map f).under R
    rwa [Ideal.under_map_of_isLocalizationAtPrime p.asIdeal hrp]
  have hKreg : ∀ x :S,f D *x∈K→x∈K:= by
    change ∀ x :S,f D *x∈(J ⊔ cy {a}).map f →
      x∈(J ⊔ cy {a}).map f at hreg
    rw [hmap J a] at hreg
    exact hreg
  refine ⟨fVL hann (fun x hx=>(hQprime.mem_or_mem hx).resolve_left hdQ) hKreg,?_⟩
  intro hDp
  have hcut:=brK (dSD hann hKreg)
  have heq : (L ⊔ cy {f D}) ⊔ cy {f a} =
      K ⊔ cy {f D} := sup_right_comm _ _ _
  change 1+Module.length S (S ⧸ ((J ⊔ cy {a}) ⊔ cy {D}).map f) ≤
    p5 S (S ⧸ (J ⊔ cy {D}).map f)
  rw [hmap,hmap J a,hmap J D,hcut,heq]
  apply add_le_add_left
  have hle :Q ⊔ cy {f D} ≤ u8 S:= by
    rw [← Il (I:=p.asIdeal)]
    exact zc (Ideal.map_mono hrp)
      ((Ea _).mpr (yL f hDp))
  let:Nontrivial (S ⧸ (Q ⊔ cy {f D})) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
      (G6 S).ne_top hle)
  exact Order.one_le_iff_pos.mpr Zt
set_option maxHeartbeats 800000 in
theorem d43 [LO R] (B:aU R) (r :nq R)
    (hr :r.asIdeal∈B.minimalPrimes) :
    ∃ g:R,g∉r.asIdeal ∧ ∀ (p:nq R),r.asIdeal≤p.asIdeal →
      g∉p.asIdeal → ∀ D:R,D∉r.asIdeal→D∈p.asIdeal →
      yC r B≤yC p (B ⊔ cy {D}) := by
  suffices ∀ J:aU R,B≤J →
    ∃ g:R,g∉r.asIdeal ∧ ∀ (p:nq R),r.asIdeal≤p.asIdeal →
      g∉p.asIdeal → ∀ D:R,D∉r.asIdeal →
      (∀ x :At p,lJ R (At p) D *x∈J.map (lJ R (At p)) →
        x∈J.map (lJ R (At p))) ∧
      (D∈p.asIdeal→yC r J≤yC p (J ⊔ cy {D})) by
    obtain ⟨g,hgr,hg⟩:=this B vh
    exact ⟨g,hgr,fun p hrp hgp D hD hDp=>(hg p hrp hgp D hD).2 hDp⟩
  intro J
  induction J using EK (Ef (α:=aU R)) with
  | h J ih =>
    intro hBJ
    by_cases hJ:J = ⊤
    · subst J
      refine ⟨1,r.asIdeal.ne_top_iff_one.mp r.isPrime.ne_top,?_⟩
      intro p _ _ D _
      refine ⟨?_,?_⟩
      · intro x _
        rw [Nq]
        exact Qx
      · intro _
        unfold yC
        rw [Nq]
        exact Module.length_eq_zero.trans_le zero_le
    obtain ⟨a,Q,ha,hQ,hann⟩:=bdz hJ
    let K:=J ⊔ cy {a}
    have hJK:J≤K:=p6
    have haK:a∈K:=u9 (th a)
    have hlt:J<K:=wA hJK fun he=>ha (he ▸ haK)
    obtain ⟨g,hgr,hg⟩:=ih K hlt (hBJ.trans hJK)
    by_cases hQr :Q=r.asIdeal
    · subst Q
      refine ⟨g,hgr,fun p hrp hgp D hD => ?_⟩
      obtain ⟨hreg,hlength⟩:=hg p hrp hgp D hD
      obtain ⟨hregular,hcut⟩:=gnO r p hrp hann hD hreg
      refine ⟨hregular,fun hDp => ?_⟩
      rw [dNr r hann]
      exact (add_le_add_right (hlength hDp) 1).trans (hcut hDp)
    · have hBQ:B≤Q:= fun x hx=>(hann x).mp (J.mul_mem_right _ (hBJ hx))
      have hnle : ¬ Q≤ r.asIdeal :=
        fun hle=>hQr (hle.antisymm (hr.2 ⟨hQ,hBQ⟩ hle))
      obtain ⟨s,hsQ,hsr⟩:=Set.not_subset.mp hnle
      refine ⟨g*s,fun h=>(r.isPrime.mem_or_mem h).elim hgr hsr,?_⟩
      intro p hrp hgp D hD
      have hg' : g∉p.asIdeal:= fun h=>hgp (p.asIdeal.mul_mem_right s h)
      have hs' : s∉p.asIdeal:= fun h=>hgp (p.asIdeal.mul_mem_left g h)
      have hlocal:K.map (lJ R (At p))=J.map (lJ R (At p)) :=
        cZg hann p hsQ hs'
      have hgen:K.map (lJ R (At r))=J.map (lJ R (At r)) :=
        cZg hann r hsQ hsr
      obtain ⟨hreg,hlength⟩:=hg p hrp hg' D hD
      rw [hlocal] at hreg
      refine ⟨hreg,fun hDp => ?_⟩
      have hsgen:yC r K=yC r J:= by
        unfold yC
        rw [hgen]
      have hscut:yC p (K ⊔ cy {D})=yC p (J ⊔ cy {D}) := by
        unfold yC
        let f :R →+* At p:=lJ R (At p)
        have hmap (I:aU R) :
            (I ⊔ cy {D}).map f=I.map f ⊔ (cy {D}).map f := by
          rw [uW]
        change p5 (At p) (At p ⧸ (K ⊔ cy {D}).map f) =
          p5 (At p) (At p ⧸ (J ⊔ cy {D}).map f)
        rw [hmap K,hmap J,hlocal]
      simpa only [hsgen,hscut] using hlength hDp
end
end bzM
end
section
namespace bar
noncomputable section
open Filter MvPolynomial Polynomial
variable {k σ:Type*} [uJ k] [qU σ]
private theorem em1
    {I Q:aU (lz σ k)} {g:lz σ k}
    (ha : ∀ x,x*g∈I↔x∈Q)
    (C:ℕ) (hC : ∀ f∈I ⊔ cy {g},∃ q:lz σ k,
      f - q*g∈I∧q.totalDegree≤f.totalDegree+C) (N :ℕ) :
    sH I N≤ sH (I ⊔ cy {g}) N +
      sH Q (N+C) := by
  let J:=I ⊔ cy {g}
  have hIJ:I≤J:=p6
  let π:=((G0 k hIJ).toLinearMap.domRestrict
    (pz I N)).codRestrict (pz J N) fun x=> by
      obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp x.property
      change Fz hIJ x.val∈pz J N
      rw [← hpx,Eg]
      exact yo hp
  have hsurj:t7 π:= by
    intro y
    obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
    exact ⟨⟨mD I p,yo hp⟩,t6 hpy⟩
  let μ:=ML.afC (k :=k) ha
  have hμ:qz μ:=ML.aUw ha
  have hrep (x :z8 π) :
      ∃ q:lz σ k,q.totalDegree≤N+C ∧
        μ (mD Q q)=x.val.val := by
    obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp x.val.property
    have hpJ:p∈J:= by
      have hzero :=qy Xg (LinearMap.mem_ker.mp x.property)
      change Fz hIJ x.val.val=0 at hzero
      rw [← hpx,Eg ,t3] at hzero
      exact hzero
    obtain ⟨q,hq,hqd⟩:=hC p hpJ
    refine ⟨q,hqd.trans (VH hp C),?_⟩
    rw [← hpx]
    change ML.afC ha (mD Q q)= _
    rw [ML.aNH,qG g q,Ideal.Quotient.eq]
    simpa only [neg_sub] using I.neg_mem hq
  let inc:=(pz I N).subtype.comp (z8 π).subtype
  let intoRange :=inc.codRestrict (v9 μ) fun x=> by
    obtain ⟨q,_,hq⟩:=hrep x
    exact ⟨mD Q q,hq⟩
  let e :=zjT μ hμ
  let back :=e.symm.toLinearMap.comp intoRange
  let bounded:=back.codRestrict (pz Q (N+C)) fun x=> by
    obtain ⟨q,hq,hqx⟩:=hrep x
    have he :e (mD Q q)=intoRange x :=t6 hqx
    change e.symm (intoRange x)∈_
    rw [← he,LinearEquiv.symm_apply_apply]
    exact yo hq
  have hback (x :z8 π) :μ (bounded x).val=x.val.val :=
    qy Xg (e.apply_symm_apply (intoRange x))
  have hinj:qz bounded:= by
    intro x y hxy
    apply t6 (t6 _)
    rw [← hback x,← hback y,hxy]
  have hker :=NZ hinj
  have hrank :=π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,Vs] at hrank
  change sH I N≤ sH J N+affineHilbertFunction Q (N+C)
  unfold sH
  omega
theorem a4G {I Q:aU (lz σ k)} {g:lz σ k}
    (ha : ∀ x,x*g∈I↔x∈Q) {d:ℕ}
    (hd: (lV I).natDegree≤d) :
    (lV I).coeff d =
      (lV (I ⊔ cy {g})).coeff d +
        (lV Q).coeff d:= by
  let J:=I ⊔ cy {g}
  have hIJ:I≤J:=p6
  have hIQ:I≤Q:= fun x hx=>(ha x).mp (I.mul_mem_right _ hx)
  have hJd:=(t9 hIJ).trans hd
  have hQd:=(t9 hIQ).trans hd
  refine sS ?_ (ML.a4G hIJ
    (u9 (th g)) ha hd)
  obtain ⟨C,hC⟩:=d38 I g
  let P:=lV J+taylor (C:ℚ) (lV Q)
  have hPd:P.natDegree≤d :=
    natDegree_add_le_of_degree_le hJd (by rwa [zm])
  have hcoeff :P.coeff d =
      (lV J).coeff d+(lV Q).coeff d:= by
    simp only [P,coeff_add,Ob _ hQd]
  rw [← hcoeff]
  refine EP hd hPd ?_
  obtain ⟨T,hT⟩:=zQf Q
  filter_upwards [vl I,
    vl J,eventually_ge_atTop T] with N hI hJ hN
  simp only [P,WK,G3]
  rw [hI,hJ,← Et,hT _ (hN.trans (yQ _ _))]
  exact_mod_cast em1 ha C hC N
end
end bar
end
section
namespace aA6
noncomputable section
open aR dN vS B8 MvPolynomial
open scoped BigOperators Pointwise
private theorem dfS {t:Fin 5→ℕ} {n:ℕ}
    (u: (i:Fin 5)→Fin (n*t i)→ Iw) :
    (∑ i,∑ j,u i j) =
      ∑ k :Fin n,∑ i,∑ j:Fin (t i),u i (G9 (k,j)) := by
  calc
    (∑ i,∑ j,u i j) =
        ∑ i,∑ k :Fin n,∑ j:Fin (t i),u i (G9 (k,j)) := by
      refine qJ rfl fun i _ => ?_
      rw [← Fintype.sum_prod_type']
      exact (Fintype.sum_equiv G9 _ _ fun _=>rfl).symm
    _ = _:=Finset.sum_comm
private theorem aHz (B:lS) (t:Fin 5→ℕ) (n:ℕ) :
   n•H7 B t=H7 B (fun i=>n*t i) := by
 ext x
 rw [Set.mem_nsmul_iff_sum]
 constructor
 · rintro ⟨g,hg,rfl⟩
   choose u hu he using hg
   let v (i:Fin 5) (j:Fin (n*t i)) :Exponent :=
     u (finProdFinEquiv.symm j).1 i (finProdFinEquiv.symm j).2
   refine ⟨v,fun i j=>hu _ _ _,?_⟩
   rw [dfS v]
   simp only [v,zwn]
   exact qJ rfl fun k _=>he k
 · rintro ⟨u,hu,rfl⟩
   exact ⟨fun k => ∑ i,∑ j:Fin (t i),u i (G9 (k,j)),
     fun k=>⟨fun i j=>u i (G9 (k,j)),fun i j=>hu _ _,rfl⟩,
     (dfS u).symm⟩
private theorem a9G (B:lS) (t:Fin 5→ℕ) :
   0∈H7 B t :=
 ⟨fun _ _=>0,fun _ _=> by simp [Nl,Qj],by simp⟩
private theorem aDS {S:Set Iw} {n:ℕ} {e :Iw}
   (he :e∈n•S) :
   ∃ q:lz S ox ,
     q.totalDegree≤n∧vw ox S q=pU e 1 := by
 induction n generalizing e with
 | zero =>
   rw [zero_smul,Set.mem_zero] at he
   subst e
   exact ⟨1,by simp,by simp⟩
 | succ n ih =>
   rw [succ_nsmul'] at he
   obtain ⟨a,ha,b,hb,rfl⟩:=he
   obtain ⟨q,hq,heq⟩:=ih hb
   refine ⟨nI ⟨a,ha⟩*q,?_,?_⟩
   · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_X]; omega)
   · rw [oK,monomialMap_X,heq,Lf ,t5]
theorem b0z (B:lS) (P:aU g9) (t:Fin 5→ℕ) (n:ℕ) :
    sH (RM B P t) n =
      Gr ox (Kx B P (fun i=>n*t i)) := by
  let S:=H7 B t
  let f :=vw ox S
  let g: (lz S ox ⧸ RM B P t) →ₐ[ox] (g9 ⧸ P) :=
    WX P f vh
  let V:=pz (RM B P t) n
  change Gr ox V= _
  have hmap :V.map g.toLinearMap=Kx B P (fun i=>n*t i) := by
    rw [Kx,← aHz]
    apply sS
    · rintro _ ⟨v,hv,rfl⟩
      obtain ⟨q,hq,rfl⟩:=mem_quotientDegreeLE.mp hv
      exact ⟨f q,ZK (a9G B t) hq,rfl⟩
    · rw [In,MS ,Sv]
      rintro _ ⟨_,⟨e,he,rfl⟩,rfl⟩
      obtain ⟨q,hq,heq⟩:=aDS he
      exact ⟨mD (RM B P t) q,yo hq,
        qy (mD P) heq⟩
  rw [← hmap]
  have hg:qz g:=Ideal.quotientMap_injective (I:=P) (f :=f.toRingHom)
  exact (Submodule.equivMapOfInjective g.toLinearMap hg V).finrank_eq
end
end aA6
end
section
namespace baE
noncomputable section
open ML
open scoped BigOperators
section Cyclic
variable {R S:Type*} [ov R] [ov S] [wB R S]
private theorem d5U [Pc R S] {J D:aU R} {a :R}
   (ha : ∀ x :R,x*a∈J↔x∈D) (x :S) :
   x*lJ R S a∈J.map (lJ R S) ↔
     x∈D.map (lJ R S) := by
 let f :=afC (k :=R) ha
 have hf :qz (f.lTensor S) :=
   Module.Flat.lTensor_preserves_injective_linearMap f (aUw ha)
 let eJ:=UP S J
 let eD:=UP S D
 have he :f.lTensor S (eD (mD (D.map (lJ R S)) x)) =
     eJ (mD (J.map (lJ R S)) (x*lJ R S a)) := by
   simp only [eD,eJ,Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
     LinearMap.lTensor_tmul,f]
   have hS:x*lJ R S a=a•x := by rw [NX ,qG]
   rw [hS,TensorProduct.smul_tmul]
   congr 1
 rw [← t3 ,← t3]
 constructor
 · intro hx
   apply eD.injective
   apply hf
   simp only [he,hx,pQ]
 · intro hx
   apply eJ.injective
   simp only [← he,hx,pQ]
end Cyclic
variable {R:Type*} [ov R]
def localColength (q:nq R) (J:aU R) :ℕ∞ :=
 let A:=vH q.asIdeal
 p5 A (A ⧸ J.map (lJ R A))
theorem b71 {q:nq R} {J:aU R}
   (h : ¬ J≤q.asIdeal) :localColength q J=0:= by
 let A:=vH q.asIdeal
 obtain ⟨s,hs,hsq⟩:=Set.not_subset.mp h
 have htop:J.map (lJ R A) = ⊤ :=
   (J.map (lJ R A)).eq_top_of_isUnit_mem
     (yL (lJ R A) hs)
     (Kl A (⟨s,hsq⟩:q.asIdeal.primeCompl))
 change p5 A (A ⧸ J.map (lJ R A))=0
 rw [htop]
 exact II
private theorem b72 {B J D:aU R} (hBJ:B≤J)
   {a :R} (hD:D.IsPrime) (ha : ∀ x :R,x*a∈J↔x∈D)
   {q:nq R} (hq:q.asIdeal∈B.minimalPrimes) :
   localColength q J=(if D =q.asIdeal then 1 else 0) +
     localColength q (J ⊔ cy {a}) := by
 classical
 let A:=vH q.asIdeal
 let f :R →+* A:=lJ R A
 have hmul :=brK (bdE (S:=A) q.asIdeal.primeCompl ha)
 change p5 A (A ⧸ J.map f)= _ +
   p5 A (A ⧸ (J ⊔ cy {a}).map f)
 rw [uW,uz ,vZ,hmul]
 congr 1
 by_cases h:D =q.asIdeal
 · subst D
   rw [x7 rfl,show q.asIdeal.map f=u8 A from
     Il]
   have :KA A (A ⧸ u8 A) :=
     isSimpleModule_iff_isCoatom.mpr (G6 A).1
   exact LR A _
 · rw [t4 h]
   have hBD:B≤D:= fun x hx=>(ha x).mp (J.mul_mem_right _ (hBJ hx))
   have hn : ¬ D ≤q.asIdeal:= fun hle=>h (hle.antisymm (hq.2 ⟨hD,hBD⟩ hle))
   exact b71 hn
section Weighted
variable {S k :Type*} [ov S] [uJ k] [wB R S] [wB k S]
 [Pc R S]
private def azq (I:aU R) :ℕ∞ :=
 p5 k (S ⧸ I.map (lJ R S))
private theorem evw {J D:aU R} {a :R}
   (ha : ∀ x :R,x*a∈J↔x∈D) :
   azq (S:=S) (k :=k) J =
     azq (S:=S) (k :=k) D + azq (S:=S) (k :=k) (J ⊔ cy {a}) := by
 let f :R →+* S:=lJ R S
 let b:=f a
 let H :=J.map f
 let E :=D.map f
 have hb : ∀ x :S,x*b∈H↔x∈E :=d5U ha
 have h:=zit
   (afC (k :=k) hb)
   (G0 k (p6:H≤H ⊔ cy {b})).toLinearMap
   (aUw hb) (WD p6) (bFP hb)
 unfold azq
 rw [uW,uz ,vZ]
 exact h
private theorem gwQ (D:aU R) (qs :nX (nq R)) (d:ℕ∞) :
   (∑ q∈qs,if D =q.asIdeal then d else 0)≤d:= by
 classical
 by_cases he : ∃ q∈qs,D =(q:nq R).asIdeal
 · obtain ⟨q,hq,heq⟩:=he
   rw [VS q hq,x7 heq]
   intro r _ hr
   exact t4 (fun her=>hr (Xx (her.symm.trans heq)))
 · rw [C5 fun q hq=>t4 (fun h=>he ⟨q,hq,h⟩)]
   exact zero_le
theorem gMl [LO R] (B:aU R)
    (qs :nX (nq R)) (hmin : ∀ q∈qs,q.asIdeal∈B.minimalPrimes)
    (J:aU R) (hBJ:B≤J) :
    ∑ q∈qs,localColength q J*p5 k (S ⧸ q.asIdeal.map (lJ R S)) ≤
      p5 k (S ⧸ J.map (lJ R S)) := by
  classical
  change ∑ q∈qs,localColength q J*azq (S:=S) (k :=k) q.asIdeal ≤
    azq (S:=S) (k :=k) J
  revert hBJ
  induction J using EK (Ef (α:=aU R)) with
  | h J ih =>
    intro hBJ
    by_cases hJ:J = ⊤
    · subst J
      have hz (q:nq R) :localColength q ⊤ = 0 :=
        b71 fun h=>q.isPrime.ne_top (top_le_iff.mp h)
      simp [hz]
    obtain ⟨a,D,haJ,hD,hann⟩:=bdz hJ
    let T:=J ⊔ cy {a}
    have hJT:J≤T:=p6
    have haT:a∈T:=u9 (th a)
    have hlt:J<T:=wA hJT fun he=>haJ (he ▸ haT)
    let d:=azq (S:=S) (k :=k) D
    have hterm (q:nq R) (hq:q∈qs) :
        localColength q J*azq (S:=S) (k :=k) q.asIdeal =
          localColength q T*azq (S:=S) (k :=k) q.asIdeal +
            (if D =q.asIdeal then d else 0) := by
      rw [b72 hBJ hD hann (hmin q hq),N0 ,FU]
      by_cases he :D =q.asIdeal
      · simp [he,d,T]
      · simp [he,T]
    calc
      _=(∑ q∈qs,localColength q T*azq (S:=S) (k :=k) q.asIdeal) +
          (∑ q∈qs,if D =q.asIdeal then d else 0) := by
        rw [← wR]
        exact qJ rfl hterm
      _≤azq (S:=S) (k :=k) T+d :=
        Nj (ih T hlt (hBJ.trans hJT)) (gwQ D qs d)
      _=azq (S:=S) (k :=k) J:= by
        rw [evw hann,FU]
end Weighted
end
end baE
end
section
namespace bzC
noncomputable section
open Filter MvPolynomial Polynomial
variable {σ k :Type*} [uJ k] [qU σ]
private theorem dz9 (J:aU (lz σ k)) (a :lz σ k) :
   ∃ C:ℕ,∀ p∈J ⊔ cy {a},∃ b:lz σ k,
     b.totalDegree≤p.totalDegree+C∧mD J p=mD J (a*b) := by
 classical
 let K:=J ⊔ cy {a}
 let _:=FQ σ
 let _:LinearOrder σ:=Z0 _ (PM σ).injective
 have :WellFoundedGT σ:=XB
 let m:KH σ:=zwf
 obtain ⟨B,hB⟩:=m.exists_finset_standardExponents_iff K
 have hchoose (e : ↥B) : ∃ f∈K,f≠0∧m.degree f≤e.val := by
   have he :e.val∉m.standardExponents K:= fun h=>(hB _).mp h _ e.property vh
   simp only [MonomialOrder.standardExponents,Set.mem_ofPred_eq,not_forall,not_imp,
     not_not] at he
   obtain ⟨p,hp,hp0,hle⟩:=he
   exact ⟨p,hp,hp0,hle⟩
 choose f hf hf0 hfe using hchoose
 have hlift (e : ↥B) : ∃ u:lz σ k,
     mD J (f e)=mD J (a*u) := by
   have he :=hf e
   change f e∈J ⊔ cy {a} at he
   rw [Av] at he
   obtain ⟨u,v,hv,heq⟩:=Ideal.mem_span_singleton_sup.mp he
   exact ⟨u,by rw [← heq,t8 ,Ideal.Quotient.eq_zero_iff_mem.mpr hv,v8 ,qG]⟩
 choose u hu using hlift
 obtain ⟨C,hC⟩:=SM (fun e=>(u e).totalDegree)
 refine ⟨C,fun p hp => ?_⟩
 obtain ⟨g,r,hpr,hd,hr⟩:=m.div (b:=f) (fun e=>m.isUnit_leadingCoeff.mpr (hf0 e)) p
 have heq :p=(∑ e∈g.support,g e*f e)+r := by
   simpa only [Finsupp.linearCombination_apply,Finsupp.sum,Dz] using hpr
 have hsum: (∑ e∈g.support,g e*f e)∈K :=
   K.sum_mem (fun e _=>K.mul_mem_left _ (hf e))
 have hrK:r∈K:= by
   rw [← add_sub_cancel_left (∑ e∈g.support,g e*f e) r,← heq]
   exact K.sub_mem hp hsum
 have hrstd:r∈m.standardSpace K:= by
   intro c hc
   exact (hB c).mpr (fun e he hle=>hr c hc ⟨e,he⟩ ((hfe ⟨e,he⟩).trans hle))
 rw [m.eq_zero_of_mem_standardSpace_of_mem hrstd hrK,v8] at heq
 refine ⟨∑ e∈g.support,g e*u e,?_,?_⟩
 · rw [← mem_restrictTotalDegree]
   apply VO
   intro e he
   rw [mem_restrictTotalDegree]
   have hgd: (g e).totalDegree≤p.totalDegree := by
     have hprod:=degLex_totalDegree_monotone (hd e)
     rw [totalDegree_mul_of_isDomain (hf0 e) (Finsupp.mem_support_iff.mp he)] at hprod
     omega
   exact (totalDegree_mul _ _).trans (G1 hgd (hC e))
 · rw [heq,zg ,Gi ,Gi]
   exact qJ rfl (fun e _=> by simp only [oK,hu,NY])
private theorem em3 {J Q:aU (lz σ k)} {a :lz σ k}
   (ha : ∀ x,x*a∈J↔x∈Q) :
   ∃ C:ℕ,∀ N :ℕ,sH J N ≤
     sH (J ⊔ cy {a}) N+affineHilbertFunction Q (N+C) := by
 let K:=J ⊔ cy {a}
 have hJK:J≤K:=p6
 obtain ⟨C,hC⟩:=dz9 J a
 refine ⟨C,fun N => ?_⟩
 let π:=((G0 k hJK).toLinearMap.domRestrict (pz J N)).codRestrict
   (pz K N) fun x=> by
     obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp x.property
     change Fz hJK x∈pz K N
     rw [← hpx,Eg]
     exact yo hp
 have hsurj:t7 π:= by
   intro y
   obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
   exact ⟨⟨mD J p,yo hp⟩,t6 hpy⟩
 let μ:=(ML.afC (k :=k) ha).domRestrict (pz Q (N+C))
 let ι:=(pz J N).subtype.comp (z8 π).subtype
 have him (z :z8 π) :ι z∈v9 μ:= by
   obtain ⟨p,hp,hpz⟩:=mem_quotientDegreeLE.mp z.val.property
   have hz :π z.val=0:=LinearMap.mem_ker.mp z.property
   have hpK:p∈K:=Ideal.Quotient.eq_zero_iff_mem.mp (by
     have hz' := qy (fun w:pz K N=>(w:lz σ k ⧸ K)) hz
     change Fz hJK (z.val :lz σ k ⧸ J)=0 at hz'
     rwa [← hpz,Eg] at hz')
   obtain ⟨b,hb,he⟩:=hC p hpK
   refine ⟨⟨mD Q b,yo (hb.trans (VH hp C))⟩,?_⟩
   change ML.afC ha (mD Q b)=(z.val :lz σ k ⧸ J)
   rw [ML.aNH,← he,hpz]
 have hinj:qz (ι.codRestrict (v9 μ) him) := by
   intro x y hxy
   have hxy' : (x.val :lz σ k ⧸ J)=(y.val :lz σ k ⧸ J) :=
     qy (fun w:v9 μ=>(w:lz σ k ⧸ J)) hxy
   exact t6 (t6 hxy')
 have hdim:=(NZ hinj).trans μ.finrank_range_le
 have hrank :=π.finrank_range_add_finrank_ker
 rw [LinearMap.range_eq_top.mpr hsurj,Vs] at hrank
 exact hrank.ge.trans (Nat.add_le_add_left hdim _)
theorem proof :axg.c1 := by
 intro σ _ J Q a ha d hd
 let K:=J ⊔ cy {a}
 have hJQ:J≤Q:= fun x hx=>(ha x).mp (J.mul_mem_right _ hx)
 have hKd:=(t9 (show J≤K from p6)).trans hd
 have hQd:=(t9 hJQ).trans hd
 obtain ⟨C,hC⟩:=em3 ha
 let P:ℚ[X] :=lV K+taylor (C:ℚ) (lV Q)
 have hPd:P.natDegree≤d :=
   (natDegree_add_le_of_le hKd ((zm _ _).trans_le hQd)).trans (max_self d).le
 have hcoeff :P.coeff d =
     (lV K).coeff d+(lV Q).coeff d:= by
   simp only [P,coeff_add,Ob _ hQd]
 change (lV J).coeff d ≤
   (lV K).coeff d+(lV Q).coeff d
 rw [← hcoeff]
 refine EP hd hPd ?_
 have hshift:Tendsto (fun n:ℕ=>n+C) atTop atTop :=
   tendsto_atTop_mono (fun n=>yQ n C) tendsto_id
 filter_upwards [vl J,vl K,
   hshift.eventually (vl Q)] with N hJ hK hQ
 simp only [P,WK,G3]
 rw [← Et,hJ,hK,hQ]
 exact_mod_cast hC N
end
end bzC
end
section
namespace aA6
noncomputable section
open aR dN vS B8 MvPolynomial
open scoped BigOperators
def c1 :Prop :=
  ∀ (B:lS) (P:aU g9),
    ∃ o:KH.{0,0} (alh B),∀ u:Fin 5→ℕ,
      Gr ox (Kx B P u) =
        {e :alh B →₀ ℕ | aeh (fun v=>v.1) e=u ∧
          e∈o.standardExponents (p9 (a8E B P).toRingHom)}.ncard
def c2 :Prop :=
  ∀ {σ:Type} [qU σ] (slot:σ→Fin 5) (bad:nX (σ →₀ ℕ)),
    ∃ (m:ℕ) (p:Fin m→Fin 5→vj ℚ),
      (∀ a i,0<(p a i).leadingCoeff) ∧
      ∃ N :ℕ,∀ (u:Fin 5→ℕ),(∀ i,N≤u i) →
        (DL slot bad u:ℚ) = ∑ a,∏ i,(p a i).eval (u i:ℚ)
private def bgC (p:vj ℚ) (t:ℕ) :vj ℚ :=
 p.comp (qm (t:ℚ)*Kv)
private def aWO (p:Fin 5→vj ℚ) (t:Fin 5→ℕ) :vj ℚ :=
 ∏ i,bgC (p i) (t i)
private theorem fT7 (p:vj ℚ) {t:ℕ} (ht:0<t) :
  (bgC p t).natDegree=p.natDegree := by
 rw [bgC,Polynomial.natDegree_comp,
  zK5 _ (Nat.cast_ne_zero.mpr ht.ne'),Dw]
private theorem c7i (p:vj ℚ) {t:ℕ} (ht:0<t) :
  (bgC p t).leadingCoeff=p.leadingCoeff*(t:ℚ)^p.natDegree := by
 rw [bgC,Polynomial.leadingCoeff_comp,Polynomial.leadingCoeff_C_mul_X]
 rw [zK5 _ (Nat.cast_ne_zero.mpr ht.ne')]
 exact one_ne_zero
private theorem ceL (p:Fin 5→vj ℚ)
   (hp : ∀ i,0<(p i).leadingCoeff) {t:Fin 5→ℕ} (ht : ∀ i,0<t i) :
   (aWO p t).natDegree = ∑ i,(p i).natDegree := by
 rw [aWO,Polynomial.natDegree_prod]
 · exact qJ rfl fun i _=>fT7 _ (ht i)
 · intro i _
   apply Polynomial.leadingCoeff_ne_zero.mp
   rw [c7i _ (ht i)]
   exact (mul_pos (hp i) (pow_pos (Nat.cast_pos.mpr (ht i)) _)).ne'
private theorem c7j (p:Fin 5→vj ℚ)
   {t:Fin 5→ℕ} (ht : ∀ i,0<t i) :
   (aWO p t).leadingCoeff =
     (∏ i,(p i).leadingCoeff) * ∏ i,(t i:ℚ)^(p i).natDegree := by
 rw [aWO,Polynomial.leadingCoeff_prod,← Finset.prod_mul_distrib]
 exact Mz rfl fun i _=>c7i _ (ht i)
private theorem gxn {m d:ℕ} (q:Fin m→vj ℚ)
   (hq : ∀ a,0<(q a).leadingCoeff) (hd: (∑ a,q a).natDegree≤d) (a :Fin m) :
   (q a).natDegree≤d:= by
 by_contra! h
 let M:=(Finset.univ :nX (Fin m)).sup (fun a=>(q a).natDegree)
 have hle (b:Fin m) : (q b).natDegree≤M:=TZ (f := fun a=>(q a).natDegree) (FR b)
 have hdM:=h.trans_le (hle a)
 obtain ⟨b,hb,he⟩:=Finset.exists_mem_eq_sup _ ⟨a,FR a⟩
   (fun a=>(q a).natDegree)
 have hn (b:Fin m) :0≤(q b).coeff M:= by
   rcases (hle b).lt_or_eq with hlt | heq
   · rw [zE hlt]
   · rw [← heq,Vq]
     exact (hq b).le
 have hs :0 < ∑ b,(q b).coeff M:=Finset.sum_pos' (fun b _=>hn b)
   ⟨b,hb,by rw [show M=(q b).natDegree from he,Vq]; exact hq b⟩
 rw [← Np,zE (hd.trans_lt hdM)]
   at hs
 exact (lt_irrefl 0) hs
private def direction (J:nX (Fin 5)) (i:Fin 5) :ℕ:=if i∈J then 2 else 1
private theorem cKQ (J:nX (Fin 5)) (i:Fin 5) :0<direction J i:= by
 by_cases h:i∈J <;> simp [direction,h]
private theorem dXj (J:nX (Fin 5)) (r :Fin 5→ℕ) :
  (∏ i,(direction J i:ℚ)^r i) = ∏ i∈J,(2 :ℚ)^r i:= by
 calc
  (∏ i,(direction J i:ℚ)^r i) = ∏ i∈J,(direction J i:ℚ)^r i :=
    (Finset.prod_subset (Finset.subset_univ J) fun i _ hi=> by simp [direction,hi]).symm
  _ = _:=Mz rfl fun i hi=> by simp [direction,hi]
private theorem gq3 (I:nX (Fin 5)) (r :Fin 5→ℕ) :
   (∑ J∈I.powerset,(-1 :ℚ)^(I.card-J.card) *
     ∏ i,(direction J i:ℚ)^r i) = ∏ i∈I,((2 :ℚ)^r i - 1) := by
 simp_rw [dXj,sub_eq_add_neg]
 rw [Finset.prod_add]
 refine qJ rfl fun J hJ => ?_
 rw [Finset.prod_const,Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hJ),qG]
private theorem dM3 {m d:ℕ} (p:Fin m→Fin 5→vj ℚ)
    (hp : ∀ a i,0<(p a i).leadingCoeff) {t:Fin 5→ℕ} (ht : ∀ i,0<t i)
    (hd : ∀ a,(∑ i,(p a i).natDegree)≤d) :
    (∑ a,aWO (p a) t).coeff d =
      ∑ a,(if (∑ i,(p a i).natDegree)=d then ∏ i,(p a i).leadingCoeff else 0) *
        ∏ i,(t i:ℚ)^(p a i).natDegree := by
  rw [Np]
  refine qJ rfl fun a _ => ?_
  rcases (hd a).lt_or_eq with hlt | heq
  · have htlt: (aWO (p a) t).natDegree<d:=(ceL (p a) (hp a) ht).trans_lt hlt
    rw [zE htlt,t4 hlt.ne,zi]
  · rw [x7 heq,← c7j _ ht,
      ← (ceL (p a) (hp a) ht).trans heq,Vq]
theorem of_children (h1 :c1) (h2 :c2) :axg.c2 := by
  intro B hB P I _ hP
  obtain ⟨o,ho⟩:=h1 B P
  obtain ⟨bad,hb⟩:=o.exists_finset_standardExponents_iff (p9 (a8E B P).toRingHom)
  have hbad (u:Fin 5→ℕ) :
      Gr ox (Kx B P u)=DL (fun v=>v.1) bad u:= by
    rw [ho]
    simp only [DL,hb]
  obtain ⟨m,p,hp,N,hN⟩:=h2 (fun v :alh B=>v.1) bad
  have hray (t:Fin 5→ℕ) (ht : ∀ i,0<t i) :
      lV (RM B P t) = ∑ a,aWO (p a) t:= by
    symm
    refine eq_affineHilbertPolynomial_of_eval_eq (N₀:=N) fun n hn => ?_
    rw [b0z B P t n,hbad,hN (fun i=>n*t i)
      (fun i=>hn.trans (Nat.le_mul_of_pos_right n (ht i)))]
    simp only [aWO,bgC,Polynomial.eval_finsetSum,Polynomial.eval_prod,
      Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Kp]
    refine qJ rfl fun a _=>Mz rfl fun i _ => ?_
    rw [qG (t i:ℚ) (n:ℚ)]
  have hd : ∀ a,(∑ i,(p a i).natDegree)≤I.card:= by
    let t:Fin 5→ℕ:= fun _=>1
    have ht (i:Fin 5) :0<t i:=Nat.zero_lt_one
    have hle :=axg.aNi hB hP ht
    change (lV (RM B P t)).natDegree≤I.card at hle
    rw [hray t ht] at hle
    intro a
    rw [← ceL (p a) (hp a) ht]
    apply gxn _ _ hle
    intro b
    rw [c7j _ ht]
    exact mul_pos (Finset.prod_pos fun i _=>hp b i)
      (Finset.prod_pos fun i _=>pow_pos (Nat.cast_pos.mpr (ht i)) _)
  let w (a :Fin m) :ℚ :=
    if (∑ i,(p a i).natDegree)=I.card then ∏ i,(p a i).leadingCoeff else 0
  have hcoeff (J:nX (Fin 5)) :
      (lV (RM B P (direction J))).coeff I.card =
        ∑ a,w a * ∏ i,(direction J i:ℚ)^(p a i).natDegree := by
    rw [hray _ (cKQ J)]
    exact dM3 p hp (cKQ J) hd
  change 0≤(∑ J∈I.powerset,(-1 :ℚ)^(I.card-J.card) *
    (lV (RM B P (direction J))).coeff I.card)/(2 :ℚ)^I.card
  apply NW _ (by positivity)
  simp_rw [hcoeff,zg]
  rw [Finset.sum_comm]
  refine zlo fun a _ => ?_
  simp_rw [NY ((-1 :ℚ)^_) (w a),← zg]
  rw [gq3]
  apply XG
  · unfold w
    split_ifs
    · exact zni fun i _=>(hp a i).le
    · exact vh
  · exact zni fun i _ =>
      sub_nonneg.mpr (one_le_pow₀ (by norm_num))
end
end aA6
end
section
namespace bzD
noncomputable section
open dN vS B8 aA6 MvPolynomial
open scoped BigOperators
def amP (B:lS) : (alh B →₀ ℕ) →+ Exponent :=
 Finsupp.mapDomain.addMonoidHom fun v=>v.1
def aaB (B:lS) : (alh B →₀ ℕ) →+ Exponent :=
 Finsupp.liftAddHom fun v=>multiplesHom Iw v.2.val
private theorem gyP (B:lS) (e :alh B →₀ ℕ) (i:Fin 5) :
  amP B e i=aeh (fun v=>v.1) e i:= by
 classical
 change (Zg (fun v=>v.1) e) i= _
 rw [Zg ,Finsupp.sum_apply]
 simp only [aeh,OJ]
theorem gyQ (B:lS) (e :alh B →₀ ℕ) (u:Fin 5→ℕ) :
   amP B e=Finsupp.equivFunOnFinite.symm u ↔
     aeh (fun v=>v.1) e=u:= by
 rw [Finsupp.equivFunOnFinite.eq_symm_apply]
 change (fun i=>amP B e i)=u↔_
 rw [funext (gyP B e)]
@[simp] private theorem csb (B:lS) (v :alh B) (n:ℕ) :
   amP B (ze v n)=ze v.1 n :=
  Finsupp.mapDomain_single
@[simp] private theorem bT3 (B:lS) (v :alh B) (n:ℕ) :
   aaB B (ze v n)=n•v.2.val :=
  Finsupp.liftAddHom_apply_single _ _ _
private theorem dsF (B:lS) (e :alh B →₀ ℕ) :
    aaB B e∈H7 B (amP B e) := by
  classical
  induction e using Yi with
  | zero =>
      rw [pQ,pQ]
      exact ⟨fun _ j=>j.elim0,fun _ j=>j.elim0,by simp⟩
  | add x y hx hy =>
      obtain ⟨a,ha,hax⟩:=hx
      obtain ⟨b,hb,hby⟩:=hy
      simp only [t8]
      change ∃ w: (i:Fin 5)→Fin (amP B x i+amP B y i)→ Iw ,
        (∀ i j,w i j∈Nl (B i))∧aaB B x+aaB B y =
          ∑ i,∑ j,w i j
      refine ⟨fun i=>Fin.append (a i) (b i),
        fun i=>Fin.addCases (fun j=> by simpa using ha i j)
          (fun j=> by simpa using hb i j),?_⟩
      rw [hax,hby,← wR]
      exact qJ rfl fun i _=> by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left,Fin.append_right]
  | single v n =>
      simp only [bT3,csb]
      let w: (i:Fin 5)→Fin (ze v.1 n i)→Exponent :=
        fun i _=>if v.1=i then v.2.val else 0
      refine ⟨w,fun i j => ?_,?_⟩
      · by_cases hi:v.1=i
        · subst i
          simp [w,v.2.property]
        · simp [w,hi,Nl,Qj]
      · simp only [w,Finset.sum_const,Finset.card_univ,UZ]
        rw [IU v.1]
        · simp
        · intro i _ hi
          simp [hi.symm]
        · simp
theorem dWG (B:lS) (u:Fin 5→ℕ) :
    H7 B u =
      aaB B '' {e | amP B e=Finsupp.equivFunOnFinite.symm u} := by
  classical
  ext m
  constructor
  · rintro ⟨a,ha,rfl⟩
    let e :alh B →₀ ℕ :=
      ∑ i,∑ j,ze (⟨i,⟨a i j,ha i j⟩⟩:alh B) 1
    refine ⟨e,?_,?_⟩
    · change amP B e=Finsupp.equivFunOnFinite.symm u
      ext i
      simp only [e,Gi ,csb,Finsupp.finsetSum_apply,
        Finsupp.coe_equivFunOnFinite_symm,Finset.sum_const,Finset.card_univ,
        UZ]
      rw [IU i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    · simp only [e,Gi ,bT3,one_nsmul]
  · rintro ⟨e,he,rfl⟩
    have h:=dsF B e
    change amP B e=Finsupp.equivFunOnFinite.symm u at he
    rw [he] at h
    exact h
theorem cp2 (B:lS) (P:aU g9) (e :alh B →₀ ℕ) :
    a8E B P (pU e 1) =
      pU (amP B e) (mD P (pU (aaB B e) 1)) := by
  classical
  induction e using Yi with
  | zero=>simp
  | add x y hx hy =>
      rw [show pU (x+y) (1 :ox)=pU x 1*pU y 1 by
        rw [Lf ,t5]]
      rw [oK,hx,hy,Lf ,t8 ,t8 ,← oK,
        Lf ,t5]
  | single v n =>
      have hv :a8E B P (nI v) =
          pU (ze v.1 1) (mD P (pU v.2.val 1)) :=
        aeval_X _ _
      rw [← X_pow_eq_monomial,Du,hv,monomial_pow,csb,bT3,
        ← Du,monomial_pow,one_pow]
      simp
end
end bzD
end
section
namespace bar
noncomputable section
open aR dN Dr MvPolynomial
open scoped BigOperators
private abbrev capMap (p:lI) :=vw ox (oD p)
private abbrev HW (I:aU c9) (p:lI) :=I.comap (capMap p).toRingHom
private theorem aye {p:lI} (hp:pG p) :
  t7 (capMap p) := by
 obtain ⟨hb,hj,ht⟩:=hp
 apply Gj
 intro i
 fin_cases i <;> simp [oD,JM] <;> omega
private theorem cap_dimension (I:aU c9) {p:lI} (hp:pG p) :
  (lV (HW I p)).natDegree=oY I :=
 GY (capMap p) (aye hp) I
private theorem dEv {P Q:aU c9} (hP:P.IsPrime) (hPQ:P<Q)
    {p:lI} (hp:pG p) {d:ℕ} (hd:oY P≤d) :
    oZ Q d p=0:= by
  obtain ⟨f,hfQ,hfP⟩:=Set.not_subset.mp
    (show ¬ (Q:Set c9)⊆P from hPQ.not_ge)
  let J:=P ⊔ cy {f}
  have hJQ:J≤Q:=zc hPQ.le (Q.span_singleton_le_iff_mem.mpr hfQ)
  have hdrop:=KI
    hP hfP (b:=f.totalDegree) vh
  have hQdim:oY Q≤oY J:=t9 hJQ
  by_cases hz :d=0
  · subst d
    have hP0:=za7 hd
    have hJ0:oY J≤0:= by simpa [J,hP0] using hdrop.1
    have hJtop:J = ⊤ := by
      apply affineHilbertPolynomial_eq_zero_iff.mp
      have hupper : (lV J).coeff 0≤0:= by
        simpa [J,hP0] using hdrop.2
      have hzero :=sS hupper
        (RP hJ0
          (Pk J))
      rw [Polynomial.eq_C_of_natDegree_le_zero hJ0,hzero,pQ]
    have hQtop:Q = ⊤ := top_le_iff.mp (hJtop ▸ hJQ)
    simp [hQtop,oZ,Nr,J4]
  · apply zE
    rw [cap_dimension Q hp]
    have hj:oY J≤oY P - 1 :=hdrop.1
    omega
private theorem dEw (I:aU c9) (g:c9) {p:lI} (hp:pG p)
   {d:ℕ} (hd:oY I≤d) :
   oZ I d p=oZ (I ⊔ cy {g}) d p+capCoeff (I.colon {g}) d p:= by
 let φ:=(capMap p).toRingHom
 have hφ:t7 φ:=aye hp
 obtain ⟨G,hG⟩:=hφ g
 have hcut:HW (I ⊔ cy {g}) p=HW I p ⊔ cy {G} := by
   have hm: (HW I p ⊔ cy {G}).map φ=I ⊔ cy {g} := by
     change (I.comap φ ⊔ cy {G}).map φ= _
     rw [uW,LP _ hφ,uz ,vZ,hG]
   change (I ⊔ cy {g}).comap φ= _
   rw [← hm,G5 _ hφ]
   exact sup_eq_left.mpr ((xu (f :=φ) bot_le :
     (⊥ : aU c9).comap φ≤I.comap φ).trans p6)
 have hann (x :lz (oD p) ox) :
     x*G∈HW I p↔x∈HW (I.colon {g}) p:= by
   change φ (x*G)∈I↔φ x∈I.colon {g}
   rw [oK,hG,ztS,Dz]
 change (lV (HW I p)).coeff d =
   (lV (HW (I ⊔ cy {g}) p)).coeff d +
     (lV (HW (I.colon {g}) p)).coeff d
 rw [hcut]
 exact a4G hann ((cap_dimension I hp).trans_le hd)
private theorem cXq {J I P:aU c9} (hJI:J≤I)
   (hP:J.IsMinimalPrime P) :oA I P hP.isPrime ≠ ⊤ := by
 by_cases hIP:I≤P
 · have hm:I.IsMinimalPrime P :=
     ⟨⟨hP.isPrime,hIP⟩,fun _ hR hRP=>hP.2 ⟨hR.1,hJI.trans hR.2⟩ hRP⟩
   exact (ccl hm).2
 · rw [WI.aIs hP.isPrime hIP]
   simp
private theorem gMd {J I P:aU c9} (hJI:J≤I)
    (hP:J.IsMinimalPrime P) (g:c9) (hA: (I.colon {g}).IsPrime) :
    (AN I P:ℚ) =
      (AN (I ⊔ cy {g}) P:ℚ)+(if P=I.colon {g} then 1 else 0) := by
  classical
  let A:=I.colon {g}
  have hterm :oA A P hP.isPrime=if P=A then 1 else 0:= by
    split_ifs with h
    · subst P
      exact WI.brM A hP.isPrime
    · exact WI.aIs hP.isPrime
        (fun hAP=>h (sS (hP.2 ⟨hA,hJI.trans Rm⟩ hAP) hAP))
  change (AN I P:ℚ) =
    (AN (I ⊔ cy {g}) P:ℚ)+(if P=A then 1 else 0)
  simp only [AN,Aa hP.isPrime]
  rw [WI.be6 I P hP.isPrime g,
    ENat.toNat_add (cXq (hJI.trans Rm) hP)
      (cXq (hJI.trans p6) hP),hterm,Et]
  split_ifs <;> simp [FU]
theorem proof :bzB.c1 := by
  classical
  intro J d hd p hp
  let T:=J.minimalPrimesFinset
  suffices h : ∀ I:aU c9,J≤I →
      oZ I d p = ∑ P∈T,(AN I P:ℚ)*oZ P d p from h J vh
  intro I
  induction I using EK (Ef (α:=aU c9)) with
  | h I ih =>
    intro hJI
    by_cases hI:I = ⊤
    · subst I
      simp only [oZ,Nr,J4 ,Polynomial.coeff_zero]
      symm
      apply C5
      intro P hP
      have hprime :=(Ideal.mem_minimalPrimesFinset.mp hP).isPrime
      have hz :=WI.aIs (I := ⊤) hprime (by simpa using hprime.ne_top)
      simp [AN,hprime,hz]
    obtain ⟨g,hg,hprime⟩:=WI.b2k I hI
    let A:=I.colon {g}
    let B:=I ⊔ cy {g}
    have hJA:J≤A:=hJI.trans Rm
    have hIB:I<B:=lt_of_le_not_ge p6
      (fun h=>hg (h (u9 (th g))))
    have hrec:=ih B hIB (hJI.trans hIB.le)
    have hindicator :oZ A d p=if A∈T then oZ A d p else 0:= by
      by_cases hA:A∈T
      · rw [x7 hA]
      · have :A.IsPrime :=hprime
        obtain ⟨P,hP,hPA⟩:=Cy hJA
        have hlt:P<A:=hPA.lt_of_ne (fun h=>hA (h ▸ Ideal.mem_minimalPrimesFinset.mpr hP))
        rw [t4 hA]
        exact dEv hP.isPrime hlt hp
          ((t9 hP.le).trans hd)
    have hdim:=(t9 hJI).trans hd
    calc
      oZ I d p=oZ B d p+capCoeff A d p:=dEw I g hp hdim
      _=(∑ P∈T,(AN B P:ℚ)*oZ P d p) +
          (if A∈T then oZ A d p else 0) := by rw [hrec,← hindicator]
      _ = _:= by
        rw [← Vl T A (fun P=>oZ P d p),← wR]
        refine qJ rfl fun P hP => ?_
        rw [gMd hJI (Ideal.mem_minimalPrimesFinset.mp hP) g hprime,N0 ,ite_mul,
          t5 ,zi]
end
end bar
end
section
namespace ML
noncomputable section
open wH K1_13_7_6 MvPolynomial
variable {σ:Type} [qU σ]
set_option maxHeartbeats 800000 in
theorem gMg (φ:lz σ cH →ₐ[cH] n5)
    (hφ:t7 φ) (B:aU n5) {d:ℕ}
    (hd: (lV (B.comap φ)).natDegree≤d)
    (qs :nX (nq n5))
    (hmin : ∀ q∈qs,q.asIdeal∈B.minimalPrimes)
    (J:aU n5) (hBJ:B≤J) (hfin : ∀ q∈qs,qM q J < ⊤) :
    ∑ q∈qs,(qM q J).toNat *
        (lV (q.asIdeal.comap φ)).coeff d ≤
      (lV (J.comap φ)).coeff d:= by
  classical
  let C:= fun I:aU n5=>(lV (I.comap φ)).coeff d
  change ∑ q∈qs,(qM q J).toNat*C q.asIdeal≤C J
  revert hBJ hfin
  induction J using EK (Ef (α:=aU n5)) with
  | h J ih =>
    intro hBJ hfin
    by_cases hJ:J = ⊤
    · subst J
      have htop (q:nq n5) :qM q ⊤ = 0:= by
        dsimp only [qM]
        rw [Nq]
        exact II
      simp [htop,C,Nr,J4]
    obtain ⟨a,Q,haJ,hQ,hann⟩:=bdz hJ
    obtain ⟨A,hA⟩:=hφ a
    let K:=J ⊔ cy {a}
    have hJK:J≤K:=p6
    have haK:a∈K:=u9 (th a)
    have hlt:J<K:=wA hJK fun he=>haJ (he ▸ haK)
    have hBQ:B≤Q:= fun x hx=>(hann x).mp (J.mul_mem_right _ (hBJ hx))
    have hQd:=(t9 (xu hBQ)).trans hd
    have hCQ:0≤C Q :=
      RP hQd
        (Pk (Q.comap φ))
    have hstep (q:nq n5) (hq:q∈qs) :
        qM q J=(if Q=q.asIdeal then 1 else 0)+localColength q K :=
      b72 hBJ hQ hann (hmin q hq)
    have hfinK (q:nq n5) (hq:q∈qs) :qM q K < ⊤ := by
      have hle :qM q K≤qM q J:= by
        rw [hstep q hq]
        exact le_add_self
      exact hle.trans_lt (hfin q hq)
    have hrec:=ih K hlt (hBJ.trans hJK) hfinK
    have hCKQ:C K+C Q≤C J:= by
      have hAK:A∈K.comap φ:= by
        change φ A∈K
        rwa [hA]
      refine a4G (xu hJK) hAK (fun x => ?_) ?_
      · change φ (x*A)∈J↔φ x∈Q
        rw [oK,hA,hann]
      · exact (t9 (xu hBJ)).trans hd
    have hindicator : ∑ q∈qs,(if Q=q.asIdeal then C Q else 0)≤C Q:= by
      by_cases he : ∃ q∈qs,Q=(q:nq n5).asIdeal
      · obtain ⟨q,hq,hEq⟩:=he
        rw [VS q hq,x7 hEq]
        intro r _ hr
        exact t4 (fun hrQ=>hr (Xx (hrQ.symm.trans hEq)))
      · rw [C5 fun q hq=>t4 (fun h=>he ⟨q,hq,h⟩)]
        exact hCQ
    calc
      ∑ q∈qs,(qM q J).toNat*C q.asIdeal
          = (∑ q∈qs,(qM q K).toNat*C q.asIdeal) +
              ∑ q∈qs,(if Q=q.asIdeal then C Q else 0) := by
            rw [← wR]
            refine qJ rfl fun q hq => ?_
            by_cases he :Q=q.asIdeal
            · rw [hstep q hq,ite_eq_left he,ite_eq_left he,ENat.toNat_add (by simp) (hfinK q hq).ne,
                ENat.toNat_one,Et ,Yc ,N0 ,t5 ,he,FU ]
            · rw [hstep q hq,t4 he,t4 he,zero_add,v8]
      _≤C K+C Q:=Nj hrec hindicator
      _≤C J:=hCKQ
theorem proof :K1_13_7_6.c1 := by
  classical
  intro σ _ φ hφ p L hL hp qs hmin hfin
  by_cases hempty :qs = ∅
  · rw [hempty]
    simpa only [a3c,TH,aGW] using
      affineDegree_nonneg (p.asIdeal.comap φ)
  let P:=p.asIdeal.comap φ
  let B:=ke p (φ L)
  have hBc:B.comap φ=P ⊔ cy {L} := by
    have hm: (P ⊔ cy {L}).map φ=B:= by
      dsimp [P,B,ke]
      rw [uW,LP _ hφ,uz ,vZ]
    rw [← hm,G5 _ hφ]
    exact sup_eq_left.mpr ((xu (f :=φ) bot_le : (⊥ : aU n5).comap φ≤P).trans
      p6)
  have hP:P.IsPrime :=Ideal.comap_isPrime _ _
  have :=hP
  have hproper :L∉P:=hp
  let d:=(lV P).natDegree - 1
  have hbound:=KI
    hP hproper hL
  have hd: (lV (B.comap φ)).natDegree≤d:=hBc.symm ▸ hbound.1
  have hpurity (q:nq n5) (hq:q∈qs) :
      (lV (q.asIdeal.comap φ)).natDegree+1 =
        (lV P).natDegree := by
    refine C9 hproper ?_
    rw [← hBc]
    exact X8 (f :=φ.toRingHom) hφ (hmin q hq)
  obtain ⟨q,hq⟩:=Finset.nonempty_iff_ne_empty.mpr hempty
  have hparent : (lV P).natDegree=d+1 := by
    have :=hpurity q hq
    dsimp [d]
    omega
  have hc:=gMg φ hφ B hd qs hmin B vh hfin
  have hmul :=SW (hc.trans (hBc.symm ▸ hbound.2))
    (Pf (α:=ℚ) d.factorial)
  calc
    a3c (aGW φ) p (φ L) qs =
        (d.factorial:ℚ) * ∑ q∈qs,(qM q B).toNat *
          (lV (q.asIdeal.comap φ)).coeff d:= by
      rw [zg]
      refine qJ rfl fun q hq => ?_
      have hchild: (lV (q.asIdeal.comap φ)).natDegree=d:= by
        have :=hpurity q hq
        omega
      unfold aGW qx
      rw [PD,hchild]
      ring
    _≤(d.factorial:ℚ)*((1 :ℚ)*(lV P).natDegree *
        (lV P).leadingCoeff) := by simpa only [Yc] using hmul
    _=aGW φ p:= by
      change _=qx P
      rw [qx ,hparent,WY ,Kp]
      ring
end
end ML
end
section
namespace cyr
noncomputable section
open scoped BigOperators
open aA6 (aeh DL)
variable {σ:Type}
private def cut (bad:nX (σ →₀ ℕ)) (v :σ) :ℕ :=
 bad.sup fun b=>b v
private abbrev tu (c:σ→ℕ) := ∀ v,Fin (c v+1)
private def clip (c x :σ→ℕ) :tu c :=
 fun v=>⟨min (x v) (c v),Zi (Fa _ _)⟩
private theorem cW3 {bad:nX (σ →₀ ℕ)} {b:σ →₀ ℕ}
  (hb:b∈bad) (x :σ→ℕ) :
  (∀ v,b v≤(clip (cut bad) x v :ℕ)) ↔ ∀ v,b v≤x v := by
 refine ⟨fun h v=>(h v).trans (F9 _ _),fun h v => ?_⟩
 exact le_min (h v) (TZ (f := fun b:σ →₀ ℕ=>b v) hb)
variable [sI σ]
private def free {c:σ→ℕ} (slot:σ→Fin 5) (b:tu c) (i:Fin 5) :nX σ :=
 Finset.univ.filter fun v=>slot v=i∧(b v :ℕ)=c v
private theorem ahR {c:σ→ℕ} {slot:σ→Fin 5} {b:tu c} {i:Fin 5} {v :σ} :
  v∈free slot b i↔slot v=i∧(b v :ℕ)=c v := by
 simp [free]
private def degree (slot:σ→Fin 5) (x :σ→ℕ) (i:Fin 5) :ℕ :=
 ∑ v,if slot v=i then x v else 0
private theorem boQ (slot:σ→Fin 5) (x y :σ→ℕ) (i:Fin 5) :
  degree slot (x+y) i=degree slot x i+degree slot y i:= by
 simp only [degree,← wR]
 exact qJ rfl fun v _=> by by_cases h:slot v=i <;> simp [h]
private theorem cJZ (slot:σ→Fin 5) (e :σ →₀ ℕ) (i:Fin 5) :
   degree slot e i=aeh slot e i:= by
 rw [aeh,Finsupp.sum_fintype]
 · rfl
 · intro v
   split <;> rfl
private abbrev shift {c:σ→ℕ} (slot:σ→Fin 5) (b:tu c) (i:Fin 5) :ℕ :=
 degree slot (fun v=>(b v :ℕ)) i
private def threshold (bad:nX (σ →₀ ℕ)) :ℕ:=(∑ v,cut bad v)+1
private theorem cpq (slot:σ→Fin 5) {bad:nX (σ →₀ ℕ)}
  (b:tu (cut bad)) (i:Fin 5) :
  shift slot b i<threshold bad:= by
 apply Zi
 change (∑ v,if slot v=i then (b v :ℕ) else 0) ≤ ∑ v,cut bad v
 exact FK fun v _=> by
  by_cases hv :slot v=i
  · simp only [x7 hv]
    exact UY (b v).isLt
  · simp [hv]
variable [xL σ]
private def residue {c:σ→ℕ} (slot:σ→Fin 5) (b:tu c)
  (x : ∀ i:Fin 5,free slot b i→ℕ) (v :σ) :ℕ :=
 if h:v∈free slot b (slot v) then x (slot v) ⟨v,h⟩ else 0
private theorem cfk {c:σ→ℕ} (slot:σ→Fin 5) (b:tu c)
  (x : ∀ i:Fin 5,free slot b i→ℕ) (i:Fin 5) (v :free slot b i) :
  residue slot b x v.val=x i v := by
 obtain ⟨v,hv⟩:=v
 have hi:=(ahR.mp hv).1
 subst i
 rw [residue,Aa hv]
private theorem cJ6 {c:σ→ℕ} (slot:σ→Fin 5) (b:tu c)
    (x : ∀ i:Fin 5,free slot b i→ℕ) (i:Fin 5) :
    degree slot (residue slot b x) i = ∑ v :free slot b i,x i v := by
  calc
    _ = ∑ v∈free slot b i,residue slot b x v := by
      rw [degree,free,Finset.sum_filter]
      refine qJ rfl fun v _ => ?_
      by_cases hi:slot v=i
      · by_cases hb: (b v :ℕ)=c v
        · simp [hi,hb]
        · have hv :v∉free slot b (slot v) := fun h=>hb (ahR.mp h).2
          have hr :residue slot b x v=0:=dite_eq_right hv
          simp [hi,hb,hr]
      · simp [hi]
    _ = ∑ v :free slot b i,residue slot b x v.val :=
      Finset.sum_subtype _ (fun _=>Iff.rfl) _
    _ = _:=qJ rfl fun v _=>cfk slot b x i v
private theorem cFJ {c:σ→ℕ} (slot:σ→Fin 5) (b:tu c)
   (x : ∀ i:Fin 5,free slot b i→ℕ) :
   clip c ((fun v=>(b v :ℕ))+residue slot b x)=b:= by
 funext v
 apply Fin.ext
 change min ((b v :ℕ)+residue slot b x v) (c v)=(b v :ℕ)
 by_cases hb: (b v :ℕ)=c v
 · rw [hb,min_eq_right (yQ _ _)]
 · have hv :v∉free slot b (slot v) := fun h=>hb (ahR.mp h).2
   rw [residue,dite_eq_right hv,v8 ,min_eq_left (UY (b v).isLt)]
private theorem fW7 (c:σ→ℕ) (slot:σ→Fin 5) (e :σ→ℕ) :
   (fun v=>((clip c e) v :ℕ)) +
     residue slot (clip c e) (fun _ v=>e v.val-((clip c e) v.val :ℕ))=e := by
 funext v
 change ((clip c e) v :ℕ)+residue slot (clip c e) _ v=e v
 rw [residue]
 split
 · exact zp3 (F9 _ _)
 · rename_i hv
   have hlt:min (e v) (c v)<c v :=wA (Fa _ _)
     (fun h=>hv (ahR.mpr ⟨rfl,h⟩))
   have hle :e v≤ c v := by omega
   change min (e v) (c v)+0=e v
   rw [min_eq_left hle,v8]
private abbrev aYN (slot:σ→Fin 5) (bad:nX (σ →₀ ℕ)) :=
 {b:tu (cut bad) // (∀ q∈bad,¬ ∀ v,q v≤(b v :ℕ)) ∧
   ∀ i,(free slot b i).Nonempty}
private abbrev Slice (slot:σ→Fin 5) (bad:nX (σ →₀ ℕ)) (u:Fin 5→ℕ) :=
 {e :σ →₀ ℕ // aeh slot e=u ∧ ∀ q∈bad,¬ q≤e}
private abbrev Fiber (slot:σ→Fin 5) (u:Fin 5→ℕ) {c:σ→ℕ} (b:tu c) :=
 ∀ i:Fin 5,{x :free slot b i→ℕ // ∑ v,x v=u i - shift slot b i}
private def assemble (slot:σ→Fin 5) (bad:nX (σ →₀ ℕ)) (u:Fin 5→ℕ)
    (hu : ∀ i,threshold bad≤u i) :
    (Σ b:aYN slot bad,Fiber slot u b.val)→Slice slot bad u
  | ⟨b,x⟩=> by
    let e :σ→ℕ:=(fun v=>(b.val v :ℕ))+residue slot b.val (fun i=>(x i).val)
    refine ⟨Finsupp.equivFunOnFinite.symm e,?_,?_⟩
    · funext i
      rw [← cJZ]
      change degree slot ((fun v=>(b.val v :ℕ)) +
        residue slot b.val (fun i=>(x i).val)) i=u i
      rw [boQ,cJ6,(x i).property]
      exact zp3 ((cpq slot b.val i).le.trans (hu i))
    · intro q hq hle
      refine b.property.1 q hq ?_
      have hc:=cW3 hq e |>.mpr (fun v=>hle v)
      rwa [show clip (cut bad) e=b.val from cFJ slot b.val _] at hc
private theorem dto (slot:σ→Fin 5) (bad:nX (σ →₀ ℕ))
    (u:Fin 5→ℕ) (hu : ∀ i,threshold bad≤u i) :
    Function.Bijective (assemble slot bad u hu) := by
  constructor
  · rintro ⟨b,x⟩ ⟨c,y⟩ h
    have hb (b:aYN slot bad) (x :Fiber slot u b.val) :
        clip (cut bad) (assemble slot bad u hu ⟨b,x⟩).val=b.val :=
      cFJ slot b.val _
    have hbc:b=c:=t6 ((hb b x).symm.trans
      ((qy (fun e :Slice slot bad u=>clip (cut bad) e.val) h).trans (hb c y)))
    subst c
    have hxy :x=y := by
      funext i
      apply t6
      funext v
      have he :=qy (fun e :Slice slot bad u=>e.val v.val) h
      change (b.val v.val :ℕ)+residue slot b.val (fun j=>(x j).val) v.val =
        (b.val v.val :ℕ)+residue slot b.val (fun j=>(y j).val) v.val at he
      have hr :=Nat.add_left_cancel he
      rwa [cfk slot b.val _ i v,cfk slot b.val _ i v] at hr
    subst y
    rfl
  · intro e
    let b:=clip (cut bad) e.val
    let x (i:Fin 5) (v :free slot b i) :=e.val v.val-(b v.val :ℕ)
    have hrestore : (fun v=>(b v :ℕ))+residue slot b x=e.val :=
      fW7 (cut bad) slot e.val
    have hsum (i:Fin 5) :shift slot b i+(∑ v,x i v)=u i:= by
      rw [← cJ6,← boQ,hrestore,cJZ,e.property.1]
    have hfree (i:Fin 5) : (free slot b i).Nonempty := by
      by_contra h
      have :IsEmpty (free slot b i) :=⟨fun v=>h ⟨v.val,v.property⟩⟩
      have hs :=hsum i
      rw [Finset.univ_eq_empty,TH,v8] at hs
      exact ((cpq slot b i).trans_le (hu i)).ne hs
    have hok (q:σ →₀ ℕ) (hq:q∈bad) :
        ¬ ∀ v,q v≤(b v :ℕ) :=
      fun h=>e.property.2 q hq ((cW3 hq e.val).mp h)
    let b' : aYN slot bad:=⟨b,hok,hfree⟩
    let x' : Fiber slot u b'.val := fun i=>⟨x i,by
      change (∑ v,x i v)=u i - shift slot b i
      have hs :=hsum i
      omega⟩
    refine ⟨⟨b',x'⟩,t6 ?_⟩
    change Finsupp.equivFunOnFinite.symm
      ((fun v=>(b v :ℕ))+residue slot b x)=e.val
    rw [hrestore,Finsupp.equivFunOnFinite_symm_coe]
private def dOE (s :nX σ) (n:ℕ) :
   s.finsuppAntidiag n ≃ {f :s→ℕ // ∑ v,f v=n} :=
 (Finset.finsuppAntidiagEquiv s n).trans (Sym.equivNatSumOfFintype s n)
omit [sI σ] in
private theorem d2j (s :nX σ) (hs :s.Nonempty)
   {u k :ℕ} (hk :k≤u) :
   ((s.finsuppAntidiag (u - k)).card:ℚ) =
     (zcb ℚ (s.card - 1) k).eval (u:ℚ) := by
 rw [Finset.card_finsuppAntidiag_nat_eq_choose,
   Polynomial.preHilbertPoly_eq_choose_add_sub ℚ (s.card - 1) (k :=k) (n:=u) (by omega)]
 apply qy (fun n:ℕ=>(n:ℚ))
 have hpos :=Finset.card_pos.mpr hs
 rw [Nat.choose_symm_of_eq_add (a :=u - k) (b:=s.card - 1) (by omega)]
 congr 1
 omega
theorem proof :aA6.c2 := by
  classical
  intro σ _ slot bad
  let:sI σ:=FQ σ
  let:sI (aYN slot bad) :=FQ _
  let m:=Fintype.card (aYN slot bad)
  let idx :aYN slot bad ≃ Fin m:=PM _
  let p (a :Fin m) (i:Fin 5) :=
    zcb ℚ ((free slot (idx.symm a).val i).card - 1)
      (shift slot (idx.symm a).val i)
  refine ⟨m,p,?_,threshold bad,?_⟩
  · intro a i
    dsimp only [p]
    rw [Polynomial.leadingCoeff_preHilbertPoly]
    positivity
  · intro u hu
    let e :Slice slot bad u ≃
        Σ b:aYN slot bad,∀ i:Fin 5,
          (free slot b.val i).finsuppAntidiag (u i - shift slot b.val i) :=
      (Equiv.ofBijective _ (dto slot bad u hu)).symm.trans
        (Equiv.sigmaCongrRight fun b =>
          Equiv.piCongrRight fun i =>
            (dOE (free slot b.val i) (u i - shift slot b.val i)).symm)
    rw [DL,← zPH]
    change (Nat.card (Slice slot bad u) :ℚ)= _
    rw [Nat.card_congr e,zey]
    simp only [Fintype.card_sigma,Fintype.card_pi,Fintype.card_coe,Nat.cast_sum,Nat.cast_prod]
    rw [← idx.sum_comp (fun a => ∏ i,(p a i).eval (u i:ℚ))]
    refine qJ rfl fun b _=>Mz rfl fun i _ => ?_
    simpa only [p,zwn] using
      d2j (free slot b.val i) (b.property.2 i) ((cpq slot b.val i).le.trans (hu i))
end
end cyr
end
section
namespace bzD
noncomputable section
open dN vS B8 aA6 MvPolynomial
section GD
variable {σ τ k R:Type} [uJ k] [ov R] [wB k R]
private def W9 (f :lz σ k →ₐ[k] lz τ R)
   (u:τ →₀ ℕ) :lz σ k →ₗ[k] R :=
 ((lcoeff R u).restrictScalars k).comp f.toLinearMap
private theorem cGx
  (f :lz σ k →ₐ[k] lz τ R)
  (tag : (σ →₀ ℕ)→(τ →₀ ℕ)) (a : (σ →₀ ℕ)→R)
  (hf : ∀ e,f (pU e 1)=pU (tag e) (a e)) (u:τ →₀ ℕ)
  (e :σ →₀ ℕ) [xL τ] :
  W9 f u (pU e 1)=if tag e=u then a e else 0:= by
 change (f (pU e 1)).coeff u= _
 rw [hf,Pv]
private theorem cZE
   (f :lz σ k →ₐ[k] lz τ R)
   (tag : (σ →₀ ℕ)→(τ →₀ ℕ)) (a : (σ →₀ ℕ)→R)
   (hf : ∀ e,f (pU e 1)=pU (tag e) (a e)) (u:τ →₀ ℕ)
   (S:Set (σ →₀ ℕ)) :
   (xI k {e | tag e=u∧e∈S}).map (W9 f u) =
     (xI k S).map (W9 f u) := by
 classical
 apply sS
 · exact Pr (VC k fun _ he=>he.2)
 · rw [In,MS ,Sv]
   rintro _ ⟨_,⟨e,he,rfl⟩,rfl⟩
   by_cases h:tag e=u
   · exact ⟨pU e 1,(monomial_mem_restrictSupport k).mpr (Or.inl ⟨h,he⟩),rfl⟩
   · rw [cGx f tag a hf,t4 h]
     exact Submodule.zero_mem _
private theorem ea7
   (f :lz σ k →ₐ[k] lz τ R)
   (tag : (σ →₀ ℕ)→(τ →₀ ℕ)) (a : (σ →₀ ℕ)→R)
   (hf : ∀ e,f (pU e 1)=pU (tag e) (a e))
   (o:KH.{0,0} σ) (u:τ →₀ ℕ) :
   Gr k (v9 (W9 f u)) =
     {e | tag e=u∧e∈o.standardExponents (p9 f.toRingHom)}.ncard:= by
 classical
 let I:=p9 f.toRingHom
 let S := {e | tag e=u∧e∈o.standardExponents I}
 let W:=xI k S
 have hstandard: (o.standardSpace I).map (W9 f u) =
     v9 (W9 f u) := by
   refine sS LinearMap.map_le_range ?_
   rintro _ ⟨p,rfl⟩
   obtain ⟨q,hq,hpq,_⟩:=o.exists_mem_standardSpace_sub_mem I p
   have heq :f p=f q:= by
     change f (p - q)=0 at hpq
     exact sub_eq_zero.mp (by simpa only [Dv] using hpq)
   exact ⟨q,hq,by
     change (f q).coeff u=(f p).coeff u
     rw [heq]⟩
 have himage :W.map (W9 f u)=v9 (W9 f u) :=
   (cZE f tag a hf u (o.standardExponents I)).trans hstandard
 have hhomogeneous :
     W≤((xI R {u}).restrictScalars k).comap f.toLinearMap:= by
   change xI k S≤_
   rw [In,Sv]
   rintro _ ⟨e,he,rfl⟩
   change f (pU e 1)∈xI R {u}
   rw [hf,monomial_mem_restrictSupport]
   exact Or.inl he.1
 let g:=(W9 f u).domRestrict W
 have hg:qz g:= by
   apply (injective_iff_map_eq_zero g).mpr
   intro p hp
   have hs : ∀ e∈(f p.val).support,e=u :=
     (mem_restrictSupport_iff R).mp (hhomogeneous p.property)
   have hz :f p.val=0:= by
     rw [eq_monomial_of_support_subset_singleton hs]
     change (f p.val).coeff u=0 at hp
     rw [hp,monomial_zero]
   apply t6
   exact o.eq_zero_of_mem_standardSpace_of_mem
     (VC k (fun e (he :e∈S)=>he.2) p.property) hz
 rw [← himage,← LinearMap.range_domRestrict,
   ← (zjT g hg).finrank_eq,
   Module.finrank_eq_nat_card_basis (basisRestrictSupport k S),zPH]
end GD
private theorem fSZ (B:lS) (P:aU g9) (u:Fin 5→ℕ) :
   v9 (W9 (a8E B P) (Finsupp.equivFunOnFinite.symm u)) =
     Kx B P u:= by
 classical
 let t:Exponent:=Finsupp.equivFunOnFinite.symm u
 let f :=a8E B P
 let a := fun e=>mD P (pU (aaB B e) 1)
 let L:=W9 f t
 change v9 L= _
 have hmap :
     (xI ox {e | amP B e=t}).map L=v9 L:= by
   simpa only [Set.mem_univ,and_true,restrictSupport_univ,Submodule.map_top] using
     cZE f (amP B) a (cp2 B P) t Set.univ
 have hL (e :alh B →₀ ℕ) (he :amP B e=t) :
     L (pU e 1)=a e := by
   rw [show L=W9 f t from rfl,
     cGx f (amP B) a (cp2 B P),x7 he]
 rw [← hmap,Kx,In,In,
   MS ,MS]
 congr 1
 rw [SU,SU,dWG B u,SU]
 exact Set.image_congr hL
private def b26 (σ:Type) [qU σ] :KH.{0,0} σ:= by
 let _:=FQ σ
 let _:LinearOrder σ:=Z0 _ (PM σ).injective
 have :WellFoundedGT σ:=XB
 exact zwf
theorem proof :aA6.c1 := by
 classical
 intro B P
 let o:=b26 (alh B)
 refine ⟨o,fun u => ?_⟩
 rw [← fSZ]
 rw [ea7 (a8E B P) (amP B)
  (fun e=>mD P (pU (aaB B e) 1)) (cp2 B P) o]
 simp only [gyQ]
end
end bzD
end
section
namespace Rl
noncomputable section
open Polynomial K1 aR dN wH
open scoped BigOperators
private theorem SZ:qz j8 :=
 (lJ lN ox).injective.comp (GF ao[X] lN)
theorem Ue {P:af 4} {S:ao[X]} :
  bC P∈Ch S↔cK P S=0:= by
 unfold Ch
 rw [RingHom.mem_ker]
 change oy _ (z9 j8 P)=0↔_
 rw [znM]
 change Bf j8 (⇑j8 ∘ jet S) P=0↔_
 rw [← MvPolynomial.eval₂_comp]
 exact Ts _ SZ
@[simp] theorem bpC (q:af 3) (S:ao[X]) :
   cK (He q) S=cK q S:= by
  rw [cK,He,ZJ]
  rfl
theorem cM4 {q:af 3} {f :af 4} {S:ao[X]}
  (hf :cK f S=0) (hreg:qg f S) (hq:cK q S=0) :
  cK (acp q) S=0:= by
 have htop:oj (He q)=0:= by
  apply zUp
  intro hv
  obtain ⟨i,_,hi⟩:=zcz xm q hv
  exact JK i hi
 have h:=aNw f (He q) S hf
 rw [bpC,hq,pQ,u5] at h
 simp only [u6,htop,u5 ,sub_zero] at h
 change oy (jet S) (_ *_)=0 at h
 rw [oK] at h
 exact (mul_eq_zero.mp h).resolve_left hreg
theorem bFl (P:af 4) (S:ao[X]) :
  Ve P S=cK P S:= by
 have he :vG (lJ ao ao)=GR ao[X] := by
  apply zh
  intro p
  change p.map (lJ ao ao)=p
  simp
 unfold Ve cK
 rw [he,MvPolynomial.eval₂_id]
 rfl
private theorem cXX {f :af 4} {q:af 3} {S:ao[X]}
   (hf :Dd f S) (hr :qg f S) (hq:cK q S=0) :
   ∃ aI,aqk f q aI∧aI≤Ch S:= by
 have hl:kC f (He q)≤Ch S:= by
   apply Ideal.span_le.mpr
   intro P hP
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP
   rcases hP with rfl | rfl
   · exact Ue.mpr hf.1
   · exact Ue.mpr ((bpC q S).trans hq)
 have : (Ch S).IsPrime :=Oc (An S)
 obtain ⟨aI,hZ,hle⟩:=Cy hl
 refine ⟨aI,⟨hZ,?_,?_⟩,hle⟩
 · intro hz
   have h:=Ue.mp (hle hz)
   rw [bpC,Ex.a3E] at h
   exact hf.2 h
 · exact fun hz=>hr (Ue.mp (hle hz))
end
end Rl
end
section
namespace aFW
noncomputable section
open Polynomial K1 aR dN BO wH lB Rl
open scoped BigOperators
def c1 :Prop :=
  ∀ (p q r h:lI),bF p→bF q→bF r→bF h→0<h.t →
    ∀ F Q:c9,S1 F Q→yy F p→yy Q q →
      ∀ (cut:aU c9→c9) (qv :nX (aU c9)),
        (∀ C∈qv,∃ aI,(cy {F,Q}).IsMinimalPrime aI ∧
          aSw aI (cut aI) C∧yy (cut aI) r) →
        32*(∑ C∈qv,pN C (h.scale 6))≤6*iH p q r h
def c2 :Prop :=
  ∀ a :lI,bF a→0<a.t →
    ∀ (aI:aU c9) (P:c9) (C:aU c9),
      aSw aI P C →
      6≤pN C (a.scale 6) ∧
      ∀ (U:c9) (points :nX KE),yy U a→U∉C →
        (∀ y∈points,C≤p9 (oy y)∧oy y U=0) →
        6*points.card≤pN C (a.scale 6)
end
end aFW
end
section
namespace bjC
noncomputable section
open aR dN BO vS Dr lB aFW
open scoped BigOperators
def c1 :Prop :=
  ∀ (J:aU c9) (p:lI) (boxes :List lI),
    bF p→(∀ q∈boxes,bF q)→boxes.length≤3 →
    oY J≤boxes.length+1 →
    ∀ D:c9,VE p D→ vk (mD J D) →
      tW (J ⊔ cy {D}) boxes≤tW J (p :: boxes)
def c2 :Prop :=
  ∀ (J:aU c9) (boxes :List lI),
    (∀ q∈boxes,bF q)→boxes.length≤2→ oY J≤boxes.length →
    ∀ S:nX (aU c9),(∀ P∈S,J.IsMinimalPrime P) →
      (∑ P∈S,tW P boxes)≤tW J boxes
def c3:Prop :=
  ∀ (C:aU c9) (h:lI),C.IsPrime→ oY C=1 →
    bF h→0<h.t →
    (pN C (h.scale 6) :ℚ)≤6*tW C [h]
private theorem dHR {p q:lI} (hp:pG p) (hq:bF q) :
  pG (p.plus q) := by
 obtain ⟨hb,hj,ht⟩:=hp
 obtain ⟨hb',hj'⟩:=hq
 exact ⟨G1 hb hb',by dsimp [y5]; omega,by dsimp [y5]; omega⟩
private theorem eMD {A B:lI→ℚ}
   (h : ∀ p,pG p→A p=B p) {boxes :List lI}
   (hboxes : ∀ q∈boxes,bF q) {p:lI} (hp:pG p) :
   BE A boxes p=BE B boxes p:= by
 induction boxes generalizing p with
 | nil=>exact h p hp
 | cons q boxes ih =>
   have hq:=hboxes q TI
   have hr := fun r hr=>hboxes r (zrw _ hr)
   simp only [BE,ih hr (dHR hp hq),ih hr hp]
private theorem bT9 {p q r h:lI}
   (hboxes : ∀ u∈[p,q,r,h],bF u) :
   tW (⊥ : aU c9) [p,q,r,h]≤(iH p q r h:ℚ)/32 := by
 have hb:pG ⟨3, 3,1⟩:=⟨by decide,by decide,by decide⟩
 unfold tW
 change BE (oZ ⊥ 4) [p,q,r,h] ⟨3,3,1⟩/(2 :ℚ)^4≤_
 rw [eMD aiK.proof hboxes hb]
 let n:=gI (gI (gI (gI Dn p) q) r) h ⟨0,0,0⟩
 have hpoly :BE (fun x=>16*(Dn x :ℚ)/32) [p,q,r,h] ⟨3,3,1⟩ /
     (2 :ℚ)^4=(n:ℚ)/32 := by
   simp only [n,BE,gI,Dn,y5]
   push_cast
   ring
 rw [hpoly]
 have hn:n≤(n.toNat :ℤ) := by omega
 apply div_le_div_of_nonneg_right _ (by norm_num)
 exact_mod_cast hn
private theorem c3t (F Q:c9) :
  (cy {F,Q} : aU c9)=cy {F} ⊔ cy {Q} := by
 rw [← Ideal.span_union]
 rfl
private theorem fV4 {F Q:c9} (h:S1 F Q) :
  vk (mD (cy {F}) Q) := by
 apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
 intro x hx
 obtain ⟨D,rfl⟩:=zf x
 rw [← oK,t3 ,Ideal.mem_span_singleton] at hx
 exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h.dvd_of_dvd_mul_left hx))
private theorem aQG {F Q:c9} (hF:F≠0) (hrel :S1 F Q)
   {S:aU c9} (hS: (cy {F,Q}).IsMinimalPrime S) :oY S=2 := by
 have :=hS.isPrime
 rw [c3t] at hS
 obtain ⟨P,hP,hPS⟩:=Cy (le_sup_left.trans hS.le)
 have :=hP.isPrime
 have hdim:=Ye hF hP
 rw [zey,UZ] at hdim
 have hPne :P ≠ ⊥ := by
   intro heq
   exact hF (Ideal.mem_bot.mp (heq ▸ hP.le (th F)))
 have hheight:P.height = 1 :=
   sS (zx8 _ _ hP) (by
     simpa [Ideal.height_bot] using Mk (bot_lt_iff_ne_bot.mpr hPne))
 obtain ⟨a,ha⟩:=(UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight).principal
 change P=cy {a} at ha
 have hQ:Q∉P:= by
   intro hmem
   have haF:a∣F:=Ideal.mem_span_singleton.mp (ha ▸ hP.le (th F))
   have haQ:a∣Q:=Ideal.mem_span_singleton.mp (ha ▸ hmem)
   exact hP.isPrime.ne_top (ha.trans (Ideal.span_singleton_eq_top.mpr (hrel haF haQ)))
 have hmin:S∈(P ⊔ cy {Q}).minimalPrimes := by
   refine ⟨⟨hS.isPrime,zc hPS (le_sup_right.trans hS.le)⟩,fun U hU hUS => ?_⟩
   exact hS.2 ⟨hU.1,zc (hP.le.trans (le_sup_left.trans hU.2)) (le_sup_right.trans hU.2)⟩ hUS
 have h:=C9 hQ hmin
 change oY S+1=oY P at h
 change oY P+1=4 at hdim
 omega
private theorem gwY (hcut:c1) (hcomp:c2) (hdeg:c3)
    {r h:lI} (hr :bF r) (hh:bF h) (ht:0<h.t)
    {S:aU c9} {D:c9} (hD:yy D r)
    (hS:oY S=2) (T:nX (aU c9)) (hn:T.Nonempty)
    (hT : ∀ C∈T,aSw S D C) :
    (∑ C∈T,(pN C (h.scale 6) :ℚ)/6)≤tW S [r,h] := by
  obtain ⟨C₀,hm⟩:=hn
  have base :=hT C₀ hm
  have hreg:=aPQ base.prime base.proper
  have hJ:oY (S ⊔ cy {D})≤1 :=(aCR hreg).trans (by omega)
  have hsingle : ∀ q∈[h],bF q:= by simpa using hh
  calc
    _ ≤ ∑ C∈T,tW C [h] := by
      apply FK
      intro C hc
      have info :=hT C hc
      have :=info.prime
      have hd:=C9
        info.proper info.component
      change oY C+1=oY S at hd
      have hC:oY C=1 := by omega
      apply (div_le_iff₀ (by norm_num : (0:ℚ)<6)).mpr
      simpa only [qG] using hdeg C h info.component.isPrime hC hh ht
    _≤tW (S ⊔ cy {D}) [h] :=
      hcomp _ [h] hsingle (by simp) (by simpa using hJ) T (fun C hc=>(hT C hc).component)
    _≤tW S [r,h] :=
      hcut S r [h] hr hsingle (by simp) (by simpa using hS.le) D
        (aY3.a6c hD) hreg
theorem of_children (hcut:c1) (hcomp:c2) (hdeg:c3) :aFW.c1 := by
  classical
  intro p q r h hp hq hr hh ht F Q hrel hF hQ cut qv hcurves
  rcases qv.eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  let H :=cy {F}
  let J:=cy {F,Q}
  have hpair :J=H ⊔ cy {Q} := c3t F Q
  have hF0:F≠0:= by
    intro hzero
    obtain ⟨C,hc⟩:=hne
    obtain ⟨S,hs,_⟩:=hcurves C hc
    have hu:uh Q:=hrel (hzero ▸ dvd_zero Q) dvd_rfl
    have hm:Q∈S:=hs.le (Re (by simp))
    exact hs.isPrime.ne_top (S.eq_top_of_isUnit_mem hm hu)
  have hregF:vk (mD (⊥ : aU c9) F) :=
    aPQ Ideal.isPrime_bot (by simpa using hF0)
  have hregQ:vk (mD H Q) :=fV4 hrel
  have hH :oY H≤3:= by
    simpa [H,bEk] using aCR hregF
  have hJ:oY J≤2 := by
    rw [hpair]
    exact (aCR hregQ).trans (by omega)
  have hall : ∀ C:aU c9,∃ S:aU c9,C∈qv →
      J.IsMinimalPrime S∧aSw S (cut S) C∧yy (cut S) r := by
    intro C
    by_cases hc:C∈qv
    · obtain ⟨S,hs⟩:=hcurves C hc
      exact ⟨S,fun _=>hs⟩
    · exact ⟨⊥,fun hm=>(hc hm).elim⟩
  choose aI hsurface using hall
  let uG:=qv.image aI
  let RS (S:aU c9) :=qv.filter fun C=>aI C=S
  let cost (C:aU c9) :=(pN C (h.scale 6) :ℚ)/6
  have hs (S:aU c9) (hm:S∈uG) :
      J.IsMinimalPrime S∧(∑ C∈RS S,cost C)≤tW S [r,h] := by
    obtain ⟨C,hc,rfl⟩:=Finset.mem_image.mp hm
    obtain ⟨hmin,_,hfit⟩:=hsurface C hc
    refine ⟨hmin,gwY hcut hcomp hdeg hr hh ht hfit
      (aQG hF0 hrel hmin)
      _ ⟨C,Finset.mem_filter.mpr ⟨hc,rfl⟩⟩ ?_⟩
    intro C' hc'
    obtain ⟨hm',heq⟩:=Finset.mem_filter.mp hc'
    exact heq ▸ (hsurface C' hm').2.1
  have hrh : ∀ a∈[r,h],bF a := by simp [hr,hh]
  have hqrh : ∀ a∈[q,r,h],bF a := by simp [hq,hr,hh]
  have hpqrh : ∀ a∈[p,q,r,h],bF a := by simp [hp,hq,hr,hh]
  have hsum: (∑ C∈qv,cost C)≤(iH p q r h:ℚ)/32 := by
    calc
      _ = ∑ S∈uG,∑ C∈RS S,cost C :=
        (Finset.sum_fiberwise_of_maps_to (fun _ hc=>Finset.mem_image_of_mem _ hc) cost).symm
      _ ≤ ∑ S∈uG,tW S [r,h] :=
        FK fun S hm=>(hs S hm).2
      _≤tW J [r,h] :=
        hcomp J [r,h] hrh (by simp) (by simpa using hJ) uG (fun S hm=>(hs S hm).1)
      _≤tW H [q,r,h] := by
        rw [hpair]
        exact hcut H q [r,h] hq hrh (by simp) (by simpa using hH) Q
          (aY3.a6c hQ) hregQ
      _≤tW ⊥ [p,q,r,h] := by
        rw [show H=(⊥ : aU c9) ⊔ cy {F} by simp [H]]
        exact hcut ⊥ p [q,r,h] hp hqrh (by simp) (by simp) F
          (aY3.a6c hF) hregF
      _≤_:=bT9 hpqrh
  dsimp only [cost] at hsum
  rw [← Finset.sum_div] at hsum
  have hfinal: (32 :ℚ)*(∑ C∈qv,(pN C (h.scale 6) :ℚ)) ≤
      6*(iH p q r h:ℚ) := by
    linarith [(div_le_div_iff₀ (by norm_num : (0:ℚ)<6)
      (by norm_num : (0:ℚ)<32)).mp hsum]
  exact_mod_cast hfinal
end
end bjC
end
section
set_option maxHeartbeats 600000
namespace as9
noncomputable section
open Polynomial K1 aR dN rW
def contraction (P:aU c9) :aU (af 4) :=
 P.comap (z9 j8)
abbrev aql (f :af 4) :=zUF (oj f)
def adZ (f :af 4) :af 4 →+* aql f :=lJ _ _
def Cm (f :af 4) (P:aU c9) :aU (aql f) :=
 (contraction P).map (adZ f)
abbrev ChartRing (f :af 4) (P:aU c9) :=aql f ⧸ Cm f P
def y3 (f :af 4) (P:aU c9) :af 4 →+* ChartRing f P :=
 (mD (Cm f P)).comp (adZ f)
def QU (f :af 4) (P:aU c9) :ChartRing f P :=
 mD (Cm f P) (Up (oj f))
theorem bhb (f :af 4) (P:aU c9) :
  y3 f P (oj f)*QU f P=1 := by
 change mD (Cm f P) (adZ f (oj f)) *
  mD (Cm f P) (Up (oj f))=1
 rw [← oK,show adZ f (oj f)* Up (oj f)=1
  from IsLocalization.Away.mul_invSelf (oj f),C4]
def Jb (f :af 4) (P:aU c9) :ao →+* ChartRing f P :=
 (y3 f P).comp (MvPolynomial.C.comp qm)
instance adp (f :af 4) (P:aU c9) :wB ao (ChartRing f P) :=
 (Jb f P).toAlgebra
def CW (f :af 4) (P:aU c9) :ChartRing f P :=
 y3 f P (p7 Kv)
def U5 (f :af 4) (P:aU c9) (i:Fin bf) :ChartRing f P :=
  if hi:i.val<4 then y3 f P (nI ⟨i.val,hi⟩)
  else Jb f P (↑i.val.factorial:ao)⁻¹ *
    (QU f P)^(2*i.val)*y3 f P (su f i.val)
def RH (f :af 4) (P:aU c9) : (ChartRing f P)[X] :=
 zS (-CW f P) (∑ i:Fin bf,Df i.val (U5 f P i))
def asX (f :af 4) (P:aU c9)
    (δ:pL ao (ChartRing f P) (ChartRing f P)) :Prop :=
  ∀ Q:af 4,δ (y3 f P Q)= QU f P*y3 f P (u6 f Q)
private def a5l {R:Type} [ov R] {f :af 4} (e :af 4 →+* R)
  (hs :uh (e (oj f))) :aql f →+* R :=
 ztx (oj f) hs
@[simp] private theorem b7B {R:Type} [ov R] {f :af 4}
   (e :af 4 →+* R) (hs :uh (e (oj f))) (Q:af 4) :
   a5l e hs (adZ f Q)=e Q :=
  zaz (oj f) hs Q
def aGX {R:Type} [ov R] {f :af 4} {P:aU c9} (e :af 4 →+* R)
    (he : ∀ Q∈contraction P,e Q=0) (hs :uh (e (oj f))) :ChartRing f P →+* R :=
  Ideal.Quotient.lift (Cm f P) (a5l e hs) (by
    change (contraction P).map (adZ f)≤p9 (a5l e hs)
    rw [JQ]
    intro Q hQ
    change a5l e hs (adZ f Q)=0
    rw [b7B,he Q hQ])
@[simp] theorem bWV {R:Type} [ov R] {f :af 4} {P:aU c9}
   (e :af 4 →+* R) (he : ∀ Q∈contraction P,e Q=0) (hs :uh (e (oj f)))
   (Q:af 4) :aGX e he hs (y3 f P Q)=e Q:= by
  change a5l e hs (adZ f Q)=e Q
  exact b7B e hs Q
private theorem dH3 {R:Type} [ov R] {f :af 4} {P:aU c9}
  (e :af 4 →+* R) (he : ∀ Q∈contraction P,e Q=0) (hs :uh (e (oj f)))
  (hker :p9 e≤ contraction P) :qz (aGX e he hs) := by
 unfold aGX
 apply RingHom.lift_injective_of_ker_le_ideal
 intro a ha
 have ha0:a5l e hs a=0:=ha
 obtain ⟨n,Q,hQ⟩:=zQH (oj f) a
 change a*adZ f (oj f)^n=adZ f Q at hQ
 have hQ0:=qy (a5l e hs) hQ
 rw [oK,ha0,zi ,b7B] at hQ0
 have hmem:adZ f Q∈Cm f P :=
  yL _ (hker (RingHom.mem_ker.mpr hQ0.symm))
 have hunit :uh (adZ f (oj f)^n) :=
  IsLocalization.Away.algebraMap_pow_isUnit (oj f) n
 obtain ⟨u,hu⟩:=hunit
 rw [← hQ,← hu] at hmem
 have h:=(Cm f P).mul_mem_left (↑u⁻¹:aql f) hmem
 simpa only [qG a (↑u:aql f),Units.inv_mul_cancel_left] using h
private def cHu (P:aU c9) :af 4 →+* tJ P :=
 (K4 P).comp (z9 j8)
private theorem bYr {P:aU c9} [P.IsPrime] {Q:af 4} :
   cHu P Q=0↔bC Q∈P :=
 (Ts _ (GF (c9 ⧸ P) (tJ P))).trans
   t3
def afJ (f :af 4) (P:aU c9) [P.IsPrime]
    (hs :bC (oj f)∉P) :ChartRing f P →+* tJ P :=
  aGX (cHu P) (fun _ h=>bYr.mpr h)
    (isUnit_iff_ne_zero.mpr fun h=>hs (bYr.mp h))
@[simp] theorem bef (f :af 4) (P:aU c9) [P.IsPrime]
   (hs :bC (oj f)∉P) (Q:af 4) :
   afJ f P hs (y3 f P Q)=K4 P (bC Q) :=
  bWV _ _ _ _
theorem efy (f :af 4) (P:aU c9) [P.IsPrime]
  (hs :bC (oj f)∉P) :qz (afJ f P hs) :=
 dH3 _ _ _ (fun _ h=>bYr.mp h)
end
end as9
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace as9
noncomputable section
open Polynomial K1 aR dN rW wH Rl
private theorem cGd {R:Type} [ov R] {M:ℕ} (a :Fin M→R) (n:ℕ) :
   (∑ i:Fin M,Df i.val (a i)).coeff n =
     if hn:n<M then a ⟨n,hn⟩ else 0:= by
 classical
 rw [Np]
 split_ifs with hn
 · rw [IU (⟨n,hn⟩:Fin M)]
   · exact coeff_monomial_same _ _
   · intro i _ hi
     exact Un _ (fun he=>hi (Fin.ext he.symm))
   · simp
 · exact C5 fun i _=>Un _ (fun he=>hn (he.symm ▸ i.isLt))
private theorem crL {R:Type} [ov R] {M:ℕ}
   (a :Fin M→R) (U:R[X]) (hdegree :U.natDegree<M)
   (hcoeff : ∀ i,a i=U.coeff i.val) : (∑ i:Fin M,Df i.val (a i))=U:= by
 ext n
 rw [cGd]
 split_ifs with hn
 · exact hcoeff ⟨n,hn⟩
 · exact (zE (hdegree.trans_le (Nat.not_lt.mp hn))).symm
private theorem b1Z {R:Type} [ov R] {M:ℕ}
  {U:R[X]} {x :R} {a :Fin M→R}
  (h:zS x U = ∑ i:Fin M,Df i.val (a i)) (i:Fin M) :
  (oz i.val U).eval x=a i:= by
 rw [← taylor_coeff,h,cGd,Aa i.isLt]
theorem ezp {R:Type} [ov R] {f :af 4} {P:aU c9}
  (φ:ChartRing f P →+* R) : ((RH f P).map φ).natDegree<bf := by
 rw [RH,zla,zm,zWe]
 simp only [map_monomial]
 apply Nat.lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n:=133671) ?_)
  (by decide :133671<bf)
 intro i _
 exact (natDegree_monomial_le _).trans (UY i.isLt)
private theorem dg0 {R:Type} [ov R]
   {f :af 4} {P:aU c9} (φ:ChartRing f P →+* R) :
   zS (φ (CW f P)) ((RH f P).map φ) =
     ∑ i:Fin bf,Df i.val (φ (U5 f P i)) := by
 rw [RH,zla,map_neg,taylor_taylor,add_neg_cancel,taylor_zero,
   zWe]
 simp only [map_monomial]
theorem bpA {R:Type} [ov R]
   {f :af 4} {P:aU c9} (φ:ChartRing f P →+* R) (i:Fin 4) :
   (oz i.val ((RH f P).map φ)).eval (φ (CW f P)) =
     φ (y3 f P (nI i)) := by
 let j:Fin bf :=⟨i.val,i.isLt.trans (by decide :4<bf)⟩
 calc
   _=φ (U5 f P j) :=b1Z (dg0 φ) j
   _ = _:= by
     rw [U5,Aa i.isLt]
private theorem SZ:qz j8 :=
 (lJ lN ox).injective.comp (GF ao[X] lN)
private def bIX (S:ao[X]) :af 4 →+* GeoField :=
 j8.comp (oy (jet S))
private theorem b8M {f :af 4} {S:ao[X]} (hr :qg f S) :
 bIX S (oj f)≠0:=(WW _ SZ).mpr hr
private def aDQ {f :af 4} {P:aU c9} {S:ao[X]}
  (hP:P≤Ch S) (hr :qg f S) :ChartRing f P →+* GeoField :=
 aGX (bIX S) (fun Q hQ=> by
  change j8 (cK Q S)=0
  rw [Ue.mp (hP hQ),pQ]) (b8M hr).isUnit
private theorem bso {f :af 4} {P:aU c9} {S:ao[X]}
  (hP:P≤Ch S) (hr :qg f S) (Q:af 4) :
  aDQ hP hr (y3 f P Q)=j8 (cK Q S) :=
 bWV _ _ _ _
private theorem ezs {f :af 4} {P:aU c9} {S:ao[X]}
  (hP:P≤Ch S) (hr :qg f S) :
  aDQ hP hr (QU f P)=(j8 (cK (oj f) S))⁻¹:= by
 have hmul :y3 f P (oj f)*QU f P=1 :=
  bhb f P
 have hm:=qy (aDQ hP hr) hmul
 rw [oK,bso,C4] at hm
 exact ((mul_eq_one_iff_inv_eq₀ (b8M hr)).mp hm).symm
private theorem cZN {f :af 4} {P:aU c9} {S:ao[X]}
  (hP:P≤Ch S) (hr :qg f S) (a :ao) :
  aDQ hP hr (Jb f P a)=ni a := by
 simp [Jb,bso,cK,ni]
private theorem ezt {f :af 4} {P:aU c9} {S:ao[X]}
    (hP:P≤Ch S) (hr :qg f S) (hf :cK f S=0) (i:Fin bf) :
    aDQ hP hr (U5 f P i)=j8 (oz i.val S) := by
  unfold U5
  split_ifs with hi
  · rw [bso]
    simp [cK,jet]
  · have ho:wY^[i.val] S=C (↑i.val.factorial:ao)*oz i.val S:= by
      have h:=Ml (factorial_smul_hasseDeriv (R:=ao) (k :=i.val)) S
      change i.val.factorial•(oz i.val S)=wY^[i.val] S at h
      simpa only [Mw ,C_eq_natCast] using h.symm
    have hs :=b8M hr
    have hfact : (i.val.factorial:ao)≠0 :=
      lB.ahA (i.isLt.trans (by decide :bf<K1.p))
    simp only [oK,Du,cZN,ezs,bso,
      arh _ _ hf,ho]
    change ni (↑i.val.factorial:ao)⁻¹*(bIX S (oj f))⁻¹^(2*i.val) *
      ((bIX S (oj f))^(2*i.val) *
        (ni (↑i.val.factorial:ao)*j8 (oz i.val S)))= _
    rw [← yB,yB (ni _),← mul_pow,inv_mul_cancel₀ hs,one_pow,
      Dw ,← yB,← oK,inv_mul_cancel₀ hfact,C4 ,t5]
private theorem cZM {f :af 4} {P:aU c9} {S:ao[X]}
  (hP:P≤Ch S) (hr :qg f S) :
  aDQ hP hr (CW f P)=rI:= by
 simp [CW,bso,cK,rI]
private theorem ezu {f :af 4} {P:aU c9} {S:ao[X]}
   (hP:P≤Ch S) (hr :qg f S) (hf :cK f S=0)
   (hd:S.natDegree≤133671) :
   (RH f P).map (aDQ hP hr)=S.map ni:= by
 apply taylor_injective rI
 rw [← cZM hP hr,dg0,cZM hP hr]
 apply crL
 · rw [zm]
   exact natDegree_map_le.trans_lt (hd.trans_lt (by decide :133671<bf))
 · intro i
   rw [ezt hP hr hf,taylor_coeff,hasseDeriv_map]
   change j8 (oz i.val S)=(yl rI)
     (vG ni (oz i.val S))
   have hc: (yl rI).comp (vG ni)=j8:= by
     apply Qw <;> simp [ni,rI]
   exact (yU hc _).symm
private theorem cHg {R:Type} [ov R] {T:Type} [ov T]
   (h:R →+* T) (a :ao →+* R) (U:R[X]) :
   h.comp (Au a (fun i:Fin bf=>U.coeff i.val)) =
     Au (h.comp a) (fun i:Fin bf=>(U.map h).coeff i.val) := by
 rw [zKt]
 simp only [Ee]
theorem specializes {f :af 4} {P:aU c9} [P.IsPrime]
   (hs :bC (oj f)∉P) {S:ao[X]} (hP:P≤Ch S)
   (hr :qg f S) (hf :cK f S=0) (hd:S.natDegree≤133671) :
   Zv (CX P) ((RH f P).map (afJ f P hs)) ≤
     aG7 S:= by
 let e :=Au (Jb f P)
   (fun i:Fin bf=>(RH f P).coeff i.val)
 have hgen: (afJ f P hs).comp (Jb f P)=CX P:= by
   ext a
   change afJ f P hs (y3 f P (p7 (C a)))= _
   rw [bef]
   simp [CX,ni,bC]
 have hmark : (aDQ hP hr).comp (Jb f P)=ni :=
   zh (cZN hP hr)
 have hm:=cHg (aDQ hP hr) (Jb f P) (RH f P)
 rw [hmark,ezu hP hr hf hd] at hm
 have hm' : (aDQ hP hr).comp e=(ni.comp (oy
     (fun i:Fin bf=>S.coeff i.val))) := by
   rw [hm,oy ,zKt]
   simp only [RingHom.comp_id,Ee]
 have hg:=cHg (afJ f P hs) (Jb f P) (RH f P)
 rw [hgen] at hg
 intro Q hQ
 have haux :afJ f P hs (e Q)=0:= by
   change ((afJ f P hs).comp e) Q=0
   rw [hg]
   exact hQ
 have he0:e Q=0:= by
   apply efy f P hs
   simpa only [pQ] using haux
 have hzero : (aDQ hP hr).comp e Q=0:= by simp [he0]
 rw [hm'] at hzero
 change oy (fun i:Fin bf=>S.coeff i.val) Q=0
 exact (Ts _ ni.injective).mp hzero
end
end as9
end
section
namespace agP
noncomputable section
open aR Ex dN wH Rl lB MvPolynomial
@[simp] private theorem ajn (P:af 4) (m:Fin 4 →₀ ℕ) :
    (lX P).coeff m=wY (P.coeff m) := by
  classical
  rw [lX,zqN]
  simp only [Pv,Vl]
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,pQ]
private theorem aCH (P Q:af 4) :
  lX (P+Q)=lX P+lX Q:= by
 ext m
 simp
private theorem a2H (P Q:af 4) :
  lX (P*Q)=P*lX Q+Q*lX P:= by
 classical
 apply MvPolynomial.ext
 intro m
 rw [qG Q,ajn,coeff_mul]
 change _=lcoeff (vj ao) m (_+_)
 rw [t8]
 simp only [lcoeff_apply,coeff_mul,Gi ,Polynomial.derivative_mul,
  ajn,wR]
 exact FU _ _
private theorem btt (P Q:af 4) :
  pK (P+Q)=pK P+pK Q:= by
 simp only [pK,aCH,t8 ,zR,wR]
 abel
private theorem a6r (P Q:af 4) :
    pK (P*Q)=P*pK Q+Q*pK P:= by
  let c (i:Fin 3) :af 4 :=
    p7 (qm ((i.val+1 :ℕ) :ao))*nI i.succ
  have hs : (∑ i:Fin 3,c i*pderiv i.castSucc (P*Q)) =
      P*(∑ i:Fin 3,c i*pderiv i.castSucc Q) +
        Q*(∑ i:Fin 3,c i*pderiv i.castSucc P) := by
    rw [zg ,zg ,← wR]
    apply qJ rfl
    intro i _
    rw [pderiv_mul]
    ring
  unfold pK
  rw [a2H,hs,zR,zR]
  exact add_add_add_comm _ _ _ _
theorem cSL (f P Q:af 4) :
  u6 f (P+Q)=u6 f P+u6 f Q:= by
 simp only [u6,btt,oj,t8 ,zR]
 ring
theorem ZF (f P Q:af 4) :
  u6 f (P*Q)=P*u6 f Q+Q*u6 f P:= by
 simp only [u6,a6r,oj,pderiv_mul]
 ring
@[simp] theorem cSN (f :af 4) :u6 f f=0:= by
  simp only [u6,qG (oj f),sub_self]
@[simp] theorem gpD (q:af 3) :oj (He q)=0:= by
  apply zUp
  intro hv
  obtain ⟨i,_,hi⟩:=zcz xm q hv
  exact JK i hi
private theorem dL9 (w:Fin 4→ℕ) (P:af 4) :
  (lX P).weightedTotalDegree w≤P.weightedTotalDegree w:= by
 apply aJY
 intro m hm
 contrapose! hm
 simp [MvPolynomial.notMem_support_iff.mp hm]
private theorem bKl (w:Fin 4→ℕ) (d Δ:ℕ)
   (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
   (hw : ∀ i:Fin 3,w i.castSucc≤d) (P:af 4)
   (hP:P.weightedTotalDegree w≤d) : (pK P).weightedTotalDegree w≤d+Δ:= by
 classical
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
 unfold pK
 apply zcy
 · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
     ((dL9 w P).trans (hP.trans (yQ _ _)))
 · apply VO
   intro i _
   apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
   rw [yB]
   apply (Po w _ _).trans
   have hp:=(weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
     (Nat.sub_le_sub_right hP (w i.castSucc))
   have he :=hshift i
   have hi:=hw i
   exact (weightedTotalDegree_mul_le _ _ _).trans
     ((G1 (abx w _) hp).trans (by omega))
theorem bZ5 (q:af 3) : (He q).degreeOf 3=0:= by
 rw [← weightedTotalDegree_piSingle,He,
  weightedTotalDegree_rename_of_injective (Fin.castSucc_injective 3)]
 have hw: (Pi.single (3:Fin 4) 1 :Fin 4→ℕ) ∘ xm=(0:Fin 3→ℕ) := by
  funext i
  have hi:i.castSucc≠(3:Fin 4) :=JK i
  simp [hi]
 rw [hw]
 simp [weightedTotalDegree,Finsupp.weight_apply]
end
end agP
end
section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace as9
noncomputable section
open Polynomial K1 aR dN rW Rl
def c1 :Prop :=
  ∀ (f :af 4) (P:aU c9),P.IsPrime →
    bC (oj f)∉P→ Invariant f P →
    ∃ δ:pL ao (ChartRing f P) (ChartRing f P),asX f P δ
def c2 :Prop :=
  ∀ (f :af 4) (P:aU c9) (hp:P.IsPrime)
    (hs :bC (oj f)∉P),
    tB f (90*180265 - 1)→bC f∈P →
    bC (vU f)∈P →
    ∀ δ:pL ao (ChartRing f P) (ChartRing f P),
      asX f P δ →
      jW (CX P) f
        ((RH f P).map (@afJ f P hp hs))=0
def c3:Prop :=
  ∀ (P:aU c9) (_hp:P.IsPrime) (U: (tJ P)[X]),
    P.height=2→U.natDegree<bf →
    (∀ i:Fin 4,(oz i.val U).eval (K4 P (p7 rI)) =
      K4 P (nI i)) →
    2≤(lV (Zv (CX P) U)).natDegree
private theorem bPa (P:aU c9) [P.IsPrime]
    (U: (tJ P)[X]) (Q:af 4)
    (hU : ∀ i:Fin 4,(oz i.val U).eval (K4 P (p7 rI)) =
      K4 P (nI i)) :
    (jW (CX P) Q U).eval (K4 P (p7 rI)) =
      K4 P (bC Q) := by
  let x :=K4 P (p7 rI)
  let e :=(yl x).comp (vG (CX P))
  have he :e=(K4 P).comp (MvPolynomial.C.comp j8) := by
    apply Qw
    · intro a
      simp [e,CX,ni]
    · simp [e,x,rI]
  change (yl x) (Bf (vG (CX P))
    (fun i:Fin 4=>oz i.val U) Q)= _
  rw [Te]
  have h:Au e (fun i=>(yl x) (oz i.val U)) =
      (K4 P).comp (z9 j8) := by
    apply FV
    · intro c
      simpa only [HZ,S2 ,MvPolynomial.map_C] using
        yU he c
    · intro i
      simpa only [HZ,Ww ,MvPolynomial.map_X,
        coe_evalRingHom,x] using hU i
  exact yU h Q
private theorem bDc {P:aU c9} [P.IsPrime] {Q:c9}
   (h:Q∉P) :K4 P Q≠0 :=
 (WW _ (GF (c9 ⧸ P) (tJ P))).mpr
   (fun he=>h (Ideal.Quotient.eq_zero_iff_mem.mp he))
end
end as9
end
section
set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 800000
namespace bRC
noncomputable section
open aR dN as9 agP
private theorem b3J (f :af 4) (a :ao) :
  u6 f (p7 (qm a))=0:= by
 have h:lX (p7 (qm a))=0:= by
  classical
  rw [lX]
  apply C5
  intro m _
  rw [RD]
  split <;> simp
 simp [u6,pK,oj,h]
private def bLD (f :af 4) (P:aU c9) :af 4 →+* Vz (ChartRing f P) where
  toFun Q:=(y3 f P Q,QU f P*y3 f P (u6 f Q))
  map_zero' := by
    apply G8
    · exact pQ (y3 f P)
    · have h:u6 f 0=0:= by
        simpa only [pQ] using b3J f 0
      change QU f P*y3 f P (u6 f 0)=0
      rw [h,pQ,u5]
  map_one' := by
    apply G8
    · exact C4 (y3 f P)
    · have h:u6 f 1=0:= by
        simpa only [C4] using b3J f 1
      change QU f P*y3 f P (u6 f 1)=0
      rw [h,pQ,u5]
  map_add' Q R:= by
    apply G8
    · exact t8 (y3 f P) Q R
    · change QU f P*y3 f P (u6 f (Q+R)) =
        QU f P*y3 f P (u6 f Q) +
          QU f P*y3 f P (u6 f R)
      rw [cSL,t8 ,zR]
  map_mul' Q R:= by
    apply G8
    · exact oK (y3 f P) Q R
    · change QU f P*y3 f P (u6 f (Q*R)) =
        y3 f P Q*(QU f P*y3 f P (u6 f R)) +
          (QU f P*y3 f P (u6 f Q))*y3 f P R
      simp only [ZF,t8 ,oK]
      ring
private theorem aO5 {f :af 4} {P:aU c9} {Q:af 4}
  (h:Q∈contraction P) :y3 f P Q=0 :=
 Ideal.Quotient.eq_zero_iff_mem.mpr (yL (adZ f) h)
theorem proof :as9.c1 := by
  intro f P _hp _hs hinv
  let _:ov (Vz (ChartRing f P)) :=inferInstance
  have hzero (Q:af 4) (hQ:Q∈contraction P) :bLD f P Q=0:= by
    apply G8
    · exact aO5 hQ
    · change QU f P*y3 f P (u6 f Q)=0
      rw [aO5 (hinv Q hQ),u5]
  have hunit :uh (bLD f P (oj f)) := by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    change uh (y3 f P (oj f))
    exact isUnit_iff_exists_inv.mpr ⟨QU f P,bhb f P⟩
  let e :ChartRing f P →+* Vz (ChartRing f P) :=
    aGX (f :=f) (P:=P) (bLD f P) hzero hunit
  have he (Q:af 4) :e (y3 f P Q)=bLD f P Q :=
    bWV _ _ _ Q
  have hefst (a :ChartRing f P) : (e a).fst=a := by
    have h: (TrivSqZeroExt.fstHom (ChartRing f P) (ChartRing f P)
        (ChartRing f P)).toRingHom.comp e=GR (ChartRing f P) := by
      apply Ideal.Quotient.ringHom_ext
      apply IsLocalization.ringHom_ext (Submonoid.powers (oj f))
      apply zh
      intro Q
      change (e (y3 f P Q)).fst=y3 f P Q
      exact qy TrivSqZeroExt.fst (he Q)
    exact yU h a
  have hsnd_mul (a b:ChartRing f P) :
      (e (a*b)).snd=a*(e b).snd+(e a).snd*b:= by
    rw [oK]
    change (e a).fst*(e b).snd+(e a).snd*(e b).fst= _
    simp only [hefst]
  have hconst (a :ao) : (e (lJ ao (ChartRing f P) a)).snd=0:= by
    change (e (y3 f P (p7 (qm a)))).snd=0
    rw [he]
    change QU f P*y3 f P (u6 f (p7 (qm a)))=0
    rw [b3J,pQ,u5]
  have hsmul (a :ao) (b:ChartRing f P) :
      a•b=lJ ao (ChartRing f P) a*b :=
    @NX ao (ChartRing f P) _ _
      (Ideal.Quotient.algebra ao (I:=Cm f P)) a b
  have hadd (a b:ChartRing f P) : (e (a+b)).snd=(e a).snd+(e b).snd:= by
    rw [t8] <;> rfl
  have hlinear (a :ao) (b:ChartRing f P) :
      (e (lJ ao (ChartRing f P) a*b)).snd=a•(e b).snd:= by
    rw [hsnd_mul,hconst,zi ,v8 ,hsmul]
  let D := @LinearMap.mk ao ao _ _ (GR ao) (ChartRing f P) (ChartRing f P) _ _
    (@Algebra.toModule ao (ChartRing f P) _ _ (adp f P))
    (Submodule.Quotient.module' (Cm f P))
    ⟨fun a=>(e a).snd,hadd⟩ hlinear
  refine ⟨Derivation.mk' D ?_,?_⟩
  · intro a b
    change (e (a*b)).snd=a*(e b).snd+b*(e a).snd
    rw [hsnd_mul,qG b]
  · intro Q
    change (e (y3 f P Q)).snd= _
    exact qy TrivSqZeroExt.snd (he Q)
end
end bRC
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace bzK
noncomputable section
open Polynomial aR dN as9
theorem cac {f :af 4} {P:aU c9} {Q:af 4}
  (hQ:bC Q∈P) :y3 f P Q=0 :=
 Ideal.Quotient.eq_zero_iff_mem.mpr (yL _ hQ)
private theorem aTO (c:ao[X]) :
  lX (p7 c)=p7 (wY c) := by
 classical
 ext m
 rw [lX,zqN]
 simp only [Pv,Vl,RD]
 split_ifs <;> simp_all [zuk,RD]
private theorem bnq (i:Fin 4) :
  lX (nI i)=0:= by
 classical
 simp [lX,RC]
private theorem b0t {f :af 4} {P:aU c9}
  {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ)
  {Q:af 4} (hQ:oj Q=0) :
  δ (y3 f P Q)=y3 f P (pK Q) := by
 rw [hδ,u6,hQ,u5 ,sub_zero,oK,← yB,
  qG (QU f P),bhb,t5]
theorem dHV {f :af 4} {P:aU c9}
  {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ) :
  δ (CW f P)=1 := by
 rw [CW,b0t hδ (by simp [oj])]
 simp [pK,aTO]
theorem dHX {f :af 4} {P:aU c9}
  {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ) (a :ao) :
  δ (Jb f P a)=0:= by
 change δ (y3 f P (p7 (C a)))=0
 rw [b0t hδ (by simp [oj])]
 simp [pK,aTO]
private theorem dIR {f :af 4} {P:aU c9}
   {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ)
   (i:Fin 3) :
   δ (y3 f P (nI i.castSucc)) =
     (↑(i.val+1) :ChartRing f P)*y3 f P (nI i.succ) := by
 have hc (a :ℕ) :p7 (C (a :ao))=(a :af 4) := by simp
 rw [b0t hδ (by
   rw [oj,show (3:Fin 4)=yJ 3 by decide]
   exact MvPolynomial.pderiv_X_of_ne (JK i))]
 fin_cases i <;>
   norm_num [pK,bnq,Fin.sum_univ_three,MvPolynomial.pderiv_X,
     LQ,xm,Fin.succ,hc] <;> rw [map_ofNat]
private theorem edh {f :af 4} {P:aU c9}
  {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ)
  (Q:af 4) :
  y3 f P (u6 f Q)=y3 f P (oj f)*δ (y3 f P Q) := by
 rw [hδ,← yB,bhb,t5]
set_option linter.overlappingInstances false in
private theorem bXl {R k :Type*} [ov R] [ov k] [wB k R] [Module k R]
   (δ:pL k R R) (s v :R) (a :ℕ) :
   s*(s*δ (s^a*v))-(a :R)*(s*δ s)*(s^a*v) =
     s^(a+2)*δ v := by
 cases a with
 | zero=>simp [pow_two,mul_assoc]
 | succ a =>
   rw [δ.leibniz,δ.leibniz_pow,Nat.succ_sub_one,pow_add s (a+1) 2,pow_succ' s a]
   simp only [Dz ,Mw]
   ring
private theorem cFn {f :af 4} {P:aU c9}
   {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ)
   (n:ℕ) :
   y3 f P (su f n) =
     y3 f P (oj f)^(2*n)*(δ^[n]) (y3 f P (nI 0)) := by
 induction n with
 | zero=>simp [su]
 | succ n ih =>
   simp only [su,aqZ,Dv,oK,RJ,edh hδ]
   rw [ih,show 2*(n+1)=2*n+2 by omega,G7]
   exact bXl (k :=ao) (R:=ChartRing f P) δ _ _ (2*n)
theorem cFi (f :af 4) (P:aU c9) {n:ℕ}
  (hn:n<K1.p) :uh (↑n.factorial:ChartRing f P) := by
 rw [← RJ (Jb f P)]
 exact (lB.ahA hn).isUnit.map (Jb f P)
private theorem dIE {f :af 4} {P:aU c9}
   {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ)
   {n:ℕ} (hn:n<4) :
   (δ^[n]) (y3 f P (nI 0)) =
     (↑n.factorial:ChartRing f P)*y3 f P (nI ⟨n,hn⟩) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   have hn' : n<3:= by omega
   rw [G7,ih (by omega),δ.leibniz,δ.map_natCast]
   simp only [Dz ,u5 ,v8]
   rw [show (⟨n,by omega⟩:Fin 4)=(⟨n,hn'⟩:Fin 3).castSucc by rfl,
     dIR hδ,WY ,Kp ]
   rw [show (⟨n,hn'⟩:Fin 3).succ=(⟨n+1,hn⟩:Fin 4) by exact Fin.ext rfl]
   change _ *((↑(n+1) :ChartRing f P)*_)=(↑(n+1) :ChartRing f P)*_ *_
   ring
private theorem dID {f :af 4} {P:aU c9}
    {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ)
    (i:Fin bf) :
    (δ^[i.val]) (y3 f P (nI 0)) =
      (↑i.val.factorial:ChartRing f P)*U5 f P i:= by
  rw [U5]
  split_ifs with hi
  · exact dIE hδ hi
  · rw [cFn hδ]
    have hmul :QU f P*y3 f P (oj f)=1 := by
      rw [qG,bhb]
    have hc: (↑i.val.factorial:ChartRing f P) *
        Jb f P (↑i.val.factorial:ao)⁻¹=1 := by
      rw [← RJ (Jb f P),← oK,
        mul_inv_cancel₀ (lB.ahA
          (i.isLt.trans (by decide :bf<K1.p))),C4]
    have hpow:QU f P^(2*i.val)*y3 f P (oj f)^(2*i.val)=1 := by
      rw [← mul_pow,hmul,one_pow]
    symm
    calc
      _=((↑i.val.factorial:ChartRing f P)*Jb f P (↑i.val.factorial:ao)⁻¹) *
          (QU f P^(2*i.val)*y3 f P (oj f)^(2*i.val)) *
          (δ^[i.val]) (y3 f P (nI 0)) := by ring
      _ = _:= by rw [hc,hpow,Dw ,t5]
private theorem dMq {R:Type*} [ov R] {M:ℕ} (a :Fin M→R) (i:Fin M) :
   (∑ j:Fin M,Df j.val (a j)).coeff i.val=a i:= by
 classical
 rw [Np,IU i]
 · exact coeff_monomial_same _ _
 · intro j _ hj
   exact Un _ (fun h=>hj (Fin.ext h.symm))
 · simp
private theorem b1Z {R:Type*} [ov R] {M:ℕ}
  {U:R[X]} {x :R} {a :Fin M→R}
  (h:zS x U = ∑ i:Fin M,Df i.val (a i)) (i:Fin M) :
  (oz i.val U).eval x=a i:= by
 rw [← taylor_coeff,h,dMq]
private theorem d2p {f :af 4} {P:aU c9} (i:Fin bf) :
  (oz i.val (RH f P)).eval (CW f P)=U5 f P i:= by
 refine b1Z ?_ i
 rw [RH,taylor_taylor,add_neg_cancel,taylor_zero]
theorem dIc (f :af 4) (P:aU c9) :
  (RH f P).natDegree<bf := by
 simpa only [zei] using ezp
  (GR (ChartRing f P))
private theorem gA7 {f :af 4} {P:aU c9}
  {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ)
  (hmem:bC (vU f)∈P) :
  (δ^[bf]) (y3 f P (nI 0))=0:= by
 have h:=cac (f :=f) hmem
 rw [vU,cFn hδ,← u5 (y3 f P (oj f)^(2*bf))]
  at h
 exact ((IsUnit.of_mul_eq_one _ (bhb f P)).pow _).mul_left_cancel h
theorem dIg {f :af 4} {P:aU c9}
    {δ:pL ao (ChartRing f P) (ChartRing f P)} (hδ:asX f P δ)
    (hmem:bC (vU f)∈P) (n:ℕ) :
    δ ((oz n (RH f P)).eval (CW f P)) =
      (↑(n+1) :ChartRing f P) *
        (oz (n+1) (RH f P)).eval (CW f P) := by
  let U:=RH f P
  let x :=CW f P
  let y :=y3 f P (nI 0)
  have hdeg:U.natDegree<bf :=dIc f P
  change δ ((oz n U).eval x)=(↑(n+1) :ChartRing f P)*(oz (n+1) U).eval x
  by_cases hn:n<bf
  · have hit (i:ℕ) (hi:i≤bf) :
        (δ^[i]) y=(↑i.factorial:ChartRing f P)*(oz i U).eval x := by
      rcases lt_or_eq_of_le hi with hi | rfl
      · rw [d2p (⟨i,hi⟩:Fin bf)]
        exact dID hδ ⟨i,hi⟩
      · rw [zrQ U _ hdeg,eval_zero,u5]
        exact gA7 hδ hmem
    have h:=hit (n+1) (by omega)
    rw [G7,hit n hn.le,δ.leibniz,δ.map_natCast,
      WY ,Kp] at h
    simp only [Dz ,u5 ,v8 ,yB] at h
    rw [NY (↑(n+1) :ChartRing f P)] at h
    exact (cFi f P (hn.trans (by decide :bf<K1.p))).mul_left_cancel h
  · rw [hasseDeriv_eq_zero_of_lt_natDegree U n (by omega),
      zrQ U (n+1) (by omega),eval_zero,pQ ,u5 ]
end
end bzK
end
section
namespace ap9
noncomputable section
open aR dN rW Rl MvPolynomial
structure XP (f :af 4) (T:Li f) (A:kT) :Prop where
 extended_prime : (gN A).IsPrime
 dimension_eq :oq (lA A)=oq A
 factor :bC f∈lA A
 regular :bC (oj f)∉lA A
 test :bC T.test∈lA A
 denom:bC T.denom∉lA A
 ar5 : ∀ i,nI i*mS (bC T.denom) -
  mS (bC (T.Fr i))∈gN A
def aFs (f :af 4) :nX n8 :=
 (cy {bC f}).minimalPrimesFinset
def Ji (f E :af 4) :nX n8:= by
  classical
  exact ((aFs f).filter (fun component=>bC E∉component)).biUnion
    (fun component=>(AX component E).minimalPrimesFinset)
end
end ap9
end
section
namespace ap9
noncomputable section
open Polynomial K1 aR dN rW wH Rl MvPolynomial
open scoped BigOperators
private theorem beg (g:af 4) : (bC g).totalDegree≤g.totalDegree := by
 rw [bC,zgn,zgn]
 exact Finset.sup_mono (Zf _ _)
private theorem bhF {α β:Type} [xL β] (A:nX α) (B:α→nX β)
   (w:β→ℚ) (hw : ∀ x,0≤w x) :
   (∑ x∈A.biUnion B,w x) ≤ ∑ i∈A,∑ x∈B i,w x := by
 classical
 induction A using zcw with
 | empty=>simp
 | @insert i A hi ih =>
   rw [Finset.biUnion_insert,Finset.sum_insert hi]
   have hu:=Finset.sum_union_inter (f :=w) (s₁:=B i) (s₂:=A.biUnion B)
   have hn:0 ≤ ∑ x∈B i∩A.biUnion B,w x :=zlo fun x _=>hw x
   linarith
end
end ap9
end
section
namespace aRU
noncomputable section
open aR rW NS MvPolynomial
structure UF where
 offset :ao
 slope :Fin bf→ao
def UF.form (H :UF) :rW.jo :=
 p7 H.offset + ∑ i,p7 (H.slope i)*nI i
def UF.aoc (H :UF) :mK :=
 z9 ni H.form
def cut {R:Type*} [ov R] (I:aU R) (p:R) :aU R :=
 I ⊔ cy {p}
def saturate {R:Type*} [ov R] (I:aU R) (d:R) :aU R :=
 let ι:=lJ R (zUF d)
 (I.map ι).comap ι
def cGz (A:kT) (H :UF) :kT :=
 cut A H.form
def cGr (A:kT) (H G:UF) :kT :=
 cut (cGz A H) G.form
def fXp (A:kT) (d:mK) (H :UF) :
    Ideal mK :=
  saturate (gN (cGz A H)) d
def c8I (A:kT) (d:mK) (H G:UF) :
    Ideal mK :=
  saturate (gN (cGr A H G)) d
structure gOO (A:kT) (d:mK) where
 first:UF
 second:UF
 first_proper :first.aoc∉gN A
 second_regular :vk (mD (fXp A d first) second.aoc)
 cIP:oq (c8I A d first second)=1
 cIO:qx (c8I A d first second)=qx A
 boundary_finite : ∀ i,oq (KL (cGr A first second) i)=0
end
end aRU
end
section
namespace ap9
noncomputable section
open Polynomial K1 aR dN rW Rl MvPolynomial
open scoped BigOperators
theorem bsp {Γ:nX K} {s :K→K[X]}
   (hs :Kc s (Γ:Set K)) (hd : ∀ γ∈Γ,(s γ).natDegree≤133671) :
   Kc (rV s) (Γ:Set K) := by
 intro α hα β hβ he
 apply hs hα hβ
 apply Polynomial.ext
 intro n
 by_cases hn:n<bf
 · have hc:=Ml he ⟨n,hn⟩
   exact embed.injective (by simpa only [rV,Gp,Ee] using hc)
 · have hlt:133671<n:= by
     change ¬ n<133672 at hn
     omega
   rw [zE ((hd α hα).trans_lt hlt),
     zE ((hd β hβ).trans_lt hlt)]
theorem ctj {Γ:nX K} {s :K→K[X]} {A:kT}
   (hp:A.IsPrime) (hdim:oq A=3)
   (hd : ∀ γ∈Γ,(s γ).natDegree<bf)
   (hinj:Kc (rV s) (Γ:Set K))
   (hpoint : ∀ γ∈Γ,rV s γ∈xW ao A) :
   bbz Γ s (aaL A) := by
 classical
 let _:=hp
 intro x a hmiss H
 let J:=A ⊔ cy {VA x a}
 let S:=J.minimalPrimesFinset.filter (fun B=>(JI H s B).Nonempty)
 have hproper :VA x a∉A:= by
   obtain ⟨γ,hγ,h⟩:=hmiss
   exact fun hm=>h ((aFp (hd γ hγ)).mp (hpoint γ hγ _ hm))
 have hsub (B:kT) (_:B∈S) :JI H s B⊆H := fun _ h=>(P6.mp h).1
 have hprime (B:kT) (hB:B∈S) :J.IsMinimalPrime B :=
   Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hB).1
 refine ⟨aa9 S (JI H s) hsub,?_,?_,?_,?_⟩
 · intro γ hγ
   obtain ⟨hΓ,hvalue⟩:=Finset.mem_filter.mp hγ
   have hz :rV s γ∈xW ao J :=
     mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoint γ hΓ,(aFp (hd γ hΓ)).mpr hvalue⟩
   obtain ⟨B,hB,hxB⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus J
     (1 :rW.jo) _ hz (by simp)
   have hmarks :=P6.mpr ⟨hγ,hxB⟩
   exact a5M.mpr ⟨B,Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr
     (Ideal.mem_retainedMinimalPrimes.mp hB).1,⟨γ,hmarks⟩⟩,hmarks⟩
 · intro i
   let B:=S.equivFin.symm i
   have hm:=hprime B B.property
   have hdimB:=C9 hproper hm
   change oq (B:kT)+1=oq A at hdimB
   have hdimB' : oq (B:kT)=2 := by omega
   apply bxh hm.isPrime hdimB'
   · exact fun γ hγ=>hd γ (Finset.mem_filter.mp (P6.mp hγ).1).1
   · exact hinj.mono (fun γ hγ=>(Finset.mem_filter.mp (P6.mp hγ).1).1)
   · exact fun _ hγ=>(P6.mp hγ).2
 · intro i
   let B:=S.equivFin.symm i
   exact aT4 (hprime B B.property).isPrime (Finset.mem_filter.mp B.property).2
 · apply Nat.le_floor
   have hsum:=principalCut_sum_affineDegree_minimalPrimes_le hproper (aQ5 x a)
   exact a6x.trans ((Finset.sum_le_sum_of_subset_of_nonneg
     (Finset.filter_subset _ _) (fun B _ _=>affineDegree_nonneg B)).trans
     (by simpa only [Yc,t5] using hsum))
end
end ap9
end
section
namespace aRU
noncomputable section
open aR dN rW wH Rl ap9 MvPolynomial
theorem brD {R:Type*} [ov R] (I:aU R) (p:R) :I≤ cut I p :=
 p6
theorem cZ2 {R:Type*} [ov R] (I:aU R) (p:R) :p∈cut I p :=
 u9 (th p)
theorem c7S {I J:n8} {p:c9} {b:ℕ}
    (hIJ:cut I p≤J) (hreg:vk (mD I p))
    (hb:p.totalDegree≤b) :
    oq J≤oq I - 1 ∧
      (oq J+1=oq I→qx J≤(b:ℚ)*qx I) := by
  have h:=zWJ hreg hb
  change oq (cut I p)≤oq I - 1∧_ at h
  have hmon :=t9 hIJ
  change oq J≤oq (cut I p) at hmon
  have hdim:=hmon.trans h.1
  refine ⟨hdim,fun hd ↦ ?_⟩
  have hsame :oq J=oq (cut I p) := by omega
  have hsucc:oq I=oq (cut I p)+1 := by omega
  have hsub:oq I - 1=oq (cut I p) := by omega
  have hc:=h.2
  change (lV (cut I p)).coeff (oq I - 1)≤_ at hc
  rw [hsub] at hc
  calc
    qx J≤qx (cut I p) :=affineDegree_le_of_le hIJ hsame
    _≤(oq (cut I p)).factorial *
        ((b:ℚ)*oq I*(lV I).leadingCoeff) :=
      SW hc (by positivity)
    _=(b:ℚ)*qx I:= by
      change _=(b:ℚ)*((oq I).factorial*(lV I).leadingCoeff)
      rw [hsucc,WY ,Kp]
      ring
end
end aRU
end
section
namespace ap9
noncomputable section
open Polynomial K1 aR dN rW wH Rl
open scoped BigOperators
open MvPolynomial
private theorem cMx {P Q:n8} (hp:P.IsPrime) (hle :P≤Q)
  (hdP:oq P=2) (hdQ:2≤oq Q) :P= Q:= by
 by_contra hne
 have hn : ∃ x,x∈Q∧x∉P:= by
  by_contra! hall
  exact hne (sS hle hall)
 obtain ⟨x,hxQ,hxP⟩:=hn
 have hJ:P ⊔ cy {x} ≤ Q:=zc hle (Ideal.span_le.mpr (by simpa using hxQ))
 have hcut:=(KI
  hp hxP (le_refl x.totalDegree)).1
 have hmon :=t9 hJ
 change oq (P ⊔ cy {x})≤oq P - 1 at hcut
 change oq Q≤oq (P ⊔ cy {x}) at hmon
 omega
end
end ap9
end
section
namespace ata
open MvPolynomial
def bze {k σ:Type*} [uJ k]
    (B:aU (lz σ k)) (ℓ:lz σ k) :Prop :=
  ∃ N :ℕ,∀ n≥N,∀ q:lz σ k,q.IsHomogeneous n→ℓ*q∈B→q∈B
end ata
end
section
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
namespace ata
noncomputable section
open aR dN rW NS aRU MvPolynomial
section Parameters
variable {k E σ:Type*} [uJ k] [uJ E] [wB k E] [sI σ]
private def Qe : (k×(σ→k)) →ₗ[k] lz σ E :=
 ∑ i:σ,((LinearMap.proj i).comp (LinearMap.snd k k (σ→k))).smulRight
   (nI i)
private def aU0: (k×(σ→k)) →ₗ[k] lz σ E :=
 (LinearMap.fst k k (σ→k)).smulRight 1+Qe
private theorem bwC (v :k×(σ→k)) :
  Qe (E :=E) v = ∑ i:σ,C (lJ k E (v.2 i))*nI i:= by
 simp only [Qe,LinearMap.sum_apply,Xp,
  LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.snd_apply,NX ,
  MO k E (lz σ E),HZ,SC]
private theorem b3M (v :k×(σ→k)) :
  aU0 (E :=E) v=C (lJ k E v.1)+Qe (E :=E) v := by
 simp only [aU0,LinearMap.add_apply,Xp,LinearMap.fst_apply,
  NX ,MO k E (lz σ E),
  HZ,SC,Dw]
private theorem cNF [Infinite k] (I J B:aU (lz σ E)) :
    ∃ v :k×(σ→k),
      (∀ P∈Ar (lz σ E) (lz σ E ⧸ I),aU0 v∉P) ∧
      (∀ P∈Ar (lz σ E) (lz σ E ⧸ J),aU0 v∉P) ∧
      (∀ P∈Ar (lz σ E) (lz σ E ⧸ B),
        (∃ i:σ,nI i∉P)→Qe v∉P) := by
  classical
  let S:=Ar (lz σ E) (lz σ E ⧸ I) ∪
    Ar (lz σ E) (lz σ E ⧸ J)
  let T := {P∈Ar (lz σ E) (lz σ E ⧸ B) |
    ∃ i:σ,nI i∉P}
  have hS:S.Finite :=(Wm _ _).union (Wm _ _)
  have hT:T.Finite :=(Wm _ _).subset fun _ hp ↦ hp.1
  let:qU S:=hS.to_subtype
  let:qU T:=hT.to_subtype
  let bad:S ⊕ T→JW k (k×(σ→k)) :=
    Sum.elim
      (fun P ↦ (P.val.restrictScalars k).comap aU0)
      (fun P ↦ (P.val.restrictScalars k).comap Qe)
  have hbad : ∀ t,bad t ≠ ⊤ := by
    intro t htop
    cases t with
    | inl P =>
      have hprime :P.val.IsPrime :=P.property.elim (·.isPrime) (·.isPrime)
      have hmem: ((1 :k),(0:σ→k))∈bad (.inl P) :=htop ▸ Qx
      change aU0 (1,0)∈P.val at hmem
      rw [b3M,bwC] at hmem
      apply hprime.ne_top
      apply P.val.eq_top_of_isUnit_mem _ isUnit_one
      simpa only [C4 ,Pi.zero_apply,pQ,zi ,Finset.sum_const_zero,v8] using hmem
    | inr P =>
      obtain ⟨i,hi⟩:=P.property.2
      let v :σ→k := fun j ↦ if j=i then 1 else 0
      have hmem: ((0:k),v)∈bad (.inr P) :=htop ▸ Qx
      change Qe (0,v)∈P.val at hmem
      rw [bwC] at hmem
      have hv : (∑ j:σ,C (lJ k E (v j))*nI j)=nI i:= by
        rw [IU i]
        · simp [v]
        · intro j _ hji
          simp [v,hji]
        · simp
      exact hi (hv ▸ hmem)
  obtain ⟨v,hv⟩:=zsi bad hbad
  exact ⟨v,fun P hP ↦ hv (.inl ⟨P,Or.inl hP⟩),fun P hP ↦ hv (.inl ⟨P,Or.inr hP⟩),
    fun P hP hi ↦ hv (.inr ⟨P,hP,hi⟩)⟩
end Parameters
private theorem br3 {F σ:Type*} [uJ F] [sI σ] (a :σ→F) :
   (∑ i:σ,C (a i)*nI i).IsHomogeneous 1 :=
 (NI σ F 1).sum_mem fun i _ ↦ isHomogeneous_C_mul_X (a i) i
theorem ceZ {R:Type*} [ov R] [LO R]
  (I:aU R) (f :R) (h : ∀ P∈Ar R (R ⧸ I),f∉P) :
  vk (mD I f) := by
 apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
 intro x hx
 by_contra hn
 have hz :f ∈ {r :R | ∃ z :R ⧸ I,z≠0∧r•z=0} := ⟨x,hn,hx⟩
 rw [← biUnion_associatedPrimes_eq_zero_divisors] at hz
 obtain ⟨P,hP,hf⟩:=Set.mem_iUnion₂.mp hz
 exact h P hP hf
private theorem bDK {R:Type*} [ov R] (I:aU R) (f p:R) :
   p∈cut I f ↔ ∃ q,p - f*q∈I:= by
 rw [cut,Av,Gk]
 constructor
 · rintro ⟨q,a,ha,rfl⟩
   refine ⟨q,?_⟩
   simpa [qG q f] using ha
 · rintro ⟨q,hq⟩
   exact ⟨q,p - f*q,hq,by rw [qG q f,add_sub_cancel]⟩
theorem cKo {R:Type*} [ov R] (I:aU R) (d f :R)
  (hd:vk (mD I d))
  (hf :vk (mD (cut I d) f)) :
  vk (mD (cut I f) d) := by
 apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
 intro x hx
 obtain ⟨p,rfl⟩:=zf x
 rw [← oK,t3 ,bDK] at hx
 obtain ⟨q,hq⟩:=hx
 have hq' : f*q∈cut I d:= by
  rw [bDK]
  exact ⟨p,by simpa only [neg_sub] using I.neg_mem hq⟩
 have hz :mD (cut I d) q=0:= by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mp hf
  rw [← oK,t3]
  exact hq'
 rw [t3 ,bDK] at hz
 obtain ⟨r,hr⟩:=hz
 have hmul :d*(p - f*r)∈I:= by
  convert I.add_mem hq (I.mul_mem_left f hr) using 1
  ring
 have hzero :mD I (p - f*r)=0:= by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mp hd
  rwa [← oK,t3]
 rw [t3 ,bDK]
 exact ⟨r,Ideal.Quotient.eq_zero_iff_mem.mp hzero⟩
end
end ata
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace bzK
noncomputable section
open Polynomial aR dN rW as9
section PolynomialFlow
variable {R:Type*} [ov R]
private def beF (d:R →+ R) (h₁:d 1=0)
  (hmul : ∀ a b,d (a*b)=a*d b+b*d a) :pL ℤ R R where
 toLinearMap:=d.toIntLinearMap
 map_one_eq_zero' := h₁
 leibniz' := hmul
private def Lv (δ:pL ℤ R R) :pL ℤ R[X] R[X] :=
 PolynomialModule.equivPolynomialSelf.compDer δ.mapCoeffs
@[simp] private theorem aTK (δ:pL ℤ R R) (U:R[X]) (n:ℕ) :
   (Lv δ U).coeff n=δ (U.coeff n) :=rfl
private theorem bXw (δ:pL ℤ R R) (U:R[X]) (n:ℕ) :
  Lv δ (oz n U)=oz n (Lv δ U) := by
 ext j
 simp [hasseDeriv_coeff,δ.leibniz,Dz]
private theorem cKs (δ:pL ℤ R R) (x :R) (U:R[X]) :
  δ (U.eval x)=(Lv δ U).eval x+(wY U).eval x*δ x := by
 have h:=PolynomialModule.aeval_equivPolynomial (δ.mapCoeffs U) x
 have he : (Lv δ U).eval x=PolynomialModule.eval x (δ.mapCoeffs U) := by
  simpa [Lv,aeval_def] using h
 rw [δ.apply_eval_eq,he,Dz]
private theorem aNh (U:R[X]) (n:ℕ) :
  wY (oz n U)=C (↑(n+1) :R)*oz (n+1) U:= by
 have h:=LinearMap.congr_fun (hasseDeriv_comp (R:=R) 1 n) U
 simpa [hasseDeriv_one',Nat.choose_one_right,Mw ,C_eq_natCast,
  Nat.add_comm,N0] using h
private theorem dWn (δ:pL ℤ R R) (x :R) (hx :δ x=1)
    (U:R[X]) (n:ℕ) :
    δ ((oz n U).eval x) =
      (oz n (Lv δ U)).eval x +
        (↑(n+1) :R)*(oz (n+1) U).eval x := by
  rw [cKs,bXw,hx,Dw ,aNh,eval_mul,eval_C]
private theorem cFX (δ:pL ℤ R R) (x :R) (hx :δ x=1) (U:R[X])
   (h : ∀ n,δ ((oz n U).eval x) =
     (↑(n+1) :R)*(oz (n+1) U).eval x) :Lv δ U=0:= by
 apply zHO _ x
 intro n
 have he :=dWn δ x hx U n
 rw [h] at he
 exact add_right_cancel (he.symm.trans (zero_add _).symm)
private theorem dL6 (δ:pL ℤ R R) {V:R[X]}
   (hV:Lv δ V=0) (n:ℕ) :Lv δ ((wY^[n]) V)=0:= by
 induction n with
 | zero=>exact hV
 | succ n ih =>
   rw [G7,← hasseDeriv_one',bXw,ih,pQ]
private theorem dmq (δ:pL ℤ R R) (x :R) (hx :δ x=1)
   (V:R[X]) (hV:Lv δ V=0) (he :V.eval x=0)
   (hunit : ∀ n≤V.natDegree,uh (↑n.factorial:R)) :V=0:= by
 have hderiv (n:ℕ) : ((wY^[n]) V).eval x=0:= by
   induction n with
   | zero=>exact he
   | succ n ih =>
     have h:=cKs δ x ((wY^[n]) V)
     rw [ih,pQ,dL6 δ hV n,eval_zero,zero_add,hx,Dw] at h
     rw [G7]
     exact h.symm
 apply zHO _ x
 intro n
 by_cases hn:n≤V.natDegree
 · have hh:n.factorial•oz n V=(wY^[n]) V :=
     Ml (factorial_smul_hasseDeriv (R:=R) n) V
   have h:=qy (yl x) hh
   rw [map_nsmul] at h
   change n.factorial•(oz n V).eval x=((wY^[n]) V).eval x at h
   rw [Mw ,hderiv] at h
   exact (hunit n hn).mul_left_cancel (h.trans (u5 _).symm)
 · rw [zrQ V _ (Nat.lt_of_not_ge hn),eval_zero]
end PolynomialFlow
private def bgS {R:Type*} [ov R]
  (k :ao →+* R) (Q:af 4) (U:R[X]) :R[X] :=
 Bf (vG k) (fun i=>oz i.val U) Q
private theorem c84 {R:Type*} [ov R]
   (δ:pL ℤ R R) (k :ao →+* R) (hc : ∀ a,δ (k a)=0)
   (Q:af 4) (U:R[X]) (hU:Lv δ U=0) :
   Lv δ (bgS k Q U)=0:= by
 let e :=Au (vG k)
   (fun i:Fin 4=>oz i.val U)
 change Lv δ (e Q)=0
 induction Q using Yo with
 | C c =>
   ext n
   rw [S2 ,aTK,coe_mapRingHom,Ee,coeff_zero]
   exact hc (c.coeff n)
 | add a b ha hb=>simp [map_add,ha,hb]
 | mul_X a i ha =>
   rw [oK,Ww ,(Lv δ).leibniz,bXw,ha,hU]
   simp
private theorem cMO (f :af 4) (P:aU c9) (Q:af 4) :
    (bgS (Jb f P) Q (RH f P)).eval (CW f P) =
      y3 f P Q:= by
  let e :=(yl (CW f P)).comp (vG (Jb f P))
  have he :e=(y3 f P).comp MvPolynomial.C:= by
    apply Qw
    · intro c
      simp [e,Jb]
    · simp [e,CW]
  change (yl (CW f P)) (Bf (vG (Jb f P))
    (fun i:Fin 4=>oz i.val (RH f P)) Q)= _
  rw [Te,show (yl (CW f P)).comp
    (vG (Jb f P))=e from rfl]
  have h:Au e (fun i:Fin 4 =>
      (yl (CW f P)) (oz i.val (RH f P)))=y3 f P:= by
    apply FV
    · intro c
      simpa only [S2 ,HZ] using yU he c
    · intro i
      simpa only [Ww ,coe_evalRingHom,RingHom.id_apply,zei] using
        bpA (GR (ChartRing f P)) i
  exact yU h Q
end
end bzK
end
section
set_option maxHeartbeats 500000
namespace ata
noncomputable section
open rW NS MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type*} [uJ k]
theorem bBP (I:aU (lz σ k)) :
  (lW I).IsHomogeneous (NI σ k) := by
 apply Ideal.homogeneous_span
 rintro _ ⟨p,n,_,_,rfl⟩
 exact ⟨n,homogeneousComponent_mem n p⟩
private theorem dzS (I:aU (lz σ k)) :
   lW I=MJ.lW I:= by
 apply sS
 · apply Ideal.span_le.mpr
   rintro _ ⟨p,n,hp,hn,rfl⟩
   exact aY6.bcK hp hn
 · apply Ideal.span_le.mpr
   rintro _ ⟨p,hp,rfl⟩
   exact Re ⟨p,p.totalDegree,hp,vh,rfl⟩
private theorem ayA (p:lz σ k) (n:ℕ) :
  (DirectSum.decompose (NI σ k) p n:lz σ k) =
    homogeneousComponent n p :=
 decomposition.decompose'_apply p n
theorem bYu {ℓ p:lz σ k}
  (hℓ:ℓ.IsHomogeneous 1) (n:ℕ) :
  Kh (n+1) (ℓ*p)=ℓ*Kh n p:= by
 simpa only [ayA,Nat.succ_sub_one] using
  (DirectSum.coe_decompose_mul_of_left_mem_of_le
    (𝒜:=homogeneousSubmodule σ k) (b:=p) hℓ (Nat.succ_le_succ (Nat.zero_le n)))
private theorem dIy (B:aU (lz σ k))
    (hB:B.IsHomogeneous (NI σ k)) (i:σ) :
    vk (mD B (nI i - 1)) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro z hz
  obtain ⟨p,rfl⟩:=zf z
  rw [← oK,t3] at hz
  rw [t3]
  have hX:IsHomogeneous (nI i:lz σ k) 1 :=isHomogeneous_X k i
  have hprod (n:ℕ) :
      Kh n ((nI i - 1)*p)∈B:= by
    simpa only [ayA] using (hB.mem_iff.mp hz n)
  have h0:Kh 0 (nI i*p)=0:= by
    simpa only [ayA] using
      (DirectSum.coe_decompose_mul_of_left_mem_of_not_le
        (𝒜:=homogeneousSubmodule σ k) (b:=p) hX (Nat.not_succ_le_zero 0))
  suffices hc : ∀ n,Kh n p∈B by
    exact hB.mem_iff.mpr (fun n ↦ by simpa only [ayA] using hc n)
  intro n
  induction n with
  | zero =>
    have h:=hprod 0
    rw [sub_mul,t5 ,Dv,h0,zero_sub] at h
    exact (B.neg_mem_iff).mp h
  | succ n ih =>
    have h:=hprod (n+1)
    rw [sub_mul,t5 ,Dv,bYu hX] at h
    exact (B.sub_mem_iff_right (B.mul_mem_left _ ih)).mp h
theorem cDn [qU σ] (I:aU (lz σ k))
  (hI:oq I=1) (i:σ) :
  oq (KL I i)=0:= by
 have hB:oq (lW I)≤1 := by
  rw [dzS,← hI]
  exact aY6.cDp I
 have hd: (nI i - 1 :lz σ k).totalDegree≤1 := by
  simpa only [totalDegree_X,totalDegree_one,Nat.max_zero] using
    (totalDegree_sub (nI i:lz σ k) 1)
 have h:=(zWJ
  (dIy (lW I) (bBP I) i) hd).1
 change oq (KL I i)≤oq (lW I) - 1 at h
 omega
end
end ata
end
section
namespace bau
noncomputable section
open aR dN Dr lB aiK Kd ap8 MvPolynomial
open scoped BigOperators Pointwise
theorem gLU {p q:lI} (hp:bF p) (hq:bF q) :
    oD p+capExponents q=oD (p.plus q) := by
  ext e
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    simp only [OW,y5 ,Finsupp.add_apply] at *
    omega
  · intro he
    obtain ⟨hpb,hpj⟩:=hp
    obtain ⟨hqb,hqj⟩:=hq
    rw [OW] at he
    simp only [y5] at he
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
theorem aCx (p:lI) (hp:pG p) :
  t7 (vw ox (oD p)) := by
 apply Gj
 intro i
 have ⟨hb,hj,ht⟩:=hp
 fin_cases i <;> norm_num [OW,OJ] <;> omega
theorem dEX (J:aU c9) (p:lI) (hp:pG p) (n:ℕ) :
    sH
        (J.comap (vw ox (oD p)).toRingHom) n =
      Sn J (oD (p.scale n)) := by
  rw [bzA.proof J p n,bzz.proof
    (fun _:Unit=>p) (fun _=>hp) (fun _=>n)]
  simp [ku,Shape.scale]
theorem awr {ι:Type} [sI ι] (s :ι→lI)
  (hs : ∀ i,bF (s i)) (a :ι→ℕ) :bF (ku s a) := by
 refine ⟨FK (fun i _=>vi _ (hs i).1),?_⟩
 change 3*(∑ i,a i*(s i).t) ≤ ∑ i,a i*(s i).j
 rw [zg]
 exact FK fun i _=> by
  rw [Nat.mul_left_comm 3]
  exact vi _ (hs i).2
private theorem auw:oD ⟨0,0,0⟩=(0:Set (Fin 4 →₀ ℕ)) := by
 simpa only [Shape.scale,zi ,zero_smul] using
  (aIH ⟨3, 3,1⟩ ⟨by decide,by decide,by decide⟩ 0).symm
private theorem guP {ι:Type} [sI ι] [xL ι] (i:ι) :
  ∑ j,step i j=1 := by
 simp [step,LQ]
private theorem d4S {ι:Type} [sI ι] [xL ι]
   (s :ι→lI) (e :Kb s →₀ ℕ) (i:ι)
   (hi:0<Pj (step ∘ Fd s) e i) :
   ∃ v :Kb s,v.1=i∧e v≠0:= by
 classical
 let _:sI (Kb s) :=FQ _
 rw [ Xu,Finset.sum_apply] at hi
 obtain ⟨v,-,hv⟩:=Finset.exists_ne_zero_of_sum_ne_zero hi.ne'
 change e v*Pi.single (M:= fun _:ι=>ℕ) v.1 1 i≠0 at hv
 simp only [LQ,mul_ite,Dw ,u5] at hv
 by_cases h:v.1=i
 · exact ⟨v,h,by simpa [h,eq_comm] using hv⟩
 · have hn:i≠v.1 :=Ne.symm h
   simp [hn] at hv
private theorem eOS {ι:Type} [sI ι] [xL ι]
   (s :ι→lI) (a :ι→ℕ) (i:ι) :
   Yz s (a+step i)=Yz s a+capExponents (s i) := by
 classical
 ext m
 constructor
 · rintro ⟨e,he,rfl⟩
   have hi:0<Pj (step ∘ Fd s) e i:= by
     rw [he]
     simp [step,SL]
   obtain ⟨v,hv,hv0⟩:=d4S s e i hi
   have hw₁:=zpI (w:=step ∘ Fd s) hv0
   have hw₂:=zpI (w:= fun v :Kb s=>v.2.val) hv0
   have hw:Pj (step ∘ Fd s) (e-Finsupp.single v 1)=a := by
     change _+step v.1= _ at hw₁
     rw [he,hv] at hw₁
     exact add_right_cancel hw₁
   refine ⟨_,⟨_,hw,rfl⟩,v.2.val,?_,hw₂⟩
   exact hv ▸ v.2.property
 · rintro ⟨m,⟨e,he,rfl⟩,x,hx,rfl⟩
   let v :Kb s :=⟨i,⟨x,hx⟩⟩
   refine ⟨e+Finsupp.single v 1,?_,?_⟩
   · rw [t8 ,zTy,he,one_smul]
     rfl
   · rw [t8 ,zTy,one_smul]
private theorem product_zero {ι:Type} [sI ι] [xL ι] (s :ι→lI) :
    Yz s 0=(0:Set (Fin 4 →₀ ℕ)) := by
  classical
  ext m
  constructor
  · rintro ⟨e,he,rfl⟩
    have he0:e=0:= by
      by_contra hn
      obtain ⟨v,hv⟩:=Finsupp.support_nonempty_iff.mpr hn
      have hv' := Finsupp.mem_support_iff.mp hv
      let _:sI (Kb s) :=FQ _
      have hle :e v≤Pj (step ∘ Fd s) e v.1 := by
        rw [ Xu,Finset.sum_apply]
        have key :=zfK
          (f := fun u:Kb s=>(e u•(step ∘ Fd s) u) v.1)
          (fun _ _=>Nat.zero_le _) (FR v)
        simpa [step,Fd] using key
      rw [he] at hle
      exact hv' (za7 hle)
    simp [he0]
  · intro h
    have hm:=Set.mem_zero.mp h
    subst m
    exact ⟨0,pQ _,pQ _⟩
theorem eOX {ι:Type} [sI ι] [xL ι] (s :ι→lI)
    (hs : ∀ i,bF (s i)) (a :ι→ℕ) :
    Yz s a=oD (ku s a) := by
  classical
  generalize hn : ∑ i,a i=n
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases ha :a=0
    · subst a
      rw [product_zero,show ku s 0=⟨0,0,0⟩ by simp [ku],auw]
    · obtain ⟨i,hi⟩:=Function.ne_iff.mp ha
      let b:ι→ℕ:= fun j=>a j - step i j
      have hb:a=b+step i:= by
        funext j
        by_cases hji:j=i
        · subst j
          simp only [b,SL,step,Pi.single_eq_same]
          have :a i≠0:=hi
          omega
        · simp [b,step,LQ,hji]
      have hsum: (∑ j,b j)+1=n:= by
        rw [hb,Pi.add_def,wR,guP] at hn
        exact hn
      have hprev :=ih _ (by omega) b rfl
      rw [hb,eOS,hprev,aES,aQe,
        gLU (awr s hs b) (hs i)]
end
end bau
end
section
namespace bzI
noncomputable section
open aR dN Dr lB MvPolynomial
open scoped BigOperators
def c1 :Prop :=
  ∀ (J Q:aU c9) (a :c9),a∉J→Q.IsPrime →
    (∀ x :c9,x*a∈J↔x∈Q) →
    ∀ (d:ℕ),oY J≤d→d≤2 →
    ∀ p:lI,pG p →
      oZ J d p≤ oZ (J ⊔ cy {a}) d p+capCoeff Q d p
def c2 :Prop :=
  ∀ (P:aU c9),P.IsPrime→ oY P=2 →
    ∀ p q:lI,bF p→bF q→0≤tW P [p,q]
private abbrev xo:Shape :=⟨3, 3,1⟩
private theorem ax7:pG xo:=⟨by decide,by decide,by decide⟩
private theorem c4i {p q:lI} (hp:pG p) (hq:bF q) :
  pG (p.plus q) := by
 obtain ⟨hb,hj,ht⟩:=hp
 obtain ⟨hb',hj'⟩:=hq
 exact ⟨G1 hb hb',by dsimp [y5]; omega,by dsimp [y5]; omega⟩
private abbrev capMap (p:lI) :=vw ox (oD p)
private theorem aye {p:lI} (hp:pG p) :
  t7 (capMap p) := by
 obtain ⟨hb,hj,ht⟩:=hp
 apply Gj
 intro i
 fin_cases i <;> simp [oD,JM] <;> omega
private theorem cap_dimension (J:aU c9) {p:lI} (hp:pG p) :
  (lV (J.comap (capMap p).toRingHom)).natDegree=oY J :=
 GY (capMap p) (aye hp) J
private theorem aqS (hupper :c1) {J Q:aU c9} {a :c9}
   (ha :a∉J) (hQ:Q.IsPrime) (hann : ∀ x :c9,x*a∈J↔x∈Q)
   {d:ℕ} (hd:oY J≤d) (hd' : d≤2) {p:lI} (hp:pG p) :
   oZ J d p=oZ (J ⊔ cy {a}) d p+capCoeff Q d p:= by
 apply sS (hupper J Q a ha hQ hann d hd hd' p hp)
 let K:aU GeoJets :=J ⊔ cy {a}
 let f :=capMap p
 obtain ⟨A,hA⟩:=aye hp a
 have hAK:A∈K.comap f.toRingHom:= by
   change f A∈K
   rw [hA]
   exact u9 (th a)
 change (lV (K.comap f.toRingHom)).coeff d +
   (lV (Q.comap f.toRingHom)).coeff d ≤
   (lV (J.comap f.toRingHom)).coeff d
 refine ML.a4G (xu p6) hAK (fun x => ?_) ?_
 · change f (x*A)∈J↔f x∈Q
   rw [oK,show f A=a from hA,hann]
 · exact (cap_dimension J hp).trans_le hd
private theorem aWr {F G:lI→ℚ} (heq : ∀ r,pG r→F r=G r)
   {boxes :List lI} (hboxes : ∀ r∈boxes,bF r) {p:lI} (hp:pG p) :
   BE F boxes p=BE G boxes p:= by
 induction boxes generalizing p with
 | nil=>exact heq p hp
 | cons r boxes ih =>
   have hr :=hboxes r TI
   have hrest:= fun q hq=>hboxes q (zrw _ hq)
   simp only [BE,ih hrest (c4i hp hr),ih hrest hp]
private theorem eMC (F G:lI→ℚ) (boxes :List lI) (p:lI) :
   BE (fun r=>F r+G r) boxes p=BE F boxes p+BE G boxes p:= by
 induction boxes generalizing p with
 | nil=>rfl
 | cons r boxes ih =>
   simp only [BE,ih]
   ring
private theorem bKA (boxes :List lI) (p:lI) :
   BE (fun _=>0) boxes p=0:= by
 induction boxes generalizing p with
 | nil=>rfl
 | cons r boxes ih=>simp only [BE,ih,sub_self]
private theorem b9k (hupper :c1) {J Q:aU c9} {a :c9}
  (ha :a∉J) (hQ:Q.IsPrime) (hann : ∀ x :c9,x*a∈J↔x∈Q)
  {boxes :List lI} (hb : ∀ q∈boxes,bF q) (hsmall:boxes.length≤2)
  (hd:oY J≤boxes.length) :
  tW J boxes=tW (J ⊔ cy {a}) boxes+tW Q boxes := by
 unfold tW
 rw [aWr (fun _=>aqS hupper ha hQ hann hd hsmall) hb ax7,
  eMC,add_div]
private theorem capCoeff_le_of_subset (J:aU c9) {p q:lI}
    (hp:pG p) (hq:pG q) (hsub:oD p⊆oD q)
    {d:ℕ} (hd:oY J≤d) :
    oZ J d p≤ oZ J d q:= by
  let incl (i:oD p) :oD q:=⟨i.val,hsub i.property⟩
  let f :=zk (R:=ox) incl
  have hf : (capMap q).comp f=capMap p:= by
    ext i
    simp [f,incl,monomialMap_X]
  let I:=J.comap (capMap p).toRingHom
  let K:=J.comap (capMap q).toRingHom
  have heq :K.comap f.toRingHom=I:= by
    change (J.comap (capMap q).toRingHom).comap f.toRingHom= _
    rw [Ideal.comap_comap]
    change J.comap ((capMap q).comp f).toRingHom=I
    rw [hf]
  let g:=WX K f heq.ge
  have hg:qz g:=Ideal.quotientMap_injective' (H :=heq.ge) heq.le
  have hgen (i:oD p) :
      g (mD I (nI i))∈pz K 1 := by
    rw [show g (mD I (nI i)) =
        mD K (nI (incl i)) by
          change X4 K f.toRingHom heq.ge
            (mD I (nI i))= _
          rw [Ideal.quotientMap_mk]
          change mD K (zk incl (nI i))= _
          rw [Y4]]
    exact mk_X_mem_quotientDegreeLE K _
  change (lV I).coeff d≤(lV K).coeff d
  refine EP
    ((cap_dimension J hp).trans_le hd) ((cap_dimension J hq).trans_le hd) ?_
  filter_upwards [vl I,
    vl K] with n hI hK
  rw [hI,hK]
  have h:sH I n≤ sH K n:= by
    simpa only [t5] using affineHilbertFunction_le_of_injective g hg hgen n
  exact_mod_cast h
private theorem b9i (hpos :c2) {Q:aU c9} (hQ:Q.IsPrime)
    {boxes :List lI} (hb : ∀ q∈boxes,bF q) (hsmall:boxes.length≤2)
    (hd:oY Q≤boxes.length) :
    0≤tW Q boxes := by
  rcases hd.lt_or_eq with hlt | heq
  · have hz (p:lI) (hp:pG p) :oZ Q boxes.length p=0 :=
      zE ((cap_dimension Q hp).trans_lt hlt)
    unfold tW
    rw [aWr hz hb ax7,bKA,zero_div]
  · match boxes with
    | [] =>
      change 0≤ oZ Q 0 xo/(2 :ℚ)^0
      apply NW _ (by norm_num)
      exact RP
        ((cap_dimension Q ax7).trans_le heq.le)
        (Pk _)
    | [p] =>
      have hp:=hb p TI
      have hsub:oD xo⊆oD (xo.plus p) := by
        intro e hm
        exact ⟨hm.1.trans (vi 2 (yQ _ _)),
          hm.2.1.trans (vi 2 (yQ _ _)),
          hm.2.2.trans (vi 2 (yQ _ _))⟩
      change 0≤(oZ Q 1 (xo.plus p) - oZ Q 1 xo)/(2 :ℚ)^1
      exact NW (sub_nonneg.mpr
        (capCoeff_le_of_subset Q ax7 (c4i ax7 hp) hsub heq.le))
        (by norm_num)
    | [p,q] =>
      exact hpos Q hQ heq p q (hb p (by simp)) (hb q (by simp))
    | _ :: _ :: _ :: rest =>
      simp at hsmall
private theorem eAt {J Q P:aU c9} {a :c9}
  (hQ:Q.IsPrime) (hann : ∀ x :c9,x*a∈J↔x∈Q)
  (hP:J.IsMinimalPrime P) (hne :P≠Q) :
  (J ⊔ cy {a}).IsMinimalPrime P:= by
 have haP:a∈P:= by
  by_contra haP
  have hQP:Q≤P:= fun x hx =>
    (hP.isPrime.mem_or_mem (hP.le ((hann x).mpr hx))).resolve_right haP
  have hJQ:J≤Q:= fun x hx=>(hann x).mp (J.mul_mem_right _ hx)
  exact hne (hQP.antisymm (hP.2 ⟨hQ,hJQ⟩ hQP)).symm
 refine ⟨⟨hP.isPrime,zc hP.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haP))⟩,?_⟩
 intro U hU hUP
 exact hP.2 ⟨hU.1,le_sup_left.trans hU.2⟩ hUP
set_option maxHeartbeats 800000 in
theorem of_children (h1 :c1) (h2 :c2) :bjC.c2 := by
  classical
  intro J boxes hb hsmall hd S hS
  revert hd S hS
  induction J using EK (Ef (α:=aU c9)) with
  | h J ih =>
    intro hd S hS
    by_cases hJ:J = ⊤
    · subst J
      have hS0:S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun P hP =>
        (hS P hP).isPrime.ne_top (top_le_iff.mp (hS P hP).le)
      have hz (p:lI) (_:pG p) :oZ (⊤ : aU c9) boxes.length p=0:= by
        simp [oZ,Nr,J4]
      rw [hS0,TH]
      unfold tW
      rw [aWr hz hb ax7,bKA,zero_div]
    obtain ⟨a,Q,ha,hQ,hann⟩:=ML.bdz hJ
    let K:aU GeoJets :=J ⊔ cy {a}
    have hJK:J≤K:=p6
    have haK:a∈K:=u9 (th a)
    have hlt:J<K:=wA hJK fun he=>ha (he ▸ haK)
    have hJQ:J≤Q:= fun x hx=>(hann x).mp (J.mul_mem_right _ hx)
    have hKd:=(t9 hJK).trans hd
    have hQd:=(t9 hJQ).trans hd
    have hrest (P:aU c9) (hP:P∈S.erase Q) :K.IsMinimalPrime P :=
      eAt hQ hann (hS P (Finset.mem_of_mem_erase hP)) (Finset.ne_of_mem_erase hP)
    have hrec:=ih K hlt hKd (S.erase Q) hrest
    rw [b9k h1 ha hQ hann hb hsmall hd]
    change _≤tW K boxes+tW Q boxes
    by_cases hQS:Q∈S
    · rw [← Finset.sum_erase_add _ _ hQS]
      exact Nj hrec vh
    · rw [Finset.erase_eq_of_notMem hQS] at hrec
      exact hrec.trans (Qy (b9i h2 hQ hb hsmall hQd))
end
end bzI
end
section
namespace dnh
noncomputable section
open Filter MvPolynomial Polynomial
open aR dN rW NS
section Filtration
variable {k σ τ:Type*} [uJ k]
variable {I:aU (lz σ k)} {J:aU (lz τ k)}
private theorem afo
   (g: (lz τ k ⧸ J) →ₐ[k] (lz σ k ⧸ I))
   (d:lz τ k ⧸ J)
   (hgen : ∀ i,∃ a,g d* mD I (nI i)=g a)
   (x :lz σ k ⧸ I) :
   ∃ (e :ℕ) (a :lz τ k ⧸ J),g d^e*x=g a := by
 obtain ⟨p,rfl⟩:=zf x
 induction p using Yo with
 | C c =>
   refine ⟨0,lJ k _ c,?_⟩
   rw [pow_zero,t5]
   exact (g.commutes c).symm
 | add p q hp hq =>
   obtain ⟨e,a,ha⟩:=hp
   obtain ⟨f,b,hb⟩:=hq
   refine ⟨e+f,d^f*a+d^e*b,?_⟩
   simp only [t8 ,oK,Du,pow_add,zR]
   calc
     _=g d^f*(g d^e* mD I p) +
         g d^e*(g d^f* mD I q) := by ac_rfl
     _ = _:= by rw [ha,hb]
 | mul_X p i hp =>
   obtain ⟨e,a,ha⟩:=hp
   obtain ⟨b,hb⟩:=hgen i
   refine ⟨e+1,a*b,?_⟩
   simp only [oK,pow_succ]
   calc
     _=(g d^e* mD I p) *
         (g d* mD I (nI i)) := by ac_rfl
     _ = _:= by rw [ha,hb]
private abbrev bex
   (g: (lz τ k ⧸ J) →ₐ[k] (lz σ k ⧸ I)) (n:ℕ) :=
 (pz J n).map g.toLinearMap
variable [qU σ] [qU τ]
private theorem cUO
    (g: (lz τ k ⧸ J) →ₐ[k] (lz σ k ⧸ I))
    (d:lz τ k ⧸ J) (hd:vk (g d))
    (hgen : ∀ j,∃ a,g d* mD I (nI j)=g a)
    (i:τ) {ℓ:lz σ k}
    (hℓ:g (mD J (nI i))=mD I ℓ)
    (hred:ahc I ℓ) :
    ∃ C:ℕ,∀ n:ℕ,sH I n≤ sH J (n+C) := by
  classical
  obtain ⟨N,hN⟩:=hred
  let B:=Module.finBasis k (pz I N)
  choose e a ha using fun j ↦ afo g d hgen (B j:lz σ k ⧸ I)
  obtain ⟨E,hE⟩:=SM e
  let Fr := fun j ↦ d^(E-e j)*a j
  have hclear (j:Fin (Gr k (pz I N))) :
      g d^E*(B j:lz σ k ⧸ I)=g (Fr j) := by
    calc
      _=g d^(E-e j)*(g d^e j*(B j:lz σ k ⧸ I)) := by
        rw [← yB,← pow_add,Nat.sub_add_cancel (hE j)]
      _ = _:= by rw [ha j]; simp only [Fr,oK,Du]
  choose levels hlevels using fun j ↦ exists_mem_quotientDegreeLE J (Fr j)
  obtain ⟨C,hC⟩:=SM levels
  have hbase (x :lz σ k ⧸ I) (hx :x∈pz I N) :
      g d^E*x∈bex g C:= by
    let z :pz I N :=⟨x,hx⟩
    have hz : (∑ j,(B.repr z j)•(B j:lz σ k ⧸ I))=x := by
      simpa only [Gi ,map_smul,Submodule.subtype_apply] using
        qy (pz I N).subtype (B.sum_repr z)
    rw [← hz,zg]
    refine VO _ fun j _ ↦ ?_
    rw [show g d^E*((B.repr z j)•(B j:lz σ k ⧸ I)) =
      (B.repr z j)•(g d^E*(B j:lz σ k ⧸ I)) from
        Algebra.mul_smul_comm (B.repr z j) (g d^E) (B j:lz σ k ⧸ I),hclear j]
    apply Submodule.smul_mem
    exact Submodule.mem_map.mpr ⟨_,IT J (hC j) (hlevels j),rfl⟩
  have hall (n:ℕ) : ∀ x∈pz I n,g d^E*x∈bex g (n+C) := by
    induction n with
    | zero =>
      intro x hx
      simpa using hbase x (IT I (Nat.zero_le N) hx)
    | succ n ih =>
      intro x hx
      by_cases hn:N≤n
      · obtain ⟨u,hu,v,hv,rfl⟩:=hN n hn x hx
        obtain ⟨s,hs,he⟩:=Submodule.mem_map.mp (ih v hv)
        change g s=g d^E*v at he
        rw [zR,NY (g d^E),← hℓ]
        apply zcy
        · exact Pr (IT J (by omega)) (ih u hu)
        · change g _ *(g d^E*v)∈_
          rw [← he,← oK]
          exact Submodule.mem_map.mpr ⟨_,by
            simpa only [Nat.add_left_comm,Nat.add_comm,Nat.add_assoc] using
              mul_mem_quotientDegreeLE (mk_X_mem_quotientDegreeLE J i) hs,rfl⟩
      · exact Pr (IT J (Ok C _))
          (hbase x (IT I (by omega) hx))
  refine ⟨C,fun n ↦ ?_⟩
  let mult:=(zzN k (g d^E)).comp (pz I n).subtype
  let m:pz I n →ₗ[k] bex g (n+C) :=
    mult.codRestrict (bex g (n+C)) (fun x ↦ hall n x x.property)
  have hm:qz m:= by
    intro x y hxy
    exact t6 ((hd.pow E) (qy Xg hxy))
  have hfin:QL k (bex g (n+C)) := by
    unfold bex
    infer_instance
  exact (NZ hm).trans (Submodule.finrank_map_le _ _)
private theorem cJ2
   (g: (lz τ k ⧸ J) →ₐ[k] (lz σ k ⧸ I)) (hg:qz g)
   {C:ℕ} (hupper : ∀ n:ℕ,sH I n≤ sH J (n+C)) :
   oq J=oq I∧qx I≤qx J:= by
 let P:=lV I
 let Q:=lV J
 have hshift:Tendsto (fun n:ℕ ↦ n+C) atTop atTop :=
   tendsto_atTop_mono (fun n ↦ yQ n C) tendsto_id
 have hbound : ∀ᶠ n:ℕ in atTop,P.eval (n:ℚ)≤(zS (C:ℚ) Q).eval (n:ℚ) := by
   filter_upwards [vl I,
     hshift.eventually (vl J)] with n hn hnC
   rw [G3 ,← Et,hn,hnC]
   exact_mod_cast hupper n
 have hle :=Xo
   (Pk I) hbound
 have hdeg:P.natDegree= Q.natDegree :=
   (hle.1.trans_eq (zm Q _)).antisymm
     (natDegree_affineHilbertPolynomial_le_of_injective g hg)
 have hlc:P.leadingCoeff≤Q.leadingCoeff := by
   simpa only [leadingCoeff_taylor] using hle.2 (hdeg.trans (zm Q _).symm)
 refine ⟨hdeg.symm,?_⟩
 change (P.natDegree.factorial:ℚ)*P.leadingCoeff ≤
   (Q.natDegree.factorial:ℚ)*Q.leadingCoeff
 rw [hdeg]
 exact SW hlc (by positivity)
end Filtration
end
end dnh
end
section
namespace cyK
noncomputable section
open aR dN Dr MvPolynomial
theorem proof :bzI.c1 := by
  intro J Q a _ _ hann d hd _ p hp
  let f :=vw ox (oD p)
  have hf :t7 f := by
    obtain ⟨hb,hj,ht⟩:=hp
    apply Gj
    intro i
    fin_cases i <;> simp [oD,JM] <;> omega
  obtain ⟨A,hA⟩:=hf a
  have hcut: (J ⊔ cy {a}).comap f.toRingHom =
      J.comap f.toRingHom ⊔ cy {A} := by
    have hmap : (J.comap f.toRingHom ⊔ cy {A}).map f.toRingHom =
        J ⊔ cy {a} := by
      rw [uW,LP f.toRingHom hf,uz ,
        vZ,show f.toRingHom A=a from hA]
    rw [← hmap,G5 f.toRingHom hf]
    exact sup_eq_left.mpr ((xu (f :=f.toRingHom) bot_le).trans p6)
  have hann' (x :lz (oD p) ox) :
      x*A∈J.comap f.toRingHom↔x∈Q.comap f.toRingHom:= by
    change f (x*A)∈J↔f x∈Q
    rw [oK,hA,hann]
  have hd' : (lV (J.comap f.toRingHom)).natDegree≤d :=
    (GY f hf J).trans_le hd
  change (lV (J.comap f.toRingHom)).coeff d ≤
    (lV ((J ⊔ cy {a}).comap f.toRingHom)).coeff d +
      (lV (Q.comap f.toRingHom)).coeff d
  rw [hcut]
  exact bzC.proof _ _ A hann' d hd'
end
end cyK
end
section
namespace bau
noncomputable section
open aR dN Dr Kd ap8 lB
open Filter Polynomial
open scoped BigOperators
private theorem gp0 {ι:Type} [sI ι]
  (s :ι→lI) (v :ι→ℕ) (n:ℕ) :
  ku s (n•v)=(ku s v).scale n:= by
 simp [ku,Shape.scale,Pi.smul_apply,yB,zg]
private theorem aXZ {J:aU c9} {p q:lI}
   (hb:p.b≤q.b) (hj:p.j≤q.j) (ht:p.t≤q.t) :
   Sn J (oD p)≤Sn J (oD q) := by
 have hsub:oD p⊆oD q :=
   fun _ hm=>⟨hm.1.trans (vi _ hb),
     hm.2.1.trans (vi _ hj),hm.2.2.trans (vi _ ht)⟩
 let:QL ox (xI ox (oD q)) :=
   MvPolynomial.restrictSupport_finite (Set.toFinite _)
 exact Submodule.finrank_mono (Pr (VC _ hsub))
theorem fT9 {ι:Type} [sI ι] (s :ι→lI)
   (hs : ∀ i,bF (s i)) (J:aU c9) (P:lz ι ℚ)
   (u v :ι→ℕ) (hv :0<(ku s v).t)
   (hP : ∀ a≥u,oy (fun i=>(a i:ℚ)) P =
     (Sn J (oD (ku s a)) :ℚ))
   (d:ℕ) (hd:oY J≤d) :
   (BZ P u v).natDegree≤d ∧
     (BZ P u v).coeff d=oZ J d (ku s v) := by
 let q:=ku s v
 let w:=ku s u
 let I:=J.comap (vw ox (oD q)).toRingHom
 let A:=lV I
 let Q:=BZ P u v
 let c:=w.b+w.j+w.t
 let B:=zS (c:ℚ) A
 have hq:pG q:=⟨(awr s hs v).1,(awr s hs v).2,hv⟩
 have hqt:1≤q.t:=hv
 have hj:3*q.t≤q.j:=hq.2.1
 have hb:q.j≤q.b:=hq.1
 have hqb:1≤q.b:= by omega
 have hqj:1≤q.j:= by omega
 have hshift (n:ℕ) {x y :ℕ} (hx :x≤ c) (hy :1≤y) :
     x+n*y≤(n+c)*y := by
   rw [Nat.add_mul,FU (n*y)]
   exact VH (hx.trans (by simpa using vi c hy)) _
 have hQ (n:ℕ) :Q.eval (n:ℚ) =
     (Sn J (oD (w.plus (q.scale n))) :ℚ) := by
   rw [bgE]
   change oy (fun i=>(((u+n•v) i:ℕ) :ℚ)) P= _
   rw [hP _ (Qy zero_le),aES,gp0]
 have hA : ∀ᶠ n:ℕ in atTop,
     A.eval (n:ℚ)=(Sn J (oD (q.scale n)) :ℚ) := by
   filter_upwards [vl I] with n hn
   rw [hn,dEX J q hq]
 have hB : ∀ᶠ n:ℕ in atTop,
     B.eval (n:ℚ)=(Sn J (oD (q.scale (n+c))) :ℚ) := by
   obtain ⟨m,hm⟩:=eventually_atTop.mp hA
   refine eventually_atTop.mpr ⟨m,fun n hn => ?_⟩
   change (zS (c:ℚ) A).eval (n:ℚ)= _
   rw [G3]
   simpa [FU] using hm (n+c) (hn.trans (yQ n c))
 have hlo : ∀ᶠ n:ℕ in atTop,A.eval (n:ℚ)≤Q.eval (n:ℚ) := by
   filter_upwards [hA] with n hn
   rw [hn,hQ]
   exact_mod_cast (aXZ (J:=J) (p:=q.scale n) (q:=w.plus (q.scale n))
     (Ok ..) (Ok ..) (Ok ..))
 have hhi : ∀ᶠ n:ℕ in atTop,Q.eval (n:ℚ)≤B.eval (n:ℚ) := by
   filter_upwards [hB] with n hn
   rw [hQ,hn]
   exact_mod_cast (aXZ (J:=J) (p:=w.plus (q.scale n)) (q:=q.scale (n+c))
     (hshift n (by dsimp [c]; omega :w.b≤ c) hqb)
     (hshift n (by dsimp [c]; omega :w.j≤ c) hqj)
     (hshift n (by dsimp [c]; omega :w.t≤ c) hqt))
 have hdim:A.natDegree=oY J :=
   GY _ (aCx q hq) J
 have hAd:A.natDegree≤d:=hdim.trans_le hd
 have hBd:B.natDegree≤d:=(zm A _).trans_le hAd
 have hQd:Q.natDegree≤d :=
   ((Xo
     (Filter.Eventually.of_forall fun n=> by rw [hQ]; positivity) hhi).1).trans hBd
 refine ⟨hQd,sS ?_ ?_⟩
 · have h:=EP hQd hBd hhi
   change Q.coeff d≤(zS (c:ℚ) A).coeff d at h
   rwa [Ob _ hAd] at h
 · exact EP hAd hQd hlo
theorem cKj {ι:Type} [xL ι] (used :List ι)
   (A B: (ι→ℕ)→ℚ) (a :ι→ℕ) (h : ∀ b≥a,A b=B b) :
   uU used A a=uU used B a := by
 induction used generalizing a with
 | nil=>exact h a le_rfl
 | cons i rest ih =>
   have hshift : ∀ b≥a+step i,A b=B b:= fun b hb =>
     h b ((Qy zero_le).trans hb)
   simp only [uU,ih _ hshift,ih _ h]
theorem dV2 {ι:Type} [sI ι] [xL ι] (s :ι→lI)
   (F:lI→ℚ) (used :List ι) (a :ι→ℕ) :
   uU used (fun v=>F (ku s v)) a =
     BE F (used.map s) (ku s a) := by
 induction used generalizing a with
 | nil=>rfl
 | cons i rest ih =>
   simp only [uU,List.map_cons,BE,ih,aES,aQe]
end
end bau
end
section
namespace bzJ
open aR dN lB aFW MvPolynomial
private theorem gxG {S:aU c9} [S.IsPrime]
  (hS:S.height=2) : (lV S).natDegree=2 := by
 have hS₀: (⊥ : aU c9)<S :=
  bot_lt_iff_ne_bot.mpr (fun h=> by simp [h,Ideal.height_bot] at hS)
 obtain ⟨f,hf,hf₀⟩:=zxV hS₀
 have hfne :f≠0:= fun h=>hf₀ (h ▸ Ideal.zero_mem _)
 obtain ⟨D,hD,hDS⟩ :=
  Cy ((Ea S).mpr hf)
 let:D.IsPrime :=hD.isPrime
 have hD₀:D ≠ ⊥ := fun h =>
  hfne (Ideal.mem_bot.mp (h ▸ hD.le (th f)))
 have hDh:D.height = 1 :=sS
  (zx8 _ D hD)
  (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hD₀))
 have hDS' : D <S:=wA hDS (fun h=> by simp [h,hS] at hDh)
 obtain ⟨g,hg,hgD⟩:=zxV hDS'
 obtain ⟨E,hE,hES⟩:=Cy
  (zc hDS ((Ea S).mpr hg))
 let:E.IsPrime :=hE.isPrime
 have hDE :D <E :=Ideal.lt_of_mem_minimalPrimes_sup_span hgD hE
 have hEh:=Mk hDE
 rw [hDh] at hEh
 have hES' : E=S:=zKE E hES (by
  rw [hS,show (2 :ℕ∞)=1+1 by decide]
  exact hEh)
 have h₁:=Ye hfne hD
 have h₂:=C9 hgD hE
 rw [R9] at h₁
 rw [hES'] at h₂
 omega
private theorem eFj {k A:Type*} [uJ k] [ov A] [IsDomain A]
   {d:ℕ} (g:lz (Fin d) k →+* A) (hgi:qz g)
   (hgf :g.Finite) :Gn A=(d:WithBot ℕ∞) := by
 let B:=lz (Fin d) k
 let inst :=g.toAlgebra
 let:=inst
 let:QL B A:=hgf
 let:FaithfulSMul B A:=(faithfulSMul_iff_algebraMap_injective _ _).mpr hgi
 have hB:Gn B=(d:WithBot ℕ∞) := by
   rw [zmx,zZT]
   simp
 rw [← hB]
 apply sS
 · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (lJ B A))
   intro x y hxy
   exact Ideal.IsIntegral.under_lt_under (show x.asIdeal<y.asIdeal from hxy)
 · obtain ⟨b,hb,hbh⟩:=Ideal.exists_isPrime_le_height (n:=d) hB.ge
   obtain ⟨z,hz⟩:=Algebra.IsIntegral.comap_surjective B A (⟨b,hb⟩:nq B)
   have hz' : z.asIdeal.under B=b:=qy zyo hz
   have hle :=zJf (R:=B) z.asIdeal
   rw [hz'] at hle
   calc
     Gn B=(d:WithBot ℕ∞) :=hB
     _≤(z.asIdeal.height:WithBot ℕ∞) :=WithBot.coe_le_coe.mpr (hbh.trans hle)
     _≤ Gn A:=ztp
theorem dOx {S:aU c9} {P:c9} {C:aU c9}
  (hC:aSw S P C) :C.IsPrime∧Gn (c9 ⧸ C)=1 := by
 let:S.IsPrime :=hC.prime
 let:C.IsPrime :=hC.component.isPrime
 have hS:=gxG hC.height
 have hcut:=C9 hC.proper hC.component
 have hdeg: (lV C).natDegree=1 := by omega
 obtain ⟨d,g,hgi,hgf⟩:=exists_finite_inj_algHom_of_fg ox (c9 ⧸ C)
 have hd:=natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hgf hgi
 rw [hdeg,R9] at hd
 refine ⟨hC.component.isPrime,?_⟩
 simpa [← hd] using eFj g.toRingHom hgi hgf
theorem dHS {a :lI} (ha :bF a) (ht:0<a.t) :
  aO ⟨1,3,1⟩ a := by
 obtain ⟨hb,hj⟩:=ha
 change 1≤a.b∧3≤a.j∧1≤a.t
 omega
end bzJ
end
section
namespace Tx
noncomputable section
open Polynomial Finset K1 aR wH
open scoped BigOperators
private theorem cr2 {H :lI} {F G:gQ}
   (hF:pC H F) (hG:pC H G) :pC H (F-G) := by
 intro m hm
 rcases mem_union.mp (MvPolynomial.support_sub _ _ _ hm) with hm | hm
 · exact hF m hm
 · exact hG m hm
private theorem crZ {H :lI} {F:gQ} (hF:pC H F)
  (a :cH) :pC H (p7 a*F) := by
 intro m hm
 apply hF m
 rw [zuk] at hm ⊢
 rw [MvPolynomial.coeff_C_mul] at hm
 exact right_ne_zero_of_mul hm
private theorem bOF (H :lI) (a :cH) :pC H (p7 a) := by
 classical
 by_cases ha :a=0
 · simp [ha,pC]
 intro m hm
 rw [MvPolynomial.support_C,t4 (fun h=>(ha h).elim),Sd] at hm
 subst m
 simp
private theorem dgk {H :lI} (hb:1≤H.b) (hj:3≤H.j) (ht:1≤H.t)
  (i:Fin 4) :pC H (nI i) := by
 intro m hm
 rw [RC,Sd] at hm
 subst m
 have hi:i.val≤H.j:=(show i.val≤3 by omega).trans hj
 refine ⟨by simpa,by simpa,?_⟩
 simpa only [OJ] using (show (if i=(3:Fin 4) then 1 else 0)≤H.t by
  split <;> omega)
private theorem bdx {r :nq gQ} {y :oe}
   (h:r.asIdeal<Ol y) :
   ∃ i:Fin 4,nI i-MvPolynomial.C (y i)∉r.asIdeal:= by
 by_contra! hmem
 let π:=mD r.asIdeal
 have hmaps :π=π.comp (MvPolynomial.C.comp (oy y)) := by
   apply FV
   · intro a
     simp
   · intro i
     have heq :=Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
     rw [Dv,sub_eq_zero] at heq
     simpa using heq
 apply not_le_of_gt h
 intro F hF
 have hz :oy y F=0:=RingHom.mem_ker.mp hF
 apply Ideal.Quotient.eq_zero_iff_mem.mp
 change π F=0
 calc
   π F=π (p7 (oy y F)) :=yU hmaps F
   _=0:= by rw [hz,pQ,pQ]
private theorem cVW:qz zq:= by
 intro S T h
 have h0:=Ml h (0:Fin 4)
 have hi:qz qY :=
  (lJ iP cH).injective.comp (GF ao[X] iP)
 exact hi (by simpa [zq,jet,Polynomial.hasseDeriv_zero'] using h0)
private theorem cFs {H :lI} (C:a1h H) (i:I) (a :K) :
  pC H (C.numerator i-MvPolynomial.C (constantCoeff a)*C.denominator) :=
 cr2 (C.numerator_supported i) (crZ C.denominator_supported _)
private theorem b1T {H :lI} {C:a1h H} {S:K[X]}
    (hS:C.ar5 S) (i:I) (a :K) :
    oy (zq (extend S))
        (C.numerator i-MvPolynomial.C (constantCoeff a)*C.denominator)=0 ↔
      S.eval (node i)=a := by
  have hinj:qz constantCoeff :=constantCoeff.injective
  rw [Dv,oK,MvPolynomial.eval_C,hS.2 i,sub_eq_zero]
  exact ⟨fun h=>hinj (mul_right_cancel₀ hS.1 h),fun h=> by rw [h]⟩
private theorem dlX (weight O3 gap:ℕ) {n a b capA capB:ℕ}
  (hpos :0<weight*gap) (h:gap*n≤O3*a+gap*b)
  (ha :weight*a≤ capA) (hb:weight*b≤ capB) :
  n≤ ceilDiv (O3*capA+gap*capB) (weight*gap) := by
 have hscaled:n*(weight*gap)≤O3*capA+gap*capB:= calc
  _=weight*(gap*n) := by ac_rfl
  _≤weight*(O3*a+gap*b) :=vi _ h
  _=O3*(weight*a)+gap*(weight*b) := by
    rw [Nat.mul_add]
    congr 1 <;> ac_rfl
  _≤_:=G1 (vi _ ha) (vi _ hb)
 unfold ceilDiv
 exact (Nat.le_div_iff_mul_le hpos).mpr (by omega)
end
end Tx
end
section
namespace XU
noncomputable section
open aR lB Tx
open scoped BigOperators Pointwise
def bTw (r :nq gQ) (D:gQ) (T:nX oe) :Prop :=
 D∉r.asIdeal ∧ ∀ y∈T,r.asIdeal≤Ol y∧oy y D =0
def pointPrime (y :oe) :nq gQ :=
 ⟨Ol y,Oc (oy y)⟩
def ke (J:aU gQ) (D:gQ) :aU gQ :=
 J ⊔ cy {D}
def bRb (J:aU gQ) (m:ℕ) (y :oe) :Prop :=
 Ol y∈J.minimalPrimes∧(m:ℕ∞)≤ajK (pointPrime y) J
def bQE (J:aU gQ) (r :nq gQ) (a :gQ) :Prop :=
  a∉r.asIdeal ∧
  (∀ q∈J.minimalPrimes,q≠r.asIdeal→a∈q) ∧
  ∀ D:gQ,D∉r.asIdeal →
    ∀ y :oe,r.asIdeal≤Ol y→ oy y a≠0 →
      oy y D =0 →
      Ol y∈(ke J D).minimalPrimes ∧
      ajK r J≤ajK (pointPrime y) (ke J D)
abbrev QC:=Fin 4→ℝ
def nD (p:lI) :Set QC :=
  {x | (∀ i,0≤x i)∧(∑ i,x i)≤p.b ∧
    (∑ i:Fin 4,(i.val :ℝ)*x i)≤p.j∧x 3≤p.t}
def a2a (x :Set QC) :ℝ :=
 (MeasureTheory.volume x).toReal
def aTq (F:Set QC→ℝ) (a x :Set QC) :ℝ :=
 F (x+a)-F x
def aTr (p q r s :lI) :ℝ :=
  aTq (aTq (aTq (aTq a2a (nD p))
    (nD q)) (nD r)) (nD s) {0}
theorem aTp:nD ⟨0,0,0⟩=({0} : Set QC) := by
 ext x
 constructor
 · intro hx
   have hsum: (∑ i,x i)≤0:= by simpa using hx.2.1
   apply Set.mem_singleton_iff.mpr
   funext i
   have hle :x i ≤ ∑ k,x k :=
     zfK (fun k _=>hx.1 k) (FR i)
   exact sS (hle.trans hsum) (hx.1 i)
 · intro hx
   rw [Set.mem_singleton_iff.mp hx]
   simp [nD]
private theorem bsv (p:lI) (x :QC) :
  x∈nD p↔(∀ i,0≤x i)∧x 0 + x 1 + x 2 + x 3≤p.b ∧
    x 1+2*x 2 + 3*x 3≤p.j∧x 3≤p.t:= by
 norm_num [nD,JM]
private theorem cqG {x a b:ℝ} (hb:0≤b) (hx :x≤a+b) :
  x - min x a≤b:= by
 rw [min_def]
 split <;> linarith
theorem cDV (p q:lI) (hp:bF p) (hq:bF q) :
    nD (p.plus q)=nD p+nD q:= by
  ext x
  rw [bsv]
  change _ ↔ ∃ u∈nD p,∃ v∈nD q,u+v=x
  constructor
  · rintro ⟨hx,htotal,hindex,htop⟩
    simp only [y5 ,Et] at htotal hindex htop
    have hpj: (p.j:ℝ)≤p.b:= by exact_mod_cast hp.1
    have hqj: (q.j:ℝ)≤q.b:= by exact_mod_cast hq.1
    have hpt:3*(p.t:ℝ)≤p.j:= by exact_mod_cast hp.2
    have hqt:3*(q.t:ℝ)≤q.j:= by exact_mod_cast hq.2
    let u3:=min (x 3) (p.t:ℝ)
    let v3:=x 3 - u3
    have hu3:0≤u3:=le_min (hx 3) (Pf _)
    have hpu3:u3≤p.t:=Fa _ _
    have hv3:0≤v3:=sub_nonneg.mpr (F9 _ _)
    have hqv3:v3≤q.t:=cqG (Pf _) htop
    let jp:=(p.j:ℝ)-3 * u3
    let jq:=(q.j:ℝ)-3*v3
    have hjp:0≤jp:= by dsimp only [jp]; linarith
    have hjq:0≤jq:= by dsimp only [jq]; linarith
    have hcharge :x 1+2*x 2≤jp+jq:= by
      dsimp only [jp,jq,v3]
      linarith
    let u1 :=min (x 1) jp
    let u2 :=min (x 2) ((jp - u1)/2)
    have hu1 :0≤u1 :=le_min (hx 1) hjp
    have hpu1 :u1≤jp:=Fa _ _
    have hu2 :0≤u2 :=le_min (hx 2) (by linarith)
    have hv1 :0≤x 1 - u1 :=sub_nonneg.mpr (F9 _ _)
    have hv2 :0≤x 2 - u2 :=sub_nonneg.mpr (F9 _ _)
    have hspent:u1+2*u2=min (x 1+2*x 2) jp:= by
      dsimp only [u1,u2]
      simp only [min_def]
      split_ifs <;> linarith [hx 2]
    have hpu:u1+2*u2≤jp:=hspent.le.trans (Fa _ _)
    have hqv : (x 1 - u1)+2*(x 2 - u2)≤jq:= by
      linarith [cqG hjq hcharge]
    dsimp only [jp] at hpu
    dsimp only [jq] at hqv
    let bp:=(p.b:ℝ) - u3 - u1 - u2
    let bq:=(q.b:ℝ) - v3-(x 1 - u1)-(x 2 - u2)
    have hbp:0≤bp:= by dsimp only [bp]; linarith
    have hbq:0≤bq:= by dsimp only [bq]; linarith
    have hfree :x 0≤bp+bq:= by dsimp only [bp,bq,v3]; linarith
    let u0:=min (x 0) bp
    have hu0:0≤u0:=le_min (hx 0) hbp
    have hv0:0≤x 0 - u0:=sub_nonneg.mpr (F9 _ _)
    have hpu0:u0≤bp:=Fa _ _
    have hqv0:x 0 - u0≤bq:=cqG hbq hfree
    dsimp only [bp] at hpu0
    dsimp only [bq] at hqv0
    let u:QC := ![u0,u1,u2,u3]
    let v :QC:=x - u
    refine ⟨u,(bsv p u).mpr ?_,v,(bsv q v).mpr ?_,?_⟩
    · refine ⟨?_,?_,?_,hpu3⟩
      · intro i
        fin_cases i <;> assumption
      · change u0+u1+u2+u3≤(p.b:ℝ)
        linarith
      · change u1+2*u2 + 3 * u3≤(p.j:ℝ)
        linarith
    · refine ⟨?_,?_,?_,hqv3⟩
      · intro i
        fin_cases i <;> assumption
      · change (x 0 - u0)+(x 1 - u1)+(x 2 - u2)+v3≤(q.b:ℝ)
        linarith
      · change (x 1 - u1)+2*(x 2 - u2)+3*v3≤(q.j:ℝ)
        linarith
    · change u+(x - u)=x
      abel
  · rintro ⟨u,hu,v,hv,rfl⟩
    obtain ⟨hu,hub,huj,hut⟩:=(bsv p u).mp hu
    obtain ⟨hv,hvb,hvj,hvt⟩:=(bsv q v).mp hv
    refine ⟨fun i=>add_nonneg (hu i) (hv i),?_,?_,?_⟩ <;>
      simp only [SL,y5 ,Et] <;> linarith
end
end XU
end
section
namespace XU
noncomputable section
open aR wH lB Tx
open scoped BigOperators Pointwise
def c1 :Prop :=
  ∀ H :lI,(∀ i:Fin 4,pC H (nI i)) →
    ∀ (R:nX (nq gQ)),(∀ r∈R,r.asIdeal.height=3) →
    ∀ (guard :nq gQ→ gQ),(∀ r∈R,guard r∉r.asIdeal) →
    ∀ (cut:nq gQ→ gQ) (points :nq gQ→nX oe),
      (∀ r∈R,pC H (cut r)∧bTw r (cut r) (points r)) →
      ∃ (D:gQ) (Ig:nq gQ→nX oe),
        pC H D ∧
        ∀ r∈R,(points r).card≤(Ig r).card∧bTw r D (Ig r) ∧
          ∀ y∈Ig r,oy y (guard r)≠0
def c2 :Prop :=
  ∀ (J:aU gQ) (r :nq gQ),
    r.asIdeal∈J.minimalPrimes→ r.asIdeal.height=3→ajK r J < ⊤ →
    ∃ a :gQ,bQE J r a
def c3:Prop :=
  ∀ (p q H :lI),bF p→bF q→bF H →
    ∀ (F G L D:gQ),pC p F→pC q G→pC q L→pC H D →
      ∀ (m:ℕ) (points :nX oe),
        (∀ y∈points,bRb (ke (cy {F,G,L}) D) m y) →
        ((32*m*points.card:ℕ) :ℝ)≤32*aTr p q q H
def c4 :Prop :=
 ∀ p:lI,bF p→32*a2a (nD p)=(Dn p:ℝ)
private theorem dgl (f :af 4) :pC (shape f).iU (ay7 f) := by
 intro m hm
 have hm' : m∈f.support :=Zf qY f hm
 refine ⟨(MvPolynomial.le_totalDegree hm').trans (le_max_left _ _),?_,
  MvPolynomial.le_degreeOf_of_mem_support 3 hm'⟩
 exact TZ (f := fun m:Fin 4 →₀ ℕ=>m.sum (fun i a=>i.val*a)) hm'
private theorem dgm {H :lI} (hc:bF H) (ht:1≤H.t)
  (i:Fin 4) :pC H (nI i) := by
 obtain ⟨hb,hj⟩:=hc
 have hi:i.val≤3:= by omega
 intro m hm
 rw [RC,Sd] at hm
 subst m
 refine ⟨by simpa using (show 1≤H.b by omega),by simpa using (show i.val≤H.j by omega),?_⟩
 simpa only [OJ] using
  (show (if i=(3:Fin 4) then 1 else 0)≤H.t by split <;> omega)
private theorem Nc {p q:lI} (hp:bF p) (hq:bF q) :
  bF (p.plus q) := by
 obtain ⟨hb,hj⟩:=hp
 obtain ⟨hb',hj'⟩:=hq
 change p.j+q.j≤p.b+q.b∧3*(p.t+q.t)≤p.j+q.j
 omega
private theorem bEh {a :lI} (ha :bF a)
   {F:Set QC→ℝ} {G:lI→ℤ}
   (h : ∀ x,bF x→32*F (nD x)=(G x :ℝ)) :
   ∀ x,bF x →
     32*aTq F (nD a) (nD x)=(gI G a x :ℝ) := by
 intro x hx
 rw [aTq,mul_sub,← cDV x a hx ha,h _ (Nc hx ha),h x hx]
 simp [gI]
private theorem c0w (hvol:c4) {p q r s :lI}
   (hp:bF p) (hq:bF q) (hr :bF r) (hs :bF s) :
   32*aTr p q r s =
     (gI (gI (gI (gI Dn p) q) r) s ⟨0,0,0⟩:ℝ) := by
 unfold aTr
 rw [← aTp]
 exact bEh hs
   (bEh hr (bEh hq (bEh hp hvol)))
     ⟨0,0,0⟩ ⟨vh,vh⟩
end
end XU
end
section
namespace VG
noncomputable section
open aR Tx XU
open scoped BigOperators
abbrev Exponent:=zP.Exponent
def dM (s :lI) (a :Exponent) :Prop :=
 (∑ i,a i)≤ s.b∧(∑ i:Fin 4,i.val*a i)≤ s.j∧a 3≤ s.t
def PS (s :lI) :nX Exponent :=
  ((XJ (s.scale 2).b).subset
    (show {a | dM (s.scale 2) a} ⊆ {a | a.degree≤(s.scale 2).b} by
      intro a ha
      change a.degree≤(s.scale 2).b
      rw [Finsupp.degree_eq_sum]
      exact ha.1)).toFinset
def Eb (p q H :lI) :Fin 4→nX Exponent :=
 ![PS p,PS q,PS q,PS H]
abbrev MZ (y :oe) :=vH (pointPrime y).asIdeal
end
end VG
end
section
namespace aKu
open Polynomial aR wH Tx
noncomputable section
def adT (R:Type*) [GB R] :
    lz (Fin 4) R ≃ₐ[R] (lz (Fin 3) R)[X] :=
  (MvPolynomial.renameEquiv R SD).trans (Wl R (Fin 3))
private theorem b7d {R:Type*} [GB R] (a :R) :
  adT R (p7 a)=qm (p7 a) := by
 simp [adT,SC]
private theorem cWN {R:Type*} [GB R] :
  adT R (nI (3:Fin 4))=Polynomial.X:= by
 change Wl R (Fin 3)
  (zk SD (nI (yJ 3)))= _
 rw [Y4 ,Ze,MvPolynomial.optionEquivLeft_X_none]
private theorem b7e {R:Type*} [GB R] (i:Fin 3) :
  adT R (nI i.castSucc)=qm (nI i) := by
 simp [adT]
theorem cWO {R:Type*} [GB R] (P:lz (Fin 3) R) :
  adT R (zk xm P)=qm P:= by
 have h: (adT R).toRingHom.comp (zk xm).toRingHom =
    Polynomial.C:= by
  apply FV
  · intro a
    simp [b7d]
  · intro i
    simp [b7e]
 exact yU h P
private theorem eun {R:Type*} [GB R] (F:lz (Fin 4) R) :
  (adT R F).natDegree=F.degreeOf (yJ 3) := by
 change (Wl R (Fin 3) (zk SD F)).natDegree= _
 rw [MvPolynomial.natDegree_optionEquivLeft,← Ze,
  MvPolynomial.degreeOf_rename_of_injective finSuccEquivLast.injective]
def ZW (y :oe) :n5[X] →+* cH :=
 zqg (oy (y ∘ xm)) (y (yJ 3))
theorem c4K (y :oe) :
   (ZW y).comp (adT cH).toRingHom=oy y := by
 apply FV
 · intro a
   simp [ZW,b7d]
 · intro i
   refine Fin.lastCases ?_ (fun j => ?_) i
   · simp [ZW,cWN]
   · simp [ZW,b7e]
def YO (f :af 4) :n5[X] :=
 adT cH (ay7 f)
private theorem Yk :qz qY :=
 (lJ iP cH).injective.comp (GF ao[X] iP)
private theorem gHf (f :af 4) :
  (YO f).natDegree=(shape f).t:= by
 change (adT cH (z9 qY f)).natDegree =
  f.degreeOf (yJ 3)
 rw [eun,zXj,zXj,
  MvPolynomial.support_map_of_injective _ Yk]
theorem gHg {f :af 4} {S:ao[X]} (hf :Dd f S) :
   ZW (zq S) (YO f)=0:= by
 change ((ZW (zq S)).comp (adT cH).toRingHom)
   (ay7 f)=0
 rw [c4K,ay7,znM]
 change Bf qY (fun i:Fin 4=>qY (jet S i)) f=0
 rw [show Bf qY
     (fun i:Fin 4=>qY (jet S i)) f=qY (cK f S) from
   (Te f (GR _) qY (jet S)).symm,
   hf.1,pQ]
theorem bPz {f :af 4} {S:ao[X]} (hf :Dd f S) :
    oy (Ud S) (YO f).leadingCoeff≠0:= by
  have h: (vG (oy (Ud S))).comp
      ((adT cH).toRingHom.comp (z9 qY)) =
    (vG qY).comp
      (Au qm
        (fun i:Fin 4=>if i=3 then Kv else qm (jet S i))) := by
    apply FV
    · intro a
      simp [b7d]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [cWN,show yJ 3=(3:Fin 4) by decide]
      · have hj:j.castSucc≠(3:Fin 4) :=JK j
        simp [b7e,hj,Ud,jet]
  rw [PD,gHf]
  have hc:=qy (fun p:cH[X]=>p.coeff (shape f).t) (yU h f)
  change ((YO f).map (oy (Ud S))).coeff (shape f).t =
    ((Bf qm
      (fun i:Fin 4=>if i=3 then Kv else qm (jet S i)) f).map
      qY).coeff (shape f).t at hc
  rw [Ee,Ee] at hc
  rw [hc]
  exact (WW _ Yk).mpr hf.2
end
end aKu
end
section
namespace aKu
open Polynomial aR wH Tx
noncomputable section
def aVJ:n5 →+* gQ :=
 (zk xm).toRingHom
abbrev aho (f :af 4) :=bRQ (YO f)
def bqZ (f :af 4) :gQ →+* zd (YO f) :=
 (MK (YO f)).comp (adT cH).toRingHom
def qR (f :af 4) :gQ →+* aho f :=
 (lJ (zd (YO f)) (aho f)).comp (bqZ f)
theorem bWW (f :af 4) :
   (qR f).comp aVJ=lJ n5 (aho f) := by
 apply zh
 intro x
 change lJ (zd (YO f)) (aho f)
   (MK (YO f)
     (adT cH (zk xm x)))= _
 rw [cWO]
 rfl
theorem dH6 (f :af 4) :qR f (ay7 f)=0:= by
 change lJ (zd (YO f)) (aho f)
  (MK (YO f) (YO f))=0
 rw [AdjoinRoot.mk_self,pQ]
theorem cXx (f :af 4) (P Q:af 3) :
  xJ f P Q=cy {ay7 f} ⊔ (Ib P Q).map aVJ:= by
 rw [Ib,uz ,← Ideal.span_union,Set.image_pair,
  Set.singleton_union]
 rfl
theorem bWX (f :af 4) (P Q:af 3) :
  (xJ f P Q).map (qR f)=(Ib P Q).map (lJ n5 (aho f)) := by
 rw [cXx,uW,uz ,vZ,dH6,
  Ideal.span_singleton_zero,bot_sup_eq,z7,bWW]
private theorem enA (f :af 4) :
   p9 (bqZ f)=cy {ay7 f} := by
 let e :=(adT cH).toRingEquiv
 change p9 ((mD (cy {YO f})).comp e.toRingHom)= _
 rw [← G4 ,Ideal.mk_ker,
   show ({YO f} : Set n5[X])=e.toRingHom '' {ay7 f} by
     simp [e,YO],
   ← uz ,zFA e.toRingHom e.bijective]
theorem b56 (f :af 4) :
   t7 (bqZ f) :=
 (AdjoinRoot.mk_surjective (g:=YO f)).comp (adT cH).surjective
private theorem dII {f :af 4} {P Q:af 3} {p:aU (aho f)}
   (hp:p∈((xJ f P Q).map (qR f)).minimalPrimes) :
   p.comap (qR f)∈(xJ f P Q).minimalPrimes := by
 let F:=YO f
 let J:=xJ f P Q
 let v :=bqZ f
 let k :=lJ (zd F) (aho f)
 have hk :p.comap k∈(J.map v).minimalPrimes := by
   change p∈Ideal.under (zd F) ⁻¹' (J.map v).minimalPrimes
   rw [← zMt (Submonoid.powers (Kz F F.leadingCoeff)),
     z7]
   exact hp
 have hm:=X8 (b56 f) hk
 have hker :p9 v≤J:= by
   change p9 (bqZ f)≤xJ f P Q
   rw [enA,cXx]
   exact p6
 change (p.comap k).comap v∈J.minimalPrimes
 rwa [G5 v (b56 f),
   ← RingHom.ker_eq_comap_bot,sup_eq_left.mpr hker] at hm
private theorem dIM {f :af 4} {S:ao[X]} (hf :Dd f S) :
   ∃ ev :aho f →+* cH,ev.comp (qR f)=oy (zq S) := by
 let F:=YO f
 let y :=zq S
 let x :=oy (Ud S)
 let z :=y (yJ 3)
 have hz :F.eval₂ x z=0:=gHg hf
 let v :zd F →+* cH :=AdjoinRoot.lift x z hz
 have hunit :uh (v (Kz F F.leadingCoeff)) := by
   change uh (AdjoinRoot.lift x z hz (Kz F F.leadingCoeff))
   rw [AdjoinRoot.lift_of]
   exact isUnit_iff_ne_zero.mpr (bPz hf)
 let ev :aho f →+* cH :=ztx _ hunit
 refine ⟨ev,?_⟩
 rw [← c4K y]
 apply zh
 intro G
 change ev (lJ (zd F) (aho f)
   (MK F (adT cH G))) =
     ZW y (adT cH G)
 rw [show ∀ t,ev (lJ (zd F) (aho f) t)=v t from
   zaz _ _]
 exact AdjoinRoot.lift_mk hz _
private theorem dIx (S:ao[X]) :
  (oy (zq S)).comp aVJ=oy (Ud S) := by
 apply zh
 intro x
 exact ZJ xm (zq S) x
theorem d3W {f :af 4} {P Q:af 3} {S:ao[X]}
   (hf :Dd f S) {q:nq n5}
   (hq:q.asIdeal∈(Ib P Q).minimalPrimes) (hy :q.asIdeal≤oF (Ud S)) :
   ∃ p:nq (aho f),p.asIdeal.LiesOver q.asIdeal ∧
     p.asIdeal.comap (qR f)∈(xJ f P Q).minimalPrimes ∧
     p.asIdeal.comap (qR f)≤Ol (zq S) := by
 let D:=aho f
 have hlead:=bPz hf
 let:Pc n5 D:=cW4 _ (fun h=>hlead (by rw [h,pQ]))
 obtain ⟨ev,hev⟩:=dIM hf
 let M:=p9 ev
 have :M.IsPrime :=Oc ev
 have : (oF (Ud S)).IsPrime :=Oc _
 have :M.LiesOver (oF (Ud S)) :=⟨by
   change p9 (oy (Ud S)) =
     (p9 ev).comap (lJ n5 D)
   rw [G4 ,← bWW,← RingHom.comp_assoc,hev,dIx]⟩
 obtain ⟨p₀,hp₀M,hp₀,hover⟩:=Ideal.exists_ideal_le_liesOver_of_le
   (p:=q.asIdeal) (q:=oF (Ud S)) M hy
 let J:=(xJ f P Q).map (qR f)
 have hJ:J≤p₀:= by
   change (xJ f P Q).map (qR f)≤p₀
   rw [bWX,JQ]
   change Ib P Q≤p₀.under n5
   rw [← hover.over]
   exact hq.le
 obtain ⟨p,hp,hpp₀⟩:=Cy hJ
 have hc:p.under n5=q.asIdeal:= by
   have hle :p.under n5≤q.asIdeal:=(xu hpp₀).trans_eq hover.over.symm
   have hpair :Ib P Q≤p.under Lower := by
     rw [Ideal.under_def,← JQ,← bWX]
     exact hp.le
   exact sS hle (hq.2 ⟨hp.isPrime.comap _,hpair⟩ hle)
 refine ⟨⟨p,hp.isPrime⟩,⟨hc.symm⟩,dII hp,?_⟩
 change p.comap (qR f)≤p9 (oy (zq S))
 rw [← hev,← G4]
 exact xu (hpp₀.trans hp₀M)
private theorem d2r {k :Type*} [uJ k] :
    ∀ n (y :Fin n→k),(p9 (oy y)).height=n:= by
  intro n
  induction n with
  | zero =>
    intro y
    rw [show p9 (oy y) = ⊥ by
      ext G
      simp only [RingHom.mem_ker,Ideal.mem_bot]
      constructor
      · obtain ⟨a,rfl⟩:=(MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.surjective G
        simp
      · rintro rfl; simp]
    simp
  | succ n ih =>
    intro y
    let e :=MvPolynomial.finSuccEquiv k n
    let l:=oy (fun i:Fin n=>y i.succ)
    let v :=zqg l (y 0)
    have hv :v.comp e.toRingHom=oy y := by
      apply zh
      intro G
      change Polynomial.eval₂ l (y 0) (e G)=oy y G
      rw [← Polynomial.eval_map,← MvPolynomial.eval_eq_eval_mv_eval']
      exact qy (fun z=>oy z G) (Fin.cons_self_tail y)
    let p:=p9 l
    let M:=p9 v
    have :M.IsMaximal:=RingHom.ker_isMaximal_of_surjective v (fun a =>
      ⟨qm (p7 a),by simp [v,l]⟩)
    have :M.LiesOver p:=⟨by
      change p9 l=(p9 v).comap qm
      rw [G4 ,show v.comp qm=l from Polynomial.eval₂RingHom_comp_C _ _]⟩
    rw [← hv,← G4]
    change (M.comap e.toRingEquiv).height= _
    rw [e.toRingEquiv.height_comap,Polynomial.height_eq_height_add_one p M,
      show p.height=n from ih _]
    simp
theorem ds7 {f :af 4} {P Q:af 3} {S:ao[X]}
    (hf :Dd f S) {q:nq n5} (hq:q.asIdeal.height=2)
    (hy :q.asIdeal≤oF (Ud S)) {r :nq gQ}
    (hr :r.asIdeal∈(xJ f P Q).minimalPrimes)
    (hle :r.asIdeal≤Ol (zq S))
    (hc:r.asIdeal.comap aVJ=q.asIdeal) :
    r.asIdeal.height=3∧r.asIdeal<Ol (zq S) := by
  let e :=(adT cH).toRingEquiv
  let I:aU n5[X] :=q.asIdeal.map qm
  let J:=I.comap e.toRingHom
  have :I.IsPrime :=Ideal.isPrime_map_C_of_isPrime
  have :J.IsPrime :=Ideal.IsPrime.comap _
  have he :e.toRingHom.comp aVJ=Polynomial.C:= by
    apply zh
    exact cWO
  have hd:I.under n5=q.asIdeal:= by
    ext x
    change qm x∈q.asIdeal.map qm↔x∈q.asIdeal
    constructor
    · exact fun h=> by simpa using Ideal.mem_map_C_iff.mp h 0
    · exact yL _
  have hJheight:q.asIdeal.height≤J.height:= by
    change _≤(I.comap e).height
    rw [e.height_comap,← hd]
    exact zJf (R:=n5) I
  have hJ:J=q.asIdeal.map aVJ:= by
    change (q.asIdeal.map qm).comap e.toRingHom= _
    rw [← he,← z7,zFA e.toRingHom e.bijective]
  have hJle :J≤ r.asIdeal:= by
    rw [hJ,JQ,hc]
  have hproper :J< r.asIdeal:= by
    refine wA hJle (fun h => ?_)
    have hmem:YO f∈I:= by
      change ay7 f∈J
      rw [h]
      exact hr.le (Re (by simp))
    have ha : (YO f).leadingCoeff∈q.asIdeal:=Ideal.mem_map_C_iff.mp hmem _
    exact bPz hf (RingHom.mem_ker.mp (hy ha))
  have hlow: (3:ℕ∞)≤ r.asIdeal.height:= by
    have h:q.asIdeal.height+1≤J.height+1 := by gcongr
    have h' := h.trans (Mk hproper)
    rw [hq] at h'
    rw [show (3:ℕ∞)=2+1 by decide]
    exact h'
  have hu:r.asIdeal.height≤3:= by
    have hcard: ({ay7 f,vY P,vY Q} : Set gQ).ncard≤3 :=
      (zGl _ _).trans (by
        simpa using Nat.succ_le_succ (zGl (vY P) {vY Q}))
    exact (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hr).trans (by
      exact_mod_cast hcard)
  have ht:=sS hu hlow
  refine ⟨ht,wA hle (fun h => ?_)⟩
  have hpt: (Ol (zq S)).height=4 :=d2r 4 _
  rw [h,hpt] at ht
  exact (by decide : (4 :ℕ∞)≠3) ht
end
end aKu
end
section
namespace aRW
noncomputable section
open aR wH Tx MvPolynomial
open scoped Pointwise
def amK (H :lI) :Set (Fin 4 →₀ ℕ) :=
 {m | m.degree≤H.b∧m.sum (fun i a=>i.val*a)≤H.j∧m 3≤H.t}
instance (H :lI) :qU (amK H) :=
 ((XJ H.b).subset
   (fun _ h=>h.1 :amK H ⊆ {m | m.degree≤H.b})).to_subtype
abbrev Gl (H :lI) :=lz (amK H) cH
abbrev bbp (H :lI) :=amK H→cH
abbrev K9 (H :lI) :=vw cH (amK H)
theorem bxg {H :lI} {f :gQ} :
  pC H f↔f∈xI cH (amK H) := by
 rfl
theorem aXu {H :lI} (hH : ∀ i:Fin 4,pC H (nI i))
  (i:Fin 4) :ze i 1∈amK H :=
 bxg.mp (hH i) (by simp)
theorem gxB {H :lI} {F:Gl H} (hF:F.totalDegree≤1) :
  pC H (K9 H F) := by
 have hz : (0:Fin 4 →₀ ℕ)∈amK H := by simp [amK]
 have h:=ZK hz hF
 rw [one_nsmul] at h
 exact bxg.mpr h
theorem b15 {H :lI} (y :oe) (F:Gl H) :
  eval y (K9 H F)=aeval (G2 (amK H) y) F:= by
 simpa only [aeval_eq_eval] using (aeval_monomialPoint y F).symm
theorem cC6 (r :nq gQ) (y :oe) :
  y∈xW cH r.asIdeal↔r.asIdeal≤Ol y := by
 simp only [mem_zeroLocus_iff,aeval_eq_eval,Ol]
 rfl
def a6Z {H :lI} (hH : ∀ i:Fin 4,pC H (nI i)) (z :bbp H) :
    oe := fun i=>z ⟨ze i 1,aXu hH i⟩
theorem c0N {H :lI} (hH : ∀ i:Fin 4,pC H (nI i))
   {r :nq gQ} {z :bbp H}
   (hz :z∈xW cH (r.asIdeal.comap (K9 H))) :
   G2 (amK H) (a6Z hH z)=z := by
 have hle :p9 (K9 H)≤ r.asIdeal.comap (K9 H) :=
   fun f hf=>show K9 H f∈r.asIdeal from
     (RingHom.mem_ker.mp hf).symm ▸ r.asIdeal.zero_mem
 obtain ⟨y,hy⟩:=exists_monomialPoint_eq_of_mem_zeroLocus_ker
   (aXu hH) (zeroLocus_anti_mono hle hz)
 rw [← hy,show a6Z hH (G2 (amK H) y)=y from
   funext fun i=>monomialPoint_single y (aXu hH i)]
private theorem em7 {k σ:Type} [uJ k] [qU σ] :
    ∀ (n:ℕ) (p:nq (lz σ k)),p.asIdeal.height=n →
      (lV p.asIdeal).natDegree+n=Nat.card σ:= by
  intro n
  induction n with
  | zero =>
    intro p hp
    rw [Ideal.height_eq_zero_iff_eq_bot.mp hp,Nat.add_zero,
      natDegree_affineHilbertPolynomial_bot]
  | succ n ih =>
    intro p hp
    have hheight:Order.height p=(n:ℕ∞)+1 := by
      rw [← p.height_eq_orderHeight,hp,Nat.cast_succ]
    obtain ⟨_,⟨q,hqp,hq⟩,hbound⟩:=Order.height_eq_coe_add_one_iff.mp hheight
    have hnot : ¬ p.asIdeal≤q.asIdeal:=not_le_of_gt hqp
    obtain ⟨f,hfp,hfq⟩ : ∃ f,f∈p.asIdeal∧f∉q.asIdeal:= by
      by_contra! h
      exact hnot h
    have hmin:p.asIdeal∈(q.asIdeal ⊔ cy {f}).minimalPrimes := by
      refine ⟨⟨p.isPrime,zc hqp.le ((Ea _).mpr hfp)⟩,?_⟩
      intro J hJ hJp
      by_contra hn
      let j:nq (lz σ k) :=⟨J,hJ.1⟩
      have hjp:j<p:=lt_of_le_not_ge hJp hn
      have hqj:q<j:= by
        refine wA (le_sup_left.trans hJ.2) ?_
        intro heq
        have hjmem:f∈j.asIdeal:=hJ.2 (u9 (th f))
        exact hfq ((qy zyo heq).symm ▸ hjmem)
      have hstep:=Order.height_add_one_le hqj
      rw [hq] at hstep
      have hcontr :=hstep.trans (hbound j hjp)
      norm_cast at hcontr
      omega
    let:=q.isPrime
    have hcut:=C9 hfq hmin
    have hprev :=ih q (q.height_eq_orderHeight.trans hq)
    omega
theorem b1u {H :lI} (hH : ∀ i:Fin 4,pC H (nI i))
  (r :nq gQ) (hr :r.asIdeal.height=3) :
  (lV (r.asIdeal.comap (K9 H))).natDegree=1 := by
 rw [GY (K9 H)
  (Gj (aXu hH))]
 have h:=em7 3 r hr
 rw [R9] at h
 omega
theorem cI1 {σ:Type} [qU σ]
  {I:aU (lz σ cH)} (hp:I.IsPrime)
  (hd: (lV I).natDegree=1) {f :lz σ cH}
  (hf :f∉I) {b:ℕ} (hb:f.totalDegree≤b) :
  (lV (I ⊔ cy {f})).natDegree=0 ∧
    qx (I ⊔ cy {f})≤(b:ℚ)*qx I:= by
 have h:=KI hp hf hb
 have hz : (lV (I ⊔ cy {f})).natDegree=0:= by
  simpa [hd] using h.1
 exact ⟨hz,by simpa [qx ,PD,hd,hz] using h.2⟩
theorem eGs {H :lI} (hH : ∀ i:Fin 4,pC H (nI i))
   (r :nq gQ) (hr :r.asIdeal.height=3) {f :gQ} {T:nX oe}
   (hf :pC H f) (hT:XU.bTw r f T) :
   (T.card:ℚ)≤qx (r.asIdeal.comap (K9 H)) := by
 classical
 let I:=r.asIdeal.comap (K9 H)
 let F:=monomialLift f (bxg.mp hf)
 have hF:K9 H F=f :=monomialMap_monomialLift f (bxg.mp hf)
 have hnot:F∉I:= by
   change K9 H F∉r.asIdeal
   simpa only [hF] using hT.1
 obtain ⟨hd,hdeg⟩:=cI1 (r.isPrime.comap (K9 H))
   (b1u hH r hr) hnot (totalDegree_monomialLift_le_one f (bxg.mp hf))
 obtain ⟨hfinite,hbound⟩:=PA
   (K:=cH) (I ⊔ cy {F}) hd
 let embed:=G2 (E :=cH) (amK H)
 have hsubset : (T.image embed:Set (bbp H)) ⊆
     xW cH (I ⊔ cy {F}) := by
   intro z hz
   obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp (Finset.mem_coe.mp hz)
   obtain ⟨hcurve,hzero⟩:=hT.2 y hy
   apply mem_zeroLocus_sup_span_singleton_iff.mpr
   refine ⟨(Zh (aXu hH) _ _).mpr
     ((cC6 r y).mpr hcurve),?_⟩
   rw [← b15 y F,hF,hzero]
 have hcard:=Set.ncard_le_ncard hsubset hfinite
 rw [Set.ncard_coe_finset,
   Finset.card_image_of_injective _ (monomialPoint_injective (aXu hH))] at hcard
 exact (Nat.cast_le.mpr hcard).trans (hbound.trans (by simpa using hdeg))
end
end aRW
end
section
namespace aRW
noncomputable section
open aR wH Tx MvPolynomial
open ac0 (P5 auW projection aYo
 bxW bJD)
def c1 :Prop :=
  ∀ (σ:Type) [qU σ] (I:aU (lz σ cH)),I.IsPrime →
    (lV I).natDegree=1 →
    ∃ bad:nX (JW cH (σ→cH)),
      (∀ B∈bad,B ≠ ⊤) ∧
      ∀ (a :σ→cH),(∀ B∈bad,a∉B) →
        (projection I a).Finite ∧
        ∀ t:cH,(lV (auW I a t)).natDegree=0 ∧
          qx (auW I a t)=qx I
def c2 :Prop :=
  ∀ (σ:Type) [qU σ] (I:aU (lz σ cH)),I.IsPrime →
    (lV I).natDegree=1 →
    ∃ B:JW cH (σ→cH),B ≠ ⊤ ∧
      ∀ (a :σ→cH),a∉B→(projection I a).Finite →
        ∃ bad:nX cH,∀ t∉bad,(auW I a t).IsRadical
private theorem el8 {H :lI} (hH : ∀ i:Fin 4,pC H (nI i))
   (r :nq gQ) (hr :r.asIdeal.height=3)
   (g:gQ) (hg:g∉r.asIdeal) :
   {z | z∈xW cH (r.asIdeal.comap (K9 H)) ∧
     eval (a6Z hH z) g=0}.Finite := by
 obtain ⟨G,hG⟩:=Gj (aXu hH) g
 let I:=r.asIdeal.comap (K9 H)
 have hGnot:G∉I:= by
   change K9 H G∉r.asIdeal
   rwa [hG]
 have hcut:=(cI1 (r.isPrime.comap (K9 H))
   (b1u hH r hr) hGnot vh).1
 refine (PA
   (K:=cH) (I ⊔ cy {G}) hcut).1.subset ?_
 intro z hz
 refine mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz.1,?_⟩
 rw [← c0N hH (r :=r) hz.1,← b15,hG]
 exact hz.2
theorem of_children (h1 :c1) (h2 :c2) :XU.c1 := by
  classical
  intro H hH R hheight guard hguard cut points hpoints
  let I (r :R) :=r.val.asIdeal.comap (K9 H)
  have hcurve (r :R) : (I r).IsPrime∧(lV (I r)).natDegree=1 :=
    ⟨r.val.isPrime.comap (K9 H),b1u hH r.val (hheight r.val r.property)⟩
  obtain ⟨degreeBad,hdegreeBad⟩:=Classical.skolem.mp fun r :R =>
    h1 (amK H) (I r) (hcurve r).1 (hcurve r).2
  obtain ⟨reduceBad,hreduceBad⟩:=Classical.skolem.mp fun r :R =>
    h2 (amK H) (I r) (hcurve r).1 (hcurve r).2
  let bad:=Finset.univ.biUnion fun r :R=>insert (reduceBad r) (degreeBad r)
  obtain ⟨a,ha⟩:=zsi
    (fun B:bad=>B.val) (by
      intro B
      obtain ⟨r,_,hB⟩:=Finset.mem_biUnion.mp B.property
      rcases Finset.mem_insert.mp hB with h | h
      · rw [h]
        exact (hreduceBad r).1
      · exact (hdegreeBad r).1 _ h)
  have havail (r :R) (B:JW cH (bbp H))
      (hB:B∈insert (reduceBad r) (degreeBad r)) :a∉B :=
    ha ⟨B,Finset.mem_biUnion.mpr ⟨r,FR _,hB⟩⟩
  have hdegree (r :R) :=
    (hdegreeBad r).2 a (fun B hB=>havail r B (Finset.mem_insert_of_mem hB))
  obtain ⟨valueBad,hvalueBad⟩:=Classical.skolem.mp fun r :R =>
    (hreduceBad r).2 a (havail r _ (Finset.mem_insert_self _ _)) (hdegree r).1
  let forbidden (r :R) :=el8 hH r.val (hheight r.val r.property)
    (guard r.val) (hguard r.val r.property)
  let value (z :bbp H) :=aeval z (P5 a)
  let exclusions :=Finset.univ.biUnion fun r :R =>
    valueBad r∪(forbidden r).toFinset.image value
  obtain ⟨t,ht⟩:=Infinite.exists_notMem_finset exclusions
  have htmiss (r :R) :t∉valueBad r∪(forbidden r).toFinset.image value :=
    fun h=>ht (Finset.mem_biUnion.mpr ⟨r,FR _,h⟩)
  let L:=P5 a-MvPolynomial.C t
  let J (r :R) :=auW (I r) a t
  have hfiber (r :R) : (lV (J r)).natDegree=0 ∧
      qx (J r)=qx (I r) :=(hdegree r).2 t
  have hradical (r :R) : (J r).IsRadical :=
    hvalueBad r t (fun h=>htmiss r (Finset.mem_union_left _ h))
  have hproper (r :R) :K9 H L∉r.val.asIdeal:= by
    intro h
    have hL:L∈I r :=h
    have heq :J r=I r :=sup_eq_left.mpr ((Ea _).mpr hL)
    have hz :=(hfiber r).1
    rw [heq,(hcurve r).2] at hz
    omega
  have hfinite (r :R) : (xW cH (J r)).Finite :=
    (PA (K:=cH) _ (hfiber r).1).1
  let Ig (r :nq gQ) :nX oe :=
    if hr :r∈R then (hfinite ⟨r,hr⟩).toFinset.image (a6Z hH) else ∅
  refine ⟨K9 H L,Ig,gxB (bxW a t),?_⟩
  intro r hr
  let q:R:=⟨r,hr⟩
  have hreconstruct {z :bbp H} (hz :z∈xW cH (J q)) :
      G2 (amK H) (a6Z hH z)=z :=
    c0N hH (r :=r) (aYo.mp hz).1
  have hb (y :oe) (hy :y∈Ig r) :
      (r.asIdeal≤Ol y∧eval y (K9 H L)=0) ∧
        eval y (guard r)≠0:= by
    simp only [Ig,Aa hr] at hy
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy
    have hzJ:z∈xW cH (J q) :=(zih _).mp hz
    obtain ⟨hzI,hzt⟩:=aYo.mp hzJ
    refine ⟨⟨?_,?_⟩,?_⟩
    · apply (cC6 r _).mp
      apply (Zh (aXu hH) _ _).mp
      rw [hreconstruct hzJ]
      exact hzI
    · rw [b15,hreconstruct hzJ]
      exact (mem_zeroLocus_sup_span_singleton_iff.mp hzJ).2
    · intro hzero
      exact htmiss q (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨z,(zih _).mpr ⟨hzI,hzero⟩,hzt⟩))
  refine ⟨?_,⟨hproper q,fun y hy=>(hb y hy).1⟩,fun y hy=>(hb y hy).2⟩
  have hinj:Kc (a6Z hH) (xW cH (J q)) := by
    intro z hz w hw heq
    rw [← hreconstruct hz,← hreconstruct hw,heq]
  have hcard: ((Ig r).card:ℚ)=qx (I q) := by
    simp only [Ig,Aa hr]
    change (((hfinite q).toFinset.image (a6Z hH)).card:ℚ)= _
    rw [Finset.card_image_of_injOn (by simpa using hinj),
      ← Set.ncard_eq_toFinset_card _ (hfinite q)]
    exact (bJD (J q) (hfiber q).1 (hradical q)).trans (hfiber q).2
  exact_mod_cast (eGs hH r (hheight r hr) (hpoints r hr).1
    (hpoints r hr).2).trans_eq hcard.symm
theorem dVC (h:ac0.c1) :c1 := by
 intro σ _ I hp hd
 exact h cH σ I hp hd
theorem fVh (hSep:ac0.c2) (hRed:ac0.c3) :c2 := by
 intro σ _ I hp hd
 obtain ⟨B,hB,hSepB⟩:=hSep cH σ I hp hd
 exact ⟨B,hB,fun a ha hfin=>hRed cH σ I hp a hfin (hSepB a ha)⟩
end
end aRW
end
section
namespace bRF
open aR (Dn)
open lB (bF)
open XU (QC nD a2a)
open MeasureTheory Set
noncomputable section
private theorem cvj {n:ℕ} {S:Set (Fin (n+1)→ℝ)}
    {t:ℝ} {f :ℝ→ℝ} (hS:Mj S) (ht:0≤t)
    (hf :Continuous f) (hn : ∀ z∈Icc 0 t,0≤f z)
    (T:ℝ→Set (Fin n→ℝ))
    (hmem : ∀ z y,Fin.snoc y z∈S↔z∈Icc 0 t∧y∈T z)
    (hT : ∀ z∈Icc 0 t,volume (T z)=Hw (f z)) :
    volume S=Hw (∫ z in (0:ℝ)..t,f z) := by
  let e :=MeasurableEquiv.piFinSuccAbove (fun _:Fin (n+1)=>ℝ) (yJ n)
  have he :MeasurePreserving e :=
    volume_preserving_piFinSuccAbove (fun _:Fin (n+1)=>ℝ) (yJ n)
  have hsnoc (z :ℝ) (y :Fin n→ℝ) :e.symm (z,y)=Fin.snoc y z := by
    change Fin.insertNth (α:= fun _=>ℝ) (yJ n) z y= _
    exact Fin.insertNth_last' z y
  have hnonneg:0 ≤ᵐ[(volume :Measure ℝ).restrict (Icc 0 t)] f :=
    (ae_restrict_mem zdy).mono hn
  have hi:IntegrableOn f (Icc 0 t) :=hf.continuousOn.integrableOn_compact isCompact_Icc
  rw [intervalIntegral.integral_of_le ht,← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hi hnonneg,
    ← lintegral_indicator zdy]
  calc
    volume S=volume (e.symm ⁻¹' S) := by
      rw [← e.symm.map_apply,(he.symm e).map_eq]
    _ = ∫⁻ z,volume (Prod.mk z ⁻¹' (e.symm ⁻¹' S)) := by
      exact Measure.prod_apply (e.symm.measurable hS)
    _ = _:= by
      apply lintegral_congr
      intro z
      by_cases hz :z∈Icc 0 t
      · have hsec:Prod.mk z ⁻¹' (e.symm ⁻¹' S)=T z := by
          ext y
          change e.symm (z,y)∈S↔y∈T z
          simp only [hsnoc,hmem,hz,true_and]
        rw [hsec,hT z hz,indicator_of_mem hz]
      · have hsec:Prod.mk z ⁻¹' (e.symm ⁻¹' S) = ∅ := by
          ext y
          change e.symm (z,y)∈S↔y∈(∅ : Set (Fin n→ℝ))
          simp only [hsnoc,hmem,hz,false_and,mem_empty_iff_false]
        rw [hsec,measure_empty,indicator_of_notMem hz]
private theorem cVq (a b c d t:ℝ) :
    (∫ x in (0:ℝ)..t,a+b*x+c*x^2+d*x^3) =
      a*t+b*t^2/2+c*t^3/3+d*t^4/4 := by
  have hcont:Continuous (fun x :ℝ=>a+b*x+c*x^2+d*x^3) := by
    fun_prop
  have hD (x :ℝ) :
      HasDerivAt (fun x=>a*x+b*x^2/2+c*x^3/3+d*x^4/4)
        (a+b*x+c*x^2+d*x^3) x := by
    have hx :=hasDerivAt_id' x
    convert (((hx.const_mul a).add (((hx.pow 2).const_mul b).div_const 2)).add
      (((hx.pow 3).const_mul c).div_const 3)).add (((hx.pow 4).const_mul d).div_const 4)
      using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>hD x)
    (hcont.intervalIntegrable _ _)]
  ring
private theorem bq9 (a b t:ℝ) :
  (∫ x in (0:ℝ)..t,a+b*x)=a*t+b*t^2/2 := by
 simpa only [zi ,zero_div,v8] using cVq a b 0 0 t
private def cah (b:ℝ) :Set (Fin 1→ℝ) :=
 {x | x 0∈Icc 0 b}
private theorem eGM (b:ℝ) :volume (cah b)=Hw b:= by
 let e :=MeasurableEquiv.funUnique (Fin 1) ℝ
 have he :MeasurePreserving e :=volume_preserving_funUnique (Fin 1) ℝ
 have hS:cah b=e ⁻¹' Icc 0 b:=rfl
 rw [hS,← e.map_apply,he.map_eq,Real.volume_Icc,sub_zero]
private def bPr (b j:ℝ) :Set (Fin 2→ℝ) :=
 {x | 0≤x 0∧0≤x 1∧x 0 + x 1≤b∧x 1≤j}
private theorem gE0 {b j:ℝ} (hj:0≤j) (hjb:j≤b) :
    volume (bPr b j)=Hw (b*j - j^2/2) := by
  have hS:Mj (bPr b j) := by
    unfold bPr
    measurability
  have hvol:=cvj hS hj (f := fun x=>b - x)
    (by fun_prop) (fun x hx=>sub_nonneg.mpr (hx.2.trans hjb))
    (fun x=>cah (b - x)) ?_ (fun x _=>eGM (b - x))
  · rw [hvol]
    congr 1
    calc
      (∫ x in (0:ℝ)..j,b - x) = ∫ x in (0:ℝ)..j,b+(-1)*x := by
        apply P7
        intro x _
        ring
      _=b*j - j^2/2 := by rw [bq9]; ring
  · intro z x
    change (0≤x 0∧0≤z∧x 0+z≤b∧z≤j) ↔
      (0≤z∧z≤j)∧0≤x 0∧x 0≤b - z
    constructor
    · rintro ⟨hx,hz,hb,hj'⟩
      exact ⟨⟨hz,hj'⟩,hx,by linarith⟩
    · rintro ⟨⟨hz,hj'⟩,hx,hb⟩
      exact ⟨hx,hz,by linarith,hj'⟩
private def bOS (b j:ℝ) :Set (Fin 3→ℝ) :=
 {x | 0≤x 0∧0≤x 1∧0≤x 2 ∧
   x 0 + x 1 + x 2≤b∧x 1+2*x 2≤j}
private theorem gBw {b j:ℝ} (hj:0≤j) (hjb:j≤b) :
    volume (bOS b j)=Hw (j^2*(2*b - j)/8) := by
  have hS:Mj (bOS b j) := by
    unfold bOS
    measurability
  have hvol:=cvj hS (show 0≤j/2 by linarith)
    (f := fun x=>(b - j/2)*(j - 2*x)) (by fun_prop)
    (fun x hx=>XG  (by linarith) (by linarith [hx.2]))
    (fun x=>bPr (b - x) (j - 2*x)) ?_ ?_
  · rw [hvol]
    congr 1
    calc
      (∫ x in (0:ℝ)..(j/2),(b - j/2)*(j - 2*x)) =
          ∫ x in (0:ℝ)..(j/2),(b - j/2)*j+(-2*(b - j/2))*x := by
        apply P7
        intro x _
        ring
      _=j^2*(2*b - j)/8:= by rw [bq9]; ring
  · intro z x
    change (0≤x 0∧0≤x 1∧0≤z∧x 0 + x 1+z≤b∧x 1+2*z≤j) ↔
      (0≤z∧z≤j/2)∧0≤x 0∧0≤x 1 ∧
        x 0 + x 1≤b - z∧x 1≤j - 2*z
    constructor
    · rintro ⟨h0,h1,hz,hb,hj'⟩
      exact ⟨⟨hz,by linarith⟩,h0,h1,by linarith,by linarith⟩
    · rintro ⟨⟨hz,_⟩,h0,h1,hb,hj'⟩
      exact ⟨h0,h1,hz,by linarith,by linarith⟩
  · intro z hz
    rw [gE0 (show 0≤j - 2*z by linarith [hz.2])
      (show j - 2*z≤b - z by linarith [hz.1])]
    congr 1
    ring
private theorem cDU (p:lI) (x :QC) :
    x∈nD p ↔
      0≤x 0∧0≤x 1∧0≤x 2∧0≤x 3∧x 0 + x 1 + x 2 + x 3≤p.b ∧
        x 1+2*x 2 + 3*x 3≤p.j∧x 3≤p.t:= by
  have h:x∈nD p↔(∀ i,0≤x i)∧x 0 + x 1 + x 2 + x 3≤p.b ∧
      x 1+2*x 2 + 3*x 3≤p.j∧x 3≤p.t:= by
    norm_num [nD,JM]
  rw [h]
  constructor
  · rintro ⟨hx,hb,hj,ht⟩
    exact ⟨hx 0,hx 1,hx 2,hx 3,hb,hj,ht⟩
  · rintro ⟨h0,h1,h2,h3,hb,hj,ht⟩
    refine ⟨?_,hb,hj,ht⟩
    intro i
    fin_cases i <;> assumption
private def a8A (b j z :ℝ) :ℝ:=(j-3*z)^2*(2*b - j+z)/8
private theorem dFd (p:lI) (hp:bF p) :
    a2a (nD p) =
      ∫ z in (0:ℝ)..(p.t:ℝ),a8A p.b p.j z := by
  have hjb: (p.j:ℝ)≤p.b:= by exact_mod_cast hp.1
  have hjt:3*(p.t:ℝ)≤p.j:= by exact_mod_cast hp.2
  have ht: (0:ℝ)≤p.t:=Pf _
  have hS:Mj (nD p) := by
    have heq :nD p = {x :QC |
        0≤x 0∧0≤x 1∧0≤x 2∧0≤x 3∧x 0 + x 1 + x 2 + x 3≤p.b ∧
          x 1+2*x 2 + 3*x 3≤p.j∧x 3≤p.t} := by
      ext x
      exact cDU p x
    rw [heq]
    measurability
  have hnonneg (z :ℝ) (hz :z∈Icc 0 (p.t:ℝ)) :0≤a8A p.b p.j z := by
    exact NW (XG (sq_nonneg _) (by linarith [hz.1])) (by norm_num)
  have hVol:=cvj hS ht (f :=a8A p.b p.j)
    (by unfold a8A; fun_prop) hnonneg
    (fun z=>bOS ((p.b:ℝ) - z) ((p.j:ℝ)-3*z)) ?_ ?_
  · rw [a2a,hVol,ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg ht hnonneg)]
  · intro z x
    rw [cDU]
    change (0≤x 0∧0≤x 1∧0≤x 2∧0≤z∧x 0 + x 1 + x 2+z≤p.b ∧
        x 1+2*x 2 + 3*z≤p.j∧z≤p.t) ↔
      (0≤z∧z≤p.t)∧0≤x 0∧0≤x 1∧0≤x 2 ∧
        x 0 + x 1 + x 2≤(p.b:ℝ) - z∧x 1+2*x 2≤(p.j:ℝ)-3*z
    constructor
    · rintro ⟨h0,h1,h2,hz,hb,hj,ht'⟩
      exact ⟨⟨hz,ht'⟩,h0,h1,h2,by linarith,by linarith⟩
    · rintro ⟨⟨hz,ht'⟩,h0,h1,h2,hb,hj⟩
      exact ⟨h0,h1,h2,hz,by linarith,by linarith,ht'⟩
  · intro z hz
    rw [gBw (show 0≤(p.j:ℝ)-3*z by linarith [hz.2])
      (show (p.j:ℝ)-3*z≤(p.b:ℝ) - z by linarith [hz.1])]
    congr 1
    unfold a8A
    ring
theorem proof :XU.c4 := by
  intro p hp
  rw [dFd p hp,← intervalIntegral.integral_const_mul]
  let b:ℝ:=p.b
  let j:ℝ:=p.j
  let t:ℝ:=p.t
  calc
    (∫ z in (0:ℝ)..t,32*a8A b j z) =
        ∫ z in (0:ℝ)..t,(8*b*j^2 - 4*j^3) +
          (-48*b*j+28*j^2)*z+(72*b-60*j)*z^2 + 36*z^3:= by
      apply P7
      intro z _
      unfold a8A
      ring
    _ = _:= by
      rw [cVq]
      push_cast [Dn]
      dsimp only [b,j,t]
      ring
end
end bRF
end
section
namespace bzM
noncomputable section
open Tx XU
open scoped BigOperators
private theorem d36 (J:aU gQ) (r :nq gQ)
    (hr :r.asIdeal∈J.minimalPrimes) :
    ∃ b:gQ,b∉r.asIdeal ∧ ∀ q∈J.minimalPrimes,q≠r.asIdeal→b∈q:= by
  classical
  have hchoose (q:aU gQ) :
      ∃ x :gQ,x∉r.asIdeal∧(q∈J.minimalPrimes→q≠r.asIdeal→x∈q) := by
    by_cases hq:q∈J.minimalPrimes∧q≠r.asIdeal
    · have hn : ¬ q≤ r.asIdeal:= fun hle=>hq.2 (hle.antisymm (hr.2 hq.1.1 hle))
      obtain ⟨x,hx,hxr⟩:=Set.not_subset.mp hn
      exact ⟨x,hxr,fun _ _=>hx⟩
    · exact ⟨1,r.asIdeal.ne_top_iff_one.mp r.isPrime.ne_top,fun h hne=>(hq ⟨h,hne⟩).elim⟩
  choose x hx using hchoose
  let t:=J.finite_minimalPrimes_of_isNoetherianRing
  refine ⟨∏ q∈t.toFinset,x q,?_,?_⟩
  · have hprod (s :nX (aU gQ)) : (∏ q∈s,x q)∉r.asIdeal:= by
      induction s using zcw with
      | empty=>simpa using r.asIdeal.ne_top_iff_one.mp r.isPrime.ne_top
      | insert q s hqs ih =>
        rw [Finset.prod_insert hqs]
        exact fun h=>(r.isPrime.mem_or_mem h).elim (hx q).1 ih
    exact hprod t.toFinset
  · intro q hq hqr
    exact q.prod_mem (t.mem_toFinset.mpr hq) ((hx q).2 hq hqr)
private theorem emA (q:aU gQ) [q.IsPrime] :q.height≤4 := by
 have h:=ztp (I:=q)
 have hd:Gn gQ=4 := by
  rw [zmx,zZT]
  simp
 rw [hd] at h
 exact WithBot.coe_le_coe.mp h
private theorem eph {J:aU gQ} {r p:nq gQ} {b D:gQ}
  (hr :r.asIdeal∈J.minimalPrimes) (hh:r.asIdeal.height=3)
  (hb : ∀ q∈J.minimalPrimes,q≠r.asIdeal→b∈q)
  (hrp:r.asIdeal≤p.asIdeal) (hbp:b∉p.asIdeal)
  (hD:D∉r.asIdeal) (hDp:D∈p.asIdeal) :
  p.asIdeal∈(ke J D).minimalPrimes := by
 have hcut:ke J D ≤p.asIdeal :=
  zc (hr.le.trans hrp) ((Ea _).mpr hDp)
 refine ⟨⟨p.isPrime,hcut⟩,?_⟩
 intro q hq hqp
 let:q.IsPrime :=hq.1
 have hJq:J≤q:=le_sup_left.trans hq.2
 obtain ⟨s,hs,hsq⟩:=Cy hJq
 have hsr :s=r.asIdeal:= by
  by_contra h
  exact hbp (hqp (hsq (hb s hs h)))
 have hrq:r.asIdeal≤q:=hsr ▸ hsq
 have hDq:D∈q:=hq.2 (u9 (th D))
 have hrlt:r.asIdeal<q:=wA hrq (fun h=>hD (h ▸ hDq))
 have hfour : (4 :ℕ∞)≤q.height:= by
  have h:=Mk hrlt
  rw [hh] at h
  exact h
 have heq :q=p.asIdeal :=
  zKE q hqp ((emA p.asIdeal).trans hfour)
 exact heq.ge
theorem proof :XU.c2 := by
 intro J r hr hh _
 obtain ⟨g,hgr,hg⟩:=d43 J r hr
 obtain ⟨b,hbr,hb⟩:=d36 J r hr
 refine ⟨g*b,fun h=>(r.isPrime.mem_or_mem h).elim hgr hbr,
  fun q hq hqr=>q.mul_mem_left g (hb q hq hqr),?_⟩
 intro D hD y hry ha hDy
 let p:=pointPrime y
 have ha' : g*b∉p.asIdeal:=ha
 have hg' : g∉p.asIdeal:= fun h=>ha' (p.asIdeal.mul_mem_right b h)
 have hb' : b∉p.asIdeal:= fun h=>ha' (p.asIdeal.mul_mem_left g h)
 exact ⟨eph hr hh hb hry hb' hD hDy,hg p hry hg' D hD hDy⟩
end
end bzM
end
section
namespace aKu
open Polynomial aR wH Tx
noncomputable section
private theorem dH9 (f :af 4) :
   (qR f).SurjectiveOnStalks := by
 let F:=YO f
 let a :=Kz F F.leadingCoeff
 apply RingHom.SurjectiveOnStalks.comp _ (RingHom.surjectiveOnStalks_of_surjective
   (b56 f))
 apply RingHom.surjectiveOnStalks_of_exists_div
 intro z
 obtain ⟨n,b,hb⟩:=zQH a z
 refine ⟨b,a^n,?_,?_⟩
 · rw [Du]
   exact (IsLocalization.Away.algebraMap_isUnit a).pow n
 · rwa [Du,qG]
private theorem cXO {f :af 4} {P Q:af 3} {r :nq gQ}
    {q:nq n5} (p:nq (aho f)) [p.asIdeal.LiesOver q.asIdeal]
    (hp:p.asIdeal.comap (qR f)=r.asIdeal)
    (ha : (YO f).leadingCoeff≠0) :
    qM q (Ib P Q)≤ajK r (xJ f P Q) := by
  let D:=aho f
  let:Pc n5 D:=cW4 _ ha
  let A:=vH q.asIdeal
  let B:=vH p.asIdeal
  let U:=vH r.asIdeal
  let:wB A B:=Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  have :IsLocalHom (lJ A B) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  let J:=(Ib P Q).map (lJ n5 A)
  let JB:=J.map (lJ A B)
  let G:=(xJ f P Q).map (lJ gQ U)
  let φ:=Localization.localRingHom r.asIdeal p.asIdeal (qR f) hp.symm
  let:wB U B:=φ.toAlgebra
  have hφ:t7 (lJ U B) :=
    (dH9 f).localRingHom_surjective _ _ hp.symm
  have hmap :G≤JB.comap (lJ U B) := by
    have hcomp: (lJ U B).comp (lJ gQ U) =
        (lJ D B).comp (qR f) :=
      zh (Localization.localRingHom_to_map _ _ _ hp.symm)
    rw [← JQ]
    change ((xJ f P Q).map (lJ gQ U)).map (lJ U B)≤JB
    rw [z7,hcomp,← z7,bWX,z7,
      ← MO n5 D B]
    change _≤((Ib P Q).map (lJ n5 A)).map (lJ A B)
    rw [z7,← MO n5 A B]
  let ψ:=WX JB (Algebra.ofId U B) hmap
  have hψ:t7 ψ:= by
    change t7 (X4 JB (lJ U B) hmap)
    exact Ideal.quotientMap_surjective hφ
  have hlength:p5 B (B ⧸ JB)≤p5 U (U ⧸ G) := by
    rw [← Module.length_eq_of_surjective (M:=B ⧸ JB) hφ]
    exact Module.length_le_of_surjective ψ.toLinearMap hψ
  have hproper :=IsLocalRing.map_maximalIdeal_lt_top (lJ A B)
  have :Nontrivial (B ⧸ (u8 A).map (lJ A B)) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper.ne
  have hpos :=Zt (R:=B)
    (M:=B ⧸ (u8 A).map (lJ A B))
  have hl:p5 B (B ⧸ JB)=p5 B (TensorProduct A B (A ⧸ J)) :=
    (UP B J).toLinearEquiv.length_eq
  rw [IsLocalRing.length_baseChange] at hl
  exact (ENat.self_le_mul_right _ hpos.ne').trans (hl.ge.trans hlength)
private theorem cXN {r :nq gQ} {I:aU gQ}
    (hr :r.asIdeal∈I.minimalPrimes) :ajK r I < ⊤ := by
  let A:=vH r.asIdeal
  let L:=I.map (lJ gQ A)
  have hmin:u8 A∈L.minimalPrimes := by
    change u8 A∈(I.map (lJ gQ A)).minimalPrimes
    rw [zMt r.asIdeal.primeCompl A,Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A r.asIdeal]
    exact hr
  have :IsArtinianRing (A ⧸ L) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing L hmin
  exact lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L,isArtinian_of_surjective_algebraMap
        (zf (I:=L))⟩))
end
end aKu
end
