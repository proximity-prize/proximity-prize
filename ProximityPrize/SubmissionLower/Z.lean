import ProximityPrize.SubmissionLower.AG
set_option Elab.async false
open _root_ renaming AddMonoidAlgebra.coeff_zero→ In,AdjoinRoot→NW,AdjoinRoot.mk→sH,AdjoinRoot.mk_self→Te,AdjoinRoot.mk_surjective→Xp,AdjoinRoot.modByMonicHom_mk→Nq,AdjoinRoot.powerBasis'→XJ,AdjoinRoot.powerBasisAux'→JQ,AdjoinRoot.powerBasisAux'_repr_apply_to_fun→SC,AlgEquiv.apply_symm_apply→LR,Algebra.algebraMap→cy,Algebra.leftMulMatrix→R9,Algebra.leftMulMatrix_eq_repr_mul→SW,Algebra.leftMulMatrix_mulVec_repr→X4,Algebra.smul_def→yB,CommMonoid→Kl,CommRing→ oD,CommSemiring→c9,Commute.all→Aa,DFunLike.congr_fun→t6,DecidableEq→wA,Field→lI,Fin.ext→zm,Fin.prod_univ_succ→S1,Fin.succ→G1,Fin.sum_univ_eq_sum_range→zf,Fin.sum_univ_two→FQ,Finset→pC,Finset.HasAntidiagonal.mem_antidiagonal→Nj,Finset.dvd_sum→Gi,Finset.mem_univ→u9,Finset.mul_sum→FR,Finset.range→xL,Finset.single_le_sum→VH,Finset.subset_univ→WK,Finset.sum_apply→Oc,Finset.sum_congr→p7,Finset.sum_eq_single_of_mem→Ok,Finset.sum_eq_zero→t5,Finset.sum_le_sum→Ts,Finset.sum_mul→EP,Finset.sum_range_id→Pk,Finset.sum_range_succ'→Pc,Finset.sum_subset→Un,Finset.sup_le→ IT,Finset.sup_le_iff→TZ,Finset.univ→ Iw,Finsupp.prod_fintype→Rm
open _root_ renaming Finsupp.sum_fintype→G2,Finsupp.zero_apply→Hw,Fintype→p5,Fintype.card→Cy,Fintype.card_coe→Pv,Fintype.card_fin→yJ,Fintype.card_prod→Vz,Fintype.card_sigma→Eg,Fintype.equivFinOfCardEq→LP,Fintype.linearCombination→Du,Fintype.linearCombination_apply→SM,FractionRing→vZ,Function.Injective→uW,IsAlgClosed.splits→KA,IsCoprime→t7,IsFractionRing.injective→qM,IsLocalization.lift→Pr,IsLocalization.lift_comp→JW,IsLocalization.lift_mk'→SL,IsRelPrime→Gk,IsScalarTower.algebraMap_apply→zc,IsScalarTower.toAlgHom→vw,IsUnit.liftRight_apply→Xo,LinearIndependent→C9,LinearIndependent.of_comp→Sv,LinearMap.congr_fun→QL,LinearMap.ker→FU,LinearMap.pi→FV,LinearMap.range→Gr,Matrix→sS,Matrix.det_one→Ob,Matrix.ext→OJ,Matrix.map_apply→KI,Matrix.map_mul→Kc,Matrix.mulVec_cramer→WX,Matrix.mulVec_smul→XB,Matrix.rank_of_det_ne_zero→Mk,Matrix.rank_submatrix_le→RC,Matrix.toLin'_mul→Qy,Mc.Sm→zk,Module→vi,Module.Basis.equivFun_apply→G6,Module.Basis.repr_reindex_apply→XG,Module.Finite→Ea,Module.Finite.of_injective→VO,Module.finrank→xu,MonoidHom.domRestrict_apply→SD,MulZeroClass.mul_zero→vj
open _root_ renaming MvPolynomial→nI,MvPolynomial.C→nq,MvPolynomial.X→nX,MvPolynomial.aeval→uz,MvPolynomial.aeval_monomial→Pf,MvPolynomial.algebraMap_eq→vH,MvPolynomial.coeff_C_mul→Kp,MvPolynomial.coeff_map→G8,MvPolynomial.coeff_monomial→Qw,MvPolynomial.coeff_sum→GF,MvPolynomial.coeff_weightedTruncation→NZ,MvPolynomial.degreeOf_X_pow_of_ne→Wl,MvPolynomial.eval→qx,MvPolynomial.eval_C→RD,MvPolynomial.ext→y5,MvPolynomial.finSuccEquiv→th,MvPolynomial.lcoeff→Wm,MvPolynomial.le_degreeOf_of_mem_support→G9,MvPolynomial.le_totalDegree→UZ,MvPolynomial.map→ oj,MvPolynomial.mapAlgHom→UP,MvPolynomial.map_C→JM,MvPolynomial.map_injective→S2,MvPolynomial.monomial→qz,MvPolynomial.pderiv→qU,MvPolynomial.rename→uh,MvPolynomial.ringHom_ext→Av,MvPolynomial.totalDegree→Xg,MvPolynomial.totalDegree_C→WD,MvPolynomial.totalDegree_finsetSum_le→TI,MvPolynomial.totalDegree_mul→Ww,Nat.choose_eq_zero_of_lt→Xu,Nat.le_of_lt_succ→VC,Nat.lt_succ_of_le→xW,Nat.min_le_left→Kz,Nat.mul_add→PA,Nat.mul_comm→Dv,Nat.mul_le_mul_left→RJ,Pi.zero_apply→Et,Polynomial→lz,Polynomial.C→mD,Polynomial.C_dvd_iff_dvd_coeff→SU,Polynomial.C_mul_X_pow_eq_monomial→Fa,Polynomial.IsRoot→TH,Polynomial.X→aU,Polynomial.coe_eval₂RingHom→zh,Polynomial.coe_mapRingHom→vG,Polynomial.coeff_C_mul→yL
open _root_ renaming Polynomial.coeff_eq_zero_of_natDegree_lt→MK,Polynomial.coeff_map→t9,Polynomial.coeff_mapAlgHom_apply→Mw,Polynomial.coeff_monomial→ze,Polynomial.coeff_natDegree→ IU,Polynomial.coeff_smul→C5,Polynomial.coeff_zero→v8,Polynomial.degree_eq_natDegree→G7,Polynomial.derivative_C→Ef,Polynomial.derivative_add→JK,Polynomial.derivative_map→zi,Polynomial.derivative_mul→yU,Polynomial.evalRingHom→sI,Polynomial.eval_C→Ee,Polynomial.eval₂→qy,Polynomial.eval₂AlgHom→z8,Polynomial.eval₂RingHom→ oy,Polynomial.eval₂_C→pL,Polynomial.eval₂_X→u8,Polynomial.eval₂_algebraMap_X→Qx,Polynomial.eval₂_eq_sum_range→WW,Polynomial.eval₂_monomial→LO,Polynomial.ext→pQ,Polynomial.finsetSum_coeff→wR,Polynomial.induction_on'→Lf,Polynomial.lcoeff→Dz,Polynomial.mapAlgHom→vl,Polynomial.mapRingHom→ oK,Polynomial.map_C→ oZ,Polynomial.map_X→Au,Polynomial.map_add→yl,Polynomial.map_id→Bf,Polynomial.map_map→ oY,Polynomial.map_modByMonic→F9,Polynomial.map_mul→qm,Polynomial.map_pow→Dw,Polynomial.map_sub→Kv,Polynomial.map_sum→UY,Polynomial.map_zero→VS,Polynomial.modByMonic_eq_zero_iff_dvd→Ml,Polynomial.monomial→pz,Polynomial.natDegree_linear→NX,Polynomial.natDegree_map_eq_of_injective→Xx,Polynomial.natDegree_mul_le_of_le→Mj,Polynomial.natDegree_sum_le_of_forall_le→G5,Polynomial.ringHom_ext→p6,Polynomial.ringHom_ext'→zS,Polynomial.smul_eq_C_mul→Ar
open _root_ renaming Polynomial.sum→NY,Polynomial.taylor→EK,Polynomial.taylorAlgHom→PM,PowerSeries→pU,PowerSeries.C→n5,PowerSeries.coeff→zg,PowerSeries.coeff_map→MS,PowerSeries.coeff_rescale→Vq,PowerSeries.coeff_zero_eq_constantCoeff_apply→Up,PowerSeries.constantCoeff→GB,PowerSeries.map→wB,PowerSeries.map_C→Df,PowerSeries.rescale→zE,RingHom.comp_apply→ oq,RingHom.comp_assoc→PD,RingHom.congr_fun→zd,RingHom.ext→xI,RingHom.id→uJ,RingHom.mapMatrix_apply→Vs,Semiring→p9,Set.range→Kh,Submodule→xm,Submodule.span→G4,Submodule.subset_span→RP,Subtype.ext→C4,Units.val_inv_eq_inv_val→Sd,add_zero→u5,congrArg→ oz,congrFun→yo,cu.Shape→lJ,cu.triangle→qJ,dvd_mul_of_dvd_left→Vl,dvd_mul_right→Pj,finTwoArrowEquiv'→P7,gR.Bx.lN→t3,gR.Principal.P8→zR,gR.Principal.aAt→Nr,gR.Principal.ahe→LQ,gR.Principal.assemble→ Il,inv_mul_cancel₀→Mz,ite_eq_left→HZ,ite_eq_right→z9,ite_false→Gj,ite_true→GR,left_ne_zero_of_mul→Re,map_add→ ov,map_dvd→vk,map_mul→lV
open _root_ renaming map_natCast→G3,map_one→vh,map_pow→pG,map_smul→x7,map_sub→Fz,map_sum→qG,map_zero→ ox,min_le_left→ II,mul_add→Gn,mul_assoc→t8,mul_comm→t4,mul_dvd_mul_iff_left→WY,mul_inv_cancel₀→Np,mul_ne_zero→z7,mul_one→FK,mul_pow→GY,nonZeroDivisors→NI,one_mul→wY,pow_add→yQ,pow_ne_zero→N0,smul_mul_assoc→KH,sub_self→J4,zero_add→v9,zero_dvd_iff→MO,zero_ne_one→G0
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace DP
noncomputable section
open K1 cu Polynomial
open scoped BigOperators Polynomial
abbrev qC:=nI (Fin 2) L
abbrev aQ:=vZ qC
abbrev Source :=lz (lz (lz qC))
abbrev US:=lz (lz (lz aQ))
def CI (i:Fin 2) :Fin 2 :=if i=0 then 1 else 0
structure jF (h:ℕ) where
 block :Fin 2→ L[X]
 offset :Fin 2→ L[X]
 constant:Fin 2→ L[X]
 slope :Fin 2→ L[X]
 monic : ∀ i,(block i).Monic
 degree : ∀ i,(block i).natDegree=h
 coprime :t7 (block 0) (block 1)
 determinant : ∀ i,t7 (offset i*constant i) (block i)
def Iy {h} (D:jF h) :L[X] :=D.block 0*D.block 1
structure zG {h:ℕ} (D:jF h) where
 denominator :Fin 2→ L[X]
 numerator :Fin 2→lz L[X]
 denominator_ne_zero : ∀ i,denominator i≠0
 af0 : ∀ i,(numerator i).degree<(2*h:ℕ)
 other_dvd : ∀ i,(D.block (CI i)).map (mD (R:=L))∣numerator i
 congruence : ∀ i,(D.block i).map (mD (R:=L)) ∣
    ((D.constant i).map (mD (R:=L)) +
      (@mD (lz L) _) (aU (R:=L))*(D.slope i).map (mD (R:=L)))*numerator i +
      (@mD (lz L) _) (denominator i*aU)*(D.offset i).map (mD (R:=L))
 regular : ∀ i z,t7 (D.constant i+C z*D.slope i) (D.block i) →
  (denominator i).eval z≠0
def MF (i:Fin 2) :L[X] →ₐ[L] aQ :=
 Polynomial.aeval (cy qC aQ (nX i))
def OY {h} {D:jF h} (Crt:zG D) :aQ[X] :=
 ∑ i,(MF i (Crt.denominator i))⁻¹•(Crt.numerator i).map (MF i)
def pW {R:Type*} [c9 R] :
    R →+* lz (lz R) :=
  C.comp C
private def cVZ {R S A:Type*} [c9 R] [c9 S]
  [c9 A] [Algebra R S] [Algebra R A]
  (base :S →ₐ[R] A) (y v :A) :lz (lz S) →ₐ[R] A :=
 z8 (z8 base y (fun _=>Aa _ _))
  v (fun _=>Aa _ _)
def au5:qC[X] →ₐ[L] aQ[X] :=
 vl (vw L qC aQ)
def IE {h} (D:jF h) :aQ[X] :=
 (Iy D).map (cy L aQ)
def forward {h} {D:jF h} (Crt:zG D) :Source →ₐ[L] US :=
  let H :=IE D
  let lift:=OY Crt
  let c:aQ[X] →+* US:=pW
  let rawOrd:US:=(@mD (lz (lz aQ)) _)
    (aU (R:=lz aQ))
  let rawDeriv :US:=aU
  cVZ (R:=L) (S:=qC[X]) (A:=US)
    ((vw L aQ[X] US).comp au5)
    (c H*rawOrd+c lift) (c H*rawDeriv+c H.derivative*rawOrd+c lift.derivative)
def Km (x r :L) :Source →ₐ[L] Source :=
  let c:qC[X] →+* Source :=pW
  let base :qC[X] →ₐ[L] qC[X] :=
    z8 (vw L qC qC[X])
      (aU (R:=qC)+(@mD qC _) (nq x))
      (fun _=>Aa _ _)
  let η:Source :=(@mD (lz (lz qC)) _)
    (aU (R:=lz qC))
  let deriv :Source :=aU
  cVZ (R:=L) (S:=qC[X]) (A:=Source)
    ((vw L qC[X] Source).comp base)
    (c ((@mD qC _) (nq r))+c (aU (R:=qC))*deriv+η) deriv
def Fg (P:Source) (j i a :ℕ) (e :Fin 2 →₀ ℕ) :L :=
 (((P.coeff j).coeff i).coeff a).coeff e
def Tl (e :Fin 2 →₀ ℕ) :ℕ:=e.sum fun _ n=>n
def awN (h:ℕ) (s :lJ) (W j i a :ℕ) (e :Fin 2 →₀ ℕ) :Prop :=
  i+j≤ s.B∧j≤ s.J∧Tl e≤ s.U ∧
    a+(i+j)*(131071+h)≤W+(s.B+s.J)*(2*h)+j
def Aw (h:ℕ) (s :lJ) (W:ℕ) :xm L Source where
  carrier := {P | ∀ j i a e,¬ awN h s W j i a e→Fg P j i a e=0}
  zero_mem' := by simp [Fg]
  add_mem' := by
    intro P Q hP hQ j i a e he
    have hp:=hP j i a e he
    have hq:=hQ j i a e he
    unfold Fg at hp hq ⊢
    simp [hp,hq]
  smul_mem' := by
    intro b P hP j i a e he
    have hp:=hP j i a e he
    unfold Fg at hp ⊢
    simp [C5 ,hp]
def ad0 (i:I) :L:=cy K L (node i)
def amm (word:I→L) (s :lJ) :xm L Source where
  carrier := {P | ∀ i a b j e,a+2*b<s.m →
    Fg (Km (ad0 i) (word i) P) j b a e=0}
  zero_mem' := by simp [Fg]
  add_mem' := by
    intro P Q hP hQ i a b j e he
    have hp:=hP i a b j e he
    have hq:=hQ i a b j e he
    unfold Fg at hp hq ⊢
    simp [hp,hq]
  smul_mem' := by
    intro b P hP i a k j e he
    have hp:=hP i a k j e he
    unfold Fg at hp ⊢
    simp [C5 ,hp]
def btN {h} {D:jF h} (Crt:zG D) (s :lJ) :xm L Source where
  carrier := {P | (pW ((IE D)^(s.B+s.J)) :US)∣forward Crt P}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    change _∣forward Crt (P+Q)
    rw [ov]
    exact dvd_add hP hQ
  smul_mem' := by
    intro b P hP
    change _∣forward Crt (b•P)
    rw [x7,yB]
    exact dvd_mul_of_dvd_right hP _
def aq7 (h:ℕ) (word:I→L) (s :lJ) (W:ℕ) :xm L Source :=
 Aw h s W ⊓ amm word s
def complete {h} {D:jF h} (Crt:zG D) (word:I→L)
    (s :lJ) (W:ℕ) :xm L Source :=
  aq7 h word s W ⊓ btN Crt s
def U4 :Source →ₐ[L] Jet :=
  let ξ:=cy (lz L) FX (aU (R:=L))
  let base :qC[X] →ₐ[L] aZ :=
    z8 (UP (Algebra.ofId L FX))
      (nq ξ) (fun _=>Aa _ _)
  vl (vl base)
def VY {h} {D:jF h} (Crt:zG D) (word:I→L) :vP :=
 fun s W=>G4 FX (U4 '' (complete Crt word s W:Set Source))
def c69 (h:ℕ) (s :lJ) (W:ℕ) :Prop :=
 ∀ q≤ s.B,∀ j≤ min q s.J,q*(131071-h)≤W+1+j
def ceG (h:ℕ) (s :lJ) (W:ℕ) :ℕ :=
 qJ s.U*ku s (fun q j=>W+1+j - q*(131071-h))
def azS (h:ℕ) (s :lJ) :ℕ :=
 qJ s.U*(2*h)*ku s (fun q _=>s.B+s.J-q)
def bga (s :lJ) :ℕ :=
 qJ s.U*262144*ku s (fun q i=>s.m+min q s.J-(q+2*i))
def Z7 (z :K) :Fin 2→L :=
 ![cy K L z,(cy K L z)^p]
def Tj {h} (D:jF h) (i:Fin 2) (z :L) :L[X] :=
 D.constant i+(@mD L _) z*D.slope i
def aKF {h} (D:jF h) (z :K) (S:K[X]) :Prop :=
  ∀ i,t7 (Tj D i (Z7 z i)) (D.block i) ∧
    D.block i∣Tj D i (Z7 z i)*j9 S +
      (@mD L _) (Z7 z i)*D.offset i
end
end DP
end
section
namespace DP
noncomputable section
open K1 cu Polynomial
open scoped Polynomial
theorem dOu {h} {D:jF h} (Crt:zG D) (word:I→L)
   {s s' : lJ} (hm:s.m=s'.m) (hB:s.B=s'.B) (hJ:s.J=s'.J)
   (hU:s.U≤ s'.U) {W W' : ℕ} (hW:W≤W') :
   complete Crt word s W≤ complete Crt word s' W' := by
 intro P hP
 rcases SetLike.mem_coe.mp hP with ⟨⟨ha,hp⟩,hc⟩
 refine ⟨⟨?_,?_⟩,?_⟩
 · intro j i a e hn
   apply ha j i a e
   intro ⟨hb,hj,hu,hw⟩
   apply hn
   exact ⟨hB ▸ hb,hJ ▸ hj,hu.trans hU,by
     rw [← hB,← hJ]
     omega⟩
 · intro i a b j e he
   exact hp i a b j e (hm ▸ he)
 · change (pW ((IE D)^(s'.B+s'.J)) :US)∣forward Crt P
   rw [← hB,← hJ]
   exact hc
theorem d3q {h} {D:jF h} (Crt:zG D) (word:I→L)
  {s s' : lJ} (hm:s.m=s'.m) (hB:s.B=s'.B) (hJ:s.J=s'.J)
  (hU:s.U≤ s'.U) {W W' : ℕ} (hW:W≤W') :
  VY Crt word s W≤VY Crt word s' W' :=
 Submodule.span_mono (Set.image_mono (dOu Crt word hm hB hJ hU hW))
private def a2f (j i:ℕ) (e :Fin 2 →₀ ℕ) :Jet →ₗ[FX] FX where
 toFun P:=((P.coeff j).coeff i).coeff e
 map_add' P Q:= by simp
 map_smul' b P:= by simp [C5]
private theorem dGs (P:Source) (j i:ℕ) (e :Fin 2 →₀ ℕ)
  (hz : ∀ a,Fg P j i a e=0) :
  a2f j i e (U4 P)=0:= by
 let ξ:=cy (lz L) FX (aU (R:=L))
 let g:=(P.coeff j).coeff i
 change (((U4 P).coeff j).coeff i).coeff e=0
 simp only [U4,Mw]
 change (g.eval₂ (oj (cy L FX)) (nq ξ)).coeff e=0
 rw [Polynomial.eval₂_eq_sum]
 simp only [NY ,GF]
 apply t5
 intro a _
 have he : (g.coeff a).coeff e=0:=hz a
 rw [← pG,t4 ,Kp]
 change ξ^a*(oj (cy L FX) (g.coeff a)).coeff e=0
 rw [G8 ,he,ox ,vj]
private theorem dGt {h} {D:jF h} (Crt:zG D) (word:I→L)
  {s W P} (hP:P∈VY Crt word s W)
  (j i:ℕ) (e :Fin 2 →₀ ℕ) (hf : ¬ (i+j≤ s.B∧j≤ s.J∧Tl e≤ s.U)) :
  a2f j i e P=0:= by
 have hsub:VY Crt word s W≤FU (a2f j i e) :=
  Submodule.span_le.mpr (by
    rintro _ ⟨Q,hQ,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply dGs
    intro a
    exact hQ.1.1 j i a e (fun hh=>hf ⟨hh.1,hh.2.1,hh.2.2.1⟩))
 exact LinearMap.mem_ker.mp (hsub hP)
theorem d3r {h} {D:jF h} (Crt:zG D) (word:I→L)
   {s W P} (hP:P∈VY Crt word s W) (j i:ℕ)
   (hne : ((P.coeff j).coeff i)≠0) :
   i+j≤ s.B∧j≤ s.J∧((P.coeff j).coeff i).totalDegree≤ s.U:= by
 classical
 let g:=(P.coeff j).coeff i
 have he (e) (hes :e∈g.support) :
     i+j≤ s.B∧j≤ s.J∧Tl e≤ s.U:= by
   by_contra hbad
   exact (MvPolynomial.mem_support_iff.mp hes) (dGt Crt word hP j i e hbad)
 obtain ⟨e,heS⟩:=Finset.nonempty_iff_ne_empty.mpr (by simpa [g] using hne :
   g.support ≠ ∅)
 refine ⟨(he e heS).1,(he e heS).2.1,?_⟩
 rw [ Xg ,TZ]
 exact fun a ha=>(he a ha).2.2
end
end DP
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 16
namespace bax
noncomputable section
open K1 cu DP Polynomial
open scoped BigOperators
def adA {A R:Type*} [c9 A] [c9 R]
    (f :A →+* R) (x y v :R) :lz (lz (lz A)) →+* R :=
  oy (oy (oy f x) y) v
def ab3 (t:Fin 2→L) (S:L[X]) :Source →+* L[X] :=
 adA (C.comp (qx t)) aU S S.derivative
theorem bFk {A R:Type*} [c9 A] [c9 R]
  {f g:lz (lz (lz A)) →+* R}
  (hc : ∀ a :A,f (C (C (C a)))=g (C (C (C a))))
  (hx :f (C (C aU))=g (C (C aU)))
  (hy :f (C aU)=g (C aU))
  (hv :f aU=g aU) :f=g:= by
 apply p6 _ hv
 have hbase : (f.comp C).comp C=(g.comp C).comp C :=
  p6 hc hx
 have hinner :f.comp C=g.comp C :=
  p6 (t6 hbase) hy
 exact t6 hinner
@[simp] theorem gPR {A R:Type*} [c9 A] [c9 R]
   (f :A →+* R) (x y v :R) (a :A) :
   adA f x y v (C (C (C a)))=f a := by
  simp [adA]
@[simp] theorem gPP {A R:Type*} [c9 A] [c9 R]
   (f :A →+* R) (x y v :R) :
   adA f x y v (C (C aU))=x := by
  simp [adA]
@[simp] theorem gPQ {A R:Type*} [c9 A] [c9 R]
   (f :A →+* R) (x y v :R) :
   adA f x y v (C aU)=y := by
  simp [adA]
@[simp] theorem gPO {A R:Type*} [c9 A] [c9 R]
   (f :A →+* R) (x y v :R) :
   adA f x y v aU=v := by
  simp [adA]
theorem cMK {A R:Type*} [c9 A] [c9 R]
    (f :A →+* R) (x y v :R) (P:lz (lz (lz A))) :
    adA f x y v P =
      ∑ j∈P.support,(∑ i∈(P.coeff j).support,(∑ a∈((P.coeff j).coeff i).support,
        f (((P.coeff j).coeff i).coeff a)*x^a)*y ^i)*v^j:= by
  simp only [adA,zh,eval₂_eq_sum,NY]
theorem cHz {h:ℕ} {s :lJ} {W:ℕ} {P:Source}
  (hP:P∈Aw h s W) (t:Fin 2→L) (S:L[X])
  (hd:S.natDegree≤131071+h) :
  (ab3 t S P).natDegree≤W+(s.B+s.J)*(2*h) := by
 let d:=131071+h
 change S.natDegree≤d at hd
 have hd' : S.derivative.natDegree≤d-1 :=
  (natDegree_derivative_le S).trans (Nat.sub_le_sub_right hd _)
 have hpred:d-1+1=d:= by dsimp [d]; omega
 rw [ab3,cMK]
 apply G5
 intro j _
 rw [EP]
 apply G5
 intro i _
 rw [EP ,EP]
 apply G5
 intro a ha
 have hne : ((P.coeff j).coeff i).coeff a≠0 :=
  mem_support_iff.mp ha
 have hw:a+(i+j)*d≤W+(s.B+s.J)*(2*h)+j:= by
  by_contra hn
  apply hne
  ext e
  exact hP j i a e (fun he=>hn he.2.2.2)
 refine (Mj (Mj
  (Mj (by simp : (C _:L[X]).natDegree≤0) (by simp : (Polynomial.X ^a :L[X]).natDegree≤a))
  (natDegree_pow_le_of_le i hd)) (natDegree_pow_le_of_le j hd')).trans ?_
 have hj:j*(d-1)+j=j*d:= by rw [← Nat.mul_succ,Nat.succ_eq_add_one,hpred]
 rw [Nat.add_mul] at hw
 omega
theorem dOD (z :K) (S:K[X]) (P:Source) :
    rD (U4 P) z S=cy L[X] FX (ab3 (Z7 z) (j9 S) P) := by
  let ev :=oy (oy (qD z) (kr S)) (kr S.derivative)
  let f :=cy L[X] FX
  change (ev.comp U4.toRingHom) P=(f.comp (ab3 (Z7 z) (j9 S))) P
  apply t6
  apply bFk
  · intro g
    have he :
        (qD z).comp (oj (cy L FX)) =
          (f.comp C).comp (qx (Z7 z)) := by
      apply Av
      · intro a
        simp [qD,oq,f]
        rfl
      · intro i
        fin_cases i <;> simp [qD,Z7,jz,f]
    simpa [oq,U4,ev,ab3] using t6 he g
  · simp [oq,U4,ev,ab3,qD,f]
  · simp [oq,U4,ev,ab3,f,kr]
  · simp [oq,U4,ev,ab3,f,kr,j9,zi]
theorem deX {h:ℕ} {D:jF h} {Crt:zG D}
   {word:I→L} {s :lJ} {W:ℕ} (z :K) (S:K[X])
   (hz : ∀ P∈complete Crt word s W,ab3 (Z7 z) (j9 S) P=0)
   {P:Jet} (hP:P∈VY Crt word s W) :rD P z S=0:= by
 let ev :=oy (oy (qD z) (kr S)) (kr S.derivative)
 change P∈G4 FX _ at hP
 change ev P=0
 induction hP using Submodule.span_induction with
 | mem P hP =>
   obtain ⟨Q,hQ,rfl⟩:=hP
   change rD (U4 Q) z S=0
   rw [dOD,hz Q hQ,ox]
 | zero=>exact map_zero ev
 | add A B _ _ hA hB=>rw [map_add,hA,hB,add_zero]
 | smul r A _ hA=>rw [Algebra.smul_def,map_mul,hA,mul_zero]
private theorem eK7 (t:Fin 2→L) (S:L[X]) (x r :L) :
   (adA (C.comp (qx t)) (aU-C x)
     (S-C r-(aU-C x)*S.derivative) S.derivative).comp (Km x r).toRingHom =
     ab3 t S:= by
 let δ:L[X] :=aU-C x
 let η:L[X] :=S-C r-δ*S.derivative
 let E :=adA (C.comp (qx t)) δ η S.derivative
 let c:qC[X] →+* Source :=pW
 let u:qC[X] :=aU +C (nq x)
 let b:qC[X] →+* Source :=c.comp (oy C u)
 let y :Source :=c (C (nq r))+c aU*aU +C aU
 let _:c9 Source :=inferInstanceAs (c9 (lz (lz (lz qC))))
 have hform : (Km x r).toRingHom=oy (oy b y) Polynomial.X:=rfl
 change E.comp (Km x r).toRingHom=ab3 t S
 rw [hform]
 apply bFk
 · intro g
   simp [E,ab3,b,c,pW,oq]
 · simp [E,ab3,b,c,u,δ,pW,oq]
 · simp [E,ab3,y,c,η,pW,oq]
 · simp [E,ab3,oq]
private theorem fWa (S:L[X]) (x r :L) (hx :S.eval x=r) :
   (aU-C x)^2∣S-C r-(aU-C x)*S.derivative := by
 rw [X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero]
 intro k hk
 have he :k=0∨k=1 := by omega
 rcases he with rfl | rfl
 · simp [hx]
 · simp [hasseDeriv_one,derivative_sub,yU]
theorem cHy {word:I→L} {s :lJ} {P:Source}
  (hP:P∈amm word s) (t:Fin 2→L) (S:L[X])
  (k :I) (hk :S.eval (ad0 k)=word k) :
  (aU-C (ad0 k))^s.m∣ab3 t S P:= by
 let x :=ad0 k
 let r :=word k
 let δ:L[X] :=aU-C x
 let η:L[X] :=S-C r-δ*S.derivative
 let E :=adA (C.comp (qx t)) δ η S.derivative
 let Q:=Km x r P
 change δ^s.m∣ab3 t S P
 have he :E Q=ab3 t S P :=
  t6 (eK7 t S x r) P
 rw [← he]
 dsimp only [E]
 rw [cMK]
 apply Gi
 intro j _
 apply Dvd.dvd.mul_right
 apply Gi
 intro b _
 rw [EP]
 apply Gi
 intro a ha
 have hw:s.m≤a+2*b:= by
  by_contra hn
  apply mem_support_iff.mp ha
  ext e
  exact hP k a b j e (by omega)
 have hη:δ^2∣η:=fWa S x r hk
 have hpow:δ^(a+2*b)∣δ^a*η^b:= by
  rw [yQ,pow_mul]
  exact mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hη b)
 exact (pow_dvd_pow _ hw).trans (by simpa only [t8] using hpow.mul_left _)
def azz {h:ℕ} {D:jF h} (Crt:zG D) (t:Fin 2→L) :L[X] :=
 ∑ i,C (((Crt.denominator i).eval (t i))⁻¹)*(Crt.numerator i).map (sI (t i))
private theorem cZq (t:L) (P:L[X]) :
  (P.map (C:L →+* L[X])).map (sI t)=P:= by
 rw [oY]
 have he : (sI t).comp (C:L →+* L[X])=uJ L:= by ext a; simp
 simp [he]
theorem cZS {h:ℕ} {D:jF h} (Crt:zG D)
   {z :K} {S:K[X]} (hm:aKF D z S) :
   Iy D ∣j9 S-azz Crt (Z7 z) := by
 let t:=Z7 z
 let d (i:Fin 2) :=(Crt.denominator i).eval (t i)
 let N (i:Fin 2) :=(Crt.numerator i).map (sI (t i))
 let U (i:Fin 2) :=C (d i)⁻¹*N i
 have hd (i:Fin 2) :d i≠0:=Crt.regular i (t i) (hm i).1
 have hc (i:Fin 2) :D.block i∣Tj D i (t i)*U i+C (t i)*D.offset i:= by
   have h0:=vk (oK (sI (t i))) (Crt.congruence i)
   have h1 :D.block i∣Tj D i (t i)*N i+C (d i*t i)*D.offset i:= by
     simpa [Tj,N,d,cZq] using h0
   have he : (C (d i)⁻¹:L[X])*C (d i*t i)=C (t i) := by
     rw [← lV,← t8 ,Mz (hd i),wY]
   simpa only [Gn,← t8 ,t4 (C (d i)⁻¹) (Tj D i (t i)),he,U] using
     h1.mul_left (C (d i)⁻¹)
 have ho (i:Fin 2) :D.block (CI i)∣U i:= by
   apply Dvd.dvd.mul_left
   simpa [N,cZq] using vk (oK (sI (t i))) (Crt.other_dvd i)
 have hsum (i:Fin 2) :azz Crt t=U i+U (CI i) := by
   rw [azz,FQ]
   fin_cases i
   · rfl
   · exact add_comm _ _
 have hblock (i:Fin 2) :D.block i∣j9 S-azz Crt t:= by
   apply (hm i).1.symm.dvd_of_dvd_mul_left
   have hoi:D.block i∣U (CI i) := by
     have hother :CI (CI i)=i:= by fin_cases i <;> decide
     simpa only [hother] using ho (CI i)
   have hmark :D.block i∣Tj D i (t i)*azz Crt t+C (t i)*D.offset i:= by
     rw [hsum,Gn,add_right_comm]
     exact dvd_add (hc i) (hoi.mul_left _)
   have hactual:D.block i∣Tj D i (t i)*j9 S+C (t i)*D.offset i :=
     (hm i).2
   change D.block i∣Tj D i (t i)*(j9 S-azz Crt t)
   simpa only [mul_sub,add_sub_add_right_eq_sub] using dvd_sub hactual hmark
 exact D.coprime.mul_dvd (hblock 0) (hblock 1)
private def buV (t:Fin 2→L) :Submonoid qC where
 carrier := {a | qx t a≠0}
 one_mem' := by simp
 mul_mem' := by
  intro a b ha hb
  change qx t (a*b)≠0
  exact (lV (qx t) a b).symm ▸ z7 ha hb
private abbrev a06 (t:Fin 2→L) :=Localization (buV t)
private def specialize (t:Fin 2→L) :a06 t →+* L :=
 Pr (g:=qx t)
  (fun a :buV t=>isUnit_iff_ne_zero.mpr a.property)
private def bq3 (t:Fin 2→L) :a06 t →+* aQ :=
  Pr (g:=cy qC aQ)
    (fun a :buV t=>isUnit_iff_ne_zero.mpr
      (fun he=>a.property (by
        have hzero :=(qM qC aQ) (he.trans (ox _).symm)
        simp [hzero])))
private theorem enZ (t:Fin 2→L) :
  uW (bq3 t) := by
 unfold bq3
 apply (IsLocalization.lift_injective_iff _).mpr
 intro a b
 have h:buV t≤NI qC:= fun x hx =>
  mem_nonZeroDivisors_iff_ne_zero.mpr (fun he=>hx (by simp [he]))
 rw [(IsLocalization.injective (a06 t) h).eq_iff,
  (qM qC aQ).eq_iff]
private def Wu (i:Fin 2) :L[X] →+* qC :=
 oy nq (nX i)
private theorem cZD (i:Fin 2) :
  (cy qC aQ).comp (Wu i)=(MF i).toRingHom:= by
 apply p6 <;>
  simp [Wu,MF,aeval_def,oq,vH,
    zc L qC aQ]
private theorem b16 (t:Fin 2→L) (i:Fin 2) :
  (qx t).comp (Wu i)=sI (t i) := by
 apply p6 <;> simp [Wu,oq]
private def bsb {h:ℕ} {D:jF h} (Crt:zG D) (t:Fin 2→L)
    (hd : ∀ i,(Crt.denominator i).eval (t i)≠0) : (a06 t)[X] :=
  ∑ i,C (IsLocalization.mk' (a06 t) 1
      (⟨Wu i (Crt.denominator i),by
        change (qx t).comp (Wu i) (Crt.denominator i)≠0
        rw [b16]
        exact hd i⟩:buV t)) *
    (Crt.numerator i).map ((cy qC (a06 t)).comp (Wu i))
private theorem ey4 {h:ℕ} {D:jF h} (Crt:zG D) (t:Fin 2→L)
   (hd : ∀ i,(Crt.denominator i).eval (t i)≠0) :
   (bsb Crt t hd).map (bq3 t)=OY Crt:= by
 rw [bsb,OY,UY]
 apply p7 rfl
 intro i _
 have he :cy qC aQ (Wu i (Crt.denominator i)) =
     MF i (Crt.denominator i) :=
   zd (cZD i) (Crt.denominator i)
 simp only [qm,oZ,oY ,bq3,
   SL,JW,← PD,cZD,
   Ar,vh,Sd ,wY ,
   Xo ,IsUnit.unit_spec,SD]
 change C ((cy qC aQ (Wu i (Crt.denominator i)))⁻¹)*_ = _
 rw [he]
 rfl
private theorem gtY {h:ℕ} {D:jF h} (Crt:zG D) (t:Fin 2→L)
   (hd : ∀ i,(Crt.denominator i).eval (t i)≠0) :
   (bsb Crt t hd).map (specialize t)=azz Crt t:= by
 rw [bsb,azz,UY]
 apply p7 rfl
 intro i _
 have he :qx t (Wu i (Crt.denominator i)) =
     (Crt.denominator i).eval (t i) :=
   zd (b16 t i) (Crt.denominator i)
 simp only [qm,oZ,oY ,specialize,
   SL,JW,← PD,b16,
   vh,Sd ,wY ,Xo ,IsUnit.unit_spec,
   SD]
 change C ((qx t (Wu i (Crt.denominator i)))⁻¹)*_ = _
 rw [he]
private def Qa (T:aQ[X]) :US →+* aQ[X] :=
 oy (oy (uJ _) T) T.derivative
private theorem edC {h:ℕ} {D:jF h} (Crt:zG D)
    (T:aQ[X]) :
    (Qa T).comp (forward Crt).toRingHom =
      adA (C.comp (cy qC aQ)) aU
        (IE D*T+OY Crt)
        (IE D*T.derivative+(IE D).derivative*T+(OY Crt).derivative) := by
  let c:aQ[X] →+* US:=pW
  let H :=IE D
  let lift:=OY Crt
  let o:US:=C (aU (R:=lz aQ))
  let v :US:=aU
  let b:qC[X] →+* US:=c.comp (oK (cy qC aQ))
  let _:c9 US:=inferInstanceAs (c9 (lz (lz (lz aQ))))
  have hf : (forward Crt).toRingHom =
      oy (oy b (c H*o+c lift)) (c H*v+c H.derivative*o+c lift.derivative) :=rfl
  rw [hf]
  apply bFk <;> simp [Qa,c,pW,H,lift,o,v,b,oq]
private theorem cMJ {R A B:Type*} [oD R] [oD A] [oD B]
  (f :R →+* A) (g:A →+* B) (jetY jetV:A[X]) :
  (oK g).comp (adA (C.comp f) aU jetY jetV) =
    adA (C.comp (g.comp f)) aU (jetY.map g) (jetV.map g) := by
 apply bFk <;> simp [oq]
theorem dfg {h:ℕ} {D:jF h} (Crt:zG D)
   {z :K} {S:K[X]} (hm:aKF D z S) {s :lJ} {P:Source}
   (hP:P∈btN Crt s) :
   Iy D^(s.B+s.J)∣ab3 (Z7 z) (j9 S) P:= by
 let t:=Z7 z
 let A:=a06 t
 let f :=cy qC A
 let e :=specialize t
 let g:=bq3 t
 let j:L →+* A:=f.comp nq
 have hef :e.comp f=qx t:=JW _
 have hgf :g.comp f=cy qC aQ:=JW _
 have hej:e.comp j=uJ L:= by
   change (e.comp f).comp nq= _
   rw [hef]
   ext a
   simp
 have hgj:g.comp j=cy L aQ:= by
   change (g.comp f).comp nq= _
   rw [hgf]
   ext a
   simp [zc L qC aQ,vH]
 have hd (i:Fin 2) : (Crt.denominator i).eval (t i)≠0:=Crt.regular i _ (hm i).1
 obtain ⟨T,hT⟩:=cZS Crt hm
 have hS:Iy D*T+azz Crt t=j9 S:= by
   rw [← hT]
   abel
 let H :=(Iy D).map j
 let U:=T.map j
 let lift:=bsb Crt t hd
 let jetY:=H*U + lift
 let Q:=adA (C.comp f) aU jetY jetY.derivative P
 let F:=H^(s.B+s.J)
 have hFm:F.Monic:=((D.monic 0).mul (D.monic 1) |>.map j).pow _
 have egH :H.map g=IE D:= by rw [oY ,hgj]; rfl
 have eeH :H.map e=Iy D:= by rw [oY ,hej,Bf]
 have eeU:U.map e=T:= by rw [oY ,hej,Bf]
 have egY:jetY.map g=IE D *U.map g+OY Crt:= by
   rw [yl,qm,egH,ey4]
 have eeY:jetY.map e=j9 S:= by
   rw [yl,qm,eeH,eeU,gtY,hS]
 have hgQ :
     Q.map g= Qa (U.map g) (forward Crt P) := by
   change ((oK g).comp (adA (C.comp f) aU jetY jetY.derivative)) P =
     ((Qa (U.map g)).comp (forward Crt).toRingHom) P
   rw [cMJ,hgf,← zi ,egY,edC,JK,yU]
   congr! 2
   abel
 have hgF:F.map g=IE D^(s.B+s.J) := by rw [Dw ,egH]
 have hdiv :F.map g∣Q.map g:= by
   rw [hgF,hgQ]
   have h:=vk (Qa (U.map g)) hP
   simpa [Qa,pW,eval₂_pow] using h
 have hlocal:F∣Q:= by
   apply (Ml hFm).mp
   apply map_injective g (enZ t)
   rw [F9 g hFm,VS]
   exact (Ml (hFm.map g)).mpr hdiv
 have heQ:Q.map e=ab3 t (j9 S) P:= by
   change ((oK e).comp (adA (C.comp f) aU jetY jetY.derivative)) P= _
   rw [cMJ,hef,← zi ,eeY]
   rfl
 have heF:F.map e=Iy D^(s.B+s.J) := by rw [Dw ,eeH]
 have hmapped:=vk (oK e) hlocal
 change F.map e∣Q.map e at hmapped
 rwa [heF,heQ] at hmapped
end
end bax
end
section
namespace axj
noncomputable section
open K1 cu DP Polynomial
open scoped Polynomial
def translation {R:Type*} [c9 R] (i:Fin 2) :
    nI (Fin 2) R →ₐ[R] (nI (Fin 2) R)[X] :=
  uz fun j =>
    C (nX j)+if j=i then aU else 0
def Bg {R:Type*} [c9 R] (i:Fin 2) (r :ℕ) :
    nI (Fin 2) R →ₗ[R] nI (Fin 2) R where
  toFun P:=(translation i P).coeff r
  map_add' P Q:= by simp
  map_smul' a P:= by simp
def mapCoeffs {R A B:Type*} [p9 R] [p9 A] [p9 B]
    [vi R A] [vi R B] (f :A →ₗ[R] B) :A[X] →ₗ[R] B[X] :=
  Polynomial.lsum fun n =>
    { toFun:= fun a=>pz n (f a)
      map_add' := fun a b=> by rw [ov,ov]
      map_smul' := fun c a=> by rw [x7,← smul_monomial]; rfl }
@[simp] theorem a5F {R A B:Type*} [p9 R] [p9 A] [p9 B]
    [vi R A] [vi R B] (f :A →ₗ[R] B) (Q:A[X]) (n:ℕ) :
    (mapCoeffs f Q).coeff n=f (Q.coeff n) := by
  change (Q.sum fun j a=>pz j (f a)).coeff n=f (Q.coeff n)
  classical
  simp only [NY ,wR,ze,Finset.sum_ite_eq']
  split
  · rfl
  next h=>rw [notMem_support_iff.mp h,map_zero]
@[simp] theorem mapCoeffs_monomial {R A B:Type*} [p9 R] [p9 A] [p9 B]
   [vi R A] [vi R B] (f :A →ₗ[R] B) (n:ℕ) (a :A) :
   mapCoeffs f (pz n a)=pz n (f a) := by
  ext m
  simp only [a5F,ze]
  split <;> simp
def awz (i:Fin 2) (r :ℕ) :Source →ₗ[L] Source :=
 mapCoeffs (mapCoeffs (mapCoeffs (Bg i r)))
def aXQ (E :L[X]) :qC[X] :=
 E.map nq
def BA {h:ℕ} (D:jF h) (i:Fin 2) (r :ℕ) (Q:Source) :Source :=
 pW (aXQ (D.block i^(2*r)))*awz i r Q
end
end axj
end
section
set_option backward.isDefEq.respectTransparency false
namespace axj
noncomputable section
open K1 cu DP Polynomial
open scoped BigOperators Polynomial
private theorem coV (i:Fin 2) (r :ℕ) (P:qC) :
    (Bg i r P).totalDegree≤P.totalDegree := by
  classical
  let g:Fin 2→nI (Option (Fin 2)) L :=
    fun j=>nX (some j)+if j=i then nX none else 0
  let f :qC →ₐ[L] nI (Option (Fin 2)) L:=uz g
  have htrans :translation i=(MvPolynomial.optionEquivLeft L (Fin 2)).toAlgHom.comp f := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj:j=i <;> simp [translation,f,g,hj]
  have hg (j:Fin 2) : (g j).totalDegree≤1 := by
    by_cases hj:j=i
    · simpa [g,hj] using (MvPolynomial.totalDegree_add
        (nX (some j) :nI (Option (Fin 2)) L)
        (nX none))
    · simp [g,hj]
  have hf : (f P).totalDegree≤P.totalDegree := by
    conv_lhs=>rw [P.as_sum]
    rw [qG]
    apply TI
    intro m hm
    change (uz g (qz m (P.coeff m))).totalDegree≤_
    rw [Pf]
    refine (Ww _ _).trans ?_
    rw [vH,WD,v9,Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine le_trans (Ts (fun j _ => ?_)) (UZ hm)
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using RJ (m j) (hg j))
  change ((translation i P).coeff r).totalDegree≤_
  rw [htrans]
  exact (MvPolynomial.totalDegree_coeff_optionEquivLeft_le L (Fin 2) (f P) r).trans hf
theorem ds6 {h:ℕ} (D:jF h) {s :lJ} {W:ℕ} {Q:Source}
   (hQ:Q∈Aw h s W) (i:Fin 2) (r :ℕ) :
   BA D i r Q∈Aw h s (W+2*h*r) := by
 classical
 intro j k a e he
 simp only [BA,Fg,pW,oq]
 rw [yL,yL,coeff_mul,GF]
 simp only [aXQ,t9,Kp,awz,a5F]
 apply t5
 rintro ⟨b,c⟩ hbc
 by_cases hb: (D.block i^(2*r)).coeff b=0
 · simp [hb]
 have hbdeg:b≤2*h*r := by
   have hb' := le_natDegree_of_ne_zero hb
   rw [natDegree_pow,D.degree] at hb'
   simpa [Dv,Nat.mul_left_comm,Nat.mul_assoc] using hb'
 have hbc' : b+c=a := by
   simpa only [Nj] using hbc
 let A:=((Q.coeff j).coeff k).coeff c
 change (D.block i^(2*r)).coeff b*(Bg i r A).coeff e=0
 by_contra hne
 have hseed : (Bg i r A).coeff e≠0:= fun hz=>hne (by simp [hz])
 have ht:Tl e≤A.totalDegree :=
   (UZ (MvPolynomial.mem_support_iff.mpr hseed)).trans
     (coV i r A)
 have hAnz :A≠0:= fun hz=>hseed (by simp [hz])
 have hshape : ∃ d,awN h s W j k c d:= by
   by_contra hall
   apply hAnz
   apply y5
   intro d
   simpa [Fg,A] using hQ j k c d (fun hd=>hall ⟨d,hd⟩)
 obtain ⟨d,hs,hj,_,hw⟩:=hshape
 have hseedCap:A.totalDegree≤ s.U:= by
   rw [ Xg ,TZ]
   intro d hd
   by_contra hbad
   exact (MvPolynomial.mem_support_iff.mp hd) (hQ j k c d (fun hd' => hbad hd'.2.2.1))
 exact he ⟨hs,hj,ht.trans hseedCap,by omega⟩
end
end axj
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace Ge
noncomputable section
open K1 cu DP Polynomial
open scoped BigOperators Polynomial
abbrev i5 (R:Type) [c9 R] :=nI (Fin 2) R
abbrev kq (F:Type) [lI F] :=vZ (i5 F)
abbrev EM (R:Type) [p9 R] :=lz (lz (lz R))
abbrev Gm (R:Type) [c9 R] :=EM (i5 R)
abbrev Exponent:=Fin 2 →₀ ℕ
def aQu {R:Type} [c9 R] (P:Gm R)
    (j i a :ℕ) (e :Exponent) :R :=
  (((P.coeff j).coeff i).coeff a).coeff e
def adk {R:Type} [c9 R] (s :lJ) (P:Gm R) :Prop :=
 ∀ j i a e,aQu P j i a e≠0→i+j≤ s.B∧j≤ s.J∧Tl e≤ s.U
def avv {R S:Type} [c9 R] [c9 S] (f :R →+* S) :
    Gm R →+* Gm S :=
  oK (oK (oK (oj f)))
def bbs {F:Type} [lI F] (U d:ℕ) (side :Fin 2) (g:i5 F) :Prop :=
 ∀ e,g.coeff e≠0→e (CI side)≤U∧e side+e (CI side)≤U + d
private def gu8 {R S A:Type} [c9 R] [c9 S]
  [c9 A] [Algebra R S] [Algebra R A]
  (base :S →ₐ[R] A) (y v :A) :lz (lz S) →ₐ[R] A :=
 z8 (z8 base y (fun _=>Aa _ _))
  v (fun _=>Aa _ _)
def forward {F:Type} [lI F] (H :F[X]) (lift: (kq F)[X]) :
    Gm F →ₐ[F] EM (kq F) :=
  let H' := H.map (cy F (kq F))
  let c: (kq F)[X] →+* EM (kq F) :=pW
  let aJc:EM (kq F) :=C (aU (R:=lz (kq F)))
  let a7z :EM (kq F) :=aU
  let coeffs : (i5 F)[X] →ₐ[F] (kq F)[X] :=
    vl (vw F (i5 F) (kq F))
  let base :=(vw F (kq F)[X] (EM (kq F))).comp coeffs
  gu8 base (c H' * aJc+c lift)
    (c H' * a7z+c H'.derivative*aJc+c lift.derivative)
def a0X {F:Type} [lI F] (s :lJ) (H :F[X])
    (lift: (kq F)[X]) (P:Gm F) :Prop :=
  (pW ((H.map (cy F (kq F)))^(s.B+s.J)) :
    EM (kq F))∣forward H lift P
abbrev jJ (s :lJ) :=Fin (s.B+1)
abbrev NQ (s :lJ) (q:ℕ) :=Fin (min q s.J+1)
abbrev bjM (s :lJ) (q:ℕ) :=Fin (s.B+s.J - q)×NQ s q
def aRi {F:Type} [lI F] (s :lJ) (q:ℕ)
    (f :NQ s q→F[X]) (k :NQ s q) :F[X] :=
  ∑ j,if k.val≤j.val then
    f j*mD (R:=F) (j.val.choose k.val :F) *
      (aU (R:=F))^(q - j.val+k.val) else 0
def residue {F:Type} [lI F] (side :Fin 2) (a b c:F) :kq F :=
  let z :=cy (i5 F) (kq F) (nX side)
  cy F (kq F) a*z /
    (cy F (kq F) b+algebraMap F (kq F) c*z)
structure bk5 {F:Type} [lI F] (h:ℕ) (H :F[X])
   (lift: (kq F)[X]) where
 root :Fin (2*h)→F
 side :Fin (2*h)→Fin 2
 a :Fin (2*h)→F
 b:Fin (2*h)→F
 c:Fin (2*h)→F
 distinct :uW root
 factorization :H = ∏ t,(aU (R:=F)-Polynomial.C (root t))
 aiq : ∀ t,H.eval (root t)=0
 simple : ∀ t,H.derivative.eval (root t)≠0
 b_ne : ∀ t,b t≠0
 centre : ∀ t,lift.eval (cy F (kq F) (root t)) =
   residue (side t) (a t) (b t) (c t)
abbrev Parameter :=L[X]
abbrev lN :=AlgebraicClosure (vZ Parameter)
def Uv :Parameter →+* L:=sI 0
def genericPoint:Parameter →+* lN :=
  (cy (vZ Parameter) lN).comp
    (cy Parameter (vZ Parameter))
def Ua {F:Type} [lI F] (point :Parameter →+* F) (num : (i5 Parameter)[X])
    (den:i5 Parameter) : (kq F)[X] :=
  (cy (i5 F) (kq F) (oj point den))⁻¹ •
    num.map ((cy (i5 F) (kq F)).comp (oj point))
structure cAi {h:ℕ} (D:jF h) (Crt:zG D) where
 H :Parameter[X]
 num : (i5 Parameter)[X]
 den:i5 Parameter
 monic:H.Monic
 specialH :H.map Uv=Iy D
 specialDen:oj Uv den≠0
 specialLift:Ua Uv num den=OY Crt
 genericDen:oj genericPoint den≠0
 genericPoles :bk5 h (H.map genericPoint) (Ua genericPoint num den)
end
end Ge
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace Ge
noncomputable section
open K1 cu DP Polynomial
open scoped BigOperators Polynomial
def c7p {F:Type} [lI F] (j i a :ℕ) (e :Exponent) :
    Gm F →ₗ[F] F where
  toFun P:=aQu P j i a e
  map_add' P Q:= by simp [aQu]
  map_smul' b P:= by simp [aQu,C5]
theorem gp2 {R S:Type} [c9 R] [c9 S]
  (f :R →+* S) {s :lJ} {P:Gm R} (h:adk s P) :
  adk s (avv f P) := by
 intro j i a e hne
 apply h j i a e
 intro hz
 apply hne
 simpa [aQu,avv,t9,G8] using
  (oz f hz).trans (ox f)
theorem ddL {F ι:Type} [lI F] [p5 ι]
  {s :lJ} {P:ι→Gm F} (hP : ∀ i,adk s (P i)) (v :ι→F) :
  adk s (Du F P v) := by
 intro j i a e hne
 by_contra hbad
 apply hne
 change c7p j i a e (Du F P v)=0
 rw [SM,qG]
 apply t5
 intro k _
 have he :aQu (P k) j i a e=0:= by
  by_contra hz
  exact hbad (hP k j i a e hz)
 rw [x7]
 change v k•aQu (P k) j i a e=0
 rw [he,smul_zero]
private abbrev cxj (B M U:ℕ) :=
 Fin (B+1)×Fin (B+1)×Fin (M+1)×(Fin 2→Fin (U + 1))
theorem dPs (h:ℕ) (word:I→L) (s :lJ) (W:ℕ) :
    Ea L (aq7 h word s W) := by
  classical
  let M:=W+(s.B+s.J)*(2*h)+s.J
  let f :aq7 h word s W →ₗ[L] (cxj s.B M s.U→L) :=
    FV fun u =>
      (c7p u.1.val u.2.1.val u.2.2.1.val
        (Finsupp.equivFunOnFinite.symm fun k=>(u.2.2.2 k).val)).comp
          (aq7 h word s W).subtype
  have hzero (Q:aq7 h word s W) (hQ:f Q=0) :Q=0:= by
    obtain ⟨P,hP⟩:= Q
    have hA:P∈Aw h s W:=hP.1
    apply C4
    change P=0
    apply pQ
    intro j
    rw [v8]
    apply pQ
    intro i
    rw [v8]
    apply pQ
    intro a
    rw [v8]
    apply y5
    intro e
    simp only [In,Hw]
    change Fg P j i a e=0
    by_cases he :awN h s W j i a e
    · obtain ⟨hB,hJ,hU,hW⟩:=he
      have hM:a≤M:= by dsimp [M]; omega
      have hU' (k :Fin 2) :e k≤ s.U:= by
        apply le_trans _ hU
        rw [Tl,G2 _ _ (by simp)]
        exact VH (fun _ _=>Nat.zero_le _) (u9 k)
      let u:cxj s.B M s.U :=
        (⟨j,by omega⟩,⟨i,by omega⟩,⟨a,by omega⟩,
          fun k=>⟨e k,xW  (hU' k)⟩)
      have hz :=yo hQ u
      change Fg P j i a (Finsupp.equivFunOnFinite.symm (fun k=>e k))=0 at hz
      exact (Finsupp.equivFunOnFinite.symm_apply_apply e) ▸ hz
    · exact hA j i a e he
  apply VO f
  intro P Q hPQ
  apply sub_eq_zero.mp
  exact hzero (P-Q) (by rw [Fz ,hPQ,J4])
theorem dPt {h:ℕ} {word:I→L} {s :lJ} {W:ℕ}
  {P:Source} (hP:P∈aq7 h word s W) :adk s P:= by
 intro j i a e hn
 have he :awN h s W j i a e := by
  by_contra hf
  exact hn (hP.1 j i a e hf)
 exact ⟨he.1,he.2.1,he.2.2.1⟩
private abbrev bTO (U d:ℕ) :=
 Σ k :Fin (U + 1),Fin (d+k.val+1)
private def bP4 {U d:ℕ} (side :Fin 2) (k :bTO U d) :Exponent :=
 Finsupp.equivFunOnFinite.symm (fun t=>if t=side then k.2.val else U - k.1.val)
private theorem gMU (U d:ℕ) :
  Cy (bTO U d)=qJ U + (U+1)*d:= by
 rw [Eg]
 simp only [yJ]
 simp_rw [show ∀ k :Fin (U+1),d+k.val+1=(k.val+1)+d by omega]
 rw [Finset.sum_add_distrib]
 simp only [Finset.sum_const,Finset.card_univ,yJ,nsmul_eq_mul]
 congr 1
 rw [zf (fun k :ℕ=>k+1)]
 have hsum:=Pk (U+2)
 rw [Pc] at hsum
 simpa [qJ,Dv (U+2) (U+1),Nat.add_comm 1] using hsum
theorem dc6 (F:Type) [lI F] (U d:ℕ) (side :Fin 2) :
    ∃ read:i5 F →ₗ[F] (Fin (qJ U + (U+1)*d)→F),
      ∀ g,bbs U d side g→ read g=0→ g=0:= by
  classical
  let eq :=LP (gMU U d)
  let read:i5 F →ₗ[F] (Fin (qJ U + (U+1)*d)→F) :=
    FV fun k=>Wm F (bP4 side (eq.symm k))
  refine ⟨read,?_⟩
  intro g hg hzero
  apply y5
  intro e
  simp only [In,Hw]
  by_contra hn
  obtain ⟨ho,ht⟩:=hg e hn
  let k :bTO U d :=
    ⟨⟨U-e (CI side),by omega⟩,⟨e side,by dsimp; omega⟩⟩
  have he :bP4 side k=e := by
    ext t
    simp only [bP4,Finsupp.coe_equivFunOnFinite_symm]
    by_cases hts :t=side
    · simp [hts,k]
    · have hto :t=CI side := by
        fin_cases t <;> fin_cases side <;> simp_all [CI]
      rw [z9 hts,hto]
      exact Nat.sub_sub_self ho
  have hz :=yo hzero (eq k)
  change g.coeff (bP4 side (eq.symm (eq k)))=0 at hz
  rw [eq.symm_apply_apply,he] at hz
  exact hn hz
end
end Ge
end
section
set_option backward.isDefEq.respectTransparency false
namespace axj
noncomputable section
open K1 cu DP Polynomial
open scoped Polynomial
def c1 :Prop :=
  ∀ h (D:jF h) (word:I→L) s,∀ Q∈amm word s,∀ i r,
    BA D i r Q∈amm word s
def c2 :Prop :=
  ∀ h (D:jF h) (Crt:zG D) s,∀ Q∈btN Crt s,∀ i r,
    BA D i r Q∈btN Crt s
private def aUq (i:Fin 2) (r :ℕ) :Jet →ₗ[FX] Jet :=
 mapCoeffs (mapCoeffs (Bg i r))
private theorem cNg (i:Fin 2) (r :ℕ) (P:Jet) :
 aUq i r P=A5 i r P:=rfl
private theorem gDV {R S:Type*} [c9 R] [c9 S]
   (f :R →+* S) (i:Fin 2) (P:nI (Fin 2) R) :
   (translation i P).map (oj f)=translation i (oj f P) := by
 let a :=(oK (oj f)).comp (translation (R:=R) i).toRingHom
 let b:=(translation (R:=S) i).toRingHom.comp (oj f)
 have hab:a=b:= by
   apply Av
   · intro c
     simp [a,b,translation,vH]
   · intro j
     by_cases hj:j=i <;> simp [a,b,translation,hj]
 exact t6 hab P
private theorem gnY {R S:Type*} [c9 R] [c9 S]
  (f :R →+* S) (i:Fin 2) (r :ℕ) (P:nI (Fin 2) R) :
  oj f (Bg i r P)=Bg i r (oj f P) := by
 change oj f ((translation i P).coeff r) =
  (translation i (oj f P)).coeff r
 rw [← t9,gDV]
private def ξ:FX:=cy (lz L) FX (aU (R:=L))
private def alC:qC[X] →ₐ[L] aZ :=
 z8 (UP (Algebra.ofId L FX))
  (nq ξ) (fun _=>Aa _ _)
private theorem dGq (i:Fin 2) (r :ℕ) (Q:qC[X]) :
   alC (mapCoeffs (Bg i r) Q)=Bg i r (alC Q) := by
 induction Q using Lf with
 | add P Q hp hq =>
   rw [ov,ov,ov,ov,hp,hq]
 | monomial n a =>
   rw [mapCoeffs_monomial]
   change (pz n (Bg i r a)).eval₂ (oj (cy L FX))
    (nq ξ)=Bg i r
    ((pz n a).eval₂ (oj (cy L FX)) (nq ξ))
   rw [LO,LO,← pG]
   simp only [t4 _ (nq (ξ^n)),← MvPolynomial.smul_eq_C_mul,
    x7,gnY]
private theorem dGv (i:Fin 2) (r :ℕ) (Q:Source) :
  U4 (awz i r Q)=aUq i r (U4 Q) := by
 apply pQ
 intro j
 apply pQ
 intro k
 change ((vl (vl alC)
  (awz i r Q)).coeff j).coeff k =
    ((aUq i r (vl (vl alC) Q)).coeff j).coeff k
 simp only [awz,aUq,Mw ,a5F]
 exact dGq i r ((Q.coeff j).coeff k)
private theorem dGr (E :L[X]) :
   alC (aXQ E)=nq (cy L[X] FX E) := by
 change (E.map nq).eval₂ (oj (cy L FX)) (nq ξ)= _
 rw [eval₂_map]
 have hc: (oj (cy L FX)).comp
     (nq:L →+* qC)=MvPolynomial.C.comp (cy L FX) := by
   ext a
   simp
 rw [hc]
 exact Qx E
   ((vw L FX aZ).comp (vw L L[X] FX))
private theorem cEw {h:ℕ} (D:jF h) (i:Fin 2) (r :ℕ) (Q:Source) :
   U4 (BA D i r Q) =
     (cy L[X] FX (D.block i^(2*r)))•aUq i r (U4 Q) := by
 rw [BA,lV,dGv]
 change Polynomial.map (oK alC.toRingHom)
   (C (C (aXQ (D.block i^(2*r)))))*_ = _
 rw [oZ]
 change C (Polynomial.map alC.toRingHom (C (aXQ (D.block i^(2*r)))))*_ = _
 rw [oZ]
 change C (C (alC (aXQ (D.block i^(2*r)))))*_ = _
 rw [dGr,yB]
 rfl
end
end axj
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace Ge
noncomputable section
open cu Polynomial
theorem gtP {m n:ℕ} (M:sS (Fin m) (Fin n) Parameter) :
    (M.map Uv).rank≤(M.map genericPoint).rank := by
  classical
  let B:=M.map Uv
  let f :=B.mulVecLin
  let k :=B.rank
  let e :Gr f ≃ₗ[L] (Fin k→L) :=
    (Module.finBasis L (Gr f)).equivFun
  obtain ⟨right,hr⟩:=f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨left,hl⟩:=(Gr f).subtype.exists_leftInverse_of_injective
    (Gr f).ker_subtype
  let U:sS (Fin k) (Fin m) L:=(e.toLinearMap.comp left).toMatrix'
  let V:sS (Fin n) (Fin k) L:=(right.comp e.symm.toLinearMap).toMatrix'
  have hB:U*B*V=1 := by
    apply (Matrix.toLin' (R:=L)).injective
    rw [Matrix.toLin'_one,Qy ,Qy]
    simp only [U,V,Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    change e (left (f (right (e.symm v))))=v
    have hright:= QL hr (e.symm v)
    have hleft:= QL hl (e.symm v)
    change f.rangeRestrict (right (e.symm v))=e.symm v at hright
    change left (f.range.subtype (e.symm v))=e.symm v at hleft
    change e (left (f.range.subtype (f.rangeRestrict (right (e.symm v)))))=v
    rw [hright,hleft,e.apply_symm_apply]
  let U₀:=U.map (mD (R:=L))
  let V₀:=V.map (mD (R:=L))
  let S:=U₀*M*V₀
  have hS:S.map Uv=1 := by
    rw [Kc,Kc]
    have hU:U₀.map Uv=U:= by
      ext i j
      simp [U₀,KI,Uv]
    have hV:V₀.map Uv=V:= by
      ext i j
      simp [V₀,KI,Uv]
    rw [hU,hV]
    exact hB
  have hdet:S.det≠0:= by
    intro hz
    have he :=Uv.map_det S
    change Uv S.det=(S.map Uv).det at he
    rw [hS,hz,ox ,Ob] at he
    exact G0 he
  have hg: (S.map genericPoint).det≠0:= by
    change (genericPoint.mapMatrix S).det≠0
    rw [← genericPoint.map_det]
    have hinj:uW genericPoint :=
      (cy (vZ Parameter) lN).injective.comp
        (qM Parameter (vZ Parameter))
    intro hz
    exact hdet (hinj (hz.trans (ox genericPoint).symm))
  calc
    B.rank=(S.map genericPoint).rank := by
      rw [Mk hg,yJ]
    _≤(M.map genericPoint).rank := by
      rw [Kc,Kc]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
end
end Ge
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace Ge
noncomputable section
open K1 cu DP Polynomial
open scoped BigOperators Polynomial
def c4 :Prop :=
  ∀ {h:ℕ} {D:jF h} {Crt:zG D} (E :cAi D Crt)
    (s :lJ) (ι:Type) [p5 ι] (P:ι→Source),
    (∀ k,adk s (P k)) →
    ∃ n:ℕ,∃ M:sS (Fin n) ι Parameter,
      (∀ v :ι→L,(M.map Uv).mulVec v=0 ↔
        a0X s (Iy D) (OY Crt) (Du L P v)) ∧
      ∀ v :ι→lN,(M.map genericPoint).mulVec v=0 ↔
        a0X s (E.H.map genericPoint) (Ua genericPoint E.num E.den)
          (Du lN (fun k=>avv (genericPoint.comp (mD (R:=L))) (P k)) v)
private theorem cb9 {F:Type} [lI F] (s :lJ) {h:ℕ}
    {H :F[X]} {lift: (kq F)[X]} (G:bk5 h H lift)
    (P:Gm F)
    (hd : ∀ t,(pW ((aU (R:=kq F) -
        mD (cy F (kq F) (G.root t)))^(s.B+s.J)) :
      EM (kq F))∣forward H lift P) :
    a0X s H lift P:= by
  let r :Fin (2*h)→(kq F)[X] := fun t =>
    aU-Polynomial.C (cy F (kq F) (G.root t))
  have hr :Pairwise (Function.onFun t7 r) :=
    Polynomial.pairwise_coprime_X_sub_C
      ((cy F (kq F)).injective.comp G.distinct)
  have hcop:Pairwise (Function.onFun t7
      (fun t=>(pW (r t^(s.B+s.J)) :EM (kq F)))) := by
    intro t u hne
    exact ((hr hne).pow).map pW
  have hp:=Fintype.prod_dvd_of_coprime hcop hd
  have hprod:H.map (cy F (kq F)) = ∏ t,r t:= by
    rw [G.factorization,Polynomial.map_prod]
    simp [r]
  unfold a0X
  rw [hprod,← Finset.prod_pow,map_prod]
  exact hp
end
end Ge
end
section
namespace bay
noncomputable section
open K1 cu DP axj Polynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
def aER {A B:Type*} [c9 A] [c9 B]
    (f :A →+* pU B) :A[X] →+* pU (B[X]) :=
  oy ((wB mD).comp f) (n5 aU)
@[simp] theorem bwl {A B:Type*} [c9 A] [c9 B]
   (f :A →+* pU B) (a :A) :
   aER f (C a)=wB mD (f a) :=
  pL _ _
@[simp] theorem bNQ {A B:Type*} [c9 A] [c9 B]
   (f :A →+* pU B) :
   aER f aU=n5 Polynomial.X :=
  u8 _ _
theorem cph {A B R:Type*} [c9 A] [c9 B]
   [p9 R] [vi R A] [vi R B]
   (f :A →+* pU B) (g:A →ₗ[R] B) (r :ℕ)
   (hg : ∀ a,zg r (f a)=g a) (P:A[X]) :
   zg r (aER f P)=mapCoeffs g P:= by
 induction P using Lf with
 | add P Q hp hq=>simp only [map_add,hp,hq]
 | monomial n a =>
   rw [mapCoeffs_monomial,← Fa ,lV,pG,bwl,
     bNQ,← pG,PowerSeries.coeff_mul_C,MS ,hg,
     Fa]
theorem ddB {A B:Type*} [c9 A] [c9 B]
  (f :B →+* pU B) (g:A →+* B)
  (hf : ∀ a,f (g a)=n5 (g a)) (P:A[X]) :
  aER f (P.map g)=n5 (P.map g) := by
 have he : (aER f).comp (oK g) =
    PowerSeries.C.comp (oK g) := by
  apply p6
  · intro a
    simp [hf]
  · simp
 exact t6 he P
theorem gpS {A:Type*} [c9 A]
    (f :A →+* pU A) (hf : ∀ a,GB (f a)=a)
    (P:A[X]) :GB (aER f P)=P:= by
  have he :PowerSeries.constantCoeff.comp (aER f)=uJ A[X] := by
    apply p6
    · intro a
      have hfa :zg 0 (f a)=a :=
        (Up _).trans (hf a)
      simp [← Up,hfa]
    · simp
  exact t6 he P
def bhu (i:Fin 2) :qC →+* pU qC :=
 Polynomial.coeToPowerSeries.ringHom.comp (translation i).toRingHom
def awA (i:Fin 2) :Source →+* pU Source :=
 aER (aER (aER (bhu i)))
theorem gta (i:Fin 2) (r :ℕ) (Q:Source) :
  zg r (awA i Q)=awz i r Q:= by
 unfold awA awz
 apply cph (R:=L)
 intro P
 apply cph (R:=L)
 intro p
 apply cph (R:=L)
 intro a
 exact Polynomial.coeff_coe (φ:=translation i a) r
def aN2 (i:Fin 2) :qC →+* pU aQ :=
 (wB (cy qC aQ)).comp (bhu i)
theorem cTG (i:Fin 2) (P:qC) :
  GB (aN2 i P)=cy qC aQ P:= by
 have he :PowerSeries.constantCoeff.comp (aN2 i) =
    algebraMap qC aQ:= by
  apply Av
  · intro a
    simp [aN2,bhu,translation,vH]
  · intro j
    by_cases hj:j=i <;> simp [aN2,bhu,translation,hj]
 exact t6 he P
def awq (i:Fin 2) :aQ →+* pU aQ :=
  Pr (M:=NI qC) (S:=aQ)
    (g:=aN2 i) fun a =>
      PowerSeries.isUnit_iff_constantCoeff.mpr (by
        rw [cTG,isUnit_iff_ne_zero]
        simpa only [ox] using
          (qM qC aQ).ne (nonZeroDivisors.ne_zero a.prop))
@[simp] theorem dcU (i:Fin 2) (a :qC) :
   awq i (cy qC aQ a)=aN2 i a :=
  IsLocalization.lift_eq _ _
theorem gou (i:Fin 2) (a :aQ) :
  GB (awq i a)=a := by
 have he :PowerSeries.constantCoeff.comp (awq i)=uJ aQ:= by
  apply IsLocalization.ringHom_ext (M:=NI qC)
  apply xI
  intro P
  simp [cTG]
 exact t6 he a
theorem dcV (i:Fin 2) (a :L) :
  awq i (cy L aQ a)=n5 (cy L aQ a) := by
 rw [zc L qC aQ,dcU]
 simp [aN2,bhu,translation,vH]
theorem dcW (i j:Fin 2) (hji:j≠i) (P:L[X]) :
  awq i (MF j P)=n5 (MF j P) := by
 have he : (awq i).comp (MF j).toRingHom =
    PowerSeries.C.comp (MF j).toRingHom:= by
  apply p6
  · intro a
    change awq i (MF j (C a))=n5 (MF j (C a))
    simpa [MF] using dcV i a
  · change awq i (MF j aU)=n5 (MF j aU)
    simp [MF,aN2,bhu,translation,hji]
 exact t6 he P
theorem gov (i:Fin 2) (a :aQ)
   (ha :awq i a=n5 a) :
   awq i a⁻¹=n5 a⁻¹:= by
 by_cases hz :a=0
 · simp [hz]
 apply (isUnit_iff_ne_zero.mpr hz |>.map (n5 (R:=aQ))).mul_left_cancel
 rw [← ha,← lV,Np hz,vh,ha,← lV,Np hz,vh]
theorem a7N {R:Type*} [c9 R] (a b:R) :
  zE a (n5 b)=n5 b:= by
 apply PowerSeries.ext
 intro n
 cases n <;> simp [PowerSeries.coeff_C]
theorem fWs {R:Type*} [oD R] (a b:R)
  (F:pU R) (hF:GB F=b) :
  ∃ B,zE a F=n5 b+PowerSeries.C a*B:= by
 have hd: (PowerSeries.X:pU R)∣F-PowerSeries.C b:= by
  rw [PowerSeries.X_dvd_iff,Fz ,PowerSeries.constantCoeff_C,hF,J4]
 obtain ⟨U,hU⟩:=hd
 have he :=oz (zE a) hU
 rw [Fz ,a7N,lV,PowerSeries.rescale_X,t8] at he
 exact ⟨PowerSeries.X*zE a U,by rw [← he]; ring⟩
end
end bay
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace aY9
noncomputable section
open K1 cu DP Ge Polynomial
open scoped BigOperators Polynomial
def aVY {h:ℕ} (D:jF h) (i:Fin 2) :Parameter[X] :=
 (D.block i).map C+C (aU (R:=L))
def bfF {h:ℕ} (D:jF h) :Parameter[X] :=
 aVY D 0*aVY D 1
theorem b9t {h:ℕ} (D:jF h) (i:Fin 2) :
  (aVY D i).map Uv=D.block i:= by
 have hc:Uv.comp (C (R:=L))=uJ L :=
  xI fun a=>Ee
 rw [aVY,yl,oY ,hc,Bf ,oZ]
 simp [Uv]
theorem aVZ {h:ℕ} (hh:0<h) (D:jF h) (i:Fin 2) :
  IsMonicOfDegree (aVY D i) h:= by
 have hb:IsMonicOfDegree ((D.block i).map (C (R:=L))) h :=
  ⟨((D.monic i).natDegree_map _).trans (D.degree i),(D.monic i).map _⟩
 exact hb.add_right (by simpa using hh)
theorem b4F:uW genericPoint :=
 (cy (vZ Parameter) lN).injective.comp
   (qM Parameter (vZ Parameter))
abbrev alL:L →+* lN :=genericPoint.comp (C (R:=L))
abbrev adH {h:ℕ} (D:jF h) (i:Fin 2) :lN[X] :=
 (aVY D i).map genericPoint
private theorem b4y {h:ℕ} (D:jF h) (i:Fin 2) :
  adH D i=(D.block i).map alL+C (genericPoint aU) := by
 unfold adH aVY
 rw [yl,oY ,oZ]
theorem other_invol (i:Fin 2) :CI (CI i)=i:= by
 fin_cases i <;> decide
theorem gw0 {R:Type*} [AddCommMonoid R] (f :Fin 2→R) (i:Fin 2) :
   (∑ j,f j)=f i+f (CI i) := by
 rw [FQ]
 fin_cases i
 · rfl
 · exact add_comm _ _
theorem cIf {h:ℕ} (D:jF h) (i:Fin 2) :
   t7 (D.block i) (D.block (CI i)) := by
 fin_cases i
 · exact D.coprime
 · exact D.coprime.symm
private theorem dWs {h:ℕ} (hlo:0<h) (hhi:h<K1.p)
  (D:jF h) (i:Fin 2) : (D.block i).derivative≠0:= by
 let _:CharP L K1.p:=charP_of_injective_ringHom (cy K L).injective K1.p
 have hn: (h:L)≠0:= fun hz =>
  (not_le_of_gt hhi) (Nat.le_of_dvd hlo ((CharP.cast_eq_zero_iff _ _ _).mp hz))
 intro hd
 have he :=oz (fun f :L[X]=>f.coeff (h - 1)) hd
 have hh:h - 1+1=h:= by omega
 have hlead: (D.block i).coeff h=1 := by
  simpa only [← IU,D.degree i] using (D.monic i).leadingCoeff
 rw [coeff_derivative,hh,hlead,wY ,v8] at he
 have hcast: ((h - 1 :ℕ) :L)+1=(h:L) := by
  simpa only [Nat.cast_add,Nat.cast_one] using oz (fun n:ℕ=>(n:L)) hh
 exact hn (hcast.symm.trans he)
private theorem fX3 {h:ℕ} (D:jF h) (i:Fin 2) (x :L) :
  (adH D i).eval (alL x)≠0:= by
 rw [b4y,eval_add,eval_map_apply,Ee]
 change genericPoint (C ((D.block i).eval x))+genericPoint aU≠0
 rw [← ov,← ox Ge.genericPoint]
 intro he
 have hc:=oz (fun P:Parameter=>P.coeff 1) (b4F he)
 simp at hc
private theorem b3p {h:ℕ} (D:jF h) (i:Fin 2)
  {α:lN} (hr : (adH D i).eval α=0)
  {f :L[X]} (hf :f≠0) : (f.map alL).eval α≠0:= by
 intro he
 obtain ⟨x,rfl⟩:=(KA f).mem_range_of_isRoot hf he
 exact fX3 D i x hr
private theorem eIl {h:ℕ} (hh:0<h) (D:jF h)
  (i:Fin 2) {α:lN} (hr : (adH D i).eval α=0) :
  (adH D (CI i)).eval α≠0:= by
 have hdiff :D.block i - D.block (CI i)≠0:= by
  intro he
  have hu:=cIf D i
  rw [← sub_eq_zero.mp he] at hu
  exact not_isUnit_of_natDegree_pos _ (by simpa [D.degree] using hh) (isCoprime_self.mp hu)
 intro ho
 apply b3p D i hr hdiff
 rw [Kv,eval_sub]
 rw [b4y,eval_add,Ee] at hr ho
 exact sub_eq_zero.mpr (add_right_cancel (hr.trans ho.symm))
private theorem dWo {h:ℕ} (hlo:0<h) (hhi:h<K1.p)
  (D:jF h) (i:Fin 2) {α:lN}
  (hr : (adH D i).eval α=0) : (adH D i).derivative.eval α≠0:= by
 rw [b4y,JK,Ef ,u5 ,zi]
 exact b3p D i hr (dWs hlo hhi D i)
private theorem cHS {h:ℕ} (hh:0<h) (D:jF h)
  (i:Fin 2) {α:lN} (hr : (adH D i).eval α=0) :
  ((D.constant i).map alL).eval α≠0:= by
 refine b3p D i hr ?_
 intro he
 have hc:=(D.determinant i).of_mul_left_right
 rw [he,isCoprime_zero_left] at hc
 exact not_isUnit_of_natDegree_pos _ (by simpa [D.degree] using hh) hc
def gq6 {h:ℕ} (hlo:0<h) (hhi:h<K1.p) (D:jF h)
    (lift: (kq lN)[X])
    (hcentre : ∀ i α,(adH D i).eval α=0 →
      ((D.constant i).map alL).eval α≠0 →
      lift.eval (cy lN (kq lN) α) =
        residue i (-((D.offset i).map alL).eval α)
          (((D.constant i).map alL).eval α) (((D.slope i).map alL).eval α)) :
    bk5 h ((bfF D).map genericPoint) lift:= by
  classical
  let H :=(bfF D).map genericPoint
  have hblocks :H=adH D 0*adH D 1 := by
    simp only [H,bfF,qm]
  have hmonic:H.Monic :=
    (((aVZ hlo D 0).monic.mul (aVZ hlo D 1).monic).map _)
  have hdegree :H.natDegree=2*h:= by
    have hd (i:Fin 2) : (adH D i).natDegree=h :=
      ((aVZ hlo D i).monic.natDegree_map _).trans
        (aVZ hlo D i).natDegree_eq
    have hm (i:Fin 2) : (adH D i).Monic :=
      (aVZ hlo D i).monic.map _
    rw [hblocks,natDegree_mul (hm 0).ne_zero (hm 1).ne_zero,hd,hd]
    omega
  have hside (α:lN) (hr :H.eval α=0) :
      ∃ i,(adH D i).eval α=0:= by
    rw [hblocks,eval_mul,mul_eq_zero] at hr
    exact hr.elim (fun h=>⟨0,h⟩) (fun h=>⟨1,h⟩)
  have hsimple (α:lN) (hr :H.eval α=0) :H.derivative.eval α≠0:= by
    obtain ⟨i,hi⟩:=hside α hr
    have hn:=dWo hlo hhi D i hi
    have ho:=eIl hlo D i hi
    rw [hblocks,yU,eval_add,eval_mul,eval_mul]
    fin_cases i
    · change (adH D 0).eval α=0 at hi
      change (adH D 1).eval α≠0 at ho
      rw [hi,zero_mul,u5]
      exact z7 hn ho
    · change (adH D 1).eval α=0 at hi
      change (adH D 0).eval α≠0 at ho
      rw [hi,vj,v9]
      exact z7 ho hn
  have hsep:H.Separable := by
    apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed lN lN H H.derivative).mpr
    intro α
    by_cases he :H.eval α=0
    · exact Or.inr (by simpa using hsimple α he)
    · exact Or.inl (by simpa using he)
  let s :=H.roots.toFinset
  have hcard:Cy s=2*h:= by
    rw [Pv,Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      ← (KA H).natDegree_eq_card_roots,hdegree]
  let e :Fin (2*h) ≃ s :=(LP hcard).symm
  let α:Fin (2*h)→lN := fun t=>(e t).val
  have hroot (t:Fin (2*h)) :H.eval (α t)=0 :=
    (mem_roots hmonic.ne_zero).mp (Multiset.mem_toFinset.mp (e t).property)
  choose i hi using fun t=>hside (α t) (hroot t)
  refine ⟨α,i,_,_,_,Subtype.val_injective.comp e.injective,?_,hroot,
    fun t=>hsimple _ (hroot t),fun t=>cHS hlo D _ (hi t),
    fun t=>hcentre _ _ (hi t) (cHS hlo D _ (hi t))⟩
  rw [e.prod_comp (fun x=>aU - C x.val)]
  rw [Finset.prod_coe_sort s (fun x=>aU - C x)]
  have hs :s.val=H.roots := by
    exact (Multiset.toFinset_val _).trans (nodup_roots hsep).dedup
  simpa only [Finset.prod,hs] using (KA H).eq_prod_roots_of_monic hmonic
end
end aY9
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace anc
noncomputable section
open cu DP Ge Polynomial
open scoped BigOperators Polynomial
def substitute {R A:Type*} [c9 R] [c9 A]
    (base :R →+* A) (y v :A) :R[X][X] →+* A :=
  oy (oy base y) v
def GV {F:Type} [lI F] (α:F) (z :kq F) :
    Gm F →+* EM (kq F) :=
  let xα:=cy F (kq F) α
  let coeffs :=(PM xα).toRingHom.comp
    (oK (cy (i5 F) (kq F)))
  substitute (pW.comp coeffs)
    (mD aU +pW (mD z)) aU
def aJ3 {R:Type} [c9 R] :EM R →+* EM R :=
 let x :=pW (aU (R:=R))
 let y :EM R:=mD aU
 substitute pW (x*y) (x*aU +y)
def aIP {R:Type} [c9 R] (s :lJ)
    (f : (q:jJ s)→NQ s q.val→R[X]) :EM R :=
  ∑ q:jJ s,∑ j:NQ s q.val,
    mD (mD (f q j)*aU ^(q.val - j.val)) *
      aU ^j.val
abbrev Shift (s :lJ) (q:jJ s) :=Fin (s.B - q.val+1)
def bHT {s :lJ} (q:jJ s) (j:NQ s q.val)
    (p:Shift s q) :ℕ :=
  q.val - j.val+p.val
def beE {F:Type} [lI F] (α:F) (P:Gm F) (j i:ℕ) : (i5 F)[X] :=
 EK (cy F (i5 F) α) ((P.coeff j).coeff i)
def aVG {F:Type} [lI F] (s :lJ) (α:F) (z :kq F)
    (P:Gm F) (q:jJ s) (j:NQ s q.val) : (kq F)[X] :=
  ∑ p:Shift s q,
    mD ((Nat.choose (bHT q j p) (q.val - j.val) :kq F)*z^p.val) *
      (beE α P j.val (bHT q j p)).map (cy (i5 F) (kq F))
def b6l {F:Type} [lI F] (α:F) (j i t:ℕ) :
    Gm F →ₗ[F] i5 F :=
  ((Dz (i5 F) t).restrictScalars F).comp
    (((EK (cy F (i5 F) α)).restrictScalars F).comp
      (((Dz ((i5 F)[X]) i).restrictScalars F).comp
        ((Dz (((i5 F)[X])[X]) j).restrictScalars F)))
end
end anc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace aY9
noncomputable section
open cu DP Ge Module Polynomial
open scoped Polynomial
private def avV {R:Type*} [oD R] {b:R[X]} {n:ℕ}
   (hb:b.Monic) (hd:b.natDegree=n) :Basis (Fin n) R (NW b) :=
 (JQ hb).reindex (finCongr hd)
private def Nn {R:Type*} [oD R] {b:R[X]} {n:ℕ}
  (hb:b.Monic) (hd:b.natDegree=n) (a :R[X]) :sS (Fin n) (Fin n) R :=
 R9 (avV hb hd) (sH b a)
private theorem aOT {R:Type*} [oD R] {b:R[X]} {n:ℕ}
   (hb:b.Monic) (hd:b.natDegree=n) (a :R[X]) (i j:Fin n) :
   Nn hb hd a i j=((a*aU (R:=R)^(j:ℕ)) %ₘ b).coeff i:= by
 have hpow (k :Fin b.natDegree) :
     (JQ hb) k=AdjoinRoot.root b^(k :ℕ) :=
   (XJ hb).basis_eq_pow k
 unfold Nn
 rw [SW]
 unfold avV
 rw [Basis.reindex_apply,hpow,← AdjoinRoot.mk_X,← pG,← lV,
   XG,SC,
   Nq]
 rfl
private theorem fVv {R S:Type*} [oD R] [lI S]
   (point :R →+* S) {b a :R[X]} (hb:b.Monic)
   (hcop:t7 (a.map point) (b.map point)) :
   ∃ (d:R) (u:R[X]),point d≠0∧b∣a*u - C d:= by
 let basis :=avV hb rfl
 let M:=Nn hb rfl a
 let d:=M.det
 let d' := (hb.natDegree_map point)
 have hmap :M.map point=Nn (hb.map point) d' (a.map point) := by
   ext i j
   change point (Nn hb rfl a i j)= _
   rw [aOT,aOT,← t9,F9 point hb,
     qm,Dw ,Au]
 obtain ⟨v,w,hvw⟩:=hcop
 have hinv :sH (b.map point) v*sH (b.map point) (a.map point)=1 := by
   simpa only [ov,lV,Te,vj,u5 ,vh] using
     oz (sH (b.map point)) hvw
 have hmat :Nn (hb.map point) d' v*M.map point=1 := by
   rw [hmap]
   unfold Nn
   rw [← lV,hinv,vh]
 have hd:point d≠0:= by
   have he :=oz Matrix.det hmat
   rw [Matrix.det_mul,Ob] at he
   change _ *(point.mapMatrix M).det=1 at he
   rw [← point.map_det] at he
   intro hz
   change point M.det=0 at hz
   rw [hz,vj] at he
   exact G0 he
 let x :=basis.equivFun.symm (M.cramer (basis.equivFun 1))
 have hsol:sH b a*x=d•(1 :NW b) := by
   apply basis.equivFun.injective
   have hv :=X4 basis (sH b a) x
   change M.mulVec (basis.repr x) = ⇑(basis.repr (sH b a*x)) at hv
   rw [← G6,← G6,
     show basis.equivFun x=M.cramer (basis.equivFun 1) from basis.equivFun.apply_symm_apply _,
     WX] at hv
   rw [x7]
   exact hv.symm
 obtain ⟨u,hu⟩:=Xp x
 refine ⟨d,u,hd,AdjoinRoot.mk_eq_zero.mp ?_⟩
 rw [Fz ,lV,hu,hsol,AdjoinRoot.mk_C,yB,FK]
 exact J4 _
abbrev Uw:i5 Parameter →+* i5 L:=oj Uv
private abbrev amd:i5 L →+* i5 Parameter :=oj (C (R:=L))
private theorem de1 :Uw.comp amd=uJ _:= by
 apply Av <;> simp [oq,Uv]
private theorem cZv (f : (i5 L)[X]) :
  (f.map amd).map Uw=f := by
 rw [oY ,de1,Bf]
def aie {F:Type} [lI F] (point :Parameter →+* F) :
    i5 Parameter →+* kq F :=
  (cy (i5 F) (kq F)).comp (oj point)
theorem bNA {F:Type} [lI F] (point :Parameter →+* F)
  {d:i5 Parameter} (hd:oj point d≠0) :aie point d≠0 :=
 fun hz=>hd ((qM (i5 F) (kq F))
  (hz.trans (ox (cy (i5 F) (kq F))).symm))
private theorem bWd {F:Type*} [lI F] {a b:F} (ha :a≠0)
  (P:F[X]) :C ((a*b)⁻¹)*(C a*P)=C (b⁻¹)*P:= by
 rw [← t8 ,← lV]
 congr 2
 rw [mul_inv_rev,t8 ,Mz ha,FK]
theorem cXv {F:Type} [lI F] (point :Parameter →+* F)
   (N M: (i5 Parameter)[X]) (d e :i5 Parameter)
   (hd:oj point d≠0) (he :oj point e≠0) :
   Ua point (C e*N+C d*M) (d*e) =
     Ua point N d+Ua point M e := by
 simp only [Ua,Ar]
 change C ((aie point (d*e))⁻¹)*(C e*N+C d*M).map (aie point) =
   C ((aie point d)⁻¹)*N.map (aie point) +
   C ((aie point e)⁻¹)*M.map (aie point)
 rw [yl,qm,qm,
   oZ,oZ,lV (aie point),Gn]
 congr 1
 · rw [t4 (aie point d) (aie point e),bWd (bNA point he)]
 · exact bWd (bNA point hd) _
abbrev ayS {h:ℕ} (D:jF h) (i:Fin 2) : (i5 Parameter)[X] :=
 (aVY D i).map nq
abbrev aft:L →+* i5 Parameter :=MvPolynomial.C.comp (C (R:=L))
def aNK {h:ℕ} (D:jF h) (i:Fin 2) : (i5 Parameter)[X] :=
 (D.constant i).map aft+C (nX i)*(D.slope i).map aft
def bp0 {h:ℕ} (D:jF h) (i:Fin 2) : (i5 Parameter)[X] :=
 C (nX i)*(D.offset i).map aft
private theorem b8C {h:ℕ} (D:jF h) (i:Fin 2) :
   (ayS D i).map Uw=(D.block i).map MvPolynomial.C:= by
 have hc:Uw.comp (nq:Parameter →+* i5 Parameter) =
     (nq:L →+* i5 L).comp Uv :=
   xI fun x=>JM Uv x
 rw [ayS,oY ,hc,← oY ,b9t]
private theorem cqi :
  Uw.comp aft=(nq:L →+* i5 L) := by
 ext x
 simp [oq,Uv]
private def aRj:i5 L →+* L:=qx fun _=>0
private theorem gNa (f :L[X]) :
  (f.map nq).map aRj=f := by
 have h:aRj.comp nq=uJ L :=
  xI fun c=>RD _
 rw [oY ,h,Bf]
private def Wu (i:Fin 2) :L[X] →+* i5 L :=
 oy nq (nX i)
private theorem edK (i:Fin 2) :
  (cy (i5 L) (kq L)).comp (Wu i)=(MF i).toRingHom:= by
 apply p6 <;>
  simp [Wu,MF,aeval_def,oq,vH,
    zc L (i5 L) (kq L)]
private theorem gNu (i:Fin 2) :
  aRj.comp (Wu i)=sI 0:= by
 apply p6 <;> simp [aRj,Wu,oq]
structure bQl {h:ℕ} (D:jF h) (Crt:zG D) (i:Fin 2) where
 den:i5 Parameter
 num : (i5 Parameter)[X]
 specialDen:Uw den≠0
 other_dvd:ayS D (CI i)∣num
 congruence :ayS D i∣aNK D i*num+C den*bp0 D i
 specialLift:Ua Uv num den =
  (MF i (Crt.denominator i))⁻¹•(Crt.numerator i).map (MF i)
set_option maxHeartbeats 800000 in
def a1P {h:ℕ} (hh:0<h) (D:jF h) (Crt:zG D) (i:Fin 2) :
    bQl D Crt i:=Classical.choice (by
  let b:=ayS D i
  let e :=ayS D (CI i)
  let a :=aNK D i*e
  let q:=bp0 D i
  let z :=aRj.comp Uw
  let d₀:=Wu i (Crt.denominator i)
  let N₀:=(Crt.numerator i).map (Wu i)
  have hconst:=(D.determinant i).of_mul_left_right
  have hd₀:d₀≠0:= by
    intro he
    have hz :aRj d₀=(Crt.denominator i).eval 0 :=
      t6 (gNu i) _
    rw [he,ox] at hz
    exact Crt.regular i 0 (by simpa using hconst) hz.symm
  have hb:b.Monic:=(aVZ hh D i).monic.map _
  have hzb (j:Fin 2) : (ayS D j).map z=D.block j:= by
    change (ayS D j).map (aRj.comp Uw)= _
    rw [← oY ,b8C,gNa]
  have hza :a.map z=D.constant i*D.block (CI i) := by
    have hc:z.comp aft=uJ L:= by
      change (aRj.comp Uw).comp aft=uJ L
      rw [PD,cqi]
      exact xI fun c=>RD _
    have hX:z (nX i)=0:= by simp [z,aRj]
    simp only [a,e,aNK,qm,yl,oY ,
      oZ,hc,Bf ,hX,C_0,zero_mul,u5 ,hzb]
  have hc:t7 (a.map z) (b.map z) := by
    change t7 (a.map z) ((ayS D i).map z)
    rw [hza,hzb i]
    exact hconst.mul_left (cIf D i).symm
  obtain ⟨d,u,hd,hu⟩:=fVv z hb hc
  have hds :Uw d≠0:= fun he=>hd (by simp [z,he])
  have hseedConst: (Wu i).comp C=(nq:L →+* i5 L) := by
    ext c
    simp [Wu]
  have hseedX:Wu i aU=nX i:= by simp [Wu]
  obtain ⟨t₀,ht₀⟩:e.map Uw∣N₀:= by
    change (ayS D (CI i)).map Uw∣N₀
    rw [b8C]
    simpa only [vG,oY ,hseedConst,N₀] using
      vk (oK (Wu i)) (Crt.other_dvd i)
  obtain ⟨w₀,hw₀⟩:b.map Uw∣a.map Uw*t₀+C d₀*q.map Uw:= by
    have he : (aNK D i).map Uw =
        (D.constant i).map nq +
          C (nX i)*(D.slope i).map MvPolynomial.C:= by
      simp [aNK,yl,qm,oY ,cqi]
    have hq:q.map Uw=C (nX i)*(D.offset i).map MvPolynomial.C:= by
      simp [q,bp0,qm,oY ,cqi]
    dsimp only [a,b]
    rw [qm,t8 ,← ht₀,he,hq,b8C,
      ← t8 (C d₀),← lV C]
    simpa only [vG,yl,qm,oZ,
      oY ,hseedConst,lV (Wu i),hseedX,N₀,d₀] using
      vk (oK (Wu i)) (Crt.congruence i)
  let r :=a*t₀.map amd+C (amd d₀)*q - b*w₀.map amd
  let t:=C d*t₀.map amd - u*r
  let N :=e*t
  let den:=d*amd d₀
  have hseed (c:i5 L) :Uw (amd c)=c :=
    t6 de1 c
  have hden:Uw den=Uw d*d₀:= by
    dsimp only [den]
    rw [lV,hseed]
  have hr :r.map Uw=0:= by
    simp only [r,Kv,yl,qm,oZ,
      cZv,hseed,hw₀,J4]
  have hN :N.map Uw=C (Uw d)*N₀:= by
    simp only [N,t,qm,Kv,oZ,hr,vj,
      sub_zero,cZv,ht₀]
    ring
  refine ⟨⟨den,N,by rw [hden]; exact z7 hds hd₀,Pj _ _,?_,?_⟩⟩
  · change b∣aNK D i*N+C den*q
    have he :aNK D i*N+C den*q =
        b*(C d*w₀.map amd)-(a*u - C d)*r := by
      simp only [N,den,t,r,a,lV]
      ring
    rw [he]
    exact dvd_sub (Pj _ _) (hu.mul_right _)
  · have hfd:=bNA Uv hds
    rw [Ua,Ar,← oY]
    let f :=cy (i5 L) (kq L)
    change f (Uw d)≠0 at hfd
    change C ((f (Uw den))⁻¹)*(N.map Uw).map f =
      (MF i (Crt.denominator i))⁻¹•(Crt.numerator i).map (MF i)
    rw [hden,hN,lV f,qm,oZ,bWd hfd]
    dsimp only [N₀,d₀]
    rw [oY ,Ar]
    change C (((f.comp (Wu i)) (Crt.denominator i))⁻¹)*_ = _
    rw [edK]
    rfl)
end
end aY9
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace bzR
noncomputable section
open K1 cu DP Ge Polynomial
open scoped BigOperators Polynomial
abbrev JH {R S:Type} [c9 R] [c9 S] (f :R →+* S) :
  EM R →+* EM S :=
 oK (oK (oK f))
abbrev aee {F:Type} [lI F] (point :Parameter →+* F) :
   i5 Parameter →+* kq F :=
 (cy (i5 F) (kq F)).comp (oj point)
abbrev awj {R:Type} [c9 R] (d:R) :EM R :=
 pW (mD d)
private abbrev jU {R:Type} [c9 R] :EM R :=
 mD (aU (R:=R[X]))
private def bJ1 {R:Type} [c9 R] (H N :R[X]) :EM R :=
 pW H*jU + pW N
private def bPJ {R:Type} [c9 R] (H N :R[X]) :EM R :=
 pW H*aU +pW H.derivative*jU + pW N.derivative
private def bXi {R:Type} [c9 R] (H N :R[X]) (d:R) :EM R :=
 awj d*(pW H*jU)+pW N
private def bXj {R:Type} [c9 R] (H N :R[X]) (d:R) :EM R :=
 awj d*(pW H*aU +pW H.derivative*jU) +
  pW N.derivative
def BA (s :lJ) (H :Parameter[X]) (N : (i5 Parameter)[X])
    (d:i5 Parameter) (P:Source) :Gm Parameter :=
  let h:=H.map (nq (σ:=Fin 2))
  let y :=bXi h N d
  let v :=bXj h N d
  ∑ j∈P.support,∑ i∈(P.coeff j).support,
    awj d^(s.B-(i+j)) *
      (pW (((P.coeff j).coeff i).map (oj (mD (R:=L)))) *
        y ^i*v^j)
private theorem bH0 {R S:Type} [c9 R] [c9 S]
  (f :R →+* S) (q:R[X]) :
  JH f (pW q)=pW (q.map f) := by
 simp only [JH,pW,oq,vG,oZ]
private theorem b6K {R S:Type} [c9 R] [c9 S]
  (f :R →+* S) :
  JH f (jU:EM R)=(jU:EM S) := by
 simp only [JH,vG,oZ,Au]
private theorem cVT {R S:Type} [c9 R] [c9 S]
  (f :R →+* S) :
  JH f (aU:EM R)=(aU:EM S) :=
 Au _
private theorem edB {F:Type} [lI F] (H :F[X]) (N : (kq F)[X])
   (q: (i5 F)[X]) :
   Ge.forward H N (pW q) =
     pW (q.map (cy (i5 F) (kq F))) := by
 change (C (C q)).eval₂ _ _ = _
 rw [pL]
 change (C q).eval₂ _ _ = _
 rw [pL]
 rfl
private theorem edD {F:Type} [lI F] (H :F[X]) (N : (kq F)[X]) :
   Ge.forward H N jU =
     bJ1 (H.map (cy F (kq F))) N := by
 change (C (aU (R:=(i5 F)[X]))).eval₂ _ _ = _
 rw [pL]
 change Polynomial.X.eval₂ _ _ = _
 rw [u8]
 rfl
private theorem edF {F:Type} [lI F] (H :F[X]) (N : (kq F)[X]) :
   Ge.forward H N aU =
     bPJ (H.map (cy F (kq F))) N := by
 change Polynomial.X.eval₂ _ _ = _
 rw [u8]
 rfl
private theorem d2i {A T:Type} [c9 A] [c9 T]
   (f :EM A →+* T) (P:EM A) :
   f P = ∑ j∈P.support,∑ i∈(P.coeff j).support,
     f (pW ((P.coeff j).coeff i))*f jU^i*f aU ^j:= by
 conv_lhs=>rw [P.as_sum_support_C_mul_X_pow]
 simp only [qG,lV,pG]
 apply p7 rfl
 intro j _
 rw [← EP]
 congr 1
 conv_lhs=>rw [(P.coeff j).as_sum_support_C_mul_X_pow]
 simp only [qG,lV,pG,pW,oq,jU]
private theorem dVB {s :lJ} {P:Source} (hP:adk s P)
  {j i:ℕ} (hi:i∈(P.coeff j).support) :i+j≤ s.B:= by
 let q:=(P.coeff j).coeff i
 have hn:q≠0:=Polynomial.mem_support_iff.mp hi
 by_contra hb
 apply hn
 apply pQ
 intro a
 rw [v8]
 apply y5
 intro e
 change aQu P j i a e=(0:i5 L).coeff e
 simp only [In,Hw]
 by_contra he
 exact hb (hP j i a e he).1
private theorem cXE {F:Type} [lI F] (point :Parameter →+* F)
  (N : (i5 Parameter)[X]) (d:i5 Parameter) (hd:oj point d≠0) :
  mD (aee point d)*Ua point N d=N.map (aee point) := by
 have hz :aee point d≠0 :=
  fun h=>hd (qM (i5 F) (kq F) (h.trans (ox _).symm))
 change C (aee point d)*((aee point d)⁻¹•N.map (aee point)) =
  N.map (aee point)
 rw [Ar,← t8 ,← lV,Np hz,vh,wY]
theorem bIS {F:Type} [lI F] (point :Parameter →+* F) (H :Parameter[X]) :
  (H.map (nq (σ:=Fin 2))).map (aee point) =
    (H.map point).map (cy F (kq F)) := by
 simp only [oY]
 congr 1
 apply xI
 intro a
 simp only [aee,oq,JM]
 exact (zc F (i5 F) (kq F) (point a)).symm
private theorem gma {R:Type} [c9 R] (d c y v :R)
   {B i j:ℕ} (hb:i+j≤B) :
   d^(B-(i+j))*(c*(d*y)^i*(d*v)^j) =
     d^B*(c*y ^i*v^j) := by
 have he :B-(i+j)+i+j=B:= by omega
 conv_rhs=>rw [← he,yQ d (B-(i+j)+i),yQ d (B-(i+j))]
 rw [GY ,GY]
 ring
set_option maxHeartbeats 800000 in
theorem dLM {F:Type} [lI F] (point :Parameter →+* F)
    (s :lJ) (H :Parameter[X]) (N : (i5 Parameter)[X])
    (d:i5 Parameter) (hd:oj point d≠0) (P:Source) (hP:adk s P) :
    JH (aee point) (BA s H N d P) =
      awj (aee point d)^s.B *
        Ge.forward (H.map point) (Ua point N d)
          (avv (point.comp (mD (R:=L))) P) := by
  let f :=aee point
  let A' := (H.map point).map (cy F (kq F))
  let N' := Ua point N d
  let D:=awj (f d)
  have hA: (H.map (nq (σ:=Fin 2))).map f=A' := bIS point H
  have hN :pW (N.map f)=D *pW N' := by
    rw [← cXE point N d hd]
    exact lV pW _ _
  have hdN :pW (N.derivative.map f)=D *pW N'.derivative := by
    have he :=oz Polynomial.derivative (cXE point N d hd)
    rw [yU,Ef ,zero_mul,v9,zi] at he
    rw [← he]
    exact lV pW _ _
  have hy :JH f (bXi (H.map nq) N d)=D *bJ1 A' N' := by
    simp only [bXi,bJ1,ov,lV,awj,bH0,
      oZ,b6K,hA,hN,D,Gn]
  have hv :JH f (bXj (H.map nq) N d)=D *bPJ A' N' := by
    simp only [bXj,bPJ,ov,lV,awj,bH0,
      oZ,b6K,cVT,← zi (H.map nq) f,hA,hdN,
      D,Gn,add_assoc]
  let g:=(Ge.forward (H.map point) N').toRingHom.comp
    (avv (point.comp (mD (R:=L))))
  have hgC (q: (i5 L)[X]) :
      g (pW q) =
        pW ((q.map (oj (mD (R:=L)))).map f) := by
    change (Ge.forward (H.map point) N')
      (JH (oj (point.comp (mD (R:=L)))) (pW q))= _
    rw [bH0,edB]
    congr 1
    apply pQ
    intro a
    simp only [t9,f,oq,MvPolynomial.map_map]
  have hgy :g jU=bJ1 A' N' := by
    change (Ge.forward (H.map point) N')
      (JH (oj (point.comp (mD (R:=L)))) jU)= _
    rw [b6K,edD]
  have hgv :g aU=bPJ A' N' := by
    change (Ge.forward (H.map point) N')
      (JH (oj (point.comp (mD (R:=L)))) aU)= _
    rw [cVT,edF]
  change JH f (BA s H N d P)=D^s.B*g P
  rw [d2i g P]
  simp only [BA,qG,lV,pG,awj,bH0,
    oZ,hy,hv,hgC,hgy,hgv,FR]
  apply p7 rfl
  intro j _
  apply p7 rfl
  intro i hi
  exact gma D _ _ _ (dVB hP hi)
end
end bzR
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace anc
noncomputable section
open cu DP Ge Polynomial
open scoped BigOperators Polynomial
@[simp] theorem efk {F:Type} [lI F] (α:F) (j i t:ℕ)
   (P:Gm F) :
   b6l α j i t P=(beE α P j i).coeff t:=rfl
end
end anc
end
section
namespace bay
noncomputable section
open K1 cu DP Polynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
abbrev VD:=aQ[X]
def X9 (P:L[X]) :VD :=
 P.map (cy L aQ)
def YH (i:Fin 2) (E :VD) :
    VD →+* pU VD :=
  (zE (E^2)).comp (aER (awq i))
theorem bNm (i:Fin 2) (E :VD) (P:L[X]) :
  YH i E (X9 P)=n5 (X9 P) := by
 unfold YH X9
 rw [oq,ddB _ _ (dcV i),a7N]
theorem dcg (i:Fin 2) (E :VD) (P:L[X]) :
   YH i E (X9 P).derivative =
     n5 (X9 P).derivative := by
 change YH i E ((P.map _).derivative)=n5 ((P.map _).derivative)
 rw [zi]
 exact bNm i E P.derivative
private def ayu {h:ℕ} {D:jF h} (Crt:zG D) (j:Fin 2) :VD :=
 C (MF j (Crt.denominator j))⁻¹*(Crt.numerator j).map (MF j).toRingHom
private theorem dRF {h:ℕ} {D:jF h} (Crt:zG D) (i:Fin 2) :
    OY Crt=ayu Crt i+ayu Crt (CI i) := by
  have he (j:Fin 2) :
      (MF j (Crt.denominator j))⁻¹•(Crt.numerator j).map (MF j) =
        ayu Crt j:=Ar _
  simp only [OY,FQ,he]
  fin_cases i
  · rfl
  · exact add_comm _ _
private theorem dRD {h:ℕ} {D:jF h} (Crt:zG D) (i:Fin 2) :
  ∃ W,ayu Crt i=X9 (D.block (CI i))*W:= by
 obtain ⟨N,hN⟩:=Crt.other_dvd i
 have hf : (MF i).toRingHom.comp (C (R:=L))=cy L aQ:= by
  apply xI
  intro a
  exact (MF i).commutes a
 refine ⟨C (MF i (Crt.denominator i))⁻¹*N.map (MF i).toRingHom,?_⟩
 rw [ayu,hN,qm,oY ,hf,X9]
 exact mul_left_comm _ _ _
private theorem dRE {h:ℕ} {D:jF h} (Crt:zG D) (i j:Fin 2)
    (hji:j≠i) (E :VD) :
    YH i E (ayu Crt j)=n5 (ayu Crt j) ∧
    YH i E (ayu Crt j).derivative=n5 (ayu Crt j).derivative := by
  have hd:awq i (MF j (Crt.denominator j))⁻¹ =
      n5 (MF j (Crt.denominator j))⁻¹ :=
    gov _ _ (dcW i j hji _)
  have hm (P:lz L[X]) :
      YH i E (C (MF j (Crt.denominator j))⁻¹*P.map (MF j).toRingHom) =
        n5 (C (MF j (Crt.denominator j))⁻¹*P.map (MF j).toRingHom) := by
    have hmap :=ddB (awq i) (MF j).toRingHom
      (dcW i j hji) P
    simp only [YH,oq,lV,bwl,hd,
      Df ,hmap,a7N]
  exact ⟨hm _,by
    simp only [ayu,yU,Ef ,zero_mul,v9,zi]
    exact hm _⟩
private theorem fTK {h:ℕ} (D:jF h) (i:Fin 2) :
  IE D =X9 (D.block i)*X9 (D.block (CI i)) := by
 fin_cases i <;> simp [IE,Iy,X9,CI,qm,
  t4]
theorem dRG {h:ℕ} {D:jF h} (Crt:zG D) (i:Fin 2) :
    let E :=X9 (D.block i)
    let H :=IE D
    let ρ:=YH i E
    let C₀:=n5 (R:=VD)
    ∃ B B₁:pU VD,
      ρ (OY Crt)=C₀ (OY Crt)+C₀ H*C₀ E*B ∧
      ρ (OY Crt).derivative=C₀ (OY Crt).derivative +
        (C₀ H.derivative*C₀ E - C₀ H*C₀ E.derivative)*B+C₀ H*C₀ E*B₁:= by
  dsimp only
  let E :=X9 (D.block i)
  let G:=X9 (D.block (CI i))
  let ρ:=YH i E
  let C₀:=n5 (R:=VD)
  have hH :IE D =E*G:=fTK D i
  obtain ⟨W,hW⟩:=dRD Crt i
  have heq :OY Crt=G*W+ayu Crt (CI i) :=
    (dRF Crt i).trans (oz (· + ayu Crt (CI i)) hW)
  have hne :CI i≠i:= by fin_cases i <;> decide
  obtain ⟨hfixed,hfixed'⟩:=dRE Crt i (CI i) hne E
  have hG:ρ G=C₀ G:=bNm _ _ _
  have hG' : ρ G.derivative=C₀ G.derivative :=dcg _ _ _
  have hc (P:VD) : ∃ U,ρ P=C₀ P+C₀ (E^2)*U :=
    fWs _ _ _
      (gpS _ (gou i) P)
  obtain ⟨B,hB⟩:=hc W
  obtain ⟨B₁,hB₁⟩:=hc W.derivative
  change ρ _ = _ at hfixed hfixed'
  change ∃ U V,ρ _=C₀ _+C₀ _ *C₀ _ *U∧ρ _ = _+_ *U + _ *V
  refine ⟨B,B₁,?_,?_⟩
  · rw [heq,hH,ov ρ,lV ρ,hG,hB,hfixed]
    simp only [ov,lV,pG]
    ring
  · rw [heq,hH,JK,yU,yU]
    simp only [ov,lV,hG,hG',hB,hB₁,hfixed',pG]
    ring
end
end bay
end
section
set_option backward.isDefEq.respectTransparency false
namespace cyS
noncomputable section
open K1 cu DP axj Polynomial
open scoped Polynomial
private abbrev sx :Source :=C (C (aU (R:=qC)))
private abbrev sy :Source :=C (aU (R:=qC[X]))
private abbrev sv :Source :=aU
private abbrev Sl:qC →+* Source :=C.comp (C.comp C)
private theorem cbD (x y :L) :Km x y sx=sx+algebraMap L Source x := by
 change qy _ _ (C (C (aU (R:=qC))))= _
 rw [pL]
 change qy _ _ (C (aU (R:=qC)))= _
 rw [pL]
 change (cy qC[X] Source)
  (qy _ _ (aU (R:=qC)))= _
 rw [u8 ,ov]
 rfl
private theorem cbE (x y :L) :
  Km x y sy=cy L Source y+sx*sv+sy := by
 change qy _ _ (C (aU (R:=qC[X])))= _
 rw [pL]
 change qy _ _ (aU (R:=qC[X]))= _
 rw [u8]
 rfl
private theorem cbC (x y :L) :Km x y sv=sv := by
 change qy _ _ (aU:Source)= _
 rw [u8]
private theorem bKs (x y :L) (p:qC) :
  Km x y (Sl p)=Sl p:= by
 change qy _ _ (C (C (C p)))= _
 rw [pL]
 change qy _ _ (C (C p))= _
 rw [pL]
 change (cy qC[X] Source) (qy _ _ (C p))= _
 rw [pL]
 rfl
private theorem cqb {T:Type*} [p9 T] {f g:Source →+* T}
   (hSeed : ∀ p,f (Sl p)=g (Sl p)) (hX:f sx=g sx)
   (hY:f sy=g sy) (hV:f sv=g sv) :f=g:= by
 apply zS
 · apply zS
   · exact p6 hSeed hX
   · exact hY
 · exact hV
private def aUv {A S:Type*} [c9 A] [c9 S]
  (f :A →+* S[X]) :A[X] →+* lz (lz S) :=
 oy ((oK (C:S →+* S[X])).comp f) (C (aU:S[X]))
@[simp] private theorem bFI {A S:Type*} [c9 A] [c9 S]
   (f :A →+* S[X]) (a :A) :
   aUv f (C a)=(f a).map (C:S →+* S[X]) := by
  simp [aUv]
@[simp] private theorem bFJ {A S:Type*} [c9 A] [c9 S]
   (f :A →+* S[X]) :aUv f aU=C (aU:S[X]) := by
  simp [aUv]
private theorem b2y {A S:Type*} [c9 A] [c9 S]
   [vi L A] [vi L S] {f :A →+* S[X]} {g:A →ₗ[L] S} {r :ℕ}
   (hg : ∀ a,(f a).coeff r=g a) (P:A[X]) :
   (aUv f P).coeff r=mapCoeffs g P:= by
 induction P using Lf with
 | add P Q hp hq=>rw [map_add,coeff_add,map_add,hp,hq]
 | monomial n a =>
   rw [mapCoeffs_monomial,← Fa ,lV,pG,
     bFI,bFJ,
     ← (C:S[X] →+* lz (lz S)).map_pow,coeff_mul_C,t9,hg,
     Fa]
private def XI (i:Fin 2) :Source →+* Source[X] :=
 aUv (aUv (aUv (translation i).toRingHom))
private theorem gDG (i:Fin 2) (r :ℕ) (P:Source) :
  (XI i P).coeff r=awz i r P:= by
 unfold XI awz
 apply b2y
 intro Q
 apply b2y
 intro q
 apply b2y
 intro a
 rfl
private theorem dhR (i:Fin 2) (p:qC) :
  XI i (Sl p)=(translation i p).map Sl:= by
 simp only [ XI,Sl,oq,bFI,
  oY]
 rfl
private theorem dhQ (i:Fin 2) (x :L) :
  XI i (cy L Source x)=C (cy L Source x) := by
 change XI i (Sl (nq x))=C (Sl (nq x))
 rw [dhR]
 have h:translation i (nq x)=C (nq x) := by
  simp [translation,vH]
 rw [h,oZ]
private theorem ctY (i:Fin 2) :XI i sx=C sx := by
 simp only [ XI,sx,bFI,bFJ,oZ]
private theorem dhS (i:Fin 2) :XI i sy=C sy := by
 simp only [ XI,sy,bFI,bFJ,oZ]
private theorem ctX (i:Fin 2) :XI i sv=C sv :=
 bFJ _
private theorem eK4 (x y :L) (i:Fin 2) (r :ℕ) (P:Source) :
    Km x y (awz i r P)=awz i r (Km x y P) := by
  let f :=(oK (Km x y).toRingHom).comp (XI i)
  let g:=(XI i).comp (Km x y).toRingHom
  have hfg:f=g:= by
    apply cqb
    · intro p
      change (XI i (Sl p)).map (Km x y).toRingHom =
        XI i (Km x y (Sl p))
      rw [bKs,dhR,oY]
      have hseed : (Km x y).toRingHom.comp Sl=Sl :=
        xI (bKs x y)
      rw [hseed]
    · change (XI i sx).map (Km x y).toRingHom =
        XI i (Km x y sx)
      rw [ctY,oZ]
      change C (Km x y sx)= _
      simp only [cbD,ov,ctY,dhQ]
    · change (XI i sy).map (Km x y).toRingHom =
        XI i (Km x y sy)
      rw [dhS,oZ]
      change C (Km x y sy)= _
      simp only [cbE,ov,lV,dhQ,ctY,
        dhS,ctX]
    · change (XI i sv).map (Km x y).toRingHom =
        XI i (Km x y sv)
      rw [ctX,oZ]
      change C (Km x y sv)= _
      rw [cbC,ctX]
  have h:=oz (fun F:Source →+* Source[X]=>(F P).coeff r) hfg
  change ((XI i P).map (Km x y).toRingHom).coeff r =
    (XI i (Km x y P)).coeff r at h
  rw [t9] at h
  change Km x y ((XI i P).coeff r) =
    (XI i (Km x y P)).coeff r at h
  simpa only [gDG] using h
private def gp8 (x :L) (P:qC[X]) :qC[X] :=
 P.eval₂ C (aU +C (nq x))
private theorem eK5 (x y :L) (P:qC[X]) :
  Km x y (pW P)=pW (gp8 x P) := by
 change qy _ _ (C (C P))= _
 rw [pL]
 change qy _ _ (C P)= _
 rw [pL]
 rfl
theorem proof :axj.c1 := by
 classical
 intro h D word s Q hQ i r t a b j e hab
 rw [BA,lV,eK5,eK4]
 simp only [Fg,pW,oq]
 rw [yL,yL,coeff_mul,GF]
 simp only [awz,a5F]
 apply t5
 rintro ⟨u,v⟩ huv
 have huv' : u+v=a := by simpa only [Nj] using huv
 have hv : (((Km (ad0 t) (word t) Q).coeff j).coeff b).coeff v=0:= by
  apply y5
  intro d
  exact hQ t v b j d (by omega)
 simp [hv]
end
end cyS
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace anc
noncomputable section
open cu DP Ge Polynomial
open scoped Polynomial
@[simp] theorem a8R {R A:Type*} [c9 R] [c9 A]
   (f :R →+* A) (y v :A) (p:R) :substitute f y v (pW p)=f p:= by
  simp [substitute,pW]
@[simp] theorem bw3 {R A:Type*} [c9 R] [c9 A]
   (f :R →+* A) (y v :A) :
   substitute f y v (C (aU (R:=R)))=y := by
  simp [substitute]
@[simp] theorem bOt {R A:Type*} [c9 R] [c9 A]
   (f :R →+* A) (y v :A) :
   substitute f y v (aU (R:=R[X]))=v := by
  simp [substitute]
theorem b6I {R A:Type*} [c9 R] [c9 A]
   {f g:R[X][X] →+* A}
   (hbase : ∀ p:R,f (pW p)=g (pW p))
   (hy :f (C aU)=g (C aU)) (hv :f aU=g aU) :
   f=g:= by
 apply zS
 · apply p6
   · exact hbase
   · exact hy
 · exact hv
theorem b3O {F:Type} [lI F] (H :F[X]) (lift: (kq F)[X]) :
  let h:=H.map (cy F (kq F))
  let c: (kq F)[X] →+* EM (kq F) :=pW
  let y :EM (kq F) :=C aU
  (Ge.forward H lift).toRingHom=substitute
    (c.comp (oK (cy (i5 F) (kq F))))
    (c h*y+c lift) (c h*aU +c h.derivative*y+c lift.derivative) := by
 rfl
theorem gDE {F:Type} [lI F] (H :F[X]) (lift: (kq F)[X])
    (α:F) (z :kq F) (N :ℕ) (P:Gm F)
    (hH :H.eval α=0) (hz :lift.eval (cy F (kq F) α)=z)
    (hd: (pW ((aU - C (cy F (kq F) α))^N) :
      EM (kq F))∣Ge.forward (aU - C α) (C z) P) :
    (pW ((aU - C (cy F (kq F) α))^N) :
      EM (kq F))∣Ge.forward H lift P:= by
  let x : (kq F)[X] :=aU - C (cy F (kq F) α)
  let h:=H.map (cy F (kq F))
  have hh:x∣h:= by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [h,TH,hH]
  have hl:x∣lift - C z := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [TH,hz]
  obtain ⟨u,hu⟩:=hh
  obtain ⟨δ,hδ⟩:=hl
  have hlift:lift=x*δ+C z := by
    rw [← hδ,sub_add_cancel]
  let c: (kq F)[X] →+* EM (kq F) :=pW
  let y :EM (kq F) :=C aU
  let v :EM (kq F) :=aU
  let E :=substitute c (c u*y+c δ) (c u*v+c u.derivative*y+c δ.derivative)
  have hx :x.derivative=1 := by simp [x]
  have hmap : (aU - C α).map (cy F (kq F))=x := by simp [x]
  have hnorm:=b3O (aU - C α) (C z)
  dsimp only at hnorm
  rw [hmap,hx,Ef ,vh,ox ,wY ,u5] at hnorm
  have he :E.comp (Ge.forward (aU - C α) (C z)).toRingHom =
      (Ge.forward H lift).toRingHom:= by
    rw [hnorm,b3O]
    apply b6I
    · intro g
      simp [E,c]
    · change E _ = _
      simp only [bw3]
      change E (c x*y+c (C z))=c h*y+c lift
      rw [ov,lV,hu,hlift]
      simp only [E,c,y,a8R,bw3,lV,ov]
      ring
    · change E _ = _
      simp only [bOt]
      change E (c x*v+y)=c h*v+c h.derivative*y+c lift.derivative
      rw [ov,lV,hu,hlift,JK,yU,
        yU,Ef ,hx]
      simp only [E,c,y,v,a8R,bw3,bOt,
        lV,ov,vh,ox]
      ring
  have hp:=vk E hd
  rw [show E (pW (x^N))=pW (x^N) from a8R ..] at hp
  exact (t6 he P) ▸ hp
private def aYb {R:Type} [oD R] (a :R) :EM R →+* EM R :=
 oK (oK (PM (-a)).toRingHom)
private theorem bPt {R:Type} [oD R] (a :R) (g:R[X]) :
  aYb a (pW g)=pW (EK (-a) g) := by
 simp [aYb,pW]
private theorem diC {R:Type} [oD R] (a :R) :
  aYb a (mD (aU (R:=R[X])))=mD Polynomial.X:= by
 simp [aYb]
private theorem gGT {R:Type} [oD R] (a :R) :
  aYb a (aU (R:=R[X][X]))=Polynomial.X:= by
 simp [aYb]
theorem exa {F:Type} [lI F] (α:F) (z :kq F) (N :ℕ)
    (P:Gm F)
    (hd: (pW ((aU (R:=kq F))^N) :
      EM (kq F))∣aJ3 (GV α z P)) :
    (pW ((aU - C (cy F (kq F) α))^N) :
      EM (kq F))∣Ge.forward (aU - C α) (C z) P:= by
  let a :=cy F (kq F) α
  let x : (kq F)[X] :=aU - C a
  have hx :x.derivative=1 := by simp [x]
  have ht:EK (-a) aU=x := by
    simp [x,sub_eq_add_neg]
  have hmap : (aU - C α).map (cy F (kq F))=x := by simp [x,a]
  have hnorm:=b3O (aU - C α) (C z)
  dsimp only at hnorm
  rw [hmap,hx,Ef ,vh,ox ,wY ,u5] at hnorm
  have he : (aYb a).comp (aJ3.comp (GV α z)) =
      (Ge.forward (aU - C α) (C z)).toRingHom:= by
    rw [hnorm]
    apply b6I
    · intro g
      simp only [oq,GV,aJ3,a8R,bPt,
        vG]
      change pW (EK (-a) (EK a _))=pW _
      rw [Polynomial.taylor_taylor,neg_add_cancel,Polynomial.taylor_zero]
    · simp only [oq,GV,aJ3,bw3,ov,
        a8R,lV,bPt,ht,diC,Polynomial.taylor_C]
    · simp only [oq,GV,aJ3,bOt,ov,
        lV,bPt,ht,diC,gGT]
  have hp:=vk (aYb a) hd
  rw [bPt,Polynomial.taylor_pow,ht] at hp
  exact (t6 he P) ▸ hp
end
end anc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
namespace bRH
noncomputable section
open K1 cu DP Polynomial
open scoped Polynomial BigOperators
private theorem cAY {R S:Type*} [oD R] [oD S]
   (f :R →+* S) (a b:S) (P:R[X]) :
   (P.eval₂ (C.comp f) (C a*(aU (R:=S))+C b)).coeff P.natDegree =
     f P.leadingCoeff*a^P.natDegree := by
 let Q:S[X] :=C a*(aU (R:=S))+C b
 change (P.eval₂ (C.comp f) Q).coeff P.natDegree= _
 have hQ:Q.natDegree≤1 := by
   apply natDegree_le_iff_coeff_eq_zero.mpr
   intro k hk
   simp [Q,yL,coeff_X,coeff_C,show 1≠k by omega,show k≠0 by omega]
 rw [WW,wR,Finset.sum_range_succ]
 have hz : ∑ k∈xL P.natDegree,
     (C (f (P.coeff k))*Q^k).coeff P.natDegree=0:= by
   apply t5
   intro k hk
   apply MK
   refine natDegree_mul_le.trans_lt ?_
   simp only [natDegree_C,v9]
   exact natDegree_pow_le.trans_lt
     ((RJ k hQ).trans_lt (by simpa using Finset.mem_range.mp hk))
 simp only [oq] at ⊢
 rw [hz,v9,yL,IU]
 have hp:=coeff_pow_of_natDegree_le (m:=P.natDegree) hQ
 simpa [Q,yL,coeff_C] using oz (f P.leadingCoeff * ·) hp
private theorem cW6 {h} {D:jF h} (Crt:zG D) (P:Source) :
   let j:=P.natDegree
   let i:=P.leadingCoeff.natDegree
   ((forward Crt P).coeff j).coeff i =
     au5 P.leadingCoeff.leadingCoeff* IE D^(i+j) := by
 let H :=IE D
 let A:=OY Crt
 let x :=aU (R:=aQ[X])
 let y : (aQ[X])[X] :=C H*x+C A
 let v₀: (aQ[X])[X] :=C H.derivative*x+C A.derivative
 let f :qC[X] →+* (aQ[X])[X] :=C.comp au5.toRingHom
 let g:=oy f y
 let c:aQ[X] →+* US:=pW
 let g' : lz (qC[X]) →+* US :=
   oy (R:=qC[X]) (S:=US)
     ((mD (R:=(aQ[X])[X])).comp f)
     (c H*C x+c A)
 change ((P.eval₂ g' (c H*aU +c H.derivative*C x+c A.derivative)).coeff
   P.natDegree).coeff P.leadingCoeff.natDegree= _
 have hg:g' = C.comp g:= by
   apply p6
   · intro a
     simp [g',g,pL]
   · simp only [g',g,oq,zh,u8]
     simp [c,pW,y,ov,lV]
 have hv :c H*aU +c H.derivative*C x+c A.derivative =
     C (C H)*aU +C v₀:= by
   rw [add_assoc]
   simp [c,pW,v₀,ov,lV]
 rw [hg,hv,cAY g]
 change ((P.leadingCoeff.eval₂ f y)*C H^P.natDegree).coeff
   P.leadingCoeff.natDegree= _
 rw [← C_pow,coeff_mul_C]
 unfold f y x
 rw [cAY au5.toRingHom]
 simp [H,yQ,t8]
end
end bRH
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace anc
noncomputable section
open cu DP Ge Polynomial
open scoped BigOperators Polynomial
private theorem dg1 {F:Type} [lI F] (s :lJ) (α:F)
    (P:Gm F) (hP:adk s P) (j i t:ℕ) :
    ((beE α P j i).coeff t).totalDegree≤ s.U:= by
  have hc (a :ℕ) : (((P.coeff j).coeff i).coeff a).totalDegree≤ s.U:= by
    apply IT
    intro e he
    exact (hP j i a e (MvPolynomial.mem_support_iff.mp he)).2.2
  rw [beE,taylor_coeff,eval_eq_sum_range]
  apply TI
  intro k _
  rw [hasseDeriv_coeff]
  have he :
      ((k+t).choose t:i5 F)*((P.coeff j).coeff i).coeff (k+t) *
          (cy F (i5 F) α)^k =
        nq (((k+t).choose t:F)*α^k) *
          ((P.coeff j).coeff i).coeff (k+t) := by
    simp only [vH,lV,pG,G3]
    ring
  rw [he]
  exact (Ww _ _).trans
    (by simpa only [WD,v9] using hc (k+t))
private theorem dc3 (side :Fin 2) (e :Exponent) :
  Tl e=e side+e (CI side) := by
 rw [Tl,G2 _ _ (by simp),FQ]
 fin_cases side <;> simp [CI,Nat.add_comm]
private theorem dmc {F ι:Type} [lI F] [p5 ι]
  {U d:ℕ} {side :Fin 2} (g:ι→i5 F) (hg : ∀ i,bbs U d side (g i)) :
  bbs U d side (∑ i,g i) := by
 intro e he
 by_contra h
 apply he
 rw [GF]
 exact t5 fun i _=>not_imp_comm.mp (hg i e) h
end
end anc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace bjE
noncomputable section
open K1 cu DP Polynomial
open scoped Polynomial BigOperators
def Bounded {R:Type*} [p9 R] (u v N :ℕ)
    (P:lz (lz R[X])) :Prop :=
  ∀ j i a,(((P.coeff j).coeff i).coeff a)≠0→a+u*i+v*j≤N
private theorem bVR {R:Type*} [p9 R] {u v N M:ℕ}
  {P:lz (lz R[X])} (hp:Bounded u v N P) (hn:N≤M) :
  Bounded u v M P :=
 fun j i a ha=>(hp j i a ha).trans hn
private theorem a1T {R:Type*} [p9 R] {u v N :ℕ}
  {P Q:lz (lz R[X])} (hp:Bounded u v N P) (hq:Bounded u v N Q) :
  Bounded u v N (P+Q) := by
 intro j i a h
 by_contra hn
 simp only [coeff_add,not_imp_comm.mp (hp j i a) hn,not_imp_comm.mp (hq j i a) hn,
  u5] at h
 exact h rfl
private theorem ahl {R ι:Type*} [p9 R] {u v N :ℕ}
  (T:pC ι) (P:ι→lz (lz R[X]))
  (hp : ∀ t∈T,Bounded u v N (P t)) :Bounded u v N (∑ t∈T,P t) := by
 intro j i a hn
 by_contra hx
 apply hn
 simp only [wR]
 exact t5 fun t ht=>not_imp_comm.mp (hp t ht j i a) hx
private theorem afg {R:Type*} [p9 R] {u v N M:ℕ}
  {P Q:lz (lz R[X])}
  (hp:Bounded u v N P) (hq:Bounded u v M Q) :Bounded u v (N+M) (P*Q) := by
 intro j i a hn
 by_contra! hx
 apply hn
 rw [coeff_mul]
 simp only [wR]
 apply t5
 intro ij hj
 rw [coeff_mul,wR]
 apply t5
 intro ii hi
 rw [coeff_mul]
 apply t5
 intro ia ha
 by_contra hprod
 have h₁:=hp ij.1 ii.1 ia.1 (Re hprod)
 have h₂:=hq ij.2 ii.2 ia.2 (right_ne_zero_of_mul hprod)
 rw [Nj] at hj hi ha
 rw [← hj,← hi,← ha,PA,PA] at hx
 omega
private theorem aTi {R:Type*} [c9 R] {u v N :ℕ}
  {p:R[X]} (hp:p.natDegree≤N) :Bounded u v N (pW p) := by
 intro j i a ha
 have hj:j=0:= by by_contra hj; simp [pW,coeff_C,hj] at ha
 have hi:i=0:= by subst j; by_contra hi; simp [pW,coeff_C,hi] at ha
 subst j i
 simp only [pW,oq,coeff_C_zero,vj,u5] at *
 exact (le_natDegree_of_ne_zero ha).trans hp
abbrev jU {R:Type*} [p9 R] :lz (lz R) :=
 (@mD (lz R) _) (aU (R:=R))
private theorem bVU {R:Type*} [c9 R] (u v :ℕ) :
  Bounded u v u (jU (R:=R[X])) := by
 intro j i a ha
 have hj:j=0:= by by_contra hj; simp [coeff_C,hj] at ha
 have hi:i=1 := by subst j; by_contra hi; simp [coeff_X,Ne.symm hi] at ha
 subst j i
 have ha₀:a=0:= by by_contra h; simp [coeff_X,coeff_one,h] at ha
 simp [ha₀]
private theorem cDr {R:Type*} [c9 R] (u v :ℕ) :
  Bounded u v v (aU:lz (lz R[X])) := by
 intro j i a ha
 have hj:j=1 := by by_contra hj; simp [coeff_X,Ne.symm hj] at ha
 have hi:i=0:= by subst j; by_contra hi; simp [coeff_one,hi] at ha
 subst j i
 have ha₀:a=0:= by by_contra h; simp [coeff_one,h] at ha
 simp [ha₀]
private theorem aMs {R:Type*} [c9 R] {u v N :ℕ}
   {P:lz (lz R[X])} (hp:Bounded u v N P) (n:ℕ) :
   Bounded u v (N*n) (P^n) := by
 induction n with
 | zero=>simpa using (aTi (u:=u) (v :=v) (N :=0)
     (p:=(1 :R[X])) (by simp))
 | succ n ih=>simpa [pow_succ,Nat.mul_succ] using afg ih hp
def substitute {A B:Type*} [c9 A] [c9 B]
    (f :A →+* B) (y v :lz (lz B)) :
    lz (lz A) →+* lz (lz B) :=
  oy (oy ((pW (R:=B)).comp f) y) v
@[simp] theorem dfH {A B:Type*} [c9 A] [c9 B]
   (f :A →+* B) (y v :lz (lz B)) (g:A[X]) :
   substitute f y v (C g)=oy ((pW (R:=B)).comp f) y g:= by
  simp [substitute]
@[simp] theorem dfI {A B:Type*} [c9 A] [c9 B]
   (f :A →+* B) (y v :lz (lz B)) :
   substitute f y v (aU:lz A[X])=v := by
  simp [substitute]
def bgw {h} (D:jF h) (Crt:zG D) :US :=
 pW (IE D)*jU + pW (OY Crt)
def bgz {h} (D:jF h) (Crt:zG D) :US :=
  pW (IE D)*aU +pW (IE D).derivative*jU +
    pW (OY Crt).derivative
theorem b3N {h} {D:jF h} (Crt:zG D) (P:Source) :
  forward Crt P =
   substitute au5.toRingHom (bgw D Crt) (bgz D Crt) P :=
 rfl
theorem c6W {h} (D:jF h) : (IE D).Monic :=
 ((D.monic 0).mul (D.monic 1)).map _
theorem bgu {h} (D:jF h) : (IE D).natDegree=2*h:= by
 rw [IE,Iy,((D.monic 0).mul (D.monic 1)).natDegree_map,
  (D.monic 0).natDegree_mul (D.monic 1),
  D.degree,D.degree,two_mul]
private theorem bY9 {h} (D:jF h) (Crt:zG D) :
  (OY Crt).natDegree≤2*h:= by
 apply G5
 intro i _
 refine (natDegree_smul_le _ _).trans (natDegree_map_le.trans ?_)
 exact natDegree_le_iff_degree_le.mpr (Crt.af0 i).le
private theorem blq {h s W P} (hp:P∈Aw h s W) {j i:ℕ}
  (hij: (P.coeff j).coeff i≠0) :
  ((P.coeff j).coeff i).natDegree+(i+j)*(131071+h)≤W+(s.B+s.J)*(2*h)+j:= by
 have hc:=leadingCoeff_ne_zero.mpr hij
 obtain ⟨e,he⟩:=Finset.nonempty_iff_ne_empty.mpr
  (show (((P.coeff j).coeff i).leadingCoeff).support ≠ ∅ by simpa using hc)
 have hne :=MvPolynomial.mem_support_iff.mp he
 have hel:awN h s W j i ((P.coeff j).coeff i).natDegree e := by
  by_contra nh
  exact hne (hp j i _ e nh)
 exact hel.2.2.2
theorem c55 {h} {D:jF h} (s :lJ) (W:ℕ) {F Q:US}
  (hF:Bounded (131071-h) (131071-h-1) (W+(s.B+s.J)*(2*h)) F)
  (he :F=pW ((IE D)^(s.B+s.J))*Q) :
  ∀ j i,W<(131071-h)*i+(131071-h-1)*j→(Q.coeff j).coeff i=0:= by
 intro j i hw
 by_contra hn
 let G:=(F.coeff j).coeff i
 have hc:G=(IE D)^(s.B+s.J)*(Q.coeff j).coeff i:= by
  dsimp [G]
  rw [he]
  change ((C (C ((IE D)^(s.B+s.J)))*Q).coeff j).coeff i= _
  rw [yL,yL]
 have hd:G.natDegree=(s.B+s.J)*(2*h)+((Q.coeff j).coeff i).natDegree := by
  rw [hc,((c6W D).pow _).natDegree_mul' hn,natDegree_pow,bgu]
 have hne :G≠0:= by
  rw [hc]
  exact z7 ((c6W D).pow _).ne_zero hn
 have hb:=hF j i G.natDegree (leadingCoeff_ne_zero.mpr hne)
 rw [hd] at hb
 omega
end
end bjE
end
section
namespace cyT
noncomputable section
open cu DP
open scoped BigOperators
private def aAC (h:ℕ) (s :lJ) (W q j:ℕ) :ℕ :=
 W+(s.B+s.J)*(2*h)+j+1 - q*(131071+h)
private theorem cZb (h:ℕ) (s :lJ) (W q j a :ℕ) :
  a<aAC h s W q j ↔
    a+q*(131071+h)≤W+(s.B+s.J)*(2*h)+j:= by
 unfold aAC
 omega
private abbrev atZ (U:ℕ) :=Σ t:Fin (U + 1),Fin (t.val+1)
private def aP8 {U:ℕ} (b:atZ U) :Fin 2 →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm ![b.1.val - b.2.val,b.2.val]
private theorem dcK {U:ℕ} (b:atZ U) :
  aP8 b 0=b.1.val - b.2.val := by
 simp [aP8]
private theorem coX {U:ℕ} (b:atZ U) :
  aP8 b 1=b.2.val := by
 simp [aP8]
private theorem dc4 (e :Fin 2 →₀ ℕ) :Tl e=e 0+e 1 := by
 unfold Tl
 rw [G2 _ _ (fun _=>rfl),FQ]
private theorem dc5 {U:ℕ} (b:atZ U) :
  Tl (aP8 b)=b.1.val := by
 rw [dc4,dcK,coX]
 have :=b.2.isLt
 omega
private theorem goa (U:ℕ) :
  uW (aP8 (U:=U)) := by
 rintro ⟨t,b⟩ ⟨t',b'⟩ he
 have ht:=oz Tl he
 simp only [dc5] at ht
 have htotal:t=t' := zm ht
 subst t'
 have hb:=oz (fun e :Fin 2 →₀ ℕ=>e 1) he
 simp only [coX] at hb
 have hlast :b=b' := zm hb
 subst b'
 rfl
private theorem d4Q {U:ℕ} (e :Fin 2 →₀ ℕ) (he :Tl e≤U) :
   ∃ b:atZ U,aP8 b=e := by
 let t:Fin (U + 1) :=⟨Tl e,by omega⟩
 have ht:t.val=e 0+e 1 :=dc4 e
 let b:Fin (t.val+1) :=⟨e 1,by omega⟩
 refine ⟨⟨t,b⟩,Finsupp.ext fun k => ?_⟩
 fin_cases k
 · change aP8 (⟨t,b⟩:atZ U) 0=e 0
   rw [dcK]
   change t.val-e 1=e 0
   omega
 · exact coX ⟨t,b⟩
private theorem dFy (U:ℕ) :Cy (atZ U)=qJ U:= by
 simp only [atZ,Eg ,yJ]
 rw [zf (fun t:ℕ=>t+1)]
 have hsum:=Pc (fun t:ℕ=>t) (U + 1)
 simp only [u5] at hsum
 rw [← hsum]
 simp [Pk,qJ,Dv]
private abbrev aSd (h:ℕ) (s :lJ) (W:ℕ) :=
 Σ q:Fin (s.B+1),Σ j:Fin (min q.val s.J+1),
   Fin (aAC h s W q.val j.val)×atZ s.U
private abbrev asU:=ℕ×ℕ×ℕ×(Fin 2 →₀ ℕ)
private def rU {h:ℕ} {s :lJ} {W:ℕ} (k :aSd h s W) :asU :=
 ⟨k.2.1.val,k.1.val - k.2.1.val,k.2.2.1.val,aP8 k.2.2.2⟩
private theorem d5p {h:ℕ} {s :lJ} {W:ℕ} (k :aSd h s W) :
  awN h s W (rU k).1 (rU k).2.1 (rU k).2.2.1
   (rU k).2.2.2 := by
 rcases k with ⟨q,j,a,b⟩
 have hq:=q.isLt
 have hj:=j.isLt
 have hjq:=Kz q.val s.J
 have hjJ:=Nat.min_le_right q.val s.J
 have hgrade :q.val - j.val+j.val=q.val := by omega
 have hb:=b.1.isLt
 simp only [rU,awN,hgrade,dc5]
 exact ⟨by omega,by omega,by omega,(cZb h s W _ _ _).mp a.isLt⟩
private theorem d4t {h:ℕ} {s :lJ} {W j i a :ℕ} {e :Fin 2 →₀ ℕ}
  (hel:awN h s W j i a e) :
  ∃ k :aSd h s W,rU k=(j,i,a,e) := by
 obtain ⟨hq,hj,he,ha⟩:=hel
 obtain ⟨b,hb⟩:=d4Q e he
 let q:Fin (s.B+1) :=⟨i+j,by omega⟩
 let v :Fin (min q.val s.J+1) :=⟨j,by
  have h:j≤ min (i+j) s.J:=le_min (by omega) hj
  exact xW h⟩
 let x :Fin (aAC h s W q.val v.val) :=
  ⟨a,(cZb h s W _ _ _).mpr ha⟩
 refine ⟨⟨q,v,x,b⟩,?_⟩
 simp [rU,q,v,x,hb]
private theorem d5q (h:ℕ) (s :lJ) (W:ℕ) :
  uW (rU (h:=h) (s :=s) (W:=W)) := by
 rintro ⟨q,j,a,b⟩ ⟨q',j',a',b'⟩ he
 have hj:=oz (fun p:asU=>p.1) he
 have hi:=oz (fun p:asU=>p.2.1) he
 change j.val=j'.val at hj
 change q.val - j.val=q'.val - j'.val at hi
 have hlt:=j.isLt
 have hlt' := j'.isLt
 have hmin:=Kz q.val s.J
 have hmin' := Kz q'.val s.J
 have hq:q=q' := zm (by omega)
 subst q'
 have hv :j=j' := zm hj
 subst j'
 have hx :a=a' := zm (oz (fun p:asU=>p.2.2.1) he)
 subst a'
 have hb:b=b' := goa s.U (oz (fun p:asU=>p.2.2.2) he)
 subst b'
 rfl
private def ahS (k :asU) :Source :=
 pz k.1 (pz k.2.1
  (pz k.2.2.1 (qz k.2.2.2 1)))
private theorem cFV (k d:asU) :
    Fg (ahS k) d.1 d.2.1 d.2.2.1 d.2.2.2=if k=d then 1 else 0:= by
  classical
  rcases k with ⟨j,i,a,e⟩
  rcases d with ⟨j',i',a',e'⟩
  by_cases hj:j=j'
  · subst j'
    by_cases hi:i=i'
    · subst i'
      by_cases ha :a=a'
      · subst a'
        simp [Fg,ahS]
      · simp [Fg,ahS,ze,ha]
    · simp [Fg,ahS,ze,hi]
  · simp [Fg,ahS,ze,hj]
private def cBd {h:ℕ} {s :lJ} {W:ℕ} (k :aSd h s W) :
  Aw h s W:= by
 refine ⟨ahS (rU k),?_⟩
 intro j i a e hbad
 rw [cFV (rU k) (j,i,a,e),z9]
 intro he
 apply hbad
 simpa only [he] using d5p k
private def aD (h:ℕ) (s :lJ) (W:ℕ) :
  Aw h s W →ₗ[L] (aSd h s W→L) where
 toFun P k :=Fg P (rU k).1 (rU k).2.1 (rU k).2.2.1 (rU k).2.2.2
 map_add' P Q:= by
  funext k
  simp [Fg]
 map_smul' b P:= by
  funext k
  simp [Fg,C5]
private theorem dPS {h:ℕ} {s :lJ} {W:ℕ} (k d:aSd h s W) :
  aD h s W (cBd k) d=if k=d then 1 else 0:= by
 classical
 change Fg (ahS (rU k)) (rU d).1 (rU d).2.1
  (rU d).2.2.1 (rU d).2.2.2= _
 simp only [cFV,(d5q h s W).eq_iff]
private def dPL (h:ℕ) (s :lJ) (W:ℕ) :
    Aw h s W ≃ₗ[L] (aSd h s W→L) := by
  classical
  refine LinearEquiv.ofBijective (aD h s W) ⟨?_,?_⟩
  · intro P Q hPQ
    apply C4
    apply pQ
    intro j
    apply pQ
    intro i
    apply pQ
    intro a
    apply y5
    intro e
    change Fg P j i a e=Fg Q j i a e
    by_cases he :awN h s W j i a e
    · obtain ⟨k,hk⟩:=d4t he
      have hcoeff :=yo hPQ k
      change Fg P (rU k).1 (rU k).2.1 (rU k).2.2.1
          (rU k).2.2.2 =
        Fg Q (rU k).1 (rU k).2.1 (rU k).2.2.1
          (rU k).2.2.2 at hcoeff
      simpa only [hk] using hcoeff
    · exact (P.property j i a e he).trans (Q.property j i a e he).symm
  · intro f
    refine ⟨∑ k,f k•cBd k,?_⟩
    funext d
    rw [qG]
    simp [Oc,dPS,mul_ite]
private theorem cSb (h:ℕ) (s :lJ) (W:ℕ) :
    xu L (Aw h s W)=qJ s.U*ku s (aAC h s W) := by
  rw [(dPL h s W).finrank_eq,Module.finrank_pi]
  unfold aSd
  rw [Eg]
  calc
    _ = ∑ q:Fin (s.B+1),∑ j:Fin (min q.val s.J+1),
        qJ s.U*aAC h s W q j:= by
      apply p7 rfl
      intro q _
      rw [Eg]
      apply p7 rfl
      intro j _
      rw [Vz ,yJ,dFy,Dv]
    _ = _:= by
      unfold ku
      simp only [FR]
      rw [zf (fun q => ∑ j:Fin (min q s.J+1),
        qJ s.U*aAC h s W q j)]
      apply p7 rfl
      intro q _
      exact zf (fun j=>qJ s.U*aAC h s W q j)
        (min q s.J+1)
private theorem dib {h:ℕ} {s :lJ} {W q j:ℕ} (hh:h≤131071)
  (hw:c69 h s W) (hq:q≤ s.B) (hj:j≤ min q s.J) :
  aAC h s W q j=W+1+j - q*(131071 - h)+2*h*(s.B+s.J - q) := by
 have hdegree :131071+h=(131071 - h)+2*h:= by omega
 have hcredit :q*(2*h)+(s.B+s.J - q)*(2*h)=(s.B+s.J)*(2*h) := by
  rw [← Nat.add_mul]
  congr 1
  omega
 have hraw:=hw q hq j hj
 rw [aAC,hdegree,PA,Dv (2*h) (s.B+s.J - q)]
 omega
end
end cyT
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1200000
namespace bRG
noncomputable section
open K1 cu DP Polynomial
open scoped BigOperators Polynomial
private abbrev sx :Source :=mD (mD (aU (R:=qC)))
private abbrev sy :Source :=mD (aU (R:=qC[X]))
private abbrev sv :Source :=aU
private abbrev asn:Source :=sy+sx*sv
private abbrev Sl:qC →+* Source :=C.comp (C.comp C)
private theorem cbD (x r :L) :Km x r sx=sx+algebraMap L Source x := by
 change qy _ _ (mD (mD (aU (R:=qC))))= _
 rw [pL]
 change qy _ _ (mD (aU (R:=qC)))= _
 rw [pL]
 change (cy qC[X] Source) (qy _ _ (aU (R:=qC)))= _
 rw [u8 ,ov]
 rfl
private theorem cbE (x r :L) :
  Km x r sy=asn+algebraMap L Source r := by
 change qy _ _ (mD (aU (R:=qC[X])))= _
 rw [pL]
 change qy _ _ (aU (R:=qC[X]))= _
 rw [u8]
 change cy L Source r+sx*sv+sy=asn+algebraMap L Source r
 dsimp only [asn]
 ac_rfl
private theorem cbC (x r :L) :Km x r sv=sv := by
 change qy _ _ (aU:Source)= _
 rw [u8]
private theorem bKs (x r :L) (p:qC) :
  Km x r (Sl p)=Sl p:= by
 change qy _ _ (C (C (C p)))= _
 rw [pL]
 change qy _ _ (C (C p))= _
 rw [pL]
 change (cy qC[X] Source) (qy _ _ (C p))= _
 rw [pL]
 rfl
private theorem c5u (p:qC) (a b j:ℕ) :
  Sl p*sx^a*sy^b*sv^j =
   pz j (pz b (pz a p)) := by
 simp only [Sl,oq,sx,sy,sv,← pG,← lV,
  Fa]
private theorem gpc (e :Fin 2 →₀ ℕ) (c:L) :
  Sl (qz e c)=c•Sl (qz e 1) := by
 rw [yB]
 change _=Sl (nq c)*_
 rw [← lV,MvPolynomial.C_mul_monomial,FK]
private theorem eAb (M:xm L Source) (P:Source)
    (H : ∀ j b a e,Fg P j b a e≠0 →
      pz j (pz b (pz a (qz e
        (Fg P j b a e))))∈M) :P∈M:= by
  rw [P.as_sum_support]
  apply M.sum_mem
  intro j _
  rw [show pz j (P.coeff j) =
      pz j (∑ b∈(P.coeff j).support,pz b ((P.coeff j).coeff b)) from
    oz _ (P.coeff j).as_sum_support,qG]
  apply M.sum_mem
  intro b _
  let p:=(P.coeff j).coeff b
  change pz j (pz b p)∈M
  rw [show p = ∑ a∈p.support,pz a (p.coeff a) from p.as_sum_support]
  simp only [qG]
  apply M.sum_mem
  intro a _
  rw [show pz a (p.coeff a) =
      pz a (∑ e∈(p.coeff a).support,qz e ((p.coeff a).coeff e)) from
    oz _ (p.coeff a).as_sum]
  simp only [qG]
  apply M.sum_mem
  intro e he
  exact H j b a e (MvPolynomial.mem_support_iff.mp he)
private theorem b9x (M:xm L Source) (p u v :Source)
  (n:ℕ) (H : ∀ k≤n,p*u^k*v^(n-k)∈M) :
  p*(u+v)^n∈M:= by
 rw [add_pow u v n,FR]
 apply M.sum_mem
 intro k hk
 have h:=M.smul_mem (n.choose k :L) (H k (by simpa using hk))
 rw [yB,G3] at h
 simpa only [t8 ,t4 ,mul_left_comm] using h
private theorem c04 (M:xm L Source) (p u:Source)
  (r :L) (n:ℕ) (H : ∀ k≤n,p*u^k∈M) :
  p*(u+algebraMap L Source r)^n∈M:= by
 apply b9x
 intro k hk
 rw [t4 (p*u^k),← pG,← yB]
 exact M.smul_mem _ (H k hk)
private structure X3 (m:ℕ) where
 j:ℕ
 b:ℕ
 a :ℕ
 e :Fin 2 →₀ ℕ
 low:a+2*b< m
private def cut (s :lJ) :Source →ₗ[L] (X3 s.m→L) where
 toFun P z :=Fg P z.j z.b z.a z.e
 map_add' P Q:= by
  funext z
  simp [Fg]
 map_smul' c P:= by
  funext z
  simp [Fg,C5]
private abbrev bk3 (U:ℕ) :=Σ a :Fin (U+1),Fin (U+1-a.val)
private def dcI {U:ℕ} (i:bk3 U) :Fin 2 →₀ ℕ :=
 (P7 ℕ).symm (i.1.val,i.2.val)
private theorem d4P {U:ℕ} {e :Fin 2 →₀ ℕ} (he :Tl e≤U) :
   ∃ i:bk3 U,dcI i=e := by
 let pair :=P7 ℕ e
 have hw:pair.1+pair.2≤U:= by
   simpa only [pair,Tl,Equiv.symm_apply_apply,← finTwoArrowEquiv'_sum_eq (d:=pair)]
     using he
 refine ⟨⟨⟨pair.1,by omega⟩,⟨pair.2,?_⟩⟩,?_⟩
 · change pair.2<U+1-pair.1
   omega
 · exact (P7 ℕ).symm_apply_apply e
private theorem goP (U:ℕ) :Cy (bk3 U)=qJ U:= by
 simp only [bk3,Eg ,yJ,zf]
 calc
  (∑ a∈xL (U+1),(U+1-a))=(∑ a∈xL (U+1),(a+1)) := by
    rw [← Finset.sum_range_reflect (fun a=>U+1-a) (U+1)]
    apply p7 rfl
    intro a ha
    simp only [Finset.mem_range] at ha
    omega
  _=(∑ a∈xL (U+2),a) := by
    simpa only [Nat.add_zero] using (Pc (fun a :ℕ=>a) (U+1)).symm
  _=qJ U:= by
    rw [Pk,qJ,show U+2-1=U+1 by omega,Dv]
private abbrev bQ2 (s :lJ) :=
 (Σ q:Fin (s.B+1),Σ k :Fin (min q.val s.J+1),
   Fin (s.m+min q.val s.J-(q.val+2*k.val)))×bk3 s.U
private theorem efm (s :lJ) :
   Cy (bQ2 s) =
     ku s (fun q k=>s.m+min q s.J-(q+2*k))*qJ s.U:= by
 unfold bQ2
 rw [Vz ,goP,ku]
 congr 1
 simp only [Eg ,yJ]
 rw [zf
   (fun q:ℕ => ∑ k :Fin (min q s.J+1),(s.m+min q s.J-(q+2*k.val)))]
 refine p7 rfl ?_
 intro q _
 exact zf (fun k :ℕ=>s.m+min q s.J-(q+2*k)) (min q s.J+1)
private def bfk (q d k a :ℕ) (e :Fin 2 →₀ ℕ) :Source :=
 Sl (qz e 1)*sx^a*sy^k*sv^(d-k)*asn^(q-d)
private def generators (s :lJ) (i:bQ2 s) :X3 s.m→L :=
 cut s (bfk i.1.1.val (min i.1.1.val s.J) i.1.2.1.val i.1.2.2.val (dcI i.2))
private def avt (s :lJ) :xm L (X3 s.m→L) :=
 G4 L (Kh (generators s))
private abbrev preimage (s :lJ) :xm L Source :=(avt s).comap (cut s)
private theorem emO (s :lJ) (e :Fin 2 →₀ ℕ) (a b j:ℕ)
   (h:s.m≤a+2*b) :
   Sl (qz e 1)*sx^a*sy^b*sv^j∈FU (cut s) := by
 apply LinearMap.mem_ker.mpr
 funext z
 change Fg _ z.j z.b z.a z.e=0
 rw [c5u]
 have hz :=z.low
 by_cases hj:j=z.j
 · by_cases hb:b=z.b
   · by_cases ha :a=z.a
     · omega
     · simp [Fg,ze,hj,hb,ha]
   · simp [Fg,ze,hj,hb]
 · simp [Fg,ze,hj]
private theorem dNw {R:Type*} [Kl R] (c x y v :R)
  (a k j t n:ℕ) :
  (c*x^a*y^k*v^j)*y^t*(x*v)^n=c*x^(a+n)*y^(k+t)*v^(j+n) := by
 simp only [yQ,GY]
 ac_rfl
private theorem dNu {R:Type*} [Kl R] (c x y v A:R)
  (a j k n:ℕ) :
  (c*x^a*v^j*A)*y^k*(x*v)^n=c*x^(a+n)*y^k*v^(j+n)*A:= by
 simp only [yQ,GY]
 ac_rfl
private theorem b9s {R:Type*} [Kl R] (c v x y :R) :
 c*v*x*y=c*x*y*v := by ac_rfl
private theorem emN (s :lJ) (q d k a :ℕ) (e :Fin 2 →₀ ℕ)
  (h:s.m≤a+(q-d)+2*k) :bfk q d k a e∈FU (cut s) := by
 unfold bfk
 change _ *(sy+sx*sv)^(q-d)∈_
 apply b9x
 intro t ht
 have ht' := emO s e (a+(q-d-t)) (k+t) (d-k+(q-d-t)) (by omega)
 rw [dNw]
 exact ht'
private theorem efo (s :lJ) (q k a :ℕ) (e :Fin 2 →₀ ℕ)
   (hq:q≤ s.B) (hk :k≤ min q s.J) (he :Tl e≤ s.U) :
   bfk q (min q s.J) k a e∈preimage s := by
 change cut s _∈avt s
 have hd:min q s.J≤q:=II _ _
 by_cases ha :a<s.m+min q s.J-(q+2*k)
 · obtain ⟨i,rfl⟩:=d4P he
   exact RP
     ⟨(⟨⟨q,xW hq⟩,⟨⟨k,xW hk⟩,⟨a,ha⟩⟩⟩,i),rfl⟩
 · rw [LinearMap.mem_ker.mp (emN s q (min q s.J) k a e (by omega))]
   exact (avt s).zero_mem
private theorem gqB (s :lJ) (a b j:ℕ) (e :Fin 2 →₀ ℕ)
  (hq:b+j≤ s.B) (hj:j≤ s.J) (he :Tl e≤ s.U) :
  Sl (qz e 1)*sx^a*asn^b*sv^j∈preimage s := by
 let q:=b+j
 let d:=min q s.J
 have hd:d≤q:=II _ _
 have hjd:j≤d:=le_min (Nat.le_add_left _ _) hj
 let p:=Sl (qz e 1)*sx^a*sv^j*asn^(q-d)
 have hpow:asn^b=asn^(q-d)*asn^(d-j) := by
  rw [← yQ,show q-d+(d-j)=b by dsimp only [q] at *; omega]
 have hexpand:p*(sy+sx*sv)^(d-j)∈preimage s := by
  apply b9x
  intro k hk
  have hV:d-k=j+(d-j-k) := by omega
  have hgen:=efo s q k (a+(d-j-k)) e hq (by omega) he
  change bfk q d k (a+(d-j-k)) e∈_ at hgen
  rw [bfk,hV] at hgen
  dsimp only [p]
  rw [dNu]
  exact hgen
 dsimp only [p] at hexpand
 change (Sl (qz e 1)*sx^a*sv^j*asn^(q-d)) *
  asn^(d-j)∈preimage s at hexpand
 rw [b9s (Sl (qz e 1)*sx^a),t8
  (Sl (qz e 1)*sx^a),← hpow] at hexpand
 exact hexpand
private theorem gDR (s :lJ) (x r :L) (a b j:ℕ) (e :Fin 2 →₀ ℕ)
   (hq:b+j≤ s.B) (hj:j≤ s.J) (he :Tl e≤ s.U) :
   Sl (qz e 1)*(sx+algebraMap L Source x)^a *
     (asn+algebraMap L Source r)^b*sv^j∈preimage s := by
 let p:=Sl (qz e 1)*sv^j
 have h: (p*(asn+algebraMap L Source r)^b) *
     (sx+algebraMap L Source x)^a∈preimage s := by
   apply c04
   intro t _
   have h' : (p*sx^t)*(asn+algebraMap L Source r)^b∈preimage s := by
     apply c04
     intro k hk
     dsimp only [p]
     rw [b9s]
     exact gqB s t k j e (by omega) hj he
   rw [mul_right_comm]
   exact h'
 rw [mul_right_comm p] at h
 dsimp only [p] at h
 rw [b9s] at h
 exact h
private theorem duH (h:ℕ) (s :lJ) (W:ℕ) (x r :L)
  (P:Aw h s W) :cut s (Km x r P.val)∈avt s := by
 change P.val∈(preimage s).comap (Km x r).toLinearMap
 apply eAb
 intro j b a e hne
 have hel:awN h s W j b a e := by
  by_contra hn
  exact hne (P.property j b a e hn)
 obtain ⟨hq,hj,he,_⟩:=hel
 change Km x r _∈preimage s
 rw [← c5u,gpc,KH,KH,KH,x7]
 apply (preimage s).smul_mem
 simp only [lV,pG,cbD,cbE,cbC,bKs]
 exact gDR s x r a b j e hq hj he
private def nodeMap (h:ℕ) (word:I→L) (s :lJ) (W:ℕ) (i:I) :
  Aw h s W →ₗ[L] avt s :=
 LinearMap.codRestrict (avt s)
  (((cut s).comp (Km (ad0 i) (word i)).toLinearMap).domRestrict (Aw h s W))
  (duH h s W (ad0 i) (word i))
private theorem cYx (s :lJ) :
   xu L (avt s) ≤
     ku s (fun q k=>s.m+min q s.J-(q+2*k))*qJ s.U:= by
 rw [← efm]
 exact finrank_range_le_card (R:=L) (generators s)
end
end bRG
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace anc
noncomputable section
open cu DP Ge Polynomial
open scoped BigOperators Polynomial
def c1 :Prop :=
  ∀ (F:Type) [lI F] (s :lJ) (α:F) (z :kq F) (P:Gm F),
    adk s P→GV α z P=aIP s (aVG s α z P)
def c2 :Prop :=
  ∀ (F:Type) [lI F] (s :lJ)
    (f : (q:jJ s)→NQ s q.val→(kq F)[X]),
    (∀ q k,(aU (R:=kq F))^(s.B+s.J)∣aRi s q.val (f q) k) →
    (pW ((aU (R:=kq F))^(s.B+s.J)) :EM (kq F)) ∣
      aJ3 (aIP s f)
end
end anc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
namespace bRH
noncomputable section
open K1 cu DP Polynomial
open scoped Polynomial BigOperators nonZeroDivisors
private abbrev Position :=ℕ×ℕ×(Fin 2 →₀ ℕ)
private def bvY (e :Fin 2 →₀ ℕ) (g:qC[X]) :L[X] :=
 ⟨⟨g.toFinsupp.coeff.mapRange (fun p=>p.coeff e) (by simp)⟩⟩
@[simp] private theorem glR (e :Fin 2 →₀ ℕ) (g:qC[X]) (a :ℕ) :
   (bvY e g).coeff a=(g.coeff a).coeff e :=rfl
private def bwM (P:Source) (t:Position) :L[X] :=
 bvY t.2.2 ((P.coeff t.1).coeff t.2.1)
private def azk :Jet →ₗ[FX] (Position→FX) :=
 FV fun t => {
  toFun P:=((P.coeff t.1).coeff t.2.1).coeff t.2.2
  map_add' P Q:= by simp
  map_smul' r P:= by simp }
private theorem dPW (P:Source) (t:Position) :
  azk (U4 P) t=cy L[X] FX (bwM P t) := by
 let ξ:=cy L[X] FX (aU (R:=L))
 let g:=(P.coeff t.1).coeff t.2.1
 let e :=t.2.2
 change (((U4 P).coeff t.1).coeff t.2.1).coeff e= _
 simp only [U4,Mw]
 change (g.eval₂ (oj (cy L FX)) (nq ξ)).coeff e =
  (vw L L[X] FX) (bvY e g)
 have hdeg: (bvY e g).natDegree≤g.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro a ha
  simp [MK ha]
 rw [← Qx (bvY e g) (vw L L[X] FX),
  Polynomial.eval₂_eq_sum_range' _ (xW hdeg),WW]
 simp only [GF,glR]
 apply p7 rfl
 intro a _
 rw [← pG,t4 ,Kp,G8 ,t4]
 rfl
private def cF0 (j i a :ℕ) (e :Fin 2 →₀ ℕ) :Source →ₗ[L] L where
 toFun P:=Fg P j i a e
 map_add' P Q:= by simp [Fg]
 map_smul' r P:= by simp [Fg]
private theorem cqb {P Q:Source}
  (heq : ∀ j i a e,Fg P j i a e=Fg Q j i a e) :P= Q :=
 pQ fun j=>pQ fun i=>pQ fun a =>
  y5 _ _ fun e=>heq j i a e
private theorem goX (e :Fin 2 →₀ ℕ) (k :Fin 2) :e k≤Tl e := by
 rw [Tl,G2 _ _ (by simp)]
 exact VH (fun i _=>Nat.zero_le (e i)) (u9 k)
private instance gPw {h} {D:jF h} (Crt:zG D) (word:I→L)
   (s :lJ) (W:ℕ) :Ea L (complete Crt word s W) := by
 classical
 let A:=W+(s.B+s.J)*(2*h)+s.J
 let T:=Fin (s.J+1)×Fin (s.B+1)×Fin (A+1)×(Fin 2→Fin (s.U+1))
 let f :complete Crt word s W →ₗ[L] (T→L) :=
   FV fun t=>(cF0 t.1 t.2.1 t.2.2.1
     (Finsupp.equivFunOnFinite.symm fun k=>(t.2.2.2 k :ℕ))).comp
     (complete Crt word s W).subtype
 apply VO f
 intro P Q hPQ
 apply C4
 apply cqb
 intro j i a e
 by_cases he :awN h s W j i a e
 · obtain ⟨hB,hJ,hU,hA⟩:=he
   let t:T:=⟨⟨j,by omega⟩,⟨i,by omega⟩,⟨a,by dsimp [A]; omega⟩,
     fun k=>⟨e k,xW  ((goX e k).trans hU)⟩⟩
   have ht:=yo hPQ t
   change Fg (P:Source) j i a (Finsupp.equivFunOnFinite.symm (e :Fin 2→ℕ)) =
     Fg (Q:Source) j i a (Finsupp.equivFunOnFinite.symm (e :Fin 2→ℕ)) at ht
   simpa only [Finsupp.equivFunOnFinite_symm_coe] using ht
 · exact (P.property.1.1 j i a e he).trans (Q.property.1.1 j i a e he).symm
private instance gPS {h} {D:jF h} (Crt:zG D) (word:I→L)
  (s :lJ) (W:ℕ) :Ea FX (VY Crt word s W) := by
 change Ea FX
  (G4 FX ((complete Crt word s W).map U4.toLinearMap:Set Jet))
 exact Module.Finite.of_fg ((Module.Finite.iff_fg.mp inferInstance).span (A:=FX))
private def anL (h:ℕ) (s :lJ) (W:ℕ) (t:Position) :ℕ :=
 W+(s.B+s.J)*(2*h)+t.1-(t.2.1+t.1)*(131071+h)
private def aMr {h} {D:jF h} (Crt:zG D) (word:I→L)
  (s :lJ) (W:ℕ) :complete Crt word s W →ₗ[L] (Position→L) :=
 FV fun t =>
  (cF0 t.1 t.2.1 (anL h s W t) t.2.2).comp (complete Crt word s W).subtype
private theorem gs6 {h} {D:jF h} {Crt:zG D} {word:I→L}
  {s W} (P:complete Crt word s W) (t:Position) :
  (bwM (P:Source) t).natDegree≤anL h s W t:= by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro a ha
 change Fg (P:Source) t.1 t.2.1 a t.2.2=0
 apply P.property.1.1
 intro he
 have hw:=he.2.2.2
 unfold anL at ha
 omega
private theorem en2 {ι σ:Type*} [p5 ι]
    (v :ι→σ→ L[X]) (d:σ→ℕ) (hd : ∀ k t,(v k t).natDegree≤d t)
    (hli:C9 L (fun k t=>(v k t).coeff (d t))) :
    C9 FX (fun k t=>cy L[X] FX (v k t)) := by
  classical
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  obtain ⟨b,hb⟩:=IsLocalization.exist_integer_multiples_of_finite (L[X])⁰ c
  choose f hf using hb
  let n:=Finset.univ.sup fun k=>(f k).natDegree
  have hn (k :ι) : (f k).natDegree≤n :=
    Finset.le_sup (f := fun k=>(f k).natDegree) (u9 k)
  have hinj:=qM L[X] FX
  have hsum (t:σ) : ∑ k,f k*v k t=0:= by
    apply hinj
    rw [qG,ox]
    simp only [lV,hf,yB,t8 ,← FR]
    have ht:=yo hc t
    simp only [Oc,Pi.smul_apply,smul_eq_mul,Et] at ht
    rw [ht,vj]
  have hlead : ∑ k,(f k).coeff n•(fun t=>(v k t).coeff (d t))=0:= by
    funext t
    simpa only [wR,coeff_mul_add_eq_of_natDegree_le (hn _) (hd _ _),
      v8 ,Oc,Pi.smul_apply,smul_eq_mul,Et] using
      oz (fun Q:L[X]=>Q.coeff (n+d t)) (hsum t)
  have hzero :=hli _ hlead
  have hfn (k :ι) :f k=0:= by
    by_contra hk
    have hlt: (f k).natDegree<n :=
      lt_of_le_of_ne (hn k) (fun he=>hk (leadingCoeff_eq_zero.mp (by
        rw [← IU,he,hzero])))
    have hn0:n≠0:= by omega
    have hprev :n≤n - 1 :=IT fun k' _=> by
      have hbd:=hn k'
      by_cases hq:f k' = 0
      · simp [hq]
      · have hne : (f k').natDegree≠n:= fun he =>
          hq (leadingCoeff_eq_zero.mp (by rw [← IU,he,hzero]))
        omega
    omega
  intro k
  have hk :=hf k
  rw [hfn k,ox ,yB] at hk
  have hb0:cy L[X] FX (b:L[X])≠0 :=
    fun hz=>nonZeroDivisors.coe_ne_zero b (hinj (hz.trans (ox _).symm))
  exact (mul_eq_zero.mp hk.symm).resolve_left hb0
private theorem bVO {h} {D:jF h} (Crt:zG D) (word:I→L)
    (s :lJ) (W:ℕ) :
    xu L (aMr Crt word s W).range ≤
      xu FX (VY Crt word s W) := by
  classical
  let F:=aMr Crt word s W
  let b:=Module.finBasis L F.range
  have hex (k :Fin (xu L F.range)) :
      ∃ P:complete Crt word s W,F P=(b k :Position→L) :=(b k).property
  choose P hP using hex
  have hli:C9 L (fun k t =>
      (bwM (P k :Source) t).coeff (anL h s W t)) := by
    change C9 L (F ∘ P)
    have heq :F ∘ P=fun k=>((b k :F.range) :Position→L) :=funext hP
    rw [heq]
    exact b.linearIndependent.map' F.range.subtype F.range.ker_subtype
  have heval :C9 FX (fun k=>U4 (P k :Source)) := by
    apply Sv azk
    have hf :azk ∘ (fun k=>U4 (P k :Source)) =
        fun k t=>cy L[X] FX (bwM (P k :Source) t) :=
      funext fun k=>funext fun t=>dPW (P k :Source) t
    rw [hf]
    exact en2 (fun k=>bwM (P k :Source))
        (anL h s W) (fun k=>gs6 (P k)) hli
  let u (k :Fin (xu L F.range)) :VY Crt word s W :=
    ⟨U4 (P k :Source),RP ⟨_,(P k).property,rfl⟩⟩
  have hu:C9 FX u :=
    Sv (VY Crt word s W).subtype heval
  simpa [F] using hu.fintype_card_le_finrank
private theorem cqC {h} {D:jF h} {Crt:zG D} {word:I→L} {s W}
  (P: (aMr Crt word s W).ker) {j i a e} (hn:Fg (P.1 :Source) j i a e≠0) :
  a+(i+j)*(131071+h)<W+(s.B+s.J)*(2*h)+j:= by
 have he :awN h s W j i a e := by
  by_contra hh
  exact hn (P.1.property.1.1 j i a e hh)
 have hw:=he.2.2.2
 by_contra hlt
 have ha :a=anL h s W (j,i,e) := by
  unfold anL
  dsimp
  omega
 exact hn (by rw [ha]; exact yo (LinearMap.mem_ker.mp P.property) (j,i,e))
private theorem cWB {h} {D:jF h} (Crt:zG D) (word:I→L)
   (s :lJ) (W:ℕ) :xu L (aMr Crt word s (W+1)).ker ≤
     xu L (complete Crt word s W) := by
 let F:=aMr Crt word s (W+1)
 have hm (P:F.ker) : (P.1 :Source)∈complete Crt word s W:= by
   refine ⟨⟨?_,P.1.property.1.2⟩,P.1.property.2⟩
   intro j i a e hb
   by_contra hn
   have he :awN h s (W+1) j i a e := by
     by_contra hh
     exact hn (P.1.property.1.1 j i a e hh)
   have hl:=cqC P hn
   exact hb ⟨he.1,he.2.1,he.2.2.1,by omega⟩
 let f :=((complete Crt word s (W+1)).subtype.comp F.ker.subtype).codRestrict
   (complete Crt word s W) hm
 apply LinearMap.finrank_le_finrank_of_injective (f :=f)
 intro P Q he
 apply C4
 apply C4
 exact oz (fun x :complete Crt word s W=>(x :Source)) he
end
end bRH
end
section
namespace XV
noncomputable section
open cu DP Module Polynomial
open scoped Polynomial
private def avV {R:Type*} [oD R] {b:R[X]} {n:ℕ}
   (hb:b.Monic) (hd:b.natDegree=n) :Basis (Fin n) R (NW b) :=
 (JQ hb).reindex (finCongr hd)
private def Nn {R:Type*} [oD R] {b:R[X]} {n:ℕ}
  (hb:b.Monic) (hd:b.natDegree=n) (a :R[X]) :sS (Fin n) (Fin n) R :=
 R9 (avV hb hd) (sH b a)
private theorem aOT {R:Type*} [oD R] {b:R[X]} {n:ℕ}
   (hb:b.Monic) (hd:b.natDegree=n) (a :R[X]) (i j:Fin n) :
   Nn hb hd a i j=((a*aU (R:=R)^(j:ℕ)) %ₘ b).coeff i:= by
 have hpow (k :Fin b.natDegree) :
     (JQ hb) k=AdjoinRoot.root b^(k :ℕ) :=
   (XJ hb).basis_eq_pow k
 unfold Nn
 rw [SW]
 unfold avV
 rw [Basis.reindex_apply,hpow,← AdjoinRoot.mk_X,← pG,← lV,
   XG,SC,
   Nq]
 rfl
private theorem bsN {R S:Type*} [oD R] [oD S]
  {b a :R[X]} {b' a' : S[X]} {n:ℕ} (f :R →+* S)
  (hb:b.Monic) (hd:b.natDegree=n) (hb' : b'.Monic) (hd' : b'.natDegree=n)
  (hmapb:b.map f=b') (hmapa :a.map f=a') :
  f (Nn hb hd a).det=(Nn hb' hd' a').det:= by
 rw [f.map_det]
 congr 1
 ext i j
 change f (Nn hb hd a i j)=Nn hb' hd' a' i j
 rw [aOT,aOT,← t9,F9 f hb,
  qm,Dw ,Au,hmapa,hmapb]
private theorem bsM {R:Type*} [oD R] [Nontrivial R]
  {b a :R[X]} {n:ℕ} (hb:b.Monic) (hd:b.natDegree=n)
  (hcop:t7 a b) : (Nn hb hd a).det≠0:= by
 obtain ⟨u,v,huv⟩:=hcop
 have hinv :sH b u*sH b a=1 := by
  have h:=oz (sH b) huv
  simpa only [ov,lV,Te,vj,u5 ,vh] using h
 have hmat :Nn hb hd u*Nn hb hd a=1 := by
  unfold Nn
  rw [← lV,hinv,vh]
 have hdet:=oz Matrix.det hmat
 rw [Matrix.det_mul,Ob] at hdet
 intro hz
 rw [hz,vj] at hdet
 exact G0 hdet
private theorem dLJ {R:Type*} [oD R] [Nontrivial R]
  {b:R[X]} {n:ℕ} (hb:b.Monic) (hd:b.natDegree=n) (a q:R[X]) :
  ∃ t:R[X],t.degree<b.degree∧b∣a*t+C (Nn hb hd a).det*q:= by
 let basis :=avV hb hd
 let matrix :=Nn hb hd a
 let target :=sH b (-q)
 let solution :=basis.equivFun.symm (matrix.cramer (basis.equivFun target))
 have hcoord:basis.equivFun solution=matrix.cramer (basis.equivFun target) :=
  basis.equivFun.apply_symm_apply _
 have hsol:sH b a*solution=matrix.det•target := by
  apply basis.equivFun.injective
  have hvec:=X4 basis (sH b a) solution
  change matrix.mulVec (basis.repr solution) = ⇑(basis.repr (sH b a*solution)) at hvec
  rw [← G6,← G6,hcoord,WX] at hvec
  rw [x7]
  exact hvec.symm
 obtain ⟨t,ht⟩:=Xp solution
 have hrep:sH b (t %ₘ b)=solution := by
  rw [← Nq hb,AdjoinRoot.mk_leftInverse hb,ht]
 refine ⟨t %ₘ b,degree_modByMonic_lt _ hb,AdjoinRoot.mk_eq_zero.mp ?_⟩
 change sH b (a*(t %ₘ b)+C matrix.det*q)=0
 rw [ov,lV,lV,hrep,hsol,AdjoinRoot.mk_C]
 simp [target,yB]
private theorem bpD {F:Type*} [lI F] (z :F) (g:F[X]) :
  (g.map (C:F →+* F[X])).map (sI z)=g:= by
 have hc: (sI z).comp (C:F →+* F[X])=uJ F :=
  xI fun x=>Ee
 rw [oY ,hc,Bf]
private theorem bVD {h:ℕ} (D:jF h) (i:Fin 2) :
    ∃ (d:L[X]) (N :lz L[X]),
      d≠0∧N.degree<(2*h:ℕ) ∧
      (D.block (CI i)).map C∣N ∧
      (D.block i).map C ∣
        ((D.constant i).map C+C (aU (R:=L))*(D.slope i).map C)*N +
          C (d*aU (R:=L))*(D.offset i).map C ∧
      ∀ z,t7 (D.constant i+C z*D.slope i) (D.block i)→d.eval z≠0:= by
  let b:=(D.block i).map (C:L →+* L[X])
  let e :=(D.block (CI i)).map (C:L →+* L[X])
  let wK:=(D.constant i).map (C:L →+* L[X]) +
    C (aU (R:=L))*(D.slope i).map (C:L →+* L[X])
  let a :=wK*e
  let q:=C (aU (R:=L))*(D.offset i).map (C:L →+* L[X])
  have hb:b.Monic:=(D.monic i).map _
  have he :e.Monic:=(D.monic (CI i)).map _
  have hbd:b.natDegree=h:=((D.monic i).natDegree_map _).trans (D.degree i)
  have hed:e.natDegree=h :=
    ((D.monic (CI i)).natDegree_map _).trans (D.degree (CI i))
  have hcop:t7 (D.block (CI i)) (D.block i) := by
    fin_cases i
    · exact D.coprime.symm
    · exact D.coprime
  let d:=(Nn hb hbd a).det
  have hregular (z :L) (hz :t7 (D.constant i+C z*D.slope i) (D.block i)) :
      d.eval z≠0:= by
    have hmapa :a.map (sI z) =
        (D.constant i+C z*D.slope i)*D.block (CI i) := by
      simp only [a,wK,e,yl,qm,oZ,
        bpD,coe_evalRingHom,eval_X]
    change (sI z) (Nn hb hbd a).det≠0
    rw [bsN (sI z) hb hbd (D.monic i) (D.degree i)
      (bpD z (D.block i)) hmapa]
    exact bsM _ _ (hz.mul_left hcop)
  have hd:d≠0:= by
    have hc:t7 (D.constant i) (D.block i) :=(D.determinant i).of_mul_left_right
    intro hd
    exact hregular 0 (by simpa using hc) (by simp [hd])
  obtain ⟨t,ht,hdiv⟩:=dLJ hb hbd a q
  refine ⟨d,e*t,hd,?_,Pj _ _,?_,hregular⟩
  · by_cases ht0:t=0
    · rw [ht0,vj,degree_zero]
      exact WithBot.bot_lt_coe _
    have htn:t.natDegree<h:= by
      rw [G7 ht0,G7 hb.ne_zero,hbd,Nat.cast_lt] at ht
      exact ht
    apply (degree_mul_le e t).trans_lt
    rw [G7 he.ne_zero,G7 ht0,hed,← Nat.cast_add,Nat.cast_lt]
    omega
  · change b∣wK*(e*t)+C (d*aU (R:=L))*(D.offset i).map C
    simpa only [a,q,← t8 ,← lV] using hdiv
end
end XV
end
section
namespace bay
noncomputable section
open K1 cu DP axj Polynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxHeartbeats 1000000
private def aVp {A B:Type*} [c9 A] [c9 B]
  (base :A →+* B) (y v :B) :lz (lz A) →+* B :=
 oy (oy base y) v
@[simp] private theorem bHY {A B:Type*} [c9 A] [c9 B]
   (base :A →+* B) (y v :B) (a :A) :
   aVp base y v (C (C a))=base a := by
  simp [aVp]
@[simp] private theorem cVR {A B:Type*} [c9 A] [c9 B]
   (base :A →+* B) (y v :B) :
   aVp base y v (C aU)=y := by
  simp [aVp]
@[simp] private theorem cVQ {A B:Type*} [c9 A] [c9 B]
   (base :A →+* B) (y v :B) :
   aVp base y v aU=v := by
  simp [aVp]
private abbrev aJc:US:=C (aU (R:=VD))
private abbrev a7z :US:=aU
private abbrev Ti:VD →+* US:=pW
private abbrev a7y :pU VD →+* pU US :=
 wB Ti
private theorem b3P {h:ℕ} {D:jF h} (Crt:zG D) :
    (forward Crt).toRingHom=aVp (Ti.comp au5.toRingHom)
      (Ti (IE D)*aJc+Ti (OY Crt))
      (Ti (IE D)*a7z+Ti (IE D).derivative*aJc +
        Ti (OY Crt).derivative) :=
  rfl
private theorem bGU {h:ℕ} {D:jF h} (Crt:zG D) (P:qC[X]) :
  forward Crt (C (C P))=Ti (au5 P) := by
 change (forward Crt).toRingHom (C (C P))= _
 rw [b3P,bHY,oq]
 rfl
private theorem cSV {h:ℕ} {D:jF h} (Crt:zG D) (a :qC) :
  (forward Crt).toRingHom (C (C (C a)))=Ti (C (cy qC aQ a)) := by
 change forward Crt _ = _
 rw [bGU]
 change Ti ((C a).map (cy qC aQ))= _
 rw [oZ]
private def aJa (i:Fin 2) (E :VD) (B B₁:pU VD) :
  US →+* pU US :=
 aVp (a7y.comp (YH i E))
  (n5 aJc-a7y (n5 E*B))
  (n5 a7z+a7y (n5 E.derivative*B-PowerSeries.C E*B₁))
private theorem c67 (i:Fin 2) (E :VD) (B B₁:pU VD) :
  aJa i E B B₁ aJc=n5 aJc-a7y (n5 E*B) :=
 cVR _ _ _
private theorem fTV (i:Fin 2) (E :VD) (B B₁:pU VD) :
  aJa i E B B₁ a7z =
   n5 a7z+a7y (n5 E.derivative*B-PowerSeries.C E*B₁) :=
 cVQ _ _ _
private theorem c66 (i:Fin 2) (E :VD) (B B₁:pU VD)
  (P:VD) (hP:YH i E P=n5 P) :
  aJa i E B B₁ (Ti P)=n5 (Ti P) := by
 change aJa i E B B₁ (C (C P))= _
 simp [aJa,hP]
private theorem dEj {R:Type*} [oD R] (H E T l B:R) :
 H*(T-E*B)+(l+H*E*B)=H*T+l:= by ring
private theorem dEn {R:Type*} [oD R] (H H' E E' T V l B B₁:R) :
 H*(V+(E' * B-E*B₁))+H' * (T-E*B) +
   (l+(H' * E - H*E')*B+H*E*B₁)=H*V+H' * T+l:= by ring
private theorem edE {h:ℕ} {D:jF h} (Crt:zG D) (i:Fin 2)
    (B B₁:pU VD)
    (hY:YH i (X9 (D.block i)) (OY Crt) =
      n5 (OY Crt)+PowerSeries.C (IE D) *
        n5 (X9 (D.block i))*B)
    (hV:YH i (X9 (D.block i)) (OY Crt).derivative =
      n5 (OY Crt).derivative +
        (n5 (IE D).derivative*n5 (X9 (D.block i)) -
          n5 (IE D)*n5 (X9 (D.block i)).derivative)*B +
        n5 (IE D)*n5 (X9 (D.block i))*B₁) :
    let E :=X9 (D.block i)
    (aJa i E B B₁).comp (forward Crt).toRingHom =
      (zE (Ti (E^2))).comp
        ((wB (forward Crt).toRingHom).comp (awA i)) := by
  let E :=X9 (D.block i)
  let F:=(forward Crt).toRingHom
  let Φ:=aJa i E B B₁
  let S:=zE (Ti (E^2))
  have hH :YH i E (IE D)=n5 (IE D) :=
    bNm i E (Iy D)
  have hH' : YH i E (IE D).derivative=n5 (IE D).derivative :=
    dcg i E (Iy D)
  have hbase (P:VD) (hp:YH i E P=n5 P) :
      Φ (Ti P)=n5 (Ti P) :=c66 _ _ _ _ _ hp
  change Φ.comp F=S.comp ((wB F).comp (awA i))
  apply zS
  · apply zS
    · apply p6
      · intro a
        change Φ (F (C (C (C a))))=S (wB F (awA i (C (C (C a)))))
        rw [show F (C (C (C a)))= _ from cSV Crt a]
        change aJa i E B B₁ (C (C (C (cy qC aQ a))))= _
        apply PowerSeries.ext
        intro n
        simp only [aJa,bHY,oq,YH,bwl,
          dcU,aN2,awA,S,Vq,
          MS ,F,cSV,lV,pG]
      · change Φ (F (C (C aU)))=S (wB F (awA i (C (C aU))))
        rw [show F (C (C aU))=Ti aU from
          (bGU Crt _).trans (oz Ti (Au _))]
        simp only [awA,bwl,bNQ,Df]
        change Φ (Ti aU)=S (n5 (F (C (C aU))))
        rw [show F (C (C aU))=Ti aU from
          (bGU Crt _).trans (oz Ti (Au _)),a7N]
        exact hbase _ (by simp [YH,a7N])
    · change Φ (F (C aU))=S (wB F (awA i (C aU)))
      simp only [awA,bwl,bNQ,Df ,S,
        a7N]
      change Φ (F (C aU))=n5 (F (C aU))
      simp only [F,b3P,cVR,ov,lV,hbase _ hH]
      change YH i E _ = _ at hY
      have he :Φ (Ti (OY Crt)) =
          a7y (YH i E (OY Crt)) :=
        bHY _ _ _ _
      rw [he,hY,show Φ aJc= _ from c67 i E B B₁]
      simp only [ov,lV,Df]
      exact dEj _ _ _ _ _
  · change Φ (F aU)=S (wB F (awA i aU))
    simp only [awA,bNQ,Df ,S,a7N]
    simp only [F,b3P,cVQ,ov,lV,hbase _ hH,hbase _ hH']
    change YH i E _ = _ at hV
    have he :Φ (Ti (OY Crt).derivative) =
        a7y (YH i E (OY Crt).derivative) :=
      bHY _ _ _ _
    rw [he,hV,show Φ a7z= _ from fTV i E B B₁,
      show Φ aJc= _ from c67 i E B B₁]
    simp only [ov,lV,Fz ,Df]
    exact dEn _ _ _ _ _ _ _ _ _
private theorem ef7 (P:L[X]) :
   au5 (aXQ P)=X9 P:= by
 change (P.map nq).map (cy qC aQ) =
   P.map (cy L aQ)
 rw [oY]
 have h: (cy qC aQ).comp (nq:L →+* qC) =
     algebraMap L aQ:= by
   apply xI
   intro a
   rw [oq,← vH,← zc]
 rw [h]
theorem proof :axj.c2 := by
 intro h D Crt s Q hQ i r
 let E :=X9 (D.block i)
 let H :=IE D
 let m:=s.B+s.J
 obtain ⟨B,B₁,hY,hV⟩:=dRG Crt i
 let Φ:=aJa i E B B₁
 have hcompat :=zd (edE Crt i B B₁ hY hV) Q
 have hr :=oz (zg r) hcompat
 change zg r (Φ (forward Crt Q)) =
   zg r (zE (Ti (E^2))
     (wB (forward Crt).toRingHom (awA i Q))) at hr
 rw [Vq,MS ,gta] at hr
 have hrow:forward Crt (BA D i r Q) =
     (Ti (E^2))^r*forward Crt (awz i r Q) := by
   rw [BA,lV]
   change forward Crt (C (C (aXQ (D.block i^(2*r)))))*_ = _
   rw [bGU,ef7,X9,Dw ,pow_mul,pG]
   rfl
 change Ti (H^m)∣forward Crt Q at hQ
 obtain ⟨W,hW⟩:=hQ
 have hfix :Φ (Ti (H^m))=n5 (Ti (H^m)) := by
   apply c66
   rw [pG,show YH i E H=n5 H from
     bNm i E (Iy D),pG]
 rw [hW,lV,hfix,PowerSeries.coeff_C_mul] at hr
 change Ti (H^m)∣forward Crt (BA D i r Q)
 exact ⟨zg r (Φ W),hrow.trans hr.symm⟩
end
end bay
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace cyU
noncomputable section
open cu DP Ge anc Polynomial
open scoped BigOperators Polynomial
private theorem gva {R S:Type} [c9 R] [c9 S]
   (f :R →+* S) (y :S[X]) :
   substitute (pW.comp f) (C y) aU =
     oK (oy (C.comp f) y) := by
 apply b6I
 · intro a
   rw [a8R]
   simp [pW]
 · simp
 · simp
private theorem cEB {F:Type} [lI F] (α:F) (z :kq F)
   (P:Gm F) (j:ℕ) :
   let f :=(PM (cy F (kq F) α)).toRingHom.comp
     (oK (cy (i5 F) (kq F)))
   ((GV α z P).coeff j) =
     oy (C.comp f) (aU +C (C z)) (P.coeff j) := by
 dsimp only
 unfold GV
 rw [show (C aU +pW (C z) :EM (kq F)) =
   C (aU +C (C z)) by simp [pW],gva,
   vG,t9]
private theorem deQ {F:Type} [lI F] {s :lJ}
  {P:Gm F} (hP:adk s P) {i j:ℕ}
  (h : ¬ (i+j≤ s.B∧j≤ s.J)) : (P.coeff j).coeff i=0:= by
 apply pQ
 intro a
 rw [v8]
 apply y5
 intro e
 change aQu P j i a e=0
 by_contra hn
 exact h ⟨(hP j i a e hn).1,(hP j i a e hn).2.1⟩
private theorem cEA {F:Type} [lI F] (α:F) (z :kq F)
    (P:Gm F) (i j N :ℕ) (hN : (P.coeff j).natDegree<N) :
    ((GV α z P).coeff j).coeff i =
      ∑ n∈xL N,
        C ((n.choose i:kq F)*z^(n - i)) *
          (beE α P j n).map (cy (i5 F) (kq F)) := by
  rw [cEB]
  conv_lhs=>rw [(P.coeff j).as_sum_range_C_mul_X_pow' hN]
  simp only [zh,eval₂_finsetSum,eval₂_mul,eval₂_pow,pL,u8 ,
    wR,yL,coeff_X_add_C_pow,oq,vG]
  refine p7 rfl fun n _ => ?_
  have hc:cy (i5 F) (kq F) (cy F (i5 F) α) =
      cy F (kq F) α :=
    (zc F (i5 F) (kq F) α).symm
  rw [beE,map_taylor,hc,← (C (R:=kq F)).map_pow,
    ← G3 (C (R:=kq F)),← lV (C (R:=kq F)),
    t4 (z^(n - i)),t4]
  rfl
private theorem c3h {R:Type} [c9 R] {s :lJ}
   (f : (q:jJ s)→NQ s q.val→R[X]) (q:jJ s)
   (k :NQ s q.val) (i j:ℕ) :
   ((C (C (f q k)*aU ^(q.val - k.val))*aU ^k.val).coeff j).coeff i =
     if j=k.val∧i+j=q.val then f q k else 0:= by
 have hk :k.val≤q.val :=(Nat.lt_succ_iff.mp k.isLt).trans (II ..)
 by_cases hj:j=k.val
 · have hi:i=q.val - k.val↔i+j=q.val := by omega
   simp only [coeff_C_mul_X_pow,hj,GR ,true_and,hi]
 · simp only [coeff_C_mul_X_pow,hj,Gj,false_and,v8]
private theorem eIR {R:Type} [c9 R] (s :lJ)
    (f : (q:jJ s)→NQ s q.val→R[X]) (i j:ℕ)
    (hq:i+j≤ s.B) (hj:j≤ s.J) :
    ((aIP s f).coeff j).coeff i =
      f ⟨i+j,xW hq⟩
        ⟨j,xW (le_min (show j≤ i+j by omega) hj)⟩:= by
  let q:jJ s :=⟨i+j,xW hq⟩
  let k :NQ s q.val :=⟨j,xW (le_min (by dsimp [q]; omega) hj)⟩
  change _=f q k
  simp only [aIP,wR,c3h]
  rw [Ok q (u9 q)]
  · rw [Ok k (u9 k)]
    · simp [q,k]
    · intro k' _ hne
      have hval :j≠k'.val := fun he=>hne (zm he.symm)
      simp [hval]
  · intro q' _ hne
    have hval :i+j≠q'.val := fun he=>hne (zm he.symm)
    simp [hval]
private theorem eIS {R:Type} [c9 R] (s :lJ)
  (f : (q:jJ s)→NQ s q.val→R[X]) (i j:ℕ)
  (h : ¬ (i+j≤ s.B∧j≤ s.J)) :
  ((aIP s f).coeff j).coeff i=0:= by
 simp only [aIP,wR,c3h]
 refine t5 fun q _=>t5 fun k _ => ?_
 have hq:q.val≤ s.B:=Nat.lt_succ_iff.mp q.isLt
 have hk :k.val≤ s.J:=(Nat.lt_succ_iff.mp k.isLt).trans (min_le_right ..)
 have hn : ¬ (j=k.val∧i+j=q.val) := by omega
 simp [hn]
theorem proof :anc.c1 := by
  intro F _ s α z P hP
  apply pQ
  intro j
  apply pQ
  intro i
  have hN : (P.coeff j).natDegree<s.B - j+1 := by
    apply xW
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact deQ hP (by omega)
  by_cases h:i+j≤ s.B∧j≤ s.J
  · rcases h with ⟨hq,hj⟩
    rw [eIR s _ i j hq hj]
    rw [cEA α z P i j (s.B - j+1) hN]
    let term (n:ℕ) :=C ((n.choose i:kq F)*z^(n - i)) *
      (beE α P j n).map (cy (i5 F) (kq F))
    change (∑ n∈xL (s.B - j+1),term n)= _
    have hs :=Finset.sum_range_add term i (s.B-(i+j)+1)
    rw [show i+(s.B-(i+j)+1)=s.B - j+1 by omega] at hs
    have hzero : (∑ n∈xL i,term n)=0:= by
      refine t5 fun n hn => ?_
      simp [term,Xu (Finset.mem_range.mp hn)]
    rw [hs,hzero,v9]
    rw [← zf (fun n=>term (i+n)) (s.B-(i+j)+1)]
    unfold aVG
    refine p7 rfl fun n _ => ?_
    have hi:i+j - j=i:= by omega
    simp only [term,bHT,hi,Nat.add_sub_cancel_left]
  · rw [eIS s _ i j h]
    by_cases hj:j≤ s.B∧j≤ s.J
    · rw [cEA α z P i j (s.B - j+1) hN]
      refine t5 fun n hn => ?_
      have hn' := Finset.mem_range.mp hn
      simp [ Xu (show n< i by omega)]
    · have hrow:P.coeff j=0:= by
        exact Polynomial.ext fun n=>(deQ hP (by omega)).trans
          (v8  n).symm
      rw [cEB,hrow,ox ,v8]
end
end cyU
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace bzR
noncomputable section
open K1 cu DP Ge Polynomial
open scoped BigOperators Polynomial
private abbrev af :=ℕ×ℕ×ℕ×Exponent
private def ah7 {R:Type} [oD R] (Q:Gm R) (G: (i5 R)[X])
   (r :af) :R :=
 ((((Q.coeff r.1).coeff r.2.1) %ₘ G).coeff r.2.2.1).coeff r.2.2.2
private def dbS (Q:Gm Parameter) (G: (i5 Parameter)[X]) :
  Finset af :=
 Q.support.biUnion fun j=>(Q.coeff j).support.biUnion fun i =>
  let p:=(Q.coeff j).coeff i %ₘ G
  p.support.biUnion fun a=>(p.coeff a).support.image fun e=>(j,i,a,e)
private theorem eAf (Q:Gm Parameter) (G: (i5 Parameter)[X])
   (r :af) (hr :ah7 Q G r≠0) :r∈dbS Q G:= by
 obtain ⟨j,i,a,e⟩:=r
 refine Finset.mem_biUnion.mpr ⟨j,Polynomial.mem_support_iff.mpr ?_,?_⟩
 · intro h
   exact hr (by simp [ah7,h])
 refine Finset.mem_biUnion.mpr ⟨i,Polynomial.mem_support_iff.mpr ?_,?_⟩
 · intro h
   exact hr (by simp [ah7,h])
 refine Finset.mem_biUnion.mpr ⟨a,Polynomial.mem_support_iff.mpr ?_,?_⟩
 · intro h
   exact hr (by simp [ah7,h])
 exact Finset.mem_image.mpr ⟨e,MvPolynomial.mem_support_iff.mpr hr,rfl⟩
private theorem fUg {F:Type} [lI F] (point :Parameter →+* F)
  (Q:Gm Parameter) {G: (i5 Parameter)[X]} (hG:G.Monic) (r :af) :
  ah7 (avv point Q) (G.map (oj point)) r =
    point (ah7 Q G r) := by
 simp only [ah7,avv,vG,t9,
  ← F9 (oj point) hG,G8]
private def c7q {F:Type} [lI F] (G: (i5 F)[X])
   (r :af) :Gm F →ₗ[F] F :=
 (Wm F r.2.2.2).comp <|
   ((Dz (i5 F) r.2.2.1).restrictScalars F).comp <|
   ((Polynomial.modByMonicHom G).restrictScalars F).comp <|
   ((Dz (i5 F)[X] r.2.1).restrictScalars F).comp <|
   (Dz ((i5 F)[X])[X] r.1).restrictScalars F
private theorem fUh {F ι:Type} [lI F] [p5 ι]
  (Q:ι→Gm F) (v :ι→F) (G: (i5 F)[X]) (r :af) :
  ah7 (∑ k,v k•Q k) G r = ∑ k,v k * ah7 (Q k) G r := by
 change c7q G r (∑ k,v k•Q k) = ∑ k,v k•c7q G r (Q k)
 simp only [qG,x7]
private theorem dYE {F:Type} [lI F] (Q:Gm F)
   {G: (i5 F)[X]} (hG:G.Monic) :
   (pW (G.map (cy (i5 F) (kq F))) :EM (kq F)) ∣
     JH (cy (i5 F) (kq F)) Q ↔
     ∀ r,ah7 Q G r=0:= by
 let f :=cy (i5 F) (kq F)
 have h: (pW (G.map f) :EM (kq F))∣JH f Q ↔
     ∀ j i,(Q.coeff j).coeff i %ₘ G=0:= by
   simp only [pW,oq,SU,
     JH,vG,t9]
   apply forall_congr'
   intro j
   apply forall_congr'
   intro i
   rw [← Ml (hG.map f),← F9 f hG,
     Polynomial.map_eq_zero_iff (qM (i5 F) (kq F))]
 rw [h]
 constructor
 · intro hz r
   simp [ah7,hz]
 · intro hz j i
   apply pQ
   intro a
   rw [v8]
   apply y5
   intro e
   simp only [In,Hw]
   exact hz (j,i,a,e)
private theorem ezR {ι:Type} [p5 ι]
    (Q:ι→Gm Parameter) (G: (i5 Parameter)[X]) (hG:G.Monic) :
    ∃ n:ℕ,∃ M:sS (Fin n) ι Parameter,
      ∀ (F:Type) [lI F] (point :Parameter →+* F) (v :ι→F),
        (M.map point).mulVec v=0 ↔
          (pW (G.map (aee point)) :EM (kq F)) ∣
            ∑ k,v k•JH (aee point) (Q k) := by
  classical
  let rows :=Finset.univ.biUnion fun k=>dbS (Q k) G
  let e :Fin rows.card ≃ ↥rows :=(LP (Pv rows)).symm
  let M:sS (Fin rows.card) ι Parameter := fun r k=>ah7 (Q k) G (e r).val
  refine ⟨rows.card,M,?_⟩
  intro F _ point v
  let inc:=cy (i5 F) (kq F)
  let incAlg:Gm F →ₐ[F] EM (kq F) :=
    vl (vl (vl (vw F (i5 F) (kq F))))
  let G' := G.map (oj point)
  let Q' : ι→Gm F:= fun k=>avv point (Q k)
  let q := ∑ k,v k•Q' k
  have hcomp (k :ι) :incAlg (Q' k)=JH (aee point) (Q k) := by
    change JH inc (JH (oj point) (Q k))= _
    apply pQ
    intro j
    apply pQ
    intro i
    apply pQ
    intro a
    simp only [JH,vG,t9,aee,inc,oq]
  have hq:JH inc q = ∑ k,v k•JH (aee point) (Q k) := by
    change incAlg (∑ k,v k•Q' k)= _
    simp only [qG,x7,hcomp]
  rw [← hq,← oY (oj point) inc,dYE q (hG.map _)]
  have hread (r :af) :ah7 q G' r = ∑ k,v k*point (ah7 (Q k) G r) := by
    rw [fUh]
    simp only [Q',G',fUg point _ hG]
  have heval (r :Fin rows.card) : ((M.map point).mulVec v) r=ah7 q G' (e r).val := by
    rw [hread]
    change ∑ k,point (ah7 (Q k) G (e r).val)*v k= _
    simp only [t4]
  change (M.map point).mulVec v=0 ↔ ∀ r,ah7 q G' r=0
  constructor
  · intro hv r
    by_cases hr :r∈rows
    · have he :=yo hv (e.symm ⟨r,hr⟩)
      rw [heval] at he
      simpa only [Equiv.apply_symm_apply,Et] using he
    · rw [hread]
      apply t5
      intro k _
      have hz :ah7 (Q k) G r=0:= by
        by_contra hn
        exact hr (Finset.mem_biUnion.mpr ⟨k,u9 k,eAf _ _ _ hn⟩)
      rw [hz,ox ,vj]
  · intro hv
    funext r
    exact (heval r).trans (hv (e r).val)
theorem proof :Ge.c4 := by
  classical
  intro h D Crt E s ι _ P hP
  let G:=(E.H.map (nq (σ:=Fin 2)))^(s.B+s.J)
  obtain ⟨n,M,hM⟩:=ezR (fun k=>BA s E.H E.num E.den (P k)) G
    ((E.monic.map _).pow _)
  have RS {F:Type} [lI F] (point :Parameter →+* F)
      (hd:oj point E.den≠0) (v :ι→F) :
      (M.map point).mulVec v=0 ↔
        a0X s (E.H.map point) (Ua point E.num E.den)
          (Du F (fun k=>avv (point.comp (mD (R:=L))) (P k)) v) := by
    let f :=Ge.forward (E.H.map point) (Ua point E.num E.den)
    let d:=awj (aee point E.den)
    have hu:IsUnit d:= by
      have hn:aee point E.den≠0:= by
        intro hzero
        exact hd (qM (i5 F) (kq F) (hzero.trans (ox _).symm))
      exact (isUnit_iff_ne_zero.mpr hn).map (pW.comp mD)
    rw [hM F point v]
    simp only [dLM point s E.H E.num E.den hd _ (hP _)]
    have hsum: (∑ k,v k•(d^s.B*f (avv (point.comp (mD (R:=L))) (P k)))) =
        d^s.B*f (Du F
          (fun k=>avv (point.comp (mD (R:=L))) (P k)) v) := by
      simp only [SM,qG,x7,FR,
        mul_smul_comm]
    have hG:G.map (aee point) =
        ((E.H.map point).map (cy F (kq F)))^(s.B+s.J) := by
      simp only [G,Dw ,bIS]
    rw [hsum,(hu.pow s.B).dvd_mul_left,hG]
    rfl
  refine ⟨n,M,?_,RS genericPoint E.genericDen⟩
  intro v
  have hpoint :Uv.comp (mD (R:=L))=uJ L:= by
    ext a
    simp [Uv]
  have hmap (Q:Source) :avv (uJ L) Q= Q:= by
    apply pQ
    intro j
    apply pQ
    intro i
    apply pQ
    intro a
    simp only [avv,vG,t9,MvPolynomial.map_id]
  simpa only [E.specialH,E.specialLift,hpoint,hmap] using RS Uv E.specialDen v
end
end bzR
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace cyV
noncomputable section
open cu DP Ge anc Polynomial
open scoped BigOperators Polynomial
private def slot {R:Type} [c9 R] (a :R[X]) (i k :ℕ) :EM R :=
 pW a*(C (aU (R:=R[X])))^i*aU ^k
private theorem c3i {R:Type} [c9 R] (s :lJ)
  (f : (q:jJ s)→NQ s q.val→R[X]) :
  aIP s f = ∑ q:jJ s,∑ j:NQ s q.val,
    slot (f q j) (q.val - j.val) j.val := by
 simp only [aIP,slot,pW,oq,lV,pG]
private theorem gNd {R:Type} [c9 R] (a :R[X]) (i j:ℕ) :
   aJ3 (slot a i j) = ∑ k∈xL (j+1),
     slot (a*C (j.choose k :R)*aU ^(i+k)) (i+(j - k)) k := by
 simp only [slot,lV,pG,aJ3,a8R,
   bw3,bOt]
 rw [add_pow,FR]
 apply p7 rfl
 intro k _
 simp only [GY ,yQ,G3]
 ac_rfl
private theorem gw5 {M:Type*} [AddCommMonoid M] {s :lJ} {q:ℕ}
   (j:NQ s q) (g:ℕ→M) :
   (∑ k∈xL (j.val+1),g k) =
     ∑ k :NQ s q,if k.val≤j.val then g k.val else 0:= by
 rw [zf (fun k=>if k≤j.val then g k else 0)]
 calc
   _ = ∑ k∈xL (j.val+1),(if k≤j.val then g k else 0) := by
     apply p7 rfl
     intro k hk
     rw [HZ (VC (Finset.mem_range.mp hk))]
   _ = _:= by
     refine Un (Finset.range_mono (Nat.succ_le_of_lt j.isLt)) ?_
     intro k _ hk
     exact z9 (fun h=>hk (Finset.mem_range.mpr (xW h)))
private theorem gNb {E :Type} [lI E] (s :lJ) (q:ℕ)
    (f :NQ s q→E[X]) (j:NQ s q) :
    aJ3 (slot (f j) (q - j.val) j.val) =
      ∑ k :NQ s q,if k.val≤j.val then
        slot (f j*C (j.val.choose k.val :E)*aU ^(q - j.val+k.val))
          (q - k.val) k.val else 0:= by
  rw [gNd,gw5 j]
  apply p7 rfl
  intro k _
  by_cases h:k.val≤j.val
  · have hj:j.val≤q:=(VC j.isLt).trans (II _ _)
    simp only [HZ h,show q - j.val+(j.val - k.val)=q - k.val by omega]
  · simp only [z9 h]
private theorem gNc {E :Type} [lI E] (s :lJ)
  (f : (q:jJ s)→NQ s q.val→E[X]) :
  aJ3 (aIP s f)=aIP s (fun q k=>aRi s q.val (f q) k) := by
 simp only [c3i,qG]
 apply p7 rfl
 intro q _
 simp_rw [gNb s q.val (f q)]
 rw [Finset.sum_comm]
 apply p7 rfl
 intro k _
 simp only [aRi,slot,qG,EP]
 apply p7 rfl
 intro j _
 split_ifs <;> simp
theorem proof :anc.c2 := by
 intro F _ s f h
 rw [gNc,c3i]
 apply Gi
 intro q _
 apply Gi
 intro k _
 unfold slot
 have hc: (pW (aU ^(s.B+s.J)) :EM (kq F)) ∣
     pW (aRi s q.val (f q) k) :=
   vk pW (h q k)
 exact Vl (Vl hc _) _
end
end cyV
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace bjE
noncomputable section
open K1 cu DP Polynomial
open scoped Polynomial
private abbrev aet:=vZ aZ
private abbrev dmK:=lz (lz aet)
private def ady {A B:Type*} [p9 A] [p9 B] (f :A →+* B) :
  lz (lz A) →+* lz (lz B) :=
 oK (oK f)
private theorem ezg {A B C' : Type*} [c9 A] [c9 B]
   [c9 C'] (f :A →+* B) (g:B →+* C') (y v :lz (lz B)) :
   (ady g).comp (substitute f y v) =
     substitute (g.comp f) (ady g y) (ady g v) := by
 apply zS
 · apply p6
   · intro a
     simp [substitute,ady,pW]
   · simp [substitute]
 · simp
private theorem gvb {A B C' : Type*} [c9 A] [c9 B]
   [c9 C'] (f :A →+* B) (g:B →+* C') (y v :lz (lz C')) :
   (substitute g y v).comp (ady f)=substitute (g.comp f) y v := by
 apply zS
 · apply p6
   · intro a
     simp [substitute,ady]
   · simp [substitute,ady]
 · simp [ady]
private def pO:qC →+* aZ :=
 oj (cy L FX)
private abbrev ξ:FX:=cy L[X] FX (aU:L[X])
private def alC:qC[X] →+* aZ :=
 oy pO (nq ξ)
private theorem dGu (P:Source) :U4 P=ady alC P:=rfl
private def wZ:aQ →+* aet :=
 IsFractionRing.lift (g:=(cy aZ aet).comp pO)
  ((qM aZ aet).comp
    (S2 (cy L FX) (FaithfulSMul.algebraMap_injective L FX)))
private def aaO:aQ[X] →+* aet :=
 oy wZ (cy FX aet ξ)
private theorem d1K :
   aaO.comp au5.toRingHom=(cy aZ aet).comp alC:= by
 apply p6
 · intro a
   change aaO ((C a).map (cy qC aQ)) =
    cy aZ aet (alC (C a))
   simp [aaO,alC,wZ]
 · change aaO ((aU:qC[X]).map (cy qC aQ)) =
    cy aZ aet (alC aU)
   simp only [Au,aaO,alC,zh,u8]
   rfl
private theorem d1I {h} (D:jF h) :
    aaO (IE D)=cy FX aet (cy L[X] FX (Iy D)) := by
  have he :aaO.comp (oK (cy L aQ)) =
      (cy FX aet).comp (cy L[X] FX) := by
    apply p6
    · intro a
      change aaO ((C a).map (cy L aQ)) =
        cy FX aet (cy L[X] FX (C a))
      simp only [oZ,aaO,zh,pL]
      change wZ (cy qC aQ (nq a))= _
      simp only [wZ,IsFractionRing.lift_algebraMap,oq,pO,
        JM]
      rfl
    · change aaO ((aU:L[X]).map (cy L aQ)) =
        cy FX aet ξ
      simp [aaO]
  exact zd he (Iy D)
private theorem d1J {h} (D:jF h) :aaO (IE D)≠0:= by
 rw [d1I]
 have hne :=((qM L[X] FX).ne ((D.monic 0).mul (D.monic 1)).ne_zero)
 exact (map_ne_zero (cy FX aet)).2 (by simpa only [Iy,ox] using hne)
private def aJB {h} {D:jF h} (Crt:zG D) :Jet →ₐ[FX] dmK where
 toRingHom:=substitute (cy aZ aet)
  (ady aaO (bgw D Crt)) (ady aaO (bgz D Crt))
 commutes' x := by
  change substitute _ _ _ (pW (nq x)) =
    pW (cy FX aet x)
  simp [substitute,pW]
  rfl
private theorem dfe {h} {D:jF h} (Crt:zG D) (P:Source) :
   aJB Crt (U4 P)=ady aaO (forward Crt P) := by
 rw [dGu,b3N]
 change ((substitute _ _ _).comp (ady alC)) P =
    ((ady aaO).comp (substitute au5.toRingHom _ _)) P
 rw [ezg,gvb,d1K]
private def bq7 {A B:Type*} [c9 A] [c9 B]
  (f :A →+* B) (y :B[X]) :A[X] →+* B[X] :=
 oy (C.comp f) y
private theorem cVl {A B:Type*} [c9 A] [c9 B]
  (f :A →+* B) (y :B[X]) (p:A[X]) :
  bq7 f y p=(p.map f).comp y := by
 change _=(p.map f).eval₂ C y
 rw [eval₂_map]
 rfl
private theorem gu9 {A B:Type*} [c9 A] [c9 B]
  (f :A →+* B) (y :B[X]) (v :lz B[X]) (P:lz A[X]) :
  substitute f (C y) v P=(P.map (bq7 f y)).comp v := by
 change P.eval₂ (oy ((pW (R:=B)).comp f) (C y)) v =
  (P.map (bq7 f y)).eval₂ C v
 rw [eval₂_map]
 congr 1
 apply p6 <;> simp [bq7,pW]
private theorem dsE {A B:Type*} [oD A] [oD B] [IsDomain B]
   (f :A →+* B) (hf :uW f) {a b:B} (ha :a≠0)
   (c:B[X]) {P:lz A[X]} (hP:P≠0) :
   let Q:=substitute f (C (C a*aU +C b)) (C (C a)*aU +C c) P
   Q.natDegree=P.natDegree∧Q.leadingCoeff.natDegree=P.leadingCoeff.natDegree∧Q≠0:= by
 let y :B[X] :=C a*aU +C b
 let v :lz B[X] :=C (C a)*aU +C c
 let ev :=bq7 f y
 have ev_degree (p:A[X]) : (ev p).natDegree=p.natDegree := by
   rw [cVl,natDegree_comp,NX ha,FK,Xx hf]
 have ev_inj:uW ev := by
   apply (injective_iff_map_eq_zero ev).mpr
   intro p hp
   by_contra hn
   have hel: (p.map f).leadingCoeff≠0:= by
     apply leadingCoeff_ne_zero.mpr
     intro hz
     apply hn
     exact map_injective f hf (by simpa only [VS] using hz)
   have he :=leadingCoeff_comp (p:=p.map f) (q:=y) (by rw [show y.natDegree=1 from NX ha]; decide)
   rw [show (p.map f).comp y=ev p from (cVl f y p).symm,hp,
     leadingCoeff_zero,leadingCoeff_linear ha] at he
   exact (z7 hel (N0 _ ha)) he.symm
 have ha' : (C a :B[X])≠0:=C_ne_zero.mpr ha
 have hv :v.natDegree=1 :=NX ha'
 have hlead: ((P.map ev).comp v).leadingCoeff=ev P.leadingCoeff*C (a^P.natDegree) := by
   rw [leadingCoeff_comp (by rw [hv]; decide),leadingCoeff_linear ha',
     leadingCoeff_map_of_injective ev_inj,Xx  ev_inj,pG ]
 change (substitute f (C y) v P).natDegree= _ ∧
   (substitute f (C y) v P).leadingCoeff.natDegree= _∧substitute f (C y) v P≠0
 rw [gu9,natDegree_comp,hv,FK,Xx ev_inj,
   hlead,natDegree_mul_C (N0 _ ha),ev_degree]
 refine ⟨rfl,rfl,leadingCoeff_ne_zero.mp ?_⟩
 rw [hlead]
 apply z7 _ (C_ne_zero.mpr (N0 _ ha))
 simpa only [ox] using ev_inj.ne (leadingCoeff_ne_zero.mpr hP)
private theorem dff {h} {D:jF h} (Crt:zG D) {P:Jet}
  (hP:P≠0) :
  (aJB Crt P).natDegree=P.natDegree ∧
  (aJB Crt P).leadingCoeff.natDegree=P.leadingCoeff.natDegree∧aJB Crt P≠0:= by
 let a :=aaO (IE D)
 let b:=aaO (OY Crt)
 let c:aet[X] :=C (aaO (IE D).derivative)*aU +
  C (aaO (OY Crt).derivative)
 have heY:ady aaO (bgw D Crt)=C (C a*aU +C b) := by
  simp [bgw,pW,ady,a,b]
 have heV:ady aaO (bgz D Crt)=C (C a)*aU +C c:= by
  simp [bgz,pW,ady,a,c,ov,lV,add_assoc]
 change (substitute _ _ _ P).natDegree= _∧(substitute _ _ _ P).leadingCoeff.natDegree= _ ∧
  substitute _ _ _ P≠0
 rw [heY,heV]
 exact dsE _ (qM aZ aet) (d1J D) c hP
private def ceD {h} {D:jF h} (Crt:zG D) (j i:ℕ) :Jet →ₗ[FX] aet where
 toFun P:=((aJB Crt P).coeff j).coeff i
 map_add' P Q:= by simp
 map_smul' b P:= by simp [C5]
end
end bjE
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace dni
open cu Ge Polynomial
open scoped BigOperators Polynomial
private theorem bXV {E :Type} [lI E] (s :lJ) (q:ℕ)
    (f :NQ s q→E[X]) (k :NQ s q) (l:ℕ) :
    (aRi s q f k).coeff l =
      ∑ j:NQ s q,
        if k.val≤j.val∧q - j.val+k.val≤l then
          (j.val.choose k.val :E)*(f j).coeff (l-(q - j.val+k.val))
        else 0:= by
  rw [aRi,wR]
  apply p7 rfl
  intro j _
  by_cases hj:k.val≤j.val
  · rw [HZ hj,coeff_mul_X_pow',coeff_mul_C]
    by_cases hl:q - j.val+k.val≤l
    · simp only [hj,hl,and_self,GR,t4]
    · simp [hj,hl]
  · simp [hj]
end dni
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace aY9
noncomputable section
open K1 cu DP Ge Polynomial
open scoped BigOperators Polynomial
private abbrev G:=lN
private abbrev F:=kq G
private abbrev g:Parameter →+* G:=Ge.genericPoint
private abbrev inc:G →+* F:=cy G F
private theorem bqB {d:i5 Parameter} (hd:Uw d≠0) :
   oj g d≠0 :=
 fun hz=>hd (by
   rw [(S2 g b4F)
     (hz.trans (ox (oj g)).symm),ox])
private theorem cTI {h:ℕ} {D:jF h} {Crt:zG D}
    (B : ∀ i,bQl D Crt i) (i:Fin 2) (α:G)
    (hr : (adH D i).eval α=0) (hb: ((D.constant i).map alL).eval α≠0) :
    (∑ j,Ua g (B j).num (B j).den).eval (inc α) =
      residue i (-((D.offset i).map alL).eval α)
        (((D.constant i).map alL).eval α) (((D.slope i).map alL).eval α) := by
  let ev :=oy (aie g) (inc α)
  let z :=cy (i5 G) F (nX i)
  let b:=((D.constant i).map alL).eval α
  let c:=((D.slope i).map alL).eval α
  let a :=((D.offset i).map alL).eval α
  have hcomp: (aie g).comp nq=inc.comp g:= by
    apply xI
    intro x
    simp only [oq,aie,JM]
    rw [zc G (i5 G) F,vH]
  have hparam (P:Parameter[X]) :
      ev (P.map nq)=inc ((P.map g).eval α) := by
    change (P.map nq).eval₂ (aie g) (inc α)= _
    rw [← eval_map,oY ,hcomp,← oY ,eval_map_apply]
  have hL (P:L[X]) :ev (P.map aft)=inc ((P.map alL).eval α) := by
    rw [aft,← oY ,hparam,oY]
  have hC (x :i5 Parameter) :ev (C x)=aie g x :=pL _ _
  have hX:ev (C (nX i))=z := by rw [hC]; simp [aie,z]
  have hA:ev (aNK D i)=inc b+z*inc c:= by
    rw [aNK,ov,lV,hL,hL]
    exact oz (fun x=>inc b + x*inc c) hX
  have hQ:ev (bp0 D i)=z*inc a := by
    rw [bp0,lV,hL]
    exact oz (fun x=>x*inc a) hX
  have hne :inc b+z*inc c≠0:= by
    have hf : (nq b+MvPolynomial.X i*nq c:i5 G)≠0:= by
      intro he
      have hv :=oz (qx (fun _:Fin 2=>(0:G))) he
      exact hb (by simpa [b] using hv)
    have he :cy (i5 G) F (nq b+MvPolynomial.X i*nq c)≠0 :=
      fun hz=>hf ((qM (i5 G) F)
        (hz.trans (ox (cy (i5 G) F)).symm))
    have hinc (x :G) :cy (i5 G) F (nq x)=inc x :=
      (zc G (i5 G) F x).symm
    simpa only [ov,lV,z,hinc] using he
  have hzero :ev (ayS D i)=0:= by rw [ayS,hparam,hr,ox]
  have hnot:ev (B (CI i)).num=0:= by
    have he :=vk ev (B (CI i)).other_dvd
    rw [other_invol,hzero,MO] at he
    exact he
  have hval (j:Fin 2) : (Ua g (B j).num (B j).den).eval (inc α) =
      (aie g (B j).den)⁻¹*ev (B j).num := by
    rw [Ua,Ar,eval_mul,Ee,eval_map]
    rfl
  have he :=vk ev (B i).congruence
  rw [hzero,MO,ov,lV,lV,hA,hQ,hC] at he
  have hd:=bNA g (bqB (B i).specialDen)
  rw [gw0 _ i,eval_add,hval,hval,hnot,vj,u5]
  unfold residue
  change _=inc (-a)*z/(inc b+inc c*z)
  rw [t4 (inc c) z,map_neg]
  apply (eq_div_iff hne).mpr
  calc
    _=(aie g (B i).den)⁻¹*((inc b+z*inc c)*ev (B i).num) := by ring
    _ = -inc a*z := by
      rw [eq_neg_of_add_eq_zero_left he,mul_neg,← t8 ,Mz hd,wY]
      ring
end
end aY9
end
section
namespace wT
noncomputable section
open K1 MvPolynomial
structure N7 (deleted:pC I) where
 N :ℕ
 index :Fin N ↪ I
 Z1 : ∀ i,i∈Kh index↔i∉deleted
 size :N+deleted.card = 262144
def N7.nodes {deleted:pC I} (P:N7 deleted) (i:Fin P.N) :K :=
 node (P.index i)
structure UJ (u:e9) (deleted:pC I) (Γ:pC K) where
 mark : ∀ γ∈Γ,B5 u γ
 survives : ∀ γ (hγ:γ∈Γ) i,i∈(mark γ hγ).support→i∉deleted
inductive Bank
 | symmetric
 | lowS
 | lowT
def Bank.dS:Bank→ℕ
 | .symmetric=>2
 | .lowS=>1
 | .lowT=>2
def Bank.dT:Bank→ℕ
 | .symmetric=>2
 | .lowS=>2
 | .lowT=>1
def Bank.s :Bank→ℕ
 | .symmetric=>10
 | .lowS=>14
 | .lowT=>9
def Bank.t:Bank→ℕ
 | .symmetric=>10
 | .lowS=>9
 | .lowT=>14
def Bank.a (b:Bank) :ℕ:=b.s+5*b.dS
def Bank.b (b:Bank) :ℕ:=b.t+5*(b.dT - 1)
def Bank.E (b:Bank) :ℕ:=b.a+b.b
def Bank.M (b:Bank) :ℕ:=(2*131071 - 1)*(b.E - 1)+1
def Bank.GA (b:Bank) (H :ℕ) :Fin 4→ℕ := ![131071+H,1,b.dS,b.dT]
structure asP (u:e9) {deleted:pC I} (P:N7 deleted)
   (b:Bank) (H :ℕ) where
 L:nI (Fin 5) K
 L_ne :L≠0
 degrees : ∀ j,L.weightedTotalDegree (vO 131071 j)=b.GA H j
 order_one : ∀ i:Fin P.N,
   (RK oH
     (Ko (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
       (u 0 (P.index i)^p) (u 1 (P.index i)^p) L)).natTrailingDegree=1
 numerator :nI (Fin 4) K
 denominator :nI (Fin 4) K
 ayD:denominator≠0
 linear :xx L =
   mD denominator*aU-Polynomial.C numerator
 primitive : (mD denominator*aU-Polynomial.C numerator).IsPrimitive
 numerator_Y:numerator.weightedTotalDegree Qb≤1
 denominator_Y:denominator.weightedTotalDegree Qb≤0
 numerator_S:numerator.weightedTotalDegree ME≤b.dS
 denominator_S:denominator.weightedTotalDegree ME≤b.dS
 numerator_T:numerator.weightedTotalDegree MD ≤b.dT
 denominator_T:denominator.weightedTotalDegree MD ≤b.dT - 1
def LV:Fin 4→ℕ := ![0,1,1,1]
def D4 (u:e9) {deleted:pC I} (P:N7 deleted)
    (numerator :lz (nI (Fin 3) kB)) (denominator :nI (Fin 3) kB)
    (i:Fin P.N) :nI (Fin 3) kB :=
  numerator.eval (C (cy K kB (P.nodes i))) -
    denominator*(C (cy K kB (u 0 (P.index i))) +
      nX 1*C (cy K kB (u 1 (P.index i))))
structure TaylorChart (u:e9) {deleted:pC I} (P:N7 deleted)
   {Γ:pC K} (F:UJ u deleted Γ) (b:Bank) (Λ:pC K) where
 subset :Λ⊆Γ
 equation :nI (Fin 3) kB
 equation_ne :equation≠0
 equation_degree :equation.totalDegree≤b.E
 numerator :lz (nI (Fin 3) kB)
 af0:numerator.natDegree≤131071
 denominator :nI (Fin 3) kB
 cut_degree : ∀ i,(D4 u P numerator denominator i).totalDegree≤b.M
 point :K→Fin 3→kB
 slope : ∀ γ∈Λ,point γ 1=cy K kB γ
 on_equation : ∀ γ∈Λ,qx (point γ) equation=0
 regular : ∀ γ∈Λ,qx (point γ) denominator≠0
 reconstruction : ∀ γ (hγ:γ∈Λ),
   numerator.map (qx (point γ)) =
     mD (qx (point γ) denominator) *
       (F.mark γ (subset hγ)).decoder.map (cy K kB)
end
end wT
end
section
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace wT
noncomputable section
open MvPolynomial
private theorem aHJ {F E G:Type*} [lI F]
  [AddCommGroup E] [vi F E] [Ea F E]
  [AddCommGroup G] [vi F G] [Ea F G]
  (f :E →ₗ[F] G) (R:xm F E)
  (hdim:xu F G+Module.finrank F R<xu F E) :
  ∃ q:E,f q=0∧q∉R:= by
 by_contra hn
 have hle :FU f≤R:= by
  intro q hq
  by_contra hnot
  exact hn ⟨q,LinearMap.mem_ker.mp hq,hnot⟩
 have hk :=Submodule.finrank_mono hle
 have hf :=LinearMap.finrank_range_add_finrank_ker f
 have hr :=(Gr f).finrank_le
 omega
variable {F:Type*} [lI F]
structure a9S (N :ℕ) (L:nI (Fin 5) F) (b:Bank) where
 x :Fin N→F
 first:Fin N→F
 firstSlope :Fin N→F
 second:Fin N→F
 secondSlope :Fin N→F
 nonzero :L≠0
 degreeS:L.weightedTotalDegree (vO 1 2)≤b.dS
 degreeT:L.weightedTotalDegree (vO 1 3)≤b.dT
 order_one : ∀ i,(RK oH
   (Ko (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree=1
variable {N :ℕ} {L:nI (Fin 5) F} {b:Bank} {H :ℕ} (D:a9S N L b)
end
end wT
end
section
namespace aiG
noncomputable section
open Polynomial Matrix gR
abbrev aZ (F:Type) [lI F] :=nI (Fin 2) F
abbrev CS (F:Type) [lI F] :=vZ (aZ F)
def graph {F:Type} [lI F] (p:ℕ) :aZ F →ₐ[F] F[X] :=
 uz ![aU,aU ^p]
def aG8 {A ι:Type} [Kl A] (v :ι→A) :Prop :=
 ∀ q:A,(∀ i,q∣v i)→ IsUnit q
def Gz {F:Type} [lI F] {h:ℕ}
    (Q:Fin 2×Fin (h+1)→aZ F) (b:Fin 2) : (aZ F)[X] :=
  Il (fun j=>Q (b,j))
def Kn {F:Type} [lI F] {h:ℕ}
    (Q:Fin 2×Fin (h+1)→aZ F) (b i:Fin 2) :ℕ :=
  Finset.univ.sup (fun j:Fin (h+1)=>(Q (b,j)).degreeOf i)
def aI1 {F ι:Type} [lI F] [p5 ι] [wA ι]
    (p:ℕ) (x u v :ι→F) (b:Fin 2) (j:ℕ) :aZ F :=
  if b=0 then
    nq (oX x u j)+MvPolynomial.X b*nq (oX x v j)
  else
    nq (oX x u j^p)+MvPolynomial.X b*nq (oX x v j^p)
def aPj {F ι:Type} [lI F] [p5 ι] [wA ι]
    (p:ℕ) (x u v :ι→F) (m h:ℕ) :
    sS (Fin (m - h)) (Fin 2×Fin (h+1)) (aZ F) :=
  fun j b=>aI1 p x u v b.1 (b.2.val+j.val)
def aoI {F ι:Type} [lI F] [p5 ι] [wA ι]
    (p:ℕ) (x u v :ι→F) (L t:ℕ) :sS (Fin 2×Fin L) (Fin (t+1)) (aZ F) :=
  fun b j=>aI1 p x u v b.1 (b.2.val+j.val)
def acH :Fin 2→Fin 5 := ![3,4]
def ZL {F:Type} [lI F] : (aZ F)[X] →+* nI (Fin 5) F :=
 oy (uh acH).toRingHom (nX 0)
end
end aiG
end
section
set_option backward.isDefEq.respectTransparency false
namespace aiG
noncomputable section
open MvPolynomial Finset Polynomial
open gR
variable {F:Type} [lI F]
def QN (p:ℕ) (e :Fin 2 →₀ ℕ) :ℕ:=e 0+p*e 1
theorem bqK (p:ℕ) (hp:0<p) :
  Set.InjOn (QN p) {e :Fin 2 →₀ ℕ | e 0<p} := by
 intro e he f hf h
 have hm:=oz (fun n:ℕ=>n%p) h
 simp only [QN,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
 have hmul :p*e 1=p*f 1 := by unfold QN at h; omega
 have h1 :e 1=f 1 :=Nat.eq_of_mul_eq_mul_left hp hmul
 ext i
 fin_cases i <;> assumption
theorem ekw (p:ℕ) (e :Fin 2 →₀ ℕ) (a :F) :
  graph p (qz e a)=pz (QN p e) a := by
 rw [graph,Pf]
 simp [Rm,S1 ,QN,← pow_mul,← yQ,Fa]
theorem ekp (p:ℕ) (hp:0<p) (Q:nI (Fin 2) F)
   (hdegree :Q.degreeOf 0<p) (e :Fin 2 →₀ ℕ) (he :e∈Q.support) :
   (graph p Q).coeff (QN p e)=Q.coeff e := by
 classical
 have hex :graph p Q=∑ f∈Q.support,pz (QN p f) (Q.coeff f) := by
   conv_lhs=>rw [Q.as_sum]
   simp only [qG,ekw]
 rw [hex,wR]
 trans ((pz (QN p e) (Q.coeff e)).coeff (QN p e))
 · apply Ok e he
   intro f hf hfe
   rw [ze,z9]
   intro h
   apply hfe
   apply bqK p hp
   · exact (G9 0 hf).trans_lt hdegree
   · exact (G9 0 he).trans_lt hdegree
   · exact h
 · simp
theorem b5H (p:ℕ) (hp:0<p) (Q:nI (Fin 2) F)
  (hQ:Q≠0) (hdegree :Q.degreeOf 0<p) :graph p Q≠0:= by
 obtain ⟨e,he⟩:=support_nonempty.mpr hQ
 intro hz
 have hh:=ekp p hp Q hdegree e he
 rw [hz,v8] at hh
 exact (mem_support_iff.mp he) hh.symm
section Rank
open Matrix
variable {r H J:ℕ}
private theorem cNG {ι κ E :Type} [p5 ι] [p5 κ] [lI E]
    (A:sS ι κ E) :
    ∃ (rows :Fin A.rank→ι) (cols :Fin A.rank→κ),(A.submatrix rows cols).det≠0:= by
  classical
  obtain ⟨B⟩:=zQ.a3O
    (sI (0:E)) (A.map mD) A.rank (by
      have heq : (A.map mD).map (sI (0:E))=A:= by
        ext i j
        simp
      rw [heq])
  refine ⟨B.rows,B.cols,?_⟩
  intro h
  apply B.minor_ne
  change ((A.submatrix B.rows B.cols).map mD).det=0
  rw [← Vs ,← RingHom.map_det,h,ox]
private theorem eAx {υ:Type} [p5 υ] [wA υ]
  (i:Fin 2) (A:sS υ υ (aZ F)) (d:υ→ℕ)
  (hd : ∀ j k,(A j k).degreeOf i≤d k) :
  A.det.degreeOf i ≤ ∑ k,d k := by
 classical
 rw [Matrix.det_apply']
 apply (degreeOf_sum_le _ _ _).trans
 apply IT
 intro σ _
 have hc: ((↑↑(Equiv.Perm.sign σ) :aZ F)).degreeOf i=0:= by
  rw [← map_intCast (nq:F →+* aZ F),degreeOf_C]
 apply (degreeOf_mul_le _ _ _).trans
 rw [hc,v9]
 exact (degreeOf_prod_le _ _ _).trans (Ts (fun k _=>hd (σ k) k))
private theorem ekv (p:ℕ) (hp:0<p) (hH :H<p)
   (A:sS (Fin J) (Fin 2×Fin H) (aZ F))
   (hd : ∀ j k,(A j k).degreeOf 0≤ if k.1=0 then 1 else 0)
   (rows :Fin r→Fin J) (cols :Fin r→Fin 2×Fin H)
   (hminor : (A.submatrix rows cols).det≠0) :
   graph p (A.submatrix rows cols).det≠0:= by
 classical
 have hinj:uW cols := by
   intro j k hjk
   by_contra hne
   exact hminor (Matrix.det_zero_of_column_eq hne (by
     intro l
     change A (rows l) (cols j)=A (rows l) (cols k)
     rw [hjk]))
 apply b5H p hp _ hminor
 apply (eAx 0 (A.submatrix rows cols) (fun k=>if (cols k).1=0 then 1 else 0)
   (fun j k=>hd (rows j) (cols k))).trans_lt
 apply lt_of_le_of_lt _ hH
 let S:pC (Fin r) :=Finset.univ.filter (fun k=>(cols k).1=0)
 have hsum: (∑ k,if (cols k).1=0 then 1 else 0)=S.card:= by
   simp [S,Finset.sum_boole]
 rw [hsum]
 have hle :S.card≤Cy (Fin H) := by
   rw [← Pv]
   refine Fintype.card_le_of_injective (fun k :S=>(cols k.val).2) ?_
   intro j k hjk
   apply C4
   apply hinj
   have hj: (cols j.val).1=0:=(Finset.mem_filter.mp j.property).2
   have hk : (cols k.val).1=0:=(Finset.mem_filter.mp k.property).2
   exact Prod.ext (hj.trans hk.symm) hjk
 simpa only [yJ] using hle
theorem ceq (q:ℕ) (hq:0<q) (hH :H<q)
    (A:sS (Fin J) (Fin 2×Fin H) (aZ F))
    (hd : ∀ j k,(A j k).degreeOf 0≤ if k.1=0 then 1 else 0) :
    (A.map (cy (aZ F) (CS F))).rank =
      (A.map ((cy F[X] (t3 F)).comp
        (graph q).toRingHom)).rank := by
  let f :=cy (aZ F) (CS F)
  let g:=(cy F[X] (t3 F)).comp
    (graph (F:=F) q).toRingHom
  have hdet {E :Type} [lI E] (φ:aZ F →+* E) {s :ℕ} (rows :Fin s→Fin J) (cols :Fin s→Fin 2×Fin H) :
      ((A.map φ).submatrix rows cols).det=φ (A.submatrix rows cols).det:= by
    have he :=φ.map_det (A.submatrix rows cols)
    rw [Vs] at he
    exact he.symm
  change (A.map f).rank=(A.map g).rank
  apply le_antisymm
  · obtain ⟨rows,cols,hn⟩:=cNG (A.map f)
    rw [hdet f] at hn
    have hn' : (A.submatrix rows cols).det≠0:= fun h=>hn (by rw [h,ox])
    have hg: ((A.map g).submatrix rows cols).det≠0:= by
      rw [hdet g]
      change cy F[X] (t3 F) (graph q _)≠0
      rw [← ox (cy F[X] (t3 F))]
      exact (qM F[X] _).ne
        (ekv q hq hH A hd rows cols hn')
    have h:=RC (A.map g) rows cols
    rwa [Mk hg,yJ] at h
  · obtain ⟨rows,cols,hn⟩:=cNG (A.map g)
    rw [hdet g] at hn
    have hn' : (A.submatrix rows cols).det≠0:= fun h=>hn (by rw [h,ox])
    have hf : ((A.map f).submatrix rows cols).det≠0:= by
      rw [hdet f]
      rw [← ox f]
      exact (qM (aZ F) _).ne hn'
    have h:=RC (A.map f) rows cols
    rwa [Mk hf,yJ] at h
end Rank
end
end aiG
end
section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace wT
noncomputable section
open K1 MvPolynomial
variable {u:e9} {deleted:pC I} {P:N7 deleted} {b:Bank} {H :ℕ}
 (D:asP u P b H)
def asP.ic (_D:asP u P b H) (i:Fin P.N) (Q:nI (Fin 5) K) :=
  Ko (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
    (u 0 (P.index i)^p) (u 1 (P.index i)^p) Q
def a2W (u:e9) {deleted:pC I} (P:N7 deleted)
    (Q Q' : lz K) (s t:K) (S:pC (Fin P.N)) :Prop :=
  ∀ i∈S,Q.eval (P.nodes i)=u 0 (P.index i)+s*u 1 (P.index i) ∧
    Q'.eval (P.nodes i)=u 0 (P.index i)^p+t*u 1 (P.index i)^p
theorem aV4 :uW P.nodes :=
 ProximityPrize.Benchmark.IRSProfile.domain.injective.comp P.index.injective
end
end wT
end
section
set_option backward.isDefEq.respectTransparency false
namespace aiG
noncomputable section
open Polynomial Matrix gR
open scoped BigOperators nonZeroDivisors
theorem b9w {A B ι κ:Type} [oD A] [oD B] [p5 κ]
  (f :A →+* B) (M:sS ι κ A) (v :κ→A) :
  (M.map f).mulVec (fun j=>f (v j))=fun i=>f (M.mulVec v i) := by
 funext i
 simp only [Matrix.mulVec,dotProduct,KI,qG,lV]
private theorem eOp {A κ:Type} [oD A] [IsDomain A]
  [NormalizedGCDMonoid A] [p5 κ] (v :κ→A) (hv :v≠0) :
  ∃ (g:A) (Q:κ→A),g≠0∧v=g•Q∧aG8 Q:= by
 classical
 let g:=Finset.univ.gcd v
 have hdiv (i:κ) :g∣v i:=Finset.gcd_dvd (u9 i)
 have hg:g≠0:= by
  intro he
  apply hv
  funext i
  simpa only [he,MO,Et] using hdiv i
 choose Q hQ using hdiv
 refine ⟨g,Q,hg,funext hQ,fun q hq => ?_⟩
 have hd:g*q∣g:=Finset.dvd_gcd (fun i _=> by
  rw [hQ i,WY hg]
  exact hq i)
 apply isUnit_iff_dvd_one.mpr
 apply (WY hg).mp
 simpa only [FK] using hd
theorem c4f {F ι κ:Type} [lI F] [p5 κ]
   (M:sS ι κ (aZ F))
   (hn:0<xu (CS F)
     (FU (M.map (cy (aZ F) (CS F))).mulVecLin)) :
   ∃ Q:κ→aZ F,Q≠0∧M.mulVec Q=0∧aG8 Q:= by
 classical
 let N :=M.map (cy (aZ F) (CS F))
 obtain ⟨w,hw⟩:=Module.finrank_pos_iff_exists_ne_zero.mp hn
 let v :κ→CS F:=w.val
 have hv :v≠0:= fun he=>hw (C4 he)
 have hk :N.mulVec v=0:=w.property
 let D:=(aZ F)⁰
 let g:=IsLocalization.commonDenom D Iw v
 let W (i:κ) :aZ F:=IsLocalization.integerMultiple D Iw v ⟨i,u9 i⟩
 have hW (i:κ) :cy (aZ F) (CS F) (W i) =
     cy (aZ F) (CS F) (g:aZ F)*v i:= by
   have he :=IsLocalization.map_integerMultiple D Iw v ⟨i,u9 i⟩
   change _=(g:aZ F)•v i at he
   simpa only [yB] using he
 have hg:cy (aZ F) (CS F) (g:aZ F)≠0 :=
   fun hz=>(mem_nonZeroDivisors_iff_ne_zero.mp g.property)
     (qM (aZ F) (CS F) (hz.trans (ox _).symm))
 have hWne :W≠0:= by
   intro he
   apply hv
   funext i
   have hf :=hW i
   rw [he,Et,ox] at hf
   exact (mul_eq_zero.mp hf.symm).resolve_left hg
 have hWM:M.mulVec W=0:= by
   have h:=b9w (cy (aZ F) (CS F)) M W
   simp only [hW] at h
   change N.mulVec ((cy (aZ F) (CS F) (g:aZ F))•v)= _ at h
   rw [ XB,hk,smul_zero] at h
   funext i
   apply qM (aZ F) (CS F)
   rw [Et,ox]
   exact (yo h i).symm
 let:=UniqueFactorizationMonoid.strongNormalizationMonoid (α:=aZ F)
 let:=UniqueFactorizationMonoid.toNormalizedGCDMonoid (aZ F)
 obtain ⟨a,Q,ha,he,hp⟩:=eOp W hWne
 refine ⟨Q,?_,?_,hp⟩
 · intro hz
   rw [hz,smul_zero] at he
   exact hWne he
 · rw [he,XB] at hWM
   funext i
   exact (mul_eq_zero.mp (yo hWM i)).resolve_left ha
theorem dd5 {F ι:Type} [lI F] [p5 ι] [wA ι]
    (p:ℕ) (x u v :ι→F) (h L s t:ℕ) (hs :h+s=L)
    (Q:Fin 2×Fin (h+1)→aZ F)
    (hQ: (aPj p x u v (L+t) h).mulVec Q=0) :
    (zk (Gz Q) L s).transpose*aoI p x u v L t=0:= by
  classical
  apply OJ
  intro d j
  let e :Fin 2×Fin (h+1) ↪ Fin 2×Fin L :=
    ⟨fun z=>(z.1,⟨z.2.val+d.val,by have :=z.2.isLt; have :=d.isLt; omega⟩),
      fun a b hab=>Prod.ext (oz  (fun z :Fin 2×Fin L=>z.1) hab)
        (zm  (by
          have he :=oz  (fun z :Fin 2×Fin L=>z.2.val) hab
          exact Nat.add_right_cancel he))⟩
  let jd:Fin (L+t - h) :=⟨j.val+d.val,by have :=j.isLt; have :=d.isLt; omega⟩
  have hshift (z :Fin 2×Fin (h+1)) :
      (zk (Gz Q) L s) (e z) d= Q z := by
    change (Gz Q z.1*aU ^d.val).coeff (z.2.val+d.val)= Q z
    rw [coeff_mul_X_pow,Gz,LQ]
  have hzero (z :Fin 2×Fin L) (hz :z∉Kh e) :
      (zk (Gz Q) L s) z d=0:= by
    change (Gz Q z.1*aU ^d.val).coeff z.2.val=0
    by_cases hlo:z.2.val<d.val
    · rw [coeff_mul_X_pow',z9 (not_le.mpr hlo)]
    · have hhi:h<z.2.val - d.val := by
        by_contra! hh
        apply hz
        refine ⟨(z.1,⟨z.2.val - d.val,by omega⟩),Prod.ext rfl (zm ?_)⟩
        change z.2.val - d.val+d.val=z.2.val
        omega
      have he :z.2.val - d.val+d.val=z.2.val :=Nat.sub_add_cancel (by omega)
      rw [← he,coeff_mul_X_pow]
      exact MK ((Principal.aCg _).trans_lt hhi)
  change (∑ z,zk (Gz Q) L s z d*aoI p x u v L t z j)=0
  have hsum: (∑ z :Fin 2×Fin L,zk (Gz Q) L s z d*aoI p x u v L t z j) =
      ∑ z :Fin 2×Fin (h+1),zk (Gz Q) L s (e z) d *
        aoI p x u v L t (e z) j:= by
    let f (z :Fin 2×Fin L) :=zk (Gz Q) L s z d*aoI p x u v L t z j
    calc
      _ = ∑ z∈Finset.univ.map e,f z := by
        symm
        apply Un (WK _)
        intro z _ hz
        change zk (Gz Q) L s z d*aoI p x u v L t z j=0
        rw [hzero z (fun hm=>hz (by
          obtain ⟨w,rfl⟩:=hm
          exact Finset.mem_map.mpr ⟨w,u9 _,rfl⟩)),zero_mul]
      _ = _:=Finset.sum_map _ e f
  rw [hsum]
  have hk :=yo hQ jd
  change (∑ z,aPj p x u v (L+t) h jd z*Q z)=0 at hk
  rw [← hk]
  apply p7 rfl
  intro z _
  rw [hshift,t4]
  congr 1
  change aI1 p x u v z.1 (z.2.val+d.val+j.val) =
    aI1 p x u v z.1 (z.2.val+(j.val+d.val))
  congr 1
  omega
end
end aiG
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000
namespace aiG
noncomputable section
open Polynomial Matrix gR K1 ProximityPrize.Benchmark
open scoped BigOperators
private theorem cUj {F ι:Type} [lI F] [p5 ι] [wA ι]
  (q:ℕ) (x u v :ι→F) (b:Fin 2) (j:ℕ) :
  graph q (aI1 q x u v b j)=zR q x u v b j:= by
 fin_cases b <;> simp [graph,aI1,zR]
private theorem cr6 {F ι:Type} [lI F] [p5 ι] [wA ι]
    (q:ℕ) (x u v :ι→F) (b i:Fin 2) (j:ℕ) :
    (aI1 q x u v b j).degreeOf i≤ if b=i then 1 else 0:= by
  have h (a c:F) :
      (nq a+MvPolynomial.X b*nq c).degreeOf i ≤
        if b=i then 1 else 0:= by
    apply (MvPolynomial.degreeOf_add_le i _ _).trans
    apply max_le
    · simp
    · apply (MvPolynomial.degreeOf_mul_C_le _ _ _).trans
      rw [MvPolynomial.degreeOf_X]
      by_cases he :b=i
      · simp [he]
      · simp [he,Ne.symm he]
  unfold aI1
  by_cases hb:b=0
  · simpa only [hb,GR] using h (oX x u j) (oX x v j)
  · simpa only [hb,Gj] using h (oX x u j^q) (oX x v j^q)
private theorem b5J {F ι:Type} [lI F] [p5 ι] [wA ι]
    (q:ℕ) (x u v :ι→F) (m h:ℕ) :
    (aPj q x u v m h).map
        ((cy F[X] (t3 F)).comp (graph q).toRingHom) =
      (kL.af7 q x u v m h).map (cy F[X] (t3 F)) := by
  apply OJ
  intro j b
  change cy F[X] (t3 F)
      (graph q (aI1 q x u v b.1 (b.2.val+j.val))) =
    cy F[X] (t3 F)
      (zR q x u v b.1 (b.2.val+j.val))
  rw [cUj]
private theorem cUi {F ι:Type} [lI F] [p5 ι] [wA ι]
    (q:ℕ) (x u v :ι→F) (L t:ℕ) :
    (aoI q x u v L t).map
        ((cy F[X] (t3 F)).comp (graph q).toRingHom) =
      (AI q x u v L t).map (cy F[X] (t3 F)) := by
  apply OJ
  intro b j
  change cy F[X] (t3 F)
      (graph q (aI1 q x u v b.1 (b.2.val+j.val))) =
    cy F[X] (t3 F)
      (zR q x u v b.1 (b.2.val+j.val))
  rw [cUj]
private theorem aOK {F E ι:Type} [lI F] [lI E]
  [p5 ι] [wA ι] (f :F →+* E)
  (x w:ι→F) (j:ℕ) :
  f (oX x w j)=oX (fun i=>f (x i)) (fun i=>f (w i)) j:= by
 simp only [oX,weight,qG,lV,pG,map_inv₀,map_prod,Fz]
private theorem cEJ {F ι:Type} [lI F] [p5 ι] [wA ι]
    (q:ℕ) [ExpChar F q] (x u v :ι→F) (hx :uW x)
    (hfix : ∀ i,x i^q=x i) (k m h:ℕ)
    (hkm:k+m=Cy ι)
    (R:kL.axT q x u v k h) :
    ((kL.af7 q x u v m h).map
      (cy F[X] (t3 F))).mulVec
      (fun j=>cy F[X] (t3 F) (R.coefficients j))=0:= by
  classical
  let E :=t3 F
  let φ:=cy F[X] E
  let f :=φ.comp mD
  let y := fun i=>f (x i)
  let z :=φ aU
  let w:Fin 2→ι→E := fun b i =>
    if b=0 then f (u i)+z*f (v i)
    else f (u i^q)+z^q*f (v i^q)
  let P (b:Fin 2) :E[X] :=(Il (fun j=>R.coefficients (b,j))).map φ
  have hmoment (b:Fin 2) (j:ℕ) :
      φ (zR q x u v b j)=oX y (w b) j:= by
    by_cases hb:b=0
    · simp only [zR,hb,GR,ov,lV]
      change f (oX x u j)+z*f (oX x v j)= _
      rw [aOK,aOK]
      simpa only [w,hb,GR,wY] using
        (Nr y (fun i=>f (u i)) (fun i=>f (v i)) 1 z j).symm
    · simp only [zR,hb,Gj,ov,lV]
      rw [φ.map_pow aU]
      change f (oX x u j^q)+z^q*f (oX x v j^q)= _
      rw [← bxn q x hfix,← bxn q x hfix,
        aOK,aOK]
      simpa only [w,hb,Gj,wY] using
        (Nr y (fun i=>f (u i^q)) (fun i=>f (v i^q)) 1 (z^q) j).symm
  have hnodes (i:ι) :
      (P 0).eval (y i)*w 0 i+(P 1).eval (y i)*w 1 i =
        (R.output.map φ).eval (y i) := by
    have he :=oz φ (R.nodes i)
    simpa only [P,y,f,oq,z,w,G0 ,one_ne_zero,
      GR,Gj,ov,lV,pG,eval_map_apply] using he
  have hP (b:Fin 2) : (P b).natDegree≤h:=natDegree_map_le.trans (R.x_degree b)
  rw [kL.c3y]
  apply (kL.c76 _ m h _).mpr
  intro j
  have hcoeff (b:Fin 2) (l:Fin (h+1)) :
      φ (R.coefficients (b,l))=(P b).coeff l.val := by
    change φ (R.coefficients (b,l)) =
      ((Il (fun j=>R.coefficients (b,j))).map φ).coeff l.val
    rw [t9,LQ]
  change (∑ b:Fin 2,∑ l:Fin (h+1),
    φ (R.coefficients (b,l))*φ (zR q x u v b (l.val+j.val)))=0
  simp only [FQ,hmoment,hcoeff]
  change (∑ l:Fin (h+1),(P 0).coeff l.val*oX y (w 0) (l.val+j.val)) +
    (∑ l:Fin (h+1),(P 1).coeff l.val*oX y (w 1) (l.val+j.val))=0
  rw [← kL.bhJ y (w 0) _ _ _ (hP 0),
    ← kL.bhJ y (w 1) _ _ _ (hP 1)]
  have hlin:=Nr y
    (fun i=>(P 0).eval (y i)*w 0 i) (fun i=>(P 1).eval (y i)*w 1 i) 1 1 j.val
  simp only [wY] at hlin
  rw [← hlin]
  simp_rw [hnodes]
  exact kL.cr7 y (f.injective.comp hx) _ (k+h) j.val
    (degree_map_le.trans_lt R.output_degree) (by have :=j.isLt; omega)
end
end aiG
end
section
set_option backward.isDefEq.respectTransparency false
namespace wT
noncomputable section
open K1 gR
def c1h (deleted:pC I) :N7 deleted:= by
  classical
  let Bp:=Iw \ deleted
  let idx :=Bp.equivFin.symm
  refine ⟨Bp.card,idx.toEmbedding.trans (Function.Embedding.subtype _),?_,?_⟩
  · intro i
    constructor
    · rintro ⟨j,rfl⟩
      exact (Finset.mem_sdiff.mp (idx j).property).2
    · intro hi
      let old:Bp:=⟨i,Finset.mem_sdiff.mpr ⟨u9 _,hi⟩⟩
      exact ⟨idx.symm old,oz Subtype.val (idx.apply_symm_apply old)⟩
  · simpa only [Bp,Finset.card_univ,ProximityPrize.Benchmark.IRSProfile.card_index] using
      Finset.card_sdiff_add_card_eq_card (WK deleted)
def arB {deleted:pC I} (P:N7 deleted) (S:pC I) :pC (Fin P.N) :=
 Finset.univ.filter fun i=>P.index i∈S
theorem aVT {deleted:pC I} (P:N7 deleted) (S:pC I)
 (i:Fin P.N) :i∈arB P S↔P.index i∈S:= by simp [arB]
theorem beB {deleted:pC I} (P:N7 deleted) (S:pC I)
  (hS : ∀ i∈S,i∉deleted) : (arB P S).card=S.card:= by
 have heq : (arB P S).map P.index=S:= by
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩:=Finset.mem_map.mp hi
    exact (aVT P S j).mp hj
  · intro hi
    obtain ⟨j,hj⟩:=(P.Z1 i).mpr (hS i hi)
    refine Finset.mem_map.mpr ⟨j,(aVT P S j).mpr ?_,hj⟩
    rwa [hj]
 calc
  (arB P S).card=((arB P S).map P.index).card:=(Finset.card_map _).symm
  _=S.card:=oz Finset.card heq
end
end wT
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Qo
noncomputable section
open K1 wT MvPolynomial
def yV {F:Type*} [lI F] (Q:nI (Fin 5) F) :Prop :=
 Q.degreeOf 1=0∧Q.degreeOf 2=0
def graph {F:Type*} [lI F] (q:ℕ) :
    nI (Fin 5) F →ₐ[F] lz (lz F) :=
  uz ![aU,0,0,mD aU,(mD aU)^q]
def aDV {F:Type*} [lI F] (x a b c d:F) :Fin 5→nI (Fin 5) F :=
  ![nq x,nq a+MvPolynomial.X 3*nq b,
    nq c+MvPolynomial.X 4*nq d,nX 3,nX 4]
def aa2 {F:Type*} [lI F] (x a b c d:F) :
    nI (Fin 5) F →ₐ[F] nI (Fin 5) F :=
  uz (aDV x a b c d)
def YF {F:Type*} [lI F] (U V:nI (Fin 5) F) :ℕ :=
 max (1+U.degreeOf 3) (V.degreeOf 3)
def aab {F:Type*} [lI F] (U V:nI (Fin 5) F) :ℕ :=
 max (U.degreeOf 4) (1+V.degreeOf 4)
structure bTn (u:e9) {deleted:pC I} (P:N7 deleted)
   (H :ℕ) (U V:nI (Fin 5) K) where
 W:nI (Fin 5) K
 omits :yV W
 height:W.degreeOf 0≤131071+H
 degreeS:W.degreeOf 3≤YF U V
 degreeT:W.degreeOf 4≤aab U V
 node : ∀ i:Fin P.N,
   aa2 (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
     (u 0 (P.index i)^p) (u 1 (P.index i)^p) (U*nX 1+V*nX 2 - W)=0
end
end Qo
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Qo
noncomputable section
open wT MvPolynomial
variable {F:Type*} [lI F]
def aHe :nI (Fin 5) F →ₐ[F] nI (Fin 5) F :=
 uz ![0,0,0,nX 3,nX 4]
theorem dPf (e :Fin 5 →₀ ℕ) (a :F) :
   aHe (qz e a)=if e.weight oH<1 then qz e a else 0:= by
 classical
 rw [aHe,Pf]
 by_cases h0:e 0=0 <;> by_cases h1 :e 1=0 <;> by_cases h2 :e 2=0 <;>
   simp [Rm,S1 ,oH,aQ8,
     h0,h1,h2,monomial_eq]
theorem gED (e :Fin 5 →₀ ℕ) (a :F) :
   weightedTruncation oH 1 (qz e a)=
     if e.weight oH<1 then qz e a else 0:= by
 classical
 ext f
 by_cases hfe :e=f
 · subst f
   split_ifs <;> simp_all [NZ,Qw]
 · split_ifs <;> simp_all [NZ,Qw]
theorem cH1 (P:nI (Fin 5) F) :
   aHe P=weightedTruncation oH 1 P:= by
 induction P using MvPolynomial.induction_on' with
 | monomial e a=>rw [dPf,gED]
 | add P Q hp hq=>simp only [map_add,hp,hq]
theorem cNo (P:nI (Fin 5) F) (i:Fin 5)
  (hi:oH i=1) (hvalue :aHe P=0)
  (hgradient:aHe (qU i P)≠0) :
  (RK oH P).natTrailingDegree=1 := by
 have hzero :P∈restrictWeightedOrder oH 1 := by
  apply (weightedTruncation_eq_zero_iff _ _ _).mp
  rwa [← cH1]
 obtain ⟨e,he⟩:=support_nonempty.mpr hgradient
 have hec:=mem_support_iff.mp he
 rw [cH1,NZ] at hec
 have heweight:e.weight oH<1 := by
  by_contra hn
  exact hec (z9 hn)
 rw [HZ heweight,coeff_pderiv] at hec
 have hcoeff :P.coeff (e+Finsupp.single i 1)≠0:=Re hec
 have hweight: (e+Finsupp.single i 1).weight oH=1 := by
  rw [ov,Finsupp.weight_single,one_smul,hi]
  omega
 exact dPq oH P hzero _ hweight hcoeff
theorem aPg (i:Fin 5) (P:nI (Fin 5) F)
  (hP:P.degreeOf i=0) :qU i P=0:= by
 ext e
 rw [coeff_pderiv]
 have hc:P.coeff (e+Finsupp.single i 1)=0:= by
  apply notMem_support_iff.mp
  apply notMem_support_of_degreeOf_lt i
  simp [hP]
 simp [hc]
theorem ew6 (U V R:nI (Fin 5) F)
  (hU:yV U) (hV:yV V) (hR:yV R) :
  qU 1 (U*nX 1+V*nX 2-R)=U∧qU 2 (U*nX 1+V*nX 2-R)=V:= by
 constructor <;> simp [aPg _ U hU.1,
  aPg _ U hU.2,aPg _ V hV.1,
  aPg _ V hV.2,aPg _ R hR.1,
  aPg _ R hR.2]
theorem cH2 (x a b c d:F) (P:nI (Fin 5) F)
   (i:Fin 5) (hi:i=1∨i=2) :
   qU i (Ko x a b c d P)=Ko x a b c d (qU i P) := by
 have hvar (j:Fin 5) :qU i (Ko x a b c d (nX j))=
     Ko x a b c d (qU i (nX j)) := by
   rcases hi with rfl | rfl
   all_goals fin_cases j <;> simp [Ko,bhe]
 induction P using MvPolynomial.induction_on with
 | C r=>simp [Ko]
 | add P Q hp hq=>simp only [map_add,hp,hq]
 | mul_X P j hp=>simp only [map_mul,pderiv_mul,map_add,hp,hvar]
theorem cYl (x a b c d:F)
   (U V R:nI (Fin 5) F)
   (hU:yV U) (hV:yV V) (hR:yV R)
   (hnode :aHe (Ko x a b c d (U*nX 1+V*nX 2-R))=0)
   (hnonzero :aHe (Ko x a b c d U)≠0 ∨
     aHe (Ko x a b c d V)≠0) :
   (RK oH (Ko x a b c d (U*nX 1+V*nX 2-R))).natTrailingDegree=1 := by
 have hd:=ew6 U V R hU hV hR
 rcases hnonzero with hu | hv
 · apply cNo _ 1 (by decide) hnode
   rw [cH2 x a b c d _ 1 (Or.inl rfl),hd.1]
   exact hu
 · apply cNo _ 2 (by decide) hnode
   rw [cH2 x a b c d _ 2 (Or.inr rfl),hd.2]
   exact hv
def bsE (P:nI (Fin 5) F) (a b:ℕ) :Prop :=
 ∀ e∈P.support,e 1=a∧e 2=b
theorem bfT (P:nI (Fin 5) F) (hP:yV P) :bsE P 0 0:= by
 rcases hP with ⟨hP1,hP2⟩
 intro e he
 have h1 :=G9 1 he
 have h2 :=G9 2 he
 exact ⟨by omega,by omega⟩
theorem fV7 {R:Type*} [oD R] [IsDomain R]
  (U V:lz R) (hUV:Gk U V) (x :R) :U.eval x≠0∨V.eval x≠0:= by
 by_contra hn
 push Not at hn
 have hu:aU-Polynomial.C x∣U:=Polynomial.dvd_iff_isRoot.mpr hn.1
 have hv :aU-Polynomial.C x∣V:=Polynomial.dvd_iff_isRoot.mpr hn.2
 exact Polynomial.not_isUnit_X_sub_C x (hUV hu hv)
def a6s (x :F) :nI (Fin 5) F →ₐ[F] nI (Fin 5) F :=
 uz ![C x,nX 1,nX 2,nX 3,nX 4]
theorem bDh (x a b c d:F) (P:nI (Fin 5) F) :
   aHe (Ko x a b c d P)=aa2 x a b c d P:= by
 rw [Ko,aeval_eq_bind₁,aHe,aeval_bind₁]
 have hf : (fun i=>uz ![0,0,0,nX 3,nX 4] (bhe x a b c d i))=
     aDV x a b c d:= by
   funext i
   fin_cases i <;> simp [bhe,aDV]
 rw [hf]
 rfl
theorem c1B (x a b c d:F) (P:nI (Fin 5) F)
  (hP:yV P) :aa2 x a b c d P=a6s x P:= by
 change eval₂ C (aDV x a b c d) P=eval₂ C ![C x,nX 1,nX 2,nX 3,nX 4] P
 apply eval₂_congr
 intro i e hi hc
 have he :e∈P.support :=mem_support_iff.mpr hc
 have ht:=bfT P hP e he
 have hin:e i≠0:=Finsupp.mem_support_iff.mp hi
 have h1 :i≠1 := by intro hi1; subst i; exact hin ht.1
 have h2 :i≠2 := by intro hi2; subst i; exact hin ht.2
 fin_cases i <;> simp [aDV] at *
theorem c3I (x :F) (P:nI (Fin 5) F) :
    a6s x P=uh G1 ((th F 4 P).eval (C x)) := by
  have heq : (a6s x).toRingHom=
      (uh (G1 :Fin 4→Fin 5)).toRingHom.comp ((sI (C x)).comp (th F 4).toRingHom) := by
    apply Av
    · intro a
      simp [a6s,finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [a6s,finSuccEquiv_X_zero]
      · change a6s x (nX j.succ) =
          uh G1 ((th F 4 (nX j.succ)).eval (C x))
        rw [finSuccEquiv_X_succ,Ee,rename_X]
        fin_cases j <;> simp [a6s]
  exact zd heq P
theorem fV8 (U V:nI (Fin 5) F)
  (hUV:Gk U V) :Gk (th F 4 U) (th F 4 V) := by
 intro d hdU hdV
 have hu: (th F 4).symm d∣U:= by
  obtain ⟨q,hq⟩:=hdU
  refine ⟨(th F 4).symm q,?_⟩
  apply (th F 4).injective
  simpa only [lV,LR] using hq
 have hv : (th F 4).symm d∣V:= by
  obtain ⟨q,hq⟩:=hdV
  refine ⟨(th F 4).symm q,?_⟩
  apply (th F 4).injective
  simpa only [lV,LR] using hq
 have hu' := (hUV hu hv).map (th F 4).toRingHom
 change IsUnit ((th F 4) ((th F 4).symm d)) at hu'
 simpa only [LR] using hu'
theorem fV6 (x a b c d:F)
   (U V:nI (Fin 5) F) (hUV:Gk U V)
   (hU:yV U) (hV:yV V) :
   aa2 x a b c d U≠0∨aa2 x a b c d V≠0:= by
 have hn:=fV7 (th F 4 U) (th F 4 V)
   (fV8 U V hUV) (C x)
 rw [c1B x a b c d U hU,
   c1B x a b c d V hV,c3I,c3I]
 have hinj:uW (uh (R:=F) (G1 :Fin 4→Fin 5)) :=
   rename_injective _ (Fin.succ_injective 4)
 rcases hn with hu | hv
 · left
   exact fun hz=>hu (hinj (hz.trans (ox _).symm))
 · right
   exact fun hz=>hv (hinj (hz.trans (ox _).symm))
theorem b7W (x a b c d:F)
   (U V R:nI (Fin 5) F) (hUV:Gk U V)
   (hU:yV U) (hV:yV V) (hR:yV R)
   (hnode :aa2 x a b c d (U*nX 1+V*nX 2-R)=0) :
   (RK oH (Ko x a b c d (U*nX 1+V*nX 2-R))).natTrailingDegree=1 := by
 apply cYl x a b c d U V R hU hV hR
 · rwa [bDh]
 · simpa only [bDh] using fV6 x a b c d U V hUV hU hV
end
end Qo
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace wT
noncomputable section
open K1 gR MvPolynomial
open scoped BigOperators
variable {u:e9} {deleted:pC I} {P:N7 deleted}
 {Γ Λ:pC K} {F:UJ u deleted Γ} {b:Bank}
private theorem ddh {F:Type*} [lI F] {s t a b c d:F}
   (hs :a+s*b=c+s*d) (ht:a+t*b=c+t*d)
   (hm:a≠c∨b≠d) :s=t:= by
 have hz : (s - t)*(b - d)=0:= by linear_combination hs - ht
 rcases mul_eq_zero.mp hz with h | h
 · exact sub_eq_zero.mp h
 · have hb:=sub_eq_zero.mp h
   exact False.elim (hm.elim
     (fun hne=>hne (by simpa only [hb,add_left_inj] using hs))
     (fun hne=>hne hb))
variable (bY:TaylorChart u P F b Λ)
end
end wT
end
section
set_option backward.isDefEq.respectTransparency false
namespace aiG
noncomputable section
open Polynomial gR
open scoped BigOperators
variable {F:Type} [lI F]
theorem bD0 {h:ℕ} (Q:Fin 2×Fin (h+1)→aZ F)
  (b i:Fin 2) (j:Fin (h+1)) : (Q (b,j)).degreeOf i≤Kn Q b i :=
 Finset.le_sup (f := fun j:Fin (h+1)=>(Q (b,j)).degreeOf i) (u9 j)
theorem goq:uW acH := by
 intro i j h
 fin_cases i <;> fin_cases j <;> first | rfl | contradiction
private theorem c8h (a :aZ F) (i:Fin 5) (hi:i∉Kh acH) :
  (uh acH a).degreeOf i=0:= by
 by_contra h
 obtain ⟨j,_,hej⟩:=MvPolynomial.mem_vars_rename acH a
  (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h)
 exact hi ⟨j,hej⟩
private theorem b6o {h:ℕ} (Q:Fin 2×Fin (h+1)→aZ F)
  (b:Fin 2) (i:Fin 5) (a d:ℕ)
  (ha : ∀ j:Fin (h+1),(uh acH (Q (b,j))).degreeOf i≤a)
  (hd : ∀ j:Fin (h+1),((nX (0:Fin 5) :nI (Fin 5) F)^j.val).degreeOf i≤d) :
  (ZL (Gz Q b)).degreeOf i≤a+d:= by
 classical
 simp only [Gz,Il,qG,ZL,zh,
  LO,AlgHom.toRingHom_eq_coe]
 apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
 exact IT fun j _=>(MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add (ha j) (hd j))
theorem b6p {h:ℕ} (Q:Fin 2×Fin (h+1)→aZ F) (b:Fin 2) :
  (ZL (Gz Q b)).degreeOf 0≤h:= by
 simpa only [v9] using b6o Q b 0 0 h
  (fun j=>(c8h (Q (b,j)) 0 (by
    rintro ⟨i,hi⟩
    fin_cases i <;> contradiction)).le)
  (fun j=> by rw [MvPolynomial.degreeOf_X_self_pow]; omega)
theorem cVx {h:ℕ} (Q:Fin 2×Fin (h+1)→aZ F)
  (b i:Fin 2) :
  (ZL (Gz Q b)).degreeOf (acH i)≤Kn Q b i:= by
 simpa only [u5] using b6o Q b (acH i) (Kn Q b i) 0
  (fun j=> by rw [MvPolynomial.degreeOf_rename_of_injective goq]; exact bD0 Q b i j)
  (fun j=>(Wl _ (by fin_cases i <;> decide)).le)
theorem brc {h:ℕ} (Q:Fin 2×Fin (h+1)→aZ F) (b:Fin 2)
  (i:Fin 5) (hi:i=1∨i=2) :
  (ZL (Gz Q b)).degreeOf i=0:= by
 apply Nat.eq_zero_of_le_zero
 simpa only [v9] using b6o Q b i 0 0
  (fun j=>(c8h (Q (b,j)) i (by
    rintro ⟨l,rfl⟩
    fin_cases l <;> rcases hi with he | he <;> contradiction)).le)
  (fun j=>(Wl _ (by rcases hi with rfl | rfl <;> decide)).le)
private def aNW:nI (Fin 5) F →ₐ[F] (aZ F)[X] :=
 uz ![aU,0,0,mD (nX 0),mD (nX 1)]
private theorem cTg (a :aZ F) :
  aNW (uh acH a)=mD a := by
 have he : (aNW (F:=F)).toRingHom.comp (uh acH).toRingHom =
    Polynomial.C:= by
  apply Av
  · intro c
    simp [aNW]
  · intro i
    fin_cases i <;> simp [aNW,acH]
 exact zd he a
private theorem eep (A: (aZ F)[X]) :aNW (ZL A)=A:= by
 have he : (aNW (F:=F)).toRingHom.comp ZL=uJ _:= by
  apply p6
  · intro a
    change aNW (ZL (mD a))=mD a
    rw [ZL,zh,pL]
    exact cTg a
  · simp [aNW,ZL]
 exact zd he A
theorem cVw {h:ℕ} (Q:Fin 2×Fin (h+1)→aZ F)
  (hQ:aG8 Q) (a :aZ F)
  (hU:uh acH a∣ZL (Gz Q 0))
  (hV:uh acH a∣ZL (Gz Q 1)) :
  IsUnit a := by
 have hd (b:Fin 2) :mD a∣Gz Q b:= by
  have hb:uh acH a∣ZL (Gz Q b) := by
    fin_cases b
    · exact hU
    · exact hV
  have ht:=vk (aNW (F:=F)) hb
  simpa only [cTg,eep] using ht
 apply hQ
 rintro ⟨b,j⟩
 simpa only [Gz,LQ] using
  (SU _ _).mp (hd b) j.val
private def aVa (q:ℕ) :nI (Fin 5) F →ₐ[F] F[X][X] :=
 uz ![aU,0,0,mD (aU:F[X]),
  (mD (aU:F[X]))^q]
private theorem ekm (q:ℕ) (a :aZ F) :
  aVa q (uh acH a)=mD (graph q a) := by
 have he : (aVa (F:=F) q).toRingHom.comp (uh acH).toRingHom =
    Polynomial.C.comp (graph q).toRingHom:= by
  apply Av
  · intro c
    simp [aVa,graph]
  · intro i
    fin_cases i <;> simp [aVa,graph,acH]
 exact zd he a
theorem b5G (q:ℕ) (A: (aZ F)[X]) :
  uz ![aU,0,0,mD (aU:F[X]),
    (mD (aU:F[X]))^q] (ZL A) =
    A.map (graph q).toRingHom:= by
 change aVa q (ZL A)= _
 have he : (aVa (F:=F) q).toRingHom.comp ZL=oK (graph q).toRingHom:= by
  apply p6
  · intro a
    change aVa q (ZL (mD a))=(mD a).map (graph q).toRingHom
    rw [ZL,zh,pL,oZ]
    exact ekm q a
  · simp [aVa,ZL]
 exact zd he A
end
end aiG
end
section
namespace aiH
noncomputable section
open K1 wT MvPolynomial
def aNg {F:Type*} [oD F] (G:nI (Fin 4) F) (j:ℕ) :
    nI (Fin 4) F :=
  (fun H :nI (Fin 4) F=>qU 1 H)^[j] G
def bk6 {F:Type*} [lI F] (G:nI (Fin 4) F)
    (D:lz F) (s t:F) :Prop :=
  uz (D9 D s t) G=0 ∧
    uz (D9 D s t) (qU 1 G)≠0
def implicitDeriv {F:Type*} [oD F] (G H :nI (Fin 4) F) :
    nI (Fin 4) F :=
  qU 1 G*qU 0 H - qU 0 G*qU 1 H
def aN9 {F:Type*} [oD F] (G:nI (Fin 4) F) :
    ℕ→nI (Fin 4) F
  | 0 => -pderiv 0 G
  | n+1 =>
    qU 1 G*implicitDeriv G (aN9 G n) -
      C (↑(2*n+1) :F)*aN9 G n*implicitDeriv G (qU 1 G)
def aIS {F:Type*} [lI F] (G:nI (Fin 4) F)
    (w:ℕ) :ℕ→nI (Fin 4) F
  | 0=>MvPolynomial.X 1*pderiv 1 G^(2*w - 1)
  | n+1 =>
    C ((↑(Nat.factorial (n+1)) :F)⁻¹) *
      aN9 G n*qU 1 G^(2*w - 1-(2*n+1))
end
end aiH
end
