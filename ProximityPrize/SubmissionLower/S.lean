import ProximityPrize.SubmissionLower.BG
set_option Elab.async false
open _root_ renaming AddMonoidAlgebra.coeff_add→HZ,AddMonoidAlgebra.coeff_zero→RP,AlgEquiv.apply_symm_apply→Pj,Algebra.algebraMap→mD,CommRing→ oj,CommSemiring→Aa,DFunLike.congr_fun→ oy,DecidableEq→zd,Fin.prod_univ_three→Kz,Fin.sum_univ_succ→JM,Fin.sum_univ_three→qG,Fin.val→Eg,Finset→pG,Finset.induction_on→R9,Finset.mem_insert_of_mem→Pk,Finset.mem_insert_self→Qw,Finset.mem_range→Du,Finset.mem_univ→Lf,Finset.mul_sum→Ar,Finset.range→cy,Finset.range_mono→xL,Finset.sum_add_distrib→zk,Finset.sum_congr→n5,Finset.sum_eq_zero→xm,Finset.sum_insert→Ob,Finset.sum_le_sum→qM,Finset.sum_range_add→Df,Finset.sum_range_reflect→z9,Finset.sum_range_succ→t3,Finset.sum_range_zero→S2,Finset.sum_sub_distrib→wA,Finset.sum_subset→ze,Finset.sup_le→Mz,Finsupp.add_apply→wB,Finsupp.finite_of_nat_weight_le→Un,Finsupp.optionElim_some→LR,Finsupp.prod_fintype→Cy,Finsupp.single→p7,Finsupp.support_mono→Ts,Finsupp.weight→z7,Finsupp.weight_apply→JW,Finsupp.weight_eq_sum→Bf,Finsupp.weight_optionElim→GR,Finsupp.weight_single→Qx,Fintype→yL,Fintype.card→MO,Fintype.prod_option→Rm,Fintype.sum_option→NI
open _root_ renaming Function.Injective→vw,Ideal.mem_span_singleton→UY,Int.mul_ediv_cancel_of_dvd→FR,Int.natCast_ediv→Nq,Int.natCast_nonneg→Ea,Int.toNat_eq_max→J4,Int.toNat_le_toNat→Hw,Int.toNat_of_nonneg→G3,Int.toNat_of_nonpos→N0,Irreducible→FU,IsCoprime→qx,IsFractionRing.injective→vh,IsScalarTower.algebraMap_apply→yU,LinearIndependent→yo,LinearMap.finrank_range_add_finrank_ker→Ok,LinearMap.ker→uJ,LinearMap.map_add→Pv,LinearMap.mulLeft→Vl,LinearMap.pi→FV,LinearMap.range→qU,LinearMap.sum_apply→RD,Matrix.transpose_apply→SU,Module.Finite→uW,Module.Finite.of_injective→SD,Module.finrank→ oz,MulZeroClass.zero_mul→vZ,MvPolynomial→lV,MvPolynomial.C→c9,MvPolynomial.C_1→Dv,MvPolynomial.C_dvd_iff_dvd_coeff→Re,MvPolynomial.C_mem_restrictWeightedDegree→G9,MvPolynomial.C_mul_monomial→Sv,MvPolynomial.X→lz,MvPolynomial.X_mem_restrictWeightedOrder→ IT,MvPolynomial.X_pow_eq_monomial→TH,MvPolynomial.basisRestrictSupport→Au,MvPolynomial.bind₁→pC,MvPolynomial.bind₁_mem_restrictWeightedOrder→SW,MvPolynomial.coeff_C_mul→vi,MvPolynomial.coeff_X→UP,MvPolynomial.coeff_map→Gr,MvPolynomial.coeff_monomial→yl,MvPolynomial.coeff_smul→Pf,MvPolynomial.coeff_sum→EP,MvPolynomial.constantCoeff_eq→PD,MvPolynomial.degreeOf_eq_sup→RC,MvPolynomial.degreeOf_le_iff→P7,MvPolynomial.eval→pz
open _root_ renaming MvPolynomial.eval_C→Pc,MvPolynomial.eval₂→KI,MvPolynomial.eval₂Hom→pL,MvPolynomial.eval₂Hom_C→GF,MvPolynomial.eval₂Hom_X'→Fa,MvPolynomial.eval₂Hom_monomial→PA,MvPolynomial.isHomogeneous_X→Np,MvPolynomial.lcoeff→MK,MvPolynomial.le_weightedTotalDegree→vj,MvPolynomial.map→ oY,MvPolynomial.mapAlgHom→LQ,MvPolynomial.mem_support_iff→G8,MvPolynomial.monomial→ ov,MvPolynomial.monomial_le_degreeOf→Gj,MvPolynomial.mul_mem_restrictWeightedOrder→G2,MvPolynomial.natDegree_optionEquivLeft→SL,MvPolynomial.optionEquivLeft→xW,MvPolynomial.optionEquivLeft_C→zh,MvPolynomial.optionEquivLeft_X_none→LO,MvPolynomial.optionEquivLeft_X_some→Gn,MvPolynomial.optionEquivLeft_coeff_coeff→ IU,MvPolynomial.restrictWeightedDegree→yQ,MvPolynomial.restrictWeightedOrder→t9,MvPolynomial.ringHom_ext→pQ,MvPolynomial.support_add→Up,MvPolynomial.support_map_of_injective→TZ,MvPolynomial.weightedTotalDegree→zg,MvPolynomial.weightedTotalDegree_le_of_dvd→Gi,MvPolynomial.weightedTotalDegree_piSingle→uz,MvPolynomial.weightedTotalDegree_rename_of_injective→OJ,MvPolynomial.weightedTruncation→GY,MvPolynomial.weightedTruncation_eq_zero_iff→G7,Nat.add_le_add_left→NZ,Nat.add_le_add_right→Te,Nat.cast_add→yJ,Nat.cast_ofNat→LP,Nat.cast_one→ In,Nat.cast_sub→zE,Nat.cast_succ→Et,Nat.cast_sum→JQ,Nat.le_add_left→G5,Nat.le_of_lt_succ→Ef,Nat.mul_add→FK,Nat.mul_comm→yB,Nat.sub_le→ Iw,Nat.succ_mul→KH,Nat.zero_add→Ee,Nat.zero_le→C9
open _root_ renaming Or.inl→Dw,Pi.single→zR,Pi.zero_apply→Ml,Polynomial.C→lI,Polynomial.X→lJ,Polynomial.X_pow_dvd_iff→ II,Polynomial.coe_mapRingHom→Kp,Polynomial.coeff_eq_zero_of_natDegree_lt→Kv,Polynomial.coeff_map→FQ,Polynomial.coeff_zero→zc,Polynomial.evalRingHom→pU,Polynomial.eval₂RingHom→x7,Polynomial.eval₂_C→Pr,Polynomial.finsetSum_coeff→RJ,Polynomial.hasseDeriv→ oK,Polynomial.hasseDeriv_C→PM,Polynomial.hasseDeriv_zero→JK,Polynomial.lcoeff→F9,Polynomial.mapAlgHom→NX,Polynomial.mapRingHom→sS,Polynomial.natDegree_C_mul_le→KA,Polynomial.natDegree_le_of_dvd→SM,Polynomial.natDegree_map_eq_of_injective→Nr,Polynomial.natDegree_mul_C_le→SC,Polynomial.natDegree_smul_le→QL,Polynomial.ringHom_ext→C4,Polynomial.taylor→zi,Polynomial.taylorAlgHom→UZ,Polynomial.taylor_C→Kl,Polynomial.taylor_X→NW,PowerSeries→G6,PowerSeries.C→u5,PowerSeries.coeff_zero_eq_constantCoeff_apply→Qy,PowerSeries.constantCoeff→Mk,PowerSeries.rescale→EK,RingHom.comp_apply→qm,RingHom.congr_fun→Gk,RingHom.id→vG,Rj.indexWeight→th,Rj.offset→aU,Submodule→u8,Submodule.add_mem→Sd,Submodule.finrank_mono→Kc,Submodule.map_comap_subtype→Oc,Submodule.mem_inf→TI,Submodule.sum_mem→Nj,Submodule.zero_mem→ Il,aR.Shape→nI
open _root_ renaming aR.embed→qz,add_assoc→vk,add_comm→wY,add_le_add→Mj,add_zero→Av,aw9.admissible→t6,aw9.columns→nX,aw9.total→ oD,congrArg→nq,congrFun→GB,dvd_mul_of_dvd_left→Vz,dvd_mul_of_dvd_right→VC,dvd_mul_right→VH,eq_neg_of_add_eq_zero_right→S1,gR.Principal.aAt→Mw,ite_eq_left→t8,ite_eq_right→p5,ite_false→t5,ite_true→t4,jA.Lower→p6,jA.translate→ ox,le_max_left→C5,le_max_right→u9,le_rfl→uh,map_add→qy,map_mul→ oq,map_ne_zero_iff→Fz,map_pow→xI,map_sub→zS,map_sum→p9,map_zero→xu,max_eq_left→zf,max_eq_right→ oZ,max_le→vH,min_eq_left→zm,min_eq_right→vl,min_le_left→G0,min_le_right→Vq,mul_add→t7,mul_assoc→z8,mul_comm→v9,mul_le_mul_of_nonneg_left→Vs,mul_nonneg→v8,not_le_of_gt→G4,one_mul→sH,pow_ne_zero→MS,pow_succ→Dz,pow_zero→y5
open _root_ renaming smul_eq_mul→sI,sub_eq_add_neg→Kh,sub_le_sub_left→G1,sub_zero→wR,tsub_add_cancel_of_le→NY,zero_add→qJ
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Mc
open K1 Polynomial Matrix
open gR ProximityPrize.Benchmark
private theorem aOK {F E ι:Type} [Field F] [Field E]
  [yL ι] [zd ι] (f :F →+* E)
  (x w:ι→F) (j:ℕ) :
  f (oX x w j)=oX (fun i=>f (x i)) (fun i=>f (w i)) j:= by
 simp only [oX,weight,p9,oq,xI,map_inv₀,map_prod,zS]
private theorem ega {F E ι:Type} [Field F] [Field E]
    [yL ι] [zd ι] (p:ℕ) [ExpChar F p]
    (node u v :ι→F) (hfixed : ∀ i,node i^p=node i)
    (φ:F[X] →+* E) (L t:ℕ) (b:Fin 2) (l:Fin L) (j:Fin (t+1)) :
    let f :=φ.comp lI
    let z :=φ lJ
    φ (AI p node u v L t (b,l) j) =
      oX (fun i=>f (node i)) (fun i =>
        if b=0 then f (u i)+z*f (v i)
        else f (u i^p)+z^p*f (v i^p)) (l.val+j.val) := by
  let f :=φ.comp lI
  let z :=φ lJ
  let x := fun i=>f (node i)
  dsimp only
  by_cases hb:b=0
  · simp only [AI,QO,hb,t4 ,qy ,oq]
    change f (oX node u _)+z*f (oX node v _)= _
    rw [aOK,aOK]
    simpa only [sH] using
      (Mw x (fun i=>f (u i)) (fun i=>f (v i))
        1 z (l.val+j.val)).symm
  · simp only [AI,hb,t5]
    rw [φ.map_add,φ.map_mul,φ.map_pow lJ]
    change f (oX node u _^p)+z^p*f (oX node v _^p)= _
    rw [← bxn p node hfixed,← bxn p node hfixed,
      aOK,aOK]
    simpa only [sH] using
      (Mw x (fun i=>f (u i^p)) (fun i=>f (v i^p))
        1 (z^p) (l.val+j.val)).symm
private theorem cEO {F E ι:Type} [Field F] [Field E]
    [yL ι] [zd ι] (p:ℕ) [ExpChar F p]
    (node u v :ι→F) (hx :vw node) (hfixed : ∀ i,node i^p=node i)
    (φ:F[X] →+* E) (hφ:vw φ)
    (k h L t s :ℕ) (hL:h+s=L+1) (hsize :k+(L+1)+t≤MO ι)
    (R:kL.axT p node u v k h)
    (P:Fin 2→F[X][X])
    (hP : ∀ b,P b=Principal.assemble (fun j=>R.coefficients (b,j))) :
    (Sm P (L+1) s).transpose*AI p node u v (L+1) t=0:= by
  classical
  let f :F →+* E :=φ.comp lI
  let x :ι→E := fun i=>f (node i)
  let z :E :=φ lJ
  let w:Fin 2→ι→E := fun b i =>
    if b=0 then f (u i)+z*f (v i)
    else f (u i^p)+z^p*f (v i^p)
  have hMoment (b:Fin 2) (l:Fin (L+1)) (j:Fin (t+1)) :
      φ (AI p node u v (L+1) t (b,l) j)=oX x (w b) (l.val+j.val) :=
    ega p node u v hfixed φ (L+1) t b l j
  have hDegree (b:Fin 2) : (P b).natDegree≤h:= by
    rw [hP]
    exact R.x_degree b
  have hNode (i:ι) :
      ((P 0).map φ).eval (x i)*w 0 i+((P 1).map φ).eval (x i)*w 1 i =
        (R.output.map φ).eval (x i) := by
    have he :=nq φ (R.nodes i)
    simpa only [hP,x,f,qm,z,w,
      zero_ne_one,one_ne_zero,t4 ,t5 ,qy ,oq,xI,
      eval_map_apply] using he
  apply Matrix.ext
  intro d j
  simp only [Matrix.mul_apply,SU,Matrix.zero_apply,Sm]
  apply hφ
  let A (b:Fin 2) :E[X] :=(P b).map φ*lJ ^d.val
  have hA (b:Fin 2) : (A b).natDegree≤L:= by
    have hd: ((P b).map φ).natDegree≤h:=natDegree_map_le.trans (hDegree b)
    have ha :=natDegree_mul_le (p:=(P b).map φ) (q:=(lJ:E[X])^d.val)
    rw [natDegree_X_pow] at ha
    have :=d.isLt
    dsimp only [A]
    omega
  have hOut (i:ι) : (A 0).eval (x i)*w 0 i+(A 1).eval (x i)*w 1 i =
      ((R.output.map φ)*lJ ^d.val).eval (x i) := by
    simp only [A,eval_mul,eval_pow,eval_X]
    rw [← hNode i]
    ring
  have hOutDegree : ((R.output.map φ)*lJ ^d.val).degree<((k+L:ℕ) :WithBot ℕ) := by
    have hR: (R.output.map φ).degree<((k+h:ℕ) :WithBot ℕ) :=degree_map_le.trans_lt R.output_degree
    have hd:=kL.ahy (lJ ^d.val :E[X])
      (R.output.map φ) d.val (k+h) (by simp) hR
    rw [v9] at hd
    refine hd.trans_le ?_
    exact_mod_cast (show k+h+d.val≤k+L by have :=d.isLt; omega)
  rw [p9,xu,Fintype.sum_prod_type,Fin.sum_univ_two]
  simp only [oq,hMoment,← FQ,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_X]
  change (∑ l:Fin (L+1),(A 0).coeff l.val*oX x (w 0) (l.val+j.val)) +
    (∑ l:Fin (L+1),(A 1).coeff l.val*oX x (w 1) (l.val+j.val))=0
  rw [← kL.bhJ x (w 0) (A 0) _ _ (hA 0),
    ← kL.bhJ x (w 1) (A 1) _ _ (hA 1)]
  have hLin:=Mw x
    (fun i=>(A 0).eval (x i)*w 0 i) (fun i=>(A 1).eval (x i)*w 1 i) 1 1 j.val
  simp only [sH] at hLin
  rw [← hLin]
  simp_rw [hOut]
  apply kL.cr7 x (f.injective.comp hx) _ (k+L) _ hOutDegree
  have :=j.isLt
  omega
end Mc
end
section
namespace aw9
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private theorem b8h (a d:ℤ) :
   cost (a+2*d)=cost a+d*(a+1)+d^2 := by
 have h: (a+1)/2+(a/2+1)=a+1 := by omega
 unfold cost
 rw [show (a+2*d+1)/2=(a+1)/2+d by omega,
     show (a+2*d)/2=a/2+d by omega]
 linear_combination d*h
private theorem b8g (x :ℤ) :cost (2*x-1)=x^2 := by
 unfold cost
 rw [show (2*x-1+1)/2=x by omega,show (2*x-1)/2=x-1 by omega]
 ring
private theorem bIM (k t:ℤ) :
   aJt true k t=nX k-(1151+k-t)^2 := by
 change nX k+cost (2300-k-2*(t-2*k-1)-(2*t-2301-k)) +
   cost (t-(t-2*k-1)-2*(2*t-2301-k))-(1151-(t-2*k-1)-(2*t-2301-k))^2= _
 rw [show 2300-k-2*(t-2*k-1)-(2*t-2301-k)=2*(2*(1151+k-t))-1 by ring,
     show t-(t-2*k-1)-2*(2*t-2301-k)=2*(2*(1151+k-t))-1 by ring,
     b8g]
 ring
private theorem b8o (k t:ℤ) :
    aJt false k t=nX k-(1151+k-t)^2+cost (RZ k t-1) := by
  change nX k+cost (2300-k-2*0-(2*t-2301-k)) +
    cost (t-0-2*(2*t-2301-k))-(1151-0-(2*t-2301-k))^2= _
  rw [show 2300-k-2*0-(2*t-2301-k)=2*(2301-t)-1 by ring,b8g,
      show t-0-2*(2*t-2301-k)=(RZ k t-1)+2*(2*(1151+k-t)) by
        unfold RZ; ring,b8h]
  unfold RZ
  ring
private theorem bsh (k t:ℤ) (hk :k≤2300) :
   aJt false k t=cost t - cost (PO k t-1) := by
 change nX k+cost (2300-k-2*0-(2*t-2301-k)) +
   cost (t-0-2*(2*t-2301-k))-(1151-0-(2*t-2301-k))^2= _
 rw [show 2300-k-2*0-(2*t-2301-k)=2*(2301-t)-1 by ring,b8g,
     show t-0-2*(2*t-2301-k)=t+2*(-(2*t-2301-k)) by ring,b8h,
     show PO k t-1=(2300-k)+2*(t-2301) by unfold PO; ring,
     b8h]
 unfold nX
 rw [oZ (by omega)]
 ring
private theorem bfo (z :ℤ) (hz :0≤z) :
   0≤ cost (z-1)∧(0<cost (z-1)↔2≤z) := by
 unfold cost
 have ha :0≤(z-1+1)/2 := by omega
 have hb:0≤(z-1)/2+1 := by omega
 constructor
 · exact v8 ha hb
 · by_cases h:2≤z
   · exact iff_of_true (mul_pos (by omega) (by omega)) h
   · rw [show (z-1+1)/2=0 by omega,zero_mul]
     omega
private theorem eyj (d q:ℤ) (hd:d≤0) (h : -d<2*q) :
  cost (d-1)<q^2 := by
 unfold cost
 have ha :0 ≤ -((d-1+1)/2) := by omega
 have hb:0 ≤ -((d-1)/2+1) := by omega
 have hl : -((d-1+1)/2)≤q:= by omega
 have hr : -((d-1)/2+1)<q:= by omega
 have hp:0<q:= by omega
 have h₁:=mul_le_mul_of_nonneg_right hl hb
 have h₂:=mul_lt_mul_of_pos_left hr hp
 nlinarith only [h₁,h₂]
private theorem eyp (k t:ℤ) (hk :k≤2300) :
    (t6 (decide (0<RZ k t)) k t t ∧
      aJt (decide (0<RZ k t)) k t< min (nX k) (cost t)) ↔
    2301+k≤2*t∧t≤2300∧t≤k+1150∧(2303+k≤2*t∨2*k+3≤t) := by
  have hAdm : ∀ b:Bool,(b=decide (0<RZ k t)) →
      (t6 b k t t↔2301+k≤2*t∧t≤2300∧t≤k+1150) := by
    intro b hb
    cases b <;> simp [t6,azu,RZ,PO] at hb ⊢ <;> omega
  by_cases hb:0<RZ k t
  · rw [decide_eq_true hb,hAdm true (by simp [hb])]
    constructor
    · rintro ⟨ha,hr⟩
      have hm:=bfo (PO k t) (by unfold PO; omega)
      have hn:=bfo (RZ k t) (by omega)
      have h₁:=bIM k t
      have h₂:=b8o k t
      have h₃:=bsh k t hk
      have he :=lt_of_lt_of_le hr (Vq  _ _)
      unfold RZ PO at *
      exact ⟨ha.1,ha.2.1,ha.2.2,by omega⟩
    · rintro ⟨h₁,h₂,h₃,h₄⟩
      refine ⟨⟨h₁,h₂,h₃⟩,lt_min ?_ ?_⟩
      · rw [bIM]
        have hq:0<1151+k-t:= by omega
        have hp:=mul_pos hq hq
        nlinarith only [hp]
      · have hm:=bfo (PO k t) (by unfold PO; omega)
        have hn:=bfo (RZ k t) (by omega)
        have e₁:=bIM k t
        have e₂:=b8o k t
        have e₃:=bsh k t hk
        unfold RZ PO at *
        omega
  · rw [decide_eq_false hb,hAdm false (by simp [hb])]
    constructor
    · rintro ⟨ha,hr⟩
      have hm:=bfo (PO k t) (by unfold PO; omega)
      have he :=lt_of_lt_of_le hr (Vq  _ _)
      rw [bsh k t hk] at he
      unfold PO at *
      exact ⟨ha.1,ha.2.1,ha.2.2,Dw  (by omega)⟩
    · rintro ⟨h₁,h₂,h₃,h₄⟩
      refine ⟨⟨h₁,h₂,h₃⟩,lt_min ?_ ?_⟩
      · rw [b8o]
        have hg:=eyj (RZ k t) (1151+k-t)
          (by omega) (by unfold RZ; omega)
        omega
      · rw [bsh k t hk]
        have hm:=bfo (PO k t) (by unfold PO; omega)
        unfold RZ PO at *
        omega
private def arM (k :ℕ) :=max ((k+2302)/2) (min ((k+2304)/2) (2*k+3))
private def aou (k :ℕ) :=min 2301 (k+1151)
private def aOB (k :ℕ) :=min (2*k+2) (aou k)
private def aov (a b c t:ℕ) :Mode :=
 if t<a then .empty else if t<b then .ic false
 else if t<c then .ic true else .columns
private abbrev b8j (k :ℕ) :Prop :=
 k≤2249∧(arM k≤2301-k∨cost ((arM k :ℤ)-1)<nX k) ∧
   nX k≤ cost ((max (2301-k) (aou k) :ℕ) :ℤ)
private theorem b8f {a b:ℤ} (ha :0≤a) (hab:a≤b) :cost a≤ cost b:= by
 unfold cost
 exact mul_le_mul (by omega) (by omega) (by omega) (by omega)
private theorem cYV (k t:ℕ) (hg:b8j k) (ht:2301-k≤t) :
    anR k t=aov (arM k) (aOB k) (aou k) t:= by
  obtain ⟨hk,hlo,hhi⟩:=hg
  unfold anR
  dsimp only
  simp only [eyp (k :ℤ) t (by omega)]
  by_cases ha :t<arM k
  · have hlt:cost (t:ℤ)<nX k := by
      rcases hlo with h | h
      · omega
      · exact lt_of_le_of_lt (b8f (by positivity) (by omega)) h
    have he : ¬ (2301+(k :ℤ)≤2*(t:ℤ)∧(t:ℤ)≤2300∧(t:ℤ)≤(k :ℤ)+1150 ∧
        (2303+(k :ℤ)≤2*(t:ℤ)∨2*(k :ℤ)+3≤(t:ℤ))) := by
      unfold arM at ha; omega
    simp [not_le.mpr hlt,aov,ha]
    omega
  · by_cases hc:t<aou k
    · have hs :2301+(k :ℤ)≤2*(t:ℤ)∧(t:ℤ)≤2300∧(t:ℤ)≤(k :ℤ)+1150 ∧
          (2303+(k :ℤ)≤2*(t:ℤ)∨2*(k :ℤ)+3≤(t:ℤ)) := by
        unfold arM at ha; unfold aou at hc; omega
      by_cases hb:t<aOB k
      · have hp : ¬ 0<RZ k t:= by
          unfold aOB at hb; unfold RZ; omega
        simp [hs,hp,aov,ha,hb]
      · have hp:0<RZ k t:= by
          unfold aOB at hb; unfold RZ; omega
        simp [hs,hp,aov,ha,hb,hc]
    · have he : ¬ (2301+(k :ℤ)≤2*(t:ℤ)∧(t:ℤ)≤2300∧(t:ℤ)≤(k :ℤ)+1150 ∧
          (2303+(k :ℤ)≤2*(t:ℤ)∨2*(k :ℤ)+3≤(t:ℤ))) := by
        unfold aou at hc; omega
      have hle :=hhi.trans (b8f (b:=(t:ℤ)) (by positivity) (by omega))
      have hb : ¬t<aOB k := by unfold aOB; omega
      simp [hle,aov,ha,hb,hc]
      omega
private def aDN (a b c t n:ℕ) :ℕ :=
 if t<a then min n ((a+1-t)/2)
 else if t<b then min n ((b+1-t)/2)
 else if t<c then min n ((c+1-t)/2)
 else n
private theorem cY2 (a b c t n:ℕ) :aDN a b c t n≤n:= by
 unfold aDN
 split_ifs <;> omega
private theorem eyv (a b c t n i:ℕ) (hi:i<n) :
  (aov a b c (t+2*i)=aov a b c t)↔i<aDN a b c t n:= by
 unfold aDN aov
 split_ifs <;> simp_all <;> omega
private theorem eyi (k t:ℤ) (mode :Mode) (n w:ℕ)
    (cut : ∀ i:ℕ,i<n→(anR k (t+2*i)=mode↔i<w))
    (fuel lo hi:ℕ) (hl:lo<w) (hr :w≤hi) (hn:hi<n)
    (hspan:hi-lo≤2^fuel) :Ly k t mode fuel lo hi=w-1 := by
  induction fuel generalizing lo hi with
  | zero=>simp only [Ly]; simp only [pow_zero] at hspan; omega
  | succ f ih =>
    rw [Ly]
    split
    · omega
    · dsimp only
      have hm:=cut ((lo+hi)/2) (by omega)
      rw [Dz] at hspan
      split
      · rename_i h
        have hh:=hm.mp h
        apply ih <;> omega
      · rename_i h
        have hh:=mt hm.mpr h
        apply ih <;> omega
private theorem eym (k t:ℤ) (mode :Mode) (n w:ℕ) (hn:0<n) (hcap:n≤4096)
   (hw:w≤n) (hw₀:0<w)
   (cut : ∀ i:ℕ,i<n→(anR k (t+2*i)=mode↔i<w)) :
   E0 k t n mode=w:= by
 unfold E0
 rw [show (n:ℤ)-1=((n-1 :ℕ) :ℤ) by omega]
 have he :=cut (n-1) (by omega)
 split
 · rename_i h
   have hh:=he.mp h
   omega
 · rename_i h
   have hh:=mt he.mpr h
   rw [eyi k t mode n w cut 12 0 (n-1) hw₀ (by omega) (by omega)
         (by change n-1-0≤4096; omega)]
   omega
private theorem b8e {k t:ℤ} {b:Bool} (h:anR k t = .ic b) :
  admissible b k t t:= by
 unfold anR at h
 dsimp only at h
 split at h
 next hs=>cases h; exact hs.1
 next=>split at h <;> contradiction
private theorem eyu {k l r :ℤ} {mode :Mode}
   (hl:anR k l=mode) (hr :anR k r=mode) :valid mode k l r := by
 cases mode with
 | columns | empty=>trivial
 | ic b =>
   have h₁:=b8e hl
   have h₂:=b8e hr
   cases b <;> simp [t6,valid] at h₁ h₂ ⊢ <;> tauto
private def aOC (t:ℕ) :=((t+1)/2)*(t/2+1)
private def b8m (t:ℕ) :=(t/2)*((t+1)/2)
private def a5A (k :ℕ) :=1324801-aOC (2300-k)
private def b8k (n:ℕ) :=n*(n-1)/2
private def b8p (n:ℕ) :=n*(n-1)*(2*n-1)/6
private theorem bfp (t:ℕ) : (aOC t:ℤ)=cost t:= by
 simp [aOC,cost,Nq]
private theorem eyn (t:ℕ) : (b8m t:ℤ)=cost ((t:ℤ)-1) := by
 simp [b8m,cost,Nq,show ((t:ℤ)-1)/2+1=((t:ℤ)+1)/2 by omega]
private theorem bIK (k :ℕ) (hk :k≤2249) :
  (a5A k :ℤ)=nX k := by
 have hm:=b8f (a :=((2300-k :ℕ) :ℤ)) (b:=2300) (by positivity) (by omega)
 rw [← bfp] at hm
 have hd:cost 2300≤1324801 := by decide
 have hc:aOC (2300-k)≤1324801 := by omega
 simp [a5A,nX ,zE hc,bfp,
  zE (by omega :k≤2300),oZ (by omega : (0:ℤ)≤2300-k)]
private theorem b8l (n:ℕ) (hn:0<n) : (b8k n:ℤ)=a5v n:= by
 simp [b8k,a5v,Nq,zE (by omega :1≤n)]
private theorem b8q (n:ℕ) (hn:0<n) : (b8p n:ℤ)=a8K n:= by
 simp [b8p,a8K,Int.natCast_ediv,Nat.cast_sub (by omega :1≤n),
  zE  (by omega :1≤2*n)]
private theorem eyq (k t:ℤ) (n:ℕ) :
  azE (.ic true) k t n =
   (n:ℤ)*nX k - bhE (1151+k-t) (-2) n:= by
 have h:=bIM k t
 simp [azE,aJt,azu,aJF,bhE,RZ,PO] at h ⊢
 linear_combination (n:ℤ)*h
private theorem eyr (k t:ℤ) (n:ℕ) (hk :k≤2300) :
  azE (.ic false) k t n =
   aJF t 1 n-aJF (PO k t-1) 2 n:= by
 have h:=bsh k t hk
 simp [azE,aJt,azu,aJF,bhE,PO] at h ⊢
 linear_combination (n:ℤ)*h
private def aDM (mode :Mode) (k t w:ℕ) :ℤ :=
 let l:=b8k w
 let s :=b8p w
 let col:=w*a5A k
 let e :=w*aOC t+(t+1)*l+s
 match mode with
 | .columns=>(col:ℤ)
 | .empty=>(e :ℤ)
 | .ic false =>
   let m:=2*t-(2301+k)
   (e :ℤ)-((w*b8m m+2*m*l+4*s :ℕ) :ℤ)
 | .ic true =>
   let q:=1151+k-t
   ((col+4*q*l:ℕ) :ℤ)-((w*q^2+4*s :ℕ) :ℤ)
private theorem eyh (k t w:ℕ) (hk :k≤2249) (hw:0<w)
    (mode :Mode) (hm:anR k t=mode) :azE mode k t w=aDM mode k t w:= by
  cases mode with
  | columns=>simp [aDM,azE,bIK k hk]
  | empty=>simp [aDM,azE,aJF,bfp,b8l w hw,b8q w hw]
  | ic b =>
    have ha :=b8e hm
    cases b with
    | false =>
      have h:2301+k≤2*t:= by simp [t6,PO] at ha; omega
      rw [eyr _ _ _ (by omega)]
      simp [aDM,aJF,bfp,eyn,b8l w hw,b8q w hw,
        zE h,PO]
      ring_nf
    | true =>
      have h:t≤1151+k := by
        simp [t6,azu,RZ,PO] at ha; omega
      rw [eyq]
      simp [aDM,bhE,bIK k hk,b8l w hw,b8q w hw,zE h]
      ring
private def ame (k a b c:ℕ) :ℕ→ℕ→ℕ→ℤ
 | 0,_,n=>(n:ℤ)*columns k
 | fuel+1,t,n =>
   if n=0 then 0 else
     let mode :=aov a b c t
     let w:=aDN a b c t n
     aDM mode k t w+ame k a b c fuel (t+2*w) (n-w)
private theorem cYZ (k :ℕ) (hg:b8j k) (fuel t n:ℕ)
    (ht:2301-k≤t) (hcap:n≤4096) :
    aoE k fuel t n=ame k (arM k) (aOB k) (aou k) fuel t n:= by
  let a :=arM k
  let b:=aOB k
  let c:=aou k
  change aoE k fuel t n=ame k a b c fuel t n
  induction fuel generalizing t n with
  | zero=>rfl
  | succ f ih =>
    by_cases hn:n=0
    · simp [aoE,ame,hn]
    · let w:=aDN a b c t n
      let m:=aov a b c t
      have hm:anR k t=m:=cYV k t hg ht
      have cut (i:ℕ) (hi:i<n) :anR k ((t:ℤ)+2*i)=m↔i<w:= by
        have hx :=cYV k (t+2*i) hg (by omega)
        push_cast at hx
        rw [hx]
        exact eyv a b c t n i hi
      have hw₀:0<w:=(cut 0 (by omega)).1 (by simpa using hm)
      have hw:=eym (k :ℤ) (t:ℤ) m n w (by omega) hcap (cY2 ..) hw₀ cut
      have hlast :=(cut (w-1) (by have :=cY2 a b c t n; dsimp [w]; omega)).2 (by omega)
      rw [show ((w-1 :ℕ) :ℤ)=(w:ℤ)-1 by omega] at hlast
      have hv :=eyu hm hlast
      have hcharge :=eyh k t w hg.1 hw₀ m hm
      have tail:=ih (t+2*w) (n-w) (by omega) (by omega)
      push_cast at tail
      simp only [aoE,ame,p5 hn,hm,hw,t8 hv,hcharge]
      exact nq (_ + ·) tail
private abbrev cYT (k :ℕ) :Prop :=
 k≤2249∧(arM k≤2301-k∨aOC (arM k-1)<a5A k) ∧
   a5A k≤aOC (max (2301-k) (aou k))
private theorem eyk {k :ℕ} (h:cYT k) :b8j k := by
 obtain ⟨hk,hlo,hhi⟩:=h
 refine ⟨hk,?_,?_⟩
 · rcases hlo with hl | hl
   · exact Dw hl
   · apply Or.inr
     have hcast: ((aOC (arM k-1) :ℕ) :ℤ)<a5A k := by exact_mod_cast hl
     rw [bfp,bIK k hk] at hcast
     have hab:1≤arM k := by unfold arM; omega
     simpa only [zE hab,In] using hcast
 · have hcast: (a5A k :ℤ)≤aOC (max (2301-k) (aou k)) := by exact_mod_cast hhi
   simpa only [bIK k hk,bfp] using hcast
private def a5B (k :ℕ) (m:Mode) (u:ℕ) (next:ℕ→ℕ→ℤ) (t n:ℕ) :ℤ :=
 if n=0 then 0 else
 if t< u then
  let w:=min n ((u+1-t)/2)
  if w=n then aDM m k t n
  else aDM m k t w+next (t+2*w) (n-w)
 else next t n
private theorem bIL (k a b c f t:ℕ) :ame k a b c f t 0=0:= by
 cases f <;> simp [ame]
private theorem b8r (k a b c t n u f :ℕ) (m:Mode) (next:ℕ→ℕ→ℤ)
   (hm:t< u→aov a b c t=m)
   (hw:t< u→aDN a b c t n=min n ((u+1-t)/2))
   (skip :u≤t→ame k a b c (f+1) t n=next t n)
   (tail : ∀ w,u≤t+2*w→ame k a b c f (t+2*w) (n-w)=next (t+2*w) (n-w)) :
   ame k a b c (f+1) t n=a5B k m u next t n:= by
 by_cases hn:n=0
 · simp [hn,a5B,bIL]
 by_cases hu:t< u
 · simp only [a5B,ame,p5 hn,t8 hu,hm hu,hw hu]
   split
   · rename_i h
     simp only [h,Nat.sub_self,bIL,Av]
   · rename_i h
     rw [tail _ (by omega)]
 · simpa only [a5B,p5 hn,p5 hu] using skip (by omega)
private theorem bIJ (k a b c t n f :ℕ) (ha :a≤t) (hb:b≤t) (hc:c≤t) :
   ame k a b c (f+1) t n=aDM .columns k t n:= by
 by_cases hn:n=0
 · simp [hn,aDM,bIL]
 · simp [ame,hn,aov,aDN,not_lt.mpr ha,not_lt.mpr hb,
    not_lt.mpr hc,bIL]
private def cY0 (k c:ℕ) :=
 a5B k (.ic true) c (aDM .columns k)
private theorem cY1 (k a b c t n f :ℕ) (ha :a≤t) (hb:b≤t) :
   ame k a b c (f+2) t n=cY0 k c t n:= by
 apply b8r
 · intro hc; simp [aov,not_lt.mpr ha,not_lt.mpr hb,hc]
 · intro hc; simp [aDN,not_lt.mpr ha,not_lt.mpr hb,hc]
 · exact bIJ k a b c t n (f+1) ha hb
 · intro w hc; exact bIJ _ _ _ _ _ _ f (by omega) (by omega) hc
private def cYW (k b c:ℕ) :=a5B k (.ic false) b (cY0 k c)
private theorem cYX (k a b c t n f :ℕ) (ha :a≤t) :
   ame k a b c (f+3) t n=cYW k b c t n:= by
 apply b8r
 · intro hb; simp [aov,not_lt.mpr ha,hb]
 · intro hb; simp [aDN,not_lt.mpr ha,hb]
 · exact cY1 k a b c t n (f+1) ha
 · intro w hb; exact cY1 _ _ _ _ _ _ f (by omega) hb
private def b8i (k a b c:ℕ) :=a5B k .empty a (cYW k b c)
private theorem cYS (k a b c t n f :ℕ) :
   ame k a b c (f+4) t n=b8i k a b c t n:= by
 apply b8r
 · intro ha; simp [aov,ha]
 · intro ha; simp [aDN,ha]
 · exact cYX k a b c t n (f+1)
 · intro w ha; exact cYX _ _ _ _ _ _ f ha
private def b8n (k :ℕ) :ℤ :=
 if cYT k then
  let a :=arM k; let b:=aOB k; let c:=aou k
  b8i k a b c (2301-k) 1350+b8i k a b c (2302-k) 1350
 else aDZ k
private theorem eyo (k :ℕ) :aDZ k=b8n k := by
  unfold b8n
  split
  · rename_i hn
    have hg:=eyk hn
    have hk :=hg.1
    unfold aDZ
    rw [zm (by omega :2700≤5000-k)]
    change aoE k 8 (5001-(k :ℤ)-2700) 1350 +
      aoE k 8 (5001-(k :ℤ)-2700+1) 1350= _
    rw [show 5001-(k :ℤ)-2700+1=((2302-k :ℕ) :ℤ) by omega,
        show 5001-(k :ℤ)-2700=((2301-k :ℕ) :ℤ) by omega,
        cYZ k hg 8 (2301-k) 1350 (by omega) (by decide),
        cYZ k hg 8 (2302-k) 1350 (by omega) (by decide),
        cYS _ _ _ _ _ _ 4,cYS _ _ _ _ _ _ 4]
  · rfl
private def b8s (s :ℕ) :ℕ→ℤ
 | 0=>0
 | n+1=>b8s s n+b8n (s+n)
private theorem aOD (s n:ℕ) :oD s n=b8s s n:= by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [total,b8s,ih,eyo]
theorem gMA:oD 0 250=93967425000 :=
 (aOD 0 250).trans (by decide +kernel)
theorem gMB:oD 250 250=267062737500 :=
 (aOD 250 250).trans (by decide +kernel)
theorem gMM:oD 500 250=418442617575 :=
 (aOD 500 250).trans (by decide +kernel)
theorem gMN :oD 750 250=531379109797 :=
 (aOD 750 250).trans (by decide +kernel)
theorem gMO:oD 1000 250=586700450900 :=
 (aOD 1000 250).trans (by decide +kernel)
theorem gMP:oD 1250 250=595527605250 :=
 (aOD 1250 250).trans (by decide +kernel)
theorem gMQ:oD 1500 250=568622558375 :=
 (aOD 1500 250).trans (by decide +kernel)
theorem gMR :oD 1750 250=514817120875 :=
 (aOD 1750 250).trans (by decide +kernel)
theorem gMS:oD 2000 250=442900355250 :=
 (aOD 2000 250).trans (by decide +kernel)
end aw9
end
section
namespace Rj
open scoped BigOperators
set_option maxHeartbeats 600000
def ast (q k :ℕ) (i:Fin 6) :ℕ :=
 if i=0∨i=3 then 7299 - q-3*k else 0
private theorem ehP (q:ℕ) :
  Xi ast q =
   ∑ k∈cy (7300 - q),xR q (aU k) (ast q k) := by
 symm
 apply ze (xL (Iw _ _))
 intro k _ hk
 have h:Ic q (aU k)≤0:= by
  unfold Ic aU
  simp only [Du] at hk
  omega
 simp [xR,h]
private def ah5 (w:ℤ) :ℤ:=w^2/4
private def xV (w:ℤ) :ℤ:=ah5 (w+1)
private theorem ZE (w:ℤ) :2*sG w=w*(w+1) := by
 unfold sG
 apply FR
 rcases (show w % 2=0∨w % 2=1 by omega) with h | h
 · have hw:w=2*(w/2) := by omega
   exact Vz  (by rw [hw]; exact VH  _ _) _
 · have hw:w+1=2*(w/2+1) := by omega
   exact VC  (by rw [hw]; exact VH  _ _) _
private theorem bKU (w:ℤ) :
   4*ah5 w=w^2 - w % 2 := by
 unfold ah5
 rcases (show w % 2=0∨w % 2=1 by omega) with h | h
 · have hw:w=2*(w/2) := by omega
   have he :w^2=4*(w/2)^2 := by
     calc _=(2*(w/2))^2 :=congrArg (· ^ 2) hw
          _ = _:= by ring
   rw [he,h]
   omega
 · have hw:w=2*(w/2)+1 := by omega
   have he :w^2=4*((w/2)^2+w/2)+1 := by
     calc _=(2*(w/2)+1)^2 :=congrArg (· ^ 2) hw
          _ = _:= by ring
   rw [he,h]
   omega
private theorem awQ (w:ℤ) :
  4*xV w=w^2+2*w+w % 2 := by
 unfold xV
 rw [bKU]
 have h: (w+1) % 2+w % 2=1 := by omega
 nlinarith only [h]
private theorem bYc {a w:ℤ} (ha :a≤(w+1)/2) (hw:0≤w) :
   yC ⟨a,w⟩=xV w:= by
 have hu:0≤(w+1)/2 := by omega
 have huv : (w+1)/2≤w:= by omega
 have h: (w+1)/2=w/2+w % 2 := by omega
 have h' : w-(w+1)/2=w/2 := by omega
 unfold yC
 simp only [oZ ha,oZ hu,oZ huv]
 rw [h',h]
 have h₁:=ZE (w/2+w % 2)
 have h₂:=ZE (w/2)
 have h₃:=awQ w
 rcases (show w % 2=0∨w % 2=1 by omega) with he | he
 · have hw:w=2*(w/2) := by omega
   rw [he] at h₁ h₃ ⊢
   conv at h₃=>rhs; rw [hw]
   nlinarith only [h₁,h₂,h₃]
 · have hw:w=2*(w/2)+1 := by omega
   rw [he] at h₁ h₃ ⊢
   conv at h₃=>rhs; rw [hw]
   nlinarith only [h₁,h₂,h₃]
private theorem agp (q k :ℕ) (f :Fin 6→ℤ) :
  (∑ j,(ast q k j:ℤ)*f j) =
    ((7299 - q-3*k :ℕ) :ℤ)*(f 0+f 3) := by
 simp [JM,ast,Fin.succ,t7]
private theorem gAc (k n t:ℤ) (hn:n=0∨t=n+2*k+1) :
    sG (2301 - 2*n) - xV (2300 - k - 2*n) - xV (2300 - 2*n) -
        xV (t - n) =
      sG 2301 - xV (2300 - k) - xV 2300 - xV t +
        ah5 n:= by
  rcases hn with rfl | ht
  · simp [ah5]
  have hp: (2300 - k - 2*n) % 2=(2300 - k) % 2 := by omega
  have hq: (2300 - 2*n) % 2=0:= by omega
  have ho: (t - n) % 2=1 := by omega
  have hs :t % 2=1 - n % 2 := by omega
  have hTP:=ZE (2301 - 2*n)
  have hT:=ZE 2301
  have hPP:=awQ (2300 - k - 2*n)
  have hP:=awQ (2300 - k)
  have hQP:=awQ (2300 - 2*n)
  have hQ:=awQ 2300
  have hOP:=awQ (t - n)
  have hO:=awQ t
  have hN :=bKU n
  rw [hp] at hPP
  rw [hq] at hQP
  rw [ho] at hOP
  rw [hs] at hO
  norm_num only [Int.reduceMod] at hQ
  rw [ht] at hOP hO ⊢
  nlinarith only [hTP,hT,hPP,hP,hQP,hQ,hOP,hO,hN]
private def bOK (r k :ℕ) :ℕ :=
 (xV ((r :ℤ) - k)-ah5 ((r - 1 - 3*k :ℕ) :ℤ)).toNat
private theorem dzb (q k :ℕ) (hlo:6790≤q) (hhi:q≤6820)
    (hk :k<7300 - q) :
    xR q (aU k) (ast q k)≤bOK (7300 - q) k := by
  let n:ℤ:=((7299 - q-3*k :ℕ) :ℤ)
  let t:ℤ:=7300-(q:ℤ) - k
  have hn:n=0∨t=n+2*(k :ℤ)+1 := by
    dsimp [n,t]
    omega
  have hnr :0≤n:=Ea _
  have htn:n≤t:= by dsimp [n,t]; omega
  have hnmax :n≤509:= by dsimp [n]; omega
  have hkmax : (k :ℤ)≤509:= by omega
  have ht:0<t:= by dsimp [t]; omega
  have hr (x :ℕ) :7300 - q - 1 - x=7299 - q - x := by omega
  have hd:iO q=2300:=vl (by omega)
  have ho:Ic q (aU k)=t:= by unfold Ic aU t; ring
  have hc:Bb q (aU k)=sG 2301 - xV (2300 - k) - xV 2300:= by
    have harg :min (2300:ℤ) (-offset k - 1)=2300 - k - 1 := by unfold aU; omega
    have hpos : ¬ (2300-(k :ℤ) - 1)<0:= by omega
    have hmin:min (2300-(k :ℤ) - 1) 4600=2300 - k - 1 :=zm (by omega)
    have hmax :max (0:ℤ) (2300 - k - 1 - 2300)=0:=zf (by omega)
    have heval :gd 2300 2300=sG 2301 - xV 2300:= by decide
    unfold Bb
    rw [hd,harg]
    change gd 2300 2300 - gd 2300 (2300-(k :ℤ) - 1)= _
    rw [heval]
    simp only [gd,hpos,t5 ,show (2*2300:ℤ)=4600 by decide,hmin,hmax]
    unfold xV ah5
    have he : (2300-(k :ℤ) - 1+2)=2300 - k+1 := by ring
    rw [he]
    norm_num [sG]
    ring
  have hd' : K6 q (ast q k)=2300 - 2*n:= by
    rw [K6,hd,agp]
    simp [yE,n]
    ring
  have hP:D8 q (aU k) (ast q k) 0=⟨-n,2300 - k - 2*n⟩:= by
    simp [D8,agp,pT,Jd,aU,n]
    ring
  have hQ:D8 q (aU k) (ast q k) 1=⟨1150 - n,2300 - 2*n⟩:= by
    simp [D8,agp,pT,Jd,aU,n,hd]
    ring
  have hO:D8 q (aU k) (ast q k) 2=⟨-n,t - n⟩:= by
    simp [D8,agp,pT,Jd,ho,n]
  have hkernel :
      m5 (K6 q (ast q k)) (D8 q (aU k) (ast q k)) =
        Bb q (aU k) - xV t+ah5 n:= by
    rw [m5,hd']
    simp only [show ¬ (2300 - 2*n)<0 by omega,t5]
    rw [qG,hP,hQ,hO]
    rw [bYc (by omega) (by omega),
      bYc (by omega) (by omega),
      bYc (by omega) (by omega),hc]
    calc
      _=sG (2301 - 2*n) - xV (2300 - k - 2*n) -
          xV (2300 - 2*n) - xV (t - n) := by ring
      _ = _:=gAc k n t hn
  have htc: ((7300 - q:ℕ) :ℤ) - k=t:= by dsimp [t]; omega
  unfold xR bOK
  simp only [ho,G4 ht,t5 ,htc,hr]
  change _≤(xV t - ah5 n).toNat
  apply Hw
  calc
    _≤Bb q (aU k) -
        m5 (K6 q (ast q k)) (D8 q (aU k) (ast q k)) := by
      exact G1 ((u9 _ _).trans (u9 _ _)) _
    _=xV t - ah5 n:= by rw [hkernel]; ring
private def Lb (r :ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>Lb r n+bOK r n
private theorem gxf (r n:ℕ) :
   (∑ k∈cy n,bOK r k)=Lb r n:= by
 induction n with
 | zero=>simp [Lb]
 | succ n ih=>rw [Finset.sum_range_succ,ih,Lb]
private def total:ℕ→ℕ
 | 0=>0
 | n+1=>total n+Lb (510 - n) (510 - n)
private theorem crM (n:ℕ) :
   (∑ j∈cy n,Lb (510 - j) (510 - j))=total n:= by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [Finset.sum_range_succ,ih,total]
section
set_option maxRecDepth 4096
private theorem gz7:Lb 510 510=7456455:= by decide +kernel
private theorem gz6:Lb 509 509=7412850:= by decide +kernel
private theorem gz5:Lb 508 508=7369415:= by decide +kernel
private theorem gz4 :Lb 507 507=7326150:= by decide +kernel
private theorem gz3:Lb 506 506=7283055:= by decide +kernel
private theorem gz2 :Lb 505 505=7240129:= by decide +kernel
private theorem gz1 :Lb 504 504=7197372 := by decide +kernel
private theorem gz0:Lb 503 503=7154784 := by decide +kernel
private theorem gzZ:Lb 502 502=7112364 := by decide +kernel
private theorem gzY:Lb 501 501=7070112 := by decide +kernel
private theorem gzX:Lb 500 500=7028028:= by decide +kernel
private theorem gzW:Lb 499 499=6986111 := by decide +kernel
private theorem gzV:Lb 498 498=6944361 := by decide +kernel
private theorem gzU:Lb 497 497=6902778:= by decide +kernel
private theorem gzT:Lb 496 496=6861361 := by decide +kernel
private theorem gzS:Lb 495 495=6820110 := by decide +kernel
private theorem gzR:Lb 494 494=6779025:= by decide +kernel
private theorem gzQ:Lb 493 493=6738105:= by decide +kernel
private theorem gzP:Lb 492 492=6697350:= by decide +kernel
private theorem gzO:Lb 491 491=6656760:= by decide +kernel
private theorem gzN :Lb 490 490=6616334 := by decide +kernel
private theorem gzM:Lb 489 489=6576072 := by decide +kernel
private theorem gzL:Lb 488 488=6535974 := by decide +kernel
private theorem gzK:Lb 487 487=6496039:= by decide +kernel
private theorem gzJ:Lb 486 486=6456267:= by decide +kernel
private theorem gzI:Lb 485 485=6416658:= by decide +kernel
private theorem gzH :Lb 484 484=6377211 := by decide +kernel
private theorem gzG:Lb 483 483=6337926:= by decide +kernel
private theorem gzF:Lb 482 482=6298803:= by decide +kernel
private theorem gzE :Lb 481 481=6259841 := by decide +kernel
private theorem gzD:Lb 480 480=6221040:= by decide +kernel
end
private theorem Rc {n a b:ℕ} (hp:total n=a)
  (hr :Lb (510 - n) (510 - n)=b) :total (n+1)=a+b :=
 congrArg₂ Nat.add hp hr
private theorem bxY:total 31≤211628840:= by
 have h0:total 0=0:=rfl
 have h1 :total 1=7456455:=Rc h0 gz7
 have h2 :total 2=14869305:=Rc h1 gz6
 have h3:total 3=22238720:=Rc h2 gz5
 have h4 :total 4=29564870:=Rc h3 gz4
 have h5:total 5=36847925:=Rc h4 gz3
 have h6:total 6=44088054 :=Rc h5 gz2
 have h7:total 7=51285426:=Rc h6 gz1
 have h8:total 8=58440210 :=Rc h7 gz0
 have h9:total 9=65552574 :=Rc h8 gzZ
 have Kr :total 10=72622686:=Rc h9 gzY
 have h11 :total 11=79650714 :=Rc Kr gzX
 have h12 :total 12=86636825:=Rc h11 gzW
 have h13:total 13=93581186:=Rc h12 gzV
 have h14 :total 14=100483964 :=Rc h13 gzU
 have h15:total 15=107345325:=Rc h14 gzT
 have MV:total 16=114165435:=Rc h15 gzS
 have h17:total 17=120944460:=Rc MV gzR
 have h18:total 18=127682565:=Rc h17 gzQ
 have h19:total 19=134379915:=Rc h18 gzP
 have h20:total 20=141036675:=Rc h19 gzO
 have Tu:total 21=147653009:=Rc h20 gzN
 have h22 :total 22=154229081 :=Rc Tu gzM
 have h23:total 23=160765055:=Rc h22 gzL
 have h24 :total 24=167261094 :=Rc h23 gzK
 have h25:total 25=173717361 :=Rc h24 gzJ
 have h26:total 26=180134019:=Rc h25 gzI
 have h27:total 27=186511230:=Rc h26 gzH
 have h28:total 28=192849156:=Rc h27 gzG
 have h29:total 29=199147959:=Rc h28 gzF
 have h30:total 30=205407800:=Rc h29 gzE
 have h31 :total 31=211628840:=Rc h30 gzD
 exact le_of_eq h31
theorem bxv :
   ∃ p:ℕ→ℕ→kJ,
     (∑ j∈cy 31,Xi p (6790+j))≤211628840:= by
 refine ⟨ast,?_⟩
 apply le_trans _ bxY
 rw [← crM]
 apply qM
 intro j hj
 have hj' := Finset.mem_range.mp hj
 rw [ehP,← gxf]
 have h:7300-(6790+j)=510 - j:= by omega
 rw [← h]
 apply qM
 intro k hk
 exact dzb _ _ (by omega) (by omega) (Finset.mem_range.mp hk)
end Rj
end
section
namespace Rj
noncomputable section
open aR MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 600000
instance gO4 (q k :ℕ) :uW ao (Block q k) := by
 apply restrictSupport_finite
 refine (Un (fun _:Option (Fin 3)=>1)
   (by simp) (q+k)).subset ?_
 intro e he
 change FF q e∧e.weight BU=q∧_ at he
 have hidx :=he.1.2.1
 have ha :e none≤k := by
   have h:=he.2.2
   unfold aU at h
   omega
 have hw:e.weight (fun _=>1)=e none+e.weight BU:= by
   simp only [Bf ,NI,BU,
     Option.elim_none,Option.elim_some,sI,Nat.mul_one,Nat.mul_zero,qJ]
 change e.weight (fun _=>1)≤q+k
 rw [hw,he.2.1]
 omega
theorem b5V (e :Exp) (c:ao) (he :5000≤e none) :
    origin (ov e c)=0:= by
  change GY oH 5000 (pC La (ov e c))=0
  apply (G7 _ _ _).mpr
  refine SW
    (w:= fun v :Option (Fin 3)=>v.elim 1 (fun _=>0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa [La] using
        (IT (R:=ao) oH
          (none :Option (Fin 3)) (m:=1) (by rfl))
    | some j=>simp
  · apply (monomial_mem_restrictWeightedOrder _ _ _ _).mpr
    exact Dw (by simpa only [Finsupp.weight_elim_one_zero] using he)
def aTt (B:ℕ) :u8 ao Flat :=qU (origin.domRestrict (apR B))
private def aTg (i:ℕ×ℕ) :u8 ao Flat :=
 qU (af3 i.1 i.2)
private instance (i:ℕ×ℕ) :uW ao (aTg i) :=
 Module.Finite.range (af3 i.1 i.2)
private def pairs (B:ℕ) :pG (ℕ×ℕ) :=
 (cy (B+1)) ×ˢ (cy 7300)
private theorem cen (B:ℕ) :aTt B≤(pairs B).sup aTg:= by
 classical
 intro P hP
 obtain ⟨Q,rfl⟩:=LinearMap.mem_range.mp hP
 change origin Q.1∈(pairs B).sup aTg
 have expand:=nq origin Q.1.as_sum
 rw [p9] at expand
 rw [expand]
 refine Nj _ fun e he => ?_
 by_cases hi:5000≤e none
 · rw [b5V e (Q.1.coeff e) hi]
   exact Il _
 have hbox :FF B e := Q.2 he
 let q:=e.weight BU
 let k :=e none+(2300-e.weight th)
 have hmem: (q,k)∈pairs B:= by
   simp only [pairs,Finset.mem_product,Du]
   have hq:=hbox.1
   dsimp [q,k] at *
   omega
 apply (Finset.le_sup (f :=aTg) hmem)
 refine LinearMap.mem_range.mpr ⟨⟨ov e (Q.1.coeff e),?_⟩,rfl⟩
 intro u hu
 have hue :u=e := by
   by_contra hne
   exact (MvPolynomial.mem_support_iff.mp hu) (by simp [yl,Ne.symm hne])
 subst u
 change (q≤q∧e.weight th≤2300∧e (some 2)≤1150) ∧
   e.weight BU=q∧(e none :ℤ)-(e.weight th:ℤ)=aU k
 refine ⟨⟨uh,hbox.2.1,hbox.2.2⟩,rfl,?_⟩
 have hj:=hbox.2.1
 dsimp [aU,k]
 omega
instance gO9 (B:ℕ) :uW ao (aTt B) :=
 SD (Submodule.inclusion (cen B))
  (Submodule.inclusion_injective (cen B))
private theorem b3b (S:pG (ℕ×ℕ)) :
   oz ao (S.sup aTg:u8 ao Flat) ≤
    ∑ i∈S,oz ao (aTg i) := by
 classical
 induction S using R9 with
 | empty=>simp
 | insert i S hi ih =>
   rw [Finset.sup_insert,Ob hi]
   exact (Submodule.finrank_add_le_finrank_add_finrank (aTg i) (S.sup aTg)).trans
    (NZ ih _)
theorem dFi (B:ℕ) (bound:ℕ→ℕ→ℕ)
   (h : ∀ q<B+1,∀ k<7300,
     oz ao (qU (af3 q k))≤bound q k) :
   oz ao (aTt B) ≤
     ∑ q∈cy (B+1),∑ k∈cy 7300,bound q k := by
 have hr :=(Kc (cen B)).trans (b3b (pairs B))
 refine hr.trans ?_
 rw [← Finset.sum_product']
 apply qM
 intro i hi
 have hp:=Finset.mem_product.mp hi
 exact h i.1 (Finset.mem_range.mp hp.1) i.2 (Finset.mem_range.mp hp.2)
end
end Rj
end
section
namespace Rj
noncomputable section
open aR MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 600000
instance gRv (q:ℕ) (g:ℤ) :uW ao (aqz q g) := by
 apply restrictSupport_finite
 refine (Un (fun _:Fin 3=>1)
  (by simp) (iO q)).subset ?_
 intro e he
 exact (show e.weight (fun _=>1)=iO q from he.1).le
private def jO (q:ℕ) :ℕ:=q - iO q
private def Ra (q:ℕ) (e :Exp) :adf :=
 Finsupp.equivFunOnFinite.symm ![e (some 0) - jO q,e (some 1),e (some 2)]
private theorem bhx (e :Exp) :
  e.weight BU=e (some 0)+e (some 1)+e (some 2) := by
 simp [Bf ,NI,qG,BU,vk]
private theorem bhy (e :Exp) :
  e.weight th=e (some 1)+2*e (some 2) := by
 simp [Bf ,NI,qG,th,
  sI,yB]
private theorem buZ {q k :ℕ} (e :TO q k) :
  jO q≤e.val (some 0) := by
 have hd:=e.property.2.1
 have hj:=e.property.1.2.1
 rw [bhx] at hd
 rw [bhy] at hj
 simp only [jO,iO]
 omega
private theorem cqD {q k :ℕ} (e :TO q k) :
  Ra q e∈cbQ q (aU k) := by
 have hd:=e.property.2.1
 have hj:=e.property.1.2.1
 have ht:=e.property.1.2.2
 have hg:=e.property.2.2
 have ha :=buZ e
 rw [bhx] at hd
 rw [bhy] at hj hg
 change (Ra q e).weight (fun _=>1)=iO q ∧
  -offset k≤((Ra q e).weight Eg :ℤ) ∧
  (Ra q e).weight Eg≤2300∧(Ra q e) 2≤1150
 simp [Bf ,qG,Ra,sI,yB]
 simp only [jO,iO] at *
 omega
private def bpl (q k :ℕ) (e :TO q k) :
   aqz q (aU k) :=
 ⟨ov (Ra q e) 1,
   (monomial_mem_restrictSupport ao).mpr (Dw (cqD e))⟩
private def encode (q k :ℕ) :Block q k →ₗ[ao] aqz q (aU k) :=
 (Au ao (TO q k)).constr ao (bpl q k)
private theorem b1y (q k :ℕ) (e :TO q k) :
  ((encode q k (Au ao (TO q k) e)) :lK) =
    ov (Ra q e) 1 :=
 nq Subtype.val
  ((Au ao (TO q k)).constr_basis ao (bpl q k) e)
local notation "T" => (MvPolynomial.X (none :Option (Fin 3)) :Flat)
private def y (j:Fin 3) :Flat :=lz (some j)
private def NH :Fin 3→Flat := ![y 0,T*y 1,T^2*y 2]
private theorem dcj :
  pC NH (acw 0)=La (some 0) := by
 simp [acw,NH,La,y]
private theorem gmr :pC NH (acw 1)=T*y 1 := by
 simp [acw,NH]
private theorem gms :pC NH (acw 2)=T^2*y 2 := by
 simp [acw,NH]
private theorem blU {σ τ:Type*} [yL σ]
  (f :σ→lV τ ao) (e :σ →₀ ℕ) :
  pC f (ov e 1) = ∏ j,f j^e j:= by
 rw [bind₁_monomial,C_1,sH]
 exact Cy e (fun j n=>f j^n) (fun _=>y5 _)
private theorem a8I (e :Exp) :
   J6 (ov e 1)=T^e none *
     (La (some 0)^e (some 0)*y 1^e (some 1)*y 2^e (some 2)) := by
 rw [J6,blU,Rm,Kz]
 simp [La,y,z8]
private theorem cqE (q:ℕ) (e :Exp) :
    pC NH (pC acw (ov (Ra q e) 1)) =
      La (some 0)^(e (some 0) - jO q) *
        (T*y 1)^e (some 1)*(T^2*y 2)^e (some 2) := by
  rw [bind₁_bind₁,blU,Kz]
  simp [dcj,gmr,gms,Ra,z8]
private theorem cpw (q k :ℕ) (e :TO q k) :
    T^(-offset k).toNat*J6 (ov e.val 1) =
      T^(aU k).toNat*La (some 0)^jO q *
        pC NH (pC acw (ov (Ra q e) 1)) := by
  have hi:=e.property.2.2
  rw [bhy] at hi
  have ht: (-offset k).toNat+e.val none =
      (aU k).toNat+e.val (some 1)+2*e.val (some 2) := by omega
  have ha :jO q+(e.val (some 0) - jO q)=e.val (some 0) := by
    have :=buZ e
    omega
  have hT:T^(-offset k).toNat*T^e.val none =
      T^(aU k).toNat*T^e.val (some 1)*T^(2*e.val (some 2)) := by
    simpa only [pow_add] using nq (T ^ ·) ht
  have hA:La (some 0)^e.val (some 0) =
      La (some 0)^jO q*La (some 0)^(e.val (some 0) - jO q) := by
    rw [← pow_add,ha]
  rw [a8I,cqE]
  simp only [mul_pow,← pow_mul]
  calc
    _=(T^(-offset k).toNat*T^e.val none) *
        (La (some 0)^e.val (some 0)*y 1^e.val (some 1)*y 2^e.val (some 2)) := by
      ring
    _ = _:= by rw [hT,hA]; ring
private theorem gqH (q k :ℕ) (p:Block q k) :
    T^(-offset k).toNat*J6 (p:Flat) =
      T^(aU k).toNat*La (some 0)^jO q *
        pC NH (pC acw (encode q k p:lK)) := by
  let l:=(Vl ao (T^(-offset k).toNat)).comp
    (J6.toLinearMap.comp (Block q k).subtype)
  let r :=(Vl ao (T^(aU k).toNat*La (some 0)^jO q)).comp
    ((pC NH).toLinearMap.comp ((pC acw).toLinearMap.comp
      ((aqz q (aU k)).subtype.comp (encode q k))))
  have h:l=r := by
    apply (Au ao (TO q k)).ext
    intro e
    change T^(-offset k).toNat *
      J6 (↑(Au ao (TO q k) e) :Flat) =
        T^(aU k).toNat*La (some 0)^jO q *
          pC NH (pC acw
            (↑(encode q k (Au ao (TO q k) e)) :lK))
    rw [b1y,coe_basisRestrictSupport_apply]
    exact cpw q k e
  exact LinearMap.congr_fun h p
private def a6A:Fin 3→ℕ := ![2,0,1]
private def aid (j:Fin 3) :ℕ:=a6A j+1
private theorem cwS (e :adf) :
  e.weight aid=e.weight a6A+e.weight (fun _=>1) := by
 simp [Bf ,aid,sI,FK,zk]
private theorem aQH (n:ℕ) :T^n∈t9 oH n:= by
 simpa using pow_mem_restrictWeightedOrder
  (IT (R:=ao) oH (none :Option (Fin 3))
    (m:=1) uh) n
private theorem bv2 (j:Fin 3) :
   NH j∈t9 oH (aid j) := by
 have hy (j:Fin 3) :y j∈t9 oH 0:= by simp
 have he :y 0∈t9 oH 3:=IT _ _ uh
 fin_cases j
 · simpa [NH,aid,a6A] using he
 · simpa [NH,aid,a6A] using G2
    (aQH 1) (hy 1)
 · simpa [NH,aid,a6A] using G2
    (aQH 2) (hy 2)
private theorem cva :La (some 0)∈t9 oH 1 := by
 have h (j:Fin 3) :NH j∈t9 oH 1 :=
  restrictWeightedOrder_anti _ (G5 1 (a6A j)) (bv2 j)
 rw [← dcj]
 simp only [acw,t4 ,qy ,zS ,bind₁_X_right]
 exact Submodule.sub_mem _ (Sd _ (h 0) (h 1)) (h 2)
private theorem caB {n m:ℕ} {p:Flat}
  (h:T^n*p∈t9 oH (m+n)) :
  p∈t9 oH m:= by
 rw [TH] at h
 intro e he
 have hh:=mem_restrictWeightedOrder.mp h (p7 none n+e) (by
  rw [G8 ,coeff_monomial_mul,sH]
  exact MvPolynomial.mem_support_iff.mp he)
 change m≤e.weight oH
 simp only [qy ,Qx ,oH,Option.elim_none,
  sI,mul_one] at hh ⊢
 omega
private theorem eLE (j:Fin 3) :
   (acw j).IsWeightedHomogeneous (fun _:Fin 3=>1) 1 := by
 have h (i:Fin 3) :=isWeightedHomogeneous_X ao (fun _:Fin 3=>(1 :ℕ)) i
 by_cases hj:j=0
 · subst j
   simpa [acw] using ((h 0).add (h 1)).sub (h 2)
 · simpa [acw,hj] using h j
private theorem brp (q k :ℕ) :
   uJ ((aPi q (aU k)).comp (encode q k)) ≤
     uJ (af3 q k) := by
 intro p hp
 let L:aqz q (aU k) :=encode q k p
 let S:lK:=pC acw (L:lK)
 let cut:=(Ic q (aU k)).toNat
 have hz :GY a6A cut S=0:=LinearMap.mem_ker.mp hp
 have hcontact :=(G7 _ _ _).mp hz
 have hgrade : (L:lK).IsWeightedHomogeneous (fun _:Fin 3=>1) (iO q) :=
   fun e he=>(L.property (mem_support_iff.mpr he)).1
 have hS:S.IsWeightedHomogeneous (fun _:Fin 3=>1) (iO q) :=
   hgrade.bind₁ eLE
 have hscaled:S∈t9 aid (cut+iO q) := by
   intro e he
   have hg:=hS (mem_support_iff.mp he)
   have hc:=mem_restrictWeightedOrder.mp hcontact e he
   change cut+iO q≤e.weight aid
   rw [cwS,hg]
   exact Te hc _
 have hprod:=G2
   (G2 (aQH (aU k).toNat)
     (by simpa using pow_mem_restrictWeightedOrder cva (jO q)))
   (SW bv2 hscaled)
 have hbound:5000+(-offset k).toNat ≤
     (aU k).toNat+jO q+(cut+iO q) := by
   change 5000+(-offset k).toNat≤(aU k).toNat+jO q +
     ((5000-(q:ℤ) - aU k).toNat+iO q)
   simp only [jO,iO]
   omega
 have hshift:T^(-offset k).toNat*J6 (p:Flat) ∈
     t9 oH (5000+(-offset k).toNat) := by
   rw [gqH]
   exact restrictWeightedOrder_anti _ hbound hprod
 apply LinearMap.mem_ker.mpr
 exact (G7 _ _ _).mpr (caB hshift)
theorem fTp (q k :ℕ) :
   oz ao (qU (af3 q k)) ≤
     oz ao (qU (aPi q (aU k))) := by
 let f :=(aPi q (aU k)).comp (encode q k)
 have hker :=Kc (brp q k)
 change oz ao (uJ f) ≤
   oz ao (uJ (af3 q k)) at hker
 have h₁:=f.finrank_range_add_finrank_ker
 have h₂:=(af3 q k).finrank_range_add_finrank_ker
 exact (show oz ao (qU (af3 q k)) ≤
     oz ao (qU f) by omega).trans
   (Kc (LinearMap.range_comp_le_range _ _))
end
end Rj
end
section
namespace Rj
noncomputable section
open aR jA NR
open ReedSolomon.HiddenDerivative
open MvPolynomial
open scoped Polynomial BigOperators
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
private abbrev aRP:=lV (Fin 3) ao[X]
private def AV:jK ≃ₐ[ao[X]] aRP[X] :=
 xW _ _
private def Ky :Flat ≃ₐ[ao] aRP:=optionEquivRight _ _
private def Bg (n:ℕ) :jK →ₗ[ao] aRP :=
 (F9 aRP n).restrictScalars ao ∘ₗ AV.toLinearMap.restrictScalars ao
private def aob (n:ℕ) :jK →ₗ[ao] Flat :=
 Ky.symm.toLinearMap ∘ₗ Bg n
private theorem dcD (n:ℕ) (F:jK) (e :adf) :
  (Bg n F).coeff e=F.coeff (e.optionElim n) :=
 IU ao[X] F n e
private theorem ec6 (n:ℕ) (F:jK) (e :Exp) :
  (aob n F).coeff e=(F.coeff (e.some.optionElim n)).coeff (e none) := by
 have h:=optionEquivRight_coeff_coeff (aob n F) e.some (e none)
 rw [LR] at h
 change ((Ky (Ky.symm (Bg n F))).coeff e.some).coeff (e none)= _ at h
 rw [Pj,dcD] at h
 exact h.symm
private theorem dMt {b:Bank} {F:jK} (hF:Jn b.box F) (n:ℕ) :
   aob n F∈apR b.box.b:= by
 intro e he
 change e∈(aob n F).support at he
 have hc:=MvPolynomial.mem_support_iff.mp he
 rw [ec6] at hc
 have hs :e.some.optionElim n∈F.support :=MvPolynomial.mem_support_iff.mpr
   (fun h=>hc (by rw [h,zc]))
 have hb:=(vj BU hs).trans hF.1
 have hj:=(vj th hs).trans hF.2.1
 have ht:=(degreeOf_le_iff.mp hF.2.2.1) _ hs
 have heq :e.some.optionElim (e none)=e :=LR e
 change e.weight BU≤b.box.b∧e.weight th≤2300 ∧
   e (some 2)≤1150
 have hg (n:ℕ) : (e.some.optionElim n).weight BU=e.some.weight (fun _=>1) := by
   unfold BU
   rw [GR,vZ,qJ]
 have hi (n:ℕ) : (e.some.optionElim n).weight th=e.some.weight Fin.val := by
   unfold th
   rw [GR,vZ,qJ]
 have hj' : b.box.j=2300:= by cases b <;> rfl
 have ht' : b.box.t=1150:= by cases b <;> rfl
 rw [hj'] at hj
 rw [ht'] at ht
 rw [hg] at hb
 rw [hi] at hj
 refine ⟨?_,?_,?_⟩
 · exact (nq (z7 BU) heq).symm.le.trans ((hg (e none)).le.trans hb)
 · exact (nq (z7 th) heq).symm.le.trans ((hi (e none)).le.trans hj)
 · simpa using ht
private theorem gnX {b:Bank} {F:jK} (hF:Jn b.box F)
  {n:ℕ} (hn:70000<n) :
  Bg n F=0:= by
 have hdeg: (AV F).natDegree≤70000:= by
  simpa only [AV,SL,gY] using hF.2.2.2
 exact Kv (hdeg.trans_lt hn)
private def normalize (x v :ao) :Flat →ₐ[ao] Flat :=
 globalPointTranslation (d:=2) x v
private theorem eFo {B:ℕ} {Q:Flat} (h:Q∈apR B) (x v :ao) :
    normalize x v Q∈apR B:= by
  have preserve (w:Option (Fin 3)→ℕ) (a :ℕ)
      (hQ : ∀ e∈Q.support,e.weight w≤a) :
      ∀ e∈(normalize x v Q).support,e.weight w≤a :=
    mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (C9 _) (C9 _)
        x v (mem_restrictWeightAtMost.mpr hQ))
  have htop (e :Exp) :e.weight topWeight=e (some 2) := by
    conv_lhs=>rw [← LR e]
    unfold topWeight
    rw [GR,vZ,qJ,
      Finsupp.weight_single_one_apply]
    simp
  intro e he
  exact ⟨preserve BU B (fun t ht=>(h ht).1) e he,
    preserve th 2300 (fun t ht=>(h ht).2.1) e he,
    htop e ▸ preserve topWeight 1150 (fun t ht=>(htop t).symm ▸ (h ht).2.2) e he⟩
private def bbX {ι:Type*} (x v :ao)
   (y :Fin 3→lV ι ao[X]) (j:Fin 3) :lV ι ao[X] :=
 if j=0 then
   y 0+C (lI v) -
     C (lI x-Polynomial.X)*y 1 -
     C ((lI x-Polynomial.X)^2)*y 2
 else y j
private def aIg (x v :ao) :aRP →ₐ[ao[X]] aRP :=
 aeval (bbX x v lz)
private def a4r (x v :ao) :jK →ₐ[ao[X]] jK :=
 aeval (fun j=>j.elim (lz none)
  (bbX x v (fun i=>lz (some i))))
private theorem eev (x v :ao) (F:jK) :
  a4r x v F=aCk x v F:= by
 rw [a4r,aeval_def,MvPolynomial.algebraMap_eq,aCk]
 apply nq (fun a=>KI C a F)
 funext j
 cases j <;> simp [bbX]
private theorem goE (x v :ao) :
    AV.toAlgHom.comp (a4r x v) =
      (NX (aIg x v)).comp AV.toAlgHom:= by
  apply algHom_ext
  intro j
  cases j with
  | none=>simp [AV,a4r,optionEquivLeft_X_none]
  | some j =>
    by_cases hj:j=0
    · subst j
      simp [AV,a4r,aIg,bbX,Gn,
        zh]
    · simp [AV,a4r,aIg,bbX,hj,Gn]
private theorem gnV (x v :ao) (F:jK) (n:ℕ) :
   Bg n (aCk x v F)=aIg x v (Bg n F) := by
 have h:=oy (goE x v) F
 have he :AV (a4r x v F) =
     NX (aIg x v) (AV F) :=h
 rw [eev] at he
 change (AV (aCk x v F)).coeff n=aIg x v ((AV F).coeff n)
 rw [he,Polynomial.coeff_mapAlgHom_apply]
private def bxA (x :ao) :aRP →ₐ[ao] aRP :=
 LQ (UZ x)
private theorem eFp (x v :ao) :
    Ky.toAlgHom.comp (J6.comp (normalize x v)) =
      (bxA x).comp (((aIg x v).restrictScalars ao).comp Ky.toAlgHom) := by
  apply algHom_ext
  intro j
  have h₁:globalPointTranslation (d:=2) x v (lz (some 1)) =
      lz (some 1) :=globalPointTranslation_Y_succ x v (0:Fin 2)
  have h₂:globalPointTranslation (d:=2) x v (lz (some 2)) =
      lz (some 2) :=globalPointTranslation_Y_succ x v (1 :Fin 2)
  cases j with
  | none =>
    simp [normalize,J6,Ky,bxA,La,aIg,NW,wY]
  | some j =>
    fin_cases j <;>
      (simp [normalize,J6,Ky,bxA,La,aIg,bbX,
        NW,Kl,h₁,h₂]; try ring)
private theorem eE1 (x v :ao) (F:jK) (n:ℕ) (e :adf) :
   (Ky (J6 (normalize x v (aob n F)))).coeff e =
     zi x ((aCk x v F).coeff (e.optionElim n)) := by
 have h:=oy (eFp x v) (aob n F)
 change Ky (J6 (normalize x v (aob n F))) =
   bxA x (aIg x v (Ky (Ky.symm (Bg n F)))) at h
 rw [Pj,← gnV] at h
 rw [h,bxA,mapAlgHom_apply,Gr,dcD]
 rfl
private theorem dPj (e :adf) (i:ℕ) :
  (e.optionElim i).weight oH=i+3*e 0:= by
 unfold oH
 rw [GR,Finsupp.weight_single_index,sH,
  sI,yB (e 0)]
private theorem cZ1 {b:Bank} {x v :ao} {F:jK}
   (hcap:Jn b.box F) (h : ∀ n:Fin 70001,origin (normalize x v (aob n F))=0) :
   F∈ays x v := by
 apply (bsz x v F).mpr
 intro e
 let P:=(aCk x v F).coeff (e.some.optionElim (e none))
 let E :=Polynomial.taylorEquiv x
 have hE :E ((lJ-Polynomial.C x)^(5000-3*e (some 0))) =
     lJ ^(5000-3*e (some 0)) := by
   have hX:E (lJ-Polynomial.C x)=Polynomial.X:= by
     rw [zS]
     change zi x lJ-Polynomial.taylor x (lI x)= _
     simp
   rw [xI,hX]
 have hP:P=(aCk x v F).coeff e := by simp [P]
 rw [← hP,← map_dvd_iff E,hE,II]
 intro i hi
 have hcoeff :E P =
     (Ky (J6 (normalize x v (aob (e none) F)))).coeff e.some :=
   (eE1 x v F (e none) e.some).symm
 rw [hcoeff]
 change ((optionEquivRight ao (Fin 3) _).coeff e.some).coeff i=0
 rw [optionEquivRight_coeff_coeff]
 by_cases hn:e none<70001
 · have hz :=nq (fun Q:Flat=>Q.coeff (e.some.optionElim i)) (h ⟨e none,hn⟩)
   change (GY oH 5000
     (J6 (normalize x v (aob (e none) F)))).coeff (e.some.optionElim i)=0 at hz
   have hlt: (e.some.optionElim i).weight oH<5000:= by
     rw [dPj]
     change i+3*e (some 0)<5000
     omega
   rw [coeff_weightedTruncation] at hz
   simpa only [hlt,t4] using hz
 · have hz :=gnX hcap (n:=e none) (by omega)
   have hz' : aob (e none) F=0:= by
     change Ky.symm (Bg (e none) F)=0
     rw [hz,xu ]
   simp [hz']
private def c1y (b:Bank) (x v :ao) (V:u8 ao jK)
   (hcap : ∀ F∈V,Jn b.box F) (n:Fin 70001) :V →ₗ[ao] apR b.box.b :=
 ((normalize x v).toLinearMap ∘ₗ aob n ∘ₗ V.subtype).codRestrict _
   (fun F=>eFo (dMt (hcap F F.2) n) x v)
end
end Rj
end
section
namespace Rj
noncomputable section
open aR jA NR
open scoped BigOperators
def c1 :Prop :=
  ∀ q<6821,∀ k<7300,
    (oz ao (aqz q (aU k)) :ℤ)≤Bb q (aU k)
def c2 :Prop :=
  ∀ q<6821,∀ k<7300,∀ p:kJ,
    m5 (K6 q p) (D8 q (aU k) p) ≤
      (oz ao (uJ (aPi q (aU k))) :ℤ)
def c3:Prop :=
  ∃ p:ℕ→ℕ→kJ,
    (∑ j∈cy 1151,Xi p j)≤1054250623200
def c4 :Prop :=
  ∃ p:ℕ→ℕ→kJ,
    (∑ j∈cy 1149,Xi p (1151+j))≤4082300934025
def c5:Prop :=
  ∃ p:ℕ→ℕ→kJ,
    (∑ j∈cy 2700,Xi p (2300+j))≤5196036704622
def c6:Prop :=
  ∃ p:ℕ→ℕ→kJ,
    (∑ j∈cy 1790,Xi p (5000+j))≤364983426528
private theorem c4g (h1 :c1) (h2 :c2) {q k :ℕ} (hq:q<6821) (hk :k<7300)
    (p:kJ) :
    oz ao (qU (aPi q (aU k)))≤xR q (aU k) p:= by
  let f :=aPi q (aU k)
  by_cases hcut:Ic q (aU k)≤0
  · have hz :f=0:= by
      ext L:1
      change GY (![2,0,1] :Fin 3→ℕ)
        (Ic q (aU k)).toNat (pC acw (L:lK))=0
      apply (G7 _ _ _).mpr
      simp [N0 hcut]
    change oz ao (qU f)≤_
    simp [hz,xR,hcut]
  have hdim:=f.finrank_range_add_finrank_ker
  have hcols :=h1 q hq k hk
  have hshift:=h2 q hq k hk p
  have hbase :=h2 q hq k hk (fun _=>0)
  have hdeg:K6 q (fun _=>0)=iO q:= by simp [K6]
  have hflag:D8 q (aU k) (fun _=>0)=pT q (aU k) := by
    funext i
    simp only [D8,Nat.cast_zero,vZ,Finset.sum_const_zero,wR]
  rw [hdeg,hflag] at hbase
  change _≤(oz ao (uJ f) :ℤ) at hshift hbase
  have hlower :=vH (Ea (oz ao (uJ f)))
    (vH hbase hshift)
  change oz ao (qU f)≤_
  unfold xR
  simp only [hcut,t5]
  have hbound: (oz ao (qU f) :ℤ) ≤
      Bb q (aU k) -
        max 0 (max (m5 (iO q) (pT q (aU k)))
          (m5 (K6 q p) (D8 q (aU k) p))) := by
    omega
  simpa using Hw hbound
private theorem bH8 {a m n r s :ℕ}
   (h₁ : ∃ p:ℕ→ℕ→kJ,(∑ j∈cy m,Xi p (a+j))≤ r)
   (h₂ : ∃ p:ℕ→ℕ→kJ,(∑ j∈cy n,Xi p (a+m+j))≤ s) :
   ∃ p:ℕ→ℕ→kJ,(∑ j∈cy (m+n),Xi p (a+j))≤ r+s := by
 obtain ⟨p₁,hp₁⟩:=h₁
 obtain ⟨p₂,hp₂⟩:=h₂
 let p:ℕ→ℕ→kJ:= fun q=>if q<a+m then p₁ q else p₂ q
 have hfirst: (∑ j∈cy m,Xi p (a+j)) =
     ∑ j∈cy m,Xi p₁ (a+j) := by
   apply n5 rfl
   intro j hj
   have h:=Nat.add_lt_add_left (Finset.mem_range.mp hj) a
   simp only [ Xi,p,h,t4]
 have hsecond: (∑ j∈cy n,Xi p (a+m+j)) =
     ∑ j∈cy n,Xi p₂ (a+m+j) := by
   apply n5 rfl
   intro j _
   have h : ¬ a+m+j<a+m:= by omega
   simp only [ Xi,p,h,t5]
 refine ⟨p,?_⟩
 rw [Df ,hfirst]
 simp only [← Nat.add_assoc]
 rw [hsecond]
 exact Nat.add_le_add hp₁ hp₂
private theorem aaH (h3:c3) (h4 :c4) (h5:c5) (h6:c6) (b:Bank) :
   ∃ p:ℕ→ℕ→kJ,(∑ q∈cy (b.box.b+1),Xi p q)≤b.avF:= by
 unfold c3 at h3
 have h34 :=bH8 (a :=0) (m:=1151) (n:=1149)
   (r :=1054250623200) (s :=4082300934025) (by simpa only [Ee] using h3) h4
 have h345:=bH8 (m:=2300) (n:=2700) (a :=0) h34 h5
 have h3456:=bH8 (m:=5000) (n:=1790) (a :=0) h345 h6
 cases b with
 | first =>
   change ∃ p:ℕ→ℕ→kJ,(∑ q∈cy 6790,Xi p q)≤10697571688375
   simpa only [Ee,Nat.reduceAdd] using h3456
 | second =>
   have hAll:=bH8 (m:=6790) (n:=31) (a :=0) h3456 bxv
   change ∃ p:ℕ→ℕ→kJ,(∑ q∈cy 6821,Xi p q)≤10697783317215
   simpa only [Ee,Nat.reduceAdd] using hAll
end
end Rj
end
section
namespace Rk
noncomputable section
open K1 aR jA
open scoped Polynomial BigOperators
def JX {R:Type*} [Aa R] (z :R) :
    VP R →+* lV (Fin 3) R :=
  pL c9
    (fun i=>i.elim (c9 z) lz)
def az5 (H res :ao[X]) :af 3 →+* af 3 :=
  pL c9 (fun i =>
    c9 (jet res i) +
     ∑ j:Fin 3,if j.val≤ i.val then
       c9 (oK (i.val - j.val) H)*lz j
     else 0)
def aPU (H res :ao[X]) (z :ao) (F:jK) :af 3 :=
 az5 H res (JX (lI z) F)
def a04 (t:ℕ) (Q:af 3) :Prop :=
  ∀ m∈Q.support,(Q.coeff m).natDegree +
    m.sum (fun j e=>(131071 - j.val)*e)≤t
def bkY (m:ℕ) (w:I→K) (H res :ao[X]) (Q:af 3) :Prop :=
  ∀ i (T:ao[X]),(H*T+res).eval (qz (node i))=qz (w i) →
    (lJ-Polynomial.C (qz (node i)))^m∣cK Q T
def Yd (H :ao[X]) (i:ℕ) (F:jK) :jK :=
 c9 (H^(3*i))*aox (p7 none i) F
end
end Rk
end
section
namespace Rk
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 12000
open K1 aR jA Polynomial
open scoped Polynomial BigOperators
private def bDj (S:ao[X]) (x v :ao) :ao[X] :=
 S-Polynomial.C v+(lI x-Polynomial.X)*oK 1 S+(lI x-Polynomial.X)^2*oK 2 S
private theorem dPg (S:ao[X]) (x v :ao) (h:S.eval x=v) :
  (lJ-Polynomial.C x)^3∣bDj S x v := by
 have ht:=map_dvd (UZ (-x)).toRingHom
  (X_pow_succ_dvd_taylor_sub_C_sub_movingHasseSum_of_eval_eq 2 h)
 change zi (-x) ((lJ:ao[X])^3) ∣
  zi (-x) (zi x S-Polynomial.C v - movingHasseSum x S 2) at ht
 simp only [Kh,Pv,LinearMap.map_neg,Kl,taylor_taylor,
  neg_add_cancel,taylor_zero,movingHasseSum,t3 ,S2 ,
  qJ,taylor_mul,NW,y5 ,C_1,sH,Dz ,C_neg] at ht
 convert ht using 1 <;> simp [bDj,Kh] <;> ring
theorem cV4 (H res T:ao[X]) (i:Fin 3) :
    jet (H*T+res) i=jet res i +
      ∑ j:Fin 3,if j.val≤ i.val then
        oK (i.val - j.val) H*jet T j else 0:= by
  have hj :
      ∑ j:Fin 3,(if j.val≤ i.val then
        oK (i.val - j.val) H*jet T j else 0) =
      oK i.val (H*T) := by
    rw [hasseDeriv_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    fin_cases i <;>
      norm_num [qG,t3 ,jet] <;> ring
  rw [hj]
  change oK i.val (H*T+res)=oK i.val res+hasseDeriv i.val (H*T)
  rw [Pv,wY]
private theorem d2J (H res T:ao[X]) (F:af 3) :
    cK (az5 H res F) T=cK F (H*T+res) := by
  have heval : (pz (jet T)).comp (az5 H res) =
      pz (jet (H*T+res)) := by
    apply pQ
    · intro c
      simp [az5]
    · intro i
      simp only [qm,az5,Fa ,qy ,
        Pc,p9,apply_ite,oq,MvPolynomial.eval_X,xu]
      exact (cV4 H res T i).symm
  exact oy heval F
private theorem eK2 (F:jK) (m:ℕ) (x v z :ao) (S:ao[X])
    (hF : ∀ a :mA →₀ ℕ,(lJ-Polynomial.C x)^(m-3*a (some 0)) ∣
      (aCk x v F).coeff a) (hS:S.eval x=v) :
    (lJ-Polynomial.C x)^m∣cK (JX (lI z) F) S:= by
  classical
  let d:ao[X] :=lJ-Polynomial.C x
  let e :=bDj S x v
  let g:mA→ao[X] := fun j=>j.elim (lI z) (fun k=>if k=0 then e else jet S k)
  let ev :=pz g
  let back :jK →+* jK:=pL c9 (fun j =>
    if j=some 0 then
      lz (some 0)+MvPolynomial.C (lI v) -
        c9 (lI x-Polynomial.X)*lz (some 1) -
        c9 ((lI x-Polynomial.X)^2)*lz (some 2)
    else lz j)
  have hcomp:ev.comp back=(pz (jet S)).comp (JX (lI z)) := by
    apply pQ
    · intro c
      simp [ev,back,JX]
    · intro j
      cases j with
      | none=>simp [ev,back,JX,g]
      | some j =>
        by_cases hj:j=0
        · subst j
          simp [ev,back,JX,g,e,bDj,jet,JK]
          ring
        · simp [ev,back,JX,g,hj]
  change d^m∣(pz (jet S)) (JX (lI z) F)
  have heval :ev (back F)=pz (jet S) (JX (lI z) F) :=
    oy hcomp F
  rw [← heval]
  set B:=back F with hB
  rw [B.as_sum,p9]
  apply Finset.dvd_sum
  intro a _
  rw [MvPolynomial.eval_monomial]
  have hcoeff :d^(m-3*a (some 0))∣B.coeff a :=hF a
  have he :d^3∣g (some 0) := by
    simpa [d,g,e] using dPg S x v hS
  have hprod:d^(3*a (some 0))∣a.prod (fun j n=>g j^n) := by
    rw [pow_mul,Cy _ _ (fun _=>y5 _)]
    exact (pow_dvd_pow_of_dvd he _).trans
      (Finset.dvd_prod_of_mem _ (Lf (some (0:Fin 3))))
  have hle :m≤(m-3*a (some 0))+3*a (some 0) := by omega
  exact (pow_dvd_pow d hle).trans (by rw [pow_add]; exact mul_dvd_mul hcoeff hprod)
theorem c6X (m:ℕ) (w:I→K) (H res :ao[X]) (z :ao) (r :ℕ)
    (F:jK) (Q:af 3) (hnodes : ∀ i,H.eval (qz (node i))≠0)
    (hF : ∀ i (a :mA →₀ ℕ),
      (lJ-Polynomial.C (qz (node i)))^(m-3*a (some 0)) ∣
        (aCk (qz (node i)) (qz (w i)) F).coeff a)
    (hQ:aPU H res z F=c9 (H^r)*Q) :
    bkY m w H res Q:= by
  intro i T hT
  have hd:qx (lJ-Polynomial.C (qz (node i))) H :=
    (prime_X_sub_C _).coprime_iff_not_dvd.mpr (by
      rw [dvd_iff_isRoot]
      exact hnodes i)
  have hh:=eK2 F m _ _ z _ (hF i) hT
  rw [← d2J,← aPU,hQ] at hh
  apply (hd.pow (m:=m) (n:=r)).dvd_of_dvd_mul_left
  simpa only [cK,oq,Pc] using hh
end
end Rk
end
section
namespace bzs
open Rj
open scoped BigOperators
set_option maxHeartbeats 900000
def quarter (w:ℤ) :ℤ:=w^2/4
private def cost (w:ℤ) :ℤ:=quarter (w+1)
private theorem bye (w:ℤ) :2*sG w=w*(w+1) := by
 unfold sG
 apply FR
 rcases (show w % 2=0∨w % 2=1 by omega) with h | h
 · have hw:w=2*(w/2) := by omega
   exact Vz  (by rw [hw]; exact VH  _ _) _
 · have hw:w+1=2*(w/2+1) := by omega
   exact VC  (by rw [hw]; exact VH  _ _) _
theorem bKV (w:ℤ) :4*quarter w=w^2 - w % 2 := by
 unfold quarter
 rcases (show w % 2=0∨w % 2=1 by omega) with h | h
 · have hw:w=2*(w/2) := by omega
   have he :w^2=4*(w/2)^2 := by
     calc _=(2*(w/2))^2 :=congrArg (· ^ 2) hw
          _ = _:= by ring
   rw [he,h]
   omega
 · have hw:w=2*(w/2)+1 := by omega
   have he :w^2=4*((w/2)^2+w/2)+1 := by
     calc _=(2*(w/2)+1)^2 :=congrArg (· ^ 2) hw
          _ = _:= by ring
   rw [he,h]
   omega
private theorem aM2 (w:ℤ) :4*cost w=w^2+2*w+w % 2 := by
 unfold cost
 rw [bKV]
 have h: (w+1) % 2+w % 2=1 := by omega
 nlinarith only [h]
private theorem bnA {a w:ℤ} (ha :a≤(w+1)/2) (hw:0≤w) :
   yC ⟨a,w⟩=cost w:= by
 have hu:0≤(w+1)/2 := by omega
 have huv : (w+1)/2≤w:= by omega
 have h: (w+1)/2=w/2+w % 2 := by omega
 have h' : w-(w+1)/2=w/2 := by omega
 unfold yC
 simp only [oZ ha,oZ hu,oZ huv]
 rw [h',h]
 have h₁:=bye (w/2+w % 2)
 have h₂:=bye (w/2)
 have h₃:=aM2 w
 rcases (show w % 2=0∨w % 2=1 by omega) with he | he
 · have hw:w=2*(w/2) := by omega
   rw [he] at h₁ h₃ ⊢
   conv at h₃=>rhs; rw [hw]
   nlinarith only [h₁,h₂,h₃]
 · have hw:w=2*(w/2)+1 := by omega
   rw [he] at h₁ h₃ ⊢
   conv at h₃=>rhs; rw [hw]
   nlinarith only [h₁,h₂,h₃]
private theorem ew7 (k a t:ℤ) (ha :a=0∨t=a+2*k+1) :
    sG (2301 - 2*a) - cost (2300 - k - 2*a) - cost (2300 - 2*a) -
        cost (t - a) =
      sG 2301 - cost (2300 - k) - cost 2300 - cost t+quarter a := by
  rcases ha with rfl | ht
  · simp [quarter]
  have hp: (2300 - k - 2*a) % 2=(2300 - k) % 2 := by omega
  have hq: (2300 - 2*a) % 2=0:= by omega
  have ho: (t - a) % 2=1 := by omega
  have hs :t % 2=1-a % 2 := by omega
  have hTP:=bye (2301 - 2*a)
  have hT:=bye 2301
  have hPP:=aM2 (2300 - k - 2*a)
  have hP:=aM2 (2300 - k)
  have hQP:=aM2 (2300 - 2*a)
  have hQ:=aM2 2300
  have hOP:=aM2 (t - a)
  have hO:=aM2 t
  have hA:=bKV a
  rw [hp] at hPP
  rw [hq] at hQP
  rw [ho] at hOP
  rw [hs] at hO
  norm_num only [Int.reduceMod] at hQ
  rw [ht] at hOP hO ⊢
  nlinarith only [hTP,hT,hPP,hP,hQP,hQ,hOP,hO,hA]
private theorem dOU (u:ℤ) :
   sG (6*u - 1) - cost (4*u - 1) - cost (6*u - 2) -
     cost (4*u - 1)=u^2 := by
 have hT:=bye (6*u - 1)
 have hP:=aM2 (4*u - 1)
 have hQ:=aM2 (6*u - 2)
 rw [show (4*u - 1) % 2=1 by omega] at hP
 rw [show (6*u - 2) % 2=0 by omega] at hQ
 nlinarith only [hT,hP,hQ]
def columns (k :ℕ) :ℤ:=1324801 - quarter (2301-(k :ℤ))
def adX (r k :ℕ) :ℤ:=(r :ℤ) - 1 - 3*k
def ahr (r k :ℕ) :ℤ:=2*(r :ℤ) - 2301 - 3*k
def aq3 (r k :ℕ) :ℤ:=2*(k :ℤ)+1151 - r
def powers (r k :ℕ) (i:Fin 6) :ℕ :=
 if i=0∨i=3 then (adX r k).toNat
 else if i=5 then (ahr r k).toNat else 0
def aWJ (r k :ℕ) :ℤ :=
  if 0<ahr r k then
    columns k-(max 0 (aq3 r k))^2
  else quarter ((r :ℤ) - k+1) - quarter (max 0 (adX r k))
private theorem dNC {q k :ℕ} (hq:5000≤q) (hk :k<2300) :
  Bb q (aU k)=columns k := by
 have hd:iO q=2300:=vl (by omega)
 have harg :min (2300:ℤ) (-offset k - 1)=2300 - k - 1 := by unfold aU; omega
 have hpos : ¬ (2300-(k :ℤ) - 1)<0:= by omega
 have hmin:min (2300-(k :ℤ) - 1) 4600=2300 - k - 1 :=zm (by omega)
 have hmax :max (0:ℤ) (2300 - k - 1 - 2300)=0:=zf (by omega)
 unfold Bb
 rw [hd,harg]
 change gd 2300 2300 - gd 2300 (2300-(k :ℤ) - 1)= _
 rw [show gd 2300 2300=1324801 by decide]
 simp only [gd,hpos,t5 ,show (2*2300:ℤ)=4600 by decide,hmin,hmax]
 simp only [columns,quarter,show sG 0=0 by decide,wR]
 congr 2
 ring
private theorem agp (r k :ℕ) (f :Fin 6→ℤ) :
  (∑ j,(powers r k j:ℤ)*f j) =
    ((adX r k).toNat :ℤ)*(f 0+f 3)+((ahr r k).toNat :ℤ)*f 5:= by
 simp [JM,powers,Fin.succ,t7,vk]
private theorem dfl {x y :ℤ} (hx :0≤x) (hxy :x≤y) :x^2≤y ^2 := by
 nlinarith only [v8 (show 0≤y - x by omega) (show 0≤y + x by omega)]
private theorem dOV {r k :ℕ} (hk :k<2300) (hb:0<ahr r k) :
  0≤ columns k-(max 0 (aq3 r k))^2 := by
 let u:=max 0 (aq3 r k)
 have hu:0≤2*u:= by dsimp [u]; omega
 have huk :2*u≤(k :ℤ) := by
  unfold ahr at hb
  dsimp [u,aq3]
  omega
 have hs :=dfl hu huk
 have hq:=bKV (2301-(k :ℤ))
 have hmod:0≤(2301-(k :ℤ)) % 2 := by omega
 have hprod:0≤(k :ℤ)*(2301 - k) := by
  exact v8 (by omega) (by omega)
 change 0≤ columns k - u^2
 unfold columns
 nlinarith only [hs,hq,hmod,hprod]
theorem bBL {q k :ℕ} (hq:5000≤q) (hk :k<7300 - q) :
    (xR q (aU k) (powers (7300 - q) k) :ℤ)≤aWJ (7300 - q) k := by
  let r :ℕ:=7300 - q
  let a :ℤ:=((adX r k).toNat :ℤ)
  let b:ℤ:=((ahr r k).toNat :ℤ)
  let t:ℤ:=(r :ℤ) - k
  let p:=powers r k
  have ha :a=max 0 (adX r k) := by
    simpa only [max_comm] using J4 (adX r k)
  have hb:b=max 0 (ahr r k) := by
    simpa only [max_comm] using J4 (ahr r k)
  have han:0≤a := by omega
  have hkn:k<2300:= by omega
  have hd:iO q=2300:=vl (by omega)
  have ho:Ic q (aU k)=t:= by unfold Ic aU t r; omega
  have ht:0<t:= by dsimp [t,r]; omega
  have hc:=dNC hq hkn
  have hd' : K6 q p=2300 - 2*a - 2*b:= by
    dsimp only [p,K6]
    rw [hd,agp]
    simp [yE,a,b]
    ring
  have hP:D8 q (aU k) p 0=⟨-a-b,2300 - k - 2*a-b⟩:= by
    simp [p,D8,agp,pT,Jd,aU,a,b] <;>
      constructor <;> ring
  have hQ:D8 q (aU k) p 1=⟨1150-a-b,2300 - 2*a-2*b⟩:= by
    simp [p,D8,agp,pT,Jd,hd,a,b] <;>
      constructor <;> ring
  have hO:D8 q (aU k) p 2=⟨-a-b,t-a-2*b⟩:= by
    simp [p,D8,agp,pT,Jd,ho,a,b] <;>
      constructor <;> ring
  let shift:=m5 (K6 q p) (D8 q (aU k) p)
  have bound {v :ℤ} (hv :0≤v)
      (hle :columns k - max 0 (max (m5 (iO q) (pT q (aU k))) shift)≤v) :
      (xR q (aU k) p:ℤ)≤v := by
    rw [xR,ite_eq_right (by omega : ¬ Ic q (offset k)≤0),hc,
      J4 ]
    exact vH hle hv
  have byShift {v :ℤ} (hv :0≤v) (hle :columns k - shift≤v) :
      (xR q (aU k) p:ℤ)≤v :=
    bound hv ((G1 ((u9 _ _).trans (u9 _ _)) _).trans hle)
  change (xR q (aU k) p:ℤ)≤aWJ r k
  by_cases h:0<ahr r k
  · let u:=aq3 r k
    have hnon :=dOV hkn h
    simp only [aWJ,h,t4]
    by_cases hu:0< u
    · have hrel :a=adX r k∧b=ahr r k := by
        have ha' : 0≤adX r k := by unfold adX ahr at *; dsimp [r] at *; omega
        exact ⟨ha.trans (oZ ha'),hb.trans (oZ h.le)⟩
      have hdeg:2300 - 2*a-2*b=6*u-2 := by
        rw [hrel.1,hrel.2]; unfold u aq3 adX ahr; ring
      have hwp:2300-(k :ℤ) - 2*a-b=4*u-1 := by
        rw [hrel.1,hrel.2]; unfold u aq3 adX ahr; ring
      have hwo:t-a-2*b=4*u-1 := by
        rw [hrel.1,hrel.2]; unfold u aq3 adX ahr t; ring
      have hs :shift=u^2 := by
        dsimp [shift]
        rw [m5,hd',qG,hP,hQ,hO,hwp,hwo]
        simp only [hdeg,p5 (by omega : ¬ 6*u-2<0)]
        rw [bnA (a := -a-b) (w:=4*u-1) (by omega) (by omega),
          bnA (a :=1150-a-b) (w:=6*u-2) (by omega) (by omega),
          show 6*u-2+1=6*u-1 by ring]
        linarith only [dOU u]
      exact byShift hnon (by rw [hs,oZ hu.le])
    · apply bound hnon
      rw [zf (show u≤0 by omega)]
      have hmax :=C5 (0:ℤ) (max (m5 (iO q)
        (pT q (aU k))) shift)
      simp only [zero_pow (by decide : (2 :ℕ)≠0),wR]
      omega
  · have hb' : b=0:=hb.trans (max_eq_left (by omega))
    have halt:a=0∨t=a+2*k+1 := by unfold adX at ha; dsimp [t]; omega
    have had:a≤t:= by omega
    have hw:0≤2300-(k :ℤ) - 2*a := by
      unfold adX at ha
      unfold ahr at h
      omega
    have hs :shift=columns k - cost t+quarter a := by
      dsimp [shift]
      rw [m5,hd',qG ,hP,hQ,hO,hb']
      simp only [mul_zero,wR ,p5  (by omega : ¬ 2300 - 2*a<0)]
      rw [bnA (by omega) (by omega),bnA (by omega) (by omega),
        bnA (by omega) (by omega)]
      calc
        _=sG (2301 - 2*a) - cost (2300 - k - 2*a) - cost (2300 - 2*a) -
            cost (t-a) := by ring
        _ = _:= by
          rw [ew7 _ _ _ halt]
          have hconst:sG 2301 - cost 2300=1324801 := by decide
          have hcost:cost (2300-(k :ℤ))=quarter (2301-k) := by
            unfold cost
            congr 1
            ring
          unfold columns
          rw [hcost]
          linarith only [hconst]
    have hsq:=dfl han (show a≤t+1 by omega)
    simp only [aWJ,h,t5 ,← ha]
    change (xR q (aU  k) p:ℤ)≤ cost t - quarter a
    apply byShift
    · unfold cost quarter
      omega
    · rw [hs]
      linarith only []
end bzs
end
section
namespace Rk
noncomputable section
open K1 aR jA
open MvPolynomial
variable {σ R S:Type*} [Aa R] [Aa S]
def taylor :lV σ R →+* lV σ (lV σ R) :=
 pL (C.comp C) (fun i=>lz i+C (lz i))
def KR (a :σ →₀ ℕ) (F:lV σ R) :lV σ R :=
 (taylor F).coeff a
theorem aIY (a :mA →₀ ℕ) (F:jK) :
 KR a F=aox a F:=rfl
theorem c3J [zd σ] (a :σ →₀ ℕ) (F:lV σ R) (i:σ) :
    KR a (F*lz i) =
      (if i∈a.support then KR (a-Finsupp.single i 1) F else 0) +
        KR a F*lz i:= by
  simp only [KR,taylor,oq,Fa ,t7,HZ,
    wB,coeff_mul_X']
  rw [v9 _ (C (lz i)),vi ,v9 (lz i)]
theorem cbu [zd σ] (a :σ →₀ ℕ) (c:R) :
  KR a (C c)=if a=0 then C c else 0:= by
 classical
 simp [KR,taylor,coeff_C,eq_comm]
private def aKc (F:lV σ R) (a b:σ →₀ ℕ) :Prop :=
 (F.coeff (a+b)=0→(KR a F).coeff b=0) ∧
   ((∀ i,i∉a.support∨i∉b.support) →
     (KR a F).coeff b=F.coeff (a+b))
private theorem drZ {a b:σ →₀ ℕ} {i:σ} :
  i∈(a+b).support↔i∈a.support∨i∈b.support := by
 simp only [Finsupp.mem_support_iff,wB]
 omega
private theorem cqI [zd σ] {a b:σ →₀ ℕ} {i:σ}
  (ha :i∈a.support) :
  (a-Finsupp.single i 1)+b=a+b-Finsupp.single i 1 := by
 have hle :p7 i 1≤a := by
  rw [Finsupp.single_le_iff]
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha)
 apply add_right_cancel (b:=p7 i 1)
 calc
  _=(a-Finsupp.single i 1+Finsupp.single i 1)+b:= by ac_rfl
  _=a+b:= by rw [NY hle]
  _ = _:=(NY (hle.trans le_self_add)).symm
private theorem dMe (F:lV σ R)
    (hF : ∀ a b,aKc F a b) (i:σ) (a b:σ →₀ ℕ) :
    aKc (F*lz i) a b:= by
  classical
  unfold aKc
  rw [c3J,HZ,wB,coeff_mul_X',coeff_mul_X']
  have ha' (hd : ∀ j,j∉a.support∨j∉b.support) (j:σ) :
      j∉(a-Finsupp.single i 1).support∨j∉b.support :=
    (hd j).imp (fun hj hk=>hj (Ts tsub_le_self hk)) id
  have hb' (hd : ∀ j,j∉a.support∨j∉b.support) (j:σ) :
      j∉a.support∨j∉(b-Finsupp.single i 1).support :=
    (hd j).imp id (fun hj hk=>hj (Ts tsub_le_self hk))
  simp only [drZ]
  by_cases ha :i∈a.support
  · have hsub:=cqI (b:=b) ha
    by_cases hb:i∈b.support
    · have hsub' : a+(b-Finsupp.single i 1)=a+b-Finsupp.single i 1 := by
        simpa only [wY] using cqI (b:=a) hb
      simp only [ha,hb,true_or,t4]
      refine ⟨fun hz => ?_,fun hd=>False.elim ((hd i).elim (fun h=>h ha) (fun h=>h hb))⟩
      rw [(hF _ _).1 ((nq F.coeff hsub).trans hz),(hF _ _).1 ((nq F.coeff hsub').trans hz),Av]
    · simp only [ha,hb,true_or,t4 ,t5 ,Av]
      exact ⟨fun hz=>(hF _ _).1 ((nq F.coeff hsub).trans hz),
        fun hd=>((hF _ _).2 (ha' hd)).trans (nq F.coeff hsub)⟩
  · by_cases hb:i∈b.support
    · have hsub:a+(b-Finsupp.single i 1)=a+b-Finsupp.single i 1 := by
        simpa only [wY] using cqI (b:=a) hb
      simp only [ha,hb,false_or,t4 ,t5 ,RP ,Finsupp.coe_zero,Ml,qJ]
      exact ⟨fun hz=>(hF _ _).1 ((nq F.coeff hsub).trans hz),
        fun hd=>((hF _ _).2 (hb' hd)).trans (nq F.coeff hsub)⟩
    · simp [ha,hb]
private theorem cF1 (m:σ →₀ ℕ) (c:R) (a b:σ →₀ ℕ) :
   aKc (ov m c) a b:= by
 classical
 refine MvPolynomial.induction_on_monomial (motive := fun F => ∀ a b,aKc F a b)
   ?_ (fun G i ih=>dMe G ih i) m c a b
 intro c a b
 unfold aKc
 by_cases ha :a=0
 · subst a
   simp [cbu]
 · have hab:a+b≠0:= fun hz=>ha (add_eq_zero.mp hz).1
   simp [cbu,coeff_C,ha,Ne.symm hab]
theorem cGh (a b:σ →₀ ℕ) (F:lV σ R) :aKc F a b:= by
 classical
 unfold aKc
 have hf : (KR a F).coeff b = ∑ m∈F.support,
     (KR a (ov m (F.coeff m))).coeff b:= by
   conv_lhs=>rw [F.as_sum]
   simp only [KR,p9,EP]
 rw [hf]
 have hzero (m:σ →₀ ℕ) (hm:m≠a+b) :
     (KR a (ov m (F.coeff m))).coeff b=0 :=
   (cF1 m _ _ _).1 (by simp [yl,hm])
 by_cases hmem:a+b∈F.support
 · rw [Finset.sum_eq_single_of_mem _ hmem (fun m _ hm=>hzero m hm)]
   have h:=cF1 (a+b) (F.coeff (a+b)) a b
   simpa [aKc] using h
 · rw [xm (fun m hm=>hzero m (fun he=>hmem (he ▸ hm)))]
   have hz :F.coeff (a+b)=0:= by simpa [G8] using hmem
   simp [hz]
theorem bXR (a b:σ →₀ ℕ) (F:lV σ R)
   (h:F.coeff (a+b)=0) : (KR a F).coeff b=0 :=
 (cGh a b F).1 h
theorem cGi (a b:σ →₀ ℕ) (F:lV σ R)
   (h : ∀ i,i∉a.support∨i∉b.support) :
   (KR a F).coeff b=F.coeff (a+b) :=
 (cGh a b F).2 h
theorem bsm (f :R →+* S) (a :σ →₀ ℕ) (F:lV σ R) :
   map f (KR a F)=KR a (map f F) := by
 let lhs :lV σ R →+* lV σ (lV σ S) :=
   (map (map f)).comp taylor
 let rhs :lV σ R →+* lV σ (lV σ S) :=
   taylor.comp (map f)
 have h:lhs=rhs := by
   apply pQ
   · intro r
     simp [lhs,rhs,taylor]
   · intro i
     simp [lhs,rhs,taylor]
 simpa only [lhs,rhs,qm,Gr,KR] using
   nq (fun G:lV σ (lV σ S)=>G.coeff a) (oy h F)
theorem bh9 (y :σ→iP) (a :σ →₀ ℕ)
   (F:lV σ iP) :
   ox y (KR a F)=KR a (ox y F) := by
 let lhs :lV σ iP →+* lV σ (lV σ iP) :=
   (map (ox y)).comp taylor
 let rhs :lV σ iP →+* lV σ (lV σ iP) :=
   taylor.comp (ox y)
 have h:lhs=rhs := by
   apply pQ
   · intro r
     simp [lhs,rhs,ox ,taylor]
   · intro i
     simp [lhs,rhs,ox ,taylor,vk]
 simpa only [lhs,rhs,qm,Gr,KR] using
   nq (fun G:lV σ (lV σ iP)=>G.coeff a)
     (oy h F)
theorem dhT (z :iP) (y :Fin 3→iP) (F:ko) :
  ox y (JX z F)=JX 0 (ox (ED z y) F) := by
 have h: (ox y).comp (JX z)=(JX 0).comp (ox (ED z y)) := by
  apply pQ
  · intro r
    simp [JX,ox]
  · intro i
    cases i <;> simp [JX,ox ,ED]
 exact oy h F
theorem cF5 (F:ko) (b:Fin 3 →₀ ℕ) :
   (JX 0 F).coeff b=F.coeff (b.optionElim 0) := by
 let e :=(xW iP (Fin 3)).toRingHom
 have h:JX (0:iP)=(pU 0).comp e := by
   apply pQ
   · intro r
     simp [e,JX,zh]
   · intro i
     cases i <;> simp [e,JX,Gn,LO]
 rw [h,qm]
 change ((qN F).eval 0).coeff b= _
 rw [← Polynomial.coeff_zero_eq_eval_zero]
 exact IU iP F 0 b
end
end Rk
end
section
namespace bzs
open Rj Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
private def aSR (a b:ℤ) (n:ℕ) :ℤ :=
 let N :ℤ:=n
 (6*N*a^2+6*a*b*N*(N-1)+b^2*N*(N-1)*(2*N-1))/6
private theorem dfQ (a b:ℤ) (n:ℕ) :
   (∑ k∈cy n,(a+b*(k :ℤ))^2)=aSR a b n:= by
 have h (n:ℕ) :6*(∑ k∈cy n,(a+b*(k :ℤ))^2) =
     6*(n:ℤ)*a^2+6*a*b*n*((n:ℤ)-1)+b^2*n*((n:ℤ)-1)*(2*(n:ℤ)-1) := by
   induction n with
   | zero=>simp
   | succ n ih =>
     rw [t3 ,t7,ih,Et]
     ring
 dsimp [aSR]
 rw [← h n]
 omega
private def aGA (a b:ℤ) (n:ℕ) :ℤ :=
 (aSR a b n-((n:ℤ)+a % 2)/2)/4
private theorem crx (a b:ℤ) (n:ℕ) (hb:b % 2=1) :
  (∑ k∈cy n,quarter (a+b*(k :ℤ)))=aGA a b n:= by
 have hmod (k :ℕ) : (a+b*(k :ℤ)) % 2=(a+(k :ℤ)) % 2 := by
  rw [Int.add_emod a,Int.mul_emod,hb,sH]
  omega
 have hpar (n:ℕ) : (∑ k∈cy n,(a+b*(k :ℤ)) % 2)=((n:ℤ)+a % 2)/2 := by
  induction n with
  | zero =>
    simp
    omega
  | succ n ih =>
    rw [t3 ,ih,hmod,Et]
    omega
 have hsum:4*(∑ k∈cy n,quarter (a+b*(k :ℤ))) =
    aSR a b n-((n:ℤ)+a % 2)/2 := by
  rw [Ar]
  simp_rw [bKV]
  rw [wA,dfQ,hpar]
 unfold aGA
 omega
private theorem crO {f :ℕ→ℤ} {m n:ℕ} (h:m≤n) :
  (∑ k∈cy n,f k) =
    (∑ k∈cy m,f k) + ∑ k∈cy (n-m),f (m+k) := by
 simpa only [Nat.add_sub_of_le h,Nat.add_comm] using Df f m (n-m)
private def bnM (r :ℕ) :ℕ:=((2*(r :ℤ)-2299)/3).toNat
private def azt (r :ℕ) :ℕ:=(r+1)/3
private def cw1 (r :ℕ) :ℕ:=min (bnM r) (((r :ℤ)-1149)/2).toNat
private def bqG (r :ℕ) :ℤ :=
 let c:=bnM r
 let z :=cw1 r
 let a :=azt r
 (c:ℤ)*1324801-aGA 2301 (-1) c -
   aSR (2*(z :ℤ)+1151-r) 2 (c-z) +
   (aGA ((r :ℤ)+1-c) (-1) (r-c) -
     aGA ((r :ℤ)-1-3*c) (-3) (a-c))
private theorem gw8 (r :ℕ) (hr :r≤2300) :
    (∑ k∈cy r,aWJ r k)=bqG r := by
  let c:=bnM r
  let a :=azt r
  let z :=cw1 r
  have hc (k :ℕ) :k<c↔0<ahr r k := by dsimp [c,bnM,ahr]; omega
  have ha (k :ℕ) :k<a↔0<adX r k := by dsimp [a,azt,adX]; omega
  have hCA:c≤a := by dsimp [c,bnM,a,azt]; omega
  have hAr :a≤ r := by dsimp [a,azt]; omega
  have hCZ:z≤ c:=G0 _ _
  have hz (k :ℕ) (hk :k<c) :k<z↔aq3 r k≤0:= by
    dsimp [z,cw1,aq3]
    change k< min c _↔_
    omega
  have hcols : (∑ k∈cy c,columns k)=(c:ℤ)*1324801-aGA 2301 (-1) c:= by
    simp only [columns,Kh,neg_one_mul,zk,sum_const,card_range,
      nsmul_eq_mul,sum_neg_distrib]
    rw [← crx 2301 (-1) c (by decide)]
    simp
  have hconic: (∑ k∈cy c,(max 0 (aq3 r k))^2) =
      aSR (2*(z :ℤ)+1151-r) 2 (c-z) := by
    rw [crO hCZ]
    have hzero : (∑ k∈cy z,(max 0 (aq3 r k))^2)=0:= by
      apply xm
      intro k hk
      have h:=mem_range.mp hk
      simp [zf ((hz k (by omega)).mp h)]
    rw [hzero,qJ,← dfQ]
    apply n5 rfl
    intro k hk
    have h:=mem_range.mp hk
    rw [oZ (show 0≤aq3 r (z+k) by
      have hh:=hz (z+k) (by omega)
      omega)]
    simp only [aq3,yJ]
    ring
  have hfirst: (∑ k∈cy c,aWJ r k) =
      (c:ℤ)*1324801-aGA 2301 (-1) c-aSR (2*(z :ℤ)+1151-r) 2 (c-z) := by
    rw [← hcols,← hconic,← wA]
    apply n5 rfl
    intro k hk
    simp only [aWJ,t8 ((hc k).mp (mem_range.mp hk))]
  have hline : (∑ k∈cy (r-c),quarter (max 0 (adX r (c+k)))) =
      aGA ((r :ℤ)-1-3*c) (-3) (a-c) := by
    rw [crO (m:=a-c) (by omega)]
    have hzero : (∑ k∈cy (r-c-(a-c)),
        quarter (max 0 (adX r (c+(a-c+k)))))=0:= by
      apply xm
      intro k _
      have hh:=ha (c+(a-c+k))
      simp [zf (show adX r (c+(a-c+k))≤0 by omega),quarter]
    rw [hzero,Av,← crx ((r :ℤ)-1-3*c) (-3) (a-c) (by decide)]
    apply n5 rfl
    intro k hk
    have h:=mem_range.mp hk
    rw [oZ (((ha (c+k)).mp (by omega)).le)]
    simp only [adX,yJ]
    ring
  have hbase : (∑ k∈cy (r-c),quarter ((r :ℤ)-(↑(c+k) :ℤ)+1)) =
      aGA ((r :ℤ)+1-c) (-1) (r-c) := by
    rw [← crx ((r :ℤ)+1-c) (-1) (r-c) (by decide)]
    apply n5 rfl
    intro k _
    simp only [yJ]
    ring
  rw [crO (hCA.trans hAr),hfirst]
  change _=(c:ℤ)*1324801-aGA 2301 (-1) c -
    aSR (2*(z :ℤ)+1151-r) 2 (c-z)+_
  congr 1
  rw [← hbase,← hline,← wA]
  apply n5 rfl
  intro k _
  simp only [aWJ,p5 (show ¬ 0<ahr r (c+k) by
    have hh:=hc (c+k)
    omega)]
private theorem aH4 {q:ℕ} (hq:5000≤q) :
   (Xi (fun q=>powers (7300-q)) q:ℤ)≤bqG (7300-q) := by
 have hsum:Xi (fun q=>powers (7300-q)) q =
     ∑ k∈cy (7300-q),xR q (aU k) (powers (7300-q) k) := by
   symm
   apply ze (xL (Iw _ _))
   intro k _ hk
   have h:Ic q (aU k)≤0:= by
     unfold Ic aU
     simp only [Du] at hk
     omega
   simp [xR,h]
 rw [hsum,JQ,← gw8 _ (by omega)]
 exact qM fun _ hk=>bBL hq (mem_range.mp hk)
private def total:ℕ→ℤ
 | 0=>0
 | j+1=>total j+bqG (2300-j)
private theorem crM (n:ℕ) :
   (∑ j∈cy n,bqG (2300-j))=total n:= by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [sum_range_succ,ih,total]
private def bqH (s :ℕ) :ℕ→ℤ
 | 0=>0
 | n+1=>bqH s n+bqG (2300-(s+n))
private theorem gCu (s n:ℕ) :
   total (s+n)=total s+bqH s n:= by
 induction n with
 | zero=>simp [bqH]
 | succ n ih=>rw [Nat.add_succ,total,bqH,ih,add_assoc]
private theorem CM (s n:ℕ) (a b:ℤ)
  (hs :total s=a) (hn:bqH s n=b) :total (s+n)=a+b:= by
 rw [gCu,hs,hn]
private theorem gC6:total 32=18649302073 :=
 CM 0 32 0 18649302073 rfl (by decide +kernel)
private theorem gDh:total 64=36632681586 :=
 CM 32 32 18649302073 17983379513 gC6 (by decide +kernel)
private theorem gDs :total 96=53962710528 :=
 CM 64 32 36632681586 17330028942 gDh (by decide +kernel)
private theorem gCJ:total 128=70651960889 :=
 CM 96 32 53962710528 16689250361 gDs (by decide +kernel)
private theorem gCU:total 160=86713004658 :=
 CM 128 32 70651960889 16061043769 gCJ (by decide +kernel)
private theorem gC2 :total 192=102158413824 :=
 CM 160 32 86713004658 15445409166 gCU (by decide +kernel)
private theorem gC3:total 224=117000760377 :=
 CM 192 32 102158413824 14842346553 gC2 (by decide +kernel)
private theorem gC4 :total 256=131252616306 :=
 CM 224 32 117000760377 14251855929 gC3 (by decide +kernel)
private theorem gC5:total 288=144926553600 :=
 CM 256 32 131252616306 13673937294 gC4 (by decide +kernel)
private theorem gC7:total 320=158035144249 :=
 CM 288 32 144926553600 13108590649 gC5 (by decide +kernel)
private theorem gC8:total 352=170590960242 :=
 CM 320 32 158035144249 12555815993 gC7 (by decide +kernel)
private theorem gC9:total 384=182606573568 :=
 CM 352 32 170590960242 12015613326 gC8 (by decide +kernel)
private theorem gDa :total 416=194094556217 :=
 CM 384 32 182606573568 11487982649 gC9 (by decide +kernel)
private theorem gDb:total 448=205067480178 :=
 CM 416 32 194094556217 10972923961 gDa (by decide +kernel)
private theorem gDc:total 480=215537917440 :=
 CM 448 32 205067480178 10470437262 gDb (by decide +kernel)
private theorem gDd:total 512=225518439993 :=
 CM 480 32 215537917440 9980522553 gDc (by decide +kernel)
private theorem gDe :total 544=235021619826 :=
 CM 512 32 225518439993 9503179833 gDd (by decide +kernel)
private theorem gDf :total 576=244060028928 :=
 CM 544 32 235021619826 9038409102 gDe (by decide +kernel)
private theorem gDg:total 608=252646239289 :=
 CM 576 32 244060028928 8586210361 gDf (by decide +kernel)
private theorem gDi:total 640=260792822898 :=
 CM 608 32 252646239289 8146583609 gDg (by decide +kernel)
private theorem gDj:total 672=268512351744 :=
 CM 640 32 260792822898 7719528846 gDi (by decide +kernel)
private theorem gDk :total 704=275817397817 :=
 CM 672 32 268512351744 7305046073 gDj (by decide +kernel)
private theorem gDl:total 736=282720533106 :=
 CM 704 32 275817397817 6903135289 gDk (by decide +kernel)
private theorem gDm:total 768=289234329600 :=
 CM 736 32 282720533106 6513796494 gDl (by decide +kernel)
private theorem gDn:total 800=295371359289 :=
 CM 768 32 289234329600 6137029689 gDm (by decide +kernel)
private theorem gDo:total 832=301144194162 :=
 CM 800 32 295371359289 5772834873 gDn (by decide +kernel)
private theorem gDp:total 864=306565406208 :=
 CM 832 32 301144194162 5421212046 gDo (by decide +kernel)
private theorem gDq:total 896=311647567417 :=
 CM 864 32 306565406208 5082161209 gDp (by decide +kernel)
private theorem gDr :total 928=316403249778 :=
 CM 896 32 311647567417 4755682361 gDq (by decide +kernel)
private theorem gDt:total 960=320845025280 :=
 CM 928 32 316403249778 4441775502 gDr (by decide +kernel)
private theorem gDu:total 992=324985465913 :=
 CM 960 32 320845025280 4140440633 gDt (by decide +kernel)
private theorem gCB:total 1024=328837143666 :=
 CM 992 32 324985465913 3851677753 gDu (by decide +kernel)
private theorem gCC:total 1056=332412630528 :=
 CM 1024 32 328837143666 3575486862 gCB (by decide +kernel)
private theorem gCD:total 1088=335724498489 :=
 CM 1056 32 332412630528 3311867961 gCC (by decide +kernel)
private theorem gCE :total 1120=338785319538 :=
 CM 1088 32 335724498489 3060821049 gCD (by decide +kernel)
private theorem gCF:total 1152=341607665664 :=
 CM 1120 32 338785319538 2822346126 gCE (by decide +kernel)
private theorem gCG:total 1184=344204093457 :=
 CM 1152 32 341607665664 2596427793 gCF (by decide +kernel)
private theorem gCH :total 1216=346586981097 :=
 CM 1184 32 344204093457 2382887640 gCG (by decide +kernel)
private theorem gCI :total 1248=348768370824 :=
 CM 1216 32 346586981097 2181389727 gCH (by decide +kernel)
private theorem gCK:total 1280=350759955353 :=
 CM 1248 32 348768370824 1991584529 gCI (by decide +kernel)
private theorem gCL:total 1312=352573077873 :=
 CM 1280 32 350759955353 1813122520 gCK (by decide +kernel)
private theorem gCM:total 1344=354218732048 :=
 CM 1312 32 352573077873 1645654175 gCL (by decide +kernel)
private theorem gCN :total 1376=355707562017 :=
 CM 1344 32 354218732048 1488829969 gCM (by decide +kernel)
private theorem gCO:total 1408=357049862393 :=
 CM 1376 32 355707562017 1342300376 gCN (by decide +kernel)
private theorem gCP:total 1440=358255578264 :=
 CM 1408 32 357049862393 1205715871 gCO (by decide +kernel)
private theorem gCQ:total 1472=359334305193 :=
 CM 1440 32 358255578264 1078726929 gCP (by decide +kernel)
private theorem gCR:total 1504=360295289217 :=
 CM 1472 32 359334305193 960984024 gCQ (by decide +kernel)
private theorem gCS:total 1536=361147426848 :=
 CM 1504 32 360295289217 852137631 gCR (by decide +kernel)
private theorem gCT:total 1568=361899265073 :=
 CM 1536 32 361147426848 751838225 gCS (by decide +kernel)
private theorem gCV:total 1600=362559001353 :=
 CM 1568 32 361899265073 659736280 gCT (by decide +kernel)
private theorem gCW:total 1632=363134483624 :=
 CM 1600 32 362559001353 575482271 gCV (by decide +kernel)
private theorem gCX:total 1664=363633210297 :=
 CM 1632 32 363134483624 498726673 gCW (by decide +kernel)
private theorem gCY:total 1696=364062330257 :=
 CM 1664 32 363633210297 429119960 gCX (by decide +kernel)
private theorem gCZ:total 1728=364428642864 :=
 CM 1696 32 364062330257 366312607 gCY (by decide +kernel)
private theorem gC0:total 1760=364738597953 :=
 CM 1728 32 364428642864 309955089 gCZ (by decide +kernel)
private theorem gC1 :total 1790=364983426528 :=
 CM 1760 30 364738597953 244828575 gC0 (by decide +kernel)
private theorem bxY:total 1790≤364983426528 :=
 gC1.le
theorem proof :Rj.c6:= by
 refine ⟨fun q=>powers (7300-q),Int.ofNat_le.mp ?_⟩
 change _≤(364983426528:ℤ)
 rw [JQ]
 refine le_trans (qM (fun j _=>aH4 (q:=5000+j) (by omega))) ?_
 simpa only [show ∀ j:ℕ,7300-(5000+j)=2300-j by intro j; omega,
  crM] using bxY
end bzs
end
section
namespace Rk
noncomputable section
open K1 aR jA
open scoped Polynomial BigOperators
private def aOz (H :ao[X]) (i:Fin 3) :Lower :=
 ∑ j:Fin 3,if j.val≤ i.val then
   c9 (qV (oK (i.val - j.val) H))*lz j
 else 0
private def substitute (g:Fin 3→p6) :p6 →+* Lower :=
 pL c9 g
private theorem eo8 (H :ao[X]) (hH :H≠0) :
    ∃ g:Fin 3→p6,(∀ i,(g i).IsHomogeneous 1) ∧
      (substitute g).comp (substitute (aOz H))=vG Lower := by
  let a :=qV H
  let b:=qV (oK 1 H)
  let c:=qV (oK 2 H)
  let u:=a⁻¹
  let g₀:Lower :=c9 u*lz 0
  let g₁ :Lower :=c9 u*(lz 1-MvPolynomial.C b*g₀)
  let g₂ :Lower :=c9 u *
    (lz 2 - c9 c*g₀-MvPolynomial.C b*g₁)
  let g:Fin 3→Lower := ![g₀,g₁,g₂]
  have ha :a≠0 :=
    (Fz _ (vh ao[X] iP)).mpr hH
  have hcancel (P:p6) :c9 a*(c9 u*P)=P:= by
    rw [← z8 ,← oq,show a*u=1 from mul_inv_cancel₀ ha,map_one,sH]
  refine ⟨g,?_,?_⟩
  · have h₀:g₀.IsHomogeneous 1 :=(Np _ _).C_mul _
    have h₁:g₁.IsHomogeneous 1 :=
      ((Np _ _).sub (h₀.C_mul _)).C_mul _
    have h₂:g₂.IsHomogeneous 1 :=
      (((Np _ _).sub (h₀.C_mul _)).sub (h₁.C_mul _)).C_mul _
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  · apply pQ
    · intro r
      simp [substitute]
    · intro i
      simp only [qm,RingHom.id_apply,substitute,Fa ,
        aOz,p9,apply_ite,oq,GF,xu]
      have h₀:c9 a*g₀=lz 0:= by simp [g₀,hcancel]
      have h₁:c9 b*g₀+MvPolynomial.C a*g₁=lz 1 := by
        simp only [g₁,hcancel]
        abel
      have h₂:c9 c*g₀+MvPolynomial.C b*g₁+MvPolynomial.C a*g₂ =
          lz 2 := by
        simp only [g₂,hcancel]
        abel
      fin_cases i
      · simpa [qG,a,g] using h₀
      · simpa [qG,a,b,g] using h₁
      · simpa [qG,a,b,c,g] using h₂
private theorem gu4 (F:p6) (g:Fin 3→p6) (d:ℕ)
   (hg : ∀ i,(g i).IsHomogeneous 1) (hF : ∀ a∈F.support,d≤a.degree) :
   ∀ a∈(substitute g F).support,d≤a.degree := by
 intro a ha
 by_contra! hlt
 apply MvPolynomial.mem_support_iff.mp ha
 conv_lhs=>rw [F.as_sum]
 rw [p9,EP]
 apply xm
 intro b hb
 have hh: (substitute g (ov b (F.coeff b))).IsHomogeneous b.degree := by
   have hm: (ov b (F.coeff b)).IsHomogeneous b.degree :=
     MvPolynomial.isHomogeneous_monomial _ rfl
   simpa only [substitute,MvPolynomial.coe_eval₂Hom,sH] using
     hm.eval₂ c9 g (fun r=>MvPolynomial.isHomogeneous_C _ r) hg
 by_contra hz
 have hab:a.degree=b.degree :=(oy Finsupp.degree_eq_weight_one a).trans (hh hz)
 exact (G4 hlt) (hab ▸ hF b hb)
private theorem fXb (H res T:ao[X]) (F:af 3) :
    ox (jW T) (oY qV (az5 H res F)) =
      substitute (aOz H)
        (ox (jW (H*T+res)) (oY qV F)) := by
  let left:=(ox (jW T)).comp ((oY qV).comp (az5 H res))
  let right:=(substitute (aOz H)).comp
    ((ox (jW (H*T+res))).comp (oY qV))
  have h:left=right:= by
    apply pQ
    · intro r
      simp [left,right,substitute,az5,ox]
    · intro i
      have hsum :
          (∑ j:Fin 3,if j.val≤ i.val then
            c9 (qV (oK (i.val - j.val) H)) *
              (lz j+MvPolynomial.C (qV (jet T j)))
          else 0)=aOz H i+MvPolynomial.C (qV
            (∑ j:Fin 3,if j.val≤ i.val then
              oK (i.val - j.val) H*jet T j else 0)) := by
        unfold aOz
        rw [p9,p9,← zk]
        apply n5 rfl
        intro j _
        by_cases hj:j.val≤ i.val
        · simp only [hj,t4 ,t7,oq]
        · simp [hj]
      simp only [left,right,qm,substitute,az5,
        ox ,Fa ,GF,qy ,
        p9,apply_ite,oq,MvPolynomial.map_X,MvPolynomial.map_C,xu,
        jW]
      rw [hsum,cV4,qy ,qy]
      abel
  exact oy h F
private theorem duI (z :ao) (F:jK) :
  oY qV (JX (lI z) F) =
    JX (DI z) (bC F) := by
 have hconst:qV (lI z)=DI z :=
  (yU ao ao[X] iP z).symm
 have h: (oY qV).comp (JX (lI z)) =
    (JX (DI z)).comp (oY qV) := by
  apply pQ
  · intro r
    simp [JX]
  · intro i
    cases i <;> simp [JX,hconst]
 exact oy h F
theorem dia (H res T:ao[X]) (z :ao) (r d:ℕ)
   (F:jK) (Q:af 3) (hH :H≠0)
   (heq :aPU H res z F=c9 (H^r)*Q)
   (hq:Qu (oY qV Q) (jW T) d) :
   Qu (JX (DI z) (bC F)) (jW (H*T+res)) d:= by
 let G:=ox (jW (H*T+res)) (JX (DI z) (bC F))
 have hc:substitute (aOz H) G =
     c9 (qV (H^r))*ox (jW T) (oY qV Q) := by
   dsimp only [G]
   rw [← duI,← fXb,← aPU,heq]
   simp [ox]
 have ho : ∀ a∈(substitute (aOz H) G).support,d≤a.degree := by
   intro a ha
   apply hq a
   rw [hc,G8 ,vi] at ha
   exact MvPolynomial.mem_support_iff.mpr (fun hz=>ha (by rw [hz,mul_zero]))
 obtain ⟨g,hg,hcomp⟩:=eo8 H hH
 have hid :substitute g (substitute (aOz H) G)=G:=oy hcomp G
 have hvan:=gu4 _ g d hg ho
 rwa [hid] at hvan
end
end Rk
end
section
namespace Rk
noncomputable section
open K1 aR jA
open scoped Polynomial
def c1 :Prop :=
  ∀ w Γ s (P:jF Γ s) (L:kH P) box t F,
    Source w P L box t F → ∀ i,
      Source w P L box (t+7800*i) (Yd P.H i F)
def c2 :Prop :=
  ∀ w Γ s (P:jF Γ s) (L:kH P) box t F,
    Source w P L box t F → ∀ γ∈Γ,
      ∃ Q:af 3,a04 t Q ∧
        aPU P.H (Tj L.numerator L.denominator (P.z γ)) (P.z γ) F =
          c9 (P.H^(box.b+box.j))*Q
end
end Rk
end
section
namespace aA0
noncomputable section
open K1 aR jA Rk
open scoped Polynomial
variable {R:Type*} [Aa R]
def aEP:VP R →+* (VP R)[X] :=
  (sS MvPolynomial.constantCoeff).comp
    ((xW (VP R) (Fin 3)).toRingHom.comp taylor)
theorem cGk (F:VP R) (i:ℕ) :
  (aEP F).coeff i=KR (p7 none i) F:= by
 simp only [aEP,qm,Kp,FQ,
  PD,KR]
 change (((xW _ _) (taylor F)).coeff i).coeff 0= _
 rw [IU,Finsupp.optionElim_zero]
@[simp] theorem gox (p:R) :
   aEP (c9 p)=lI (c9 p) := by
  simp [aEP,taylor,zh]
@[simp] theorem goy :
    aEP (lz none :VP R) =
      lJ+Polynomial.C (lz none) := by
  simp [aEP,taylor,zh,
    LO]
@[simp] theorem goz (j:Fin 3) :
    aEP (lz (some j) :VP R) =
      lI (lz (some j)) := by
  simp [aEP,taylor,zh,
    Gn]
private theorem bno (F:jK) (i:ℕ) (b:mA →₀ ℕ) :
   ∃ u:ao,(KR (p7 none i) F).coeff b =
     F.coeff (p7 none i+b)*lI u:= by
 let a :mA →₀ ℕ:=p7 none i
 let m:=a+b
 let c:=F.coeff m
 have hz : (KR a (F-MvPolynomial.monomial m c)).coeff b=0 :=
   bXR _ _ _ (by simp [c,m])
 have hz' : (KR a F).coeff b-(KR a (ov m c)).coeff b=0:= by
   simpa only [KR,zS ,MvPolynomial.coeff_sub] using hz
 let G:VP ao:=ov m 1
 refine ⟨(KR a G).coeff b,(sub_eq_zero.mp hz').trans ?_⟩
 have hG: (ov m c:jK) =
     c9 c*oY lI G:= by
   simp [G,Sv]
 rw [hG]
 have hmul :KR a (c9 c*oY lI G) =
     c9 c*KR a (oY lI G) := by
   simp [KR,taylor,vi]
 rw [hmul,vi ,← bsm,Gr]
private theorem a8W {H :ao[X]} {i:ℕ} {F:jK} {b:mA →₀ ℕ}
  (hb:b∈(Yd H i F).support) :p7 none i+b∈F.support := by
 obtain ⟨u,hu⟩:=bno F i b
 rw [G8] at hb ⊢
 intro hz
 apply hb
 simp only [Yd,← aIY,vi ,hu,hz,
  vZ,mul_zero]
private theorem byG (w:mA→ℕ) (hw:w none=0)
  (i:ℕ) (b:mA →₀ ℕ) :
  z7 w (p7 none i+b)=z7 w b:= by
 rw [qy ,Qx ,hw,smul_zero,qJ]
theorem cEb (H :ao[X]) (i:ℕ) (F:jK) (box :nI)
   (hF:Jn box F) :Jn box (Yd H i F) := by
 obtain ⟨hB,hJ,hC,hU⟩:=hF
 refine ⟨?_,?_,?_,?_⟩
 · unfold vC zg
   apply Mz
   intro b hb
   rw [← byG _ rfl i b]
   exact (vj _ (a8W hb)).trans hB
 · unfold lP zg
   apply Mz
   intro b hb
   rw [← byG _ rfl i b]
   exact (vj _ (a8W hb)).trans hJ
 · rw [P7]
   intro b hb
   have h:=(Gj (some 2) (a8W hb)).trans hC
   simpa using h
 · rw [gY,P7]
   intro b hb
   exact (G5 ..).trans
     ((Gj none (a8W hb)).trans hU)
private def back (x v :ao) :jK →+* jK :=
  pL c9 (fun j =>
    if j=some 0 then
      lz (some 0)+MvPolynomial.C (lI v) -
        c9 (lI x-Polynomial.X)*lz (some 1) -
        c9 ((lI x-Polynomial.X)^2)*lz (some 2)
    else lz j)
private theorem dxM (x v :ao) (p:ao[X]) :
  back x v (c9 p)=c9 p:= by
 simp [back]
private theorem dxO (x v :ao) :
    (sS (back x v)).comp aEP=aEP.comp (back x v) := by
  apply pQ
  · intro c
    simp [back]
  · intro j
    cases j with
    | none=>simp [back]
    | some j =>
      by_cases h:j=0
      · subst j
        simp [back]
      · simp [back,h]
private theorem dxN (H :ao[X]) (i m:ℕ) (x v :ao) (F:jK)
    (hF : ∀ b:mA →₀ ℕ,(lJ-Polynomial.C x)^(m-3*b (some 0)) ∣
      (back x v F).coeff b) (b:mA →₀ ℕ) :
    (lJ-Polynomial.C x)^(m-3*b (some 0)) ∣
      (back x v (Yd H i F)).coeff b:= by
  have hcomm :
      back x v (KR (p7 none i) F) =
        KR (p7 none i) (back x v F) := by
    have h:=nq (fun p:jK[X]=>p.coeff i)
      (oy (dxO x v) F)
    simpa only [qm,Kp,FQ,
      cGk] using h
  rw [Yd,← aIY,oq,dxM,hcomm,vi]
  obtain ⟨u,hu⟩:=bno (back x v F) i b
  rw [hu]
  have hd:=hF (p7 none i+b)
  rw [wB,Finsupp.single_eq_of_ne (by decide),qJ] at hd
  exact VC (Vz hd _) _
theorem cH4 (H :ao[X]) (i:ℕ) (w:I→K) (F:jK)
  (hF:bAy w F) :bAy w (Yd H i F) :=
 fun j b=>dxN H i 5000 _ _ F (hF j) b
end
end aA0
end
section
namespace aFN
noncomputable section
open aR jA NR
open scoped Polynomial BigOperators
def GV (z₀:kS) :jK →+* Lq :=
  pL (MvPolynomial.C.comp (sS (mD ao kS)))
    (fun i:mA=>i.elim
      (c9 (lI (mD ao[X] kS lJ)))
      (fun j=>if j=0 then lz j+MvPolynomial.C (lI z₀)
        else lz j))
def aTo {R:Type*} [oj R] (t:R) (i:Fin 3) :lV (Fin 3) R :=
  ![c9 t*lz 0,
    lz 0+MvPolynomial.C t*lz 1,
    lz 1+MvPolynomial.C t*lz 2] i
def canonical {R:Type*} [oj R] (t:R) :
    lV (Fin 3) R →+* lV (Fin 3) R :=
  pL c9 (aTo t)
def admissible (a :nI) (e :Fin 3 →₀ ℕ) :Prop :=
 e 0+e 1+e 2≤a.b∧e 1+2*e 2≤a.j∧e 2≤a.t
abbrev Slot (a :nI) (q:ℕ) :=
 Σ e₂:Fin (min q (min a.t (a.j/2))+1),
   Fin (min (q-e₂.val) (a.j - 2*e₂.val)+1)
def exponent (a :nI) (q:ℕ) (e :Slot a q) :Fin 3 →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm ![q-e.1.val-e.2.val,e.2.val,e.1.val]
abbrev abE (a :nI) (q:ℕ) :=Fin (a.b+a.j)×Slot a q
def bfj (a :nI) (α:ao) (q:ℕ) (c:abE a q) (G:Lq) :
    kS :=
  ((G.coeff (exponent a q c.2)).taylor (mD ao kS α)).coeff c.1.val
abbrev Test (a :nI) (q:ℕ) :=Fin ((a.b+a.j - q)*ay8 a q)
def dot (a :nI) (α:ao) (q:ℕ) (w:abE a q→ao) (G:Lq) :
    kS :=
  ∑ c,mD ao kS (w c)*bfj a α q c G
end
end aFN
end
section
namespace aFN
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

open aR jA NR
open scoped Polynomial BigOperators
private abbrev gQ (R:Type*) [oj R] :=lV (Fin 3) R
private def bbH {R:Type*} [oj R] (u v :Fin 3→R) (i:Fin 3) :gQ R :=
 ![c9 (v 0)+MvPolynomial.C (u 0)*lz 0,
   c9 (v 1)+MvPolynomial.C (u 1)*lz 0 +
    c9 (u 0)*lz 1,
   c9 (v 2)+MvPolynomial.C (u 2)*lz 0 +
    c9 (u 1)*lz 1+MvPolynomial.C (u 0)*lz 2] i
private def sW {R:Type*} [oj R] (u v :Fin 3→R) :gQ R →+* gQ R :=
 pL c9 (bbH u v)
private theorem ceO {R:Type*} [oj R] {u r :R} (hr :r*u=1)
  (x p:gQ R) :
  p+MvPolynomial.C u*(c9 r*(x - p))=x := by
 rw [← z8 (c9 u) (c9 r),← oq,v9 u r,
  hr,map_one,sH]
 ring
private theorem dsC {R:Type*} [oj R] (u v :Fin 3→R)
   (hu:IsUnit (u 0)) :vw (sW u v) := by
 obtain ⟨r,hr⟩:=isUnit_iff_exists_inv'.mp hu
 let k₀:gQ R:=c9 (v 0)
 let x₀:=c9 r*(lz (0:Fin 3) - k₀)
 let k₁:=c9 (v 1)+MvPolynomial.C (u 1)*x₀
 let x₁:=c9 r*(lz (1 :Fin 3) - k₁)
 let k₂:=c9 (v 2)+MvPolynomial.C (u 2)*x₀+MvPolynomial.C (u 1)*x₁
 let x₂:=c9 r*(lz (2 :Fin 3) - k₂)
 let ψ:gQ R →+* gQ R:=pL c9 ![x₀,x₁,x₂]
 have h:ψ.comp (sW u v)=vG _:= by
   apply pQ
   · intro c
     simp [ψ,sW]
   · intro i
     fin_cases i
     · simpa [ψ,sW,bbH] using ceO hr (lz 0) k₀
     · simpa [ψ,sW,bbH] using ceO hr (lz 1) k₁
     · simpa [ψ,sW,bbH] using ceO hr (lz 2) k₂
 have hleft:Function.LeftInverse ψ (sW u v) := fun p=>oy h p
 exact hleft.injective
private theorem b8z {R S:Type*} [oj R] [oj S] (f :R →+* S)
   (u v :Fin 3→R) :
   (oY f).comp (sW u v) =
     (sW (f ∘ u) (f ∘ v)).comp (oY f) := by
 apply pQ
 · intro c
   simp [sW]
 · intro i
   fin_cases i <;> simp [sW,bbH]
private theorem dsy {R:Type*} [oj R] (t:R) (n:ℕ)
  (u v :Fin 3→R) (hu:qx t (u 0)) (G:gQ R) :
  c9 t^n∣sW u v G↔c9 t^n∣G:= by
 let I:Ideal R:=Ideal.span {t^n}
 let f :=Ideal.Quotient.mk I
 have hf (x :R) :f x=0↔t^n∣x :=
  Ideal.Quotient.eq_zero_iff_mem.trans UY
 have hu' : IsUnit (f (u 0)) := by
  obtain ⟨c,d,h⟩:=hu.pow_left (m:=n)
  refine isUnit_iff_exists_inv'.mpr ⟨f d,?_⟩
  have hm:=nq f h
  simpa only [qy ,oq,map_one,(hf (t^n)).mpr dvd_rfl,mul_zero,qJ] using hm
 have hmap :=oy (b8z f u v) G
 simp only [qm] at hmap
 simp only [← xI,MvPolynomial.C_dvd_iff_map_hom_eq_zero f _ hf,hmap]
 exact (injective_iff_map_eq_zero' _).mp (dsC (f ∘ u) (f ∘ v) hu') _
private theorem emi {R:Type*} [oj R] (x :R) (u:R[X]) :
   oK 2 ((lJ-Polynomial.C x)*u) =
     oK 1 u+(lJ-Polynomial.C x)*oK 2 u:= by
 rw [Polynomial.hasseDeriv_mul]
 simp [show 2=1+1 from rfl,Finset.Nat.antidiagonal_succ,
   Polynomial.hasseDeriv_X,PM,Polynomial.hasseDeriv_one,
   wY]
private def aVo (u:kS[X]) (i:Fin 3) :kS[X] :=
 oK i.val u
private theorem fXa {Γ s} (P:jF Γ s) (L:kH P)
    (α:ao) (z₀:kS) (u v :kS[X])
    (hH :jH P.H=O8 α*u)
    (hres :ahH L.numerator L.denominator=lI z₀+O8 α*v)
    (F:jK) :
    restore P L F =
      sW (aVo u) (aVo v) (canonical (O8 α) (GV z₀ F)) := by
  let f :jK →+* Lq :=
    pL (MvPolynomial.C.comp (sS (mD ao kS)))
      (fun i:mA=>i.elim
        (c9 (lI (mD ao[X] kS lJ)))
        (ar9 P L))
  let g:=(sW (aVo u) (aVo v)).comp
    ((canonical (O8 α)).comp (GV z₀))
  have h:f=g:= by
    apply pQ
    · intro c
      simp [f,g,sW,canonical,GV]
    · intro i
      cases i with
      | none=>simp [f,g,sW,canonical,GV]
      | some i =>
        fin_cases i <;>
          simp [f,g,sW,bbH,canonical,aTo,GV,aVo,ar9,
            qG,hH,hres,O8,JK,
            PM,emi] <;> ring
  exact oy h F
private theorem eval_lift (p:ao[X]) (α:ao) :
  (jH p).eval (mD ao kS α)=mD ao kS (p.eval α) := by
 exact Polynomial.eval_map_apply (mD ao kS) α
private theorem cM8 {p H :ao[X]} {α:ao} (hc:qx p H)
  (hroot :H.IsRoot α) :p.eval α≠0:= by
 obtain ⟨u,v,hu⟩:=hc
 intro hp
 have h:=nq (pU α) hu
 simp [hp,show H.eval α=0 from hroot] at h
private theorem edX {Γ s} (P:jF Γ s) (L:kH P) (α:ao)
    (hroot :P.H.IsRoot α) :
    ∃ N D:ao[X],D ≠0∧N.natDegree≤1∧D.natDegree≤1 ∧
      (ahH L.numerator L.denominator).eval (mD ao kS α) =
        mD ao[X] kS N/mD ao[X] kS D:= by
  let N :ao[X] := -Polynomial.X*lI (P.q.eval α)
  let D:ao[X] :=lI (P.c.eval α) *
    (lI (P.a₀.eval α)+Polynomial.X*lI (P.a₁.eval α))
  have hD:D ≠0:= by
    intro h
    have he :=nq (pU 0) h
    simp [D,cM8 P.c_unit hroot,cM8 P.a₀_unit hroot] at he
  have hNdeg:N.natDegree≤1 := by
    simpa [N,neg_mul] using SC (lJ:ao[X]) (P.q.eval α)
  have hDdeg:D.natDegree≤1 := by
    refine (KA _ _).trans ((Polynomial.natDegree_add_le _ _).trans (vH ?_ ?_))
    · simp
    · exact (SC _ _).trans (by simp)
  refine ⟨N,D,hD,hNdeg,hDdeg,(eq_div_iff ?_).mpr ?_⟩
  · exact (Fz _ (vh ao[X] kS)).mpr hD
  have h:=Polynomial.eval_dvd (x :=mD ao kS α) L.generic_congruence
  have hz :P.H.eval α=0:=hroot
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,eval_lift,
    hz,xu,zero_dvd_iff] at h
  have hC (a :ao) :mD ao[X] kS (lI a) =
      algebraMap ao kS a := by
    rw [← Polynomial.algebraMap_eq,← yU]
  simp only [N,D,oq,qy ,map_neg,hC]
  linear_combination h
theorem eFi {Γ s} (P:jF Γ s) (L:kH P) (α:ao)
    (hroot :P.H.IsRoot α) (hsimple :P.H.derivative.eval α≠0) :
    ∃ N D:ao[X],D ≠0∧N.natDegree≤1∧D.natDegree≤1 ∧
      ∀ (a :nI) (F:jK),
        F∈amn P L a (O8 α) ↔
          (c9 (O8 α) :Lq)^(a.b+a.j) ∣
            canonical (O8 α)
              (GV (mD ao[X] kS N/mD ao[X] kS D) F) := by
  obtain ⟨N,D,hD,hNdeg,hDdeg,hcent⟩:=edX P L α hroot
  refine ⟨N,D,hD,hNdeg,hDdeg,fun a F => ?_⟩
  let u₀:=P.H /ₘ (lJ-Polynomial.C α)
  have hu₀: (lJ-Polynomial.C α)*u₀=P.H :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hH :jH P.H=O8 α*jH u₀:= by
    have h:=nq (sS (mD ao kS)) hu₀.symm
    simpa [jH,O8] using h
  have hcop:qx (O8 α) (jH u₀) := by
    have h:=Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero P.H α hsimple
    simpa [O8,jH,u₀] using h.map (sS (mD ao kS))
  let z₀:=mD ao[X] kS N/mD ao[X] kS D
  have hres :O8 α∣ahH L.numerator L.denominator-Polynomial.C z₀ :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot,hcent,z₀])
  obtain ⟨v,hv⟩:=hres
  have hres' : ahH L.numerator L.denominator=lI z₀+O8 α*v := by
    linear_combination hv
  rw [aVU,fXa P L α z₀ (jH u₀) v hH hres' F]
  exact dsy (O8 α) (a.b+a.j) (aVo (jH u₀)) (aVo v)
    (by simpa [aVo,JK] using hcop) _
end
end aFN
end
section
namespace aA0
noncomputable section
open K1 aR jA
open scoped Polynomial PowerSeries
abbrev atU:=kS[X]
abbrev bbm:=lV (Fin 3) atU
def seed :kS:=mD ao[X] kS lJ
private def aXx :ao[X] →+* G6 kS :=
 x7 (PowerSeries.C.comp (mD ao kS))
  (u5 seed+PowerSeries.X)
private theorem cHW :
   PowerSeries.constantCoeff.comp aXx=mD ao[X] kS:= by
 apply C4
 · intro a
   simp [aXx,yU ao ao[X] kS]
 · simp [aXx,seed]
private theorem dcJ (p:nonZeroDivisors ao[X]) :
  IsUnit (aXx p.val) := by
 rw [PowerSeries.isUnit_iff_constantCoeff]
 change IsUnit ((PowerSeries.constantCoeff.comp aXx) p.val)
 rw [cHW]
 exact isUnit_iff_ne_zero.mpr ((Fz _ (vh ao[X] kS)).2
  (nonZeroDivisors.coe_ne_zero p))
private def bNB:kS →+* G6 kS :=
 IsLocalization.lift dcJ
private theorem coY (p:ao[X]) :
  bNB (mD ao[X] kS p)=aXx p :=
 IsLocalization.lift_eq dcJ p
private theorem dPa :
  PowerSeries.constantCoeff.comp bNB=vG kS:= by
 apply IsLocalization.ringHom_ext (nonZeroDivisors ao[X])
 exact RingHom.ext fun p=> by
  simp only [qm,coY,RingHom.id_apply]
  exact Gk cHW p
def expand:atU →+* G6 atU :=
  x7 ((PowerSeries.map lI).comp bNB)
    (u5 lJ)
theorem dO6 (p:atU) :
    Mk (expand p)=p:= by
  have h:PowerSeries.constantCoeff.comp expand=vG atU:= by
    apply C4
    · intro k
      have hk :=Gk dPa k
      change Mk (expand (lI k))=lI k
      simp only [expand,Polynomial.coe_eval₂RingHom,Pr,qm]
      rw [← Qy ,PowerSeries.coeff_map,
        Qy]
      exact nq lI hk
    · simp [expand]
  exact Gk h p
theorem d49 (p:ao[X]) :expand (jH p)=u5 (jH p) := by
  let f :=sS (mD ao kS)
  have h:expand.comp f=PowerSeries.C.comp f := by
    apply C4
    · intro r
      have hr :bNB (mD ao kS r) =
          u5 (mD ao kS r) := by
        have hc:mD ao[X] kS (lI r) =
            algebraMap ao kS r :=
          (yU ao ao[X] kS r).symm
        simpa [hc,aXx] using coY (lI r)
      simp [f,expand,hr]
    · simp [f,expand]
  exact Gk h p
theorem d5b :
  expand (lI seed)=u5 (lI seed)+PowerSeries.X:= by
 simp [expand,seed,coY,aXx]
@[simp] theorem bLl {A:Type*} [Aa A] (a b:A) :
   EK a (u5 b)=u5 b:= by
  ext n
  cases n <;> simp
theorem c8o {A:Type*} [Aa A] (a :A) :
  EK a PowerSeries.X=u5 a*PowerSeries.X:= by
 ext n
 simp only [PowerSeries.coeff_rescale,PowerSeries.coeff_C_mul,PowerSeries.coeff_X]
 split_ifs with h <;> simp [h]
theorem d5a (a p:atU) :
   ∃ d:G6 atU,
     EK a (expand p)=u5 p+PowerSeries.C a*d:= by
 obtain ⟨d,hd⟩:=(PowerSeries.X_dvd_iff).2
   (show Mk (expand p-PowerSeries.C p)=0 by
     simp [dO6])
 refine ⟨PowerSeries.X*EK a d,?_⟩
 have h:=nq (EK a) hd
 rw [zS ,bLl,oq,c8o,z8] at h
 rw [wY ,← sub_eq_iff_eq_add]
 exact h
end
end aA0
end
section
namespace aw9
open Rj
open scoped BigOperators
set_option maxHeartbeats 600000
private theorem cup (w:ℤ) :2*sG w=w*(w+1) := by
 unfold sG
 apply FR
 rcases (show w % 2=0∨w % 2=1 by omega) with h | h
 · have hw:w=2*(w/2) := by omega
   exact Vz  (by rw [hw]; exact VH  _ _) _
 · have hw:w+1=2*(w/2+1) := by omega
   exact VC  (show (2 :ℤ)∣w+1 from ⟨w/2+1,hw⟩) w
private theorem dQj (w:ℤ) :cost w=(w+1)^2/4 := by
 have h:4*cost w=(w+1)^2 - (w+1) % 2 := by
  unfold cost
  rcases (show w % 2=0∨w % 2=1 by omega) with h | h
  · have hw:w=2*(w/2) := by omega
    have hu: (w+1)/2=w/2 := by omega
    have hp: (w+1) % 2=1 := by omega
    rw [hu,hp]
    conv_rhs=>rw [hw]
    ring
  · have hw:w=2*(w/2)+1 := by omega
    have hu: (w+1)/2=w/2+1 := by omega
    have hp: (w+1) % 2=0:= by omega
    rw [hu,hp]
    conv_rhs=>rw [hw]
    ring
 omega
private theorem a2L {a w:ℤ} (ha :a≤(w+1)/2) (hw:0≤w) :
   yC ⟨a,w⟩=cost w:= by
 have hu:0≤(w+1)/2 := by omega
 have hv : (w+1)/2≤w:= by omega
 unfold yC cost
 simp only [oZ ha,oZ hu,oZ hv]
 have h₁:=cup ((w+1)/2)
 have h₂:=cup (w-(w+1)/2)
 have he :w-(w+1)/2=w/2 := by omega
 rw [he] at h₂ ⊢
 rcases (show w % 2=0∨w % 2=1 by omega) with h | h
 · have h' : (w+1)/2=w/2 := by omega
   rw [h'] at h₁ ⊢
   nlinarith only [h₁,h₂]
 · have h' : (w+1)/2=w/2+1 := by omega
   rw [h'] at h₁ ⊢
   nlinarith only [h₁,h₂]
private theorem d3w (s :ℤ) :
  sG (2*s+1) - cost (2*s)=(s+1)^2 := by
 have h:=cup (2*s+1)
 unfold cost
 rw [show (2*s+1)/2=s by omega,show 2*s/2=s by omega]
 nlinarith only [h]
private theorem bnD (q k :ℕ) (hq:2300≤q) :
   Bb q (aU k)=nX k := by
 have hd:iO q=2300:=vl hq
 have harg :min (2300:ℤ) (-offset k - 1)=2300 - k - 1 := by
   unfold aU
   rw [vl (by omega)]
   ring
 have hval :gd 2300 2300=1324801 := by decide
 unfold Bb nX
 rw [hd,harg]
 change gd 2300 2300 - gd 2300 (2300-(k :ℤ) - 1)= _
 rw [hval]
 by_cases hk :k<2300
 · have hnon : ¬ (2300-(k :ℤ) - 1)<0:= by omega
   have hclip:min (2300-(k :ℤ) - 1) 4600=2300-(k :ℤ) - 1 :=
     zm  (by omega)
   have hmax :max (0:ℤ) (2300 - k - 1 - 2300)=0:=zf  (by omega)
   rw [oZ  (show 0≤2300-(k :ℤ) by omega),dQj]
   simp only [gd,hnon,ite_false,show (2*2300:ℤ)=4600 by decide,
     hclip,hmax,show sG 0=0 by decide,wR ]
   rw [show 2300-(k :ℤ) - 1+2=2300 - k+1 by ring]
 · have hneg: (2300-(k :ℤ) - 1)<0:= by omega
   simp [gd,hneg,zf  (show 2300-(k :ℤ)≤0 by omega),cost]
private theorem cIm {w:ℤ} (hw:0≤w) :0≤ cost w:= by
 exact v8 (by omega) (by omega)
private theorem cG3 {k :ℤ} (hk :0≤k) :0≤ nX k := by
 let w:=max 0 (2300 - k)
 have h₀:0≤w:=C5 _ _
 have h₁:w≤2300:=vH (by omega) (by omega)
 unfold nX cost
 change 0≤1324801-((w+1)/2)*(w/2+1)
 have h:=mul_le_mul (show (w+1)/2≤1151 by omega)
  (show w/2+1≤1151 by omega) (show 0≤w/2+1 by omega) (by omega)
 omega
private theorem eOW {a b a' b' s :ℤ} (hab:a≤b) (hb:b≤1151)
   (hb₀:0≤b) (ha' : 0≤a') (hb' : 0≤b') (hs₀:0≤ s) (hs₁:s≤1150)
   (hra :a - s≤a') (hrb:b - s≤b') :
   a*b-a' * b' ≤ 1324801-(1151 - s)^2 := by
 by_cases hsa :s≤a
 · have h:=mul_le_mul hra hrb (show 0≤b - s by omega) ha'
   have h' := Vs  (show a+b≤2302 by omega) hs₀
   nlinarith only [h,h']
 · have h:=mul_le_mul (show a≤ s by omega) hb hb₀ hs₀
   have h' := v8  ha' hb'
   have h'' := v8  hs₀ (show 0≤1151 - s by omega)
   nlinarith only [h,h',h'']
private theorem gqE {k n m t:ℤ} (hk :0≤k) (hn:0≤n) (hm:0≤ m)
   (hs :n+m≤1150) (hP:0≤2300 - k - 2*n - m) (hO:0≤t - n - 2*m) :
   0≤ nX k+cost (2300 - k - 2*n - m)+cost (t - n - 2*m) -
     (1151 - n - m)^2 := by
 let w:=2300 - k
 let v :=w - 2*n - m
 let s :=n+m
 have hv :0≤v :=hP
 have hw:0≤w:= by dsimp [w,v] at *; omega
 have hws :w≤2300:= by dsimp [w]; omega
 have hs₀:0≤ s := by dsimp [s]; omega
 have hs₁:s≤1150:=hs
 have hO' := cIm hO
 unfold nX
 rw [oZ hw]
 rw [show 1151 - n - m=1151 - s by dsimp [s]; ring]
 change 0≤1324801 - cost w+cost v+cost (t - n - 2*m)-(1151 - s)^2
 let a :=(w+1)/2
 let b:=w/2+1
 let a' := (v+1)/2
 let b' := v/2+1
 change 0≤1324801-a*b+a' * b' + cost (t - n - 2*m)-(1151 - s)^2
 have h:=eOW (show a≤b by dsimp [a,b]; omega)
   (show b≤1151 by dsimp [b]; omega) (show 0≤b by dsimp [b]; omega)
   (show 0≤a' by dsimp [a']; omega) (show 0≤b' by dsimp [b']; omega)
   hs₀ hs₁ (show a - s≤a' by dsimp [a,a',s,v]; omega)
   (show b - s≤b' by dsimp [b,b',s,v]; omega)
 nlinarith only [h,hO']
private def product (n m:ℕ) (i:Fin 6) :ℕ :=
 if i=0∨i=3 then n else if i=5 then m else 0
def powers (q k :ℕ) :kJ :=
 let t:=Ic q (aU k)
 product (RZ k t).toNat (PO k t).toNat
private theorem a6V (n m:ℕ) (f :Fin 6→ℤ) :
  (∑ i,(product n m i:ℤ)*f i) =
    (n:ℤ)*(f 0+f 3)+(m:ℤ)*f 5:= by
 simp [JM,product,Fin.succ,t7,vk]
private theorem bGO {q k :ℕ} (hq:2300≤q) :
   pT q (aU k) =
     ![⟨0,2300-(k :ℤ)⟩,⟨1150,2300⟩,⟨0,Ic q (aU k)⟩] := by
 have hd:iO q=2300:=vl hq
 have h : -offset k=2300-(k :ℤ) := by unfold aU; ring
 unfold pT
 dsimp only
 rw [hd,h]
 norm_num
private theorem bVK {q k :ℕ} (t:ℤ) (ht:Ic q (aU k)=t)
    (hpos :0<t) (p:kJ) (r :ℤ) (hr :0≤ r)
    (h:Bb q (aU k) -
      max 0 (max (m5 (iO q) (pT q (aU k)))
        (m5 (K6 q p) (D8 q (aU k) p)))≤ r) :
    (xR q (aU k) p:ℤ)≤ r := by
  rw [xR,ht,p5 (G4 hpos),J4]
  exact vH h hr
theorem dzk {q k :ℕ} (hq:2300≤q) :
   (xR q (aU k) (powers q k) :ℤ)≤ nX k := by
 by_cases h:Ic q (aU k)≤0
 · simpa [xR,h] using cG3 (Ea k)
 refine bVK _ rfl (lt_of_not_ge h) _ _ (cG3 (Ea k)) ?_
 rw [bnD q k hq]
 exact sub_le_self _ (C5 _ _)
theorem dzl {q k :ℕ} (hq:2300≤q) {t:ℤ}
   (ht:Ic q (aU k)=t) (hpos :0<t) :
   (xR q (aU k) (powers q k) :ℤ)≤ cost t:= by
 have hkP:yC ⟨0,2300-(k :ℤ)⟩=cost (max 0 (2300-(k :ℤ))) := by
   by_cases hk :0≤2300-(k :ℤ)
   · rw [oZ hk,a2L (by omega) hk]
   · have hhalf : (2300-(k :ℤ)+1)/2≤0:= by omega
     simp [yC,zf  (le_of_not_ge hk),zf  hhalf,sG,cost]
 have hQ:yC ⟨1150,2300⟩=1323650:= by decide
 have hO:yC ⟨0,t⟩=cost t:=a2L (by omega) (by omega)
 have hd:iO q=2300:=vl hq
 have hbase :m5 (iO q) (pT q (aU k))=nX k - cost t:= by
   rw [hd,bGO hq,ht,m5,qG]
   rw [p5 (show ¬ (↑(2300:ℕ) :ℤ)<0 by decide)]
   change sG 2301-(yC ⟨0,2300-(k :ℤ)⟩ +
     yC ⟨1150,2300⟩+yC ⟨0,t⟩)= _
   rw [hkP,hQ,hO]
   unfold nX
   norm_num [sG]
   ring
 refine bVK t ht hpos _ _ (cIm (le_of_lt hpos)) ?_
 rw [bnD q k hq]
 have h:nX k - cost t≤ max 0 (max (m5 (iO q)
     (pT q (aU k))) (m5 (K6 q (powers q k))
     (D8 q (aU k) (powers q k)))) := by
   rw [← hbase]
   exact (C5 _ _).trans (u9 _ _)
 omega
theorem dsl {both:Bool} {k l r t:ℤ} (ha :t6 both k l r)
  (hl:l≤t) (hr :t≤ r) :t6 both k t t:= by
 cases both <;> simp [t6,azu,RZ,PO] at ha ⊢ <;> omega
theorem dzu {q k :ℕ} (hq:2300≤q) {t:ℤ}
    (ht:Ic q (aU k)=t) (hpos :0<t) {both:Bool}
    (ha :t6 both k t t) :
    (xR q (aU k) (powers q k) :ℤ)≤aJt both k t:= by
  let n:=azu both k t
  let m:=PO k t
  obtain ⟨hlin,hm,hs,hP,hO⟩:=ha
  have hn:0≤n:= by
    cases both
    · exact uh
    · exact hlin
  have hs' : n+m≤1150:=hs
  have hnc: ((RZ k t).toNat :ℤ)=n:= by
    cases both
    · exact N0 hlin ▸ rfl
    · exact G3 hlin
  have hmc: (m.toNat :ℤ)=m:=G3 hm
  have hp:powers q k=product n.toNat m.toNat := by
    unfold powers
    rw [ht,← hnc,Int.toNat_natCast]
  have hnc' : (n.toNat :ℤ)=n:=G3 hn
  have hd:iO q=2300:=vl hq
  have hd' : K6 q (powers q k)=2*(1150 - n - m) := by
    rw [hp,K6,hd,a6V,hnc',hmc]
    norm_num [yE]
    ring
  have hP' : D8 q (aU k) (powers q k) 0 =
      ⟨-n - m,2300 - k - 2*n - m⟩:= by
    simp [hp,D8,a6V,hnc',hmc,bGO hq,Jd]
    constructor <;> first | trivial | ring
  have hQ' : D8 q (aU k) (powers q k) 1 =
      ⟨1150 - n - m,2*(1150 - n - m)⟩:= by
    simp [hp,D8,a6V,hnc',hmc,bGO hq,Jd]
    constructor <;> first | trivial | ring
  have hO' : D8 q (aU k) (powers q k) 2=⟨-n - m,t - n - 2*m⟩:= by
    simp [hp,D8,a6V,hnc',hmc,bGO hq,Jd,ht]
    constructor <;> first | trivial | ring
  have hker :m5 (K6 q (powers q k)) (D8 q (aU k) (powers q k)) =
      (1151 - n - m)^2 - cost (2300 - k - 2*n - m) - cost (t - n - 2*m) := by
    rw [m5,hd',ite_eq_right (show ¬ 2*(1150 - n - m)<0 by omega),
      qG ,hP',hQ',hO']
    rw [a2L (by omega) hP,a2L (by omega) (by omega),
      a2L (by omega) hO]
    have h:=d3w (1150 - n - m)
    nlinarith only [h]
  refine bVK t ht hpos _ _ (gqE (Ea k) hn hm hs' hP hO) ?_
  have hle :m5 (K6 q (powers q k)) (D8 q (aU k) (powers q k)) ≤
      max 0 (max (m5 (iO q) (pT q (aU k)))
        (m5 (K6 q (powers q k)) (D8 q (aU k) (powers q k)))) :=
    (u9 _ _).trans (u9 _ _)
  calc
    _≤Bb q (aU k) -
        m5 (K6 q (powers q k)) (D8 q (aU k) (powers q k)) :=
      G1 hle _
    _ = _:= by
      rw [hker,bnD q k hq]
      change _=nX k+cost (2300 - k - 2*n - m)+cost (t - n - 2*m) -
        (1151 - n - m)^2
      ring
end aw9
end
section
namespace acZ
noncomputable section
open K1 aR jA
open scoped BigOperators
structure asW (moving:Bool) (A:pG ko) :Prop where
 different: (↑A:Set ko).Pairwise (fun f g => ¬ Associated f g)
 irreducible : ∀ f∈A,FU f
 Bo : ∀ f∈A,0<vC f
 seed : ∀ f∈A,if moving then 0<gY f else gY f=0
def aaP (A:pG ko) :ko := ∏ f∈A,f
end
end acZ
end
section
namespace acZ
noncomputable section
open aR jA
open scoped Polynomial BigOperators
private def a7b:ko →+* iP[X] :=
 pL lI (fun i=>i.elim lJ (fun _=>0))
private theorem c5R {F:ko} (hF:vC F=0) :
    YB (a7b F)=F:= by
  let φ:=(x7 c9 (lz (none :mA))).comp a7b
  change φ F=(vG _) F
  apply MvPolynomial.hom_congr_vars
  · ext a
    simp [φ,a7b]
  · intro i hi
    cases i with
    | none=>simp [φ,a7b]
    | some j =>
      have hd:=MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi
      apply False.elim
      apply hd
      apply Nat.eq_zero_of_le_zero
      exact (MvPolynomial.degreeOf_le_weightedTotalDegree
        (fun i:mA=>i.elim 0 (fun _=>1)) (some j) (show 0<1 by decide) F).trans_eq hF
  · rfl
private theorem dtl (p:iP[X]) :
   qN (YB p)=p.map MvPolynomial.C:= by
 let e :=(xW iP (Fin 3)).toRingHom
 let l:=e.comp (x7 c9 (lz none))
 let r :=sS (c9:iP →+* p6)
 have h:l=r := by
   apply C4
   · intro x
     simp [l,r,e,zh]
   · simp [l,r,e,LO]
 exact oy h p
private theorem c5S {p:iP[X]} {F:ko} (hF:F≠0)
  (hp:YB p∣F) :p.natDegree≤gY F:= by
 let e :=xW iP (Fin 3)
 have hmap :qN (YB p)∣qN F:=map_dvd e.toRingHom hp
 have hne :qN F≠0:=(Fz e e.injective).mpr hF
 have h:=SM hmap hne
 rw [dtl,Nr (MvPolynomial.C_injective (Fin 3) iP)] at h
 simpa only [qN,SL,gY] using h
private theorem cEa {a :nI} {F Q:ko} (hF:F≠0)
    (hCap:Jn a F) (hQ:Q∣F) :Jn a Q:= by
  classical
  refine ⟨(Gi _ hQ hF).trans hCap.1,
    (Gi _ hQ hF).trans hCap.2.1,?_,?_⟩
  · simpa only [uz] using
      (Gi (zR (some 2 :mA) 1) hQ hF).trans
        (by simpa only [uz] using hCap.2.2.1)
  · simpa only [gY,uz] using
      (Gi (zR (none :mA) 1) hQ hF).trans
        (by simpa only [gY,uz] using hCap.2.2.2)
end
end acZ
end
section
namespace acZ
noncomputable section
open K1 aR jA
open scoped Polynomial BigOperators
def Bu:jK →ₗ[ao] ko :=
 (LQ (IsScalarTower.toAlgHom ao ao[X] iP)).toLinearMap
@[simp] theorem cfL (F:jK) :Bu F=bC F:=rfl
theorem aFf :vw bC :=
 MvPolynomial.map_injective _ (vh ao[X] iP)
theorem agr {F:jK} (hF:F≠0) :bC F≠0:= by
 intro h
 exact hF (aFf (h.trans (Bu.map_zero.symm)))
def OV (a :nI) :u8 iP ko :=
 yQ (fun i:mA=>i.elim 0 (fun _=>1)) a.b ⊓
 yQ (fun i:mA=>i.elim 0 Eg) a.j ⊓
 yQ (zR (some 2 :mA) 1) a.t ⊓
 yQ (zR (none :mA) 1) 70000
theorem bI3 {a :nI} {F:ko} :
  F∈OV a↔Jn a F:= by
 classical
 simp only [OV,TI,
  MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
  uz ,Jn,vC,lP,gY]
 tauto
theorem a88 {a :nI} {F:jK} (h:Jn a F) :
  Jn a (bC F) := by
 have hs : (bC F).support=F.support :=
  TZ F (vh ao[X] iP)
 simpa only [Jn,vC,lP,gY,zg ,
  RC,hs] using h
theorem bJg (F:jK) :aox 0 F=F:= by
 let ev :lV mA jK →+* jK :=
   pL (vG _) (fun _=>0)
 let shift:jK →+* lV mA jK :=
   pL (MvPolynomial.C.comp c9)
     (fun i=>lz i+MvPolynomial.C (lz i))
 have hev (Q:lV mA jK) :ev Q= Q.coeff 0:= by
   simp [ev,PD]
 have hcomp:ev.comp shift=vG jK:= by
   apply pQ <;> intro i <;> simp [ev,shift]
 change (shift F).coeff 0=F
 rw [← hev]
 exact oy hcomp F
private abbrev aYU:=lV mA jK
private def aFA (v :mA→ℕ) (d:ℕ) (R:aYU) :Prop :=
 ∀ a,R.coeff a∈yQ v d
private theorem bXv {v :mA→ℕ} {d e :ℕ} {R S:aYU}
  (hR:aFA v d R) (hS:aFA v e S) :aFA v (d+e) (R*S) := by
 classical
 intro a
 rw [MvPolynomial.coeff_mul]
 exact Nj _ fun b _=>MvPolynomial.mul_mem_restrictWeightedDegree (hR b.1) (hS b.2)
private theorem bCQ {v :mA→ℕ} {d:ℕ} {F:jK}
   (hF:F∈yQ v d) :
   aFA v d (c9 F) := by
 classical
 intro a
 rw [MvPolynomial.coeff_C]
 split
 · exact hF
 · exact Il _
private theorem dL2 {v :mA→ℕ} {d:ℕ} {R:aYU}
   (hR:aFA v d R) (n:ℕ) :aFA v (n*d) (R^n) := by
 induction n with
 | zero =>
   rw [y5 ,Nat.zero_mul,← Dv]
   apply bCQ
   rw [← Dv]
   exact G9 v 0 _
 | succ n ih =>
   rw [Dz ,KH]
   exact bXv ih hR
private theorem dL3 {ι:Type*} {v :mA→ℕ} (s :pG ι)
   (d:ι→ℕ) (R:ι→aYU) (h : ∀ i∈s,aFA v (d i) (R i)) :
   aFA v (∑ i∈s,d i) (∏ i∈s,R i) := by
 classical
 induction s using R9 with
 | empty =>
   simp only [Finset.sum_empty,Finset.prod_empty,← Dv]
   exact bCQ (G9 v 0 _)
 | insert i s hi ih =>
   rw [Ob hi,Finset.prod_insert hi]
   exact bXv (h i (Qw _ _))
     (ih fun j hj=>h j (Pk hj))
theorem bfD (v :mA→ℕ) (a :mA →₀ ℕ)
    (F:jK) :
    (aox a F).weightedTotalDegree v≤F.weightedTotalDegree v := by
  classical
  let g:mA→aYU:= fun i=>lz i+MvPolynomial.C (lz i)
  have hg (i:mA) :aFA v (v i) (g i) := by
    intro b
    change (lz i:aYU).coeff b +
      (c9 (lz i) :aYU).coeff b∈_
    apply Sd
    · rw [UP]
      split
      · rw [← Dv]
        exact G9 v (v i) _
      · exact Il _
    · exact bCQ (MvPolynomial.X_mem_restrictWeightedDegree v (v i) i uh) b
  apply MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  change (KI (MvPolynomial.C.comp c9) g F).coeff a∈_
  rw [MvPolynomial.eval₂_eq,EP]
  apply Nj
  intro m hm
  have hp:=dL3 m.support (fun i=>m i*v i) (fun i=>g i^m i)
    (fun i _=>dL2 (hg i) (m i))
  have hC:aFA v 0 (c9 (c9 (F.coeff m))) :=
    bCQ (G9 v 0 _)
  have hP:=bXv hC hp a
  apply MvPolynomial.restrictWeightedDegree_mono v _ hP
  rw [Ee]
  simpa only [JW,Finsupp.sum,sI] using
    vj v hm
theorem c0r (a :mA →₀ ℕ) (F:jK) (hF:Jn Ga F) :
    Jn Ga (aox a F) := by
  classical
  obtain ⟨hb,hj,ht,hs⟩:=hF
  refine ⟨(bfD _ a F).trans hb,
    (bfD _ a F).trans hj,?_,?_⟩
  · simpa only [uz] using
      (bfD (zR (some 2 :mA) 1) a F).trans
        (by simpa only [uz] using ht)
  · simpa only [gY,uz] using
      (bfD (zR (none :mA) 1) a F).trans
        (by simpa only [gY,uz] using hs)
end
end acZ
end
section
namespace acZ
noncomputable section
open jA
open scoped BigOperators
set_option maxHeartbeats 650000
private abbrev Exponent:=mA →₀ ℕ
private def aei (q:ℕ×ℕ×ℕ×ℕ) :Exponent :=
 Finsupp.equivFunOnFinite.symm (fun i=>i.elim q.2.2.2 (![q.2.2.1,q.2.1,q.1] ·))
private theorem dgc {k :ℕ} (hk :k≤1150) :
    (∑ j∈cy (2301 - 2*k),(6821 - k - j))=(2301 - 2*k)*5671 := by
  let n:=2301 - 2*k
  have hpair : (∑ j∈cy n,(6821 - k - j)) +
      (∑ j∈cy n,(6821 - k-(n - 1 - j)))=n*(5671+5671) := by
    rw [← zk]
    calc
      _ = ∑ _∈cy n,(5671+5671) := by
        refine n5 rfl fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        dsimp [n] at hj' ⊢
        omega
      _ = _:= by simp
  let s := ∑ j∈cy n,(6821 - k - j)
  have hs : (∑ j∈cy n,(6821 - k-(n - 1 - j)))=s :=
    z9 (fun j=>6821 - k - j) n
  rw [hs,FK] at hpair
  change s+s=n*5671+n*5671 at hpair
  change s=n*5671
  omega
private theorem gwW (n:ℕ) : (∑ k∈cy n,(2*k+1))=n^2 := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [t3 ,ih]
   ring
private theorem dfZ (a :ℕ) :
   (∑ k∈Finset.Ico a 1151,(2301 - 2*k))=(1151-a)^2 := by
 rw [Finset.sum_Ico_eq_sum_range]
 let n:=1151-a
 calc
   _ = ∑ k∈cy n,(2*(n - 1 - k)+1) := by
     refine n5 rfl fun k hk => ?_
     have hk' := Finset.mem_range.mp hk
     dsimp [n] at hk' ⊢
     omega
   _ = _:= by
     rw [z9 (fun k=>2*k+1) n,gwW]
private theorem c6G {σ 𝕜:Type*} [Field 𝕜]
   (A:pG (σ →₀ ℕ)) {r :ℕ} (e :Fin r→lV σ 𝕜)
   (he :yo 𝕜 e)
   (h : ∀ R∈Submodule.span 𝕜 (Set.range e),R≠0 → ∃ m∈A,R.coeff m≠0) :
   r≤A.card:= by
 classical
 let V:=Submodule.span 𝕜 (Set.range e)
 let proj:lV σ 𝕜 →ₗ[𝕜] (↥A→𝕜) :=
   FV fun m=>MK 𝕜 m.val
 let L:=proj.comp V.subtype
 have hker :uJ L = ⊥ := by
   apply LinearMap.ker_eq_bot'.mpr
   intro R hR
   apply Subtype.ext
   change R.val=0
   by_contra hn
   obtain ⟨m,hm,hcoeff⟩:=h R.val R.property hn
   exact hcoeff (GB hR ⟨m,hm⟩)
 have hli:yo 𝕜
     (fun i=>(⟨e i,Submodule.subset_span (Set.mem_range_self i)⟩:V)) :=
   LinearIndependent.of_comp V.subtype he
 have hr :MO (Fin r)≤oz 𝕜 (↥A→𝕜) :=
   (hli.map' L hker).fintype_card_le_finrank
 simpa only [Fintype.card_fin,Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using hr
end
end acZ
end
section
namespace aw9
open scoped BigOperators
private theorem bh5 (s m n:ℕ) :oD s (m+n)=oD s m+total (s+m) n:= by
 induction n with
 | zero=>simp [total]
 | succ n ih =>
   change oD s (m+n)+aDZ (s+(m+n)) =
    oD s m+(oD (s+m) n+aDZ (s+m+n))
   rw [ih,Nat.add_assoc s m n,vk]
private theorem gDv (s width n:ℕ) :
   oD s (n*width) = ∑ i∈cy n,oD (s+i*width) width := by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [Nat.succ_mul,bh5,Finset.sum_range_succ,ih]
theorem bxY:oD 0 5000=5196036704622 := by
 rw [show 5000=20*250 by decide,gDv 0 250 20]
 simp only [t3 ,S2 ,Nat.reduceMul,Ee,
  gMA,gMB,gMM,gMN,gMO,gMP,gMQ,gMR,gMS,gMT,
  gMC,gMD,gME,gMF,gMG,gMH,gMI,gMJ,gMK,gML]
 norm_num
end aw9
end
section
namespace acZ
open jA
open scoped BigOperators
set_option maxRecDepth 1024
private theorem blocks (e :ℕ) (he :0<e) (q:ℕ→ℕ) (n:ℕ) :
    (∑ t∈cy (n*e),q (t/e))=e * ∑ k∈cy n,q k := by
  induction n with
  | zero=>simp
  | succ n ih =>
    rw [KH,Df ,ih,t3 ,FK]
    congr 1
    calc
      (∑ t∈cy e,q ((n*e+t)/e)) =
          ∑ _∈cy e,q n:= by
        apply n5 rfl
        intro t ht
        have ht' := Finset.mem_range.mp ht
        rw [yB n e,Nat.mul_add_div he,Nat.div_eq_of_lt ht',Nat.add_zero]
      _ = _:= by simp
theorem bZx {W e n:ℕ} (he :0<e) (r q:ℕ→ℕ)
    (h : ∀ t≤W,r t≤q ((W - t)/e)) (hz : ∀ k,n≤k→q k=0) :
    (∑ t∈cy (W+1),r t)≤e * ∑ k∈cy n,q k := by
  calc
    _ ≤ ∑ t∈cy (W+1),q ((W - t)/e) :=
      qM fun t ht=>h t (Ef (Finset.mem_range.mp ht))
    _ = ∑ t∈cy (W+1),q (t/e) := by
      simpa only [Nat.add_sub_cancel] using
        (z9 (fun t=>q (t/e)) (W+1))
    _≤_:= by
      rw [← blocks e he q n]
      by_cases hW:W+1≤n*e
      · exact Finset.sum_le_sum_of_subset_of_nonneg (xL hW) (fun _ _ _=>C9 _)
      · have hs :=Finset.range_mono (show n*e≤W+1 by omega)
        refine (ze  hs ?_).ge
        intro t _ ht
        apply hz
        apply (Nat.le_div_iff_mul_le he).mpr
        exact Nat.le_of_not_gt (fun hlt=>ht (Finset.mem_range.mpr hlt))
private theorem dgb (n:ℕ) :
   6*(∑ k∈cy n,(n - k)^2)=n*(n+1)*(2*n+1) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [Finset.sum_range_succ']
   simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
   rw [FK,ih]
   ring
end acZ
end
section
namespace aFN
set_option backward.isDefEq.respectTransparency false
noncomputable section
open K1 aR jA NR
open scoped Polynomial BigOperators
def c1 :Prop :=
  ∀ (a :nI) (α:ao),
    ∃ w : ∀ q:Fin (a.b+1),Test a q.val→abE a q.val→ao,
      ∀ G:Lq,(∀ e∈G.support,admissible a e) →
        (((c9 (O8 α) :Lq)^(a.b+a.j) ∣
          canonical (O8 α) G) ↔
          ∀ (q:Fin (a.b+1)) (i:Test a q.val),dot a α q.val (w q i) G=0)
private def aCD {a :nI} {q:ℕ}
   (w:abE a q→ao) (p:jK →ₗ[ao] (abE a q→ao[X])) :
   jK →ₗ[ao] ao[X] :=
 ∑ c,w c•((LinearMap.proj c).comp p)
private theorem bCI {a :nI} {q:ℕ}
  (w:abE a q→ao) (p:jK →ₗ[ao] (abE a q→ao[X]))
  (F:jK) :
  aCD w p F = ∑ c,w c•p F c:= by
 simp [aCD,RD]
private theorem cFU {E :Type*} [AddCommGroup E] [Module ao E]
  [uW ao E] (V W:u8 ao jK) [uW ao V]
  (f :V →ₗ[ao] E) (hker :uJ f=W.comap V.subtype) :
  TT V W≤oz ao E := by
 have h:=Ok (K:=ao) (V := ↥V) (V₂:=E) f
 have he :=(V.equivSubtypeMap (W.comap V.subtype)).finrank_eq
 rw [Oc] at he
 rw [hker,he] at h
 have hle :=Submodule.finrank_le (qU f)
 unfold TT
 omega
end
end aFN
end
section
namespace acZ
noncomputable section
open K1 aR jA
open scoped BigOperators
set_option maxRecDepth 1024
private def multiples (D:ko) :u8 iP ko :=
 (Ideal.span {D}).restrictScalars iP
private theorem mem_multiples {F D:ko} : F∈multiples D↔D ∣F :=
 UY
private theorem aJZ (v :mA→ℕ) (D:ko) (hD:D ≠0) (n:ℕ) :
   (D^n).weightedTotalDegree v=n*D.weightedTotalDegree v := by
 induction n with
 | zero =>
   rw [y5 ,vZ,← Dv,MvPolynomial.weightedTotalDegree_C]
 | succ n ih =>
   rw [Dz ,MvPolynomial.weightedTotalDegree_mul v _ _ (MS _ hD) hD,
     ih,KH]
end
end acZ
end
section
namespace HM
open Rj Finset
open scoped BigOperators
theorem ZE (w:ℤ) :2*sG w=w*(w+1) := by
 unfold sG
 apply FR
 rcases (show w % 2=0∨w % 2=1 by omega) with h | h
 · have hw:w=2*(w/2) := by omega
   exact Vz  (by rw [hw]; exact VH  _ _) _
 · have hw:w+1=2*(w/2+1) := by omega
   exact VC  (by rw [hw]; exact VH  _ _) _
theorem gEl {u v :ℤ} (hu:0≤u) (huv :u≤v) :
  sG u≤ sG v := by
 have h:=v8 (show 0≤v - u by omega) (show 0≤v+u+1 by omega)
 nlinarith only [ZE u,ZE v,h]
def xV (w:ℤ) :ℤ :=
 let m:=w/2
 m*(m+1)+w % 2*(m+1)
theorem aJX {w:ℤ} (hw:0≤w) :0≤xV w :=
 add_nonneg (v8 (by omega) (by omega)) (v8 (by omega) (by omega))
theorem gL2 (w:ℤ) :xV w=(w+1)^2/4 := by
 have hw:w=2*(w/2)+w % 2 := by omega
 have hsq: (w+1)^2=4*xV w+(1 - w % 2) := by
  conv_lhs=>rw [hw]
  rcases (show w % 2=0∨w % 2=1 by omega) with he | he <;>
   simp only [xV,he] <;> ring
 omega
theorem gL3 (w:ℤ) :
   xV (w+1) - xV w=(w+2)/2 := by
 rcases (show w % 2=0∨w % 2=1 by omega) with he | he
 · rw [xV,xV,show (w+1)/2=w/2 by omega,
    show (w+1) % 2=1 by omega,show (w+2)/2=w/2+1 by omega,he]
   ring
 · rw [xV,xV,show (w+1)/2=w/2+1 by omega,
    show (w+1) % 2=0 by omega,show (w+2)/2=w/2+1 by omega,he]
   ring
theorem gEm (w:ℤ) :
    sG (w+1) - xV w=xV (w+1) := by
  have heq :2*(xV (w+1) + xV w)=(w+1)*(w+2) := by
    rcases (show w % 2=0∨w % 2=1 by omega) with he | he
    · rw [xV,xV,show (w+1)/2=w/2 by omega,
        show (w+1) % 2=1 by omega,he]
      conv_rhs=>rw [show w=2*(w/2) by omega]
      ring
    · rw [xV,xV,show (w+1)/2=w/2+1 by omega,
        show (w+1) % 2=0 by omega,he]
      conv_rhs=>rw [show w=2*(w/2)+1 by omega]
      ring
  linarith only [heq,ZE (w+1)]
theorem cGR {a w:ℤ} (ha :a≤(w+1)/2) (hw:0≤w) :
   yC ⟨a,w⟩=xV w:= by
 unfold yC
 simp only [max_eq_right ha,max_eq_right (show 0≤(w+1)/2 by omega),
   oZ  (show (w+1)/2≤w by omega)]
 have h:w-(w+1)/2=w/2 := by omega
 rw [h,xV]
 rcases (show w % 2=0∨w % 2=1 by omega) with he | he
 · rw [show (w+1)/2=w/2 by omega,he]
   nlinarith only [ZE (w/2)]
 · rw [show (w+1)/2=w/2+1 by omega,he]
   nlinarith only [ZE (w/2),ZE (w/2+1)]
def akx (w:ℤ) :ℤ :=
 let m:=w/2
 m*(m+1)*(4*m+5)+6*(w % 2)*(m+1)^2
theorem cwN (w:ℤ) :
   akx (w+1)-akx w=6*xV (w+1) := by
 rcases (show w % 2=0∨w % 2=1 by omega) with he | he
 · rw [akx,akx,xV,show (w+1)/2=w/2 by omega,
    show (w+1) % 2=1 by omega,he]
   ring
 · rw [akx,akx,xV,show (w+1)/2=w/2+1 by omega,
    show (w+1) % 2=0 by omega,he]
   ring
def aQX (w:ℤ) :ℤ :=
 let n:=max 0 w
 (n - 1)*n*(n+1)
theorem gEi (w:ℤ) :
   aQX (w+1)-aQX w=6*sG (max 0 w) := by
 unfold aQX
 by_cases h:w<0
 · rw [max_eq_left (show w+1≤0 by omega),max_eq_left h.le]
   decide
 · rw [max_eq_right (show 0≤w+1 by omega),max_eq_right (show 0≤w by omega)]
   linear_combination 3*(ZE w).symm
theorem amJ (f p:ℤ→ℤ) (h : ∀ j,p (j+1) - p j=6*f j)
   (a :ℤ) (n:ℕ) :
   6*(∑ j∈cy n,f (a+j))=p (a+n) - p a := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [t3 ,t7,ih,← h,Et,← vk]
   ring
theorem gxk (a :ℤ) (n:ℕ) :
   6*(∑ j∈cy n,xV (a - j))=akx a-akx (a - n) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [t3 ,t7,ih,Et]
   have h:=cwN (a-(n:ℤ) - 1)
   rw [sub_add_cancel] at h
   rw [show a-((n:ℤ)+1)=a - n - 1 by ring]
   linarith only [h]
def OU (q w:ℤ) :ℤ :=
 xV (w+1) - sG (max 0 (w - q))
theorem aTY {q w:ℤ} (hw:0≤w) (hq:w≤2*q) :
  gd q w=OU q w:= by
 rw [gd,p5 (not_lt.mpr hw),zm hq,OU,gL2]
 ring_nf
private theorem dEz {q w:ℤ} (hw:0≤w) (hq:w+1≤2*q) :
  OU q w≤OU q (w+1) := by
 have hW:=gL3 (w+1)
 have hT:sG (max 0 (w+1 - q)) - sG (max 0 (w - q)) =
    max 0 (w+1 - q) := by
  by_cases h:w<q
  · rw [max_eq_left (show w+1 - q≤0 by omega),max_eq_left (show w - q≤0 by omega)]
    exact sub_self _
  · rw [max_eq_right (show 0≤w+1 - q by omega),max_eq_right (show 0≤w - q by omega)]
    nlinarith only [ZE (w+1 - q),ZE (w - q)]
 unfold OU
 omega
theorem cDW {q:ℤ} {w v :ℕ} (hwv :w≤v) (hv : (v :ℤ)≤2*q) :
   OU q w≤OU q v := by
 induction v with
 | zero =>
   obtain rfl :w=0:= by omega
   exact uh
 | succ v ih =>
   by_cases h:w=v+1
   · rw [h]
   · refine (ih (by omega) (by omega)).trans ?_
     simpa only [Et ] using dEz (q:=q) (w:=(v :ℤ)) (by omega) (by omega)
theorem dEx {q:ℤ} (hq:q≤2300) :
   OU q 2300=sG (q+1) - xV (2*q - 2300) := by
 have hQ:xV (2*q - 2300)=(q - 1150)*(q - 1149) := by
   rw [xV,show (2*q - 2300)/2=q - 1150 by omega,
     show (2*q - 2300) % 2=0 by omega]
   ring
 rw [OU,max_eq_right (show 0≤2300 - q by omega),
   show xV (2300+1)=1324801 by decide,hQ]
 nlinarith only [ZE (2300 - q),ZE (q+1)]
end HM
end
section
namespace aw9
open Rj
open scoped BigOperators
set_option maxHeartbeats 1000000
private theorem bsK (len:ℕ) :
   2*(∑ i∈cy len,(i:ℤ))=(len:ℤ)*(len - 1 :ℤ) ∧
   6*(∑ i∈cy len,(i:ℤ)^2) =
     (len:ℤ)*(len - 1 :ℤ)*(2*len - 1 :ℤ) := by
 induction len with
 | zero=>simp
 | succ len ih =>
   simp only [t3 ,Et]
   exact ⟨by nlinarith only [ih.1],by nlinarith only [ih.2]⟩
private theorem dQi (a b x :ℤ) :
  cost (a+2*b*x)=cost a+b*(a+1)*x+b^2*x^2 := by
 have hs : (a+1)/2+(a/2+1)=a+1 := by omega
 have he :2*b*x=2*(b*x) := by ring
 have h₁: (a+2*b*x+1)/2=(a+1)/2+b*x := by rw [he]; omega
 have h₂: (a+2*b*x)/2=a/2+b*x := by rw [he]; omega
 unfold cost
 rw [h₁,h₂]
 linear_combination (b*x)*hs
private theorem bnP (a :ℤ) (len:ℕ) :
  (∑ _i∈cy len,a)=(len:ℤ)*a := by
 simp
private theorem c5V (a b c:ℤ) (len:ℕ) :
  (∑ i∈cy len,(a+b*(i:ℤ)+c*(i:ℤ)^2)) =
    (len:ℤ)*a+b*a5v len+c*a8K len:= by
 have h₁:a5v len = ∑ i∈cy len,(i:ℤ) := by
  unfold a5v
  have h:=(bsK len).1
  omega
 have h₂:a8K len = ∑ i∈cy len,(i:ℤ)^2 := by
  unfold a8K
  have h:=(bsK len).2
  omega
 simp only [zk,bnP,Ar,h₁,h₂]
private theorem dfK (a b:ℤ) (len:ℕ) :
  aJF a b len = ∑ i∈cy len,cost (a+2*b*i) := by
 simp_rw [dQi]
 exact (c5V _ _ _ _).symm
private theorem gwC (a b:ℤ) (len:ℕ) :
  bhE a b len = ∑ i∈cy len,(a+b*i)^2 := by
 have h (i:ℕ) : (a+b*(i:ℤ))^2=a^2+(2*a*b)*i+b^2*(i:ℤ)^2 :=
  by ring
 simp_rw [h]
 exact (c5V _ _ _ _).symm
private def bJt (mode :Mode) (k t:ℤ) :ℤ :=
 match mode with
 | .columns=>columns k
 | .empty=>cost t
 | .ic both=>aJt both k t
private theorem eA3 (mode :Mode) (k start:ℤ) (len:ℕ) :
    azE mode k start len = ∑ i∈cy len,bJt mode k (start+2*i) := by
  cases mode with
  | columns=>exact (bnP _ _).symm
  | empty=>simpa only [azE,bJt,mul_one] using dfK start 1 len
  | ic both =>
    simp only [azE,bJt,dfK,gwC,← bnP (nX k) len,
      ← zk,← wA]
    apply n5 rfl
    intro i _
    cases both <;> simp [aJt,azu,RZ,PO]
    all_goals
      apply congrArg₂ (fun a b:ℤ=>a - b)
      · apply congrArg₂ (fun a b:ℤ=>a+b)
        · apply nq (fun a :ℤ=>nX k+a)
          apply nq cost
          ring
        · apply nq cost
          ring
      · apply nq (fun a :ℤ=>a^2)
        ring
private def DV (k :ℕ) (t:ℤ) :ℤ :=
 let q:=(7300-(k :ℤ) - t).toNat
 xR q (aU k) (powers q k)
private theorem bYF {k :ℕ} {mode :Mode} {l r t:ℤ}
   (ha :valid mode k l r) (hl:l≤t) (hr :t≤ r)
   (hpos :0<t) (hmax :t≤5000-(k :ℤ)) :
   DV k t≤bJt mode k t:= by
 let q:=(7300-(k :ℤ) - t).toNat
 have hq:2300≤q:= by dsimp [q]; omega
 have ht:Ic q (aU k)=t:= by unfold Ic aU q; omega
 change (xR q (aU k) (powers q k) :ℤ)≤_
 cases mode with
 | columns=>exact dzk hq
 | empty=>exact dzl hq ht hpos
 | ic both=>exact dzu hq ht hpos (dsl ha hl hr)
private theorem c3G (k fuel:ℕ) (start:ℤ) (len:ℕ) (hpos :0<start)
    (hmax : ∀ i:ℕ,i<len→start+2*i≤5000-(k :ℤ)) :
    (∑ i∈cy len,DV k (start+2*i))≤aoE k fuel start len:= by
  have width_bound (n:ℕ) (mode :Mode) (s :ℤ) :E0 k s n mode≤n:= by
    unfold E0
    split <;> omega
  induction fuel generalizing start len with
  | zero =>
    rw [aoE,← bnP]
    apply qM
    intro i hi
    exact bYF (mode := .columns) (l:=start) (r :=start+2*i)
      trivial (by omega) uh (by omega) (hmax i (Finset.mem_range.mp hi))
  | succ fuel ih =>
    rw [aoE]
    split
    · rename_i h
      simp [h]
    · let mode :=anR k start
      let width :=E0 k start len mode
      let last :=start+2*((width :ℤ) - 1)
      have hw:width≤len:=width_bound len mode start
      change _≤(if valid mode k start last then azE mode k start width
        else (width :ℤ)*nX k)+aoE k fuel (start+2*width) (len - width)
      conv_lhs =>
        rw [show len=width+(len - width) by omega,Df]
      apply Mj
      · split
        · rename_i hv
          rw [eA3]
          apply qM
          intro i hi
          have hi' := Finset.mem_range.mp hi
          exact bYF hv (by omega) (by dsimp [last]; omega) (by omega) (hmax i (by omega))
        · rw [← bnP]
          apply qM
          intro i hi
          have hi' := Finset.mem_range.mp hi
          exact bYF (mode := .columns) (l:=start) (r :=start+2*i)
            trivial (by omega) uh (by omega) (hmax i (by omega))
      · have hr (i:ℕ) (hi:i<len - width) :
            start+2*(width :ℤ)+2*(i:ℤ)≤5000-(k :ℤ) := by
          simpa only [yJ,t7,vk] using hmax (width+i) (by omega)
        have h:=ih (start+2*width) (len - width) (by omega) hr
        refine le_trans (le_of_eq ?_) h
        apply n5 rfl
        intro i _
        congr 1
        push_cast
        ring
private theorem gwF (f :ℕ→ℤ) (len:ℕ) :
    (∑ i∈cy len,f i)=(∑ i∈cy ((len+1)/2),f (2*i)) +
      ∑ i∈cy (len/2),f (2*i+1) := by
  induction len with
  | zero=>simp
  | succ len ih =>
    rw [t3 ,ih]
    rcases (show len % 2=0∨len % 2=1 by omega) with he | ho
    · rw [show (len.succ+1)/2=(len+1)/2+1 by omega,
        show len.succ/2=len/2 by omega,t3  (fun i=>f (2*i)),
        show 2*(len/2)=len by omega]
      abel
    · rw [show (len.succ+1)/2=(len+1)/2 by omega,
        show len.succ/2=len/2+1 by omega,t3  (fun i=>f (2*i+1)),
        show 2*(len/2)+1=len by omega]
      abel
private theorem eGa {k :ℕ} (hk :k<5000) :
   (∑ j∈cy 2700,(xR (2300+j) (aU k) (powers (2300+j) k) :ℤ)) ≤
     aDZ k := by
 let len:=min 2700 (5000 - k)
 let start:ℤ:=5001-(k :ℤ)-len
 let rank (j:ℕ) :ℤ:=xR (2300+j) (aU k) (powers (2300+j) k)
 change (∑ j∈cy 2700,rank j)≤_
 have hlen:len≤2700:=G0 _ _
 have hklen:len≤5000 - k :=Vq _ _
 have htrim: (∑ j∈cy 2700,rank j) = ∑ j∈cy len,rank j:= by
   symm
   apply ze (xL hlen)
   intro j hj h
   have hj' := Finset.mem_range.mp hj
   have hj'' := mt Finset.mem_range.mpr h
   have hcut:Ic (2300+j) (aU k)≤0:= by
     unfold Ic aU
     dsimp [len] at hj''
     omega
   simp [rank,xR,hcut]
 have hreflect : (∑ j∈cy len,rank j) = ∑ j∈cy len,DV k (start+j) := by
   rw [← z9 rank len]
   apply n5 rfl
   intro j hj
   have hj' := Finset.mem_range.mp hj
   have he : (7300-(k :ℤ)-(start+j)).toNat=2300+(len - 1 - j) := by
     dsimp [start]
     omega
   simp only [rank,DV,he]
 have hpos :0<start:= by dsimp [start]; omega
 rw [htrim,hreflect,gwF]
 change _≤aoE k 8 start ((len+1)/2)+aoE k 8 (start+1) (len/2)
 apply Mj
 · simpa only [Nat.cast_mul,LP] using
     c3G k 8 start ((len+1)/2) hpos (by intros; dsimp [start]; omega)
 · simpa only [Nat.cast_mul,yJ,LP ,In,vk,add_left_comm,wY] using
     c3G k 8 (start+1) (len/2) (by omega) (by intros; dsimp [start]; omega)
private theorem gCA (n:ℕ) :
   oD 0 n = ∑ k∈cy n,aDZ k := by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [total,Finset.sum_range_succ,ih,Nat.zero_add]
theorem proof :Rj.c5:= by
  refine ⟨powers,?_⟩
  apply Int.ofNat_le.mp
  push_cast [ Xi]
  rw [Finset.sum_comm]
  have htrim: (∑ k∈cy 7300,∑ j∈cy 2700,
      (xR (2300+j) (aU k) (powers (2300+j) k) :ℤ)) =
      ∑ k∈cy 5000,∑ j∈cy 2700,
        (xR (2300+j) (aU k) (powers (2300+j) k) :ℤ) := by
    symm
    apply ze (xL (by decide))
    intro k _ hk
    have hk' := mt Finset.mem_range.mpr hk
    apply xm
    intro j _
    have hcut:Ic (2300+j) (aU k)≤0:= by unfold Ic aU; omega
    simp [xR,hcut]
  rw [htrim]
  calc
    _ ≤ ∑ k∈cy 5000,aDZ k :=
      qM fun k hk=>eGa (Finset.mem_range.mp hk)
    _=oD 0 5000:=(gCA 5000).symm
    _≤5196036704622 :=le_of_eq bxY
end aw9
end
section
namespace Sy
open aR NR aFN
open scoped Polynomial Pointwise
noncomputable section
abbrev Exp:=Fin 3 →₀ ℕ
abbrev gQ (R:Type*) [oj R] :=lV (Fin 3) R
def cV (e :Exp) :ℕ:=e 0+e 1+e 2
def weight (e :Exp) :ℕ:=e 1+2*e 2
private def Jm (d e :Exp) :Prop :=
 cV d=cV e∧weight d≤weight e∧d 2≤e 2
private theorem bBw {d e f g:Exp} (h₁:Jm d e) (h₂:Jm f g) :
  Jm (d+f) (e+g) := by
 obtain ⟨h₁,h₂',h₃⟩:=h₁
 obtain ⟨h₄,h₅,h₆⟩:=h₂
 simp only [Jm,cV,weight,wB] at *
 omega
@[simp] theorem bWf {R:Type*} [oj R] (t c:R) :
   canonical t (c9 c)=c9 c :=
  GF _ _ _
@[simp] theorem dEp {R:Type*} [oj R] (t:R) (i:Fin 3) :
   canonical t (lz i)=aTo t i :=
  Fa _ _ _
private theorem eqb {R:Type*} [oj R] (t:R) (i:Fin 3)
  {d:Exp} (hd:d∈(aTo t i).support) :
  Jm d (p7 i 1) := by
 classical
 fin_cases i
 all_goals
  simp [aTo,vi ,UP] at hd
  try split_ifs at hd
  all_goals subst_vars
  all_goals simp_all [Jm,cV,weight]
theorem bB4 {R:Type*} [oj R] (t:R) (G:gQ R)
    {d:Exp} (hd:d∈(canonical t G).support) :
    ∃ e∈G.support,cV d=cV e∧weight d≤weight e∧d 2≤e 2 := by
  classical
  suffices h : ∀ d∈(canonical t G).support,∃ e∈G.support,Jm d e from h d hd
  clear d hd
  induction G using MvPolynomial.induction_on'' with
  | C r =>
      intro d hd
      simp only [bWf] at hd
      exact ⟨d,hd,rfl,uh,uh⟩
  | monomial_add a b G ha hb hG hm =>
      have hs : (ov a b+G).support=insert a G.support := by
        have ha' : G.coeff a=0:=MvPolynomial.notMem_support_iff.mp ha
        ext e
        by_cases he :a=e
        · subst e
          simp [yl,ha',hb]
        · simp [yl,he,Ne.symm he]
      intro d hd
      rw [qy] at hd
      rcases Finset.mem_union.mp (Up hd) with hd | hd
      · obtain ⟨e,he,hde⟩:=hm d hd
        rw [hs]
        have hea :e=a :=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
        subst e
        exact ⟨a,Qw _ _,hde⟩
      · obtain ⟨e,he,hde⟩:=hG d hd
        exact ⟨e,hs.symm ▸ Pk he,hde⟩
  | mul_X G i hG =>
      intro d hd
      rw [oq,dEp] at hd
      obtain ⟨f,hf,g,hg,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul _ _ hd)
      obtain ⟨e,he,hfe⟩:=hG f hf
      refine ⟨e+Finsupp.single i 1,?_,bBw hfe (eqb t i hg)⟩
      rw [MvPolynomial.support_mul_X]
      exact Finset.mem_map.mpr ⟨e,he,rfl⟩
theorem cZk {R S:Type*} [oj R] [oj S] (f :R →+* S) (t:R)
  (G:gQ R) :oY f (canonical t G)=canonical (f t) (oY f G) := by
 have h: (oY f).comp (canonical t) =
    (canonical (f t)).comp (oY f) := by
  apply pQ
  · intro r
    simp
  · intro i
    fin_cases i <;> simp [aTo]
 exact oy h G
private def scale {R:Type*} [oj R] (t:R) (n:ℕ) :gQ R →+* gQ R :=
 pL c9
  (fun i=>c9 (t^(n - i.val))*lz i)
private theorem gl4 {R:Type*} [oj R] (t:R) (n:ℕ) (G:gQ R)
    (e :Exp) :
    (scale t n G).coeff e=t^((n - 0)*e 0+(n - 1)*e 1+(n - 2)*e 2)*G.coeff e := by
  classical
  let k (d:Exp) :=(n - 0)*d 0+(n - 1)*d 1+(n - 2)*d 2
  change (scale t n G).coeff e=t^k e*G.coeff e
  induction G using MvPolynomial.induction_on' with
  | add P Q hP hQ=>simp [hP,hQ,mul_add]
  | monomial d r =>
      have hmono: (∏ i:Fin 3,lz i^d i)=(ov d 1 :gQ R) := by
        rw [← Cy d _ (by simp)]
        exact (MvPolynomial.monic_monomial_eq d).symm
      rw [scale,PA,Cy d _ (by simp)]
      simp_rw [mul_pow,← xI,← pow_mul]
      rw [Finset.prod_mul_distrib,hmono,← map_prod,Finset.prod_pow_eq_pow_sum,
        qG,← z8 ,← oq,vi]
      simp only [yl]
      split
      · rename_i hd
        subst d
        simp [k,v9]
      · simp
private theorem gl1 {R:Type*} [oj R] (t:R) (G:gQ R) :
  scale t 2 (canonical t G)=canonical 1 (scale t 3 G) := by
 have h: (scale t 2).comp (canonical t)=(canonical 1).comp (scale t 3) := by
  apply pQ
  · intro r
    simp [scale]
  · intro i
    fin_cases i <;> simp [aTo,scale,Dz] <;> ring
 exact oy h G
private theorem dEr {R:Type*} [oj R] (r :R) (G:gQ R) :
   c9 r∣canonical 1 G↔c9 r∣G:= by
 let inv :gQ R →+* gQ R:=pL c9
   ![lz 0,lz 1-MvPolynomial.X 0,
     lz 2 - lz 1+MvPolynomial.X 0]
 have hi:inv.comp (canonical 1)=vG _:= by
   apply pQ
   · intro x
     simp [inv]
   · intro i
     fin_cases i <;> simp [aTo,inv]
 constructor
 · intro h
   have hh:=map_dvd inv h
   have hleft:inv (canonical 1 G)=G:=oy hi G
   have hC:inv (c9 r)=c9 r :=GF _ _ _
   rwa [hleft,hC] at hh
 · intro h
   simpa only [bWf] using map_dvd (canonical (1 :R)) h
def probe {R:Type*} [oj R] (q:ℕ) (e :Exp) (i:ℕ) (G:gQ R[X]) :R :=
 if i<weight e then (G.coeff e).coeff i
 else ((canonical lJ G).coeff e).coeff (q+i)
theorem eiP {R:Type*} [oj R] (q L:ℕ) (G:gQ R[X])
    (hG : ∀ e∈G.support,cV e=q∧q+weight e≤L) (hq:q≤L) :
    c9 ((lJ:R[X])^L)∣canonical lJ G ↔
      ∀ e i,i<L - q→probe q e i G=0:= by
  let A:=canonical (lJ:R[X]) G
  have hA : ∀ e∈A.support,cV e=q∧q+weight e≤L:= by
    intro e he
    obtain ⟨d,hd,hgrade,hw,_⟩:=bB4 _ _ he
    exact ⟨hgrade.trans (hG d hd).1,(NZ hw _).trans (hG d hd).2⟩
  let X3 := ∀ e i,i<weight e→(G.coeff e).coeff i=0
  let High := ∀ e i,weight e≤ i→i<L - q→(A.coeff e).coeff (q+i)=0
  have htests : (∀ e i,i<L - q→probe q e i G=0)↔X3∧High:= by
    constructor
    · intro h
      refine ⟨?_,fun e i hw hi=> by simpa [probe,not_lt.mpr hw,A] using h e i hi⟩
      intro e i hi
      by_cases he :e∈G.support
      · simpa [probe,hi] using h e i (by have :=(hG e he).2; omega)
      · simp [MvPolynomial.notMem_support_iff.mp he]
    · rintro ⟨hl,hh⟩ e i hi
      by_cases hw:i<weight e
      · simpa [probe,hw] using hl e i hw
      · simpa [probe,hw,A] using hh e i (Nat.le_of_not_gt hw) hi
  have scale_low (n m:ℕ) (P:gQ R[X]) (hP : ∀ e∈P.support,cV e=q) (hn:2≤n) :
      c9 ((lJ:R[X])^(n*q+m))∣scale lJ n P ↔
        ∀ e i,i< m+weight e→(P.coeff e).coeff i=0:= by
    simp only [Re,II,gl4,
      Polynomial.coeff_X_pow_mul']
    have hshift (e :Exp) (he :e∈P.support) :
        (n - 0)*e 0+(n - 1)*e 1+(n - 2)*e 2+weight e=n*q:= by
      rw [← hP e he]
      simp only [cV,weight,Nat.sub_zero]
      have h₁:n - 1+1=n:= by omega
      have h₂:n - 2+2=n:= by omega
      have hm₁:=nq (fun x=>x*e 1) h₁
      have hm₂:=nq (fun x=>x*e 2) h₂
      simp only [Nat.add_mul,Nat.one_mul] at hm₁ hm₂
      simp only [FK]
      omega
    constructor
    · intro h e i hi
      by_cases he :e∈P.support
      · let s :=(n - 0)*e 0+(n - 1)*e 1+(n - 2)*e 2
        have hs :s+weight e=n*q:=hshift e he
        have hz :=h e (s+i) (by omega)
        change (if s≤ s+i then (P.coeff e).coeff (s+i - s) else 0)=0 at hz
        simpa only [t8 (by omega :s≤ s+i),show s+i - s=i by omega] using hz
      · simp [MvPolynomial.notMem_support_iff.mp he]
    · intro h e i hi
      by_cases he :e∈P.support
      · split
        · exact h e _ (by have :=hshift e he; omega)
        · rfl
      · simp [MvPolynomial.notMem_support_iff.mp he]
  have hl: (∀ e i,i<q+weight e→(A.coeff e).coeff i=0)↔X3:= by
    have hs :c9 ((lJ:R[X])^(3*q+0))∣scale lJ 3 G
        ↔ X3:= by
      simpa [ X3] using scale_low 3 0 G (fun e he=>(hG e he).1) (by decide)
    rw [← scale_low 2 q A (fun e he=>(hA e he).1) (by decide),← hs]
    rw [show 2*q+q=3*q+0 by omega]
    change c9 ((lJ:R[X])^(3*q+0)) ∣
      scale lJ 2 (canonical lJ G)↔_
    rw [gl1,dEr]
  rw [htests,← hl,Re]
  simp only [II]
  change (∀ e i,i<L→(A.coeff e).coeff i=0)↔_
  constructor
  · intro h
    refine ⟨?_,fun e i _ hi=>h e _ (by omega)⟩
    intro e i hi
    by_cases he :e∈A.support
    · exact h e i (hi.trans_le (hA e he).2)
    · simp [MvPolynomial.notMem_support_iff.mp he]
  · rintro ⟨hl',hh⟩ e i hi
    by_cases hw:i<q+weight e
    · exact hl' e i hw
    · have heq :q+(i - q)=i:= by omega
      rw [← heq]
      exact hh e (i - q) (by omega) (by omega)
end
end Sy
end
section
namespace aFP
noncomputable section
open jA
def aGx (F G:ko) :Lower :=
 Polynomial.resultant (qN F) (qN G) (gY F) (gY G)
end
end aFP
end
section
namespace aFO
noncomputable section
open aR jA NR
open scoped Polynomial BigOperators
abbrev I6:=ao[X][X]
def Wv (ε:ao) :I6 →+* ao[X] :=
 sS (pU ε)
def Q8 (H :ao[X]) (ε:ao) :ao[X] :=H+Polynomial.C ε
def awc (N :I6[X]) (D:I6) (ε:ao) :kS[X] :=
 ahH (N.map (Wv ε)) (Wv ε D)
def bu4 (c a₀ a₁:ao[X]) :kS[X] :=
  jH c*(jH a₀ +
    lI (mD ao[X] kS lJ)*jH a₁)
def bu5 (q:ao[X]) :kS[X] :=
 lI (mD ao[X] kS lJ)*jH q
structure cAj (H c q a₀ a₁:ao[X]) (N :I6[X]) (D:I6)
  (ε:ao) :Prop where
 at_zero : (Wv ε D).eval 0≠0
 small: (N.map (Wv ε)).natDegree<(Q8 H ε).natDegree
 generic_unit :qx (bu4 c a₀ a₁) (jH (Q8 H ε))
 generic_congruence :jH (Q8 H ε) ∣
  bu4 c a₀ a₁*awc N D ε+bu5 q
def amA (H :ao[X]) (R:kS[X]) (F:jK) :Lq :=
  KI
    (MvPolynomial.C.comp (sS (mD ao kS)))
    (fun i:mA=>i.elim
      (c9 (lI (mD ao[X] kS lJ)))
      (fun i:Fin 3 =>
        c9 (oK i.val R) +
          ∑ j:Fin 3,if j.val≤ i.val then
            c9 (oK (i.val - j.val) (jH H)) *
              lz j
          else 0)) F
end
end aFO
end
section
namespace axa
noncomputable section
open Polynomial K1 aR jA acZ
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev Exponent:=mA →₀ ℕ
abbrev Lq:=NR.Lq
abbrev arX:=Ga.b+Ga.j
def weight (h:ℕ) (a :Exponent) :ℕ :=
 a.sum (fun i e=>i.elim 0 (fun j=>(131071+h - j.val)*e))
def bgL {Γ s} (P:jF Γ s) (L:kH P) :jK →+* Lq :=
  pL
    (MvPolynomial.C.comp (sS (mD ao kS)))
    (fun i=>i.elim
      (c9 (lI (mD ao[X] kS lJ)))
      (ar9 P L))
theorem fXc {Γ s} (P:jF Γ s) (L:kH P) (F:jK) :
 bgL P L F=restore P L F:=rfl
private theorem dFo (F:jK) :
  Jn Ga (bC F)↔Jn Ga F:= by
 have hs : (bC F).support=F.support :=
  TZ F (vh ao[X] iP)
 simp only [Jn,vC,lP,gY,zg ,
  RC,hs]
private def cutoff (h T:ℕ) :u8 ao jK where
  carrier := {F | ahb h T F}
  zero_mem' := by simp [ahb]
  add_mem' {F G} hF hG:= by
    change ahb h T F at hF
    change ahb h T G at hG
    intro m hm
    have hor :=Finset.mem_union.mp (Up hm)
    have hbound:weight h m≤T:= by
      rcases hor with hf | hg
      · exact (G5 ..).trans (hF m hf)
      · exact (G5 ..).trans (hG m hg)
    have hd (Q:jK) (hQ:ahb h T Q) :
        (Q.coeff m).natDegree≤T - weight h m:= by
      by_cases hmem:m∈Q.support
      · have hh: (Q.coeff m).natDegree+weight h m≤T:=hQ m hmem
        omega
      · simp [MvPolynomial.notMem_support_iff.mp hmem]
    change ((F+G).coeff m).natDegree+weight h m≤T
    simp only [HZ,wB]
    have hh:=(natDegree_add_le (F.coeff m) (G.coeff m)).trans (vH (hd F hF) (hd G hG))
    omega
  smul_mem' c F hF:= by
    intro m hm
    have hh: (F.coeff m).natDegree+weight h m≤T :=
      hF m (MvPolynomial.support_smul hm)
    rw [Pf]
    exact (Te (QL c (F.coeff m)) _).trans hh
private def aV {Γ s} (w:I→K) (P:jF Γ s) (L:kH P) (t:ℕ) :
   Submodule ao jK :=
 ((OV Ga).restrictScalars ao).comap Bu ⊓
 cutoff P.H.natDegree (t+arX*P.H.natDegree) ⊓
 (⨅ i:I,NR.ays (qz (node i)) (qz (w i))) ⊓
 NR.amn P L Ga (jH P.H)
private theorem b8T {Γ s} (w:I→K) (P:jF Γ s) (L:kH P)
  (t:ℕ) (F:jK) :F∈aV w P L t↔Source w P L Ga t F:= by
 simp only [aV,TI,Submodule.mem_comap,Submodule.restrictScalars_mem,
  cfL,bI3,dFo,Submodule.mem_iInf,
  NR.bsz,NR.aVU,Source,bAy]
 change ((_∧ahb _ _ F)∧_)∧_↔_
 tauto
private instance bqa {Γ s} (w:I→K) (P:jF Γ s) (L:kH P) (t:ℕ) :
    uW ao (aV w P L t) := by
  classical
  let T:=t+arX*P.H.natDegree
  let E :=mA→Fin 70001
  let f :aV w P L t →ₗ[ao] ((E×Fin (T+1))→ao) :=FV fun u =>
    (F9 ao u.2.val).comp
      (((MK ao[X] (Finsupp.equivFunOnFinite.symm (fun i=>(u.1 i).val))
        : jK →ₗ[ao[X]] ao[X]).restrictScalars ao).comp (aV w P L t).subtype)
  have hzero (Q:aV w P L t) (hQ:f Q=0) :Q=0:= by
    obtain ⟨F,hF⟩:= Q
    have hsrc :=(b8T w P L t F).mp hF
    apply Subtype.ext
    change F=0
    apply MvPolynomial.ext
    intro m
    change F.coeff m=0
    by_contra hnz
    have hm:=MvPolynomial.mem_support_iff.mpr hnz
    have hd: (F.coeff m).natDegree≤T:=(Nat.le_add_right ..).trans (hsrc.2.1 m hm)
    have he (i:mA) :m i<70001 := by
      cases i with
      | none =>
        exact Nat.lt_succ_of_le ((MvPolynomial.le_degreeOf_of_mem_support none hm).trans hsrc.1.2.2.2)
      | some i =>
        by_cases hz :m (some i)=0
        · simp [hz]
        let v :mA→ℕ:= fun j=>j.elim 0 (fun _=>1)
        have hi:=(vj v hm).trans hsrc.1.1
        have hs :=Finset.single_le_sum (f := fun j=>m j*v j)
          (fun j _=>C9 _) (Finsupp.mem_support_iff.mpr hz)
        have hsum:z7 v m = ∑ j∈m.support,m j*v j:= by
          simp [JW,Finsupp.sum,sI]
        rw [hsum] at hi
        change _≤6820 at hi
        change m (some i)*1≤_ at hs
        omega
    let u:E := fun i=>⟨m i,he i⟩
    apply hnz
    ext k
    rw [zc]
    by_cases hk :k<T+1
    · have hval :=GB hQ (u,⟨k,hk⟩)
      change (F.coeff (Finsupp.equivFunOnFinite.symm (fun i=>(u i).val))).coeff k=0 at hval
      have heq :Finsupp.equivFunOnFinite.symm (fun i=>(u i).val)=m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact Kv (by omega)
  apply SD f
  intro Q R h
  apply sub_eq_zero.mp
  apply hzero
  rw [zS ,h,sub_self]
private def anL (h t:ℕ) (m:Exponent) :ℕ :=
 t+arX*h - weight h m
private def boundary (h t:ℕ) :jK →ₗ[ao] (Exponent→ao) :=
 FV fun m=>(F9 ao (anL h t m)).comp
  ((MK ao[X] m).restrictScalars ao)
private theorem cDm (h t:ℕ) (F:jK) (m:Exponent) :
 boundary h t F m=(F.coeff m).coeff (anL h t m) :=rfl
private theorem bVx {h t:ℕ} {F:jK}
  (hF:ahb h (t+arX*h) F) (hz :boundary h t F=0)
  (m:Exponent) (hm:m∈F.support) :
  (F.coeff m).natDegree+weight h m<t+arX*h:= by
 have hle : (F.coeff m).natDegree+weight h m≤t+arX*h:=hF m hm
 by_contra! hn
 have heq : (F.coeff m).natDegree=anL h t m:= by
  unfold anL
  omega
 have h:=GB hz m
 rw [cDm,← heq,coeff_natDegree] at h
 exact (leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)) h
private theorem cU3 {ι:Type*} [yL ι] {h t:ℕ} (e :ι→jK)
   (hcut : ∀ i,ahb h (t+arX*h) (e i))
   (he :yo ao (fun i=>boundary h t (e i))) :
   yo iP (fun i=>bC (e i)) := by
 apply (LinearIndependent.iff_fractionRing ao[X] iP).mp
 let f :jK →ₗ[ao[X]] ko :=
   (LQ (Algebra.ofId ao[X] iP)).toLinearMap
 suffices hi:yo ao[X] e from
   hi.map' f (LinearMap.ker_eq_bot.mpr aFf)
 classical
 rw [Fintype.linearIndependent_iff] at he ⊢
 intro c hc j
 by_contra hj
 let n:=Finset.univ.sup (fun i=>(c i).natDegree)
 have hn (i:ι) : (c i).natDegree≤n :=
   Finset.le_sup (f := fun i=>(c i).natDegree) (Lf i)
 have hd (i:ι) (m:Exponent) : ((e i).coeff m).natDegree≤anL h t m:= by
   by_cases hm:m∈(e i).support
   · have hh: ((e i).coeff m).natDegree+weight h m≤_:=hcut i m hm
     unfold anL
     omega
   · simp [MvPolynomial.notMem_support_iff.mp hm]
 have hz : (∑ i,(c i).coeff n•boundary h t (e i))=0:= by
   funext m
   simpa only [EP ,Pf ,sI,
     RJ,coeff_mul_add_eq_of_natDegree_le (hn _) (hd _ m),
     RP ,Finsupp.zero_apply,zc,
     Finset.sum_apply,Pi.smul_apply,Ml,cDm]
     using nq (fun F:jK=>(F.coeff m).coeff (n+anL h t m)) hc
 have hlt (i:ι) (hi:c i≠0) : (c i).natDegree<n :=
   lt_of_le_of_ne (hn i) (fun h=>hi (leadingCoeff_eq_zero.mp (by
     rw [← coeff_natDegree,h,he _ hz i])))
 have hpos :=(C9 _).trans_lt (hlt j hj)
 have hle :n≤n - 1 :=Mz fun i _=> by
   by_cases hi:c i=0
   · simp [hi]
   · have hh:=hlt i hi
     omega
 omega
end
end axa
end
section
namespace aFP
noncomputable section
open K1 aR jA
open scoped Polynomial BigOperators
theorem aOE (Q:p6) :
  H9 Q=zg Eg Q:= by
 unfold H9 zg
 simp only [JW,sI,yB]
theorem cSA (f :ko) (hf :f≠0) (hu:gY f=0) :
   ∃ q:p6,q≠0∧q.totalDegree=vC f∧H9 q=lP f ∧
     ∀ z y,pz (ED z y) f=pz y q:= by
 have hsome :vw (Option.some :Fin 3→mA) :=Option.some_injective _
 have hv : (f.vars :Set mA)⊆Set.range (Option.some :Fin 3→mA) := by
   intro i hi
   cases i with
   | none=>exact ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hu).elim
   | some i=>exact ⟨i,rfl⟩
 obtain ⟨q,hq⟩:=MvPolynomial.exists_rename_eq_of_vars_subset_range f some hsome hv
 rw [← hq] at hf ⊢
 refine ⟨q,fun h=>hf (by simp [h]),?_,?_,?_⟩
 · rw [vC,OJ hsome,
     ← MvPolynomial.weightedTotalDegree_one]
   rfl
 · rw [lP,OJ hsome,
     aOE]
   rfl
 · intro z y
   rw [MvPolynomial.eval_rename]
   rfl
theorem c5T (p:iP[X]) (z :iP) (y :Fin 3→iP) :
   pz (ED z y) (YB p)=p.eval z := by
 let e :=pz (ED z y)
 have he :e.comp (x7 c9 (lz none)) =
     Polynomial.evalRingHom z := by
   apply C4
   · intro x
     simp [e]
   · simp [e,ED]
 exact oy he p
def a8n (Γ:pG K) (z :K→ao) (p:iP[X]) :pG K:= by
 classical
 exact Γ.filter fun γ=>p.eval (DI (z γ))=0
theorem b81 {Γ:pG K} {z :K→ao} {p:iP[X]} {γ:K} :
  γ∈a8n Γ z p↔γ∈Γ∧p.eval (DI (z γ))=0:= by
 classical
 simp [a8n]
theorem cIv (Γ:pG K) (z :K→ao) (hz :vw z)
  (p:iP[X]) (hp:p≠0) :
  (a8n Γ z p).card≤p.natDegree := by
 classical
 let B:=a8n Γ z p
 let e :K→iP:= fun γ=>DI (z γ)
 rw [show (a8n Γ z p).card=(B.image e).card by
  have he :vw e :=DI.injective.comp hz
  exact (Finset.card_image_of_injective B he).symm]
 apply Polynomial.card_le_degree_of_subset_roots
 intro x hx
 change x∈B.image e at hx
 obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
 exact (Polynomial.mem_roots hp).mpr (b81.mp hγ).2
theorem cAF {F G:ko} (hF:FU F)
  (hdeg:0<gY F) (hrel :IsRelPrime F G) :
  aGx F G≠0:= by
 let e :=xW iP (Fin 3)
 let φ:=mD p6 (FractionRing p6)
 have hinj:vw φ:=vh p6 (FractionRing p6)
 have hsize (P:ko) : (qN P).natDegree=gY P:= by
  simp [qN,gY]
 have hi:FU (qN F) :=(MulEquiv.irreducible_iff e).mpr hF
 have hp: (qN F).IsPrimitive :=hi.isPrimitive (by rw [hsize]; omega)
 have him:FU ((qN F).map φ) :=
  hp.irreducible_iff_irreducible_map_fraction_map.mp hi
 have hcop:qx ((qN F).map φ) ((qN G).map φ) := by
  apply him.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨a,ha⟩:=hp.dvd_of_fraction_map_dvd_fraction_map hd
  apply hF.isRelPrime_iff_not_dvd.mp hrel
  refine ⟨e.symm a,e.injective ?_⟩
  change e G=e F*a at ha
  simpa only [oq,e.apply_symm_apply] using ha
 have hn:=Polynomial.resultant_ne_zero _ _ hcop
 intro hz
 apply hn
 rw [Nr hinj,
  Nr hinj,hsize,hsize,Polynomial.resultant_map_map]
 change φ (aGx F G)=0
 rw [hz,xu]
theorem cAG {F G:ko} (hdeg:0<gY F)
    {z :iP} {y :Fin 3→iP}
    (hF:pz (ED z y) F=0)
    (hG:pz (ED z y) G=0) :
    pz y (aGx F G)=0:= by
  have hsize (P:ko) : (qN P).natDegree≤gY P:= by
    simp [qN,gY]
  obtain ⟨a,b,_,_,he⟩:=Polynomial.exists_mul_add_mul_eq_C_resultant
    (qN F) (qN G) (hsize F) (hsize G) (Dw (Nat.ne_of_gt hdeg))
  have hEval (P:ko) :
      x7 (pz y) z (qN P) =
        pz (ED z y) P:= by
    change (qN P).eval₂ (pz y) z= _
    rw [Polynomial.eval₂_eq_eval_map]
    exact (MvPolynomial.optionEquivLeft_elim_eval iP (Fin 3) y z P).symm
  have h:=nq (x7 (pz y) z) he
  simp only [qy ,oq,hEval F,hEval G,hF,hG,vZ,Av] at h
  change 0=(lI (aGx F G)).eval₂ (pz y) z at h
  simpa only [Pr] using h.symm
end
end aFP
end
section
namespace dm5
noncomputable section
open aR jA NR aFN
open scoped Polynomial BigOperators
private abbrev aGu:=mA →₀ ℕ
private abbrev Jp:=Fin 3 →₀ ℕ
private abbrev pO:ao[X] →+* kS:=mD _ _
private abbrev constMap:ao →+* kS:=mD _ _
private theorem gol (x :ao) :pO (lI x)=constMap x :=
 (yU ao ao[X] kS x).symm
private def cV (m:aGu) :ℕ :=
 m (some 0)+m (some 1)+m (some 2)
private def asm (m:aGu) (k :ℕ) :Jp :=
 p7 0 k+Finsupp.single 1 (m (some 1))+Finsupp.single 2 (m (some 2))
private theorem ddW (m:aGu) (k :ℕ) :
  asm m k 0=k∧asm m k 1=m (some 1) ∧
   asm m k 2=m (some 2) := by
 simp [asm,wB]
private theorem d5k (a :nI) (q:ℕ) (c:Slot a q) :
  exponent a q c 0+exponent a q c 1+exponent a q c 2=q:= by
 have h₂:c.1.val≤q :=
  (Ef c.1.isLt).trans (G0 _ _)
 have h₁:c.2.val≤q - c.1.val :=
  (Ef c.2.isLt).trans (G0 _ _)
 change q - c.1.val - c.2.val+c.2.val+c.1.val=q
 omega
private theorem aJI {a :nI} {F:jK} (hF:Jn a F)
    {m:aGu} (hm:m∈F.support) :
    cV m≤a.b∧m (some 1)+2*m (some 2)≤a.j ∧
      m (some 2)≤a.t∧m none≤70000:= by
  have hB:=vj
    (fun i:mA=>i.elim 0 (fun _=>1)) hm
  have hJ:=vj
    (fun i:mA=>i.elim 0 Eg) hm
  have hweight (w:mA→ℕ) :
      z7 w m=m none*w none+(m (some 0)*w (some 0) +
        m (some 1)*w (some 1)+m (some 2)*w (some 2)) := by
    rw [Finsupp.weight_apply,Finsupp.sum_fintype m (fun i c=>c•w i) (fun _=> by simp),
      NI ,qG ]
    simp only [sI]
  rw [hweight] at hB hJ
  refine ⟨?_,?_,(Gj _ hm).trans hF.2.2.1,
    (Gj _ hm).trans hF.2.2.2⟩
  · simpa [cV,vC] using hB.trans hF.1
  · simpa [lP,yB] using hJ.trans hF.2.1
private def bg8 (z :kS) (m:aGu) (k :ℕ) :kS :=
 (pO lJ)^m none*z^(m (some 0) - k)*(m (some 0)).choose k
private theorem dGE (z :kS) (m:aGu) (P:ao[X]) :
    GV z (ov m P) =
      ∑ k∈cy (m (some 0)+1),
        ov (asm m k)
          (lI (bg8 z m k)*P.map constMap) := by
  classical
  unfold GV
  rw [PA,
    Cy _ _ (fun _=>y5 _),Rm,Kz]
  simp only [qm,Kp,Option.elim,
    t4 ,p5 (show (1 :Fin 3)≠0 by decide),
    p5 (show (2 :Fin 3)≠0 by decide)]
  rw [add_pow]
  simp only [Finset.sum_mul,Ar]
  apply n5 rfl
  intro k _
  have hmon : (lz (0:Fin 3)^k*lz 1^m (some 1) *
      lz 2^m (some 2) :Lq) =
      ov (asm m k) 1 := by
    simp only [asm,TH,
      MvPolynomial.monomial_mul_monomial,mul_one]
  calc
    _=c9 (lI (bg8 z m k)*P.map constMap) *
        ov (asm m k) 1 := by
      rw [← hmon]
      simp only [bg8,oq,xI,map_natCast]
      ring
    _ = _:= by rw [Sv,mul_one]
private theorem cEz (z :kS) (F:jK) (e :Jp) :
    (GV z F).coeff e =
      ∑ m∈F.support,∑ k∈cy (m (some 0)+1),
        if asm m k=e then
          lI (bg8 z m k)*(F.coeff m).map constMap
        else 0:= by
  nth_rw 1 [F.as_sum]
  simp only [p9,dGE,EP ,yl]
private theorem cEy (z :kS) {a :nI} {F:jK}
  (hF:Jn a F) (e :Jp) (he :e∈(GV z F).support) :admissible a e := by
 classical
 by_contra ha
 apply MvPolynomial.mem_support_iff.mp he
 rw [cEz]
 apply xm
 intro m hm
 apply xm
 intro k hk
 refine p5 fun h=>ha ?_
 subst e
 obtain ⟨h₀,h₁,h₂⟩:=ddW m k
 obtain ⟨hB,hJ,hT,_⟩:=aJI hF hm
 simp only [admissible,h₀,h₁,h₂]
 have hk' : k≤ m (some 0) :=Ef (Finset.mem_range.mp hk)
 unfold cV at hB
 exact ⟨by omega,hJ,hT⟩
private def bcu (a :nI) (N D:ao[X]) (m:aGu) (k :ℕ) :
  ao[X] :=
 lI ((m (some 0)).choose k :ao)*lJ ^m none *
  N^(m (some 0) - k)*D^(a.b - cV m)
private def bCG (a :nI) (α:ao) (N D:ao[X]) (i:ℕ)
    (e :Jp) (m:aGu) :ao[X] →ₗ[ao] ao[X] := by
  classical
  exact ∑ k∈cy (m (some 0)+1),
    if asm m k=e then
      ((F9 ao i).comp (zi α)).smulRight
        (bcu a N D m k)
    else 0
private def BA (a :nI) (α:ao) (N D:ao[X]) (q:Fin (a.b+1)) :
  jK →ₗ[ao] (abE a q.val→ao[X]) :=
 FV fun c =>
  (Finsupp.lsum ao (bCG a α N D c.1.val (exponent a q.val c.2))).comp
    (AddMonoidAlgebra.coeffLinearEquiv ao).toLinearMap
private theorem bXk (a :nI) (α:ao) (N D:ao[X])
    (q:Fin (a.b+1)) (F:jK) (c:abE a q.val) :
    BA a α N D q F c =
      ∑ m∈F.support,∑ k∈cy (m (some 0)+1),
        if asm m k=exponent a q.val c.2 then
          ((F.coeff m).taylor α).coeff c.1.val•bcu a N D m k
        else 0:= by
  classical
  change Finsupp.lsum ao (bCG a α N D c.1.val (exponent a q.val c.2))
    F.coeff= _
  rw [Finsupp.lsum_apply]
  apply n5 rfl
  intro m _
  change bCG a α N D c.1.val (exponent a q.val c.2) m (F.coeff m)= _
  unfold bCG
  rw [RD]
  apply n5 rfl
  intro k _
  by_cases h:asm m k=exponent a q.val c.2 <;> simp [h]
private theorem b5x {a :nI} {q:ℕ} {c:Slot a q} {m:aGu} {k :ℕ}
  (hB:cV m≤a.b) (hk :k≤ m (some 0))
  (he :asm m k=exponent a q c) :
  a.b - q=(m (some 0) - k)+(a.b - cV m) := by
 have h:=d5k a q c
 rw [← he] at h
 obtain ⟨h₀,h₁,h₂⟩:=ddW m k
 rw [h₀,h₁,h₂] at h
 unfold cV at *
 omega
private theorem eyW (a :nI) {N D:ao[X]} (hD:pO D ≠0)
  (m:aGu) (k q:ℕ)
  (hq:a.b - q=(m (some 0) - k)+(a.b - cV m)) :
  pO (bcu a N D m k) =
    pO D^(a.b - q)*bg8 (pO N/pO D) m k := by
 simp only [bcu,bg8,oq,xI,map_natCast,hq,pow_add,
  div_pow]
 field_simp [MS _ hD]
private theorem cZl {a :nI} {α:ao} {N D:ao[X]} (hD:pO D ≠0)
    {F:jK} (hF:Jn a F) (q:Fin (a.b+1)) (c:abE a q.val) :
    pO (BA a α N D q F c) =
      pO D^(a.b - q.val) *
        bfj a α q.val c (GV (pO N/pO D) F) := by
  classical
  rw [bXk,bfj,cEz]
  simp only [p9,RJ,Ar]
  apply n5 rfl
  intro m hm
  apply n5 rfl
  intro k hk
  by_cases he :asm m k=exponent a q.val c.2
  · simp only [t8 he]
    rw [Polynomial.smul_eq_C_mul,oq,gol,
      eyW a hD m k q.val
        (b5x (aJI hF hm).1 (Ef (Finset.mem_range.mp hk)) he),
      Polynomial.taylor_mul,Kl,Polynomial.coeff_C_mul,
      ← Polynomial.map_taylor,FQ]
    ring
  · simp [he]
end
end dm5
end
section
namespace aFO
set_option backward.isDefEq.respectTransparency false
noncomputable section
open K1 aR jA NR Polynomial
open scoped Polynomial
@[simp] theorem cpt (H :ao[X]) :Q8 H 0=H := by
  simp [Q8]
@[simp] theorem cps (H :ao[X]) (ε:ao) :
   (Q8 H ε).natDegree=H.natDegree :=Polynomial.natDegree_add_C
theorem gqo {H :ao[X]} (hm:H.Monic) (hp:0<H.natDegree)
  (ε:ao) : (Q8 H ε).Monic :=
 hm.add_of_left (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp hp))
private theorem derivative_ne_zero {Γ s} (P:jF Γ s) :P.H.derivative≠0:= by
 let:CharP ao K1.p:=charP_of_injective_ringHom embed.injective K1.p
 have hcast: (P.H.natDegree :ao)≠0:= by
   intro hz
   have hp:=Nat.le_of_dvd P.small.1
     ((CharP.cast_eq_zero_iff ao K1.p P.H.natDegree).mp hz)
   change 2130706433≤P.H.natDegree at hp
   have hb:=P.small.2
   omega
 intro hz
 let n:=P.H.natDegree - 1
 have hn:n+1=P.H.natDegree :=Nat.sub_add_cancel P.small.1
 have he :P.H.derivative.coeff n=(0:ao[X]).coeff n :=
   nq (fun f :ao[X]=>f.coeff n) hz
 rw [coeff_derivative,hn,coeff_natDegree,P.monic.leadingCoeff,sH,zc] at he
 apply hcast
 rw [← hn,yJ,In]
 exact he
private theorem bUa {Γ s} (P:jF Γ s) {A:ao[X]}
  (h:qx A P.H) :A≠0:= by
 rintro rfl
 exact not_isUnit_of_natDegree_pos _ P.small.1 (isCoprime_zero_left.mp h)
private def b3L (H A:ao[X]) :pG ao:= by
 classical
 exact A.roots.toFinset.image (fun x => -H.eval x)
private theorem bDq {H A:ao[X]} (hA:A≠0) {ε:ao}
   (hε:ε∉b3L H A) :
   qx A (Q8 H ε) := by
 classical
 apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ao ao _ _).mpr
 intro x
 simp only [Polynomial.coe_aeval_eq_eval]
 by_cases hx :A.eval x=0
 · right
   intro h
   apply hε
   unfold b3L
   refine Finset.mem_image.mpr ⟨x,Multiset.mem_toFinset.mpr ((mem_roots hA).mpr hx),?_⟩
   have he :H.eval x+ε=0:= by simpa [Q8] using h
   exact (S1 he).symm
 · exact Dw hx
theorem egn {Γ s} (P:jF Γ s) :
    ∃ bad:pG ao,∀ ε∉bad,
      ∃ P' : jF ∅ (fun _:K=>(0:K[X])),
        P'.H= Q8 P.H ε∧cxD P P' ∧
          P'.H.natDegree=P.H.natDegree∧P'.H.Separable := by
  classical
  let badFor :=b3L P.H
  let badNodes :pG ao:=Finset.univ.image (fun i:I => -P.H.eval (qz (node i)))
  refine ⟨(((badFor P.c∪badFor P.q)∪badFor P.a₀) ∪
    badFor P.H.derivative)∪badNodes,?_⟩
  intro ε hε
  simp only [Finset.mem_union,not_or] at hε
  obtain ⟨⟨⟨⟨hc,hq⟩,ha⟩,hd⟩,hn⟩:=hε
  let H := Q8 P.H ε
  have hsep:H.Separable := by
    rw [Polynomial.separable_def]
    have he :H.derivative=P.H.derivative := by simp [H,Q8]
    rw [he]
    exact (bDq (derivative_ne_zero P) hd).symm
  let P' : jF ∅ (fun _:K=>(0:K[X])) :=
    { H :=H
      monic:=gqo P.monic P.small.1 ε
      small:= by simpa [H] using P.small
      nodes := by
        intro i hi
        apply hn
        refine Finset.mem_image.mpr ⟨i,Lf _,?_⟩
        have he :P.H.eval (qz (node i))+ε=0:= by simpa [H,Q8] using hi
        exact (S1 he).symm
      degree := by simp
      z :=P.z
      injective :=P.injective
      c:=P.c
      q:=P.q
      a₀:=P.a₀
      a₁:=P.a₁
      c_unit :=bDq (bUa P P.c_unit) hc
      q_unit :=bDq (bUa P P.q_unit) hq
      a₀_unit :=bDq (bUa P P.a₀_unit) ha
      regular := by simp
      residue := by simp }
  exact ⟨P',rfl,⟨⟨ε,rfl⟩,rfl,rfl,rfl,rfl⟩,cps _ _,
    hsep⟩
end
end aFO
end
section
namespace HM
open Rj Finset
open scoped BigOperators
private def exponent (q k :ℕ) :ℕ :=
 if 5000 - q≤k then 7300 - q - k - q else 0
private def powers (q k :ℕ) (i:Fin 6) :ℕ :=
 if i=4 then exponent q k else 0
private theorem agp (q k :ℕ) (f :Fin 6→ℤ) :
  (∑ i,(powers q k i:ℤ)*f i)=(exponent q k :ℤ)*f 4 := by
 simp [powers]
private def jO (q k :ℕ) :ℤ :=
 if k<2300 then OU q (2299 - k) else 0
private def aUg (q k :ℕ) :ℤ :=
 OU q 2300 - jO q k
private theorem cGW {q k :ℕ} (hlo:1151≤q) (hhi:q≤2300) :
   Bb q (aU k)=aUg q k := by
 have hd:iO q=q:=zm hhi
 have harg :min (2300:ℤ) (-offset k - 1)=2299 - k := by unfold aU; omega
 rw [Bb,hd,harg,aTY (by omega) (by omega),aUg,jO]
 by_cases hk :k<2300
 · rw [t8 hk,aTY (by omega) (by omega)]
 · rw [p5 hk,gd,t8 (by omega)]
private theorem d0x {q k :ℕ} (hq:1151≤q) :0≤aUg q k := by
 rw [aUg,sub_nonneg,jO]
 by_cases hk :k<2300
 · rw [ite_eq_left hk,show (2299:ℤ) - k=((2299 - k :ℕ) :ℤ) by omega]
   exact cDW (v :=2300) (by omega) (by omega)
 · rw [p5 hk]
   have h0:OU (q:ℤ) 0=1 := by
     rw [OU,zf (by omega : (0:ℤ) - q≤0)]
     decide
   have hm:=cDW (q:=q) (w:=0) (v :=2300) (by decide) (by omega)
   change OU (q:ℤ) 0≤OU q 2300 at hm
   omega
private theorem bBL {q k :ℕ} {r :ℤ} (hr :0≤ r)
    (h:Bb q (aU k) -
        max 0 (max (m5 (iO q) (pT q (aU k)))
          (m5 (K6 q (powers q k)) (D8 q (aU k) (powers q k))))≤ r) :
    (xR q (aU k) (powers q k) :ℤ)≤ r := by
  unfold xR
  split
  · simpa using hr
  · have h' := Hw h
    exact (Int.ofNat_le.mpr h').trans_eq (G3 hr)
private theorem dzo {q k :ℕ} (hlo:1151≤q) (hhi:q≤2300) :
  (xR q (aU k) (powers q k) :ℤ)≤aUg q k := by
 apply bBL (d0x hlo)
 rw [cGW hlo hhi]
 exact sub_le_self _ (C5 _ _)
private def Xl (q t:ℤ) :ℤ :=
 if t≤q then xV t else sG (q+1) - xV (2*q - t+1)
private theorem dzq {q j:ℕ} (hlo:1151≤q) (hhi:q≤2300) (hj:j<2300) :
    (xR q (aU (5000 - q+j)) (powers q (5000 - q+j)) :ℤ)≤Xl q (2300 - j) := by
  let k :=5000 - q+j
  let t:ℤ:=2300 - j
  let n:ℤ:=exponent q k
  change (xR q (aU k) (powers q k) :ℤ)≤Xl q t
  have hn:n=max 0 (t - q) := by
    have h:5000 - q≤k := by dsimp [k]; omega
    simp only [n,exponent,t8 h]
    dsimp [k,t]
    omega
  have ht:0<t∧t≤2300:= by dsimp [t]; omega
  have hk :2300≤k := by dsimp [k]; omega
  have hd:iO q=q:=zm hhi
  have ho:Ic q (aU k)=t:= by unfold Ic aU k t; omega
  have hcol:Bb q (aU k)=sG ((q:ℤ)+1) - xV (2*(q:ℤ) - 2300) := by
    rw [cGW hlo hhi,aUg,jO,p5 (not_lt.mpr hk),wR,dEx (by omega)]
  have hdeg:K6 q (powers q k)=(q:ℤ) - n:= by
    rw [K6,hd,agp]
    simp [yE,n]
  have hP:D8 q (aU k) (powers q k) 0=⟨0,2300 - k⟩:= by
    simp [D8,agp,pT,Jd,aU]
  have hQ:D8 q (aU k) (powers q k) 1=⟨(q:ℤ) - 1150,2*(q:ℤ) - 2300⟩:= by
    simp [D8,agp,pT,Jd,hd]
  have hO:D8 q (aU k) (powers q k) 2=⟨-n,t - 2*n⟩:= by
    simp [D8,agp,pT,Jd,ho,n,v9]
  have hP0:yC ⟨0,2300-(k :ℤ)⟩=0:= by
    simp [yC,max_eq_left (show (2300-(k :ℤ)+1)/2≤0 by omega),
      zf  (show 2300-(k :ℤ)≤0 by omega),sG]
  have hnet:Bb q (aU k) -
      m5 (K6 q (powers q k)) (D8 q (aU k) (powers q k)) =
      sG ((q:ℤ)+1) - sG ((q:ℤ) - n+1) + xV (t - 2*n) := by
    rw [hcol,m5,hdeg,ite_eq_right (by omega),Fin.sum_univ_three,hP,hQ,hO,hP0,
      cGR (by omega) (by omega),cGR (by omega) (by omega)]
    ring
  have hterm :Xl q t =
      sG ((q:ℤ)+1) - sG ((q:ℤ) - n+1) + xV (t - 2*n) := by
    by_cases h:t≤(q:ℤ)
    · have hn0:n=0:= by omega
      simp [ Xl,h,hn0]
    · have hn' : n=t - q:= by omega
      rw [ Xl,p5  h,
        show (q:ℤ) - n=2*(q:ℤ) - t by omega,
        show t - 2*n=2*(q:ℤ) - t by omega]
      linarith only [gEm (2*(q:ℤ) - t)]
  apply bBL
  · rw [hterm]
    exact add_nonneg (sub_nonneg.mpr (gEl (by omega) (by omega))) (aJX (by omega))
  · rw [hterm,← hnet]
    exact G1 ((u9 _ _).trans (u9 _ _)) _
private theorem gwJ (q:ℕ) (hhi:q≤2300) :
   6*(∑ k∈cy (5000 - q),aUg q k) =
     6*(5000-(q:ℤ))*OU q 2300-akx 2300+aQX (2300 - q) := by
 have hr : (∑ k∈cy (5000 - q),jO q k) = ∑ k∈cy 2300,OU q k := by
   have htrunc: (∑ k∈cy 2300,jO q k) = ∑ k∈cy (5000 - q),jO q k := by
     apply ze (xL (by omega))
     intro k _ hk
     simp [jO,not_lt.mpr (by simpa only [Du,not_lt] using hk :2300≤k)]
   rw [← htrunc,← z9 (fun k :ℕ=>OU q k) 2300]
   apply n5 rfl
   intro k hk
   have hk' := mem_range.mp hk
   rw [jO,t8 hk']
   exact nq (OU (q:ℤ)) (show (2299:ℤ) - k=((2300 - 1 - k :ℕ) :ℤ) by omega)
 have hw:=amJ (fun w=>xV (w+1)) akx cwN 0 2300
 have ht:=amJ (fun w=>sG (max 0 w)) aQX gEi (-(q:ℤ)) 2300
 have hz :aQX (-(q:ℤ))=0:= by simp [aQX]
 simp only [qJ,show akx 0=0 by decide,wR] at hw
 simp only [hz,wR,neg_add_eq_sub] at ht
 have hc:6*(∑ k∈cy 2300,OU (q:ℤ) k) =
     akx 2300-aQX (2300 - q) := by
   simp only [OU,wA,mul_sub]
   rw [hw,ht]
   simp only [LP]
 simp only [aUg,wA,sum_const,card_range,nsmul_eq_mul,hr]
 rw [mul_sub,hc,show ((5000 - q:ℕ) :ℤ)=5000 - q by omega]
 ring
private theorem gwR (q:ℕ) (hhi:q≤2300) :
    6*(∑ j∈cy 2300,Xl q (2300 - j)) =
      6*(2300-(q:ℤ))*sG ((q:ℤ)+1)+akx (2*(q:ℤ) - 2300) := by
  have hr : (∑ j∈cy 2300,Xl q (2300 - j)) =
      ∑ j∈cy 2300,Xl q ((j:ℤ)+1) := by
    rw [← z9 (fun j:ℕ=>Xl q ((j:ℤ)+1)) 2300]
    apply n5 rfl
    intro j hj
    have hj' := mem_range.mp hj
    exact nq (Xl (q:ℤ))
      (show (2300:ℤ) - j=((2300 - 1 - j:ℕ) :ℤ)+1 by omega)
  have hs : (∑ j∈cy 2300,Xl q ((j:ℤ)+1)) =
      (∑ j∈cy q,Xl q ((j:ℤ)+1)) +
      ∑ j∈cy (2300 - q),Xl q (((q+j:ℕ) :ℤ)+1) := by
    conv_lhs=>rw [show (2300:ℕ)=q+(2300 - q) by omega,Df]
  have ha : (∑ j∈cy q,Xl q ((j:ℤ)+1)) =
      ∑ j∈cy q,xV ((j:ℤ)+1) := by
    apply n5 rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [ Xl,t8 (by omega)]
  have hb: (∑ j∈cy (2300 - q),Xl q (((q+j:ℕ) :ℤ)+1)) =
      ((2300 - q:ℕ) :ℤ)*sG ((q:ℤ)+1) -
        ∑ j∈cy (2300 - q),xV ((q:ℤ) - j) := by
    have hconst: (∑ _j∈cy (2300 - q),sG ((q:ℤ)+1)) =
        ((2300 - q:ℕ) :ℤ)*sG ((q:ℤ)+1) := by simp
    rw [← hconst,← wA]
    apply n5 rfl
    intro j _
    push_cast
    rw [ Xl,p5 (by omega)]
    rw [show 2*(q:ℤ)-((q:ℤ)+j+1)+1=(q:ℤ) - j by ring]
  have hw:=amJ (fun w=>xV (w+1)) akx cwN 0 q
  simp only [qJ,show akx 0=0 by decide,wR] at hw
  rw [hr,hs,ha,hb,t7,mul_sub,hw,gxk]
  rw [show ((2300 - q:ℕ) :ℤ)=2300 - q by omega,
    show (q:ℤ)-(2300 - q)=2*(q:ℤ) - 2300 by ring]
  ring
private def budget (q:ℕ) :ℤ :=
 6*(5000-(q:ℤ))*OU q 2300-akx 2300+aQX (2300 - q) +
   (6*(2300-(q:ℤ))*sG ((q:ℤ)+1)+akx (2*(q:ℤ) - 2300))
private theorem aH4 {q:ℕ} (hlo:1151≤q) (hhi:q≤2300) :
   6*(Xi powers q:ℤ)≤budget q:= by
 have hcut:Xi powers q = ∑ k∈cy (7300 - q),xR q (aU k) (powers q k) := by
   symm
   apply ze (xL (Iw _ _))
   intro k _ hk
   have h:Ic q (aU k)≤0:= by unfold Ic aU; simp only [Du] at hk; omega
   simp [xR,h]
 rw [hcut,show 7300 - q=(5000 - q)+2300 by omega,sum_range_add,Nat.cast_add,
   JQ ,JQ ,t7 ,budget,← gwJ q hhi,← gwR q hhi]
 apply Mj <;> apply Vs _ (by decide) <;> apply qM
 · intro k _
   exact dzo (k :=k) hlo hhi
 · intro j hj
   exact dzq hlo hhi (mem_range.mp hj)
private def total:ℕ→ℤ
 | 0=>0
 | n+1=>total n+budget (1151+n)
private theorem asB (n:ℕ) :
   (∑ j∈cy n,budget (1151+j))=total n:= by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [sum_range_succ,ih,total]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ctS:total 1149=24493805604150:= by decide +kernel
theorem proof :Rj.c4 := by
 refine ⟨powers,?_⟩
 have h:=qM (s :=cy 1149) (fun j hj =>
  aH4 (q:=1151+j) (by omega) (by have :=mem_range.mp hj; omega))
 rw [← Ar,asB,ctS,← JQ] at h
 omega
end HM
end
section
namespace aFO
set_option backward.isDefEq.respectTransparency false
noncomputable section
open aR jA NR Polynomial
open scoped Polynomial BigOperators
def c1 :Prop :=
  ∀ (H c q a₀ a₁:ao[X]),H.Monic→0<H.natDegree →
    ∃ (N :I6[X]) (D:I6),∀ ε:ao,
      qx c (Q8 H ε)→ qx a₀ (Q8 H ε) →
      cAj H c q a₀ a₁ N D ε
def c2 :Prop :=
  ∀ (H :ao[X]),H.Monic→0<H.natDegree → ∀ (N :I6[X]) (D:I6)
    (n m:ℕ) (F:Fin m→jK),
    ∃ (k :ℕ) (M:Matrix (Fin k) (Fin m) ao[X]),
      ∀ (ε:ao),Wv ε D ≠0 → ∀ v :Fin m→ao,
        (M.map (pU ε)).mulVecLin v=0 ↔
          (c9 (jH (Q8 H ε)))^n ∣
            amA (Q8 H ε) (awc N D ε) (∑ j,v j•F j)
private theorem fS2 {E :Type*} [Field E] [Infinite E] {k m:ℕ}
    (M:Matrix (Fin k) (Fin m) E[X]) (bad:pG E) (r :ℕ)
    (h : ∀ ε∉bad,(M.map (pU ε)).rank≤ r) :
    (M.map (pU 0)).rank≤ r := by
  classical
  let B:=M.map (pU 0)
  let d:=B.rank
  obtain ⟨ι,col,hinj,hspan,hind⟩:=exists_linearIndependent' E B.col
  let:Finite ι:=Finite.of_injective col hinj
  let:yL ι:=Fintype.ofFinite ι
  have hcard:MO ι=d:= by
    rw [← finrank_span_eq_card hind,hspan,← Matrix.rank_eq_finrank_span_cols]
  let e :Fin d ≃ ι:=(Fintype.equivFinOfCardEq hcard).symm
  let cols :Fin d→Fin m:=col ∘ e
  have hli:yo E (fun j=>B.col (cols j)) :=hind.comp e e.injective
  obtain ⟨rows,hdet⟩ :=
    gR.aRz.bFA (B.submatrix id cols) (by
      intro v hv
      have hsum: (∑ j,v j•B.col (cols j))=0:= by
        funext i
        simpa only [Matrix.mulVec,dotProduct,Matrix.submatrix_apply,id_eq,Matrix.col,
          SU,Finset.sum_apply,Pi.smul_apply,sI,v9,
          Ml] using GB hv i
      funext j
      exact Fintype.linearIndependent_iff.mp hli v hsum j)
  let T:=M.submatrix rows cols
  have hT:T.det≠0:= by
    intro hz
    apply hdet
    change ((pU (0:E)).mapMatrix T).det=0
    rw [← (pU (0:E)).map_det,hz,xu]
  obtain ⟨ε,hε⟩:=Infinite.exists_notMem_finset (bad∪T.det.roots.toFinset)
  rw [Finset.mem_union,not_or] at hε
  have ht: (T.map (pU ε)).det≠0:= by
    change ((pU ε).mapMatrix T).det≠0
    rw [← (pU ε).map_det]
    exact fun hz=>hε.2 (Multiset.mem_toFinset.mpr ((mem_roots hT).mpr hz))
  have hr :=Matrix.rank_submatrix_le (M.map (pU ε)) rows cols
  change (T.map (pU ε)).rank≤_ at hr
  rw [Matrix.rank_of_det_ne_zero ht,Fintype.card_fin] at hr
  exact hr.trans (h ε hε.1)
private theorem fW0 {Γ:pG K1.K} {s :K1.K→K1.K[X]}
   (P:jF Γ s) (L:kH P) {N :I6[X]} {D:I6}
   (h:cAj P.H P.c P.q P.a₀ P.a₁ N D 0) :
   awc N D 0=ahH L.numerator L.denominator := by
 let A:=bu4 P.c P.a₀ P.a₁
 let R:=awc N D 0
 let S:=ahH L.numerator L.denominator
 let H :=jH P.H
 have hR:H∣A*R+bu5 P.q:= by
   simpa only [cpt] using h.generic_congruence
 have hS:H∣A*S+bu5 P.q:=L.generic_congruence
 have hsub:H∣R - S:= by
   have hu:qx A H :=L.generic_unit
   apply hu.symm.dvd_of_dvd_mul_left
   simpa only [add_sub_add_right_eq_sub,← mul_sub] using dvd_sub hR hS
 have hH :H.natDegree=P.H.natDegree :=P.monic.natDegree_map _
 have hRdeg:R.natDegree<H.natDegree := by
   rw [hH]
   exact ((KA _ _).trans natDegree_map_le).trans_lt
     (by simpa only [cpt] using h.small)
 have hSdeg:S.natDegree<H.natDegree := by
   rw [hH]
   exact ((KA _ _).trans natDegree_map_le).trans_lt L.small
 apply sub_eq_zero.mp
 by_contra hz
 exact (G4 ((natDegree_sub_le _ _).trans_lt (max_lt hRdeg hSdeg)))
   (SM hsub hz)
private theorem dL1 (V W:u8 ao jK) [uW ao V]
  {k m:ℕ} (B:Module.Basis (Fin m) ao V) (M:Matrix (Fin k) (Fin m) ao)
  (h : ∀ v,M.mulVecLin v=0↔(B.equivFun.symm v :jK)∈W) :
  TT V W=M.rank := by
 let f :=M.mulVecLin.comp B.equivFun.toLinearMap
 have hker :f.ker=W.comap V.subtype := by
  ext x
  simpa [f,LinearMap.mem_ker] using h (B.equivFun x)
 have hrange :f.range=M.mulVecLin.range :=
  LinearMap.range_comp_of_range_eq_top _ B.equivFun.range
 have hk :=Submodule.finrank_map_subtype_eq V f.ker
 rw [hker,Oc] at hk
 have hd:=Ok (K:=ao) (V := ↥V)
  (V₂:=Fin k→ao) f
 rw [hrange,← Matrix.rank,hker,← hk] at hd
 unfold TT
 omega
private theorem fW9 {Γ:pG K1.K} {s :K1.K→K1.K[X]}
 (P:jF Γ s) (L:kH P) (F:jK) :
 restore P L F=amA P.H (ahH L.numerator L.denominator) F:=rfl
theorem of_children (h1 :c1) (h2 :c2) :NR.c4 := by
 classical
 intro Γ s P L a V r hV hbound
 let:uW ao V:=hV
 obtain ⟨N,D,hres⟩:=h1 P.H P.c P.q P.a₀ P.a₁ P.monic P.small.1
 let:Module.Free ao ↥V:=Module.Free.of_divisionRing (K:=ao) (V := ↥V)
 let B:=Module.finBasis ao ↥V
 let F:= fun j=>(B j:jK)
 obtain ⟨k,M,hM⟩:=h2 P.H P.monic P.small.1 N D (a.b+a.j) (oz ao V) F
 have hmatch {Γ' : pG K1.K} {s' : K1.K→K1.K[X]}
     (P' : jF Γ' s') (L' : kH P') (ε:ao)
     (hd:Wv ε D ≠0) (hh:P'.H= Q8 P.H ε)
     (hr :ahH L'.numerator L'.denominator=awc N D ε) :
     TT V (amn P' L' a (jH P'.H))=(M.map (pU ε)).rank := by
   apply dL1 _ _ B
   intro v
   have hv : (B.equivFun.symm v :jK) = ∑ j,v j•F j:= by
     rw [B.equivFun_symm_apply]
     simp [F]
   rw [aVU,fW9,hh,hr,hv]
   exact hM ε hd v
 have hz :=hres 0 (by simpa using P.c_unit) (by simpa using P.a₀_unit)
 have hd {ε} (hz : (Wv ε D).eval 0≠0) :Wv ε D ≠0 :=
   fun he=>hz (by rw [he,eval_zero])
 rw [hmatch P L 0 (hd hz.at_zero) (cpt _).symm (fW0 P L hz).symm]
 obtain ⟨bad,hbad⟩:=egn P
 apply fS2 M bad r
 intro ε hε
 obtain ⟨P',hh,hs,hdeg,hsep⟩:=hbad ε hε
 obtain ⟨hc,hq,ha₀,ha₁⟩:=hs.2
 have hc' : qx P.c (Q8 P.H ε) := by rw [← hc,← hh]; exact P'.c_unit
 have ha' : qx P.a₀ (Q8 P.H ε) := by rw [← ha₀,← hh]; exact P'.a₀_unit
 have h' := hres ε hc' ha'
 let L' : kH P' :=
   { numerator :=N.map (Wv ε)
     denominator :=Wv ε D
     at_zero :=h'.at_zero
     small:= by rw [hh]; exact h'.small
     generic_unit := by rw [hc,ha₀,ha₁,hh]; exact h'.generic_unit
     generic_congruence := by rw [hc,ha₀,ha₁,hq,hh]; exact h'.generic_congruence
     regular := by simp
     quotient:= by simp }
 rw [← hmatch P' L' ε (hd h'.at_zero) hh rfl]
 exact hbound P' L' hs hdeg hsep
end
end aFO
end
section
namespace aFP
noncomputable section
open K1 aR jA
open scoped Polynomial BigOperators
def c2 :Prop :=
  ∀ F G:ko,
    (aGx F G).totalDegree ≤
      gY G*vC F+gY F*vC G ∧
    H9 (aGx F G) ≤
      gY G*lP F+gY F*lP G
end
end aFP
end
section
namespace axh
def bRT (P:p6) (threshold :ℕ) :Prop :=
 ∀ f :p6,Prime f → ¬ f^threshold∣P
end axh
end
section
namespace aw8
open jA NR
open scoped BigOperators
@[simp] theorem a1U (b:Bank) :b.box.j=2300:= by
  cases b <;> rfl
@[simp] theorem gO6 (b:Bank) :b.box.t=1150:= by
  cases b <;> rfl
theorem bZs (b:Bank) :131071*b.box.b≤b.cut+1 := by
 cases b <;> decide
def ama {M:Type*} [AddCommMonoid M] (B:ℕ) (f :ℕ→ℕ→ℕ→M) :M :=
  ∑ q∈cy (B+1),∑ k∈cy (min q 1150+1),
    ∑ l∈cy (min (q - k) (2300 - 2*k)+1),f q k l
def aEw (b:Bank) :ℕ:=b.cut+1 - 131071*b.box.b
def width (b:Bank) (h q k l:ℕ) :ℕ :=
 aEw b+131071*(b.box.b - q)+(l+2*k)+(2300+(b.box.b - q))*h
end aw8
end
section
namespace aiI
noncomputable section
open Polynomial K1 aR
def Pq (w:I→K) (T:ℕ) (P:af 4) :Prop :=
 aO (shape P) ⟨4012,1650,550⟩∧tB P T∧Contact w P
abbrev Symbol:=lV (Fin 4) ao
def LY (x :ao) :af 4 →+* Symbol :=
 oY (pU x)
def acO (P:Symbol) :ℕ :=
 P.support.sup (fun m=>m.sum (fun i a=>i.val*a))
end
end aiI
end
