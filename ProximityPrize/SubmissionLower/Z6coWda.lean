import ProximityPrize.SubmissionLower.ZAZ7Tec
set_option Elab.async false
open _root_ renaming CommRing → za6, Finset.sum_eq_single → zi6, Function.Injective → zq4, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.eval_X → zV6, Nat.sub_add_cancel → zxt, Nat.sub_le_sub_right → zIu, Polynomial.X → z7y
section
set_option backward.isDefEq.respectTransparency false
namespace qIPidRd
noncomputable section
open scoped Classical
open Polynomial
open cu (L)
open q8Z6NHc (Slot)
open qAW6lac (Index block aMp)
open qHJDQEb
private def form {R:Type} [za6 R] {m D A:ℕ}
   (u:Slot m D A→R) (x :R) :R[X] :=
 ∑ i,monomial i.val.1.val (u i*x^i.val.2.val)
private theorem map_form {R S:Type} [za6 R] [za6 S] {m D A:ℕ}
  (j:R →+* S) (u:Slot m D A→R) (x :R) :
  (form u x).map j=form (fun i=>j (u i)) (j x) := by
 simp only [form,Polynomial.map_sum,map_monomial,map_mul,map_pow]
private theorem eval_form {R:Type} [za6 R] {m D A:ℕ}
  (u:Slot m D A→R) (x y :R) : (form u x).eval y=aMp u x y := by
 simp only [form,aMp,eval_finsetSum,eval_monomial]
private theorem cSQ {R:Type} [za6 R] {m D A:ℕ}
  (u:Slot m D A→R) (x :R) : (form u x).natDegree≤ m :=
 natDegree_sum_le_of_forall_le _ _ fun i _ =>
  (natDegree_monomial_le _).trans (Nat.le_of_lt_succ i.val.1.isLt)
private theorem form_add {m D A:ℕ} (u v :Slot m D A→L) :
  form (fun i=>u i+v i) 0=form u 0+form v 0:= by
 simp only [form,add_mul,map_add,Finset.sum_add_distrib]
private theorem form_single {m D A:ℕ} (s :Slot m D A) (hs :s.val.2.val=0) :
   form (fun i=>if i=s then (1 :L) else 0) 0=(z7y:L[X])^s.val.1.val := by
 unfold form
 rw [zi6 s]
 · simp [hs,monomial_one_right_eq_X_pow]
 · intro i _ hi
   simp [hi]
 · simp
private structure ChartBlock (d D W m A:ℕ) (b:Fin 3) where
 emb:Slot m D A ↪ Index d D W
 bVH (i:Slot m D A) :block (emb i)=b
 free_iff (i:Slot m D A) :IsFree (emb i)↔i≠zeroSlot m D A
 coeff_eq (i:Slot m D A) :
  incCoeff (emb i)=adjust (fun j=>raw (emb j)) (coordX d D W) (coordY d D W) i
 root :aMp (fun i=>atInc (emb i)) (pointX d D W) (pointY d D W)=0
private def first (d D W:ℕ) :ChartBlock d D W d W 0 :=
 ⟨⟨Sum.inl,Sum.inl_injective⟩,fun _=>rfl,fun _=>Iff.rfl,fun _=>rfl,
   (incidence_roots d D W).1⟩
private def second (d D W:ℕ) :ChartBlock d D W d W 1 :=
 ⟨⟨fun i => .inr (.inl i),Sum.inr_injective.comp Sum.inl_injective⟩,
   fun _=>rfl,fun _=>Iff.rfl,fun _=>rfl,(incidence_roots d D W).2.1⟩
private def rL (d D W:ℕ) :ChartBlock d D W (d-1) (W-D) 2 :=
 ⟨⟨fun i => .inr (.inr i),Sum.inr_injective.comp Sum.inr_injective⟩,
   fun _=>rfl,fun _=>Iff.rfl,fun _=>rfl,(incidence_roots d D W).2.2⟩
private def origin {d D W:ℕ} (u:Index d D W→L) :IncRing d D W →+* L :=
 MvPolynomial.eval (Sum.elim (fun _=>0) (fun i=>u i.val))
private theorem originX {d D W:ℕ} (u:Index d D W→L) :
  origin u (coordX d D W)=0 :=
 zV6 _
private theorem originY {d D W:ℕ} (u:Index d D W→L) :
  origin u (coordY d D W)=0 :=
 zV6 _
private theorem specialize {d D W m A:ℕ} {b:Fin 3}
    (B:ChartBlock d D W m A b) (u:Index d D W→L) (v :Slot m D A→L)
    (hu : ∀ i,u (B.emb i)=v i) (hv :v (zeroSlot m D A)=0) :
    (form (fun i=>incCoeff (B.emb i)) (coordX d D W)).map (origin u)=form v 0:= by
  rw [map_form,originX]
  congr 1
  funext i
  rw [B.coeff_eq]
  by_cases hi:i=zeroSlot m D A
  · subst i
    rw [hv,adjust,ite_eq_left (rfl :zeroSlot m D A=zeroSlot m D A)]
    simp only [map_sub,aMp,map_sum,map_mul,map_pow,originX,originY]
    rw [zi6 (zeroSlot m D A)]
    · simp [zeroSlot]
    · intro j _ hj
      by_cases hx :j.val.2.val=0
      · have hy :j.val.1.val≠0:= fun h =>
          hj (Subtype.ext (Prod.ext (Fin.ext h) (Fin.ext hx)))
        simp [zero_pow hy]
      · simp [zero_pow hx]
    · simp
  · simp [adjust,hi,raw,(B.free_iff i).2 hi,origin,hu]
private def ySlot {m D A:ℕ} (t:ℕ) (ht:t≤ m) (hw:t*D ≤A) :Slot m D A :=
 ⟨(⟨t,Nat.lt_succ_of_le ht⟩,0),by simpa using hw⟩
private theorem zero_ne_ySlot {m D A t:ℕ} (ht:t≤ m) (hw:t*D ≤A) (h:t≠0) :
  zeroSlot m D A≠ySlot t ht hw :=
 fun e=>h (congrArg (fun i:Slot m D A=>i.val.1.val) e).symm
private theorem recover_root {K E :Type} [Field K] [Field E] (j:K →+* E) (y :E)
   {f g:K[X]} {q r :E[X]}
   (hf :f.map j=q*(z7y - C y)) (hg:g.map j=r*(z7y - C y))
   (hc:IsCoprime q r) :y∈Set.range j:= by
 let h:=EuclideanDomain.gcd f g
 have hd:h.map j∣z7y - C y := by
   obtain ⟨a,b,hab⟩:=hc
   have e :a*f.map j+b*g.map j=z7y - C y := by
     rw [hf,hg,← mul_assoc,← mul_assoc,← add_mul,hab,one_mul]
   rw [← e]
   exact dvd_add
     (dvd_mul_of_dvd_right (map_dvd (mapRingHom j) (EuclideanDomain.gcd_dvd_left f g)) _)
     (dvd_mul_of_dvd_right (map_dvd (mapRingHom j) (EuclideanDomain.gcd_dvd_right f g)) _)
 have hn:h≠0:= by
   intro hz
   rw [hz,Polynomial.map_zero,zero_dvd_iff] at hd
   exact X_sub_C_ne_zero y hd
 have hdeg:h.natDegree≤1 := by
   rw [← natDegree_map_eq_of_injective j.injective h,← natDegree_X_sub_C y]
   exact natDegree_le_of_dvd hd (X_sub_C_ne_zero y)
 have hz :h.eval₂ j y=0:=eval₂_gcd_eq_zero
   (by rw [← eval_map,hf]; simp) (by rw [← eval_map,hg]; simp)
 have hl:=eq_X_add_C_of_natDegree_le_one hdeg
 have hz' : j (h.coeff 1)*y+j (h.coeff 0)=0:= by
   conv at hz=>lhs; rw [hl]
   simpa using hz
 have ha :h.coeff 1≠0:= by
   intro ha
   have hb:h.coeff 0=0:= by
     apply j.injective
     simpa [ha] using hz'
   exact hn (by rw [hl,ha,hb]; simp)
 refine ⟨-h.coeff 0/h.coeff 1,?_⟩
 rw [map_div₀,map_neg,div_eq_iff ((_root_.map_ne_zero j).2 ha),mul_comm]
 exact (eq_neg_of_add_eq_zero_left hz').symm
private theorem lift_form {d D W m A:ℕ} {b k :Fin 3}
    (B:ChartBlock d D W m A b) (hk :b≠k) :
    ∃ f : (pointField d D W k)[X],
      f.map (algebraMap (pointField d D W k) (Incident d D W)) =
        (form (fun i=>incCoeff (B.emb i)) (coordX d D W)).map (algebraMap (IncRing d D W) _) := by
  let K:=pointField d D W k
  have hx :pointX d D W∈K:=IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have h (i:Slot m D A) :atInc (B.emb i)∈K:=K.algebraMap_mem
    (⟨_,IntermediateField.subset_adjoin _ _ ⟨B.emb i,by simpa only [Set.mem_ofPred_eq,B.bVH] using hk,
      rfl⟩⟩:pairField d D W k)
  refine ⟨form (fun i=>(⟨_,h i⟩:K)) ⟨_,hx⟩,?_⟩
  rw [map_form,map_form]
  rfl
private theorem recover {d D W m n A A' : ℕ} {b c k :Fin 3}
    (B:ChartBlock d D W m A b) (G:ChartBlock d D W n A' c)
    (hbc:b≠c) (hbk :b≠k) (hck :c≠k)
    (hm:2≤ m) (hn:2≤n) (hA:m*D ≤A) (hA' : n*D ≤A') :
    pointY d D W∈pointField d D W k := by
  let j:=algebraMap (IncRing d D W) (Incident d D W)
  let F:=form (fun i=>incCoeff (B.emb i)) (coordX d D W)
  let H :=form (fun i=>incCoeff (G.emb i)) (coordX d D W)
  let T: (IncRing d D W)[X] :=z7y - C (coordY d D W)
  let Q:=F /ₘ T
  let V:=H /ₘ T
  have ht:T.Monic:=monic_X_sub_C _
  have htdeg:T.natDegree=1 :=natDegree_X_sub_C _
  have hQ:Q.natDegree≤ m-1 := by
    rw [show Q=F /ₘ T from rfl,natDegree_divByMonic F ht,htdeg]
    exact zIu (cSQ _ _) 1
  have hV:V.natDegree≤n-1 := by
    rw [show V=H /ₘ T from rfl,natDegree_divByMonic H ht,htdeg]
    exact zIu (cSQ _ _) 1
  let s :Slot m D A:=ySlot m le_rfl hA
  let t:Slot n D A' := ySlot n le_rfl hA'
  have hw:1*D ≤A' := (Nat.mul_le_mul_right D (by omega :1≤n)).trans hA'
  let l:Slot n D A' := ySlot 1 (by omega) hw
  have sep (i:Slot m D A) (i' : Slot n D A') :B.emb i≠G.emb i' := by
    intro h
    exact hbc ((B.bVH i).symm.trans ((congrArg block h).trans (G.bVH i')))
  let u (i:Index d D W) :L :=
    (if i=B.emb s then 1 else 0)+((if i=G.emb t then 1 else 0)+(if i=G.emb l then 1 else 0))
  let σ:=origin u
  have hF:F.map σ=(z7y:L[X])^m:= by
    rw [specialize B u (fun i=>if i=s then 1 else 0)
      (fun i=> by simp [u,sep,B.emb.injective.eq_iff])
      (by simp [s,zero_ne_ySlot _ _ (by omega :m≠0)]),form_single s rfl]
    rfl
  have hH :H.map σ=(z7y:L[X])^n+Polynomial.X:= by
    rw [specialize G u (fun i=>(if i=t then 1 else 0)+(if i=l then 1 else 0))
      (fun i=> by simp [u,(sep s i).symm,G.emb.injective.eq_iff])
      (by simp [t,l,zero_ne_ySlot _ _ (by omega :n≠0),zero_ne_ySlot _ _ Nat.one_ne_zero]),
      form_add,form_single t rfl,form_single l rfl]
    simp [t,l,ySlot]
  have hT:T.map σ=Polynomial.X:= by
    simp only [T,Polynomial.map_sub,Polynomial.map_X,map_C,show σ (coordY d D W)=0 from originY u,
      C_0,sub_zero]
  have hQs :Q.map σ=(z7y:L[X])^(m-1) := by
    rw [show Q=F /ₘ T from rfl,map_divByMonic σ ht,hT,hF,
      show (z7y:L[X])^m=z7y*z7y^(m-1) by
        rw [← pow_succ',zxt (by omega :1≤ m)],
      mul_divByMonic_cancel_left _ monic_X]
  have hVs :V.map σ=(z7y:L[X])^(n-1)+1 := by
    rw [show V=H /ₘ T from rfl,map_divByMonic σ ht,hT,hH,
      show (z7y:L[X])^n+Polynomial.X=z7y*(z7y^(n-1)+1) by
        rw [mul_add,mul_one,← pow_succ',zxt (by omega :1≤n)],
      mul_divByMonic_cancel_left _ monic_X]
  have hres : (Q.map j).resultant (V.map j) (m-1) (n-1)≠0:= by
    rw [resultant_map_map,← j.map_zero]
    apply (IsFractionRing.injective (IncRing d D W) (Incident d D W)).ne
    intro he
    have hh:σ (Q.resultant V (m-1) (n-1))=0:= by rw [he,map_zero]
    have hcap: ((z7y:L[X])^(n-1)+1).natDegree≤n-1 :=
      (natDegree_add_le _ _).trans (by simp)
    rw [← resultant_map_map,hQs,hVs,resultant_X_pow_left _ _ _ hcap] at hh
    simp [coeff_X_pow,show 0≠n-1 by omega] at hh
  obtain ⟨a,e,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant (Q.map j) (V.map j)
    (natDegree_map_le.trans hQ) (natDegree_map_le.trans hV) (Or.inl (by omega))
  have hcop:IsCoprime (Q.map j) (V.map j) := by
    let r :=(Q.map j).resultant (V.map j) (m-1) (n-1)
    refine ⟨a*C r⁻¹,e*C r⁻¹,?_⟩
    calc
      (a*C r⁻¹)*Q.map j+(e*C r⁻¹)*V.map j =
          (Q.map j*a+V.map j*e)*C r⁻¹:= by ring
      _=1 := by rw [hab,← C_mul,mul_inv_cancel₀ hres,C_1]
  obtain ⟨f,hf⟩:=lift_form B hbk
  obtain ⟨g,hg⟩:=lift_form G hck
  have factor {a : (IncRing d D W)[X]} (ha :IsRoot (a.map j) (pointY d D W)) :
      a.map j=(a /ₘ T).map j*(z7y - C (pointY d D W)) := by
    have he :T.map j=z7y - C (pointY d D W) := by simp [T,pointY,j]
    rw [map_divByMonic j ht,he,mul_comm]
    exact (mul_divByMonic_eq_iff_isRoot.mpr ha).symm
  have root {v B' : ℕ} {a :Fin 3} (S:ChartBlock d D W v B' a) :
      IsRoot ((form (fun i=>incCoeff (S.emb i)) (coordX d D W)).map j) (pointY d D W) := by
    rw [IsRoot,map_form,eval_form]
    exact S.root
  obtain ⟨z,hz⟩:=recover_root (algebraMap (pointField d D W k) (Incident d D W)) (pointY d D W)
    (hf.trans (factor (root B))) (hg.trans (factor (root G))) hcop
  rw [← hz]
  exact z.property
theorem proof :qHJDQEb.c2 := by
 intro d D W _ _ hd hW k
 have hs : (d-1)*D ≤W-D:= by
   rw [Nat.sub_mul,one_mul]
   exact zIu hW D
 fin_cases k
 · exact recover (second d D W) (rL d D W) (by decide) (by decide) (by decide)
    (by omega) (by omega) hW hs
 · exact recover (first d D W) (rL d D W) (by decide) (by decide) (by decide)
    (by omega) (by omega) hW hs
 · exact recover (first d D W) (second d D W) (by decide) (by decide) (by decide)
    (by omega) (by omega) hW hW
end
end qIPidRd
end
section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency false
namespace q1XnGpd
noncomputable section
open Finset MvPolynomial
open scoped Matrix
open cu (L)
open q8Z6NHc (Slot)
open qAW6lac (Index jo block aMp)
open qHJDQEb
private theorem b0v {ι R:Type} [za6 R] {n:ℕ} (w:ι→ℕ)
   (M:Matrix (Fin n) (Fin n) (z3y ι R))
   (h : ∀ i j,(M i j).weightedTotalDegree w≤1) :
   M.det.weightedTotalDegree w≤n:= by
 classical
 rw [Matrix.det_apply]
 refine AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun σ _ => ?_)
 have hv : (∏ j,M (σ j) j).weightedTotalDegree w≤n:= by
   refine (AddMonoidAlgebra.supDegree_prod_le (map_zero (Finsupp.weight w))
     (map_add (Finsupp.weight w))).trans ?_
   change (∑ j,(M (σ j) j).weightedTotalDegree w)≤n
   exact (sum_le_sum fun j _=>h (σ j) j).trans_eq (by simp)
 change (Equiv.Perm.sign σ•(∏ j,M (σ j) j)).weightedTotalDegree w≤n
 rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
 · simpa only [hs,one_smul] using hv
 · have hn:Equiv.Perm.sign σ•(∏ j,M (σ j) j) = -(∏ j,M (σ j) j) := by simp [hs]
   rw [hn]
   exact AddMonoidAlgebra.supDegree_neg.le.trans hv
private theorem dN9 {J R E :Type} [Fintype J] [za6 R] [Field E]
  (f :R →+* E) (v :J→E)
  (hv : ∀ i,∃ a b:R,f b≠0∧f a=f b*v i) :
  ∃ δ:E,δ≠0 ∧ ∃ A:J→R,∀ i,f (A i)=δ*v i:= by
 classical
 choose a b hb hab using hv
 refine ⟨∏ i,f (b i),prod_ne_zero_iff.mpr (fun i _=>hb i),
  fun i=>(∏ j∈univ.erase i,b j)*a i,fun i => ?_⟩
 rw [map_mul,map_prod,hab,← mul_assoc,prod_erase_mul _ _ (mem_univ i)]
private theorem FT {R E ι σ:Type} [Field R] [Field E] [Algebra R E] [Fintype σ]
    (v :ι→E) (w:ι→ℕ) (K:IntermediateField R E)
    (hK:K=IntermediateField.adjoin R (Set.range fun i : {i // w i=0} => v i.val))
    (T:IntermediateField K E) [FiniteDimensional K T]
    (e :σ→ι) (he :zq4 e) (hw : ∀ i,w (e i)=1)
    (s :σ) (t:σ→T) (hts :t s=1)
    (hz : ∑ i,v (e i)*algebraMap T E (t i)=0) :
    ∃ Q:z3y ι R,Q≠0∧aeval v Q=0 ∧
      Q.weightedTotalDegree w≤zsE K T:= by
  classical
  let n:=zsE K T
  let b:Module.Basis (Fin n) K T:=Module.finBasis K T
  let Ret := {i:ι // w i=0}
  let z (i:Ret) :E :=v i.val
  let f :z3y Ret R →ₐ[R] E :=aeval z
  let u (j:σ×Fin n×Fin n) :E :=
    algebraMap K E (b.repr (t j.1*b j.2.2) j.2.1)
  have hu (j) : ∃ A B:z3y Ret R,f B≠0∧f A=f B*u j:= by
    by_cases h:u j=0
    · exact ⟨0,1,by simp,by simp [h]⟩
    have hm:u j∈K:=(b.repr (t j.1*b j.2.2) j.2.1).property
    rw [hK] at hm
    obtain ⟨A,B,hAB⟩:=(IntermediateField.mem_adjoin_range_iff R z (u j)).mp hm
    change u j=f A/f B at hAB
    have hB:f B≠0:= fun he=>h (by simp [hAB,he])
    exact ⟨A,B,hB,by rw [mul_comm]; exact (eq_div_iff hB).mp hAB |>.symm⟩
  obtain ⟨δ,hδ,A,hA⟩:=dN9 f.toRingHom u hu
  let ret:Ret→ι:=Subtype.val
  let M:Matrix (Fin n) (Fin n) (z3y ι R) :=
    fun r c => ∑ i,MvPolynomial.X (e i)*rename ret (A (i,r,c))
  have hentry (v :ι→E) (hv : ∀ i:Ret,v (ret i)=z i) (r c:Fin n) :
      (MvPolynomial.aeval v :z3y ι R →ₐ[R] E) (M r c) =
        ∑ i,v (e i)*(δ*u (i,r,c)) := by
    have hcomp:v ∘ ret=z :=funext hv
    simp only [M,map_sum,map_mul,aeval_X,aeval_rename,hcomp]
    exact sum_congr rfl fun i _=>congrArg (v (e i) * ·) (hA (i,r,c))
  refine ⟨M.det,?_,?_,b0v _ M ?_⟩
  · let v' (i:ι) :E :=if i=e s then 1 else if w i=1 then 0 else v i
    have hv (i:Ret) :v' (ret i)=z i:= by
      have hne :ret i≠e s := fun hij=>Nat.zero_ne_one
        (i.property.symm.trans ((congrArg w hij).trans (hw s)))
      simp [v',hne,z,ret,i.property]
    let ψ:z3y ι R →ₐ[R] E :=aeval v'
    have hdiag:ψ.mapMatrix M=Matrix.diagonal (fun _=>δ) := by
      ext r c
      change ψ (M r c)= _
      rw [hentry v' hv,sum_eq_single s]
      · have hval :v' (e s)=1 := by simp [v']
        rw [hval,one_mul]
        change δ*algebraMap K E (b.repr (t s*b c) r)= _
        rw [hts,one_mul,b.repr_self_apply,Matrix.diagonal_apply]
        by_cases h:c=r
        · subst c
          simp only [ite_true,map_one,mul_one]
        · simp only [ite_eq_right h,ite_eq_right (Ne.symm h),map_zero,mul_zero]
      · intro i _ hi
        have hne :e i≠e s := fun hij=>hi (he hij)
        simp [v',hne,hw]
      · simp
    intro hzero
    have hh:=congrArg ψ hzero
    rw [ψ.map_det,map_zero,hdiag,Matrix.det_diagonal] at hh
    exact (prod_ne_zero_iff.mpr fun _ _=>hδ) hh
  · let φ:z3y ι R →ₐ[R] E :=aeval v
    change φ M.det=0
    rw [φ.map_det]
    let row (r :Fin n) :E :=algebraMap T E (b r)
    have hcoords (i:σ) (c:Fin n) :
        (∑ r,u (i,r,c)*row r)=algebraMap T E (t i*b c) := by
      simpa only [map_sum,Algebra.smul_def,map_mul,← IsScalarTower.algebraMap_apply] using
        congrArg (algebraMap T E) (b.sum_repr (t i*b c))
    have hrow:row ᵥ* φ.mapMatrix M=0:= by
      funext c
      rw [Matrix.vecMul_apply_eq_sum]
      change ∑ r,row r*φ (M r c)=0
      calc
        _ = ∑ r,row r*(∑ i,v (e i)*(δ*u (i,r,c))) :=
          sum_congr rfl fun r _=>congrArg (row r * ·) (hentry v (fun _=>rfl) r c)
        _ = ∑ i,(v (e i)*δ) * ∑ r,u (i,r,c)*row r := by
          simp only [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun i _=>sum_congr rfl fun r _=> by ring
        _=(δ*row c) * ∑ i,v (e i)*algebraMap T E (t i) := by
          rw [mul_sum]
          exact sum_congr rfl fun i _=> by rw [hcoords,map_mul]; dsimp [row]; ring
        _=0:= by rw [hz,mul_zero]
    by_contra hdet
    have hzero :=Matrix.eq_zero_of_vecMul_eq_zero hdet hrow
    let j:Fin n:=⟨0,Module.finrank_pos⟩
    apply b.ne_zero j
    exact (algebraMap T E).injective ((congrFun hzero j).trans (map_zero _).symm)
  · intro r c
    refine AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun i _ => ?_)
    have hX:=(mem_restrictWeightedDegree_iff_weightedTotalDegree_le).mp
      (X_mem_restrictWeightedDegree (R:=R) w 1 (e i) (hw i).le)
    have hA0: (rename ret (A (i,r,c))).weightedTotalDegree w=0:= by
      rw [weightedTotalDegree_rename_of_injective Subtype.val_injective,
        show w ∘ ret=0 from funext fun j=>j.property]
      simp [weightedTotalDegree,Finsupp.weight_apply,Finsupp.sum]
    exact (weightedTotalDegree_mul_le _ _ _).trans (by simpa only [hA0,add_zero] using hX)
private theorem eliminateBlock {d D W a B:ℕ} (k :Fin 3)
    [hfin:FiniteDimensional (pairField d D W k) (pointField d D W k)]
    (hy :pointY d D W∈pointField d D W k)
    (e :Slot a D B→ Index d D W) (he :zq4 e)
    (hw : ∀ i,block (e i)=k)
    (hz :aMp (fun i=>atInc (e i)) (pointX d D W) (pointY d D W)=0) :
    ∃ Q:jo d D W,Q≠0∧incidence d D W Q=0 ∧
      Q.weightedTotalDegree (blockWeight k) ≤
        zsE (pairField d D W k) (pointField d D W k) := by
  classical
  let K:=pairField d D W k
  let T:=pointField d D W k
  let x :T:=⟨pointX d D W,IntermediateField.mem_adjoin_simple_self K _⟩
  let y :T:=⟨pointY d D W,hy⟩
  let t (i:Slot a D B) :T:=x^i.val.2.val*y^i.val.1.val
  let s :=zeroSlot a D B
  have hts :t s=1 := by simp [t,s,zeroSlot]
  have hset :Set.range (fun i : {i:Index d D W // blockWeight k i=0} => atInc i.val) =
      atInc '' {i:Index d D W | block i≠k} := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,by simpa [blockWeight] using i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,by simpa [blockWeight] using hi⟩,rfl⟩
  have hK:K=IntermediateField.adjoin L _ :=
    congrArg (IntermediateField.adjoin L) hset.symm
  have hx' : algebraMap T (Incident d D W) x=pointX d D W:=rfl
  have hy' : algebraMap T (Incident d D W) y=pointY d D W:=rfl
  have hroot : ∑ i,atInc (e i)*algebraMap T (Incident d D W) (t i)=0:= by
    simpa only [aMp,t,map_mul,map_pow,hx',hy',mul_assoc] using hz
  obtain ⟨Q,hQ,hinc,hdeg⟩ :=
    FT atInc (blockWeight k) K hK T e he
      (fun i=> by simp [blockWeight,hw i]) s t hts hroot
  exact ⟨Q,hQ,(incidence_over_field Q).mp hinc,hdeg⟩
theorem proof :qHJDQEb.c3:= by
 intro d D W _ _ _ _ k
 obtain ⟨h0,h1,h2⟩:=incidence_roots d D W
 fin_cases k <;> intro hfin hy
 · exact @eliminateBlock d D W d W 0 hfin hy Sum.inl Sum.inl_injective (fun _=>rfl) h0
 · exact @eliminateBlock d D W d W 1 hfin hy (fun i => .inr (.inl i))
    (Sum.inr_injective.comp Sum.inl_injective) (fun _=>rfl) h1
 · exact @eliminateBlock d D W (d-1) (W-D) 2 hfin hy (fun i => .inr (.inr i))
    (Sum.inr_injective.comp Sum.inr_injective) (fun _=>rfl) h2
end
end q1XnGpd
end
