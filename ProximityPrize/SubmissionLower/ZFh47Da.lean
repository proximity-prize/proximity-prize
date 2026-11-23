import ProximityPrize.SubmissionLower.ZfWgThc
set_option Elab.async false
open _root_ renaming MvPolynomial.C → znf, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, MvPolynomial.eval₂Hom → zOD, MvPolynomial.map → zDK, MvPolynomial.totalDegree_mul → zhM, Nat.mul_assoc → zfR, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Polynomial.X → z7y, Polynomial.mapRingHom → zhd, Set.InjOn → zwm
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace quN7Z4a
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P5 (K I node blockLength)
open P5_7 (midAgreement)
open cu (L FX jz j9)

open DQ (DT)
open Cu
open private cK5 from ProximityPrize.SubmissionLower.CR
open private b1t from ProximityPrize.SubmissionLower.ZgdIx1d
open scoped BigOperators
private theorem line_bound {T:Finset K} {s :K→K[X]} {w:I→K} {D H :ℕ}
    (W:OF T s w D) (hd:D < midAgreement) (sites :Finset I)
    (hit : ∀ i∉sites,(T.filter (fun γ=>(s γ).eval (node i)=w i)).card≤H)
    (miss : ∀ i∈sites,(T.filter (fun γ=>(s γ).eval (node i)≠w i)).card≤H) :
    (T.card:ℚ)≤3*(blockLength:ℚ)/(midAgreement-D:ℕ)*H+1 := by
  classical
  let q:ℕ:=midAgreement - D
  have hq: (0:ℚ)<q:= by exact_mod_cast Nat.sub_pos_of_lt hd
  have hn:sites.card≤blockLength:= by
    simpa only [card_univ,IRSProfile.card_index] using card_le_card (subset_univ sites)
  let lg (γ:K) :=univ.filter (fun i=>(s γ).eval (node i)=w i)
  have sum_swap (S:Finset I) (P:K→ I→Prop) [∀ γ i,Decidable (P γ i)] :
      ∑ γ∈T,(S.filter (P γ)).card = ∑ i∈S,(T.filter fun γ=>P γ i).card:= by
    simp only [card_filter]
    rw [sum_comm]
  by_cases hsplit :q≤3*(midAgreement - sites.card)
  · let zJ:=univ \ sites
    have hsum: (midAgreement - sites.card)*T.card≤zJ.card*H := by
      calc
        _ = ∑ γ∈T,(midAgreement - sites.card) := by rw [sum_const,smul_eq_mul,Nat.mul_comm]
        _ ≤ ∑ γ∈T,(zJ.filter (fun i=>(s γ).eval (node i)=w i)).card:= by
          apply sum_le_sum
          intro γ hγ
          obtain ⟨B,hB,hv⟩:=W.lg γ hγ
          have hB' : midAgreement≤(lg γ).card :=
            hB.trans (card_le_card fun i hi=>mem_filter.mpr ⟨mem_univ _,hv i hi⟩)
          have hEq:zJ.filter (fun i=>(s γ).eval (node i)=w i)=lg γ \ sites := by
            ext i
            simp only [zJ,lg,mem_filter,mem_sdiff,mem_univ,true_and]
            exact and_comm
          rw [hEq]
          have hh:=card_le_card (s :=lg γ) (t:=(lg γ \ sites)∪sites) (by
            intro i hi
            by_cases h:i∈sites
            · exact mem_union_right _ h
            · exact mem_union_left _ (mem_sdiff.mpr ⟨hi,h⟩))
          have hu:=card_union_le (lg γ \ sites) sites
          omega
        _ = ∑ i∈zJ,(T.filter (fun γ=>(s γ).eval (node i)=w i)).card:=sum_swap _ _
        _≤_:= by
          rw [← Nat.nsmul_eq_mul,← sum_const]
          exact sum_le_sum fun i hi=>hit i (mem_sdiff.mp hi).2
    have hl:q*T.card≤3*blockLength*H := calc
      _≤(3*(midAgreement-sites.card))*T.card:=ztf _ hsplit
      _=3*((midAgreement-sites.card)*T.card) :=zfR _ _ _
      _≤3*(zJ.card*H) :=zBI _ hsum
      _≤_:= by
        rw [zfR]
        have ho:zJ.card≤blockLength:= by
          simpa only [card_univ,IRSProfile.card_index] using card_le_card (subset_univ zJ)
        exact zBI _ (ztf _ ho)
    have hh: (q:ℚ)*T.card≤3*(blockLength:ℚ)*H := by exact_mod_cast hl
    have hh' := (le_div_iff₀ hq).mpr (by rwa [mul_comm] : (T.card:ℚ)*q≤3*(blockLength:ℚ)*H)
    rw [mul_div_right_comm] at hh'
    exact hh'.trans (le_add_of_nonneg_right zero_le_one)
  · by_cases hT:T.Nonempty
    · let bad (γ:K) :=sites.filter (fun i=>(s γ).eval (node i)≠w i)
      obtain ⟨a,ha,hmin⟩:=exists_min_image T (fun γ=>(bad γ).card) hT
      have hpair (γ:K) (hγ:γ∈T.erase a) :sites.card - D ≤2*(bad γ).card:= by
        have hγT:=mem_of_mem_erase hγ
        let P:=s a - s γ
        have hp:P≠0:=sub_ne_zero.mpr fun he=>(ne_of_mem_erase hγ) (W.distinct ha hγT he).symm
        let common :=sites \ (bad a∪bad γ)
        have hc:common.card≤D:= by
          refine (gR.kL.agd node IRSProfile.domain.injective P hp _ ?_).trans
            ((natDegree_sub_le _ _).trans (max_le (W.degree a ha) (W.degree γ hγT)))
          intro i hi
          have his :=(mem_sdiff.mp hi).1
          have hv : ∀ x :K,i∉bad x→(s x).eval (node i)=w i:= fun x hx=> by
            by_contra hh
            exact hx (mem_filter.mpr ⟨his,hh⟩)
          change ((s a)-(s γ)).eval (node i)=0
          rw [eval_sub,hv a (fun hh=>(mem_sdiff.mp hi).2 (mem_union_left _ hh)),
            hv γ (fun hh=>(mem_sdiff.mp hi).2 (mem_union_right _ hh)),sub_self]
        have hsum:=card_sdiff_add_card_eq_card (s :=bad a∪bad γ) (t:=sites)
          (union_subset (filter_subset _ _) (filter_subset _ _))
        change common.card+(bad a∪bad γ).card=sites.card at hsum
        have hu:=card_union_le (bad a) (bad γ)
        have ha' := hmin γ hγT
        omega
      have hsum: (sites.card - D)*(T.card - 1)≤2*(sites.card*H) := calc
        _ = ∑ γ∈T.erase a,(sites.card - D) := by
          rw [sum_const,smul_eq_mul,card_erase_of_mem ha,Nat.mul_comm]
        _ ≤ ∑ γ∈T.erase a,2*(bad γ).card:=sum_le_sum hpair
        _ ≤ ∑ γ∈T,2*(bad γ).card:=sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (by simp)
        _=2 * ∑ i∈sites,(T.filter fun γ=>(s γ).eval (node i)≠w i).card:= by
          rw [← mul_sum]
          exact congrArg (2 * ·) (sum_swap sites (fun γ i=>(s γ).eval (node i)≠w i))
        _≤_:= by
          apply zBI
          rw [← Nat.nsmul_eq_mul,← sum_const]
          exact sum_le_sum miss
      have hlarge :2*q≤3*(sites.card - D) := by dsimp [q] at hsplit ⊢; omega
      have hl:q*(T.card - 1)≤3*blockLength*H := by
        have h:=(ztf (T.card - 1) hlarge).trans (by
          simpa only [zfR] using zBI 3 hsum)
        have h' := zBI 2 (ztf H hn)
        simp only [zfR] at h h' ⊢
        omega
      have hh: (q:ℚ)*((T.card - 1 :ℕ) :ℚ)≤3*(blockLength:ℚ)*H := by exact_mod_cast hl
      have hh' := (le_div_iff₀ hq).mpr (by
        rwa [mul_comm] : ((T.card-1 :ℕ) :ℚ)*q≤3*(blockLength:ℚ)*H)
      rw [mul_div_right_comm,Nat.cast_sub (card_pos.mpr hT),Nat.cast_one] at hh'
      exact sub_le_iff_le_add.mp hh'
    · rw [not_nonempty_iff_eq_empty.mp hT,card_empty,Nat.cast_zero]
      positivity
private theorem parameter_eval {n:ℕ} (z :K) (t:Fin n→L) (q:DT n) :
   MvPolynomial.aeval (aCn z t) (aa4 n (zDK (algebraMap L FX) q)) =
     algebraMap L FX (zY9 t q) := by
 change zY9 (aCn z t)
   (MvPolynomial.rename Sum.inr (zDK (algebraMap L FX) q))= _
 rw [MvPolynomial.eval_rename,MvPolynomial.eval_map]
 exact (MvPolynomial.eval₂_comp (algebraMap L FX) t q).symm
private theorem dSG {C₀:sQ} [Fact (Irreducible C₀)] {J T z s H}
   (S:Sheet C₀ J 1 H T z s) (hz :zwm z (T:Set K))
   (q:DT S.n) (hq:q.totalDegree≤1)
   (hproper :aa4 S.n (zDK (algebraMap L FX) q)∉EF S.bY)
   (V:Finset K) (hV:V⊆T) (hzeros : ∀ γ∈V,zY9 (S.parameter γ) q=0) :
   V.card≤H := by
 let pt (γ:K) :=aCn (z γ) (S.parameter γ)
 refine (cK5 S.n H (EF S.bY) (RingHom.ker_isPrime (W8 S.bY))
   S.height (zDK (algebraMap L FX) q) hproper V pt ?_ ?_).trans ?_
 · intro γ hγ η hη he
   exact hz (hV hγ) (hV hη) (jz.injective (congrFun he (Sum.inl 0)))
 · intro γ hγ
   exact ⟨S.onBase γ (hV hγ),by rw [parameter_eval,hzeros γ hγ,map_zero]⟩
 · have hle : (zDK (algebraMap L FX) q).totalDegree≤q.totalDegree :=
     Finset.sup_mono (MvPolynomial.support_map_subset _ _)
   exact (ztf H (hle.trans hq)).trans_eq (one_mul _)
private theorem taylor_degree {n:ℕ} (x :L) (f : (DT n)[X])
   (h : ∀ j,(f.coeff j).totalDegree≤1) (j:ℕ) :
   ((f.taylor (znf x)).coeff j).totalDegree≤1 := by
 classical
 let u:=znf (σ:=Fin n) x
 change ((taylor u f).coeff j).totalDegree≤1
 rw [f.as_sum_range_C_mul_X_pow,map_sum]
 simp only [finsetSum_coeff]
 apply MvPolynomial.totalDegree_finsetSum_le
 intro i _
 rw [taylor_mul,taylor_C,taylor_X_pow,coeff_C_mul]
 have he : ((z7y: (DT n)[X])+C u)^i =
     (((z7y:L[X])+C x)^i).map MvPolynomial.C:= by simp [u]
 rw [he,coeff_map]
 exact (zhM _ _).trans (by simpa using h i)
private theorem coeff_mul_at {P Q:L[X]} {j:ℕ}
   (hQ : ∀ i<j,Q.coeff i=0) :
   (Q*P).coeff j= Q.coeff j*P.coeff 0:= by
 classical
 rw [coeff_mul]
 refine Finset.sum_eq_single (j,0) ?_ ?_
 · intro k hk hne
   obtain ⟨a,b⟩:=k
   have hs :a+b=j :=
     (Finset.HasAntidiagonal.mem_antidiagonal (n:=j) (a :=(a,b))).mp hk
   have ha :a<j:= by
     by_contra! hn
     have he :a=j∧b=0:= by omega
     exact hne (Prod.ext he.1 he.2)
   simp only [hQ a ha,zero_mul]
 · simp
private theorem cTM {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
   {R:wJ C₀ J g} (A:yI R n) (q:DT n) :
   W8 A (aa4 n (zDK (algebraMap L FX) q)) =
     Mu C₀ (zOD (zT C₀) A.coordinate q) := by
 let f :=((W8 A).comp (aa4 n)).comp (zDK (algebraMap L FX))
 let m:=(Mu C₀).comp (zOD (zT C₀) A.coordinate)
 have h:f=m:= by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [f,m,W8,aa4,b1t]
   · intro i
     simp [f,m,W8,aa4]
 exact DFunLike.congr_fun h q
private theorem marked_eval {C₀:sQ} [Fact (Irreducible C₀)] {J T z s H}
  (S:Sheet C₀ J 1 H T z s) (q:DT S.n)
  (hq:aa4 S.n (zDK (algebraMap L FX) q)∈EF S.bY)
  {γ:K} (hγ:γ∈T) :zY9 (S.parameter γ) q=0:= by
 have h:=S.onBase γ hγ _ hq
 rw [parameter_eval,← map_zero (algebraMap L FX)] at h
 exact (algebraMap L FX).injective h
private theorem node_bounds {C₀:sQ} [Fact (Irreducible C₀)] {J T z s H}
    (S:Sheet C₀ J 1 H T z s) (hz :zwm z (T:Set K))
    (v :K→K) (y :K) (a b:DT S.n) (ha :a.totalDegree≤1) (hb:b.totalDegree≤1)
    (hne : let cut := (aa4 S.n).comp (zDK (algebraMap L FX))
      cut a∉EF S.bY∨cut b∉EF S.bY)
    (he : ∀ γ∈T,
      zY9 (S.parameter γ) b*algebraMap K L (v γ) +
        zY9 (S.parameter γ) a=0) :
    let cut:=(aa4 S.n).comp (zDK (algebraMap L FX))
    let q:=a+MvPolynomial.C (algebraMap K L y)*b
    (cut q∉EF S.bY→(T.filter (fun γ=>v γ=y)).card≤H) ∧
      (cut q∈EF S.bY→(T.filter (fun γ=>v γ≠y)).card≤H) := by
  classical
  dsimp only
  let cut:=(aa4 S.n).comp (zDK (algebraMap L FX))
  let e :=(W8 S.bY).comp cut
  let r :=algebraMap K L y
  let q:=a+MvPolynomial.C r*b
  have hd:q.totalDegree≤1 :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le ha
      ((zhM _ _).trans (by simpa only [MvPolynomial.totalDegree_C,zero_add] using hb)))
  constructor
  · intro hq
    refine dSG S hz q hd hq _ (filter_subset _ _) ?_
    intro γ hγ
    obtain ⟨hγ,heq⟩:=mem_filter.mp hγ
    have hi:=he γ hγ
    rw [heq] at hi
    let A:=zY9 (S.parameter γ) a
    let B:=zY9 (S.parameter γ) b
    change zY9 (S.parameter γ) (a+MvPolynomial.C r*b)=0
    rw [map_add,map_mul,z9X]
    change A+r*B=0
    rw [mul_comm r B,add_comm A (B*r)]
    exact hi
  · intro hq
    have hproper :cut b∉EF S.bY:= by
      intro hb'
      have hq' : e (a+MvPolynomial.C r*b)=0:=hq
      have hb'' : e b=0:=hb'
      rw [map_add,map_mul,hb'',mul_zero,add_zero] at hq'
      exact hne.elim (fun h=>h (show cut a∈EF S.bY from hq')) (fun h=>h hb')
    refine dSG S hz b hb hproper _ (filter_subset _ _) ?_
    intro γ hγ
    obtain ⟨hγ,hmiss⟩:=mem_filter.mp hγ
    have hm:=marked_eval S q hq hγ
    let A:=zY9 (S.parameter γ) a
    let B:=zY9 (S.parameter γ) b
    change zY9 (S.parameter γ) (a+MvPolynomial.C r*b)=0 at hm
    rw [map_add,map_mul,z9X] at hm
    change A+r*B=0 at hm
    by_contra hB
    have hr :B*r+A=0:= by
      rw [mul_comm B r,add_comm (r*B) A]
      exact hm
    have hf :B*algebraMap K L (v γ)+A=B*r+A:=(he γ hγ).trans hr.symm
    exact hmiss ((algebraMap K L).injective (mul_left_cancel₀ hB (add_right_cancel hf)))
theorem line {C₀:sQ} [Fact (Irreducible C₀)] {J T z s w D H}
    (S:Sheet C₀ J 1 H T z s) (hz :zwm z (T:Set K))
    (W:OF T s w D) (hD:D < midAgreement) :
    (T.card:ℚ)≤(1+3*(blockLength:ℚ)/(midAgreement-D:ℕ))*H+1 := by
  classical
  let A:=S.bY
  let e :=zOD (zT C₀) A.coordinate
  let below (q:DT S.n) :=aa4 S.n (zDK (algebraMap L FX) q)
  let f :=A.equation
  have f_linear :f=C (f.coeff 1)*z7y+C (f.coeff 0) := by
    have h:f.natDegree<2 :=Nat.lt_succ_of_le A.degree.1
    conv_lhs=>rw [f.as_sum_range_C_mul_X_pow' h]
    simp [sum_range_succ,add_comm]
  have f1 : (f.coeff 1).map e≠0:= by
    have he :=congrArg (fun F: ((oO C₀)[X])[X]=>F.coeff 1) A.generic_eq
    change (f.map (zhd e)).coeff 1 =
      (C (C (A.scale :oO C₀))*S.root.equation).coeff 1 at he
    rw [coeff_map,coeff_C_mul] at he
    change (f.coeff 1).map e= _ at he
    have hR:S.root.equation≠0:= fun h=> by
      have hdeg:=S.root.degree
      simp [h] at hdeg
    have hc:S.root.equation.coeff 1≠0:= by
      have h:=S.root.equation.coeff_natDegree
      rw [S.root.degree] at h
      rw [h]
      exact leadingCoeff_ne_zero.mpr hR
    rw [he]
    exact mul_ne_zero (C_ne_zero.mpr A.scale.ne_zero) hc
  have mem_iff (q:DT S.n) :below q∈EF A↔e q=0:= by
    change W8 A (below q)=0↔e q=0
    rw [cTM]
    exact map_eq_zero_iff _ (Mu C₀).injective
  let slot (i:I) (j k :ℕ) :=
    ((f.coeff j).taylor (znf (algebraMap K L (node i)))).coeff k
  have nonzero (i:I) : ∃ k,e (slot i 0 k)≠0∨e (slot i 1 k)≠0:= by
    by_contra! h
    apply f1
    apply (taylor_eq_zero (e (znf (algebraMap K L (node i)))) _).mp
    ext k
    rw [← map_taylor,coeff_map,coeff_zero]
    exact (h k).2
  let j (i:I) :=Nat.find (nonzero i)
  let p0 (i:I) :=slot i 0 (j i)
  let p1 (i:I) :=slot i 1 (j i)
  let q (i:I) :=p0 i+MvPolynomial.C (algebraMap K L (w i))*p1 i
  let sites :=univ.filter (fun i=>below (q i)∈EF A)
  have idx_ne (i:I) :e (p0 i)≠0∨e (p1 i)≠0:=Nat.find_spec (nonzero i)
  have lower (i:I) (a :ℕ) {k} (hk :k<j i) (ha :a=0∨a=1) :
      below (slot i a k)∈EF A:= by
    have h:=Nat.find_min (nonzero i) hk
    rcases ha with rfl | rfl
    · exact (mem_iff _).2 (not_not.mp (fun hn=>h (Or.inl hn)))
    · exact (mem_iff _).2 (not_not.mp (fun hn=>h (Or.inr hn)))
  have hdegree (i:I) (a k :ℕ) : (slot i a k).totalDegree≤1 :=taylor_degree _ _ (A.degree.2 a) k
  have identity (γ:K) (hγ:γ∈T) (i:I) :
      zY9 (S.parameter γ) (p1 i)*algebraMap K L ((s γ).eval (node i)) +
        zY9 (S.parameter γ) (p0 i)=0:= by
    let ev :=zY9 (S.parameter γ)
    let x :=algebraMap K L (node i)
    have he :=S.identity γ hγ
    change ((f.map (zhd ev)).eval (j9 (s γ)))=0 at he
    nth_rw 1 [f_linear] at he
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C,
      eval_add,eval_mul,eval_C,eval_X,Polynomial.coe_mapRingHom] at he
    have hc:=congrArg (fun F:L[X]=>(F.taylor x).coeff (j i)) he
    have hl (a k :ℕ) :
        (((f.coeff a).map ev).taylor x).coeff k=ev (slot i a k) := by
      rw [← show ev (znf x)=x from z9X x,← map_taylor,coeff_map]
    simp only [map_add,taylor_mul,map_zero,coeff_add,coeff_zero] at hc
    rw [coeff_mul_at (fun k hk=> by
      rw [hl]
      exact marked_eval S _ (lower i 1 hk (Or.inr rfl)) hγ)] at hc
    have hx : (j9 (s γ)).eval x=algebraMap K L ((s γ).eval (node i)) :=
      Polynomial.eval_map_apply (p:=s γ) (algebraMap K L) (node i)
    simpa only [hl,taylor_coeff_zero,hx] using hc
  have counts (i:I) :=
    node_bounds S hz (fun γ=>(s γ).eval (node i)) (w i) (p0 i) (p1 i)
      (hdegree i 0 (j i)) (hdegree i 1 (j i))
      ((idx_ne i).imp (fun h he=>h ((mem_iff _).mp he)) (fun h he=>h ((mem_iff _).mp he)))
      (fun γ hγ=>identity γ hγ i)
  refine (line_bound W hD sites (fun i hi=>(counts i).1 ?_) (fun i hi=>(counts i).2 ?_)).trans ?_
  · exact fun hh=>hi (mem_filter.mpr ⟨mem_univ _,hh⟩)
  · exact (mem_filter.mp hi).2
  · rw [add_mul,one_mul,add_assoc]
    exact le_add_of_nonneg_left (Nat.cast_nonneg H)
end
end quN7Z4a
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace quN7Z4a
noncomputable section
open MvPolynomial
open P5 (K p)
open cu (L)
open Cu (sQ)
open scoped Classical
open private eLU from ProximityPrize.SubmissionLower.G
theorem singular_bound (C₀:sQ) (hC:Irreducible C₀) (hd:0<C₀.totalDegree)
   (hp:C₀.totalDegree<p) {T:Finset K} {z :K→K}
   (hz :zwm z (T:Set K))
   (hseed : ∀ γ∈T,C₀.eval (Z7 (z γ))=0) :
   (T.filter fun γ => ¬Smooth C₀ (Z7 (z γ))).card≤C₀.totalDegree*(C₀.totalDegree-1) := by
 classical
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 have hvars :C₀.vars.Nonempty :=Finset.nonempty_iff_ne_empty.mpr fun he=> by
   have h:=(vars_eq_empty_iff_eq_C.mp he)
   rw [h,totalDegree_C] at hd
   exact (Nat.lt_irrefl _ hd)
 obtain ⟨i,hi⟩:=hvars
 have hi' : 0<C₀.degreeOf i:=Nat.pos_of_ne_zero (mem_vars_iff_degreeOf_ne_zero.mp hi)
 have hcast: (C₀.degreeOf i:L)≠0:= fun h =>
   (not_le_of_gt ((C₀.degreeOf_le_totalDegree i).trans_lt hp))
     (Nat.le_of_dvd hi' ((CharP.cast_eq_zero_iff L p _).mp h))
 let Q:=pderiv i C₀
 have hQ:Q≠0:=pderiv_ne_zero_of_natCast_ne_zero i C₀ hcast
 have hdeg:Q.totalDegree≤C₀.totalDegree - 1 := by
   simpa only [weightedTotalDegree_one,Pi.one_apply] using weightedTotalDegree_pderiv_le_sub 1 i C₀
 have hproper :Q∉Ideal.span {C₀} := fun h=> by
   have hh:=MvPolynomial.totalDegree_le_of_dvd_of_isDomain (Ideal.mem_span_singleton.mp h) hQ
   omega
 let U:=T.filter fun γ => ¬Smooth C₀ (Z7 (z γ))
 let pt:=Z7 ∘ z
 have hinj:zwm pt (U:Set K) := fun γ hγ δ hδ he =>
   hz (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hδ).1
     ((algebraMap K L).injective (congrFun he 0))
 rw [← Finset.card_image_of_injOn hinj]
 refine (eLU C₀ Q hC hproper (U.image pt) ?_).trans (zBI _ hdeg)
 intro x hx
 obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
 obtain ⟨hγT,hγs⟩:=Finset.mem_filter.mp hγ
 exact ⟨hseed γ hγT,not_not.mp (fun h=>hγs ⟨i,h⟩)⟩
end
end quN7Z4a
end
