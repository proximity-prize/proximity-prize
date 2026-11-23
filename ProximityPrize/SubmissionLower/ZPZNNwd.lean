import ProximityPrize.SubmissionLower.Z7Epuse
import ProximityPrize.SubmissionLower.ZODErLe
import ProximityPrize.SubmissionLower.ZhkBS3a
import ProximityPrize.SubmissionLower.ZlPdtnc
import ProximityPrize.SubmissionLower.Zx71HLe
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, Module.finrank → zsE, MvPolynomial.le_degreeOf_of_mem_support → zTo, Nat.add_le_add → z9f, Nat.add_le_add_right → zlr, Nat.le_of_lt_succ → zeh, Nat.lt_succ_of_le → zB1, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.mul_left_comm → zZ0, Nat.sub_le → z7J
set_option maxHeartbeats 1500000
section
set_option autoImplicit true
namespace qPY5jQe
noncomputable section
open P5 (p)
open P5_7_2 (fO)
open qHEUR1a (Raw embed height)
open qbIP9ia (wt flatten)
open Polynomial
abbrev degree :ℕ:=133774
abbrev threshold :ℕ:=7600000
abbrev modulus :ℕ:=threshold+1+degree
abbrev seedCap:ℕ:=137
abbrev slope :ℕ:=12500
def ordinateCap (b:fO) :ℕ:=if b.val=0 then 13 else 12
def rate (e :ℕ) :=e*1001+(e+5)+p*(e*2+(e+5))
abbrev weight (F:Raw) :=wt degree (flatten F)
def polar (e :ℕ) :=(6*e-2)*threshold-3*e^2*degree
def Sheet (F:Raw) :Prop :=
  Irreducible F∧Irreducible (embed F)∧0<F.natDegree∧F.natDegree≤13 ∧
    0<height F∧height F≤ seedCap
end
end qPY5jQe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qPY5jQe
noncomputable section
open Finset Polynomial
open P5 (K)
open cu (L Equation yq)
open qHEUR1a (Raw embed height)
open qbIP9ia hiding transfer
open Y3 (ek aka)
open private transfer from ProximityPrize.SubmissionLower.ZhkBS3a
private theorem product_coord {P Q:Flat} {m:Exps} {i:Vars} {a b:ℕ}
   (hm:m∈(P*Q).support) (hp : ∀ t∈P.support,t i≤a)
   (hq : ∀ t∈Q.support,t i≤b) :m i≤a+b :=
 (zTo _ hm).trans
   ((MvPolynomial.degreeOf_mul_le _ _ _).trans
     (z9f (MvPolynomial.degreeOf_le_iff.mpr hp) (MvPolynomial.degreeOf_le_iff.mpr hq)))
private theorem top_count {e :ℕ} (he :e≤13) :
  (∑ j:Fin (e+6),(j:ℕ)*degree)≤171*degree := by
 rw [← sum_mul,Fin.sum_univ_eq_sum_range (fun j:ℕ=>j)]
 apply ztf
 have hs : (∑ i∈range (e+6),i) ≤ ∑ i∈range 19,i :=
  sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _=>Nat.zero_le _)
 have h: (∑ i∈range 19,i)*2=19*(19-1) :=sum_range_id_mul_two 19
 omega
private theorem x5 (v :ℕ) :
   (1001*v+1)*(2*v+1)*(172*degree)<6*(1000*v+1)*(v+1)*modulus := by
 have h:6*(1000*v+1)*(v+1)*modulus =
     (1001*v+1)*(2*v+1)*(172*degree)+(0x142b3440*v^2+0x571039772*v+0x164f4f2) := by
   change 6*(1000*v+1)*(v+1)*7733775=(1001*v+1)*(2*v+1)*23009128+_
   ring
 rw [h]
 exact Nat.lt_add_of_pos_right (by positivity)
private theorem raw_remainder (n:ℕ) (U V:Flat) :
  ∃ B:Raw,flatten.symm U*flatten.symm V =
    flatten.symm (rem n (U*V))+aka (Polynomial.X^n)*B:= by
 refine ⟨flatten.symm ((U*V).divMonomial (Finsupp.single amm n)),?_⟩
 have hX:flatten.symm (MvPolynomial.X amm)=aka (Polynomial.X:L[X]) := by
  rw [← flatten_X,RingEquiv.symm_apply_apply]
 have h:=congrArg flatten.symm (rem_eq n (U*V))
 simpa only [map_mul,map_add,map_pow,hX] using h
theorem high_row {F:Raw} (hi:Irreducible F) (hpos :0<F.natDegree)
    {e :ℕ} (hdeg:F.natDegree≤e) (he :e≤13) (high:threshold<weight F)
    (T:Finset K) (z :K→K) (S:K→K[X])
    (hS : ∀ γ∈T,(S γ).natDegree≤degree)
    (hroots : ∀ γ∈T,yq (embed F) (z γ) (S γ)=0) :
    ∃ g:Equation,g.natDegree≤e+5∧(embed F).resultant g≠0 ∧
      (∀ (j:ℕ) (i:Fin 2),(g.coeff j).degreeOf i ≤
        (if i=0 then 1001 else 2)*height F) ∧
      ∀ γ∈T,yq g (z γ) (S γ)=0:= by
  classical
  let f :=flatten F
  let v :=height F
  let a :=1001*v
  let b:=2*v
  let I:=Idx 6 (1000*v) v (fun _=>modulus)
  let J:=Idx (e+6) a b (fun j=>j*degree)
  let Q:=Idx 1 a b (fun _=>degree)
  let mulF:=LinearMap.mulRight L f
  let cut: (I →₀ L) →ₗ[L] Flat :=(rem modulus).comp (mulF.comp rows)
  let pick (j:J) :Exps :=exps j.1.1 (modulus-1-j.1.2) (seedMon j.2.1 j.2.2)
  let test : (I →₀ L) →ₗ[L] (J→L) :=
    (LinearMap.pi fun j=>MvPolynomial.lcoeff L (pick j)).comp cut
  have hf0 : ¬ MvPolynomial.X amm∣f :=physical_not_dvd hi hpos
  have hinj:zq4 cut:= by
    apply (injective_iff_map_eq_zero cut).mpr
    intro H hz
    have hd:=rem_eq modulus (rows H*f)
    change rem modulus (rows H*f)=0 at hz
    rw [hz,zero_add] at hd
    have hh:=(MvPolynomial.X_prime (R:=L) (i:=amm)).pow_dvd_of_dvd_mul_right
      modulus hf0 ⟨_,hd⟩
    rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero] at hh
    apply rows_inj
    rw [map_zero]
    apply MvPolynomial.ext
    intro m
    by_cases hm:m∈(rows H).support
    · have hb:=(mem_coord.mp (rows_support H hm)).2.1
      exact (MvPolynomial.mem_support_iff.mp hm (by
        have he :=congrArg (fun A:Flat=>A.coeff m) hh
        rwa [MvPolynomial.coeff_modMonomial_of_not_le _ (Finsupp.single_le_iff.not.mpr hb.not_ge),
          AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at he)).elim
    · exact MvPolynomial.notMem_support_iff.mp hm
  have stock (H :I →₀ L) {m:Exps} (hm:m∈(cut H).support) :
      m none<e+6∧m amm< modulus∧m (seed 0)≤a∧m (seed 1)≤b:= by
    have hh:=rem_support hm
    have hs {t:Exps} (ht:t∈(rows H).support) :=mem_coord.mp (rows_support H ht)
    have hy :=product_coord hh.1 (fun t ht=>zeh (hs ht).1)
      (fun t ht=>(flat_deg ht).1.trans hdeg)
    refine ⟨by omega,hh.2,?_,?_⟩
    · have hz :=product_coord hh.1 (fun t ht=>(hs ht).2.2.1) (fun t ht=>(flat_deg ht).2 0)
      change m (seed 0)≤1001*v
      rw [Nat.succ_mul 1000 v]
      exact hz
    · have hz :=product_coord hh.1 (fun t ht=>(hs ht).2.2.2) (fun t ht=>(flat_deg ht).2 1)
      change m (seed 1)≤2*v
      rw [two_mul]
      exact hz
  have narrow (H :test.ker) :wt degree (cut H.val)< modulus := by
    apply Nat.lt_of_le_pred (by decide :0< modulus)
    apply wt_le
    intro m hm
    obtain ⟨hy,hx,ha,hb⟩:=stock H.val hm
    by_contra! hl
    rw [Nat.pred_eq_sub_one] at hl
    have htop:modulus-1-m amm< m none*degree := by omega
    let j:J :=
      ⟨⟨⟨m none,hy⟩,⟨modulus-1-m amm,htop⟩⟩,
        ⟨m (seed 0),zB1 ha⟩,⟨m (seed 1),zB1 hb⟩⟩
    have hj:pick j=m:= by
      change exps (m none) (modulus-1-(modulus-1-m amm)) _=m
      rw [show modulus-1-(modulus-1-m amm)=m amm by omega]
      exact exps_eta m
    have hz :=congrFun (LinearMap.mem_ker.mp H.property) j
    change (cut H.val).coeff (pick j)=0 at hz
    exact MvPolynomial.mem_support_iff.mp hm (hj ▸ hz)
  have hlarge :zsE L (Q →₀ L)<zsE L test.ker := by
    have hdim:zsE L (J→L)+Module.finrank L (Q →₀ L) <
        zsE L (I →₀ L) := by
      rw [Module.finrank_fintype_fun_eq_card,Module.finrank_finsupp_self,
        Module.finrank_finsupp_self]
      simp only [J,Q,I,idx_card,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,one_mul]
      refine lt_of_le_of_lt ?_ (show (a+1)*(b+1)*(172*degree) <
          (∑ _:Fin 6,modulus)*(1000*v+1)*(v+1) from by
        simpa only [a,b,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,
          Nat.mul_assoc,zZ0,Nat.mul_comm] using x5 v)
      rw [← add_mul,← add_mul]
      have hsum:=zlr (top_count he) degree
      exact (ztf (b+1) (ztf (a+1) hsum)).trans_eq (by ring)
    have hr :=test.finrank_range_add_finrank_ker
    have ht:=test.range.finrank_le
    omega
  have hex : ∃ H :test.ker,IsCoprime (ek (embed F))
      (ek (embed (flatten.symm (cut H.val)))) := by
    by_contra! hall
    let mulQ: (Q →₀ L) →ₗ[L] Flat :=mulF.comp rows
    have hout (H :test.ker) :cut H.val∈mulQ.range := by
      by_cases hz :cut H.val=0
      · rw [hz]
        exact mulQ.range.zero_mem
      have hdiv :=((ba5.efR hi hpos).isCoprime_or_dvd _).resolve_left (hall H)
      obtain ⟨R,hR⟩:=ba5.efO (hi.isPrimitive hpos.ne') hdiv
      have hmul :=congrArg flatten hR
      rw [RingEquiv.apply_symm_apply,map_mul] at hmul
      have hf :f≠0:=(map_ne_zero_iff _ flatten.injective).mpr hi.ne_zero
      have hR0:flatten R≠0:=right_ne_zero_of_mul (hmul ▸ hz)
      have hwt:wt degree (flatten R)<degree := by
        have hc:=narrow H
        rw [hmul] at hc
        change wt degree (f*flatten R)< modulus at hc
        have hweight:wt degree (f*flatten R)=wt degree f+wt degree (flatten R) :=
          MvPolynomial.weightedTotalDegree_mul _ _ _ hf hR0
        rw [hweight] at hc
        change threshold<wt degree f at high
        have hM:modulus=threshold+1+degree :=rfl
        omega
      have hmem:flatten R∈(@rows 1 a b (fun _=>degree)).range := by
        apply rows_range
        intro m hm
        have hsmall:=(wt_term degree hm).trans_lt hwt
        have hj:m none<1 := by
          by_contra! hn
          have ht:=ztf degree hn
          omega
        have hd (i:Vars) : (flatten R).degreeOf i≤(cut H.val).degreeOf i :=
          by rw [hmul,MvPolynomial.degreeOf_mul_eq hf hR0]; exact Nat.le_add_left _ _
        refine mem_coord.mpr ⟨hj,by omega,?_,?_⟩
        · exact (zTo _ hm).trans ((hd _).trans
            (MvPolynomial.degreeOf_le_iff.mpr fun t ht=>(stock H.val ht).2.2.1))
        · exact (zTo _ hm).trans ((hd _).trans
            (MvPolynomial.degreeOf_le_iff.mpr fun t ht=>(stock H.val ht).2.2.2))
      obtain ⟨A,hA⟩:=hmem
      exact ⟨A,by change rows A*f= _; rw [hA,hmul,mul_comm]⟩
    let out:=(cut.comp test.ker.subtype).codRestrict mulQ.range hout
    have ho:zq4 out:= by
      intro H H' hh
      exact Subtype.ext (hinj (congrArg Subtype.val hh))
    exact hlarge.not_ge ((LinearMap.finrank_le_finrank_of_injective ho).trans mulQ.finrank_range_le)
  obtain ⟨H,hcop⟩:=hex
  let G:=flatten.symm (cut H.val)
  obtain ⟨he,hcaps⟩:=output_bounds (G:=G) (n:=e+5) (a :=a) (b:=b) (by
    change ∀ m∈(flatten (flatten.symm (cut H.val))).support,_
    rw [RingEquiv.apply_symm_apply]
    intro m hm
    obtain ⟨hy,_,ha,hb⟩:=stock H.val hm
    exact ⟨by omega,ha,hb⟩)
  have hG:qt5AtZa.HeightLT degree modulus G:= by
    intro j m hm
    have hs :exps j ((G.coeff j).coeff m).natDegree m∈(flatten G).support :=
      MvPolynomial.mem_support_iff.mpr (by rw [flat_coeff]; exact leadingCoeff_ne_zero.mpr hm)
    have hh:=wt_term degree hs
    rw [exps_x,exps_y,show flatten G=cut H.val from RingEquiv.apply_symm_apply ..] at hh
    exact hh.trans_lt (narrow H)
  refine ⟨embed G,he,nonzero_resultant hcop,fun j i => ?_,fun γ hγ => ?_⟩
  · by_cases h:i=0 <;> simpa only [a,b,h,ite_true,ite_false] using hcaps j i
  · obtain ⟨B,hB⟩:=raw_remainder modulus (rows H.val) f
    have hf :flatten.symm f=F:=RingEquiv.symm_apply_apply ..
    rw [hf] at hB
    exact transfer (Q:=F) (a :=1) (by decide :0< modulus) (by rw [map_one,one_mul]) hG
      ⟨flatten.symm (rows H.val),B,hB⟩ (z γ) (S γ) (hS γ hγ) (hroots γ hγ)
end
end qPY5jQe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qPY5jQe
noncomputable section
open Polynomial Finset
open scoped Classical BigOperators
open P5 (K I p blockLength)
open P5_7_2 (fO jX)
open q7F2qKe (originBudget eHB)
open qzVScmb (last)
open cu (L FX Equation yq)
open Qt (gY Qc acG)


open qHEUR1a (Raw embed height)
open qQ9yWTb (count_resultant)
open qkgz7gb (PlaneCurve SmoothAt rV UJ ceilDiv planeFee)
open P5_7_3_5_2 (Prepared BranchBudget gap)


open private lift_factor from ProximityPrize.SubmissionLower.ZEXAOre
open private prepared_count from ProximityPrize.SubmissionLower.ZlPdtnc
open private eLM from ProximityPrize.SubmissionLower.ZIbuJkc
def c1 :Prop :=
  ∀ (F:Raw),Sheet F→weight F≤threshold →
    ∀ (T:Finset K) (z :K→K) (S:K→K[X]),Set.InjOn z (T:Set K) →
      (∀ γ∈T,yq (embed F) (z γ) (S γ)=0) →
      ∀ q:PlaneCurve,Irreducible q →
        Nonempty (Prepared q z S (T.filter fun γ=>SmoothAt q (rV z γ))
          degree F.natDegree threshold (height F))
def c2 :Prop :=P5_7_3_5_2.c2
def c3:Prop :=
  ∀ {q:PlaneCurve} {C:qb0hmCe.CurveModel q} {z :K→K} {s :K→K[X]}
    (F:P5_7_3_5_2.Sheet C z s) (e :ℕ),2≤F.d→F.d≤e→e≤13 →
    F.weight degree threshold→(∀ γ∈F.marks,(s γ).natDegree≤degree) →
    BranchBudget F degree (6+2*e) (polar e)
def c4 :Prop :=
  ∀ {q:PlaneCurve} {C:qb0hmCe.CurveModel q} {z :K→K} {s :K→K[X]}
    (F:P5_7_3_5_2.Sheet C z s),F.d = 1 →
    F.weight degree threshold→(∀ γ∈F.marks,(s γ).natDegree≤degree) →
    BranchBudget F degree 0 (2*threshold-degree)
private theorem low_room {e :ℕ} (he :1≤e) (hE :e≤13) :
  2*threshold-degree≤polar e∧7+6*e+4*e*e≤ slope ∧
  2*e*blockLength+polar e≤gap degree*(slope-(7+6*e+4*e*e)) := by
 interval_cases e <;> decide
private theorem smooth_rate {e u:ℕ} (he :1≤e) (hE :e≤13) (hu:1≤u) :
  (1+(6+2*e)+4*e)*u+ceilDiv (u*(2*e*blockLength+polar e)) (gap degree)+4*e*e≤ slope*u:= by
 obtain ⟨_,hbase,hpole⟩:=low_room he hE
 let a :=slope-(7+6*e+4*e*e)
 have hl:u*(2*e*blockLength+polar e)≤(u*a)*gap degree := by
  simpa only [a,zZ0,Nat.mul_assoc,Nat.mul_comm] using zBI u hpole
 have hc:ceilDiv (u*(2*e*blockLength+polar e)) (gap degree)≤u*a := by
  apply zeh
  unfold ceilDiv
  apply (Nat.div_lt_iff_lt_mul (by decide :0<gap degree)).mpr
  rw [Nat.succ_mul (u*a) (gap degree)]
  have hg:0<gap degree := by decide
  omega
 have ha :4*e*e≤(4*e*e)*u:= by
  simpa only [Nat.mul_one] using zBI (4*e*e) hu
 rw [show 1+(6+2*e)+4*e=7+6*e by ring]
 calc
  _≤(7+6*e)*u+u*a+(4*e*e)*u:=z9f (Nat.add_le_add_left hc _) ha
  _=((7+6*e+4*e*e)+a)*u:= by ring
  _=slope*u:= by rw [show (7+6*e+4*e*e)+a=slope from Nat.add_sub_of_le hbase]
private theorem eLK (B:ℕ) :planeFee B≤4*B^2 := by
 unfold planeFee
 have hd:2*B-1≤2*B:=z7J ..
 have hx : (2*B-1-1)*(2*B-1-2)≤(2*B)*(2*B) :=
  Nat.mul_le_mul ((z7J ..).trans hd) ((z7J ..).trans hd)
 have he : (2*B)*(2*B)/2=2*B^2 := by
  rw [show (2*B)*(2*B)=2*(2*B^2) by ring,Nat.mul_div_cancel_left _ (by decide)]
 calc
  _≤B*(2*B)+(2*B)*(2*B)/2 :=
    z9f (zBI _ hd) (Nat.div_le_div_right hx)
  _ = _:= by rw [he]; ring
private theorem low_count (prep:c1) (local_hit :c2) (nonlinear :c3) (linear :c4)
    {F:Raw} (hF:Sheet F) (hW:weight F≤threshold)
    {w:I→K} {T:Finset K} {z :K→K} {s :K→K[X]} (m:UJ degree w T z s)
    (hr : ∀ γ∈T,yq (embed F) (z γ) (s γ)=0) :
    T.card≤(4*slope^2*seedCap)*height F:= by
  let u:=height F
  let e :=F.natDegree
  obtain ⟨_,_,he,hE,hu,hU⟩:=(show Sheet F from hF)
  have hcount:qkgz7gb.SmoothCount T z (slope*u) := by
    intro q hq
    let U:=T.filter fun γ=>SmoothAt q (rV z γ)
    have hUT:U⊆T:=filter_subset _ _
    obtain ⟨Q⟩:=prep F hF hW T z s m.Kw hr q hq
    have branches (j:Fin Q.n) :BranchBudget (Q.part j) degree (6+2*e) (polar e) := by
      have hd: (Q.part j).d≤e :=
        (single_le_sum (fun i _=>Nat.zero_le (Q.part i).d) (mem_univ j)).trans Q.degree
      have hs : ∀ γ∈(Q.part j).marks,(s γ).natDegree≤degree :=
        fun γ hγ=>m.degree γ (hUT (Q.inside j hγ))
      by_cases h:2≤(Q.part j).d
      · exact nonlinear _ e h hd hE (Q.weight j) hs
      · have hd1 : (Q.part j).d = 1 :=le_antisymm (by omega) (Q.part j).positive
        obtain ⟨V,ho,hp⟩:=linear _ hd1 (Q.weight j) hs
        exact ⟨V,ho.trans (Nat.mul_le_mul_right _ (Nat.zero_le _)),
          hp.trans (Nat.mul_le_mul_right _ (low_room he hE).1)⟩
    exact (prepared_count local_hit m hUT Q (by decide) (hE.trans_lt (by decide)) branches).trans
      (Nat.mul_le_mul_right _ (smooth_rate he hE hu))
  have hb:0<slope*u:=Nat.mul_pos (by decide) hu
  have hp:2*(slope*u)<p :=
    (zBI _ (zBI _ hU)).trans_lt (by decide)
  have h:=eLM qCexLpd.proof quj0Mle.proof m.Kw hb hp hcount
  calc
    _≤4*(slope*u)^2 :=h.trans (eLK _)
    _=(4*slope^2*u)*u:= by ring
    _≤_:=ztf _ (zBI _ hU)
private theorem bgt (b:fO) :
  ordinateCap b≤13∧4*slope^2*seedCap≤ rate (ordinateCap b) := by
 by_cases h:b.val=0 <;> simp only [ordinateCap,h,ite_true,ite_false] <;> decide
private theorem caps (b:fO) :
  originBudget b (last b) 0≤ordinateCap b∧originBudget b (last b) 2≤ seedCap ∧
  ordinateCap b+rate (ordinateCap b)*originBudget b (last b) 2≤eHB b:= by
 fin_cases b <;> decide
private theorem Ca (b:fO) :0<(jX b).lo∧(jX b).hi≤2703:= by
 fin_cases b <;> decide
private theorem d5P (prep:c1) (local_hit :c2) (nonlinear :c3) (linear :c4)
   (b:fO) {w:I→K} {T:Finset K} {z :K→K} {s :K→K[X]}
   (m:UJ degree w T z s) {f :Equation}
   (hi:Irreducible f) (hpos :0<f.natDegree) (he :f.natDegree≤ordinateCap b)
   (hp:0<gY f) (hu:gY f≤ seedCap)
   (hr : ∀ γ∈T,yq f (z γ) (s γ)=0) :
   T.card≤ rate (ordinateCap b)*gY f := by
 obtain ⟨F,hF,ha⟩:=lift_factor hi
 have hirr :=ha.symm.irreducible hi
 have hd: (embed F).natDegree=f.natDegree :=
   le_antisymm (natDegree_le_of_dvd ha.dvd hi.ne_zero) (natDegree_le_of_dvd ha.dvd' hirr.ne_zero)
 have hdeg:F.natDegree=f.natDegree :=
   (natDegree_map_eq_of_injective (MvPolynomial.map_injective _
     (IsFractionRing.injective L[X] FX)) F).symm.trans hd
 have hh:height F=gY f := by
   have mono {g h:Equation} (hn:h≠0) (hgh:g∣h) :gY g≤gY h:= by
     obtain ⟨r,rfl⟩:=hgh
     rw [acG (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn)]
     exact Nat.le_add_right _ _
   exact le_antisymm (mono hi.ne_zero ha.dvd) (mono hirr.ne_zero ha.dvd')
 have roots (γ:K) (hγ:γ∈T) :yq (embed F) (z γ) (s γ)=0:= by
   obtain ⟨r,hr'⟩:=ha.dvd'
   have hz :=hr γ hγ
   rw [hr',yq,eval₂_mul]
   change f.eval₂ _ _=0 at hz
   rw [hz,zero_mul]
 let e :=ordinateCap b
 have ⟨hE,hR⟩:=bgt b
 have H :height F≤ seedCap:=hh ▸ hu
 rw [← hh]
 by_cases hW:threshold<weight F
 · obtain ⟨g,hg,hgR,hgc,hgr⟩:=high_row hF (hdeg ▸ hpos) (hdeg ▸ he) hE hW T z s m.degree roots
   have hA: (e*(1000+1)+(e+5))*height F<p:= by
     have h:=z9f (ztf (1000+1) hE) (zlr hE 5)
     exact (Nat.mul_le_mul h H).trans_lt (by decide)
   have h:=count_resultant (e :=e) (E :=e+5) (cz :=1000) (ct :=1)
     (hd ▸ hpos) (hd ▸ he) hg ((Qc _ _).mp le_rfl) hgc hgR hA m.Kw roots hgr
   exact h.trans_eq (by unfold rate; ring)
 · have hs :Sheet F:=⟨hF,hirr,hdeg ▸ hpos,hdeg ▸ he.trans hE,hh ▸ hp,H⟩
   exact (low_count prep local_hit nonlinear linear hs (le_of_not_gt hW) m roots).trans
     (ztf _ hR)
end
end qPY5jQe
end
