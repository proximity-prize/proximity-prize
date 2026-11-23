import ProximityPrize.SubmissionLower.Zqby9gc
import ProximityPrize.SubmissionLower.ZwYh3la
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace q9scLLa
noncomputable section
open Finset
open Polynomial
open P6 (K p)
open cu (L FX Equation)
open P6_7_1 (Input degree)
open qHEUR1a (Raw embed height threshold)
open qbIP9ia
open Y3 (ek)
open private azZ abn cZx fTI from ProximityPrize.SubmissionLower.BJ
open private rawAt_deg from ProximityPrize.SubmissionLower.Z7Epuse
private theorem flat_high_at {F:Raw} (hw:threshold<weight F) :
    threshold<wt degree (flatten F) := by
  by_contra! h
  apply hw.not_ge
  classical
  apply Finset.sup_le fun j _=>Finset.sup_le fun m hm => ?_
  have hc:exps j ((F.coeff j).coeff m).natDegree m∈(flatten F).support :=
    MvPolynomial.mem_support_iff.mpr (by
      rw [flat_coeff]
      exact leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm))
  simpa only [exps_x,exps_y] using (wt_term degree hc).trans h
private theorem bPb {n:ℕ} (hn:0<n) {F G H B:Flat}
    (he :H*F=G+MvPolynomial.X amm^n*B) (hw:wt degree G<n)
    (x :Input) {γ:K} (hγ:γ∈x.Γ) (hr :Zk x (embed (flatten.symm F)) γ) :
    Zk x (embed (flatten.symm G)) γ:= by
  let z :=x.M.label γ
  let S:=x.F.scalar γ
  let ev :=azZ (abn z p) S
  have hD:S.natDegree≤degree :=
    (P6_7.aic x.F hγ).trans (Nat.add_le_add_left (qFAh60c.emz x).2 _)
  have hF:ev (flatten.symm F)=0 :=
    (IsFractionRing.injective L[X] FX) (by rw [cZx,map_zero]; exact hr)
  let E :Flat →+* Polynomial L:=ev.comp flatten.symm.toRingHom
  have hX:E (MvPolynomial.X amm)=Polynomial.X:= by
    change ev (flatten.symm (MvPolynomial.X amm))= _
    rw [← flatten_X,RingEquiv.symm_apply_apply,fTI]
  have hF' : E F=0:=hF
  have hrel :=congrArg E he
  rw [map_mul,map_add,map_mul,map_pow,hX,hF',mul_zero] at hrel
  have hdvd: (Polynomial.X:L[X])^n∣ev (flatten.symm G) :=
    ⟨-ev (flatten.symm B),by rw [mul_neg]; exact eq_neg_of_add_eq_zero_left hrel.symm⟩
  have hzero :ev (flatten.symm G)=0:= by
    by_contra hne
    have hle :=natDegree_le_of_dvd hdvd hne
    rw [natDegree_X_pow] at hle
    exact (rawAt_deg hn (by simpa only [RingEquiv.apply_symm_apply] using hw) _ hD).not_ge hle
  unfold Zk
  rw [← cZx,hzero,map_zero]
private theorem product_coord {P Q:Flat} {m:Exps} {i:Vars} {a b:ℕ}
    (hm:m∈(P*Q).support) (hp : ∀ t∈P.support,t i≤a)
    (hq : ∀ t∈Q.support,t i≤b) :m i≤a+b :=
  (MvPolynomial.le_degreeOf_of_mem_support _ hm).trans
    ((MvPolynomial.degreeOf_mul_le _ _ _).trans
      (Nat.add_le_add (MvPolynomial.degreeOf_le_iff.mpr hp) (MvPolynomial.degreeOf_le_iff.mpr hq)))
private theorem top_count: (∑ j:Fin 15,(j:ℕ)*degree)=105*degree := by
  rw [← sum_mul,Fin.sum_univ_eq_sum_range (fun j:ℕ=>j)]
  have h: (∑ i∈range 15,i)*2=105*2 :=sum_range_id_mul_two 15
  rw [Nat.eq_of_mul_eq_mul_right (by decide :0<2) h]
theorem emK (x :Input) (T:Finset K) (hT:T⊆x.Γ)
    (F:Raw) (hF:Sheet F) (high:threshold<weight F)
    (hroots : ∀ γ∈T,Zk x (embed F) γ) :
    ∃ g:Equation,g.natDegree≤14∧(embed F).resultant g≠0 ∧
      (∀ (j:ℕ) (i:Fin 2),(g.coeff j).degreeOf i ≤
        (if i=0 then 1001 else 2)*height F) ∧
      ∀ γ∈T,Zk x g γ:= by
  classical
  obtain ⟨hi,_,hpos,hdeg,_,_⟩:=hF
  let f :=flatten F
  let v :=height F
  let a :=1001*v
  let b:=2*v
  let I:=Idx 3 (1000*v) v (fun _=>modulus)
  let J:=Idx 15 a b (fun j=>j*degree)
  let Q:=Idx 1 a b (fun _=>degree)
  let mulF:=LinearMap.mulRight L f
  let cut: (I →₀ L) →ₗ[L] Flat :=(rem modulus).comp (mulF.comp rows)
  let pick (j:J) :Exps :=exps j.1.1 (modulus-1-j.1.2) (seedMon j.2.1 j.2.2)
  let test : (I →₀ L) →ₗ[L] (J→L) :=
    (LinearMap.pi fun j=>MvPolynomial.lcoeff L (pick j)).comp cut
  have hf0 : ¬ MvPolynomial.X amm∣f :=physical_not_dvd hi hpos
  have hinj:Function.Injective cut:= by
    apply (injective_iff_map_eq_zero cut).mpr
    intro H hz
    have hd:=rem_eq modulus (rows H*f)
    change rem modulus (rows H*f)=0 at hz
    rw [hz,zero_add] at hd
    have hh:=((MvPolynomial.X_prime (R:=L) (i:=amm))).pow_dvd_of_dvd_mul_right modulus hf0 ⟨_,hd⟩
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
      m none<15∧m amm< modulus∧m (seed 0)≤a∧m (seed 1)≤b:= by
    have hh:=rem_support hm
    have hs {t:Exps} (ht:t∈(rows H).support) :=mem_coord.mp (rows_support H ht)
    refine ⟨Nat.lt_succ_of_le (product_coord hh.1 (fun t ht=>Nat.le_of_lt_succ (hs ht).1)
      (fun t ht=>(flat_deg ht).1.trans hdeg)),hh.2,?_,?_⟩
    · have he :=product_coord hh.1 (fun t ht=>(hs ht).2.2.1) (fun t ht=>(flat_deg ht).2 0)
      change m (seed 0)≤1001*v
      rw [Nat.succ_mul 1000 v]
      exact he
    · have he :=product_coord hh.1 (fun t ht=>(hs ht).2.2.2) (fun t ht=>(flat_deg ht).2 1)
      change m (seed 1)≤2*v
      rw [two_mul]
      exact he
  have narrow (H :test.ker) :wt degree (cut H.val)< modulus := by
    have hM:0< modulus := by decide
    apply Nat.lt_of_le_pred hM
    apply wt_le
    intro m hm
    obtain ⟨hy,hx,ha,hb⟩:=stock H.val hm
    by_contra! hl
    rw [Nat.pred_eq_sub_one] at hl
    have htop:modulus-1-m amm< m none*degree := by omega
    let j:J :=
      ⟨⟨⟨m none,hy⟩,⟨modulus-1-m amm,htop⟩⟩,
        ⟨m (seed 0),Nat.lt_succ_of_le ha⟩,⟨m (seed 1),Nat.lt_succ_of_le hb⟩⟩
    have hj:pick j=m:= by
      change exps (m none) (modulus-1-(modulus-1-m amm)) _=m
      rw [show modulus-1-(modulus-1-m amm)=m amm by omega]
      exact exps_eta m
    have hz :=congrFun (LinearMap.mem_ker.mp H.property) j
    change (cut H.val).coeff (pick j)=0 at hz
    exact MvPolynomial.mem_support_iff.mp hm (hj ▸ hz)
  have hlarge :Module.finrank L (Q →₀ L)<Module.finrank L test.ker := by
    have hdim:Module.finrank L (J→L)+Module.finrank L (Q →₀ L) <
        Module.finrank L (I →₀ L) := by
      rw [Module.finrank_fintype_fun_eq_card,Module.finrank_finsupp_self,
        Module.finrank_finsupp_self]
      simp only [J,Q,I,idx_card,top_count,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,one_mul]
      convert multiplier_surplus v using 1 <;> (try dsimp [a,b]) <;> ring
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
      have he :=congrArg flatten hR
      rw [RingEquiv.apply_symm_apply,map_mul] at he
      have hf :f≠0:=(map_ne_zero_iff _ flatten.injective).mpr hi.ne_zero
      have hR0:flatten R≠0:=right_ne_zero_of_mul (he ▸ hz)
      have hwt:wt degree (flatten R)<degree := by
        have hc:=narrow H
        rw [he] at hc
        change wt degree (f*flatten R)< modulus at hc
        have hmul :wt degree (f*flatten R)=wt degree f+wt degree (flatten R) :=
          MvPolynomial.weightedTotalDegree_mul _ _ _ hf hR0
        rw [hmul] at hc
        have hhi:threshold<wt degree f :=flat_high_at high
        have hM:modulus=threshold+1+degree :=rfl
        omega
      have hmem:flatten R∈(@rows 1 a b (fun _=>degree)).range := by
        apply rows_range
        intro m hm
        have hsmall:=(wt_term degree hm).trans_lt hwt
        have hj:m none<1 := by
          by_contra! h
          have ht:=Nat.mul_le_mul_right degree h
          omega
        have hd (i:Vars) : (flatten R).degreeOf i≤(cut H.val).degreeOf i :=
          by rw [he,MvPolynomial.degreeOf_mul_eq hf hR0]; exact Nat.le_add_left _ _
        refine mem_coord.mpr ⟨hj,by omega,?_,?_⟩
        · exact (MvPolynomial.le_degreeOf_of_mem_support _ hm).trans ((hd _).trans
            (MvPolynomial.degreeOf_le_iff.mpr fun t ht=>(stock H.val ht).2.2.1))
        · exact (MvPolynomial.le_degreeOf_of_mem_support _ hm).trans ((hd _).trans
            (MvPolynomial.degreeOf_le_iff.mpr fun t ht=>(stock H.val ht).2.2.2))
      obtain ⟨A,hA⟩:=hmem
      exact ⟨A,by change rows A*f= _; rw [hA,he,mul_comm]⟩
    let out:=(cut.comp test.ker.subtype).codRestrict mulQ.range hout
    have ho:Function.Injective out:= by
      intro H H' hh
      exact Subtype.ext (hinj (congrArg Subtype.val hh))
    exact hlarge.not_ge ((LinearMap.finrank_le_finrank_of_injective ho).trans mulQ.finrank_range_le)
  obtain ⟨H,hcop⟩:=hex
  let G:=cut H.val
  obtain ⟨he,hcaps⟩:=output_bounds (G:=flatten.symm G) (n:=14) (a :=a) (b:=b)
    (by rw [RingEquiv.apply_symm_apply]
        intro m hm
        obtain ⟨hy,_,ha,hb⟩:=stock H.val hm
        exact ⟨Nat.le_of_lt_succ hy,ha,hb⟩)
  refine ⟨embed (flatten.symm G),he,nonzero_resultant hcop,fun j i => ?_,fun γ hγ => ?_⟩
  · by_cases h:i=0 <;> simpa only [a,b,h,ite_true,ite_false] using hcaps j i
  · apply bPb (by decide :0< modulus) (rem_eq modulus (rows H.val*f)) (narrow H) x (hT hγ)
    simpa only [f,RingEquiv.symm_apply_apply] using hroots γ hγ
end
end q9scLLa
