import ProximityPrize.SubmissionLower.ZQWBuGc
import ProximityPrize.SubmissionLower.ZG8ydqc
import ProximityPrize.SubmissionLower.ZIBb1mb
import ProximityPrize.SubmissionLower.ZY18Mqc
import ProximityPrize.SubmissionLower.Zsr715c
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
namespace q7twcKc
noncomputable section
open aR dN MvPolynomial P6_6 P6_6_7
open qAzl5me (Selected MemberCurve chartRow memberTest)
open rW (n8)
open lB (bF Tn)
open bat (raw step)
open private c7g ZF aTO ajn from ProximityPrize.SubmissionLower.L
open private br5 ew1 from ProximityPrize.SubmissionLower.ZG8ydqc
open private aDr from ProximityPrize.SubmissionLower.ZQWBuGc
private def thin (g:af 4) :ℕ→af 4
  | 0=>6*MvPolynomial.X 3
  | n+1=>step true g n (thin g n)
private theorem flow_const (g:af 4) (a :ℕ) :u6 g (a :af 4)=0:= by
  rw [← map_natCast (MvPolynomial.C:Polynomial ao →+* af 4)]
  unfold u6 pK separant
  simp only [aTO,MvPolynomial.pderiv_C,Polynomial.derivative_natCast,
    map_zero,mul_zero,Finset.sum_const_zero,add_zero,sub_zero]
private theorem b3I (g:af 4) (i:Fin 3) :
    u6 g (MvPolynomial.X i.castSucc) =
      separant g*((i.val+1 :ℕ) :af 4)*MvPolynomial.X i.succ:= by
  have hcoeff (j:Fin 4) :lX (MvPolynomial.X j:af 4)=0:= by
    ext m
    rw [ajn,MvPolynomial.coeff_X]
    split_ifs <;> simp
  fin_cases i <;>
    simp [u6,pK,separant,hcoeff,Fin.sum_univ_three,
      MvPolynomial.pderiv_X,Pi.single_apply,mul_assoc] <;> norm_num
private theorem raw_shift (g:af 4) (h:separant (separant g)=0) (n:ℕ) :
    raw true g (n+3)=separant g^3*thin g n:= by
  let S:=separant g
  have hS:u6 g S=S*pK S:= by
    simp [S,u6,h]
  have hpow (e :ℕ) :u6 g (S^e)=(e :af 4)*S^e*pK S:= by
    induction e with
    | zero=>simpa using flow_const g 1
    | succ e ih =>
      rw [pow_succ,ZF,ih,hS,Nat.cast_succ]
      ring
  have hsc (n e :ℕ) (P:af 4) :
      step true g (n+e) (S^e*P)=S^e*step true g n P:= by
    unfold step
    simp only [↓reduceIte,ZF,hpow,Nat.cast_add]
    ring
  have hi (i:Fin 3) (n a :ℕ) :
      step true g n (S^n*((a :af 4)*MvPolynomial.X i.castSucc)) =
        S^(n+1)*(((a*(i.val+1) :ℕ) :af 4)*MvPolynomial.X i.succ) := by
    change u6 g (S^n*((a :af 4)*MvPolynomial.X i.castSucc)) -
      (n:af 4)*pK S*(S^n*((a :af 4)*MvPolynomial.X i.castSucc))= _
    rw [ZF,hpow,ZF,flow_const,b3I,pow_succ,Nat.cast_mul]
    ring
  have h1 :raw true g 1=S^1*((1 :af 4)*MvPolynomial.X 1) := by
    have hv :=hi 0 0 1
    simp only [pow_zero,Nat.cast_one,one_mul] at hv
    exact hv
  have h2 :raw true g 2=S^2*((2 :af 4)*MvPolynomial.X 2) := by
    change step true g 1 (raw true g 1)= _
    rw [h1]
    exact hi 1 1 1
  induction n with
  | zero =>
    change step true g 2 (raw true g 2)=S^3*thin g 0
    rw [h2]
    exact hi 2 2 2
  | succ n ih =>
    rw [show n+1+3=(n+3)+1 by omega,raw,ih]
    simp only [bat.Fy,↓reduceIte,one_mul,thin]
    exact hsc n 3 (thin g n)
private theorem thin_degree {g:af 4} {p:Shape} (hg:aO (shape g) p)
    (hb:1≤p.b) (m:ℕ) :
    (bC (thin g m)).totalDegree≤1+m*(p.b - 1) := by
  rw [WI.ctQ,← weightedTotalDegree_one]
  have hg' : weightedTotalDegree (1 :Fin 4→ℕ) g≤p.b:= by
    simpa only [shape,weightedTotalDegree_one] using hg.1
  induction m with
  | zero =>
    rw [thin,weightedTotalDegree_one,
      show (6:af 4)=MvPolynomial.C (6:Polynomial ao) from
        (map_natCast (MvPolynomial.C:Polynomial ao →+* af 4) 6).symm]
    exact (totalDegree_mul _ _).trans (by simp)
  | succ m ih =>
    have h:=ew1 1 0 (fun _=> by simp) hb hg' ih m
    simpa only [thin,step,↓reduceIte,add_zero,Nat.succ_mul,Pi.one_apply,
      br5,Nat.add_assoc] using h
theorem member_equation {C:Context} {R G ell cs} (h:PairInput C R G ell cs)
    {Sfc:n8} {γ:P6.K} {i:Fin C.n} {a :ℕ} (hs :Selected C cs Sfc γ i a) :
    ∃ E :af 4,(bC E).totalDegree≤(weightedChart (P6_6.bf+1) (chartBody C R cs)).b ∧
      (∃ e :ℕ,memberTest (chartRow C i a)=separant (chartRow C i a)^e*E) := by
  let p:=chartBody C R cs
  let g:=chartRow C i a
  have hf :=(P6_6_7_3.bW2 h).2 i hs.index_mem
  have hg:aO (shape g) p :=
    ⟨(by simpa only [g,chartRow,shape,weightedTotalDegree_one] using aDr 1 (C.f i) a :
      (shape g).b≤(shape (C.f i)).b).trans hf.1,
    (by simpa only [g,chartRow,shape,Ex.C6] using aDr Fin.val (C.f i) a :
      (shape g).j≤(shape (C.f i)).j).trans hf.2.1,
    (by simpa only [g,chartRow,shape,weightedTotalDegree_piSingle] using
      aDr (Pi.single 3 1) (C.f i) a : (shape g).t≤(shape (C.f i)).t).trans hf.2.2⟩
  have hp:bF p:= by
    cases cs with
    | union _ =>
      exact (P6_6_8_3.remaining_fits C.v).2
    | own _=>exact Tn R
  have ht:0<p.t:=(Nat.zero_lt_of_lt hs.canonical.1).trans_le hf.2.2
  by_cases ht1 :p.t=1
  · have htop: (shape (C.f i)).t≤p.t:=hf.2.2
    rw [ht1] at htop
    have ha0:=hs.canonical.1
    have ha :a=0:= by omega
    have he : (shape (C.f i)).t=1 := by omega
    have hgt: (shape g).t=1 := by simpa only [g,chartRow,ha,Function.iterate_zero_apply] using he
    have hb:1≤p.b:= by have :=hp.1; have :=hp.2; omega
    refine ⟨thin g (P6_6.bf-3),?_,P6_6.bf+3,?_⟩
    · rw [weightedChart,ite_eq_left ht1]
      exact (thin_degree hg hb _).trans (le_max_left _ _)
    · change su g P6_6.bf= _
      have he :P6_6.bf-3+3=P6_6.bf := by decide
      have hlin:=bat.exb hgt
      have hr :=raw_shift g hlin (P6_6.bf-3)
      rw [he] at hr
      rw [c7g g hlin,hr,← mul_assoc,← pow_add]
  · refine ⟨memberTest g,?_,0,by rw [pow_zero,one_mul]⟩
    rw [weightedChart,ite_eq_right ht1]
    exact (aY3.bH1 hg hp ht (Nat.le_succ P6_6.bf)).1
theorem b85 {g E :af 4} {Sfc P:n8} (hm:MemberCurve g Sfc P)
    (hP:bC (separant g)∉P)
    (he : ∃ e :ℕ,memberTest g=separant g^e*E) :
    bC E∉Sfc∧(AX Sfc E).IsMinimalPrime P:= by
  obtain ⟨e,he⟩:=he
  have hmul :bC (memberTest g)=(bC (separant g))^e*bC E := by
    rw [he,bC,map_mul,map_pow]
    rfl
  have hspan:AX Sfc (memberTest g)≤AX Sfc E :=
    sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (by
      rw [hmul]
      exact (AX Sfc E).mul_mem_left _
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (bC E)))))
  have hp:=hm.minimal
  refine ⟨fun h=>hm.proper (by rw [hmul]; exact Sfc.mul_mem_left _ h),⟨⟨hp.isPrime,?_⟩,?_⟩⟩
  · apply sup_le (le_sup_left.trans hp.le)
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    have hraw:=hp.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (bC (memberTest g))))
    rw [hmul] at hraw
    exact (hp.isPrime.mem_or_mem hraw).resolve_left (fun hp' => hP (hp.isPrime.mem_of_pow_mem e hp'))
  · exact fun Q hQ hQP=>hp.2 ⟨hQ.1,hspan.trans hQ.2⟩ hQP
end
end q7twcKc
