import ProximityPrize.SubmissionLower.CS
import ProximityPrize.SubmissionLower.ZFZJbJc
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.ZXrG2Fd
import ProximityPrize.SubmissionLower.ZRlaVZc
import ProximityPrize.SubmissionLower.ZJ6ikSc
import ProximityPrize.SubmissionLower.Z9XsBxd
set_option Elab.async false
open _root_ renaming Fin.sum_univ_eq_sum_range → zdx, Fin.sum_univ_succ → zCS, Finset → zJe, Finset.Ico → zUb, Finset.card_range → ztd, Finset.mul_sum → zxw, Finset.range → z4x, Finset.sum_congr → zUo, Finset.sum_le_sum → zQk, Finset.univ → zdB, Finsupp.single → zhf, Finsupp.sum_fintype → z9d, Finsupp.weight_apply → zDM, Fintype.card_fin → zgY, Fintype.sum_option → zy6, LinearIndependent → z14, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.C → znf, MvPolynomial.coeff_C_mul → z06, MvPolynomial.le_degreeOf_of_mem_support → zTo, MvPolynomial.le_weightedTotalDegree → z6P, MvPolynomial.support_eq_empty → zlK, MvPolynomial.support_zero → zCb, MvPolynomial.totalDegree → zph, MvPolynomial.weightedTotalDegree_le_of_dvd → zJD, MvPolynomial.weightedTotalDegree_piSingle → z5e, Nat.add_le_add_left → z3b, Nat.div_mul_le_self → zuB, Nat.le_div_iff_mul_le → z1g, Nat.mul_comm → z5A, Nat.mul_le_mul_left → zBI, Nat.pos_of_ne_zero → zOl, Nat.sub_le_sub_right → zIu, Polynomial → zM1, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.coeff_C → zFI, Submodule → zpI, Submodule.mem_bot → zLn, Submodule.mem_top → z8t, Submodule.span → zLD, Submodule.subset_span → zBO
section
set_option autoImplicit true
namespace P6_6_4
noncomputable section
open Polynomial K1 aR jA Rk gR ProximityPrize.Benchmark
open scoped BigOperators
open private line bdm bnl bfX ctZ from ProximityPrize.SubmissionLower.CS
set_option maxRecDepth 12000
private def Bounded (F:zM1 ao[X]) (b:ℕ) :Prop :=
  ∀ j,(F.coeff j).natDegree≤b+48758*j
private theorem afg {F G:zM1 ao[X]} {a b:ℕ}
    (hF:Bounded F a) (hG:Bounded G b) :Bounded (F*G) (a+b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum,Nat.mul_add]
  omega
private theorem aCs (f :ao[X]) {a :ℕ} (hf :f.natDegree≤a) :
    Bounded (z1z f) a := by
  intro j
  by_cases h:j=0
  · simpa [h] using hf
  · simp [zFI,h]
private theorem bmr {ι:Type*} (A:zJe ι)
    (f :ι→zM1 ao[X]) (b:ι→ℕ) (hf : ∀ i∈A,Bounded (f i) (b i)) :
    Bounded (∏ i∈A,f i) (∑ i∈A,b i) := by
  classical
  induction A using Finset.induction_on with
  | empty=>simpa using aCs (1 :ao[X]) (a :=0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact afg (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk=>hf k (Finset.mem_insert_of_mem hk))
private theorem aMs {f :zM1 ao[X]} {b:ℕ} (hf :Bounded f b) (n:ℕ) :
    Bounded (f^n) (b*n) := by
  induction n with
  | zero=>simpa using aCs (1 :ao[X]) (a :=0) (by simp)
  | succ n ih =>
    rw [pow_succ,Nat.mul_succ]
    exact afg ih hf
private theorem avr (Q:af 3) (T U:ao[X]) (t:ℕ)
    (hQ:a04 t Q) (hT:T.natDegree≤131071) (hU:U.natDegree≤179829)
    (j:ℕ) : ((line Q T U).coeff j).natDegree≤t+48758*j:= by
  let b (i:Fin 3) :ℕ:=131071 - i.val
  let F (i:Fin 3) :zM1 ao[X] :=
    z1z (jet T i)+Polynomial.C (jet U i)*z7y
  have hF (i:Fin 3) :Bounded (F i) (b i) := by
    intro k
    have ht: (jet T i).natDegree≤b i :=
      (natDegree_hasseDeriv_le T i.val).trans (zIu hT _)
    have hu: (jet U i).natDegree≤b i+48758:= by
      refine (natDegree_hasseDeriv_le U i.val).trans ((zIu hU _).trans ?_)
      have hi:=i.isLt
      change 179829 - i.val≤(131071 - i.val)+48758
      omega
    change ((F i).coeff k).natDegree≤b i+48758*k
    rw [show F i= _ from rfl,Polynomial.coeff_add,zFI,
      Polynomial.coeff_C_mul_X]
    by_cases h0:k=0
    · simpa [h0] using ht
    · by_cases h1 :k=1
      · simpa [h1] using hu
      · simp [h0,h1]
  unfold line
  rw [MvPolynomial.eval₂_eq,Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hterm :=afg (aCs (Q.coeff a) le_rfl)
    (bmr a.support (fun i=>F i^a i) (fun i=>b i*a i)
      (fun i _=>aMs (hF i) (a i))) j
  exact hterm.trans (Nat.add_le_add_right (hQ a ha) _)
private theorem brV (w:I→K) (H res T:ao[X]) (t r :ℕ) (Q:af 3)
    (hT:T.natDegree≤131071) (hQ:a04 t Q) (hcontact :bkY r w H res Q)
    (A:zJe I) (hA:A.card = 179827)
    (hhit : ∀ i∈A,(H*T+res).eval (embed (node i))=embed (w i))
    (V:ao[X]) (hV:V.natDegree≤2) (j:ℕ) (hj:t+48758*j< r*179827) :
    (line Q T (mL (fun i=>embed (node i)) A*V)).coeff j=0:= by
  classical
  let x (i:I) :ao:=embed (node i)
  let L:=mL x A
  let U:=L*V
  have hU:U.natDegree≤179829 :=
    natDegree_mul_le.trans (by rw [ZQ,hA]; omega)
  have hc (i:I) (hi:i∈A) (c:ao) :
      (z7y - C (x i))^r∣(line Q T U).eval (C c) := by
    rw [bdm]
    apply hcontact i
    have hL:L.eval (x i)=0:=arK x A i hi
    have hU0:U.eval (x i)=0:= by simp [U,hL]
    have ht: (T+c•U).eval (x i)=T.eval (x i) := by simp [eval_smul,hU0]
    change (H*(T+c•U)+res).eval (x i)= _
    rw [eval_add,eval_mul,ht,← eval_mul,← eval_add]
    exact hhit i hi
  have hx :Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  apply wT.aHG A x hx r
  · exact fun i hi=>bnl _ _ _ (hc i hi) j
  · rw [hA]
    exact (avr Q T U t hQ hT hU j).trans_lt hj
theorem ceK (w:I→K) (H res T:ao[X]) (t k :ℕ) (Q:af 3)
    (hT:T.natDegree≤131071)
    (hhits : ∃ A:zJe I,179827≤A.card ∧
      ∀ i∈A,(H*T+res).eval (embed (node i))=embed (w i))
    (hc:bkY 5000 w H res Q) (hQ:a04 t Q)
    (hcut:t+48758*k<5000*179827) :
    Qu (MvPolynomial.map qV Q) (jW T) (k+1) := by
  obtain ⟨B,hB,hhits⟩:=hhits
  obtain ⟨A,hAB,hA⟩:=Finset.exists_subset_card_eq hB
  let x (i:I) :=embed (node i)
  have ho:wU Q T (k+1) := by
    apply bfX Q T (mL x A) (S8 x A).ne_zero
    intro V hV j hj
    exact brV w H res T t 5000 Q hT hQ hc A hA
      (fun i hi=>hhits i (hAB hi)) V hV j (by omega)
  intro a
  rw [ctZ]
  intro ha
  exact ho a (MvPolynomial.support_map_subset _ _ ha)
end
end P6_6_4
end
section
set_option autoImplicit true
namespace P6_6_4
noncomputable section
open K1 aR jA Rk
open scoped Polynomial BigOperators
open private bno a8W byG from ProximityPrize.SubmissionLower.S
private theorem cuk (H :ao[X]) (i t:ℕ) (F:jK)
    (hH :H.natDegree≤2354) (hF:ahb H.natDegree t F) :
    ahb H.natDegree (t+7062*i) (Yd H i F) := by
  intro b hb
  obtain ⟨u,hu⟩:=bno F i b
  have hbefore :=hF _ (a8W hb)
  let w:mA→ℕ:= fun j=>j.elim 0 (fun k=>131071+H.natDegree - k.val)
  have hw (a :mA →₀ ℕ) :
      a.sum (fun j e=>j.elim 0 (fun k=>(131071+H.natDegree - k.val)*e)) =
        Finsupp.weight w a := by
    rw [zDM]
    congr 1
    funext j e
    cases j <;> simp [w,z5A]
  rw [hw,byG w rfl] at hbefore
  rw [hw]
  have hcoeff : ((Yd H i F).coeff b).natDegree ≤
      (H^(3*i)).natDegree+(F.coeff (zhf none i+b)).natDegree := by
    simp only [Yd,← aIY,z06,hu]
    exact Polynomial.natDegree_mul_le.trans
      (z3b (Polynomial.natDegree_mul_C_le _ _) _)
  have hp' : (H^(3*i)).natDegree≤7062*i:= by
    calc
      _≤(3*i)*H.natDegree :=Polynomial.natDegree_pow_le
      _≤(3*i)*2354 :=zBI _ hH
      _=7062*i:= by ring
  omega
private theorem go4 (w:I→K) {Γ s} (P:jF Γ s) (L:kH P)
    (hh:P.H.natDegree≤2354) (box :Shape) (t:ℕ) (F:jK)
    (hF:jA.Source w P L box t F) (i:ℕ) :
    jA.Source w P L box (t+7062*i) (Yd P.H i F) := by
  obtain ⟨hcap,hcut,hcontact,hpole⟩:=hF
  refine ⟨aA0.cEb P.H i F box hcap,?_,
    aA0.cH4 P.H i w F hcontact,
    aA0.c4E P L _ i F hpole⟩
  simpa only [Nat.add_right_comm] using cuk P.H i _ F hh hcut
open private bXJ from ProximityPrize.SubmissionLower.CS
private theorem afW {F:ko} {z :iP}
    {y :Fin 3→iP} {d:ℕ} :
    NT F z y d ↔
      ∀ a,Dl a<d→(jA.translate (ED z y) F).coeff a=0:= by
  constructor
  · intro h a ha
    by_contra hz
    exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hz))
  · intro h a ha
    by_contra! hlt
    exact (MvPolynomial.mem_support_iff.mp ha) (h a hlt)
private theorem b3s (h2 :Rk.c2)
    {w Γ s} (hw:P6_6.Messages w Γ s) (P:jF Γ s) (L:kH P)
    {box t F} (hF:jA.Source w P L box t F) {γ} (hγ:γ∈Γ)
    (k :ℕ) (hk :t+48758*k<5000*179827) :
    Qu (JX (DI (P.z γ)) (bC F))
      (jW (extend (s γ))) (k+1) := by
  let res :=Tj L.numerator L.denominator (P.z γ)
  obtain ⟨Q,hQ,hrestore⟩:=h2 w Γ s P L box t F hF γ hγ
  obtain ⟨T,hT,hST⟩:=L.quotient γ hγ
  change extend (s γ)=P.H*T+res at hST
  obtain ⟨A,hA,hhits⟩:=hw.lg γ hγ
  have hhit : ∃ B:zJe I,179827≤B.card ∧
      ∀ i∈B,(P.H*T+res).eval (embed (node i))=embed (w i) := by
    refine ⟨A,hA,fun i hi => ?_⟩
    rw [← hST,extend,Polynomial.eval_map,Polynomial.eval₂_at_apply,hhits i hi]
  have hcontact :=c6X 5000 w P.H res (P.z γ) (box.b+box.j) F Q
    P.nodes hF.2.2.1 hrestore
  have ho:=ceK w P.H res T t k Q hT hhit hcontact hQ hk
  rw [hST]
  exact dia P.H res T (P.z γ) (box.b+box.j) (k+1) F Q
    P.monic.ne_zero hrestore ho
private theorem aeT (h2 :Rk.c2)
    {w Γ s} (hw:P6_6.Messages w Γ s) (P:jF Γ s) (L:kH P)
    {box t F} (hF:jA.Source w P L box t F) {γ} (hγ:γ∈Γ)
    (hh:P.H.natDegree≤2354) {d:ℕ} (hd:t+d≤5000*179827) :
    NT (bC F) (DI (P.z γ)) (jW (extend (s γ))) d:= by
  set z :=DI (P.z γ)
  set y :=jW (extend (s γ))
  apply afW.mpr
  intro m hm
  let a :mA →₀ ℕ:=zhf none (m none)
  let b:mA →₀ ℕ:=m.some.optionElim 0
  have hab:a+b=m:= by
    ext i
    cases i <;> simp [a,b]
  have hdis : ∀ i,i∉a.support∨i∉b.support := by
    intro i
    cases i <;> simp [a,b,Finsupp.mem_support_iff]
  have hlt:t+7062*m none+48758*m.some.degree<5000*179827:= by
    change 7062*m none+48758*m.some.degree<d at hm
    omega
  have hD:=go4 w P L hh box t F hF (m none)
  have ho:=b3s h2 hw P L hD hγ m.some.degree hlt
  have hc:=bXJ ho m.some (Nat.lt_succ_self _)
  change (jA.translate y (JX z (bC (Yd P.H (m none) F)))).coeff m.some=0 at hc
  have hmap :
      jA.translate y (JX z (bC (Yd P.H (m none) F))) =
        znf (qV (P.H^(3*m none))) *
          jA.translate y (JX z (bC (aox a F))) := by
    simp [Yd,bC,a,JX,jA.translate]
  rw [hmap,z06] at hc
  have hn:qV (P.H^(3*m none))≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ao[X] iP)).mpr (pow_ne_zero _ P.monic.ne_zero)
  have hcoef :=(mul_eq_zero.mp hc).resolve_left hn
  rw [dhT,cF5,← aIY,bC,bsm,
    bh9] at hcoef
  change (KR a (jA.translate (ED z y) (bC F))).coeff b=0 at hcoef
  rw [cGi _ _ _ hdis,hab] at hcoef
  exact hcoef
private theorem b9g (F:jK) (a :mA →₀ ℕ)
    (z :iP) (y :Fin 3→iP) (d:ℕ)
    (hF:NT (bC F) z y (d+Dl a)) :
    NT (bC (aox a F)) z y d:= by
  apply afW.mpr
  intro b hb
  have hlt:Dl (a+b)<d+Dl a := by rw [aOR]; omega
  have hz :=afW.mp hF _ hlt
  rw [← aIY,bC,bsm,bh9]
  exact bXR _ _ _ hz
theorem cqc (w:I→K) (Γ:zJe K) (s :K→K[X])
    (hw:P6_6.Messages w Γ s) (P:jF Γ s) (L:kH P)
    (hh:P.H.natDegree≤2354) :
    (∀ F,Source w P L ahD ajA F → ∀ γ∈Γ,
      NT (bC F) (DI (P.z γ)) (jW (extend (s γ))) Cj) ∧
    (∀ G∈akX w P L,∀ γ∈Γ,
      NT (bC G) (DI (P.z γ)) (jW (extend (s γ))) Fw) := by
  let h2 :=bRe.proof
  constructor
  · intro F hF γ hγ
    exact aeT h2 hw P L hF.1 hγ hh (by decide)
  · intro G hG γ hγ
    let z :=DI (P.z γ)
    let y :=jW (extend (s γ))
    change NT (bC G) z y Fw
    change G∈zLD ao _ at hG
    induction hG using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨t,F,a,hF,ht,rfl⟩:=hQ
      apply b9g
      apply aeT h2 hw P L hF.1 hγ hh
      change t+Dl a≤5000*179827 - 2340282 at ht
      change t+(2340282+Dl a)≤5000*179827
      omega
    | zero =>
      exact afW.mpr (fun _ _=> by simp [bC])
    | add Q R _ _ hQ hR =>
      exact afW.mpr (fun a ha=> by
        simp only [bC,map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
        exact (congrArg₂ (· + ·)
          (afW.mp hQ a ha) (afW.mp hR a ha)).trans (add_zero 0))
    | smul c Q _ hQ =>
      apply afW.mpr
      intro a ha
      have hsmul :c•Q=znf (z1z c)*Q:= by
        rw [Algebra.smul_def]
        rfl
      rw [hsmul]
      simp only [bC,map_mul,MvPolynomial.map_C,jA.translate,MvPolynomial.eval₂Hom_C,
        z06]
      exact mul_eq_zero.mpr (Or.inr (afW.mp hQ a ha))
end
end P6_6_4
end
section
set_option autoImplicit true
namespace P6_6_4
noncomputable section
open K1 aR jA
open scoped Polynomial
open anj (afo)
open private aNv cav from ProximityPrize.SubmissionLower.CS
def c1 :Prop :=
  ∀ w Γ s (P:jF Γ s) (L:kH P),P.H.natDegree≤2354 →
    (∃ F,F≠0∧Source w P L ahD ajA F)∧ap2 w P L Ga E3 RF
def c2 :Prop :=
  ∀ w Γ s (P:jF Γ s) (L:kH P) (F:jK),
    P.H.natDegree≤2354→F≠0→Source w P L ahD ajA F →
    ap2 w P L Ga E3 RF →
    ∃ G,G∈akX w P L∧Nonempty (awY (bC F) (bC G))
set_option maxRecDepth 4000 in
theorem of_children (h1 :c1) (h2 :c2) :P6_6.c4 := by
  intro w Γ s hw P hsmall
  have hh:P.H.natDegree≤2354 :=hsmall
  obtain ⟨L⟩:=bRd.proof Γ s P
  obtain ⟨⟨F,neF,hF⟩,rank2⟩:=h1 w Γ s P L hh
  obtain ⟨vanishes1,vanishes2⟩:=cqc w Γ s hw P L hh
  obtain ⟨G,hG,⟨D⟩⟩:=h2 w Γ s P L F hh neF hF rank2
  have hOrders : ∀ γ∈Γ,aqw (bC F) (bC G)
      (DI (P.z γ)) (jW (extend (s γ))) := fun γ hγ =>
    ⟨vanishes1 F hF γ hγ,vanishes2 G hG γ hγ⟩
  obtain ⟨book,Q,hcard,hQ,htQ,hiQ,hcover⟩ :=
    b1p Γ P.z (fun γ=>extend (s γ)) P.injective D hOrders
  obtain ⟨a,b,ha,hb,hR,htR,hiR⟩ :=
    eJp D.left_ne D.right_ne D.proper D.left_caps D.right_caps
  let R:=YI (pad D.left a) (pad D.right b)
  obtain ⟨_,Q',_,suppQ,mapQ⟩:=afo Q
  obtain ⟨_,R',_,suppR,mapR⟩:=afo R
  have neQ:Q' ≠ 0:= by
    intro h
    rw [h,zCb,eq_comm,zlK] at suppQ
    exact hQ suppQ
  have neR:R' ≠ 0:= by
    intro h
    rw [h,zCb,eq_comm,zlK] at suppR
    exact hR suppR
  have totalQ:Q'.totalDegree≤P6_6.aHc:= by
    simpa only [zph,suppQ] using htQ
  have indexQ:qE Q' ≤ P6_6.aM1 := by
    simpa only [aR.qE,H9,suppQ] using hiQ
  have totalR:R'.totalDegree≤P6_6.aPr := by
    have h:R.totalDegree≤P6_6.aPr :=htR
    simpa only [zph,suppR] using h
  have indexR:qE R' ≤ P6_6.aWz := by
    have h:H9 R≤P6_6.aWz :=hiR
    simpa only [aR.qE,H9,suppR] using h
  refine ⟨book,⟨Q',R',neQ,neR,totalQ,indexQ,totalR,indexR⟩,hcard,?_⟩
  intro γ hγ hb'
  rcases hcover γ hγ hb' with he | ho
  · exact Or.inl (aNv mapQ _ he)
  · refine Or.inr (cav mapR _ ?_)
    exact cfp (pad D.left a) (pad D.right b) (DI (P.z γ)) _
      ha.le hb.le ⟨aVW a ho.1,aVW b ho.2⟩
end
end P6_6_4
end
section
set_option autoImplicit true
namespace qIkXmGe
noncomputable section
open acZ (bZx)
open P6_6_4 (E3 RF)
open private dgb from ProximityPrize.SubmissionLower.S
open scoped BigOperators
set_option maxRecDepth 1024
theorem bwH :Vx 0=0x11153840804e7:= by
  decide
theorem ec1 :48758*6820*0x11153840804e7/RF=121 := by
  decide
theorem ecY:48758*2300*0x11153840804e7/RF=41 := by
  decide
theorem eD8:7062*6820*0x11153840804e7/RF=17:= by
  decide
theorem eD4 :7062*2300*0x11153840804e7/RF=5:= by
  decide
theorem eD7:7062*40000*0x11153840804e7/RF=103:= by
  decide
private theorem eD5 :
    7062*(∑ k∈z4x 1150,Vx (1+k))=0x2c156694edc1a64726:= by
  have hsum: (∑ k∈z4x 1150,Vx (1+k)) =
      (40001*5671) * ∑ k∈z4x 1150,(1150 - k)^2 := by
    rw [zxw]
    apply zUo rfl
    intro k _
    have hk :1151-(1+k)=1150 - k := by omega
    rw [Vx,hk]
  rw [hsum]
  have hsquare : (∑ k∈z4x 1150,(1150 - k)^2)=0x1e41a9bf := by
    have h:=dgb 1150
    omega
  rw [hsquare]
theorem fW2 {e V d:ℕ} (he :0<e) (r :ℕ→ℕ)
    (hr :RF ≤ ∑ t∈z4x (E3+1),r t)
    (hcap : ∀ t≤E3,r t≤Vx 0)
    (hspend : ∀ t≤E3,r t≠0→aDA e t*d≤V) :
    d≤e*V*Vx 0/RF:= by
  by_cases hd:d=0
  · simp [hd]
  have hd' : 0<d:=zOl hd
  let q (k :ℕ) :=if k<V/d then Vx 0 else 0
  have hb:=bZx (W:=E3) (n:=V/d) he r q
    (fun t ht=> by
      by_cases hn:r t=0
      · simp [hn]
      have hle :=(z1g hd').mpr (hspend t ht hn)
      have hlt: (E3 - t)/e<V/d:= by
        unfold aDA at hle
        omega
      simpa [q,hlt] using hcap t ht)
    (fun k hk=>ite_eq_right (Nat.not_lt.mpr hk))
  have hc: (∑ k∈z4x (V/d),q k)=(V/d)*Vx 0:= by
    have hsum: (∑ k∈z4x (V/d),q k) =
        ∑ _∈z4x (V/d),Vx 0 :=
      zUo rfl fun k hk=>ite_eq_left (Finset.mem_range.mp hk)
    rw [hsum]
    simp
  rw [hc] at hb
  apply (z1g (by decide :0<RF)).mpr
  calc
    d*RF≤d*(e*(V/d*Vx 0)) :=
      zBI d (hr.trans hb)
    _=(e*Vx 0)*(V/d*d) := by ring
    _≤(e*Vx 0)*V:=zBI _ (zuB _ _)
    _=e*V*Vx 0:= by ring
theorem gCh (r :ℕ→ℕ)
    (hr :RF ≤ ∑ t∈z4x (E3+1),r t)
    (h : ∀ t≤E3,r t≤Vx (aDA 7062 t)) :False := by
  have hb:=bZx (W:=E3) (n:=1150) (by decide :0<7062)
    r (fun k=>Vx (1+k)) h (fun k hk=> by
      have hk' : 1151-(1+k)=0:= by omega
      simp [Vx,hk'])
  rw [eD5] at hb
  exact (not_le_of_gt (by decide :0x2c156694edc1a64726<RF)) (hr.trans hb)
end
end qIkXmGe
end
section
set_option autoImplicit true
namespace qIkXmGe
noncomputable section
open jA hiding Dl E3 Ga
open acZ (asW aaP bJg a88)
open P6_6_4 (Dl E3 Ga)
open scoped BigOperators
open private line b7T cYc ct4 c40 c4V from ProximityPrize.SubmissionLower.A3
private theorem dLi {moving:Bool} {A:zJe ko}
    (hA:asW moving A) {F f :ko} (hF:F≠0) (hcap:Jn Ga F)
    (hf :f∈A) (hd:f∣F) :
    ∃ i:mA,(∀ n,Dl (zhf i n)=n*amz moving) ∧
      ¬ f∣(line i f).coeff 1 := by
  classical
  cases moving with
  | false =>
    obtain ⟨j,hj⟩:=c4V (hA.Bo f hf)
    have hjet:vC f≤6820 :=
      (zJD _ hd hF).trans hcap.1
    have hdeg:f.degreeOf (some j)≤vC f :=
      MvPolynomial.degreeOf_le_weightedTotalDegree
        (fun i:mA=>i.elim 0 (fun _=>1)) (some j) Nat.one_pos f
    refine ⟨some j,?_,ct4 hj (hdeg.trans_lt (hjet.trans_lt (by decide)))⟩
    intro n
    simp [Dl,amz,mul_comm]
  | true =>
    have hs :0<gY f :=hA.seed f hf
    have hdeg:gY f≤70000:= by
      simpa only [gY,z5e] using
        (zJD (Pi.single (none :mA) 1) hd hF).trans
          (by simpa only [gY,z5e] using hcap.2.2.2)
    refine ⟨none,?_,ct4 hs (hdeg.trans_lt (by decide))⟩
    intro n
    simp [Dl,amz,mul_comm]
theorem forced_power {moving:Bool} {A:zJe ko} {F:jK} {t:ℕ}
    (hA:asW moving A) (hcap:Jn Ga F) (ht:t≤E3)
    (htest : ∀ f∈A,∀ a,t+Dl a≤E3→f∣bC (aox a F)) :
    aaP A^aDA (amz moving) t∣bC F:= by
  classical
  by_cases hF:bC F=0
  · rw [hF]
    exact dvd_zero _
  unfold aaP
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro f hf g hg hfg
    refine IsRelPrime.pow ((hA.irreducible f hf).isRelPrime_iff_not_dvd.mpr ?_)
    intro hd
    exact hA.different hf hg hfg ((hA.irreducible f hf).associated_of_dvd (hA.irreducible g hg) hd)
  · intro f hf
    have hdiv :f∣bC F:= by
      simpa [Dl,bJg] using htest f hf 0 (by simpa [Dl] using ht)
    obtain ⟨i,hi,hsep⟩:=dLi hA hF (a88 hcap) hf hdiv
    apply c40 (line i) (b7T i)
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp (hA.irreducible f hf)) hsep
    intro a ha
    rw [cYc]
    apply htest f hf
    rw [hi]
    have ha' : a≤(E3 - t)/amz moving:= by
      unfold aDA at ha
      omega
    have hm:=(Nat.mul_le_mul_right (amz moving) ha').trans
      (zuB (E3 - t) (amz moving))
    omega
end
end qIkXmGe
end
section
set_option autoImplicit true
namespace qIkXmGe
noncomputable section
open jA hiding Ga
open P6_6_4 (Ga)
open scoped BigOperators
open private c6G aei dgc dfZ from ProximityPrize.SubmissionLower.S
set_option maxHeartbeats 650000
private abbrev Exponent:=mA →₀ ℕ
private def bwF (a :ℕ) :zJe (ℕ×ℕ×ℕ×ℕ) :=
  (zUb a 1151).biUnion (fun k =>
    (z4x (2301 - 2*k)).biUnion (fun j =>
      (z4x (6821 - k - j)).biUnion (fun i =>
        (z4x 40001).image (fun z=>(k,j,i,z)))))
private theorem cun (a :ℕ) : (bwF a).card≤Vx a := by
  unfold bwF
  calc
    _ ≤ ∑ k∈zUb a 1151,∑ j∈z4x (2301 - 2*k),
        ∑ _∈z4x (6821 - k - j),40001 := by
      refine Finset.card_biUnion_le.trans (zQk fun k _ => ?_)
      refine Finset.card_biUnion_le.trans (zQk fun j _ => ?_)
      refine Finset.card_biUnion_le.trans (zQk fun i _ => ?_)
      exact Finset.card_image_le.trans_eq (ztd _)
    _=Vx a := by
      unfold Vx
      simp only [Finset.sum_const,ztd,Nat.nsmul_eq_mul]
      calc
        _ = ∑ k∈zUb a 1151,(40001*5671)*(2301 - 2*k) := by
          refine zUo rfl fun k hk => ?_
          have hk' : k≤1150:= by have h:=(Finset.mem_Ico.mp hk).2; omega
          rw [← Finset.sum_mul,dgc hk']
          ring
        _ = _:= by rw [← zxw,dfZ]
private theorem b2w {a :ℕ} {R:ko} (hR:am0 R)
    {m:Exponent} (hm:m∈R.support) (ha :a≤ m (some 2)) :
    m∈(bwF a).image aei:= by
  classical
  obtain ⟨⟨hb,hj,hk,_⟩,hz⟩:=hR
  have htotalWeight:=(z6P
    (fun i:mA=>i.elim 0 (fun _=>1)) hm).trans hb
  have hindexWeight:=(z6P
    (fun i:mA=>i.elim 0 Fin.val) hm).trans hj
  have hseed :=(zTo (none :mA) hm).trans hz
  have htop:=(zTo (some 2 :mA) hm).trans hk
  have htotal:m (some 0)+m (some 1)+m (some 2)≤6820:= by
    simpa [zDM,z9d,zy6,
      zCS,Ga,Nat.add_assoc] using htotalWeight
  have hindex :m (some 1)+2*m (some 2)≤2300:= by
    simpa [zDM,z9d,zy6,
      zCS,Ga,z5A] using hindexWeight
  change m (some 2)≤1150 at htop
  change m none≤40000 at hseed
  refine Finset.mem_image.mpr ⟨(m (some 2),m (some 1),m (some 0),m none),?_,?_⟩
  · simp only [bwF,Finset.mem_biUnion,Finset.mem_Ico,Finset.mem_range,
      Finset.mem_image]
    exact ⟨m (some 2),⟨ha,by omega⟩,m (some 1),by omega,m (some 0),by omega,
      m none,by omega,rfl⟩
  · ext i
    cases i with
    | none=>simp [aei]
    | some i=>fin_cases i <;> simp [aei]
theorem dQC (a r :ℕ) (e :Fin r→ko) (he :z14 iP e)
    (h : ∀ R∈zLD iP (Set.range e),
      am0 R∧(R≠0→a≤R.degreeOf (some 2))) :r≤Vx a := by
  have hc:=c6G ((bwF a).image aei) e he (by
    intro R hR hn
    obtain ⟨m,hm,hmax⟩:=Finset.exists_mem_eq_sup R.support
      (MvPolynomial.support_nonempty.mpr hn) (fun u=>u (some 2))
    have hdeg:=(h R hR).2 hn
    rw [MvPolynomial.degreeOf_eq_sup,hmax] at hdeg
    exact ⟨m,b2w (h R hR).1 hm hdeg,MvPolynomial.mem_support_iff.mp hm⟩)
  exact hc.trans (Finset.card_image_le.trans (cun a))
end
end qIkXmGe
end
section
set_option autoImplicit true
namespace qKVHaka
set_option backward.isDefEq.respectTransparency false
noncomputable section
section Contact
open aR jA NR Rj
open MvPolynomial
open scoped Polynomial
open private AV Bg Ky aob normalize c1y cZ1 from ProximityPrize.SubmissionLower.S
open private eGH from ProximityPrize.SubmissionLower.E2
theorem dPk (b:Bank) (x v :ao) (V:zpI ao jK)
    [zAa ao V] (hcap : ∀ F∈V,apR b F) :
    TT V (ays x v)≤40001*b.avF:= by
  let A:V →ₗ[ao] (Fin 40001→aTt b.box.b) :=LinearMap.pi fun n =>
    (origin.domRestrict (Rj.apR b.box.b)).rangeRestrict ∘ₗ
      c1y b x v V (fun F hF=>(hcap F hF).1) (Fin.castLE (by decide) n)
  have hz (F:A.ker) : (F.1 :jK)∈ays x v := by
    obtain ⟨hF,hs⟩:=hcap F.1 F.1.2
    apply cZ1 hF
    intro n
    by_cases hn:n.val<40001
    · have h:=congrFun (LinearMap.mem_ker.mp F.2) ⟨n.val,hn⟩
      have hv :=congrArg (fun z :aTt b.box.b=>z.val) h
      change origin (normalize x v (aob n.val F.1))=0 at hv
      exact hv
    · have hd: (AV (F.1 :jK)).natDegree≤40000:= by
        simpa only [AV,natDegree_optionEquivLeft,gY] using hs
      have h₀:Bg n.val F.1=0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))
      have h₁:aob n.val F.1=0:= by
        change Ky.symm (Bg n.val F.1)=0
        rw [h₀,map_zero]
      simp [h₁]
  have hle :A.ker.map V.subtype≤V ⊓ ays x v := by
    rintro _ ⟨F,hF,rfl⟩
    exact Submodule.mem_inf.mpr ⟨F.property,hz ⟨F,hF⟩⟩
  have hk :=Submodule.finrank_mono hle
  rw [Submodule.finrank_map_subtype_eq] at hk
  have hr :=Submodule.finrank_le A.range
  rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,zgY,nsmul_eq_mul] at hr
  have hnull:=LinearMap.finrank_range_add_finrank_ker (K:=ao)
    (V := ↥V) (V₂:=Fin 40001→aTt b.box.b) A
  exact (show TT V (ays x v)≤40001*zsE ao (aTt b.box.b) by
    unfold TT
    omega).trans (zBI 40001 (eGH b))
end Contact
open aR jA NR
open scoped Polynomial BigOperators
open private bCP cFT from ProximityPrize.SubmissionLower.DG
open private rank_le from ProximityPrize.SubmissionLower.Z9XsBxd
theorem c4y (b:Bank) {Γ s} (P:jF Γ s) (L:kH P)
    (V:zpI ao jK) [hV:zAa ao V]
    (hcap : ∀ F∈V,apR b F) :
    TT V (amn P L b.box (jH P.H))≤P.H.natDegree*azR b.box := by
  classical
  apply aFO.of_children cxQ.proof cxR.proof Γ s P L b.box V _ hV
  intro P' L' _ hdeg hsep
  rw [← hdeg]
  let T:zJe ao:=⟨P'.H.roots,Polynomial.nodup_roots hsep⟩
  have hcard:T.card=P'.H.natDegree :=IsAlgClosed.card_roots_eq_natDegree
  have hprod: (∏ α∈T,O8 α)=jH P'.H := by
    have he : (∏ α∈T,(z7y-Polynomial.C α))=P'.H :=
      ((IsAlgClosed.splits P'.H).eq_prod_roots_of_monic P'.monic).symm
    change _=Polynomial.mapRingHom (algebraMap ao kS) P'.H
    rw [← he,map_prod]
    simp [O8]
  let W (α:ao) :=amn P' L' b.box (O8 α)
  have hlocal (α:ao) (hα:α∈T) :TT V (W α)≤azR b.box := by
    have hr :P'.H.IsRoot α:=(Polynomial.mem_roots P'.monic.ne_zero).mp hα
    exact rank_le b.box 40000 P' L' α V hcap hr
      (hsep.eval₂_derivative_ne_zero (RingHom.id ao) hr)
  have hsub:T.inf W≤amn P' L' b.box (jH P'.H) := by
    intro F hF
    have hcop:=Polynomial.pairwise_coprime_X_sub_C
      (FaithfulSMul.algebraMap_injective ao kS)
    have h:=Finset.prod_dvd_of_coprime (t:=T)
      (s := fun α=>(znf (O8 α) :Lq)^(b.box.b+b.box.j))
      (fun α _ β _ hne=>(IsCoprime.map (f :=znf) (hcop hne)).pow)
      (fun α hα=>(aVU P' L' b.box _ _).mp
        ((Finset.inf_le hα:T.inf W≤W α) hF))
    rw [Finset.prod_pow,← map_prod znf,hprod] at h
    exact (aVU P' L' b.box _ _).mpr h
  exact (cFT V hsub).trans (hcard ▸ bCP V T W _ hlocal)
end
end qKVHaka
end
section
set_option autoImplicit true
namespace qKVHaka
open aR jA NR
open aw8 (ama)
open scoped BigOperators Polynomial
noncomputable section
open private Lh Ac auD column i7 cGZ coordinate bDn exponent_none space deR from ProximityPrize.SubmissionLower.B9
private abbrev bAe (b:Bank) (h:ℕ) :=
  Σ q:Fin (b.box.b+1),Σ k :Fin (min q.val 1150+1),
    Σ l:Fin (min (q.val - k.val) (2300 - 2*k.val)+1),
      Fin (width b h q.val k.val l.val)×Fin 40001
private def gap (b:Bank) :ℕ:=b.cut - cut b
private theorem cI4 (b:Bank) :cut b≤b.cut:= by
  cases b <;> decide
private theorem eGt (b:Bank) (h q k l:ℕ) :
    aw8.width b h q k l=width b h q k l+gap b:= by
  have hle :=cI4 b
  have hwidth :=bZs b
  unfold aw8.width aw8.aEw width aEw gap
  omega
private def cLB {b:Bank} {h:ℕ} (d:ℕ) (hd:d≤gap b) :
    bAe b h ↪ Lh b h :=
  .sigmaMap (.refl _) fun q => .sigmaMap (.refl _) fun k => .sigmaMap (.refl _) fun l =>
    .prodMap ((Fin.addNatEmb d).trans (Fin.castLEEmb (by
      change width b h q.val k.val l.val+d≤aw8.width b h q.val k.val l.val
      rw [eGt]
      exact z3b hd _)))
      (Fin.castLEEmb (by decide))
private abbrev a8F (b:Bank) (h:ℕ) :bAe b h ↪ Lh b h :=
  cLB 0 (Nat.zero_le _)
private def bhr (b:Bank) (h:ℕ) :zpI ao jK :=
  zLD ao (Set.range (column ∘ a8F b h))
private theorem occurs {b:Bank} {h:ℕ} {F:jK}
    (hF:F∈bhr b h) {e :mA →₀ ℕ} {x :ℕ} (hne : (F.coeff e).coeff x≠0) :
    ∃ c:bAe b h,Ac (a8F b h c)=e∧auD (a8F b h c)=x := by
  classical
  by_contra! hn
  have hle :bhr b h≤LinearMap.ker (coordinate e x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    change coordinate e x (column (a8F b h c))=0
    rw [bDn,ite_eq_right]
    exact fun hc=>(hn c hc.1 hc.2).elim
  exact hne (LinearMap.mem_ker.mp (hle hF))
private theorem Ca (b:Bank) (h:ℕ) (F:jK) (hF:F∈bhr b h) :
    apR b F∧ahb h (cut b+(b.box.b+b.box.j)*h) F:= by
  have hsub:bhr b h≤ space b h:= by
    apply Submodule.span_mono
    rintro _ ⟨c,rfl⟩
    exact ⟨a8F b h c,rfl⟩
  have hs (e :mA →₀ ℕ) (hm:e∈F.support) :=
    occurs hF (e :=e) (x :=(F.coeff e).natDegree) (by
      rw [Polynomial.coeff_natDegree,Polynomial.leadingCoeff_ne_zero]
      exact MvPolynomial.mem_support_iff.mp hm)
  refine ⟨⟨(deR b h F (hsub hF)).1,MvPolynomial.degreeOf_le_iff.mpr ?_⟩,?_⟩
  · intro e hm
    obtain ⟨c,rfl,_⟩:=hs e hm
    rw [Ac,exponent_none]
    exact Nat.le_of_lt_succ c.2.2.2.2.isLt
  · intro e hm
    obtain ⟨c,he,hx⟩:=hs e hm
    let d:=cLB (gap b) le_rfl c
    have hd:=(i7 d).2.2.2.2
    have he' : Ac d=e :=he
    have hx' : auD d=auD (a8F b h c)+gap b:= by
      rcases c with ⟨q,k,l,x,u⟩
      change x.val+gap b=x.val+0+gap b
      exact congrArg (fun n:ℕ=>n+gap b) (Nat.add_zero x.val).symm
    rw [he',hx',hx] at hd
    have hle :=cI4 b
    unfold gap at hd
    omega
theorem Aw (b:Bank) (h:ℕ) :
    ∃ V:zpI ao jK,zAa ao V ∧
      (∀ F∈V,apR b F∧ahb h (cut b+(b.box.b+b.box.j)*h) F) ∧
      zsE ao V=40001*ama b.box.b (width b h) := by
  refine ⟨bhr b h,Module.Finite.span_of_finite _ (Set.finite_range _),Ca b h,?_⟩
  rw [bhr,finrank_span_eq_card ((cGZ b h).comp _ (a8F b h).injective)]
  simp only [bAe,Fintype.card_sigma,Fintype.card_prod,zgY,
    z5A _ 40001]
  unfold ama
  simp only [zxw]
  rw [← zdx]
  refine zUo rfl fun q _ => ?_
  rw [← zdx]
  refine zUo rfl fun k _ => ?_
  rw [← zdx]
end
end qKVHaka
end
section
set_option autoImplicit true
namespace qKVHaka
noncomputable section
open K1 aR jA
open NR (Bank TT ays amn bsz aVU)
open scoped Polynomial
open private bXt bCP cKM from ProximityPrize.SubmissionLower.DG
private theorem c6J (b:Bank) (w:I→K) {Γ s}
    (P:jF Γ s) (L:kH P) (hh:P.H.natDegree≤2354) :
    P6_6_4.ap2 w P L b.box (cut b) (aAv b) := by
  classical
  obtain ⟨V,hV,hbox,hdimV⟩:=Aw b P.H.natDegree
  have hsize :=(budget b P.H.natDegree hh).trans_eq hdimV.symm
  let:zAa ao V:=hV
  have hcap : ∀ F∈V,apR b F:= fun F hF=>(hbox F hF).1
  let A:I→zpI ao jK:= fun i=>ays (embed (node i)) (embed (w i))
  let U:zpI ao jK := ⨅ i,A i
  let W:zpI ao jK:=amn P L b.box (jH P.H)
  have hU:TT V U≤262144*(40001*b.avF) := by
    have hA (i:I) (_:i∈zdB) :TT V (A i)≤40001*b.avF :=
      dPk b (embed (node i)) (embed (w i)) V hcap
    have h:=bCP V (zdB :zJe I) A (40001*b.avF) hA
    have hc: (zdB :zJe I).card = 262144 :=zgY (2^18)
    rw [hc,Finset.inf_univ_eq_iInf] at h
    exact h
  have hW:TT V W≤P.H.natDegree*azR b.box :=
    c4y b P L V hcap
  have hdebit :=(bXt V U W).trans (Nat.add_le_add hU hW)
  let S:zpI ao jK:=V ⊓ (U ⊓ W)
  have hdim:aAv b≤zsE ao S:=cKM hsize hdebit
  obtain ⟨f,hf⟩:=exists_linearIndependent_of_le_finrank (R:=ao) (M := ↥S) hdim
  let e :Fin (aAv b)→jK:= fun i=>(f i).val
  refine ⟨e,hf.map_injOn S.subtype Subtype.val_injective.injOn,?_⟩
  intro i
  have hm:=Submodule.mem_inf.mp (f i).property
  have hUW:e i∈U ⊓ W:=hm.2
  have hb:=hbox (e i) hm.1
  refine ⟨⟨hb.1.1,hb.2,?_,(aVU P L b.box _ _).mp (Submodule.mem_inf.mp hUW).2⟩,
    hb.1.2⟩
  intro j
  have hmem:e i∈A j:=(Submodule.mem_iInf A).mp (Submodule.mem_inf.mp hUW).1 j
  exact (bsz (embed (node j)) (embed (w j)) (e i)).mp hmem
theorem proof :P6_6_4.c1 := by
  intro w Γ s P L hh
  refine ⟨?_,c6J .second w P L hh⟩
  obtain ⟨e,he,hsource⟩:=c6J .first w P L hh
  let i:Fin (aAv Bank.first) :=⟨0,by decide⟩
  exact ⟨e i,he.ne_zero i,hsource i⟩
end
end qKVHaka
end
section
set_option autoImplicit true
namespace qIkXmGe
noncomputable section
open K1 aR
open jA hiding ahD Ga E3 Dl awY ap2 Source
open acZ (asW aaP Bu bJg agr
  c0r bfD a88)
open P6_6_4 (akX Dl E3 RF ahD Ga ap2 Source awY)
open scoped BigOperators
open private multiples mem_multiples aJZ from ProximityPrize.SubmissionLower.S
set_option maxRecDepth 1024
def c1 :Prop :=
  ∀ w Γ s (P:jF Γ s) (L:kH P),
    ap2 w P L Ga E3 RF →
    ∃ r :ℕ→ℕ,RF ≤ ∑ t∈z4x (E3+1),r t ∧
      ∀ t≤E3,∃ e :Fin (r t)→ko,
        z14 iP e ∧ ∀ i,e i∈avl w P L t
def c2 :Prop :=
  ∀ F G:ko,F≠0→G≠0 →
    Jn ahD F→ gY F≤40000→am0 G →
    (∀ A,asW false A→(∀ f∈A,f∣F∧f∣G) →
      vC (aaP A)≤121∧lP (aaP A)≤41) →
    (∀ A,asW true A→(∀ f∈A,f∣F∧f∣G) →
      vC (aaP A)≤17∧lP (aaP A)≤5 ∧
      gY (aaP A)≤103 ∧ ∀ f∈A,f.degreeOf (some 2)=0) →
    Nonempty (awY F G)
private theorem cIu {Γ s} {w:I→K} {P:jF Γ s}
    {L:kH P} {a r t:ℕ}
    (hb : ∃ e :Fin r→ko,z14 iP e ∧
      ∀ i,e i∈avl w P L t)
    (hdeg : ∀ R∈avl w P L t,R≠0→a≤R.degreeOf (some 2)) :
    r≤Vx a := by
  obtain ⟨e,he,hs⟩:=hb
  have hspan:zLD iP (Set.range e)≤avl w P L t :=
    Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hs i)
  exact dQC a r e he (fun R hR=>⟨b7k (hspan hR),hdeg R (hspan hR)⟩)
private theorem emg {Γ s} {w:I→K} {P:jF Γ s}
    {L:kH P} (hr :ap2 w P L Ga E3 RF) :
    ∃ G:akX w P L,G≠0:= by
  obtain ⟨e,he,hs⟩:=hr
  let i:Fin RF:=⟨0,by decide⟩
  have hmem:e i∈akX w P L:= by
    apply zBO
    exact ⟨E3,e i,0,hs i,by simp [Dl],(bJg _).symm⟩
  refine ⟨⟨e i,hmem⟩,fun h=>he.ne_zero i ?_⟩
  exact congrArg (fun Q:akX w P L=>Q.val) h
private theorem eEy {Γ s} {w:I→K} {P:jF Γ s}
    {L:kH P} {Q:jK} (hQ:Q∈akX w P L) :
    am0 (bC Q) := by
  classical
  have hle :akX w P L≤(bBt.restrictScalars ao).comap Bu:= by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,F,a,hF,_,rfl⟩
    have hseed :=bfD (Pi.single (none :mA) 1) a F
    simp only [z5e] at hseed
    exact bsu.mpr (ctu (c0r a F hF.1.1)
      (hseed.trans hF.2))
  exact bsu.mp (hle hQ)
private theorem gpj {Γ s} {w:I→K} {P:jF Γ s} {L:kH P}
    {F:jK} (hF:F≠0) (hr :ap2 w P L Ga E3 RF) :
    ∃ G,G∈akX w P L∧G≠0 ∧
      ∀ f :ko,Irreducible f→f∣bC F→f∣bC G →
        ∀ Q∈akX w P L,f∣bC Q:= by
  classical
  let N :=akX w P L
  let _:StrongNormalizationMonoid ko :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let bad:=(UniqueFactorizationMonoid.normalizedFactors (bC F)).toFinset.filter
    (fun f => ∃ Q∈N,¬ f∣bC Q)
  let sub:Option ↥bad→zpI ao N
    | none => ⊥
    | some f=>((multiples f.val).restrictScalars ao).comap (Bu.comp N.subtype)
  have hproper (i:Option ↥bad) :sub i ≠ ⊤ := by
    cases i with
    | none =>
      obtain ⟨Q,hQ⟩:=emg hr
      intro h
      have hm:Q∈sub none :=h ▸ z8t
      exact hQ ((zLn ao).mp hm)
    | some f =>
      obtain ⟨Q,hQ,hnd⟩:=(Finset.mem_filter.mp f.property).2
      intro h
      have hm: (⟨Q,hQ⟩:N)∈sub (some f) :=h ▸ z8t
      exact hnd (mem_multiples.mp hm)
  obtain ⟨G,hG⟩:=Submodule.exists_forall_notMem_of_forall_ne_top
    (ι:=Option ↥bad) (K:=ao) (M:=N) sub hproper
  refine ⟨G.val,G.property,?_,fun f hf hdf hdg Q hQ => ?_⟩
  · intro h
    exact hG none ((zLn ao).mpr (Subtype.ext h))
  · by_contra hn
    obtain ⟨p,hp,hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd (agr hF) hf hdf
    have hp' : p∈bad:=Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hp,Q,hQ,fun h=>hn (hassoc.dvd_iff_dvd_left.mpr h)⟩
    exact hG (some ⟨p,hp'⟩) (mem_multiples.mpr (hassoc.dvd_iff_dvd_left.mp hdg))
private theorem euS {Γ s} {w:I→K} {P:jF Γ s}
    {L:kH P} {moving:Bool} {A:zJe ko} (hA:asW moving A)
    (hcommon : ∀ f∈A,∀ Q∈akX w P L,f∣bC Q)
    {t:ℕ} (ht:t≤E3) :
    avl w P L t≤ multiples (aaP A^aDA (amz moving) t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨F,hF,rfl⟩
  apply mem_multiples.mpr (forced_power hA hF.1.1 ht ?_)
  intro f hf a ha
  exact hcommon f hf _ (zBO ⟨t,F,a,hF,ha,rfl⟩)
private theorem ccP {moving:Bool} {A:zJe ko} (hA:asW moving A) :
    aaP A≠0 :=
  Finset.prod_ne_zero_iff.mpr fun f hf=>(hA.irreducible f hf).ne_zero
private theorem gMn {Γ s} {w:I→K} {P:jF Γ s} {L:kH P}
    {e :ℕ} (he :0<e) {r :ℕ→ℕ} {D:ko} (hD:D ≠0)
    (hr :RF ≤ ∑ t∈z4x (E3+1),r t)
    (hb : ∀ t≤E3,∃ u:Fin (r t)→ko,z14 iP u ∧
      ∀ i,u i∈avl w P L t)
    (hcount : ∀ t≤E3,r t≤Vx 0)
    (hdvd : ∀ t≤E3,avl w P L t≤ multiples (D^aDA e t))
    (v :mA→ℕ) (V:ℕ)
    (hcap : ∀ R:ko,am0 R→R.weightedTotalDegree v≤V) :
    D.weightedTotalDegree v≤e*V*Vx 0/RF:= by
  apply fW2 he r hr hcount
  intro t ht hne
  obtain ⟨u,hu,hs⟩:=hb t ht
  let i:Fin (r t) :=⟨0,zOl hne⟩
  have hm:=zJD v
    (mem_multiples.mp (hdvd t ht (hs i))) (hu.ne_zero i)
  rw [aJZ _ _ hD] at hm
  exact hm.trans (hcap (u i) (b7k (hs i)))
private theorem d3V {Γ s} {w:I→K} {P:jF Γ s}
    {L:kH P} {r :ℕ→ℕ} {A:zJe ko} (hA:asW true A)
    (hr :RF ≤ ∑ t∈z4x (E3+1),r t)
    (hb : ∀ t≤E3,∃ u:Fin (r t)→ko,
      z14 iP u ∧ ∀ i,u i∈avl w P L t)
    (hdvd : ∀ t≤E3,
      avl w P L t≤ multiples (aaP A^aDA 7062 t)) :
    ∀ f∈A,f.degreeOf (some 2)=0:= by
  classical
  let v :mA→ℕ:=Pi.single (some 2) 1
  have hzero : (aaP A).weightedTotalDegree v=0:= by
    by_contra hn
    apply gCh r hr
    intro t ht
    apply cIu (hb t ht)
    intro R hR hRne
    have h:=zJD v
      (mem_multiples.mp (hdvd t ht hR)) hRne
    rw [aJZ _ _ (ccP hA)] at h
    have hle :=zBI (aDA 7062 t) (zOl hn)
    rw [Nat.mul_one] at hle
    simpa only [v,z5e] using hle.trans h
  intro f hf
  have hfd:f∣aaP A:=Finset.dvd_prod_of_mem id hf
  have h:=(zJD v hfd (ccP hA)).trans_eq hzero
  simpa only [v,z5e,Nat.le_zero] using h
theorem of_children (telescope :c1) (hgcd:c2) :P6_6_4.c2 := by
  classical
  intro w Γ s P L F _ hF hFCaps hRank
  obtain ⟨r,hr,hb⟩:=telescope w Γ s P L hRank
  have hcount : ∀ t≤E3,r t≤Vx 0:= fun t ht =>
    cIu (hb t ht) (fun _ _ _=>Nat.zero_le _)
  obtain ⟨G,hG,hGne,hchoose⟩:=gpj hF hRank
  have hdiv (moving:Bool) (A:zJe ko) (hA:asW moving A)
      (hcomm : ∀ f∈A,f∣bC F∧f∣bC G) :
      ∀ t≤E3,avl w P L t ≤
        multiples (aaP A^aDA (amz moving) t) :=
    fun _ ht=>euS hA
      (fun f hf=>hchoose f (hA.irreducible f hf) (hcomm f hf).1 (hcomm f hf).2) ht
  have hbound (moving:Bool) (A:zJe ko) (hA:asW moving A)
      (hcomm : ∀ f∈A,f∣bC F∧f∣bC G)
      (v :mA→ℕ) (V:ℕ)
      (hc : ∀ R:ko,am0 R→R.weightedTotalDegree v≤V) :
      (aaP A).weightedTotalDegree v≤amz moving*V*Vx 0/RF :=
    gMn (by cases moving <;> decide) (ccP hA) hr hb hcount
      (hdiv moving A hA hcomm) v V hc
  have hbcap (R:ko) (h:am0 R) :vC R≤6820:=h.1.1
  have hjcap (R:ko) (h:am0 R) :lP R≤2300:=h.1.2.1
  have hscap (R:ko) (h:am0 R) :
      R.weightedTotalDegree (Pi.single (none :mA) 1)≤40000:= by
    rw [z5e]
    exact h.2
  refine ⟨G,hG,hgcd _ _ (agr hF) (agr hGne)
    (a88 hFCaps.1.1) ((bAl.bxL F).trans_le hFCaps.2)
    (eEy hG) ?_ ?_⟩
  · intro A hA hcomm
    have hbt:=hbound false A hA hcomm _ _ hbcap
    have hji:=hbound false A hA hcomm _ _ hjcap
    change vC _≤_ at hbt
    change lP _≤_ at hji
    have hbt' : vC (aaP A)≤121 := by
      simpa only [amz,Bool.false_eq_true,ite_false,bwH,ec1] using hbt
    have hji' : lP (aaP A)≤41 := by
      simpa only [amz,Bool.false_eq_true,ite_false,bwH,ecY] using hji
    exact ⟨hbt',hji'⟩
  · intro A hA hcomm
    have hbt:=hbound true A hA hcomm _ _ hbcap
    have hji:=hbound true A hA hcomm _ _ hjcap
    have hse :=hbound true A hA hcomm _ _ hscap
    change vC _≤_ at hbt
    change lP _≤_ at hji
    rw [z5e] at hse
    have hbt' : vC (aaP A)≤17:= by
      simpa only [amz,ite_true,bwH,eD8] using hbt
    have hji' : lP (aaP A)≤5:= by
      simpa only [amz,ite_true,bwH,eD4] using hji
    have hse' : gY (aaP A)≤103:= by
      simpa only [gY,amz,ite_true,bwH,eD7] using hse
    exact ⟨hbt',hji',hse',d3V hA hr hb (hdiv true A hA hcomm)⟩
end
end qIkXmGe
end
