import ProximityPrize.SubmissionLower.ZTFKldb
set_option Elab.async false
open _root_ renaming Fin.sum_univ_succ → zCS, Finset.Ico → zUb, Finset.card_range → ztd, Finset.range → z4x, Finset.sum_filter → zLJ, Finset.sum_le_sum → zQk, Finsupp.sum_fintype → z9d, Finsupp.weight_apply → zDM, Fintype.sum_option → zy6, IsFractionRing.injective → zxb, MvPolynomial.degreeOf_rename_of_injective → zTg, MvPolynomial.eval → zY9, MvPolynomial.eval₂_comp → z6r, MvPolynomial.le_degreeOf_of_mem_support → zTo, MvPolynomial.le_weightedTotalDegree → z6P, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.mapRingHom → zhd, Submodule → zpI, Submodule.mem_bot → zLn, Submodule.mem_top → z8t
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qlc9qed
noncomputable section
open Polynomial
open P5 (K p twist)
open P5_7_1 (TopRow atTop topConjugate topLift)
open aR (ao embed)
open jA Rk
open acZ (Bu agr)
open UniqueFactorizationMonoid


private def values (z :K) (S:K[X]) :Fin 4→ao[X] :=
 ![C (embed z),cu.j9 S,cu.j9 S.derivative,
   cu.j9 (hasseDeriv 2 S)]
theorem duQ (F:TopRow) (z :K) (S:K[X]) :
  atTop F z S=qV (zY9 (values z S) F) := by
 rw [z6r]
 unfold atTop
 congr 1
 funext j
 fin_cases j <;> rfl
theorem cHJ (F:TopRow) (z :K) (S:K[X])
   (hS:S.map twist=S) (hz :atTop F z S=0) :
   atTop (topConjugate F) (twist z) S=0:= by
 let σ:=zhd (frobenius ao p)
 have hf (T:K[X]) (hT:T.map twist=T) :
     σ (cu.j9 T)=cu.j9 T :=
   (cu.dio T).symm.trans (congrArg cu.j9 hT)
 have hD:S.derivative.map twist=S.derivative :=
   (Polynomial.derivative_map S twist).symm.trans (congrArg derivative hS)
 have hH : (hasseDeriv 2 S).map twist=hasseDeriv 2 S :=
   (Polynomial.hasseDeriv_map twist 2 S).symm.trans (congrArg (hasseDeriv 2) hS)
 have hv :σ ∘ values z S=values (twist z) S:= by
   funext j
   fin_cases j
   · change (C (embed z)).map (frobenius ao p)=C (embed (twist z))
     rw [Polynomial.map_C]
     exact congrArg C (((algebraMap K ao).map_frobenius p z).symm)
   · exact hf S hS
   · exact hf S.derivative hD
   · exact hf (hasseDeriv 2 S) hH
 have hs :zY9 (values z S) F=0 :=
   (zxb ao[X] iP) (by simpa only [duQ,map_zero] using hz)
 rw [duQ,topConjugate,MvPolynomial.eval_map,← hv,← z6r,
   hs,map_zero,map_zero]
theorem toTop_injective :Function.Injective toTop :=
 MvPolynomial.rename_injective _ aD.injective
private def bEl (V:zpI ao jK) (G:ko) :zpI ao V :=
 (((Ideal.span {G}).restrictScalars iP).restrictScalars ao).comap
   (Bu.comp V.subtype)
private theorem mem_divisible (V:zpI ao jK) (G:ko) (F:V) :
  F∈bEl V G↔G∣bC F.val :=
 Ideal.mem_span_singleton
theorem choose_strong (F:jK) (hF:F≠0) (V:zpI ao jK)
    (hn : ∃ W∈V,W≠0)
    (hproper : ∀ G:ko,Irreducible G→G∣bC F →
      0<G.degreeOf (some 2)→0<G.degreeOf none → ∃ W∈V,¬ G∣bC W) :
    ∃ W∈V,W≠0 ∧ ∀ G:ko,Irreducible G→G∣bC F →
      0<G.degreeOf (some 2)→0<G.degreeOf none → ¬ G∣bC W:= by
  classical
  let I := {H :ko // H∈factors (bC F)}
  let:Finite I:=Set.finite_coe_iff.mpr (factors (bC F)).finite_toSet
  let tests :Option I→zpI ao V:= fun k =>
    match k with
    | none => ⊥
    | some H =>
      if ∃ G:ko,Irreducible G∧G∣bC F∧0<G.degreeOf (some 2) ∧
          0<G.degreeOf none∧Associated G H.val then bEl V H.val else ⊥
  have bot_proper : (⊥ : zpI ao V) ≠ ⊤ := by
    obtain ⟨W,hW,hnW⟩:=hn
    intro heq
    have hmem: (⟨W,hW⟩:V)∈(⊥ : zpI ao V) :=heq ▸ z8t
    exact hnW (congrArg Subtype.val ((zLn ao).mp hmem))
  have ht : ∀ k,tests k ≠ ⊤ := by
    intro k
    cases k with
    | none=>exact bot_proper
    | some H =>
      change (if _ then bEl V H.val else ⊥) ≠ ⊤
      split_ifs with h
      · obtain ⟨G,hi,hd,hv,hs,ha⟩:=h
        obtain ⟨W,hW,hnW⟩:=hproper G hi hd hv hs
        intro heq
        have hmem: (⟨W,hW⟩:V)∈bEl V H.val :=heq ▸ z8t
        exact hnW (ha.dvd.trans ((mem_divisible V H.val ⟨W,hW⟩).mp hmem))
      · exact bot_proper
  obtain ⟨W,hW⟩:=Submodule.exists_forall_notMem_of_forall_ne_top
    (ι:=Option I) (K:=ao) (M:=V) tests ht
  refine ⟨W.val,W.property,?_,?_⟩
  · exact fun hz=>hW none ((zLn ao).mpr (Subtype.ext hz))
  · intro G hi hd hv hs hdiv
    obtain ⟨H,hH,ha⟩:=exists_mem_factors_of_dvd (agr hF) hi hd
    let key :I:=⟨H,hH⟩
    apply hW (some key)
    change W∈(if _ then bEl V H else ⊥)
    rw [ite_eq_left ⟨G,hi,hd,hv,hs,ha⟩]
    exact (mem_divisible V H W).mpr (ha.symm.dvd.trans hdiv)
theorem topCommon {F W:jK}
   (h : ∀ G:ko,Irreducible G→G∣bC F →
     0<G.degreeOf (some 2)→0<G.degreeOf none → ¬ G∣bC W) :
   ∀ Q:MvPolynomial (Fin 4) cu.FX,Irreducible Q→0<Q.degreeOf 3 →
     Q∣topLift (toTop F)→Q∣topLift (toTop W)→Q.degreeOf 0=0:= by
 intro Q hQ ht hF hW
 let e :=MvPolynomial.renameEquiv iP aD
 let G:=e.symm Q
 have hG:e G= Q:=e.apply_symm_apply Q
 have he (R:jK) :e (bC R)=topLift (toTop R) :=
   (MvPolynomial.map_rename qV aD R).symm
 have hirr :Irreducible G:=hQ.map e.symm
 have hpos :0<G.degreeOf (some 2) := by
   have hdeg:Q.degreeOf 3=G.degreeOf (some 2) :=
     hG ▸ zTg aD.injective (some 2)
   exact hdeg ▸ ht
 have hs :Q.degreeOf 0=G.degreeOf none :=
   hG ▸ zTg aD.injective none
 rw [hs]
 by_contra hne
 have hd (R:jK) (hr :Q∣topLift (toTop R)) :G∣bC R:= by
   have hd:=map_dvd e.symm (by simpa only [he] using hr :Q∣e (bC R))
   simpa only [AlgEquiv.symm_apply_apply] using hd
 exact h G hirr (hd F hF) hpos (Nat.pos_of_ne_zero hne) (hd W hW)
end
end qlc9qed
end
section
set_option autoImplicit true
namespace qfqELEc
open Finset Rj
open qlc9qed (Bank)
open qPQ4nYa (cappedCumulative)
structure Factors where
 z :ℕ
 y :ℕ
 x :ℕ
 xy :ℕ
 xz :ℕ
 conic:ℕ
def Factors.powers (p:Factors) :kJ := ![p.z,p.y,p.x,p.xy,p.xz,p.conic]
private def slot (width start bits k :ℕ) :ℕ :=
 if k<start then 0 else bits >>> (width*(k-start))
private def slopePower (q k :ℕ) :ℕ :=
 let power :=170-(2*q+k)
 if q<50∧max (170-3*q) (max (151-2*q) (120-q))≤k∧2≤power then power else 0
private def atoms (q start bits k :ℕ) :Factors :=
 if q<32 then
  ⟨0,0,slot 4 start bits k % 16,0,slopePower q k,0⟩
 else if q<90 then
  ⟨0,0,slot 4 (120-q) 0x223566789b k % 16,0,slopePower q k,slot 5 start bits k % 32⟩
 else if q<119 then
  let w:=slot 9 start bits k
  ⟨0,0,w % 16,0,0,(w >>> 4) % 32⟩
 else
  let w:=slot 19 start bits k
  ⟨w % 32,(w >>> 5) % 16,0,(w >>> 9) % 32,0,(w >>> 14) % 32⟩
private def kernel (d w t:ℤ) (p:Factors) :ℤ :=
 let a :ℤ:=p.z
 let b:ℤ:=p.y
 let c:ℤ:=p.x
 let e :ℤ:=p.xy
 let f :ℤ:=p.xz
 let z :ℤ:=p.conic
 let n:=d-(a+b+c+e+f+2*z)
 if n<0 then 0 else
   sG (n+1)-(yC ⟨-(a+b+z),w-(2*a+b+z)⟩ +
     yC ⟨d-19-(b+c+e+z),2*d-50-(b+c+2*e+2*z)⟩ +
     yC ⟨-(a+c+f+z),t-(a+c+2*f+2*z)⟩)
private def PN (q k :ℕ) (p:Factors) :ℕ :=
 let d:=min q 50
 let w:=50-(k :ℤ)
 let t:=170-(q:ℤ) - k
 if t≤0 then 0 else
   (cappedCumulative d 19 50 - cappedCumulative d 19 (min 50 (w-1)) -
     max 0 (max (kernel d w t ⟨0,0,0,0,0,0⟩) (kernel d w t p))).toNat
private theorem cell_eq (q k :ℕ) (p:Factors) :
  qPQ4nYa.xR .strong q (qPQ4nYa.offset .strong k) p.powers=PN q k p:= by
 have hw : -qPQ4nYa.offset .strong k=50-(k :ℤ) := by
  change -((k :ℤ)-50)= _
  omega
 have ht:qPQ4nYa.Ic .strong q (qPQ4nYa.offset .strong k) =
    170-(q:ℤ) - k := by
  change 120-(q:ℤ)-((k :ℤ)-50)= _
  omega
 simp [qPQ4nYa.xR,qPQ4nYa.Bb,qPQ4nYa.K6,
  qPQ4nYa.D8,qPQ4nYa.pT,hw,ht,PN,kernel,Factors.powers,
  qPQ4nYa.iO,Bank.box,m5,zCS,
  yE,Jd]
 ring_nf
private def sumUp (f :ℕ→ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>sumUp f n+f n
private theorem sumUp_eq (f :ℕ→ℕ) (n:ℕ) :sumUp f n = ∑ k∈range n,f k := by
 induction n with
 | zero=>simp [sumUp]
 | succ n ih=>rw [sumUp,sum_range_succ,ih]
def Sk (q start bits :ℕ) :ℕ :=
 sumUp (fun k=>PN q k (atoms q start bits k)) (170-q)
def gradeSum (q:ℕ) (p:ℕ→kJ) :ℕ :=
 ∑ k∈range 170,qPQ4nYa.xR .strong q (qPQ4nYa.offset .strong k) (p k)
private theorem c85 (q start bits :ℕ) :
   gradeSum q (fun k=>(atoms q start bits k).powers)=Sk q start bits := by
 rw [Sk,sumUp_eq,gradeSum]
 rw [← sum_subset (range_mono (Nat.sub_le 170 q))]
 · exact sum_congr rfl fun k _=>cell_eq q k _
 · intro k _ hk
   rw [cell_eq,PN,ite_eq_left]
   simp only [mem_range,not_lt] at hk
   omega
structure Window (s n r :ℕ) :Prop where
 witness : ∃ p:ℕ→ℕ→kJ,∑ i∈range n,gradeSum (s+i) (p (s+i))=r
theorem row (q start bits r :ℕ) (h:Sk q start bits=r) :Window q 1 r := by
 refine ⟨⟨fun _ k=>(atoms q start bits k).powers,?_⟩⟩
 simpa [c85] using h
theorem join {s n m r t:ℕ} (h:Window s n r) (l:Window (s+n) m t) :
   Window s (n+m) (r+t) := by
 obtain ⟨p,hp⟩:=h.witness
 obtain ⟨v,hv⟩:=l.witness
 refine ⟨⟨fun q=>if q<s+n then p q else v q,?_⟩⟩
 rw [sum_range_add]
 apply congrArg₂ Nat.add
 · rw [← hp]
   refine sum_congr rfl fun i hi => ?_
   simp only [ite_eq_left (Nat.add_lt_add_left (mem_range.mp hi) s)]
 · rw [← hv]
   refine sum_congr rfl fun i _ => ?_
   simp only [← Nat.add_assoc,ite_eq_right (by omega : ¬ s+n+i<s+n)]
end qfqELEc
end
section
set_option autoImplicit true
namespace qzLARrc
noncomputable section
open aR (ao jF Shape)
open jA
open NR (Lq amn O8 aVU)
open aFN (canonical GV)
open private eval_lift cM8 aVo fXa dsy from ProximityPrize.SubmissionLower.S
open scoped Polynomial
theorem normalized_center {Γ s} (P:jF Γ s) (L:kH P) (α:ao)
    (hroot :P.H.IsRoot α) (hsimple :P.H.derivative.eval α≠0) :
    ∃ k d e :ao,k≠0∧d≠0 ∧
      ∀ (a :Shape) (F:jK),F∈amn P L a (O8 α) ↔
        (MvPolynomial.C (O8 α) :Lq)^(a.b+a.j) ∣
          canonical (O8 α) (GV (projectivity k d e) F) := by
  let k := -P.q.eval α
  let c:=P.c.eval α
  let d:=c*P.a₀.eval α
  let e :=c*P.a₁.eval α
  have hk :k≠0:=neg_ne_zero.mpr (cM8 P.q_unit hroot)
  have hd:d≠0:=mul_ne_zero (cM8 P.c_unit hroot)
    (cM8 P.a₀_unit hroot)
  let D:ao[X] :=z1z d+Polynomial.C e*z7y
  have hD:D ≠0:= by
    intro hz
    have he :=congrArg (Polynomial.evalRingHom 0) hz
    exact hd (by simpa [D] using he)
  have hD' : algebraMap ao[X] kS D ≠0 :=
    (map_ne_zero_iff _ (zxb ao[X] kS)).mpr hD
  have hC (a :ao) :algebraMap ao[X] kS (z1z a) =
      algebraMap ao kS a :=
    (IsScalarTower.algebraMap_apply ao ao[X] kS a).symm
  have hcent: (ahH L.numerator L.denominator).eval
      (algebraMap ao kS α)=projectivity k d e := by
    unfold projectivity
    dsimp only
    have heD:algebraMap ao[X] kS D =algebraMap ao kS d +
        algebraMap ao kS e*algebraMap ao[X] kS Polynomial.X:= by
      simp [D,hC]
    rw [← heD]
    apply (eq_div_iff hD').mpr
    have h:=Polynomial.eval_dvd (x :=algebraMap ao kS α) L.generic_congruence
    have hz :P.H.eval α=0:=hroot
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,eval_lift,
      hz,map_zero,zero_dvd_iff] at h
    simp only [D,hC,k,d,c,e,map_add,map_mul,map_neg]
    linear_combination h
  refine ⟨k,d,e,hk,hd,fun a F => ?_⟩
  let u₀:=P.H /ₘ (z7y-Polynomial.C α)
  have hu₀: (z7y-Polynomial.C α)*u₀=P.H :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hH :jH P.H=O8 α*jH u₀:= by
    have h:=congrArg (zhd (algebraMap ao kS)) hu₀.symm
    simpa [jH,O8] using h
  have hcop:IsCoprime (O8 α) (jH u₀) := by
    have h:=Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero P.H α hsimple
    simpa [O8,jH,u₀] using h.map (zhd (algebraMap ao kS))
  let z₀:=projectivity k d e
  have hres :O8 α∣ahH L.numerator L.denominator-Polynomial.C z₀ :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot,hcent,z₀])
  obtain ⟨v,hv⟩:=hres
  have hres' : ahH L.numerator L.denominator=z1z z₀+O8 α*v := by
    linear_combination hv
  rw [aVU,fXa P L α z₀ (jH u₀) v hH hres' F]
  exact dsy (O8 α) (a.b+a.j) (aVo (jH u₀)) (aVo v)
    (by simpa [aVo,Polynomial.hasseDeriv_zero] using hcop) _
end
end qzLARrc
end
section
set_option autoImplicit true
namespace q6AUWfb
noncomputable section
open jA
open qlc9qed (Bank)
open private c6G aei from ProximityPrize.SubmissionLower.S
open scoped BigOperators
abbrev Exponent:=mA →₀ ℕ
private def tuples (a :ℕ) :Finset (ℕ×ℕ×ℕ×ℕ) :=
  (zUb a 20).biUnion fun c =>
    (z4x (51 - 2*c)).biUnion fun j =>
      (z4x (165 - c - j)).biUnion fun i =>
        (z4x 3038).image fun z=>(c,j,i,z)
def rU (a :ℕ) :Finset Exponent:=(tuples a).image aei
def slots (a :ℕ) :ℕ:=3038 * ∑ c∈zUb a 20,(51 - 2*c)*140
private theorem value_choices {c:ℕ} (hc:c≤19) :
   (∑ j∈z4x (51 - 2*c),(165 - c - j))=(51 - 2*c)*140:= by
 let n:=51 - 2*c
 let f (j:ℕ) :=165 - c - j
 have h:=Finset.sum_range_reflect f n
 have hp: (∑ j∈z4x n,(f j+f (n - 1 - j)))=n*280:= by
   rw [Finset.sum_const_nat (m:=280) (by
     intro j hj
     have hj' := Finset.mem_range.mp hj
     dsimp [f,n] at *
     omega),ztd]
 rw [Finset.sum_add_distrib,h] at hp
 change (∑ j∈z4x n,f j)=n*140
 omega
theorem b2w {R:Type*} [CommSemiring R] {a :ℕ} {F:VP R}
   (hc:Jn Bank.strong.box F) (hz :gY F≤Bank.strong.U)
   {m:Exponent} (hm:m∈F.support) (ha :a≤ m (some 2)) :m∈rU a := by
 classical
 have htotal:=(z6P
   (fun i:mA=>i.elim 0 (fun _=>1)) hm).trans hc.1
 have hindex :=(z6P
   (fun i:mA=>i.elim 0 Fin.val) hm).trans hc.2.1
 have hseed :=(zTo (none :mA) hm).trans hz
 have htop:=(zTo (some 2 :mA) hm).trans hc.2.2.1
 have hB:m (some 0)+m (some 1)+m (some 2)≤164 := by
   simpa [zDM,z9d,zy6,
     zCS,Bank.box,Nat.add_assoc] using htotal
 have hJ:m (some 1)+2*m (some 2)≤50:= by
   simpa [zDM,z9d,zy6,
     zCS,Bank.box,Nat.mul_comm] using hindex
 change m (some 2)≤19 at htop
 change m none≤3037 at hseed
 refine Finset.mem_image.mpr ⟨(m (some 2),m (some 1),m (some 0),m none),?_,?_⟩
 · simp only [tuples,Finset.mem_biUnion,Finset.mem_Ico,Finset.mem_range,Finset.mem_image]
   exact ⟨m (some 2),⟨ha,by omega⟩,m (some 1),by omega,m (some 0),by omega,
     m none,by omega,rfl⟩
 · ext i
   cases i with
   | none=>simp [aei]
   | some i=>fin_cases i <;> simp [aei]
private theorem card_exponents (a :ℕ) : (rU a).card≤ slots a :=
  Finset.card_image_le.trans (by
    unfold tuples
    calc
      _ ≤ ∑ c∈zUb a 20,∑ j∈z4x (51 - 2*c),
          ∑ _∈z4x (165 - c - j),3038:= by
        refine Finset.card_biUnion_le.trans (zQk fun c _ => ?_)
        refine Finset.card_biUnion_le.trans (zQk fun j _ => ?_)
        refine Finset.card_biUnion_le.trans (zQk fun i _ => ?_)
        exact Finset.card_image_le.trans_eq (ztd _)
      _=slots a := by
        rw [slots,Finset.mul_sum]
        simp only [Finset.sum_const,ztd,Nat.nsmul_eq_mul]
        apply Finset.sum_congr rfl
        intro c hc
        rw [← Finset.sum_mul,value_choices (by have :=(Finset.mem_Ico.mp hc).2; omega),
          Nat.mul_comm])
theorem dQC (a r :ℕ) (e :Fin r→ko) (he :LinearIndependent iP e)
    (h : ∀ F∈Submodule.span iP (Set.range e),
      Jn Bank.strong.box F∧gY F≤Bank.strong.U ∧
        (F≠0→a≤F.degreeOf (some 2))) :r≤ slots a := by
  have hr :=c6G (rU a) e he (by
    intro F hF hn
    obtain ⟨m,hm,heq⟩:=Finset.exists_mem_eq_sup F.support
      (MvPolynomial.support_nonempty.mpr hn) (fun u=>u (some 2))
    obtain ⟨hb,hs,hd⟩:=h F hF
    rw [MvPolynomial.degreeOf_eq_sup,heq] at hd
    exact ⟨m,b2w hb hs hm (hd hn),MvPolynomial.mem_support_iff.mp hm⟩)
  exact hr.trans (card_exponents a)
theorem bwH {a :ℕ} (ha :20≤a) :slots a=0:= by
 rw [slots,Finset.Ico_eq_empty_of_le ha,Finset.sum_empty,Nat.mul_zero]
theorem slots_sum: (∑ k∈z4x 19,slots (1+k))=3038*665000:= by
 have hf (a :ℕ) : (z4x 20).filter (fun c=>a≤ c)=zUb a 20:= by
   ext c
   simp [and_comm]
 unfold slots
 rw [← Finset.mul_sum]
 refine congrArg (fun n:ℕ=>3038*n) ?_
 simp only [← hf,zLJ]
 rw [Finset.sum_comm]
 have hc (c:ℕ) (hc:c∈z4x 20) :
     (z4x 19).filter (fun k=>1+k≤ c)=z4x c:= by
   have hn:=Finset.mem_range.mp hc
   ext k
   simp only [Finset.mem_filter,Finset.mem_range]
   omega
 calc
   _ = ∑ c∈z4x 20,c*((51 - 2*c)*140) := by
     apply Finset.sum_congr rfl
     intro c h
     rw [← zLJ,hc c h]
     simp
   _ = _:= by norm_num [Finset.sum_range_succ]
end
end q6AUWfb
end
