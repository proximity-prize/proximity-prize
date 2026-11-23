import ProximityPrize.SubmissionLower.Zm2Uhnd
import ProximityPrize.SubmissionLower.ZlH1Cxb
import ProximityPrize.SubmissionLower.ZAJiURc
import ProximityPrize.SubmissionLower.P5_7_1_3_2Local
import ProximityPrize.SubmissionLower.ZSyXMse
import ProximityPrize.SubmissionLower.ZbnhR9d
import ProximityPrize.SubmissionLower.ZHcXm6a
import ProximityPrize.SubmissionLower.ZVHUUZd
import ProximityPrize.SubmissionLower.Z9Zvicc
import ProximityPrize.SubmissionLower.ZZ5hHja
import ProximityPrize.SubmissionLower.ZVZMqYa
import ProximityPrize.SubmissionLower.ZVMYHza
import ProximityPrize.SubmissionLower.ZJLBXgd
set_option Elab.async false
open _root_ renaming Finset → zJe, Finsupp.mapDomain → z8D, Ideal → znc, MvPolynomial.le_degreeOf_of_mem_support → zTo, MvPolynomial.le_weightedTotalDegree → z6P, Nat.cast_add → z6H, Nat.cast_mul → z2R, Nat.cast_nonneg → zqJ, Nat.cast_sum → zCt, Nat.le_mul_of_pos_left → zCV, Nat.sub_add_cancel → zxt, Nat.zero_le → zD0, Submodule.mem_iInf → zxR
set_option maxHeartbeats 2000000
section
set_option autoImplicit true
set_option Elab.async false
namespace q4atxtd
theorem node_bound:qGnV2ac.c1 :=
  qbjv5ec.of_children (qcuqT2c.of_children qNqPG5b.proof qbY56ta.proof
    qGA3mAd.proof) qkA2Qzc.proof
theorem proof :qXdgDRd.c1 := fun F l h _ H=>node_bound F l h H
theorem proof271 :qcuQADa.c1 := fun F l h _=>node_bound F l h
end q4atxtd
end
section
set_option autoImplicit true
namespace q4RoJqb
theorem proof :qcuQADa.c2 := by
  have poles :qGnV2ac.c2 :=
    qrKC9pb.of_children qWIOgVd.proof qazuAoe.proof
      (qyUzJvd.of_children qnCt0Qc.proof qc2iTLd.proof
        q6lciJe.proof)
      (qj0Yp9c.of_children
        (qO4AyGb.of_children qWz9F7b.proof qW0d9ye.proof)
        qBTXDtb.proof)
  intro b F l h u s W _
  exact poles F l h u s (qXdgDRd.width (qcuQADa.degree b)) W
end q4RoJqb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qpWH4Ce
noncomputable section
open aR (ao)
open jA
open NR (TT)
open qlc9qed (Bank ays)
open qPQ4nYa (apR origin originRange originRange_le_sum rankBudget)
open MvPolynomial
open private AV Bg Ky aob normalize from ProximityPrize.SubmissionLower.S
open private flat_capped normalize_capped contact_of_origin_zero from ProximityPrize.SubmissionLower.P5_7_1_3_2Local
theorem codim_le_origin (b:Bank) (u:ℕ) (a v :ao) (V:Submodule ao jK)
    [Module.Finite ao V] (hcap : ∀ F∈V,Jn b.box F∧gY F≤u) :
    TT V (ays b.m a v)≤(u+1)*Module.finrank ao (originRange b) := by
  let A:V →ₗ[ao] (Fin (u+1)→ originRange b) :=LinearMap.pi fun n =>
    ((origin b).domRestrict (apR b)).rangeRestrict ∘ₗ
      (((normalize a v).toLinearMap ∘ₗ aob n ∘ₗ V.subtype).codRestrict _
        (fun F=>normalize_capped (flat_capped (hcap F F.property).1 n) a v))
  have hz (F:A.ker) : (F.val :jK)∈ays b.m a v := by
    apply contact_of_origin_zero
    intro n
    by_cases hn:n< u+1
    · have h:=congrFun (LinearMap.mem_ker.mp F.property) ⟨n,hn⟩
      exact congrArg (fun z :originRange b=>z.val) h
    · have hd: (AV (F.val :jK)).natDegree≤u:= by
        simpa only [AV,natDegree_optionEquivLeft,gY] using
          (hcap F.val F.val.property).2
      have h₀:Bg n F.val=0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))
      have h₁:aob n F.val=0:= by
        change Ky.symm (Bg n F.val)=0
        rw [h₀,map_zero]
      simp [h₁]
  have hle :A.ker.map V.subtype≤V ⊓ ays b.m a v := by
    rintro _ ⟨F,hF,rfl⟩
    exact Submodule.mem_inf.mpr ⟨F.property,hz ⟨F,hF⟩⟩
  have hk :=Submodule.finrank_mono hle
  rw [Submodule.finrank_map_subtype_eq] at hk
  have hr :=Submodule.finrank_le A.range
  rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hr
  have hnull:=LinearMap.finrank_range_add_finrank_ker (K:=ao)
    (V := ↥V) (V₂:=Fin (u+1)→ originRange b) A
  have hc:TT V (ays b.m a v)≤Module.finrank ao A.range := by
    unfold TT
    omega
  exact hc.trans (by simpa only [Nat.cast_id] using hr)
theorem proof :qFAh60c.c2 := by
  intro b a v V hV hcap
  let:Module.Finite ao V:=hV
  have hb : ∃ p:ℕ→ℕ→Rj.kJ,rankBudget b p≤b.contactRank := by
    cases b
    · exact P5_7_2_3Q1322.proof
    · exact P5_7_2_3Q132.proof
  obtain ⟨p,hp⟩:=hb
  have hr :=(originRange_le_sum b p
    (fun q hq k hk=>qzM5sEd.proof b q k hq hk (p q k))).trans hp
  exact (codim_le_origin b (qFAh60c.width b) a v V hcap).trans (Nat.mul_le_mul_left _ hr)
end
end qpWH4Ce
end
section
set_option autoImplicit true
namespace qMjv6ic
theorem proof :qXdgDRd.c2 := by
  have poleBound:qGnV2ac.c2 :=
    qrKC9pb.of_children qWIOgVd.proof qazuAoe.proof
      (qyUzJvd.of_children qnCt0Qc.proof qc2iTLd.proof
        q6lciJe.proof)
      (qj0Yp9c.of_children
        (qO4AyGb.of_children qWz9F7b.proof qW0d9ye.proof)
        qBTXDtb.proof)
  intro F l h u s W _
  exact poleBound F l h u s (qXdgDRd.width P6_7_1.degree) W
end qMjv6ic
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q84jfie
noncomputable section
open Polynomial
open P6 (p)
open P6_7 (RectTail)
open P6_7_2 (Input TopCaps)
open aR (ao)
open jA Rk
open acZ (bI3 cfL)
open aA0 (cEb c4E)
open qlc9qed (Bank bsz toTop aD)
open private trueCut_shift egb sum_coeffs from ProximityPrize.SubmissionLower.ZTFKldb
open private dxN a8W from ProximityPrize.SubmissionLower.S
open private line b7T cYc ct4 c40 from ProximityPrize.SubmissionLower.A3
theorem mem_ambient {b h U t F} : F∈Aw b h U t ↔
    Jn b.box F∧gY F≤U∧ahb h (t+(b.box.b+b.box.j)*h) F:= by
  classical
  simp only [Aw,Submodule.mem_inf,Submodule.mem_comap,Submodule.restrictScalars_mem,
    cfL,bI3,MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle]
  change (Jn b.box (bC F)∧gY (bC F)≤U)∧ahb h _ F↔_
  simp only [Jn,vC,lP,gY,MvPolynomial.weightedTotalDegree,
    MvPolynomial.degreeOf_eq_sup,egb,and_assoc]
theorem shift {r :RectTail} {x :Input r} (P:OnePole x) (b:Bank) {U t F}
    (hF:F∈aV x.M.word P.data P.bY b U t) (i:ℕ) :
    Yd P.data.H i F∈aV x.M.word P.data P.bY b U (t+(3*x.h)*i) := by
  obtain ⟨hA,hC,hP⟩:=Submodule.mem_inf.mp hF
  obtain ⟨hc,hs,hw⟩:=mem_ambient.mp hA
  refine Submodule.mem_inf.mpr ⟨mem_ambient.mpr ⟨cEb P.data.H i F b.box hc,?_,?_⟩,?_,?_⟩
  · rw [gY,MvPolynomial.degreeOf_le_iff]
    intro a ha
    exact (Nat.le_add_left ..).trans
      ((zTo none (a8W ha)).trans hs)
  · rw [← P.height]
    simpa only [Nat.add_right_comm] using trueCut_shift P.data.H i _ F hw
  · apply (zxR _).mpr
    intro j
    have hj:=(bsz _ _ _ _).mp ((zxR _).mp hC j)
    apply (bsz _ _ _ _).mpr
    intro a
    exact dxN P.data.H i b.m _ _ F hj a
  · exact (NR.aVU _ _ _ _ _).mpr
      (c4E P.data P.bY _ i F ((NR.aVU _ _ _ _ _).mp hP))
theorem bank_mono {r :RectTail} {x :Input r} (P:OnePole x) (b:Bank) (U:ℕ) {s t:ℕ} (hst:s≤t) :
    aV x.M.word P.data P.bY b U s≤aV x.M.word P.data P.bY b U t:= by
  rintro F ⟨hA,hC⟩
  obtain ⟨hc,hs,hw⟩:=mem_ambient.mp hA
  exact ⟨mem_ambient.mpr ⟨hc,hs,fun a ha=>(hw a ha).trans (Nat.add_le_add_right hst _)⟩,hC⟩
theorem topCaps {r :RectTail} {x :Input r} (P:OnePole x) (b:Bank) {U F}
    (hF:F∈aV x.M.word P.data P.bY b U (cut b)) :
    TopCaps x.h b.m b.box.b b.box.j b.box.t U (toTop F) := by
  classical
  obtain ⟨⟨hB,hJ,hC,_⟩,hU,hw⟩:=mem_ambient.mp (Submodule.mem_inf.mp hF).1
  intro a ha
  rw [toTop,MvPolynomial.support_rename_of_injective aD.injective] at ha
  obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp ha
  rw [toTop,MvPolynomial.coeff_rename_mapDomain _ aD.injective]
  have hB' := (z6P (fun i:mA=>i.elim 0 (fun _=>1)) he).trans hB
  have hJ' := (z6P (fun i:mA=>i.elim 0 Fin.val) he).trans hJ
  have hC' := (zTo (some 2) he).trans hC
  have hU' := (zTo none he).trans hU
  rw [P.height] at hw
  have hf :=hw e he
  simp only [Finsupp.weight_apply,smul_eq_mul] at hB' hJ'
  have hs (w:Fin 3→ℕ) :
      e.sum (fun i n=>n*i.elim 0 w) =
        w 0*e (some 0)+w 1*e (some 1)+w 2*e (some 2) := by
    rw [← sum_coeffs e w]
    congr 1
    funext i n
    cases i <;> simp [Nat.mul_comm]
  rw [hs] at hB' hJ'
  rw [sum_coeffs] at hf
  let d:=131071 + x.h
  have h1 : (d-1)*e (some 1)+e (some 1)=d*e (some 1) := by
    calc
      _=(d-1)*e (some 1)+1*e (some 1) := by simp
      _ = _:= by rw [← Nat.add_mul,zxt (by dsimp [d]; omega)]
  have h2 : (d-2)*e (some 2)+2*e (some 2)=d*e (some 2) := by
    rw [← Nat.add_mul,zxt (by dsimp [d]; omega)]
  change (F.coeff e).natDegree+(d*e (some 0)+(d-1)*e (some 1) +
    (d-2)*e (some 2))≤ cut b+(b.box.b+b.box.j)*x.h at hf
  have he0: (z8D aD e) 0=e none := by
    simpa only [aD,finSuccEquiv_symm_none] using
      Finsupp.mapDomain_apply_of_injective aD.injective e none
  have he1 : (z8D aD e) 1=e (some 0) := by
    simpa only [aD,finSuccEquiv_symm_some,(by decide : ((0:Fin 3).succ)=1)] using
      Finsupp.mapDomain_apply_of_injective aD.injective e (some 0)
  have he2 : (z8D aD e) 2=e (some 1) := by
    simpa only [aD,finSuccEquiv_symm_some,(by decide : ((1 :Fin 3).succ)=2)] using
      Finsupp.mapDomain_apply_of_injective aD.injective e (some 1)
  have he3: (z8D aD e) 3=e (some 2) := by
    simpa only [aD,finSuccEquiv_symm_some,(by decide : ((2 :Fin 3).succ)=3)] using
      Finsupp.mapDomain_apply_of_injective aD.injective e (some 2)
  rw [he0,he1,he2,he3]
  refine ⟨by simpa using hB',by simpa using hJ',hC',hU',?_⟩
  change (F.coeff e).natDegree+d*(e (some 0)+e (some 1)+e (some 2)) ≤
    cut b+(b.box.b+b.box.j)*x.h+e (some 1)+2*e (some 2)
  simp only [Nat.mul_add]
  omega
theorem factor_power {r :RectTail} {x :Input r} (P:OnePole x) {U:ℕ}
    (hh:0<x.h) {G:ko}
    (hi:Irreducible G) (hs :0<G.degreeOf none) (hsmall:G.degreeOf none<p)
    (hdiv : ∀ F∈aV x.M.word P.data P.bY .strong U (cut .strong),G∣bC F) :
    ∀ t≤ cut .strong,∀ F∈aV x.M.word P.data P.bY .strong U t,G^powerAt P.data.H.natDegree t∣bC F:= by
  intro t ht F hF
  rw [P.height]
  have hpos :0<3*x.h:= by omega
  apply c40 (line none) (b7T none)
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi) (ct4 hs hsmall)
  intro i hi'
  have hle :i≤(cut .strong - t)/(3*x.h) := by
    unfold powerAt at hi'
    omega
  have hm: (3*x.h)*i≤ cut .strong - t:= by
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hpos).mp hle
  have hcut:t+(3*x.h)*i≤ cut .strong:= by omega
  have hd:=hdiv _ (bank_mono P .strong U hcut (shift P .strong hF i))
  rw [cYc]
  have hn:qV (P.data.H^(3*i))≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ao[X] iP)).mpr
      (pow_ne_zero _ P.data.monic.ne_zero)
  have hunit :IsUnit (MvPolynomial.C (qV (P.data.H^(3*i))) :ko) :=
    (IsUnit.mk0 _ hn).map MvPolynomial.C
  apply hunit.dvd_mul_left.mp
  simpa only [Yd,bC,map_mul,MvPolynomial.map_C] using hd
end
end q84jfie
end
section
set_option autoImplicit true
namespace qigFtUb
open Finset cu P6_7_2
open P6_7 (RectTail)
open czX (a8x dei)
open private bcT dfW auf from ProximityPrize.SubmissionLower.A2
private def poleRow (B J q d:ℤ) :ℤ :=
  let a :=B+J-q-d
  let z :=B-2*q
  bcT (a*z) (a+2*z) 2 0 (d+1)
private theorem poleRow_eq (B J q:ℤ) (d:ℕ) :
    poleRow B J q d =
      12*(∑ j∈range (d+1),(B+J-q-d+2*j)*(B-2*q+j)) := by
  unfold poleRow
  rw [← Nat.cast_succ,← dfW]
  congr 1
  apply sum_congr rfl
  intro j _
  ring
private theorem aJH (B J start base step:ℤ) (n:ℕ) :
    120*(∑ i∈range n,poleRow B J (start+i) (base+step*i)) =
      auf (fun i=>poleRow B J (start+i) (base+step*i)) n:= by
  let f (i:ℤ) :=poleRow B J (start+i) (base+step*i)
  have h (x :ℤ) :auf f (x+1)=auf f x+120*f x := by
    unfold auf f poleRow bcT
    ring
  change 120*(∑ i∈range n,f i)=auf f n
  induction n with
  | zero=>simp [auf]
  | succ n ih=>rw [Nat.cast_succ,h,sum_range_succ,mul_add,ih]
private def eta (s :Shape) (q j:ℕ) :ℕ :=
  s.B+s.J+2*j-(q+min q s.J)
private def paidPole (s :Shape) :ℕ :=
  ku s fun q j=>eta s q j*(2*s.B+j+1-2*q)
private def rawPole (s :Shape) :ℕ :=
  (s.B+1)*ku s (eta s)
private theorem pole_signed (s :Shape) :
    (paidPole s :ℤ)-rawPole s =
      ∑ q∈range (s.B+1),∑ j∈range (min q s.J+1),
      ((s.B:ℤ)+s.J-q-(min q s.J:ℕ)+2*j)*(s.B-2*q+j) := by
  unfold paidPole rawPole ku
  simp only [zCt,z2R,z6H,Nat.cast_one,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro j _
  have hb:=Nat.lt_succ_iff.mp (mem_range.mp hq)
  have hd:=min_le_right q s.J
  have h1 :q+min q s.J≤ s.B+s.J+2*j:= by omega
  have h2 :2*q≤2*s.B+j+1 := by omega
  simp only [eta,Nat.cast_sub h1,Nat.cast_sub h2,z6H,z2R,Nat.cast_one,
    Nat.cast_ofNat]
  ring
private def poleTotal (s :Shape) :ℤ :=
  auf (fun i=>poleRow s.B s.J i i) s.J +
  auf (fun i=>poleRow s.B s.J (s.J+i) s.J) (s.B+1-s.J:ℕ)
private theorem poleTotal_eq (s :Shape) (hJ:s.J≤ s.B+1) :
    poleTotal s=1440*((paidPole s :ℤ)-rawPole s) := by
  let f (q:ℕ) :=poleRow s.B s.J q ((min q s.J:ℕ) :ℤ)
  have hf : (∑ q∈range (s.B+1),f q)=12*((paidPole s :ℤ)-rawPole s) := by
    rw [pole_signed,mul_sum]
    apply sum_congr rfl
    intro q _
    exact poleRow_eq s.B s.J q (min q s.J)
  have hs :=sum_range_add f s.J (s.B+1-s.J)
  rw [Nat.add_sub_of_le hJ] at hs
  have ha : (∑ q∈range s.J,f q) = ∑ q∈range s.J,poleRow s.B s.J q q:= by
    apply sum_congr rfl
    intro q hq
    simp only [f,min_eq_left (mem_range.mp hq).le]
  have hb: (∑ i∈range (s.B+1-s.J),f (s.J+i)) =
      ∑ i∈range (s.B+1-s.J),poleRow s.B s.J ((s.J:ℤ)+i) s.J:= by
    apply sum_congr rfl
    intro i _
    simp only [f,min_eq_right (Nat.le_add_right _ _),z6H]
  have h₀:=aJH s.B s.J 0 0 1 s.J
  have h₁:=aJH s.B s.J s.J s.J 0 (s.B+1-s.J)
  simp only [zero_add,one_mul] at h₀
  simp only [zero_mul,add_zero] at h₁
  rw [poleTotal,show (1440:ℤ)=120*12 by decide,mul_assoc,← hf,hs,mul_add,ha,hb,h₀,h₁]
def pole (b:RectTail) :ℕ:=(poleTotal (Bs b).terminal/ 1440).toNat
def amm (b:RectTail) :ℕ :=
  let s :=(Bs b).terminal
  262144*a8x (s.m-2*s.J) s.J/6
private theorem c4C (b:RectTail) :pole b=poleExtra (Bs b).terminal:= by
  let s :=(Bs b).terminal
  have hb:s.J≤ s.B+1 := by cases b <;> decide
  unfold pole
  rw [poleTotal_eq _ hb,Int.mul_ediv_cancel_left _ (by decide : (1440:ℤ)≠0)]
  change ((paidPole s :ℤ)-rawPole s).toNat=paidPole s-rawPole s
  omega
private theorem physical_eq (b:RectTail) :amm b=262144*localPhysical (Bs b).terminal:= by
  let s :=(Bs b).terminal
  have hm:2*s.J≤ s.m:= by cases b <;> decide
  have hb:s.m+s.J≤ s.B+1 := by cases b <;> decide
  have hp:=dei s hm hb
  change 6*(262144*localPhysical s)= _ at hp
  change 262144*a8x (s.m-2*s.J) s.J/6=262144*localPhysical s
  omega
theorem Fi (b:RectTail) (h u x :ℕ) :
    rectDebit b h ⟨u,x⟩=(u+1)*(x+1)*amm b+h*pole b*(u+x+2) := by
  rw [physical_eq,c4C]
  unfold rectDebit
  dsimp only
  ring
end qigFtUb
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qKfhfIb
noncomputable section
open Polynomial Finset
open P6 (K p blockLength)
open P5_7 (midAgreement)
open P6_7_3 (Input IntroIndex emz)
open qUrGXob (rankMarks rankPrice onMark initialBound originBox)
open TD (FP J2)
open aR (af extend embed)
open oR (qg)
open gT (Ambient tK FW)
open pI (xN dual abM d2l pN mass)



open private OF.distinct OF.degree from ProximityPrize.SubmissionLower.Z2oJVua
open qkOaTje (cover ordinatePrice mixedPrice phi phi_nonneg price_regular)
open private c3F from ProximityPrize.SubmissionLower.U
open scoped Classical BigOperators
local notation "Dmax" => P6_7_3.degree
abbrev lambdaD:ℚ:=((blockLength:ℚ)/midAgreement)*Dmax
abbrev μ:ℚ:=((blockLength - Dmax :ℕ) :ℚ)/(midAgreement - Dmax :ℕ)
private theorem regular_price (x :Input) {T:zJe K} (hT:T⊆x.Γ)
    (f :af 2) (hf :Irreducible f) (hj:0<f.degreeOf 1)
    (hreg : ∀ γ∈T,qg 1 f (extend (x.F.scalar γ))) :
    let b:ℚ:=f.totalDegree
    let j:ℚ:=f.degreeOf 1
    (T.card:ℚ)≤lambdaD*(4*b*j-2*j*j)+μ*j+1 :=
  qkOaTje.regular_price' (D:=Dmax) (by decide) (by decide) (by decide) x.F
    (fun γ hγ=>(P6_7.aic x.F hγ).trans (Nat.add_le_add_left (emz x).2 _))
    hT f hf hj hreg
private theorem equation_price (x :Input) {T:zJe K} (hT:T⊆x.Γ)
    {b j:ℕ} {B J:ℚ} (hbB: (b:ℚ)≤B) (hjJ: (j:ℚ)≤J)
    (hp:b<p) (G:tK) (hG:abM G b j)
    (hroot : ∀ γ∈T,FW G (x.F.scalar γ)=0) :
    (T.card:ℚ)≤ordinatePrice lambdaD μ B*j+(mixedPrice lambdaD B (min J B)+B+1)*b:= by
  classical
  obtain ⟨q,hq,hb,hj,hsolve⟩:=bz3.cFG G hG.1 hG.2.1 hG.2.2
  obtain ⟨A,R,hA,hAb,hAj,hR,hRd,hcover⟩:=cover q hq hp hb hj
  let s (γ:K) :=extend (x.F.scalar γ)
  let iy :=T.filter fun γ=>R.eval (s γ)=0
  let reg (f :af 2) :=T.filter fun γ=>qg 1 f (s γ)
  have hord:iy.card≤b^2 := by
    have hi:Set.InjOn s (iy :Set K) := fun _ ha _ hb he =>
      x.F.distinct (hT (filter_subset _ _ ha)) (hT (filter_subset _ _ hb))
        (Polynomial.map_injective embed embed.injective he)
    have hc: (iy.image s).card≤R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (mem_filter.mp hγ).2
    rw [card_image_of_injOn hi] at hc
    exact hc.trans hRd
  have hsub:T⊆iy∪A.biUnion reg:= by
    intro γ hγ
    rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨f,hf,hr⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨hγ,hr⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨f,hf,mem_filter.mpr ⟨hγ,hr⟩⟩)
  have hall: (T.card:ℚ)≤ iy.card + ∑ f∈A,((reg f).card:ℚ) := by
    exact_mod_cast (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left card_biUnion_le _))
  have hnum :A.card≤b:= calc
    A.card = ∑ _∈A,1 := by simp
    _ ≤ ∑ f∈A,f.totalDegree :=sum_le_sum fun f hf =>
      (hA f hf).2.trans_le (f.degreeOf_le_totalDegree 1)
    _≤b:=hAb
  let u:=ordinatePrice lambdaD μ B
  let v :=mixedPrice lambdaD B (min J B)
  have hL:0≤lambdaD:= by unfold lambdaD; positivity
  have hB:=(zqJ b).trans hbB
  have hu:0≤u:= by unfold u ordinatePrice μ; positivity
  have hv :0≤v := by
    have :=phi_nonneg (le_min ((zqJ j).trans hjJ) hB) (min_le_right J B)
    unfold v mixedPrice
    positivity
  have hreg: (∑ f∈A,((reg f).card:ℚ))≤u*j+v*b+b:= by
    calc
      _ ≤ ∑ f∈A,(u*f.degreeOf 1+v*f.totalDegree+1) := by
        apply sum_le_sum
        intro f hf
        have hfb: (f.totalDegree :ℚ)≤B :=
          (Nat.cast_le.mpr ((single_le_sum (fun g _=>zD0 g.totalDegree) hf).trans hAb)).trans hbB
        have hfj: (f.degreeOf 1 :ℚ)≤J :=
          (Nat.cast_le.mpr ((single_le_sum (fun g _=>zD0 (g.degreeOf 1)) hf).trans hAj)).trans hjJ
        have hjb: (f.degreeOf 1 :ℚ)≤f.totalDegree :=Nat.cast_le.mpr (f.degreeOf_le_totalDegree 1)
        exact price_regular hL (zqJ _) hjb hfb (le_min hfj (hjb.trans hfb)) (min_le_right J B)
          (regular_price x ((filter_subset _ _).trans hT) f (hA f hf).1 (hA f hf).2
            (fun _ hγ=>(mem_filter.mp hγ).2))
      _≤_:= by
        simp only [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,mul_one]
        have hjQ: (∑ f∈A,(f.degreeOf 1 :ℚ))≤j:= by exact_mod_cast hAj
        have hbQ: (∑ f∈A,(f.totalDegree :ℚ))≤b:= by exact_mod_cast hAb
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hjQ hu)
          (mul_le_mul_of_nonneg_left hbQ hv)) (Nat.cast_le.mpr hnum)
  have hordQ: (iy.card:ℚ)≤(b:ℚ)^2 := by exact_mod_cast hord
  have hreserve : (b:ℚ)^2≤B*b:= by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hbB (zqJ _)
  change (T.card:ℚ)≤u*j+(v+B+1)*b
  linarith only [hall,hreg,hordQ,hreserve]
private def marks (x :Input) (I:znc Ambient) :zJe K :=
  x.Γ.filter fun γ=>onMark x I γ
private theorem parent_price (x :Input) (o:IntroIndex) (I:znc Ambient)
    (ha :xN I) (hn : ¬ dual I)
    (hfit : ∀ k,(pN I k :ℚ)≤ min (originBox o k) (initialBound k)) :
    ((marks x I).card:ℚ)≤FP (rankPrice o) (fun k=>pN I k) := by
  obtain ⟨G,hG,hGon⟩:=c3F bzS.proof cy5.proof ha hn
  have h:=equation_price x (filter_subset _ _) (hfit 2) (hfit 1) ha.mixed_lt G hG
    (fun γ (hγ:γ∈marks x I)=> by
      have hz :=RingHom.mem_ker.mp ((mem_filter.mp hγ).2 hGon)
      simpa only [d2l] using hz)
  simpa [marks,FP,Fin.sum_univ_succ,rankPrice,ordinatePrice,mixedPrice,phi,lambdaD,μ,mul_assoc] using h
theorem proof :qUrGXob.c2 := by
  classical
  intro x o S hS
  have heq :rankMarks x S=S.biUnion (marks x) := by
    ext γ
    simp only [rankMarks,marks,mem_filter,mem_biUnion]
    exact ⟨fun ⟨ha,I,hI,hmark⟩=>⟨I,hI,ha,hmark⟩,fun ⟨I,hI,ha,hmark⟩=>⟨ha,I,hI,hmark⟩⟩
  rw [heq]
  calc
    _ ≤ ∑ I∈S,((marks x I).card:ℚ) := by
      exact_mod_cast (card_biUnion_le : (S.biUnion (marks x)).card≤_)
    _ ≤ ∑ I∈S,FP (rankPrice o) (fun k=>pN I k) :=
      sum_le_sum fun I hI=>parent_price x o I (hS I hI).1 (hS I hI).2.1 (hS I hI).2.2
    _ = _:= by
      simp only [FP,J2,mass,zCt,mul_sum]
      exact sum_comm
end
end qKfhfIb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qY7abfd
noncomputable section
open P6 (K p)
open P6_7_3 (Input Poles)
open qUrGXob (aSz NativeOK graphRate nativeRate onMark onCurves)
open cu (L qD)
open gT (Ambient kM)
open pI (by6)
open YY (bAG xg Si by9 aef a9E)
open private cag c2p ddj c0U b1I diE from ProximityPrize.SubmissionLower.G
open private mix mix_zero ePj from ProximityPrize.SubmissionLower.ZzWMDba
open Finset
open scoped Classical
def c1 :Prop :=
  ∀ (x :Input) (_P:Poles x) (T:zJe K) (J:znc kM)
    (Q:MvPolynomial (Fin 2) L) (H :ℕ),DescendedMarks x T J Q 2 H →
    (T.card:ℚ)≤16*(2*(Q.totalDegree :ℚ))+quadraticRate*H+2
def c2 :Prop :=
  ∀ (x :Input) (_P:Poles x) (T:zJe K) (J:znc kM)
    (Q:MvPolynomial (Fin 2) L) (e H g c W M:ℕ),DescendedMarks x T J Q e H →
    3≤e→e<55→NativeOK e g c W M →
    (T.card:ℚ)≤nativeSlope Q.totalDegree e*((e :ℚ)*Q.totalDegree) +
      nativeRate e g c W*H+e
private theorem rated_descended (h1 :c1) (h2 :c2)
    {x :Input} (P:Poles x) {T:zJe K} {J Q e H} (A:DescendedMarks x T J Q e H)
    (he :0<e) {d a b:ℚ} (hr :aSz d a b) (hd: (Q.totalDegree :ℚ)≤d)
    (direct : (T.card:ℚ)≤((p+1 :ℕ) :ℚ)*Q.totalDegree) :
    (T.card:ℚ)≤a*((e :ℚ)*Q.totalDegree)+b*H+e := by
  have ha :0≤a :=hr.1.trans ((le_max_left _ _).trans hr.2.2.1)
  have hH : (0:ℚ)≤H :=zqJ _
  have hE : (0:ℚ)≤e :=zqJ _
  have hmass :0≤(e :ℚ)*Q.totalDegree :=mul_nonneg hE (zqJ _)
  have hdir : (T.card:ℚ)≤graphRate e*((e :ℚ)*Q.totalDegree) := by
    rw [← mul_assoc,graphRate,div_mul_cancel₀ _ (Nat.cast_pos.mpr he : (0:ℚ)<e).ne']
    exact direct
  by_cases h:a<graphRate e
  · rcases hr.2.2.2.2 e he h with hb | hb | hb | hb
    · have heP:e<p:=(zCV e A.plane_pos).trans_lt A.seed_lt
      exact mix_zero ha h hH hE hdir (persistent he heP A) hb
    · obtain ⟨rfl,hb⟩:=hb
      exact mix_zero ha h hH hE hdir (linear A) hb
    · obtain ⟨rfl,ha₀,hb⟩:=hb
      exact mix ha₀ h hH hE hdir (h1 x P T J Q H A) hb
    · obtain ⟨he₃,g,c,W,M,hw,ha₀,hb⟩:=hb
      have hs :nativeSlope Q.totalDegree e≤nativeSlope d e := by
        unfold nativeSlope
        exact add_le_add (add_le_add
          (div_le_div_of_nonneg_right hd (mul_nonneg (by norm_num) hE)) le_rfl) le_rfl
      have he55:e<55:= by
        by_contra! hge
        have hq:graphRate e≤graphRate 55 :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num)
            (Nat.cast_le.mpr hge)
        exact (not_lt_of_ge (hq.trans ((le_max_right _ _).trans hr.2.2.1))) h
      have hone :=(h2 x P T J Q e H g c W M A he₃ he55 hw).trans
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hs hmass) le_rfl) le_rfl)
      exact mix ha₀ h hH hE hdir hone hb
  · exact hdir.trans ((mul_le_mul_of_nonneg_right (le_of_not_gt h) hmass).trans
      ((le_add_of_nonneg_right (mul_nonneg hr.2.2.2.1 hH)).trans (le_add_of_nonneg_right hE)))
private def aHl (x :Input) (I:znc Ambient) :zJe K :=
  x.Γ.filter (onMark x I)
private theorem fTy (h1 :c1) (h2 :c2)
    (x :Input) (P:Poles x) {I:znc Ambient} (geom:by6 I)
    {d a b:ℚ} (hr :aSz d a b) (hD: (aef I:ℚ)≤d) :
    ((aHl x I).card:ℚ)≤(a+1)*aef I+b*a9E I:= by
  let T:=aHl x I
  let D:=aef I
  let H :=a9E I
  have ha :0≤a :=hr.1.trans ((le_max_left _ _).trans hr.2.2.1)
  have hdP:D <p:= by exact_mod_cast hD.trans_lt hr.2.1
  have slice :bAG I:=⟨geom.1,geom.2.1,geom.2.2.1,geom.2.2.2.1⟩
  obtain ⟨f,hf,hI,hpos,hdeg⟩:=GK.proof I slice
  have hdegQ: (f.totalDegree :ℚ)≤D:=Nat.cast_le.mpr hdeg
  have hlabels : ∀ z∈T.image x.M.label,qD z f=0:= by
    intro z hz
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz
    apply c2p (mem_filter.mp hγ).2
    rw [hI]
    exact Ideal.mem_span_singleton_self f
  have hcard: (T.image x.M.label).card=T.card :=
    card_image_of_injective _ (fun _ _ h=>sub_left_inj.mp h)
  change (T.card:ℚ)≤(a+1)*D+b*H
  suffices h: (T.card:ℚ)≤a*D+b*H+D by
    calc _≤_:=h
         _ = _:= by ring
  by_cases hc:by9 (xg I)
  · obtain ⟨Q,hQ,hIQ⟩:=hc
    have hde :=b1I f hf.ne_zero Q (hI.symm.trans hIQ)
    obtain ⟨e,he,hcurve,hmass⟩:=ePj I Q slice geom.2.2.2.2 hQ hIQ
    have hmarks :DescendedMarks x T (Si I) Q e H :=
      ⟨filter_subset _ _,hcurve,hQ,hIQ,hde ▸ hpos,hmass.trans_lt hdP,
        fun _ hγ=>cag (mem_filter.mp hγ).2⟩
    have hdir :=ddj f hf.ne_zero (hdeg.trans_lt hdP)
      (T.image x.M.label) hlabels
    rw [hcard,hde] at hdir
    have htotal:=rated_descended h1 h2 P hmarks he hr
      ((show (Q.totalDegree :ℚ)≤D from hde ▸ hdegQ).trans hD) (by exact_mod_cast hdir)
    have hmassQ: (e :ℚ)*Q.totalDegree≤D:= by
      rw [mul_comm]
      exact_mod_cast hmass
    have heQ: (e :ℚ)≤D :=
      Nat.cast_le.mpr ((zCV e hmarks.plane_pos).trans hmass)
    exact htotal.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmassQ ha) le_rfl) heQ)
  · have hm:=c0U p f hf (hI ▸ hc) (T.image x.M.label) hlabels
    rw [hcard] at hm
    have hq: (T.card:ℚ)≤(f.totalDegree :ℚ)^2 := by exact_mod_cast hm
    have hfa : (f.totalDegree :ℚ)≤a :=(hdegQ.trans hD).trans
      ((le_max_left _ _).trans hr.2.2.1)
    calc
      _≤(f.totalDegree :ℚ)^2 :=hq
      _≤a*D:= by rw [pow_two]; exact mul_le_mul hfa hdegQ (zqJ _) ha
      _≤_:=le_add_of_nonneg_right (mul_nonneg hr.2.2.2.1 (zqJ _)) |>.trans
        (le_add_of_nonneg_right (zqJ _))
theorem of_children (h1 :c1) (h2 :c2) :qUrGXob.c3:= by
  intro x P C d a b hr hC
  have hs :onCurves x C=C.qv.biUnion (aHl x) := by
    ext γ
    constructor
    · intro h
      obtain ⟨hγ,I,hI,hm⟩:=mem_filter.mp h
      exact mem_biUnion.mpr ⟨I,hI,mem_filter.mpr ⟨hγ,hm⟩⟩
    · intro h
      obtain ⟨I,hI,hm⟩:=mem_biUnion.mp h
      exact mem_filter.mpr ⟨(mem_filter.mp hm).1,I,hI,(mem_filter.mp hm).2⟩
  have hsum : ∑ I∈C.qv,aef I=C.cost 0:=rfl
  have hsumH : ∑ I∈C.qv,a9E I=C.cost 1 :=rfl
  rw [hs]
  calc
    _ ≤ ∑ I∈C.qv,((aHl x I).card:ℚ) :=diE _ _
    _ ≤ ∑ I∈C.qv,((a+1)*aef I+b*a9E I) := by
      apply sum_le_sum
      intro I hI
      have hD:aef I≤C.cost 0 :=
        hsum ▸ single_le_sum (fun _ _=>zD0 _) hI
      exact fTy h1 h2 x P (C.geometric I hI) hr ((Nat.cast_le.mpr hD).trans hC)
    _ = _:= by simp only [sum_add_distrib,← mul_sum,← zCt,hsum,hsumH]
end
end qY7abfd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qrrIula
noncomputable section
open Polynomial
open scoped Classical
open P6_7_4 (wordLift)
open q6nKpZc (Input I0 Pass)

open P5_7_2 (A Ls stages movingOrder O2)
open q7F2qKe (agA chosen_mem afterFree a3D aHp SS)
open q3soobb (after_free cqz shapes_ok terminal_ok selected_ok cut_shape_bounds)
open cu (Jet Shape rD)
open DP (d3r)
open gT (Ambient iJ aNB)
open pI (oU dot)
variable {b u del M Γ F} {x : @Input b u del M Γ F}
private theorem b2N {s :Shape} {I:znc Ambient}
    (hpos :0<s.m*A) (hf : ¬ agA x.banks s I) :
    ∃ P:Jet,oU P s∧iJ P∉I ∧
      ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0:= by
  unfold agA at hf
  push Not at hf
  obtain ⟨P,hP,hprop⟩:=hf
  exact ⟨P,d3r x.crt (wordLift M) hP,hprop,
    qCReOzb.aS3 x (by unfold O2; omega) hP⟩
private theorem d1m {s :Ls} {P:Jet}
    (hb:s.free.J≤ s.free.B) (hc:s.moving.J≤ s.moving.B)
    (hP:oU P s.free∨oU P s.moving) :oU P (a3D s) := by
  have ha :s.free.B≤(a3D s).B :=
    (zxt hb).symm.trans_le
      (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
  have hd:s.moving.B≤(a3D s).B :=
    (zxt hc).symm.trans_le
      (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
  intro j i h
  rcases hP with hp | hp
  · obtain ⟨hg,hj,hu⟩:=hp j i h
    exact ⟨hg.trans ha,hj.trans (le_max_left _ _),hu.trans (le_max_left _ _)⟩
  · obtain ⟨hg,hj,hu⟩:=hp j i h
    exact ⟨hg.trans hd,hj.trans (le_max_right _ _),hu.trans (le_max_right _ _)⟩
private theorem d59 {s :Ls} (hs :s∈stages b) {I:znc Ambient}
    (hf : ¬ (agA x.banks s.free I∧agA x.banks s.moving I ∧
      aFX.aTw (x.donors.staged s hs).free.jet (x.donors.staged s hs).moving.jet I)) :
    ∃ P:Jet,oU P (a3D s)∧iJ P∉I ∧
      ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0:= by
  let pair :=x.donors.staged s hs
  obtain ⟨ga,gb⟩:=shapes_ok b s hs
  have liftCaps {P:Jet} (h:oU P s.free∨oU P s.moving) :
      oU P (a3D s) :=d1m ga.2.2.1 gb.2.2.1 h
  by_cases hP:agA x.banks s.free I
  · by_cases hQ:agA x.banks s.moving I
    · have htest : ¬ aFX.aTw pair.free.jet pair.moving.jet I :=
        fun h=>hf ⟨hP,hQ,h⟩
      unfold aFX.aTw at htest
      push Not at htest
      obtain ⟨f,_,_,_,hdiv,hmem,g,a,hclear,hproper⟩:=htest
      have hcaps :=d3r x.crt (wordLift M) (chosen_mem pair.moving)
      have hG:=YZ.bWO pair.moving.nonzero hcaps gb.2.1 hdiv hclear
      refine ⟨YZ.alD g,liftCaps (Or.inr hG),hproper,?_⟩
      intro γ _ hγ
      apply YZ.bWP hclear
      have hz :=RingHom.mem_ker.mp (hγ hmem)
      simpa only [aNB,rD,eval₂_C,coe_eval₂RingHom,cu.yq] using hz
    · obtain ⟨P,hcaps,hproper,hzero⟩:=b2N (x :=x) gb.1 hQ
      exact ⟨P,liftCaps (Or.inr hcaps),hproper,fun γ hγ _=>hzero γ hγ⟩
  · obtain ⟨P,hcaps,hproper,hzero⟩:=b2N (x :=x) ga.1 hP
    exact ⟨P,liftCaps (Or.inl hcaps),hproper,fun γ hγ _=>hzero γ hγ⟩
private theorem failed_test {j I} (hj:0<j) (h : ¬ Pass x j I) :
    ∃ P:Jet,oU P (aHp b j)∧iJ P∉I ∧
      ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0:= by
  rw [Pass,ite_eq_right (Nat.ne_of_gt hj)] at h
  unfold aHp
  by_cases hf :j<afterFree b
  · rw [ite_eq_left hf] at h ⊢
    have hs :=cqz ((after_free b) ▸ hf)
    obtain ⟨P,hc,hp,hz⟩:=b2N (x :=x) (shapes_ok b _ hs).1.1 h
    exact ⟨P,hc,hp,fun γ hγ _=>hz γ hγ⟩
  · rw [ite_eq_right hf] at h ⊢
    cases he : (movingOrder b)[j-afterFree b]? with
    | none =>
      rw [he] at h
      obtain ⟨P,hc,hp,hz⟩:=b2N (x :=x) (terminal_ok b).1 h
      exact ⟨P,hc,hp,fun γ hγ _=>hz γ hγ⟩
    | some n =>
      rw [he] at h
      have hs :=cqz (selected_ok b n (List.mem_iff_getElem?.mpr ⟨_,he⟩)).2.1
      exact d59 (x :=x) hs fun hp=>h ⟨hs,hp⟩
theorem proof :qkrKkqa.c2 := by
  intro b _ u del M Γ F x j _ hj I ha h
  obtain ⟨P,hc,hp,hz⟩:=failed_test hj h
  obtain ⟨Q,hcost,hcover⟩ :=
    qQNoJ5c.bKS F (aHp b j) (cut_shape_bounds hj).1 ha hc hp
  refine ⟨Q,⟨fun i => ?_,fun γ hγ hm=>hcover γ hγ hm (hz γ hγ hm)⟩⟩
  simpa only [SS,TD.FP,dot,zCt,z2R]
    using (Nat.cast_le (α:=ℚ)).mpr (hcost i)
end
end qrrIula
end
section
set_option autoImplicit true
namespace qCImdUb
theorem proof :qNUt03b.c3 :=
  q8iJfvb.of_children qOj34lc.proof qJ69aaa.proof
    (qnyP9Da.of_children q3zqDZc.proof qJQ0Sxd.proof
      qDhaEec.proof) qU1uHGd.proof
end qCImdUb
end
