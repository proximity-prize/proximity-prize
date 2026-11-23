import ProximityPrize.SubmissionLower.ZTNySHa
import ProximityPrize.SubmissionLower.Z1xfoqa
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qQCjxhb
noncomputable section
open Polynomial
open P6 (K I dw)
open P6_7 (RectTail)
open P6_7_2
open P6_7_2_3 (terminalPass)
open cu (L FX Jet Shape j9)
open DP
open gT (Ambient iJ aci aNB)
open scoped Polynomial BigOperators
def c1 :Prop :=
  ∀ {h:ℕ} (D:jF h) (Crt:zG D) (word:I→L)
    (s :Shape) (W:ℕ) (Q:Source),Q∈complete Crt word s W →
    (∀ i k,(D.block i).eval (ad0 k)≠0) →
    ∀ (z :K) (S:K[X]),aKF D z S →
      (j9 S).natDegree≤131071+h →
      ∀ (T:Finset I),T.card=dw →
        (∀ k∈T,(j9 S).eval (ad0 k)=word k) →
        ∀ (U:L[X]),U.natDegree≤1 →
          ∀ n,0<n→n≤2→W+(dw-131071+1+h)*n<s.m*dw →
            (line (iJ (U4 Q)) z S (inc (mL D T*U))
              (inc (mL D T*U).derivative)).coeff n=0
def c2 :Prop :=
  ∀ (F:Ambient) (z :K) (S:K[X]) (D:L[X]),D ≠0 →
    ∀ (a :Fin 4 →₀ ℕ),a 0=0→a 1=0→0<a 2+a 3→a 2+a 3≤2 →
      (∀ (U:L[X]),U.natDegree≤1 →
        (line F z S (inc (D*U)) (inc (D*U).derivative)).coeff (a 2+a 3)=0) →
      (jA.translate (point z S) F).coeff a=0
private theorem tx_zero (z :K) (S:K[X]) (F:Ambient) :
    (jA.translate (point z S) F).coeff 0=aci z S F:= by
  have he : (MvPolynomial.constantCoeff.comp
      (jA.translate (point z S)) :Ambient →+* FX)=aci z S:= by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [jA.translate,aci]
    · intro j
      simp [jA.translate,aci,point]
  exact RingHom.congr_fun he F
private theorem toJet_smul (r :FX) (G:Jet) :iJ (r•G)=MvPolynomial.C r*iJ G:= by
  rw [Algebra.smul_def,map_mul]
  congr 1
  change iJ (C (C (MvPolynomial.C r)))= _
  simp [iJ,gT.A7,gT.pZ,gT.oi]
private theorem pure (h1 :c1) (h2 :c2) {b:RectTail} {x :Input b} (P:Poles x)
    (s :Shape) (W:ℕ) (G:Jet) (hG:G∈P.rows s W) {γ:K} (hγ:γ∈x.Γ)
    (a :Fin 4 →₀ ℕ) (h0:a 0=0) (h₁:a 1=0)
    (ht:a 2+a 3≤2) (hw:W+(dw-131071+1+x.h)*(a 2+a 3)<s.m*dw) :
    (jA.translate (point (x.M.label γ) (x.F.scalar γ)) (iJ G)).coeff a=0:= by
  classical
  let z :=x.M.label γ
  let S:=x.F.scalar γ
  let B:=x.F.mark γ hγ
  have hd: (j9 S).natDegree≤131071+x.h :=
    natDegree_map_le.trans (P6_7.aic x.F hγ)
  have hh (k) (hk :k∈B.bad.support) : (j9 S).eval (ad0 k)=x.word k := by
    rw [j9,ad0,Polynomial.eval_map,Polynomial.eval₂_hom,B.scalar_hits k hk]
  by_cases ha :0<a 2+a 3
  · obtain ⟨T,hT,hcard⟩:=Finset.exists_subset_card_eq B.bad.dw
    have hD:mL P.D T≠0:=mul_ne_zero ((P.D.monic 0).mul (P.D.monic 1)).ne_zero
      (gR.S8 ad0 T).ne_zero
    refine h2 _ z S _ hD a h0 h₁ ha ht fun U hU => ?_
    change G∈Submodule.span FX _ at hG
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨Q,hQ,rfl⟩:=hG
      exact h1 P.D P.crt x.word s W Q hQ P.nodes z S (P.marks γ hγ) hd T hcard
        (fun k hk=>hh k (hT hk)) U hU _ ha ht hw
    | zero=>simp [line]
    | add G H _ _ hg hh =>
      simp only [line,map_add,Polynomial.coeff_add] at hg hh ⊢
      rw [hg,hh,add_zero]
    | smul r G _ hg =>
      rw [toJet_smul]
      simp only [line] at hg ⊢
      rw [map_mul,MvPolynomial.eval₂Hom_C,Polynomial.coeff_C_mul,hg,mul_zero]
  · have hz :a=0:= by
      ext j
      fin_cases j <;> simp_all
    rw [hz,tx_zero,aNB]
    exact atp.dPr P.crt x.word P.nodes z S (P.marks γ hγ) hd B.bad.support
      B.bad.dw hh s W (by omega) G hG
private theorem budget {b:RectTail} (x :Input b) :
    2*x.h≤dw-131071+1+x.h ∧
    2*x.h*(Bs b).dI<(Bs b).terminal.m*dw:= by
  have hb:x.h≤2406:= by
    have hh:=x.kA.2
    have hhi:b.kA.hi≤2406:= by cases b <;> decide
    change (x.M.iF:ℤ)≤(b.kA.hi:ℤ) at hh
    change x.M.iF.toNat≤2406
    omega
  constructor
  · change 2*x.h≤48757+x.h
    omega
  · refine (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hb)).trans_lt ?_
    cases b <;> decide
theorem of_children (h1 :c1) (h2 :c2) :P6_7_2_3.c5:= by
  intro b x P Q hr hn
  unfold terminalPass at hn
  push Not at hn
  obtain ⟨G,hG,hp⟩:=hn
  refine ⟨⟨iJ G,hp,fun _ ha=>caps P hG ha,?_⟩⟩
  intro γ hγ a ha
  let s :=rectShape b (full b)
  let W:=rectCutoff b x.h
  let d:Fin 4 →₀ ℕ:=Finsupp.single 2 (a 2)+Finsupp.single 3 (a 3)
  let Cst:=dw-131071+1+x.h
  obtain ⟨hgap,hB⟩:=budget x
  have hg:=toEvaluated P (full b) W hG
  have hseed :=atp.d3s P.crt x.word
    (atp.d3s P.crt x.word hg 0 (a 0)) 1 (a 1)
  rw [eval_hasse,← seed_extract]
  have ha' : a 0+a 1+(a 2+a 3)≤(Bs b).paidOrder := by
    rw [Fin.sum_univ_four] at ha
    omega
  have hm:Cst*(a 0+a 1+(a 2+a 3))≤2*x.h*(Bs b).dI :=
    (Nat.mul_le_mul_left Cst ha').trans (by rw [Nat.mul_comm Cst]; exact hr)
  have h0:2*x.h*a 0≤Cst*a 0:=Nat.mul_le_mul_right (a 0) hgap
  have h1' : 2*x.h*a 1≤Cst*a 1 :=Nat.mul_le_mul_right (a 1) hgap
  have hcost:2*x.h*a 0+2*x.h*a 1+Cst*(a 2+a 3)≤2*x.h*(Bs b).dI:= by
    refine le_trans ?_ hm
    simp only [Nat.mul_add]
    exact Nat.add_le_add_right (Nat.add_le_add h0 h1') _
  have hd2 :d 2=a 2 := by simp [d]
  have hd3:d 3=a 3:= by simp [d]
  have hpkt: (Bs b).paidOrder≤2 := by cases b <;> decide
  refine pure h1 h2 P s _ _ hseed hγ d (by simp [d]) (by simp [d]) ?_ ?_
  · rw [hd2,hd3]
    omega
  rw [hd2,hd3]
  simp only [W,rectCutoff,cutoff]
  change (Bs b).terminal.m*dw-1-2*x.h*(Bs b).dI+
    2*x.h*a 0+2*x.h*a 1+Cst*(a 2+a 3)<(Bs b).terminal.m*dw
  omega
end
end qQCjxhb
end
section
set_option autoImplicit true
namespace qVWQWJa
noncomputable section
open Finset P6_7_2_3
open P6_7 (RectTail)

open P5_7_1 (wD)
open cu (Jet)
open TD (FP dYl a3x)
open scoped Classical BigOperators
def c1 :Prop :=
  ∀ b o i,FreeOK b o i ((bgt b).freeSeed o i) ((bgt b).freeHeight o i)
def c2 :Prop :=
  ∀ b o,TerminalOK b o ((bgt b).terminalZ o) ((bgt b).terminalT o)
    ((bgt b).terminalHeight o)
def c3:Prop :=
  ∀ b o s k,(priceAt (bgt b) o s+bAY b s) k≤a3D b o s k
private theorem bY8 (b:RectTail) (n:ℕ) (j:Fin 3) :
    iL b n j≤ iL b (n+1) j:=le_max_left _ _
private theorem credit_sum (b:RectTail) (o:Origin) (j:Fin 3) :
    (∑ i:Origin,if i≤o then (a4Q b i j:ℚ) else 0)=(iL b (o.val+1) j:ℚ) := by
  have h:=Fin.sum_Iic_sub o (fun i:Fin 15=>(iL b i.val j:ℚ))
  change (∑ i∈Iic o,((iL b (i.val+1) j:ℚ)-(iL b i.val j:ℚ))) =
    (iL b (o.val+1) j:ℚ) - 0 at h
  rw [← sum_filter]
  have hf : (univ.filter fun i:Origin=>i≤o)=Iic o:= by ext i; simp
  rw [hf]
  simpa only [a4Q,Nat.cast_sub (bY8 b _ j),sub_zero] using h
private theorem unit_le (b:RectTail) (o:Origin) (j:Fin 3) :
    (unitN b o j:ℚ) ≤ ∑ i:Origin,if i≤o then (a4Q b i j:ℚ) else 0:= by
  rw [credit_sum]
  apply Nat.cast_le.mpr
  change unitN b o j≤ max _ (if h:o.val<14 then unitN b ⟨o.val,h⟩ j else 0)
  exact (le_max_right _ _:unitN b o j≤ max (iL b o.val j) _).trans_eq
    (by rw [dite_eq_left o.isLt])
private theorem dot_mixed (b:RectTail) (o:Origin) (v :Fin 3→ℕ) :
    FP (residue b o) (kK v (originShape b o)) =
      ∑ j,(unitN b o j:ℚ)*(v j:ℚ) := by
  simp only [FP,kK,unitN,residue,Nat.cast_sum,Nat.cast_mul,mul_sum,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring
private theorem pay_factor {b:RectTail} (B:aAU b) (f :Jet) (hf :f∈B.factors) :
    (lineCharge b f (B.line f) :ℚ)+(∑ s,FP (residue b (B.origin f)) (B.arL f s)) ≤
      ∑ j,(unitN b (B.origin f) j:ℚ)*(wD f j:ℚ) := by
  have hs :
      (∑ s,FP (residue b (B.origin f)) (B.arL f s)) ≤
        FP (residue b (B.origin f)) (stock b (B.origin f) f (B.line f)) := by
    simp only [FP]
    rw [sum_comm]
    simp only [← mul_sum]
    exact a3x (fun k=>Nat.cast_nonneg _) (B.initial f hf)
  refine (add_le_add le_rfl hs).trans ?_
  cases hl:B.line f with
  | false =>
    simpa only [hl,lineCharge,stock,anZ,Bool.false_eq_true,ite_false,Nat.cast_zero,zero_add]
      using (dot_mixed b (B.origin f) (wD f)).le
  | true =>
    obtain ⟨ho,hj,_⟩:=B.line_pos f hf hl
    have hsp (j:Fin 3) :wD f j≤ introCap b last j:= by
      have hmem:f∈B.factors.filter (fun f=>last≤B.origin f) :=
        mem_filter.mpr ⟨hf,ho ▸ le_rfl⟩
      exact (single_le_sum (fun g _=>Nat.zero_le (wD g j)) hmem).trans (B.nested last j)
    simpa only [hl,ho,lineCharge,stock,anZ,ite_true] using lineAbsorbs b (wD f) hsp hj
private theorem aNI {b:RectTail} (B:aAU b) :
    (∑ f∈B.factors,((lineCharge b f (B.line f) :ℚ) +
      ∑ s,FP (residue b (B.origin f)) (B.arL f s)))≤(factorBook b:ℚ) := by
  calc
    _ ≤ ∑ f∈B.factors,∑ j,(∑ i:Origin,if i≤B.origin f then (a4Q b i j:ℚ) else 0) *
          (wD f j:ℚ) :=
      sum_le_sum fun f hf=>(pay_factor B f hf).trans
        (sum_le_sum fun j _=>mul_le_mul_of_nonneg_right (unit_le b (B.origin f) j) (Nat.cast_nonneg _))
    _ = ∑ j:Fin 3,∑ i:Origin,∑ f∈B.factors,
        (if i≤B.origin f then (a4Q b i j:ℚ) else 0)*(wD f j:ℚ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      simp only [sum_mul]
      exact sum_comm
    _ = ∑ i:Origin,∑ j:Fin 3,(a4Q b i j:ℚ) *
        (∑ f∈B.factors.filter (fun f=>i≤B.origin f),(wD f j:ℚ)) := by
      rw [sum_comm]
      simp only [sum_filter,mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro f _
      by_cases h:i≤B.origin f <;> simp [h]
    _≤_:= by
      simp only [factorBook,Nat.cast_sum,Nat.cast_mul]
      refine sum_le_sum fun i _=>sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (a4Q b i j))
      simpa only [Nat.cast_sum] using (Nat.cast_le (α:=ℚ)).mpr (B.nested i j)
private theorem terminal_bound {b:RectTail} (B:aAU b) :
    (∑ f∈B.factors,FP (terminalDual b (B.origin f)) (B.arL f terminalStop)) ≤
      terminalBook b:= by
  unfold terminalBook
  rw [← sum_fiberwise B.factors B.origin]
  apply sum_le_sum
  intro o _
  calc
    _ = ∑ f∈B.factors.filter (fun f=>B.origin f=o),
          FP (terminalDual b o) (B.arL f terminalStop) := by
      exact sum_congr rfl fun f hf=> by rw [(mem_filter.mp hf).2]
    _=FP (terminalDual b o) (fun k =>
          ∑ f∈B.factors.filter (fun f=>B.origin f=o),B.arL f terminalStop k) := by
      simp only [FP,mul_sum]
      exact sum_comm
    _≤_:=a3x (fun k=>Nat.cast_nonneg _) (B.finalPool o)
private theorem sum_envelope {b:RectTail} (B:aAU b) (f :Jet) :
    (∑ s,FP (a3D b (B.origin f) s) (B.arL f s)) =
      (∑ s,FP (residue b (B.origin f)) (B.arL f s)) +
      FP (terminalDual b (B.origin f)) (B.arL f terminalStop) := by
  simp only [FP,a3D,add_mul,sum_add_distrib]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  simp only [ite_mul,zero_mul,sum_ite_eq',mem_univ,ite_true]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P6_7_2_3.c7:= by
  intro b
  refine ⟨{ toRates :=bgt b,freeOK :=h1 b,terminalOK :=h2 b,Az := ?_ }⟩
  intro B
  have h :
      (∑ f∈B.factors,((lineCharge b f (B.line f) :ℚ) +
        ∑ s,FP (priceAt (bgt b) (B.origin f) s+bAY b s) (B.arL f s))) ≤
      ∑ f∈B.factors,((lineCharge b f (B.line f) :ℚ) +
        ∑ s,FP (a3D b (B.origin f) s) (B.arL f s)) :=
    sum_le_sum fun f hf=>add_le_add le_rfl
      (sum_le_sum fun s _=>dYl (B.nonneg f hf s) (h3 b (B.origin f) s))
  simp only [sum_envelope,← add_assoc,sum_add_distrib] at h
  have hf :=aNI B
  have ht:=terminal_bound B
  have hb:=booksCovered b
  simp only [sum_add_distrib] at hf ⊢
  linarith only [h,hf,ht,hb]
end
end qVWQWJa
end
