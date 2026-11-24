import ProximityPrize.SubmissionLower.ZzQsYjc
import ProximityPrize.SubmissionLower.Z3e8uLd
import ProximityPrize.SubmissionLower.ZNc08Oa
set_option Elab.async false
open _root_ renaming Nat.cast_nonneg → zqJ, Nat.cast_sub → zjK, Nat.sub_pos_of_lt → zuI
set_option autoImplicit true
namespace q8ADoQd
noncomputable section
open P5 (K I node p blockLength)
open P5_7 (FarBand farAgreement)
open P5_7_5 (wX gap sheetCut alO)

open DQ (Ag Wh)
open axI (azO aVj dcv c3X)
open Finset Polynomial ProximityPrize.Benchmark
private structure OF (w:I→K) (U:Finset K) (s :K→K[X]) (d:ℕ) :Prop where
 distinct :Set.InjOn s (U:Set K)
 degree : ∀ γ∈U,(s γ).natDegree≤d
 lg : ∀ γ∈U,∃ B:Finset I,farAgreement≤B.card ∧ ∀ i∈B,(s γ).eval (node i)=w i
private theorem bf9 {w U s d} (hw:OF w U s d) (hU:1<U.card) :
  (azO w U s).card≤d:= by
 obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp hU
 let P:=s a - s b
 have hp:P≠0:=sub_ne_zero.mpr fun eq=>hab (hw.distinct ha hb eq)
 refine (gR.kL.agd node IRSProfile.domain.injective P hp _ ?_).trans
  ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
 intro i hi
 change ((s a)-(s b)).eval (node i)=0
 rw [Polynomial.eval_sub,aVj ha hi,aVj hb hi,sub_self]
private theorem bNu {w U s d} (hw:OF w U s d) (D:ℕ)
   (hsection : ∀ i:I,(∃ γ∈U,(s γ).eval (node i)≠w i) →
     (U.filter fun γ=>(s γ).eval (node i)=w i).card≤D) :
   (farAgreement - (azO w U s).card)*U.card ≤
     (blockLength-(azO w U s).card)*D:= by
 classical
 let sites :=azO w U s
 let nodes :Finset I:=univ \ sites
 let lg (γ:K) :=nodes.filter fun i=>(s γ).eval (node i)=w i
 let occ (i:I) :=U.filter fun γ=>(s γ).eval (node i)=w i
 have hhit (γ:K) (hγ:γ∈U) :farAgreement - sites.card≤(lg γ).card:= by
   obtain ⟨B,hB,hvals⟩:=hw.lg γ hγ
   let good:Finset I:=univ.filter fun i=>(s γ).eval (node i)=w i
   have hgood:farAgreement≤good.card :=
     hB.trans (card_le_card fun i hi=>mem_filter.mpr ⟨mem_univ _,hvals i hi⟩)
   have hZG:sites⊆good:= fun i hi=>mem_filter.mpr ⟨mem_univ _,aVj hγ hi⟩
   have heq :lg γ=good \ sites := by
     ext i
     simp only [lg,nodes,good,mem_filter,mem_sdiff,mem_univ,true_and]
     exact and_comm
   rw [heq,card_sdiff_of_subset hZG]
   exact Nat.sub_le_sub_right hgood _
 have hnodes :nodes.card=blockLength - sites.card:= by
   rw [card_sdiff_of_subset (subset_univ sites),card_univ,IRSProfile.card_index]
 calc
   _ = ∑ γ∈U,(farAgreement - sites.card) := by rw [sum_const,smul_eq_mul,Nat.mul_comm]
   _ ≤ ∑ γ∈U,(lg γ).card:=sum_le_sum hhit
   _ = ∑ i∈nodes,(occ i).card:= by simp only [lg,occ,card_filter]; rw [sum_comm]
   _ ≤ ∑ _i∈nodes,D:= by
     apply sum_le_sum
     intro i hi
     apply hsection i
     by_contra! h
     exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
   _ = _:= by rw [sum_const,smul_eq_mul,hnodes]
private def rho (s :ℕ) :ℚ :=
 ((blockLength - s :ℕ) :ℚ)/((farAgreement - s :ℕ) :ℚ)
private abbrev aaM:ℚ:=(blockLength:ℚ)/farAgreement
private theorem weights {s d:ℕ} (hs :s≤d) (hd:d<farAgreement)
   (haux :rho d≤aaM*d) :
   rho s≤ rho d∧rho s*(max 1 (d-s) :ℕ)≤aaM*d:= by
 have hAN :farAgreement≤blockLength:= by decide
 have hsA:=hs.trans_lt hd
 have hdN :=hd.le.trans hAN
 have hsN :=hs.trans hdN
 have hAs : (0:ℚ)<(farAgreement:ℚ) - s :=sub_pos.mpr (by exact_mod_cast hsA)
 have hAd: (0:ℚ)<(farAgreement:ℚ) - d:=sub_pos.mpr (by exact_mod_cast hd)
 have hmain:rho s≤ rho d:= by
   unfold rho
   rw [zjK hsN,zjK hsA.le,zjK hdN,zjK hd.le]
   apply (div_le_div_iff₀ hAs hAd).mpr
   have h:=mul_nonneg (sub_nonneg.mpr (show (s :ℚ)≤d by exact_mod_cast hs))
     (sub_nonneg.mpr (show (farAgreement:ℚ)≤blockLength by exact_mod_cast hAN))
   nlinarith only [h]
 refine ⟨hmain,?_⟩
 by_cases heq :s=d
 · subst s
   simpa using haux
 have hpos :1≤d - s := by omega
 rw [max_eq_right hpos]
 have hden: (0:ℚ)<(farAgreement:ℚ) := by exact_mod_cast (by decide :0<farAgreement)
 have hfrac: ((d-s :ℕ) :ℚ)/((farAgreement-s :ℕ) :ℚ)≤(d:ℚ)/farAgreement:= by
   rw [zjK hs,zjK hsA.le]
   apply (div_le_div_iff₀ hAs hden).mpr
   have h:=mul_nonneg (zqJ s : (0:ℚ)≤ s) hAd.le
   nlinarith only [h]
 calc
   _=((blockLength-s :ℕ) :ℚ)*(((d-s :ℕ) :ℚ)/((farAgreement-s :ℕ) :ℚ)) := by
     unfold rho
     ring
   _≤(blockLength:ℚ)*((d:ℚ)/farAgreement) :=
     mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
   _=aaM*d:= by ring
private theorem bu7 {d:ℕ} (hl:131071≤d) (hh:d≤135870) :
  rho d≤aaM*d:= by
 have hdA:d<farAgreement:=hh.trans_lt (by decide)
 have hdN :d≤blockLength:=hh.trans (by decide)
 have hrho:rho d≤17:= by
  unfold rho
  have hp: (0:ℚ)<((farAgreement - d:ℕ) :ℚ) := by exact_mod_cast zuI hdA
  apply (div_le_iff₀ hp).mpr
  rw [zjK hdN,zjK hdA.le]
  change (262144 :ℚ) - d≤17*((179779:ℚ) - d)
  have hQ: (d:ℚ)≤135870:= by exact_mod_cast hh
  linarith only [hQ]
 have hDensity :1≤aaM:= by
  apply (le_div_iff₀ (show (0:ℚ)<(farAgreement:ℚ) by positivity)).mpr
  rw [one_mul]
  exact_mod_cast (by decide :farAgreement≤blockLength)
 exact hrho.trans (calc
  (17:ℚ)≤(d:ℚ) := by exact_mod_cast (show 17≤d by omega)
  _=1*(d:ℚ) :=(one_mul _).symm
  _≤aaM*d:=mul_le_mul_of_nonneg_right hDensity (zqJ _))
private theorem gAN {g:ℕ} (hg:0<g) :
  (Ag g:ℚ)=2*(g:ℚ) - 1 := by
 unfold Ag
 rw [zjK (by omega)]
 push_cast
 rfl
private theorem ceY {n g H d:ℕ} {U:Finset K} {s :K→Polynomial K} {w}
   (A:DQ.bk0 U s g H n) (hw:OF w U s d)
   (hg:0<g) (hl:131071≤d) (hh:d≤135870) :
   (U.card:ℚ)≤(2*aaM*d*(Ag g:ℚ)+rho d)*H+1 := by
 have hbound:0≤(2*aaM*d*(Ag g:ℚ)+rho d)*(H :ℚ) := by
   unfold rho
   positivity
 by_cases hc:U.card≤1
 · have h: (U.card:ℚ)≤1 := by exact_mod_cast hc
   linarith only [h,hbound]
 let sites :=azO w U s
 let t:=max 1 (d-sites.card)
 have hd:d<farAgreement:=hh.trans_lt (by decide)
 have hs :sites.card≤d:=bf9 hw (by omega)
 have ht:0<t:=(by decide :0<1).trans_le (le_max_left _ _)
 have htp:t<p:=(max_le (by omega :1≤d) (Nat.sub_le _ _)).trans_lt
   (hh.trans_lt (by decide))
 have hdt:d≤ sites.card+t:= by
   have h:=le_max_right 1 (d-sites.card)
   omega
 obtain ⟨C,hreconstruct⟩:=c3X sites w hdt htp hg A.equation A.equation_degree
 let D:=Ag t*(g*H)+Wh t g*H
 have hsection :=dcv (w:=w) A ht hw.distinct C fun γ hγ =>
   hreconstruct _ _ (hw.degree γ hγ) (fun _ hi=>aVj hγ hi) (A.root γ hγ) (A.simple γ hγ)
 have hinc: ((farAgreement - sites.card:ℕ) :ℚ)*U.card≤((blockLength - sites.card:ℕ) :ℚ)*D:= by
   exact_mod_cast bNu hw D hsection
 have hden: (0:ℚ)<((farAgreement - sites.card:ℕ) :ℚ) := by
   exact_mod_cast zuI (hs.trans_lt hd)
 have hcard: (U.card:ℚ)≤ rho sites.card*(D:ℚ) := by
   rw [rho,div_mul_eq_mul_div]
   apply (le_div_iff₀ hden).mpr
   calc
     _=((farAgreement - sites.card:ℕ) :ℚ)*U.card:=mul_comm _ _
     _≤_:=hinc
 obtain ⟨hρ,hρt⟩:=weights hs hd (bu7 hl hh)
 have hρb:rho sites.card*(Ag t:ℚ)≤2*aaM*d:= by
   have hb: (Ag t:ℚ)≤2*(t:ℚ) := by
     exact_mod_cast (Nat.sub_le (2*t) 1 :Ag t≤2*t)
   have hρ0:0≤ rho sites.card:=div_nonneg (zqJ _) (zqJ _)
   have h:=mul_le_mul_of_nonneg_left hb hρ0
   nlinarith only [h,hρt]
 have hsum:g+(g - 1)=Ag g:= by unfold Ag; omega
 have hD:D =(Ag t*Ag g+1)*H := by
   rw [← hsum]
   dsimp [D,Wh]
   ring
 refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
 calc
   _=(rho sites.card*(Ag t:ℚ)*(Ag g:ℚ)+rho sites.card)*H := by
     rw [hD]
     push_cast
     ring
   _≤_:=mul_le_mul_of_nonneg_right
     (add_le_add (mul_le_mul_of_nonneg_right hρb (zqJ _)) hρ) (zqJ _)
private abbrev beta (hi:ℕ) :ℚ:=((blockLength - farAgreement:ℕ) :ℚ)/gap hi
private theorem highDegree_nonneg (hi:ℕ) :0≤2*(wX hi:ℚ) - 1 := by
 have h: (1 :ℚ)≤wX hi:= by exact_mod_cast (show 1≤131071+hi by omega)
 linarith only [h]
private theorem beta_nonneg (hi:ℕ) :0≤beta hi :=
 div_nonneg (zqJ _) (zqJ _)
private theorem curveUnit_eq (hi g:ℕ) :
  alO hi g=(1+beta hi*(2*(wX hi:ℚ) - 1))*(2*(g:ℚ) - 1)+beta hi:= by
 unfold alO beta
 ring
private theorem curveSlope_nonneg (hi:ℕ) :0≤1+beta hi*(2*(wX hi:ℚ) - 1) :=
 add_nonneg zero_le_one (mul_nonneg (beta_nonneg hi) (highDegree_nonneg hi))
theorem curveUnit_nonneg (hi:ℕ) {g:ℕ} (hg:0<g) :0≤alO hi g:= by
 rw [curveUnit_eq]
 have h: (1 :ℚ)≤g:= by exact_mod_cast hg
 exact add_nonneg (mul_nonneg (curveSlope_nonneg hi) (by linarith only [h])) (beta_nonneg hi)
theorem curveUnit_mono (hi:ℕ) {g q:ℕ} (h:g≤q) :alO hi g≤alO hi q:= by
 rw [curveUnit_eq,curveUnit_eq]
 have hq: (g:ℚ)≤q:= by exact_mod_cast h
 have hstep:2*(g:ℚ) - 1≤2*(q:ℚ) - 1 := by linarith only [hq]
 exact add_le_add (mul_le_mul_of_nonneg_left hstep (curveSlope_nonneg hi)) le_rfl
private theorem small_hi {b:FarBand} (hq:sheetCut b≠0) :
  b.row.hi=3999∨b.row.hi=4799:= by
 cases b <;> first | exact Or.inl rfl | exact Or.inr rfl | exact False.elim (hq rfl)
private theorem rate_le {hi g:ℕ} (hhi:hi=3999∨hi=4799) (hg:0<g) :
   (1+2*aaM*(wX hi:ℚ))*(2*(g:ℚ) - 1)+rho (wX hi) ≤
     alO hi g:= by
 have hb: (9/5:ℚ)≤beta hi:= by
   rcases hhi with rfl | rfl
   · change (9/5:ℚ)≤82365/44709
     norm_num
   · change (9/5:ℚ)≤82365/43909
     norm_num
 have hLambda :aaM≤(3/2 :ℚ) := by
   change (262144 :ℚ)/ 179779≤3/2
   norm_num
 have hd: (5:ℚ)≤wX hi:= by exact_mod_cast (show 5≤131071+hi by omega)
 have hβd:=mul_le_mul_of_nonneg_right hb (highDegree_nonneg hi)
 have hLambdad:=mul_le_mul_of_nonneg_right hLambda (zqJ (α:=ℚ) (wX hi))
 have h2 :=mul_le_mul_of_nonneg_left hLambdad (show (0:ℚ)≤2 by norm_num)
 rw [← mul_assoc,← mul_assoc,show (2 :ℚ)*(3/2)=3 by norm_num] at h2
 have hcoef :1+(1+2*aaM*(wX hi:ℚ)) ≤
     1+beta hi*(2*(wX hi:ℚ) - 1) := by
   apply add_le_add le_rfl
   calc
     _≤1+3*(wX hi:ℚ) :=add_le_add le_rfl h2
     _≤(9/5:ℚ)*(2*(wX hi:ℚ) - 1) := by linarith only [hd]
     _≤_:=hβd
 have hρ:rho (wX hi)=1+beta hi:= by
   have hgap:0<gap hi:= by rcases hhi with rfl | rfl <;> decide
   have hn:blockLength - wX hi=gap hi+(blockLength - farAgreement) := by
     unfold gap
     have hdA:wX hi<farAgreement:=Nat.sub_pos_iff_lt.mp hgap
     have hAN :farAgreement≤blockLength:= by decide
     omega
   change ((blockLength - wX hi:ℕ) :ℚ)/(gap hi:ℚ)=1+beta hi
   rw [hn,Nat.cast_add,add_div,div_self (Nat.cast_ne_zero.mpr hgap.ne')]
 have hgq: (1 :ℚ)≤g:= by exact_mod_cast hg
 have hmul :=mul_le_mul_of_nonneg_right hcoef (show 0≤2*(g:ℚ) - 1 by linarith only [hgq])
 rw [curveUnit_eq,hρ]
 refine (le_trans ?_ (add_le_add hmul le_rfl))
 rw [add_mul,one_mul]
 linarith only [hgq]
end
end q8ADoQd
