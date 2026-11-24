import ProximityPrize.SubmissionLower.Z3e8uLd
import ProximityPrize.SubmissionLower.ZNBvygc
set_option Elab.async false
set_option autoImplicit true
namespace q9NbxKa
noncomputable section
open P5 (K I node blockLength)
open P5_7 (midAgreement)
open P5_7_1 (degree hi)


open DQ (Ag)
open axI (azO aVj)
open Finset Polynomial ProximityPrize.Benchmark
private structure OF (w:I→K) (U:Finset K) (s :K→K[X]) (d:ℕ) :Prop where
 distinct :Set.InjOn s (U:Set K)
 degree : ∀ γ∈U,(s γ).natDegree≤d
 lg : ∀ γ∈U,∃ B:Finset I,midAgreement≤B.card ∧ ∀ i∈B,(s γ).eval (node i)=w i
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
   (midAgreement - (azO w U s).card)*U.card ≤
     (blockLength-(azO w U s).card)*D:= by
 classical
 let sites :=azO w U s
 let nodes :Finset I:=univ \ sites
 let lg (γ:K) :=nodes.filter fun i=>(s γ).eval (node i)=w i
 let occ (i:I) :=U.filter fun γ=>(s γ).eval (node i)=w i
 have hhit (γ:K) (hγ:γ∈U) :midAgreement - sites.card≤(lg γ).card:= by
   obtain ⟨B,hB,hvals⟩:=hw.lg γ hγ
   let good:Finset I:=univ.filter fun i=>(s γ).eval (node i)=w i
   have hgood:midAgreement≤good.card :=
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
   _ = ∑ γ∈U,(midAgreement - sites.card) := by rw [sum_const,smul_eq_mul,Nat.mul_comm]
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
 ((blockLength - s :ℕ) :ℚ)/((midAgreement - s :ℕ) :ℚ)
private abbrev aaM:ℚ:=(blockLength:ℚ)/midAgreement
private theorem weights {s d:ℕ} (hs :s≤d) (hd:d< midAgreement)
   (haux :rho d≤aaM*d) :
   rho s≤ rho d∧rho s*(max 1 (d-s) :ℕ)≤aaM*d:= by
 have hAN :midAgreement≤blockLength:= by decide
 have hsA:=hs.trans_lt hd
 have hdN :=hd.le.trans hAN
 have hsN :=hs.trans hdN
 have hAs : (0:ℚ)<(midAgreement:ℚ) - s :=sub_pos.mpr (by exact_mod_cast hsA)
 have hAd: (0:ℚ)<(midAgreement:ℚ) - d:=sub_pos.mpr (by exact_mod_cast hd)
 have hmain:rho s≤ rho d:= by
   unfold rho
   rw [Nat.cast_sub hsN,Nat.cast_sub hsA.le,Nat.cast_sub hdN,Nat.cast_sub hd.le]
   apply (div_le_div_iff₀ hAs hAd).mpr
   have h:=mul_nonneg (sub_nonneg.mpr (show (s :ℚ)≤d by exact_mod_cast hs))
     (sub_nonneg.mpr (show (midAgreement:ℚ)≤blockLength by exact_mod_cast hAN))
   nlinarith only [h]
 refine ⟨hmain,?_⟩
 by_cases heq :s=d
 · subst s
   simpa using haux
 have hpos :1≤d - s := by omega
 rw [max_eq_right hpos]
 have hden: (0:ℚ)<(midAgreement:ℚ) := by exact_mod_cast (by decide :0< midAgreement)
 have hfrac: ((d-s :ℕ) :ℚ)/((midAgreement-s :ℕ) :ℚ)≤(d:ℚ)/midAgreement:= by
   rw [Nat.cast_sub hs,Nat.cast_sub hsA.le]
   apply (div_le_div_iff₀ hAs hden).mpr
   have h:=mul_nonneg (Nat.cast_nonneg s : (0:ℚ)≤ s) hAd.le
   nlinarith only [h]
 calc
   _=((blockLength-s :ℕ) :ℚ)*(((d-s :ℕ) :ℚ)/((midAgreement-s :ℕ) :ℚ)) := by
     unfold rho
     ring
   _≤(blockLength:ℚ)*((d:ℚ)/midAgreement) :=
     mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
   _=aaM*d:= by ring
private theorem gAN {g:ℕ} (hg:0<g) :
  (Ag g:ℚ)=2*(g:ℚ) - 1 := by
 unfold Ag
 rw [Nat.cast_sub (by omega)]
 push_cast
 rfl
end
end q9NbxKa
