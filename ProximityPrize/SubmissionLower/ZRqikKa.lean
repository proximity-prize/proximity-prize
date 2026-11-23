import ProximityPrize.SubmissionLower.ZogIzOe
import ProximityPrize.SubmissionLower.ZUt8KUb
set_option Elab.async false
set_option autoImplicit true
namespace qxRSHvb
noncomputable section
open P5 (K p blockLength)
open P5_7 (midAgreement)
open P5_7_2 (A fO jX row)

open DQ (Ag Wh)
open axI (azO aVj dcv c3X)
open private OF OF.distinct OF.degree bf9 bNu q9NbxKa.rho aaM weights from ProximityPrize.SubmissionLower.ZogIzOe
open Finset Polynomial
private theorem band_degrees (b:fO) :
  (jX b).hi≤(row b).declaredHi∧(row b).declaredHi≤2703:= by
 fin_cases b <;> decide
private theorem rho_endpoint {d:ℕ} (hl:131071≤d) (hh:d≤133774) :
  q9NbxKa.rho d≤aaM*d:= by
 have hdA:d< midAgreement:=hh.trans_lt (by decide)
 have hdN :d≤blockLength:=hh.trans (by decide)
 have hrho:q9NbxKa.rho d≤6:= by
  unfold q9NbxKa.rho
  have hp: (0:ℚ)<((midAgreement-d:ℕ) :ℚ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt hdA)
  apply (div_le_iff₀ hp).mpr
  rw [Nat.cast_sub hdN,Nat.cast_sub hdA.le]
  change (262144 :ℚ) - d≤6*((179740:ℚ) - d)
  have hQ: (d:ℚ)≤133774 :=Nat.cast_le.mpr hh
  linarith only [hQ]
 have hDensity :1≤aaM:= by
  apply (le_div_iff₀ (show (0:ℚ)<(midAgreement:ℚ) by positivity)).mpr
  rw [one_mul]
  exact_mod_cast (by decide :midAgreement≤blockLength)
 exact hrho.trans (calc
  (6:ℚ)≤(d:ℚ) := by exact_mod_cast (show 6≤d by omega)
  _=1*(d:ℚ) :=(one_mul _).symm
  _≤aaM*d:=mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem ceY {n g H d:ℕ} {U:Finset K} {s :K→Polynomial K} {w}
   (A:DQ.bk0 U s g H n) (hw:OF w U s d)
   (hg:0<g) (hd₀:131071≤d) (hd₁:d≤133774) :
   (U.card:ℚ)≤(2*aaM*d*(Ag g:ℚ)+q9NbxKa.rho d)*H+1 := by
 have hbound:0≤(2*aaM*d*(Ag g:ℚ)+q9NbxKa.rho d)*(H :ℚ) := by
   unfold q9NbxKa.rho
   positivity
 by_cases hc:U.card≤1
 · have h: (U.card:ℚ)≤1 := by exact_mod_cast hc
   linarith only [h,hbound]
 let sites :=azO w U s
 let t:=max 1 (d-sites.card)
 have hd:d< midAgreement:=hd₁.trans_lt (by decide)
 have hs :sites.card≤d:=bf9 hw (by omega)
 have ht:0<t:=(by decide :0<1).trans_le (le_max_left _ _)
 have htp:t<p:=(max_le (by omega :1≤d) (Nat.sub_le _ _)).trans_lt (hd₁.trans_lt (by decide))
 have hdt:d≤ sites.card+t:= by
   have h:=le_max_right 1 (d-sites.card)
   omega
 obtain ⟨C,hreconstruct⟩:=c3X sites w hdt htp hg A.equation A.equation_degree
 let D:=Ag t*(g*H)+Wh t g*H
 have hsection :=dcv (w:=w) A ht (OF.distinct hw) C fun γ hγ =>
   hreconstruct _ _ (OF.degree hw γ hγ) (fun _ hi=>aVj hγ hi) (A.root γ hγ) (A.simple γ hγ)
 have hinc: ((midAgreement - sites.card:ℕ) :ℚ)*U.card≤((blockLength - sites.card:ℕ) :ℚ)*D:= by
   exact_mod_cast bNu hw D hsection
 have hden: (0:ℚ)<((midAgreement - sites.card:ℕ) :ℚ) := by
   exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
 have hcard: (U.card:ℚ)≤q9NbxKa.rho sites.card*(D:ℚ) := by
   rw [q9NbxKa.rho,div_mul_eq_mul_div]
   apply (le_div_iff₀ hden).mpr
   calc
     _=((midAgreement - sites.card:ℕ) :ℚ)*U.card:=mul_comm _ _
     _≤_:=hinc
 obtain ⟨hρ,hρt⟩:=weights hs hd (rho_endpoint hd₀ hd₁)
 have hρb:q9NbxKa.rho sites.card*(Ag t:ℚ)≤2*aaM*d:= by
   have hb: (Ag t:ℚ)≤2*(t:ℚ) := by
     exact_mod_cast (Nat.sub_le (2*t) 1 :Ag t≤2*t)
   have hρ0:0≤q9NbxKa.rho sites.card:=div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
   have h:=mul_le_mul_of_nonneg_left hb hρ0
   nlinarith only [h,hρt]
 have hsum:g+(g - 1)=Ag g:= by unfold Ag; omega
 have hD:D =(Ag t*Ag g+1)*H := by
   rw [← hsum]
   dsimp [D,Wh]
   ring
 refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
 calc
   _=(q9NbxKa.rho sites.card*(Ag t:ℚ)*(Ag g:ℚ)+q9NbxKa.rho sites.card)*H := by
     rw [hD]
     push_cast
     ring
   _≤_:=mul_le_mul_of_nonneg_right
     (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)
end
end qxRSHvb
