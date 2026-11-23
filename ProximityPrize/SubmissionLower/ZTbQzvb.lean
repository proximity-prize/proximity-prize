import ProximityPrize.SubmissionLower.ZjZXRjd
import ProximityPrize.SubmissionLower.ZODPK9c
import ProximityPrize.SubmissionLower.Zc1KtHb
set_option Elab.async false
set_option maxHeartbeats 1000000
section
section
set_option autoImplicit true
namespace qgNKTHc
open scoped BigOperators
open qlc9qed (Bank)
open qPQ4nYa (xR Bb offset Ic pT iO
 K6 D8)
open Rj (kJ Flag yE Jd sG yC m5)
private def digit (data :ℕ×ℕ) (k :ℕ) :ℕ :=
 if k<data.1 then 0 else (data.2 >>> (20*(k - data.1))) % 0x100000
private def decode (z :ℕ) (i:Fin 6) :ℕ :=
 let s :=(![0,4,6,8,12,16] :Fin 6→ℕ) i
 let m:=(![16,4,4,16,16,16] :Fin 6→ℕ) i
 (z >>> s) % m
private def Cd (d:ℤ) (F:Fin 3→Flag) :ℤ :=
 if d<0 then 0 else sG (d+1)-(yC (F 0)+yC (F 1)+yC (F 2))
private theorem aDb (d:ℤ) (F:Fin 3→Flag) :
  Cd d F=m5 d F:= by
 simp only [m5,Cd,Fin.sum_univ_three]
private def six (f :Fin 6→ℤ) :ℤ:=f 0+f 1+f 2+f 3+f 4+f 5
private def fastShift (b:Bank) (q:ℕ) (g:ℤ) (p:kJ) :ℤ :=
 let F:=pT b q g
 Cd (iO b q - six (fun j=>p j*yE j)) (fun i =>
   ⟨(F i).iy - six (fun j=>p j*(Jd j i).iy),
    (F i).HE - six (fun j=>p j*(Jd j i).HE)⟩)
private theorem fastShift_eq (b:Bank) (q:ℕ) (g:ℤ) (p:kJ) :
   fastShift b q g p=m5 (K6 b q p) (D8 b q g p) := by
 simp only [fastShift,aDb]
 apply congrArg₂ m5
 · simp only [K6,Fin.sum_univ_six,six]
 · funext i
   simp only [D8,Fin.sum_univ_six,six]
private def shiftedKernel (b:Bank) (q:ℕ) (g:ℤ) (z :ℕ) :ℤ :=
 if z=0 then Cd (iO b q) (pT b q g)
 else fastShift b q g (decode z)
private theorem shiftedKernel_eq (b:Bank) (q:ℕ) (g:ℤ) (z :ℕ) :
   shiftedKernel b q g z =
    m5 (K6 b q (decode z)) (D8 b q g (decode z)) := by
 by_cases hz :z=0
 · subst z
   have hp (j:Fin 6) :decode 0 j=0:= by fin_cases j <;> rfl
   have hd:K6 b q (decode 0)=(iO b q:ℤ) := by
    simp only [K6,hp,Nat.cast_zero,zero_mul,Finset.sum_const_zero,sub_zero]
   have hf :D8 b q g (decode 0)=pT b q g:= by
    funext i
    simp only [D8,hp,Nat.cast_zero,zero_mul,Finset.sum_const_zero,sub_zero]
   rw [shiftedKernel,ite_eq_left rfl,aDb,hd,hf]
 · rw [shiftedKernel,ite_eq_right hz,fastShift_eq]
private def block (q k z :ℕ) :ℕ :=
 let b:=Bank.cheap
 let g:=offset b k
 let base :=Cd (iO b q) (pT b q g)
 let ic:=shiftedKernel b q g z
 if Ic b q g≤0 then 0 else (Bb b q g - max 0 (max base ic)).toNat
private theorem bVH (q k z :ℕ) :
  block q k z=xR .cheap q (offset .cheap k) (decode z) := by
 simp only [block,xR,aDb,shiftedKernel_eq]
private def sumBlocks (q:ℕ) (data :ℕ×ℕ) :ℕ→ℕ
 | 0=>0
 | k+1=>sumBlocks q data k+block q k (digit data k)
def cV (q:ℕ) (data :ℕ×ℕ) :ℕ:=sumBlocks q data (91 - q)
private theorem ay9 (q:ℕ) (data :ℕ×ℕ) :
   cV q data = ∑ k∈Finset.range 91,xR .cheap q (offset .cheap k) (decode (digit data k)) := by
 have h (n:ℕ) :sumBlocks q data n =
     ∑ k∈Finset.range n,xR .cheap q (offset .cheap k) (decode (digit data k)) := by
   induction n with
   | zero=>simp [sumBlocks]
   | succ n ih=>rw [sumBlocks,Finset.sum_range_succ,ih,bVH]
 rw [cV,h]
 refine Finset.sum_subset (Finset.range_mono (Nat.sub_le 91 q)) ?_
 intro k _ hk
 simp only [Finset.mem_range] at hk
 have hzero :Ic .cheap q (offset .cheap k)≤0:= by
   change (64 :ℤ)-(q:ℤ)-((k :ℤ) - 27)≤0
   omega
 simp only [xR,hzero,ite_true]
structure Window (q n total:ℕ) where
 codes :Fin n→ℕ×ℕ
 checked : (∑ i:Fin n,cV (q+i.val) (codes i))=total
def row (q a x v :ℕ) (h:cV q (a,x)=v) :Window q 1 v :=
 ⟨fun _=>(a,x),by simpa only [Fin.sum_univ_one,Fin.val_zero,Nat.add_zero] using h⟩
def Window.join {q n m s t:ℕ} (a :Window q n s) (b:Window (q+n) m t) :
    Window q (n+m) (s+t) := by
  refine ⟨Fin.addCases a.codes b.codes,?_⟩
  simpa only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,
    Fin.val_natAdd,Nat.add_assoc] using congrArg₂ (fun x y :ℕ=>x+y) a.checked b.checked
theorem Window.close (w:Window 0 88 292256) :qPQ4nYa.c2 := by
 let data (q:ℕ) :ℕ×ℕ:=if h:q<88 then w.codes ⟨q,h⟩ else (0,0)
 refine ⟨fun q k=>decode (digit (data q) k),?_⟩
 change (∑ q∈Finset.range 88,∑ k∈Finset.range 91,
  xR .cheap q (offset .cheap k) (decode (digit (data q) k)))≤292256
 simp_rw [← ay9]
 rw [← Fin.sum_univ_eq_sum_range]
 simpa only [data,dite_eq_left,Fin.is_lt,Fin.eta,Nat.zero_add] using w.checked.le
end qgNKTHc
end
end
section
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace q41fOQb
noncomputable section
open Polynomial Finset IsLocalRing UniqueFactorizationMonoid
open cu (FX aZ Equation Jet Shape)
open gT (Ambient iJ)
open pI (xN dual O9 oU)
open Ty (Be aoD)
open aFY (drS bID ew9)
open XY (ag6)
open P5_7_1 (bgK)
open qehP9ee (kK mixedCols)

open private sections dci from ProximityPrize.SubmissionLower.D7
private theorem choose_cut {P F G:Jet} (hP:P≠0) (h:ag6 F G) :
   ∃ a b:FX,ag6 P (a•F+b•G) := by
 classical
 let:UniqueFactorizationMonoid aZ:=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
 let:UniqueFactorizationMonoid Equation :=Polynomial.uniqueFactorizationMonoid (D:=aZ)
 let:UniqueFactorizationMonoid Jet:=Polynomial.uniqueFactorizationMonoid (D:=Equation)
 let:StrongNormalizationMonoid Jet:=UniqueFactorizationMonoid.strongNormalizationMonoid
 let:Infinite FX:=Infinite.of_injective _ (IsFractionRing.injective cu.L[X] FX)
 let V:=Submodule.span FX ({F,G} : Set Jet)
 let D:=insert 0 (normalizedFactors P).toFinset
 let J (d:Jet) :=((Ideal.span ({d} : Set Jet)).restrictScalars FX).comap V.subtype
 have hm (d:Jet) (Q:V) :Q∈J d↔d∣(Q:Jet) :=Ideal.mem_span_singleton
 have hF:F∈V:=Submodule.subset_span (by simp)
 have hG:G∈V:=Submodule.subset_span (by simp)
 have hp (d : ↥D) :J d.val ≠ ⊤ := by
   intro he
   have hall (Q:V) :Q∈J d.val :=he.symm ▸ Submodule.mem_top
   have hdF:=(hm _ _).mp (hall ⟨F,hF⟩)
   rcases mem_insert.mp d.property with hd | hd
   · exact h.left_ne (zero_dvd_iff.mp (hd ▸ hdF))
   · have hd:=Multiset.mem_toFinset.mp hd
     exact h.no_common _ (irreducible_of_normalized_factor _ hd) hdF ((hm _ _).mp (hall ⟨G,hG⟩))
 obtain ⟨Q,hQ⟩:=Submodule.exists_forall_notMem_of_forall_ne_top (fun d : ↥D =>J d.val) hp
 obtain ⟨a,b,hab⟩:=Submodule.mem_span_pair.mp Q.property
 refine ⟨a,b,?_⟩
 rw [hab]
 refine ⟨hP,fun hz=>hQ ⟨0,mem_insert_self _ _⟩ ((hm _ Q).mpr (zero_dvd_iff.mpr hz)),?_⟩
 intro f hf hdP hdQ
 obtain ⟨d,hd,he⟩:=exists_mem_normalizedFactors_of_dvd hP hf hdP
 exact hQ ⟨d,mem_insert_of_mem (Multiset.mem_toFinset.mpr hd)⟩
   ((hm _ Q).mpr (he.dvd_iff_dvd_left.mp hdQ))
private theorem smul_caps {s :Shape} {F:Jet} (hF:oU F s) (a :FX) :
  oU (a•F) s := by
 intro j i hn
 simp only [coeff_smul] at hn ⊢
 obtain ⟨hb,hj,hu⟩:=hF j i (fun hz=>hn (by rw [hz,smul_zero]))
 exact ⟨hb,hj,(MvPolynomial.totalDegree_smul_le a _).trans hu⟩
private theorem add_caps {s :Shape} {F G:Jet} (hF:oU F s) (hG:oU G s) :
  oU (F+G) s := by
 intro j i hn
 simp only [coeff_add] at hn ⊢
 have hu (H :Jet) (hH :oU H s) : ((H.coeff j).coeff i).totalDegree≤ s.U:= by
  by_cases hz : (H.coeff j).coeff i=0
  · simp [hz]
  · exact (hH j i hz).2.2
 have hij:i+j≤ s.B∧j≤ s.J:= by
  by_cases hz : (F.coeff j).coeff i=0
  · have h:=hG j i (fun he=>hn (by rw [hz,he,add_zero]))
    exact ⟨h.1,h.2.1⟩
  · have h:=hF j i hz
    exact ⟨h.1,h.2.1⟩
 exact ⟨hij.1,hij.2,(MvPolynomial.totalDegree_add _ _).trans (max_le (hu F hF) (hu G hG))⟩
private theorem dSV {P Q:Jet} {I:Ideal Ambient} (hI:xN I) (hd:dual I)
   {n:ℕ} (hP:O9 I P n) (hQ:iJ Q∈I) :
   (n:ℕ∞)≤Be P Q I hI.prime := by
 let:I.IsPrime :=hI.prime
 let R:=Localization.AtPrime I
 let:CommRing R:=inferInstanceAs (CommRing (Localization.AtPrime I))
 let φ:=algebraMap Ambient R
 have hdim:ringKrullDim R=2 := by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height I R,drS hI]
   rfl
 have hM:1<(maximalIdeal R).height:= by
   have he : (maximalIdeal R).height=2 :=
     WithBot.coe_injective ((maximalIdeal_height_eq_ringKrullDim (R:=R)).trans hdim)
   rw [he]
   decide
 have hq:φ (iJ Q)∈maximalIdeal R :=
   (IsLocalization.AtPrime.to_map_mem_maximal_iff R I _).mpr hQ
 rw [O9,ite_eq_left hd] at hP
 have hp:φ (iJ P)∈(maximalIdeal R)^n:= by
   simpa only [Ideal.map_bot,sup_bot_eq] using bID hP
 change _≤Module.length R (R ⧸ ((Ideal.span {iJ P,iJ Q}).map φ:Submodule R R))
 rw [Ideal.map_span,Set.image_insert_eq,Set.image_singleton]
 exact ew9 hq hM (Ideal.mem_sup_left hp) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
private theorem cast_cap (s t:Shape) (ht:t.J≤t.B) (k :Fin 4) :
  (aoD s t k :ℚ)=kK (bgK s) t k := by
 have h0:s.B*t.J+t.B*s.J - s.J*t.J=s.B*t.J+s.J*(t.B - t.J) := by
  rw [mul_comm t.B s.J,Nat.add_sub_assoc (Nat.mul_le_mul_left s.J ht),Nat.mul_sub_left_distrib]
 fin_cases k <;>
  simp [aoD,kK,mixedCols,bgK,Fin.sum_univ_three,h0,Nat.cast_mul] <;> ring
theorem proof :q54LkTb.c1 := by
  intro P F G s t S n hn hP hproper hs ht hPs hF hG hS k
  obtain ⟨a,b,hcut⟩:=choose_cut hP hproper
  let Q:=a•F+b•G
  have hQ:oU Q t:=add_caps (smul_caps hF a) (smul_caps hG b)
  have hb:=sections P Q s t S k n hP hcut.right_ne
    (aFX.gBO hcut) hs ht hPs hQ hn (fun I hI=> by
      obtain ⟨ha,hd,hf,hg,hp⟩:=hS I hI
      have hq:iJ Q∈I:= by
        simp only [Q,Algebra.smul_def,map_add,map_mul]
        exact I.add_mem (I.mul_mem_left _ hf) (I.mul_mem_left _ hg)
      exact ⟨ha,fun _=>dSV ha hd hp hq⟩)
  exact (dci hn hb).trans_eq (congrArg (· / (n:ℚ)) (cast_cap s t ht k))
end
end q41fOQb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace qp73k1b
noncomputable section
open Finset Polynomial
open P5 (p)
open P5_7_1 (bgK)
open qehP9ee (MovingBox kK mixedCols ordinaryBox)
open cu (Equation Jet Shape)
open gT (Ambient iJ)
open pI
open Ty (aYS aaW gY aoD)
open aqb
open scoped Classical
open private sections dci from ProximityPrize.SubmissionLower.D7
open private bWa from ProximityPrize.SubmissionLower.CO
open private aUy from ProximityPrize.SubmissionLower.AH
open private dcG gn4 from ProximityPrize.SubmissionLower.A0
open private ekt from ProximityPrize.SubmissionLower.A0
private theorem bJi (a b:Shape) (hb:b.J≤b.B) (k :Fin 4) :
   kK (bgK a) b k=(aoD a b k :ℚ) := by
 fin_cases k
 · have h:=Nat.mul_le_mul_right a.J hb
   simp only [kK,Fin.sum_univ_three]
   change ((a.B:ℚ)*b.J+(a.J:ℚ)*(b.B - b.J:ℕ)+(a.U:ℚ)*0) =
    (a.B*b.J+b.B*a.J-a.J*b.J:ℕ)
   rw [Nat.mul_comm a.J b.J,Nat.add_sub_assoc h,← Nat.sub_mul]
   push_cast
   ring
 all_goals simp [kK,bgK,mixedCols,aoD,Fin.sum_univ_three] <;> ring
private theorem residual_caps {F:Jet} {H :Equation} {s :Shape} {ν e u:ℕ}
  (he :ν*e≤H.natDegree) (hu:ν*u≤gY H)
  (hc:oU F (Ty.aea s (gY H) H.natDegree)) :
  oU F (qehP9ee.aea s ν e u) := by
 have hb:=Nat.sub_le_sub_left he s.B
 intro j i hij
 obtain ⟨hB,hJ,hU⟩:=hc j i hij
 exact ⟨hB.trans hb,hJ.trans (min_le_min_left _ hb),
  hU.trans (Nat.sub_le_sub_left hu s.U)⟩
private theorem residual_bound {F G:Jet} {a b:Shape} {I:Ideal Ambient} {n:ℕ}
  (ha :xN I) (hd:dual I) (hn:0<n) (hF:F≠0) (hG:G≠0)
  (hcop:IsRelPrime (iJ F) (iJ G)) (haJ:a.J≤a.B) (hbJ:b.J≤b.B)
  (hcF:oU F a) (hcG:oU G b)
  (hoF:O9 I F n) (hoG:O9 I G n) (k :Fin 4) :
  (pN I k :ℚ)≤kK (bgK a) b k/(n:ℚ)^2 := by
 have hl:=aFY.proof F G I ha n hn hoF hoG
 rw [ite_eq_left hd] at hl
 have h:=sections F G a b {I} k (n^2) hF hG hcop haJ hbJ hcF hcG (Nat.pow_pos hn)
  (fun J hJ=> by rw [mem_singleton.mp hJ]; exact ⟨ha,fun _=>hl⟩)
 have hs :n^2*pN I k≤aoD a b k := by
  simpa only [mass,sum_singleton] using h
 rw [bJi a b hbJ k]
 simpa only [Nat.cast_pow] using dci (Nat.pow_pos hn) hs
private theorem ordinary_dvd {P D T:Jet} {H :Equation} (h:P=D *(C H*T)) :
 C H∣P:=⟨D *T,h.trans (by rw [← mul_assoc,mul_comm D (C H),mul_assoc])⟩
private theorem spend_power {f H :Equation} {ν:ℕ}
   (hf :f≠0) (hH :H≠0) (hdiv :f^ν∣H) :
   ν*f.natDegree≤H.natDegree∧ν*gY f≤gY H := by
 constructor
 · simpa only [natDegree_pow] using natDegree_le_of_dvd hdiv hH
 · simpa only [dcG,Qt.bg4 hf] using gn4 hH hdiv
private theorem cancel_branch {I:Ideal Ambient} {f g:Equation} {F:Jet} {ν m:ℕ}
   (ha :xN I) (hd:dual I) (hf :Irreducible f) (hpos :0<f.natDegree)
   (hp:f.natDegree<p) (hcon :I.comap Co=Ideal.span {f})
   (hg:Co g∉I) (hν:ν< m) :
   O9 I (C (f^ν*g)*F) m→O9 I F (m-ν) := by
 let:I.IsPrime :=ha.prime
 obtain ⟨hf',t,ht⟩:=cy1.proof I ha f hd hf hpos hp hcon
 intro ho
 rw [map_mul,mul_comm (C (f^ν)) (C g),mul_assoc] at ho
 have h:=bWc (r :=ν+1) (f :=f) (fun Q n hQ=> by
   apply (c2C I hd Q n).mpr
   apply a1X (R:=aBW I) (M:=I.map (aIW I)) hf' ht
   simpa only [map_mul,btc] using
     (c2C I hd (C f*Q) (n+1)).mp hQ) (Nat.lt_succ_self ν)
   (Nat.succ_le_of_lt hν) (bB3 ha.prime hg ho)
 simpa only [Nat.add_sub_add_right] using h
theorem proof :q54LkTb.c2 := by
 intro s P Q A B I hB _hU hP hQ hcP hcQ hno ha hd hchain hA hBF hoP hoQ
 obtain ⟨G⟩:=bR0.gp3 A B hP hQ hcP hcQ hno
 let H :=G.iy
 let m:=s.dI+1
 have hm:0< m:=Nat.succ_pos _
 obtain ⟨hRU,hRB,_⟩:=aUy hQ G.ordinary_ne hcQ G.right_factor
 have hBP:=G.ordinate_le.trans_lt hB
 have hUle :gY H≤ min s.free.U s.moving.U:=le_min G.acI hRU
 have hBle :H.natDegree≤ min s.free.B s.moving.B:=le_min G.ordinate_le hRB
 have hDP:=ordinary_dvd G.left_factor
 have hDQ:=ordinary_dvd G.right_factor
 rw [G.left_factor] at hoP
 rw [G.right_factor] at hoQ
 have hLP:=bWa ha.prime _ _ m hA hoP
 have hLQ:=bWa ha.prime _ _ m hBF hoQ
 have residual {ν e u:ℕ} (he :ν*e≤H.natDegree) (hu:ν*u≤gY H)
     (hn:ν< m) (hp:O9 I G.left (m-ν)) (hq:O9 I G.right (m-ν)) (k :Fin 4) :=
   residual_bound ha hd (Nat.sub_pos_of_lt hn) G.left_ne G.right_ne G.relativelyPrime
     (min_le_right _ _) (min_le_right _ _) (residual_caps he hu G.left_caps)
     (residual_caps he hu G.right_caps) hp hq k
 have graph {f :Equation} {ν:ℕ} (hn:0<ν) (hf :Irreducible f)
     (he :0<f.natDegree) (hdiv :f^ν∣H) (hI:Co f∈I) (k :Fin 4) :
     pN I k≤ordinaryBox f.natDegree (gY f) k := by
   have hv :=(dvd_pow_self f hn.ne').trans hdiv
   have hvp:=(natDegree_le_of_dvd hv G.ordinary_ne).trans_lt hBP
   have hc:= _root_.map_dvd (C:Equation →+* Jet) hv
   have h:=ekt aFY.proof sections hf he hvp
     (hc.trans hDP) (hc.trans hDQ) {I}
     (fun J hJ=> by rw [mem_singleton.mp hJ]; exact ⟨ha,hchain,hI⟩) k
   fin_cases k <;> simpa [mass,aaW,ordinaryBox,Nat.mul_assoc,Nat.mul_comm,
     Nat.mul_left_comm] using h
 unfold MovingBox
 by_cases hh:aYS H m I
 · obtain ⟨f,hf,he,hdiv,hI⟩:=hh
   obtain ⟨hb,hu⟩:=spend_power hf.ne_zero G.ordinary_ne hdiv
   exact Or.inr ⟨m,f.natDegree,gY f,hm,le_rfl,he,hb.trans hBle,
     hu.trans hUle,graph hm hf he hdiv hI,fun h=>(lt_irrefl _ h).elim⟩
 by_cases hI:Co H∈I
 · obtain ⟨f,g,ν,hfac,hn,hf,he,hfb,_,hcon,hg⟩ :=
     eHJ ha G.ordinary_ne hh hI
   change H=f^ν*g at hfac
   have hν:0<ν:=Nat.pos_of_ne_zero fun hz=>hg (by simpa [hfac,hz] using hI)
   have hfin:Co f∈I:= by
     change f∈I.comap Co
     rw [hcon]
     exact Ideal.mem_span_singleton_self f
   have hdiv :f^ν∣H :=⟨g,hfac⟩
   obtain ⟨hb,hu⟩:=spend_power hf.ne_zero G.ordinary_ne hdiv
   have hcancel {F:Jet} (h:O9 I (C H*F) m) :O9 I F (m-ν) :=
     cancel_branch ha hd hf he (hfb.trans_lt hBP) hcon hg hn (hfac ▸ h)
   exact Or.inr ⟨ν,f.natDegree,gY f,hν,hn.le,he,hb.trans hBle,
     hu.trans hUle,graph hν hf he hdiv hfin,fun _=>residual hb hu hn (hcancel hLP) (hcancel hLQ)⟩
 exact Or.inl (residual (ν:=0) (e :=0) (u:=0) (Nat.zero_le _) (Nat.zero_le _) hm
   (bB3 ha.prime hI hLP) (bB3 ha.prime hI hLQ))
end
end qp73k1b
end
section
set_option backward.isDefEq.respectTransparency false
namespace qbjv5ec
noncomputable section
open Polynomial
open cu (L)
open P5_7_7 (Dg seedDerivative)
abbrev Coeff :=L[X][X]
def polarOver {R:Type*} [CommRing R] (F:R[X]) (r :R) :R[X] :=
 (Polynomial.X (R:=R) - C r)*F.derivative
def cutOver {R:Type*} [CommRing R] (F G:R[X]) (r :R) :R[X][X] :=
 (polarOver F r).map C+C (Polynomial.X (R:=R))*G.map C
def resultantOver {R:Type*} [CommRing R] (F G:R[X]) (r :R) :R[X] :=
 (F.map C).resultant (cutOver F G r) F.natDegree F.natDegree
abbrev polar (F:Dg) (r :L) :Dg:=polarOver F (C (C r))
abbrev reciprocalResultant (F:Dg) (r :L) :Coeff[X] :=
 resultantOver F (seedDerivative F) (C (C r))
abbrev aQ:=FractionRing L[X]
abbrev lN :=FractionRing aQ[X]
abbrev EC:=AlgebraicClosure lN
def qY:Coeff →+* lN :=
  (algebraMap aQ[X] lN).comp
    ((mapRingHom (algebraMap L[X] aQ)).comp Bivariate.swap.toRingHom)
abbrev uniformizer (x :L) :aQ[X] :=
 Polynomial.X (R:=aQ) -
  Polynomial.C (R:=aQ) (algebraMap L[X] aQ (Polynomial.C (R:=L) x))
def physicalPrime (x :L) :IsDedekindDomain.HeightOneSpectrum aQ[X] := by
  have h:Prime (uniformizer x) :=prime_X_sub_C _
  exact ⟨Ideal.span {uniformizer x},
    (Ideal.span_singleton_prime h.ne_zero).mpr h,
    Ideal.span_singleton_eq_bot.not.mpr h.ne_zero⟩
abbrev NodeRing (x :L) :=(physicalPrime x).valuationSubringAtPrime lN
def cTD (F:Dg) (y :EC) :EC :=
 F.eval₂ ((algebraMap lN EC).comp qY) y
def TameAt (F:Dg) (x r :L) :Prop :=
  ∀ y :EC,cTD F y=0 →
    cTD (polar F r) y≠0 ∧
    IsIntegral (NodeRing x) (cTD (seedDerivative F) y/ cTD (polar F r) y)
end
end qbjv5ec
end
section
set_option synthInstance.maxSize 512
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace q7kdBxd
noncomputable section
open Polynomial Finset
open scoped WithZero

open cu (L)
open P5_7_7 (Dg seedDerivative)
open qGnV2ac (EquationBounds Sections HE pN)
structure Input where
 F:Dg
 l:ℕ
 h:ℕ
 s :ℕ
 b:ℕ
 Ca :EquationBounds F l h
 weight:HE F s (b+l*s)
def horizontalDegree (J:Input) :ℕ :=
 (2*J.l-2)*J.b+J.l*(J.l-1)*J.s
def polarBudget (J:Input) :ℕ :=
 ((6*J.l-4)*J.b+(3*J.l*J.l-2)*J.s)*J.h
def intrinsic {F:Dg} (S:Sections F) (s :ℕ) :ℕ :=
 ∑ γ∈S.CF,max (S.B γ).natDegree ((S.A γ).natDegree-pN S s γ)
def finitePoles {F:Dg} (S:Sections F) :ℕ :=
 ∑ γ∈S.CF,(S.B γ).natDegree
instance (J:Input) :IsDomain (AdjoinRoot J.F) :=
 AdjoinRoot.isDomain_of_prime
  ((UniqueFactorizationMonoid.irreducible_iff_prime (α:=Dg)).mp J.Ca.irreducible)
abbrev EC (J:Input) :=FractionRing (AdjoinRoot J.F)
def a7W (J:Input) :Dg →+* EC J :=
 (algebraMap (AdjoinRoot J.F) (EC J)).comp (AdjoinRoot.mk J.F)
def constant (J:Input) (a :L) :EC J:=a7W J (C (C (C a)))
def amm (J:Input) :EC J:=a7W J (C (C (Polynomial.X:L[X])))
def seed (J:Input) :EC J:=a7W J (C (Polynomial.X:L[X][X]))
def jU (J:Input) (recip:Bool) :EC J :=
 if recip then (a7W J X)⁻¹ else a7W J X
def chartEq (J:Input) (recip:Bool) :Dg :=
 if recip then J.F.reverse else J.F
def KM (J:Input) (recip:Bool) :Dg →+* EC J :=
 eval₂RingHom ((a7W J).comp C) (jU J recip)
def physicalDerivative (F:Dg) :Dg :=
 F.sum fun i a=>monomial i (a.sum fun j b=>monomial j b.derivative)
def polar (J:Input) (recip:Bool) :EC J :=
 KM J recip (chartEq J recip).derivative
def jet (J:Input) (recip:Bool) :EC J :=
 -(KM J recip (physicalDerivative (chartEq J recip)))/polar J recip
def variation (J:Input) (recip:Bool) :EC J :=
 -(KM J recip (seedDerivative (chartEq J recip)))/polar J recip
def aD (J:Input) (recip:Bool) :Fin 4→EC J :=
 ![amm J,seed J,jU J recip,jet J recip]
def ResidueConstant (J:Input) (v :Valuation (EC J) ℤᵐ⁰) (a :EC J) :Prop :=
 ∃ c:L,v (a-constant J c)<1
structure GraphPrime (J:Input) (recip:Bool) where
 val :Valuation (EC J) ℤᵐ⁰
 normalized:Function.Surjective val
 constants : ∀ a :L,a≠0→val (constant J a)=1
 regular : ∀ i,val (aD J recip i)≤1
 curve : ∃ i,¬ ResidueConstant J val (aD J recip i)
end
end q7kdBxd
end
end
