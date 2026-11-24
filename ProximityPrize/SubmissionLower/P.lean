import ProximityPrize.SubmissionLower.AE
import Mathlib.Algebra.AffineMonoid.UniqueSums
set_option Elab.async false
section
set_option autoImplicit true
section
namespace akL
noncomputable section
open aR xE
open MvPolynomial
abbrev Jp:=Fin 4 →₀ ℕ
abbrev MI:=MvPolynomial (Fin 4) ao
def BU:Fin 4→ℕ:= fun _=>1
def Oq:Fin 4→ℕ:=Fin.val
def oH :Fin 4→ℕ := ![3,0,1, 2]
def arP (F:Flag) :Set Jp :=
  { e | (e.weight BU:ℤ)=F.degree ∧
    F.lower≤(e.weight Oq:ℤ) ∧
    (e.weight Oq:ℤ)≤F.upper∧(e (3:Fin 4) :ℤ)≤F.cap }
def bOM (F:Flag) :Set Jp :=
  { e | (e.weight BU:ℤ)=F.degree ∧
    F.lower≤(e.weight Oq:ℤ)∧(e.weight oH :ℤ)<F.order }
def bob (d u:ℤ) :Set Jp :=
 { e | (e.weight BU:ℤ)=d∧(e.weight Oq:ℤ)≤u }
theorem bGD {s :Set Jp} {d:ℤ}
  (hs : ∀ e∈s,(e.weight BU:ℤ)=d) :s.Finite := by
 refine (Finsupp.finite_of_nat_weight_le BU (fun _=> by simp [BU])
  d.toNat).subset ?_
 intro e he
 change e.weight BU≤d.toNat
 have hd:=hs e he
 omega
theorem bJP (F:Flag) : (arP F).Finite :=
 bGD fun _ h=>h.1
theorem bON (F:Flag) : (bOM F).Finite :=
 bGD fun _ h=>h.1
theorem cIH (d u:ℤ) : (bob d u).Finite :=
 bGD fun _ h=>h.1
def aWa (F:Flag) :Finset Jp:=(bJP F).toFinset
def aAu (F:Flag) :Finset Jp:=(bON F).toFinset
def adw (d u:ℤ) :Finset Jp:=(cIH d u).toFinset
def a9U:Prop :=
 ∀ d u:ℤ,((adw d u).card:ℤ)=gd d u
@[simp] theorem eAc {F:Flag} {e :Jp} :
    e∈aWa F↔e∈arP F :=
  (bJP F).mem_toFinset
@[simp] theorem b83 {F:Flag} {e :Jp} :
    e∈aAu F↔e∈bOM F :=
  (bON F).mem_toFinset
@[simp] theorem azA {d u:ℤ} {e :Jp} :
    e∈adw d u↔e∈bob d u :=
  (cIH d u).mem_toFinset
def ahV (F:Flag) :Submodule ao MI:=restrictSupport ao (arP F)
def bOO (F:Flag) :Submodule ao MI:=restrictSupport ao (bOM F)
instance (F:Flag) :Module.Finite ao (ahV F) :=
 restrictSupport_finite (bJP F)
instance (F:Flag) :Module.Finite ao (bOO F) :=
 restrictSupport_finite (bON F)
theorem aDd (F:Flag) :
  Module.finrank ao (ahV F)=(aWa F).card:= by
 conv_lhs=>rw [ahV,← (bJP F).coe_toFinset]
 exact finrank_restrictSupport_finset (aWa F)
theorem b3d (F:Flag) :
  Module.finrank ao (bOO F)=(aAu F).card:= by
 conv_lhs=>rw [bOO,← (bON F).coe_toFinset]
 exact finrank_restrictSupport_finset (aAu F)
def La (j:Fin 4) :MI :=
 if j=0 then MvPolynomial.X 0+MvPolynomial.X 1-MvPolynomial.X 2+MvPolynomial.X 3
 else MvPolynomial.X j
def alM:MI →ₐ[ao] MI:=bind₁ La
def KP (F:Flag) :ahV F →ₗ[ao] MI :=
  (weightedTruncation oH F.order.toNat).comp
    (alM.toLinearMap.comp (ahV F).subtype)
end
end akL
end
section
namespace akL
noncomputable section
open aR xE
open MvPolynomial
def c2 :Prop :=a9U
def c3:Prop :=
 a9U → ∀ F:Flag,((aWa F).card:ℤ)=oldCount F
def c4 :Prop :=
 a9U → ∀ F:Flag,((aAu F).card:ℤ)=AO F
def c5:Prop :=
  ∀ (F:Flag) (power :Fin 11→ℕ),
    ∃ f :LinearMap.ker (KP (BH F power)) →ₗ[ao]
        LinearMap.ker (KP F),Function.Injective f
theorem cpn (j:Fin 4) :
   (La j).IsWeightedHomogeneous BU (BU j) := by
 have hX (k :Fin 4) :=
   isWeightedHomogeneous_X ao BU k
 by_cases h:j=0
 · subst j
   simp only [La]
   exact (((hX 0).add (hX 1)).sub (hX 2)).add (hX 3)
 · simpa only [La,ite_eq_right h] using hX j
theorem gp6 (j:Fin 4) :
   La j∈restrictWeightedOrder Oq (Oq j) := by
 by_cases h:j=0
 · subst j
   change La 0∈restrictWeightedOrder Oq 0
   simp
 · simp only [La,ite_eq_right h]
   exact X_mem_restrictWeightedOrder Oq j le_rfl
theorem b3u (F:Flag) (p:ahV F) :
   KP F p∈bOO F:= by
 change ∀ e∈(KP F p).support,e∈bOM F
 intro e he
 by_cases hp: (p:MI)=0
 · have hz :p=0:=Subtype.ext hp
   simp [hz] at he
 have hd:0≤F.degree := by
   obtain ⟨u,hu⟩:=Finset.nonempty_iff_ne_empty.mpr
     (fun hs=>hp (support_eq_empty.mp hs))
   have h:=(p.2 hu).1
   omega
 have hgrade : (p:MI).IsWeightedHomogeneous BU F.degree.toNat := by
   intro u hu
   have h:=(p.2 (MvPolynomial.mem_support_iff.mpr hu)).1
   omega
 have hmin: (p:MI)∈restrictWeightedOrder Oq F.lower.toNat := by
   intro u hu
   change F.lower.toNat≤u.weight Oq
   have h:=(p.2 hu).2.1
   omega
 have hgrade' := hgrade.bind₁ cpn
 have hmin' := mem_restrictWeightedOrder.mp
   (bind₁_mem_restrictWeightedOrder gp6 hmin)
 change e∈(weightedTruncation oH F.order.toNat
   (bind₁ La (p:MI))).support at he
 rw [MvPolynomial.mem_support_iff,coeff_weightedTruncation] at he
 split at he
 next hcut =>
   have hs :=MvPolynomial.mem_support_iff.mpr he
   have hg:=hgrade' he
   have hl:=hmin' e hs
   change (e.weight BU:ℤ)=F.degree ∧
     F.lower≤(e.weight Oq:ℤ)∧(e.weight oH :ℤ)<F.order
   exact ⟨by omega,by omega,by omega⟩
 next=>exact (he rfl).elim
end
end akL
end
end
section
open _root_ renaming Finset.range → z4x, Finset.sum_le_sum → zQk, Int.toNat_of_nonneg → zi4, Monotone → zVa, Nat.cast_mul → z2R, Nat.cast_ofNat → zWE, Nat.cast_one → z4o, ite_eq_left → zYo, ite_eq_right → zNB, one_dvd → zJl, xE.denominator → ziF
set_option autoImplicit true
section
namespace GI
open xE
open scoped BigOperators
structure kJ where
 value :ℕ
 top:ℕ
 Ej:ℕ
def kJ.expand (p:kJ) :Fin 11→ℕ :=
 ![p.value,0,0,p.top,0,0,0,0,0,0,p.Ej]
structure Window where
 gradeLo:ℕ
 gradeHi:ℕ
 offsetLo:ℕ
 offsetHi:ℕ
 diagonalLo:ℕ
 diagonalHi:ℕ
def Window.dY (w:Window) (i:sP) :Prop :=
 w.gradeLo≤ i.1.val∧i.1.val<w.gradeHi ∧
 w.offsetLo≤ i.2.val∧i.2.val≤w.offsetHi ∧
 w.diagonalLo≤ i.1.val+i.2.val∧i.1.val+i.2.val≤w.diagonalHi
instance (w:Window) (i:sP) :Decidable (w.dY i) := by
 unfold Window.dY
 infer_instance
theorem a7O (F:Flag) (p:kJ) :
    BH F p.expand =
      ⟨F.degree-((p.value :ℤ)+p.top+3*p.Ej),
        F.lower-(3*(p.top:ℤ)+2*p.Ej),
        F.upper-(3*(p.top:ℤ)+3*p.Ej),
        F.cap-((p.top:ℤ)+p.Ej),
        F.order-(2*(p.top:ℤ)+3*p.Ej)⟩:= by
  simp [BH,kJ.expand,Fin.sum_univ_succ,Jd]
  ring_nf
  simp
end GI
end
section
namespace GI
open xE
open scoped BigOperators
private def gI (k :ℕ) (f :ℤ→ℤ) (u:ℤ) :ℤ:=f u - f (u - k)
private theorem alS (a b:ℕ) (f :ℤ→ℤ) :
  gI a (gI b f)=gI b (gI a f) := by
 funext u
 unfold gI
 rw [show u-(a :ℤ) - b=u-(b:ℤ)-a by ring]
 ring
private theorem b0E (k n:ℕ) (f :ℤ→ℤ) (u:ℤ) :
   gI (k*n) f u = ∑ j∈z4x n,gI k f (u-(k :ℤ)*j) := by
 induction n with
 | zero=>simp [gI]
 | succ n ih =>
   rw [Finset.sum_range_succ,← ih]
   simp only [gI,z2R,Nat.cast_succ]
   rw [show u-(k :ℤ)*((n:ℤ)+1)=u-(k :ℤ)*n - k by ring]
   ring
private theorem b0D {a b:ℕ} {f :ℤ→ℤ} (h:a∣b)
  (hm:zVa (gI a f)) :zVa (gI b f) := by
 obtain ⟨n,rfl⟩:=h
 intro u v huv
 rw [b0E,b0E]
 exact zQk fun j _=>hm (sub_le_sub_right huv _)
private theorem eDT {f :ℤ→ℤ}
  (h : ∀ u,0≤gI 1 f u) :zVa f := by
 intro u v huv
 let n:=(v - u).toNat
 have hn: (n:ℤ)=v - u:=zi4 (by omega)
 have hz :0≤gI (1*n) f v := by
  rw [b0E]
  exact Finset.sum_nonneg fun _ _=>h _
 simpa only [gI,z4o,z2R,one_mul,hn,sub_sub_cancel,
  sub_nonneg] using hz
private def btS (q r :ℤ) :ℤ :=
 2+r*(r+1)+q*(44+14*r+r*(r - 1)) +
   (57+6*r)*(q*(q - 1))+12*q*(q - 1)*(q - 2)
private theorem XK (x :ℤ) :2*(x*(x - 1)/2)=x*(x - 1) := by
 have h: (2 :ℤ)∣x*(x - 1) := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx
  · exact dvd_mul_of_dvd_left (by omega : (2 :ℤ)∣x) _
  · exact dvd_mul_of_dvd_right (by omega : (2 :ℤ)∣x - 1) _
 rw [mul_comm,Int.ediv_mul_cancel h]
private theorem coI (u:ℤ) (hu:0≤u) :
  2*ziF u=btS (u/6) (u % 6) := by
 let q:=u/6
 let r :=u % 6
 simp only [ziF,not_lt.mpr hu,ite_false,btS]
 change 2*(1+r*(r+1)/2+q*(22+7*r+r*(r - 1)/2) +
  (57+6*r)*(q*(q - 1)/2)+6*q*(q - 1)*(q - 2))= _
 have h:=XK (r+1)
 rw [show (r+1)*(r+1 - 1)=r*(r+1) by ring] at h
 change _=2+r*(r+1)+q*(44+14*r+r*(r - 1)) +
  (57+6*r)*(q*(q - 1))+12*q*(q - 1)*(q - 2)
 linear_combination h+q*XK r+(57+6*r)*XK q
private theorem aAe (u k :ℤ) (h:k≤u) :
  2*ziF (u - k)=btS (u/6+(u % 6 - k)/6) ((u % 6 - k) % 6) := by
 rw [coI _ (by omega)]
 congr 1 <;> omega
private theorem Jc (u:ℤ) (h:u<0) :ziF u=0:= by
 simp only [ziF,zYo h]
private theorem ded (u:ℤ) :
    gI 1 (gI 2 (gI 3 ziF)) u=if u<0 then 0 else 1 := by
  by_cases hu:u<0
  · simp (disch:=omega) only [gI,Jc,hu,sub_self,ite_true]
  by_cases hs :u<8
  · interval_cases u <;> decide
  rw [zNB hu]
  have hf :gI 1 (gI 2 (gI 3 ziF)) u =
      ziF u - ziF (u - 1) - ziF (u - 2) +
        ziF (u-4)+denominator (u - 5) - ziF (u-6) := by
    simp only [gI,zWE,z4o]
    rw [show u - 2 - 3=u - 5 by ring,show u - 1 - 3=u-4 by ring,
      show u - 1 - 2=u-3 by ring,show u-3-3=u-6 by ring]
    ring
  rw [hf]
  apply (mul_left_cancel₀ (show (2 :ℤ)≠0 by decide))
  have hh (k :ℤ) (hk :k≤8) :=aAe u k (by omega)
  have h0:=hh 0 (by decide)
  rw [sub_zero] at h0
  have h1 :=hh 1 (by decide)
  have h2 :=hh 2 (by decide)
  have h4 :=hh 4 (by decide)
  have h5:=hh 5 (by decide)
  have h6:=hh 6 (by decide)
  have hd:0≤u % 6:= by omega
  have hb:u % 6<6:= by omega
  generalize u % 6=r at h0 h1 h2 h4 h5 h6 hd hb
  interval_cases r <;> norm_num [btS] at h0 h1 h2 h4 h5 h6 <;>
    linear_combination (norm:=ring_nf) h0 - h1 - h2+h4+h5 - h6
private theorem c0n (u:ℤ) :
    gI 1 (gI 1 (gI 6 ziF)) u =
      if u<0∨u=1 then 0 else 1 := by
  by_cases hu:u<0
  · simp (disch:=omega) only [gI,Jc,hu,sub_self,true_or,ite_true]
  by_cases hs :u<8
  · interval_cases u <;> decide
  rw [zNB (by omega)]
  have hf :gI 1 (gI 1 (gI 6 ziF)) u =
      ziF u - 2*ziF (u - 1)+denominator (u - 2) -
        ziF (u-6)+2*ziF (u - 7) - ziF (u-8) := by
    simp only [gI,zWE,z4o]
    rw [show u - 1-6=u - 7 by ring,show u - 1 - 1=u - 2 by ring,
      show u - 2 - 6=u-8 by ring]
    ring
  rw [hf]
  apply (mul_left_cancel₀ (show (2 :ℤ)≠0 by decide))
  have hh (k :ℤ) (hk :k≤8) :=aAe u k (by omega)
  have h0:=hh 0 (by decide)
  rw [sub_zero] at h0
  have h1 :=hh 1 (by decide)
  have h2 :=hh 2 (by decide)
  have h6:=hh 6 (by decide)
  have h7:=hh 7 (by decide)
  have h8:=hh 8 (by decide)
  have hd:0≤u % 6:= by omega
  have hb:u % 6<6:= by omega
  generalize u % 6=r at h0 h1 h2 h6 h7 h8 hd hb
  interval_cases r <;> norm_num [btS] at h0 h1 h2 h6 h7 h8 <;>
    linear_combination (norm:=ring_nf) h0 - 2*h1+h2 - h6+2*h7 - h8
private theorem bc9 {a b c k l m:ℕ} (f :ℤ→ℤ)
  (ha :k∣a) (hb:l∣b) (hc:m∣c)
  (hm:zVa (gI k (gI l (gI m f)))) :
  zVa (gI a (gI b (gI c f))) := by
 have H₁:=b0D ha hm
 rw [alS a l] at H₁
 have H₂:=b0D hb H₁
 rw [alS b a,alS b m,alS a m] at H₂
 have H₃:=b0D hc H₂
 rwa [alS c a,alS c b] at H₃
private theorem bwq:zVa (gI 1 (gI 2 (gI 3 ziF))) := by
 intro u v huv
 rw [ded,ded]
 split <;> split <;> omega
private theorem gtN (a :ℕ) (ha :2≤a) :
  zVa (gI a (gI 1 (gI 6 ziF))) := by
 apply eDT
 intro u
 rw [alS 1 a]
 simp only [gI]
 change 0≤gI 1 (gI 1 (gI 6 ziF)) u -
  gI 1 (gI 1 (gI 6 ziF)) (u-a)
 rw [c0n,c0n]
 split <;> split <;> omega
private def bgv (d:ℕ) :ℤ→ℤ :=
 gI (d+1) (gI (d+2) (gI (d+3) ziF))
private theorem fTO (d:ℕ) :zVa (bgv d) := by
 unfold bgv
 have hmod:d % 6<6:=Nat.mod_lt _ (by decide)
 interval_cases hr :d % 6
 · exact bc9 _ (zJl _) (by omega) (by omega) bwq
 · rw [alS (d+2) (d+3),alS (d+1) (d+3)]
   exact bc9 _ (zJl _) (by omega) (by omega) bwq
 · rw [alS (d+1) (d+2),alS (d+1) (d+3),alS (d+2) (d+3)]
   exact bc9 _ (zJl _) (by omega) (by omega) bwq
 · rw [alS (d+1) (d+2)]
   exact bc9 _ (zJl _) (by omega) (by omega) bwq
 · have ha :2≤d+1 := by omega
   rw [alS (d+2) (d+3)]
   exact bc9 _ (dvd_refl _) (zJl _) (by omega) (gtN _ ha)
 · rw [alS (d+1) (d+2),alS (d+1) (d+3)]
   exact bc9 _ (zJl _) (by omega) (by omega) bwq
private theorem fTN (d:ℕ) (u:ℤ) (h:u<0) :bgv d u=0:= by
 simp (disch:=omega) only [bgv,gI,Jc,sub_self]
private theorem bDC (d:ℕ) (u:ℤ) :
   gd d u=bgv d (min u (3*(d:ℤ))) := by
 by_cases hu:u<0
 · rw [min_eq_left (by omega),fTN _ _ hu]
   simp [gd,hu]
 · have hd : ¬ (d:ℤ)<0:= by omega
   simp [gd,hu,hd,bgv,gI]
   ring_nf
theorem anX (d:ℕ) :zVa (gd (d:ℤ)) := by
 intro u v huv
 rw [bDC,bDC]
 exact fTO d (min_le_min_right _ huv)
end GI
end
end
