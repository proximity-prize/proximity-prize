import ProximityPrize.SubmissionLower.CH
set_option Elab.async false
open _root_ renaming Dr.ChamberBox→lJ,Dr.dimension→ oj,Finset→nX,Ideal→c9,Ideal.Quotient.mk→ oD,Ideal.mem_span_singleton'→pG,Ideal.span→lI,Ideal.subset_span→pz,Irreducible→ oy,IsLocalization.Away.lift→pL,MvPolynomial.C→nq,MvPolynomial.eval→ ov,MvPolynomial.le_weightedTotalDegree→ oq,MvPolynomial.support_map_subset→ oZ,Nat.le_add_right→ oz,Nat.mul_le_mul_left→nI,Nat.succ_le_of_lt→pQ,aR.Shape→cy,aR.shape→lz,dN.GeoField→mD,dN.GeoJets→aU,dN.separant→lV,smul_eq_mul→ oY
set_option autoImplicit true
section
namespace aeM
noncomputable section
open Polynomial

open gW (bf)
open aR (af Shape bY)
open dN (bC su AX oA GeoJets kC YR Invariant pK)
open vS (oe g9)
open scoped BigOperators
def vU (g:af 4) :af 4 :=su g bf
def ZV (g:af 4) :af 4 :=su g (bf+1)
structure Branch (f Q:af 4) (l:ℕ) where
 aI:c9 aU
 r :ℕ
 base : (kC f Q).IsMinimalPrime aI
 high: (l:ℕ∞)≤oA (kC f Q) aI base.isPrime
 bY:YR f aI r
 invariant:Invariant ((lV^[r]) f) aI
 proper :bC (vU ((lV^[r]) f))∉aI
 curve :c9 aU
 divisor : (AX aI (vU ((lV^[r]) f))).IsMinimalPrime curve
 regularCurve :bC (lV ((lV^[r]) f))∉curve
 terminal :
   oA (AX aI (vU ((lV^[r]) f))) curve
     divisor.isPrime≠1∨bC (ZV ((lV^[r]) f))∉curve
namespace Branch
variable {f Q:af 4} {l:ℕ} (b:Branch f Q l)
def g:af 4 :=(lV^[b.r]) f
def sigma :GeoJets :=bC (lV b.g)
def member :GeoJets :=bC (vU b.g)
def next:GeoJets :=bC (ZV b.g)
def Simple :Prop :=oA (AX b.aI (vU b.g))
 b.curve b.divisor.isPrime=1
def weight:ℕ:= by classical exact if b.Simple then 1 else 2
def dY (p:oe) :Prop :=
 b.curve≤RingHom.ker (ov p)∧ov p b.sigma≠0
abbrev Local:=Localization.Away b.sigma
def vN :aU →+* b.Local:=algebraMap aU b.Local
def yu:g9 →+* b.Local :=
  MvPolynomial.eval₂Hom (b.vN.comp nq)
    (Fin.lastCases
      (b.vN (nq (-(4 :mD)⁻¹)*bC (pK b.g)) *
        IsLocalization.Away.invSelf b.sigma)
      (fun i=>b.vN (MvPolynomial.X i)))
def a5x :c9 b.Local:=b.curve.map b.vN
end Branch
def azb (p:cy) :Shape :=
 ⟨max p.b (p.j+1),p.j+1,p.t+1⟩
def aco (L:ℕ) (p:cy) :Shape :=
 let i:=4+(L - 5)*(p.j - 2)
 ⟨max (1+(L - 5)*(p.b - 1)) i,i,2+(L - 5)*p.t⟩
export ac7 (Sx FH)
end
end aeM
end
section
namespace aeM
noncomputable section
open Polynomial MvPolynomial
open aR (af)
open dN (j8 bC)
open aA5 (RT)
open aKq (Chart incl)
open scoped BigOperators
open private topWeight auY from ProximityPrize.SubmissionLower.A2
variable {f Q:af 4} {l:ℕ}
@[simp] theorem cad (b:Branch f Q l) (a :mD) :
   b.yu (nq a)=b.vN (nq a) := by
  simp [Branch.yu]
private def aAy (b:Branch f Q l) :Chart b.g →+* b.Local :=
 pL (lV b.g)
  (g:=b.vN.comp (MvPolynomial.map j8))
  (IsLocalization.Away.algebraMap_isUnit b.sigma)
@[simp] private theorem a87 (b:Branch f Q l) (P:af 4) :
   aAy b (incl b.g P)=b.vN (bC P) :=
  IsLocalization.Away.lift_eq _ _ _
local notation "aeq" => MvPolynomial.weightedTotalDegree
private theorem b60 (P:af 5) {b j t d:ℕ}
   (hb:aeq 1 P≤b) (hj:aeq Fin.val P≤j)
   (ht:aeq topWeight P≤t) (hd:aeq auY P≤d) :
   FH ⟨b,j,t⟩ d (RT P) := by
 intro m hm
 have hsource :=oZ j8 P hm
 have hb' := (oq (1 :Fin 5→ℕ) hsource).trans hb
 have hj' := (oq Fin.val hsource).trans hj
 have ht' := (oq topWeight hsource).trans ht
 have hd' := (oq auY hsource).trans hd
 rw [Finsupp.weight_eq_sum,Fin.sum_univ_castSucc] at hb' hj' ht'
 simp only [Pi.one_apply,oY ,mul_one] at hb'
 simp only [Fin.val_castSucc,Fin.val_last,oY] at hj'
 simp [topWeight,Pi.single_apply] at ht'
 refine ⟨hb',?_,?_,?_⟩
 · simpa only [Nat.mul_comm] using hj'
 · change m ((3:Fin 4).castSucc)+m (Fin.last 4)*2≤t at ht'
   simpa only [Nat.mul_comm] using ht'
 · simpa only [auY,Finsupp.weight_single_one_apply] using hd'
end
end aeM
end
section
namespace aeM
noncomputable section
open Polynomial
open P0 (K)
open aR (ao af embed)
open dN (j8)
open vS (g9)
open aA5 (RT denominator CJ)
open scoped BigOperators
open private iy ajW const centre asv factorial_ne_zero
 from ProximityPrize.SubmissionLower.BI
variable {f Q:af 4} {l:ℕ}
private theorem bds {M:ℕ} (hM:M≤K1.p) (T:ao[X]) (hT:T.natDegree<M) (x :ao) :
   (∑ i∈Finset.range M,asv x i*iy T i)=const (T.eval x) := by
 have hd: (Polynomial.taylor centre (T.map const)).natDegree<M:= by
   rw [Polynomial.natDegree_taylor]
   exact Polynomial.natDegree_map_le.trans_lt hT
 rw [← Polynomial.eval_map_apply const x,← Polynomial.taylor_eval_sub centre,
   Polynomial.eval_eq_sum_range' hd]
 apply Finset.sum_congr rfl
 intro i hi
 have hcent (P:ao[X]) : (P.map const).eval centre=j8 P:= by
   rw [Polynomial.eval_map]
   simpa only [Polynomial.eval₂_C_X] using
     (Polynomial.hom_eval₂ P Polynomial.C j8 Polynomial.X).symm
 rw [Polynomial.taylor_coeff,Polynomial.hasseDeriv_map,hcent]
 have hord:iy T i=(i.factorial:mD)*j8 (hasseDeriv i T) := by
   unfold iy
   rw [ajW,map_mul,Polynomial.C_eq_natCast,map_natCast]
 have hn:i<K1.p :=
   (Finset.mem_range.mp hi).trans_le hM
 rw [hord,asv]
 calc
   _=((i.factorial:mD)⁻¹*(i.factorial:mD)) *
         (j8 (hasseDeriv i T)*(const x - centre)^i) := by ring
   _ = _:= by rw [inv_mul_cancel₀ (factorial_ne_zero hn),one_mul]
private def bix (M:ℕ) (g:af 4) (k :ℕ) (x a :K) :g9 :=
 (∑ i∈Finset.range M,nq (asv (embed x) i) *
     RT (CJ g k i)) -
   nq (const (embed a))*RT (denominator g k)
private theorem b6Z {a :cy} {z :ℕ} {P:g9}
  (hP:FH a z P) (c:mD) :FH a z (nq c*P) := by
 intro m hm
 rw [MvPolynomial.mem_support_iff,MvPolynomial.coeff_C_mul] at hm
 exact hP m (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm))
private theorem cWs {α:Type*} {a :cy} {z :ℕ} (I:nX α) (P:α→ g9)
  (hP : ∀ i∈I,FH a z (P i)) :FH a z (∑ i∈I,P i) := by
 classical
 intro m hm
 obtain ⟨i,hi,hmi⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
 exact hP i hi m hmi
private theorem cWr {a :cy} {z :ℕ} {A B:g9}
  (hA:FH a z A) (hB:FH a z B) :FH a z (A - B) := by
 intro m hm
 exact (Finset.mem_union.mp (MvPolynomial.support_sub (Fin 5) A B hm)).elim (hA m) (hB m)
end
end aeM
end
section
namespace aeM
noncomputable section
open aR (af)
open dN (GeoJets bC kC oA)
open Dr (aIT aIc)
open private Be b7x from ProximityPrize.SubmissionLower.AH
private theorem dho (Q:af 4) (n:ℕ) :
  bC (Q^n)=bC Q^n:= by
 simp only [bC,map_pow]
private theorem bJe {f Q:af 4} {P:c9 aU}
   (h: (kC f Q).IsMinimalPrime P) {n:ℕ} (hn:0<n) :
   (kC f (Q^n)).IsMinimalPrime P:= by
 simp only [aIc,dho] at h ⊢
 let H :c9 GeoJets :=lI {bC f}
 let D:=bC Q
 have hspan:lI {D^n} ≤ lI {D} :=
   Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self D (Nat.ne_of_gt hn))
 refine ⟨⟨h.isPrime,(sup_le_sup_left hspan H).trans h.le⟩,?_⟩
 intro T hT hTP
 have hDT:D^n∈T :=
   hT.2 (Ideal.mem_sup_right (pz (Set.mem_singleton _)))
 have hle :H ⊔ lI {D} ≤ T :=
   sup_le (le_sup_left.trans hT.2)
     (Ideal.span_singleton_le_iff_mem T |>.mpr (hT.1.mem_of_pow_mem n hDT))
 exact h.2 ⟨hT.1,hle⟩ hTP
private theorem bIn {f Q:af 4} (hf :oy f) (hQ : ¬ f∣Q)
    (P:c9 aU) (hp:P.IsPrime) (n:ℕ) :
    oA (kC f (Q^n)) P hp =
      (n:ℕ∞)*oA (kC f Q) P hp:= by
  let H :c9 GeoJets :=lI {bC f}
  let D:=bC Q
  let I (j:ℕ) :=H ⊔ lI {D^j}
  let φ:=oD H
  have hreg:IsLeftRegular (φ D) :=
    aIT f Q (lB.amo f Q hf hQ)
  have mem (j:ℕ) (a :aU) :a∈I j↔φ a∈lI {φ D^j} := by
    change a∈H ⊔ lI {D^j} ↔ a∈(lI {φ D^j}).comap φ
    have hmap : (lI {D^j}).map φ=lI {φ D^j} := by
      rw [Ideal.map_span,Set.image_singleton,map_pow]
    rw [← hmap,show φ=oD H from rfl,Ideal.comap_map_quotientMk]
  have hcolon (j:ℕ) : (I (j+1)).colon {D} = I j:= by
    ext a
    rw [Submodule.mem_colon_singleton,oY ,mem (j+1) (a*D),mem j a,map_mul,
      pG,pG]
    constructor
    · rintro ⟨b,hb⟩
      refine ⟨b,hreg ?_⟩
      simpa only [pow_succ',mul_left_comm (φ D) b,mul_assoc,mul_comm (φ D) (φ a)]
        using hb
    · rintro ⟨b,hb⟩
      exact ⟨b,by rw [pow_succ,← mul_assoc,hb]⟩
  have hsup (j:ℕ) :I (j+1) ⊔ lI {D} = I 1 := by
    have hpow:lI {D^(j+1)} ≤ lI {D} :=
      Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self D (Nat.succ_ne_zero j))
    change (H ⊔ lI {D^(j+1)}) ⊔ lI {D} = H ⊔ lI {D^1}
    rw [sup_assoc,sup_eq_right.mpr hpow,pow_one]
  have hpow (j:ℕ) :kC f (Q^j)=I j:= by
    simp only [I,H,D,aIc,dho]
  have hbase :kC f Q=I 1 := by
    simpa only [pow_one] using hpow 1
  rw [hpow,hbase]
  change Be (I n) P hp=(n:ℕ∞)*Be (I 1) P hp
  induction n with
  | zero =>
    have htop:I 0 = ⊤ := by simp [I]
    rw [htop,Nat.cast_zero,zero_mul]
    let _:P.IsPrime :=hp
    let A:=Localization.AtPrime P
    let J:=(⊤ : c9 aU).map (algebraMap aU A)
    have hsub:Subsingleton (A ⧸ J) :=
      Ideal.Quotient.subsingleton_iff.mpr (Ideal.map_top _)
    exact Module.length_eq_zero_iff.mpr hsub
  | succ j ih =>
    rw [b7x (I (j+1)) P hp D,hcolon,hsup,ih,Nat.cast_succ,add_mul,one_mul]
end
end aeM
end
section
namespace aeM
noncomputable section
open aR (Shape iH Dn gI)

open vS (oe VE)
open Dr (ChamberBox capCoeff BE tW AN oF aPQ aCR aFq btI c4m bge)
open scoped BigOperators
private lemma Nc {x y :cy} (hx :lJ x) (hy :lJ y) :
  lJ (x.plus y) := by
 obtain ⟨hx₁,hx₂,hx₃⟩:=hx
 obtain ⟨hy₁,hy₂,hy₃⟩:=hy
 refine ⟨Nat.add_le_add hx₁ hy₁,?_,Nat.add_pos_left hx₃ _⟩
 change 3*(x.t+y.t)≤x.j+y.j
 omega
private lemma aWr {A B:cy→ℚ} (h : ∀ p,lJ p→A p=B p)
   {boxes :List cy} (hboxes : ∀ q∈boxes,lJ q) {p:cy}
   (hp:lJ p) :BE A boxes p=BE B boxes p:= by
 induction boxes generalizing p with
 | nil=>exact h p hp
 | cons q boxes ih =>
   have hq:=hboxes q List.mem_cons_self
   have hr := fun r hr=>hboxes r (List.mem_cons_of_mem _ hr)
   simp only [BE,ih hr (Nc hp hq),ih hr hp]
private lemma blq (h:Dr.c1) {p q r s :cy}
   (hp:lJ p) (hq:lJ q) (hr :lJ r) (hs :lJ s) :
   tW (⊥ : c9 aU) [p,q,r,s]≤(iH p q r s :ℚ)/32 := by
 have hb:lJ ⟨3, 3,1⟩:=⟨by decide,by decide,by decide⟩
 have hboxes : ∀ u∈[p,q,r,s],ChamberBox u:= by
   intro u hu
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
   rcases hu with rfl | rfl | rfl | rfl
   · exact hp
   · exact hq
   · exact hr
   · exact hs
 unfold tW
 change BE (capCoeff ⊥ 4) [p,q,r,s] ⟨3,3,1⟩/(2 :ℚ)^4≤_
 rw [aWr h hboxes hb]
 let n:=gI (gI (gI (gI Dn p) q) r) s ⟨0,0,0⟩
 have hpoly :BE (fun x=>16*(Dn x :ℚ)/32) [p,q,r,s] ⟨3,3,1⟩ /
     (2 :ℚ)^4=(n:ℚ)/32 := by
   simp only [n,BE,gI,Dn,Shape.plus]
   push_cast
   ring
 rw [hpoly]
 have hn:n≤(n.toNat :ℤ) := by omega
 apply div_le_div_of_nonneg_right _ (by norm_num)
 exact_mod_cast hn
private lemma eMr {J:c9 aU} (hJ:oj J=0)
  (x :oe) (hx :J≤oF x) :J.IsMinimalPrime (oF x) := by
 have :Module.Finite mD (aU ⧸ J) :=
  MvPolynomial.natDegree_affineHilbertPolynomial_eq_zero_iff.mp hJ
 have :IsArtinianRing (aU ⧸ J) :=IsArtinianRing.of_finite mD _
 have :Ring.KrullDimLE 0 (aU ⧸ J) :=isArtinianRing_iff_krullDimLE_zero.mp ‹_›
 have hp:=c4m x
 change oF x∈J.minimalPrimes
 rw [Ideal.minimalPrimes_eq_comap]
 refine ⟨(oF x).map (oD J),?_,Ideal.comap_map_mk hx⟩
 have :=Ideal.isPrime_map_quotientMk_of_isPrime hx
 exact Ideal.mem_minimalPrimes_of_krullDimLE_zero _
private lemma cc1 (h2 :Dr.c2) (h3:Dr.c3) {C:c9 aU} (hC:C.IsPrime)
    (hdim:oj C=1) {s :cy} (hs :lJ s)
    {D:aU} (hD:VE s D) (hproper :D∉C) (T:nX oe)
    (hT : ∀ x∈T,C≤oF x∧ov x D =0) :
    (T.card:ℚ)≤tW C [s] := by
  classical
  let J:=C ⊔ lI {D}
  have hreg:=aPQ hC hproper
  have hJ:oj J=0:= by
    have hdrop:=aCR hreg
    change oj J≤oj C - 1 at hdrop
    omega
  have hmin (x :oe) (hx :x∈T) :J.IsMinimalPrime (oF x) :=
    eMr hJ x (sup_le (hT x hx).1 ((oF x).span_singleton_le_iff_mem.mpr (hT x hx).2))
  calc
    (T.card:ℚ) = ∑ _x∈T,(1 :ℚ) := by simp
    _ ≤ ∑ x∈T,(AN J (oF x) :ℚ)*tW (oF x) [] := by
      apply Finset.sum_le_sum
      intro x hx
      rw [bge,mul_one]
      exact_mod_cast pQ (aFq (hmin x hx))
    _ = ∑ P∈T.image oF,(AN J P:ℚ)*tW P [] :=
      (Finset.sum_image (f := fun P=>(AN J P:ℚ)*tW P [])
        btI.injOn).symm
    _≤tW J [] :=h3 J [] (by simp) (by simp [hJ]) _ (by
      intro P hP
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hP
      exact hmin x hx)
    _≤tW C [s] :=h2 C s [] hs (by simp) (by simp [hdim]) D hD hreg
end
end aeM
end
section
namespace aeM
open aR (af Shape aO iH)

open lB (bF)
open MvPolynomial
open private Q9 bwo a8w from ProximityPrize.SubmissionLower.T
open private bNV from ProximityPrize.SubmissionLower.CH
theorem aME {Q:af 4} {q:cy} (hQ:aO (lz Q) q) (n:ℕ) :
  aO (lz (Q^n)) (q.scale n) := by
 refine ⟨(totalDegree_pow Q n).trans (nI n hQ.1),?_,
  (degreeOf_pow_le 3 Q n).trans (nI n hQ.2.2)⟩
 change aR.qE (Q^n)≤n*q.j
 rw [Ex.C6]
 exact (weightedTotalDegree_pow_le _ Q n).trans
  (nI n ((Ex.C6 Q) ▸ hQ.2.1))
def aby (q:cy) (n:ℕ) :Shape :=(q.scale n).plus ⟨3, 3,1⟩
theorem bP1 {q:cy} (hq:bF q) (n:ℕ) :lJ (aby q n) := by
 have hj:=nI n hq.1
 have ht:=nI n hq.2
 rw [← Nat.mul_left_comm 3 n] at ht
 change n*q.j+3≤n*q.b+3∧3*(n*q.t+1)≤n*q.j+3∧0<n*q.t+1
 omega
private theorem dLP (a b:ℤ) (n:ℕ) :
  ((n:ℤ)*a+b).toNat≤n*a.toNat+b.toNat := by
 have ha :a≤(a.toNat :ℤ) := by omega
 have hb:b≤(b.toNat :ℤ) := by omega
 apply Int.toNat_le.mpr
 push_cast
 exact add_le_add (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg n)) hb
theorem bJl (p q r s :cy) (n:ℕ) :
  iH p (aby q n) r s≤n*iH p q r s+iH p ⟨3, 3,1⟩ r s := by
 change (Q9 p (aby q n) r s).toNat ≤
  n*(Q9 p q r s).toNat+(Q9 p ⟨3, 3,1⟩ r s).toNat
 rw [a8w p (aby q n) r s,a8w p q r s,
  a8w p ⟨3, 3,1⟩ r s,aby,bwo]
 have hs :Q9 (q.scale n) r s p=(n:ℤ)*Q9 q r s p :=
  bNV n q r s p
 rw [hs]
 exact dLP _ _ n
theorem aQ3 {n a b e :ℕ} (he :e<n) (h:n*a≤n*b+e) :a≤b:= by
 by_contra! hbad
 have hstrict :=nI n (pQ hbad)
 rw [Nat.mul_succ] at hstrict
 omega
end aeM
end
section
namespace aSm
noncomputable section
open aR (af aO iH)
open dN (kC oA)
open GJ (vE Ux)
open lB (bF amo abr)
open aeM (aby bP1 aME bJl aQ3)
open aeM (bJe bIn)
open private bPY agr from ProximityPrize.SubmissionLower.B5
open scoped BigOperators
theorem dl4 {f Q:af 4} (p q a h:cy)
    (hf :oy f) (hQ : ¬ f∣Q) (hp:vE p) (hq:bF q)
    (ha :vE a) (hh:vE h)
    (hfb:aO (lz f) p) (hQb:aO (lz Q) q)
    (uG:nX (c9 aU)) (v :c9 aU→ℕ)
    (hlen : ∀ aI∈uG,∃ hs : (kC f Q).IsMinimalPrime aI,
      oA (kC f Q) aI hs.isPrime=(v aI:ℕ∞)) :
    32*(∑ aI∈uG,v aI*Ux aI (a.scale 6) (h.scale 6)) ≤
      36*iH p q a h:= by
  let e :=36*iH p ⟨3, 3,1⟩ a h
  let n:=e+1
  have hn:0<n:=Nat.succ_pos e
  have hch:=bP1 hq n
  have hfull:vE (aby q n) :=⟨⟨hch.1,hch.2.1⟩,hch.2.2⟩
  have hprime :=UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  have hproper : ¬ f∣Q^n:= fun hd=>hQ (hprime.dvd_of_dvd_pow hd)
  have hnonzero :=agr (show Q^n≠0 from fun hz=>hproper (hz.symm ▸ dvd_zero f))
  have hb:=aME hQb n
  have hpbox :aO (lz (Q^n)) (aby q n) :=
    ⟨hb.1.trans (oz _ _),hb.2.1.trans (oz _ _),
      hb.2.2.trans (oz _ _)⟩
  have hweights (aI:c9 aU) (hs :aI∈uG) :
      ∃ hs' : (kC f (Q^n)).IsMinimalPrime aI,
        oA (kC f (Q^n)) aI hs'.isPrime=(↑(n*v aI) :ℕ∞) := by
    obtain ⟨hs',hv⟩:=hlen aI hs
    refine ⟨bJe hs' hn,?_⟩
    rw [bIn hf hQ,hv,Nat.cast_mul]
  have hbound:=bPY _ _ p (aby q n) a h
    (agr hf.ne_zero) hnonzero (amo f (Q^n) hf hproper)
    hp hfull ha hh (abr hfb) (abr hpbox) uG _ hweights
  simp only [Nat.mul_assoc,← Finset.mul_sum] at hbound
  apply aQ3 (Nat.lt_succ_self e)
  calc
    _=32*(n * ∑ aI∈uG,v aI*Ux aI (a.scale 6) (h.scale 6)) := by
      ac_rfl
    _≤36*iH p (aby q n) a h:=hbound
    _≤36*(n*iH p q a h+iH p ⟨3, 3,1⟩ a h) :=
      nI _ (bJl p q a h n)
    _ = _:= by rw [Nat.mul_add]; dsimp only [e]; ac_rfl
end
end aSm
end
