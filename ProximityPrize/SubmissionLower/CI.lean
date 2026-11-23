import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.DY
import ProximityPrize.SubmissionLower.AR
import ProximityPrize.SubmissionLower.Z0omYcd
set_option Elab.async false
set_option autoImplicit true
section
namespace dpg
noncomputable section
open Polynomial
open P4 (I K)
open bJ (Bank Pq Contact aRG Dj tB gZ)
open aR (ao af aO shape qE cK)

open private yZ ajI bpc from ProximityPrize.SubmissionLower.AB
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent:=Fin 4 →₀ ℕ
private def kO (m:Exponent) :ℕ :=
 m.sum (fun i a=>(gZ - i.val)*a)
private theorem aaG {b:Bank} {w:I→K} {T:ℕ} {P:af 4} :
    Pq b w T P ↔
      (∀ m∈P.support,m.sum (fun _ a=>a)≤b.box.b ∧
        m.sum (fun i a=>i.val*a)≤b.box.j∧m 3≤b.box.t ∧
        m 1+m 2+m 3≤Dj (m.sum (fun _ a=>a)) ∧
        (P.coeff m).natDegree+kO m≤T)∧Contact b w P:= by
  simp only [Pq,aO,shape,qE,MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff,Finset.sup_le_iff,aRG,tB]
  constructor
  · rintro ⟨⟨hb,hj,ht⟩,hp,hT,hc⟩
    exact ⟨fun m hm=>⟨hb m hm,hj m hm,ht m hm,hp m hm,hT m hm⟩,hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨⟨fun m hm=>(h m hm).1,fun m hm=>(h m hm).2.1,fun m hm=>(h m hm).2.2.1⟩,
      fun m hm=>(h m hm).2.2.2.1,fun m hm=>(h m hm).2.2.2.2,hc⟩
private def aV (b:Bank) (w:I→K) (T:ℕ) :Submodule ao (af 4) where
  carrier := {P | Pq b w T P}
  zero_mem' := by
    apply aaG.mpr
    simp [Contact,cK]
  add_mem' {P Q} hP hQ:= by
    obtain ⟨hP,hp⟩:=aaG.mp hP
    obtain ⟨hQ,hq⟩:=aaG.mp hQ
    apply aaG.mpr
    constructor
    · intro m hm
      have hor :=Finset.mem_union.mp (MvPolynomial.support_add hm)
      have Ca :
          m.sum (fun _ a=>a)≤b.box.b∧m.sum (fun i a=>i.val*a)≤b.box.j ∧
            m 3≤b.box.t∧m 1+m 2+m 3≤Dj (m.sum (fun _ a=>a)) ∧
            kO m≤T:= by
        rcases hor with h | h
        · obtain ⟨hb,hj,ht,hprofile,hw⟩:=hP m h
          exact ⟨hb,hj,ht,hprofile,by omega⟩
        · obtain ⟨hb,hj,ht,hprofile,hw⟩:=hQ m h
          exact ⟨hb,hj,ht,hprofile,by omega⟩
      obtain ⟨hb,hj,ht,hprofile,hw⟩:=Ca
      refine ⟨hb,hj,ht,hprofile,?_⟩
      have hsum: ((P+Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m)+(Q.coeff m)).natDegree≤_
        exact natDegree_add_le _ _
      have hdegree (R:af 4) (hR:m∈R.support→(R.coeff m).natDegree+kO m≤T) :
          (R.coeff m).natDegree≤T - kO m:= by
        by_cases h:m∈R.support
        · have :=hR h
          omega
        · have hz :R.coeff m=0:= by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz,natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h=>(hP m h).2.2.2.2)
      have hq' := hdegree Q (fun h=>(hQ m h).2.2.2.2)
      have :=hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← ajI,map_add,ajI,ajI]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP:= by
    obtain ⟨hP,hp⟩:=aaG.mp hP
    apply aaG.mpr
    constructor
    · intro m hm
      obtain ⟨hb,hj,ht,hprofile,hw⟩:=hP m (MvPolynomial.support_smul hm)
      refine ⟨hb,hj,ht,hprofile,?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h:yZ S (c•P)=c•yZ S P:=(yZ S).map_smul c P
      rw [ajI,ajI] at h
      rw [h]
      exact bpc _ _ c (hp i S hS)
private def bnp (b:Bank) (T:ℕ) :
    af 4 →ₗ[ao] (((Fin 4→Fin (b.box.b+1))×Fin (T+1))→ao) :=
  LinearMap.pi fun u =>
    (Polynomial.lcoeff ao u.2.val).comp
      ((MvPolynomial.lcoeff ao[X] (Finsupp.equivFunOnFinite.symm (fun i=>(u.1 i).val))
        : af 4 →ₗ[ao[X]] ao[X]).restrictScalars ao)
private instance bqa (b:Bank) (w:I→K) (T:ℕ) :Module.Finite ao (aV b w T) := by
  classical
  let f :aV b w T →ₗ[ao] (((Fin 4→Fin (b.box.b+1))×Fin (T+1))→ao) :=
    (bnp b T).comp (aV b w T).subtype
  have hzero (Q:aV b w T) (hQ:f Q=0) :Q=0:= by
    obtain ⟨P,hP⟩:= Q
    change Pq b w T P at hP
    apply Subtype.ext
    change P=0
    apply MvPolynomial.ext
    intro m
    change _=0
    by_contra hnz
    have hm:=MvPolynomial.mem_support_iff.mpr hnz
    have hT: (P.coeff m).natDegree≤T:=(Nat.le_add_right _ _).trans (hP.2.2.1 m hm)
    let u:Fin 4→Fin (b.box.b+1) := fun i=>⟨m i,Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk :k<T+1
    · have hval :=congrFun hQ (u,⟨k,hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i=>(u i).val))).coeff k=0 at hval
      have heq :Finsupp.equivFunOnFinite.symm (fun i=>(u i).val)=m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz :=f.map_sub P Q
  rw [h,sub_self] at hz
  exact hzero (P-Q) hz
end
end dpg
end
section
namespace bj0
open aR (Shape Dn gI iH)
open yi (bF)
open Ds (wP)
private theorem a2j (p:Shape) (h:bF p) :
  (p.b:ℤ)=(↑(p.b - p.j) :ℤ) + ↑(p.j-3*p.t)+3*p.t ∧
  (p.j:ℤ)=(↑(p.j-3*p.t) :ℤ)+3*p.t:= by
 obtain ⟨hb,hj⟩:=h
 constructor <;> exact_mod_cast (by omega :_)
private theorem bwp (p q r s :Shape) (hq:bF q) (hr :bF r)
  (hs :bF s) :0≤wP p q r s := by
 obtain ⟨hqb,hqj⟩:=a2j q hq
 obtain ⟨hrb,hrj⟩:=a2j r hr
 obtain ⟨hsb,hsj⟩:=a2j s hs
 simp only [wP,gI,Dn,Shape.plus,Nat.cast_add]
 rw [hqb,hqj,hrb,hrj,hsb,hsj]
 ring_nf
 positivity
private theorem aCz (p q r s :Shape) (hq:bF q) (hr :bF r)
  (hs :bF s) : (iH p q r s :ℤ)=wP p q r s :=
 Int.toNat_of_nonneg (bwp p q r s hq hr hs)
def slope :Shape :=⟨1,4, 2⟩
private theorem cpC (p q x y z :Shape) :
  wP p q (x.plus y) z=wP p q x z+wP p q y z := by
 simp only [wP,gI,Dn,Shape.plus,Nat.cast_add]
 ring
private theorem aJv (p q x y :Shape) :
  wP p q x y=wP p q y x := by
 simp only [wP,gI,Dn,Shape.plus,Nat.cast_add]
 ring
private theorem cpB (p q x y z :Shape) :
  wP p q x (y.plus z)=wP p q x y+wP p q x z := by
 rw [aJv p q x,cpC,aJv p q y,aJv p q z]
private theorem gq4 (p q x y :Shape) (v :ℕ) :
    wP p q x (y.scale v)=(v :ℤ)*wP p q x y := by
  induction v with
  | zero =>
      have h:y.scale 0=⟨0,0,0⟩:= by simp [Shape.scale]
      rw [h]
      simp [wP,gI,Shape.plus]
  | succ v ih =>
      have h:y.scale (v+1)=(y.scale v).plus y := by
        cases y
        simp [Shape.scale,Shape.plus,Nat.add_mul]
      rw [h,cpB,ih,Nat.cast_succ]
      ring
private theorem gq5 (p q g a b:Shape) (u v :ℕ) :
    wP p q a (b.plus (slope.scale v)) +
        (u:ℤ)*wP p q (g.plus slope) (b.plus (slope.scale v)) +
        (v :ℤ)*wP p q (g.plus slope) a -
      ((u:ℤ)*wP p q slope (b.plus (slope.scale v)) +
        (v :ℤ)*wP p q slope a +
        (u:ℤ)*(v :ℤ) *
          (wP p q slope (g.plus slope) - wP p q slope slope)) =
    wP p q a (b.plus (slope.scale v)) +
      (u:ℤ)*wP p q g b+(v :ℤ)*wP p q g a := by
  have h:=cpB p q g b (slope.scale v)
  rw [gq4,aJv p q g slope] at h
  rw [cpC p q g slope,cpC p q g slope,
    cpB p q slope g slope,h]
  ring
theorem bN4 (p q g a b g' b' : Shape) (u v :ℕ)
    (hg:g=g'.plus slope) (hb:b=b'.plus (slope.scale v))
    (hq:bF q) (hgc:bF g) (ha :bF a) (hbc:bF b)
    (hg' : bF g') (hb' : bF b') :
    ((↑(iH p q a b+u*iH p q g b+v*iH p q g a) :ℤ) -
      ((u:ℤ)*wP p q slope b+(v :ℤ)*wP p q slope a +
        (u:ℤ)*(v :ℤ) *
          (wP p q slope g - wP p q slope slope))).toNat =
    iH p q a b+u*iH p q g' b' + v*iH p q g' a := by
  have h:=gq5 p q g' a b' u v
  rw [← hg,← hb] at h
  simp only [Nat.cast_add,Nat.cast_mul,aCz p q a b hq ha hbc,
    aCz p q g b hq hgc hbc,aCz p q g a hq hgc ha]
  rw [h]
  rw [← aCz p q a b hq ha hbc,← aCz p q g' b' hq hg' hb',
    ← aCz p q g' a hq hg' ha,← Nat.cast_mul,← Nat.cast_mul,
    ← Nat.cast_add,← Nat.cast_add]
  exact Int.toNat_natCast _
end bj0
end
section
namespace bj0
open aR (Shape aO qP)
open yi (bF)
open Ds (bf)
private def shift (k :ℕ) (x :Shape) :Shape :=
 ⟨x.b - k,x.j-4*k,x.t - 2*k⟩
private theorem shift_add {k :ℕ} {x :Shape} (hc:bF x) (ht:2*k≤x.t) :
  x=(shift k x).plus (slope.scale k) := by
 rcases x with ⟨b,j,t⟩
 obtain ⟨hb,hj⟩:=hc
 change j≤b at hb
 change 3*t≤j at hj
 change 2*k≤t at ht
 simp only [shift,Shape.plus,Shape.scale,slope,Nat.mul_one]
 congr 1 <;> omega
private theorem acJ {k :ℕ} {x :Shape} (hc:bF x) (ht:2*k≤x.t) :
  bF (shift k x) := by
 obtain ⟨hb,hj⟩:=hc
 change x.j-4*k≤x.b - k∧3*(x.t - 2*k)≤x.j-4*k
 omega
private theorem aET (k :ℕ) {x y :Shape} (h:aO x y) :
   aO (shift k x) (shift k y) :=
 ⟨Nat.sub_le_sub_right h.1 _,Nat.sub_le_sub_right h.2.1 _,Nat.sub_le_sub_right h.2.2 _⟩
private def arE (p:Shape) :Prop :=
 let u:=bf+1
 let v :=bf+2
 let a :=qP u p
 let b:=qP v p
 3*(p.t+1)≤p.j+1∧2≤p.t+1 ∧
   3*(2+(u - 5)*p.t)≤a.j∧3*(2+(v - 5)*p.t)≤b.j ∧
   2*u≤a.t∧2*v≤b.t
private instance (p:Shape) :Decidable (arE p) := by
 unfold arE
 infer_instance
end bj0
end
section
namespace Jt
open aR (Shape)
structure fQ where
 lowerB:ℕ
 upperB:ℕ
 lowerJ:ℕ
 upperJ:ℕ
def fQ.dY (a :fQ) (s :Shape) :Prop :=
 a.lowerB≤ s.b∧s.b≤a.upperB∧a.lowerJ≤ s.j∧s.j≤a.upperJ
end Jt
end
