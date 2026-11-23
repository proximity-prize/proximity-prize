import ProximityPrize.SubmissionLower.Zzjdkoa
import ProximityPrize.SubmissionLower.Zay1XCa
import ProximityPrize.SubmissionLower.ZsE91Ed
set_option Elab.async false
section
namespace qYVN5fe
noncomputable section
open Finset Polynomial
open qAW6lac (Index jo block)
open cu (L)
abbrev lK (K:Type) [Semiring K] :=Polynomial (Polynomial K)
abbrev Moving (d s W:ℕ) (k :Fin 3) := {i:Index d s W // block i=k}
abbrev Fixed (d s W:ℕ) (k :Fin 3) := {i:Index d s W // block i≠k}
abbrev FixedRing (d s W:ℕ) (k :Fin 3) :=MvPolynomial (Fixed d s W k) L
abbrev Ground (d s W:ℕ) (k :Fin 3) :=FractionRing (FixedRing d s W k)
abbrev SplitRing (d s W:ℕ) (k :Fin 3) :=
 MvPolynomial (Moving d s W k) (FixedRing d s W k)
abbrev LocalRing (d s W:ℕ) (k :Fin 3) :=
 MvPolynomial (Moving d s W k) (Ground d s W k)
def iS (d s W:ℕ) (k :Fin 3) :
    Index d s W ≃ Moving d s W k ⊕ Fixed d s W k :=
  (Equiv.sumCompl (fun i:Index d s W=>block i=k)).symm
def splitCoeff (d s W:ℕ) (k :Fin 3) :jo d s W ≃+* SplitRing d s W k :=
  (MvPolynomial.renameEquiv L (iS d s W k)).toRingEquiv.trans
    (MvPolynomial.sumRingEquiv L _ _)
def localizeCoeff (d s W:ℕ) (k :Fin 3) :SplitRing d s W k →+* LocalRing d s W k :=
 MvPolynomial.map (algebraMap (FixedRing d s W k) (Ground d s W k))
def left (k :Fin 3) :Fin 3:=if k=0 then 1 else 0
def right (k :Fin 3) :Fin 3:=if k=2 then 1 else 2
def yCap (d:ℕ) (k :Fin 3) :ℕ:=if k=2 then d-1 else d
def wCap (s W:ℕ) (k :Fin 3) :ℕ:=if k=2 then W-s else W
def xDeg {d s W:ℕ} : Index d s W→ℕ
 | .inl i=>i.val.2.val
 | .inr (.inl i)=>i.val.2.val
 | .inr (.inr i)=>i.val.2.val
def yDeg {d s W:ℕ} : Index d s W→ℕ
 | .inl i=>i.val.1.val
 | .inr (.inl i)=>i.val.1.val
 | .inr (.inr i)=>i.val.1.val
def form {K:Type} [CommRing K] {d s W:ℕ} (u:Index d s W→K) (j:Fin 3) :
    lK K :=
  ∑ i,if block i=j then Polynomial.monomial (yDeg i) (Polynomial.monomial (xDeg i) (u i)) else 0
def fixedVars {d s W:ℕ} (k :Fin 3) (i:Index d s W) :Ground d s W k :=
 if h:block i=k then 0 else algebraMap (FixedRing d s W k) (Ground d s W k) (MvPolynomial.X ⟨i,h⟩)
def pairForm (d s W:ℕ) (k j:Fin 3) :lK (Ground d s W k) :=
 form (fixedVars k) j
abbrev pairQuot {K:Type} [Field K] (F G:lK K) :=
 lK K ⧸ Ideal.span ({F,G} : Set (lK K))
abbrev PairAlgebra (d s W:ℕ) (k :Fin 3) :=
 pairQuot (pairForm d s W k (left k)) (pairForm d s W k (right k))
def splitForm (d s W:ℕ) (k j:Fin 3) :lK (SplitRing d s W k) :=
 form (fun i=>splitCoeff d s W k (MvPolynomial.X i)) j
def localForm (d s W:ℕ) (k j:Fin 3) :lK (LocalRing d s W k) :=
 form (fun i=>localizeCoeff d s W k (splitCoeff d s W k (MvPolynomial.X i))) j
end
end qYVN5fe
end
section
namespace qpVvmab
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation)
open qZV9OWb (ValueSlice)
open qAW6lac (Index jo actualCoeffs aMp)
abbrev Series (E :Type) [Field E] :=PowerSeries (AlgebraicClosure E)
abbrev Direction {E :Type} [Field E] (A:Equation E) :=
 Index A.d A.s (A.b+A.d*A.s)→L
abbrev actual {E :Type} [Field E] [Algebra L E] (A:Equation E) (B:ValueSlice A) :
  Index A.d A.s (A.b+A.d*A.s)→E :=
 actualCoeffs A.f B.g A.f.derivative
def base {E :Type} [Field E] [Algebra L E] {d s W:ℕ}
    (α:Index d s W→E) (δ:Index d s W→L) (i:Index d s W) :Series E :=
  PowerSeries.C (algebraMap E (AlgebraicClosure E) (α i)) +
    algebraMap L (Series E) (δ i)*PowerSeries.X
def sample {E :Type} [Field E] [Algebra L E] {d s W:ℕ}
    (α:Index d s W→E) (δ:Index d s W→L) (Q:jo d s W) :E :=
  Q.eval₂ (algebraMap L E) (fun i=>α i+algebraMap L E (δ i))
structure Lift {E :Type} [Field E] [Algebra L E] (A:Equation E) (B:ValueSlice A)
   (δ:Direction A) where
 x :Fin B.size→Series E
 y :Fin B.size→Series E
 x₀ : ∀ i,PowerSeries.constantCoeff (x i)=(B.point i).1
 y₀ : ∀ i,PowerSeries.constantCoeff (y i)=(B.point i).2
 f_zero : ∀ i,aMp (fun j=>base (actual A B) δ (.inl j)) (x i) (y i)=0
 g_zero : ∀ i,aMp (fun j=>base (actual A B) δ (.inr (.inl j))) (x i) (y i)=0
def value {E :Type} [Field E] [Algebra L E] (A:Equation E) (B:ValueSlice A)
    (δ δ' : Direction A) (U:Lift A B δ) (i:Fin B.size) :Series E :=
  aMp (fun j=>base (actual A B) δ' (.inr (.inr j))) (U.x i) (U.y i)
end
end qpVvmab
end
section
namespace qFe6O4d
noncomputable section
open TrivSqZeroExt
open cu (FX)
open qJai0ob (pair pair_fst pair_snd)
theorem change_denominator (p q a b t:FX) (hm:t*q-p≠0) :
  b+(b*p-a*q)/(t*q-p)=(t*b-a)*q/(t*q-p) := by
 apply (eq_div_iff hm).mpr
 rw [add_mul,div_mul_cancel₀ _ hm]
 ring
theorem parameter_change (p q a b a₁ b₁ t u:FX)
   (hq:q≠0) (hm:t*q-p≠0) (hD:t*b-a≠0) :
   let m:=t*q-p
   let D:=t*b-a
   let k :=(b₁*p-a₁*q)*m
   let W:=pair ((b*p-a*q)/m) u
   pair a a₁+inl t*W=(pair b b₁+W)*pair (p/q) ((m^2*u-k)/(D*q^2)) := by
 have hB:=change_denominator p q a b t hm
 dsimp only
 apply TrivSqZeroExt.ext
 · simp only [fst_add,fst_mul,fst_inl,pair_fst,hB]
   field_simp [hq,hm]
   ring
 · simp only [fst_add,snd_add,DualNumber.snd_mul,fst_inl,snd_inl,pair_fst,pair_snd,
     hB,zero_mul,add_zero]
   field_simp [hq,hm,hD]
   ring
theorem first_order (n:ℕ) (b b₁ w q m D k φ j₁ j i₀ i₁ i:FX)
   (hz :b+w≠0) (hq:q≠0) (hm:m≠0) (hD:D ≠0) (hj:j≠0)
   (hφ:φ = -(j₁/j)*q^2)
   (he : ∀ u:FX,pair i₀ (i₁+u*i) =
     (pair b b₁+pair w u)^n*pair 0 (j₁+((m^2*u-k)/(D*q^2))*j)) :
   i₀=0∧i≠0 ∧ -(i₁/i)*m^2=D*φ+k := by
 have hI:i₀=0:= by
   simpa only [fst_mul,fst_pow,fst_add,pair_fst,mul_zero] using congrArg fst (he 0)
 let z :=(b+w)^n
 have hs (u:FX) :i₁+u*i=z*(j₁+((m^2*u-k)/(D*q^2))*j) := by
   simpa only [DualNumber.snd_mul,snd_add,fst_pow,fst_add,pair_fst,pair_snd,
     mul_zero,add_zero,z] using congrArg snd (he u)
 have hsep:i=z*(m^2/(D*q^2)*j) := by
   linear_combination hs 1 - hs 0
 have hq2 :=pow_ne_zero 2 hq
 have hm2 :=pow_ne_zero 2 hm
 have hi:i≠0:=hsep ▸ mul_ne_zero (pow_ne_zero n hz)
   (mul_ne_zero (div_ne_zero hm2 (mul_ne_zero hD hq2)) hj)
 let u:=(D*φ+k)/m^2
 have hv : (m^2*u-k)/(D*q^2)=φ/q^2 := by
   change (m^2*((D*φ+k)/m^2)-k)/(D*q^2)= _
   rw [← mul_div_assoc,mul_div_cancel_left₀ _ hm2,add_sub_cancel_right]
   field_simp [hD,hq]
 have hroot :j₁+φ/q^2*j=0:= by
   rw [hφ,mul_div_cancel_right₀ _ hq2,neg_mul,div_mul_cancel₀ _ hj,add_neg_cancel]
 have hlin:i₁+u*i=0:= by rw [hs,hv,hroot,mul_zero]
 have heq : -(i₁/i)=u:= by
   rw [← neg_div,div_eq_iff hi]
   linear_combination -hlin
 exact ⟨hI,hi,by rw [heq]; exact div_mul_cancel₀ _ hm2⟩
end
end qFe6O4d
end
section
namespace qCe4xzb
noncomputable section
open Polynomial
open cu (L FX)
open P5 (K)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qb0hmCe (CurveModel)
def weightAt {R:Type} [Semiring R] (f :R[X][X]) (D:ℕ) :ℕ :=
 f.support.sup fun i=>(f.coeff i).natDegree+i*D
def physicalChart {R:Type} [Semiring R] (f :R[X][X]) (w D:ℕ) :R[X][X] :=
 f.sum fun i g=>monomial i (g.reflect (w-i*D))
def ordinateChart {R:Type} [CommRing R] (f :R[X][X]) (d:ℕ) (b:R) :R[X][X] :=
 (f.taylor (C b)).reflect d
def equation {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet Cq z S) (D:ℕ) (b:L) :Cq.E[X][X] :=
  ordinateChart (physicalChart F.f (weightAt F.f D) D) F.d (algebraMap L Cq.E b)
abbrev invertX:FX ≃+* FX:=(qWIOgVd.bY 0).changeX
end
end qCe4xzb
end
section
namespace qCe4xzb
noncomputable section
open Polynomial
open cu (L)
open P5_7_7 (phys)
open qWIOgVd (x phys_inj phys_ne)
open qps5rle (finiteAt)
theorem reflect_physical (g:L[X]) (n:ℕ) (h:g.natDegree≤n) :
  phys (g.reflect n)=x^n*invertX (phys g) := by
 simpa only [qWIOgVd.rev,taylor_zero] using (qWIOgVd.bY 0).CJ g n h
theorem invertX_eval :
   invertX.toRingHom.comp phys=eval₂RingHom (phys.comp C) x⁻¹:= by
 apply Polynomial.ringHom_ext
 · intro c
   change invertX (phys (C c))= _
   rw [(qWIOgVd.bY 0).constant]
   simp
 · change invertX x= _
   have h:=reflect_physical (Polynomial.X:L[X]) 1 (by simp)
   have hr : (Polynomial.X:L[X]).reflect 1=1 := by
    rw [← pow_one (Polynomial.X:L[X]),reflect_monomial,revAt_le le_rfl,Nat.sub_self,pow_zero]
   rw [hr] at h
   simp only [map_one,pow_one] at h
   simpa only [coe_eval₂RingHom,eval₂_X] using eq_inv_of_mul_eq_one_right h.symm
theorem degree_of_regular {n d:L[X]} {D:ℕ} (hd:d≠0)
   (h:finiteAt 0 (x^D *invertX (phys n/phys d))) :
   n.natDegree≤D+d.natDegree := by
 by_contra! hlt
 let k :=n.natDegree-(D+d.natDegree)
 have hk :k≠0:=Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)
 have hsum:n.natDegree=k+(D+d.natDegree) :=(Nat.sub_add_cancel hlt.le).symm
 have hn:n≠0:= by
   intro hz
   simp [hz] at hlt
 obtain ⟨a,b,hb,h⟩:=h
 rw [← coeff_zero_eq_eval_zero] at hb
 have hb' : phys b≠0:=phys_ne (fun hz=>hb (by simp [hz]))
 have hd' : invertX (phys d)≠0:= by simpa only [map_zero] using invertX.injective.ne (phys_ne hd)
 change x^D *invertX (phys n/phys d)=phys a/phys b at h
 rw [map_div₀,← mul_div_assoc] at h
 have hm:=(div_eq_div_iff hd' hb').mp h
 have he :phys n.reverse*phys b=phys (Polynomial.X^k*(d.reverse*a)) := by
   rw [reverse,reflect_physical n _ le_rfl,map_mul,map_pow,map_mul,reverse,
     reflect_physical d _ le_rfl,hsum,pow_add,pow_add]
   linear_combination (x^k*x^d.natDegree)*hm
 rw [← map_mul] at he
 have hz :=congrArg (fun g:L[X]=>g.coeff 0) (phys_inj he)
 rw [mul_coeff_zero,coeff_zero_reverse,mul_coeff_zero,coeff_X_pow,
   ite_eq_right (Ne.symm hk),zero_mul] at hz
 exact mul_ne_zero (leadingCoeff_ne_zero.mpr hn) hb hz
end
end qCe4xzb
end
section
namespace qCe4xzb
noncomputable section
open Polynomial Finset
open cu (L)
open P5 (K)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qxPDCsa (infinityRef)
open qb0hmCe (CurveModel)
open q1kuFjb (mapTwice)
open qJai0ob (evalAt)
@[simp] theorem coeff_physicalChart {R:Type} [Semiring R] (f :R[X][X]) (w D i:ℕ) :
    (physicalChart f w D).coeff i=(f.coeff i).reflect (w-i*D) := by
  simp only [physicalChart,Polynomial.sum_def,Polynomial.finsetSum_coeff,coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hi
    simp [notMem_support_iff.mp hi]
theorem cFo {R B:Type} [CommRing R] [CommRing B] (φ:R →+* B)
  (f :R[X][X]) (w D d:ℕ) (b:R) :
  mapTwice φ (ordinateChart (physicalChart f w D) d b) =
    ordinateChart (physicalChart (mapTwice φ f) w D) d (φ b) := by
 have h:mapTwice φ (physicalChart f w D)=physicalChart (mapTwice φ f) w D:= by
  apply Polynomial.ext fun i=>Polynomial.ext fun j => ?_
  simp only [mapTwice,coeff_map,coe_mapRingHom,coeff_physicalChart,coeff_reflect]
 unfold ordinateChart
 have ht:mapTwice φ ((physicalChart f w D).taylor (C b)) =
    (physicalChart (mapTwice φ f) w D).taylor (C (φ b)) := by
  unfold mapTwice at *
  rw [coe_mapRingHom,map_taylor,coe_mapRingHom,map_C,← coe_mapRingHom,h]
 apply Polynomial.ext fun i => ?_
 simpa only [mapTwice,coe_mapRingHom,coeff_map,coeff_reflect] using
  congrArg (fun g:B[X][X]=>g.coeff (revAt d i)) ht
theorem degree_physicalChart {R:Type} [CommRing R] (f :R[X][X]) (w D:ℕ) :
  (physicalChart f w D).natDegree≤f.natDegree :=
 natDegree_le_iff_coeff_eq_zero.mpr fun i hi=> by
  simp [coeff_eq_zero_of_natDegree_lt hi]
theorem equation_degree {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
  (F:Sheet Cq z S) (D:ℕ) (b:L) (h: (infinityRef F D b).coeff 0≠0) :
  (equation F D b).natDegree=F.d∧(equation F D b).leadingCoeff=infinityRef F D b:= by
 have hc: (equation F D b).coeff F.d=infinityRef F D b:= by
  simp only [equation,ordinateChart,coeff_reflect,revAt_le le_rfl,Nat.sub_self,
    taylor_coeff_zero]
  rfl
 have hn: (equation F D b).coeff F.d≠0:= fun hz=>h (by simp [← hc,hz])
 have hd: (equation F D b).natDegree≤F.d:= by
  apply natDegree_reflect_le.trans
  change max F.d (((physicalChart F.f (weightAt F.f D) D).taylor
    (C (algebraMap L Cq.E b))).natDegree)≤F.d
  rw [natDegree_taylor]
  exact max_le le_rfl (degree_physicalChart _ _ _)
 have he :=le_antisymm hd (le_natDegree_of_ne_zero hn)
 exact ⟨he,by rw [leadingCoeff,he,hc]⟩
private theorem c7J {R B:Type} [CommRing R] [CommRing B] (φ:R →+* B)
   {x y :B} (h:x*y=1) (f :R[X]) {n:ℕ} (hd:f.natDegree≤n) :
   (f.reflect n).eval₂ φ y=y^n*f.eval₂ φ x := by
 let:Invertible x :=invertibleOfRightInverse x y h
 calc
   _=y^n*((f.reflect n).eval₂ φ y*x^n) := by
     rw [mul_left_comm,← mul_pow,mul_comm y x,h,one_pow,mul_one]
   _ = _:=congrArg (y^n * ·) (eval₂_reflect_mul_pow φ x n f hd)
theorem physical_eval {R B:Type} [CommRing R] [CommRing B] (φ:R →+* B)
   (f :R[X][X]) (w D:ℕ) (s t u:B) (hst:t*s=1)
   (hw : ∀ i∈f.support,(f.coeff i).natDegree+i*D ≤w) :
   evalAt φ s u (physicalChart f w D)=s^w*evalAt φ t (t^D*u) f := by
 rw [physicalChart,Polynomial.sum_def,map_sum]
 simp only [evalAt,coe_eval₂RingHom,eval₂_monomial]
 rw [eval₂_eq_sum (p:=f),Polynomial.sum_def,mul_sum]
 apply Finset.sum_congr rfl
 intro i hi
 have h:=hw i hi
 have hn: (f.coeff i).natDegree≤w-i*D:= by omega
 have he :w-i*D+i*D =w:=Nat.sub_add_cancel (le_trans (Nat.le_add_left _ _) h)
 have hp:s^w*(t^D)^i=s^(w-i*D) := by
   calc
     _=(s^(w-i*D)*s^(i*D))*t^(i*D) := by rw [← pow_mul,mul_comm D i,← pow_add,he]
     _ = _:= by rw [mul_assoc,← mul_pow,mul_comm s t,hst,one_pow,mul_one]
 simp only [coe_eval₂RingHom,c7J φ hst _ hn,mul_pow]
 calc
   _=s^(w-i*D)*((f.coeff i).eval₂ φ t*u^i) := by ring
   _ = _:= by rw [← hp]; ring
theorem c2S {R B:Type} [CommRing R] [CommRing B] (φ:R →+* B)
  (f :R[X][X]) (d:ℕ) (b:R) (s y z :B) (hyz :y*z=1)
  (hd:f.natDegree≤d) :
  evalAt φ s z (ordinateChart f d b)=z^d*evalAt φ s (y+φ b) f := by
 simp only [evalAt,coe_eval₂RingHom,ordinateChart]
 rw [c7J _ hyz _ (by simpa only [natDegree_taylor] using hd),
  taylor_apply,eval₂_comp,eval₂_add,eval₂_X,eval₂_C,coe_eval₂RingHom,eval₂_C]
end
end qCe4xzb
end
