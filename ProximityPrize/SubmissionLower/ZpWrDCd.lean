import ProximityPrize.SubmissionLower.Z0zgXCc
import ProximityPrize.SubmissionLower.ZjU0F6a
import ProximityPrize.SubmissionLower.Z99zqBd
import ProximityPrize.SubmissionLower.Z3swOYa
import ProximityPrize.SubmissionLower.ZhyMlza
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.RingTheory.Polynomial.ContentIdeal
import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZJbAGBd
set_option Elab.async false
open _root_ renaming Algebra → zZE, Field → zrb, Function.Injective → zq4, IsFractionRing.injective → zxb, MvPolynomial.C → znf, MvPolynomial.totalDegree_C → ziW, MvPolynomial.totalDegree_finsetSum_le → zTw, MvPolynomial.totalDegree_mul → zhM, Nat.add_sub_of_le → zp3, Nat.cast_add → z6H, Nat.le_of_dvd → zTm, Nat.mul_le_mul_left → zBI, Nat.sub_add_cancel → zxt, Polynomial.X → z7y
section
section
namespace qb1WXKc
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L)


open qxPDCsa (infinityRef)
open qCe4xzb (weightAt physicalChart equation coeff_physicalChart degree_physicalChart)

open q14iMuc (discr_map discr_scale)
open LaurentPolynomial (T invert T_add T_pow toLaurent_reverse isUnit_T)
private theorem toLaurent_reflect {E :Type*} [zrb E] (g:E[X]) (n:ℕ)
    (h:g.natDegree≤n) :
    toLaurent (g.reflect n)=invert (toLaurent g)*T (n:ℤ) := by
  have he :n=g.natDegree+(n-g.natDegree) :=(zp3 h).symm
  have h1 : (1 :E[X]).reflect (n-g.natDegree)=z7y^(n-g.natDegree) := by
    simpa only [C_1,one_mul] using (reflect_C (1 :E) (n-g.natDegree))
  conv_lhs =>
    rw [he]
    rw [show g.reflect (g.natDegree+(n-g.natDegree)) =
      g.reverse*z7y^(n-g.natDegree) by
        simpa only [mul_one,reverse,h1] using
          (reflect_mul g 1 (F:=g.natDegree) (G:=n-g.natDegree) le_rfl (by simp))]
  rw [map_mul,toLaurent_reverse,toLaurent_X_pow,mul_assoc,← T_add,← z6H,
    zp3 h]
private theorem physical_discr {E :Type} [zrb E] (f :E[X][X]) (D:ℕ)
   (hd:0<f.natDegree) (hn: (f.natDegree :E)≠0) :
   (physicalChart f (weightAt f D) D).discr.trailingCoeff=f.discr.leadingCoeff := by
 let d:=f.natDegree
 let w:=weightAt f D
 let G:=physicalChart f w D
 let ι:E[X] →+* LaurentPolynomial E :=toLaurent
 let φ:E[X] →+* LaurentPolynomial E :=invert.toRingHom.comp ι
 have hι:zq4 ι:=toLaurent_injective
 have hφ:zq4 φ:=invert.injective.comp hι
 have hw (i:ℕ) (hi:f.coeff i≠0) : (f.coeff i).natDegree+i*D ≤w :=
   le_sup (f := fun i=>(f.coeff i).natDegree+i*D) (mem_support_iff.mpr hi)
 have hW:d*D ≤w:=(Nat.le_add_left _ _).trans
   (hw d (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd)))
 have he :G.map ι=C (T (w-d*D:ℕ))*(f.map φ).scaleRoots (T (D:ℤ)) := by
   apply Polynomial.ext
   intro i
   rw [coeff_map,coeff_C_mul,coeff_scaleRoots,coeff_map,natDegree_map_eq_of_injective hφ,
     coeff_physicalChart]
   by_cases hi:f.coeff i=0
   · simp [hi]
   have hi' : i≤d:=le_natDegree_of_ne_zero hi
   have hwi:=hw i hi
   have hid :i*D ≤d*D:=Nat.mul_le_mul_right D hi'
   have hsub:w-i*D =w-d*D+(d-i)*D:= by rw [Nat.sub_mul]; omega
   change toLaurent ((f.coeff i).reflect (w-i*D)) =
     T (w-d*D:ℕ)*(invert (toLaurent (f.coeff i))*T (D:ℤ)^(d-i))
   rw [toLaurent_reflect _ _ (by omega),T_pow,mul_left_comm,← T_add,
     ← Nat.cast_mul,← Nat.cast_add,hsub]
 have hT: (T (w-d*D:ℕ) :LaurentPolynomial E)≠0:=(isUnit_T _).ne_zero
 have hf : (f.map φ).natDegree=d:=natDegree_map_eq_of_injective hφ _
 have hs : ((f.map φ).scaleRoots (T (D:ℤ))).natDegree=d :=
   (natDegree_scaleRoots _ _).trans hf
 have hG:G.natDegree=d:= by
   rw [← natDegree_map_eq_of_injective hι G,he,natDegree_C_mul hT,hs]
 have hcast: (d:LaurentPolynomial E)≠0:= by
   simpa only [map_natCast,map_zero] using
     (LaurentPolynomial.C (R:=E)).injective.ne hn
 have hdis :=discr_scaleRoots (f.map φ) (T (D:ℤ)) (hf.symm ▸ hd) (hf.symm ▸ hcast)
 let k :=(2*d-2)*(w-d*D)+(d*(d-1))*D
 have hL:ι G.discr=T (k :ℤ)*invert (ι f.discr) := by
   rw [← discr_map ι hι _ (hG.symm ▸ hd),he,discr_scale _ hT _ (hs.symm ▸ hd),
     hdis,hs,hf,discr_map φ hφ _ hd]
   change _=T (k :ℤ)*φ f.discr
   rw [← mul_assoc,T_pow,T_pow,← T_add,← Nat.cast_mul,← Nat.cast_mul,← z6H]
 have hP:z7y^f.discr.natDegree*G.discr=z7y^k*f.discr.reverse := by
   apply hι
   change toLaurent _=toLaurent _
   rw [map_mul,map_mul,toLaurent_X_pow,toLaurent_X_pow,toLaurent_reverse]
   change _ *ι G.discr= _
   rw [hL]
   ac_rfl
 have hX (n:ℕ) : ((z7y:E[X])^n).trailingCoeff=1 := by
   rw [trailingCoeff,natTrailingDegree_X_pow,coeff_X_pow,ite_eq_left rfl]
 simpa only [trailingCoeff_mul,hX,one_mul,reverse_trailingCoeff] using
   congrArg trailingCoeff hP
private theorem reflect_degree {R:Type*} [CommRing R] [IsDomain R]
  (f :R[X]) (h:f.coeff 0≠0) :f.reverse.natDegree=f.natDegree := by
 rw [reverse_natDegree,natTrailingDegree_eq_zero.mpr (Or.inr h),Nat.sub_zero]
theorem infinity_discr :qCe4xzb.c1 := by
 intro q Cq z S F D b hp hb
 let E :=Cq.E
 let G:=physicalChart F.f (weightAt F.f D) D
 let g:=G.taylor (C (algebraMap L E b))
 have htop:G.coeff F.d≠0:= by
   rw [coeff_physicalChart]
   exact fun h=>(leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt F.positive))
     (reflect_eq_zero_iff.mp h)
 have hG:G.natDegree=F.d :=
   (degree_physicalChart _ _ _).antisymm (le_natDegree_of_ne_zero htop)
 have hg:g.natDegree=F.d:=(natDegree_taylor _ _).trans hG
 have hg0:g.coeff 0≠0:= by
   change (G.taylor (C (algebraMap L E b))).coeff 0≠0
   rw [taylor_coeff_zero]
   change infinityRef F D b≠0
   exact fun h=>hb (h ▸ coeff_zero _)
 have hEq:equation F D b=g.reverse := by
   change g.reflect F.d= _
   rw [reverse,hg]
 let B:=FractionRing E[X]
 let ι:=algebraMap E[X] B
 have hi:zq4 ι:=zxb E[X] B
 let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let _:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
 have hn: (F.d:E)≠0:= fun hz =>
   hp.not_ge (zTm F.positive ((CharP.cast_eq_zero_iff E p _).mp hz))
 have hdg:0<g.natDegree :=hg.symm ▸ F.positive
 have hrg:=reflect_degree g hg0
 have hr :g.reverse.discr=g.discr := by
   apply hi
   rw [← discr_map ι hi _ (hrg.symm ▸ hdg),← discr_map ι hi _ hdg]
   have hm: (g.reverse.map ι)=(g.map ι).reverse := by
     ext i
     simp only [coeff_map,coeff_reverse,natDegree_map_eq_of_injective hi]
   have hd: (g.map ι).natDegree=F.d:=(natDegree_map_eq_of_injective hi _).trans hg
   have hcast: (F.d:B)≠0:= by
     rw [← map_natCast ι,← map_natCast (C:E →+* E[X])]
     exact (map_ne_zero_iff ι hi).mpr (C_ne_zero.mpr hn)
   rw [hm,discr_reverse _ (hd.symm ▸ F.positive) (hd.symm ▸ hcast)
     (by simpa only [coeff_map,map_zero] using hi.ne hg0)]
 rw [hEq,hr,discr_taylor G _ (hG.symm ▸ F.positive)]
 exact physical_discr F.f D F.positive hn
end
end qb1WXKc
end
section
namespace qb8HqGc
noncomputable section
open Polynomial Finset
open cu (L)
open P5 (K p)
open qb1WXKc (discr_reverse discr_scaleRoots discr_taylor)
open q14iMuc (discr_map discr_scale)
open qgpYCte (changeOrdinate changeOrdinate_coeff_top)
private def binary {F:Type*} [zrb F] (f :F[X]) (a b c d:F) :F[X] :=
 ∑ i∈range (f.natDegree+1),C (f.coeff i) *
   (C a+C b*z7y)^i*(C c+C d*z7y)^(f.natDegree-i)
private theorem binary_value {F:Type*} [zrb F] (f :F[X]) (u v :F) (hv :v≠0) :
   (∑ i∈range (f.natDegree+1),f.coeff i*u^i*v^(f.natDegree-i)) =
     v^f.natDegree*f.eval (u/v) := by
 rw [eval_eq_sum_range' (Nat.lt_succ_self _),mul_sum]
 refine sum_congr rfl fun i hi => ?_
 rw [pow_sub₀ _ hv (Nat.lt_succ_iff.mp (mem_range.mp hi)),div_pow,div_eq_mul_inv]
 ring
private theorem eval_binary {F:Type*} [zrb F] (f :F[X]) (a b c d x :F)
  (hx :c+d*x≠0) : (binary f a b c d).eval x=(c+d*x)^f.natDegree *
    f.eval ((a+b*x)/(c+d*x)) := by
 simp only [binary,eval_finsetSum,eval_add,eval_mul,eval_pow,eval_C,eval_X]
 exact binary_value f _ _ hx
private theorem cNb {F:Type*} [zrb F] (f :F[X]) (s x :F) :
  (f.taylor s).eval x=f.eval (x+s) := by
 simp [taylor_apply,eval_comp]
private theorem aNz {F:Type*} [zrb F] (f :F[X]) {r :F} (hr :r≠0) (x :F) :
  (f.scaleRoots r).eval x=r^f.natDegree*f.eval (x/r) := by
 have he :r*(x/r)=x := by field_simp
 simpa only [he] using scaleRoots_eval_mul f (x/r) r
private theorem eval_reverse {F:Type*} [zrb F] (f :F[X]) {x :F} (hx :x≠0) :
   f.reverse.eval x=x^f.natDegree*f.eval x⁻¹:= by
 let:Invertible x⁻¹:=invertibleOfNonzero (inv_ne_zero hx)
 have hh:=eval₂_reverse_mul_pow (RingHom.id F) x⁻¹ f
 rw [invOf_eq_inv,inv_inv] at hh
 change f.reverse.eval x*(x⁻¹)^f.natDegree=f.eval x⁻¹ at hh
 calc
   _=(f.reverse.eval x*(x⁻¹)^f.natDegree)*x^f.natDegree := by
     rw [mul_assoc,← mul_pow,inv_mul_cancel₀ hx,one_pow,mul_one]
   _ = _:= by rw [hh,mul_comm]
private theorem discriminant_binary {F:Type*} [zrb F] [Infinite F]
    (f :F[X]) (a b c d:F) (hpos :0<f.natDegree) (hn: (f.natDegree :F)≠0)
    (hdet:a*d-b*c≠0)
    (htop: (∑ i∈range (f.natDegree+1),f.coeff i*b^i*d^(f.natDegree-i))≠0) :
    (binary f a b c d).discr=(a*d-b*c)^(f.natDegree*(f.natDegree-1))*f.discr := by
  let n:=f.natDegree
  let m:=n*(n-1)
  change (binary f a b c d).discr=(a*d-b*c)^m*f.discr
  have weight (u v :F) : (u^n)^(2*n-2)*v^m=(u*u*v)^m:= by
    rw [← pow_mul,show 2*n-2=2*(n-1) by omega,
      show n*(2*(n-1))=m+m by dsimp [m]; ring,pow_add,mul_pow,mul_pow]
  by_cases hd:d=0
  · subst d
    have hbc:b*c≠0:= by simpa using hdet
    have hb:=left_ne_zero_of_mul hbc
    have hc:=right_ne_zero_of_mul hbc
    let r :=c/b
    have hr :r≠0:=div_ne_zero hc hb
    have hscalar :b*r=c:= by dsimp [r]; field_simp
    have he :binary f a b c 0=C (b^n)*((f.scaleRoots r).taylor (a/b)) := by
      apply Polynomial.funext
      intro x
      have harg : (x+a/b)/r=(a+b*x)/c:= by dsimp [r]; field_simp; ring
      rw [eval_binary f a b c 0 x (by simpa using hc),eval_mul,eval_C,cNb,
        aNz _ hr,harg,← mul_assoc,← mul_pow,hscalar,zero_mul,add_zero]
    have hsign: (-1 :F)^m=1 := by
      obtain ⟨j,hj⟩:2∣m:= by
        have h:=Nat.two_dvd_mul_add_one (n-1)
        rw [zxt (show 1≤n from hpos),mul_comm] at h
        exact h
      rw [hj,pow_mul,neg_one_sq,one_pow]
    rw [he,discr_scale _ (pow_ne_zero _ hb) _ (by simpa using hpos),
      natDegree_taylor,natDegree_scaleRoots,discr_taylor _ _ (by simpa using hpos),
      discr_scaleRoots _ _ hpos hn,← mul_assoc,weight]
    rw [show b*b*r=b*c by rw [mul_assoc,hscalar]]
    have hs : (-(b*c))^m=(b*c)^m:= by
      rw [neg_eq_neg_one_mul,mul_pow,hsign,one_mul]
    rw [mul_zero,zero_sub,hs]
  · let h:=f.taylor (b/d)
    let t:=(a*d-b*c)/d^2
    have ht:t≠0:=div_ne_zero hdet (pow_ne_zero _ hd)
    have hdeg:h.natDegree=n:=natDegree_taylor _ _
    have h0:h.coeff 0≠0:= by
      intro hz
      apply htop
      rw [binary_value f b d hd,← taylor_coeff_zero,show (f.taylor (b/d)).coeff 0=0 from hz,
        mul_zero]
    have hrev :h.reverse.natDegree=n:= by
      rw [reverse_natDegree,natTrailingDegree_eq_zero.mpr (Or.inr h0),Nat.sub_zero,hdeg]
    have he :binary f a b c d=C (d^n)*((h.reverse.scaleRoots t).taylor (c/d)) := by
      apply Polynomial.eq_of_infinite_eval_eq
      refine (Set.infinite_univ.sdiff (Set.finite_singleton (-(c/d)))).mono ?_
      intro x hx
      have hx' : x+c/d≠0:= fun hz=>hx.2 (Set.mem_singleton_iff.mpr
        (show x = -(c/d) by linear_combination hz))
      have hlin:c+d*x=d*(x+c/d) := by field_simp; ring
      have harg : (a+b*x)/(c+d*x)=t/(x+c/d)+b/d:= by
        apply (div_eq_iff (hlin ▸ mul_ne_zero hd hx')).2
        rw [hlin,add_mul,mul_comm d (x+c/d),← mul_assoc,div_mul_cancel₀ _ hx',
          mul_comm (x+c/d) d,← mul_assoc,div_mul_cancel₀ _ hd]
        dsimp [t]
        field_simp
        ring
      have hscalar :t*((x+c/d)/t)=x+c/d:= by field_simp
      change (binary f a b c d).eval x= _
      rw [eval_binary f a b c d x (hlin ▸ mul_ne_zero hd hx'),eval_mul,eval_C,
        cNb,aNz _ ht,eval_reverse _ (div_ne_zero hx' ht),hrev,hdeg,
        inv_div,show h.eval _=f.eval _ from cNb _ _ _,harg,hlin,mul_pow d (x+c/d)]
      have hs :t^n*((x+c/d)/t)^n=(x+c/d)^n:= by rw [← mul_pow,hscalar]
      rw [← mul_assoc (t^n) (((x+c/d)/t)^n),hs,← mul_assoc]
    rw [he,discr_scale _ (pow_ne_zero _ hd) _ (by simpa only [natDegree_taylor,
      natDegree_scaleRoots,hrev] using hpos),natDegree_taylor,natDegree_scaleRoots,hrev,
      discr_taylor _ _ (by simpa only [natDegree_scaleRoots,hrev] using hpos),
      discr_scaleRoots _ _ (hrev.symm ▸ hpos) (hrev.symm ▸ hn),hrev,
      discr_reverse _ (hdeg.symm ▸ hpos) (hdeg.symm ▸ hn) h0,
      discr_taylor _ _ hpos,← mul_assoc,weight]
    rw [show d*d*t=a*d-b*c by dsimp [t]; field_simp]
theorem covariance {E :Type} [zrb E] [zZE L E] (f :E[X][X])
   (M:Matrix (Fin 2) (Fin 2) E[X]) (hpos :0<f.natDegree) (hp:f.natDegree<p)
   (hdet:M.det≠0) (hdeg: (changeOrdinate f M).natDegree=f.natDegree) :
   (changeOrdinate f M).discr=M.det^(f.natDegree*(f.natDegree-1))*f.discr := by
 let F:=FractionRing E[X]
 let i:=algebraMap E[X] F
 have hi:zq4 i:=zxb E[X] F
 let:Infinite F:=Infinite.of_injective i hi
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP F p:=charP_of_injective_ringHom
   (f :=i.comp (Polynomial.C.comp (algebraMap L E)))
   (hi.comp (C_injective.comp (algebraMap L E).injective)) p
 let g:=f.map i
 have hgd:g.natDegree=f.natDegree :=natDegree_map_eq_of_injective hi _
 have hn: (g.natDegree :F)≠0:= fun hz=>hp.not_ge
   (hgd ▸ zTm (hgd.symm ▸ hpos) ((CharP.cast_eq_zero_iff F p _).mp hz))
 have hM:i M.det=i (M 0 0)*i (M 1 1) - i (M 0 1)*i (M 1 0) := by
   rw [Matrix.det_fin_two,map_sub,map_mul,map_mul]
 have hM' : i (M 0 0)*i (M 1 1) - i (M 0 1)*i (M 1 0)≠0:= by
   rw [← hM]
   simpa only [map_zero] using hi.ne hdet
 have htop: (∑ j∈range (g.natDegree+1),g.coeff j*(i (M 0 1))^j *
     (i (M 1 1))^(g.natDegree-j))≠0:= by
   have h:=hi.ne (leadingCoeff_ne_zero.mpr
     (ne_zero_of_natDegree_gt (hdeg.symm ▸ hpos)))
   rw [← coeff_natDegree,hdeg,changeOrdinate_coeff_top,map_sum,map_zero] at h
   simpa only [hgd,g,coeff_map,map_mul,map_pow] using h
 have he : (changeOrdinate f M).map i=binary g (i (M 0 0)) (i (M 0 1))
     (i (M 1 0)) (i (M 1 1)) := by
   simp only [changeOrdinate,binary,hgd,g,coeff_map,Polynomial.map_sum,
     Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,map_C,map_X]
 apply hi
 rw [← discr_map i hi _ (hdeg.symm ▸ hpos),he,map_mul,map_pow,← discr_map i hi f hpos]
 simpa only [hgd,← hM] using discriminant_binary g _ _ _ _ (hgd.symm ▸ hpos) hn
   hM' htop
end
end qb8HqGc
end
end
section
section
namespace qLXroAb
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K)
open cu (L FX j9)
open E7 (CurvePlace KB)
open qb0hmCe (CurveModel)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open P5_7_7 (phys)
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
def evalXY {E M:Type} [zrb E] [zrb M] [zZE E M]
    (f :E[X][X]) (x y :M) :M :=
  f.eval₂ (eval₂RingHom (algebraMap E M) x) y
def dx {E :Type} [zrb E] (f :E[X][X]) :E[X][X] :=
 f.sum fun i g=>monomial i g.derivative
def coords {E M:Type} [zrb E] [zrb M] [zZE E M]
    (f :E[X][X]) (x y :M) :Fin 4→M :=
  let r :=evalXY f.derivative x y
  ![r,x*r,y*r,-evalXY (dx f) x y]
def linear {E :Type} [CommRing E] (j:L →+* E) (a :Fin 4→L) (v :Fin 4→E) :E :=
 ∑ i,j (a i)*v i
abbrev tu (E :Type) [zrb E] :=FractionRing E[X]
structure Pencil (F:Sheet Cq z S) where
 M:Type
 [field :zrb M]
 [aO8:zZE Cq.E M]
 [overBase :zZE (tu Cq.E) M]
 [tower :IsScalarTower Cq.E (tu Cq.E) M]
 [finite :Module.Finite (tu Cq.E) M]
 separable :Algebra.IsSeparable (tu Cq.E) M
 x :M
 y :M
 independent:Transcendental Cq.E x
 equation :evalXY F.f x y=0
 generates :IntermediateField.adjoin Cq.E ({x,y} : Set M) = ⊤
 polar_ne :evalXY F.f.derivative x y≠0
 y_ne :y≠0
 a :Fin 4→L
 b:Fin 4→L
 gauge_ne :linear ((algebraMap Cq.E M).comp (algebraMap L Cq.E)) a (coords F.f x y)≠0
 value :linear ((algebraMap Cq.E M).comp (algebraMap L Cq.E)) b (coords F.f x y) =
   algebraMap (tu Cq.E) M (algebraMap Cq.E[X] (tu Cq.E) z7y) *
     linear ((algebraMap Cq.E M).comp (algebraMap L Cq.E)) a (coords F.f x y)
attribute [instance] Pencil.field Pencil.aO8 Pencil.overBase Pencil.tower Pencil.finite
variable {F:Sheet Cq z S}
abbrev Pencil.u (A:Pencil F) :A.M :=
 algebraMap (tu Cq.E) A.M (algebraMap Cq.E[X] (tu Cq.E) z7y)
abbrev Pencil.polar (A:Pencil F) :A.M:=evalXY F.f.derivative A.x A.y
def Pencil.polarPoly (A:Pencil F) : (tu Cq.E)[X] :=
 (Algebra.lmul (tu Cq.E) A.M A.polar).charpoly
def Pencil.ratio (A:Pencil F) (i:Fin 4) :A.M :=
  coords F.f A.x A.y i /
    linear ((algebraMap Cq.E A.M).comp (algebraMap L Cq.E)) A.a (coords F.f A.x A.y)
abbrev seedRing (F:Sheet Cq z S) (γ:K) :=(F.place γ).value.valuationSubring
def Pencil.pO (A:Pencil F) (γ:K) :seedRing F γ →+* A.M :=
 (algebraMap Cq.E A.M).comp (seedRing F γ).subtype
def Pencil.bY (A:Pencil F) (γ:K) :Subring A.M :=
 Subring.closure (Set.range (A.pO γ)∪Set.range A.ratio)
def Pencil.inChart (A:Pencil F) (γ:K) :seedRing F γ →+* A.bY γ :=
  (A.pO γ).codRestrict (A.bY γ) fun c =>
    Subring.subset_closure (Or.inl ⟨c,rfl⟩)
def Pencil.chartRatio (A:Pencil F) (γ:K) (i:Fin 4) :A.bY γ :=
 ⟨A.ratio i,Subring.subset_closure (Or.inr ⟨i,rfl⟩)⟩
def markJet (S:K→K[X]) (γ:K) :Fin 4→ L[X] :=
 ![1,z7y,j9 (S γ),(j9 (S γ)).derivative]
structure Chart (A:Pencil F) (γ:K) (hγ:γ∈F.marks) (B:L[X]) where
  u:A.bY γ
  center : (u:A.M)=A.u
  finite :letI:=(eval₂RingHom (A.inChart γ) u).toAlgebra
          Module.Finite (seedRing F γ)[X] (A.bY γ)
  map :A.bY γ →+* FX
  seed : ∀ c:seedRing F γ,
    map (A.inChart γ c)=phys (C ((F.atPlace γ hγ (c:Cq.E)).coeff 0))
  gauge_ne :linear (C:L →+* L[X]) A.a (markJet S γ)≠0
  F8 : ∀ i,map (A.chartRatio γ i) =
    phys (markJet S γ i)/phys (linear (C:L →+* L[X]) A.a (markJet S γ))
  avoids : ∀ x,B.eval x=0→(linear (C:L →+* L[X]) A.a (markJet S γ)).eval x≠0
structure Vertical (A:Pencil F) (w:CurvePlace L Cq.E) where
 value :Valuation A.M ℤᵐ⁰
 normalized:Function.Surjective value
 ramification :ℕ
 positive :0< ramification
 overGauss : ∀ g:Cq.E[X],
  value (g.eval₂ (algebraMap Cq.E A.M) A.u) =
   (g.support.sup fun i=>w.value (g.coeff i))^ramification
def RootCharge (A:Pencil F) (w:CurvePlace L Cq.E) (B:L[X]) :Prop :=
  ∀ x,B.eval x=0 → ∃ v :Vertical A w,
    v.value (A.x-algebraMap Cq.E A.M (algebraMap L Cq.E x))<1 ∧
      B.rootMultiplicity x≤KB v.value A.polar
def chargeCoeff (R:Cq.E[X][X]) :Cq.E :=R.trailingCoeff.leadingCoeff
def bw (D e W:ℕ) :ℕ:=(6*e-2)*W-3*e*e*D
end
end qLXroAb
end
section
namespace qBd5KZd
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)
open E7 (CurveField CurvePlace)
open scoped WithZero
structure MarkedCurve (T:Finset K) where
 E :Type
 [field :zrb E]
 [algebra :zZE L E]
 curve :CurveField L E
 Ia :T ↪ CurvePlace L E
attribute [instance] MarkedCurve.field MarkedCurve.algebra
abbrev Allowance (E :Type) [zrb E] [zZE L E] :=CurvePlace L E →₀ ℕ
def mass {ι:Type} : (ι →₀ ℕ) →+ ℕ :=
 Finsupp.liftAddHom (fun _=>AddMonoidHom.id ℕ)
variable {E :Type} [zrb E] [zZE L E]
def small (v :CurvePlace L E) (a :ℤ) (x :E) :Prop :=
 v.value x≤WithZero.exp a
def btN (A:Allowance E) :Submodule L E where
  carrier := {x | ∀ v,small v (A v) x}
  zero_mem' v := by simp [small]
  add_mem' hx hy v :=(v.value.map_add _ _).trans (max_le (hx v) (hy v))
  smul_mem' c x hx v := by
    change small v (A v) (c•x)
    by_cases hc:c=0
    · simp [hc,small]
    · simpa only [small,Algebra.smul_def,map_mul,v.on_constants c hc,one_mul] using hx v
def bounded (A:Allowance E) (f :E[X][X]) :Prop :=
 ∀ i j,(f.coeff i).coeff j∈btN A
def weight (D:ℕ) (f :E[X][X]) :ℕ :=
 f.support.sup fun i=>(f.coeff i).natDegree+i*D
def j3 (D n:ℕ) :ℕ:=D*n*(n+1)/2
variable {T:Finset K}
def avoids (C:MarkedCurve T) (A:Allowance C.E) :Prop :=
 ∀ t,A (C.Ia t)=0
def integral (C:MarkedCurve T) (S:T→C.E[X]) :Prop :=
 ∀ t i,small (C.Ia t) 0 ((S t).coeff i)
def roots (C:MarkedCurve T) (S:T→C.E[X]) (q:ℕ) (f :C.E[X][X]) :Prop :=
 ∀ t i,small (C.Ia t) (-(q:ℤ)) ((f.eval (S t)).coeff i)
def sections (C:MarkedCurve T) (s :K→K[X]) (t:T) :C.E[X] :=
 (s t).map ((algebraMap L C.E).comp (algebraMap K L))
def pull [CharP E p] (a :ℕ) (f :E[X][X]) :E[X][X] :=
 f.map (mapRingHom (iterateFrobenius E p a))
def modulus (b:L) (M:ℕ) :E[X] :=((z7y:E[X]) - C (algebraMap L E b))^M
end
end qBd5KZd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qBd5KZd
noncomputable section
open Polynomial
open P5 (p)
private theorem separable_of_small {F:Type} [zrb F] [CharP F p] {Q:F[X]}
  (hQ:Irreducible Q) (h:Q.natDegree<p) :Q.Separable := by
 apply (separable_iff_derivative_ne_zero hQ).mpr
 intro hz
 have hn: (Q.natDegree :F)≠0:= fun hn =>
  h.not_ge (zTm hQ.natDegree_pos ((CharP.cast_eq_zero_iff F p _).mp hn))
 have hc:=congrArg (fun P:F[X]=>P.coeff (Q.natDegree-1)) hz
 have he : (Q.natDegree-1).succ= Q.natDegree :=zxt hQ.natDegree_pos
 rw [coeff_derivative,← Nat.cast_succ,he,zxt hQ.natDegree_pos,coeff_zero] at hc
 exact mul_ne_zero (leadingCoeff_ne_zero.mpr hQ.ne_zero) hn hc
theorem pull_irreducible {E :Type} [zrb E] [CharP E p] (a :ℕ) (f :E[X][X])
   (hp:f.IsPrimitive) (hi:Irreducible (f.map (algebraMap _ (FractionRing E[X]))))
   (hd:f.natDegree<p) :
   (pull a f).IsPrimitive∧Irreducible ((pull a f).map (algebraMap _ (FractionRing E[X]))) := by
 let φ:=iterateFrobenius E p a
 let F:=FractionRing E[X]
 let i:E[X] →+* F:=algebraMap E[X] F
 let ψ:=mapRingHom φ
 let j:F →+* F:=IsFractionRing.map (j:=ψ) (Polynomial.map_injective φ φ.injective)
 have hcomp (P:E[X]) :j (i P)=i (ψ P) :=IsLocalization.map_eq _ _
 let:CharP F p:=charP_of_injective_ringHom
   (zxb E[X] F) p
 let:zZE F F:=j.toAlgebra
 have hsep: (f.map i).Separable :=
   separable_of_small hi (by rwa [natDegree_map_eq_of_injective (zxb E[X] F)])
 have hj:IsPurelyInseparable F F:= by
   apply (isPurelyInseparable_iff_pow_mem F p).mpr
   intro x
   obtain ⟨u,v,_,rfl⟩:=IsFractionRing.div_surjective E[X] x
   refine ⟨a,i (expand E (p^a) u)/i (expand E (p^a) v),?_⟩
   change j _=(i u/i v)^(p^a)
   simp only [map_div₀,hcomp,ψ,φ,coe_mapRingHom,map_iterateFrobenius_expand,div_pow,map_pow]
 refine ⟨?_,?_⟩
 · rw [pull,isPrimitive_iff_contentIdeal_eq_top,contentIdeal_map_eq_map_contentIdeal,
     (isPrimitive_iff_contentIdeal_eq_top f).mp hp,Ideal.map_top]
 · have he : (f.map i).map (algebraMap F F)=(pull a f).map i:= by
     change (f.map i).map j=(f.map ψ).map i
     rw [map_map,map_map]
     exact congrArg (fun k=>f.map k) (RingHom.ext hcomp)
   rw [← he]
   exact hsep.map_irreducible_of_isPurelyInseparable F hi
end
end qBd5KZd
end
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_2
noncomputable section
open Polynomial
open cu (L)
open DQ (DT aKg)
open scoped BigOperators
open private fXo from ProximityPrize.SubmissionLower.ZQfUTPd
theorem branch_degree {F:Type} [zrb F] {f :F[X][X]} {g D W:ℕ}
    (hg:0<g) (hgd:f.natDegree=g)
    (hf : ∀ i,f.coeff i≠0→(f.coeff i).natDegree+D*i≤W) (a :F) :
    (f.resultant f.derivative g (g-1)*f.eval (C a)).natDegree≤2*g*W-g*g*D:= by
  have hG:D*g≤W:= by
    rw [← hgd]
    exact (Nat.le_add_left _ _).trans (hf _ (leadingCoeff_ne_zero.mpr
      (ne_zero_of_natDegree_gt (hgd.symm ▸ hg))))
  have hW:D ≤W:= by
    have h:=zBI D (show 1≤g by omega)
    simp only [mul_one] at h
    exact h.trans hG
  have hd (i:ℕ) (hi:f.derivative.coeff i≠0) :
      (f.derivative.coeff i).natDegree+D*i≤W-D:= by
    have h:=hf (i+1) (fun hz=>hi (by simp [coeff_derivative,hz]))
    have hh:=coeff_derivative_natDegree_le f i
    rw [Nat.mul_add,Nat.mul_one] at h
    omega
  have hr :=fXo f f.derivative g (g-1) D W (W-D) hf hd
  have hcut:D*(g*(g-1))≤(g-1)*W:= by
    rw [show D*(g*(g-1))=(g-1)*(D*g) by ring]
    exact zBI _ hG
  have he : (f.eval (C a)).natDegree≤W:= by
    rw [eval_eq_sum_range]
    apply natDegree_sum_le_of_forall_le
    intro i _
    rw [← map_pow]
    apply (natDegree_mul_C_le _ _).trans
    by_cases hi:f.coeff i=0
    · simp [hi]
    · exact (Nat.le_add_right _ _).trans (hf i hi)
  have h₁: (g-1)*W+W=g*W:= by
    rw [← Nat.succ_mul,show (g-1).succ=g by omega]
  have h₂:g*(W-D)+D*g=g*W:= by
    rw [mul_comm D g,← Nat.mul_add,zxt hW]
  have h₃:D*(g*(g-1))+D*g=g*g*D:= by
    calc
      _=D*g*((g-1)+1) := by ring
      _ = _:= by rw [zxt hg]; ring
  have h₄:2*g*W=g*W+g*W:= by ring
  have hb:=natDegree_mul_le_of_le (p:=f.resultant f.derivative g (g-1)) le_rfl he
  exact Nat.le_sub_of_add_le (by omega)
private theorem coeff_mul_bound {n a b:ℕ} {P Q: (DT n)[X]}
    (hP : ∀ j,(P.coeff j).totalDegree≤a) (hQ : ∀ j,(Q.coeff j).totalDegree≤b) (j:ℕ) :
    ((P*Q).coeff j).totalDegree≤a+b:= by
  rw [coeff_mul]
  apply zTw
  exact fun i _=>(zhM _ _).trans (Nat.add_le_add (hP _) (hQ _))
private theorem coeff_prod_bound {ι:Type} {n k :ℕ} (U:Finset ι)
    (P:ι→(DT n)[X]) (h : ∀ i∈U,∀ j,((P i).coeff j).totalDegree≤k) (j:ℕ) :
    ((∏ i∈U,P i).coeff j).totalDegree≤U.card*k := by
  classical
  induction U using Finset.induction_on generalizing j with
  | empty=>by_cases hj:j=0 <;> simp [coeff_one,hj]
  | @insert i U hi ih =>
      rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul,add_comm]
      exact coeff_mul_bound (h i (Finset.mem_insert_self ..))
        (fun j=>ih (fun l hl=>h l (Finset.mem_insert_of_mem hl)) j) j
theorem branch_height {n g:ℕ} {f : (DT n)[X][X]} (hf :aKg f g)
    (hg:0<g) (a :L) (j:ℕ) :
    ((f.resultant f.derivative g (g-1)*f.eval (C (znf a))).coeff j).totalDegree≤2*g:= by
  classical
  let M:=sylvester f f.derivative g (g-1)
  have hd (i k :ℕ) : ((f.derivative.coeff i).coeff k).totalDegree≤1 := by
    rw [coeff_derivative,← Nat.cast_succ]
    have hc: ((i+1 :ℕ) : (DT n)[X])=C (znf ((i+1 :ℕ) :L)) := by simp
    rw [hc,mul_comm,coeff_C_mul]
    exact (zhM _ _).trans (by simpa only [ziW,zero_add] using hf.2 (i+1) k)
  have hentry (i j:Fin (g+(g-1))) (k :ℕ) : ((M i j).coeff k).totalDegree≤1 := by
    cases j using Fin.addCases with
    | left j =>
      simp only [M,sylvester,Matrix.of_apply,Fin.addCases_left]
      split_ifs
      · exact hd _ _
      · simp
    | right j =>
      simp only [M,sylvester,Matrix.of_apply,Fin.addCases_right]
      split_ifs
      · exact hf.2 _ _
      · simp
  have hres (j:ℕ) : (M.det.coeff j).totalDegree≤g+(g-1) := by
    rw [Matrix.det_apply',finsetSum_coeff]
    apply zTw
    intro σ _
    rw [← zsmul_eq_mul,coeff_smul,zsmul_eq_mul]
    have hsign: ((Equiv.Perm.sign σ:ℤ) :DT n) =
        znf ((Equiv.Perm.sign σ:ℤ) :L) := by simp
    rw [hsign]
    exact (zhM _ _).trans (by
      simpa only [ziW,zero_add,Finset.card_univ,Fintype.card_fin,mul_one] using coeff_prod_bound Finset.univ (fun i=>M (σ i) i)
        (fun i _ k=>hentry (σ i) i k) j)
  have he (j:ℕ) : ((f.eval (C (znf a))).coeff j).totalDegree≤1 := by
    rw [eval_eq_sum_range,finsetSum_coeff]
    apply zTw
    intro i _
    rw [← C_pow,← map_pow znf,mul_comm,coeff_C_mul]
    exact (zhM _ _).trans (by simpa only [ziW,zero_add] using hf.2 i j)
  exact (coeff_mul_bound hres he j).trans (by omega)
end
end P5_7_3_3_4_1_2
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_4
noncomputable section
open Polynomial EuclideanDomain UniqueFactorizationMonoid
variable {F:Type*} [zrb F]
theorem irreducible_degree_pos {q:F[X]} (hq:Irreducible q) :0<q.natDegree := by
  by_contra! hz
  have h:=eq_C_of_natDegree_eq_zero (show q.natDegree=0 by omega)
  exact hq.not_isUnit (Polynomial.isUnit_iff.mpr
    ⟨_,isUnit_iff_ne_zero.mpr (C_ne_zero.mp (h ▸ hq.ne_zero)),h.symm⟩)
variable {p:ℕ} [CharP F p]
private theorem cEo {e :ℕ} (he :0<e) (hp:e<p) : (e :F)≠0 :=
  fun h=>(not_le_of_gt hp) (zTm he ((CharP.cast_eq_zero_iff F p e).mp h))
theorem bD9 {f :F[X]} (hf :0<f.natDegree) (hp:f.natDegree<p) :
    f.derivative≠0∧f.derivative.natDegree=f.natDegree - 1 := by
  have he : (↑(f.natDegree - 1)+1 :F)=(f.natDegree :F) := by
    simpa only [z6H,Nat.cast_one] using
      congrArg (fun k :ℕ=>(k :F)) (zxt hf)
  have h:f.derivative.coeff (f.natDegree - 1)≠0:= by
    rw [coeff_derivative,zxt hf,he,coeff_natDegree]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr fun h=> by simp [h] at hf) (cEo hf hp)
  exact ⟨fun h0=>h (by rw [h0,coeff_zero]),
    le_antisymm (natDegree_derivative_le _) (le_natDegree_of_ne_zero h)⟩
private theorem pow_not_dvd_derivative {f q u:F[X]} {e :ℕ} (hq:Irreducible q)
    (hf :f=q^(e+1)*u) (hu : ¬q∣u) (he :e+1<p) (hq' : q.derivative≠0) :
    ¬q^(e+1)∣f.derivative := by
  intro h
  rw [hf,derivative_mul,derivative_pow_succ] at h
  have h' : q^(e+1)∣q^e*(C ((e+1 :ℕ) :F)*q.derivative*u) := by
    have h₂:q^(e+1)∣q^(e+1)*u.derivative :=dvd_mul_right _ _
    simpa only [add_sub_cancel_right,z6H,Nat.cast_one,mul_assoc,mul_left_comm,
      mul_comm] using dvd_sub h h₂
  rw [pow_succ,mul_dvd_mul_iff_left (pow_ne_zero e hq.ne_zero)] at h'
  have hunit :IsUnit (C ((e+1 :ℕ) :F)) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (cEo (Nat.succ_pos e) he))
  rcases hq.prime.dvd_mul.mp h' with h' | h'
  · rcases hq.prime.dvd_mul.mp h' with h' | h'
    · exact hq.not_isUnit (isUnit_of_dvd_unit h' hunit)
    · exact (not_le_of_gt (natDegree_derivative_lt (irreducible_degree_pos hq).ne'))
        (natDegree_le_of_dvd h' hq')
  · exact hu h'
theorem gcd_degree [DecidableEq F] (f :F[X]) (hf :f≠0) (hp:f.natDegree<p) :
    (EuclideanDomain.gcd f f.derivative).natDegree+(radical f).natDegree=f.natDegree := by
  let G:=EuclideanDomain.gcd f f.derivative
  obtain ⟨u,hfu⟩:=EuclideanDomain.gcd_dvd_left f f.derivative
  change f=G*u at hfu
  have hG:G≠0:=left_ne_zero_of_mul (hfu ▸ hf)
  have hu:u≠0:=right_ne_zero_of_mul (hfu ▸ hf)
  have hdr :divRadical f∣G :=
    EuclideanDomain.dvd_gcd (divRadical_dvd_self f) (divRadical_dvd_derivative f)
  have h₁:u∣radical f := by
    obtain ⟨v,hv⟩:=hdr
    have he :divRadical f*radical f=divRadical f*(v*u) := calc
      _=f :=divRadical_mul_radical
      _=G*u:=hfu
      _ = _:= by rw [hv,mul_assoc]
    exact ⟨v,(mul_left_cancel₀ (divRadical_ne_zero hf) he).trans (mul_comm _ _)⟩
  have h₂:radical f∣u:= by
    apply (radical_dvd_iff_primeFactors_subset hu).mpr
    intro q hq
    rw [mem_primeFactors,mem_normalizedFactors_iff' hf] at hq
    rw [mem_primeFactors,mem_normalizedFactors_iff' hu]
    refine ⟨hq.1,hq.2.1,?_⟩
    by_contra hnu
    obtain ⟨e,v,hnv,hv⟩:=WfDvdMonoid.max_power_factor hf hq.1
    cases e with
    | zero=>exact hnv (by simpa [hv] using hq.2.2)
    | succ e =>
      have hd:q^(e+1)∣f :=⟨v,hv⟩
      have hdeg: (e+1)*q.natDegree≤f.natDegree := by
        simpa only [natDegree_pow] using natDegree_le_of_dvd hd hf
      have hqpos :=irreducible_degree_pos hq.1
      have he :e+1<p:=((Nat.le_mul_of_pos_right _ hqpos).trans hdeg).trans_lt hp
      have hq' := (bD9 hqpos ((natDegree_le_of_dvd hq.2.2 hf).trans_lt hp)).1
      have hcop:IsCoprime (q^(e+1)) u :=
        ((hq.1.isCoprime_or_dvd u).resolve_right hnu).pow_left
      have hdG:q^(e+1)∣G:=hcop.dvd_of_dvd_mul_right (hfu ▸ hd)
      exact pow_not_dvd_derivative hq.1 hv hnv he hq'
        (hdG.trans (EuclideanDomain.gcd_dvd_right f f.derivative))
  have hdu:u.natDegree=(radical f).natDegree :=
    le_antisymm (natDegree_le_of_dvd h₁ radical_ne_zero) (natDegree_le_of_dvd h₂ hu)
  rw [← hdu,← natDegree_mul hG hu,← hfu]
end
end P5_7_3_3_4_1_4
end
