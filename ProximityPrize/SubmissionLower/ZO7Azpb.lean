import ProximityPrize.SubmissionLower.ZFdiUYb
import ProximityPrize.SubmissionLower.Z66Jm5b
import ProximityPrize.SubmissionLower.ZvFqJTb
set_option Elab.async false
set_option autoImplicit true
section
namespace qbnx7gb
noncomputable section
open Polynomial qQ9yWTb qb0hmCe qFD8jve


open P5_7_7 (phys)
open cu (L)

end
end qbnx7gb
end
section
namespace qFe6O4d
noncomputable section
open Finset Polynomial TrivSqZeroExt
open qwGrtCa (form transform transform_sum)
open q1kuFjb (IntSeries Ua mapTwice map_liftAt)
open qJai0ob (scalar evalAt)
open private constant τ center center_poly from ProximityPrize.SubmissionLower.ZFdiUYb
open P5_7_7 (phys)
open qb0hmCe (specialize)
open cu (L)
private def translate {A:Type} [CommRing A] (x :A) (f :A[X][X]) :A[X][X] :=
 f.map (taylorAlgHom x).toRingHom
private theorem ctZ {A B:Type} [CommRing A] [CommRing B]
  (e :A →+* B) (x :A) (f :A[X][X]) :
  mapTwice e (translate x f)=translate (e x) (mapTwice e f) := by
 apply Polynomial.ext
 intro i
 simp only [translate,mapTwice,coe_mapRingHom,coeff_map]
 exact map_taylor (f.coeff i) x e
private theorem transform_map {A B:Type} [CommRing A] [CommRing B]
  (e :A →+* B) (a b c d:A) (n:ℕ) (f :A[X]) :
  (transform a b c d n f).map e=transform (e a) (e b) (e c) (e d) n (f.map e) := by
 simp only [transform_sum,form,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_pow,
  Polynomial.map_add,Polynomial.map_C,Polynomial.map_X,coeff_map]
theorem lift_change {E :Type} [Field E] [Algebra L E]
   (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (hf)
   (x t A B:E) (x' t' A' B' : IntSeries) (n:ℕ)
   (hx : (x' : LaurentSeries L)=a x) (ht: (t' : LaurentSeries L)=a t)
   (hA: (A' : LaurentSeries L)=a A) (hB: (B' : LaurentSeries L)=a B)
   (hF) :
   Ua a (transform (C t) (C A) 1 (C B) n (translate x f)) hF =
     transform (C t') (C A') 1 (C B') n (translate x' (Ua a f hf)) := by
 let ι:IntSeries →+* LaurentSeries L:=IntSeries.subtype
 apply Polynomial.map_injective (mapRingHom ι) (Polynomial.map_injective ι Subtype.val_injective)
 change mapTwice ι _=mapTwice ι _
 rw [map_liftAt]
 simp only [mapTwice,coe_mapRingHom,transform_map,Polynomial.map_C,Polynomial.map_one]
 change transform (C (a t)) (C (a A)) 1 (C (a B)) n (mapTwice a.toRingHom (translate x f)) =
   transform (C (t' : LaurentSeries L)) (C (A' : LaurentSeries L))
     1 (C (B' : LaurentSeries L)) n (mapTwice ι (translate x' (Ua a f hf)))
 rw [ctZ,ctZ,map_liftAt]
 have hx' : ι x' = a.toRingHom x :=hx
 rw [hx',ht,hA,hB]
private theorem eval_transform {A B:Type} [CommRing A] [CommRing B]
  (e :A →+* B) (f :A[X]) {n:ℕ} (hn:f.natDegree≤n)
  (t a b:A) (w y :B) (h:e a+e t*w=(e b+w)*y) :
  (transform t a 1 b n f).eval₂ e w=(e b+w)^n*f.eval₂ e y := by
 rw [transform_sum,eval₂_eq_sum_range' e (Nat.lt_succ_of_le hn),mul_sum]
 simp only [eval₂_finsetSum]
 apply sum_congr rfl
 intro i hi
 have hpow: (e b+w)^i*(e b+w)^(n-i)=(e b+w)^n:= by
  rw [← pow_add,Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hi))]
 simp only [form,eval₂_mul,eval₂_add,eval₂_C,eval₂_pow,eval₂_X,map_one,one_mul,
  h,mul_pow,← hpow]
 ring
theorem eval_change {A B:Type} [CommRing A] [CommRing B]
   (e :A →+* B) (x w y :B) (f :A[X][X]) {n:ℕ} (hn:f.natDegree≤n)
   (c t a b:A) (h:e a+e t*w=(e b+w)*y) :
   evalAt e x w (transform (C t) (C a) 1 (C b) n (translate c f)) =
     (e b+w)^n*evalAt e (x+e c) y f := by
 have hd: (translate c f).natDegree≤n:=natDegree_map_le.trans hn
 have hh:=eval_transform (eval₂RingHom e x) (translate c f) hd (C t) (C a) (C b) w y
   (by simpa only [coe_eval₂RingHom,eval₂_C] using h)
 simp only [coe_eval₂RingHom,eval₂_C] at hh
 simp only [evalAt,coe_eval₂RingHom]
 rw [hh]
 congr 1
 rw [translate,eval₂_map]
 congr 1
 apply ringHom_ext
 · intro r
   change (taylor c (C r)).eval₂ e x=(C r).eval₂ e (x+e c)
   rw [taylor_C,eval₂_C,eval₂_C]
 · change (taylor c (Polynomial.X:A[X])).eval₂ e x=(Polynomial.X:A[X]).eval₂ e (x+e c)
   rw [taylor_X,eval₂_add,eval₂_X,eval₂_C,eval₂_X]
theorem constant_coe {E :Type} [Field E] [Algebra L E]
  (a :E →ₐ[L] LaurentSeries L) (x :L) :
  (constant x :LaurentSeries L)=a (algebraMap L E x) := by
 change (((LaurentSeries.powerSeriesEquivSubring L) (PowerSeries.C x) :IntSeries) :LaurentSeries L)= _
 rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,a.commutes,LaurentSeries.algebraMap_apply,
  PowerSeries.coe_C]
theorem eval_phys :eval₂RingHom scalar τ=phys := by
 apply ringHom_ext
 · intro r
   exact eval₂_C _ _
 · exact eval₂_X _ _
theorem center_specialize (x :L) (f :L[X][X]) (P Q:L[X]) :
   center x (specialize f P Q) =
     f.eval₂ (eval₂RingHom scalar (τ+scalar x)) (phys (taylor x P)/phys (taylor x Q)) := by
 change (center x).toRingHom (f.eval₂ phys (phys P/phys Q))= _
 rw [hom_eval₂,map_div₀]
 change f.eval₂ ((center x).toRingHom.comp phys) (center x (phys P)/ center x (phys Q))= _
 rw [center_poly,center_poly]
 congr 1
 apply ringHom_ext
 · intro c
   change center x (phys (C c))=(C c).eval₂ scalar (τ+scalar x)
   rw [center_poly,taylor_C,eval₂_C]
   rfl
 · change center x τ=(Polynomial.X (R:=L)).eval₂ scalar (τ+scalar x)
   rw [center_poly,taylor_X,map_add,eval₂_X]
   rfl
end
end qFe6O4d
end
