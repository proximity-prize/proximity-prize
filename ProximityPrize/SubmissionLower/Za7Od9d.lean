import Mathlib.Algebra.Polynomial.Homogenize
import ProximityPrize.SubmissionLower.ZK7Ye0a
set_option Elab.async false
set_option autoImplicit true
open MvPolynomial renaming C→qz0,aeval→qz1,isHomogeneous_C_mul_X→qz2,aeval_C→qz3,algebraMap_eq→qz4
set_option maxHeartbeats 600000
namespace qVXVW4b
noncomputable section
open Polynomial Finset qQ9yWTb
open P5 (K)


open Finset.HasAntidiagonal
open cu (FX aZ Equation vm qD)
open scoped Classical
private abbrev Binary :=MvPolynomial (Fin 2) aZ
private abbrev scalar :FX →+* aZ :=qz0
private abbrev c₂:FX →+* Binary :=qz0.comp scalar
private def form (a b:FX) :Binary :=
 c₂ a*MvPolynomial.X 0+c₂ b*MvPolynomial.X 1
private def substitute (a b c d:FX) :Binary →ₐ[aZ] Binary :=
 qz1 ![form a b,form c d]
private def sW :Binary →ₐ[aZ] Equation :=qz1 (![Polynomial.X,1] :Fin 2→Equation)
private def changeOrd (a b c d:FX) (f :Equation) (n:ℕ) :Equation :=
 sW (substitute a b c d (f.homogenize n))
private theorem substitute_form (a b c d e f :FX) :
  substitute a b c d (form e f)=form (e*a+f*c) (e*b+f*d) := by
 simp only [substitute,form,map_add,map_mul,RingHom.comp_apply,
  qz3,qz4,MvPolynomial.aeval_X,
  Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
 ring
private theorem substitute_zero (a b c d:FX) :
 substitute a b c d (MvPolynomial.X 0)=form a b:= by simp [substitute]
private theorem substitute_one (a b c d:FX) :
 substitute a b c d (MvPolynomial.X 1)=form c d:= by simp [substitute]
private theorem inverse (a b c d:FX) (hn:a*d-b*c≠0) :
   (substitute (d/(a*d-b*c)) (-b/(a*d-b*c)) (-c/(a*d-b*c)) (a/(a*d-b*c))).comp
     (substitute a b c d)=AlgHom.id aZ Binary := by
 let δ:=a*d-b*c
 have hδ:δ≠0:=hn
 have h₀:a*(d/δ)+b*(-c/δ)=1 := by
   rw [← mul_div_assoc,← mul_div_assoc,← add_div,show a*d+b*(-c)=δ by dsimp [δ]; ring,div_self hδ]
 have h₁:a*(-b/δ)+b*(a/δ)=0:= by
   rw [← mul_div_assoc,← mul_div_assoc,← add_div,show a*(-b)+b*a=0 by ring,zero_div]
 have h₂:c*(d/δ)+d*(-c/δ)=0:= by
   rw [← mul_div_assoc,← mul_div_assoc,← add_div,show c*d+d*(-c)=0 by ring,zero_div]
 have h₃:c*(-b/δ)+d*(a/δ)=1 := by
   rw [← mul_div_assoc,← mul_div_assoc,← add_div,show c*(-b)+d*a=δ by dsimp [δ]; ring,div_self hδ]
 change (substitute (d/δ) (-b/δ) (-c/δ) (a/δ)).comp _ = _
 apply MvPolynomial.algHom_ext
 intro i
 simp only [AlgHom.comp_apply,AlgHom.id_apply]
 have hi:i=0∨i=1 := by fin_cases i <;> simp
 rcases hi with rfl | rfl
 · rw [substitute_zero,substitute_form,h₀,h₁]
   simp [form]
 · rw [substitute_one,substitute_form,h₂,h₃]
   simp [form]
private theorem changed_primitive {a b c d:FX} (hm:a*d-b*c≠0)
   {f :Equation} {n:ℕ} (hf :f.IsPrimitive) (hd:f.natDegree≤n) :
   (changeOrd a b c d f n).IsPrimitive := by
 let B:=substitute a b c d (f.homogenize n)
 have hB:B.IsHomogeneous n:= by
   change (qz1 ![form a b,form c d] (f.homogenize n)).IsHomogeneous n
   have h (s t:FX) : (form s t).IsHomogeneous 1 :=
     (qz2 _ _).add (qz2 _ _)
   have hh:=(isHomogeneous_homogenize (n:=n) f).aeval
     (![form a b,form c d] :Fin 2→Binary) (fun i=> by fin_cases i <;> exact h _ _)
   rw [Nat.one_mul] at hh
   exact hh
 have hb: (changeOrd a b c d f n).homogenize n=B :=
   homogenize_eq_of_isHomogeneous hB rfl
 intro r hr
 apply hf r
 obtain ⟨q,hq⟩:=hr
 let inv :=substitute (d/(a*d-b*c)) (-b/(a*d-b*c)) (-c/(a*d-b*c)) (a/(a*d-b*c))
 have hfac:B=qz0 r*q.homogenize n:= by
   rw [← hb,hq,homogenize_C_mul]
 have hid :inv.comp (substitute a b c d)=AlgHom.id aZ Binary :=inverse a b c d hm
 have hback :inv B=f.homogenize n :=
   DFunLike.congr_fun hid (f.homogenize n)
 refine ⟨sW (inv (q.homogenize n)),?_⟩
 have h₁:inv (qz0 r)=qz0 r := by
   simp only [inv,substitute,qz3,qz4]
 have h₂:sW (qz0 r)=C r := by
   simp only [sW,qz3,← C_eq_algebraMap]
 calc
   f=sW (inv B) := by rw [hback]; exact (aeval_homogenize_X_one f hd).symm
   _ = _:= by rw [hfac,map_mul,h₁,map_mul,h₂]
private def line (a b:FX) :FX[X] :=C a*Polynomial.X+C b
private theorem change_sum (a b c d:FX) (f :Equation) (n:ℕ) :
    changeOrd a b c d f n =
      ∑ k∈antidiagonal n,C (f.coeff k.1) *
        (((line a b)^k.1*(line c d)^k.2).map scalar) := by
  have h (s t:FX) :sW (form s t)=(line s t).map scalar := by
    simp [sW,form,line,RingHom.comp_apply]
  have he :sW.comp (substitute a b c d) =
      qz1 ![(line a b).map scalar,(line c d).map scalar] := by
    rw [substitute,MvPolynomial.comp_aeval]
    congr 1
    funext i
    fin_cases i <;> exact h _ _
  change (sW.comp (substitute a b c d)) (f.homogenize n)= _
  rw [he,homogenize,map_sum]
  apply sum_congr rfl
  intro k _
  simp [MvPolynomial.aeval_monomial,Finsupp.prod_fintype,Fin.prod_univ_two]
private theorem change_caps (a b c d:FX) {f :Equation} {n u:ℕ} (hs :vm f u) :
   (changeOrd a b c d f n).natDegree≤n∧vm (changeOrd a b c d f n) u:= by
 have h (a b:FX) : (line a b).natDegree≤1 :=natDegree_linear_le
 rw [change_sum]
 constructor
 · apply natDegree_sum_le_of_forall_le
   intro k hk
   have he :=mem_antidiagonal.mp hk
   refine (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (natDegree_mul_le.trans ?_))
   simpa only [Nat.mul_one,he] using
     Nat.add_le_add (natDegree_pow_le_of_le k.1 (h a b)) (natDegree_pow_le_of_le k.2 (h c d))
 · intro j
   rw [finsetSum_coeff]
   apply MvPolynomial.totalDegree_finsetSum_le
   intro k _
   rw [coeff_C_mul,coeff_map]
   exact (MvPolynomial.totalDegree_mul _ _).trans
     (by rw [MvPolynomial.totalDegree_C,add_zero]; exact hs k.1)
private theorem change_eval (a b c d:FX) {f :Equation} {n:ℕ} (hn:f.natDegree≤n)
   (z :K) (y s :FX) (hy :a*y+b=(c*y+d)*s) :
   (changeOrd a b c d f n).eval₂ (qD z) y =
     f.eval₂ (qD z) s*(c*y+d)^n:= by
 let E :=eval₂RingHom (qD z) y
 have hE (r :aZ) :E (C r)=qD z r :=eval₂_C _ _
 have hline (v w:FX) :E ((line v w).map scalar)=v*y+w:= by
   simp [E,line,cu.qD]
 rw [change_sum,eval₂_eq_sum_range' (qD z) (Nat.lt_succ_iff.mpr hn),
   Nat.sum_antidiagonal_eq_sum_range_succ_mk,sum_mul]
 change E (∑ _∈range (n+1),_)= _
 rw [map_sum]
 apply sum_congr rfl
 intro k hk
 have hkn:k≤n:=Nat.lt_succ_iff.mp (mem_range.mp hk)
 simp only [Polynomial.map_mul,Polynomial.map_pow,map_mul,map_pow,hE,hline,hy]
 change qD z (f.coeff k)*(((c*y+d)*s)^k*(c*y+d)^(n-k)) =
   qD z (f.coeff k)*s^k*(c*y+d)^n
 rw [mul_pow]
 calc
   _=(qD z (f.coeff k)*s^k)*((c*y+d)^k*(c*y+d)^(n-k)) := by ring
   _ = _:= by rw [← pow_add,Nat.add_sub_of_le hkn]
end
end qVXVW4b
