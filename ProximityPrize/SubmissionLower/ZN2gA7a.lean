import ProximityPrize.SubmissionLower.Z5cOcra
import ProximityPrize.SubmissionLower.ZQfUTPd
set_option Elab.async false
set_option autoImplicit true
open Polynomial renaming coeff_eq_zero_of_natDegree_lt→qz0,coeff_derivative→qz1,natDegree_derivative_le→qz2,le_natDegree_of_ne_zero→qz3
set_option backward.isDefEq.respectTransparency false
namespace qWnROxa
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L)
open qNu3xvc qypA4Sc
open private fXo from ProximityPrize.SubmissionLower.ZQfUTPd
open private chart_root chartIntegral from ProximityPrize.SubmissionLower.Z5cOcra
private def other {R:Type} [CommRing R] (d:ℕ) (f :R[X]) :R[X] :=
 C (d:R)*f-Polynomial.X*f.derivative
private theorem coeff_other {R:Type} [CommRing R] (d:ℕ) (f :R[X]) (i:ℕ) :
   (other d f).coeff i=((d:R)-(i:R))*f.coeff i:= by
 cases i with
 | zero=>simp [other]
 | succ i =>
   simp only [other,coeff_sub,coeff_C_mul,coeff_X_mul,qz1,Nat.cast_succ,sub_mul]
   ring
private theorem other_degree {R:Type} [CommRing R] (f :R[X]) (m:ℕ)
   (hf :f.natDegree≤ m+1) : (other (m+1) f).natDegree≤ m:= by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro i hi
 rw [coeff_other]
 rcases eq_or_lt_of_le (show m+1≤ i by omega) with h | h
 · simp [← h]
 · rw [qz0 (hf.trans_lt h),mul_zero]
private theorem reflect_partials {R:Type} [CommRing R] (f :R[X]) (m:ℕ)
    (hm:f.natDegree=m+1) :
    reflect m (other (m+1) f)=f.reverse.derivative ∧
      reflect m f.derivative=other (m+1) f.reverse := by
  have hP:f.derivative.natDegree≤ m:= by simpa [hm] using qz2 f
  have hQ:=other_degree f m hm.le
  have hR:f.reverse.natDegree≤ m+1 :=f.reverse_natDegree_le.trans hm.le
  constructor <;> ext i
  · by_cases hi:i≤ m
    · have h:=show i+1≤f.natDegree by omega
      rw [coeff_reflect,revAt_le hi,coeff_other,qz1,coeff_reverse,revAt_le h,hm,
        ← Nat.cast_sub (show m-i≤ m+1 by omega),
        show m+1-(m-i)=i+1 by omega,show m+1-(i+1)=m-i by omega,mul_comm]
      simp only [Nat.cast_add,Nat.cast_one]
    · rw [qz0 (natDegree_reflect_le.trans_lt (max_lt (lt_of_not_ge hi)
        (hQ.trans_lt (lt_of_not_ge hi)))),qz1,
        qz0 (by omega :f.reverse.natDegree< i+1),zero_mul]
  · by_cases hi:i≤ m
    · rw [coeff_reflect,revAt_le hi,qz1,coeff_other,coeff_reverse,
        revAt_le (show i≤f.natDegree by omega),hm,← Nat.cast_sub (show i≤ m+1 by omega),
        show m+1-i=m-i+1 by omega,mul_comm]
      simp only [Nat.cast_add,Nat.cast_one]
    · rw [qz0 (natDegree_reflect_le.trans_lt (max_lt (lt_of_not_ge hi)
        (hP.trans_lt (lt_of_not_ge hi)))),
        qz0 ((other_degree f.reverse m hR).trans_lt (lt_of_not_ge hi))]
private theorem padded_ne_zero {F:Type} [Field F] {P Q:F[X]} {m:ℕ}
  (hP:P.natDegree=m) (hn:P≠0) (hQ:Q.natDegree≤ m) (h:IsCoprime P Q) :
  P.resultant Q m m≠0:= by
 subst m
 have hp:=resultant_add_right_deg P Q P.natDegree Q.natDegree (P.natDegree-Q.natDegree) le_rfl
 rw [Nat.add_sub_of_le hQ] at hp
 rw [hp]
 exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hn)) (resultant_ne_zero _ _ h)
private theorem common_root {R F:Type} [CommRing R] [Field F] (a :R →+* F)
  {P Q:R[X]} {m:ℕ} (hm:0< m) (hP:P.natDegree≤ m) (hQ:Q.natDegree≤ m)
  (t:F) (hp:P.eval₂ a t=0) (hq:Q.eval₂ a t=0) :
  a (P.resultant Q m m)=0:= by
 obtain ⟨u,v,_,_,huv⟩:=exists_mul_add_mul_eq_C_resultant P Q hP hQ (Or.inl hm.ne')
 have hh:=congrArg (eval₂RingHom a t) huv
 simpa only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,hp,hq,zero_mul,add_zero] using hh.symm
private theorem cap_drop {R F:Type} [CommRing R] [Field F] (a :R →+* F)
   {P:R[X]} {m:ℕ} (hm:0< m) (hP:P.natDegree≤ m) (h:a (P.coeff m)=0) :
   (P.map a).natDegree< m:= by
 apply (lt_of_le_of_lt (b:=m-1)) _ (by omega)
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro i hi
 rw [coeff_map]
 rcases eq_or_lt_of_le (show m≤ i by omega) with heq | hlt
 · simpa only [← heq] using h
 · rw [qz0 (hP.trans_lt hlt),map_zero]
private theorem elim_bound {E :Type} [Field E] (A:Equation E) {m:ℕ} (hm:m+1=A.d) :
   (A.f.derivative.resultant (other (m+1) A.f) m m).natDegree≤horizontalDegree A:= by
 have hw (i:ℕ) (hi:i≤A.d) :
     (A.f.coeff i).natDegree+i*A.s≤A.b+A.d*A.s := by
   rcases A.weight i with h | h
   · exact h
   · rw [h,natDegree_zero,zero_add]
     exact (Nat.mul_le_mul_right _ hi).trans (Nat.le_add_left _ _)
 have hP (i:ℕ) (hi:i≤ m) :
     (A.f.derivative.coeff i).natDegree+A.s*i≤A.b+m*A.s := by
   have h:=hw (i+1) (by omega)
   rw [← hm,Nat.add_mul,one_mul,Nat.add_mul,one_mul] at h
   rw [qz1,← Nat.cast_succ,← C_eq_natCast,mul_comm A.s i]
   exact (Nat.add_le_add_right (natDegree_mul_C_le _ _) _).trans (by omega)
 have hQ (i:ℕ) (hi:i≤ m) :
     ((other (m+1) A.f).coeff i).natDegree+A.s*i≤A.b+A.d*A.s := by
   rw [coeff_other,← C_eq_natCast,← C_eq_natCast,← C_sub,mul_comm A.s i]
   exact (Nat.add_le_add_right (natDegree_C_mul_le _ _) _).trans (hw i (by omega))
 have hdP:A.f.derivative.natDegree≤ m:= by
   simpa [← hm] using qz2 A.f
 have hdQ: (other (m+1) A.f).natDegree≤ m:=other_degree A.f m hm.ge
 have h:=fXo _ _ m m A.s (A.b+m*A.s) (A.b+A.d*A.s)
   (fun i h=>hP i ((qz3 h).trans hdP))
   (fun i h=>hQ i ((qz3 h).trans hdQ))
 rw [Nat.add_comm (m*(A.b+A.d*A.s))] at h
 refine h.trans_eq ?_
 have h2 :2*A.d-2=m+m:= by omega
 have h1 :A.d-1=m:= by omega
 unfold horizontalDegree
 rw [h2,h1,show m*(A.b+m*A.s)+m*(A.b+A.d*A.s) =
   ((m+m)*A.b+A.d*m*A.s)+A.s*(m*m) by ring,Nat.add_sub_cancel]
private theorem elim_nonzero {E :Type} [Field E] [Algebra L E] (A:Equation E)
   {m:ℕ} (hm:m+1=A.d) (ht:A.d<p) :
   A.f.derivative.resultant (other (m+1) A.f) m m≠0:= by
 let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let _:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
 let _:CharP E[X] p:=inferInstance
 let B:=FractionRing E[X]
 let a :E[X] →+* B:=algebraMap _ _
 let H :=A.f.map a
 have q1 :H.natDegree=m+1 :=
   (natDegree_map_eq_of_injective (IsFractionRing.injective E[X] B) _).trans hm.symm
 have q3:Irreducible H :=
   ((A.irreducible.isPrimitive A.positive.ne').irreducible_iff_irreducible_map_fraction_map
     (K:=B)).mp A.irreducible
 have hm' : m+1<p:=hm.symm ▸ ht
 have hc₀: ((m+1 :ℕ) :E[X])≠0:= fun h =>
   (not_le_of_gt hm') (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff _ p _).mp h))
 have hc: ((m+1 :ℕ) :B)≠0:= by
   simpa only [map_natCast] using (map_ne_zero_iff a (IsFractionRing.injective E[X] B)).mpr hc₀
 have hh:H.derivative.coeff m≠0:= by
   rw [qz1,← q1,← leadingCoeff]
   simpa only [Nat.cast_add,Nat.cast_one] using
     mul_ne_zero (leadingCoeff_ne_zero.mpr q3.ne_zero) hc
 have hp:H.derivative.natDegree=m :=
   le_antisymm (by simpa [q1] using qz2 H) (qz3 hh)
 have hn:H.derivative≠0:= fun h=>hh (by simp [h])
 have hcop:IsCoprime H H.derivative :=(separable_iff_derivative_ne_zero q3).mpr hn
 have hunit :IsCoprime H.derivative (C ((m+1 :ℕ) :B)) := by
   refine ⟨0,C (((m+1 :ℕ) :B)⁻¹),?_⟩
   rw [zero_mul,zero_add,← C_mul,inv_mul_cancel₀ hc,C_1]
 have hc' : IsCoprime H.derivative (other (m+1) H) := by
   have h:=hunit.mul_right hcop.symm
   have hadd:IsCoprime H.derivative (other (m+1) H+Polynomial.X*H.derivative) := by
     simpa only [other,sub_add_cancel] using h
   exact hadd.of_add_mul_right_right
 have q0:=padded_ne_zero hp hn (other_degree H m q1.le) hc'
 have q2 :A.f.derivative.map a=H.derivative :=(derivative_map _ _).symm
 have ho: (other (m+1) A.f).map a=other (m+1) H := by
   rw [other,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,map_natCast,
     Polynomial.map_mul,Polynomial.map_X,q2]
   rfl
 rw [← q2,← ho,resultant_map_map] at q0
 exact fun h=>q0 (by rw [h,map_zero])
private theorem elim_vanish {E :Type} [Field E] [Algebra L E] (A:Equation E)
   {m:ℕ} (hm:m+1=A.d) (hd:2≤A.d) (r :Bool) (v :GraphVal A r)
   (h:Horizontal v) (hp:v.val (polar A r)<1) :
   v.val (ajm A (A.f.derivative.resultant (other (m+1) A.f) m m))<1 := by
 obtain ⟨φ,hφ,_⟩:=chartIntegral A v h
 let π:=IsLocalRing.residue v.val.valuationSubring
 let ψ:=π.comp φ
 let a :=ψ.comp (C:E[X] →+* E[X][X])
 let y :=ψ (Polynomial.X:E[X][X])
 have he (f :E[X][X]) :f.eval₂ a y=ψ f := by
   dsimp only [a,y]
   rw [← hom_eval₂,eval₂_C_X]
 have hc (f :E[X][X]) :ψ f=0↔v.val (KM A r f)<1 := by
   change π (φ f)=0↔_
   rw [IsLocalRing.residue_eq_zero_iff,v.val.mem_maximalIdeal_iff,hφ]
 have hr : (chartEq A r).eval₂ a y=0:= by
   rw [he,hc,chart_root A hd r,map_zero]
   exact zero_lt_one
 have q2 : (chartEq A r).derivative.eval₂ a y=0:= by
   rwa [he,hc]
 have q0:0< m:= by omega
 let P:=A.f.derivative
 let Q:=other (m+1) A.f
 have hP:P.natDegree≤ m:= by simpa [P,← hm] using qz2 A.f
 have hQ:Q.natDegree≤ m:=other_degree A.f m hm.ge
 have q1 (f :E[X][X]) (hf :f.eval₂ a y=0) (hg:f.derivative.eval₂ a y=0) :
     (other (m+1) f).eval₂ a y=0:= by
   simp only [other,eval₂_sub,eval₂_mul,hf,hg,mul_zero,sub_zero]
 suffices hq:a (P.resultant Q m m)=0 by
   have hz :ψ (C (P.resultant Q m m))=0:=hq
   rw [hc] at hz
   simpa only [KM,coe_eval₂RingHom,eval₂_C,ajm] using hz
 cases r with
 | false=>exact common_root a q0 hP hQ y q2 (q1 _ hr q2)
 | true =>
   change A.f.reverse.eval₂ a y=0 at hr
   change A.f.reverse.derivative.eval₂ a y=0 at q2
   obtain ⟨hRQ,hRP⟩:=reflect_partials A.f m hm.symm
   have hp' : (reflect m P).eval₂ a y=0:= by rw [hRP]; exact q1 _ hr q2
   have hq' : (reflect m Q).eval₂ a y=0:= by rwa [hRQ]
   by_cases hy :y=0
   · simp only [hy,eval₂_at_zero,coeff_reflect,revAt_zero] at hp' hq'
     rw [← resultant_map_map]
     exact resultant_eq_zero_of_lt_lt _ _ _ _ (cap_drop a q0 hP hp') (cap_drop a q0 hQ hq')
   · let _:=invertibleOfNonzero (inv_ne_zero hy)
     refine common_root a q0 hP hQ y⁻¹ ?_ ?_
     · exact (eval₂_reflect_eq_zero_iff a y⁻¹ m P hP).mp (by simpa [invOf_eq_inv] using hp')
     · exact (eval₂_reflect_eq_zero_iff a y⁻¹ m Q hQ).mp (by simpa [invOf_eq_inv] using hq')
theorem proof :qypA4Sc.c1 := by
 intro E _ _ A hd ht
 let m:=A.d-1
 have hm:m+1=A.d:=Nat.sub_add_cancel (by omega)
 exact ⟨_,elim_nonzero A hm ht,elim_bound A hm,elim_vanish A hm hd⟩
end
end qWnROxa
