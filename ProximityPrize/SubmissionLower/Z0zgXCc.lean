import ProximityPrize.SubmissionLower.ZDI0Pnd
set_option Elab.async false
namespace qb1WXKc
noncomputable section
open Polynomial

open private cfq from ProximityPrize.SubmissionLower.CS
private theorem reflect_map {R B:Type*} [CommRing R] [CommRing B] (φ:R →+* B)
  (f :R[X]) (n:ℕ) : (f.reflect n).map φ=(f.map φ).reflect n:= by
 ext i
 simp only [coeff_map,coeff_reflect]
private theorem resultant_reflect_aux {E :Type*} [Field E] (f g:E[X]) (n:ℕ)
    (hg:g.natDegree≤n) (hf :f.Splits) (h0:f.coeff 0≠0) :
    f.reverse.resultant (g.reflect n) f.natDegree n =
      (-1 :E)^(f.natDegree*n)*f.resultant g f.natDegree n:= by
  induction hf using Submonoid.closure_induction with
  | mem h hh =>
    obtain ⟨a,rfl⟩ | ⟨a,rfl⟩:=hh
    · simp
    · have ha :a≠0:= by simpa using h0
      let t := -a⁻¹
      have ht:t≠0:=neg_ne_zero.mpr (inv_ne_zero ha)
      have hat :a*t = -1 := by simp [t,ha]
      have hr : (Polynomial.X+C a).reverse=C a*(Polynomial.X-C t) := by
        have hx : (Polynomial.X:E[X]).reverse=1 := by
          simpa only [reverse,natDegree_X,pow_one,revAt_le le_rfl,Nat.sub_self,pow_zero]
            using (reflect_monomial (R:=E) 1 1)
        rw [reverse_add_C,natDegree_X,pow_one,hx,mul_sub,← C_mul]
        rw [hat,map_neg,C_1]
        rw [sub_neg_eq_add,add_comm]
      have hi: (-a)*t=1 := by simp [t,ha]
      let:Invertible (-a) :=invertibleOfRightInverse (-a) t hi
      have he :=eval₂_reflect_mul_pow (RingHom.id E) (-a) n g hg
      have hev : (g.reflect n).eval t=t^n*g.eval (-a) := by
        change (g.reflect n).eval₂ (RingHom.id E) t= _
        calc
          _=t^n*((g.reflect n).eval₂ (RingHom.id E) (⅟ (-a))*(-a)^n) := by
            change _=t^n*((g.reflect n).eval₂ (RingHom.id E) t*(-a)^n)
            rw [mul_left_comm,← mul_pow,mul_comm t (-a),hi,one_pow,mul_one]
          _ = _:=congrArg (t^n * ·) he
      rw [natDegree_X_add_C,hr,resultant_C_mul_left,
        resultant_X_sub_C_left _ _ _ (natDegree_reflect_le.trans (max_le le_rfl hg)),
        resultant_X_add_C_left _ _ _ hg,hev,← mul_assoc,← mul_pow,hat,one_mul]
  | one=>simp
  | mul f₁ f₂ _ _ ih₁ ih₂ =>
    rw [mul_coeff_zero] at h0
    have h₁:=left_ne_zero_of_mul h0
    have h₂:=right_ne_zero_of_mul h0
    have h₁' : f₁≠0:= fun h=>h₁ (by simp [h])
    have h₂' : f₂≠0:= fun h=>h₂ (by simp [h])
    have hrev₁:f₁.reverse.natDegree=f₁.natDegree := by
      rw [reverse_natDegree,natTrailingDegree_eq_zero.2 (Or.inr h₁),Nat.sub_zero]
    have hrev₂:f₂.reverse.natDegree=f₂.natDegree := by
      rw [reverse_natDegree,natTrailingDegree_eq_zero.2 (Or.inr h₂),Nat.sub_zero]
    have hg' : (g.reflect n).natDegree≤n:=natDegree_reflect_le.trans (max_le le_rfl hg)
    rw [reverse_mul_of_domain,natDegree_mul h₁' h₂',← hrev₁,← hrev₂]
    rw [resultant_mul_left _ _ _ _ hg',hrev₁,hrev₂,resultant_mul_left _ _ _ _ hg,
      ih₁ h₁,ih₂ h₂,Nat.add_mul,pow_add]
    ac_rfl
private theorem resultant_reflect {E :Type*} [Field E] (f g:E[X]) (n:ℕ)
   (hg:g.natDegree≤n) (h0:f.coeff 0≠0) :
   f.reverse.resultant (g.reflect n) f.natDegree n =
     (-1 :E)^(f.natDegree*n)*f.resultant g f.natDegree n:= by
 let φ:=algebraMap E (AlgebraicClosure E)
 apply φ.injective
 simp only [map_mul,map_pow,map_neg,map_one,← resultant_map_map]
 unfold reverse
 rw [reflect_map,reflect_map]
 have H :=resultant_reflect_aux (f.map φ) (g.map φ) n (natDegree_map_le.trans hg)
   (IsAlgClosed.splits _) (by simpa only [coeff_map,map_zero] using φ.injective.ne h0)
 rw [reverse,natDegree_map_eq_of_injective φ.injective f] at H
 exact H
private theorem coeff_X_derivative {E :Type*} [Field E] (f :E[X]) (i:ℕ) :
   (Polynomial.X*f.derivative).coeff i=f.coeff i*(i:E) := by
 cases i with
 | zero=>simp
 | succ i=>rw [coeff_X_mul,coeff_derivative,Nat.cast_succ]
private theorem derivative_reverse {E :Type*} [Field E] (f :E[X])
   (hd:0<f.natDegree) :
   f.reverse.derivative =
     (C (f.natDegree :E)*f-Polynomial.X*f.derivative).reflect (f.natDegree-1) := by
 ext i
 rw [coeff_derivative,coeff_reverse,coeff_reflect,coeff_sub,coeff_C_mul]
 by_cases hi:i<f.natDegree
 · rw [revAt_le (by omega :i+1≤f.natDegree),revAt_le (by omega :i≤f.natDegree-1)]
   set k :=f.natDegree-1-i
   have hk :k=f.natDegree-(i+1) := by omega
   rw [← hk]
   have hsum: ((k :ℕ) :E)+((i+1 :ℕ) :E)=(f.natDegree :E) := by
     rw [← Nat.cast_add,show k+(i+1)=f.natDegree by omega]
   rw [coeff_X_derivative,← hsum,Nat.cast_succ]
   ring
 · rw [revAt_eq_self_of_lt (by omega :f.natDegree< i+1),
     revAt_eq_self_of_lt (by omega :f.natDegree-1< i)]
   have hz₁:=coeff_eq_zero_of_natDegree_lt (p:=f) (show f.natDegree< i+1 by omega)
   rw [hz₁,zero_mul,coeff_X_derivative]
   rcases lt_or_eq_of_le (le_of_not_gt hi) with hlt | he
   · rw [coeff_eq_zero_of_natDegree_lt hlt,mul_zero,zero_mul,sub_zero]
   · rw [← he,mul_comm,sub_self]
theorem bD9 {R:Type*} [CommRing R] [IsDomain R]
  (f :R[X]) (hd:0<f.natDegree) (hn: (f.natDegree :R)≠0) :
  f.derivative.natDegree=f.natDegree-1 := by
 apply (natDegree_derivative_le f).antisymm
 apply le_natDegree_of_ne_zero
 rw [coeff_derivative,← Nat.cast_add_one,Nat.sub_add_cancel hd,coeff_natDegree]
 exact mul_ne_zero (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd)) hn
theorem discr_reverse {E :Type*} [Field E] (f :E[X]) (hd:0<f.natDegree)
   (hn: (f.natDegree :E)≠0) (h0:f.coeff 0≠0) :f.reverse.discr=f.discr := by
 let d:=f.natDegree
 let H :=C (d:E)*f-Polynomial.X*f.derivative
 have hder :=bD9 f hd hn
 have hrev :f.reverse.natDegree=d:= by
   rw [reverse_natDegree,natTrailingDegree_eq_zero.2 (Or.inr h0),Nat.sub_zero]
 have hH :H.natDegree≤d-1 := by
   apply natDegree_le_iff_coeff_eq_zero.mpr
   intro i hi
   have hi₀:0< i:= by omega
   obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hi₀.ne'
   rw [coeff_sub,coeff_C_mul,coeff_X_mul,coeff_derivative]
   rcases lt_or_eq_of_le (show d≤k+1 by omega) with hlt | he
   · rw [coeff_eq_zero_of_natDegree_lt hlt,mul_zero,zero_mul,sub_zero]
   · rw [he,Nat.cast_add,Nat.cast_one,mul_comm,sub_self]
 have hsign: (-1 :E)^(d*(d-1))=1 := by
   obtain ⟨j,hj⟩:=(show 2∣d*(d-1) by
     rw [show d=d-1+1 by omega,Nat.add_sub_cancel,mul_comm]
     exact Nat.two_dvd_mul_add_one _)
   rw [hj,pow_mul]
   simp
 have h:=resultant_reflect f H (d-1) hH h0
 rw [← derivative_reverse f hd,hsign,one_mul] at h
 have hH' : f.resultant H d d=f.resultant (-(Polynomial.X*f.derivative)) d d:= by
   have he :H = -(Polynomial.X*f.derivative)+f*C (d:E) := by
     dsimp [H]
     ring
   rw [he]
   exact resultant_add_mul_right _ _ _ _ _ (by simp) le_rfl
 have he :d-1+1=d:=Nat.sub_add_cancel (by omega)
 rw [← he,resultant_add_right_deg _ _ _ _ 1 hH,pow_one,he] at hH'
 rw [show -(Polynomial.X*f.derivative)=C (-1)*(Polynomial.X*f.derivative) by simp,
   resultant_C_mul_right] at hH'
 have hx :f.resultant Polynomial.X d 1=(-1 :E)^d*f.coeff 0:= by
   have hh:=resultant_X_sub_C_right f d (0:E) le_rfl
   rw [C_0,sub_zero,← coeff_zero_eq_eval_zero] at hh
   exact hh
 have hmul :=resultant_mul_right f (Polynomial.X:E[X]) f.derivative d le_rfl
 rw [natDegree_X,hder,Nat.add_comm,he,hx] at hmul
 rw [hmul,← mul_assoc ((-1 :E)^d),← mul_assoc ((-1 :E)^d),← pow_add,
   show d+d = 2*d by omega,pow_mul] at hH'
 simp only [neg_one_sq,one_pow,one_mul] at hH'
 have hprod:=(congrArg (f.leadingCoeff * ·) h).trans hH'
 have hleft:f.reverse.resultant f.reverse.derivative d (d-1) =
     (-1 :E)^(d*(d-1)/2)*f.coeff 0*f.reverse.discr := by
   rw [← hrev,resultant_deriv (natDegree_pos_iff_degree_pos.mp (hrev.symm ▸ hd)),
     hrev,reverse_leadingCoeff,trailingCoeff_eq_coeff_zero h0]
 rw [hleft,resultant_deriv (natDegree_pos_iff_degree_pos.mp hd)] at hprod
 apply mul_left_cancel₀ (a :=f.leadingCoeff*(-1 :E)^(d*(d-1)/2)*f.coeff 0)
   (mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd))
     (pow_ne_zero _ (by simp))) h0)
 linear_combination hprod
theorem discr_taylor {R:Type*} [CommRing R] [IsDomain R] (f :R[X]) (b:R)
   (hd:0<f.natDegree) : (f.taylor b).discr=f.discr := by
 have h:=cfq f f.derivative b le_rfl (natDegree_derivative_le f)
 have hder : (f.taylor b).derivative=f.derivative.taylor b:= by
   simp only [taylor_apply,derivative_comp,derivative_add,derivative_X,derivative_C,add_zero,
     one_mul]
 have hp:0<(f.taylor b).natDegree := by simpa only [natDegree_taylor] using hd
 have h' := resultant_deriv (natDegree_pos_iff_degree_pos.mp hp)
 rw [natDegree_taylor,leadingCoeff_taylor] at h'
 rw [← hder,h',resultant_deriv (natDegree_pos_iff_degree_pos.mp hd)] at h
 exact mul_left_cancel₀
   (mul_ne_zero (pow_ne_zero _ (by simp)) (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd))) h
theorem discr_scaleRoots {R:Type*} [CommRing R] [IsDomain R] (f :R[X]) (r :R)
   (hd:0<f.natDegree) (hn: (f.natDegree :R)≠0) :
   (f.scaleRoots r).discr=r^(f.natDegree*(f.natDegree-1))*f.discr := by
 have hdeg:=bD9 f hd hn
 have hder : (f.scaleRoots r).derivative=f.derivative.scaleRoots r := by
   ext i
   rw [coeff_derivative,coeff_scaleRoots,coeff_scaleRoots,hdeg,coeff_derivative,
     show f.natDegree-(i+1)=f.natDegree-1-i by omega]
   ring
 have h:=resultant_scaleRoots f f.derivative r
 have hp:0<(f.scaleRoots r).natDegree := by simpa only [natDegree_scaleRoots] using hd
 change (f.scaleRoots r).resultant (f.derivative.scaleRoots r) _ _ = _ at h
 rw [natDegree_scaleRoots f.derivative,hdeg,← hder] at h
 conv at h=>lhs; rw [← natDegree_scaleRoots f r]
 rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp hp),natDegree_scaleRoots,
   leadingCoeff_scaleRoots,resultant_deriv (natDegree_pos_iff_degree_pos.mp hd)] at h
 apply mul_left_cancel₀ (a :=(-1 :R)^(f.natDegree*(f.natDegree-1)/2)*f.leadingCoeff)
   (mul_ne_zero (pow_ne_zero _ (by simp)) (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd)))
 linear_combination h
end
end qb1WXKc
