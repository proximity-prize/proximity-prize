import ProximityPrize.SubmissionLower.ZRfXqSb
import ProximityPrize.SubmissionLower.ZULJdud
set_option Elab.async false
open _root_ renaming Field → zrb, Finset.sum_add_distrib → zfW, MvPolynomial.eval → zY9, Polynomial → zM1, Polynomial.X → z7y, PowerSeries → zpm
section
namespace q9sUlTb
noncomputable section
open qFwMjQd (Chart aax simple)
open MvPolynomial
open scoped Matrix
variable {R S:Type} [CommRing R] [CommRing S]
def jac (f g h:Chart R) (q:aax R) :Matrix (Fin 3) (Fin 3) R :=
 fun i j=>eval q (pderiv j ((![f,g,h] :Fin 3→Chart R) i))
theorem jac_map (k :R →+* S) (f g h:Chart R) (q:aax R) :
  (jac f g h q).map k=jac (map k f) (map k g) (map k h) (k ∘ q) := by
 ext i j
 fin_cases i <;> simp [jac,map_eval,pderiv_map]
theorem simple_map {E F:Type} [zrb E] [zrb F] (k :E →+* F)
  {f g h:Chart E} {q:aax E} (hs :simple f g h q) :
  simple (map k f) (map k g) (map k h) (k ∘ q) := by
 obtain ⟨hf,hg,hh,hd⟩:=hs
 obtain ⟨hf',hg',hh'⟩:=zeroAt_map k (show zeroAt f g h q from ⟨hf,hg,hh⟩)
 refine ⟨hf',hg',hh',?_⟩
 change (jac (map k f) (map k g) (map k h) (k ∘ q)).det≠0
 rw [← jac_map]
 change (k.mapMatrix (jac f g h q)).det≠0
 rw [← k.map_det]
 exact fun e=>hd (k.injective (e.trans k.map_zero.symm))
theorem difference_row (k :R →+* S) (u v :aax R)
    (he :k ∘ u=k ∘ v) (p:Chart R) :
    ∃ D:aax R,eval u p-eval v p = ∑ j,D j*(u j - v j) ∧
      ∀ j,k (D j)=eval (k ∘ v) (pderiv j (map k p)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact ⟨0,by simp,by simp⟩
  | add p q hp hq =>
    obtain ⟨D,hD,eD⟩:=hp
    obtain ⟨B,hB,eB⟩:=hq
    refine ⟨D+B,?_,?_⟩
    · simp only [map_add,Pi.add_apply,add_mul,zfW,← hD,← hB]
      ring
    · intro j
      simp [eD,eB]
  | mul_X p i hp =>
    obtain ⟨D,hD,eD⟩:=hp
    refine ⟨fun j=>(if j=i then eval u p else 0)+v i*D j,?_,?_⟩
    · have heval :
          eval u (p*MvPolynomial.X i)-eval v (p*MvPolynomial.X i) =
            eval u p*(u i - v i)+v i*(eval u p-eval v p) := by
        simp only [map_mul,eval_X]
        ring
      rw [heval,hD,Finset.mul_sum]
      simp [add_mul,zfW,mul_assoc]
    · intro j
      have hup:k (eval u p)=eval (k ∘ v) (map k p) := by rw [map_eval,he]
      by_cases hij:i=j
      · subst j
        simp [eD,hup,mul_comm,add_comm]
      · simp [eD,hij,Ne.symm hij,mul_comm]
theorem unique_zero {R F:Type} [CommRing R] [zrb F]
   (k :R →+* F) [IsLocalHom k] (f g h:Chart R) (u v :aax R)
   (hu:zeroAt f g h u) (hv :zeroAt f g h v) (he :k ∘ u=k ∘ v)
   (hs :simple (map k f) (map k g) (map k h) (k ∘ v)) :u=v := by
 classical
 let P:Fin 3→Chart R := ![f,g,h]
 have hz (q:aax R) (hq:zeroAt f g h q) (i:Fin 3) :eval q (P i)=0:= by
   obtain ⟨h₀,h₁,h₂⟩:=hq
   fin_cases i
   · simpa [P] using h₀
   · simpa [P] using h₁
   · simpa [P] using h₂
 choose rows hr₁ hr₂ using fun i=>difference_row k u v he (P i)
 let D:Matrix (Fin 3) (Fin 3) R:=rows
 have hD:D.map k=jac (map k f) (map k g) (map k h) (k ∘ v) := by
   ext i j
   have hr :=hr₂ i j
   change k (rows i j)=eval (k ∘ v) (pderiv j ((![map k f,map k g,map k h] :Fin 3→Chart F) i))
   fin_cases i <;> simpa [P] using hr
 have hd:IsUnit D.det:=IsUnit.of_map k D.det (by
   rw [k.map_det]
   change IsUnit ((D.map k).det)
   rw [hD,isUnit_iff_ne_zero]
   exact hs.2.2.2)
 let w:aax R:= fun j=>u j - v j
 have hw:D *ᵥ w=0:= by
   funext i
   rw [← show eval u (P i)-eval v (P i)=(D *ᵥ w) i from hr₁ i]
   simp [hz u hu i,hz v hv i]
 have heq :w=0:= by
   rw [← Matrix.one_mulVec w,← Matrix.nonsing_inv_mul D hd,← Matrix.mulVec_mulVec,hw,
     Matrix.mulVec_zero]
 exact funext fun i=>sub_eq_zero.mp (congrFun heq i)
end
end q9sUlTb
end
section
namespace q9sUlTb
noncomputable section
abbrev SeriesFrac (E :Type) [zrb E] :=FractionRing (zpm E)
theorem valuation_one (E :Type) [zrb E] :
   ∃ (V:ValuationSubring (SeriesFrac E)) (k :E →+* V) (t:V),
     V.subtype.comp k=(algebraMap (zpm E) (SeriesFrac E)).comp PowerSeries.C ∧
     V.subtype t=algebraMap (zpm E) (SeriesFrac E) PowerSeries.X ∧
     IsLocalRing.residue V t=1 := by
 let K:=SeriesFrac E
 let ι:=algebraMap (zpm E) K
 let j:zM1 E →+* K:=ι.comp Polynomial.coeToPowerSeries.ringHom
 have hj:Function.Injective j :=
   (IsFractionRing.injective (zpm E) K).comp (Polynomial.coe_injective E)
 let e :zM1 E ≃+* j.range :=
   RingEquiv.ofBijective j.rangeRestrict
     ⟨fun _ _ h=>hj (congrArg Subtype.val h),j.rangeRestrict_surjective⟩
 let I:=RingHom.ker ((Polynomial.evalRingHom (1 :E)).comp e.symm.toRingHom)
 obtain ⟨V,hV,hI⟩:=Ideal.image_subset_nonunits_valuationSubring I
   (RingHom.ker_ne_top _)
 let u:zM1 E →+* V:=j.codRestrict V.toSubring fun r=>hV ⟨r,rfl⟩
 have hnon :j (z7y - 1)∈V.nonunits := by
   apply hI
   refine ⟨e (z7y - 1),?_,rfl⟩
   simp [I,RingHom.mem_ker]
 refine ⟨V,u.comp Polynomial.C,u z7y,?_,?_,?_⟩
 · ext c
   change j (Polynomial.C c)=ι (PowerSeries.C c)
   simp [j]
 · change j z7y=ι PowerSeries.X
   simp [j]
 · have hm:u (z7y - 1)∈IsLocalRing.maximalIdeal V :=
     V.coe_mem_nonunits_iff.mp hnon
   simpa [sub_eq_zero] using (IsLocalRing.residue_eq_zero_iff _).mpr hm
end
end q9sUlTb
end
section
namespace qRIxBbd
noncomputable section
open Polynomial
open cu (L)
open q8Z6NHc (Index)
open qFwMjQd
open MvPolynomial (pderiv pderiv_C pderiv_mul pderiv_pow pderiv_X_self pderiv_X_of_ne)
abbrev Yn {E :Type} [zrb E] {d s a :ℕ}
 (f :LineData E d s a) (k :ℕ) :E[X] :=cV k fun i=>(f i).1
abbrev slope {E :Type} [zrb E] {d s a :ℕ}
 (f :LineData E d s a) (k :ℕ) :E[X] :=cV k fun i=>(f i).2
private theorem zero_power_jet {E :Type} [zrb E] (d i:ℕ) (hi:i≤d) :
   (↑(d-i) :E)*0^(d-i-1)=if i=d-1∧d≠0 then 1 else 0:= by
 by_cases h:d-i=1
 · have hh:i=d-1∧d≠0:= by omega
   rw [h,ite_eq_left hh]
   simp
 · have hh : ¬ (i=d-1∧d≠0) := by omega
   rw [ite_eq_right hh]
   rcases Nat.eq_zero_or_pos (d-i) with hz | hp
   · simp [hz]
   · rw [zero_pow (show d-i-1≠0 by omega),mul_zero]
theorem chart_jets {E :Type} [zrb E] {d s a :ℕ} (hd:d≠0)
   (f :LineData E d s a) (x z :E) :
   let q:aax E := ![x,0,z]
   let F:=bY true f
   zY9 q F=(Yn f d).eval x+(slope f d).eval x*z ∧
   zY9 q (pderiv 0 F) =
     (Yn f d).derivative.eval x+(slope f d).derivative.eval x*z ∧
   zY9 q (pderiv 1 F)=(Yn f (d-1)).eval x+(slope f (d-1)).eval x*z ∧
   zY9 q (pderiv 2 F)=(slope f d).eval x := by
 classical
 dsimp only
 refine ⟨?_,?_,?_,?_⟩
 · rw [chart_boundary]
   simp only [cV,eval_finsetSum,Finset.sum_mul,← zfW]
   apply Finset.sum_congr rfl
   intro i _
   split_ifs <;> simp [eval_monomial] <;> ring
 all_goals
   have h01 : (0:Fin 3)≠1 := by decide
   have h02 : (0:Fin 3)≠2 := by decide
   have h12 : (1 :Fin 3)≠2 := by decide
   simp only [bY,ite_true,cV,map_sum,derivative_sum,
     eval_finsetSum,Finset.sum_mul,← zfW]
   apply Finset.sum_congr rfl
   intro i _
   have hi:i.val.1.val≤d:=Nat.le_of_lt_succ i.val.1.isLt
   simp only [map_add,pderiv_mul,pderiv_pow,pderiv_C,pderiv_X_self,
     pderiv_X_of_ne h01,pderiv_X_of_ne h01.symm,pderiv_X_of_ne h02,pderiv_X_of_ne h02.symm,
     pderiv_X_of_ne h12,pderiv_X_of_ne h12.symm,mul_zero,zero_mul,zero_add,add_zero,mul_one,
     map_mul,map_pow,map_natCast,MvPolynomial.eval_C,MvPolynomial.eval_X,
     Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
 · by_cases h:i.val.1.val=d
   · simp [h,eval_monomial,derivative_monomial] <;> ring
   · simp [h,zero_pow (show d-i.val.1.val≠0 by omega)]
 · rw [mul_assoc,zero_power_jet d _ hi]
   by_cases h:i.val.1.val=d-1 <;> simp [h,hd,eval_monomial] <;> ring
 · by_cases h:i.val.1.val=d
   · simp [h,eval_monomial]
   · simp [h,zero_pow (show d-i.val.1.val≠0 by omega)]
theorem h_grade {d s a k :ℕ} (hd:2≤d) (ha :d*s≤a) (hk :k+1≤d) (b c:L) :
    let E :=Eline d s a
    let f :=fLine d s a
    let h:=hLine d s a hd (weight_base hd ha) b c
    let l:E[X] :=C (algebraMap L E b)+C (algebraMap L E c)*z7y
    Yn h k=C (↑(k+1) :E)*Yn f (k+1) -
      C (lineVar (σ:=Index d s a) none*(l^(d-2)).coeff k) ∧
    slope h k=C (↑(k+1) :E)*slope f (k+1) := by
  dsimp only
  have hs :=weight_base hd ha
  have hk' : k≤d-1 := by omega
  have hks : (k+1)*s≤a :=(Nat.mul_le_mul_right s hk).trans ha
  have hbound (j:ℕ) :j+k*s≤a-s↔j+(k+1)*s≤a := by
    rw [Nat.add_mul,one_mul]
    omega
  constructor <;> apply Polynomial.ext <;> intro j
  · rw [coeff_sub,coeff_C_mul,grade_coeff k _ hk',grade_coeff (k+1) _ hk,coeff_C]
    by_cases hj:j+k*s≤a-s
    · rw [dite_eq_left hj,dite_eq_left ((hbound j).mp hj)]
      rfl
    · have h0:j≠0:= by
        intro hj0
        exact hj ((hbound j).mpr (by simpa [hj0] using hks))
      rw [dite_eq_right hj,dite_eq_right (mt (hbound j).mpr hj),ite_eq_right h0,mul_zero,sub_zero]
  · rw [coeff_C_mul,grade_coeff k _ hk',grade_coeff (k+1) _ hk]
    by_cases hj:j+k*s≤a-s
    · rw [dite_eq_left hj,dite_eq_left ((hbound j).mp hj)]
      rfl
    · rw [dite_eq_right hj,dite_eq_right (mt (hbound j).mpr hj),mul_zero]
theorem h_boundary {d s a :ℕ} (hd:2≤d) (ha :d*s≤a) (b c:L) :
  let E :=Eline d s a
  let f :=fLine d s a
  let h:=hLine d s a hd (weight_base hd ha) b c
  let v :=lineVar (σ:=Index d s a) none*(algebraMap L E c)^(d-2)
  Yn h (d-1)=C (d:E)*Yn f d ∧
  slope h (d-1)=C (d:E)*slope f d ∧
  Yn h (d-1-1)=C ((d-1 :ℕ) :E)*Yn f (d-1) - C v ∧
  slope h (d-1-1)=C ((d-1 :ℕ) :E)*slope f (d-1) := by
 dsimp only
 let E :=Eline d s a
 let l:E[X] :=C (algebraMap L E b)+C (algebraMap L E c)*z7y
 have hl:l.natDegree≤1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hj0:j≠0:= by omega
  have hj1 :j≠1 := by omega
  simp [l,coeff_C_mul,coeff_X,coeff_C,hj0,hj1.symm]
 have hlt: (l^(d-2)).natDegree<d-1 := by
  have h:=natDegree_pow_le_of_le (d-2) hl
  omega
 have hz :=coeff_eq_zero_of_natDegree_lt hlt
 have ht: (l^(d-2)).coeff (d-2)=(algebraMap L E c)^(d-2) := by
  simpa [l,coeff_C_mul] using (coeff_pow_of_natDegree_le (m:=d-2) hl)
 have h1 :=h_grade (k :=d-1) hd ha (by omega) b c
 have h2 :=h_grade (k :=d-1-1) hd ha (by omega) b c
 have e1 :d-1+1=d:= by omega
 have e2 :d-1-1+1=d-1 := by omega
 have e3:d-1-1=d-2 := by omega
 change _ = _ - C (_ *(l^(d-2)).coeff (d-1))∧_ at h1
 change _ = _ - C (_ *(l^(d-2)).coeff (d-1-1))∧_ at h2
 rw [hz,mul_zero,C_0,sub_zero] at h1
 rw [e1] at h1
 rw [show (l^(d-2)).coeff (d-1-1)= _ by rw [e3,ht]] at h2
 rw [e2] at h2
 exact ⟨h1.1,h1.2,h2.1,h2.2⟩
end
end qRIxBbd
end
