import ProximityPrize.SubmissionLower.ZEMNtxd
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qEAs6me
noncomputable section
open cu (L)
open qfbIfsd (form Detects)
open q2tSkEc (bzm caps orders top L4 DetectsValue)
open scoped BigOperators Classical
variable {s b d:ℕ}
private theorem tied_map {M N :Type} [CommSemiring M] [CommSemiring N] (m:M →+* N)
  (a :bzm s b d→M) (r :bzm s b d) :m (tied a r)=tied (m ∘ a) r := by
 unfold tied
 split_ifs <;> simp
theorem tie_degree (R:Coeff s b d) : (tie R).totalDegree≤R.totalDegree := by
 apply cYh R
 intro i
 unfold tied
 split_ifs
 · rw [← map_natCast (MvPolynomial.C:L →+* Coeff s b d) d]
   exact MvPolynomial.isHomogeneous_C_mul_X _ _
 · exact MvPolynomial.isHomogeneous_X _ _
private theorem tie_eval {M:Type} [CommSemiring M] (m:L →+* M)
  (a :bzm s b d→M) (R:Coeff s b d) : (tie R).eval₂ m a=R.eval₂ m (tied a) := by
 change (MvPolynomial.eval₂Hom m a) (R.eval₂ MvPolynomial.C (tied MvPolynomial.X))= _
 rw [MvPolynomial.eval₂_comp_left]
 have hm: (MvPolynomial.eval₂Hom m a).comp MvPolynomial.C=m:= by ext k; simp
 rw [hm]
 congr 1
 funext i
 rw [Function.comp_apply,tied_map]
 simp [Function.comp_def]
private def cV {M:Type} [CommSemiring M] (a :bzm s b d→M) (t:Fin 3)
   (i:Fin (orders d t+1)) (x :M) :M :=
 ∑ j:Fin (caps b s t+(orders d t-i.val)*s+1),a ⟨t,i,j⟩*x^j.val
private theorem form_grades {M:Type} [CommSemiring M] (a :bzm s b d→M)
   (t:Fin 3) (x y :M) :form a t x y =
     ∑ i:Fin (orders d t+1),cV a t i x*y ^i.val := by
 rw [form,Fintype.sum_sigma]
 simp only [cV,Finset.sum_mul]
private theorem top_grade {M:Type} [CommSemiring M] (a :bzm s b d→M)
   (t:Fin 3) (x :M) :top a t x=cV a t ⟨orders d t,Nat.lt_succ_self _⟩ x := by
 rw [top,Fintype.sum_sigma,Finset.sum_eq_single ⟨orders d t,Nat.lt_succ_self _⟩]
 · simp [cV]
 · intro i _ hi
   have hv :i.val≠orders d t:= fun he=>hi (Fin.ext he)
   simp [hv]
 · simp
private theorem topPoly_grade {M:Type} [CommSemiring M] (a :bzm s b d→M)
  (t:Fin 3) (x :M) :
  (topPoly a t).eval x=cV a t ⟨orders d t,Nat.lt_succ_self _⟩ x := by
 simp only [topPoly,Polynomial.eval_finsetSum,Polynomial.eval_monomial,cV,topSlot]
 exact Fintype.sum_equiv (finCongr (by simp)) _ _ (fun _=>rfl)
theorem top_eq_eval {M:Type} [CommSemiring M] (a :bzm s b d→M)
   (t:Fin 3) (x :M) : (topPoly a t).eval x=top a t x :=
 (topPoly_grade a t x).trans (top_grade a t x).symm
private theorem form_tied_fixed {M:Type} [CommSemiring M] (a :bzm s b d→M)
  (t:Fin 3) (ht:t≠2) (x y :M) :form (tied a) t x y=form a t x y := by
 simp [form,tied,ht]
private theorem topPoly_tied {M:Type} [CommSemiring M] (a :bzm s b d→M)
  (x :M) : (topPoly (tied a) 2).eval x=(d:M)*(topPoly a 0).eval x := by
 simp only [topPoly,Polynomial.eval_finsetSum,Polynomial.eval_monomial,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro j _
 have he :tied a ⟨2,topSlot s b d 2 j⟩=(d:M)*a ⟨0,topSlot s b d 0 j⟩:= by
  unfold tied
  rw [dite_eq_left ⟨rfl,rfl⟩]
  rfl
 rw [he,mul_assoc]
private theorem form_tied_value {M:Type} [CommRing M] (a :bzm s b d→M)
   (x y :M) :form (tied a) 2 x y=L4 a x y := by
 rw [L4,add_comm (form a 2 x y)]
 apply (sub_eq_iff_eq_add).mp
 rw [form_grades,form_grades,← Finset.sum_sub_distrib,
   Finset.sum_eq_single ⟨orders d 2,Nat.lt_succ_self _⟩]
 · rw [← topPoly_grade,← topPoly_grade,topPoly_tied,top_eq_eval,top_eq_eval,sub_mul]
   rfl
 · intro i _ hi
   have hv :i.val≠d-1 := fun he=>hi (Fin.ext he)
   simp [cV,tied,hv]
 · simp
theorem detect_tie {R:Coeff s b d} (hR:Detects R) :DetectsValue (tie R) := by
 intro M _ m a x y hf hg hh
 rw [tie_eval]
 apply hR m (tied a) x y
 intro t
 fin_cases t
 · exact (form_tied_fixed a 0 (by decide) x y).trans hf
 · exact (form_tied_fixed a 1 (by decide) x y).trans hg
 · exact (form_tied_value a x y).trans hh
end
end qEAs6me
