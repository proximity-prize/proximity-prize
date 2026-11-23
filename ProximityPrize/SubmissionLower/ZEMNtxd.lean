import ProximityPrize.SubmissionLower.ZOb5aoe
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qEAs6me
noncomputable section
open cu (L)
open q2tSkEc (bzm caps)
open scoped BigOperators Classical
theorem topPoly_map {M N :Type} [CommSemiring M] [CommSemiring N] (m:M →+* N)
  {s b d:ℕ} (a :bzm s b d→M) (t:Fin 3) :
  (topPoly a t).map m=topPoly (m ∘ a) t:= by
 simp only [topPoly,Polynomial.map_sum,Polynomial.map_monomial,Function.comp_apply]
theorem topRes_eval {M:Type} [CommRing M] (m:L →+* M) {s b d:ℕ}
   (a :bzm s b d→M) :
   (topRes :Coeff s b d).eval₂ m a =
     (topPoly a 0).resultant (topPoly a 1) b (b+s+1) := by
 change MvPolynomial.eval₂Hom m a topRes= _
 rw [topRes,← Polynomial.resultant_map_map,topPoly_map,topPoly_map]
 rw [show (MvPolynomial.eval₂Hom m a) ∘ MvPolynomial.X=a from
   funext (MvPolynomial.eval₂Hom_X' m a)]
theorem coeff_topPoly {M:Type} [CommSemiring M] {s b d:ℕ}
   (a :bzm s b d→M) (t:Fin 3) (j:ℕ) :
   (topPoly a t).coeff j =
     if h:j<caps b s t+1 then a ⟨t,topSlot s b d t ⟨j,h⟩⟩ else 0:= by
 simp only [topPoly,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
 split_ifs with h
 · rw [Finset.sum_eq_single (⟨j,h⟩:Fin (caps b s t+1))]
   · simp
   · intro i _ hi
     exact ite_eq_right (fun he=>hi (Fin.ext he))
   · simp
 · apply Finset.sum_eq_zero
   intro i _
   have hn: (i:ℕ)≠j:= fun he=>h (he ▸ i.isLt)
   simp [hn]
theorem topPoly_degree {M:Type} [CommSemiring M] {s b d:ℕ}
  (a :bzm s b d→M) (t:Fin 3) : (topPoly a t).natDegree≤ caps b s t:= by
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro j hj
 rw [coeff_topPoly,dite_eq_right (by omega)]
theorem cYh {ι κ:Type} (R:MvPolynomial ι L) (g:ι→MvPolynomial κ L)
  (hg : ∀ i,(g i).IsHomogeneous 1) :
  (R.eval₂ MvPolynomial.C g).totalDegree≤R.totalDegree := by
 let e :=MvPolynomial.eval₂Hom MvPolynomial.C g
 change (e R).totalDegree≤R.totalDegree
 conv_lhs=>rw [← MvPolynomial.sum_homogeneousComponent R]
 rw [map_sum]
 apply MvPolynomial.totalDegree_finsetSum_le
 intro j hj
 have he :=(MvPolynomial.homogeneousComponent_isHomogeneous j R).eval₂
  MvPolynomial.C g (MvPolynomial.isHomogeneous_C _) hg
 exact he.totalDegree_le.trans (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj))
private def witness {M:Type} [Zero M] {s b d:ℕ} (z :M) (r :bzm s b d) :M :=
 if r.1=0 then (if r.2.2.val=b then z else 0) else (if r.2.2.val=0 then z else 0)
private theorem witness0 {M:Type} [CommSemiring M] (z :M) (s b d:ℕ) :
   topPoly (witness z :bzm s b d→M) 0=Polynomial.monomial b z := by
 ext j
 rw [coeff_topPoly,Polynomial.coeff_monomial]
 by_cases hj:j=b
 · subst j
   rw [dite_eq_left (show b<caps b s 0+1 from Nat.lt_succ_self b)]
   simp [witness,topSlot]
 · split_ifs <;> simp_all [witness,topSlot,Ne.symm hj]
private theorem witness1 {M:Type} [CommSemiring M] (z :M) (s b d:ℕ) :
   topPoly (witness z :bzm s b d→M) 1=Polynomial.C z := by
 ext j
 rw [coeff_topPoly,Polynomial.coeff_C]
 have Kr : (1 :Fin 3)≠0:= by decide
 by_cases hj:j=0
 · subst j
   rw [dite_eq_left (Nat.lt_succ_of_le (Nat.zero_le _))]
   simp [witness,topSlot,Kr]
 · split_ifs <;> simp_all [witness,topSlot]
private theorem topRes_witness {M:Type} [CommRing M] (m:L →+* M) (z :M) (s b d:ℕ) :
  (topRes :Coeff s b d).eval₂ m (witness z)=z^(b+(b+s+1)) := by
 rw [topRes_eval,witness0,witness1,Polynomial.resultant_C_right,Polynomial.coeff_monomial,
  ite_eq_left rfl,mul_comm,← pow_add]
theorem topRes_ne (s b d:ℕ) : (topRes :Coeff s b d)≠0:= by
 intro h
 have H :=topRes_witness (RingHom.id L) 1 s b d
 simp [h] at H
theorem topRes_degree (s b d:ℕ) :2*b+s+1≤(topRes :Coeff s b d).totalDegree := by
  let z :MvPolynomial Unit L:=MvPolynomial.X ()
  have h:=cYh (topRes :Coeff s b d) (witness z) (by
    intro i
    unfold witness
    split_ifs <;> first | exact MvPolynomial.isHomogeneous_X _ _
                        | exact MvPolynomial.isHomogeneous_zero _ _ _)
  rw [topRes_witness] at h
  have hz :z^(b+(b+s+1))≠0:=pow_ne_zero _ (MvPolynomial.X_ne_zero _)
  rw [((MvPolynomial.isHomogeneous_X L ()).pow _).totalDegree hz,one_mul] at h
  omega
end
end qEAs6me
