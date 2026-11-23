import ProximityPrize.SubmissionLower.L
set_option Elab.async false
set_option autoImplicit true
namespace bat
noncomputable section
open Polynomial MvPolynomial aR Ex dN wH lB
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem arU (w:Fin 4→ℕ) (i:Fin 4) (P:af 4)
    (h:W w P<w i) :pderiv i P=0:= by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz :P.coeff (m+Finsupp.single i 1)=0:= by
    by_contra hn
    have hm:=le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add,Finsupp.weight_single,one_smul] at hm
    omega
  simp [hz]
private theorem aQ9 (w:Fin 4→ℕ) (P:af 4) :
    W w (lX P)≤W w P:= by
  classical
  apply aJY
  intro m hm
  obtain ⟨j,hj,hmj⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h:j=m:= by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial,ite_eq_right hne])
  exact h ▸ hj
private theorem aa5 (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    (P:af 4) {d:ℕ} (hP:W w P≤d) :W w (pK P)≤d+Δ:= by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((aQ9 w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (Po w _ _).trans
    by_cases h:w i.castSucc≤d
    · have hp:=(weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he :=hshift i
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (abx w _) hp).trans (by omega))
    · rw [arU w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),mul_zero,
        weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem al0 (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {g P:af 4} {B d:ℕ} (hB:w 3≤B) (hg:W w g≤B) (hP:W w P≤d) :
    W w (u6 g P)≤d+(B - w 3)+Δ:= by
  have hsep:=(weightedTotalDegree_pderiv_le_sub w 3 g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (aa5 w Δ hshift P hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    by_cases h:w 3≤d
    · have hp:=(weightedTotalDegree_pderiv_le_sub w 3 P).trans (Nat.sub_le_sub_right hP (w 3))
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (aa5 w Δ hshift g hg) hp).trans (by omega))
    · rw [separant,arU w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
        mul_zero,weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem dlS (w:Fin 4→ℕ) (a :ℕ) (P:af 4) :
    W w ((a :af 4)*P)≤W w P:= by
  rw [← map_natCast (MvPolynomial.C:ao[X] →+* af 4)]
  exact Po w _ _
private theorem step_bound (linear :Bool) (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {g P:af 4} {B d:ℕ} (hB:w 3≤B) (hg:W w g≤B) (hP:W w P≤d) (a :ℕ) :
    W w (step linear g a P)≤d+(Fy linear*(B - w 3)+Δ) := by
  have hsep:W w (separant g)≤B - w 3 :=
    (weightedTotalDegree_pderiv_le_sub w 3 g).trans (Nat.sub_le_sub_right hg (w 3))
  cases linear
  · simp only [step,Bool.false_eq_true,↓reduceIte,Fy,aqZ]
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sub_mem <;> apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    · exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add hsep (al0 w Δ hshift hB hg hP)).trans (by omega))
    · exact (weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add
        ((dlS _ _ _).trans (al0 w Δ hshift hB hg hsep)) hP |>.trans (by omega))
  · simp only [step,Fy,↓reduceIte,one_mul]
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sub_mem <;> apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    · exact (al0 w Δ hshift hB hg hP).trans (by omega)
    · exact (weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add
        ((dlS _ _ _).trans (aa5 w Δ hshift _ hsep)) hP |>.trans (by omega))
private theorem ceI (linear :Bool) (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) {g:af 4} {B:ℕ}
    (hB:w 3≤B) (hg:W w g≤B) (n:ℕ) :
    W w (raw linear g n)≤w 0+n*(Fy linear*(B - w 3)+Δ) := by
  induction n with
  | zero=>simpa only [raw,zero_mul,add_zero] using abx (R:=ao[X]) w 0
  | succ n ih =>
    simpa only [raw,Nat.add_mul,one_mul,Nat.add_assoc] using
      step_bound linear w Δ hshift hB hg ih (Fy linear*n)
private theorem cpc (g:af 4) (w:Fin 4→ℕ) (a :ℕ) {B:ℕ} (hg:W w g≤B) :
    W w (separant g^a)≤a*(B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _
    ((weightedTotalDegree_pderiv_le_sub w 3 g).trans (Nat.sub_le_sub_right hg _)))
end
end bat
