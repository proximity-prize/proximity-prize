import ProximityPrize.SubmissionLower.BI
set_option Elab.async false
set_option autoImplicit true
namespace aY3
noncomputable section
open Polynomial MvPolynomial aR Ex dN vS lB
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem aAA (w:Fin 4→ℕ) (P:af 4) :
    W w (separant P)≤W w P - w 3 :=
  weightedTotalDegree_pderiv_le_sub w 3 P
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
  have hsep:=(aAA w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (aa5 w Δ hshift P hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    by_cases h:w 3≤d
    · have hp:=(aAA w P).trans (Nat.sub_le_sub_right hP (w 3))
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (aa5 w Δ hshift g hg) hp).trans (by omega))
    · rw [separant,arU w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
        mul_zero,weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem step_bound (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {g P:af 4} {B d:ℕ} (hB:w 3≤B) (hg:W w g≤B) (hP:W w P≤d) (a :ℕ) :
    W w (aqZ g a P)≤d+(2*(B - w 3)+Δ) := by
  have hsep:=(aAA w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (al0 w Δ hshift hB hg hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    apply (weightedTotalDegree_mul_le _ _ _).trans
    rw [← map_natCast (MvPolynomial.C:ao[X] →+* af 4)]
    exact (Nat.add_le_add ((Po _ _ _).trans (al0 w Δ hshift hB hg hsep))
      hP).trans (by omega)
private theorem aDr (w:Fin 4→ℕ) (f :af 4) (r :ℕ) :
    W w ((separant^[r]) f)≤W w f := by
  induction r with
  | zero=>exact le_rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (weightedTotalDegree_pderiv_le w 3 _).trans ih
end
end aY3
