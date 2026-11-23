import ProximityPrize.SubmissionLower.AF
set_option Elab.async false
set_option autoImplicit true
section
namespace Sr.Weight
open MvPolynomial Polynomial aR Ex dN lB
local notation "W" => MvPolynomial.weightedTotalDegree
theorem aAA (w:Fin 4→ℕ) (P:af 4) :
  W w (separant P)≤W w P - w 3 :=
 weightedTotalDegree_pderiv_le_sub w 3 P
theorem arU (w:Fin 4→ℕ) (i:Fin 4) (P:af 4)
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
theorem aQ9 (w:Fin 4→ℕ) (P:af 4) :
  W w (lX P)≤W w P:= by
 classical
 apply aJY
 intro m hm
 obtain ⟨j,hj,hmj⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
 have h:j=m:= by
  by_contra hne
  exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial,ite_eq_right hne])
 exact h ▸ hj
theorem aa5 (w:Fin 4→ℕ) (Δ:ℕ)
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
theorem al0 (w:Fin 4→ℕ) (Δ:ℕ)
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
theorem step_bound (w:Fin 4→ℕ) (Δ:ℕ)
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
theorem avh (w:Fin 4→ℕ) (Δ:ℕ)
   (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) {g:af 4} {B:ℕ}
   (hB:w 3≤B) (hg:W w g≤B) (n:ℕ) :
   W w (su g n)≤w 0+n*(2*(B - w 3)+Δ) := by
 induction n with
 | zero=>simpa only [su,zero_mul,add_zero] using abx (R:=ao[X]) w 0
 | succ n ih =>
   simpa only [su,Nat.add_mul,one_mul,Nat.add_assoc] using
     step_bound w Δ hshift hB hg ih (2*n)
end Sr.Weight
end
section
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
namespace dnO
noncomputable section
open Polynomial P1
open ProximityPrize.Benchmark
open scoped BigOperators
variable {u:e9} {deleted:Finset I}
private theorem b0b {q:ℕ} (hq:2≤q) {σ:K →+* K}
   {P:K[X]} (hdiv :P^q∣P.map σ) :P.natDegree=0:= by
 by_cases hP:P=0
 · simp [hP]
 have h:=natDegree_le_of_dvd hdiv (Polynomial.map_ne_zero hP)
 rw [natDegree_pow,natDegree_map_eq_of_injective σ.injective] at h
 have htwo:=(Nat.mul_le_mul_right P.natDegree hq).trans h
 omega
private theorem same_label {a b γ δ:K} (hpair :a≠0∨b≠0)
  (hγ:a+γ*b=0) (hδ:a+δ*b=0) :γ=δ:= by
 have hb:b≠0:= by
  intro hz
  exact hpair.elim (fun ha=>ha (by simpa [hz] using hγ)) (fun hb=>hb hz)
 apply sub_eq_zero.mp
 refine (mul_eq_zero.mp (show (γ-δ)*b=0 from ?_)).resolve_right hb
 linear_combination hγ - hδ
end
end dnO
end
