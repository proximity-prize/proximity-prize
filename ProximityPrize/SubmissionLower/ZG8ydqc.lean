import ProximityPrize.SubmissionLower.ZceTCvc
set_option Elab.async false
set_option autoImplicit true
namespace atb
noncomputable section
open Polynomial MvPolynomial aR Ex dN wH lB
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private def br5 (f :af 4) (n:ℕ) (P:af 4) :af 4 :=
  u6 f P-(n:af 4)*pK (separant f)*P
private def azv (f :af 4) :ℕ→af 4
  | 0=>MvPolynomial.X 0
  | n+1=>br5 f n (azv f n)
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
private theorem gpA {f :af 4} (hf : (shape f).t=1) :
    separant (separant f)=0:= by
  let w:Fin 4→ℕ:=Pi.single 3 1
  have h:=weightedTotalDegree_pderiv_le_sub w 3 f
  have h₁:W w f=1 := by simpa only [w,weightedTotalDegree_piSingle,shape] using hf
  have h₂:w 3=1 := by decide
  rw [h₁,h₂] at h
  exact arU w 3 _ (h.trans_lt (by decide))
private theorem eGF (n:ℕ) (U V:ao[X]) :
    U*derivative (U^n*V)-(n:ao[X])*derivative U*(U^n*V) =
      U^(n+1)*derivative V:= by
  cases n with
  | zero=>simp
  | succ n =>
    rw [derivative_mul,derivative_pow,Nat.succ_sub_one,
      pow_succ U n,pow_succ U (n+1)]
    simp only [C_eq_natCast,pow_succ U n]
    ring
private theorem cM3 {f :af 4} (hf : (shape f).t=1) (S:ao[X])
    (hon :cK f S=0) (hr :qg f S) (n:ℕ) :
    cK (azv f n) S=cK (separant f) S^n*(derivative^[n]) S:= by
  have hnz :cK (separant f) S≠0:=hr
  have hflow:=aNw f (separant f) S hon
  have hsep:cK (pK (separant f)) S=derivative (cK (separant f) S) := by
    simp only [u6,gpA hf,cK,map_mul,mul_zero,
      sub_zero] at hflow
    exact mul_left_cancel₀ hnz hflow
  induction n with
  | zero=>simp [azv,cK,jet]
  | succ n ih =>
    let e :=MvPolynomial.eval (jet S:Fin 4→ao[X])
    change e (br5 f n (azv f n))= _
    unfold br5
    rw [map_sub,map_mul,map_mul,map_natCast]
    change cK (u6 f (azv f n)) S -
      (n:ao[X])*cK (pK (separant f)) S*cK (azv f n) S= _
    rw [aNw _ _ _ hon,hsep,ih,eGF,
      Function.iterate_succ_apply']
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
private theorem Ur (w:Fin 4→ℕ) {f :af 4} {B:ℕ} (hf :W w f≤B) :
    W w (separant f)≤B - w 3 :=
  (weightedTotalDegree_pderiv_le_sub w 3 f).trans (Nat.sub_le_sub_right hf _)
private theorem ew1 (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {f P:af 4} {B d:ℕ} (hB:w 3≤B) (hf :W w f≤B) (hP:W w P≤d) (n:ℕ) :
    W w (br5 f n P)≤d+(B - w 3+Δ) := by
  have hsep:=Ur w hf
  unfold br5 u6
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply Submodule.sub_mem
    · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add hsep (aa5 w Δ hshift P hP)).trans (by omega))
    · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      by_cases h:w 3≤d
      · exact (weightedTotalDegree_mul_le _ _ _).trans
          ((Nat.add_le_add (aa5 w Δ hshift f hf) (Ur w hP)).trans (by omega))
      · rw [separant,arU w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
          mul_zero,weightedTotalDegree_zero]
        exact Nat.zero_le _
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc,← map_natCast (MvPolynomial.C:ao[X] →+* af 4)]
    exact (Po w _ _).trans
      ((weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (aa5 w Δ hshift (separant f) hsep) hP).trans (by omega)))
private theorem cYg (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) {f :af 4} {B:ℕ}
    (hB:w 3≤B) (hf :W w f≤B) (n:ℕ) :
    W w (azv f n)≤w 0+n*(B - w 3+Δ) := by
  induction n with
  | zero=>simpa only [azv,zero_mul,add_zero] using abx (R:=ao[X]) w 0
  | succ n ih =>
    simpa only [azv,Nat.add_mul,one_mul,Nat.add_assoc] using
      ew1 w Δ hshift hB hf ih n
private def denominator (L:ℕ) (f :af 4) :af 4 :=separant f^L
private def numerator (L:ℕ) (f :af 4) (i:AK) :af 4 :=
  if hi:i.val<4 then MvPolynomial.X ⟨i.val,hi⟩*denominator L f
  else
    MvPolynomial.C (Polynomial.C (↑i.val.factorial:ao)⁻¹) *
      (separant f^(L - i.val)*azv f i.val)
private theorem ajW (S:ao[X]) (n:ℕ) :
    derivative^[n] S=Polynomial.C (n.factorial:ao)*hasseDeriv n S:= by
  ext m
  rw [coeff_iterate_derivative,Polynomial.coeff_C_mul,hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul,Nat.cast_mul,mul_assoc]
end
end atb
