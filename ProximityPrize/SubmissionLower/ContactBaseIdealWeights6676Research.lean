import ProximityPrize.SubmissionLower.ContactBaseIdealCoefficients6676Research
import ProximityPrize.SubmissionLower.ContactPost6464MinkowskiRecurrenceResearch
namespace ProximityPrize.SubmissionLower.ContactBaseIdealWeights6676Research
open ContactTaylorNumerators ContactBaseIdealAlgebra6676Research
open ContactBaseIdealCoefficients6676Research ContactPost6464MinkowskiRecurrenceResearch
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
private theorem pderiv_eq_zero_of_wt_lt (weights:Fin 4 → ℕ) (P:Poly K) (i:Fin 4)
    (hP:wt weights P < weights i):MvPolynomial.pderiv i P=0:=by
  apply MvPolynomial.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hh:=MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i P d hd)
  simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
  change Finsupp.weight weights d+weights i ≤ wt weights P at hh
  omega
def WeightBound (w:Fin 4 → ℕ) (P:Poly K) (c:ℤ):Prop:=
  P=0∨(wt w P:ℤ) ≤ c
namespace WeightBound
variable {w:Fin 4 → ℕ} {P Q:Poly K} {a b:ℤ}
theorem mono (h:WeightBound w P a) (hab:a ≤ b):WeightBound w P b:=
  h.imp_right (fun hp => hp.trans hab)
theorem add (hP:WeightBound w P a) (hQ:WeightBound w Q a):
    WeightBound w (P+Q) a:=by
  rcases hP with rfl | hp
  · simpa only [zero_add] using hQ
  rcases hQ with rfl | hq
  · rw [add_zero]
    exact Or.inr hp
  right
  have h:(wt w (P+Q):ℤ) ≤ max (wt w P:ℤ) (wt w Q:ℤ):=by
    exact_mod_cast wt_add_le w P Q
  exact h.trans (max_le hp hq)
theorem neg (hP:WeightBound w P a):WeightBound w (-P) a:=by
  rcases hP with rfl | hp
  · exact Or.inl neg_zero
  exact Or.inr (by simpa only [wt_neg] using hp)
theorem sub (hP:WeightBound w P a) (hQ:WeightBound w Q a):
    WeightBound w (P-Q) a:=by
  simpa only [sub_eq_add_neg] using hP.add hQ.neg
theorem mul (hP:WeightBound w P a) (hQ:WeightBound w Q b):
    WeightBound w (P*Q) (a+b):=by
  rcases hP with rfl | hp
  · exact Or.inl (zero_mul _)
  rcases hQ with rfl | hq
  · exact Or.inl (mul_zero _)
  right
  have h:(wt w (P*Q):ℤ) ≤ (wt w P:ℤ)+(wt w Q:ℤ):=by
    exact_mod_cast wt_mul_le w P Q
  linarith
theorem natCast (n:ℕ):WeightBound w (n:Poly K) 0:=
  Or.inr (by simp only [wt_natCast,Nat.cast_zero,le_refl])
theorem scale (n:ℕ) (hP:WeightBound w P a):WeightBound w ((n:Poly K)*P) a:=by
  simpa only [zero_add] using (natCast n).mul hP
theorem pderiv (hP:WeightBound w P a) (i:Fin 4):
    WeightBound w (MvPolynomial.pderiv i P) (a-w i):=by
  by_cases hz:MvPolynomial.pderiv i P=0
  · exact Or.inl hz
  rcases hP with rfl | hp
  · exact (hz (map_zero _)).elim
  right
  have hi:w i ≤ wt w P:=by
    by_contra hh
    exact hz (pderiv_eq_zero_of_wt_lt w P i (by omega))
  have hd:=wt_pderiv_le w P i (wt w P) le_rfl
  have hsum:wt w (MvPolynomial.pderiv i P)+w i ≤ wt w P:=by omega
  have hsum':(wt w (MvPolynomial.pderiv i P):ℤ)+w i ≤ wt w P:=by
    exact_mod_cast hsum
  linarith
theorem horizontal (hP:WeightBound w P a) (t:ℕ)
    (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1):
    WeightBound w (horizontalDerivation P) (a+1-t):=by
  have hx:=hP.pderiv (0:Fin 4)
  have hy:=hP.pderiv (1:Fin 4)
  have hr:WeightBound w (MvPolynomial.X (2:Fin 4):Poly K) 1:=
    Or.inr (by simp only [wt_X,hR,Nat.cast_one,le_refl])
  simp only [hX,Nat.cast_zero,sub_zero] at hx
  rw [hY] at hy
  have hxy:WeightBound w (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) P)
      (a+1-t):=by convert hr.mul hy using 1;ring
  have ht':(t:ℤ) ≤ 1:=by exact_mod_cast ht
  simpa only [horizontalDerivation,Derivation.add_apply,Derivation.smul_apply,
    smul_eq_mul] using (hx.mono (by linarith)).add hxy
end WeightBound
theorem contribution_bounds (w:Fin 4 → ℕ) (t:ℕ)
    (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1)
    (F P:Poly K) (C a:ℤ) (hF:WeightBound w F C) (hP:WeightBound w P a)
    (n j:ℕ):
    WeightBound w (sameContribution F n j P) (a+C-t)∧
    WeightBound w (downContribution F j P) (a+C+2-2*t)∧
    WeightBound w (upContribution F n j P) (a+C-2):=by
  have hH:WeightBound w (polyH K F) (C-1):=by
    simpa only [polyH,hR,Nat.cast_one] using hF.pderiv (2:Fin 4)
  have hG:WeightBound w (polyG K F) (C+1-t):=by
    simpa only [polyG,horizontalDerivation,Derivation.add_apply,
      Derivation.smul_apply,smul_eq_mul] using (hF.horizontal t hX hY hR ht).neg
  have hDH:=hH.horizontal t hX hY hR ht
  have hDG:=hG.horizontal t hX hY hR ht
  have hDP:=hP.horizontal t hX hY hR ht
  have hGR:=hG.pderiv (2:Fin 4)
  have hHR:=hH.pderiv (2:Fin 4)
  have hPR:=hP.pderiv (2:Fin 4)
  simp only [hR,Nat.cast_one] at hGR hHR hPR
  refine ⟨?_,?_,?_⟩
  · unfold sameContribution
    apply WeightBound.add
    · apply WeightBound.sub
      · convert hH.mul hDP using 1;ring
      · convert (hP.scale (n+j)).mul hDH using 1;ring
    · convert (hP.scale j).mul hGR using 1;ring
  · unfold downContribution
    convert (hP.scale j).mul hDG using 1;ring
  · unfold upContribution
    apply WeightBound.sub
    · convert hH.mul hPR using 1;ring
    · convert (hP.scale (n+j)).mul hHR using 1;ring
theorem baseCoefficients_weightBound (w:Fin 4 → ℕ) (t:ℕ)
    (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1)
    (F:Poly K) (C:ℤ) (hF:WeightBound w F C) (n j:ℕ):
    WeightBound w (baseCoefficients F n j)
      (2-t+n*(C-t)-j*(2-t)):=by
  induction n generalizing j with
  | zero =>
    by_cases hj:j=1
    · subst j
      simp only [baseCoefficients,↓reduceIte]
      convert WeightBound.natCast (w:=w) (K:=K) 1 using 1 <;> push_cast <;> ring
    · exact Or.inl (by simp [baseCoefficients,hj])
  | succ n ih =>
    rw [baseCoefficients,coefficientStep]
    apply WeightBound.add
    · apply WeightBound.add
      · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih j) n j).1 using 1
        push_cast
        ring
      · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j+1)) n (j+1)).2.1
          using 1
        push_cast
        ring
    · by_cases hj:j=0
      · rw [if_pos hj]
        exact Or.inl rfl
      · rw [if_neg hj]
        have hj1:1 ≤ j:=by omega
        convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j-1)) n (j-1)).2.2
          using 1
        simp only [Nat.cast_sub hj1,Nat.cast_one,Nat.cast_add]
        ring
theorem baseCoefficients_cumulative_wt_le (w:Fin 4 → ℕ)
    (hX:w 0=0) (hY:w 1=1) (hR:w 2=1)
    (F:Poly K) (C:ℕ) (hC:1 ≤ C) (hF:wt w F ≤ C) (n j:ℕ):
    wt w (baseCoefficients F n j) ≤ 1+n*(C-1)-j:=by
  have h:=baseCoefficients_weightBound w 1 hX hY hR le_rfl F C
    (Or.inr (by exact_mod_cast hF)) n j
  rcases h with hz | hb
  · simp [hz,wt,MvPolynomial.weightedTotalDegree]
  · have hi:(wt w (baseCoefficients F n j):ℤ)+j ≤ 1+n*((C-1:ℕ):ℤ):=by
      rw [Nat.cast_sub hC,Nat.cast_one]
      norm_num at hb ⊢
      linarith
    have hn:wt w (baseCoefficients F n j)+j ≤ 1+n*(C-1):=by exact_mod_cast hi
    omega
theorem baseCoefficients_R_wt_le (w:Fin 4 → ℕ)
    (hX:w 0=0) (hY:w 1=0) (hR:w 2=1)
    (F:Poly K) (s:ℕ) (hF:wt w F ≤ s) (n j:ℕ):
    wt w (baseCoefficients F n j) ≤ n*s+2-2*j:=by
  have h:=baseCoefficients_weightBound w 0 hX hY hR (by omega) F s
    (Or.inr (by exact_mod_cast hF)) n j
  rcases h with hz | hb
  · simp [hz,wt,MvPolynomial.weightedTotalDegree]
  · have hi:(wt w (baseCoefficients F n j):ℤ)+2*j ≤ n*s+2:=by
      norm_num at hb ⊢
      linarith
    have hn:wt w (baseCoefficients F n j)+2*j ≤ n*s+2:=by exact_mod_cast hi
    omega
private theorem wt_coordinate (P:Poly K) (i:Fin 4):
    wt (Pi.single i 1) P=P.degreeOf i:=by
  rw [wt,MvPolynomial.weightedTotalDegree,MvPolynomial.degreeOf_eq_sup]
  apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
  funext d
  exact Finsupp.weight_single_one_apply i d
theorem baseCoefficients_R_degree_le (F:Poly K) (s:ℕ)
    (hF:F.degreeOf (2:Fin 4) ≤ s) (n j:ℕ):
    (baseCoefficients F n j).degreeOf (2:Fin 4) ≤ n*s+2-2*j:=by
  simpa only [wt_coordinate] using baseCoefficients_R_wt_le (Pi.single (2:Fin 4) 1)
    (by simp) (by simp) (by simp) F s (by simpa only [wt_coordinate] using hF) n j
theorem baseCoefficients_support_bounds (F:Poly K) (s M L:ℕ)
    (hM:1 ≤ M) (hL:1 ≤ L) (hR:F.degreeOf (2:Fin 4) ≤ s)
    (hYR:wt ![0,1,1,0] F ≤ M) (hAll:wt ![0,1,1,1] F ≤ L) (n j:ℕ):
    (baseCoefficients F n j).degreeOf (2:Fin 4) ≤ n*s+2-2*j∧
    wt ![0,1,1,0] (baseCoefficients F n j) ≤ 1+n*(M-1)-j∧
    wt ![0,1,1,1] (baseCoefficients F n j) ≤ 1+n*(L-1)-j:=by
  exact ⟨baseCoefficients_R_degree_le F s hR n j,
    baseCoefficients_cumulative_wt_le _ rfl rfl rfl F M hM hYR n j,
    baseCoefficients_cumulative_wt_le _ rfl rfl rfl F L hL hAll n j⟩
end
end ProximityPrize.SubmissionLower.ContactBaseIdealWeights6676Research
