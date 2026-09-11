import ProximityPrize.SubmissionLower.PartG074


section Compact_SecondJetRelaxedGlobalSupport
/-! Localization preserves the degree-sensitive clipped second-jet source. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalSupport
open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetBasis SecondJetGlobalSupport
open SecondJetWeightedSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem linear_C (w : Fin 5 → ℤ) (c : K) : LinearBound w 0 (MvPolynomial.C c) := by
  intro e he
  have he0 : e = 0 := Finset.mem_singleton.mp (MvPolynomial.support_C_subset he)
  subst e
  simp [weight]

theorem localize_X_bound (w : Fin 5 → ℤ) (hw0 : w 0 = 0) (hw4 : w 4 = 0)
    (hw2 : 0 ≤ w 2) (x u0 u1 : K) (j : Fin 5) :
    LinearBound w (w j) (localize x u0 u1 (MvPolynomial.X j)) := by
  have hE := linear_X (K := K) w 0
  have hZ := linear_X (K := K) w 4
  fin_cases j
  · simpa [localize, hw0] using (linear_C w x).add (hE.mono (by omega))
  · simpa [localize] using linear_X (K := K) w 1
  · have hU : LinearBound w (w 2)
        (MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4 : Poly (K := K)) :=
      ((linear_C w u0).mono hw2).add (((linear_C w u1).mul hZ).mono (by omega))
    have hA := linear_X (K := K) w 2
    simpa [localize] using hU.add ((hE.mul hA).mono (by omega))
  · simpa [localize] using linear_X (K := K) w 3
  · simpa [localize] using hZ

theorem localize_monomial_bound (w : Fin 5 → ℤ) (hw0 : w 0 = 0) (hw4 : w 4 = 0)
    (hw2 : 0 ≤ w 2) (x u0 u1 : K) (e : Fin 5 →₀ ℕ) (c : K) :
    LinearBound w (weight w e) (localize x u0 u1 (MvPolynomial.monomial e c)) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow, map_C]
    have h0 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 0).pow (e 0)
    have h1 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 1).pow (e 1)
    have h2 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 2).pow (e 2)
    have h3 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 3).pow (e 3)
    have h4 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 4).pow (e 4)
    simpa [weight, Fin.sum_univ_five, add_assoc] using
      (linear_C w c).mul (h0.mul (h1.mul (h2.mul (h3.mul h4))))
  · intro i
    simp

theorem localize_support (x u0 u1 : K) (e d : Fin 5 →₀ ℕ) (c : K)
    (hd : d ∈ (localize x u0 u1 (MvPolynomial.monomial e c)).support) :
    d 1 = e 1 ∧ 2*d 1+d 3 ≤ 2*e 1+e 3 ∧ d 1+d 2+d 3 ≤ e 1+e 2+e 3 := by
  have hs := localize_monomial_bound ![0,1,0,0,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hl := localize_monomial_bound ![0,-1,0,0,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hB := localize_monomial_bound ![0,2,0,1,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hM := localize_monomial_bound ![0,1,1,1,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  norm_num [weight, Fin.sum_univ_five, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four] at hs hl hB hM
  omega

/-- The global weighted cutoff induces the local middle-degree cap used by
all three numerical profiles. -/
theorem middle_cap (e : Fin 5 →₀ ℕ) (w B D : ℕ) (hw : 2 ≤ w)
    (hB : 2*e 1+e 3 ≤ B)
    (hD : e 0+w*e 2+(w-1)*e 3+(w-2)*e 1 < D) :
    e 1+e 2+e 3 ≤ (D+B-1)/w := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < w)).mpr
  have h1 : w-1+1=w := by omega
  have h2 : w-2+2=w := by omega
  have hh : (e 1+e 2+e 3)*w < D+B := by nlinarith
  omega

theorem truncated_local_monomial_mem (x u0 u1 : K) (m L B s U w : ℕ)
    (D : ℕ → ℕ) (hw : 2 ≤ w) (e : Fin 5 →₀ ℕ) (c : K)
    (hB : 2*e 1+e 3 ≤ B) (hs : e 1 ≤ s)
    (hU : e 1+e 2+e 3 ≤ U) (hL : e 1+e 2+e 3+e 4 ≤ L)
    (hD : e 0+w*e 2+(w-1)*e 3+(w-2)*e 1 < D (e 1)) :
    truncateOuter (K := K) m (flatEquiv (K := K)
      (localize x u0 u1 (MvPolynomial.monomial e c))) ∈
        SecondJetRelaxedSpace.source (K := K) m L B s U (fun h => (D h+B-1)/w) := by
  rw [← flatEquiv_truncFlat, SecondJetRelaxedSpace.mem_source_iff]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  obtain ⟨hm,hd'⟩ := support_truncFlat m _ d hd
  have hb := localize_monomial x u0 u1 e c d hd'
  obtain ⟨hS,hRS,hM⟩ := localize_support x u0 u1 e d c hd'
  have hcap := middle_cap e w B (D (e 1)) hw hB hD
  refine ⟨⟨hm,hb.1,by omega,by omega,hb.2.2.2.trans hL⟩,hRS.trans hB,hM.trans hU,?_⟩
  simpa only [hS] using hM.trans hcap

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalSupport

end Compact_SecondJetRelaxedGlobalSupport
