import ProximityPrize.SubmissionLower.Fast040

set_option Elab.async false
namespace LeadingCoefficient82190
open K1_13 (Geom Row shape indexDegree)
open K1_13_1 (topView topView_degree anchorLead anchorLead_ne indexDegree_eq)
open MvPolynomial
open scoped Polynomial

/-- Taking the coefficient of the highest power of the last variable removes
that power from every weighted degree of its supporting monomials. -/
theorem term_weight (P : Row 4) (m : Fin 3 →₀ ℕ) (hm : m ∈ (anchorLead P).support) :
    ∃ u ∈ P.support, ∀ w : Fin 4 → ℕ,
      m.weight (fun i => w i.castSucc) + (shape P).t * w 3 = u.weight w := by
  classical
  let k := (topView P).natDegree
  let c := rename finSuccEquivLast P
  have hc : c.coeff (m.optionElim k) = (anchorLead P).coeff m :=
    (optionEquivLeft_coeff_coeff _ _ _ _).symm
  have hs : m.optionElim k ∈ c.support :=
    mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
  rw [show c = rename finSuccEquivLast P from rfl,
    support_rename_of_injective finSuccEquivLast.injective] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hs
  refine ⟨u, hu, fun w => ?_⟩
  let w' : Option (Fin 3) → ℕ := fun v => v.elim (w 3) (fun i => w i.castSucc)
  have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
  have hw : ∀ i : Fin 4, w' (finSuccEquivLast i) = w i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [w', hlast, show Fin.last 3 = (3 : Fin 4) by rfl]
    · simp [w']
  have hweight : (m.optionElim k).weight w' = u.weight w := by
    rw [← he]
    simp only [Finsupp.weight_apply, smul_eq_mul]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
    simp only [hw]
  rw [Finsupp.weight_optionElim] at hweight
  simpa only [w', Option.elim, k, topView_degree, smul_eq_mul, Nat.add_comm, Nat.mul_comm] using hweight

theorem lead_degree (P : Row 4) (hP : P ≠ 0) :
    (anchorLead P).totalDegree + (shape P).t ≤ P.totalDegree := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ ((support_nonempty.mpr (anchorLead_ne hP))) (fun m => m.weight (1 : Fin 3 → ℕ))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  have h := (hw (1 : Fin 4 → ℕ)).le.trans (le_weightedTotalDegree _ hu)
  rw [← weightedTotalDegree_one, weightedTotalDegree, he, ← weightedTotalDegree_one]
  have hconst : (fun i : Fin 3 => (1 : Fin 4 → ℕ) i.castSucc) = (1 : Fin 3 → ℕ) := rfl
  rw [hconst] at h
  simpa only [Pi.one_apply, Nat.mul_one] using h

theorem lead_index (P : Row 4) (hP : P ≠ 0) :
    indexDegree (anchorLead P) + 3 * (shape P).t ≤ indexDegree P := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr (anchorLead_ne hP)) (fun m => m.weight (fun i : Fin 3 => i.val))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  rw [indexDegree_eq, weightedTotalDegree, he, indexDegree_eq]
  simpa [Nat.mul_comm] using (hw (fun i => i.val)).le.trans (le_weightedTotalDegree _ hu)

/-- The remaining three-variable row uses a smaller degree box when the
highest derivative occurs at least nine times. -/
theorem large_top_box (P : Row 4) (hP : P ≠ 0) (hb : P.totalDegree ≤ 120)
    (hj : indexDegree P ≤ 48) (ht : 9 ≤ (shape P).t) :
    (anchorLead P).totalDegree ≤ 111 ∧ indexDegree (anchorLead P) ≤ 21 ∧
      (anchorLead P).degreeOf 2 ≤ 10 := by
  have hdegree := (lead_degree P hP).trans hb
  have hindex := (lead_index P hP).trans hj
  have hsmall : indexDegree (anchorLead P) ≤ 21 := by omega
  refine ⟨by omega, hsmall, ?_⟩
  rw [MvPolynomial.degreeOf_eq_sup]
  apply Finset.sup_le
  intro m hm
  have h := Finsupp.apply_smul_le_weight (fun i : Fin 3 => i.val) m (2 : Fin 3)
  have hm' := le_weightedTotalDegree (fun i : Fin 3 => i.val) hm
  rw [indexDegree_eq] at hsmall
  have htwo : m 2 * 2 ≤ 21 := by
    simpa only [smul_eq_mul, show (2 : Fin 3).val = 2 by rfl] using h.trans (hm'.trans hsmall)
  omega

#print axioms lead_degree
#print axioms lead_index
#print axioms large_top_box
end LeadingCoefficient82190
