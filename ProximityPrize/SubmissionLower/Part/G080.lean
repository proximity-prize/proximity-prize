import ProximityPrize.SubmissionLower.Part.G079


section Compact_SecondJetRelaxedDifferentiation
/-! Degree-sensitive S budgets preserve the required derivative vanishings.
This module is conditional on the source support and contact hypotheses; it
makes no claim that the new interpolation source has positive nullity. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedDifferentiation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetGlobalDifferentiation SecondJetSpecialize
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K]

/-- Low S coefficients reserve their own derivative order. Higher coefficients
reserve the common requested order. The cutoff is strictly above that order. -/
def reserve (k n0 h : ℕ) : ℕ := if h < n0 then h else k

theorem reserve_ge_order (k n0 h d : ℕ) (hdk : d ≤ k) (hdh : d ≤ h) :
    d ≤ reserve k n0 h := by
  unfold reserve
  split <;> assumption

theorem derivative_weight (P : Poly (K := K)) (m a w k n0 d : ℕ)
    (hwa : w-2 ≤ a) (hdm : d ≤ m) (hdk : d ≤ k)
    (hP : ∀ e ∈ P.support,
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+
        reserve k n0 (e 1)*(a-(w-2)) < m*a)
    (e : Fin 5 →₀ ℕ) (he : e ∈ ((pderiv 1)^[d] P).support) :
    e 0+w*e 2+(w-1)*e 3+(w-2)*e 1 < (m-d)*a := by
  have hh := hP _ (support_iterate P d e he)
  simp [Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff] at hh
  have hr := reserve_ge_order k n0 (e 1+d) d hdk (by omega)
  have hp := Nat.mul_le_mul_right (a-(w-2)) hr
  have ha : a-(w-2)+(w-2) = a := Nat.sub_add_cancel hwa
  have hm : (m-d)*a+d*a = m*a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hdm]
  nlinarith

/-- Every requested derivative vanishes after codeword specialization whenever
its contact and degree-sensitive support bounds are supplied. -/
theorem derivative_vanish (P : Poly (K := K)) (m a w k n0 d : ℕ)
    (ha : 0 < a) (hwa : w-2 ≤ a) (hdm : d < m) (hdk : d ≤ k)
    (hP : ∀ e ∈ P.support,
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+
        reserve k n0 (e 1)*(a-(w-2)) < m*a)
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hcontact : ∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (f : Polynomial K) (hf : f.natDegree ≤ w) (z : K) (S : Finset N)
    (hS : a ≤ S.card) (hvalues : ∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) :
    specialize f z ((pderiv 1)^[d] P) = 0 := by
  refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
  · intro i _
    apply local_derivative_contact (nodes i) (u0 i) (u1 i) P (m-d) d
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hcontact i
  · have hd := specialization_degree ((pderiv 1)^[d] P) f z w ((m-d)*a) hf (Nat.mul_pos (Nat.sub_pos_of_lt hdm) ha)
      (derivative_weight P m a w k n0 d hwa (Nat.le_of_lt hdm) hdk hP)
    exact hd.trans_le (Nat.mul_le_mul_left (m-d) hS)

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedDifferentiation

end Compact_SecondJetRelaxedDifferentiation
