import ProximityPrize.SubmissionLower.PrimaryTaperColumns

set_option Elab.async false

namespace PrimaryTaperActive

open K1_13 (Row)
open K1_13_2_2 (gradeWeight)
open MvPolynomial
open TaperColumns (jetExponents)
open TaperBudget (cap)

def Fits (P : Row 4) (n : ℕ) : Prop :=
  ∀ m ∈ P.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ n

theorem of_jets {P : Row 4} (h : ∀ m ∈ P.support, m ∈ jetExponents) :
    Fits P 5163 := by
  intro m hm
  have hz := h m hm
  let q := m.weight gradeWeight
  change q ≤ 4012 ∧ m.weight K1_13_2_2.oldWeight ≤ 1650 ∧ m 1 + m 2 + m 3 ≤ cap q at hz
  have hq : q = m 0 + m 1 + m 2 + m 3 := by
    simp [q, Finsupp.weight_eq_sum, Fin.sum_univ_four, gradeWeight, smul_eq_mul]
  obtain ⟨hqmax, _, hd⟩ := hz
  unfold cap at hd
  split at hd <;> omega

private def weight : Fin 4 → ℕ := ![1,2,2,2]

private theorem weight_at (m : Fin 4 →₀ ℕ) :
    m.weight weight = m 0 + 2*m 1 + 2*m 2 + 2*m 3 := by
  simp [weight, Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, Nat.mul_comm]

theorem fits_iff (P : Row 4) (n : ℕ) : Fits P n ↔ weightedTotalDegree weight P ≤ n := by
  unfold Fits weightedTotalDegree
  rw [Finset.sup_le_iff]
  simp only [weight_at]

theorem of_dvd {P Q : Row 4} {n : ℕ} (hQ : Q ≠ 0) (hdiv : P ∣ Q) (h : Fits Q n) :
    Fits P n :=
  (fits_iff P n).mpr ((weightedTotalDegree_le_of_dvd weight hdiv hQ).trans ((fits_iff Q n).mp h))

#print axioms of_jets
#print axioms of_dvd
end PrimaryTaperActive
