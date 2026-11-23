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





#print axioms of_jets
end PrimaryTaperActive
