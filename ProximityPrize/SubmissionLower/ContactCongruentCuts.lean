import ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily

/-!
# Congruent representatives for regular cuts and finite zero budgets

Replacing a cut by a polynomial congruent modulo its surface leaves the
actual two-generated ideal unchanged. These lemmas transport the original
component family and its once-assigned costs; no components or affine
boundary points are removed.
-/

namespace ProximityPrize.SubmissionLower.ContactCongruentCuts

open scoped Classical BigOperators
open ContactCurveComponents ContactRegularComponentCover
open ContactFlagBezout
open ContactResidualSparseComponentAdapter
open ContactIdentityResidualZeroBudgetTransport
open ContactPrimeFlagBudgetFamily

noncomputable section

variable {K : Type} [Field K]

abbrev Poly3 := MvPolynomial (Fin 3) K

theorem mem_iff_of_sub_mem (P : Ideal (Poly3 (K := K)))
    {A B : Poly3 (K := K)} (h : A - B ∈ P) : A ∈ P ↔ B ∈ P := by
  constructor
  · intro hA
    simpa only [sub_sub_cancel] using P.sub_mem hA h
  · intro hB
    simpa only [sub_add_cancel] using P.add_mem h hB

theorem sub_mem_of_dvd (P : Ideal (Poly3 (K := K)))
    {G A B : Poly3 (K := K)} (hG : G ∈ P) (h : G ∣ A - B) :
    A - B ∈ P := by
  obtain ⟨Q, hQ⟩ := h
  rw [hQ]
  exact P.mul_mem_right Q hG

theorem cutIdeal_eq_of_dvd_sub {G T T' : Poly3 (K := K)}
    (h : G ∣ T - T') : cutIdeal K G T = cutIdeal K G T' := by
  have hG : G ∈ cutIdeal K G T := Ideal.subset_span (by simp)
  have hG' : G ∈ cutIdeal K G T' := Ideal.subset_span (by simp)
  have hT : T ∈ cutIdeal K G T := Ideal.subset_span (by simp)
  have hT' : T' ∈ cutIdeal K G T' := Ideal.subset_span (by simp)
  have hd := sub_mem_of_dvd (cutIdeal K G T) hG h
  have hd' := sub_mem_of_dvd (cutIdeal K G T') hG' h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact hG'
    · exact (mem_iff_of_sub_mem _ hd').mpr hT'
  · apply Ideal.span_le.mpr
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact hG
    · exact (mem_iff_of_sub_mem _ hd).mp hT

theorem regularComponents_eq_of_dvd_sub {G T T' H : Poly3 (K := K)}
    (h : G ∣ T - T') :
    regularComponents K G T H = regularComponents K G T' H := by
  classical
  ext P
  simp only [regularComponents, Finset.mem_filter, mem_componentFamily,
    cutIdeal_eq_of_dvd_sub h]

def regularComponentEquiv {G T T' H : Poly3 (K := K)}
    (h : G ∣ T - T') :
    RegularComponent K G T H ≃ RegularComponent K G T' H where
  toFun C := ⟨C.1, (regularComponents_eq_of_dvd_sub h) ▸ C.2⟩
  invFun C := ⟨C.1, (regularComponents_eq_of_dvd_sub h).symm ▸ C.2⟩
  left_inv C := by rfl
  right_inv C := by rfl

end
end ProximityPrize.SubmissionLower.ContactCongruentCuts
