import ProximityPrize.SubmissionLower.Final50BentCycleCap
import ProximityPrize.SubmissionLower.Final50GeometryCut

set_option autoImplicit false
set_option Elab.async false

namespace Final50BentCycle

noncomputable section

open Low48BentCycle

open Polynomial
open P3 (K)
open Final50Price (physicalDegree taylorLength)
open K1_13 (Row shape extend)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5 actualPoint)
open K1_13_6_2_2 (generic5 rawGraph numerator denominator padded padded_last)
open Final50GeometryCut_2 (Branch branch_box)
open MvPolynomial
open private valuePolynomial value_section numerator_associated
  from ProximityPrize.SubmissionLower.Final50GeometryCut

private theorem scalar_section {R : Family} {i : Fin 5} {D : GeoJets5}
    (h : Section R i D) (c : GeoField) : Section R i (MvPolynomial.C c * D) := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
  exact h m (MvPolynomial.mem_support_iff.mpr fun hz => hm (mul_eq_zero_of_right _ hz))

private theorem sum_section {R : Family} {i : Fin 5} {ι : Type*} (S : Finset ι)
    (D : ι → GeoJets5) (h : ∀ j ∈ S, Section R i (D j)) :
    Section R i (∑ j ∈ S, D j) := by
  classical
  intro m hm
  obtain ⟨j, hj, hjm⟩ := Finset.mem_biUnion.mp (support_sum hm)
  exact h j hj m hjm

private theorem sub_section {R : Family} {i : Fin 5} {D E : GeoJets5}
    (hD : Section R i D) (hE : Section R i E) : Section R i (D - E) := by
  intro m hm
  exact (Finset.mem_union.mp (MvPolynomial.support_sub (Fin 5) D E hm)).elim (hD m) (hE m)

theorem chart {f Q : Row 4} {l : ℕ} (ht : 1 ≤ (shape f).t) (b : Branch f Q l) :
    let R := rawFamily (caps (shape f).chamber)
    Section R 2 b.graph ∧ ∃ E H : GeoJets5,
      Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member) ∧
      Section R 4 H ∧ Associated (b.onGraph H) (b.localMap b.next) ∧
      ∀ x a : K, ∃ D, Section R 4 D ∧
        ∀ S : K[X], S.natDegree ≤ physicalDegree → ∀ h : b.Contains (actualPoint (extend S)),
          (b.liftedEval (actualPoint (extend S)) h D = 0 ↔ S.eval x = a) := by
  let R := rawFamily (caps (shape f).chamber)
  obtain ⟨hG, hbox⟩ := Low48BentSupport.chart_support (K1_13_7_1.shape_chamber f) ht (branch_box b)
  have hGraph : generic5 (rawGraph b.g) = b.graph := by
    simp [rawGraph, Branch.graph, Branch.sigma, toGeneric, MvPolynomial.map_rename, map_ofNat]
  let k := taylorLength - 4
  have hk : k + 4 = taylorLength := by decide
  have hk' : (k + 1) + 4 = taylorLength + 1 := by decide
  have hE := (hbox k).2 (k + 4) le_rfl
  have hH := (hbox (k + 1)).2 ((k + 1) + 4) le_rfl
  rw [padded_last] at hE hH
  have hm := numerator_associated b k
  have hn := numerator_associated b (k + 1)
  rw [hk] at hm
  rw [hk'] at hn
  refine ⟨hGraph ▸ hG, generic5 (numerator b.g k), generic5 (numerator b.g (k + 1)),
    hE, hm, hH, hn, ?_⟩
  intro x a
  have hM : taylorLength ≤ K1.p := by decide
  have hlen : taylorLength ≤ (k + 1) + 5 := by decide
  refine ⟨valuePolynomial taylorLength b.g (k + 1) x a, ?_, ?_⟩
  · unfold valuePolynomial
    apply sub_section
    · apply sum_section
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hki : i ≤ (k + 1) + 4 := by omega
      exact scalar_section (R := R) (i := 4) ((hbox (k + 1)).2 i hki) _
    · exact scalar_section (R := R) (i := 4) (hbox (k + 1)).1 _
  · intro T hT h
    exact value_section hM b (k + 1) hlen x a T (Nat.lt_succ_of_le hT) h

end

end Final50BentCycle
