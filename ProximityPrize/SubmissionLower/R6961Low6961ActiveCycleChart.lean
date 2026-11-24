import ProximityPrize.SubmissionLower.R6961Low6961ActiveCycleCaps
import ProximityPrize.SubmissionLower.R6961Low6961GeometryCut

set_option autoImplicit false
set_option Elab.async false

namespace Low6961ActiveCycle

noncomputable section

open Polynomial
open P3 (K)
open Low6961Prices (physicalDegree taylorLength)
open K1_13 (Row shape extend InBox Shape)
open Low48BentCycle (Family rawFamily)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5 actualPoint)
open K1_13_6_2_2 (generic5 rawGraph numerator denominator padded padded_last)
open Low6961GeometryCut_2 (Branch branch_box)
open MvPolynomial
open Low6961GeometryCut_2_1 (valuePolynomial value_section numerator_associated)

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

def Chart {f Q : Row 4} {l : ℕ} (R : Family) (b : Branch f Q l) : Prop :=
    Section R 2 b.graph ∧ ∃ E H : GeoJets5,
      Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member) ∧
      Section R 4 H ∧ Associated (b.onGraph H) (b.localMap b.next) ∧
      ∀ x a : K, ∃ D, Section R 4 D ∧
        ∀ S : (Polynomial K), S.natDegree ≤ physicalDegree → ∀ h : b.Contains (actualPoint (extend S)),
          (b.liftedEval (actualPoint (extend S)) h D = 0 ↔ S.eval x = a)

private theorem recover {f Q : Row 4} {l : ℕ} {R : Family} (b : Branch f Q l)
    (hG : Section R 2 (generic5 (rawGraph b.g)))
    (hmem : Section R 3 (generic5 (padded b.g (taylorLength - 4) taylorLength)))
    (hden : Section R 4 (generic5 (denominator b.g (taylorLength - 3))))
    (hpad : ∀ i ≤ taylorLength + 1,
      Section R 4 (generic5 (padded b.g (taylorLength - 3) i))) : Chart R b := by
  have hGraph : generic5 (rawGraph b.g) = b.graph := by
    simp [rawGraph, Branch.graph, Branch.sigma, toGeneric, MvPolynomial.map_rename, map_ofNat]
  let k := taylorLength - 4
  have hk : k + 4 = taylorLength := by decide
  have hk' : (k + 1) + 4 = taylorLength + 1 := by decide
  have hE : Section R 3 (generic5 (padded b.g k (k + 4))) := by
    rw [hk]
    exact hmem
  have hH : Section R 4 (generic5 (padded b.g (k + 1) ((k + 1) + 4))) :=
    hpad _ (by omega)
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
      exact scalar_section (R := R) (i := 4) (hpad i (by omega)) _
    · exact scalar_section (R := R) (i := 4) hden _
  · intro T hT h
    exact value_section hM b (k + 1) hlen x a T (Nat.lt_succ_of_le hT) h

theorem ordinary_chart {f Q : Row 4} {l : ℕ} (ht : 1 ≤ (shape f).t) (b : Branch f Q l) :
    Chart (rawFamily (caps (shape f).chamber)) b := by
  obtain ⟨hg, hbox⟩ := Low48BentSupport.chart_support (K1_13_7_1.shape_chamber f) ht (branch_box b)
  exact recover b hg ((hbox _).2 _ (by decide)) (hbox _).1
    (fun i hi => (hbox _).2 i hi)

theorem active_chart {f Q : Row 4} {l K : ℕ}
    (hK : Low6961Prices.ActiveFits f K) (ha : Low6961Prices.activeFitsPrice (shape f) K)
    (b : Branch f Q l) : Chart (activeRaw (shape f).chamber K) b := by
  let p := (shape f).chamber
  have ht : 1 ≤ p.t := by have H : 3 ≤ p.t := ha.1; omega
  have hc : 4 ≤ baseClip p K := ha.2.1
  obtain ⟨hK', hb, _, _, _⟩ := clip_bounds p 0 (p.b + p.j - K)
  have hKb : K ≤ p.b + p.j - baseClip p K := by
    change baseClip p K ≤ p.b + p.j - K at hK'
    omega
  have hFits : Low49ActiveSupport.Fits b.g (p.b + p.j - baseClip p K) := by
    have hsep := Low49ActiveSupport.separant_fits hK b.r
    exact fun m hm => (hsep m hm).trans hKb
  have hg : graphClip p K ≤ baseClip p K := (clip_bounds _ _ _).1
  obtain ⟨hG, hbox⟩ := Low49ActiveSupport.chart_support (K1_13_7_1.shape_chamber f) ht
    (branch_box b) (show 2 ≤ baseClip p K by omega) hFits hb hg
  have hchart (k : ℕ) := hbox k (liftClip p K k) (clip_bounds _ _ _).1
  exact recover b hG ((hchart (taylorLength - 4)).2 taylorLength (by decide))
    (hchart (taylorLength - 3)).1
    (fun i hi => (hchart (taylorLength - 3)).2 i hi)

end

end Low6961ActiveCycle
