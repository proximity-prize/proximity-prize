import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleCaps
import ProximityPrize.SubmissionLower.R6960Low6960GeometryCut
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice

-- merged module R6960Low6960ActiveCycleChart
section Merged_R6960Low6960ActiveCycleChart

set_option autoImplicit false
set_option Elab.async false

namespace Low6960ActiveCycle

noncomputable section

open Polynomial
open P3 (K)
open Low6960Prices (physicalDegree taylorLength)
open K1_13 (Row shape extend InBox Shape)
open Low48BentCycle (Family rawFamily)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5 actualPoint)
open K1_13_6_2_2 (generic5 rawGraph numerator denominator padded padded_last)
open Low6960GeometryCut_2 (Branch branch_box)
open MvPolynomial
open Low6960GeometryCut_2_1 (valuePolynomial value_section numerator_associated)

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
    (hK : Low6960Prices.ActiveFits f K) (ha : Low6960Prices.activeFitsPrice (shape f) K)
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

end Low6960ActiveCycle

end Merged_R6960Low6960ActiveCycleChart

-- merged module R6960Low6960SharedBentCaps
section Merged_R6960Low6960SharedBentCaps
set_option Elab.async false
namespace Low6960SharedBentCaps
noncomputable section

open K1_13 (Shape Row shape)
open K1_13_6 (GeoField)
open Low6960Prices (taylorLength)
open Low6960ActiveCycle (Doubled Chart)
open Low48BentLattice (Cap Allowed Chamber latticePoints)
open Low48BentSupport (graph lifted)
open Low48BentCycle (Family rawFamily capFamily capSum ambient_cap integral mixedDegree)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators
open Low48BentCycle (slots ambient_list)

def caps (p q : Shape) : Fin 5 → Cap :=
  ![(p, 0), (q, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]

theorem caps_chamber {p q : Shape} (hb : p.j ≤ p.b) (ht : 1 ≤ p.t) (hj : 3 * p.t + 3 ≤ p.j) (hq : Chamber (q,0)) :
    ∀ i, Chamber (caps p q i) := by
  intro i
  fin_cases i
  · change Chamber (p, 0)
    exact ⟨hb, show 3 * p.t ≤ p.j by omega, Nat.zero_le _⟩
  · exact hq
  · exact Low48BentSupport.graph_chamber ht hj
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 4)
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 3)

private theorem last_allowed {p q : Shape}
    (v : Fin 5) : Allowed (caps p q 4) (Finsupp.single v 1) := by
  let k := taylorLength - 3
  have hb' : 1 ≤ 1 + k * (p.b - 1) := by omega
  have hj' : 4 ≤ 4 + k * (p.j - 2) := by omega
  have ht' : 2 ≤ 2 + k * p.t := by omega
  have hd' : 1 ≤ min (1 + k) ((2 + k * p.t) / 2) := by omega
  fin_cases v <;> simp [caps, lifted, Allowed, ← show k = taylorLength - 3 from rfl] <;> omega

theorem ordinary_doubled {p q : Shape} :
    Doubled (rawFamily (caps p q)) (capFamily (caps p q)) where
  zero_mem i := by simp [rawFamily, Allowed]
  pair_mem _ _ ha _ hb := Low48BentSupport.raw_add ha hb
  last_coordinate := last_allowed

private def integr (a : Cap) : ℚ := integral a

private def signed (p q : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps p q))

private theorem base_signed (p q : Shape) :
    Low6960Prices.tiltedSurface p q = (signed p q).toNat := by
  change Low48Price.ambientMix (slots.map (caps p q)) = _
  exact ambient_list (caps p q)

private theorem base_normalize (p q : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (capSum (caps p q) (positiveDiagonal J))) = (signed p q : ℚ) := by
  have H := Low48BentPolarization.remove_baseline (caps p q)
  change _ = _ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr (capSum (caps p q) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (Low48BentLattice.Sum J (caps p q)) from H]
  unfold signed
  push_cast
  rfl

private theorem ordinary_coeff (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5 = integr a / 60 := by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget {p q : Shape} (h : ∀ i, Chamber (caps p q i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps p q)) ⊥ Finset.univ ≤
      (Low6960Prices.tiltedSurface p q : ℚ) := by
  rw [mul_assoc, ambient_cap (caps p q) h (fun a => integr a / 60) ordinary_coeff]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize, base_signed]
  exact_mod_cast (show signed p q ≤ ((signed p q).toNat : ℤ) by omega)


theorem chart {f Q : Row 4} {l : ℕ} (q : Shape) (ht : 1 ≤ (shape f).t)
    (b : Low6960GeometryCut_2.Branch f Q l) :
    Chart (rawFamily (caps (shape f).chamber q)) b := by
  have h := Low6960ActiveCycle.ordinary_chart ht b
  exact h

#print axioms ordinary_budget
#print axioms chart

end
end Low6960SharedBentCaps

end Merged_R6960Low6960SharedBentCaps
