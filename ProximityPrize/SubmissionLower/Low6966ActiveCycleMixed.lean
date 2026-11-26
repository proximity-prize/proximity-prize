import ProximityPrize.SubmissionLower.Low6966ActiveCycleCaps
import ProximityPrize.SubmissionLower.Low6966GeometryCut
import ProximityPrize.SubmissionLower.Low6966ActiveCyclePrice

set_option Elab.async false

-- merged module Low6966SharedBentCaps
section Merged_Low6966SharedBentCaps

-- merged module R6960Low6966ActiveCycleChart
section Merged_R6960Low6966ActiveCycleChart

set_option autoImplicit false
set_option Elab.async false

namespace Low6966ActiveCycle

noncomputable section

open Polynomial
open P3 (K)
open Low6966Prices (physicalDegree taylorLength)
open K1_13 (Row shape extend InBox Shape)
open Low48BentCycle (Family rawFamily)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5 actualPoint)
open K1_13_6_2_2 (generic5 rawGraph numerator denominator padded padded_last)
open Low6966GeometryCut_2 (Branch branch_box)
open MvPolynomial
open Low6966GeometryCut_2_1 (valuePolynomial value_section numerator_associated)

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
    (hK : Low6966Prices.ActiveFits f K) (ha : Low6966Prices.activeFitsPrice (shape f) K)
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

end Low6966ActiveCycle

end Merged_R6960Low6966ActiveCycleChart

-- merged module R6960Low6966SharedBentCaps
section Merged_R6960Low6966SharedBentCaps
set_option Elab.async false
namespace Low6966SharedBentCaps
noncomputable section

open K1_13 (Shape Row shape)
open K1_13_6 (GeoField)
open Low6966Prices (taylorLength)
open Low6966ActiveCycle (Doubled Chart)
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
    Low6966Prices.tiltedSurface p q = (signed p q).toNat := by
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
      (Low6966Prices.tiltedSurface p q : ℚ) := by
  rw [mul_assoc, ambient_cap (caps p q) h (fun a => integr a / 60) ordinary_coeff]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize, base_signed]
  exact_mod_cast (show signed p q ≤ ((signed p q).toNat : ℤ) by omega)


theorem chart {f Q : Row 4} {l : ℕ} (q : Shape) (ht : 1 ≤ (shape f).t)
    (b : Low6966GeometryCut_2.Branch f Q l) :
    Chart (rawFamily (caps (shape f).chamber q)) b := by
  have h := Low6966ActiveCycle.ordinary_chart ht b
  exact h


end
end Low6966SharedBentCaps

end Merged_R6960Low6966SharedBentCaps

end Merged_Low6966SharedBentCaps

-- merged module Low6966ActiveCycleMixed
section Merged_Low6966ActiveCycleMixed

set_option autoImplicit false
set_option Elab.async false

namespace Low6966ActiveCycle

noncomputable section

open Polynomial MvPolynomial
open P3 (K)
open Low6966GeometryCut (MixedMark CutInput MixedBound)
open Low6966GeometryCut_2 (Branch branch_of_mixed)
open Low6966Prices (primaryBox tiltedSurface)
open K1_13 (Row extend embed shape)
open Low48BentCycle (Family mixedDegree rawFamily capFamily)
open K1_13_6 (Pieces CurveSections toGeneric)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand)
open K1_13_6_2_4 (oldEmbedding)
open scoped BigOperators

theorem mixed {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l budget : ℕ}
    {R B : Family} [∀ i, Finite (B i)]
    (input : CutInput Γ s f Q l) (hDB : Doubled R B)
    (hfbox : Section R 0 (oldEmbedding (toGeneric f)))
    (hQbox : Section R 1 (oldEmbedding (toGeneric Q)))
    (hchart : ∀ b : Branch f Q l, Chart R b)
    (hbudget : (60 * 32 : ℚ) * mixedDegree B ⊥ Finset.univ ≤ (budget : ℚ)) :
    MixedBound Γ s f Q l (60 * 32) budget := by
  classical
  let point (γ : K) := actualPoint (extend (s γ))
  let marked := Γ.filter (fun γ => MixedMark f Q l (extend (s γ)))
  let assign (γ : marked) : Branch f Q l :=
    Classical.choose (branch_of_mixed (Finset.mem_filter.mp γ.property).2)
  let branches := marked.attach.image assign
  let labels (b : Branch f Q l) :=
    marked.filter (fun γ => ∃ h : γ ∈ marked, assign ⟨γ, h⟩ = b)
  have label_sub (b : Branch f Q l) : labels b ⊆ Γ :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have contains_label (b : Branch f Q l) (γ : K) (hγ : γ ∈ labels b) :
      b.Contains (point γ) := by
    obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hγ).2
    exact Classical.choose_spec (branch_of_mixed (Finset.mem_filter.mp h).2)
  have labels_nonempty (b : Branch f Q l) (hb : b ∈ branches) : (labels b).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨γ.val, Finset.mem_filter.mpr ⟨γ.property, γ.property, rfl⟩⟩
  have available (b : Branch f Q l) : ∃ T ⊆ labels b,
      (b.Simple → T = labels b) ∧
      (b ∈ branches → ¬ b.Simple → 0 < T.card ∧ CurveSections (labels b) s T.card ∧
        Demand (labels b) s T) := by
    by_cases hs : b.Simple
    · exact ⟨labels b, Finset.Subset.rfl, fun _ => rfl, fun _ hn => (hn hs).elim⟩
    by_cases hb : b ∈ branches
    · obtain ⟨T, hsub, hd⟩ := maximal_demand (labels b) s (labels_nonempty b hb)
      exact ⟨T, hsub, fun h => (hs h).elim, fun _ _ => hd⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => (hs h).elim, fun h _ => (hb h).elim⟩
  choose demanded demand_sub demand_simple demand_multiple using available
  let points (b : Branch f Q l) := (demanded b).image point
  have points_card (b : Branch f Q l) : (points b).card = (demanded b).card := by
    apply Finset.card_image_of_injOn
    intro γ hγ δ hδ heq
    exact input.distinct (label_sub b (demand_sub b hγ)) (label_sub b (demand_sub b hδ))
      (Polynomial.map_injective embed embed.injective (actualPoint_injective heq))
  have points_on (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) : b.Contains p := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    exact contains_label b γ (demand_sub b hγ)
  have points_next (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) :
      MvPolynomial.eval p b.next = 0 := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    apply b.next_actual (contains_label b γ (demand_sub b hγ))
    simpa only [Polynomial.natDegree_map] using input.degree γ (label_sub b (demand_sub b hγ))
  have bound5 := bound hDB f Q l input.small input.proper hfbox hQbox branches points
    (by
      intro b hb
      obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := hchart b
      refine ⟨hgraph, ⟨E, hE, hEeq⟩, points_on b, ?_⟩
      by_cases hs : b.Simple
      · exact Or.inr ⟨H, hH, b.lifted_proper_of_associated hHeq (b.next_proper hs),
          fun p hp hon => b.lifted_zero_of_associated hHeq hon (points_next b p hp)⟩
      rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
      · exact Or.inl (by rw [points_card, hone])
      obtain ⟨D, hD, hEval⟩ := hvalue x a
      obtain ⟨δ, hδ, hδvalue⟩ := hwit
      have hδon := contains_label b δ hδ
      refine Or.inr ⟨D, hD, b.lifted_proper_of_nonzero (point δ) hδon ?_, ?_⟩
      · exact fun hzero => hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp hzero)
      · intro p hp hon
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
        have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
        exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ))) hon).mpr hvalueγ)
  let simple := branches.filter Branch.Simple
  let multiple := branches.filter (fun b => ¬ b.Simple)
  let e := multiple.equivFin
  let C : Pieces Γ :=
    { n := multiple.card
      piece := fun i => labels (e.symm i).val
      subset := fun i => label_sub (e.symm i).val
      degree := fun i => (demanded (e.symm i).val).card }
  let B := simple.biUnion labels
  have hmultiple (i : Fin C.n) := Finset.mem_filter.mp (e.symm i).property
  refine ⟨C, B,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).2.1,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).1, ?_, ?_⟩
  · intro γ hγ hm
    have hmark : γ ∈ marked := Finset.mem_filter.mpr ⟨hγ, hm⟩
    let b := assign ⟨γ, hmark⟩
    have hb : b ∈ branches := Finset.mem_image.mpr ⟨_, Finset.mem_attach _ _, rfl⟩
    have hlabel : γ ∈ labels b := Finset.mem_filter.mpr ⟨hmark, hmark, rfl⟩
    by_cases hs : b.Simple
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hs⟩, hlabel⟩)
    have hbm : b ∈ multiple := Finset.mem_filter.mpr ⟨hb, hs⟩
    apply Finset.mem_union_left _
    refine Finset.mem_biUnion.mpr ⟨e ⟨b, hbm⟩, Finset.mem_univ _, ?_⟩
    change γ ∈ labels (e.symm (e ⟨b, hbm⟩)).val
    simpa only [Equiv.symm_apply_apply] using hlabel
  · have htotal : C.total = ∑ b ∈ multiple, (demanded b).card := by
      calc
        C.total = ∑ b : multiple, (demanded b.val).card :=
          Equiv.sum_comp e.symm (fun b : multiple => (demanded b.val).card)
        _ = _ := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_attach multiple (fun b => (demanded b).card)
    have hsimple : (∑ b ∈ simple, b.weight * (points b).card) =
        ∑ b ∈ simple, (labels b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, demand_simple b hs, Branch.weight, ite_eq_left hs, one_mul]
    have hmult : (∑ b ∈ multiple, b.weight * (points b).card) = 2 * C.total := by
      rw [htotal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, Branch.weight, ite_eq_right hs]
    have hpart : (∑ b ∈ simple, b.weight * (points b).card) +
        (∑ b ∈ multiple, b.weight * (points b).card) =
        ∑ b ∈ branches, b.weight * (points b).card :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hB : B.card ≤ ∑ b ∈ simple, (labels b).card := Finset.card_biUnion_le
    have hpay : 2 * C.total + B.card ≤ ∑ b ∈ branches, b.weight * (points b).card := by
      rw [← hpart, hsimple, hmult, Nat.add_comm (∑ b ∈ simple, (labels b).card)]
      exact Nat.add_le_add_left hB _
    have hcount := (mul_le_mul_of_nonneg_left bound5 (by norm_num : (0 : ℚ) ≤ 60 * 32)).trans
      hbudget
    have hcount' : (60 * 32) * l * (∑ b ∈ branches, b.weight * (points b).card) ≤
        budget := by
      apply (Nat.cast_le (α := ℚ)).mp
      push_cast
      simpa only [← mul_assoc, show (60 : ℚ) * 32 = 1920 by norm_num] using hcount
    exact (Nat.mul_le_mul_left ((60 * 32) * l) hpay).trans hcount'

theorem mixed_tilted : Low6966GeometryCut.c2Tilted := by
  intro Γ s f Q l input hguard
  let p := (shape f).chamber
  have hp := K1_13_7_1.shape_chamber f
  have ht : 1 ≤ p.t := input.small.2.1
  have hj : 3 * p.t + 3 ≤ p.j := hguard.1
  have hCh : ∀ i, Low48BentLattice.Chamber (caps p i) := caps_chamber hp.1 ht hj
  refine mixed (R := rawFamily (caps p)) (B := capFamily (caps p)) input
    ordinary_doubled ?_ ?_ ?_ ?_
  · exact Low48BentCycle.old_section ⟨le_max_left _ _, le_rfl, le_rfl⟩
  · exact Low48BentCycle.old_section input.box
  · exact ordinary_chart ht
  · exact ordinary_budget hCh

theorem mixed_active : Low6966GeometryCut.c2Active := by
  intro Γ s f Q l input K hK hQ hguard hactive
  let p := (shape f).chamber
  have ht3 : 3 ≤ p.t := hactive.1
  have hfits := caps_active hguard hactive
  have hc : 4 ≤ baseClip p K := hactive.2.1
  have hK' : baseClip p K ≤ p.b + p.j - K := (clip_bounds _ _ _).1
  have hsum : K + baseClip p K ≤ p.b + p.j := by omega
  refine mixed (R := activeRaw p K) (B := activeFamily p K) input
    (active_doubled hfits) ?_ ?_ ?_ ?_
  · exact old_section_active ⟨le_max_left _ _, le_rfl, le_rfl⟩ hK hsum
  · exact old_section_active input.box hQ (by decide : 5164 + 498 ≤ 4012 + 1650)
  · exact active_chart hK hactive
  · exact active_budget ht3 hfits

theorem proof : Low6966Prices.c6 := Low6966GeometryCut.proof mixed_tilted mixed_active

end

end Low6966ActiveCycle


end Merged_Low6966ActiveCycleMixed
