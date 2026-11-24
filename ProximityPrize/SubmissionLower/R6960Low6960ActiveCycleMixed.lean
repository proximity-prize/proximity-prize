import ProximityPrize.SubmissionLower.R6960Low6960SharedBentCaps
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice

set_option autoImplicit false
set_option Elab.async false

namespace Low6960ActiveCycle

noncomputable section

open Polynomial MvPolynomial
open P3 (K)
open Low6960GeometryCut (MixedMark CutInput MixedBound)
open Low6960GeometryCut_2 (Branch branch_of_mixed)
open Low6960Prices (primaryBox tiltedSurface)
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

theorem mixed_tilted : Low6960GeometryCut.c2Tilted := by
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

theorem mixed_active : Low6960GeometryCut.c2Active := by
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

theorem proof : Low6960Prices.c6 := Low6960GeometryCut.proof mixed_tilted mixed_active

end

end Low6960ActiveCycle

#print axioms Low6960ActiveCycle.proof
#print axioms Low6960ActiveCycle.bound
