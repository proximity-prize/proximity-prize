import ProximityPrize.SubmissionLower.Final50ActiveCycleMixed
import ProximityPrize.SubmissionLower.Shared50CycleBound
import ProximityPrize.SubmissionLower.Shared50CycleFour
import ProximityPrize.SubmissionLower.Shared50CycleLegacy

namespace Shared50Tally
noncomputable section

open P3 (K)
open K1_13 (Row extend embed chart liftedChart shape)
open K1_13_6 (GeoJets Pieces CurveSections toGeneric)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand Box4 Box5 graphBox)
open Final50GeometryCut (CutInput)
open Final50GeometryCut_2 (Branch Chart4 Chart5 Slice4 Slice5 chart4)
open Final50ActiveCycle (Chart Section Slice)
open Final50Price (taylorLength)
open scoped Polynomial BigOperators

def hasBranch (f Q : Row 4) (l : ℕ) (S : Set (Ideal GeoJets)) (g : K1_13.Geom[X]) : Prop :=
  ∃ b : Branch f Q l, b.surface ∈ S ∧ b.Contains (actualPoint g)

structure Data (Γ : Finset K) (s : K→K[X]) (f Q : Row 4) (l : ℕ)
    (S : Set (Ideal GeoJets)) where
  branches : Finset (Branch f Q l)
  allowed : ∀ b∈branches, b.surface∈S
  labels : Branch f Q l → Finset K
  label_sub : ∀ b, labels b ⊆ Γ
  label_on : ∀ b γ, γ∈labels b → b.Contains (actualPoint (extend (s γ)))
  demanded : Branch f Q l → Finset K
  demand_sub : ∀ b, demanded b ⊆ labels b
  demand_simple : ∀ b, b.Simple → demanded b=labels b
  demand_multiple : ∀ b∈branches, ¬b.Simple → 0<(demanded b).card ∧
    CurveSections (labels b) s (demanded b).card ∧ Demand (labels b) s (demanded b)
  covered : ∀ γ∈Γ, hasBranch f Q l S (extend (s γ)) → ∃ b∈branches, γ∈labels b

private def point {s : K→K[X]} (γ : K) : JetPoint := actualPoint (extend (s γ))

def Data.points {Γ s f Q l S} (D : Data Γ s f Q l S) (b : Branch f Q l) :
    Finset JetPoint := by
  classical
  exact (D.demanded b).image (point (s := s))

def build {Γ s f Q l} (S : Set (Ideal GeoJets)) : Data Γ s f Q l S := by
  classical
  let marked := Γ.filter (fun γ => hasBranch f Q l S (extend (s γ)))
  let assign (γ : marked) : Branch f Q l :=
    Classical.choose (Finset.mem_filter.mp γ.property).2
  let branches := marked.attach.image assign
  let labels (b : Branch f Q l) :=
    marked.filter (fun γ => ∃ h : γ ∈ marked, assign ⟨γ, h⟩ = b)
  let point := point (s := s)
  have label_sub (b : Branch f Q l) : labels b ⊆ Γ :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have contains_label (b : Branch f Q l) (γ : K) (hγ : γ ∈ labels b) :
      b.Contains (point γ) := by
    obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hγ).2
    exact (Classical.choose_spec (Finset.mem_filter.mp h).2).2
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
  refine ⟨branches,?_,labels,label_sub,contains_label,demanded,demand_sub,
    demand_simple,demand_multiple,?_⟩
  · intro b hb
    obtain ⟨γ,_,rfl⟩ := Finset.mem_image.mp hb
    exact (Classical.choose_spec (Finset.mem_filter.mp γ.property).2).1
  · intro γ hγ hcase
    have hmark : γ∈marked := Finset.mem_filter.mpr ⟨hγ,hcase⟩
    exact ⟨assign ⟨γ,hmark⟩,Finset.mem_image.mpr ⟨_,Finset.mem_attach _ _,rfl⟩,
      Finset.mem_filter.mpr ⟨hmark,hmark,rfl⟩⟩

variable {Γ : Finset K} {s : K→K[X]} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

theorem Data.points_card (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) (b : Branch f Q l) : (D.points b).card = (D.demanded b).card := by
  classical
  unfold Data.points
  apply Finset.card_image_of_injOn
  intro γ hγ δ hδ heq
  exact input.distinct (D.label_sub b (D.demand_sub b hγ)) (D.label_sub b (D.demand_sub b hδ))
    (Polynomial.map_injective embed embed.injective (actualPoint_injective heq))

theorem Data.points_on (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) (b : Branch f Q l) (p : JetPoint) (hp : p ∈ D.points b) : b.Contains p := by
  classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
  exact D.label_on b γ (D.demand_sub b hγ)

theorem Data.points_next (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) (b : Branch f Q l) (p : JetPoint) (hp : p ∈ D.points b) :
    MvPolynomial.eval p b.next = 0 := by
  classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
  apply b.next_actual (D.label_on b γ (D.demand_sub b hγ))
  simpa only [Polynomial.natDegree_map] using input.degree γ (D.label_sub b (D.demand_sub b hγ))


theorem Data.four (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) :
    ∀ b∈D.branches, Box4 (chart (taylorLength+1) (shape f).chamber) b.member ∧
      (∀ p∈D.points b, b.Contains p) ∧ Slice4 b (D.points b) := by
  let points := D.points
  let points_card := D.points_card input
  let points_on := D.points_on input
  let points_next := D.points_next input
  let contains_label := D.label_on
  let label_sub := D.label_sub
  let demand_sub := D.demand_sub
  let demand_multiple := D.demand_multiple
  intro b hb
  obtain ⟨hmember, hnext, hvalue⟩ := chart4 input.small b
  refine ⟨hmember, points_on b, ?_⟩
  by_cases hs : b.Simple
  · exact Or.inr ⟨b.next, hnext, b.next_proper hs, points_next b⟩
  rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
  · exact Or.inl (by rw [points_card, hone])
  obtain ⟨D, hD, hEval⟩ := hvalue x a
  obtain ⟨δ, hδ, hδvalue⟩ := hwit
  have hδon := contains_label b δ hδ
  have hproper : D ∉ b.curve := fun hmem =>
    hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp (hδon.1 hmem))
  refine Or.inr ⟨D, hD, hproper, ?_⟩
  intro p hp
  classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
  have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
  exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ)))
    (contains_label b γ (demand_sub b hγ))).mpr hvalueγ

theorem Data.five (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) :
    ∀ b∈D.branches, Box5 (graphBox (shape f).chamber) 1 b.graph ∧
      (∃ E, Box5 (liftedChart (taylorLength+1) (shape f).chamber) (taylorLength+1) E ∧
        Associated (b.onGraph E) (b.localMap b.member)) ∧
      (∀ p∈D.points b, b.Contains p) ∧ Slice5 b (D.points b) := by
  let points := D.points
  let points_card := D.points_card input
  let points_on := D.points_on input
  let points_next := D.points_next input
  let contains_label := D.label_on
  let label_sub := D.label_sub
  let demand_sub := D.demand_sub
  let demand_multiple := D.demand_multiple
  intro b hb
  obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := Final50GeometryCut_2_1.proof f Q l input.small b
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
    classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
    exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ))) hon).mpr hvalueγ

theorem Data.bent {R : Low48BentCycle.Family} (D : Data Γ s f Q l S)
    (input : CutInput Γ s f Q l) (hchart : ∀ b : Branch f Q l, Chart R b) :
    ∀ b∈D.branches, Section R 2 b.graph ∧
      (∃ E, Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member)) ∧
      (∀ p∈D.points b,b.Contains p) ∧ Slice R b (D.points b) := by
  let points := D.points
  let points_card := D.points_card input
  let points_on := D.points_on input
  let points_next := D.points_next input
  let contains_label := D.label_on
  let label_sub := D.label_sub
  let demand_sub := D.demand_sub
  let demand_multiple := D.demand_multiple
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
    classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
    exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ))) hon).mpr hvalueγ

theorem Data.pieces (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) :
    ∃ (C : Pieces Γ) (B : Finset K), C.curves s ∧ (∀ i, 0<C.degree i) ∧
      (∀ γ∈Γ, hasBranch f Q l S (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      2*C.total+B.card ≤ ∑ b∈D.branches, b.weight*(D.points b).card := by
  classical
  let branches := D.branches
  let labels := D.labels
  let demanded := D.demanded
  let demand_simple := D.demand_simple
  let points := D.points
  let points_card := D.points_card input
  let points_on := D.points_on input
  let points_next := D.points_next input
  let contains_label := D.label_on
  let label_sub := D.label_sub
  let demand_sub := D.demand_sub
  let demand_multiple := D.demand_multiple
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
    obtain ⟨b,hb,hlabel⟩ := D.covered γ hγ hm
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
    exact hpay

end
end Shared50Tally
