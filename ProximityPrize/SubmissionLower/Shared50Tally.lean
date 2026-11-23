import ProximityPrize.SubmissionLower.Final50ActiveCycleMixed
import ProximityPrize.SubmissionLower.Shared50CycleBound
import ProximityPrize.SubmissionLower.Shared50CycleFour
import ProximityPrize.SubmissionLower.Shared50CycleLegacy

set_option Elab.async false
namespace Shared50Tally
noncomputable section

open P3 (K)
open K1_13 (Row extend embed chart liftedChart shape)
open K1_13_6 (GeoJets Pieces CurveSections toGeneric)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand Box4 Box5 graphBox)
open Final50GeometryCut (CutInput)
open Final50GeometryCut_2 (Branch Chart4  Slice4  chart4)
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




end
end Shared50Tally
