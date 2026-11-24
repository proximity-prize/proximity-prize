import ProximityPrize.SubmissionLower.R6960Low6960GeometryCut
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleMixed
import ProximityPrize.SubmissionLower.R6960Low6960SharedCycleBound
import ProximityPrize.SubmissionLower.R6960Low6960SharedCycleFour
import ProximityPrize.SubmissionLower.R6960Low6960SharedBentCaps
import ProximityPrize.SubmissionLower.R6960Low6960RetainedWitness

-- merged module R6960Low6960SharedCycleLegacy
section Merged_R6960Low6960SharedCycleLegacy
set_option Elab.async false

namespace Low6960SharedCycleLegacy
noncomputable section
open Low6960Prices (SmallFactor primaryBox taylorLength)
open Low6960GeometryCut_2 (Branch Slice5 budget5)
open P0_9_6_2_3 (cylinder_comparison cycle_comparison divisor_comparison proper_cut_comparison)
open K1_13 (Row Shape shape InBox liftedChart)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5 Box5 graphBox)
open K1_13_6_2_4 (Admissible Chamber Component DimLE DivisorBound OfDim LengthAt
  ambient_dim cylinder cylinder_injective dim_le_after_section mixedDegree oldEmbedding
  old_section_box point_bound pointIdeal sectionIdeal)
open scoped BigOperators
open Low6960GeometryCut_2_3 (boxes graphLift last_caps boxes_admissible chart_index_eq
  graphLift_same_chart membership_same_chart graphLift_comap member_proper_on_graph ambient_budget)
open Low6960GeometryCut_2_3 (bound_marks)

private theorem initial_bound
    (f Q : Row 4) (weight : Ideal GeoJets → ℕ) (hf : SmallFactor f) (hQ : ¬ f ∣ Q)
    (hQbox : InBox (shape Q) primaryBox) (S : Finset (Ideal GeoJets))
    (hS : ∀ P ∈ S, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (weight P : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime) :
    (∀ P ∈ S, (cylinder P).IsPrime ∧ OfDim (cylinder P) 3) ∧
      (∑ P ∈ S, (weight P : ℚ) * mixedDegree (boxes (shape f).chamber) (cylinder P) {2, 3, 4}) ≤
        mixedDegree (boxes (shape f).chamber) ⊥ Finset.univ := by
  classical
  let p := (shape f).chamber
  let B := boxes p
  have hB := boxes_admissible p (K1_13_7_1.shape_chamber f)
  let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
  let J := sectionIdeal A (oldEmbedding (toGeneric Q))
  obtain ⟨hregQ, hAlgebra⟩ := cylinder_comparison f Q hf.1 hQ
  have hregf : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets5)
      (oldEmbedding (toGeneric f))) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne
      (K1_13_6_3_6.toGeneric_ne_zero hf.1.ne_zero)
  have hboxf : Box5 p 0 (oldEmbedding (toGeneric f)) :=
    old_section_box ⟨le_max_left _ _, le_rfl, le_rfl⟩
  have hAdim : DimLE A 4 := dim_le_after_section hregf ambient_dim
  have hJdim : DimLE J 3 := dim_le_after_section hregQ hAdim
  have hgeom (P : Ideal GeoJets) (hP : P ∈ S) :
      (cylinder P).IsPrime ∧ OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P), (weight P : ℕ∞) ≤ LengthAt J (cylinder P) hc.isPrime := by
    obtain ⟨h, hw⟩ := hS P hP
    obtain ⟨hd, hc, hl⟩ := hAlgebra P h
    exact ⟨hc.isPrime, hd, hc, hw.trans hl⟩
  refine ⟨fun P hP => ⟨(hgeom P hP).1, (hgeom P hP).2.1⟩, ?_⟩
  have hs := cycle_comparison B hB J {2, 3, 4} hJdim S cylinder weight cylinder_injective.injOn
    (fun P hP => (hgeom P hP).2.2)
  have hcutQ := proper_cut_comparison B hB A {2, 3, 4} 1 (by decide) hAdim
    (oldEmbedding (toGeneric Q)) (old_section_box hQbox) hregQ
  have hcutf := proper_cut_comparison B hB ⊥ {1, 2, 3, 4} 0 (by decide) ambient_dim
    (oldEmbedding (toGeneric f)) hboxf hregf
  have hall : (insert (0 : Fin 5) {1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
  rw [hall] at hcutf
  exact hs.trans (hcutQ.trans hcutf)
theorem bound_with_weights
    (f Q : Row 4) (l : ℕ) (hf : SmallFactor f) (hproper : ¬ f ∣ Q)
    (hQ : InBox (shape Q) primaryBox)
    (weight : Ideal GeoJets → ℕ)
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hF : ∀ b ∈ F, Box5 (graphBox (shape f).chamber) 1 b.graph ∧
       (∃ E, Box5 (liftedChart (taylorLength + 1) (shape f).chamber)
          (taylorLength + 1) E ∧ Associated (b.onGraph E) (b.localMap b.member)) ∧
       (∀ p ∈ T b, b.Contains p) ∧ Slice5 b (T b))
    (hcut : ∀ b ∈ F, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime) :
    32 * (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight : ℚ) * (T b).card)) ≤
      (budget5 (shape f).chamber : ℚ) := by
  classical
  have hdiv := divisor_comparison
  have hgraph := @Low6960GeometryCut_2_3_1.proof f Q l
  have hmember := @Low6960GeometryCut_2_3_2.proof f Q l
  let p := (shape f).chamber
  have hp : Chamber p := K1_13_7_1.shape_chamber f
  let B := boxes p
  have hB : Admissible B := boxes_admissible p hp
  let S := F.image Branch.surface
  let fibre (P : Ideal GeoJets) := F.filter fun b => b.surface = P
  let charge (b : Branch f Q l) : ℚ := (b.weight : ℚ) * (T b).card
  obtain ⟨hZ, hsumZ⟩ := initial_bound f Q weight hf hproper hQ S (by
    intro P hP
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨b.base, hcut b hb⟩)
  have hfibre (P : Ideal GeoJets) (hP : P ∈ S) :
      (∑ c ∈ fibre P, charge c) ≤ mixedDegree B (cylinder P) {2, 3, 4} := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    let G := graphLift b b.surface
    let C (c : Branch f Q l) := graphLift c c.curve
    obtain ⟨hboxG, ⟨E, hboxE, hE⟩, _, _⟩ := hF b hb
    obtain ⟨hZprime, hZdim⟩ := hZ _ hP
    obtain ⟨hproperG, hG, hGdim⟩ := hgraph b hZprime hZdim
    have hC (c : Branch f Q l) (hcs : c.surface = b.surface) :
        Component G E (C c) c.weight ∧ OfDim (C c) 1 := by
      have hr := chart_index_eq hcs
      have hsame : graphLift c c.surface = G :=
        (graphLift_same_chart hr c.surface).trans (congrArg (graphLift b) hcs)
      have hE' := (membership_same_chart hr E).mpr hE
      rw [← hsame]
      exact hmember c E (hsame.symm ▸ hG.minimal.isPrime) (hsame.symm ▸ hGdim) hE'
    have hproperE := member_proper_on_graph b hE
    have inj : Set.InjOn C (fibre b.surface : Set (Branch f Q l)) := by
      intro c hc d hd he
      have hcs := (Finset.mem_filter.mp hc).2
      have hds := (Finset.mem_filter.mp hd).2
      apply Branch.eq_of_surface_curve (hcs.trans hds.symm)
      rw [← graphLift_comap c c.curve c.divisor.isPrime c.regularCurve,
        ← graphLift_comap d d.curve d.divisor.isPrime d.regularCurve]
      exact congrArg (Ideal.comap oldEmbedding) he
    have hmarks : (∑ c ∈ fibre b.surface, charge c) ≤
        ∑ c ∈ fibre b.surface, (c.weight : ℚ) * mixedDegree B (C c) {4} := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨hcF, hcs⟩ := Finset.mem_filter.mp hc
      obtain ⟨_, _, hon, hslice⟩ := hF c hcF
      obtain ⟨hcomp, hdim⟩ := hC c hcs
      exact mul_le_mul_of_nonneg_left
        (bound_marks hdiv hB c (T c) rfl hon hslice hcomp.minimal.isPrime hdim)
        (Nat.cast_nonneg _)
    have hEbound := hdiv B hB G {4} 3 hG.minimal.isPrime (by decide) hGdim E hboxE hproperE
      (fibre b.surface) C Branch.weight inj (fun c hc => (hC c (Finset.mem_filter.mp hc).2).1)
    have hGbound := hdiv B hB (cylinder b.surface) {3, 4} 2 hZprime (by decide) hZdim
      b.graph hboxG hproperG {G} id (fun _ => 1) (fun _ _ _ _ h => h) (by
        intro P hP
        obtain rfl := Finset.mem_singleton.mp hP
        exact hG)
    have hGbound' : mixedDegree B G {3, 4} ≤ mixedDegree B (cylinder b.surface) {2, 3, 4} := by
      simpa only [Finset.sum_singleton, Nat.cast_one, one_mul, id_eq] using hGbound
    exact hmarks.trans (hEbound.trans hGbound')
  have hcharge :
      (∑ c ∈ F, (weight c.surface : ℚ) * charge c) ≤
        ∑ P ∈ S, (weight P : ℚ) * mixedDegree B (cylinder P) {2, 3, 4} := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Branch.surface)
      (fun b hb => Finset.mem_image_of_mem Branch.surface hb)
      (fun b => (weight b.surface : ℚ) * charge b)]
    apply Finset.sum_le_sum
    intro P hP
    change (∑ c ∈ fibre P, (weight c.surface : ℚ) * charge c) ≤ _
    calc
      _ = ∑ c ∈ fibre P, (weight P : ℚ) * charge c := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [(Finset.mem_filter.mp hc).2]
      _ = (weight P : ℚ) * ∑ c ∈ fibre P, charge c := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfibre P hP) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left (hcharge.trans hsumZ) (by norm_num)).trans
    (ambient_budget p hp)

#print axioms bound_with_weights
end
end Low6960SharedCycleLegacy

end Merged_R6960Low6960SharedCycleLegacy

-- merged module R6960Low6960SharedTally
section Merged_R6960Low6960SharedTally

set_option Elab.async false
namespace Low6960SharedTally
noncomputable section

open P3 (K)
open K1_13 (Row extend embed chart liftedChart shape)
open K1_13_6 (GeoJets Pieces CurveSections toGeneric)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand Box4 Box5 graphBox)
open Low6960GeometryCut (CutInput)
open Low6960GeometryCut_2 (Branch Chart4 Chart5 Slice4 Slice5 chart4)
open Low6960ActiveCycle (Chart Section Slice)
open Low6960Prices (taylorLength)
open scoped Polynomial BigOperators

def hasBranch (f Q : Row 4) (l : ℕ) (S : Set (Ideal GeoJets)) (g : (Polynomial K1_13.Geom)) : Prop :=
  ∃ b : Branch f Q l, b.surface ∈ S ∧ b.Contains (actualPoint g)

structure Data (Γ : Finset K) (s : K→(Polynomial K)) (f Q : Row 4) (l : ℕ)
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

private def point {s : K→(Polynomial K)} (γ : K) : JetPoint := actualPoint (extend (s γ))

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

variable {Γ : Finset K} {s : K→(Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

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
  obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := Low6960GeometryCut_2_1.proof f Q l input.small b
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

#print axioms Data.pieces
#print axioms Data.bent
end
end Low6960SharedTally

end Merged_R6960Low6960SharedTally

-- merged module R6960Low6960RetainedGeometry
section Merged_R6960Low6960RetainedGeometry

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

namespace Low6960RetainedCut
noncomputable section

open P3 (K I)
open K1_13 (Row Shape InBox shape mixed32 chart)
open Low6960Prices (Messages tiltedFits tiltedSurface taylorLength)
open Low6960GeometryCut (CutInput MixedBound)
open Low6960GeometryCut (chargedPrice assemble_charge continued_bound)
open Low6960ActiveCycle (mixed)
open scoped Polynomial BigOperators

/-- The accepted physical charge with an arbitrary mixed surface budget. -/
def cutPrice (x : Shape) (l scale surface : ℕ) := chargedPrice x l scale surface

def fourSurface (p q : Shape) :=
  mixed32 p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)

variable {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}

theorem smaller_tilted (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q : Shape) (hQ : InBox (shape Q) q) (hq : Low48BentLattice.Chamber (q,0))
    (hguard : tiltedFits (shape f)) :
    Γ.card ≤ cutPrice (shape f) l (60*32) (tiltedSurface (shape f).chamber q) := by
  let p := (shape f).chamber
  have hp := K1_13_7_1.shape_chamber f
  have ht : 1 ≤ p.t := input.small.2.1
  have hCh := Low6960SharedBentCaps.caps_chamber (p := p) hp.1 ht hguard.1 hq
  apply assemble_charge Low6960GeometryCut_1.proof continued_bound hm input (by decide : 0 < 60*32)
  apply Low6960ActiveCycle.mixed (R := Low48BentCycle.rawFamily (Low6960SharedBentCaps.caps p q))
    (B := Low48BentCycle.capFamily (Low6960SharedBentCaps.caps p q)) input Low6960SharedBentCaps.ordinary_doubled
  · exact Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩
  · exact Low48BentCycle.old_section hQ
  · exact Low6960SharedBentCaps.chart q ht
  · exact Low6960SharedBentCaps.ordinary_budget hCh

theorem smaller_four (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q : Shape) (hQ : InBox (shape Q) q) (hq : K1_13_6_2_3.ChamberBox q) :
    Γ.card ≤ cutPrice (shape f) l 32 (fourSurface (shape f).chamber q) := by
  classical
  let D : Low6960SharedTally.Data Γ s f Q l Set.univ := Low6960SharedTally.build Set.univ
  have h := Low6960SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q Q l input.small input.proper q hq hQ (fun _ => l)
    D.branches D.points (D.four input) (fun b _ => ⟨b.base,b.high⟩)
  have hh := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp h
  have hn : 32*l*(∑ b∈D.branches, b.weight*(D.points b).card) ≤ fourSurface (shape f).chamber q := by
    apply (Nat.cast_le (α := ℚ)).mp
    simp only [fourSurface,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat]
    simpa only [Nat.cast_mul,← Finset.mul_sum,mul_comm (32:ℚ),mul_assoc,mul_left_comm] using hh
  apply assemble_charge Low6960GeometryCut_1.proof continued_bound hm input (by decide : 0 < 32)
  obtain ⟨C,B,hcurve,hpos,hcover,hcost⟩ := D.pieces input
  refine ⟨C,B,hcurve,hpos,?_,(Nat.mul_le_mul_left (32*l) hcost).trans hn⟩
  intro γ hγ hmixed
  obtain ⟨b,hb⟩ := Low6960GeometryCut_2.branch_of_mixed hmixed
  exact hcover γ hγ ⟨b,Set.mem_univ _,hb⟩

#print axioms smaller_tilted
#print axioms smaller_four

end
end Low6960RetainedCut

end Merged_R6960Low6960RetainedGeometry

-- merged module R6960Low6960RetainedAssembly
section Merged_R6960Low6960RetainedAssembly

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
namespace Low6960RetainedCut
noncomputable section

open P3 (I K)
open K1_13 (Geom Row Shape shape InBox OrderAt atJet extend)
open Low6960Prices (primaryBox primaryCutoff TrueWeightLE ActiveFits SmallFactor Messages
  tiltedFits tiltedSurface physicalPrice ProperCut)
open scoped Polynomial BigOperators

def chamberHull (x : Shape) : Shape := ⟨max x.b x.j,x.j,min x.t (x.j/3)⟩

theorem hull_includes {Q : Row 4} {x : Shape} (hb : InBox (shape Q) x) :
    InBox (shape Q) (chamberHull x) := by
  have h := (K1_13_7_1.shape_chamber Q).2
  change 3*(shape Q).t ≤ (shape Q).j at h
  exact ⟨hb.1.trans (le_max_left _ _),hb.2.1, le_min hb.2.2 (by have := hb.2.1; omega)⟩

theorem hull_valid (x : Shape) : Low48BentLattice.Chamber (chamberHull x,0) := by
  refine ⟨le_max_right _ _,?_,Nat.zero_le _⟩
  change 3*min x.t (x.j/3) ≤ x.j
  have := min_le_right x.t (x.j/3)
  omega

def contractedPrice (x h : Shape) (l active : ℕ) : ℕ :=
  let q := chamberHull (residualBox h l)
  let old := physicalPrice x l active
  let four := if 0 < q.t then min old (cutPrice x l 32 (fourSurface x.chamber q)) else old
  if tiltedFits x then min four (cutPrice x l (60*32) (tiltedSurface x.chamber q)) else four

/-- Physical count for the actual extremal bank witness and the selected (off-retained) marks. -/
theorem price_of_witness_floor {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {P H f : Row 4}
    {k a l active : ℕ} (hm : Messages w Γ s) (hsmall : SmallFactor f)
    (hactive : ActiveFits f active) (hchar : f.degreeOf 3 < K1.p)
    (hon : ∀ γ∈Γ, K1_13.OnFactor f (extend (s γ)))
    (hoff : ∀ γ∈Γ, atJet H (extend (s γ)) ≠ 0)
    (hP : P ≠ 0) (hH : H ≠ 0) (hc : IsRelPrime f H) (hpos : 0 < l) (hl : l ≤ k-a)
    (hbox : InBox (shape P) primaryBox) (hweight : TrueWeightLE P primaryCutoff)
    (htaper : ActiveFits P 5164) (hord : ∀ γ∈Γ, OrderAt P (extend (s γ)) k)
    (divH : H^k ∣ P) (divF : f^a ∣ P) (exactF : ¬ f^(a+1) ∣ P) :
    ∀ h : Shape, InBox h (shape H) → Γ.card ≤ contractedPrice (shape f) h l active := by
  intro h hfloor
  obtain ⟨Q,hproper,hboxQ,hweightQ,hactiveQ,horderQ⟩ :=
    exists_divided_cut hP hH hsmall.1 hsmall.2.1 hchar hc hl hbox hweight htaper divH divF exactF
  have hQP : InBox (shape Q) primaryBox :=
    ⟨hboxQ.1.trans (Nat.sub_le _ _), hboxQ.2.1.trans (Nat.sub_le _ _),
      hboxQ.2.2.trans (Nat.sub_le _ _)⟩
  have horder (γ) (hγ : γ∈Γ) := horderQ _ (hoff γ hγ) (hord γ hγ)
  have hfloorQ : InBox (shape Q) (residualBox h l) :=
    ⟨hboxQ.1.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left l hfloor.1) _),
      hboxQ.2.1.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left l hfloor.2.1) _),
      hboxQ.2.2.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left l hfloor.2.2) _)⟩
  let q := chamberHull (residualBox h l)
  have hQ : InBox (shape Q) q := hull_includes hfloorQ
  have hch := hull_valid (residualBox h l)
  have input : Low6960GeometryCut.CutInput Γ s f Q l :=
    ⟨hm.distinct,hm.degree,hsmall,hon,hpos,hproper,hQP,hweightQ,horder⟩
  have hold := Low6960ActiveCycle.proof w Γ s hm f hsmall active hactive hon l hpos
    ⟨Q,hproper,hQP,hweightQ,hactiveQ,horder⟩
  have hfour : Γ.card ≤ (if 0 < q.t then min (physicalPrice (shape f) l active)
      (cutPrice (shape f) l 32 (fourSurface (shape f).chamber q)) else physicalPrice (shape f) l active) := by
    split
    next ht => exact le_min hold (smaller_four hm input q hQ ⟨hch.1,hch.2.1,ht⟩)
    next => exact hold
  unfold contractedPrice
  split
  next hg => exact le_min hfour (smaller_tilted hm input q hQ hch hg)
  next => exact hfour

/-- Physical count for the actual extremal bank witness and the selected (off-retained) marks. -/
theorem price_of_witness {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {P H f : Row 4}
    {k a l active : ℕ} (hm : Messages w Γ s) (hsmall : SmallFactor f)
    (hactive : ActiveFits f active) (hchar : f.degreeOf 3 < K1.p)
    (hon : ∀ γ∈Γ, K1_13.OnFactor f (extend (s γ)))
    (hoff : ∀ γ∈Γ, atJet H (extend (s γ)) ≠ 0)
    (hP : P ≠ 0) (hH : H ≠ 0) (hc : IsRelPrime f H) (hpos : 0 < l) (hl : l ≤ k-a)
    (hbox : InBox (shape P) primaryBox) (hweight : TrueWeightLE P primaryCutoff)
    (htaper : ActiveFits P 5164) (hord : ∀ γ∈Γ, OrderAt P (extend (s γ)) k)
    (divH : H^k ∣ P) (divF : f^a ∣ P) (exactF : ¬ f^(a+1) ∣ P) :
    Γ.card ≤ contractedPrice (shape f) (shape H) l active :=
  price_of_witness_floor hm hsmall hactive hchar hon hoff hP hH hc hpos hl hbox hweight
    htaper hord divH divF exactF (shape H) ⟨le_rfl,le_rfl,le_rfl⟩

#print axioms price_of_witness_floor
#print axioms price_of_witness

end
end Low6960RetainedCut

end Merged_R6960Low6960RetainedAssembly
