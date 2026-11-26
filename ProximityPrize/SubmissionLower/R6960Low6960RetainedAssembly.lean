import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdZZ6ou4c
import ProximityPrize.SubmissionLower.R6960ExceptionalStage
import ProximityPrize.SubmissionLower.R6960HelperPrefix
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleBound
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice
import ProximityPrize.SubmissionLower.R6960Low6960AllocWeight
import ProximityPrize.SubmissionLower.R6960Low6960FatCount
import ProximityPrize.SubmissionLower.R6960Low6960GeometryCut

section Merged6967_R6960Low6960RetainedAssembly
set_option Elab.async false






set_option Elab.async false

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

end Merged6967_R6960Low6960RetainedAssembly

section Merged6967_R6960RescueGeometryBills
set_option Elab.async false











set_option Elab.async false

-- merged module R6960RescueSource6960
section Merged_R6960RescueSource6960

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)

theorem checked (rect : Fin 4) (i : Fin 17) :
    Checked (bank rect i) (reserve i) (excess rect) (seed rect) := by
  fin_cases i
  · exact group0_checked rect 0
  · exact group1_checked rect 0
  · exact group1_checked rect 1
  · exact group1_checked rect 2
  · exact group1_checked rect 3
  · exact group2_checked rect 0
  · exact group2_checked rect 1
  · exact group2_checked rect 2
  · exact group3_checked rect 0
  · exact group3_checked rect 1
  · exact group3_checked rect 2
  · exact group4_checked rect 0
  · exact group4_checked rect 1
  · exact group5_checked rect 0
  · exact group5_checked rect 1
  · exact group6_checked rect 0
  · exact group7_checked rect 0

theorem cutoff_fit {h : ℕ} (lo : 2359≤h) (hi : h≤33579) (rect : Fin 4) (i : Fin 17) :
    cutoff h rect i+2*h*(reserve i)<(bank rect i).shape.m*179818 :=
  (checked rect i).cutoff_fit lo hi

/-- Each stage of each rectangle supplies a native avoiding row throughout
the high interval. The lower degree bounds refer to the single exceptional prime. -/
theorem rescue_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) (rect : Fin 4) (i : Fin 17) {G : Jet}
    (irr : Irreducible G) (seeded : UsesSeed G) (slope : 1≤G.natDegree)
    (hs : seed rect≤seedDegree G) (hj : G.natDegree+excess rect≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q :=
  (checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms checked
#print axioms cutoff_fit
#print axioms rescue_row

end Lower6960.RescueSource

end Merged_R6960RescueSource6960

-- merged module R6960RescueSourceException
section Merged_R6960RescueSourceException

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open HelperSource (helperBank helperCutoff helper_common_caps)

def jetCap (rect : Fin 4) : ℕ := ([1,1,1,7] : List ℕ).get ⟨rect.val,rect.isLt⟩

def seedCap (rect : Fin 4) : ℕ := ([1,6,85,78] : List ℕ).get ⟨rect.val,rect.isLt⟩

private theorem fits_rectangle {j u : ℕ} (loJ : 1≤j) (hiJ : j≤7)
    (loU : 1≤u) (hiU : u≤85) (mixed : 2≤j → u≤78) :
    ∃ rect : Fin 4, 1+excess rect≤j ∧ j≤jetCap rect ∧ seed rect≤u ∧ u≤seedCap rect := by
  by_cases hJ : 2≤j
  · refine ⟨3,?_⟩
    change 2≤j ∧ j≤7 ∧ 1≤u ∧ u≤78
    exact ⟨hJ,hiJ,loU,mixed hJ⟩
  · by_cases hU : u≤1
    · refine ⟨0,?_⟩
      change 1≤j ∧ j≤1 ∧ 1≤u ∧ u≤1
      omega
    · by_cases hU' : u≤6
      · refine ⟨1,?_⟩
        change 1≤j ∧ j≤1 ∧ 2≤u ∧ u≤6
        omega
      · refine ⟨2,?_⟩
        change 1≤j ∧ j≤1 ∧ 7≤u ∧ u≤85
        omega

/-- A common moving prime in the powered helper determines one rescue schedule
for all 17 stages. Its actual degrees fit that rectangle's geometry caps. -/
theorem exceptional_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 0<G.natDegree)
    (common : ∀ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣P) :
    ∃ rect : Fin 4, G.natDegree=1 ∧ jetDegree G≤jetCap rect ∧ seedDegree G≤seedCap rect ∧
      ∀ i : Fin 17, ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q := by
  obtain ⟨linear,loJ,hiJ,loU,hiU,mixed⟩ := helper_common_caps Crt word lo hi irr seeded slope common
  obtain ⟨rect,lowJ,highJ,lowU,highU⟩ := fits_rectangle loJ hiJ loU hiU mixed
  refine ⟨rect,linear,highJ,highU,fun i => ?_⟩
  exact rescue_row Crt word lo hi rect i irr seeded (by omega) lowU (by rw [linear]; exact lowJ)

#print axioms exceptional_rows

end Lower6960.RescueSource

end Merged_R6960RescueSourceException

-- merged module R6960RescueGeometry
section Merged_R6960RescueGeometry
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L FX Shape Jet jetAt atX liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom UsesSeed ODE)
open K1_14_2_2 (RowCaps Active dual Fits mass sectionDegree ordinateIncl ODECaps fixedOn)
open K1_14_2_2_2 (FiniteSections residualBudget ordinate_eq length_le_mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open RescueSource (bank reserve cutoff jetCap seedCap)
open DifferentialContact (Native)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
open P0_10R_1 (seed_projection section_bound component_height)
open P1_7_4_1 (irreducible_cut)
abbrev Model (u : P1.Words) (deleted : Finset I) := P1.ModelAt 33579 u deleted
abbrev Family {u deleted} (M : Model u deleted) (Γ : Finset K) := P1.FamilyAt 179818 M Γ
def word {u deleted} (M : Model u deleted) : I→L := fun i => algebraMap K L (M.word i)
def OnMark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (A : Ideal Ambient) (γ : K) : Prop := OnJet A (M.label γ) (F.scalar γ)
theorem label_injective {u deleted} (M : Model u deleted) : Function.Injective M.label :=
  fun _ _ h => sub_left_inj.mp h
def primeShape (rect : Fin 4) : Shape := ⟨0,jetCap rect,1,seedCap rect⟩
def initialCap (rect : Fin 4) : Fin 4 → ℕ := pairCap (primeShape rect) (bank rect 0).shape
theorem prime_shape_fit (rect : Fin 4) : (primeShape rect).J≤(primeShape rect).B := by
  fin_cases rect <;> decide
theorem initial_small (rect : Fin 4) (k : Fin 4) : initialCap rect k<K1.p := by
  fin_cases rect <;> fin_cases k <;> decide +kernel
theorem reserve_small (i : Fin 17) : reserve i<K1.p := by
  fin_cases i <;> decide +kernel
theorem contact_at_mark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {s : Shape} {W r : ℕ} {P : Jet} (inside : P∈evaluated Crt (word M) s W)
    (width : W+2*M.overhead.toNat*r<s.m*179818)
    (γ : K) (hγ : γ∈Γ) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (r+1) P := by
  let B := F.mark γ hγ
  have degree : (liftPoly (F.scalar γ)).natDegree≤131071+M.overhead.toNat := by
    rw [liftPoly, Polynomial.natDegree_map]
    rcases B.scalar_degree with hzero | hd
    · simp [hzero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at hd
      omega
  refine PrefixRows.contact_of_crt Crt (word M) s P inside width noPole
    (M.label γ) (F.scalar γ) (residues γ hγ) degree B.bad.support B.bad.agreement ?_
  intro i hit
  rw [word,liftPoly,nodeL,Polynomial.eval_map,Polynomial.eval₂_hom]
  exact congrArg (algebraMap K L) (B.scalar_hits i hit)
theorem zero_of_contact {z : K} {S : (Polynomial K)} {P : Jet} {r : ℕ}
    (contact : Native (RingHom.ker (jetMarkHom z S)) (r+1) P) : jetAt P z S=0 := by
  have test := contact [] (by simp)
  change toJet P∈RingHom.ker (jetMarkHom z S) at test
  rwa [RingHom.mem_ker,K1_14_2.eval_toJet] at test
private theorem initial_sections {G Q : Jet} {s t : Shape} (irr : Irreducible G)
    (avoid : ¬G∣Q) (gs : RowCaps G s) (qs : RowCaps Q t) (js : s.J≤s.B) (jt : t.J≤t.B) :
    ∃ A : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry A ∧ Fits A (pairCap s t) ∧
      (∀ J∈A,toJet G∈J ∧ toJet Q∈J) ∧
      ∀ z S,jetAt G z S=0 → jetAt Q z S=0 → ∃ J∈A,OnJet J z S := by
  have proper := irreducible_cut irr avoid
  obtain ⟨A,geom,cover⟩ := K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩ := section_bound _ _ proper s t js jt gs qs A geom
  refine ⟨A,?_,fit,fun J mem=>(geom J mem).2.2,cover⟩
  intro J mem
  obtain ⟨prime,dim,g,q⟩ := geom J mem
  exact ⟨prime,dim,component_height proper prime dim g q,finite J mem⟩
structure Initial {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (G Q₀ : Jet) (rect : Fin 4) where
  seeds : SeedCover
  seed_degree : seeds.curve.totalDegree ≤ initialCap rect 2
  seed_points : seeds.points.card ≤ initialCap rect 3
  ordinates : Finset FX
  ordinate_card : ordinates.card ≤ initialCap rect 0
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet Q₀∈J
  disjoint : Disjoint rankExit parents
  fits : Fits (rankExit∪parents) (initialCap rect)
  covers : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark F J γ) ∨ ∃ J∈parents,OnMark F J γ
private theorem classify {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 4} {A : Finset (Ideal Ambient)}
    (geom : P1_7_4_1.SectionGeometry A) (fit : Fits A (initialCap rect))
    (rows : ∀ J∈A,toJet G∈J ∧ toJet Q₀∈J)
    (cover : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → ∃ J∈A,OnMark F J γ) :
    Nonempty (Initial F G Q₀ rect) := by
  classical
  let noSeeds := A.filter (fun J=>sectionDegree J 0=0)
  let constY := A.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := A.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>¬dual J)
  let parents := active.filter dual
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small rect k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) := (Γ.filter (OnMark F J)).image fun γ=>atX (F.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2⟩
  · intro J mem
    obtain ⟨hin,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,rows J (mem_filter.mp hin).1⟩
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2 (mem_filter.mp b).2
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · intro γ hγ zero
    obtain ⟨J,hin,on⟩ := cover γ hγ zero
    by_cases z : sectionDegree J 0=0
    · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
      exact Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))
    · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
      · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        by_cases d : dual J
        · exact Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
      · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        exact Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
          mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))
theorem initial_cover {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 4} (irr : Irreducible G) (avoid : ¬G∣Q₀)
    (capsG : RowCaps G (primeShape rect)) (capsQ : RowCaps Q₀ (bank rect 0).shape)
    (zero : ∀ γ∈Γ,jetAt Q₀ (M.label γ) (F.scalar γ)=0) :
    Nonempty (Initial F G Q₀ rect) := by
  obtain ⟨A,geom,fit,rows,cover⟩ := initial_sections irr avoid capsG capsQ (prime_shape_fit rect)
    (RescueSource.shape_guards rect 0).2.1
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))
theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (initial : Initial F G Q₀ rect) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))
#print axioms initial_cover
#print axioms Initial.rank_ode
end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometry

-- merged module R6960RescueGeometryHistory
section Merged_R6960RescueGeometryHistory
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual Fits mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open RescueSource (bank reserve cutoff jetCap seedCap)
open DifferentialContact (Native)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
theorem history_from_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G : Jet} {rect : Fin 4} (irr : Irreducible G) (capsG : RowCaps G (primeShape rect))
    (Q : Fin 17→Jet) (init : Initial F G (Q 0) rect) (avoid : ∀ i,¬G∣Q i)
    (caps : ∀ i,RowCaps (Q i) (bank rect i).shape)
    (contact : ∀ i γ,γ∈Γ → Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ)))
      (reserve i+1) (Q i)) :
    ∃ kept : ℕ→Finset (Ideal Ambient),
      kept 0=init.parents ∧ kept 1=init.parents ∧ Antitone kept ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve i+1) (Q i)) ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
        (reserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c) ∧
      ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
        ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
          ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  have on (J : Ideal Ambient) (mem : J∈init.parents) : Active J ∧ dual J ∧ toJet G∈J :=
    let h := init.parent_geom J mem
    ⟨h.1,h.2.1,h.2.2.2.1⟩
  choose S sub pass bound cut using fun i =>
    ExceptionalStage.filter irr (avoid i) capsG (caps i) (prime_shape_fit rect)
      (RescueSource.shape_guards rect i).2.1 init.parents on (reserve i) (reserve_small i)
  let selected (i : Fin 17) := if i = 0 then init.parents else S i
  have first : selected 0=init.parents := by simp [selected]
  have rzero : reserve 0=0 := by decide
  have contact_zero (J : Ideal Ambient) (mem : J∈init.parents) : Native J (reserve 0+1) (Q 0) := by
    intro w hw
    have hz : w.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hz]
    exact (init.parent_geom J mem).2.2.2.2
  have sel_pass (i : Fin 17) (J : Ideal Ambient) (mem : J∈selected i) :
      Native J (reserve i+1) (Q i) := by
    by_cases zi : i = 0
    · subst i; exact contact_zero J (first ▸ mem)
    · exact pass i J (by simpa only [selected,ite_eq_right zi] using mem)
  have sel_bound (i : Fin 17) (c : Fin 4) :
      (reserve i+1)*mass (selected i) c≤pairCap (primeShape rect) (bank rect i).shape c := by
    by_cases zi : i = 0
    · subst i
      rw [rzero, Nat.zero_add, first, one_mul]
      exact K1_14_2_2.mass_mono (subset_union_right (s₁:=init.rankExit) (s₂:=init.parents)) c
        |>.trans (init.fits c)
    · simpa only [selected,ite_eq_right zi] using bound i c
  let kept (n : ℕ) := init.parents.filter (fun J=>∀ i : Fin 17,i.val<n → J∈selected i)
  have spec {J n} : J∈kept n ↔ J∈init.parents ∧ ∀ i : Fin 17,i.val<n → J∈selected i := mem_filter
  refine ⟨kept,?_,?_,?_,?_,?_,?_⟩
  · ext J; simp [kept]
  · ext J
    refine ⟨fun h=>(spec.mp h).1,fun h=>spec.mpr ⟨h,?_⟩⟩
    intro i hi
    have zi : i = 0 := Fin.ext (by omega)
    subst i
    exact first.symm ▸ h
  · intro n m h J mem
    exact spec.mpr ⟨(spec.mp mem).1,fun i hi=>(spec.mp mem).2 i (hi.trans_le h)⟩
  · intro i n hi J mem
    exact sel_pass i J ((spec.mp mem).2 i hi)
  · intro i n hi c
    have hsub : kept n⊆selected i := fun _ mem=>(spec.mp mem).2 i hi
    exact (Nat.mul_le_mul_left _ (K1_14_2_2.mass_mono hsub c)).trans (sel_bound i c)
  · intro i J prev lost
    obtain ⟨root,prior⟩ := spec.mp prev
    have fail : J∉selected i := by
      intro pass
      apply lost (spec.mpr ⟨root,?_⟩)
      intro j hj
      by_cases same : j=i
      · exact same ▸ pass
      · apply prior
        have diff : j.val≠i.val := fun h=>same (Fin.ext h)
        omega
    have nz : i ≠ 0 := by
      intro z
      subst i
      exact fail (first.symm ▸ root)
    obtain ⟨C,cap,proper,zero⟩ := cut i J root (by simpa only [selected,ite_eq_right nz] using fail)
    exact ⟨C,cap,proper,fun γ hγ=>zero _ _ (contact i γ hγ)⟩
structure Run {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (G : Jet) where
  rect : Fin 4
  row : Fin 17→Jet
  row_mem : ∀ i,row i∈evaluated Crt (word M) (bank rect i).shape (cutoff M.overhead.toNat rect i)
  avoids : ∀ i,¬G∣row i
  initial : Initial F G (row 0) rect
  kept : ℕ→Finset (Ideal Ambient)
  start : kept 0=initial.parents
  intro_pass : kept 1=initial.parents
  antitone : Antitone kept
  passed : ∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve i+1) (row i)
  cap : ∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
    (reserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c
  cut : ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
    ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0
theorem prepare {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2359≤M.overhead.toNat) (hi : M.overhead.toNat≤33579)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : PrefixRows.Common
      (evaluated Crt (word M) HelperSource.helperBank.shape (HelperSource.helperCutoff M.overhead.toNat)) G) :
    Nonempty (Run F Crt G) := by
  obtain ⟨rect,linear,jCap,uCap,rows⟩ := RescueSource.exceptional_rows Crt (word M) lo hi
    common.1 common.2.2.1 common.2.1 common.2.2.2
  choose Q inside avoid using rows
  have capsG : RowCaps G (primeShape rect) :=
    (rowCaps_iff G _).mpr ⟨jCap,linear.le,uCap⟩
  have caps (i : Fin 17) : RowCaps (Q i) (bank rect i).shape :=
    evaluated_shape Crt (word M) (inside i)
  have contact (i : Fin 17) (γ : K) (hγ : γ∈Γ) :
      Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (Q i) :=
    contact_at_mark F Crt noPole residues (inside i) (RescueSource.cutoff_fit lo hi rect i) γ hγ
  obtain ⟨ini⟩ := initial_cover F common.1 (avoid 0) capsG (caps 0)
    (fun γ hγ=>zero_of_contact (contact 0 γ hγ))
  obtain ⟨kept,start,intro_pass,anti,passed,cap,cut⟩ :=
    history_from_initial common.1 capsG Q ini avoid caps contact
  exact ⟨⟨rect,Q,inside,avoid,ini,kept,start,intro_pass,anti,passed,cap,cut⟩⟩
theorem Run.parent_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈R.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet (R.row 0)∈J :=
  R.initial.parent_geom J (R.start ▸ R.antitone (Nat.zero_le n) mem)
#print axioms prepare
#print axioms history_from_initial
end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryHistory

-- merged module R6960RescueGeometryCuts
section Merged_R6960RescueGeometryCuts
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt atX seedEmbedding)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom eval_toJet CoordinateRing)
open K1_14_2_2 (RowCaps Active dual mass sectionDegree CutCover weight dot emptyCut joinCuts
  joinCuts_cost sum_dot)
open K1_14_2_2_3 K1_14_2_2_7
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open RescueSource (bank reserve)
open scoped Classical
open HighCore82258_3 (envelope_caps)
open K1_14_2_2_7 (seed_value_eq)
def terminalShape : Shape := ⟨4500,6286,1329,748778⟩
def terminalCutoff : ℕ := terminalShape.m*179818-1
def TerminalFits (s : Shape) : Prop :=
  0<s.m ∧ s.B≤terminalShape.B ∧ s.J≤terminalShape.J ∧ s.U≤terminalShape.U
def TerminalPass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (J : Ideal Ambient) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179818-1),toJet P∈J

/-- A parent that fails any terminal bank provides a proper row inside
the single envelope used by the geometric cut bill. -/
theorem terminal_failure {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L)
    {J : Ideal Ambient} (failed : ¬ TerminalPass Crt w J) :
    ∃ (s : Shape) (P : Jet), 0<s.m ∧ P∈evaluated Crt w s (s.m*179818-1) ∧
      RowCaps P terminalShape ∧ toJet P∉J := by
  classical
  unfold TerminalPass at failed
  push Not at failed
  obtain ⟨s,⟨sm,sb,sj,su⟩,P,inside,proper⟩ := failed
  refine ⟨s,P,sm,inside,?_,proper⟩
  intro j i nz
  obtain ⟨b,v,u⟩ := evaluated_shape Crt w inside j i nz
  exact ⟨b.trans sb,v.trans sj,u.trans su⟩

def Run.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    Finset (Ideal Ambient) :=
  (R.kept 17).filter (TerminalPass Crt (word M))
def Run.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  if n<17 then R.kept (n+1) else R.final
def Run.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  R.live n \ R.live (n+1)
theorem Run.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) : R.live (i+1)⊆R.live i := by
  by_cases hn : i+1<17
  · simp only [Run.live,ite_eq_left hi,ite_eq_left hn]
    exact R.antitone (by omega)
  · have eq : i+1=17 := by omega
    rw [Run.live,Run.live,ite_eq_right hn,ite_eq_left hi,eq]
    exact filter_subset _ _
theorem Run.live_active {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.live i) : Active J := by
  rw [Run.live,ite_eq_left hi] at mem
  exact (R.parent_geom mem).1
theorem Run.live_start {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    R.live 0=R.initial.parents := by
  rw [Run.live,ite_eq_left (by decide : 0<17)]
  exact R.intro_pass
def rescueStage (rect : Fin 4) (i : Fin 17) : P1_7.Stage :=
  ⟨reserve i,⟨HelperPrefix.timesShape (reserve i+1) (primeShape rect),0,0⟩,bank rect i⟩
def cutShape (rect : Fin 4) (i : ℕ) : Shape :=
  if hi : i+1<17 then HighCore82258_3.envelope (rescueStage rect ⟨i+1,hi⟩) else terminalShape
theorem cutShape_fit (rect : Fin 4) (i : ℕ) : (cutShape rect i).J≤(cutShape rect i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide
theorem Run.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.lost i) :
    ∃ C : Jet, RowCaps C (cutShape R.rect i) ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Run.live,ite_eq_left hi] at prev
  by_cases hn : i+1<17
  · let j : Fin 17 := ⟨i+1,hn⟩
    rw [Run.live,ite_eq_left hn] at lost
    obtain ⟨C,cap,proper,zero⟩ := R.cut j J prev lost
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    apply envelope_caps (s:=rescueStage R.rect j)
    · exact Nat.mul_le_mul_left _ (prime_shape_fit R.rect)
    · exact (RescueSource.shape_guards R.rect j).2.1
    · exact Or.inr cap
  · have eq : i+1=17 := by omega
    rw [Run.live,ite_eq_right hn] at lost
    have hf : ¬ TerminalPass Crt (word M) J := fun pass =>
      lost (mem_filter.mpr ⟨eq ▸ prev,pass⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := terminal_failure Crt (word M) hf
    rw [cutShape,dite_eq_right hn]
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ
    apply zero_of_contact (r:=0)
    exact contact_at_mark F Crt noPole residues inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179818)) (by decide : 0<1)) γ hγ
private theorem mark_on_cut {J : Ideal Ambient} {P : Jet} {z : K} {S : (Polynomial K)}
    (on : OnJet J z S) (zero : jetAt P z S=0) :
    ∃ Q∈cutComponents J P,OnJet Q z S := by
  let e := jetMarkHom z S
  have incl : J ⊔ Ideal.span {toJet P} ≤ RingHom.ker e :=
    sup_le on ((Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr ((eval_toJet _ _ _).trans zero)))
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q,minimal,mark⟩ := Ideal.exists_minimalPrimes_le incl
  exact ⟨Q,Ideal.mem_minimalPrimesFinset.mpr minimal,mark⟩
theorem proper_cut {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (s : Shape) {J : Ideal Ambient} {P : Jet} (sl : s.J≤s.B) (act : Active J)
    (cap : RowCaps P s) (proper : toJet P∉J) (zero : ∀ γ∈Γ,jetAt P (M.label γ) (F.scalar γ)=0) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight s fee) (sectionDegree J)) ∧
      ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  let marked (Q : Ideal Ambient) := Γ.filter (OnMark F Q)
  let direct := (constantComponents J P).biUnion marked
  have card : direct.card≤(constantComponents J P).card := by
    have single (Q : Ideal Ambient) (mem : Q∈constantComponents J P) : (marked Q).card≤1 := by
      obtain ⟨comp,seed⟩ := mem_filter.mp mem
      let _ : Q.IsPrime := (cutComponent_curve act proper comp).1
      apply card_le_one.mpr
      intro γ hγ δ hδ
      apply label_injective M
      apply seedEmbedding.injective
      apply (algebraMap K1_14.FX (CoordinateRing Q)).injective
      exact (seed_value_eq seed (mem_filter.mp hγ).2).trans (seed_value_eq seed (mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q∈constantComponents J P,(marked Q).card := card_biUnion_le
      _ ≤ ∑ _∈constantComponents J P,1 := sum_le_sum single
      _ = _ := by simp
  let C : CutCover := ⟨direct,movingComponents J P,by
    intro Q hQ
    obtain ⟨comp,moving⟩ := mem_filter.mp hQ
    obtain ⟨prime,dim⟩ := cutComponent_curve act proper comp
    exact ⟨prime,dim,K1_14_2_2_7_1.proof Q prime dim moving⟩⟩
  refine ⟨C,?_,?_⟩
  · intro fee
    fin_cases fee
    · exact P0_10R.Bridge.cut_seed_mass s J P sl act cap proper
    · exact P0_10R.Bridge.cut_ordinate_mass s J P sl act cap proper
    · exact card.trans (P0_10R.Bridge.cut_constant_count s J P sl act cap proper)
  · intro γ hγ on
    obtain ⟨Q,comp,mark⟩ := mark_on_cut on (zero γ hγ)
    by_cases c : ConstantSeed Q
    · exact Or.inl (mem_biUnion.mpr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mem_filter.mpr ⟨hγ,mark⟩⟩)
    · exact Or.inr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mark⟩
theorem Run.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<17) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈R.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := R.marked_cutter noPole residues hi mem
    exact proper_cut F _ (cutShape_fit _ _) (R.live_active hi (mem_sdiff.mp mem).1) cap proper zero
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈R.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈R.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark F Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (R.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩
theorem Run.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈R.final ∨ ∃ i<17,J∈R.lost i := by
  by_cases h : ∃ i<17,J∈R.lost i
  · exact Or.inr h
  · have live : ∀ n≤17,J∈R.live n := by
      intro n hn
      induction n with
      | zero => exact R.live_start.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Run.live] using live 17 le_rfl)
def OnSurface {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (q : Surface) (γ : K) : Prop :=
  ∀ P∈q.asIdeal,jetAt P (M.label γ) (F.scalar γ)=0
def SurfacePass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (q : Surface) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179818-1),P∈q.asIdeal

theorem SurfacePass.original {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {w : I→L}
    {q : Surface} (pass : SurfacePass Crt w q) :
    ∀ P∈evaluated Crt w terminalShape terminalCutoff,P∈q.asIdeal :=
  pass terminalShape ⟨by decide,le_rfl,le_rfl,le_rfl⟩
theorem Run.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈R.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  let getGeom (J : R.final) := R.parent_geom (mem_filter.mp J.property).1
  let surface (J : R.final) := surfaceOf J.val (getGeom J).1.prime
  let S := R.final.attach.image surface
  refine ⟨S,?_,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩:=mem_image.mp hq
    exact ⟨J.val,J.property,rfl⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : R.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Run.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=R.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩
#print axioms Run.cutCover
#print axioms Run.retained_or_lost
#print axioms Run.terminal_surfaces
end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryCuts

-- merged module R6960RescueGeometryBills
section Merged_R6960RescueGeometryBills
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (Shape Jet atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass weight dot CutCover emptyCut mass_mono)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open RescueSource (bank reserve)
open P1_7_4 (Mass massQ dotQ massQ_mono weightedBill bill_bound)
open scoped Classical
def initialMass (rect : Fin 4) : Mass := fun k => initialCap rect k
def history (rect : Fin 4) : ℕ → Mass
  | 0 => initialMass rect
  | n+1 => fun k =>
    if hn : n+1<17 then
      let i : Fin 17 := ⟨n+1,hn⟩
      min (history rect n k)
        ((pairCap (primeShape rect) (bank rect i).shape k : ℚ)/(reserve i+1))
    else history rect n k
theorem Run.initial_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) (k : Fin 4) : massQ (R.kept n) k ≤ initialMass R.rect k := by
  have sub : R.kept n ⊆ R.initial.parents := by
    simpa only [R.start] using (R.antitone (Nat.zero_le n) : R.kept n⊆R.kept 0)
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono (sub.trans subset_union_right) k).trans (R.initial.fits k))
theorem Run.history_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i n : ℕ} (hi : i<17) (prior : i<n) (k : Fin 4) :
    massQ (R.kept n) k ≤ history R.rect i k := by
  induction i with
  | zero => exact R.initial_cap n k
  | succ i ih =>
    simp only [history,dite_eq_left hi]
    apply le_min (ih (by omega) (by omega))
    let j : Fin 17 := ⟨i+1,hi⟩
    change massQ (R.kept n) k ≤ (pairCap (primeShape R.rect) (bank R.rect j).shape k : ℚ) / (reserve j+1)
    have pos : (0 : ℚ)<reserve j+1 := by positivity
    apply (le_div_iff₀ pos).mpr
    have bound := R.cap j n prior k
    rw [Nat.mul_comm] at bound
    unfold massQ
    exact_mod_cast bound
theorem Run.live_history {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ history R.rect i k := by
  rw [Run.live,ite_eq_left hi]
  exact R.history_cap hi (Nat.lt_succ_self _) k
theorem Run.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ initialMass R.rect k := by
  rw [Run.live,ite_eq_left hi]
  exact R.initial_cap _ k
def cutWeight (rect : Fin 4) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape rect i) fee k
def seedLimit (rect : Fin 4) : ℚ := weightedBill 17 (cutWeight rect 0) (history rect)
def pointLimit (rect : Fin 4) : ℚ := weightedBill 17 (cutWeight rect 2) (fun _ => initialMass rect)
def initialSeedLimit (rect : Fin 4) : ℕ := (K1.p+1)*initialCap rect 2+initialCap rect 3
theorem seed_limit_small (rect : Fin 4) : seedLimit rect < (K1.p : ℚ) := by
  fin_cases rect <;> decide +kernel
theorem point_limit_bound (rect : Fin 4) : pointLimit rect ≤ 206700957314 := by
  fin_cases rect <;> decide +kernel
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>ini.seeds.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>atX (F.scalar γ)∈ini.ordinates)
theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) :
    ini.seedMarks.card ≤ initialSeedLimit rect := by
  have bound := K1_14_3.seed_count (T := ini.seedMarks) (label_injective M).injOn ini.seeds
    (ini.seed_degree.trans_lt (initial_small rect 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_degree) ini.seed_points)
theorem Initial.ordinate_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) :
    ini.ordinateMarks.card ≤ initialCap rect 0 := by
  refine (card_le_card_of_injOn (fun γ=>atX (F.scalar γ)) (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_card
  intro γ hγ δ hδ eq
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (K1_14_3.scalar_atX_injective eq)
structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) where
  cover : ℕ→CutCover
  cost : ∀ i<17,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))
  covers : ∀ i<17,∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark F Q γ
theorem Run.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks R) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<17 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    by_cases hi : i<17
    · obtain ⟨C,cap,cover⟩ := R.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩
theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) {i : ℕ} (hi : i<17) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight R.rect fee i) (massQ (R.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound
theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (∑ i∈range 17,((C.cover i).cost 0 : ℚ))≤seedLimit R.rect :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_history hi))
def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : Finset K := (range 17).biUnion fun i=>(C.cover i).direct
theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (C.pointMarks.card : ℚ) ≤ pointLimit R.rect := by
  calc
    _ ≤ ∑ i∈range 17,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 17,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 17,dotQ (cutWeight R.rect 2 i) (massQ (R.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_initial hi)
def beforeCuts (first : Mass) (rest : ℕ → Mass) : ℕ → Mass
  | 0 => first
  | i+1 => rest i
private def Run.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit∪R.initial.parents
  | i+1 => R.live i
private def Run.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i+1 => R.lost i
theorem Run.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 18) (massQ R.final) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) := by
  have bill := P1_7_4.bill_bound_with_final 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect))
    R.jointLive R.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    have final : R.jointLive 18 = R.final := by simp [Run.jointLive,Run.live]
    simpa only [beforeCuts,Run.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Run.jointLive,R.live_start] using
        (subset_union_right : R.initial.parents⊆ R.initial.rankExit∪R.initial.parents)
    | succ i => exact R.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Run.jointLive,R.live_start]
      exact fun h=>(disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (R.initial.fits k)
    | succ i => exact R.live_history (by omega) k
theorem Run.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 18 (beforeCuts rank cut) R.final)).trans
    (R.joint_bill_with_final rank cut)

theorem inventory {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2359≤M.overhead.toNat) (hi : M.overhead.toNat≤33579)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : PrefixRows.Common
      (K1_14_1.evaluated Crt (word M) HelperSource.helperBank.shape (HelperSource.helperCutoff M.overhead.toNat)) G) :
    ∃ (R : Run F Crt G) (C : CutBooks R) (S : Finset Surface),
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
        γ∈R.initial.seedMarks ∨ γ∈R.initial.ordinateMarks ∨
        (∃ J∈R.initial.rankExit,OnMark F J γ) ∨ γ∈C.pointMarks ∨
        (∃ i<17,∃ Q∈(C.cover i).curves,OnMark F Q γ) ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := prepare F Crt lo hi noPole residues common
  obtain ⟨C⟩ := R.cutBooks noPole residues
  obtain ⟨S,geom,pass⟩ := R.terminal_surfaces
  refine ⟨R,C,S,geom,?_⟩
  intro γ hγ zero
  rcases R.initial.covers γ hγ zero with seed | ordinate | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_filter.mpr ⟨hγ,seed⟩)
  · exact Or.inr (Or.inl (mem_filter.mpr ⟨hγ,ordinate⟩))
  · exact Or.inr (Or.inr (Or.inl rank))
  · rcases R.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pass γ hγ ⟨J,final,on⟩)))))
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | curve
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,hi,curve⟩))))
#print axioms inventory
#print axioms Run.joint_bill
#print axioms seed_limit_small
#print axioms CutBooks.point_bill
end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryBills

end Merged6967_R6960RescueGeometryBills

section Merged6967_R6966ProofPadeFiltered
set_option Elab.async false



set_option Elab.async false

namespace Research6966.PadeFiltered
open Polynomial Finset Module
open K1_14 (Jet Shape Seeds FX L)
open K1_14_3 (SeedField SeedClosure fibreRow Parent Surface)
open K1_14_1 (PoleData CRTLift jetConstant)
open K1_14_1_4 (specialized rawPosition doubleMap substitute)
open PadeRank (Plane box positions)
open PadeChart (chart window)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

private abbrev E:=SeedClosure

theorem base_change {A K M:Type*} [CommSemiring A] [Field K] [Field M]
    (g:A→+*K) (f:K→+*M) (a b u d:K) :
    (chart (f a) (f b) (f u) (f d)).toRingHom.comp (doubleMap (f.comp g)) =
    (doubleMap f).comp (substitute g (C (C a*Polynomial.X+C b))
      (C (C a)*Polynomial.X+C (C u*Polynomial.X+C d))) := by
  change (substitute (RingHom.id M) _ _).comp _ = _
  rw [K1_14_1_4.map_substitute,K1_14_1_4.substitute_map]
  simp only [RingHom.id_comp,doubleMap,coe_mapRingHom,Polynomial.map_C,Polynomial.map_X,map_add,map_mul]

/-- The two-dimensional physical window, including its partial top diagonal. -/
def physicalWindow (B J step W:ℕ) : Finset (ℕ×ℕ) :=
  (positions (B+1) (J+1)).filter (fun t=>step*t.2+(step-1)*t.1≤W)

private theorem compatibility {h} {D:PoleData h} (Crt:CRTLift D) :
    ∃ a b u d:E, a≠0 ∧ ∀ P:Jet,chart a b u d (fibreRow P)=
      doubleMap (algebraMap SeedField E) (specialized Crt P) := by
  obtain ⟨a,b,u,d,ne,form⟩:=K1_14_1_4.specialized_affine_form Crt
  let f:=algebraMap SeedField E
  refine ⟨f a,f b,f u,f d,(map_ne_zero f).mpr ne,?_⟩
  intro P
  change (chart _ _ _ _).toRingHom.comp (doubleMap (f.comp (algebraMap Seeds SeedField))) P =
    (doubleMap f).comp (specialized Crt).toRingHom P
  rw [form,base_change]

private theorem inject_chart (a b u d:E) (ne:a≠0) : Function.Injective (chart a b u d) := by
  apply (injective_iff_map_eq_zero (chart a b u d).toRingHom).mpr
  intro P hz
  by_contra pn
  exact (K1_14_1_4.affine_leading (RingHom.id E) Function.injective_id ne
    (b:=b) (C u*Polynomial.X+C d) pn).2.2 hz

private theorem window_rows {h W:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U:Fin 2→ℕ) (a b₀ u d:E)
    (commute:∀ P:Jet,chart a b₀ u d (fibreRow P)=doubleMap (algebraMap SeedField E) (specialized Crt P)) :
    PadeBankRank.rows Crt word s W U ≤ (window E (physicalWindow s.B s.J (131071-h) W)).comap
      (chart a b₀ u d).toLinearMap := by
  let H:=PadeBankRank.rows Crt word s W U
  apply Submodule.span_le.mpr
  rintro _ ⟨P,hP,rfl⟩ j i outside
  have inH:PadeBankRank.fibre P∈H:=Submodule.subset_span ⟨P,hP,rfl⟩
  have after:=PadeChart.chart_box a b₀ u d _ _ (PadeBankRank.rows_shape Crt word s W U inH)
  by_cases pos:(j,i)∈positions (s.B+1) (s.J+1)
  · have heavy:W<(131071-h)*i+(131071-h-1)*j := by
      by_contra! valid
      exact outside (mem_filter.mpr ⟨pos,valid⟩)
    have zero:=P0_10_1.rawPosition_zero hp hl Crt word
      (KoalaRect.rectEvaluated_le Crt word s W U hP) j i heavy
    change ((chart a b₀ u d (fibreRow P)).coeff j).coeff i=0
    rw [commute]
    simp only [doubleMap,coe_mapRingHom,coeff_map]
    change algebraMap SeedField E (rawPosition Crt j i P)=0
    rw [zero,map_zero]
  · exact after j i pos

/-- A normalized physical row fits the same total-degree cap even in
native coordinates over the algebraic closure. The full triangular box
is invariant under the invertible affine chart. -/
theorem rows_weighted_degree {h W:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U:Fin 2→ℕ) :
    PadeBankRank.rows Crt word s W U ≤
      box E (min s.B ((W+s.J)/(131071-h))+1) (s.J+1) := by
  classical
  obtain ⟨a,b,u,d,ne,commute⟩:=compatibility Crt
  let B:=min s.B ((W+s.J)/(131071-h))+1
  let M:=box E B (s.J+1)
  let T:Plane E→ₗ[E]Plane E:=(chart a b u d).toLinearMap
  have preserve:∀ Q∈M,T Q∈M:=fun Q hQ=>PadeChart.chart_box a b u d _ _ hQ
  let F:↥M→ₗ[E]M := T.restrict preserve
  have inj:Function.Injective F:=fun x y eq=>Subtype.ext (inject_chart a b u d ne (congrArg Subtype.val eq))
  have onto:Function.Surjective F:=LinearMap.surjective_of_injective inj
  intro Q hQ
  have phys:=window_rows hp hl Crt word s U a b u d commute hQ
  have fit:T Q∈M := by
    intro j i outside
    apply phys j i
    intro yes
    obtain ⟨pos,weight⟩:=mem_filter.mp yes
    have pos': j≤s.J ∧ i+j≤s.B := by simp [positions] at pos;omega
    change (131071-h)*i+(131071-h-1)*j≤W at weight
    have sum:(i+j)*(131071-h)≤W+j := by
      have off: (131071-h-1)*j+j = (131071-h)*j := by rw [←Nat.succ_mul];congr 1;omega
      rw [Nat.add_mul,Nat.mul_comm i _,Nat.mul_comm j _];omega
    have raw:i+j≤(W+s.J)/(131071-h) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    apply outside
    simp [positions,B];omega
  obtain ⟨R,eq⟩:=onto ⟨T Q,fit⟩
  have id:R.val=Q:=inject_chart a b u d ne (congrArg Subtype.val eq)
  exact id ▸ R.property

/-- Exact rectangular-bank bound for a graph on retained sheets. All support,
seed-axis and order hypotheses are obtained here from the benchmark's bank. -/
theorem graph_rank {h A W r b:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    (innerShape:b≤s.B) (innerWeight:(131071-h)*b≤W)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    (ys:Finset E) (v:E→E) {G:Pade.Row E} (gp:G.primitive)
    (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ G.err v y=0) :
    finrank FX (KoalaRect.rectEvaluated Crt word s W U) +
      PadeRank.gain G.graphDegree ys.card (r+1) (b+1) (s.J+1)*KoalaRect.area U ≤
      (physicalWindow s.B s.J (131071-h) W).card*KoalaRect.area U := by
  classical
  obtain ⟨a,b₀,u,d,ne,commute⟩:=compatibility Crt
  let H:=PadeBankRank.rows Crt word s W U
  let S:=physicalWindow s.B s.J (131071-h) W
  let T:=chart a b₀ u d
  have inner:box E (b+1) (s.J+1) ≤ (window E S).comap T.toLinearMap := by
    intro Q bound j i outside
    have after:=PadeChart.chart_box a b₀ u d _ _ bound
    apply after j i
    intro hit
    have hi:i+j≤b ∧ j≤s.J := by simp [positions] at hit;omega
    apply outside
    have wt := Nat.mul_le_mul_left (131071-h) hi.1
    have lt:=Nat.mul_le_mul_right j (Nat.sub_le (131071-h) 1)
    rw [Nat.mul_add] at wt
    exact Finset.mem_filter.mpr ⟨by simp [positions];omega,by dsimp only;omega⟩
  have bank:=window_rows hp hl Crt word s U a b₀ u d commute (W:=W)
  have dim := PadeChart.filtered_gain gp ys v (fun y hy=>(sheets y hy).2)
    (r+1) (b+1) (s.J+1) S H T.toLinearMap (inject_chart _ _ _ _ ne) bank inner (by
      intro R mem y hy
      exact PadeBankRank.rows_contact Crt word U fits small cut geo pass (sheets y hy).1 R mem)
  have mult:=Nat.mul_le_mul_right (KoalaRect.area U) dim
  rw [Nat.add_mul] at mult
  exact (Nat.add_le_add_right (PadeBankRank.bank_dimension Crt word s W U) _).trans mult

#print axioms rows_weighted_degree
#print axioms graph_rank

/-- The exact rounded graph power is forced on the evaluated bank at
its physical cutoff before applying the integral divisibility theorem. -/
theorem forced_bank_layers {h W A r:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    (ys:Finset E) (v:E→E) {G:Pade.Row E} (gp:G.primitive)
    (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ G.err v y=0)
    (many:2*G.graphDegree-1<ys.card) (b:ℕ) (bound:min s.B ((W+s.J)/(131071-h))≤b)
    {Q:Plane E} (mem:Q∈PadeBankRank.rows Crt word s W U) :
    G.polynomial^(Pade.layers G.graphDegree ys.card b s.J (r+1))∣Q := by
  by_cases zero:Q=0
  · rw [zero];exact dvd_zero _
  have boxMem:=rows_weighted_degree hp hl Crt word s U mem
  obtain ⟨degree,slope⟩:=(PadeRank.mem_box zero).mp boxMem
  apply Pade.forced_layers gp ys v (fun y hy=>(sheets y hy).2) Q _ _ _
    ((Nat.le_of_lt_succ degree).trans bound) (Nat.le_of_lt_succ slope) _ many
  intro y hy
  exact PadeBankRank.rows_contact Crt word U fits small cut geo pass (sheets y hy).1 Q mem

#print axioms forced_bank_layers

end
end Research6966.PadeFiltered

end Merged6967_R6966ProofPadeFiltered
