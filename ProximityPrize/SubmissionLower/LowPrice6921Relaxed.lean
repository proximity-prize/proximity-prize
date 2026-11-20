import ProximityPrize.SubmissionLower.LowPrice6921Physical

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace LowPrice6921

noncomputable section

open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators

/-- The cutter's true weight is used only to integrate its equation in positive characteristic. -/
def RelaxedProperCut (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) ⟨4012, 1650, 550⟩ ∧
    TrueWeightLE Q (K1.p - 4) ∧ ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l

structure RelaxedCutInput (Γ : Finset K) (s : K → K[X]) (f Q : Row 4) (l : ℕ) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ 133671
  small : SmallFactor f
  onFactor : ∀ γ ∈ Γ, OnFactor f (extend (s γ))
  positive : 0 < l
  proper : ¬ f ∣ Q
  box : InBox (shape Q) ⟨4012, 1650, 550⟩
  weight : TrueWeightLE Q (K1.p - 4)
  order : ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l

/-- Low-weight, failed-chart and noninvariant branches of the physical cut. -/
private def AuxGeometry : Prop :=
  ∀ Γ s f Q l, RelaxedCutInput Γ s f Q l →
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧
      (∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * C.total ≤ auxCurves32 (shape f) ∧
      32 * (B.card + C.n) ≤ 2 * auxPoints32 (shape f)

/-- The joint sparse budget for multiple membership-test curves and
simple curves properly cut by the next test. -/
private def MixedGeometry : Prop :=
  ∀ Γ s f Q l, RelaxedCutInput Γ s f Q l →
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧ (∀ i, 0 < C.degree i) ∧
      (∀ γ ∈ Γ, MixedMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * l * (2 * C.total + B.card) ≤ surfaceNumerator32 (shape f).chamber cutterBox

/-- Continued families. A simple invariant curve can promote to a
surface when the original abscissa is allowed to vary. -/
private def ContinuedGeometry : Prop :=
  ∀ Γ s f Q l, RelaxedCutInput Γ s f Q l →
    ∃ C D : Pieces Γ,
      C.curves s ∧ D.surfaces s ∧ (∀ i, 0 < C.degree i) ∧ (∀ i, 0 < D.degree i) ∧
      (∀ γ ∈ Γ, ContinuedMark f Q l (extend (s γ)) → γ ∈ C.union ∪ D.union) ∧
      l * C.total ≤ membershipDegree (shape f) ∧
      2 * D.total ≤ 133671 * (shape f).b * cutterBox.b

namespace Aux
open K1_13_6_1

private theorem factor_mem {f Q : Row 4} {surface : Ideal GeoJets}
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) :
    toGeneric f ∈ surface :=
  hZ.le (Ideal.subset_span (Set.mem_insert _ _))

private theorem one_surface (h1 : K1_13_6_1.c1) (h2 : K1_13_6_1.c2) (h3 : K1_13_6_1.c3)
    {Γ s f Q l surface} (input : RelaxedCutInput Γ s f Q l)
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) (active : HasMark Γ s surface) :
    ∃ P, SurfaceCut f Q surface P ∧
      ∀ γ ∈ Γ, surface ≤ markIdeal (extend (s γ)) →
        ¬ HighMark f Q l (extend (s γ)) → atJet P (extend (s γ)) = 0 := by
  have hbox : InBox (shape Q) cutterBox :=
    ⟨input.box.1.trans (by decide), input.box.2⟩
  obtain ⟨v, hv, hvmax, hlen, hlow⟩ := h2 f Q l surface hZ input.small input.proper hbox
  by_cases low : v < l
  · obtain ⟨P, hP, hPb, hvan⟩ := hlow low
    have hPb' : InBox (shape P) (cutterBox.plus ((anchorBox f).scale 0)) := by
      simpa [InBox, Shape.plus, Shape.scale] using hPb
    exact ⟨P, ⟨hZ, v, 0, hv, hlen, Or.inl rfl, hP,
      box_cutter_charge hPb' (Nat.zero_le _)⟩,
      fun γ hγ _ _ => hvan _ (input.order γ hγ)⟩
  obtain ⟨γ₀, hγ₀, hmark₀⟩ := active
  obtain ⟨r, hr, hrBox⟩ := h1 f surface (extend (s γ₀)) input.small
    (input.onFactor γ₀ hγ₀) (factor_mem hZ) hmark₀
  let g := (separant^[r]) f
  have on_g : ∀ S, surface ≤ markIdeal S → atJet g S = 0 :=
    fun S hS => mem_markIdeal.mp (hS (hr.2.1 r le_rfl))
  have high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hZ.isPrime := by
    rw [hlen]
    exact_mod_cast Nat.le_of_not_gt low
  by_cases inv : Invariant g surface
  · have hsep : InBox (shape (separant g)) ((anchorBox f).scale 1) := by
      simpa [InBox, Shape.scale] using hrBox
    refine ⟨separant g, ⟨hZ, v, 0, hv, hlen, Or.inl rfl, hr.2.2,
      box_charge hsep (by omega)⟩, ?_⟩
    intro γ _ hpoint hnot
    by_contra hregular
    exact hnot ⟨surface, r, hZ, high, hpoint, hr, hregular, inv⟩
  rcases h3 f Q surface hZ v r input.small input.proper hbox hv hvmax hlen hr inv with
    ⟨_, hP, hPb⟩ | ⟨hrPos, w, hw, hP, hPb⟩
  · exact ⟨tangentCut g Q v, ⟨hZ, v, 0, hv, hlen, Or.inl rfl, hP,
      box_cutter_charge hPb (by omega)⟩,
      fun γ hγ hpoint _ => tangentCut_vanishes g Q _ v (on_g _ hpoint)
        (orderAt_vanishes input.positive (input.order γ hγ))⟩
  · have hPb' : InBox (shape (tangentCut g f w)) ((anchorBox f).scale (2*w+1)) := by
      simpa [InBox, Shape.plus, Shape.scale, Nat.add_mul, Nat.add_comm] using hPb
    exact ⟨tangentCut g f w, ⟨hZ, v, w, hv, hlen, Or.inr ⟨r, hrPos, hr.1, hw⟩, hP,
      box_charge hPb' (by omega)⟩,
      fun γ hγ hpoint _ => tangentCut_vanishes g f _ w (on_g _ hpoint)
        (input.onFactor γ hγ).1⟩

private theorem assemble {Γ s f Q l} (curves : Finset (Ideal GeoJets))
    (marks : ∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) →
      ∃ C ∈ curves, C ≤ markIdeal (extend (s γ)))
    (recover : ∀ C : curves, ∃ (A B : Finset K) (d : ℕ),
      A ⊆ Γ ∧ CurveSections A s d ∧
      (∀ γ ∈ Γ, C.val ≤ markIdeal (extend (s γ)) → γ ∈ A ∪ B) ∧
      6*d ≤ sectionDegree C.val ((chart taylorLength (anchorBox f)).scale 6) ∧
      6*B.card ≤ sectionDegree C.val ((anchorBox f).scale 6) ∧
      6 ≤ sectionDegree C.val ((anchorBox f).scale 6))
    (hcurves : 32 * (∑ C ∈ curves,
      sectionDegree C ((chart taylorLength (anchorBox f)).scale 6)) ≤
      6 * auxCurves32 (shape f))
    (hpoints : 32 * (∑ C ∈ curves, sectionDegree C ((anchorBox f).scale 6)) ≤
      6 * auxPoints32 (shape f)) :
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧
      (∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * C.total ≤ auxCurves32 (shape f) ∧
      32 * (B.card + C.n) ≤ 2 * auxPoints32 (shape f) := by
  classical
  choose A B d hd using recover
  let e := curves.equivFin.symm
  let cover : Pieces Γ :=
    ⟨curves.card, fun i => A (e i), fun i => (hd (e i)).1, fun i => d (e i)⟩
  let points := curves.attach.biUnion B
  refine ⟨cover, points, fun i => (hd (e i)).2.1, ?_, ?_, ?_⟩
  · intro γ hγ hn
    obtain ⟨C, hC, hm⟩ := marks γ hγ hn
    let i := curves.equivFin ⟨C, hC⟩
    have hi : e i = ⟨C, hC⟩ := e.apply_symm_apply ⟨C, hC⟩
    rcases Finset.mem_union.mp ((hd ⟨C, hC⟩).2.2.1 γ hγ hm) with ha | hb
    · exact Finset.mem_union_left _ <| Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, by change γ ∈ A (e i); rwa [hi]⟩
    · exact Finset.mem_union_right _ <| Finset.mem_biUnion.mpr
        ⟨⟨C, hC⟩, Finset.mem_attach _ _, hb⟩
  · let degree := fun C => sectionDegree C ((chart taylorLength (anchorBox f)).scale 6)
    have hsum : 6 * cover.total ≤ ∑ C ∈ curves, degree C := by
      change 6 * (∑ i, d (e i)) ≤ _
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ i, degree (e i).val := Finset.sum_le_sum fun i _ => (hd (e i)).2.2.2.1
        _ = _ := by
          rw [← Finset.sum_attach curves degree]
          exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    change 32 * (∑ C ∈ curves, degree C) ≤ _ at hcurves
    omega
  · let degree := fun C => sectionDegree C ((anchorBox f).scale 6)
    have hB : 6 * points.card ≤ ∑ C ∈ curves, degree C := by
      calc
        _ ≤ 6 * (∑ C ∈ curves.attach, (B C).card) :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ C ∈ curves.attach, 6 * (B C).card := by rw [Finset.mul_sum]
        _ ≤ ∑ C ∈ curves.attach, degree C.val :=
          Finset.sum_le_sum fun C _ => (hd C).2.2.2.2.1
        _ = _ := Finset.sum_attach curves degree
    have hN : 6 * cover.n ≤ ∑ C ∈ curves, degree C := by
      calc
        _ = ∑ _ ∈ curves.attach, 6 := by simp [cover, Nat.mul_comm]
        _ ≤ ∑ C ∈ curves.attach, degree C.val :=
          Finset.sum_le_sum fun C _ => (hd C).2.2.2.2.2
        _ = _ := Finset.sum_attach curves degree
    change 32 * (∑ C ∈ curves, degree C) ≤ _ at hpoints
    omega

theorem aux_geometry : AuxGeometry := by
  classical
  intro Γ s f Q l input
  have h1 := Geometry.K1_13_6_1_1
  have h2 := Geometry.K1_13_6_1_2
  have h3 := Geometry.K1_13_6_1_3
  have h4 := Geometry.K1_13_6_1_4
  have h5 := Geometry.K1_13_6_1_5
  let hs := (intersectionIdeal f Q).finite_minimalPrimes_of_isNoetherianRing
  let zs := hs.toFinset.filter (HasMark Γ s)
  have selected : ∀ surface ∈ zs, ∃ P, SurfaceCut f Q surface P ∧
      ∀ γ ∈ Γ, surface ≤ markIdeal (extend (s γ)) →
        ¬ HighMark f Q l (extend (s γ)) → atJet P (extend (s γ)) = 0 := by
    intro surface hZ
    rcases Finset.mem_filter.mp hZ with ⟨hbase, hmark⟩
    exact one_surface h1 h2 h3 input (hs.mem_toFinset.mp hbase) hmark
  have all : ∀ surface, ∃ P : Row 4, surface ∈ zs →
      SurfaceCut f Q surface P ∧
      ∀ γ ∈ Γ, surface ≤ markIdeal (extend (s γ)) →
        ¬ HighMark f Q l (extend (s γ)) → atJet P (extend (s γ)) = 0 := by
    intro surface
    by_cases hz : surface ∈ zs
    · obtain ⟨P, hP⟩ := selected surface hz
      exact ⟨P, fun _ => hP⟩
    · exact ⟨0, fun h => (hz h).elim⟩
  choose P hP using all
  have hbox : InBox (shape Q) cutterBox :=
    ⟨input.box.1.trans (by decide), input.box.2⟩
  obtain ⟨cs, hdiv, hcurve, hc, hp⟩ := h4 f Q zs P input.small input.proper hbox
    (fun surface hZ => (hP surface hZ).1)
  let curves := cs.filter (HasMark Γ s)
  apply assemble curves
  · intro γ hγ hn
    obtain ⟨surface, hZ, hmark⟩ := mark_surface input.positive
      (input.onFactor γ hγ) (input.order γ hγ)
    have hz : surface ∈ zs := Finset.mem_filter.mpr ⟨hs.mem_toFinset.mpr hZ, γ, hγ, hmark⟩
    obtain ⟨C, hC, hcmark⟩ := mark_curve hmark ((hP surface hz).2 γ hγ hmark hn)
    exact ⟨C, Finset.mem_filter.mpr ⟨hdiv surface hz C hC, γ, hγ, hcmark⟩, hcmark⟩
  · intro C
    obtain ⟨hC, γ, hγ, hmark⟩ := Finset.mem_filter.mp C.property
    have hcf := hcurve C.val hC
    obtain ⟨r, hr, hsep⟩ := h1 f C.val (extend (s γ)) input.small
      (input.onFactor γ hγ) hcf.contains hmark
    exact h5 Γ s f C.val r input.small hcf hr hsep input.distinct input.degree
  · exact (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))).trans hc
  · exact (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))).trans hp

end Aux

namespace Mixed
open K1_13_6_2

theorem mixed_geometry : MixedGeometry := by
  classical
  intro Γ s f Q l input
  have h4chart := Geometry.K1_13_6_2_1
  have h5chart := Geometry.K1_13_6_2_2
  have h4budget := Geometry.K1_13_6_2_3
  have h5budget := Geometry.K1_13_6_2_4
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
  have fitQ : InBox (shape Q) cutterBox :=
    ⟨input.box.1.trans (by decide), input.box.2⟩
  have bound4 := h4budget f Q l input.small input.proper fitQ input.positive branches points
    (by
      intro b hb
      obtain ⟨hmember, hnext, hvalue⟩ := h4chart f Q l input.small b
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
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
      have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
      exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ)))
        (contains_label b γ (demand_sub b hγ))).mpr hvalueγ)
  have bound5 := h5budget f Q l input.small input.proper fitQ input.positive branches points
    (by
      intro b hb
      obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := h5chart f Q l input.small b
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
    change _ ≤ min (budget4 (shape f).chamber) (budget5 (shape f).chamber)
    exact (Nat.mul_le_mul_left (32 * l) hpay).trans (le_min bound4 bound5)

end Mixed

namespace Continued
open K1_13_6_3

/-- Truncated exponential integration of a regular invariant component.
The true weights pay for the identities in the independent argument. -/
private def IntegralContinuation : Prop :=
  ∀ (f Q : Row 4) (r : ℕ) (P : JetIdeal) (hp : P.IsPrime),
    TrueWeightLE f (90 * 180265 - 1) → TrueWeightLE Q (K1.p - 4) →
    intersectionIdeal f Q ≤ P →
    let g := (separant^[r]) f
    toGeneric g ∈ P → toGeneric (separant g) ∉ P →
    toGeneric (membershipTest g) ∈ P → Invariant g P →
    ∃ U : (JetField P)[X], @Integrated f Q g P hp U

section Exponential
open K1_13_6_3_2
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem rowAt_eval (P : JetIdeal) (H : Row 4) :
    MvPolynomial.eval₂ (Polynomial.aeval (abscissa (rowAt P))).toRingHom
      (jetCoordinate (rowAt P)) H = rowAt P H := by
  change MvPolynomial.eval₂Hom _ _ H = rowAt P H
  have hc : (Polynomial.aeval (abscissa (rowAt P))).toRingHom =
      (rowAt P).comp MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, RingHom.comp_apply]
      rfl
    · simp [abscissa]
  rw [hc]
  have h : MvPolynomial.eval₂Hom ((rowAt P).comp MvPolynomial.C)
      (jetCoordinate (rowAt P)) = rowAt P := by
    apply MvPolynomial.ringHom_ext <;> simp [jetCoordinate]
  rw [h]

private theorem initial_dividedIterate {F : Type} [Field F] [Algebra Geom F]
    (e : Row 4 →+* F) (D : Derivation Geom F F)
    (shift : ∀ i : Fin 3, D (jetCoordinate e i.castSucc) =
      ((i.val + 1 : ℕ) : F) * jetCoordinate e i.succ) (i : Fin 4) :
    dividedIterate D (jetCoordinate e 0) i.val = jetCoordinate e i := by
  have raw (j : Fin 4) : ((D : F → F)^[j.val]) (jetCoordinate e 0) =
      (j.val.factorial : F) * jetCoordinate e j := by
    induction j using Fin.induction with
    | zero => simp
    | succ j ih =>
      rw [Fin.val_succ, Function.iterate_succ_apply', ← Fin.val_castSucc j, ih]
      simp only [D.leibniz, D.map_natCast, smul_eq_mul, mul_zero, add_zero, shift,
        Fin.val_castSucc, Nat.factorial_succ, Nat.cast_mul]
      ring
  have hfact := factorial_ne_zero (algebraMap Geom F)
    (i.isLt.trans (by decide : 4 < K1.p))
  rw [dividedIterate, raw i, mul_div_cancel_left₀ _ hfact]

private theorem chartTaylor_toComponent (P : JetIdeal) [P.IsPrime] (g : Row 4) :
    (chartTaylor (rowAt P) g).map (toComponent P) = chartTaylor (componentRow P) g := by
  unfold chartTaylor abscissa
  rw [map_fromTaylor]
  simp only [map_div₀, map_pow, map_natCast, toComponent_rowAt]

private theorem integral_continuation : IntegralContinuation := by
  intro f Q r P hp hf hQ hcut
  have h1 := Geometry.K1_13_6_3_2_1
  have h2 := Geometry.K1_13_6_3_2_2
  have h3 := Geometry.K1_13_6_3_2_3
  dsimp only
  intro hg hsep hmember hinv
  let g := (separant^[r]) f
  let e := rowAt P
  let x := abscissa e
  let y := jetCoordinate e 0
  let k := toComponent P
  obtain ⟨D, hx, hshift, haction⟩ := h1 g P hp hg hsep hinv
  have hs : e (separant g) ≠ 0 := fun hz => hsep ((rowAt_eq_zero P _).mp hz)
  have hM : ((D : ContractedField P → ContractedField P)^[taylorLength]) y = 0 := by
    have hz := (rowAt_eq_zero P (membershipTest g)).mpr hmember
    change e (jetNumerator g taylorLength) = 0 at hz
    rw [jetNumerator_eq_iterate e g D haction] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hs)
  have hcanon : chartTaylor e g = differentialTaylor D x y := by
    unfold chartTaylor differentialTaylor
    apply congrArg (fromTaylor (M := taylorLength) x)
    funext i
    unfold dividedIterate
    rw [jetNumerator_eq_iterate e g D haction, mul_div_cancel_left₀ _ (pow_ne_zero _ hs)]
  have hmap : (differentialTaylor D x y).map k = chartTaylor (componentRow P) g := by
    rw [← hcanon]
    exact chartTaylor_toComponent P g
  have hinitial (i : Fin 4) : dividedIterate D y i.val = jetCoordinate e i :=
    initial_dividedIterate e D hshift i
  have hconstants : k.comp (algebraMap Geom (ContractedField P)) = componentConstants P := by
    ext a
    exact toComponent_constantsAt P a
  have hcontinue (H : Row 4) (B : ℕ) (hW : TrueWeightLE H B) (hguard : B + 3 < K1.p)
      (hH : toGeneric H ∈ P) :
      trajectory (componentConstants P) H (chartTaylor (componentRow P) g) = 0 := by
    have hzero : MvPolynomial.eval₂ (Polynomial.aeval x).toRingHom
        (fun i => dividedIterate D y i.val) H = 0 := by
      simp only [hinitial]
      exact (rowAt_eval P H).trans ((rowAt_eq_zero P H).mpr hH)
    have hh := congrArg (fun U : (ContractedField P)[X] => U.map k)
      (h2 (ContractedField P) D x y hx hM H B hW hguard hzero)
    rw [map_trajectory, hconstants, hmap, Polynomial.map_zero] at hh
    exact hh
  have hfP : toGeneric f ∈ P :=
    hcut (Ideal.subset_span (by simp : toGeneric f ∈ ({toGeneric f, toGeneric Q} : Set GeoJets)))
  have hQP : toGeneric Q ∈ P :=
    hcut (Ideal.subset_span (by simp : toGeneric Q ∈ ({toGeneric f, toGeneric Q} : Set GeoJets)))
  refine ⟨chartTaylor (componentRow P) g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fromTaylor_degree _ _ (by decide : 0 < taylorLength)
  · intro i
    rw [← hmap]
    change (hasseDeriv i.val ((differentialTaylor D x y).map k)).eval
      (onComponent P (MvPolynomial.C genericArgument)) = _
    rw [Polynomial.hasseDeriv_map, ← toComponent_abscissa P]
    change ((hasseDeriv i.val (differentialTaylor D x y)).map k).eval (k x) = _
    rw [Polynomial.eval_map_apply]
    have hT := fromTaylor_hasse x (fun j => dividedIterate D y j.val)
      (i.castLE (by decide : 4 ≤ taylorLength))
    change (hasseDeriv i.val (differentialTaylor D x y)).eval x = dividedIterate D y i.val at hT
    rw [hT, hinitial]
    exact toComponent_jetCoordinate P i
  · exact hcontinue f _ hf (by decide) hfP
  · exact hcontinue Q _ hQ (by decide) hQP
  · exact hcontinue g _ (iterate_separant_weight hf r) (by decide) hg
  · exact h3 g P hp hg hsep

end Exponential

section CoefficientFamilies
open MvPolynomial

private theorem markPoint_inj {Γ : Finset K} {s : K → K[X]} {f Q : Row 4} {l : ℕ}
    (h : RelaxedCutInput Γ s f Q l) : Set.InjOn (markPoint s) (Γ : Set K) := by
  intro α hα β hβ hEq
  apply h.distinct hα hβ
  apply Polynomial.ext
  intro n
  by_cases hn : n < taylorLength
  · have hcoeff := congrFun hEq ⟨n, hn⟩
    exact embed.injective (by simpa only [markPoint, coeffPoint, Polynomial.coeff_map] using hcoeff)
  · have hαdeg := h.degree α hα
    have hβdeg := h.degree β hβ
    have hlt : 133671 < n := by
      change ¬ n < 133672 at hn
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hαdeg.trans_lt hlt),
      Polynomial.coeff_eq_zero_of_natDegree_lt (hβdeg.trans_lt hlt)]

private def CurveSource (f Q : Row 4) (l : ℕ) (P : JetIdeal) : Prop :=
  ∃ (surface : JetIdeal) (r : ℕ) (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime ∧
    CanonicalChart f surface r ∧ SimpleCut ((separant^[r]) f) surface P

private def FamilyCase (f Q : Row 4) (l : ℕ) (A : CoeffIdeal) : Prop :=
  (dimension A = 1 ∧ CurveSource f Q l (freshImage A)) ∨
  (dimension A = 2 ∧ (intersectionIdeal f Q).IsMinimalPrime (freshImage A))

private theorem canonical_unique {f : Row 4} {surface : JetIdeal} {r t : ℕ}
    (hr : CanonicalChart f surface r) (ht : CanonicalChart f surface t) : r = t := by
  rcases lt_trichotomy r t with h | h | h
  · have hm := ht.2.1 (r + 1) (Nat.succ_le_of_lt h)
    rw [Function.iterate_succ_apply'] at hm
    exact False.elim (hr.2.2 hm)
  · exact h
  · have hm := hr.2.1 (t + 1) (Nat.succ_le_of_lt h)
    rw [Function.iterate_succ_apply'] at hm
    exact False.elim (ht.2.2 hm)

private theorem cycleWeight_ge {f Q : Row 4} (hc : CutCycle f Q) {surface : JetIdeal}
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface) {l : ℕ}
    (hl : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime) :
    l ≤ cycleWeight (intersectionIdeal f Q) surface := by
  classical
  have hne : cycleLength (intersectionIdeal f Q) surface hz.isPrime ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hc.local_bound surface hz).2.2
  simpa only [cycleWeight, dite_eq_left hz.isPrime, ENat.toNat_natCast] using ENat.toNat_le_toNat hl hne

private theorem surface_sum {f Q : Row 4} (hc : CutCycle f Q) (T : Finset JetIdeal)
    (hT : ∀ P ∈ T, (intersectionIdeal f Q).IsMinimalPrime P) :
    ∑ P ∈ T, affineDegree P ≤ ((shape f).b * cutterBox.b : ℕ) := by
  classical
  let S := (intersectionIdeal f Q).minimalPrimesFinset
  have hsub : T ⊆ S := fun P hP => Ideal.mem_minimalPrimesFinset.mpr (hT P hP)
  calc
    _ ≤ ∑ P ∈ S, affineDegree P :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => affineDegree_nonneg P)
    _ ≤ ∑ P ∈ S, (cycleWeight (intersectionIdeal f Q) P : ℚ) * affineDegree P := by
      apply Finset.sum_le_sum
      intro P hP
      have hz := Ideal.mem_minimalPrimesFinset.mp hP
      have h1 := cycleWeight_ge hc hz (hc.local_bound P hz).2.1
      exact le_mul_of_one_le_left (affineDegree_nonneg P) (by exact_mod_cast h1)
    _ ≤ _ := hc.weighted_degree

private theorem curve_sum {f Q : Row 4} {l : ℕ} (hc : CutCycle f Q)
    (T : Finset JetIdeal) (hT : ∀ P ∈ T, CurveSource f Q l P) :
    (l : ℚ) * (∑ P ∈ T, affineDegree P) ≤ (membershipDegree (shape f) : ℕ) := by
  classical
  let J := intersectionIdeal f Q
  let S := J.minimalPrimesFinset
  let b := (chart (taylorLength + 1) (shape f).chamber).b
  let parent : JetIdeal → JetIdeal := fun P =>
    if h : P ∈ T then Classical.choose (hT P h) else ⊥
  have hd (P : JetIdeal) (hP : P ∈ T) :
      ∃ (r : ℕ) (hz : J.IsMinimalPrime (parent P)),
        (l : ℕ∞) ≤ cycleLength J (parent P) hz.isPrime ∧
        CanonicalChart f (parent P) r ∧ SimpleCut ((separant^[r]) f) (parent P) P := by
    simpa only [parent, dite_eq_left hP] using Classical.choose_spec (hT P hP)
  have hm (P : JetIdeal) (hP : P ∈ T) : parent P ∈ S := by
    obtain ⟨_, hz, _⟩ := hd P hP
    exact Ideal.mem_minimalPrimesFinset.mpr hz
  have hfibre (surface : JetIdeal) :
      (∑ P ∈ T.filter (fun P => parent P = surface), (l : ℚ) * affineDegree P) ≤
        b * ((cycleWeight J surface : ℚ) * affineDegree surface) := by
    let V := T.filter (fun P => parent P = surface)
    by_cases hV : V.Nonempty
    · obtain ⟨P₀, hP₀⟩ := hV
      obtain ⟨hP₀T, hP₀parent⟩ := Finset.mem_filter.mp hP₀
      have hdata := hd P₀ hP₀T
      rw [hP₀parent] at hdata
      obtain ⟨r, hz, hhigh, hchart, hcut⟩ := hdata
      let _ := hz.isPrime
      let g := (separant^[r]) f
      let B := (divisorIdeal surface (membershipTest g)).minimalPrimesFinset
      have hsub : V ⊆ B := by
        intro P hP
        obtain ⟨hPT, hPparent⟩ := Finset.mem_filter.mp hP
        obtain ⟨r', hz', _, hchart', hcut'⟩ := hd P hPT
        rw [hPparent] at hchart' hcut'
        have hEq := canonical_unique hchart' hchart
        subst r'
        exact Ideal.mem_minimalPrimesFinset.mpr hcut'.minimal
      have hB : (∑ P ∈ B, affineDegree P) ≤ (b : ℚ) * affineDegree surface :=
        principalCut_sum_affineDegree_minimalPrimes_le hcut.proper (membershipTest_degree f r)
      have hl := cycleWeight_ge hc hz hhigh
      calc
        _ = (l : ℚ) * (∑ P ∈ V, affineDegree P) := (Finset.mul_sum ..).symm
        _ ≤ (l : ℚ) * ((b : ℚ) * affineDegree surface) :=
          mul_le_mul_of_nonneg_left
            ((Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun P _ _ => affineDegree_nonneg P)).trans hB) (by positivity)
        _ ≤ _ := by
          rw [mul_left_comm]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) (affineDegree_nonneg _))
            (by positivity)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hV
      change (∑ P ∈ V, (l : ℚ) * affineDegree P) ≤ _
      rw [he, Finset.sum_empty]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (affineDegree_nonneg _))
  calc
    _ = ∑ P ∈ T, (l : ℚ) * affineDegree P := Finset.mul_sum ..
    _ = ∑ surface ∈ S, ∑ P ∈ T.filter (fun P => parent P = surface),
          (l : ℚ) * affineDegree P :=
      (Finset.sum_fiberwise_of_maps_to hm _).symm
    _ ≤ ∑ surface ∈ S, (b : ℚ) * ((cycleWeight J surface : ℚ) * affineDegree surface) :=
      Finset.sum_le_sum (fun surface _ => hfibre surface)
    _ = (b : ℚ) * ∑ surface ∈ S, (cycleWeight J surface : ℚ) * affineDegree surface :=
      (Finset.mul_sum ..).symm
    _ ≤ (b : ℚ) * (((shape f).b * cutterBox.b : ℕ) : ℚ) :=
      mul_le_mul_of_nonneg_left hc.weighted_degree (by positivity)
    _ = _ := by simp only [membershipDegree, Nat.cast_mul, b]; ring

private theorem family_of_mark (h1 : K1_13_6_3.c1) (h2 : IntegralContinuation) (h3 : K1_13_6_3.c3)
    {Γ : Finset K} {s : K → K[X]} {f Q : Row 4} {l : ℕ}
    (input : RelaxedCutInput Γ s f Q l) (hc : CutCycle f Q)
    {γ : K} (hγ : γ ∈ Γ) (hmark : ContinuedMark f Q l (extend (s γ))) :
    ∃ A : CoeffIdeal, FreshModel f A ∧ FamilyCase f Q l A ∧ γ ∈ marksOn Γ s A := by
  obtain ⟨surface, r, hz, hcont⟩ := hmark
  let g := (separant^[r]) f
  have hdim (T : JetIdeal) (hT : (intersectionIdeal f Q).IsMinimalPrime T) :
      dimension T = 2 := (hc.local_bound T hT).1
  have hnum : (shape f).b * cutterBox.b < K1.p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ input.small.2.2.1.1) (by decide)
  have hsmall : cycleLength (intersectionIdeal f Q) surface hz.base.isPrime < (K1.p : ℕ∞) :=
    (hc.local_bound surface hz.base).2.2.trans_lt (by exact_mod_cast hnum)
  have integrate (P : JetIdeal) (hp : P.IsPrime) (hle : surface ≤ P)
      (hpoint : P ≤ markIdeal (extend (s γ))) (hI : Invariant g P)
      (hE : toGeneric (membershipTest g) ∈ P)
      (hbranch : P = surface ∨ SimpleCut g surface P) :
      ∃ A : CoeffIdeal, FreshModel f A ∧ FamilyCase f Q l A ∧ γ ∈ marksOn Γ s A := by
    have hg : toGeneric g ∈ P := hle (hz.chart.2.1 r le_rfl)
    have hsep : toGeneric (separant g) ∉ P := by
      intro hm
      have h := hpoint hm
      apply hz.regular
      unfold markIdeal at h
      rw [RingHom.mem_ker] at h
      have hinj : Function.Injective genericCoeffs :=
        (algebraMap GenericField GeoField).injective.comp
          (IsFractionRing.injective Geom[X] GenericField)
      apply hinj
      rw [map_zero]
      change MvPolynomial.eval _ (MvPolynomial.map genericCoeffs (separant g)) = 0 at h
      rw [MvPolynomial.eval_map] at h
      change MvPolynomial.eval₂ genericCoeffs (⇑genericCoeffs ∘ jet (extend (s γ)))
        (separant g) = 0 at h
      rw [← MvPolynomial.eval₂_comp] at h
      exact h
    obtain ⟨U, hU⟩ := h2 f Q r P hp input.small.2.2.2 input.weight
      (hz.base.1.2.trans hle) hg hsep hE hI
    obtain ⟨hA, hcase⟩ := h3.1 f Q surface r P hp U hz.base hdim hsep hbranch hU
    refine ⟨_, hA, ?_, mem_marksOn.mpr ⟨hγ, ?_⟩⟩
    · rcases hcase with ⟨hd, heq, hsimple⟩ | hsurface
      · exact Or.inl ⟨hd, surface, r, hz.base, hz.high, hz.chart, heq.symm ▸ hsimple⟩
      · exact Or.inr hsurface
    · have hs : (extend (s γ)).natDegree < taylorLength := by
        rw [Polynomial.natDegree_map]
        exact Nat.lt_succ_of_le (input.degree γ hγ)
      exact hU.specializes _ hs hpoint hz.regular
  rcases hcont with hE | ⟨P, hm, hproper, hpoint, hone, hnext⟩
  · exact integrate surface hz.base.isPrime le_rfl hz.point hz.invariant hE (Or.inl rfl)
  · have hs : SimpleCut g surface P := ⟨hproper, hm, hone, hnext⟩
    have hI := h1 f Q surface r P hz.base hz.chart hsmall hz.invariant hs
    have hl : divisorIdeal surface (membershipTest g) ≤ P := hm.1.2
    have hE : toGeneric (membershipTest g) ∈ P :=
      hl (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
    exact integrate P hm.isPrime (le_sup_left.trans hl) hpoint hI hE (Or.inr hs)

theorem continued_geometry : ContinuedGeometry := by
  classical
  intro Γ s f Q l input
  have h1 := Geometry.K1_13_6_3_1
  have h2 := integral_continuation
  have h3 := Geometry.K1_13_6_3_3
  have h4 := Geometry.K1_13_6_3_4
  have h5 := Geometry.K1_13_6_3_5
  have h6 := Geometry.K1_13_6_3_6
  have hc := h6 f Q input.small input.proper input.box
  let B := Γ.filter (fun γ => ContinuedMark f Q l (extend (s γ)))
  have hw (γ : B) :
      ∃ A : CoeffIdeal, FreshModel f A ∧ FamilyCase f Q l A ∧ γ.val ∈ marksOn Γ s A := by
    obtain ⟨hγ, hmark⟩ := Finset.mem_filter.mp γ.property
    exact family_of_mark h1 h2 h3 input hc hγ hmark
  let A : B → CoeffIdeal := fun γ => Classical.choose (hw γ)
  have hA (γ : B) : FreshModel f (A γ) ∧ FamilyCase f Q l (A γ) ∧ γ.val ∈ marksOn Γ s (A γ) :=
    Classical.choose_spec (hw γ)
  let T := B.attach.image A
  let Tc := T.filter (fun P => dimension P = 1)
  let Td := T.filter (fun P => dimension P = 2)
  have hT (P : CoeffIdeal) (hp : P ∈ T) :
      FreshModel f P ∧ FamilyCase f Q l P ∧ (marksOn Γ s P).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(hA γ).1, (hA γ).2.1, ⟨γ.val, (hA γ).2.2⟩⟩
  have hd (P : CoeffIdeal) (hp : P ∈ T) : dimension P = 1 ∨ dimension P = 2 :=
    (hT P hp).2.1.imp And.left And.left
  have hC (P : CoeffIdeal) (hp : P ∈ Tc) : CurveSource f Q l (freshImage P) := by
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp hp
    rcases (hT P ht).2.1 with h | h
    · exact h.2
    · exact False.elim (by omega)
  have hD (P : CoeffIdeal) (hp : P ∈ Td) :
      (intersectionIdeal f Q).IsMinimalPrime (freshImage P) := by
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp hp
    rcases (hT P ht).2.1 with h | h
    · exact False.elim (by omega)
    · exact h.2
  have hinj : Set.InjOn freshImage (T : Set CoeffIdeal) := by
    apply (h3.2 f).mono
    intro P hp
    have hm := (hT P hp).1
    exact ⟨hm.prime, hm.regular⟩
  have hpart (P : CoeffIdeal) : marksOn Γ s P ⊆ Γ := fun _ h => (mem_marksOn.mp h).1
  let C := piecesOf Tc (marksOn Γ s) (fun P _ => hpart P)
  let D := piecesOf Td (marksOn Γ s) (fun P _ => hpart P)
  have hdegree (γ : K) (hγ : γ ∈ Γ) : (s γ).natDegree < taylorLength :=
    Nat.lt_succ_of_le (input.degree γ hγ)
  refine ⟨C, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    let P := Tc.equivFin.symm i
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp P.property
    exact curveSections_of_prime (hT P ht).1.prime he
      (fun γ hγ => hdegree γ (hpart P hγ))
      ((markPoint_inj input).mono (hpart P))
      (fun _ hγ => (mem_marksOn.mp hγ).2)
  · intro i
    let P := Td.equivFin.symm i
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp P.property
    exact surfaceSections_of_prime (hT P ht).1.prime he
      (fun γ hγ => hdegree γ (hpart P hγ))
      ((markPoint_inj input).mono (hpart P))
      (fun _ hγ => (mem_marksOn.mp hγ).2)
  · intro i
    let P := Tc.equivFin.symm i
    have ht := hT P (Finset.mem_filter.mp P.property).1
    exact degreeAllowance_pos ht.1.prime ht.2.2
  · intro i
    let P := Td.equivFin.symm i
    have ht := hT P (Finset.mem_filter.mp P.property).1
    exact degreeAllowance_pos ht.1.prime ht.2.2
  · intro γ hγ hm
    let γ' : B := ⟨γ, Finset.mem_filter.mpr ⟨hγ, hm⟩⟩
    have hmem : A γ' ∈ T := Finset.mem_image_of_mem A (Finset.mem_attach _ _)
    rcases hd _ hmem with h | h
    · exact Finset.mem_union_left _ (mem_piecesOf.mpr
        ⟨_, Finset.mem_filter.mpr ⟨hmem, h⟩, (hA γ').2.2⟩)
    · exact Finset.mem_union_right _ (mem_piecesOf.mpr
        ⟨_, Finset.mem_filter.mpr ⟨hmem, h⟩, (hA γ').2.2⟩)
  · have hsum := curve_sum hc (Tc.image freshImage) (by
      intro P hp
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
      exact hC A hA)
    have heq : (∑ P ∈ Tc, affineDegree P) = ∑ P ∈ Tc.image freshImage, affineDegree P := by
      rw [Finset.sum_image (fun P hP R hR h => hinj (Finset.mem_filter.mp hP).1
        (Finset.mem_filter.mp hR).1 h)]
      apply Finset.sum_congr rfl
      intro P hP
      obtain ⟨ht, he⟩ := Finset.mem_filter.mp hP
      have hf := (hT P ht).1
      exact h4 P hf.prime hf.extended_prime he hf.birational
    rw [← heq] at hsum
    exact_mod_cast
      (mul_le_mul_of_nonneg_left (piecesOf_le_degree (T := Tc) (part := marksOn Γ s))
        (show (0 : ℚ) ≤ l by positivity)).trans hsum
  · have hsum := surface_sum hc (Td.image freshImage) (by
      intro P hp
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
      exact hD A hA)
    have hbound : (2 : ℚ) * (D.total : ℚ) ≤ 133671 * (((shape f).b * cutterBox.b : ℕ) : ℚ) := by
      calc
        _ ≤ 2 * (∑ P ∈ Td, affineDegree P) :=
          mul_le_mul_of_nonneg_left (piecesOf_le_degree (T := Td) (part := marksOn Γ s))
            (by positivity)
        _ ≤ ∑ P ∈ Td, 133671 * affineDegree (freshImage P) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro P hP
          obtain ⟨ht, he⟩ := Finset.mem_filter.mp hP
          have hf := (hT P ht).1
          exact h5 P hf.prime hf.extended_prime he hf.birational
        _ = 133671 * (∑ P ∈ Td.image freshImage, affineDegree P) := by
          rw [Finset.mul_sum, Finset.sum_image (fun P hP R hR h =>
            hinj (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hR).1 h)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [Nat.mul_assoc]
    exact_mod_cast hbound

end CoefficientFamilies
end Continued

/-- A cutter charged at the new message degree satisfies the characteristic guard in the old metric. -/
theorem cutter_weight_of_new_degree (Q : Row 4) (hbox : InBox (shape Q) ⟨4012, 1650, 550⟩)
    (hw : ∀ m ∈ Q.support, (Q.coeff m).natDegree +
      m.sum (fun i a => (133518 - i.val) * a) ≤ 3000 * 180169 - 1) :
    TrueWeightLE Q (K1.p - 4) := by
  intro m hm
  have hsum : m.sum (fun i a => (133671 - i.val) * a) =
      m.sum (fun i a => (133518 - i.val) * a) + 153 * m.degree := by
    simp only [Finsupp.degree_apply, Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    rw [show 133671 - i.val = (133518 - i.val) + 153 by omega, Nat.add_mul]
  have hdeg : m.degree ≤ 4012 := (MvPolynomial.le_totalDegree hm).trans hbox.1
  calc
    _ = ((Q.coeff m).natDegree + m.sum (fun i a => (133518 - i.val) * a)) + 153 * m.degree := by
      rw [hsum, Nat.add_assoc]
    _ ≤ 3000 * 180169 - 1 + 153 * 4012 :=
      Nat.add_le_add (hw m hm) (Nat.mul_le_mul_left 153 hdeg)
    _ ≤ K1.p - 4 := by decide

/-- The original physical price holds for a cutter obeying the characteristic guard. -/
theorem physical_count_relaxed (w : I → K) {Γ s} (hm : LowFat6921.Messages w Γ s)
    (f : Row 4) (hf : SmallFactor f) (hOn : ∀ γ ∈ Γ, OnFactor f (extend (s γ)))
    (l : ℕ) (hl : 0 < l) (hCut : RelaxedProperCut f Γ s l) :
    Γ.card ≤ physicalPrice (shape f) l := by
  obtain ⟨Q, hproper, hbox, hweight, horder⟩ := hCut
  have input : RelaxedCutInput Γ s f Q l :=
    ⟨hm.distinct, hm.old_degree, hf, hOn, hl, hproper, hbox, hweight, horder⟩
  obtain ⟨A, AB, hA, haCover, haCurves, haPoints⟩ := Aux.aux_geometry Γ s f Q l input
  obtain ⟨C, CB, hC, hcPos, hcCover, hcBudget⟩ := Mixed.mixed_geometry Γ s f Q l input
  obtain ⟨D, F, hD, hF, hdPos, hfPos, hdCover, hdBudget, hfBudget⟩ :=
    Continued.continued_geometry Γ s f Q l input
  exact physical_count_from_sections w hm f Q l hl A C D F AB CB hA haCover haCurves haPoints
    hC hcPos hcCover hcBudget hD hF hdPos hfPos hdCover hdBudget hfBudget

end
end LowPrice6921
