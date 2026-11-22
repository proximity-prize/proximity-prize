import ProximityPrize.SubmissionLower.Final50ActiveCycleBound
import ProximityPrize.SubmissionLower.Final50GeometryCut
import ProximityPrize.SubmissionLower.Final50ActiveCycleMixed
import ProximityPrize.SubmissionLower.Shared50CycleLegacy

-- merged module Shared50CycleBound
section Merged_Shared50CycleBound
set_option autoImplicit false

namespace Shared50CycleBound

noncomputable section

open Low48BentCycle (Family mixedDegree properCut cycleComparison divisorBound diagonalExponents)

open Final50Price (SmallFactor)
open Final50GeometryCut_2 (Branch)
open Final50GeometryCut_2_3 (graphLift chart_index_eq graphLift_same_chart
  membership_same_chart graphLift_comap member_proper_on_graph)
open P0_9_6_2_3 (cylinder_comparison)
open K1_13 (Row)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5)
open K1_13_6_2_4 (Exponent Component DimLE OfDim LengthAt ambient_dim cylinder cylinder_injective
  dim_le_after_section oldEmbedding pointIdeal sectionIdeal)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators Pointwise

open Final50ActiveCycle (Section Doubled Slice)
open private square_support bound_marks from ProximityPrize.SubmissionLower.Final50ActiveCycleBound

private theorem initial_bound {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (f Q : Row 4) (weight : Ideal GeoJets → ℕ) (hf : SmallFactor f) (hQ : ¬ f ∣ Q)
    (hfbox : Section R 0 (oldEmbedding (toGeneric f)))
    (hQbox : Section R 1 (oldEmbedding (toGeneric Q))) (S : Finset (Ideal GeoJets))
    (hS : ∀ P ∈ S, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (weight P : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime) :
    (∀ P ∈ S, (cylinder P).IsPrime ∧ OfDim (cylinder P) 3) ∧
      (∑ P ∈ S, (weight P : ℚ) * mixedDegree B (cylinder P) {2, 3, 4}) ≤
        mixedDegree B ⊥ Finset.univ := by
  classical
  let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
  let J := sectionIdeal A (oldEmbedding (toGeneric Q))
  obtain ⟨hregQ, hAlgebra⟩ := cylinder_comparison f Q hf.1 hQ
  have hregf : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets5)
      (oldEmbedding (toGeneric f))) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne
      (K1_13_6_3_6.toGeneric_ne_zero hf.1.ne_zero)
  have hAdim : DimLE A 4 := dim_le_after_section hregf ambient_dim
  have hJdim : DimLE J 3 := dim_le_after_section hregQ hAdim
  have hgeom (P : Ideal GeoJets) (hP : P ∈ S) :
      (cylinder P).IsPrime ∧ OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P), (weight P : ℕ∞) ≤ LengthAt J (cylinder P) hc.isPrime := by
    obtain ⟨h, hw⟩ := hS P hP
    obtain ⟨hd, hc, hl⟩ := hAlgebra P h
    exact ⟨hc.isPrime, hd, hc, hw.trans hl⟩
  refine ⟨fun P hP => ⟨(hgeom P hP).1, (hgeom P hP).2.1⟩, ?_⟩
  have hs := cycleComparison B hB.double_zero hB.double_coordinates J {2, 3, 4} hJdim S cylinder weight cylinder_injective.injOn
    (fun P hP => (hgeom P hP).2.2)
  have hcutQ := properCut B hB.double_zero A {2, 3, 4} 1 (by decide) hAdim
    (oldEmbedding (toGeneric Q)) (fun m hm => hB.raw_mem (hQbox m hm)) (square_support hB hQbox) hregQ
  have hcutf := properCut B hB.double_zero ⊥ {1, 2, 3, 4} 0 (by decide) ambient_dim
    (oldEmbedding (toGeneric f)) (fun m hm => hB.raw_mem (hfbox m hm)) (square_support hB hfbox) hregf
  have hall : (insert (0 : Fin 5) {1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
  rw [hall] at hcutf
  exact hs.trans (hcutQ.trans hcutf)
/-- Bound fixed chart incidences with a separate cut and surface-dependent orders. -/
theorem bound_with_cut {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (f Q cut : Row 4) (l : ℕ) (hf : SmallFactor f) (hproper : ¬ f ∣ cut)
    (weight : Ideal GeoJets → ℕ)
    (hfbox : Section R 0 (oldEmbedding (toGeneric f)))
    (hQ : Section R 1 (oldEmbedding (toGeneric cut)))
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hF : ∀ b ∈ F, Section R 2 b.graph ∧
      (∃ E, Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member)) ∧
      (∀ p ∈ T b, b.Contains p) ∧ Slice R b (T b))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal f cut).IsMinimalPrime b.surface,
      (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal f cut) b.surface h.isPrime) :
    (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight : ℚ) * (T b).card)) ≤
      mixedDegree B ⊥ Finset.univ := by
  classical
  have hgraph := @Final50GeometryCut_2_3_1.proof f Q l
  have hmember := @Final50GeometryCut_2_3_2.proof f Q l
  let S := F.image Branch.surface
  let fibre (P : Ideal GeoJets) := F.filter fun b => b.surface = P
  let charge (b : Branch f Q l) : ℚ := (b.weight : ℚ) * (T b).card
  obtain ⟨hZ, hsumZ⟩ := initial_bound hB f cut weight hf hproper hfbox hQ S (by
    intro P hP
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    exact hcut b hb)
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
        (bound_marks hB c (T c) hon hslice hcomp.minimal.isPrime hdim)
        (Nat.cast_nonneg _)
    have hEbound := divisorBound B hB.double_zero hB.double_coordinates G {4} 3 hG.minimal.isPrime (by decide) hGdim E (fun m hm => hB.raw_mem (hboxE m hm)) (square_support hB hboxE) hproperE
      (fibre b.surface) C Branch.weight inj (fun c hc => (hC c (Finset.mem_filter.mp hc).2).1)
    have hGbound := divisorBound B hB.double_zero hB.double_coordinates (cylinder b.surface) {3, 4} 2 hZprime (by decide) hZdim
      b.graph (fun m hm => hB.raw_mem (hboxG m hm)) (square_support hB hboxG) hproperG {G} id (fun _ => 1) (fun _ _ _ _ h => h) (by
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
  exact hcharge.trans hsumZ

#print axioms bound_with_cut

end

end Shared50CycleBound
end Merged_Shared50CycleBound

-- merged module Shared50CycleFour
section Merged_Shared50CycleFour

namespace Shared50CycleFour
noncomputable section
open Final50Price (SmallFactor primaryBox taylorLength)
open Final50GeometryCut (membershipTest)
open Final50GeometryCut_2 (Branch Slice4 budget4)
open K1_13 (Row Shape shape InBox chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators
open private surface_slice_sum ambient_degree from ProximityPrize.SubmissionLower.Final50GeometryCut

theorem bound_with_cut (h1 : K1_13_6_2_3.c1)
    (h2 : K1_13_6_2_3.c2) (h3 : K1_13_6_2_3.c3)
    (f Q cut : Row 4) (l : ℕ) (hf : SmallFactor f) (hproper : ¬ f ∣ cut)
    (q : Shape) (hq : ChamberBox q) (hQ : InBox (shape cut) q)
    (weight : Ideal GeoJets → ℕ)
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hT : ∀ b ∈ F, Box4 (chart (taylorLength + 1) (shape f).chamber) b.member ∧
      (∀ p ∈ T b, b.Contains p) ∧ Slice4 b (T b))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal f cut).IsMinimalPrime b.surface,
       (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal f cut) b.surface h.isPrime) :
    let p := (shape f).chamber
    (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight * (T b).card : ℕ) : ℚ)) ≤
      (mixed32 p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p) : ℚ) / 32 := by
  classical
  dsimp only
  let p := (shape f).chamber
  let r := chart (taylorLength + 1) p
  let s := chart (taylorLength + 2) p
  have hp : ChamberBox p :=
    ⟨(K1_13_7_1.shape_chamber f).1, (K1_13_7_1.shape_chamber f).2, hf.2.1⟩
  have hr : ChamberBox r := chart_box _ _ (Nat.zero_lt_succ _)
  have hs : ChamberBox s := chart_box _ _ (Nat.zero_lt_succ _)
  have hboxes : ∀ q ∈ [r,s], ChamberBox q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact hq.elim (fun h => h ▸ hr) (fun h => h ▸ hs)
  let J := intersectionIdeal f cut
  let H : Ideal GeoJets := Ideal.span {toGeneric f}
  have hpair := K1_13_7_1.proper_generic f cut hf.1 hproper
  have hf0 : toGeneric f ≠ 0 := by
    intro hz
    exact hf.1.ne_zero (K1_13_7_1.toGeneric_injective (hz.trans (map_zero _).symm))
  have hregF : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) (toGeneric f)) :=
    regular_cut (by infer_instance) (by simpa using hf0)
  have hregQ := pair_regular f cut hpair
  have hH : dimension H ≤ 3 := by
    simpa [H, dimension_bot] using cut_dimension hregF
  have hJ : dimension J ≤ 2 := by
    rw [show J = H ⊔ Ideal.span {toGeneric cut} from intersection_eq f cut]
    have hdrop : dimension (H ⊔ Ideal.span {toGeneric cut}) ≤ dimension H - 1 := cut_dimension hregQ
    exact hdrop.trans (by omega)
  let surfaces := F.image Branch.surface
  let fiber (P : Ideal GeoJets) := F.filter (fun b => b.surface = P)
  let cost (b : Branch f Q l) : ℚ := ((b.weight * (T b).card : ℕ) : ℚ)
  have hsurface (P : Ideal GeoJets) (hP : P ∈ surfaces) :
      J.IsMinimalPrime P ∧ weight P ≤ localWeight J P ∧
      (∑ b ∈ fiber P, cost b) ≤ mixedDegree P [r,s] := by
    obtain ⟨ref, href, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hmin, hlen⟩ := hcut ref href
    have hl : (weight ref.surface : ℕ∞) ≤ (localWeight J ref.surface : ℕ∞) := by
      rw [weight_cast hmin]
      exact hlen
    refine ⟨hmin, ENat.natCast_le_natCast.mp hl, ?_⟩
    exact surface_slice_sum h2 h3 ref (surface_dimension hf0 hpair hmin) _ T
      (fun _ hb => (Finset.mem_filter.mp hb).2) (hT ref href).1
      (fun b hb => (hT b (Finset.mem_filter.mp hb).1).2)
  change (∑ b ∈ F, (weight b.surface : ℚ) * cost b) ≤ (mixed32 p q r s : ℚ) / 32
  calc
    _ = ∑ P ∈ surfaces, (weight P : ℚ) * ∑ b ∈ fiber P, cost b := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := Branch.surface)
        (fun b hb => Finset.mem_image_of_mem Branch.surface hb)
        (fun b => (weight b.surface : ℚ) * cost b)]
      apply Finset.sum_congr rfl
      intro P _
      change (∑ b ∈ fiber P, (weight b.surface : ℚ) * cost b) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      simp [(Finset.mem_filter.mp hb).2]
    _ ≤ ∑ P ∈ surfaces, (localWeight J P : ℚ) * mixedDegree P [r,s] := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨_, hl, hsum⟩ := hsurface P hP
      have hnonneg : 0 ≤ ∑ b ∈ fiber P, cost b := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hnonneg).trans
        (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
    _ ≤ mixedDegree J [r,s] := h3 J [r,s] hboxes (by simpa using hJ) surfaces
      (fun P hP => (hsurface P hP).1)
    _ ≤ mixedDegree H [q,r,s] := by
      rw [show J = H ⊔ Ideal.span {toGeneric cut} from intersection_eq f cut]
      exact h2 H q [r,s] hq hboxes (by simpa using hH) _ (generic_box hQ) hregQ
    _ ≤ mixedDegree (⊥ : Ideal GeoJets) [p,q,r,s] := by
      rw [show H = (⊥ : Ideal GeoJets) ⊔ Ideal.span {toGeneric f} by simp [H]]
      apply h2 _ p [q,r,s] hp _ (by simp) _ _ hregF
      · intro u hu
        exact (List.mem_cons.mp hu).elim (fun h => h ▸ hq) (hboxes u)
      · exact generic_box ⟨le_max_left _ _, le_rfl, le_rfl⟩
    _ ≤ _ := ambient_degree h1 hp hq hr hs

#print axioms bound_with_cut
end
end Shared50CycleFour
end Merged_Shared50CycleFour

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

#print axioms Data.pieces
#print axioms Data.bent
end
end Shared50Tally