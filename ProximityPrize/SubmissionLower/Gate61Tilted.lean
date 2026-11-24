import ProximityPrize.SubmissionLower.R6960Low6960RetainedAssembly
import ProximityPrize.SubmissionLower.R6960Low6960SharedBentCaps

-- merged module Gate61Comparison
section Merged_Gate61Comparison

set_option autoImplicit false
set_option Elab.async false

namespace Gate61
noncomputable section

open K1_13 (Row)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (sectionIdeal cylinder oldEmbedding OfDim LengthAt)
open K1_13_6_2_4_4 (cylinder_regular cylinder_dimension cylinder_minimal cylinder_length)

theorem pair_regular₂ {F G : GeoJets} (hrel : IsRelPrime F G) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {F}) G) := by
  apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
  intro x hx
  obtain ⟨D, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (hrel.dvd_of_dvd_mul_left hx))

theorem cylinder_comparison₂ (f Q : Row 4) (hF : toGeneric f ≠ 0)
    (hrel : IsRelPrime (toGeneric f) (toGeneric Q)) :
    let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
    let J := sectionIdeal A (oldEmbedding (toGeneric Q))
    IsLeftRegular (Ideal.Quotient.mk A (oldEmbedding (toGeneric Q))) ∧
    ∀ P : Ideal GeoJets, ∀ h : (intersectionIdeal f Q).IsMinimalPrime P,
      OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P),
          cycleLength (intersectionIdeal f Q) P h.isPrime ≤ LengthAt J (cylinder P) hc.isPrime := by
  let F : Ideal GeoJets := Ideal.span {toGeneric f}
  have hA : sectionIdeal ⊥ (oldEmbedding (toGeneric f)) = cylinder F := by
    simp [sectionIdeal, cylinder, F, Ideal.map_span]
  have hJ : sectionIdeal (sectionIdeal ⊥ (oldEmbedding (toGeneric f))) (oldEmbedding (toGeneric Q)) =
      cylinder (intersectionIdeal f Q) := by
    rw [hA, intersectionIdeal, Ideal.span_insert]
    simp [sectionIdeal, cylinder, F, Ideal.map_sup, Ideal.map_span]
  have hreg := pair_regular₂ hrel
  dsimp only
  constructor
  · exact (congrArg (fun I : Ideal GeoJets5 =>
      IsLeftRegular (Ideal.Quotient.mk I (oldEmbedding (toGeneric Q)))) hA).mpr
      (cylinder_regular hreg)
  · intro P hP
    refine ⟨cylinder_dimension (K1_13_6_1_4.pair_dimension hF hrel hP), ?_⟩
    apply (congrArg (fun I : Ideal GeoJets5 => ∃ hc : I.IsMinimalPrime (cylinder P),
      cycleLength (intersectionIdeal f Q) P hP.isPrime ≤ LengthAt I (cylinder P) hc.isPrime) hJ).mpr
    exact ⟨cylinder_minimal hP, (cylinder_length (intersectionIdeal f Q) P hP.isPrime).le⟩

end
end Gate61

end Merged_Gate61Comparison

-- merged module Gate61Tilted
section Merged_Gate61Tilted

set_option autoImplicit false
set_option Elab.async false

namespace Gate61
noncomputable section

open Low48BentCycle (Family mixedDegree properCut cycleComparison divisorBound diagonalExponents
  rawFamily capFamily capSum ambient_cap integral)
open Low48BentLattice (Cap Allowed Chamber latticePoints)
open Low48BentSupport (graph lifted)
open Low6960Prices (SmallFactor taylorLength)
open Low6960GeometryCut_2 (Branch)
open Low6960GeometryCut_2_3 (graphLift chart_index_eq graphLift_same_chart
  membership_same_chart graphLift_comap member_proper_on_graph)
open K1_13 (Row Shape shape)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5)
open K1_13_6_2_4 (Exponent Component DimLE OfDim LengthAt ambient_dim cylinder cylinder_injective
  dim_le_after_section oldEmbedding pointIdeal sectionIdeal)
open K1_13_6_2_4_1 (positiveDiagonal)
open Low6960ActiveCycle (Section Doubled Slice Chart)
open MvPolynomial
open scoped BigOperators Pointwise
open Low6960ActiveCycle (square_support bound_marks)
open Low48BentCycle (slots ambient_list)

def caps₂ (p q₁ q₂ : Shape) : Fin 5 → Cap :=
  ![(q₁, 0), (q₂, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]

theorem caps₂_chamber {p q₁ q₂ : Shape} (hb : p.j ≤ p.b) (ht : 1 ≤ p.t) (hj : 3 * p.t + 3 ≤ p.j)
    (hq₁ : Chamber (q₁, 0)) (hq₂ : Chamber (q₂, 0)) :
    ∀ i, Chamber (caps₂ p q₁ q₂ i) := by
  intro i
  fin_cases i
  · exact hq₁
  · exact hq₂
  · exact Low48BentSupport.graph_chamber ht hj
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 4)
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 3)

private theorem last_allowed₂ {p q₁ q₂ : Shape}
    (v : Fin 5) : Allowed (caps₂ p q₁ q₂ 4) (Finsupp.single v 1) := by
  let k := taylorLength - 3
  have hb' : 1 ≤ 1 + k * (p.b - 1) := by omega
  have hj' : 4 ≤ 4 + k * (p.j - 2) := by omega
  have ht' : 2 ≤ 2 + k * p.t := by omega
  have hd' : 1 ≤ min (1 + k) ((2 + k * p.t) / 2) := by omega
  fin_cases v <;> simp [caps₂, lifted, Allowed, ← show k = taylorLength - 3 from rfl] <;> omega

theorem ordinary_doubled₂ {p q₁ q₂ : Shape} :
    Doubled (rawFamily (caps₂ p q₁ q₂)) (capFamily (caps₂ p q₁ q₂)) where
  zero_mem i := by simp [rawFamily, Allowed]
  pair_mem _ _ ha _ hb := Low48BentSupport.raw_add ha hb
  last_coordinate := last_allowed₂

def tiltedPair (p q₁ q₂ : Shape) : ℕ :=
  Low6960Prices.ambientMix [(q₁, 0), (q₂, 0), Low6960Prices.bentGraph p,
    Low6960Prices.bentLift (taylorLength - 4) p, Low6960Prices.bentLift (taylorLength - 3) p]

theorem tiltedPair_self (p q : Shape) : tiltedPair p p q = Low6960Prices.tiltedSurface p q := rfl

private def integr₂ (a : Cap) : ℚ := integral a

private def signed₂ (p q₁ q₂ : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps₂ p q₁ q₂))

private theorem base_signed₂ (p q₁ q₂ : Shape) :
    tiltedPair p q₁ q₂ = (signed₂ p q₁ q₂).toNat := by
  change Low48Price.ambientMix (slots.map (caps₂ p q₁ q₂)) = _
  exact ambient_list (caps₂ p q₁ q₂)

private theorem base_normalize₂ (p q₁ q₂ : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr₂ (capSum (caps₂ p q₁ q₂) (positiveDiagonal J))) = (signed₂ p q₁ q₂ : ℚ) := by
  have H := Low48BentPolarization.remove_baseline (caps₂ p q₁ q₂)
  change _ = _ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr₂ (capSum (caps₂ p q₁ q₂) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr₂ (Low48BentLattice.Sum J (caps₂ p q₁ q₂)) from H]
  unfold signed₂
  push_cast
  rfl

private theorem ordinary_coeff₂ (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5 = integr₂ a / 60 := by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr₂ integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget₂ {p q₁ q₂ : Shape} (h : ∀ i, Chamber (caps₂ p q₁ q₂ i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps₂ p q₁ q₂)) ⊥ Finset.univ ≤
      (tiltedPair p q₁ q₂ : ℚ) := by
  rw [mul_assoc, ambient_cap (caps₂ p q₁ q₂) h (fun a => integr₂ a / 60) ordinary_coeff₂]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize₂, base_signed₂]
  exact_mod_cast (show signed₂ p q₁ q₂ ≤ ((signed₂ p q₁ q₂).toNat : ℤ) by omega)

theorem chart₂ {f Q : Row 4} {l : ℕ} (q₁ q₂ : Shape) (ht : 1 ≤ (shape f).t)
    (b : Branch f Q l) :
    Chart (rawFamily (caps₂ (shape f).chamber q₁ q₂)) b := by
  have h := Low6960ActiveCycle.ordinary_chart ht b
  exact h

private theorem initial_bound₂ {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (G₁ G₂ : Row 4) (weight : Ideal GeoJets → ℕ) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (hbox₁ : Section R 0 (oldEmbedding (toGeneric G₁)))
    (hbox₂ : Section R 1 (oldEmbedding (toGeneric G₂))) (S : Finset (Ideal GeoJets))
    (hS : ∀ P ∈ S, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime P,
      (weight P : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) P h.isPrime) :
    (∀ P ∈ S, (cylinder P).IsPrime ∧ OfDim (cylinder P) 3) ∧
      (∑ P ∈ S, (weight P : ℚ) * mixedDegree B (cylinder P) {2, 3, 4}) ≤
        mixedDegree B ⊥ Finset.univ := by
  classical
  let A := sectionIdeal ⊥ (oldEmbedding (toGeneric G₁))
  let J := sectionIdeal A (oldEmbedding (toGeneric G₂))
  have hF : toGeneric G₁ ≠ 0 := K1_13_6_3_6.toGeneric_ne_zero hG₁
  obtain ⟨hregQ, hAlgebra⟩ := cylinder_comparison₂ G₁ G₂ hF hrel
  have hregf : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets5)
      (oldEmbedding (toGeneric G₁))) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne hF
  have hAdim : DimLE A 4 := dim_le_after_section hregf ambient_dim
  have hJdim : DimLE J 3 := dim_le_after_section hregQ hAdim
  have hgeom (P : Ideal GeoJets) (hP : P ∈ S) :
      (cylinder P).IsPrime ∧ OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P), (weight P : ℕ∞) ≤ LengthAt J (cylinder P) hc.isPrime := by
    obtain ⟨h, hw⟩ := hS P hP
    obtain ⟨hd, hc, hl⟩ := hAlgebra P h
    exact ⟨hc.isPrime, hd, hc, hw.trans hl⟩
  refine ⟨fun P hP => ⟨(hgeom P hP).1, (hgeom P hP).2.1⟩, ?_⟩
  have hs := cycleComparison B hB.double_zero hB.double_coordinates J {2, 3, 4} hJdim S cylinder weight
    cylinder_injective.injOn (fun P hP => (hgeom P hP).2.2)
  have hcutQ := properCut B hB.double_zero A {2, 3, 4} 1 (by decide) hAdim
    (oldEmbedding (toGeneric G₂)) (fun m hm => hB.raw_mem (hbox₂ m hm)) (square_support hB hbox₂) hregQ
  have hcutf := properCut B hB.double_zero ⊥ {1, 2, 3, 4} 0 (by decide) ambient_dim
    (oldEmbedding (toGeneric G₁)) (fun m hm => hB.raw_mem (hbox₁ m hm)) (square_support hB hbox₁) hregf
  have hall : (insert (0 : Fin 5) {1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
  rw [hall] at hcutf
  exact hs.trans (hcutQ.trans hcutf)

theorem bound_with_cut₂ {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (f Q G₁ G₂ : Row 4) (l : ℕ) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (weight : Ideal GeoJets → ℕ)
    (hbox₁ : Section R 0 (oldEmbedding (toGeneric G₁)))
    (hbox₂ : Section R 1 (oldEmbedding (toGeneric G₂)))
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hF : ∀ b ∈ F, Section R 2 b.graph ∧
      (∃ E, Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member)) ∧
      (∀ p ∈ T b, b.Contains p) ∧ Slice R b (T b))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime b.surface,
      (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) b.surface h.isPrime) :
    (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight : ℚ) * (T b).card)) ≤
      mixedDegree B ⊥ Finset.univ := by
  classical
  have hgraph := @Low6960GeometryCut_2_3_1.proof f Q l
  have hmember := @Low6960GeometryCut_2_3_2.proof f Q l
  let S := F.image Branch.surface
  let fibre (P : Ideal GeoJets) := F.filter fun b => b.surface = P
  let charge (b : Branch f Q l) : ℚ := (b.weight : ℚ) * (T b).card
  obtain ⟨hZ, hsumZ⟩ := initial_bound₂ hB G₁ G₂ weight hG₁ hrel hbox₁ hbox₂ S (by
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
    have hEbound := divisorBound B hB.double_zero hB.double_coordinates G {4} 3 hG.minimal.isPrime
      (by decide) hGdim E (fun m hm => hB.raw_mem (hboxE m hm)) (square_support hB hboxE) hproperE
      (fibre b.surface) C Branch.weight inj (fun c hc => (hC c (Finset.mem_filter.mp hc).2).1)
    have hGbound := divisorBound B hB.double_zero hB.double_coordinates (cylinder b.surface) {3, 4} 2
      hZprime (by decide) hZdim
      b.graph (fun m hm => hB.raw_mem (hboxG m hm)) (square_support hB hboxG) hproperG {G} id
      (fun _ => 1) (fun _ _ _ _ h => h) (by
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

end
end Gate61

end Merged_Gate61Tilted
