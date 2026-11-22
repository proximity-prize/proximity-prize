import ProximityPrize.SubmissionLower.Low53At2389GeometryCut
set_option Elab.async false

namespace Low53At2389SharedCycleFour
noncomputable section
open Low53At2389Price (SmallFactor primaryBox taylorLength)
open Low53At2389GeometryCut (membershipTest)
open Low53At2389GeometryCut_2 (Branch Slice4 budget4)
open K1_13 (Row Shape shape InBox chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators
open private surface_slice_sum ambient_degree from ProximityPrize.SubmissionLower.Low53At2389GeometryCut

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
end Low53At2389SharedCycleFour
