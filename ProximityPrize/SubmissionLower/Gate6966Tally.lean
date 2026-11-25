import ProximityPrize.SubmissionLower.Gate6966Tilted
import ProximityPrize.SubmissionLower.Low6966SharedTallyNew

set_option Elab.async false

-- merged module Gate6966Ordinary
section Merged_Gate6966Ordinary

set_option autoImplicit false
set_option Elab.async false

namespace Gate6966
noncomputable section

open Low6966Prices (SmallFactor primaryBox taylorLength)
open Low6966GeometryCut (membershipTest)
open Low6966GeometryCut_2 (Branch Slice4 budget4)
open K1_13 (Row Shape shape InBox chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators
open Low6966GeometryCut_2_2 (surface_slice_sum ambient_degree)

theorem ordinary_bound_with_cut₂ (h1 : K1_13_6_2_3.c1)
    (h2 : K1_13_6_2_3.c2) (h3 : K1_13_6_2_3.c3)
    (f Q G₁ G₂ : Row 4) (l : ℕ) (hf : SmallFactor f) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (q₁ q₂ : Shape) (hq₁ : ChamberBox q₁) (hq₂ : ChamberBox q₂)
    (hQ₁ : InBox (shape G₁) q₁) (hQ₂ : InBox (shape G₂) q₂)
    (weight : Ideal GeoJets → ℕ)
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hT : ∀ b ∈ F, Box4 (chart (taylorLength + 1) (shape f).chamber) b.member ∧
      (∀ p ∈ T b, b.Contains p) ∧ Slice4 b (T b))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime b.surface,
       (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) b.surface h.isPrime) :
    (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight * (T b).card : ℕ) : ℚ)) ≤
      (mixed32 q₁ q₂ (chart (taylorLength + 1) (shape f).chamber)
        (chart (taylorLength + 2) (shape f).chamber) : ℚ) / 32 := by
  classical
  let p := (shape f).chamber
  let r := chart (taylorLength + 1) p
  let s := chart (taylorLength + 2) p
  have hr : ChamberBox r := chart_box _ _ (Nat.zero_lt_succ _)
  have hs : ChamberBox s := chart_box _ _ (Nat.zero_lt_succ _)
  have hboxes : ∀ q ∈ [r,s], ChamberBox q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact hq.elim (fun h => h ▸ hr) (fun h => h ▸ hs)
  let J := intersectionIdeal G₁ G₂
  let H : Ideal GeoJets := Ideal.span {toGeneric G₁}
  have hf0 : toGeneric G₁ ≠ 0 := K1_13_6_3_6.toGeneric_ne_zero hG₁
  have hregF : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) (toGeneric G₁)) :=
    regular_cut (by infer_instance) (by simpa using hf0)
  have hregQ := pair_regular G₁ G₂ hrel
  have hH : dimension H ≤ 3 := by
    simpa [H, dimension_bot] using cut_dimension hregF
  have hJ : dimension J ≤ 2 := by
    rw [show J = H ⊔ Ideal.span {toGeneric G₂} from intersection_eq G₁ G₂]
    have hdrop : dimension (H ⊔ Ideal.span {toGeneric G₂}) ≤ dimension H - 1 := cut_dimension hregQ
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
    exact surface_slice_sum h2 h3 ref (surface_dimension hf0 hrel hmin) _ T
      (fun _ hb => (Finset.mem_filter.mp hb).2) (hT ref href).1
      (fun b hb => (hT b (Finset.mem_filter.mp hb).1).2)
  change (∑ b ∈ F, (weight b.surface : ℚ) * cost b) ≤ (mixed32 q₁ q₂ r s : ℚ) / 32
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
    _ ≤ mixedDegree H [q₂,r,s] := by
      rw [show J = H ⊔ Ideal.span {toGeneric G₂} from intersection_eq G₁ G₂]
      exact h2 H q₂ [r,s] hq₂ hboxes (by simpa using hH) _ (generic_box hQ₂) hregQ
    _ ≤ mixedDegree (⊥ : Ideal GeoJets) [q₁,q₂,r,s] := by
      rw [show H = (⊥ : Ideal GeoJets) ⊔ Ideal.span {toGeneric G₁} by simp [H]]
      apply h2 _ q₁ [q₂,r,s] hq₁ _ (by simp) _ _ hregF
      · intro u hu
        exact (List.mem_cons.mp hu).elim (fun h => h ▸ hq₂) (hboxes u)
      · exact generic_box hQ₁
    _ ≤ _ := ambient_degree h1 hq₁ hq₂ hr hs

end
end Gate6966

end Merged_Gate6966Ordinary

-- merged module Gate6966Tally
section Merged_Gate6966Tally

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Gate6966
noncomputable section

open P3 (K)
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo)
open Low6966GeometryCut (CutInput)
open Low6966GeometryCut_2 (Branch)
open Low6966Prices (taylorLength)
open Low6966SharedTally (Data)
open scoped Polynomial BigOperators

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

theorem tilted_pair_tally (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (G₁ G₂ : Row 4) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (weight : Ideal GeoJets → ℕ) (htilt : Low6966Prices.tiltedFits (shape f))
    (q₁ q₂ : Shape) (hQ₁ : InBox (shape G₁) q₁) (hQ₂ : InBox (shape G₂) q₂)
    (hq₁ : Low48BentLattice.Chamber (q₁, 0)) (hq₂ : Low48BentLattice.Chamber (q₂, 0))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime b.surface,
      (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) b.surface h.isPrime) :
    1920 * (∑ b ∈ F, weight b.surface * (b.weight * (D.points b).card)) ≤
      tiltedPair (shape f).chamber q₁ q₂ := by
  let p := (shape f).chamber
  have ht : 1 ≤ p.t := input.small.2.1
  have hfamily := caps₂_chamber (K1_13_7_1.shape_chamber f).1 ht htilt.1 hq₁ hq₂
  let R := Low48BentCycle.rawFamily (caps₂ p q₁ q₂)
  let B := Low48BentCycle.capFamily (caps₂ p q₁ q₂)
  have h := bound_with_cut₂ (R := R) (B := B) ordinary_doubled₂ f Q G₁ G₂ l hG₁ hrel weight
    (Low48BentCycle.old_section hQ₁) (Low48BentCycle.old_section hQ₂)
    F D.points (fun b hb => D.bent input (chart₂ q₁ q₂ ht) b (hF hb)) hcut
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℚ) ≤ 60 * 32)).trans
    (ordinary_budget₂ hfamily)
  norm_num only [show (60 : ℚ) * 32 = 1920 by norm_num] at hh
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, ← Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc] using hh

theorem ordinary_pair_tally (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (G₁ G₂ : Row 4) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (q₁ q₂ : Shape) (hq₁ : K1_13_6_2_3.ChamberBox q₁) (hq₂ : K1_13_6_2_3.ChamberBox q₂)
    (hQ₁ : InBox (shape G₁) q₁) (hQ₂ : InBox (shape G₂) q₂)
    (weight : Ideal GeoJets → ℕ)
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime b.surface,
      (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) b.surface h.isPrime) :
    32 * (∑ b ∈ F, weight b.surface * (b.weight * (D.points b).card)) ≤
      mixed32 q₁ q₂ (chart (taylorLength + 1) (shape f).chamber)
        (chart (taylorLength + 2) (shape f).chamber) := by
  have h := ordinary_bound_with_cut₂ K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q G₁ G₂ l input.small hG₁ hrel q₁ q₂ hq₁ hq₂ hQ₁ hQ₂ weight F D.points
    (fun b hb => D.four input b (hF hb)) hcut
  have h' := (le_div_iff₀ (by norm_num : (0 : ℚ) < 32)).mp h
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, ← Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc] using h'

theorem product_weight_admissible (G₁ G₂ : Row 4) (hF : toGeneric G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂)) (P : Ideal GeoJets) {a c : ℕ}
    (hP : (intersectionIdeal G₁ G₂).IsMinimalPrime P)
    (h₁ : @VanishesTo GeoJets _ P hP.isPrime (toGeneric G₁) a)
    (h₂ : @VanishesTo GeoJets _ P hP.isPrime (toGeneric G₂) c) :
    ((a * c : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) P hP.isPrime :=
  Shared50Multiplicity.cycleLength_ge_product_of_minimal hP hF hrel h₁ h₂

end
end Gate6966

end Merged_Gate6966Tally
