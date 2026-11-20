import ProximityPrize.SubmissionLower.Fast061
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921Fast035
import ProximityPrize.SubmissionLower.Hi6921Fast048
import ProximityPrize.SubmissionLower.Hi6921Fast051
import ProximityPrize.SubmissionLower.Hi6921Fast057
import ProximityPrize.SubmissionLower.Hi6921P32Split
import ProximityPrize.SubmissionLower.Hi6921P34Cutter
import ProximityPrize.SubmissionLower.Hi6921P3Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3_4Split
set_option autoImplicit true
namespace H21_3_4

noncomputable section

open K21 H21 H21_3 H21_3_2 Polynomial
open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

/-- Factor both rows and retain the residual orders off the high ordinary factors. -/
def c1 : Prop :=
  ∀ (h : ℕ) (rows : Banks) (i : Fin 4) (B : BufferedPair h rows i)
    (r : ℕ), 1 ≤ r → r ≤ reserve i + 1 → Nonempty (ThresholdPair i B.cheap B.layered r)

export _root_.K1_14_3_4 (c2)

export _root_.K1_14_3_4 (c3)

export _root_.K1_14_3_4 (c4)

export _root_.K1_14_3_4 (c5)

open private mass_mono from ProximityPrize.SubmissionLower.Fast061

open private mass_union from ProximityPrize.SubmissionLower.Fast061

open private mass_biUnion from ProximityPrize.SubmissionLower.Fast061

open private heavy_mass from ProximityPrize.SubmissionLower.Fast061

private theorem threshold_cap (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    {h : ℕ} {rows : Banks} {i : Fin 4} (B : BufferedPair h rows i) (qs : Finset Surface)
    (hall : ∀ q ∈ qs, Parent q ∧ Compatible B.cheap B.layered q ∧
      OrderAt q B.cheap (reserve i + 1) ∧ OrderAt q B.layered (reserve i + 1))
    (r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ reserve i + 1) :
    let b := (cheapShape i).B / (r : ℚ)
    let u := (cheapShape i).U / (r : ℚ)
    let d := ((reserve i + 2 - r : ℕ) : ℚ)^2
    MassCap qs (b + residualSeed (cheapShape i) (layeredShape i) / d)
      (u + residualOrdinate (cheapShape i) (layeredShape i) / d)
      (2*b*u + residualMixed (cheapShape i) (layeredShape i) / d) := by
  classical
  obtain ⟨D⟩ := h1 h rows i B r hr hr'
  let T (f : Equation) := qs.filter fun q => C f ∈ q.asIdeal
  let H := D.heavy.biUnion T
  have hsub : H ⊆ qs := by
    intro q hq
    obtain ⟨f, _, hf⟩ := Finset.mem_biUnion.mp hq
    exact (Finset.mem_filter.mp hf).1
  have high := heavy_mass T D.seed_budget D.y_budget (fun f hf => by
    obtain ⟨hi, hd, hp, hP, hQ⟩ := D.factors f hf
    obtain ⟨g, a, hg, proper, left_caps, right_caps⟩ := h2 f hi hd hp
    have weighted := h4 _ _ proper (T f) 1 (by decide) (fun q hq => by
      obtain ⟨hq', hm⟩ := Finset.mem_filter.mp hq
      obtain ⟨hparent, hc, _⟩ := hall q hq'
      exact ⟨hparent, by simpa only [Nat.cast_one] using
        intersectionLength_one hm (graph_test_of_compatible hparent hc hi hd hp hP hQ hm g a hg)⟩)
    obtain ⟨hseed, hord, hmix⟩ := h5 _ _ _ _ proper left_caps right_caps (Nat.zero_le _) hd
    constructor
    · simpa [residualSeed] using (weighted .seed (by intro e; cases e)).trans hseed
    · simpa [residualOrdinate] using (weighted .ordinate (by intro e; cases e)).trans hord
    · simpa [residualMixed, two_mul, add_mul] using (weighted .mixed (by intro e; cases e)).trans hmix)
  let k := reserve i + 2 - r
  have hk : 0 < k := by dsimp [k]; omega
  have hk₂ : 0 < k^2 := pow_pos hk 2
  have weighted := h4 D.left D.right D.proper (qs \ H) (k^2) hk₂ (fun q hq => by
    obtain ⟨hq', hn⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hparent, _, hP, hQ⟩ := hall q hq'
    have ⟨hF, hG⟩ := D.residual_order q hparent hP hQ (fun f hf hm =>
      hn (Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_filter.mpr ⟨hq', hm⟩⟩))
    exact ⟨hparent, by simpa only [Nat.cast_pow] using h3 _ _ q k D.proper hparent hk hF hG⟩)
  obtain ⟨hseed, hord, hmix⟩ := h5 _ _ _ _ D.proper D.left_caps D.right_caps
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
  have add_bounds (s : Slice) (hs : s ≠ .jets) (ordinary residual : ℚ) (hm : mass H s ≤ ordinary)
      (hd : (pairSectionDegree D.left D.right s : ℚ) ≤ residual) :
      mass qs s ≤ ordinary + residual / (k : ℚ)^2 := by
    have hw := (weighted s hs).trans hd
    rw [Nat.cast_pow, mul_comm] at hw
    have hlow := (le_div_iff₀ (show 0 < (k : ℚ)^2 by positivity)).mpr hw
    linarith only [mass_sdiff hsub s, hm, hlow]
  exact ⟨add_bounds .seed (by intro e; cases e) _ _ high.seed hseed,
    add_bounds .ordinate (by intro e; cases e) _ _ high.ordinate hord,
    add_bounds .mixed (by intro e; cases e) _ _ high.mixed hmix⟩

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    H21_3.c4 := by
  intro h rows i B qs hall
  have H := threshold_cap h1 h2 h3 h4 h5 B qs hall
  let axisThreshold : Fin 4 → ℕ := ![1, 1, 1, 2]
  let mixedThreshold : Fin 4 → ℕ := ![1, 2, 3, 6]
  have ranges (j : Fin 4) :
      (1 ≤ axisThreshold j ∧ axisThreshold j ≤ reserve j + 1) ∧
      (1 ≤ mixedThreshold j ∧ mixedThreshold j ≤ reserve j + 1) := by
    fin_cases j <;> decide
  obtain ⟨⟨ha, ha'⟩, ⟨hz, hz'⟩⟩ := ranges i
  have axis := H _ ha ha'
  have mixed := H _ hz hz'
  refine ⟨axis.seed.trans ?_, axis.ordinate.trans ?_, mixed.mixed.trans ?_⟩ <;>
    fin_cases i <;>
    norm_num [cheapShape, layeredShape, reserve, residualSeed, residualOrdinate, residualMixed,
      seedMassCap, ordinateMassCap, mixedMassCap, axisThreshold, mixedThreshold]

end
end H21_3_4
end High_K1_14_3_4Split
