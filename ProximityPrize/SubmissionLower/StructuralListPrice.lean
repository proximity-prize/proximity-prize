import ProximityPrize.SubmissionLower.StructuralListArithmetic

set_option maxRecDepth 6000

namespace StructuralList

open CJ0 CJ0_4 MvPolynomial
open scoped BigOperators
open private chart_degree surfaceBound from ProximityPrize.SubmissionLower.ListProofA

noncomputable section

def bandVolume (s : Source) (L b j c : ℕ) : ℚ :=
  volumeTotal s L * b + volumeIndex s L * j + volumeTop s L * c

def slicePrice (A : ℕ) (s : Source) (L b j c : ℕ) : ℚ :=
  curveFactor A * bandVolume s L b j c + (totalCap s L : ℚ) * b

theorem volume_nonneg (s : Source) (hs : ShapeOK s) (L : ℕ) (hL : 3 ≤ L) :
    0 ≤ volumeTotal s L ∧ 0 ≤ volumeIndex s L ∧ 0 ≤ volumeTop s L := by
  have hd : (indexCap s L : ℚ) ≤ totalCap s L := by exact_mod_cast indexCap_le_totalCap s hs L hL
  have he : 2 * (topCap s L : ℚ) ≤ indexCap s L := by exact_mod_cast twice_topCap_le s L
  have ha : 0 ≤ (totalCap s L : ℚ) := Nat.cast_nonneg _
  have ht : 0 ≤ (topCap s L : ℚ) := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · unfold volumeTotal
    exact mul_nonneg (by positivity) (by linarith)
  · unfold volumeIndex
    exact mul_nonneg ht (by linarith)
  · unfold volumeTop
    exact mul_nonneg (by linarith) (by linarith)

theorem volumeDegree (s : Source) (hs : ShapeOK s) (L : ℕ) (hL : 3 ≤ L)
    (T : Chart 2) (hT : ChartOK T) (hb : ShortBand s L T) :
    affineDegree T.ideal ≤ bandVolume s L T.equation.totalDegree
      (T.equation.weightedTotalDegree Fin.val) (T.equation.degreeOf (Fin.last 2)) := by
  simpa only [surfaceBound, bandVolume, volumeTotal, volumeIndex, volumeTop] using
    (chart_degree CJ0_4_1.proof CJ0_4_2.proof T hT (CJ0_4.image_geometry T hT).2
      (totalCap s L) (indexCap s L) (topCap s L) (indexCap_le_totalCap s hs L hL)
      (twice_topCap_le s L) (CJ0_4.mem_bandSpace.mpr hb.denominator)
      (fun i => CJ0_4.mem_bandSpace.mpr (hb.numerator i)))

theorem weighted_price (A common : ℕ) (s : Source) (hs : ShapeOK s)
    (hJ : 2 * s.C + 1 ≤ s.J) (hA : k + 5 ≤ A) (hAn : A ≤ n) (hc : common ≤ N)
    (b j c : ℕ) :
    incidenceFactor A common * slicePrice A s (shortLength common) b j c ≤
      baseFactor A * slicePrice A s k b j c := by
  let L := shortLength common
  have hL : 3 ≤ L := le_max_left ..
  have hK : L ≤ k := max_le (by decide) (Nat.sub_le ..)
  obtain ⟨ha, hu, hv, hw⟩ := volumeScale s hs L hL hK hJ
  have hscl : (k : ℚ) * slicePrice A s L b j c ≤ (L : ℚ) * slicePrice A s k b j c := by
    have hui := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg b)
    have hvi := mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg j)
    have hwi := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg c)
    have hai := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg b)
    have hcurve : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hvol := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hui hvi) hwi) hcurve
    unfold slicePrice bandVolume
    nlinarith only [hvol, hai]
  have hp : 0 ≤ slicePrice A s k b j c := by
    obtain ⟨hu, hv, hw⟩ := volume_nonneg s hs k (by decide)
    have hcurve : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    unfold slicePrice bandVolume
    positivity
  have h := mul_le_mul_of_nonneg_left hscl (show 0 ≤ incidenceFactor A common by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have h' := mul_le_mul_of_nonneg_right (incidenceLength A common hA hAn hc) hp
  have h'' : (k : ℚ) * (incidenceFactor A common * slicePrice A s L b j c) ≤
      (k : ℚ) * (baseFactor A * slicePrice A s k b j c) := by
    nlinarith only [h, h']
  exact le_of_mul_le_mul_left h'' (by positivity)

theorem volume_full (s : Source) (hs : ShapeOK s) : bandVolume s k s.B s.J s.C = R₂ s := by
  have hda : D s ≤ a₀ s := indexCap_le_totalCap s hs k (by decide)
  have hde : 2 * e s ≤ D s := twice_topCap_le s k
  have hD' : D s ≤ 2*a₀ s := by omega
  have hJ' : s.J ≤ 2*s.B := by have := hs.total_index; omega
  have he' : e s ≤ D s := by omega
  have hC' : 2*s.C*e s ≤ s.C*D s + e s*s.J := by
    calc
      _ = s.C * (2*e s) := by ring
      _ ≤ s.C*D s := Nat.mul_le_mul_left _ hde
      _ ≤ _ := Nat.le_add_right _ _
  unfold bandVolume volumeTotal volumeIndex volumeTop
  rw [show totalCap s k = a₀ s by rfl, show indexCap s k = D s by rfl, show topCap s k = e s by rfl]
  dsimp [R₂]
  push_cast [Nat.cast_sub hD', Nat.cast_sub hJ', Nat.cast_sub he', Nat.cast_sub hC']
  ring

end

end StructuralList
