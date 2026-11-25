import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false

-- merged module StructuralListDefs
section Merged_StructuralListDefs
set_option Elab.async false
namespace StructuralList
open CJ0
def exponent (length : ℕ) : ℕ := max (2 * length - 7) (length - 2)
def totalCap (s : Source) (length : ℕ) : ℕ :=
  1 + exponent length * (s.B - 1)
def indexCap (s : Source) (length : ℕ) : ℕ :=
  exponent length * (s.J - 2) + length - 1
def topCap (s : Source) (length : ℕ) : ℕ :=
  min (exponent length * (s.C - 1) + length - 2) (indexCap s length / 2)
def InBand (s : Source) (length : ℕ) (P : InitialRing 2) : Prop :=
  P.totalDegree ≤ totalCap s length ∧
    P.weightedTotalDegree Fin.val ≤ indexCap s length ∧
    P.degreeOf (Fin.last 2) ≤ topCap s length
structure ShortBand (s : Source) (length : ℕ) (T : Chart 2) : Prop where
  denominator : InBand s length T.denominator
  numerator : ∀ i, InBand s length (T.numerator i)
end StructuralList

end Merged_StructuralListDefs

-- merged module StructuralListArithmetic
section Merged_StructuralListArithmetic

set_option Elab.async false
set_option maxRecDepth 6000

namespace StructuralList

open CJ0

def shortLength (common : ℕ) : ℕ := max 3 (k - common)

def incidenceFactor (A common : ℕ) : ℚ := (n - common : ℕ) / (A - common : ℕ)

def baseFactor (A : ℕ) : ℚ := (n : ℚ) / A

def curveFactor (A : ℕ) : ℚ := (errors A : ℚ) / gap A

def volumeTotal (s : Source) (length : ℕ) : ℚ :=
  2 * topCap s length * ((indexCap s length : ℚ) - topCap s length)

def volumeIndex (s : Source) (length : ℕ) : ℚ :=
  topCap s length * (2 * totalCap s length - 2 * indexCap s length + topCap s length)

def volumeTop (s : Source) (length : ℕ) : ℚ :=
  ((indexCap s length : ℚ) - 2 * topCap s length) *
    (2 * totalCap s length - indexCap s length)

def surfacePrice (A : ℕ) (s : Source) : ℚ :=
  baseFactor A * (curveFactor A * R₂ s + (s.B : ℚ) * totalCap s k)

def totalPrice (A : ℕ) (s : Source) : ℚ :=
  surfacePrice A s + curveFactor A * R₁ s + s.B + (H s : ℚ) ^ 2

def tariff (A : ℕ) (s : Source) : ℕ := ⌈totalPrice A s⌉₊

theorem indexCap_le_totalCap (s : Source) (hs : ShapeOK s) (L : ℕ) (hL : 3 ≤ L) :
    indexCap s L ≤ totalCap s L := by
  have hj : 2 ≤ s.J := by have := hs.index_top; have := hs.top_pos; omega
  have hb := hs.total_index
  have ht : L - 2 ≤ exponent L := le_max_right _ _
  have ht' := Nat.mul_le_mul_left (exponent L) (show s.J - 2 + 1 ≤ s.B - 1 by omega)
  rw [Nat.mul_add, Nat.mul_one] at ht'
  unfold indexCap totalCap
  omega

theorem twice_topCap_le (s : Source) (L : ℕ) : 2 * topCap s L ≤ indexCap s L := by
  have he : topCap s L ≤ indexCap s L / 2 := min_le_right _ _
  omega

private theorem topCap_eq (s : Source) (L : ℕ) (hL : 3 ≤ L)
    (hJ : 2 * s.C + 1 ≤ s.J) (hc : 0 < s.C) :
    topCap s L = exponent L * (s.C - 1) + L - 2 := by
  have ht : L - 2 ≤ exponent L := le_max_right _ _
  have hb := Nat.mul_le_mul_left (exponent L)
    (show 2 * (s.C - 1) + 1 ≤ s.J - 2 by omega)
  rw [Nat.mul_add, Nat.mul_one, show exponent L * (2 * (s.C - 1)) =
    2 * (exponent L * (s.C - 1)) by ring] at hb
  have hc' : 2 * (exponent L * (s.C - 1) + L - 2) ≤ indexCap s L := by
    unfold indexCap
    omega
  unfold topCap
  exact min_eq_left (by omega)

theorem incidenceLength (A common : ℕ) (hA : k + 5 ≤ A) (hAn : A ≤ n)
    (hc : common ≤ N) :
    incidenceFactor A common * shortLength common ≤ baseFactor A * k := by
  have hk : common < k := Nat.lt_succ_of_le hc
  have hcn : common ≤ n := by unfold k n at *; omega
  have hca : common < A := hk.trans_le (by omega)
  have hAq : (0 : ℚ) < A := by positivity
  have hx : (0 : ℚ) < (A - common : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hca
  unfold incidenceFactor baseFactor
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hx hAq]
  rw [Nat.cast_sub hcn, Nat.cast_sub hca.le]
  by_cases hlong : 3 ≤ k - common
  · unfold shortLength
    rw [max_eq_right hlong, Nat.cast_sub hk.le]
    have hcq : (0 : ℚ) ≤ common := by positivity
    have hcK : (common : ℚ) ≤ k := Nat.cast_le.mpr hk.le
    have hbound : (n : ℚ) ≤ n + k - common := by linarith
    have hnq : (0 : ℚ) ≤ n := by positivity
    have hknq : (k : ℚ) ≤ A := by exact_mod_cast (show k ≤ A by omega)
    have h1 := mul_le_mul_of_nonneg_left hbound (show (0 : ℚ) ≤ A by positivity)
    have h2 := mul_le_mul_of_nonneg_right hknq hnq
    have hd : (n : ℚ) * k ≤ (A : ℚ) * (n + k - common) := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left hd hcq]
  · unfold shortLength
    rw [max_eq_left (by omega : k - common ≤ 3), Nat.cast_ofNat]
    have hd : 6 ≤ A - common := by unfold k N at *; omega
    have hdq : (6 : ℚ) ≤ (A - common : ℕ) := by exact_mod_cast hd
    rw [Nat.cast_sub hca.le] at hdq
    have hAnq : (A : ℚ) ≤ 2 * k := by exact_mod_cast hAn
    have hnq : (0 : ℚ) ≤ n := by positivity
    have hkq : (0 : ℚ) ≤ k := by positivity
    have h1 := mul_le_mul_of_nonneg_right hAnq (show (0 : ℚ) ≤ n * 3 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hdq (show (0 : ℚ) ≤ n * k by positivity)
    change ((n : ℚ) - common) * 3 * A ≤ (n : ℚ) * k * ((A : ℚ) - common)
    calc
      _ ≤ (n : ℚ) * 3 * A := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) (by norm_num)) (by positivity)
      _ = (A : ℚ) * (n * 3) := by ring
      _ ≤ (2 * k : ℚ) * (n * 3) := h1
      _ = (n : ℚ) * k * 6 := by ring
      _ ≤ _ := h2

private theorem affine_scaled {L K m b : ℚ} (hLK : L ≤ K) (hb : b ≤ 0) :
    K * (m * L + b) ≤ L * (m * K + b) := by
  nlinarith only [mul_nonpos_of_nonpos_of_nonneg hb (sub_nonneg.mpr hLK)]

private theorem cap_forms (s : Source) (hs : ShapeOK s) (L : ℕ) (hL : 3 ≤ L)
    (hJ : 2 * s.C + 1 ≤ s.J) :
    ((totalCap s L : ℚ) = 1 + ↑(exponent L) * ((s.B : ℚ) - 1)) ∧
    ((indexCap s L : ℚ) = ↑(exponent L) * ((s.J : ℚ) - 2) + L - 1) ∧
    ((topCap s L : ℚ) = ↑(exponent L) * ((s.C : ℚ) - 1) + L - 2) := by
  have hc := hs.top_pos
  have hj : 2 ≤ s.J := by omega
  have hb : 1 ≤ s.B := by have := hs.total_index; omega
  unfold totalCap indexCap
  rw [topCap_eq s L hL hJ hc]
  push_cast [Nat.cast_sub hb, Nat.cast_sub hj, Nat.cast_sub (Nat.one_le_of_lt hc),
    Nat.cast_sub (by omega : 1 ≤ exponent L * (s.J - 2) + L),
    Nat.cast_sub (by omega : 2 ≤ exponent L * (s.C - 1) + L)]
  simp

private theorem expo_big {L : ℕ} (hL : 5 ≤ L) :
    (exponent L : ℚ) = 2 * (L : ℚ) - 7 := by
  unfold exponent
  rw [max_eq_left (by omega : L - 2 ≤ 2 * L - 7), Nat.cast_sub (by omega)]
  push_cast
  rfl

theorem volumeScale (s : Source) (hs : ShapeOK s) (L : ℕ) (hL : 3 ≤ L) (hK : L ≤ k)
    (hJ : 2 * s.C + 1 ≤ s.J) :
    (k : ℚ) * totalCap s L ≤ (L : ℚ) * totalCap s k ∧
    (k : ℚ) * volumeTotal s L ≤ (L : ℚ) * volumeTotal s k ∧
    (k : ℚ) * volumeIndex s L ≤ (L : ℚ) * volumeIndex s k ∧
    (k : ℚ) * volumeTop s L ≤ (L : ℚ) * volumeTop s k := by
  obtain ⟨ha, hd, he⟩ := cap_forms s hs L hL hJ
  obtain ⟨hA, hD, hE⟩ := cap_forms s hs k (by decide) hJ
  have hLq : (3 : ℚ) ≤ L := by exact_mod_cast hL
  have hKq : (L : ℚ) ≤ k := by exact_mod_cast hK
  have hBq : (2 : ℚ) ≤ s.B := by
    exact_mod_cast (show 2 ≤ s.B by have := hs.total_index; have := hs.index_top; have := hs.top_pos; omega)
  have hCq : (1 : ℚ) ≤ s.C := by exact_mod_cast hs.top_pos
  have hBJq : (s.J : ℚ) ≤ s.B := by exact_mod_cast hs.total_index
  have hJCq : (2 : ℚ) * s.C + 1 ≤ s.J := by exact_mod_cast hJ
  have hcastK : (exponent k : ℚ) = 2*(k : ℚ)-7 := expo_big (by decide)
  have hto : exponent L + (k-L) ≤ exponent k := by
    unfold exponent
    change max (2*L-7) (L-2) + (131072-L) ≤ max (2*131072-7) (131072-2)
    change L ≤ 131072 at hK
    omega
  have htoQ := (show (↑(exponent L) : ℚ) + ↑(k-L) ≤ ↑(exponent k) by exact_mod_cast hto)
  rw [Nat.cast_sub hK] at htoQ
  have hmonoT : (exponent L : ℚ) ≤ exponent k := by linarith
  have hDminus : (indexCap s L : ℚ) - topCap s L ≤ (indexCap s k : ℚ) - topCap s k := by
    rw [hd, he, hD, hE]
    have hh := mul_le_mul_of_nonneg_right hmonoT
      (show (0 : ℚ) ≤ (s.J : ℚ)-s.C-1 by linarith)
    nlinarith only [hh]
  have hDif : 2*(totalCap s L : ℚ)-2*indexCap s L+topCap s L ≤
      2*(totalCap s k : ℚ)-2*indexCap s k+topCap s k := by
    rw [ha, hd, he, hA, hD, hE]
    let slope : ℚ := 2*(s.B : ℚ)-2*s.J+s.C+1
    have hnon : 0 ≤ slope-1 := by dsimp [slope]; linarith
    have hh := mul_le_mul_of_nonneg_right hmonoT hnon
    dsimp [slope] at hh
    nlinarith only [hh, htoQ]
  have hLow : (indexCap s L : ℚ)-2*topCap s L ≤
      (indexCap s k : ℚ)-2*topCap s k := by
    rw [hd, he, hD, hE]
    have hh := mul_le_mul_of_nonneg_right hmonoT
      (show (0 : ℚ) ≤ (s.J : ℚ)-2*s.C-1 by linarith)
    nlinarith only [hh, htoQ]
  have hlin : (k : ℚ) * totalCap s L ≤ (L : ℚ) * totalCap s k ∧
      (k : ℚ) * topCap s L ≤ (L : ℚ) * topCap s k ∧
      (k : ℚ) * (2*totalCap s L-indexCap s L : ℚ) ≤
        (L : ℚ) * (2*totalCap s k-indexCap s k : ℚ) := by
    rw [ha, hA, hd, hD, he, hE, hcastK]
    by_cases hbig : 5 ≤ L
    · rw [expo_big hbig]
      have h1 := affine_scaled (m := 2*((s.B : ℚ)-1)) hKq (show (1-7*((s.B : ℚ)-1)) ≤ 0 by
        have hb : (2 : ℚ) ≤ s.B := by exact_mod_cast
          (show 2 ≤ s.B by have := hs.index_top; have := hs.top_pos; have := hs.total_index; omega)
        linarith)
      have h2 := affine_scaled (m := 2*((s.C : ℚ)-1)+1) hKq (show (-2-7*((s.C : ℚ)-1)) ≤ 0 by linarith)
      have h3 := affine_scaled (m := 2*(2*(s.B : ℚ)-s.J)-1) hKq (show (3-7*(2*(s.B : ℚ)-s.J)) ≤ 0 by linarith)
      exact ⟨by nlinarith only [h1],
        by nlinarith only [h2],
        by nlinarith only [h3]⟩
    · have hcase : L = 3 ∨ L = 4 := by omega
      rcases hcase with rfl | rfl
      all_goals norm_num [exponent, k]; constructor
      all_goals try constructor
      all_goals nlinarith only [hBq, hCq, hBJq]
  refine ⟨hlin.1, ?_, ?_, ?_⟩
  · unfold volumeTotal
    have hkpos : (0 : ℚ) ≤ k := by positivity
    have hlpos : (0 : ℚ) ≤ L := by positivity
    have hnon : (0 : ℚ) ≤ (indexCap s L : ℚ)-topCap s L := by
      have hh := twice_topCap_le s L
      exact sub_nonneg.mpr (by exact_mod_cast (show topCap s L ≤ indexCap s L by omega))
    have hh := mul_le_mul hlin.2.1 hDminus hnon
      (show (0 : ℚ) ≤ (L : ℚ)*topCap s k by positivity)
    nlinarith only [hh]
  · unfold volumeIndex
    have hn : (0 : ℚ) ≤ 2*(totalCap s L : ℚ)-2*indexCap s L+topCap s L := by
      have hdQ : (indexCap s L : ℚ) ≤ totalCap s L := by exact_mod_cast indexCap_le_totalCap s hs L hL
      have heQ : (0 : ℚ) ≤ topCap s L := by positivity
      linarith
    have hh := mul_le_mul hlin.2.1 hDif hn
      (show (0 : ℚ) ≤ (L : ℚ)*topCap s k by positivity)
    simpa only [mul_assoc] using hh
  · unfold volumeTop
    have hn : (0 : ℚ) ≤ (indexCap s L : ℚ)-2*topCap s L := by
      exact sub_nonneg.mpr (by exact_mod_cast twice_topCap_le s L)
    have hkP : (0 : ℚ) ≤ 2*(totalCap s k : ℚ)-indexCap s k := by
      have hdQ : (indexCap s k : ℚ) ≤ totalCap s k := by exact_mod_cast indexCap_le_totalCap s hs k (by decide)
      have haQ : (0 : ℚ) ≤ totalCap s k := by positivity
      linarith
    have hh := mul_le_mul hlin.2.2 hLow hn
      (mul_nonneg (by positivity : (0 : ℚ) ≤ L) hkP)
    nlinarith only [hh]

end StructuralList

end Merged_StructuralListArithmetic

-- merged module StructuralListPrice
section Merged_StructuralListPrice

set_option Elab.async false
set_option maxRecDepth 6000

namespace StructuralList

open CJ0 CJ0_4 MvPolynomial
open scoped BigOperators
open CJ0_4 (chart_degree surfaceBound)

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

end Merged_StructuralListPrice
