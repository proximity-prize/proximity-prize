import ProximityPrize.SubmissionLower.PortFoundation

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# Case-B `CJ0` / `StructuralList` Arithmetic at `k = 133,721` (`CJ0High133721`)

Parametrizes the `StructuralList` arithmetic (`StructuralListDefs` + `StructuralListArithmetic`)
from `CJ0.k = 131,072` (`N = 131,071`) to `kHigh = 133,721` (`NHigh = 133,720`), covering all
polynomials of degree `≤ 131,071 + 2,649 = 133,720` on the split lower-high band
`h ∈ [2302, 2649]` at `69.63` (`A = 179,798`):

1. Proves `AgreementOKHigh 179798` (`errors = 82,346 < 2 * gap = 92,156`).
2. Proves the exact `StructuralList` scaling inequalities at `kHigh = 133,721`:
   - `indexCap_le_totalCap`, `twice_topCap_le`, `incidenceLength`, `volumeScale`.
3. Kernel-checks (`decide +kernel`, zero axioms!) the exact Case-B `tariffHigh 179798` bounds
   for all 6 small 2-jet Prolongation Rescue rectangles at `69.63`:
   - `r0     (B=3,   J=3,  C=1)  ≤ 0.002e15`
   - `r1     (B=18,  J=18, C=6)  ≤ 0.64e15`
   - `r2a    (B=72,  J=72, C=24) ≤ 44.89e15`
   - `r3a_j2 (B=85,  J=51, C=17) ≤ 36.86e15`
   - `r3a_j4 (B=72,  J=24, C=8)  ≤ 7.87e15`
   - `r3a_j7 (B=105, J=21, C=7)  ≤ 9.38e15`
   so every Case-B prime across all 6 small rectangles costs at most `44.89e15` (well below
   the `61.30e15` 4-large-rect 1-jet Rescue cap at `69.63`).
-/

namespace CJ0High133721

open CJ0

abbrev nHigh : ℕ := 262144
abbrev kHigh : ℕ := 133721
abbrev NHigh : ℕ := 133720

def errorsHigh (A : ℕ) : ℕ := nHigh - A
def gapHigh (A : ℕ) : ℕ := A - NHigh

structure AgreementOKHigh (A : ℕ) : Prop where
  gt_degree : NHigh < A
  lt_length : A < nHigh
  one_le_beta : gapHigh A ≤ errorsHigh A
  beta_lt_two : errorsHigh A < 2 * gapHigh A

theorem agreementOK_6963 : AgreementOKHigh 179798 :=
  ⟨by decide, by decide, by decide, by decide⟩

structure BoxShape where
  B : ℕ
  J : ℕ
  C : ℕ

structure BoxOK (s : BoxShape) : Prop where
  top_pos : 0 < s.C
  index_top : 2 * s.C + 1 ≤ s.J
  total_index : s.J ≤ s.B
  characteristic : max NHigh (s.B * (s.B - 1)) < CJ0.p

def exponent (length : ℕ) : ℕ := max (2 * length - 7) (length - 2)

def totalCap (s : BoxShape) (length : ℕ) : ℕ :=
  1 + exponent length * (s.B - 1)

def indexCap (s : BoxShape) (length : ℕ) : ℕ :=
  exponent length * (s.J - 2) + length - 1

def topCap (s : BoxShape) (length : ℕ) : ℕ :=
  min (exponent length * (s.C - 1) + length - 2) (indexCap s length / 2)

def shortLength (common : ℕ) : ℕ := max 3 (kHigh - common)

def incidenceFactor (A common : ℕ) : ℚ := (nHigh - common : ℕ) / (A - common : ℕ)
def baseFactor (A : ℕ) : ℚ := (nHigh : ℚ) / A
def curveFactor (A : ℕ) : ℚ := (errorsHigh A : ℚ) / gapHigh A

def volumeTotal (s : BoxShape) (length : ℕ) : ℚ :=
  2 * topCap s length * ((indexCap s length : ℚ) - topCap s length)

def volumeIndex (s : BoxShape) (length : ℕ) : ℚ :=
  topCap s length * (2 * totalCap s length - 2 * indexCap s length + topCap s length)

def volumeTop (s : BoxShape) (length : ℕ) : ℚ :=
  ((indexCap s length : ℚ) - 2 * topCap s length) *
    (2 * totalCap s length - indexCap s length)

def tHigh : ℕ := exponent kHigh
def t1High : ℕ := 2 * kHigh - 5
def a0High (s : BoxShape) : ℕ := totalCap s kHigh
def DHigh (s : BoxShape) : ℕ := indexCap s kHigh
def eHigh (s : BoxShape) : ℕ := topCap s kHigh
def R2High (s : BoxShape) : ℕ :=
  (s.C * DHigh s + eHigh s * s.J - 2 * s.C * eHigh s) * (2 * a0High s - DHigh s) +
    eHigh s * (DHigh s - eHigh s) * (2 * s.B - s.J)
def HHigh (s : BoxShape) : ℕ := max s.B ((2 * s.C - 1) * s.B - s.C ^ 2)
def I1High (s : BoxShape) : ℕ := max s.J ((2 * s.C - 1) * s.J - 2 * s.C ^ 2)
def a1High (s : BoxShape) : ℕ := 1 + t1High * (HHigh s - 1)
def d1High (s : BoxShape) : ℕ := min (a1High s) (t1High * (I1High s - 1) + kHigh - 1)
def R1High (s : BoxShape) : ℕ := HHigh s * d1High s + I1High s * a1High s - I1High s * d1High s

def surfacePriceHigh (A : ℕ) (s : BoxShape) : ℚ :=
  baseFactor A * (curveFactor A * R2High s + (s.B : ℚ) * totalCap s kHigh)

def totalPriceHigh (A : ℕ) (s : BoxShape) : ℚ :=
  surfacePriceHigh A s + curveFactor A * R1High s + s.B + (HHigh s : ℚ) ^ 2

def tariffHigh (A : ℕ) (s : BoxShape) : ℕ := ⌈totalPriceHigh A s⌉₊

/-! ## Exact `StructuralList` Scaling Theorems at `kHigh = 133,721` -/

theorem indexCap_le_totalCap (s : BoxShape) (hs : BoxOK s) (L : ℕ) (hL : 3 ≤ L) :
    indexCap s L ≤ totalCap s L := by
  have hj : 2 ≤ s.J := by have := hs.index_top; have := hs.top_pos; omega
  have hb := hs.total_index
  have ht : L - 2 ≤ exponent L := le_max_right _ _
  have ht' := Nat.mul_le_mul_left (exponent L) (show s.J - 2 + 1 ≤ s.B - 1 by omega)
  rw [Nat.mul_add, Nat.mul_one] at ht'
  unfold indexCap totalCap
  omega

theorem twice_topCap_le (s : BoxShape) (L : ℕ) : 2 * topCap s L ≤ indexCap s L := by
  have he : topCap s L ≤ indexCap s L / 2 := min_le_right _ _
  omega

private theorem topCap_eq (s : BoxShape) (hs : BoxOK s) (L : ℕ) (hL : 3 ≤ L) :
    topCap s L = exponent L * (s.C - 1) + L - 2 := by
  have hc := hs.top_pos
  have hJ := hs.index_top
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

theorem incidenceLength (A common : ℕ) (hA : kHigh + 5 ≤ A) (hAn : A ≤ nHigh)
    (hc : common ≤ NHigh) :
    incidenceFactor A common * shortLength common ≤ baseFactor A * kHigh := by
  have hk : common < kHigh := Nat.lt_succ_of_le hc
  have hcn : common ≤ nHigh := by unfold kHigh nHigh at *; omega
  have hca : common < A := hk.trans_le (by omega)
  have hAq : (0 : ℚ) < A := by positivity
  have hx : (0 : ℚ) < (A - common : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hca
  unfold incidenceFactor baseFactor
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hx hAq]
  rw [Nat.cast_sub hcn, Nat.cast_sub hca.le]
  by_cases hlong : 3 ≤ kHigh - common
  · unfold shortLength
    rw [max_eq_right hlong, Nat.cast_sub hk.le]
    have hcq : (0 : ℚ) ≤ common := by positivity
    have hcK : (common : ℚ) ≤ kHigh := Nat.cast_le.mpr hk.le
    have hbound : (nHigh : ℚ) ≤ nHigh + kHigh - common := by linarith
    have hnq : (0 : ℚ) ≤ nHigh := by positivity
    have hknq : (kHigh : ℚ) ≤ A := by exact_mod_cast (show kHigh ≤ A by omega)
    have h1 := mul_le_mul_of_nonneg_left hbound (show (0 : ℚ) ≤ A by positivity)
    have h2 := mul_le_mul_of_nonneg_right hknq hnq
    have hd : (nHigh : ℚ) * kHigh ≤ (A : ℚ) * (nHigh + kHigh - common) := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left hd hcq]
  · unfold shortLength
    rw [max_eq_left (by omega : kHigh - common ≤ 3), Nat.cast_ofNat]
    have hd : 6 ≤ A - common := by unfold kHigh NHigh at *; omega
    have hdq : (6 : ℚ) ≤ (A - common : ℕ) := by exact_mod_cast hd
    rw [Nat.cast_sub hca.le] at hdq
    have hAnq : (A : ℚ) ≤ 2 * kHigh := by
      exact_mod_cast (show A ≤ 2 * kHigh by unfold nHigh kHigh at *; omega)
    have hnq : (0 : ℚ) ≤ nHigh := by positivity
    have hkq : (0 : ℚ) ≤ kHigh := by positivity
    have h1 := mul_le_mul_of_nonneg_right hAnq (show (0 : ℚ) ≤ nHigh * 3 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hdq (show (0 : ℚ) ≤ nHigh * kHigh by positivity)
    change ((nHigh : ℚ) - common) * 3 * A ≤ (nHigh : ℚ) * kHigh * ((A : ℚ) - common)
    calc
      _ ≤ (nHigh : ℚ) * 3 * A :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) (by norm_num)) (by positivity)
      _ = (A : ℚ) * (nHigh * 3) := by ring
      _ ≤ (2 * kHigh : ℚ) * (nHigh * 3) := h1
      _ = (nHigh : ℚ) * kHigh * 6 := by ring
      _ ≤ _ := h2

private theorem affine_scaled {L K m b : ℚ} (hLK : L ≤ K) (hb : b ≤ 0) :
    K * (m * L + b) ≤ L * (m * K + b) := by
  nlinarith only [mul_nonpos_of_nonpos_of_nonneg hb (sub_nonneg.mpr hLK)]

private theorem cap_forms (s : BoxShape) (hs : BoxOK s) (L : ℕ) (hL : 3 ≤ L) :
    ((totalCap s L : ℚ) = 1 + ↑(exponent L) * ((s.B : ℚ) - 1)) ∧
    ((indexCap s L : ℚ) = ↑(exponent L) * ((s.J : ℚ) - 2) + L - 1) ∧
    ((topCap s L : ℚ) = ↑(exponent L) * ((s.C : ℚ) - 1) + L - 2) := by
  have hc := hs.top_pos
  have hJ := hs.index_top
  have hj : 2 ≤ s.J := by omega
  have hb : 1 ≤ s.B := by have := hs.total_index; omega
  unfold totalCap indexCap
  rw [topCap_eq s hs L hL]
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

theorem volumeScale (s : BoxShape) (hs : BoxOK s) (L : ℕ) (hL : 3 ≤ L) (hK : L ≤ kHigh) :
    (kHigh : ℚ) * totalCap s L ≤ (L : ℚ) * totalCap s kHigh ∧
    (kHigh : ℚ) * volumeTotal s L ≤ (L : ℚ) * volumeTotal s kHigh ∧
    (kHigh : ℚ) * volumeIndex s L ≤ (L : ℚ) * volumeIndex s kHigh ∧
    (kHigh : ℚ) * volumeTop s L ≤ (L : ℚ) * volumeTop s kHigh := by
  obtain ⟨ha, hd, he⟩ := cap_forms s hs L hL
  obtain ⟨hA, hD, hE⟩ := cap_forms s hs kHigh (by decide)
  have hLq : (3 : ℚ) ≤ L := by exact_mod_cast hL
  have hKq : (L : ℚ) ≤ kHigh := by exact_mod_cast hK
  have hBq : (2 : ℚ) ≤ s.B := by
    exact_mod_cast (show 2 ≤ s.B by have := hs.total_index; have := hs.index_top; have := hs.top_pos; omega)
  have hCq : (1 : ℚ) ≤ s.C := by exact_mod_cast hs.top_pos
  have hBJq : (s.J : ℚ) ≤ s.B := by exact_mod_cast hs.total_index
  have hJCq : (2 : ℚ) * s.C + 1 ≤ s.J := by exact_mod_cast hs.index_top
  have hcastK : (exponent kHigh : ℚ) = 2 * (kHigh : ℚ) - 7 := expo_big (by decide)
  have hto : exponent L + (kHigh - L) ≤ exponent kHigh := by
    unfold exponent
    change max (2 * L - 7) (L - 2) + (133721 - L) ≤ max (2 * 133721 - 7) (133721 - 2)
    change L ≤ 133721 at hK
    omega
  have htoQ := (show (↑(exponent L) : ℚ) + ↑(kHigh - L) ≤ ↑(exponent kHigh) by exact_mod_cast hto)
  rw [Nat.cast_sub hK] at htoQ
  have hmonoT : (exponent L : ℚ) ≤ exponent kHigh := by linarith
  have hDminus : (indexCap s L : ℚ) - topCap s L ≤ (indexCap s kHigh : ℚ) - topCap s kHigh := by
    rw [hd, he, hD, hE]
    have hh := mul_le_mul_of_nonneg_right hmonoT (show (0 : ℚ) ≤ (s.J : ℚ) - s.C - 1 by linarith)
    nlinarith only [hh]
  have hDif : 2 * (totalCap s L : ℚ) - 2 * indexCap s L + topCap s L ≤
      2 * (totalCap s kHigh : ℚ) - 2 * indexCap s kHigh + topCap s kHigh := by
    rw [ha, hd, he, hA, hD, hE]
    let slope : ℚ := 2 * (s.B : ℚ) - 2 * s.J + s.C + 1
    have hnon : 0 ≤ slope - 1 := by dsimp [slope]; linarith
    have hh := mul_le_mul_of_nonneg_right hmonoT hnon
    dsimp [slope] at hh
    nlinarith only [hh, htoQ]
  have hLow : (indexCap s L : ℚ) - 2 * topCap s L ≤
      (indexCap s kHigh : ℚ) - 2 * topCap s kHigh := by
    rw [hd, he, hD, hE]
    have hh := mul_le_mul_of_nonneg_right hmonoT (show (0 : ℚ) ≤ (s.J : ℚ) - 2 * s.C - 1 by linarith)
    nlinarith only [hh, htoQ]
  have hlin : (kHigh : ℚ) * totalCap s L ≤ (L : ℚ) * totalCap s kHigh ∧
      (kHigh : ℚ) * topCap s L ≤ (L : ℚ) * topCap s kHigh ∧
      (kHigh : ℚ) * (2 * totalCap s L - indexCap s L : ℚ) ≤
        (L : ℚ) * (2 * totalCap s kHigh - indexCap s kHigh : ℚ) := by
    rw [ha, hA, hd, hD, he, hE, hcastK]
    by_cases hbig : 5 ≤ L
    · rw [expo_big hbig]
      have h1 := affine_scaled (m := 2 * ((s.B : ℚ) - 1)) hKq (show (1 - 7 * ((s.B : ℚ) - 1)) ≤ 0 by linarith)
      have h2 := affine_scaled (m := 2 * ((s.C : ℚ) - 1) + 1) hKq (show (-2 - 7 * ((s.C : ℚ) - 1)) ≤ 0 by linarith)
      have h3 := affine_scaled (m := 2 * (2 * (s.B : ℚ) - s.J) - 1) hKq
        (show (3 - 7 * (2 * (s.B : ℚ) - s.J)) ≤ 0 by linarith)
      exact ⟨by nlinarith only [h1], by nlinarith only [h2], by nlinarith only [h3]⟩
    · have hcase : L = 3 ∨ L = 4 := by omega
      rcases hcase with rfl | rfl
      all_goals norm_num [exponent, kHigh]; constructor
      all_goals try constructor
      all_goals nlinarith only [hBq, hCq, hBJq]
  refine ⟨hlin.1, ?_, ?_, ?_⟩
  · unfold volumeTotal
    have hnon : (0 : ℚ) ≤ (indexCap s L : ℚ) - topCap s L := by
      have hh := twice_topCap_le s L
      exact sub_nonneg.mpr (by exact_mod_cast (show topCap s L ≤ indexCap s L by omega))
    have hh := mul_le_mul hlin.2.1 hDminus hnon (show (0 : ℚ) ≤ (L : ℚ) * topCap s kHigh by positivity)
    nlinarith only [hh]
  · unfold volumeIndex
    have hn : (0 : ℚ) ≤ 2 * (totalCap s L : ℚ) - 2 * indexCap s L + topCap s L := by
      have hdQ : (indexCap s L : ℚ) ≤ totalCap s L := by exact_mod_cast indexCap_le_totalCap s hs L hL
      have heQ : (0 : ℚ) ≤ topCap s L := by positivity
      linarith
    have hh := mul_le_mul hlin.2.1 hDif hn (show (0 : ℚ) ≤ (L : ℚ) * topCap s kHigh by positivity)
    simpa only [mul_assoc] using hh
  · unfold volumeTop
    have hn : (0 : ℚ) ≤ (indexCap s L : ℚ) - 2 * topCap s L :=
      sub_nonneg.mpr (by exact_mod_cast twice_topCap_le s L)
    have hkP : (0 : ℚ) ≤ 2 * (totalCap s kHigh : ℚ) - indexCap s kHigh := by
      have hdQ : (indexCap s kHigh : ℚ) ≤ totalCap s kHigh := by
        exact_mod_cast indexCap_le_totalCap s hs kHigh (by decide)
      have haQ : (0 : ℚ) ≤ totalCap s kHigh := by positivity
      linarith
    have hh := mul_le_mul hlin.2.2 hLow hn (mul_nonneg (by positivity : (0 : ℚ) ≤ L) hkP)
    nlinarith only [hh]

/-! ## Kernel-Checked `69.63` Case-B Tariffs for All 6 Small Rescue Rectangles -/

def box_r0     : BoxShape := ⟨3, 3, 1⟩
def box_r1     : BoxShape := ⟨18, 18, 6⟩
def box_r2a    : BoxShape := ⟨72, 72, 24⟩
def box_r3a_j2 : BoxShape := ⟨85, 51, 17⟩
def box_r3a_j4 : BoxShape := ⟨72, 24, 8⟩
def box_r3a_j7 : BoxShape := ⟨105, 21, 7⟩

theorem all_six_boxes_ok :
    BoxOK box_r0 ∧ BoxOK box_r1 ∧ BoxOK box_r2a ∧
    BoxOK box_r3a_j2 ∧ BoxOK box_r3a_j4 ∧ BoxOK box_r3a_j7 :=
  ⟨⟨by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩⟩

theorem caseB_tariffs_6963 :
    tariffHigh 179798 box_r0     ≤ 2000000000000 ∧
    tariffHigh 179798 box_r1     ≤ 640000000000000 ∧
    tariffHigh 179798 box_r2a    ≤ 44890000000000000 ∧
    tariffHigh 179798 box_r3a_j2 ≤ 36860000000000000 ∧
    tariffHigh 179798 box_r3a_j4 ≤ 7870000000000000 ∧
    tariffHigh 179798 box_r3a_j7 ≤ 9380000000000000 := by
  decide +kernel

#print axioms agreementOK_6963
#print axioms indexCap_le_totalCap
#print axioms twice_topCap_le
#print axioms incidenceLength
#print axioms volumeScale
#print axioms all_six_boxes_ok
#print axioms caseB_tariffs_6963

end CJ0High133721
