import ProximityPrize.SubmissionLower.PortFoundation
import ProximityPrize.SubmissionLower.R6960Front6960List
import ProximityPrize.SubmissionLower.RungSplit
import ProximityPrize.SubmissionLower.TwoJetCaseAFXCore
import ProximityPrize.SubmissionLower.TwoJetCaseAKernel
import ProximityPrize.SubmissionLower.TwoJetCaseAFXRank

set_option Elab.async false

-- merged module CJ0High133721
section Merged_CJ0High133721

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

end Merged_CJ0High133721

-- merged module CJ0High133721Main
section Merged_CJ0High133721Main

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# Case-B `StructuralList` / Order-Two Counting Theorem at `kHigh = 133,721` (`CJ0High133721Main`)

Lifts the full sharpened `StructuralList` counting pipeline (`ShortenChart` + `ScalarCutCapacity` +
`CJ0_4` + `CJ0_5` + `CJ0_6` + `CJ0_7` + `CJ0_8`) from `CJ0.k = 131,072` (`N = 131,071`) to
`kHigh = 133,721` (`NHigh = 133,720`), covering all polynomials of degree `≤ 131,071 + 2,649`
on the split lower-high band `h ∈ [2302, 2649]` at `69.63` (`A = 179,798`).

Main results:
1. `shortenChart_high`: shortened order-2 charts at `kHigh = 133,721`.
2. `cutCap_high`: evaluation-section capacity bound for order-2 surface charts at `kHigh = 133,721`.
3. `order_two_card_le_high133721`: any finite set `T ⊆ closeHigh A w` of degree-`< 133,721`
   polynomials annihilated by a nonzero order-2 differential polynomial `Q` of box shape `s`
   satisfies `T.card ≤ tariffHigh A s`.
4. `caseB_six_rects_card_le_6963`: concrete cardinality caps (`≤ 44.89e15`) for all 6 small
   Case-B Rescue rectangles at `69.63` (`A = 179,798`).
-/

namespace CJ0High133721

noncomputable section

open CJ0 Polynomial PolynomialDifferential MvPolynomial Finset Filter
open scoped BigOperators
open K1_14_6 (occupancy curve_degree_nat)
open P0_10 (incidence_arithmetic)
open K1_13_5_4_2 (ratio_image_degree)

/-! ## Section 1: Degree-`< 133,721` Geometry, Charts, and Capacity Bounds -/

abbrev closeHigh (A : ℕ) (w : Node → K) :=
  ReedSolomon.closePolynomialSet node w kHigh A

def boxToSource (b : BoxShape) : CJ0.Source :=
  ⟨1, b.B, b.J, b.C, CJ0.fullBox b.B b.J b.C⟩

abbrev OrderTwoHigh (b : BoxShape) (Q : DifferentialPolynomial K 2) : Prop :=
  CJ0.OrderTwo (boxToSource b) Q

abbrev OrderOneHigh (b : BoxShape) (Q : DifferentialPolynomial K 1) : Prop :=
  CJ0.OrderOne (boxToSource b) Q

theorem boxToSource_shapeOK (b : BoxShape) (hb : BoxOK b) : CJ0.ShapeOK (boxToSource b) where
  multiplicity := Nat.zero_lt_one
  top_pos := hb.top_pos
  index_top := by dsimp [boxToSource]; have := hb.index_top; omega
  total_index := hb.total_index
  characteristic := by
    have hc := hb.characteristic
    have hle : max CJ0.N (b.B * (b.B - 1)) ≤ max NHigh (b.B * (b.B - 1)) :=
      max_le_max_right _ (by decide)
    exact hle.trans_lt hc
  support := by
    intro j hj
    dsimp [boxToSource] at hj ⊢
    exact (CJ0.mem_fullBox hb.total_index (by have := hb.index_top; omega) j).mp hj
  lower := by
    intro j hj ha
    dsimp [boxToSource] at hj ⊢
    have hmem := (CJ0.mem_fullBox hb.total_index (by have := hb.index_top; omega) j).mp hj
    rw [CJ0.mem_fullBox hb.total_index (by have := hb.index_top; omega)]
    rcases j with ⟨c, b', a⟩
    simp only [Jet.q, Jet.v, Jet.c, Jet.b, Jet.a] at hmem ha ⊢
    omega

abbrev CoeffRingHigh := MvPolynomial (Fin kHigh) Geo

def coeffPointHigh (f : Polynomial K) (i : Fin kHigh) : Geo :=
  embed (f.coeff i.val)

def readJetHigh (y : Fin kHigh → Geo) (j : ℕ) : Geo :=
  ∑ i : Fin kHigh, (i.val.choose j : Geo) * center ^ (i.val - j) * y i

structure ChartHigh (r : ℕ) where
  equation : InitialRing r
  denominator : InitialRing r
  numerator : Fin kHigh → InitialRing r

def ChartHigh.locus {r : ℕ} (T : ChartHigh r) : Set (Fin (r + 1) → Geo) :=
  {u | MvPolynomial.eval u T.equation = 0 ∧ MvPolynomial.eval u T.denominator ≠ 0}

def ChartHigh.output {r : ℕ} (T : ChartHigh r) (u : Fin (r + 1) → Geo) (i : Fin kHigh) : Geo :=
  MvPolynomial.eval u (T.numerator i) / MvPolynomial.eval u T.denominator

def ChartHigh.imageSet {r : ℕ} (T : ChartHigh r) : Set (Fin kHigh → Geo) :=
  T.output '' T.locus

def ChartHigh.ideal {r : ℕ} (T : ChartHigh r) : Ideal CoeffRingHigh :=
  MvPolynomial.vanishingIdeal Geo T.imageSet

structure ChartOKHigh {r : ℕ} (T : ChartHigh r) : Prop where
  irreducible : Irreducible T.equation
  nonvanishing : ¬ T.equation ∣ T.denominator
  recover : ∀ u ∈ T.locus, ∀ j : Fin (r + 1), readJetHigh (T.output u) j.val = u j

structure FamilyHigh (r : ℕ) where
  count : ℕ
  chart : Fin count → ChartHigh r

def InBandHigh (s : BoxShape) (length : ℕ) (P : InitialRing 2) : Prop :=
  P.totalDegree ≤ totalCap s length ∧
  P.weightedTotalDegree Fin.val ≤ indexCap s length ∧
  P.degreeOf (Fin.last 2) ≤ topCap s length

structure ShortBandHigh (s : BoxShape) (length : ℕ) (T : ChartHigh 2) : Prop where
  denominator : InBandHigh s length T.denominator
  numerator : ∀ i : Fin kHigh, InBandHigh s length (T.numerator i)

def inBand1High (s : BoxShape) (P : InitialRing 1) : Prop :=
  P.totalDegree ≤ a1High s ∧ P.degreeOf (Fin.last 1) ≤ d1High s

structure Family1High (s : BoxShape) (F : FamilyHigh 1) : Prop where
  count : F.count ≤ HHigh s
  chart_ok : ∀ i, ChartOKHigh (F.chart i)
  total : (∑ i, (F.chart i).equation.totalDegree) ≤ HHigh s
  index : (∑ i, (F.chart i).equation.degreeOf (Fin.last 1)) ≤ I1High s
  bands : ∀ i, inBand1High s (F.chart i).denominator ∧ ∀ j, inBand1High s ((F.chart i).numerator j)

structure ImageDegreesHigh {r : ℕ} (F : FamilyHigh r) (budget : ℕ) : Prop where
  prime : ∀ i, (F.chart i).ideal.IsPrime
  dimension : ∀ i, (MvPolynomial.affineHilbertPolynomial (F.chart i).ideal).natDegree = r
  total : (∑ i, MvPolynomial.affineDegree (F.chart i).ideal) ≤ (budget : ℚ)

private theorem section_capacity_high {A : ℕ} {w : Node → K} {T : Finset (Polynomial K)}
    (h : (T : Set (Polynomial K)) ⊆ closeHigh A w) (hA : AgreementOKHigh A) (cap : ℕ)
    (hsection : ∀ i : Node, (∃ γ ∈ T, γ.eval (node i) ≠ w i) →
      (T.filter fun γ => γ.eval (node i) = w i).card ≤ cap) :
    gapHigh A * T.card ≤ errorsHigh A * cap + gapHigh A := by
  classical
  have hd := hA.gt_degree
  have hn := hA.lt_length
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (gapHigh A) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : Polynomial K) : Finset Node := univ.filter fun i => γ.eval (node i) = w i
  let common : Finset Node := univ.filter fun i => ∀ γ ∈ T, γ.eval (node i) = w i
  let nodes : Finset Node := univ \ common
  have common_le (γ : Polynomial K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : Polynomial K) (hγ : γ ∈ T) : A ≤ (hits γ).card := (h hγ).2
  have degree (a : Polynomial K) (ha : a ∈ T) : a.natDegree ≤ NHigh := by
    by_cases hz : a = 0
    · simp [hz]
    · have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hz).2 (h ha).1
      exact Nat.le_of_lt_succ hdeg
  have pair_count (a : Polynomial K) (ha : a ∈ T) (b : Polynomial K) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ NHigh := by
    refine (FrobeniusLocator.Strata.root_nodes_card_le node node.injective
      (a - b) (sub_ne_zero.mpr hab) _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (degree a ha) (degree b hb)))
    intro i hi
    change (a - b).eval (node i) = 0
    rw [Polynomial.eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ NHigh :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := A - common.card
  let t := NHigh - common.card
  have ht : t = x - gapHigh A := by dsimp [t, x, gapHigh]; omega
  have hx : gapHigh A ≤ x := by dsimp [x, gapHigh]; omega
  have hnodes : nodes.card = x + errorsHigh A := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ,
      ProximityPrize.Benchmark.IRSProfile.card_index]
    change nHigh - common.card = (A - common.card) + (nHigh - A)
    have hbound := hcommon.trans hd.le
    omega
  have exists_trim (γ : Polynomial K) :
      ∃ B : Finset Node, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ : γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hsize
      exact ⟨B, fun _ => ⟨hB, hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : Polynomial K) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : Polynomial K) (ha : a ∈ T) (b : Polynomial K) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card ≤ t := by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi, common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : Node) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, γ.eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    have hi' : i ∈ hits γ := (mem_sdiff.mp ((hB γ hγ).1 hi)).1
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp hi').2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic (errorsHigh A) _ _ _ _ (by omega)
    (Nat.sub_pos_of_lt hd) hx (Nat.sub_pos_of_lt hn) second first

def valueCutHigh (x a : K) : CoeffRingHigh :=
  (∑ i : Fin kHigh, MvPolynomial.C (embed x ^ i.val) * MvPolynomial.X i) - MvPolynomial.C (embed a)

theorem valueCutHigh_degree (x a : K) : (valueCutHigh x a).totalDegree ≤ 1 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply totalDegree_finsetSum_le
  intro i _
  simpa only [totalDegree_C, totalDegree_X, zero_add] using
    (totalDegree_mul (MvPolynomial.C (embed x ^ i.val)) (MvPolynomial.X i))

private theorem natDegree_bound_high {f : Polynomial K} (h : f.degree < kHigh) :
    f.natDegree < kHigh := by
  by_cases hz : f = 0
  · rw [hz, Polynomial.natDegree_zero]
    exact Nat.zero_lt_succ _
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 h

theorem valueCutHigh_eval {f : Polynomial K} (h : f.degree < kHigh) (x a : K) :
    MvPolynomial.aeval (coeffPointHigh f) (valueCutHigh x a) = 0 ↔ f.eval x = a := by
  have heval : f.eval x = ∑ j : Fin kHigh, f.coeff j.val * x ^ j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => f.coeff j * x ^ j)]
    exact Polynomial.eval_eq_sum_range' (natDegree_bound_high h) x
  have hmap : embed (∑ j : Fin kHigh, f.coeff j.val * x ^ j.val) =
      ∑ j : Fin kHigh, embed x ^ j.val * embed (f.coeff j.val) := by
    rw [map_sum]
    exact sum_congr rfl fun _ _ => by rw [map_mul, map_pow, mul_comm]
  simp only [valueCutHigh, coeffPointHigh, map_sub, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, sub_eq_zero, Algebra.algebraMap_self_apply]
  rw [heval, ← hmap]
  exact embed.injective.eq_iff

private theorem coeffPointHigh_injOn {A w} {Γ : Finset (Polynomial K)}
    (h : (Γ : Set (Polynomial K)) ⊆ closeHigh A w) :
    Set.InjOn coeffPointHigh (Γ : Set (Polynomial K)) := by
  intro f hf g hg heq
  apply Polynomial.ext
  intro j
  by_cases hj : j < kHigh
  · exact embed.injective (congrFun heq ⟨j, hj⟩)
  · have hfj := (natDegree_bound_high (h hf).1).trans_le (Nat.le_of_not_gt hj)
    have hgj := (natDegree_bound_high (h hg).1).trans_le (Nat.le_of_not_gt hj)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hfj, Polynomial.coeff_eq_zero_of_natDegree_lt hgj]

private theorem zeroDim_count_high {A w} {Γ : Finset (Polynomial K)}
    (h : (Γ : Set (Polynomial K)) ⊆ closeHigh A w) (P : Ideal CoeffRingHigh)
    (hdim : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ Γ, coeffPointHigh γ ∈ zeroLocus Geo P) :
    (Γ.card : ℚ) ≤ affineDegree P := by
  classical
  let Im := Γ.image coeffPointHigh
  have hIm : Im.card = Γ.card := card_image_of_injOn (coeffPointHigh_injOn h)
  have hsub : (Im : Set _) ⊆ zeroLocus Geo P := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := Geo) P hdim
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hIm] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree

private theorem section_count_high {A w} {Γ : Finset (Polynomial K)}
    (h : (Γ : Set (Polynomial K)) ⊆ closeHigh A w) {P : Ideal CoeffRingHigh}
    (hP : P.IsPrime) (hpoints : ∀ γ ∈ Γ, coeffPointHigh γ ∈ zeroLocus Geo P)
    (x a : K) (hmiss : ∃ γ ∈ Γ, γ.eval x ≠ a)
    {c : ℚ} (hc : 0 ≤ c)
    (bound : ∀ (V : Finset (Polynomial K)), V ⊆ Γ → ∀ (Q : Ideal CoeffRingHigh), Q.IsPrime →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, coeffPointHigh γ ∈ zeroLocus Geo Q) →
      (V.card : ℚ) ≤ c * affineDegree Q) :
    ((Γ.filter fun γ => γ.eval x = a).card : ℚ) ≤ c * affineDegree P := by
  classical
  let _ := hP
  let cut := valueCutHigh x a
  let Ps := (P ⊔ Ideal.span {cut}).minimalPrimesFinset
  let U := Γ.filter fun γ => γ.eval x = a
  let part (Q : Ideal CoeffRingHigh) := U.filter fun f => coeffPointHigh f ∈ zeroLocus Geo Q
  have hproper : cut ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hm
    exact hv ((valueCutHigh_eval (h hγ).1 x a).mp (hpoints γ hγ _ hm))
  have hcover : U ⊆ Ps.biUnion part := by
    intro γ hγ
    obtain ⟨hγΓ, hv⟩ := mem_filter.mp hγ
    have hp : coeffPointHigh γ ∈ zeroLocus Geo (P ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγΓ, (valueCutHigh_eval (h hγΓ).1 x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact mem_biUnion.mpr ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  have hsum : U.card ≤ ∑ Q ∈ Ps, (part Q).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hdeg : (∑ Q ∈ Ps, affineDegree Q) ≤ affineDegree P := by
    simpa only [Ps, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCutHigh_degree x a)
  change (U.card : ℚ) ≤ c * affineDegree P
  calc
    _ ≤ ∑ Q ∈ Ps, ((part Q).card : ℚ) := by exact_mod_cast hsum
    _ ≤ ∑ Q ∈ Ps, c * affineDegree Q := by
      apply sum_le_sum
      intro Q hQ
      have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
      exact bound _ ((filter_subset _ _).trans (filter_subset _ _)) Q hmin.isPrime
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => (mem_filter.mp hγ).2)
    _ ≤ c * affineDegree P := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hdeg hc

theorem curve_capacity_high {A w} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w)
    (hA : AgreementOKHigh A) {P : Ideal CoeffRingHigh} (hp : P.IsPrime)
    (hd : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ f ∈ T, coeffPointHigh f ∈ zeroLocus Geo P) :
    ((gapHigh A : ℕ) : ℚ) * T.card ≤ (errorsHigh A : ℚ) * affineDegree P + gapHigh A ∧
    (T.card : ℚ) ≤ 2 * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hp hd
  have hcap := section_capacity_high hT hA δ fun i hi => by
    have hc := section_count_high hT hp hpoints (node i) (w i) hi (c := 1) zero_le_one
      (fun _ hV Q _ hdim hpts => by
        rw [one_mul]
        exact zeroDim_count_high (fun _ hf => hT (hV hf)) Q (by omega) hpts)
    rw [one_mul, hdeg] at hc
    exact_mod_cast hc
  rw [hdeg]
  refine ⟨by exact_mod_cast hcap, ?_⟩
  suffices hn : T.card ≤ 2 * δ by exact_mod_cast hn
  by_contra! hbad
  have hstep := Nat.mul_le_mul_left (gapHigh A) (show 2 * δ + 1 ≤ T.card by omega)
  rw [Nat.mul_add, Nat.mul_one] at hstep
  have hstrict := Nat.mul_lt_mul_of_pos_right hA.beta_lt_two hδ
  rw [mul_comm 2 (gapHigh A), mul_assoc] at hstrict
  omega

theorem family1_capacity_high {A w budget} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w)
    (hA : AgreementOKHigh A) (F : FamilyHigh 1) (hg : ImageDegreesHigh F budget)
    (hcover : ∀ f ∈ T, ∃ i, coeffPointHigh f ∈ (F.chart i).imageSet) :
    (gapHigh A : ℚ) * T.card ≤ (errorsHigh A : ℚ) * (budget : ℚ) + (gapHigh A : ℚ) * F.count := by
  classical
  let part (i : Fin F.count) := T.filter fun f => coeffPointHigh f ∈ (F.chart i).imageSet
  have hc : T.card ≤ ∑ i, (part i).card := by
    apply (card_le_card (t := univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i, hi⟩ := hcover f hf
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hf, hi⟩⟩
  have hone (i : Fin F.count) : (gapHigh A : ℚ) * (part i).card ≤
      (errorsHigh A : ℚ) * affineDegree (F.chart i).ideal + gapHigh A := by
    have hsub : (part i : Set (Polynomial K)) ⊆ closeHigh A w := fun _ hf => hT (mem_filter.mp hf).1
    have hp : ∀ f ∈ part i, coeffPointHigh f ∈ zeroLocus Geo (F.chart i).ideal :=
      fun _ hf => zeroLocus_vanishingIdeal_le _ (mem_filter.mp hf).2
    exact (curve_capacity_high hsub hA (hg.prime i) (hg.dimension i) hp).1
  have hq : (T.card : ℚ) ≤ ∑ i, ((part i).card : ℚ) := by exact_mod_cast hc
  calc
    _ ≤ (gapHigh A : ℚ) * ∑ i, ((part i).card : ℚ) :=
      mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    _ = ∑ i, (gapHigh A : ℚ) * (part i).card := mul_sum ..
    _ ≤ _ := sum_le_sum fun i _ => hone i
    _ = (errorsHigh A : ℚ) * (∑ i, affineDegree (F.chart i).ideal) + (gapHigh A : ℚ) * F.count := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin,
        mul_comm (F.count : ℚ)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hg.total (Nat.cast_nonneg _)) le_rfl

/-! ## Section 2: Chart Image Geometry and Degree Bounds (`CJ0_4` at `kHigh`) -/

def sourceIdealHigh {r : ℕ} (T : ChartHigh r) : Ideal (InitialRing r) :=
  Ideal.span {T.equation}

def quotientBandHigh (T : ChartHigh 2) (a d e : ℕ) :
    Submodule Geo (InitialRing 2 ⧸ sourceIdealHigh T) :=
  (CJ0_4.bandSpace a d e).map (Ideal.Quotient.mkₐ Geo (sourceIdealHigh T)).toLinearMap

private theorem quotientBandHigh_mono (T : ChartHigh 2) {a d e a' d' e' : ℕ}
    (ha : a ≤ a') (hd : d ≤ d') (he : e ≤ e') :
    quotientBandHigh T a d e ≤ quotientBandHigh T a' d' e' :=
  Submodule.map_mono (CJ0_4.bandSpace_mono ha hd he)

local instance (T : ChartHigh 2) (a d e : ℕ) : Module.Finite Geo (quotientBandHigh T a d e) := by
  unfold quotientBandHigh
  infer_instance

abbrev ChartOpenHigh {r : ℕ} (T : ChartHigh r) :=
  Localization.Away (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)

def localizeHigh {r : ℕ} (T : ChartHigh r) : InitialRing r →ₐ[Geo] ChartOpenHigh T :=
  (IsScalarTower.toAlgHom Geo (InitialRing r ⧸ sourceIdealHigh T) (ChartOpenHigh T)).comp
    (Ideal.Quotient.mkₐ Geo (sourceIdealHigh T))

def invDenomHigh {r : ℕ} (T : ChartHigh r) : ChartOpenHigh T :=
  IsLocalization.Away.invSelf (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)

theorem denom_mul_inv_high {r : ℕ} (T : ChartHigh r) :
    localizeHigh T T.denominator * invDenomHigh T = 1 :=
  IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)

def chartMapHigh {r : ℕ} (T : ChartHigh r) : CoeffRingHigh →ₐ[Geo] ChartOpenHigh T :=
  MvPolynomial.aeval fun i => localizeHigh T (T.numerator i) * invDenomHigh T

private theorem in_zeroLocus_high {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo}
    (hy : y ∈ T.locus) : y ∈ zeroLocus Geo (sourceIdealHigh T) := by
  apply mem_zeroLocus_iff_le_ker_aeval.mpr
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact RingHom.mem_ker.mpr hy.1

private def pointEvalHigh {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo} (hy : y ∈ T.locus) :
    (InitialRing r ⧸ sourceIdealHigh T) →ₐ[Geo] Geo :=
  Ideal.Quotient.liftₐ (sourceIdealHigh T) (MvPolynomial.aeval y) fun q hq =>
    in_zeroLocus_high hy q hq

def openEvalHigh {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo} (hy : y ∈ T.locus) :
    ChartOpenHigh T →ₐ[Geo] Geo :=
  IsLocalization.Away.liftAlgHom (f := pointEvalHigh hy)
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)

theorem openEvalHigh_localize {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo} (hy : y ∈ T.locus)
    (q : InitialRing r) : openEvalHigh hy (localizeHigh T q) = MvPolynomial.eval y q :=
  IsLocalization.Away.lift_eq (g := (pointEvalHigh hy).toRingHom)
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
    (Ideal.Quotient.mk (sourceIdealHigh T) q)

theorem openEvalHigh_chartMap {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo} (hy : y ∈ T.locus)
    (q : CoeffRingHigh) : openEvalHigh hy (chartMapHigh T q) = MvPolynomial.eval (T.output y) q := by
  have hu := congrArg (openEvalHigh hy) (denom_mul_inv_high T)
  rw [map_mul, openEvalHigh_localize, map_one] at hu
  have hi : openEvalHigh hy (invDenomHigh T) = (MvPolynomial.eval y T.denominator)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hy.2).mpr ((mul_comm _ _).trans hu)
  have h : (openEvalHigh hy).comp (chartMapHigh T) = MvPolynomial.aeval (T.output y) := by
    apply MvPolynomial.algHom_ext
    intro i
    change openEvalHigh hy (chartMapHigh T (MvPolynomial.X i)) =
      MvPolynomial.aeval (T.output y) (MvPolynomial.X i)
    rw [chartMapHigh, MvPolynomial.aeval_X, map_mul, openEvalHigh_localize, hi, MvPolynomial.aeval_X,
      ChartHigh.output, div_eq_mul_inv]
  exact DFunLike.congr_fun h q

private theorem eq_zero_of_openEvalHigh {r : ℕ} {T : ChartHigh r} [(sourceIdealHigh T).IsPrime]
    (hD : T.denominator ∉ sourceIdealHigh T) {z : ChartOpenHigh T}
    (hz : ∀ y (hy : y ∈ T.locus), openEvalHigh hy z = 0) : z = 0 := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator) z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  change z * localizeHigh T T.denominator ^ m = localizeHigh T q at ha
  have hq : q ∈ sourceIdealHigh T := by
    have hmul : T.denominator * q ∈ sourceIdealHigh T := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := Geo) (sourceIdealHigh T)]
      intro y hy
      change MvPolynomial.eval y (T.denominator * q) = 0
      by_cases hyD : MvPolynomial.eval y T.denominator = 0
      · rw [map_mul, hyD, zero_mul]
      · have hy' : y ∈ T.locus := ⟨hy _ (Ideal.subset_span (by simp)), hyD⟩
        have he := congrArg (openEvalHigh hy') ha
        rw [map_mul, map_pow, openEvalHigh_localize, openEvalHigh_localize, hz y hy', zero_mul] at he
        rw [map_mul, ← he, mul_zero]
    exact (‹(sourceIdealHigh T).IsPrime›.mem_or_mem hmul).resolve_left hD
  have hq0 : localizeHigh T q = 0 := by
    change algebraMap (InitialRing r ⧸ sourceIdealHigh T) (ChartOpenHigh T)
      (Ideal.Quotient.mk (sourceIdealHigh T) q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  rw [hq0] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := ChartOpenHigh T)
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)).pow m).mul_right_cancel
      (ha.trans (zero_mul _).symm)

theorem imageIdeal_eq_ker_high {r : ℕ} (T : ChartHigh r) [(sourceIdealHigh T).IsPrime]
    (hD : T.denominator ∉ sourceIdealHigh T) :
    T.ideal = RingHom.ker (chartMapHigh T).toRingHom := by
  ext q
  change q ∈ vanishingIdeal Geo T.imageSet ↔ chartMapHigh T q = 0
  constructor
  · intro hq
    apply eq_zero_of_openEvalHigh hD
    intro y hy
    rw [openEvalHigh_chartMap hy]
    exact hq _ ⟨y, hy, rfl⟩
  · intro hq
    rintro _ ⟨y, hy, rfl⟩
    change MvPolynomial.eval (T.output y) q = 0
    rw [← openEvalHigh_chartMap hy, hq, map_zero]

private def jetFormHigh (j : ℕ) : CoeffRingHigh :=
  ∑ i : Fin kHigh, MvPolynomial.C ((i.val.choose j : Geo) * center ^ (i.val - j)) * MvPolynomial.X i

private theorem eval_jetFormHigh (y : Fin kHigh → Geo) (j : ℕ) :
    MvPolynomial.eval y (jetFormHigh j) = readJetHigh y j := by
  simp [jetFormHigh, readJetHigh]

private theorem chartMapHigh_recover {r : ℕ} (T : ChartHigh r) (hT : ChartOKHigh T)
    [(sourceIdealHigh T).IsPrime] (hD : T.denominator ∉ sourceIdealHigh T) :
    (chartMapHigh T).comp (MvPolynomial.aeval fun j : Fin (r + 1) => jetFormHigh j.val) =
      localizeHigh T := by
  apply MvPolynomial.algHom_ext
  intro j
  change chartMapHigh T (MvPolynomial.aeval (fun j : Fin (r + 1) => jetFormHigh j.val)
      (MvPolynomial.X j)) = localizeHigh T (MvPolynomial.X j)
  rw [MvPolynomial.aeval_X, ← sub_eq_zero]
  apply eq_zero_of_openEvalHigh hD
  intro y hy
  rw [map_sub, openEvalHigh_chartMap, openEvalHigh_localize, eval_jetFormHigh, MvPolynomial.eval_X,
    hT.recover y hy j, sub_self]

theorem image_geometry_high {r : ℕ} (T : ChartHigh r) (hT : ChartOKHigh T) :
    T.ideal.IsPrime ∧ (affineHilbertPolynomial T.ideal).natDegree = r := by
  have hprime : (sourceIdealHigh T).IsPrime :=
    Ideal.span_singleton_prime hT.irreducible.ne_zero |>.mpr hT.irreducible.prime
  let _ := hprime
  have hD : T.denominator ∉ sourceIdealHigh T :=
    fun h => hT.nonvanishing (Ideal.mem_span_singleton.mp h)
  have hne : Ideal.Quotient.mk (sourceIdealHigh T) T.denominator ≠ 0 :=
    mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  let _ : IsDomain (ChartOpenHigh T) := Localization.Away.isDomain hne
  have hreg := (IsRegular.of_ne_zero hne).1
  have hsource : (affineHilbertPolynomial (sourceIdealHigh T)).natDegree = r := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      hT.irreducible.ne_zero hprime.ne_top
    rw [Nat.card_fin] at h
    exact Nat.add_right_cancel h
  rw [imageIdeal_eq_ker_high T hD]
  refine ⟨RingHom.ker_isPrime _, Eq.trans (le_antisymm ?_ ?_) hsource⟩
  · let E := awayPresentationEquiv (sourceIdealHigh T) T.denominator
    exact (natDegree_affineHilbertPolynomial_le_of_injective
      (E.symm.toAlgHom.comp (Ideal.kerLiftAlg (chartMapHigh T)))
      (E.symm.injective.comp (Ideal.kerLiftAlg_injective (chartMapHigh T)))).trans
      (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le (sourceIdealHigh T) T.denominator)
  · exact natDegree_affineHilbertPolynomial_le_of_away_range (sourceIdealHigh T) T.denominator hreg
      (chartMapHigh T)
      (fun q => ⟨_, DFunLike.congr_fun (chartMapHigh_recover T hT hD) q⟩) le_rfl

private theorem c1_high (T : ChartHigh 2) (a d e : ℕ) (hT : ChartOKHigh T)
    (hD : T.denominator ∈ CJ0_4.bandSpace a d e)
    (hN : ∀ i : Fin kHigh, T.numerator i ∈ CJ0_4.bandSpace a d e) (m : ℕ) :
    affineHilbertFunction T.ideal m ≤
      Module.finrank Geo (quotientBandHigh T (m * a) (m * d) (m * e)) := by
  let _ : (sourceIdealHigh T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  have hD' : T.denominator ∉ sourceIdealHigh T :=
    fun h => hT.nonvanishing (Ideal.mem_span_singleton.mp h)
  rw [imageIdeal_eq_ker_high T hD']
  let j := IsScalarTower.toAlgHom Geo (InitialRing 2 ⧸ sourceIdealHigh T) (ChartOpenHigh T)
  let δ := localizeHigh T T.denominator
  have hδ : IsUnit δ :=
    IsLocalization.Away.algebraMap_isUnit (S := ChartOpenHigh T)
      (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)
  let y (i : Fin kHigh) := localizeHigh T (T.numerator i) * invDenomHigh T
  have hy (i : Fin kHigh) : δ * y i = localizeHigh T (T.numerator i) := by
    change localizeHigh T T.denominator * (localizeHigh T (T.numerator i) * invDenomHigh T) = _
    rw [mul_left_comm _ (localizeHigh T (T.numerator i)), denom_mul_inv_high, mul_one]
  let V (n : ℕ) : Submodule Geo (ChartOpenHigh T) :=
    (quotientBandHigh T (n * a) (n * d) (n * e)).map j.toLinearMap
  let W (n : ℕ) : Submodule Geo (ChartOpenHigh T) :=
    (V n).comap (LinearMap.mulLeft Geo (δ ^ n))
  have hW (n : ℕ) (z : ChartOpenHigh T) :
      z ∈ W n ↔ ∃ P ∈ CJ0_4.bandSpace (n * a) (n * d) (n * e), localizeHigh T P = δ ^ n * z := by
    change δ ^ n * z ∈ V n ↔ _
    simp only [V, quotientBandHigh, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap,
      Submodule.mem_map, AlgHom.toLinearMap_apply, localizeHigh, j]
  have hOne : (1 : InitialRing 2) ∈ CJ0_4.bandSpace 0 0 0 := by
    have hw : weightedTotalDegree Fin.val (1 : InitialRing 2) = 0 := by
      rw [← MvPolynomial.C_1, weightedTotalDegree_C]
    exact CJ0_4.mem_bandSpace.mpr ⟨totalDegree_one.le, hw.le, (degreeOf_one _).le⟩
  have hpow (n : ℕ) : T.denominator ^ n ∈ CJ0_4.bandSpace (n * a) (n * d) (n * e) := by
    induction n with
    | zero => simpa only [pow_zero, Nat.zero_mul] using hOne
    | succ n ih => simpa only [pow_succ, Nat.succ_mul] using CJ0_4.mul_mem_bandSpace ih hD
  have hmono : Monotone W := by
    intro n l hnl z hz
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨T.denominator ^ (l - n) * P, ?_, ?_⟩
    · simpa only [← Nat.add_mul, Nat.sub_add_cancel hnl] using
        CJ0_4.mul_mem_bandSpace (hpow (l - n)) hP
    · rw [map_mul, map_pow, heq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hnl]
  have hmul (i : Fin kHigh) (n : ℕ) (z : ChartOpenHigh T) (hz : z ∈ W n) :
      y i * z ∈ W (n + 1) := by
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨P * T.numerator i, ?_, ?_⟩
    · simpa only [Nat.add_mul, Nat.one_mul] using CJ0_4.mul_mem_bandSpace hP (hN i)
    · rw [map_mul, heq, ← hy i, pow_succ]
      ac_rfl
  have h0 : (1 : ChartOpenHigh T) ∈ W 0 :=
    (hW _ _).mpr ⟨1, by simpa only [Nat.zero_mul] using hOne, by simp⟩
  have hclear (P : CoeffRingHigh) (hP : P.totalDegree ≤ m) : chartMapHigh T P ∈ W m := by
    change MvPolynomial.aeval y P ∈ W m
    simpa only [Nat.one_mul] using
      (aeval_mem_of_forall_mul_mem y hmono h0 hmul hP)
  let Q := RingHom.ker (chartMapHigh T).toRingHom
  let ι : (CoeffRingHigh ⧸ Q) →ₐ[Geo] ChartOpenHigh T := Ideal.kerLiftAlg (chartMapHigh T)
  have hmem (x : quotientDegreeLE Q m) : δ ^ m * ι x.val ∈ V m := by
    obtain ⟨P, hP, heq⟩ := mem_quotientDegreeLE.mp x.property
    change ι x.val ∈ W m
    rw [← heq]
    change chartMapHigh T P ∈ W m
    exact hclear P hP
  let L : quotientDegreeLE Q m →ₗ[Geo] V m :=
    (((LinearMap.mulLeft Geo (δ ^ m)).comp ι.toLinearMap).domRestrict
      (quotientDegreeLE Q m)).codRestrict (V m) hmem
  have hL : Function.Injective L := by
    intro x z hxz
    have h : δ ^ m * ι x.val = δ ^ m * ι z.val := congrArg Subtype.val hxz
    exact Subtype.ext (Ideal.kerLiftAlg_injective (chartMapHigh T) ((hδ.pow m).mul_left_cancel h))
  exact (LinearMap.finrank_le_finrank_of_injective hL).trans (Submodule.finrank_map_le _ _)

private theorem quotientBandHigh_add_finrank_le (T : ChartHigh 2) (a d e b j c : ℕ)
    (hn : T.equation ≠ 0) (hf : T.equation ∈ CJ0_4.bandSpace b j c) :
    Module.finrank Geo (quotientBandHigh T (a + b) (d + j) (e + c)) +
      Module.finrank Geo (CJ0_4.bandSpace a d e) ≤
      Module.finrank Geo (CJ0_4.bandSpace (a + b) (d + j) (e + c)) := by
  let W := CJ0_4.bandSpace (a + b) (d + j) (e + c)
  let F := (Ideal.Quotient.mkₐ Geo (sourceIdealHigh T)).toLinearMap.domRestrict W
  have hF : LinearMap.range F = quotientBandHigh T (a + b) (d + j) (e + c) :=
    LinearMap.range_domRestrict W _
  let mul := (LinearMap.mulLeft Geo T.equation).domRestrict (CJ0_4.bandSpace a d e)
  have hmul (p : CJ0_4.bandSpace a d e) : mul p ∈ W := by
    simpa only [mul, W, LinearMap.domRestrict_apply, LinearMap.mulLeft_apply, Nat.add_comm]
      using CJ0_4.mul_mem_bandSpace hf p.property
  let g : CJ0_4.bandSpace a d e →ₗ[Geo] W := mul.codRestrict W hmul
  have hg (p : CJ0_4.bandSpace a d e) : g p ∈ LinearMap.ker F := by
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (sourceIdealHigh T) (T.equation * p.val) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨p.val, rfl⟩)
  let G := g.codRestrict (LinearMap.ker F) hg
  have hG : Function.Injective G := by
    intro p q hpq
    have he : T.equation * p.val = T.equation * q.val :=
      congrArg (fun x : LinearMap.ker F => x.val.val) hpq
    exact Subtype.ext (mul_left_cancel₀ hn he)
  have hRank := F.finrank_range_add_finrank_ker
  rw [hF] at hRank
  exact (Nat.add_le_add_left (LinearMap.finrank_le_finrank_of_injective hG) _).trans_eq hRank

private theorem band_difference_high (a d e b j c : ℚ) :
    ∃ u v : ℚ, ∀ x : ℚ,
      CJ0_4.bandCount (x * a + j + 2 * c + b) (x * d + 2 * c + j) (x * e + c) -
        CJ0_4.bandCount (x * a + j + 2 * c) (x * d + 2 * c) (x * e) =
      (CJ0_4.surfaceBound a d e b j c / 2) * x ^ 2 + u * x + v := by
  let f (x : ℚ) :=
    CJ0_4.bandCount (x * a + j + 2 * c + b) (x * d + 2 * c + j) (x * e + c) -
      CJ0_4.bandCount (x * a + j + 2 * c) (x * d + 2 * c) (x * e)
  refine ⟨f 1 - f 0 - CJ0_4.surfaceBound a d e b j c / 2, f 0, fun x => ?_⟩
  dsimp [f, CJ0_4.bandCount, CJ0_4.surfaceBound]
  ring

private theorem degree_le_of_quadratic_high
    (I : Ideal CoeffRingHigh) (hdim : (affineHilbertPolynomial I).natDegree = 2)
    (q u v : ℚ) (hle : ∀ᶠ m : ℕ in atTop,
      (affineHilbertPolynomial I).eval (m : ℚ) ≤ q * (m : ℚ) ^ 2 + u * (m : ℚ) + v) :
    affineDegree I ≤ 2 * q := by
  let P : Polynomial ℚ := Polynomial.C q * Polynomial.X ^ 2 +
    Polynomial.C u * Polynomial.X + Polynomial.C v
  have hP : ∀ᶠ m : ℕ in atTop, (affineHilbertPolynomial I).eval (m : ℚ) ≤ P.eval (m : ℚ) := by
    filter_upwards [hle] with m hm
    simpa [P] using hm
  obtain ⟨hnat, hlead⟩ := Polynomial.natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg I) hP
  have hdeg : P.natDegree = 2 := by
    apply le_antisymm
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      have h₀ : i ≠ 0 := by omega
      have h₁ : i ≠ 1 := by omega
      have h₂ : i ≠ 2 := by omega
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
      simp [h₀, h₁, h₂]
    · simpa only [hdim] using hnat
  have hc : P.leadingCoeff = q := by
    rw [Polynomial.leadingCoeff, hdeg]
    simp [P]
  have hcoeff := hlead (hdim.trans hdeg.symm)
  rw [hc] at hcoeff
  rw [affineDegree, hdim]
  exact mul_le_mul_of_nonneg_left hcoeff (by norm_num)

theorem chart_degree_high (T : ChartHigh 2) (hT : ChartOKHigh T)
    (hdim : (affineHilbertPolynomial T.ideal).natDegree = 2)
    (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d)
    (hD : T.denominator ∈ CJ0_4.bandSpace a d e)
    (hN : ∀ i : Fin kHigh, T.numerator i ∈ CJ0_4.bandSpace a d e) :
    affineDegree T.ideal ≤ CJ0_4.surfaceBound a d e T.equation.totalDegree
      ((T.equation.weightedTotalDegree Fin.val : ℕ) : ℚ) (T.equation.degreeOf (Fin.last 2)) := by
  let b := T.equation.totalDegree
  let j := T.equation.weightedTotalDegree Fin.val
  let c := T.equation.degreeOf (Fin.last 2)
  have hf : T.equation ∈ CJ0_4.bandSpace b j c := CJ0_4.mem_bandSpace.mpr ⟨le_rfl, le_rfl, le_rfl⟩
  obtain ⟨u, v, hexpand⟩ := band_difference_high a d e b j c
  have hle : ∀ᶠ m : ℕ in atTop, (affineHilbertPolynomial T.ideal).eval (m : ℚ) ≤
      (CJ0_4.surfaceBound a d e b j c / 2) * (m : ℚ) ^ 2 + u * (m : ℚ) + v := by
    filter_upwards [eventually_eval_affineHilbertPolynomial T.ideal] with m hm
    have hma := Nat.mul_le_mul_left m hda
    have hme : 2 * (m * e) ≤ m * d := by
      simpa only [Nat.mul_left_comm 2 m e] using Nat.mul_le_mul_left m hed
    have hmono : Module.finrank Geo (quotientBandHigh T (m * a) (m * d) (m * e)) ≤
        Module.finrank Geo (quotientBandHigh T (m * a + j + 2 * c + b) (m * d + 2 * c + j) (m * e + c)) :=
      Submodule.finrank_mono (quotientBandHigh_mono T (by omega) (by omega) (by omega))
    have hdimNat := (Nat.add_le_add_right ((c1_high T a d e hT hD hN m).trans hmono) _).trans
      (quotientBandHigh_add_finrank_le T (m * a + j + 2 * c) (m * d + 2 * c) (m * e) b j c
        hT.irreducible.ne_zero hf)
    have hdimRat := (Nat.cast_le (α := ℚ)).mpr hdimNat
    rw [Nat.cast_add,
      CJ0_4_2.proof (m * a + j + 2 * c) (m * d + 2 * c) (m * e) (by omega) (by omega),
      CJ0_4_2.proof (m * a + j + 2 * c + b) (m * d + 2 * c + j) (m * e + c) (by omega) (by omega)] at hdimRat
    push_cast at hdimRat
    rw [hm, ← hexpand (m : ℚ)]
    exact le_sub_iff_add_le.mpr hdimRat
  calc
    _ ≤ 2 * (CJ0_4.surfaceBound a d e b j c / 2) :=
      degree_le_of_quadratic_high T.ideal hdim (CJ0_4.surfaceBound a d e b j c / 2) u v hle
    _ = _ := by ring

def bandVolumeHigh (s : BoxShape) (L b j c : ℕ) : ℚ :=
  volumeTotal s L * b + volumeIndex s L * j + volumeTop s L * c

def slicePriceHigh (A : ℕ) (s : BoxShape) (L b j c : ℕ) : ℚ :=
  curveFactor A * bandVolumeHigh s L b j c + (totalCap s L : ℚ) * b

theorem volume_nonneg_high (s : BoxShape) (hs : BoxOK s) (L : ℕ) (hL : 3 ≤ L) :
    0 ≤ volumeTotal s L ∧ 0 ≤ volumeIndex s L ∧ 0 ≤ volumeTop s L := by
  have hd : (indexCap s L : ℚ) ≤ totalCap s L := by exact_mod_cast indexCap_le_totalCap s hs L hL
  have he : 2 * (topCap s L : ℚ) ≤ indexCap s L := by exact_mod_cast twice_topCap_le s L
  have ha : 0 ≤ (totalCap s L : ℚ) := Nat.cast_nonneg _
  have ht : 0 ≤ (topCap s L : ℚ) := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · unfold volumeTotal; exact mul_nonneg (by positivity) (by linarith)
  · unfold volumeIndex; exact mul_nonneg ht (by linarith)
  · unfold volumeTop; exact mul_nonneg (by linarith) (by linarith)

theorem volumeDegree_high (s : BoxShape) (hs : BoxOK s) (L : ℕ) (hL : 3 ≤ L)
    (T : ChartHigh 2) (hT : ChartOKHigh T) (hb : ShortBandHigh s L T) :
    affineDegree T.ideal ≤ bandVolumeHigh s L T.equation.totalDegree
      (T.equation.weightedTotalDegree Fin.val) (T.equation.degreeOf (Fin.last 2)) := by
  simpa only [CJ0_4.surfaceBound, bandVolumeHigh, volumeTotal, volumeIndex, volumeTop] using
    (chart_degree_high T hT (image_geometry_high T hT).2
      (totalCap s L) (indexCap s L) (topCap s L) (indexCap_le_totalCap s hs L hL)
      (twice_topCap_le s L) (CJ0_4.mem_bandSpace.mpr hb.denominator)
      (fun i => CJ0_4.mem_bandSpace.mpr (hb.numerator i)))

theorem weighted_price_high (A common : ℕ) (s : BoxShape) (hs : BoxOK s)
    (hA : kHigh + 5 ≤ A) (hAn : A ≤ nHigh) (hc : common ≤ NHigh) (b j c : ℕ) :
    incidenceFactor A common * slicePriceHigh A s (shortLength common) b j c ≤
      baseFactor A * slicePriceHigh A s kHigh b j c := by
  let L := shortLength common
  have hL : 3 ≤ L := le_max_left ..
  have hK : L ≤ kHigh := max_le (by decide) (Nat.sub_le ..)
  obtain ⟨ha, hu, hv, hw⟩ := volumeScale s hs L hL hK
  have hscl : (kHigh : ℚ) * slicePriceHigh A s L b j c ≤
      (L : ℚ) * slicePriceHigh A s kHigh b j c := by
    have hui := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg b)
    have hvi := mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg j)
    have hwi := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg c)
    have hai := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg b)
    have hcurve : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hvol := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hui hvi) hwi) hcurve
    unfold slicePriceHigh bandVolumeHigh
    nlinarith only [hvol, hai]
  have hp : 0 ≤ slicePriceHigh A s kHigh b j c := by
    obtain ⟨hu, hv, hw⟩ := volume_nonneg_high s hs kHigh (by decide)
    have hcurve : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    unfold slicePriceHigh bandVolumeHigh
    positivity
  have h := mul_le_mul_of_nonneg_left hscl (show 0 ≤ incidenceFactor A common by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have h' := mul_le_mul_of_nonneg_right (incidenceLength A common hA hAn hc) hp
  have h'' : (kHigh : ℚ) * (incidenceFactor A common * slicePriceHigh A s L b j c) ≤
      (kHigh : ℚ) * (baseFactor A * slicePriceHigh A s kHigh b j c) := by
    nlinarith only [h, h']
  exact le_of_mul_le_mul_left h'' (by positivity)

theorem volume_full_high (s : BoxShape) (hs : BoxOK s) :
    bandVolumeHigh s kHigh s.B s.J s.C = R2High s := by
  have hda : DHigh s ≤ a0High s := indexCap_le_totalCap s hs kHigh (by decide)
  have hde : 2 * eHigh s ≤ DHigh s := twice_topCap_le s kHigh
  have hD' : DHigh s ≤ 2 * a0High s := by omega
  have hJ' : s.J ≤ 2 * s.B := by have := hs.total_index; omega
  have he' : eHigh s ≤ DHigh s := by omega
  have hC' : 2 * s.C * eHigh s ≤ s.C * DHigh s + eHigh s * s.J := by
    calc
      _ = s.C * (2 * eHigh s) := by ring
      _ ≤ s.C * DHigh s := Nat.mul_le_mul_left _ hde
      _ ≤ _ := Nat.le_add_right _ _
  unfold bandVolumeHigh volumeTotal volumeIndex volumeTop
  rw [show totalCap s kHigh = a0High s by rfl,
    show indexCap s kHigh = DHigh s by rfl,
    show topCap s kHigh = eHigh s by rfl]
  dsimp [R2High]
  push_cast [Nat.cast_sub hD', Nat.cast_sub hJ', Nat.cast_sub he', Nat.cast_sub hC']
  ring

/-! ## Section 3: Evaluation-Section Capacity (`ScalarCutCapacity.cutCap` at `kHigh`) -/

private def pullbackHigh (T : ChartHigh 2) (x a : K) : InitialRing 2 :=
  (∑ j : Fin kHigh, MvPolynomial.C (embed x ^ j.val) * T.numerator j) -
    MvPolynomial.C (embed a) * T.denominator

private theorem pullbackHigh_degree (T : ChartHigh 2) (x a : K) (b : ℕ)
    (hd : T.denominator.totalDegree ≤ b) (hn : ∀ j, (T.numerator j).totalDegree ≤ b) :
    (pullbackHigh T x a).totalDegree ≤ b := by
  apply (totalDegree_sub _ _).trans
  refine max_le (totalDegree_finsetSum_le ?_) ?_
  · intro j _
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hn j)
  · exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hd)

private theorem eval_pullbackHigh (T : ChartHigh 2) (x a : K) (y : Fin 3 → Geo)
    (hd : MvPolynomial.eval y T.denominator ≠ 0) :
    MvPolynomial.eval y (pullbackHigh T x a) =
      MvPolynomial.eval (T.output y) (valueCutHigh x a) * MvPolynomial.eval y T.denominator := by
  simp only [pullbackHigh, valueCutHigh, map_sub, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, ChartHigh.output]
  rw [sub_mul, sum_mul]
  refine congrArg₂ (· - ·) (sum_congr rfl ?_) rfl
  intro j _
  rw [mul_assoc, div_mul_cancel₀ _ hd]

private def componentImageHigh (T : ChartHigh 2) (Q : Ideal (InitialRing 2)) :
    Set (Fin kHigh → Geo) :=
  T.output '' {y | y ∈ zeroLocus Geo Q ∧ MvPolynomial.eval y T.denominator ≠ 0}

private theorem belongs_chart_high (T : ChartHigh 2) {Q : Ideal (InitialRing 2)}
    (hle : sourceIdealHigh T ≤ Q) {y : Fin 3 → Geo}
    (hy : y ∈ zeroLocus Geo Q) (hd : MvPolynomial.eval y T.denominator ≠ 0) : y ∈ T.locus :=
  ⟨hy _ (hle (Ideal.mem_span_singleton_self T.equation)), hd⟩

private theorem clear_at_chart_high (T : ChartHigh 2) (P : CoeffRingHigh) :
    ∃ R : InitialRing 2, ∃ m : ℕ, ∀ y ∈ T.locus,
      MvPolynomial.eval y R = MvPolynomial.eval (T.output y) P * MvPolynomial.eval y T.denominator ^ m := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator) (chartMapHigh T P)
  obtain ⟨R, rfl⟩ := Ideal.Quotient.mk_surjective a
  change chartMapHigh T P * localizeHigh T T.denominator ^ m = localizeHigh T R at ha
  refine ⟨R, m, fun y hy => ?_⟩
  have hh := congrArg (openEvalHigh hy) ha
  rw [map_mul, map_pow, openEvalHigh_chartMap hy, openEvalHigh_localize hy,
    openEvalHigh_localize hy] at hh
  exact hh.symm

private theorem component_image_prime_high (T : ChartHigh 2) (Q : Ideal (InitialRing 2))
    (hQ : Q.IsPrime) (hle : sourceIdealHigh T ≤ Q) (hD : T.denominator ∉ Q) :
    (vanishingIdeal Geo (componentImageHigh T Q)).IsPrime := by
  let _ := hQ
  have hrad := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := Geo) Q
  have hpoint : ∃ y ∈ zeroLocus Geo Q, MvPolynomial.eval y T.denominator ≠ 0 := by
    by_contra! h
    apply hD
    rw [← hrad]
    exact h
  apply Ideal.isPrime_iff.mpr
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨y, hy, hdy⟩ := hpoint
    have hone : (1 : CoeffRingHigh) ∈ vanishingIdeal Geo (componentImageHigh T Q) := by
      rw [h]; trivial
    have hh := hone _ ⟨y, ⟨hy, hdy⟩, rfl⟩
    exact one_ne_zero (by simpa only [map_one] using hh)
  · intro P₁ P₂ hmul
    obtain ⟨R₁, m₁, h₁⟩ := clear_at_chart_high T P₁
    obtain ⟨R₂, m₂, h₂⟩ := clear_at_chart_high T P₂
    have hRs : T.denominator * (R₁ * R₂) ∈ Q := by
      rw [← hrad]
      intro y hy
      change MvPolynomial.eval y (T.denominator * (R₁ * R₂)) = 0
      by_cases hdy : MvPolynomial.eval y T.denominator = 0
      · rw [map_mul, hdy, zero_mul]
      · have hchart := belongs_chart_high T hle hy hdy
        have hh : MvPolynomial.eval (T.output y) (P₁ * P₂) = 0 := hmul _ ⟨y, ⟨hy, hdy⟩, rfl⟩
        rw [map_mul] at hh
        rw [map_mul, map_mul, h₁ y hchart, h₂ y hchart]
        calc
          _ = (MvPolynomial.eval (T.output y) P₁ * MvPolynomial.eval (T.output y) P₂) *
              (MvPolynomial.eval y T.denominator * MvPolynomial.eval y T.denominator ^ m₁ *
                MvPolynomial.eval y T.denominator ^ m₂) := by ring
          _ = 0 := by rw [hh, zero_mul]
    have hor := hQ.mem_or_mem ((hQ.mem_or_mem hRs).resolve_left hD)
    have conclude {P : CoeffRingHigh} {R : InitialRing 2} {m : ℕ}
        (hr : R ∈ Q) (he : ∀ y ∈ T.locus,
          MvPolynomial.eval y R =
            MvPolynomial.eval (T.output y) P * MvPolynomial.eval y T.denominator ^ m) :
        P ∈ vanishingIdeal Geo (componentImageHigh T Q) := by
      rintro _ ⟨y, ⟨hy, hdy⟩, rfl⟩
      have hval : MvPolynomial.eval y R = 0 := hy R hr
      exact (mul_eq_zero.mp ((he y (belongs_chart_high T hle hy hdy)).symm.trans hval)).resolve_right
        (pow_ne_zero _ hdy)
    exact hor.imp (fun hr => conclude hr h₁) (fun hr => conclude hr h₂)

private theorem component_target_high (T : ChartHigh 2) (x a : K)
    {Q : Ideal (InitialRing 2)} (hQ : Q.IsPrime) (hle : sourceIdealHigh T ≤ Q)
    (hD : T.denominator ∉ Q) (hcut : pullbackHigh T x a ∈ Q) :
    ∃ P ∈ (T.ideal ⊔ Ideal.span {valueCutHigh x a}).minimalPrimesFinset,
      componentImageHigh T Q ⊆ zeroLocus Geo P := by
  let J := vanishingIdeal Geo (componentImageHigh T Q)
  let _ : J.IsPrime := component_image_prime_high T Q hQ hle hD
  have hT : T.ideal ≤ J := by
    intro q hq
    rintro _ ⟨y, ⟨hy, hdy⟩, rfl⟩
    exact hq _ ⟨y, belongs_chart_high T hle hy hdy, rfl⟩
  have hC : valueCutHigh x a ∈ J := by
    rintro _ ⟨y, ⟨hy, hdy⟩, rfl⟩
    have he : MvPolynomial.eval y (pullbackHigh T x a) = 0 := hy _ hcut
    exact (mul_eq_zero.mp ((eval_pullbackHigh T x a y hdy).symm.trans he)).resolve_right hdy
  obtain ⟨P, hP, hPJ⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hT ((Ideal.span_singleton_le_iff_mem J).mpr hC))
  exact ⟨P, Ideal.mem_minimalPrimesFinset.mpr hP, fun y hy q hq => hPJ hq _ hy⟩

theorem cutCap_high {A w} {V : Finset (Polynomial K)} (T : ChartHigh 2) (hT : ChartOKHigh T)
    (hA : AgreementOKHigh A) (hV : (V : Set (Polynomial K)) ⊆ closeHigh A w)
    (hcover : ∀ f ∈ V, coeffPointHigh f ∈ T.imageSet)
    (i : Node) (hmiss : ∃ f ∈ V, f.eval (node i) ≠ w i)
    (a : ℕ) (hden : T.denominator.totalDegree ≤ a) (hnum : ∀ j, (T.numerator j).totalDegree ≤ a) :
    (gapHigh A : ℚ) * (V.filter (fun f => f.eval (node i) = w i)).card ≤
      (errorsHigh A : ℚ) * affineDegree T.ideal + (gapHigh A : ℚ) * (a * T.equation.totalDegree : ℕ) := by
  classical
  let x := node i
  let b := w i
  let c := valueCutHigh x b
  let r := pullbackHigh T x b
  let J := sourceIdealHigh T ⊔ Ideal.span {r}
  let D := T.ideal ⊔ Ideal.span {c}
  let src := J.retainedMinimalPrimes T.denominator
  let Vhit := V.filter fun f => f.eval x = b
  have hp : (sourceIdealHigh T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  let _ := hp
  obtain ⟨hprime, hdim⟩ := image_geometry_high T hT
  let _ := hprime
  have hsrcDim : (affineHilbertPolynomial (sourceIdealHigh T)).natDegree = 2 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      hT.irreducible.ne_zero hp.ne_top
    rw [Nat.card_fin] at h
    exact Nat.add_right_cancel h
  obtain ⟨f, hf, hmiss⟩ := hmiss
  obtain ⟨y, hy, hyf⟩ := hcover f hf
  have hcNe : MvPolynomial.eval (T.output y) c ≠ 0 := by
    rw [hyf]
    exact fun h => hmiss ((valueCutHigh_eval (hV hf).1 x b).mp h)
  have hc : c ∉ T.ideal := fun hm => hcNe (hm _ ⟨y, hy, rfl⟩)
  have hr : r ∉ sourceIdealHigh T := by
    intro hh
    have hpt : y ∈ zeroLocus Geo (sourceIdealHigh T) := by
      apply mem_zeroLocus_iff_le_ker_aeval.mpr
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact RingHom.mem_ker.mpr hy.1
    have he : MvPolynomial.eval y r = 0 := hpt _ hh
    rw [eval_pullbackHigh T x b y hy.2] at he
    exact mul_ne_zero hcNe hy.2 he
  have srcDegree : (src.card : ℚ) ≤ (a * T.equation.totalDegree : ℕ) := by
    have hs := principalCut_sum_affineDegree_minimalPrimes_le hr (pullbackHigh_degree T x b a hden hnum)
    rw [show affineDegree (sourceIdealHigh T) = (T.equation.totalDegree : ℚ) from
      affineDegree_span_singleton hT.irreducible.ne_zero] at hs
    rw [Nat.cast_mul]
    calc
      _ = ∑ Q ∈ src, (1 : ℚ) := by simp
      _ ≤ ∑ Q ∈ src, affineDegree Q := by
        apply sum_le_sum
        intro Q hQ
        have hmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
        have hq := principalCut_natDegree_affineHilbertPolynomial_add_one hr hmin
        obtain ⟨n, hn, he⟩ := curve_degree_nat Q hmin.isPrime (by omega)
        rw [he]
        exact_mod_cast hn
      _ ≤ ∑ Q ∈ J.minimalPrimesFinset, affineDegree Q :=
        sum_le_sum_of_subset_of_nonneg (Ideal.retainedMinimalPrimes_subset _ _)
          (fun Q _ _ => affineDegree_nonneg Q)
      _ ≤ _ := hs
  have hcomp (Q : Ideal (InitialRing 2)) (hQ : Q ∈ src) :
      ∃ P ∈ D.minimalPrimesFinset, componentImageHigh T Q ⊆ zeroLocus Geo P := by
    obtain ⟨hmin, hdenQ⟩ := Ideal.mem_retainedMinimalPrimes.mp hQ
    exact component_target_high T x b hmin.isPrime (le_sup_left.trans hmin.le) hdenQ
      (hmin.le ((show Ideal.span {r} ≤ J from le_sup_right) (Ideal.mem_span_singleton_self r)))
  let pick (Q : Ideal (InitialRing 2)) : Ideal CoeffRingHigh :=
    if hQ : Q ∈ src then (hcomp Q hQ).choose else ⊤
  have picked (Q : Ideal (InitialRing 2)) (hQ : Q ∈ src) :
      pick Q ∈ D.minimalPrimesFinset ∧ componentImageHigh T Q ⊆ zeroLocus Geo (pick Q) := by
    dsimp only [pick]
    rw [dite_eq_left hQ]
    exact (hcomp Q hQ).choose_spec
  let Ps := src.image pick
  have hPs : Ps ⊆ D.minimalPrimesFinset := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hP
    exact (picked Q hQ).1
  let part (P : Ideal CoeffRingHigh) := Vhit.filter fun f => coeffPointHigh f ∈ zeroLocus Geo P
  have hpart : Vhit ⊆ Ps.biUnion part := by
    intro f hf
    obtain ⟨hfV, hfb⟩ := mem_filter.mp hf
    obtain ⟨z, hz, hzf⟩ := hcover f hfV
    have hzEq : MvPolynomial.eval z r = 0 := by
      have hv : MvPolynomial.eval (coeffPointHigh f) (valueCutHigh x b) = 0 :=
        (valueCutHigh_eval (hV hfV).1 x b).mpr hfb
      rw [eval_pullbackHigh T x b z hz.2, hzf, hv, zero_mul]
    have hzJ : z ∈ zeroLocus Geo J := by
      apply mem_zeroLocus_sup_span_singleton_iff.mpr
      refine ⟨?_, hzEq⟩
      apply mem_zeroLocus_iff_le_ker_aeval.mpr
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact RingHom.mem_ker.mpr hz.1
    obtain ⟨Q, hQ, hzQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J T.denominator z hzJ hz.2
    refine mem_biUnion.mpr ⟨pick Q, mem_image.mpr ⟨Q, hQ, rfl⟩, mem_filter.mpr ⟨hf, ?_⟩⟩
    apply (picked Q hQ).2
    exact ⟨z, ⟨hzQ, hz.2⟩, hzf⟩
  have hone (P : Ideal CoeffRingHigh) (hP : P ∈ Ps) :
      (gapHigh A : ℚ) * (part P).card ≤ (errorsHigh A : ℚ) * affineDegree P + gapHigh A := by
    have hmin := Ideal.mem_minimalPrimesFinset.mp (hPs hP)
    have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hc hmin
    exact (curve_capacity_high (fun _ hf => hV (mem_filter.mp (mem_filter.mp hf).1).1) hA
      hmin.isPrime (by omega) (fun _ hf => (mem_filter.mp hf).2)).1
  have hsum : (Vhit.card : ℚ) ≤ ∑ P ∈ Ps, ((part P).card : ℚ) := by
    exact_mod_cast ((card_le_card hpart).trans card_biUnion_le)
  have hpdeg : (∑ P ∈ Ps, affineDegree P) ≤ affineDegree T.ideal := by
    apply (sum_le_sum_of_subset_of_nonneg hPs (fun P _ _ => affineDegree_nonneg P)).trans
    simpa only [D, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hc (valueCutHigh_degree x b)
  have hcard : (Ps.card : ℚ) ≤ (a * T.equation.totalDegree : ℕ) :=
    (Nat.cast_le.mpr card_image_le).trans srcDegree
  calc
    _ ≤ (gapHigh A : ℚ) * ∑ P ∈ Ps, ((part P).card : ℚ) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = ∑ P ∈ Ps, (gapHigh A : ℚ) * (part P).card := mul_sum ..
    _ ≤ _ := sum_le_sum hone
    _ = (errorsHigh A : ℚ) * (∑ P ∈ Ps, affineDegree P) + (gapHigh A : ℚ) * Ps.card := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm (Ps.card : ℚ)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hpdeg (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _))

/-! ## Section 4: Shortened Order-2 Charts at `kHigh = 133,721` -/

private theorem exponent_sufficient_high (length : ℕ) :
    TaylorExponentSufficient 2 length (exponent length) := by
  intro l
  have hl := l.isLt
  unfold exponent
  omega

private theorem top_monotone_high : Monotone (Pi.single (Fin.last 2) (1 : ℕ)) := by
  intro i j hij
  by_cases hi : i = Fin.last 2
  · have hj : j = Fin.last 2 := le_antisymm (Fin.le_last j) (hi ▸ hij)
    rw [hi, hj]
  · have hi₂ : i ≠ (2 : Fin 3) := hi
    have hw : (Pi.single (Fin.last 2) (1 : ℕ) : Fin 3 → ℕ) i = 0 := by simp [hi₂]
    rw [hw]
    exact Nat.zero_le _

private theorem lift_total_high {s : BoxShape} {G : CJ0_3.Equation} (hG : OrderTwoHigh s G)
    (g L : Polynomial K) :
    jetTotalDegree (CJ0_3.lifted (ShortenChart.transform g L G)) ≤ s.B := by
  rw [CJ0_3.lifted_total]
  have h := ShortenChart.transform_weight g L G 1 (fun _ _ _ => le_rfl)
  rw [CJ0_3.totalWeight_eq] at h
  exact h.trans hG.2.1

private theorem lift_index_high {s : BoxShape} {G : CJ0_3.Equation} (hG : OrderTwoHigh s G)
    (g L : Polynomial K) :
    (CJ0_3.lifted (ShortenChart.transform g L G)).weightedTotalDegree (Astra7.jetWeight 0 1 3) ≤ s.J := by
  rw [CJ0_3.lifted_weight, CJ0_3.indexWeight_eq]
  exact (ShortenChart.transform_weight g L G Fin.val (fun _ _ h => h)).trans hG.2.2.1

private theorem lift_top_high {s : BoxShape} {G : CJ0_3.Equation} (hG : OrderTwoHigh s G)
    (g L : Polynomial K) :
    (CJ0_3.lifted (ShortenChart.transform g L G)).degreeOf (some (Fin.last 2)) ≤ s.C := by
  change jetDegree (CJ0_3.lifted (ShortenChart.transform g L G)) (Fin.last 2) ≤ s.C
  rw [CJ0_3.lifted_top]
  have hw := ShortenChart.transform_weight g L G (Pi.single (Fin.last 2) 1) top_monotone_high
  have he : (fun v : Option (Fin 3) => v.elim 0 (Pi.single (Fin.last 2) 1)) =
      Pi.single (some (Fin.last 2)) (1 : ℕ) := by
    funext v
    cases v <;> simp [Pi.single_apply]
  rw [he, weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at hw
  exact hw.trans hG.2.2.2

private def basisPolynomialHigh (L : Polynomial K) (j : ℕ) : Polynomial Geo :=
  L.map embed * (Polynomial.X - Polynomial.C center) ^ j

private def rawDenominatorHigh (length : ℕ) (G : CJ0_3.Equation) : InitialRing 2 :=
  CJ0_3.initialSep G ^ exponent length

private def rawNumeratorHigh (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation)
    (i : Fin kHigh) : InitialRing 2 :=
  MvPolynomial.C ((g.map embed).coeff i.val) * rawDenominatorHigh length G +
    ∑ l : Fin length, MvPolynomial.C ((basisPolynomialHigh L l.val).coeff i.val) *
      commonTaylorNumerator center (CJ0_3.lifted G) (exponent length) l.val

def chartShortHigh (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation) (E : InitialRing 2) :
    ChartHigh 2 :=
  ⟨E, ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L)
      (rawDenominatorHigh length (ShortenChart.transform g L G)),
    fun i => ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L)
      (rawNumeratorHigh length g L (ShortenChart.transform g L G) i)⟩

private theorem rawDenominatorHigh_band (s : BoxShape) (length : ℕ) (hK : 3 ≤ length)
    (g L : Polynomial K) (G : CJ0_3.Equation) (hG : OrderTwoHigh s G) :
    InBandHigh s length (rawDenominatorHigh length (ShortenChart.transform g L G)) := by
  let Q := CJ0_3.lifted (ShortenChart.transform g L G)
  have hb : (initialJetSeparant center Q).totalDegree ≤ s.B - 1 :=
    (totalDegree_initialJetSeparant_le center Q).trans
      (Nat.sub_le_sub_right (lift_total_high hG g L) 1)
  have hi : (initialJetSeparant center Q).weightedTotalDegree Fin.val ≤ s.J - 2 := by
    simpa only [CJ0_3.coeffWeight_eq, zero_add, one_mul] using
      (Astra7.initialSeparant_weight 0 1 center Q).trans
        (Nat.sub_le_sub_right (lift_index_high hG g L) (0 + 1 * 2))
  have ht : (initialJetSeparant center Q).degreeOf (Fin.last 2) ≤ s.C - 1 :=
    (degreeOf_initialJetSeparant_le center Q).trans (Nat.sub_le_sub_right (lift_top_high hG g L) 1)
  have hindex : (initialJetSeparant center Q ^ exponent length).weightedTotalDegree Fin.val ≤
      indexCap s length :=
    ((weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ hi)).trans (by
      unfold indexCap; omega)
  refine ⟨((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hb)).trans (by unfold totalCap; omega),
    hindex, le_min ?_ (CJ0_3.degreeOf_top_of_index hindex)⟩
  exact ((degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ ht)).trans (by omega)

private theorem rawCenteredHigh_band (s : BoxShape) (hs : BoxOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : Polynomial K) (G : CJ0_3.Equation) (hG : OrderTwoHigh s G) (l : Fin length) :
    InBandHigh s length
      (commonTaylorNumerator center (CJ0_3.lifted (ShortenChart.transform g L G))
        (exponent length) l.val) := by
  let Q := CJ0_3.lifted (ShortenChart.transform g L G)
  have hlK := l.isLt
  have hJ := hs.index_top
  have hC := hs.top_pos
  have hi := Astra7.commonTaylor_weight 0 1 s.J length (exponent length) center Q
    (exponent_sufficient_high length) (by omega) (lift_index_high hG g L) l
  have hindex : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
      indexCap s length := by
    have h : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
        exponent length * (s.J - 2) + l.val := by
      simpa only [CJ0_3.coeffWeight_eq, zero_add, one_mul, add_zero] using hi
    exact h.trans (by unfold indexCap; omega)
  refine ⟨?_, hindex, le_min ?_ (CJ0_3.degreeOf_top_of_index hindex)⟩
  · exact (totalDegree_commonTaylorNumerator_le center Q (exponent_sufficient_high length l)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (lift_total_high hG g L) 1)) 1)
  · have hl : l.val - 1 ≤ length - 2 := by omega
    apply (CJ0_3_2.commonTaylor_top center Q hs.top_pos (lift_top_high hG g L)
      (exponent_sufficient_high length) l).trans
    rw [Nat.add_sub_assoc (by omega : 2 ≤ length)]
    exact Nat.add_le_add_left hl _

private theorem rawNumeratorHigh_band (s : BoxShape) (hs : BoxOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : Polynomial K) (G : CJ0_3.Equation) (hG : OrderTwoHigh s G) (i : Fin kHigh) :
    InBandHigh s length (rawNumeratorHigh length g L (ShortenChart.transform g L G) i) := by
  let V := CJ0_4.bandSpace (totalCap s length) (indexCap s length) (topCap s length)
  have hmem {P : InitialRing 2} (hp : InBandHigh s length P) : P ∈ V := CJ0_4.mem_bandSpace.mpr hp
  have hc (a : Geo) {P : InitialRing 2} (hp : InBandHigh s length P) : MvPolynomial.C a * P ∈ V := by
    rw [← MvPolynomial.smul_eq_C_mul]
    exact V.smul_mem _ (hmem hp)
  suffices h : rawNumeratorHigh length g L (ShortenChart.transform g L G) i ∈ V from
    CJ0_4.mem_bandSpace.mp h
  unfold rawNumeratorHigh
  exact V.add_mem (hc _ (rawDenominatorHigh_band s length hK g L G hG))
    (V.sum_mem fun l _ => hc _ (rawCenteredHigh_band s hs length hK g L G hG l))

private theorem inverse_band_high (s : BoxShape) (length : ℕ) (g L : Polynomial K) {P : InitialRing 2}
    (hp : InBandHigh s length P) :
    InBandHigh s length (ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) P) := by
  have hb := ShortenChart.inverse_weight (1 : Fin 3 → ℕ) (fun _ _ _ => le_rfl)
    (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) P
  have hi := ShortenChart.inverse_weight Fin.val (fun _ _ h => h)
    (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) P
  have ht := ShortenChart.inverse_weight (Pi.single (Fin.last 2) 1) top_monotone_high
    (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) P
  simp only [weightedTotalDegree_one] at hb
  simp only [weightedTotalDegree_piSingle] at ht
  exact ⟨hb.trans hp.1, hi.trans hp.2.1, ht.trans hp.2.2⟩

private theorem chartShortHigh_band (s : BoxShape) (hs : BoxOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : Polynomial K) (G : CJ0_3.Equation) (hG : OrderTwoHigh s G) (E : InitialRing 2) :
    ShortBandHigh s length (chartShortHigh length g L G E) :=
  ⟨inverse_band_high s length g L (rawDenominatorHigh_band s length hK g L G hG),
    fun i => inverse_band_high s length g L (rawNumeratorHigh_band s hs length hK g L G hG i)⟩

private theorem denominator_eval_high (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation)
    (E : InitialRing 2) (u : Fin 3 → Geo) (hL : L ≠ 0) :
    MvPolynomial.eval u (chartShortHigh length g L G E).denominator =
      (CJ0_3.nativeJet L 0 * MvPolynomial.eval u (CJ0_3.initialSep G)) ^ exponent length := by
  change MvPolynomial.eval u (ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L)
    (rawDenominatorHigh length (ShortenChart.transform g L G))) = _
  rw [ShortenChart.eval_inverse, rawDenominatorHigh, map_pow, ShortenChart.transform_initialSep,
    map_mul, MvPolynomial.eval_C, ShortenChart.eval_affine,
    ShortenChart.triangular_inverse _ _ _ (ShortenChart.nativeJet_zero_ne hL)]

private theorem denominator_regular_high (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation)
    (E : InitialRing 2) (hL : L ≠ 0) (hE : Irreducible E) (hreg : ¬ E ∣ CJ0_3.initialSep G) :
    ¬ E ∣ (chartShortHigh length g L G E).denominator := by
  have he : (chartShortHigh length g L G E).denominator =
      MvPolynomial.C (CJ0_3.nativeJet L 0 ^ exponent length) *
        (CJ0_3.initialSep G) ^ exponent length := by
    apply MvPolynomial.funext
    intro u
    rw [denominator_eval_high length g L G E u hL, map_mul, MvPolynomial.eval_C, map_pow, mul_pow]
  rw [he]
  have hu : IsUnit (MvPolynomial.C (CJ0_3.nativeJet L 0 ^ exponent length) : InitialRing 2) :=
    ((isUnit_iff_ne_zero).mpr (pow_ne_zero _ (ShortenChart.nativeJet_zero_ne hL))).map MvPolynomial.C
  intro h
  have hh := (hE.prime.dvd_or_dvd h).resolve_left (fun hd => hE.not_isUnit (isUnit_of_dvd_unit hd hu))
  exact hreg (hE.prime.dvd_of_dvd_pow hh)

private theorem reconstruct_basis_high (length : ℕ) (L : Polynomial K) (G : CJ0_3.Equation)
    (u : Fin 3 → Geo) :
    L.map embed * rationalTaylorPolynomial center (CJ0_3.lifted G) length u =
      ∑ l : Fin length, Polynomial.C (rationalTaylorCoefficient center (CJ0_3.lifted G) u l.val) *
        basisPolynomialHigh L l.val := by
  rw [rationalTaylorPolynomial, Polynomial.centeredCoefficientPrefix, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.taylor_monomial, map_neg, ← sub_eq_add_neg]
  unfold basisPolynomialHigh
  ring

private theorem raw_output_high (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation)
    (u : Fin 3 → Geo) (hsep : MvPolynomial.eval u (CJ0_3.initialSep G) ≠ 0) (i : Fin kHigh) :
    MvPolynomial.eval u (rawNumeratorHigh length g L G i) /
      MvPolynomial.eval u (rawDenominatorHigh length G) =
      (g.map embed + L.map embed * rationalTaylorPolynomial center (CJ0_3.lifted G) length u).coeff i.val := by
  have hpow : MvPolynomial.eval u (CJ0_3.initialSep G) ^ exponent length ≠ 0 := pow_ne_zero _ hsep
  rw [reconstruct_basis_high, Polynomial.coeff_add, Polynomial.finsetSum_coeff, rawNumeratorHigh,
    map_add, add_div, map_mul, MvPolynomial.eval_C, rawDenominatorHigh, map_pow,
    mul_div_cancel_right₀ _ hpow, map_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.coeff_C_mul, map_mul, MvPolynomial.eval_C, ← MvPolynomial.aeval_eq_eval (f := u),
    aeval_commonTaylorNumerator center (CJ0_3.lifted G) u (exponent_sufficient_high length l) hsep]
  change _ * (MvPolynomial.eval u (CJ0_3.initialSep G) ^ exponent length * _) /
    MvPolynomial.eval u (CJ0_3.initialSep G) ^ exponent length = _
  field_simp

private theorem chartShortHigh_output (length : ℕ) (hK : 3 ≤ length) (g L : Polynomial K)
    (G : CJ0_3.Equation) (E : InitialRing 2) (u : Fin 3 → Geo)
    (hu : MvPolynomial.eval u (chartShortHigh length g L G E).denominator ≠ 0) (i : Fin kHigh) :
    (chartShortHigh length g L G E).output u i =
      (g.map embed + L.map embed * rationalTaylorPolynomial center
        (CJ0_3.lifted (ShortenChart.transform g L G)) length
        (ShortenChart.inverseJet (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) u)).coeff i.val := by
  let v := ShortenChart.inverseJet (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) u
  have hv : MvPolynomial.eval v (CJ0_3.initialSep (ShortenChart.transform g L G)) ≠ 0 := by
    intro hh
    apply hu
    change MvPolynomial.eval u (ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L)
      (rawDenominatorHigh length (ShortenChart.transform g L G))) = 0
    rw [ShortenChart.eval_inverse, rawDenominatorHigh, map_pow, hh, zero_pow]
    unfold exponent
    omega
  rw [ChartHigh.output, chartShortHigh, ShortenChart.eval_inverse, ShortenChart.eval_inverse]
  exact raw_output_high length g L (ShortenChart.transform g L G) v hv i

private theorem geoJet_affine_high (g L h : Polynomial Geo) :
    polynomialJet (d := 2) center (g + L * h) =
      ShortenChart.triangular (polynomialJet center g) (polynomialJet center L)
        (polynomialJet center h) := by
  funext i
  change Polynomial.evalRingHom center (ShortenChart.derivatives (g + L * h) i) =
    ShortenChart.triangular (Polynomial.evalRingHom center ∘ ShortenChart.derivatives g)
      (Polynomial.evalRingHom center ∘ ShortenChart.derivatives L)
      (Polynomial.evalRingHom center ∘ ShortenChart.derivatives h) i
  rw [ShortenChart.derivatives_affine]
  exact ShortenChart.map_triangular (Polynomial.evalRingHom center) _ _ _ i

private theorem natDegree_lt_any {F : Type*} [Field F] {P : Polynomial F} {b : ℕ} (hb : 0 < b)
    (hp : P.degree < b) : P.natDegree < b := by
  by_cases hz : P = 0
  · simpa [hz] using hb
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hp

private theorem reconstruction_degree_high (length : ℕ) (hK : 3 ≤ length) (g L : Polynomial K)
    (hg : g.degree < kHigh) (hsum : L.natDegree + length ≤ kHigh) (G : CJ0_3.Equation)
    (u : Fin 3 → Geo) :
    (g.map embed + L.map embed * rationalTaylorPolynomial center (CJ0_3.lifted G) length u).degree <
      kHigh := by
  let U := rationalTaylorPolynomial center (CJ0_3.lifted G) length u
  have hU : U.natDegree < length :=
    natDegree_lt_any (by omega) (Polynomial.degree_centeredCoefficientPrefix_lt _ _ _)
  have hg' : (g.map embed).natDegree < kHigh :=
    Polynomial.natDegree_map_le.trans_lt (natDegree_lt_any (by decide) hg)
  have hm : (L.map embed * U).natDegree < kHigh :=
    (Polynomial.natDegree_mul_le).trans_lt
      ((Nat.add_lt_add_of_le_of_lt Polynomial.natDegree_map_le hU).trans_le hsum)
  have hh : (g.map embed + L.map embed * U).natDegree < kHigh :=
    (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hg' hm)
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hh)

private theorem chartShortHigh_ok (length : ℕ) (hK : 3 ≤ length) (g L : Polynomial K) (hL : L ≠ 0)
    (hg : g.degree < kHigh) (hsum : L.natDegree + length ≤ kHigh) (G : CJ0_3.Equation)
    (E : InitialRing 2) (hE : Irreducible E) (hreg : ¬ E ∣ CJ0_3.initialSep G) :
    ChartOKHigh (chartShortHigh length g L G E) := by
  refine ⟨hE, denominator_regular_high length g L G E hL hE hreg, ?_⟩
  intro u hu j
  let v := ShortenChart.inverseJet (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) u
  let U := rationalTaylorPolynomial center (CJ0_3.lifted (ShortenChart.transform g L G)) length v
  let P := g.map embed + L.map embed * U
  have hcoeff : (chartShortHigh length g L G E).output u = (fun i : Fin kHigh => P.coeff i.val) := by
    funext i
    exact chartShortHigh_output length hK g L G E u hu.2 i
  rw [hcoeff, show readJetHigh (fun i : Fin kHigh => P.coeff i.val) j.val =
    (polynomialJet (d := 2) center P) j from CJ0_3.readJet_eq P
      (reconstruction_degree_high length hK g L hg hsum (ShortenChart.transform g L G) v) j.val]
  have hU : polynomialJet (d := 2) center U = v :=
    polynomialJet_rationalTaylorPolynomial center (CJ0_3.lifted (ShortenChart.transform g L G))
      (by omega) v
  change (polynomialJet (d := 2) center (g.map embed + L.map embed * U)) j = u j
  rw [geoJet_affine_high, hU]
  exact congrFun (ShortenChart.triangular_inverse (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) u
    (ShortenChart.nativeJet_zero_ne hL)) j

private theorem chartShortHigh_contains (length : ℕ) (hK : 3 ≤ length) (hk : length ≤ kHigh)
    (g L : Polynomial K) (hL : L ≠ 0) (G : CJ0_3.Equation) (E : InitialRing 2)
    {f h : Polynomial K} (hh : h.degree < length) (hf : f = g + L * h)
    (hsol : differentialSpecialization G f = 0)
    (hE : MvPolynomial.eval (CJ0_3.nativeJet f) E = 0)
    (hsep : MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0) :
    coeffPointHigh f ∈ (chartShortHigh length g L G E).imageSet := by
  have hL0 := ShortenChart.nativeJet_zero_ne hL
  have hu : MvPolynomial.eval (CJ0_3.nativeJet f) (chartShortHigh length g L G E).denominator ≠ 0 := by
    rw [denominator_eval_high length g L G E _ hL]
    exact pow_ne_zero _ (mul_ne_zero hL0 hsep)
  have hv : ShortenChart.inverseJet (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) (CJ0_3.nativeJet f) =
      CJ0_3.nativeJet h := by
    rw [hf, ShortenChart.nativeJet_affine]
    exact ShortenChart.inverse_triangular _ _ _ hL0
  have hs : MvPolynomial.eval (CJ0_3.nativeJet h)
      (CJ0_3.initialSep (ShortenChart.transform g L G)) ≠ 0 := by
    rw [ShortenChart.transform_initialSep, map_mul, MvPolynomial.eval_C, ShortenChart.eval_affine,
      ← ShortenChart.nativeJet_affine, ← hf]
    exact mul_ne_zero hL0 hsep
  have hsol' : differentialSpecialization (CJ0_3.lifted (ShortenChart.transform g L G))
      (h.map embed) = 0 := by
    rw [CJ0_3.lifted, ← map_differentialSpecialization, ShortenChart.transform_spec, ← hf, hsol,
      Polynomial.map_zero]
  have hsep' : jetEvaluation (separant (CJ0_3.lifted (ShortenChart.transform g L G)) (Fin.last 2))
      center (CJ0_3.nativeJet h) ≠ 0 := by
    simpa only [CJ0_3.initialSep, ← MvPolynomial.aeval_eq_eval, aeval_initialJetSeparant] using hs
  let _ : CharP Geo p := charP_of_injective_ringHom embed.injective p
  have hbin (i : ℕ) (hlo : 2 < i) (hhi : i < length) : (i.choose 2 : Geo) ≠ 0 := by
    have hb := natCast_choose_ne_zero_of_ringChar (F := Geo)
      (D := kHigh) (s := 2) (Or.inr (by rw [ringChar.eq Geo p]; norm_num)) (i - 2) (by omega)
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hlo)] using hb
  have hrec := rationalTaylorPolynomial_polynomialJet center
    (CJ0_3.lifted (ShortenChart.transform g L G)) (h.map embed) hsol' hsep'
    (Polynomial.degree_map_le.trans_lt hh) hbin
  refine ⟨CJ0_3.nativeJet f, ⟨hE, hu⟩, ?_⟩
  funext i
  rw [chartShortHigh_output length hK g L G E _ hu, hv, CJ0_3.nativeJet, hrec,
    ← Polynomial.map_mul, ← Polynomial.map_add, ← hf, Polynomial.coeff_map]
  rfl

theorem shortenChart_high (s : BoxShape) (hs : BoxOK s) (G : CJ0_3.Equation)
    (hG : OrderTwoHigh s G) (E : InitialRing 2) (hE : Irreducible E)
    (_hEdvd : E ∣ CJ0_3.initial G) (hreg : ¬ E ∣ CJ0_3.initialSep G)
    (S : Finset Node) (hS : S.card + 3 ≤ kHigh) (w : Node → K) :
    ∃ T : ChartHigh 2, ChartOKHigh T ∧ T.equation = E ∧ ShortBandHigh s (kHigh - S.card) T ∧
      ∀ f : Polynomial K, f.degree < kHigh → differentialSpecialization G f = 0 →
        MvPolynomial.eval (CJ0_3.nativeJet f) E = 0 →
        MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0 →
        (∀ i ∈ S, f.eval (node i) = w i) → coeffPointHigh f ∈ T.imageSet := by
  classical
  let g := Lagrange.interpolate S node w
  let L := FrobeniusLocator.locator node S
  let length := kHigh - S.card
  have hK : 3 ≤ length := by dsimp [length]; omega
  have hk : length ≤ kHigh := Nat.sub_le _ _
  have hL := (FrobeniusLocator.locator_monic node S).ne_zero
  have hLn : L.natDegree = S.card := FrobeniusLocator.locator_natDegree _ _
  have hx : Function.Injective node := ProximityPrize.Benchmark.IRSProfile.domain.injective
  have hg : g.degree < kHigh := (Lagrange.degree_interpolate_lt w hx.injOn).trans_le
    (by exact_mod_cast (show S.card ≤ kHigh by omega))
  have hsum : L.natDegree + length ≤ kHigh := by rw [hLn]; dsimp [length]; omega
  refine ⟨chartShortHigh length g L G E, chartShortHigh_ok length hK g L hL hg hsum G E hE hreg,
    rfl, chartShortHigh_band s hs length hK g L G hG E, ?_⟩
  intro f hf hroot hEroot hsep hits
  have hdiv : L ∣ f - g := FrobeniusLocator.Strata.locator_dvd_of_eval_zero node hx S _
    (fun i hi => by
      rw [Polynomial.eval_sub, hits i hi, show g.eval (node i) = w i from
        Lagrange.eval_interpolate_at_node w hx.injOn hi, sub_self])
  have hd : (f - g).degree < kHigh := (Polynomial.degree_sub_le _ _).trans_lt (max_lt hf hg)
  have hdN : (f - g).natDegree ≤ NHigh := by
    have hh := natDegree_lt_any (by decide) hd
    change _ < 133721 at hh
    change _ ≤ 133720
    omega
  have hS' : S.card ≤ NHigh := by
    change _ ≤ 133721 at hS
    change _ ≤ 133720
    omega
  obtain ⟨h, hdeg, he⟩ :=
    FrobeniusLocator.Strata.bounded_locator_quotient node S (f - g) NHigh hS' hdN hdiv
  have hf' : f = g + L * h := by rw [← he]; ring
  have hlen : NHigh - S.card + 1 = length := by
    dsimp [length]
    change _ ≤ 133721 at hS
    change 133720 - S.card + 1 = 133721 - S.card
    omega
  rw [hlen] at hdeg
  exact chartShortHigh_contains length hK hk g L hL G E hdeg hf' hroot hEroot hsep

/-! ## Section 5: Order-2 → Order-1 Elimination, Order-1 Charts, and Order-0 Exceptional Locus -/

private theorem eliminate_ne_zero_high {G : DifferentialPolynomial K 2} (hG : Irreducible G)
    (hchar : jetDegree G (Fin.last 2) < p) : CJ0_5.eliminate G ≠ 0 := by
  let P := Sol1.C57.topPresentation 1 G
  let c := P.natDegree
  have hi : Irreducible P :=
    (MulEquiv.irreducible_iff (Sol1.C57.topPresentation 1).toMulEquiv).mpr hG
  change (if c = 0 then P.coeff 0 else P.resultant P.derivative c (c - 1)) ≠ 0
  by_cases h : c = 0
  · have hn := leadingCoeff_ne_zero.mpr hi.ne_zero
    change P.coeff c ≠ 0 at hn
    simpa only [h, ite_true] using hn
  · have hlt : c < p := (Sol1.C57.topPresentation_degree 1 G).trans_lt hchar
    have hcast : (c : K) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hlt) (Nat.le_of_dvd (Nat.pos_of_ne_zero h)
        ((CharP.cast_eq_zero_iff K p c).mp hz))
    have hc : (c : DifferentialPolynomial K 1) ≠ 0 := by
      simpa only [map_natCast, map_zero] using (MvPolynomial.C_injective _ K).ne hcast
    have hder : P.derivative ≠ 0 := by
      intro hz
      have hindex : c - 1 + 1 = c := by omega
      have hz' := congrArg (fun R : Polynomial (DifferentialPolynomial K 1) => R.coeff (c - 1)) hz
      rw [coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one, hindex, coeff_zero] at hz'
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr hi.ne_zero) hc hz'
    simpa only [ite_eq_right h] using Polynomial.resultant_derivative_ne_zero_of_irreducible P hi hder

private theorem eliminate_root_high (G : DifferentialPolynomial K 2) (f : Polynomial K)
    (hG : differentialSpecialization G f = 0)
    (hsep : differentialSpecialization (separant G (Fin.last 2)) f = 0) :
    differentialSpecialization (CJ0_5.eliminate G) f = 0 := by
  let P := Sol1.C57.topPresentation 1 G
  let ψ := (differentialSpecializationHom (d := 1) f).toRingHom
  have he : P.eval₂ ψ (hasseDeriv 2 f) = 0 := (Sol1.C57.topPresentation_eval 1 G f).trans hG
  change ψ (if P.natDegree = 0 then P.coeff 0 else
    P.resultant P.derivative P.natDegree (P.natDegree - 1)) = 0
  by_cases hc : P.natDegree = 0
  · rw [ite_eq_left hc]
    have h := congrArg (fun R : Polynomial (DifferentialPolynomial K 1) =>
      R.eval₂ ψ (hasseDeriv 2 f)) (eq_C_of_natDegree_eq_zero hc)
    change P.eval₂ ψ (hasseDeriv 2 f) = _ at h
    rw [Polynomial.eval₂_C] at h
    exact h.symm.trans he
  · rw [ite_eq_right hc]
    have hd : P.derivative.eval₂ ψ (hasseDeriv 2 f) = 0 := by
      change (Sol1.C57.topPresentation 1 G).derivative.eval₂ ψ _ = 0
      rw [Sol1.C57.topPresentation_derivative, Sol1.C57.topPresentation_eval]
      exact hsep
    exact Sol1.C40Primitives.map_resultant_eq_zero_of_common_root ψ P P.derivative
      P.natDegree (P.natDegree - 1) le_rfl (natDegree_derivative_le P) (Or.inl hc)
      (hasseDeriv 2 f) he hd

private theorem input_total_high :
    CJ0_5.inputWeight 1 jetDegreeWeight = jetDegreeWeight := by
  funext v
  rcases v with _ | j
  · simp [CJ0_5.inputWeight]
  · induction j using Fin.lastCases with
    | last => simp only [CJ0_5.inputWeight, Sol1.C57.topVariableEquiv_top, Option.elim_none,
        jetDegreeWeight_some]
    | cast j => simp [CJ0_5.inputWeight]

private theorem input_index_high :
    CJ0_5.inputWeight 2 CJ0.indexWeight = CJ0.indexWeight := by
  funext v
  rcases v with _ | j
  · simp [CJ0_5.inputWeight, CJ0.indexWeight]
  · induction j using Fin.lastCases with
    | last =>
      rw [CJ0_5.inputWeight, Sol1.C57.topVariableEquiv_top]
      rfl
    | cast j => simp [CJ0_5.inputWeight, CJ0.indexWeight]

private theorem output_index_high :
    CJ0.indexWeight = (Pi.single (some (Fin.last 1)) 1 : JetVariable 1 → ℕ) := by
  funext v
  rcases v with _ | j
  · simp [CJ0.indexWeight]
  · induction j using Fin.lastCases with
    | last =>
      change 1 = (Pi.single (some (Fin.last 1)) 1 : JetVariable 1 → ℕ) (some (Fin.last 1))
      simp only [Pi.single_eq_same]
    | cast j =>
      have hne : some j.castSucc ≠ some (Fin.last 1) :=
        (Option.some_injective _).ne (Fin.castSucc_ne_last j)
      rw [Pi.single_eq_of_ne hne]
      change j.val = 0
      omega

private theorem eliminate_orderTwo_high (s : BoxShape) (hs : BoxOK s)
    (Q : DifferentialPolynomial K 2) (hQ : OrderTwoHigh s Q) :
    ∃ Q₁ : DifferentialPolynomial K 1, OrderOneHigh s Q₁ ∧
      ∀ f : Polynomial K, differentialSpecialization Q f = 0 → ¬ RegularRoot Q f →
        differentialSpecialization Q₁ f = 0 := by
  classical
  obtain ⟨hq, hb, hj, hc⟩ := hQ
  dsimp [boxToSource] at hb hj hc
  let _ : StrongNormalizationMonoid (DifferentialPolynomial K 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := UniqueFactorizationMonoid.normalizedFactors Q
  let T := A.toFinset
  let c (G : DifferentialPolynomial K 2) := jetDegree G (Fin.last 2)
  let Q₁ : DifferentialPolynomial K 1 := ∏ G ∈ T, CJ0_5.eliminate G
  have hmem (G) (hG : G ∈ T) : G ∈ A := Multiset.mem_toFinset.mp hG
  have hirr (G) (hG : G ∈ T) : Irreducible G :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor G (hmem G hG)
  have hdvd : (∏ G ∈ T, G) ∣ Q :=
    (Multiset.toFinset_prod_dvd_prod A).trans
      (UniqueFactorizationMonoid.prod_normalizedFactors hq).dvd
  have hcSum : ∑ G ∈ T, c G ≤ s.C := by
    let w : JetVariable 2 → ℕ := Pi.single (some (Fin.last 2)) 1
    have hh := sum_weightedTotalDegree_le_of_prod_dvd w T id hq hdvd
    exact (by simpa only [w, id_eq, weightedTotalDegree_piSingle, jetDegree, c] using hh :
      (∑ G ∈ T, c G) ≤ jetDegree Q (Fin.last 2)).trans hc
  have h2 : 2 ≤ s.B := by have := hs.top_pos; have := hs.index_top; have := hs.total_index; omega
  have hC : s.C < p := calc
    s.C ≤ s.B := by have := hs.index_top; have := hs.total_index; omega
    _ = s.B * 1 := (Nat.mul_one _).symm
    _ ≤ s.B * (s.B - 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ max NHigh (s.B * (s.B - 1)) := le_max_right _ _
    _ < p := hs.characteristic
  have he (G) (hG : G ∈ T) : CJ0_5.eliminate G ≠ 0 :=
    eliminate_ne_zero_high (hirr G hG)
      (((Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) hG).trans hcSum).trans_lt hC)
  have hweight (a B : ℕ) (w : JetVariable 1 → ℕ)
      (hB : a * s.C ≤ B) (hQw : Q.weightedTotalDegree (CJ0_5.inputWeight a w) ≤ B) :
      Q₁.weightedTotalDegree w ≤ max B ((2 * s.C - 1) * B - a * s.C ^ 2) := by
    rw [show Q₁ = ∏ G ∈ T, CJ0_5.eliminate G from rfl, weightedTotalDegree_prod w T _ he]
    apply CJ0_5.aggregate T (fun G => G.weightedTotalDegree (CJ0_5.inputWeight a w)) c
      (fun G => (CJ0_5.eliminate G).weightedTotalDegree w) B a s.C
      ((sum_weightedTotalDegree_le_of_prod_dvd _ T id hq hdvd).trans hQw) hcSum hB
    · exact fun G _ => (CJ0_5.eliminate_weight a w G).1
    · exact fun G _ => (CJ0_5.eliminate_weight a w G).2.1
    · exact fun G _ => (CJ0_5.eliminate_weight a w G).2.2
  refine ⟨Q₁, ⟨Finset.prod_ne_zero_iff.mpr he, ?_, ?_⟩, ?_⟩
  · simpa only [jetTotalDegree, OrderOneHigh, CJ0.H, boxToSource, one_mul] using
      hweight 1 s.B jetDegreeWeight (by have := hs.index_top; have := hs.total_index; omega)
        (by simpa only [input_total_high, jetTotalDegree] using hb)
  · have hh := hweight 2 s.J CJ0.indexWeight (by have := hs.index_top; omega)
      (by rwa [input_index_high])
    simpa only [output_index_high, weightedTotalDegree_piSingle, jetDegree, OrderOneHigh, CJ0.I₁,
      boxToSource] using hh
  · intro f hf hsing
    let ψ := (differentialSpecializationHom (d := 2) f).toRingHom
    change ψ Q = 0 at hf
    have hz := map_dvd ψ (UniqueFactorizationMonoid.prod_normalizedFactors hq).symm.dvd
    change ψ Q ∣ ψ A.prod at hz
    rw [hf, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨G, hG, hg⟩ := hz
    have hgT : G ∈ T := Multiset.mem_toFinset.mpr hG
    have hsep : differentialSpecialization (separant G (Fin.last 2)) f = 0 := by
      by_contra hne
      exact hsing ⟨G, hirr G hgT, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hG, hg, hne⟩
    have hroot := eliminate_root_high G f hg hsep
    change (differentialSpecializationHom (d := 1) f).toRingHom (∏ G ∈ T, CJ0_5.eliminate G) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero hgT hroot

/-! ### Order-1 Charts at `kHigh = 133,721` -/

private def denominator1High (G : DifferentialPolynomial K 1) : InitialRing 1 :=
  CJ0_6.sep G ^ t1High

private theorem exponent1_sufficient_high : TaylorExponentSufficient 1 kHigh t1High :=
  taylorExponentSufficient_firstOrder_tight NHigh

private def shiftedWeightHigh (z : Geo) (l i : ℕ) : Geo :=
  (l.choose i : Geo) * z ^ (l - i)

private theorem coeff_taylor_sum_high {m : ℕ} (z : Geo) (a : Fin m → Geo) (i : ℕ) :
    (Polynomial.taylor z (∑ l : Fin m, Polynomial.monomial l.val (a l))).coeff i =
      ∑ l : Fin m, shiftedWeightHigh z l.val i * a l := by
  rw [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  unfold shiftedWeightHigh
  ring

private theorem readJetHigh_coeff {P : Polynomial Geo} (hP : P.degree < kHigh) (i : ℕ) :
    readJetHigh (fun j => P.coeff j.val) i = (Polynomial.taylor center P).coeff i := by
  have hnat : P.natDegree < kHigh := natDegree_lt_any (by decide) hP
  have hsum : P = ∑ l : Fin kHigh, Polynomial.monomial l.val (P.coeff l.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.monomial j (P.coeff j))]
    exact P.as_sum_range' _ hnat
  exact (coeff_taylor_sum_high center (fun j : Fin kHigh => P.coeff j.val) i).symm.trans
    (congrArg (fun P : Polynomial Geo => (Polynomial.taylor center P).coeff i) hsum.symm)

private def padded1High (G : DifferentialPolynomial K 1) (l : Fin kHigh) : InitialRing 1 :=
  commonTaylorNumerator center (CJ0_6.centeredEquation G) t1High l.val

private def combine1High {m : ℕ} (P : Fin m → InitialRing 1) (i : ℕ) : InitialRing 1 :=
  ∑ l : Fin m, MvPolynomial.C (shiftedWeightHigh (-center) l.val i) * P l

private def chart1High (G : DifferentialPolynomial K 1) (g : InitialRing 1) : ChartHigh 1 :=
  ⟨g, denominator1High G, fun i => combine1High (padded1High G) i.val⟩

private theorem denominator1High_band (s : BoxShape) (G : DifferentialPolynomial K 1)
    (hT : jetTotalDegree G ≤ HHigh s) (hI : jetDegree G (Fin.last 1) ≤ I1High s) :
    inBand1High s (denominator1High G) := by
  have ht : (CJ0_6.sep G).totalDegree ≤ HHigh s - 1 :=
    (totalDegree_initialJetSeparant_le center (CJ0_6.centeredEquation G)).trans
      (Nat.sub_le_sub_right ((jetTotalDegree_map_le embed G).trans hT) 1)
  have hi : (CJ0_6.sep G).degreeOf (Fin.last 1) ≤ I1High s - 1 := by
    rw [CJ0_6.sep, ← pderiv_last_initialJetEquation]
    exact (MvPolynomial.degreeOf_pderiv_le_sub_one _ _).trans
      (Nat.sub_le_sub_right ((CJ0_6.initial_top G).trans hI) 1)
  have hdt : (denominator1High G).totalDegree ≤ a1High s :=
    (MvPolynomial.totalDegree_pow _ _).trans
      ((Nat.mul_le_mul_left _ ht).trans (Nat.le_add_left _ _))
  refine ⟨hdt, le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans hdt) ?_⟩
  exact (MvPolynomial.degreeOf_pow_le _ _ _).trans
    ((Nat.mul_le_mul_left _ hi).trans (by unfold kHigh; omega))

private theorem padded1High_band (s : BoxShape) (G : DifferentialPolynomial K 1)
    (hT : jetTotalDegree G ≤ HHigh s) (hI : jetDegree G (Fin.last 1) ≤ I1High s) (l : Fin kHigh) :
    inBand1High s (padded1High G l) := by
  have htd : (padded1High G l).totalDegree ≤ a1High s :=
    (totalDegree_commonTaylorNumerator_le center (CJ0_6.centeredEquation G)
      (exponent1_sufficient_high l)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left t1High
        (Nat.sub_le_sub_right ((jetTotalDegree_map_le embed G).trans hT) 1)) 1)
  refine ⟨htd, le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans htd) ?_⟩
  have hm : (CJ0_6.centeredEquation G).degreeOf (some (1 : Fin 2)) ≤ I1High s := by
    rw [show (1 : Fin 2) = Fin.last 1 from rfl]
    apply le_trans _ hI
    simpa only [CJ0_6.centeredEquation, jetDegree, MvPolynomial.degreeOf_def] using
      (Multiset.count_le_of_le (some (Fin.last 1))
        (MvPolynomial.degrees_map_le (p := G) (f := embed)))
  exact (degreeOf_commonTaylorNumerator_firstOrder_le center (CJ0_6.centeredEquation G)
    (I1High s) kHigh t1High exponent1_sufficient_high hm l).trans (by
      have hl := l.isLt
      omega)

private theorem combine1High_band (s : BoxShape) {m : ℕ} (P : Fin m → InitialRing 1)
    (h : ∀ l, inBand1High s (P l)) (i : ℕ) : inBand1High s (combine1High P i) := by
  unfold inBand1High combine1High
  constructor
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro l _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa only [MvPolynomial.totalDegree_C, zero_add] using (h l).1)
  · apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro l _
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by
      simpa only [MvPolynomial.degreeOf_C, zero_add] using (h l).2)

private theorem eval_combine1High {m : ℕ} (u : Fin 2 → Geo) (P : Fin m → InitialRing 1)
    (d : Geo) (hd : d ≠ 0) (a : Fin m → Geo) (h : ∀ l, MvPolynomial.eval u (P l) = d * a l)
    (i : ℕ) : MvPolynomial.eval u (combine1High P i) / d =
      (Polynomial.taylor (-center) (∑ l : Fin m, Polynomial.monomial l.val (a l))).coeff i := by
  rw [coeff_taylor_sum_high, combine1High, map_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_mul, MvPolynomial.eval_C, h]
  field_simp

set_option maxRecDepth 200000 in
private theorem output1High_coeff (G : DifferentialPolynomial K 1) (g : InitialRing 1)
    (u : Fin 2 → Geo) (hu : MvPolynomial.eval u (denominator1High G) ≠ 0) (i : Fin kHigh) :
    (chart1High G g).output u i =
      (rationalTaylorPolynomial center (CJ0_6.centeredEquation G) kHigh u).coeff i.val := by
  have hS : MvPolynomial.aeval u (CJ0_6.sep G) ≠ 0 := by
    intro hz
    apply hu
    change MvPolynomial.eval u (CJ0_6.sep G ^ t1High) = 0
    rw [map_pow, ← MvPolynomial.aeval_eq_eval, hz, zero_pow (by decide : t1High ≠ 0)]
  have he (l : Fin kHigh) : MvPolynomial.eval u (padded1High G l) =
      MvPolynomial.eval u (denominator1High G) *
        rationalTaylorCoefficient center (CJ0_6.centeredEquation G) u l.val := by
    simpa only [padded1High, denominator1High, CJ0_6.sep, map_pow, MvPolynomial.aeval_eq_eval] using
      aeval_commonTaylorNumerator center (CJ0_6.centeredEquation G) u
        (exponent1_sufficient_high l) hS
  simp only [ChartHigh.output, chart1High, rationalTaylorPolynomial,
    Polynomial.centeredCoefficientPrefix]
  exact eval_combine1High (m := kHigh) u (padded1High G) (MvPolynomial.eval u (denominator1High G))
    hu (fun l : Fin kHigh => rationalTaylorCoefficient center (CJ0_6.centeredEquation G) u l.val)
    he i.val

set_option maxRecDepth 200000 in
private theorem chart1High_ok (G : DifferentialPolynomial K 1) {g : InitialRing 1}
    (hg : Irreducible g) (hS : ¬ g ∣ denominator1High G) : ChartOKHigh (chart1High G g) := by
  refine ⟨hg, hS, ?_⟩
  intro u hu j
  have hd : MvPolynomial.eval u (denominator1High G) ≠ 0 := hu.2
  let P := rationalTaylorPolynomial center (CJ0_6.centeredEquation G) kHigh u
  have hout : (chart1High G g).output u = fun i => P.coeff i.val := by
    funext i
    exact output1High_coeff G g u hd i
  have hP : P.degree < kHigh := Polynomial.degree_centeredCoefficientPrefix_lt _ _ _
  rw [hout, readJetHigh_coeff hP]
  have h := congrFun (polynomialJet_rationalTaylorPolynomial center (CJ0_6.centeredEquation G)
    (show 1 < kHigh by decide) u) j
  change Polynomial.hasseCoeffAt center j.val P = u j at h
  rw [Polynomial.hasseCoeffAt_apply, ← Polynomial.taylor_coeff] at h
  exact h

private def centerMapHigh : Polynomial K →+* Geo :=
  (algebraMap FX Geo).comp (algebraMap (Polynomial K) FX)

private theorem centerMapHigh_injective : Function.Injective centerMapHigh :=
  (algebraMap FX Geo).injective.comp (IsFractionRing.injective (Polynomial K) FX)

private theorem eval_mapped_at_center_high (f : Polynomial K) :
    (f.map embed).eval center = centerMapHigh f := by
  rw [Polynomial.eval_map]
  change Polynomial.eval₂RingHom embed center f = centerMapHigh f
  congr 1
  apply Polynomial.ringHom_ext
  · intro a; simp [centerMapHigh, embed]
  · simp [centerMapHigh, center]

private theorem eval_mark_high (G : DifferentialPolynomial K 1) (f : Polynomial K) :
    jetEvaluation (CJ0_6.centeredEquation G) center (CJ0_6.mark f) =
      centerMapHigh (differentialSpecialization G f) := by
  rw [CJ0_6.mark, ← eval_differentialSpecialization, CJ0_6.centeredEquation,
    ← map_differentialSpecialization, eval_mapped_at_center_high]

private theorem sep_mark_high (G : DifferentialPolynomial K 1) (f : Polynomial K)
    (h : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    MvPolynomial.eval (CJ0_6.mark f) (CJ0_6.sep G) ≠ 0 := by
  rw [← MvPolynomial.aeval_eq_eval, CJ0_6.sep, aeval_initialJetSeparant, CJ0_6.centeredEquation,
    ← map_separant]
  exact fun hz => h (centerMapHigh_injective
    ((eval_mark_high _ _).symm.trans (hz.trans (map_zero _).symm)))

private theorem denominator1High_mark (G : DifferentialPolynomial K 1) (f : Polynomial K)
    (h : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    MvPolynomial.eval (CJ0_6.mark f) (denominator1High G) ≠ 0 := by
  rw [denominator1High, map_pow]
  exact pow_ne_zero _ (sep_mark_high G f h)

private theorem chart1High_contains (G : DifferentialPolynomial K 1) (g : InitialRing 1)
    (f : Polynomial K) (hf : f.degree < kHigh) (h : differentialSpecialization G f = 0)
    (hs : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0)
    (hg : MvPolynomial.eval (CJ0_6.mark f) g = 0) :
    coeffPointHigh f ∈ (chart1High G g).imageSet := by
  let _ : CharP Geo p := charP_of_injective_ringHom embed.injective p
  have hpiv : ∀ i : ℕ, 1 < i → i < kHigh → (i.choose 1 : Geo) ≠ 0 := by
    intro i hlo hhi hz
    rw [Nat.choose_one_right] at hz
    have hdiv := (CharP.cast_eq_zero_iff Geo p i).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (hhi.trans (by decide : kHigh < p))) hdiv
  have hsol : differentialSpecialization (CJ0_6.centeredEquation G) (f.map embed) = 0 := by
    rw [CJ0_6.centeredEquation, ← map_differentialSpecialization, h, Polynomial.map_zero]
  have hsep : jetEvaluation (separant (CJ0_6.centeredEquation G) (Fin.last 1)) center
      (CJ0_6.mark f) ≠ 0 := by
    rw [← aeval_initialJetSeparant, MvPolynomial.aeval_eq_eval]
    exact sep_mark_high G f hs
  have hdeg : (f.map embed).degree < kHigh := Polynomial.degree_map_le.trans_lt hf
  have hr := rationalTaylorPolynomial_polynomialJet center (CJ0_6.centeredEquation G)
    (f.map embed) hsol hsep hdeg hpiv
  refine ⟨CJ0_6.mark f, ⟨hg, denominator1High_mark G f hs⟩, ?_⟩
  funext i
  rw [output1High_coeff G g (CJ0_6.mark f) (denominator1High_mark G f hs), CJ0_6.mark, hr,
    Polynomial.coeff_map]
  rfl

private theorem root_of_associated_high {G G' : DifferentialPolynomial K 1} {f : Polynomial K}
    (ha : Associated G G') (hG : differentialSpecialization G f = 0)
    (hS : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    differentialSpecialization G' f = 0 ∧
      differentialSpecialization (separant G' (Fin.last 1)) f ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  let ev := differentialSpecializationHom f (d := 1)
  have hu : ev (u : DifferentialPolynomial K 1) ≠ 0 := (u.isUnit.map ev).ne_zero
  change ev G = 0 at hG
  change ev (separant G (Fin.last 1)) ≠ 0 at hS
  change ev (G * u) = 0 ∧ ev (separant (G * u) (Fin.last 1)) ≠ 0
  refine ⟨by rw [map_mul, hG, zero_mul], ?_⟩
  rw [separant, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hG, zero_mul, add_zero]
  exact mul_ne_zero hS hu

local instance : StrongNormalizationMonoid (InitialRing 1) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

private theorem root_in_factor_high {P : InitialRing 1} (hP : P ≠ 0) (u : Fin 2 → Geo)
    (h : MvPolynomial.eval u P = 0) :
    ∃ g ∈ UniqueFactorizationMonoid.normalizedFactors P, MvPolynomial.eval u g = 0 := by
  have hd := map_dvd (MvPolynomial.eval u)
    (UniqueFactorizationMonoid.prod_normalizedFactors hP).symm.dvd
  rw [h, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  exact hd

private theorem positive_total_high {g : InitialRing 1} (hg : Irreducible g) :
    1 ≤ g.totalDegree := by
  by_contra! h
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.lt_one_iff.mp h)
  have hcoef : g.coeff 0 ≠ 0 := fun hz => hg.ne_zero (by rw [hc, hz, map_zero])
  exact hg.not_isUnit (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr
    ⟨g.coeff 0, isUnit_iff_ne_zero.mpr hcoef, hc⟩)

set_option maxRecDepth 200000 in
private theorem order_one_family_high (s : BoxShape) (_hs : BoxOK s)
    (Q : DifferentialPolynomial K 1) (hQ : OrderOneHigh s Q) :
    ∃ F : FamilyHigh 1, Family1High s F ∧
      ∀ f : Polynomial K, f.degree < kHigh → RegularRoot Q f →
        ∃ i, coeffPointHigh f ∈ (F.chart i).imageSet := by
  classical
  let _ : StrongNormalizationMonoid (DifferentialPolynomial K 1) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
  let B (G : DifferentialPolynomial K 1) :=
    (UniqueFactorizationMonoid.normalizedFactors (CJ0_6.initial G)).toFinset.filter
      fun g => ¬ g ∣ denominator1High G
  let T := A.sigma B
  let n := T.card
  let e : Fin n ≃ ↥T := (Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let entry (i : Fin n) := (e i).val
  let F : FamilyHigh 1 := ⟨n, fun i => chart1High (entry i).1 (entry i).2⟩
  have hmember (i : Fin n) : (entry i).1 ∈ A ∧ (entry i).2 ∈ B (entry i).1 :=
    Finset.mem_sigma.mp (e i).property
  have hG (i : Fin n) : (entry i).1 ∣ Q :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (hmember i).1)
  have hg (i : Fin n) : Irreducible (entry i).2 ∧ ¬ (entry i).2 ∣ denominator1High (entry i).1 := by
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp (hmember i).2
    exact ⟨UniqueFactorizationMonoid.irreducible_of_normalized_factor _
      (Multiset.mem_toFinset.mp hm), hd⟩
  have hQ' : CJ0_6.initial Q ≠ 0 :=
    fun hz => hQ.1 (CJ0_6.initial_injective (hz.trans (map_zero CJ0_6.initial).symm))
  have hd : (∏ a ∈ T, a.2) ∣ CJ0_6.initial Q := by
    have hA : (∏ G ∈ A, G) ∣ Q :=
      (Multiset.toFinset_prod_dvd_prod _).trans
        (UniqueFactorizationMonoid.prod_normalizedFactors hQ.1).dvd
    have hm := map_dvd CJ0_6.initial hA
    rw [map_prod] at hm
    change (∏ a ∈ A.sigma B, a.2) ∣ CJ0_6.initial Q
    rw [Finset.prod_sigma]
    refine (Finset.prod_dvd_prod_of_dvd _ _ (fun G hGA => ?_)).trans hm
    have hne : CJ0_6.initial G ≠ 0 := ne_zero_of_dvd_ne_zero hQ'
      (map_dvd CJ0_6.initial (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
        (Multiset.mem_toFinset.mp hGA)))
    exact (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
      ((Multiset.toFinset_prod_dvd_prod _).trans
        (UniqueFactorizationMonoid.prod_normalizedFactors hne).dvd)
  have heq (d : InitialRing 1 → ℕ) :
      (∑ i : Fin n, d (entry i).2) = ∑ a ∈ T, d a.2 := by
    calc
      _ = ∑ a : ↥T, d a.val.2 := e.sum_comp (fun a : ↥T => d a.val.2)
      _ = _ := Finset.sum_coe_sort T (fun a => d a.2)
  have ht : (∑ i : Fin n, (entry i).2.totalDegree) ≤ HHigh s := by
    rw [heq]
    have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd
      (1 : Fin 2 → ℕ) T (fun a => a.2) hQ' hd
    simp only [MvPolynomial.weightedTotalDegree_one] at h
    exact h.trans ((CJ0_6.initial_total Q).trans hQ.2.1)
  have hi : (∑ i : Fin n, (entry i).2.degreeOf (Fin.last 1)) ≤ I1High s := by
    rw [heq]
    have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd
      (Pi.single (Fin.last 1) 1) T (fun a => a.2) hQ' hd
    simp only [MvPolynomial.weightedTotalDegree_piSingle] at h
    exact h.trans ((CJ0_6.initial_top Q).trans hQ.2.2)
  have hn : n ≤ HHigh s := by
    calc
      n = ∑ _ : Fin n, 1 := by simp
      _ ≤ ∑ i : Fin n, (entry i).2.totalDegree :=
        Finset.sum_le_sum fun i _ => positive_total_high (hg i).1
      _ ≤ HHigh s := ht
  refine ⟨F, ⟨hn, fun i => chart1High_ok _ (hg i).1 (hg i).2, ht, hi, ?_⟩, ?_⟩
  · intro i
    have hT : jetTotalDegree (entry i).1 ≤ HHigh s :=
      (MvPolynomial.weightedTotalDegree_le_of_dvd jetDegreeWeight (hG i) hQ.1).trans hQ.2.1
    have hI : jetDegree (entry i).1 (Fin.last 1) ≤ I1High s := by
      have hb := MvPolynomial.weightedTotalDegree_le_of_dvd
        (Pi.single (some (Fin.last 1)) 1) (hG i) hQ.1
      simp only [MvPolynomial.weightedTotalDegree_piSingle] at hb
      exact hb.trans hQ.2.2
    exact ⟨denominator1High_band s _ hT hI, fun j : Fin kHigh =>
      combine1High_band s (m := kHigh) (padded1High (entry i).1)
        (padded1High_band s _ hT hI) j.val⟩
  · intro f hf hreg
    obtain ⟨G, hGir, hGdvd, hGroot, hGsep⟩ := hreg
    obtain ⟨G', hGA, hGassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hQ.1 hGir hGdvd
    obtain ⟨hroot, hsep⟩ := root_of_associated_high hGassoc hGroot hGsep
    have hne : CJ0_6.initial G' ≠ 0 := ne_zero_of_dvd_ne_zero hQ'
      (map_dvd CJ0_6.initial (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hGA))
    obtain ⟨g, hgM, hgroot⟩ := root_in_factor_high hne (CJ0_6.mark f) (CJ0_6.initial_mark G' f hroot)
    have hgden : ¬ g ∣ denominator1High G' := by
      intro hdvd
      have hm := map_dvd (MvPolynomial.eval (CJ0_6.mark f)) hdvd
      rw [hgroot, zero_dvd_iff] at hm
      exact denominator1High_mark G' f hsep hm
    have ht' : (⟨G', g⟩ : Sigma fun _ : DifferentialPolynomial K 1 => InitialRing 1) ∈ T :=
      Finset.mem_sigma.mpr ⟨Multiset.mem_toFinset.mpr hGA,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hgM, hgden⟩⟩
    let a : ↥T := ⟨⟨G', g⟩, ht'⟩
    refine ⟨e.symm a, ?_⟩
    change coeffPointHigh f ∈ (chart1High (e (e.symm a)).val.1 (e (e.symm a)).val.2).imageSet
    rw [e.apply_symm_apply]
    exact chart1High_contains G' g f hf hroot hsep hgroot

/-! ### Order-1 Image Degrees (`CJ0_7` at `kHigh = 133,721`) -/

private theorem equationIdeal_prime_high {r : ℕ} {T : ChartHigh r} (hT : ChartOKHigh T) :
    (sourceIdealHigh T).IsPrime :=
  (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime

private theorem mem_locus_iff_high {r : ℕ} (T : ChartHigh r) (u : Fin (r + 1) → Geo) :
    u ∈ T.locus ↔ u ∈ zeroLocus Geo (sourceIdealHigh T) ∧ MvPolynomial.aeval u T.denominator ≠ 0 := by
  rw [sourceIdealHigh, zeroLocus_span]
  simp only [ChartHigh.locus, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, aeval_eq_eval]

private theorem locus_ideal_high {r : ℕ} {T : ChartHigh r} (hT : ChartOKHigh T) :
    vanishingIdeal Geo T.locus = sourceIdealHigh T := by
  have hp := equationIdeal_prime_high hT
  ext g
  rw [mem_vanishingIdeal_iff]
  constructor
  · intro hg
    have hmul : T.denominator * g ∈ vanishingIdeal Geo (zeroLocus Geo (sourceIdealHigh T)) := by
      apply mem_vanishingIdeal_iff.mpr
      intro u hu
      rw [map_mul]
      by_cases hd : MvPolynomial.aeval u T.denominator = 0
      · rw [hd, zero_mul]
      · rw [hg u ((mem_locus_iff_high T u).2 ⟨hu, hd⟩), mul_zero]
    rw [vanishingIdeal_zeroLocus_eq_radical, hp.isRadical.radical] at hmul
    exact (hp.mem_or_mem hmul).resolve_left
      (fun hd => hT.nonvanishing (Ideal.mem_span_singleton.mp hd))
  · intro hg u hu
    exact ((mem_locus_iff_high T u).1 hu).1 g hg

private theorem curve_image_high {T : ChartHigh 1} (hT : ChartOKHigh T) {a d : ℕ}
    (ha : 0 < a) (hd : 0 < d)
    (hD : T.denominator ∈ restrictCappedDegree (Fin 2) Geo 1 a d)
    (hN : ∀ j : Fin kHigh, T.numerator j ∈ restrictCappedDegree (Fin 2) Geo 1 a d) :
    T.ideal.IsPrime ∧ (affineHilbertPolynomial T.ideal).natDegree = 1 ∧
      affineDegree T.ideal ≤ (cappedDegreeMixedVolume T.equation.totalDegree
        (T.equation.degreeOf (Fin.last 1)) a d : ℕ) := by
  let E := cappedDegreeExponents (Fin 2) 1 a d
  let φ := monomialMap Geo E
  let P := (sourceIdealHigh T).comap φ
  let A := monomialPoint E '' T.locus
  have hA : P = vanishingIdeal Geo A := by
    ext g
    change φ g ∈ sourceIdealHigh T ↔ g ∈ vanishingIdeal Geo A
    rw [← locus_ideal_high hT, mem_vanishingIdeal_iff, mem_vanishingIdeal_iff]
    constructor
    · rintro h _ ⟨u, hu, rfl⟩
      rw [aeval_monomialPoint]
      exact h u hu
    · intro h u hu
      simpa only [aeval_monomialPoint] using h (monomialPoint E u) ⟨u, hu, rfl⟩
  have hp : P.IsPrime := (equationIdeal_prime_high hT).comap φ.toRingHom
  have hdim : (affineHilbertPolynomial P).natDegree = 1 := by
    have h := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
      φ (monomialMap_cappedDegreeExponents_surjective ha hd) hT.irreducible.ne_zero
      (equationIdeal_prime_high hT).ne_top
    rw [Nat.card_fin] at h
    change (affineHilbertPolynomial P).natDegree + 1 = 2 at h
    omega
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hp hdim
  have hone : 1 ≤ affineDegree P := by
    rw [hdeg]
    exact_mod_cast hδ
  let D := monomialLift T.denominator hD
  let N (j : Fin kHigh) := monomialLift (T.numerator j) (hN j)
  have eval_lift (u : Fin 2 → Geo) (g : InitialRing 1) (hg : g ∈ restrictSupport Geo E) :
      MvPolynomial.eval (monomialPoint E u) (monomialLift g hg) = MvPolynomial.eval u g := by
    simpa only [aeval_eq_eval, monomialMap_monomialLift] using
      aeval_monomialPoint u (monomialLift g hg)
  have eval_D (u : Fin 2 → Geo) :
      MvPolynomial.eval (monomialPoint E u) D = MvPolynomial.eval u T.denominator :=
    eval_lift u T.denominator hD
  have eval_N (u : Fin 2 → Geo) (j : Fin kHigh) :
      MvPolynomial.eval (monomialPoint E u) (N j) = MvPolynomial.eval u (T.numerator j) :=
    eval_lift u (T.numerator j) (hN j)
  have hden (z) (hz : z ∈ A) : MvPolynomial.eval z D ≠ 0 := by
    obtain ⟨u, hu, rfl⟩ := hz
    rw [eval_D]
    exact hu.2
  obtain ⟨Q, hQ, hdQ, hbQ, hcover⟩ :=
    ratio_image_degree A P hA hp hdim hone D N
      (totalDegree_monomialLift_le_one _ _) (fun j => totalDegree_monomialLift_le_one _ _) hden
  have hle : Q ≤ T.ideal := by
    intro g hg
    rw [ChartHigh.ideal, mem_vanishingIdeal_iff]
    rintro _ ⟨u, hu, rfl⟩
    have hz := hcover (monomialPoint E u) ⟨u, hu, rfl⟩ g hg
    change MvPolynomial.aeval
      (fun i => MvPolynomial.eval u (T.numerator i) / MvPolynomial.eval u T.denominator) g = 0
    simpa only [eval_D, eval_N] using hz
  have hlower : 1 ≤ (affineHilbertPolynomial T.ideal).natDegree :=
    (image_geometry_high T hT).2.ge
  have heq : Q = T.ideal := by
    refine le_antisymm hle fun g hg => ?_
    by_contra hn
    have hdrop := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hQ hn le_rfl).1
    have hsub : Q ⊔ Ideal.span {g} ≤ T.ideal :=
      sup_le hle ((Ideal.span_singleton_le_iff_mem T.ideal).mpr hg)
    have h := natDegree_affineHilbertPolynomial_le_of_le hsub
    omega
  subst Q
  refine ⟨hQ, le_antisymm hdQ hlower, hbQ.trans ?_⟩
  exact affineDegree_comap_cappedDegree_span_singleton_le ha hd hT.irreducible.ne_zero
    (K1_13_5_3.mem_capped T.equation le_rfl le_rfl)

private theorem order_one_image_degrees_high (s : BoxShape) (F : FamilyHigh 1)
    (hF : Family1High s F) : ImageDegreesHigh F (R1High s) := by
  have ha : 0 < a1High s := by unfold a1High; omega
  have hk : 1 < kHigh := by decide
  have hpos : 0 < t1High * (I1High s - 1) + kHigh - 1 := by omega
  have hd : 0 < d1High s := by rw [d1High]; exact lt_min ha hpos
  have hda : d1High s ≤ a1High s := min_le_left _ _
  have hlocal (i : Fin F.count) := curve_image_high (hF.chart_ok i) ha hd
    (K1_13_5_3.mem_capped _ (hF.bands i).1.1 (hF.bands i).1.2)
    (fun j => K1_13_5_3.mem_capped _ ((hF.bands i).2 j).1 ((hF.bands i).2 j).2)
  refine ⟨fun i => (hlocal i).1, fun i => (hlocal i).2.1, ?_⟩
  let cap (i : Fin F.count) := cappedDegreeMixedVolume (F.chart i).equation.totalDegree
    ((F.chart i).equation.degreeOf (Fin.last 1)) (a1High s) (d1High s)
  have hsum : ∑ i, cap i ≤ R1High s := by
    simp only [cap, cappedDegreeMixedVolume, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [R1High, Nat.add_sub_assoc (Nat.mul_le_mul_left _ hda), ← Nat.mul_sub_left_distrib]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hF.total) (Nat.mul_le_mul_right _ hF.index)
  calc
    (∑ i, affineDegree (F.chart i).ideal) ≤ ∑ i, (cap i : ℚ) :=
      Finset.sum_le_sum fun i _ => (hlocal i).2.2
    _ = ((∑ i, cap i : ℕ) : ℚ) := by rw [Nat.cast_sum]
    _ ≤ (R1High s : ℚ) := Nat.cast_le.mpr hsum

/-! ### Order-1 Singular → Order-0 Exceptional Polynomial (`CJ0_8` without `f.degree < k`) -/

private theorem regularRoot_of_simple_high (Q : DifferentialPolynomial K 1) (f : Polynomial K) :
    differentialSpecialization Q f = 0 →
    differentialSpecialization (separant Q (Fin.last 1)) f ≠ 0 →
    RegularRoot Q f := by
  let φ := differentialSpecializationHom (d := 1) f
  induction Q using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    intro _ hsep
    change φ (pderiv (some (Fin.last 1)) 0) ≠ 0 at hsep
    exact (hsep (by simp only [map_zero])).elim
  | unit u hu =>
    intro hroot _
    change φ u = 0 at hroot
    exact ((hu.map φ.toRingHom).ne_zero hroot).elim
  | mul a i _ hi ih =>
    intro hroot hsep
    change φ (i * a) = 0 at hroot
    change φ (pderiv (some (Fin.last 1)) (i * a)) ≠ 0 at hsep
    rw [map_mul, mul_eq_zero] at hroot
    rw [pderiv_mul, map_add, map_mul, map_mul] at hsep
    rcases hroot with h_i | h_a
    · have hiSep : φ (pderiv (some (Fin.last 1)) i) ≠ 0 := by
        intro hz
        exact hsep (by rw [hz, h_i, zero_mul, zero_mul, add_zero])
      exact ⟨i, hi, dvd_mul_right i a, h_i, hiSep⟩
    · have haSep : φ (pderiv (some (Fin.last 1)) a) ≠ 0 := by
        intro hz
        exact hsep (by rw [hz, h_a, mul_zero, mul_zero, add_zero])
      obtain ⟨g, hg, hdvd, hzero, hnonzero⟩ := ih h_a haSep
      exact ⟨g, hg, hdvd.trans (dvd_mul_left a i), hzero, hnonzero⟩

private theorem height_bounds_high {s : BoxShape} (hs : BoxOK s) :
    2 ≤ HHigh s ∧ HHigh s < p := by
  have hB : 2 ≤ s.B := by have := hs.top_pos; have := hs.index_top; have := hs.total_index; omega
  have hC : 2 * s.C - 1 ≤ s.B - 1 := by have := hs.index_top; have := hs.total_index; omega
  have hBprod : s.B ≤ s.B * (s.B - 1) := by
    calc
      s.B = s.B * 1 := (Nat.mul_one _).symm
      _ ≤ s.B * (s.B - 1) := Nat.mul_le_mul_left _ (by omega)
  have hc := (le_max_right NHigh (s.B * (s.B - 1))).trans_lt hs.characteristic
  have hmax : HHigh s ≤ s.B * (s.B - 1) := by
    unfold HHigh
    apply max_le hBprod
    exact (Nat.sub_le _ _).trans
      ((Nat.mul_le_mul_right s.B hC).trans_eq (Nat.mul_comm _ _))
  exact ⟨hB.trans (le_max_left _ _), hmax.trans_lt hc⟩

private theorem exceptional_orderOne_high (s : BoxShape) (hs : BoxOK s)
    (Q : DifferentialPolynomial K 1) (hQ : OrderOneHigh s Q) :
    ∃ G : Polynomial (Polynomial K), G ≠ 0 ∧ G.natDegree ≤ HHigh s * (HHigh s - 1) ∧
      ∀ f : Polynomial K, differentialSpecialization Q f = 0 → ¬ RegularRoot Q f →
        G.eval f = 0 := by
  classical
  obtain ⟨hQ, hweight, _⟩ := hQ
  have hweight' : jetTotalDegree Q ≤ HHigh s := hweight
  obtain ⟨hH, hHp⟩ := height_bounds_high hs
  suffices ∃ R : DifferentialPolynomial K 0, R ≠ 0 ∧ jetTotalDegree R ≤ HHigh s * (HHigh s - 1) ∧
      ∀ f : Polynomial K, differentialSpecialization Q f = 0 → ¬ RegularRoot Q f →
        differentialSpecialization R f = 0 by
    obtain ⟨R, hR, hRdeg, hRroot⟩ := this
    refine ⟨orderZeroAsPolynomial R, ?_, ?_, ?_⟩
    · intro hz
      apply hR
      apply Sol1.C57.orderZeroAsPolynomial_injective
      simpa only [orderZeroAsPolynomial, map_zero, Polynomial.map_zero] using hz
    · exact (Sol1.C57.orderZeroAsPolynomial_degree R).trans_le hRdeg
    · intro f hroot hnreg
      exact (orderZeroAsPolynomial_eval R f).trans (hRroot f hroot hnreg)
  by_cases hb : jetDegree (Sol1.C57.regularPart 0 Q) (Fin.last 1) = 0
  · have hGone := Sol1.C57.regular_eq_one_of_degree_zero 0 Q hb
    have hsplit := (Sol1.C57.split_weight 0 Q).trans hweight'
    have hlow : jetTotalDegree (Sol1.C57.lowerPart 0 Q) ≤ HHigh s := by omega
    have hbudget : HHigh s ≤ HHigh s * (HHigh s - 1) :=
      (Nat.mul_one _).symm.le.trans (Nat.mul_le_mul_left _ (by omega))
    refine ⟨Sol1.C57.lowerPart 0 Q, Sol1.C57.lower_ne_zero 0 Q, hlow.trans hbudget, ?_⟩
    intro f hroot _
    rcases Sol1.C57.root_split 0 Q hQ f hroot with hc | hr
    · exact hc
    · rw [hGone] at hr
      exact (one_ne_zero (by simpa only [differentialSpecialization, map_one] using hr)).elim
  · have hbpos : 0 < jetDegree (Sol1.C57.regularPart 0 Q) (Fin.last 1) := Nat.pos_of_ne_zero hb
    have hchar : ringChar K = 0 ∨ jetDegree Q (Fin.last 1) < ringChar K := by
      right
      rw [ringChar.eq K p]
      exact (jetDegree_le_total Q (Fin.last 1)).trans_lt (hweight'.trans_lt hHp)
    refine ⟨Sol1.C57.exceptionalEquation 0 Q, Sol1.C57.exceptional_ne_zero 0 Q hchar,
      Sol1.C57.exceptional_weight_sharp 0 Q (HHigh s) hweight'
        (hbpos.trans_le (jetDegree_le_total (Sol1.C57.regularPart 0 Q) (Fin.last 1))), ?_⟩
    intro f hroot hnreg
    rcases Sol1.C57.root_regular_or_exceptional 0 Q hQ f hroot hbpos with hreg | hex
    · have hdvd : Sol1.C57.regularPart 0 Q ∣ Q := by
        obtain ⟨R, hR⟩ := radicalPrimPart_dvd_self none (Sol1.C57.topReindex 0 Q)
        refine ⟨(Sol1.C57.topReindex 0).symm R, ?_⟩
        simpa [Sol1.C57.regularPart] using congrArg (Sol1.C57.topReindex 0).symm hR
      obtain ⟨g, hg, hgdvd, hzero, hsep⟩ :=
        regularRoot_of_simple_high (Sol1.C57.regularPart 0 Q) f hreg.1 hreg.2
      exact (hnreg ⟨g, hg, hgdvd.trans hdvd, hzero, hsep⟩).elim
    · exact hex

/-! ## Section 6: Incidence, Regular Factor Pricing, and Main Theorem at `kHigh = 133,721` -/

private def commonSitesHigh (w : Node → K) (T : Finset (Polynomial K)) : Finset Node :=
  univ.filter fun i => ∀ f ∈ T, f.eval (node i) = w i

private theorem mem_commonSitesHigh {w : Node → K} {T : Finset (Polynomial K)} {i : Node} :
    i ∈ commonSitesHigh w T ↔ ∀ f ∈ T, f.eval (node i) = w i := by
  simp [commonSitesHigh]

private theorem commonSitesHigh_card_le {A w} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w) (hsize : 1 < T.card) :
    (commonSitesHigh w T).card ≤ NHigh := by
  obtain ⟨f, hf, g, hg, hfg⟩ := one_lt_card.mp hsize
  have hdeg {P : Polynomial K} (hP : P ∈ T) : P.natDegree ≤ NHigh := by
    by_cases hz : P = 0
    · simp [hz, NHigh]
    · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt hz).2 (hT hP).1)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node node.injective (f - g)
    (sub_ne_zero.mpr hfg) _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (hdeg hf) (hdeg hg)))
  intro i hi
  change (f - g).eval (node i) = 0
  rw [Polynomial.eval_sub, mem_commonSitesHigh.mp hi f hf, mem_commonSitesHigh.mp hi g hg, sub_self]

private theorem firstMoment_high {A w} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w) (_hS : (commonSitesHigh w T).card ≤ A)
    (cap : ℚ) (hcap : ∀ i ∉ commonSitesHigh w T,
      ((T.filter fun f => f.eval (node i) = w i).card : ℚ) ≤ cap) :
    ((A - (commonSitesHigh w T).card : ℕ) : ℚ) * T.card ≤
      ((nHigh - (commonSitesHigh w T).card : ℕ) : ℚ) * cap := by
  classical
  let S := commonSitesHigh w T
  let candidates := (univ : Finset Node) \ S
  let hits := fun f : Polynomial K => univ.filter fun i : Node => f.eval (node i) = w i
  let occ := fun i : Node => (T.filter fun f => f.eval (node i) = w i).card
  have hcard : candidates.card = nHigh - S.card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ,
      ProximityPrize.Benchmark.IRSProfile.card_index]
  have hnew (f : Polynomial K) (hf : f ∈ T) : A - S.card ≤ (hits f \ S).card := by
    have hsub : S ⊆ hits f := fun i hi => mem_filter.mpr ⟨mem_univ _, mem_commonSitesHigh.mp hi f hf⟩
    exact (Nat.sub_le_sub_right (hT hf).2 _).trans_eq (card_sdiff_of_subset hsub).symm
  have hsum : ∑ i ∈ candidates, occ i = ∑ f ∈ T, (hits f \ S).card := by
    simp only [occ, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun f _ => ?_
    rw [sum_boole, Nat.cast_id]
    have eqSet : (candidates.filter fun i => f.eval (node i) = w i) = hits f \ S := by
      ext i
      simp [candidates, hits, and_comm]
    rw [eqSet]
  have lower : T.card * (A - S.card) ≤ ∑ i ∈ candidates, occ i := by
    rw [hsum]
    calc
      _ = ∑ f ∈ T, (A - S.card) := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := sum_le_sum hnew
  have hlower : (T.card : ℚ) * (A - S.card : ℕ) ≤ ∑ i ∈ candidates, (occ i : ℚ) := by
    exact_mod_cast lower
  calc
    _ = (T.card : ℚ) * (A - S.card : ℕ) := mul_comm _ _
    _ ≤ _ := hlower
    _ ≤ ∑ i ∈ candidates, cap := sum_le_sum fun i hi => hcap i (mem_sdiff.mp hi).2
    _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]

private theorem factorPrice_high
    {A w s} (hA : AgreementOKHigh A) (hA₅ : kHigh + 5 ≤ A) (hs : BoxOK s)
    {G : CJ0_3.Equation} (hG : OrderTwoHigh s G)
    {E : InitialRing 2} (hE : Irreducible E) (hEdvd : E ∣ CJ0_3.initial G)
    (hreg : ¬ E ∣ CJ0_3.initialSep G) (V : Finset (Polynomial K))
    (hV : (V : Set (Polynomial K)) ⊆ closeHigh A w)
    (hroots : ∀ f ∈ V, differentialSpecialization G f = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) E = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0) :
    (V.card : ℚ) ≤ baseFactor A * slicePriceHigh A s kHigh E.totalDegree
      (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) + 1 := by
  classical
  by_cases hv : 1 < V.card
  · let S := commonSitesHigh w V
    obtain ⟨S', hsubset, hcard⟩ := exists_subset_card_eq (min_le_left S.card (kHigh - 3))
    have hshort : S'.card + 3 ≤ kHigh := by
      rw [hcard]; have := min_le_right S.card (kHigh - 3); unfold kHigh at *; omega
    have hL : kHigh - S'.card = shortLength S.card := by
      rw [hcard]; unfold shortLength kHigh; omega
    obtain ⟨T, hT, heq, hband, hcovers⟩ :=
      shortenChart_high s hs G hG E hE hEdvd hreg S' hshort w
    rw [hL] at hband
    have hcov (f : Polynomial K) (hf : f ∈ V) : coeffPointHigh f ∈ T.imageSet := by
      obtain ⟨h₁, h₂, h₃⟩ := hroots f hf
      exact hcovers f (hV hf).1 h₁ h₂ h₃ (fun i hi => mem_commonSitesHigh.mp (hsubset hi) f hf)
    have hc : S.card ≤ NHigh := commonSitesHigh_card_le hV hv
    have hS : S.card < A := hc.trans_lt hA.gt_degree
    have hd : (0 : ℚ) < gapHigh A := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hA.gt_degree)
    have hdegree := volumeDegree_high s hs (shortLength S.card) (le_max_left ..) T hT hband
    rw [heq] at hdegree
    let price := slicePriceHigh A s (shortLength S.card) E.totalDegree
      (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2))
    have hprice (i : Node) (hi : i ∉ S) :
        ((V.filter fun f => f.eval (node i) = w i).card : ℚ) ≤ price := by
      have hmiss : ∃ f ∈ V, f.eval (node i) ≠ w i := by
        simpa only [S, mem_commonSitesHigh, not_forall, exists_prop] using hi
      have cut := cutCap_high T hT hA hV hcov i hmiss
        (totalCap s (shortLength S.card)) hband.denominator.1 (fun j => (hband.numerator j).1)
      rw [heq, Nat.cast_mul] at cut
      have price_mul : (gapHigh A : ℚ) * price =
          (errorsHigh A : ℚ) * bandVolumeHigh s (shortLength S.card) E.totalDegree
            (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) +
          (gapHigh A : ℚ) * ((totalCap s (shortLength S.card) : ℚ) * E.totalDegree) := by
        dsimp only [price, slicePriceHigh, curveFactor]
        rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd.ne']
      apply le_of_mul_le_mul_left _ hd
      rw [price_mul]
      exact cut.trans
        (add_le_add (mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg (errorsHigh A))) le_rfl)
    have hh := firstMoment_high hV hS.le price hprice
    have hu : (0 : ℚ) < (A - S.card : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hS)
    have hpart : (V.card : ℚ) ≤ incidenceFactor A S.card * price := by
      rw [incidenceFactor, div_mul_eq_mul_div, le_div_iff₀ hu, mul_comm (V.card : ℚ)]
      exact hh
    exact hpart.trans ((weighted_price_high A S.card s hs hA₅ hA.lt_length.le hc ..).trans
      (le_add_of_nonneg_right zero_le_one))
  · have hc : (V.card : ℚ) ≤ 1 := by exact_mod_cast (show V.card ≤ 1 by omega)
    have hp : 0 ≤ baseFactor A * slicePriceHigh A s kHigh E.totalDegree
        (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) := by
      obtain ⟨ht, hi, hz⟩ := volume_nonneg_high s hs kHigh (by decide)
      have hbf : 0 ≤ baseFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hcf : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      unfold slicePriceHigh bandVolumeHigh
      positivity
    exact hc.trans (le_add_of_nonneg_left hp)

private theorem regularPrice_high
    {A w s Q} (hA : AgreementOKHigh A) (hA₅ : kHigh + 5 ≤ A) (hs : BoxOK s)
    (hQ : OrderTwoHigh s Q) (T : Finset (Polynomial K))
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w) (hreg : ∀ f ∈ T, RegularRoot Q f) :
    (T.card : ℚ) ≤ surfacePriceHigh A s + s.B := by
  classical
  obtain ⟨F⟩ := CJ0_3_1.proof Q hQ.1
  let root (i : Fin F.count) (f : Polynomial K) :=
    differentialSpecialization (F.source i) f = 0 ∧
    MvPolynomial.eval (CJ0_3.nativeJet f) (F.equation i) = 0 ∧
    MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep (F.source i)) ≠ 0
  let part (i : Fin F.count) := T.filter (root i)
  have hc : T.card ≤ ∑ i, (part i).card := by
    apply (card_le_card (t := univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i, hi⟩ := F.covers f (hreg f hf)
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hf, hi⟩⟩
  let b (i : Fin F.count) := (F.equation i).totalDegree
  let j (i : Fin F.count) := (F.equation i).weightedTotalDegree Fin.val
  let c (i : Fin F.count) := (F.equation i).degreeOf (Fin.last 2)
  have hp (i : Fin F.count) : ((part i).card : ℚ) ≤
      baseFactor A * slicePriceHigh A s kHigh (b i) (j i) (c i) + 1 :=
    factorPrice_high hA hA₅ hs (CJ0_3.orderTwo_of_dvd hQ (F.source_dvd i))
      (F.irreducible i) (F.component i) (F.regular i) (part i)
      (fun _ hf => hT (mem_filter.mp hf).1) (fun _ hf => (mem_filter.mp hf).2)
  obtain ⟨hb, hj, ht⟩ := CJ0_3.factor_weights hQ F
  have hn : F.count ≤ s.B := (CJ0_3.factor_count F).trans hb
  have hbq : (∑ i, (b i : ℚ)) ≤ s.B := by exact_mod_cast hb
  have hjq : (∑ i, (j i : ℚ)) ≤ s.J := by exact_mod_cast hj
  have hcq : (∑ i, (c i : ℚ)) ≤ s.C := by exact_mod_cast ht
  obtain ⟨hu, hv, hw⟩ := volume_nonneg_high s hs kHigh (by decide)
  have hsum : (∑ i, bandVolumeHigh s kHigh (b i) (j i) (c i)) ≤ R2High s := by
    rw [← volume_full_high s hs]
    simp only [bandVolumeHigh, sum_add_distrib, ← mul_sum]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbq hu)
      (mul_le_mul_of_nonneg_left hjq hv)) (mul_le_mul_of_nonneg_left hcq hw)
  have hprice : (∑ i, slicePriceHigh A s kHigh (b i) (j i) (c i)) ≤
      curveFactor A * R2High s + (s.B : ℚ) * totalCap s kHigh := by
    simp only [slicePriceHigh, sum_add_distrib, ← mul_sum]
    rw [mul_comm (s.B : ℚ)]
    exact add_le_add (mul_le_mul_of_nonneg_left hsum
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (mul_le_mul_of_nonneg_left hbq (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ i, ((part i).card : ℚ) := by exact_mod_cast hc
    _ ≤ ∑ i, (baseFactor A * slicePriceHigh A s kHigh (b i) (j i) (c i) + 1) :=
      sum_le_sum fun i _ => hp i
    _ = baseFactor A * (∑ i, slicePriceHigh A s kHigh (b i) (j i) (c i)) + F.count := by
      simp only [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul, mul_one, card_univ,
        Fintype.card_fin]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hprice
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Nat.cast_le.mpr hn)

/-- **Main Case-B Order-Two Counting Theorem at `kHigh = 133,721`:**
Any finite set `T` of polynomials of degree `< 133,721` (`≤ 131,071 + 2,649`) agreeing with a
word `w` on at least `A` positions and annihilated by a nonzero order-2 differential polynomial `Q`
of box shape `s = (B, J, C)` has cardinality at most `tariffHigh A s`. -/
theorem order_two_card_le_high133721
    {A : ℕ} {w : Node → K} {s : BoxShape} {Q : DifferentialPolynomial K 2}
    (hA : AgreementOKHigh A) (hA₅ : kHigh + 5 ≤ A) (hs : BoxOK s)
    (hQ : OrderTwoHigh s Q)
    (T : Finset (Polynomial K)) (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w)
    (hroots : ∀ f ∈ T, differentialSpecialization Q f = 0) :
    T.card ≤ tariffHigh A s := by
  classical
  obtain ⟨Q₁, hQ₁, hremain₁⟩ := eliminate_orderTwo_high s hs Q hQ
  obtain ⟨F₁, hF₁, hcover₁⟩ := order_one_family_high s hs Q₁ hQ₁
  obtain ⟨G, hG, hGdeg, hordinary⟩ := exceptional_orderOne_high s hs Q₁ hQ₁
  let T₂ := T.filter (RegularRoot Q)
  let rest := T.filter fun f => ¬ RegularRoot Q f
  let T₁ := rest.filter (RegularRoot Q₁)
  let T₀ := rest.filter fun f => ¬ RegularRoot Q₁ f
  have h₂ (f) (hf : f ∈ T₂) := hT (mem_filter.mp hf).1
  have hrest (f) (hf : f ∈ rest) := hT (mem_filter.mp hf).1
  have h₁ (f) (hf : f ∈ T₁) := hrest f (mem_filter.mp hf).1
  have p₂ := regularPrice_high hA hA₅ hs hQ T₂
    (fun f hf => h₂ f hf) (fun _ hf => (mem_filter.mp hf).2)
  have hprice₁ := family1_capacity_high (fun f hf => h₁ f hf) hA F₁
    (order_one_image_degrees_high s F₁ hF₁)
    (fun f hf => hcover₁ f (h₁ f hf).1 (mem_filter.mp hf).2)
  have hd : (0 : ℚ) < gapHigh A := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hA.gt_degree)
  have p₁ : (T₁.card : ℚ) ≤ curveFactor A * R1High s + HHigh s := by
    apply le_of_mul_le_mul_left _ hd
    unfold curveFactor
    rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd.ne']
    have hcount : (F₁.count : ℚ) ≤ HHigh s := by exact_mod_cast hF₁.count
    exact hprice₁.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hd.le))
  have p₀ : T₀.card ≤ HHigh s * (HHigh s - 1) := by
    refine (Polynomial.card_le_degree_of_subset_roots (p := G) ?_).trans hGdeg
    intro f hf
    obtain ⟨hr', hsing₁⟩ := mem_filter.mp (show f ∈ T₀ from hf)
    have hf' := (mem_filter.mp hr').1
    exact (Polynomial.mem_roots hG).mpr
      (hordinary f (hremain₁ f (hroots f hf') (mem_filter.mp hr').2) hsing₁)
  have htail : ∀ h : ℕ, h + h * (h - 1) = h ^ 2 := by
    intro h
    cases h with
    | zero => rfl
    | succ h => rw [Nat.succ_sub_one]; ring
  have hp₀ : (HHigh s : ℚ) + T₀.card ≤ (HHigh s : ℚ) ^ 2 := by
    exact_mod_cast (Nat.add_le_add_left p₀ (HHigh s)).trans_eq (htail (HHigh s))
  have hpart₂ : T₂.card + rest.card = T.card := card_filter_add_card_filter_not ..
  have hpart₁ : T₁.card + T₀.card = rest.card := card_filter_add_card_filter_not ..
  have hp : (T.card : ℚ) ≤ totalPriceHigh A s := by
    rw [show T.card = T₂.card + T₁.card + T₀.card by omega, Nat.cast_add, Nat.cast_add]
    unfold totalPriceHigh
    linarith only [p₂, p₁, hp₀]
  exact Nat.cast_le.mp (hp.trans (Nat.le_ceil _))

/-- Concrete Case-B cardinality caps for all 6 small Rescue rectangles at `69.63` (`A = 179,798`). -/
theorem caseB_six_rects_card_le_6963 (w : Node → K) (T : Finset (Polynomial K))
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh 179798 w) :
    (∀ Q, OrderTwoHigh box_r0 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 2_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r1 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 640_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r2a Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 44_890_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r3a_j2 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 36_860_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r3a_j4 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 7_870_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r3a_j7 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 9_380_000_000_000_000) := by
  obtain ⟨hb0, hb1, hb2a, hb32, hb34, hb37⟩ := all_six_boxes_ok
  obtain ⟨ht0, ht1, ht2a, ht32, ht34, ht37⟩ := caseB_tariffs_6963
  have hA₅ : kHigh + 5 ≤ 179798 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb0 hQ T hT hr).trans ht0
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb1 hQ T hT hr).trans ht1
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb2a hQ T hT hr).trans ht2a
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb32 hQ T hT hr).trans ht32
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb34 hQ T hT hr).trans ht34
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb37 hQ T hT hr).trans ht37

end

end CJ0High133721

#print axioms CJ0High133721.shortenChart_high
#print axioms CJ0High133721.cutCap_high
#print axioms CJ0High133721.order_two_card_le_high133721
#print axioms CJ0High133721.caseB_six_rects_card_le_6963

end Merged_CJ0High133721Main

-- merged module TwoJetCaseBResultant
section Merged_TwoJetCaseBResultant

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

/-!
# Case-B Sylvester Resultant Box & 6-Small-Rect Consumer (`TwoJetCaseBResultant`)

Connects L4 `TwoJetRescueBridge.caseB_cj0_box_exact` directly to L4
`CJ0High133721Main.caseB_six_rects_card_le_6963`:

1. `sylvester_weightedTotalDegree_le`: for any weight function `w : JetVariable 2 → ℕ` and any
   polynomials `G G₁ : Polynomial (DifferentialPolynomial K 2)` whose coefficients have
   `w`-weighted degree `≤ B` and `≤ D`, their Sylvester resultant `G.resultant G₁ m n` has
   `w`-weighted degree `≤ n * B + m * D`.
2. `resultant_orderTwoHigh`: if `G` (the 1-jet prime) has `(Y₀, Y₁, Y₂)`-degree `≤ j`,
   `indexWeight ≤ 1`, `Y₂`-degree `= 0`, and `G₁` (its prolongation `G^(1)`) has total degree
   `≤ j + 1`, `indexWeight ≤ 2`, `Y₂`-degree `≤ 1`, with `m, n ≤ u`, then any nonzero
   `Q = G.resultant G₁ m n` satisfies `OrderTwoHigh box Q` whenever
   `(2 * j + 1) * u ≤ box.B`, `3 * u ≤ box.J`, `u ≤ box.C`.
3. `resultant_vanishes_on_common_root`: if `G` and `G₁` share a root `z₀` after specializing at `f`,
   then `differentialSpecialization (G.resultant G₁ m n) f = 0`.
4. `caseB_small_rects_card_le_6963`: end-to-end cardinality cap (`≤ 44.89e15`, plus exact per-rect
   caps) for any Case-B pair `(G, G₁)` in any of the 6 small Rescue rectangles at `69.63`
   (`A = 179,798`, `deg < 133,721`).
-/

namespace TwoJetCaseBResultant

noncomputable section

open CJ0 CJ0High133721 TwoJetRescueBridge Polynomial PolynomialDifferential MvPolynomial
open scoped BigOperators

/-- General weighted-degree bound on a Sylvester resultant over `DifferentialPolynomial K 2`. -/
theorem sylvester_weightedTotalDegree_le (w : JetVariable 2 → ℕ)
    (G G₁ : Polynomial (DifferentialPolynomial K 2)) (m n B D : ℕ)
    (hG : ∀ i ≤ m, (G.coeff i).weightedTotalDegree w ≤ B)
    (hG₁ : ∀ i ≤ n, (G₁.coeff i).weightedTotalDegree w ≤ D) :
    (G.resultant G₁ m n).weightedTotalDegree w ≤ n * B + m * D := by
  classical
  let M := Polynomial.sylvester G G₁ m n
  let W : Fin (m + n) → ℕ :=
    Fin.addCases (fun _ : Fin m => D) (fun _ : Fin n => B)
  have hentry (σ : Equiv.Perm (Fin (m + n))) (i : Fin (m + n))
      (hne : M (σ i) i ≠ 0) :
      (M (σ i) i).weightedTotalDegree w ≤ W i := by
    cases i using Fin.addCases with
    | left j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, W] at hne ⊢
      split_ifs at hne ⊢ with h
      · exact hG₁ ((σ (j.castAdd n)).val - j.val) (by have := h.2; omega)
      · exact absurd rfl hne
    | right j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, W] at hne ⊢
      split_ifs at hne ⊢ with h
      · exact hG ((σ (j.natAdd m)).val - j.val) (by have := h.2; omega)
      · exact absurd rfl hne
  have hW : ∑ i, W i = n * B + m * D := by
    simp only [W, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hterm (σ : Equiv.Perm (Fin (m + n))) :
      (∏ i, M (σ i) i).weightedTotalDegree w ≤ n * B + m * D := by
    by_cases hz : ∃ i, M (σ i) i = 0
    · obtain ⟨i, hi⟩ := hz
      have hp : (∏ k, M (σ k) k) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hp, weightedTotalDegree_zero]
      exact Nat.zero_le _
    · simp only [not_exists] at hz
      rw [weightedTotalDegree_prod _ _ _ (fun i _ => hz i)]
      exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hentry σ i (hz i))).trans_eq hW
  change M.det.weightedTotalDegree w ≤ n * B + m * D
  rw [Matrix.det_apply]
  refine AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun σ _ => ?_)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
    exact hterm σ
  · rw [hs, Units.neg_smul, one_smul]
    let P : DifferentialPolynomial K 2 := ∏ i, M (σ i) i
    change (-P).weightedTotalDegree w ≤ n * B + m * D
    have hsup : (-P).weightedTotalDegree w = P.weightedTotalDegree w := by
      simp only [MvPolynomial.weightedTotalDegree, MvPolynomial.support_neg]
    rw [hsup]
    exact hterm σ

/-- Exact `OrderTwoHigh` box certificate for the Sylvester resultant `Res_z(G, G₁)` of a 1-jet
    prime `G` and its prolongation `G₁ = G^(1)`. -/
theorem resultant_orderTwoHigh {j u m n : ℕ} {box : BoxShape}
    (G G₁ : Polynomial (DifferentialPolynomial K 2))
    (hm : m ≤ u) (hn : n ≤ u)
    (hne : G.resultant G₁ m n ≠ 0)
    (hG_tot : ∀ i ≤ m, jetTotalDegree (G.coeff i) ≤ j)
    (hG_idx : ∀ i ≤ m, (G.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 1)
    (hG_top : ∀ i ≤ m, jetDegree (G.coeff i) (Fin.last 2) = 0)
    (hG₁_tot : ∀ i ≤ n, jetTotalDegree (G₁.coeff i) ≤ j + 1)
    (hG₁_idx : ∀ i ≤ n, (G₁.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 2)
    (hG₁_top : ∀ i ≤ n, jetDegree (G₁.coeff i) (Fin.last 2) ≤ 1)
    (hB : (2 * j + 1) * u ≤ box.B) (hJ : 3 * u ≤ box.J) (hC : u ≤ box.C) :
    OrderTwoHigh box (G.resultant G₁ m n) := by
  refine ⟨hne, ?_, ?_, ?_⟩
  · change jetTotalDegree (G.resultant G₁ m n) ≤ box.B
    have h := sylvester_weightedTotalDegree_le jetDegreeWeight G G₁ m n j (j + 1) hG_tot hG₁_tot
    have hmul : n * j + m * (j + 1) ≤ (2 * j + 1) * u := by
      have h1 : n * j ≤ u * j := Nat.mul_le_mul_right j hn
      have h2 : m * (j + 1) ≤ u * (j + 1) := Nat.mul_le_mul_right (j + 1) hm
      have h3 : u * j + u * (j + 1) = (2 * j + 1) * u := by ring
      omega
    exact h.trans (hmul.trans hB)
  · change (G.resultant G₁ m n).weightedTotalDegree CJ0.indexWeight ≤ box.J
    have h := sylvester_weightedTotalDegree_le CJ0.indexWeight G G₁ m n 1 2 hG_idx hG₁_idx
    have hmul : n * 1 + m * 2 ≤ 3 * u := by omega
    exact h.trans (hmul.trans hJ)
  · change jetDegree (G.resultant G₁ m n) (Fin.last 2) ≤ box.C
    let wtop : JetVariable 2 → ℕ := Pi.single (some (Fin.last 2)) 1
    have h := sylvester_weightedTotalDegree_le wtop G G₁ m n 0 1
      (fun i hi => by
        simpa only [wtop, weightedTotalDegree_piSingle, jetDegree] using (hG_top i hi).le)
      (fun i hi => by
        simpa only [wtop, weightedTotalDegree_piSingle, jetDegree] using hG₁_top i hi)
    simp only [wtop, weightedTotalDegree_piSingle, mul_zero, zero_add, mul_one] at h
    exact h.trans (hm.trans hC)

/-- Common root vanishing: if `G` and `G₁` share a seed root `z₀` after specializing at `f`, then
    their Sylvester resultant annihilates `f`. -/
theorem resultant_vanishes_on_common_root
    (G G₁ : Polynomial (DifferentialPolynomial K 2)) (m n : ℕ)
    (hGm : G.natDegree ≤ m) (hG₁n : G₁.natDegree ≤ n) (hsize : m ≠ 0 ∨ n ≠ 0)
    (f z₀ : Polynomial K)
    (hG0 : G.eval₂ (differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0)
    (hG₁0 : G₁.eval₂ (differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0) :
    differentialSpecialization (G.resultant G₁ m n) f = 0 :=
  Sol1.C40Primitives.map_resultant_eq_zero_of_common_root
    (differentialSpecializationHom (d := 2) f).toRingHom G G₁ m n hGm hG₁n hsize z₀ hG0 hG₁0

/-- Exact per-rectangle Case-B budget cap at `69.63` (`A = 179,798`) for the 6 small rectangles. -/
def smallRectCap6963 : RescueRect → ℕ
  | .r0     => 2_000_000_000_000
  | .r1     => 640_000_000_000_000
  | .r2a    => 44_890_000_000_000_000
  | .r3a_j2 => 36_860_000_000_000_000
  | .r3a_j4 => 7_870_000_000_000_000
  | .r3a_j7 => 9_380_000_000_000_000
  | _       => 0

def IsSmallRect : RescueRect → Prop
  | .r0 | .r1 | .r2a | .r3a_j2 | .r3a_j4 | .r3a_j7 => True
  | _ => False

theorem smallRectCap6963_le_max (r : RescueRect) :
    smallRectCap6963 r ≤ 44_890_000_000_000_000 := by
  cases r <;> decide

/-- **End-to-End Case-B Small-Rectangle Rescue Theorem at `69.63` (`A = 179,798`, `deg < 133,721`)**:
    For ANY of the 6 small Rescue rectangles `r ∈ {.r0, .r1, .r2a, .r3a_j2, .r3a_j4, .r3a_j7}` and
    any Case-B pair `(G, G₁)` with `InRect j u r` and nonzero Sylvester resultant
    `G.resultant G₁ m n ≠ 0` (`m, n ≤ u`, `m ≠ 0 ∨ n ≠ 0`), any finite set `T ⊆ closeHigh 179798 w`
    of degree-`< 133,721` polynomials whose marks all admit a common `z₀` root of `(G, G₁)` obeys:
    1. `T.card ≤ smallRectCap6963 r` (exact per-rectangle cap), and
    2. `T.card ≤ 44_890_000_000_000_000` (`44.89e15 < 61.30e15` 4-large-rect Rescue cap). -/
theorem caseB_small_rects_card_le_6963
    {r : RescueRect} (hr : IsSmallRect r) {j u m n : ℕ} (hin : InRect j u r)
    (G G₁ : Polynomial (DifferentialPolynomial K 2))
    (hm : m ≤ u) (hn : n ≤ u) (hGm : G.natDegree ≤ m) (hG₁n : G₁.natDegree ≤ n)
    (hsize : m ≠ 0 ∨ n ≠ 0) (hne : G.resultant G₁ m n ≠ 0)
    (hG_tot : ∀ i ≤ m, jetTotalDegree (G.coeff i) ≤ j)
    (hG_idx : ∀ i ≤ m, (G.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 1)
    (hG_top : ∀ i ≤ m, jetDegree (G.coeff i) (Fin.last 2) = 0)
    (hG₁_tot : ∀ i ≤ n, jetTotalDegree (G₁.coeff i) ≤ j + 1)
    (hG₁_idx : ∀ i ≤ n, (G₁.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 2)
    (hG₁_top : ∀ i ≤ n, jetDegree (G₁.coeff i) (Fin.last 2) ≤ 1)
    (w : Node → K) (T : Finset (Polynomial K))
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh 179798 w)
    (hcommon : ∀ f ∈ T, ∃ z₀ : Polynomial K,
      G.eval₂ (differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0 ∧
      G₁.eval₂ (differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0) :
    T.card ≤ smallRectCap6963 r ∧ T.card ≤ 44_890_000_000_000_000 := by
  have hroots : ∀ f ∈ T, differentialSpecialization (G.resultant G₁ m n) f = 0 := by
    intro f hf
    obtain ⟨z₀, hzG, hzG₁⟩ := hcommon f hf
    exact resultant_vanishes_on_common_root G G₁ m n hGm hG₁n hsize f z₀ hzG hzG₁
  obtain ⟨h0, h1, h2a, h32, h34, h37⟩ := caseB_six_rects_card_le_6963 w T hT
  obtain ⟨b0, b1, b2a, b32, b34, b37⟩ := caseB_cj0_box_exact (j := j) (u := u)
  have hcap : T.card ≤ smallRectCap6963 r := by
    cases r with
    | r0 =>
      obtain ⟨hB, hJ, hC, _⟩ := b0 hin
      exact h0 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r1 =>
      obtain ⟨hB, hJ, hC, _⟩ := b1 hin
      exact h1 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r2a =>
      obtain ⟨hB, hJ, hC, _⟩ := b2a hin
      exact h2a _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r3a_j2 =>
      obtain ⟨hB, hJ, hC, _⟩ := b32 hin
      exact h32 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r3a_j4 =>
      obtain ⟨hB, hJ, hC, _⟩ := b34 hin
      exact h34 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r3a_j7 =>
      obtain ⟨hB, hJ, hC, _⟩ := b37 hin
      exact h37 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r2b => exact hr.elim
    | r3b_j2 => exact hr.elim
    | r3b_j4 => exact hr.elim
    | r3b_j7 => exact hr.elim
  exact ⟨hcap, hcap.trans (smallRectCap6963_le_max r)⟩

end

end TwoJetCaseBResultant

#print axioms TwoJetCaseBResultant.sylvester_weightedTotalDegree_le
#print axioms TwoJetCaseBResultant.resultant_orderTwoHigh
#print axioms TwoJetCaseBResultant.resultant_vanishes_on_common_root
#print axioms TwoJetCaseBResultant.caseB_small_rects_card_le_6963

end Merged_TwoJetCaseBResultant

-- merged module TwoJetCaseADriver
section Merged_TwoJetCaseADriver

set_option Elab.async false
set_option autoImplicit false
set_option maxSynthPendingDepth 24
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

/-!
# 2-Jet Case-A Driver (`TwoJetShift.complete2_cleared` → `TwoJetCaseAKernel`) & Hybrid 6-Rect Rescue (`TwoJetCaseADriver`)

Closes the final algebraic link between L4 `TwoJetShift.complete2_cleared` and L4
`TwoJetCaseAKernel.caseA_avoidance_of_wordVanishes`, and packages both Case A (`det M ≠ 0`) and
Case B (`det M = 0`) for the 6 small Rescue rectangles at `69.63` (`A = 179,798`):

1. **Seed-Derivative Base Ring & Explicit `FieldDerivs (FractionRing BaseRing)`**:
   Proves that `K1_14_1_3.seedCoeff i 1` is an `L`-derivation on `SeedPoly`, lifts it to
   `baseDeriv i` on `BaseRing = SeedPoly[X][Y₀]`, and explicitly constructs
   `fractionRingFieldDerivs : FieldDerivs (FractionRing BaseRing)` via the quotient rule,
   witnessing `BaseDerivCompat` non-vacuously.
2. **Exact Intertwining of `sourceHasse2 i 1` with `liftD`**:
   For any `BaseDerivCompat φ D` and any `(α₁, α₂) : E × E`, proves the exact coefficient identity
     `polyBivar (shift2 α₁ α₂ (embed2 φ (sourceHasse2 i 1 P))) =`
       `liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))`.
3. **Iterated Cleared-Shift Words (`applyClearedWord`)**:
   Uses L4 `TwoJetShift.complete2_cleared` to show that if every `Q ∈ complete2 Crt word s W'`
   (`W' < N`) vanishes at `(α₁, α₂)`, then every `P ∈ complete2 Crt word s W` automatically obeys
   `WordVanishes D α₁ α₂ k (polyBivar (shift2 α₁ α₂ (embed2 φ P)))` whenever
   `W + k * (boundedShiftExp s 1 * h) < N`.
4. **End-to-End Case-A Avoidance Without `hvan` (`caseA_avoidance_from_complete2_cleared`)**:
   Eliminates the `hvan` hypothesis from `TwoJetCaseAKernel.caseA_avoidance_of_lowCoords_surplus`
   via `TwoJetShift.complete2_cleared` and `TwoJetRescueBridge.prolongSubst_bezout`.
5. **Unified Hybrid 6-Small-Rect Rescue Theorem (`small_rect_hybrid_rescue_6963`)**:
   Packages Case A (2-jet prolongation avoidance) and Case B (L4 `TwoJetCaseBResultant`,
   `T.card ≤ smallRectCap6963 r ≤ 44.89e15 < 61.30e15`) across all 6 small Rescue rectangles.
-/

namespace TwoJetCaseADriver

noncomputable section

open Polynomial Finset
open K1 (I)
open K1_14 (L)
open K1_14_1 (SeedPoly PoleData CRTLift)
open K1_14_1_3 (translation seedCoeff mapCoeffs mapCoeffs_coeff sourceX)
open PoleMoment2Jet (Shape2 groupedPoleMoment2 poleCredit2 jetConstant2)
open PoleBound2Jet (Source2 coeffAt2 ambient2 contacted2 complete2)
open TwoJetShift (boundedShiftExp sourceHasse2 cleared2Shift complete2_cleared)
open TwoJetRescueBridge (Jet2 centerEval2 prolongSubst prolongSubst_bezout prolongKernel
  RescueRect InRect)
open TwoJetCaseAKernel (FieldDerivs Bivar liftD bivarAdd bivarSmul applyWord WordVanishes
  jacDet shift1 shift2 polyBivar embed2 lowCoords highCoords
  caseA_avoidance_of_lowCoords_surplus)
open TwoJetCaseBResultant (IsSmallRect smallRectCap6963 caseB_small_rects_card_le_6963)
open scoped BigOperators Polynomial

abbrev BaseRing := Polynomial (Polynomial SeedPoly)

/-! ## 1. Generic Coefficientwise Derivation Lifting on Polynomials -/

def mapDeriv {R : Type*} [CommRing R] (d : R → R) (p : Polynomial R) : Polynomial R :=
  p.sum fun n a => Polynomial.monomial n (d a)

theorem mapDeriv_coeff {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0)
    (p : Polynomial R) (n : ℕ) : (mapDeriv d p).coeff n = d (p.coeff n) := by
  classical
  change (p.sum fun j a => Polynomial.monomial j (d a)).coeff n = d (p.coeff n)
  simp only [Polynomial.sum, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finsupp.single_apply, Finset.sum_ite_eq']
  split
  · rfl
  next h => rw [Polynomial.notMem_support_iff.mp h, h0]

theorem mapDeriv_zero {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0) :
    mapDeriv d (0 : Polynomial R) = 0 := by
  ext n; simp [mapDeriv_coeff h0, h0]

theorem mapDeriv_add {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (p q : Polynomial R) :
    mapDeriv d (p + q) = mapDeriv d p + mapDeriv d q := by
  ext n; simp [mapDeriv_coeff h0, hadd]

theorem mapDeriv_C {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0) (c : R) :
    mapDeriv d (Polynomial.C c) = Polynomial.C (d c) := by
  ext n
  rw [mapDeriv_coeff h0, Polynomial.coeff_C, Polynomial.coeff_C]
  split <;> simp [h0]

theorem mapDeriv_X {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0) (h1 : d 1 = 0) :
    mapDeriv d (Polynomial.X : Polynomial R) = 0 := by
  ext n
  rw [mapDeriv_coeff h0, Polynomial.coeff_X, Polynomial.coeff_zero]
  split <;> simp [h0, h1]

theorem mapDeriv_mul {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (p q : Polynomial R) :
    mapDeriv d (p * q) = mapDeriv d p * q + p * mapDeriv d q := by
  have hd_sum : ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → R),
      d (∑ i ∈ s, f i) = ∑ i ∈ s, d (f i) := by
    intro s f
    classical
    induction s using Finset.induction with
    | empty => simp [h0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  ext n
  rw [mapDeriv_coeff h0, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul,
    Polynomial.coeff_mul, hd_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [hmul, mapDeriv_coeff h0, mapDeriv_coeff h0]

theorem fieldDerivs_d₀_one {E : Type*} [Field E] (D : FieldDerivs E) : D.d₀ 1 = 0 := by
  have h := D.d₀_mul 1 1
  simp only [one_mul, mul_one] at h
  exact add_left_cancel (a := D.d₀ 1) (by rw [add_zero]; exact h.symm)

theorem fieldDerivs_d₁_one {E : Type*} [Field E] (D : FieldDerivs E) : D.d₁ 1 = 0 := by
  have h := D.d₁_mul 1 1
  simp only [one_mul, mul_one] at h
  exact add_left_cancel (a := D.d₁ 1) (by rw [add_zero]; exact h.symm)

/-! ## 2. `seedCoeff i 1`, `baseDeriv`, and Explicit `FieldDerivs (FractionRing BaseRing)` -/

theorem translation_coeff_zero (i : Fin 2) (p : SeedPoly) :
    (translation i p).coeff 0 = p := by
  have h : (Polynomial.evalRingHom 0).comp (translation i).toRingHom = RingHom.id SeedPoly := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [translation]
    · intro j
      by_cases hj : j = i <;> simp [translation, hj]
  have hp := RingHom.congr_fun h p
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.coe_evalRingHom, RingHom.id_apply] at hp
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact hp

theorem seedCoeff_one_mul (i : Fin 2) (p q : SeedPoly) :
    seedCoeff i 1 (p * q) = seedCoeff i 1 p * q + p * seedCoeff i 1 q := by
  change (translation i (p * q)).coeff 1 =
    (translation i p).coeff 1 * q + p * (translation i q).coeff 1
  rw [map_mul, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, translation_coeff_zero]
  ring

theorem seedCoeff_one_C (i : Fin 2) (a : L) :
    seedCoeff i 1 (MvPolynomial.C a) = 0 := by
  change (translation i (MvPolynomial.C a)).coeff 1 = 0
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  change (Polynomial.C (MvPolynomial.C a)).coeff 1 = 0
  simp

def baseDeriv (i : Fin 2) : BaseRing →ₗ[L] BaseRing :=
  mapCoeffs (mapCoeffs (seedCoeff i 1))

theorem baseDeriv_coeff (i : Fin 2) (r : BaseRing) (b a : ℕ) :
    ((baseDeriv i r).coeff b).coeff a = seedCoeff i 1 ((r.coeff b).coeff a) := by
  simp [baseDeriv]

theorem baseDeriv_mul (i : Fin 2) (r₁ r₂ : BaseRing) :
    baseDeriv i (r₁ * r₂) = baseDeriv i r₁ * r₂ + r₁ * baseDeriv i r₂ := by
  have h1 : ∀ p q : Polynomial SeedPoly,
      mapCoeffs (seedCoeff i 1) (p * q) =
        mapCoeffs (seedCoeff i 1) p * q + p * mapCoeffs (seedCoeff i 1) q := by
    intro p q
    have heq : ∀ x : Polynomial SeedPoly, mapCoeffs (seedCoeff i 1) x = mapDeriv (seedCoeff i 1) x := by
      intro x; ext n; rw [mapCoeffs_coeff, mapDeriv_coeff (map_zero _)]
    simp only [heq]
    exact mapDeriv_mul (map_zero _) (map_add _) (seedCoeff_one_mul i) p q
  have heq2 : ∀ x : BaseRing,
      baseDeriv i x = mapDeriv (mapCoeffs (seedCoeff i 1)) x := by
    intro x; ext b; rw [baseDeriv, mapCoeffs_coeff, mapDeriv_coeff (map_zero _)]
  simp only [heq2]
  exact mapDeriv_mul (map_zero _) (map_add _) h1 r₁ r₂

theorem baseDeriv_sourceX (i : Fin 2) (p : Polynomial L) :
    baseDeriv i (Polynomial.C (sourceX p)) = 0 := by
  ext b a
  rw [baseDeriv_coeff]
  simp only [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
  by_cases hb : b = 0
  · subst hb
    simp [sourceX, seedCoeff_one_C]
  · simp [Polynomial.coeff_C, hb]

/-- Quotient-rule extension of any ring derivation `d : R → R` on an integral domain `R`
    to `FractionRing R`. -/
def fracDeriv {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y) :
    FractionRing R → FractionRing R :=
  fun x => Localization.liftOn x
    (fun (a : R) (s : nonZeroDivisors R) =>
      algebraMap R (FractionRing R) (d a * s - a * d s) /
        algebraMap R (FractionRing R) (s * s : R))
    (by
      intro a₁ a₂ s₁ s₂ h
      rw [Localization.r_iff_exists] at h
      obtain ⟨c, hc⟩ := h
      have hc0 : (c : R) ≠ 0 := nonZeroDivisors.ne_zero c.2
      have h1 : a₁ * s₂ = a₂ * s₁ := mul_left_cancel₀ hc0 (by
        have h' : (c : R) * (a₁ * s₂) = (c : R) * (a₂ * s₁) := by
          linear_combination (by simpa [mul_assoc, mul_comm, mul_left_comm] using hc :
            (c : R) * (s₂ * a₁) = (c : R) * (s₁ * a₂))
        exact h')
      have hd : d a₁ * s₂ + a₁ * d s₂ = d a₂ * s₁ + a₂ * d s₁ := by
        have h' := congrArg d h1
        rwa [hmul, hmul] at h'
      have hs1 : algebraMap R (FractionRing R) (s₁ * s₁ : R) ≠ 0 := by
        rw [map_mul]
        exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₁.2)
          (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₁.2)
      have hs2 : algebraMap R (FractionRing R) (s₂ * s₂ : R) ≠ 0 := by
        rw [map_mul]
        exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₂.2)
          (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₂.2)
      rw [div_eq_div_iff hs1 hs2]
      rw [← map_mul, ← map_mul]
      congr 1
      have hcross : (d a₁ * s₁ - a₁ * d s₁) * (s₂ * s₂) - (d a₂ * s₂ - a₂ * d s₂) * (s₁ * s₁) =
          (s₁ * s₂) * ((d a₁ * s₂ + a₁ * d s₂) - (d a₂ * s₁ + a₂ * d s₁)) -
          (d s₁ * s₂ + s₁ * d s₂) * (a₁ * s₂ - a₂ * s₁) := by ring
      linear_combination hcross + (s₁ * s₂) * hd - (d s₁ * s₂ + s₁ * d s₂) * h1)

private theorem fracDeriv_mk {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (a : R) (s : nonZeroDivisors R) :
    fracDeriv d hadd hmul (Localization.mk a s) =
      algebraMap R (FractionRing R) (d a * s - a * d s) /
        algebraMap R (FractionRing R) (s * s : R) := by
  unfold fracDeriv
  simp only [Localization.liftOn_mk]

theorem fracDeriv_algebraMap {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y) (a : R) :
    fracDeriv d hadd hmul (algebraMap R (FractionRing R) a) = algebraMap R (FractionRing R) (d a) := by
  have hd1 : d 1 = 0 := by
    have h := hmul 1 1; simp only [one_mul, mul_one] at h
    exact add_left_cancel (a := d 1) (by rw [add_zero]; exact h.symm)
  rw [← Localization.mk_one_eq_algebraMap, fracDeriv_mk]
  simp [hd1]

theorem fracDeriv_add {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (x y : FractionRing R) :
    fracDeriv d hadd hmul (x + y) = fracDeriv d hadd hmul x + fracDeriv d hadd hmul y := by
  induction x using Localization.induction_on with
  | H p =>
    induction y using Localization.induction_on with
    | H q =>
      rcases p with ⟨a, s⟩
      rcases q with ⟨b, t⟩
      rw [Localization.add_mk, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk]
      have hs : algebraMap R (FractionRing R) (s : R) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have ht : algebraMap R (FractionRing R) (t : R) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
      simp only [Submonoid.coe_mul, hadd, hmul, map_add, map_sub, map_mul]
      field_simp [hs, ht]
      ring

theorem fracDeriv_mul {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (x y : FractionRing R) :
    fracDeriv d hadd hmul (x * y) =
      fracDeriv d hadd hmul x * y + x * fracDeriv d hadd hmul y := by
  induction x using Localization.induction_on with
  | H p =>
    induction y using Localization.induction_on with
    | H q =>
      rcases p with ⟨a, s⟩
      rcases q with ⟨b, t⟩
      rw [Localization.mk_mul, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk]
      have hs : algebraMap R (FractionRing R) (s : R) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have ht : algebraMap R (FractionRing R) (t : R) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
      have hmk_eq : ∀ (c : R) (u : nonZeroDivisors R),
          Localization.mk c u = algebraMap R (FractionRing R) c / algebraMap R (FractionRing R) (u : R) := by
        intro c u
        have hu : algebraMap R (FractionRing R) (u : R) ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors u.2
        rw [eq_div_iff hu, ← Localization.mk_one_eq_algebraMap (u : R), Localization.mk_mul, mul_one,
          ← Localization.mk_one_eq_algebraMap c, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        refine ⟨1, by simp [mul_comm]⟩
      rw [hmk_eq a s, hmk_eq b t]
      simp only [Submonoid.coe_mul, hmul, map_add, map_sub, map_mul]
      field_simp [hs, ht]
      ring

/-- Compatibility of a `FieldDerivs E` and base embedding `φ : BaseRing →+* E` with `baseDeriv`. -/
structure BaseDerivCompat {E : Type*} [Field E] (φ : BaseRing →+* E) (D : FieldDerivs E) : Prop where
  compat0 : ∀ r : BaseRing, D.d₀ (φ r) = φ (baseDeriv 0 r)
  compat1 : ∀ r : BaseRing, D.d₁ (φ r) = φ (baseDeriv 1 r)

private theorem baseDeriv_add (i : Fin 2) (x y : BaseRing) :
    baseDeriv i (x + y) = baseDeriv i x + baseDeriv i y :=
  (baseDeriv i).map_add x y

/-- Explicit `FieldDerivs` on `FractionRing BaseRing` extending `baseDeriv 0, baseDeriv 1`. -/
def fractionRingFieldDerivs : FieldDerivs (FractionRing BaseRing) where
  d₀ := fracDeriv (baseDeriv 0) (baseDeriv_add 0) (baseDeriv_mul 0)
  d₁ := fracDeriv (baseDeriv 1) (baseDeriv_add 1) (baseDeriv_mul 1)
  d₀_add := fracDeriv_add (baseDeriv 0) (baseDeriv_add 0) (baseDeriv_mul 0)
  d₁_add := fracDeriv_add (baseDeriv 1) (baseDeriv_add 1) (baseDeriv_mul 1)
  d₀_mul := fracDeriv_mul (baseDeriv 0) (baseDeriv_add 0) (baseDeriv_mul 0)
  d₁_mul := fracDeriv_mul (baseDeriv 1) (baseDeriv_add 1) (baseDeriv_mul 1)

theorem fractionRingFieldDerivs_compat :
    BaseDerivCompat (algebraMap BaseRing (FractionRing BaseRing)) fractionRingFieldDerivs where
  compat0 := fracDeriv_algebraMap (baseDeriv 0) (baseDeriv_add 0) (baseDeriv_mul 0)
  compat1 := fracDeriv_algebraMap (baseDeriv 1) (baseDeriv_add 1) (baseDeriv_mul 1)

/-! ## 3. Exact Intertwining of `sourceHasse2 i 1` with `liftD` -/

private def mapDeriv2 {E : Type*} [Field E] (d : E → E) (P : Polynomial (Polynomial E)) :
    Polynomial (Polynomial E) :=
  mapDeriv (mapDeriv d) P

private theorem mapDeriv2_coeff {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (P : Polynomial (Polynomial E)) (b a : ℕ) :
    ((mapDeriv2 d P).coeff b).coeff a = d ((P.coeff b).coeff a) := by
  rw [mapDeriv2, mapDeriv_coeff (mapDeriv_zero h0), mapDeriv_coeff h0]

private theorem mapDeriv2_add {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (P Q : Polynomial (Polynomial E)) :
    mapDeriv2 d (P + Q) = mapDeriv2 d P + mapDeriv2 d Q :=
  mapDeriv_add (mapDeriv_zero h0) (mapDeriv_add h0 hadd) P Q

private theorem mapDeriv2_mul {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (P Q : Polynomial (Polynomial E)) :
    mapDeriv2 d (P * Q) = mapDeriv2 d P * Q + P * mapDeriv2 d Q :=
  mapDeriv_mul (mapDeriv_zero h0) (mapDeriv_add h0 hadd) (mapDeriv_mul h0 hadd hmul) P Q

private def derivY1 {E : Type*} [CommRing E] (Q : Polynomial (Polynomial E)) :
    Polynomial (Polynomial E) :=
  mapDeriv (fun p : Polynomial E => p.derivative) Q

private theorem derivY1_coeff {E : Type*} [CommRing E] (Q : Polynomial (Polynomial E)) (b : ℕ) :
    (derivY1 Q).coeff b = (Q.coeff b).derivative :=
  mapDeriv_coeff (d := fun p : Polynomial E => p.derivative) Polynomial.derivative_zero Q b

private theorem derivY1_add {E : Type*} [CommRing E] (P Q : Polynomial (Polynomial E)) :
    derivY1 (P + Q) = derivY1 P + derivY1 Q :=
  mapDeriv_add (d := fun p : Polynomial E => p.derivative) Polynomial.derivative_zero
    (fun x y => Polynomial.derivative_add) P Q

private theorem derivY1_mul {E : Type*} [CommRing E] (P Q : Polynomial (Polynomial E)) :
    derivY1 (P * Q) = derivY1 P * Q + P * derivY1 Q :=
  mapDeriv_mul (d := fun p : Polynomial E => p.derivative) Polynomial.derivative_zero
    (fun x y => Polynomial.derivative_add) (fun x y => Polynomial.derivative_mul) P Q

private def liftPoly {E : Type*} [Field E] (d : E → E) (α₁ α₂ : E) (Q : Polynomial (Polynomial E)) :
    Polynomial (Polynomial E) :=
  mapDeriv2 d Q - Polynomial.C (Polynomial.C (d α₁)) * derivY1 Q -
    Polynomial.C (Polynomial.C (d α₂)) * Q.derivative

private theorem polyBivar_liftPoly {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (α₁ α₂ : E) (Q : Polynomial (Polynomial E)) :
    polyBivar (liftPoly d α₁ α₂ Q) = liftD d α₁ α₂ (polyBivar Q) := by
  funext a b
  simp only [polyBivar, liftPoly, liftD, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    mapDeriv2_coeff h0, derivY1_coeff, Polynomial.coeff_derivative]
  have hcast : ((Q.coeff (b + 1) * ((b : Polynomial E) + 1)).coeff a : E) =
      (Q.coeff (b + 1)).coeff a * ((b + 1 : ℕ) : E) := by
    have h1 : ((b : Polynomial E) + 1) = Polynomial.C ((b + 1 : ℕ) : E) := by simp
    rw [h1, Polynomial.coeff_mul_C]
  rw [hcast]
  push_cast
  ring

private theorem liftPoly_add {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (α₁ α₂ : E) (P Q : Polynomial (Polynomial E)) :
    liftPoly d α₁ α₂ (P + Q) = liftPoly d α₁ α₂ P + liftPoly d α₁ α₂ Q := by
  simp only [liftPoly, mapDeriv2_add h0 hadd, derivY1_add, Polynomial.derivative_add]
  ring

private theorem liftPoly_mul {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (α₁ α₂ : E) (P Q : Polynomial (Polynomial E)) :
    liftPoly d α₁ α₂ (P * Q) = liftPoly d α₁ α₂ P * Q + P * liftPoly d α₁ α₂ Q := by
  simp only [liftPoly, mapDeriv2_mul h0 hadd hmul, derivY1_mul, Polynomial.derivative_mul]
  ring

private theorem shift2_mapDeriv2 {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0) (h1 : d 1 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (α₁ α₂ : E) (P : Polynomial (Polynomial E)) :
    shift2 α₁ α₂ (mapDeriv2 d P) = liftPoly d α₁ α₂ (shift2 α₁ α₂ P) := by
  have hd0 : (fun p : Polynomial E => p.derivative) 0 = 0 := Polynomial.derivative_zero
  have hd1 : (fun p : Polynomial E => p.derivative) 1 = 0 := Polynomial.derivative_one
  have hC : ∀ p : Polynomial E,
      shift2 α₁ α₂ (mapDeriv2 d (Polynomial.C p)) =
        liftPoly d α₁ α₂ (shift2 α₁ α₂ (Polynomial.C p)) := by
    intro p
    induction p using Polynomial.induction_on with
    | C c =>
      have hl : mapDeriv2 d (Polynomial.C (Polynomial.C c)) = Polynomial.C (Polynomial.C (d c)) := by
        rw [mapDeriv2, mapDeriv_C (mapDeriv_zero h0), mapDeriv_C h0]
      have hs : shift2 α₁ α₂ (Polynomial.C (Polynomial.C c)) = Polynomial.C (Polynomial.C c) := by
        simp [shift2, shift1]
      have hs' : shift2 α₁ α₂ (Polynomial.C (Polynomial.C (d c))) = Polynomial.C (Polynomial.C (d c)) := by
        simp [shift2, shift1]
      rw [hl, hs, hs']
      have hdy : derivY1 (Polynomial.C (Polynomial.C c)) = 0 := by
        rw [derivY1, mapDeriv_C hd0, Polynomial.derivative_C, map_zero]
      rw [liftPoly, hl, hdy, mul_zero, sub_zero, Polynomial.derivative_C, mul_zero, sub_zero]
    | add p q ihp ihq =>
      rw [map_add, mapDeriv2_add h0 hadd, map_add, map_add, liftPoly_add h0 hadd, ihp, ihq]
    | monomial n c ih =>
      have hsplit : Polynomial.C (Polynomial.C c * Polynomial.X ^ (n + 1)) =
          Polynomial.C (Polynomial.C c * Polynomial.X ^ n) * Polynomial.C Polynomial.X := by
        rw [← map_mul, pow_succ, mul_assoc]
      have hX : shift2 α₁ α₂ (mapDeriv2 d (Polynomial.C Polynomial.X)) =
          liftPoly d α₁ α₂ (shift2 α₁ α₂ (Polynomial.C Polynomial.X)) := by
        have hl : mapDeriv2 d (Polynomial.C Polynomial.X) = 0 := by
          rw [mapDeriv2, mapDeriv_C (mapDeriv_zero h0), mapDeriv_X h0 h1, map_zero]
        have hs : shift2 α₁ α₂ (Polynomial.C Polynomial.X) =
            Polynomial.C (Polynomial.X + Polynomial.C α₁) := by
          simp [shift2, shift1]
        rw [hl, map_zero, hs]
        have hdy : derivY1 (Polynomial.C (Polynomial.X + Polynomial.C α₁)) = 1 := by
          rw [derivY1, mapDeriv_C hd0, Polynomial.derivative_add, Polynomial.derivative_X,
            Polynomial.derivative_C, add_zero, map_one]
        rw [liftPoly, mapDeriv2, mapDeriv_C (mapDeriv_zero h0), mapDeriv_add h0 hadd,
          mapDeriv_X h0 h1, mapDeriv_C h0, zero_add, hdy, mul_one, Polynomial.derivative_C,
          mul_zero, sub_zero, sub_self]
      rw [hsplit, mapDeriv2_mul h0 hadd hmul, map_add]
      rw [map_mul (shift2 α₁ α₂), map_mul (shift2 α₁ α₂), map_mul (shift2 α₁ α₂),
        liftPoly_mul h0 hadd hmul, ih, hX]
  induction P using Polynomial.induction_on with
  | C p => exact hC p
  | add P Q ihP ihQ =>
    rw [mapDeriv2_add h0 hadd, map_add, map_add, liftPoly_add h0 hadd, ihP, ihQ]
  | monomial n p ih =>
    have hsplit : Polynomial.C p * Polynomial.X ^ (n + 1) =
        (Polynomial.C p * Polynomial.X ^ n) * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    have hX : shift2 α₁ α₂ (mapDeriv2 d Polynomial.X) =
        liftPoly d α₁ α₂ (shift2 α₁ α₂ Polynomial.X) := by
      have hl : mapDeriv2 d (Polynomial.X : Polynomial (Polynomial E)) = 0 := by
        apply mapDeriv_X (mapDeriv_zero h0)
        rw [show (1 : Polynomial E) = Polynomial.C 1 from rfl, mapDeriv_C h0, h1, map_zero]
      have hs : shift2 α₁ α₂ Polynomial.X = Polynomial.X + Polynomial.C (Polynomial.C α₂) := by
        simp [shift2]
      rw [hl, map_zero, hs]
      have hm1 : mapDeriv2 d (Polynomial.X : Polynomial (Polynomial E)) = 0 := by
        apply mapDeriv_X (mapDeriv_zero h0)
        rw [show (1 : Polynomial E) = Polynomial.C 1 from rfl, mapDeriv_C h0, h1, map_zero]
      have hm2 : mapDeriv2 d (Polynomial.C (Polynomial.C α₂)) = Polynomial.C (Polynomial.C (d α₂)) := by
        rw [mapDeriv2, mapDeriv_C (mapDeriv_zero h0), mapDeriv_C h0]
      have hdy : derivY1 (Polynomial.X + Polynomial.C (Polynomial.C α₂) : Polynomial (Polynomial E)) = 0 := by
        rw [derivY1_add, derivY1, mapDeriv_X hd0 hd1,
          derivY1, mapDeriv_C hd0, Polynomial.derivative_C, map_zero, add_zero]
      simp only [liftPoly, mapDeriv2_add h0 hadd, hm1, hm2, zero_add, hdy, mul_zero, sub_zero,
        Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
        mul_one, sub_self]
    rw [hsplit, mapDeriv2_mul h0 hadd hmul, map_add]
    conv_lhs => rw [map_mul, map_mul]
    conv_rhs => rw [map_mul, liftPoly_mul h0 hadd hmul]
    rw [ih, hX]

private theorem embed2_sourceHasse2 {E : Type*} [Field E] {φ : BaseRing →+* E} {D : FieldDerivs E}
    (hcompat : BaseDerivCompat φ D) (i : Fin 2) (P : Source2) :
    embed2 φ (sourceHasse2 i 1 P) =
      mapDeriv2 (if i = 0 then D.d₀ else D.d₁) (embed2 φ P) := by
  have hd0 : (if i = 0 then D.d₀ else D.d₁) 0 = 0 := by
    split_ifs <;> [exact D.d₀_zero; exact D.d₁_zero]
  ext b a
  rw [mapDeriv2_coeff hd0]
  simp only [embed2, Polynomial.coe_mapRingHom, Polynomial.coeff_map, sourceHasse2,
    mapCoeffs_coeff]
  change φ (baseDeriv i ((P.coeff b).coeff a)) =
    (if i = 0 then D.d₀ else D.d₁) (φ ((P.coeff b).coeff a))
  fin_cases i
  · simp [hcompat.compat0]
  · simp [hcompat.compat1]

/-- **Exact Intertwining Identity**: `sourceHasse2 i 1` acts on the shifted bivariate expansion
    `polyBivar (shift2 α₁ α₂ (embed2 φ P))` identically as `liftD D.dᵢ α₁ α₂`. -/
theorem sourceHasse2_shift2 {E : Type*} [Field E] {φ : BaseRing →+* E} {D : FieldDerivs E}
    (hcompat : BaseDerivCompat φ D) (α₁ α₂ : E) (i : Fin 2) (P : Source2) :
    polyBivar (shift2 α₁ α₂ (embed2 φ (sourceHasse2 i 1 P))) =
      liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P))) := by
  rw [embed2_sourceHasse2 hcompat i P]
  fin_cases i
  · simp only [Fin.zero_eta, ↓reduceIte]
    rw [shift2_mapDeriv2 D.d₀_zero (fieldDerivs_d₀_one D) D.d₀_add D.d₀_mul,
      polyBivar_liftPoly D.d₀_zero]
  · simp only [Fin.mk_one, Fin.one_eq_zero_iff]
    rw [ite_eq_right (by decide : (2 : ℕ) ≠ 1)]
    rw [shift2_mapDeriv2 D.d₁_zero (fieldDerivs_d₁_one D) D.d₁_add D.d₁_mul,
      polyBivar_liftPoly D.d₁_zero]

/-! ## 4. Iterated Cleared-Shift Words & `WordVanishes` From `TwoJetShift.complete2_cleared` -/

def clearedFactor {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [CommRing E]
    (φ : BaseRing →+* E) (i : Fin 2) : E :=
  φ (Polynomial.C (sourceX (Dpole.block i ^ boundedShiftExp s 1)))

theorem clearedFactor_ne_zero {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [Field E]
    {φ : BaseRing →+* E} (hφ : Function.Injective φ) (i : Fin 2) :
    clearedFactor Dpole s φ i ≠ 0 := by
  intro hz
  have hzero : Polynomial.C (sourceX (Dpole.block i ^ boundedShiftExp s 1)) = (0 : BaseRing) :=
    hφ (hz.trans (map_zero φ).symm)
  have hpow_ne : Dpole.block i ^ boundedShiftExp s 1 ≠ 0 :=
    ((Dpole.monic i).pow _).ne_zero
  have hsx : sourceX (Dpole.block i ^ boundedShiftExp s 1) = 0 :=
    Polynomial.C_eq_zero.mp hzero
  apply hpow_ne
  ext n
  have hn := congrArg (fun p : Polynomial SeedPoly => (p.coeff n).coeff 0) hsx
  rw [sourceX, Polynomial.coeff_map, MvPolynomial.coeff_C, ite_eq_left rfl, Polynomial.coeff_zero,
    MvPolynomial.coeff_zero] at hn
  exact hn

theorem clearedFactor_deriv_zero {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [Field E]
    {φ : BaseRing →+* E} {D : FieldDerivs E} (hcompat : BaseDerivCompat φ D) (i : Fin 2) :
    D.d₀ (clearedFactor Dpole s φ i) = 0 ∧ D.d₁ (clearedFactor Dpole s φ i) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [clearedFactor, hcompat.compat0, baseDeriv_sourceX, map_zero]
  · rw [clearedFactor, hcompat.compat1, baseDeriv_sourceX, map_zero]

private theorem applyWord_bivarSmul_of_const {E : Type*} [Field E] (D : FieldDerivs E)
    (α₁ α₂ c : E) (hc0 : D.d₀ c = 0) (hc1 : D.d₁ c = 0) (w : List (Fin 2)) (P : Bivar E) :
    applyWord D α₁ α₂ w (bivarSmul c P) = bivarSmul c (applyWord D α₁ α₂ w P) := by
  induction w generalizing P with
  | nil => rfl
  | cons i ws ih =>
    simp only [applyWord]
    have hstep : (if i = 0 then liftD D.d₀ α₁ α₂ (bivarSmul c P)
        else liftD D.d₁ α₁ α₂ (bivarSmul c P)) =
        bivarSmul c (if i = 0 then liftD D.d₀ α₁ α₂ P else liftD D.d₁ α₁ α₂ P) := by
      split_ifs
      · funext a b
        simp only [liftD, bivarSmul, D.d₀_mul, hc0, zero_mul, zero_add]
        ring
      · funext a b
        simp only [liftD, bivarSmul, D.d₁_mul, hc1, zero_mul, zero_add]
        ring
    rw [hstep, ih]

def applyClearedWord {h : ℕ} (Dpole : PoleData h) (s : Shape2) :
    List (Fin 2) → Source2 → Source2
  | [], P => P
  | i :: ws, P => applyClearedWord Dpole s ws (cleared2Shift Dpole s i 1 P)

def wordFactor {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [CommRing E]
    (φ : BaseRing →+* E) : List (Fin 2) → E
  | [] => 1
  | i :: ws => wordFactor Dpole s φ ws * clearedFactor Dpole s φ i

theorem wordFactor_ne_zero {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [Field E]
    {φ : BaseRing →+* E} (hφ : Function.Injective φ) (w : List (Fin 2)) :
    wordFactor Dpole s φ w ≠ 0 := by
  induction w with
  | nil => exact one_ne_zero
  | cons i ws ih =>
    exact mul_ne_zero ih (clearedFactor_ne_zero Dpole s hφ i)

theorem applyClearedWord_mem_complete2 {h : ℕ} {Dpole : PoleData h} (Crt : CRTLift Dpole)
    (word : I → L) {s : Shape2} {W : ℕ} {P : Source2}
    (hP : P ∈ complete2 Crt word s W) (w : List (Fin 2)) :
    applyClearedWord Dpole s w P ∈
      complete2 Crt word s (W + w.length * (boundedShiftExp s 1 * h)) := by
  induction w generalizing W P with
  | nil => simpa [applyClearedWord] using hP
  | cons i ws ih =>
    have h1 := complete2_cleared Crt word hP i 1
    have h2 := ih h1
    have hlen : W + boundedShiftExp s 1 * h + ws.length * (boundedShiftExp s 1 * h) =
        W + (i :: ws).length * (boundedShiftExp s 1 * h) := by
      simp only [List.length_cons]
      ring
    simpa only [applyClearedWord, hlen] using h2

private theorem cleared2Shift_shift2 {h : ℕ} (Dpole : PoleData h) (s : Shape2)
    {E : Type*} [Field E] {φ : BaseRing →+* E} {D : FieldDerivs E}
    (hcompat : BaseDerivCompat φ D) (α₁ α₂ : E) (i : Fin 2) (P : Source2) :
    polyBivar (shift2 α₁ α₂ (embed2 φ (cleared2Shift Dpole s i 1 P))) =
      bivarSmul (clearedFactor Dpole s φ i)
        (liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))) := by
  have hc : shift2 α₁ α₂ (embed2 φ (jetConstant2 (sourceX (Dpole.block i ^ boundedShiftExp s 1)))) =
      Polynomial.C (Polynomial.C (clearedFactor Dpole s φ i)) := by
    simp [jetConstant2, embed2, shift2, shift1, clearedFactor]
  have hmul : shift2 α₁ α₂ (embed2 φ (cleared2Shift Dpole s i 1 P)) =
      Polynomial.C (Polynomial.C (clearedFactor Dpole s φ i)) *
        shift2 α₁ α₂ (embed2 φ (sourceHasse2 i 1 P)) := by
    rw [cleared2Shift, map_mul, map_mul, hc]
  funext a b
  rw [hmul, polyBivar, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  have hs := congrFun (congrFun (sourceHasse2_shift2 hcompat α₁ α₂ i P) a) b
  change clearedFactor Dpole s φ i * polyBivar (shift2 α₁ α₂ (embed2 φ (sourceHasse2 i 1 P))) a b =
    bivarSmul (clearedFactor Dpole s φ i)
      (liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))) a b
  rw [hs]
  rfl

theorem applyClearedWord_shift2 {h : ℕ} (Dpole : PoleData h) (s : Shape2)
    {E : Type*} [Field E] {φ : BaseRing →+* E} {D : FieldDerivs E}
    (hcompat : BaseDerivCompat φ D) (α₁ α₂ : E) (w : List (Fin 2)) (P : Source2) :
    polyBivar (shift2 α₁ α₂ (embed2 φ (applyClearedWord Dpole s w P))) =
      bivarSmul (wordFactor Dpole s φ w)
        (applyWord D α₁ α₂ w (polyBivar (shift2 α₁ α₂ (embed2 φ P)))) := by
  induction w generalizing P with
  | nil =>
    funext a b
    simp [applyClearedWord, wordFactor, applyWord, bivarSmul]
  | cons i ws ih =>
    rw [applyClearedWord, ih, cleared2Shift_shift2 Dpole s hcompat α₁ α₂ i P]
    obtain ⟨hc0, hc1⟩ := clearedFactor_deriv_zero Dpole s hcompat i
    rw [applyWord_bivarSmul_of_const D α₁ α₂ _ hc0 hc1]
    have hif : liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P))) =
        (if i = 0 then liftD D.d₀ α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))
         else liftD D.d₁ α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))) := by
      split_ifs <;> rfl
    rw [hif]
    funext a b
    simp only [wordFactor, applyWord, bivarSmul]
    ring

/-- **Automatic `WordVanishes` from `TwoJetShift.complete2_cleared`**:
    If every `Q ∈ complete2 Crt word s W'` with `W' < N` vanishes at `(α₁, α₂)`, then every
    `P ∈ complete2 Crt word s W` satisfies `WordVanishes D α₁ α₂ k` whenever
    `W + k * (boundedShiftExp s 1 * h) < N`. -/
theorem wordVanishes_of_all_complete2_eval_zero {h : ℕ} {Dpole : PoleData h} (Crt : CRTLift Dpole)
    (word : I → L) (s : Shape2) (N : ℕ)
    {E : Type*} [Field E] {φ : BaseRing →+* E} (hφ : Function.Injective φ)
    {D : FieldDerivs E} (hcompat : BaseDerivCompat φ D) (α₁ α₂ : E)
    (hall : ∀ W' < N, ∀ Q ∈ complete2 Crt word s W',
      polyBivar (shift2 α₁ α₂ (embed2 φ Q)) 0 0 = 0)
    {W k : ℕ} (hWk : W + k * (boundedShiftExp s 1 * h) < N)
    {P : Source2} (hP : P ∈ complete2 Crt word s W) :
    WordVanishes D α₁ α₂ k (polyBivar (shift2 α₁ α₂ (embed2 φ P))) := by
  intro w hw
  have hW' : W + w.length * (boundedShiftExp s 1 * h) < N :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hw) W).trans_lt hWk
  have hmem := applyClearedWord_mem_complete2 Crt word hP w
  have hz := hall _ hW' _ hmem
  have hsc := congrFun (congrFun (applyClearedWord_shift2 Dpole s hcompat α₁ α₂ w P) 0) 0
  rw [hsc] at hz
  exact (mul_eq_zero.mp hz).resolve_left (wordFactor_ne_zero Dpole s hφ w)

/-! ## 5. Bézout Evaluation Bridge (`prolongSubst_bezout` → `(α₁, α₂)` Vanishing) -/

theorem polyBivar_shift2_zero_zero {E : Type*} [CommRing E] (α₁ α₂ : E)
    (P : Polynomial (Polynomial E)) :
    polyBivar (shift2 α₁ α₂ P) 0 0 =
      Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ P := by
  have h : (Polynomial.evalRingHom 0).comp
      ((Polynomial.evalRingHom (0 : Polynomial E)).comp (shift2 α₁ α₂)) =
      Polynomial.eval₂RingHom (Polynomial.evalRingHom α₁) α₂ := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro c; simp [shift2, shift1]
      · simp [shift2, shift1]
    · simp [shift2]
  have hp := RingHom.congr_fun h P
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_eval₂RingHom] at hp
  rw [polyBivar, Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero]
  exact hp

theorem natDegree_le_of_mem_ambient2 {h : ℕ} {s : Shape2} {W : ℕ} {Q : Source2}
    (hQ : Q ∈ ambient2 h s W) : Q.natDegree ≤ s.C := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro e₂ he₂
  ext e₁ e₀ a e
  simp only [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
  exact hQ e₂ e₁ e₀ a e (fun hel => (not_le_of_gt he₂) hel.2.2.1)

/-- If `evJet : K1_14.Jet →+* E` evaluates the 1-jet prime `G` to `0`, `A` to a nonzero element,
    `A * Y₂ + B₁` at `α₂` to `0`, and intertwines `centerEval2` with `embed2 φ` at `(α₁, α₂)`,
    then `G ∣ prolongSubst A B₁ s.C (centerEval2 Q)` implies `Q` vanishes at `(α₁, α₂)`. -/
theorem eval_zero_of_prolongSubst_dvd {E : Type*} [Field E]
    (φ : BaseRing →+* E) (evJet : K1_14.Jet →+* E) (α₁ α₂ : E)
    (hcomm : ∀ Q : Source2,
      Polynomial.eval₂ evJet α₂ (centerEval2 Q) =
        Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ (embed2 φ Q))
    {h : ℕ} {s : Shape2} {W : ℕ} {G A B₁ : K1_14.Jet}
    (hG0 : evJet G = 0) (hAne : evJet A ≠ 0) (hG1 : evJet A * α₂ + evJet B₁ = 0)
    {Q : Source2} (hQ : Q ∈ ambient2 h s W)
    (hdvd : G ∣ prolongSubst A B₁ s.C (centerEval2 Q)) :
    polyBivar (shift2 α₁ α₂ (embed2 φ Q)) 0 0 = 0 := by
  have hdeg : (centerEval2 Q).natDegree ≤ s.C :=
    (Polynomial.natDegree_map_le).trans (natDegree_le_of_mem_ambient2 hQ)
  obtain ⟨R, hR⟩ := prolongSubst_bezout A B₁ s.C hdeg
  obtain ⟨q, hq⟩ := hdvd
  have hps0 : evJet (prolongSubst A B₁ s.C (centerEval2 Q)) = 0 := by
    rw [hq, map_mul, hG0, zero_mul]
  have hev := congrArg (Polynomial.eval₂ evJet α₂) hR
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, hps0, hG1, map_pow,
    sub_zero, mul_zero, zero_mul] at hev
  have h0 : Polynomial.eval₂ evJet α₂ (centerEval2 Q) = 0 :=
    (mul_eq_zero.mp hev).resolve_left (pow_ne_zero s.C hAne)
  rw [polyBivar_shift2_zero_zero, ← hcomm Q]
  exact h0

/-! ## 5B. Automatic Non-Vanishing of Case-B Resultant (`Res_{z₀}(G, G^(1)) ≠ 0`) -/

private theorem pderiv_eq_zero_of_jetDegree_zero {P : PolynomialDifferential.DifferentialPolynomial CJ0.K 2}
    (h0 : PolynomialDifferential.jetDegree P (Fin.last 2) = 0) :
    MvPolynomial.pderiv (some (Fin.last 2)) P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero]
  by_cases hmem : m + Finsupp.single (some (Fin.last 2)) 1 ∈ P.support
  · exfalso
    have hle := MvPolynomial.degreeOf_le_iff.mp h0.le (m + Finsupp.single (some (Fin.last 2)) 1) hmem
    have hpos : (m + Finsupp.single (some (Fin.last 2)) 1 : Option (Fin 3) →₀ ℕ) (some (Fin.last 2)) =
        m (some (Fin.last 2)) + 1 := by simp
    omega
  · rw [MvPolynomial.notMem_support_iff.mp hmem, zero_mul]
    rfl

/-- **Linear-`Y₂` Coprimality (`not_dvd_linear_Y2`)**:
    If `Gd`, `A_poly`, `B_poly` are `Y₂`-free (`jetDegree _ (Fin.last 2) = 0`) and `¬ Gd ∣ A_poly`,
    then `Gd` cannot divide the prolongation `G₁d = A_poly * C (X (some (Fin.last 2))) + B_poly`. -/
theorem not_dvd_linear_Y2
    (Gd A_poly B_poly : Polynomial (PolynomialDifferential.DifferentialPolynomial CJ0.K 2))
    (hG_top : ∀ i, PolynomialDifferential.jetDegree (Gd.coeff i) (Fin.last 2) = 0)
    (hA_top : ∀ i, PolynomialDifferential.jetDegree (A_poly.coeff i) (Fin.last 2) = 0)
    (hB_top : ∀ i, PolynomialDifferential.jetDegree (B_poly.coeff i) (Fin.last 2) = 0)
    (hndiv : ¬ Gd ∣ A_poly) :
    ¬ Gd ∣ (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly) := by
  let dY2 : PolynomialDifferential.DifferentialPolynomial CJ0.K 2 →
      PolynomialDifferential.DifferentialPolynomial CJ0.K 2 :=
    fun p => MvPolynomial.pderiv (some (Fin.last 2)) p
  have hd0 : dY2 0 = 0 := map_zero _
  have hdadd : ∀ x y, dY2 (x + y) = dY2 x + dY2 y := fun x y => map_add _ x y
  have hdmul : ∀ x y, dY2 (x * y) = dY2 x * y + x * dY2 y := fun x y => by
    simp only [dY2, MvPolynomial.pderiv_mul]
  have hkill : ∀ P : Polynomial (PolynomialDifferential.DifferentialPolynomial CJ0.K 2),
      (∀ i, PolynomialDifferential.jetDegree (P.coeff i) (Fin.last 2) = 0) →
      mapDeriv dY2 P = 0 := by
    intro P hP
    apply Polynomial.ext
    intro i
    rw [mapDeriv_coeff hd0, Polynomial.coeff_zero]
    exact pderiv_eq_zero_of_jetDegree_zero (hP i)
  rintro ⟨Q, hQ⟩
  have hL := congrArg (mapDeriv dY2) hQ
  rw [mapDeriv_add hd0 hdadd, mapDeriv_mul hd0 hdadd hdmul, mapDeriv_mul hd0 hdadd hdmul,
    hkill Gd hG_top, hkill A_poly hA_top, hkill B_poly hB_top,
    zero_mul, zero_mul, zero_add, zero_add, add_zero,
    mapDeriv_C hd0] at hL
  have hX1 : dY2 (MvPolynomial.X (some (Fin.last 2))) = 1 := by simp [dY2]
  rw [hX1, map_one, mul_one] at hL
  exact hndiv ⟨mapDeriv dY2 Q, hL⟩

/-- **Automatic Resultant Non-Vanishing (`resultant_ne_zero_of_irreducible_not_dvd`)**:
    For any irreducible `Gd` of positive `z₀`-degree and any `G₁d` not divisible by `Gd`,
    the Sylvester resultant `Gd.resultant G₁d Gd.natDegree G₁d.natDegree` is nonzero. -/
theorem resultant_ne_zero_of_irreducible_not_dvd
    (Gd G₁d : Polynomial (PolynomialDifferential.DifferentialPolynomial CJ0.K 2))
    (hIrr : Irreducible Gd) (hpos : 0 < Gd.natDegree) (hndiv : ¬ Gd ∣ G₁d) :
    Gd.resultant G₁d Gd.natDegree G₁d.natDegree ≠ 0 := by
  let R := PolynomialDifferential.DifferentialPolynomial CJ0.K 2
  let φ := algebraMap R (FractionRing R)
  have hinj : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hp : Gd.IsPrimitive := hIrr.isPrimitive hpos.ne'
  have him : Irreducible (Gd.map φ) := hp.irreducible_iff_irreducible_map_fraction_map.mp hIrr
  have hcop : IsCoprime (Gd.map φ) (G₁d.map φ) := by
    apply him.coprime_iff_not_dvd.mpr
    intro hd
    obtain ⟨a, ha⟩ := hp.dvd_of_fraction_map_dvd_fraction_map hd
    exact hndiv ⟨a, ha⟩
  have hn := Polynomial.resultant_ne_zero (Gd.map φ) (G₁d.map φ) hcop
  intro hz
  apply hn
  rw [Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.resultant_map_map]
  change φ (Gd.resultant G₁d Gd.natDegree G₁d.natDegree) = 0
  rw [hz, map_zero]

/-! ## 6. End-to-End Case-A Avoidance Without `hvan` & Unified Hybrid 6-Rect Rescue -/

/-- **End-to-End 2-Jet Case-A Avoidance Theorem (`caseA_avoidance_from_complete2_cleared`)**:
    Removes the `hvan` assumption completely by combining L4 `TwoJetShift.complete2_cleared`,
    L4 `TwoJetRescueBridge.prolongSubst_bezout`, and L4
    `TwoJetCaseAKernel.caseA_avoidance_of_lowCoords_surplus`. -/
theorem caseA_avoidance_from_complete2_cleared {E : Type*} [Field E] [CharP E K1.p]
    (D : FieldDerivs E) (φ : BaseRing →+* E) (hφ : Function.Injective φ)
    (hcompat : BaseDerivCompat φ D)
    (evJet : K1_14.Jet →+* E) {α₁ α₂ : E} (hdet : jacDet D α₁ α₂ ≠ 0)
    (hcomm : ∀ Q : Source2,
      Polynomial.eval₂ evJet α₂ (centerEval2 Q) =
        Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ (embed2 φ Q))
    {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {Dpole : PoleData h} (Crt : CRTLift Dpole) (word : I → L) (s : Shape2) (N physRank : ℕ)
    (G A B₁ : K1_14.Jet) (hG0 : evJet G = 0) (hAne : evJet A ≠ 0) (hG1 : evJet A * α₂ + evJet B₁ = 0)
    (k : ℕ → ℕ)
    (hk : ∀ W < N, k W < K1.p)
    (hWk : ∀ W < N, W + k W * (boundedShiftExp s 1 * h) < N)
    (hphys : ∀ W < N, Module.finrank L (ambient2 h s W) ≤
      physRank + Module.finrank L (contacted2 h word s W))
    (hlow :
      N * (physRank + poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) <
      ∑ W ∈ Finset.range N, (lowCoords h s W (k W)).card) :
    ∃ W < N, ∃ P ∈ complete2 Crt word s W, ¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P) := by
  by_contra hnone
  push_neg at hnone
  have hall : ∀ W' < N, ∀ Q ∈ complete2 Crt word s W',
      polyBivar (shift2 α₁ α₂ (embed2 φ Q)) 0 0 = 0 := fun W' hW' Q hQ =>
    eval_zero_of_prolongSubst_dvd φ evJet α₁ α₂ hcomm hG0 hAne hG1 hQ.1.1 (hnone W' hW' Q hQ)
  have hvan : ∀ W < N, ∀ P ∈ prolongKernel Crt word s W G A B₁,
      WordVanishes D α₁ α₂ (k W) (polyBivar (shift2 α₁ α₂ (embed2 φ P))) :=
    fun W hW P hP => wordVanishes_of_all_complete2_eval_zero Crt word s N hφ hcompat α₁ α₂ hall
      (hWk W hW) hP.1
  obtain ⟨W, hW, P, hP, havoid⟩ :=
    caseA_avoidance_of_lowCoords_surplus D φ hφ hdet hpos hchar Crt word s N physRank G A B₁
      k hk hphys hvan hlow
  exact havoid (hnone W hW P hP)

/-- **Unified 6-Small-Rectangle Hybrid Rescue Dichotomy at `69.63` (`A = 179,798`)**:
    Packages both branches of the 2-jet Prolongation Rescue for every small rectangle
    `r ∈ {.r0, .r1, .r2a, .r3a_j2, .r3a_j4, .r3a_j7}`:
    - **Case A (`jacDet D α₁ α₂ ≠ 0`)**: produces `W < N` and `P ∈ complete2 Crt word s W`
      whose prolongation substitution `prolongSubst A B₁ s.C (centerEval2 P)` avoids `G`
      (zero `hvan` assumption, directly from L4 `TwoJetShift.complete2_cleared` + L4
      `PoleBound2Jet.pole_bound_2jet`).
    - **Case B (`jacDet D α₁ α₂ = 0`, nonzero Sylvester resultant `Res_{z₀}(G, G^(1))`)**:
      proves `T.card ≤ smallRectCap6963 r ≤ 44_890_000_000_000_000` (`44.89e15 < 61.30e15`)
      for any finite `T ⊆ closeHigh 179798 w` of degree-`< 133,721` polynomials on `(G, G^(1))`. -/
theorem small_rect_hybrid_rescue_6963 {E : Type*} [Field E] [CharP E K1.p]
    (D : FieldDerivs E) (φ : BaseRing →+* E) (hφ : Function.Injective φ)
    (hcompat : BaseDerivCompat φ D) (evJet : K1_14.Jet →+* E) (α₁ α₂ : E)
    (hcomm : ∀ Q : Source2,
      Polynomial.eval₂ evJet α₂ (centerEval2 Q) =
        Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ (embed2 φ Q))
    {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {Dpole : PoleData h} (Crt : CRTLift Dpole) (word : I → L) (s : Shape2) (N physRank : ℕ)
    (G A B₁ : K1_14.Jet) (hG0 : evJet G = 0) (hAne : evJet A ≠ 0) (hG1 : evJet A * α₂ + evJet B₁ = 0)
    (k : ℕ → ℕ) (hk : ∀ W < N, k W < K1.p)
    (hWk : ∀ W < N, W + k W * (boundedShiftExp s 1 * h) < N)
    (hphys : ∀ W < N, Module.finrank L (ambient2 h s W) ≤
      physRank + Module.finrank L (contacted2 h word s W))
    (hlow :
      N * (physRank + poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) <
      ∑ W ∈ Finset.range N, (lowCoords h s W (k W)).card)
    {r : RescueRect} (hr : IsSmallRect r) {j u : ℕ} (hin : InRect j u r)
    (Gd A_poly B_poly : Polynomial (PolynomialDifferential.DifferentialPolynomial CJ0.K 2))
    (hIrr : Irreducible Gd) (hposG : 0 < Gd.natDegree)
    (hG_u : Gd.natDegree ≤ u)
    (hG₁_u : (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).natDegree ≤ u)
    (hG_top_all : ∀ i, PolynomialDifferential.jetDegree (Gd.coeff i) (Fin.last 2) = 0)
    (hA_top_all : ∀ i, PolynomialDifferential.jetDegree (A_poly.coeff i) (Fin.last 2) = 0)
    (hB_top_all : ∀ i, PolynomialDifferential.jetDegree (B_poly.coeff i) (Fin.last 2) = 0)
    (hndivA : ¬ Gd ∣ A_poly)
    (hG_tot : ∀ i ≤ Gd.natDegree, PolynomialDifferential.jetTotalDegree (Gd.coeff i) ≤ j)
    (hG_idx : ∀ i ≤ Gd.natDegree, (Gd.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 1)
    (hG₁_tot : ∀ i ≤ (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).natDegree,
      PolynomialDifferential.jetTotalDegree
        ((A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).coeff i) ≤ j + 1)
    (hG₁_idx : ∀ i ≤ (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).natDegree,
      ((A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).coeff i).weightedTotalDegree
        CJ0.indexWeight ≤ 2)
    (hG₁_top : ∀ i ≤ (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).natDegree,
      PolynomialDifferential.jetDegree
        ((A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).coeff i) (Fin.last 2) ≤ 1)
    (w : CJ0.Node → CJ0.K) (T : Finset (Polynomial CJ0.K))
    (hT : (T : Set (Polynomial CJ0.K)) ⊆ CJ0High133721.closeHigh 179798 w)
    (hcommon : ∀ f ∈ T, ∃ z₀ : Polynomial CJ0.K,
      Gd.eval₂ (PolynomialDifferential.differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0 ∧
      (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).eval₂
        (PolynomialDifferential.differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0) :
    (∃ W < N, ∃ P ∈ complete2 Crt word s W, ¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P)) ∨
    (T.card ≤ smallRectCap6963 r ∧ T.card ≤ 44_890_000_000_000_000) := by
  by_cases hdet : jacDet D α₁ α₂ ≠ 0
  · exact Or.inl (caseA_avoidance_from_complete2_cleared D φ hφ hcompat evJet hdet hcomm
      hpos hchar Crt word s N physRank G A B₁ hG0 hAne hG1 k hk hWk hphys hlow)
  · let G₁d := A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly
    have hndiv : ¬ Gd ∣ G₁d := not_dvd_linear_Y2 Gd A_poly B_poly hG_top_all hA_top_all hB_top_all hndivA
    have hne : Gd.resultant G₁d Gd.natDegree G₁d.natDegree ≠ 0 :=
      resultant_ne_zero_of_irreducible_not_dvd Gd G₁d hIrr hposG hndiv
    exact Or.inr (caseB_small_rects_card_le_6963 hr hin Gd G₁d hG_u hG₁_u le_rfl le_rfl
      (Or.inl hposG.ne') hne hG_tot hG_idx (fun i _ => hG_top_all i)
      hG₁_tot hG₁_idx hG₁_top w T hT hcommon)

end

end TwoJetCaseADriver

#print axioms TwoJetCaseADriver.fractionRingFieldDerivs_compat
#print axioms TwoJetCaseADriver.sourceHasse2_shift2
#print axioms TwoJetCaseADriver.applyClearedWord_mem_complete2
#print axioms TwoJetCaseADriver.applyClearedWord_shift2
#print axioms TwoJetCaseADriver.wordVanishes_of_all_complete2_eval_zero
#print axioms TwoJetCaseADriver.eval_zero_of_prolongSubst_dvd
#print axioms TwoJetCaseADriver.not_dvd_linear_Y2
#print axioms TwoJetCaseADriver.resultant_ne_zero_of_irreducible_not_dvd
#print axioms TwoJetCaseADriver.caseA_avoidance_from_complete2_cleared
#print axioms TwoJetCaseADriver.small_rect_hybrid_rescue_6963

end Merged_TwoJetCaseADriver

-- merged module TwoJetCaseAFX
section Merged_TwoJetCaseAFX

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

/-!
# End-to-End 2-Jet Case-A Prolongation Avoidance at `69.61` (`TwoJetCaseAFX`)

Combines:
- `TwoJetCaseAFXCore` (`telescope2`, `leading_bound_2jet`)
- `TwoJetCaseAFXRank` (`physRank2_m59`)
- `PoleBound2Jet` (`pole_bound_2jet`)
- `TwoJetCaseADriver` (`fractionRingFieldDerivs`, `wordVanishes_of_all_complete2_eval_zero`,
  `eval_zero_of_prolongSubst_dvd`)
- `TwoJetCaseAKernel` (`pow_collapse_of_wordVanishes`, `zero_of_deg_le_and_order_gt`)

to prove `caseA_avoidance_6961`: for every `h ∈ [2368, 2401]` and every linear-in-`Y₁` prime
`G : K1_14.Jet` (`G.natDegree = 1`) with Case-A nonzero seed Jacobian determinant
`jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) ≠ 0`, there exist `W < 59 * 179798` and
`P₀ ∈ complete2 Crt word (shape2_m59 399) W` such that
  `¬ G ∣ prolongSubst (prolongA G) (prolongB1 G) 10 (centerEval2 P₀)`.
-/

namespace TwoJetCaseAFX

section FastNat61

private def natSum : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => natSum n f + f n

private def natSumBlock (start : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => natSumBlock start n f + f (start + n)

private theorem natSumBlock_add (a b c : ℕ) (f : ℕ → ℕ) :
    natSumBlock a (b + c) f = natSumBlock a b f + natSumBlock (a + b) c f := by
  induction c with
  | zero => simp [natSumBlock]
  | succ c ih =>
    rw [← Nat.add_assoc, natSumBlock, natSumBlock, ih, Nat.add_assoc, Nat.add_assoc]

private theorem natSum_eq_block (n : ℕ) (f : ℕ → ℕ) : natSum n f = natSumBlock 0 n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natSum, natSumBlock, ih]

private def gradeCount61 (q : ℕ) : ℕ :=
  natSum 11 fun e₂ => if e₂ ≤ q then min (q - e₂) (24 - 2 * e₂) + 1 else 0

private def colCount61 (t q : ℕ) : ℕ :=
  natSum 11 fun e₂ =>
    if e₂ ≤ q ∧ t + 2 * e₂ ≤ 127 then
      min (min (q - e₂) (24 - 2 * e₂)) (127 - t - 2 * e₂) + 1 - (24 - t - 2 * e₂)
    else 0

private def pivCount61 (t q : ℕ) : ℕ :=
  natSum 11 fun e₂ =>
    if e₂ ≤ q ∧ t + q + 2 * e₂ ≤ 127 then
      min (min (q - e₂) (24 - 2 * e₂)) (127 - t - q - 2 * e₂) + 1 - (24 - t - 2 * e₂)
    else 0

private def optK61 (t : ℕ) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42,
    43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61,
    62, 63, 64, 65, 66, 67, 68, 69, 69, 70, 71, 72, 72, 73, 74, 74, 75, 75, 76,
    76, 77, 77, 77, 77, 77, 78, 78, 78, 78, 78, 78, 78, 78, 78, 79, 79, 79, 79,
    79, 79, 79, 79, 79, 79, 79, 79]).getD t 0

private def offsetUpper61 (t : ℕ) : ℕ :=
  let R := natSum 81 (pivCount61 t)
  let k := optK61 t
  R * k + natSum 81 (fun q => (q - k) * colCount61 t q) - natSum 81 (fun q => q * pivCount61 t q)

private theorem optK61_lt_81 : ∀ t : Fin 128, optK61 t.val < 81 := by decide +kernel
private theorem poleRows2_nat_val : natSum 81 (fun q => (104 - q) * gradeCount61 q) = 662695 := by decide +kernel
private theorem box_card_val : natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ => 81 - e₁ - e₂)) = 11385 := by decide +kernel
private theorem box_q_val :
    natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ =>
      (81 - e₁ - e₂) * (81 - e₁ - e₂ - 1) / 2 + (81 - e₁ - e₂) * (e₁ + e₂))) = 521345 := by decide +kernel
private theorem box_v_val :
    natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ => (81 - e₁ - e₂) * (e₁ + 2 * e₂))) = 173635 := by decide +kernel
private theorem box_12_val :
    natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ => (81 - e₁ - e₂) * (e₁ + e₂))) = 131890 := by decide +kernel
private theorem offsetUpper_val : natSum 128 offsetUpper61 = 9858694 := by decide +kernel

end FastNat61

noncomputable section

open Polynomial Finset
open K1 (I)
open K1_14 (L FX Seeds Equation Jet triangle)
open K1_14_1 (SeedPoly seedWeight PoleData CRTLift)
open K1_14_1_3 (sourceX)
open K1_14_2_2 (RowCaps)
open PoleMoment2Jet (Shape2 jetIdx poleRows2 poleCredit2 groupedPoleMoment2)
open PoleBound2Jet (Source2 coeffAt2 trueEligible2 ambient2 contacted2 complete2 pole_bound_2jet)
open TwoJetShift (boundedShiftExp)
open TwoJetRescueBridge (Jet2 centerEval2 evaluated2 prolongSubst)
open TwoJetCaseAKernel (FieldDerivs jacDet shift2 polyBivar embed2 zero_of_deg_le_and_order_gt
  pow_collapse_of_wordVanishes)
open TwoJetCaseADriver (BaseRing mapDeriv mapDeriv_coeff mapDeriv_zero mapDeriv_add mapDeriv_mul
  fracDeriv fracDeriv_algebraMap fracDeriv_add fracDeriv_mul fractionRingFieldDerivs
  fractionRingFieldDerivs_compat wordVanishes_of_all_complete2_eval_zero
  eval_zero_of_prolongSubst_dvd)
open scoped BigOperators Polynomial Classical

/-! ## 1. Field Embedding `Equation →+* FractionRing BaseRing` & `Jet2 →+* E[Y₁][Y₂]` -/

abbrev EField := FractionRing BaseRing

private def sourceXHom : Polynomial L →+* Polynomial SeedPoly :=
  Polynomial.mapRingHom MvPolynomial.C

private theorem sourceXHom_eq (p : Polynomial L) : sourceXHom p = sourceX p := rfl

private theorem sourceX_injective : Function.Injective sourceXHom := by
  intro p q hpq
  ext a
  have h := congrArg (fun r : Polynomial SeedPoly => (r.coeff a).coeff 0) hpq
  simpa [sourceXHom, Polynomial.coeff_map, MvPolynomial.coeff_C] using h

private def fxToE : FX →+* EField :=
  IsFractionRing.lift
    (g := (algebraMap BaseRing EField).comp (Polynomial.C.comp sourceXHom))
    ((IsFractionRing.injective BaseRing EField).comp
      (Polynomial.C_injective.comp sourceX_injective))

private theorem fxToE_algebraMap (p : Polynomial L) :
    fxToE (algebraMap (Polynomial L) FX p) =
      algebraMap BaseRing EField (Polynomial.C (sourceX p)) :=
  IsFractionRing.lift_algebraMap _ p

def seedsToE : Seeds →+* EField :=
  MvPolynomial.eval₂Hom fxToE
    (fun i => algebraMap BaseRing EField (Polynomial.C (Polynomial.C (MvPolynomial.X i))))

def seedsY0ToE : Equation →+* EField :=
  Polynomial.eval₂RingHom seedsToE (algebraMap BaseRing EField Polynomial.X)

def jet2ToE : Jet2 →+* Polynomial (Polynomial EField) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom seedsY0ToE)

private def centerBaseY0 : BaseRing →+* Equation :=
  Polynomial.mapRingHom (Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
    (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X)))

private theorem seedsY0ToE_comp_centerBaseY0 :
    seedsY0ToE.comp centerBaseY0 = algebraMap BaseRing EField := by
  apply Polynomial.ringHom_ext
  · intro q
    simp only [RingHom.comp_apply, centerBaseY0, Polynomial.coe_mapRingHom, Polynomial.map_C,
      seedsY0ToE, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    induction q using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ =>
      rw [Polynomial.eval₂_add, map_add, Polynomial.C_add, map_add, ih₁, ih₂]
    | monomial n s =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, map_mul, map_pow,
        Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      simp only [seedsToE, MvPolynomial.eval₂Hom_C, fxToE_algebraMap, Polynomial.map_pow,
        sourceX, Polynomial.map_X]
      congr 1
      induction s using MvPolynomial.induction_on with
      | C c =>
        have hC : MvPolynomial.map (algebraMap L FX) (MvPolynomial.C c : SeedPoly) =
            MvPolynomial.C (algebraMap (Polynomial L) FX (Polynomial.C c)) := by
          rw [MvPolynomial.map_C]; rfl
        rw [hC, MvPolynomial.eval₂Hom_C, fxToE_algebraMap]
        simp [sourceX]
      | add p₁ p₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
      | mul_X p i ih =>
        rw [map_mul, MvPolynomial.map_X, map_mul, MvPolynomial.eval₂Hom_X', ih]
        rw [Polynomial.C_mul, Polynomial.C_mul, map_mul]
  · simp [centerBaseY0, seedsY0ToE]

private theorem fxToE_mul_denom (a : FX) :
    ∃ d : Polynomial L, d ≠ 0 ∧ ∃ n : Polynomial L,
      algebraMap (Polynomial L) FX d * a = algebraMap (Polynomial L) FX n := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial L)) a
  refine ⟨d.1, nonZeroDivisors.ne_zero d.2, n, ?_⟩
  simpa [mul_comm] using hnd

theorem seedsY0ToE_injective : Function.Injective seedsY0ToE := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  -- Clear denominators of all FX-coefficients in `q : Polynomial Seeds`
  let coeffs : Finset FX :=
    q.support.biUnion fun i => (q.coeff i).support.image fun m => (q.coeff i).coeff m
  have hex : ∀ c ∈ coeffs, ∃ d : Polynomial L, d ≠ 0 ∧
      ∃ n : Polynomial L, algebraMap (Polynomial L) FX d * c = algebraMap (Polynomial L) FX n :=
    fun c _ => fxToE_mul_denom c
  choose den hden_ne num hnum using fun c : coeffs => fxToE_mul_denom c.1
  let D : Polynomial L := ∏ c : coeffs, den c
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hden_ne c
  -- Every coefficient of `D • q` lies in `algebraMap (Polynomial L) FX`
  have hclear : ∀ i m, ∃ p : Polynomial L,
      algebraMap (Polynomial L) FX D * ((q.coeff i).coeff m) = algebraMap (Polynomial L) FX p := by
    intro i m
    by_cases h0 : (q.coeff i).coeff m = 0
    · exact ⟨0, by simp [h0]⟩
    · have hmem : (q.coeff i).coeff m ∈ coeffs := by
        refine Finset.mem_biUnion.mpr ⟨i, Polynomial.mem_support_iff.mpr (fun hz => h0 (by simp [hz])),
          Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr h0, rfl⟩⟩
      let c : coeffs := ⟨(q.coeff i).coeff m, hmem⟩
      let D' : Polynomial L := ∏ c' ∈ Finset.univ.erase c, den c'
      have hD_split : D = D' * den c := by
        dsimp only [D, D']
        rw [Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
      refine ⟨D' * num c, ?_⟩
      rw [hD_split, map_mul, map_mul, mul_assoc, hnum c]
  -- Lift `D • q` to `r : BaseRing` with `centerBaseY0 r = C (MvPolynomial.C (algebraMap D)) * q`
  choose poly hpoly using hclear
  let mkSeedPoly (i : ℕ) : Polynomial SeedPoly :=
    ∑ m ∈ (q.coeff i).support, (poly i m).map MvPolynomial.C * Polynomial.C (MvPolynomial.monomial m 1)
  let r : BaseRing := ∑ i ∈ q.support, Polynomial.monomial i (mkSeedPoly i)
  have hr_eq : centerBaseY0 r = Polynomial.C (MvPolynomial.C (algebraMap (Polynomial L) FX D)) * q := by
    have hcoeff_r : ∀ i, (centerBaseY0 r).coeff i =
        MvPolynomial.C (algebraMap (Polynomial L) FX D) * q.coeff i := by
      intro i
      rw [centerBaseY0, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      have hri : r.coeff i = if i ∈ q.support then mkSeedPoly i else 0 := by
        simp only [r, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply,
          Finset.sum_ite_eq']
      rw [hri]
      split_ifs with hi
      · apply MvPolynomial.ext; intro m
        simp only [mkSeedPoly, map_sum, map_mul, MvPolynomial.coeff_sum]
        have hterm (m' : Fin 2 →₀ ℕ) :
            (Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
              (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
              ((poly i m').map MvPolynomial.C) *
            Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
              (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
              (Polynomial.C (MvPolynomial.monomial m' 1))) =
            MvPolynomial.monomial m' (algebraMap (Polynomial L) FX (poly i m')) := by
          have hev : Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
              (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
              ((poly i m').map (MvPolynomial.C : L →+* SeedPoly)) =
              MvPolynomial.C (algebraMap (Polynomial L) FX (poly i m')) := by
            induction poly i m' using Polynomial.induction_on' with
            | add p₁ p₂ ih₁ ih₂ => simp only [Polynomial.map_add, map_add, ih₁, ih₂]
            | monomial n c =>
              simp only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_pow,
                Polynomial.map_C, Polynomial.map_X, map_mul, map_pow, Polynomial.coe_eval₂RingHom,
                Polynomial.eval₂_C, Polynomial.eval₂_X, MvPolynomial.map_C]
              rfl
          rw [hev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, MvPolynomial.map_monomial,
            map_one, MvPolynomial.C_mul_monomial, mul_one]
        simp_rw [hterm, MvPolynomial.coeff_monomial]
        rw [Finset.sum_ite_eq', MvPolynomial.coeff_C_mul]
        split_ifs with hm
        · exact (hpoly i m).symm
        · have h0 : (q.coeff i).coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
          rw [h0, mul_zero]
      · rw [map_zero, Polynomial.notMem_support_iff.mp hi, mul_zero]
    ext i; rw [hcoeff_r i, Polynomial.coeff_C_mul]
  have hr0 : algebraMap BaseRing EField r = 0 := by
    rw [← seedsY0ToE_comp_centerBaseY0, RingHom.comp_apply, hr_eq, map_mul, hq, mul_zero]
  have hr_zero : r = 0 := IsFractionRing.injective BaseRing EField (hr0.trans (map_zero _).symm)
  rw [hr_zero, map_zero] at hr_eq
  have hD_ne' : Polynomial.C (MvPolynomial.C (algebraMap (Polynomial L) FX D)) ≠ (0 : Equation) := by
    intro hz
    have h1 : algebraMap (Polynomial L) FX D = 0 :=
      MvPolynomial.C_eq_zero.mp (Polynomial.C_eq_zero.mp hz)
    exact hD_ne (IsFractionRing.injective (Polynomial L) FX (h1.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hr_eq.symm).resolve_left hD_ne'

theorem jet2ToE_centerEval2 (Q : Source2) :
    jet2ToE (centerEval2 Q) = embed2 (algebraMap BaseRing EField) Q := by
  have hbase_eq :
      (Polynomial.mapRingHom
        (Polynomial.eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
          (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
          (fun _ => Commute.all _ _)).toRingHom) = centerBaseY0 := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply MvPolynomial.ringHom_ext
        · intro a; simp [centerBaseY0]
        · intro i; simp [centerBaseY0]
      · simp [centerBaseY0]
    · simp [centerBaseY0]
  have hcomp : (jet2ToE.comp centerEval2.toRingHom) = embed2 (algebraMap BaseRing EField) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply RingHom.ext; intro q
        have hq := RingHom.congr_fun seedsY0ToE_comp_centerBaseY0 q
        have hq' : seedsY0ToE
            (Polynomial.map
              (Polynomial.eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
                (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
                (fun _ => Commute.all _ _)).toRingHom q) =
            algebraMap BaseRing EField q := by
          have := congrArg (fun f : BaseRing →+* Equation => seedsY0ToE (f q)) hbase_eq
          exact this.trans hq
        simpa [jet2ToE, centerEval2, K1_14_1.centerEval, embed2] using congrArg (Polynomial.C ∘ Polynomial.C) hq'
      · simp [jet2ToE, centerEval2, K1_14_1.centerEval, embed2]
    · simp [jet2ToE, centerEval2, K1_14_1.centerEval, embed2]
  exact RingHom.congr_fun hcomp Q

theorem jet2ToE_smul (c : FX) (P : Jet2) :
    jet2ToE (c • P) = Polynomial.C (Polynomial.C (fxToE c)) * jet2ToE P := by
  ext e₂ e₁
  simp only [jet2ToE, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_C_mul]
  have hsmul : ((c • P).coeff e₂).coeff e₁ = Polynomial.C (MvPolynomial.C c) * ((P.coeff e₂).coeff e₁) := by
    rw [Algebra.smul_def]
    simp [MvPolynomial.algebraMap_eq]
  rw [hsmul, map_mul]
  congr 1
  simp [seedsY0ToE, seedsToE]

theorem jet2ToE_eval₂_comm (α₁ α₂ : EField) (Q : Source2) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom seedsY0ToE α₁) α₂ (centerEval2 Q) =
      Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ (embed2 (algebraMap BaseRing EField) Q) := by
  rw [← jet2ToE_centerEval2 Q]
  have h : (Polynomial.eval₂RingHom (Polynomial.evalRingHom α₁) α₂).comp jet2ToE =
      Polynomial.eval₂RingHom (Polynomial.eval₂RingHom seedsY0ToE α₁) α₂ := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply RingHom.ext; intro c; simp [jet2ToE]
      · simp [jet2ToE]
    · simp [jet2ToE]
  exact (RingHom.congr_fun h (centerEval2 Q)).symm

/-! ## 2. 1-Jet Prolongation `G^(1) = prolongA G * Y₂ + prolongB1 G` & `RowCaps` -/

def derivFX : FX → FX :=
  fracDeriv (fun p : Polynomial L => p.derivative)
    (fun _ _ => Polynomial.derivative_add)
    (fun _ _ => Polynomial.derivative_mul)

theorem derivFX_zero : derivFX 0 = 0 := by
  have h := fracDeriv_algebraMap (fun p : Polynomial L => p.derivative)
    (fun _ _ => Polynomial.derivative_add) (fun _ _ => Polynomial.derivative_mul) 0
  rw [map_zero, Polynomial.derivative_zero, map_zero] at h
  exact h

theorem derivFX_add (x y : FX) : derivFX (x + y) = derivFX x + derivFX y :=
  fracDeriv_add _ _ _ x y

theorem derivFX_mul (x y : FX) : derivFX (x * y) = derivFX x * y + x * derivFX y :=
  fracDeriv_mul _ _ _ x y

theorem derivFX_algebraMap (p : Polynomial L) :
    derivFX (algebraMap (Polynomial L) FX p) = algebraMap (Polynomial L) FX p.derivative :=
  fracDeriv_algebraMap _ _ _ p

def derivSeedsX (p : Seeds) : Seeds :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (derivFX (p.coeff m))

theorem derivSeedsX_coeff (p : Seeds) (m : Fin 2 →₀ ℕ) :
    (derivSeedsX p).coeff m = derivFX (p.coeff m) := by
  classical
  dsimp only [derivSeedsX]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, derivFX_zero]

theorem derivSeedsX_zero : derivSeedsX 0 = 0 := by
  ext m; simp [derivSeedsX_coeff, derivFX_zero]

theorem derivSeedsX_add (p q : Seeds) : derivSeedsX (p + q) = derivSeedsX p + derivSeedsX q := by
  ext m; simp [derivSeedsX_coeff, derivFX_add]

theorem derivSeedsX_mul (p q : Seeds) :
    derivSeedsX (p * q) = derivSeedsX p * q + p * derivSeedsX q := by
  classical
  have hd_sum : ∀ (s : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) (f : _ → FX),
      derivFX (∑ i ∈ s, f i) = ∑ i ∈ s, derivFX (f i) := by
    intro s f
    induction s using Finset.induction with
    | empty => simp [derivFX_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, derivFX_add, ih]
  ext m
  rw [derivSeedsX_coeff, MvPolynomial.coeff_add, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul, hd_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [derivFX_mul, derivSeedsX_coeff, derivSeedsX_coeff]

theorem derivSeedsX_totalDegree_le (p : Seeds) : (derivSeedsX p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro m hm
  have hne : p.coeff m ≠ 0 := by
    intro hz
    have h0 := MvPolynomial.mem_support_iff.mp hm
    rw [derivSeedsX_coeff, hz, derivFX_zero] at h0
    exact h0 rfl
  exact MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)

def jetDerivX (G : Jet) : Jet :=
  mapDeriv (mapDeriv derivSeedsX) G

def jetDerivY0 (G : Jet) : Jet :=
  mapDeriv Polynomial.derivative G

def prolongA (G : Jet) : Jet :=
  2 * Polynomial.C (G.coeff 1)

def prolongB1 (G : Jet) : Jet :=
  jetDerivX G + jetDerivY0 G * Polynomial.X

theorem jetDerivX_coeff (G : Jet) (j i : ℕ) :
    ((jetDerivX G).coeff j).coeff i = derivSeedsX ((G.coeff j).coeff i) := by
  rw [jetDerivX, mapDeriv_coeff (mapDeriv_zero derivSeedsX_zero), mapDeriv_coeff derivSeedsX_zero]

theorem jetDerivY0_coeff (G : Jet) (j i : ℕ) :
    ((jetDerivY0 G).coeff j).coeff i = ((G.coeff j).coeff (i + 1)) * ((i + 1 : ℕ) : Seeds) := by
  rw [jetDerivY0, mapDeriv_coeff Polynomial.derivative_zero, Polynomial.coeff_derivative]
  push_cast; rfl

theorem rowCaps_add {P Q : Jet} {s : K1_14.Shape} (hP : RowCaps P s) (hQ : RowCaps Q s) :
    RowCaps (P + Q) s := by
  intro j i hne
  simp only [Polynomial.coeff_add] at hne ⊢
  by_cases hp : (P.coeff j).coeff i = 0
  · rw [hp, zero_add] at hne ⊢; exact hQ j i hne
  · by_cases hq : (Q.coeff j).coeff i = 0
    · rw [hq, add_zero]; exact hP j i hp
    · have h1 := hP j i hp
      have h2 := hQ j i hq
      exact ⟨h1.1, h1.2.1, (MvPolynomial.totalDegree_add _ _).trans (max_le h1.2.2 h2.2.2)⟩

theorem rowCaps_neg {P : Jet} {s : K1_14.Shape} (hP : RowCaps P s) : RowCaps (-P) s := by
  intro j i hne
  simp only [Polynomial.coeff_neg, neg_ne_zero] at hne
  have h := hP j i hne
  refine ⟨h.1, h.2.1, ?_⟩
  simp only [Polynomial.coeff_neg, MvPolynomial.totalDegree, MvPolynomial.support_neg]
  exact h.2.2

theorem rowCaps_mul {P Q : Jet} {s t : K1_14.Shape} (hP : RowCaps P s) (hQ : RowCaps Q t) :
    RowCaps (P * Q) ⟨0, s.B + t.B, s.J + t.J, s.U + t.U⟩ := by
  intro j i hne
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff] at hne
  obtain ⟨⟨j₁, j₂⟩, hj, hne1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [Polynomial.coeff_mul] at hne1
  obtain ⟨⟨i₁, i₂⟩, hi, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
  have h1 := hP j₁ i₁ (left_ne_zero_of_mul hne2)
  have h2 := hQ j₂ i₂ (right_ne_zero_of_mul hne2)
  have hje := Finset.mem_antidiagonal.mp hj
  have hie := Finset.mem_antidiagonal.mp hi
  dsimp only
  refine ⟨by omega, by omega, ?_⟩
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  refine MvPolynomial.totalDegree_finsetSum_le fun ⟨a₁, a₂⟩ _ => ?_
  rw [Polynomial.coeff_mul]
  refine MvPolynomial.totalDegree_finsetSum_le fun ⟨b₁, b₂⟩ _ => ?_
  by_cases hz : ((P.coeff a₁).coeff b₁) * ((Q.coeff a₂).coeff b₂) = 0
  · simp [hz]
  · have ha1 := hP a₁ b₁ (left_ne_zero_of_mul hz)
    have ha2 := hQ a₂ b₂ (right_ne_zero_of_mul hz)
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ha1.2.2 ha2.2.2)

theorem rowCaps_pow {P : Jet} {s : K1_14.Shape} (hP : RowCaps P s) (n : ℕ) :
    RowCaps (P ^ n) ⟨0, n * s.B, n * s.J, n * s.U⟩ := by
  induction n with
  | zero =>
    intro j i hne
    rw [pow_zero] at hne
    by_cases hj : j = 0
    · subst hj
      by_cases hi : i = 0
      · subst hi; simp
      · simp [Polynomial.coeff_one, hi] at hne
    · simp [Polynomial.coeff_one, hj] at hne
  | succ n ih =>
    rw [pow_succ]
    have hm := rowCaps_mul ih hP
    intro j i hne
    have ⟨h1, h2, h3⟩ := hm j i hne
    exact ⟨by simp only [Nat.succ_mul]; omega, by simp only [Nat.succ_mul]; omega,
      by simp only [Nat.succ_mul]; omega⟩

theorem rowCaps_mono {P : Jet} {s t : K1_14.Shape} (hP : RowCaps P s)
    (hB : s.B ≤ t.B) (hJ : s.J ≤ t.J) (hU : s.U ≤ t.U) : RowCaps P t := by
  intro j i hne
  have ⟨h1, h2, h3⟩ := hP j i hne
  exact ⟨h1.trans hB, h2.trans hJ, h3.trans hU⟩

theorem prolongA_rowCaps {G : Jet} {j u : ℕ} (hj : 1 ≤ j) (hG : RowCaps G ⟨0, j, 1, u⟩) :
    RowCaps (prolongA G) ⟨0, j - 1, 0, u⟩ := by
  intro k i hne
  have h2 : prolongA G = Polynomial.C (2 * G.coeff 1) := by
    simp [prolongA, map_ofNat]
  rw [h2, Polynomial.coeff_C] at hne ⊢
  split_ifs at hne ⊢ with hk
  · subst hk
    rw [show (2 : Equation) = Polynomial.C (2 : Seeds) from (map_ofNat Polynomial.C 2).symm,
      Polynomial.coeff_C_mul] at hne ⊢
    have hc := hG 1 i (right_ne_zero_of_mul hne)
    dsimp only at hc ⊢
    refine ⟨by omega, le_rfl, ?_⟩
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      have h2d : (2 : Seeds).totalDegree = 0 := by
        rw [show (2 : Seeds) = MvPolynomial.C (2 : FX) from (map_ofNat MvPolynomial.C 2).symm,
          MvPolynomial.totalDegree_C]
      rw [h2d, zero_add]; exact hc.2.2)
  · simp at hne

theorem prolongB1_rowCaps {G : Jet} {j u : ℕ} (hG : RowCaps G ⟨0, j, 1, u⟩) :
    RowCaps (prolongB1 G) ⟨0, j, 2, u⟩ := by
  apply rowCaps_add
  · intro k i hne
    rw [jetDerivX_coeff] at hne ⊢
    have hc : (G.coeff k).coeff i ≠ 0 := fun hz => hne (by rw [hz, derivSeedsX_zero])
    have ⟨h1, h2, h3⟩ := hG k i hc
    dsimp only at h1 h2 h3 ⊢
    exact ⟨h1, by omega, (derivSeedsX_totalDegree_le _).trans h3⟩
  · intro k i hne
    cases k with
    | zero => simp at hne
    | succ k' =>
      rw [Polynomial.coeff_mul_X, jetDerivY0_coeff] at hne ⊢
      have hc : (G.coeff k').coeff (i + 1) ≠ 0 := left_ne_zero_of_mul hne
      have ⟨h1, h2, h3⟩ := hG k' (i + 1) hc
      dsimp only at h1 h2 h3 ⊢
      refine ⟨by omega, by omega, ?_⟩
      exact (MvPolynomial.totalDegree_mul _ _).trans (by
        have hnd : ((i + 1 : ℕ) : Seeds).totalDegree = 0 := by
          rw [← MvPolynomial.C_eq_natCast, MvPolynomial.totalDegree_C]
        rw [hnd, add_zero]; exact h3)

/-- Exact `RowCaps` of `prolongSubst (prolongA G) (prolongB1 G) 10 (centerEval2 P₀)` for
    `P₀ ∈ ambient2 h (shape2_m59 399) W`: `⟨0, 80 + 10*(j - 1), 24, 399 + 10*u⟩`! -/
theorem prolongSubst_rowCaps {h W j u : ℕ} (hj : 1 ≤ j) {G : Jet} (hG : RowCaps G ⟨0, j, 1, u⟩)
    {P₀ : Source2} (hP : P₀ ∈ ambient2 h (shape2_m59 399) W) :
    RowCaps (prolongSubst (prolongA G) (prolongB1 G) 10 (centerEval2 P₀))
      ⟨0, 80 + 10 * (j - 1), 24, 399 + 10 * u⟩ := by
  unfold prolongSubst
  have hsum : ∀ (S : Finset ℕ) (f : ℕ → Jet),
      (∀ e₂ ∈ S, RowCaps (f e₂) ⟨0, 80 + 10 * (j - 1), 24, 399 + 10 * u⟩) →
      RowCaps (∑ e₂ ∈ S, f e₂) ⟨0, 80 + 10 * (j - 1), 24, 399 + 10 * u⟩ := by
    intro S f hf
    induction S using Finset.induction with
    | empty => intro k i hne; simp at hne
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact rowCaps_add (hf a (Finset.mem_insert_self a S))
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
  apply hsum
  intro e₂ he₂
  have he₂_le : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  have hPcoeff : RowCaps ((centerEval2 P₀).coeff e₂) ⟨0, 80 - e₂, 24 - 2 * e₂, 399⟩ := by
    intro e₁ e₀ hne
    rw [centerEval2_eq_tripleMap, tripleMap_coeff] at hne
    have hcoeff_ne : (((P₀.coeff e₂).coeff e₁).coeff e₀) ≠ 0 := fun hz => hne (by rw [hz, map_zero])
    obtain ⟨a, ha⟩ : ∃ a, ((((P₀.coeff e₂).coeff e₁).coeff e₀).coeff a) ≠ 0 := by
      by_contra! hall; exact hcoeff_ne (Polynomial.ext fun a => by simpa using hall a)
    obtain ⟨e, he⟩ : ∃ e, coeffAt2 P₀ e₂ e₁ e₀ a e ≠ 0 := by
      by_contra! hall
      exact ha (MvPolynomial.ext _ _ fun e => by simpa [coeffAt2, PoleMoment2Jet.sourceCoeff2] using hall e)
    have hel : trueEligible2 h (shape2_m59 399) W e₂ e₁ e₀ a e := by
      by_contra hnot; exact he (hP e₂ e₁ e₀ a e hnot)
    obtain ⟨hB, hJ, _, _, _⟩ := hel
    dsimp only [shape2_m59, jetIdx] at hB hJ ⊢
    refine ⟨by omega, by omega, ?_⟩
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro m hm
    by_contra hbig
    have h0 : ((((centerEval2 P₀).coeff e₂).coeff e₁).coeff e₀).coeff m = 0 := by
      change jetCoords2 (centerEval2 P₀) (e₂, e₁, e₀, m) = 0
      rw [coords2_center]
      have hsc0 : sourceCoord2 P₀ (e₂, e₁, e₀, m) = 0 := by
        apply Polynomial.ext; intro c
        rw [sourceCoord2_coeff, Polynomial.coeff_zero]
        exact hP e₂ e₁ e₀ c m (fun hel' => hbig hel'.2.2.2.1)
      rw [hsc0, map_zero]
    exact (MvPolynomial.mem_support_iff.mp hm) h0
  have hB1 := rowCaps_pow (rowCaps_neg (prolongB1_rowCaps hG)) e₂
  have hA := rowCaps_pow (prolongA_rowCaps hj hG) (10 - e₂)
  have hmul := rowCaps_mul (rowCaps_mul hPcoeff hB1) hA
  apply rowCaps_mono hmul
  · have h1 : e₂ * j + (10 - e₂) * (j - 1) = e₂ + 10 * (j - 1) := by
      zify [hj, he₂_le]; ring
    dsimp only; omega
  · dsimp only; omega
  · have h2 : e₂ * u + (10 - e₂) * u = 10 * u := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' he₂_le]
    dsimp only; omega

/-! ## 3. Graded `FX`-Kernel Finrank Bound & Exact Linear-in-`h` Surplus -/

def boxPos2 : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range 11) ×ˢ ((Finset.range 25) ×ˢ (Finset.range 81))).filter fun m =>
    m.2.2 + m.2.1 + m.1 ≤ 80 ∧ jetIdx m.2.1 m.1 ≤ 24 ∧ m.1 ≤ 10

def highPos2 (h W k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  boxPos2.filter fun m =>
    (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧ k < m.2.1 + m.1

theorem mem_boxPos2 {m : ℕ × ℕ × ℕ} :
    m ∈ boxPos2 ↔ m.2.2 + m.2.1 + m.1 ≤ 80 ∧ jetIdx m.2.1 m.1 ≤ 24 ∧ m.1 ≤ 10 := by
  rcases m with ⟨e₂, e₁, e₀⟩
  simp only [boxPos2, Finset.mem_filter, Finset.mem_product, Finset.mem_range, jetIdx]
  constructor
  · intro h; exact h.2
  · intro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega, by omega⟩, h1, h2, h3⟩

private def seedExpsU (U : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  ((Finset.range (U + 1)) ×ˢ (Finset.range (U + 1))).filter (fun p => p.1 + p.2 ≤ U)
    |>.image (fun p => Finsupp.single 0 p.1 + Finsupp.single 1 p.2)

private theorem mem_seedExpsU {U : ℕ} {e : Fin 2 →₀ ℕ} :
    e ∈ seedExpsU U ↔ seedWeight e ≤ U := by
  simp only [seedExpsU, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨_, _⟩, hab⟩, rfl⟩
    rw [seedWeight, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
    simpa using hab
  · intro hle
    have hsum : e 0 + e 1 ≤ U := by
      rw [seedWeight, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hle
      exact hle
    refine ⟨(e 0, e 1), ⟨⟨by omega, by omega⟩, hsum⟩, ?_⟩
    ext j; fin_cases j <;> simp

private theorem card_seedExpsU (U : ℕ) : (seedExpsU U).card = triangle U := by
  have hinj : Set.InjOn (fun p : ℕ × ℕ => Finsupp.single (0 : Fin 2) p.1 + Finsupp.single 1 p.2)
      (((Finset.range (U + 1)) ×ˢ (Finset.range (U + 1))).filter (fun p => p.1 + p.2 ≤ U) : Set (ℕ × ℕ)) := by
    intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp only [Finsupp.add_apply, Finsupp.single_apply] at h0 h1
    exact Prod.ext (by simpa using h0) (by simpa using h1)
  rw [seedExpsU, Finset.card_image_of_injOn hinj]
  have hfib : (((Finset.range (U + 1)) ×ˢ (Finset.range (U + 1))).filter (fun p => p.1 + p.2 ≤ U)).card =
      ∑ a ∈ Finset.range (U + 1), (U + 1 - a) := by
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl; intro a ha
    have ha' : a ≤ U := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [← Finset.card_filter]
    have heq : (Finset.range (U + 1)).filter (fun b => a + b ≤ U) = Finset.range (U + 1 - a) := by
      ext b; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [heq, Finset.card_range]
  rw [hfib]
  clear hinj hfib
  induction U with
  | zero => decide
  | succ U ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero]
    have hshift : ∑ k ∈ Finset.range (U + 1), (U + 1 + 1 - (k + 1)) =
        ∑ k ∈ Finset.range (U + 1), (U + 1 - k) := by
      apply Finset.sum_congr rfl; intro k _; omega
    rw [hshift, ih]
    unfold triangle
    have h2 : 2 * ((U + 1) * (U + 2) / 2) = (U + 1) * (U + 2) :=
      Nat.mul_div_cancel' (Nat.even_mul_succ_self (U + 1)).two_dvd
    have h2' : 2 * ((U + 1 + 1) * (U + 1 + 2) / 2) = (U + 1 + 1) * (U + 1 + 2) :=
      Nat.mul_div_cancel' (Nat.even_mul_succ_self (U + 1 + 1)).two_dvd
    have hring : (U + 1 + 1) * (U + 1 + 2) = (U + 1) * (U + 2) + 2 * (U + 2) := by ring
    omega

private theorem evaluated2_mem_box {h U W : ℕ} {D : PoleData h} {Crt : CRTLift D} {word : I → L}
    {P : Jet2} (hP : P ∈ evaluated2 Crt word (shape2_m59 U) W) :
    ∀ e₂ e₁ e₀ e, ((((P.coeff e₂).coeff e₁).coeff e₀).coeff e ≠ 0) →
      (e₂, e₁, e₀) ∈ boxPos2 ∧ seedWeight e ≤ U := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Q, hQ, rfl⟩ := hP
    intro e₂ e₁ e₀ e hne
    rw [show ((((centerEval2 Q).coeff e₂).coeff e₁).coeff e₀).coeff e =
        algebraMap (Polynomial L) FX (sourceCoord2 Q (e₂, e₁, e₀, e)) from
        coords2_center Q (e₂, e₁, e₀, e)] at hne
    have hsc_ne : sourceCoord2 Q (e₂, e₁, e₀, e) ≠ 0 := fun hz => hne (by rw [hz, map_zero])
    obtain ⟨a, ha⟩ : ∃ a, (sourceCoord2 Q (e₂, e₁, e₀, e)).coeff a ≠ 0 := by
      by_contra! hall; exact hsc_ne (Polynomial.ext fun a => by simpa using hall a)
    rw [sourceCoord2_coeff] at ha
    have hel : trueEligible2 h (shape2_m59 U) W e₂ e₁ e₀ a e := by
      by_contra hnot; exact ha (hQ.1.1 e₂ e₁ e₀ a e hnot)
    exact ⟨mem_boxPos2.mpr ⟨hel.1, hel.2.1, hel.2.2.1⟩, hel.2.2.2.1⟩
  | zero => intro e₂ e₁ e₀ e hne; simp at hne
  | add P₁ P₂ _ _ ih₁ ih₂ =>
    intro e₂ e₁ e₀ e hne
    simp only [Polynomial.coeff_add, MvPolynomial.coeff_add] at hne
    by_cases h1 : (((P₁.coeff e₂).coeff e₁).coeff e₀).coeff e = 0
    · rw [h1, zero_add] at hne; exact ih₂ e₂ e₁ e₀ e hne
    · exact ih₁ e₂ e₁ e₀ e h1
  | smul c P _ ih =>
    intro e₂ e₁ e₀ e hne
    have hmul : ((((c • P).coeff e₂).coeff e₁).coeff e₀).coeff e =
        c * (((P.coeff e₂).coeff e₁).coeff e₀).coeff e := by
      change jetCoords2 (c • P) (e₂, e₁, e₀, e) = c * jetCoords2 P (e₂, e₁, e₀, e)
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hmul] at hne
    exact ih e₂ e₁ e₀ e (right_ne_zero_of_mul hne)

/-- **Graded 2-Jet `FX`-Kernel Finrank Bound (`finrank_FX_vanishOrder_le`)**:
    If every `Q ∈ complete2 Crt word (shape2_m59 U) W` vanishes to order `> k` at `(α₁, α₂)` under
    `shift2 α₁ α₂ ∘ embed2 (algebraMap BaseRing EField)`, then
      `Module.finrank FX (evaluated2 Crt word (shape2_m59 U) W) ≤ triangle U * (highPos2 h W k).card`. -/
theorem finrank_FX_vanishOrder_le {h U W k : ℕ} (hpos : 0 < h) (hh : h ≤ 131069)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (α₁ α₂ : EField)
    (hord : ∀ Q ∈ complete2 Crt word (shape2_m59 U) W,
      ∀ a b, a + b ≤ k → polyBivar (shift2 α₁ α₂ (embed2 (algebraMap BaseRing EField) Q)) a b = 0) :
    Module.finrank FX (evaluated2 Crt word (shape2_m59 U) W) ≤
      triangle U * (highPos2 h W k).card := by
  classical
  let s := shape2_m59 U
  -- Step 1: Every `P ∈ evaluated2 Crt word s W` also vanishes to order `> k` under `shift2 α₁ α₂ ∘ jet2ToE`!
  have hordP : ∀ P ∈ evaluated2 Crt word s W,
      ∀ a b, a + b ≤ k → polyBivar (shift2 α₁ α₂ (jet2ToE P)) a b = 0 := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨Q, hQ, rfl⟩ := hP
      rw [jet2ToE_centerEval2]
      exact hord Q hQ
    | zero => intro a b _; simp [polyBivar]
    | add P₁ P₂ _ _ ih₁ ih₂ =>
      intro a b hab
      simp only [map_add, polyBivar, Polynomial.coeff_add]
      unfold polyBivar at ih₁ ih₂
      rw [ih₁ a b hab, ih₂ a b hab, add_zero]
    | smul c P _ ih =>
      intro a b hab
      rw [jet2ToE_smul, map_mul]
      have hC : shift2 α₁ α₂ (Polynomial.C (Polynomial.C (fxToE c))) =
          Polynomial.C (Polynomial.C (fxToE c)) := by
        simp [TwoJetCaseAKernel.shift2, TwoJetCaseAKernel.shift1]
      rw [hC, polyBivar, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
      change fxToE c * polyBivar (shift2 α₁ α₂ (jet2ToE P)) a b = 0
      rw [ih a b hab, mul_zero]
  -- Step 2: Project `evaluated2 Crt word s W` onto `(highPos2 h W k × seedExpsU U → FX)`!
  let H := highPos2 h W k
  let SE := seedExpsU U
  let π : evaluated2 Crt word s W →ₗ[FX] (H × SE → FX) :=
    LinearMap.pi fun u =>
      { toFun := fun P => jetCoords2 P.1 (u.1.1.1, u.1.1.2.1, u.1.1.2.2, u.2.1)
        map_add' := fun P Q => by simp
        map_smul' := fun c P => by simp }
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    apply Subtype.ext
    change P.1 = 0
    by_contra hnz
    -- Take the graded-maximal nonzero monomial `m* = (e₂*, e₁*, e₀*)` of `P.1`!
    obtain ⟨m, hm, hmax⟩ := exists_graded_max hnz
    have hbd := leading_bound_2jet hpos hh Crt word s W P.2 hm hmax
    have hm_ne : (((P.1.coeff m.1).coeff m.2.1).coeff m.2.2) ≠ 0 := (mem_support3 P.1 m).mp hm
    obtain ⟨e, he⟩ : ∃ e, ((((P.1.coeff m.1).coeff m.2.1).coeff m.2.2).coeff e) ≠ 0 := by
      by_contra! hall; exact hm_ne (MvPolynomial.ext _ _ fun e => by simpa using hall e)
    obtain ⟨hm_box, heU⟩ := evaluated2_mem_box P.2 m.1 m.2.1 m.2.2 e he
    -- Cannot have `k < m.2.1 + m.1`, because then `(m, e) ∈ H × SE` and `π P = 0` contradicts `he`!
    have hle_k : m.2.1 + m.1 ≤ k := by
      by_contra hgt
      have hmH : m ∈ H := Finset.mem_filter.mpr ⟨hm_box, hbd, Nat.lt_of_not_ge hgt⟩
      have heSE : e ∈ SE := mem_seedExpsU.mpr heU
      have h0 : jetCoords2 P.1 (m.1, m.2.1, m.2.2, e) = 0 := congrFun hP (⟨m, hmH⟩, ⟨e, heSE⟩)
      exact he h0
    -- Since `m` is maximal under `(e₁ + e₂, e₂, e₀)`, EVERY nonzero `(e₂, e₁)` of `P.1` has `e₁ + e₂ ≤ k`!
    have hdeg_le : ∀ a b, k < a + b → polyBivar (jet2ToE P.1) a b = 0 := by
      intro a b hab
      simp only [polyBivar, jet2ToE, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      have hzero : (P.1.coeff b).coeff a = 0 := by
        apply Polynomial.ext; intro e₀
        simp only [Polynomial.coeff_zero]
        by_contra hne₀
        have hmem' : (b, a, e₀) ∈ support3 P.1 := (mem_support3 P.1 _).mpr hne₀
        have hle := hmax (b, a, e₀) hmem'
        rcases hle with hlt | heq
        · unfold gradedLt at hlt
          dsimp only at hlt
          omega
        · subst heq
          dsimp only at hle_k
          omega
      rw [hzero, map_zero]
    -- Apply `zero_of_deg_le_and_order_gt` to `jet2ToE P.1`!
    have hj0 : jet2ToE P.1 = 0 := zero_of_deg_le_and_order_gt α₁ α₂ hdeg_le (hordP P.1 P.2)
    have hP0 : P.1 = 0 :=
      (Polynomial.map_injective _ (Polynomial.map_injective _ seedsY0ToE_injective))
        (hj0.trans (Polynomial.map_zero _).symm)
    exact hnz hP0
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, card_seedExpsU] at hle
  simpa only [mul_comm] using hle

/-! ## 4. Exact Combinatorial Receipts & Linear-in-`h` Surplus for `69.61` -/

private theorem finset_sum_range_eq_natSum (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range n, f i = natSum n f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ih]; rfl

private theorem card_range_filter_Icc (N lo hi : ℕ) (hhi : hi < N) :
    ((Finset.range N).filter fun x => lo ≤ x ∧ x ≤ hi).card = hi + 1 - lo := by
  by_cases h : lo ≤ hi
  · have heq : (Finset.range N).filter (fun x => lo ≤ x ∧ x ≤ hi) = Finset.Icc lo hi := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    rw [heq, Nat.card_Icc]
  · have heq : (Finset.range N).filter (fun x => lo ≤ x ∧ x ≤ hi) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]; omega
    rw [heq, Finset.card_empty]; omega

private theorem gradeSlots2_card_61 (q : ℕ) :
    (PoleMoment2Jet.gradeSlots2 (shape2_m59 399) q).card = gradeCount61 q := by
  rw [PoleMoment2Jet.gradeSlots2, Finset.card_filter, Finset.sum_product_right, gradeCount61,
    ← finset_sum_range_eq_natSum]
  dsimp only [shape2_m59]
  apply Finset.sum_congr rfl; intro e₂ he₂
  have he₂' : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  rw [← Finset.card_filter]
  split_ifs with hq
  · have heq : (Finset.range 25).filter (fun e₁ => e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) =
        (Finset.range 25).filter (fun e₁ => 0 ≤ e₁ ∧ e₁ ≤ min (q - e₂) (24 - 2 * e₂)) := by
      ext e₁; simp only [Finset.mem_filter, Finset.mem_range, jetIdx]; omega
    rw [heq, card_range_filter_Icc 25 0 (min (q - e₂) (24 - 2 * e₂)) (by omega)]
    omega
  · have heq : (Finset.range 25).filter (fun e₁ => e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) = ∅ := by
      ext e₁; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, jetIdx]; omega
    rw [heq, Finset.card_empty]

private theorem columnCount2_61 (t q : ℕ) :
    PoleMoment2Jet.columnCount2 (shape2_m59 399) t q = colCount61 t q := by
  rw [PoleMoment2Jet.columnCount2, PoleMoment2Jet.colSlots2, PoleMoment2Jet.gradeSlots2,
    Finset.filter_filter, Finset.card_filter, Finset.sum_product_right, colCount61,
    ← finset_sum_range_eq_natSum]
  change ∑ e₂ ∈ Finset.range 11,
      (∑ e₁ ∈ Finset.range 25,
        if (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsCol (shape2_m59 399) t q e₁ e₂ then 1 else 0) = _
  apply Finset.sum_congr rfl; intro e₂ he₂
  have he₂' : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  rw [← Finset.card_filter]
  split_ifs with hcond
  · have heq :
        (Finset.range 25).filter (fun e₁ =>
          (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsCol (shape2_m59 399) t q e₁ e₂) =
        (Finset.range 25).filter (fun e₁ =>
          (24 - t - 2 * e₂) ≤ e₁ ∧ e₁ ≤ min (min (q - e₂) (24 - 2 * e₂)) (127 - t - 2 * e₂)) := by
      ext e₁
      simp only [Finset.mem_filter, Finset.mem_range, PoleMoment2Jet.IsCol, shape2_m59, jetIdx]
      omega
    rw [heq, card_range_filter_Icc 25 _ _ (by omega)]
  · have heq :
        (Finset.range 25).filter (fun e₁ =>
          (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsCol (shape2_m59 399) t q e₁ e₂) = ∅ := by
      ext e₁
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
        PoleMoment2Jet.IsCol, shape2_m59, jetIdx]
      omega
    rw [heq, Finset.card_empty]

private theorem pivotCount2_61 (t q : ℕ) :
    PoleMoment2Jet.pivotCount2 (shape2_m59 399) t q = pivCount61 t q := by
  rw [PoleMoment2Jet.pivotCount2, PoleMoment2Jet.pivotSlots2, PoleMoment2Jet.gradeSlots2,
    Finset.filter_filter, Finset.card_filter, Finset.sum_product_right, pivCount61,
    ← finset_sum_range_eq_natSum]
  change ∑ e₂ ∈ Finset.range 11,
      (∑ e₁ ∈ Finset.range 25,
        if (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsPivot (shape2_m59 399) t q e₁ e₂ then 1 else 0) = _
  apply Finset.sum_congr rfl; intro e₂ he₂
  have he₂' : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  rw [← Finset.card_filter]
  split_ifs with hcond
  · have heq :
        (Finset.range 25).filter (fun e₁ =>
          (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsPivot (shape2_m59 399) t q e₁ e₂) =
        (Finset.range 25).filter (fun e₁ =>
          (24 - t - 2 * e₂) ≤ e₁ ∧ e₁ ≤ min (min (q - e₂) (24 - 2 * e₂)) (127 - t - q - 2 * e₂)) := by
      ext e₁
      simp only [Finset.mem_filter, Finset.mem_range, PoleMoment2Jet.IsPivot,
        PoleMoment2Jet.IsCol, PoleMoment2Jet.IsRow, shape2_m59, jetIdx]
      omega
    rw [heq, card_range_filter_Icc 25 _ _ (by omega)]
  · have heq :
        (Finset.range 25).filter (fun e₁ =>
          (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsPivot (shape2_m59 399) t q e₁ e₂) = ∅ := by
      ext e₁
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
        PoleMoment2Jet.IsPivot, PoleMoment2Jet.IsCol, PoleMoment2Jet.IsRow, shape2_m59, jetIdx]
      omega
    rw [heq, Finset.card_empty]

theorem groupedPoleMoment2_m59_le : groupedPoleMoment2 (shape2_m59 399) ≤ 9858694 := by
  have hsum_le : groupedPoleMoment2 (shape2_m59 399) ≤ ∑ t ∈ Finset.range 128, offsetUpper61 t := by
    rw [groupedPoleMoment2]
    change ∑ t ∈ Finset.range 128, PoleMoment2Jet.offsetMoment2 (shape2_m59 399) t ≤ _
    apply Finset.sum_le_sum
    intro t ht
    rw [PoleMoment2Jet.offsetMoment2, PoleMoment2Jet.largestGradeSum2]
    have hmem : optK61 t ∈ Finset.range ((shape2_m59 399).B + 1) :=
      Finset.mem_range.mpr (optK61_lt_81 ⟨t, Finset.mem_range.mp ht⟩)
    refine (Nat.sub_le_sub_right (Finset.inf'_le _ hmem) _).trans ?_
    simp_rw [columnCount2_61, pivotCount2_61]
    change (∑ q ∈ Finset.range 81, pivCount61 t q) * optK61 t +
        ∑ q ∈ Finset.range 81, (q - optK61 t) * colCount61 t q -
        ∑ q ∈ Finset.range 81, q * pivCount61 t q ≤ offsetUpper61 t
    simp only [finset_sum_range_eq_natSum, offsetUpper61]
    exact le_rfl
  refine hsum_le.trans ?_
  rw [finset_sum_range_eq_natSum, offsetUpper_val]

theorem poleRows2_m59 : poleRows2 (shape2_m59 399) = 662695 := by
  rw [poleRows2]
  simp_rw [gradeSlots2_card_61]
  dsimp only [shape2_m59]
  rw [finset_sum_range_eq_natSum]
  exact poleRows2_nat_val

private theorem sum_boxPos2_eq (f : ℕ × ℕ × ℕ → ℕ) :
    ∑ m ∈ boxPos2, f m =
      ∑ e₂ ∈ Finset.range 11, ∑ e₁ ∈ Finset.range (25 - 2 * e₂),
        ∑ e₀ ∈ Finset.range (81 - e₁ - e₂), f (e₂, e₁, e₀) := by
  rw [boxPos2, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl; intro e₂ he₂
  have he₂' : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  rw [Finset.sum_product]
  have h1 : ∀ e₁ ∈ Finset.range 25,
      (∑ e₀ ∈ Finset.range 81, if e₀ + e₁ + e₂ ≤ 80 ∧ jetIdx e₁ e₂ ≤ 24 ∧ e₂ ≤ 10 then f (e₂, e₁, e₀) else 0) =
      if e₁ < 25 - 2 * e₂ then ∑ e₀ ∈ Finset.range (81 - e₁ - e₂), f (e₂, e₁, e₀) else 0 := by
    intro e₁ he₁
    split_ifs with hlt
    · rw [← Finset.sum_filter]
      have heq : (Finset.range 81).filter (fun e₀ => e₀ + e₁ + e₂ ≤ 80 ∧ jetIdx e₁ e₂ ≤ 24 ∧ e₂ ≤ 10) =
          Finset.range (81 - e₁ - e₂) := by
        ext e₀; simp only [Finset.mem_filter, Finset.mem_range, jetIdx]; omega
      rw [heq]
    · apply Finset.sum_eq_zero; intro e₀ _
      rw [ite_eq_right_iff]; intro hc; exfalso; simp only [jetIdx] at hc; omega
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have heq : (Finset.range 25).filter (fun e₁ => e₁ < 25 - 2 * e₂) = Finset.range (25 - 2 * e₂) := by
    ext e₁; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [heq]

private theorem boxPos2_moments :
    boxPos2.card = 11385 ∧
    (∑ m ∈ boxPos2, (m.2.2 + m.2.1 + m.1)) = 521345 ∧
    (∑ m ∈ boxPos2, jetIdx m.2.1 m.1) = 173635 ∧
    (∑ m ∈ boxPos2, (m.2.1 + m.1)) = 131890 ∧
    (∑ m ∈ boxPos2, (80 + 24 - (m.2.2 + m.2.1 + m.1))) = 662695 := by
  have hcard : boxPos2.card = 11385 := by
    rw [Finset.card_eq_sum_ones, sum_boxPos2_eq]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, finset_sum_range_eq_natSum]
    exact box_card_val
  have hq : (∑ m ∈ boxPos2, (m.2.2 + m.2.1 + m.1)) = 521345 := by
    rw [sum_boxPos2_eq]
    have hinner : ∀ e₂ ∈ Finset.range 11, ∀ e₁ ∈ Finset.range (25 - 2 * e₂),
        (∑ e₀ ∈ Finset.range (81 - e₁ - e₂), (e₀ + e₁ + e₂)) =
        (81 - e₁ - e₂) * (81 - e₁ - e₂ - 1) / 2 + (81 - e₁ - e₂) * (e₁ + e₂) := by
      intro e₂ _ e₁ _
      have : ∀ e₀, e₀ + e₁ + e₂ = e₀ + (e₁ + e₂) := fun _ => Nat.add_assoc _ _ _
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hsum : (∑ e₂ ∈ Finset.range 11, ∑ e₁ ∈ Finset.range (25 - 2 * e₂),
          ∑ e₀ ∈ Finset.range (81 - e₁ - e₂), (e₀ + e₁ + e₂)) =
        natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ =>
          (81 - e₁ - e₂) * (81 - e₁ - e₂ - 1) / 2 + (81 - e₁ - e₂) * (e₁ + e₂))) := by
      rw [← finset_sum_range_eq_natSum]
      apply Finset.sum_congr rfl; intro e₂ he₂
      rw [← finset_sum_range_eq_natSum]
      exact Finset.sum_congr rfl (hinner e₂ he₂)
    rw [hsum]; exact box_q_val
  have hv : (∑ m ∈ boxPos2, jetIdx m.2.1 m.1) = 173635 := by
    rw [sum_boxPos2_eq]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, jetIdx, finset_sum_range_eq_natSum]
    exact box_v_val
  have h12 : (∑ m ∈ boxPos2, (m.2.1 + m.1)) = 131890 := by
    rw [sum_boxPos2_eq]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, finset_sum_range_eq_natSum]
    exact box_12_val
  have hp : (∑ m ∈ boxPos2, (80 + 24 - (m.2.2 + m.2.1 + m.1))) = 662695 := by
    have hadd : (∑ m ∈ boxPos2, (80 + 24 - (m.2.2 + m.2.1 + m.1))) +
        (∑ m ∈ boxPos2, (m.2.2 + m.2.1 + m.1)) = ∑ _m ∈ boxPos2, (80 + 24) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro m hm
      have hbox := mem_boxPos2.mp hm
      omega
    rw [Finset.sum_const, smul_eq_mul, hcard, hq] at hadd
    have hsub : ∀ x : ℕ, x + 521345 = 11385 * (80 + 24) → x = 662695 := by omega
    exact hsub _ hadd
  exact ⟨hcard, hq, hv, h12, hp⟩

private theorem finrank_ambient2_m59_ge (h : ℕ) (hlo : 2368 ≤ h) (hhi : h ≤ 2401) :
    let N := 59 * 179798
    triangle 399 * (N * 11385 + 173635 - (131071 - h) * 521345) + poleCredit2 h (shape2_m59 399) ≤
      Module.finrank L (ambient2 h (shape2_m59 399) (N - 1)) := by
  intro N
  rw [TwoJetCaseAKernel.finrank_ambient2_eq]
  -- Count `eligibleCoords h (shape2_m59 399) (N - 1)` by fibering over `(m ∈ boxPos2, e ∈ seedExpsU 399, a ≤ bound)`!
  let s := shape2_m59 399
  let M := (N - 1) + (s.B + s.J) * (2 * h) + s.J
  let width (m : ℕ × ℕ × ℕ) : ℕ :=
    N + (s.B + s.J) * (2 * h) + jetIdx m.2.1 m.1 - (m.2.2 + m.2.1 + m.1) * (131071 + h)
  -- Build explicit injection from `(m : boxPos2) × (e : seedExpsU 399) × Fin (width m.1)` into `eligibleCoords`!
  let f : (Σ m : boxPos2, seedExpsU 399 × Fin (width m.1)) →
      TwoJetCaseAKernel.CoeffBox2 s.B M s.U := fun ⟨⟨⟨e₂, e₁, e₀⟩, hm⟩, ⟨e, he⟩, ⟨a, ha⟩⟩ =>
    have hbox := mem_boxPos2.mp hm
    have hse := mem_seedExpsU.mp he
    have haM : a ≤ M := by
      dsimp only [width, M, s, shape2_m59, jetIdx] at ha hbox ⊢; omega
    have hej (j : Fin 2) : e j ≤ 399 := by
      apply le_trans _ hse
      rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    (⟨e₂, by dsimp only [s, shape2_m59] at hbox ⊢; omega⟩,
     ⟨e₁, by dsimp only [s, shape2_m59] at hbox ⊢; omega⟩,
     ⟨e₀, by dsimp only [s, shape2_m59] at hbox ⊢; omega⟩,
     ⟨a, by omega⟩,
     fun j => ⟨e j, by have := hej j; dsimp only [s, shape2_m59]; omega⟩)
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨⟨e₂, e₁, e₀⟩, hm⟩, ⟨e, he⟩, ⟨a, ha⟩⟩ ⟨⟨⟨e₂', e₁', e₀'⟩, hm'⟩, ⟨e', he'⟩, ⟨a', ha'⟩⟩ hfeq
    simp only [f, Prod.mk.injEq, Fin.ext_iff] at hfeq
    obtain ⟨rfl, rfl, rfl, rfl, heeq⟩ := hfeq
    have he_eq : e = e' := by
      ext j
      have := congrFun heeq j
      simpa [Fin.ext_iff] using this
    subst he_eq
    rfl
  have hf_mem : ∀ x, f x ∈ TwoJetCaseAKernel.eligibleCoords h s (N - 1) := by
    rintro ⟨⟨⟨e₂, e₁, e₀⟩, hm⟩, ⟨e, he⟩, ⟨a, ha⟩⟩
    rw [TwoJetCaseAKernel.eligibleCoords, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hbox := mem_boxPos2.mp hm
    have hse := mem_seedExpsU.mp he
    have hbox_e : TwoJetCaseAKernel.boxExp (f ⟨⟨(e₂, e₁, e₀), hm⟩, ⟨e, he⟩, ⟨a, ha⟩⟩).2.2.2.2 = e := by
      ext j; simp [TwoJetCaseAKernel.boxExp, f]
    rw [hbox_e]
    refine ⟨hbox.1, hbox.2.1, hbox.2.2, hse, ?_⟩
    have hpos_w : (e₀ + e₁ + e₂) * (131071 + h) ≤ N + (s.B + s.J) * (2 * h) + jetIdx e₁ e₂ := by
      dsimp only [N, s, shape2_m59, jetIdx] at hbox ⊢
      have hmul_le : (e₀ + e₁ + e₂) * (131071 + h) ≤ 80 * (131071 + h) := Nat.mul_le_mul_right _ hbox.1
      omega
    dsimp only [f, width] at ha ⊢
    omega
  have hcard_le : Fintype.card (Σ m : boxPos2, seedExpsU 399 × Fin (width m.1)) ≤
      (TwoJetCaseAKernel.eligibleCoords h s (N - 1)).card := by
    have := Fintype.card_le_of_injective
      (fun x => (⟨f x, hf_mem x⟩ : TwoJetCaseAKernel.eligibleCoords h s (N - 1)))
      (fun x y hxy => hf_inj (congrArg Subtype.val hxy))
    simpa only [Fintype.card_coe] using this
  -- Evaluate `Fintype.card (Σ m : boxPos2, seedExpsU 399 × Fin (width m.1))`!
  have hcard_eq : Fintype.card (Σ m : boxPos2, seedExpsU 399 × Fin (width m.1)) =
      triangle 399 * ∑ m ∈ boxPos2, width m := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_coe, card_seedExpsU, Fintype.card_fin]
    rw [← Finset.mul_sum, Finset.sum_coe_sort]
  have hsum_width : ∑ m ∈ boxPos2, width m =
      (N * 11385 + 173635 - (131071 - h) * 521345) + 2 * h * 662695 := by
    have hterm (m : ℕ × ℕ × ℕ) (hm : m ∈ boxPos2) :
        width m + (m.2.2 + m.2.1 + m.1) * (131071 - h) =
          N + jetIdx m.2.1 m.1 + 2 * h * (80 + 24 - (m.2.2 + m.2.1 + m.1)) := by
      have hbox := mem_boxPos2.mp hm
      dsimp only [width, s, shape2_m59, N, jetIdx] at hbox ⊢
      have hmul : (m.2.2 + m.2.1 + m.1) * (131071 + h) =
          (m.2.2 + m.2.1 + m.1) * (131071 - h) + 2 * h * (m.2.2 + m.2.1 + m.1) := by
        have h1 : 131071 + h = (131071 - h) + 2 * h := by omega
        rw [h1, Nat.mul_add]; ring
      have h2 : 2 * h * (80 + 24 - (m.2.2 + m.2.1 + m.1)) + 2 * h * (m.2.2 + m.2.1 + m.1) =
          (80 + 24) * (2 * h) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega : m.2.2 + m.2.1 + m.1 ≤ 80 + 24), mul_comm]
      have hmul_le : (m.2.2 + m.2.1 + m.1) * (131071 + h) ≤ 80 * (131071 + h) :=
        Nat.mul_le_mul_right _ hbox.1
      omega
    have hsum := Finset.sum_congr rfl hterm
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hsum
    obtain ⟨hc, hq, hv, _, hp⟩ := boxPos2_moments
    rw [hc, hq, hv, ← Finset.mul_sum, hp] at hsum
    have hcomm : 521345 * (131071 - h) = (131071 - h) * 521345 := mul_comm _ _
    have hN : 11385 * N = N * 11385 := mul_comm _ _
    omega
  rw [hcard_eq, hsum_width, Nat.mul_add] at hcard_le
  have hpc : poleCredit2 h (shape2_m59 399) = triangle 399 * (2 * h * 662695) := by
    rw [poleCredit2, poleRows2_m59, mul_assoc]; rfl
  rw [hpc]
  exact hcard_le

private theorem sum_highPos2_card_le (h : ℕ) (hlo : 2368 ≤ h) (hhi : h ≤ 2401) :
    let N := 59 * 179798
    (∑ W ∈ Finset.range N, (highPos2 h W ((N - 1 - W) / (3 * h))).card) +
      (N * 11385 + 173635 - 131071 * 521345 + h * 125675) ≤
      N * 11385 + 173635 - (131071 - h) * 521345 := by
  intro N
  -- Swap sum over `W ∈ range N` and `m ∈ boxPos2`!
  have hswap : ∑ W ∈ Finset.range N, (highPos2 h W ((N - 1 - W) / (3 * h))).card =
      ∑ m ∈ boxPos2, ((Finset.range N).filter fun W =>
        (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧
        (N - 1 - W) / (3 * h) < m.2.1 + m.1).card := by
    simp only [highPos2, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  -- For each `m ∈ boxPos2`, the inner count is at most `3 * h * (m.2.1 + m.1)`!
  have hper (m : ℕ × ℕ × ℕ) (hm : m ∈ boxPos2) :
      ((Finset.range N).filter fun W =>
        (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧
        (N - 1 - W) / (3 * h) < m.2.1 + m.1).card ≤
      3 * h * (m.2.1 + m.1) := by
    have hsub : ((Finset.range N).filter fun W =>
        (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧
        (N - 1 - W) / (3 * h) < m.2.1 + m.1) ⊆
      (Finset.range (3 * h * (m.2.1 + m.1))).image (fun t => N - 1 - t) := by
      intro W hW
      obtain ⟨hWN, _, hdiv⟩ := Finset.mem_filter.mp hW
      have hWN' : W < N := Finset.mem_range.mp hWN
      have h3h : 0 < 3 * h := by omega
      have hlt : N - 1 - W < 3 * h * (m.2.1 + m.1) := by
        by_contra hge
        push_neg at hge
        have hq : m.2.1 + m.1 ≤ (N - 1 - W) / (3 * h) :=
          (Nat.le_div_iff_mul_le h3h).mpr (by simpa [mul_comm] using hge)
        omega
      exact Finset.mem_image.mpr ⟨N - 1 - W, Finset.mem_range.mpr hlt, by omega⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  have hsum_le : ∑ m ∈ boxPos2, ((Finset.range N).filter fun W =>
      (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧
      (N - 1 - W) / (3 * h) < m.2.1 + m.1).card ≤ 3 * h * 131890 := by
    calc
      _ ≤ ∑ m ∈ boxPos2, 3 * h * (m.2.1 + m.1) := Finset.sum_le_sum hper
      _ = 3 * h * ∑ m ∈ boxPos2, (m.2.1 + m.1) := (Finset.mul_sum _ _ _).symm
      _ = 3 * h * 131890 := by rw [boxPos2_moments.2.2.2.1]
  have hNval : N = 10608082 := rfl
  have hsub1 : (131071 - h) * 521345 + h * 521345 = 131071 * 521345 := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  omega

/-! ## 5. End-to-End Case-A Avoidance Theorem at `69.61` (`caseA_avoidance_6961`) -/

def alpha1 (G : Jet) : EField :=
  -(seedsY0ToE (G.coeff 0)) / seedsY0ToE (G.coeff 1)

def evJetAt (G : Jet) : Jet →+* EField :=
  Polynomial.eval₂RingHom seedsY0ToE (alpha1 G)

def alpha2 (G : Jet) : EField :=
  -(evJetAt G (prolongB1 G)) / evJetAt G (prolongA G)

theorem caseA_avoidance_6961 {h : ℕ} (hlo : 2368 ≤ h) (hhi : h ≤ 2401)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {G : Jet} (hdegG : G.natDegree = 1)
    (hdet : jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) ≠ 0) :
    ∃ W < 59 * 179798, ∃ P₀ ∈ complete2 Crt word (shape2_m59 399) W,
      ¬ G ∣ prolongSubst (prolongA G) (prolongB1 G) 10 (centerEval2 P₀) := by
  let s := shape2_m59 399
  let N := 59 * 179798
  let φ : BaseRing →+* EField := algebraMap BaseRing EField
  have hφ : Function.Injective φ := IsFractionRing.injective BaseRing EField
  have hcharE : CharP EField K1.p := by
    have h2 : ∀ n : ℕ, (n : EField) = 0 ↔ K1.p ∣ n := by
      intro n
      have hcast : (n : EField) = φ (Polynomial.C (Polynomial.C (MvPolynomial.C (n : L)))) := by
        simp [φ]
      rw [hcast, show (0 : EField) = φ 0 from (map_zero φ).symm, hφ.eq_iff,
        Polynomial.C_eq_zero, Polynomial.C_eq_zero, MvPolynomial.C_eq_zero]
      exact CharP.cast_eq_zero_iff L K1.p n
    exact ⟨h2⟩
  have hA1_ne : G.coeff 1 ≠ 0 := by
    rw [← hdegG, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (fun hz => by rw [hz, Polynomial.natDegree_zero] at hdegG; omega)
  have hA_ne : seedsY0ToE (G.coeff 1) ≠ 0 := fun hz =>
    hA1_ne (seedsY0ToE_injective (hz.trans (map_zero _).symm))
  have h2_ne : (2 : EField) ≠ 0 := by
    intro h2
    have hdvd : K1.p ∣ 2 := (CharP.cast_eq_zero_iff EField K1.p 2).mp (by simpa using h2)
    have hle := Nat.le_of_dvd (by decide) hdvd
    change 2130706433 ≤ 2 at hle
    omega
  have hG0 : evJetAt G G = 0 := by
    have hlin : G = Polynomial.C (G.coeff 0) + Polynomial.C (G.coeff 1) * Polynomial.X := by
      ext n
      cases n with
      | zero => simp
      | succ n =>
        cases n with
        | zero => simp
        | succ n =>
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < n + 2)]
          simp [Polynomial.coeff_C, Polynomial.coeff_X]
    conv_lhs => arg 2; rw [hlin]
    rw [map_add, map_mul]
    simp only [evJetAt, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X, alpha1]
    rw [mul_div_cancel₀ _ hA_ne, add_neg_cancel]
  have hAne : evJetAt G (prolongA G) ≠ 0 := by
    simp only [prolongA, map_mul, map_ofNat, evJetAt, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact mul_ne_zero h2_ne hA_ne
  have hG1 : evJetAt G (prolongA G) * alpha2 G + evJetAt G (prolongB1 G) = 0 := by
    dsimp only [alpha2]
    rw [mul_div_cancel₀ _ hAne, neg_add_cancel]
  by_contra hnone
  push_neg at hnone
  -- Every `Q ∈ complete2 Crt word s W'` (`W' < N`) vanishes at `(alpha1 G, alpha2 G)`!
  have hall : ∀ W' < N, ∀ Q ∈ complete2 Crt word s W',
      polyBivar (shift2 (alpha1 G) (alpha2 G) (embed2 φ Q)) 0 0 = 0 := fun W' hW' Q hQ =>
    eval_zero_of_prolongSubst_dvd φ (evJetAt G) (alpha1 G) (alpha2 G)
      (jet2ToE_eval₂_comm (alpha1 G) (alpha2 G)) hG0 hAne hG1 hQ.1.1 (hnone W' hW' Q hQ)
  -- For each `W < N`, let `k W = (N - 1 - W) / (3 * h)`. Then `boundedShiftExp s 1 = 3`!
  have hbse : boundedShiftExp s 1 = 3 := by decide
  let k (W : ℕ) : ℕ := (N - 1 - W) / (3 * h)
  have hWk : ∀ W < N, W + k W * (boundedShiftExp s 1 * h) < N := by
    intro W hW
    rw [hbse]
    have hmul : k W * (3 * h) ≤ N - 1 - W := by
      rw [mul_comm]
      exact Nat.mul_div_le (N - 1 - W) (3 * h)
    omega
  have hk : ∀ W < N, k W < K1.p := by
    intro W hW
    have hle : k W ≤ N - 1 - W := Nat.div_le_self _ _
    change k W < 2130706433
    dsimp only [N] at hle
    omega
  -- Hence every `Q ∈ complete2 Crt word s W` vanishes to order `> k W` at `(alpha1 G, alpha2 G)`!
  have hord : ∀ W < N, ∀ Q ∈ complete2 Crt word s W,
      ∀ a b, a + b ≤ k W → polyBivar (shift2 (alpha1 G) (alpha2 G) (embed2 φ Q)) a b = 0 := by
    intro W hW Q hQ
    have hvan := wordVanishes_of_all_complete2_eval_zero Crt word s N hφ
      fractionRingFieldDerivs_compat (alpha1 G) (alpha2 G) hall (hWk W hW) hQ
    exact pow_collapse_of_wordVanishes fractionRingFieldDerivs hdet (k W) (hk W hW) hvan
  -- Chain `finrank_ambient2_m59_ge` ≤ `physRank2_m59` ≤ `pole_bound_2jet` ≤ `telescope2` ≤ `finrank_FX_vanishOrder_le`!
  have hamb := finrank_ambient2_m59_ge h hlo hhi
  have hphys := physRank2_m59 h 399 (N - 1) word
  have hpole := pole_bound_2jet (by omega : 0 < h) (by change h < 2130706433; omega) Crt word s (N - 1)
  have htele := telescope2 (by omega : 0 < h) (by omega : h ≤ 131068) Crt word s (N - 1)
  have hN_eq : (N - 1) + 1 = N := rfl
  rw [hN_eq] at htele
  have hsum_fx : ∑ W ∈ Finset.range N, Module.finrank FX (evaluated2 Crt word s W) ≤
      triangle 399 * ∑ W ∈ Finset.range N, (highPos2 h W (k W)).card := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro W hW
    exact finrank_FX_vanishOrder_le (by omega) (by omega) Crt word (alpha1 G) (alpha2 G)
      (hord W (Finset.mem_range.mp hW))
  have hhigh := sum_highPos2_card_le h hlo hhi
  have hhigh_mul := Nat.mul_le_mul_left (triangle 399) hhigh
  rw [Nat.mul_add] at hhigh_mul
  have hgpm : groupedPoleMoment2 s ≤ 9858694 := groupedPoleMoment2_m59_le
  have htri : triangle 399 = 80200 := by decide
  -- Pure linear arithmetic in `h ∈ [2368, 2401]` gives contradiction!
  dsimp only [s, N] at hamb hphys hpole htele hsum_fx hhigh_mul hgpm
  have hmul_gpm : 2 * h * ((shape2_m59 399).U + 1) * groupedPoleMoment2 (shape2_m59 399) ≤
      2 * h * 400 * 9858694 := by
    dsimp only [shape2_m59]
    exact Nat.mul_le_mul_left _ hgpm
  rw [htri] at hamb hphys hsum_fx hhigh_mul
  dsimp only [k, N] at hsum_fx
  omega

#print axioms seedsY0ToE_injective
#print axioms prolongSubst_rowCaps
#print axioms finrank_FX_vanishOrder_le
#print axioms caseA_avoidance_6961

end
end TwoJetCaseAFX

end Merged_TwoJetCaseAFX
