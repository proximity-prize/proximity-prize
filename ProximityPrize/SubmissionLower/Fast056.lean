import ProximityPrize.SubmissionLower.Fast000
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Fast022
import ProximityPrize.SubmissionLower.Numeric6AuxCert
import ProximityPrize.SubmissionLower.Numeric5Certificate
import ProximityPrize.SubmissionLower.Fast049
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast019
import ProximityPrize.SubmissionLower.Fast020
import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
set_option Elab.async false

section PackSource_K1_13_1_1BudgetE
set_option autoImplicit true
namespace K1_13_1_1

set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000

open private activeNatCount_eq sumRange_prefix innerSlice_eq sumToCap_eq sumRange_suffix
  sumRange_congr sumRange_zero natLine_zero from ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic

-- All grades in this certificate have residual degree 48. Remove the two
-- cutoff-dependent starting indices to expose a sum with a fixed domain.
private def budgetERaw (lo o : ℕ) : ℕ :=
  sumRange 49 fun b =>
    min (natPairs 48 lo b) (sumRange (48 - b + 1) (natLine 48 lo o b))

private def budgetERawEval (lo o : ℕ) : ℕ :=
  let startB := 49 - o
  sumRange (49 - startB) fun i =>
    let b := i + startB
    let startC := 2 * (48 - b) + 1 - o
    sumToCap (natLine 48 lo o b) (48 - b + 1 - startC) startC (natPairs 48 lo b)

private theorem budgetERaw_eq_eval (lo o : ℕ) :
    budgetERaw lo o = budgetERawEval lo o := by
  unfold budgetERaw budgetERawEval
  rw [sumRange_suffix 49 (49 - o) _ (Nat.sub_le _ _)]
  · apply sumRange_congr
    intro i hi
    exact (innerSlice_eq 48 lo o (i + (49 - o)) (by omega)).symm
  · intro b hb
    have hzero : sumRange (48 - b + 1) (natLine 48 lo o b) = 0 := by
      apply sumRange_zero
      intro c hc
      exact natLine_zero 48 lo o b c (by omega) (by omega)
    simp [hzero]

private theorem budgetEFull (s r : ℕ) (hs : 62 ≤ s ∧ s ≤ 74) (hr : s + r < 138) :
    fastPascal s r =
      min (activeNatCount 48 (48 - r) 48) (budgetERaw (48 - r) (138 - (s + r))) := by
  have hd : residualDegree s = 48 := by unfold residualDegree; omega
  have hh : min 48 (137 - r) = 48 := by omega
  rw [fastPascal, hd, hh, sumToCap_eq, budgetERaw_eq_eval]
  rfl

private theorem budgetERangeMono (n : ℕ) {f g : ℕ → ℕ} (h : ∀ i, f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.add_le_add ih (h n)

-- The uncapped sum decreases as the lower index rises and increases with
-- the contact order. Both comparisons hold pointwise on the fixed domain.
private theorem budgetERawMono {l₁ l₂ o₁ o₂ : ℕ} (hl : l₂ ≤ l₁) (ho : o₁ ≤ o₂) :
    budgetERaw l₁ o₁ ≤ budgetERaw l₂ o₂ := by
  apply budgetERangeMono
  intro b
  apply min_le_min
  · apply budgetERangeMono
    intro f
    omega
  · apply budgetERangeMono
    intro c
    unfold natLine
    dsimp only
    have hf : (l₂ - (b + 2 * min c 24) + 2) / 3 ≤
        (l₁ - (b + 2 * min c 24) + 2) / 3 := by omega
    apply min_le_min
    · exact Nat.sub_le_sub_left hf _
    · apply Nat.sub_le_sub_left
      apply max_le_max hf
      omega

private theorem budgetETableSpan {P : ℕ → Prop} (n k : ℕ) (pre : ∀ i < n, P i)
    (more : ∀ j : Fin k, P (n + j.val)) : ∀ i < n + k, P i := by
  intro i h
  by_cases hi : i < n
  · exact pre i hi
  · have hit := more ⟨i - n, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : n ≤ i)] using hit

private theorem budgetETableEmpty {P : ℕ → Prop} : ∀ i < 0, P i :=
  fun i hi => (Nat.not_lt_zero i hi).elim

-- Sum of the positive terms in the progression t, t - 2, t - 4, ...
private def budgetEHalf (t : ℕ) : ℕ := ((t + 1) / 2) * ((t + 2) / 2)

private theorem budgetEHalfStep (t : ℕ) : budgetEHalf (t + 2) = budgetEHalf t + (t + 2) := by
  unfold budgetEHalf
  rw [show (t + 2 + 1) / 2 = (t + 1) / 2 + 1 by omega, show (t + 2 + 2) / 2 = (t + 2) / 2 + 1 by omega]
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

private theorem budgetEHalfDrop (t : ℕ) : t + budgetEHalf (t - 2) = budgetEHalf t := by
  rcases t with _ | t
  · rfl
  rcases t with _ | t
  · rfl
  exact (Nat.add_comm _ _).trans (budgetEHalfStep t).symm

private theorem budgetEHalfSum (t n : ℕ) (h : t ≤ 2 * n) :
    sumRange n (fun c => t - 2 * c) = budgetEHalf t := by
  have aux (k : ℕ) : sumRange k (fun c => t - 2 * c) + budgetEHalf (t - 2 * k) = budgetEHalf t := by
    induction k with
    | zero => simp [sumRange]
    | succ k ih =>
      change (sumRange k _ + (t - 2 * k)) + budgetEHalf (t - 2 * (k + 1)) = _
      rw [Nat.add_assoc, show t - 2 * (k + 1) = (t - 2 * k) - 2 by omega, budgetEHalfDrop, ih]
  simpa only [Nat.sub_eq_zero_of_le h, show budgetEHalf 0 = 0 by rfl, Nat.add_zero] using aux n

private theorem budgetESubSum (n : ℕ) (f g : ℕ → ℕ) (h : ∀ i, g i ≤ f i) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  have aux : sumRange n (fun i => f i - g i) + sumRange n g = sumRange n f := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (sumRange n _ + (f n - g n)) + (sumRange n g + g n) = sumRange n f + f n
      have := h n
      omega
  omega

private def budgetEBandShort (d lo top : ℕ) : ℕ :=
  sumRange (min d top + 1) fun f => budgetEHalf (d + 1 - 3 * f) - budgetEHalf (lo - 3 * f)

private theorem budgetEBandShort_eq (d top : ℕ) (lo : ℤ) (hl : lo ≤ (d : ℤ) + 1) :
    bandCount d lo (d : ℤ) top = budgetEBandShort d lo.toNat top := by
  unfold bandCount budgetEBandShort
  apply sumRange_congr
  intro f hf
  have hfd : f ≤ d := by omega
  let n := min (d - f) (((d : ℤ) - 3 * f) / 2).toNat + 1
  let u := d + 1 - 3 * f
  let l := lo.toNat - 3 * f
  have hlu : l ≤ u := by dsimp only [l, u]; omega
  have hun : u ≤ 2 * n := by dsimp only [u, n]; omega
  have term (c : ℕ) (_ : c < n) :
      intervalSize (max 0 (lo - 2 * c - 3 * f)) (min ((d : ℤ) - f - c) ((d : ℤ) - 2 * c - 3 * f)) =
        (u - 2 * c) - (l - 2 * c) := by
    rw [min_eq_right (by omega : (d : ℤ) - 2 * c - 3 * f ≤ (d : ℤ) - f - c)]
    unfold intervalSize
    dsimp only [u, l]
    omega
  change sumRange n _ = budgetEHalf u - budgetEHalf l
  rw [sumRange_congr n term, budgetESubSum n (fun c => u - 2 * c) (fun c => l - 2 * c) (fun c => by omega),
    budgetEHalfSum u n hun, budgetEHalfSum l n (hlu.trans hun)]

-- The hexadecimal tables store one value per three digits, starting at the right.
private def budgetEActive (i : ℕ) : ℕ :=
  (0xbe1762292d637e4204bd5545e66726f977a7f686c8dd9489aea0ea69abeb0eb59b9fbe0c1dc55c89cb9ce5d0dd32d53d71d8cda4db9dccddcdeadf6e00e08e0fe14e18e1be1de1ee1f >>> (12 * i)) % 4096

private abbrev budgetEActiveEntry (lo : ℕ) : Prop :=
  budgetEBandShort 48 lo 10 = budgetEActive lo ∧
  (20 ≤ lo → budgetEActive lo ≤ 3301) ∧ (30 < lo → budgetEActive lo ≤ 2869)

private theorem budgetEActive8 : ∀ i < 8, budgetEActiveEntry i :=
  budgetETableSpan 0 8 budgetETableEmpty (by decide +kernel)

private theorem budgetEActive16 : ∀ i < 16, budgetEActiveEntry i :=
  budgetETableSpan 8 8 budgetEActive8 (by decide +kernel)

private theorem budgetEActive24 : ∀ i < 24, budgetEActiveEntry i :=
  budgetETableSpan 16 8 budgetEActive16 (by decide +kernel)

private theorem budgetEActive32 : ∀ i < 32, budgetEActiveEntry i :=
  budgetETableSpan 24 8 budgetEActive24 (by decide +kernel)

private theorem budgetEActive40 : ∀ i < 40, budgetEActiveEntry i :=
  budgetETableSpan 32 8 budgetEActive32 (by decide +kernel)

private theorem budgetEActive48 : ∀ i < 48, budgetEActiveEntry i :=
  budgetETableSpan 40 8 budgetEActive40 (by decide +kernel)

private theorem budgetEActive49 : ∀ i < 49, budgetEActiveEntry i :=
  budgetETableSpan 48 1 budgetEActive48 (by decide +kernel)

private theorem budgetEActiveCount (lo : ℕ) (h : lo < 49) :
    activeNatCount 48 lo 48 = budgetEActive lo :=
  (activeNatCount_eq 48 (lo : ℤ) 48 (by decide)).symm.trans
    ((budgetEBandShort_eq 48 10 lo (by omega)).trans (budgetEActive49 lo h).1)

-- Below order 48, on the interval lo ≤ 30, the lower-index restriction
-- drops out of the line lengths. Here x is the residual degree 48 - b.
private def budgetEFreeLine (x o c : ℕ) : ℕ :=
  min 11 (min (x - c + 1) (o + c - 2 * x))

private theorem budgetEClip (a b z : ℕ) : a - (b - z) = min a (a + z - b) := by omega

private theorem budgetEFreeLine_eq (lo o b c : ℕ) (hl : lo ≤ 30) (ho : o ≤ 47)
    (hbc : b + c ≤ 48) : natLine 48 lo o b c = budgetEFreeLine (48 - b) o c := by
  have he : 48 - b - c + 1 - (145 - (3 * b + 2 * c + o)) =
      min (48 - b - c + 1) (o + c - 2 * (48 - b)) := by
    rw [budgetEClip]
    congr 1
    omega
  unfold natLine budgetEFreeLine
  dsimp only
  rw [← he]
  by_cases h : lo ≤ b + 2 * min c 24
  · simp [Nat.sub_eq_zero_of_le h]
  · have hc : min c 24 = c := min_eq_left (by omega)
    rw [hc] at h ⊢
    have hf : (lo - (b + 2 * c) + 2) / 3 ≤ 145 - (3 * b + 2 * c + o) := by omega
    have hm : 48 - b - c + 1 - (145 - (3 * b + 2 * c + o)) ≤ 11 - (lo - (b + 2 * c) + 2) / 3 := by
      omega
    rw [show min (48 : ℕ) 10 + 1 = 11 by decide, max_eq_right hf, min_eq_right hm, min_eq_right (hm.trans (Nat.sub_le 11 _))]

private def budgetEFreeRow (x o : ℕ) : ℕ :=
  sumRange (x + 1) (budgetEFreeLine x o)

private theorem budgetEFreeRow_mono (x : ℕ) {o o' : ℕ} (h : o ≤ o') :
    budgetEFreeRow x o ≤ budgetEFreeRow x o' := by
  apply budgetERangeMono
  intro c
  unfold budgetEFreeLine
  omega

private abbrev budgetECapEntry (b : ℕ) : Prop :=
  budgetEFreeRow (48 - b) 47 ≤ natPairs 48 30 b

private theorem budgetECap8 : ∀ i < 8, budgetECapEntry i :=
  budgetETableSpan 0 8 budgetETableEmpty (by decide +kernel)

private theorem budgetECap16 : ∀ i < 16, budgetECapEntry i :=
  budgetETableSpan 8 8 budgetECap8 (by decide +kernel)

private theorem budgetECap24 : ∀ i < 24, budgetECapEntry i :=
  budgetETableSpan 16 8 budgetECap16 (by decide +kernel)

private theorem budgetECap32 : ∀ i < 32, budgetECapEntry i :=
  budgetETableSpan 24 8 budgetECap24 (by decide +kernel)

private theorem budgetECap40 : ∀ i < 40, budgetECapEntry i :=
  budgetETableSpan 32 8 budgetECap32 (by decide +kernel)

private theorem budgetECap48 : ∀ i < 48, budgetECapEntry i :=
  budgetETableSpan 40 8 budgetECap40 (by decide +kernel)

private theorem budgetECap49 : ∀ i < 49, budgetECapEntry i :=
  budgetETableSpan 48 1 budgetECap48 (by decide +kernel)

private def budgetEFreeSum (o : ℕ) : ℕ :=
  let start := 49 - o
  sumRange (49 - start) fun i => budgetEFreeRow (48 - (i + start)) o

private theorem budgetEFreeSum_eq (lo o : ℕ) (hl : lo ≤ 30) (ho : o ≤ 47) :
    budgetERaw lo o = budgetEFreeSum o := by
  unfold budgetERaw budgetEFreeSum
  have hrows : ∀ b < 49, min (natPairs 48 lo b) (sumRange (48 - b + 1) (natLine 48 lo o b))
      = budgetEFreeRow (48 - b) o := by
    intro b hb
    have he : sumRange (48 - b + 1) (natLine 48 lo o b) = budgetEFreeRow (48 - b) o :=
      sumRange_congr _ (fun c hc => budgetEFreeLine_eq lo o b c hl ho (by omega))
    rw [he]
    apply min_eq_right
    have hp : natPairs 48 30 b ≤ natPairs 48 lo b := by
      apply budgetERangeMono
      intro f
      omega
    exact (budgetEFreeRow_mono _ ho).trans ((budgetECap49 b hb).trans hp)
  rw [sumRange_congr 49 hrows]
  apply sumRange_suffix _ _ _ (Nat.sub_le _ _)
  intro b hb
  apply sumRange_zero
  intro c hc
  unfold budgetEFreeLine
  omega

private def budgetEOrder (i : ℕ) : ℕ :=
  (0xca9bf6b49aa19ff9628cb8397ad7266a56295b35424d74714113b63613112c628023f2021ca19616613a1120ed0cc0ae09307b06605304303502901f01701000b007004002001000 >>> (12 * i)) % 4096

private abbrev budgetEOrderEntry (o : ℕ) : Prop :=
  budgetEFreeSum o = budgetEOrder o

private theorem budgetEOrder8 : ∀ i < 8, budgetEOrderEntry i :=
  budgetETableSpan 0 8 budgetETableEmpty (by decide +kernel)

private theorem budgetEOrder16 : ∀ i < 16, budgetEOrderEntry i :=
  budgetETableSpan 8 8 budgetEOrder8 (by decide +kernel)

private theorem budgetEOrder24 : ∀ i < 24, budgetEOrderEntry i :=
  budgetETableSpan 16 8 budgetEOrder16 (by decide +kernel)

private theorem budgetEOrder32 : ∀ i < 32, budgetEOrderEntry i :=
  budgetETableSpan 24 8 budgetEOrder24 (by decide +kernel)

private theorem budgetEOrder40 : ∀ i < 40, budgetEOrderEntry i :=
  budgetETableSpan 32 8 budgetEOrder32 (by decide +kernel)

private theorem budgetEOrder48 : ∀ i < 48, budgetEOrderEntry i :=
  budgetETableSpan 40 8 budgetEOrder40 (by decide +kernel)

private theorem budgetERawHighLo : 2869 ≤ budgetERaw 48 47 := by
  rw [budgetERaw_eq_eval]
  decide +kernel

private theorem budgetERawHighOrder : 3301 ≤ budgetERaw 30 48 := by
  rw [budgetERaw_eq_eval]
  decide +kernel

-- In the two high ranges the active count already caps the Pascal sum.
-- The other cells use the order table on the free lines.
private def budgetEPascalValue (lo o : ℕ) : ℕ :=
  if 30 < lo ∨ 47 < o then budgetEActive lo else min (budgetEActive lo) (budgetEOrder o)

private theorem budgetEPascal_eq (s r : ℕ) (hs : 62 ≤ s ∧ s ≤ 74) (hr : s + r < 138) :
    fastPascal s r = budgetEPascalValue (48 - r) (138 - (s + r)) := by
  rw [budgetEFull s r hs hr]
  let lo := 48 - r
  let o := 138 - (s + r)
  change min (activeNatCount 48 lo 48) (budgetERaw lo o) = budgetEPascalValue lo o
  have hlt : lo < 49 := by dsimp only [lo]; omega
  obtain ⟨_, h20, h31⟩ := budgetEActive49 lo hlt
  rw [budgetEActiveCount lo hlt]
  unfold budgetEPascalValue
  by_cases hl : 30 < lo
  · rw [ite_eq_left (Or.inl hl)]
    have ho : 47 ≤ o := by dsimp only [o, lo] at *; omega
    exact min_eq_left ((h31 hl).trans (budgetERawHighLo.trans
      (budgetERawMono (Nat.sub_le 48 r) ho)))
  · by_cases ho : 47 < o
    · rw [ite_eq_left (Or.inr ho)]
      have hlo : 20 ≤ lo := by dsimp only [o, lo] at *; omega
      exact min_eq_left ((h20 hlo).trans (budgetERawHighOrder.trans
        (budgetERawMono (by omega) ho)))
    · rw [ite_eq_right (fun h => h.elim hl ho)]
      rw [budgetEFreeSum_eq lo o (by omega) (by omega), budgetEOrder48 o (by omega)]

-- The outer contact cutoff also truncates each shifted target count.
private def budgetETargetShort (o : ℕ) : ℕ :=
  sumRange ((o + 2) / 3) fun a => budgetEHalf (o - 3 * a)

private theorem budgetETargetShort_eq (d : ℕ) (lo o : ℤ) (hn : 0 ≤ o)
    (ho : o ≤ (d : ℤ) + 1) (hl : lo + (o - 1) / 3 ≤ (d : ℤ)) :
    targetCount d lo o = budgetETargetShort o.toNat := by
  unfold targetCount budgetETargetShort
  rw [sumRange_prefix (d + 1) ((o.toNat + 2) / 3) _ (by omega)]
  · apply sumRange_congr
    intro a ha
    have had : lo + a ≤ d := by omega
    have term (f : ℕ) (_ : f < d - a + 1) :
        intervalSize (max 0 (lo - d + a - 2 * f)) (min ((d : ℤ) - a - f) (o - 1 - 3 * a - 2 * f)) =
          o.toNat - 3 * a - 2 * f := by
      rw [max_eq_left (by omega : lo - d + a - 2 * f ≤ 0),
        min_eq_right (by omega : o - 1 - 3 * a - 2 * f ≤ (d : ℤ) - a - f)]
      unfold intervalSize
      omega
    rw [sumRange_congr _ term, budgetEHalfSum (o.toNat - 3 * a) (d - a + 1) (by omega)]
  · intro a ha _
    apply sumRange_zero
    intro f _
    have hneg : o - 1 - 3 * (a : ℤ) - 2 * f < 0 := by omega
    unfold intervalSize
    omega

-- The selected cells have hi = d. The other inequalities ensure the lower
-- endpoint is zero for each contributing target interval.
private def budgetEShift (d top : ℕ) (lo hi o : ℤ) : ℕ :=
  if hi = d ∧ lo ≤ (d : ℤ) + 1 ∧ 0 ≤ o ∧ o ≤ (d : ℤ) + 1 ∧ lo + (o - 1) / 3 ≤ (d : ℤ) then
    budgetEBandShort d lo.toNat top - budgetETargetShort o.toNat
  else
    bandCount d lo hi top - targetCount d lo o

private theorem budgetEShift_eq (d top : ℕ) (lo hi o : ℤ) :
    bandCount d lo hi top - targetCount d lo o = budgetEShift d top lo hi o := by
  unfold budgetEShift
  split
  next h =>
    obtain ⟨e, hl, hn, ho, h⟩ := h
    rw [e, budgetEBandShort_eq d top lo hl, budgetETargetShort_eq d lo o hn ho h]
  next => rfl

private def budgetEFlag (s r : ℕ) (v : FactorPowers) : ℕ :=
  let g := offset r
  let count := budgetEActive (48 - r)
  if v.degree ≤ 48 ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10 then
    let d' := 48 - v.degree
    let lo' := -g - (v.minIndex : ℤ)
    let hi' := 48 - (v.maxIndex : ℤ)
    let order' := orderCutoff s g - (v.minOrder : ℤ)
    count - budgetEShift d' (10 - v.maxTop) lo' hi' order'
  else count

private theorem budgetEFlag_eq (s r : ℕ) (v : FactorPowers) (hs : 62 ≤ s ∧ s ≤ 74) :
    flagBound s (offset r) v = budgetEFlag s r v := by
  have hd : residualDegree s = 48 := by unfold residualDegree; omega
  have hlo : (-(offset r)).toNat = 48 - r := by unfold offset; omega
  have hcount : bandCount 48 (-(offset r)) 48 10 = budgetEActive (48 - r) := by
    rw [activeNatCount_eq 48 (-(offset r)) 48 (by decide), hlo]
    exact budgetEActiveCount _ (by omega : 48 - r < 49)
  unfold flagBound budgetEFlag
  dsimp only
  rw [hd, hcount]
  by_cases h : v.degree ≤ 48 ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10
  · simp only [ite_eq_left h]
    rw [budgetEShift_eq]
  · simp only [ite_eq_right h]

private def budgetEBlockValue (s r : ℕ) : ℕ :=
  if s + r < 138 then
    let p := budgetEPascalValue (48 - r) (138 - (s + r))
    match selectedFactors s (offset r) with
    | none => p
    | some v => min p (budgetEFlag s r v)
  else 0

private theorem budgetEBlock_eq (s r : ℕ) (hs : 62 ≤ s ∧ s ≤ 74) :
    fastBlock s r = budgetEBlockValue s r := by
  by_cases hr : s + r < 138
  · cases hv : selectedFactors s (offset r) <;>
      simp only [fastBlock, budgetEBlockValue, ite_eq_left hr, hv,
        budgetEPascal_eq s r hs hr, budgetEFlag_eq s r _ hs]
  · simp only [fastBlock, budgetEBlockValue, ite_eq_right hr]

private theorem budgetECheckBlocks (s start n value : ℕ) (hs : 62 ≤ s ∧ s ≤ 74)
    (h : sumRange n (fun i => budgetEBlockValue s (i + start)) = value) :
    sumRange n (fun i => fastBlock s (i + start)) = value :=
  (sumRange_congr n (fun i _ => budgetEBlock_eq s (i + start) hs)).trans h

private theorem budgetERangeAdd (a b : ℕ) (f : ℕ → ℕ) :
    sumRange (a + b) f = sumRange a f + sumRange b (fun i => f (i + a)) := by
  have hsucc (n : ℕ) (g : ℕ → ℕ) : sumRange (n + 1) g = sumRange n g + g n := rfl
  induction b with
  | zero => simp [sumRange]
  | succ b ih =>
    rw [Nat.add_succ, hsucc, ih, hsucc, Nat.add_assoc, Nat.add_comm a b]

private theorem budgetERangeJoin (f : ℕ → ℕ) (a b : ℕ) {x y : ℕ}
    (ha : sumRange a f = x) (hb : sumRange b (fun i => f (i + a)) = y) :
    sumRange (a + b) f = x + y :=
  (budgetERangeAdd a b f).trans (congrArg₂ Nat.add ha hb)

private theorem budgetEZeroTail (s start n : ℕ) (h : 138 ≤ s + start) :
    sumRange n (fun i => fastBlock s (i + start)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : ¬ s + (n + start) < 138 := by omega
    have hz : fastBlock s (n + start) = 0 := by simp only [fastBlock, ite_eq_right hn]
    exact congrArg₂ Nat.add ih hz

-- Check short consecutive groups of active blocks separately. The grade proofs
-- combine the checked sums and the zero tail by congruence.

private theorem budgetEBlocks62_00 :
    sumRange 4 (fastBlock 62) = 1843 :=
  budgetECheckBlocks 62 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_04 :
    sumRange 4 (fun i => fastBlock 62 (i + 4)) = 4527 :=
  budgetECheckBlocks 62 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_08 :
    sumRange 4 (fun i => fastBlock 62 (i + 8)) = 6859 :=
  budgetECheckBlocks 62 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_12 :
    sumRange 4 (fun i => fastBlock 62 (i + 12)) = 8839 :=
  budgetECheckBlocks 62 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_16 :
    sumRange 4 (fun i => fastBlock 62 (i + 16)) = 10467 :=
  budgetECheckBlocks 62 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_20 :
    sumRange 4 (fun i => fastBlock 62 (i + 20)) = 11750 :=
  budgetECheckBlocks 62 20 4 11750 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_24 :
    sumRange 4 (fun i => fastBlock 62 (i + 24)) = 12724 :=
  budgetECheckBlocks 62 24 4 12724 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_28 :
    sumRange 4 (fun i => fastBlock 62 (i + 28)) = 12423 :=
  budgetECheckBlocks 62 28 4 12423 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_32 :
    sumRange 4 (fun i => fastBlock 62 (i + 32)) = 9933 :=
  budgetECheckBlocks 62 32 4 9933 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_36 :
    sumRange 4 (fun i => fastBlock 62 (i + 36)) = 7601 :=
  budgetECheckBlocks 62 36 4 7601 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_40 :
    sumRange 4 (fun i => fastBlock 62 (i + 40)) = 5621 :=
  budgetECheckBlocks 62 40 4 5621 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_44 :
    sumRange 4 (fun i => fastBlock 62 (i + 44)) = 3993 :=
  budgetECheckBlocks 62 44 4 3993 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_48 :
    sumRange 4 (fun i => fastBlock 62 (i + 48)) = 2710 :=
  budgetECheckBlocks 62 48 4 2710 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_52 :
    sumRange 4 (fun i => fastBlock 62 (i + 52)) = 1736 :=
  budgetECheckBlocks 62 52 4 1736 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_56 :
    sumRange 4 (fun i => fastBlock 62 (i + 56)) = 1029 :=
  budgetECheckBlocks 62 56 4 1029 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_60 :
    sumRange 4 (fun i => fastBlock 62 (i + 60)) = 546 :=
  budgetECheckBlocks 62 60 4 546 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_64 :
    sumRange 4 (fun i => fastBlock 62 (i + 64)) = 244 :=
  budgetECheckBlocks 62 64 4 244 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_68 :
    sumRange 4 (fun i => fastBlock 62 (i + 68)) = 81 :=
  budgetECheckBlocks 62 68 4 81 (by decide) (by decide +kernel)
private theorem budgetEBlocks62_72 :
    sumRange 4 (fun i => fastBlock 62 (i + 72)) = 14 :=
  budgetECheckBlocks 62 72 4 14 (by decide) (by decide +kernel)

private theorem grade62 : fastGrade 62 = 102940 := by
  have h8 := budgetERangeJoin (fastBlock 62) 4 4 budgetEBlocks62_00 budgetEBlocks62_04
  have h12 := budgetERangeJoin (fastBlock 62) 8 4 h8 budgetEBlocks62_08
  have h16 := budgetERangeJoin (fastBlock 62) 12 4 h12 budgetEBlocks62_12
  have h20 := budgetERangeJoin (fastBlock 62) 16 4 h16 budgetEBlocks62_16
  have h24 := budgetERangeJoin (fastBlock 62) 20 4 h20 budgetEBlocks62_20
  have h28 := budgetERangeJoin (fastBlock 62) 24 4 h24 budgetEBlocks62_24
  have h32 := budgetERangeJoin (fastBlock 62) 28 4 h28 budgetEBlocks62_28
  have h36 := budgetERangeJoin (fastBlock 62) 32 4 h32 budgetEBlocks62_32
  have h40 := budgetERangeJoin (fastBlock 62) 36 4 h36 budgetEBlocks62_36
  have h44 := budgetERangeJoin (fastBlock 62) 40 4 h40 budgetEBlocks62_40
  have h48 := budgetERangeJoin (fastBlock 62) 44 4 h44 budgetEBlocks62_44
  have h52 := budgetERangeJoin (fastBlock 62) 48 4 h48 budgetEBlocks62_48
  have h56 := budgetERangeJoin (fastBlock 62) 52 4 h52 budgetEBlocks62_52
  have h60 := budgetERangeJoin (fastBlock 62) 56 4 h56 budgetEBlocks62_56
  have h64 := budgetERangeJoin (fastBlock 62) 60 4 h60 budgetEBlocks62_60
  have h68 := budgetERangeJoin (fastBlock 62) 64 4 h64 budgetEBlocks62_64
  have h72 := budgetERangeJoin (fastBlock 62) 68 4 h68 budgetEBlocks62_68
  have h76 := budgetERangeJoin (fastBlock 62) 72 4 h72 budgetEBlocks62_72
  exact budgetERangeJoin (fastBlock 62) 76 62 h76
    (budgetEZeroTail 62 76 62 (by decide))

private theorem budgetEBlocks63_00 :
    sumRange 4 (fastBlock 63) = 1843 :=
  budgetECheckBlocks 63 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_04 :
    sumRange 4 (fun i => fastBlock 63 (i + 4)) = 4527 :=
  budgetECheckBlocks 63 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_08 :
    sumRange 4 (fun i => fastBlock 63 (i + 8)) = 6859 :=
  budgetECheckBlocks 63 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_12 :
    sumRange 4 (fun i => fastBlock 63 (i + 12)) = 8839 :=
  budgetECheckBlocks 63 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_16 :
    sumRange 4 (fun i => fastBlock 63 (i + 16)) = 10467 :=
  budgetECheckBlocks 63 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_20 :
    sumRange 4 (fun i => fastBlock 63 (i + 20)) = 11750 :=
  budgetECheckBlocks 63 20 4 11750 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_24 :
    sumRange 4 (fun i => fastBlock 63 (i + 24)) = 12698 :=
  budgetECheckBlocks 63 24 4 12698 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_28 :
    sumRange 4 (fun i => fastBlock 63 (i + 28)) = 11853 :=
  budgetECheckBlocks 63 28 4 11853 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_32 :
    sumRange 4 (fun i => fastBlock 63 (i + 32)) = 9317 :=
  budgetECheckBlocks 63 32 4 9317 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_36 :
    sumRange 4 (fun i => fastBlock 63 (i + 36)) = 7073 :=
  budgetECheckBlocks 63 36 4 7073 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_40 :
    sumRange 4 (fun i => fastBlock 63 (i + 40)) = 5181 :=
  budgetECheckBlocks 63 40 4 5181 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_44 :
    sumRange 4 (fun i => fastBlock 63 (i + 44)) = 3641 :=
  budgetECheckBlocks 63 44 4 3641 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_48 :
    sumRange 4 (fun i => fastBlock 63 (i + 48)) = 2439 :=
  budgetECheckBlocks 63 48 4 2439 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_52 :
    sumRange 4 (fun i => fastBlock 63 (i + 52)) = 1536 :=
  budgetECheckBlocks 63 52 4 1536 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_56 :
    sumRange 4 (fun i => fastBlock 63 (i + 56)) = 889 :=
  budgetECheckBlocks 63 56 4 889 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_60 :
    sumRange 4 (fun i => fastBlock 63 (i + 60)) = 455 :=
  budgetECheckBlocks 63 60 4 455 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_64 :
    sumRange 4 (fun i => fastBlock 63 (i + 64)) = 192 :=
  budgetECheckBlocks 63 64 4 192 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_68 :
    sumRange 4 (fun i => fastBlock 63 (i + 68)) = 57 :=
  budgetECheckBlocks 63 68 4 57 (by decide) (by decide +kernel)
private theorem budgetEBlocks63_72 :
    sumRange 3 (fun i => fastBlock 63 (i + 72)) = 7 :=
  budgetECheckBlocks 63 72 3 7 (by decide) (by decide +kernel)

private theorem grade63 : fastGrade 63 = 99623 := by
  have h8 := budgetERangeJoin (fastBlock 63) 4 4 budgetEBlocks63_00 budgetEBlocks63_04
  have h12 := budgetERangeJoin (fastBlock 63) 8 4 h8 budgetEBlocks63_08
  have h16 := budgetERangeJoin (fastBlock 63) 12 4 h12 budgetEBlocks63_12
  have h20 := budgetERangeJoin (fastBlock 63) 16 4 h16 budgetEBlocks63_16
  have h24 := budgetERangeJoin (fastBlock 63) 20 4 h20 budgetEBlocks63_20
  have h28 := budgetERangeJoin (fastBlock 63) 24 4 h24 budgetEBlocks63_24
  have h32 := budgetERangeJoin (fastBlock 63) 28 4 h28 budgetEBlocks63_28
  have h36 := budgetERangeJoin (fastBlock 63) 32 4 h32 budgetEBlocks63_32
  have h40 := budgetERangeJoin (fastBlock 63) 36 4 h36 budgetEBlocks63_36
  have h44 := budgetERangeJoin (fastBlock 63) 40 4 h40 budgetEBlocks63_40
  have h48 := budgetERangeJoin (fastBlock 63) 44 4 h44 budgetEBlocks63_44
  have h52 := budgetERangeJoin (fastBlock 63) 48 4 h48 budgetEBlocks63_48
  have h56 := budgetERangeJoin (fastBlock 63) 52 4 h52 budgetEBlocks63_52
  have h60 := budgetERangeJoin (fastBlock 63) 56 4 h56 budgetEBlocks63_56
  have h64 := budgetERangeJoin (fastBlock 63) 60 4 h60 budgetEBlocks63_60
  have h68 := budgetERangeJoin (fastBlock 63) 64 4 h64 budgetEBlocks63_64
  have h72 := budgetERangeJoin (fastBlock 63) 68 4 h68 budgetEBlocks63_68
  have h75 := budgetERangeJoin (fastBlock 63) 72 3 h72 budgetEBlocks63_72
  exact budgetERangeJoin (fastBlock 63) 75 63 h75
    (budgetEZeroTail 63 75 63 (by decide))

private theorem budgetEBlocks64_00 :
    sumRange 4 (fastBlock 64) = 1843 :=
  budgetECheckBlocks 64 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_04 :
    sumRange 4 (fun i => fastBlock 64 (i + 4)) = 4527 :=
  budgetECheckBlocks 64 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_08 :
    sumRange 4 (fun i => fastBlock 64 (i + 8)) = 6859 :=
  budgetECheckBlocks 64 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_12 :
    sumRange 4 (fun i => fastBlock 64 (i + 12)) = 8839 :=
  budgetECheckBlocks 64 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_16 :
    sumRange 4 (fun i => fastBlock 64 (i + 16)) = 10467 :=
  budgetECheckBlocks 64 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_20 :
    sumRange 4 (fun i => fastBlock 64 (i + 20)) = 11750 :=
  budgetECheckBlocks 64 20 4 11750 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_24 :
    sumRange 4 (fun i => fastBlock 64 (i + 24)) = 12612 :=
  budgetECheckBlocks 64 24 4 12612 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_28 :
    sumRange 4 (fun i => fastBlock 64 (i + 28)) = 11231 :=
  budgetECheckBlocks 64 28 4 11231 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_32 :
    sumRange 4 (fun i => fastBlock 64 (i + 32)) = 8723 :=
  budgetECheckBlocks 64 32 4 8723 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_36 :
    sumRange 4 (fun i => fastBlock 64 (i + 36)) = 6567 :=
  budgetECheckBlocks 64 36 4 6567 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_40 :
    sumRange 4 (fun i => fastBlock 64 (i + 40)) = 4763 :=
  budgetECheckBlocks 64 40 4 4763 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_44 :
    sumRange 4 (fun i => fastBlock 64 (i + 44)) = 3310 :=
  budgetECheckBlocks 64 44 4 3310 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_48 :
    sumRange 4 (fun i => fastBlock 64 (i + 48)) = 2187 :=
  budgetECheckBlocks 64 48 4 2187 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_52 :
    sumRange 4 (fun i => fastBlock 64 (i + 52)) = 1352 :=
  budgetECheckBlocks 64 52 4 1352 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_56 :
    sumRange 4 (fun i => fastBlock 64 (i + 56)) = 762 :=
  budgetECheckBlocks 64 56 4 762 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_60 :
    sumRange 4 (fun i => fastBlock 64 (i + 60)) = 375 :=
  budgetECheckBlocks 64 60 4 375 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_64 :
    sumRange 4 (fun i => fastBlock 64 (i + 64)) = 148 :=
  budgetECheckBlocks 64 64 4 148 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_68 :
    sumRange 4 (fun i => fastBlock 64 (i + 68)) = 38 :=
  budgetECheckBlocks 64 68 4 38 (by decide) (by decide +kernel)
private theorem budgetEBlocks64_72 :
    sumRange 2 (fun i => fastBlock 64 (i + 72)) = 3 :=
  budgetECheckBlocks 64 72 2 3 (by decide) (by decide +kernel)

private theorem grade64 : fastGrade 64 = 96356 := by
  have h8 := budgetERangeJoin (fastBlock 64) 4 4 budgetEBlocks64_00 budgetEBlocks64_04
  have h12 := budgetERangeJoin (fastBlock 64) 8 4 h8 budgetEBlocks64_08
  have h16 := budgetERangeJoin (fastBlock 64) 12 4 h12 budgetEBlocks64_12
  have h20 := budgetERangeJoin (fastBlock 64) 16 4 h16 budgetEBlocks64_16
  have h24 := budgetERangeJoin (fastBlock 64) 20 4 h20 budgetEBlocks64_20
  have h28 := budgetERangeJoin (fastBlock 64) 24 4 h24 budgetEBlocks64_24
  have h32 := budgetERangeJoin (fastBlock 64) 28 4 h28 budgetEBlocks64_28
  have h36 := budgetERangeJoin (fastBlock 64) 32 4 h32 budgetEBlocks64_32
  have h40 := budgetERangeJoin (fastBlock 64) 36 4 h36 budgetEBlocks64_36
  have h44 := budgetERangeJoin (fastBlock 64) 40 4 h40 budgetEBlocks64_40
  have h48 := budgetERangeJoin (fastBlock 64) 44 4 h44 budgetEBlocks64_44
  have h52 := budgetERangeJoin (fastBlock 64) 48 4 h48 budgetEBlocks64_48
  have h56 := budgetERangeJoin (fastBlock 64) 52 4 h52 budgetEBlocks64_52
  have h60 := budgetERangeJoin (fastBlock 64) 56 4 h56 budgetEBlocks64_56
  have h64 := budgetERangeJoin (fastBlock 64) 60 4 h60 budgetEBlocks64_60
  have h68 := budgetERangeJoin (fastBlock 64) 64 4 h64 budgetEBlocks64_64
  have h72 := budgetERangeJoin (fastBlock 64) 68 4 h68 budgetEBlocks64_68
  have h74 := budgetERangeJoin (fastBlock 64) 72 2 h72 budgetEBlocks64_72
  exact budgetERangeJoin (fastBlock 64) 74 64 h74
    (budgetEZeroTail 64 74 64 (by decide))

private theorem budgetEBlocks65_00 :
    sumRange 4 (fastBlock 65) = 1843 :=
  budgetECheckBlocks 65 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_04 :
    sumRange 4 (fun i => fastBlock 65 (i + 4)) = 4527 :=
  budgetECheckBlocks 65 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_08 :
    sumRange 4 (fun i => fastBlock 65 (i + 8)) = 6859 :=
  budgetECheckBlocks 65 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_12 :
    sumRange 4 (fun i => fastBlock 65 (i + 12)) = 8839 :=
  budgetECheckBlocks 65 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_16 :
    sumRange 4 (fun i => fastBlock 65 (i + 16)) = 10467 :=
  budgetECheckBlocks 65 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_20 :
    sumRange 4 (fun i => fastBlock 65 (i + 20)) = 11750 :=
  budgetECheckBlocks 65 20 4 11750 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_24 :
    sumRange 4 (fun i => fastBlock 65 (i + 24)) = 12425 :=
  budgetECheckBlocks 65 24 4 12425 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_28 :
    sumRange 4 (fun i => fastBlock 65 (i + 28)) = 10571 :=
  budgetECheckBlocks 65 28 4 10571 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_32 :
    sumRange 4 (fun i => fastBlock 65 (i + 32)) = 8151 :=
  budgetECheckBlocks 65 32 4 8151 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_36 :
    sumRange 4 (fun i => fastBlock 65 (i + 36)) = 6083 :=
  budgetECheckBlocks 65 36 4 6083 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_40 :
    sumRange 4 (fun i => fastBlock 65 (i + 40)) = 4367 :=
  budgetECheckBlocks 65 40 4 4367 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_44 :
    sumRange 4 (fun i => fastBlock 65 (i + 44)) = 3000 :=
  budgetECheckBlocks 65 44 4 3000 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_48 :
    sumRange 4 (fun i => fastBlock 65 (i + 48)) = 1953 :=
  budgetECheckBlocks 65 48 4 1953 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_52 :
    sumRange 4 (fun i => fastBlock 65 (i + 52)) = 1183 :=
  budgetECheckBlocks 65 52 4 1183 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_56 :
    sumRange 4 (fun i => fastBlock 65 (i + 56)) = 648 :=
  budgetECheckBlocks 65 56 4 648 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_60 :
    sumRange 4 (fun i => fastBlock 65 (i + 60)) = 305 :=
  budgetECheckBlocks 65 60 4 305 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_64 :
    sumRange 4 (fun i => fastBlock 65 (i + 64)) = 111 :=
  budgetECheckBlocks 65 64 4 111 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_68 :
    sumRange 4 (fun i => fastBlock 65 (i + 68)) = 24 :=
  budgetECheckBlocks 65 68 4 24 (by decide) (by decide +kernel)
private theorem budgetEBlocks65_72 :
    sumRange 1 (fun i => fastBlock 65 (i + 72)) = 1 :=
  budgetECheckBlocks 65 72 1 1 (by decide) (by decide +kernel)

private theorem grade65 : fastGrade 65 = 93107 := by
  have h8 := budgetERangeJoin (fastBlock 65) 4 4 budgetEBlocks65_00 budgetEBlocks65_04
  have h12 := budgetERangeJoin (fastBlock 65) 8 4 h8 budgetEBlocks65_08
  have h16 := budgetERangeJoin (fastBlock 65) 12 4 h12 budgetEBlocks65_12
  have h20 := budgetERangeJoin (fastBlock 65) 16 4 h16 budgetEBlocks65_16
  have h24 := budgetERangeJoin (fastBlock 65) 20 4 h20 budgetEBlocks65_20
  have h28 := budgetERangeJoin (fastBlock 65) 24 4 h24 budgetEBlocks65_24
  have h32 := budgetERangeJoin (fastBlock 65) 28 4 h28 budgetEBlocks65_28
  have h36 := budgetERangeJoin (fastBlock 65) 32 4 h32 budgetEBlocks65_32
  have h40 := budgetERangeJoin (fastBlock 65) 36 4 h36 budgetEBlocks65_36
  have h44 := budgetERangeJoin (fastBlock 65) 40 4 h40 budgetEBlocks65_40
  have h48 := budgetERangeJoin (fastBlock 65) 44 4 h44 budgetEBlocks65_44
  have h52 := budgetERangeJoin (fastBlock 65) 48 4 h48 budgetEBlocks65_48
  have h56 := budgetERangeJoin (fastBlock 65) 52 4 h52 budgetEBlocks65_52
  have h60 := budgetERangeJoin (fastBlock 65) 56 4 h56 budgetEBlocks65_56
  have h64 := budgetERangeJoin (fastBlock 65) 60 4 h60 budgetEBlocks65_60
  have h68 := budgetERangeJoin (fastBlock 65) 64 4 h64 budgetEBlocks65_64
  have h72 := budgetERangeJoin (fastBlock 65) 68 4 h68 budgetEBlocks65_68
  have h73 := budgetERangeJoin (fastBlock 65) 72 1 h72 budgetEBlocks65_72
  exact budgetERangeJoin (fastBlock 65) 73 65 h73
    (budgetEZeroTail 65 73 65 (by decide))

private theorem budgetEBlocks66_00 :
    sumRange 4 (fastBlock 66) = 1843 :=
  budgetECheckBlocks 66 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_04 :
    sumRange 4 (fun i => fastBlock 66 (i + 4)) = 4527 :=
  budgetECheckBlocks 66 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_08 :
    sumRange 4 (fun i => fastBlock 66 (i + 8)) = 6859 :=
  budgetECheckBlocks 66 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_12 :
    sumRange 4 (fun i => fastBlock 66 (i + 12)) = 8839 :=
  budgetECheckBlocks 66 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_16 :
    sumRange 4 (fun i => fastBlock 66 (i + 16)) = 10467 :=
  budgetECheckBlocks 66 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_20 :
    sumRange 4 (fun i => fastBlock 66 (i + 20)) = 11750 :=
  budgetECheckBlocks 66 20 4 11750 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_24 :
    sumRange 4 (fun i => fastBlock 66 (i + 24)) = 12107 :=
  budgetECheckBlocks 66 24 4 12107 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_28 :
    sumRange 4 (fun i => fastBlock 66 (i + 28)) = 9933 :=
  budgetECheckBlocks 66 28 4 9933 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_32 :
    sumRange 4 (fun i => fastBlock 66 (i + 32)) = 7601 :=
  budgetECheckBlocks 66 32 4 7601 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_36 :
    sumRange 4 (fun i => fastBlock 66 (i + 36)) = 5621 :=
  budgetECheckBlocks 66 36 4 5621 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_40 :
    sumRange 4 (fun i => fastBlock 66 (i + 40)) = 3993 :=
  budgetECheckBlocks 66 40 4 3993 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_44 :
    sumRange 4 (fun i => fastBlock 66 (i + 44)) = 2710 :=
  budgetECheckBlocks 66 44 4 2710 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_48 :
    sumRange 4 (fun i => fastBlock 66 (i + 48)) = 1736 :=
  budgetECheckBlocks 66 48 4 1736 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_52 :
    sumRange 4 (fun i => fastBlock 66 (i + 52)) = 1029 :=
  budgetECheckBlocks 66 52 4 1029 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_56 :
    sumRange 4 (fun i => fastBlock 66 (i + 56)) = 546 :=
  budgetECheckBlocks 66 56 4 546 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_60 :
    sumRange 4 (fun i => fastBlock 66 (i + 60)) = 244 :=
  budgetECheckBlocks 66 60 4 244 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_64 :
    sumRange 4 (fun i => fastBlock 66 (i + 64)) = 81 :=
  budgetECheckBlocks 66 64 4 81 (by decide) (by decide +kernel)
private theorem budgetEBlocks66_68 :
    sumRange 4 (fun i => fastBlock 66 (i + 68)) = 14 :=
  budgetECheckBlocks 66 68 4 14 (by decide) (by decide +kernel)

private theorem grade66 : fastGrade 66 = 89900 := by
  have h8 := budgetERangeJoin (fastBlock 66) 4 4 budgetEBlocks66_00 budgetEBlocks66_04
  have h12 := budgetERangeJoin (fastBlock 66) 8 4 h8 budgetEBlocks66_08
  have h16 := budgetERangeJoin (fastBlock 66) 12 4 h12 budgetEBlocks66_12
  have h20 := budgetERangeJoin (fastBlock 66) 16 4 h16 budgetEBlocks66_16
  have h24 := budgetERangeJoin (fastBlock 66) 20 4 h20 budgetEBlocks66_20
  have h28 := budgetERangeJoin (fastBlock 66) 24 4 h24 budgetEBlocks66_24
  have h32 := budgetERangeJoin (fastBlock 66) 28 4 h28 budgetEBlocks66_28
  have h36 := budgetERangeJoin (fastBlock 66) 32 4 h32 budgetEBlocks66_32
  have h40 := budgetERangeJoin (fastBlock 66) 36 4 h36 budgetEBlocks66_36
  have h44 := budgetERangeJoin (fastBlock 66) 40 4 h40 budgetEBlocks66_40
  have h48 := budgetERangeJoin (fastBlock 66) 44 4 h44 budgetEBlocks66_44
  have h52 := budgetERangeJoin (fastBlock 66) 48 4 h48 budgetEBlocks66_48
  have h56 := budgetERangeJoin (fastBlock 66) 52 4 h52 budgetEBlocks66_52
  have h60 := budgetERangeJoin (fastBlock 66) 56 4 h56 budgetEBlocks66_56
  have h64 := budgetERangeJoin (fastBlock 66) 60 4 h60 budgetEBlocks66_60
  have h68 := budgetERangeJoin (fastBlock 66) 64 4 h64 budgetEBlocks66_64
  have h72 := budgetERangeJoin (fastBlock 66) 68 4 h68 budgetEBlocks66_68
  exact budgetERangeJoin (fastBlock 66) 72 66 h72
    (budgetEZeroTail 66 72 66 (by decide))

private theorem budgetEBlocks67_00 :
    sumRange 4 (fastBlock 67) = 1843 :=
  budgetECheckBlocks 67 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_04 :
    sumRange 4 (fun i => fastBlock 67 (i + 4)) = 4527 :=
  budgetECheckBlocks 67 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_08 :
    sumRange 4 (fun i => fastBlock 67 (i + 8)) = 6859 :=
  budgetECheckBlocks 67 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_12 :
    sumRange 4 (fun i => fastBlock 67 (i + 12)) = 8839 :=
  budgetECheckBlocks 67 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_16 :
    sumRange 4 (fun i => fastBlock 67 (i + 16)) = 10467 :=
  budgetECheckBlocks 67 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_20 :
    sumRange 4 (fun i => fastBlock 67 (i + 20)) = 11750 :=
  budgetECheckBlocks 67 20 4 11750 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_24 :
    sumRange 4 (fun i => fastBlock 67 (i + 24)) = 11677 :=
  budgetECheckBlocks 67 24 4 11677 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_28 :
    sumRange 4 (fun i => fastBlock 67 (i + 28)) = 9317 :=
  budgetECheckBlocks 67 28 4 9317 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_32 :
    sumRange 4 (fun i => fastBlock 67 (i + 32)) = 7073 :=
  budgetECheckBlocks 67 32 4 7073 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_36 :
    sumRange 4 (fun i => fastBlock 67 (i + 36)) = 5181 :=
  budgetECheckBlocks 67 36 4 5181 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_40 :
    sumRange 4 (fun i => fastBlock 67 (i + 40)) = 3641 :=
  budgetECheckBlocks 67 40 4 3641 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_44 :
    sumRange 4 (fun i => fastBlock 67 (i + 44)) = 2439 :=
  budgetECheckBlocks 67 44 4 2439 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_48 :
    sumRange 4 (fun i => fastBlock 67 (i + 48)) = 1536 :=
  budgetECheckBlocks 67 48 4 1536 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_52 :
    sumRange 4 (fun i => fastBlock 67 (i + 52)) = 889 :=
  budgetECheckBlocks 67 52 4 889 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_56 :
    sumRange 4 (fun i => fastBlock 67 (i + 56)) = 455 :=
  budgetECheckBlocks 67 56 4 455 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_60 :
    sumRange 4 (fun i => fastBlock 67 (i + 60)) = 192 :=
  budgetECheckBlocks 67 60 4 192 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_64 :
    sumRange 4 (fun i => fastBlock 67 (i + 64)) = 57 :=
  budgetECheckBlocks 67 64 4 57 (by decide) (by decide +kernel)
private theorem budgetEBlocks67_68 :
    sumRange 3 (fun i => fastBlock 67 (i + 68)) = 7 :=
  budgetECheckBlocks 67 68 3 7 (by decide) (by decide +kernel)

private theorem grade67 : fastGrade 67 = 86749 := by
  have h8 := budgetERangeJoin (fastBlock 67) 4 4 budgetEBlocks67_00 budgetEBlocks67_04
  have h12 := budgetERangeJoin (fastBlock 67) 8 4 h8 budgetEBlocks67_08
  have h16 := budgetERangeJoin (fastBlock 67) 12 4 h12 budgetEBlocks67_12
  have h20 := budgetERangeJoin (fastBlock 67) 16 4 h16 budgetEBlocks67_16
  have h24 := budgetERangeJoin (fastBlock 67) 20 4 h20 budgetEBlocks67_20
  have h28 := budgetERangeJoin (fastBlock 67) 24 4 h24 budgetEBlocks67_24
  have h32 := budgetERangeJoin (fastBlock 67) 28 4 h28 budgetEBlocks67_28
  have h36 := budgetERangeJoin (fastBlock 67) 32 4 h32 budgetEBlocks67_32
  have h40 := budgetERangeJoin (fastBlock 67) 36 4 h36 budgetEBlocks67_36
  have h44 := budgetERangeJoin (fastBlock 67) 40 4 h40 budgetEBlocks67_40
  have h48 := budgetERangeJoin (fastBlock 67) 44 4 h44 budgetEBlocks67_44
  have h52 := budgetERangeJoin (fastBlock 67) 48 4 h48 budgetEBlocks67_48
  have h56 := budgetERangeJoin (fastBlock 67) 52 4 h52 budgetEBlocks67_52
  have h60 := budgetERangeJoin (fastBlock 67) 56 4 h56 budgetEBlocks67_56
  have h64 := budgetERangeJoin (fastBlock 67) 60 4 h60 budgetEBlocks67_60
  have h68 := budgetERangeJoin (fastBlock 67) 64 4 h64 budgetEBlocks67_64
  have h71 := budgetERangeJoin (fastBlock 67) 68 3 h68 budgetEBlocks67_68
  exact budgetERangeJoin (fastBlock 67) 71 67 h71
    (budgetEZeroTail 67 71 67 (by decide))

private theorem budgetEBlocks68_00 :
    sumRange 4 (fastBlock 68) = 1843 :=
  budgetECheckBlocks 68 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_04 :
    sumRange 4 (fun i => fastBlock 68 (i + 4)) = 4527 :=
  budgetECheckBlocks 68 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_08 :
    sumRange 4 (fun i => fastBlock 68 (i + 8)) = 6859 :=
  budgetECheckBlocks 68 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_12 :
    sumRange 4 (fun i => fastBlock 68 (i + 12)) = 8839 :=
  budgetECheckBlocks 68 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_16 :
    sumRange 4 (fun i => fastBlock 68 (i + 16)) = 10467 :=
  budgetECheckBlocks 68 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_20 :
    sumRange 4 (fun i => fastBlock 68 (i + 20)) = 11733 :=
  budgetECheckBlocks 68 20 4 11733 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_24 :
    sumRange 4 (fun i => fastBlock 68 (i + 24)) = 11143 :=
  budgetECheckBlocks 68 24 4 11143 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_28 :
    sumRange 4 (fun i => fastBlock 68 (i + 28)) = 8723 :=
  budgetECheckBlocks 68 28 4 8723 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_32 :
    sumRange 4 (fun i => fastBlock 68 (i + 32)) = 6567 :=
  budgetECheckBlocks 68 32 4 6567 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_36 :
    sumRange 4 (fun i => fastBlock 68 (i + 36)) = 4763 :=
  budgetECheckBlocks 68 36 4 4763 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_40 :
    sumRange 4 (fun i => fastBlock 68 (i + 40)) = 3310 :=
  budgetECheckBlocks 68 40 4 3310 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_44 :
    sumRange 4 (fun i => fastBlock 68 (i + 44)) = 2187 :=
  budgetECheckBlocks 68 44 4 2187 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_48 :
    sumRange 4 (fun i => fastBlock 68 (i + 48)) = 1352 :=
  budgetECheckBlocks 68 48 4 1352 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_52 :
    sumRange 4 (fun i => fastBlock 68 (i + 52)) = 762 :=
  budgetECheckBlocks 68 52 4 762 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_56 :
    sumRange 4 (fun i => fastBlock 68 (i + 56)) = 375 :=
  budgetECheckBlocks 68 56 4 375 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_60 :
    sumRange 4 (fun i => fastBlock 68 (i + 60)) = 148 :=
  budgetECheckBlocks 68 60 4 148 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_64 :
    sumRange 4 (fun i => fastBlock 68 (i + 64)) = 38 :=
  budgetECheckBlocks 68 64 4 38 (by decide) (by decide +kernel)
private theorem budgetEBlocks68_68 :
    sumRange 2 (fun i => fastBlock 68 (i + 68)) = 3 :=
  budgetECheckBlocks 68 68 2 3 (by decide) (by decide +kernel)

private theorem grade68 : fastGrade 68 = 83639 := by
  have h8 := budgetERangeJoin (fastBlock 68) 4 4 budgetEBlocks68_00 budgetEBlocks68_04
  have h12 := budgetERangeJoin (fastBlock 68) 8 4 h8 budgetEBlocks68_08
  have h16 := budgetERangeJoin (fastBlock 68) 12 4 h12 budgetEBlocks68_12
  have h20 := budgetERangeJoin (fastBlock 68) 16 4 h16 budgetEBlocks68_16
  have h24 := budgetERangeJoin (fastBlock 68) 20 4 h20 budgetEBlocks68_20
  have h28 := budgetERangeJoin (fastBlock 68) 24 4 h24 budgetEBlocks68_24
  have h32 := budgetERangeJoin (fastBlock 68) 28 4 h28 budgetEBlocks68_28
  have h36 := budgetERangeJoin (fastBlock 68) 32 4 h32 budgetEBlocks68_32
  have h40 := budgetERangeJoin (fastBlock 68) 36 4 h36 budgetEBlocks68_36
  have h44 := budgetERangeJoin (fastBlock 68) 40 4 h40 budgetEBlocks68_40
  have h48 := budgetERangeJoin (fastBlock 68) 44 4 h44 budgetEBlocks68_44
  have h52 := budgetERangeJoin (fastBlock 68) 48 4 h48 budgetEBlocks68_48
  have h56 := budgetERangeJoin (fastBlock 68) 52 4 h52 budgetEBlocks68_52
  have h60 := budgetERangeJoin (fastBlock 68) 56 4 h56 budgetEBlocks68_56
  have h64 := budgetERangeJoin (fastBlock 68) 60 4 h60 budgetEBlocks68_60
  have h68 := budgetERangeJoin (fastBlock 68) 64 4 h64 budgetEBlocks68_64
  have h70 := budgetERangeJoin (fastBlock 68) 68 2 h68 budgetEBlocks68_68
  exact budgetERangeJoin (fastBlock 68) 70 68 h70
    (budgetEZeroTail 68 70 68 (by decide))

private theorem budgetEBlocks69_00 :
    sumRange 4 (fastBlock 69) = 1843 :=
  budgetECheckBlocks 69 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_04 :
    sumRange 4 (fun i => fastBlock 69 (i + 4)) = 4527 :=
  budgetECheckBlocks 69 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_08 :
    sumRange 4 (fun i => fastBlock 69 (i + 8)) = 6859 :=
  budgetECheckBlocks 69 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_12 :
    sumRange 4 (fun i => fastBlock 69 (i + 12)) = 8839 :=
  budgetECheckBlocks 69 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_16 :
    sumRange 4 (fun i => fastBlock 69 (i + 16)) = 10467 :=
  budgetECheckBlocks 69 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_20 :
    sumRange 4 (fun i => fastBlock 69 (i + 20)) = 11646 :=
  budgetECheckBlocks 69 20 4 11646 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_24 :
    sumRange 4 (fun i => fastBlock 69 (i + 24)) = 10553 :=
  budgetECheckBlocks 69 24 4 10553 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_28 :
    sumRange 4 (fun i => fastBlock 69 (i + 28)) = 8151 :=
  budgetECheckBlocks 69 28 4 8151 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_32 :
    sumRange 4 (fun i => fastBlock 69 (i + 32)) = 6083 :=
  budgetECheckBlocks 69 32 4 6083 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_36 :
    sumRange 4 (fun i => fastBlock 69 (i + 36)) = 4367 :=
  budgetECheckBlocks 69 36 4 4367 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_40 :
    sumRange 4 (fun i => fastBlock 69 (i + 40)) = 3000 :=
  budgetECheckBlocks 69 40 4 3000 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_44 :
    sumRange 4 (fun i => fastBlock 69 (i + 44)) = 1953 :=
  budgetECheckBlocks 69 44 4 1953 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_48 :
    sumRange 4 (fun i => fastBlock 69 (i + 48)) = 1183 :=
  budgetECheckBlocks 69 48 4 1183 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_52 :
    sumRange 4 (fun i => fastBlock 69 (i + 52)) = 648 :=
  budgetECheckBlocks 69 52 4 648 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_56 :
    sumRange 4 (fun i => fastBlock 69 (i + 56)) = 305 :=
  budgetECheckBlocks 69 56 4 305 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_60 :
    sumRange 4 (fun i => fastBlock 69 (i + 60)) = 111 :=
  budgetECheckBlocks 69 60 4 111 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_64 :
    sumRange 4 (fun i => fastBlock 69 (i + 64)) = 24 :=
  budgetECheckBlocks 69 64 4 24 (by decide) (by decide +kernel)
private theorem budgetEBlocks69_68 :
    sumRange 1 (fun i => fastBlock 69 (i + 68)) = 1 :=
  budgetECheckBlocks 69 68 1 1 (by decide) (by decide +kernel)

private theorem grade69 : fastGrade 69 = 80560 := by
  have h8 := budgetERangeJoin (fastBlock 69) 4 4 budgetEBlocks69_00 budgetEBlocks69_04
  have h12 := budgetERangeJoin (fastBlock 69) 8 4 h8 budgetEBlocks69_08
  have h16 := budgetERangeJoin (fastBlock 69) 12 4 h12 budgetEBlocks69_12
  have h20 := budgetERangeJoin (fastBlock 69) 16 4 h16 budgetEBlocks69_16
  have h24 := budgetERangeJoin (fastBlock 69) 20 4 h20 budgetEBlocks69_20
  have h28 := budgetERangeJoin (fastBlock 69) 24 4 h24 budgetEBlocks69_24
  have h32 := budgetERangeJoin (fastBlock 69) 28 4 h28 budgetEBlocks69_28
  have h36 := budgetERangeJoin (fastBlock 69) 32 4 h32 budgetEBlocks69_32
  have h40 := budgetERangeJoin (fastBlock 69) 36 4 h36 budgetEBlocks69_36
  have h44 := budgetERangeJoin (fastBlock 69) 40 4 h40 budgetEBlocks69_40
  have h48 := budgetERangeJoin (fastBlock 69) 44 4 h44 budgetEBlocks69_44
  have h52 := budgetERangeJoin (fastBlock 69) 48 4 h48 budgetEBlocks69_48
  have h56 := budgetERangeJoin (fastBlock 69) 52 4 h52 budgetEBlocks69_52
  have h60 := budgetERangeJoin (fastBlock 69) 56 4 h56 budgetEBlocks69_56
  have h64 := budgetERangeJoin (fastBlock 69) 60 4 h60 budgetEBlocks69_60
  have h68 := budgetERangeJoin (fastBlock 69) 64 4 h64 budgetEBlocks69_64
  have h69 := budgetERangeJoin (fastBlock 69) 68 1 h68 budgetEBlocks69_68
  exact budgetERangeJoin (fastBlock 69) 69 69 h69
    (budgetEZeroTail 69 69 69 (by decide))

private theorem budgetEBlocks70_00 :
    sumRange 4 (fastBlock 70) = 1843 :=
  budgetECheckBlocks 70 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_04 :
    sumRange 4 (fun i => fastBlock 70 (i + 4)) = 4527 :=
  budgetECheckBlocks 70 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_08 :
    sumRange 4 (fun i => fastBlock 70 (i + 8)) = 6859 :=
  budgetECheckBlocks 70 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_12 :
    sumRange 4 (fun i => fastBlock 70 (i + 12)) = 8839 :=
  budgetECheckBlocks 70 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_16 :
    sumRange 4 (fun i => fastBlock 70 (i + 16)) = 10467 :=
  budgetECheckBlocks 70 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_20 :
    sumRange 4 (fun i => fastBlock 70 (i + 20)) = 11489 :=
  budgetECheckBlocks 70 20 4 11489 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_24 :
    sumRange 4 (fun i => fastBlock 70 (i + 24)) = 9933 :=
  budgetECheckBlocks 70 24 4 9933 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_28 :
    sumRange 4 (fun i => fastBlock 70 (i + 28)) = 7601 :=
  budgetECheckBlocks 70 28 4 7601 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_32 :
    sumRange 4 (fun i => fastBlock 70 (i + 32)) = 5621 :=
  budgetECheckBlocks 70 32 4 5621 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_36 :
    sumRange 4 (fun i => fastBlock 70 (i + 36)) = 3993 :=
  budgetECheckBlocks 70 36 4 3993 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_40 :
    sumRange 4 (fun i => fastBlock 70 (i + 40)) = 2710 :=
  budgetECheckBlocks 70 40 4 2710 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_44 :
    sumRange 4 (fun i => fastBlock 70 (i + 44)) = 1736 :=
  budgetECheckBlocks 70 44 4 1736 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_48 :
    sumRange 4 (fun i => fastBlock 70 (i + 48)) = 1029 :=
  budgetECheckBlocks 70 48 4 1029 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_52 :
    sumRange 4 (fun i => fastBlock 70 (i + 52)) = 546 :=
  budgetECheckBlocks 70 52 4 546 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_56 :
    sumRange 4 (fun i => fastBlock 70 (i + 56)) = 244 :=
  budgetECheckBlocks 70 56 4 244 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_60 :
    sumRange 4 (fun i => fastBlock 70 (i + 60)) = 81 :=
  budgetECheckBlocks 70 60 4 81 (by decide) (by decide +kernel)
private theorem budgetEBlocks70_64 :
    sumRange 4 (fun i => fastBlock 70 (i + 64)) = 14 :=
  budgetECheckBlocks 70 64 4 14 (by decide) (by decide +kernel)

private theorem grade70 : fastGrade 70 = 77532 := by
  have h8 := budgetERangeJoin (fastBlock 70) 4 4 budgetEBlocks70_00 budgetEBlocks70_04
  have h12 := budgetERangeJoin (fastBlock 70) 8 4 h8 budgetEBlocks70_08
  have h16 := budgetERangeJoin (fastBlock 70) 12 4 h12 budgetEBlocks70_12
  have h20 := budgetERangeJoin (fastBlock 70) 16 4 h16 budgetEBlocks70_16
  have h24 := budgetERangeJoin (fastBlock 70) 20 4 h20 budgetEBlocks70_20
  have h28 := budgetERangeJoin (fastBlock 70) 24 4 h24 budgetEBlocks70_24
  have h32 := budgetERangeJoin (fastBlock 70) 28 4 h28 budgetEBlocks70_28
  have h36 := budgetERangeJoin (fastBlock 70) 32 4 h32 budgetEBlocks70_32
  have h40 := budgetERangeJoin (fastBlock 70) 36 4 h36 budgetEBlocks70_36
  have h44 := budgetERangeJoin (fastBlock 70) 40 4 h40 budgetEBlocks70_40
  have h48 := budgetERangeJoin (fastBlock 70) 44 4 h44 budgetEBlocks70_44
  have h52 := budgetERangeJoin (fastBlock 70) 48 4 h48 budgetEBlocks70_48
  have h56 := budgetERangeJoin (fastBlock 70) 52 4 h52 budgetEBlocks70_52
  have h60 := budgetERangeJoin (fastBlock 70) 56 4 h56 budgetEBlocks70_56
  have h64 := budgetERangeJoin (fastBlock 70) 60 4 h60 budgetEBlocks70_60
  have h68 := budgetERangeJoin (fastBlock 70) 64 4 h64 budgetEBlocks70_64
  exact budgetERangeJoin (fastBlock 70) 68 70 h68
    (budgetEZeroTail 70 68 70 (by decide))

private theorem budgetEBlocks71_00 :
    sumRange 4 (fastBlock 71) = 1843 :=
  budgetECheckBlocks 71 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_04 :
    sumRange 4 (fun i => fastBlock 71 (i + 4)) = 4527 :=
  budgetECheckBlocks 71 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_08 :
    sumRange 4 (fun i => fastBlock 71 (i + 8)) = 6859 :=
  budgetECheckBlocks 71 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_12 :
    sumRange 4 (fun i => fastBlock 71 (i + 12)) = 8839 :=
  budgetECheckBlocks 71 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_16 :
    sumRange 4 (fun i => fastBlock 71 (i + 16)) = 10467 :=
  budgetECheckBlocks 71 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_20 :
    sumRange 4 (fun i => fastBlock 71 (i + 20)) = 11245 :=
  budgetECheckBlocks 71 20 4 11245 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_24 :
    sumRange 4 (fun i => fastBlock 71 (i + 24)) = 9317 :=
  budgetECheckBlocks 71 24 4 9317 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_28 :
    sumRange 4 (fun i => fastBlock 71 (i + 28)) = 7073 :=
  budgetECheckBlocks 71 28 4 7073 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_32 :
    sumRange 4 (fun i => fastBlock 71 (i + 32)) = 5181 :=
  budgetECheckBlocks 71 32 4 5181 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_36 :
    sumRange 4 (fun i => fastBlock 71 (i + 36)) = 3641 :=
  budgetECheckBlocks 71 36 4 3641 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_40 :
    sumRange 4 (fun i => fastBlock 71 (i + 40)) = 2439 :=
  budgetECheckBlocks 71 40 4 2439 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_44 :
    sumRange 4 (fun i => fastBlock 71 (i + 44)) = 1536 :=
  budgetECheckBlocks 71 44 4 1536 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_48 :
    sumRange 4 (fun i => fastBlock 71 (i + 48)) = 889 :=
  budgetECheckBlocks 71 48 4 889 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_52 :
    sumRange 4 (fun i => fastBlock 71 (i + 52)) = 455 :=
  budgetECheckBlocks 71 52 4 455 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_56 :
    sumRange 4 (fun i => fastBlock 71 (i + 56)) = 192 :=
  budgetECheckBlocks 71 56 4 192 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_60 :
    sumRange 4 (fun i => fastBlock 71 (i + 60)) = 57 :=
  budgetECheckBlocks 71 60 4 57 (by decide) (by decide +kernel)
private theorem budgetEBlocks71_64 :
    sumRange 3 (fun i => fastBlock 71 (i + 64)) = 7 :=
  budgetECheckBlocks 71 64 3 7 (by decide) (by decide +kernel)

private theorem grade71 : fastGrade 71 = 74567 := by
  have h8 := budgetERangeJoin (fastBlock 71) 4 4 budgetEBlocks71_00 budgetEBlocks71_04
  have h12 := budgetERangeJoin (fastBlock 71) 8 4 h8 budgetEBlocks71_08
  have h16 := budgetERangeJoin (fastBlock 71) 12 4 h12 budgetEBlocks71_12
  have h20 := budgetERangeJoin (fastBlock 71) 16 4 h16 budgetEBlocks71_16
  have h24 := budgetERangeJoin (fastBlock 71) 20 4 h20 budgetEBlocks71_20
  have h28 := budgetERangeJoin (fastBlock 71) 24 4 h24 budgetEBlocks71_24
  have h32 := budgetERangeJoin (fastBlock 71) 28 4 h28 budgetEBlocks71_28
  have h36 := budgetERangeJoin (fastBlock 71) 32 4 h32 budgetEBlocks71_32
  have h40 := budgetERangeJoin (fastBlock 71) 36 4 h36 budgetEBlocks71_36
  have h44 := budgetERangeJoin (fastBlock 71) 40 4 h40 budgetEBlocks71_40
  have h48 := budgetERangeJoin (fastBlock 71) 44 4 h44 budgetEBlocks71_44
  have h52 := budgetERangeJoin (fastBlock 71) 48 4 h48 budgetEBlocks71_48
  have h56 := budgetERangeJoin (fastBlock 71) 52 4 h52 budgetEBlocks71_52
  have h60 := budgetERangeJoin (fastBlock 71) 56 4 h56 budgetEBlocks71_56
  have h64 := budgetERangeJoin (fastBlock 71) 60 4 h60 budgetEBlocks71_60
  have h67 := budgetERangeJoin (fastBlock 71) 64 3 h64 budgetEBlocks71_64
  exact budgetERangeJoin (fastBlock 71) 67 71 h67
    (budgetEZeroTail 71 67 71 (by decide))

private theorem budgetEBlocks72_00 :
    sumRange 4 (fastBlock 72) = 1843 :=
  budgetECheckBlocks 72 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_04 :
    sumRange 4 (fun i => fastBlock 72 (i + 4)) = 4527 :=
  budgetECheckBlocks 72 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_08 :
    sumRange 4 (fun i => fastBlock 72 (i + 8)) = 6859 :=
  budgetECheckBlocks 72 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_12 :
    sumRange 4 (fun i => fastBlock 72 (i + 12)) = 8839 :=
  budgetECheckBlocks 72 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_16 :
    sumRange 4 (fun i => fastBlock 72 (i + 16)) = 10467 :=
  budgetECheckBlocks 72 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_20 :
    sumRange 4 (fun i => fastBlock 72 (i + 20)) = 10885 :=
  budgetECheckBlocks 72 20 4 10885 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_24 :
    sumRange 4 (fun i => fastBlock 72 (i + 24)) = 8723 :=
  budgetECheckBlocks 72 24 4 8723 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_28 :
    sumRange 4 (fun i => fastBlock 72 (i + 28)) = 6567 :=
  budgetECheckBlocks 72 28 4 6567 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_32 :
    sumRange 4 (fun i => fastBlock 72 (i + 32)) = 4763 :=
  budgetECheckBlocks 72 32 4 4763 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_36 :
    sumRange 4 (fun i => fastBlock 72 (i + 36)) = 3310 :=
  budgetECheckBlocks 72 36 4 3310 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_40 :
    sumRange 4 (fun i => fastBlock 72 (i + 40)) = 2187 :=
  budgetECheckBlocks 72 40 4 2187 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_44 :
    sumRange 4 (fun i => fastBlock 72 (i + 44)) = 1352 :=
  budgetECheckBlocks 72 44 4 1352 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_48 :
    sumRange 4 (fun i => fastBlock 72 (i + 48)) = 762 :=
  budgetECheckBlocks 72 48 4 762 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_52 :
    sumRange 4 (fun i => fastBlock 72 (i + 52)) = 375 :=
  budgetECheckBlocks 72 52 4 375 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_56 :
    sumRange 4 (fun i => fastBlock 72 (i + 56)) = 148 :=
  budgetECheckBlocks 72 56 4 148 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_60 :
    sumRange 4 (fun i => fastBlock 72 (i + 60)) = 38 :=
  budgetECheckBlocks 72 60 4 38 (by decide) (by decide +kernel)
private theorem budgetEBlocks72_64 :
    sumRange 2 (fun i => fastBlock 72 (i + 64)) = 3 :=
  budgetECheckBlocks 72 64 2 3 (by decide) (by decide +kernel)

private theorem grade72 : fastGrade 72 = 71648 := by
  have h8 := budgetERangeJoin (fastBlock 72) 4 4 budgetEBlocks72_00 budgetEBlocks72_04
  have h12 := budgetERangeJoin (fastBlock 72) 8 4 h8 budgetEBlocks72_08
  have h16 := budgetERangeJoin (fastBlock 72) 12 4 h12 budgetEBlocks72_12
  have h20 := budgetERangeJoin (fastBlock 72) 16 4 h16 budgetEBlocks72_16
  have h24 := budgetERangeJoin (fastBlock 72) 20 4 h20 budgetEBlocks72_20
  have h28 := budgetERangeJoin (fastBlock 72) 24 4 h24 budgetEBlocks72_24
  have h32 := budgetERangeJoin (fastBlock 72) 28 4 h28 budgetEBlocks72_28
  have h36 := budgetERangeJoin (fastBlock 72) 32 4 h32 budgetEBlocks72_32
  have h40 := budgetERangeJoin (fastBlock 72) 36 4 h36 budgetEBlocks72_36
  have h44 := budgetERangeJoin (fastBlock 72) 40 4 h40 budgetEBlocks72_40
  have h48 := budgetERangeJoin (fastBlock 72) 44 4 h44 budgetEBlocks72_44
  have h52 := budgetERangeJoin (fastBlock 72) 48 4 h48 budgetEBlocks72_48
  have h56 := budgetERangeJoin (fastBlock 72) 52 4 h52 budgetEBlocks72_52
  have h60 := budgetERangeJoin (fastBlock 72) 56 4 h56 budgetEBlocks72_56
  have h64 := budgetERangeJoin (fastBlock 72) 60 4 h60 budgetEBlocks72_60
  have h66 := budgetERangeJoin (fastBlock 72) 64 2 h64 budgetEBlocks72_64
  exact budgetERangeJoin (fastBlock 72) 66 72 h66
    (budgetEZeroTail 72 66 72 (by decide))

private theorem budgetEBlocks73_00 :
    sumRange 4 (fastBlock 73) = 1843 :=
  budgetECheckBlocks 73 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_04 :
    sumRange 4 (fun i => fastBlock 73 (i + 4)) = 4527 :=
  budgetECheckBlocks 73 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_08 :
    sumRange 4 (fun i => fastBlock 73 (i + 8)) = 6859 :=
  budgetECheckBlocks 73 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_12 :
    sumRange 4 (fun i => fastBlock 73 (i + 12)) = 8839 :=
  budgetECheckBlocks 73 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_16 :
    sumRange 4 (fun i => fastBlock 73 (i + 16)) = 10467 :=
  budgetECheckBlocks 73 16 4 10467 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_20 :
    sumRange 4 (fun i => fastBlock 73 (i + 20)) = 10405 :=
  budgetECheckBlocks 73 20 4 10405 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_24 :
    sumRange 4 (fun i => fastBlock 73 (i + 24)) = 8151 :=
  budgetECheckBlocks 73 24 4 8151 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_28 :
    sumRange 4 (fun i => fastBlock 73 (i + 28)) = 6083 :=
  budgetECheckBlocks 73 28 4 6083 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_32 :
    sumRange 4 (fun i => fastBlock 73 (i + 32)) = 4367 :=
  budgetECheckBlocks 73 32 4 4367 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_36 :
    sumRange 4 (fun i => fastBlock 73 (i + 36)) = 3000 :=
  budgetECheckBlocks 73 36 4 3000 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_40 :
    sumRange 4 (fun i => fastBlock 73 (i + 40)) = 1953 :=
  budgetECheckBlocks 73 40 4 1953 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_44 :
    sumRange 4 (fun i => fastBlock 73 (i + 44)) = 1183 :=
  budgetECheckBlocks 73 44 4 1183 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_48 :
    sumRange 4 (fun i => fastBlock 73 (i + 48)) = 648 :=
  budgetECheckBlocks 73 48 4 648 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_52 :
    sumRange 4 (fun i => fastBlock 73 (i + 52)) = 305 :=
  budgetECheckBlocks 73 52 4 305 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_56 :
    sumRange 4 (fun i => fastBlock 73 (i + 56)) = 111 :=
  budgetECheckBlocks 73 56 4 111 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_60 :
    sumRange 4 (fun i => fastBlock 73 (i + 60)) = 24 :=
  budgetECheckBlocks 73 60 4 24 (by decide) (by decide +kernel)
private theorem budgetEBlocks73_64 :
    sumRange 1 (fun i => fastBlock 73 (i + 64)) = 1 :=
  budgetECheckBlocks 73 64 1 1 (by decide) (by decide +kernel)

private theorem grade73 : fastGrade 73 = 68766 := by
  have h8 := budgetERangeJoin (fastBlock 73) 4 4 budgetEBlocks73_00 budgetEBlocks73_04
  have h12 := budgetERangeJoin (fastBlock 73) 8 4 h8 budgetEBlocks73_08
  have h16 := budgetERangeJoin (fastBlock 73) 12 4 h12 budgetEBlocks73_12
  have h20 := budgetERangeJoin (fastBlock 73) 16 4 h16 budgetEBlocks73_16
  have h24 := budgetERangeJoin (fastBlock 73) 20 4 h20 budgetEBlocks73_20
  have h28 := budgetERangeJoin (fastBlock 73) 24 4 h24 budgetEBlocks73_24
  have h32 := budgetERangeJoin (fastBlock 73) 28 4 h28 budgetEBlocks73_28
  have h36 := budgetERangeJoin (fastBlock 73) 32 4 h32 budgetEBlocks73_32
  have h40 := budgetERangeJoin (fastBlock 73) 36 4 h36 budgetEBlocks73_36
  have h44 := budgetERangeJoin (fastBlock 73) 40 4 h40 budgetEBlocks73_40
  have h48 := budgetERangeJoin (fastBlock 73) 44 4 h44 budgetEBlocks73_44
  have h52 := budgetERangeJoin (fastBlock 73) 48 4 h48 budgetEBlocks73_48
  have h56 := budgetERangeJoin (fastBlock 73) 52 4 h52 budgetEBlocks73_52
  have h60 := budgetERangeJoin (fastBlock 73) 56 4 h56 budgetEBlocks73_56
  have h64 := budgetERangeJoin (fastBlock 73) 60 4 h60 budgetEBlocks73_60
  have h65 := budgetERangeJoin (fastBlock 73) 64 1 h64 budgetEBlocks73_64
  exact budgetERangeJoin (fastBlock 73) 65 73 h65
    (budgetEZeroTail 73 65 73 (by decide))

private theorem budgetEBlocks74_00 :
    sumRange 4 (fastBlock 74) = 1843 :=
  budgetECheckBlocks 74 0 4 1843 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_04 :
    sumRange 4 (fun i => fastBlock 74 (i + 4)) = 4527 :=
  budgetECheckBlocks 74 4 4 4527 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_08 :
    sumRange 4 (fun i => fastBlock 74 (i + 8)) = 6859 :=
  budgetECheckBlocks 74 8 4 6859 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_12 :
    sumRange 4 (fun i => fastBlock 74 (i + 12)) = 8839 :=
  budgetECheckBlocks 74 12 4 8839 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_16 :
    sumRange 4 (fun i => fastBlock 74 (i + 16)) = 10414 :=
  budgetECheckBlocks 74 16 4 10414 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_20 :
    sumRange 4 (fun i => fastBlock 74 (i + 20)) = 9881 :=
  budgetECheckBlocks 74 20 4 9881 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_24 :
    sumRange 4 (fun i => fastBlock 74 (i + 24)) = 7601 :=
  budgetECheckBlocks 74 24 4 7601 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_28 :
    sumRange 4 (fun i => fastBlock 74 (i + 28)) = 5621 :=
  budgetECheckBlocks 74 28 4 5621 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_32 :
    sumRange 4 (fun i => fastBlock 74 (i + 32)) = 3993 :=
  budgetECheckBlocks 74 32 4 3993 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_36 :
    sumRange 4 (fun i => fastBlock 74 (i + 36)) = 2710 :=
  budgetECheckBlocks 74 36 4 2710 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_40 :
    sumRange 4 (fun i => fastBlock 74 (i + 40)) = 1736 :=
  budgetECheckBlocks 74 40 4 1736 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_44 :
    sumRange 4 (fun i => fastBlock 74 (i + 44)) = 1029 :=
  budgetECheckBlocks 74 44 4 1029 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_48 :
    sumRange 4 (fun i => fastBlock 74 (i + 48)) = 546 :=
  budgetECheckBlocks 74 48 4 546 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_52 :
    sumRange 4 (fun i => fastBlock 74 (i + 52)) = 244 :=
  budgetECheckBlocks 74 52 4 244 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_56 :
    sumRange 4 (fun i => fastBlock 74 (i + 56)) = 81 :=
  budgetECheckBlocks 74 56 4 81 (by decide) (by decide +kernel)
private theorem budgetEBlocks74_60 :
    sumRange 4 (fun i => fastBlock 74 (i + 60)) = 14 :=
  budgetECheckBlocks 74 60 4 14 (by decide) (by decide +kernel)

private theorem grade74 : fastGrade 74 = 65938 := by
  have h8 := budgetERangeJoin (fastBlock 74) 4 4 budgetEBlocks74_00 budgetEBlocks74_04
  have h12 := budgetERangeJoin (fastBlock 74) 8 4 h8 budgetEBlocks74_08
  have h16 := budgetERangeJoin (fastBlock 74) 12 4 h12 budgetEBlocks74_12
  have h20 := budgetERangeJoin (fastBlock 74) 16 4 h16 budgetEBlocks74_16
  have h24 := budgetERangeJoin (fastBlock 74) 20 4 h20 budgetEBlocks74_20
  have h28 := budgetERangeJoin (fastBlock 74) 24 4 h24 budgetEBlocks74_24
  have h32 := budgetERangeJoin (fastBlock 74) 28 4 h28 budgetEBlocks74_28
  have h36 := budgetERangeJoin (fastBlock 74) 32 4 h32 budgetEBlocks74_32
  have h40 := budgetERangeJoin (fastBlock 74) 36 4 h36 budgetEBlocks74_36
  have h44 := budgetERangeJoin (fastBlock 74) 40 4 h40 budgetEBlocks74_40
  have h48 := budgetERangeJoin (fastBlock 74) 44 4 h44 budgetEBlocks74_44
  have h52 := budgetERangeJoin (fastBlock 74) 48 4 h48 budgetEBlocks74_48
  have h56 := budgetERangeJoin (fastBlock 74) 52 4 h52 budgetEBlocks74_52
  have h60 := budgetERangeJoin (fastBlock 74) 56 4 h56 budgetEBlocks74_56
  have h64 := budgetERangeJoin (fastBlock 74) 60 4 h60 budgetEBlocks74_60
  exact budgetERangeJoin (fastBlock 74) 64 74 h64
    (budgetEZeroTail 74 64 74 (by decide))

private theorem sumStep (f : ℕ → ℕ) (n a b : ℕ)
    (ha : sumRange n f = a) (hb : f n = b) :
    sumRange (n + 1) f = a + b :=
  (show sumRange (n + 1) f = sumRange n f + f n from rfl).trans (congrArg₂ Nat.add ha hb)

private def gradeFrom (i : ℕ) : ℕ := fastGrade (i + 62)

private theorem prefix62 : sumRange 1 gradeFrom = 102940 :=
  sumStep gradeFrom 0 0 102940 rfl grade62
private theorem prefix63 : sumRange 2 gradeFrom = 202563 :=
  sumStep gradeFrom 1 102940 99623 prefix62 grade63
private theorem prefix64 : sumRange 3 gradeFrom = 298919 :=
  sumStep gradeFrom 2 202563 96356 prefix63 grade64
private theorem prefix65 : sumRange 4 gradeFrom = 392026 :=
  sumStep gradeFrom 3 298919 93107 prefix64 grade65
private theorem prefix66 : sumRange 5 gradeFrom = 481926 :=
  sumStep gradeFrom 4 392026 89900 prefix65 grade66
private theorem prefix67 : sumRange 6 gradeFrom = 568675 :=
  sumStep gradeFrom 5 481926 86749 prefix66 grade67
private theorem prefix68 : sumRange 7 gradeFrom = 652314 :=
  sumStep gradeFrom 6 568675 83639 prefix67 grade68
private theorem prefix69 : sumRange 8 gradeFrom = 732874 :=
  sumStep gradeFrom 7 652314 80560 prefix68 grade69
private theorem prefix70 : sumRange 9 gradeFrom = 810406 :=
  sumStep gradeFrom 8 732874 77532 prefix69 grade70
private theorem prefix71 : sumRange 10 gradeFrom = 884973 :=
  sumStep gradeFrom 9 810406 74567 prefix70 grade71
private theorem prefix72 : sumRange 11 gradeFrom = 956621 :=
  sumStep gradeFrom 10 884973 71648 prefix71 grade72
private theorem prefix73 : sumRange 12 gradeFrom = 1025387 :=
  sumStep gradeFrom 11 956621 68766 prefix72 grade73
theorem budgetE : sumRange 13 (fun i => fastGrade (i + 62)) = 1091325 :=
  sumStep gradeFrom 12 1025387 65938 prefix73 grade74

end K1_13_1_1
end PackSource_K1_13_1_1BudgetE

section PackSource_K1_13_8_3Mixed
set_option autoImplicit true
namespace K1_13_8_3

open K1_13

/-- Increase the total-degree coordinate while fixing the index and top degree. -/
private def bump (p : Shape) (d : ℕ) : Shape := ⟨p.b + d, p.j, p.t⟩

def Widen (p q : Shape) : Prop := p.b ≤ q.b ∧ p.j = q.j ∧ p.t = q.t

theorem Widen.refl (p : Shape) : Widen p p := ⟨le_rfl, rfl, rfl⟩

def Admissible (p : Shape) : Prop := 3 * p.t ≤ p.j

private def mixedInt (p q r s : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩

private def slack (p : Shape) : ℤ := (p.j : ℤ) - 3 * (p.t : ℤ)

private def weight (q r s : Shape) : ℤ :=
  16 * (slack q * slack r * s.t + slack q * slack s * r.t + slack r * slack s * q.t) +
  48 * (slack q * r.t * s.t + slack r * q.t * s.t + slack s * q.t * r.t) +
  144 * q.t * r.t * s.t

private theorem weight_nonneg {q r s : Shape}
    (hq : Admissible q) (hr : Admissible r) (hs : Admissible s) :
    0 ≤ weight q r s := by
  have hslack {p : Shape} (hp : Admissible p) : 0 ≤ slack p := by
    unfold slack
    have : 3 * p.t ≤ p.j := hp
    omega
  have := hslack hq
  have := hslack hr
  have := hslack hs
  unfold weight
  positivity

set_option maxHeartbeats 0 in
private theorem mixed_bump (p q r s : Shape) (d : ℕ) :
    mixedInt (bump p d) q r s = mixedInt p q r s + (d : ℤ) * weight q r s := by
  simp only [mixedInt, difference, volume32, Shape.plus, bump, weight, slack,
    Nat.cast_add, Nat.cast_zero]
  ring

private theorem mixed_first {p p' q r s : Shape} (hp : Widen p p')
    (hq : Admissible q) (hr : Admissible r) (hs : Admissible s) :
    mixedInt p q r s ≤ mixedInt p' q r s := by
  have h : p' = bump p (p'.b - p.b) := by
    obtain ⟨b, j, t⟩ := p
    obtain ⟨b', j', t'⟩ := p'
    obtain ⟨hb, rfl, rfl⟩ := hp
    simp [bump, Nat.add_sub_of_le hb]
  rw [h, mixed_bump]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (weight_nonneg hq hr hs))

private theorem commute (h : Shape → ℤ) (p q : Shape) :
    difference (difference h p) q = difference (difference h q) p := by
  funext x
  have hsum : (x.plus q).plus p = (x.plus p).plus q := by
    cases x
    cases p
    cases q
    simp [Shape.plus, Nat.add_right_comm]
  unfold difference
  rw [hsum]
  ring

private theorem mixed_swap12 (p q r s : Shape) : mixedInt p q r s = mixedInt q p r s := by
  unfold mixedInt
  rw [commute volume32 p q]

private theorem mixed_swap23 (p q r s : Shape) : mixedInt p q r s = mixedInt p r q s := by
  unfold mixedInt
  rw [commute (difference volume32 p) q r]

private theorem mixed_swap34 (p q r s : Shape) : mixedInt p q r s = mixedInt p q s r := by
  unfold mixedInt
  rw [commute (difference (difference volume32 p) q) r s]

theorem Widen.admissible {p q : Shape} (h : Widen p q) (hp : Admissible p) : Admissible q := by
  unfold Admissible at *
  simpa only [← h.2.1, ← h.2.2] using hp

theorem mixed_widen {p p' q q' r r' s s' : Shape}
    (hp : Widen p p') (hq : Widen q q') (hr : Widen r r') (hs : Widen s s')
    (vp : Admissible p) (vq : Admissible q) (vr : Admissible r) (vs : Admissible s) :
    mixed32 p q r s ≤ mixed32 p' q' r' s' := by
  change (mixedInt p q r s).toNat ≤ (mixedInt p' q' r' s').toNat
  apply Int.toNat_le_toNat
  have vp' := hp.admissible vp
  have vq' := hq.admissible vq
  have vr' := hr.admissible vr
  calc
    mixedInt p q r s ≤ mixedInt p' q r s := mixed_first hp vq vr vs
    _ ≤ mixedInt p' q' r s := by
      rw [mixed_swap12 p', mixed_swap12 p']
      exact mixed_first hq vp' vr vs
    _ ≤ mixedInt p' q' r' s := by
      rw [mixed_swap23 p' q' r, mixed_swap23 p' q' r', mixed_swap12 p' r,
        mixed_swap12 p' r']
      exact mixed_first hr vp' vq' vs
    _ ≤ mixedInt p' q' r' s' := by
      rw [mixed_swap34 p' q' r' s, mixed_swap34 p' q' r' s',
        mixed_swap23 p' q' s, mixed_swap23 p' q' s', mixed_swap12 p' s,
        mixed_swap12 p' s']
      exact mixed_first hs vp' vq' vr'

end K1_13_8_3
end PackSource_K1_13_8_3Mixed

section PackSource_K1_13_8_3Prices
set_option autoImplicit true
namespace K1_13_8_3

open K1_13 K1_13_8

private theorem Widen.plus {p p' q q' : Shape} (hp : Widen p p') (hq : Widen q q') :
    Widen (p.plus q) (p'.plus q') :=
  ⟨Nat.add_le_add hp.1 hq.1, congrArg₂ Nat.add hp.2.1 hq.2.1, congrArg₂ Nat.add hp.2.2 hq.2.2⟩

private theorem Widen.scale {p p' : Shape} (hp : Widen p p') (d : ℕ) :
    Widen (p.scale d) (p'.scale d) :=
  ⟨Nat.mul_le_mul_left _ hp.1, congrArg (fun n => d * n) hp.2.1,
    congrArg (fun n => d * n) hp.2.2⟩

private theorem chamber_widen {p p' : Shape} (hp : Widen p p') :
    Widen p.chamber p'.chamber :=
  ⟨max_le_max hp.1 (le_of_eq hp.2.1), hp.2⟩

private theorem chart_widen {p p' : Shape} (hp : Widen p p') (L : ℕ) :
    Widen (chart L p) (chart L p') := by
  have hb := Nat.mul_le_mul_left (2 * L) (Nat.sub_le_sub_right hp.1 1)
  simp only [Widen, chart, hp.2.1, hp.2.2]
  exact ⟨max_le_max (Nat.add_le_add_left hb _) le_rfl, trivial, trivial⟩

private theorem lifted_widen {p p' : Shape} (hp : Widen p p') (L : ℕ) :
    Widen (liftedChart L p) (liftedChart L p') := by
  have hb := Nat.mul_le_mul_left (L - 5) (Nat.sub_le_sub_right hp.1 1)
  simp only [Widen, liftedChart, hp.2.1, hp.2.2]
  exact ⟨max_le_max (Nat.add_le_add_left hb _) le_rfl, trivial, trivial⟩

private theorem admissible_min (i t : ℕ) : 3 * min t (i / 3) ≤ i := by
  have := min_le_right t (i / 3)
  omega

private theorem chart_admissible (L : ℕ) (p : Shape) : Admissible (chart L p) :=
  admissible_min _ _

private theorem lifted_admissible (L : ℕ) (p : Shape) : Admissible (liftedChart L p) :=
  admissible_min _ _

private def graph (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩

private theorem graph_widen {p p' : Shape} (hp : Widen p p') : Widen (graph p) (graph p') := by
  simp only [Widen, graph, hp.2.1, hp.2.2]
  exact ⟨max_le_max hp.1 le_rfl, trivial, trivial⟩

private theorem graph_admissible (p : Shape) : Admissible (graph p) :=
  admissible_min _ _

private abbrev bank : Shape := ⟨4013, 1650, 550⟩

private theorem bank_admissible : Admissible bank := by
  change 3 * 550 ≤ 1650
  decide

private theorem surface_widen {p p' : Shape} (hp : Widen p p') (vp : Admissible p) :
    surfaceNumerator32 p bank ≤ surfaceNumerator32 p' bank := by
  let L := taylorLength
  have mix {r r' s s' : Shape} (hr : Widen r r') (hs : Widen s s')
      (vr : Admissible r) (vs : Admissible s) :
      mixed32 p bank r s ≤ mixed32 p' bank r' s' :=
    mixed_widen hp (Widen.refl _) hr hs vp bank_admissible vr vs
  have direct := mix (chart_widen hp (L + 1)) (chart_widen hp (L + 2))
    (chart_admissible _ _) (chart_admissible _ _)
  have lift := mix (lifted_widen hp (L + 1)) (lifted_widen hp (L + 2))
    (lifted_admissible _ _) (lifted_admissible _ _)
  have graph₁ := mix (graph_widen hp) (lifted_widen hp (L + 2))
    (graph_admissible _) (lifted_admissible _ _)
  have graph₂ := mix (graph_widen hp) (lifted_widen hp (L + 1))
    (graph_admissible _) (lifted_admissible _ _)
  exact min_le_min direct <| Nat.add_le_add
    (Nat.add_le_add lift (Nat.mul_le_mul_left _ graph₁)) (Nat.mul_le_mul_left _ graph₂)

private theorem ceil_mono {a b : ℕ} (h : a ≤ b) (d : ℕ) : ceilDiv a d ≤ ceilDiv b d :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h d) 1)

private theorem physical_widen {x x' : Shape} (hx : Widen x x') (vx : Admissible x)
    (l : ℕ) : physicalPrice x l ≤ physicalPrice x' l := by
  let p := x.chamber
  let p' := x'.chamber
  let h := chart taylorLength p
  let h' := chart taylorLength p'
  let extra := bank.plus (p.scale 4)
  let extra' := bank.plus (p'.scale 4)
  have hp : Widen p p' := chamber_widen hx
  have vp : Admissible p := vx
  have hh : Widen h h' := chart_widen hp _
  have vh : Admissible h := chart_admissible _ _
  have hextra : Widen extra extra' := (Widen.refl bank).plus (hp.scale 4)
  have vextra : Admissible extra := by
    have hpj : 3 * p.t ≤ p.j := vp
    change 3 * (550 + 4 * p.t) ≤ 1650 + 4 * p.j
    omega
  have surface := ceil_mono (surface_widen hp vp) 32
  have component := ceil_mono (Nat.mul_le_mul
    (Nat.mul_le_mul_right bank.b (Nat.mul_le_mul_left (81908 + 2 * 46578) hx.1))
    (chart_widen hp (taylorLength + 1)).1) 46578
  have curves := Nat.add_le_add
    (mixed_widen hp (Widen.refl bank) hextra hh vp bank_admissible vextra vh)
    (Nat.mul_le_mul (le_of_eq (congrArg (fun t => 2 * t) hx.2.2))
      (mixed_widen hp hp hp hh vp vp vp vh))
  have points := Nat.add_le_add
    (mixed_widen hp (Widen.refl bank) hextra hp vp bank_admissible vextra vp)
    (Nat.mul_le_mul (le_of_eq (congrArg (fun t => 2 * t) hx.2.2))
      (mixed_widen hp hp hp hp vp vp vp vp))
  exact Nat.add_le_add (Nat.add_le_add (ceil_mono (Nat.add_le_add surface component) l)
    (Nat.mul_le_mul_right bank.b (Nat.mul_le_mul_left (2 * 133658) hx.1)))
    (ceil_mono (Nat.add_le_add (Nat.mul_le_mul_left 81908 curves)
      (Nat.mul_le_mul_left (2 * 46578) points)) (32 * 46578))

/-- Uniform cost per unit of the derivative-index budget. -/
def rate : ℕ := 4112448315350269

section
set_option maxRecDepth 32768
set_option maxHeartbeats 0

-- Each index has its own kernel check over the ten possible top degrees.
private abbrev capPriceRow (j : ℕ) : Prop :=
  ∀ t : Fin 10, 0 < t.val → 3 * t.val ≤ j →
    physicalPrice ⟨119, j, t.val⟩ (indexOrder j) ≤ rate * j

private theorem capPriceRow0 : capPriceRow 0 := by decide +kernel
private theorem capPriceRow1 : capPriceRow 1 := by decide +kernel
private theorem capPriceRow2 : capPriceRow 2 := by decide +kernel
private theorem capPriceRow3 : capPriceRow 3 := by decide +kernel
private theorem capPriceRow4 : capPriceRow 4 := by decide +kernel
private theorem capPriceRow5 : capPriceRow 5 := by decide +kernel
private theorem capPriceRow6 : capPriceRow 6 := by decide +kernel
private theorem capPriceRow7 : capPriceRow 7 := by decide +kernel
private theorem capPriceRow8 : capPriceRow 8 := by decide +kernel
private theorem capPriceRow9 : capPriceRow 9 := by decide +kernel
private theorem capPriceRow10 : capPriceRow 10 := by decide +kernel
private theorem capPriceRow11 : capPriceRow 11 := by decide +kernel
private theorem capPriceRow12 : capPriceRow 12 := by decide +kernel
private theorem capPriceRow13 : capPriceRow 13 := by decide +kernel
private theorem capPriceRow14 : capPriceRow 14 := by decide +kernel
private theorem capPriceRow15 : capPriceRow 15 := by decide +kernel
private theorem capPriceRow16 : capPriceRow 16 := by decide +kernel
private theorem capPriceRow17 : capPriceRow 17 := by decide +kernel
private theorem capPriceRow18 : capPriceRow 18 := by decide +kernel
private theorem capPriceRow19 : capPriceRow 19 := by decide +kernel
private theorem capPriceRow20 : capPriceRow 20 := by decide +kernel
private theorem capPriceRow21 : capPriceRow 21 := by decide +kernel
private theorem capPriceRow22 : capPriceRow 22 := by decide +kernel
private theorem capPriceRow23 : capPriceRow 23 := by decide +kernel
private theorem capPriceRow24 : capPriceRow 24 := by decide +kernel
private theorem capPriceRow25 : capPriceRow 25 := by decide +kernel
private theorem capPriceRow26 : capPriceRow 26 := by decide +kernel
private theorem capPriceRow27 : capPriceRow 27 := by decide +kernel
private theorem capPriceRow28 : capPriceRow 28 := by decide +kernel
private theorem capPriceRow29 : capPriceRow 29 := by decide +kernel
private theorem capPriceRow30 : capPriceRow 30 := by decide +kernel
private theorem capPriceRow31 : capPriceRow 31 := by decide +kernel
private theorem capPriceRow32 : capPriceRow 32 := by decide +kernel
private theorem capPriceRow33 : capPriceRow 33 := by decide +kernel
private theorem capPriceRow34 : capPriceRow 34 := by decide +kernel
private theorem capPriceRow35 : capPriceRow 35 := by decide +kernel
private theorem capPriceRow36 : capPriceRow 36 := by decide +kernel
private theorem capPriceRow37 : capPriceRow 37 := by decide +kernel
private theorem capPriceRow38 : capPriceRow 38 := by decide +kernel
private theorem capPriceRow39 : capPriceRow 39 := by decide +kernel
private theorem capPriceRow40 : capPriceRow 40 := by decide +kernel
private theorem capPriceRow41 : capPriceRow 41 := by decide +kernel
private theorem capPriceRow42 : capPriceRow 42 := by decide +kernel
private theorem capPriceRow43 : capPriceRow 43 := by decide +kernel
private theorem capPriceRow44 : capPriceRow 44 := by decide +kernel
private theorem capPriceRow45 : capPriceRow 45 := by decide +kernel

private theorem prices_at_cap : ∀ (j : Fin 46) (t : Fin 10),
    0 < t.val → 3 * t.val ≤ j.val →
      physicalPrice ⟨119, j.val, t.val⟩ (indexOrder j.val) ≤ rate * j.val := by
  intro j
  fin_cases j
  · exact capPriceRow0
  · exact capPriceRow1
  · exact capPriceRow2
  · exact capPriceRow3
  · exact capPriceRow4
  · exact capPriceRow5
  · exact capPriceRow6
  · exact capPriceRow7
  · exact capPriceRow8
  · exact capPriceRow9
  · exact capPriceRow10
  · exact capPriceRow11
  · exact capPriceRow12
  · exact capPriceRow13
  · exact capPriceRow14
  · exact capPriceRow15
  · exact capPriceRow16
  · exact capPriceRow17
  · exact capPriceRow18
  · exact capPriceRow19
  · exact capPriceRow20
  · exact capPriceRow21
  · exact capPriceRow22
  · exact capPriceRow23
  · exact capPriceRow24
  · exact capPriceRow25
  · exact capPriceRow26
  · exact capPriceRow27
  · exact capPriceRow28
  · exact capPriceRow29
  · exact capPriceRow30
  · exact capPriceRow31
  · exact capPriceRow32
  · exact capPriceRow33
  · exact capPriceRow34
  · exact capPriceRow35
  · exact capPriceRow36
  · exact capPriceRow37
  · exact capPriceRow38
  · exact capPriceRow39
  · exact capPriceRow40
  · exact capPriceRow41
  · exact capPriceRow42
  · exact capPriceRow43
  · exact capPriceRow44
  · exact capPriceRow45

end

private theorem edge_le_physical (a : Shape) (l : ℕ) : edgePrice a l ≤ physicalPrice a l := by
  unfold edgePrice
  split
  · exact min_le_left _ _
  · exact le_rfl

theorem charged_price {y a : Shape} (ha : Valid a)
    (hb : InBox (start.plus (y.plus a)) fullCap) :
    edgePrice a (indexOrder (y.plus a).j) ≤ rate * a.j := by
  have hb' : 1 + (y.b + a.b) ≤ 120 := hb.1
  have hj' : 3 + (y.j + a.j) ≤ 48 := hb.2.1
  have ht' : 1 + (y.t + a.t) ≤ 10 := hb.2.2
  have hab : a.b ≤ 119 := by omega
  have hwiden : Widen a ⟨119, a.j, a.t⟩ := ⟨hab, rfl, rfl⟩
  have hjle : a.j ≤ (y.plus a).j := Nat.le_add_left _ _
  have hle := edgePrice_anti a (l := indexOrder a.j) (u := indexOrder (y.plus a).j)
    (indexOrder_pos a.j) (indexOrder_mono hjle)
  have hprice := physical_widen hwiden ha.2.1 (indexOrder a.j)
  let j : Fin 46 := ⟨a.j, by omega⟩
  let t : Fin 10 := ⟨a.t, by omega⟩
  have hcap := prices_at_cap j t ha.1 ha.2.1
  exact hle.trans ((edge_le_physical a (indexOrder a.j)).trans (hprice.trans hcap))

end K1_13_8_3
end PackSource_K1_13_8_3Prices

section PackSource_K1_13_8_3Proof
set_option autoImplicit true
namespace K1_13_8_3

open K1_13 K1_13_8

/-- Unspent index is enough to pay for every later factor. -/
private def potential (y : Shape) : ℕ := rate * (45 - y.j)

theorem proof : K1_13_8.c3 := by
  change Bellman start 185060174190762111
  refine ⟨potential, fun x => indexOrder x.j, by decide, ?_, ?_⟩
  · intro x hx _
    exact checked_order x hx K1_13_8_1.proof
  · intro y a _ ha hb
    have hbox : 3 + (y.j + a.j) ≤ 48 := hb.2.1
    have hbalance : a.j + (45 - (y.j + a.j)) = 45 - y.j := by omega
    apply (Nat.add_le_add_right (charged_price ha hb) _).trans
    change rate * a.j + rate * (45 - (y.j + a.j)) ≤ rate * (45 - y.j)
    rw [← Nat.mul_add, hbalance]

end K1_13_8_3
end PackSource_K1_13_8_3Proof

section PackSource_K1_13_2_3_3Proof
set_option autoImplicit true
set_option Elab.async false
namespace K1_13_2_3_3

open K1_13_2 K1_13_2_3 Finset
open K1_13_2_3_1 (denPrefix denPrefix_of_nonpos)
open scoped BigOperators

/-- There are this many offsets with positive contact order in grade `s`. -/
private def offsets (s : ℕ) : ℕ := 4650 - s

private def flag (n j : ℤ) : Flag := ⟨1650, 1650 - j, 1650, 550, n - j⟩

private def active (j : ℤ) : ℤ := denominator 1650 - denominator (1649 - j)

private def removed (n : ℤ) : ℤ := (n - 1) / 4 + 1

private def target (n j : ℤ) : ℤ :=
  smallCount 1650 (n - 1 - j) - denominator ((n - 3 * removed n) - 1 - j) -
    denominator ((removed n - 1) - 1 - j) -
    denominator ((removed n - 2) - 1 - j) -
    denominator ((removed n - 3) - 1 - j)

private theorem cumulative_denominator (d u : ℤ) (hd : 2 ≤ d) (hu : u ≤ d) :
    cumulative d u = denominator u :=
  (cumulative_eq_small d u hd (by omega)).trans (smallCount_eq_denominator d u hu)

private theorem initial_eq (s : Fin 4013) (j : Fin 4650) (hs : 2510 ≤ s.val) :
    initialFlag (s, j) = flag (offsets s.val) j.val := by
  have hn : (offsets s.val : ℤ) = 4650 - (s.val : ℤ) := by unfold offsets; omega
  change K1_13_2.Flag.mk (min (s.val : ℤ) 1650) (-((j.val : ℤ) - 1650)) 1650 550
    (3000 - (s.val : ℤ) - ((j.val : ℤ) - 1650)) = _
  rw [min_eq_right (show (1650 : ℤ) ≤ s.val by omega), flag, hn]
  congr 1 <;> ring

private theorem old_eq (n j : ℤ) (hj : 0 ≤ j) : oldCount (flag n j) = active j := by
  have hcap (u : ℤ) (hu : u ≤ 1650) : cappedCount 1650 u 550 = denominator u := by
    change cumulative 1650 u - cumulative 1099 (u - 1653) = denominator u
    rw [cumulative_denominator 1650 u (by decide) hu]
    simp [cumulative, show u - 1653 < 0 by omega]
  change cappedCount 1650 1650 550 - cappedCount 1650 (min 1650 (1650 - j - 1)) 550 = _
  rw [min_eq_right (by omega), hcap 1650 (by decide), hcap (1650 - j - 1) (by omega), active,
    show 1650 - j - 1 = 1649 - j by ring]

private theorem target_original (n j : ℤ) (hn₁ : 638 ≤ n) (hn₂ : n ≤ 2140) :
    targetCount (flag n j) =
      cumulative 1650 (n - 1 - j) -
      cumulative (1650 - removed n) ((n - 3 * removed n) - 1 - j) -
      cumulative 1650 (1649 - j) + cumulative (1650 - removed n) (1649 - j) := by
  unfold targetCount flag
  dsimp only
  rw [show n - j - 1 - (1650 - j) + 1650 = n - 1 by ring,
    ite_eq_right (by omega), min_eq_right (by omega), ← removed]
  rw [show n - j - 1 = n - 1 - j by ring,
    show n - 1 - j - 3 * removed n = (n - 3 * removed n) - 1 - j by ring,
    show 1650 - j - 1 = 1649 - j by ring]

private theorem target_eq (n j : ℤ) (hn₁ : 638 ≤ n) (hn₂ : n ≤ 2140) (hj : 0 ≤ j) :
    targetCount (flag n j) = target n j := by
  have hr : 160 ≤ removed n ∧ removed n ≤ 535 := by unfold removed; omega
  have hd : 2 ≤ 1650 - removed n := by omega
  rw [target_original n j hn₁ hn₂, cumulative_eq_small 1650 (n - 1 - j) (by decide) (by omega),
    cumulative_denominator (1650 - removed n) _ hd (by unfold removed; omega),
    cumulative_denominator 1650 (1649 - j) (by decide) (by omega),
    cumulative_eq_small (1650 - removed n) (1649 - j) hd (by omega)]
  have hres :
      smallCount (1650 - removed n) (1649 - j) =
        denominator (1649 - j) - denominator ((removed n - 1) - 1 - j) -
          denominator ((removed n - 2) - 1 - j) - denominator ((removed n - 3) - 1 - j) := by
    unfold smallCount
    rw [show 1649 - j - (1650 - removed n) - 1 = (removed n - 1) - 1 - j by ring,
      show 1649 - j - (1650 - removed n) - 2 = (removed n - 2) - 1 - j by ring,
      show 1649 - j - (1650 - removed n) - 3 = (removed n - 3) - 1 - j by ring]
  rw [hres, target]
  ring

private theorem active_nonneg (j : ℤ) (hj : 0 ≤ j) : 0 ≤ active j :=
  sub_nonneg.mpr (denominator_mono_to _ _ (by omega) (by decide))

private theorem target_nonneg (n j : ℤ) (hn₁ : 638 ≤ n) (hn₂ : n ≤ 2140)
    (hj : 0 ≤ j) (hjn : j < n) : 0 ≤ target n j := by
  by_cases hn : n ≤ 1650
  · -- Here the contact cutoff can be below the old lower cutoff.
    -- The four subtracted terms are bounded by one quarter of the leading term.
    let u := n - 1 - j
    let t := removed n - 1 - j
    have htu : t + 478 ≤ u := by dsimp [t, u, removed]; omega
    have htmax : t ≤ 412 := by dsimp [t, removed]; omega
    have hu₁ : 0 ≤ u := by dsimp [u]; omega
    have hu₂ : u ≤ 1650 := by dsimp [u]; omega
    have ht (v : ℤ) (hv : v ≤ t) : denominator v ≤ denominator t :=
      denominator_mono_to _ _ hv (by omega)
    have hbig : 4 * denominator t ≤ denominator u := by
      by_cases h : 0 ≤ t
      · exact (denominator_quadruple t h).trans (denominator_mono_to _ _ (by omega) hu₂)
      · rw [denominator_of_neg t (by omega), mul_zero, ← denominator_of_neg (-1) (by decide)]
        exact denominator_mono_to _ _ (by omega) hu₂
    have h₁ := ht ((n - 3 * removed n) - 1 - j) (by dsimp [t, removed]; omega)
    have h₂ := ht ((removed n - 1) - 1 - j) (by dsimp [t]; omega)
    have h₃ := ht ((removed n - 2) - 1 - j) (by dsimp [t]; omega)
    have h₄ := ht ((removed n - 3) - 1 - j) (by dsimp [t]; omega)
    unfold target
    rw [smallCount_eq_denominator 1650 u hu₂]
    omega
  · rw [← target_eq n j hn₁ hn₂ hj, target_original n j hn₁ hn₂]
    have h₁ : cumulative 1650 (1649 - j) ≤ cumulative 1650 (n - 1 - j) :=
      K1_13_2_3.cumulative_mono 1650 (by omega)
    have hd : 0 ≤ 1650 - removed n := by unfold removed; omega
    have hm : Monotone (cumulative (1650 - removed n)) := by
      simpa only [Int.toNat_of_nonneg hd] using
        K1_13_2_3.cumulative_mono (1650 - removed n).toNat
    have h₂ := hm (show (n - 3 * removed n) - 1 - j ≤ 1649 - j by unfold removed; omega)
    omega

/-- Each entry holds the first cut for 32 grades in its low ten bits.
The higher bits mark the subsequent one-step decreases in those grades. -/
private def packedCuts : List ℕ :=
  [1884877150839, 1492194651746, 942438537804, 1570711722551, 1492155854371,
   1560874277390, 922171043323, 780298540519, 1471922525652, 778910935489,
   778910390703, 1488933185949, 1466373428620, 1471742129531, 1466015503722,
   1282763565401, 1466015503690, 1454562252090, 1463151842603, 727278331164,
   709921952013, 1276991850751, 640642880754, 638428270820, 1414291165399,
   1259115981003, 314223174847, 1256585316531, 1256584717480, 314146179229,
   1256582320274, 311689515144, 1246690353278, 1177429774453, 293274685548,
   146601559140, 292630437979, 1170521474132, 1170450030668, 141872603205,
   69827855423, 70901579832, 558482097203, 279206961197, 554118418472,
   69260558371, 34495008799]

private def lowOnes : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, bits => bits % 2 + lowOnes k (bits / 2)

private def cut (n : ℕ) : ℕ :=
  let k := 2140 - n
  let code := (packedCuts[k / 32]?).getD 0
  min n (code % 1024 - lowOnes (k % 32) (code / 1024))

private def upper (n j : ℕ) : ℤ :=
  if j < cut n then active j else if j < n then target n j else 0

private theorem cast_toNat_le {x y : ℤ} (hy : 0 ≤ y) (hxy : x ≤ y) :
    (x.toNat : ℤ) ≤ y := by omega

private theorem block_le_upper (s : Fin 4013) (j : Fin 4650) (hs : 2510 ≤ s.val) :
    (baseline (s, j) : ℤ) ≤ upper (offsets s.val) j.val := by
  let n := offsets s.val
  have hn₁ : 638 ≤ n := by dsimp [n, offsets]; omega
  have hn₂ : n ≤ 2140 := by dsimp [n, offsets]; omega
  have hc : cut n ≤ n := min_le_left _ _
  have hf : initialFlag (s, j) = flag n j.val := initial_eq s j hs
  change (baseline (s, j) : ℤ) ≤ upper n j.val
  by_cases hj : j.val < n
  · have horder : ¬ (flag n j.val).order ≤ 0 := by change ¬ (n : ℤ) - j.val ≤ 0; omega
    have hactive :
        { flag n j.val with upper := min (flag n j.val).upper (2999 - offset (s,j)) } =
          flag n j.val := by
      have hu : (1650 : ℤ) ≤ 2999 - offset (s,j) := by unfold offset; dsimp; omega
      simp only [flag, min_eq_left hu]
    rw [baseline, blockBound, hf]
    dsimp only
    rw [ite_eq_right horder, hactive]
    by_cases hcut : j.val < cut n
    · rw [upper, ite_eq_left hcut, ← old_eq n j.val (by omega)]
      apply cast_toNat_le
      · rw [old_eq n j.val (by omega)]
        exact active_nonneg _ (by omega)
      · exact min_le_left _ _
    · rw [upper, ite_eq_right hcut, ite_eq_left hj]
      apply cast_toNat_le (target_nonneg n j.val (by omega) (by omega) (by omega) (by omega))
      apply (min_le_right _ _).trans
      rw [← target_eq n j.val (by omega) (by omega) (by omega)]
      have hk : kernelLower (flag n j.val) =
          oldCount (flag n j.val) - targetCount (flag n j.val) := by simp [kernelLower, flag]
      have hm := (le_max_left (kernelLower (flag n j.val))
        (kernelLower (residualFlag (flag n j.val) (fun _ => 0)))).trans (le_max_right 0 _)
      rw [hk] at hm
      omega
  · have horder : (initialFlag (s,j)).order ≤ 0 := by rw [hf]; change (n : ℤ) - j.val ≤ 0; omega
    have hcut : ¬ j.val < cut n := by omega
    simp [baseline, blockBound, horder, upper, hcut, hj]

/-- The scaled sum of the active bounds before offset `j`. -/
private def activePrefix (j : ℤ) : ℤ :=
  j * (24 * denominator 1650) - denPrefix 1650 + denPrefix (1650 - j)

/-- The scaled sum of the target bounds from offset `j` to the end of the row. -/
private def targetTail (n j : ℤ) : ℤ :=
  smallPrefix 1650 (n - j) - denPrefix ((n - 3 * removed n) - j) -
    denPrefix ((removed n - 1) - j) -
    denPrefix ((removed n - 2) - j) -
    denPrefix ((removed n - 3) - j)

private theorem activePrefix_step (j : ℤ) : activePrefix (j + 1) - activePrefix j = 24 * active j := by
  unfold activePrefix active
  linear_combination (norm := ring_nf) -prefix_offset_step 1650 j

private theorem targetTail_step (n j : ℤ) :
    targetTail n j - targetTail n (j + 1) = 24 * target n j := by
  unfold targetTail target
  linear_combination (norm := ring_nf) smallPrefix_offset_step 1650 n j -
    prefix_offset_step (n - 3 * removed n) j - prefix_offset_step (removed n - 1) j -
    prefix_offset_step (removed n - 2) j - prefix_offset_step (removed n - 3) j

private theorem targetTail_end (n : ℕ) : targetTail n n = 0 := by
  simp only [targetTail, sub_self, smallPrefix_of_nonpos 1650 0 (by decide) (by decide),
    denPrefix_of_nonpos ((n : ℤ) - 3 * removed n - n) (by unfold removed; omega),
    denPrefix_of_nonpos (removed n - 1 - n) (by unfold removed; omega),
    denPrefix_of_nonpos (removed n - 2 - n) (by unfold removed; omega),
    denPrefix_of_nonpos (removed n - 3 - n) (by unfold removed; omega)]

private def rowBudget (n : ℕ) : ℤ := activePrefix (cut n) + targetTail n (cut n)

private theorem scaled_sum (f p : ℤ → ℤ) (h : ∀ j, p (j + 1) - p j = 24 * f j)
    (a : ℤ) (n : ℕ) : 24 * (∑ j ∈ range n, f (a + j)) = p (a + n) - p a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ, ← h, ← add_assoc]
    ring

private theorem sum_upper (n : ℕ) (hn : n ≤ 4650) :
    24 * (∑ j ∈ range 4650, upper n j) = rowBudget n := by
  let c := cut n
  have hc : c ≤ n := min_le_left _ _
  have htrunc : (∑ j ∈ range 4650, upper n j) = ∑ j ∈ range n, upper n j := by
    symm
    apply sum_subset (range_mono hn)
    intro j _ h
    rw [mem_range] at h
    have hcut : ¬ j < cut n := by change ¬ j < c; omega
    simp [upper, h, hcut]
  have hsplit (f : ℕ → ℤ) : (∑ j ∈ range n, f j) =
      (∑ j ∈ range c, f j) + ∑ j ∈ range (n - c), f (c + j) := by
    conv_lhs => rw [← Nat.add_sub_of_le hc, sum_range_add]
  rw [htrunc, hsplit, mul_add]
  have hactive : (∑ j ∈ range c, upper n j) = ∑ j ∈ range c, active j := by
    exact sum_congr rfl fun j hj => by rw [upper, ite_eq_left (mem_range.mp hj)]
  have htarget : (∑ j ∈ range (n - c), upper n (c + j)) =
      ∑ j ∈ range (n - c), target n ((c : ℤ) + j) := by
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    rw [upper, ite_eq_right (show ¬ c + j < cut n by change ¬ c + j < c; omega),
      ite_eq_left (by omega), Nat.cast_add]
  have h₁ := scaled_sum active activePrefix activePrefix_step 0 c
  have hzero : activePrefix 0 = 0 := by simp [activePrefix]
  simp only [zero_add, hzero, sub_zero] at h₁
  have h₂ := scaled_sum (target n) (fun j => -targetTail n j)
    (fun j => by linear_combination targetTail_step n j) c (n - c)
  have hend : (c : ℤ) + (↑(n - c) : ℤ) = n := by omega
  simp only [hend, targetTail_end, neg_zero, zero_sub, neg_neg] at h₂
  rw [hactive, htarget, h₁, h₂]
  rfl

private theorem grade_bound (s : Fin 4013) (hs : 2510 ≤ s.val) :
    24 * (∑ j : Fin 4650, (baseline (s,j) : ℤ)) ≤ rowBudget (offsets s.val) := by
  have h := mul_le_mul_of_nonneg_left
    (sum_le_sum (s := (univ : Finset (Fin 4650))) (fun j _ => block_le_upper s j hs))
    (show (0 : ℤ) ≤ 24 by decide)
  rw [Fin.sum_univ_eq_sum_range (upper (offsets s.val)), sum_upper _ (by unfold offsets; omega)] at h
  exact h

private def total (start : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => total start k + rowBudget (2140 - (start + k))

private theorem total_eq (n : ℕ) : total 0 n = ∑ k ∈ range n, rowBudget (2140 - k) := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [total, sum_range_succ, ih, zero_add]

private theorem total_add (start a b : ℕ) :
    total start (a + b) = total start a + total (start + a) b := by
  induction b with
  | zero => simp [total]
  | succ b ih =>
    rw [Nat.add_succ, total, ih, total]
    simp only [add_assoc]

section
set_option maxRecDepth 50000
set_option maxHeartbeats 0

private theorem check₀ : total 0 256 = 366834691880448 := by decide +kernel
private theorem check₁ : total 256 256 = 242162127775344 := by decide +kernel
private theorem check₂ : total 512 256 = 145789791736344 := by decide +kernel
private theorem check₃ : total 768 256 = 77485223947464 := by decide +kernel
private theorem check₄ : total 1024 256 = 34445829248736 := by decide +kernel
private theorem check₅ : total 1280 223 = 10846507362312 := by decide +kernel

end

private theorem total_check : total 0 1503 = 877564171950648 := by
  calc
    _ = total 0 256 + total 256 256 + total 512 256 +
        total 768 256 + total 1024 256 + total 1280 223 := by
      rw [← total_add 0 256 256, ← total_add 0 512 256, ← total_add 0 768 256,
        ← total_add 0 1024 256, ← total_add 0 1280 223]
    _ = _ := by
      rw [check₀, check₁, check₂, check₃, check₄, check₅]
      decide

private theorem sum_grades :
    (∑ s : Fin 4013, if 2510 ≤ s.val then rowBudget (offsets s.val) else 0) = total 0 1503 := by
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => if 2510 ≤ s then rowBudget (offsets s) else 0),
    show (4013 : ℕ) = 2510 + 1503 by decide, sum_range_add, total_eq]
  have hzero : (∑ s ∈ range 2510, if 2510 ≤ s then rowBudget (offsets s) else 0) = 0 := by
    apply sum_eq_zero
    intro s hs
    rw [ite_eq_right (not_le.mpr (mem_range.mp hs))]
  rw [hzero, zero_add]
  apply sum_congr rfl
  intro k _
  rw [ite_eq_left (by omega), show offsets (2510 + k) = 2140 - k by unfold offsets; omega]

theorem proof : K1_13_2_3.c3 := by
  have h : 24 * (baselineSum 2510 4013 : ℤ) ≤ 877564171950648 := by
    unfold baselineSum baselineSumOn
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Nat.cast_sum]
    rw [mul_sum, ← total_check, ← sum_grades]
    apply sum_le_sum
    intro s _
    by_cases hs : 2510 ≤ s.val
    · simpa only [hs, s.isLt, and_self, ite_true] using grade_bound s hs
    · simp [hs]
  unfold K1_13_2_3.c3
  omega

end K1_13_2_3_3
end PackSource_K1_13_2_3_3Proof

section PackSource_K1_13_6_1_4_2_1_1Defs
set_option autoImplicit true
namespace K1_13_6_1_4_2_1_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1
open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

abbrev Generator (a h : Shape) := latticeIndices a ⊕ latticeIndices h
abbrev BigradedPolynomial (a h : Shape) := MvPolynomial (Generator a h) (Coeff a h)

/-- The two blocks of monomial generators have degrees (1,0) and (0,1). -/
def weight {α β : Type} : α ⊕ β → ℕ × ℕ := Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))

abbrev grade {k α β : Type} [CommSemiring k] (d : ℕ × ℕ) :
    Submodule k (MvPolynomial (α ⊕ β) k) :=
  weightedHomogeneousSubmodule k weight d

def generatorExponent {a h : Shape} : Generator a h → Fin 4 →₀ ℕ :=
  Sum.elim Subtype.val Subtype.val

/-- Evaluate the homogeneous coordinates as affine monomials. -/
def dehom (surface : Ideal GeoJets) (a h : Shape) :
    BigradedPolynomial a h →ₐ[Coeff a h] SurfaceRing surface a h :=
  (Ideal.Quotient.mkₐ _ _).comp (aeval fun v => monomial (generatorExponent v) 1)

/-- Homogeneous relations of the monomial embedding. -/
def relations (surface : Ideal GeoJets) (a h : Shape) : Ideal (BigradedPolynomial a h) :=
  ((RingHom.ker (dehom surface a h).toRingHom).homogeneousCore grade).toIdeal

/-- The exponent in the affine variables indexed by a coefficient in a box. -/
def boxExponent {p : Shape} (m : SectionIndex p) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (m i).val)

theorem boxExponent_mem (p : Shape) (m : boxMonomials (p.scale 6)) :
    boxExponent m.val ∈ latticeIndices p := by
  change (fun i => boxExponent m.val i) ∈ exponents (p.scale 6)
  simpa only [boxExponent, Finsupp.coe_equivFunOnFinite_symm] using
    (mem_exponents_iff _ m.val).2 m.property

def leftForm (a h : Shape) : BigradedPolynomial a h :=
  ∑ m ∈ (boxMonomials (a.scale 6)).attach,
    C (algebraMap
        (MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField) (Coeff a h)
        (MvPolynomial.X (Sum.inl m.val))) *
      MvPolynomial.X (Sum.inl ⟨boxExponent m.val, boxExponent_mem a m⟩)

def rightForm (a h : Shape) : BigradedPolynomial a h :=
  ∑ m ∈ (boxMonomials (h.scale 6)).attach,
    C (algebraMap
        (MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField) (Coeff a h)
        (MvPolynomial.X (Sum.inr m.val))) *
      MvPolynomial.X (Sum.inr ⟨boxExponent m.val, boxExponent_mem h m⟩)

def firstCut (surface : Ideal GeoJets) (a h : Shape) : Ideal (BigradedPolynomial a h) :=
  relations surface a h ⊔ Ideal.span {leftForm a h}

/-- The homogeneous coordinate whose nonvanishing selects the product chart. -/
def chart {k α β : Type} [CommSemiring k] (x : α) (y : β) :
    MvPolynomial (α ⊕ β) k :=
  MvPolynomial.X (Sum.inl x) * MvPolynomial.X (Sum.inr y)

end
end K1_13_6_1_4_2_1_1
end PackSource_K1_13_6_1_4_2_1_1Defs

section PackSource_K1_13_6_1_4_2_1_2_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_2_1_2_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2
  K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_1 K1_13_6_1_4_2_1_2 MvPolynomial

abbrev Base (surface : Ideal GeoJets) := GeoJets ⧸ surface

abbrev FunctionField (surface : Ideal GeoJets) := FractionRing (Base surface)

def monomialAt (surface : Ideal GeoJets) (x : Fin 4 →₀ ℕ) : Base surface :=
  Ideal.Quotient.mk surface (monomial x 1)

def monomialFraction (surface : Ideal GeoJets) (x : Fin 4 →₀ ℕ) : FunctionField surface :=
  algebraMap (Base surface) (FunctionField surface) (monomialAt surface x)

def chartValue (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h) : Generator a h → FunctionField surface :=
  Sum.elim (fun x => monomialFraction surface x.val / monomialFraction surface e.1.val)
    (fun y => monomialFraction surface y.val / monomialFraction surface e.2.val)

/-- The product chart algebra before adjoining the two sets of section coefficients. -/
def chartAlgebra (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h) : Subalgebra GeoField (FunctionField surface) :=
  Algebra.adjoin GeoField (Set.range (chartValue surface a h e))

instance (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h) : Algebra.FiniteType GeoField (chartAlgebra surface a h e) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

def chartCoord (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h) (i : Generator a h) : chartAlgebra surface a h e :=
  ⟨chartValue surface a h e i, Algebra.subset_adjoin ⟨i, rfl⟩⟩

def zeroCoord (p : Shape) : latticeIndices p := ⟨0, latticeIndices_zero p⟩

def sectionCoord (p : Shape) (m : boxMonomials (p.scale 6)) : latticeIndices p :=
  ⟨boxExponent m.val, boxExponent_mem p m⟩

def ratioValue {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (e : latticeIndices a × latticeIndices h)
    {E : Type} [Field E] [Algebra k E] (φ : rees I a h →ₐ[k] E) :
    Generator a h → E :=
  Sum.elim
    (fun x => φ (leftGen I a h x) /
      φ (leftGen I a h e.1))
    (fun y => φ (rightGen I a h y) /
      φ (rightGen I a h e.2))

end
end K1_13_6_1_4_2_1_2_2
end PackSource_K1_13_6_1_4_2_1_2_2Defs

section PackSource_K1_13_6_1_4_2_1_1Pieces
set_option autoImplicit true
namespace K1_13_6_1_4_2_1_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1
open MvPolynomial
open scoped Pointwise BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem leftForm_grade (a h : Shape) : leftForm a h ∈ grade (1, 0) := by
  apply Submodule.sum_mem
  intro m _
  exact (isWeightedHomogeneous_X (Coeff a h) weight
    (Sum.inl ⟨boxExponent m.val, boxExponent_mem a m⟩ : Generator a h)).C_mul _

theorem rightForm_grade (a h : Shape) : rightForm a h ∈ grade (0, 1) := by
  apply Submodule.sum_mem
  intro m _
  exact (isWeightedHomogeneous_X (Coeff a h) weight
    (Sum.inr ⟨boxExponent m.val, boxExponent_mem h m⟩ : Generator a h)).C_mul _

private theorem box_monomial {k : Type} [CommRing k] {p : Shape} (m : SectionIndex p) :
    (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) k) ^ (m i).val) =
      monomial (boxExponent m) 1 := by
  have he : Finsupp.indicator Finset.univ (fun i _ => (m i).val) = boxExponent m := by
    ext i
    simp [Finsupp.indicator_apply, boxExponent]
  rw [prod_X_pow, he]

theorem dehom_left (surface : Ideal GeoJets) (a h : Shape) :
    dehom surface a h (leftForm a h) =
      Ideal.Quotient.mk (extendIdeal surface a h) (leftSection a h) := by
  unfold leftForm leftSection sectionWith dehom
  simp only [AlgHom.comp_apply, map_sum, map_mul, aeval_C, aeval_X,
    generatorExponent, Sum.elim_inl, MvPolynomial.algebraMap_eq, box_monomial, Ideal.Quotient.mkₐ_eq_mk]
  exact Finset.sum_attach (boxMonomials (a.scale 6)) fun m =>
    Ideal.Quotient.mk (extendIdeal surface a h) (C (algebraMap
      (MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField) (Coeff a h)
      (MvPolynomial.X (Sum.inl m)))) *
    Ideal.Quotient.mk (extendIdeal surface a h) (monomial (boxExponent m) 1)

theorem dehom_right (surface : Ideal GeoJets) (a h : Shape) :
    dehom surface a h (rightForm a h) =
      Ideal.Quotient.mk (extendIdeal surface a h) (rightSection a h) := by
  unfold rightForm rightSection sectionWith dehom
  simp only [AlgHom.comp_apply, map_sum, map_mul, aeval_C, aeval_X,
    generatorExponent, Sum.elim_inr, MvPolynomial.algebraMap_eq, box_monomial, Ideal.Quotient.mkₐ_eq_mk]
  exact Finset.sum_attach (boxMonomials (h.scale 6)) fun m =>
    Ideal.Quotient.mk (extendIdeal surface a h) (C (algebraMap
      (MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField) (Coeff a h)
      (MvPolynomial.X (Sum.inr m)))) *
    Ideal.Quotient.mk (extendIdeal surface a h) (monomial (boxExponent m) 1)

theorem relations_homogeneous (surface : Ideal GeoJets) (a h : Shape) :
    (relations surface a h).IsHomogeneous grade :=
  ((RingHom.ker (dehom surface a h).toRingHom).homogeneousCore grade).isHomogeneous

theorem dehom_eq_zero_of_mem_relations {surface : Ideal GeoJets} {a h : Shape}
    {f : BigradedPolynomial a h} (hf : f ∈ relations surface a h) :
    dehom surface a h f = 0 :=
  Ideal.toIdeal_homogeneousCore_le grade _ hf

theorem mem_relations_of_dehom_eq_zero {surface : Ideal GeoJets} {a h : Shape}
    {d : ℕ × ℕ} {f : BigradedPolynomial a h} (hm : f ∈ grade d)
    (hf : dehom surface a h f = 0) : f ∈ relations surface a h :=
  Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hm⟩ hf

private def boxAt (a h : Shape) (d : ℕ × ℕ) : Shape :=
  (a.scale d.1).plus (h.scale d.2)

private theorem boxAt_add (a h : Shape) (s t : ℕ × ℕ) :
    boxAt a h (s + t) = (boxAt a h s).plus (boxAt a h t) := by
  cases a
  cases h
  simp [boxAt, Shape.scale, Shape.plus, Nat.add_mul, add_assoc, add_left_comm]

private theorem boxAt_chamber {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (d : ℕ × ℕ) : Chamber (boxAt a h d) :=
  chamber_plus (K1_13_6_1_4_2.chamber_scale ha d.1) (K1_13_6_1_4_2.chamber_scale hh d.2)

private theorem boxAt_zero (a h : Shape) :
    latticeIndices (boxAt a h 0) = {0} := by
  have hz : boxAt a h 0 = ⟨0, 0, 0⟩ := by simp [boxAt, Shape.scale, Shape.plus]
  rw [hz]
  ext e
  change (fun i => e i) ∈ exponents ⟨0, 0, 0⟩ ↔ e ∈ ({0} : Set (Fin 4 →₀ ℕ))
  rw [exponents_zero, Set.mem_singleton_iff, Set.mem_singleton_iff]
  constructor
  · intro he
    ext i
    exact congrFun he i
  · rintro rfl
    rfl

private theorem boxAt_left (a h : Shape) : boxAt a h (1, 0) = a := by
  cases a
  simp [boxAt, Shape.plus, Shape.scale]

private theorem boxAt_right (a h : Shape) : boxAt a h (0, 1) = h := by
  cases h
  simp [boxAt, Shape.plus, Shape.scale]

private theorem exponent_mem_box {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (d : Generator a h →₀ ℕ) :
    Finsupp.weight generatorExponent d ∈ latticeIndices (boxAt a h (Finsupp.weight weight d)) := by
  have hplus (u v : ℕ × ℕ) : latticeIndices (boxAt a h (u + v)) =
      latticeIndices (boxAt a h u) + latticeIndices (boxAt a h v) := by
    rw [boxAt_add, latticeIndices_plus (boxAt_chamber ha hh _) (boxAt_chamber ha hh _)]
  have hgen (v : Generator a h) : generatorExponent v ∈ latticeIndices (boxAt a h (weight v)) := by
    cases v with
    | inl x => exact (boxAt_left a h).symm ▸ x.property
    | inr y => exact (boxAt_right a h).symm ▸ y.property
  induction d using Finsupp.induction_linear with
  | zero => simp [boxAt_zero]
  | add u v hu hv => simpa only [map_add, hplus] using Set.add_mem_add hu hv
  | single v n =>
    rw [Finsupp.weight_single, Finsupp.weight_single]
    induction n with
    | zero => simp [boxAt_zero]
    | succ n ih => simpa only [succ_nsmul, hplus] using Set.add_mem_add ih (hgen v)

set_option maxHeartbeats 800000 in
private theorem exponent_lift {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (i j : ℕ) {e : Fin 4 →₀ ℕ} (he : e ∈ latticeIndices (boxAt a h (i, j))) :
    ∃ d : Generator a h →₀ ℕ,
      Finsupp.weight weight d = (i, j) ∧ Finsupp.weight generatorExponent d = e := by
  have hplus (u v : ℕ × ℕ) : latticeIndices (boxAt a h (u + v)) =
      latticeIndices (boxAt a h u) + latticeIndices (boxAt a h v) := by
    rw [boxAt_add, latticeIndices_plus (boxAt_chamber ha hh _) (boxAt_chamber ha hh _)]
  induction i generalizing j e with
  | zero =>
    induction j generalizing e with
    | zero =>
      have he' : e = 0 := Set.mem_singleton_iff.mp ((boxAt_zero a h) ▸ he)
      exact ⟨0, rfl, by simp [he']⟩
    | succ j ih =>
      have hm : e ∈ latticeIndices (boxAt a h (0, j)) + latticeIndices h := by
        have hsum := hplus (0, j) (0, 1)
        rw [boxAt_right] at hsum
        rw [← hsum]
        exact he
      obtain ⟨u, hu, v, hv, rfl⟩ := hm
      obtain ⟨d, hd, hdu⟩ := ih (e := u) hu
      refine ⟨d + Finsupp.single (Sum.inr ⟨v, hv⟩) 1, ?_, ?_⟩
      · (rw [map_add, hd, Finsupp.weight_single]; rfl)
      · (rw [map_add, hdu, Finsupp.weight_single, one_nsmul]; rfl)
  | succ i ih =>
    have hm : e ∈ latticeIndices (boxAt a h (i, j)) + latticeIndices a := by
      have hsum := hplus (i, j) (1, 0)
      rw [boxAt_left] at hsum
      rw [← hsum]
      exact he
    obtain ⟨u, hu, v, hv, rfl⟩ := hm
    obtain ⟨d, hd, hdu⟩ := ih j (e := u) hu
    refine ⟨d + Finsupp.single (Sum.inl ⟨v, hv⟩) 1, ?_, ?_⟩
    · (rw [map_add, hd, Finsupp.weight_single]; rfl)
    · (rw [map_add, hdu, Finsupp.weight_single, one_nsmul]; rfl)

private theorem dehom_monomial (surface : Ideal GeoJets) (a h : Shape)
    (d : Generator a h →₀ ℕ) (c : Coeff a h) :
    dehom surface a h (monomial d c) =
      Ideal.Quotient.mk (extendIdeal surface a h) (monomial (Finsupp.weight generatorExponent d) c) := by
  unfold dehom
  rw [AlgHom.comp_apply, aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  simp only [monomial_pow, one_pow, ← monomial_sum_one, MvPolynomial.algebraMap_eq,
    C_mul_monomial, mul_one]
  rfl

/-- The homogeneous coordinate polynomials give exactly the prescribed affine filtration pieces. -/
theorem dehom_grade (surface : Ideal GeoJets) {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (i j : ℕ) : (grade (i, j)).map (dehom surface a h).toLinearMap = biPiece surface a h i j := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    change dehom surface a h f ∈ biPiece surface a h i j
    rw [f.as_sum, map_sum]
    apply Submodule.sum_mem
    intro d hd
    have hweight : Finsupp.weight weight d = (i, j) := hf (mem_support_iff.mp hd)
    have hexp := exponent_mem_box ha hh d
    rw [hweight] at hexp
    rw [dehom_monomial]
    refine ⟨_, ?_, rfl⟩
    intro e he
    have he' : Finsupp.weight generatorExponent d = e := by
      change e ∈ (monomial (Finsupp.weight generatorExponent d) (f.coeff d)).support at he
      have hne := mem_support_iff.mp he
      rw [coeff_monomial] at hne
      split at hne
      next hEq => exact hEq
      next => exact (hne rfl).elim
    exact he' ▸ hexp
  · unfold biPiece piece
    rw [restrictSupport_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    obtain ⟨d, hd, hde⟩ := exponent_lift ha hh i j he
    refine ⟨monomial d 1, isWeightedHomogeneous_monomial _ _ _ hd, ?_⟩
    change dehom surface a h (monomial d 1) = _
    rw [dehom_monomial, hde]
    rfl

end
end K1_13_6_1_4_2_1_1
end PackSource_K1_13_6_1_4_2_1_1Pieces

section PackSource_K1_13_6_1_4_2_1_2_2Sections
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_2_1_2_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2
  K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_1 K1_13_6_1_4_2_1_2 MvPolynomial

abbrev LeftLabels (a : Shape) := (boxMonomials (a.scale 6) : Type)

abbrev RightLabels (h : Shape) := (boxMonomials (h.scale 6) : Type)

abbrev Parameters (a h : Shape) := PairSectionIndex (a.scale 6) (h.scale 6)

def parameter (a h : Shape) (i : Parameters a h) : Coeff a h :=
  algebraMap (MvPolynomial (Parameters a h) GeoField) (Coeff a h) (MvPolynomial.X i)

theorem sectionCoord_surjective (p : Shape) : Function.Surjective (sectionCoord p) := by
  intro x
  have hx : (fun i => x.val i) ∈ exponents (p.scale 6) := x.property
  rw [exponents_eq_image] at hx
  obtain ⟨m, hm, he⟩ := hx
  refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
  ext i
  exact congrFun he i

private theorem homogeneous_sum {k ι : Type} [Field k] {I : Ideal (MvPolynomial (Fin 4) k)}
    {a h : Shape} (d : ℕ × ℕ) (s : Finset ι) (w : ι → k) (x : ι → Affine I)
    (hx : ∀ i, x i ∈ box I a h d) (y : Affine I) (hy : y ∈ box I a h d)
    (heq : y = ∑ i ∈ s, w i • x i) :
    homogeneous d y hy = ∑ i ∈ s, w i • homogeneous d (x i) (hx i) := by
  apply Subtype.ext
  change AddMonoidAlgebra.single d y = (rees I a h).val _
  rw [map_sum]
  simp_rw [map_smul, val_homogeneous, ← AddMonoidAlgebra.lsingle_apply (R := k),
    ← map_smul, ← map_sum, ← heq]

theorem leftHom_sum (surface : Ideal GeoJets) (a h : Shape) :
    leftHom surface a h = ∑ m : LeftLabels a,
      parameter a h (Sum.inl m.val) • leftGen (baseIdeal surface a h) a h (sectionCoord a m) := by
  classical
  unfold leftHom
  apply homogeneous_sum (I := baseIdeal surface a h) (a := a) (h := h) (d := (1, 0))
  change Ideal.Quotient.mk (extendIdeal surface a h) (leftSection a h) = _
  rw [← dehom_left surface a h]
  simp only [leftForm, Finset.attach_eq_univ, map_sum, map_mul, dehom, AlgHom.comp_apply,
    aeval_C, aeval_X, generatorExponent, Sum.elim_inl, Ideal.Quotient.mkₐ_eq_mk,
    MvPolynomial.algebraMap_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact (Algebra.smul_def (parameter a h (Sum.inl m.val))
    (Ideal.Quotient.mk (extendIdeal surface a h) (monomial (boxExponent m.val) 1))).symm

theorem rightHom_sum (surface : Ideal GeoJets) (a h : Shape) :
    rightHom surface a h = ∑ m : RightLabels h,
      parameter a h (Sum.inr m.val) • rightGen (baseIdeal surface a h) a h (sectionCoord h m) := by
  classical
  unfold rightHom
  apply homogeneous_sum (I := baseIdeal surface a h) (a := a) (h := h) (d := (0, 1))
  change Ideal.Quotient.mk (extendIdeal surface a h) (rightSection a h) = _
  rw [← dehom_right surface a h]
  simp only [rightForm, Finset.attach_eq_univ, map_sum, map_mul, dehom, AlgHom.comp_apply,
    aeval_C, aeval_X, generatorExponent, Sum.elim_inr, Ideal.Quotient.mkₐ_eq_mk,
    MvPolynomial.algebraMap_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact (Algebra.smul_def (parameter a h (Sum.inr m.val))
    (Ideal.Quotient.mk (extendIdeal surface a h) (monomial (boxExponent m.val) 1))).symm

theorem shift_eq_pair (surface : Ideal GeoJets) (a h : Shape) :
    shift (baseIdeal surface a h) a h =
      pairGen (baseIdeal surface a h) a h (zeroCoord a, zeroCoord h) := by
  apply Subtype.ext
  change AddMonoidAlgebra.single (1, 1) (1 : SurfaceRing surface a h) =
    (rees (baseIdeal surface a h) a h).val
      (leftGen (baseIdeal surface a h) a h (zeroCoord a) *
      rightGen (baseIdeal surface a h) a h (zeroCoord h))
  simp only [map_mul, leftGen, rightGen, val_homogeneous, zeroCoord, monomial_zero', map_one,
    AddMonoidAlgebra.single_mul_single, mul_one]
  rfl

end
end K1_13_6_1_4_2_1_2_2
end PackSource_K1_13_6_1_4_2_1_2_2Sections

section PackSource_K1_13_6_1_4_2_1_2_2BaseChange
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_2_1_2_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1_4_2 K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_2 MvPolynomial

def affineBaseChange (surface : Ideal GeoJets) (a h : Shape) :
    Base surface →ₐ[GeoField] SurfaceRing surface a h :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId GeoField (Coeff a h)))
    Ideal.le_comap_map

private theorem affineBaseChange_mk (surface : Ideal GeoJets) (a h : Shape) (q : GeoJets) :
    affineBaseChange surface a h (Ideal.Quotient.mk surface q) =
      Ideal.Quotient.mk (extendIdeal surface a h)
        (MvPolynomial.map (algebraMap GeoField (Coeff a h)) q) := rfl

/-- Extending the coefficients of a polynomial does not enlarge its support. -/
def reesBaseChange (surface : Ideal GeoJets) (a h : Shape) :
    rees surface a h →ₐ[GeoField] Rees surface a h := by
  let f := affineBaseChange surface a h
  let g := (AddMonoidAlgebra.mapAlgHom (ℕ × ℕ) f).comp (rees surface a h).val
  refine g.codRestrict ((rees (baseIdeal surface a h) a h).restrictScalars GeoField) ?_
  intro p d
  change (AddMonoidAlgebra.mapAlgHom (ℕ × ℕ) f p.val).coeff d ∈ _
  rw [AddMonoidAlgebra.coeff_mapAlgHom]
  obtain ⟨q, hq, he⟩ := p.property d
  refine ⟨MvPolynomial.map (algebraMap GeoField (Coeff a h)) q, ?_, ?_⟩
  · intro m hm
    exact hq (support_map_subset _ _ hm)
  · rw [← he]
    rfl

@[simp] theorem reesBaseChange_left (surface : Ideal GeoJets) (a h : Shape) (x : latticeIndices a) :
    reesBaseChange surface a h (leftGen surface a h x) =
      leftGen (baseIdeal surface a h) a h x := by
  apply Subtype.ext
  change AddMonoidAlgebra.mapAlgHom (ℕ × ℕ) (affineBaseChange surface a h)
    (AddMonoidAlgebra.single (1, 0) (monomialAt surface x.val)) = _
  rw [AddMonoidAlgebra.mapAlgHom_single]
  change AddMonoidAlgebra.single (1, 0) _ =
    AddMonoidAlgebra.single (1, 0) (Ideal.Quotient.mk (extendIdeal surface a h) (monomial x.val 1))
  apply congrArg (AddMonoidAlgebra.single (1, 0))
  rw [monomialAt, affineBaseChange_mk, MvPolynomial.map_monomial, map_one]

@[simp] theorem reesBaseChange_right (surface : Ideal GeoJets) (a h : Shape) (y : latticeIndices h) :
    reesBaseChange surface a h (rightGen surface a h y) =
      rightGen (baseIdeal surface a h) a h y := by
  apply Subtype.ext
  change AddMonoidAlgebra.mapAlgHom (ℕ × ℕ) (affineBaseChange surface a h)
    (AddMonoidAlgebra.single (0, 1) (monomialAt surface y.val)) = _
  rw [AddMonoidAlgebra.mapAlgHom_single]
  change AddMonoidAlgebra.single (0, 1) _ =
    AddMonoidAlgebra.single (0, 1) (Ideal.Quotient.mk (extendIdeal surface a h) (monomial y.val 1))
  apply congrArg (AddMonoidAlgebra.single (0, 1))
  rw [monomialAt, affineBaseChange_mk, MvPolynomial.map_monomial, map_one]

@[simp] theorem reesBaseChange_pair (surface : Ideal GeoJets) (a h : Shape)
    (e : latticeIndices a × latticeIndices h) :
    reesBaseChange surface a h (pairGen surface a h e) =
      pairGen (baseIdeal surface a h) a h e := by
  simp [pairGen]

end
end K1_13_6_1_4_2_1_2_2
end PackSource_K1_13_6_1_4_2_1_2_2BaseChange

section PackSource_K1_13_6_1_4_2_1_2_2Dimension
set_option autoImplicit true
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace K1_13_6_1_4_2_1_2_2

noncomputable section

open K1_13_6 K1_13_6_1_4_2 Algebra
open scoped nonZeroDivisors

theorem affineDimension (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ d : ℕ, ringKrullDim A = d ∧ trdeg k A = (d : Cardinal) := by
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let N := MvPolynomial (Fin d) k
  letI : Algebra N A := g.toRingHom.toAlgebra
  letI : IsScalarTower k N A := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  letI : FaithfulSMul N A := (faithfulSMul_iff_algebraMap_injective N A).mpr hg
  letI : Module.Finite N A := hfin
  letI : Algebra.IsIntegral N A := Algebra.IsIntegral.of_finite N A
  let p := PrimeSpectrum.comap (algebraMap N A)
  have hmono : StrictMono p := by
    intro x y hxy
    letI : x.asIdeal.IsPrime := x.2
    exact Ideal.IsIntegral.under_lt_under (R := N) hxy
  have hdim : ringKrullDim A = ringKrullDim N := by
    refine (Order.krullDim_le_of_strictMono p hmono).antisymm ?_
    change Order.krullDim (PrimeSpectrum N) ≤ Order.krullDim (PrimeSpectrum A)
    rw [Order.krullDim_eq_iSup_length, Order.krullDim_eq_iSup_length]
    apply WithBot.coe_le_coe.mpr
    apply iSup_le
    intro l
    obtain ⟨P, hP⟩ := Algebra.IsIntegral.comap_surjective N A l.head
    letI : P.asIdeal.IsPrime := P.2
    letI : P.asIdeal.LiesOver l.head.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hP).symm⟩
    obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    exact hL ▸ le_iSup (fun L : LTSeries (PrimeSpectrum A) => (L.length : ℕ∞)) L
  refine ⟨d, ?_, ?_⟩
  · simp [hdim, N, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  · letI : Algebra.IsAlgebraic N A := Algebra.IsAlgebraic.of_finite N A
    simpa [N, trdeg_eq_zero (R := N) (A := A), Cardinal.mk_fin] using
      (trdeg_add_eq (A := A) k N).symm

theorem chart_trdeg (surface : Ideal GeoJets) [surface.IsPrime] (a h : K1_13.Shape)
    (e : latticeIndices a × latticeIndices h)
    (hdim : ringKrullDim (Base surface) = 2) :
    trdeg GeoField (chartAlgebra surface a h e) ≤ 2 := by
  obtain ⟨d, hd, ht⟩ := affineDimension GeoField (Base surface)
  have hd' : d = 2 := by exact_mod_cast hd.symm.trans hdim
  have hfield : trdeg GeoField (FunctionField surface) = 2 := by
    letI : Algebra.IsAlgebraic (Base surface) (FunctionField surface) :=
      IsLocalization.isAlgebraic _ (Base surface)⁰
    rw [← trdeg_add_eq GeoField (Base surface) (A := FunctionField surface),
      trdeg_eq_zero (R := Base surface) (A := FunctionField surface), add_zero, ht, hd']
    rfl
  exact (trdeg_le_of_injective (chartAlgebra surface a h e).val Subtype.val_injective).trans hfield.le

end
end K1_13_6_1_4_2_1_2_2
end PackSource_K1_13_6_1_4_2_1_2_2Dimension

section PackSource_K1_13_6_1_4_2_1_2_2Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace K1_13_6_1_4_2_1_2_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2
  K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_2 MvPolynomial

/-- An evaluation on a standard chart induces an evaluation of the original monomial ratios. -/
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h)
    {E : Type} [Field E] [Algebra GeoField E]
    (φ : rees surface a h →ₐ[GeoField] E), φ (pairGen surface a h e) ≠ 0 →
    monomialFraction surface e.1.val ≠ 0 ∧ monomialFraction surface e.2.val ≠ 0 ∧
      ∃ f : chartAlgebra surface a h e →ₐ[GeoField] E,
        ∀ i, f (chartCoord surface a h e i) = ratioValue surface a h e φ i

/-- Two independent linear coefficient blocks miss a nonzero boundary equation
on an integral affine algebra of transcendence degree at most two. -/
def c2 : Prop :=
  ∀ {k A E σ τ : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field E] [Algebra k E] [Fintype σ] [Fintype τ]
    (t : σ ⊕ τ → E), AlgebraicIndependent k t →
    Algebra.trdeg k A ≤ 2 →
    ∀ (b : A), b ≠ 0 → ∀ f : A →ₐ[k] E, f b = 0 →
    ∀ (i : σ) (j : τ),
    ∀ (u : σ → A) (v : τ → A), u i = 1 → v j = 1 →
    (∑ m, t (Sum.inl m) * f (u m)) = 0 →
    (∑ m, t (Sum.inr m) * f (v m)) = 0 → False

private theorem no_boundary_point (h1 : c1) (h2 : c2)
    (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (hdim : ringKrullDim (Base surface) = 2) (e : latticeIndices a × latticeIndices h)
    {E : Type} [Field E] [Algebra (Coeff a h) E] [Algebra GeoField E]
    [IsScalarTower GeoField (Coeff a h) E]
    (φ : Rees surface a h →ₐ[Coeff a h] E)
    (hchart : φ (pairGen (baseIdeal surface a h) a h e) ≠ 0)
    (hleft : φ (leftHom surface a h) = 0) (hright : φ (rightHom surface a h) = 0)
    (hshift : φ (shift (baseIdeal surface a h) a h) = 0) : False := by
  classical
  let ψ := (φ.restrictScalars GeoField).comp (reesBaseChange surface a h)
  have hψ : ψ (pairGen surface a h e) ≠ 0 := by simpa [ψ] using hchart
  obtain ⟨hα, hβ, f, hratio⟩ := h1 surface a h e ψ hψ
  have hcoord (i : K1_13_6_1_4_2_1_1.Generator a h) :
      f (chartCoord surface a h e i) = ratioValue (baseIdeal surface a h) a h e φ i := by
    rw [hratio]
    cases i with
    | inl x =>
      change ψ (leftGen surface a h x) / ψ (leftGen surface a h e.1) =
        φ (leftGen (baseIdeal surface a h) a h x) / φ (leftGen (baseIdeal surface a h) a h e.1)
      simp [ψ]
    | inr y =>
      change ψ (rightGen surface a h y) / ψ (rightGen surface a h e.2) =
        φ (rightGen (baseIdeal surface a h) a h y) / φ (rightGen (baseIdeal surface a h) a h e.2)
      simp [ψ]
  let b := chartCoord surface a h e (Sum.inl (zeroCoord a)) *
    chartCoord surface a h e (Sum.inr (zeroCoord h))
  have hb : b ≠ 0 := by
    intro hz
    have hzero : monomialFraction surface 0 = 1 := by simp [monomialFraction, monomialAt]
    have hv := congrArg Subtype.val hz
    change (monomialFraction surface 0 / monomialFraction surface e.1.val) *
      (monomialFraction surface 0 / monomialFraction surface e.2.val) = 0 at hv
    rw [hzero] at hv
    exact mul_ne_zero (div_ne_zero one_ne_zero hα) (div_ne_zero one_ne_zero hβ) hv
  have hbzero : f b = 0 := by
    dsimp only [b]
    rw [map_mul, hcoord, hcoord]
    simp only [ratioValue, Sum.elim_inl, Sum.elim_inr, ← mul_div_mul_comm, ← map_mul]
    change φ (pairGen (baseIdeal surface a h) a h (zeroCoord a, zeroCoord h)) /
      φ (pairGen (baseIdeal surface a h) a h e) = 0
    rw [← shift_eq_pair, hshift, zero_div]
  let P := MvPolynomial (Parameters a h) GeoField
  let F := Coeff a h
  let t (l : LeftLabels a ⊕ RightLabels h) : E :=
    algebraMap F E (parameter a h (Sum.map Subtype.val Subtype.val l))
  have htFull : AlgebraicIndependent GeoField (fun l : Parameters a h =>
      algebraMap F E (parameter a h l)) :=
    ((algebraicIndependent_X (Parameters a h) GeoField).map'
      (f := IsScalarTower.toAlgHom GeoField P F) (IsFractionRing.injective P F)).map'
        (f := IsScalarTower.toAlgHom GeoField F E) (algebraMap F E).injective
  have ht : AlgebraicIndependent GeoField t :=
    htFull.comp (Sum.map Subtype.val Subtype.val)
      (Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩)
  let u (m : LeftLabels a) := chartCoord surface a h e (Sum.inl (sectionCoord a m))
  let v (m : RightLabels h) := chartCoord surface a h e (Sum.inr (sectionCoord h m))
  obtain ⟨i, hi⟩ := sectionCoord_surjective a e.1
  obtain ⟨j, hj⟩ := sectionCoord_surjective h e.2
  have hui : u i = 1 := by
    apply Subtype.ext
    change chartValue surface a h e (Sum.inl (sectionCoord a i)) = 1
    simp [hi, chartValue, hα]
  have hvj : v j = 1 := by
    apply Subtype.ext
    change chartValue surface a h e (Sum.inr (sectionCoord h j)) = 1
    simp [hj, chartValue, hβ]
  have hu : (∑ m, t (Sum.inl m) * f (u m)) = 0 := by
    rw [leftHom_sum] at hleft
    simp only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes] at hleft
    calc
      _ = (∑ m : LeftLabels a, t (Sum.inl m) *
          φ (leftGen (baseIdeal surface a h) a h (sectionCoord a m))) /
            φ (leftGen (baseIdeal surface a h) a h e.1) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun m _ => ?_
        dsimp only [u]
        rw [hcoord]
        exact (mul_div_assoc _ _ _).symm
      _ = 0 := by rw [show (∑ m, t (Sum.inl m) *
        φ (leftGen (baseIdeal surface a h) a h (sectionCoord a m))) = 0 from hleft, zero_div]
  have hv : (∑ m, t (Sum.inr m) * f (v m)) = 0 := by
    rw [rightHom_sum] at hright
    simp only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes] at hright
    calc
      _ = (∑ m : RightLabels h, t (Sum.inr m) *
          φ (rightGen (baseIdeal surface a h) a h (sectionCoord h m))) /
            φ (rightGen (baseIdeal surface a h) a h e.2) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun m _ => ?_
        dsimp only [v]
        rw [hcoord]
        exact (mul_div_assoc _ _ _).symm
      _ = 0 := by rw [show (∑ m, t (Sum.inr m) *
        φ (rightGen (baseIdeal surface a h) a h (sectionCoord h m))) = 0 from hright, zero_div]
  exact h2 t ht (chart_trdeg surface a h e hdim)
    b hb f hbzero i j u v hui hvj hu hv

theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2_1_2.c2 := by
  intro surface a h hsurface hdim _ _ e
  let : surface.IsPrime := hsurface
  let I := homBoundaryIdeal surface a h
  change pairGen (baseIdeal surface a h) a h e ∈ I.radical
  rw [Ideal.radical_eq_sInf]
  refine Ideal.mem_sInf.mpr fun {J} hJ => ?_
  obtain ⟨hIJ, hprime⟩ := hJ
  let : J.IsPrime := hprime
  by_contra hchart
  let F := Coeff a h
  let D := Rees surface a h ⧸ J
  let : CommRing D := Ideal.Quotient.commRing (R := Rees surface a h) J
  let : IsDomain D := Ideal.Quotient.isDomain J
  let : Algebra F D := inferInstanceAs (Algebra (Coeff a h) (Rees surface a h ⧸ J))
  let E := FractionRing D
  let : Field E := inferInstanceAs (Field (FractionRing D))
  let : Algebra D E := inferInstanceAs (Algebra D (FractionRing D))
  let : Algebra F E := inferInstanceAs (Algebra F (FractionRing D))
  let : IsScalarTower F D E := inferInstanceAs (IsScalarTower F D (FractionRing D))
  let : Algebra GeoField E := Algebra.compHom E (algebraMap GeoField F)
  let : IsScalarTower GeoField F E := IsScalarTower.of_algebraMap_eq' rfl
  let φ : Rees surface a h →ₐ[F] E :=
    (IsScalarTower.toAlgHom F D E).comp (Ideal.Quotient.mkₐ F J)
  have hvanish (x : Rees surface a h) (hx : x ∈ I) : φ x = 0 := by
    change algebraMap D E (Ideal.Quotient.mk J x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx), map_zero]
  have hnonzero : φ (pairGen (baseIdeal surface a h) a h e) ≠ 0 := by
    intro hz
    apply hchart
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective D E
    change algebraMap D E (Ideal.Quotient.mk J (pairGen (baseIdeal surface a h) a h e)) = 0 at hz
    rw [map_zero]
    exact hz
  exact no_boundary_point h1 h2 surface a h hdim e φ hnonzero
    (hvanish _ (Ideal.mem_sup_left (Ideal.subset_span (by simp))))
    (hvanish _ (Ideal.mem_sup_left (Ideal.subset_span (by simp))))
    (hvanish _ (Ideal.mem_sup_right (Ideal.subset_span (by simp))))

end
end K1_13_6_1_4_2_1_2_2
end PackSource_K1_13_6_1_4_2_1_2_2Split

section PackSource_K1_13_6_1_4_2_1_2_2_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace K1_13_6_1_4_2_1_2_2_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_1_4_2 K1_13_6_1_4_2_1_1
  K1_13_6_1_4_2_1_2 K1_13_6_1_4_2_1_2_2

private theorem away_fraction {k R F : Type*} [CommRing k] [CommRing R] [Field F]
    [Algebra k R] [Algebra k F] (b x : R) (g : R →ₐ[k] F) (hb : g b ≠ 0) :
    IsLocalization.Away.liftAlgHom (S := Localization.Away b) b (f := g) hb.isUnit
      (IsLocalization.mk' (Localization.Away b) x ⟨b, Submonoid.mem_powers b⟩) =
        g x / g b := by
  let f : Localization.Away b →ₐ[k] F := IsLocalization.Away.liftAlgHom b (f := g) hb.isUnit
  have hf (y : R) : f (algebraMap R (Localization.Away b) y) = g y :=
    IsLocalization.Away.lift_eq b (g := g.toRingHom) hb.isUnit y
  change f _ = _
  apply (eq_div_iff hb).2
  simpa only [map_mul, hf] using
    congrArg f (IsLocalization.mk'_spec (Localization.Away b) x ⟨b, Submonoid.mem_powers b⟩)

/-- An algebra generated by ratios with a common denominator in an embedded ring
maps to any field where the denominator remains nonzero. -/
private theorem evaluate_adjoin {k R K L E ι : Type*}
    [CommRing k] [CommRing R] [CommRing K] [Field L] [Field E]
    [Algebra k R] [Algebra k K] [Algebra k L] [Algebra k E]
    (j : R →ₐ[k] L) (hj : Function.Injective j)
    (b : R) (φ : R →ₐ[k] E) (hb : φ b ≠ 0)
    (c : K →ₐ[k] L) (r : ι → K) (n : ι → R)
    (hr : ∀ t, c (r t) * j b = j (n t)) :
    ∃ f : Algebra.adjoin k (Set.range r) →ₐ[k] E,
      ∀ t, f ⟨r t, Algebra.subset_adjoin (Set.mem_range_self t)⟩ = φ (n t) / φ b := by
  let S := Localization.Away b
  let fraction (x : R) : S := IsLocalization.mk' S x ⟨b, Submonoid.mem_powers b⟩
  have hjb : j b ≠ 0 := by
    intro hz
    have h : b = 0 := hj (hz.trans (map_zero j).symm)
    exact hb (h ▸ map_zero φ)
  let lift : S →ₐ[k] L := IsLocalization.Away.liftAlgHom b (f := j) hjb.isUnit
  have hlift (x : R) : lift (algebraMap R S x) = j x :=
    IsLocalization.Away.lift_eq b (g := j.toRingHom) hjb.isUnit x
  have hinj : Function.Injective lift := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers b) lift.toRingHom).2
    intro x y
    change algebraMap R S x = algebraMap R S y ↔
      lift (algebraMap R S x) = lift (algebraMap R S y)
    rw [hlift, hlift]
    constructor
    · exact fun h => (hlift x).symm.trans ((congrArg lift h).trans (hlift y))
    · exact fun h => congrArg (algebraMap R S) (hj h)
  have hlift_fraction (t : ι) : lift (fraction (n t)) = c (r t) :=
    (away_fraction b (n t) j hjb).trans ((eq_div_iff hjb).2 (hr t)).symm
  let chart := Algebra.adjoin k (Set.range r)
  have hchart : chart ≤ lift.range.comap c := by
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    exact ⟨fraction (n t), hlift_fraction t⟩
  let g : chart →ₐ[k] lift.range :=
    (c.comp chart.val).codRestrict lift.range fun x => hchart x.property
  let u : S ≃ₐ[k] lift.range := AlgEquiv.ofInjective lift hinj
  let ev : S →ₐ[k] E := IsLocalization.Away.liftAlgHom b (f := φ) hb.isUnit
  refine ⟨(ev.comp u.symm.toAlgHom).comp g, fun t => ?_⟩
  have ht : g ⟨r t, Algebra.subset_adjoin (Set.mem_range_self t)⟩ = u (fraction (n t)) :=
    Subtype.ext (hlift_fraction t).symm
  change ev (u.symm (g ⟨r t, _⟩)) = _
  rw [ht, AlgEquiv.symm_apply_apply]
  exact away_fraction b (n t) φ hb

theorem proof : K1_13_6_1_4_2_1_2_2.c1 := by
  intro surface hprime a h e E hE hAlgebra φ hφ
  let : surface.IsPrime := hprime
  let : Field E := hE
  let : Algebra GeoField E := hAlgebra
  let A := AddMonoidAlgebra (Base surface) (ℕ × ℕ)
  let L := FractionRing A
  let embed := IsScalarTower.toAlgHom GeoField A L
  let j := embed.comp (rees surface a h).val
  have hj : Function.Injective j := (IsFractionRing.injective A L).comp Subtype.val_injective
  let constant : Base surface →ₐ[GeoField] L := embed.comp AddMonoidAlgebra.singleZeroAlgHom
  have hconstant : Function.Injective constant := by
    intro x y hxy
    have hs : (AddMonoidAlgebra.single 0 x : A) = AddMonoidAlgebra.single 0 y :=
      IsFractionRing.injective A L hxy
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using
      congrArg (fun p : A => p.coeff 0) hs
  let c : FunctionField surface →ₐ[GeoField] L := IsFractionRing.liftAlgHom hconstant
  have hconstant_monomial (x : Fin 4 →₀ ℕ) :
      c (monomialFraction surface x) =
        embed (AddMonoidAlgebra.single 0 (monomialAt surface x)) :=
    IsFractionRing.lift_algebraMap (g := constant.toRingHom) hconstant _
  let degree (d : ℕ × ℕ) := embed (AddMonoidAlgebra.single d 1)
  have homogeneous_image (d : ℕ × ℕ) (x : Fin 4 →₀ ℕ)
      (hx : monomialAt surface x ∈ box surface a h d) :
      j (homogeneous d (monomialAt surface x) hx) =
        c (monomialFraction surface x) * degree d := by
    change embed (AddMonoidAlgebra.single d (monomialAt surface x)) =
      c (monomialFraction surface x) * embed (AddMonoidAlgebra.single d 1)
    rw [hconstant_monomial, ← map_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  have hleft (x : latticeIndices a) :
      j (leftGen surface a h x) = c (monomialFraction surface x.val) * degree (1, 0) :=
    homogeneous_image (1, 0) x.val _
  have hright (y : latticeIndices h) :
      j (rightGen surface a h y) = c (monomialFraction surface y.val) * degree (0, 1) :=
    homogeneous_image (0, 1) y.val _
  have hp : φ (leftGen surface a h e.1) * φ (rightGen surface a h e.2) ≠ 0 := by
    simpa only [pairGen, map_mul] using hφ
  obtain ⟨hφleft, hφright⟩ := mul_ne_zero_iff.mp hp
  have coeff_ne_zero (x : Fin 4 →₀ ℕ) (p : rees surface a h) (d : ℕ × ℕ)
      (hj' : j p = c (monomialFraction surface x) * degree d) (hp' : φ p ≠ 0) :
      monomialFraction surface x ≠ 0 := by
    intro hz
    have heq : j p = j 0 := by rw [hj', hz, map_zero, zero_mul, map_zero]
    have hzero : p = 0 := hj heq
    exact hp' (hzero ▸ map_zero φ)
  have hα := coeff_ne_zero e.1.val (leftGen surface a h e.1) (1, 0) (hleft e.1) hφleft
  have hβ := coeff_ne_zero e.2.val (rightGen surface a h e.2) (0, 1) (hright e.2) hφright
  have left_ratio (x : latticeIndices a) :
      c (monomialFraction surface x.val / monomialFraction surface e.1.val) *
        j (leftGen surface a h e.1) = j (leftGen surface a h x) := by
    rw [map_div₀, hleft, hleft, ← mul_assoc, div_mul_cancel₀ _ ((map_ne_zero c).2 hα)]
  have right_ratio (y : latticeIndices h) :
      c (monomialFraction surface y.val / monomialFraction surface e.2.val) *
        j (rightGen surface a h e.2) = j (rightGen surface a h y) := by
    rw [map_div₀, hright, hright, ← mul_assoc, div_mul_cancel₀ _ ((map_ne_zero c).2 hβ)]
  let n : Generator a h → rees surface a h :=
    Sum.elim (fun x => pairGen surface a h (x, e.2)) (fun y => pairGen surface a h (e.1, y))
  have hratio (i : Generator a h) :
      c (chartValue surface a h e i) * j (pairGen surface a h e) = j (n i) := by
    cases i with
    | inl x =>
      simp only [chartValue, n, Sum.elim_inl, pairGen, map_mul]
      rw [← mul_assoc, left_ratio]
    | inr y =>
      simp only [chartValue, n, Sum.elim_inr, pairGen, map_mul]
      rw [mul_left_comm, right_ratio]
  obtain ⟨f, hf⟩ := evaluate_adjoin j hj (pairGen surface a h e) φ hφ c
    (chartValue surface a h e) n hratio
  refine ⟨hα, hβ, f, fun i => (hf i).trans ?_⟩
  cases i with
  | inl x =>
    simp only [n, ratioValue, Sum.elim_inl, pairGen, map_mul]
    exact mul_div_mul_right _ _ hφright
  | inr y =>
    simp only [n, ratioValue, Sum.elim_inr, pairGen, map_mul]
    exact mul_div_mul_left _ _ hφleft

end
end K1_13_6_1_4_2_1_2_2_1
end PackSource_K1_13_6_1_4_2_1_2_2_1Proof

section PackSource_K1_13_6_1_4_2_1_1Saturation
set_option autoImplicit true
namespace K1_13_6_1_4_2_1_1

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem component_mul {k α β : Type} [CommSemiring k]
    {g : MvPolynomial (α ⊕ β) k} {e : ℕ × ℕ} (hg : g ∈ grade e)
    (p : MvPolynomial (α ⊕ β) k) (d : ℕ × ℕ) :
    weightedHomogeneousComponent weight (d + e) (p * g) =
      weightedHomogeneousComponent weight d p * g := by
  induction p using MvPolynomial.induction_on' with
  | monomial b r =>
    have hb := isWeightedHomogeneous_monomial weight b r rfl
    simp only [weightedHomogeneousComponent_of_mem (hb.mul hg),
      weightedHomogeneousComponent_of_mem hb, add_right_cancel_iff]
    split <;> simp_all
  | add a b ha hb => simp [add_mul, ha, hb]

theorem homogeneous_colon {k α β : Type} [CommRing k]
    {I : Ideal (MvPolynomial (α ⊕ β) k)} (hI : I.IsHomogeneous grade)
    {g : MvPolynomial (α ⊕ β) k} {e : ℕ × ℕ} (hg : g ∈ grade e) :
    (I.colon {g}).IsHomogeneous grade := by
  intro d p hp
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hp ⊢
  have he : (DirectSum.decompose grade p d : MvPolynomial (α ⊕ β) k) =
      weightedHomogeneousComponent weight d p :=
    weightedDecomposition.decompose'_apply k weight p d
  rw [he, ← component_mul hg]
  exact weightedHomogeneousComponent_mem_of_mem _ _ hI hp _

section Noetherian

variable {k α β : Type} [Field k] [Fintype α] [Fintype β]

private abbrev P := MvPolynomial (α ⊕ β) k

private theorem chart_pow_dvd_monomial (d : α ⊕ β →₀ ℕ) (r : k) (n : ℕ)
    (hleft : Fintype.card α * n < (Finsupp.weight weight d).1)
    (hright : Fintype.card β * n < (Finsupp.weight weight d).2) :
    ∃ x : α, ∃ y : β, (chart x y : P (k := k)) ^ n ∣ monomial d r := by
  classical
  have hs₁ : (Finsupp.weight weight d).1 = ∑ x : α, d (Sum.inl x) := by
    simp [Finsupp.weight_eq_sum, Fintype.sum_sum_type, weight, Prod.fst_sum]
  have hs₂ : (Finsupp.weight weight d).2 = ∑ y : β, d (Sum.inr y) := by
    simp [Finsupp.weight_eq_sum, Fintype.sum_sum_type, weight, Prod.snd_sum]
  have hx : ∃ x : α, n ≤ d (Sum.inl x) := by
    by_contra! hnone
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun x _ => (hnone x).le
    rw [hs₁] at hleft
    exact (not_le_of_gt hleft) (by simpa using hsum)
  have hy : ∃ y : β, n ≤ d (Sum.inr y) := by
    by_contra! hnone
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun y _ => (hnone y).le
    rw [hs₂] at hright
    exact (not_le_of_gt hright) (by simpa using hsum)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  let t := Finsupp.single (Sum.inl x) n + Finsupp.single (Sum.inr y) n
  have ht : t ≤ d := by
    intro z
    rcases z with z | z
    · by_cases h : z = x
      · subst z
        simpa [t, Finsupp.single_apply] using hx
      · simp [t, h]
    · by_cases h : z = y
      · subst z
        simpa [t, Finsupp.single_apply] using hy
      · simp [t, h]
  refine ⟨x, y, monomial (d - t) r, ?_⟩
  rw [chart, mul_pow, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial,
    one_mul, ← show t = _ from rfl, monomial_mul_monomial, one_mul,
    add_comm t, tsub_add_cancel_of_le ht]

private theorem uniform_chart_power (I K : Ideal (P (k := k) (α := α) (β := β)))
    (hlocal : ∀ x : α, ∀ y : β, ∀ p ∈ K, ∃ n : ℕ, chart x y ^ n * p ∈ I) :
    ∃ n : ℕ, ∀ x : α, ∀ y : β, ∀ p ∈ K, chart x y ^ n * p ∈ I := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian K
  have hg (v : α × β × ↥s) : ∃ n : ℕ, chart v.1 v.2.1 ^ n * v.2.2.val ∈ I :=
    hlocal v.1 v.2.1 _ (hs ▸ Ideal.subset_span v.2.2.property)
  choose n hn using hg
  let N := Finset.univ.sup n
  refine ⟨N, fun x y p hp => ?_⟩
  have hf : K ≤ I.colon {chart x y ^ N} := by
    rw [← hs]
    apply Ideal.span_le.mpr
    intro q hq
    change q ∈ I.colon {chart x y ^ N}
    apply Submodule.mem_colon_singleton.mpr
    let v : α × β × ↥s := (x, y, ⟨q, hq⟩)
    have hnv : n v ≤ N := Finset.le_sup (Finset.mem_univ v)
    have hq' : chart x y ^ n v * q ∈ I := hn v
    rw [smul_eq_mul, mul_comm,
      show N = N - n v + n v from (Nat.sub_add_cancel hnv).symm,
      pow_add, mul_assoc]
    exact I.mul_mem_left _ hq'
  exact mul_comm p _ ▸ (Submodule.mem_colon_singleton.mp (hf hp))

/-- If every element of a homogeneous ideal lies in another ideal on each product chart,
the same containment holds in all sufficiently high bidegrees before localization. -/
theorem high_degree_of_charts (I K : Ideal (P (k := k) (α := α) (β := β)))
    (hK : K.IsHomogeneous grade)
    (hlocal : ∀ x : α, ∀ y : β, ∀ p ∈ K, ∃ n : ℕ, chart x y ^ n * p ∈ I) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ p ∈ K, p ∈ grade (i, j) → p ∈ I := by
  classical
  obtain ⟨n, hn⟩ := uniform_chart_power I K hlocal
  let S : Set (P (k := k) (α := α) (β := β)) :=
    {p | p ∈ K ∧ ∃ e : ℕ × ℕ, p ∈ grade e}
  have hS : Ideal.span S = K := by
    apply le_antisymm (Ideal.span_le.mpr fun _ hp => hp.1)
    have hle : (K.homogeneousCore grade).toIdeal ≤ Ideal.span S := by
      change Ideal.span _ ≤ _
      apply Ideal.span_mono
      rintro _ ⟨⟨q, hq⟩, hmem, rfl⟩
      exact ⟨hmem, hq⟩
    simpa only [hK.toIdeal_homogeneousCore_eq_self] using hle
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp
    (hS.symm ▸ IsNoetherian.noetherian K)
  have hsg (q : ↥s) : ∃ d : ℕ × ℕ, q.val ∈ grade d := (hsS q.property).2
  choose e he using hsg
  let B := Finset.univ.sup fun q : ↥s => max (e q).1 (e q).2
  let N := (Fintype.card α + Fintype.card β) * n + B + 1
  refine ⟨N, fun i j hi hj p hp hpg => ?_⟩
  let proj := weightedHomogeneousComponent weight (i, j) (R := k) (σ := α ⊕ β)
  have hgen (q : ↥s) (u : P (k := k) (α := α) (β := β)) : proj (u * q.val) ∈ I := by
    have hbound := Finset.le_sup (f := fun q : ↥s => max (e q).1 (e q).2) (Finset.mem_univ q)
    have hb₁ : (e q).1 ≤ B := (le_max_left _ _).trans hbound
    have hb₂ : (e q).2 ≤ B := (le_max_right _ _).trans hbound
    induction u using MvPolynomial.induction_on' with
    | add u v hu hv => simpa only [add_mul, map_add] using I.add_mem hu hv
    | monomial d c =>
      have hm := isWeightedHomogeneous_monomial weight d c rfl
      change weightedHomogeneousComponent weight (i, j) (monomial d c * q.val) ∈ I
      rw [weightedHomogeneousComponent_of_mem (hm.mul (he q))]
      split
      next h =>
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        change i = (Finsupp.weight weight d).1 + (e q).1 at h₁
        change j = (Finsupp.weight weight d).2 + (e q).2 at h₂
        have hc₁ := Nat.mul_le_mul_right n (Nat.le_add_right (Fintype.card α) (Fintype.card β))
        have hc₂ := Nat.mul_le_mul_right n (Nat.le_add_left (Fintype.card β) (Fintype.card α))
        dsimp only [N] at hi hj
        obtain ⟨x, y, t, ht⟩ := chart_pow_dvd_monomial d c n
          (by omega : _ < (Finsupp.weight weight d).1) (by omega : _ < (Finsupp.weight weight d).2)
        rw [ht, mul_comm (_ ^ n), mul_assoc]
        exact I.mul_mem_left t (hn x y _ (hsS q.property).1)
      next => exact I.zero_mem
  have hmem : p ∈ Submodule.span (P (k := k) (α := α) (β := β)) (↑s : Set _) := by
    rw [← hs]
    change p ∈ Ideal.span S
    rwa [hS]
  have hproj : ∀ u : P (k := k) (α := α) (β := β), proj (u * p) ∈ I := by
    refine Submodule.span_induction (p := fun q _ => ∀ u, proj (u * q) ∈ I)
      (fun q hq u => hgen ⟨q, hq⟩ u) ?_ ?_ ?_ hmem
    · intro u
      simp
    · intro x y hx hy hpx hpy u
      simpa only [mul_add, map_add] using I.add_mem (hpx u) (hpy u)
    · intro c x hx hpx u
      simpa only [smul_eq_mul, mul_assoc] using hpx (u * c)
  simpa only [one_mul, proj, weightedHomogeneousComponent_eq_self hpg] using hproj 1

end Noetherian

end
end K1_13_6_1_4_2_1_1
end PackSource_K1_13_6_1_4_2_1_1Saturation

section PackSource_K1_13_6_1_4_2_1_1_2Model
set_option autoImplicit true
set_option maxHeartbeats 1200000

namespace K1_13_6_1_4_2_1_1_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_1
open MvPolynomial
open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.weightedGradedAlgebra MvPolynomial.algebraMvPolynomial

private def block {α β : Type} : α ⊕ β → Bool := Sum.elim (fun _ => false) (fun _ => true)

private def degree : (Bool →₀ ℕ) →+ ℕ × ℕ where
  toFun d := (d false, d true)
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem degree_apply (d : Bool →₀ ℕ) : degree d = (d false, d true) := rfl

private theorem degree_injective : Function.Injective degree := by
  intro u v hv
  ext b
  cases b
  · exact congrArg Prod.fst hv
  · exact congrArg Prod.snd hv

private theorem degree_weight {α β : Type} (d : α ⊕ β →₀ ℕ) :
    degree (Finsupp.weight (fun i => Finsupp.single (block i) 1) d) = Finsupp.weight weight d := by
  have h : degree.comp (Finsupp.weight (fun i : α ⊕ β => Finsupp.single (block i) 1)) =
      Finsupp.weight (R := ℕ) (weight : α ⊕ β → ℕ × ℕ) := by
    apply Finsupp.addHom_ext
    intro v n
    cases v <;> simp [degree_apply, block, weight, Finsupp.weight_single]
  exact DFunLike.congr_fun h d

private def homogenize {k B α β : Type} [CommRing k] [CommRing B] [Algebra k B]
    (f : MvPolynomial (α ⊕ β) k →ₐ[k] B) :
    MvPolynomial (α ⊕ β) k →ₐ[k] MvPolynomial Bool B :=
  aeval fun v => monomial (Finsupp.single (block v) 1) (f (MvPolynomial.X v))

private theorem coeff_homogenize {k B α β : Type} [CommRing k] [CommRing B] [Algebra k B]
    (f : MvPolynomial (α ⊕ β) k →ₐ[k] B) (p : MvPolynomial (α ⊕ β) k) (b : Bool →₀ ℕ) :
    (homogenize f p).coeff b = f (weightedHomogeneousComponent weight (degree b) p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, map_add]
    change (homogenize f p).coeff b + (homogenize f q).coeff b = _
    rw [hp, hq]
  | monomial d c =>
    let w := fun v : α ⊕ β => Finsupp.single (block v) (1 : ℕ)
    have hm : homogenize f (monomial d c) =
        monomial (Finsupp.weight w d) (f (monomial d c)) := by
      unfold homogenize
      rw [aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
      simp only [monomial_pow, ← monomial_sum_prod]
      change C (algebraMap k B c) * monomial _ _ = _
      rw [C_mul_monomial]
      congr 1
      symm
      have hmono : monomial d c = C c * (d.prod fun i n => (MvPolynomial.X i : MvPolynomial (α ⊕ β) k) ^ n) :=
        monomial_eq
      have hC : f (C c) = algebraMap k B c := f.commutes c
      rw [congrArg f hmono, map_mul, hC, Finsupp.prod, map_prod]
      simp only [map_pow]
    have hh : monomial d c ∈ weightedHomogeneousSubmodule k weight (Finsupp.weight weight d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    rw [hm, coeff_monomial, weightedHomogeneousComponent_of_mem hh]
    by_cases he : degree b = Finsupp.weight weight d
    · have he' : Finsupp.weight w d = b := degree_injective ((degree_weight d).trans he.symm)
      simp [he, he']
    · have he' : Finsupp.weight w d ≠ b := fun h => he ((congrArg degree h).symm.trans (degree_weight d))
      simp [he, he']

private abbrev Target := Bool ⊕ Fin 4

private def jetInclude (k : Type) [CommRing k] :
    MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial Target k :=
  rename Sum.inr

private def model (k : Type) [CommRing k] (a h : Shape) :
    MvPolynomial (Generator a h) k →ₐ[k] MvPolynomial Target k :=
  aeval fun v => MvPolynomial.X (Sum.inl (block v)) *
    jetInclude k (monomial (generatorExponent v) 1)

private def targetIdeal (k : Type) [CommRing k] [Algebra GeoField k]
    (surface : Ideal GeoJets) : Ideal (MvPolynomial Target k) :=
  surface.map ((jetInclude k).toRingHom.comp (MvPolynomial.map (algebraMap GeoField k)))

/-- The homogeneous coordinate relations at the indicated coefficient ring. -/
def modelRelations (k : Type) [CommRing k] [Algebra GeoField k]
    (surface : Ideal GeoJets) (a h : Shape) : Ideal (MvPolynomial (Generator a h) k) :=
  (targetIdeal k surface).comap (model k a h).toRingHom

private def affineEval {k : Type} [CommRing k] (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) :
    MvPolynomial (Generator a h) k →ₐ[k] (MvPolynomial (Fin 4) k ⧸ I) :=
  (Ideal.Quotient.mkₐ _ _).comp (aeval fun v => monomial (generatorExponent v) 1)

private theorem homogeneous_core_eq_model {k : Type} [CommRing k]
    (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) :
    ((RingHom.ker (affineEval I a h).toRingHom).homogeneousCore grade).toIdeal =
      (I.map (jetInclude k).toRingHom).comap (model k a h).toRingHom := by
  classical
  let Q := MvPolynomial (Fin 4) k ⧸ I
  let e := sumAlgEquiv k Bool (Fin 4)
  let q : MvPolynomial (Fin 4) k →+* Q := Ideal.Quotient.mk I
  let g : MvPolynomial Target k →+* MvPolynomial Bool Q := (MvPolynomial.map q).comp e.toRingHom
  have hcomp : e.toRingHom.comp (jetInclude k).toRingHom = (C : MvPolynomial (Fin 4) k →+* _) :=
    congrArg AlgHom.toRingHom (sumAlgEquiv_comp_rename_inr (R := k) (S₁ := Bool) (S₂ := Fin 4))
  have hk : RingHom.ker g = I.map (jetInclude k).toRingHom := by
    change RingHom.ker ((MvPolynomial.map q).comp e.toRingHom) = _
    rw [← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← hcomp, ← Ideal.map_map]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  have hg : g.comp (model k a h).toRingHom = (homogenize (affineEval I a h)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change g (model k a h (C c)) = homogenize (affineEval I a h) (C c)
      rw [model, aeval_C, homogenize, aeval_C]
      change MvPolynomial.map q (e (C c)) = C (algebraMap k Q c)
      rw [sumAlgEquiv_C_inl, MvPolynomial.map_C]
      rfl
    · intro v
      change g (model k a h (MvPolynomial.X v)) = homogenize (affineEval I a h) (MvPolynomial.X v)
      rw [model, aeval_X, homogenize, aeval_X]
      have hi := DFunLike.congr_fun hcomp (monomial (generatorExponent v) (1 : k))
      change e (jetInclude k (monomial (generatorExponent v) 1)) = _ at hi
      change MvPolynomial.map q (e (_ * _)) = _
      rw [map_mul, sumAlgEquiv_X_inl, hi, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, mul_comm]
      change C (q _) * monomial _ 1 = _
      rw [C_mul_monomial, mul_one]
      simp only [affineEval, AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk, q]
  rw [← hk, RingHom.comap_ker, hg]
  let J := (RingHom.ker (affineEval I a h).toRingHom).homogeneousCore grade
  change J.toIdeal = _
  ext p
  rw [mem_iff_weightedHomogeneousComponent_mem _ _ J.isHomogeneous, RingHom.mem_ker]
  constructor
  · intro hp
    ext1 b
    change (homogenize (affineEval I a h) p).coeff b = 0
    rw [coeff_homogenize]
    exact Ideal.toIdeal_homogeneousCore_le grade _ (hp (degree b))
  · intro hp d
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨d, weightedHomogeneousComponent_mem _ _ _⟩
    let b := Finsupp.single false d.1 + Finsupp.single true d.2
    have hb : degree b = d := by simp [b, degree_apply]
    have hz := congrArg (fun z : MvPolynomial Bool Q => z.coeff b) hp
    change (homogenize (affineEval I a h) p).coeff b = 0 at hz
    rw [coeff_homogenize, hb] at hz
    exact RingHom.mem_ker.mpr hz

theorem relations_eq_model (surface : Ideal GeoJets) (a h : Shape) :
    relations surface a h = modelRelations (Coeff a h) surface a h := by
  unfold modelRelations targetIdeal
  rw [← Ideal.map_map]
  exact homogeneous_core_eq_model (extendIdeal surface a h) a h

private theorem model_map {k L : Type} [CommRing k] [CommRing L] (g : k →+* L) (a h : Shape) :
    (MvPolynomial.map g).comp (model k a h).toRingHom =
      (model L a h).toRingHom.comp (MvPolynomial.map g) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [model, MvPolynomial.algebraMap_eq]
  · intro i
    simp [model, jetInclude, MvPolynomial.map_rename]

private theorem targetIdeal_map {k L : Type} [CommRing k] [CommRing L]
    [Algebra GeoField k] [Algebra GeoField L] (g : k →+* L)
    (hg : g.comp (algebraMap GeoField k) = algebraMap GeoField L) (surface : Ideal GeoJets) :
    (targetIdeal k surface).map (MvPolynomial.map g) = targetIdeal L surface := by
  unfold targetIdeal
  rw [Ideal.map_map, ← RingHom.comp_assoc, show (MvPolynomial.map g).comp
    (jetInclude k).toRingHom = (jetInclude L).toRingHom.comp (MvPolynomial.map g) from
      MvPolynomial.map_comp_rename g Sum.inr, RingHom.comp_assoc]
  congr 2
  exact (RingHom.ext fun p => MvPolynomial.map_map _ g p).trans (congrArg MvPolynomial.map hg)

/-- Swapping the two variable sets identifies the extension of base coordinates
with constant polynomials in the coefficient variables. -/
theorem commAlgEquiv_comp_map_C (k σ τ : Type) [CommRing k] :
    (commAlgEquiv k σ τ).toRingHom.comp (MvPolynomial.map C) =
      (C : MvPolynomial σ k →+* MvPolynomial τ (MvPolynomial σ k)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    simp

theorem modelRelations_polynomial (τ : Type) (surface : Ideal GeoJets) (a h : Shape) :
    modelRelations (MvPolynomial τ GeoField) surface a h =
      (modelRelations GeoField surface a h).map (MvPolynomial.map C) := by
  let k := GeoField
  let P := MvPolynomial τ k
  let e := commAlgEquiv k (Generator a h) τ
  let E := commAlgEquiv k Target τ
  let f := (model k a h).toRingHom
  let g := (model P a h).toRingHom
  have hcomm : E.toRingHom.comp g = (MvPolynomial.map f).comp e.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change E (model P a h (C c)) = MvPolynomial.map f (e (C c))
      rw [model, aeval_C, MvPolynomial.algebraMap_eq, commAlgEquiv_C, commAlgEquiv_C,
        MvPolynomial.map_map]
      have hC : f.comp (C (σ := Generator a h)) = C (σ := Target) := by
        apply RingHom.ext
        intro r
        change model k a h (C r) = C r
        simp [model, MvPolynomial.algebraMap_eq]
      rw [hC]
    · intro i
      change E (model P a h (MvPolynomial.X i)) =
        MvPolynomial.map f (e (MvPolynomial.X i))
      have hi := DFunLike.congr_fun (model_map (C : k →+* P) a h) (MvPolynomial.X i)
      change MvPolynomial.map C (model k a h (MvPolynomial.X i)) =
        model P a h (MvPolynomial.map C (MvPolynomial.X i)) at hi
      rw [MvPolynomial.map_X] at hi
      rw [← hi, commAlgEquiv_X, MvPolynomial.map_C]
      exact DFunLike.congr_fun (commAlgEquiv_comp_map_C k Target τ) _
  have hI : (targetIdeal P surface).map E.toRingHom =
      (targetIdeal k surface).map (C (σ := τ)) := by
    rw [← targetIdeal_map (k := k) (L := P) C (by ext; simp [k, P, MvPolynomial.algebraMap_eq]),
      Ideal.map_map, commAlgEquiv_comp_map_C]
  have hJ : ((modelRelations k surface a h).map (MvPolynomial.map C)).map e.toRingHom =
      (modelRelations k surface a h).map (C (σ := τ)) := by
    rw [Ideal.map_map, commAlgEquiv_comp_map_C]
  change (targetIdeal P surface).comap g = _
  rw [← Ideal.comap_map_of_bijective E.toRingHom E.bijective (I := targetIdeal P surface),
    hI, Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  rw [← Ideal.comap_map_of_bijective e.toRingHom e.bijective
    (I := (modelRelations k surface a h).map (MvPolynomial.map C)), hJ]
  congr 1
  ext p
  simp only [Ideal.mem_comap, MvPolynomial.mem_map_C_iff, MvPolynomial.coeff_map]
  rfl

private theorem comap_of_localization {A B A' B' : Type} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
    (g : A →+* B) (h : A' →+* B') (M : Submonoid A)
    [IsLocalization M A'] [IsLocalization (M.map g) B']
    (hcomm : h.comp (algebraMap A A') = (algebraMap B B').comp g) (I : Ideal B) :
    (I.map (algebraMap B B')).comap h = (I.comap g).map (algebraMap A A') := by
  have he : h = IsLocalization.map B' g M.le_comap_map := by
    apply IsLocalization.ringHom_ext M
    rw [hcomm, IsLocalization.map_comp]
  ext p
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq M p
  rw [Ideal.mem_comap, he, IsLocalization.map_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff]
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, he⟩
    exact ⟨d, hd, by simpa only [Ideal.mem_comap, map_mul] using he⟩
  · rintro ⟨d, hd, he⟩
    exact ⟨g d, Submonoid.mem_map_of_mem _ hd, by simpa only [Ideal.mem_comap, map_mul] using he⟩

abbrev CoeffPoly (a h : Shape) := MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField
abbrev IntegralForms (a h : Shape) := MvPolynomial (Generator a h) (CoeffPoly a h)

theorem modelRelations_fraction (surface : Ideal GeoJets) (a h : Shape) :
    modelRelations (Coeff a h) surface a h =
      (modelRelations (CoeffPoly a h) surface a h).map
        (algebraMap (IntegralForms a h) (BigradedPolynomial a h)) := by
  let P := CoeffPoly a h
  let F := Coeff a h
  let M := (nonZeroDivisors P).map (C (σ := Generator a h))
  let f := (model P a h).toRingHom
  have hC (p : P) : f (C p) = C p := by
    change model P a h (C p) = C p
    simp [model, MvPolynomial.algebraMap_eq]
  have hM : M.map f = (nonZeroDivisors P).map (C (σ := Target)) := by
    ext p
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, (hC r).symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨C r, ⟨r, hr, rfl⟩, hC r⟩
  have : IsLocalization (M.map f) (MvPolynomial Target F) := hM ▸ MvPolynomial.isLocalization _ _
  have hcomm := model_map (algebraMap P F) a h
  rw [modelRelations, ← targetIdeal_map (algebraMap P F)
    (IsScalarTower.algebraMap_eq GeoField P F).symm]
  exact comap_of_localization f (model F a h).toRingHom M hcomm.symm _

end

end K1_13_6_1_4_2_1_1_2
end PackSource_K1_13_6_1_4_2_1_1_2Model

section PackSource_K1_13_6_1_4_2_1_2_2_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_2_1_2_2_2

noncomputable section

open Algebra MvPolynomial
open scoped BigOperators

/-- The prime quotient through which the boundary point factors has dimension
at least one less than that of the affine domain. -/
private theorem boundary_trdeg {k A E : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [Field E] [Algebra k E]
    (hdim : trdeg k A ≤ 2) (b : A) (hb : b ≠ 0) (f : A →ₐ[k] E) (hfb : f b = 0) :
    trdeg k (A ⧸ RingHom.ker f) ≤ 1 := by
  let P := RingHom.ker f
  let : P.IsPrime := RingHom.ker_isPrime f
  obtain ⟨d, hA, htA⟩ := K1_13_6_1_4_2_1_2_2.affineDimension k A
  obtain ⟨e, hQ, htQ⟩ := K1_13_6_1_4_2_1_2_2.affineDimension k (A ⧸ P)
  have hd : d ≤ 2 := by
    rw [htA] at hdim
    exact_mod_cast hdim
  have hbq : Ideal.Quotient.mk P b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hfb
  have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hb) hbq
  have hcast : ((e + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
    simpa only [hQ, hA, Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one]
      using hdrop
  have hle : e + 1 ≤ d := by exact_mod_cast hcast
  have he : e ≤ 1 := by omega
  rw [htQ]
  exact_mod_cast he

/-- Lift the nonpivot entries to indeterminates and solve the normalized
equation for the pivot. -/
private def blockLift {D I J : Type} [CommRing D] [Fintype I] [DecidableEq I]
    (i : I) (tag : {m : I // m ≠ i} → J) (w : I → D) (m : I) : MvPolynomial J D :=
  if hm : m ≠ i then MvPolynomial.X (tag ⟨m, hm⟩)
  else -∑ x, MvPolynomial.X (tag x) * C (w x)

private theorem eval_blockLift {D E I J : Type} [CommRing D] [CommRing E]
    [Fintype I] [DecidableEq I]
    (f : D →+* E) (z : J → E) (i : I) (tag : {m : I // m ≠ i} → J)
    (w : I → D) (p : I → E) (hw : f (w i) = 1)
    (hvar : ∀ x, z (tag x) = p x.val) (hz : (∑ m, p m * f (w m)) = 0)
    (m : I) : eval₂Hom f z (blockLift i tag w m) = p m := by
  by_cases hm : m ≠ i
  · rw [blockLift, dite_eq_left hm, eval₂Hom_X']
    exact hvar ⟨m, hm⟩
  · have heq : m = i := not_ne_iff.mp hm
    subst m
    rw [blockLift, dite_eq_right hm]
    simp only [map_neg, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C, hvar]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hw, mul_one] at hz
    exact (eq_neg_of_add_eq_zero_left hz).symm

/-- A boundary point with both normalized linear sums zero would lift all
the independent coefficients into an algebra of insufficient transcendence degree. -/
theorem proof : K1_13_6_1_4_2_1_2_2.c2 := by
  classical
  intro k A E σ τ _ _ _ _ _ _ _ _ _ t ht hd b hb f hfb i j u v hui hvj hu hv
  let P := RingHom.ker f
  let : P.IsPrime := RingHom.ker_isPrime f
  let D := A ⧸ P
  let J := {m : σ // m ≠ i} ⊕ {m : τ // m ≠ j}
  let g : D →ₐ[k] E := Ideal.kerLiftAlg f
  let u' (m : σ) : D := Ideal.Quotient.mk P (u m)
  let v' (m : τ) : D := Ideal.Quotient.mk P (v m)
  let z : J → E := t ∘ Sum.map Subtype.val Subtype.val
  let ev : MvPolynomial J D →ₐ[k] E :=
    { eval₂Hom g.toRingHom z with
      commutes' := fun a => by
        change eval₂Hom g.toRingHom z (C (algebraMap k D a)) = _
        rw [eval₂Hom_C]
        exact g.commutes a }
  let s : σ ⊕ τ → MvPolynomial J D :=
    Sum.elim (blockLift i Sum.inl u') (blockLift j Sum.inr v')
  have hcomp : ev ∘ s = t := by
    funext l
    cases l with
    | inl m =>
      exact eval_blockLift g.toRingHom z i Sum.inl u' (fun x => t (Sum.inl x))
        (by change f (u i) = 1; rw [hui, map_one]) (fun _ => rfl) hu m
    | inr m =>
      exact eval_blockLift g.toRingHom z j Sum.inr v' (fun x => t (Sum.inr x))
        (by change f (v j) = 1; rw [hvj, map_one]) (fun _ => rfl) hv m
  have hs : AlgebraicIndependent k s :=
    AlgebraicIndependent.of_comp ev (hcomp.symm ▸ ht)
  have hD : trdeg k D ≤ 1 := boundary_trdeg hd b hb f hfb
  let : FaithfulSMul D (MvPolynomial J D) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (C_injective J D)
  have hdim : trdeg k (MvPolynomial J D) = trdeg k D + Cardinal.mk J := by
    rw [← trdeg_add_eq k D (A := MvPolynomial J D), MvPolynomial.trdeg_of_isDomain,
      Cardinal.lift_id]
  have hle : Cardinal.mk (σ ⊕ τ) ≤ 1 + Cardinal.mk J := by
    refine hs.cardinalMk_le_trdeg.trans ?_
    rw [hdim]
    gcongr
  have hcard : Fintype.card (σ ⊕ τ) ≤ 1 + Fintype.card J := by
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype] at hle
    exact_mod_cast hle
  have hσ := Fintype.card_congr (Equiv.optionSubtypeNe i)
  have hτ := Fintype.card_congr (Equiv.optionSubtypeNe j)
  simp only [Fintype.card_option] at hσ hτ
  simp only [J, Fintype.card_sum] at hcard
  omega

end

end K1_13_6_1_4_2_1_2_2_2
end PackSource_K1_13_6_1_4_2_1_2_2_2Proof

section PackSource_K1_13_6_1_4_2_1_1Split
set_option autoImplicit true
namespace K1_13_6_1_4_2_1_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1
open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- Independent generic sections are nonzerodivisors on the uncut surface. -/
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    Function.Injective (leftMul surface a h) ∧ Function.Injective (rightMul surface a h)

/-- The second section acts injectively on the first section quotient on each product chart.
The chart formulation clears powers of the inverted homogeneous coordinate. -/
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    ∀ (x : latticeIndices a) (y : latticeIndices h) (p : BigradedPolynomial a h),
      p * rightForm a h ∈ firstCut surface a h →
      ∃ n : ℕ, chart x y ^ n * p ∈ firstCut surface a h

private theorem dehom_mul_left (surface : Ideal GeoJets) (a h : Shape)
    (p : BigradedPolynomial a h) :
    dehom surface a h (p * leftForm a h) =
      leftMul surface a h (dehom surface a h p) := by
  rw [map_mul, dehom_left, leftMul, LinearMap.mulLeft_apply]
  exact mul_comm (dehom surface a h p)
    (Ideal.Quotient.mk (extendIdeal surface a h) (leftSection a h))

private theorem dehom_mul_right (surface : Ideal GeoJets) (a h : Shape)
    (p : BigradedPolynomial a h) :
    dehom surface a h (p * rightForm a h) =
      rightMul surface a h (dehom surface a h p) := by
  rw [map_mul, dehom_right, rightMul, LinearMap.mulLeft_apply]
  exact mul_comm (dehom surface a h p)
    (Ideal.Quotient.mk (extendIdeal surface a h) (rightSection a h))

private theorem muls_commute (surface : Ideal GeoJets) (a h : Shape)
    (x : SurfaceRing surface a h) :
    rightMul surface a h (leftMul surface a h x) =
      leftMul surface a h (rightMul surface a h x) := by
  simp only [leftMul, rightMul, LinearMap.mulLeft_apply]
  exact mul_left_comm _ _ x

private theorem lift_piece (surface : Ideal GeoJets) {a h : Shape}
    (ha : FullChamber a) (hh : FullChamber h) {i j : ℕ}
    {w : SurfaceRing surface a h} (hw : w ∈ biPiece surface a h i j) :
    ∃ p : BigradedPolynomial a h, p ∈ grade (i, j) ∧ dehom surface a h p = w := by
  rw [← dehom_grade surface ha.1 hh.1] at hw
  exact hw

private theorem dehom_mem_piece (surface : Ideal GeoJets) {a h : Shape}
    (ha : FullChamber a) (hh : FullChamber h) {i j : ℕ}
    {p : BigradedPolynomial a h} (hp : p ∈ grade (i, j)) :
    dehom surface a h p ∈ biPiece surface a h i j := by
  rw [← dehom_grade surface ha.1 hh.1]
  exact ⟨p, hp, rfl⟩

private theorem firstCut_homogeneous (surface : Ideal GeoJets) (a h : Shape) :
    (firstCut surface a h).IsHomogeneous grade := by
  unfold firstCut
  apply (relations_homogeneous surface a h).sup
  apply Ideal.homogeneous_span
  rintro _ ⟨⟩
  exact ⟨(1, 0), leftForm_grade a h⟩

private theorem exists_high_intersection (h2 : c2) (surface : Ideal GeoJets) (a h : Shape)
    (hs : surface.IsPrime) (hd : ringKrullDim (GeoJets ⧸ surface) = 2)
    (ha : FullChamber a) (hh : FullChamber h) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊓
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) =
      (biPiece surface a h i j).map ((leftMul surface a h).comp (rightMul surface a h)) := by
  classical
  let : Fintype (latticeIndices a) := Fintype.ofFinite _
  let : Fintype (latticeIndices h) := Fintype.ofFinite _
  let I := firstCut surface a h
  let K := I.colon {rightForm a h}
  have hI := firstCut_homogeneous surface a h
  have hK : K.IsHomogeneous grade := homogeneous_colon hI (rightForm_grade a h)
  have hlocal (x : latticeIndices a) (y : latticeIndices h) (p : BigradedPolynomial a h)
      (hp : p ∈ K) : ∃ n : ℕ, chart x y ^ n * p ∈ I :=
    h2 surface a h hs hd ha hh x y p (Submodule.mem_colon_singleton.mp hp)
  obtain ⟨N, hN⟩ := high_degree_of_charts I K hK hlocal
  refine ⟨N, fun i j hi hj => le_antisymm ?_ ?_⟩
  · rintro w ⟨hw₁, hw₂⟩
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.mp hw₁
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp hw₂
    obtain ⟨p, hp, hpu⟩ := lift_piece surface ha hh hu
    obtain ⟨q, hq, hqv⟩ := lift_piece surface ha hh hv
    have hpL : p * leftForm a h ∈ grade (i + 1, j + 1) :=
      IsWeightedHomogeneous.mul hp (leftForm_grade a h)
    have hqR : q * rightForm a h ∈ grade (i + 1, j + 1) :=
      IsWeightedHomogeneous.mul hq (rightForm_grade a h)
    have hsubloc : q * rightForm a h - p * leftForm a h ∈ relations surface a h := by
      have hgrade : q * rightForm a h - p * leftForm a h ∈ grade (i + 1, j + 1) :=
        Submodule.sub_mem (grade (k := Coeff a h) (α := latticeIndices a)
          (β := latticeIndices h) (i + 1, j + 1)) hqR hpL
      apply mem_relations_of_dehom_eq_zero hgrade
      rw [map_sub, dehom_mul_right, dehom_mul_left, hqv, hpu, hve, hue, sub_self]
    have hpLcut : p * leftForm a h ∈ I :=
      Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨p, rfl⟩)
    have hqK : q ∈ K := by
      apply Submodule.mem_colon_singleton.mpr
      change q * rightForm a h ∈ I
      rw [← sub_add_cancel (q * rightForm a h) (p * leftForm a h)]
      exact I.add_mem (Submodule.mem_sup_left hsubloc) hpLcut
    have hqI := hN (i + 1) j (hi.trans (Nat.le_succ i)) hj q hqK hq
    obtain ⟨r, hr, s, hspan, hsum⟩ := Submodule.mem_sup.mp hqI
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hspan
    let z := weightedHomogeneousComponent weight (i, j) t
    have hz : z ∈ grade (i, j) := weightedHomogeneousComponent_mem _ _ _
    have hcomp := congrArg (weightedHomogeneousComponent weight ((i, j) + (1, 0))) hsum
    have hq' : q ∈ grade ((i, j) + (1, 0)) := hq
    rw [map_add, component_mul (leftForm_grade a h),
      weightedHomogeneousComponent_eq_self hq'] at hcomp
    have hrel := weightedHomogeneousComponent_mem_of_mem _ _
      (relations_homogeneous surface a h) hr ((i, j) + (1, 0))
    have hdiv : leftMul surface a h (dehom surface a h z) = v := by
      have he := congrArg (dehom surface a h) hcomp
      rw [map_add, dehom_eq_zero_of_mem_relations hrel, zero_add, dehom_mul_left, hqv] at he
      exact he
    refine Submodule.mem_map.mpr ⟨dehom surface a h z, dehom_mem_piece surface ha hh hz, ?_⟩
    rw [LinearMap.comp_apply, ← hve, ← hdiv]
    exact (muls_commute surface a h _).symm
  · rintro w hw
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.mp hw
    obtain ⟨p, hp, hpu⟩ := lift_piece surface ha hh hu
    have hpL : p * leftForm a h ∈ grade (i + 1, j) :=
      IsWeightedHomogeneous.mul hp (leftForm_grade a h)
    have hpR : p * rightForm a h ∈ grade (i, j + 1) :=
      IsWeightedHomogeneous.mul hp (rightForm_grade a h)
    refine ⟨Submodule.mem_map.mpr ⟨_, dehom_mem_piece surface ha hh hpR, ?_⟩,
      Submodule.mem_map.mpr ⟨_, dehom_mem_piece surface ha hh hpL, ?_⟩⟩
    · rw [dehom_mul_right, hpu]
      exact hue
    · rw [dehom_mul_left, hpu, ← hue, LinearMap.comp_apply]
      exact muls_commute surface a h u

theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2_1.c1 := by
  intro surface a h hs hd ha hh
  obtain ⟨hl, hr⟩ := h1 surface a h hs hd ha hh
  exact ⟨hl, hr, exists_high_intersection h2 surface a h hs hd ha hh⟩

end
end K1_13_6_1_4_2_1_1
end PackSource_K1_13_6_1_4_2_1_1Split

section PackSource_K1_13_6_1_4_2_1_1_2Proof
set_option autoImplicit true
set_option maxHeartbeats 1200000

namespace K1_13_6_1_4_2_1_1_2

noncomputable section

open K1_13 (Shape)
open K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_1
open MvPolynomial
open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.algebraMvPolynomial

private def coordinate {γ : Type} (b : Shape) (i : latticeIndices b → γ)
    (m : SectionIndex (b.scale 6)) : MvPolynomial γ GeoField :=
  if hm : m ∈ boxMonomials (b.scale 6) then
    MvPolynomial.X (i ⟨boxExponent m, boxExponent_mem b ⟨m, hm⟩⟩)
  else 0

private def integralForm {γ τ : Type} (b : Shape) (i : latticeIndices b → γ)
    (j : SectionIndex (b.scale 6) → τ) : MvPolynomial γ (MvPolynomial τ GeoField) :=
  ∑ m ∈ boxMonomials (b.scale 6), C (MvPolynomial.X (j m)) *
    MvPolynomial.map C (coordinate b i m)

private abbrev leftIntegral (a h : Shape) : IntegralForms a h := integralForm a Sum.inl Sum.inl
private abbrev rightIntegral (a h : Shape) : IntegralForms a h := integralForm h Sum.inr Sum.inr

private theorem integralForm_map {γ τ : Type} (b : Shape) (i : latticeIndices b → γ)
    (j : SectionIndex (b.scale 6) → τ) :
    let P := MvPolynomial τ GeoField
    let F := FractionRing P
    MvPolynomial.map (algebraMap P F) (integralForm b i j) =
      ∑ m ∈ (boxMonomials (b.scale 6)).attach,
        C (algebraMap P F (MvPolynomial.X (j m.val))) *
          MvPolynomial.X (i ⟨boxExponent m.val, boxExponent_mem b m⟩) := by
  dsimp only
  unfold integralForm
  rw [map_sum]
  rw [← Finset.sum_attach (boxMonomials (b.scale 6))]
  apply Finset.sum_congr rfl
  intro m _
  simp [coordinate, m.property]

private theorem coordinate_covers {γ : Type} (b : Shape) (i : latticeIndices b → γ)
    (y : latticeIndices b) : ∃ m ∈ boxMonomials (b.scale 6), coordinate b i m = MvPolynomial.X (i y) := by
  have hy : (fun j => y.val j) ∈ exponents (b.scale 6) := y.property
  rw [exponents_eq_image] at hy
  obtain ⟨m, hm, he⟩ := hy
  have hey : (⟨boxExponent m, boxExponent_mem b ⟨m, hm⟩⟩ : latticeIndices b) = y := by
    apply Subtype.ext
    ext j
    simpa [boxExponent] using congrFun he j
  have hm' : m ∈ boxMonomials (b.scale 6) := hm
  exact ⟨m, hm', by simp only [coordinate, dite_eq_left hm', hey]⟩

private theorem integral_cancel (surface : Ideal GeoJets) (a h : Shape)
    (x : latticeIndices a) (y : latticeIndices h) (p : IntegralForms a h)
    (hp : p * rightIntegral a h ∈
      modelRelations (CoeffPoly a h) surface a h ⊔ Ideal.span {leftIntegral a h}) :
    ∃ n : ℕ, chart x y ^ n * p ∈
      modelRelations (CoeffPoly a h) surface a h ⊔ Ideal.span {leftIntegral a h} := by
  let α := SectionIndex (a.scale 6)
  let β := SectionIndex (h.scale 6)
  let σ := Generator a h
  let J := modelRelations GeoField surface a h
  let Q := MvPolynomial σ GeoField ⧸ J
  let : CommRing Q := inferInstanceAs (CommRing (MvPolynomial σ GeoField ⧸ J))
  let q : MvPolynomial σ GeoField →+* Q := Ideal.Quotient.mk J
  let e := commAlgEquiv GeoField σ (α ⊕ β)
  let f := (MvPolynomial.map q).comp e.toRingHom
  let E := (renameEquiv Q (Equiv.sumComm α β)).trans (sumAlgEquiv Q β α)
  let g := E.toRingHom.comp f
  have hf : RingHom.ker f = modelRelations (CoeffPoly a h) surface a h := by
    change RingHom.ker ((MvPolynomial.map q).comp e.toRingHom) = _
    rw [← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker,
      modelRelations_polynomial, ← commAlgEquiv_comp_map_C GeoField σ (α ⊕ β),
      ← Ideal.map_map]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  have hg : RingHom.ker g = modelRelations (CoeffPoly a h) surface a h := by
    rw [show g = E.toRingHom.comp f from rfl, ← hf]
    ext z
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change E (f z) = 0 ↔ f z = 0
    rw [← map_zero E]
    exact E.injective.eq_iff
  have hconst (v : MvPolynomial σ GeoField) :
      g (MvPolynomial.map C v) = C (C (q v)) := by
    change E (MvPolynomial.map q (e (MvPolynomial.map C v))) = _
    have hv := DFunLike.congr_fun (commAlgEquiv_comp_map_C GeoField σ (α ⊕ β)) v
    change e (MvPolynomial.map C v) = C v at hv
    rw [hv, MvPolynomial.map_C]
    simp [E, renameEquiv_apply, sumAlgEquiv_C_inl]
  have hleft (m : α) : g (C (MvPolynomial.X (Sum.inl m))) = C (MvPolynomial.X m) := by
    change E (MvPolynomial.map q (e (C (MvPolynomial.X (Sum.inl m))))) = _
    rw [commAlgEquiv_C_X, MvPolynomial.map_X]
    simp [E, renameEquiv_apply, sumAlgEquiv_X_inr]
  have hright (m : β) : g (C (MvPolynomial.X (Sum.inr m))) = MvPolynomial.X m := by
    change E (MvPolynomial.map q (e (C (MvPolynomial.X (Sum.inr m))))) = _
    rw [commAlgEquiv_C_X, MvPolynomial.map_X]
    simp [E, renameEquiv_apply, sumAlgEquiv_X_inl]
  let l : MvPolynomial α Q := ∑ m ∈ boxMonomials (a.scale 6),
    C (q (coordinate a Sum.inl m)) * MvPolynomial.X m
  let w : β → Q := fun m => q (coordinate h Sum.inr m)
  have hl : g (leftIntegral a h) = C l := by
    simp only [leftIntegral, integralForm, map_sum, map_mul, hleft, hconst, l]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hr : g (rightIntegral a h) = ∑ m ∈ boxMonomials (h.scale 6), C (C (w m)) * MvPolynomial.X m := by
    simp only [rightIntegral, integralForm, map_sum, map_mul, hright, hconst, w]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  obtain ⟨m, hm, he⟩ := coordinate_covers h (Sum.inr : latticeIndices h → σ) y
  have hchart : g (chart x y) = C (C (q (MvPolynomial.X (Sum.inl x)) * w m)) := by
    have hh := hconst (chart x y : MvPolynomial σ GeoField)
    simpa only [chart, map_mul, MvPolynomial.map_X, w, he] using hh
  have hsurj : Function.Surjective g :=
    E.surjective.comp ((MvPolynomial.map_surjective q Ideal.Quotient.mk_surjective).comp e.surjective)
  have hcut : (Ideal.span {C l}).comap g =
      modelRelations (CoeffPoly a h) surface a h ⊔ Ideal.span {leftIntegral a h} := by
    rw [← hl, Ideal.comap_span_singleton_of_surjective g hsurj, hg]
  rw [← hcut, Ideal.mem_comap, map_mul, hr] at hp
  obtain ⟨n, hn⟩ := cancel_chart l _ w m hm (q (MvPolynomial.X (Sum.inl x))) (g p) hp
  refine ⟨n, ?_⟩
  rwa [← hcut, Ideal.mem_comap, map_mul, map_pow, hchart]

theorem proof : K1_13_6_1_4_2_1_1.c2 := by
  intro surface a h _ _ _ _ x y p hp
  let A := IntegralForms a h
  let B := BigradedPolynomial a h
  let M := (nonZeroDivisors (CoeffPoly a h)).map (C (σ := Generator a h))
  let g := algebraMap A B
  let I := modelRelations (CoeffPoly a h) surface a h ⊔ Ideal.span {leftIntegral a h}
  have : IsLocalization M B := MvPolynomial.isLocalization _ _
  have hl : g (leftIntegral a h) = leftForm a h := integralForm_map a Sum.inl Sum.inl
  have hr : g (rightIntegral a h) = rightForm a h := integralForm_map h Sum.inr Sum.inr
  have hz : g (chart x y) = chart x y := by
    change MvPolynomial.map (algebraMap (CoeffPoly a h) (Coeff a h)) (chart x y) = _
    simp [chart]
  have hI : I.map g = firstCut surface a h := by
    simp only [I, firstCut, Ideal.map_sup, Ideal.map_span, Set.image_singleton, hl,
      relations_eq_model, modelRelations_fraction, g]
    rfl
  have hreg : ∀ q : A, q * rightIntegral a h ∈ I → ∃ n : ℕ, chart x y ^ n * q ∈ I :=
    integral_cancel surface a h x y
  have hmem : p * g (rightIntegral a h) ∈ I.map g := by rwa [hr, hI]
  have hres : ∃ n : ℕ, g (chart x y) ^ n * p ∈ I.map g :=
    cancel_localization M I (chart x y) (rightIntegral a h) hreg p hmem
  rwa [hz, hI] at hres

end

end K1_13_6_1_4_2_1_1_2
end PackSource_K1_13_6_1_4_2_1_1_2Proof

section PackSource_K1_13_2_3_6AuxA
set_option autoImplicit true
namespace K1_13_2_3_6

section

set_option maxRecDepth 50000
set_option maxHeartbeats 0

-- Check each grade in its own declaration so replay reduces only one row at a time.

private def rowsA_grade3012 : List (List ℕ) :=
  [[8791654400, 13086490624, 8724414464, 6576865280, 6543310848, 4395761664, 4362207232,
    2214690816, 50429952, 2214592704, 4345299136, 33554624, 25166016, 16777408, 12583104,
    4194496, 6442451136, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072, 112, 108, 102,
    98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18, 16,
    12, 6, 2]]

private theorem rowsA_grade3012_checked :
    rowsA_grade3012.length = 1 ∧ fits 3012 rowsA_grade3012 = true ∧
      value 3012 rowsA_grade3012 = 56171069 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3013 : List (List ℕ) :=
  [[0, 8791654400, 13086490624, 6576930816, 8724348928, 4395827200, 6543245312, 4362207232,
    67207168, 2197913600, 2214592704, 2197815488, 2181038272, 25166016, 16777408, 6291648,
    8589934784, 160, 2147483800, 2147483792, 140, 134, 129, 6442451072, 112, 108, 102, 97,
    6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17, 16, 12,
    6, 1]]

private theorem rowsA_grade3013_checked :
    rowsA_grade3013.length = 1 ∧ fits 3013 rowsA_grade3013 = true ∧
      value 3013 rowsA_grade3013 = 55575093 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3014 : List (List ℕ) :=
  [[0, 10939138048, 10939006976, 8724414464, 6576865280, 6543310848, 4395761664, 4362207232,
    67207168, 2197913600, 2214592704, 2197815488, 2181038272, 25166016, 16777408, 8388800,
    2097344, 8589934784, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100,
    8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8,
    4]]

private theorem rowsA_grade3014_checked :
    rowsA_grade3014.length = 1 ∧ fits 3014 rowsA_grade3014 = true ∧
      value 3014 rowsA_grade3014 = 56103008 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3015 : List (List ℕ) :=
  [[0, 10939138048, 13086490624, 6576930816, 8724348928, 6543310848, 2248278016, 6509690880,
    67207168, 2197913600, 2214592704, 2197815488, 33554624, 2172649664, 12583104, 6291648,
    8589934784, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108, 104, 99,
    8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16, 12, 8,
    3]]

private theorem rowsA_grade3015_checked :
    rowsA_grade3015.length = 1 ∧ fits 3015 rowsA_grade3015 = true ∧
      value 3015 rowsA_grade3015 = 56895847 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3016 : List (List ℕ) :=
  [[2147483648, 10939138048, 10939006976, 8724414464, 6576865280, 6543310848, 4395761664,
    4362207232, 50462720, 2197913600, 2214592704, 2197815488, 2181038272, 25166016, 16777408,
    8388800, 10737418432, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072, 112, 108, 102,
    98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18, 16,
    12, 6, 2]]

private theorem rowsA_grade3016_checked :
    rowsA_grade3016.length = 1 ∧ fits 3016 rowsA_grade3016 = true ∧
      value 3016 rowsA_grade3016 = 56371788 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3017 : List (List ℕ) :=
  [[2147483648, 10939138048, 10939006976, 10871898112, 4429381632, 8690794496, 2248278016,
    4362207232, 50462720, 67207168, 2197913600, 67109056, 4345299136, 33554624, 25166016,
    16777408, 12583104, 4194496, 10737418432, 160, 2147483800, 2147483792, 140, 134, 129,
    6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696,
    38, 33, 32, 25, 24, 17, 16, 12, 6, 1]]

private theorem rowsA_grade3017_checked :
    rowsA_grade3017.length = 1 ∧ fits 3017 rowsA_grade3017 = true ∧
      value 3017 rowsA_grade3017 = 57063697 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3018 : List (List ℕ) :=
  [[4294967296, 10939138048, 10939006976, 8724414464, 6576865280, 6543310848, 2248278016,
    6509690880, 50462720, 2197913600, 2214592704, 2197815488, 2181038272, 25166016, 16777408,
    6291648, 12884902080, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100,
    8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8,
    4]]

private theorem rowsA_grade3018_checked :
    rowsA_grade3018.length = 1 ∧ fits 3018 rowsA_grade3018 = true ∧
      value 3018 rowsA_grade3018 = 56668144 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3019 : List (List ℕ) :=
  [[4294967296, 10939138048, 10939006976, 10871898112, 4429381632, 8690794496, 2248278016,
    4362207232, 50462720, 4345397248, 67109056, 2197815488, 2181038272, 25166016, 16777408,
    8388800, 2097344, 10737418432, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108,
    104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16,
    12, 8, 3]]

private theorem rowsA_grade3019_checked :
    rowsA_grade3019.length = 1 ∧ fits 3019 rowsA_grade3019 = true ∧
      value 3019 rowsA_grade3019 = 57382107 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3020 : List (List ℕ) :=
  [[4294967296, 13086621696, 10939006976, 8724414464, 4429381632, 8690794496, 67305472,
    100794368, 6509690880, 50462720, 2197913600, 2214592704, 2197815488, 33554624, 2172649664,
    12583104, 6291648, 12884902080, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072, 112,
    108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26,
    24, 18, 16, 12, 6, 2]]

private theorem rowsA_grade3020_checked :
    rowsA_grade3020.length = 1 ∧ fits 3020 rowsA_grade3020 = true ∧
      value 3020 rowsA_grade3020 = 58013970 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3021 : List (List ℕ) :=
  [[6442450944, 10939138048, 10939006976, 10871898112, 4429381632, 6543310848, 67305472,
    2248278016, 4362207232, 50462720, 2197913600, 98560, 67109056, 2197815488, 2181038272,
    25166016, 16777408, 8388800, 2097344, 12884902080, 160, 2147483800, 2147483792, 140, 134,
    129, 6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49,
    2147483696, 38, 33, 32, 25, 24, 17, 16, 12, 6, 1]]

private theorem rowsA_grade3021_checked :
    rowsA_grade3021.length = 1 ∧ fits 3021 rowsA_grade3021 = true ∧
      value 3021 rowsA_grade3021 = 57706514 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3022 : List (List ℕ) :=
  [[6442450944, 13086621696, 8791523328, 10871898112, 4429381632, 8690794496, 67305472,
    100794368, 4362207232, 2197946368, 50429952, 98560, 98496, 67109056, 2197815488, 33554624,
    25166016, 16777408, 12583104, 4194496, 15032385728, 160, 2147483800, 144, 140, 136, 132,
    8589934720, 108, 104, 100, 8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36,
    2147483680, 2147483672, 16, 12, 8, 4]]

private theorem rowsA_grade3022_checked :
    rowsA_grade3022.length = 1 ∧ fits 3022 rowsA_grade3022 = true ∧
      value 3022 rowsA_grade3022 = 58257555 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3023 : List (List ℕ) :=
  [[8589934592, 13086621696, 8791523328, 10871898112, 4429381632, 6543310848, 67305472,
    100794368, 6509690880, 2197946368, 2147582208, 67109056, 2197815488, 2181038272, 25166016,
    16777408, 8388800, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108,
    104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16,
    12, 8, 3]]

private theorem rowsA_grade3023_checked :
    rowsA_grade3023.length = 1 ∧ fits 3023 rowsA_grade3023 = true ∧
      value 3023 rowsA_grade3023 = 57679792 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3024 : List (List ℕ) :=
  [[8589934592, 13086621696, 8791523328, 13019381760, 2281897984, 8690794496, 67305472,
    100794368, 4362207232, 2197946368, 50429952, 2147582208, 2197815488, 2181038272, 25166016,
    16777408, 12583104, 2097344, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130,
    6442451072, 112, 108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696,
    38, 34, 32, 26, 24, 18, 16, 12, 6, 2]]

private theorem rowsA_grade3024_checked :
    rowsA_grade3024.length = 1 ∧ fits 3024 rowsA_grade3024 = true ∧
      value 3024 rowsA_grade3024 = 58493504 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3025 : List (List ℕ) :=
  [[8589934592, 15234105344, 8791523328, 10871898112, 2281897984, 8690794496, 2214789120,
    6509690880, 2197946368, 2147582208, 67109120, 2197815488, 33554624, 2172649664, 12583104,
    6291648, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134, 129, 6442451072, 112, 108,
    102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17,
    16, 12, 6, 1]]

private theorem rowsA_grade3025_checked :
    rowsA_grade3025.length = 1 ∧ fits 3025 rowsA_grade3025 = true ∧
      value 3025 rowsA_grade3025 = 59069395 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3026 : List (List ℕ) :=
  [[10737418240, 13086621696, 8791523328, 13019381760, 2281897984, 6543310848, 2214789120,
    100794368, 4362207232, 2197946368, 2147582208, 67109120, 50331904, 50331840, 2181038272,
    25166016, 16777408, 8388800, 196, 17179869376, 160, 2147483800, 144, 140, 136, 132,
    8589934720, 108, 104, 100, 8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36,
    2147483680, 2147483672, 16, 12, 8, 4]]

private theorem rowsA_grade3026_checked :
    rowsA_grade3026.length = 1 ∧ fits 3026 rowsA_grade3026 = true ∧
      value 3026 rowsA_grade3026 = 58930449 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3027 : List (List ℕ) :=
  [[10737418240, 15234105344, 6644039680, 13019381760, 2281897984, 8690794496, 2214789120,
    4362207232, 4345430016, 2147582208, 67109120, 2197815488, 33554624, 25166016, 16777408,
    12583104, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720,
    108, 104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680,
    2147483672, 16, 12, 8, 3]]

private theorem rowsA_grade3027_checked :
    rowsA_grade3027.length = 1 ∧ fits 3027 rowsA_grade3027 = true ∧
      value 3027 rowsA_grade3027 = 59459098 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3028 : List (List ℕ) :=
  [[12884901888, 13086621696, 8791523328, 10871898112, 100925440, 2281897984, 6543310848,
    2214789120, 6509690880, 2197946368, 33685504, 98560, 67109120, 50331904, 50331840,
    2181038272, 25166016, 16777408, 8388800, 198, 194, 15032385728, 160, 2147483800, 2147483792,
    140, 134, 130, 6442451072, 112, 108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54,
    50, 2147483696, 38, 34, 32, 26, 24, 18, 16, 12, 6, 2]]

private theorem rowsA_grade3028_checked :
    rowsA_grade3028.length = 1 ∧ fits 3028 rowsA_grade3028 = true ∧
      value 3028 rowsA_grade3028 = 59274138 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3029 : List (List ℕ) :=
  [[12884901888, 15234105344, 6644039680, 13019381760, 100925440, 134414336, 8690794496,
    2214789120, 4362207232, 2197946368, 33685504, 2147582208, 2197815552, 50331840, 33554624,
    25166016, 16777408, 12583104, 204, 198, 193, 15032385728, 160, 2147483800, 2147483792, 140,
    134, 129, 6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49,
    2147483696, 38, 33, 32, 25, 24, 17, 16, 12, 6, 1]]

private theorem rowsA_grade3029_checked :
    rowsA_grade3029.length = 1 ∧ fits 3029 rowsA_grade3029 = true ∧
      value 3029 rowsA_grade3029 = 59729025 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3030 : List (List ℕ) :=
  [[12884901888, 17381588992, 4496556032, 13019381760, 100925440, 134414336, 8690794496,
    2214789120, 6509690880, 2197946368, 131328, 98560, 67109120, 2197815552, 2181038272,
    25166016, 12583104, 204, 200, 196, 17179869376, 160, 2147483800, 144, 140, 136, 132,
    8589934720, 108, 104, 100, 8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36,
    2147483680, 2147483672, 16, 12, 8, 4]]

private theorem rowsA_grade3030_checked :
    rowsA_grade3030.length = 1 ∧ fits 3030 rowsA_grade3030 = true ∧
      value 3030 rowsA_grade3030 = 60419416 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private def rowsA_grade3031 : List (List ℕ) :=
  [[15032385536, 15234105344, 6644039680, 13019381760, 100925440, 134414336, 6543310848,
    4362272768, 4362207232, 2197946368, 33685504, 2147582208, 2197815552, 2181038272, 25166016,
    16777408, 208, 204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131,
    8589934720, 108, 104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35,
    2147483680, 2147483672, 16, 12, 8, 3]]

private theorem rowsA_grade3031_checked :
    rowsA_grade3031.length = 1 ∧ fits 3031 rowsA_grade3031 = true ∧
      value 3031 rowsA_grade3031 = 60143148 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

/-- Certified factor products for grades 3012 through 3031. -/
def rowsA : List (List ℕ) :=
  rowsA_grade3012 ++ rowsA_grade3013 ++ rowsA_grade3014 ++ rowsA_grade3015 ++ rowsA_grade3016 ++
    rowsA_grade3017 ++ rowsA_grade3018 ++ rowsA_grade3019 ++ rowsA_grade3020 ++ rowsA_grade3021
    ++ rowsA_grade3022 ++ rowsA_grade3023 ++ rowsA_grade3024 ++ rowsA_grade3025 ++
    rowsA_grade3026 ++ rowsA_grade3027 ++ rowsA_grade3028 ++ rowsA_grade3029 ++ rowsA_grade3030
    ++ rowsA_grade3031

theorem checkA :
    rowsA.length = 20 ∧ fits 3012 rowsA = true ∧
      value 3012 rowsA = 1159406757 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [rowsA, List.length_append, Nat.reduceAdd, rowsA_grade3012_checked.1,
      rowsA_grade3013_checked.1, rowsA_grade3014_checked.1, rowsA_grade3015_checked.1,
      rowsA_grade3016_checked.1, rowsA_grade3017_checked.1, rowsA_grade3018_checked.1,
      rowsA_grade3019_checked.1, rowsA_grade3020_checked.1, rowsA_grade3021_checked.1,
      rowsA_grade3022_checked.1, rowsA_grade3023_checked.1, rowsA_grade3024_checked.1,
      rowsA_grade3025_checked.1, rowsA_grade3026_checked.1, rowsA_grade3027_checked.1,
      rowsA_grade3028_checked.1, rowsA_grade3029_checked.1, rowsA_grade3030_checked.1,
      rowsA_grade3031_checked.1]
  · simp only [fits_append, Bool.true_and, rowsA, List.length_append, Nat.reduceAdd,
      rowsA_grade3012_checked.1, rowsA_grade3013_checked.1, rowsA_grade3014_checked.1,
      rowsA_grade3015_checked.1, rowsA_grade3016_checked.1, rowsA_grade3017_checked.1,
      rowsA_grade3018_checked.1, rowsA_grade3019_checked.1, rowsA_grade3020_checked.1,
      rowsA_grade3021_checked.1, rowsA_grade3022_checked.1, rowsA_grade3023_checked.1,
      rowsA_grade3024_checked.1, rowsA_grade3025_checked.1, rowsA_grade3026_checked.1,
      rowsA_grade3027_checked.1, rowsA_grade3028_checked.1, rowsA_grade3029_checked.1,
      rowsA_grade3030_checked.1, rowsA_grade3012_checked.2.1,
      rowsA_grade3013_checked.2.1, rowsA_grade3014_checked.2.1, rowsA_grade3015_checked.2.1,
      rowsA_grade3016_checked.2.1, rowsA_grade3017_checked.2.1, rowsA_grade3018_checked.2.1,
      rowsA_grade3019_checked.2.1, rowsA_grade3020_checked.2.1, rowsA_grade3021_checked.2.1,
      rowsA_grade3022_checked.2.1, rowsA_grade3023_checked.2.1, rowsA_grade3024_checked.2.1,
      rowsA_grade3025_checked.2.1, rowsA_grade3026_checked.2.1, rowsA_grade3027_checked.2.1,
      rowsA_grade3028_checked.2.1, rowsA_grade3029_checked.2.1, rowsA_grade3030_checked.2.1,
      rowsA_grade3031_checked.2.1]
  · simp only [value_append, rowsA, List.length_append, Nat.reduceAdd,
      rowsA_grade3012_checked.1, rowsA_grade3013_checked.1, rowsA_grade3014_checked.1,
      rowsA_grade3015_checked.1, rowsA_grade3016_checked.1, rowsA_grade3017_checked.1,
      rowsA_grade3018_checked.1, rowsA_grade3019_checked.1, rowsA_grade3020_checked.1,
      rowsA_grade3021_checked.1, rowsA_grade3022_checked.1, rowsA_grade3023_checked.1,
      rowsA_grade3024_checked.1, rowsA_grade3025_checked.1, rowsA_grade3026_checked.1,
      rowsA_grade3027_checked.1, rowsA_grade3028_checked.1, rowsA_grade3029_checked.1,
      rowsA_grade3030_checked.1, rowsA_grade3012_checked.2.2,
      rowsA_grade3013_checked.2.2, rowsA_grade3014_checked.2.2, rowsA_grade3015_checked.2.2,
      rowsA_grade3016_checked.2.2, rowsA_grade3017_checked.2.2, rowsA_grade3018_checked.2.2,
      rowsA_grade3019_checked.2.2, rowsA_grade3020_checked.2.2, rowsA_grade3021_checked.2.2,
      rowsA_grade3022_checked.2.2, rowsA_grade3023_checked.2.2, rowsA_grade3024_checked.2.2,
      rowsA_grade3025_checked.2.2, rowsA_grade3026_checked.2.2, rowsA_grade3027_checked.2.2,
      rowsA_grade3028_checked.2.2, rowsA_grade3029_checked.2.2, rowsA_grade3030_checked.2.2,
      rowsA_grade3031_checked.2.2]

end

end K1_13_2_3_6
end PackSource_K1_13_2_3_6AuxA

section PackSource_K1_13_2_3_5DataE
set_option autoImplicit true
namespace K1_13_2_3_5

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open K1_13_2_3
open private rowLoop rowScore unpack from ProximityPrize.SubmissionLower.Numeric5Certificate

-- Cubic in Horner form for denFast. The residue proof handles rounding.
private def denE (x : Nat) : Nat :=
  let q := Nat.add (Nat.mul 2 x) 15
  let t := Nat.add (Nat.mul q x) 30
  Nat.div (Nat.add (Nat.mul t x) 25) 72

-- Sum of the three consecutive denominator values at x, x-1 and x-2.
private def triE (x : Nat) : Nat :=
  let q := Nat.add (Nat.mul 2 x) 9
  let t := Nat.add (Nat.mul q x) 10
  Nat.div (Nat.add (Nat.mul t x) 3) 24

private theorem divE_helper (y z k : Nat) (hk : k < 36) (h : z = 36*y+k) : y/2 = z/72 := by omega

private theorem denE_residue (q r : Nat) (hr : r < 6) :
    (q * (q * (12*q+21+6*r) + 11+r*(7+r)) + 2+r*(r+1)) / 2 =
      denE (6*q+r+1) := by
  change _ = (((2*(6*q+r+1)+15)*(6*q+r+1)+30)*(6*q+r+1)+25)/72
  interval_cases r
  · apply divE_helper _ _ 0 (by decide); ring
  · apply divE_helper _ _ 17 (by decide); ring
  · apply divE_helper _ _ 16 (by decide); ring
  · apply divE_helper _ _ 9 (by decide); ring
  · apply divE_helper _ _ 8 (by decide); ring
  · apply divE_helper _ _ 25 (by decide); ring

private theorem denE_eq (u : Nat) : denFast u = denE u := by
  cases u with
  | zero => rfl
  | succ n =>
    simp only [denFast, Nat.beq_eq_true_eq, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    have e : 6*(n/6) + n%6 + 1 = n+1 := by omega
    simpa only [e] using denE_residue (n/6) (n%6) (Nat.mod_lt _ (by decide))

private theorem denE_period (q v : Nat) : denE (12*q+v) =
    denE v + (48*q^3 + (12*v+30)*q^2 + (v^2+5*v+5)*q) := by
  change (((2*(12*q+v)+15)*(12*q+v)+30)*(12*q+v)+25) / 72 = (((2*v+15)*v+30)*v+25) / 72 + _
  rw [show (((2*(12*q+v)+15)*(12*q+v)+30)*(12*q+v)+25) = (((2*v+15)*v+30)*v+25)
      + 72*(48*q^3 + (12*v+30)*q^2 + (v^2+5*v+5)*q) by ring,
    Nat.add_mul_div_left _ _ (by decide)]

private theorem triE_period (q v : Nat) : triE (12*q+v) =
    triE v + (144*q^3 + (36*v+54)*q^2 + (3*v^2+9*v+5)*q) := by
  change (((2*(12*q+v)+9)*(12*q+v)+10)*(12*q+v)+3) / 24 = (((2*v+9)*v+10)*v+3) / 24 + _
  rw [show (((2*(12*q+v)+9)*(12*q+v)+10)*(12*q+v)+3) = (((2*v+9)*v+10)*v+3)
      + 24*(144*q^3 + (36*v+54)*q^2 + (3*v^2+9*v+5)*q) by ring,
    Nat.add_mul_div_left _ _ (by decide)]

private theorem triE_eq (u : Nat) : denFast u + denFast (u-1) + denFast (u-2) = triE u := by
  simp only [denE_eq]
  match u with
  | 0 => rfl
  | 1 => rfl
  | k+2 =>
    obtain ⟨q,r,hr,rfl⟩ : ∃ q r, r < 12 ∧ k = 12*q+r :=
      ⟨k/12,k%12,Nat.mod_lt _ (by decide),by omega⟩
    have e : denE (r+2) + denE (r+1) + denE r = triE (r+2) := by
      interval_cases r <;> decide
    rw [show 12*q+r+2-1 = 12*q+(r+1) by omega, show 12*q+r+2-2 = 12*q+r by omega,
      Nat.add_assoc (12*q) r 2, denE_period, denE_period, denE_period, triE_period]
    linear_combination e

-- Inside the verified range, the upper clipping point and three positive
-- correction terms in cumFast can be removed.
private def shortE (d v : Nat) : Nat :=
  Nat.sub (denE v) (triE (Nat.sub v (Nat.add d 1)))

private theorem shortE_eq (d v : Nat) (h₂ : v ≤ 2*d+3) (h₃ : v ≤ 3*d+1) :
    cumFast d v = shortE d v := by
  by_cases hd : v ≤ d+1
  · simp only [cumFast, hd, ite_true, shortE, denE_eq v]
    change denE v = denE v - triE (v-(d+1))
    rw [Nat.sub_eq_zero_of_le hd]
    rfl
  · have ht := triE_eq (v-(d+1))
    rw [show v-(d+1)-1 = v-(d+2) by omega, show v-(d+1)-2 = v-(d+3) by omega] at ht
    simp only [cumFast, hd, ite_false, min_eq_left h₃, Nat.sub_eq_zero_of_le h₂,
      Nat.sub_eq_zero_of_le (show v ≤ 2*d+4 by omega),
      Nat.sub_eq_zero_of_le (show v ≤ 2*d+5 by omega), show denFast 0 = 0 by rfl,
      Nat.add_zero, shortE, denE_eq v]
    change denE v - _ = denE v - triE (v-(d+1))
    rw [ht]

private theorem cutDiagE (d v r : Nat) (hr : r ≤ d) (hv : v ≤ d-r+1) :
    cutFast d v r = denE v := by
  simp only [cutFast, Nat.not_lt.mpr hr, ite_false, cumFast, hv, ite_true, denE_eq v]

private theorem cutShortE (d v r : Nat) (hr : r ≤ d) (h₂ : v ≤ 2*(d-r)+3)
    (h₃ : v ≤ 3*(d-r)+1) : cutFast d v r = shortE (d-r) v := by
  simp only [cutFast, Nat.not_lt.mpr hr, ite_false, shortE_eq _ _ h₂ h₃]

private def gradeBaseE (s j r : Nat) : Nat :=
  let o := Nat.sub 4650 (Nat.add s j)
  Nat.sub (Nat.add 125576826 (denE (Nat.sub o (Nat.mul 3 r))))
    (Nat.add (denE o) (shortE (Nat.sub 1650 r) (Nat.sub 1650 j)))

private def gradeSaveE (s j a b c baseR : Nat) : Nat :=
  let bc := Nat.add b c
  let dc := Nat.mul 3 c
  let d := Nat.sub 1650 (Nat.add (Nat.add a b) dc)
  let u := Nat.sub 1651 (Nat.mul 3 bc)
  let l := Nat.sub 1650 (Nat.add (Nat.add j (Nat.mul 3 b)) (Nat.mul 2 c))
  let o := Nat.sub 4650 (Nat.add (Nat.add (Nat.add s j) (Nat.mul 2 b)) dc)
  let r := Nat.add (Nat.div (Nat.sub 4649 (Nat.add (Nat.add s a) (Nat.mul 4 c))) 4) 1
  let k := Nat.sub (Nat.add (shortE d u) (denE (Nat.sub o (Nat.mul 3 r))))
    (Nat.add (shortE d o) (shortE (Nat.sub d r) l))
  Nat.sub (Nat.sub k (Nat.sub k 30000000)) (gradeBaseE s j baseR)

private theorem gradeSaveE_eq (s j a b c : Nat) (hs : 2680 ≤ s) (hs' : s ≤ 2847)
    (hj : 390 ≤ j) (hj' : j ≤ 573) (hdia : 3137 ≤ s+j) (hdiag : 3594 ≤ s+2*j)
    (ha : a ≤ 192) (hb : b ≤ 96) (hc : c ≤ 384) :
    certifiedSaving s j ⟨a,b,c⟩ = gradeSaveE s j a b c ((4649-s)/4+1) := by
  let d := 1650-(a+b+3*c)
  let l := 1650-(j+3*b+2*c)
  let u := 1651-3*(b+c)
  let o := 4650-(s+j+2*b+3*c)
  let r := (4649-(s+a+4*c))/4+1
  let baseR := (4649-s)/4+1
  let baseO := 4650-(s+j)
  have hd : d + (a+b+3*c) = 1650 := by dsimp [d]; omega
  have hl : l + (j+3*b+2*c) = 1650 := by dsimp [l]; omega
  have hu : u + 3*(b+c) = 1651 := by dsimp [u]; omega
  have ho : o = 0 ∨ o + (s+j+2*b+3*c) = 4650 := by dsimp [o]; omega
  have hr : 4*r + (s+a+4*c) ≤ 4653 ∧ 4650 ≤ 4*r + (s+a+4*c) := by dsimp [r]; omega
  have hbr : 4*baseR + s ≤ 4653 ∧ 4650 ≤ 4*baseR+s := by dsimp [baseR]; omega
  have hbo : baseO+(s+j) = 4650 := by dsimp [baseO]; omega
  have gr : r ≤ d := by omega
  have eK : kFast d l u o r =
      (shortE d u + denE (o-3*r)) - (shortE d o + shortE (d-r) l) := by
    rw [kFast, shortE_eq d u (by omega) (by omega),
      shortE_eq d o (by omega) (by omega),
      cutDiagE _ _ _ gr (by omega), cutShortE _ _ _ gr (by omega) (by omega)]
  have eB : originalK s j = gradeBaseE s j baseR := by
    change (125576826 + cutFast 1650 (baseO-3*baseR) baseR) -
        (denFast baseO + cutFast 1650 (1650-j) baseR) = _
    rw [cutDiagE _ _ _ (by omega) (by omega), denE_eq,
      cutShortE _ _ _ (by omega) (by omega) (by omega)]
    rfl
  have hg : (decide (1650 < a+b+3*c) || decide (550 < b+c) || decide (j+1 < c) ||
               decide (4649 < s+a+4*c)) = false := by simp; omega
  simp only [certifiedSaving, hg, Bool.false_eq_true, ite_false]
  change min 30000000 (kFast d l u o (min d ((4649-(s+a+4*c))/4)+1)) - originalK s j = _
  rw [min_eq_right (show (4649-(s+a+4*c))/4 ≤ d by dsimp [r] at gr; omega), eB]
  have eMin (k : Nat) : min 30000000 k = k-(k-30000000) := by omega
  rw [eMin]
  change (kFast d l u o r - (kFast d l u o r-30000000)) - _ = _
  rw [eK]
  rfl

-- Use the specialized arithmetic only for the exponent range proved above.
private def boundedSaveE (s j a b c br : Nat) : Nat :=
  bif Nat.ble a 192 && Nat.ble b 96 && Nat.ble c 384 then gradeSaveE s j a b c br
  else certifiedSaving s j ⟨a,b,c⟩

private theorem boundedSaveE_eq (s j a b c : Nat) (hs : 2680 ≤ s) (hs' : s ≤ 2847)
    (hj : 390 ≤ j) (hj' : j ≤ 573) (hdia : 3137 ≤ s+j) (hdiag : 3594 ≤ s+2*j) :
    certifiedSaving s j ⟨a,b,c⟩ = boundedSaveE s j a b c ((4649-s)/4+1) := by
  unfold boundedSaveE
  cases e : (Nat.ble a 192 && Nat.ble b 96 && Nat.ble c 384) with
  | false => rfl
  | true =>
    simp only [Bool.and_eq_true, Nat.ble_eq] at e
    exact gradeSaveE_eq s j a b c hs hs' hj hj' hdia hdiag e.1.1 e.1.2 e.2

private def gradeLoopE (s br : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n+1, j, p =>
      Nat.add (boundedSaveE s j (Nat.mod p 512) (Nat.mod (Nat.div p 512) 512)
                 (Nat.mod (Nat.div p 262144) 1024) br)
        (gradeLoopE s br n (Nat.add j 1) (Nat.div p 268435456))

private theorem gradeLoopE_eq (s n j p : Nat) (hs : 2680 ≤ s) (hs' : s ≤ 2847)
    (hj : 390 ≤ j) (hj' : j+n ≤ 574) (hdia : 3137 ≤ s+j) (hdiag : 3594 ≤ s+2*j) :
    rowLoop s n j p = gradeLoopE s ((4649-s)/4+1) n j p := by
  induction n generalizing j p with
  | zero => rfl
  | succ n ih =>
    simp only [rowLoop, gradeLoopE, unpack, boundedSaveE_eq _ _ _ _ _ hs hs' hj (by omega) hdia hdiag,
      ih (j+1) _ (by omega) (by omega) (by omega) (by omega)]
    rfl

-- The row guard establishes the offset bounds for every recursive step.
private def rowE (s : Nat) (r : Row) : Nat :=
  if 2680 ≤ s ∧ s ≤ 2847 ∧ 390 ≤ r.first ∧ r.first+r.count ≤ 574 ∧
      3137 ≤ s+r.first ∧ 3594 ≤ s+2*r.first ∧ s+r.first+r.count ≤ 3420 then
    gradeLoopE s ((4649-s)/4+1) r.count r.first r.packed
  else rowScore s r

private theorem rowE_eq (s : Nat) (r : Row) : rowScore s r = rowE s r := by
  unfold rowE
  split
  · rename_i h
    obtain ⟨hs,hs',hj,hj',hdia,hdiag,hend⟩ := h
    have guard : 2008 ≤ s ∧ s < 3012 ∧ 322 ≤ r.first ∧ r.first+r.count ≤ 1063 ∧
        3000 ≤ s+r.first ∧ s+r.first+r.count ≤ 3420 := by omega
    rw [rowScore, ite_eq_left guard]
    exact gradeLoopE_eq _ _ _ _ hs hs' hj hj' hdia hdiag
  · rfl

private def batchE : Nat → List Row → Nat
  | _, [] => 0
  | s, r :: rs => Nat.add (rowE s r) (batchE (Nat.add s 1) rs)

private theorem batchE_eq (s : Nat) (rs : List Row) : batchScore s rs = batchE s rs := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp only [batchScore, batchE, rowE_eq, ih]; rfl

private def rowsE_chunk000 : List Row := [
  ⟨457, 117, 145869953675430191290366673337613799722677255882510579867738962524055233028946684510110375725771724624439232517549102816810103382623773654840538178193646684721264185682482079611585530424467851819004230195170479176529657371188765804999398395695956269810400832191233679500232392729283451444417616880907030757345004703096702555451008542486176290241958603683157488998909377742334934122461532220394859974398689190986215230389534138782344264722696356961634085841350844135182592174596757626474454392876363365589140476841635092712895235315687141677098957086239302216922982468519937087763687075542081709949740323789590429369477899025629426161282193775640966807250644604677603162132952008238044856585132756718316702166227122225218258476044723244508855641354686264227367430362449387873260879533846221912511016594721653756986301479513587567041545356226692278477141521293427316634512288713168685738351329654920969303761447293783548071139913544424057903354818956319315002139869736477203298259066880⟩,
  ⟨457, 116, 1086815842479633301691694355987173413372754138062481110399084839542498506950287322272225690815640944171594772464327067515993422541565819235516817445780809863701064077772652240121636467544383728167634131970717536031020295446810096975326065066205593829862951396750932409953603358211828395351845570507950415630053885391964955857106437570732056233894165655445078536165087717600625144947542358907442475873650556546551961188289040639794197538036284467515759250972567994945805294571581079276784646151958145721602257698661124185566576558516727292989798793630708136856490326178237433712556039247394450558783393909378338598579976729342802820373378635690619563171680751413350029912268685688956230858499067712552886587561224874434748803267681469209208039238025321787215343664809985157748745012665268938819392161625342821256015581172697919934209164782238148677298770769703092495340638008877224525082067650314407212008252322124721207325585124082286701791793817935827824121342654649661939712⟩,
  ⟨456, 116, 1630223757646393226479205585693921671877569733144277381694369246968255673999673595429023880556108146660684815355162567735610415520664702808510076851169600530402119151226007185705485822638527383521716519756164589493404320909137930538532782136933301786054654418332786552203317418240398810036313230507781415243155137188408478769137930591188917201664417265661849337465801265611487756708033475051359870462697470275407362480721678949410694360101511608707227394910987825194592889871306244093880110539819785703061623674809628111682841555128444576720768270255594959083677210184212315176948870861767367866437431427995713614970400115757483732210116021367713901100576275621712438698277492055178727518415974715417447448352821526046008973121530538337668407330010623176582207951432467267519255699077704781832053069915328506604335812464382419032440049706831743305295316505154622841940426079098888160170071184842662836878720555310647027599392603581687900985442183742647184102131548668794265600⟩,
  ⟨456, 116, 543407923264168915489191835141233353773792296210343315704684564933386568087885843627845731092112385664164308850741065967953874796113437077263710202870417125061036442047485811643766917326709275006718851824686229294720793221390936521669457680745269243500263713038792940333944031726606407734174152981999047879988718720812690986740111460878053776044660640893504430143788738458653933018412429148059593102068229895634195472766520591031320057054585411229496449492922131934010384154936177181899750061431958701121676826393368038061580269025331600259056746725247891497909438271319620819438041523523435992232020673516332938661591146141482342076978836665056673304725574233948080432345495245275937285433607296182099891206109516237128461995760895874332902973155066681323674661114333480376439644698586406091986722786252422873832843041866567981875514989372127313766347337957419783857851943423821575768265242542911138124083312269423435754856404397519152969456635127799412078311697817159098368⟩
]

private theorem rowsE_chunk000_length : rowsE_chunk000.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk000_score : batchScore 2680 rowsE_chunk000 = 731242585 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk004 : List Row := [
  ⟨456, 115, 4048704514204089722378903463435073991763420917326514089104104189360508721136627056718713383434865415735523300112512214168881708910933953655946319720822609453279763749885008633589880420060395181803532436380973219987080601777173940000407640137544251344587472814138726927167189710631327313750406989857369719557664861500132664505788823853180021918915829269010866195578454872968141529513680784863376621544231832636062209915728540777137015301220729217156995109273029428378701461652636518375103429856490020215787896895602906560037993307107855311475008052049928930144893052715512811661657543221876093023548572972460701745660322178357108657988625794918605460912807927568662682331842852195839886118421680668890446239228362286132068662085089161469277011809707783482744788951452957591034581116420705951027161134932160687855615262953379168660184665064356722750293988265391603512095900385391299540600069737823853110530633356789175561212012728852630793024957156616292686270350516224⟩,
  ⟨455, 115, 6073056748682235308067892959211226815439489427651221692802315239177634173348055599582361270996266579722294085443604661460570091967010686772738859582717258978541854579861328629688557294981246975950368735893052261089896197606545734653621805736146737291645619510364485363853561407201411105665259911541323927234043339052156217094509611999164090855367289951623668959001596724076623425443511016201947065619865698369787397152209934596291005753497431741172781322456325889305401610150556709464470400935426026880998916797559291501937398542075225128696628673994129520686878415745208700151344683288538093876717062596168284856502610834187120267033369195378195438758358804898104788470001819623338997702139490964137545352065337241927917791401816121203769451261769196972132068775324247393542192943010510250335094969956139063380536620380850121130618884680495238411229927706857867259732154711955199960187701127963841957687493024026775099474838313439647278198567196257612750288215629824⟩,
  ⟨455, 115, 2024352264643344713334708791752283847979427487441707869286387916249965979123186872162731059146258043346557655695428524805921584018838313076422658389126587282819191451706352712836489842834557202475843346313179104669810797686572029676588005914758827423442752286354972624599757054173877265615905166020199143242260024322376415567531824546873349379764190733092565881927944609197745535658958725982154955165667354837986393921775368400810343502789898096507708138798659001586003980991384582927081761095462517999057285020308545690079121621714160346258531067213260637365101496654136843143332563987735547524265123176361357620575639196908925885508158401232817249681453503313221879451185338308305688655455205857762259989355125474415170010619264684917306737298411372369935117629167654211648523146809317840962038133141233876059958435101388632270896970252726026193490057447298151869058430898405223993391600015537445971564816500518533380378957073783040379462371415450018731658582188032⟩,
  ⟨454, 115, 4048704514204089750472434221797834381524889133263149979595828807572424885908074969166689990446549621102510925640356595551925083944655400302639517294889184089634878848055492196886156565227611847008597165962462923726272808983753501327499915617835078212311729470839839844614844960575010777382586255949582922077279907592030337754417850291767528411320128356469893284935506263996012053336607125328679935641916962264813424043339807785217285927336920202301566832830791516062876017175040241490818728200556797708559133793356090953773006777676895727133492803655451859264174483042498603277930831327535363397481913969018017820592684795305196990272033768169140570002972909293456953739321029203472393055536753355946580848327193893023247327014099256047801911583461190776884619586322280430936588257664695887312447595201499475599958758046692492980047161893394151397672961556175392015164794358706811893906207433034412473937655098477353368829205132543870108121904011981179783782611312640⟩
]

private theorem rowsE_chunk004_length : rowsE_chunk004.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk004_score : batchScore 2684 rowsE_chunk004 = 723671953 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk008 : List Row := [
  ⟨454, 114, 22623899387874585792675215598982672450838571144831261384495777037656434526100961862438772883252302481689654608978348454313613819758008132148081854099355035196494391360339028301519859776994374672865218021938220233986992854245400882561163303320548783379335595275096423589991437159353890249146192790457949036248318221640232880452692877855190870805869727560348238451326610866477075201469199680602993542981124334985805073659428943610827913687554717847038428474033974623335282409302356306553652957198384762095501192248373025453259248016411620834189346535706958682106282159984994895543583947307386464633584372221732050508588353703649171438777552361877489979273097008818332682391643423412102071765996193226914608787587019228634682307655659737541215156662057930585283815994695951203799171562353022432723271650927757734010198769510553299684385164986524869117683084759115812687583048368343189723993375233337646950696943619409988783922425182930141414048814510425461776384⟩,
  ⟨454, 114, 7541299852145257269347864358694418698472632048434420933151200101710729223203610152612369727888174516616315652390797705424169500770539220897595822433654176414962069871386717088502788848059606935257213273060722574443877100059097489916789202854354664737529505554002583453735972352517365693702502340464609111508164631485634260852589704077193712129282967196324829722618590169574056029368349349126373714806860849421866282605750371412405939765386791162833117247232995379523348223864335631751724793163120966123887370150753705658533190520309470907113304998621490453507061041172865098995133945376041552154352245468453368367380442116498338716760469983455973955074537768658866953960952291009566539272974233552317577094845671932023550649554074209104208614702823996062173500741563032418936253683902529120059956502249785598369040662127954322180232376271098437259777885922340433462700700267370611303110174790232939620753369345547793145702694823927182378766298006383721734144⟩,
  ⟨453, 114, 15082599648103452289374300173661985924560163666543178184314924506740644474721207509902337815740235270063335456049421576435294512834478641106911828571410240372737564145182571747463234935275455742514567237765863325151558240286488472770569038061699517300127521665936583472650767524664254564967688095973583680710359067832323203256964384956429889011122239813131625908863186299460039506357165696880443782086275966242008549226838917867583862502961389059093871840462877003481191004791383540911588109016346435911259754621449870974338562400466889073929829701249215942183277479863748036192872432064079657382014403200514978150066251088386003682905731144770787836270936866712104741044388513156584813679705375690292167156600888447807350549502947067238438593479829159722008825436421082786564600827108825847105350322733048470432043233687700546202070962686827199714391218747982270090371659559829114906602547050366641756177138101620323332025618557573500206677613175482339057664⟩,
  ⟨453, 113, 84280593007684188153736203866988944511023190004091657708241392681106487060148039718905303956954179902528852226391120680507482728722273428094642464440104600810085546225647614843276685372984411468647834538470108595396065935960243214679527569745298161861868782922245782540313831706317615755746477483411614583730443354693248634079415897176787416469104963836156333308061615697471972965742067562509077931569728618142025268216719969778911380669301511474788939400541912776475948493787817250151581089628714722963548767273520520438679425569055182402195297539553355986068901213481389788318886985418346235162213177698401437544756112650595037546308569290873662534017411323000145996307192953466221485884385426864105006924342812241566848125474356791549978834174754483172894579114171297138005801333768251953192041581218663325153099009238910193174991349835579090894738922939812304127792253664231824011756227699051182978476488761984075292813736156587636718116469235712⟩
]

private theorem rowsE_chunk008_length : rowsE_chunk008.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk008_score : batchScore 2688 rowsE_chunk008 = 715960368 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk012 : List Row := [
  ⟨452, 114, 7541299852145257269347864358694418698472632048434420933151200101711008945557399517995490266881817782445639169121902868576395014163098385083249092318654585406725583971349136558890686294282901673758688022284082526921907205906445084550060971981885644907290390277679902514226014784222011909049561711214704411221355987857138531000017623886427229504868666781704377990192314536186547474583457844523798261578434926163377096139079649974369707162387809168892194982178941898361848419382070710631257502213729802020391374615888261016238165860181287516442628458362520805130787037748972704017983990909654077939759937983058296938047852750890980877558842810369924594535773023198574021702389091501898154275300197561683775770614027111123265183689271151718436629286746434472020966856511109460806734265893090828607962192617887471477498137081770856243796519298135318221222267289987958782132835262965845662671413828625282492218517436584106906915684137536429749378456353184617095168⟩,
  ⟨452, 113, 56187062144664869790428504994742519872487201044496812612991498808341639022235600314670569508407853109975785775120521355530083965709235869976468234858972401736360396776900790198229057576261505101257822022988363777283495895687125482835073092858713765480203025580490944367014322209796443903701855763822791232960664489973462448663615208416372789435842195103784543545064673569094413607533192315483507604046260902217318266275351377692560587533115639800670468052027067087981453873477823632880505827164487520725249436043313651246846422164582795908155303200584782884227259110590764949077652297798133799294623602616494382324835699786662306036148049308392447324804910082309290787169702733100045580906758993041267587878369244870882360052628831987366502300603970268572726629012158007576133816979733946610379781443691789534834584411217733311551103344988818523669897145457144863310317926370702909862894317656574774259991375668141282798826755375263214213693161103360⟩,
  ⟨452, 112, 313969675480142936683208509784150661941704116776927030489748986078278260028105826146524202908514080268367966225532241887971914905711735404952030157416567634456038347244394988900050446804883550614262257934822741005830988062288517580172057321017936673560867907466519431850810122372527995829077025227589698432148067731063512085399630312882417957268545675960087209280009896728215017884566152867882589359833137743858084582686077813615606828631042304791563347339846788703618520797372225481864564097638092771650032163567570259271120970209942595142960661470972942862552961282406168268919178537405353046483660055206760322941139654661540383766945198687172863516649674875872863396485633276070811490076096287626932935559373768346624470436319430510531233114176844264756685825381355182261176921607438409282669149997337199553673578817419802382072072408654739933513796179687545026755093760411783648846870962742627548187043104145875821590518545143653323530240⟩,
  ⟨451, 113, 28093531281645551427120807574897594076440727799777600843885477329677500581342593977059397112116929507252641242916073639518990735191783471500555999993690125266877151070471543029815893115814995235514575514711163611944056304337335048684915991772584623057830654659300120294576427354326635621016031876538128715954816832673306001892728132007676423718111393536859975994367858504272234815699150878841093110630815105992279627148260265070803605956233582370239203069257849105449844014950319795727510350598127220111772806685824116206579664037959243565538245987262466473985553550271498139662155771983024246550433411427176624805035945554825954379657652449553393491052912331242449163036327246373852533929695387519287021268307360099331064592007500491757883602572719711188137235285197666165094061397361750820409771980111824322677504621740903861597988832396187509288554653747541103429138116274816214402571675090779804928546569959127550491878037376880343245956273168384⟩
]

private theorem rowsE_chunk012_length : rowsE_chunk012.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk012_score : batchScore 2692 rowsE_chunk012 = 708053556 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk016 : List Row := [
  ⟨451, 112, 209313117506596706026898715625489204646971825676026987332820067296532647265563610396028357648242922971795838096263806778649401403571997646856342682010672735790838552865907290302116734093448273913091413122304988791009875846883986382539646011963386402087221903704489930492298928827143602617180283655288192107420925132413688215858903284619555411668971585577296294948990777016391979550626054064451649056277873528090657294436004950138349576279292998568437519297361086389666408630903582625512668860505142941089138906883443955941984878860255738498698232341079188815857333215635602290097763540644019651109053465836416937281430885483377534018341707127112833947018210659563397301953932682791780751295480005426797730417366629946001909975318520057685339656696479187587248460942354513880548634092247089746343687859501083039715311621546463577001553358460469890305226741734990877621573830971076223487934572811017743541474559236434794322664742748641053138944⟩,
  ⟨450, 112, 418626233063813107250249654363563583796899447673199973527390958055512059601183401283436433949825230281164961492466884895558362922769462335777398576742138737998149303852623297116676183681457244946001478147896651985938005379772035519354621382110043340037221912625742669903050892646472764849074368440694728411266990489934505312824335443528173450658083281542884234910696498860847868440759728158952821969126083916072757612246766422639375460916882155215112606582372197995901611949739396543222222745877734159703233300232375800707788201345193944843612516450936685840561494460757150237639464740787169808678396717089357935463221053962216514022142272441009796308519406224201857172818827736864152730399500098186711410501311986368565709412724975274198791825329083776426255559516808872218341879765492880805238711088620829177903292062190636826986326369808214196451276420562792880220293131989893405683717554563076561978379839035808867400910375006814045495296⟩,
  ⟨450, 112, 209313117116720645937630071456857882316903965242167998137537111498882909075745486402178906961041103671573879207765744095510506510998942622915447607648927781383048448377093383290076142459439800053745213728413973143991556846861504543491995837561009637242593533760601709137894213626163627560332908984666839218043708857882161324002050250096491734720916648414640225968051414566451289531299848952414442998199021202782966237249471815958768096939288189544234488041257829414311789145183512559316238849410075925385308599353047083482789467088425692671256916711500550910061040370387892879436944436802087163158583730303543096232310626100656275665515022435860957084533965496165380226869624070630232552049396443867050126059710714013941052440088977925481704600146730644513814924661439382647013212145111052074132976709966236716394268903325015193034188167872665220230073057624151249068357401216941086537701274945766349396030235527993446587205429939726956126208⟩,
  ⟨450, 111, 1169628184625010477728917673993491107606020408020540812501542416489744360888902789104508566444941136928621058773988670804485117720923291808671173085779860017198881169684736425127644407044866237171526336317753555501618099757180669210728054824378523078958218347798892086307212703458773212136445164717674186704347662685829245851023590897723164069214431870530048484662456568517735680037152194031958127995203819353327691968573196589236131263489989527744002961437494510505311655998017728297360030470027425404262411130632687209617998254837806350634994882546968165223708398433287926078323738594035398776506614599820988618877079288871308688033079332283015229581508391532565257699345092098484040621421625950480375130577794388517304348358368187618979771908374987166214402702143248692232909936316387904445962948060895646372779606933034479910141403079338639085613797595645762622641639807694722013320350839480842761011593898223897750803811378683904⟩
]

private theorem rowsE_chunk016_length : rowsE_chunk016.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk016_score : batchScore 2696 rowsE_chunk016 = 700130495 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk020 : List Row := [
  ⟨449, 112, 104656559143174415281320271887579151444343136307266964904857506751414145017131208652387181129262400200198581595250979477187859000405481568608621372979348407618286117307377171221605589898210983861246249813520873351190559969680720158892450371172625173353639768919215929277585718383373698730656597157047508694266452360876874502190855353008485710910348663765927829479630472921383196143722932421922614682894914161957701978964034916477332884895513302797246828531232024383973603743539939808256967122027484852203890571941391678680520006886629217295559162858969451018029389191206202290185862683340057726451059339367385894799707158969679235391323773462568564473483561743851743292574440015939700377781599015543345445770315192968977273516354331853219654265218109474277360094586051672468581305639716742447594574158730625806715029922051236633161843824893018872733505108419943497441106855978439721744158991483038556405846860750073287714579677099912157224960⟩,
  ⟨449, 111, 779752124535741828149669138553954222488790621020525686955217687408934939934855276354323726002280055253110376029334009049499431665982837315333811967257141252543957711670895603634700709802805632553045502783410151094166773732235672114387139072869008918265229216816282678909205696084214849622297692986826744742854345060445969268687256612243100012544232042188347227752400243902397489291801485987061422311510969708796464790588139802063882712048620691687742203627742191457419802044270606932477052693851574977432595936034050149778982501806414472577187853721903826706338824221446711120892109113939431172455041595934119434030021079995910564731606164398951924870316121284873352104503152717718899606963341469045244295839587395815386806947261656761720840993891544144462810618420555465360047313312976609858266138046840723641916939351263132507914265765131156275378875159183333436402663191073145945729176147628488106758497910631756941045131829600256⟩,
  ⟨448, 111, 1169628184625010477728917673993491107606020408020540812501542416489744360888902789104508566444941136928621058773988670804485117720923291808671173085779860017198881169684736425127644407044866237171526336317753555501618099757180669210728054824378523078958218347798892086307212703458773212136445164717674186704347662685829245851023590897723164069214431870530048484662456568517735680037152194031958127995203827476064502088756018809690645233818045137691054397037430915397074539332359146673633671981283064190490845858894966760668809885220316335913453833783308789378729572775616525014713876131120734737087865514043905853367115958345295052388693437334572039895116781477334877826442200653702820951130586747167761002280881941312809924561317140744081835273150911323577884597509202102881942296633976002533238275846892058985101591892592421246065091729677607876172801599713104963752536514245364332743194331210648358618059912753025988863234244894720⟩,
  ⟨448, 111, 389876064446473178570420603114417112109368055495632687491250329205759331548928982973695165844752612058285896374298819300334746049964402542331584968408998805107625351923043910618281357028949095497552385305515040642472675328723634480869974863715106165511584162959390501821990301352634731409454041762294306080570759468927445803521253031942814880229948134053952617045410108527459464389616696898876104686537772347784425263070626829322527427848917780237881206785552679553601002211736759696593455389816558257879325345197964539920390844984059202835386790291696755267881578069166219999965367281553528020868639361835518392929357484473806955114670955386233608963950092324395973068536212906273396347759072483988927602738901976893934811872644811892517538096754802587052817015403552213671532807767226058427125394900912296765306238079394890997644082501031172686600771676501637041719052786473259089409630525740448755773265328109243901476272032735232⟩
]

private theorem rowsE_chunk020_length : rowsE_chunk020.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk020_score : batchScore 2700 rowsE_chunk020 = 692205014 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk024 : List Row := [
  ⟨448, 110, 2904803024738065258226056168056853944393957484589985336941546527329589947815445349940373472877890077431166082729898426866156725831265886557600691792581756608724436579908786727617311141650399686966260905502029326163853607074304193684410821917910162054990340831936458792199215650872196441971874583463470431949400697128645961242494197980475053237915903487013083799751103833032717256630761928688097054164793735712229037383697183845800121760907257472040968545438167104178227725608504726210602340737991131164592655290101239295620733745535325371317244666502114348334592246941362847740817836226859383215068155919194316377507694291736242376788538382513797255047696870930449808081441589883397814305681654941318907101621327022105357834783137719493603192655303101811505430290145693802366284454892308909268273506232882150638482532427888050190423160757380587785284648036778189978982770804212525863749437566534604748738032376894495670689792⟩,
  ⟨447, 110, 4357204528991172007206520713841509474836366950507814444105794791239484583518356748357960617785460076624347101316965668345199298076242634092865121895537944082894139849067950957203624749347100980305572447722529188315377822099097706060746414933890850715157137450613807065286037461931871311998646137879948424997730648952234717111788370947176570406815587305416256349349390272850732668029777571389381380053719422154022265346088644379195814618133112491400253122476628716054080781822495552358161486628523682564382268486962813044809129577512643068278944384456049612835379959877859598265934172605463825025771605047676060821244718900794144617187601506107149726770281797534963249846446996760199156446734488415248473023671569698145438150276120601103081362002091554380908435571049478693270667950956460690887923372536062246572792796470615158159418495923013075828496582244355568975214886534601765657252434778336103401221363364885844115611648⟩,
  ⟨447, 110, 1452401520484958529401711434959941401631148331396246209232076551623592219441123690797744000850266228016431074924092606710486215454457463729149574043112331113540213015299556368214273598931285989945662344287437502484023513024774019209219634146392858010823172276517784426409987874302650731936857283488062510251723614371833694077682559551607569611175667170855144641472532536160209373193970479677138713819502232592996825901837250247077830533629444966906254054789058810050719858338275537373504474893020756053848915021926571572051656629728265280046305199804638422620663658942683507391387147088534292795443927414337100216049236671736895476623491880376484612504618410654691718720791168473801873492586540273089592712520462292919602473877147512196790670641182197003813542237942511808822389750469252540893109395460847154630987085620901203028517131255998506926277356112025381633014563252943787283280550146958313608707083247661443908132864⟩,
  ⟨446, 110, 2904803024738065258226056168056853944393958526636956171395632654234500911834406107183750089874238821739341822242437535224051893036717924585319215009836588613652367168698399704330010133149695712025163981566077329559640562499559466675037816030329242408774335411369258726351656880876830039613716251360277847384181123332646980646730214020556314123526951018650107435627103183843736834902907334204008143316826950827661719909403521196298101762227337224776654376793197832623905217990799618846917312546031586392538552637731156743955184731624516693284936534609668822522769108926787821005695754943333745955869322726659903705456049806302573967702568034059273563775016867138888565943390523829945737769711187368250070968169683209928527865623765674409259212375644087116660600666848772735221300554300254160355670215572030915419449468139324001580356045508093776671619535161695002834798045054479309334834023937809582758009585172921436168282112⟩
]

private theorem rowsE_chunk024_length : rowsE_chunk024.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk024_score : batchScore 2704 rowsE_chunk024 = 684283062 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk028 : List Row := [
  ⟨446, 109, 16231851760265126851225348986094852815703924560948515102661381629256474165314274833942607975830481262418608627826593792111298783924392092692190536081182729973586295548674463429044620354973750065338066290363945885998614726840124283015017137039376754191212231735456522925861345271378708312234811426149550335241754662730482198699031664626846021215529206643327190654181395792404818458814938166237047434565509833077808410349328487557812852387852352803083659977735976387856170151758801886411127358168341630123376670214279867920952291676743245716157262333764165044214868804865905069687207594876433962037444864527236213728567796095884647472054978253524661008078592946592592176402993454924555278009054147283382773633179353233940954820050429602155379435734112555821196877530335409976316192466645364764599709546095716869829667147563201323119743726434855735417263804643872555088661327674609207938365712458364994835253349564047360⟩,
  ⟨446, 109, 5410617293733948951220927517711897945520089311138712649166869191913277728263749520472228530236580327214416395590054268801533488387083507058747468701151623811502109591252430857248284020330518439946155556472529847875575214067539241920643160729494883625663555505779042795740529662510110827346568291395428188922129328185226758420066744984014005391034193990829086821994152396242801346330976967369462824946586764953835035388106722903031980242365142638446525969062742401215885778057287420219459293124890540597991139080560053910072788126413177864536187087748708261642544157775035097099329242825128619130857197098863230238129898859988851789593547054156611082312138179228578195257440237952873649978213881049709459549856951116255732790621430852331894392776079989790987785181385844974647697973516498813667613304106594415809392089182719222982482937776716705631281246908342922911413616386360324302752607337031166290107416392523776⟩,
  ⟨445, 109, 10821234547155657676367183282329224256120482525392646344799049933267655627562385986802543904414590512863100111311666581521608974486818604206411407523432999593505076842847352061967110488818159502280991923732843532701256088732536033547608942514906222138330363727449428343057289136382903377985743462369088178713418806644570458257058745046712044957763451602236660972893864158567732103275695297785452185350975546979506517391449160806810771165510955442448840934582600963996681184814102075649680535083783117294898737072572407949609935970988461963128930750344239446144979003706276259201377226672097363610041666595957383298898136024272070229390821968187758161002629386687960628385597475274635147422691196607214105137126034363905865353165678651811418621333912870200172425012544818233790965209950362770734311014811460599558569744753285655226628642242527644701390457953505649505179088818728585828166588557982432793472564440621056⟩,
  ⟨445, 108, 60468359888587619555090923852537596989681227808771687544611137184400876128961991740226747598479192389877489314360862805043901310645442463815822422971433520461782626075699767129473181170131688321772158385305454309573928940815769762488694173570371834095212649411172507803191509353074636059269633469830875659076607982508816213332766666799196250188181158920870591421121647659348236109114342025240432576336398167731499548038052766465293098427488143122147170739874626215279594719374428883030824250156734073536350093695758044803313022316366251263168599417217985740299249866445230480451468989515917756443857837866235730614383919404761524615109972080382777199222116895301310731124010422953534421165473344389284425712323009159459378175751531893511517862772996142887255256176566856600018748453207213708354049029657278401190295386278978400401148204182428131361781695883735876716734665803328068301032920667918123959083008⟩
]

private theorem rowsE_chunk028_length : rowsE_chunk028.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk028_score : batchScore 2708 rowsE_chunk028 = 676070898 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk032 : List Row := [
  ⟨444, 109, 5410617293733948951220927517711898987567060145592798776071780155932238485507126137471362420914660867054255667228914545053408940299243235248059730067131894889470602321683742766339259844192737055254367897688800198156514410872210667595038854665098244080000473261452809724082957476001744916814327995655284518021727922179002448732597599566944430338477456145719616439924384848979264732330080869894118146899541312409728998692862781579236452810610441266171451364436905800904062000008765339781688520730695294420154454781162745890083898885699588326049684941677307709783537392319362654538984871520630592111051503241909650699965401472319106612988456853438202878470371129912268448377541321826470254104902919580220349031460489315020086976526144166585910752973318516575151132934703568942654133582808625134128158191610018374359020576575877464073484900219501185913977324006799829289779260748248501904665795617188156501489696301408256⟩,
  ⟨444, 108, 40312240075899875448521909424398929834814677109541916641589440156771449847379274617145001532191747847434506234942624649113450104321608708077712466467695908084571656121086177374912208749059126739967187903132346466471936823613807145753765462452837665964420729610458759805801200673673048261237084274918815330954467883738945226988901213842236903275702631562075214710865009495358125959267594834414569933090751377383889152672778755243993744253553316705511838191066934875537195819706007697024002722122479294640148000454541863988691406368001234454227345853304817740885541156998211492630387185366074090765163056755602841056422846998884379944835382655551858025013088990153887512792446245459199649558695125753400228009300720656332943143180870211151236335515231164287211064751541249483275600170739755835822723549969303063104028493262955489211432878033377547928029229368919176973966514460206047788460587294176850718253056⟩,
  ⟨444, 107, 225262194456859005820344849871611583939497276428236393424165014864507601145513324961910946661528916619261686929914589245035876745899924873619610156757509412101591475589945044850830663629366786486551755611991339585087928700505829462739431014546647049841331874620812042814461549196670338763823146780537919539642366085885137692285424161885276795577103013820550546588398657611144344998065266946165687308633448891334150962473246403098410806136529421421914872950415855985296643516121025260450533802471096785914577092760738675332530942459571346634573344177320487416934286598075534865534072158590762231781771800961038688932184494440748721359826273974346564798974023392522456796299824795552801900056511041168367077034507037969332388756658501489430555279486767345564551162111522344353284890982185818838899643099792208093494580593121395293571859483579116091375033061586369196804235852550713958286950741315706880⟩,
  ⟨443, 108, 20156120113037336435992000690519433422263935750696273972461999287557397870586493838085980556237639571636085319368029631662591019972529079620876878597645341527229302650450800788143251408365943256444354239838016398649653021498332589722688320095672607519400859514521742005726877436947221425689377821200769862600197424638370629794745559724320077544561854052755603605450341197784199009835939550873463689640575768488750368431526070015242940449518699545913733724750994503103168463868275483410859129697065781866149069460242695320295332290364478488483636617262373928043134137681688168067553192365244080746163201229516902019848851034213278431211472414039216947431345907741631358689069150095459151636957227944076706120806747778598478668744265663435794103686426267297611323767009029189240071567924933709704321587314090952780069304151572908205154707596007520004845166569366210340508423165465975895219871956038959675498496⟩
]

private theorem rowsE_chunk032_length : rowsE_chunk032.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk032_score : batchScore 2712 rowsE_chunk032 = 668032569 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk036 : List Row := [
  ⟨443, 107, 150174796864017380209721287430818862597699005564830886727532148945228001026120434540873204547346575235098450223722436034666452809648920146107662479548404114368281585593802098756045468377234253288403995819018848735658143879626213210443418415298179017154336283376838775122867253665968644873692479154483950101045094582104883654866154380234159798390706971582751621560823562507153770367978084300645208710852265733030128259665401971854120826212475711605692680733035629271988197941092076234954858398359008078344582546426089814875445128657727587563257750462074012194283452793254139103090312203152614366677803538853430644958723150533221070781334269503466045123494046805851550647069013666833335324878910797325718228358815120241769597727105439615677402262764253185154019632237104165516945431815493030095021344331016825835430365511624552766213948486972830212574907708491297524695273381657452435596549559007862784⟩,
  ⟨443, 106, 839167067620378013187616395600384734818347496510503270407797364449143223054042088618216983116741522351157437890553130836237712122145491854132711029552750703294168306943043872440599782757358980580628652836665799403798597609184608357037534937053577712702593011784716105215046708928079391780345631870804839481192401734630566715927443559643370761951473001037013489416015020608797750815805220500208441709706746223422201685975605122685996627564198148808217674668291088822985801135889798107596967239410167943759860462358376766208021057016887681006551832742130485172264658283535428079795874280180294043671408689122453501217912313941778656137231426486333087619098600293306040586838924465439686975028098909041316862709702181957778596683909341378920737298588649869600449760915421355789082520174213557296629075961866361511218588701400643586842515149455272416661414157385415803999173085240167077559427072⟩,
  ⟨442, 107, 75087398711731048062413933465329682164877413774640388684205708233856206769579373217517243045631199690710945848773332903140590832638844380817440315893056207731949516424678118059995519293306351780877778594592820456611796418552925169373486747085093496568101892111025221676431496751754499484327511695693129076048978512524591531456319896490056562693907183465535073450257355047112502880155010431150834218043452553766077780241925387150106582754543947887206220772253608718878937642467201458342090170791342675126311242431956493146721194415587040647613257642385117733233486710098888235748651015319344590410414530980945225028745332193344612695079041150049090167275487944345271096159628707046485313042108213674609487230251142768123109581857324911240719537309568638762009719348389459480750944459814070052180741795231858196322343222051468667294308595867623340172580597372570437113649655252996253042121496388984832⟩,
  ⟨442, 106, 559444713831012626185149916504595237689479874554462162721068684735373340212483175281304657387999582275907133849642842524424219268227884330035535027660593781321376715247983049612129425173223191675458043414543007680134879793056565185542553800083445027479999036563029399844718211461396558138754264935067033526483118864729863205108780594631970449677132169854382413133364658454943530927221558329487145116612937611522946590582572688072122632604938269331423020573235780436036379099592937476031244829635712746056032190819386447775743908998037552574180503130825873009008120961476842453265249371481596890031519360870258515478083351020459049178458758578336062870946299930857054253883728160111978847152057979826764147042756147937566012562780906013967484687696942745331039719002796494535532825175137507260620200092731182632470649203895796048591011185768824223312213109380691924562608520652794551959838720⟩
]

private theorem rowsE_chunk036_length : rowsE_chunk036.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk036_score : batchScore 2716 rowsE_chunk036 = 659645900 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk040 : List Row := [
  ⟨441, 106, 839167068662424984022070481727289645782366457267746647024796498339821303593881927889855843392993397801071353097235916064854251579405670083343082701034558029119832833020094408948322007822693362591333792765582570882615984827704279314570736168326846681546355867331797802857601467371907607404168820258630964327413387205960757115999048467616059804811415069633268188389451703111436727593070785269570677109806383181296851210379392335782195193992278284163527145173584320855630186689690482798321370838701869730937117460516952814037860061573111742310229011706879542275489790249373808681373359334790052715400791085003252930275808206069599047088965867757376218174941957601727712473853592777720982976498981408217422073483604015847168042768306436004062269908447056990931960003120842132978284697103788543542378212067844312759748731114035317810585042826723122261423543857520379425647643119112825987252903936⟩,
  ⟨441, 106, 279722357957553297513775279616302665648948057768448598881193631870874858416737746429962486610044651553683876911893374977170919535762403651238359861334297005698994185399972731465888490582159349270922159775809748533849136841480864662313269751218638233473485146477937036544480829887783667074694408909315979001936067810230647319334550385078787743406574986531363457185602915043458610394639129460477526053310081286370053348929583194384652082424726704799691116809126181591013387345448945620292489155437852619021011534696124529016972809622820056618798553468733720927960734342517259907079954526953781425702269859448434519187006483761109833116780119252731323639260025795824647025566143761068548882198535960049473187723183599152177208545553364886748938646238443005297983026052403901587416241619651945764045734673295364843790084297755756505700417772517408485597781238718026882928391125441245676321136640⟩,
  ⟨441, 105, 2084093964960473128352872716280055186485796699503295729760336446521331892209064868395420377656815880074751130676429132090599161640658543743325527860449976404463413042008813655421619956095603077394731504524286864996458887282969672924066162854743916643708940731596311181205206407090263657788761947062116241181206400933600452561336683461934217995692536867612534810354428956117270629581889354919966850864190375847827444190467047274381379159558334459854003118623926417663828950746331130996462869754566677447352763059217290481427492301993648362370148564518996165422305792517900533632074269197612156514331322668434297739600149704710128519484329398267353816935638388923594078344806500931395741423593463334648248312102509531152434001223698161301003850018359413116868832777470718186629992887813812541010864747706202805473281146265737984979311701585452703736291248559400978060478822891988738048⟩,
  ⟨440, 105, 4168187910511308786059206259886009525902134136754683402368090640377199237224280137159916889505488789690624264944841572225648871316213672884098651091332449403382227956322952832741728753271500196879504263856392009806553331119342574902755125362293812621545298352185781702775393880242333819402762315284114857495367333818705481427089640049532961446168467315219921359486103962642470405471850605367255763691374082535063414229987642555562147561406377523263894883351846853511385928529122156075590863525974525451032542680605237788817086300189027432549133759081084507687588900951568354846763637707505913626254208527082897424771637432723158569849317645985895394602231046676092359059464664823659400769867452030382730679797448707187781931830343718867324967515723070399895912805942119091539282326702103997449647860930619925351190222485573856005492377201002119809827026398940604967496949728354000896⟩
]

private theorem rowsE_chunk040_length : rowsE_chunk040.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk040_score : batchScore 2720 rowsE_chunk040 = 651622799 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk044 : List Row := [
  ⟨440, 105, 1042046990244091556773444137510685535568621078601822165765575992372568823979237249263824454610236375002978725117112062160580782094415997207965972126743928722009260537012444076815598828358440812117632097119034200289273137213109558698458830999407056179641270044143762989040836314471099169564442422232419496190011158696995427661994379996661864353421230824694170383340072368277650118478277943109103153142811258033798160239758597480599638413311388842808576221492330974743960538214463484892272626774679867192855780368626686632681339014240443471196905642884459414345956794239401349551852039151578549096594018495923026994607546836246298409004537377727716169682097571324246186475253755222992072347071960574589145727536558717948669432960260827301640389261852065216815655160183856950215233445387874788552913023956460690298416591208049388309736953090427674826282034792244999211492261361287716864⟩,
  ⟨440, 104, 11645782499741491729318267208501972806614041612000361377390640311915423862631483888948930630876668639110228972695380428927953744321008641641333757417591973823322099810546163418074902762107880763060129291769260793140282361283888949944781700287582276727333768112100985182970902471413303629290187163229760820754302899355254108441776946542380040933685501807475259077542274243455945436748347687026366015740950798912531772174449464142626698088990135299614242776971822532194542558483807819186349968351806067333649540241804463980289766885722903225424182784740086027811909089590963626141316833019416278480441774242527778163208813705339275617244174873419664115507032141490806077511552244142208493279396674688381477880555307365027631136892634186020943452158786745302325084017774190004800762554403778152029555206623628061185662217766222542955066733576944641304115125263707196929467244544⟩,
  ⟨439, 104, 15527709985194015558741315282578606081274015749053722074167043529166283259763855986608770975252871552207202692931083951042070700667590672800390211619690248374008407972569520621520904880327857326029196280490205994277987587660055654856754251355200672172445475722198219393972816931113061571469220234125522177477736814045397940739429890569608722902802348810161132850368976273847084586279424086031188348935494243546919350724784940411274600586484019606892703245455479628679751956139439277297497998910732867342112033274483063919847137929383517019105433945900444534452044167581593850326356353587353701173406537497896736271709376292144197208278055671036472015974977359850928155431094680466539650023893499862364327964308998807830404583301143208245275907344885254432290909965206858646753115892918028699128286641324359493930563185090257183685806854299957027635428355701964425111866990592⟩,
  ⟨439, 104, 7763855014288968007640350790600122870228682469020986358261244803222494436102964396867039254587500731790409530491284580739294972107640047365864584528861571499169311128603673986995115192354740994722405306392022638724016244838168144543867635683303977825519167083367696848895011718510220103256331565696412354848188304700143985042172686066209057105587718713702506194723904242845336978469270207595376827428068018303402600955398729473115185726004199746718664748160534644677698693459550839980325135684315500031583399702468590713353794244872944878926488067944161479987278677357448533809179086721208619428390364742228064069633923405373058591306021779925034877420004021831132728061443605954542272842602067187776100245235681609380695928172729173353944679735868887843630333188980777550983408942864871925832219632064005814295526882452448844794812921856903082514994942729866179969061773312⟩
]

private theorem rowsE_chunk044_length : rowsE_chunk044.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk044_score : batchScore 2724 rowsE_chunk044 = 643218939 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk048 : List Row := [
  ⟨438, 104, 11645782499741491729318267208501972806614044397146731282190967612078704827740530312362815072081640696539590025035869607807707462933926233321132560733131217987659920293942047709873946189855646822033025191209700666617539505400129485321725267914649702743000046852515578774732421419546462946501633704671130244803357984982534449306403216475911764502250337389961308346927853699055494669830653824643144210465026189503722062241900643201870135642454332094639859528435300250850465346189436424930505224797480119511854535457022813776886697831940705212353904716837669516919450213812910586763183593966496787438058113503327649511017168804077716604819102919548521623257754392134240045823906288335396405747104027477087076156586546530443936833493675307445981926164896001147763041757152437982634074340661606117843729039451275911461596405685802354552641905776801342831150300330902124398798462976⟩,
  ⟨438, 104, 3881927528836444339835000100440189130680130804344628153078292416647249173950490119271234543688296809775811307818845373514311001329458470896955270863747654364126494633198388140968237390560633475349212280358131647852771308968579174938798800672749631077958254333034177623364372632245472390354400278192951468832490684901061994725561270817211357806411411283296507033247344425160416663479194395316509106158409520535030442267455639467719733675574756506183720657070696818896062511801969335831670612792367584870239615213227949090027693776165515351639777358971951142476940737499159019099744765519044748884873082081327229746801141578513053632479985660943206014085815210631298281377937966989600251367181468664877309797574322803178950769505792689364874900520305785767016335098981120905864613211830396742361402492981195667950171257242769395193328916001456511031203421980616386921212436480⟩,
  ⟨438, 103, 28922613763395577697606201434880952798682013411153057062108981621349209681536869693059613924879607778210225250444802947361200011974476881060045684272917145758848638711257520706181476011229519277253987967033190379804054894645933012330351736752752523129338196311140086438583628329617002489709467121464364724376103046135969004168825942807325237337774492992722613144873741096466072194081403019144225909241256558789017702537094081086021990428414006629331756885367153745675332216964904196049535613483595859866473099763163794159518464730923823942002832301369369698363084214780019072877093135139713487564308849811617307784210413824277583988962184495629292430958436820364678069314348106587838804010320669452111007020970521220148342623243038908788497483919987060394243986800716336318250066740466687088949567532321140742649401481143371968733258239828144605925826114807580852416⟩,
  ⟨437, 103, 43383920564284517352723580630503493572078810621599597045000521883661690457688757450740095496481808634622357878967633872507912900052689885054277482379716701759621204040728687159247495941280002974096779492533581952070964520425086786306371047774887467708438809411658267582701226396659251103183752688285448569071881417120003883937013483192848813064343218231316171474322232059280985983482815613458304779591611143470544543984428859202560071565924082441879657113977849271724076184506035709478308487195173731144977020334147306089439228528010620788478824073980049200958626431232333196171743838703541307043528622194253908040704384080074465004772555943742547070977776210862993133051977262990337361828899215701350725674323859503067684028309932949114709195010120176085317472233770064290796290103045919061918212698617495540096647724805236196420809353452401470804681305699416801472⟩
]

private theorem rowsE_chunk048_length : rowsE_chunk048.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk048_score : batchScore 2728 rowsE_chunk048 = 634934112 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk052 : List Row := [
  ⟨437, 103, 14461306962506638243179768698067180359036351131217109415109722379492283390254634865738698471339766340800861362738117175227769096063059440943147504513066248418445858770817111540291147424775090996851099065760272030984726077346737577122938819925410474577918077160079356372001996172928135298086552098529135518539721498699602696830787833183813647064985262408856317783079113600191698082780849845999571089152157426890691834390166240255388084398699112403221096682621297431340386385914099522531659406912724741791991556649764196857233475298143244589516577847616370034565445139358679291368609636631962951144265508232760106007733604757511732624177957794284355784586194246467604826796889523101724631241866386554754084787943795691108124748913392425538148707716515360508177645244174138664926177652002793158199845152068468407895643240409534515540838514093257769451864512092629369024⟩,
  ⟨437, 102, 107745132659629521613374799022875244016016643401684361863043180276535002606426383918919409655168453440414410721533028605858327072090895808278566025962410940154278151573653855272530522709089970600262651180124487387641223727153467890137311865053173500585614157282047899675675178852720645841318453153500441366068245163998619301389030360425690729524119041196584852234996337758481442897977008539023642394426864572367980594296961681778650830244925381188086126384728462474636642726200928958421342602072438931035162483470057475796424737351882473414086270135147088463800996413047242405289818891490234338845608233348145493064650580527147980000066940752070482812807430359176819841855852037651555100383846066321015231293245492097326110244255902854533247667698697046652286507811195052175729565383031501043335216569193044374023531542579694498058175724839040200819563561152⟩,
  ⟨436, 102, 161617698387371440800739755400030051932553064336509169061950180120972652750892896980242400598812347371085397043140466510502520528481067711619468673783347955882395329278795548610436137877472694720797045437535106263277512659208023009081450517430380240889009790652636421025446836153775760209316398193275824470910236861498234191851716332789431320870467980124918764599691122331863271731170771987534592214069723527001671004812268595851450223232437921122806907764538791197038988435125898253288327282718205060125615007778836061779011682063132098845989924188352897975642928120776908108869565059546799253588288674555528562937552892483723046415042976464559701638693766992255961145044129800919487894128510979990880019138164826317771836900846525291363923575318344549249686994522452415305671063153621791301617968660244558060369446672392430761627916569189718861290978410688⟩,
  ⟨436, 102, 53872566530505710256024333454918788220868822676007688126679745888770807963503664333526729920436547232093007363335040524171233492073301559503420647966155044512392541536110312562155032180715227682048120333298677848326225352869429098335393820991041925893047770809196511109590815243067964061957711135019283250140679684528475506284962234152837900283300502225582322136138813140353910543083105104966955136430421194496553705933203263752243319446412830449033195412154206330747541531423635704279100522957813095749587159909464717940546338579858558502933485890436252096945292303005493759413508169468213893861023791332167342576965650670731871780182090573236581363797911101161548856906867326509970417472438816331384065236017284120360702560405890620835320627703421892565417675203550646801762202063696149149835287728218597576165242618999522824900073412346696232842972627136⟩
]

private theorem rowsE_chunk052_length : rowsE_chunk052.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk052_score : batchScore 2732 rowsE_chunk052 = 626370242 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk056 : List Row := [
  ⟨436, 101, 401381897403409785082097347910982534349026692664937532928001807170126590322508999876499768704109904284320513828619516477324242712238998977536396337784664294193907777114234706007016661524373140643389416471711348781964869331214379693112368172376665933325774553053983624999909830307415708490857702773006152209904341348149823059074569441240545813655796318167271197756329922314476017612914509443850433163460017190305634171270312588761421539545196473306135121168903513870286893341931345449900243791739708874323932445269232919007978700891169509027937996990848566065889982911064526725105261311339957564826084272477360848018124628597947844714863295803789732671854584806881870048507135464725143914041968830737879933491360545897817261524294290240985219099155413190746152453489512734536845940745943199832813335120525336631708396272902000528086916841932140314816⟩,
  ⟨435, 101, 602072843862218564556433972836173342095023555818328023062439468755121583545938900493517740364402531196639326841889838411238113419512261794561194938776773778605427995107229184089649888118394108776317486493341502902674649761484189279049039677321008225453971112244618527895743921664042353344105330373084075649193348530880604120966627089971047511747223644872216339763020260394572982487996409615452253769651196660201451206764697148519403304663253061381763282764839692592889661768190320273213569851631451784075866861775846192151347765586242773093985623360633047668363841276415007562094068471036750348949794747825996518466235054048286637666248517651074620180789847246793943188087267343258423345886747511513042877287396260843105577346220518682567855962490488590159044692921039377474953050786416469044088671882212362143724577152441606933911392369280852951232⟩,
  ⟨435, 101, 200690949449336939513773968275333897102135504320292503113596684816378378152941058801708666090854872101383385887525221982609306172642701203910153096667306475255542161070042903302773707388036013411528768242630529363046713552628261767553696201740621435767615832530624755663006840976039950056822068505045337663064528533721737786283014361263551250176752091608518386994590283510457610617163525329619188391753990854584838685008934456998043567856341511145399560554717435085478705869891534806355202267551432644492624041623845771979876923836335715618824986842058754546775907812566055830586424546299923814801764200249856515031292098444974576161390446984553250109878364544065010525651487579210558680579852589512800009177911331091670695302887740110132100126158182284347215824729259523423341262595047161130052578412710406745166140689091804019686665971098791706816⟩,
  ⟨435, 100, 1495264088375157817703648350446607402150295576565141153899638696057094493433603498819620377879551269119604532744292306762825327584309460131526685570141962727881084844119636330583795073232297303798095550828548106519892202993255220559833788889009148653632191831493733170373050273391851980821639712180529633830049053328884032483969331489231923216535744029954362712114277664834326479130125437137609887345055680587985633792727128967032153317071555976341091822540648931780082703532932552199566893756917087853953768807201076668267220952877942963848110506962265131218670207437880030380633972220897163219602798484563333855299716121355042893368249903806916192190245108531515062454849060756478834009834038507281032082985318703412628098906574034329631103361217204518985875152213585561688513379223119207858004164482326515944400848299386476234172006400192⟩
]

private theorem rowsE_chunk056_length : rowsE_chunk056.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk056_score : batchScore 2736 rowsE_chunk056 = 618007945 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk060 : List Row := [
  ⟨434, 100, 2242896126992443950431696047201536302623706768396205312793948875786490290778629323035043076633108258709054018665288854109940247643952419409697996107203024348870639093950467608240426985694371736109708856542711084241782305159472231874888510995723780882774720548841787094118034473833362386858154073274522552304834656145375233399893069027259631235148079311802311616740513901499841806240147598198799797376343669623847008761578058601738550145356524944858859262427502665359991174739069200412298420930049602065931073358800675307108202550897986010153893391543299541071592107179010583389789168845509234606353787702621630098816493703896145120963335460507750226767166852348521309030028632651076035179512898229251688667911849349933586054705256412507276753830514184629352269378422787244200985320938951582861145980629376828959987673033019156664809481568448⟩,
  ⟨434, 100, 747632046972725315070800365043185555955306346741894334465470672138145643601051679883019803250133667721270372650613176848415800735296581799801894881021306945364396626356136124058085241541467157004815515053604633987594012226512764249094819272634224414229665380367214922700702745525556125684915987148640325608782844676958253273161778010093813474650077051392139090515066790549891093794640158681927109496265698635298635047358104588157968595998431592195854203817187141261977726397422575224142569571201835316602712997620862514572915652747933032372272649424319561191149508829266313295663349302744197867015958450044680187621123631770667291062552376600275209244626309143081014476997204757689976417171034084056641313622648629262401041337716561492126515779938705801589625708523970850662301114288258908574739983363228229028808864051972895136555976360128⟩,
  ⟨434, 99, 5570292802062473512081982010776577152871696563680250770969833046410998025117195695918505989851944232490140970188812329157412784882859666510825370749714372544550676058537045089861650899728747183298650764872123632698063031626079797063993664437467259456971709515561818771527455744741842592225971591077507752788894870355350704441840493605133532290287016221909754384122428902755858881937949477311135746445326000695199957255033315423341862568126681725773767959912304386439785817406717812273202819275418625975104518138469981260975389748357790827064866909688538783158407768796793230325630721096028883556253722550824587416023682993593312815415708168432667129785802934348925368976774628724983764200866790052761486283265503355584698325443959080925738940802811210134390601843430418079759967747265261936999100262360549723074952140849234627788992⟩,
  ⟨433, 99, 11140585552247552956936749169237395635210354043330667446023420186744496039519552049389729763769810077945926337518475962697415628129917426865476695380501620698992532105570712601453457463056125035617164986533469391429279721815067081987677054458125500937109874377315541742025568185867076621244047940427650226758523548862214277406930307367019575116671317597760177224803477802095498558235195056305424965406264158253010480154608616135421390772376195597146938557804129925875701519997212925438681542449230079626852007648815415799819241219299182953038354869106053042480339365946561049289159696767259171099267875011238416829437818516721313660387762204310677798557354687465735793972401315543741592342535715693673788008310843625459176242494815994867212581724897490294580674080960912160469488229214677336730529685404627673551996946474809641926848⟩
]

private theorem rowsE_chunk060_length : rowsE_chunk060.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk060_score : batchScore 2740 rowsE_chunk060 = 609536511 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk064 : List Row := [
  ⟨433, 99, 2785146421782194394527378277269560236187336568405129837476291275279753860878118691115215558220096521188691903860256739450172856926275975488621638865626436778972396546202298274049779710400508888589807086525095139560691896717160027109792071294332581654597118371618150968079967906164703533936326613584646114542597038812389260895394367661332163138840982945292908142664700510364138096421450438228752221030668506289514126811880819653194307890055774985639773400032051869580025567679868676093089016313751822466886170886390368751298574315920198325131387900164431144476043710833607482195589548611019378480221576328289052914816981400899490089420530877068181912416596254515082636514444613838501670206259182001661038973290604609781045224493031689456630589712218636293295944358147853108071204162449577352119506769543883222109720729382306369765568⟩,
  ⟨433, 98, 31126436486718333659254555745950662342068219364141880508613818911698976584881825184960361225320488331070007791493001084692389442542730235773585000305216707759983993818761501168554162636132969014040190272309976962104450190491674519975436433797369572206811582489646362636907775456147086573890304317980834172069869300756327211655389597637300662531204922918995656184774037103435060708875904148017390731800802265654291481186902824269027641964425702430378070680611995089392519022750643721242325180956977058229375808855450334064617400648944564234271082428497666404036644902568046282411830404827615563689974882415103650427220291648820777337835970948296761372273427251444412068990142124017686133274201176613662721694181870713838840466900483844676145354304518811320174682941660750422198836370647500236463360611886676610283268665770176⟩,
  ⟨432, 99, 2785146411406715604272937824727650756727352467252011062607251098106855812638057296089085357879366948725581425195778686258192521910119753732169502719416682807476517127230746207701642762463218347032304585963365420115868986436869937019123708390582890512299730374223740044662145041873652233153230288241445655550874279648142978243473696113671070015538245515334567162156907700497678847179433023156840299585440475287536583496116660933385325961711396676370026422336493102105431289492144647768987485293861866328262675271570315300540697001429513171877176436337586779988877098185252708465572659233728093134690949209794329595201825770196673653220105506453774414145811087114528134299449724275928936009499871270607501798880495751379362222130002789391489762749439352798826523469151731748017915509050226913274468505463655575902223509620516347445440⟩,
  ⟨432, 98, 20750957696463893062723955356458832631300205189162249898663612590477222018156194853908674701347113848295721420229451233879312194580874087422796697712525898762262028083509342154551623333723031038281545364483133917062371784348099440624296497077591421239781836848420069120994314518511654650082785711655085531331935288977579278274211871356674619705968643693285460493158135765793182802246193537792974853774612798256145750439957713406930889369406003824195257649306274707151961433099607139247472301550904445707757490585482172010144502847880160566827120030263478385449146417869517383162765185589965366221025863441225648204194257478672253541326114102266412033552832101364688734244311376677802440009377768081517375522271192692277494759895287481486804710798630980953364427873087622515287383806327966003919717649673819382498313602334912⟩
]

private theorem rowsE_chunk064_length : rowsE_chunk064.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk064_score : batchScore 2744 rowsE_chunk064 = 601260122 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk068 : List Row := [
  ⟨431, 98, 31126436486718333659254555745950662342068219364141880508613818911698976584881825184960361225320488331070007791493001084692389442542730235773585000305216707759983993818761501168554162636132969014040190272309976962104450190491674519975436433797369572206812997670000009799121057644437450870970806127131076317743786063589662483216229983042592100703542255011931795985579521079654659027584471967081552714254565271046354835495901849918871325452557775220468516920029892194187428285447590327544540868739994875751228841563105814274177576327607849344591961401648445157086147427365080020220713295642943740358991181748614772154223181588339208953799072295949788565944186392298119821237138624370817163609435770878471046110620562415569458182838906000432029234600948754573076053975752035798169801155502863919869482663424114384414797501300928⟩,
  ⟨431, 98, 10375478906209452610182047486197882523977238770631058873128481454328127219270392112486635237203940702960333212370796072218942480049474207550061402013117294755293638247245402715709327274921283152875312099611551035705741304136547733003810730573213979295404186367251796578392873739694732162890692474859171675835061854270351957233761160766152857844544302068183279329765779102495418374813448977762165259782565223044854393882244455410803460673251267441977265550719410091101379795007758303810446551888623827343394974938120957475410850305227672611424278214414384888360159991710550127263502772897414523493234592135527028546476765312460007344600340787910669617053362912958823622672546029233370539741001249337350909771819674901020122827353111562430258714841344990020378861333650156943458931149200713574655197493309891504968424830795968⟩,
  ⟨431, 97, 77303341534419221423445218670703701142061616519477256626439245347689965883952971576362068685885735244227022411578173227780250798439332593278244014290401770577458223053975642257986734724968620190375233842126957084719290915570302678011210481437624858853028970932013489857167107280394116332310858495648670693190926051208661081014194536452482429524144330855546942916124008528794884747905059379082837205221520690647669449688501762573549094194372256446138578514547820955153901640200046321934431302904131894474197440419519849201197568032340566878202903730933289503717642322167242802223845463402800875889694291634011895768346603091238486158048231912778060395133092964168909360924857163962115009802766460072323221377477566168207990558582628476505656036684233834548694999390041093578446953100945252044183682101626775900520640⟩,
  ⟨430, 97, 115955011869662752968276129224711439282352515967804786230636571392662698262481871609160252797524901425694144159371140728218217728191355056929638382151632815606032107492236692759477249958422144667224974254395245400870288419742050829383481040663537114051937484441235453003938480420959871859982218598221526530380470312258582821760184097457549407014951823168470771747468402920763360194111178865699486106918656035509732440795358150159309927659445526538016240625886477503472089606828739585848038294308854447039262689314012422582198600035717808842115650755079502518727443390887784802831099657546880234744664850351384220170200789066268974506632685361563848863220988687738991252644892164573648539957675882104291814322708949742663901417396113647686954782892922865430423140469541462379535149975155502730031897688073078529065152⟩
]

private theorem rowsE_chunk068_length : rowsE_chunk068.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk068_score : batchScore 2748 rowsE_chunk068 = 593509954 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk072 : List Row := [
  ⟨430, 97, 38651670911198305376552222245178679093633736560609824202888875587225009439555915379280833432128997011684941662213331498593734194117795125930585056502588001251217891588026464871738705389233083085819071596715729626737264872880029697772750862123644731639926788840003581723219995903594936256248090598490771841825047795348808465126185200315724266580446884322655405931683356273160145852093090016104727544634644489858815706709822972499012579341389138586439774934162038459182642353746485038856025442522243277905450936906721454727659282006240818290848500193126271320020463091417423414585842092773576308315764577799975740136006545133285510942766602627076153334392139400331534672205038256017497796053483973804079324394038538816999678230164364463800525272387069702168334179866699725816377553069964750941387828795761746293817536⟩,
  ⟨430, 96, 287977388256859859166462788994251568399599256066520723053960614635003422463383382625865061920004634763592941678463511238063992485763027503649356064801315147748553864971826396509180663902474923906739302608651756346794278895113215122852445002362753523931585595867950927489747556902532113130204584779881916299433240179170225386840909863835160521943298361035282735195114959258007948437472138296229231247614056740125535885049823644876406038688764953088997699795607603424824298799456471447960229036443082809599211666113106670572444651866156925084281794528157463217806382578962741811898170302629137902918965099102900057311078028765320530833439339772584182329932839358564976113141043240458454682618907131661095089625616904107969616332210643589307719427995016209893342859745169123495604903086363497978810342009995456⟩,
  ⟨429, 96, 431966080776090746762885930220849179829566160477677049230798878215091748874978975891082230120141565428602223806766742875657062782438240175939865710975932663564338873033413515943072126141160814130644902465949251486714540020835828768021202770146371394652032435338090063004308046113915908841736855250573949355417540401559726528179225431557838692609905814857994108147185645523371959068964295186417586196263592864429579926718313725741797668831024409347241722011062183872085733806815446159539391766750373466983375363469249609870545241606710205265080889245043009012557763125764088661311792833485137161241606370482463143518952234548131369324256144279000743724298573506152237780734049815177618033701095056015544946096114089038346567781489336352709679533074313923073261020970541083913077504497539681583152905953738944⟩,
  ⟨429, 96, 143988694664829616906315916199902739724642547073251844208273573172185605166688246202770000070814032151121428840657068411237501331112515650431011082614168529403276337638634095116610357807090048279729047304025708766071989951552748148765428203668169137345597255517807434426953069681620020170050201693775226695463758209358250315864431857028801922101346037078653797584779485512665115039747352521646454325176223049901145760746829328976815159893193087411438652995716031402407847069450904852181518393861515991276125979078694636983077674882406619785612342273775146343985877462633414246035658787224903333552501057986016868263417440236961726809865951450266615883318468660052810528120810287581907868745347511270993245969203969217952060882148420128873120213969499731190922691883454639052932827617437003359910736898818240⟩
]

private theorem rowsE_chunk072_length : rowsE_chunk072.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk072_score : batchScore 2752 rowsE_chunk072 = 585586498 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk076 : List Row := [
  ⟨429, 95, 1072799370649679978060377055781999979723394177423085967354546567023372851994125568429113558941655614633271121457586099170767210527788233294178641045734467169550741238382136821657675481086576647941600613944682311601014663502126749918439044650463851592928127746456603342148443244363773470538537375548854376346486030509573933097705136607975635282303315482954761314780909382135000239049827285252158205903554040852797021727958474751036133346571696343733411391894261034314416714314685978079101871423590623876551344811498549076044161220982561349892256294709419843456282275230954728632072077718506935754679168881956356158536763462892577009230116112734901461880929339463049419657808168918194391293643900852744340205495102769785380376527794043475917433505413076167442780110927614293562789517494996936616313024⟩,
  ⟨429, 94, 5994733616627867885021001565410862211177253505407003785046504444989770214547405437844446161062225526983952382952325557742312129848156450770161789679470032223484229312609364868616130969773693741792370667838124216899728599009138524824613641882241618461309033032071226275751110938028174886574742971782212596011064055784024596512209981226269745437755344948026597885587366191614236145685665817651794362244158195557420176765552162654606779481264562380404096310499739234969613759173596446078013661265359746239239101312236863258731181881669836742296467657124331602417720721481860980681859054439245979198569720723521335783932019494423396707395853607798782183949938285394585720326033641098953384159567145314814804013474737820731749888070941555054654203893175554431814948030564703674431162301062054080⟩,
  ⟨428, 95, 536399689321329058097386014507434792031567888573730679764762596268472665604922705984554191744649700557993467002467678655701313112282214958619015932384425750771256170831310962270467018546479223817854221594766261742630273250895969273621170671613345164355720268615533784300657732770773150047982988484425697920969221982660961057859941229303139671329234193157295396722894536457830992862510005383039835235560588760284464775413268168061266528883531402183457256143185691989850336464106021653035987118927855430041504175662112791394971260636031065678428697979478066051955243727951121370537478141309188623511513862919315660539931059558910969831599144180685330281604795975693810110563230103713995264007210051508347913330749078896299029332926507456259928320352145521177501185117069971008366446825347251752140992⟩,
  ⟨428, 94, 3996489087677299894617412447117268963617811211462996844466697941670453043272713097320055309793508313624381492564296410471070237607003934300724171163632014135393644732936826599796225004106011104042815850332710990591863779585318437162944995715401358089981138666464513722758042897666808022696913346190122290872822493150071186317422439069413140007032535045651583597656360101443159059664357179647806673337658728415714189150500541257423112028253830482841605811562579940298709644806049041523318318551776068362337588014607234735133174811547111197758762315037273933591828799954737656131793565872889724831331533025917089465628745404923562363036680869717417310379589936642184364550525493257518139294864536689489120335030349902791844788009930322944934023571834361476823879912521763281072240988493185216⟩
]

private theorem rowsE_chunk076_length : rowsE_chunk076.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk076_score : batchScore 2756 rowsE_chunk076 = 577439256 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk080 : List Row := [
  ⟨428, 93, 29776163913810234417143722230267823581604233716469240051812486534924015021997692204444871310872236737036916362902736968662256145374908968898251821024385885706034750088469343417437720558905627024557090273801399066481663273575411488460607175777889430653263436542241615107326053368022694963689113119312494107896326232827981952271621483391364230372148561799582809488301670836103588034309419056969615107379610533663879039115869531424869846410883871030019294345893117149383975782531563235072195966432480163137432135694539469585059771146416407633225072881050330807560281379835147569755481312645834278653627838128518670649778733633500270293635939627366272003068049420835332994635108677180853217729306438383460856095037935521129304273802374749519349148252727180468752958505470705272864374976⟩,
  ⟨427, 94, 1998244558726731904213823432130496174214662139943341528926771760104558219495056906890345022266981739864291036698974374545774868120059836072241645714772897557618965834787332259663682184044959516479048819988358584180965400207373232635230154420635076113878366544673722413470894912633239699283149553830789241932290880068951277389946149962994935537589774799498832609413403994229617479694716764001997066155649736166081069789858863667640079709049143686564564598480465058687898447431526653536738157539784919800947938013585995628515168246215762053105907076498859404764733717924865850297089327671412652356812570697212762126944837350314649162460961319555328601142055787417230334512751292728274800154617290953158247235051928390639745077514363054850384362243342551382859633727155537084001273284000743616⟩,
  ⟨427, 93, 22332122956156085906054277945067954164511969008371781841614761074360893231715987119322660469916251717420233853359633823014269620570257866136669345886232561941716079687265944251565813982689360111160009872489561374624955147041312327062736971807401130892073520967811231506823799903553728826050910970239042374267182308153464977294429469609248127485396710286240019953420362468678534383825951793823005164654650090470811544430600128791844896145172872260565026548636975645062802539568694252973888451101842874417127332367369235130731472256200640132966523704605484232094569231443113331922565635329516781968703652162601322904196553342121016829864168343956153037039873151626867067567858392209884420109562226484974514034395794351653205825437962299936010162857120977855845348433570338868043972800⟩,
  ⟨427, 93, 7444041040847789400409492435145476345222329697459456438518914954120948822945082739601909849591682856197066631211645385931590977940421114628886849603939665053394690536968877856480426694554388793219531505261396475468196750841508838758851256022235771910685714571025572693782502829814198240424959931819866178909275579589704301203121257639291295000313568361472788720603133603313490653038286436230055465247495663561122668394442681328294940722304358080626959589315905914284466818039122290554019639953595521205806974541332317923872544919791363668343134653896235363122380930732664039442655113255891051719204703428104304957323353862303579707966185946269017624488345544009707768431416229465917145279140998667122517174568583411767410753331621632885121278604733737680860518385603717265264476352⟩
]

private theorem rowsE_chunk080_length : rowsE_chunk080.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk080_score : batchScore 2760 rowsE_chunk080 = 569591105 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk084 : List Row := [
  ⟨426, 93, 14888081998501937601578474961028570077325106958674236240410998403136788228355482105051445552258964389534963433564705674409769086513329212000289517849445324426056865638996393195433674739918319719024332858763033277402143771098923957283322586933869739862337134449629333598584734474289509454806914398097409968186149335106059907275550519799216977036569365163522006274410250869618930052085022215004594909079049957199519362432863225055209012662206652414930391171729681323009412655430825025622942892790142554355772807600565026104226403421441355255976538570547119168768276522516525530412876951493607529046521661106817761049966581227910137891386044113246667460858802954373331995474482270303350508617444079046847685764045195768882209331734043502684126267047944782548459231712998255981873856704⟩,
  ⟨426, 92, 83193640992626867838406109548791684889154142067338894565919570844334074233460696135472776021515926613353369362465832359108799019014740741444202111821181784144687174688357871611088032978096972278571548629307118807593702320694477854428775572632229462183624578050055567412908835890497535261501368275558389259618653430382767608645427003837227332859804436288094784558863541837513097724031956630716213221628252944113678175532866837077937924259959861836066392635246261917734649746055614049913451866644352750432489058378726500332146878115917451439527273361267893665215089797996032616652271169130632997471615427432982466236912402548248148632992686343931017145887091433126308221896076322610929158634939323320194879001860245702120766468701550900951966416020295419624661740927070503104⟩,
  ⟨426, 92, 27731213870822598786687450241839430402563747449733516171871888762765788239082544177793477827235041573260879762799926720188618480025287998924316503224669920998114883111372076964306160962568882699730590771406301049304492450725568746179658995940273890630014954808372723040871816559900396961634533334213598173681628260570962690581050295745372452908092594225065661051033339910528073042001156183566462193073980434526830812447898193909139543120552848931737428507017953255333210372019193984555877844635206956795616342504266039169560631085631629623825476095953309586819253965649978621089889938271183804033045067977581891433034771863014337470422029269341755662164282927341947146705932639028441622795531568148531831933450610629869028709006871308620160023720137999147073907211976573120⟩,
  ⟨425, 92, 55462427535031553578279125825716765034993964518579689399880546196783681146440141981408528508499308060448145277494442011078813285053570657298724604424396161771375864199750220130033482885166830342244280190690557291264844084354680695182898945155087236820921514630297689751861560835667617503629362279299963735360913921083559338181717097939707088575937100784177535880133404810809343037463987959618110441430200368158636465761515687077414590886342622195933443594913163271815663167344000658433764803103370632358874116578912176546662891875950130245720553930650285092894448169894964376184988483950211696118353829328738251308360228274425361982474065815458858592096544972059328800295407468478546046664725286370773716072970547220206146012671475509632258947347377534534092847637319385280⟩
]

private theorem rowsE_chunk084_length : rowsE_chunk084.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk084_score : batchScore 2764 rowsE_chunk084 = 562101687 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk088 : List Row := [
  ⟨425, 91, 309920463683556274411283454174206098396022837963188721055098160954710066057578444881421334694123925699641590316923678123017892150548722187811025276639892155311799147386677669520285547231770166710166307800391167409227222251863835451007478983367692432567307993853599239530938253496895198956035476849737894174949957563355772503858393418110420893401585560591961593788592806180911439388362314375353417428779946328039797988779652375668091826364585438147805683804727165978440219166763786233271836498570927613831515707625850661225379331907510543544633479706661384107789692023676057218813700621571506716998297722592193154263008423435415703169605226589006577897894488755924631246877233815409383144194093080188583192281712302166183393451101950908937144822000908925943546904768⟩,
  ⟨425, 91, 103306821997547890196321346766648554811491621470948741480230870704225406941333950228219769251477128167677222798764432669388571717839524279883133905277749683924688245583331468802468876817422359981448194678315976937573206541911227357288557996209731346271325037783193193325589939390926428583588103704662402849494122097666015631958789143630223106659976487304761707437216555447178891725520806548513887192695253337604244968492157658365787358367943129062706440440732632803175922296166272722012317311461361609990197019814571571778320510262761350383372964935791810252024207083574804387587937823398796920969290871495642019043750272504481512275512758232582306071112593626661962278543946871324826604214957833354852945196642922871507754508407545962494918364783602926568307949760⟩,
  ⟨424, 91, 206613643225399978321518830371771743918795442381141596974591818445431742384364722116637459002674587782781545755310610638175226932321433539599056215270271209448449063710182578745535460928919361450484622071633354361907569742470175137410696381063301545011708723669793815738797170145463156329548649759162298289966403180762394230086265002109172934952620756523397157878880624216269892059673406394535981577564521094251806649412615667872996846793876337036517840193618815089486802009458089270489227704846802036735300028945598557283584291671209027798379850922900429034989832074061823225842971619553357584460438009103917685102314284180485049928987878951775033309789174475236354511629371573625891819464614029153340877205664534860116852886379014415804132234068282709370396999872⟩,
  ⟨424, 90, 1154543698088840285051613624192659614323625784172680042894851588683539919535009886085138939378721848940313970416797556260333113642508322748176183396227508756894406692588070244854475190397124895190097783383590386234278794710203078666513404712138418304549656935514215128439107856651890406367302432203639407448132966393935245941673390054441659632038668689298161905076187212557723204140341211925578079030619325160382888008674976633263810980724523768428286695851967285278434879745711664980224025788648408849189588896675197665707557928137285220751907353773648004454420607580675680567044618807194701279695803859009746816949434767213276181219544998738376941857566149078730376580365899403851844071570680728492734131681318997485235826289273634745820291302809327894720⟩
]

private theorem rowsE_chunk088_length : rowsE_chunk088.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk088_score : batchScore 2768 rowsE_chunk088 = 554093546 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk092 : List Row := [
  ⟨424, 90, 384847901752397008971576939398976395293442224825810912456819433285537359580103952416049767035367211861772940590809110230934466944482362226707763373506864585972322039418933689286759020975806384601580406465358780615841185292184917701709097383138815456463891319862376948991277611820544856686519617821945280095961286821597906387846750908494272812809441246913036182842311952135819721145703586284048324513697295102648411440677858899024133439419997994073720165713003342618813008458947715036454421959116875308261271891136095076984968421938026596845158092542624828272562651464047136049276380654617410786301572015249863481197569266630228862150742398240259712707735675106945750002025804547772953038293669532497804794583893585657182320112346436874059067330976618119360⟩,
  ⟨423, 90, 769695800637453713720734530582173704798502909020149314661045926246252912494033133247540624480716108543277457274779466103447252127263635652007099457536003955607052873196102064156922692643881940972065486370904448632041602763116716897842266185540389820287708445485007990036211239006065321007887155820411816256032784343024774188117477769264314283646506393535432845621392711200669431088091942392585758857285512050674303401316650755946030857100728100923736358220350448640382080910801724691552933337904232754199233982156200999595125426028265843936037493097887946817794369939619329867990922620588717812113975566492600667965651969093692890956493561620200169269130880340909527491038478768567533875135629912186770102287660669318178046786459471057704386673334892363968⟩,
  ⟨423, 89, 5734680571058976383153541459351052569261902590159261076561845139632108791055679496578262212632703832489734880537099429403251008134706556266749810814696421511961791962783636238070596906319704144927634989473138049047272702187526743970235056251905767478253000070033872792491585933409163934109135570493979798948330195400485770307070740665226458996310614867918503692241632280292918051115418454315953503297883782965274976508869862802219686464163036350011148239392533829326009067169939473219183051453065537173826336469825733629156968946218695853283334067662391647346434833444051478080862968802464101907611182566037205183925892548098308991488474281222027462699324699182411288662986229790547650926855098710751922247833294777062155858204410646313090892726272⟩,
  ⟨423, 89, 1433670160122465872726796034231251825590770406425894503021034881342764790341037436014988480400410094890044072978055381886151910058539031721479686466754403564438592680755173509755580648087304849099277739284607519191828916064980744823836733504962461312090813934086324298497194031869640462930061311731737029546444869755064012958878279386547876891727485036700288346366311985898328836331240287192592067738328177751476350285443812718102695827553572652523508355347035779479359889805101826477502974713847062772342689265863874595369296513125306288466798387021209685197424073176282286284412307899454350870685335825454358136799232227454466103073128901677457554626448295313864014898445974915713414198320155060692072450465494283980141595673692302347200490405888⟩
]

private theorem rowsE_chunk092_length : rowsE_chunk092.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk092_score : batchScore 2772 rowsE_chunk092 = 546359698 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk096 : List Row := [
  ⟨422, 89, 4301010432299860366778439460731660894241426654240601509686285027054168858931701432124268023861344028789508245923720856197192897975473449543247567653536926648567987879932039522702180048904782817642789612707996435065843190913928455946569134863342041378113349330614039763764609113481802489191249676484385622019607253656010954142230393503065582219976443405129566516062125532815843337855954721169996098116621737028526138934830263103233145439693096906458337122561690696869890785561556557466315046470763762782804053566330272274922196474038037452318319247285769947934675830833133957119112953831832028131986057887754507562648385554307100940751645935892046998142311755570158832384710276609422992305166935678203460372411253356613236675723612871657460049412096⟩,
  ⟨422, 89, 1433670154781628433509085101630449939282298581086867330279379845914843643425077973309209628283392860321106907062884688031239161288438535408656051692577352756482060452301705391929485105108769970536298563841075774933309941169737000747510063404056947962589085592042910961850210719206606662351960013919908299961219589084030850183447972610980859311751480771148642794842692938257354558674164757245418401605215196116724284830110592145403429802394004833369376469924864163454732442466679192213821790018234647336462527057125580430360683744954218006508577462261237709779224893756041366823507055641511737642592526489759879029437011440438302883799603858106672729845528936832631606543954974831742809063632088962087077429829448126816714593244710101470340003692544⟩,
  ⟨421, 89, 2867340293540744390195677332191100248090375782704804861665611296527722758993761515096168382452274375648945294326966513295678649625248451590265288848504758344652331762989761564725643099928815619104109651890807227768381503963018741471193902101583995843644074949546749700257307907005091198418817310106482845108894516401498597971471172693740470417452616162236101459823702976628506794234832446728377807025408576601967357339844062725514669277583800289462226798005845512937708505506118671698321631181899779588595812005187302510834505970373010286220855820553790665563948338667790499718775698613991923642956633292232114766241163383167335057170343319468212320233667740676750998185566308809809821265001268287459434603108232089718430328133939217798405342396416⟩,
  ⟨421, 88, 16022512437030152852752952034960201351851076574787590787405514944872906836158703688530070801608360261136612433213606441188965195036498479245408090952859810365939099400620299672556010754792694000435298840754660890862762217849083677707184656856291256988286160813507306592481731344844296597193945227937767513036122388940784760137440593629545231088507466545100331772041093048438918228686172749028650341128439641638229317541355485869083988617361039837757287861865068414941869905459567047200040692577982628106368524121024308850354533190031621895276069744953912096250979637323242147350982457811708341441261398288775521102881331382310568330305985900997329796630000314143661531516210141121340884375479026505040596299479067019644672273644070885163008⟩
]

private theorem rowsE_chunk096_length : rowsE_chunk096.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk096_score : batchScore 2776 rowsE_chunk096 = 538913988 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk100 : List Row := [
  ⟨420, 89, 1433670154781628433509085101630450215397122613477497741766171084124367836894669434425194771302552012688341959139654467189469884661472469099029651635714833811728444812096542726499294140538353636591509180896408483762610821281458341987077281745734549188044452097445707790612650359015157028091781761589862437954097680560067379795224767108783080297451324559909215209347007550333126409479744902526947122479322063730428008894057361081666118503545234145483766207761838703710128040204830558934273658564860350453338490617878120400271382894981966186923924389434835256751239907840522265749796474001224195594579131093673510688321766656830774587183906400433583116187871452778630561232999121537168309251629911553742466742158741129781578184212727664522444647989248⟩,
  ⟨420, 88, 10681674997812441846033142003386845089697742768615842705469946549846702091046801846360904488972897857097118121014897186507057026580040689338424307468645657022702926464075532689567212009993841626281078447405093420276122794394293533659840193619423939796111715678204217867804253134250491950601101212895407967697633735208805661175211361679534105224494470300377055479057610939629522727537842028369408863825654021834196050760838766147408767619160454664513919562216141742041645711416800350947098206424008112223657423846267346839998682493869474944296103166061985432147525351450874994958129736092208020115735203450789657170425597922918052910047455061863944559771883355970110692437787882992297788591421378050611030770458411957818144427474773543518208⟩,
  ⟨420, 87, 59688510138653788443177792178298290379548445721193738083136416279827200025987931798233037296990068452623915089444324258830455272449699544453874417151179834834324577577296657150839528407690553520227940775553118268364672238194641360609142612869556059344201086942169279439213524206938404864898686152884172668347728890984334071632730869798169345426296527007876997748761448785343882780407041578321074669832325312210422902364356275002217818371396375208903204328481013337547127522392785654876736677688861318491017428036980024398575078312012422711860400816896618165783616985959598978679778261974995638951525447889973806919331580477442138886510758557718988680028955256841744857160780817697320576311875083437705809613351959080384589826392064⟩,
  ⟨419, 88, 5340837518802391117472518614047954855959008180568843744085153386690586468645069345929223922844297942926951880277102044799121079783376684162296046586111194858952384004454251438347975613704732075781306345004778310612286525041260655556744871052238458293048070810431308313789566958519938941243769848209310521061104351016324870462574969854191775209590176829654043737519239641484090462151368680943111121481245258620399552049872151321638504642872930599331916134408385971193593346001082823478229479348140826805074681931304397747534415985896905054054849834622635435262778152249963101475833206895332942960597972928432985934854532572399536666856543251145868514643932414356743454271826778951275009526407198137358866401624696512023236031006210512683008⟩
]

private theorem rowsE_chunk100_length : rowsE_chunk100.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk100_score : batchScore 2780 rowsE_chunk100 = 530896644 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk104 : List Row := [
  ⟨419, 87, 39792340240673877001375521350210080369938784446895651015474354547470158732498270273970668958008626887876863531059056733625604624623731469827803758469338990627141569924770719733575289165850709996729533938579321908505223427026480316054845919500336526054606190174223577984862977635682371936388353334697710009050789683049000491104021587547794695241119840410828658006295837687751126281110982097512636153035511210019640011164674433030181463787436868015341235167683836074097844048748150243963324698771466978733670957665568421374925596806657766998761721702912218521821207695587540891511903110322539816054940372513635794557663965061297625590665645144121662299214234183362827091203950912863441228960110702814789030348326230135786184900640768⟩,
  ⟨418, 87, 59688510212772797140672325708501713906020759155281342832814493760702383527471362716383450699997913019818542411869564603660507048458240717344091012528189100891193102928412711254175848094583851567536329593308827767957923200489778946340430895458531758175845652845593849261433896972607703738528033003611780609696465512580040221039239959574280505523235813968764808204070001969562260515679863391159992426236758282273216218423528995861926842778323135464297025741677722827940649258428621552096350922981089390912609984764187830707161936601363249341801053655640665984151432121452998276536714223058643215503758479178548901160191457489281357756327822288846232679988673247683442475499983565081533722320738445635231961360802529782194859558338560⟩,
  ⟨418, 87, 19896170268574956862078718020526322063240154492195978272753782452913551147836121957487693917571298858477158902042450121047000161902105093723598462179180717596652004385759569950958567498101937213995617787720932876829547234523679307264708863356715625948669176994075204206580290023232534010833236466326085286393556167886542903789553591201269592661201328503324225875614660413319708331447630632547297518276248205029136580133206817584946271128528929282702510815620461925500110369080251732829314403679440248680688785947200544952386054036135599397140330767779933863687791426378221487044996043287421511841414334638270080714989740135115258621072571035836370691468792251930188067608841622600827119554501186072667339890035142203098755781132288⟩,
  ⟨417, 87, 39792340240673877001375521350210080369938798721697480895744100824324763599756186632646906169525462471595902360009002103880752436225180077955452595373208786605277461769392405178362050750091863196533542723803132180640436417402478232229106407779280148307329054375271958049887704174178798649563447821301498519560801469471744258169117680433313398344625608104780001182762435849699827854905366841963911083630003950133922565261728712854576613073560555997197895725465936621639113499486823520960693732743979173748647513611876146116175771575117196330553671172205536957077397410265958728696542859323483832032808768177278459374657869059938684995374271308395457106661290831413441067927039582137554286290032878076704262013226271621185263236055040⟩
]

private theorem rowsE_chunk104_length : rowsE_chunk104.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk104_score : batchScore 2784 rowsE_chunk104 = 523119238 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk108 : List Row := [
  ⟨417, 86, 296476036722781914690842552260952694722060358704145280597061121391528201098243219245567873092443060354624997087819749584089583554357084307817366477742811909221490254743512346257687539557358098412616959042448254961573026404125139403529183230519633255685808026753716241253010160281770526723395282110374639430328975250287232641584398548050093334597330336541975113756530956981944296657544673094591603060602242883497865964788467641231484872302095465388138646088055625932550926945512490654367564257787720510955048895894489547737392755829770386867829970834641369728537422629856255220425528029698804711583167642457075578168843817359093448724154176110070914332122463521169036656772239769500320764458520977673693439424258298236403712⟩,
  ⟨416, 87, 39792340166554868027766163787616041759431448103578944109704075511975734355443211563654442897878726554518964618852951327316861548293456794270562155482991145869231873240328407966616884349658687986928943357311122845811477288158654754645484811297911176765348007944161924961690110594456084844986610763557113328701386561671766899803603876249994521281602506107203100169509982565552658616923982061006993501606033854796273109189448262856592066313002140235211805717613038261579858620126729288077038511830011588787183787855506399417365821729955463545625058972606536109107061689896996748682207287404334162986685347196747188081440110748374241817699662733041175917346967694435311845303648826383998658914648161957758549835805946286816598484353024⟩,
  ⟨416, 86, 222357027749172554042424884130432456978150056053252692269886255212340513234251010230468090031440697526136653049279359467253012533762909572862852774057538615928841904724328089908911811441668324556294442464466260230934733870095936914472043605549873313928430211087381917350932364527433828880690789564668073603639374612572941198089574800075412996628487545936670009864675312634888261989060054866492186493579839342751605096908512322665187038907123656283296026025111132975203311391113070842788503882431743475001701322254829387662327622126864361332759180279835635017070043493862269402514455813556168054570277911782060340311683475181781251262733047094603190847672000196207110835174151342261217349766590758852469859210203938158575616⟩,
  ⟨415, 87, 19896170194455948164584184490322890873041964031019104033412168765553971151653209681681094435392487439045210983185808339821913424426031839751106306486900157811221268201692140654969405973694818687162860505696200305073157184063946972639131984618911924534496339609458800826484534701217369666707703774831775797950407317650243804353639998651709820079589000461501765093307863234481304394424696760500866705809088427786976414776124116244466572251157507663909395602146822860496202882023767967738699066951172512596151751949810388339498167869120936985364702880941982034244113915835638165310696131191157793404991802717929676882090487257467132140871039816716911944794244143207785190718986588489605508697707553974888677801053175809925524637122560⟩
]

private theorem rowsE_chunk108_length : rowsE_chunk108.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk108_score : batchScore 2788 rowsE_chunk108 = 515614985 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk112 : List Row := [
  ⟨415, 86, 148238019051678019483613585374576841614781868691983517181547749112051377704629721109864999420048484972360887682236957142809755474666687088103671325176680887185417057950669493382001185162072375238831252903179848845998439989435816507442558197372565457946084266848864250611436761215455073711664481296341566191472112357931945879972577235965208520704277766238800870970332610257263802503917836708636679710894586155439525834696218579435123374176093244067464864349676674095293844559285337129776858698560919673206253793892107782018447759717614969423534119155362523766891967500556104719874172312221694392664093409234092100201607262771484726385181906626803528528786891619972045394081943597304876301448456155836051720816194804351270912⟩,
  ⟨414, 86, 222357027749172555071032763191678711695777050112164534938098550885272026158824308955047418538443999188482445066587344776207414539343489499590823118206783513852672940408053462024180324404278969467535394339088791118430615358779733481292212802430826380165042905699448040853050252965391180002334384244277133218843115612654415874001364561768328866258495158562023305343304690962086902591827369849902007774948219327757117080908774814577415172905017142317515643703561394709056321016674484465608569035127403341516501074118566984478257095771797929165692333765182356438118517418632161278411040629237048081446473410574060709004639243299358517834437009911853792381218631634386009673365000636038478845970434918084824494493669971273482240⟩,
  ⟨414, 86, 74119009801953837888628931680034439537830516811531424646869930496640395938058233565432340291993530926177496488421665148800846390120292730990864449009845567562165530112495389086577583318083563093860012618926847536196926013345466745258770042240687648698996410055034456489318208428504679622467833867313295848678868081406627614775021170293908479005205452773263042361461331487772826538444713880381380076821555397970871688278134599702716911070530425401819619839427576588976610403598275664910956770867772033170231974180994961645832189721863331484675433471502950099824407945616196827943608789066808264754668724806529131453142547392684928328351764523792333914241222475547082011795683171203734713827565635876499281809678201006358528⟩,
  ⟨413, 86, 148238019051678020512221460603960157818864228006063591746517846537642772244283073671052861802312086849946020286750259748196619095741702131285532409211020881783744580763469337424690158333157985802160586768613131045417834750123464688658596870858013328557191480017767374312305475697733950109991946074641279080258633383544997676001239599755187747165437203728984243691990429421262335003509099477808953383006722151624807155198294059949472679093522794847472544482332117398680534959163076952620564086743368125266607781914039359236986454320156406403750328201692242159059906333778748041197150533077609616449954839710590034443750366410500980230804582872159787490059439326573262949951662958647036053336953955266386988418366052591763456⟩
]

private theorem rowsE_chunk112_length : rowsE_chunk112.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk112_score : batchScore 2792 rowsE_chunk112 = 508070975 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk116 : List Row := [
  ⟨413, 85, 828344479297427010176417895688540298043966424935709886201641496415759340458553376901110902597007338008219013035093378267422024159003522932655114337621564414448828679703948553464160870286746742981441528820806545524627994183780096478958755166947229635744774374220993877910631177508897375448534855475130223997592578755738669219603551452365667230099906127997491922803088166507647807388770580264631444883158171582827141840235160794324866615435596241031646831224597061768328302273727884840443023636814104195803541598213820615729743623922678136869636176999021586326287693158846667572418974243786355359989100223377919651531604166376025967113943202283481793293047048086184961987187911471828094911902730362128930288760291328⟩,
  ⟨412, 86, 74119009801953837888628931680034468087434229749851686519926232281673597222616361919205463447447461291955014970897135743492124333869601676118856269275972799219155237644902822756538683785183617371251762851440504485845646324903433838343174529466551947049971499506903361094206114538696372593418394986265996646625252246390116153060680790472786885446289388836537665586507950504541377879853342058048431783201962009622161548269614281031904452445587278260643107088952633436029004214857616754544786013817478209312718836414421404043434381476026448157848408648743069572516836086018933740692336411840406933639551607522043059670281442027684949831127233666549723765921825528228253798150294761856905035831081290834965204880502710668918784⟩,
  ⟨412, 85, 552229654236428516031136589512080542068422888159172091878447452888489294094922868914128518812521085762311278677519384204274605681589623392006593173055601838395441964716182905254117843738067823479818015324902524940178879562167160740009175866935643153117489251287846368307354113197775618728622001575747559004414074147102762556302792848380149994182429714261946982079499625555613753232845621366173559897991503361466150444056798526847885726734673445536037936213260222730364621816918999631999540451000021878475289194796403305030480795060297523790625565580137981956574742329015143202181410745388717696009557150360018983031866267989018629168115615936744570069867119473770957798970635189344015509637666263225021433640943616⟩,
  ⟨412, 84, 4114431527740574005708764530344532999201761484855195413715982530205142479715663395644751802632852760091899905867392905679657871186831257276546199131671992605488042259881177917081028194468648103667134300028770154178722742432051350511515515607391400428851961925705846736917523990868427476959191199727762806892812645132180577402311050514962615154976261758700468029790320263086293649840728245451615306443232384922637248573748297353305462700630326773887442009808572128530996562584259113473105349542757094791759259082344284019193537856458619609007945232151988808535903042857054444696636647347894934343279457367475579848416826456492543035525217913813941270963049743707400482968538418793559701281216367863623876608⟩
]

private theorem rowsE_chunk116_length : rowsE_chunk116.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk116_score : batchScore 2796 rowsE_chunk116 = 500320275 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk120 : List Row := [
  ⟨411, 85, 276114829175430021885855297610422615973149097659488902422511325719854518270703472965294461112277062805127543986193304563972112581604357159744767790443580168823509101889760419428954102350677512080477244267402003751367756053309511026220269657645686373865016477884823231648459138032081312244725459913522043368633541158188249484256109772595759284653283155465736369900217633436172589538400141253739836534206544451928099674851431856599878127327001848098963007041023715875164349537816485763173918007985359948963373311186217722604605168135516195013868877289635917275235567813211097243045861454151150849195584294673744251971484869129177541879861500230785277518856379558150946429051392156181302017913702533576401017580322816⟩,
  ⟨411, 84, 3085823648679327708166731993467030950280966750860110640457077069325482660464718551597108759257946618644550443995013814726961057004458157226225795988143509230745498124359424043730922392427989917988224321353060328973134403942464734693526614500872459440385404464175815919752500036818183719014612767588435450472451672848720129025288327265785073691342412399329925364102169497037768843038131448992274485328731830558974339684646466300689235953655290672058955148538956348947337226165918718032631700883915297879202014046740437545225328536412481435373622263626026378224580676387553744139916587472119135771920569336085167713591983611562717189884226480831571660152550744874363563672883347965809276773756939162838138880⟩,
  ⟨410, 85, 276114828146822146656471981406340150303507286353153827215991655352117106087722754349537890797179443533943140931333331264700878599300136385905681042949598390958516689357570956755606324715006033073192394958856009944801413102094951261666504165313505339109961751102410168305499821937312897537656770920539717857979474641640274783526594483919010117578791320295685712109434858410881424536312355513057188600228927463935323514430346293433009374168245035484031016182557567597268856277934639043207514796446951777004688180467128401631366856191041877385051901989617814351136691890763853948407607228375686559235511343156691234817827242266993929964711485456687561254910083469214467280665225074516176029563163718034739415333502976⟩,
  ⟨410, 84, 2057215773449944377687847804272681129439141310577314719375937439483517345304299255152923783887860382449983707121924071346167679733644407859583276361554286840093972549216907692553954967361895309862060068441670529075659200746440829538511413603331330595494216228006551856606992678322819333841136964663241603327483994447490300569988732090899958771856493766484758296132154591249659197002817137354837791744805932116279288892260746591745673229356457069793228129505449591504546674248292171075845750498705481614653461386612110917142456361649576045062708375937844721682506913786347016236520494143751996026510241383917963579598086487415355631571399222415133900165949826570106004513843728851859565240128124888671092736⟩
]

private theorem rowsE_chunk120_length : rowsE_chunk120.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk120_score : batchScore 2800 rowsE_chunk120 = 492373720 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk124 : List Row := [
  ⟨409, 84, 3085823648679327722441533876525081465877168447777885925382958960467738948036169179742863301878611806129473168890939108857368093138882492747387001777204774823638318975917627413723759973783995826187647009990702811146162515245853827358654057001895902026692222863725205540138035060166817802153387727387190268843425114660051809399153110008279526675154372313034104354030570294181538538998190967558256644548322980144121992927495581871923253911579326181550538060733520927978733761586859417899733935086277827592617612322532088527664756591298469539886021419830550398224504547944904178930267447243112581248017279987061704549138600022214180654167888762969805454842876477083263757937051993169645669771984490874793918464⟩,
  ⟨409, 84, 1028607890556835184456676175468937122462344491307265412867038158148963399558226594141423786032873018500242941037104776169653441582622809421938343113626179275462778768719598736039144472571620945925696852514914063861330512280399068009966862566893603513060123783793210157218564588084484529329875088170212529856143326010261814336382871651912165014140933105464599195848477959551806709523173302895493110297145964116998730400358342104465643448198270275355626304481687607923495221070456571084561452813020474242315309562599473294149222025535052486685823843205851424945650220447432024678524876718385363791692374748467185681780706305828338517517903590325331967289527508501366832370662013189575086082821499453234511872⟩,
  ⟨408, 84, 2057215773449944391962649634152950875715995915444572635734613676695186793634316147914199182676787775596955191819568405767146555770143208797883399702330643490696263818732659661071589254649578296654698350274834263036536308646610348257313014594192124975651999832864135873004495205944603530776622277104642712247584614328890700383271343845690788740293080695651728543559844977841932306432105818110511083331323272910145544512331929690382509527220744159368223403618801508733919818824459441141368859409637015499800367545170994068878502940276137080735276112961317265564015976863093330842316450088178262073258409265577930291922870355452218756574844624682898869600693648119205184777794313947297576455770969317130141696⟩,
  ⟨408, 83, 11495588915464247245174193796775911874996168106850961773713358466061364721846246540763887591898963741579839562477380030916824018558157843468866545251134822356937444765333713762049759938804813457576093655530416498150005120852677679525907961049541536560538041783094908034859697310888794903447697560018628759600446969552887669714652849153696005039731492526381284091502503556778595289440614223631231090099075219679046300539995285769479705010505158529846425170861352128940330273223020845179939772184636785535850338368483755177476306867630387708184101664660505274304004983660925720945929547654763291451211181361954745489127121090975220587584382375372136016774215793157325382884302357978025565331201753088⟩
]

private theorem rowsE_chunk124_length : rowsE_chunk124.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk124_score : batchScore 2804 rowsE_chunk124 = 485075901 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk128 : List Row := [
  ⟨407, 84, 1028607890556835184456676175468937518667686816657032091159116208879309401250328774846196969831139418515772651226096941805167655509855731065468006068342410428407745375754885825364634719162666787036318087185080892578579845841022699578965695352928794684584014618470180755433912484122306226534929677676909585497475873181131769623950243217902977992514207083432210751095096007185261222237603007247785260315898059161077437005006373420519126780744624984544868903064956675474121408392770056193236973246665353396444028978782521097895464216131894042813266900801275629378136476549099149926679770320675937488242276756228973910177660633526698295018300994905037948525102266820071846651630800864052689614921859585550630912⟩,
  ⟨407, 83, 7663725962675900727371311314973797186151134421805032502206903767378993937094451129240065251520556768337500956299593094015945661267997015439142819139949529024723900047454711464882156096975498542171310323387512210397546913560418537070946593682908015245643620690262481430700534055167522020229344551938323115364789292821122156001263270927546735800234737471409623713138944523549246963016389456795072501266017588931637419626527315881008092565360037867432871417026605985209101704388968003211339241996524312140394026115256679786708012900191971933700782786662053761972959292765469179700868989089205508591779981194121146021223492965248743403101364555233073973805985757397383731358724711591872661835093147648⟩,
  ⟨407, 82, 57099207691765546747574907181851003301644740873454989173396600552939628826758229475396064409110068769058565398638390663583011765058087304247500396410784344569896540636260834637822186702616366308727453564158698339183377534219868199078348953642068599067696878403557938275975922607659166799274700302918039850010945689204686782349289359098636562066792092509084001827049818465546586637382974757800184300770461974926592432143296917200808964890420981732966516330804408773930190137664781359562071789849590381745730343807546558938464791016539166539355883900888026186644372535119477869486153786511293680929725955528279325176335801270217497961941151079754892203423144918428355251298637523171003105280⟩,
  ⟨406, 83, 3831863009887554209568429031274353290986005272360083484840966385196671637895830433502487326506384152162814404704489831321069689706931243319065313746634995462396604286173706667954728584236933252479397240111481549796837065590907757513732529905036719339916415918559415731879724088882554139940967947433639381944397209305462557061105528013437624633424503758400194998934973386007008019739716700759176549031454093687277007572222224678510379330609002883050377855564499428096370949232530937850534869034751224916633589795861789903228545130878322182456551717451360374890176662869307944232885486529051991292066549147026911180608169851544949442639464616918298479570551483727413248296020522245814676114219499520⟩
]

private theorem rowsE_chunk128_length : rowsE_chunk128.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk128_score : batchScore 2808 rowsE_chunk128 = 477301420 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk132 : List Row := [
  ⟨406, 82, 42824405808707495637670693103893511660689078542211094672080322665833370005711996110679869960497108562043100226337014235079560479892604160909847923659423183418683643604371419384523590551504710891870613568602293805961784271343104451879616940258570621541836970038118897022374130279701301386281510816642758248687070447680125208597318914052762650765663177341455407605022397043598060878216101739087984293920165810117149325032081227997572242381380554491213498801752367205296404758758057497472126046016854826957413269976978590826069998838185817732156218359907717776445999531364135140439491164891979652844118120027561450887082409587997738415174120465573400099033443929826247953978474967400712273920⟩,
  ⟨405, 83, 3831862995612752379688159284997497210138829392594342726718776517171276359104464181294380821410093525425504673410597354805668598348732327751585629260637533945824126782713825762417705627425093002340558366905577718694994271846112117208416993047645701144114597826425769020686166689114587490744428057492638514220355345994832417059531287393729971768865193044332669650752763809483121537801895447610174236540909335409483285023255946058594357928377970951158907385826042259089553876385682422513838963157869349849632559072748700193794069896790080642889941502605609291283814694386901103105312461415337821277864913655678152199229334190111116913991816965444690206999832084860027372859236617479142063853113753600⟩,
  ⟨405, 82, 28549603978827225693291166967356391601639294266741713182121940032882483868217864246347854025133880914518649019199225082696928595590372600438165988647366886029990039330361170463504980989216085159757792188440177448168495735252878222448656495264200837433608778273946831066344865604727511285116173672714260538953094945740082266327716843515737603653025604358227136568715244281560782431417185313452424625336177814987785625887429702713768216297973102971141606136283260995222570232042620597852121444490424728167444937642850010804743766332043412879965864033788274585511295676128135350785464266106364267108741161257386931736357812091614132177482271060411256517486398577450608884492585020042829135872⟩,
  ⟨404, 82, 42824405808707495835773363897573416196290058796351611988580939678169220264318685523744830696003777313139155349296995069609664920299717669684590084317316237780347507905692428718330383402221142172868098989857279882874302286565867618095728391574632014195946956940271832576634723794493030919015884477903084922148953494046815495319767644479410320387772849770338905352120927227171690907957741774416690571019866125058816164350109333463103871545676703346866276283777435022764176958798423852097113821783249926390423710691220084077765373374317588668568561891443127769653088947953089789954195470133962941355006982565920120219685379193328069732573844694222828063940796561790869263671539104358772817920⟩
]

private theorem rowsE_chunk132_length : rowsE_chunk132.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk132_score : batchScore 2812 rowsE_chunk132 = 469614928 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk136 : List Row := [
  ⟨404, 82, 14274802042591394408375618178388098948146196480000681473379579389665323015937989631534203772231959092972103541343387205854356203725588981385635060531019561955551705095154634096645982498474097826547428323756062032994670359922146367943301572234466481325327389096590672322730074266867589176502688137711553535023722433889413313608916810716821257969300323365763707862248406428132530928692346176600191625087891963500282610882016893847024309247619352976060918140387493801746294130543484793542099964481844110960653668220757415617044415674959313768177380488198025713689497781314557967600184337477698606316749382678845888651093546227531407716271489116021629181607120568815037481643766335271090552832⟩,
  ⟨403, 82, 28549603978827225891393837761036296137240284762550266467805593339275546137595367168039326561691450954740870581193242572307384242370713559683944356217792365792110189972276655826278612378893414669377022696239919254174630766959557447846923614601048628475840872124659382023733071659443900295821798227047683300244813022345271009449183473703249230853554073714275175800449694060205987304781537998378661741538008447042364553059369040480480324959059552361307477482277124458141636943226075108326115435941778518000798371191816266612942729468924859591245566596855465788302864304190489897698322274390597980410023732015009156427704338148740120460332079019961502578684573487860841169042626545583782936576⟩,
  ⟨403, 81, 159533343694676744211810495665758600700114945664817047900526626264835549110585690434969791005867020017014995015810774771313049192907251987032873908260370597873946775569961319580414089452167750243784256309176966404797477901323205112284088565068022739581004027619425422249732858452116381750627839229970931658190171318453380871372223911913685313883297028307986420243634470337730508885819403494713472784677276386497719939729489737905032236122839529937891292437400273887632739440601234866563470065727701940465610767983119751412437208054446366104465984208084305628109942535968448308662025880626281198678140661975708893006971672954525815701960684963781152833398856998279102970455430053888⟩,
  ⟨402, 82, 14274802095769175177694965270438616316713412375599456894550347273039339623957240706318942183652461141954416054131425288770607448022556466307734376738350821518885360234132806464861067325759430425164838284669375232595343387093051364696950558210455832750361279015731199128858699349745147533613875583169920124118499497775512362938086367598293642843916546961661023208641556729428926616153353653576324659074116945633855051465849876231401116739844322847654742945746782788336919731120477473440744388272697236444062134728130336665371438966326540498667272071908245421561417990571210568478425512035372100379677509039264941260569434351359826985828720383701726637129389437878810925244991976550374096896⟩
]

private theorem rowsE_chunk136_length : rowsE_chunk136.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk136_score : batchScore 2816 rowsE_chunk136 = 462414700 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk140 : List Row := [
  ⟨402, 81, 106355562727254725588090113405273467813582289079391458883157877143365693814146717596707166120983946119292197880707049411574410932670477800835824979783405191047321049500745147495195039813339930086962951519980789391537851309710864339392382339558615628215402239795072060538149513915125153092117533864576795570210205524377848881561457943389323234044275643565865496527336759725733553857566901782730686817918166229324269688344784388295198357641999627803871035100670386542560915275126152999157746130133796273525228089029260712181455383452906911592084668753392119263757815693073123847147890619626210388112201994470188583952974730670976796650823875002279296742410510362787156628729095045120⟩,
  ⟨402, 80, 792410688340649354382756840429205004560293803852705835350228784147463133808373683367844132987131367805829753329561693487308622162232060100803391604006184105325459161665590571354011098467869208890814575649511481924472925273627682375199389664459999794060048676153949104621249041301384555128215141071772213273031670340914834852892881113216991661999662488508744006945788071320548455852052741118805414082437461797727220295963986879685626799975546830600707408238862802211875154343518495383349512049328354836236244345206029555100551253628511164676391509965269337050988379920506379678132489477147420592922830610165237888993175034817275946371224333715861230119613999939562827186176⟩,
  ⟨401, 81, 106355562529152054056420251262582370016992422241013399251305343372986058985773407202489217159051335641060661563916237747046942454080828629345697906087146092204704915160168079339217312890065040404615681577920283572603046850565203713344936601264053207581387556926921350109249823021111711590901687516472390362738265449277017358900094071274320981292885993426266011557866877393150839950133168230343777216315491581971771205788503155893458780167979406242088004892372701809652334903180139228164668773794590575171337680860878192380881281283944509806999295231577391300577807060348786593584988457051483801606209326256876039787804587839496434486864539979474517502039257010280544203575503405056⟩,
  ⟨401, 80, 594308016808979483992385244082910950867552603879716203617582552046668814628632268373605926727387678874477528467825405438277300896201699454240206808750378480508875199015274023512160063218233100139978007638951364546030705012075499632552357443527026896890666941219444965661774371331533144529324187370547920086427003190958889936481507557458561517033511239446014412325069763183449366706701687169251068586498310512879811382772627103888833247879552092766991235670114336755671753538914043871447163720332253594375289229905882843761348257827443880577047918646595358174813978133868094745876019408186976971592365003093402156769182561705166003346671382199137724120621119669588742684672⟩
]

private theorem rowsE_chunk140_length : rowsE_chunk140.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk140_score : batchScore 2820 rowsE_chunk140 = 454435309 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk144 : List Row := [
  ⟨400, 81, 53177781561730036170689829358414163625585055380972403598055183132232664454448259079488448306316372681326819661939664659899048123395642805576479348144571815087871187851200707460737991009674569782515278691456778767320297989608115722462292144310509663701368693169901875937472189056129570044654706834968061172704458809272473685950526175724241904541997782378003774212657611017592082091860237900289183932810239900132385213034206782412751067165114887544726234601384677837034537752706826254170001985977174377407236792466993630251363278722123315920770728880787077773340153143837451973164816388230207760680009730963238096236281966003286401548797737501473518170142654653521825395626511220736⟩,
  ⟨400, 80, 396205346015299576707557424151090347286809010645426870374535000441963470799415006994679461576251435141452620070079763718541973628072403491221509288276140385118005579700687350803639723590225600690197335326114385486434706999695515763715001684253572805072076827588271177442625084758098868640765954583373318332803058197055146167726553089114537963654406871303049476047680492309152489647294334927587025826545843208675012301483859085802352428226424173259493838861358079033682339270861536044538406809847107284275029497279350776213672780798037118714907532932826556983743972837338375528588806024016890370887474246696774443642958672765929560832618501265160766001971407886959190786048⟩,
  ⟨399, 80, 594308016808979486741612073518923001162612543807612474591250628256167591255291642120073785691724690451159107712372197564857837346383202833712792332634021071493938670370188341523775545902716475548200716650650679265532941129263136372614046005353926920241055968913768486899862577127156772949498310243897529769175053523660283821463276365750852380723251256913996937134990016120789712691713700710507059674642056645236473985564201227718713820480275489913858274540101825423523648100786683697199361887350077972395466226662395671336727589838616352099098196224846940585684079914661421203838896121256012361644183965707443970543447865206427322647363980764406016784584296259213496205312⟩,
  ⟨399, 80, 198102673745639756957776208812051207232926657321024874782758535881090553403144011358425067283330783018009649182863275526347634689605434916915025235813399580756845380535845148060415373564349674095355270979169043507802401588254678555953643351547165605354878655460040690341501155906344165402885481436984004244916562112834204511380502258984015456831990620674297169227627987194783919485100076301377703432389705584214967910401428745960653045298498864623748034050074987061727234333344370035431629764568385651786795445506696329986709650696109571008148791380001375696475585336266538101869163264269533861784752065037562028055332775929333519666094631415696650812573222380688847716352⟩
]

private theorem rowsE_chunk144_length : rowsE_chunk144.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk144_score : batchScore 2824 rowsE_chunk144 = 447436622 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk148 : List Row := [
  ⟨398, 80, 396205346015299579456784253587102397581868950573323141348203076651462247426074380741147320540588446718134199314626555845122510078253904690263535219563092289988443156874453288011415482157777281268357223256275623798914053599363988826059653363034528960836748867806070792844647346716498269380823134345491584520082160479496885687826140737685067657581310444254481494998090285523149873790462206845802034697828124729782460938271364640786429130716374937739563402455025607946642952011834810476379130601596092553647127584515774426015943180239500264372340508791226335281941175926921697653200065412685350776783195174620564897824087492193313716571541615252843826837071854959373655785472⟩,
  ⟨398, 79, 2213969892065858281579449213793115508834310436793836850974154774940653373568565075574896899704401755020839339822729342319363794510652589741640766356287469298462775957616879982467599965441896227025610675029739654657843342530123136402677377951450574920312500319941902806572554826076588270926664926967593865025613300971993571357341463106308795621198411596526038433701614276586259661918304824424240913883715553869403545470795201697093152543686069088106469516871288132421018423645939064913278174545668320137878702446480674912026992665257232424957166007288516301652644882907114395552609760053113198207059594601114322712546501666217619059442981821552598365062342178291712⟩,
  ⟨398, 79, 737989971353224346655854308435695315158432444472081763481145336957643197271421028486479070217528804203420791660486509300784985268791145244441584805767520402163832104067379329505966830410434578434167622309587343782642511130929926622133665226743410597222054234004830844927753527828901811093268817709821364161026233202715650135340564824358677569457386579090235270272514466229536473698537215189660605950353170439885838100388976732738828173454456439112514859235492777488074786846711813366191550385354298035895154762086519153034849182970977210593011682716184524658765120354689476203004091669643142620371932349039993289412057213524398565236747291273014008629441729708032⟩,
  ⟨397, 79, 2213969889316631421418433055590506460024239882378713055020505756313610131400096769648443568673426689249533818472592139380221147194034089048773008337027432928791120877764084148006153900685245988608476613151765288403259894402587608647675922528635218941569328627628451726277343428716585199872587453940989475133909539516030284398441427489471786963387871536779335712359787873250708458935991829416272421816158353774482318119986912923821455475712870716325144865637650713259935763451913171897593390374980124061482404326110671829019639777664066193117015824867375813905575310439011854670847050870732364744229556573807008245967135681470982349931551399100020606936250874642432⟩
]

private theorem rowsE_chunk148_length : rowsE_chunk148.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk148_score : batchScore 2828 rowsE_chunk148 = 439961080 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk152 : List Row := [
  ⟨397, 78, 10996907399677392946771944364942806770093839841117274003468219252829095906149967169451544734235122278679336666053122929419718149275451108833138660218219464401485231414679993303962197846152653658230425561310151503923699149656691252164164476317875085740253824589965375002976205119671122533236567058772023523882656448006883526774838096751396897082963692951119241714753026866284786731199907464876726479980321129003255543774318886983803071858080205082310283321497137780069257589157324761449668988671624718830830718527928767738926180823271570229620876068122183678878003196677182923938515331394670278889170105506632069851581672129014156587886244690078360888459264⟩,
  ⟨396, 79, 1475979931709541293634315670099445981110665986856173241043593736149234588442053671906439444334251564523028657101391865754656395420701814782699604661301301364295205398279008831097333593630141022392352429502140596365252899772238883124256433190297931870222225463873872846682567962344532911662263558277264286283933033621102936690341238549447178353957877940359545020005642654024284758406532138923467773594555170975730010488455734978888511148174200204493317164115154084748675886806598566005948746385655353781006967334462807133940991599579831404241943151608351655263775858648140323247235821356249840341521714917696424182105935326398155910641105410666611184159526416859136⟩,
  ⟨396, 78, 8247680549758044748232145203499829382890081494567220335312899119009183313767802932515629611594574911048170891452904728914056161437107256763534462071702239464781307031890194313480606873349949497545308697527106967853645617151223398968321414480523157011934238413199931585183915482206019313913434645869631586937575522649303019919716736978008308231242985108283889255692194114475241663490826096472976884830554101526468024211385695513465170624526685682470575532617168248128285883489797981366869728751798162461837886917853522294704484472057839194880915848333818313944253366388166994633639593929683035725111874766973089918590378427473873215665989478368438390931456⟩,
  ⟨395, 79, 737989968603997517219842258140635517362231445272747701133031583056429653349076902746984013651215267108834181322509240685535473721919503479381363489997317126178180093824636124064258346276529280658782132557503045276429152005161724182110414028573303884957416505891748268738099647074076740118180158189816603092955239239828873112748756853080255695755951425828099778268503154645729573184983440434400252914511056371827793730368919813609884498141457047520954158116990337350633761057177892083580596443024000836516497402650992155090366425932273814560486179163556901507837609076416043981463158793809917542163042487022868008943267905441834476107045599086320697336786065604608⟩
]

private theorem rowsE_chunk152_length : rowsE_chunk152.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk152_score : batchScore 2832 rowsE_chunk152 = 432578269 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk156 : List Row := [
  ⟨395, 78, 5498453720322032659783898689108450030553056777822872621511217048499185025918134250027359829224144576161534260708521002563066577526666787876557174468737547306913015466780490391241960237147444505221131445438045487889528021896067889359924708163200035813152008629043133251699434497503359573531691344358901655278813924271377271704908398304555128852250179713857929497745548670541641061518637835001453878594632601039909525356085551424894186529640318325832152742045927639421135446971989318848876865983692432156743526691638326902619305586234376280014924756454593359518180357373405587981702781609892468470857717777062455082718418050472914635951074229217555329892352⟩,
  ⟨394, 78, 8247680559999712784201328239793887124382681752908905556692544752196734845616944906878452042702108343881425823902007208328400984763047102277048152183773842237855056028905080518215226530218703002037198853437843005545265595961060775695746048490789139385034131733343752651744726311897452159818714685574975153830206197738851481446901251113167934879793613581060304941783956068948404936827323575006761397612474431782718288699578335716722330115309859872937566808698194918593831258849099134048343952040882882110368452279227108418158113706719654923577064808284928346025353636344110437011060326316053706967704282277314378734960320335410622645081121622472597897789440⟩,
  ⟨394, 78, 2749226880644352535366469280554709267461420761317319286916919011329090006807692119307784486758824666478214502376330839050074295568161584714177631531115974344448574073216653651536318543736208434701139093745165228304708371234189235665516407581145821459564995871493514617368075721951809593857888387153691634835751038422662245406429112508570527494755362481447207104029982059876965283173795872695403328533866581939766942241643702100611046771465847754192470741765722870973481179158373721433075180033175058942420036401136145510503285822294612869423345689020592553520279447781662441123147708335506998018119282451099901927723359386826722313455515977115921517953024⟩,
  ⟨394, 77, 20483336300857486798554281477289088184211614645357700517442987941459134383493674250289736798765158837201254549872924901263626682580327919303573623820044140844031930791912673151986460178605389811209742503055385517875654598329654305423329322037434637717334422901626765670428370376269794604529610571493261112895628339719920542315810013552139620619388191936456027839824323646499540091083193981834274401522293876539859059019875707982432700628648844453874507684832253368959006089830843665409273897899380522776927286656812467149011836633358247198590140537800488834731102483649774663105839798965380564951922923632926404303960728068536210493881373438296064⟩
]

private theorem rowsE_chunk156_length : rowsE_chunk156.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk156_score : batchScore 2836 rowsE_chunk156 = 425251864 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk160 : List Row := [
  ⟨393, 77, 40966672410949039872000967445406129800092678722497569013391214089017124145840378128627022004387834077372266384526613661755656720872663977605794230636507992997276736364546637903648124505123855598690609615965095612943065088302152588560996162249304479601196974937814514556501690216858674542578716117333112963360873914841602813551950637413839847031142949112677976001387771101887923699177846923043793952963805176532743131237436711521917325200466222509490491060270318935791028947993004468795896439118303536763568318042999484830641157062475456921514010384579714566014518184257831893850813994682984803954940735218815906393006178433737456997651881901735936⟩,
  ⟨393, 77, 20483336262704300081959102594669572029929337469137765757252064097130276338982421051263791153471931624353167953239183554824645193185833196310747748931651458440765843075122838483955521177037423085737708176836359557656802046376427615924445864958364058730993217642537570512113395739819019484099341206193700702615320650542004763590080524514465169321782572108472097305342979994109890746328544149107819984646852817221063344705924728801607240231100244974389423599050328701153925588760122606210408018665126868139135755264895191746312458437517600535853521409924429394462544539351563810670336904274340559632464079187280080019790550399094091160773493170159616⟩,
  ⟨392, 77, 30725004336826669834848339218781688442553299866737318777061640455628007287394703241621659567604490820088509591989147246707628351411891432904280388790254989804091155682142553022386414828650023464641232888112134221538316501861853904967843817217619886031753719147755747514285608263477912559963806470636591481998130482012864110077456577366780953443958458969720620139846113519165859279362330676199548377489806220927657592126288657915796496165178757412591496304321797022811093099175307958381938846467512607906634025913196750786176417194014167722850561904944524588010868181959375859440892955551551780675305904763402716198917552789159606592963922729418752⟩,
  ⟨392, 77, 10241668188581930471201562301295444575885854672125215030401451419500980696123916584935664898115204966955657258122342488448001575656036480901652833824762538571787542713723246290708262618533242341385503983181535293922939698761844997819316217016600778571012889875364198928570770825775031053010842011337559342631524962017325339120522387961844916439928326786243208719479278847394355670564657409345333360013402883439873234630572808622543153782693701421747548377880635525185460208816507508586745535637683137357966744935105295261708950635695915754643645303966894627149873022122755874977373686181968391068329419216350124299737079818104557950463833312116736⟩
]

private theorem rowsE_chunk160_length : rowsE_chunk160.length = 4 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk160_score : batchScore 2840 rowsE_chunk160 = 417952193 := by
  rw [batchE_eq]
  decide +kernel

private def rowsE_chunk164 : List Row := [
  ⟨391, 77, 20483336300857486798554281477289088184211614645357700517442885966968480594151222147149442990214171171790116506474170843374232119048635616438676321762968044112167123043551875523413229043639609393976766433844495043953808486613321860187423381993250099301199077133982600110289246260351605804773432752554524864889634952009985439639467472796073221857908229594081481063972282466241158901896067922174694483923393978570699075238403595793992218515661447830086289150902339043685434059361080116514157010691575352217199569532543415068728521960223837644773975875237817593435292543879165808343431649721113225760184396041311396399995751867941239936957843654098944⟩,
  ⟨391, 76, 114459560718312325147701494773481810723651543772307136957629768894649997046610646984610871228830786326726127397589743882590846653773485685336912288686848516934416539628889793573793306002646170297802007768957356094639954671658561169359014275197528559481383821475400603749335713645554824692223777975470284960736177388137584883738308764516057261614511648767129026357130266154613019002864547264075993628601819736429896889864502720130945198706867437064797595545916665753723836030012467060356739842155853357894981830912602699118967828992597485598426754724734312839097984145978662150623287759452440140627864700302366901499119112829285116472770560⟩,
  ⟨391, 76, 38153187142990270522242644061503725409082554355865958279484534672028750620295619533731982494972676384229501936427586429028757913079327577294043908564975952429355156585486708454982950394796894285862098843846599185591148481480220656787013822778998269834017429722222856374138343301386977962376042932368701279516097968630837308266399698237016510263605573603479173141505902408223014473110595116365741746863023455083700153415353085649604465993853707359223380091374327761659564718125647884665649205953742999960785964961050246004733409754478025329705987336322467864479317007516957574309581894217687789421030641114882142181613939388726679227645952⟩,
  ⟨390, 76, 76306374001717145735600149174366474837853069027355687757741614958119147954485096969789776201416398723428154550019371886788408020810514387874807712106000341341422359624102710073952552472219836750171047178358646253504441451983312677531845415937413377240749413613412722764147132600002199316720690762587092472984643032936020194664216013512954129589324340430520211367173647418223933643602071681364270038448854933757590122615890260878645690227409316333514327811238996553674231944146561902660404408705619306264070435055995509831065283928636566420880965724929829901931373414419833935243429470729374503273134509729585873430340566537845433274777600⟩
]

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk164_score : batchScore 2844 rowsE_chunk164 = 410853595 := by
  rw [batchE_eq]
  decide +kernel

/-- Original two-round witness for grades 2680 through 2847. -/
def rowsE : List Row :=
  rowsE_chunk000 ++ rowsE_chunk004 ++ rowsE_chunk008 ++ rowsE_chunk012 ++
  rowsE_chunk016 ++ rowsE_chunk020 ++ rowsE_chunk024 ++ rowsE_chunk028 ++
  rowsE_chunk032 ++ rowsE_chunk036 ++ rowsE_chunk040 ++ rowsE_chunk044 ++
  rowsE_chunk048 ++ rowsE_chunk052 ++ rowsE_chunk056 ++ rowsE_chunk060 ++
  rowsE_chunk064 ++ rowsE_chunk068 ++ rowsE_chunk072 ++ rowsE_chunk076 ++
  rowsE_chunk080 ++ rowsE_chunk084 ++ rowsE_chunk088 ++ rowsE_chunk092 ++
  rowsE_chunk096 ++ rowsE_chunk100 ++ rowsE_chunk104 ++ rowsE_chunk108 ++
  rowsE_chunk112 ++ rowsE_chunk116 ++ rowsE_chunk120 ++ rowsE_chunk124 ++
  rowsE_chunk128 ++ rowsE_chunk132 ++ rowsE_chunk136 ++ rowsE_chunk140 ++
  rowsE_chunk144 ++ rowsE_chunk148 ++ rowsE_chunk152 ++ rowsE_chunk156 ++
  rowsE_chunk160 ++ rowsE_chunk164

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
theorem checkedE : batchScore 2680 rowsE = 23865114520 := by
  simp only [rowsE, batchScore_append, List.length_append, Nat.reduceAdd,
    rowsE_chunk000_length, rowsE_chunk000_score,
    rowsE_chunk004_length, rowsE_chunk004_score,
    rowsE_chunk008_length, rowsE_chunk008_score,
    rowsE_chunk012_length, rowsE_chunk012_score,
    rowsE_chunk016_length, rowsE_chunk016_score,
    rowsE_chunk020_length, rowsE_chunk020_score,
    rowsE_chunk024_length, rowsE_chunk024_score,
    rowsE_chunk028_length, rowsE_chunk028_score,
    rowsE_chunk032_length, rowsE_chunk032_score,
    rowsE_chunk036_length, rowsE_chunk036_score,
    rowsE_chunk040_length, rowsE_chunk040_score,
    rowsE_chunk044_length, rowsE_chunk044_score,
    rowsE_chunk048_length, rowsE_chunk048_score,
    rowsE_chunk052_length, rowsE_chunk052_score,
    rowsE_chunk056_length, rowsE_chunk056_score,
    rowsE_chunk060_length, rowsE_chunk060_score,
    rowsE_chunk064_length, rowsE_chunk064_score,
    rowsE_chunk068_length, rowsE_chunk068_score,
    rowsE_chunk072_length, rowsE_chunk072_score,
    rowsE_chunk076_length, rowsE_chunk076_score,
    rowsE_chunk080_length, rowsE_chunk080_score,
    rowsE_chunk084_length, rowsE_chunk084_score,
    rowsE_chunk088_length, rowsE_chunk088_score,
    rowsE_chunk092_length, rowsE_chunk092_score,
    rowsE_chunk096_length, rowsE_chunk096_score,
    rowsE_chunk100_length, rowsE_chunk100_score,
    rowsE_chunk104_length, rowsE_chunk104_score,
    rowsE_chunk108_length, rowsE_chunk108_score,
    rowsE_chunk112_length, rowsE_chunk112_score,
    rowsE_chunk116_length, rowsE_chunk116_score,
    rowsE_chunk120_length, rowsE_chunk120_score,
    rowsE_chunk124_length, rowsE_chunk124_score,
    rowsE_chunk128_length, rowsE_chunk128_score,
    rowsE_chunk132_length, rowsE_chunk132_score,
    rowsE_chunk136_length, rowsE_chunk136_score,
    rowsE_chunk140_length, rowsE_chunk140_score,
    rowsE_chunk144_length, rowsE_chunk144_score,
    rowsE_chunk148_length, rowsE_chunk148_score,
    rowsE_chunk152_length, rowsE_chunk152_score,
    rowsE_chunk156_length, rowsE_chunk156_score,
    rowsE_chunk160_length, rowsE_chunk160_score,
    rowsE_chunk164_score]

end K1_13_2_3_5
end PackSource_K1_13_2_3_5DataE

section PackSource_K1_13_2_3_4Bounds
set_option autoImplicit true
namespace K1_13_2_3_4

open K1_13_2 K1_13_2_3
open scoped BigOperators

private theorem initial_eq (i : BlockIndex) :
    initialFlag i = windowFlag i.1.val i.2.val := by
  simp only [initialFlag, windowFlag, offset]
  congr 1 <;> ring

private theorem residual_cubic (F : Flag) (k : ℕ) :
    residualFlag F (Powers.expand ⟨0, 0, k⟩) = cubicFlag F k := by
  simp [residualFlag_expand, cubicFlag]

private theorem rank_window (i : BlockIndex) (hi : w1.Contains i) (p : Fin 11 → ℕ) :
    blockBound i p =
      (oldCount (initialFlag i) -
        max 0 (max (kernelLower (initialFlag i))
          (kernelLower (residualFlag (initialFlag i) p)))).toNat := by
  have hj := hi.2.2.2.1
  have hd := hi.2.2.2.2.2
  change i.2.val ≤ 1581 at hj
  change i.1.val + i.2.val ≤ 3070 at hd
  have ho : ¬ (initialFlag i).order ≤ 0 := by
    simp only [initialFlag, offset]
    omega
  have hu : min (initialFlag i).upper (2999 - offset i) = (initialFlag i).upper := by
    apply min_eq_left
    simp only [initialFlag, offset]
    omega
  have ha : { initialFlag i with upper := min (initialFlag i).upper (2999 - offset i) } =
      initialFlag i := by
    rw [hu]
  unfold blockBound
  dsimp only
  rw [ite_eq_right ho, ha, min_eq_right]
  exact sub_le_self _ (le_max_left _ _)

private theorem savings_eq (i : BlockIndex) (hi : w1.Contains i) (k : ℕ) :
    savings i ⟨0, 0, k⟩ = cubicSavings i.1.val i.2.val k := by
  by_cases hk : k = 0
  · subst k
    have hz : (Powers.expand ⟨0, 0, 0⟩) = fun _ => 0 := by
      ext i
      fin_cases i <;> rfl
    simp [savings, baseline, cubicSavings, hz]
  unfold savings baseline cubicSavings
  rw [ite_eq_right hk, rank_window i hi, rank_window i hi, residual_cubic]
  have hz : residualFlag (initialFlag i) (fun _ => 0) = initialFlag i := by
    cases initialFlag i
    simp [residualFlag]
  rw [hz, max_self, ← max_assoc, initial_eq]

private theorem rowSum_eq (s q code n : ℕ) :
    rowSum s q code n = ∑ j : Fin n, entry s (q + j.val) (rowPower code j.val) := by
  induction n generalizing q code with
  | zero => simp [rowSum]
  | succ n ih =>
    rw [rowSum, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, Nat.add_zero, rowPower, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show q + (j.val + 1) = q + 1 + j.val by omega]

private theorem rowsSum_eq (s : ℕ) (rows : List ℕ) :
    rowsSum s rows =
      ∑ r : Fin rows.length, ∑ q : Fin 71,
        entry (s + r.val) q.val (rowPower (rows[r.val]) q.val) := by
  induction rows generalizing s with
  | nil => simp [rowsSum]
  | cons code rows ih =>
    rw [rowsSum, rowSum_eq, ih]
    let f (r : Fin (rows.length + 1)) : ℕ :=
      ∑ q : Fin 71, entry (s + r.val) q.val (rowPower (code :: rows)[r.val] q.val)
    change _ = ∑ r, f r
    rw [Fin.sum_univ_succ f]
    simp only [f, Fin.val_zero, Nat.add_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ, Nat.zero_add, Nat.add_right_comm]
    simp only [Nat.add_assoc]

theorem rowsSum_append (s : ℕ) (a b : List ℕ) :
    rowsSum s (a ++ b) = rowsSum s a + rowsSum (s + a.length) b := by
  induction a generalizing s with
  | nil => simp [rowsSum]
  | cons code rows ih =>
    simp [rowsSum, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private def sample (n : ℕ) (hn : n ≤ 589) (a : Fin n × Fin 71) : BlockIndex :=
  (⟨1419 + a.1.val, by have h := a.1.isLt; omega⟩,
    ⟨3000 + a.2.val - (1419 + a.1.val), by have h := a.2.isLt; omega⟩)

private def sampleEmbedding (n : ℕ) (hn : n ≤ 589) : Fin n × Fin 71 ↪ BlockIndex where
  toFun := sample n hn
  inj' := by
    intro x y h
    have hs := congrArg (fun i : BlockIndex => i.1.val) h
    have hj := congrArg (fun i : BlockIndex => i.2.val) h
    change 1419 + x.1.val = 1419 + y.1.val at hs
    change 3000 + x.2.val - (1419 + x.1.val) =
      3000 + y.2.val - (1419 + y.1.val) at hj
    have hx := x.1.isLt
    have hy := y.1.isLt
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

private theorem entry_eq (n : ℕ) (hn : n ≤ 589) (r : Fin n) (q : Fin 71) (k : ℕ) :
    (if w1.Contains (sample n hn (r,q)) then savings (sample n hn (r,q)) ⟨0, 0, k⟩ else 0) =
      entry (1419 + r.val) q.val k := by
  have hr := r.isLt
  have hq := q.isLt
  have hw : w1.Contains (sample n hn (r,q)) ↔
      993 ≤ 3000 + q.val - (1419 + r.val) ∧ 3000 + q.val - (1419 + r.val) ≤ 1581 := by
    simp only [w1, Window.Contains, sample]
    omega
  unfold entry
  by_cases h : w1.Contains (sample n hn (r,q))
  · rw [ite_eq_left h, ite_eq_left (hw.mp h), savings_eq _ h]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun hj => h (hw.mpr hj))]

private theorem sum_le_univ {α β : Type} [Fintype α] [Fintype β]
    (f : α ↪ β) (v : β → ℕ) : (∑ a : α, v (f a)) ≤ ∑ b : β, v b := by
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem rows_bound (rows : List ℕ) (hn : rows.length ≤ 589) :
    ∃ p : BlockIndex → Powers, rowsSum 1419 rows ≤ savingsSum w1 p := by
  let f := sampleEmbedding rows.length hn
  let small : Fin rows.length × Fin 71 → Powers :=
    fun a => ⟨0, 0, rowPower (rows[a.1.val]) a.2.val⟩
  let p := Function.extend f small (fun _ => ⟨0, 0, 0⟩)
  refine ⟨p, le_trans ?_ (sum_le_univ f
    (fun i => if w1.Contains i then savings i (p i) else 0))⟩
  rw [rowsSum_eq, ← Finset.univ_product_univ, Finset.sum_product]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro q _
  change entry (1419 + r.val) q.val (rowPower rows[r.val] q.val) =
    (if w1.Contains (f (r,q)) then savings (f (r,q)) (p (f (r,q))) else 0)
  rw [show p (f (r,q)) = small (r,q) from f.injective.extend_apply _ _ _]
  exact (entry_eq _ hn r q _).symm

end K1_13_2_3_4
end PackSource_K1_13_2_3_4Bounds

section PackSource_K1_13_7_1Derivatives
set_option autoImplicit true
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_1 K1_13_6

theorem factorial_cast_ne_zero {n : ℕ} (h : n < K1.p) : (n.factorial : Geom) ≠ 0 := by
  let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  intro hz
  have hp := CharP.char_is_prime_of_two_le Geom K1.p (by decide)
  exact (not_le_of_gt h) (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz))

private theorem topView_X (i : Fin 4) :
    topView (MvPolynomial.X i) =
      if h : i = 3 then Polynomial.X else Polynomial.C (MvPolynomial.X (i.castPred h)) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
    simp [topView, hlast, optionEquivLeft_X_none, show Fin.last 3 = (3 : Fin 4) by rfl]
  · have h : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
    simp [topView, optionEquivLeft_X_some, h]

private theorem topView_separant (f : Row 4) :
    topView (separant f) = derivative (topView f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp [separant, topView, optionEquivLeft_C]
  | add f g hf hg =>
    simp only [separant, map_add] at hf hg ⊢
    rw [hf, hg]
  | mul_X f i ih =>
    simp only [separant, pderiv_mul, map_add, map_mul] at ih ⊢
    rw [derivative_mul, ih, topView_X]
    by_cases h : i = 3
    · subst i
      simp
    · simp only [dite_eq_right h, pderiv_X_of_ne h, map_zero, derivative_C, mul_zero, add_zero]

private def topAt (S : Geom[X]) (f : Row 4) : Geom[X][X] :=
  (topView f).map (MvPolynomial.eval (jet S))

private theorem eval_topAt (S : Geom[X]) (f : Row 4) :
    (topAt S f).eval (jet S (3 : Fin 4)) = atJet f S := by
  let e := (Polynomial.evalRingHom (jet S (3 : Fin 4))).comp
    ((Polynomial.mapRingHom (MvPolynomial.eval (jet S))).comp topView.toRingHom)
  change e f = (MvPolynomial.eval (jet S)) f
  have he : e = MvPolynomial.eval (jet S) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, topView, optionEquivLeft_C]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [e, topView_X, show Fin.last 3 = (3 : Fin 4) by rfl]
      · simp [e, topView_X, show j.castSucc ≠ (3 : Fin 4) from Fin.castSucc_ne_last j, jet]
  rw [he]

private theorem topAt_coeff (S : Geom[X]) (f : Row 4) :
    (topAt S f).coeff (shape f).t = topLead f S := by
  rw [topAt, Polynomial.coeff_map, ← eval_anchorLead, atJet, anchorLead,
    Polynomial.leadingCoeff, topView_degree]

/-- Ordinary partials of order at most ten may be used in place of Hasse
    partials. The leading coefficient makes the last derivative a unit at the mark. -/
theorem regular_derivative (f : Row 4) (S : Geom[X])
    (hf : SmallFactor f) (hon : OnFactor f S) (hs : atJet (separant f) S = 0) :
    ∃ j, 0 < j ∧ j < (shape f).t ∧
      atJet ((separant^[j]) f) S = 0 ∧ atJet (separant ((separant^[j]) f)) S ≠ 0 := by
  classical
  let t := (shape f).t
  let P := topAt S f
  have hdeg : P.natDegree ≤ t := Polynomial.natDegree_map_le.trans_eq (topView_degree f)
  have hnz : (derivative^[t] P).coeff 0 ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    change (t.factorial : Geom[X]) * P.coeff t ≠ 0
    rw [← map_natCast (Polynomial.C : Geom →+* Geom[X])]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      (factorial_cast_ne_zero (hf.2.2.1.2.2.trans_lt (by decide : 10 < K1.p))))
      (by simpa only [P, t, topAt_coeff] using hon.2)
  have hc : derivative^[t] P = Polynomial.C ((derivative^[t] P).coeff 0) :=
    eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans
      (by omega : P.natDegree - t ≤ 0))
  have he (k : ℕ) : atJet ((separant^[k]) f) S =
      (derivative^[k] P).eval (jet S (3 : Fin 4)) := by
    rw [← eval_topAt]
    congr 1
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      change (topView (separant ((separant^[k]) f))).map (MvPolynomial.eval (jet S)) = _
      rw [topView_separant, ← derivative_map]
      exact congrArg derivative ih
  have hex : ∃ k, atJet ((separant^[k]) f) S ≠ 0 := by
    refine ⟨t, ?_⟩
    rw [he, hc, Polynomial.eval_C]
    exact hnz
  let k := Nat.find hex
  have hk : atJet ((separant^[k]) f) S ≠ 0 := Nat.find_spec hex
  have hkt : k ≤ t := Nat.find_min' hex (by
    rw [he, hc, Polynomial.eval_C]
    exact hnz)
  have hk0 : k ≠ 0 := by
    intro h
    apply hk
    simpa only [h, Function.iterate_zero_apply] using hon.1
  have hk1 : k ≠ 1 := by
    intro h
    apply hk
    simpa only [h, Function.iterate_one] using hs
  have hprev : k - 1 + 1 = k := by omega
  refine ⟨k - 1, by omega, by omega, ?_, ?_⟩
  · exact not_ne_iff.mp (Nat.find_min hex (by omega : k - 1 < k))
  · have he' : (separant^[k]) f = separant ((separant^[k - 1]) f) := by
      conv_lhs => rw [← hprev]
      rw [Function.iterate_succ_apply']
    simpa only [he'] using hk

theorem derivative_degree (f : Row 4) (j : ℕ) :
    (shape ((separant^[j]) f)).t ≤ (shape f).t - j := by
  rw [← topView_degree, ← topView_degree]
  have h : topView ((separant^[j]) f) = derivative^[j] (topView f) := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [Function.iterate_succ_apply', topView_separant, ih]
  rw [h]
  exact natDegree_iterate_derivative _ _

theorem derivative_in_box (f : Row 4) (j : ℕ) :
    InBox (shape ((separant^[j]) f)) (shape f) := by
  have h (w : Fin 4 → ℕ) :
      ((separant^[j]) f).weightedTotalDegree w ≤ f.weightedTotalDegree w := by
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', separant]
      exact (weightedTotalDegree_pderiv_le _ _ _).trans ih
  exact ⟨by simpa only [shape, weightedTotalDegree_one] using h 1,
    by simpa only [shape, indexDegree_eq] using h Fin.val,
    (derivative_degree f j).trans (Nat.sub_le _ _)⟩

end
end K1_13_7_1
end PackSource_K1_13_7_1Derivatives

section PackSource_K1_13_6_1_1Proof
set_option autoImplicit true
namespace K1_13_6_1_1
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_1

private theorem exists_nonzero_at_mark {f : Row 4} {S : Geom[X]}
    (hf : SmallFactor f) (hon : OnFactor f S) :
    ∃ k ≤ (shape f).t, atJet ((separant^[k]) f) S ≠ 0 := by
  by_cases hz : atJet (separant f) S = 0
  · obtain ⟨j, _, hj, _, hr⟩ := K1_13_7_1.regular_derivative f S hf hon hz
    exact ⟨j + 1, Nat.succ_le_of_lt hj, by simpa only [Function.iterate_succ_apply'] using hr⟩
  · exact ⟨1, hf.2.1, by simpa only [Function.iterate_one] using hz⟩

theorem proof : K1_13_6_1.c1 := by
  classical
  intro f surface S hf hon hfmem hmark
  obtain ⟨k, hkt, hk⟩ := exists_nonzero_at_mark hf hon
  have hkSurface : toGeneric ((separant^[k]) f) ∉ surface :=
    fun h => hk (mem_markIdeal.mp (hmark h))
  have hex : ∃ i, toGeneric ((separant^[i]) f) ∉ surface := ⟨k, hkSurface⟩
  let n := Nat.find hex
  have hn : toGeneric ((separant^[n]) f) ∉ surface := Nat.find_spec hex
  have hnt : n ≤ (shape f).t := (Nat.find_min' hex hkSurface).trans hkt
  have hn0 : n ≠ 0 := by
    intro h
    exact hn (by simpa only [h, Function.iterate_zero_apply] using hfmem)
  have hstep : (n - 1).succ = n := by omega
  have hsep : separant ((separant^[n - 1]) f) = (separant^[n]) f := by
    rw [← Function.iterate_succ_apply' separant (n - 1) f, hstep]
  refine ⟨n - 1, ⟨by omega, ?_, ?_⟩, ?_⟩
  · intro i hi
    by_contra h
    exact Nat.find_min hex (show i < n by omega) h
  · rwa [hsep]
  · rw [hsep]
    obtain ⟨hb, hj, ht⟩ := K1_13_7_1.derivative_in_box f n
    exact ⟨hb.trans (le_max_left _ _), hj, ht⟩

end
end K1_13_6_1_1
end PackSource_K1_13_6_1_1Proof

section PackSource_K1_13_7Defs
set_option autoImplicit true
namespace K1_13_7
noncomputable section
open Polynomial K1_13

/-- The two opens are tested at the generic abscissa. The leading-unit
condition is part of `OnFactor`, independently of this separant test. -/
def RegularAt (f : Row 4) (S : Geom[X]) : Prop :=
  atJet (MvPolynomial.pderiv (3 : Fin 4) f) S ≠ 0

def LowerCaps (P : Row 3) (b j : ℕ) : Prop :=
  P.totalDegree ≤ b ∧ indexDegree P ≤ j

abbrev GenericX := FractionRing Geom[X]
abbrev GeometricX := AlgebraicClosure GenericX
abbrev Lower := MvPolynomial (Fin 3) GeometricX
abbrev LowerPoint := Fin 3 → GeometricX

abbrev genericCoeff : Geom[X] →+* GeometricX :=
  (algebraMap GenericX GeometricX).comp (algebraMap Geom[X] GenericX)

def genericRow (P : Row 3) : Lower := MvPolynomial.map genericCoeff P

def lowerPoint (S : Geom[X]) : LowerPoint :=
  fun i => genericCoeff (jet S i)

/-- Coprimality of the two residual cuts is geometric and ignores pure
abscissa content. -/
def ProperLowerPair (P Q : Row 3) : Prop :=
  P ≠ 0 ∧ Q ≠ 0 ∧ IsRelPrime (genericRow P) (genericRow Q)

def pointIdeal (y : LowerPoint) : Ideal Lower :=
  RingHom.ker (MvPolynomial.eval y)

def pairIdeal (P Q : Row 3) : Ideal Lower :=
  Ideal.span {genericRow P, genericRow Q}

def tripleIdeal (P Q R : Row 3) : Ideal Lower :=
  Ideal.span {genericRow P, genericRow Q, genericRow R}

def localColength (q : PrimeSpectrum Lower) (J : Ideal Lower) : ℕ∞ :=
  let A := Localization.AtPrime q.asIdeal
  Module.length A (A ⧸ J.map (algebraMap Lower A))

/-- The point lies on a geometric complete-intersection curve carrying
at least the threshold local length. Equality qualifies. -/
def HighCurve (P Q : Row 3) (y : LowerPoint) : Prop :=
  ∃ q : PrimeSpectrum Lower,
    q.asIdeal ∈ (pairIdeal P Q).minimalPrimes ∧ q.asIdeal.height = 2 ∧
      q.asIdeal ≤ pointIdeal y ∧
      293711590 ≤ localColength q (pairIdeal P Q) ∧
      localColength q (pairIdeal P Q) < ⊤

/-- Being a minimal prime at the evaluation point excludes isolated
counting on positive-dimensional excess components. -/
def IsolatedFat (P Q R : Row 3) (y : LowerPoint) : Prop :=
  ∃ q : PrimeSpectrum Lower,
    q.asIdeal = pointIdeal y ∧ q.asIdeal ∈ (tripleIdeal P Q R).minimalPrimes ∧
      (↑(41481 * (41481 - 33184 + 1) * 1037 : ℕ) : ℕ∞) ≤
        localColength q (tripleIdeal P Q R) ∧
      localColength q (tripleIdeal P Q R) < ⊤

def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber

def hypersurfacePrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  let big : Shape := ⟨35007, 12106, 0⟩
  let cut : Shape :=
    ⟨max (max h.b big.b) (max h.j (big.j + 1)), max h.j (big.j + 1), max 1 h.t⟩
  ceilDiv (81908 * mixed32 p big cut h) (32 * 46578) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b ^ 2 + 5 * 133658 * p.b * h.b + 1

def singularPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b ^ 2 + 1 else 0

def highCurvePrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  let q : Shape := ⟨952630000, 322000000, 0⟩
  ceilDiv (81908 * mixed32 p q q h + 46578 * mixed32 p q q p) (32 * 46578 * 293711590)

def isolatedPrice : ℕ :=
  let q : Shape := ⟨952630000, 322000000, 0⟩
  ceilDiv (3 * q.j ^ 2 * (2 * q.b - q.j)) (4 * 41481 * (41481 - 33184 + 1) * 1037)

end
end K1_13_7
end PackSource_K1_13_7Defs

section PackSource_K1_13_7_6Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6
noncomputable section

open K1_13_7 MvPolynomial

/-- Total degree and the jet index weight (the three weights are 0, 1, 2). -/
def cap (b j : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {e | e.degree ≤ b ∧ e 1 + 2 * e 2 ≤ j}

instance capFinite (b j : ℕ) : Finite (cap b j) :=
  ((Finsupp.finite_of_degree_le b).subset (fun _ h => h.1 :
    cap b j ⊆ {e | e.degree ≤ b})).to_subtype

abbrev totalCap : ℕ := 952630000
abbrev halfIndexCap : ℕ := 161000000

/-- The affine chart of the common monomial compactification. -/
abbrev chartExponents := cap totalCap (2 * halfIndexCap)
abbrev chartMap := monomialMap GeometricX chartExponents

/-- Affine degree of a prime in the coordinates of an affine presentation. -/
def chartDegree {σ : Type} [Finite σ]
    (φ : MvPolynomial σ GeometricX →ₐ[GeometricX] Lower) (p : PrimeSpectrum Lower) : ℚ :=
  affineDegree (p.asIdeal.comap φ)

def zeroPrime : PrimeSpectrum Lower := ⟨⊥, inferInstance⟩

/-- One local Cartier section on an integral parent. -/
def cutIdeal (p : PrimeSpectrum Lower) (f : Lower) : Ideal Lower :=
  p.asIdeal ⊔ Ideal.span {f}

/-- Sum of the degrees of the retained children, weighted by their lengths at the cut. -/
def cutCost (D : PrimeSpectrum Lower → ℚ) (p : PrimeSpectrum Lower) (f : Lower)
    (qs : Finset (PrimeSpectrum Lower)) : ℚ :=
  ∑ q ∈ qs, (localColength q (cutIdeal p f)).toNat * D q

end
end K1_13_7_6
end PackSource_K1_13_7_6Defs

section PackSource_K1_13_7_6Lattice
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6
noncomputable section

open MvPolynomial

private theorem degree_fin_three (e : Fin 3 →₀ ℕ) : e.degree = e 0 + e 1 + e 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc]

private theorem degree_fin_two (e : Fin 2 →₀ ℕ) : e.degree = e 0 + e 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- Fixing the exponent of index two leaves a two-variable capped triangle. -/
private def capFibers (b m : ℕ) (hb : 2 * m ≤ b) :
    cap b (2 * m) ≃ Σ z : Fin (m + 1),
      cappedDegreeExponents (Fin 2) 1 (b - z) (2 * (m - z)) where
  toFun e := by
    have htotal := e.property.1
    rw [degree_fin_three] at htotal
    have hindex := e.property.2
    let z : Fin (m + 1) := ⟨e.val 2, by omega⟩
    refine ⟨z, ⟨Finsupp.equivFunOnFinite.symm ![e.val 0, e.val 1], ?_⟩⟩
    rw [mem_cappedDegreeExponents, degree_fin_two]
    change e.val 0 + e.val 1 ≤ b - e.val 2 ∧ e.val 1 ≤ 2 * (m - e.val 2)
    omega
  invFun p := by
    obtain ⟨z, u⟩ := p
    have htotal := u.property.1
    rw [degree_fin_two] at htotal
    have hindex := u.property.2
    have hz := z.isLt
    refine ⟨Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1, z.val], ?_⟩
    change (Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1, z.val]).degree ≤ b ∧ _
    rw [degree_fin_three]
    change u.val 0 + u.val 1 + z.val ≤ b ∧ u.val 1 + 2 * z.val ≤ 2 * m
    omega
  left_inv e := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨z, hz⟩, u⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

private theorem fiber_card (b m z : ℕ) (hb : 2 * m ≤ b) (hz : z ≤ m) :
    (cappedDegreeExponents (Fin 2) 1 (b - z) (2 * (m - z))).ncard =
      (2 * (m - z) + 1) * (b + 1 - m) := by
  have hc : 2 * (m - z) ≤ b - z := by omega
  have h := two_mul_ncard_cappedDegreeExponents_fin_two (b - z) (2 * (m - z)) hc
  have hfactor : 2 * (b - z) + 2 - 2 * (m - z) = (b + 1 - m) * 2 := by omega
  rw [hfactor, ← mul_assoc, ← mul_comm 2] at h
  exact Nat.eq_of_mul_eq_mul_left (show 0 < 2 by decide) h

private theorem sum_odd_reverse (m : ℕ) :
    (∑ z ∈ Finset.range (m + 1), (2 * (m - z) + 1)) = (m + 1) ^ 2 := by
  calc
    _ = ∑ z ∈ Finset.range (m + 1), (2 * z + 1) := by
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun z => 2 * z + 1) (m + 1)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        Nat.nsmul_eq_mul, mul_one]
      rw [← Finset.mul_sum, mul_comm 2, Finset.sum_range_id_mul_two]
      simp only [Nat.add_sub_cancel]
      ring

theorem cap_ncard (b m : ℕ) (hb : 2 * m ≤ b) :
    (cap b (2 * m)).ncard = (m + 1) ^ 2 * (b + 1 - m) := by
  classical
  let (z : Fin (m + 1)) : Fintype
      (cappedDegreeExponents (Fin 2) 1 (b - z) (2 * (m - z))) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_congr (capFibers b m hb), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  calc
    _ = ∑ z : Fin (m + 1), (2 * (m - z.val) + 1) * (b + 1 - m) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, fiber_card b m z hb (by omega)]
    _ = _ := by
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun z => 2 * (m - z) + 1),
        sum_odd_reverse]

end
end K1_13_7_6
end PackSource_K1_13_7_6Lattice

section PackSource_K1_13_7_2Defs
set_option autoImplicit true
namespace K1_13_7_2

noncomputable section

open Polynomial K1 K1_13 K1_13_6 K1_13_7

def lowerBox : Shape := ⟨35007, 12106, 0⟩

def cutBox (x : Shape) : Shape :=
  let h := fatChart x
  ⟨max (max h.b lowerBox.b) (max h.j (lowerBox.j + 1)),
    max h.j (lowerBox.j + 1), max 1 h.t⟩

def curveMass32 (x : Shape) : ℕ :=
  mixed32 x.chamber lowerBox (cutBox x) (fatChart x)

def componentMass32 (x : Shape) : ℕ :=
  mixed32 x.chamber lowerBox (cutBox x) x.chamber

def liftLower (q : Row 3) : Row 4 := MvPolynomial.rename Fin.castSucc q

/-- The abscissa and lower jets are differentiated before geometric scalar extension. -/
def lowerFlow (q : Row 3) : Row 4 := partialFlow (liftLower q)

structure LiftedSurface (f : Row 4) (q : Row 3) (surface : Ideal GeoJets) : Prop where
  minimal : (intersectionIdeal f (liftLower q)).IsMinimalPrime surface
  leading : toGeneric (liftLower (K1_13_1.anchorLead f)) ∉ surface
  regular : toGeneric (separant f) ∉ surface

/-- A single reduced lower equation serves for every lifted component. -/
structure ReducedCut (f : Row 4) (D q : Row 3) : Prop where
  ne_zero : q ≠ 0
  divides : q ∣ D
  caps : LowerCaps q 35007 12106
  reduced : Squarefree (genericRow q)
  proper : IsRelPrime (toGeneric f) (toGeneric (liftLower q))
  roots : ∀ S : Geom[X], atJet D S = 0 → atJet q S = 0
  flow_box : InBox (shape (lowerFlow q)) ⟨35007, 12107, 1⟩
  simple : ∀ surface, (h : LiftedSurface f q surface) → surface.height = 2 ∧
    cycleLength (intersectionIdeal f (liftLower q)) surface h.minimal.isPrime = 1
  invariant : ∀ surface, LiftedSurface f q surface → toGeneric (lowerFlow q) ∈ surface → Invariant f surface

/-- Substitute a genuine polynomial trajectory over any extension of the constants. -/
def evalTrajectory {L : Type} [Field L] [Algebra Geom L] (P : Row 4) (S : L[X]) : L[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (algebraMap Geom L))
    (fun i => Polynomial.hasseDeriv i.val S) P

/-- Cleared coefficients and a numerically bounded form of the degree test.
The prime-wise test equivalence allows the sharper linear-in-`Y₃` chart. -/
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : L[X]),
    S.natDegree ≤ 133658 → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)

def ProperMark (f : Row 4) (q : Row 3) (E : Row 4) (S : Geom[X]) : Prop :=
  ∃ surface, LiftedSurface f q surface ∧ surface ≤ markIdeal S ∧
    (toGeneric E ∉ surface ∨ toGeneric (lowerFlow q) ∉ surface)

abbrev CoeffRing := MvPolynomial (Fin taylorLength) Geom

def universalPolynomial : CoeffRing[X] :=
  ∑ i : Fin taylorLength, C (MvPolynomial.X i) * Polynomial.X ^ i.val

def universalEval (f : Row 4) : CoeffRing[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (MvPolynomial.C : Geom →+* CoeffRing))
    (fun i => hasseDeriv i.val universalPolynomial) f

def coefficientPointIdeal (S : Geom[X]) : Ideal CoeffRing :=
  RingHom.ker (MvPolynomial.eval (fun i : Fin taylorLength => S.coeff i.val))

/-- An integral coefficient family of dimension at least two, defined over
the constants, whose universal polynomial solves the small equation. -/
structure ActualFamily (f : Row 4) (P : Ideal CoeffRing) : Prop where
  prime : P.IsPrime
  dimension : 2 ≤ (MvPolynomial.affineHilbertPolynomial P).natDegree
  solves : ∀ i, (universalEval f).coeff i ∈ P
  regular : ∃ i, (universalEval (separant f)).coeff i ∉ P

def IntegratedMark (f : Row 4) (S : Geom[X]) : Prop :=
  ∃ P, ActualFamily f P ∧ P ≤ coefficientPointIdeal S

/-- Proper value sections of a coefficient threefold admit surface covers
whose total degree is bounded by the degree of the threefold. -/
def ThreefoldSections (Γ : Finset K) (s : K → K[X]) (d : ℕ) : Prop := by
  classical
  exact ∀ x a : K, (∃ γ ∈ Γ, (s γ).eval x ≠ a) →
    let H := Γ.filter (fun γ => (s γ).eval x = a)
    ∃ C : Pieces H, H ⊆ C.union ∧ C.surfaces s ∧ (∀ i, 0 < C.degree i) ∧ C.total ≤ d

def ThreefoldPieces {Γ : Finset K} (C : Pieces Γ) (s : K → K[X]) : Prop :=
  ∀ i, ThreefoldSections (C.piece i) s (C.degree i)

end

end K1_13_7_2
end PackSource_K1_13_7_2Defs

section PackSource_K1_13_7_4Defs
set_option autoImplicit true
namespace K1_13_7_4
noncomputable section
open Polynomial K1_13 K1_13_7
open scoped BigOperators

/-- The ordinary total degree of a multi-index in the three lower jets. -/
def multiOrder (a : Fin 3 →₀ ℕ) : ℕ :=
  a.sum (fun _ k => k)

/-- The Hasse partial at a multi-index. The product of binomial coefficients
makes the definition valid in positive characteristic. -/
def hassePartial {A : Type*} [CommSemiring A]
    (a : Fin 3 →₀ ℕ) (F : MvPolynomial (Fin 3) A) : MvPolynomial (Fin 3) A :=
  ∑ m ∈ F.support,
    MvPolynomial.monomial (m - a) (F.coeff m * ∏ i : Fin 3, ((m i).choose (a i) : A))

/-- Order at the ambient local ring of a geometric prime. -/
def VanishesTo (q : PrimeSpectrum Lower) (F : Lower) (d : ℕ) : Prop :=
  let A := Localization.AtPrime q.asIdeal
  algebraMap Lower A F ∈ IsLocalRing.maximalIdeal A ^ d

end
end K1_13_7_4
end PackSource_K1_13_7_4Defs
