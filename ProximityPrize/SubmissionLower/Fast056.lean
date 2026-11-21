import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Fast052
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000
open private activeNatCount_eq sumRange_prefix innerSlice_eq sumToCap_eq sumRange_suffix
  sumRange_congr sumRange_zero natLine_zero from ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
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
end
section
set_option Elab.async false
namespace K1_13_2_3_3
open K1_13_2 K1_13_2_3 Finset
open K1_13_2_3_1 (denPrefix denPrefix_of_nonpos)
open scoped BigOperators
private def offsets (s : ℕ) : ℕ := 4650 - s
private def flag (n j : ℤ) : Flag := ⟨1650,1650 - j, 1650,550, n - j⟩
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
  ·
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
private def packedCuts : List ℕ :=
  [1884877150839,1492194651746,942438537804,1570711722551,1492155854371,
   1560874277390,922171043323,780298540519,1471922525652,778910935489,
   778910390703,1488933185949,1466373428620,1471742129531,1466015503722,
   1282763565401,1466015503690,1454562252090,1463151842603,727278331164,
   709921952013,1276991850751,640642880754,638428270820,1414291165399,
   1259115981003,314223174847,1256585316531,1256584717480,314146179229,
   1256582320274,311689515144,1246690353278,1177429774453,293274685548,
   146601559140,292630437979,1170521474132,1170450030668,141872603205,
   69827855423,70901579832,558482097203,279206961197,554118418472,
   69260558371,34495008799]
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
private def activePrefix (j : ℤ) : ℤ :=
  j * (24 * denominator 1650) - denPrefix 1650 + denPrefix (1650 - j)
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
private theorem check₁ : total 256 256 = 0xdc3ec39aa670 := by decide +kernel
private theorem check₂ : total 512 256 = 0x849854bf9218 := by decide +kernel
private theorem check₃ : total 768 256 = 77485223947464 := by decide +kernel
private theorem check₄ : total 1024 256 = 34445829248736 := by decide +kernel
private theorem check₅ : total 1280 223 = 0x9dd6637e808 := by decide +kernel
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
end
section
namespace K1_13_6_1_4_2_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
abbrev Generator (a h : Shape) := latticeIndices a ⊕ latticeIndices h
abbrev BigradedPolynomial (a h : Shape) := MvPolynomial (Generator a h) (Coeff a h)
def weight {α β : Type} : α ⊕ β → ℕ × ℕ := Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))
abbrev grade {k α β : Type} [CommSemiring k] (d : ℕ × ℕ) :
    Submodule k (MvPolynomial (α ⊕ β) k) :=
  weightedHomogeneousSubmodule k weight d
def generatorExponent {a h : Shape} : Generator a h → Fin 4 →₀ ℕ :=
  Sum.elim Subtype.val Subtype.val
def dehom (surface : Ideal GeoJets) (a h : Shape) :
    BigradedPolynomial a h →ₐ[Coeff a h] SurfaceRing surface a h :=
  (Ideal.Quotient.mkₐ _ _).comp (aeval fun v => monomial (generatorExponent v) 1)
def relations (surface : Ideal GeoJets) (a h : Shape) : Ideal (BigradedPolynomial a h) :=
  ((RingHom.ker (dehom surface a h).toRingHom).homogeneousCore grade).toIdeal
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
def chart {k α β : Type} [CommSemiring k] (x : α) (y : β) :
    MvPolynomial (α ⊕ β) k :=
  MvPolynomial.X (Sum.inl x) * MvPolynomial.X (Sum.inr y)
end
end K1_13_6_1_4_2_1_1
end
section
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
end
section
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
end
section
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
end
section
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
end
section
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
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_1_4_2_1_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2
  K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_2 MvPolynomial
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h)
    {E : Type} [Field E] [Algebra GeoField E]
    (φ : rees surface a h →ₐ[GeoField] E), φ (pairGen surface a h e) ≠ 0 →
    monomialFraction surface e.1.val ≠ 0 ∧ monomialFraction surface e.2.val ≠ 0 ∧
      ∃ f : chartAlgebra surface a h e →ₐ[GeoField] E,
        ∀ i, f (chartCoord surface a h e i) = ratioValue surface a h e φ i
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
end
section
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
end
section
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
end
section
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
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_2_1_2_2_2
noncomputable section
open Algebra MvPolynomial
open scoped BigOperators
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
end
section
namespace K1_13_6_1_4_2_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    Function.Injective (leftMul surface a h) ∧ Function.Injective (rightMul surface a h)
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
end
section
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
end
section
namespace K1_13_2_3_6
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
private def rowsA_grade3012 : List (List ℕ) :=
  [[8791654400,13086490624,8724414464,6576865280,6543310848,4395761664,4362207232,
    2214690816,50429952,2214592704,4345299136,33554624,25166016,16777408,12583104,
    4194496,6442451136,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,
    98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,
    12,6,2]]
private theorem rowsA_grade3012_checked :
    rowsA_grade3012.length = 1 ∧ fits 3012 rowsA_grade3012 = true ∧
      value 3012 rowsA_grade3012 = 56171069 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3013 : List (List ℕ) :=
  [[0,8791654400,13086490624,6576930816,8724348928,4395827200,6543245312,4362207232,
    67207168,2197913600,2214592704,2197815488,2181038272,25166016,16777408,6291648,
    8589934784,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,
    6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,
    6,1]]
private theorem rowsA_grade3013_checked :
    rowsA_grade3013.length = 1 ∧ fits 3013 rowsA_grade3013 = true ∧
      value 3013 rowsA_grade3013 = 55575093 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3014 : List (List ℕ) :=
  [[0,10939138048,10939006976,8724414464,6576865280,6543310848,4395761664,4362207232,
    67207168,2197913600,2214592704,2197815488,2181038272,25166016,16777408,8388800,
    2097344,8589934784,160,2147483800,144,140,136,132,8589934720,108,104,100,
    8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,
    4]]
private theorem rowsA_grade3014_checked :
    rowsA_grade3014.length = 1 ∧ fits 3014 rowsA_grade3014 = true ∧
      value 3014 rowsA_grade3014 = 56103008 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3015 : List (List ℕ) :=
  [[0,10939138048,13086490624,6576930816,8724348928,6543310848,2248278016,6509690880,
    67207168,2197913600,2214592704,2197815488,33554624,2172649664,12583104,6291648,
    8589934784,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,
    8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,
    3]]
private theorem rowsA_grade3015_checked :
    rowsA_grade3015.length = 1 ∧ fits 3015 rowsA_grade3015 = true ∧
      value 3015 rowsA_grade3015 = 56895847 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3016 : List (List ℕ) :=
  [[2147483648,10939138048,10939006976,8724414464,6576865280,6543310848,4395761664,
    4362207232,50462720,2197913600,2214592704,2197815488,2181038272,25166016,16777408,
    8388800,10737418432,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,
    98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,
    12,6,2]]
private theorem rowsA_grade3016_checked :
    rowsA_grade3016.length = 1 ∧ fits 3016 rowsA_grade3016 = true ∧
      value 3016 rowsA_grade3016 = 56371788 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3017 : List (List ℕ) :=
  [[2147483648,10939138048,10939006976,10871898112,4429381632,8690794496,2248278016,
    4362207232,50462720,67207168,2197913600,67109056,4345299136,33554624,25166016,
    16777408,12583104,4194496,10737418432,160,2147483800,2147483792,140,134,129,
    6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,
    38,33,32,25,24,17,16,12,6,1]]
private theorem rowsA_grade3017_checked :
    rowsA_grade3017.length = 1 ∧ fits 3017 rowsA_grade3017 = true ∧
      value 3017 rowsA_grade3017 = 57063697 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3018 : List (List ℕ) :=
  [[4294967296,10939138048,10939006976,8724414464,6576865280,6543310848,2248278016,
    6509690880,50462720,2197913600,2214592704,2197815488,2181038272,25166016,16777408,
    6291648,12884902080,160,2147483800,144,140,136,132,8589934720,108,104,100,
    8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,
    4]]
private theorem rowsA_grade3018_checked :
    rowsA_grade3018.length = 1 ∧ fits 3018 rowsA_grade3018 = true ∧
      value 3018 rowsA_grade3018 = 56668144 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3019 : List (List ℕ) :=
  [[4294967296,10939138048,10939006976,10871898112,4429381632,8690794496,2248278016,
    4362207232,50462720,4345397248,67109056,2197815488,2181038272,25166016,16777408,
    8388800,2097344,10737418432,2147483808,2147483800,144,140,136,131,8589934720,108,
    104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,
    12,8,3]]
private theorem rowsA_grade3019_checked :
    rowsA_grade3019.length = 1 ∧ fits 3019 rowsA_grade3019 = true ∧
      value 3019 rowsA_grade3019 = 57382107 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3020 : List (List ℕ) :=
  [[4294967296,13086621696,10939006976,8724414464,4429381632,8690794496,67305472,
    100794368,6509690880,50462720,2197913600,2214592704,2197815488,33554624,2172649664,
    12583104,6291648,12884902080,160,2147483800,2147483792,140,134,130,6442451072,112,
    108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,
    24,18,16,12,6,2]]
private theorem rowsA_grade3020_checked :
    rowsA_grade3020.length = 1 ∧ fits 3020 rowsA_grade3020 = true ∧
      value 3020 rowsA_grade3020 = 58013970 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3021 : List (List ℕ) :=
  [[6442450944,10939138048,10939006976,10871898112,4429381632,6543310848,67305472,
    2248278016,4362207232,50462720,2197913600,98560,67109056,2197815488,2181038272,
    25166016,16777408,8388800,2097344,12884902080,160,2147483800,2147483792,140,134,
    129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,
    2147483696,38,33,32,25,24,17,16,12,6,1]]
private theorem rowsA_grade3021_checked :
    rowsA_grade3021.length = 1 ∧ fits 3021 rowsA_grade3021 = true ∧
      value 3021 rowsA_grade3021 = 57706514 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3022 : List (List ℕ) :=
  [[6442450944,13086621696,8791523328,10871898112,4429381632,8690794496,67305472,
    100794368,4362207232,2197946368,50429952,98560,98496,67109056,2197815488,33554624,
    25166016,16777408,12583104,4194496,15032385728,160,2147483800,144,140,136,132,
    8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,
    2147483680,2147483672,16,12,8,4]]
private theorem rowsA_grade3022_checked :
    rowsA_grade3022.length = 1 ∧ fits 3022 rowsA_grade3022 = true ∧
      value 3022 rowsA_grade3022 = 58257555 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3023 : List (List ℕ) :=
  [[8589934592,13086621696,8791523328,10871898112,4429381632,6543310848,67305472,
    100794368,6509690880,2197946368,2147582208,67109056,2197815488,2181038272,25166016,
    16777408,8388800,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,
    104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,
    12,8,3]]
private theorem rowsA_grade3023_checked :
    rowsA_grade3023.length = 1 ∧ fits 3023 rowsA_grade3023 = true ∧
      value 3023 rowsA_grade3023 = 57679792 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3024 : List (List ℕ) :=
  [[8589934592,13086621696,8791523328,13019381760,2281897984,8690794496,67305472,
    100794368,4362207232,2197946368,50429952,2147582208,2197815488,2181038272,25166016,
    16777408,12583104,2097344,15032385728,160,2147483800,2147483792,140,134,130,
    6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,
    38,34,32,26,24,18,16,12,6,2]]
private theorem rowsA_grade3024_checked :
    rowsA_grade3024.length = 1 ∧ fits 3024 rowsA_grade3024 = true ∧
      value 3024 rowsA_grade3024 = 58493504 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3025 : List (List ℕ) :=
  [[8589934592,15234105344,8791523328,10871898112,2281897984,8690794496,2214789120,
    6509690880,2197946368,2147582208,67109120,2197815488,33554624,2172649664,12583104,
    6291648,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,
    102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,
    16,12,6,1]]
private theorem rowsA_grade3025_checked :
    rowsA_grade3025.length = 1 ∧ fits 3025 rowsA_grade3025 = true ∧
      value 3025 rowsA_grade3025 = 59069395 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3026 : List (List ℕ) :=
  [[10737418240,13086621696,8791523328,13019381760,2281897984,6543310848,2214789120,
    100794368,4362207232,2197946368,2147582208,67109120,50331904,50331840,2181038272,
    25166016,16777408,8388800,196,17179869376,160,2147483800,144,140,136,132,
    8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,
    2147483680,2147483672,16,12,8,4]]
private theorem rowsA_grade3026_checked :
    rowsA_grade3026.length = 1 ∧ fits 3026 rowsA_grade3026 = true ∧
      value 3026 rowsA_grade3026 = 58930449 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3027 : List (List ℕ) :=
  [[10737418240,15234105344,6644039680,13019381760,2281897984,8690794496,2214789120,
    4362207232,4345430016,2147582208,67109120,2197815488,33554624,25166016,16777408,
    12583104,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,
    108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,
    2147483672,16,12,8,3]]
private theorem rowsA_grade3027_checked :
    rowsA_grade3027.length = 1 ∧ fits 3027 rowsA_grade3027 = true ∧
      value 3027 rowsA_grade3027 = 59459098 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3028 : List (List ℕ) :=
  [[12884901888,13086621696,8791523328,10871898112,100925440,2281897984,6543310848,
    2214789120,6509690880,2197946368,33685504,98560,67109120,50331904,50331840,
    2181038272,25166016,16777408,8388800,198,194,15032385728,160,2147483800,2147483792,
    140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,
    50,2147483696,38,34,32,26,24,18,16,12,6,2]]
private theorem rowsA_grade3028_checked :
    rowsA_grade3028.length = 1 ∧ fits 3028 rowsA_grade3028 = true ∧
      value 3028 rowsA_grade3028 = 59274138 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3029 : List (List ℕ) :=
  [[12884901888,15234105344,6644039680,13019381760,100925440,134414336,8690794496,
    2214789120,4362207232,2197946368,33685504,2147582208,2197815552,50331840,33554624,
    25166016,16777408,12583104,204,198,193,15032385728,160,2147483800,2147483792,140,
    134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,
    2147483696,38,33,32,25,24,17,16,12,6,1]]
private theorem rowsA_grade3029_checked :
    rowsA_grade3029.length = 1 ∧ fits 3029 rowsA_grade3029 = true ∧
      value 3029 rowsA_grade3029 = 59729025 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3030 : List (List ℕ) :=
  [[12884901888,17381588992,4496556032,13019381760,100925440,134414336,8690794496,
    2214789120,6509690880,2197946368,131328,98560,67109120,2197815552,2181038272,
    25166016,12583104,204,200,196,17179869376,160,2147483800,144,140,136,132,
    8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,
    2147483680,2147483672,16,12,8,4]]
private theorem rowsA_grade3030_checked :
    rowsA_grade3030.length = 1 ∧ fits 3030 rowsA_grade3030 = true ∧
      value 3030 rowsA_grade3030 = 60419416 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private def rowsA_grade3031 : List (List ℕ) :=
  [[15032385536,15234105344,6644039680,13019381760,100925440,134414336,6543310848,
    4362272768,4362207232,2197946368,33685504,2147582208,2197815552,2181038272,25166016,
    16777408,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,
    8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,
    2147483680,2147483672,16,12,8,3]]
private theorem rowsA_grade3031_checked :
    rowsA_grade3031.length = 1 ∧ fits 3031 rowsA_grade3031 = true ∧
      value 3031 rowsA_grade3031 = 60143148 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
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
end
section
namespace K1_13_2_3_5
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open K1_13_2_3
open private rowLoop rowScore unpack from ProximityPrize.SubmissionLower.Numeric5Certificate
private def denE (x : Nat) : Nat :=
  let q := Nat.add (Nat.mul 2 x) 15
  let t := Nat.add (Nat.mul q x) 30
  Nat.div (Nat.add (Nat.mul t x) 25) 72
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
  ⟨457,117,0x400000100000020000003000000380000044000005000000600000068000008000000800000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000408000041800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c00000600004060000406000040600004060000406000040600006060000606000060600006060000606000060600006060000606000080600008060040006004000600600060060006006000⟩,
  ⟨457,116,0x80000018000002000000300000040000004800000600000060000006c00000800000088000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002040000210000022000002300000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003400000340000036000003600000360000040000004000000400000040000004000000400000040000004000000400000040000004000000410000042000004300000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c0000060000406000040600004060000406000040600006060000606000060600006060000606000060600006060000606000080600008060000806004000600600060060006006000⟩,
  ⟨456,116,0xc0000018000002400000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000380000040000004000000400000040000004000000400000040000004000000400000040000004080000410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c00000600004060000406000040600004060000406000060600006060000606000060600006060000606000060600006060000806000080600008060040006004000600600060060006006000⟩,
  ⟨456,116,0x400000100000020000003000000380000044000005000000600000068000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003000000310000031800003300000330000034000003600000360000036000003800000400000040000004000000400000040000004000000400000040000004000000400000040c000041800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c0000060000406000040600004060000406000060600006060000606000060600006060000606000060600006060000806000080600008060000806004000600600060060006006000⟩
]
private theorem rowsE_chunk000_length : rowsE_chunk000.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk000_score : batchScore 2680 rowsE_chunk000 = 731242585 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk004 : List Row := [
  ⟨456,115,0x80000018000002000000300000040000004800000600000060000006c00000800000088000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002040000210000022000002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000040000004000000400000040000004000000400000040000004000000400000040000004040000410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c0000050000006000040600004060000406000040600006060000606000060600006060000606000060600006060000606000080600008060000806004000600600060060006006000⟩,
  ⟨455,115,0xc0000018000002800000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000408000041800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c0000060000406000040600004060000406000060600006060000606000060600006060000606000060600006060000806000080600008060000806004000600600060060006006000⟩,
  ⟨455,115,0x400000100000020000003000000380000044000006000000600000068000008000000840000090000009800000c000000c000000c000000d000000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000330000034000003600000360000036000003800000400000040000004000000400000040000004000000400000040000004000000400000040c000041800004300000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000006000040600004060000406000060600006060000606000060600006060000606000060600006060000806000080600008060000806004000600600060060006006000⟩,
  ⟨454,115,0x80000018000002400000300000040000004800000600000060000006c00000800000088000009000000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002040000210000022000002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000380000040000004000000400000040000004000000400000040000004000000400000040000004040000410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c0000060000406000040600004060000606000060600006060000606000060600006060000606000060600008060000806000080600008060000806006000600600060060006006000⟩
]
private theorem rowsE_chunk004_length : rowsE_chunk004.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk004_score : batchScore 2684 rowsE_chunk004 = 723671953 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk008 : List Row := [
  ⟨454,114,0xc0000018000002800000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003200000330000034000003400000360000036000003800000400000040000004000000400000040000004000000400000040000004000000400000240c000041800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c000006000040600004060000406000060600006060000606000060600006060000606000060600006060000806000080600008060000806004000600600060060006006000⟩,
  ⟨454,114,0x40000010000002000000300000038000004400000600000060000006800000800000084000009000000a000000c000000c000000c400000d000000d80000100000010000001000000110000011800001200000130000018000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000002000000200000020c000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000014000006410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000005000000600004060000406000060600006060000606000060600006060000606000060600006060000806000080600008060000806000080600600060060006006000⟩,
  ⟨453,114,0x80000018000002400000300000040000004800000600000060000007000000800000088000009000000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001c0000020000002000000200000020000002000000204000021000002200000230000024000002400000260000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003080000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000004408000041800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c000006000040600004060000606000060600006060000606000060600006060000606000060600008060000806000080600008060000806004000600600060060006006000⟩,
  ⟨453,113,0xc000001c000002800000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003300000330000034000003400000360000036000003800000400000040000004000000400000040000004000000400000040000004000003400000840c000041800004200000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c00000600004060000606000060600006060000606000060600006060000606000060600008060000806000080600008060000806000080600600060060006006000⟩
]
private theorem rowsE_chunk008_length : rowsE_chunk008.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk008_score : batchScore 2688 rowsE_chunk008 = 715960368 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk012 : List Row := [
  ⟨452,114,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d800001000000100000010000001100000118000013000001300000180000018000001800000180000018000001800000190000019800001a000001b00000200000020000002000000200000020000002000000210000021800002300000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003400000340000036000003600000360000040000004000000400000040000004000000400000040000004000000400000240000064040000410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000006000040600004060000606000060600006060000606000060600006060000606000060600008060000806000080600008060000806006000600600060060006006000⟩,
  ⟨452,113,0x80000018000002400000300000040000004800000600000060000007000000800000088000009800000c000000c000000c000000c800000d000001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001c00000200000020000002000000200000020000002080000210000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003200000330000034000003400000360000036000003800000400000040000004000000400000040000004000000400000040000014000006400000c408000041800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c00000600004060000606000060600006060000606000060600006060000606000060600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨452,112,0xc000001c000002800000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003000000310000032000003300000330000034000003600000360000036000003800000400000040000004000000400000040000004000000400000040000044000008400000c410000041800004300000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c00000500000060000606000060600006060000606000060600006060000606000060600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨451,113,0x40000014000002000000300000040000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e000001000000100000010400001100000118000013000001300000180000018000001800000180000018000001800000190000019800001b000001b000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000308000031000003200000330000034000003400000360000036000003800000400000040000004000000400000040000004000000400000040000034000008400000c4000010410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c00000600006060000606000060600006060000606000060600006060000606000080600008060000806000080600008060000806000080600600060060006006000⟩
]
private theorem rowsE_chunk012_length : rowsE_chunk012.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk012_score : batchScore 2692 rowsE_chunk012 = 708053556 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk016 : List Row := [
  ⟨451,112,0x80000018000002400000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c00000200000020000002000000200000020000002080000210000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000380000040000004000000400000040000004000000400000040000024000006400000c400001040c000041800004200000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c0000060000606000060600006060000606000060600006060000606000060600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨450,112,0x10000001c000002800000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020c000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000014000006400000c40000104000010410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c00000600006060000606000060600006060000606000060600006060000606000080600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨450,112,0x80000014000002000000300000040000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002040000210000022000002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000380000040000004000000400000040000004000000400000040000044000008400000c4000010400001841800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c0000060000606000060600006060000606000060600006060000606000080600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨450,111,0xc0000018000002400000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000026000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000034000008400000c4000010400001840c000041800004300000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c0000060000606000060600006060000606000060600006060000606000080600008060000806000080600008060000806000080600600060060006006000⟩
]
private theorem rowsE_chunk016_length : rowsE_chunk016.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk016_score : batchScore 2696 rowsE_chunk016 = 700130495 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk020 : List Row := [
  ⟨449,112,0x40000010000001c000002800000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000340000034000003600000360000036000004000000400000040000004000000400000040000024000006400000c400001040000104000018410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c0000060000606000060600006060000606000060600006060000606000080600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨449,111,0x80000014000002000000300000040000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001b000002000000200000020000002000000200000020400002100000220000023000002300000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000308000031800003200000330000034000003400000360000036000003800000400000040000004000000400000040000014000006400000c400001040000104000018400001841800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c000006000060600006060000606000060600006060000606000080600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨448,111,0xc0000018000002400000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003000000310000031800003300000330000034000003600000360000036000003800000400000040000004000000400000040000044000008400000c400001040000184000018410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c0000060000606000060600006060000606000060600006060000806000080600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨448,111,0x40000010000001c00000300000034000004000000500000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000308000031000003200000330000034000003400000360000036000003800000400000040000004000000400000040000034000008400000c400001040000184000018400002041800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c000006000060600006060000606000060600006060000806000080600008060000806000080600008060000806000080600600060060006006000⟩
]
private theorem rowsE_chunk020_length : rowsE_chunk020.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk020_score : batchScore 2700 rowsE_chunk020 = 692205014 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk024 : List Row := [
  ⟨448,110,0x80000014000002000000300000040000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002040000210000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000380000040000004000000400000040000024000006400000c4000010400001040000184000018400002041800004200000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c000006000060600006060000606000060600006060000606000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨447,110,0xc0000018000002400000300000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c0000020000002000000200000020000002000000208000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000036000003600000360000038000004000000400000040000014000006400000c40000104000010400001840000184000020410000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000006000060600006060000606000060600006060000806000080600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨447,110,0x400000100000020000003000000340000044000005000000600000068000008000000800000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000018c000019800001a000001b00000200000020000002000000200000020000002000000210000021800002300000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000380000040000004000000400000040000044000008400000c4000010400001840000184000020400002041800004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000005000000600006060000606000060600006060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨446,110,0x80000014000002000000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001c00000200000020000002000000200000020000002080000210000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000038000004000000400000040000034000008400000c40000104000018400001840000204000020400002042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000006000060600006060000606000060600008060000806000080600008060000806000080600008060000806000080600600060060006006000⟩
]
private theorem rowsE_chunk024_length : rowsE_chunk024.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk024_score : batchScore 2704 rowsE_chunk024 = 684283062 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk028 : List Row := [
  ⟨446,109,0xc0000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000340000034000003600000360000036000004000000400000040000024000006400000c40000104000010400001840000184000020400002041000004200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c00000600006060000606000060600006060000806000080600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨446,109,0x400000100000020000003000000340000044000005000000600000068000008000000800000090000009800000c000000c000000c000000d000000d800001000000100000010000001100000118000012000001300000180000018000001800000180000018000001800000190000019800001b000001b000002000000200000020000002000000200000020400002100000220000023000002300000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000308000031800003200000330000034000003400000360000036000003800000400000040000014000006400000c400001040000104000018400001840000204000020400002041800004200000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c00000600006060000606000060600006060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨445,109,0x80000018000002000000300000040000004800000600000060000006c00000800000088000009000000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000030000003000000300000030000003000000300000030000003000000300000030000003000000310000031800003300000330000034000003600000360000036000003800000400000040000044000008400000c400001040000184000018400002040000204000020400003042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c00000600006060000606000060600008060000806000080600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨445,108,0xc0000018000002400000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000304000031000003200000330000034000003400000360000036000003800000400000040000034000008400000c400001040000184000018400002040000204000020400003040000304200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c00000500000060000606000060600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩
]
private theorem rowsE_chunk028_length : rowsE_chunk028.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk028_score : batchScore 2708 rowsE_chunk028 = 676070898 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk032 : List Row := [
  ⟨444,109,0x400000100000020000003000000380000044000005000000600000068000008000000840000090000009800000c000000c000000c400000d000000d80000100000010000001040000110000011800001300000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002040000210000022000002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000380000040000024000006400000c4000010400001040000184000018400002040000204000020400003041800004300000430000044000004600000460000048000004800000480000048000004c000004c000004c000004c00000600006060000606000060600008060000806000080600008060000806000080600008060000806000080600600060060006006000⟩,
  ⟨444,108,0x80000018000002000000300000040000004800000600000060000006c00000800000088000009000000c000000c000000c000000c800000d000001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c0000020000002000000200000020000002000000208000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000036000003600000360000040000014000006400000c4000010400001040000184000018400002040000204000020400003040000304200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c0000060000606000060600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨444,107,0xc0000018000002400000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000002000000200000020c000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000380000040000044000008400000c4000010400001840000184000020400002040000204000030400003040000304200000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c0000060000606000060600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨443,108,0x40000010000002000000300000038000004400000600000060000006800000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002040000210000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000038000004000008400000c40000104000018400001840000204000020400002040000304000030400003042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c0000060000606000080600008060000806000080600008060000806000080600008060000806000080600600060060006006000⟩
]
private theorem rowsE_chunk032_length : rowsE_chunk032.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk032_score : batchScore 2712 rowsE_chunk032 = 668032569 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk036 : List Row := [
  ⟨443,107,0x80000018000002000000300000040000004800000600000060000007000000800000088000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000340000034000003600000360000036000004000006400000c40000104000010400001840000184000020400002040000204000030400003040000304200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c0000060000606000060600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨443,106,0xc0000018000002800000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000002000000200000020000002000000200000020000002100000218000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000308000031800003200000330000034000003400000360000036000003800000400000c400001040000104000018400001840000204000020400002040000304000030400003040000304300000430000044000004600000460000048000004800000480000048000004c000004c000004c000004c000006000060600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨442,107,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002040000210000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003300000330000034000003600000360000036000003800000400000c40000104000018400001840000204000020400002040000304000030400003040000304200000430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c000006000080600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨442,106,0x80000018000002400000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000304000031000003200000330000034000003400000360000036000003800000400000c400001040000184000018400002040000204000020400003040000304000030400003040000404200000430000044000004600000460000046000004800000480000048000004c000004c000004c000004c000006000080600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩
]
private theorem rowsE_chunk036_length : rowsE_chunk036.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk036_score : batchScore 2716 rowsE_chunk036 = 659645900 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk040 : List Row := [
  ⟨441,106,0xc000001c000002800000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000018c000019800001a000001b00000200000020000002000000200000020000002040000210000022000002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003200000330000034000003400000360000036000003800000400001040000104000018400001840000204000020400002040000304000030400003040000304000040430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c000006000080600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨441,106,0x40000010000002000000300000040000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000340000034000003600000360000036000004000010400001040000184000018400002040000204000020400003040000304000030400003040000404000040430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000006000080600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨441,105,0x80000018000002400000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003080000318000032000003300000340000034000003600000360000038000004000010400001840000184000020400002040000204000030400003040000304000030400004040000404300000430000044000004600000460000048000004800000480000048000004c000004c000004c000004c00000600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨440,105,0x10000001c000002800000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000180000018000001800000180000018000001800000190000019800001b000001b00000200000020000002000000200000020000002040000210000022000002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003200000330000034000003400000360000036000003800000400001840000184000020400002040000204000030400003040000304000030400004040000404000040430000044000004400000460000046000004800000480000048000004c000004c000004c000004c000005000000600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩
]
private theorem rowsE_chunk040_length : rowsE_chunk040.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk040_score : batchScore 2720 rowsE_chunk040 = 651622799 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk044 : List Row := [
  ⟨440,105,0x40000014000002000000300000040000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000340000034000003600000360000038000004000010400001840000184000020400002040000204000030400003040000304000030400004040000404000040430000044000004600000460000046000004800000480000048000004c000004c000004c000004c00000600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨440,104,0xc0000018000002400000300000040000004800000600000064000008000000800000088000009800000c000000c000000c000000c800000d80000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000308000031800003200000330000034000003400000360000036000003800000400001840000184000020400002040000204000030400003040000304000030400004040000404000040400004044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c0000060000806000080600008060000806000080600008060000806000080600008060000806006000⟩,
  ⟨439,104,0x10000001c000003000000340000040000005000000600000068000008000000800000090000009800000c000000c000000c000000d000000d80000100000010000001000000110000011800001300000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002040000210000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003300000330000034000003600000360000036000003800000400001840000204000020400002040000304000030400003040000304000040400004040000404000040430000044000004400000460000046000004800000480000048000004c000004c000004c000004c00000600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨439,104,0x80000014000002000000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000340000034000003600000360000038000004000018400002040000204000020400003040000304000030400003040000404000040400004040000404000040430000044000004600000460000048000004800000480000048000004c000004c000004c000004c0000060000806000080600008060000806000080600008060000806000080600008060000c06006000⟩
]
private theorem rowsE_chunk044_length : rowsE_chunk044.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk044_score : batchScore 2724 rowsE_chunk044 = 643218939 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk048 : List Row := [
  ⟨438,104,0xc0000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b00000200000020000002000000200000020000002000000210000021800002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003200000330000034000003400000360000036000003800000400001840000204000020400002040000304000030400003040000304000040400004040000404000040400004044000004400000460000046000004800000480000048000004c000004c000004c000004c00000600008060000806000080600008060000806000080600008060000806000080600008060060006006000⟩,
  ⟨438,104,0x400000100000020000003000000340000044000005000000600000068000008000000840000090000009800000c000000c000000c400000d000000d80000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001b000002000000200000020000002000000200000020400002100000220000023000002400000240000026000002600000260000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000340000034000003600000360000036000004000018400002040000204000020400003040000304000030400003040000404000040400004040000404000040430000044000004600000460000046000004800000480000048000004c000004c000004c000004c0000060000806000080600008060000806000080600008060000806000080600008060000c06006000⟩,
  ⟨438,103,0x80000014000002000000300000040000004800000600000060000006c00000800000088000009000000c000000c000000c000000c800000d000001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000308000031800003200000330000034000003400000360000036000003800000400002040000204000020400003040000304000030400003040000404000040400004040000404000040400004044000004400000460000046000004800000480000048000004c000004c000004c000004c000004c000006000080600008060000806000080600008060000806000080600008060000c060000c0⟩,
  ⟨437,103,0xc0000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b00000200000020000002000000200000020000002040000210000022000002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003200000330000034000003600000360000036000003800000400002040000204000030400003040000304000030400004040000404000040400004040000404000040400006044000004400000460000046000004800000480000048000004c000004c000004c000004c0000060000806000080600008060000806000080600008060000806000080600008060000c060000c0⟩
]
private theorem rowsE_chunk048_length : rowsE_chunk048.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk048_score : batchScore 2728 rowsE_chunk048 = 634934112 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk052 : List Row := [
  ⟨437,103,0x40000010000002000000300000038000004400000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000340000034000003600000360000038000004000020400002040000204000030400003040000304000030400004040000404000040400004040000404000040400006044000004600000460000048000004800000480000048000004c000004c000004c000004c000006000080600008060000806000080600008060000806000080600008060000c060000c0⟩,
  ⟨437,102,0x80000018000002000000300000040000004800000600000060000006c00000800000088000009800000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000308000031800003200000330000034000003400000360000036000003800000400002040000204000030400003040000304000030400004040000404000040400004040000404000040400006044000004400000460000046000004800000480000048000004c000004c000004c000004c000006000080600008060000806000080600008060000806000080600008060000c060000c0⟩,
  ⟨436,102,0xc0000018000002400000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000018c000019800001b000001b000002000000200000020000002000000200000020400002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000310000031800003300000330000034000003600000360000036000004000020400002040000304000030400003040000304000040400004040000404000040400004040000404000060400006044000004600000460000046000004800000480000048000004c000004c000004c000004c00000600008060000806000080600008060000806000080600008060000c060000c060000c0⟩,
  ⟨436,102,0x40000010000002000000300000038000004400000600000060000006800000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001c00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000304000031000003200000330000034000003400000360000036000003800000400002040000304000030400003040000304000040400004040000404000040400004040000404000060400006040000604400000460000046000004800000480000048000004c000004c000004c000004c000006000080600008060000806000080600008060000806000080600008060000c060000c0⟩
]
private theorem rowsE_chunk052_length : rowsE_chunk052.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk052_score : batchScore 2732 rowsE_chunk052 = 626370242 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk056 : List Row := [
  ⟨436,101,0x80000018000002000000300000040000004800000600000060000007000000800000088000009800000c000000c000000c000000c800000d80000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020c000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030c000031800003200000330000034000003400000360000036000003800000400002040000304000030400003040000304000040400004040000404000040400004040000404000060400006040000604400000460000046000004800000480000048000004c000004c000004c000004c00000600008060000806000080600008060000806000080600008060000c060000c0⟩,
  ⟨435,101,0xc0000018000002800000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001b000002000000200000020000002000000200000020400002100000220000023000002400000240000026000002600000260000030000003000000300000030000003000000300000030000003000000300000030000003040000310000032000003300000340000034000003600000360000038000004000020400003040000304000030400003040000404000040400004040000404000040400004040000604000060400006044000004600000460000048000004800000480000048000004c000004c000004c000004c0000060000806000080600008060000806000080600008060000c060000c060000c0⟩,
  ⟨435,101,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000308000031800003200000330000034000003400000360000036000003800000400003040000304000030400003040000404000040400004040000404000040400004040000604000060400006040000604400000460000046000004800000480000048000004c000004c000004c000004c0000060000806000080600008060000806000080600008060000c060000c060000c0⟩,
  ⟨435,100,0x80000018000002400000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000c800000d80000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b00000200000020000002000000200000020000002000000210000021800002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000330c000031800003300000330000034000003600000360000036000004000030400003040000304000030400004040000404000040400004040000404000040400006040000604000060400006040000604600000460000046000004800000480000048000004c000004c000004c000004c0000060000806000080600008060000806000080600008060000c060000c0⟩
]
private theorem rowsE_chunk056_length : rowsE_chunk056.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk056_score : batchScore 2736 rowsE_chunk056 = 618007945 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk060 : List Row := [
  ⟨434,100,0xc000001c000002800000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001000000110000011800001300000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002080000210000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000002304000031000003200000330000034000003400000360000036000003800000400003040000304000030400003040000404000040400004040000404000040400004040000604000060400006040000604000060460000046000004800000480000048000004c000004c000004c000004c0000060000806000080600008060000806000080600008060000c060000c060000c0⟩,
  ⟨434,100,0x40000010000002000000300000040000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001080000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000013000006308000031800003200000330000034000003400000360000036000003800000400003040000304000030400004040000404000040400004040000404000040400006040000604000060400006040000604000060460000046000004800000480000048000004c000004c000004c000004c000006000080600008060000806000080600008060000c060000c060000c0⟩,
  ⟨434,99,0x80000018000002400000300000040000004800000600000064000008000000800000088000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b00000200000020000002000000200000020000002040000210000022000002300000230000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000004300000831000003200000330000034000003400000360000036000003600000400003040000304000030400004040000404000040400004040000404000040400006040000604000060400006040000604000060460000046000004800000480000048000004c000004c000004c000004c000006000080600008060000806000080600008060000c060000c060000c0⟩,
  ⟨433,99,0x10000001c000002800000340000040000005000000600000068000008000000800000090000009800000c000000c000000c000000d000000d80000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001c00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000033000008308000031800003200000330000034000003400000360000036000003800000400003040000304000040400004040000404000040400004040000404000060400006040000604000060400006040000604000060460000046000004800000480000048000004c000004c000004c000004c000006000080600008060000806000080600008060000c060000c060000c0⟩
]
private theorem rowsE_chunk060_length : rowsE_chunk060.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk060_score : batchScore 2740 rowsE_chunk060 = 609536511 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk064 : List Row := [
  ⟨433,99,0x40000014000002000000300000040000004400000600000060000006c00000800000084000009000000a000000c000000c000000c800000d000001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000023000006300000c30c000031800003200000330000034000003600000360000036000003800000400003040000304000040400004040000404000040400004040000404000060400006040000604000060400006040000604000060460000048000004800000480000048000004c000004c000004c000004c00000600008060000806000080600008060000c060000c060000c0⟩,
  ⟨433,98,0xc0000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000018c000019800001b000001b0000020000002000000200000020000002000000204000021000002200000230000024000002400000260000026000002600000300000030000003000000300000030000003000000300000030000013000006300000c3000010310000032000003300000340000034000003600000360000038000004000030400003040000404000040400004040000404000040400004040000604000060400006040000604000060400006040000604600000460000048000004800000480000040060004c000004c000004c00000600008060000806000080600008060000c060000c060000c0⟩,
  ⟨432,99,0x40000010000001c00000300000034000004400000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001c0000020000002000000200000020000002000000208000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000003000000300000030000043000008300000c30800003180000320000033000003400000340000036000003600000380000040000304000040400004040000404000040400004040000404000060400006040000604000060400006040000604000060400006040030004004000400400040040004006000400600040060004006000400600060000806000080600008060000c060000c060000c060000c0⟩,
  ⟨432,98,0x80000014000002000000300000040000004800000600000060000006c00000800000088000009000000c000000c000000c000000c800000d80000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000021000002180000230000023000002400000260000026000002600000280000030000003000000300000030000003000000300000030000033000008300000c300001030c00003180000330000033000003400000360000036000003600000400003040000404000040400004040000404000040400004040000604000060400006040000604000060400006040000604000060400300040030004004000400400040040004006000400600040060004006000600008060000806000080600008060000c060000c060000c0⟩
]
private theorem rowsE_chunk064_length : rowsE_chunk064.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk064_score : batchScore 2744 rowsE_chunk064 = 601260122 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk068 : List Row := [
  ⟨431,98,0xc0000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000019000001a000001b000001b000002000000200000020000002000000200000020400002100000220000023000002400000240000026000002600000280000030000003000000300000030000003000000300000030000023000006300000c300001030000103100000320000033000003400000340000036000003600000380000040000304000040400004040000404000040400004040000404000060400006040000604000060400006040000604000060400006040030004004000400400040040004006000400600040060004006000400800060000806000080600008060000c060000c060000c060000c0⟩,
  ⟨431,98,0x40000010000002000000300000038000004400000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000013000006300000c3000010300001030c0000318000032000003300000340000034000003600000360000038000004000040400004040000404000040400004040000404000060400006040000604000060400006040000604000060400006040030004003000400400040040004004000400600040060004006000400600060000806000080600008060000c060000c060000c060000c0⟩,
  ⟨431,97,0x80000018000002000000300000040000004800000600000060000006c00000800000088000009800000c000000c000000c000000c800000d80000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000002000000200000020000002000000200000020400002100000220000023000002300000240000026000002600000260000028000003000000300000030000003000000300000030000043000008300000c30000103000018310000032000003300000340000034000003600000360000038000004000040400004040000404000040400004040000404000060400006040000604000060400006040000604000060400006040000804003000400400040040004004000400600040060004006000400600040080006000080600008060000c060000c060000c060000c0⟩,
  ⟨430,97,0xc0000018000002400000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000033000008300000c300001030000183000018318000032000003300000340000034000003600000360000038000004000040400004040000404000040400004040000604000060400006040000604000060400006040000604000060400008040030004004000400400040040004004000400600040060004006000400600040080006000080600008060000c060000c060000c060000c0⟩
]
private theorem rowsE_chunk068_length : rowsE_chunk068.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk068_score : batchScore 2748 rowsE_chunk068 = 593509954 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk072 : List Row := [
  ⟨430,97,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000023000006300000c30000103000010300001830c000031800003300000330000034000003600000360000036000004000040400004040000404000040400004040000404000060400006040000604000060400006040000604000060400006040000804003000400400040040004004000400600040060004006000400600040080006000080600008060000c060000c060000c060000c0⟩,
  ⟨430,96,0x80000018000002000000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000002000000204000021000002200000230000024000002400000260000026000002600000300000030000003000000300000030000013000006300000c300001030000103000018300001831000003200000330000034000003400000360000036000003800000400004040000404000040400004040000404000060400006040000604000060400006040000604000060400006040000804003000400400040040004004000400600040060004006000400600040080004008000600008060000c060000c060000c060000c0⟩,
  ⟨429,96,0xc0000018000002800000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001000000110000011800001300000130000018000001800000180000018000001800000184000019000001a000001b000001c0000020000002000000200000020000002000000208000021800002200000230000024000002400000260000026000002800000300000030000003000000300000030000043000008300000c30000103000018300001830000203180000320000033000003400000340000036000003600000380000040000404000040400004040000404000060400006040000604000060400006040000604000060400006040000804000080400300040040004004000400400040060004006000400600040060004008000600008060000c060000c060000c060000c060000c0⟩,
  ⟨429,96,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001080000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c00002180000230000023000002400000260000026000002600000280000030000003000000300000030000033000008300000c300001030000183000018300002031000003200000330000034000003400000360000036000003800000400004040000404000040400004040000604000060400006040000604000060400006040000604000060400008040000804003000400400040040004004000400600040060004006000400600040080004008000600008060000c060000c060000c060000c0⟩
]
private theorem rowsE_chunk072_length : rowsE_chunk072.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk072_score : batchScore 2752 rowsE_chunk072 = 585586498 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk076 : List Row := [
  ⟨429,95,0x80000018000002400000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000180000018000001800000180000018000001800000190000019800001b000001b000002000000200000020000002000000200000020400002100000220000023000002400000240000026000002600000280000030000003000000300000030000023000006300000c300001030000103000018300001830000203180000320000033000003400000340000036000003600000380000040000404000040400004040000404000060400006040000604000060400006040000604000060400006040000804000080400400040040004004000400400040060004006000400600040060004008000600008060000c060000c060000c060000c0⟩,
  ⟨429,94,0xc000001c000002800000340000040000004c00000600000068000008000000800000090000009800000c000000c000000c400000d000000d80000100000010000001040000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000013000006300000c300001030000103000018300001830000203000020318000032000003300000340000036000003600000360000040000404000040400004040000404000060400006040000604000060400006040000604000060400006040000804000080400300040040004004000400400040060004006000400600040060004008000400800060000c060000c060000c060000c0⟩,
  ⟨428,95,0x40000014000002000000300000040000004400000600000060000006c00000800000084000009000000a000000c000000c000000c800000d00000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000002000000200000020000002000000200000020000002100000220000023000002300000240000026000002600000260000028000003000000300000030000043000008300000c300001030000183000018300002030000203100000320000033000003400000340000036000003600000380000040000404000040400004040000604000060400006040000604000060400006040000604000060400008040000804000080400400040040004004000400600040060004006000400600040060004008000400800060000c060000c060000c060000c0⟩,
  ⟨428,94,0x80000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001b00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000000300000030000033000008300000c300001030000183000018300002030000203000020318000032000003300000340000034000003600000360000038000004000040400004040000604000060400006040000604000060400006040000604000060400008040000804000080400300040040004004000400400040060004006000400600040060004008000400800060000c060000c060000c060000c0⟩
]
private theorem rowsE_chunk076_length : rowsE_chunk076.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk076_score : batchScore 2756 rowsE_chunk076 = 577439256 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk080 : List Row := [
  ⟨428,93,0x10000001c00000300000034000004000000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c000021800002200000230000024000002400000260000026000002800000300000030000023000006300000c3000010300001030000183000018300002030000203000020318000033000003300000340000036000003600000380000040000404000040400004040000604000060400006040000604000060400006040000604000060400008040000804000080400400040040004004000400600040060004006000400600040080004008000400800060000c060000c060000c0⟩,
  ⟨427,94,0x40000014000002000000300000040000004800000600000060000006c00000800000088000009000000c000000c000000c000000c800000d80000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000002000000204000021000002200000230000024000002400000260000026000002600000300000030000013000006300000c3000010300001030000183000018300002030000203000020310000032000003300000340000034000003600000360000038000004000040400004040000604000060400006040000604000060400006040000604000060400008040000804000080400400040040004004000400400040060004006000400600040060004008000400800060000c060000c060000c060000c0⟩,
  ⟨427,93,0xc0000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c0000020000002000000200000020000002000000208000021800002200000230000024000002400000260000026000002800000300000030000043000008300000c3000010300001830000183000020300002030000203000030318000032000003300000340000036000003600000360000040000404000040400006040000604000060400006040000604000060400006040000604000080400008040000804000080400400040040004004000400600040060004006000400600040080004008000400800060000c060000c060000c0⟩,
  ⟨427,93,0x40000010000002000000300000034000004400000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c00002180000230000023000002400000260000026000002600000280000030000033000008300000c3000010300001830000183000020300002030000203000030300003032000003300000340000034000003600000360000038000004000040400006040000604000060400006040000604000060400006040000604000080400008040000804000080400400040040004004000400600040060004006000400600040060004008000400800060000c060000c060000c0⟩
]
private theorem rowsE_chunk080_length : rowsE_chunk080.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk080_score : batchScore 2760 rowsE_chunk080 = 569591105 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk084 : List Row := [
  ⟨426,93,0x80000014000002000000300000040000004800000600000060000007000000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000002000000200000020000002000000200000020400002100000220000023000002400000240000026000002600000280000030000023000006300000c30000103000010300001830000183000020300002030000203000030300003032000003300000340000034000003600000360000038000004000040400006040000604000060400006040000604000060400006040000604000080400008040000804000080400400040040004004000400600040060004006000400600040080004008000400800060000c060000c060000c0⟩,
  ⟨426,92,0xc0000018000002400000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001000000110000011800001300000130000018000001800000180000018000001800000184000019000001a000001b000001c00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000006300000c300001030000103000018300001830000203000020300002030000303000030318000033000003300000340000036000003600000360000040000404000060400006040000604000060400006040000604000060400006040000804000080400008040000804004000400400040040004006000400600040060004006000400800040080004008000400800060000c060000c0⟩,
  ⟨426,92,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001080000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c00000200000020000002000000200000020000002100000220000023000002300000240000026000002600000260000028000003000008300000c30000103000018300001830000203000020300002030000303000030300003032000003300000340000034000003600000360000038000004000060400006040000604000060400006040000604000060400006040000804000080400008040000804000080400400040040004004000400600040060004006000400600040080004008000400800060000c060000c0⟩,
  ⟨425,92,0x80000018000002000000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000180000019000001a000001b000001b00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000008300000c300001030000183000018300002030000203000020300003030000303000030300003032000003300000340000036000003600000360000040000604000060400006040000604000060400006040000604000060400008040000804000080400008040000804004000400400040040004006000400600040060004006000400800040080004008000400800060000c060000c0⟩
]
private theorem rowsE_chunk084_length : rowsE_chunk084.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk084_score : batchScore 2764 rowsE_chunk084 = 562101687 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk088 : List Row := [
  ⟨425,91,0xc0000018000002800000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000d000000d80000100000010000001040000110000012000001300000130000018000001800000180000018000001800000188000019000001a000001b000001c000002000000200000020000002000000200000020c000021800002200000230000024000002400000260000026000002800000300000c300001030000103000018300001830000203000020300002030000303000030300003032000003300000340000034000003600000360000038000004000060400006040000604000060400006040000604000060400006040000804000080400008040000804000080400400040040004006000400600040060004006000400600040080004008000400800060000c060000c0⟩,
  ⟨425,91,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c800000d00000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000002000000204000021000002200000230000024000002400000260000026000002600000300000c3000010300001030000183000018300002030000203000020300003030000303000030300003032000003300000340000034000003600000360000038000004000060400006040000604000060400006040000604000060400008040000804000080400008040000804004000400400040040004006000400600040060004006000400800040080004008000400800060000c0⟩,
  ⟨424,91,0x8000001800000240000030000004000000480000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c0000020000002000000200000020000002000000208000021800002200000230000024000002400000260000026000002800000300000c300001030000183000018300002030000203000020300003030000303000030300003030000403300000330000034000003600000360000036000004000060400006040000604000060400006040000604000060400008040000804000080400008040000804000080400400040040004006000400600040060004006000400600040080004008000400800060000c060000c0⟩,
  ⟨424,90,0xc000001c000002800000340000040000004c00000600000068000008000000800000090000009800000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c0000218000023000002300000240000026000002600000260000028000003000010300001830000183000020300002030000203000030300003030000303000030300004030000403300000340000034000003600000360000038000004000060400006040000604000060400006040000604000080400008040000804000080400008040000804004000400400040040004006000400600040060004006000400800040080004008000400800060000c0⟩
]
private theorem rowsE_chunk088_length : rowsE_chunk088.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk088_score : batchScore 2768 rowsE_chunk088 = 554093546 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk092 : List Row := [
  ⟨424,90,0x40000010000002000000300000040000004400000600000060000006c00000800000088000009000000c000000c000000c000000c800000d80000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b00000200000020000002000000200000020000002040000210000022000002300000240000024000002600000260000028000003000010300001030000183000018300002030000203000020300003030000303000030300003030000403200000330000034000003400000360000036000003800000400006040000604000060400006040000604000060400008040000804000080400008040000804000080400400040040004006000400600040060004006000400800040080004008000400800060000c0⟩,
  ⟨423,90,0x80000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001300000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000010300001830000183000020300002030000203000030300003030000303000030300004030000403300000340000034000003600000360000038000004000060400006040000604000060400006040000604000080400008040000804000080400008040000804004000400400040040004006000400600040060004006000400800040080004008000400800060000c0⟩,
  ⟨423,89,0x10000001c00000300000034000004000000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000021000002200000230000023000002400000260000026000002600000280000030000183000018300002030000203000020300003030000303000030300003030000403000040300004033000003400000340000036000003600000380000040000604000060400006040000604000060400008040000804000080400008040000804000080400400040040004004000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨423,89,0x40000014000002000000300000040000004800000600000060000006c00000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000190000019800001b000001b000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000280000030000183000018300002030000203000020300003030000303000030300003030000403000040300004032000003300000340000036000003600000360000040000604000060400006040000604000060400008040000804000080400008040000804000080400008040040004004000400600040060004006000400600040060004008000400800040080004008000⟩
]
private theorem rowsE_chunk092_length : rowsE_chunk092.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk092_score : batchScore 2772 rowsE_chunk092 = 546359698 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk096 : List Row := [
  ⟨422,89,0xc0000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001000000110000012000001300000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000280000030000183000018300002030000203000020300003030000303000030300003030000403000040300004033000003400000340000036000003600000380000040000604000060400006040000604000060400008040000804000080400008040000804000080400400040040004004000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨422,89,0x40000010000002000000300000034000004400000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e0000010000001000000108000011000001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000002000000200000020000002000000200000020400002100000220000023000002400000240000026000002600000280000030000183000018300002030000203000020300003030000303000030300003030000403000040300004030000403300000340000034000003600000360000038000004000060400006040000604000060400008040000804000080400008040000804000080400008040040004004000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨421,89,0x80000014000002000000300000040000004800000600000060000007000000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001b000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000280000030000183000020300002030000203000030300003030000303000030300004030000403000040300004033000003400000340000036000003600000380000040000604000060400006040000604000080400008040000804000080400008040000804000080400400040040004004000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨421,88,0xc0000018000002400000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000d000000d80000100000010000001040000110000012000001300000130000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c0000218000023000002300000240000026000002600000260000028000003000020300002030000203000030300003030000303000030300004030000403000040300004030000403300000340000034000003600000360000038000004000060400006040000604000080400008040000804000080400008040000804000080400008040040004004000400600040060004006000400600040080004008000400800040080004008000⟩
]
private theorem rowsE_chunk096_length : rowsE_chunk096.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk096_score : batchScore 2776 rowsE_chunk096 = 538913988 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk100 : List Row := [
  ⟨420,89,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c800000d00000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000002000000200000020000002000000200000020400002100000220000023000002400000240000026000002600000280000030000183000020300002030000203000030300003030000303000030300004030000403000040300004030000403300000340000036000003600000360000040000604000060400006040000604000080400008040000804000080400008040000804000080400400040040004006000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨420,88,0x80000018000002000000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000020300002030000203000030300003030000303000030300004030000403000040300004030000403000040340000034000003600000360000038000004000060400006040000604000080400008040000804000080400008040000804000080400008040040004004000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨420,87,0xc0000018000002800000340000040000004c00000600000068000008000000800000090000009800000c000000c000000c400000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c0000020000002000000200000020000002000000210000022000002300000240000024000002600000260000026000003000020300002030000203000030300003030000303000030300004030000403000040300004030000403000040330000034000003400000360000036000003800000400006040000604000080400008040000804000080400008040000804000080400008040040004004000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨419,88,0x40000010000002000000300000040000004400000600000060000006c00000800000088000009000000c000000c000000c000000c800000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000190000019800001b000001b00000200000020000002000000200000020000002080000218000022000002300000240000024000002600000260000028000003000020300002030000303000030300003030000303000040300004030000403000040300004030000403000060340000034000003600000360000038000004000060400006040000804000080400008040000804000080400008040000804000080400008040040004004000400600040060004006000400600040080004008000400800040080004008000⟩
]
private theorem rowsE_chunk100_length : rowsE_chunk100.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk100_score : batchScore 2780 rowsE_chunk100 = 530896644 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk104 : List Row := [
  ⟨419,87,0x8000001800000240000030000004000000480000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001000000110000011800001300000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000000200000020c000021800002200000230000024000002600000260000026000002800000300002030000203000030300003030000303000030300004030000403000040300004030000403000040300006034000003400000360000036000003800000400006040000604000080400008040000804000080400008040000804000080400008040040004004000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨418,87,0xc000001c00000280000034000004000000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e0000010000001000000104000011000001200000130000014000001800000180000018000001800000180000018c000019800001a000001b00000200000020000002000000200000020000002040000210000022000002300000240000024000002600000260000028000003000020300002030000303000030300003030000303000040300004030000403000040300004030000403000060300006034000003600000360000036000004000060400006040000804000080400008040000804000080400008040000804000080400008040040004006000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨418,87,0x40000014000002000000300000040000004800000600000060000006c00000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000208000021800002200000230000024000002400000260000026000002800000300002030000303000030300003030000303000040300004030000403000040300004030000403000060300006034000003400000360000036000003800000400006040000804000080400008040000804000080400008040000804000080400008040040004004000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨417,87,0x80000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001040000110000012000001300000130000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020c000021800002300000230000024000002600000260000026000002800000300003030000303000030300003030000403000040300004030000403000040300004030000603000060300006034000003400000360000036000004000060400008040000804000080400008040000804000080400008040000804000080400008040040004006000400600040060004006000400600040080004008000400800040080004008000⟩
]
private theorem rowsE_chunk104_length : rowsE_chunk104.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk104_score : batchScore 2784 rowsE_chunk104 = 523119238 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk108 : List Row := [
  ⟨417,86,0x10000001c00000300000034000004400000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e0000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000002000000204000021000002200000230000024000002400000260000026000002800000300002030000303000030300003030000303000040300004030000403000040300004030000403000060300006030000603400000360000036000003800000400006040000804000080400008040000804000080400008040000804000080400008040040004004000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨416,87,0x80000014000002000000300000040000004800000600000060000007000000800000088000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000000200000120c000021800002200000230000024000002400000260000026000002800000300003030000303000030300003030000403000040300004030000403000040300004030000603000060300006030000603400000360000036000003800000400008040000804000080400008040000804000080400008040000804000080400400040040004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨416,86,0xc0000018000002400000300000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000d000000e00000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000204000021000002200000230000024000002400000260000026000002800000300003030000303000030300003030000403000040300004030000403000040300004030000603000060300006030000603400000360000036000003600000400008040000804000080400008040000804000080400008040000804000080400008040040004006000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨415,87,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c800000d00000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001b000001b0000020000002000000200000020000002000003208000021800002200000230000024000002400000260000026000002800000300003030000303000030300004030000403000040300004030000403000040300006030000603000060300006030000603400000360000036000003800000400008040000804000080400008040000804000080400008040000804000080400400040040004006000400600040060004006000400800040080004008000400800040080004008000⟩
]
private theorem rowsE_chunk108_length : rowsE_chunk108.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk108_score : batchScore 2788 rowsE_chunk108 = 515614985 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk112 : List Row := [
  ⟨415,86,0x80000018000002000000300000040000004800000600000064000007000000800000088000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001300000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000002200000620c00002180000230000023000002400000260000026000002600000280000030000303000030300003030000403000040300004030000403000040300004030000603000060300006030000603000060340000036000003600000400008040000804000080400008040000804000080400008040000804000080400008040040004006000400600040060004006000400600040080004008000400800040080004008000⟩,
  ⟨414,86,0xc0000018000002800000340000040000004c00000600000068000008000000800000090000009800000c000000c000000c400000d000000e0000010000001000000104000011000001200000130000014000001800000180000018000001800000180000018c000019800001a000001b0000020000002000000200000020000012000006204000021000002200000230000024000002400000260000026000002800000300003030000303000030300004030000403000040300004030000403000040300006030000603000060300006030000603400000360000036000003800000400008040000804000080400008040000804000080400008040000804000080400400040040004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨414,86,0x40000010000002000000300000038000004400000600000060000006c00000800000088000009000000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000000200000020000002000004200000820800002180000220000023000002400000240000026000002600000280000030000303000030300004030000403000040300004030000403000040300006030000603000060300006030000603000060340000036000003600000380000040000804000080400008040000804000080400008040000804000080400008040040004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨413,86,0x8000001800000240000030000004000000480000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001000000110000012000001300000130000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000032000008200000c21000002200000230000023000002400000260000026000002600000300003030000303000040300004030000403000040300004030000403000060300006030000603000060300006030000603000060360000036000003600000400008040000804000080400008040000804000080400008040000804000080400400040060004006000400600040060004006000400800040080004008000400800040080004008000⟩
]
private theorem rowsE_chunk112_length : rowsE_chunk112.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk112_score : batchScore 2792 rowsE_chunk112 = 508070975 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk116 : List Row := [
  ⟨413,85,0xc000001c00000280000034000004000000500000060000006800000800000084000009000000a000000c000000c000000c400000d000000e0000010000001000000108000011000001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000002000000200000020000022000006200000c20800002100000220000023000002400000240000026000002600000280000030000303000030300004030000403000040300004030000403000040300006030000603000060300006030000603000060300006036000003600000380000040000804000080400008040000804000080400008040000804000080400008040040004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨412,86,0x40000010000002000000300000040000004800000600000060000006c00000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c00000200000020000012000006200000c200001020c00002180000220000023000002400000260000026000002600000280000030000303000040300004030000403000040300004030000403000060300006030000603000060300006030000603000060340000036000003600000400008040000804000080400008040000804000080400008040000804000080400400040060004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨412,85,0x80000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000d000000d80000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c00000200000020000042000008200000c20000102100000220000023000002400000240000026000002600000280000030000303000040300004030000403000040300004030000403000060300006030000603000060300006030000603000060300006036000003600000380000040000804000080400008040000804000080400008040000804000080400008040060004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨412,84,0x10000001c00000300000034000004400000500000060000006800000800000084000009000000a000000c000000c000000c400000d00000100000010000001000000108000011800001200000130000014000001800000180000018000001800000180000018c000019800001b000001b00000200000020000032000008200000c20000102080000218000022000002300000240000024000002600000260000028000003000040300004030000403000040300004030000403000060300006030000603000060300006030000603000060300006030000803600000360000038000004000080400008040000804000080400008040000804000080400008040040004006000400600040060004006000400800040080004008000400800040080004008000⟩
]
private theorem rowsE_chunk116_length : rowsE_chunk116.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk116_score : batchScore 2796 rowsE_chunk116 = 500320275 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk120 : List Row := [
  ⟨411,85,0x40000014000002000000300000040000004800000600000060000007000000800000088000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c0000020000022000006200000c2000010200001020c0000218000023000002300000240000026000002600000260000030000303000040300004030000403000040300004030000403000060300006030000603000060300006030000603000060300006030000803600000380000040000804000080400008040000804000080400008040000804000080400008040060004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨411,84,0xc0000018000002400000300000040000004c0000060000006800000800000080000008c000009800000c000000c000000c400000d000000e0000010000001000000104000011000001200000130000014000001800000180000018000001800000180000018c000019800001a000001b0000020000012000006200000c200001020000102000018210000022000002300000240000024000002600000260000028000003000040300004030000403000040300004030000403000060300006030000603000060300006030000603000060300006030000803600000360000038000004000080400008040000804000080400008040000804000080400008040040004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨410,85,0x40000010000002000000300000038000004400000600000060000006c00000800000084000009000000a000000c000000c000000c800000d80000100000010000001000000108000011800001200000130000014000001800000180000018000001800000184000019000001a000001b000001c0000020000042000008200000c2000010200001820c0000218000022000002300000240000024000002600000260000028000003000040300004030000403000040300004030000603000060300006030000603000060300006030000603000060300008030000803600000360000040000804000080400008040000804000080400008040000804000080400400040060004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨410,84,0x8000001800000200000030000004000000480000060000006400000700000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001000000110000012000001300000130000018000001800000180000018000001800000188000019800001a000001b000001c000002000008200000c200001020000182000018210000022000002300000240000024000002600000260000028000003000040300004030000403000040300004030000603000060300006030000603000060300006030000603000060300008030000803000080360000038000004000080400008040000804000080400008040000804000080400008040060004006000400600040060004006000400800040080004008000400800040080004008000⟩
]
private theorem rowsE_chunk120_length : rowsE_chunk120.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk120_score : batchScore 2800 rowsE_chunk120 = 492373720 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk124 : List Row := [
  ⟨409,84,0xc0000018000002800000340000040000004c0000060000006800000800000080000009000000a000000c000000c000000c400000d000000e0000010000001000000108000011000001200000130000014000001800000180000018000001800000180000018c000019800001a000001b000002000006200000c200001020000102000018200001821800002200000230000024000002400000260000026000002800000300004030000403000040300004030000403000060300006030000603000060300006030000603000060300006030000803000080300008036000003800000400008040000804000080400008040000804000080400008040000c040060004006000400600040060004008000400800040080004008000400800040080004008000⟩,
  ⟨409,84,0x40000010000002000000300000038000004400000600000060000006c00000800000088000009000000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c00000200000c200001020000102000018200001820c00002180000220000023000002400000260000026000002600000280000030000403000040300004030000403000060300006030000603000060300006030000603000060300006030000803000080300008036000003800000400008040000804000080400008040000804000080400008040000c040060004006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨408,84,0x8000001800000240000030000004000000480000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000002000008200000c20000102000018200001820000202100000220000023000002400000240000026000002600000280000030000403000040300004030000403000060300006030000603000060300006030000603000060300006030000803000080300008030000803600000380000040000804000080400008040000804000080400008040000c040000c040060004006000400600040060004008000400800040080004008000400800040080004008000⟩,
  ⟨408,83,0xc000001c00000280000034000004000000500000060000006800000800000084000009000000a000000c000000c000000c400000d000001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000190000019800001b000001b00000200000c200001020000182000018200002020000202180000220000023000002400000240000026000002600000280000030000403000040300004030000603000060300006030000603000060300006030000603000060300008030000803000080300008030000803600000400008040000804000080400008040000804000080400008040000c040060004006000400600040060004006000400800040080004008000400800040080004008000⟩
]
private theorem rowsE_chunk124_length : rowsE_chunk124.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk124_score : batchScore 2804 rowsE_chunk124 = 485075901 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk128 : List Row := [
  ⟨407,84,0x40000010000002000000300000040000004800000600000060000006c00000800000088000009800000c000000c000000c000000cc00000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c00000200001020000102000018200001820000202100000220000023000002300000240000026000002600000260000030000403000040300004030000403000060300006030000603000060300006030000603000060300006030000803000080300008030000803000080380000040000804000080400008040000804000080400008040000c040000c04006000400600040060004006000400800040080004008000400800040080004008000400c000⟩,
  ⟨407,83,0x80000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000d000000e0000010000001000000104000011000001200000130000014000001800000180000018000001800000180000018c000019800001a000001b00000200001020000102000018200001820000202000020210000022000002300000240000024000002600000260000028000003000040300004030000403000060300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008038000004000080400008040000804000080400008040000c040000c040060004006000400600040060004008000400800040080004008000400800040080004008000⟩,
  ⟨407,82,0x10000001c00000300000034000004400000500000060000006c00000800000084000009000000a000000c000000c000000c800000d80000100000010000001000000108000011800001200000130000014000001800000180000018000001800000184000019000001a000001b000001c0000020000102000018200001820000202000020200002021800002200000230000024000002600000260000026000002800000300004030000403000060300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008030040004000080400008040000804000080400008040000c040000c040000c04006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨406,83,0x40000014000002000000300000040000004800000600000060000007000000800000088000009800000c000000c000000c000000cc00000d80000100000010000001000000110000011800001300000130000018000001800000180000018000001800000188000019800001a000001b000001c0000020000182000018200002020000202000020210000022000002300000240000024000002600000260000028000003000040300004030000603000060300006030000603000060300006030000603000060300008030000803000080300008030000803000080300008030040004000080400008040000804000080400008040000c040000c040060004006000400600040060004008000400800040080004008000400800040080004008000⟩
]
private theorem rowsE_chunk128_length : rowsE_chunk128.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk128_score : batchScore 2808 rowsE_chunk128 = 477301420 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk132 : List Row := [
  ⟨406,82,0xc0000018000002400000340000040000004c00000600000068000008000000800000090000009800000c000000c000000c400000d000000e0000010000001000000108000011000001200000130000014000001800000180000018000001800000180000018c000019800001b000001b0000020000102000018200001820000202000020200002021800002200000230000024000002400000260000026000002800000300004030000403000060300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008030040004000080400008040000804000080400008040000c040000c040000c04006000400600040060004006000400800040080004008000400800040080004008000⟩,
  ⟨405,83,0x40000010000002000000300000038000004400000600000060000006c00000800000088000009000000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800000184000019000001a000001b000001c000002000018200001820000202000020200002020000302180000230000023000002400000260000026000002600000300004030000403000060300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008030000803004000400008040000804000080400008040000c040000c040000c04006000400600040060004006000400800040080004008000400800040080004008000400c000⟩,
  ⟨405,82,0x8000001800000200000030000004000000480000060000006400000800000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001040000110000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000002000018200001820000202000020200002020000302000030220000023000002400000240000026000002600000280000030000403000060300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008030000803004000400008040000804000080400008040000c040000c040000c040000c04006000400600040060004008000400800040080004008000400800040080004008000⟩,
  ⟨404,82,0xc0000018000002800000340000040000004c0000060000006800000800000084000009000000a000000c000000c000000c400000d000000e0000010000001000000108000011800001200000130000014000001800000180000018000001800000180000319000001a000001b000001b000002000018200002020000202000020200003020000302180000220000023000002400000260000026000002600000280000030000603000060300006030000603000060300006030000603000060300008030000803000080300008030000803000080300008030040003004000400008040000804000080400008040000c040000c040000c04006000400600040060004006000400800040080004008000400800040080004008000400c000⟩
]
private theorem rowsE_chunk132_length : rowsE_chunk132.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk132_score : batchScore 2812 rowsE_chunk132 = 469614928 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk136 : List Row := [
  ⟨404,82,0x40000010000002000000300000040000004400000600000060000006c00000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000018000001800000180000018000001800002188000019000001a000001b000001c00000200001820000202000020200002020000302000030220000023000002400000240000026000002600000280000030000403000060300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008030000803004000300400040000804000080400008040000c040000c040000c040000c04006000400600040060004008000400800040080004008000400800040080004008000⟩,
  ⟨403,82,0x80000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000d000000e0000010000001000000104000011000001200000130000014000001800000180000018000001800001180000618c000019800001a000001b00000200001820000202000020200002020000302000030200003022000002300000240000024000002600000260000028000003000060300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008030000803004000300400040000804000080400008040000c040000c040000c040000c04006000400600040060004008000400800040080004008000400800040080004008000400c000⟩,
  ⟨403,81,0xc000001c00000280000034000004000000500000060000006800000800000084000009000000a000000c000000c000000c800000d00000100000010000001000000108000011800001200000130000018000001800000180000018000001800004184000019000001a000001b000001c0000020000202000020200002020000302000030200003021800002300000230000024000002600000260000026000003000060300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008030000803000080300400030040004000080400008040000c040000c040000c040000c040000c0400600040060004006000400800040080004008000400800040080004008000400c000⟩,
  ⟨402,82,0x40000014000002000000300000040000004800000600000060000007000000800000088000009800000c000000c000000c000000cc00000d80000100000010000001000000110000011800001300000130000018000001800000180000018000031800008188000019800001a000001b000001c0000020000202000020200003020000302000030200003022000002300000240000024000002600000260000028000003000060300006030000603000060300006030000603000060300008030000803000080300008030000803000080300008030000803004000300400040000804000080400008040000c040000c040000c040000c04006000400600040060004008000400800040080004008000400800040080004008000400c000⟩
]
private theorem rowsE_chunk136_length : rowsE_chunk136.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk136_score : batchScore 2816 rowsE_chunk136 = 462414700 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk140 : List Row := [
  ⟨402,81,0x80000018000002400000300000040000004c0000060000006800000800000080000008c000009800000c000000c000000c400000d000000e0000010000001000000108000011000001200000130000014000001800000180000018000021800006180000c18c000019800001b000001b0000020000202000020200002020000302000030200003020000302200000230000024000002400000260000026000002800000300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008030000803000080300400030040004000080400008040000c040000c040000c040000c040000c0400600040060004006000400800040080004008000400800040080004008000400c000⟩,
  ⟨402,80,0x10000001c00000300000038000004400000600000060000006c00000800000084000009000000c000000c000000c000000c800000d8000010000001000000100000010c00001180000120000013000001800000180000018000011800006180000c184000019000001a000001b000001c000002000020200002020000302000030200003020000302200000230000024000002400000260000026000002800000300006030000603000060300006030000603000060300006030000803000080300008030000803000080300008030000803000080300400030040003004000400008040000c040000c040000c040000c040000c04006000400600040060004008000400800040080004008000400800040080004008000⟩,
  ⟨401,81,0x8000001400000200000030000004000000480000060000006400000700000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000104000011000001200000130000014000001800000180000018000041800008180000c18c000019800001a000001b000002000020200002020000302000030200003020000302000040220000023000002400000240000026000002600000280000030000603000060300006030000603000060300006030000803000080300008030000803000080300008030000803000080300008030040003004000400008040000c040000c040000c040000c040000c040000c0400600040060004008000400800040080004008000400800040080004008000400c000⟩,
  ⟨401,80,0xc0000018000002400000340000040000004c0000060000006800000800000084000009000000a000000c000000c000000c400000d000000e000001000000100000010800001180000120000013000001400000180000018000031800008180000c180001019000001a000001b000001c000002000020200003020000302000030200003020000402000040220000023000002400000260000026000002600000300006030000603000060300006030000603000060300008030000803000080300008030000803000080300008030000803000080300400030040003004000400008040000c040000c040000c040000c040000c0400600040060004006000400800040080004008000400800040080004008000400c000⟩
]
private theorem rowsE_chunk140_length : rowsE_chunk140.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk140_score : batchScore 2820 rowsE_chunk140 = 454435309 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk144 : List Row := [
  ⟨400,81,0x40000010000002000000300000038000004400000600000060000006c00000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c0000118000012000001300000180000018000021800006180000c1800010188000019800001a000001b000001c00000200002020000302000030200003020000302000040200004023000002400000240000026000002600000280000030000603000060300006030000603000060300006030000803000080300008030000803000080300008030000803000080300008030040003004000400008040000c040000c040000c040000c040000c040000c0400600040060004008000400800040080004008000400800040080004008000400c000⟩,
  ⟨400,80,0x8000001800000200000030000004000000480000060000006400000800000080000008c000009800000c000000c000000c000000d000000e00000100000010000001040000110000012000001300000140000018000011800006180000c1800010180001018c000019800001a000001b00000200002020000302000030200003020000302000040200004022000002300000240000024000002600000260000028000003000060300006030000603000060300006030000803000080300008030000803000080300008030000803000080300008030040003004000300600040000c040000c040000c040000c040000c040000c0400600040060004006000400800040080004008000400800040080004008000400c000⟩,
  ⟨399,80,0xc000001800000280000034000004000000500000060000006800000800000084000009000000a000000c000000c000000c800000d000001000000100000010000001080000118000012000001300000180000018000041800008180000c1800010180001819000001a000001b000001c00000200003020000302000030200003020000402000040200004023000002400000240000026000002600000280000030000603000060300006030000603000060300008030000803000080300008030000803000080300008030000803000080300400030040003004000300600040000c040000c040000c040000c040000c040000c0400600040060004008000400800040080004008000400800040080004008000400c000⟩,
  ⟨399,80,0x40000010000002000000300000040000004800000600000060000006c00000800000088000009800000c000000c000000c000000cc00000d80000100000010000001000000110000012000001300000130000018000031800008180000c18000101800018188000019800001a000001b00000200003020000302000030200003020000402000040200004020000402300000240000024000002600000260000028000003000060300006030000603000060300008030000803000080300008030000803000080300008030000803000080300008030040003004000300600040000c040000c040000c040000c040000c040000c0400600040060004008000400800040080004008000400800040080004008000400c000⟩
]
private theorem rowsE_chunk144_length : rowsE_chunk144.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk144_score : batchScore 2824 rowsE_chunk144 = 447436622 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk148 : List Row := [
  ⟨398,80,0x80000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c400000d000000e0000010000001000000108000011000001200000130000014000001800006180000c18000101800010180001819000001a000001b000001b00000200003020000302000030200003020000402000040200004022000002300000240000026000002600000260000030000603000060300006030000603000060300008030000803000080300008030000803000080300008030000803000080300400030040003004000300600040000c040000c040000c040000c040000c040000c040060004006000400800040080004008000400800040080004008000400c000400c000⟩,
  ⟨398,79,0xc000001c00000300000034000004400000600000060000006c00000800000084000009000000c000000c000000c000000c800000d8000010000001000000100000010c00001180000120000013000001800006180000c180001018000101800018180001819000001a000001b000001c0000020000302000030200003020000402000040200004020000402300000240000024000002600000260000028000003000060300006030000603000060300008030000803000080300008030000803000080300008030000803000080300008030040003004000300600040000c040000c040000c040000c040000c040000c0400600040060004008000400800040080004008000400800040080004008000400c000⟩,
  ⟨398,79,0x4000001400000200000030000004000000480000060000006400000700000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000104000011000001200000130000014000001800008180000c18000101800018180001818c000019800001a000001b00000200003020000302000030200004020000402000040200004020000402300000240000024000002600000260000028000003000060300006030000603000080300008030000803000080300008030000803000080300008030000803000080300400030040003006000300600040000c040000c040000c040000c040000c040000c040060004006000400800040080004008000400800040080004008000400c000⟩,
  ⟨397,79,0xc0000018000002400000340000040000004c0000060000006800000800000080000009000000a000000c000000c000000c400000d000000e000001000000100000010800001180000120000013000001400000180000c180001018000181800018180002019000001a000001b000001c0000020000302000030200004020000402000040200004020000402300000230000024000002600000260000028000003000060300006030000603000080300008030000803000080300008030000803000080300008030000803000080300008030040003004000300600040000c040000c040000c040000c040000c040000c0400600040060004008000400800040080004008000400800040080004008000400c000⟩
]
private theorem rowsE_chunk148_length : rowsE_chunk148.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk148_score : batchScore 2828 rowsE_chunk148 = 439961080 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk152 : List Row := [
  ⟨397,78,0x10000002000000300000038000004400000600000060000006c00000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000010c0000118000013000001300000180000c1800010180001018000181800018180002019800001a000001b00000200003020000302000030200004020000402000040200004020000402300000240000024000002600000260000028000003000060300006030000603000080300008030000803000080300008030000803000080300008030000803000080300400030040003006000300600040000c040000c040000c040000c040000c040000c040060004008000400800040080004008000400800040080004008000400c000⟩,
  ⟨396,79,0x8000001800000200000030000004000000480000060000006400000800000080000008c000009800000c000000c000000c000000d000000e0000010000001000000104000011000001200000130000014000001800010180001018000181800018180002018c000019800001b000001b00000200003020000302000040200004020000402000040200004020000402300000240000026000002600000260000030000603000060300006030000803000080300008030000803000080300008030000803000080300008030000803000080300400030040003006000300600040000c040000c040000c040000c040000c040060004006000400800040080004008000400800040080004008000400c000400c000⟩,
  ⟨396,78,0xc000001800000280000034000004000000500000060000006800000800000084000009000000a000000c000000c000000c800000d000001000000100000010000001080000118000012000001300000180000c1800010180001818000181800020180002019000001a000001b000001c0000020000302000040200004020000402000040200004020000402000060240000024000002600000260000028000003000060300006030000803000080300008030000803000080300008030000803000080300008030000803000080300400030040003006000300600040000c040000c040000c040000c040000c040000c040060004008000400800040080004008000400800040080004008000400c000⟩,
  ⟨395,79,0x40000010000002000000300000040000004400000600000060000006c00000800000088000009800000c000000c000000c000000cc00000d80000100000010000001000000110000012000001300000130000018000101800018180001818000201800020180002019800001a000001b00000200003020000402000040200004020000402000040200004020000602300000240000024000002600000260000028000003000060300008030000803000080300008030000803000080300008030000803000080300008030000803000080300400030060003006000300600040000c040000c040000c040000c040000c040060004008000400800040080004008000400800040080004008000400c000400c000⟩
]
private theorem rowsE_chunk152_length : rowsE_chunk152.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk152_score : batchScore 2832 rowsE_chunk152 = 432578269 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk156 : List Row := [
  ⟨395,78,0x80000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c400000d000000e0000010000001000000108000011800001200000130000014000001800010180001818000181800020180002019000001a000001b000001c0000020000302000040200004020000402000040200004020000402000060230000024000002600000260000028000003000060300006030000803000080300008030000803000080300008030000803000080300008030000803000080300400030040003006000300600040000c040000c040000c040000c040000c040000c040060004008000400800040080004008000400800040080004008000400c000⟩,
  ⟨394,78,0xc000001c00000280000034000004400000500000060000006c00000800000084000009000000a000000c000000c000000c800000d8000010000001000000100000010c000011800001200000130000018000101800018180001818000201800020180002019800001a000001b000001c0000020000402000040200004020000402000040200004020000602000060240000024000002600000260000028000003000060300008030000803000080300008030000803000080300008030000803000080300008030000803000080300400030060003006000300600040000c040000c040000c040000c040000c040060004008000400800040080004008000400800040080004008000400c000400c000⟩,
  ⟨394,78,0x4000001400000200000030000004000000480000060000006000000700000080000008c000009800000c000000c000000c000000cc00000d80000100000010000001040000110000012000001300000140000018000181800018180002018000201800020180003019800001a000001b00000200004020000402000040200004020000402000040200006020000602000060240000026000002600000260000030000603000080300008030000803000080300008030000803000080300008030000803000080300008030000803004000300400030060003006000300600040000c040000c040000c040000c040000c04006000400800040080004008000400800040080004008000400c000400c000⟩,
  ⟨394,77,0x80000018000002400000300000040000004c0000060000006800000800000080000009000000a000000c000000c000000c400000d00000100000010000001000000108000011800001200000130000014000001800018180002018000201800020180003018000301a000001b000001c0000020000402000040200004020000402000040200006020000602000060240000024000002600000260000028000003000080300008030000803000080300008030000803000080300008030000803000080300008030000803004000300400030060003006000300600040000c040000c040000c040000c040000c040060004008000400800040080004008000400800040080004008000400c000⟩
]
private theorem rowsE_chunk156_length : rowsE_chunk156.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk156_score : batchScore 2836 rowsE_chunk156 = 425251864 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk160 : List Row := [
  ⟨393,77,0x10000001c00000300000038000004400000600000060000006c00000800000088000009800000c000000c000000c000000c800000d8000010000001000000100000210c000011800001300000130000018000181800018180002018000201800020180003019800001a000001b00000200004020000402000040200004020000402000040200006020000602000060240000024000002600000260000028000003000080300008030000803000080300008030000803000080300008030000803000080300008030000803004000300600030060003006000300600040000c040000c040000c040000c040000c04008000400800040080004008000400800040080004008000400c000400c000⟩,
  ⟨393,77,0x8000001400000200000030000004000000480000060000006400000800000080000008c000009800000c000000c000000c000000d000000e0000010000001000001104000011000001200000130000014000001800018180002018000201800020180003018000301a000001b000001c0000020000402000040200004020000402000040200006020000602000060200006024000002600000260000028000003000080300008030000803000080300008030000803000080300008030000803000080300008030000803004000300400030060003006000300600040000c040000c040000c040000c040000c040060004008000400800040080004008000400800040080004008000400c000⟩,
  ⟨392,77,0xc0000018000002400000340000040000004c0000060000006800000800000084000009000000a000000c000000c000000c800000d8000010000001000000100000410c000011800001200000130000018000181800020180002018000201800030180003018000301a000001b000001c0000020000402000040200004020000402000060200006020000602000060240000024000002600000260000028000003000080300008030000803000080300008030000803000080300008030000803000080300008030000c03004000300600030060003006000300600040000c040000c040000c040000c040000c04008000400800040080004008000400800040080004008000400c000400c000⟩,
  ⟨392,77,0x40000010000002000000300000040000004400000600000060000006c00000800000088000009800000c000000c000000c000000cc00000d80000100000010000031000008110000012000001300000140000018000201800020180002018000301800030180003019800001a000001b00000200004020000402000040200004020000602000060200006020000602000060240000026000002600000260000030000803000080300008030000803000080300008030000803000080300008030000803000080300008030000c0300400030060003006000300600040000c040000c040000c040000c040000c04006000400800040080004008000400800040080004008000400c000400c000⟩
]
private theorem rowsE_chunk160_length : rowsE_chunk160.length = 4 := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk160_score : batchScore 2840 rowsE_chunk160 = 417952193 := by
  rw [batchE_eq]
  decide +kernel
private def rowsE_chunk164 : List Row := [
  ⟨391,77,0x80000018000002400000300000040000004c0000060000006400000800000080000008c000009800000c000000c000000c400000d000000e0000010000021000006108000011800001200000130000014000001800020180002018000201800030180003018000301a000001b000001c0000020000402000040200004020000402000060200006020000602000060200006024000002600000260000028000003000080300008030000803000080300008030000803000080300008030000803000080300008030000c03004000300600030060003006000300600040000c040000c040000c040000c040000c04008000400800040080004008000400800040080004008000400c000400c000⟩,
  ⟨391,76,0xc000001c00000280000034000004400000500000060000006c00000800000084000009000000c000000c000000c000000c800000d8000010000011000006100000c10c000011800001200000130000018000201800020180002018000301800030180003018000301a000001b0000020000402000040200004020000402000060200006020000602000060200006020000602400000260000026000002800000300008030000803000080300008030000803000080300008030000803000080300008030000c030000c03006000300600030060003006000300600040000c040000c040000c040000c04008000400800040080004008000400800040080004008000400c000400c000⟩,
  ⟨391,76,0x4000001000000200000030000004000000480000060000006000000700000080000008c000009800000c000000c000000c000000cc00000d80000100000410000081040000110000012000001300000140000018000201800020180003018000301800030180003019800001b000001b000002000040200004020000402000060200006020000602000060200006020000602400000260000026000002800000300008030000803000080300008030000803000080300008030000803000080300008030000c030000c03004000300600030060003006000300600040000c040000c040000c040000c040000c04008000400800040080004008000400800040080004008000400c000⟩,
  ⟨390,76,0x80000018000002400000300000040000004c0000060000006800000800000080000009000000a000000c000000c000000c400000d0000010000031000008100000c108000011800001200000130000018000201800020180003018000301800030180003018000401a000001b000001c000002000040200004020000602000060200006020000602000060200006020000602400000260000026000002800000300008030000803000080300008030000803000080300008030000803000080300008030000c030000c03006000300600030060003006000300600040000c040000c040000c040000c04008000400800040080004008000400800040080004008000400c000400c000⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem rowsE_chunk164_score : batchScore 2844 rowsE_chunk164 = 410853595 := by
  rw [batchE_eq]
  decide +kernel
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
end
section
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
end
section
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
end
section
namespace K1_13_7
noncomputable section
open Polynomial K1_13
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
def HighCurve (P Q : Row 3) (y : LowerPoint) : Prop :=
  ∃ q : PrimeSpectrum Lower,
    q.asIdeal ∈ (pairIdeal P Q).minimalPrimes ∧ q.asIdeal.height = 2 ∧
      q.asIdeal ≤ pointIdeal y ∧
      293711590 ≤ localColength q (pairIdeal P Q) ∧
      localColength q (pairIdeal P Q) < ⊤
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
  ceilDiv (81879 * mixed32 p big cut h) (32 * 46594) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b ^ 2 + 5 * 133671 * p.b * h.b + 1
def singularPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b ^ 2 + 1 else 0
def highCurvePrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  let q : Shape := ⟨952630000, 322000000, 0⟩
  ceilDiv (81879 * mixed32 p q q h + 46594 * mixed32 p q q p) (32 * 46594 * 293711590)
def isolatedPrice : ℕ :=
  let q : Shape := ⟨952630000, 322000000, 0⟩
  ceilDiv (3 * q.j ^ 2 * (2 * q.b - q.j)) (4 * 41481 * (41481 - 33184 + 1) * 1037)
end
end K1_13_7
end
section
set_option autoImplicit false
namespace K1_13_7_6
noncomputable section
open K1_13_7 MvPolynomial
def cap (b j : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {e | e.degree ≤ b ∧ e 1 + 2 * e 2 ≤ j}
instance capFinite (b j : ℕ) : Finite (cap b j) :=
  ((Finsupp.finite_of_degree_le b).subset (fun _ h => h.1 :
    cap b j ⊆ {e | e.degree ≤ b})).to_subtype
abbrev totalCap : ℕ := 952630000
abbrev halfIndexCap : ℕ := 161000000
abbrev chartExponents := cap totalCap (2 * halfIndexCap)
abbrev chartMap := monomialMap GeometricX chartExponents
def chartDegree {σ : Type} [Finite σ]
    (φ : MvPolynomial σ GeometricX →ₐ[GeometricX] Lower) (p : PrimeSpectrum Lower) : ℚ :=
  affineDegree (p.asIdeal.comap φ)
def zeroPrime : PrimeSpectrum Lower := ⟨⊥, inferInstance⟩
def cutIdeal (p : PrimeSpectrum Lower) (f : Lower) : Ideal Lower :=
  p.asIdeal ⊔ Ideal.span {f}
def cutCost (D : PrimeSpectrum Lower → ℚ) (p : PrimeSpectrum Lower) (f : Lower)
    (qs : Finset (PrimeSpectrum Lower)) : ℚ :=
  ∑ q ∈ qs, (localColength q (cutIdeal p f)).toNat * D q
end
end K1_13_7_6
end
section
set_option autoImplicit false
namespace K1_13_7_6
noncomputable section
open MvPolynomial
private theorem degree_fin_three (e : Fin 3 →₀ ℕ) : e.degree = e 0 + e 1 + e 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc]
private theorem degree_fin_two (e : Fin 2 →₀ ℕ) : e.degree = e 0 + e 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
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
end
section
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
def lowerFlow (q : Row 3) : Row 4 := partialFlow (liftLower q)
structure LiftedSurface (f : Row 4) (q : Row 3) (surface : Ideal GeoJets) : Prop where
  minimal : (intersectionIdeal f (liftLower q)).IsMinimalPrime surface
  leading : toGeneric (liftLower (K1_13_1.anchorLead f)) ∉ surface
  regular : toGeneric (separant f) ∉ surface
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
def evalTrajectory {L : Type} [Field L] [Algebra Geom L] (P : Row 4) (S : L[X]) : L[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (algebraMap Geom L))
    (fun i => Polynomial.hasseDeriv i.val S) P
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
    S.natDegree ≤ 133671 → evalTrajectory f S = 0 →
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
structure ActualFamily (f : Row 4) (P : Ideal CoeffRing) : Prop where
  prime : P.IsPrime
  dimension : 2 ≤ (MvPolynomial.affineHilbertPolynomial P).natDegree
  solves : ∀ i, (universalEval f).coeff i ∈ P
  regular : ∃ i, (universalEval (separant f)).coeff i ∉ P
def IntegratedMark (f : Row 4) (S : Geom[X]) : Prop :=
  ∃ P, ActualFamily f P ∧ P ≤ coefficientPointIdeal S
def ThreefoldSections (Γ : Finset K) (s : K → K[X]) (d : ℕ) : Prop := by
  classical
  exact ∀ x a : K, (∃ γ ∈ Γ, (s γ).eval x ≠ a) →
    let H := Γ.filter (fun γ => (s γ).eval x = a)
    ∃ C : Pieces H, H ⊆ C.union ∧ C.surfaces s ∧ (∀ i, 0 < C.degree i) ∧ C.total ≤ d
def ThreefoldPieces {Γ : Finset K} (C : Pieces Γ) (s : K → K[X]) : Prop :=
  ∀ i, ThreefoldSections (C.piece i) s (C.degree i)
end
end K1_13_7_2
end
section
namespace K1_13_7_4
noncomputable section
open Polynomial K1_13 K1_13_7
open scoped BigOperators
def multiOrder (a : Fin 3 →₀ ℕ) : ℕ :=
  a.sum (fun _ k => k)
def hassePartial {A : Type*} [CommSemiring A]
    (a : Fin 3 →₀ ℕ) (F : MvPolynomial (Fin 3) A) : MvPolynomial (Fin 3) A :=
  ∑ m ∈ F.support,
    MvPolynomial.monomial (m - a) (F.coeff m * ∏ i : Fin 3, ((m i).choose (a i) : A))
def VanishesTo (q : PrimeSpectrum Lower) (F : Lower) (d : ℕ) : Prop :=
  let A := Localization.AtPrime q.asIdeal
  algebraMap Lower A F ∈ IsLocalRing.maximalIdeal A ^ d
end
end K1_13_7_4
end
