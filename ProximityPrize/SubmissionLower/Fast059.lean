import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Numeric6Defs
import ProximityPrize.SubmissionLower.Numeric6AuxCert
import ProximityPrize.SubmissionLower.Numeric5Defs
import ProximityPrize.SubmissionLower.Numeric5Certificate
import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast020
import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
set_option Elab.async false

section PackSource_K1_13_1_1BudgetB
set_option autoImplicit true
namespace K1_13_1_1

set_option maxRecDepth 30000
set_option maxHeartbeats 450000

-- Each base-65536 digit is the value at one offset.
private def bbPack : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + 65536 * bbPack n (fun i => f (i+1))

private theorem bbAdd (n : ℕ) (f g : ℕ → ℕ) :
    bbPack n (fun i => f i + g i) = bbPack n f + bbPack n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [bbPack, ih, Nat.mul_add]
    omega

private theorem bbScale (n k : ℕ) (f : ℕ → ℕ) :
    bbPack n (fun i => k * f i) = k * bbPack n f := by
  induction n generalizing f with
  | zero => simp [bbPack]
  | succ n ih =>
    simp only [bbPack, ih]
    ring

private theorem bbConst (n k : ℕ) :
    bbPack n (fun _ => k) = k * bbPack n (fun _ => 1) := by
  simpa using bbScale n k (fun _ => 1)

private theorem bbSub (n : ℕ) (f g : ℕ → ℕ) (h : ∀ i, g i ≤ f i) :
    bbPack n (fun i => f i - g i) = bbPack n f - bbPack n g := by
  apply Nat.eq_sub_of_add_eq
  rw [← bbAdd]
  exact congrArg (bbPack n) (funext fun i => Nat.sub_add_cancel (h i))

private theorem bbAndCons (x y a b : ℕ) (hx : x < 65536) (hy : y < 65536) :
    (x + 65536*a) &&& (y + 65536*b) = (x &&& y) + 65536*(a &&& b) := by
  let z := (x + 65536*a) &&& (y + 65536*b)
  have hmod : z % 65536 = x &&& y := by
    change _ % 2^16 = _
    rw [Nat.and_mod_two_pow]
    change (x + 65536*a) % 65536 &&& (y + 65536*b) % 65536 = _
    simp [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  have hdiv : z / 65536 = a &&& b := by
    change _ / 2^16 = _
    rw [Nat.and_div_two_pow]
    change (x + 65536*a) / 65536 &&& (y + 65536*b) / 65536 = _
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.add_mul_div_left _ _ (by decide),
      Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy, Nat.zero_add, Nat.zero_add]
  exact (Nat.mod_add_div z 65536).symm.trans (by rw [hmod, hdiv])

private theorem bbAnd (n : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ i, f i < 65536) (hg : ∀ i, g i < 65536) :
    bbPack n (fun i => f i &&& g i) = bbPack n f &&& bbPack n g := by
  induction n generalizing f g with
  | zero => simp [bbPack]
  | succ n ih =>
    simp only [bbPack]
    rw [bbAndCons _ _ _ _ (hf 0) (hg 0), ← ih]
    all_goals first | rfl | exact fun i => hf (i+1) | exact fun i => hg (i+1)

private theorem bbLow (n k : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i < 65536) (hk : 2^k ≤ 65536) :
    bbPack n (fun i => f i % 2^k) =
      bbPack n f &&& ((2^k-1) * bbPack n (fun _ => 1)) := by
  rw [← bbConst, ← bbAnd n f (fun _ => 2^k-1) hf (by intro; omega)]
  simp [Nat.and_two_pow_sub_one_eq_mod]

private def bbShr (u z k : ℕ) := (z - (z &&& ((2^k-1)*u))) / 2^k

private theorem bbShr_eq (n k : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i < 65536) (hk : 2^k ≤ 65536) :
    bbPack n (fun i => f i / 2^k) = bbShr (bbPack n (fun _ => 1)) (bbPack n f) k := by
  unfold bbShr
  rw [← bbLow n k f hf hk, ← bbSub n f _ (fun i => Nat.mod_le _ _)]
  have he : (fun i => f i - f i % 2^k) = (fun i => 2^k * (f i / 2^k)) := by
    funext i
    have := Nat.mod_add_div (f i) (2^k)
    omega
  rw [he, bbScale, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

-- Adding 32768 before the subtraction prevents borrowing between digits.
-- The high bit marks nonnegative differences and expands to a 15-bit mask.
private def bbMonus (u x y : ℕ) : ℕ :=
  let biased := 32768*u + x - y
  let low := biased &&& (32767*u)
  low &&& (32767*((biased-low) >>> 15))

private theorem bbMonus_eq (n : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ i, f i < 32768) (hg : ∀ i, g i < 32768) :
    bbPack n (fun i => f i - g i) =
      bbMonus (bbPack n (fun _ => 1)) (bbPack n f) (bbPack n g) := by
  let v := fun i => 32768 + f i - g i
  have hv (i) : v i < 65536 := by dsimp [v]; have := hf i; omega
  have hvp : bbPack n v = 32768 * bbPack n (fun _ => 1) + bbPack n f - bbPack n g := by
    unfold v
    rw [bbSub n _ _ (by intro i; have := hg i; omega), bbAdd n (fun _ => 32768) f, bbConst]
  have hlow := bbLow n 15 v hv (by decide)
  have hshr := bbShr_eq n 15 v hv (by decide)
  change bbPack n (fun i => v i % 32768) = bbPack n v &&& (32767 * _) at hlow
  change bbPack n (fun i => v i / 32768) =
    (bbPack n v - (bbPack n v &&& (32767 * _))) / 32768 at hshr
  simp only [bbMonus, Nat.shiftRight_eq_div_pow]
  rw [← hvp, ← hshr, ← hlow, ← bbScale, ← bbAnd]
  · congr 1
    funext i
    have ha := hf i
    have hb := hg i
    by_cases h : g i ≤ f i
    · have hq : v i / 32768 = 1 := by dsimp [v]; omega
      rw [hq, Nat.mul_one]
      change _ = _ &&& (2^15 - 1)
      rw [Nat.and_two_pow_sub_one_eq_mod]
      dsimp [v]
      omega
    · have hq : v i / 32768 = 0 := by dsimp [v]; omega
      rw [hq, Nat.mul_zero, Nat.and_zero]
      omega
  · intro i; omega
  · intro i; have := hv i; omega

private def bbMin (u x y : ℕ) := x - bbMonus u x y

private theorem bbMin_eq (n : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ i, f i < 32768) (hg : ∀ i, g i < 32768) :
    bbPack n (fun i => min (f i) (g i)) =
      bbMin (bbPack n (fun _ => 1)) (bbPack n f) (bbPack n g) := by
  unfold bbMin
  rw [← bbMonus_eq n f g hf hg, ← bbSub n _ _ (fun i => Nat.sub_le (f i) (g i))]
  congr 1
  funext i
  omega

open private sumRange_succ sumRange_succ_left sumRange_zero sumRange_prefix sumRange_congr
  activeNatCount_eq natPairs_eq natLine_eq fastBlock_eq from ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic

private theorem bbSumPack (n m : ℕ) (f : ℕ → ℕ → ℕ) :
    bbPack n (fun r => sumRange m (fun i => f i r)) =
      sumRange m (fun i => bbPack n (f i)) := by
  induction m with
  | zero =>
    change bbPack n (fun _ => 0) = 0
    simpa using bbConst n 0
  | succ m ih => simp only [sumRange_succ, bbAdd, ih]

private theorem bbSumBound (n : ℕ) (f g : ℕ → ℕ) (h : ∀ i, f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih => exact Nat.add_le_add ih (h n)

private structure BBVec where
  atOffset : ℕ → ℕ
  word : ℕ
  limit : ℕ
  correct : bbPack 138 atOffset = word
  bound : ∀ i, atOffset i ≤ limit

private def bbOnes : ℕ := 0x100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001

private theorem bbOnes_ok : bbPack 138 (fun _ => 1) = bbOnes := by decide +kernel

private def bbSmaller (x y : BBVec) : BBVec where
  atOffset i := min (x.atOffset i) (y.atOffset i)
  word := if x.limit < 32768 ∧ y.limit < 32768 then bbMin bbOnes x.word y.word
    else bbPack 138 (fun i => min (x.atOffset i) (y.atOffset i))
  limit := min x.limit y.limit
  correct := by
    split
    · rename_i h
      rw [bbMin_eq 138 _ _ (fun i => (x.bound i).trans_lt h.1)
        (fun i => (y.bound i).trans_lt h.2), x.correct, y.correct, bbOnes_ok]
    · rfl
  bound i := min_le_min (x.bound i) (y.bound i)

private def bbKnownMeet (x y : BBVec) (hx : x.limit < 32768) (hy : y.limit < 32768) : BBVec where
  atOffset i := min (x.atOffset i) (y.atOffset i)
  word := bbMin bbOnes x.word y.word
  limit := min x.limit y.limit
  correct := by
    rw [bbMin_eq 138 _ _ (fun i => (x.bound i).trans_lt hx) (fun i => (y.bound i).trans_lt hy),
      x.correct, y.correct, bbOnes_ok]
  bound i := min_le_min (x.bound i) (y.bound i)

private theorem bbSumConst (n cap : ℕ) : sumRange n (fun _ => cap) = n*cap := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange_succ, ih, Nat.succ_mul]

private def bbSum (n cap : ℕ) (f : ℕ → BBVec) (h : ∀ i, (f i).limit ≤ cap) : BBVec where
  atOffset r := sumRange n (fun i => (f i).atOffset r)
  word := sumRange n (fun i => (f i).word)
  limit := n*cap
  correct := by rw [bbSumPack]; exact sumRange_congr _ (fun i _ => (f i).correct)
  bound r := (bbSumBound _ _ (fun _ => cap) (fun i => ((f i).bound r).trans (h i))).trans_eq
    (bbSumConst n cap)

-- Trailing zero digits let us reuse a packed ramp at every translated offset.
private theorem bbLastZero (n : ℕ) (f : ℕ → ℕ) (h : f n = 0) :
    bbPack (n+1) f = bbPack n f := by
  induction n generalizing f with
  | zero => simp [bbPack, h]
  | succ n ih =>
    change f 0 + 65536 * bbPack (n+1) (fun i => f (i+1)) =
      f 0 + 65536 * bbPack n (fun i => f (i+1))
    rw [ih _ h]

private theorem bbDropOne (n : ℕ) (f : ℕ → ℕ) (h0 : f 0 < 65536) (h : f n = 0) :
    bbPack n f / 65536 = bbPack n (fun i => f (i+1)) := by
  conv_lhs => rw [← bbLastZero n f h]
  change (f 0 + 65536 * bbPack n _) / 65536 = _
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt h0, Nat.zero_add]

private theorem bbTranslated (n : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i < 65536)
    (hz : ∀ i, n ≤ i → f i = 0) (k : ℕ) :
    bbPack n (fun i => f (k+i)) = bbPack n f / 65536^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : (fun i => f (k+1+i)) = (fun i => f (k+(i+1))) :=
      funext fun i => congrArg f (by omega)
    calc
      _ = bbPack n (fun i => f (k+(i+1))) := congrArg (bbPack n) he
      _ = bbPack n (fun i => f (k+i)) / 65536 :=
        (bbDropOne n (fun i => f (k+i)) (hf _) (hz _ (by omega))).symm
      _ = _ := by rw [ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

private def bbSlope (k : ℕ) (f : ℕ → ℕ) (cap value : ℕ)
    (hc : cap < 65536) (hf : ∀ i, f i ≤ cap) (hz : ∀ i, 138 ≤ i → f i = 0)
    (hw : bbPack 138 f = value) : BBVec where
  atOffset i := f (k+i)
  word := value >>> (16*k)
  limit := cap
  correct := (bbTranslated 138 f (fun i => (hf i).trans_lt hc) hz k).trans
    ((congrArg (· / 65536^k) hw).trans (by rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]))
  bound i := hf (k+i)

private def bbOrder (k : ℕ) : BBVec :=
  bbSlope k (fun i => 138-i) 138 0x100020003000400050006000700080009000a000b000c000d000e000f0010001100120013001400150016001700180019001a001b001c001d001e001f0020002100220023002400250026002700280029002a002b002c002d002e002f0030003100320033003400350036003700380039003a003b003c003d003e003f0040004100420043004400450046004700480049004a004b004c004d004e004f0050005100520053005400550056005700580059005a005b005c005d005e005f0060006100620063006400650066006700680069006a006b006c006d006e006f0070007100720073007400750076007700780079007a007b007c007d007e007f0080008100820083008400850086008700880089008a
    (by decide) (fun _ => Nat.sub_le ..) (by intros; omega) (by decide +kernel)

private def bbThird (k : ℕ) : BBVec :=
  bbSlope k (fun i => (48-i+2)/3) 16 0x100010001000200020002000300030003000400040004000500050005000600060006000700070007000800080008000900090009000a000a000a000b000b000b000c000c000c000d000d000d000e000e000e000f000f000f001000100010
    (by decide) (by intro i; omega) (by intros; omega) (by decide +kernel)

private def bbHalf (k : ℕ) : BBVec :=
  bbSlope k (fun i => (48-i+1)/2) 24 0x100010002000200030003000400040005000500060006000700070008000800090009000a000a000b000b000c000c000d000d000e000e000f000f001000100011001100120012001300130014001400150015001600160017001700180018
    (by decide) (by intro i; omega) (by intros; omega) (by decide +kernel)

-- A shifted ceiling ramp gives the part of another ramp above a constant.
private def bbFlip (cap : ℕ) (x tail : BBVec)
    (ht : ∀ i, tail.atOffset i = x.atOffset i - cap) : BBVec where
  atOffset i := cap - x.atOffset i
  word := cap*bbOnes + tail.word - x.word
  limit := cap
  correct := by
    have he : (fun i => cap - x.atOffset i) =
        (fun i => cap + tail.atOffset i - x.atOffset i) := by
      funext i; rw [ht]; omega
    rw [he, bbSub 138 _ _ (by intro i; rw [ht]; omega), bbAdd 138 (fun _ => cap),
      bbConst, bbOnes_ok, tail.correct, x.correct]
  bound _ := Nat.sub_le ..

private def bbFlipThird (k cap : ℕ) : BBVec :=
  bbFlip cap (bbThird k) (bbThird (k+3*cap)) (by
    intro i
    change (48-(k+3*cap+i)+2)/3 = (48-(k+i)+2)/3-cap
    omega)

private def bbFlipHalf (k cap : ℕ) : BBVec :=
  bbFlip cap (bbHalf k) (bbHalf (k+2*cap)) (by
    intro i
    change (48-(k+2*cap+i)+1)/2 = (48-(k+i)+1)/2-cap
    omega)

-- The line count is the smaller of a translated ceiling ramp and an order cutoff.
private def bbLine (s b c : ℕ) : BBVec :=
  let t := s-b
  bbKnownMeet (bbFlipThird (b+2*min c 24) (min (min s 10 + 1) (t-c+1)))
    (bbOrder (s+2*t-c))
    (by change min (min s 10 + 1) (t-c+1) < 32768; omega)
    (by exact (by decide : 138 < 32768))

private theorem bbWindow (t c o : ℕ) (hc : c ≤ t) :
    t-c+1 - (3*t+1-(2*c+o)) = min (t-c+1) (o+c-2*t) := by omega

private theorem bbWindowShift (s r t c : ℕ) (hc : c ≤ t) :
    138-(s+2*t-c+r) = (138-(s+r))+c-2*t := by omega

private theorem bbWindowBase (s b e : ℕ) (hb : b ≤ s) :
    3*s+1-(3*b+e) = 3*(s-b)+1-e := by omega

private theorem bbLineMeet (a h u v z : ℕ) (hv : h-v = min h z) :
    min (min a h-u) z = min (a-u) (h-max u v) := by
  rw [← Nat.sub_min_sub_right, ← Nat.sub_min_sub_left, hv, Nat.min_assoc (a-u) (h-u) z,
    ← Nat.min_assoc (h-u) h z, Nat.min_eq_left (Nat.sub_le h u)]

private theorem bbLine_val (s b c r : ℕ) (hb : b ≤ s) (hc : c ≤ s-b) :
    (bbLine s b c).atOffset r = natLine s (48-r) (138-(s+r)) b c := by
  change min (min (min s 10+1) (s-b-c+1) - ((48-((b+2*min c 24)+r)+2)/3))
    (138-((s+2*(s-b)-c)+r)) = _
  unfold natLine
  dsimp only
  rw [Nat.sub_sub 48 r _, Nat.add_comm (b+2*min c 24) r, bbWindowShift _ _ _ _ hc,
    Nat.add_assoc (3*b), bbWindowBase _ _ _ hb]
  exact bbLineMeet _ _ _ _ _ (bbWindow _ _ _ hc)

private def bbPairs (s b : ℕ) : BBVec :=
  bbSum (min s 10+1) 25 (fun f =>
    bbFlipHalf (b+3*f) (min (s-f) ((48-3*f)/2)+1)) (by
    intro f
    change min (s-f) ((48-3*f)/2)+1 ≤ 25
    omega)

private theorem bbPairs_val (s b r : ℕ) :
    (bbPairs s b).atOffset r = natPairs s (48-r) b := by
  change sumRange (min s 10+1) (fun f => (min (s-f) ((48-3*f)/2)+1) - ((48-(b+3*f+r)+1)/2)) =
    sumRange (min s 10+1) _
  apply sumRange_congr
  intro f _
  rw [show 48-(b+3*f+r) = 48-r-(b+3*f) by omega]

private def bbSlice (s b : ℕ) : BBVec :=
  bbSmaller (bbPairs s b) (bbSum (s-b+1) 11 (bbLine s b) (by
    intro c
    change min (min (min s 10+1) (s-b-c+1)) 138 ≤ 11
    exact (Nat.min_le_left ..).trans ((Nat.min_le_left ..).trans (Nat.succ_le_succ (Nat.min_le_right ..)))))

private def bbCappedRamp (k m : ℕ) : BBVec where
  atOffset i := min m (138-(k+i))
  word := (bbOrder k).word - (bbOrder (k+m)).word
  limit := m
  correct := by
    have he : (fun i => min m (138-(k+i))) =
        (fun i => (bbOrder k).atOffset i - (bbOrder (k+m)).atOffset i) := by
      funext i; change min m (138-(k+i)) = (138-(k+i)) - (138-(k+m+i)); omega
    rw [he, bbSub 138 _ _ (by intro i; change 138-(k+m+i) ≤ 138-(k+i); omega),
      (bbOrder k).correct, (bbOrder (k+m)).correct]
  bound _ := Nat.min_le_left ..

-- The number in a band is the difference of its two capped ramps.
private def bbCell (s f c : ℕ) : BBVec :=
  let k := 2*c+3*f
  let m := min (s-f-c+1) (49-k)
  let x := bbCappedRamp k m
  let y := bbCappedRamp (90+k) m
  { atOffset := fun i => x.atOffset i - y.atOffset i
    word := x.word - y.word
    limit := m
    correct := by
      rw [bbSub 138 _ _ (by
        intro i
        change min m (138-(90+k+i)) ≤ min m (138-(k+i))
        exact min_le_min (le_refl m) (Nat.sub_le_sub_left (by omega) _)), x.correct, y.correct]
    bound := fun i => (Nat.sub_le ..).trans (x.bound i) }

private theorem bbTruncLow (m hi lo : ℕ) (h : lo ≤ hi) :
    min m hi - min m lo = min m hi - lo := by omega

private theorem bbCell_val (s f c r : ℕ) (hr : r < 138) :
    (bbCell s f c).atOffset r =
      min (s-f-c+1) (min 48 (137-r)+1-(2*c+3*f)) - (48-r-(2*c+3*f)) := by
  let k := 2*c+3*f
  let a := s-f-c+1
  change min (min a (49-k)) (138-(k+r)) - min (min a (49-k)) (138-(90+k+r)) =
    min a (min 48 (137-r)+1-k) - (48-r-k)
  have hhi : min 48 (137-r)+1 = min 49 (138-r) := by omega
  have hlow : 138-(90+k+r) = 48-r-k := by omega
  have hhigh : 138-(k+r) = 138-r-k := by omega
  have he : min (min a (49-k)) (138-(k+r)) = min a (min 48 (137-r)+1-k) := by
    calc
      _ = min a (min (49-k) (138-r-k)) := by rw [Nat.min_assoc, hhigh]
      _ = _ := by rw [Nat.sub_min_sub_right, hhi]
  exact (bbTruncLow _ _ _ (Nat.sub_le_sub_left (by omega) 138)).trans (congrArg₂ Nat.sub he hlow)

private def bbActive (s : ℕ) : BBVec :=
  bbSum (min s 10+1) 1225 (fun f =>
    bbSum (min (s-f) ((48-3*f)/2)+1) 49 (bbCell s f) (fun _ => (Nat.min_le_right ..).trans (Nat.sub_le ..))) (by
      intro f
      change (min (s-f) ((48-3*f)/2)+1)*49 ≤ 1225
      omega)

private theorem bbCellInside (a hi base lo : ℕ) (h : base ≤ hi) :
    min (a+1) (hi+1-base) - (lo-base) = (min a (hi-base)+1) - (lo-base) := by
  rw [Nat.succ_sub h, Nat.succ_min_succ]

private theorem bbCellOutside (a hi base lo : ℕ) (h : hi < base) :
    min a (hi+1-base) - (lo-base) = 0 := by simp [Nat.sub_eq_zero_of_le h]

private theorem bbInC (hi f c : ℕ) (hf : f ≤ hi/3) (hc : c ≤ (hi-3*f)/2) :
    2*c+3*f ≤ hi := by omega

private theorem bbPastC (t hi f c : ℕ) (h : min t ((hi-3*f)/2) < c) (hc : c ≤ t) :
    hi < 2*c+3*f := by omega

private theorem bbPastF (t hi f c : ℕ) (h : min t (hi/3) < f) (hf : f ≤ t) :
    hi < 2*c+3*f := by omega

private theorem bbActive_val (s r : ℕ) (hr : r < 138) :
    (bbActive s).atOffset r = activeNatCount s (48-r) (min 48 (137-r)) := by
  let hi := min 48 (137-r)
  let lo := 48-r
  change sumRange (min s 10+1) (fun f => sumRange (min (s-f) ((48-3*f)/2)+1)
    (fun c => (bbCell s f c).atOffset r)) = _
  simp only [bbCell_val _ _ _ r hr]
  unfold activeNatCount
  change _ = sumRange (min (min s 10) (hi/3)+1) _
  have hhi : hi ≤ 48 := min_le_left ..
  rw [sumRange_prefix (min s 10+1) (min (min s 10) (hi/3)+1) _ (Nat.succ_le_succ (min_le_left ..))]
  · apply sumRange_congr
    intro f hf
    have hf' := (Nat.le_of_lt_succ hf).trans (Nat.min_le_right ..)
    rw [sumRange_prefix (min (s-f) ((48-3*f)/2)+1) (min (s-f) ((hi-3*f)/2)+1) _
      (Nat.succ_le_succ (min_le_min_left _ (Nat.div_le_div_right (Nat.sub_le_sub_right hhi _))))]
    · apply sumRange_congr
      intro c hc
      change min (s-f-c+1) (hi+1-(2*c+3*f)) - (lo-(2*c+3*f)) =
        min (s-f-c) (hi-2*c-3*f)+1-(lo-(2*c+3*f))
      rw [Nat.sub_sub hi (2*c) (3*f)]
      exact bbCellInside _ _ _ _ (bbInC _ _ _ hf' ((Nat.le_of_lt_succ hc).trans (Nat.min_le_right ..)))
    · intro c hc hc'
      exact bbCellOutside _ _ _ _ (bbPastC _ _ _ _ hc ((Nat.le_of_lt_succ hc').trans (Nat.min_le_left ..)))
  · intro f hf hf'
    apply sumRange_zero
    intro c _
    exact bbCellOutside _ _ _ _ (bbPastF _ _ _ _ hf (Nat.le_of_lt_succ hf'))

private def bbBlock (s : ℕ) : BBVec :=
  bbSmaller (bbActive s) (bbSum (s+1) 275 (bbSlice s) (by
    intro b
    apply (Nat.min_le_left ..).trans
    change (min s 10+1)*25 ≤ 275
    omega))

private theorem bbBC (s b c : ℕ) (hb : b < s+1) (hc : c < s-b+1) : b+c ≤ s := by omega

private theorem bbLate (s r b c : ℕ) (hr : ¬ s+r < 138) (hc : c < s-b+1) :
    138-((s+2*(s-b)-c)+r) = 0 := by omega

private theorem bbBlock_val (s r : ℕ) (hs : residualDegree s = s)
    (hn : selectedFactors s (offset r) = none) :
    (bbBlock s).atOffset r = fastBlock s r := by
  by_cases hr : s+r < 138
  · rw [fastBlock_eq]
    unfold blockBudget
    have hcut : offset r < 90 - (s : ℤ) := by unfold offset; omega
    rw [ite_eq_left hcut, hn]
    simp only [pascalBound, hs]
    have hh : 0 ≤ activeIndex (offset r) := by unfold activeIndex offset; omega
    rw [activeNatCount_eq _ _ _ hh]
    have hlo : (-(offset r)).toNat = 48-r := by unfold offset; omega
    have hhi : (activeIndex (offset r)).toNat = min 48 (137-r) := by
      unfold activeIndex offset; omega
    have ho : 0 ≤ orderCutoff s (offset r) := by unfold orderCutoff offset; omega
    have horder : (orderCutoff s (offset r)).toNat = 138-(s+r) := by
      unfold orderCutoff offset; omega
    rw [hlo, hhi]
    change min ((bbActive s).atOffset r) (sumRange (s+1) (fun b => (bbSlice s b).atOffset r)) = _
    rw [bbActive_val s r (by omega)]
    congr 1
    apply sumRange_congr
    intro b hb
    rw [natPairs_eq, hlo]
    change min ((bbPairs s b).atOffset r) (sumRange (s-b+1) (fun c => (bbLine s b c).atOffset r)) = _
    rw [bbPairs_val]
    congr 1
    apply sumRange_congr
    intro c hc
    rw [bbLine_val s b c r (Nat.le_of_lt_succ hb) (Nat.le_of_lt_succ hc),
      natLine_eq _ _ _ ho _ _ (bbBC _ _ _ hb hc), hlo, horder]
  · rw [fastBlock, ite_eq_right hr]
    change min _ (sumRange (s+1) (fun b => (bbSlice s b).atOffset r)) = 0
    suffices hz : sumRange (s+1) (fun b => (bbSlice s b).atOffset r) = 0 by simp [hz]
    apply sumRange_zero
    intro b hb
    change min _ (sumRange (s-b+1) (fun c => (bbLine s b c).atOffset r)) = 0
    suffices hz : sumRange (s-b+1) (fun c => (bbLine s b c).atOffset r) = 0 by simp [hz]
    apply sumRange_zero
    intro c hc
    change min _ (138-((s+2*(s-b)-c)+r)) = 0
    rw [bbLate s r b c hr hc, Nat.min_zero]

private def bbDigits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, z => z%65536 + bbDigits n (z/65536)

private theorem bbDigits_eq (n : ℕ) (f : ℕ → ℕ) (h : ∀ i, f i < 65536) :
    bbDigits n (bbPack n f) = sumRange n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [bbDigits, bbPack, sumRange_succ_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (h 0), Nat.add_mul_div_left _ _ (by decide : 0 < 65536),
      Nat.div_eq_of_lt (h 0), Nat.zero_add]
    rw [ih _ (fun i => h (i+1))]

private theorem bbGrade (s ans : ℕ) (hs : residualDegree s = s)
    (hn : ∀ g, selectedFactors s g = none) (hlim : (bbBlock s).limit < 65536)
    (hnum : bbDigits 138 (bbBlock s).word = ans) :
    fastGrade s = ans := by
  unfold fastGrade
  rw [sumRange_congr 138 (fun r _ => (bbBlock_val s r hs (hn _)).symm)]
  rw [← bbDigits_eq 138 _ (fun i => ((bbBlock s).bound i).trans_lt hlim), (bbBlock s).correct, hnum]

-- Four hexadecimal digits per offset, starting with offset zero at the right.
-- Each equality checks the complete block vector before its digits are summed.
private theorem bbWord20 : (bbBlock 20).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019501c701fb0232026a02a402df031b0357039403d0040c0446047f04b504e905190546056e059205b005c905dd05ed05f906020608060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060b060a06080605060105fc05f505ed05e305d705c905b905a605910579055e0540051f04fa04d204a604770445041103da03a20368032d02f102b50278023c020001c6018d0157012300f300c6009e007a005c0043002f001f0013000a0004 := by decide +kernel

private theorem grade20 : fastGrade 20 = 108360 :=
  bbGrade 20 108360 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord20).trans (by decide +kernel))

private theorem bbWord21 : (bbBlock 21).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601c901ff0238027302b002ef032f037003b203f40436047704b704f50531056a05a005d206000629064d066b0684069806a806b406bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bc06bb06b906b606b206ad06a6069e06940688067a066a06570642062a060f05f105d005ab05830557052704f404be0485044a040d03ce038e034d030b02c902870246020601c8018c0153011d00eb00bd0094007000520039002500150009 := by decide +kernel

private theorem grade21 : fastGrade 21 = 119025 :=
  bbGrade 21 119025 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord21).trans (by decide +kernel))

private theorem bbWord22 : (bbBlock 22).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0201023c027902b902fb033f038403cb0412045a04a104e8052d057105b205f1062c0664069706c606ef07130731074a075e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076d076c076a07670763075e0757074f07450739072b071b070806f306db06c006a20681065c0634060805d805a4056d053204f504b50473042f03ea03a3035c031402cd0286024101fd01bc017d0142010a00d700a8007f005b003d00240010 := by decide +kernel

private theorem grade22 : fastGrade 22 = 129336 :=
  bbGrade 22 129336 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord22).trans (by decide +kernel))

private theorem bbWord23 : (bbBlock 23).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023e027d02bf0304034b039403df042b047804c50512055e05a905f20639067d06be06fb07340768079707c007e40802081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081a0819081708140810080b080407fc07f207e607d807c807b507a00788076d074f072e070906e106b506850651061905dd059e055c051704d00487043c03f003a30356030902bd0272022901e2019e015d012000e700b30084005b00370019 := by decide +kernel

private theorem grade23 : fastGrade 23 = 139025 :=
  bbGrade 23 139025 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord23).trans (by decide +kernel))

private theorem bbWord24 : (bbBlock 24).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f027f02c3030a035403a003ef043f049104e30536058805da062a067906c5070f0755079807d6081008440873089c08c008c008c008c008c008c008c008c008c008c008c008c008c008c008c008c008c008c008bf08be08bc08b908b508b008a908a10897088b087d086d085a0845082d081207f407d307ae0786075a072a06f606be0681064105fd05b6056c052004d10481042f03dd038a033802e60296024701fb01b1016b012800ea00b0007c004d0024 := by decide +kernel

private theorem grade24 : fastGrade 24 = 147840 :=
  bbGrade 24 147840 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord24).trans (by decide +kernel))

private theorem bbWord25 : (bbBlock 25).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c5030e035a03a903fb044f04a504fc055405ac0604065b06b10705075707a607f2083a087e08bd08f7092b095a095a095a095a095a095a095a095a095a095a095a095a095a095a095a095a095a0959095809560953094f094a0943093b093109250917090708f408df08c708ac088e086d0848082007f407c407900758071b06da0695064c060005b1055f050b04b5045e040603ae035602ff02a90255020301b40168012000dc009d0063002f := by decide +kernel

private theorem grade25 : fastGrade 25 = 155610 :=
  bbGrade 25 155610 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord25).trans (by decide +kernel))

private theorem bbWord26 : (bbBlock 26).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60310035e03af0404045b04b50510056d05ca0628068506e2073d079707ee0843089408e2092b097009af09e909e909e909e909e909e909e909e909e909e909e909e909e909e909e909e909e809e709e509e209de09d909d209ca09c009b409a609960983096e0956093b091d08fc08d708af08830853081f07e707aa0769072306d9068b063a05e5058e053404d9047c041f03c10364030702ac025201fb01a60155010700be0079003a := by decide +kernel

private theorem grade26 : fastGrade 26 = 162368 :=
  bbGrade 26 162368 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord26).trans (by decide +kernel))

private theorem bbWord27 : (bbBlock 27).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036003b3040a046404c10520058105e3064606a9070c076e07cf082e088b08e5093c098f09de0a280a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6c0a6b0a690a660a620a5d0a560a4e0a440a380a2a0a1a0a0709f209da09bf09a10980095b0933090708d708a3086b082e07ed07a7075c070d06ba0663060905ac054d04ec048a042703c4036102ff029e023f01e20188013100de008f0045 := by decide +kernel

private theorem grade27 : fastGrade 27 = 168147 :=
  bbGrade 27 168147 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord27).trans (by decide +kernel))

private theorem bbWord28 : (bbBlock 28).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b5040e046a04ca052c059105f7065f06c7073007980800086608cb092d098d09e90a420a960ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae50ae40ae20adf0adb0ad60acf0ac70abd0ab10aa30a930a800a6b0a530a380a1a09f909d409ac09800950091c08e408a70866082007d50785073106d8067c061c05ba055504ef0487041f03b6034e02e60280021b01b9015900fd00a40050 := by decide +kernel

private theorem grade28 : fastGrade 28 = 172980 :=
  bbGrade 28 172980 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord28).trans (by decide +kernel))

private theorem bbWord29 : (bbBlock 29).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60410046e04d00535059d0607067306e0074e07bc082a08970903096d09d50a3a0a9c0afa0b540b540b540b540b540b540b540b540b540b540b540b540b540b530b520b500b4d0b490b440b3d0b350b2b0b1f0b110b010aee0ad90ac10aa60a880a670a420a1a09ee09be098a0952091508d4088e084307f3079e074406e60684061f05b7054d04e1047404060398032a02bd025101e7017f011a00b8005a := by decide +kernel

private theorem grade29 : fastGrade 29 = 176900 :=
  bbGrade 29 176900 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord29).trans (by decide +kernel))

private theorem bbWord30 : (bbBlock 30).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047004d4053b05a60613068306f4076707da084e08c1093409a50a150a820aed0b540bb80bb80bb80bb80bb80bb80bb80bb80bb80bb80bb80bb80bb70bb60bb40bb10bad0ba80ba10b990b8f0b830b750b650b520b3d0b250b0a0aec0acb0aa60a7e0a520a2209ee09b60979093808f208a70857080207a7074806e4067d061205a5053504c4045103de036a02f70284021301a3013600cb0064 := by decide +kernel

private theorem grade30 : fastGrade 30 = 180000 :=
  bbGrade 30 180000 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord30).trans (by decide +kernel))

private theorem bbWord31 : (bbBlock 31).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d6053f05ac061c068f0704077b07f3086c08e5095e09d60a4d0ac20b350ba50c120c120c120c120c120c120c120c120c120c120c120c110c100c0e0c0b0c070c020bfb0bf30be90bdd0bcf0bbf0bac0b970b7f0b640b460b250b000ad80aac0a7c0a480a1009d30992094c090108b1085c080107a1073c06d3066605f60583050e0497041f03a6032d02b4023c01c5015000dd006d := by decide +kernel

private theorem grade31 : fastGrade 31 = 182310 :=
  bbGrade 31 182310 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord31).trans (by decide +kernel))

private theorem bbWord32 : (bbBlock 32).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d7054105b0062206980710078b08070885090309820a000a7e0afa0b750bed0c630c630c630c630c630c630c630c630c630c630c620c610c5f0c5c0c580c530c4c0c440c3a0c2e0c200c100bfd0be80bd00bb50b970b760b510b290afd0acd0a990a610a2409e3099d0952090208ad085207f2078c072206b3064105cb055304d8045c03de036002e1026301e5016900ee0076 := by decide +kernel

private theorem grade32 : fastGrade 32 = 183918 :=
  bbGrade 32 183918 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord32).trans (by decide +kernel))

private theorem bbWord33 : (bbBlock 33).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d7054205b20626069e0719079708170899091c09a00a240aa80b2b0bad0c2d0cab0cab0cab0cab0cab0cab0cab0cab0cab0caa0ca90ca70ca40ca00c9b0c940c8c0c820c760c680c580c450c300c180bfd0bdf0bbe0b990b710b450b150ae10aa90a6c0a2b09e5099a094a08f5089a083a07d4076906f90685060d0592051404940412038f030b02870203018000fe007e := by decide +kernel

private theorem grade33 : fastGrade 33 = 184851 :=
  bbGrade 33 184851 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord33).trans (by decide +kernel))

private theorem bbWord34 : (bbBlock 34).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d7054205b3062806a2071f07a0082308a9093009b90a420acc0b550bde0c650ceb0ceb0ceb0ceb0ceb0ceb0ceb0ceb0cea0ce90ce70ce40ce00cdb0cd40ccc0cc20cb60ca80c980c850c700c580c3d0c1f0bfe0bd90bb10b850b550b210ae90aac0a6b0a2509da098a093508da087a081407a9073806c3064905cc054b04c8044203bb033202a9021f0196010d0086 := by decide +kernel

private theorem grade34 : fastGrade 34 = 185192 :=
  bbGrade 34 185192 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord34).trans (by decide +kernel))

private theorem bbWord35 : (bbBlock 35).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d7054205b3062906a4072307a6082c08b5094009cd0a5b0aea0b790c080c960d230d230d230d230d230d230d230d220d210d1f0d1c0d180d130d0c0d040cfa0cee0ce00cd00cbd0ca80c900c750c570c360c110be90bbd0b8d0b590b210ae40aa30a5d0a1209c2096d091208b2084c07e1077006fa067f0600057d04f7046e03e3035602c8023901aa011b008d := by decide +kernel

private theorem grade35 : fastGrade 35 = 184965 :=
  bbGrade 35 184965 rfl (fun _ => rfl) (by decide +kernel)
    ((congrArg (bbDigits 138) bbWord35).trans (by decide +kernel))

private theorem sumStep (f : ℕ → ℕ) (n a b : ℕ)
    (ha : sumRange n f = a) (hb : f n = b) :
    sumRange (n + 1) f = a + b :=
  (show sumRange (n + 1) f = sumRange n f + f n from rfl).trans (congrArg₂ Nat.add ha hb)

private def gradeFrom (i : ℕ) : ℕ := fastGrade (i + 20)

private theorem prefix20 : sumRange 1 gradeFrom = 108360 :=
  sumStep gradeFrom 0 0 108360 rfl grade20
private theorem prefix21 : sumRange 2 gradeFrom = 227385 :=
  sumStep gradeFrom 1 108360 119025 prefix20 grade21
private theorem prefix22 : sumRange 3 gradeFrom = 356721 :=
  sumStep gradeFrom 2 227385 129336 prefix21 grade22
private theorem prefix23 : sumRange 4 gradeFrom = 495746 :=
  sumStep gradeFrom 3 356721 139025 prefix22 grade23
private theorem prefix24 : sumRange 5 gradeFrom = 643586 :=
  sumStep gradeFrom 4 495746 147840 prefix23 grade24
private theorem prefix25 : sumRange 6 gradeFrom = 799196 :=
  sumStep gradeFrom 5 643586 155610 prefix24 grade25
private theorem prefix26 : sumRange 7 gradeFrom = 961564 :=
  sumStep gradeFrom 6 799196 162368 prefix25 grade26
private theorem prefix27 : sumRange 8 gradeFrom = 1129711 :=
  sumStep gradeFrom 7 961564 168147 prefix26 grade27
private theorem prefix28 : sumRange 9 gradeFrom = 1302691 :=
  sumStep gradeFrom 8 1129711 172980 prefix27 grade28
private theorem prefix29 : sumRange 10 gradeFrom = 1479591 :=
  sumStep gradeFrom 9 1302691 176900 prefix28 grade29
private theorem prefix30 : sumRange 11 gradeFrom = 1659591 :=
  sumStep gradeFrom 10 1479591 180000 prefix29 grade30
private theorem prefix31 : sumRange 12 gradeFrom = 1841901 :=
  sumStep gradeFrom 11 1659591 182310 prefix30 grade31
private theorem prefix32 : sumRange 13 gradeFrom = 2025819 :=
  sumStep gradeFrom 12 1841901 183918 prefix31 grade32
private theorem prefix33 : sumRange 14 gradeFrom = 2210670 :=
  sumStep gradeFrom 13 2025819 184851 prefix32 grade33
private theorem prefix34 : sumRange 15 gradeFrom = 2395862 :=
  sumStep gradeFrom 14 2210670 185192 prefix33 grade34
theorem budgetB : sumRange 16 (fun i => fastGrade (i + 20)) = 2580827 :=
  sumStep gradeFrom 15 2395862 184965 prefix34 grade35

end K1_13_1_1
end PackSource_K1_13_1_1BudgetB

section PackSource_K1_13_2_3_5DataC
set_option autoImplicit true
namespace K1_13_2_3_5


namespace DataC2344

open K1_13_2_3
open private rowLoop rowScore unpack from ProximityPrize.SubmissionLower.Numeric5Certificate

set_option maxHeartbeats 3000000
set_option maxRecDepth 50000

-- Field u stores denFast u. The kernel checks all 1,652 fields below.
private def cDenTable : Nat := 0xef84cf5de2b417ba9a52771bd56edc8e37dab47cfb3aeef763eadbec0f1d7d742037accc20f562987ea577bfd3d3d23a5f1e1f48794fe8a1fd9d069e6b9f202cf3ada28e6eea11cd043e39856fc72d4c08e53d651c9a2d5f91964b71fcee4e38e483c645ab78ade1471262b1e1e1493c2ecbbf842e51f050765e03666bbf9804b7d86feef7bcf5de8d9f5bc4783376e815eea8356dce6f1db8fb34b7051916dd5a7edb425cdb5b316769c36c6d04262d99fdefb26f25f633da16c33af7d7ff76faf2f6075cc02aeb64433d661237abf3c33564b03ea95e0bd4c4e31a8bc4bb4fde26e9c8874d32ab49a588f7349798e68fc364d192969a259c2f431d356830ed0cffc87b9f2eac73cc9166766aadce6886b9c07b0f367d2be69d6f1ccd692398e4cdb303970e5d5391cb46a8d95c600329fddfe50e082c9b8c9592ab45b23ca736447dbac82cf258f949b71d9f266382b2ec6a32278c81fef177bf362be8d3c51b58789736d71160d4e1fb69fc39592f8668e430b4dc5e139487c211d09836260b0542c0e078280c090101805fe02ff3fc05fb8080bf105017d615fef944bf5ef8e7cbd928f37a66dd6f351b85e3ac69bc16cc3777055eed66a5dd7da3dba9d05b747dc6ae78382dcc17edb9253a5718f2d2e1a849dc0656eb7af68d6ea486adbd4f55b4c2b6b63b8fd6bbdd06d609805a92fbab4c9adf68db07ed045e559dac6fb359c1f65fc2a6ca8a1ed9238cbb1ebca76321352c4d627d86d4c3b07fc61604a25abf29fad7b804caf15b395d76f92b985925703b5cadad9195aa7aceb3e8e956505e8ac475eb57dc3e6ae53fa559dfe5aae319b5514aaea8c6bfd4ec949a980c135250efaa34134d43c209a82053d4f910a29dc353d38ca1aa6c1d054cd4f7a984d1752de172a5653554a1cb5692de7a5230806a40a817476840e8d77775183dcba2b1b3744b7976881808d0d82b7a15ac9f420ab6282c029d02d6bfa005c393f619aa7d6fd4cf839d89eb29f13cbc4227827044edabf89d615b13a1aa9e72e5b34e32d149c11f63377ccf66dabdc4d8bd219ac46f334e2afe687979cce5c159978c4b324c48a634e86cc409e5982ef552fb99725e2afdcb9c68696e6ffd2d2a98a590ed94af91ee95a0e2d2a9f4a653fa144a56c12945c9cf2817a9e4eeca949b54e7931a2cf2593b4649e692c914c6391d9917231367244e7cbc87527b909ac912096bfa3ff04ec7d67248f5dd291e1dbb23b00164738a548e22ac91ba856e36171d469bc008ce955b193690631355e45ffc1d8bb1ccb16c864e2c5ad3c564aa18a7c103145dd1a278778c4ca78189481ed11f6d4222bb47c4312b28815f750f9369a1df63b4398c2a86e59850d338f619384e43013de85b70070ad742e14817b426a9c3848a2e7087e8160fd1bcc1d4dcf835f20f06294820b290dc13fff78235d6903d794a068768c0ac030810e4e1018964201ecc84018e707fe8860ff3eb3dfd59273f86aac7ec47d2fcf7815f8cc803ef54d97da2322fab3c9df446cdbe64ced7c81a3af8738a9efc80abdd52dd7b62d04f636c11eb5031bd4669e7a45b6cf3fd6a9e6df3d3cb8826792a55cf1c7845e275283c2b76a7810abeef950bdde11ed3b9f45f76f8b7eed65fe5d9b586bb13efb75e2786eb3a591d55fefba8973374cdec0e912199d11122b9ffcfc73bb118e6ed3d1ccc91a397704c72a9e78e4cbc0dc887d138ef118719a6cae2ada25c44d423867f55708c9fae092dedc01967b7e1af96f807f2de7b739bbec3cb75c3f96e7609cdc675e1b7c5bbb6d7a4a6d6d3e4da569b9b3a5df3653de26c661b4d849295af8ca235d0eb66b609f6d63f04dab79ff354ecbb6a5cc96d4382b5a76df0b4cd7e7695a97ed2349a1a36871b44d02f685a098d0344e99f697cb3cd588675b1d0ce374619b710c334e7e8665dd10cc3d7dd977f1b32d07446562242ca46f359393a432533916468152c853a3d8faea1b1d6cc5636fa2ac6638c98bd00eb15b2d56278cb4c476ab187f7e5b0e05b661838dcc28cfc9842621306655e608fe8cc0a67e5805abc2fed1c25f9ddaebec32dd7c95b12f74ad75ead62ebce308578d6faaefd0935dbe7f6bb060b1751e93ae862eb5cd12f0b92c339716c76ae101d45be5708b7557f16dc09e2d9ad445afb428b581ead6a1b052d265305a12a3ab3b1745667ba62cb298d592b92ab1e418d62e27bac3fa5158460e2b019d595f4f80abcd771576214cae52a815bc2afab5c0e2567fa54ac8e8d9583c032aeb69a559ebe4aacd83554bb762a7b88e54bf5e6a90f86d5141032a0c6b353e1846a7549554dcca4a99e0ff53052eea59cac14a5e55a930767522a5c8a3e7c8946f610a8c39e051510c0a235e814393d0285786050793c0a08707d40378f27ec2dc4fa2eb29edb2553ce14827819494ece1829d323dd3990f5a717b9d4dfac1a9b8c4e9364692a6ae9cd4d28e6499e9551330219a6463ce4c5884c98494e92fc38525de9964b899bc96ac3852c8ad02577b1a4abc29e95120fd2957f5251184f49f02de937ad25262aeea4ac12b4925a6691e67d12303b7a4475a3485c92090550d91fe24aa3e35ac4794ef88ec68111cc6a2238013c46cebd88d3ad4d19b0b9231d8484609faa8bb206516a08a22bbac54546a5a8a2c12d13960fa25a8a94484bd288a8f79109144a1fa1e943c43fc8728b210d9223a19a67a43052c485ab3f90a98a7213b652424781484309d507a4ca20dd166418b3d682b8c8d04b687207f7ab40d05f68143bf501cdd8a0229174016e5e7fd17e0feeab99fc659f3f5ecf87e62028fc0d249f6ad383ea81b07cf54a0f935141f0ffd83df2c707b8b51cf662831eb5d743d3ed227a24174f3956c1e5c6013c8c3b278bf97cf0cdc99e039753bdb00a775dd08ee0b969dab7c53b2b21475febf0eb4ecd9d540e63a7c9bc74a2608e897691cfd4ce39cf6ec7348b24e5e5641ca7372392398e71f1b1ce338b91c51cc7387918e709d5c4e091629bfd0c337cfed66f4baf0ddef5b9ba8f5b37281506dfca78db529e9b5588436818e86cb0430d8bb261b02c3435dc5886b667ecd628ed1ab0a60353871a6a1f584d39bee1a5f2fd3495d8a68dacccd114239a0e60133f48c26798d98ce918899be36133548ac66597c0cc1417996eb1232b5d34651cb18c99bcb191fd0a321864463e2774c7289e18d193e317c3c662aacacc4ba8b1883fa330e15a66175a94c2518c983702f3047bce6043100bfed9d97eaad72faf6285f12fc8bd8eb8979ef902f184a05de56c0bb34d81753e502e827205cba5bcb8dff7170970c2dedd925b91c94b6901016bf9b92d5a7e25a6bb1cb4451d967664d2cc85fa5948128b1ff1a962dcbd2c377c45826e90afbe0195e5cfe2ba7d2c5708328ad81cd159e7062b1961c55ebec4ab4a781557aca2a8c27e54d213ca917fd151183f2a0023e53baa64a6ea5694cbf5b297554652a5a10a4c17f948701328ebb805193018a29d729442a5c28634d85082c50a07e2a13fee2c27dc1384f74e8c9e63a113bbb78275608a4e696a49c4dd2137923526d12ba4d6046c9a3cb79337259264d7b24c597b898304c92f5bd925caf5c4b5506096288b92b4eaa25499a44a52e3894256f1274ac224c967449531149226f21235016244a5b648558cc902d0f11f5e9b23cc756475a5348e37c091b7647234fb3e46616208c4701917970f22d4158456ab688a5acc913c0e8225999044764e088731c10ff3c821e03d0438425c868feb10c2fa4216800242943b484b134108747120f0e1241a68bc82d6f1904c225207adea40bb14881011e90118b52005f743fd1d307f2fb58fd78161f9229c3eeac487d62b10f9e03e1f1f74c3e05e647b9a0c0f651221eadd6e3d2335c79d5c10f2cab71e3d4ee3c42b047815ca8ef4cf31dcddb63b64530765a238ebd7cb1d5f7b03a881b874a2c68e86b341cf22c839ae07072efae0e507241c85ee838d612c7140d50e1ab901c1abfa38003c46f96360de586d1bb09ea372c80c6defcb8db0db11b478a2365add86c4d908d7cb511adf80c358b5006aaf7f8d491421a7881434bdd586915930d15f7a1a128a433f26b4677fc60ce35ee19ad9a633290ec65ee130cb14931949b063261bd46460748c7fb5f18e6cae319c74062d6e58c4ea471884e8830d93086151608c1e14018240803017f005fcfe00bee04017c42802f58afc5e525f0bbe73c17654722e9b6d45cd8d80b8f62917076422de025c5b63458b60cfd16aa7da2d26d6859f1a28b32bad164e9242c6f7d05883e98b0522e15f3a0c2bba168571a150ad80761599a7c2b06a0455b4200aab67a1540a5e2a5517c5452050a7f42f14e899e29a57a452f3be8a5398b149182628f7c505199478a28683143b5e0284bf5850429a89fdb0c13e62b827a20904eefb209d371c1391e9826f9fcc4da08909a9aa8133e96a2653ce44c551a09805a512ec31a25af7ac4b0d5f8957809129ab92250cff849c954892f1c9124a2bc246c5a04888f389072da11fa88423cd878474c3708dfb3211abcd4233085446131a08b8ac6115df96229550c44dd97089218b11110b621fbe7443aba8886bf7710c501e2164460427d49884647f1079db820ce6a84152748821098102f970203a520402b2407fc3b80fe63301fa7f9c3f075307d7dd40f9dae21f175f43de6fc07b3ee10f560721e887fc3cca1987906d50f0f3ca1dfb5883bb0a6876d5a50ec94d41d6fe703a9a9d874ab460e8437c1ce62883987f907287ae0e3ffac1c5e1a43878b40706ad20dfc94e1bd7b9c376cc906e54a70dba04e1b5304436643286c45230d784961acff70355eeb86a3c3b0d376101a4e8f8345cee86839e40cf74a819cecb0335e360663e140cb80481950a6c3262bd06448c00c798da18d4204316a7e06259dd0c3be4a185934c30757386071610bff08217dfe182f839885e8f410bc2f6c17682402e94e785cb3720b87af416f1f982da95b05addea0b4d304167d5f42cc0ee0590e9e0b13786160a52c2bdb9b05745830ada8661598d142af95c855828f0aa258e1528d802a1a2d853c5b70a6aee814ba648293e088520ef00a34460144d7402864e80505e3009fe5e013e203c278ec704eb36c09c9352137811426bba004d0e990994ca2130f99c25eb6d84b6fad09611ba12a89a8251e2a849d69d092e28412431102453d1848435e08fbeec11defa8238c5d046b5e608ca6dc117c54422c7c80452e2a0899a3e111b1bc22060d043ac1f08698fe10bb4e42147268422fbb083a306105ce90208b0f840b8f3080b8400fffe981fd1c283f47bc07dd8980fa44d01f1b3a03ddc0c07b03f80f4a10c1e677103c75d80783a4a0ef13241db66203b15150757b7a0e99aec1d0807839b9b9072c7720e438381c5c5c83863b90701e1c0deeae01bb35b837130a06d7f640d9b2b81b0cff035c7a206aeb340d48f941a6942034817606861760cf814c19c81f033407b065e2160ca87b419299083204a70636cfe0c5a2a0188d91830cdef06102180c0d1e817f41c82f9c4805ea1500bc1560175d2c02e6fa805c4a900b76cdc16c8bb02d4804059fdc20b2d8341636c402c2551057bad20ae573c15a74182b078505581aa0a9e9c8151a2e829ee9505352340a58fb0148f85828da760512c5c0a148c8140741027cb1e04f100c09d14e413815c026c08204cfd2e098f3dc12fdd1025ba9704af3ae094e584127c9a824b953048f376090e9b011fdb3823bcab046fc7008d0038118116822c4940450e8808928f01106be021d10404329a808563ac108ea5020e1f00414dba081b0441018c601ff74d03f7aaa07e0e8c0fa51b81f111103db06207a7e580f33a081e2f3103beecc076ff800ec44f81d51a203a35d407391d80e572301c785a038856407035340dec1601ba34e036dd6606ce96c0d832301ad2730353dc6069ae540d1c4481a05bf033a66e06683c00cb7758193d27032174806369880c54b081878a003090400605f800bf3f0017b82002f114005d657c0b952f016fb9c02d9a3205a7b540b3868016430902c2b02057a0dc0add958158e5d02ac39a054d5e80a84b2814dd8d02963e40521a500a2db9814308e0280bcc04f6de809d8a50138756026bb3c04cd084098570012e1da025721e04a41fc093415012400f024305e047c22408e48e811a1eb022f5e604550d00896d78110763021c2a0042edd8084aea810706c020967804099100800c200fdcfc01f715803e524c07b85900f4d0801e532a03c19640771aa00ec08501d3bda039ee2c072caf80e376901c2b52037d07806e96480db1a901b217c035c02006a7c380d2f3a01a1e44033bcf80667c700cb0120192194031c6d406296a00c34260182b5602fdd8c05eca700bbb6b0173b7602e00f405b17880b45d701651de02c30e00577d980ad35f0156e7802a6d28053fc480a63f80149130028b5a0050934009f798013b9f00270a1c04d4230098e34012e8a20256a7404a08c00927c10121d32023d67c046e69808c435011578a0224e08043db680863850109794020d0f0040e6d80805a600fdd3c01f5f0803e089007aa8e00f286c01df82403b404007523200e790e01c9c1c0388d9006fc8700dcf0e01b4ac4035f02806a98300d2a5601a03f003367b806591b00c8ad0018c778030f3e8060b4400bf068017953002e946005bff400b5b080166cec02c48d005772000aca9a0154e8402a10e00530bd00a3f0a01439cc027ec3804ecc1009b8420132e98025da8804ab21009362c0122cc0023db78046bd2008b8b40113418021eeb0042eca0083fc4010447402013e003f3fe007cb4600f5dac01e4ab003bb630075b2600e7f9401c92c80384ef006ef4e00daa0001aebd803509700687a800cdcc80195588031e50006242000c17c0017cf8002ee10005c4a000b5abc016597002bfcc005691200aa594014f3000293790051162009f81c0139bd802690d004bd7a009522801253a802407d0046d44008b3900111a180219be00420ac0081c2800feed001f4c6003d79c0078bc400ed18001d18a00391fe007023c00dc1d001afff0034fbe0067f6400cbf6801901b00310c6006031000bc9f80171d3002d5000058d1800ae12801551c0029c580051d5000a04a00139ec00266b8004b38c0093410012038002340a0044fa40086f200107f5002043a003f16c007b57800f119001d73200398b800706c800db99001acdc003456000662b800c76a0018524002f738005c8f000b4820015ff4002ae14005392000a2d60013d3600269cc004b2f000925b0011cd60022a340043608008307000febe001ef20003c2180074cf000e2d8001b86800356c80067a8000c91000185e0002f3c0005b88000b150001575c00298b00050640009b820012cb40024540004631000879200105bc001f918003ce5000756a000e248001b3e800347500064f4000c2300017558002cd6000561c000a5480013d100025fe00048cc0008b640010ac0001fe20003cee000745c000de10001a77000326e0006004000b6a80015b300029360004e30000943800118b00021300003eb80007668000df40001a4800031700005ce0000ae40001468000262c00047500008500000f7a0001cc4000356000062d0000b6a000150c00026b800047100008220000ed80001b08000311000058c0000a0000011f8000202000039400006580000b3000013a000022400003b400006600000ae000012600001ec0000330000053000008600000d4000014800001f000002e00000400000058000007000000800000080000008000000

private def cDen (u : Nat) : Nat :=
  Nat.land (Nat.shiftRight cDenTable (Nat.mul 27 u)) 134217727

private def cTableOK : Nat → Bool
  | 0 => true
  | n + 1 => (cDen n == denFast n) && cTableOK n

private theorem cTableEntry {n u : Nat} (hu : u < n) (h : cTableOK n = true) :
    cDen u = denFast u := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨he, ht⟩ := Bool.and_eq_true_iff.mp h
    by_cases h' : u = n
    · subst u
      exact beq_iff_eq.mp he
    · exact ih (by omega) ht

private theorem cTableVerified : cTableOK 1652 = true := by decide +kernel

private theorem cDen_eq (u : Nat) (hu : u ≤ 1651) : cDen u = denFast u :=
  cTableEntry (by omega : u < 1652) cTableVerified

-- With only a cubic exponent, the shifted degree is 1650 - 3*c.
-- In this range both order cuts vanish and the remaining counts use denFast.
private def cCheap (o l c : Nat) : Nat :=
  let c3 := Nat.mul 3 c
  let k := Nat.sub (cDen (Nat.sub 1651 c3))
    (Nat.add (cDen (Nat.sub o c3)) (cDen (Nat.sub l (Nat.mul 2 c))))
  Nat.sub (Nat.min 30000000 k) (Nat.sub 125576826 (Nat.add (cDen o) (cDen l)))

private theorem cCheap_eq (s j c : Nat) (hs : 2344 ≤ s) (hs' : s ≤ 2511)
    (hj : 526 ≤ j) (hdiag : 3000 ≤ s+j) (hc : c ≤ 524)
    (hl : (4649-s)/4+1 ≤ j+1)
    (ho : 4650-(s+j) ≤ 3*((4649-s)/4+1)) :
    certifiedSaving s j ⟨0,0,c⟩ = cCheap (4650-(s+j)) (1650-j) c := by
  let R := (4649-s)/4+1
  let d := 1650-3*c
  let g := 4650-(s+j)
  let l := 1650-j
  have hg : g ≤ 1650 := by dsimp [g]; omega
  have hl' : l ≤ 1650 := by dsimp [l]; omega
  have hr : min d ((4649-(s+4*c))/4)+1 = R-c := by
    have hmin : (4649-(s+4*c))/4 ≤ d := by dsimp [d]; omega
    rw [Nat.min_eq_right hmin]
    dsimp [R]; omega
  have hgood : (decide (1650 < 3*c) || decide (550 < c) || decide (j+1 < c) ||
      decide (4649 < s+4*c)) = false := by simp [show ¬1650 < 3*c by omega,
        show ¬550 < c by omega, show ¬j+1 < c by omega, show ¬4649 < s+4*c by omega]
  simp only [certifiedSaving, Nat.zero_add, Nat.add_zero, Nat.mul_zero, hgood, Bool.false_eq_true,
    ite_false, Nat.sub_add_eq 1650 j (2*c), Nat.sub_add_eq 4650 (s+j) (3*c)]
  change min 30000000 (kFast d (l-2*c) (1651-3*c) (g-3*c)
    (min d ((4649-(s+4*c))/4)+1)) - originalK s j = cCheap g l c
  rw [hr]
  have hu : 1651-3*c ≤ d+1 := by dsimp [d]; omega
  have hv : g-3*c ≤ d+1 := by dsimp [d]; omega
  have hrd : R-c ≤ d := by dsimp [d,R]; omega
  have hw : l-2*c ≤ d-(R-c)+1 := by dsimp [d,R,l]; omega
  have hz : g-3*c-3*(R-c) = 0 := by dsimp [g,R]; omega
  have hR : R ≤ 1650 := by dsimp [R]; omega
  have hL : l ≤ 1650-R+1 := by dsimp [l,R]; omega
  have hZ : g-3*R = 0 := by dsimp [g,R]; omega
  have horig : originalK s j = 125576826 - (denFast g + denFast l) := by
    change (125576826 + cutFast 1650 (g-3*R) R) - (denFast g + cutFast 1650 l R) = _
    simp only [hZ, cutFast, Nat.not_lt.mpr hR, ite_false, cumFast, hL, Nat.zero_le, ite_true]
    all_goals rfl
  rw [horig]
  simp only [kFast, hz, cutFast, Nat.not_lt.mpr hrd, ite_false, cumFast, hu, hv, hw,
    Nat.zero_le, ite_true]
  change _ = min 30000000 (cDen (1651-3*c) - (cDen (g-3*c) + cDen (l-2*c))) -
    (125576826 - (cDen g + cDen l))
  have hg' := Nat.le_trans hg (by decide : 1650 ≤ 1651)
  have hl'' := Nat.le_trans hl' (by decide : 1650 ≤ 1651)
  simp only [cDen_eq _ (Nat.sub_le 1651 (3*c)),
    cDen_eq _ ((Nat.sub_le g (3*c)).trans hg'), cDen_eq _ ((Nat.sub_le l (2*c)).trans hl''),
    cDen_eq _ hg', cDen_eq _ hl'']
  all_goals rfl

private def cHead (p : Nat) : Nat := Nat.mod (Nat.div p 262144) 1024

private def cValid : Nat → Nat → Bool
  | 0, _ => true
  | n+1, p => (Nat.beq (Nat.mod p 262144) 0 && Nat.ble (cHead p) 524) && cValid n (Nat.div p 268435456)

private def cSum : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | n+1, o, l, p => Nat.add (cCheap o l (cHead p)) (cSum n (Nat.sub o 1) (Nat.sub l 1) (Nat.div p 268435456))

private theorem cSum_eq (s n j p : Nat) (hs : 2344 ≤ s) (hs' : s ≤ 2511)
    (hj : 526 ≤ j) (hdiag : 3000 ≤ s+j)
    (hl : (4649-s)/4+1 ≤ j+1) (ho : 4650-(s+j) ≤ 3*((4649-s)/4+1))
    (h : cValid n p = true) :
    rowLoop s n j p = cSum n (4650-(s+j)) (1650-j) p := by
  induction n generalizing j p with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hh, ht⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨h0, hc⟩ := Bool.and_eq_true_iff.mp hh
    have h0' : p % 262144 = 0 := Nat.eq_of_beq_eq_true h0
    have hp : unpack p = ⟨0, 0, cHead p⟩ := by
      unfold unpack cHead
      congr 1 <;> omega
    rw [rowLoop, cSum, hp, cCheap_eq s j _ hs hs' hj hdiag (Nat.le_of_ble_eq_true hc) hl ho,
      ih (j+1) (p / 268435456) (by omega) (by omega) (by omega) (by omega) ht]
    have eo : 4650-(s+(j+1)) = Nat.sub (4650-(s+j)) 1 := by
      change _ = (4650-(s+j))-1
      omega
    have el : 1650-(j+1) = Nat.sub (1650-j) 1 := by
      change _ = (1650-j)-1
      omega
    rw [eo, el]
    rfl

-- Keep the packed row fixed. Each step reads its own field by its direct bit offset.
private def cFixed (t o l p : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      let i := Nat.sub t (Nat.succ k)
      let c := Nat.land (Nat.shiftRight p (Nat.add (Nat.mul 28 i) 18)) 1023
      Nat.add (cCheap (Nat.sub o i) (Nat.sub l i) c) (cFixed t o l p k)

private theorem cHead_shift (p i : Nat) :
    cHead (p >>> (28*i)) = Nat.land (Nat.shiftRight p (Nat.add (Nat.mul 28 i) 18)) 1023 := by
  change (p >>> (28*i)) / 262144 % 1024 = (p >>> (28*i+18)) &&& (2^10-1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (p >>> (28*i)) 18]

private theorem cFixed_eq (t o l p k : Nat) (hk : k ≤ t) :
    cSum k (o-(t-k)) (l-(t-k)) (p >>> (28*(t-k))) = cFixed t o l p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := ih (by omega)
    have ho : Nat.sub (o-(t-(k+1))) 1 = o-(t-k) := by
      change (o-(t-(k+1)))-1 = _
      omega
    have hl : Nat.sub (l-(t-(k+1))) 1 = l-(t-k) := by
      change (l-(t-(k+1)))-1 = _
      omega
    have hp : Nat.div (p >>> (28*(t-(k+1)))) 268435456 = p >>> (28*(t-k)) := by
      calc
        _ = (p >>> (28*(t-(k+1)))) >>> 28 := by rw [Nat.shiftRight_eq_div_pow (p >>> _) 28]; rfl
        _ = _ := by rw [← Nat.shiftRight_add]; congr 1; omega
    rw [cFixed, cSum, cHead_shift, ho, hl, hp, h]
    rfl

private theorem cFixed_full (k o l p : Nat) : cSum k o l p = cFixed k o l p k := by
  simpa using cFixed_eq k o l p k (Nat.le_refl k)

private def cPrefix (s : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n+1, j, p => certifiedSaving s j (unpack p) + cPrefix s n (j+1) (p / 268435456)

-- Peel off the few exceptional offsets, then switch to the common formula.
private theorem cSplit (s m n j p : Nat) :
    rowLoop s (m+n) j p = cPrefix s m j p +
      rowLoop s n (j+m) (p / (268435456^m)) := by
  induction m generalizing j p with
  | zero => simp [cPrefix]
  | succ m ih =>
    rw [Nat.succ_add, rowLoop, cPrefix, ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 m, Nat.div_div_eq_div_mul, Nat.pow_succ']


-- The witness holds the original row and the length of its exceptional prefix.
private structure CEntry where
  row : Row
  cut : Nat

private def cAllowed (s : Nat) (e : CEntry) : Bool :=
  let j := e.row.first
  let t := e.row.count
  let m := e.cut
  decide (m ≤ t ∧ 2344 ≤ s ∧ s ≤ 2511 ∧ 526 ≤ j+m ∧ 3000 ≤ s+(j+m) ∧
    (4649-s)/4+1 ≤ j+m+1 ∧ 4650-(s+(j+m)) ≤ 3*((4649-s)/4+1) ∧
    (2008 ≤ s ∧ s < 3012 ∧ 322 ≤ j ∧ j+t ≤ 1063 ∧
      3000 ≤ s+j ∧ s+j+t ≤ 3420)) &&
    cValid (t-m) (e.row.packed / 268435456^m)

private def cEvaluate (s : Nat) (e : CEntry) : Nat :=
  let j := e.row.first
  let m := e.cut
  let p := e.row.packed
  cPrefix s m j p + cFixed (e.row.count-m) (4650-(s+(j+m))) (1650-(j+m))
    (p / 268435456^m) (e.row.count-m)

private theorem cEntry_eq (s : Nat) (e : CEntry) (h : cAllowed s e = true) :
    rowScore s e.row = cEvaluate s e := by
  rcases e with ⟨⟨j,t,p⟩,m⟩
  simp only [cAllowed, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  obtain ⟨⟨hm, hs, hs', hj, hd, hl, ho, hb⟩, hv⟩ := h
  have ht : m+(t-m) = t := by omega
  change (if _ then rowLoop s t j p else 0) = _
  rw [ite_eq_left hb]
  calc
    rowLoop s t j p = rowLoop s (m+(t-m)) j p := by rw [ht]
    _ = _ := by rw [cSplit, cSum_eq s (t-m) (j+m) _ hs hs' hj hd hl ho hv, cFixed_full]; rfl

private def cGroupOK : Nat → List CEntry → Bool
  | _, [] => true
  | s, e :: es => cAllowed s e && cGroupOK (s+1) es

private def cGroupSum : Nat → List CEntry → Nat
  | _, [] => 0
  | s, e :: es => cEvaluate s e + cGroupSum (s+1) es

private theorem cGroup_eq (s : Nat) (es : List CEntry) (h : cGroupOK s es = true) :
    batchScore s (es.map CEntry.row) = cGroupSum s es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨he, ht⟩ := Bool.and_eq_true_iff.mp h
    exact congrArg₂ Nat.add (cEntry_eq s e he) (ih (s+1) ht)

private theorem cJoin (s : Nat) (es : List CEntry) (rs : List Row) (n a b : Nat)
    (h : cGroupOK s es = true) (ha : cGroupSum s es = a)
    (hn : es.length = n) (hb : batchScore (s+n) rs = b) :
    batchScore s (es.map CEntry.row ++ rs) = a+b := by
  rw [batchScore_append, List.length_map, hn, cGroup_eq s es h, ha, hb]


private def entries164 : List CEntry := [
  ⟨⟨527, 163, 1554641491391448646851394010439098237057720929648090940948589076261448707627130592682234061004106826335530218177779474477233328668794725355444334556724300225634913116404877595852395697129200860616275850188620486919417890940178554383891809023428257087286396252070901807020803922091838595319586362155520446093302929139168609979349560655040129372110290516738548075641473610630712516870743714441951994363056788025076349057116677558122852121015307621018321000747470874525569217809700035170964148723095546276371154135222162948035943832401655388406307280813471343757115963530696161225898674804934932965920328640027141575818408683861933727700298248965846503457297198050155444739588896732217954767117110533097028758248188526610420327491934180503386609775702251147459307671087075775614427704910619105339986491079536671161996430613713205453600350646895776511222242221242502237644416014271943357914752028332560052078259253541104298349098735803292121725122488219076595495823668812698225018546668596869771552423854982023795040756734824351084240965628824219383479241815628465490831266855705560715738004732519860002518600263479646961524078397775335499859555316496737251224694099771516535909908575347315970694670882489853991792316051856547006170221899702902247644645011425298344266037542571744863754602041731585219883402810369757096535463047310077936829090802232954917201691630471831617568⟩, 8⟩,
  ⟨⟨526, 163, 2331962228399936720620419030786932744789314171497793797055452253147166304573138738732713572649550066644617275340480916198661938507789591938304076165570282259751708005011188861295131448361581713721424355354193630028427940472584478918494394090561674999187325137129936985937555935413172994882119423436010850123043511851233884361586355710938898837467000211255727234007313796854903652673025671848492512807319552730264946742688978199164150723333431918025860145454372690346224851628760945241352417008783288297324633321389747766170969403699453744012791005800126877188916037367180244291435192430333991390195039943305633317528959406258277506437409741588851939454052809546496547212162265574178889949757912613148978578710450323299166519601518429433609445610431451648496528786093804312663248213859555164575827140630407004415056007266858556302662163730393143162329829483553838036215109599151894882020578083513734938602911539271718621477396782048782048888780451205769973704442348774555019408605682904861637882006047424063289670070172063799604811998528411083663355788444407250861242822012287070592522079383583589333526222007159995418055609092297663384332040982415086247679072406502066334801300361693821737694153705989246965900067700497277342537948491983906155532688066197919585460589374797027230877681496836345342131959081831551151579856120866068123481574708605043407829073537505379227648⟩, 9⟩,
  ⟨⟨526, 163, 777320748591469761552905654558435660545110082814141552693730949640124361772945832268553540225285097891759318663815908094328613162517261591666641754622554076443952289578151882126090333344324747642000098294814718462808550560781866664739620355899442573512518054655832375239813872268799518201283735752417766901490940946404187686264526299946654742317489147498891413194008204262230633583013840512102798268082459870817887463267820848180773409172152672697897854615224939622600822743159203519187366452286397543418011602654729227998426547382296493551462543887539981196293076098421154099660481839938243619678264988626703199009295356228766426735777278721886467792802358434887024718358049014614152767701187436047225582274127722304125083450167095306375482462825173882428840189312901967168102886299279813527057824630191088074401861697935967073538284741572243239249678849937049247134518524422156273722401083681381024151155432366550398433568284774394477820757383231772533542016287354727110191733643667362840758054906733242004359674025803841842668183111765204297976654549908523219951601849991644936085717801386078872594947853753579377956104798843660878162834362921429391573455394475825502336801896409301907038098426856531651105643558582501234274286415280057241618205071222028727489596940177626508444746121436909232492211006775978212502379221013203183033307629164270177686953350278078791712⟩, 9⟩,
  ⟨⟨526, 162, 5791490865466924891113868965288082756524046829174766647213842179018930484503647227640526309707126191556068541058485605439172678506626605907914009530049236565919569378434347993039855625417697187284557611534681877475323635319650994894572713987142199730926255099731141553313444856973902458482944011323465776027966007333991833822822466040058625269028185732335283436610740523528720173806025774206765920423944845863276175669534817654912383036836385825429543689069885706799543501379085154728888939494827989823981726478238690396638689273788739029258374433707151066135747873869679883019232389511290767771892400468771588319762090697627726600400778905387223853683416002547355451858062588627679488222899014275216261954174821527027878277883979623946835049899010094553017067208278762286862567895868087294890403319517317105635063931539332646106096069013097743713915697820115826928855932469387547553350252018107185448265697717349421517419457279141272458043646612587667364552091545166203079309389653073246003136763796818747900394474774896807913057772768955856835794169642623682136139548676713855373623070651491144719160734329385770789669727825842091151475544927457863387508972604779004993863102708862121495799278006929588333835762871654014003162844783262311220456465274792048835715523959189755354301851018575865911019322837631822805296914269217489571066918696437827097615279325216⟩, 8⟩]

private def suffix164 : List Row := entries164.map CEntry.row ++ []

private theorem score164 : batchScore 2508 suffix164 = 949525536 :=
  cJoin 2508 entries164 [] 4 949525536 0
    (by decide +kernel) (by decide +kernel) rfl rfl

private def entries160 : List CEntry := [
  ⟨⟨528, 165, 112023725252543397380656234202080610674248670281395298423839488455913980350218359277002273279044724732607385198953211935306910951918218324586208915688788347823235382234106317271252632708470212948299873737488146065958273350827411649764432331517000210656525478003820654875132439406903962902811649976605963818548286391285012961257707868632626246493445005001106671831678877253319789276056399956851075520094217730591105560115904747419735772385575563031388376284181390096159551294244414309414396185226105203931951578550748367426915104150231666132007789408697030850470207530831200496388589695649104886494342838521510323137197312564880627674487597421108618016443150887392947325905228096328456262523542633932400204456419272786215063147467799162893515631547277485574077398349016965198948357750732059459243253569608600350825204498066974700098434211989302418778183246018869272054751132168969060701450130475761993480250063483754676525456193056239813653959028609782586842948413181041578243056613945201959534462677024269459199036795355350922851487492300160972731483901614744687420820010320795588368836932628148533221212202533763584641854276530257580297591378945392782736467087367719884926836852149608137987546726695272379720722176643410843090841536012253441785010698357850407998906417193841797474962942210265372979113990374918019870548115453982174682447223281677152497445353536863939949812319408275593216⟩, 8⟩,
  ⟨⟨528, 164, 625981344155313163970886785440368330188851023846744101126287492041386038714964629346346785689676305268631948906772503723820201205046791073029992206478267983976668819584288241179308348564504708754014754224629204569887705444012513516301131613631843212347401407791409709601309852053180077492064903440050662064588708884587261115814522611308959413898284639683666761324897029311440919172412175432644324761453734825965920404603550533645257268107467335863091513737896871110742797806348539243095816856384644001659496762304030515221525918703836325504729060847626675848720501823147123950880622767233212399402496150683475647437650445283968109859398496147230937908632127372784156067044081324553745358108936987979139945087698461070149013483130423047621824574577678728327225104180310223245254955379848495376294173852989132316955621761124466928099833581716511789631731126345040265972426730644212749460430525685385463051339996506532163266361689368843188232691671875853659965728534596030333492449925605911483379757130328842808725619656044059934992911970069141778741525889102252598085717998186257212935628110394684253473471449303054768724032117717596457353916158175072426528096151062939550448084825591165887168714687222419628017757163046922144540925157668071118654332675734084353547916123805655766507386417859190639956196172714595202202852415155286468836482452901458996885613866372772591025044592640⟩, 8⟩,
  ⟨⟨528, 164, 208660449606412540256920075560402117192058667403019009684629165902653319110899022440052624345005571902154099973428440687959273467029801648574175314750074784485145975441913498485267442962158464263367347146062459159066735869158899673255566700959434791703012785918002290967757023996483334601780695548419287200527959104334239424803219640137839523060761899641758895787593793335342666767470370599060541669346819240049876607329905065425122224852547969758456036213854918682728802927900177763456187751515512173668640036350214897748255846078528542753105636158609293226659028144060901955152701833996499441468104237435793642885642872961604152363674883466496564046754652865313127478734934303652996343753808689257587483503156847528418166897492342670219053037883421903083110714350174857796284578081748798236334524452175543274681625704373826038525708832874516649440791418167111879093357264556375713028740340723019244508908849526767674497196955157442895719746430884163793527831091564732782869720229104053583713606708839813758270873434442294096814524869310135793897668898115777156169649241432142843671948929262232632862384761434601928628060457363421623943216234809106946894503794371194073943692702651802953288589729722960341301433458146684633085529172967479336767797735673892011270953064428821159020123988804521142461566231096732982088315318142154478464513337679949141877256914468258438900927692832⟩, 8⟩,
  ⟨⟨527, 164, 208660450383733280161153571275397215719462702891788781881651189484446011053998850925753327682673159416658726336046616921325725320942573452137258366702583490377511524892736909008322071428221870034555387816876096087474303085883396987012412981500963629909620862525029153451104968649396657953335300416826084244640903304144140907108193094297833106361540004457704904778424761001344398398284836655445079502743544033139437611265334402866538637720838004737446505044917361078392762837295535628486982706729566524131953802778025421816829877284679408247681181717390412932665162468888180538449618715825416594084217020237928230679779358631680121718650003282372439727435322970760619746144196847947362160555147395561631914311520146100019163435914040880295225028933478960041224885631465077162434325976018923788035743351081593741319309589591836392958712327700520200449369014491156283164597102118740867515086827574848224496677743486954826049017643352361841490651006657912286651023540205842098474325973274285205072580798562872525399113927915661068685683179536789522664726931375728594615677430373259480241631677230942011933158731440325320311560165216440266574943882394567844818182358456278781914579659760644791123315009388905774273294618129992760889083912584157248139933598867325225071794139442831774206049385826187996790309152555071485557213382332775541348582988118628955348156758257841607326675507200⟩, 8⟩]

private def suffix160 : List Row := entries160.map CEntry.row ++ suffix164

private theorem score160 : batchScore 2504 suffix160 = 1900764264 :=
  cJoin 2504 entries160 suffix164 4 951238728 949525536
    (by decide +kernel) (by decide +kernel) rfl score164

private def entries156 : List CEntry := [
  ⟨⟨530, 166, 15035569969510395009405490563413712390061896665562954410778690922374289741468863846402307528216186081686494588990854809293619493056205338675861967766390781440755164561668937789381228191133352116582604666498404705995748468718649245271592355919134438030013627743149139492393502297726355615419500483532112309814372739235214937844828350892052270416313033842188086609277280650897125484395475142346882259755614248223701691678407826099931094185485337989335902241175259686545866001167556796096871950774067639429008985308657912971521904840077379679451549718654843870366288854587086488364305273558216902088466867031337895550887151316099247442680429385676137260494803927578302204971289760294527642202419745043430370308591809348639183999915201251724090047185561272757009144842460399882707371444194538308626544528478109272684584222992755086605642155449646065194140174545307089449176074979396967890669789570744788352876424879867546982837233012511658743923916424189340265222522330108489865162279148879299606453293578215087290755722875296759777126636024682223585496102440980438001667741941379986044851290411575158796244932776116124256183275093545865326908013203325618980687134734413939094343584634621576165396381431959759811948485855115646604844382021298733033662885974033485508698797927972655509892234806395036818296996118806177188180692592348255349560166489327339483829920185114329813881630688045469176818569216⟩, 7⟩,
  ⟨⟨530, 165, 112023725461203843877785806154830502261713398612348048088656151105059016551802278805724278203321863180183213444373138593328534656838433664967952668671824950353503349033206819069573998231031523820159693031385733698004704244576739015651604603844110686067837063558094829401871869690136322755666651335373708449518815378862749314634754791119162825624701797901221421714776753067822535791091747174870432415210396492540366380940822401654360095841409980806866320706759353193269543737599322039094000298891232781922789495568817568183081198118715311349406700792302920438124784197955318387788694296114736450808856834322515996954884966697540343198073945650216411806695047058910185092524009058341378039328629249515140907287247046757264272894196468867113833279978391493243238139875485932131621647913163561771658960573185388173688286408251847653216082591100075007334521171929483590301751352114768293461170267662871421232416724400554691640052013131883809746508942502405597272490504167642057160944856569415230593373725819305923825493907707932939242008578566359343351563932720220136103467092783518567209947038826462512884778678291400936639977862135256315641421149395507455069623918083707061825698641940681884510604234469976699514390937146008966493293767939243560689471420869866269797288715144436700573531515576492036426129782100815353744504031508834824211021337508621727616989350196495831547430136455398166528⟩, 7⟩,
  ⟨⟨529, 165, 168035587565824423993327764974059433522202790702367626901145096513225832174485184302457581350742533497180419700958178525365373793174737946260830900266681543589472492099872854607713185906658345413673214481538055619022675102980523438359108219827656575727074579126781824772646425179906528401089575621467578022360453321317697498820782156678496834956076407391728887652742802941053672254996404209532012964227968342335394679332176103102688059514568198409224279893944931950500508093507023898767367502294594445774887746057478470106444076766268437848463762282496692856432610473546427369617052934714594982388314067065941421337497436054677666633562941317142841639699484579687278597509197398315382277584134267263295755310534679598109667290958774763390819996117433421909691406193567558324860458329716740597384654406624960072471441350316367378736676825206150865061251834216666687013062025823399366229509821487887238164402122025557214834407557012844743469568617319603751018987117455957590905668895830072758335603818087395137789366867928180431883050565451269352477363116519808774406636500950924088821056279149941562467826467657177592287214576988303337781664762902098153828275246043097015551609905367627314061554394737482125017647152066627539217277537091437402088045634161678193809464976693916895134336679405565989216694103198072748685259034859649604540673597889914654061052362385389913459455980049348433920⟩, 8⟩,
  ⟨⟨529, 165, 56011862939262370767984697638610997871815707963081743641361846339978395325447693658649758880048272016095523208636851359441301282550845848186858135863754593208639401828948298220853308898855114470757887379070360223676170668030113616208401090470089893876718879253818328095919937475372494320236685297915594205004776136067041979992711136486241683275489839521512425824334990200827109838331104835090393209714350466620796403496172434741590304730425629876094487041985899378927326289486929331544989224424902989594576446207034454399998321493043004661964880901101665656044258714172615263926807852679066791607176841049696444067463461585649832554037722237269798544287779572599924988747519983064338227094703343795499022755098568388776710464814003057293826732686852527843606001022397379998315450606490536232083108489565237821687942923787942910342544575964913192340052247914651008563570165081467811990910487526181899744776173098692030394722979936378161265709956845822881689113597074754117895766059778102155744555995066030798036250921392553057945688237151129690262609066931610599847951253869728787699761882681148699474072644739670891280906025926250054385358009603989589033001182483180912914482897542954174551658689949848925967994258541050529071023798613787254437190291459766516533527689977773913818875896643957536883908247466124625954694797841517458279693024975338474417354792812173280550624752663344975872⟩, 7⟩]

private def suffix156 : List Row := entries156.map CEntry.row ++ suffix160

private theorem score156 : batchScore 2500 suffix156 = 2853575461 :=
  cJoin 2500 entries156 suffix160 4 952811197 1900764264
    (by decide +kernel) (by decide +kernel) rfl score160

private def entries152 : List CEntry := [
  ⟨⟨532, 166, 45106709572460009479246726822722781169872146815660116067890587063179184176916944843350963823189607570342358831312180050264792334091150821494107228893365355365364586017716399222962946585483100632756664037244699354467244636735833670141352922874732836769881555790020813706576824014290698056127970268137130003519194360759399019722623703509070377077743074010549558681006698509434794736549439740364774936176105265179274525354998982658465669726052003087657562753245573911230964771331268829776333595177703943882494096578044371958398816760909256889533185075959037000319400305939513354075795274035456376573050786525428043353763961284790726194105121940352178607129171588603387612822669627547128504974658891193471134615554469990319868261070775001091177947252886986908847909864066001990596637951854723281508976119289561281516299019685740745180863256621474204072423894023203674832109514566927198564959896987569525902123072504557136047795938088305769395887861384537678825353434309716983236227495871725347613155508652292836899231024885242099068362370623370872825544180084742905393843833670052946467203169521427921607818948751199437681349153019259647348994908410789134301747928372833558102186675597978321891611419494994059689261576638678486510597084436078263688237900011280018718104189325251308807434436564580334221423532329854787204657892894353446138565101267113932383884174721812000230886582252258226234915295232⟩, 6⟩,
  ⟨⟨531, 167, 4036080080985428981089887148293657579399855003878756091467400735950855810489777674150374697130963864761829349160034503584355681671244202717454438477620030297480863376358793448071937991530045350784756130085191450760173042940189205626158547981970520748713057548228451393884299159140768297638320226518773805528348071123966358315099512932542217692216069160725205705037628758197685734836504039626837517037672014928955785185115698303840743417722671115131841915495554722491349577844236168395524984445170936710633502320949681550942472621633286117286880073605843277295036661102328458361352256754203755474046490001314969828611170639522876992927389340947230219107268987228700203297596006100926251315595495119486690610195129087505080517909690278534407729647651400045099811103696257325114668650717797877111200800550361173020139042158976407457786041914342675308003032575455105079915329425546930110658212839557986607342624643036915112900367631712501304273769648475490690857879419980485503169546253495803462744474137311884617434172746252823405020616701429465654053689840714099785662492639760350585468542003136120452979813704176359369418278977847709198113942754050142348723444814870271416176218900428609775031731668015745668299543405628267337438450363862204278779907976253393637670569557353219630848272125002531634946837517713033206079866654911483103934115685138233323184365288006124331981455314581940389832687473930541056⟩, 7⟩,
  ⟨⟨531, 166, 30071139826997064140286241145499532477332067497815415519388342349091978715272381941682373167235131712809977771439541358601319279319214929560603825496079910207921101437389684001987539759206867456469696750039372492071120003908814439109834226604093955949444997130895776405889964786815562899986182760645210456843278704365202147579190367034559365006657182335066328766380545846227731571977153722281034352423510876582841617378084505824020524998218347812649540296497771741075544406674078477834898455364775571840574362373861344923328355788264565180121486537382955187010749424176036773918102635340879297668308843133394371804250762509586532467409427470313441048168357096501207308259575145817433756198286666414930153337383165152071234853771439323656394951893075401187865002055591932906065478590260944632602724947414461902423555427852708848783166760993826099839960948515937495015789289560111674563277802914823580311352421268727015003742617498256670330710066462611272102254350030889335266243850603005580396136142301068638268721923356670876568137996582264807282003216521618519567418538996046093201292562558139894548408315040534005596596043692655923573366994876894000681245122999263059033645181847640139546819668615438011509827593650378375181036120183834705170793894312095253638175699403488307683745204363114586807134223657810412834276694805198531827555833475879646771199929272809705596957226809984792174165757952⟩, 7⟩,
  ⟨⟨531, 165, 168035587565824423993327764974059433522202790702367626901145654213505699378540384937308089730750143085327513283641532251933084056392345301433761916092409247126083683876493537357056161572957033295348214145862279249623826285848798069956893350801923856207674019791518327259099149683239157732524325195175651411292599825245013097558542055050224303274594636357537601708358528194798970771126227538890939189593394130422512541578429012092014360434640664537286370411342023003394579142506335370551616362145421630673330276200398280316528017387354530128782248386689022781102237106524684968230510750884845612103236373302533254012182379573851469318228352385626787161916950269143663528975131176274467376485150401786889829757250110113221863426165480257353418002398545728729505190580370485850457442465395570484452640668228922899386261931400243009492379466300657886994036792374971271633983005959419366722221501862361402110406815542094367682719375554827870235923865612015941650567233368030812478979797526850735926578505092177981166858925329047764622559169756770017813421359848786023171231161680866775843995008636661088767746995183273285358731047795346338180211569018607220362320414603544817420146414831339177535805173529059035876157729187730107004989731811559689691394916429710492463343607011655283663716728489805858568906109290762846302080033985684895142747190498927659008133786686139123377281551630935789568⟩, 6⟩]

private def suffix152 : List Row := entries152.map CEntry.row ++ suffix156

private theorem score152 : batchScore 2496 suffix152 = 3807362729 :=
  cJoin 2496 entries152 suffix156 4 953787268 2853575461
    (by decide +kernel) (by decide +kernel) rfl score156

private def entries148 : List CEntry := [
  ⟨⟨534, 167, 12108240152742867630314055337883995089572046532924543322766985901219352192408643085742276502365592865456983190520160978031377740233457511831665468756623264087400592027543568563068109256207159771954066236501280911115003154447211151683403348522988229083869084464594157360394015347105229746327465092942716175736754992390556033886768465811018214571993962129228427935216374060992870701968490819842828019268336243915265554331201076706326934480356746475516062712440607262310423875538581603183692485912057148483811107886290297102323579802903728120668951575801171274361269820733389441903952126149656719331841622147071481250097061231506562257994532239583614813128109142421023678515573160054164698447625174711691335742259028421890289026704596444630639558471613757638261511323236949963203748976798221701429824324569099222446970056662877877189277041935204325393858518904849778565552146180474269973198163849937865281366448189865859266991949931288559374710014533920233949450894626067794353233765235430705869907311306385456257699097536483611538739551049386838469065489186360850731303676719078683846391521816245188551462398456588108930906997693422922580795923695137249878026244692299262058349841129655578800896776143294835420570103155604869723206266437121756115985318927793680760714248585320752129418979147192082785997944893053207245200628515124709519041919234739915699204136454793214051127685210565393931297669162152758272⟩, 5⟩,
  ⟨⟨533, 168, 1083426996991840542858909376154078254692858427763952403108526341395483700157772993530403625906866716470831171415870209237670533597280846198138130845158886685557325818089110358692255306325268738650708898725650273664349985627605051940843971735413721523085132387481544493302579243865451747427960439714651513643705516385512891842779230998922028860287275186674568977740271607867980009709105585938888428344452960785741148606738252362165673946523864038692496126126860850589126731075152256822349095815069071165846180254461945903873661484708626148152678577222704242531741294857714234514357846231789285312986124090151541625040562402077575163335286796229535654983826185115074485495643828364483151410274165107355344500863522257913882099982000714549437904895633068094102691058146029191681395239146404406586387301422765732696839288222403573518293801667173590985841194947229734523315386546428256495387834518643042790615841455526262636283195064548863395296884635550312818463041294659980216913784804379467949773483965383053255843434915927375806320432113035844723470656890694254878855587082541165925291969943280103770316318010508661859280848842721615374806242460883549362030439114206081990701554544869109539774796384094804264937685101092312034059345908281992054492070504493099877817523113548108071619468969669660373313536128143529944680963935513812588875066598571009711123424573516210392744803582145493317758465102733716292821323776⟩, 6⟩,
  ⟨⟨533, 167, 8072160116864148277696040190778535888054601406670425431882741378669937709625111040634452055584322242892391592806316078043648173857379693269179013316130960959993042778308105044964793875644642670884206977948656126168199373011798883274178902471083478339324234011997526983379824962376009431299304543490067413932585607059101731115556876188896613127368991650001835171270910802322209862141193944195173611663874504268234221799229604046360763671156534894219564049254099034103940586715529097011601598203356560809561820737932817574473485595290233876051709489701027645063235911294422440025585778036456139571241023529755753833407496473607787308292797919174274029948108375717128583634720276835931004090272573237949675016702317422121367475335103046811729221002597274635093132398891363615630916822337761873232934196942714384386614649013963926078994512495069667080076383856544233795277361600886542549006728660960118333804214100456535704143091459774446397681485673601644299297027242858732360426516908292819143479666412268968682364449132377199857311216932525017871433247759618306392362702633626680205167420581613723802279591714057008081805674097668645320062675623250684046462997838292962744078610024799148566170264307616427493510197264418985906985483338752268017057143365659380386788679320875428304094987959658846702702036677260665044626782284829547543130976117409691738534420161601009487430198676624191393100002358080835584⟩, 6⟩,
  ⟨⟨532, 167, 12108240152742867630314055337883995089572046532924543322766985901219352192408643085742276502365592865456983190520160978031377738742855884994061445992359643969802820895230743443281904904553387816517577976089150494207072297317319126161546401511290374780895488184426454479747608432359984696152014249250072025547354527696715843951780021052614311951989261498435828344519575084298086158187782349796124498546384805877324280788271660065400249086647729830174373896865729500650878331675914886393250737653845828712912742654312990470426761372111595260837784428817359841101792410864601222662165321919609196977853376564709816141413409765430531892355248919299749183443465086770403374546214432444261726999512168654735531807653828623633345682048046112406200877977425938631757420407594263703367315512688211251578695162219962730946022337071352508378813628638597894215654460016791264768334912417482881443657158575395338527161021800011549425887410036248059299895454655196060737514973935450270999211341599973213518382827904543929293647524483645388102042209334332110715034487026478667028929036745224037639106031735063283009703655279650876886132380097089595531620915341690045675833739060672152887921273278442323641550318841236579967260976087414843654256168257834990214326334271632731976934838905317725654264320482523859480872788453210475736392998485667696441838000257848980269611666511814231778854923452260370010229927457138413568⟩, 6⟩]

private def suffix148 : List Row := entries148.map CEntry.row ++ suffix152

private theorem score148 : batchScore 2492 suffix148 = 4762156983 :=
  cJoin 2492 entries148 suffix152 4 954794254 3807362729
    (by decide +kernel) (by decide +kernel) rfl score152

private def entries144 : List CEntry := [
  ⟨⟨536, 168, 2166853985911520953818100729149171814288481278768351205242207520956643878684189124192893247492808005313197349958442483840883825011940472934601896271062464776089321396660020497970337274915393497974759561366922031323330301726373710831287419990375490532908565027826621799271196921475556991805261276451022093773822359421676400807515689996933349865250787926057314666863096495292104607655302764682844407107823107731910874053671273380410383377473546164853514248835587812818083212923213456701457533294201567238380004673877283624135776953204240787658258926806683021000536987466822377856246004442535398029028353470804386515953170115658034912819204146314119838682540011321405181909644927180204877243785419293468692520980692829338123012220695724195165532168118822298880356306726341097111917138093763032580728749655877023704062703754561621527103914339060567792523750892577265665436075336060190291112007262086647402251738793868391287004965773894170240358797831872593865253557183800822569979223527548889413086926969024303177213542356760331114419854634785210150523920267876437089523396931447800691489574473833490151305062059503410838499267828883448681580578570472877098553335617676903326385762750714103585687426456020686636484702489870197507751146117982506070966177884037068441760898058107270163859798586347453027448244037532972925505430155252408904713031269040567623508181326127313874836285227066090028941809044354907041053540352⟩, 4⟩,
  ⟨⟨535, 168, 3250280966759041323090992867834124296971033155918818800438711042139387761793813845063032791668382608170193422471657578410020905536420648975625795533814255635022693677685096159566210173575435298841330449799968934742563979727291465971646086100504258062381038329459295032782867431250166911012819137931612851772702323391159544409381353283548008713078415529216184633209838993446109995064145842150592871383628671940648306882392518319759191062236295219764798543773142743961661964649640296896663409033743674963635857747545355346775984167442774480036841355071180362822662880680329423252505194233075160613907454528422457691024072612389008816229359755091972142592450727681660574688605674229389956307256897571033471195555338664607520248795346632623746465659422280351410678908521652271283967027739687762163140342025537955922724738487599068382363912090257029770629107644124311065343241843821392269265243748346653559810361421221110636855925164050213453543453365774806980610366255774215125067849206491240366462372694983876727076790246352485705010817202968651617789100138271520889377216662209386036742716616839599920856526594539946992186176125389689111980337124717851794976574879043256132924458327494207362206945542337095074298286249677642528186899885963052048400872720756253541413406400563610806515530993687278200246731474028546436721361710872570109127898424175451383472552901538496584561326810749879536093065416339375557561028608⟩, 5⟩,
  ⟨⟨535, 168, 1083426996991840557894479233640747385573609009849763803142485273198863985696721384045223450488328435650818818765363362055458592031000920525096095131154341731433915152203101274253428602168132434299769844112924817812363953521234161841974200436465941374938544116865318383712756229049857065869532633103108615382729049795986475907687464744692356449976067679505363246643874749825263486592849408282041312708046417381343456819184230169114805689158899785659322546107421123530342984277837031759877216759259001803470252734694969644319849241326189296190476759594123455418389027316756214804319579985718238140336675745034907640758474434332740550100506626448106016932466067659946920216649769866959381028676561683315368708267755491302028737364493703962594839540406465190186774127906383504419318455160316724890632974369989613142660030207218206634852182646817362230506904558419324236572654438213723233748300850243563061476893630362009712549309345765550918010527475904493745918105518135345922802323983282260568117215310384926041563039584561226996669259060547012314605701500859368940203475464343088679308056848276353963667408356891681453927326319008515879617333448834632849896080434708254589565276825353763265420664137853529305604266638995817713955206975049205245809457694240586863183174850789739743924503481556299354391506388252227431147155340016957009406214444600004514599121487271260709011272463319533489527053763544758477484198912⟩, 5⟩,
  ⟨⟨534, 168, 2166853981875440932974951178005963693443194875756972581002782129415980223674125257035166493905196059249196559548789860209687626703877548531252086358011740147167418757628174743344626956447697138402525058875586468331708242668429197538292617922824827734852831516718930235611674861650948136264408153336351658188348489244678414221860971028377795708424532163390123104070981343311058895481755251388119666597741287057253072628160005129983262226909670877629070830396346558808817380375427522622439976420861712849557534002175131023544400266196807245523839368834278025135170014866154595638364619652461546652323952827139264128437099053441013115798663518179343982054868978006994619351789485238997072481884175626318487233770031061727944094787531388788961436457639819563207532577011293026080155721368721042632993325999797810390066251893741063748726799517114587839830331465479758429931370049920856013283831762044859929853568375274099643859673772856481333904772830136129695016283184087181898822178259061795427322006016549013852854221761965141125835831926978360319257541363740723967968992641889956966494773871469791171389059199516758771810303816952592969317302256934667118195042653387821552886044751558426946291424504596332476124499259045487435723484432168675423441696438680833155428864591517411745620850168717400997244540264477253574468859854505620195926199761579291905474000680887176795106291107316225935099843049818138656706138112⟩, 5⟩]

private def suffix144 : List Row := entries144.map CEntry.row ++ suffix148

private theorem score144 : batchScore 2488 suffix144 = 5718258539 :=
  cJoin 2488 entries144 suffix148 4 956101556 4762156983
    (by decide +kernel) (by decide +kernel) rfl score148

private def entries140 : List CEntry := [
  ⟨⟨538, 169, 581660436710149722044196456045767922745144017329524494235587102744419606000201306145602644175837421902779955715249927806237530994466972986014604188867410825282391774253072127180356857811589974222291773393156481655430926970854152195455809327321457887756315905908784759228493610513858827804935872922879040315784690555028901764480723143567829261159419741816833301712163758862460199001151550935934503747811249747587974361232150718564406357721859179285256394567874266243264220500825465088397639050682413170206339620199912293049263866054577580160670297290745001646715993278462634244329535087123042798790714295968050407301355613326985865055883053216075771673664549736943118129977506703199541666592566205898323094857330978216884170540829577011553235439094887594056440992324129222606306885060817064540196505426048460253450172951494640684706093295915846470375692995935173114601361770430002425106539512884208686683501227386778923253562917026924919288336283135908421028863795222627733692663320195760581853462302087723544707426153612801227100856526178277985616667588819560787978561371932896568492300534554898233811726874873288094995661381065302769849254521687057828796277936304532421074104892153261032642566224018425003501836422993724376121305438635359765970826879439288862081791542382920425357343537306751572665939463979347211409063774477876671331661707094993839431466866356436702864675134406932254886735578442071919765919094858579968⟩, 3⟩,
  ⟨⟨537, 169, 581660437793576706927796831126239979134084117119378374288292143323921659825057151478419770666244684148295329564052409043620198748999554959150539386953399265903386721071252474332767776655470170933999406423664908721530366126869058382955630034953408940705764403802692113053882335564870917222351403577020528859422048524715716686928663108766537331765237417417919113937640168712244367404328059100121268669161414259853777185449104447702687628625578982755815943007321717486223751094731217582379595225084117502730420801829285201024242257563307345081635709459199234380946672051097141285360697660926941723110257919220216311162356761528794990446621356528037938361432645074073897239077252986588570524184696558911210919627643612187225213724503140081810937142250361246745021126059039825721450579003031942052006685594615745888429943313220289924073422200852389928990681762707077056726955200230079942375306684053679330692865252251664850834400943066810774864666199088543213550944106113010359604992387044295810531617336833936639805594180455111795553415357519961092684677167737421251759792478809898100673565752162903680053218817790486958299282967171255822155233064930732911958076452683680185835741972348318927234545307559153988254837254889358300044747272289642971471279918096170953122022216401462122555403249312027732238951919893908590205921768996213990885478417612448373581319274298114824010861446472640561212319938333535516756701340426567680⟩, 4⟩,
  ⟨⟨537, 168, 3250280966759041323090992867834124296971033933239555808926795598656695113912104324362470340098225763226760889005655345872667431317433630551487060770918655140591829852778805947712932385637331122810010918997939085936269251979107964038119399434291642744451987919880811178921285644417586979627910165659968458809685953033692219577381648208706722351641574486637427690137119975467071363254700612912883425167179255338045745248989475446873107358536703938329529545897718243638435999289423581367358738015691920963592539992822575470797016453193318034553109912106147017696030973616263986836166986998040825231743817924686519163594861784261066119807245422645692079636289890674845408234608823366497310752540308403018364383011472819562999884337516759536135824844261457186104535361543345701772019139329813698553054454865623076028312527503708836900441125591603929126463820930488022083034070571467317284859857835085837844333178864956308642396996339808041314401907349429532941206142386206891610931880810602552539759995241967719043937681813848727970994357336079958584108606766931981744789521969695025063301040447212423439495035565358709491365169985120333448145228186664221678903397894773161019204873836155360697228249433509773533170181620772243645512670581486408654343975059775673311282202953319289412177494650223954301588637280781274460602068963774540068016894845896993427706929285954638961858080576294747710401574330382301944073420800⟩, 4⟩,
  ⟨⟨536, 169, 290830219980215348437698932964884564627259556124730615309584275772506189199744048009209357597856108935113014773418843800718373686646874140443864906050480975481458215898113638558136060031909960763371237048133039327219034014897672276701087222381187523984317603430633258232770444892169265311571295327232050441000008176334618992342704797856575623767920470860057129082293459738556401199344921167228976036989396003455886838116080521032167916664494087357529661862140497492621570153556267464530888563333389585320223243001729711760993651359227567432438453627469253279534187631291120150482729955692561678515124806953658529616042578416920311523433406636911103386554048721911869757609712339058142491872221176720414143195062298822888253594485580333350108599777636468828000365814932451802963860045756551690083580819519922070202005303130122035222647662329385134965327143229100291584840758583883325764954513720874234078968251067260766046010498246874970879219574209356728718939040820426798512297349355513641286332890239187930750517159713843901287045110387912614920992939937226501478805103114918454999236765622119350745604905959332256903515902724109365238288184869154271772928671291143208304688604476658757100425882293182817867681720313674911203404962684316025476001267273730232985392032957434619940100956334423212103969276181323144341330995405305361281092208330093996528499022857118761437301685885795367691739977788957643842955465587687424⟩, 4⟩]

private def suffix140 : List Row := entries140.map CEntry.row ++ suffix144

private theorem score140 : batchScore 2484 suffix140 = 6675050431 :=
  cJoin 2484 entries140 suffix144 4 956791892 5718258539
    (by decide +kernel) (by decide +kernel) rfl score144

private def entries136 : List CEntry := [
  ⟨⟨540, 170, 78069142718969416952645619813621865855757495756691885894383144921484794509199381861852592072578574247735942642326584662386008327196929445200275976605766173989906969759033714935668148803548555254079548355065756090950024994575775975053229849581780811613536932757552101018486550493744892662871803149095110031768384139884346340772445426547368937289515271782176010533964350194912103471457497720643733213615607369563885389421861624893886420351252609912170279629689531526709945823628529687265728460478124323963371414738080139742378008313679630027921290253276191617055326208931338643636530556822269072313458796574852476848084139155104647819132897154012215249986113500098036601948016883128832642177953668580250190765932214619963300224748884196652445330757485992827629716480995249035204129601972659512137711820116528404647607852026480783053606757300811358089031921473094949306177137252015156306546479587404174700316644916691659150777705864854578127100159691741700956914579032762941500007644783785202252586613504648059528420252234074174611957350249498377529966986080808744717719162294171846465374368066568275760502252410333420507995294873990547744847405761897043813278401555217768616861804195366684344496060636327756802119926090928939081479165822950538451856537096853231266799365917515380009172427561943786901606843243228293557118584109463943018479299673873891486120987878493745153019944532112614208219061539100149043812008688636813744537600⟩, 2⟩,
  ⟨⟨539, 170, 156138284565448180465207127832229699283404997003413487794268995157940496495972321377363578545037436657959216716819258100293116567333545503396817762968771750011232478415551858541502254771555279781994003679997218859002930770267626335701816406352651069962814189173234868176729577296626031779533006863775072777311435254967007172091431568343087496263490460607154292962359689590104829325135573772218485209854033683732122791175618297906229019313603847248198532548929488450053330577826662854366446349509505515126425893129729242490829959043326211965565592044867557091589540212778675572686203356823282015416886284676207016284283791629761892354197103255985506255588483548611887925807651752594918974056234621927137049539496304912790645737572390750684270870075871514849577063709642775653998258128403120809840423739790102462147328966587173479526309209308402806149367633679218009077581876510243868278572926624015738664598292013049573158943343379076858208140806220684247956714444100149829725728202001120404987222009238733745949044380166234544567414219524406053994803832444087669184363756312091928081008187087543471002250413297474390963507489212701313084499515091095507257824083817059126630543713530385189438942913415941442118048144366681815657928095970520352998899358242065988760507753582124855056522805055594607451088168812814044123672633742324376471025561052843838492420875471587066183239681879144118837170445035671922463526626161852319767986176⟩, 3⟩,
  ⟨⟨539, 169, 872490653440084099686773999969800888018098704000187223677138398648921769397941797478458849646075505944421974010435477772752408643442280628276530549648501230826272993592720770887943873708132489785157129352432154468591397767392879601407740520892605819620130656131016678308817153104752827857145033571309537204293680111182132912635986273909834453787997953813204336703021864034791661908167413052207206834706009538576422780070858415682221669758789398866827535008693130872117715661298886169871858546631820073676463712901284693221133804217456352006493940142202009779998849956641575919052207766414856105682520368016390943062827832216323257428410456455048861237670781021372501008543359693981889189891968395869428692328021022834009150210804817755639027824132092354067712151382964979410507601791627502209535139353366862237828077861324622734654836025337966853579085585725290697054599190497001357753077416310072009472172455846878920366970927989382371380364987240167345876372819865838565316571182846924045260862993757055932468916357785567531003523417705731879998155660024789762637992652170575969506559433233766638171302460317845782678513118630291430760387034109057390280086951274532485361832314550606804510592138607265801999542282618611436258647675558092187637871245020546994121539026643802309674812036801203915158125568791409316348118900004867439437114770711378066124330596625605946213582670312386780266393482613028435630465081241763840⟩, 3⟩,
  ⟨⟨538, 170, 78069142718969416952645611741461824169458393470275644203810338898727546030348598780605655132874446445131848175265011230209267495989199506685398696988162268134707611566653348007472323788948749664550077538904838271191568676183751761586971175946923313506110660462791239335260195030416366839011764100555682789652753627049225070489581947940390728727193978370799016417584633984796555305568630672242866461675343821785854527090110649905332698319062809051928714435252648418233461024410465762396147259522966087757458289984494896926987725236153776159063314125072581195903530595563821878576899447434257687610462236158436868270598980156445115814102319666438915184387493445535521139772689474005318345165164857761966104418562971757425420255046412830589995346103146428947375971189176820246895772898546228438394699687084306031548821963108644500420908325446180900674850252274249610454766185969979710315167999400315487092996485927865671059796303503624560411879341936177921365351521085363595909558582933556663017408076599113319147189422597075139718663631621992630743575417608613370274082501001758015808579144716427374846903108922703736682193061109988181690107095619480354900305085493065175510282493480637722850274119271390037007925194944909054906062387368448556524909055491563079906878779369974766606683461466855332774278865420621294656902250207428805916709681113571280277698100749640587555949366120306539044222072667809470126329507573415444320616448⟩, 3⟩]

private def suffix136 : List Row := entries136.map CEntry.row ++ suffix140

private theorem score136 : batchScore 2480 suffix136 = 7631825269 :=
  cJoin 2480 entries136 suffix140 4 956774838 6675050431
    (by decide +kernel) (by decide +kernel) rfl score140

private def entries132 : List CEntry := [
  ⟨⟨542, 170, 234207426411926943977768635850837487604343317873161386093726758358394814050994983342526199043582888028077806536264317102331845059210912156517069145088629404894292408627052895564167684534981683185787919973466615786181817417083578422656888405088111012575016729370115373219383892945681919996903217992800112764518564940276277357813771558272365673018928679363676365436159561223576053662515093810210823446543087627517043856258383982333566245489049560987962127675209196449010318720481885234338353241085749804707158890480574453290967026232400620207939211220107874602703799744040991716853245608004365796142221431176929053169272695187744633304040826686713819557650570624180477493222906943691064086256503499964034236375784268602476543133342396816766274112805603577199886514930132233283664799301176526967184011107123785836805959143820758897890453979925929124754195282059738050421814550257173050511102339320479013458272396106590299981708380256234598490884369124248305298363142124646408662187891689069144126974632282744725907252857475552169814469009569492859237558500077009351822077717061670952004638847106109786888400628057895153438319110942773684441765247678773858826713071861036466948716104450565357955449311387073042601210880804521308761311731500972436676087480417409659037547149144130898571880246312167248245988348338487743632740993165855765715023429383549916792233794009978534739931769637058207202923262819075904913864904484489612761235456⟩, 1⟩,
  ⟨⟨542, 170, 78069142718969418036072600661142220093079888978699446937342339107850498410785556130403310640639793309492873248326625489358947303002726629842230811125937630801996587989689001127075756699986770685194731216255593789146276289380674335766393633547553694619366289433371365575744569234944376826618516458861561583304886016675917678160578614607350815664594531578408152991796644168191860070024540076203243154109647540960590491847669652473690706611809617217987991999373335944951442612909029326123371032391685936902390355195195688090807167388524497872181758014965551520881159735923339889379222291004940607304307306111059890950909383180035302626918447117730939772525700496748949059220440817305299028622239722328984504856001634841050906633483797289373784745650399687406670359302410961972362319892806692369666244762130710479658068069827647576167091372734316092825792655896506893428106733800172582187273118430162237363411632044563804080440251248201907435302348694797178406891017070038144974708463869487561897834170035549950936171616152225779122802491106953585792242467060032609715503194615621484334489465306467412072597948372644179626849663097940574112203426566642827700765445568920173720008398028558137320381918595226083817503735920956285190711254717494514280451457160422248876404982648293219293430413150491350066667219085144078371299912235368517703847709992222397610024088186061484138360605517880070828869915567489554921034830478045937041145856⟩, 1⟩,
  ⟨⟨541, 170, 156138284856278396111714520591206868126965905887428074675077844546786751820972430950288411085438025422036824849373080798332541832435870689911486827213242685065568793310076025818528263317912223040778929291545803584251677661038751649585046848974493467605451995281803138758875280785630833089887718504234253063111126992843189971571972912007272656808814830197043442403207826243917505174860875379533023702762059034933314692886366741427256600849202627155557855858237923616353948636977657376680948010458185249895040256873229057501225126066891088867880908485698873861221810260485935490039463293119795021213333237747593128309931184858087472090216706712330342017694547361017843650856671948021372870372962092566165994609658664332281336934194584609923635520361895490828366277911741019340875991246607867128568392030532203253328276922870651139509234174934077112347129607587585587293341126320476181840828110221811088188065757984660451574542663888430681509649641356908479303109838474778408760095034939168735259038299831086904602619151167036593247163169776884856996008905781634428695138995529418841899994406249714826733932666954393892454529865465204028996722499230990520787740670279506359937365106642912518658014036106874697514020329436597351814020469263129008396123888558699464005562426512894206293942763407868733401102859202052315581577065101679474446673469253516542819394914150563775229952773153901785086127150070950241901185787461103441193992192⟩, 2⟩,
  ⟨⟨540, 170, 234207426411926943977768635850837487604343261861299281473146642816433099076663351867589751481979717048621623249911396234506657218133198705228178107182616915084134499166128944135584902494643958919215501775616993216324432106332617445241982498850698832564375534804010175354708591051391948571684924984040742364301813111384445146598652076942280059712984137024535555995700673177707871880012713358525879390880037487086858978545201087091566720763763760045912562519470036339513249338965588208138584841665627764825239977401022380736946314738590724447124809901911115325418586503940137360824376756259746738303557956076424967548383583677219422230997962139066529807594005956320264736503515716666819794108123658953316646768274528840042870909920490333617454067326494016049951847361810942078045546848122066762765290385023498422286199089010843549090840300689559548046812927053789399376214575174671941198643298313675432678156087378526576154756222497411776832735735147632392568290159741521972561203635367756448196443223313817503827516414707761854034877390505416052298113753833763816521907934314635782428873479104521363489650871425909514655756182422337332521372581623753640552347225873569018599038065757900308119097475892705079935351733737581771820753845545025939581732648146887806864642886011948327245285009100375711496202444488539257523655568913583422053157559423898532449013220090450475191074119633174117414713184431819365169955333364500418199027712⟩, 2⟩]

private def suffix132 : List Row := entries132.map CEntry.row ++ suffix136

private theorem score132 : batchScore 2476 suffix132 = 8589383154 :=
  cJoin 2476 entries132 suffix136 4 957557885 7631825269
    (by decide +kernel) (by decide +kernel) rfl score136

private def entries128 : List CEntry := [
  ⟨⟨544, 171, 62869577307472053045358777627117508966966231078265281374716470819298343244137305817064906559991901128697719608550167607806477457645630518820740797438480585388493041084168983883523602610556483860742131405175132451265812891242151101481340819289726200133246025446222270450180561228487523958741313378982606656205368621491506617934150190168918922371997989562568773893543818089136883714076272659932859233498950344256359319253213301260182355552537624263474418343376703365819396786686621556348783246700810737507733396897889534911785312046247754299401240303922868432812455176649766742324345318432921853654977757400791552757320487065210519455853331399648866467384298730396223172086838794636879214296549040883704993956281809486018633098878025643689619913833554399635816705064389755146656123333137817201715119239901439247332926811808878083344265070754510531180171981220089809001082361420644008372135933851494353745681245062163121052464141827720326913653436002033343791018990295311474710280779901175352261675188496107734577774109775582123177435778785286117959742718593306069420769251824049540342233349837933000073877964020690511825398686528059493161205212705592452061216073892912590099931097359111428265786681086434728289793172335931641821079360308544635398344150865407478708552544612837316854008197186027391552609409977152261241207442972929911499026917594574661270473542631547999078021822016865362793463901442366490966136598959969734428500212845641728⟩, 0⟩,
  ⟨⟨544, 171, 20956525925295635289737555194218258877520385124220864997543585259794466638417615952632922991771892622246546645050031210426345695711838940652070047767823165048734507137565465866312524643666105376833347098991278001933560163480163184958088303838471255893629126229775339174064979170841361266418666509815463558306781132449861151039686648484333279469037032899323262606193105627066106986265182226306898956841780058916202100377261382593594891189105525919094832864893210737560095819599464900581181589757520007318609985945307623332970628942389803215314621554457523250524109821052252211535169824158237346576741794500618019886905141412160871131010157142330059582428368875116290227294225609650267066921132113144558694732548876133384307843897004028313166736727174679016725944045812290709926871949690750047679102972679984749577861804323631692773034248464573406446479323981684851598467607571365591338211136582774724996997291210021752805561293935100949858637128149436832595186422755869659439668752810154264537553415220015829976086661468919454723321177794564281635716338838456389574373562569921318279598444230587856057282484271191828574135547757710612878584912288847016751420817482943454479738495119456425026931080727989281767808700137979860659035633252190635101102833327361235983921033542840018033563607176998664202093690606249906577567665091375825717920910093436581068179683491228022264629832952814807426007778802454821575222268559269696896667224719228928⟩, 0⟩,
  ⟨⟨543, 171, 41913051616383844167548167494094862751723651916990606818740371728993390290118240810030391345955781327209160004601095288842008161801314862191367732239398011820098592085085261733854800425377541219214231590467985060990162355658407680347563718790916966056233940076034572711844765164329929983568306260429150692946839983658111199599200698847668814185748069986269685520119052234364682970378881328317116746257394133198431628397202273537462026765678099160655041097603343706831833271581790930124733022482014790126250024748582656121362127890036832293413077792956035258536522704483326605504532124215179350295968078148353681047008209377696873022571278882275913559743506521113183856696837131862361238183307139713789177458699592199049399373226894432516267408255562262694934249622727302491581602241716880148682089869981733147479724807714967145078934484967350137537331645449735569569358015068632907192042781829220661291765925081338404398314914461183470422435232565771181274515381848982883858178205702746131008515553816452242050213445101685759918566235578540085942299874452490272951913371064802842118957085163372803133504669762893202074487908004725714531037125848111890852222468177485105083310567353937771862792663786193558901297793165219124081113260722991353573087185698279770447909795864746881835123648772460889078964386199249188572856002232091658600986514256156616794402650790985340223594350197724572604469079885354088130741675347564775696200736592363520⟩, 1⟩,
  ⟨⟨543, 170, 156138284856278397195141501438727222364288355121297740338616376954374266463416096683170685298208815595808227858617472387719729261911746921732557355776925521758280489062433027412861009665669745285551063911774748979893043748025551972694038132568189185299747613945371180154865663510808048618029784440725113860611014595370038712568471785686424118345457313222845506956159321921730532490736975383967246868697216397975444158368068546522427945167027212534947738132136747728114476117346051363480558955256958690711359809916620021440850774352738060492947601441604318664164721619506693146758372850097135014017572179043697975970013327666114225353366778042105767929450303909726812088262606917398952576107798444160190992303477513130994306144691921968308086074814736747310932782676496033249736369084014843234595460062593588992200750428919183115489297263284588195681368439100084384669690992872057551020744935917832713117233746292851866671986674670030040882413619918882973417428134550718666613390416941576619998897543657850202346278017442169197223107472051723884396482686407180496359326609650925069465762295014741760775243848792070349503732425002776251783066147441368456201583049478666480402040197080516820947601623711794349105318018263337918866849964211619360428662442823116806924946326744513019892283026000599093393372373739741951483274295965304859360694120075638753941321900067632958321496105554421486604543854452880037855256397500624482865250304⟩, 0⟩]

private def suffix128 : List Row := entries128.map CEntry.row ++ suffix132

private theorem score128 : batchScore 2472 suffix128 = 9547294464 :=
  cJoin 2472 entries128 suffix132 4 957911310 8589383154
    (by decide +kernel) (by decide +kernel) rfl score132

private def entries124 : List CEntry := [
  ⟨⟨547, 171, 41913051694452985723196714276722005235993958843344839892606573036413815059821564865569182961235011313904047527233594258225239906428998539403424566100980009404240348931560007385264407612631840559925198479567854730025033511705950732727114261685831286345690734439580674054969960044818850928143898705483759651815632152997770436513549585454320110946805713763505926313314828700554762727996138819064120284709741776541244259176451812418259716477965694456900155971688368382449141259767675919721114045699635726488049083492122376242791587274423395942586135423052846683623557354419020874855326787083873839145930780954731574300342886936001005858424594805142656182155795889568421484554415525009525524204594969388712978934737265564386876200220165312495433226086142701104856319546260928280672866149735191265844666941902677902991859533485060067651080891959212759592064966503874597064115831007390626009581613185010120603619645502597969323578277972345623115433569877878186391996851709063486654470505307231691710203224136622536212632570637856400076988766185463504847218440803554074292079121248321508240416904839091449384284206127198855724646683701770695656772426586530589779334646036224937184686733840178851114072505836749374162038113525583233222589011859982019355641344657747673387288736497455246146272595733291357438667476912806709468996544669711016088933140402169692775267799424087439660933877520032183858808540803275960538044972592981890266931331799711744⟩, 0⟩,
  ⟨⟨546, 171, 62869577307472053045358777627117508966966231078265281374716470819298343244137305817064906559991901128697719608550167607806477465385276663176535574250782646873922922648991442873834259127865288670124880381406557255372955576404436651587086602423006817038085796040358342049981162385997917149568791526416769399139875324181262324234196019259348033508762125942947685161919444243964981622900789996193185922091885104143255101513475270425120426442645593204199119656042448083133809904346926238959903933167200588577124053643073137639327800044373121914334296234932825513847326659060616569155528110482385970141028246361803107013635549347308552418634475301871059343239089251751546346584041087006624571501240287695522036787632699482362059112253641746448193412121842122079640142924610117222509743956945009735125344545476198369701676414965410377044858101538779031719100137420378693949520275040859342186063000364175495806958130554630626078220713154930189133865652791849928619439980170528292838486185768801429868552614228354432740721114129563160027257752224411428468364013450238138284358690337767303730211439929728663870086182952011390781356593853359306441198278694069528933329419445490669989984819057643350643255947980918867790979984521490953142278594336443325318457866481358759322734958990155572324678954321925291534847913369956199345944728274354946729859256456521783549554246021256250711512300161837986534569667315324066112841174720514451190384219627978752⟩, 0⟩,
  ⟨⟨546, 171, 20956525925295635289737557361072220572561093598865651441558707345712855011143232265004529557784614674020854730782781654770194193330904957422163093106014175144356016824844425388130090188756410847770039422966126146258947432630345950417258378945296741457529882317614835680655501611655435409629046747869581848747920682973022297247182780310357486281546435999812350059945523832314919371057229774925151348788915770286049502653734334357584588097304462386202153653818417014920216426860597600244405408412151128170627355198113730197030732645025993963207923760380817018427248788128908628729351810213540783163650391235727972314638598056816480621635134883139742060769944103133695352849793978653133051353019554306512549503034688559828230133344573745339807568302968789844188264429392809793687325744656375535634055455842296570625716437473103381100524656525041394045016728438983311418702297550896960986852092208737411136172199158888280543438448682214644977942758149954791141781565144770515689207831143586887029213337164170620048714301393417700682335732927143153656135784153974627540078582856616586254633177960453562705723357313094452504275623307008346952115246695870761494944555753053398021431080347025141937978818415478322766452689383779344031717718065386926646786444735826519309682582365515842537249031471642528841412874242796100884657680241998595427546175656713884303545162308478094742620410935392206067515284813925930350948425434523133460996308154187776⟩, 0⟩,
  ⟨⟨545, 171, 41913051616383844167548167494094870823883693603289933152605031901883549197762732252311140284528940846350398368782200417733876479413334991301074325151422158474183195465488820639235652684630617357487140967105731523148251426653221517461726167067555186774355929913987564834120292670307056102209434164528591542410781576681544835195633906740971856507388357944731499493708614111138242947694940007367109208936423225331992163297219873880402432039880055739424518263302729543936799017977643732270118616930119489287477032272486136364560515874256595465729255998473995147486871991847580804430082142997588419225030899927203442766671145239544116745521812926399554101109747129720130302385071166497016258083837510379998632667629280619579997221099701044170114547708881570631878451524711937666817927654499137117461842587453196042989702643769718920109203687064457664931745437466251866899364909905228075956687459486406598387971134517145723409184679093873513483471251242978906674785043238413270699981877159694203253715010962509356726053287645640445642482111901279190093610448277524192707639537370931990492577775885766773396866578850524119510302994964898874591211654440789450932424205401781178120560576364118753270760643735850099297990409456613282082881447153446989950859454472694581701292208555391235086487493590154195491854905646317429868034156267811009065397812997553251894011151168495131330961231879027354777850653492056802584374675069408786366882014875877376⟩, 0⟩]

private def suffix124 : List Row := entries124.map CEntry.row ++ suffix128

private theorem score124 : batchScore 2468 suffix124 = 10504730364 :=
  cJoin 2468 entries124 suffix128 4 957435900 9547294464
    (by decide +kernel) (by decide +kernel) rfl score128

private def entries120 : List CEntry := [
  ⟨⟨549, 172, 11250949122995534280148732743241731790016353288322647689105281030681849143513862265758317474810093916405676073212057111959756172868857736431916956467368706468421555531317853032412216913733857668872986369778719284551717922023654078721568996676369999589777586888504184931536106932898778967709016691205795326931688494484645637216287814577088187338992541749311056000430247262288957781788778747818642733779184232696218578316770163871584129270289050893373133325949132672529358318498242838245689597171566748723997433769828128472008522059376106595793690516674862057006226391303140988404523920272310100880172901557623161309690150938114938351574200811595448524017794924765286211154421263430609573513139113271407638579962032296224507851900358675102414180244330717991365726630601232423597784047084138959139347827471884240928703100548441147307176237957881797843278021484560974208520824475697870954918916170925810304368543760922788288404325264350950071153012230405922239118895449963730394868371712201053407819189304822291288931897467294496015760647631839276204675810611449836322976297071614147343321280243921917175976099786739849418749522465410248437729766293081883612849075175447737322421876237868863728478507304280371337306007970702337378518110067069726924218754306511587934601839358805344474045906289965171808517194173466530055151205828917047749374188174601979263189839796893860641056486993035914180950213719053283353358739467093164226362318058083579874770944⟩, 0⟩,
  ⟨⟨549, 171, 41913051694452986014026929923229397994971142722475494239566081556815347412772607230887010433857179397980106390539445254391400242506965943886491336545241213456212045911574189607006316632857406392123696717411227695577845724477328648637770835801883177170736702153782471527945416551222091410964118241152952672658122664740054604240166581434014664827280805877435288804377775257678249016428535614897619814298937249904901818241507690402243326199002080853701058886659679403975867276702532632396450993213253203994151841515496844181831277674484189408337556117084098067730375900760465279307902839910804679995351975677496098899868411454209327759761368043049435001745828353543605728720259633578469120083671705525718441226549779418678978576514256533767967868621713939834747280803671427464046013764601024684991260186580812836624453283134856270898506077531216973282136915534269343297697964480244854071370466291285662503562417086903966742133112205361245360296690959323213696614680262554124489025702454066871877431700925278967018782281009297287765931592203463791523290392285969275585829493977841130302121065070070460300102404804464116737629312099621515956749588844903548234009331779666380175893935254439124333201698674720605573047652855592357312645800508245178736172481663277406077629300945243279695714063923483787470295563430793569008225889479092455994059945430001329093014071779410154805400438374040907103190083181568997332523327565475542301340291955687424⟩, 0⟩,
  ⟨⟨548, 171, 62869577307472053045358778710544489814486600351157420059669162162296717524176853763449227715217297447501160843908267720064971740600161198879435056570674581675069238322489883377708014006169502728497252253757440053318924369301117223741201510783556193089898742344224084032256568769647404556108497253480259404899091820665710293934057405597635245967774118281959723666981314339462247302715249505304552792198717969006596412216562241469766981787696313759814453126060853368924211198210621528892394453296695280370274762568180747239444953833563380200639305774564480077415168111361840161159922084002785417030398956705388102991630711727118400826989111048281418361767631157598819999420821554883919183035068841936553074307756821004667932544195256073481753414048294015473510404071889934588181279128136733823060846076404626267257498833793744560897277072902658383092918964013159266777633111621543708644898179509080771907897129316563373306071414233337782176365828272074708498363966310554547188069105381145865799000721747945227494831326087422495382652956542345702038168826173709156191135070770317325479013610231733878131334782152103646217940555349128384158733007562757172502113158293200609299587897016192163066186264732478488100376923763097268001178914249117936367717965678539514922166926154778424143949698920613433280388482245477275131363641054411026987783583809790320066090250964255508352307950060868147956459770031895096543741720963858454453555446953279488⟩, 0⟩,
  ⟨⟨547, 172, 5625474592932555871879534886194124960955152660180447467506775697118729674954881626001189097037446546705658886117055047920922703683540290721819775284555316971264814927796041490971660378182083694673533192314813690594568304348756604474822167134144692504081350107363232898068963835425955692246024739714834295442428595397556890958096779055001977908524459797171652714228611324585108412056593983304628631121784143331145448577930344361077236946771275806956680230394438705267661327341915832645977901866771298837627852991105101281858667565356434959780781302976879533836837610788994530942770248111606085058255973352623372562337590700130482969409478369294320998867792829872543418031850828899786500663598803300701176248356289511882819985674231230192745616073812154523681403360827451679672770879120179996962207269142630983373175138507004786654598894596812585775726565699238922746956519290338965857924140821108182704403959645080853623365672074780402977164319969780196615935270625877022669507997038030667959584240704205716871000030494931184530802763654493261085206680797868885004775209682518022349028838346394033386175877880244077341623557118207842029104316783678871203274038869928007866875322759693603104318007419642508389968599109036401465791415207174848670652803254754148196390183207608117680764551308645560534041173699828513449542633483337464397154344600335707583021257671050961458258724400466318075481354036849287057708416264681529190109166862674162642583552⟩, 0⟩]

private def suffix120 : List Row := entries120.map CEntry.row ++ suffix124

private theorem score120 : batchScore 2464 suffix120 = 11461981380 :=
  cJoin 2464 entries120 suffix124 4 957251016 10504730364
    (by decide +kernel) (by decide +kernel) rfl score124

private def entries116 : List CEntry := [
  ⟨⟨552, 172, 5625474592932555871879534886194124960955152660180447467506775697118521014508384496429236347156646574224145676938334682144666489210040236122224181706728302322079632412750670378691659147580565194253484185908979394194863997980131958061141236710006911602505992218466150900916333656701460611709852762032254675723059968489059063099332136799345685653136791305116847085014572473839113596174256648001460595383652133941799892058958069125489426499639844130477260602357524388210204786426242808456426656960446249922913268099485488316958453148142699698468682162795034543700951149134688875025959540030883219933659328244459919750017124496393739989067433558646696254113974584918401815248397735483921183582346272228910075440107969932901981285227027298470201538488859755664338910425823287500836538497158487124231714041225467169218657000904173012491129837842698757012168847891906128564293907107183160783085742216478468457357870562889964896671671651084651506135377868670268833825045572196097930091837283773438976697246217002331268074539014169004916410629682670276243148122894209761455458767430989973234141203118974200286408979696184025315553437278636106817001840621441374734431148458472828134755808712485475819386640768088549312953850070013170842471942825390079336660392109195538826719493893833621174963179605417890182410731353353964237150217034828345968589452733717897515112916764821535655787485884868497275381320078917713132447551503961980664165024073987434004611072⟩, 0⟩,
  ⟨⟨551, 172, 11250949122995534280148732743241733956870314983363416306029049326476657787799873211955047996157495981287095121905706133817783619398993190870659919761914276158521630302315623831195433919856443961918575699641308045907692285584580739318269529299204830414472967250849257198396992652882539316313515320251833181474780456138786556963405421362175056993737976584200238703349619426691204847739428571891306510338358259398358836305071423614750282481165619221600704813016781538096540738543152869056934845635548878102208013865118343658401033626104079103376026465799914887434866997990163900931384550942781319637940194393476081741791723764573182170203881334543381567005495408188676340474467831709554766499332273824211523270565235934148872935417280182533111155898266008784988536731248307734624574987915901111358102897117559663514534482761570755223226920146868444064657147199827025404233128605504838713947673263913036169095433714319933117409761823732934032046738122411955042545701441841009412605959812891588332688866231745018249719707210336256603493788796320583450383875920496742976920610577868283090358232622067904811628749390057868297810408156452536559618363995854011115371526457272135719411817232565916936660950011433094893496200329247952857729522644139410142308200755400765566425902979811163401377066524404374585917500384898949720925333381562246172756986213033050980933662545568753711995090360406039657962597567731373181508403175632473502606754741906060736462848⟩, 0⟩,
  ⟨⟨551, 171, 62869577307472053045358777627117508966966231078265281374716470819298343244137305817064906559991901128697719608550167607806477457645630547653169385126115221569592103140750732563700599460531696029933345252095321449366107831441286885403825955468087999533243384605969079136993017601568674551713810267973982141427362759674625633727044145679594358554890591327782437081037381088810306718057814147667534076622698667090383290560758497349020832523700457234932316845677393518930372425476444756419944794525398926937529368558185725758077285790768724933043604527562132045480274543876174103296967600709077317161663897175726310951397487318999877402326225860760029968494336052532808583586047613750526679913378330334432238277873210995063282131004306984293652348932370344387436169566888163396131013216457592740187268742156744162490834294830949952026397825298158730323508327204100990505560632840919279980593878842050947617568760982961937516495374411633194745567563633615894781069662422193914090528638906445152783814412838014592094994149718362501274769672389286956724868062021227093183438874270296879053109183552238236204874856141789825928790891034479330701979031878136030982485513410022365613671420876491704115066623156164855572162433413821515014119860222298162507610524222907798431975351231265792450974408701322849319542344300009545331432761861967096954466387196109413413976563315561702483140067500474082939236675796448096320531618337292458702550172549775360⟩, 0⟩,
  ⟨⟨550, 172, 5625474592932555793810392748885146885313232730115844540330051189087806118360419856677893083909172244035787493089275270785028061242044730632495360616497393437220309646407640559676037591233748508574311364524000850471804167931670714323120825739443866868917685322267363969727485524730991433101723073604177056902559023122191579934450554557542164120226751826846191651850697379864171627165999050766491008636082900535622353706810490834732525772109586540265365294790156681914081225392460192407863964648417798348645243090541886364049825784367082133695431762277805985567855422117857433780562115555402609914776275991572450733602903469562060069288753545920049653441324798446083653696514650814343141189952157814924200721809671874975264871298367247794026048989351298926376804321798175961437659922707242508802346922180761409795575218695751487085557651057646536330270200988152940274361626472358039693710034615468267769392284785645354449921270912394798453873294683462419856478897837260357246511229448848325611387492005907485311198933282916749710625707540351425957075305641100229286907223876556413881942980680799554184173760725303321352611843134958990701762815915528509242408480534111009156246224494956410391499751490249682962712183473299040221133970809065036776291036606905225501786928053212199082772802635805456635732132417698695698489194660855531548801941309430696195531472052847346851695244181251342959376606691488787243281784977197833516332244495471907343171584⟩, 0⟩]

private def suffix116 : List Row := entries116.map CEntry.row ++ suffix120

private theorem score116 : batchScore 2460 suffix116 = 12418900505 :=
  cJoin 2460 entries116 suffix120 4 956919125 11461981380
    (by decide +kernel) (by decide +kernel) rfl score120

private def entries112 : List CEntry := [
  ⟨⟨554, 172, 16876423674015038457575281033748496618154311355258055777345532629325995772918866458060340774007344690282890407846801384250486821656544146911599039652087585098651639930858901650134576728742982068095103892272209706212008579803201923952861069340886323818435669538883072422868739626958801770908698591565430777555892819143264168137647656801705994330297410511127591621310223394669525792503260367466087011583069022513444379365167566802445460380734685662384555272373944536598886462037006537997343213827388334754952327580605388560574873559320801010382561006415397590366308467712211330799957855594623184341761751338314551484014159827427544136128082607008174552597666049092821007641764449121696071252582094678749663751718319534199886567636681303571497430322265844666004044415630356884974652561617179081347607790899536708283628197363257547368468265274995408486101300920030273057633317076583192843034336812036013062000183312694943623988062568873430170492001414927636720670164505054425194646073825401620184810877327303801468804127348462200182035759825720186321709499448710062101668483740230693627170251704839699251856650976364850698205746790297879016233555144479012936614291112720981347517562186376640008462440775359825207084080166478394896602711821308784613862025807669937699838113435923659679252217615206954885451137563357589555235154901565658124638846708544832972554808805978840862535914235950001131200666481192339637502028940594205645576338545844967816822784⟩, 0⟩,
  ⟨⟨554, 172, 5625474592932555871879534886194124960955156696260483346226072303271772159833190280747591888706786962046301605198954183254289187760898744080197963511656138628108546582486351739625709463110915905554620042876643333746543189421203189294508581241819248016091690475694519075928811137694377006497798359203170928702200583746047358520566759439198207011609964024265957032356894241510083562288680199007406917337307990621801347086360904785226307802003641349343969051482479380300114608486846231479116230031387700050743966043766976734992829919479555640856219052648059646155300851091315491939755896387522731049793835127940023709470141061848625941582401681950601796735040008632047581255900145883262333442102482772654986021156201250865742971237480111860946523510338131805070564937673775451722735117632387944208525206950863360067430145531116395810881746208535056124168319431617206801027350066546910223201561251032952581517025293286106396131647831368716222123270302863361604429739208521168663448294450501905891442372700455336382890414674347397451830916977729070360821960785583032331364190840211057272651635045754937621134544334856198217236344577498499897312318502844807164450360307170056209926318350999472625152028508821959012793497962888464794423486857655578898833906272423625275741307426156203478607454233967638348795598188086849812105364466346746295150366908505375332491041630742163995098730188745475654037779232690125887417248142341827959434808915437994336321536⟩, 0⟩,
  ⟨⟨553, 172, 11250949143952059893167799774573581660758425955358504661818836461627255710729366172894595077616563065447687603826398208115537308902464079827754706513646851893736853470510964459615259719491783191828256985755150297573154184716695680880798804242851730920795657134223243761310340001684962911933337273303012339807009985775456208935141697906801062868192578578424066471048075875057172939590382131784729964058925105817041035181274417275449293755232363975011618873751496027162600532415020598137488017851533364360056344966316828555461597332684200279650254191188353009154095558609215787582079730658208833821669114907603160971674737276766289621643749019415980336228058708966817084518800266777356705091644274154171224378145622830452021219307829526849066604846968621439227538396576952197125419828192575058269650556518588588108723689643229589669596858620158899106272014080743861513374353192533658165861621085476936866408006247729112740198829185053039621072071364294713390200483699816831343921924566487388631961629692973209404526770395899834638054701068871107427439772180450115875136674656306369836855065787447206397138986901592811173750578675876529481704221063867976005645588291555739872144316088576359161715834982801156533498052600313807323441074489132367819789256101305123819928233676466962760933505343231007780681563022601339005591724378691853696583438079706751186890695455652722570277242828766471805348139949891510287655409292549388938560868216540236717490176⟩, 0⟩,
  ⟨⟨552, 172, 16876423653058512766487072155937886485131669176095512494790322715089044368784517013618166519429188321333244591305664231188736059789314575984786353613887657636611133440538003564607901473145480542584601128842991166167715215272627230404723985511961828330583304518263044116873665859930481473301325077132906583342798292701070298079761028876530058788733605548408177279096282440045272874443046964874705292339129784407097393671834588930229521467598147267444383860362494518001113498952412510653061754812482252104647891706313544204292427157639598406405773109672109569332350666737162890936899721683117865155150924881822672799382470180033179074559537081636176221435492527239545463243260389808584503622531024229663400221732273466257016444883715365401343703300523780634106828728064010460678971243392544341237590491684048114214647713904146855191526609219722276589168935640383894470214723508903943806533575743049456504335078216653730848145887646911684169570380390160979033347167889067157993893828742448870736801287511122547336487428274119320624088431670966499566354230553762351365078899017520281932579166561737666849390824216124307908945246758630111319658616757936460148612863146486332673723259313127298349328968616129582665761606252372656684065777546924161689642467646106595343731041014685452062564346552223927841296170743873342712306983852245517581541309685278054108490154018532648670287677562057440722267186813447597037529898337561636088033577683357961760538624⟩, 0⟩]

private def suffix112 : List Row := entries112.map CEntry.row ++ suffix116

private theorem score112 : batchScore 2456 suffix112 = 13375066241 :=
  cJoin 2456 entries112 suffix116 4 956165736 12418900505
    (by decide +kernel) (by decide +kernel) rfl score116

private def entries108 : List CEntry := [
  ⟨⟨557, 172, 16876423653058512766487072155937886485131669176095512494790322715089044368784517013615270774028817335788887049281305740677960938174420956765951735374230698170488474250134745907935649817410681070736605842128323118236147780219867792991892715832910539822727130027216585951590668116495398905094718756762621539704958440429744978661426259223267871637627841273024591850584279850895315089974993605388356127089515651830302172499096024361290515527046027658159691799668317706552350170690683527153566778015931014238168686508246798943563721538388119215217919746263276146178041446105893140382419723258157657862809301621010958013422056906855273641196048274978495468005445440318625142250421111513358941871740041193118647103136958846058823294896761509868457178959122617600455870081872890438837856583525778055172811080222016046517326092415685158789168416941856451062755109298095492035622073493921561550934459889311407831594583141305112668458630605128978668709287749830563588617844831844580733224776072885138822553395938265876220408642185952305633281149205429070255761919220371385650940896048568016696991551726897086904456602381264421109401534325964212354701969485913578962681935403774520807808157668890883522422953947490991594355709841293909179282153516073227885914229449331270654144138311494224997885254194398356010250689249687712910530481244610302591665167885428317798970222661638053523120554029618856647366622377083344180116526272366661104407361990656541118693376⟩, 0⟩,
  ⟨⟨557, 172, 5625474592932555793810392748885146885313232730115844540330051189087806118360419856677893083909172244035787493089275270785028061242044730632495360616497393437220309646407640559676037591233748508574311364524000850471804167931670714323120825739443866868917685322267363969727485524730991433101723073604177056902559023122191579934450554557542164120226751826846191651850697379864171627165999050766491008636082900535622353706810490834738584972927374995716126023419147584808347524749053374049976629557270803933157748238272261123038092591023710039579089017838224474430099925774748648617398038288106495465935407748634368151908382848734887439654484765092331453917265664398936745470848441921894404074610690118729784348599370324886601022802949731109548687979586193226937852253050023710762737694841510472550838406116322485773100263019715119012508991784345871354858324942881216465139661518709039793030482086586422629453460141333813541494083695656641396747734648749722169558288275433698084754316782889053595819375549200075834909074885549303731334634181333073121961027314390086384777457237538636792399797604547446935175713621584661744108915442577742754256960898778473826095429232644529292494784042344309476513892262157258196663338592759795618398143028704009388564939534596128730690409006881850759405298362702359050223766854682976497861972187023302439903051926214765831415712281758285152524795868965538234654912536299955584439152770522461853301984758134828634734592⟩, 0⟩,
  ⟨⟨556, 172, 11250949122995534280148732743241731790016353288322647689105281030681849143513862265758317474810093916405676073212057111959756172868857736431916956467368706468421555531317853032412216913733857668872986369778719284551717922023654078721568996676369999589777586888504184931536106932898778967709016691205795326931688494484645637216287814577088187338992541749316537309112633305107236399434050671308078924225453330381887232609370270916830292178718854300799511593711379589913249886234780228909225588621619525731575238747642810333013235548806505455623772252967690537386660426423437440913596901752350490664618316317485475419924371553018768250320505510370457764360678969020972197329451429632317046948990198723610049853008143034390934788261881149298291987352223429200874146978450756017709960157980471421657323061029805028238666133167340055752420953378868956385349181974272437062855359605485652029782880739423380868522074067831082735390645123174854969624636827496535229312800494062483905689692809933646045436466727365004509531091249887834996962679308383324316933484066931956396111675151532420807387833965440314287218160164278746930074644658355490467852621820586135591658247707649004302179190871685818502063744161819235080780338129427282636303124911339548324587925718203481971167945776749470635567501392352244581350913157958960091344848055956786499784986841378298475578253249687444432493414973889664462957456819484849520938302880798348249766379114559862861725696⟩, 0⟩,
  ⟨⟨555, 172, 16876423653058512766487072155937886485131669176095512494790322715089044368784517013615270774028817335788887049281305740677960936096825514727162138218202167885907066636255635569830309153527520158914954542160107439415936260671265237347045998317451248647915157600844278645649544235704968684175649642926096833827123355558163979112171384270480467953955881959305908042791944221920229408561765946759973807281832113496144140470985784943796262347469765718896041364576843030396573022342620595914379334423239848885006912944899280880668296523800999537292541262556514528098658728712237384831179920431997221617192537074245687982093681612789170904263418229007543492998970160497613318439033366083585978990442394045269795189353210677490532415186628324432535947088460280813985887901111811915903023002923261783852674294708771711670371076509024901527799924959255432582615332273991389947727619490735816395077671943124578648392831931488437203939625659430337238545312411432855718182172063899455650256106382079620579098095707605870132575260160275289672736550188711816817702114229533698665958678384697725313786739864043403828748752603324660742727391561624899805924214326559760346878105270207562977371274663278564959621341239481484925866124032791122706463011709596433228638400090875257625499986569953010654424408510578492381767673637844717767719639348428522350911354756413740204201906066871463497314638353913523099823373051204355445216865337635780510595445594733060436262912⟩, 0⟩]

private def suffix108 : List Row := entries108.map CEntry.row ++ suffix112

private theorem score108 : batchScore 2452 suffix108 = 14330625860 :=
  cJoin 2452 entries108 suffix112 4 955559619 13375066241
    (by decide +kernel) (by decide +kernel) rfl score112

private def entries104 : List CEntry := [
  ⟨⟨560, 172, 11250949143952059893167799774573581660758429991438525504968387604835376556015769184273219317041954606071156073678462109417584542433250795916125122117511767446592243874967024680144487480479532220109693650953158458137231220756305679264953064541255305981829845638056333719078036636098902065712879077639378139354232777818085697135576071438422069769913021473129430326525876860831081564772830584688400733756130051343435820341222207727171874284402412766778465700555745944919474172966635451655741373223225121327927767796407114548820162222017168009269099571676978701127993337651140820196082830671618638203837669191789205873875383880009848939265153719572894683884595906558274851215543723188453520967538179200165118402268099252164212870366710156744913742465111657805296025103215213398461149070938661500674417595105814077905827910312156304433199500980673166923395325668266607636172921055360482250167125332369506676706799231772389764660313496120283753325351349163965861410437436087773169023598917331263891392145153315303258725242712069297975725308872892495074221174115262045786478184956901861637966492011835178763421154679407822873065155264504518531477902933112004584535877321741186568640908402090916626525401162993444444664260456384045511337630236811429573903636105184541869976050822851054848834022917066576930563623593200752233504583857912020014454488560299338713099948385261816307441864125329819866304426906943582566960789192159123240363728523769067806392320⟩, 0⟩,
  ⟨⟨559, 172, 16876423653058512766487072155937886485131669176095512494790378726951357649810352364411930010156692265899495701772717786472852009157686822623268693696860017563975395290223023984250678290726475728467670883397380350637366675257620815021647474764254475897349210370166989049312197041686378941572466873081985099417644703611875955346945574968526287764988830012697459771986655509067949801629151450188851877687149824431437237893371479932733895705756847130450927506571662573921316797148958948822333393430379385718589210498595033988632138061963492555725845727897177267397377306198859811525174144803791957196405077498331272317382188347025469194308334184957804272178681012812184816233447726449573589773828486449428643913155710655901628177928533432376239327848028318633696305549680500576464975512909483813474497796575020051268689933393180001497923685951292156688765766428066476450311766696060502443187843613022599642195346787801081646056071655761161151578008038979926402712412194975904643098836910572351341956453439009888537711111611691568154789319674503556058992850732605306283633731877963082491606193365861353829804175045749819397258786463267668488928839768001293296104801507413828104067184530820477272192970285212707897788204566364590241410789263586466931968377318375799029963352424726251485590980216061531984748918662437240945769856657774861636148777662088704999341041292404783159366748298512081669977845676017298577428920003899414577939122338140811821056000⟩, 0⟩,
  ⟨⟨559, 172, 5625474592932555871879534886194124960955152660180447467506775697118521014508384496429236347167434066470963420509279133031059419772741765442157310133826316675507517386793217092055998233518049010604478712682653013206907056597423688154946122949890474819472712545665306332330200851961231897046624996049680154607209473828025359233197997717266936910132391584931463956578608442890986986791825994704081357593601853141440569512228750741891252669766126352271513015480487545875505929787776476089777955080879908761631995781089849843474429199609981058784104583152356938652317183939227203277967478779445944964560635002557945078206255656632556955498865225081616250666727249707503125119552657537050640406118334758294639721872106708903839788412453980521328972621990433301325992495543479410021938065021834839076209395976149540887966661274777085790159146204212687727331729278219603908901028031421165178016226092025490992842665953614666312989118336545787856985054988461956118599454361272705064620967943899002665120572787490850080782178723198766095423417791766235395604952820277321304368046180181424944972450617392397593395269431629033121072213129027080198132554457376044091049411810173453125966825902429143177026063854923263286689972669577010839421669961082104867301126323579686067287524680587225873123072959479622155621126485807624018353516310662923787526144653317886513180532209483299491394607445246127002886777903211679124997874190171114604110914921181574074466304⟩, 0⟩,
  ⟨⟨558, 172, 11250949143952059893167799774573581660758425955358504661818836461627047050282869043319746582346179599668634596194263802714898903376771935329257623123261751405188887208639165717154567282290527502962474697028196985902820872702370486913487966044628592657149529637898187321040436625391306274720265022018002828787448283485102777619815045689671024646720876435887675552129938404600428520093355954116492688155221901153062238781187256366861912581575550278651896739983079307854382525188308047752474341343685640846024637383796983433152164471996851142143323904340174336559503539043551268433335305380193087091056856813289816618009055532154475805996694875083302825944211516930001275889628584115246590489700526513954004863404987354311121954865510737704388485786277414585437141292298955644492993892622914493330267672009676416178112271135737958845293561732917966904045235669621606963342900379168109370515221994219525836877242667136671240402228336335964104518869472817582278519954573465856555146592527204756653196506535345514313125357094143313618448841993077768459006611436341406696942215521001791771159828456087946147137970041506685035494062967528344767093025660418914745373846468697774860578160792065051704786487208872069587612963589676072691996939404578961723716105381237056880682699622563355086485973163759469599595641176200240896012694729417987489943826731747545387707440197208287316095169496502137512208047274919451329940757710429114020098612341863984269361152⟩, 0⟩]

private def suffix104 : List Row := entries104.map CEntry.row ++ suffix108

private theorem score104 : batchScore 2448 suffix104 = 15285123178 :=
  cJoin 2448 entries104 suffix108 4 954497318 14330625860
    (by decide +kernel) (by decide +kernel) rfl score108

private def entries100 : List CEntry := [
  ⟨⟨563, 172, 11250949122995534280148732743241733956870314983363416306029049326476657787799873211955047996157495981287095121905706133817783619398993190870659919761914276158521630302315623831195433919856443961918575699641308041629875427316308071908850426203911359366939403152765292744576645121807332264814172067457211495724781491852909454620184836965074254184727361233985222864157440960051428924703275369770233319902647926298996776516182585078580424546280264600194455467272215156646807437404765866266121614310208344231178338722751318649780879975554291107909798591826114485961443620975634770522954440331325508739034229455831396468155269001315550801733858509426576482171649546354408215701020648537290848403953988430347125078945279351952481599538121901827535953468575020917306208791202229989545533012692747493122994772322354139447636983366579667468605552569707955279976354507822353691014371559165767653958212230119950079576751060389806030132440077441983988858773254291136787688417867960682655687682280703654838610006652770559076931826647872577904543912697535915934975768601008632085408483371603916566825125077735546909061666760307627375339279711946593225475219327595989259807935027171623339607833341219983289842474595445427338355145722857386332787531116432675075138121292141903659226978872040740563415620743833317401456337408835510316694344547244052707732278976556566369415590620076870963244529182934290901771029346133786249310374288886207328788376351994360571625472⟩, 0⟩,
  ⟨⟨562, 172, 16876423653058512766487072155937886485131669176095512494790322715089044368784517013615270774028817335788887049281305740677960936096825514727162138218202167885907066636255635569830309153527520158914954542160107439415936260671265237347045998317451248647915157600844278645649544235704968684175649642926096833827123355558163979112171384270480467953955881959311389351474330264738508026207037870249409997728101211181812794763585891989042425255899569126322419632339089947780464590079157986577915325873292625892584717922713962741673010013236809014335732467949113776590016767823540687769470135455006583198239220977738855225359382283491887526128860883383861710055413356934131227876897043436841026306615861015979993022126410756445319689461415100985552645337031592003245217931302799717878189363104331784027345941671211006157415980504120952107582105629517675262187487431399043409015600629019111349121730964676913007960545158532688596364805663234097121362089824668596268388929549268163099806401257116717193755976546318204018343486537020167625235250904703475207931235725594100943327182336930658875275145913699290772940925034018088218887596528638539859153719693440377964861887958469301048125822240453709732748261527058046802574404005561022919058032993702874970337957764522705980952592546906135088808094177442677890018375041093817221398313875972091978933391119540897920361850782140775081720652836442022857510201153079576768126353264379048408458178616826867183779840⟩, 0⟩,
  ⟨⟨561, 173, 1510076837570264991756934755086077895786037330742771662008607681446127459420834634792796356810593914430239975087734593591598826032851067996536959426324058327219077102693405469646568019922209757788130337000218367233400429141661481621572168452140683835738203569718725608957905666974733995366989419087259457881211298880073424064281013574586591029325127942106190875636074492847263489683856997827766240036282321628795185094028143074291451633210111079227126992799393001767784407782425156508388176718946937321477045924437205737312959279874290439416263158809068950385334693950648188032650224642043774162491731384754798410603218242957155144065857428462060277360677050826248588608844286494358769387600398208568407122332119733279401194652567323829335105024007154502570373904061030482724693678225817829353865298967989599640048944871957685514738456144870131487127675831637259886643231748381828072001825537841222805225513987193377559083989434778621109666074656140084903250319913318905840489470847280606557132630891300330408207343416639633645345605177881539312678170557488786152392545780240534396398880254675116911317683814314593223525556272839823949255535515178928617177983203686501959510919467054354630379573968329542705800700583488911198159880417325138978004104355786886607595664530050333274224058689036100698810564532656629555151053153807843455414604515624905250906412508415390626726745049298468989157984271512550530151852680655927729408694258177414271726497068744704⟩, 0⟩,
  ⟨⟨561, 172, 5625474613889081484898601917525973748270248515775925939338252660429722465275380298475098631070486371187384361803721444131386763347900208028395532414737828346626105472028570727569109160427799977805071164362597891118049861900110918833466791490898387264417925786246686155297607332310396271720218618583755689742740077897929247350234265737572502971794243136257193280373232515065821330047310177005981968273904005637482481799097223502102157376903793867282102684390657494640176848946143290055042099454222355374716872232244821248007755173138011944294080751883040775345002932938906072308984207112082576247083949752476263398084481512456774901581592020131142914601020403032554191037141092769838388427141966888950241106179231388650947904074352284569766958678023396110974623594775576393332790571084714695151122628665521880137321808694136804061750194983743616478267313623764231172117273186175077286083622476019186389583570885264017080721664844800639803971757766633058364639635774296006360914527163265884487832751654554660373250500852419644786710778995571023097593130154092428961933232162537185883786254007282501401557314357917818616679276461415761028721885026501509832443478288775627364925598443265006531960420297774159904364384568241112391164095222996603823424735000342132914013789838270994065705575459647359626040560635801876051545091921435166523597782989700070364334318380876266467733859724747371009669560576909869116259085826372952041064436965588400329457664⟩, 0⟩]

private def suffix100 : List Row := entries100.map CEntry.row ++ suffix104

private theorem score100 : batchScore 2444 suffix100 = 16238520547 :=
  cJoin 2444 entries100 suffix104 4 953397369 15285123178
    (by decide +kernel) (by decide +kernel) rfl score104

private def entries096 : List CEntry := [
  ⟨⟨566, 172, 5625474592932555871879534886194124960955156696260483346226072303271772159833190280747591888706786962046301605198954183254289187760898744080197963511656138628108546582486351739625709463110915905554620042876643333746543189421203189294508581241819248016091690475694519075928811137694377006497798359203170928702200583746047358520566759439198207011609964024265957032356894241510083562288680199007406917337307990621801347086360904785226307802003641349343969051482479380300114608486846231479116230031387700050743966043766976734992829919479555640856219052648059646155300851091315491939755896387522731049793835127940023709470141061848625941582401681950601796735040008632047581255900145883262333442102482772654986021156201250865742971237480111860946523510338131805070564937673775451722735117632387944208525206950863360067430145531116395810881746208535056124168319431617206801027350066546910223201561251032952581517025293286106396131647831368716222123270302863361604429739208521168663448294450501905891442372700455336382890414674347397451830916977729070360821960785583032331364190840211057272651635045754937621134544334856198217236344577498499897312318502844807164450360307170056209926318350999472625152028508821959012793497962888464794423486857655578898833906272423625275741307426156203478607454233967638348795598188086849812105364466346746295150366908505375332491041630742163995098730188745475654037779232690125887417248142341827959434808915437994336321536⟩, 0⟩,
  ⟨⟨565, 172, 11250949143952059893167799774573581660758425955358504661818836461627255710729366172894595077616563065447687603826398208115537308902464079827754706513646851893736853470510964459615259719491783191828256985755150297573154184716695680880798804242851730920795657134223243761310340001684962911933337273303012339807009985775456208935141697906801062868192578578424066471048075875057172939590382131784729964058925105817041035181274417275449293755232363975011618873751496027162600532415020598137488017851533364360056344966316828555461597332684200279650254191188353009154095558609215787582079730658208833821669114907603160971674737276766289621643749019415980336228058708966817084518800266777356705091644274154171224378145622830452021219307829526849066604846968621439227538396576952197125419828192575058269650556518588588108723689643229589669596858620158899106272014080743861513374353192533658165861621085476936866408006247729112740198829185053039621072071364294713390200483699816831343921924566487388631961629692973209404526770395899834638054701068871107427439772180450115875136674656306369836855065787447206397138986901592811173750578675876529481704221063867976005645588291555739872144316088576359161715834982801156533498052600313807323441074489132367819789256101305123819928233676466962760933505343231007780681563022601339005591724378691853696583438079706751186890695455652722570277242828766471805348139949891510287655409292549388938560868216540236717490176⟩, 0⟩,
  ⟨⟨564, 172, 16876423653058512766487072155937886485131669176095512494790322715089044368784517013618166519429188321333244591305664231188736059789314575984786353613887657636611133440538003564607901473145480542584601128842991166167715215272627230404723985511961828330583304518260185717389911633183624376899172331830158570304035208167476534877682141545237436418381582021371116328048273788235954965678210358212735046502241770455164057634189120325057466791505781380928933154022224712597773897274653407750457450503325435712545043827441023730941349702530243199452417992216420074500063346343176402366969401652764397299684464657988262577002019889629049218897253012212985138613751913371051368615184267334141808183498709642470633855781802300676267987889606438419717561240034310467878410308840186689279327084530133994906327930412943712060639481617538141605942579464077546976786191533373208000147620303270292433685236929254587891044989250583831692325727798320187844476037793869135172037235007607048813215747257459866451113609505236414895641051669243305303383654429302772402179274411110852826112402478365641467286086770016793282245780795292345825810825555814803971593156697305071276220739947846988296828810051154925313347191705697476306981548650403233484391705367809552668943202588182670198232401371271513060805181285523115465514610715033390548814292691644599019507364750694666989851269786110139156758980937798319911947490315084598826067564942687955198412283010283482964295680⟩, 0⟩,
  ⟨⟨564, 172, 5625474592932555871879534886194124960955152660180447467506775697118521014508384496429236347156646574224145676938334682144666489210040236122224181706728302322079632412750670378691659147580565194099359590638129644710061462946762691167656426242876203369762069879584204525996706040895195606835155140377119523277037333506824990706941344650803317519952965309660577707866369508327365407472276470600908213784078094666496532396127339918604004723285261701398049876516790663172130343862869091103429374090530375012732561249105743657226601963986898718647215376847664430645765788815170984433378879262291027625178201742395513359578898240046426763723456711542473560546307263423680608030759023980530282611775642133798763570169995888396905591108008729803312266511583958132973154032987840489804628280588678716803774342997853683864798965116510606575263836952500333054388035579126070247772752922145264754867705197591723069426827239252729213301184117221355804652905749567614411956005306841379884252147483253341884461495760539734895752220160343646881971077393418256737785958924246832411007448368703207803419640717044786844217134864406317595398513817610089658495617248335421593817590997364919607802382269228539237848523838966272982637315535276287553735080346302408948364747601208725806797556402118738538201236739607795077791618653231905939370996186845312334226782468140708765281911699816065169301767926001473668752729345674557655029689701182877524060479845642028611272704⟩, 0⟩]

private def suffix096 : List Row := entries096.map CEntry.row ++ suffix100

private theorem score096 : batchScore 2440 suffix096 = 17190197667 :=
  cJoin 2440 entries096 suffix100 4 951677120 16238520547
    (by decide +kernel) (by decide +kernel) rfl score100

private def entries092 : List CEntry := [
  ⟨⟨569, 172, 5625474592932555793810392748885146885313232730115844540330051189087806118360419856677893083909172244035787493089275270785028061242044738372141476139863582561887734950738460067916747901367408175907904004715535979783039973938518459286270591922704513823836502827109775404116748437719136217530965671459158315345346280834704144441087245064694037699980426780717726267015945460746234782320673955609466857161734746004808790759682301787455358049026968914661261992685950395173402088952490852920458112097229942574959409877866946207925504472274224293183485999128916181800793394141800763801840504146667005239244060727998717337985178910972949467963159781400580895028295039143689944689586204919887877330708581706591741709689168834646089510101726712358883450134127256416409629945253997068484691521226145132699112121994737883583503997175805503728302095903397232461392907529985342478902681697699957130301738037075383521169516117595744760043873066022671415637322697180237966843401495295831919088545515732460027647316264903695933396858554335105707889793990269087261097886701966457134133322414895215657296122628569921998120815763701603314248885379635712062637306038728640354264245236698625106325322775241376709133820344466220558487584778952494154204905816527925711707322862231695495792716993982438263330013306120165687209763321661507914061557928624920114300923087963628187677142792897558052721683111636653929488511041101162328615335075923142371988161663304857042288640⟩, 0⟩,
  ⟨⟨568, 172, 11250949122995534280148732743241731790016353288322647689105281030681849143513862265758317474810093916405676073212057111959756172868857736431916956467368706468421555531317853032412216913733857668872986369778719284551717922023654078721568996676369999589777586888504184931536106932898778967709016691205795326931688494484645637216287814577088187338992541749316537309112633305107236399434050671308078924225453330381887232609370270916830292178718854300799511593711379589913249886234780228909225588621619525731575238747642810333013235548811916072836881722067461305497584430414444291342814135295319462461219585461116328552955851608817654973439643465971766741074238121201804120592284940783864620829312580242117836412735232375179295126175145451655430878492902029180625056660792220225572950407265208959314019474434323535415748004543537197886958418628144040522850176641968627669808805613981165908962975192478144663936256987967039680829505268154709953969789643641662789325652935332437844418666587238150022477070143534625174700123844039373968259348347830934594904932107510238600344801023847080904809686293577804120168272217433276894909727432423888490959271659962501230832857863709475393176423815044008501605427591856933214014287943472237591113131351176168665918311980159036290054445335758468908429591956829357316767895576715629508829880356460617377396224537729136979349784512163172225462501475564413938637041820928504676268227393836432124187272148314429460578304⟩, 0⟩,
  ⟨⟨567, 172, 16876423653058512766487072155937886485131669176095512494790322715089044368784517013615270774028817335788887049281305740677960936096825514727162138218202167885907066636255635569830309153527520158914954542160107439415936260671265237347045998317451248647915157600844278645649544235704968684175649642926096833827123355558163979112171384270480467953955881959305908042791944221920229408561765946759973807281832113496144140470985784943796262347469765718896041364576843030396573022342620595914379334423239848885006912944899280880668296523800999537292541262556514528098658728712237384831179920431997221617192537074245687982093681612789170904263418229007543492998970160497613318439033366083585978990442394045269795189353210677490532415186628324432535947088460280813985887901111811915903023002923261783852674294708771711670371076509024901527799924959255432582615332273991389947727619490735816395077671943124578648392831931488437203939625659430337238545312411432855718182172063899455650256106382079620579098095707605870132575260160275289672736550188711816817702114229533698665958678384697725313786739864043403828748752603324660742727391561624899805924214326559760346878105270207562977371274663278564959621341239481484925866124032791122706463011709596433228638400090875257625499986569953010654424408510578492381767673637844717767719639348428522350911354756413740204201906066871463497314638353913523099823373051204355445216865337640851112996358512339047249084416⟩, 0⟩,
  ⟨⟨567, 171, 62869577385541194891837541139679016985574034434773235683685290177635832775081941701696592472521009632508793502475326449612106463523746084092553852692572716991050690154950699396932783457424424842354297236622161068812044634681947246018279602158391191879047712455999375964957250755126780908214668153097595190837580036905646950519262465840972938873981723603336481829398212562015376212087498484053041829105723733132497889418779189893772678005452028149308842690191956373299980394680077351619836739552722628246815232860317038597817993012520674654776457721052309834831612064362359534203849194923874677500731316724101273283415138078583568841696093257547075124821312908428985653973238353139519956903837973917833208112859426193683916954832826940609132611461974101759508417604976731855327831810776811396135418828202548281414911886167740625770644341688586058043320852965229276782398361997988793414214018032088924430311409058775542765811318788205944636806850935994225444906072709912155548654771690821722838323106345921015250698206381731481038167177981585958308389408322833709797518267259861132603772922250776362612309496761727521934381674193955507189905476363297600062989782961908658398380734720739126236969384459256474700138271475130300583700507213580551050089395819864935054772024735523982641295409259226005097669130427232345771920512994995929765100951152089360999147626779894682997971453651599590224030116502912117680542278813549152186424801296908288⟩, 0⟩]

private def suffix092 : List Row := entries092.map CEntry.row ++ suffix096

private theorem score092 : batchScore 2436 suffix092 = 18140584433 :=
  cJoin 2436 entries092 suffix096 4 950386766 17190197667
    (by decide +kernel) (by decide +kernel) rfl score096

private def entries088 : List CEntry := [
  ⟨⟨572, 171, 62869577307472053045358777627117508966966246113835026837661601119337523337814045607263424432210936421614006801041892497893047491790628204910602827745396394717808014507141277956887729658611956077624513017369018909340514657263572563997662570560939799839196349956095512982755503341929309425324233909764702986794961600208675278527214931324673051635583016676466254992278130705810555915577709313826719848008285350940495815326717758120806799214060961910403424253225000544183665654437891402619282710559931183928477143230607062511111434367658422460200976984149973688167613317224326894205723869864649182478240250730951567067141961121071236252522985954264993294459649214162091102191027935075277111119487849978441513841145437499932273585302435093641603236891967635600882739783520854181798937751559802352932337057449838299549349226288894997021281452148431630827073298452754402805530781145719165084858789518159514116101487621085191780766680713103731288877457469139914489993326109822267547996756663233885919254157317250901430508434503752855555936423981655179358177828294848040472623862846888622123319343038242861029450643703407479913405158419432291269893800294699868538417823544814687246554475446261787388742730872660741250160613624901613224193419503779663292996235826427206007401185937269208670814091661728131683521921530618249551271728053968477870200746467156682671799109082761253143998586130491797606106021587324708077948312745118449945496675559669760⟩, 0⟩,
  ⟨⟨571, 172, 5625474592932555871879534886194124960955152660180447467506775697118729674954881626001189097037446546705658886117055047920922703683540290721819775284555316971264814927796041490971660378182083694673533192314813690594568304348756604474822167134144692504081350107363232898068963835425955692246024739714834295442428595397556890958096779055001977908524459797171652714228611324585108412056593983304628631121784143331145448577930344361077236946771275806956680230394438705267661327341915832645977901866771298837627852991105101281858667565356434959780781302976879533836837610788994530942770248111606085058255973352623372562337590700130482969409478369294320998867792829872543418031850828899786500663598803300701176248356289511882819985674231230192745616073812154523681403360827451679672770879120179996962207269142630983373175138507004786654598894596812585775726565699237291155106058660859732207763791206564630842060881993322180534762162524965426652262774019758360344958026448411487840564047649614722065168354423677083355507990531369928453443574168876804616017991721835529427772213017564686473599274064629974651730701155554531668577027307290569478683109873242856320213653644105249283200589592712328206101169976272697394938670361385037308956406748757610279627214965659302345328065314565746288256821067992852928831386133222269409311360073209399237249266991010944747499340179597448000890080721983068808940742528730795234044221067223408390876460292161717272576000⟩, 0⟩,
  ⟨⟨571, 171, 41913051694452985723196714276722005235993958843344839892606573036413815059821564865569182961235011313904047527233594258225239906428998539403424566100980009404240348931560007385264407612631840559925198479567854730025033511705950732727114261685831286345690734439570025687104001880384503267296321456587294897775230409147681709031592480163085325738878399098199339723471761725790751267584453834119470328196962727144977709210543178481422197234262038981092032076384948384893603731678394364818753068805596749788552099461545877163060937031597965284895121024861480404178040888861508550664899301357628960922054812038944171756462642308871240412695568036710672928876057176100390333454355379789071940713188943259661255013398049122686682354742706913581214798267790839850223879744269576270823659757269409665097511881740577923728580422471937394119764283085376242435716720923287622227799613569288180812359155165654866350654056885815720480624928832643939064897021528342043597279644588589945765391626629817943577332348075958570694684575664817195480756300581397753626094342018171139647923882129315090630223439902761345048936926265429429568760822896868152690572634167899952651980935390873200686754390149949947084071566150858479922633443795303702055298520836944133892865335923920937818066549588881580915854687531224230926939671633601370868369344451745265836147764774283537461312203162889084505864406159643508598179625474985121944824496847415287077182058210000896⟩, 0⟩,
  ⟨⟨570, 171, 62869577307472053045358777627117508966966231078265281374716470819298343244137305817064906559991901128697719608550167607806477465385276663176535574250782646873922922648991442873834259127865288670124880381406557255372955576404436651587086602423006817038085796040358342049981162385997917149568791526416769399139875324181262324234196019259348033508762125942947685161919444243964981622900789996193185922091885104143255101513475270425120426442645593204199119656042448083133809904346926238959903933167200588577124053643073137639327800044373121914334296234932825513847326659060616569155528110482385970141028246361803107013635549347308552418634475301871059343239089251751546346584041087006624571501240287695522036787632699482362059112253641746448193412121842122079640142924610117222509743956945009735125344545476198369701676414965410377044858101538779031719100137420354381336353993020659541900956853811857878534475651164744469033400083352360794949193625710273398416555839895623105515631944212634633565520480045176581369372614420772737388615120967585855185098645166946149062145114125937285635588883336250062675984957744421143492316955052182869444422310165738981078125295802110883622646919149498952636208213670145688929988853042177517634936248943482443265297373568010593407393017081522289655675195881718233265916590577690723950156872140654558657352506687597624208667213699363371443452514818380984095359676990968526080684834243251873950691055164719104⟩, 0⟩]

private def suffix088 : List Row := entries088.map CEntry.row ++ suffix092

private theorem score088 : batchScore 2432 suffix088 = 19089410993 :=
  cJoin 2432 entries088 suffix092 4 948826560 18140584433
    (by decide +kernel) (by decide +kernel) rfl score092

private def entries084 : List CEntry := [
  ⟨⟨575, 171, 62869577307472053045358777627117508966966231078265281374716470819298343244137305817064906559991901128697719608550167607806477465385276663176535574250782646873922922648991442873834259127865288670124880381406557255372955576404436651587086602423006817038085796040358342049981162385997917149568791526416769399139875324181262324234196019259348033508762125942947685161919444243964981622900789996193185922091885104143255101513475270425120426442645593204199119656042448083133809904346926238959903933167200588577124053643073137639327800044373121914334296234932825513847326659060616569155528110482385970141028246361803107013635549347308552418634475301871059343239089251751546346584041087006624571501240287695522036787632699482362059112253641746448193412121842122079640142924610117222509743956945009735125344545476198369701676414965410377044858101538779031719100137420354381336353993020659541900956853811857878534475651164744469033400083352360794949193625710273398416555839895623105515631944212634633565520480045176581369372614420772737388615120967585855185098645166946149062145114125937285635588883336250062675984957744421143492316955052182869444422310165738981078125295802110883622646919149498952636208213670145688929988853042177517634936248943482443265297373568010593407393017081522289655675195881718233265916590577690723950156872140654558657352506687597624208667213699363371443452514818380984095359676990968526080689904845671676334369258047799296⟩, 0⟩,
  ⟨⟨575, 171, 20956525925295635289737555194218258877520385124220864997543585259794466638417615952632922991771892622246546645050031210426345695711838940652070047767823165048734507137565465866312524643666105376833347098991278001933560400946701743912401891274168591458043773927790537363765707331638751302293401485697094563031789001532612666243503073444747046084056615184419571056405817642301960390679534713799100401386927442757868594329098205397794339704651705432570649457084796298060803525505811490112832176398096313154802173399947387611685335307362113035877875418861913295886462731979581481776458953564425483338100476831222321940364322653062080177175412335683053451020913204400383884492642659583437427577575585939397458353797753883580549841698677608756026087532579473871139207613256537697958920559053553550582548274149687991752965111144176600320618327922591634144129630961162709023526031513062740551765544946754410360420708033834631841614726834614989698772620368997623703565555116028571391041035102412048534378860397458308176156831332207507862853086424475340714464226498090639200710492041783171118606209297692397523843460984494298883804965488360830093413851587221643519614986467533681969223472760014076363679353274839963099640020787463735684248627010791404553801572207812661465928206225439411552278499113658440171526722108664932647844585380513414174620668246839152734905865491377652412719594919875485988567687678785304941442306321251922300643300629020672⟩, 0⟩,
  ⟨⟨574, 171, 41913051616383844167548167494094862751723651916990606818740371728993390290118240810030391345955781327209160004601095288842008161801314862191367732239398011820098592085085261733875486678383714217219450957248804288177631504921816582685593503253050146958893488677234146488964956003795485823262545061133039470507534200268408794761776233379126292984904876907583534719162610405269852957832734092394421747994364174813846417951472714064956192934099774410475542120446013929431730205186616026780343045188362705424418426192656637996466912550390163793391326504479579839878627625491995321231051982463561374247718235692468141427971984960566976486050340576452942654556762146820449125596960125232523581062030469147144401743866623551489814564214492869013600722865502230790874833727632583765677303251192491349351956797658965889098879324452732307118088893435455105614952823089662843229326696975893791597034469883612581731261848512749330283717532695647143092576459908507474657591042853756734709696366310868611215871532651865077350034927827471852361264257251617596315874943924880908142686996875756037769173384621448506325394286910965477745046922808178694686777019102431400168124866394131397166929678014922379435891312749238205467559426913791661629520766686907883451203831682024851197756228442510010577909299321342899682064332714179642703947446603018968363755152279890996453128158289543765191199209515139140862786075916339767550523353618004302787643786429202432⟩, 0⟩,
  ⟨⟨573, 171, 41913051694452986014026929923229397994971142722475494239566081556815347412772607230887010433857179397680693333779884729964954324617823216691875343844133236711221944857377222183031845394224465621130750052442398511703124029729188143441823674597330315050206247434337671834129515003266319461453025871441063546146688064995468241422795567739826660488973233034931302719458326676850205449162020817449879523353911262123555180781871318974261079158579750146391221013420201405461187396375348372897277262137098068158302685932839882986876341550372399852613432032438185174054458660524817686120171152410386162356130450355231700818420017014897683386592295751539419058487641518632255750998608885054796293929693030327005030890557938074493099370752963552889097546398616993436140554909230113922631650628855540645575036423706812644478340769907076649865409225654917517969261487226921058403950925999657736111019540544454216587530407301255815590809842269186199961299209627537451512183716297368986028099626046770048670253563132345589992112539237486012679876033673559307590100284103808102399033621948046665943593757859776737371449919311989899155459838850279672359866069097881961593053024263037874919891437527599675267908854393095425868739550136327251399189474010106646675402904419937380031020229707065586106017130348419311600123748944044018980682107886822630627135789469729877209237279475328257751081035559402807209886228420876221037811380074478700530054596936073216⟩, 0⟩]

private def suffix084 : List Row := entries084.map CEntry.row ++ suffix088

private theorem score084 : batchScore 2428 suffix084 = 20036343383 :=
  cJoin 2428 entries084 suffix088 4 946932390 19089410993
    (by decide +kernel) (by decide +kernel) rfl score088

private def entries080 : List CEntry := [
  ⟨⟨579, 170, 156138284856278396111714520591206868126965961899290179295657182768011458307230293400164324272321661552941852636445548138910196267942914692907279168819664297942931883641612743065303463014797006049162642767796339267855499088282013032471421739317486792911619042895870114727147568380023785274314228022620983640153979579963196238295509591354233016739963844548142323322507630534592992299259142439776814250631115801085599675019108363948792593317616183662111885307396202184341745991072939620743794858815161071373786125188286501974945816612299731702533095052356763870027208352552494932620236615544976308043135643119209225363966163091648100259350352974797785986013575012497018468453964845483371584149686883693579608798741854172101485164851771791151759694942109083022563702270113691873159437613886334215640672094885439384695900865043187494735070511018742530120963575127982054193866449312018161029823678126037071421755564767547133151752623782541670079478825910512333216695854910646317895478437061830055568203217593527310762608377615452664662416949371732886517621570688669288363678369037394222911908803372793269107226469808000530640550930001960152230770824859251774470945657881953785426366992956799759441696722791956881202572189009992263843651791832714958634160064348880029710620748512759565341162833433199765433891153992861825415613739291731676606868169936139494240189667735055571821138122386577183152495491943228847028265348107447355029061632⟩, 0⟩,
  ⟨⟨578, 170, 234207426411926943977768635850837487604343261861299281473147420137173003310137491878194643398723610387683553870806743380973025241943525112987399462672611049673601569951250977789240480124811568225335773932268839539990827259519368328278369689236161287034648925272736622722916058926356504843075785242151114199061277870881846931801839247884820635128689109326314551517792754546209291222474294799483383567972186517939198717360875233905097232780479587089402342217232291436986257831389653794350777424737300249060606573117613221477364111338718873852130588185354826793979317409150894984187415215401317186655409351124946697416981227599451070774232627549307831807105531774118378999147812114655830964174816433829138305660551448104967189571941807884839494400375630148626542114532751722950423494031123081336377669777956967590413910515384221543127070213498210858437755899464728321511694057678050518478238878520050753637084900268831600484654593349336820112510771360324701755201318095432681019846767192132288320455999461459758139035719655290492740980496856655846668505287674973223738718762193021273471191153829081746798381966714189530948936147404066794432531680825189297713639934139915261649665636444479808623466289680753626679276557104132635916087866823779138366979422128031662206349870967191493725966828373104971314667063701365794287370251188105116647830066476563253253181792591418265702419159246688357427638740011167566247502972826944279618256896⟩, 0⟩,
  ⟨⟨577, 171, 20956525925295635580567773007579613331538262442426560325573294226521704399989487590004639130709447214271736966480609525110793932425758858927180283270129251016331901352082256570667021846465949008630509349266637165870171251138387948851831715367326419128003390676026442394890639379476129625166300669497550109800731665745472011093787840445589039139942793491972476082215489606898229519992418567478959849452979315599205231339591558061135011426233225883064840046616224742962069547875882968640990387949645179367184623260385728789398182927109230528712662246645826617823232650530439627461014236433230135457816105345479939424269853743287015540521089826083243827025321311159071047304394310478309692465209717893207966245234410125403999494614794842587106077679981590637082572333943207371378691766645729942328259577101580424669317015754087788894253460697077794334204404766699457854603852408917299082650450577085274688956885174076726230868696917402889923572759204612721378739949300370922349746672788804961333199567585642375439557813623349059734577066902329371078523687168536674756215324914555982455729241673989762268634824776711651999030168979418514314343518178679122018523718839241607253661074075890645484946731053828386201256561544518157954526961604957164705199400573199651596268880073535945299437067648085884735390542652712703620326069618920061129487953342385011936240666699945056110469403911042995375838550223965261916131912947353106809866493341204480⟩, 0⟩,
  ⟨⟨576, 171, 41913051694452985723196714276722005235993958843344839892606573036413815059821564865558395468948007030121299820480195253448583084397280238603519256026162717684213080386059802039676264659885479832483381667191249753872967563886488813235175161826405783892358874196928113287825948737552363998509349110901931668817116067508377974242113203755419249389171828940512140638651285415678318522298213716503187940016132295779669864593072751273372456419513947992753977787775270968025750194268109067904028779832942764229658903065959165425264115745899254388873722351510032069220377738887722667893119631256106193222377451819790569007483567042272132217166562906172154396227299812106167058467332379762640682388035698691867508974583777243748341129310348859234438958171029140578523439914675307536996476378790214865374172872794177600063874875662337106253863937584701945276871986353987516422830318154340117003096354757522127434652092622278767514039000054817423758533633753323664693319169765438286122916917059836741080973338339457481576462662719811888195266924803970445580632346529198409316935015218321972645144498191545344827248243981585235301722994791746309046338481751450658139867846986535408259552271720924846224044295388840544271903611497730481319329262482533812010608126910009666790566444696590417715486127546463263160619056973695214020545386042037003245394925902138278882088564238222238640989089111581741255405104449943659382789505632468317753397944708497408⟩, 0⟩]

private def suffix080 : List Row := entries080.map CEntry.row ++ suffix084

private theorem score080 : batchScore 2424 suffix080 = 20981112590 :=
  cJoin 2424 entries080 suffix084 4 944769207 20036343383
    (by decide +kernel) (by decide +kernel) rfl score084

private def entries076 : List CEntry := [
  ⟨⟨582, 170, 156138284565448180465207127832229699283404997003413487794268995157940496495972321377363578545037436657959216716819258100293116567333545503396817762968771750011232478415551858541502254771555279781994003679997218918369565410006204732560740740243754731887317988720660050216928924805594715523503414614956324744582123133767961278331535009996842391834764537719707470966168652941208417447008624191955765701427916854869465942757589491138455608671869789587266743321722029612682373331557185840120466160966482024189951974578326486143689065607707967048351158465662394507497689608445920208058975194148941363677095548065182038813901641080276915444438206841912145872499137167195690351175554594470129390401476603438210498890140451081684320635955615759911066194227519751554311208892466137051936877489841030716131008911701027423766077544271701527069905648230253382488684987587050056725769349675596740775224215651650587361821366286692809972019983696552709619875438812734762126609568579397339640048603231767612708283553638624500946635498549696484264882487413091074949783338138245469380846111132827381067579262389537649765428047443162642462318636549918511230454239547347630169335128462155115068691284412976624233717067761706258501650035357351663832479164733297475797025915785060727249736957899549247434126897536214509771385477154624404417634414725315382960903727044610255205976117413735648388921957732133455810943143221096065567381325320434795560304640⟩, 0⟩,
  ⟨⟨581, 170, 234207426411926943977768635850837487604343261861299281473146642816433099076663351867589751481979717048621623249911396234506657189300770117540543471001517853027552750485951947285609690325452745072295312777516698276125296322410132309063620699450701473404628726117197718981627440458419451682693549498818748226118694095591551191087976640759387457947770473837041992996027250173726330392278038515402131068046013515779313782456362610120403887792305861543611872366359060700723426138894426660313996652235831793164943786554730406992425344104948360223485546289243295958192179142967515078548221292753060598528623197882347967294594225730746527769886798637956492485457420544821055917389868251049990504657396414631725245259229879807916589569316457898518638122574874551547453439112336052194725771309649917260509985469865590939264127220328710794547192101546223202062801745549311127955939303566213996208086704441787916757357270914495343570843354665497649201153184157581720441407720361274113555933834845617223854536365796597463884736036610427960430876551740290708870192730071094194075660595603759948714568242973524471368551557322517310149336344881563513348829002702484201035237450351574093032663020434365056910046776633478829388147461761291885828458538708310740294944558800220356685360122993212473094382014652825547711825620726775455203729189916206467997182670850431817601858063181693038907646584674459268817479409727467731955267861557731929083609088⟩, 0⟩,
  ⟨⟨580, 171, 20956525925295635289737555194218258877520385124220864997543585259794466638417615952632922991771892622246546645050031210426345695711838940652070047767823165048734507137565465866312524643666105376833347098991278001933560163480163184958088303838471255893629126229775339174064979170841361266418666509815463558306781132449861151039686648484333279469037032899323262606193105627066106986265182226306898956841780058916202100377261382593594891189105525919094832864893210737560095819599464900581181589757520007318609985945307623332970628942389803215314621554457523250524109821052252211535169824158237346576741794500618019886905141412160871131010157142330059582428368875116290227294225609650267066921132113144558694732548876133384307843897004028313166736727174679016725944045812290709926871949712743862314591069082345227960231408081371745492942750792190980430127300765766294988381156652592615079556966956710073991688681975312613029209461535812090931454229645911477586299703947665561248202709321994865525965541872903118052240783204638812430467448721943433668590717874829988442150713371981740030952134719901023879550641058944672329415371071805699019375842264531357677019505017994240910121714667602805598544550896534441909877463253024444712607309055077784579604439711514465402815945800459708735027303597454079809658432797661989024039368233689281300923596676803563061426277580108123643249078902279551687419679958331154039312156792988621919736117876228096⟩, 0⟩,
  ⟨⟨580, 170, 78069143009799633682579993420119403972210599337521268738768929490858295778757118522571382000375761078639130244368213919650506029511430439565771338888103663503444183291831863885217162596749651240561218073535336302554847069669493026442913412173118904219508787187912864859140706534779089894041362565398840669166625720580960470094043303878779446355804560123930930798003442958957494719020450371721214337021654905944302330054979426084168467005250295166514411032569163632069087612549197625275738946701608525140471009810050635025043752240031690651984607630151657633246805214329106963180640686884617322026157917209624784145090025006774243931684132137992822500508211012067913290262426051072641558880332397620669408841154615472809173760603722099917874936409237175846323791777664152698634627712336235482603089395413657471630178417894796506239926611510954408388697678741255813918382594293264260616510875568074634267328888521442446523114012180153406583346078576505477417674602390262971764380394757791355007003226342746920646965836549086636779609379926545319161495103317433399513730594430479878608598517538760044471648290053555505332000716786877218247278148115337181219131617876350578587345815195229469172840980759456722927014705024386854391710147587766932751601270281080055448209349444285697246839045763772040144191267304230346070752702095302000173755389897776622818530633062468029760127702730810199713545581863221424916136520360031862027976704⟩, 0⟩]

private def suffix076 : List Row := entries076.map CEntry.row ++ suffix080

private theorem score076 : batchScore 2420 suffix076 = 21923463453 :=
  cJoin 2420 entries076 suffix080 4 942350863 20981112590
    (by decide +kernel) (by decide +kernel) rfl score080

private def entries072 : List CEntry := [
  ⟨⟨586, 169, 290830219980215348437698932964884620639121869405756450660378039263233693144310299119676411153140224884481387020057326083136488871198969129931351802356960254938685217384046283974308021522539234227155640752351691248626356390107714583752996448994132437792448588152742098842774529630261360752038112708132996955506216494289523344441208876819038670461956021787896387559644523348435071553121764365782464985376809985516368584036761398735461287715812910349504257022730122731097144191521032404463578109797136914531963189662007843111933990610014066846564511813604712980709617158780063376085866275660691880293963096565828610826418417545441173006785971345628119900196620169835872288595819003848111440418682985435369663197784631766227693262287537920668486160888425656598567525520529808030910532978299984079256798999782175409569309674142422467723657552341459815143527159025204016237898011740630406592326832677186785159755262881442658031001190353075113205026976604796858126566803415042363395906241872923609589465057884328062559386428998480843935637378450625400256096495603758850861177122666721333566868492868234262243458054115762804832033097526514145756676801265278645963141203179246658275211845569225100849679293694748083198263025728493766657141419655547697439196453459899915455297214070296452324798985922171516729047982457856241407262707093086744267958301451145660454717172837611980008325838717531178649277576261349695264248669039755264⟩, 0⟩,
  ⟨⟨585, 169, 581660437793576702891716810283090427990875996274091971276913519084496268284433683008567706764942636910609351979365751664751009151126871604126986745073140777434899969553994920348016407395888142470876286803917360558567565263368237884608737153252537522135745893775932918217582882866351996639051392758715836853362543806296572976915201512553665849342807548299961996534867698455575824898701691775682621637847705934515594225448028608965846126219690530233501960737244047911248154904965086358576248805281374869397975970761055134143478485242648913348216917560833557956022055270345862703845786361191333487790583234724436794832222771240950004232489887531093455798974540131155470268629360368413372278771128072193188998098454826221248079705431207236467896755569089513356103384010917290572670987300151341466757178660055396648853647951197577620800847228686297424588216748565368556208411042809554044268368475608665762177689242242079724191697775507501028774227298462809373500555213207924060134136814854406027377408808445659692446173644123422595346037109835940921744784603598226936295248218980546304107722930285549246991230854718144806377725050277773456703904433092747336087424141506677508792081570522143588798389972286524801000467529893166715568680213547835561523544631906473826993461361599057032090782883598253744703355696726475744086258078406537217145189639134239504201635080207675556327445118148305064502421513472731378385845238240378880⟩, 0⟩,
  ⟨⟨584, 169, 872490653440084099686773999969800888018098704000187223677141294394332927875732972764203859115852454258812792117918816883016471721021552059752489113852229721429558631005914801810492731802504735336638862106246405939373339358995063207825542948201324805261012508314590973711841353155773966352873823244699425696823690242511893228104768073250028460103574945756578050135841757519723564850805719956483198714115100034911556143676599965523973923208598539646815739330328345112519476466164585351765247744059722361784826621057910846358297770354087251230302665711450672008842972617463677980170138566289666721450916858432237893201400823700453669057819380673664398747572413076218854866998598099306614865312881966173230608846470480107891574489642232909355270159555981399337139716158252693661359097655565143338836166652639933012213721835920526086101080348868280850556286860490384148748495920875322770278466877591743761271175015984703177503320591889115266102141280807521812893576708752851855656359385201533423797280747516835286063771075727467786223160016536023573130138903346818886258031068922050676026288988718922721213869555055594216582770499710891149126180969648596521297774070513028423481377900766953990150955898196843702326610142609422883958366915238900403287563172645513487690268724118668634644600285908410843289022460686099103243425093475570413509593600007023661254852723942428368633839333848182751768575821590593861086818926438907904⟩, 0⟩,
  ⟨⟨583, 170, 78069142718969418036072600661142220093079888978699446937342339107847602665385185144858953098615434818982098126711731870140112684763069670376108151935522448332354058891841234902542165839917767825091292520115662984066349458464935231401889455941790413588298077419498720745932203225682013034318303612597896103269322628898424723297006930723821333235856822732658806419548139968854760962044460813230533811193255453295979375216182016505620227155412648009200870242612674978656211069897293663995224702025195915694358571057421628160115785742258637469030340205904357703906500854247106818268840442381506918218029653405545543935364119799711225415242359943353187750032112642507299949161714123717981036183798662515550129237592880269974865761534655117725724483593302494615637836768721231307306324565429046885955287847619708036059356715155582324497873434116097546799274603681685590483442234799254513761903932946040067846906561381133090950200321726027029612620443899830808533845754813001599091577854945312473005260982522509238099381879602405647661489869243456956185785703487089905891768097484448079393535497697399452031032272109136057714704357135613013480771018753322398784838771020404174067035750872220713019678885489173325163683719364775431944276414983712795120117727579748336037597957386372611388617854407392692806923164196377999877417855096013809491982633470697361351165318029118326877950299579967262401699198403227636994979697393882288091037696⟩, 0⟩]

private def suffix072 : List Row := entries072.map CEntry.row ++ suffix076

private theorem score072 : batchScore 2416 suffix072 = 22863445635 :=
  cJoin 2416 entries072 suffix076 4 939982182 21923463453
    (by decide +kernel) (by decide +kernel) rfl score076

private def entries068 : List CEntry := [
  ⟨⟨589, 169, 290830219980215348437698932964884564627259556124729837988847267284421632682476882431130681553727866301694206388661671099050124440959698237573929740350795529057292547746948895168400166386445218669648758799501888963178840301435297916828144434398134001450895061986859030917116691361838828211510028873913656187791487006432336630113098504225416283363866916634884037558488988076230524343701417251519936387623034918927256723874028373455289981520763520421762508315426614278899948821022014314149123184782532371219359675273091197379156540946649668465209691819050904675530929333169910961831477223194748742717867547142585168464885270644451265295920342101618998991610250076824704464151999766532300779910541911972888591011985915404164117839542105632328152695275839908675913438193552381319677764720175173150443612603644474519213538261648393789528771141393705579063298036287769940656232371252324621709019727960318561472305975129721522264602776715637329767374555794951791134674793416777852505182636312109992313363753293359157493249483627743528770423037100068860108796942583069093335756669055748750078496004540985682994560807934356060736489791132530009282310651360448140187443284014920830086812709012636893197629526595991267298829273521265563055391027609892311057137631106546665866981198562261634753793868111723284765833528907192217832668361476901964716168724284295959980605178255037474701758236796829287148327860254357974931404790343663616⟩, 0⟩,
  ⟨⟨588, 169, 581660436710149722044196456045768034768868226570686279960978758178429665028945808773352125827362524933961096096110560373563753691813146708148784052464260719758393162546872565677397902203929721496976925730694900894051661379658448444905656353547255441126666921081617661628607380411009175790486539210961478742145460597306345695002134926605382531265782332866294201337429333259196644451501310586764535685732650961240626658341249418029396268248072972846279827213741949247875710321803338230104990903163261801712036038109386288164887821703061338694211685902112701935685014756194949925165531017441084100593237385396592463604739461393195820765339608646601981939744715270383992609290609488152449542289512617283353577890025269544438722118569969236519434281541108159550693664299198005541923930830661321864020112572986734747015228659926733102909869135283877635332513554346002849659954569025325554517001716984996897585024559075731076195910512270602247192991669523472942883556964171667917221965652822582471029026633644940335104746738633872882518479553658854495546904720881005635041170236218077618880492681225902027507975874256948539846832441352004227155649064285113029812779756121915262448382692087354601300198837227025100967474413504271447034475075950091614563114627395051446742329589648355720319326585293615273279642601142169551617035324593318190279989417808541116140693863532452465552545926467081367265221265036989510691985551901327360⟩, 0⟩,
  ⟨⟨587, 169, 872490653440084099686773999969800888018098704000187223677138398648921769397941797478458849646075505944421974010435477772752408643442280628276530549648501230826272993592720770887943873708132489785157129352432154468591397767392879601407740520892605819620130656131016678308817153104752827857145033571309537204293680111182132912635986273909834453787997953813204336703021864034791661908167413052207206834706009538576422780070858415682221669758789398866827535008693130872117715661298886169871858546631820073676463712901284693221133804217456352006493940142202009779998849956641575919052207766414856105682520368016390943062827832216323257428410456455048861237670781021372501008543359693981889189891968395869428692328021022834009150210804817755639027824132092354067712151382964979410507601791627502209535139353366862237828077861324622734654836025337966853579085585725290697054599190497001357753077416310072009472172455846878920366970927989382371380364987240167345876372819865838565316571182846924045260862993757055932468916357785567531003523417705731879998155660024789762637992652170575969506559433233766638171302460317845782678513118630291430760387034109057390280086951274532485361832314550606812459484771186895549962317263546624519173904083195578836669817679713927871875788684657899762877482003907701096327436663607007806173986749689062190285325618144104875601557348142023304476016454349892126822265310933051896472428835527196672⟩, 0⟩,
  ⟨⟨586, 170, 78069142718969416952645611741461824169458393470275644203810338898727546030305448811618384158590668641586276453014205112929534982280807449271687157091992081281250255222903412742068345681854055188501905304435671350816348246592425205714565328534865967666561630243727434826314737214235763870732927275520401028379257424119255027740479966108941720707904305269819821629041977689613550808160254913032034346246467971711716489949053442238851920880483688792881387623814924922675700102790825853614523648694211907840643401428301299647994834950014241902165285651271923071052792568184634663003470251004162037479998827898205999757235040902996262491941151515648592208729078759929093632489392004066487114850416578562719968404338066919433491090771900308985424860643967026718655667824340147223635771383658772489945907304451583236088950580939439944469129615494857898996891858298128687289026585871349219039270681069456454620898389618744257036384750649984909813937871335049043829907068142541757973415449677490532178378219482065419155544812026477187580411661683120988041178457597185023794665012726741558389549204604421035880468415079077295315060159401497193563988486793288697533620334948947991016181041835021820309139770133303252263272165902621554431870531833136423317668896435232222878705879746938615593431663920927551066937779828643125794208158345875113435183040876806597577724292896903181934919356868107658979157074089277732951552366371084645945049088⟩, 0⟩]

private def suffix068 : List Row := entries068.map CEntry.row ++ suffix072

private theorem score068 : batchScore 2412 suffix068 = 23800699191 :=
  cJoin 2412 entries068 suffix072 4 937253556 22863445635
    (by decide +kernel) (by decide +kernel) rfl score072

private def entries064 : List CEntry := [
  ⟨⟨593, 168, 1083426996991840542858909376154078254692858427763952403108526341395483700157174167416884504858013824635052885961480977252268317643790865996029736910310937743080059936547124465362317647957519295261212617715258379341940867626631689403717902616326256954684148923247591839534791596986126381168171296458530031675261093628271566843008776955105977878145222321607241433975038181891836092221041083952682215017039146383477872386661609058740807348431912641486268779856244177903719509110768109556553737228077309543690356706146338303160768767019331229074210784081649311115727994985077375688807608093262051427658832903600966985510999014132516738714850405515959784871292646615038348884268824702171820144917723539150579019082307654878832524638060564100346796709957405164020171046992288442910178219773790010373577508652800082675853633166795960081011007775732273445701546843511912574888226019348016782278905295754057958697692372771597394230390116865282352925568334440906197081191217211536732989055931579728454261281315660139954347006812961614399242116798553192100634829347560297274191839456393970924413080544694748509824794130219477635839200933602906611498313720306873045738971347354126602337747571999473318724364138614661638529673138290658373301563298638601806134331685097399030265645274579329278756149370821094278042565520030467255270302661890986363838101981043348232161084720632126314706442016481769076647364732093368164454760448⟩, 0⟩,
  ⟨⟨592, 168, 1083426996991840557894479233640747594234056284300075660125829425689703573079073053299175244395212176756863992735957078945400151875611279643816321351963878627638091211706572338843002995560091861438585969628213685932108597420557270138535635355838136515738251016112946342091167456024368706166886213079590339047857435398882341922973129439424867445461288175686807884125577372865509508375532047323072198723915256505893053800004576886949916510715383702328444484705962697904918879984025032834945537558932367393866044244401186120182029867954604576701538681289571199494263593698963759005389609469699456841848653169594066630402275985276107389505155277794704287872450873888417602660491388305455861391196709071976578471057343284004405453344328600756274599928128672414747504985420506959584062372346470938678681485577644759193718592757866088754902905992678793824520658114706994354725828498704895489707964260527740321774275678555230765566333003239642800700976075702128257079298620714527236072558123833132803850212534891028412880122511378488362537208200703832235450823230306635458406824135873002279845759190413749356067882517924193739072569095705322776357935958900127506007482019349824317382596906507298932077746834011857021252920060024001493731642632837323473125884767558851960783360661843385016650609582238069461280326457449739767107369785087792231864543158824913061839167451689040036813236528972674930517546077298296492761022464⟩, 0⟩,
  ⟨⟨591, 168, 2166853985911520953818100729149171814288482056089088213730281289981664226518696855785577396917874503547733098191640345993455533501233427241917650196973758851866796499319355638131560412779033714796886916473200025255112220582992724644425277237789845176546819112360227548396523605534255492087645056689962136944243847602220524016451841267025716041560499177500464009250952670185177865992120250223884812138407326990796604102283822778485142164750734456753365549211368143227875809762496822918117973228102083762727588306222316377399409134844872777716133436414724431768141892814434553324601748441127439915353742371218043546498651695404015497239268897217115222658867165934873634087403716029276595558118552238468784831831063427855253516530361798541500779820863490973994520992081304231929298442975250413517494420185891526374420702275624787884953793990188454928205224680026503489197831760382481084273638112875319131380652048595546648620433269096542256974530586834286799656432916253522262476894314789794487421992452612741635911813542706603539534051380440372682157101495557378740218461375611075401707451530864645715770240331881287717736233213088562550782801334160370141593456795578555381755775297671949336931439194716839180359323610765533426361159831530640213307900945742576353563616785689201350764710541835874691088002050243123736097147505030806736388643299775896443495417737816357263621075564335581429624874376880567894477897728⟩, 0⟩,
  ⟨⟨590, 168, 3250280966759041323090992867834124296971033155918818800438711042139427948334025648318899797742596563462905207644030385705742294943166633697457931400073906294158934919290493453010089932957936703792162622022753859570973694587078716730082405166460296369136587838987955898556015700568165218774736269148003942573449465176951659796224614786999540277444699056002776449110423693807090963170606114236072099276450772150036306641823912874496057689944480046332745885289205068498969383704253319630198380050332638374048041168874786600889059254623074938841407680695750274995149544917146872047830973795526052856699165265465291919053220503143390128704782405671848489313392453677606195951064102770961709401973577296287707104973194076588789607572461703304679329929148927065864709616521444830340028442405245564690360105297800745372664470156733507554867047539168622745707813939460747485213046538950095731120174941831017679414111716643185336039067805006470473927044280526148762842851378720053577387736214638199570249206076531531526967315526464769587805763464512269379102278650871244531081361904913738831689265306987238974199117142845468112712972462407583554476468166273849071237144084664107683873794086798201181493370132393142804475647627104911003602225202363986318001193432590283001283713152200438852215734847342124456177514156287809186004875648177512208964595483472505965737588520238478600031917516047119052938941076541689582816591872⟩, 0⟩]

private def suffix064 : List Row := entries064.map CEntry.row ++ suffix068

private theorem score064 : batchScore 2408 suffix064 = 24735438337 :=
  cJoin 2408 entries064 suffix068 4 934739146 23800699191
    (by decide +kernel) (by decide +kernel) rfl score068

private def entries060 : List CEntry := [
  ⟨⟨596, 167, 12108240152742867630314055337883995089572046532924543322766985901219501898937022866006567320758836580302213160857671446002059783574814474945731205493487068616445865181425561953373588371865215539157996408726103080700984949570442425944218058759198696796359821554228499153837620096535106073225797225341215515782868359897105618552210237037388757904785495460043759826982109598096798968205623754248291623877178028784827540225624713579178071357102990323054588903819043444465731768698443918042623922416316860817551766220013747367594611848231684188699005844800734054279139432747464150368537656201146739932519068067764088209916727629093043985608154556422861253147544166734837725576252128075665643073519979776023727301408328401255568890170982864889052994285333629942926427783524412029758201697488298880645484124488386308299990259694805396925162701082112724876805446816462082733262503664754687738121207586791432199679731267106478423025711644464993752267376633458393673758400152325829779311031902723757811819039570285124804702831530812269403806937726260235082739139537778662633453912706602603274320648394563375681735247268609225760831287495936809777169459539277777006955401031610809071906441861795765883608118338138762109575499605796513776789065430758919002177117430496709791717149606493132091887372656400603350879285844059368931126207061326102650554741695363392965315681838419358151467745326705686242482609288021803008⟩, 0⟩,
  ⟨⟨595, 168, 1083426996991840557894479233640747385573609009849763803142485273198863985696721384045223450488328435650818818765363362055458592031000920525096095131154341731433915152203101274253428602168132434299769844112924817812363953521234161841974200436465941374938544116865318383714807030103047029564494048635586426744277377555570847959931852715586393208147583709682967349779647008850347207762204362879024897610600984002052138387194498719653415991994371234403697631546595048793537306558281062190831199837949060043720631383360742445338759218940468082560886496705639268009310336548142308302131170372701918670520282011150482640988487383472138113554377892767788983955141644977715678496144544813727938332098209400980717520336939624619173230855340972122237444222634169864895475338481565228821559760726034088658592479582462327759680982770639604130763933700647115701082958988938512262301009235178081784906114914452489522387727906319405069073420925109228805267940033070579758069218478571753216295169039398162283188711984917575493983118962670975985171023120900864754467350894940699747946882576895237789002911270585444495736959772218681780468171413237497465308142288819565212961078281125540201978983034426316672777275518659787984516824951467458043638576685442699471048049926156541079464209529520993164515648905161922482966724263985014703163525237216139790095095833166329895511964391306210858709888920846628915832866288946988865768390656⟩, 0⟩,
  ⟨⟨594, 168, 2166853981875440932974951178005963693443194875756972581002782129415980223674125257035166493905196059249196559548789860209687626703877548531252086358011740147167418757628174743344626956447697138402525058875586468331708242668429197538292617922824827734852831516718930235611674861650948136264408153336351658188348489244678414221860971028377795708424532163390123104070981343311058895481755251388119666597741287057253072628160005129983262226909670877629070830396346558808817380375427522622439976420861712849557534002175131023544400266196807245523839368834278025135170014866154595638364619652461546652323952827139264128437099053441013115798663518179343982054868978006994619351789485238997072481884175626318487233770031061727944094787531388788961436457639819563207532577011293026080155721368721042632993325999797810390066251893741063748726799517114587839830331465479758429931370049920856013283831762044859929853568375274099643859673772856481333904772830136129695016283184087181898822178259061795427322006016549013852854221761965141125835831926978360319257541363740723967968992641889956966494773871469791171389059199516758771810303816952592969317302256934667118195042653502377168559944596376102111638056466223498133622269402398851898947821482926884585303306206306932127578822811927304270316090649197991292878628444540441974131694902665836718087741708789305605813331466435665404567742101965728137289559306557740664531976192⟩, 0⟩,
  ⟨⟨594, 167, 12108240152742867630314055337883995089572046532924543322766985901219352192408643085742276502365592865456983190520160978031377738742855884994061445992359643969802820895230743443281904904553387816517577976089150494207072297317319126161546401511290374780895488184426454479747608432359984696152014249250072025547354527696715843951780021052614311951989261498435828344519575084298086158187782349796124498546384805877324280788271660065400249086647729830174373896865729500650878331675914886393250737653845828712912742654312990470426761372111595260837784428817359841101792410864601222662165321919609196977853376564709816141413409765430531892355248919299749183443465086770403374546214432444261726999512168654735531807653828623633345682048046112406200877977425938631757420407594263703367315512688211251578695162219962730946022337071352508378813628638597894215654460016791264768334912417482881443657158575395338527161021800011549425887410036248059299895454655196060737514973935450270999211341599973213518382827904543929293647524483645388102042209334332110715034487026478667028929036745224037639106031735063283009703655279650876886132380097089595531620915341690045675833739060672152887921273278442323641550318841236579967260976087414843654256168257834990214326334271632731976934838905317725654264320482523859480872788453210475736392998485667696441838000257848980269611666511810050389088660585320939683506701156683350016⟩, 0⟩]

private def suffix060 : List Row := entries060.map CEntry.row ++ suffix064

private theorem score060 : batchScore 2404 suffix060 = 25667131473 :=
  cJoin 2404 entries060 suffix064 4 931693136 24735438337
    (by decide +kernel) (by decide +kernel) rfl score064

private def entries056 : List CEntry := [
  ⟨⟨600, 166, 45106709572460009270586279548272472208634192246662614206846750904691786290737402013474242770543667917910900676698092289385861675228386688955357097060828074700395840761180011344261113198672934683105267495249027364727378999133851849144497519401052500236390114517608487903131576002985182017654233609326452112001756309333130135952606875645422607481439640739693598242549505398787879043026947788134681055495086334188745471791444942598790858263700194024199150118476634847562306864842455410932193464241347568902793313020143622422318016633807105052611918854778110389045597653331612134956439293621514726347675087171457022955318576713765158848297778216375966308427844519802940542050504805312535639850468071754036589740417259274547344751835041166865083865737266609936048911540188877669600082608640980912665632226392487924344920877633066879133930909032366775779628977242079618455227138167183404578481460271013299104426137357993235535500235990613919868675822970256435638349406180718060579938223957915654474432870390057300380049364580383107446291332447275931816676583239729207116846132178015976105993096958657776770951874351582502164097569266039161254143409808671423998689715804340950739459607914251725435136309073911194693017583976435367254234502224778415054772159201790375100818845783754858677955622913951159636254745014606619723654549769346867587802523328183003487356202990485326361805804000049819228011233280⟩, 0⟩,
  ⟨⟨599, 167, 4036080080985428925078024626352184469598749383404673647539788266254528239954911796066479775525681021195102058207545344726250758930261678978911552244093037184626087309968190138646653473218974825967895305586078686050850450632587041822839834302760994881351369781727054374527765309856939607219663511920782817960966901394859987113975819299937002223452996833399072096293330666743554017445232319325093759602297083629892408644123497182202320510621498074128634324699128058280700522674175197300254486101415609171978967917526132075877374630128124034673747725920113843518273747795953569798593660576739864513678479199875904174363398440893958470469206930227921729858140794421607733313912158995163320480234151143371395449719445844253286369477225471651736729847454426317778230048966395646913525606550694188326342933553083013717408065914280051967796329771675530481636601356078060983947380090490700586946823508815453390566599982709689712597517446354037029171416009323524928273438096961468239605121502005042382440944817703001718162096843350662253633550430321145726036533571694792302083222704693157055627634779050070136106142116020973100464067121743048577655052581323476011219472497982890539386511539893200003863372550412608727594494957367974816160894394624136060534846474653877357644566006242351392827815821821141280714409341699189069719690947779487834374989585810791349016682705765972596488983306847540577675482638088404992⟩, 0⟩,
  ⟨⟨598, 167, 4036080080985428981089887148293657579399855003878756091467400735950855810489777674150374697130963864761829349160034503584355681671244202717454438477620030297480863376358793448071937991530045350784756130085191450760173042940189205626158547981970520748713057548228451393884299159140768297638320226518773805528348071123966358315099512932542217692216069160725205705037628758197685734836504039626837517037672014928955785185115698303840743417722671115131841915495554722491349577844236168395524984445170936710633502320949681550942472621633286117286880073605843277295036661102328458361352256754203755474046490001314969828611170639522876992927389340947230219107268987228700203297596006100926251315595495119486690610195129087505080517909690278534407729647651400045099811103696257325114668650717797877111200800550361173020139042158976407457786041914342675308003032575455105079915329425546930110658212839557986607342624643036915112900367631712501304273769648475490690857879419980485503169546253495803462744474137311884617434172746252823405020616701429465654053689840714099785662492639760350585468542003136120452979813704176359369418278977847709198113942754050142348723444815297024339880529573969720399950937429072756175502325676511903749553610928784779789302667561433150860762433474204399397112980764984093145338699388833323663026191391388234230884878654430984651605117395799505978396911684734369854859084411539292160⟩, 0⟩,
  ⟨⟨597, 167, 8072160131899718023158985112418129348339446097944260439762030877104640850866946785843288141928145675166447081385703183686195066203301501430264302331856484904389070344415886842204482901018238495278682248567044829037458526279750185625349272928349096985708248288781298504756851514928994670836795332617916676939442186065839693011536602925605014121385288154708087478767904155646182097465247847973871276298192616517829165243669684151132189351136738273327669312102228936656846887478593077205561001703523411462931291409665034627167169507015022552446027980799691497415832775884995435642457561348108350915289455545015795329580648598834929977503675584558826769362640253956890233186646238078462315939808458978193941830963239206859778239751480076092536970583455492077097674420899301172950293764217750605605987159197691132853929877606514124362635846407702831673823213209678282837563369169654069831311009183994957506674460406474345225514391563542323678896738438732260445953581083138657047360095419174343691462873872937911799850026078312156913257822464755271333412717490885162212263719047349768016218081537363894130400595183938493563014116457125213558900848373025232595010807538888067348423654359117454410733313712864447017043528474102539558681014904262603256463414093533723168706825758885609342390798873550492179475767457378792456416473527695691221379499372687476489385873546634108289880087662919909791266531194957725696⟩, 0⟩]

private def suffix056 : List Row := entries056.map CEntry.row ++ suffix060

private theorem score056 : batchScore 2400 suffix056 = 26595469372 :=
  cJoin 2400 entries056 suffix060 4 928337899 25667131473
    (by decide +kernel) (by decide +kernel) rfl score060

private def entries052 : List CEntry := [
  ⟨⟨604, 165, 112023725461203843877785806154830502261713438798888259891912018111135308102529289734407116101546432118208450076447857175573828233995664369480387033859665259277597492487908532074532037839640331789973801809399201315740314897625304136138242218750220260760467442928429972270288499310422684497058496567562427157227543129366883988401035521835186924606540601682460040007020449670790728428057266170594436740245624226338453380096796593217119512388598955391433344878531200202177815695251719617424911038815686495351964716968726472919976406065175310687345572337260466321323759043678938644627712256268115318305894517433349208254816738570781188718316641329128068561986507552336274390430845608814727490282329706727548659579782981104415600524042764841024698166584219076614374670224793330817349914937247958438910998988402026673391957021281884979856234852628255591769943271075140002860567827688464091080213287132102701788110464665026043651597152738268754579111617586949816171631605767874032269500065808275412154159511951198327502613279397690404770710358470563408645288822915468812561138042905742560660016307720329177355319096254645952804489351341571139629419737121557470873616313213100078621217376037746802205483153304282499723108500885818160479756910852323972108844712291223622964439161327463757898947224399000369194206419934348256926002064820605730666909698999149946964559995154260262723910204951062380544⟩, 0⟩,
  ⟨⟨603, 165, 168035587565824423993327764974059433522202790702367626901145654213505699378540384937308089730750143085327513283641532251933084056392345301433761916092409247126083683876493537357056161572957033295348214145862279249623826285848798069956893350801923856207674019791518327259099149683239157732524325195175651411292599825245013097558542055050224303274594636357537601708358528194798970771126227538890939189593394130422512541578429012092014360434640664537286370411342023003394579142506335370551616362145421630673330276200398280316528017387354530128782248386689022781102237106524684968230510750884845612103236373302533254012182379573851469318228352385626787161916950269143663528975131176274467376485150401786889829757250110113221863426165480257353418002398545728729505190580370485850457442465395570484452640668228922899386261931400243009492379466300657886994036792374971271633983005959419366722221501862361402110406815542094367682719375554827870235923865612015941650567233368030812478979797526850735926578505092177981166858925329047764622559169756770017813421359848786023171231161680866775843995019351747160630420204667523775958749153409394455235547643456111104065830925852906042352130202988297758811751902704590504128029182044653247440974309386258264495329484204534723448764681616717654805594682671958905043889691232030245069639199529630972205661761695401164160535184249031345674945092985595887616⟩, 0⟩,
  ⟨⟨602, 166, 15035569969510395009405490563413712390061896665562954410778690922374289741468863846402307528216186081686494588990854809293619493056205338675861967766390781440755164561668937789381228191133352116582604666498404705995748468718649245271592355919134438030013627743149139492393502297726355615419500483532112309814372739235214937844828350892052270416313033842188086609277280650897125484395475142346882259755614248223701691678407826099931094185485337989335902241175259686545866001167556796096871950774067639429008985308657912971521904840077379679451549718654843870366288854587086488364305273558216902088466867031337895550887151316099247442680429385676137260494803927578302204971289760294527642202419745043430370308591809348639183999915201251724090047185561272757009144842460399882707371444194538308626544528478109272684584222992755086605642155449646065194140174545307089449176074979396967890669789570744788352876424879867546982837233012511658743923916424189340265222522330108489865162279148879299606453293578215087290755722875296759777126636024682223585496102440980437987758765003914274948251211785176266983345155783535060066758433675533059257104576672427297487482592687900194953078844913943136921388226172135976783647792611314487579141286973159445154082456893209879821905858303070104550980601897427570624373022401681510418348336373271355141356124513954433006122729269866110441357701302995823443334660096⟩, 0⟩,
  ⟨⟨601, 166, 30071139770985202035665661807278310666591210006351083963743483071451026762329134759332373209933465241910873760167036975034066485832872480266798697584758883571512660360216733548064201814838074777770996743814036882443244717405944587383556903010040469365793829269447177071790040259898603939642371859158216071244269635485668798772509611011119419593858483932687407415002648285683389430378086796285190257154562643424770432212378444915444989315009055631001724236660265750114545070219920851824649982716947950574519950118221705231235939603906360405505259322302294231577412309752878547370893955477369329534946293660237005646232904096588702440175713227062710050431084559576145954914918070079938821345068183108354975142333521775166893975721432727785638311002791257095885303878992746780689850933983253747066776528783647131253138604314480516701024851695467588258248327751013515632204123925574591470726878050729676803589313475111496530869294645805382119789027468450596025587346344219340154579675493483529352803956338952629287515771827039647447403329235575152398013858243483866963021587676887748343631161248383121288851957201616973604251740287364237302066487807505368290201072248964201859849492807052354111892010139377448511863411709830205454785733648881731743329847858372403587702885029247383172294833952118434783882466732165650892637323627556204903233699508415737008253753895052068344053418895011322879110283264⟩, 0⟩]

private def suffix052 : List Row := entries052.map CEntry.row ++ suffix056

private theorem score052 : batchScore 2396 suffix052 = 27520811859 :=
  cJoin 2396 entries052 suffix056 4 925342487 26595469372
    (by decide +kernel) (by decide +kernel) rfl score056

private def entries048 : List CEntry := [
  ⟨⟨608, 164, 417320896880862852113903441287877530788008734274217636558194686628040320252168920424800841044908134595965345516974622994605760376475196430739993091806867614050778064197177085582260461434753930795705682987650761290223652136628766282818726457148629613539551484492277316770171809726240121491094546483417330330886971708075980602905890901183995719668187137927316264874096244414043960986457143804678697085468832433488799449428502356961728455135431300604003168725198125811893611438774731853540386307646651939402971008895855138835199710906210337641484896975094886016298667177171751362967056039648698313892353030601982529755664497844921074659386251315545960425117639124765394761506029166733861779074325620226971192134505905590338894279022496264868691194827553571817656654045870953756826399531268805743679360960072645684215314322631740525256475669053818531378855851358005868493310032227630823181700534029702062881596267402128497538445757338756952874400641332156622178760680441834887654112169597040264758701762062137686282018584600599484496110169396226495232457101326986016939819992961157086129988715728894548050920364278269446401820879325240739840065371351614331613820981913924127081136018665126530989699598287276775976002661388991880942139994444651131382477445529127772530387339168111810730227239791565583920046122991997980686518008830581587361168965314443466361537338068549804017399889920⟩, 0⟩,
  ⟨⟨607, 164, 625981344155313163970886785440368330188851023846744101126287492041386038714964629346346785689676305268631948906772503723820201282109088995534296707312321452757241174950722063361529953430065309307251924580104856263930630322473210984316126331044944285329709124292365553873205278738984943930393366595609404229970474993130927901047401713872316609904454676031056373017813276279917628522948936408504892007365704858062396494046509649987101776579648995433838218055460348540918931713353931526718167596662768892105250604664826654294297385090099416108666964927675920935096630728045207893911946321705710077242233108974775006389235839451393733298640479583825326113773452414897377034683515870255910894215607148644684833699966518573871505599315370482917204484781002334913951926654456400591360249853569047888311201358679533274737899565385160515966552589856650177617564179810384985108159578678754591306708088099536441878982342874844427534966010648178843667986308483793404024046351969084109759587406479093277214481748966109520902361228794531642954984923643132122149181055030665365398310914812699584094640544347194624405655046294826732222905340314488453298431481543207837560398509479027167723596593702175785654255253999378367190584048410856607901015572593818594058205212400161634665165091124415750389539408182430475676289343082397144382852396628685593462602549777101343750506637131941389455086583808⟩, 0⟩,
  ⟨⟨606, 165, 56011862939262370767984697638610997871815707963081743641361846339978395325447693658649758880048272016095523208636851359441301282550845771124560500438879850807371885144314851478448075333500998098796717926663574828845455777469225570248609051910461515813063253761729323584974538033698946320229579421537101438868686142921313136410229974368556855227638136237761785832799219056742469669981954898247809674618114644852362089832336008674102518284028247023985355937018658614441225538285019340414421895099681201412292581057526511775046431246755621182945406856911109881471648071472284749702056732508099152480182206916984944652318586675867577348738887324492745918004817535059693778450279288962459602208896493112092607416585881884155067447540393277174611593880416659202809885472188055947012449926187852194421043100244561210955351728664253247697997236347658341601787706642207161899392429347906431590503862845103362230601238340232183311632280922090306935340379389413049128387777549027099502929998324686802192784000512704976010397774938233095510895686766275439516721385844783274142447450030098497963869009582755783258188319202063699594133749440861613347786599195153979721589761075370733373731205543766487797247120252226896064972693197963411829840096266202250891078172258221935580066640746511626042624506673472400410580486463874739760799861477126288286949523950563407476069735272106490041343668728199905280⟩, 0⟩,
  ⟨⟨605, 165, 56011862939262371545305440438589883170304104030284232544170685218915759086135942509265465931874770421664407731854797062092605775974255048996953122409093038490136331702379155595860310439399539644622029872583649650621587841872589608546142258854318451265400757136232059911266900053283372651867780635509178132185715713930539959507219806741115909645923736658439639356933074883515562098815376098006353293759102184198325527261508745396204053409025222229384003080023343850471611017695110296202187201079108152495609354267634302502299784354674677638194445957768228287609401944105261928554968259324746873599563095723600107727252311386072748317883849098268033585701193617471781825214610630753530161041902386960238899210794158275739353189995799630170864506993119335436584574663595246801933352672298347658857130020986124662750073464636446418922525655997687815772582009843390238372740484471116899947470960200238519101743954320172561419155841207830727051076462429452357672999226909662779174102666723817965378794069577478794139826789385409053187923805021237259023382101663383542351599024711880925810176437990536894503660831132883710852889261182049337152781395756051178005198798563129660532161271643484913804863883082851925461757022538378002686658023263071355807575983772009589167311562333388418135447078325135960005595660635365383577780485788480445718657529618427165939595788157157380737810391212642533376⟩, 0⟩]

private def suffix048 : List Row := entries048.map CEntry.row ++ suffix052

private theorem score048 : batchScore 2392 suffix048 = 28442572131 :=
  cJoin 2392 entries048 suffix052 4 921760272 27520811859
    (by decide +kernel) (by decide +kernel) rfl score052

private def entries044 : List CEntry := [
  ⟨⟨612, 163, 777320751487215161923891198915977834610129531069803170418930014537446242026980410984729706058923748942683362722570512150696386847431113765154996390277830848014025110351804304898984996334544830152971252116844415990540024213058490257756460389125956706366020673979182367962244781290727324609962479832865611630085495502293634813681964182473097392773404734051618370333406183873654896014499800858814565475074738387537887734418118010709206155392669158940935526210506860458823900063691793488290096471941346392527050535298978618595115383284834803073410621722751904028151789564222769954985449894612344332353089080147177840321434135107994533027149749109046309171003561358007117160201806008619674148243469728386521020202041216567230088397540304363873694199820902049695048055169973809877165876239608689353003141846811748077419808468192206296915979414062649758344028199059510080463002263202750487988130807305473491535912430281704376066773067300685420951297172053052072573898166355327515566457466610334127246851460083657721106732330899112811520580640350711568092586870101124109110717360407775267605898201054503204980324807328820266730992392607329290599029763377980065683950284366634639325852712533593467327022368120234705732411210411815062529519437160358044313521212293403808997130771634343522076467493728239928271543702373468353071272929512130567033836873897075541983351662221943898112⟩, 0⟩,
  ⟨⟨611, 163, 1554641491391448636063901763621354666113270043255160378247059756328320280529116239254349086961560112960085284723008819057402499691440183736129518802522104504693044209172444082213860286895705961479255433196888809773421531690647314440632018300167686297170547323315686509136009087350857931341152380159940431166935650633760327171370089317174754896133527678481397425358186867835054279732513299490673464464771286931169434658312917974560769493326755191417387523270362889687913933396043156829462219568507111682496517349894214895670136625622939409304680844019082601595455885461314115552440045123776781887814504627121163817744514623976124645529627354765454519637598768601345965297063719632813067172459982871677341636642172359622210363490444787119954551953589437559756662861433995530306754699707030423490858392441325960020547729674333305855490645936081778051199787625650863190114182430379201149389943522036780911988863578508556490987381891889607796063372387648138201199248246020210805655019050923511277392106715168364715181507215684959224258325744157658545170136225670317674818308806654007393272788596947668961176512968059051091563267419391995352658998159259278582895733586622799984296140214911130961574503150909931709202628695970954878891196998325917629048502688713500886265868551282715900950007779442838105318207776747857199739951928547999951829578550523489285154303564322023931904⟩, 0⟩,
  ⟨⟨610, 163, 2331962228399936720620419030786932744789313613797516007446831351655826261284059976693184969714219599364428599003761403306759837034017120180797748520035290275083157461262405548655609632449040487180816546367888009850031037576545385053240674194690083223631044403882904937062846973994655854385886845318866052734718284621943713544964749306772995423461611028572642746858705048155360812921763863986346496639815768309022862677215455016132841246170158339808074511174527485322223963938617278963663114375306261610985441542851064286707546397643877567755428735061827248476657570757363484863035717059034151803631123113872035524089552922849508522417900317077808784377274788847005147751312922520296130319104830106022181841216564435988255248711707359361076513067063923162747657631767465092236057842536506030958507865636959199970983985389343875261716103599771582329731152867636089941883307633616120512713994791069812922257379120688957400108921293231819913411970652522225097221563293500971004674800147343988084799308548746783606207402371574539437036975507155149435104068738811709928028463499287007705319872139107904549470867250378512200743975167139142410083514752693403410826309030070844991610085755659364970247247520473680373191514450395161486941968424863483000756462543723218296526277791443280673397932741632150542034913416556325179034119874388922390552887803054375967990297152871100055552⟩, 0⟩,
  ⟨⟨609, 164, 208660449606412543152665497506372155185087833650411293245611906199331177811774116293040797323834840716429075826871747518976012062633181557922717571740150752656539131525261468310967041694022784900400322806424190186177343008225987881382073539914468435635586492692810360488529818036673108219973555903682842363666315721948615017411870360575957694897378716966497383529206564185780679648800005931237353803348242412325798273964425429137946241063346880369676370497667712380155752310389405347569202070130251472759988291947568131039529649163285769378921998255178081182557704090039886307199408132493036212135968196936501522371731222550695453758501782061065239211245013855854121900425115491907840956120886236660893629910136284212177963238464247030092797789728730609079845421998343693989488471746159530638543650588951770717538987471719937799663176552347768605594698060881120343488477443001819648803726245101709821434398508035144885334216667805422312627813234414455636018849423834348031684704101257355734376393140250531560981204904736598157077282842015630112061855101539537612695040548018470613288192324472582109143306591975551451705983563372484761259496502222127269504876263264941633057868538995685390135141089368747647872323489618032914740061922106057281084868355927220364967158180594860887426329330530798770098826544969201761721546869363828537842201357869663260031117624062198369030993084416⟩, 0⟩]

private def suffix044 : List Row := entries044.map CEntry.row ++ suffix048

private theorem score044 : batchScore 2388 suffix044 = 29360755663 :=
  cJoin 2388 entries044 suffix048 4 918183532 28442572131
    (by decide +kernel) (by decide +kernel) rfl score048

private def entries040 : List CEntry := [
  ⟨⟨616, 162, 2895745443520954853120839799040688799862228642456753086664887705805311832989024640450519437629708156090710181423703818046562199986862808774005354243769285808306190957797719770047573044204819485880952814566080577570878098082685542217238967108842013518863669071422153231954311998289568849863790834239400395334549660423524330744527023735060222669240712106107079305302886632718497647049236640726297281160929792246401003973888498337561139699943369461948417912104833842608371845333608021221519099686242863963957464911282674732569600952694352312257826264061837995193081724688547988461918283999702067914947718046986538506981010611921808521525444598149840014386302723956410780364153452108341274911199672667131968465634324695936489900289263917217458001526163922170715956087321138527933429632461973407554713424330100111374001913373270014051866193312613303454825378203566062454431099789433971272157763342516486031023965992680394492778776450452721651377038701756828448813831981786395015184885921545886064946164237434152554794593756972602297951404761883147999825671585872970182767416145336181405955217694625572560460834243899652220096736304745023158592298018547439907398049434627069934911482653814668131423877558344941303388892619591036082526368115236255801547777371619139235125890768436199042476728452643950895693971701704091678919904135815753067954716146647669782194281250816⟩, 0⟩,
  ⟨⟨615, 162, 5791490865466924891113868965288082756524046829174766647213842179018823075337148418947250293944938840887078825339834474566091558583825970126429406285135506368690850289717716808482592280613869466047443995607365652795574403023238314231041888460106464998233453489715438721615446784966143993380092793786495493432256239165456613810680922033270247659674773422320587685833019914946596591021469953502029009029462805902490858517135527212577670614850429987144069758275757458572805455975519778446669495239222712717941114369673593288907811148773005249573392578589678246671440234263560891935556788143021802585582231935360141252386774600711525989399547791081039312324060489498220595019542573875486676582092649118898402205437596590855847324798087430933736220800179310085603920001114730789351583999375824585798842488480297868299874898908058868333361308012372387039914750963987082803176598938760433479786933989759886919542924910695172657819255733020185630803839648532101477929964800291798055299820512391967911658686146433041080191774362308768114976706348345412209156621062061438710527688607923204714284094275598822637245982631874828552581000416558395445007330942398736744419587116350130652860456331290420495163104029813693927211618655086137738390620404848639400105156045239659870357110620899390232187156091438648428667747797065158864862887537375256126922243982914917725425566220288⟩, 0⟩,
  ⟨⟨614, 162, 8687236265837910475657951201449829134305244735619112876977114424145526831929695473576796628379874460732400899648127153338253454458021809929867084011827514000120847511436956480700560165737274383280396358454689912708271836184653766137432983216528418831249696078938359792748287162830535867030686916706724912534277535563083770545725361049043075771575942945355258320819420385093779076220845364438084723715051483601023947417975457768556126988685597781673061985256161628711753682115985935134868761673714988748380019865436377977861678660460856506284984603456443843159893041350822050132739847751263546588615842416687162847175869416430119885610052028849752387623175227652110414929997493217020470131893899503485336070519259544659322275215923325966349045434315160009498753441720791672282708551059598991622521159167280486293510479482079675184917843455202958258635508939038077148098029638487317233774976816079741347355389291237089550586412076921463769177865456937761672557352960317581079438948660448638552831627446973441416006679986910804814549506431971388199731821198024107226888491747731173123618354605233962820695977192047612825525154786245876532598983147067432088424160884771828196694132358332202355926234598807693055489248974375354277781872475633157498831467576047323732091401538407597502836905418052240029760526101824128959693096485212828499885769194167015704091435204608⟩, 0⟩,
  ⟨⟨613, 163, 777320748591469750765413327367611665994147462409060484486181906993140723969411188513236583564451232188023999234394880711880599957070505800001976321451644541640378443307852366884303998061114789036539745129877549257378041256811096047071988511679451136674779601089664887516785502420676255977826921449673500659048404933267233613145424575127063404995061083293553053541458373275930683350244617423623341690192655295028030825163358129452096137181769517704289575448060559130014780084944784459594331302358847075270468248681323828219309189527173246789886146791391720473355708420604020821478538823880552396742866024580433034787009796720548556610120943208702306596957858540848479739493688110669158858492472363720629869205066510417463331761811833867973262554291591565910997215085155253402034123328866338942760439275988923853915611085264088770773255082150502015861514333658547816926809446968492621968978490381817388121562923739075475874789930745288399534253900586664204762016436188336884036695139459866854543618562184282950454057035648599252235523866828257366936602472148949101275568091930143393943760419847228466493418756601816916292518809048819540229263157981848930881944748548817454245891315282057317845215095220931381769881953112103108468968063070399010578122864021234439818917953793650162315752320559885099460480311365940310374002821185393800205848424595552116322019586159973236736⟩, 0⟩]

private def suffix040 : List Row := entries040.map CEntry.row ++ suffix044

private theorem score040 : batchScore 2384 suffix040 = 30275227599 :=
  cJoin 2384 entries040 suffix044 4 914471936 29360755663
    (by decide +kernel) (by decide +kernel) rfl score044

private def entries036 : List CEntry := [
  ⟨⟨620, 161, 10787492407563905466103178589881867815910391517190420946989164271883353595901810902297165755742858641974879486047296249682800328110611571683866023570461270458741762328247761459461204516548175936946721676609089431906396911730595637697841364377190172353625188193703030527071347346513801310986034492676128346910637819716589614383257376099421606973255639006040231300761848686662682154817177620280640998828064013910730568237797042063724025891228501722415926605970108471091309114493821203724430677820142338229882817492726834619761850378065312408014158416318050693458312076456990452582109366055381525310403980529208421953511038482726747429302507249510695436114022131534984239515396285209068620860087836246676781160062207193585272459130719897597263529193637351656087851535299354965662805417809428214630573312208841869360110351427677230280871741222486176505888924446386860605986580208797633327834223377539022579465035359346258766019830416467223169843469280182670639122059345810895531389499564126798680521577852000202067003296756162621455798956981144579328274426744622180067032189015428035290874717684756973168631401613241880414350777276853725018019654369455595265642041669279656438264410291555936195062851880253688254767507366151441874130868178196853584348382776279709335984857472574107424961910250512296111996260112037738553854345335349105202810455432059978514432⟩, 0⟩,
  ⟨⟨619, 161, 21574984694568189398557414838461692462602856335252391419237746193550134819598887196595834989293769888516045713187184307638153499022838285707660277858081123927418579049677062148518991371142744073594303223388558208359685433847080731967767440288383783005641542080165662240854103712444315443258932188372893908619678230593142180119515489363383106833623539456366149304931482533261071062923001587245420261209637113232118416677661627928807360010308442150050838977383758489734681595201143043267031491240331680851515186999917756336824364445251058734701143906774147944009233031641906432059391158602618287219054484819174629966708885026910049424158025498326425502291263666554123561600506712819994520858916752018604686605984508801517617706066107514634223771767028673087142860865002630795047459522077347532560978722439745482477232073568011958584095033845472823583425625442231521386244297485011447450442336343889522852329358874795064134595516077943561237929170584716957019949649235708907078892937951424860655004958885449704902530567977971826991741597793425159025888455533893954211076614659525761974576764146957803800482573199259714139856475555761171221212573618936270394471278039129250334720822108651883863511969524428469040679213077311181627116115024635467774839947425873290874449331214240769217602434087581542559345757579132869171151474595344962715140589339770932428800⟩, 0⟩,
  ⟨⟨618, 161, 21574984734754729760067199085248033044971984329542121507758260460527864716228232842585217102272893507024651124328866104124432077471167431496128699074447957273954938844996409517312294003261349693359392057758876483175748848727005644540977132952085428774715503245808902496923410810145189604180663290375005133438245790417433301120896768586592316722568493272576198451038932302657526635758795168512353182655842648849759180540984209275926357653860864574012494382259779254897302624280546267442643263437301587608710700119463769693456342681734019367471470769745272437954235461897210391116305893268313660719170981262439461833654167954956050851753307032737057605049645280177513174219833508731562780425755812151442041291537195503449325335972763286809754969272938318631168814179296113427311181078395502885645535345881744221863579109801680404153814205889266642824370882496636275718641199755123790164717934014289009997896681518283577401290023800415174195298202624233162583851230302719532168226943281605347596032713667196973582916198008097858359890136279703922767845714728360482848424949420462133311147563973446490611318590710847311516222129761762168312518416964861634359344848798973996615337779609180091600756023868025921513080657063380741855005856538994903392654447655747163086095564188599382673463531785197294826049193956602100552055375069133698344608337690431699550208⟩, 0⟩,
  ⟨⟨617, 161, 32362476981572473331011649971640963607673521389121365458222571347790073933619308370789235571728798915922227165959958408695567290522110303317760928798061979268947785451526600615445187330587474751639525607424441728094232368814548979597733786719461132596988366632167158170285069732257834869167393058109345045967368712669846647100679255955864283520839790379765472394002097554773617878641953250327313875168204450133172326844068098003554396899631815488690448021424307118563899997885092715378935731408610652931461827751042033376564932251213912206351001653669773447577435096129001565471953155680131458134647012014641008708072691181937939916212032352726130738559420980563168758292005408972600640852437366996937590632295477195625583836402312697402200101651988696653459098849485320231287977633928840593825452836390952617253733608433241845553764435838542516931320767272355133169934065774155244038294166813429060068863667467826498677692060763694874644212764290777653264224777994652736758583508047299386368559814986676167589324124073816958304676897716933490753417497545160279440345565323982414549558255355801292560823233131884081176848820944590439445129279973619159135708309126321123756501817980960938012098777225469509803984436745641146531702919817664851091849766725378616032881311439072041072096557168665686118456589541194500123711634413999619442432449667632463872000⟩, 0⟩]

private def suffix036 : List Row := entries036.map CEntry.row ++ suffix040

private theorem score036 : batchScore 2380 suffix036 = 31185892671 :=
  cJoin 2380 entries036 suffix040 4 910665072 30275227599
    (by decide +kernel) (by decide +kernel) rfl score040

private def entries032 : List CEntry := [
  ⟨⟨624, 159, 449119588485542474153275045849496910500901775620042748177469050524285172757556058381166296801430639556432844878065018596168489548223511209319125082666906215710181236707628092731384933358196155720773610448495340340892881767357841811130172191542732705918863337810122117419897797944761289695541233696370095068331434840353519893140936005468820886649028764791157217799988060356952445200796515794223838431078028308949246933465263225661233263830807758616646316223098033475954756631113191517081304195088351216938741618450115087023771240341796340555621147853471896117104063833717306104129438885974980003674062072004144753892068439756972828048747642008046295018502476297211963608077029648173163993089665367286538577499606074358057388226579114458784806692009874287204523122622282098449917713386573329266110366763095037804783059201574227757717643193235117946406624606579611559443966829929408457215865912485432203513966524628927582202577478397116464570410421419400697179770870334245928669484743373684198919705243473269055630182090691822613698467489471589940711941159506205287791177392571567466122911900953861064166227401810462111609174680018356772131435236872797160898886706180284913954254050429829914666490115600312192614599023524050730542215338078649666105122556275690473640418429131456300440326917495816146924517257299808411375974504353609679896576⟩, 0⟩,
  ⟨⟨623, 160, 40186540810629373847729370314861407907123089822920014945059663929609341493593559835069958045417316347741180215209728352450354167653393183413283718071182970426697382736410353239048027765207871093559832673049503007715312859558409729478938460449070957742006319368341773848677481360197840259210949462238483822739208830415405196613740934462766696582645758770289883813604052820393103825015024612411168920239898643720832434618479301605154617305460346679912881142310409106966346697868177671784194708377818138343428235644937863137568067105492431703672669621019438988663532694673288679168903296639732427803448810413423954027558764716275590144785888562363970255351816760375064082933214486579706510620740789587496962260693115651444646093285539435872270530225395759218355286297378197500041096466006623379139990050864366390030965371454868605529524568821890139269958535034848307261823774419509396343755001633431559876693153150451300252149399395632194476981812251455222351401136573831335347575036892571502478487040746015453661227613740821469860738677177332662864198748776722365940486808750655677512388753578071964203809352152638257751199225958304549112674704996494838618000427938891591193259773297082696711016830752795229614903357329196756760162150572506477609048613470125398663275225408478841736488147300657739722796274754626429363752086324393645668403460964352⟩, 0⟩,
  ⟨⟨622, 160, 80373081321845686474295968955262641726989364792870888065859954749444317219415168491177346855968230293022332725562184649869721921136936442052661887653481295272766679305608661280089450104881193360847302536091344947124010468781515821514903535715299006266330238131433715738547519338490255614889434966955719330916147015913983867358184404739699164669067068149866986900991268676485159897033086126665961674064087653425128228012114495955492174906148264776761021136867814512732326201181547935660356145254723384318852975580753239490654067281160386333171619567638397726102415434125124147058288747048776065216751935804278932359319280421091161176205526569904844714823055653420905861923120691965298337573739482708971320542784854232652412246495627123161129694281641568834554756443605026501078135379553359014670512177021492821589425277780718612578132965257052735931122198550775860418310548558563424520819761911824557711485353557107551044809330094018000076994762862335205916539967778547096473888768110603848945374703317579400488035033495236815589522549495001351642037177783347175358836185742571448552600640248727397292563473657881906325405962208349315782263460979681758111755441440605750487186460413484380870953444293413342165738937590950573491732047029589734564372552988235179329377016894206943920501006254650764374916364743259738810465076829991061742978481520640⟩, 0⟩,
  ⟨⟨621, 160, 120559621533648942899002320958826555340265906041395850236923526279463431575412972107341722355076586169658771347636504930021148696811819771705185988683699443992381576832253426988247337971711303551419718883201541613618299422570259245810389326044159958185165938389924333439594542330443261059132813602554190994526126305672674993508611654543829257770639943700670570458292469250648458970753241586453002184181039519188508176604143925755988851383357336464661053435853937823192018966181642383996343464916250832732821464171728952964024233624831580305777002683120199522707752511225972285346910189851641790718660609632412373172492207446413708094917337900815742545321845479528947553576184956104004051099554950711356481354232650653773610902063127688824948248090942224799062192636201427058742414508569013451865650920658222389310855883647231701715862368468722930503502630038284064197743525093330000923353119426411593763701999040842940948083199878773925223633822927104093391688912086219846141288070009273501572923087309561298830180877359562616278825656656960203093350546577323165290432385621738394096491756558923066477418078033157104689980416944675738131778980307243102790068388734906423136381004988815054717389142343721361859755942223446718642502383230631290721168396702361601994643028035640464327275294600820746683238708487013662511231737668973674189779502104576⟩, 0⟩]

private def suffix032 : List Row := entries032.map CEntry.row ++ suffix036

private theorem score032 : batchScore 2376 suffix032 = 32092553355 :=
  cJoin 2376 entries032 suffix036 4 906660684 31185892671
    (by decide +kernel) (by decide +kernel) rfl score036

private def entries028 : List CEntry := [
  ⟨⟨628, 158, 1673100845834398538156150295625281756165896124863232827763619512954420017983778967535592594631072818821733196952544876279840777952756742097376071482887805209256724515392738005835579165837784494921962855747253951884023709883171067438079911806714812501389886033643755414000252999610579783558536404082802297458749126989724119858388789222162103082207443210922952202866775484200130083843510369913304862934113942288677305708664271021729520250522322902773409855925669540027357119994595034292067984389460100285023283450361893483883547712625734002674699737273331692779480649430755628390554125883987594404970184284278622358261274222257228315840668742873779444804947501245366520462216442639140169296434334355786292446511668702205439922653230438674661290093735596354705499241078704566863765427089941163016729565391486404643487609408026835580912611148144705677784833673971042468861896224926119968034076669862111149695086681838079623187652290754603899086117582874341399415822666788654380038595975633659593382381180010144870372269489576631241251529124810598954789670789449122304480161596554358423633590110231462716711406437676963456030315222263090487317222714545615304450079392261380373057080781782391609872375659785317031860909396504776261430957569416145891350870359037073985848359245962470878050352047222189157438291224527904864924635282538496⟩, 0⟩,
  ⟨⟨627, 159, 149706530610581387914825575520294856301068327500040936372628944061624761710134088278056117954588311976786336857032105779300071071747945612068252450282385649982530655966906417594120272875357446595843511653709003431623837408208905944382802931152405392473034509036558174819752351094695305312810498879568934448003441334870051835627642303273736367824959530641500188188901063116610974382342602020283691818911107466797698697828907663151973142213937231636844991920444003684034551828560319527016731973474952079673719253208818498880978118188193879858358057195743535628846997734865199554063846713415139009223723363866552775676809498917393948249603307478995136176723760497429902223849376722131770429808921803603750598716706402829746559306218680687673062567346350404405662735510202664459105097573691795018162828566302285925040584687095493879209283551478599609778067925238393932677466262626705952913119348074649275207399364053331017881047412192748831395701607999710555280144128327804614277262272095479852613553622795932116967500263174073017291535040776672645160073237097184073832349629979680541074574162378790986461840359482573758774088078262641077002432571734682062729293117806664471885787755117872789369791687197405418112626609702062888076531048654583993866673089500972527002562129586481818119245029068831594700704376051397257807475557362830149681152⟩, 0⟩,
  ⟨⟨626, 159, 299413059548061929995252589665501070406756438869351571299028082818858836122654301966123226302920430469635326569566853506783453301221238092936522877144743080218792509772962804734832920134491655527863330673042872983061112386468997309024420204074440035625362188135598103978779177297160108019600093286172772810650496677115820859864790081647915750072754561801134837964383354414284192793137306696632662664878630816246025774199840787865836848862725536272126248281444597389378736417448670012668294677502999155822790607790203003827305517917297374046823364046308042318659789310131620561070731829038866377483338198154092485001604224074808777225558694289936381259487073959984778824261736099371602355641021743166796476353341762592179085491840328371996444293034118409123581891246974876172509985355901425450503155257945765377548687703061764165456996613667301384420549749435077538529809684375865646665716886685996504144777676176504633381691165018393200462931364137901023477763318492883641301036912483517355524762157651687398128699045995690047674524498088693260955307505058789373060154864411426477778429674859175000181732210912692498915865929872863091322076148506695477779051856764598291093870671077563168005792881475623292289737840085595640335860286635244762517096407751124334258444816855051998899851336316406267355593671439172031224751001249771304255488⟩, 0⟩,
  ⟨⟨625, 159, 449119588485542472075679603810707313344873137926294841754896664170412091819245264334014513921277918553571296288209054358382331885286275507811659464728775155313878752641403926236733823865942588835800894793824976541410842756718166346795926646529717101436978120533541412917345195104949206222173131407511684785337732364559517942861681196245636678400943298298154899680183015401956851506230155751168622777601944980856091848506342984758803395172889045192356195789692511260729625162301286832568953407400640875059207816197144257023305950504565909965081886611703684609242058141606290692289214074284379006161804449207126747586228004516214594552863593446470028480034172771681949296237934372422805613425891118346497633102864548049098758378997473750599074761429704253109047519586421904658531857355026348219041806232718686580313108312981089976501126387426411260603412306051572339415168327923747071149283361797447806187502962059883143802143031244175740486980344312872575054099838593713422048315134680257384983732633375089117032024203134474634526860813587417163775877188868268063790427965967629988735875612314553663801357056112945831641393016591068311863908613882313387523785298456976081251034384944841834772769800454415472057829078491889248634713825034666607408252535438537947039154769524638923004155360163445346826895830004732724612092606948216701714432⟩, 0⟩]

private def suffix028 : List Row := entries028.map CEntry.row ++ suffix032

private theorem score028 : batchScore 2372 suffix028 = 32994943172 :=
  cJoin 2372 entries028 suffix032 4 902389817 32092553355
    (by decide +kernel) (by decide +kernel) rfl score032

private def entries024 : List CEntry := [
  ⟨⟨632, 157, 6232786349335307397530042736326462612174064386126521333171499941328165425847369412099198608974119897218769907446104449588485551255964172322460613971593761686914860084422033401648100404413449310480628567683395709672676579626421675161860774025756199574574136480625704911303535886769021432726066974503021467087757414747943251771364698810223551992219693355692520823101853929000348782067962253814040415544129963851316005618276284544256110022531383017070899166237291294466701152863795302686749940144247236827584783145663222175344155546627332555021022663991948841974445225899700140411228946440545247292161364755847287001231867451635230015940599259612178372497230920904032896264416654547724424657018829267800773508609462224319204479365689288286337006327978590818772819090953386569709432066128503270618625062828733399991540595309922933163866045433140717590485090300806995434250177142502973181584629694491645281447492347483962508603141001769620713410032411179600438222560431887677732153756668786163492297165040207716396985410482025233550290254132072081263446414708590297612817302771658929411966144164254192121265902395688954348381091053560156294179424088905176600709387208700751372318358195959878896459672966335210384395653422649972568631610845652498230840420639875461084182562018167152958322192833985101150340686911131938461843456⟩, 0⟩,
  ⟨⟨631, 158, 557700286099990412275588363561789040469884683380671165004250798542586494571964327035058038958181596242501829732278027718416495395382583559263591530501251801404996889358496779658898215203647737668146322394999549583375201159831378540050018786066284088242202098359022674428407065312522107522652055868804271273960656013894482280221139373241327530651017047486497316298350197321524428733048317050652325141427596460326239643095269071527287026831350796517665268489972829592476762067232355021223788869824952800091126675104647203556514272728418306429792884977102754383926789672796106063332462364288604838446975287250386127473680584485107036176518839823915764234209249384859313378962129701974438043685658878738529740668285308286692588168547577555905214009045715480142420885270591878696562041731496773068045435786632589795513401354758177661896588396134614430340226814329424086544656085708154528695357587980554202978550356169848351429619853937798109220879080214235975524732047802679462128443586044012415911468096170069558506125342604615194223611593509672203206720008295015815350169749978210627171780071614611763457395964000779632460077766161814233138266753412338090867381134855044565140575445480824295783442478190396656715616612653725657658111246511275690254407267326095848424790948308076577709674454077317091990819629583888074516914218467328⟩, 0⟩,
  ⟨⟨630, 158, 557700286099990420015234536750012512378988279986219308533869707042985073542018787181870556095649187859974021833647144737976198603175408595720018173409243502241199782067749069465305250318018113054991308366423911559562158719779573609510534713832870501018763413344235929736423596706396318015287486492882767841944894801224825770802944517728268007113192846723766190798941253545159771398285813936546301675526861553030342924990523961640796064000363428170933112268200111824895143530084798955298990134903018425429859179680492119116943835782238305929764933853106742450686587735271854682111675086164442120809477248502821921308808375789400235953214652482393401653413547876627784506966388116132357237799997049281820885692842345952413166193842890939238393303762760512535411597290424149759100779675671551995891717418951568632785843042098241674373756258870978079675275965229204965413167080561389328113983202101624612200104179546894947609708503702493234889445571506599592320844237929913868331876719448290872484237299311352923893025617859869675166796658727249704838860947254325028160121400106597719705799359357071624578656617043691628362122157026275204676150050027992909369756136334481377361364778719843209592086250485846423133578577321710323258433688734550546319550923891974285309626010997531735083448002128453827897457606170256077868844906971136⟩, 0⟩,
  ⟨⟨629, 158, 1115400568044789909515012840058626488279188770825640753895646100488707702916501680756274734406921920929244461750426196248588444086781940629180846608812811772037480441488575284571103248055806608241659374171230525262299571997736067095959071822576500008593756137645815414684951063215803813329059527662126820932283803477155533828682940519521869737954482864520468650661378354983651667793091580550933670912279574502294155413330072478182582107404111411852925419995707573743923751128900665763697089868020544343651665547165183631942911782580711316786276143265905990328470853879374935682294256236354549111606914776206193749422038235725052220042718900498965770943733982996580686194796188372888998669493457055601700103271438493852353069484907140021816080949523598297432216167697278546038750407307033322343043252353637314695674811169667199010225073708980347982784322756161553497855246404514995863793219893837034349827306808095664805937698943882419310822203174355717720236486399055401373353420685037333106912090955976304275856641731327402270646700594725972212047486107841690853385935951723017840672817164279078003722353943490098549592706906032007612307579958069659842026262127744664206623079297980830975335893608649162807624565888909612978583319216232348169415170064298534845461210795261140193926171649819301013650547672532169959540159898714112⟩, 0⟩]

private def suffix024 : List Row := entries024.map CEntry.row ++ suffix028

private theorem score024 : batchScore 2368 suffix024 = 33893084869 :=
  cJoin 2368 entries024 suffix028 4 898141697 32994943172
    (by decide +kernel) (by decide +kernel) rfl score028

private def entries020 : List CEntry := [
  ⟨⟨636, 156, 15479292404041304763648479459728725231004569803327601232147117865211152117767935684706156865740112392112199495400673768699494360142748331119490350886177869663303047267894608747155824587596173391036435974529648074203638847770417516922132027420899770015648790231208913439888129894741393617284712774861555246883780303336757445525529874084183892991166305114940175148724189520003821428521421629354400166845768700057753593673998531699384867136492098704148697182611727189791512313819032924355001866792565766915980709745974287057181468329324317342298027734136131460365179517071926321095404594727346225832586788596898708610897997256740624288279039701981258205323307470478509886603839824604757714408465722464122161888911519832735307691599795053129561882417564558196990665588530585058042634811699134551794938334283280669498529382530375606534235701977896563167591510189979653025394758670355836821495556048297986360415227392697078544083710790507106527023708613107694445167834734339250001435077077162276544544637892292474571538590231923822615173349160248056861252432500606621803058656806076423738265793785358095816976835212936944619773029350317628646962105901540354211110604431954414174398962549770840495132606088610904408089320813077524539114490501907520775253372219642054549591550660017398067989306168709819089199563255316480⟩, 0⟩,
  ⟨⟨635, 156, 23218938519564671060182313383841747835926956969231898404105695889984571786931452707176330564882706908841769399026797913282394486626424393786195324226690209585309919108778258623953844707028373931470188960780949123056744931049611443062768886375879199757928683901757170699721814891736694184915929008331125523993457650425340733757194986791894595417445201041199389081816862567662980993205662231333169694362808043664971925777399339857340107194769733842960826519091461337901920439668958405951998728868632325206308206957790971565853597387484982132121452723635503464701230544617073206193944143070672660296644331602932900350497614651691291748127593101370816800825362530787574867561781853367241286896611889105779658263727124475512203070310093766504248367144282295823078974906564381569011848357566382019156405328898445527833843908266449137448693362632804392400265123951015062396524338210826966047114031425128374939077535070385307569871914807353979183578159365704706800538343881317956027954587328727843755555475963806092329070724667252198619604472497686621315998886723886519106509003328320954693800349456191275030891800138985525856659982860513373538666042017494133524793441440454980550480155869427209566805121932783030803093684294244885462171526085599587429681215537971276739759585492894959137524135348389083274454780816130048⟩, 0⟩,
  ⟨⟨634, 157, 2077595465257728174385557088069663960374226350513101028746571414966412439716042369654893881762037665617750344889207943634012899109930210314276532157875937163651137337058071945064574904713901734513000617563062413455666884823182594919122561360589375077665218127402533836075557561076062429567752281061392042171799654813644588463757452234393504458555728603976686931086880985977318662268168243580180147928800092000312055653297858661738501593421828784108376614276337599509618052797861077983514263612967813544139595629418529489414410392863990033044667042364689862424583548560331109017358726764449356981839418560202313025514962931364694434928450229274096255723395634439405129285513672876154358810055319683917934472857295162778069899237949563448932556658656174295452326889877451233874630583391840345593231190587636971215761262188248253640147163317147582836622961196488898663034794887424959881267972453281819419922730106791139660690239347315889050343928594543342188535898032995913248339889919015837101782901376024574016352369831433561841658845838237835300148351122053141960790451286311081797422401652787625157232538426873020208848753341656423158316539877152929145972818237157363674467822818965758639685202175807204603342755701461601229537157125244103621409720843356844657807924153440219169188990958594427194221072368913811945553920⟩, 0⟩,
  ⟨⟨633, 157, 4155190907296517771541585618354246568379084723130212959147175662722205800633905265846124869062767323061809218245447097683533189530855183686692356725199928837142878223312288353277699511378019191743009824203221122834168691266470941853127663582700721755673618554745665259489416985540816405164490584031858930572026281579918892117900031205586863841244196251357128474536950314330774226043783006633466769373688126768572715810584208621083777186322136435606919965775192686304525059508348898680870697016247869777761428515210747460310735672525061728322663314800938560172773985314895001829239984057706974975331283676705237498565305973221923326787102905433710507619246643500246983581269031151960329537240767065699320225936036475757762822475096107139358154918075307375720032999495297907748524482655034406110275670228845227777697295902085438304940212842816518365060361768841929036750377985592616963513463784191034137165651924885640340803231235303539200252761764846086700599068662785493998093772325849943200170632114318880631560598512761801345400439446760860765449694674607400137668647622199117258158353096374412271085638338761619309063292269794299301648953811028633334597008003826656995435559035566553810357194124364510416215250689556418034253891517847023346824736131860411576258487572725431713518783505899436000575322360703124192100352⟩, 0⟩]

private def suffix020 : List Row := entries020.map CEntry.row ++ suffix024

private theorem score020 : batchScore 2364 suffix020 = 34786687084 :=
  cJoin 2364 entries020 suffix024 4 893602215 33893084869
    (by decide +kernel) (by decide +kernel) rfl score024

private def entries016 : List CEntry := [
  ⟨⟨640, 155, 57664857819830271466256974114957173284160212615146646606652376976087876697281867447598235348266731290185029979525692259599230942809955113378658391005905646486094481405368409854922414877919028981292139989624053322072166395404428958375837488703425440851696819041110269242464174503993525462556474135450440607222392865358443268476549989502003238004410667753292739450822075002993206883100518736582990604570382154549137089481880665991887089232260784147610500914293563947858527247746417867388810068713309338445789448491141894543417049705345328868467848972470686207590930811688345488245793288852069440222684170938304371089698218398210458898074414748887777276657932577197711795955359832130097982038877203450841331646209056673679454728095823430371007711342867601250533388186918130510464779546961167888429855494517076136911728977800645515242317215549408321251347093268786415592998948006603980801440831607384269864741006932105839780861832500575587724479665849641649511763016546807981017720804251098583077222537232696221931107447712526341870925342686346525974939946526587220730028618150641032149018249343929175765486818325046622285409135721153789094264872544682705135640383136176793563719015137699337524553783932539116305006577093751286749875082642900264530800482854454393975663432506993916886371207521325443065053184⟩, 0⟩,
  ⟨⟨639, 155, 86497286407517906502568399100906207546319631547883673610858933663128120609244883944244344911230214195934777702352908712431022609456512555448923412365538366904300361443253450400404930337359262072513940262699579232151211588919571470771851723704451425292135342557188550251294987907938214176746069207727863090549364419029702998756161403409509666987533375185825513237892739946470050683477189536269872077564004492499709660390576654528530032741736955153058885372469796412214622607196542450675209600387275268675745204692722082902227110894616349899696519289433714693170405108744626534850418378759851340504123509700761902593348034414275991225543758407770367482021906549757526591872152140539138906816327468957359121174744969829893394105225902588115076020448296761841389801901156942643494833851704268475765869385505743391057291506099063221219577649359352757392581707377814054731936383701508503138026998752269222847513586623012247364142092099245839335711348093348545887517491485731439275542679934260348151388603523589994267000774539020453959737774446070123736678489052803255237065063407889440154803148759031256836111561722920428851740902524149558995445503465682885162147581783537318926898848491019605047691808481637678964598977208609933895880508591377673718800093090529116843266373917305404820457186002467028841005056⟩, 0⟩,
  ⟨⟨638, 156, 7739646230853081291739375462992848182379244706139853130003752858836842045852704261508476210026674594368048944629773607229113122010535690356016763378095575950741342135947628192991101369029311999766655537499309151085486165589318870279601014042056977818479029088386863279475338895775162809106827730138535093152345187879339605833260283541084257134333561865147301817641437825674777110734627703198109438022257398617435643581636138690567677611881002730277896159178433118586383435208705574296626907625578361873640752202101877065896181689366977983810144467726888141832162862542791870909810970849572593657557906631258878346683675003352937068796634342205866801063946940607343772023601787597506148024467379668610708381727256343003156653393627804537707078336379477092672779037034966936779080913104265932646964753927984224032298635226577708506132717828545438755537819920614245300413122651266788031816096333063816562796488530697133862575469435914066573743443429551435993136804578095558758054207047425232762756910557139193387704551359169161653611141241839433664512471351851962400523960159276769063900471402802226179284962617391497536328631271948801096222044492600273680912042033205552438693239062577039421944819930545707448455645328839978606626548668055188781570118813367305441974469805938325480817509441745935375789885461889024⟩, 0⟩,
  ⟨⟨637, 156, 15479292375208876175960844823547623187744739932363054605177412144005212522859787182315530322764203090284991665652646195548038738225404016175222052388684379084754344129199150793599099496790616672964955419140060755689946569053215254827525471430242232535091227767115923117893986534440843687197580252560554905826498457349049492929536499913330215573525113341799613565759072034773002270812892654662275079915555414895200591415429810147196799618210705620025743940747892978187841764082127008516736346668547061721766382472687262826073192605263280623389246972535645327586518019347899706081338512780462113200662447492047674495105776329388112307846352844768901253247776067126565277656455242711761214399499508452669794150964577552338015049133518830416776246055693599571320755945735755549070831841671326756104189866360893934841850333366288178737873338766404074424184365678194080188830531887141843558875217439588758887970391994276384483428918398859792570714174342462585781307657713159551857363335670495547597634796044729738059331478423703586826682751319333048622378871782373850084135217772455721976984075698840411464051704339400645956525204083405551335575653494921770604642188625695486349189395082283322100779272602632302364338775073499358129607065875066670473058141181443763694728718647806657992772705235422967350820208950378496⟩, 0⟩]

private def suffix016 : List Row := entries016.map CEntry.row ++ suffix020

private theorem score016 : batchScore 2360 suffix016 = 35675637416 :=
  cJoin 2360 entries016 suffix020 4 888950332 34786687084
    (by decide +kernel) (by decide +kernel) rfl score020

private def entries012 : List CEntry := [
  ⟨⟨644, 154, 214818334998269025115103581285264422281243989092990550468362754232793296331845290514709903564334002672086329288482424830104130736571755104762060360898505091073101400967621838109847013868173153325023998621689641185235029974199567163908993459632435926014285213025724715167984013815111745049203082335341098735640826654403556134154226773127673012575048292099205311119039564554594688543976629607008171647700642147536505010645152867547685727332165363037327740359063997972834210795197395521986133812122007069556227556510587934498177391617219725964153067062968980310765400184357400049758251007179551123005117380738541665000408873601535585075517955629282566655978766833564298329029748316679492839223951022645519182414494065763075797270633906751364475453949453833972185794916157394501980109103697443229737249258448720081851914034544628404787884416342870100168409317283172869196270189506166204383404983591582738597990603250573409354398285975347680861614994360300519560443774202691821445863787801086451429369235856891821264202998916023993016833896115868753070737265850445633373932226665228888569103631085030844516426729184575206128020065245905256879869528866191750255924421091768363693337063871296071223694670413744383114202195992624884707395184398089221865088508715637847846880844773311684662217777224876032⟩, 0⟩,
  ⟨⟨643, 154, 322227501897208044315011795986094353893099842771454429666917523976892682199347331912235710439198517039175248527351426752027208353609385674784924753076871929045958314010871239001531452866762057376685176148691666516797789492953500254842925666619058749106341592621922632575949995373890728757203118350068027316035993721712660832053747088407453415053335460006809619169511454946573970664063797369027524511541198389198120607997450128502579346624782505934683712209439532856161252306083182481147043608655277093742751801115903329689307793373858706210847044736819346947660318385464186521421304291098722199172480989006128576436071371426572961511739213786568379984431228971116422272517372020330081227054678170939969129248101418080035275759636981734529854503844149149073255048592583562371466242268171503038249341612152326757102057982722674984818888850549649666847149591658455068536333268090089859263518078361698444308728890672387057607494395978649217788954470501623262262781040233704305190905313047301873465562843178722713055220565955196202905603142005424180613393626403251640839600046540615613888978766360183358446853226822300334617875948556135674958419455600841022641897489769317002991903161018527398691987802442648555169898785559365347838925631262500132730807064159690642542511974869241523596533928439054336⟩, 0⟩,
  ⟨⟨642, 154, 322227501897208045805613422823698376657363539951349836224106160952164954331211578870161683719343711669122748663340937275336314283616315322185031835241216231689959675993680475724454573465956003698011295230321679833946826266318545965065114905900313496948425113673453361644989052198941053461288760814565055366764472009029996683670920384081499490684126225714883255633238205674579673143008774706876473861624138796602058579436508323237452095117443408915070149600890464736241741876281724685228074965189861781834286115044833161896298785309835453950266134593487524009907273918807700855758604082365545740666931984478198938211324851918815791765749579261011804938426096110366271103039589847305895966848877900902002313836095202586473213953120703421821811082088237139283247639608830362839681237140516704363381645074636048614868244914223127925251475905774045907694637011306989792002059252205202745559403525087685281430885118758777753243617572466566078399877136878213586752176835148924678070189135036031629322780211919076414010767204287441991353930686955708615002647833742182552993760397960515763991869105287414582034180479314133430144690541983211034000882190771414395978486445102734914175751288067494132155997002253814116842167317721256505278089830416311471700598440222862546138270605852605217065058895036153856⟩, 0⟩,
  ⟨⟨641, 155, 28832429017324303832458491482072293071367949950294493987470930962820203907907136803879541470326790279856813452737520761529894763583882605592012791838896036798070967988628862566209698446409445214611592433120828120779144772633806156176429844010541621442995987904280695606896135035467867389472416052346323092204199729230258449694041888324623349646069885902488693306566734713628457866288083069384150211587531177740179399202956398591774064723839052727790083013869107907220192050910254086493869351495713494454554550614374365565179269007908184719473866937802121386336404354775581875766767461112391157571797226520785530753580462918061661472326159154494261567810624849410190003384200982646555144355261480218203743928930932301766682021761020062305950618628991036675455544246191788958819987634037474736580345337031165791863831413752643629588307393151142331417269231435977240457767991574703482313983563130308069076952275265026519779362403933117276160408773983277715658072230445709938161673796871010797604216462590999184793617114997749573105176552114313715365512931271472973491141058421088519129343654423579053885438234062651661062985279027335624529594006166434915775703814263899756240551174508763427036744388450399763908932337843732590234866711368509013976397048270800519638467021550203485002983563794800472198479872⟩, 0⟩]

private def suffix012 : List Row := entries012.map CEntry.row ++ suffix016

private theorem score012 : batchScore 2356 suffix012 = 36560092496 :=
  cJoin 2356 entries012 suffix016 4 884455080 35675637416
    (by decide +kernel) (by decide +kernel) rfl score016

private def entries008 : List CEntry := [
  ⟨⟨648, 153, 400130331886298982075590595115403816710182691075898103816616446827291002971495399152984038232657215049147850070080688049395776096981944332954413323999291416382616895177478862275602558529466528318953357963235938928640235107288650511265155779849559422744413239183926244874924749164801714013314818625877437149555590130269930967992684069537002028978881659149611183980536646951311095269836991411536407628912275432422124617093868761187340280394652405562085746969104480389644995789881291160092748709172342756999320327458463608126189180757057171676089846749543923344926790322635545386317737377107754512031133458854231019638180455028081671637739679070907652798548668913779989247438907311551323485803485742596100975155262805432923111505394657280053691916183841923063085086267977102332608924622043607268629596632355383666655920133773632715309035522781261613056961850069461917400612095367924336682997895641664941114645485618334828367787976913107928469168921760237528141122383385137654190413408000274260801593514419267934502978905104984063143163781336663837725975442547851184316836806852359956485976620764941229084143941679554359156884815350757671444009012475819729837019363214459601527157392422918668308416662835379484541764601048112780603786939223403253387202029097839502674974577690389794217000960⟩, 0⟩,
  ⟨⟨647, 153, 800260660791394677158430344606726187852710947842611210740348701090577619950265016401207123735842959294259786494404382810739752339183425902176314331629051760741370473355091466400149838014819432976228600630806885178632705598402435615775245083947269883710109403221529868444687472121466122003085598654303383528278580904272112626453071333382125510258488026407848652542524282074601973455133566878380332574463346589849604048141932412017902361110618239346305453564663244815030783860186356672666584816726416874769631478825648889546663172621483232564021937214513187452893349862110439277463929200879907074560209288153915681990036826232613712694572920070876346729512938700094274915404640549350134543248640471395184296875994843188563131736523036801788818387083446133232893450420265624128540988146435296299336635627372647408481759994807595079741104436807984360959457230419821244603977993239320916562915407485028910888435660684480131224779389848254773976955142818740323568457509447256640961226768572686375788399338886865087963665450146831433258500099031835288106139857815406924838777120629523571905120142254032064526162808598779650713510400060748440522819173902828036788451910756366752323417067112095328517238409450966783953056637899238395628654996608482569921606070948782403314674881814440666705428480⟩, 0⟩,
  ⟨⟨646, 153, 1200390986715287135224833324499779767889901409936899057279968982305792098100946695254444934029748760517381550727939414380274209067577334145946175626730386337873092244111298235842650065113324956744892941515318938936820459585479865681222758674511634905262209291048570868830360471129541700737382232642996538661239329605185302730493021086256387484567446733103630477720505762736676098306010656943697388349187342874422434761418888885739133374145657872686362417401482886756350316236919966941925486834796116580827769485923949788527808079240974816363783206701058351301449555900030968011415159686619109855849270262467647542670860988842881033188322939416990183378230678249956529805920951469130074357931742703193086759168369294159972829849818577899219388421420397429014284366252689250951693998544451341373389305554513028283335810081446777054597781860278439444250263479399925213760416594857584313091978997514062996352933801861016529517605461221644181242071133741691056378046512429359691777715397668856115058277648324643536936684722570719522685894432639695714885458169371099020135052709569814812876141333321041464363211137197093769015951313826735558560281384936758287419140638670859927271977018033950861424424060360897783826052603724994444803698392366951090488991362654526511901839665263347256996659200⟩, 0⟩,
  ⟨⟨645, 154, 107409168099330007405796987869114775476485227286969910383877494627898973350218927792943935708118397226000104338692218586865785155852939238648517871450084558506879220927740635296737915375621874691694140085508033342068842836810955719044209688467720137942355135125168810447403302455804802649368374830736041957953525178893669360252912192713215098363471927936890960599630719837650498957891571520409393329307208840593000312600199735052999936856066444477219823272013880966334175376339357638618283320932788019566550352319061698810869475340584202199444301657648175349749415113818509280222034710784061865217522365994811065765185679960795830505652933610742934586149332020024103605076516457545516148325668935624107245276655154944092164316466350359897261485207374958175269217596345492031820027956122808851967878725559319476266999957591266472424692227146478559875928511475113718360720293416342335877259117875770608993074424701335299367636951000140107640327299221746560295199399533920619744063956371169882274479302872723245076504025220403736668211367053273702294382310492735351089995426857436416447574003550435394723008769465490847071650855407983640442746560195504419143098217526030145640240449271383241765764223937455489655601123060316819680117148389959834105980519414266255215824056671635699330522158974631936⟩, 0⟩]

private def suffix008 : List Row := entries008.map CEntry.row ++ suffix012

private theorem score008 : batchScore 2352 suffix008 = 37439617737 :=
  cJoin 2352 entries008 suffix012 4 879525241 36560092496
    (by decide +kernel) (by decide +kernel) rfl score012

private def entries004 : List CEntry := [
  ⟨⟨652, 152, 1490601643496375464184547197503610475539731862290179740572582848544115750510474953691521411266537809729243366847206042540642809936855907980126956874825769452006776551442306555819929249315819586556617082056433056057861124235460964828953075810990908206312371856289244014640948961734657949041020389103551275228570028778254707879676045382335599946965209023437383735757592914979347991570734517842040699110012646764607083938172696310385953830266815044776232446426168078206314032254436930090598851707742145079530348773194610995422893282021681036060704658955357834974348640324250808349413394247204577040878708987995196783858220059184902450451264058902400521326186719652416405400997121916126087989593284180638752628166061117851863684307287165724627801080150058637023533096106235146832845672903617608174010211434518317682609834936169181279994607456505399848793083993921879691037337601344262732705676826273862433470101335686335237839026020648134476169069392085261572413085061817434055091439001345699263807310808938224740784237370609334611477081714409102826755468890672976023404122977134255108704618793691547288638976238232364237814055542888406586077843481045674439853648879294880526414737737609965463910893349660185687918445215028389705389110676406844048944521584320214372956887317085159424⟩, 0⟩,
  ⟨⟨651, 152, 2981203275886903245592230352039360209750796335798432872845093715915917864693613697363959329244345632941885007565037156156523626461361242138080052163821314708797561866118711730745703754109100079549927683794289353078512528074505188620952472219239048064787732513137046256674697954485724230516658688839516952330814775427806563436688006857298960131053097706013525551482401622570786588055063468911674054340125979856047405630801554701455927897289247139368810127467025335363185086233001476884443313667136169909592082292675107881035442916240591093088485629529594680943502829014426569950131769459228968775921239387039114216378409928809365143339722927546157951887601696500650422451725520461516000155350905810537747162749524459332147778192069661526600696022796597142315329393384906924068727760222323465193171633304868753917999512672442368592302679501879336716052359722766971541049902859567547778674938714891411507829644171694221517072153731320783729701320013216867189601749793160301136930999554028237184943933602317811772409131136430846707261738009649871303764704060552390784552676764856383913259306753373494456174953466445262343625360168706641559594989515106147141607985409760018806940901016291078365304886224096169819658308886568304231509632857024051607903503885214644101555959458560999424⟩, 0⟩,
  ⟨⟨650, 152, 4471804897171583530399327443911804884262015707555782263278830790066596420619761841245217027218640762897473147177033008681612652375181970747126531581795178433187440317481496435210789702051676061061095490638309068132675822855743317542616247517923915777385478400066200235622098954825923286617338288908577238119684499268974584444341587921126233208808445691486457459107355200002293097485216839178897237377873893426251863408511697740121812343862249007180246610251781326985048448726027706501823060791704972750198112972105092386265275627500917198787033735937319490459764420769201708329866049534705018731974740310056578155004194451195186741507783590142778614005285276092595488719295320641848102763752105437156813239914804118429084756816548339170407150129077272157917513999723011776701616908158399073325601683270220351662093080701056335308856987625126639368367864644213768181443378787235369197860929057957854244582919710669123818802509639555139098516046691944313669123494021876311101820903362992700535507754910330685299025294223180571041459036059188122739796355008107026577265289963793271106088164532966599075602308216888158496825547908491430869420318493339626003465507243652226342720269134897703416818704530203313895092956753628039143126386722146283999902926988622418085664223048417411072⟩, 0⟩,
  ⟨⟨649, 153, 400130331886298976522666795099478192883737656292397668254015467585005613205329858768791384149585474593885418418799936451366789673955963062639636416575480000414002917475238673919155332151568573302071481561458888753871132068557412423068622582553144888329699444818229910655260490977943780566803712700428477141557956312394133199703830887804526276938430145720541225481429749553331137572758970577071825680757082954251753441206560789184656822527275879510105927641049551828786234740099646428691819725801667771352550603284625304562067296635204637526125322965590366231103673205076985729311926622117327044471748642584498782062708710871973591838440491012861480132009266029829223047208233790031174432526373869410992919690662516569593535651720142326079139562023214475676320796709697384072709292247730078617651721117090756801059618020863238982930419247105676144406769164392908400469758318166807240166691986336471432661294019254010597669779823874334177824393205574208135478296601501117146745861310682319445822524884217991337388283978477233584525667256863915715157670966034928395218814588577970417104140441511749408052015583042343456837259806059238794913257246335373906112481542599150385030086423020443963746543275465493762381712920129576732123896498455631586704024325480929383791946068125230633876193280⟩, 0⟩]

private def suffix004 : List Row := entries004.map CEntry.row ++ suffix008

private theorem score004 : batchScore 2348 suffix004 = 38314124310 :=
  cJoin 2348 entries004 suffix008 4 874506573 37439617737
    (by decide +kernel) (by decide +kernel) rfl score008

private def entries000 : List CEntry := [
  ⟨⟨656, 151, 5552923841388432098546230015645222627819944476600544784501282160095516349561852382071274031548538059358454555917531835375293427671009918515248494867637759968873636939864842316673764445908534592261587919756610787146925564486258878712185342500414967511837777331374665730997201856852470302151803186859056484247337650625263572339797336687408475283657268259787732196167869993257231430823171482042693582688379923189031656338652353539189633182797600101182289205253115090065655011398579908247111947293833571751374663780623611235272691942710690169132556945194191936850768287987852952939833847729281086187298394398952521347780605066061712731795139348414199231050822680548489110389976093077401776132848712318629863890581485242320759715230540041569625518768371284480884959866201957756283879034028183749870765873887728359983137604288304700696254000564240077389157660556862413703695962256730512091336579039137423849462306876537309844264901848294831500760959333863672234718236784685612886951849125389552059364781847653629068967430487823556588817851511725576331667252908396776730488282373979791245019764642766178902034196780449167376344457397053487100086874599744007330793874833494122111588454536474881425799731274946926482796427637818585847459244657067171711204436348358215519344525312⟩, 0⟩,
  ⟨⟨655, 151, 11105847620718104716199676758129926524130536300305211544774409700555240190719975426942429057251430315342494536928281579849743075313875723108589990475188690961115207869588902809251043285915428661324578277052363567242670172411701323469964427300374004016664402483907706254091722717836540837655971929083231361777368693961385051672566754023874218016859732292325438725928541952056945043758715099543801750379398313239486903930024044884320149313917527787924388706083809807647395834256719200883968850097275288888411550906684619696869784255819819875568549327325721381343838109519115552157190249422876290643337671888473229527498684895411412579133109659125121301069732025501596030061649052473854052977202670347023515421374006954929319664060466477622653464195088906906192876088908780062720389856252008328659852215792353296655006329256585576714231840788197327089964641780805758084319885692629733488570915450201996399867225937736149924148568766046615326719418464484109431208130407471466480193272580996925182103690618287756325543933424533097112966336344970920809476124330329264520242517332299779430918740146965728652920828150559704278858973716474958313628475213330651820542471693727661131866369516966478601921393282275526136476467592657794146360793421544656254276894230398656134651052032⟩, 0⟩,
  ⟨⟨654, 151, 16658771400047777333853123500614631489895342691077970949109013341615335720106072132457856190274062614506010514412198248064565106573232467728847162803198015567002212994826094261264456004550932545980850719309141099817147143683161787666947086324071335333588125437928529543087330040315062702918186934244730001075330922943821329552039082555600788187174943254652555512278327273331710500059876579021923755914795935273682716893925951783115906584089527266866216723818231180646127747060281542793817436377237300421896135825683521966417981212551276707208706784188327448398484630378410698077122182101969499044201179257933751207448502620788829458306643505275279266270458979989134688079933546132569880082496399442602993002327221209716802443230957944639126349110348107602131114140802414059361497952912674222382180097933578617651120625787228607614196850533224529505944256182532237109731735446622058170681152602428087441866277663011881800359397853668336375273595170873458163088049395833500596441125163061658905462561303370607877565818449049018235829438509956000442018909346055261801882547499905372682291681409165218081300819772077203685904683959339080109880716379319162014188657673438898187539078875806426988080932780004044433581053721466554478332983812945882999356210363731304516656562176⟩, 0⟩,
  ⟨⟨653, 151, 16658771400047777333853123787694061248328132627201320033638350407863008425161621987879668813887552662047553003613742535834017851135394960428519723913537459683492904639084605155244583211699978196198829370337115401780795977294012701186837735338151594138585060525549043297748252118109569433937406496643540121103430537376470110283683903350476068815764371179110333215606403011752928556915457094880340995355673825410443932479616016504911853153440618080155340782276121201042347971687820436639725996639183127328556461818982159972859240196103937119608029156068915904516996399044063899098656287479590724705278021132837349438036898915107630265144594129533420979797850769015905550920892645076116843443409714070868329921176655236375549740601544083612896381162636818072117850392186929285515677814248094604029639335278442807772254286408094254171833188941216836766928135414807223170651089006175453143890212687849003672275748528067509867939743634479153119170184524682984868698167125843516746422756378651265702592202983636055103970591885970567825388268212252639711202877107041529466992332769526028744021873422208211083206543130080950425853267985873398848408311549283920359925563990617879732305856026199105880768943182020709633177284580997897767880441055398030633711961028344446265501679616⟩, 0⟩]

private def suffix000 : List Row := entries000.map CEntry.row ++ suffix004

private theorem score000 : batchScore 2344 suffix000 = 39183500746 :=
  cJoin 2344 entries000 suffix004 4 869376436 38314124310
    (by decide +kernel) (by decide +kernel) rfl score004

end DataC2344

/-- Original two-round witness for grades 2344 through 2511. -/
def rowsC : List Row := DataC2344.suffix000

theorem checkedC : batchScore 2344 rowsC = 39183500746 := DataC2344.score000

end K1_13_2_3_5
end PackSource_K1_13_2_3_5DataC

section PackSource_K1_13_2_3_6AuxD
set_option autoImplicit true
/-!
The row literals are the original run-length codes. The private evaluator uses
the shifted denominator cubic and a single cubic for three consecutive correction
terms. The range proof connects this natural-number calculation to `blockSaving`.
-/

namespace K1_13_2_3_6

open K1_13_2 K1_13_2_3
open K1_13_2_3_5
open private fastDen fastDen_eq fastC fastC_eq fastOld fastKernel fastKernel_eq from ProximityPrize.SubmissionLower.Numeric6Defs
open private kFast_correct denFast_correct cumFast_clipped balance from ProximityPrize.SubmissionLower.Numeric5Defs
open private rowStart rowValue runValue sumFrom runLength decode from ProximityPrize.SubmissionLower.Numeric6AuxCert

-- The denominator cubic at the shifted argument u - 1, including its zero case.
private def dDen (u : ℕ) : ℕ := (u * (u * (2*u + 15) + 30) + 25) / 72

private theorem dDen_eq (u : ℕ) : dDen u = denFast u := by
  apply Int.ofNat_inj.mp
  rw [denFast_correct, ← fastDen_eq]
  cases u with
  | zero => decide
  | succ n =>
    simp only [dDen, Int.natCast_ediv, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_succ, add_sub_cancel_right, fastDen, Int.natCast_nonneg, not_lt.mpr,
      ite_false]
    congr 1
    ring

private def dNatKernel (d l c o : ℤ) (j : ℕ) : ℕ :=
  let r := (min d ((o-1-l+d)/4) + 1).toNat
  kFast d.toNat (l.toNat-j) (3*c+1).toNat (o.toNat-j) r

private theorem dNatKernel_eq (d l c o : ℤ) (j : ℕ)
    (hd : 0 ≤ d) (hc : 0 ≤ c) (hl : l-j-1 ≤ 3*c) (hb : 0 ≤ o-1-l+d) :
    dNatKernel d l c o j = (fastKernel d (l-j) c (o-j)).toNat := by
  let F : Flag := ⟨d, l-j, 3*c, c, o-j⟩
  let r := (min d ((o-1-l+d)/4) + 1).toNat
  change kFast d.toNat (l.toNat-j) (3*c+1).toNat (o.toNat-j) r = _
  rw [fastKernel_eq]
  have hl' : l.toNat-j = (l-j).toNat := by omega
  have ho' : o.toNat-j = (o-j).toNat := by omega
  rw [hl', ho']
  have hbal : balance F = o-1-l+d := by dsimp only [balance, F]; ring
  have hrpos : 0 ≤ min d ((o-1-l+d)/4) + 1 := by
    have : 0 ≤ (o-1-l+d)/4 := by omega
    omega
  exact kFast_correct F d.toNat (3*c+1).toNat r (by dsimp [F]; omega)
    (by dsimp [F]; omega) (by dsimp [F]; omega) hc le_rfl hl (by rw [hbal]; exact hb)
    (by rw [hbal]; exact Int.toNat_of_nonneg hrpos)

private theorem dSaving_eq (old ini res : ℤ) :
    (old - max 0 ini).toNat - (old - max (max 0 ini) res).toNat =
      (old.toNat - ini.toNat) - (old.toNat - res.toNat) := by omega

private def dOld (j : ℕ) : ℕ := 125576826 - dDen (1650-j)

private theorem dOld_eq (j : ℕ) : dOld j = (fastOld 1650 (1650-j) 550).toNat := by
  unfold fastOld
  rw [min_eq_right (show (1650:ℤ)-j-1 ≤ 3*550 by omega)]
  change _ = ((125576826:ℤ) - fastC 1650 (1650-j-1)).toNat
  have he : (dDen (1650-j) : ℤ) = fastC 1650 (1650-j-1) := by
    rw [fastC_eq]
    change _ = cumulative ((1650 : ℕ) : ℤ) ((1650:ℤ)-j-1)
    rw [← cumFast_clipped 1650 (1650-j), dDen_eq]
    have ht : ((1650:ℤ)-j).toNat = 1650-j := by omega
    rw [ht, cumFast, ite_eq_left (by omega)]
  rw [← he]
  unfold dOld
  omega

private def dRange (d l c o : ℤ) (j : ℕ) : Bool :=
  decide (0 ≤ d ∧ 0 ≤ c ∧ l-j-1 ≤ 3*c ∧ 0 ≤ o-1-l+d)

private def dColumn (s : ℕ) (d l c o : ℤ) (j : ℕ) : ℕ :=
  let old := dOld j
  (old - dNatKernel 1650 1650 550 (4650-s) j) - (old - dNatKernel d l c o j)

private theorem dColumn_eq (s j start : ℕ) (p : Powers) (hj : start ≤ j)
    (hs : s ≤ 4649)
    (hg : dRange (1650-(p.value+(p.top:ℤ)+3*p.cubic)) (1650-(3*(p.top:ℤ)+2*p.cubic))
      (550-(p.top+(p.cubic:ℤ))) (4650-s-(2*(p.top:ℤ)+3*p.cubic)) start = true) :
    dColumn s (1650-(p.value+(p.top:ℤ)+3*p.cubic)) (1650-(3*(p.top:ℤ)+2*p.cubic))
      (550-(p.top+(p.cubic:ℤ))) (4650-s-(2*(p.top:ℤ)+3*p.cubic)) j = blockSaving s j p := by
  obtain ⟨hd, hc, hl, hb⟩ := of_decide_eq_true hg
  unfold blockSaving dColumn
  rw [dSaving_eq, dOld_eq, dNatKernel_eq _ _ _ _ _ hd hc (by omega) hb,
    dNatKernel_eq _ _ _ _ _ (by decide) (by decide) (by omega) (by omega)]
  rw [show (1650:ℤ) - (3*(p.top:ℤ)+2*p.cubic) - j = 1650-j-(3*(p.top:ℤ)+2*p.cubic) by ring,
    show (4650:ℤ) - s - (2*(p.top:ℤ)+3*p.cubic) - j = 4650-s-j-(2*(p.top:ℤ)+3*p.cubic) by ring]

private theorem dSumFrom_congr (f g : ℕ → ℕ) (j n : ℕ) (h : ∀ i, j ≤ i → f i = g i) :
    sumFrom f j n = sumFrom g j n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumFrom, sumFrom, ih, h _ (by omega)]

-- Three consecutive shifted denominators have a single cubic formula.
private def dPenalty (x : ℕ) : ℕ := (x * (x * (2*x + 9) + 10) + 3) / 24

private theorem dDen_shift (q r : ℕ) :
    dDen (12*q+r) = dDen r + q * (q * (48*q+12*r+30) + r*r+5*r+5) := by
  unfold dDen
  rw [show (12*q+r) * ((12*q+r) * (2*(12*q+r)+15)+30)+25 =
    r*(r*(2*r+15)+30)+25 + 72*(q*(q*(48*q+12*r+30)+r*r+5*r+5)) by ring,
    Nat.add_mul_div_left _ _ (by decide)]

private theorem dPenalty_shift (q r : ℕ) :
    dPenalty (12*q+r) = dPenalty r + q * (q * (144*q+36*r+54) + 3*r*r+9*r+5) := by
  unfold dPenalty
  rw [show (12*q+r) * ((12*q+r) * (2*(12*q+r)+9)+10)+3 =
    r*(r*(2*r+9)+10)+3 + 24*(q*(q*(144*q+36*r+54)+3*r*r+9*r+5)) by ring,
    Nat.add_mul_div_left _ _ (by decide)]

private theorem dPenalty_period (q r : ℕ) (hr : r < 12) :
    dPenalty (12*q+r+2) = dDen (12*q+r+2) + dDen (12*q+r+1) + dDen (12*q+r) := by
  have h : ∀ i : Fin 12, dPenalty (i.val+2) = dDen (i.val+2) + dDen (i.val+1) + dDen i.val := by
    decide
  simp only [Nat.add_assoc (12*q) r, dPenalty_shift, dDen_shift]
  rw [h ⟨r, hr⟩]
  ring

private theorem dPenalty_eq : ∀ x : ℕ, dPenalty x = dDen x + dDen (x-1) + dDen (x-2)
  | 0 => rfl
  | 1 => rfl
  | n+2 => by
    rw [show n+2-1 = n+1 by omega, show n+2-2 = n by omega]
    simpa only [Nat.div_add_mod] using dPenalty_period (n/12) (n%12) (Nat.mod_lt _ (by decide))

-- Force a potentially long arithmetic expression before substituting it in a loop.
private def dWith (x : ℕ) (f : ℕ → ℕ) : ℕ :=
  match x with
  | 0 => f 0
  | n+1 => f (n+1)

private theorem dWith_eq (x : ℕ) (f : ℕ → ℕ) : dWith x f = f x := by
  cases x <;> rfl

private def dCellK (top o l rd tripleR j : ℕ) : ℕ :=
  let x := o-j
  let y := l-j
  top + dDen (x-tripleR) - (dDen x + (dDen y - dPenalty (y-(rd+1))))

private theorem dCum_simple (d u : ℕ) (hu₁ : u ≤ 3*d+1) (hu₂ : u ≤ 2*d+3) :
    cumFast d u = dDen u - dPenalty (u-(d+1)) := by
  by_cases h : u ≤ d+1
  · simp only [cumFast, ite_eq_left h, Nat.sub_eq_zero_of_le h, show dPenalty 0 = 0 by rfl,
      Nat.sub_zero, dDen_eq]
  have h₃ : u-(2*d+3) = 0 := by omega
  have h₄ : u-(2*d+4) = 0 := by omega
  have h₅ : u-(2*d+5) = 0 := by omega
  simp only [cumFast, ite_eq_right h, min_eq_left hu₁, h₃, h₄, h₅, ← dDen_eq,
    show dDen 0 = 0 by rfl, Nat.add_zero, dPenalty_eq,
    show u-(d+1)-1 = u-(d+2) by omega, show u-(d+1)-2 = u-(d+3) by omega]

private def dSpecRange (d l u o r j : ℕ) : Bool :=
  decide (r ≤ d ∧ u ≤ 3*d+1 ∧ u ≤ 2*d+3 ∧ o-j ≤ d+1 ∧ o-j-3*r ≤ d-r+1 ∧
    l-j ≤ 3*(d-r)+1 ∧ l-j ≤ 2*(d-r)+3)

private theorem dCellK_eq (d l u o r j start : ℕ) (hj : start ≤ j)
    (hg : dSpecRange d l u o r start = true) :
    dCellK (dDen u - dPenalty (u-(d+1))) o l (d-r) (3*r) j =
      kFast d (l-j) u (o-j) r := by
  obtain ⟨hr, hu₁, hu₂, ho, ho', hl₁, hl₂⟩ := of_decide_eq_true hg
  have h₁ : cumFast d (o-j) = dDen (o-j) := by rw [cumFast, ite_eq_left (by omega), dDen_eq]
  have h₂ : cumFast (d-r) (o-j-3*r) = dDen (o-j-3*r) := by rw [cumFast, ite_eq_left (by omega), dDen_eq]
  simp only [kFast, cutFast, ite_eq_right (by omega : ¬ d < r), dCum_simple d u hu₁ hu₂, h₁, h₂,
    dCum_simple (d-r) (l-j) (by omega) (by omega)]
  rfl

private def dRemoved (d l o : ℤ) : ℕ := (min d ((o-1-l+d)/4) + 1).toNat

private def dGood (d l c o : ℤ) (j : ℕ) : Bool :=
  dSpecRange d.toNat l.toNat (3*c+1).toNat o.toNat (dRemoved d l o) j

-- Normalize each run's constant coefficients before traversing its columns.
private def dPrepare (d l c o : ℤ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  let u := (3*c+1).toNat
  let r := dRemoved d l o
  dWith (dDen u - dPenalty (u-(d.toNat+1))) fun top =>
  dWith o.toNat fun ord => dWith l.toNat fun lo =>
  dWith (d.toNat-r) fun rd => dWith (3*r) fun triple => f top ord lo rd triple

-- These bounds on the grade, column and exponents select the cubic formulas.
private def dRegion (s j a b c : ℕ) : Prop :=
  3162 ≤ s ∧ s ≤ 3213 ∧ 3383 ≤ s+j ∧ a+4*c ≤ 512 ∧ b ≤ 256 ∧ a ≤ b+384

private instance (s j a b c : ℕ) : Decidable (dRegion s j a b c) := by
  unfold dRegion
  infer_instance

private theorem dRegion_data (s j a b c : ℕ) (h : dRegion s j a b c) :
    let d : ℤ := 1650-(a+(b:ℤ)+3*c)
    let l : ℤ := 1650-(3*(b:ℤ)+2*c)
    let cap : ℤ := 550-(b+(c:ℤ))
    let o : ℤ := 4650-s-(2*(b:ℤ)+3*c)
    dRange d l cap o j = true ∧ dGood d l cap o j = true ∧
    d.toNat = 1650-(a+b+3*c) ∧ l.toNat = 1650-(3*b+2*c) ∧
    (3*cap+1).toNat = 1651-3*(b+c) ∧ o.toNat = 4650-(s+2*b+3*c) ∧
    dRemoved d l o = (4649-(s+a+4*c))/4+1 := by
  obtain ⟨hs, hs', hj, ha, hb, hba⟩ := h
  intro d l cap o
  have hbal : o-1-l+d = 4649-((s:ℤ)+a+4*c) := by dsimp [d,l,o]; ring
  have hd : 882 ≤ d := by dsimp [d]; omega
  have hc : 0 ≤ cap := by dsimp [cap]; omega
  have h₁ : 0 ≤ o-1-l+d := by rw [hbal]; omega
  have h₂ : (o-1-l+d)/4 ≤ 371 := by rw [hbal]; omega
  have hr : dRemoved d l o = (4649-(s+a+4*c))/4+1 := by
    unfold dRemoved
    rw [min_eq_right (by omega), hbal]
    omega
  have ed : d.toNat = 1650-(a+b+3*c) := by dsimp [d]; omega
  have el : l.toNat = 1650-(3*b+2*c) := by dsimp [l]; omega
  have ec : (3*cap+1).toNat = 1651-3*(b+c) := by dsimp [cap]; omega
  have eo : o.toNat = 4650-(s+2*b+3*c) := by dsimp [o]; omega
  refine ⟨?_, ?_, ed, el, ec, eo, hr⟩
  · apply decide_eq_true
    refine ⟨by omega, hc, ?_, h₁⟩
    dsimp [l,cap]
    omega
  · unfold dGood dSpecRange
    rw [ed, el, ec, eo, hr]
    apply decide_eq_true
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private def dNatPrepare (s a b c : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  let d := 1650-(a+b+3*c)
  let u := 1651-3*(b+c)
  let r := (4649-(s+a+4*c))/4+1
  dWith (dDen u - dPenalty (u-(d+1))) fun t =>
  dWith (4650-(s+2*b+3*c)) fun o => dWith (1650-(3*b+2*c)) fun l =>
  dWith (d-r) fun rd => dWith (3*r) fun tr => f t o l rd tr

private theorem dNatPrepare_eq (s j a b c : ℕ) (h : dRegion s j a b c)
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    dNatPrepare s a b c f =
      dPrepare (1650-(a+(b:ℤ)+3*c)) (1650-(3*(b:ℤ)+2*c)) (550-(b+(c:ℤ)))
        (4650-s-(2*(b:ℤ)+3*c)) f := by
  obtain ⟨_, _, ed, el, ec, eo, er⟩ := dRegion_data s j a b c h
  unfold dNatPrepare dPrepare
  rw [ed, el, ec, eo, er]

private def dCubic (u a b c divisor : ℕ) : ℕ :=
  Nat.div (Nat.add (Nat.mul u (Nat.add (Nat.mul u (Nat.add (Nat.mul 2 u) a)) b)) c) divisor

private def dCountAt (top x y rd tr denX denY : ℕ) : ℕ :=
  Nat.sub (Nat.add top (dCubic (Nat.sub x tr) 15 30 25 72))
    (Nat.add denX (Nat.sub denY (dCubic (Nat.sub y (Nat.add rd 1)) 9 10 3 24)))

-- Runs with only the first exponent active use the same order and lower
-- cutoff as the initial kernel. Share both column denominators in that case.
private def dRunSum (t o l rd tr t₀ o₀ l₀ rd₀ tr₀ j n : ℕ) : ℕ :=
  if o = o₀ ∧ l = 1650 ∧ l₀ = 1650 then
    sumFrom (fun k => dWith k fun k =>
      let x := Nat.sub o₀ k
      let y := Nat.sub 1650 k
      dWith (dCubic x 15 30 25 72) fun denX =>
      dWith (dCubic y 15 30 25 72) fun denY =>
      let old := Nat.sub 125576826 denY
      Nat.sub (Nat.sub old (dCountAt t₀ x y rd₀ tr₀ denX denY))
        (Nat.sub old (dCountAt t x y rd tr denX denY))) j n
  else
    sumFrom (fun k => dWith k fun k =>
      let old := dOld k
      (old - dCellK t₀ o₀ l₀ rd₀ tr₀ k) - (old - dCellK t o l rd tr k)) j n

private theorem dRunSum_eq (t o l rd tr t₀ o₀ l₀ rd₀ tr₀ j n : ℕ) :
    dRunSum t o l rd tr t₀ o₀ l₀ rd₀ tr₀ j n =
      sumFrom (fun k => (dOld k - dCellK t₀ o₀ l₀ rd₀ tr₀ k) -
        (dOld k - dCellK t o l rd tr k)) j n := by
  by_cases h : o = o₀ ∧ l = 1650 ∧ l₀ = 1650
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [dRunSum, and_self, ite_true, dWith_eq]
    rfl
  · simp only [dRunSum, ite_eq_right h, dWith_eq]

-- The initial kernel coefficients stay fixed across the grade; the residual
-- coefficients stay fixed across the run.
private def dRunAt (s j code t₀ o₀ l₀ rd₀ tr₀ : ℕ) : ℕ :=
  if code % 2147483648 = 0 then 0 else
    let p := decode code
    if dRegion s j p.value p.top p.cubic then
      dNatPrepare s p.value p.top p.cubic fun t o l rd tr =>
      dRunSum t o l rd tr t₀ o₀ l₀ rd₀ tr₀ j (runLength code)
    else runValue s j code

private theorem dRunAt_eq (s j code : ℕ) :
    dNatPrepare s 0 0 0 (fun t o l rd tr => dRunAt s j code t o l rd tr) =
      runValue s j code := by
  by_cases hz : code % 2147483648 = 0
  · simp only [dNatPrepare, dWith_eq, dRunAt, runValue, hz, ite_true]
  by_cases h : dRegion s j (decode code).value (decode code).top (decode code).cubic
  · have h₀ : dRegion s j 0 0 0 := ⟨h.1, h.2.1, h.2.2.1, by decide, by decide, by decide⟩
    obtain ⟨hg, h₁, _⟩ := dRegion_data s j (decode code).value (decode code).top (decode code).cubic h
    have h₂ : dGood 1650 1650 550 (4650-s) j = true := by
      simpa using (dRegion_data s j 0 0 0 h₀).2.1
    simp only [dRunAt, dRunSum_eq, runValue, ite_eq_right hz, ite_eq_left h, dNatPrepare_eq s j _ _ _ h,
      dNatPrepare_eq s j 0 0 0 h₀, Nat.cast_zero, mul_zero, add_zero, sub_zero, dPrepare, dWith_eq]
    apply dSumFrom_congr
    intro k hk
    rw [dCellK_eq _ _ _ _ _ k j hk h₁, dCellK_eq _ _ _ _ _ k j hk h₂]
    exact dColumn_eq s k j (decode code) hk (by have := h.2.1; omega) hg
  · simp only [dNatPrepare, dWith_eq, dRunAt, ite_eq_right hz, ite_eq_right h]

private def dFold (s t o l rd tr j : ℕ) : List ℕ → ℕ
  | [] => 0
  | code :: tail => dWith j fun j =>
    dRunAt s j code t o l rd tr + dFold s t o l rd tr (j + runLength code) tail

private def dRowWork (s j : ℕ) (row : List ℕ) : ℕ :=
  dNatPrepare s 0 0 0 fun t o l rd tr => dFold s t o l rd tr j row

private theorem dRowWork_eq (s j : ℕ) (row : List ℕ) : dRowWork s j row = rowValue s j row := by
  induction row generalizing j with
  | nil => simp only [dRowWork, dNatPrepare, dWith_eq, dFold, rowValue]
  | cons code tail ih =>
    have h := dRunAt_eq s j code
    have ht := ih (j + runLength code)
    simp only [dRowWork, dNatPrepare, dWith_eq, dFold, rowValue] at h ht ⊢
    rw [h, ht]


-- Check each row's fit and its individual saving. An unequal number of
-- rows and expected savings makes the check fail.
private def dCheckRows (s : ℕ) : List (List ℕ) → List ℕ → Bool
  | [], [] => true
  | row :: tail, v :: vs =>
    (fits s [row] && Nat.beq (dRowWork s (rowStart s) row) v) && dCheckRows (s+1) tail vs
  | _, _ => false

private theorem dCheckRows_sound (s : ℕ) (rows : List (List ℕ)) (vs : List ℕ)
    (ok : dCheckRows s rows vs = true) :
    rows.length = vs.length ∧ fits s rows = true ∧ value s rows = vs.sum := by
  induction rows generalizing s vs with
  | nil =>
    cases vs with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons => contradiction
  | cons row tail ih =>
    cases vs with
    | nil => contradiction
    | cons v vs =>
      obtain ⟨hrow, ht⟩ := Bool.and_eq_true_iff.mp ok
      obtain ⟨hf, hv⟩ := Bool.and_eq_true_iff.mp hrow
      obtain ⟨hlen, hfit, hval⟩ := ih (s+1) vs ht
      refine ⟨by simp only [List.length_cons, hlen], ?_, ?_⟩
      · exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp hf).1, hfit⟩
      · rw [value, ← dRowWork_eq, Nat.eq_of_beq_eq_true hv, hval, List.sum_cons]

private theorem dJoin {s n m v w : ℕ} {a b : List (List ℕ)}
    (ha : a.length = n ∧ fits s a = true ∧ value s a = v)
    (hb : b.length = m ∧ fits (s+n) b = true ∧ value (s+n) b = w) :
    (a ++ b).length = n+m ∧ fits s (a ++ b) = true ∧ value s (a ++ b) = v+w := by
  simp only [List.length_append, fits_append, value_append, ha.1, hb.1, ha.2.1, hb.2.1,
    Bool.true_and, ha.2.2, hb.2.2, and_self]

set_option maxRecDepth 50000
set_option maxHeartbeats 0

private def dRows3162 : List (List ℕ) := [
  [nat_lit 128849018880, nat_lit 2349334528, nat_lit 10872160256, nat_lit 8691122176, nat_lit 67633152, nat_lit 4396023808, nat_lit 6509953024, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 6442844544, nat_lit 25770066304, nat_lit 8590131584, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 130996502528, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 2215116800, nat_lit 4396023808, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 6442844544, nat_lit 25770066304, nat_lit 10737615232, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 130996502528, nat_lit 201850880, nat_lit 13019643904, nat_lit 8691122176, nat_lit 2215116800, nat_lit 2248540160, nat_lit 4362469376, nat_lit 4345692160, nat_lit 33947648, nat_lit 25559040, nat_lit 17170432, nat_lit 12976128, nat_lit 6684672, nat_lit 6442844544, nat_lit 25770066304, nat_lit 8590131584, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 133143986176, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 2215116800, nat_lit 4396023808, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 6442844544, nat_lit 27917549952, nat_lit 8590131584, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3162 : dRows3162.length = 4 ∧ fits 3162 dRows3162 = true ∧
    value 3162 dRows3162 = 487238266 :=
  dCheckRows_sound 3162 dRows3162 [121051295, 121455241, 122157715, 122574015] (by decide +kernel)

private def dRows3166 : List (List ℕ) := [
  [nat_lit 133143986176, nat_lit 201850880, nat_lit 13019643904, nat_lit 8691122176, nat_lit 2215116800, nat_lit 2248540160, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 12976128, nat_lit 8590328192, nat_lit 25770066304, nat_lit 8590131584, nat_lit 131456, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 33152, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 133143986176, nat_lit 2349334528, nat_lit 10872160256, nat_lit 8691122176, nat_lit 2215116800, nat_lit 2248540160, nat_lit 6509953024, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 12976128, nat_lit 6684672, nat_lit 8590328192, nat_lit 25770066304, nat_lit 8590131584, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 135291469824, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 4362600448, nat_lit 2248540160, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 8590328192, nat_lit 27917549952, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 135291469824, nat_lit 201850880, nat_lit 13019643904, nat_lit 8691122176, nat_lit 4362600448, nat_lit 101056512, nat_lit 4362469376, nat_lit 4345692160, nat_lit 33947648, nat_lit 25559040, nat_lit 17170432, nat_lit 12976128, nat_lit 10737811840, nat_lit 25770066304, nat_lit 8590131584, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3166 : dRows3166.length = 4 ∧ fits 3166 dRows3166 = true ∧
    value 3166 dRows3166 = 497513376 :=
  dCheckRows_sound 3166 dRows3166 [123443105, 124175938, 124552060, 125342273] (by decide +kernel)

private def dRows3170 : List (List ℕ) := [
  [nat_lit 137438953472, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2248540160, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 8590328192, nat_lit 27917549952, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 137438953472, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 101056512, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 12976128, nat_lit 10737811840, nat_lit 25770066304, nat_lit 8590131584, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 139586437120, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 101056512, nat_lit 6509953024, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 12976128, nat_lit 12885295488, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 139586437120, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 101056512, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 2147877376, nat_lit 10737811840, nat_lit 27917549952, nat_lit 6442647936, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3170 : dRows3170.length = 4 ∧ fits 3170 dRows3170 = true ∧
    value 3170 dRows3170 = 507103137 :=
  dCheckRows_sound 3170 dRows3170 [125831812, 126595216, 126914003, 127762106] (by decide +kernel)

private def dRows3174 : List (List ℕ) := [
  [nat_lit 141733920768, nat_lit 13019643904, nat_lit 8691122176, nat_lit 4362600448, nat_lit 101056512, nat_lit 4362469376, nat_lit 4345692160, nat_lit 33947648, nat_lit 25559040, nat_lit 4295361024, nat_lit 10737811840, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 141733920768, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 6510084096, nat_lit 101056512, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 4295361024, nat_lit 10737811840, nat_lit 27917549952, nat_lit 6442647936, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 141733920768, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 50855936, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 6442844672, nat_lit 10737811840, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 143881404416, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 50855936, nat_lit 6509953024, nat_lit 2198208512, nat_lit 33947648, nat_lit 8590328320, nat_lit 10737811840, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3174 : dRows3174.length = 4 ∧ fits 3174 dRows3174 = true ∧
    value 3174 dRows3174 = 517353169 :=
  dCheckRows_sound 3174 dRows3174 [128216459, 129037592, 129876377, 130222741] (by decide +kernel)

private def dRows3178 : List (List ℕ) := [
  [nat_lit 143881404416, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 50855936, nat_lit 4362469376, nat_lit 2198208512, nat_lit 33947648, nat_lit 10737811968, nat_lit 8590328192, nat_lit 27917549952, nat_lit 4295164288, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 146028888064, nat_lit 13019643904, nat_lit 8691122176, nat_lit 4362600448, nat_lit 50855936, nat_lit 4362469376, nat_lit 4345692160, nat_lit 10737811968, nat_lit 10737811840, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 16768, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 146028888064, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 4362469376, nat_lit 2198208512, nat_lit 12885295616, nat_lit 8590328192, nat_lit 27917549952, nat_lit 4295164288, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 148176371712, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2214985728, nat_lit 2198208512, nat_lit 15032779264, nat_lit 8590328192, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 24960, nat_lit 16768, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3178 : dRows3178.length = 4 ∧ fits 3178 dRows3178 = true ∧
    value 3178 dRows3178 = 527675991 :=
  dCheckRows_sound 3178 dRows3178 [131068258, 131494371, 132362658, 132750704] (by decide +kernel)

private def dRows3182 : List (List ℕ) := [
  [nat_lit 148176371712, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 4362469376, nat_lit 2198208512, nat_lit 15032779264, nat_lit 8590328192, nat_lit 25770066304, nat_lit 4295164288, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 150323855360, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2214985728, nat_lit 2198208512, nat_lit 15032779264, nat_lit 8590328192, nat_lit 27917549952, nat_lit 4295164288, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 150323855360, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 4362469376, nat_lit 50724864, nat_lit 17180262912, nat_lit 8590328192, nat_lit 25770066304, nat_lit 4295164288, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 16768, nat_lit 12672, nat_lit 4480, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 150323855360, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 2214985728, nat_lit 50724864, nat_lit 19327746560, nat_lit 6442844544, nat_lit 27917549952, nat_lit 4295164288, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3182 : dRows3182.length = 4 ∧ fits 3182 dRows3182 = true ∧
    value 3182 dRows3182 = 538132627 :=
  dCheckRows_sound 3182 dRows3182 [133575592, 133903412, 134901286, 135752337] (by decide +kernel)

private def dRows3186 : List (List ℕ) := [
  [nat_lit 152471339008, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 34078720, nat_lit 67502080, nat_lit 50724864, nat_lit 21475230208, nat_lit 6442844544, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 152471339008, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 34078720, nat_lit 2214985728, nat_lit 50724864, nat_lit 19327746560, nat_lit 8590328192, nat_lit 25770066304, nat_lit 4295164288, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 154618822656, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 67502080, nat_lit 50724864, nat_lit 21475230208, nat_lit 6442844544, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 384, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 154618822656, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 34078720, nat_lit 2214985728, nat_lit 23622713856, nat_lit 6442844544, nat_lit 25770066304, nat_lit 4295164288, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3186 : dRows3186.length = 4 ∧ fits 3186 dRows3186 = true ∧
    value 3186 dRows3186 = 548627072 :=
  dCheckRows_sound 3186 dRows3186 [136025913, 136921355, 137350350, 138329454] (by decide +kernel)

private def dRows3190 : List (List ℕ) := [
  [nat_lit 156766306304, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 67502080, nat_lit 25770197504, nat_lit 4295360896, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 6528, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 156766306304, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 34078720, nat_lit 67502080, nat_lit 50724864, nat_lit 23622713856, nat_lit 6442844544, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 2432, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 158913789952, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 458752, nat_lit 25770197504, nat_lit 6442844544, nat_lit 25770066304, nat_lit 2147680640, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 24960, nat_lit 16768, nat_lit 6528, nat_lit 2147484032, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 158913789952, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 25690112, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 2432, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3190 : dRows3190.length = 4 ∧ fits 3190 dRows3190 = true ∧
    value 3190 dRows3190 = 559083761 :=
  dCheckRows_sound 3190 dRows3190 [138748011, 139530254, 139934828, 140870668] (by decide +kernel)

private def dRows3194 : List (List ℕ) := [
  [nat_lit 161061273600, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 458752, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 6528, nat_lit 2147484032, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 161061273600, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 2432, nat_lit 2147484032, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 161061273600, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 458752, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 4294967680, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 163208757248, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 30065164800, nat_lit 4295360896, nat_lit 25770066304, nat_lit 2147680640, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 2147484032, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3194 : dRows3194.length = 4 ∧ fits 3194 dRows3194 = true ∧
    value 3194 dRows3194 = 569946396 :=
  dCheckRows_sound 3194 dRows3194 [141204068, 142225914, 143029513, 143486901] (by decide +kernel)

private def dRows3198 : List (List ℕ) := [
  [nat_lit 163208757248, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 2173173760, nat_lit 30065164800, nat_lit 2147877248, nat_lit 27917549952, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 4294967680, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 165356240896, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 458752, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 4294967680, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 165356240896, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 30065164800, nat_lit 4295360896, nat_lit 25770066304, nat_lit 196992, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 6442451328, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 167503724544, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 458752, nat_lit 30065164800, nat_lit 2147877248, nat_lit 262656, nat_lit 25770066304, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 4294967680, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3198 : dRows3198.length = 4 ∧ fits 3198 dRows3198 = true ∧
    value 3198 dRows3198 = 580860862 :=
  dCheckRows_sound 3198 dRows3198 [144406018, 144700125, 145599828, 146154891] (by decide +kernel)

private def dRows3202 : List (List ℕ) := [
  [nat_lit 167503724544, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 32212648448, nat_lit 2147877248, nat_lit 25770066304, nat_lit 196992, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 6442451328, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 169651208192, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 30065164800, nat_lit 2147877248, nat_lit 262656, nat_lit 25770066304, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 6528, nat_lit 6442451328, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 169651208192, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 32212648448, nat_lit 2147877248, nat_lit 262656, nat_lit 25770066304, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 2432, nat_lit 6442451328, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 171798691840, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 32212648448, nat_lit 2147877248, nat_lit 262656, nat_lit 23622582656, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 6528, nat_lit 6442451328, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3202 : dRows3202.length = 4 ∧ fits 3202 dRows3202 = true ∧
    value 3202 dRows3202 = 591542798 :=
  dCheckRows_sound 3202 dRows3202 [147038068, 147478451, 148257426, 148768853] (by decide +kernel)

private def dRows3206 : List (List ℕ) := [
  [nat_lit 171798691840, nat_lit 10872160256, nat_lit 6543638528, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 2173173760, nat_lit 13107200, nat_lit 34360132096, nat_lit 393600, nat_lit 262656, nat_lit 25770066304, nat_lit 4295098752, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 2432, nat_lit 6442451328, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 173946175488, nat_lit 8724676608, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 8912896, nat_lit 32212648448, nat_lit 2147877248, nat_lit 262656, nat_lit 25770066304, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 6528, nat_lit 8589934976, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 173946175488, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 6815744, nat_lit 32212648448, nat_lit 393600, nat_lit 2147746304, nat_lit 23622582656, nat_lit 4295098752, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 16768, nat_lit 12672, nat_lit 2432, nat_lit 8589934976, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 173946175488, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 8912896, nat_lit 34360132096, nat_lit 393600, nat_lit 2147746304, nat_lit 23622582656, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 8589934976, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3206 : dRows3206.length = 4 ∧ fits 3206 dRows3206 = true ∧
    value 3206 dRows3206 = 602620127 :=
  dCheckRows_sound 3206 dRows3206 [149720308, 149986155, 151047748, 151865916] (by decide +kernel)

private def dRows3210 : List (List ℕ) := [
  [nat_lit 176093659136, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 4718592, nat_lit 34360132096, nat_lit 393600, nat_lit 262656, nat_lit 23622582656, nat_lit 4295098752, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 8589934976, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 176093659136, nat_lit 10872160256, nat_lit 6543638528, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 2173173760, nat_lit 13107200, nat_lit 6815744, nat_lit 34360132096, nat_lit 393600, nat_lit 2147746304, nat_lit 23622582656, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 10737418624, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 178241142784, nat_lit 8724676608, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 8912896, nat_lit 2621440, nat_lit 34360132096, nat_lit 393600, nat_lit 2147746304, nat_lit 21475099008, nat_lit 4295098752, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 10737418624, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 178241142784, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 4718592, nat_lit 524800, nat_lit 34360132096, nat_lit 4295229952, nat_lit 21475099008, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 10737418624, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]

private theorem dTotal3210 : dRows3210.length = 4 ∧ fits 3210 dRows3210 = true ∧
    value 3210 dRows3210 = 614063765 :=
  dCheckRows_sound 3210 dRows3210 [152336857, 153280828, 153771695, 154674385] (by decide +kernel)

/-- Certified factor products for grades 3162 through 3213. -/
def rowsD : List (List ℕ) :=
  dRows3162 ++
  dRows3166 ++
  dRows3170 ++
  dRows3174 ++
  dRows3178 ++
  dRows3182 ++
  dRows3186 ++
  dRows3190 ++
  dRows3194 ++
  dRows3198 ++
  dRows3202 ++
  dRows3206 ++
  dRows3210

theorem checkD :
    rowsD.length = 52 ∧ fits 3162 rowsD = true ∧
      value 3162 rowsD = 7141761347 :=
  dJoin dTotal3162 <|
  dJoin dTotal3166 <|
  dJoin dTotal3170 <|
  dJoin dTotal3174 <|
  dJoin dTotal3178 <|
  dJoin dTotal3182 <|
  dJoin dTotal3186 <|
  dJoin dTotal3190 <|
  dJoin dTotal3194 <|
  dJoin dTotal3198 <|
  dJoin dTotal3202 <|
  dJoin dTotal3206 <| dTotal3210

end K1_13_2_3_6
end PackSource_K1_13_2_3_6AuxD

section PackSource_K1_13_7_1Taylor
set_option autoImplicit true
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_7

local notation "W" => MvPolynomial.weightedTotalDegree

private theorem topPartial_bound (w : Fin 4 → ℕ) (P : Row 4) :
    W w (separant P) ≤ W w P - w 3 :=
  weightedTotalDegree_pderiv_le_sub w 3 P

private theorem pderiv_zero_of_weight_lt (w : Fin 4 → ℕ) (i : Fin 4) (P : Row 4)
    (h : W w P < w i) : pderiv i P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz : P.coeff (m + Finsupp.single i 1) = 0 := by
    by_contra hn
    have hm := le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add, Finsupp.weight_single, one_smul] at hm
    omega
  simp [hz]

private theorem weight_coeff_deriv (w : Fin 4 → ℕ) (P : Row 4) :
    W w (coefficientDerivative P) ≤ W w P := by
  classical
  apply weight_le_of_support_subset
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj

private theorem partialFlow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    (P : Row 4) {d : ℕ} (hP : W w P ≤ d) : W w (partialFlow P) ≤ d + Δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_coeff_deriv w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (weight_const_mul_le w _ _).trans
    by_cases h : w i.castSucc ≤ d
    · have hp := (weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he := hshift i
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (weight_X_le w _) hp).trans (by omega))
    · rw [pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)), mul_zero,
        weightedTotalDegree_zero]
      exact Nat.zero_le _

private theorem flow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) :
    W w (flowNumerator g P) ≤ d + (B - w 3) + Δ := by
  have hsep := (topPartial_bound w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (partialFlow_bound w Δ hshift P hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    by_cases h : w 3 ≤ d
    · have hp := (topPartial_bound w P).trans (Nat.sub_le_sub_right hP (w 3))
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (partialFlow_bound w Δ hshift g hg) hp).trans (by omega))
    · rw [separant, pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
        mul_zero, weightedTotalDegree_zero]
      exact Nat.zero_le _

private theorem step_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) (a : ℕ) :
    W w (clearedStep g a P) ≤ d + (2 * (B - w 3) + Δ) := by
  have hsep := (topPartial_bound w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (flow_bound w Δ hshift hB hg hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    apply (weightedTotalDegree_mul_le _ _ _).trans
    rw [← map_natCast (MvPolynomial.C : Geom[X] →+* Row 4)]
    exact (Nat.add_le_add ((weight_const_mul_le _ _ _).trans (flow_bound w Δ hshift hB hg hsep))
      hP).trans (by omega)

private theorem jet_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) {g : Row 4} {B : ℕ}
    (hB : w 3 ≤ B) (hg : W w g ≤ B) (n : ℕ) :
    W w (jetNumerator g n) ≤ w 0 + n * (2 * (B - w 3) + Δ) := by
  induction n with
  | zero => simpa only [jetNumerator, zero_mul, add_zero] using weight_X_le (R := Geom[X]) w 0
  | succ n ih =>
    simpa only [jetNumerator, Nat.add_mul, one_mul, Nat.add_assoc] using
      step_bound w Δ hshift hB hg ih (2 * n)

private def denominator (L : ℕ) (g : Row 4) : Row 4 :=
  separant g ^ (2 * L)

private def numerator (L : ℕ) (g : Row 4) (i : TaylorIndex) : Row 4 :=
  if hi : i.val < 4 then MvPolynomial.X ⟨i.val, hi⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑i.val.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - i.val)) * jetNumerator g i.val)

private def taylorChart (L : ℕ) (g : Row 4) : TaylorChart where
  denom := toGeneric (denominator L g)
  numerator i := toGeneric (numerator L g i)
  initial i := by
    unfold numerator toGeneric
    have hi : (i.castLE (by decide : 4 ≤ taylorLength)).val < 4 := i.isLt
    rw [dite_eq_left hi, map_mul, MvPolynomial.map_X]
    rfl

private theorem denominator_bound (L : ℕ) (w : Fin 4 → ℕ) {g : Row 4} {B : ℕ} (hg : W w g ≤ B) :
    W w (denominator L g) ≤ 2 * L * (B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans
    (Nat.mul_le_mul_left _ ((topPartial_bound w g).trans (Nat.sub_le_sub_right hg _)))

private theorem numerator_bound {L : ℕ} (hL : taylorLength ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (i : TaylorIndex) :
    W w (numerator L g i) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  have hi : i.val ≤ L := i.isLt.le.trans hL
  unfold numerator
  split_ifs with hinit
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (denominator_bound L w hg)).trans
        (Nat.le_add_right _ _))
  · have hp := (weightedTotalDegree_pow_le w (separant g) (2 * (L - i.val))).trans
      (Nat.mul_le_mul_left _ ((topPartial_bound w g).trans (Nat.sub_le_sub_right hg _)))
    apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - i.val) * (B - w 3) + (w 0 + i.val * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add hp (jet_bound w Δ hshift hB hg i.val)
      _ = w 0 + 2 * (i.val + (L - i.val)) * (B - w 3) + i.val * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hi]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hi)

private theorem chart_box {L : ℕ} (hL : taylorLength ≤ L) (g : Row 4) (p : Shape) (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t) :
    (taylorChart L g).Fits (chart L p) := by
  have hb : 1 ≤ p.b := by have := hp.1; have := hp.2; omega
  have hj : 3 ≤ p.j := by have := hp.2; omega
  have h₁ : W 1 g ≤ p.b := by simpa only [shape, weightedTotalDegree_one] using hB.1
  have h₂ : W Fin.val g ≤ p.j := by simpa only [shape, indexDegree_eq] using hB.2.1
  let w : Fin 4 → ℕ := Pi.single 3 1
  have h₃ : W w g ≤ p.t := by simpa only [w, shape, weightedTotalDegree_piSingle] using hB.2.2
  have hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i, w i ≤ 1 := by
    intro i
    fin_cases i <;> decide
  have hw3 : w 3 = 1 := by decide
  have pkg (P : Row 4) (hb' : W 1 P ≤ 1 + 2 * L * (p.b - 1))
      (hj' : W Fin.val P ≤ 2 * L * (p.j - 3) + L + 3)
      (ht' : W w P ≤ 2 * L * (p.t - 1) + L + 1) :
      GeoFits (toGeneric P) (chart L p) := by
    apply toGeneric_fits
    refine ⟨?_, ?_, ?_⟩
    · change P.totalDegree ≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree ≤ 1 + 2 * L * (p.b - 1)).trans (le_max_left _ _)
    · change indexDegree P ≤ _
      rwa [indexDegree_eq]
    · change P.degreeOf 3 ≤ min _ _
      apply le_min
      · simpa only [w, weightedTotalDegree_piSingle] using ht'
      · have h := (top_le_index P).trans hj'
        omega
  constructor
  · apply pkg
    · exact (denominator_bound L _ h₁).trans (Nat.le_add_left _ _)
    · exact (denominator_bound L _ h₂).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    · have h := denominator_bound L w h₃
      rw [hw3] at h
      exact h.trans (by omega)
  · intro i
    apply pkg
    · have h := numerator_bound hL 1 0 1 (fun _ => by simp) (fun _ => le_rfl) hb h₁ i
      change W 1 (numerator L g i) ≤ 1 + 2 * L * (p.b - 1) + L * 0 at h
      simpa only [mul_zero, add_zero] using h
    · have h := numerator_bound hL Fin.val 1 3 (fun _ => by rfl)
        (fun j : Fin 4 => Nat.le_of_lt_succ j.isLt) hj h₂ i
      change W Fin.val (numerator L g i) ≤ 3 + 2 * L * (p.j - 3) + L * 1 at h
      simpa only [mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
    · have hwle : w 3 ≤ p.t := hw3.symm ▸ ht
      have h := numerator_bound hL w 1 1 hshift hw hwle h₃ i
      simpa only [hw3, mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h

private theorem ordinary_eq_hasse (S : Geom[X]) (n : ℕ) :
    derivative^[n] S = Polynomial.C (n.factorial : Geom) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]

theorem evalGeneric_toGeneric (S : Geom[X]) (P : Row 4) :
    evalGeneric S (toGeneric P) = genericCoeffs (atJet P S) := by
  exact (MvPolynomial.map_eval genericCoeffs (jet S) P).symm

private theorem chart_recovers {L : ℕ} (hL : taylorLength ≤ L) (g : Row 4) (S : Geom[X])
    (hg : atJet g S = 0) (hr : RegularAt g S) : (taylorChart L g).Recovers S := by
  have hp : atJet (separant g) S ≠ 0 := hr
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → Geom[X])) _ _
  constructor
  · change evalGeneric S (toGeneric (denominator L g)) ≠ 0
    rw [evalGeneric_toGeneric]
    apply (map_ne_zero_iff _ genericCoeffs_injective).mpr
    rw [hden]
    exact pow_ne_zero _ hp
  · intro i
    change evalGeneric S (toGeneric (numerator L g i)) =
      evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv i.val S)
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - i.val)) *
        atJet (jetNumerator g i.val) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero
          (i.isLt.trans (by decide : taylorLength < K1.p))), map_one]
      have hpow : 2 * (L - i.val) + 2 * i.val = 2 * L := by
        have hi : i.val ≤ L := i.isLt.le.trans hL
        rw [← Nat.mul_add, Nat.sub_add_cancel hi]
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - i.val)) * atJet (separant g) S ^ (2 * i.val)) *
              hasseDeriv i.val S) := by ring
        _ = _ := by
          rw [hinv, one_mul, ← pow_add, hpow, hden]

/-- The common denominator and all Taylor-coordinate numerators fit the same box. -/
theorem exists_chart (g : Row 4) (p : Shape) (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t) :
    ∃ C : TaylorChart, C.Fits (chart (taylorLength + 4) p) ∧
      ∀ S : Geom[X], atJet g S = 0 → RegularAt g S → C.Recovers S :=
  ⟨taylorChart (taylorLength + 4) g, chart_box (Nat.le_add_right _ _) g p hB hp ht,
    chart_recovers (Nat.le_add_right _ _) g⟩

end
end K1_13_7_1
end PackSource_K1_13_7_1Taylor

section PackSource_K1_13_7_4_2Defs
set_option autoImplicit true
namespace K1_13_7_4_2

open K1_13_7

/-- The ambient local ring at a geometric prime. -/
abbrev Local (q : PrimeSpectrum Lower) := Localization.AtPrime q.asIdeal

/-- The ideal generated by the entries other than the distinguished one. -/
def remainingIdeal {R ι : Type*} [CommRing R] (f : ι → R) (i : ι) : Ideal R :=
  Ideal.span (f '' {j | j ≠ i})

end K1_13_7_4_2
end PackSource_K1_13_7_4_2Defs

section PackSource_K1_13_5_4_4Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_4

noncomputable section

open K1_13 K1_13_5 K1_13_5_4
open scoped Polynomial

/-- The old geometric field is a field of constants for the new argument. -/
abbrev FreshField := FractionRing GeometricX[X]
abbrev FreshJetRing := MvPolynomial (Fin 3) FreshField
abbrev FreshCoeffRing := MvPolynomial (Fin taylorLength) FreshField
abbrev FreshJetIdeal := Ideal FreshJetRing

def freshArgument : FreshField := algebraMap GeometricX[X] FreshField Polynomial.X

def freshCoeff : Geom[X] →+* FreshField :=
  (algebraMap GeometricX[X] FreshField).comp
    (Polynomial.mapRingHom (algebraMap Geom GeometricX))

def freshRow (g : Row 3) : FreshJetRing := MvPolynomial.map freshCoeff g

def freshHypersurface (f : Row 3) : FreshJetIdeal := Ideal.span {freshRow f}

def freshDivisor (f : Row 3) : FreshJetIdeal :=
  freshHypersurface f ⊔ Ideal.span {freshRow (oldCut f)}

def extendIdeal (Q : CoefficientIdeal) : Ideal FreshCoeffRing :=
  Q.map (MvPolynomial.map (algebraMap GeometricX FreshField))

def freshProjection : FreshJetRing →ₐ[FreshField] FreshCoeffRing :=
  MvPolynomial.aeval fun j => K1_13_5_5.jetForm freshArgument j.val

def freshImage (Q : CoefficientIdeal) : FreshJetIdeal := (extendIdeal Q).comap freshProjection

/-- Each coefficient lies in the fraction field of the projected coordinate ring.
The denominator must survive modulo the curve ideal. -/
def FreshBirational (Q : CoefficientIdeal) : Prop :=
  ∀ j : Fin taylorLength, ∃ u v : FreshJetRing,
    v ∉ freshImage Q ∧
      freshProjection v * MvPolynomial.X j - freshProjection u ∈ extendIdeal Q

structure FreshChart (f : Row 3) (Q : CoefficientIdeal) : Prop where
  extended_prime : (extendIdeal Q).IsPrime
  on_divisor : freshDivisor f ≤ freshImage Q
  regular : freshRow (separant f) ∉ freshImage Q
  birational : FreshBirational Q

end
end K1_13_5_4_4
end PackSource_K1_13_5_4_4Defs

section PackSource_K1_13_7_2_1Defs
set_option autoImplicit true
namespace K1_13_7_2_1

open K1_13 K1_13_6 K1_13_7_2

/-- At the generic point of a regular lift the two equations generate its maximal ideal. -/
def LocalGenerators (f : Row 4) (q : Row 3) (surface : Ideal GeoJets)
    (hp : surface.IsPrime) : Prop :=
  letI := hp
  let A := Localization.AtPrime surface
  (intersectionIdeal f (liftLower q)).map (algebraMap GeoJets A) = IsLocalRing.maximalIdeal A

end K1_13_7_2_1
end PackSource_K1_13_7_2_1Defs
