import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.Fast057
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option maxHeartbeats 450000
def bbPack : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + 65536 * bbPack n (fun i => f (i+1))
theorem bbAdd (n : ℕ) (f g : ℕ → ℕ) :
    bbPack n (fun i => f i + g i) = bbPack n f + bbPack n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [bbPack, ih, Nat.mul_add]
    omega
theorem bbScale (n k : ℕ) (f : ℕ → ℕ) :
    bbPack n (fun i => k * f i) = k * bbPack n f := by
  induction n generalizing f with
  | zero => simp [bbPack]
  | succ n ih =>
    simp only [bbPack, ih]
    ring
theorem bbConst (n k : ℕ) :
    bbPack n (fun _ => k) = k * bbPack n (fun _ => 1) := by
  simpa using bbScale n k (fun _ => 1)
theorem bbSub (n : ℕ) (f g : ℕ → ℕ) (h : ∀ i, g i ≤ f i) :
    bbPack n (fun i => f i - g i) = bbPack n f - bbPack n g := by
  apply Nat.eq_sub_of_add_eq
  rw [← bbAdd]
  exact congrArg (bbPack n) (funext fun i => Nat.sub_add_cancel (h i))
theorem bbAndCons (x y a b : ℕ) (hx : x < 65536) (hy : y < 65536) :
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
theorem bbAnd (n : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ i, f i < 65536) (hg : ∀ i, g i < 65536) :
    bbPack n (fun i => f i &&& g i) = bbPack n f &&& bbPack n g := by
  induction n generalizing f g with
  | zero => simp [bbPack]
  | succ n ih =>
    simp only [bbPack]
    rw [bbAndCons _ _ _ _ (hf 0) (hg 0), ← ih]
    all_goals first | rfl | exact fun i => hf (i+1) | exact fun i => hg (i+1)
theorem bbLow (n k : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i < 65536) (hk : 2^k ≤ 65536) :
    bbPack n (fun i => f i % 2^k) =
      bbPack n f &&& ((2^k-1) * bbPack n (fun _ => 1)) := by
  rw [← bbConst, ← bbAnd n f (fun _ => 2^k-1) hf (by intro; omega)]
  simp [Nat.and_two_pow_sub_one_eq_mod]
def bbShr (u z k : ℕ) := (z - (z &&& ((2^k-1)*u))) / 2^k
theorem bbShr_eq (n k : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i < 65536) (hk : 2^k ≤ 65536) :
    bbPack n (fun i => f i / 2^k) = bbShr (bbPack n (fun _ => 1)) (bbPack n f) k := by
  unfold bbShr
  rw [← bbLow n k f hf hk, ← bbSub n f _ (fun i => Nat.mod_le _ _)]
  have he : (fun i => f i - f i % 2^k) = (fun i => 2^k * (f i / 2^k)) := by
    funext i
    have := Nat.mod_add_div (f i) (2^k)
    omega
  rw [he, bbScale, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
def bbMonus (u x y : ℕ) : ℕ :=
  let biased := 32768*u + x - y
  let low := biased &&& (32767*u)
  low &&& (32767*((biased-low) >>> 15))
theorem bbMonus_eq (n : ℕ) (f g : ℕ → ℕ)
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
def bbMin (u x y : ℕ) := x - bbMonus u x y
theorem bbMin_eq (n : ℕ) (f g : ℕ → ℕ)
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
theorem bbSumPack (n m : ℕ) (f : ℕ → ℕ → ℕ) :
    bbPack n (fun r => sumRange m (fun i => f i r)) =
      sumRange m (fun i => bbPack n (f i)) := by
  induction m with
  | zero =>
    change bbPack n (fun _ => 0) = 0
    simpa using bbConst n 0
  | succ m ih => simp only [sumRange_succ, bbAdd, ih]
theorem bbSumBound (n : ℕ) (f g : ℕ → ℕ) (h : ∀ i, f i ≤ g i) :
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
def bbOnes : ℕ := 0x100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001
theorem bbOnes_ok : bbPack 138 (fun _ => 1) = bbOnes := by decide +kernel
def bbSmaller (x y : BBVec) : BBVec where
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
def bbKnownMeet (x y : BBVec) (hx : x.limit < 32768) (hy : y.limit < 32768) : BBVec where
  atOffset i := min (x.atOffset i) (y.atOffset i)
  word := bbMin bbOnes x.word y.word
  limit := min x.limit y.limit
  correct := by
    rw [bbMin_eq 138 _ _ (fun i => (x.bound i).trans_lt hx) (fun i => (y.bound i).trans_lt hy),
      x.correct, y.correct, bbOnes_ok]
  bound i := min_le_min (x.bound i) (y.bound i)
theorem bbSumConst (n cap : ℕ) : sumRange n (fun _ => cap) = n*cap := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange_succ, ih, Nat.succ_mul]
def bbSum (n cap : ℕ) (f : ℕ → BBVec) (h : ∀ i, (f i).limit ≤ cap) : BBVec where
  atOffset r := sumRange n (fun i => (f i).atOffset r)
  word := sumRange n (fun i => (f i).word)
  limit := n*cap
  correct := by rw [bbSumPack]; exact sumRange_congr _ (fun i _ => (f i).correct)
  bound r := (bbSumBound _ _ (fun _ => cap) (fun i => ((f i).bound r).trans (h i))).trans_eq
    (bbSumConst n cap)
theorem bbLastZero (n : ℕ) (f : ℕ → ℕ) (h : f n = 0) :
    bbPack (n+1) f = bbPack n f := by
  induction n generalizing f with
  | zero => simp [bbPack, h]
  | succ n ih =>
    change f 0 + 65536 * bbPack (n+1) (fun i => f (i+1)) =
      f 0 + 65536 * bbPack n (fun i => f (i+1))
    rw [ih _ h]
theorem bbDropOne (n : ℕ) (f : ℕ → ℕ) (h0 : f 0 < 65536) (h : f n = 0) :
    bbPack n f / 65536 = bbPack n (fun i => f (i+1)) := by
  conv_lhs => rw [← bbLastZero n f h]
  change (f 0 + 65536 * bbPack n _) / 65536 = _
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt h0, Nat.zero_add]
theorem bbTranslated (n : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i < 65536)
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
def bbSlope (k : ℕ) (f : ℕ → ℕ) (cap value : ℕ)
    (hc : cap < 65536) (hf : ∀ i, f i ≤ cap) (hz : ∀ i, 138 ≤ i → f i = 0)
    (hw : bbPack 138 f = value) : BBVec where
  atOffset i := f (k+i)
  word := value >>> (16*k)
  limit := cap
  correct := (bbTranslated 138 f (fun i => (hf i).trans_lt hc) hz k).trans
    ((congrArg (· / 65536^k) hw).trans (by rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]))
  bound i := hf (k+i)
def bbOrder (k : ℕ) : BBVec :=
  bbSlope k (fun i => 138-i) 138 0x100020003000400050006000700080009000a000b000c000d000e000f0010001100120013001400150016001700180019001a001b001c001d001e001f0020002100220023002400250026002700280029002a002b002c002d002e002f0030003100320033003400350036003700380039003a003b003c003d003e003f0040004100420043004400450046004700480049004a004b004c004d004e004f0050005100520053005400550056005700580059005a005b005c005d005e005f0060006100620063006400650066006700680069006a006b006c006d006e006f0070007100720073007400750076007700780079007a007b007c007d007e007f0080008100820083008400850086008700880089008a
    (by decide) (fun _ => Nat.sub_le ..) (by intros; omega) (by decide +kernel)
def bbThird (k : ℕ) : BBVec :=
  bbSlope k (fun i => (48-i+2)/3) 16 0x100010001000200020002000300030003000400040004000500050005000600060006000700070007000800080008000900090009000a000a000a000b000b000b000c000c000c000d000d000d000e000e000e000f000f000f001000100010
    (by decide) (by intro i; omega) (by intros; omega) (by decide +kernel)
def bbHalf (k : ℕ) : BBVec :=
  bbSlope k (fun i => (48-i+1)/2) 24 0x100010002000200030003000400040005000500060006000700070008000800090009000a000a000b000b000c000c000d000d000e000e000f000f001000100011001100120012001300130014001400150015001600160017001700180018
    (by decide) (by intro i; omega) (by intros; omega) (by decide +kernel)
def bbFlip (cap : ℕ) (x tail : BBVec)
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
def bbFlipThird (k cap : ℕ) : BBVec :=
  bbFlip cap (bbThird k) (bbThird (k+3*cap)) (by
    intro i
    change (48-(k+3*cap+i)+2)/3 = (48-(k+i)+2)/3-cap
    omega)
def bbFlipHalf (k cap : ℕ) : BBVec :=
  bbFlip cap (bbHalf k) (bbHalf (k+2*cap)) (by
    intro i
    change (48-(k+2*cap+i)+1)/2 = (48-(k+i)+1)/2-cap
    omega)
def bbLine (s b c : ℕ) : BBVec :=
  let t := s-b
  bbKnownMeet (bbFlipThird (b+2*min c 24) (min (min s 10 + 1) (t-c+1)))
    (bbOrder (s+2*t-c))
    (by change min (min s 10 + 1) (t-c+1) < 32768; omega)
    (by exact (by decide : 138 < 32768))
theorem bbWindow (t c o : ℕ) (hc : c ≤ t) :
    t-c+1 - (3*t+1-(2*c+o)) = min (t-c+1) (o+c-2*t) := by omega
theorem bbWindowShift (s r t c : ℕ) (hc : c ≤ t) :
    138-(s+2*t-c+r) = (138-(s+r))+c-2*t := by omega
theorem bbWindowBase (s b e : ℕ) (hb : b ≤ s) :
    3*s+1-(3*b+e) = 3*(s-b)+1-e := by omega
theorem bbLineMeet (a h u v z : ℕ) (hv : h-v = min h z) :
    min (min a h-u) z = min (a-u) (h-max u v) := by
  rw [← Nat.sub_min_sub_right, ← Nat.sub_min_sub_left, hv, Nat.min_assoc (a-u) (h-u) z,
    ← Nat.min_assoc (h-u) h z, Nat.min_eq_left (Nat.sub_le h u)]
theorem bbLine_val (s b c r : ℕ) (hb : b ≤ s) (hc : c ≤ s-b) :
    (bbLine s b c).atOffset r = natLine s (48-r) (138-(s+r)) b c := by
  change min (min (min s 10+1) (s-b-c+1) - ((48-((b+2*min c 24)+r)+2)/3))
    (138-((s+2*(s-b)-c)+r)) = _
  unfold natLine
  dsimp only
  rw [Nat.sub_sub 48 r _, Nat.add_comm (b+2*min c 24) r, bbWindowShift _ _ _ _ hc,
    Nat.add_assoc (3*b), bbWindowBase _ _ _ hb]
  exact bbLineMeet _ _ _ _ _ (bbWindow _ _ _ hc)
def bbPairs (s b : ℕ) : BBVec :=
  bbSum (min s 10+1) 25 (fun f =>
    bbFlipHalf (b+3*f) (min (s-f) ((48-3*f)/2)+1)) (by
    intro f
    change min (s-f) ((48-3*f)/2)+1 ≤ 25
    omega)
theorem bbPairs_val (s b r : ℕ) :
    (bbPairs s b).atOffset r = natPairs s (48-r) b := by
  change sumRange (min s 10+1) (fun f => (min (s-f) ((48-3*f)/2)+1) - ((48-(b+3*f+r)+1)/2)) =
    sumRange (min s 10+1) _
  apply sumRange_congr
  intro f _
  rw [show 48-(b+3*f+r) = 48-r-(b+3*f) by omega]
def bbSlice (s b : ℕ) : BBVec :=
  bbSmaller (bbPairs s b) (bbSum (s-b+1) 11 (bbLine s b) (by
    intro c
    change min (min (min s 10+1) (s-b-c+1)) 138 ≤ 11
    exact (Nat.min_le_left ..).trans ((Nat.min_le_left ..).trans (Nat.succ_le_succ (Nat.min_le_right ..)))))
def bbCappedRamp (k m : ℕ) : BBVec where
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
def bbCell (s f c : ℕ) : BBVec :=
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
theorem bbTruncLow (m hi lo : ℕ) (h : lo ≤ hi) :
    min m hi - min m lo = min m hi - lo := by omega
theorem bbCell_val (s f c r : ℕ) (hr : r < 138) :
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
def bbActive (s : ℕ) : BBVec :=
  bbSum (min s 10+1) 1225 (fun f =>
    bbSum (min (s-f) ((48-3*f)/2)+1) 49 (bbCell s f) (fun _ => (Nat.min_le_right ..).trans (Nat.sub_le ..))) (by
      intro f
      change (min (s-f) ((48-3*f)/2)+1)*49 ≤ 1225
      omega)
theorem bbCellInside (a hi base lo : ℕ) (h : base ≤ hi) :
    min (a+1) (hi+1-base) - (lo-base) = (min a (hi-base)+1) - (lo-base) := by
  rw [Nat.succ_sub h, Nat.succ_min_succ]
theorem bbCellOutside (a hi base lo : ℕ) (h : hi < base) :
    min a (hi+1-base) - (lo-base) = 0 := by simp [Nat.sub_eq_zero_of_le h]
theorem bbInC (hi f c : ℕ) (hf : f ≤ hi/3) (hc : c ≤ (hi-3*f)/2) :
    2*c+3*f ≤ hi := by omega
theorem bbPastC (t hi f c : ℕ) (h : min t ((hi-3*f)/2) < c) (hc : c ≤ t) :
    hi < 2*c+3*f := by omega
theorem bbPastF (t hi f c : ℕ) (h : min t (hi/3) < f) (hf : f ≤ t) :
    hi < 2*c+3*f := by omega
theorem bbActive_val (s r : ℕ) (hr : r < 138) :
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
def bbBlock (s : ℕ) : BBVec :=
  bbSmaller (bbActive s) (bbSum (s+1) 275 (bbSlice s) (by
    intro b
    apply (Nat.min_le_left ..).trans
    change (min s 10+1)*25 ≤ 275
    omega))
theorem bbBC (s b c : ℕ) (hb : b < s+1) (hc : c < s-b+1) : b+c ≤ s := by omega
theorem bbLate (s r b c : ℕ) (hr : ¬ s+r < 138) (hc : c < s-b+1) :
    138-((s+2*(s-b)-c)+r) = 0 := by omega
theorem bbBlock_val (s r : ℕ) (hs : residualDegree s = s)
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
def bbDigits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, z => z%65536 + bbDigits n (z/65536)
theorem bbDigits_eq (n : ℕ) (f : ℕ → ℕ) (h : ∀ i, f i < 65536) :
    bbDigits n (bbPack n f) = sumRange n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [bbDigits, bbPack, sumRange_succ_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (h 0), Nat.add_mul_div_left _ _ (by decide : 0 < 65536),
      Nat.div_eq_of_lt (h 0), Nat.zero_add]
    rw [ih _ (fun i => h (i+1))]
theorem bbGrade (s ans : ℕ) (hs : residualDegree s = s)
    (hn : ∀ g, selectedFactors s g = none) (hlim : (bbBlock s).limit < 65536)
    (hnum : bbDigits 138 (bbBlock s).word = ans) :
    fastGrade s = ans := by
  unfold fastGrade
  rw [sumRange_congr 138 (fun r _ => (bbBlock_val s r hs (hn _)).symm)]
  rw [← bbDigits_eq 138 _ (fun i => ((bbBlock s).bound i).trans_lt hlim), (bbBlock s).correct, hnum]
theorem bbWord20 : (bbBlock 20).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019501c701fb0232026a02a402df031b0357039403d0040c0446047f04b504e905190546056e059205b005c905dd05ed05f906020608060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060c060b060a06080605060105fc05f505ed05e305d705c905b905a605910579055e0540051f04fa04d204a604770445041103da03a20368032d02f102b50278023c020001c6018d0157012300f300c6009e007a005c0043002f001f0013000a0004 := by decide +kernel
theorem bbWord21 : (bbBlock 21).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601c901ff0238027302b002ef032f037003b203f40436047704b704f50531056a05a005d206000629064d066b0684069806a806b406bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bd06bc06bb06b906b606b206ad06a6069e06940688067a066a06570642062a060f05f105d005ab05830557052704f404be0485044a040d03ce038e034d030b02c902870246020601c8018c0153011d00eb00bd0094007000520039002500150009 := by decide +kernel
theorem bbWord22 : (bbBlock 22).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0201023c027902b902fb033f038403cb0412045a04a104e8052d057105b205f1062c0664069706c606ef07130731074a075e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076e076d076c076a07670763075e0757074f07450739072b071b070806f306db06c006a20681065c0634060805d805a4056d053204f504b50473042f03ea03a3035c031402cd0286024101fd01bc017d0142010a00d700a8007f005b003d00240010 := by decide +kernel
theorem bbWord23 : (bbBlock 23).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023e027d02bf0304034b039403df042b047804c50512055e05a905f20639067d06be06fb07340768079707c007e40802081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081a0819081708140810080b080407fc07f207e607d807c807b507a00788076d074f072e070906e106b506850651061905dd059e055c051704d00487043c03f003a30356030902bd0272022901e2019e015d012000e700b30084005b00370019 := by decide +kernel
theorem bbWord24 : (bbBlock 24).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f027f02c3030a035403a003ef043f049104e30536058805da062a067906c5070f0755079807d6081008440873089c08c008c008c008c008c008c008c008c008c008c008c008c008c008c008c008c008c008c008bf08be08bc08b908b508b008a908a10897088b087d086d085a0845082d081207f407d307ae0786075a072a06f606be0681064105fd05b6056c052004d10481042f03dd038a033802e60296024701fb01b1016b012800ea00b0007c004d0024 := by decide +kernel
theorem bbWord25 : (bbBlock 25).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c5030e035a03a903fb044f04a504fc055405ac0604065b06b10705075707a607f2083a087e08bd08f7092b095a095a095a095a095a095a095a095a095a095a095a095a095a095a095a095a095a0959095809560953094f094a0943093b093109250917090708f408df08c708ac088e086d0848082007f407c407900758071b06da0695064c060005b1055f050b04b5045e040603ae035602ff02a90255020301b40168012000dc009d0063002f := by decide +kernel
theorem bbWord26 : (bbBlock 26).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60310035e03af0404045b04b50510056d05ca0628068506e2073d079707ee0843089408e2092b097009af09e909e909e909e909e909e909e909e909e909e909e909e909e909e909e909e909e809e709e509e209de09d909d209ca09c009b409a609960983096e0956093b091d08fc08d708af08830853081f07e707aa0769072306d9068b063a05e5058e053404d9047c041f03c10364030702ac025201fb01a60155010700be0079003a := by decide +kernel
theorem bbWord27 : (bbBlock 27).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036003b3040a046404c10520058105e3064606a9070c076e07cf082e088b08e5093c098f09de0a280a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6d0a6c0a6b0a690a660a620a5d0a560a4e0a440a380a2a0a1a0a0709f209da09bf09a10980095b0933090708d708a3086b082e07ed07a7075c070d06ba0663060905ac054d04ec048a042703c4036102ff029e023f01e20188013100de008f0045 := by decide +kernel
theorem bbWord28 : (bbBlock 28).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b5040e046a04ca052c059105f7065f06c7073007980800086608cb092d098d09e90a420a960ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae60ae50ae40ae20adf0adb0ad60acf0ac70abd0ab10aa30a930a800a6b0a530a380a1a09f909d409ac09800950091c08e408a70866082007d50785073106d8067c061c05ba055504ef0487041f03b6034e02e60280021b01b9015900fd00a40050 := by decide +kernel
theorem bbWord29 : (bbBlock 29).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60410046e04d00535059d0607067306e0074e07bc082a08970903096d09d50a3a0a9c0afa0b540b540b540b540b540b540b540b540b540b540b540b540b540b530b520b500b4d0b490b440b3d0b350b2b0b1f0b110b010aee0ad90ac10aa60a880a670a420a1a09ee09be098a0952091508d4088e084307f3079e074406e60684061f05b7054d04e1047404060398032a02bd025101e7017f011a00b8005a := by decide +kernel
theorem bbWord30 : (bbBlock 30).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047004d4053b05a60613068306f4076707da084e08c1093409a50a150a820aed0b540bb80bb80bb80bb80bb80bb80bb80bb80bb80bb80bb80bb80bb70bb60bb40bb10bad0ba80ba10b990b8f0b830b750b650b520b3d0b250b0a0aec0acb0aa60a7e0a520a2209ee09b60979093808f208a70857080207a7074806e4067d061205a5053504c4045103de036a02f70284021301a3013600cb0064 := by decide +kernel
theorem bbWord31 : (bbBlock 31).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d6053f05ac061c068f0704077b07f3086c08e5095e09d60a4d0ac20b350ba50c120c120c120c120c120c120c120c120c120c120c120c110c100c0e0c0b0c070c020bfb0bf30be90bdd0bcf0bbf0bac0b970b7f0b640b460b250b000ad80aac0a7c0a480a1009d30992094c090108b1085c080107a1073c06d3066605f60583050e0497041f03a6032d02b4023c01c5015000dd006d := by decide +kernel
theorem bbWord32 : (bbBlock 32).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d7054105b0062206980710078b08070885090309820a000a7e0afa0b750bed0c630c630c630c630c630c630c630c630c630c630c620c610c5f0c5c0c580c530c4c0c440c3a0c2e0c200c100bfd0be80bd00bb50b970b760b510b290afd0acd0a990a610a2409e3099d0952090208ad085207f2078c072206b3064105cb055304d8045c03de036002e1026301e5016900ee0076 := by decide +kernel
theorem bbWord33 : (bbBlock 33).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d7054205b20626069e0719079708170899091c09a00a240aa80b2b0bad0c2d0cab0cab0cab0cab0cab0cab0cab0cab0cab0caa0ca90ca70ca40ca00c9b0c940c8c0c820c760c680c580c450c300c180bfd0bdf0bbe0b990b710b450b150ae10aa90a6c0a2b09e5099a094a08f5089a083a07d4076906f90685060d0592051404940412038f030b02870203018000fe007e := by decide +kernel
theorem bbWord34 : (bbBlock 34).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d7054205b3062806a2071f07a0082308a9093009b90a420acc0b550bde0c650ceb0ceb0ceb0ceb0ceb0ceb0ceb0ceb0cea0ce90ce70ce40ce00cdb0cd40ccc0cc20cb60ca80c980c850c700c580c3d0c1f0bfe0bd90bb10b850b550b210ae90aac0a6b0a2509da098a093508da087a081407a9073806c3064905cc054b04c8044203bb033202a9021f0196010d0086 := by decide +kernel
theorem bbWord35 : (bbBlock 35).word = 0x1000200040007000b00100017001f00290035004300530066007b009300ae00cc00ed0112013a0166019601ca0202023f028002c60311036103b60411047104d7054205b3062906a4072307a6082c08b5094009cd0a5b0aea0b790c080c960d230d230d230d230d230d230d230d220d210d1f0d1c0d180d130d0c0d040cfa0cee0ce00cd00cbd0ca80c900c750c570c360c110be90bbd0b8d0b590b210ae40aa30a5d0a1209c2096d091208b2084c07e1077006fa067f0600057d04f7046e03e3035602c8023901aa011b008d := by decide +kernel
private theorem sumStep (f : ℕ → ℕ) (n a b : ℕ)
    (ha : sumRange n f = a) (hb : f n = b) :
    sumRange (n + 1) f = a + b :=
  (show sumRange (n + 1) f = sumRange n f + f n from rfl).trans (congrArg₂ Nat.add ha hb)
private def gradeFrom (i : ℕ) : ℕ := fastGrade (i + 20)
end K1_13_1_1
end
section
namespace K1_13_2_3_5
namespace DataC2344
open K1_13_2_3
open private rowLoop rowScore unpack from ProximityPrize.SubmissionLower.Numeric5Certificate
set_option maxHeartbeats 3000000
set_option maxRecDepth 50000
def cDenTable : Nat := 0xef84cf5de2b417ba9a52771bd56edc8e37dab47cfb3aeef763eadbec0f1d7d742037accc20f562987ea577bfd3d3d23a5f1e1f48794fe8a1fd9d069e6b9f202cf3ada28e6eea11cd043e39856fc72d4c08e53d651c9a2d5f91964b71fcee4e38e483c645ab78ade1471262b1e1e1493c2ecbbf842e51f050765e03666bbf9804b7d86feef7bcf5de8d9f5bc4783376e815eea8356dce6f1db8fb34b7051916dd5a7edb425cdb5b316769c36c6d04262d99fdefb26f25f633da16c33af7d7ff76faf2f6075cc02aeb64433d661237abf3c33564b03ea95e0bd4c4e31a8bc4bb4fde26e9c8874d32ab49a588f7349798e68fc364d192969a259c2f431d356830ed0cffc87b9f2eac73cc9166766aadce6886b9c07b0f367d2be69d6f1ccd692398e4cdb303970e5d5391cb46a8d95c600329fddfe50e082c9b8c9592ab45b23ca736447dbac82cf258f949b71d9f266382b2ec6a32278c81fef177bf362be8d3c51b58789736d71160d4e1fb69fc39592f8668e430b4dc5e139487c211d09836260b0542c0e078280c090101805fe02ff3fc05fb8080bf105017d615fef944bf5ef8e7cbd928f37a66dd6f351b85e3ac69bc16cc3777055eed66a5dd7da3dba9d05b747dc6ae78382dcc17edb9253a5718f2d2e1a849dc0656eb7af68d6ea486adbd4f55b4c2b6b63b8fd6bbdd06d609805a92fbab4c9adf68db07ed045e559dac6fb359c1f65fc2a6ca8a1ed9238cbb1ebca76321352c4d627d86d4c3b07fc61604a25abf29fad7b804caf15b395d76f92b985925703b5cadad9195aa7aceb3e8e956505e8ac475eb57dc3e6ae53fa559dfe5aae319b5514aaea8c6bfd4ec949a980c135250efaa34134d43c209a82053d4f910a29dc353d38ca1aa6c1d054cd4f7a984d1752de172a5653554a1cb5692de7a5230806a40a817476840e8d77775183dcba2b1b3744b7976881808d0d82b7a15ac9f420ab6282c029d02d6bfa005c393f619aa7d6fd4cf839d89eb29f13cbc4227827044edabf89d615b13a1aa9e72e5b34e32d149c11f63377ccf66dabdc4d8bd219ac46f334e2afe687979cce5c159978c4b324c48a634e86cc409e5982ef552fb99725e2afdcb9c68696e6ffd2d2a98a590ed94af91ee95a0e2d2a9f4a653fa144a56c12945c9cf2817a9e4eeca949b54e7931a2cf2593b4649e692c914c6391d9917231367244e7cbc87527b909ac912096bfa3ff04ec7d67248f5dd291e1dbb23b00164738a548e22ac91ba856e36171d469bc008ce955b193690631355e45ffc1d8bb1ccb16c864e2c5ad3c564aa18a7c103145dd1a278778c4ca78189481ed11f6d4222bb47c4312b28815f750f9369a1df63b4398c2a86e59850d338f619384e43013de85b70070ad742e14817b426a9c3848a2e7087e8160fd1bcc1d4dcf835f20f06294820b290dc13fff78235d6903d794a068768c0ac030810e4e1018964201ecc84018e707fe8860ff3eb3dfd59273f86aac7ec47d2fcf7815f8cc803ef54d97da2322fab3c9df446cdbe64ced7c81a3af8738a9efc80abdd52dd7b62d04f636c11eb5031bd4669e7a45b6cf3fd6a9e6df3d3cb8826792a55cf1c7845e275283c2b76a7810abeef950bdde11ed3b9f45f76f8b7eed65fe5d9b586bb13efb75e2786eb3a591d55fefba8973374cdec0e912199d11122b9ffcfc73bb118e6ed3d1ccc91a397704c72a9e78e4cbc0dc887d138ef118719a6cae2ada25c44d423867f55708c9fae092dedc01967b7e1af96f807f2de7b739bbec3cb75c3f96e7609cdc675e1b7c5bbb6d7a4a6d6d3e4da569b9b3a5df3653de26c661b4d849295af8ca235d0eb66b609f6d63f04dab79ff354ecbb6a5cc96d4382b5a76df0b4cd7e7695a97ed2349a1a36871b44d02f685a098d0344e99f697cb3cd588675b1d0ce374619b710c334e7e8665dd10cc3d7dd977f1b32d07446562242ca46f359393a432533916468152c853a3d8faea1b1d6cc5636fa2ac6638c98bd00eb15b2d56278cb4c476ab187f7e5b0e05b661838dcc28cfc9842621306655e608fe8cc0a67e5805abc2fed1c25f9ddaebec32dd7c95b12f74ad75ead62ebce308578d6faaefd0935dbe7f6bb060b1751e93ae862eb5cd12f0b92c339716c76ae101d45be5708b7557f16dc09e2d9ad445afb428b581ead6a1b052d265305a12a3ab3b1745667ba62cb298d592b92ab1e418d62e27bac3fa5158460e2b019d595f4f80abcd771576214cae52a815bc2afab5c0e2567fa54ac8e8d9583c032aeb69a559ebe4aacd83554bb762a7b88e54bf5e6a90f86d5141032a0c6b353e1846a7549554dcca4a99e0ff53052eea59cac14a5e55a930767522a5c8a3e7c8946f610a8c39e051510c0a235e814393d0285786050793c0a08707d40378f27ec2dc4fa2eb29edb2553ce14827819494ece1829d323dd3990f5a717b9d4dfac1a9b8c4e9364692a6ae9cd4d28e6499e9551330219a6463ce4c5884c98494e92fc38525de9964b899bc96ac3852c8ad02577b1a4abc29e95120fd2957f5251184f49f02de937ad25262aeea4ac12b4925a6691e67d12303b7a4475a3485c92090550d91fe24aa3e35ac4794ef88ec68111cc6a2238013c46cebd88d3ad4d19b0b9231d8484609faa8bb206516a08a22bbac54546a5a8a2c12d13960fa25a8a94484bd288a8f79109144a1fa1e943c43fc8728b210d9223a19a67a43052c485ab3f90a98a7213b652424781484309d507a4ca20dd166418b3d682b8c8d04b687207f7ab40d05f68143bf501cdd8a0229174016e5e7fd17e0feeab99fc659f3f5ecf87e62028fc0d249f6ad383ea81b07cf54a0f935141f0ffd83df2c707b8b51cf662831eb5d743d3ed227a24174f3956c1e5c6013c8c3b278bf97cf0cdc99e039753bdb00a775dd08ee0b969dab7c53b2b21475febf0eb4ecd9d540e63a7c9bc74a2608e897691cfd4ce39cf6ec7348b24e5e5641ca7372392398e71f1b1ce338b91c51cc7387918e709d5c4e091629bfd0c337cfed66f4baf0ddef5b9ba8f5b37281506dfca78db529e9b5588436818e86cb0430d8bb261b02c3435dc5886b667ecd628ed1ab0a60353871a6a1f584d39bee1a5f2fd3495d8a68dacccd114239a0e60133f48c26798d98ce918899be36133548ac66597c0cc1417996eb1232b5d34651cb18c99bcb191fd0a321864463e2774c7289e18d193e317c3c662aacacc4ba8b1883fa330e15a66175a94c2518c983702f3047bce6043100bfed9d97eaad72faf6285f12fc8bd8eb8979ef902f184a05de56c0bb34d81753e502e827205cba5bcb8dff7170970c2dedd925b91c94b6901016bf9b92d5a7e25a6bb1cb4451d967664d2cc85fa5948128b1ff1a962dcbd2c377c45826e90afbe0195e5cfe2ba7d2c5708328ad81cd159e7062b1961c55ebec4ab4a781557aca2a8c27e54d213ca917fd151183f2a0023e53baa64a6ea5694cbf5b297554652a5a10a4c17f948701328ebb805193018a29d729442a5c28634d85082c50a07e2a13fee2c27dc1384f74e8c9e63a113bbb78275608a4e696a49c4dd2137923526d12ba4d6046c9a3cb79337259264d7b24c597b898304c92f5bd925caf5c4b5506096288b92b4eaa25499a44a52e3894256f1274ac224c967449531149226f21235016244a5b648558cc902d0f11f5e9b23cc756475a5348e37c091b7647234fb3e46616208c4701917970f22d4158456ab688a5acc913c0e8225999044764e088731c10ff3c821e03d0438425c868feb10c2fa4216800242943b484b134108747120f0e1241a68bc82d6f1904c225207adea40bb14881011e90118b52005f743fd1d307f2fb58fd78161f9229c3eeac487d62b10f9e03e1f1f74c3e05e647b9a0c0f651221eadd6e3d2335c79d5c10f2cab71e3d4ee3c42b047815ca8ef4cf31dcddb63b64530765a238ebd7cb1d5f7b03a881b874a2c68e86b341cf22c839ae07072efae0e507241c85ee838d612c7140d50e1ab901c1abfa38003c46f96360de586d1bb09ea372c80c6defcb8db0db11b478a2365add86c4d908d7cb511adf80c358b5006aaf7f8d491421a7881434bdd586915930d15f7a1a128a433f26b4677fc60ce35ee19ad9a633290ec65ee130cb14931949b063261bd46460748c7fb5f18e6cae319c74062d6e58c4ea471884e8830d93086151608c1e14018240803017f005fcfe00bee04017c42802f58afc5e525f0bbe73c17654722e9b6d45cd8d80b8f62917076422de025c5b63458b60cfd16aa7da2d26d6859f1a28b32bad164e9242c6f7d05883e98b0522e15f3a0c2bba168571a150ad80761599a7c2b06a0455b4200aab67a1540a5e2a5517c5452050a7f42f14e899e29a57a452f3be8a5398b149182628f7c505199478a28683143b5e0284bf5850429a89fdb0c13e62b827a20904eefb209d371c1391e9826f9fcc4da08909a9aa8133e96a2653ce44c551a09805a512ec31a25af7ac4b0d5f8957809129ab92250cff849c954892f1c9124a2bc246c5a04888f389072da11fa88423cd878474c3708dfb3211abcd4233085446131a08b8ac6115df96229550c44dd97089218b11110b621fbe7443aba8886bf7710c501e2164460427d49884647f1079db820ce6a84152748821098102f970203a520402b2407fc3b80fe63301fa7f9c3f075307d7dd40f9dae21f175f43de6fc07b3ee10f560721e887fc3cca1987906d50f0f3ca1dfb5883bb0a6876d5a50ec94d41d6fe703a9a9d874ab460e8437c1ce62883987f907287ae0e3ffac1c5e1a43878b40706ad20dfc94e1bd7b9c376cc906e54a70dba04e1b5304436643286c45230d784961acff70355eeb86a3c3b0d376101a4e8f8345cee86839e40cf74a819cecb0335e360663e140cb80481950a6c3262bd06448c00c798da18d4204316a7e06259dd0c3be4a185934c30757386071610bff08217dfe182f839885e8f410bc2f6c17682402e94e785cb3720b87af416f1f982da95b05addea0b4d304167d5f42cc0ee0590e9e0b13786160a52c2bdb9b05745830ada8661598d142af95c855828f0aa258e1528d802a1a2d853c5b70a6aee814ba648293e088520ef00a34460144d7402864e80505e3009fe5e013e203c278ec704eb36c09c9352137811426bba004d0e990994ca2130f99c25eb6d84b6fad09611ba12a89a8251e2a849d69d092e28412431102453d1848435e08fbeec11defa8238c5d046b5e608ca6dc117c54422c7c80452e2a0899a3e111b1bc22060d043ac1f08698fe10bb4e42147268422fbb083a306105ce90208b0f840b8f3080b8400fffe981fd1c283f47bc07dd8980fa44d01f1b3a03ddc0c07b03f80f4a10c1e677103c75d80783a4a0ef13241db66203b15150757b7a0e99aec1d0807839b9b9072c7720e438381c5c5c83863b90701e1c0deeae01bb35b837130a06d7f640d9b2b81b0cff035c7a206aeb340d48f941a6942034817606861760cf814c19c81f033407b065e2160ca87b419299083204a70636cfe0c5a2a0188d91830cdef06102180c0d1e817f41c82f9c4805ea1500bc1560175d2c02e6fa805c4a900b76cdc16c8bb02d4804059fdc20b2d8341636c402c2551057bad20ae573c15a74182b078505581aa0a9e9c8151a2e829ee9505352340a58fb0148f85828da760512c5c0a148c8140741027cb1e04f100c09d14e413815c026c08204cfd2e098f3dc12fdd1025ba9704af3ae094e584127c9a824b953048f376090e9b011fdb3823bcab046fc7008d0038118116822c4940450e8808928f01106be021d10404329a808563ac108ea5020e1f00414dba081b0441018c601ff74d03f7aaa07e0e8c0fa51b81f111103db06207a7e580f33a081e2f3103beecc076ff800ec44f81d51a203a35d407391d80e572301c785a038856407035340dec1601ba34e036dd6606ce96c0d832301ad2730353dc6069ae540d1c4481a05bf033a66e06683c00cb7758193d27032174806369880c54b081878a003090400605f800bf3f0017b82002f114005d657c0b952f016fb9c02d9a3205a7b540b3868016430902c2b02057a0dc0add958158e5d02ac39a054d5e80a84b2814dd8d02963e40521a500a2db9814308e0280bcc04f6de809d8a50138756026bb3c04cd084098570012e1da025721e04a41fc093415012400f024305e047c22408e48e811a1eb022f5e604550d00896d78110763021c2a0042edd8084aea810706c020967804099100800c200fdcfc01f715803e524c07b85900f4d0801e532a03c19640771aa00ec08501d3bda039ee2c072caf80e376901c2b52037d07806e96480db1a901b217c035c02006a7c380d2f3a01a1e44033bcf80667c700cb0120192194031c6d406296a00c34260182b5602fdd8c05eca700bbb6b0173b7602e00f405b17880b45d701651de02c30e00577d980ad35f0156e7802a6d28053fc480a63f80149130028b5a0050934009f798013b9f00270a1c04d4230098e34012e8a20256a7404a08c00927c10121d32023d67c046e69808c435011578a0224e08043db680863850109794020d0f0040e6d80805a600fdd3c01f5f0803e089007aa8e00f286c01df82403b404007523200e790e01c9c1c0388d9006fc8700dcf0e01b4ac4035f02806a98300d2a5601a03f003367b806591b00c8ad0018c778030f3e8060b4400bf068017953002e946005bff400b5b080166cec02c48d005772000aca9a0154e8402a10e00530bd00a3f0a01439cc027ec3804ecc1009b8420132e98025da8804ab21009362c0122cc0023db78046bd2008b8b40113418021eeb0042eca0083fc4010447402013e003f3fe007cb4600f5dac01e4ab003bb630075b2600e7f9401c92c80384ef006ef4e00daa0001aebd803509700687a800cdcc80195588031e50006242000c17c0017cf8002ee10005c4a000b5abc016597002bfcc005691200aa594014f3000293790051162009f81c0139bd802690d004bd7a009522801253a802407d0046d44008b3900111a180219be00420ac0081c2800feed001f4c6003d79c0078bc400ed18001d18a00391fe007023c00dc1d001afff0034fbe0067f6400cbf6801901b00310c6006031000bc9f80171d3002d5000058d1800ae12801551c0029c580051d5000a04a00139ec00266b8004b38c0093410012038002340a0044fa40086f200107f5002043a003f16c007b57800f119001d73200398b800706c800db99001acdc003456000662b800c76a0018524002f738005c8f000b4820015ff4002ae14005392000a2d60013d3600269cc004b2f000925b0011cd60022a340043608008307000febe001ef20003c2180074cf000e2d8001b86800356c80067a8000c91000185e0002f3c0005b88000b150001575c00298b00050640009b820012cb40024540004631000879200105bc001f918003ce5000756a000e248001b3e800347500064f4000c2300017558002cd6000561c000a5480013d100025fe00048cc0008b640010ac0001fe20003cee000745c000de10001a77000326e0006004000b6a80015b300029360004e30000943800118b00021300003eb80007668000df40001a4800031700005ce0000ae40001468000262c00047500008500000f7a0001cc4000356000062d0000b6a000150c00026b800047100008220000ed80001b08000311000058c0000a0000011f8000202000039400006580000b3000013a000022400003b400006600000ae000012600001ec0000330000053000008600000d4000014800001f000002e00000400000058000007000000800000080000008000000
def cDen (u : Nat) : Nat :=
  Nat.land (Nat.shiftRight cDenTable (Nat.mul 27 u)) 134217727
def cTableOK : Nat → Bool
  | 0 => true
  | n + 1 => (cDen n == denFast n) && cTableOK n
theorem cTableEntry {n u : Nat} (hu : u < n) (h : cTableOK n = true) :
    cDen u = denFast u := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨he, ht⟩ := Bool.and_eq_true_iff.mp h
    by_cases h' : u = n
    · subst u
      exact beq_iff_eq.mp he
    · exact ih (by omega) ht
theorem cTableVerified : cTableOK 1652 = true := by decide +kernel
theorem cDen_eq (u : Nat) (hu : u ≤ 1651) : cDen u = denFast u :=
  cTableEntry (by omega : u < 1652) cTableVerified
def cCheap (o l c : Nat) : Nat :=
  let c3 := Nat.mul 3 c
  let k := Nat.sub (cDen (Nat.sub 1651 c3))
    (Nat.add (cDen (Nat.sub o c3)) (cDen (Nat.sub l (Nat.mul 2 c))))
  Nat.sub (Nat.min 30000000 k) (Nat.sub 125576826 (Nat.add (cDen o) (cDen l)))
theorem cCheap_eq (s j c : Nat) (hs : 2344 ≤ s) (hs' : s ≤ 2511)
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
def cHead (p : Nat) : Nat := Nat.mod (Nat.div p 262144) 1024
def cValid : Nat → Nat → Bool
  | 0, _ => true
  | n+1, p => (Nat.beq (Nat.mod p 262144) 0 && Nat.ble (cHead p) 524) && cValid n (Nat.div p 268435456)
def cSum : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | n+1, o, l, p => Nat.add (cCheap o l (cHead p)) (cSum n (Nat.sub o 1) (Nat.sub l 1) (Nat.div p 268435456))
theorem cSum_eq (s n j p : Nat) (hs : 2344 ≤ s) (hs' : s ≤ 2511)
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
    have hp : unpack p = ⟨0,0, cHead p⟩ := by
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
def cFixed (t o l p : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      let i := Nat.sub t (Nat.succ k)
      let c := Nat.land (Nat.shiftRight p (Nat.add (Nat.mul 28 i) 18)) 1023
      Nat.add (cCheap (Nat.sub o i) (Nat.sub l i) c) (cFixed t o l p k)
theorem cHead_shift (p i : Nat) :
    cHead (p >>> (28*i)) = Nat.land (Nat.shiftRight p (Nat.add (Nat.mul 28 i) 18)) 1023 := by
  change (p >>> (28*i)) / 262144 % 1024 = (p >>> (28*i+18)) &&& (2^10-1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (p >>> (28*i)) 18]
theorem cFixed_eq (t o l p k : Nat) (hk : k ≤ t) :
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
theorem cFixed_full (k o l p : Nat) : cSum k o l p = cFixed k o l p k := by
  simpa using cFixed_eq k o l p k (Nat.le_refl k)
def cPrefix (s : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n+1, j, p => certifiedSaving s j (unpack p) + cPrefix s n (j+1) (p / 268435456)
theorem cSplit (s m n j p : Nat) :
    rowLoop s (m+n) j p = cPrefix s m j p +
      rowLoop s n (j+m) (p / (268435456^m)) := by
  induction m generalizing j p with
  | zero => simp [cPrefix]
  | succ m ih =>
    rw [Nat.succ_add, rowLoop, cPrefix, ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 m, Nat.div_div_eq_div_mul, Nat.pow_succ']
private structure CEntry where
  row : Row
  cut : Nat
def cAllowed (s : Nat) (e : CEntry) : Bool :=
  let j := e.row.first
  let t := e.row.count
  let m := e.cut
  decide (m ≤ t ∧ 2344 ≤ s ∧ s ≤ 2511 ∧ 526 ≤ j+m ∧ 3000 ≤ s+(j+m) ∧
    (4649-s)/4+1 ≤ j+m+1 ∧ 4650-(s+(j+m)) ≤ 3*((4649-s)/4+1) ∧
    (2008 ≤ s ∧ s < 3012 ∧ 322 ≤ j ∧ j+t ≤ 1063 ∧
      3000 ≤ s+j ∧ s+j+t ≤ 3420)) &&
    cValid (t-m) (e.row.packed / 268435456^m)
def cEvaluate (s : Nat) (e : CEntry) : Nat :=
  let j := e.row.first
  let m := e.cut
  let p := e.row.packed
  cPrefix s m j p + cFixed (e.row.count-m) (4650-(s+(j+m))) (1650-(j+m))
    (p / 268435456^m) (e.row.count-m)
theorem cEntry_eq (s : Nat) (e : CEntry) (h : cAllowed s e = true) :
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
def cGroupOK : Nat → List CEntry → Bool
  | _, [] => true
  | s, e :: es => cAllowed s e && cGroupOK (s+1) es
def cGroupSum : Nat → List CEntry → Nat
  | _, [] => 0
  | s, e :: es => cEvaluate s e + cGroupSum (s+1) es
theorem cGroup_eq (s : Nat) (es : List CEntry) (h : cGroupOK s es = true) :
    batchScore s (es.map CEntry.row) = cGroupSum s es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨he, ht⟩ := Bool.and_eq_true_iff.mp h
    exact congrArg₂ Nat.add (cEntry_eq s e he) (ih (s+1) ht)
theorem cJoin (s : Nat) (es : List CEntry) (rs : List Row) (n a b : Nat)
    (h : cGroupOK s es = true) (ha : cGroupSum s es = a)
    (hn : es.length = n) (hb : batchScore (s+n) rs = b) :
    batchScore s (es.map CEntry.row ++ rs) = a+b := by
  rw [batchScore_append, List.length_map, hn, cGroup_eq s es h, ha, hb]
def entries164 : List CEntry := [
  ⟨⟨527,163,0x80000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000028000006800000c80000108000010800001880000188000020⟩,8⟩,
  ⟨⟨526,163,0xc0000018000002400000300000040000004c00000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020000002100000218000022000002300000240000024000002600000260000028000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000018000006800000c800001080000108000018800001880000208001800⟩,9⟩,
  ⟨⟨526,163,0x40000010000002000000300000034000004000000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000048000008800000c80000108000018800001880000208000020⟩,9⟩,
  ⟨⟨526,162,0x80000018000002000000300000040000004400000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000038000008800000c80000108000018800001880000208000020⟩,8⟩]
def suffix164 : List Row := entries164.map CEntry.row ++ []
theorem score164 : batchScore 2508 suffix164 = 949525536 :=
  cJoin 2508 entries164 [] 4 949525536 0
    (by decide +kernel) (by decide +kernel) rfl rfl
def entries160 : List CEntry := [
  ⟨⟨528,165,0x80000014000002000000300000038000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000028000006800000c80000108000010800001880000188001800⟩,8⟩,
  ⟨⟨528,164,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000018000006800000c80000108000010800001880000188001800⟩,8⟩,
  ⟨⟨528,164,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000048000008800000c8000010800001880000188000020⟩,8⟩,
  ⟨⟨527,164,0x40000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000038000008800000c80000108000018800001880000208001800⟩,8⟩]
def suffix160 : List Row := entries160.map CEntry.row ++ suffix164
theorem score160 : batchScore 2504 suffix160 = 1900764264 :=
  cJoin 2504 entries160 suffix164 4 951238728 949525536
    (by decide +kernel) (by decide +kernel) rfl score164
def entries156 : List CEntry := [
  ⟨⟨530,166,0x400000100000020000003000000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000028000006800000c8000010800001080000188001000⟩,7⟩,
  ⟨⟨530,165,0x800000180000020000003000000400000044000006000000600000068000008000000800000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000018000006800000c8000010800001080000188001000⟩,7⟩,
  ⟨⟨529,165,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000048000008800000c8000010800001880000188001800⟩,8⟩,
  ⟨⟨529,165,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000118000013000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000038000008800000c8000010800001880000188001000⟩,7⟩]
def suffix156 : List Row := entries156.map CEntry.row ++ suffix160
theorem score156 : batchScore 2500 suffix156 = 2853575461 :=
  cJoin 2500 entries156 suffix160 4 952811197 1900764264
    (by decide +kernel) (by decide +kernel) rfl score160
def entries152 : List CEntry := [
  ⟨⟨532,166,0xc0000018000002800000340000040000004c00000600000064000007000000800000088000009000000c000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020000002100000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006300000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000028000006800000c800001080000108001000⟩,6⟩,
  ⟨⟨531,167,0x40000010000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000018000006800000c800001080000108000c008001800⟩,7⟩,
  ⟨⟨531,166,0x80000018000002000000300000040000004400000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000048000008800000c800001080000188001000⟩,7⟩,
  ⟨⟨531,165,0xc0000018000002400000300000040000004800000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006300000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000038000008800000c800001080000188001000⟩,6⟩]
def suffix152 : List Row := entries152.map CEntry.row ++ suffix156
theorem score152 : batchScore 2496 suffix152 = 3807362729 :=
  cJoin 2496 entries152 suffix156 4 953787268 2853575461
    (by decide +kernel) (by decide +kernel) rfl score156
def entries148 : List CEntry := [
  ⟨⟨534,167,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000028000006800000c80000108000c00⟩,5⟩,
  ⟨⟨533,168,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000018000006800000c80000108000c008001000⟩,6⟩,
  ⟨⟨533,167,0x80000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000048000008800000c80000108001000⟩,6⟩,
  ⟨⟨532,167,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000038000008800000c80000108000c008001000⟩,6⟩]
def suffix148 : List Row := entries148.map CEntry.row ++ suffix152
theorem score148 : batchScore 2492 suffix148 = 4762156983 :=
  cJoin 2492 entries148 suffix152 4 954794254 3807362729
    (by decide +kernel) (by decide +kernel) rfl score152
def entries144 : List CEntry := [
  ⟨⟨536,168,0x80000018000002000000300000040000004400000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000028000006800000c8180000⟩,4⟩,
  ⟨⟨535,168,0xc0000018000002400000300000040000004800000600000060000006c00000800000088000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000018000006800000c80008008001000⟩,5⟩,
  ⟨⟨535,168,0x400000100000020000003000000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000120000013000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000048000008800000c8000c00⟩,5⟩,
  ⟨⟨534,168,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000038000008800000c80008008001000⟩,5⟩]
def suffix144 : List Row := entries144.map CEntry.row ++ suffix148
theorem score144 : batchScore 2488 suffix144 = 5718258539 :=
  cJoin 2488 entries144 suffix148 4 956101556 4762156983
    (by decide +kernel) (by decide +kernel) rfl score148
def entries140 : List CEntry := [
  ⟨⟨538,169,0x80000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000280c00008180000⟩,3⟩,
  ⟨⟨537,169,0x80000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000001800000681000008200000⟩,4⟩,
  ⟨⟨537,168,0xc0000018000002400000300000040000004c00000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000480800008180000⟩,4⟩,
  ⟨⟨536,169,0x40000010000002000000300000034000004000000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000003800000881000008200000⟩,4⟩]
def suffix140 : List Row := entries140.map CEntry.row ++ suffix144
theorem score140 : batchScore 2484 suffix140 = 6675050431 :=
  cJoin 2484 entries140 suffix144 4 956791892 5718258539
    (by decide +kernel) (by decide +kernel) rfl score144
def entries136 : List CEntry := [
  ⟨⟨540,170,0x40000010000001c000003000000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000118000013000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000804000081000008200000⟩,2⟩,
  ⟨⟨539,170,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,3⟩,
  ⟨⟨539,169,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000081000008200000⟩,3⟩,
  ⟨⟨538,170,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000808000081800008200000⟩,3⟩]
def suffix136 : List Row := entries136.map CEntry.row ++ suffix140
theorem score136 : batchScore 2480 suffix136 = 7631825269 :=
  cJoin 2480 entries136 suffix140 4 956774838 6675050431
    (by decide +kernel) (by decide +kernel) rfl score140
def entries132 : List CEntry := [
  ⟨⟨542,170,0xc0000018000002400000300000040000004c00000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,1⟩,
  ⟨⟨542,170,0x400000100000020000003000000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000c800000d000001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000804000081000008200000⟩,1⟩,
  ⟨⟨541,170,0x800000180000020000003000000400000044000006000000600000068000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000808000081800008200000⟩,2⟩,
  ⟨⟨540,170,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008300000⟩,2⟩]
def suffix132 : List Row := entries132.map CEntry.row ++ suffix136
theorem score132 : batchScore 2476 suffix132 = 8589383154 :=
  cJoin 2476 entries132 suffix136 4 957557885 7631825269
    (by decide +kernel) (by decide +kernel) rfl score136
def entries128 : List CEntry := [
  ⟨⟨544,171,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨544,171,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000036000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩,
  ⟨⟨543,171,0x80000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000810000082000008300000⟩,1⟩,
  ⟨⟨543,170,0x80000018000002400000300000040000004800000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000808000081000008200000⟩,0⟩]
def suffix128 : List Row := entries128.map CEntry.row ++ suffix132
theorem score128 : batchScore 2472 suffix128 = 9547294464 :=
  cJoin 2472 entries128 suffix132 4 957911310 8589383154
    (by decide +kernel) (by decide +kernel) rfl score132
def entries124 : List CEntry := [
  ⟨⟨547,171,0x800000180000020000003000000400000044000006000000600000068000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩,
  ⟨⟨546,171,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨546,171,0x40000010000001c000003000000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000118000013000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000808000081800008200000⟩,0⟩,
  ⟨⟨545,171,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008300000⟩,0⟩]
def suffix124 : List Row := entries124.map CEntry.row ++ suffix128
theorem score124 : batchScore 2468 suffix124 = 10504730364 :=
  cJoin 2468 entries124 suffix128 4 957435900 9547294464
    (by decide +kernel) (by decide +kernel) rfl score128
def entries120 : List CEntry := [
  ⟨⟨549,172,0x80000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000818000082000008300000⟩,0⟩,
  ⟨⟨549,171,0x80000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001b000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩,
  ⟨⟨548,171,0xc0000018000002400000340000040000004c00000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨547,172,0x400000100000020000003000000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000c800000d000001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000818000082000008300000⟩,0⟩]
def suffix120 : List Row := entries120.map CEntry.row ++ suffix124
theorem score120 : batchScore 2464 suffix120 = 11461981380 :=
  cJoin 2464 entries120 suffix124 4 957251016 10504730364
    (by decide +kernel) (by decide +kernel) rfl score124
def entries116 : List CEntry := [
  ⟨⟨552,172,0x400000100000020000003000000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000120000013000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨551,172,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000818000082000008300000⟩,0⟩,
  ⟨⟨551,171,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩,
  ⟨⟨550,172,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030000003100000318000032000003300000340000034000003600000360000036000004000000400000040000004000000400000040000004000000400000040000004000000400000040000004100000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩]
def suffix116 : List Row := entries116.map CEntry.row ++ suffix120
theorem score116 : batchScore 2460 suffix116 = 12418900505 :=
  cJoin 2460 entries116 suffix120 4 956919125 11461981380
    (by decide +kernel) (by decide +kernel) rfl score120
def entries112 : List CEntry := [
  ⟨⟨554,172,0xc000001c000002800000340000040000004c00000600000064000007000000800000088000009000000c000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c0000818000082000008300000⟩,0⟩,
  ⟨⟨554,172,0x40000010000002000000300000034000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨553,172,0x80000018000002000000300000040000004400000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000818000082000008300000⟩,0⟩,
  ⟨⟨552,172,0xc0000018000002400000300000040000004800000600000060000006c00000800000088000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c0000818000082000008300000⟩,0⟩]
def suffix112 : List Row := entries112.map CEntry.row ++ suffix116
theorem score112 : batchScore 2456 suffix112 = 13375066241 :=
  cJoin 2456 entries112 suffix116 4 956165736 12418900505
    (by decide +kernel) (by decide +kernel) rfl score116
def entries108 : List CEntry := [
  ⟨⟨557,172,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000818000082000008300000⟩,0⟩,
  ⟨⟨557,172,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩,
  ⟨⟨556,172,0x80000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨555,172,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000818000082000008300000⟩,0⟩]
def suffix108 : List Row := entries108.map CEntry.row ++ suffix112
theorem score108 : batchScore 2452 suffix108 = 14330625860 :=
  cJoin 2452 entries108 suffix112 4 955559619 13375066241
    (by decide +kernel) (by decide +kernel) rfl score112
def entries104 : List CEntry := [
  ⟨⟨560,172,0x80000018000002000000300000040000004800000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000810000082000008300000⟩,0⟩,
  ⟨⟨559,172,0xc0000018000002400000300000040000004800000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c0000818000082000008300000⟩,0⟩,
  ⟨⟨559,172,0x400000100000020000003000000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000081800008200000⟩,0⟩,
  ⟨⟨558,172,0x800000180000020000003000000400000044000006000000600000068000008000000800000090000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000810000082000008300000⟩,0⟩]
def suffix104 : List Row := entries104.map CEntry.row ++ suffix108
theorem score104 : batchScore 2448 suffix104 = 15285123178 :=
  cJoin 2448 entries104 suffix108 4 954497318 14330625860
    (by decide +kernel) (by decide +kernel) rfl score108
def entries100 : List CEntry := [
  ⟨⟨563,172,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨562,172,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000818000082000008300000⟩,0⟩,
  ⟨⟨561,173,0x40000010000001c000002800000340000040000004c00000600000064000007000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c0000020000002000000200000020000002000000200000021000002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c0000818000082000008300000⟩,0⟩,
  ⟨⟨561,172,0x40000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩]
def suffix100 : List Row := entries100.map CEntry.row ++ suffix104
theorem score100 : batchScore 2444 suffix100 = 16238520547 :=
  cJoin 2444 entries100 suffix104 4 953397369 15285123178
    (by decide +kernel) (by decide +kernel) rfl score104
def entries096 : List CEntry := [
  ⟨⟨566,172,0x40000010000002000000300000034000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨565,172,0x80000018000002000000300000040000004400000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000818000082000008300000⟩,0⟩,
  ⟨⟨564,172,0xc0000018000002400000300000040000004800000600000060000006c00000800000088000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c0000818000082000008300000⟩,0⟩,
  ⟨⟨564,172,0x400000100000020000003000000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000118000013000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000081800008200000⟩,0⟩]
def suffix096 : List Row := entries096.map CEntry.row ++ suffix100
theorem score096 : batchScore 2440 suffix096 = 17190197667 :=
  cJoin 2440 entries096 suffix100 4 951677120 16238520547
    (by decide +kernel) (by decide +kernel) rfl score100
def entries092 : List CEntry := [
  ⟨⟨569,172,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨568,172,0x80000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000810000082000008300000⟩,0⟩,
  ⟨⟨567,172,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c0000818000082000008300000⟩,0⟩,
  ⟨⟨567,171,0xc000001c000002800000340000040000004c00000600000064000007000000800000088000009000000c000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩]
def suffix092 : List Row := entries092.map CEntry.row ++ suffix096
theorem score092 : batchScore 2436 suffix092 = 18140584433 :=
  cJoin 2436 entries092 suffix096 4 950386766 17190197667
    (by decide +kernel) (by decide +kernel) rfl score096
def entries088 : List CEntry := [
  ⟨⟨572,171,0xc0000018000002400000300000040000004c00000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨571,172,0x400000100000020000003000000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000c800000d000001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000810000082000008300000⟩,0⟩,
  ⟨⟨571,171,0x800000180000020000003000000400000044000006000000600000068000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001800000190000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩,
  ⟨⟨570,171,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩]
def suffix088 : List Row := entries088.map CEntry.row ++ suffix092
theorem score088 : batchScore 2432 suffix088 = 19089410993 :=
  cJoin 2432 entries088 suffix092 4 948826560 18140584433
    (by decide +kernel) (by decide +kernel) rfl score092
def entries084 : List CEntry := [
  ⟨⟨575,171,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000810000082000008300000⟩,0⟩,
  ⟨⟨575,171,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000808000081800008200000⟩,0⟩,
  ⟨⟨574,171,0x80000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩,
  ⟨⟨573,171,0x80000018000002400000300000040000004800000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001b000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩]
def suffix084 : List Row := entries084.map CEntry.row ++ suffix088
theorem score084 : batchScore 2428 suffix084 = 20036343383 :=
  cJoin 2428 entries084 suffix088 4 946932390 19089410993
    (by decide +kernel) (by decide +kernel) rfl score088
def entries080 : List CEntry := [
  ⟨⟨579,170,0x80000018000002000000300000040000004800000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000804000081000008200000⟩,0⟩,
  ⟨⟨578,170,0xc0000018000002400000300000040000004800000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000808000081800008200000⟩,0⟩,
  ⟨⟨577,171,0x400000100000020000003000000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩,
  ⟨⟨576,171,0x80000018000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000810000081800008300000⟩,0⟩]
def suffix080 : List Row := entries080.map CEntry.row ++ suffix084
theorem score080 : batchScore 2424 suffix080 = 20981112590 :=
  cJoin 2424 entries080 suffix084 4 944769207 20036343383
    (by decide +kernel) (by decide +kernel) rfl score084
def entries076 : List CEntry := [
  ⟨⟨582,170,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000808000081800008200000⟩,0⟩,
  ⟨⟨581,170,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008200000⟩,0⟩,
  ⟨⟨580,171,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000036000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c000081800008300000⟩,0⟩,
  ⟨⟨580,170,0x40000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000804000081000008200000⟩,0⟩]
def suffix076 : List Row := entries076.map CEntry.row ++ suffix080
theorem score076 : batchScore 2420 suffix076 = 21923463453 :=
  cJoin 2420 entries076 suffix080 4 942350863 20981112590
    (by decide +kernel) (by decide +kernel) rfl score080
def entries072 : List CEntry := [
  ⟨⟨586,169,0x40000010000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c00008180000⟩,0⟩,
  ⟨⟨585,169,0x80000018000002000000300000040000004800000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c00006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c00008200000⟩,0⟩,
  ⟨⟨584,169,0xc0000018000002400000300000040000004800000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000804000081000008200000⟩,0⟩,
  ⟨⟨583,170,0x400000100000020000003000000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000120000013000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000804000081000008200000⟩,0⟩]
def suffix072 : List Row := entries072.map CEntry.row ++ suffix076
theorem score072 : batchScore 2416 suffix072 = 22863445635 :=
  cJoin 2416 entries072 suffix076 4 939982182 21923463453
    (by decide +kernel) (by decide +kernel) rfl score076
def entries068 : List CEntry := [
  ⟨⟨589,169,0x400000100000020000003000000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000120000013000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006300000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000081000008200000⟩,0⟩,
  ⟨⟨588,169,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000804000081000008200000⟩,0⟩,
  ⟨⟨587,169,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000804000081800008200000⟩,0⟩,
  ⟨⟨586,170,0x40000010000001c000002800000340000040000004c00000600000064000007000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000808000081800008200000⟩,0⟩]
def suffix068 : List Row := entries068.map CEntry.row ++ suffix072
theorem score068 : batchScore 2412 suffix068 = 23800699191 :=
  cJoin 2412 entries068 suffix072 4 937253556 22863445635
    (by decide +kernel) (by decide +kernel) rfl score072
def entries064 : List CEntry := [
  ⟨⟨593,168,0x40000010000001c000002800000340000040000004c00000600000064000007000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080400008180000⟩,0⟩,
  ⟨⟨592,168,0x40000010000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080800008180000⟩,0⟩,
  ⟨⟨591,168,0x80000018000002000000300000040000004800000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c00008180000⟩,0⟩,
  ⟨⟨590,168,0xc0000018000002400000300000040000004800000600000060000007000000800000088000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c00008200000⟩,0⟩]
def suffix064 : List Row := entries064.map CEntry.row ++ suffix068
theorem score064 : batchScore 2408 suffix064 = 24735438337 :=
  cJoin 2408 entries064 suffix068 4 934739146 23800699191
    (by decide +kernel) (by decide +kernel) rfl score068
def entries060 : List CEntry := [
  ⟨⟨596,167,0xc0000018000002400000300000040000004800000600000060000007000000800000088000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c00008200000⟩,0⟩,
  ⟨⟨595,168,0x400000100000020000003000000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006180000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000081000008200000⟩,0⟩,
  ⟨⟨594,168,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000081000008200000⟩,0⟩,
  ⟨⟨594,167,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080400008100000⟩,0⟩]
def suffix060 : List Row := entries060.map CEntry.row ++ suffix064
theorem score060 : batchScore 2404 suffix060 = 25667131473 :=
  cJoin 2404 entries060 suffix064 4 931693136 24735438337
    (by decide +kernel) (by decide +kernel) rfl score064
def entries056 : List CEntry := [
  ⟨⟨600,166,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080400008180000⟩,0⟩,
  ⟨⟨599,167,0x40000010000001c000002800000340000040000004c00000600000064000007000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080400008180000⟩,0⟩,
  ⟨⟨598,167,0x40000010000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080800008180000⟩,0⟩,
  ⟨⟨597,167,0x80000018000002000000300000040000004800000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080800008200000⟩,0⟩]
def suffix056 : List Row := entries056.map CEntry.row ++ suffix060
theorem score056 : batchScore 2400 suffix056 = 26595469372 :=
  cJoin 2400 entries056 suffix060 4 928337899 25667131473
    (by decide +kernel) (by decide +kernel) rfl score060
def entries052 : List CEntry := [
  ⟨⟨604,165,0x80000018000002000000300000040000004800000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001b000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c0000⟩,0⟩,
  ⟨⟨603,165,0xc0000018000002400000300000040000004800000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008100000⟩,0⟩,
  ⟨⟨602,166,0x400000100000020000003000000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008100000⟩,0⟩,
  ⟨⟨601,166,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008100000⟩,0⟩]
def suffix052 : List Row := entries052.map CEntry.row ++ suffix056
theorem score052 : batchScore 2396 suffix052 = 27520811859 :=
  cJoin 2396 entries052 suffix056 4 925342487 26595469372
    (by decide +kernel) (by decide +kernel) rfl score056
def entries048 : List CEntry := [
  ⟨⟨608,164,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001800000190000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008040000⟩,0⟩,
  ⟨⟨607,164,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000⟩,0⟩,
  ⟨⟨606,165,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008080000⟩,0⟩,
  ⟨⟨605,165,0x40000010000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080c0000⟩,0⟩]
def suffix048 : List Row := entries048.map CEntry.row ++ suffix052
theorem score048 : batchScore 2392 suffix048 = 28442572131 :=
  cJoin 2392 entries048 suffix052 4 921760272 27520811859
    (by decide +kernel) (by decide +kernel) rfl score052
def entries044 : List CEntry := [
  ⟨⟨612,163,0x40000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨611,163,0x80000018000002000000300000040000004800000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨610,163,0xc0000018000002400000300000040000004800000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c0000020000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨609,164,0x400000100000020000003000000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix044 : List Row := entries044.map CEntry.row ++ suffix048
theorem score044 : batchScore 2388 suffix044 = 29360755663 :=
  cJoin 2388 entries044 suffix048 4 918183532 28442572131
    (by decide +kernel) (by decide +kernel) rfl score048
def entries040 : List CEntry := [
  ⟨⟨616,162,0x400000100000020000003000000340000040000004c0000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨615,162,0x800000180000020000003000000400000044000006000000600000068000008000000800000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨614,162,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨613,163,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix040 : List Row := entries040.map CEntry.row ++ suffix044
theorem score040 : batchScore 2384 suffix040 = 30275227599 :=
  cJoin 2384 entries040 suffix044 4 914471936 29360755663
    (by decide +kernel) (by decide +kernel) rfl score044
def entries036 : List CEntry := [
  ⟨⟨620,161,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e000001000000100000010400001100000118000013000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨619,161,0x80000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨618,161,0x80000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000004c00000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨617,161,0xc0000018000002400000300000040000004c00000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix036 : List Row := entries036.map CEntry.row ++ suffix040
theorem score036 : batchScore 2380 suffix036 = 31185892671 :=
  cJoin 2380 entries036 suffix040 4 910665072 30275227599
    (by decide +kernel) (by decide +kernel) rfl score040
def entries032 : List CEntry := [
  ⟨⟨624,159,0xc0000018000002800000340000040000004c00000600000064000007000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004300000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000064000006600000660000068000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨623,160,0x40000010000002000000300000034000004000000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060800006100000620000063000006400000640000066000006600000660000068000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨622,160,0x80000018000002000000300000040000004400000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c00000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨621,160,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix032 : List Row := entries032.map CEntry.row ++ suffix036
theorem score032 : batchScore 2376 suffix032 = 32092553355 :=
  cJoin 2376 entries032 suffix036 4 906660684 31185892671
    (by decide +kernel) (by decide +kernel) rfl score036
def entries028 : List CEntry := [
  ⟨⟨628,158,0xc0000018000002400000300000040000004800000600000060000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c000002000000200000020000002000000200000020000002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000066000006600000660000068000006800000680000068000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨627,159,0x40000010000001c000003000000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000610000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨626,159,0x80000014000002000000300000038000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001100000120000013000001400000180000018000001800000180000018000001800000190000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c000004c00000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨625,159,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix028 : List Row := entries028.map CEntry.row ++ suffix032
theorem score028 : batchScore 2372 suffix028 = 32994943172 :=
  cJoin 2372 entries028 suffix032 4 902389817 32092553355
    (by decide +kernel) (by decide +kernel) rfl score032
def entries024 : List CEntry := [
  ⟨⟨632,157,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060400006100000620000063000006300000640000066000006600000660000068000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨631,158,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000610000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨630,158,0x40000010000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨629,158,0x80000018000002000000300000040000004400000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000003800000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix024 : List Row := entries024.map CEntry.row ++ suffix028
theorem score024 : batchScore 2368 suffix024 = 33893084869 :=
  cJoin 2368 entries024 suffix028 4 898141697 32994943172
    (by decide +kernel) (by decide +kernel) rfl score028
def entries020 : List CEntry := [
  ⟨⟨636,156,0x80000018000002000000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000500000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006040000610000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨635,156,0xc0000018000002400000300000040000004c00000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000066000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨634,157,0x400000100000020000003000000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨633,157,0x80000014000002000000300000040000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000050000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix020 : List Row := entries020.map CEntry.row ++ suffix024
theorem score020 : batchScore 2364 suffix020 = 34786687084 :=
  cJoin 2364 entries020 suffix024 4 893602215 33893084869
    (by decide +kernel) (by decide +kernel) rfl score024
def entries016 : List CEntry := [
  ⟨⟨640,155,0x80000018000002000000300000040000004400000600000060000006c000008000000840000090000009800000c000000c000000c000000cc00000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000500000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006040000610000062000006300000640000064000006600000660000066000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨639,155,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c000002000000200000020000002000000200000020000002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨638,156,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c00004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨637,156,0x80000014000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001080000110000012000001300000140000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c00003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006100000618000063000006300000640000064000006600000660000068000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix016 : List Row := entries016.map CEntry.row ++ suffix020
theorem score016 : batchScore 2360 suffix016 = 35675637416 :=
  cJoin 2360 entries016 suffix020 4 888950332 34786687084
    (by decide +kernel) (by decide +kernel) rfl score020
def entries012 : List CEntry := [
  ⟨⟨644,154,0x80000014000002000000300000038000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001a000001b0000020000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000003800000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000500000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000610000062000006300000640000064000006600000660000066000006800000680000068000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨643,154,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004100000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨642,154,0xc0000018000002800000340000040000004c00000600000064000007000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003300000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨641,155,0x40000010000002000000300000034000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000500000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006040000610000062000006300000630000064000006600000660000066000006800000680000068000006c000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix012 : List Row := entries012.map CEntry.row ++ suffix016
theorem score012 : batchScore 2356 suffix012 = 36560092496 :=
  cJoin 2356 entries012 suffix016 4 884455080 35675637416
    (by decide +kernel) (by decide +kernel) rfl score016
def entries008 : List CEntry := [
  ⟨⟨648,153,0x40000010000002000000300000038000004400000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d8000010000001000000100000010800001100000120000013000001400000180000018000001800000180000018000001800000190000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000003800000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000043000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000500000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨647,153,0x80000018000002000000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000cc00000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000026000002800000300000030000003000000300000030000003000000300000030000003000000300000030400003100000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨646,153,0xc0000018000002400000300000040000004800000600000064000007000000800000088000009000000a000000c000000c000000c400000d000000e0000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000218000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨645,154,0x400000100000020000003000000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d000001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002300000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c00000500000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006040000610000062000006300000630000064000006600000660000066000006800000680000068000006c000006c000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix008 : List Row := entries008.map CEntry.row ++ suffix012
theorem score008 : batchScore 2352 suffix008 = 37439617737 :=
  cJoin 2352 entries008 suffix012 4 879525241 36560092496
    (by decide +kernel) (by decide +kernel) rfl score012
def entries004 : List CEntry := [
  ⟨⟨652,152,0x40000010000002000000300000034000004000000500000060000006800000800000080000008c000009800000c000000c000000c000000c800000d800001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000003800000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c00000500000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000618000062000006300000640000064000006600000660000068000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨651,152,0x800000180000020000003000000400000044000006000000600000068000008000000840000090000009800000c000000c000000c000000cc00000d800001000000100000010000001080000118000012000001300000140000018000001800000180000018000001800000184000019000001a000001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨650,152,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c400000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001c000002000000200000020000002000000200000020400002100000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000610000062000006300000630000064000006600000660000066000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨649,153,0x40000010000001c000002800000340000040000004c00000600000064000008000000800000088000009800000c000000c000000c000000c800000d000000e00000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003180000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c00000500000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006040000610000062000006300000640000064000006600000660000066000006800000680000068000006c000006c00000800000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix004 : List Row := entries004.map CEntry.row ++ suffix008
theorem score004 : batchScore 2348 suffix004 = 38314124310 :=
  cJoin 2348 entries004 suffix008 4 874506573 37439617737
    (by decide +kernel) (by decide +kernel) rfl score008
def entries000 : List CEntry := [
  ⟨⟨656,151,0x40000010000001c000003000000340000040000004c0000060000006400000800000080000008c000009800000c000000c000000c000000c800000d000001000000100000010000001040000110000012000001300000130000018000001800000180000018000001800000180000018c000019800001a000001b000001c000002000000200000020000002000000200000020800002100000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000036000003800000400000040000004000000400000040000004000000400000040000004000000400000040400004100000418000042000004300000440000044000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000005000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c0000618000062000006300000640000064000006600000660000068000006800000680000068000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨655,151,0x80000014000002000000300000038000004400000600000060000006800000800000080000008c000009800000c000000c000000c000000cc00000d8000010000001000000100000010800001180000120000013000001400000180000018000001800000180000018000001840000190000019800001b000001b0000020000002000000200000020000002000000200000020c00002180000220000023000002400000240000026000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030c0000318000032000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040400004100000420000043000004300000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060c000061800006200000630000064000006400000660000066000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨654,151,0xc0000018000002400000300000040000004800000600000060000006c00000800000084000009000000a000000c000000c000000c000000d000000d8000010000001000000100000010c0000118000012000001300000140000018000001800000180000018000001800000188000019000001a000001b000001b0000020000002000000200000020000002000000200000020c0000218000022000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030400003100000320000033000003300000340000034000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040800004180000420000043000004400000440000046000004600000460000048000004800000480000048000004c000004c000004c000004c000004c0000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006040000610000062000006300000640000064000006600000660000066000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩,
  ⟨⟨653,151,0xc0000018000002400000340000040000004c00000600000064000007000000800000088000009800000c000000c000000c000000c400000d000000e000001000000100000010400001100000118000012000001300000180000018000001800000180000018000001800000188000019800001a000001b000001c000002000000200000020000002000000200000020400002100000220000023000002300000240000024000002600000260000028000003000000300000030000003000000300000030000003000000300000030000003000000300000030800003100000320000033000003400000340000036000003600000360000038000004000000400000040000004000000400000040000004000000400000040000004000000400000040c0000418000042000004300000440000044000004600000460000046000004800000480000048000004c000004c000004c000004c000004c00000500000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006000000600000060000006080000610000062000006300000640000064000006600000660000068000006800000680000068000006c000006c0000080000008000000800000080000008000000800000080000008000000800000080000008000000800000080000008000000⟩,0⟩]
def suffix000 : List Row := entries000.map CEntry.row ++ suffix004
theorem score000 : batchScore 2344 suffix000 = 39183500746 :=
  cJoin 2344 entries000 suffix004 4 869376436 38314124310
    (by decide +kernel) (by decide +kernel) rfl score004
end DataC2344
def rowsC : List Row := DataC2344.suffix000
theorem checkedC : batchScore 2344 rowsC = 39183500746 := DataC2344.score000
end K1_13_2_3_5
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3
open K1_13_2_3_5
open private fastDen fastDen_eq fastC fastC_eq fastOld fastKernel fastKernel_eq from ProximityPrize.SubmissionLower.Numeric6Defs
open private kFast_correct denFast_correct cumFast_clipped balance from ProximityPrize.SubmissionLower.Numeric5Defs
open private rowStart rowValue runValue sumFrom runLength decode from ProximityPrize.SubmissionLower.Numeric6AuxCert
def dDen (u : ℕ) : ℕ := (u * (u * (2*u + 15) + 30) + 25) / 72
theorem dDen_eq (u : ℕ) : dDen u = denFast u := by
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
def dNatKernel (d l c o : ℤ) (j : ℕ) : ℕ :=
  let r := (min d ((o-1-l+d)/4) + 1).toNat
  kFast d.toNat (l.toNat-j) (3*c+1).toNat (o.toNat-j) r
theorem dNatKernel_eq (d l c o : ℤ) (j : ℕ)
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
theorem dSaving_eq (old ini res : ℤ) :
    (old - max 0 ini).toNat - (old - max (max 0 ini) res).toNat =
      (old.toNat - ini.toNat) - (old.toNat - res.toNat) := by omega
def dOld (j : ℕ) : ℕ := 125576826 - dDen (1650-j)
theorem dOld_eq (j : ℕ) : dOld j = (fastOld 1650 (1650-j) 550).toNat := by
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
def dRange (d l c o : ℤ) (j : ℕ) : Bool :=
  decide (0 ≤ d ∧ 0 ≤ c ∧ l-j-1 ≤ 3*c ∧ 0 ≤ o-1-l+d)
def dColumn (s : ℕ) (d l c o : ℤ) (j : ℕ) : ℕ :=
  let old := dOld j
  (old - dNatKernel 1650 1650 550 (4650-s) j) - (old - dNatKernel d l c o j)
theorem dColumn_eq (s j start : ℕ) (p : Powers) (hj : start ≤ j)
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
theorem dSumFrom_congr (f g : ℕ → ℕ) (j n : ℕ) (h : ∀ i, j ≤ i → f i = g i) :
    sumFrom f j n = sumFrom g j n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumFrom, sumFrom, ih, h _ (by omega)]
def dPenalty (x : ℕ) : ℕ := (x * (x * (2*x + 9) + 10) + 3) / 24
theorem dDen_shift (q r : ℕ) :
    dDen (12*q+r) = dDen r + q * (q * (48*q+12*r+30) + r*r+5*r+5) := by
  unfold dDen
  rw [show (12*q+r) * ((12*q+r) * (2*(12*q+r)+15)+30)+25 =
    r*(r*(2*r+15)+30)+25 + 72*(q*(q*(48*q+12*r+30)+r*r+5*r+5)) by ring,
    Nat.add_mul_div_left _ _ (by decide)]
theorem dPenalty_shift (q r : ℕ) :
    dPenalty (12*q+r) = dPenalty r + q * (q * (144*q+36*r+54) + 3*r*r+9*r+5) := by
  unfold dPenalty
  rw [show (12*q+r) * ((12*q+r) * (2*(12*q+r)+9)+10)+3 =
    r*(r*(2*r+9)+10)+3 + 24*(q*(q*(144*q+36*r+54)+3*r*r+9*r+5)) by ring,
    Nat.add_mul_div_left _ _ (by decide)]
theorem dPenalty_period (q r : ℕ) (hr : r < 12) :
    dPenalty (12*q+r+2) = dDen (12*q+r+2) + dDen (12*q+r+1) + dDen (12*q+r) := by
  have h : ∀ i : Fin 12, dPenalty (i.val+2) = dDen (i.val+2) + dDen (i.val+1) + dDen i.val := by
    decide
  simp only [Nat.add_assoc (12*q) r, dPenalty_shift, dDen_shift]
  rw [h ⟨r, hr⟩]
  ring
theorem dPenalty_eq : ∀ x : ℕ, dPenalty x = dDen x + dDen (x-1) + dDen (x-2)
  | 0 => rfl
  | 1 => rfl
  | n+2 => by
    rw [show n+2-1 = n+1 by omega, show n+2-2 = n by omega]
    simpa only [Nat.div_add_mod] using dPenalty_period (n/12) (n%12) (Nat.mod_lt _ (by decide))
def dWith (x : ℕ) (f : ℕ → ℕ) : ℕ :=
  match x with
  | 0 => f 0
  | n+1 => f (n+1)
theorem dWith_eq (x : ℕ) (f : ℕ → ℕ) : dWith x f = f x := by
  cases x <;> rfl
def dCellK (top o l rd tripleR j : ℕ) : ℕ :=
  let x := o-j
  let y := l-j
  top + dDen (x-tripleR) - (dDen x + (dDen y - dPenalty (y-(rd+1))))
theorem dCum_simple (d u : ℕ) (hu₁ : u ≤ 3*d+1) (hu₂ : u ≤ 2*d+3) :
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
def dSpecRange (d l u o r j : ℕ) : Bool :=
  decide (r ≤ d ∧ u ≤ 3*d+1 ∧ u ≤ 2*d+3 ∧ o-j ≤ d+1 ∧ o-j-3*r ≤ d-r+1 ∧
    l-j ≤ 3*(d-r)+1 ∧ l-j ≤ 2*(d-r)+3)
theorem dCellK_eq (d l u o r j start : ℕ) (hj : start ≤ j)
    (hg : dSpecRange d l u o r start = true) :
    dCellK (dDen u - dPenalty (u-(d+1))) o l (d-r) (3*r) j =
      kFast d (l-j) u (o-j) r := by
  obtain ⟨hr, hu₁, hu₂, ho, ho', hl₁, hl₂⟩ := of_decide_eq_true hg
  have h₁ : cumFast d (o-j) = dDen (o-j) := by rw [cumFast, ite_eq_left (by omega), dDen_eq]
  have h₂ : cumFast (d-r) (o-j-3*r) = dDen (o-j-3*r) := by rw [cumFast, ite_eq_left (by omega), dDen_eq]
  simp only [kFast, cutFast, ite_eq_right (by omega : ¬ d < r), dCum_simple d u hu₁ hu₂, h₁, h₂,
    dCum_simple (d-r) (l-j) (by omega) (by omega)]
  rfl
def dRemoved (d l o : ℤ) : ℕ := (min d ((o-1-l+d)/4) + 1).toNat
def dGood (d l c o : ℤ) (j : ℕ) : Bool :=
  dSpecRange d.toNat l.toNat (3*c+1).toNat o.toNat (dRemoved d l o) j
def dPrepare (d l c o : ℤ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  let u := (3*c+1).toNat
  let r := dRemoved d l o
  dWith (dDen u - dPenalty (u-(d.toNat+1))) fun top =>
  dWith o.toNat fun ord => dWith l.toNat fun lo =>
  dWith (d.toNat-r) fun rd => dWith (3*r) fun triple => f top ord lo rd triple
def dRegion (s j a b c : ℕ) : Prop :=
  3162 ≤ s ∧ s ≤ 3213 ∧ 3383 ≤ s+j ∧ a+4*c ≤ 512 ∧ b ≤ 256 ∧ a ≤ b+384
private instance (s j a b c : ℕ) : Decidable (dRegion s j a b c) := by
  unfold dRegion
  infer_instance
theorem dRegion_data (s j a b c : ℕ) (h : dRegion s j a b c) :
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
def dNatPrepare (s a b c : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  let d := 1650-(a+b+3*c)
  let u := 1651-3*(b+c)
  let r := (4649-(s+a+4*c))/4+1
  dWith (dDen u - dPenalty (u-(d+1))) fun t =>
  dWith (4650-(s+2*b+3*c)) fun o => dWith (1650-(3*b+2*c)) fun l =>
  dWith (d-r) fun rd => dWith (3*r) fun tr => f t o l rd tr
theorem dNatPrepare_eq (s j a b c : ℕ) (h : dRegion s j a b c)
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    dNatPrepare s a b c f =
      dPrepare (1650-(a+(b:ℤ)+3*c)) (1650-(3*(b:ℤ)+2*c)) (550-(b+(c:ℤ)))
        (4650-s-(2*(b:ℤ)+3*c)) f := by
  obtain ⟨_, _, ed, el, ec, eo, er⟩ := dRegion_data s j a b c h
  unfold dNatPrepare dPrepare
  rw [ed, el, ec, eo, er]
def dCubic (u a b c divisor : ℕ) : ℕ :=
  Nat.div (Nat.add (Nat.mul u (Nat.add (Nat.mul u (Nat.add (Nat.mul 2 u) a)) b)) c) divisor
def dCountAt (top x y rd tr denX denY : ℕ) : ℕ :=
  Nat.sub (Nat.add top (dCubic (Nat.sub x tr) 15 30 25 72))
    (Nat.add denX (Nat.sub denY (dCubic (Nat.sub y (Nat.add rd 1)) 9 10 3 24)))
def dRunSum (t o l rd tr t₀ o₀ l₀ rd₀ tr₀ j n : ℕ) : ℕ :=
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
theorem dRunSum_eq (t o l rd tr t₀ o₀ l₀ rd₀ tr₀ j n : ℕ) :
    dRunSum t o l rd tr t₀ o₀ l₀ rd₀ tr₀ j n =
      sumFrom (fun k => (dOld k - dCellK t₀ o₀ l₀ rd₀ tr₀ k) -
        (dOld k - dCellK t o l rd tr k)) j n := by
  by_cases h : o = o₀ ∧ l = 1650 ∧ l₀ = 1650
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [dRunSum, and_self, ite_true, dWith_eq]
    rfl
  · simp only [dRunSum, ite_eq_right h, dWith_eq]
def dRunAt (s j code t₀ o₀ l₀ rd₀ tr₀ : ℕ) : ℕ :=
  if code % 2147483648 = 0 then 0 else
    let p := decode code
    if dRegion s j p.value p.top p.cubic then
      dNatPrepare s p.value p.top p.cubic fun t o l rd tr =>
      dRunSum t o l rd tr t₀ o₀ l₀ rd₀ tr₀ j (runLength code)
    else runValue s j code
theorem dRunAt_eq (s j code : ℕ) :
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
def dFold (s t o l rd tr j : ℕ) : List ℕ → ℕ
  | [] => 0
  | code :: tail => dWith j fun j =>
    dRunAt s j code t o l rd tr + dFold s t o l rd tr (j + runLength code) tail
def dRowWork (s j : ℕ) (row : List ℕ) : ℕ :=
  dNatPrepare s 0 0 0 fun t o l rd tr => dFold s t o l rd tr j row
theorem dRowWork_eq (s j : ℕ) (row : List ℕ) : dRowWork s j row = rowValue s j row := by
  induction row generalizing j with
  | nil => simp only [dRowWork, dNatPrepare, dWith_eq, dFold, rowValue]
  | cons code tail ih =>
    have h := dRunAt_eq s j code
    have ht := ih (j + runLength code)
    simp only [dRowWork, dNatPrepare, dWith_eq, dFold, rowValue] at h ht ⊢
    rw [h, ht]
def dCheckRows (s : ℕ) : List (List ℕ) → List ℕ → Bool
  | [], [] => true
  | row :: tail, v :: vs =>
    (fits s [row] && Nat.beq (dRowWork s (rowStart s) row) v) && dCheckRows (s+1) tail vs
  | _, _ => false
theorem dCheckRows_sound (s : ℕ) (rows : List (List ℕ)) (vs : List ℕ)
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
theorem dJoin {s n m v w : ℕ} {a b : List (List ℕ)}
    (ha : a.length = n ∧ fits s a = true ∧ value s a = v)
    (hb : b.length = m ∧ fits (s+n) b = true ∧ value (s+n) b = w) :
    (a ++ b).length = n+m ∧ fits s (a ++ b) = true ∧ value s (a ++ b) = v+w := by
  simp only [List.length_append, fits_append, value_append, ha.1, hb.1, ha.2.1, hb.2.1,
    Bool.true_and, ha.2.2, hb.2.2, and_self]
set_option maxRecDepth 50000
set_option maxHeartbeats 0
def dRows3162 : List (List ℕ) := [
  [nat_lit 128849018880, nat_lit 2349334528, nat_lit 10872160256, nat_lit 8691122176, nat_lit 67633152, nat_lit 4396023808, nat_lit 6509953024, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 6442844544, nat_lit 25770066304, nat_lit 8590131584, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 130996502528, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 2215116800, nat_lit 4396023808, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 6442844544, nat_lit 25770066304, nat_lit 10737615232, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 130996502528, nat_lit 201850880, nat_lit 13019643904, nat_lit 8691122176, nat_lit 2215116800, nat_lit 2248540160, nat_lit 4362469376, nat_lit 4345692160, nat_lit 33947648, nat_lit 25559040, nat_lit 17170432, nat_lit 12976128, nat_lit 6684672, nat_lit 6442844544, nat_lit 25770066304, nat_lit 8590131584, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 133143986176, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 2215116800, nat_lit 4396023808, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 6442844544, nat_lit 27917549952, nat_lit 8590131584, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3162 : dRows3162.length = 4 ∧ fits 3162 dRows3162 = true ∧
    value 3162 dRows3162 = 487238266 :=
  dCheckRows_sound 3162 dRows3162 [121051295,121455241,122157715,122574015] (by decide +kernel)
def dRows3166 : List (List ℕ) := [
  [nat_lit 133143986176, nat_lit 201850880, nat_lit 13019643904, nat_lit 8691122176, nat_lit 2215116800, nat_lit 2248540160, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 12976128, nat_lit 8590328192, nat_lit 25770066304, nat_lit 8590131584, nat_lit 131456, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 33152, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 133143986176, nat_lit 2349334528, nat_lit 10872160256, nat_lit 8691122176, nat_lit 2215116800, nat_lit 2248540160, nat_lit 6509953024, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 12976128, nat_lit 6684672, nat_lit 8590328192, nat_lit 25770066304, nat_lit 8590131584, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 135291469824, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 4362600448, nat_lit 2248540160, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 8590328192, nat_lit 27917549952, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 135291469824, nat_lit 201850880, nat_lit 13019643904, nat_lit 8691122176, nat_lit 4362600448, nat_lit 101056512, nat_lit 4362469376, nat_lit 4345692160, nat_lit 33947648, nat_lit 25559040, nat_lit 17170432, nat_lit 12976128, nat_lit 10737811840, nat_lit 25770066304, nat_lit 8590131584, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3166 : dRows3166.length = 4 ∧ fits 3166 dRows3166 = true ∧
    value 3166 dRows3166 = 497513376 :=
  dCheckRows_sound 3166 dRows3166 [123443105,124175938,124552060,125342273] (by decide +kernel)
def dRows3170 : List (List ℕ) := [
  [nat_lit 137438953472, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2248540160, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 8781824, nat_lit 8590328192, nat_lit 27917549952, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 137438953472, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 101056512, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 17170432, nat_lit 12976128, nat_lit 10737811840, nat_lit 25770066304, nat_lit 8590131584, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 139586437120, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 101056512, nat_lit 6509953024, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 12976128, nat_lit 12885295488, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 139586437120, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 101056512, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 25559040, nat_lit 2147877376, nat_lit 10737811840, nat_lit 27917549952, nat_lit 6442647936, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3170 : dRows3170.length = 4 ∧ fits 3170 dRows3170 = true ∧
    value 3170 dRows3170 = 507103137 :=
  dCheckRows_sound 3170 dRows3170 [125831812,126595216,126914003,127762106] (by decide +kernel)
def dRows3174 : List (List ℕ) := [
  [nat_lit 141733920768, nat_lit 13019643904, nat_lit 8691122176, nat_lit 4362600448, nat_lit 101056512, nat_lit 4362469376, nat_lit 4345692160, nat_lit 33947648, nat_lit 25559040, nat_lit 4295361024, nat_lit 10737811840, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 141733920768, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 6510084096, nat_lit 101056512, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 4295361024, nat_lit 10737811840, nat_lit 27917549952, nat_lit 6442647936, nat_lit 131456, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 141733920768, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 50855936, nat_lit 4362469376, nat_lit 2198208512, nat_lit 2181431296, nat_lit 6442844672, nat_lit 10737811840, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 143881404416, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 50855936, nat_lit 6509953024, nat_lit 2198208512, nat_lit 33947648, nat_lit 8590328320, nat_lit 10737811840, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3174 : dRows3174.length = 4 ∧ fits 3174 dRows3174 = true ∧
    value 3174 dRows3174 = 517353169 :=
  dCheckRows_sound 3174 dRows3174 [128216459,129037592,129876377,130222741] (by decide +kernel)
def dRows3178 : List (List ℕ) := [
  [nat_lit 143881404416, nat_lit 201850880, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 50855936, nat_lit 4362469376, nat_lit 2198208512, nat_lit 33947648, nat_lit 10737811968, nat_lit 8590328192, nat_lit 27917549952, nat_lit 4295164288, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 146028888064, nat_lit 13019643904, nat_lit 8691122176, nat_lit 4362600448, nat_lit 50855936, nat_lit 4362469376, nat_lit 4345692160, nat_lit 10737811968, nat_lit 10737811840, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 16768, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 146028888064, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 4362469376, nat_lit 2198208512, nat_lit 12885295616, nat_lit 8590328192, nat_lit 27917549952, nat_lit 4295164288, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 148176371712, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2214985728, nat_lit 2198208512, nat_lit 15032779264, nat_lit 8590328192, nat_lit 25770066304, nat_lit 6442647936, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 24960, nat_lit 16768, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3178 : dRows3178.length = 4 ∧ fits 3178 dRows3178 = true ∧
    value 3178 dRows3178 = 527675991 :=
  dCheckRows_sound 3178 dRows3178 [131068258,131494371,132362658,132750704] (by decide +kernel)
def dRows3182 : List (List ℕ) := [
  [nat_lit 148176371712, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 4362469376, nat_lit 2198208512, nat_lit 15032779264, nat_lit 8590328192, nat_lit 25770066304, nat_lit 4295164288, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 150323855360, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2214985728, nat_lit 2198208512, nat_lit 15032779264, nat_lit 8590328192, nat_lit 27917549952, nat_lit 4295164288, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 150323855360, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 4362469376, nat_lit 50724864, nat_lit 17180262912, nat_lit 8590328192, nat_lit 25770066304, nat_lit 4295164288, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 16768, nat_lit 12672, nat_lit 4480, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 150323855360, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 2214985728, nat_lit 50724864, nat_lit 19327746560, nat_lit 6442844544, nat_lit 27917549952, nat_lit 4295164288, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3182 : dRows3182.length = 4 ∧ fits 3182 dRows3182 = true ∧
    value 3182 dRows3182 = 538132627 :=
  dCheckRows_sound 3182 dRows3182 [133575592,133903412,134901286,135752337] (by decide +kernel)
def dRows3186 : List (List ℕ) := [
  [nat_lit 152471339008, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 34078720, nat_lit 67502080, nat_lit 50724864, nat_lit 21475230208, nat_lit 6442844544, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 152471339008, nat_lit 201850880, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 34078720, nat_lit 2214985728, nat_lit 50724864, nat_lit 19327746560, nat_lit 8590328192, nat_lit 25770066304, nat_lit 4295164288, nat_lit 131456, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 154618822656, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 67502080, nat_lit 50724864, nat_lit 21475230208, nat_lit 6442844544, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 384, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 154618822656, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 34078720, nat_lit 2214985728, nat_lit 23622713856, nat_lit 6442844544, nat_lit 25770066304, nat_lit 4295164288, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3186 : dRows3186.length = 4 ∧ fits 3186 dRows3186 = true ∧
    value 3186 dRows3186 = 548627072 :=
  dCheckRows_sound 3186 dRows3186 [136025913,136921355,137350350,138329454] (by decide +kernel)
def dRows3190 : List (List ℕ) := [
  [nat_lit 156766306304, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 67502080, nat_lit 25770197504, nat_lit 4295360896, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 6528, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 156766306304, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 34078720, nat_lit 67502080, nat_lit 50724864, nat_lit 23622713856, nat_lit 6442844544, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 2432, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 158913789952, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 458752, nat_lit 25770197504, nat_lit 6442844544, nat_lit 25770066304, nat_lit 2147680640, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 24960, nat_lit 16768, nat_lit 6528, nat_lit 2147484032, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 158913789952, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 25690112, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 2432, nat_lit 384, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3190 : dRows3190.length = 4 ∧ fits 3190 dRows3190 = true ∧
    value 3190 dRows3190 = 559083761 :=
  dCheckRows_sound 3190 dRows3190 [138748011,139530254,139934828,140870668] (by decide +kernel)
def dRows3194 : List (List ℕ) := [
  [nat_lit 161061273600, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 458752, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 6528, nat_lit 2147484032, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 161061273600, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 2147680640, nat_lit 2147615104, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 2432, nat_lit 2147484032, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 161061273600, nat_lit 13019643904, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 458752, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 4294967680, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 163208757248, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 30065164800, nat_lit 4295360896, nat_lit 25770066304, nat_lit 2147680640, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 2147484032, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3194 : dRows3194.length = 4 ∧ fits 3194 dRows3194 = true ∧
    value 3194 dRows3194 = 569946396 :=
  dCheckRows_sound 3194 dRows3194 [141204068,142225914,143029513,143486901] (by decide +kernel)
def dRows3198 : List (List ℕ) := [
  [nat_lit 163208757248, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 2173173760, nat_lit 30065164800, nat_lit 2147877248, nat_lit 27917549952, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 4294967680, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 165356240896, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 458752, nat_lit 27917681152, nat_lit 4295360896, nat_lit 27917549952, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 4294967680, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 165356240896, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 30065164800, nat_lit 4295360896, nat_lit 25770066304, nat_lit 196992, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 6442451328, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 167503724544, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 458752, nat_lit 30065164800, nat_lit 2147877248, nat_lit 262656, nat_lit 25770066304, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 4294967680, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3198 : dRows3198.length = 4 ∧ fits 3198 dRows3198 = true ∧
    value 3198 dRows3198 = 580860862 :=
  dCheckRows_sound 3198 dRows3198 [144406018,144700125,145599828,146154891] (by decide +kernel)
def dRows3202 : List (List ℕ) := [
  [nat_lit 167503724544, nat_lit 10872160256, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 32212648448, nat_lit 2147877248, nat_lit 25770066304, nat_lit 196992, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 6442451328, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 169651208192, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 30065164800, nat_lit 2147877248, nat_lit 262656, nat_lit 25770066304, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 6528, nat_lit 6442451328, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 169651208192, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 32212648448, nat_lit 2147877248, nat_lit 262656, nat_lit 25770066304, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 2432, nat_lit 6442451328, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 171798691840, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 32212648448, nat_lit 2147877248, nat_lit 262656, nat_lit 23622582656, nat_lit 196992, nat_lit 2147615104, nat_lit 6442549632, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 6528, nat_lit 6442451328, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3202 : dRows3202.length = 4 ∧ fits 3202 dRows3202 = true ∧
    value 3202 dRows3202 = 591542798 :=
  dCheckRows_sound 3202 dRows3202 [147038068,147478451,148257426,148768853] (by decide +kernel)
def dRows3206 : List (List ℕ) := [
  [nat_lit 171798691840, nat_lit 10872160256, nat_lit 6543638528, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 2173173760, nat_lit 13107200, nat_lit 34360132096, nat_lit 393600, nat_lit 262656, nat_lit 25770066304, nat_lit 4295098752, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 12672, nat_lit 2432, nat_lit 6442451328, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 173946175488, nat_lit 8724676608, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 8912896, nat_lit 32212648448, nat_lit 2147877248, nat_lit 262656, nat_lit 25770066304, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 6528, nat_lit 8589934976, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 173946175488, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 6815744, nat_lit 32212648448, nat_lit 393600, nat_lit 2147746304, nat_lit 23622582656, nat_lit 4295098752, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 16768, nat_lit 12672, nat_lit 2432, nat_lit 8589934976, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 173946175488, nat_lit 10872160256, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 8912896, nat_lit 34360132096, nat_lit 393600, nat_lit 2147746304, nat_lit 23622582656, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 8589934976, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3206 : dRows3206.length = 4 ∧ fits 3206 dRows3206 = true ∧
    value 3206 dRows3206 = 602620127 :=
  dCheckRows_sound 3206 dRows3206 [149720308,149986155,151047748,151865916] (by decide +kernel)
def dRows3210 : List (List ℕ) := [
  [nat_lit 176093659136, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 4718592, nat_lit 34360132096, nat_lit 393600, nat_lit 262656, nat_lit 23622582656, nat_lit 4295098752, nat_lit 6442549632, nat_lit 2147549568, nat_lit 2147533184, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 8589934976, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 260, nat_lit 17179869440, nat_lit 224, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 196, nat_lit 17179869376, nat_lit 160, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 132, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 100, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 68, nat_lit 4294967360, nat_lit 52, nat_lit 4294967344, nat_lit 36, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 4],
  [nat_lit 176093659136, nat_lit 10872160256, nat_lit 6543638528, nat_lit 4362600448, nat_lit 4345823232, nat_lit 34078720, nat_lit 2173173760, nat_lit 13107200, nat_lit 6815744, nat_lit 34360132096, nat_lit 393600, nat_lit 2147746304, nat_lit 23622582656, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 10737418624, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 272, nat_lit 268, nat_lit 264, nat_lit 259, nat_lit 15032385792, nat_lit 2147483872, nat_lit 2147483864, nat_lit 208, nat_lit 204, nat_lit 200, nat_lit 195, nat_lit 15032385728, nat_lit 2147483808, nat_lit 2147483800, nat_lit 144, nat_lit 140, nat_lit 136, nat_lit 131, nat_lit 8589934720, nat_lit 108, nat_lit 104, nat_lit 99, nat_lit 8589934688, nat_lit 76, nat_lit 72, nat_lit 67, nat_lit 4294967360, nat_lit 51, nat_lit 4294967344, nat_lit 35, nat_lit 2147483680, nat_lit 2147483672, nat_lit 16, nat_lit 12, nat_lit 8, nat_lit 3],
  [nat_lit 178241142784, nat_lit 8724676608, nat_lit 6543638528, nat_lit 6510084096, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 8912896, nat_lit 2621440, nat_lit 34360132096, nat_lit 393600, nat_lit 2147746304, nat_lit 21475099008, nat_lit 4295098752, nat_lit 6442549632, nat_lit 4295033216, nat_lit 49536, nat_lit 2147516800, nat_lit 24960, nat_lit 12672, nat_lit 4480, nat_lit 10737418624, nat_lit 2147483968, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 258, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 194, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 130, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 98, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 66, nat_lit 2147483712, nat_lit 54, nat_lit 50, nat_lit 2147483696, nat_lit 38, nat_lit 34, nat_lit 32, nat_lit 26, nat_lit 24, nat_lit 18, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 2],
  [nat_lit 178241142784, nat_lit 8724676608, nat_lit 8691122176, nat_lit 4362600448, nat_lit 2198339584, nat_lit 2181562368, nat_lit 25690112, nat_lit 17301504, nat_lit 13107200, nat_lit 4718592, nat_lit 524800, nat_lit 34360132096, nat_lit 4295229952, nat_lit 21475099008, nat_lit 4295098752, nat_lit 4295065984, nat_lit 4295033216, nat_lit 2147533184, nat_lit 33152, nat_lit 24960, nat_lit 16768, nat_lit 8576, nat_lit 10737418624, nat_lit 4294967616, nat_lit 6442451248, nat_lit 4294967584, nat_lit 2147483928, nat_lit 2147483920, nat_lit 268, nat_lit 262, nat_lit 257, nat_lit 15032385792, nat_lit 224, nat_lit 2147483864, nat_lit 2147483856, nat_lit 204, nat_lit 198, nat_lit 193, nat_lit 15032385728, nat_lit 160, nat_lit 2147483800, nat_lit 2147483792, nat_lit 140, nat_lit 134, nat_lit 129, nat_lit 6442451072, nat_lit 112, nat_lit 108, nat_lit 102, nat_lit 97, nat_lit 6442451040, nat_lit 80, nat_lit 76, nat_lit 70, nat_lit 65, nat_lit 2147483712, nat_lit 54, nat_lit 49, nat_lit 2147483696, nat_lit 38, nat_lit 33, nat_lit 32, nat_lit 25, nat_lit 24, nat_lit 17, nat_lit 16, nat_lit 12, nat_lit 6, nat_lit 1]]
theorem dTotal3210 : dRows3210.length = 4 ∧ fits 3210 dRows3210 = true ∧
    value 3210 dRows3210 = 614063765 :=
  dCheckRows_sound 3210 dRows3210 [152336857,153280828,153771695,154674385] (by decide +kernel)
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
end
section
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
def taylorChart (L : ℕ) (g : Row 4) : TaylorChart where
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
theorem exists_chart (g : Row 4) (p : Shape) (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t) :
    ∃ C : TaylorChart, C.Fits (chart (taylorLength + 4) p) ∧
      ∀ S : Geom[X], atJet g S = 0 → RegularAt g S → C.Recovers S :=
  ⟨taylorChart (taylorLength + 4) g, chart_box (Nat.le_add_right _ _) g p hB hp ht,
    chart_recovers (Nat.le_add_right _ _) g⟩
end
end K1_13_7_1
end
section
namespace K1_13_7_4_2
open K1_13_7
abbrev Local (q : PrimeSpectrum Lower) := Localization.AtPrime q.asIdeal
def remainingIdeal {R ι : Type*} [CommRing R] (f : ι → R) (i : ι) : Ideal R :=
  Ideal.span (f '' {j | j ≠ i})
end K1_13_7_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4
open scoped Polynomial
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
end
section
namespace K1_13_7_2_1
open K1_13 K1_13_6 K1_13_7_2
def LocalGenerators (f : Row 4) (q : Row 3) (surface : Ideal GeoJets)
    (hp : surface.IsPrime) : Prop :=
  letI := hp
  let A := Localization.AtPrime surface
  (intersectionIdeal f (liftLower q)).map (algebraMap GeoJets A) = IsLocalRing.maximalIdeal A
end K1_13_7_2_1
end
