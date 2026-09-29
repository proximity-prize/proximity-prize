import ProximityPrize.SubmissionLower.MovingFiberDirectReceipt6814
/-! Kernel-fast forms of the direct receipt checks.

`decide +kernel` on the `Prop` checks spends most of its time in instance dispatch,
structural-recursion encodings, `Int` arithmetic and `Array` bounds computations. The
`Bool` functions below compute the same checks with the list and `Nat` recursors, `Bool.rec`
and the `Nat` primitives the kernel evaluates directly; each is proved sound against the
`Prop` it replaces, so the receipts' statements are unchanged. -/

namespace ProximityPrize.SubmissionLower.Lower80889.DirectKernel
open Lower80889.CompressedBand Lower80889.BandPolynomial Lower80889.Oracle Lower80889.ThresholdFast
open LocatorPhase6800Oracle (rawFlag)
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## Threshold checks: the exact fallback loop -/

def minK (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

theorem minK_eq (a b : ℕ) : minK a b = min a b := by
  unfold minK
  by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h, min_eq_left h]; rfl
  · rw [show Nat.ble a b = false from Bool.eq_false_iff.mpr (fun hb => h (Nat.le_of_ble_eq_true hb)),
      min_eq_right (by omega)]; rfl

/-- `evalChannelCount` with direct `Nat` operations. -/
def channelK (T YS S : ℕ) : ℕ :=
  let U := minK T YS
  let B := Nat.sub (Nat.add T 1) U
  let k := minK S U
  let n := Nat.sub U k
  let S1 := Nat.add S 1
  let C := Nat.sub (Nat.mul S1 (Nat.add (Nat.add B S) 1)) (Nat.div (Nat.mul S1 S) 2)
  let k2 := Nat.add k 2
  Nat.add (Nat.add (Nat.add (Nat.mul B (Nat.div (Nat.mul k2 (Nat.sub k2 1)) 2))
    (Nat.div (Nat.mul (Nat.mul k2 (Nat.sub k2 1)) (Nat.sub k2 2)) 6))
    (Nat.mul n C)) (Nat.mul S1 (Nat.div (Nat.mul n (Nat.sub n 1)) 2))

theorem channelK_eq (T YS S : ℕ) : channelK T YS S = evalChannelCount T YS S := by
  simp only [channelK, evalChannelCount, evalChooseTwo, evalChooseThree, minK_eq]
  rfl

/-- `evalPowerBandBudgetThin` by the `Nat` recursor on the fuel. -/
def thinLoopK (w delta dc dT dY dS fuel : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ) (fun _ _ _ _ => 0)
    (fun _ ih Dh T YS S => Nat.add
      (Nat.mul delta (channelK T (minK YS (Nat.div (Nat.sub (Nat.add Dh S) 1) w)) S))
      (ih (Nat.sub (Nat.sub Dh delta) dc) (Nat.sub T dT) (Nat.sub YS dY) (Nat.sub S dS))) fuel

theorem thinLoopK_eq (w delta dc dT dY dS fuel Dh T YS S : ℕ) :
    thinLoopK w delta dc dT dY dS fuel Dh T YS S =
      evalPowerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel := by
  induction fuel generalizing Dh T YS S with
  | zero => rfl
  | succ fuel ih =>
    show Nat.add _ (thinLoopK w delta dc dT dY dS fuel _ _ _ _) = _
    rw [ih, evalPowerBandBudgetThin, channelK_eq, minK_eq]
    rfl

def bandThinK (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  thinLoopK 131071 50185 (contactDec p) (total p) (middle p) p.all (s.fuel p)
    (s.contactCap p) (s.totalCap - total p) (s.middleCap - middle p) (s.slopeCap - p.all)

theorem bandThinK_eq (s : SourceNumbers) (p : FlagDegree) : bandThinK s p = evalBandThin s p :=
  thinLoopK_eq _ _ _ _ _ _ _ _ _ _ _

/-- The exact (fallback) threshold check: `FastSourceThresholdSufficient` through its thin
band only. -/
def fastK (s : SourceNumbers) (r v threshold : ℕ) : Bool :=
  Nat.blt (10714-(r+v)) threshold ||
    (let p := rawFlag r v threshold
     Nat.ble 1 p.all && Nat.ble (total p) s.totalCap && Nat.ble (middle p) s.middleCap &&
       Nat.ble p.all s.slopeCap && Nat.blt (bandThinK s p) s.gap)

theorem fastK_sound (s : SourceNumbers) (r v threshold : ℕ) (h : fastK s r v threshold = true) :
    FastSourceThresholdSufficient s r v threshold := by
  simp only [fastK, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, bandThinK_eq] at h
  rcases h with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, h4, Or.inl h5⟩

/-! ## Threshold checks: the compressed runs -/

/-- `FastValidAt` in `ℕ`: each affine quantity is checked nonnegative first, so the
truncated subtractions are exact. -/
def validN (p : Input) (code i : ℕ) : Bool :=
  let t := p.T - i*p.dT
  let y := p.YS - i*p.dY
  let s := p.S - i*p.dS
  let hasD := Nat.ble 6 code
  let dh := cond hasD (p.Dh - i*p.dDh) 0
  let m := code/2%3
  let u := cond (Nat.beq m 0) (131071*t) (cond (Nat.beq m 1) (131071*y) (dh+s))
  let c := cond (Nat.beq (code%2) 0) (131071*s) u
  Nat.ble (i*p.dT) p.T && Nat.ble (i*p.dY) p.YS && Nat.ble (i*p.dS) p.S &&
    cond hasD (Nat.ble (i*p.dDh) p.Dh) (Nat.ble p.Dh (i*p.dDh)) &&
    Nat.ble u (131071*t) && Nat.ble u (131071*y) && Nat.ble u (dh+s) &&
    Nat.ble c (131071*s) && Nat.ble c u

theorem affine_cast (t d i : ℕ) (h : i*d ≤ t) :
    Affine.eval ⟨t,-(d : ℤ)⟩ i = ((t - i*d : ℕ) : ℤ) := by
  simp only [Affine.eval]
  push_cast [Nat.cast_sub h]
  ring

theorem validN_sound (p : Input) (code i : ℕ) (h : validN p code i = true) : ValidAt p code i := by
  rw [validAt_iff_fast]
  unfold validN at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hT, hY⟩, hS⟩, hD⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have et : p.atT.eval i = ((p.T - i*p.dT : ℕ) : ℤ) := affine_cast _ _ _ hT
  have ey : p.atY.eval i = ((p.YS - i*p.dY : ℕ) : ℤ) := affine_cast _ _ _ hY
  have es : p.atS.eval i = ((p.S - i*p.dS : ℕ) : ℤ) := affine_cast _ _ _ hS
  generalize p.T - i*p.dT = t at et h1 h2 h3 h4 h5
  generalize p.YS - i*p.dY = y at ey h1 h2 h3 h4 h5
  generalize p.S - i*p.dS = s at es h1 h2 h3 h4 h5
  have key : 0 ≤ (if 6 ≤ code then p.atDh else p.atDh.scale (-1)).eval i ∧
      (p.dh code).eval i = ((cond (Nat.ble 6 code) (p.Dh - i*p.dDh) 0 : ℕ) : ℤ) := by
    by_cases hc : 6 ≤ code
    · have hb : Nat.ble 6 code = true := Nat.ble_eq_true_of_le hc
      rw [hb] at hD
      have hD' : i*p.dDh ≤ p.Dh := by simpa only [cond, Nat.ble_eq] using hD
      have e := affine_cast p.Dh p.dDh i hD'
      rw [hb]
      simp only [Input.dh, if_pos hc, Input.atDh, cond, e]
      exact ⟨Int.natCast_nonneg _, trivial⟩
    · have hb : Nat.ble 6 code = false := Bool.eq_false_iff.mpr (fun hb => hc (Nat.le_of_ble_eq_true hb))
      rw [hb] at hD
      have hD' : p.Dh ≤ i*p.dDh := by simpa only [cond, Nat.ble_eq] using hD
      rw [hb]
      simp only [Input.dh, if_neg hc, Input.atDh, Affine.scale, Affine.eval, cond]
      refine ⟨?_, by simp⟩
      have hc' : ((p.Dh : ℕ) : ℤ) ≤ (i : ℤ)*(p.dDh : ℤ) := by exact_mod_cast hD'
      linarith
  obtain ⟨hDz, edh⟩ := key
  generalize cond (Nat.ble 6 code) (p.Dh - i*p.dDh) 0 = dh at edh h1 h2 h3 h4 h5
  have eu : (p.u code).eval i =
      ((cond (Nat.beq (code/2%3) 0) (131071*t) (cond (Nat.beq (code/2%3) 1) (131071*y) (dh+s)) : ℕ) : ℤ) := by
    rcases (show code/2%3 = 0 ∨ code/2%3 = 1 ∨ code/2%3 = 2 by omega) with hm | hm | hm <;>
      simp only [Input.u, hm, Affine.eval_scale, Affine.eval_add, et, ey, es, edh, cond, Nat.beq,
        if_true, if_false, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] <;> push_cast <;> ring
  generalize cond (Nat.beq (code/2%3) 0) (131071*t) (cond (Nat.beq (code/2%3) 1) (131071*y) (dh+s)) = u
    at eu h1 h2 h3 h4 h5
  have ec : (p.c code).eval i = ((cond (Nat.beq (code%2) 0) (131071*s) u : ℕ) : ℤ) := by
    rcases (show code%2 = 0 ∨ code%2 = 1 by omega) with hm | hm <;>
      simp only [Input.c, hm, Affine.eval_scale, es, eu, cond, Nat.beq, if_true, if_false,
        one_ne_zero] <;> push_cast <;> ring
  generalize cond (Nat.beq (code%2) 0) (131071*s) u = c at ec h4 h5
  simp only [FastValidAt]
  rw [et, ey, es, eu, ec, edh]
  exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, Int.natCast_nonneg _, hDz,
    by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4,
    by exact_mod_cast h5⟩

def runsValidK (p : Input) (runs : List Run) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun start => Nat.beq start p.fuel)
    (fun run _ ih start => Bool.rec false (ih run.stop)
      (Nat.blt start run.stop && Nat.ble run.stop p.fuel &&
        validN p run.code start && validN p run.code (run.stop-1))) runs

theorem runsValidK_sound (p : Input) (runs : List Run) (start : ℕ)
    (h : runsValidK p runs start = true) : RunsValid p start runs := by
  induction runs generalizing start with
  | nil => exact Nat.eq_of_beq_eq_true h
  | cons run runs ih =>
    change Bool.rec false (runsValidK p runs run.stop) (Nat.blt start run.stop &&
      Nat.ble run.stop p.fuel && validN p run.code start && validN p run.code (run.stop-1)) = true at h
    cases hb : (Nat.blt start run.stop && Nat.ble run.stop p.fuel &&
        validN p run.code start && validN p run.code (run.stop-1)) with
    | false => rw [hb] at h; exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hb
      exact ⟨⟨hb.1.1.1, hb.1.1.2, validN_sound _ _ _ hb.1.2, validN_sound _ _ _ hb.2⟩, ih _ h⟩

/-- `12 * Σ_{k<x} k^j` for `j = 0..3` in `ℕ`: `12x`, `6x(x-1)`, `2x(x-1)(2x-1)`, `3x²(x-1)²`. -/
def sPow (x : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let xx1 := x*(x-1)
  (12*x, 6*xx1, 2*xx1*(2*x-1), 3*(xx1*xx1))

theorem sPow_mono {lo hi : ℕ} (h : lo ≤ hi) :
    (sPow lo).1 ≤ (sPow hi).1 ∧ (sPow lo).2.1 ≤ (sPow hi).2.1 ∧
      (sPow lo).2.2.1 ≤ (sPow hi).2.2.1 ∧ (sPow lo).2.2.2 ≤ (sPow hi).2.2.2 := by
  have h1 : lo*(lo-1) ≤ hi*(hi-1) := Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)
  have h2 : 2*lo-1 ≤ 2*hi-1 := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 h) 1
  simp only [sPow]
  refine ⟨Nat.mul_le_mul_left 12 h, Nat.mul_le_mul_left 6 h1, Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2,
    Nat.mul_le_mul_left 3 (Nat.mul_le_mul h1 h1)⟩

/-- `factoredBoxPrefix` through `sPow`, with its three quadratic forms regrouped. -/
theorem factoredBoxPrefix_sPow (a b c : Affine) (n : ℕ) :
    factoredBoxPrefix a b c n =
      let w : ℤ := 131071
      let A := a.constant
      let B := b.constant
      let C := c.constant
      let α := a.slope
      let β := b.slope
      let γ := c.slope
      let q0 := (C+2*w)*(3*A+3*w+C)+B*(6*A+9*w+3*C+3*B)
      let q1 := γ*(3*A+5*w+2*C+3*B)+α*(3*C+6*w+6*B)+β*(6*A+9*w+3*C+6*B)
      let q2 := γ*(3*α+γ+3*β)+β*(6*α+3*β)
      (C+w)*(q0*(sPow n).1+q1*(sPow n).2.1+q2*(sPow n).2.2.1)+
        γ*(q0*(sPow n).2.1+q1*(sPow n).2.2.1+q2*(sPow n).2.2.2) := by
  unfold factoredBoxPrefix sPow
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg (by omega)]
    have h1 : ((n-1 : ℕ) : ℤ) = (n : ℤ)-1 := by push_cast [Nat.cast_sub hn]; ring
    have h2 : ((2*n-1 : ℕ) : ℤ) = 2*(n : ℤ)-1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ 2*n)]; ring
    simp only [Nat.cast_mul, Nat.cast_ofNat, h1, h2]
    ring

/-- The run's contribution to `runsUpper`, from one evaluation of the quadratic forms and the
`ℕ` differences of `sPow`. -/
def runUpperK (p : Input) (start : ℕ) (run : Run) : ℤ :=
  let a := p.a run.code
  let b := p.b run.code
  let c := p.c run.code
  let w : ℤ := 131071
  let A := a.constant
  let B := b.constant
  let C := c.constant
  let α := a.slope
  let β := b.slope
  let γ := c.slope
  let q0 := (C+2*w)*(3*A+3*w+C)+B*(6*A+9*w+3*C+3*B)
  let q1 := γ*(3*A+5*w+2*C+3*B)+α*(3*C+6*w+6*B)+β*(6*A+9*w+3*C+6*B)
  let q2 := γ*(3*α+γ+3*β)+β*(6*α+3*β)
  let hi := sPow run.stop
  let lo := sPow start
  let d0 : ℤ := ((hi.1-lo.1 : ℕ) : ℤ)
  let d1 : ℤ := ((hi.2.1-lo.2.1 : ℕ) : ℤ)
  let d2 : ℤ := ((hi.2.2.1-lo.2.2.1 : ℕ) : ℤ)
  let d3 : ℤ := ((hi.2.2.2-lo.2.2.2 : ℕ) : ℤ)
  (C+w)*(q0*d0+q1*d1+q2*d2)+γ*(q0*d1+q1*d2+q2*d3)

theorem runUpperK_eq (p : Input) (start : ℕ) (run : Run) (h : start ≤ run.stop) :
    runUpperK p start run = runUpper p start run := by
  obtain ⟨m0, m1, m2, m3⟩ := sPow_mono h
  unfold runUpperK runUpper
  rw [factoredBoxPrefix_sPow, factoredBoxPrefix_sPow]
  simp only [Nat.cast_sub m0, Nat.cast_sub m1, Nat.cast_sub m2, Nat.cast_sub m3]
  ring

def runsUpperK (p : Input) (runs : List Run) : ℕ → ℤ :=
  List.rec (motive := fun _ => ℕ → ℤ) (fun _ => 0)
    (fun run _ ih start => runUpperK p start run + ih run.stop) runs

theorem runsUpperK_eq (p : Input) (runs : List Run) (start : ℕ) (h : RunsValid p start runs) :
    runsUpperK p runs start = runsUpper p start runs := by
  induction runs generalizing start with
  | nil => rfl
  | cons run runs ih =>
    change runUpperK p start run + runsUpperK p runs run.stop = runUpper p start run + runsUpper p run.stop runs
    rw [runUpperK_eq p start run h.1.1.le, ih run.stop h.2]

/-- `a < b` on integers, by the sign of `b - a`. -/
def zlt (a b : ℤ) : Bool := Int.casesOn (motive := fun _ => Bool) (b - a) (fun k => Nat.ble 1 k) (fun _ => false)

theorem zlt_sound (a b : ℤ) (h : zlt a b = true) : a < b := by
  unfold zlt at h
  rcases hb : b - a with k | k <;> rw [hb] at h
  · have hk : 1 ≤ k := Nat.le_of_ble_eq_true h
    rw [Int.ofNat_eq_natCast] at hb
    omega
  · exact absurd h Bool.false_ne_true

def sufficientK (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) : Bool :=
  Nat.blt (10714-(r+v)) threshold ||
    (let p := rawFlag r v threshold
     Nat.ble 1 p.all && Nat.ble (total p) s.totalCap && Nat.ble (middle p) s.middleCap &&
       Nat.ble p.all s.slopeCap && runsValidK (ofSource s p) runs 0 &&
       zlt (50185*runsUpperK (ofSource s p) runs 0) ((s.gap*162125875761905592 : ℕ) : ℤ))

theorem sufficientK_sound (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run)
    (h : sufficientK s r v threshold runs = true) : Sufficient s r v threshold runs := by
  simp only [sufficientK, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  rcases h with h | ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  · exact Or.inl h
  · have hv := runsValidK_sound _ _ _ h5
    refine Or.inr ⟨h1, h2, h3, h4, hv, ?_⟩
    have hz := zlt_sound _ _ h6
    rw [runsUpperK_eq _ _ _ hv] at hz
    push_cast at hz
    norm_num
    linarith

/-- `ThresholdValid`: the compressed runs, else the exact loop. The generator stores no runs
for a threshold the runs cannot certify, so the failing attempt costs one comparison. -/
def thresholdK (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) : Bool :=
  sufficientK s r v threshold runs || fastK s r v threshold

theorem thresholdK_sound (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run)
    (h : thresholdK s r v threshold runs = true) :
    MovingFiberReceiptTypes6814.ThresholdValid s r v threshold runs := by
  simp only [thresholdK, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (sufficientK_sound _ _ _ _ _ h)
  · exact Or.inr (fastK_sound _ _ _ _ h)

/-! ## Lookups without bounds computations -/

/-- `(l[i]?).getD d` by the list recursor: `i` steps, no `length`. -/
def listGetD (l : List ℕ) (i d : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => d)
    (fun x _ ih i => Nat.casesOn (motive := fun _ => ℕ) i x (fun j => ih j)) l i

theorem listGetD_eq (l : List ℕ) (i d : ℕ) : listGetD l i d = (l[i]?).getD d := by
  induction l generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem arrGetD_eq (a : Array ℕ) (i d : ℕ) : listGetD a.toList i d = (a[i]?).getD d := by
  rw [listGetD_eq, Array.getElem?_toList]

/-- `listGetD` at any type (the receipt row tables). -/
def getDK {α : Type} (l : List α) (i : ℕ) (d : α) : α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun x _ ih i => Nat.casesOn (motive := fun _ => α) i x (fun j => ih j)) l i

theorem getDK_eq {α : Type} (l : List α) (i : ℕ) (d : α) : getDK l i d = (l[i]?).getD d := by
  induction l generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

def ownRowK (j r : ℕ) : Array ℕ :=
  match j with
  | 0 => MovingFiberPackingData6814.S0.ownRow r | 1 => MovingFiberPackingData6814.S1.ownRow r
  | 2 => MovingFiberPackingData6814.S2.ownRow r | 3 => MovingFiberPackingData6814.S3.ownRow r
  | 4 => MovingFiberPackingData6814.S4.ownRow r | 5 => MovingFiberPackingData6814.S5.ownRow r
  | 6 => MovingFiberPackingData6814.S6.ownRow r | _ => MovingFiberPackingData6814.S7.ownRow r

def packedRowK (j r : ℕ) : Array ℕ :=
  match j with
  | 0 => MovingFiberPackingData6814.S0.packedRow r | 1 => MovingFiberPackingData6814.S1.packedRow r
  | 2 => MovingFiberPackingData6814.S2.packedRow r | 3 => MovingFiberPackingData6814.S3.packedRow r
  | 4 => MovingFiberPackingData6814.S4.packedRow r | 5 => MovingFiberPackingData6814.S5.packedRow r
  | 6 => MovingFiberPackingData6814.S6.packedRow r | _ => MovingFiberPackingData6814.S7.packedRow r

theorem ownK_eq (j r v : ℕ) :
    listGetD (ownRowK j r).toList v 0 = MovingFiberReceiptTypes6814.sheetOwn j r v := by
  rw [arrGetD_eq]
  rcases j with _|_|_|_|_|_|_|_|j <;> rfl

theorem packedK_eq (j r v : ℕ) :
    listGetD (packedRowK j r).toList v 0 = MovingFiberReceiptTypes6814.sheetPacked j r v := by
  rw [arrGetD_eq]
  rcases j with _|_|_|_|_|_|_|_|j <;> rfl

/-! ## Singleton covers and base runs -/

open MovingFiberSingleCore6814 in
/-- `Cover` as a `Bool`, by the list recursor. -/
def coverK (c : Carrier) (slope intercept r v : ℕ) (th : Array ℕ) (finish : ℕ)
    (xs : List MovingFiberSingleCore6814.Run) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun lo => Nat.beq lo finish)
    (fun x _ ih lo => Bool.rec false (ih x.stop)
      (Nat.blt lo x.stop && Nat.ble x.stop finish && (Nat.ble 3 lo || Nat.beq x.stop (lo+1)) &&
        decide (Active th x.who r v lo (x.stop-1)) &&
        Nat.ble (choice c x.who r v lo) (cap slope intercept lo) &&
        Nat.ble (choice c x.who r v (x.stop-1)) (cap slope intercept (x.stop-1)))) xs

open MovingFiberSingleCore6814 in
theorem coverK_sound (c : Carrier) (slope intercept r v : ℕ) (th : Array ℕ) (finish : ℕ)
    (xs : List MovingFiberSingleCore6814.Run) (lo : ℕ)
    (h : coverK c slope intercept r v th finish xs lo = true) :
    Cover c slope intercept r v th finish lo xs := by
  induction xs generalizing lo with
  | nil => exact Nat.eq_of_beq_eq_true h
  | cons x xs ih =>
    change Bool.rec false (coverK c slope intercept r v th finish xs x.stop) _ = true at h
    cases hb : (Nat.blt lo x.stop && Nat.ble x.stop finish && (Nat.ble 3 lo || Nat.beq x.stop (lo+1)) &&
        decide (Active th x.who r v lo (x.stop-1)) &&
        Nat.ble (choice c x.who r v lo) (cap slope intercept lo) &&
        Nat.ble (choice c x.who r v (x.stop-1)) (cap slope intercept (x.stop-1))) with
    | false => rw [hb] at h; exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, decide_eq_true_eq,
        Nat.beq_eq] at hb
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
      exact ⟨h1, h2, h3, h4, h5, h6, ih _ h⟩

open MovingFiberReceiptTypes6814 LocatorPhase6800Oracle in
/-- `BaseValid` as a `Bool`, with the packed intercept read by `listGetD`. -/
def baseK (base : BaseRow) (r v finish : ℕ) (xs : List BaseRun) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun lo => Nat.beq lo finish)
    (fun x _ ih lo => Bool.rec false (ih x.stop)
      (let pk := listGetD (packedRowK x.sheet r).toList v 0
       Nat.blt lo x.stop && Nat.ble x.stop finish && Nat.blt x.sheet 8 &&
        decide (SecondJetRowIntervals.BaseCell base lo (x.stop-1)) &&
        Nat.ble (sheetSlope x.sheet*lo+pk) (base.evalAt lo) &&
        Nat.ble (sheetSlope x.sheet*(x.stop-1)+pk) (base.evalAt (x.stop-1)))) xs

open MovingFiberReceiptTypes6814 LocatorPhase6800Oracle in
theorem baseK_sound (base : BaseRow) (r v finish : ℕ) (xs : List BaseRun) (lo : ℕ)
    (h : baseK base r v finish xs lo = true) : BaseValid base r v finish lo xs := by
  induction xs generalizing lo with
  | nil => exact Nat.eq_of_beq_eq_true h
  | cons x xs ih =>
    change Bool.rec false (baseK base r v finish xs x.stop) _ = true at h
    cases hb : (Nat.blt lo x.stop && Nat.ble x.stop finish && Nat.blt x.sheet 8 &&
        decide (SecondJetRowIntervals.BaseCell base lo (x.stop-1)) &&
        Nat.ble (sheetSlope x.sheet*lo+listGetD (packedRowK x.sheet r).toList v 0) (base.evalAt lo) &&
        Nat.ble (sheetSlope x.sheet*(x.stop-1)+listGetD (packedRowK x.sheet r).toList v 0)
          (base.evalAt (x.stop-1))) with
    | false => rw [hb] at h; exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, decide_eq_true_eq, packedK_eq] at hb
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
      exact ⟨h1, h2, h3, h4, h5, h6, ih _ h⟩

/-! ## Ledger runs in `ℕ`

Every term of `branchUpper` is nonnegative on a run, and each is monotone in the
subtractions it contains; evaluating them with truncated `ℕ` subtraction therefore gives an
upper bound, so `branchN ≤ bound` implies `branchUpper ≤ bound`. -/

section Ledger
open Lower80889.PhaseRows Lower80889.LedgerAudit FoldChainPolynomial6814

def complementN (R V mode z : ℕ) : ℕ :=
  let t := 10714-(R+V+z)
  let y := 185-(R+V)
  let r := min y (40-R)
  cond (Nat.beq mode 0) (9419418648*t+5377994938571*y+25200613727349*r)
    (cond (Nat.beq mode 1) ((9419418648+5377994938571)*t+25200613727349*r)
      ((9419418648+5377994938571+25200613727349)*t))

def lineN (r y t : ℕ) : ℕ := PairCell6814.constant r y / 50184 - PairCell6814.slope r y / 50184 * t

def branchN (c : PhaseRowContext) (w mode z : ℕ) : ℕ :=
  sourceLine c w z + complementN c.R c.V mode z +
    c.R * foldUnit (c.R+c.V) (c.R+c.V+z) c.R +
    (40-c.R) * foldUnit (185-(c.R+c.V)) (35527-(c.R+c.V+z)) (40-c.R) +
    18000000000000 + (lineN c.R (c.R+c.V) (c.R+c.V+z) + 42*4502611644209)

theorem unitUpper_mono (y r : ℕ) {t t' : ℤ} (h : t ≤ t') : unitUpper y r t ≤ unitUpper y r t' := by
  have hp : ∀ u, piece y r u t ≤ piece y r u t' := by
    intro u
    unfold piece
    split_ifs
    · exact le_rfl
    · have := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg (foldSlope y 2)); linarith
    · have := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg (foldSlope y r)); linarith
  unfold unitUpper
  exact max_le_max (hp 0) (max_le_max (hp 1) (hp 2))

theorem complement_le_N (R V mode z : ℕ) :
    complementUpper R V mode z ≤ (complementN R V mode z : ℤ) := by
  have ht : (10714-R-V-z : ℤ) ≤ ((10714-(R+V+z) : ℕ) : ℤ) := by omega
  unfold complementUpper complementN
  rcases (show mode = 0 ∨ mode = 1 ∨ 2 ≤ mode by omega) with hm | hm | hm
  · subst hm; simp only [cond, if_true]; push_cast; omega
  · subst hm; simp only [cond]; push_cast; omega
  · have h0 : Nat.beq mode 0 = false := Bool.eq_false_iff.mpr (fun hb => by
      have := Nat.eq_of_beq_eq_true hb; omega)
    have h1 : Nat.beq mode 1 = false := Bool.eq_false_iff.mpr (fun hb => by
      have := Nat.eq_of_beq_eq_true hb; omega)
    simp only [h0, h1, cond, if_neg (show mode ≠ 0 by omega), if_neg (show mode ≠ 1 by omega)]
    push_cast; omega

theorem line_le_N (r y t : ℕ) : PairCell6814.line r y t ≤ (lineN r y t : ℤ) := by
  unfold PairCell6814.line lineN
  have e : ((PairCell6814.slope r y / 50184 : ℕ) : ℤ) * (t : ℤ) =
      ((PairCell6814.slope r y / 50184 * t : ℕ) : ℤ) := by push_cast; ring
  rw [e]
  omega

theorem branchUpper_le_N (c : PhaseRowContext) (w mode z : ℕ) :
    branchUpper c w mode z ≤ (branchN c w mode z : ℤ) := by
  unfold branchUpper branchN
  have h1 := complement_le_N c.R c.V mode z
  have h2 : unitUpper (c.R+c.V) c.R ((c.R : ℤ)+c.V+z) = (foldUnit (c.R+c.V) (c.R+c.V+z) c.R : ℤ) := by
    rw [foldUnit_cast]; push_cast; ring_nf
  have h3 : unitUpper (185-(c.R+c.V)) (40-c.R) (35527-c.R-c.V-z) ≤
      (foldUnit (185-(c.R+c.V)) (35527-(c.R+c.V+z)) (40-c.R) : ℤ) := by
    rw [foldUnit_cast]; exact unitUpper_mono _ _ (by omega)
  have h4 := line_le_N c.R (c.R+c.V) (c.R+c.V+z)
  have h5 := mul_le_mul_of_nonneg_left h3 (Int.natCast_nonneg (40-c.R))
  rw [h2]
  push_cast
  linarith

def ledgerK (c : PhaseRowContext) (runs : List LedgerRun) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun start => Nat.beq start (10715-(c.R+c.V)))
    (fun run _ ih start => Bool.rec false (ih run.stop)
      (Nat.blt start run.stop && Nat.ble run.stop (10715-(c.R+c.V)) && Nat.ble run.witness 10 &&
        decide (SourceActive c run.witness start) && decide (SourceCell c run.witness start (run.stop-1)) &&
        Nat.ble (branchN c run.witness run.mode start) bound &&
        Nat.ble (branchN c run.witness run.mode (run.stop-1)) bound)) runs

theorem ledgerK_sound (c : PhaseRowContext) (runs : List LedgerRun) (start : ℕ)
    (h : ledgerK c runs start = true) : Lower80889.LedgerAudit.RunsValid c start runs := by
  induction runs generalizing start with
  | nil => exact Nat.eq_of_beq_eq_true h
  | cons run runs ih =>
    change Bool.rec false (ledgerK c runs run.stop) _ = true at h
    cases hb : (Nat.blt start run.stop && Nat.ble run.stop (10715-(c.R+c.V)) && Nat.ble run.witness 10 &&
        decide (SourceActive c run.witness start) && decide (SourceCell c run.witness start (run.stop-1)) &&
        Nat.ble (branchN c run.witness run.mode start) bound &&
        Nat.ble (branchN c run.witness run.mode (run.stop-1)) bound) with
    | false => rw [hb] at h; exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hb
      refine ⟨(runValid_iff_fast c start run).mpr ⟨h1, h2, h3, h4, h5, ?_, ?_⟩, ih _ h⟩
      · exact (branchUpper_le_N _ _ _ _).trans (by exact_mod_cast h6)
      · exact (branchUpper_le_N _ _ _ _).trans (by exact_mod_cast h7)

/-! ## Phase runs -/

def phaseRunsK (c : PhaseRowContext) (phase finish : ℕ) (runs : List PhaseRun) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun start => Nat.beq start finish)
    (fun run _ ih start => Bool.rec false (ih run.stop)
      (Nat.ble run.stop finish && Nat.blt start run.stop && Nat.ble run.witness phase &&
        decide (SourceActive c run.witness start) && decide (SourceCell c run.witness start (run.stop-1)) &&
        Nat.ble (sourceLine c run.witness start) (hereCharge c phase start) &&
        Nat.ble (sourceLine c run.witness (run.stop-1)) (hereCharge c phase (run.stop-1)))) runs

theorem phaseRunsK_sound (c : PhaseRowContext) (phase finish : ℕ) (runs : List PhaseRun) (start : ℕ)
    (h : phaseRunsK c phase finish runs start = true) :
    Lower80889.PhaseRows.RunsValid c phase finish start runs := by
  induction runs generalizing start with
  | nil => exact Nat.eq_of_beq_eq_true h
  | cons run runs ih =>
    change Bool.rec false (phaseRunsK c phase finish runs run.stop) _ = true at h
    cases hb : (Nat.ble run.stop finish && Nat.blt start run.stop && Nat.ble run.witness phase &&
        decide (SourceActive c run.witness start) && decide (SourceCell c run.witness start (run.stop-1)) &&
        Nat.ble (sourceLine c run.witness start) (hereCharge c phase start) &&
        Nat.ble (sourceLine c run.witness (run.stop-1)) (hereCharge c phase (run.stop-1))) with
    | false => rw [hb] at h; exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hb
      exact ⟨h1, ⟨h2, h3, h4, h5, h6, h7⟩, ih _ h⟩

def phaseRunsAtK (runs : Array (List PhaseRun)) (j : ℕ) : List PhaseRun :=
  List.rec (motive := fun _ => ℕ → List PhaseRun) (fun _ => [])
    (fun x _ ih i => Nat.casesOn (motive := fun _ => List PhaseRun) i x (fun j => ih j)) runs.toList j

theorem phaseRunsAtK_eq (runs : Array (List PhaseRun)) (j : ℕ) :
    phaseRunsAtK runs j = (runs[j]?).getD [] := by
  unfold phaseRunsAtK
  rw [← Array.getElem?_toList]
  generalize runs.toList = l
  induction l generalizing j with
  | nil => rfl
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

def phasesK (c : PhaseRowContext) (runs : Array (List PhaseRun)) : Bool :=
  let ph (j : ℕ) := phaseRunsK c j (phaseFinish c j) (phaseRunsAtK runs j) 0
  ph 0 && ph 1 && ph 2 && ph 3 && ph 4 && ph 5 && ph 6 && ph 7 && ph 8 && ph 9

theorem phasesK_sound (c : PhaseRowContext) (runs : Array (List PhaseRun)) (h : phasesK c runs = true) :
    RowRunsValid c runs := by
  simp only [phasesK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  intro j hj
  rw [List.mem_range] at hj
  have hk : ∀ k, phaseRunsK c k (phaseFinish c k) (phaseRunsAtK runs k) 0 = true →
      Lower80889.PhaseRows.RunsValid c k (phaseFinish c k) 0 ((runs[k]?).getD []) := by
    intro k hk
    rw [← phaseRunsAtK_eq]
    exact phaseRunsK_sound _ _ _ _ _ hk
  interval_cases j
  exacts [hk 0 h0, hk 1 h1, hk 2 h2, hk 3 h3, hk 4 h4, hk 5 h5, hk 6 h6, hk 7 h7, hk 8 h8, hk 9 h9]

end Ledger

/-! ## The direct check -/

open MovingFiberReceiptTypes6814

def thresholdAtK (row : Numbers) (j : ℕ) : ℕ := listGetD row.threshold.toList j 10715

def thresholdRunsK (row : Numbers) (j : ℕ) : List Run :=
  List.rec (motive := fun _ => ℕ → List Run) (fun _ => [])
    (fun x _ ih i => Nat.casesOn (motive := fun _ => List Run) i x (fun j => ih j)) row.thresholdRuns.toList j

theorem thresholdAtK_eq (row : Numbers) (j : ℕ) :
    thresholdAtK row j = Lower80889.PhaseRows.thresholdAt row.threshold j := arrGetD_eq _ _ _

theorem thresholdRunsK_eq (row : Numbers) (j : ℕ) :
    thresholdRunsK row j = (row.thresholdRuns[j]?).getD [] := by
  unfold thresholdRunsK
  rw [← Array.getElem?_toList]
  generalize row.thresholdRuns.toList = l
  induction l generalizing j with
  | nil => rfl
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

def thrK (r v : ℕ) (row : Numbers) (j : ℕ) : Bool :=
  thresholdK (Lower80889.TenPhase.sound j).source r v (thresholdAtK row j) (thresholdRunsK row j)

def thresholdsK (r v : ℕ) (row : Numbers) : Bool :=
  thrK r v row 0 && thrK r v row 1 && thrK r v row 2 && thrK r v row 3 &&
    thrK r v row 4 && thrK r v row 5 && thrK r v row 6

theorem thresholdsK_sound (r v : ℕ) (row : Numbers) (h : thresholdsK r v row = true) :
    ThresholdsCore r v row := by
  simp only [thresholdsK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  intro ⟨j, hj⟩
  have hk : ∀ k, thrK r v row k = true → ThresholdValid (Lower80889.TenPhase.sound k).source r v
      (Lower80889.PhaseRows.thresholdAt row.threshold k) ((row.thresholdRuns[k]?).getD []) := by
    intro k hk
    rw [← thresholdAtK_eq, ← thresholdRunsK_eq]
    exact thresholdK_sound _ _ _ _ _ hk
  interval_cases j
  exacts [hk 0 h0, hk 1 h1, hk 2 h2, hk 3 h3, hk 4 h4, hk 5 h5, hk 6 h6]

def coversK (r v : ℕ) (row : Numbers) : Bool :=
  let fin := 10715-r-v
  let cov (j : ℕ) := coverK row.carrier (sheetSlope j) (listGetD (ownRowK j r).toList v 0) r v
    row.threshold fin row.singletons 0
  cov 0 && cov 1 && cov 2 && cov 3 && cov 4 && cov 5 && cov 6 && cov 7

theorem coversK_sound (r v : ℕ) (row : Numbers) (h : coversK r v row = true) :
    ∀ j : Fin 8, MovingFiberSingleCore6814.Cover row.carrier (sheetSlope j.val) (sheetOwn j.val r v) r v
      row.threshold (10715-r-v) 0 row.singletons := by
  simp only [coversK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  intro ⟨j, hj⟩
  have hk : ∀ k, coverK row.carrier (sheetSlope k) (listGetD (ownRowK k r).toList v 0) r v
      row.threshold (10715-r-v) row.singletons 0 = true →
      MovingFiberSingleCore6814.Cover row.carrier (sheetSlope k) (sheetOwn k r v) r v
        row.threshold (10715-r-v) 0 row.singletons := by
    intro k hk
    rw [← ownK_eq]
    exact coverK_sound _ _ _ _ _ _ _ _ _ hk
  interval_cases j
  exacts [hk 0 h0, hk 1 h1, hk 2 h2, hk 3 h3, hk 4 h4, hk 5 h5, hk 6 h6, hk 7 h7]

/-- `∀ j < 10, a[j] ≤ b[j]` (with defaults 0) over the two prefix lists. -/
def prefixLeK (a b : List ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => ih && Nat.ble (listGetD a j 0) (listGetD b j 0))

theorem prefixLeK_sound (a b : Array ℕ) (n : ℕ) (h : prefixLeK a.toList b.toList n = true) :
    ∀ j : Fin n, (a[j.val]?).getD 0 ≤ (b[j.val]?).getD 0 := by
  induction n with
  | zero => intro j; exact j.elim0
  | succ n ih =>
    change (prefixLeK a.toList b.toList n && Nat.ble (listGetD a.toList n 0) (listGetD b.toList n 0)) = true at h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    intro ⟨j, hj⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih h.1 ⟨j, hj⟩
    · rw [← arrGetD_eq, ← arrGetD_eq]; exact h.2

def directChecksK (r v : ℕ) (row parent prior : Numbers) : Bool :=
  decide (row.carrier.Correct r v) && coversK r v row &&
    baseK row.base r v (10715-r-v) row.baseChoices 0 &&
    decide (ThresholdsDup row) && thresholdsK r v row &&
    phasesK (context r v row parent) row.phaseRuns &&
    ledgerK (context r v row parent) row.ledgerRuns 0 &&
    prefixLeK parent.prefixValues.toList row.prefixValues.toList 10 &&
    (Nat.beq v 0 || prefixLeK prior.prefixValues.toList row.prefixValues.toList 10)

theorem directChecksK_sound (r v : ℕ) (row parent prior : Numbers)
    (h : directChecksK r v row parent prior = true) : DirectAt r v row parent prior := by
  simp only [directChecksK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, hcov⟩, hb⟩, hd⟩, ht⟩, hp⟩, hl⟩, hpr⟩, hpv⟩ := h
  refine DirectAt.of_checks ⟨⟨hc, coversK_sound _ _ _ hcov⟩, baseK_sound _ _ _ _ _ _ hb,
    ⟨hd, thresholdsK_sound _ _ _ ht⟩, phasesK_sound _ _ hp, ledgerK_sound _ _ _ hl,
    prefixLeK_sound _ _ _ hpr, ?_⟩
  intro hv
  rcases hpv with hv0 | hpv
  · omega
  · exact prefixLeK_sound _ _ _ hpv

end ProximityPrize.SubmissionLower.Lower80889.DirectKernel

namespace ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814

/-- The receipts' entry point: `DirectAt` from the kernel-fast check. -/
theorem DirectAt.ofK {r v : ℕ} {row parent prior : Numbers}
    (h : Lower80889.DirectKernel.directChecksK r v row parent prior = true) : DirectAt r v row parent prior :=
  Lower80889.DirectKernel.directChecksK_sound r v row parent prior h

end ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814
