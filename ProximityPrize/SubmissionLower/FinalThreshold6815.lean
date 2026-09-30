import ProximityPrize.SubmissionLower.MovingFiberThresholdClosed6815
namespace ProximityPrize.SubmissionLower.FinalThreshold6815
open Lower80899.CompressedBand Lower80899.BandPolynomial Lower80899.Oracle Lower80899.ThresholdFast
open LocatorPhase6800Oracle (rawFlag)
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 100000

def minK (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

theorem minK_eq (a b : ℕ) : minK a b = min a b := by
  unfold minK
  by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h, min_eq_left h]; rfl
  · rw [show Nat.ble a b = false from Bool.eq_false_iff.mpr (fun hb => h (Nat.le_of_ble_eq_true hb)),
      min_eq_right (by omega)]; rfl

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
  thinLoopK 131071 50175 (contactDec p) (total p) (middle p) p.all (s.fuel p)
    (s.contactCap p) (s.totalCap - total p) (s.middleCap - middle p) (s.slopeCap - p.all)

theorem bandThinK_eq (s : SourceNumbers) (p : FlagDegree) : bandThinK s p = evalBandThin s p :=
  thinLoopK_eq _ _ _ _ _ _ _ _ _ _ _

def fastK (s : SourceNumbers) (r v threshold : ℕ) : Bool :=
  Nat.blt (11192-(r+v)) threshold ||
    (let p := rawFlag r v threshold
     Nat.ble 1 p.all && Nat.ble (total p) s.totalCap && Nat.ble (middle p) s.middleCap &&
       Nat.ble p.all s.slopeCap && Nat.blt (bandThinK s p) s.gap)

theorem fastK_sound (s : SourceNumbers) (r v threshold : ℕ) (h : fastK s r v threshold = true) :
    FastSourceThresholdSufficient s r v threshold := by
  simp only [fastK, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, bandThinK_eq] at h
  rcases h with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, h4, Or.inl h5⟩

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

def zlt (a b : ℤ) : Bool := Int.casesOn (motive := fun _ => Bool) (b - a) (fun k => Nat.ble 1 k) (fun _ => false)

theorem zlt_sound (a b : ℤ) (h : zlt a b = true) : a < b := by
  unfold zlt at h
  rcases hb : b - a with k | k <;> rw [hb] at h
  · have hk : 1 ≤ k := Nat.le_of_ble_eq_true h
    rw [Int.ofNat_eq_natCast] at hb
    omega
  · exact absurd h Bool.false_ne_true

def sufficientK (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) : Bool :=
  Nat.blt (11192-(r+v)) threshold ||
    (let p := rawFlag r v threshold
     Nat.ble 1 p.all && Nat.ble (total p) s.totalCap && Nat.ble (middle p) s.middleCap &&
       Nat.ble p.all s.slopeCap && runsValidK (ofSource s p) runs 0 &&
       zlt (50175*runsUpperK (ofSource s p) runs 0) ((s.gap*162125875761905592 : ℕ) : ℤ))

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

def thresholdK (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) : Bool :=
  sufficientK s r v threshold runs || fastK s r v threshold

theorem thresholdK_sound (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run)
    (h : thresholdK s r v threshold runs = true) :
    FastSourceThresholdSufficient s r v threshold := by
  simp only [thresholdK, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Lower80899.CompressedBand.sufficient_sound s r v threshold runs (sufficientK_sound _ _ _ _ _ h)
  · exact fastK_sound _ _ _ _ h

end ProximityPrize.SubmissionLower.FinalThreshold6815
