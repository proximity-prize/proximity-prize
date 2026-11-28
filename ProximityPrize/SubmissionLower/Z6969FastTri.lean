import ProximityPrize.SubmissionLower.Z6969Pack0558
set_option Elab.async false
set_option maxRecDepth 30000


namespace Research6969.PhysicalWindow.Fast
open Research6966.HelperWindowIntervals (bound cutoff slotLimit)
open Research6966.HelperWindowPrefix (volume)
open Research6966.HelperAvoidance (triSlots)
open Research6966.HelperWindowGrouping (sumCount)

/-! Kernel-friendly evaluator.  Every operation is written with the explicit
`Nat.*` constants so the kernel's GMP acceleration fires without unfolding
`HAdd`/`HMul`/`min`/`ite` instance chains. -/

def mn (x y : ℕ) : ℕ := cond (Nat.ble x y) x y

theorem mn_eq (x y : ℕ) : mn x y = min x y := by
  unfold mn
  by_cases h : x ≤ y
  · simp [Nat.ble_eq_true_of_le h, Nat.min_def, h]
  · have : Nat.ble x y = false := by simpa [Bool.eq_false_iff, Nat.ble_eq] using h
    simp [this, Nat.min_def, h]

def volF (stop B J w : ℕ) : ℕ :=
  cond (Nat.beq stop 0) 0
    (let last := mn B (Nat.div (Nat.sub stop 1) w)
     let n := mn last J
     let len := Nat.sub (mn (Nat.add last 1) J) (Nat.sub (Nat.mul w (Nat.add last 1)) stop)
     let mom := Nat.mul (Nat.mul n (Nat.add n 1)) (Nat.add n 2)
     let r := Nat.sub last n
     Nat.add (Nat.add
      (Nat.div (Nat.sub (Nat.add (Nat.mul (Nat.mul (Nat.mul 3 stop) (Nat.add n 1)) (Nat.add n 2)) mom)
         (Nat.mul (Nat.mul 2 w) mom)) 6)
      (Nat.div (Nat.sub (Nat.mul r (Nat.add (Nat.mul (Nat.mul 2 stop) (Nat.add J 1)) (Nat.mul J (Nat.add J 1))))
         (Nat.mul (Nat.mul (Nat.mul w (Nat.add J 1)) (Nat.add (Nat.add last n) 1)) r)) 2))
      (cond (Nat.ble (Nat.add last 1) B) (Nat.div (Nat.mul len (Nat.add len 1)) 2) 0))

theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem volF_eq (stop B J w : ℕ) : volF stop B J w = volume stop B J w := by
  unfold volF Research6966.HelperWindowPrefix.volume
  simp only [mn_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, nat_div_eq]
  by_cases h0 : stop = 0
  · simp [h0]
  · have : Nat.beq stop 0 = false := by simpa [Bool.eq_false_iff, Nat.beq_eq] using h0
    simp only [this, h0, Bool.cond_false, ite_false]
    by_cases hl : min B ((stop-1)/w) < B
    · have : Nat.ble (min B ((stop-1)/w) + 1) B = true := by simpa using hl
      simp only [this, hl, Bool.cond_true, ite_true]
      rfl
    · have : Nat.ble (min B ((stop-1)/w) + 1) B = false := by simpa [Bool.eq_false_iff, Nat.ble_eq] using hl
      simp only [this, hl, Bool.cond_false, ite_false]
      rfl


def triF (n : ℕ) : ℕ := Nat.div (Nat.mul (Nat.add n 1) (Nat.add n 2)) 2

/-- layer term with an abstract slot function `sl` (evaluated at `k+1`). -/
def termG (sl : ℕ → ℕ) (B J reserve lo hi a b wt c w k : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul (Nat.add k 1) a) B && Nat.ble (Nat.mul (Nat.add k 1) b) J)
    (let stop := Nat.sub (Nat.sub c (Nat.mul (Nat.mul 2 lo) k)) (Nat.mul (Nat.add k 1) wt)
     let B2 := Nat.sub B (Nat.mul (Nat.add k 1) a)
     let J2 := Nat.sub J (Nat.mul (Nat.add k 1) b)
     Nat.mul (Nat.sub (volF stop B2 J2 w) (volF (Nat.sub stop (Nat.mul 2 hi)) B2 J2 w))
       (sl (Nat.add k 1))) 0

def boundG (sl : ℕ → ℕ) (m B J reserve lo hi a b wt limit : ℕ) : ℕ :=
  let w := Nat.sub 131071 hi
  let c := Nat.sub (Nat.mul m 179730) (Nat.mul (Nat.mul 2 lo) reserve)
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.add acc (termG sl B J reserve lo hi a b wt c w k)) limit

def limF (J U seed : ℕ) : ℕ := cond (Nat.beq seed 0) J (mn J (Nat.div U seed))

def slotT (U seed j : ℕ) : ℕ := cond (Nat.ble (Nat.mul j seed) U) (triF (Nat.sub U (Nat.mul j seed))) 0

def slotR (CAP v seed j : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul j seed) v)
    (Nat.mul (Nat.add (Nat.sub CAP v) 1) (Nat.add (Nat.sub v (Nat.mul j seed)) 1)) 0

theorem rec_eq (g f : ℕ → ℕ) (h : ∀ k, g k = f k) (n : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.add acc (g k)) n = sumCount f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.add _ _ = sumCount f n + f n
    rw [← h n]; exact congrArg (· + g n) ih

theorem limF_eq (s : K1_14.Shape) (u : ℕ) (U : ℕ) :
    limF s.J U u = slotLimit s U u := by
  unfold limF slotLimit
  by_cases h : u = 0
  · simp [h]
  · have : Nat.beq u 0 = false := by simpa [Bool.eq_false_iff, Nat.beq_eq] using h
    simp [this, h, mn_eq, nat_div_eq]

theorem boundG_eq (s : K1_14.Shape) (sl : ℕ → ℕ) (slots : ℕ → ℕ)
    (hs : ∀ j, sl (j+1) = slots (j+1)) (reserve lo hi a b wt limit : ℕ) :
    boundG sl s.m s.B s.J reserve lo hi a b wt limit =
      bound s agreement reserve lo hi a b wt limit slots := by
  unfold boundG Research6966.HelperWindowIntervals.bound
  apply rec_eq
  intro k
  unfold termG Research6966.HelperWindowIntervals.layerBound
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, nat_div_eq, Research6966.HelperWindowIntervals.cutoff, volF_eq,
    hs]
  by_cases h1 : (k+1)*a ≤ s.B <;> by_cases h2 : (k+1)*b ≤ s.J <;>
    simp [h1, h2, Nat.ble_eq, agreement]

theorem slotT_eq (U seed j : ℕ) : slotT U seed j = triSlots U seed j := by
  unfold slotT triSlots K1_14.triangle triF
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, nat_div_eq]
  by_cases h : j*seed ≤ U <;> simp [h, Nat.ble_eq]

theorem slotR_eq (CAP v seed j : ℕ) :
    slotR CAP v seed j = Research6966.HelperAvoidance.rectSlots (Research6966.HelperWindowIntervals.box CAP v)
      (Research6966.HelperWindowIntervals.axis seed) j := by
  unfold slotR Research6966.HelperAvoidance.rectSlots KoalaRect.area
    Research6966.HelperWindowIntervals.box Research6966.HelperWindowIntervals.axis
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, nat_div_eq]
  by_cases h : j*seed ≤ v
  · have : ∀ z : Fin 2, j * (![0, seed] : Fin 2 → ℕ) z ≤ (![CAP - v, v] : Fin 2 → ℕ) z := by
      intro z; fin_cases z <;> simp [h]
    simp [h, this, Nat.ble_eq]
  · have : ¬ ∀ z : Fin 2, j * (![0, seed] : Fin 2 → ℕ) z ≤ (![CAP - v, v] : Fin 2 → ℕ) z := by
      intro hz; exact h (by simpa using hz 1)
    simp [h, this, Nat.ble_eq]

def TF (m B J U rows pole reserve jet slope weight seed lo hi : ℕ) : Bool :=
  Nat.blt
    (Nat.add (Nat.add (Nat.mul (triF U) rows) (Nat.mul (Nat.mul hi (Nat.mul 2 (Nat.add U 1))) pole))
      (boundG (slotT U seed) m B J reserve lo hi jet slope weight (limF J U seed)))
    (Nat.mul (triF U)
      (volF (Nat.sub (Nat.mul m 179730) (Nat.mul (Nat.mul 2 hi) reserve)) B J (Nat.sub 131071 lo)))

/-- Rectangle certificate; `v` is the width. -/
def RF (m B J U v rows pole reserve jet slope weight seed lo hi : ℕ) : Bool :=
  Nat.blt
    (Nat.add (Nat.add (Nat.mul (Nat.mul (Nat.add (Nat.sub U v) 1) (Nat.add v 1)) rows)
        (Nat.mul (Nat.mul hi (Nat.add (Nat.add (Nat.sub U v) v) 2)) pole))
      (boundG (slotR U v seed) m B J reserve lo hi jet slope weight (limF J v seed)))
    (Nat.mul (Nat.mul (Nat.add (Nat.sub U v) 1) (Nat.add v 1))
      (volF (Nat.sub (Nat.mul m 179730) (Nat.mul (Nat.mul 2 hi) reserve)) B J (Nat.sub 131071 lo)))

/-! CUT3: branch-free evaluator.  `mn x y = x - (x - y)` and `ble`-flags written as `1 - (a - b)`
avoid `cond` unfolding in the kernel; the slot test and the activity flags are removed by capping the loop
at `capL`. -/

def mnA (x y : ℕ) : ℕ := Nat.sub x (Nat.sub x y)

theorem mnA_eq (x y : ℕ) : mnA x y = mn x y := by
  rw [mn_eq]; unfold mnA; simp only [Nat.sub_eq]; omega

def volA (stop B J w : ℕ) : ℕ :=
  let last := mnA B (Nat.div (Nat.sub stop 1) w)
  let n := mnA last J
  let l1 := Nat.add last 1
  let len := Nat.sub (mnA l1 J) (Nat.sub (Nat.mul w l1) stop)
  let mom := Nat.mul (Nat.mul n (Nat.add n 1)) (Nat.add n 2)
  let r := Nat.sub last n
  let J1 := Nat.add J 1
  Nat.mul (Nat.sub 1 (Nat.sub 1 stop)) (Nat.add (Nat.add
      (Nat.div (Nat.sub (Nat.add (Nat.mul (Nat.mul (Nat.mul 3 stop) (Nat.add n 1)) (Nat.add n 2)) mom)
         (Nat.mul (Nat.mul 2 w) mom)) 6)
      (Nat.div (Nat.sub (Nat.mul r (Nat.add (Nat.mul (Nat.mul 2 stop) J1) (Nat.mul J J1)))
         (Nat.mul (Nat.mul (Nat.mul w J1) (Nat.add (Nat.add last n) 1)) r)) 2))
      (Nat.mul (Nat.sub 1 (Nat.sub l1 B)) (Nat.div (Nat.mul len (Nat.add len 1)) 2)))

theorem volA_eq (stop B J w : ℕ) : volA stop B J w = volF stop B J w := by
  unfold volA volF
  simp only [mnA_eq]
  by_cases h0 : stop = 0
  · subst h0; simp
  · have hb : Nat.beq stop 0 = false := by simpa [Bool.eq_false_iff, Nat.beq_eq] using h0
    have h1 : Nat.sub 1 (Nat.sub 1 stop) = 1 := by simp only [Nat.sub_eq]; omega
    simp only [hb, h1, Bool.cond_false, Nat.mul_eq, Nat.one_mul]
    generalize mn B (Nat.div (Nat.sub stop 1) w) = L
    by_cases hl : L + 1 ≤ B
    · have h2 : Nat.sub 1 (Nat.sub (Nat.add L 1) B) = 1 := by
        simp only [Nat.sub_eq, Nat.add_eq]; omega
      have h3 : Nat.ble (Nat.add L 1) B = true := by simpa [Nat.ble_eq] using hl
      simp only [h2, h3, Nat.one_mul, Bool.cond_true]
    · have h2 : Nat.sub 1 (Nat.sub (Nat.add L 1) B) = 0 := by
        simp only [Nat.sub_eq, Nat.add_eq]; omega
      have h3 : Nat.ble (Nat.add L 1) B = false := by
        simpa [Bool.eq_false_iff, Nat.ble_eq] using hl
      simp only [h2, h3, Nat.zero_mul, Bool.cond_false]

def lp (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.add acc (f k)) n

theorem lp_congr (f g : ℕ → ℕ) (n : ℕ) (h : ∀ k, k < n → g k = f k) : lp g n = lp f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.add (lp g n) (g n) = Nat.add (lp f n) (f n)
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

theorem lp_trunc (f : ℕ → ℕ) (n : ℕ) : ∀ N, n ≤ N → (∀ k, n ≤ k → k < N → f k = 0) → lp f N = lp f n := by
  intro N
  induction N with
  | zero => intro h _; have : n = 0 := by omega
            subst this; rfl
  | succ N ih =>
    intro h hz
    by_cases hn : n = N + 1
    · subst hn; rfl
    · show Nat.add (lp f N) (f N) = lp f n
      rw [hz N (by omega) (by omega), ih (by omega) (fun k a b => hz k a (by omega))]; rfl

def termB (U seed B J lo hi a b wt c w k : ℕ) : ℕ :=
  let k1 := Nat.add k 1
  let stop := Nat.sub (Nat.sub c (Nat.mul (Nat.mul 2 lo) k)) (Nat.mul k1 wt)
  let B2 := Nat.sub B (Nat.mul k1 a)
  let J2 := Nat.sub J (Nat.mul k1 b)
  Nat.mul (Nat.sub (volA stop B2 J2 w) (volA (Nat.sub stop (Nat.mul 2 hi)) B2 J2 w))
    (triF (Nat.sub U (Nat.mul k1 seed)))

def capL (limit B J a b : ℕ) : ℕ :=
  mn (mn limit (cond (Nat.beq a 0) limit (Nat.div B a))) (cond (Nat.beq b 0) limit (Nat.div J b))

def TFB (m B J U rows pole reserve jet slope weight seed lo hi : ℕ) : Bool :=
  Nat.blt
    (Nat.add (Nat.add (Nat.mul (triF U) rows) (Nat.mul (Nat.mul hi (Nat.mul 2 (Nat.add U 1))) pole))
      (lp (termB U seed B J lo hi jet slope weight
          (Nat.sub (Nat.mul m 179730) (Nat.mul (Nat.mul 2 lo) reserve)) (Nat.sub 131071 hi))
        (capL (limF J U seed) B J jet slope)))
    (Nat.mul (triF U)
      (volA (Nat.sub (Nat.mul m 179730) (Nat.mul (Nat.mul 2 hi) reserve)) B J (Nat.sub 131071 lo)))

theorem capL_le (limit B J a b : ℕ) : capL limit B J a b ≤ limit := by
  unfold capL; rw [mn_eq, mn_eq]
  have : min limit (cond (Nat.beq a 0) limit (Nat.div B a)) ≤ limit := Nat.min_le_left _ _
  exact le_trans (Nat.min_le_left _ _) this

theorem capL_lt (limit B J a b k : ℕ) (hk : k < capL limit B J a b) :
    (k + 1) * a ≤ B ∧ (k + 1) * b ≤ J := by
  unfold capL at hk; rw [mn_eq, mn_eq] at hk
  rw [lt_min_iff, lt_min_iff] at hk
  obtain ⟨⟨_, h1⟩, h2⟩ := hk
  constructor
  · by_cases ha : a = 0
    · subst ha; simp
    · have hb : Nat.beq a 0 = false := by simpa [Bool.eq_false_iff, Nat.beq_eq] using ha
      rw [hb] at h1; simp only [Bool.cond_false, nat_div_eq] at h1
      exact (Nat.le_div_iff_mul_le (by omega)).mp h1 |>.trans' (by rw [Nat.mul_comm]) |> fun h => by
        have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero ha)).mp (by omega : k + 1 ≤ B / a)
        exact this
  · by_cases hb0 : b = 0
    · subst hb0; simp
    · have hb : Nat.beq b 0 = false := by simpa [Bool.eq_false_iff, Nat.beq_eq] using hb0
      rw [hb] at h2; simp only [Bool.cond_false, nat_div_eq] at h2
      exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb0)).mp (by omega : k + 1 ≤ J / b)

theorem capL_ge (limit B J a b k : ℕ) (hk : capL limit B J a b ≤ k) (hl : k < limit) :
    ¬ ((k + 1) * a ≤ B ∧ (k + 1) * b ≤ J) := by
  unfold capL at hk; rw [mn_eq, mn_eq] at hk
  intro ⟨h1, h2⟩
  rw [min_le_iff, min_le_iff] at hk
  rcases hk with (hk | hk) | hk
  · omega
  · by_cases ha : a = 0
    · subst ha; simp at hk; omega
    · have hb : Nat.beq a 0 = false := by simpa [Bool.eq_false_iff, Nat.beq_eq] using ha
      rw [hb] at hk; simp only [Bool.cond_false, nat_div_eq] at hk
      have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero ha)).mpr h1
      omega
  · by_cases hb0 : b = 0
    · subst hb0; simp at hk; omega
    · have hb : Nat.beq b 0 = false := by simpa [Bool.eq_false_iff, Nat.beq_eq] using hb0
      rw [hb] at hk; simp only [Bool.cond_false, nat_div_eq] at hk
      have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb0)).mpr h2
      omega

theorem termB_eq (U seed B J reserve lo hi a b wt c w k : ℕ) (h1 : (k + 1) * a ≤ B) (h2 : (k + 1) * b ≤ J)
    (h3 : (k + 1) * seed ≤ U) :
    termB U seed B J lo hi a b wt c w k = termG (slotT U seed) B J reserve lo hi a b wt c w k := by
  unfold termB termG slotT
  have e1 : Nat.ble (Nat.mul (Nat.add k 1) a) B = true := by simpa [Nat.ble_eq] using h1
  have e2 : Nat.ble (Nat.mul (Nat.add k 1) b) J = true := by simpa [Nat.ble_eq] using h2
  have e3 : Nat.ble (Nat.mul (Nat.add k 1) seed) U = true := by simpa [Nat.ble_eq] using h3
  simp only [e1, e2, e3, Bool.and_self, Bool.cond_true, volA_eq]

theorem termG_zero (U seed B J reserve lo hi a b wt c w k : ℕ) (h : ¬ ((k + 1) * a ≤ B ∧ (k + 1) * b ≤ J)) :
    termG (slotT U seed) B J reserve lo hi a b wt c w k = 0 := by
  unfold termG
  have : (Nat.ble (Nat.mul (Nat.add k 1) a) B && Nat.ble (Nat.mul (Nat.add k 1) b) J) = false := by
    by_contra hh
    apply h
    have hh' : (Nat.ble (Nat.mul (Nat.add k 1) a) B && Nat.ble (Nat.mul (Nat.add k 1) b) J) = true := by simpa using hh
    simp only [Bool.and_eq_true, Nat.ble_eq] at hh'
    exact hh'
  simp only [this, Bool.cond_false]

theorem limF_slot (J U seed k : ℕ) (hk : k < limF J U seed) : (k + 1) * seed ≤ U := by
  unfold limF at hk
  by_cases h : seed = 0
  · subst h; simp
  · have hb : Nat.beq seed 0 = false := by simpa [Bool.eq_false_iff, Nat.beq_eq] using h
    rw [hb] at hk; simp only [Bool.cond_false, mn_eq, nat_div_eq] at hk
    have : k < U / seed := lt_of_lt_of_le hk (Nat.min_le_right _ _)
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero h)).mp (by omega)

theorem TFB_eq (m B J U rows pole reserve jet slope weight seed lo hi : ℕ) :
    TFB m B J U rows pole reserve jet slope weight seed lo hi =
      TF m B J U rows pole reserve jet slope weight seed lo hi := by
  have key : lp (termB U seed B J lo hi jet slope weight
          (Nat.sub (Nat.mul m 179730) (Nat.mul (Nat.mul 2 lo) reserve)) (Nat.sub 131071 hi))
        (capL (limF J U seed) B J jet slope) =
      boundG (slotT U seed) m B J reserve lo hi jet slope weight (limF J U seed) := by
    unfold boundG
    show lp _ _ = lp (fun k => termG (slotT U seed) B J reserve lo hi jet slope weight _ _ k) _
    refine Eq.trans ?_ (lp_trunc _ (capL (limF J U seed) B J jet slope) (limF J U seed)
      (capL_le _ _ _ _ _) (fun k h1 h2 => termG_zero _ _ _ _ _ _ _ _ _ _ _ _ _
        (capL_ge (limF J U seed) B J jet slope k h1 h2))).symm
    apply lp_congr
    intro k hk
    obtain ⟨c1, c2⟩ := capL_lt _ _ _ _ _ _ hk
    exact termB_eq _ _ _ _ _ _ _ _ _ _ _ _ _ c1 c2 (limF_slot _ _ _ _ (lt_of_lt_of_le hk (capL_le _ _ _ _ _)))
  unfold TFB TF
  rw [key, volA_eq]

end Research6969.PhysicalWindow.Fast

namespace Research6969.PhysicalWindow
open Fast

/-- Kernel-fast certificate for `Triangular`. -/
theorem triangular_of_fast (b : Request) (lo hi : ℕ)
    (h : TFB b.shape.m b.shape.B b.shape.J b.shape.U b.bank.nodeRows b.bank.poleMoment
      b.reserve b.jet b.slope b.weight b.seed lo hi = true) : Triangular b lo hi := by
  rw [TFB_eq] at h
  unfold TF at h
  rw [Nat.blt_eq] at h
  unfold Triangular
  rw [boundG_eq b.shape _ (Research6966.HelperAvoidance.triSlots b.shape.U b.seed) (fun j => slotT_eq _ _ _), limF_eq] at h
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, nat_div_eq, volF_eq, triF] at h
  simp only [Request.top, Request.limit, Request.shape] at *
  simpa [K1_14.triangle, Research6966.HelperWindowIntervals.cutoff, agreement, Nat.mul_assoc] using h

/-- Kernel-fast certificate for `Rectangle`. -/
theorem rectangle_of_fast (b : Request) (width lo hi : ℕ)
    (h : RF b.shape.m b.shape.B b.shape.J b.shape.U width b.bank.nodeRows b.bank.poleMoment
      b.reserve b.jet b.slope b.weight b.seed lo hi = true) : Rectangle b width lo hi := by
  unfold RF at h
  rw [Nat.blt_eq] at h
  unfold Rectangle
  rw [boundG_eq b.shape _ _ (fun j => slotR_eq _ _ _ _), limF_eq] at h
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, nat_div_eq, volF_eq] at h
  simp only [Request.top, Request.limit, Request.shape, Research6966.HelperWindowIntervals.box,
    KoalaRect.area] at *
  simpa [Research6966.HelperWindowIntervals.cutoff, agreement, Nat.mul_assoc] using h

end Research6969.PhysicalWindow
