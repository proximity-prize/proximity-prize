import ProximityPrize.SubmissionLower.FadicVar

set_option autoImplicit false
namespace KoalaFarBridge
open FadicGate (Entry)

abbrev FeeBox:=ℕ × ℕ × ℕ

structure GateRate where
  b:ℕ
  j:ℕ
  t:ℕ
  sep:ℕ
  unit:ℕ
  split:ℕ
  bl:ℕ
  jl:ℕ
  tl:ℕ
  deriving DecidableEq

def boxFee (g : GateRate) (z : FeeBox) : ℕ :=
  g.b*max z.1 z.2.1+g.j*z.2.1+g.t*min z.2.2 (z.2.1/3)

def residual (g : GateRate) (z : FeeBox) (a : ℕ) : FeeBox :=
  (z.1-a*g.bl,z.2.1-a*g.jl,z.2.2-a*g.tl)

def maxDepth (g : GateRate) (z : FeeBox) : ℕ :=
  min (z.1/g.bl) (min (z.2.1/g.jl) (z.2.2/g.tl))

def localLength (r a d e:ℕ):ℕ:=e*(24*(r-e*a)+d*(e-1))

private def chargeCheckRange (g : GateRate) (r a : ℕ) (z : FeeBox) (d : ℕ) : Bool :=
  (List.range g.split).all fun k =>
    let e:=k+1
    let len:=localLength r a d e
    decide (0 < len ∧ (g.split+1-e)*(24*boxFee g z+d*g.sep)≤g.split*g.unit*len)

private theorem charge_of_range (g : GateRate) {r a d e : ℕ} {z : FeeBox}
    (h:chargeCheckRange g r a z d=true) (he:1≤e) (hs:e≤g.split) :
    0 < localLength r a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep)≤g.split*g.unit*localLength r a d e:=by
  unfold chargeCheckRange at h
  have hi:e-1 ∈ List.range g.split:=List.mem_range.mpr (by omega)
  have hv:=of_decide_eq_true (List.all_eq_true.mp h (e-1) hi)
  simpa only [Nat.sub_add_cancel he] using hv

private abbrev chargeAt (n unit fee r a d e : ℕ) : Prop :=
  0 < localLength r a d e ∧ (n + 1 - e) * fee ≤ n * unit * localLength r a d e

private theorem chargeAt_of_length {n unit fee r a d i e : ℕ}
    (hie : i ≤ e) (hL : localLength r a d i ≤ localLength r a d e)
    (hi : chargeAt n unit fee r a d i) : chargeAt n unit fee r a d e := by
  refine ⟨hi.1.trans_le hL, ?_⟩
  exact (Nat.mul_le_mul_right fee (show n + 1 - e ≤ n + 1 - i by omega)).trans
    (hi.2.trans (Nat.mul_le_mul_left _ hL))

private def quadratic (c b k x : ℤ) : ℤ := c*x*x + b*x + k

-- Multiply the secant inequality by the length of the interval.
private theorem quadratic_nonneg {c b k x y : ℤ}
    (hc : c ≤ 0) (hx : 1 ≤ x) (hy : x ≤ y)
    (h1 : 0 ≤ quadratic c b k 1) (h2 : 0 ≤ quadratic c b k y) :
    0 ≤ quadratic c b k x := by
  by_cases heq : y = 1
  · have hxeq : x = 1 := by omega
    simpa only [hxeq] using h1
  have hw : 0 < y - 1 := by omega
  have hgap : 0 ≤ (-c) * (x-1) * (y-x) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have hweighted := mul_nonneg hw.le hgap
  have hleft := mul_nonneg (show 0 ≤ y-x by omega) h1
  have hright := mul_nonneg (show 0 ≤ x-1 by omega) h2
  have hsec : (y-1) * quadratic c b k x =
      (y-x) * quadratic c b k 1 + (x-1) * quadratic c b k y +
        (y-1) * ((-c) * (x-1) * (y-x)) := by
    unfold quadratic
    ring
  by_contra h
  have hneg : (y-1) * quadratic c b k x < 0 := mul_neg_of_pos_of_neg hw (by omega)
  omega

private theorem length_pre {r a d e : ℕ} (he : 1 ≤ e) (her : e*a ≤ r) :
    (localLength r a d e : ℤ) =
      quadratic ((d : ℤ)-24*a) (24*(r : ℤ)-d) 0 e := by
  unfold localLength quadratic
  push_cast [Nat.cast_sub her, Nat.cast_sub he]
  ring

private theorem charge_pre_iff {n unit fee r a d e : ℕ}
    (he : 1 ≤ e) (hn : e ≤ n) (her : e*a ≤ r) :
    chargeAt n unit fee r a d e ↔
      0 ≤ quadratic ((d : ℤ)-24*a) (24*(r : ℤ)-d) (-1) e ∧
      0 ≤ quadratic ((n : ℤ)*unit*((d : ℤ)-24*a))
        ((n : ℤ)*unit*(24*(r : ℤ)-d)+fee) (-((n : ℤ)+1)*fee) e := by
  have hL := length_pre (d := d) he her
  have hP : quadratic ((d : ℤ)-24*a) (24*(r : ℤ)-d) (-1) e =
      (localLength r a d e : ℤ) - 1 := by
    rw [hL]
    unfold quadratic
    ring
  have hF : quadratic ((n : ℤ)*unit*((d : ℤ)-24*a))
      ((n : ℤ)*unit*(24*(r : ℤ)-d)+fee) (-((n : ℤ)+1)*fee) e =
      ((n * unit * localLength r a d e : ℕ) : ℤ) - (((n+1-e)*fee : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (show e ≤ n+1 by omega)]
    rw [hL]
    unfold quadratic
    ring
  simp only [hP, hF, sub_nonneg]
  have hp : 0 < localLength r a d e ↔ 1 ≤ (localLength r a d e : ℤ) := by
    omega
  unfold chargeAt
  rw [← hp]
  norm_cast

private theorem charge_pre {n unit fee r a d m e : ℕ}
    (he : 1 ≤ e) (hm : e ≤ m) (hN : m ≤ n) (hr : m*a ≤ r)
    (h1 : chargeAt n unit fee r a d 1) (hM : chargeAt n unit fee r a d m) :
    chargeAt n unit fee r a d e := by
  have hma : 1 ≤ m := he.trans hm
  have ham : a ≤ m*a := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right a hma
  have ha : a ≤ r := ham.trans hr
  have hEr := (Nat.mul_le_mul_right a hm).trans hr
  by_cases h : d ≤ 24*a
  · have h1' := (charge_pre_iff (by decide) (hma.trans hN) (by simpa using ha)).mp h1
    have hM' := (charge_pre_iff hma hN hr).mp hM
    have hc : (d : ℤ)-24*a ≤ 0 := by omega
    have hw : 0 ≤ (n : ℤ)*unit := by positivity
    have hwc : (n : ℤ)*unit*((d : ℤ)-24*a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hw hc
    have hEi : (1 : ℤ) ≤ e := by exact_mod_cast he
    have hMi : (e : ℤ) ≤ m := by exact_mod_cast hm
    exact (charge_pre_iff he (hm.trans hN) hEr).mpr
      ⟨quadratic_nonneg hc hEi hMi h1'.1 hM'.1,
        quadratic_nonneg hwc hEi hMi h1'.2 hM'.2⟩
  · apply chargeAt_of_length he _ h1
    have h1L := length_pre (d := d) (e := 1) (by decide) (by simpa using ha)
    have heL := length_pre (d := d) he hEr
    have hEi : (1 : ℤ) ≤ e := by exact_mod_cast he
    have hc : 0 ≤ (d : ℤ)-24*a := by omega
    have hb : 0 ≤ 24*((r : ℤ)-a) := by omega
    have hgap₁ := mul_nonneg (show 0 ≤ (e : ℤ)-1 by omega) hb
    have hgap₂ := mul_nonneg
      (mul_nonneg (show 0 ≤ (e : ℤ) by positivity) hc)
      (show 0 ≤ (e : ℤ)-1 by omega)
    have hdiff : (localLength r a d e : ℤ) - (localLength r a d 1 : ℤ) =
        ((e : ℤ)-1)*(24*((r : ℤ)-a)) + (e : ℤ)*((d : ℤ)-24*a)*((e : ℤ)-1) := by
      rw [heL, h1L]
      unfold quadratic
      push_cast
      ring
    have hLe : (localLength r a d 1 : ℤ) ≤ (localLength r a d e : ℤ) := by omega
    exact_mod_cast hLe

private theorem length_sat_mono {r a d i e : ℕ} (hie : i ≤ e) (hi : r ≤ i*a) :
    localLength r a d i ≤ localLength r a d e := by
  have he : r ≤ e*a := hi.trans (Nat.mul_le_mul_right a hie)
  simp only [localLength, Nat.sub_eq_zero_of_le hi, Nat.sub_eq_zero_of_le he,
    Nat.mul_zero, Nat.zero_add]
  gcongr

private def chargeCut (n r a : ℕ) : ℕ := if a = 0 then n else max 1 (min n (r/a))

private def chargeTest (n unit fee r a d e : ℕ) : Bool :=
  let len := Nat.mul e (Nat.add (Nat.mul 24 (Nat.sub r (Nat.mul e a)))
    (Nat.mul d (Nat.sub e 1)))
  Nat.blt 0 len &&
    Nat.ble (Nat.mul (Nat.sub (Nat.add n 1) e) fee) (Nat.mul (Nat.mul n unit) len)

private theorem chargeTest_true (n unit fee r a d e : ℕ) :
    chargeTest n unit fee r a d e = true ↔ chargeAt n unit fee r a d e := by
  simp only [chargeTest, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.mul_eq,
    Nat.add_eq, Nat.sub_eq, chargeAt, localLength]

/-- Check the first index, the last index before saturation, and its successor. -/
def chargeCheck (g : GateRate) (r a : ℕ) (z : FeeBox) (d : ℕ) : Bool :=
  if g.split = 0 then true else
    let m := chargeCut g.split r a
    let fee := 24*boxFee g z+d*g.sep
    (chargeTest g.split g.unit fee r a d 1 &&
      chargeTest g.split g.unit fee r a d m) &&
      chargeTest g.split g.unit fee r a d (min g.split (m+1))

private theorem chargeCheckRange_eq (g : GateRate) (r a : ℕ) (z : FeeBox) (d : ℕ) :
    chargeCheckRange g r a z d = chargeCheck g r a z d := by
  let n := g.split
  let fee := 24*boxFee g z+d*g.sep
  let m := chargeCut n r a
  let j := min n (m+1)
  by_cases hn : n = 0
  · have hz : g.split = 0 := hn
    simp [chargeCheckRange, chargeCheck, hz]
  have hm : 1 ≤ m ∧ m ≤ n := by
    unfold m chargeCut
    split <;> omega
  have hj : 1 ≤ j ∧ j ≤ n := by unfold j; omega
  have hs : g.split ≠ 0 := hn
  simp only [chargeCheck, if_neg hs]
  change chargeCheckRange g r a z d =
    ((chargeTest n g.unit fee r a d 1 &&
      chargeTest n g.unit fee r a d m) &&
      chargeTest n g.unit fee r a d j)
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, chargeTest_true]
  constructor
  · intro h
    exact ⟨⟨charge_of_range g h (by decide) (by omega),
      charge_of_range g h hm.1 hm.2⟩, charge_of_range g h hj.1 hj.2⟩
  · rintro ⟨⟨h1, hM⟩, hJ⟩
    have ha : a ≤ r := by
      by_contra h
      have hz : r - a = 0 := by omega
      have hpos := h1.1
      simp [localLength, hz] at hpos
    have hmr : m*a ≤ r := by
      by_cases h : a = 0
      · simp [h]
      · have hap : 0 < a := by omega
        have hdiv : 1 ≤ r/a := (Nat.le_div_iff_mul_le hap).mpr (by simpa using ha)
        have hcut : m = min n (r/a) := by
          unfold m chargeCut
          rw [if_neg h, max_eq_right (by omega)]
        rw [hcut]
        exact (Nat.le_div_iff_mul_le hap).mp (min_le_right _ _)
    unfold chargeCheckRange
    apply List.all_eq_true.mpr
    intro k hk
    have hk' : k < n := List.mem_range.mp hk
    let e := k+1
    have he : 1 ≤ e := by dsimp [e]; omega
    have hE : e ≤ n := by dsimp [e]; omega
    change decide (chargeAt n g.unit fee r a d e) = true
    rw [decide_eq_true_eq]
    by_cases hem : e ≤ m
    · exact charge_pre he hem hm.2 hmr h1 hM
    · have hje : j ≤ e := by unfold j; omega
      have hjr : r ≤ j*a := by
        by_cases h : a = 0
        · have hcut : m = n := by simp [m, chargeCut, h]
          omega
        · have hcut : m = max 1 (min n (r/a)) := by simp [m, chargeCut, h]
          have hc : r/a < j := by unfold j; omega
          exact ((Nat.div_lt_iff_lt_mul (show 0 < a by omega)).mp hc).le
      exact chargeAt_of_length hje (length_sat_mono hje hjr) hJ

theorem charge_of_check (g : GateRate) {r a d e : ℕ} {z : FeeBox}
    (h : chargeCheck g r a z d = true) (he : 1 ≤ e) (hs : e ≤ g.split) :
    0 < localLength r a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep)≤g.split*g.unit*localLength r a d e := by
  rw [← chargeCheckRange_eq] at h
  exact charge_of_range g h he hs

def plainCheck (g : GateRate) (r : ℕ) (z : FeeBox) (ds : List ℕ) : Bool :=
  (List.range (maxDepth g z+1)).all fun a => chargeCheck g r a (residual g z a) (ds.getD a 0)

theorem plain_at (g : GateRate) {r a : ℕ} {z : FeeBox} {ds : List ℕ}
    (h:plainCheck g r z ds=true) (ha:a≤maxDepth g z) :
    chargeCheck g r a (residual g z a) (ds.getD a 0)=true :=
  List.all_eq_true.mp h a (List.mem_range.mpr (by omega))

def depthCheck (g : GateRate) (r : ℕ) (boxes : List Entry) (ds : List ℕ) : Bool :=
  (List.range boxes.length).all fun a =>
    match boxes.getD a none with
    | none => true
    | some z => chargeCheck g r a z (ds.getD a 0)

theorem depth_at (g : GateRate) {r a : ℕ} {z : FeeBox} {boxes : List Entry} {ds : List ℕ}
    (h:depthCheck g r boxes ds=true) (ha:a < boxes.length) (he:boxes.getD a none=some z) :
    chargeCheck g r a z (ds.getD a 0)=true:=by
  have hv:=List.all_eq_true.mp h a (List.mem_range.mpr ha)
  change (match boxes.getD a none with
    | none => true
    | some v => chargeCheck g r a v (ds.getD a 0))=true at hv
  rw [he] at hv
  exact hv

def rowCheck (g : GateRate) (r : ℕ) (boxes : List Entry) (ds : List ℕ) (z : FeeBox) (pd : List ℕ) : Bool :=
  depthCheck g r boxes ds && plainCheck g r z pd

/-- Reuse the first full-source schedule at every later level. -/
theorem charge_mono (g : GateRate) {r R a d e : ℕ} {z : FeeBox} (hr : R ≤ r)
    (h : 0 < localLength R a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep)≤g.split*g.unit*localLength R a d e) :
    0 < localLength r a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep)≤g.split*g.unit*localLength r a d e:=by
  have hL : localLength R a d e ≤ localLength r a d e := by
    unfold localLength
    gcongr
  exact ⟨h.1.trans_le hL,h.2.trans (Nat.mul_le_mul_left _ hL)⟩

end KoalaFarBridge

#print axioms KoalaFarBridge.charge_of_check
