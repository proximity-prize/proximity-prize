import ProximityPrize.SubmissionLower.FadicVar

set_option Elab.async false

set_option autoImplicit false
namespace KoalaFarBridge
open FadicGate (Entry)

abbrev FeeBox := ℕ × ℕ × ℕ

structure GateRate where
  b : ℕ
  j : ℕ
  t : ℕ
  sep : ℕ
  unit : ℕ
  split : ℕ
  bl : ℕ
  jl : ℕ
  tl : ℕ
  deriving DecidableEq

def boxFee (g : GateRate) (z : FeeBox) : ℕ :=
  g.b * max z.1 z.2.1 + g.j * z.2.1 + g.t * min z.2.2 (z.2.1/3)

def residual (g : GateRate) (z : FeeBox) (a : ℕ) : FeeBox :=
  (z.1-a*g.bl, z.2.1-a*g.jl, z.2.2-a*g.tl)

def maxDepth (g : GateRate) (z : FeeBox) : ℕ :=
  min (z.1/g.bl) (min (z.2.1/g.jl) (z.2.2/g.tl))

def localLength (r a d e : ℕ) : ℕ := e*(24*(r-e*a)+d*(e-1))

/-- The same check is used at an f-adic depth and at the actual valuation of a plain row. -/
def chargeCheck (g : GateRate) (r a : ℕ) (z : FeeBox) (d : ℕ) : Bool :=
  (List.range g.split).all fun k =>
    let e := k+1
    let len := localLength r a d e
    decide (0 < len ∧ (g.split+1-e)*(24*boxFee g z+d*g.sep) ≤ g.split*g.unit*len)

theorem charge_of_check (g : GateRate) {r a d e : ℕ} {z : FeeBox}
    (h : chargeCheck g r a z d = true) (he : 1 ≤ e) (hs : e ≤ g.split) :
    0 < localLength r a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep) ≤ g.split*g.unit*localLength r a d e := by
  unfold chargeCheck at h
  have hi : e-1 ∈ List.range g.split := List.mem_range.mpr (by omega)
  have hv := of_decide_eq_true (List.all_eq_true.mp h (e-1) hi)
  simpa only [Nat.sub_add_cancel he] using hv

def plainCheck (g : GateRate) (r : ℕ) (z : FeeBox) (ds : List ℕ) : Bool :=
  (List.range (maxDepth g z+1)).all fun a => chargeCheck g r a (residual g z a) (ds.getD a 0)

theorem plain_at (g : GateRate) {r a : ℕ} {z : FeeBox} {ds : List ℕ}
    (h : plainCheck g r z ds = true) (ha : a ≤ maxDepth g z) :
    chargeCheck g r a (residual g z a) (ds.getD a 0) = true :=
  List.all_eq_true.mp h a (List.mem_range.mpr (by omega))

def depthCheck (g : GateRate) (r : ℕ) (boxes : List Entry) (ds : List ℕ) : Bool :=
  (List.range boxes.length).all fun a =>
    match boxes.getD a none with
    | none => true
    | some z => chargeCheck g r a z (ds.getD a 0)

theorem depth_at (g : GateRate) {r a : ℕ} {z : FeeBox} {boxes : List Entry} {ds : List ℕ}
    (h : depthCheck g r boxes ds = true) (ha : a < boxes.length) (he : boxes.getD a none = some z) :
    chargeCheck g r a z (ds.getD a 0) = true := by
  have hv := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  change (match boxes.getD a none with
    | none => true
    | some v => chargeCheck g r a v (ds.getD a 0)) = true at hv
  rw [he] at hv
  exact hv

def rowCheck (g : GateRate) (r : ℕ) (boxes : List Entry) (ds : List ℕ) (z : FeeBox) (pd : List ℕ) : Bool :=
  depthCheck g r boxes ds && plainCheck g r z pd

/-- Reuse the first full-source schedule at every later level. -/
theorem charge_mono (g : GateRate) {r R a d e : ℕ} {z : FeeBox} (hr : R ≤ r)
    (h : 0 < localLength R a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep) ≤ g.split*g.unit*localLength R a d e) :
    0 < localLength r a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep) ≤ g.split*g.unit*localLength r a d e := by
  have hL : localLength R a d e ≤ localLength r a d e := by
    unfold localLength
    gcongr
  exact ⟨h.1.trans_le hL,h.2.trans (Nat.mul_le_mul_left _ hL)⟩

end KoalaFarBridge
