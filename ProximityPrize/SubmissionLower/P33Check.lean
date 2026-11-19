/- P33Check: the per-cell decision procedure of the composition certificate (DRAFT, not compiled).
   Mirrors cert_eval.checks (Scratch6833) with YBALL = 1, LREM = 0, SHARED = 1, RQ1 = 1; bands in closed form. -/
import ProximityPrize.SubmissionLower.P33OldTable
import ProximityPrize.SubmissionLower.P33Windows

namespace ProximityPrize
namespace SubmissionLower
namespace P33
open K6833Residual
set_option autoImplicit false

/-- The bound `ub(Q)` of a big factor in box `(rq, j, k)`: `min (old price | clip) (window cap)`. -/
def ub (c : CertCell) (rq j k : ℕ) : Option ℕ :=
  let clip := (c.clips.find? fun x => x.1 = rq ∧ x.2.1 = j ∧ x.2.2.1 = k).map (·.2.2.2.2.2)
  let o : Option ℕ := match clip with
    | some p => some p
    | none => if oldAt rq j k = 0 then none else some (oldAt rq j k)
  let w : Option ℕ := (capAt rq j k).map (·.cap)
  match o, w with
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

/-- A clip row is a verified 68.32 support at the clipped corner of its box. -/
def clipOK (c : CertCell) (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  let rq := x.1; let j := x.2.1; let k := x.2.2.1; let ys := x.2.2.2.1; let code := x.2.2.2.2.1
  let price := x.2.2.2.2.2
  decide (ys = min (bandHi rq j) c.env.middle) &&
    oldRowOK (⟨⟨rq, ys, min (300 * (k + 1)) c.env.total⟩, idsOfCode code⟩, price)

/-- One box row. Boxes with `lo(Q) ≰ κ(E)`, or with `thi < T*`, hold no big factor and are skipped. -/
def boxOK (c : CertCell) (a : ℕ × ℕ × ℕ) (rq j k : ℕ) : Bool :=
  let r := c.env.slope; let y := c.env.middle; let t := c.env.total
  let Ts := t / 2 + 1
  let loy := bandLo rq j; let lot := max (300 * k) Ts
  if r < rq ∨ y < loy ∨ t < lot ∨ 300 * k + 300 < Ts then true
  else
    let rest := if r - rq = 0 then 0 else cumCharge a (r - rq) (y - loy) (t - lot) / terminalScale
    match ub c rq j k with
    | some u => decide (u + rest ≤ c.bound)
    | none => false

/-- The certificate of one cell (≈ 2 ms per non-skipped row, probes/t11). -/
def certCheck (c : CertCell) : Bool :=
  let S := smallSupport c
  let a := axes S c.lam
  routeOK S c.lam && capsOK S && capsOK c.env &&
  decide (1 ≤ c.env.slope ∧ c.env.slope ≤ 14 ∧ c.env.total ≤ 7200) &&
  c.clips.all (clipOK c) &&
  decide (cumCharge a c.env.slope c.env.middle c.env.total / terminalScale ≤ c.bound) &&
  (List.range (c.env.slope + 1)).all fun rq =>
    rq = 0 || (List.range 24).all fun j => (List.range 24).all fun k => boxOK c a rq j k

/-! ### Unpacking `certCheck` (small lemmas used by `composition_card_le`) -/

theorem certCheck_parts {c : CertCell} (h : certCheck c = true) :
    routeOK (smallSupport c) c.lam = true ∧ capsOK (smallSupport c) = true ∧ capsOK c.env = true ∧
    (1 ≤ c.env.slope ∧ c.env.slope ≤ 14 ∧ c.env.total ≤ 7200) ∧
    (∀ x ∈ c.clips, clipOK c x = true) ∧
    cumCharge (axes (smallSupport c) c.lam) c.env.slope c.env.middle c.env.total / terminalScale ≤ c.bound ∧
    (∀ rq, rq ≤ c.env.slope → 1 ≤ rq → ∀ j < 24, ∀ k < 24,
      boxOK c (axes (smallSupport c) c.lam) rq j k = true) := by
  unfold certCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun rq hr h1r j hj k hk => ?_⟩
  rcases h7 rq (Nat.lt_succ_of_le hr) with h0 | hrow
  · exact absurd h0 (by omega)
  · exact hrow j hj k hk

end P33
end SubmissionLower
end ProximityPrize
