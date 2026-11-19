/- P33RCheck: the REFINED composition certificate (68.35 lever, lower-6832/Scratch6833/F35.md).
   A cell certifies a row envelope E = (r, y, t) by splitting on the box Q = (rq, j, k) of the factor F1 with the
   LARGEST total (it always exists, there is no separate "all small" case):
   * rq = r: F1 is the only factor; bound = `ub` (clip | old table | packet cap), as in `P33Check`;
   * rq < r: F1 gets `ub` (the clip, if any, is taken at the support (rq, min(bandHi, y-1), min(300(k+1), t-1)), since at
     least one other factor of slope, middle, total >= 1 exists); every other factor G is charged at the
     Q-dependent support S'(Q) = (min(rr, yy), yy, min(300 ceil(tt/300), 8870)) with rr = r - rq, lo_y = bandLo, lo_t = max(300k+1, lo_y),
     tt = min(300(k+1), t - lo_t), yy = min(y - lo_y, tt); the others' aggregate is <= (rr, y - lo_y, min(t - lo_t, rr * tt)).
   The route of S' is read from the global support table `supTab` (`supAt`; entries validated by `supSliceOK`). -/
import ProximityPrize.SubmissionLower.P33Check
import ProximityPrize.SubmissionLower.P33SupTable

set_option Elab.async false

namespace ProximityPrize
namespace SubmissionLower
namespace P33
open K6833Residual RCN095
set_option autoImplicit false

structure RCell where
  env : Envelope
  bound : ℕ
  /-- clip rows `(rq, j, k, ys, code, price)` with the same shape as `CertCell.clips` -/
  clips : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)

/-- The clip list of `c` seen as a `CertCell` whose envelope is the one that bounds a box with slope `rq`:
(rq, y - 1, t - 1) if `rq < r` (another factor exists), `E` itself if `rq = r`. Only `clips`, `env.middle`, `env.total`
are read by `ub` / `clipOK`. -/
def pcell (c : RCell) (rq : ℕ) : CertCell :=
  ⟨⟨rq, c.env.middle - (if rq < c.env.slope then 1 else 0), c.env.total - (if rq < c.env.slope then 1 else 0)⟩,
    none, c.bound, c.clips⟩

def clipOKR (c : RCell) (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Bool := clipOK (pcell c x.1) x

/-- One box row (rq, j, k), `1 ≤ rq ≤ r`. -/
def boxR (c : RCell) (rq j k : ℕ) : Bool :=
  let r := c.env.slope; let y := c.env.middle; let t := c.env.total
  let loy := bandLo rq j; let lot := max (300 * k + 1) loy
  if rq < r then
    if y ≤ loy ∨ t ≤ lot then true
    else
      let rr := r - rq
      let tt := min (300 * (k + 1)) (t - lot)
      let yy := min (y - loy) tt
      let e := supAt (min rr yy) yy ((tt + 299) / 300)
      if e.1 = 0 then false
      else
        match ub (pcell c rq) rq j k with
        | some u => decide (u + cumCharge (e.2.1, e.2.2.1, e.2.2.2) rr (y - loy) (min (t - lot) (rr * tt)) /
            terminalScale ≤ c.bound)
        | none => false
  else
    if y < loy ∨ t < lot then true
    else
      match ub (pcell c rq) rq j k with
      | some u => decide (u ≤ c.bound)
      | none => false

/-- The certificate of one refined cell. -/
def certCheckR (c : RCell) : Bool :=
  capsOK c.env && decide (1 ≤ c.env.slope ∧ c.env.slope ≤ 14) && c.clips.all (clipOKR c) &&
  (List.range (c.env.slope + 1)).all fun rq =>
    rq = 0 || (List.range 24).all fun j => (List.range 30).all fun k => boxR c rq j k

theorem certCheckR_parts {c : RCell} (h : certCheckR c = true) :
    capsOK c.env = true ∧ (1 ≤ c.env.slope ∧ c.env.slope ≤ 14) ∧
    (∀ x ∈ c.clips, clipOKR c x = true) ∧
    (∀ rq, rq ≤ c.env.slope → 1 ≤ rq → ∀ j < 24, ∀ k < 30, boxR c rq j k = true) := by
  unfold certCheckR at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun rq hr h1r j hj k hk => ?_⟩
  rcases h4 rq (Nat.lt_succ_of_le hr) with h0 | hrow
  · exact absurd h0 (by omega)
  · exact hrow j hj k hk

end P33
end SubmissionLower
end ProximityPrize
