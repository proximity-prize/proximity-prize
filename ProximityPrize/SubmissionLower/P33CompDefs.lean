/- P33CompDefs (Bome2017 tree): data types and row checks of the composition certificate over
`K6833Residual` (Profiles = Fin 6 × Fin 6 × Fin 6, caps 16/67/8870 of `validRow`).
The 68.32 "old price" of a support is replaced by Bome2017's single-factor check `simpleMode`
(K6833TerminalNumeric.lean:34), whose soundness is `single_count` (K6833TerminalCount.lean:58). -/
import ProximityPrize.SubmissionLower.P33Base
import ProximityPrize.SubmissionLower.K6833TerminalCount
import ProximityPrize.SubmissionLower.K6833TerminalFactorRouting

namespace ProximityPrize
namespace SubmissionLower
namespace P33
open K6833Residual RCN095
set_option autoImplicit false

/-- A support with its route (`none` = raw), the analogue of the 68.32 `Cell`. -/
structure OldCell where
  envelope : Envelope
  sourceIds : Option Profiles

structure CertCell where
  env : Envelope
  lam : Option Profiles
  bound : ℕ
  clips : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)

def smallSupport (c : CertCell) : Envelope :=
  ⟨c.env.slope, c.env.middle, max (c.env.total / 2) c.env.middle⟩

def routeOK (e : Envelope) (ids : Option Profiles) : Bool :=
  match ids with
  | some ids => jetGatesWithCorrections TailCorrections.original e (cellConfig ids) &&
      jetMonotoneWithCorrections TailCorrections.original e (cellConfig ids) &&
      decide (1 ≤ e.slope ∧ 2 ≤ e.middle ∧ e.total < 2130706433)
  | none => rawGatesWithCorrections TailCorrections.original (e.pad 0)

/-- Shape and the terminal caps of `validRow` (16/67/8870). -/
def capsOK (e : Envelope) : Bool :=
  decide (e.slope ≤ e.middle ∧ e.middle ≤ e.total ∧ e.slope ≤ 16 ∧ e.middle ≤ 67 ∧ e.total ≤ 8870)

def axes (e : Envelope) (ids : Option Profiles) : ℕ × ℕ × ℕ :=
  match ids with
  | some ids => (jetChargeAxisWithCorrections TailCorrections.original e (cellConfig ids) 0,
                 jetChargeAxisWithCorrections TailCorrections.original e (cellConfig ids) 1,
                 jetChargeAxisWithCorrections TailCorrections.original e (cellConfig ids) 2)
  | none => (rawChargeWithCorrections TailCorrections.original (e.pad 0) unitZFlag * terminalScale,
             rawChargeWithCorrections TailCorrections.original (e.pad 0) unitYZFlag * terminalScale,
             rawChargeWithCorrections TailCorrections.original (e.pad 0) unitAllFlag * terminalScale)

def cumCharge (a : ℕ × ℕ × ℕ) (r y t : ℕ) : ℕ :=
  a.1 * t + (a.2.1 - a.1) * y + (a.2.2 - a.2.1) * r

def bandLo (rq j : ℕ) : ℕ := rq + 3 * j
def bandHi (rq j : ℕ) : ℕ := min (rq + 3 * j + 2) 71

/-- Route of a code: 1 = raw, 2 + 36 i + 6 j + k = jet ids (i, j, k) over `Fin 6`. -/
def idsOfCode (c : ℕ) : Option Profiles :=
  if h : 2 ≤ c ∧ (c - 2) / 36 < 6 then
    some (⟨(c - 2) / 36, h.2⟩, ⟨(c - 2) / 6 % 6, Nat.mod_lt _ (by decide)⟩, ⟨(c - 2) % 6, Nat.mod_lt _ (by decide)⟩)
  else none

/-- An old-price row: caps plus Bome2017's single-factor check at the stored price. -/
def oldRowOK (x : OldCell × ℕ) : Bool :=
  capsOK x.1.envelope && simpleMode x.1.envelope x.2 x.1.sourceIds

def oldSliceOK (rq : ℕ) (slice : List (List (ℕ × ℕ))) : Bool :=
  (List.range 24).all fun j => (List.range 24).all fun k =>
    let v := (slice.getD j []).getD k (0, 0)
    v.1 = 0 || oldRowOK (⟨⟨rq, bandHi rq j, 300 * (k + 1)⟩, idsOfCode v.2⟩, v.1)

end P33
end SubmissionLower
end ProximityPrize
