import ProximityPrize.SubmissionLower.R6961Front6961PoleChart
import ProximityPrize.SubmissionLower.R6961HiTerminalMarked
import ProximityPrize.SubmissionLower.R6961LoTerminalMarked
import ProximityPrize.SubmissionLower.R6960MarkedProtocol

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6961
open Polynomial
open K1 (K p)
open K1_14 (Equation atMark)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open KoalaRect (axisDegree)
open Lower6961.RescueGeometry (Model Family)
open Lower6960.RetainedCompression (bandHi bandLo)
open Lower6960.MarkedEvaluation (rate nonlinear_price retained_of_nonlinear)
open scoped Polynomial

abbrev retainedCapHi : ℕ := 10000000000000000
abbrev retainedCapLo : ℕ := 66000000000000000

private theorem live_max_hi (e : Fin 48) (lo : 3 ≤ e.val) :
    rate e.val * (1149 + p * ((Hi.TerminalReceipts.witness e.val).order 1 - 1)) +
      (e.val - 1) * e.val ≤ 6641028433030601 := by
  fin_cases e <;> decide +kernel

private theorem budget_hi (e a b : ℕ) (lo : 3 ≤ e) (hi : e < 48) (axes : a + b ≤ 1149)
    (bound : b < (Hi.TerminalReceipts.witness e).order 1) :
    rate e * (a + p * b) + (e - 1) * e ≤ retainedCapHi := by
  have fit := live_max_hi ⟨e, hi⟩ lo
  have bnd : b ≤ (Hi.TerminalReceipts.witness e).order 1 - 1 := by omega
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add
    (show a ≤ 1149 by omega) (Nat.mul_le_mul_left _ bnd))) _).trans
    (fit.trans (by decide))

private theorem live_max_lo (e : Fin 58) (lo : 3 ≤ e.val) :
    rate e.val * (3491 + p * ((Lo.TerminalReceipts.witness e.val).order 1 - 1)) +
      (e.val - 1) * e.val ≤ 65458235685340932 := by
  fin_cases e <;> decide +kernel

private theorem budget_lo (e a b : ℕ) (lo : 3 ≤ e) (hi : e < 58) (axes : a + b ≤ 3491)
    (bound : b < (Lo.TerminalReceipts.witness e).order 1) :
    rate e * (a + p * b) + (e - 1) * e ≤ retainedCapLo := by
  have fit := live_max_lo ⟨e, hi⟩ lo
  have bnd : b ≤ (Lo.TerminalReceipts.witness e).order 1 - 1 := by omega
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add
    (show a ≤ 3491 by omega) (Nat.mul_le_mul_left _ bnd))) _).trans
    (fit.trans (by decide))

/-- Unconditional 69.63 high-band mark count on `h ∈ [2346, 33599]` via the 2-subband split:
- `High_lo`: `h ∈ [2346, 2449]` (`ed = 133520`, `E = 58`, Hybrid 2-jet + 1-jet 10-rect rescue)
- `High_hi`: `h ∈ [2450, 33599]` (`ed = 164672`, `E = 48`, pure 1-jet rescue)
Both subbands share the single unified `MarkedEvaluation.nonlinear_price` theorem! -/
theorem high_count {u deleted} (M : Model u deleted) {Γ} (F : Family M Γ)
    (lo : 2346 ≤ M.overhead) (hi : M.overhead ≤ 33599) :
    Γ.card ≤ 272188771910282110 := by
  obtain ⟨D, ⟨Crt⟩, regular, residues⟩ := FrontPoleChart.of_family M F
  by_cases hband : M.overhead ≤ 2449
  · have hlo : 2346 ≤ M.overhead.toNat := by omega
    have hhi : M.overhead.toNat ≤ 2449 := by omega
    rcases Lo.TerminalMarked.good_remainder F Crt hlo hhi regular residues with
      paid | ⟨T, f, sub, paid, degree, small, axes, grade, marks⟩
    · exact paid.trans (by decide +kernel)
    · have hT : T.card ≤ retainedCapLo :=
        retained_of_nonlinear bandLo (nonlinear_price bandLo) 2449 3491 retainedCapLo
          (fun e => (Lo.TerminalReceipts.witness e).order 1) (by decide) (by decide)
          budget_lo F hhi T f sub degree small axes grade (fun γ hγ => (marks γ hγ).1)
      exact (paid.trans (Nat.add_le_add_left hT _)).trans (by decide +kernel)
  · have hlo : 2450 ≤ M.overhead.toNat := by omega
    have hhi : M.overhead.toNat ≤ 33599 := by omega
    rcases Hi.TerminalMarked.good_remainder F Crt hlo hhi regular residues with
      paid | ⟨T, f, sub, paid, degree, small, axes, grade, marks⟩
    · exact paid.trans (by decide +kernel)
    · have hT : T.card ≤ retainedCapHi :=
        retained_of_nonlinear bandHi (nonlinear_price bandHi) 33599 1149 retainedCapHi
          (fun e => (Hi.TerminalReceipts.witness e).order 1) (by decide) (by decide)
          budget_hi F hhi T f sub degree small axes grade (fun γ hγ => (marks γ hγ).1)
      exact (paid.trans (Nat.add_le_add_left hT _)).trans (by decide +kernel)

#print axioms high_count
end Lower6961
