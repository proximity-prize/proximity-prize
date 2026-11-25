import ProximityPrize.SubmissionLower.R6961Front6961PoleChart
import ProximityPrize.SubmissionLower.R6961LoTerminalMarked
import ProximityPrize.SubmissionLower.R6961MarkedProtocol

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

/-!
# 69.63 Lo band `h ∈ [2368, 2401]` (patternrecognition9's 69.61 2-jet rescue, retargeted)

`high_count_lo` is pr9's `high_count` restricted to the Lo band at agreement `179798`:
`E = 58`, `endpointDegree = 133472 = 4 * 33368`, axes `≤ 3523`, `retainedCapLo = highCap - prefixCap - smallCap - excCap`.
-/
namespace Lower6961
open Polynomial
open K1 (K p)
open K1_14 (Equation atMark)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open KoalaRect (axisDegree)
open Lower6961.RescueGeometry (Model Family)
open Lower6961.RetainedCompression (bandLo)
open Lower6961.MarkedEvaluation (rate nonlinear_price retained_of_nonlinear)
open scoped Polynomial

abbrev highCapLo : ℕ := 274796225155308725
abbrev retainedCapLo : ℕ := 78043278772029918

private theorem live_max_lo (e : Fin 58) (lo : 3 ≤ e.val) :
    rate e.val * (3523 + p * ((Lo.TerminalReceipts.witness e.val).order 1 - 1)) +
      (e.val - 1) * e.val ≤ 66543451347950190 := by
  fin_cases e <;> decide +kernel

private theorem budget_lo (e a b : ℕ) (lo : 3 ≤ e) (hi : e < 58) (axes : a + b ≤ 3523)
    (bound : b < (Lo.TerminalReceipts.witness e).order 1) :
    rate e * (a + p * b) + (e - 1) * e ≤ retainedCapLo := by
  have fit := live_max_lo ⟨e, hi⟩ lo
  have bnd : b ≤ (Lo.TerminalReceipts.witness e).order 1 - 1 := by omega
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add
    (show a ≤ 3523 by omega) (Nat.mul_le_mul_left _ bnd))) _).trans
    (fit.trans (by decide))

/-- Unconditional Lo-band mark count at `A = 179798` on `h ∈ [2368, 2401]`. -/
theorem high_count_lo {u deleted} (M : Model u deleted) {Γ} (F : Family M Γ)
    (lo : 2368 ≤ M.overhead) (hi : M.overhead ≤ 2401) :
    Γ.card ≤ highCapLo := by
  obtain ⟨D, ⟨Crt⟩, regular, residues⟩ := FrontPoleChart.of_family M F
  have hlo : 2368 ≤ M.overhead.toNat := by omega
  have hhi : M.overhead.toNat ≤ 2401 := by omega
  rcases Lo.TerminalMarked.good_remainder F Crt hlo hhi regular residues with
    paid | ⟨T, f, sub, paid, degree, small, axes, grade, marks⟩
  · exact paid.trans (by decide +kernel)
  · have hT : T.card ≤ retainedCapLo :=
      retained_of_nonlinear bandLo (nonlinear_price bandLo) 2401 3523 retainedCapLo
        (fun e => (Lo.TerminalReceipts.witness e).order 1) (by decide) (by decide)
        budget_lo F hhi T f sub degree small axes grade (fun γ hγ => (marks γ hγ).1)
    exact (paid.trans (Nat.add_le_add_left hT _)).trans (by decide +kernel)

/-- Exactly the statement of lean-6963's `Lower6960.lo_band_count` (TEMP-STUB-LO): drop-in replacement. -/
theorem lo_band_count_6963 {u deleted Γ} (M : P1.ModelAt 33619 u deleted) (_F : P1.FamilyAt 179798 M Γ)
    (_lo : 2368 ≤ M.overhead) (_hi : M.overhead ≤ 2401) : Γ.card ≤ 274796225155308725 :=
  high_count_lo M _F _lo _hi

/-- Glue for `protocol_claim`'s `high` argument: the Lo band `[2368, 2401]` (this module) together with the
1-jet high count `hiCount` on `[2402, 33619]` (the retargeted R6960 `high_count_of_retained`) cover `[2368, 33619]`.
Both counts share the single cap `highCapLo`. -/
theorem high_split
    (hiCount : ∀ {u deleted} {Γ} (M : Model u deleted) (_F : Family M Γ),
      2402 ≤ M.overhead → M.overhead ≤ 33619 → Γ.card ≤ highCapLo) :
    ∀ {u deleted} {Γ} (M : Model u deleted) (_F : Family M Γ),
      2368 ≤ M.overhead → M.overhead ≤ 33619 → Γ.card ≤ highCapLo := by
  intro u deleted Γ M F lo hi
  by_cases h : M.overhead ≤ 2401
  · exact high_count_lo M F lo h
  · exact hiCount M F (by omega) hi

#print axioms high_count_lo
#print axioms lo_band_count_6963
#print axioms high_split
end Lower6961
