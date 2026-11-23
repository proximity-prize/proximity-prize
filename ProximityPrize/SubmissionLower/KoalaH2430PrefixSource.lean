import ProximityPrize.SubmissionLower.HighCore82258BankProof
import ProximityPrize.SubmissionLower.HighCore82258Pairs
import ProximityPrize.SubmissionLower.HighCore82258Ledger
import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option autoImplicit false

open FrontCore82258 (effectiveHeight)

namespace KoalaH2430
open HighCore82258
open HighCore82258_3 (ScheduleOK)
open K1_14 (Banks)
open scoped Polynomial

theorem band : InBand .h2430 (2430 : ℤ) := by
  change (2430 : ℤ) ≤ 2430 ∧ (2430 : ℤ) ≤ 2430
  exact ⟨le_rfl, le_rfl⟩
theorem terminal_eq : HighCore82258.terminal .h2430 = KoalaH2430Terminal.terminal := rfl
theorem schedule : ScheduleOK .h2430 := HighCore82258.schedule .h2430

theorem crt_source : CRTSourceExists :=
  HighCore82258BankProof.interpolation_sources_for_crt

theorem source_and_pairs {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (hw : (effectiveHeight M) = 2430) (hshift : M.shift ∉ Γ)
    {H : K1_14.L[X]} (hH : AdjacentChart M F H) :
    ∃ C : ChartSource .h2430 M F, Nonempty (Pairs .h2430 (effectiveHeight M).toNat C.rows) := by
  have hb : InBand .h2430 (effectiveHeight M) := by simpa only [hw] using band
  obtain ⟨C⟩ := crt_source .h2430 u del M Γ F hb hshift H hH
  exact ⟨C, buffered_pairs .h2430 M F hb C.source⟩

#print axioms source_and_pairs
end KoalaH2430
