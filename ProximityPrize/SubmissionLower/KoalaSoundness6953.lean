import ProximityPrize.SubmissionLower.FrontAssembly82200
import ProximityPrize.SubmissionLower.Scalar50Wide55NextDirectList
import ProximityPrize.SubmissionLower.HighCore82249Finish
import ProximityPrize.SubmissionLower.Final50Low82249

set_option Elab.async false

namespace KoalaSoundness6953
open ProximityPrize.Benchmark

/-- 69.53 staging at 82,249 errors (agreement 179,895): the scalar list, the low count to `h0` and the high
count from `h0 + 1` are the hypotheses (caps = `Front82200.lowCap`/`highCap`). -/
theorem of_parts (hlist : CJ0.ScalarList Front82200.agreement Front82200.listCap) (h0 : ℤ)
    (low : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      1 ≤ M.overhead → M.overhead ≤ h0 → Γ.card ≤ Front82200.highCap)
    (h0low : Front82200.lowCutoff ≤ h0)
    (high : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      h0 + 1 ≤ M.overhead → M.overhead ≤ (Front82200.heightCap : ℤ) → Γ.card ≤ Front82200.highCap)
    (caps : Front82200.highCap ≤ Front82200.lowCap) :
    ProtocolClaim 6953 ProximityPrize.SubmissionLower.Cell82200.p
      ProximityPrize.SubmissionLower.Cell82200.q := by
  apply Front82200.of_low_mid_high hlist h0
  · intro u d M Γ F lo hi
    exact (low u d M Γ F lo (le_trans hi h0low)).trans caps
  · intro u d M Γ F lo hi
    exact low u d M Γ F (le_trans (by decide) lo) hi
  · exact high


/-- The scalar list at 82,249 errors: lambda's coupled order-55 list (Λ = 1,710,834,581,234,467, lambda-c53L-coupled@299ee11d; was
`lambda-c53-lifted-weight@b8bb4612`). Only the low count to `h0` and the high count from `h0 + 1` remain. -/
theorem of_low_high (h0 : ℤ)
    (low : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      1 ≤ M.overhead → M.overhead ≤ h0 → Γ.card ≤ Front82200.highCap)
    (h0low : Front82200.lowCutoff ≤ h0)
    (high : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      h0 + 1 ≤ M.overhead → M.overhead ≤ (Front82200.heightCap : ℤ) → Γ.card ≤ Front82200.highCap) :
    ProtocolClaim 6953 ProximityPrize.SubmissionLower.Cell82200.p
      ProximityPrize.SubmissionLower.Cell82200.q :=
  of_parts Scalar50Wide55NextDirectList.scalar_list_tight h0 low h0low high le_rfl


/-- 69.53 with cutter's high (`HighCore82249.count`, heights 2391.., ≤ 272,966,371,768,711,151, cutter-c53-integration-high@731e3aef):
only the low count for heights 1..2390 at agreement 179,895 remains. -/
theorem of_low
    (low : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      1 ≤ M.overhead → M.overhead ≤ 2390 → Γ.card ≤ Front82200.highCap) :
    ProtocolClaim 6953 ProximityPrize.SubmissionLower.Cell82200.p
      ProximityPrize.SubmissionLower.Cell82200.q :=
  of_low_high 2390 low (by decide) fun _ _ M _ F lo hi =>
    (HighCore82249.count M F (le_trans (by decide) lo) hi).trans (by decide)


/-- 69.53 at 82,249 errors: leap's low (`Final50Low82249.count`, heights 1..2390, ≤ 272,987,140,666,905,598; PR649 low with
12 split bands + cutter's PR655-based anchor `Cutter53Anchor` + theta primary rank) and cutter's high from 2391. -/
theorem proof :
    ProtocolClaim 6953 ProximityPrize.SubmissionLower.Cell82200.p
      ProximityPrize.SubmissionLower.Cell82200.q :=
  of_low fun _ _ M _ F lo hi => (Final50Low82249.count M F lo hi).trans (by decide)

end KoalaSoundness6953
