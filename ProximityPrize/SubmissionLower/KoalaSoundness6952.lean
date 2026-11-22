import ProximityPrize.SubmissionLower.FrontAssembly82200
import ProximityPrize.SubmissionLower.Scalar50Wide55DirectList
import ProximityPrize.SubmissionLower.HighCore82239Finish
import ProximityPrize.SubmissionLower.Final50Low82239

set_option Elab.async false

namespace KoalaSoundness6952
open ProximityPrize.Benchmark

/-- 69.52 staging at 82,239 errors (agreement 179,905): the scalar list, the low count to `h0` and the high
count from `h0 + 1` are the hypotheses (caps = `Front82200.lowCap`/`highCap`). -/
theorem of_parts (hlist : CJ0.ScalarList Front82200.agreement Front82200.listCap) (h0 : ℤ)
    (low : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      1 ≤ M.overhead → M.overhead ≤ h0 → Γ.card ≤ Front82200.highCap)
    (h0low : Front82200.lowCutoff ≤ h0)
    (high : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      h0 + 1 ≤ M.overhead → M.overhead ≤ (Front82200.heightCap : ℤ) → Γ.card ≤ Front82200.highCap)
    (caps : Front82200.highCap ≤ Front82200.lowCap) :
    ProtocolClaim 6952 ProximityPrize.SubmissionLower.Cell82200.p
      ProximityPrize.SubmissionLower.Cell82200.q := by
  apply Front82200.of_low_mid_high hlist h0
  · intro u d M Γ F lo hi
    exact (low u d M Γ F lo (le_trans hi h0low)).trans caps
  · intro u d M Γ F lo hi
    exact low u d M Γ F (le_trans (by decide) lo) hi
  · exact high

#print axioms of_parts

/-- The scalar list at 82,239 errors: lambda's order-55 list (Λ = 2,002,422,605,167,821, checked as
`lambda-c52-m55@f1128302`). Only the low count to `h0` and the high count from `h0 + 1` remain. -/
theorem of_low_high (h0 : ℤ)
    (low : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      1 ≤ M.overhead → M.overhead ≤ h0 → Γ.card ≤ Front82200.highCap)
    (h0low : Front82200.lowCutoff ≤ h0)
    (high : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      h0 + 1 ≤ M.overhead → M.overhead ≤ (Front82200.heightCap : ℤ) → Γ.card ≤ Front82200.highCap) :
    ProtocolClaim 6952 ProximityPrize.SubmissionLower.Cell82200.p
      ProximityPrize.SubmissionLower.Cell82200.q :=
  of_parts Scalar50Wide55DirectList.scalar_list h0 low h0low high le_rfl

#print axioms of_low_high

/-- 69.52 with cutter's high (`HighCore82239.count`, heights 2378.., ≤ 272,100,187,954,834,303, cutter-c52-high@37107ee2):
only the low count for heights 1..2377 at agreement 179,905 remains. -/
theorem of_low
    (low : ∀ u deleted (M : Front82200.AnchorModel u deleted) Γ, Front82200.AnchoredFamily M Γ →
      1 ≤ M.overhead → M.overhead ≤ 2377 → Γ.card ≤ Front82200.highCap) :
    ProtocolClaim 6952 ProximityPrize.SubmissionLower.Cell82200.p
      ProximityPrize.SubmissionLower.Cell82200.q :=
  of_low_high 2377 low (by decide) fun _ _ M _ F lo hi =>
    (HighCore82239.count M F (le_trans (by decide) lo) hi).trans (by decide)

#print axioms of_low

/-- 69.52 at 82,239 errors: PR649's low (GordoAR 78870eea) retargeted by leap to 179,905 agreements and heights
1..2377 with the theta primary rank (`Final50Low82239.count`, cap = `Front82200.highCap`). -/
theorem proof :
    ProtocolClaim 6952 ProximityPrize.SubmissionLower.Cell82200.p
      ProximityPrize.SubmissionLower.Cell82200.q :=
  of_low fun _ _ M _ F lo hi => (Final50Low82239.count M F lo hi).trans (by decide)

#print axioms proof
end KoalaSoundness6952
