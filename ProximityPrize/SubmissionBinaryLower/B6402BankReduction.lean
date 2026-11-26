import ProximityPrize.SubmissionBinaryLower.B6402GlobalHardLinear
import ProximityPrize.SubmissionBinaryLower.B6402GlobalHardScalar
import ProximityPrize.SubmissionBinaryLower.B6402HardReduction

namespace ProximityPrize.SubmissionBinaryLower.B6402BankReduction
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd
open B6401Params hiding A
open B6402LinearSplit B6402CleanFamily
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem line (bank : Bank) : HardLinear := by
  intro u₀ u₁ q hq F hirr inv slope quart ord range hZ S P Az hP froot card hit bad
  let WF := wdeg wY F
  obtain ⟨c,e,_⟩ := (mem_kerD_iff_exists_unique_coords (wY:=wY) (W:=WF) (s:=1) (by decide) F).mp ⟨inv,slope.le,le_rfl⟩
  have hhi : (WF:ℚ)/wY≤51/2 := range.le.trans (by norm_num)
  have h2 (_ : q=2) : (WF:ℚ)/wY<13 ∧ 1811≤1811 := ⟨range.trans (by norm_num),le_rfl⟩
  exact B6402GlobalHardLinear.hard_labels bank u₀ u₁ hq hhi h2 c (e ▸ inv) (e ▸ hirr)
    (e ▸ B6401Main.irreducible_liftCRat_of_irred hirr (by omega)) (e ▸ slope) (by rw [←e]) (e ▸ hZ)
    S P Az hP (e ▸ froot) card hit bad le_rfl (by change _ ∧ _ ∧ _; rw [←e]; exact ⟨quart,ord,range⟩)

theorem protocol (bank : Bank) : ProtocolClaim 6402 78643482 268435456 :=
  B6402HardReduction.protocol (line bank) (B6402GlobalHardScalar.hard_scalar bank)

#print axioms protocol
end ProximityPrize.SubmissionBinaryLower.B6402BankReduction
