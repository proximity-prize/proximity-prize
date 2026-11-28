import ProximityPrize.SubmissionLower.R6970Height2308DualAxis
import ProximityPrize.SubmissionLower.R6970Height2308SelectedRank

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.Geometry2308

open _root_.Research6969 _root_.Research6969.PhysicalWindow

def src332 : Request :=
  ⟨⟨⟨2998, 4184, 900, 23250⟩, 806961139154944, 8370437628682⟩, 18, 3, 1, 386273, 3⟩

private theorem fit332 : TerminalWitness.Fits src332 2308 2313 SpreadCatalogue.shape := by
  refine ⟨bank_2998_4184_900 23250, ?_, by decide, by decide, by decide, by decide, by decide, ?_⟩
  · unfold Research6966.TerminalBanks.inside
    decide
  · unfold Lower6960.HelperSource.WidthGuard
    decide

def test332 : DualAxis.Test where
  source := src332
  side := 12395
  other := 23
  fits := fit332
  space := by decide
  checked h low high := by
    interval_cases h
    all_goals exact DualAxis.of_fast src332 12395 23 _ _ (by decide +kernel)

def src344 : Request :=
  ⟨⟨⟨2998, 4184, 900, 24056⟩, 806961139154944, 8370437628682⟩, 18, 3, 1, 386273, 0⟩

private theorem fit344 : TerminalWitness.Fits src344 2308 2313 SpreadCatalogue.shape := by
  refine ⟨bank_2998_4184_900 24056, ?_, by decide, by decide, by decide, by decide, by decide, ?_⟩
  · unfold Research6966.TerminalBanks.inside
    decide
  · unfold Lower6960.HelperSource.WidthGuard
    decide

def test344 : DualAxis.Test where
  source := src344
  side := 13893
  other := 22
  fits := fit344
  space := by decide
  checked h low high := by
    interval_cases h
    all_goals exact DualAxis.of_fast src344 13893 22 _ _ (by decide +kernel)

def src495 : Request :=
  ⟨⟨⟨2998, 4184, 900, 21678⟩, 806961139154944, 8370437628682⟩, 18, 3, 1, 386273, 7⟩

private theorem fit495 : TerminalWitness.Fits src495 2308 2313 SpreadCatalogue.shape := by
  refine ⟨bank_2998_4184_900 21678, ?_, by decide, by decide, by decide, by decide, by decide, ?_⟩
  · unfold Research6966.TerminalBanks.inside
    decide
  · unfold Lower6960.HelperSource.WidthGuard
    decide

def test495 : DualAxis.Test where
  source := src495
  side := 6821
  other := 46
  fits := fit495
  space := by decide
  checked h low high := by
    interval_cases h
    all_goals exact DualAxis.of_fast src495 6821 46 _ _ (by decide +kernel)

end Research6970.Height2313.Research6969.Geometry2308
