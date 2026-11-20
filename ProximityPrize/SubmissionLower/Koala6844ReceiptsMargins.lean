import ProximityPrize.SubmissionLower.Koala6844ReceiptsArithmeticBundle02
import ProximityPrize.SubmissionLower.Koala6844ReceiptsArithmeticBundle01

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxRecDepth 4096

private structure PositiveSource where
  shape : SourceShape
  positive : sourceMargin shape

private def positiveSources : Array PositiveSource := #[
  ⟨contact00, contact00_margin⟩,
  ⟨contact01, contact01_margin⟩,
  ⟨contact02, contact02_margin⟩,
  ⟨contact03, contact03_margin⟩,
  ⟨contact04, contact04_margin⟩,
  ⟨contact05, contact05_margin⟩,
  ⟨contact06, contact06_margin⟩,
  ⟨contact07, contact07_margin⟩,
  ⟨contact08, contact08_margin⟩,
  ⟨contact09, contact09_margin⟩,
  ⟨contact10, contact10_margin⟩,
  ⟨contact11, contact11_margin⟩,
  ⟨contact12, contact12_margin⟩,
  ⟨contact13, contact13_margin⟩,
  ⟨contact14, contact14_margin⟩,
  ⟨contact15, contact15_margin⟩,
  ⟨contact16, contact16_margin⟩,
  ⟨contact17, contact17_margin⟩,
  ⟨contact18, contact18_margin⟩,
  ⟨contact19, contact19_margin⟩,
  ⟨contact20, contact20_margin⟩,
  ⟨contact21, contact21_margin⟩,
  ⟨contact22, contact22_margin⟩,
  ⟨contact23, contact23_margin⟩,
  ⟨contact24, contact24_margin⟩,
  ⟨contact25, contact25_margin⟩,
  ⟨contact26, contact26_margin⟩,
  ⟨contact27, contact27_margin⟩,
  ⟨contact28, contact28_margin⟩,
  ⟨contact29, contact29_margin⟩,
  ⟨contact30, contact30_margin⟩,
  ⟨contact31, contact31_margin⟩,
  ⟨contact32, contact32_margin⟩,
  ⟨contact33, contact33_margin⟩]

theorem terminal_profile_margin (i : Fin contactProfiles.size) :
    sourceMargin (contactProfiles[i.val]'i.isLt) := by
  have hM : positiveSources.map PositiveSource.shape = contactProfiles := by
    simp only [positiveSources,contactProfiles,List.map_toArray,List.map_cons,List.map_nil]
  have hl : positiveSources.size = contactProfiles.size := by
    simpa only [Array.size_map] using congrArg Array.size hM
  have hi : i.val < positiveSources.size := by rw [hl]; exact i.isLt
  have h := congrArg (fun a : Array SourceShape => a[i.val]?) hM
  have he : (positiveSources[i.val]'hi).shape = (contactProfiles[i.val]'i.isLt) := by
    simpa only [Array.getElem?_map,Array.getElem?_eq_getElem hi,
      Array.getElem?_eq_getElem i.isLt,Option.map_some,Option.some.injEq] using h
  exact Eq.mp (congrArg sourceMargin he) (positiveSources[i.val]'hi).positive

end ProximityPrize.SubmissionLower.Koala6844Receipts
