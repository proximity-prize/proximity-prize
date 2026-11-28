import ProximityPrize.SubmissionLower.R6970Height2308GeometryRank
import ProximityPrize.SubmissionLower.R6970Height2313PairBounds

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.Geometry2308

open _root_.Research6969 _root_.Research6969.PhysicalWindow

def src501 : Request :=
  ⟨⟨⟨2987, 4162, 900, 49307⟩, 800354147500032, 8229637344156⟩, 194, 2, 1, 257515, 129⟩

private theorem fit501 : TerminalWitness.Fits src501 2308 2313 SpreadCatalogue.shape := by
  refine ⟨bank_2987_4162_900 49307, ?_, by decide, by decide, by decide, by decide, by decide, ?_⟩
  · unfold Research6966.TerminalBanks.inside
    decide
  · unfold Lower6960.HelperSource.WidthGuard
    decide

private theorem at501_2308 : Triangular src501 2308 2308 :=
  triangular_of_fast src501 2308 2308 (by decide +kernel)

private theorem at501_2309 : Triangular src501 2309 2309 :=
  triangular_of_fast src501 2309 2309 (by decide +kernel)

private theorem at501_2310 : Triangular src501 2310 2310 :=
  triangular_of_fast src501 2310 2310 (by decide +kernel)

private theorem at501_2311 : Triangular src501 2311 2311 :=
  triangular_of_fast src501 2311 2311 (by decide +kernel)

private theorem at501_2312 : Triangular src501 2312 2312 :=
  triangular_of_fast src501 2312 2312 (by decide +kernel)

private theorem at501_2313 : Triangular src501 2313 2313 :=
  triangular_of_fast src501 2313 2313 (by decide +kernel)

private theorem cover501 : Cover (Triangular src501) 2313 2308 [2308, 2309, 2310, 2311, 2312, 2313] :=
  ⟨le_rfl, by decide, at501_2308, le_rfl, by decide, at501_2309, le_rfl, by decide, at501_2310, le_rfl, by decide, at501_2311, le_rfl, by decide, at501_2312, le_rfl, by decide, at501_2313, rfl⟩

def test501 : _root_.Research6970.Height2313.Research6969.MeasuredBound.Test :=
  ⟨src501, .triangle, fit501, [2308, 2309, 2310, 2311, 2312, 2313], cover501⟩

end Research6970.Height2313.Research6969.Geometry2308
