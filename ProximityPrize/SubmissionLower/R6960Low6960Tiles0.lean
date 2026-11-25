import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top1
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top2
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top3
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top4
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top5
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top6
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top7
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top8
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top9
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top10
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top11
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top12
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top13
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top14

set_option Elab.async false

namespace Low6960Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)

def receipt : Receipt 0 where
  orders := orders
  covers := by
    intro a ha box
    change 0+a.b≤136 ∧ 0+a.j≤57 ∧ 0+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
    · exact Top1.exact a ha h1 (by omega) (by omega)
    · exact Top2.exact a ha h2 (by omega) (by omega)
    · exact Top3.exact a ha h3 (by omega) (by omega)
    · exact Top4.exact a ha h4 (by omega) (by omega)
    · exact Top5.exact a ha h5 (by omega) (by omega)
    · exact Top6.exact a ha h6 (by omega) (by omega)
    · exact Top7.exact a ha h7 (by omega) (by omega)
    · exact Top8.exact a ha h8 (by omega) (by omega)
    · exact Top9.exact a ha h9 (by omega) (by omega)
    · exact Top10.exact a ha h10 (by omega) (by omega)
    · exact Top11.exact a ha h11 (by omega) (by omega)
    · exact Top12.exact a ha h12 (by omega) (by omega)
    · exact Top13.exact a ha h13 (by omega) (by omega)
    · exact Top14.exact a ha h14 (by omega) (by omega)
end Low6960Allocation.Group0
