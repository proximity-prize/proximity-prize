import ProximityPrize.SubmissionLower.Bundle6970_8bfd9edfbe4e8ef2
import ProximityPrize.SubmissionLower.Bundle6970_8bfd9edfbe4e8ef2
import ProximityPrize.SubmissionLower.Bundle6970_2dca0e349cdc4e9e
import ProximityPrize.SubmissionLower.Bundle6970_2dca0e349cdc4e9e
import ProximityPrize.SubmissionLower.Bundle6970_8bfd9edfbe4e8ef2
import ProximityPrize.SubmissionLower.Bundle6970_8bfd9edfbe4e8ef2

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.Lower6960.Prefix6969Early
open _root_.Lower6960.Prefix6969Early (seed threshold)

theorem choose (a : Fin 6) (j : Fin 56) (ok : UniformAllowed (a.val+2) (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧
        w≤(if a.val=0 then threshold j else (a.val+2)*128758-1) ∧
        ∃ c : NearCase (a.val+2) l u w, c.uniform := by
  fin_cases a
  · exact nearChoose2 j ok
  · obtain ⟨l,u,w,lo,hi,hw,data⟩ := nearChoose3 j ok
    exact ⟨l,u,w,lo,hi,hw.trans (show 385979 ≤ 386273 by decide),data⟩
  · obtain ⟨l,u,w,lo,hi,hw,data⟩ := nearChoose4 j ok
    exact ⟨l,u,w,lo,hi,hw.trans (show 514639 ≤ 515031 by decide),data⟩
  · obtain ⟨l,u,w,lo,hi,hw,data⟩ := nearChoose5 j ok
    exact ⟨l,u,w,lo,hi,hw.trans (show 643299 ≤ 643789 by decide),data⟩
  · obtain ⟨l,u,w,lo,hi,hw,data⟩ := nearChoose6 j ok
    exact ⟨l,u,w,lo,hi,hw.trans (show 771959 ≤ 772547 by decide),data⟩
  · obtain ⟨l,u,w,lo,hi,hw,data⟩ := nearChoose7 j ok
    exact ⟨l,u,w,lo,hi,hw.trans (show 900619 ≤ 901305 by decide),data⟩

end Research6970.Height2313.Lower6960.Prefix6969Early
