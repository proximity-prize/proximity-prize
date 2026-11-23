import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.Z1sUWDe
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.ZrIiE0d
import ProximityPrize.SubmissionLower.ZdZNCPb
import ProximityPrize.SubmissionLower.ZeFfOZc
import ProximityPrize.SubmissionLower.ZpWezjb
set_option Elab.async false
set_option autoImplicit true
section
namespace ai7



open jQ (eE)
open aF8 (bi6 CH)
structure aqm where
 B:ℕ
 J:ℕ
 total:ℕ
 exactness :eE B J=total
instance :Inhabited aqm:=⟨⟨0,0,0,rfl⟩⟩
def blocks (last :ℕ) :List ℕ→List (ℕ×ℕ)
 | []=>[]
 | [v]=>[(last,v)]
 | v :: w :: rest=>(256,v) :: blocks last (w :: rest)
theorem bsJ {B J total last :ℕ} (values :List ℕ)
  (h:bi6 B J J (blocks last values))
  (hlen: ((blocks last values).map Prod.fst).sum=B+J)
  (htotal: ((blocks last values).map Prod.snd).sum=total) :
  eE B J=total :=
 CH (blocks last values) h hlen htotal
end ai7
end
section
namespace CQ
open aR (Shape)



abbrev box :Shape :=⟨125, 51,8⟩
end CQ
end
