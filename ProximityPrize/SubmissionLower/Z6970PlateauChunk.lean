import ProximityPrize.SubmissionLower.Z6970PlateauLines

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem chunk_one (f : ℕ) : chunk f 1 = row f := by simp [chunk,sumN]

theorem join_chunk {f a b : ℕ} {u v : ℤ} (left : chunk f a = u) (right : chunk (f+a) b = v) :
    chunk f (a+b) = u+v := by rw [chunk_add,left,right]

end ExpandedPlateauSum6970
