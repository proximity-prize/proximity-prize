/- Apache-2.0. A split between adjacent checked rows limits the peak memory in each kernel reduction. -/
import ProximityPrize.SubmissionLower.Night6836Checks
namespace Koala6836.Fast
theorem appendCell (r s n : Nat) (before : block r s n = true)
    (last : (dataOK r (s+n) && checks r (s+n) && rounded r (s+n)) = true) :
    block r s (n+1)=true := by
  unfold block at *
  rw [List.range_succ, List.all_append]
  simp only [before, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, last]
end Koala6836.Fast
