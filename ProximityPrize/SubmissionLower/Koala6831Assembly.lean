import ProximityPrize.SubmissionLower.Koala6831Protocol
import ProximityPrize.SubmissionLower.Koala6831ScalarList

namespace ProximityPrize.SubmissionLower.Koala6831Assembly

open ProximityPrize.Benchmark
open Koala6831Protocol

private theorem filter_card_le {I : Type*} (P : I → Prop)
    (left right : DecidablePred P) (nodes : Finset I) :
    (@Finset.filter I P left nodes).card ≤ (@Finset.filter I P right nodes).card := by
  rw [Subsingleton.elim left right]

set_option maxHeartbeats 2000000 in

theorem protocolClaim_6831_of_seed_bound
    (hseed : ScalarSeedBound) :
    ProtocolClaim 6831 332025855 1073741824 := by
  apply protocolClaim_6831_of_bounds hseed
  intro received words hcode hclose
  have hagreement : Fintype.card IRSProfile.Index - errors = 181084 := by
    rw [IRSProfile.card_index]
    decide
  refine Koala6831ScalarList.irs_scalar_finite_list_card_le received words hcode ?_
  intro word hword
  have hnear := hclose word hword
  rw [hagreement] at hnear
  exact hnear.trans (filter_card_le (fun i ↦ word i = received i) _ _ _)

end ProximityPrize.SubmissionLower.Koala6831Assembly
