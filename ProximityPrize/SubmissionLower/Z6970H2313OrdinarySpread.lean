import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryComplete
import ProximityPrize.SubmissionLower.R6970Height2313Classification

set_option Elab.async false

namespace Research6970.Height2313.Spread2313

/-- Bridge the checked singleton spread classification to the ordinary route. -/
theorem graph_above_twenty_one : OrdinaryComplete.GraphClassifier := by
  intro h lo hi D Crt word parents live geo pass f proj large
  exact Classification.graph_above_twenty_one_from2313 Crt word
    lo (hi.trans (by decide)) parents live geo pass proj large

end Research6970.Height2313.Spread2313
