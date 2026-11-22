import ProximityPrize.SubmissionLower.KoalaTaperTransferReceipt
import ProximityPrize.SubmissionLower.Low53At2389Primary

set_option Elab.async false

namespace Low53At2389Primary

theorem koala_local_rank : LocalRankBound := by
  intro x y
  exact (KoalaTaperTransfer.node_rank x y).trans (by decide)

theorem primary_rank_koala (w : P3.I → P3.K) : Low53At2389Order.PrimaryRank w :=
  primary_rank koala_local_rank w

end Low53At2389Primary
