import ProximityPrize.SubmissionLower.HighSource82190
import ProximityPrize.SubmissionLower.HighPairs82190
import ProximityPrize.SubmissionLower.HighRegular82190
import ProximityPrize.SubmissionLower.HighSchedule82190

set_option Elab.async false

namespace Heights82190
open ProximityPrize.Benchmark

theorem high : Front82190.c7 :=
  HighFamily82190.of_children HighFamily82190_1.proof HighFamily82190_2.proof
    (HighFamily82190_3.of_children HighFamily82190_3_1.proof HighFamily82190_3_2.proof
      HighFamily82190_3.schedule HighFamily82190_3.ledger)
    HighFamily82190_2.terminal
    (HighFamily82190_5.of_children HighFamily82190_5_1.proof
      (HighFamily82190_5_2.of_children HighFamily82190_5_2_1.proof HighFamily82190_5_2_2.proof))

#print axioms high
end Heights82190
