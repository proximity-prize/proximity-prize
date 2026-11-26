import ProximityPrize.SubmissionLower.R6966ProofNearLedgerApply
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable0_1
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable0_2
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable0_3
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable0_4
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable0_5
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable1_1
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable1_2
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable1_3
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable1_4
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable2_1
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable2_2
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable2_3
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable3_1
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable3_2

set_option Elab.async false

namespace Research6966.NearLedger

def quote (b : Fin 4) (a : ℕ) : Fin 23 → Fin 23 → Quote :=
  match b.val, a with
  | 0, 1 => q0_1
  | 0, 2 => q0_2
  | 0, 3 => q0_3
  | 0, 4 => q0_4
  | 0, 5 => q0_5
  | 1, 1 => q1_1
  | 1, 2 => q1_2
  | 1, 3 => q1_3
  | 1, 4 => q1_4
  | 2, 1 => q2_1
  | 2, 2 => q2_2
  | 2, 3 => q2_3
  | 3, 1 => q3_1
  | 3, 2 => q3_2
  | _, _ => fun _ _ => ⟨.degree, none, none, none⟩

theorem quote_valid (b : Fin 4) (a : ℕ) (lo : 1≤a) (hi : a≤(band b).maxGraph)
    (i j : Fin 23) : (quote b a i j).Valid (band b) a i j := by
  fin_cases b
  · change a≤5 at hi
    interval_cases a
    · exact q0_1_ok i j
    · exact q0_2_ok i j
    · exact q0_3_ok i j
    · exact q0_4_ok i j
    · exact q0_5_ok i j
  · change a≤4 at hi
    interval_cases a
    · exact q1_1_ok i j
    · exact q1_2_ok i j
    · exact q1_3_ok i j
    · exact q1_4_ok i j
  · change a≤3 at hi
    interval_cases a
    · exact q2_1_ok i j
    · exact q2_2_ok i j
    · exact q2_3_ok i j
  · change a≤2 at hi
    interval_cases a
    · exact q3_1_ok i j
    · exact q3_2_ok i j

theorem quoted_bounds {r : Fin 58} (I : Invoice (branch r)) (b : Fin 4) (a : ℕ)
    (lo : 1≤a) (hi : a≤(band b).maxGraph) (i j : Fin 23) (G : GraphEvidence (band b) a i j)
    (mass : G.onMass+G.offMass≤I.mass) :
    G.onDegree≤(quote b a i j).degreeCap (band b) a ∧ ∀ z, G.axes z≤(quote b a i j).axisCap i j z :=
  (quote b a i j).bounds (quote_valid b a lo hi i j) G ((Nat.le_add_right _ _).trans (mass.trans I.mass_le))

theorem finish {r : Fin 58} (I : Invoice (branch r)) (b : Fin 4) (a : ℕ)
    (lo : 1≤a) (hi : a≤(band b).maxGraph) (i j : Fin 23) (G : GraphEvidence (band b) a i j)
    (mass : G.onMass+G.offMass≤I.mass) (tail : ℕ)
    (count : (quote b a i j).Demand (band b) a i j I G tail) : I.paid+tail≤core :=
  Quote.finish I (quote_valid b a lo hi i j) G mass tail count

end Research6966.NearLedger
