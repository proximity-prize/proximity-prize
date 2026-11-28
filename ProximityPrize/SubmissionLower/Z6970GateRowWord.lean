import ProximityPrize.SubmissionLower.Z6970H2307FastGateNumeric

set_option Elab.async false
set_option autoImplicit false

namespace Gate6970Row

/-- Evaluate the class weights using a word already selected for this level. -/
def wordCV (w r a : ℕ) : ℕ × ℕ :=
  bif Nat.beq a 0 then (0, 0)
  else match (if 1 ≤ a ∧ a ≤ w % 256 then some (Gate6966ClassTable.decode w a) else none) with
    | some (k, vn) => (min (2 * (r - a)) (k * a), vn)
    | none => (2 * (r - a), (10000000 * a * a + (r - a) * (r - a) - 1) / ((r - a) * (r - a)))

theorem wordCV_eq (ws : List ℕ) (i a : ℕ) :
    wordCV (ws.getD i 0) (i + 1) a = Gate6966CertCF.cvOf 1 ws (i + 1) a := by
  have one : 1 ≤ i + 1 := by omega
  by_cases inList : i < ws.length
  · by_cases fits : 1 ≤ a ∧ a ≤ ws.getD i 0 % 256
    · simp only [wordCV, Gate6966CertCF.cvOf, Gate6966ClassTable.lookup,
        Nat.add_sub_cancel, one, inList, true_and, if_pos fits]
    · simp only [wordCV, Gate6966CertCF.cvOf, Gate6966ClassTable.lookup,
        Nat.add_sub_cancel, one, inList, true_and, if_neg fits]
  · have out : ws.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    have noClass : ¬ (1 ≤ a ∧ a ≤ 0 % 256) := by omega
    simp only [wordCV, Gate6966CertCF.cvOf, Gate6966ClassTable.lookup,
      Nat.add_sub_cancel, out, inList, and_false, ite_false, noClass]

end Gate6970Row
