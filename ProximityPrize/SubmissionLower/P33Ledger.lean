/- P33Ledger (Bome2017 tree): row dispatch. A terminal row whose envelope carries a composition certificate
with `bound ≤ terminalLimit` is counted by `composition_card_le`; every other row by Bome2017's
`terminal_count` (K6833TerminalCount.lean:170), unchanged. -/
import ProximityPrize.SubmissionLower.P33CertCells
import ProximityPrize.SubmissionLower.P33Composition

namespace ProximityPrize
namespace SubmissionLower
namespace P33
open scoped Classical BigOperators
open RCN095 RCN266 LocatorFactorAggregate
open K6833Residual Koala6831MovingAdaptive Koala6831MovingPaid
set_option autoImplicit false

def isCert (e : Envelope) : Option CertCell := certCells.find? (fun c => c.env = e)

theorem isCert_mem {e : Envelope} {c : CertCell} (h : isCert e = some c) : c ∈ certCells ∧ c.env = e := by
  unfold isCert at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem certCheck_of_mem {c : CertCell} (h : c ∈ certCells) : certCheck c = true :=
  List.all_eq_true.mp certCells_ok c h

/-- The row is certified: its envelope has a certificate cell whose bound is within the row's limit. -/
def certRow (row : TerminalRow) : Bool :=
  match isCert row.envelope with
  | some c => decide (c.bound ≤ row.terminalLimit)
  | none => false

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]

/-- Replaces `terminal_count` at `Mid6833Candidate6833.lean:45`: certificate rows use the composition
certificate (bound ≤ row.terminalLimit), all other rows `terminal_count` with `validRow`. -/
theorem row_count {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (row : TerminalRow) (valid : validRow row = true ∨ certRow row = true)
    (hs : row.envelope.slope = (aggregateFlag T.primary A).all)
    (hy : row.envelope.middle = middle (aggregateFlag T.primary A))
    (ht : total (aggregateFlag T.primary A) ≤ row.envelope.total) :
    (A.biUnion (regularFiber T.primary T.seeds T.selected)).card ≤ row.terminalLimit := by
  by_cases hcr : certRow row = true
  · unfold certRow at hcr
    cases hc : isCert row.envelope with
    | none => rw [hc] at hcr; exact absurd hcr Bool.false_ne_true
    | some c =>
      rw [hc] at hcr
      have hb : c.bound ≤ row.terminalLimit := of_decide_eq_true hcr
      obtain ⟨hmem, henv⟩ := isCert_mem hc
      have hck := certCheck_of_mem hmem
      obtain ⟨_, _, hcE, _, _, _, _⟩ := certCheck_parts hck
      obtain ⟨hs1, hm1, _⟩ := caps_of c.env hcE
      have below : Below (aggregateFlag T.primary A) c.env.flag := by
        rw [henv]
        simp only [Below, Envelope.flag, total, middle] at hs hy ht ⊢
        omega
      exact (composition_card_le T A c hck ⟨hs1, hm1⟩ below).trans hb
  · exact terminal_count T A row (valid.resolve_right hcr) hs hy ht


/-! ### Row validity at 68.34: every row passes Bome2017's `validRow` or is a certificate row -/

def rowOK (row : TerminalRow) : Bool := validRow row || certRow row

theorem rows1_0_ok : K6833Residual.rows1_0.all rowOK = true := by decide +kernel
theorem rows1_1_ok : K6833Residual.rows1_1.all rowOK = true := by decide +kernel
theorem rows1_2_ok : K6833Residual.rows1_2.all rowOK = true := by decide +kernel
theorem rows1_3_ok : K6833Residual.rows1_3.all rowOK = true := by decide +kernel
theorem rows1_4_ok : K6833Residual.rows1_4.all rowOK = true := by decide +kernel
theorem rows1_5_ok : K6833Residual.rows1_5.all rowOK = true := by decide +kernel
theorem rows1_6_ok : K6833Residual.rows1_6.all rowOK = true := by decide +kernel
theorem rows1_7_ok : K6833Residual.rows1_7.all rowOK = true := by decide +kernel
theorem rows1_8_ok : K6833Residual.rows1_8.all rowOK = true := by decide +kernel
theorem rows2_0_ok : K6833Residual.rows2_0.all rowOK = true := by decide +kernel
theorem rows2_1_ok : K6833Residual.rows2_1.all rowOK = true := by decide +kernel
theorem rows2_2_ok : K6833Residual.rows2_2.all rowOK = true := by decide +kernel
theorem rows2_3_ok : K6833Residual.rows2_3.all rowOK = true := by decide +kernel
theorem rows2_4_ok : K6833Residual.rows2_4.all rowOK = true := by decide +kernel
theorem rows2_5_ok : K6833Residual.rows2_5.all rowOK = true := by decide +kernel
theorem rows2_6_ok : K6833Residual.rows2_6.all rowOK = true := by decide +kernel
theorem rows2_7_ok : K6833Residual.rows2_7.all rowOK = true := by decide +kernel
theorem rows2_8_ok : K6833Residual.rows2_8.all rowOK = true := by decide +kernel
theorem rows3_0_ok : K6833Residual.rows3_0.all rowOK = true := by decide +kernel
theorem rows3_1_ok : K6833Residual.rows3_1.all rowOK = true := by decide +kernel
theorem rows3_2_ok : K6833Residual.rows3_2.all rowOK = true := by decide +kernel
theorem rows3_3_ok : K6833Residual.rows3_3.all rowOK = true := by decide +kernel
theorem rows3_4_ok : K6833Residual.rows3_4.all rowOK = true := by decide +kernel
theorem rows3_5_ok : K6833Residual.rows3_5.all rowOK = true := by decide +kernel
theorem rows3_6_ok : K6833Residual.rows3_6.all rowOK = true := by decide +kernel
theorem rows3_7_ok : K6833Residual.rows3_7.all rowOK = true := by decide +kernel
theorem rows4_0_ok : K6833Residual.rows4_0.all rowOK = true := by decide +kernel
theorem rows4_1_ok : K6833Residual.rows4_1.all rowOK = true := by decide +kernel
theorem rows4_2_ok : K6833Residual.rows4_2.all rowOK = true := by decide +kernel
theorem rows4_3_ok : K6833Residual.rows4_3.all rowOK = true := by decide +kernel
theorem rows4_4_ok : K6833Residual.rows4_4.all rowOK = true := by decide +kernel
theorem rows4_5_ok : K6833Residual.rows4_5.all rowOK = true := by decide +kernel
theorem rows4_6_ok : K6833Residual.rows4_6.all rowOK = true := by decide +kernel
theorem rows4_7_ok : K6833Residual.rows4_7.all rowOK = true := by decide +kernel
theorem rows5_0_ok : K6833Residual.rows5_0.all rowOK = true := by decide +kernel
theorem rows5_1_ok : K6833Residual.rows5_1.all rowOK = true := by decide +kernel
theorem rows5_2_ok : K6833Residual.rows5_2.all rowOK = true := by decide +kernel
theorem rows5_3_ok : K6833Residual.rows5_3.all rowOK = true := by decide +kernel
theorem rows5_4_ok : K6833Residual.rows5_4.all rowOK = true := by decide +kernel
theorem rows5_5_ok : K6833Residual.rows5_5.all rowOK = true := by decide +kernel
theorem rows5_6_ok : K6833Residual.rows5_6.all rowOK = true := by decide +kernel
theorem rows5_7_ok : K6833Residual.rows5_7.all rowOK = true := by decide +kernel
theorem rows6_0_ok : K6833Residual.rows6_0.all rowOK = true := by decide +kernel
theorem rows6_1_ok : K6833Residual.rows6_1.all rowOK = true := by decide +kernel
theorem rows6_2_ok : K6833Residual.rows6_2.all rowOK = true := by decide +kernel
theorem rows6_3_ok : K6833Residual.rows6_3.all rowOK = true := by decide +kernel
theorem rows6_4_ok : K6833Residual.rows6_4.all rowOK = true := by decide +kernel
theorem rows6_5_ok : K6833Residual.rows6_5.all rowOK = true := by decide +kernel
theorem rows6_6_ok : K6833Residual.rows6_6.all rowOK = true := by decide +kernel
theorem rows6_7_ok : K6833Residual.rows6_7.all rowOK = true := by decide +kernel
theorem rows7_0_ok : K6833Residual.rows7_0.all rowOK = true := by decide +kernel
theorem rows7_1_ok : K6833Residual.rows7_1.all rowOK = true := by decide +kernel
theorem rows7_2_ok : K6833Residual.rows7_2.all rowOK = true := by decide +kernel
theorem rows7_3_ok : K6833Residual.rows7_3.all rowOK = true := by decide +kernel
theorem rows7_4_ok : K6833Residual.rows7_4.all rowOK = true := by decide +kernel
theorem rows7_5_ok : K6833Residual.rows7_5.all rowOK = true := by decide +kernel
theorem rows7_6_ok : K6833Residual.rows7_6.all rowOK = true := by decide +kernel
theorem rows8_0_ok : K6833Residual.rows8_0.all rowOK = true := by decide +kernel
theorem rows8_1_ok : K6833Residual.rows8_1.all rowOK = true := by decide +kernel
theorem rows8_2_ok : K6833Residual.rows8_2.all rowOK = true := by decide +kernel
theorem rows8_3_ok : K6833Residual.rows8_3.all rowOK = true := by decide +kernel
theorem rows8_4_ok : K6833Residual.rows8_4.all rowOK = true := by decide +kernel
theorem rows8_5_ok : K6833Residual.rows8_5.all rowOK = true := by decide +kernel
theorem rows8_6_ok : K6833Residual.rows8_6.all rowOK = true := by decide +kernel
theorem rows9_0_ok : K6833Residual.rows9_0.all rowOK = true := by decide +kernel
theorem rows9_1_ok : K6833Residual.rows9_1.all rowOK = true := by decide +kernel
theorem rows9_2_ok : K6833Residual.rows9_2.all rowOK = true := by decide +kernel
theorem rows9_3_ok : K6833Residual.rows9_3.all rowOK = true := by decide +kernel
theorem rows9_4_ok : K6833Residual.rows9_4.all rowOK = true := by decide +kernel
theorem rows9_5_ok : K6833Residual.rows9_5.all rowOK = true := by decide +kernel
theorem rows9_6_ok : K6833Residual.rows9_6.all rowOK = true := by decide +kernel
theorem rows10_0_ok : K6833Residual.rows10_0.all rowOK = true := by decide +kernel
theorem rows10_1_ok : K6833Residual.rows10_1.all rowOK = true := by decide +kernel
theorem rows10_2_ok : K6833Residual.rows10_2.all rowOK = true := by decide +kernel
theorem rows10_3_ok : K6833Residual.rows10_3.all rowOK = true := by decide +kernel
theorem rows10_4_ok : K6833Residual.rows10_4.all rowOK = true := by decide +kernel
theorem rows10_5_ok : K6833Residual.rows10_5.all rowOK = true := by decide +kernel
theorem rows11_0_ok : K6833Residual.rows11_0.all rowOK = true := by decide +kernel
theorem rows11_1_ok : K6833Residual.rows11_1.all rowOK = true := by decide +kernel
theorem rows11_2_ok : K6833Residual.rows11_2.all rowOK = true := by decide +kernel
theorem rows11_3_ok : K6833Residual.rows11_3.all rowOK = true := by decide +kernel
theorem rows11_4_ok : K6833Residual.rows11_4.all rowOK = true := by decide +kernel
theorem rows11_5_ok : K6833Residual.rows11_5.all rowOK = true := by decide +kernel
theorem rows12_0_ok : K6833Residual.rows12_0.all rowOK = true := by decide +kernel
theorem rows12_1_ok : K6833Residual.rows12_1.all rowOK = true := by decide +kernel
theorem rows12_2_ok : K6833Residual.rows12_2.all rowOK = true := by decide +kernel
theorem rows12_3_ok : K6833Residual.rows12_3.all rowOK = true := by decide +kernel
theorem rows12_4_ok : K6833Residual.rows12_4.all rowOK = true := by decide +kernel
theorem rows13_0_ok : K6833Residual.rows13_0.all rowOK = true := by decide +kernel
theorem rows13_1_ok : K6833Residual.rows13_1.all rowOK = true := by decide +kernel
theorem rows13_2_ok : K6833Residual.rows13_2.all rowOK = true := by decide +kernel
theorem rows13_3_ok : K6833Residual.rows13_3.all rowOK = true := by decide +kernel
theorem rows14_0_ok : K6833Residual.rows14_0.all rowOK = true := by decide +kernel
theorem rows14_1_ok : K6833Residual.rows14_1.all rowOK = true := by decide +kernel
theorem rows14_2_ok : K6833Residual.rows14_2.all rowOK = true := by decide +kernel
theorem rows14_3_ok : K6833Residual.rows14_3.all rowOK = true := by decide +kernel
theorem rows15_0_ok : K6833Residual.rows15_0.all rowOK = true := by decide +kernel
theorem rows15_1_ok : K6833Residual.rows15_1.all rowOK = true := by decide +kernel
theorem rows16_0_ok : K6833Residual.rows16_0.all rowOK = true := by decide +kernel
theorem rows1_ok : K6833Residual.rows1.all rowOK = true := by
  simp only [K6833Residual.rows1, List.all_append, rows1_0_ok, rows1_1_ok, rows1_2_ok, rows1_3_ok, rows1_4_ok, rows1_5_ok, rows1_6_ok, rows1_7_ok, rows1_8_ok, Bool.and_self]
theorem rows2_ok : K6833Residual.rows2.all rowOK = true := by
  simp only [K6833Residual.rows2, List.all_append, rows2_0_ok, rows2_1_ok, rows2_2_ok, rows2_3_ok, rows2_4_ok, rows2_5_ok, rows2_6_ok, rows2_7_ok, rows2_8_ok, Bool.and_self]
theorem rows3_ok : K6833Residual.rows3.all rowOK = true := by
  simp only [K6833Residual.rows3, List.all_append, rows3_0_ok, rows3_1_ok, rows3_2_ok, rows3_3_ok, rows3_4_ok, rows3_5_ok, rows3_6_ok, rows3_7_ok, Bool.and_self]
theorem rows4_ok : K6833Residual.rows4.all rowOK = true := by
  simp only [K6833Residual.rows4, List.all_append, rows4_0_ok, rows4_1_ok, rows4_2_ok, rows4_3_ok, rows4_4_ok, rows4_5_ok, rows4_6_ok, rows4_7_ok, Bool.and_self]
theorem rows5_ok : K6833Residual.rows5.all rowOK = true := by
  simp only [K6833Residual.rows5, List.all_append, rows5_0_ok, rows5_1_ok, rows5_2_ok, rows5_3_ok, rows5_4_ok, rows5_5_ok, rows5_6_ok, rows5_7_ok, Bool.and_self]
theorem rows6_ok : K6833Residual.rows6.all rowOK = true := by
  simp only [K6833Residual.rows6, List.all_append, rows6_0_ok, rows6_1_ok, rows6_2_ok, rows6_3_ok, rows6_4_ok, rows6_5_ok, rows6_6_ok, rows6_7_ok, Bool.and_self]
theorem rows7_ok : K6833Residual.rows7.all rowOK = true := by
  simp only [K6833Residual.rows7, List.all_append, rows7_0_ok, rows7_1_ok, rows7_2_ok, rows7_3_ok, rows7_4_ok, rows7_5_ok, rows7_6_ok, Bool.and_self]
theorem rows8_ok : K6833Residual.rows8.all rowOK = true := by
  simp only [K6833Residual.rows8, List.all_append, rows8_0_ok, rows8_1_ok, rows8_2_ok, rows8_3_ok, rows8_4_ok, rows8_5_ok, rows8_6_ok, Bool.and_self]
theorem rows9_ok : K6833Residual.rows9.all rowOK = true := by
  simp only [K6833Residual.rows9, List.all_append, rows9_0_ok, rows9_1_ok, rows9_2_ok, rows9_3_ok, rows9_4_ok, rows9_5_ok, rows9_6_ok, Bool.and_self]
theorem rows10_ok : K6833Residual.rows10.all rowOK = true := by
  simp only [K6833Residual.rows10, List.all_append, rows10_0_ok, rows10_1_ok, rows10_2_ok, rows10_3_ok, rows10_4_ok, rows10_5_ok, Bool.and_self]
theorem rows11_ok : K6833Residual.rows11.all rowOK = true := by
  simp only [K6833Residual.rows11, List.all_append, rows11_0_ok, rows11_1_ok, rows11_2_ok, rows11_3_ok, rows11_4_ok, rows11_5_ok, Bool.and_self]
theorem rows12_ok : K6833Residual.rows12.all rowOK = true := by
  simp only [K6833Residual.rows12, List.all_append, rows12_0_ok, rows12_1_ok, rows12_2_ok, rows12_3_ok, rows12_4_ok, Bool.and_self]
theorem rows13_ok : K6833Residual.rows13.all rowOK = true := by
  simp only [K6833Residual.rows13, List.all_append, rows13_0_ok, rows13_1_ok, rows13_2_ok, rows13_3_ok, Bool.and_self]
theorem rows14_ok : K6833Residual.rows14.all rowOK = true := by
  simp only [K6833Residual.rows14, List.all_append, rows14_0_ok, rows14_1_ok, rows14_2_ok, rows14_3_ok, Bool.and_self]
theorem rows15_ok : K6833Residual.rows15.all rowOK = true := by
  simp only [K6833Residual.rows15, List.all_append, rows15_0_ok, rows15_1_ok, Bool.and_self]
theorem rows16_ok : K6833Residual.rows16.all rowOK = true := by
  simp only [K6833Residual.rows16, List.all_append, rows16_0_ok, Bool.and_self]
theorem all_rows_ok (r : ℕ) : (rowsBySlope r).all rowOK = true := by
  rcases r with _|r
  · rfl
  rcases r with _|r
  · exact rows1_ok
  rcases r with _|r
  · exact rows2_ok
  rcases r with _|r
  · exact rows3_ok
  rcases r with _|r
  · exact rows4_ok
  rcases r with _|r
  · exact rows5_ok
  rcases r with _|r
  · exact rows6_ok
  rcases r with _|r
  · exact rows7_ok
  rcases r with _|r
  · exact rows8_ok
  rcases r with _|r
  · exact rows9_ok
  rcases r with _|r
  · exact rows10_ok
  rcases r with _|r
  · exact rows11_ok
  rcases r with _|r
  · exact rows12_ok
  rcases r with _|r
  · exact rows13_ok
  rcases r with _|r
  · exact rows14_ok
  rcases r with _|r
  · exact rows15_ok
  rcases r with _|r
  · exact rows16_ok
  rfl

theorem rowAt_ok {r y : ℕ} {row : TerminalRow} (h : rowAt r y = some row) :
    validRow row = true ∨ certRow row = true := by
  have h1 := List.all_eq_true.mp (all_rows_ok r) _ (List.mem_of_getElem? h)
  simpa only [rowOK, Bool.or_eq_true] using h1

end P33
end SubmissionLower
end ProximityPrize
