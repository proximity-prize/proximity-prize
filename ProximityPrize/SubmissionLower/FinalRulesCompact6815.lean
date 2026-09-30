import ProximityPrize.SubmissionLower.FinalRulesCached6815
import ProximityPrize.SubmissionLower.CompactAllN6815
namespace ProximityPrize.SubmissionLower.FinalRulesCompact6815
open FinalCurves6815 FinalRulesRowCheck6815 FinalRulesCached6815 SingletonCertificate6815 CompactAllN6815
set_option autoImplicit false

def rowL (r v : ℕ) (c w : List Piece) (n : ℕ) : Bool :=
  validFrom (11193-r-v) 0 w && Nat.ble w.length (8*n) && allN (fun b => blockL r v c w b) n

theorem row_of_rowL (r v : ℕ) (c w : List Piece) (n : ℕ) (hR : r≤39) (hy : r+v≤182)
    (h : rowL r v c w n=true) : checkRow r v c w=true := by
  simp only [rowL,Bool.and_eq_true,Nat.ble_eq] at h
  refine of_blocks r v c w n h.1.1 h.1.2 (fun b hb => ?_)
  rw [←blockL_eq r v c w b hR hy]
  exact allN_sound _ n h.2 b hb

theorem row_of_blocks (r v : ℕ) (c w : List Piece) (n : ℕ)
    (hv : validFrom (11193-r-v) 0 w=true) (hn : w.length≤8*n)
    (hb : allN (fun b => blockCheck r v c w b) n=true) : checkRow r v c w=true :=
  of_blocks r v c w n hv hn (fun b hb' => allN_sound _ n hb b hb')

theorem blk (r v : ℕ) (c w : List Piece) (b : ℕ) (hR : r≤39) (hy : r+v≤182)
    (h : blockL r v c w b=true) : blockCheck r v c w b=true := by
  rw [←blockL_eq r v c w b hR hy]; exact h

theorem blk8 (r v : ℕ) (c w : List Piece) (b : ℕ) (hR : r≤39) (hy : r+v≤182)
    (h0 : indexL r v c w (8*b+0)=true) (h1 : indexL r v c w (8*b+1)=true)
    (h2 : indexL r v c w (8*b+2)=true) (h3 : indexL r v c w (8*b+3)=true)
    (h4 : indexL r v c w (8*b+4)=true) (h5 : indexL r v c w (8*b+5)=true)
    (h6 : indexL r v c w (8*b+6)=true) (h7 : indexL r v c w (8*b+7)=true) :
    blockCheck r v c w b=true := by
  apply block_of_indices
  intro i hi
  rw [←indexL_eq r v c w _ hR hy]
  interval_cases i <;> assumption

def rowC (r v : ℕ) (c w : List Piece) (n : ℕ) : Bool :=
  validFrom (11193-r-v) 0 w && Nat.ble w.length (8*n) && allN (fun b => FinalRulesCapped6815.blockC r v c w b) n

theorem row_of_rowC (r v : ℕ) (c w : List Piece) (n : ℕ) (hR : r≤39) (hy : r+v≤182)
    (h : rowC r v c w n=true) : checkRow r v c w=true := by
  simp only [rowC,Bool.and_eq_true,Nat.ble_eq] at h
  refine of_blocks r v c w n h.1.1 h.1.2 (fun b hb => ?_)
  rw [←FinalRulesCapped6815.blockC_eq r v c w b hR hy]
  exact allN_sound _ n h.2 b hb

theorem blkC (r v : ℕ) (c w : List Piece) (b : ℕ) (hR : r≤39) (hy : r+v≤182)
    (h : FinalRulesCapped6815.blockC r v c w b=true) : blockCheck r v c w b=true := by
  rw [←FinalRulesCapped6815.blockC_eq r v c w b hR hy]; exact h

end ProximityPrize.SubmissionLower.FinalRulesCompact6815
