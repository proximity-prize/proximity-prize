import ProximityPrize.SubmissionLower.Z6970GateRowWord

set_option autoImplicit false
namespace Gate6970Row
open Gate6966Cell (Gt Lv levelOKF)
open ExpandedGate6970.H2307Numeric (defaultRow checked)

abbrev Row := ℕ × ℕ × ℕ × ℕ

def rowOK (g : Gt) (r word : ℕ) (row : Row) : Bool :=
  let (b,j,t,w) := row
  levelOKF g r w b j t 80 (fun a => some (wordCV word r a))

def run (g : Gt) : ℕ → ℕ → List ℕ → Lv → Bool
  | 0, _, _, _ => true
  | n+1, r, ws, lv =>
    rowOK g r (ws.getD 0 0) (lv.getD 0 defaultRow) && run g n (r+1) ws.tail lv.tail

def scan (g : Gt) (ws : List ℕ) (lv : Lv) (lo n : ℕ) : Bool :=
  run g n (lo+1) (ws.drop lo) (lv.drop lo)

private theorem first_after_drop {α : Type} (xs : List α) (lo : ℕ) (z : α) :
    (xs.drop lo).getD 0 z = xs.getD lo z := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]

private theorem row_eq (g : Gt) (ws : List ℕ) (i : ℕ) (row : Row) :
    rowOK g (i+1) (ws.getD i 0) row =
      (let (b,j,t,w) := row
       levelOKF g (i+1) w b j t 80 (fun a => some (Gate6966CertCF.cvOf 1 ws (i+1) a))) := by
  rcases row with ⟨b,j,t,w⟩
  simp only [rowOK, wordCV_eq]

theorem scan_eq (g : Gt) (ws : List ℕ) (lv : Lv) (lo n : ℕ) :
    scan g ws lv lo n = checked g ws lv lo n := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    change (rowOK g (lo+1) ((ws.drop lo).getD 0 0) ((lv.drop lo).getD 0 defaultRow) &&
      run g n (lo+1+1) (ws.drop lo).tail (lv.drop lo).tail) = _
    rw [first_after_drop,first_after_drop,row_eq,← List.drop_add_one_eq_tail_drop,← List.drop_add_one_eq_tail_drop]
    change (_ && scan g ws lv (lo+1) n) = _
    rw [ih]
    simp only [checked, List.range_succ_eq_map, List.all_cons, List.all_map, Function.comp_def,
      Nat.add_zero, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1]

end Gate6970Row
