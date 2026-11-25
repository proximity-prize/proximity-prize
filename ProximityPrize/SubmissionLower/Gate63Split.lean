import ProximityPrize.SubmissionLower.Gate61Assm
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
namespace Gate61Cell
open Gate61FreeCard (mn mx)
open Gate61FreeU3 (freeD)

/-- node of the `cell` recursion that splits axis 0 -/
theorem cell_node0 (P : Pr) (f l0 l1 l2 h0 h1 h2 : ℕ)
    (c0 : (Nat.blt (mn h2 (mn (h1 / 3) h0)) l2 || Nat.blt (2 * h0 + mn h2 (mn (h1 / 3) h0)) l1) = false)
    (c1 : Nat.ble (freeD (P.t0 - l0) (P.t1 - l1) (P.t2 - l2)) P.W = false)
    (c2 : Nat.ble (lhsV P (P.t0 - l0) (P.t1 - l1) (P.t2 - l2) h0 h1 h2) P.rhs = false)
    (c3 : (Nat.beq l0 h0 && Nat.beq l1 h1 && Nat.beq l2 h2) = false)
    (c4 : (Nat.ble (h1 - l1) (h0 - l0) && Nat.ble (h2 - l2) (h0 - l0)) = true)
    (a b : Bool) (ha : cell P f l0 l1 l2 ((l0 + h0) / 2) h1 h2 = a) (hb : cell P f ((l0 + h0) / 2 + 1) l1 l2 h0 h1 h2 = b) :
    cell P (f + 1) l0 l1 l2 h0 h1 h2 = (a && b) := by
  unfold cell
  simp only [c0, c1, c2, c3, c4, Bool.cond_false, Bool.cond_true, ha, hb]

theorem cell_node1 (P : Pr) (f l0 l1 l2 h0 h1 h2 : ℕ)
    (c0 : (Nat.blt (mn h2 (mn (h1 / 3) h0)) l2 || Nat.blt (2 * h0 + mn h2 (mn (h1 / 3) h0)) l1) = false)
    (c1 : Nat.ble (freeD (P.t0 - l0) (P.t1 - l1) (P.t2 - l2)) P.W = false)
    (c2 : Nat.ble (lhsV P (P.t0 - l0) (P.t1 - l1) (P.t2 - l2) h0 h1 h2) P.rhs = false)
    (c3 : (Nat.beq l0 h0 && Nat.beq l1 h1 && Nat.beq l2 h2) = false)
    (c4 : (Nat.ble (h1 - l1) (h0 - l0) && Nat.ble (h2 - l2) (h0 - l0)) = false)
    (c5 : Nat.ble (h2 - l2) (h1 - l1) = true)
    (a b : Bool) (ha : cell P f l0 l1 l2 h0 ((l1 + h1) / 2) h2 = a) (hb : cell P f l0 ((l1 + h1) / 2 + 1) l2 h0 h1 h2 = b) :
    cell P (f + 1) l0 l1 l2 h0 h1 h2 = (a && b) := by
  unfold cell
  simp only [c0, c1, c2, c3, c4, c5, Bool.cond_false, Bool.cond_true, ha, hb]

theorem cell_node2 (P : Pr) (f l0 l1 l2 h0 h1 h2 : ℕ)
    (c0 : (Nat.blt (mn h2 (mn (h1 / 3) h0)) l2 || Nat.blt (2 * h0 + mn h2 (mn (h1 / 3) h0)) l1) = false)
    (c1 : Nat.ble (freeD (P.t0 - l0) (P.t1 - l1) (P.t2 - l2)) P.W = false)
    (c2 : Nat.ble (lhsV P (P.t0 - l0) (P.t1 - l1) (P.t2 - l2) h0 h1 h2) P.rhs = false)
    (c3 : (Nat.beq l0 h0 && Nat.beq l1 h1 && Nat.beq l2 h2) = false)
    (c4 : (Nat.ble (h1 - l1) (h0 - l0) && Nat.ble (h2 - l2) (h0 - l0)) = false)
    (c5 : Nat.ble (h2 - l2) (h1 - l1) = false)
    (a b : Bool) (ha : cell P f l0 l1 l2 h0 h1 ((l2 + h2) / 2) = a) (hb : cell P f l0 l1 ((l2 + h2) / 2 + 1) h0 h1 h2 = b) :
    cell P (f + 1) l0 l1 l2 h0 h1 h2 = (a && b) := by
  unfold cell
  simp only [c0, c1, c2, c3, c4, c5, Bool.cond_false, ha, hb]

def allR (f : ℕ → Bool) (lo n : ℕ) : Bool := (List.range n).all fun d => f (lo + d)

theorem allR_zero (f : ℕ → Bool) (n : ℕ) : allR f 0 n = (List.range n).all f := by
  unfold allR
  simp only [Nat.zero_add]

theorem allR_add (f : ℕ → Bool) (lo n m : ℕ) (h1 : allR f lo n = true) (h2 : allR f (lo + n) m = true) :
    allR f lo (n + m) = true := by
  unfold allR at *
  rw [List.range_add]
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at *
  refine ⟨h1, ?_⟩
  simpa [Function.comp_def, Nat.add_assoc] using h2

theorem allR_one (f : ℕ → Bool) (lo : ℕ) (h : f lo = true) : allR f lo 1 = true := by
  simp [allR, h]

end Gate61Cell

namespace Gate61Cell
open Gate61FreeCard (mn mx)
open Gate61FreeU3 (freeD)

def lvBody (G : Gt) (r W B0 B1 B2 fuel : ℕ) (cv : ℕ → Option (ℕ × ℕ)) (a : ℕ) : Bool :=
  bif Nat.ble r a then Nat.ble (freeD (B0 - a * G.lb) (B1 - a * G.lj) (B2 - a * G.lt)) W
    else match cv a with
      | none => Nat.ble (freeD (B0 - a * G.lb) (B1 - a * G.lj) (B2 - a * G.lt)) W
      | some c => cell (mkPr G r a c.1 c.2 W B0 B1 B2) fuel 0 0 0 (B0 - a * G.lb) (B1 - a * G.lj) (B2 - a * G.lt)

theorem levelOK_eq (G : Gt) (r W B0 B1 B2 fuel : ℕ) (cv : ℕ → Option (ℕ × ℕ)) :
    levelOK G r W B0 B1 B2 fuel cv = (List.range (min (B0 / G.lb) (min (B1 / G.lj) (B2 / G.lt)) + 1)).all (lvBody G r W B0 B1 B2 fuel cv) := rfl

end Gate61Cell

namespace Gate61Cell
open Gate61FreeCard (mn mx)
open Gate61FreeU3 (freeD)
theorem lvBody_cell (G : Gt) (r a W B0 B1 B2 fuel : ℕ) (cv : ℕ → Option (ℕ × ℕ)) (c : ℕ × ℕ)
    (hr : Nat.ble r a = false) (hcv : cv a = some c) :
    lvBody G r W B0 B1 B2 fuel cv a =
      cell (mkPr G r a c.1 c.2 W B0 B1 B2) fuel 0 0 0 (B0 - a * G.lb) (B1 - a * G.lj) (B2 - a * G.lt) := by
  unfold lvBody
  simp only [hr, hcv, Bool.cond_false]
end Gate61Cell
