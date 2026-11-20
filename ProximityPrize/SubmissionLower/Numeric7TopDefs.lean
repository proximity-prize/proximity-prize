import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Numeric6Defs
set_option Elab.async false

/-! w4 top-factor upgrade (6916 radius work, source 12b4b15d + c6c7 patch).

The official w4 witness is `⟨valuePower s j, 0, 0⟩` (Fast049/Fast068, total 177382348097).
Here a table of rows `(start offset, tops)` per grade replaces the top exponent on listed cells by
`⟨valuePower s j, t, 0⟩`. Every listed cell must not lose savings (`okCell`); the extra savings
are `gainCell`. `savings_top` turns a checked table into
`savingsSum w4 witness + value ≤ savingsSum w4 (witnessTop rows start)`.
Cell values use `K1_13_2_3_6.blockSaving`, which equals `savings` on any block with
`1650 ≤ s`, `j ≤ 2999`, `s + j < 4650` (`blockSaving_eq_of`), in particular on all of w4.
UNBUILT. -/

section PackSource_K1_13_2_3_7TopDefs
set_option autoImplicit true
namespace K1_13_2_3_7

open K1_13_2 K1_13_2_3
open scoped BigOperators

def topPowers (s j t : ℕ) : Powers := ⟨valuePower s j, t, 0⟩

theorem witness_eq (i : BlockIndex) : witness i = topPowers i.1.val i.2.val 0 := rfl

def gainCell (s j t : ℕ) : ℕ :=
  K1_13_2_3_6.blockSaving s j (topPowers s j t) - K1_13_2_3_6.blockSaving s j (topPowers s j 0)

def okCell (s j t : ℕ) : Bool :=
  decide (K1_13_2_3_6.blockSaving s j (topPowers s j 0) ≤
    K1_13_2_3_6.blockSaving s j (topPowers s j t))

theorem okCell_zero (s j : ℕ) : okCell s j 0 = true := by
  simp [okCell]

theorem blockSaving_eq_w4 (i : BlockIndex) (p : Powers) (hw : w4.Contains i) :
    K1_13_2_3_6.blockSaving i.1.val i.2.val p = savings i p := by
  rcases hw with ⟨hs, _, _, hj, _, hsum⟩
  change 3514 ≤ i.1.val at hs
  change i.2.val ≤ 282 at hj
  change i.1.val + i.2.val ≤ 4170 at hsum
  exact K1_13_2_3_6.blockSaving_eq_of i p (by omega) (by omega) (by omega)

/-- Top exponent at position `k` of a row; zero past the end. -/
def topIn : ℕ → List ℕ → ℕ
  | _, [] => 0
  | 0, t :: _ => t
  | k + 1, _ :: tail => topIn k tail

def rowGain (s j : ℕ) : List ℕ → ℕ
  | [] => 0
  | t :: tail => gainCell s j t + rowGain s (j + 1) tail

def rowOk (s j : ℕ) : List ℕ → Bool
  | [] => true
  | t :: tail => okCell s j t && rowOk s (j + 1) tail

theorem rowOk_topIn (s j₀ : ℕ) (l : List ℕ) (h : rowOk s j₀ l = true) (k : ℕ) :
    okCell s (j₀ + k) (topIn k l) = true := by
  induction l generalizing j₀ k with
  | nil => simp only [topIn, okCell_zero]
  | cons t tail ih =>
    have hb := Bool.and_eq_true_iff.mp h
    cases k with
    | zero => simpa [topIn] using hb.1
    | succ k =>
      have := ih (j₀ + 1) hb.2 k
      simpa only [topIn, show j₀ + (k + 1) = j₀ + 1 + k by omega] using this

theorem rowGain_eq (s j : ℕ) (l : List ℕ) :
    rowGain s j l = ∑ k ∈ Finset.range l.length, gainCell s (j + k) (topIn k l) := by
  induction l generalizing j with
  | nil => simp [rowGain]
  | cons t tail ih =>
    rw [rowGain, ih, List.length_cons, Finset.sum_range_succ']
    simp only [topIn, add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show j + (k + 1) = j + 1 + k by omega]

abbrev TopRow := ℕ × List ℕ

def value (s : ℕ) : List TopRow → ℕ
  | [] => 0
  | r :: tail => rowGain s r.1 r.2 + value (s + 1) tail

/-- Every listed cell lies in w4 (offset ≤ 282, diagonal 3537..4170) and does not lose savings. -/
def fits (s : ℕ) : List TopRow → Bool
  | [] => true
  | r :: tail =>
    (decide (3537 ≤ s + r.1 ∧ r.1 + r.2.length ≤ 283 ∧ s + r.1 + r.2.length ≤ 4171) &&
      rowOk s r.1 r.2) && fits (s + 1) tail

theorem value_append (s : ℕ) (a b : List TopRow) :
    value s (a ++ b) = value s a + value (s + a.length) b := by
  induction a generalizing s with
  | nil => simp [value]
  | cons row tail ih =>
    simp only [List.cons_append, value, List.length_cons, ih, add_assoc, Nat.add_comm 1 tail.length]

theorem fits_append (s : ℕ) (a b : List TopRow) :
    fits s (a ++ b) = (fits s a && fits (s + a.length) b) := by
  induction a generalizing s with
  | nil => simp [fits]
  | cons row tail ih =>
    simp only [List.cons_append, fits, List.length_cons, ih, Bool.and_assoc]
    rw [show s + 1 + tail.length = s + (tail.length + 1) by omega]

def getRow (rows : List TopRow) (k : ℕ) : TopRow := rows[k]?.getD (0, [])

theorem fits_row (s : ℕ) (rows : List TopRow) (h : fits s rows = true) (k : ℕ) :
    rowOk (s + k) (getRow rows k).1 (getRow rows k).2 = true ∧
      (k < rows.length → 3537 ≤ s + k + (getRow rows k).1 ∧
        (getRow rows k).1 + (getRow rows k).2.length ≤ 283 ∧
        s + k + (getRow rows k).1 + (getRow rows k).2.length ≤ 4171) := by
  induction rows generalizing s k with
  | nil => simp [getRow, rowOk]
  | cons row tail ih =>
    have hs := Bool.and_eq_true_iff.mp h
    have hr := Bool.and_eq_true_iff.mp hs.1
    cases k with
    | zero =>
      refine ⟨by simpa [getRow] using hr.2, fun _ => ?_⟩
      simpa [getRow] using of_decide_eq_true hr.1
    | succ k =>
      have he : s + (k + 1) = s + 1 + k := by omega
      have := ih (s + 1) hs.2 k
      simp only [getRow, List.getElem?_cons_succ, List.length_cons] at this ⊢
      rw [he]
      exact ⟨this.1, fun hk => this.2 (by omega)⟩

theorem value_eq (s : ℕ) (rows : List TopRow) :
    value s rows = ∑ k ∈ Finset.range rows.length,
      rowGain (s + k) (getRow rows k).1 (getRow rows k).2 := by
  induction rows generalizing s with
  | nil => simp [value]
  | cons row tail ih =>
    rw [value, List.length_cons, Finset.sum_range_succ', ih]
    simp only [getRow, add_zero, List.getElem?_cons_zero, Option.getD_some,
      List.getElem?_cons_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show s + 1 + k = s + (k + 1) by omega]

/-- The top exponent the table assigns to block `(s, j)`. -/
def topAt (rows : List TopRow) (start s j : ℕ) : ℕ :=
  if start ≤ s ∧ (getRow rows (s - start)).1 ≤ j then
    topIn (j - (getRow rows (s - start)).1) (getRow rows (s - start)).2
  else 0

def witnessTop (rows : List TopRow) (start : ℕ) (i : BlockIndex) : Powers :=
  topPowers i.1.val i.2.val (topAt rows start i.1.val i.2.val)

theorem ok_topAt (rows : List TopRow) (start : ℕ) (h : fits start rows = true) (s j : ℕ) :
    okCell s j (topAt rows start s j) = true := by
  unfold topAt
  split
  · rename_i hc
    have hr := (fits_row start rows h (s - start)).1
    rw [show start + (s - start) = s by omega] at hr
    have := rowOk_topIn s _ _ hr (j - (getRow rows (s - start)).1)
    rwa [show (getRow rows (s - start)).1 + (j - (getRow rows (s - start)).1) = j by omega]
      at this
  · exact okCell_zero s j

/-- Pointwise: on w4 the new witness keeps the official savings and adds `gainCell`. -/
theorem savings_top_cell (rows : List TopRow) (start : ℕ) (h : fits start rows = true)
    (i : BlockIndex) (hw : w4.Contains i) :
    savings i (witnessTop rows start i) =
      savings i (witness i) + gainCell i.1.val i.2.val (topAt rows start i.1.val i.2.val) := by
  have hok : K1_13_2_3_6.blockSaving i.1.val i.2.val (topPowers i.1.val i.2.val 0) ≤
      K1_13_2_3_6.blockSaving i.1.val i.2.val
        (topPowers i.1.val i.2.val (topAt rows start i.1.val i.2.val)) := by
    have := ok_topAt rows start h i.1.val i.2.val
    simpa [okCell] using this
  rw [witness_eq, witnessTop, ← blockSaving_eq_w4 i _ hw, ← blockSaving_eq_w4 i _ hw, gainCell]
  omega

private def wrap (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

private theorem wrap_val (n : ℕ) (hn : 0 < n) (i : Fin n) : wrap n hn i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

private theorem sum_wrap (n : ℕ) (hn : 0 < n) (f : Fin n → ℕ) :
    (∑ i : Fin n, f i) = ∑ j ∈ Finset.range n, f (wrap n hn j) := by
  simpa only [wrap_val] using
    (Fin.sum_univ_eq_sum_range (fun j => f (wrap n hn j)) n)

private theorem sum_subinterval (f : ℕ → ℕ) {a b n : ℕ} (h : a + b ≤ n) :
    (∑ j ∈ Finset.range b, f (a + j)) ≤ ∑ j ∈ Finset.range n, f j := by
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun _ _ _ => Nat.zero_le _))
  rw [Finset.sum_range_add]
  exact Nat.le_add_left _ _

/-- The table gain is dominated by the gain summed over w4. -/
theorem value_le_gainSum (start : ℕ) (rows : List TopRow)
    (hstart : 3514 ≤ start) (hend : start + rows.length ≤ 4013)
    (hfit : fits start rows = true) :
    value start rows ≤ ∑ i : BlockIndex,
      if w4.Contains i then gainCell i.1.val i.2.val (topAt rows start i.1.val i.2.val) else 0 := by
  rw [← Finset.univ_product_univ, Finset.sum_product, sum_wrap 4013 (by decide), value_eq]
  apply le_trans _ (sum_subinterval _ (show start + rows.length ≤ 4013 by omega))
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  let s := start + k
  let row := getRow rows k
  have hs : 3514 ≤ s ∧ s < 4013 := by dsimp [s]; omega
  have hf := (fits_row start rows hfit k).2 hk'
  change 3537 ≤ s + row.1 ∧ row.1 + row.2.length ≤ 283 ∧ s + row.1 + row.2.length ≤ 4171 at hf
  rw [sum_wrap 4650 (by decide), rowGain_eq]
  apply le_trans _ (sum_subinterval _ (show row.1 + row.2.length ≤ 4650 by omega))
  apply Finset.sum_le_sum
  intro k' hk''
  have hlt := Finset.mem_range.mp hk''
  let j := row.1 + k'
  have hj : j < 4650 := by dsimp [j]; omega
  let i : BlockIndex := (wrap 4013 (by decide) s, wrap 4650 (by decide) j)
  have his : i.1.val = s := Nat.mod_eq_of_lt (by omega)
  have hij : i.2.val = j := Nat.mod_eq_of_lt hj
  have hw : w4.Contains i := by
    change 3514 ≤ i.1.val ∧ i.1.val < 4013 ∧ 0 ≤ i.2.val ∧ i.2.val ≤ 282 ∧
      3537 ≤ i.1.val + i.2.val ∧ i.1.val + i.2.val ≤ 4170
    rw [his, hij]
    dsimp [j]
    omega
  have ht : topAt rows start s j = topIn k' row.2 := by
    have hsk : s - start = k := by dsimp [s]; omega
    have hc : start ≤ s ∧ (getRow rows (s - start)).1 ≤ j := by
      rw [hsk]; dsimp [s, j, row]; omega
    unfold topAt
    rw [if_pos hc, hsk]
    dsimp [j, row]
    rw [Nat.add_sub_cancel_left]
  change gainCell s j (topIn k' row.2) ≤
    if w4.Contains i then gainCell i.1.val i.2.val (topAt rows start i.1.val i.2.val) else 0
  rw [if_pos hw, his, hij, ht]

/-- Savings of the upgraded witness: official value-only total plus the table gain. -/
theorem savings_top (start : ℕ) (rows : List TopRow)
    (hstart : 3514 ≤ start) (hend : start + rows.length ≤ 4013)
    (hfit : fits start rows = true) :
    savingsSum w4 witness + value start rows ≤ savingsSum w4 (witnessTop rows start) := by
  have hcell : ∀ i : BlockIndex,
      (if w4.Contains i then savings i (witnessTop rows start i) else 0) =
        (if w4.Contains i then savings i (witness i) else 0) +
          (if w4.Contains i then gainCell i.1.val i.2.val (topAt rows start i.1.val i.2.val)
            else 0) := by
    intro i
    by_cases hw : w4.Contains i
    · rw [if_pos hw, if_pos hw, if_pos hw, savings_top_cell rows start hfit i hw]
    · rw [if_neg hw, if_neg hw, if_neg hw]
  unfold savingsSum
  rw [Finset.sum_congr rfl (fun i _ => hcell i), Finset.sum_add_distrib]
  exact Nat.add_le_add_left (value_le_gainSum start rows hstart hend hfit) _

end K1_13_2_3_7
end PackSource_K1_13_2_3_7TopDefs
