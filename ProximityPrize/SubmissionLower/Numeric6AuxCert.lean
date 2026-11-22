import ProximityPrize.SubmissionLower.Numeric6Defs
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_1
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
end CJ6_1
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3
open scoped BigOperators
private def decode (code : ℕ) : Powers :=
  ⟨code % 2048, code / 2048 % 1024, code / 2097152 % 1024⟩
private def runLength (code : ℕ) : ℕ := code / 2147483648 + 1
private def rowLength : List ℕ → ℕ
  | [] => 0
  | code :: tail => runLength code + rowLength tail
private def rowPower (k : ℕ) : List ℕ → Powers
  | [] => ⟨0, 0, 0⟩
  | code :: tail =>
    if k < runLength code then decode code else rowPower (k - runLength code) tail
private def sumFrom (f : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumFrom f j n + f (j + n)
private theorem sumFrom_eq (f : ℕ → ℕ) (j n : ℕ) :
    sumFrom f j n = ∑ k ∈ Finset.range n, f (j + k) := by
  induction n with
  | zero => simp [sumFrom]
  | succ n ih => rw [sumFrom, Finset.sum_range_succ, ih]
private def runValue (s j code : ℕ) : ℕ :=
  if code % 2147483648 = 0 then 0
  else sumFrom (fun u => blockSaving s u (decode code)) j (runLength code)
private theorem runValue_eq (s j code : ℕ) :
    runValue s j code = ∑ k ∈ Finset.range (runLength code),
      blockSaving s (j + k) (decode code) := by
  unfold runValue
  split
  · rename_i h
    have hz : decode code = ⟨0, 0, 0⟩ := by
      unfold decode
      congr <;> omega
    simp [hz, blockSaving_zero]
  · exact sumFrom_eq _ _ _
private def rowValue (s j : ℕ) : List ℕ → ℕ
  | [] => 0
  | code :: tail => runValue s j code + rowValue s (j + runLength code) tail
private theorem rowValue_eq (s j : ℕ) (row : List ℕ) :
    rowValue s j row = ∑ k ∈ Finset.range (rowLength row),
      blockSaving s (j + k) (rowPower k row) := by
  induction row generalizing j with
  | nil => simp [rowValue, rowLength]
  | cons code tail ih =>
    rw [rowValue, runValue_eq, ih, rowLength, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      simp [rowPower, Finset.mem_range.mp hk]
    · apply Finset.sum_congr rfl
      intro k hk
      simp (disch := omega) [rowPower, add_assoc]
private def rowStart (s : ℕ) : ℕ := max 23 (3333 - s)
def value (s : ℕ) : List (List ℕ) → ℕ
  | [] => 0
  | row :: tail => rowValue s (rowStart s) row + value (s + 1) tail
def fits (s : ℕ) : List (List ℕ) → Bool
  | [] => true
  | row :: tail =>
    decide (rowStart s + rowLength row ≤ 409 ∧ s + rowStart s + rowLength row ≤ 3797)
      && fits (s + 1) tail
theorem value_append (s : ℕ) (a b : List (List ℕ)) :
    value s (a ++ b) = value s a + value (s + a.length) b := by
  induction a generalizing s with
  | nil => simp [value]
  | cons row tail ih =>
    simp only [List.cons_append, value, List.length_cons, ih, add_assoc, Nat.add_comm 1 tail.length]
theorem fits_append (s : ℕ) (a b : List (List ℕ)) :
    fits s (a ++ b) = (fits s a && fits (s + a.length) b) := by
  induction a generalizing s with
  | nil => simp [fits]
  | cons row tail ih =>
    simp only [List.cons_append, fits, List.length_cons, ih, Bool.and_assoc]
    rw [show s + 1 + tail.length = s + (tail.length + 1) by omega]
private theorem rows_eq (s : ℕ) (rows : List (List ℕ)) :
    value s rows = ∑ k ∈ Finset.range rows.length,
      rowValue (s + k) (rowStart (s + k)) (rows[k]?.getD []) := by
  induction rows generalizing s with
  | nil => simp [value]
  | cons row tail ih =>
    rw [value, List.length_cons, Finset.sum_range_succ', ih]
    simp only [add_zero, List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [show s + 1 + k = s + (k + 1) by omega]
private theorem fit_row (s : ℕ) (rows : List (List ℕ)) (h : fits s rows = true)
    (k : ℕ) (hk : k < rows.length) :
    rowStart (s + k) + rowLength (rows[k]?.getD []) ≤ 409 ∧
      s + k + rowStart (s + k) + rowLength (rows[k]?.getD []) ≤ 3797 := by
  induction rows generalizing s k with
  | nil => simp at hk
  | cons row tail ih =>
    have hs := Bool.and_eq_true_iff.mp h
    cases k with
    | zero => simpa using (of_decide_eq_true hs.1)
    | succ k =>
      have he : s + (k + 1) = s + 1 + k := by omega
      simpa only [Nat.succ_eq_add_one, he, List.getElem?_cons_succ] using
        ih (s + 1) hs.2 k (by simpa using hk)
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
theorem value_le_savingsSum (start : ℕ) (rows : List (List ℕ))
    (hstart : 3012 ≤ start) (hend : start + rows.length ≤ 3514)
    (hfit : fits start rows = true) :
    ∃ p : BlockIndex → Powers, value start rows ≤ savingsSum w3 p := by
  let p : BlockIndex → Powers := fun i =>
    rowPower (i.2.val - rowStart i.1.val) (rows[i.1.val - start]?.getD [])
  refine ⟨p, ?_⟩
  unfold savingsSum
  rw [← Finset.univ_product_univ, Finset.sum_product, sum_wrap 4013 (by decide), rows_eq]
  apply le_trans _ (sum_subinterval _ (show start + rows.length ≤ 4013 by omega))
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  let s := start + k
  let row := rows[k]?.getD []
  have hs : 3012 ≤ s ∧ s < 3514 := by dsimp [s]; omega
  have hf := fit_row start rows hfit k hk'
  change rowStart s + rowLength row ≤ 409 ∧ s + rowStart s + rowLength row ≤ 3797 at hf
  rw [sum_wrap 4650 (by decide), rowValue_eq]
  apply le_trans _ (sum_subinterval _ (show rowStart s + rowLength row ≤ 4650 by omega))
  apply Finset.sum_le_sum
  intro k' hk'
  have hlt := Finset.mem_range.mp hk'
  change k' < rowLength row at hlt
  let j := rowStart s + k'
  have hj : j < 4650 := by dsimp [j]; omega
  let i : BlockIndex := (wrap 4013 (by decide) s, wrap 4650 (by decide) j)
  have his : i.1.val = s := Nat.mod_eq_of_lt (by omega)
  have hij : i.2.val = j := Nat.mod_eq_of_lt hj
  have hw : w3.Contains i := by
    change 3012 ≤ i.1.val ∧ i.1.val < 3514 ∧ 23 ≤ i.2.val ∧ i.2.val ≤ 408 ∧
      3333 ≤ i.1.val + i.2.val ∧ i.1.val + i.2.val ≤ 3796
    rw [his, hij]
    have h₁ : 23 ≤ rowStart s := le_max_left _ _
    have h₂ : 3333 - s ≤ rowStart s := le_max_right _ _
    dsimp [j]
    omega
  have hp : p i = rowPower k' row := by
    dsimp only [p]
    rw [his, hij]
    have he : s - start = k := by dsimp [s]; omega
    simp only [he, j, Nat.add_sub_cancel_left, row]
  change blockSaving s j (rowPower k' row) ≤ if w3.Contains i then savings i (p i) else 0
  rw [ite_eq_left hw, hp, ← his, ← hij, blockSaving_eq i _ hw]
end K1_13_2_3_6
end
