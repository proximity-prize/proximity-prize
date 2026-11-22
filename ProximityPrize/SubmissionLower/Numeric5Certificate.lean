import ProximityPrize.SubmissionLower.Numeric5Defs
set_option autoImplicit true
section
namespace K1_13_2_3_5
open K1_13_2 K1_13_2_3
open scoped BigOperators
structure Row where
  first : ℕ
  count : ℕ
  packed : ℕ
  deriving Inhabited
private def unpack (packed : ℕ) : Powers :=
  ⟨packed % 512, packed / 512 % 512, packed / 262144 % 1024⟩
private def powersAt : ℕ → ℕ → Powers
  | 0, packed => unpack packed
  | k + 1, packed => powersAt k (packed / 268435456)
private def rowLoop (s : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, j, packed =>
      certifiedSaving s j (unpack packed) + rowLoop s n (j + 1) (packed / 268435456)
private def rowScore (s : ℕ) (r : Row) : ℕ :=
  if 2008 ≤ s ∧ s < 3012 ∧ 322 ≤ r.first ∧ r.first + r.count ≤ 1063 ∧
    3000 ≤ s + r.first ∧ s + r.first + r.count ≤ 3420
  then rowLoop s r.count r.first r.packed else 0
def batchScore : ℕ → List Row → ℕ
  | _, [] => 0
  | s, r :: rs => rowScore s r + batchScore (s + 1) rs
theorem batchScore_append (s : ℕ) (xs ys : List Row) :
    batchScore s (xs ++ ys) = batchScore s xs + batchScore (s + xs.length) ys := by
  induction xs generalizing s with
  | nil => simp [batchScore]
  | cons x xs ih =>
    simp only [List.cons_append, batchScore, List.length_cons, ih]
    rw [show s + 1 + xs.length = s + (xs.length + 1) by omega, Nat.add_assoc]
private def rowPowers (r : Row) (j : ℕ) : Powers :=
  powersAt (j - r.first) r.packed
private def assignment (start : ℕ) (rows : List Row) (i : BlockIndex) : Powers :=
  rowPowers (rows[i.1.val - start]?.getD default) i.2.val
private theorem rowLoop_eq (s n j packed : ℕ) :
    rowLoop s n j packed =
      ∑ k : Fin n, certifiedSaving s (j + k.val) (powersAt k.val packed) := by
  induction n generalizing j packed with
  | zero => simp [rowLoop]
  | succ n ih =>
    rw [rowLoop, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, Nat.add_zero, powersAt, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show j + 1 + k.val = j + (k.val + 1) by omega]
private theorem rowScore_le (s : Fin 4013) (r : Row) :
    rowScore s.val r ≤ ∑ j : Fin 4650,
      if w2.Contains (s,j) then savings (s,j) (rowPowers r j.val) else 0 := by
  unfold rowScore
  split
  · rename_i h
    obtain ⟨hs, hs', hj, hj', hsum, hsum'⟩ := h
    rw [rowLoop_eq]
    let f (k : Fin r.count) : Fin 4650 := ⟨r.first + k.val, by have := k.isLt; omega⟩
    refine Finset.sum_le_sum_of_injOn f ?_ (by simp) ?_ (fun _ _ _ => Nat.zero_le _)
    · intro k _ l _ he
      apply Fin.ext
      have hv := congrArg Fin.val he
      dsimp [f] at hv
      omega
    · intro k _
      have hk := k.isLt
      have hw : w2.Contains (s, f k) := by
        simp only [w2, Window.Contains, f]
        omega
      rw [ite_eq_left hw]
      have he : rowPowers r (f k).val = powersAt k.val r.packed := by
        simp [rowPowers, f]
      rw [he]
      exact certifiedSaving_le _ _ hw
  · exact Nat.zero_le _
private theorem batchScore_eq (start : ℕ) (rows : List Row) :
    batchScore start rows = ∑ k : Fin rows.length, rowScore (start+k.val) (rows.get k) := by
  induction rows generalizing start with
  | nil => simp [batchScore]
  | cons r rs ih =>
    simp only [batchScore, List.length_cons, Fin.sum_univ_succ, Fin.val_zero,
      Nat.add_zero, List.get_eq_getElem, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ,
      ih]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show start + 1 + k.val = start + (k.val + 1) by omega]
theorem certificate (start : ℕ) (rows : List Row) (h : start + rows.length ≤ 4013) :
    ∃ p : BlockIndex → Powers, batchScore start rows ≤ savingsSum w2 p := by
  refine ⟨assignment start rows, ?_⟩
  rw [batchScore_eq, savingsSum, ← Finset.univ_product_univ, Finset.sum_product]
  let f (k : Fin rows.length) : Fin 4013 := ⟨start+k.val, by have := k.isLt; omega⟩
  refine Finset.sum_le_sum_of_injOn f ?_ (by simp) ?_ (fun _ _ _ => Nat.zero_le _)
  · intro k _ l _ he
    apply Fin.ext
    have hv := congrArg Fin.val he
    dsimp [f] at hv
    omega
  · intro k _
    have hp (j : Fin 4650) : assignment start rows (f k,j) =
        rowPowers (rows.get k) j.val := by
      simp [assignment, f, k.isLt]
    simp_rw [hp]
    exact rowScore_le (f k) (rows.get k)
end K1_13_2_3_5
end
