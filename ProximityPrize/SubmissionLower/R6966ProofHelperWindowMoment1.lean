import ProximityPrize.SubmissionLower.KoalaRectPoleBalance

set_option Elab.async false

-- merged module R6966ProofHelperWindowMoments
section Merged_R6966ProofHelperWindowMoments

set_option Elab.async false

namespace Research6966.HelperWindowMoments
open Finset P1_7_1 P1_7_1_3
set_option maxHeartbeats 600000

/-- A supplied cutoff replaces the search in each pole estimate. Every
admissible cutoff yields a bound, and its choice is numeric data. -/
def cutOffset (B J t k : ℕ) : ℕ :=
  (pivotRank6 B J t*k+excess6 B J t k-pivotWeight6 B J t)/6

theorem offset_le (B J t k : ℕ) (hk : k ≤ B) : offsetMoment B J t ≤ cutOffset B J t k := by
  let R := ∑ q ∈ range (B+1), pivotCount B J t q
  let W := ∑ q ∈ range (B+1), q*pivotCount B J t q
  let E := ∑ q ∈ range (B+1), (q-k)*columnCount B J t q
  have bound : largestGradeSum B J t R ≤ R*k+E :=
    inf'_le _ (mem_range.mpr (Nat.lt_succ_iff.mpr hk))
  unfold cutOffset
  rw [← pivot_rank, ← pivot_weight, ← column_excess]
  change largestGradeSum B J t R-W ≤ (6*R*k+6*E-6*W)/6
  rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_sub_left_distrib, Nat.mul_div_cancel_left _ (by decide)]
  exact Nat.sub_le_sub_right bound W

def packedBlock (B J : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, start, packed =>
    cutOffset B J start (min B (packed%16384)) + packedBlock B J n (start+1) (packed/16384)

theorem block_le (B J length start packed : ℕ) :
    (∑ i ∈ range length, offsetMoment B J (start+i)) ≤ packedBlock B J length start packed := by
  induction length generalizing start packed with
  | zero => simp [packedBlock]
  | succ len ih =>
    rw [sum_range_succ', packedBlock, Nat.add_zero, Nat.add_comm (cutOffset B J start _)]
    apply Nat.add_le_add ?_ (offset_le B J start _ (min_le_left _ _))
    apply le_trans ?_ (ih (start+1) (packed/16384))
    apply le_of_eq
    apply sum_congr rfl
    intro i _
    exact congrArg (offsetMoment B J) (by omega)

private theorem early_zero (B J t : ℕ) (lt : t < J) : offsetMoment B J t = 0 := by
  let R := ∑ q ∈ range (B+1), pivotCount B J t q
  have equal (q : ℕ) (mem : q ∈ range (B+1)) : pivotCount B J t q = columnCount B J t q := by
    have qb := mem_range.mp mem
    unfold pivotCount
    apply min_eq_left
    dsimp only [columnCount]
    omega
  have inf : largestGradeSum B J t R ≤ R*0+
      ∑ q ∈ range (B+1), (q-0)*columnCount B J t q :=
    inf'_le _ (mem_range.mpr (Nat.zero_lt_succ B))
  simp only [Nat.mul_zero,Nat.zero_add,Nat.sub_zero] at inf
  change largestGradeSum B J t R - (∑ q ∈ range (B+1), q*pivotCount B J t q) = 0
  apply Nat.sub_eq_zero_of_le
  exact inf.trans_eq (sum_congr rfl (fun q mem => congrArg (q*·) (equal q mem).symm))

structure Block where
  length : ℕ
  packed : ℕ
  total : ℕ

def Checked (B J : ℕ) : ℕ → List Block → Prop
  | _, [] => True
  | start, entry::rest =>
    packedBlock B J entry.length start entry.packed = entry.total ∧
      Checked B J (start+entry.length) rest

private theorem partition_le (B J : ℕ) (parts : List Block) (start : ℕ) (checked : Checked B J start parts) :
    (∑ i ∈ range (parts.map Block.length).sum, offsetMoment B J (start+i)) ≤ (parts.map Block.total).sum := by
  induction parts generalizing start with
  | nil => simp
  | cons entry rest ih =>
    obtain ⟨this,more⟩ := checked
    simp only [List.map_cons,List.sum_cons]
    rw [sum_range_add]
    refine Nat.add_le_add ((block_le B J entry.length start entry.packed).trans_eq this) ?_
    simpa only [← Nat.add_assoc] using ih (start+entry.length) more

theorem grouped_from_blocks (B J total : ℕ) (parts : List Block)
    (checked : Checked B J J parts) (length : (parts.map Block.length).sum = B+J)
    (price : (parts.map Block.total).sum ≤ total) : groupedPoleMoment B J ≤ total := by
  rw [groupedPoleMoment, show B+2*J=J+(B+J) by omega, sum_range_add]
  rw [sum_eq_zero (fun t ht => early_zero B J t (mem_range.mp ht)), Nat.zero_add, ← length]
  exact (partition_le B J parts J checked).trans price

end Research6966.HelperWindowMoments

end Merged_R6966ProofHelperWindowMoments

-- merged module R6966ProofHelperWindowMoment1
section Merged_R6966ProofHelperWindowMoment1

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0









































































end Research6966.HelperWindowCatalogue

end Merged_R6966ProofHelperWindowMoment1
