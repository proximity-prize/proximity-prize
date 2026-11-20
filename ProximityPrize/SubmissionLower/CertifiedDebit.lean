import ProximityPrize.SubmissionLower.PoleGrid
import ProximityPrize.SubmissionLower.RowTotal
import ProximityPrize.SubmissionLower.StructuredSource

namespace CertifiedDebit
open K1 K1_14 K1_14_1 PoleFamily PoleGrid PoleGlobal
open scoped BigOperators Polynomial
noncomputable section

theorem sum_rows (s : Shape) : (∑ v : Label s.U s.B s.J, rowBound v) = RowTotal.allRows s := by
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  rfl

theorem sum_blocks (s : Shape) :
    (∑ v : Label s.U s.B s.J, blockBound v) = blockSum s := by
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  rfl

theorem charge_comparison (s : Shape) (h saved : ℕ)
    (cert : saved ≤ (∑ v : Label s.U s.B s.J, rowBound v) -
                    (∑ v : Label s.U s.B s.J, blockBound v)) :
    2*h*blockSum s ≤ poleCredit h s + (poleSeedDebit h s - (2*h)*saved) := by
  have cap : (∑ v : Label s.U s.B s.J, blockBound v) ≤ ∑ v : Label s.U s.B s.J, rowBound v :=
    Finset.sum_le_sum fun _ _ => min_le_right _ _
  rw [sum_blocks,sum_rows] at cap
  rw [sum_blocks,sum_rows] at cert
  have hsum : blockSum s + saved ≤ RowTotal.allRows s := by omega
  have hs := Nat.mul_le_mul_left (2*h) hsum
  rw [Nat.mul_add,RowTotal.old_charge] at hs
  omega

/-- A numerical charge can be consumed by the source proof without the
elaborator or kernel evaluating the enormous normalized block matrix. -/
theorem source_with_receipt (h : ℕ) (hl : 2442 ≤ h) (hu : h ≤ 32970)
    (D : PoleData h) (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ)
    (hw : rawWidthCond h s W) (saved : ℕ)
    (cert : saved ≤ (∑ v : Label s.U s.B s.J, rowBound v) -
                    (∑ v : Label s.U s.B s.J, blockBound v)) :
    rawVolumeAt h s W ≤ physicalDebit s + (poleSeedDebit h s - (2*h)*saved) +
      ∑ t ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word s t) := by
  have h1 := StructuredSource.source_floor h hl hu D Crt word s W hw
  have h2 := charge_comparison s h saved cert
  omega

def runSum (f : ℕ → ℕ) : ℕ → ℕ | 0 => 0 | n+1 => runSum f n + f n
theorem sum_run (f : ℕ → ℕ) (n : ℕ) : ∑ k ∈ Finset.range n, f k = runSum f n := by
  induction n with
  | zero => simp [runSum]
  | succ n ih => rw [Finset.sum_range_succ,ih,runSum]

theorem row_computation (B J g : ℕ) : rowSum B J g =
    runSum (fun s => min (min J s+1) (B+J-g-s)) (B+1) := by
  unfold rowSum
  rw [Fin.sum_univ_eq_sum_range (fun s => min (min J s+1) (B+J-g-s)) (B+1), sum_run]

theorem col_computation (B J l : ℕ) : colSum B J l =
    runSum (fun q => if l ≤ q then min J q + 1 else 0) (B+1) := by
  rw [← sum_run, ← Finset.sum_filter]
  unfold colSum
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
  omega

end
end CertifiedDebit
