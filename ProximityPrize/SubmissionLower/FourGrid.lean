import ProximityPrize.SubmissionLower.PoleGrid

namespace FourGrid

open PoleGrid PoleFamily
open scoped BigOperators

/-- The boundary at grid index k for an interval of length L. -/
def cut (L k : ℕ) : ℕ := k*L/4

def offsetLo (B J : ℕ) (i : Fin 4) : ℕ := cut (B+J) i.val

def offsetHi (B J : ℕ) (i : Fin 4) : ℕ := cut (B+J) (i.val+1)-1

def gradeLo (B : ℕ) (k : Fin 4) : ℕ := 1+cut B k.val

def gradeHi (B : ℕ) (k : Fin 4) : ℕ := cut B (k.val+1)

private theorem cut_mono (L : ℕ) : Monotone (cut L) := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.mul_le_mul_right L hij)

private theorem cut_step {L : ℕ} (hL : 4 ≤ L) (i : ℕ) :
    cut L i + 1 ≤ cut L (i+1) := by
  unfold cut
  rw [Nat.add_mul]
  have h := show i*L+4 ≤ i*L+1*L by omega
  exact (show (i*L)/4+1 ≤ (i*L+4)/4 by omega).trans (Nat.div_le_div_right h)

private theorem cut_le_length (L : ℕ) (i : Fin 4) : cut L (i.val+1) ≤ L := by
  have hi := i.isLt
  have h := cut_mono L (show i.val+1 ≤ 4 by omega)
  have he : cut L 4 = L := by simp [cut]
  exact h.trans_eq he

/-- One inclusive rectangle in the quarter grid, with positive input grades. -/
def rectangle {B J : ℕ} (hB : 4 ≤ B) (p : Fin 4 × Fin 4) : Rectangle B J where
  gradeLo := gradeLo B p.2
  gradeHi := gradeHi B p.2
  offsetLo := offsetLo B J p.1
  offsetHi := offsetHi B J p.1
  gradeOrder := by
    unfold gradeLo gradeHi
    have hs := cut_step hB p.2.val
    omega
  gradeBound := cut_le_length B p.2
  offsetOrder := by
    unfold offsetLo offsetHi
    have hs := cut_step (show 4 ≤ B+J by omega) p.1.val
    omega
  offsetBound := by
    unfold offsetHi
    have h := cut_le_length (B+J) p.1
    omega

private theorem offsets_separated {B J : ℕ} (hB : 4 ≤ B) {i j : Fin 4}
    (h : i < j) : offsetHi B J i < offsetLo B J j := by
  unfold offsetHi offsetLo
  have hm := cut_mono (B+J) (show i.val+1 ≤ j.val from Nat.succ_le_of_lt h)
  have hp := cut_step (show 4 ≤ B+J by omega) i.val
  omega

private theorem grades_separated (B : ℕ) {i j : Fin 4}
    (h : i < j) : gradeHi B i < gradeLo B j := by
  unfold gradeHi gradeLo
  have hm := cut_mono B (show i.val+1 ≤ j.val from Nat.succ_le_of_lt h)
  omega

theorem rectangles_separated {B J : ℕ} (hB : 4 ≤ B) :
    Pairwise (fun p p' : Fin 4 × Fin 4 ↦ Separated (rectangle (J := J) hB p) (rectangle hB p')) := by
  intro p p' hne
  by_cases h : p.1 = p'.1
  · have hk : p.2 ≠ p'.2 := fun e ↦ hne (Prod.ext h e)
    rcases lt_or_gt_of_ne hk with hk | hk
    · exact Or.inl (grades_separated B hk)
    · exact Or.inr (Or.inl (grades_separated B hk))
  · rcases lt_or_gt_of_ne h with hi | hi
    · exact Or.inr (Or.inr (Or.inl (offsets_separated hB hi)))
    · exact Or.inr (Or.inr (Or.inr (offsets_separated hB hi)))

/-- The directly computable saving certified by the 16 rectangular endpoints. -/
def fourGridSaving (U B J : ℕ) : ℕ :=
  ∑ i : Fin 4, ∑ k : Fin 4,
    (U-B+1)*(offsetHi B J i-offsetLo B J i+1)*(gradeHi B k-gradeLo B k+1) *
      (rowSum B J (offsetHi B J i) - colSum B J (gradeLo B k))

theorem fourGridSaving_le {U B J : ℕ} (hB : 4 ≤ B) (hU : B ≤ U) :
    fourGridSaving U B J ≤
      (∑ v : Label U B J, rowBound v) - (∑ v : Label U B J, blockBound v) := by
  have h := rectangles_saving hU (rectangle (J := J) hB)
    (rectSamples_injective_of_separated hU _ (rectangles_separated hB))
  rw [Fintype.sum_prod_type] at h
  exact h

/-- Shape-only coefficient, independent of the seed cap. -/
def gridCoefficient (B J : ℕ) : ℕ :=
  ∑ i : Fin 4, ∑ k : Fin 4,
    (offsetHi B J i-offsetLo B J i+1)*(gradeHi B k-gradeLo B k+1) *
      (rowSum B J (offsetHi B J i) - colSum B J (gradeLo B k))

theorem fourGridSaving_eq (U B J : ℕ) :
    fourGridSaving U B J = (U-B+1)*gridCoefficient B J := by
  unfold fourGridSaving gridCoefficient
  simp only [Finset.mul_sum, Nat.mul_assoc]

theorem gridCoefficient_saving {U B J : ℕ} (hB : 4 ≤ B) (hU : B ≤ U) :
    (U-B+1)*gridCoefficient B J ≤
      (∑ v : Label U B J, rowBound v) - (∑ v : Label U B J, blockBound v) := by
  rw [← fourGridSaving_eq]
  exact fourGridSaving_le hB hU

end FourGrid
