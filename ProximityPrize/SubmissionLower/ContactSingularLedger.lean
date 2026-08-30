import ProximityPrize.SubmissionLower.ContactParameters

namespace ProximityPrize.SubmissionLower.ContactSingularLedger

open scoped BigOperators
open ContactParameters

def sumVector {I : Type} [Fintype I] (v : I -> DegreeVector) : DegreeVector :=
  ⟨∑ i, (v i).y, ∑ i, (v i).r, ∑ i, (v i).z⟩

def vectorLE (a b : DegreeVector) : Prop :=
  a.y ≤ b.y ∧ a.r ≤ b.r ∧ a.z ≤ b.z

def dot (a b : DegreeVector) : Nat :=
  a.y * b.y + a.r * b.r + a.z * b.z

theorem dot_mono_left {a b : DegreeVector} (c : DegreeVector)
    (h : vectorLE a b) : dot a c ≤ dot b c :=
  Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1)
      (Nat.mul_le_mul_right c.r h.2.1))
    (Nat.mul_le_mul_right c.z h.2.2)

theorem dot_sum_left {I : Type} [Fintype I]
    (v : I -> DegreeVector) (a : DegreeVector) :
    dot (sumVector v) a = ∑ i, dot (v i) a := by
  simp only [dot, sumVector, Finset.sum_add_distrib, Finset.sum_mul]

end ProximityPrize.SubmissionLower.ContactSingularLedger
