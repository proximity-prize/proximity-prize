import ProximityPrize.SubmissionLower.HighMassBridge6921
import ProximityPrize.SubmissionLower.Hi6921Fast029

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace HighOrdinate6921

open K21 H21 Polynomial
open HighJoint6921 (HeightBand)
open HighMassBridge6921 (choose)

private theorem later_bank {w : ℤ} (lo : 3555 ≤ w) :
    (choose w).fullBank = H21_3.fullShape := by
  rw [choose, ite_eq_right (by omega : ¬ w ≤ 3554)]
  split_ifs <;> rfl

/-- Ordinate exclusion for each remaining band using its common actual full bank. -/
theorem later {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 3555 ≤ M.overhead) (hu : M.overhead ≤ 32932) (rows : Banks)
    (hJ : JetSource M F rows) (f : Equation) (hf : f ≠ 0)
    (hd : ∀ W < H21_3.fullShape.m*180139, ∀ P ∈ rows H21_3.fullShape W, P ≠ 0 →
      f ^ (H21_3.contactPower M.overhead.toNat H21_3.fullShape W - P.natDegree) ∣ P.leadingCoeff) :
    f.natDegree ≤ (H21.band M.overhead).yBound := by
  have hbank := later_bank hl
  apply HighMassBridge6921.ordinate hJ (by omega) hu f hf
  rw [hbank]
  exact hd

end HighOrdinate6921
