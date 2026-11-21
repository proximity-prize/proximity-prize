import ProximityPrize.SubmissionLower.Low48PrimaryPivotAffine

set_option Elab.async false
namespace Low48PrimaryPivot
open K1_13_2_3

def affineFeeChunk (w : Window) (start count : ℕ) : ℤ :=
  ((List.range' start count).map (directSlab w)).sum

theorem affineFeeChunk_append (w : Window) (start left right : ℕ) :
    affineFeeChunk w start (left+right) =
      affineFeeChunk w start left + affineFeeChunk w (start+left) right := by
  unfold affineFeeChunk
  rw [← List.range'_append_1, List.map_append, List.sum_append]

theorem affineFeeChunk_succ (w : Window) (first size : ℕ) :
    affineFeeChunk w first (size+1) = directSlab w first + affineFeeChunk w (first+1) size := by
  rfl

def affineFeeCertified (w : Window) : ℕ → List ℤ → Prop
  | _, [] => True
  | first, row :: tail => directSlab w first = row ∧ affineFeeCertified w (first+1) tail

theorem affineFeeCertified_eq (w : Window) (first : ℕ) (rows : List ℤ)
    (h : affineFeeCertified w first rows) :
    affineFeeChunk w first rows.length = rows.sum := by
  induction rows generalizing first with
  | nil => rfl
  | cons row tail ih =>
    change directSlab w first = row ∧ affineFeeCertified w (first+1) tail at h
    rw [List.length_cons, affineFeeChunk_succ, h.1, ih (first+1) h.2, List.sum_cons]

theorem feeCompute_affine (w : Window) : feeCompute w = affineFeeChunk w 0 551 := by
  unfold feeCompute affineFeeChunk
  rw [List.range_eq_range']
  apply congrArg List.sum
  exact List.map_congr_left fun f _ => (directSlab_eq w f).symm

end Low48PrimaryPivot
