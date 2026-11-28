import ProximityPrize.SubmissionLower.Z6970PlateauChunk
set_option Elab.async false
set_option autoImplicit false

namespace ExpandedPlateauSum6970

def columnChunk (f start len : ℕ) : ℤ := sumN (fun i => column f (start+i)) len

theorem join_columns {f start a b : ℕ} {u v : ℤ}
    (hx : columnChunk f start a = u) (hy : columnChunk f (start+a) b = v) :
    columnChunk f start (a+b) = u+v := by
  have h : columnChunk f start (a+b) = columnChunk f start a + columnChunk f (start+a) b := by
    simp only [columnChunk,sumN_eq,Finset.sum_range_add,Nat.add_assoc]
  rw [h,hx,hy]

theorem one_from_columns (f : ℕ) : chunk f 1 = columnChunk f 0 ((1681-3*f)/2) := by
  rw [chunk_one]
  simp [row,columnChunk]

end ExpandedPlateauSum6970
