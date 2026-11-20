import ProximityPrize.SubmissionLower.PoleBlocks

namespace PoleSavings

open PoleBlocks
open scoped BigOperators

private def gap {B J : ℕ} (h : Fin (B+2*J)) : ℤ := (h.val : ℤ)-J

private def rowCount (B J s : ℕ) (g : ℤ) : ℕ :=
  min (slotCount g J s) (((B+J : ℕ) : ℤ)-g-s).toNat

/-- The offset slice counts each pair of admissible derivative index
and retained abscissa exponent exactly once. -/
theorem sum_rowCount (B J s : ℕ) (hs : s ≤ B) :
    (∑ h : Fin (B+2*J),
      min (slotCount ((h.val : ℤ)-J) J s) (((B+J : ℕ) : ℤ)-((h.val : ℤ)-J)-s).toNat) =
      (B+J-s)*(min J s+1) := by
  classical
  let W := B+J-s
  let C := min J s+1
  let dom := Sigma fun h : Fin (B+2*J) ↦ Fin (rowCount B J s (gap h))
  let A : dom → Fin W × Fin C := fun ⟨h,k⟩ ↦
    let g := gap h
    let lo := (-g).toNat
    let j := lo+k.val
    have hk := k.isLt
    have hk₁ : k.val < C-lo := (lt_min_iff.mp hk).1
    have hk₂ : k.val < (((B+J : ℕ) : ℤ)-g-s).toNat := (lt_min_iff.mp hk).2
    (⟨(g+j).toNat, by
      by_cases hnon : 0 ≤ g
      · dsimp [j,lo,W]
        omega
      · have hmin := min_le_left J s
        dsimp [j,lo,W,C] at *
        omega⟩, ⟨j, by dsimp [j]; omega⟩)
  have hinj : Function.Injective A := by
    rintro ⟨h,k⟩ ⟨h',k'⟩ he
    have hj := congrArg (fun p : Fin W × Fin C ↦ p.2.val) he
    have hx := congrArg (fun p : Fin W × Fin C ↦ p.1.val) he
    change (-(gap h)).toNat+k.val = (-(gap h')).toNat+k'.val at hj
    change (gap h + ((-(gap h)).toNat+k.val : ℕ)).toNat =
      (gap h' + ((-(gap h')).toNat+k'.val : ℕ)).toNat at hx
    have hh : h = h' := by
      apply Fin.ext
      unfold gap at hx hj
      omega
    subst h'
    congr 1
    apply Fin.ext
    omega
  have hsurj : Function.Surjective A := by
    rintro ⟨x,j⟩
    let g : ℤ := (x.val : ℤ)-j.val
    have hx := x.isLt
    have hj := j.isLt
    have hm := min_le_left J s
    let h : Fin (B+2*J) := ⟨(g+J).toNat, by dsimp [g,W,C] at *; omega⟩
    have hg : gap h = g := by dsimp [gap,h,g,C] at *; omega
    let lo := (-g).toNat
    let k : Fin (rowCount B J s (gap h)) := ⟨j.val-lo, by
      unfold rowCount slotCount
      rw [hg, lt_min_iff]
      dsimp [g,lo,W,C] at *
      constructor <;> omega⟩
    refine ⟨⟨h,k⟩, Prod.ext (Fin.ext ?_) (Fin.ext ?_)⟩
    · change (gap h + ((-(gap h)).toNat + (j.val-lo) : ℕ)).toNat = x.val
      rw [hg]
      dsimp [g,lo]
      omega
    · change (-(gap h)).toNat + (j.val-lo) = j.val
      rw [hg]
      dsimp [g,lo]
      omega
  have hcard := Fintype.card_congr (Equiv.ofBijective A ⟨hinj,hsurj⟩)
  change Fintype.card (Sigma fun h : Fin (B+2*J) ↦ Fin (rowCount B J s (gap h))) =
    Fintype.card (Fin W × Fin C) at hcard
  rw [Fintype.card_sigma, Fintype.card_prod] at hcard
  refine Eq.trans ?_ (by simpa only [W, C, Fintype.card_fin] using hcard)
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rfl

end PoleSavings
