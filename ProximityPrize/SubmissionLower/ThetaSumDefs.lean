import Mathlib.Tactic

/-!
Kernel-evaluated entries of the theta savings sum.

`tsFast s j` is the saving of the theta bound over the block bound without products for the
block of grade `s` and offset index `j`; `chunk lo len` sums it over the grades `lo, …, lo+len-1`
and the offsets `0, …, 1646` inside the strip where the saving is positive.
-/

namespace ThetaSum

def fastDen (u : ℤ) : ℤ :=
  if u < 0 then 0 else u * (u * (2 * u + 21) + 66) / 72 + 1
def fastCum (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    if v ≤ d then fastDen v else
      let a := v - d
      let first := fastDen v - fastDen (a - 1) - fastDen (a - 2) -
        fastDen (a - 3)
      if v ≤ 2 * d + 2 then first else
        let b := v - 2 * d
        first + fastDen (b - 3) + fastDen (b - 4) + fastDen (b - 5)
def signedKernel (d j h : ℤ) : ℤ :=
  let low := 1649 - j
  let balance := h - (1650 - j) + d
  if balance < 0 then fastCum d 1650 - fastCum d low else
    let removed := min d (balance / 4) + 1
    fastCum d 1650 - fastCum d h + fastCum (d - removed) (h - 3 * removed) -
      fastCum (d - removed) low
def rangeSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rangeSum f n + f n
def tsFast (s j : ℕ) : ℕ :=
  let d : ℤ := min (s : ℤ) 1650
  let h : ℤ := 4649 - (s : ℤ) - j
  let old := fastCum d 1650 - fastCum d (1649 - (j : ℤ))
  let base := (old - max 0 (signedKernel d j h)).toNat
  let theta := (fastCum d h - fastCum d (1649 - (j : ℤ) - 3 * ((s : ℤ) + j - 2999))).toNat
  base - min base theta
def entry (s j : ℕ) : ℕ :=
  if 3000 ≤ s + j ∧ 4 * (s + j - 3000) ≤ s - 1354 ∧
      9 * (s - 2304) ≤ 20 * (s + j - 3000) + 19 then tsFast s j else 0
def row (s : ℕ) : ℕ := rangeSum (entry s) 1647
def chunk (lo len : ℕ) : ℕ := rangeSum (fun t => row (lo + t)) len

theorem rangeSum_append (f : ℕ → ℕ) (a b : ℕ) :
    rangeSum f (a + b) = rangeSum f a + rangeSum (fun k => f (a + k)) b := by
  induction b with
  | zero => simp [rangeSum]
  | succ b ih =>
    change rangeSum f (a + b) + f (a + b) =
      rangeSum f a + (rangeSum (fun k => f (a + k)) b + f (a + b))
    rw [ih, Nat.add_assoc]

theorem chunk_append (lo a b : ℕ) : chunk lo (a + b) = chunk lo a + chunk (lo + a) b := by
  unfold chunk
  rw [rangeSum_append]
  simp only [Nat.add_assoc]

theorem chunk_join {lo a b u v : ℕ} (hu : chunk lo a = u) (hv : chunk (lo + a) b = v) :
    chunk lo (a + b) = u + v := by
  rw [chunk_append, hu, hv]

end ThetaSum
