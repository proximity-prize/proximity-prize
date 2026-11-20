
namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

def nodes : Nat := 262144
def degree : Nat := 131071
def prime : Nat := 2130706433
def agreements : Nat := 180960
def poleWidth : Nat := 6676

structure Flag where
  r : Nat
  y : Nat
  t : Nat
  deriving DecidableEq, Repr

structure SourceShape where
  m : Nat
  B : Nat
  s : Nat
  U : Nat
  L : Nat
  k : Nat
  n0 : Nat
  q : Nat
  deriving DecidableEq, Repr

def SourceShape.carrierFlag (src : SourceShape) : Flag :=
  ⟨src.B, src.U, src.L + src.q⟩

def sumRange (n : Nat) (f : Nat → Nat) : Nat :=
  ((List.range n).map f).sum

theorem sumRange_add (m n : Nat) (f : Nat → Nat) :
    sumRange (m + n) f = sumRange m f + sumRange n (fun j => f (m + j)) := by
  unfold sumRange
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl

def triangle (h : Nat) : Nat :=
  (h + 1) * (h + 2) / 2

def shiftedTriangle (h a : Nat) : Nat :=
  if a ≤ h then triangle (h - a) else 0

def chooseTwo (n : Nat) : Nat :=
  n * (n - 1) / 2

def chooseThree (n : Nat) : Nat :=
  n * (n - 1) * (n - 2) / 6

def squares (n : Nat) : Nat :=
  n * (n - 1) * (2 * n - 1) / 6

def seedlessRectangle (a b h : Nat) : Nat :=
  triangle h + shiftedTriangle h (a + b) -
    (shiftedTriangle h a + shiftedTriangle h b)

def weightedTriangle (h z : Nat) : Nat :=
  triangle h * z - h * (h + 1) * (h + 2) / 3

def shiftedWeightedTriangle (h z a : Nat) : Nat :=
  if a ≤ h then weightedTriangle (h - a) (z - a) else 0

def weightedRectangle (a b z h : Nat) : Nat :=
  weightedTriangle h z + shiftedWeightedTriangle h z (a + b) -
    (shiftedWeightedTriangle h z a + shiftedWeightedTriangle h z b)

def sourceCutoff (src : SourceShape) (h : Nat) : Nat :=
  src.m * agreements - (if h < src.n0 then h else src.k) * (agreements - (degree - 2))

def ordinaryColumnRow (src : SourceShape) (h r : Nat) : Nat :=
  let D := sourceCutoff src h - (degree - 2) * h - (degree - 1) * r
  let z := src.L + 1 - h - r
  let y := min ((D + degree - 1) / degree) (src.U + 1 - h - r)
  y * D * z + degree * squares y - chooseTwo y * (D + degree * z)

def ordinaryColumnCount (src : SourceShape) : Nat :=
  sumRange (src.s + 1) fun h =>
    sumRange (src.B - 2 * h + 1) fun r => ordinaryColumnRow src h r

def localKernelOrder (m t s h : Nat) : Nat :=
  max ((m - t + 1) / 2) (m - t - (s - h))

def ordinaryRankRow (src : SourceShape) (t h : Nat) : Nat :=
  let z := src.L + 1 - h
  let height := src.U - h
  let b := src.B + 1 - 2 * h
  let k := localKernelOrder src.m t src.s h
  let all := weightedRectangle (t + 1) b z height
  if k ≤ t ∧ src.m - t + 2 * h ≤ src.B then
    if k ≤ height then all - weightedRectangle (t + 1 - k) (b - k) (z - k) (height - k)
    else all
  else all

def ordinaryRankBound (src : SourceShape) : Nat :=
  sumRange src.m fun t =>
    sumRange (min src.s src.U + 1) fun h => ordinaryRankRow src t h

def auxiliaryColumnRow (src : SourceShape) (j h r : Nat) : Nat :=
  let D := sourceCutoff src h - (degree + poleWidth) * j - (degree - 2) * h - (degree - 1) * r
  let y := min ((D + degree - 1) / degree) (src.U - j + 1 - h - r)
  y * D - degree * chooseTwo y

def auxiliaryColumnSlice (src : SourceShape) (j : Nat) : Nat :=
  sumRange (src.s + 1) fun h =>
    sumRange (src.B - 2 * h + 1) fun r => auxiliaryColumnRow src j h r

def auxiliaryRankSlice (src : SourceShape) (j : Nat) : Nat :=
  if j ≤ src.U then
    let m := src.m - j
    let U := src.U - j
    sumRange m fun t =>
      sumRange (min src.s U + 1) fun h =>
        let height := U - h
        let b := src.B + 1 - 2 * h
        let k := localKernelOrder m t src.s h
        let all := seedlessRectangle (t + 1) b height
        if k ≤ t ∧ m - t + 2 * h ≤ src.B then
          if k ≤ height then all - seedlessRectangle (t - k + 1) (b - k) (height - k)
          else all
        else all
  else 0

def globalColumnCount (src : SourceShape) : Nat :=
  ordinaryColumnCount src + sumRange src.q (fun j => auxiliaryColumnSlice src (j + 1))

def localRankBound (src : SourceShape) : Nat :=
  ordinaryRankBound src + sumRange src.q (fun j => auxiliaryRankSlice src (j + 1))

def sourceWellFormed (src : SourceShape) : Bool :=
  decide (2 * src.s ≤ src.B ∧ src.B ≤ src.m ∧ src.m + src.s ≤ src.U ∧
    src.U ≤ src.L ∧ src.k ≤ src.s ∧ src.s < src.m ∧ src.k + 1 ≤ src.n0 ∧
    2 * (src.n0 - src.k - 1) ≤ src.B ∧ src.s < prime ∧ src.q ≤ src.U) &&
  (List.range (src.s + 1)).all fun h =>
    decide (src.U ≤ (sourceCutoff src h + src.B - 1) / degree)

def sourceMargin (src : SourceShape) : Prop :=
  nodes * localRankBound src < globalColumnCount src

end ProximityPrize.SubmissionLower.Koala6844Receipts
