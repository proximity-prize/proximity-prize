import ProximityPrize.SubmissionLower.Z6970PlateauColumnChunk

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedPlateauEnvelope6970
open KoalaPiecewiseTriangle (Line)
open KoalaLinearWindow (Span)
open ExpandedPlateauIntegral6970 (poly clipped bill delta)
open ExpandedPlateauSum6970 (sumN spanLength lines)

def cross (l k : Line) : ℤ := -((k.a-l.a)/(k.d-l.d))

def switchAt (bound : ℤ) (l : Line) : List Line → ℤ
  | [] => bound
  | k :: ks => min (cross l k) (switchAt bound l ks)

def clippedFast (lo hi : ℤ) (l : Line) : ℤ :=
  let start := max lo (-(l.a/l.d))
  if hi ≤ start then 0 else poly (l.a + l.d*start) l.d (hi-start).toNat / 6

def billFast (lo hi : ℤ) (l : Line) : ℤ :=
  if hi ≤ lo then 0 else
    clippedFast lo hi l - clippedFast lo hi ⟨l.a-1835,l.d⟩

def integrate (lo hi : ℤ) (l : Line) : List Line → ℤ
  | [] => billFast lo hi l
  | k :: ks =>
    if hi ≤ lo then 0 else
      let t := switchAt hi l (k :: ks)
      billFast lo t l + integrate (max lo t) hi k ks

def strip (f c r : ℕ) : ℤ :=
  let n := spanLength c f r
  if n = 0 then 0 else
    let l := lines c f r
    integrate 0 n l.1 l.2

def column (f c : ℕ) : ℤ := strip f c 0 + strip f c 1 + strip f c 2

def columns (f start len : ℕ) : ℤ := sumN (fun i => column f (start+i)) len

end ExpandedPlateauEnvelope6970
