import ProximityPrize.SubmissionLower.Z6970PlateauEnvelope

set_option autoImplicit false
namespace ExpandedPlateauNatural6970

structure Ray where
  base : ℕ
  slope : ℕ

def ceiling (n d : ℕ) : ℕ := (n + (d - 1)) / d

def stop (hi : ℕ) (l : Ray) : List Ray → ℕ
  | [] => hi
  | k :: ks => min (ceiling (l.base-k.base) (k.slope-l.slope)) (stop hi l ks)

def polynomial (a d n : ℕ) : ℕ :=
  6*n*a*(a+1) + 3*d*(2*a+1)*n*(n-1) + d*d*n*(n-1)*(2*n-1)

def clipped (offset lo hi : ℕ) (l : Ray) : ℕ :=
  let start := max lo (ceiling (offset-l.base) l.slope)
  if hi ≤ start then 0 else
    polynomial (l.base+l.slope*start-offset) l.slope (hi-start) / 6

def bill (lo hi : ℕ) (l : Ray) : ℕ :=
  if hi ≤ lo then 0 else clipped 10000 lo hi l - clipped 11835 lo hi l

def integrate (lo hi : ℕ) (l : Ray) : List Ray → ℕ
  | [] => bill lo hi l
  | k :: ks => if hi ≤ lo then 0 else
      let t := stop hi l (k::ks)
      bill lo t l + integrate (max lo t) hi k ks

def strip (f c r : ℕ) : ℕ :=
  let n := ExpandedPlateauSum6970.spanLength c f r
  if n = 0 then 0 else
    let w := 1679-2*c-3*f
    let u := 500-f
    let base := 11321+2*r+c+f-w
    integrate 0 n ⟨base-r-min c u,3⟩ [⟨base-(w+c)/2,6⟩, ⟨base-(2*w+u-r)/3,7⟩,
      ⟨base+r-w,8⟩, ⟨base+r-w-u,9⟩, ⟨base+2*r-2*w,12⟩]

def column (f c : ℕ) : ℕ := strip f c 0 + strip f c 1 + strip f c 2

def columns (f start : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => columns f start n + column f (start+n)

end ExpandedPlateauNatural6970
