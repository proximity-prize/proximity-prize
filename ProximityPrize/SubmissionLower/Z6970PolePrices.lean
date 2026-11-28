import ProximityPrize.Benchmark.TargetLower

set_option autoImplicit false

namespace PoleAffine6970

def tri (k : ℕ) : ℕ := (k+1).choose 2

def cubicSum (N n : ℕ) : ℕ :=
  (N+1-n) * Nat.fast_choose (n+1) 3 + Nat.fast_choose (n+1) 4

def charge (N H k : ℕ) : ℕ := (N-k) * (tri k - tri (k-H))

def chargePrefix (N H n : ℕ) : ℕ := cubicSum N n - cubicSum (N-H) (n-H)

def tailTerm (B J e : ℕ) : ℕ :=
  let w := min (J+1) e
  let p := (e+1)/2
  let r := p*(e+1-p)
  let d := (r-1)/w
  (2*r*(B-d) + w*d*(d+1) - r*(e-1))/2

def tailSum (B J : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => tailSum B J n + tailTerm B J (n+1)

def budget (B J : ℕ) : ℕ :=
  chargePrefix (B+1) (J+1) (B-J+1) + tailSum B J (2*J)

end PoleAffine6970
