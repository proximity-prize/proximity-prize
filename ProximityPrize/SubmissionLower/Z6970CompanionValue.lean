import ProximityPrize.SubmissionLower.Z6970CompanionRegistry
set_option autoImplicit false
set_option Elab.async false

namespace Height2307Companion
open K1_13 (Shape InBox mixed32 chart liftedChart ceilDiv)

def surface (p q : Shape) : ℕ :=
  let L : ℕ := 133379
  let g : Shape := ⟨max p.b (p.j+1),p.j+1,min (p.t+1) ((p.j+1)/3)⟩
  let a := liftedChart (L+1) p
  let b := liftedChart (L+2) p
  min (mixed32 p q (chart (L+1) p) (chart (L+2) p))
    (mixed32 p q a b + (L+1)*mixed32 p q g b + (L+2)*mixed32 p q g a)

def value (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q : Shape := ⟨4024,1679,500⟩
  let h := chart 133379 p
  let numerator := ceilDiv (surface p q) 32 +
    ceilDiv ((82414+2*46352)*x.b*q.b*(chart 133380 p).b) 46352
  let aux := q.plus (p.scale 4)
  let curves := mixed32 p q aux h + 2*x.t*mixed32 p p p h
  let points := mixed32 p q aux p + 2*x.t*mixed32 p p p p
  ceilDiv numerator l + 2*133378*x.b*q.b +
    ceilDiv (82414*curves + 2*46352*points) (32*46352)

def Corners (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) : Prop :=
  ∀ (x y : Shape) (m b j : ℕ), legal x → InBox x y → 3*y.t ≤ y.j →
    b ≤ x.b → j ≤ x.j → 0<m → m≤ord b j → cost x ≤ value y m

structure Anchor where
  k : ℕ
  b : ℕ
  j : ℕ
  m : ℕ
  deriving DecidableEq

def Supports (tab : List Anchor) (k : ℕ) (ord : ℕ → ℕ → ℕ) : Prop :=
  (∀ b j, 1 ≤ ord b j) ∧ ∀ a ∈ tab, a.k=k → a.m ≤ ord a.b a.j

def Within (r : Rule) (cost : Shape → ℕ) : Prop :=
  ∀ x, legal x → InBox x r.cap → cost x ≤ charge r.byDegree r.rate x

end Height2307Companion
