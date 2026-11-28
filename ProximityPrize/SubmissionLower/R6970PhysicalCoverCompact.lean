import ProximityPrize.SubmissionLower.Z6969FastTri

set_option autoImplicit false

namespace Research6969.PhysicalWindow.Compact

def check (test : ℕ → ℕ → Bool) (last : ℕ) : ℕ → List ℕ → Bool
  | lo, [] => lo == last + 1
  | lo, hi :: ends =>
    decide (lo ≤ hi ∧ hi ≤ last) && test lo hi && check test last (hi+1) ends

private theorem sound (fast : ℕ → ℕ → Bool) (test : ℕ → ℕ → Prop)
    (hs : ∀ lo hi, fast lo hi = true → test lo hi) (last first : ℕ) (ends : List ℕ)
    (h : check fast last first ends = true) : Cover test last first ends := by
  induction ends generalizing first with
  | nil =>
    change first = last+1
    exact beq_iff_eq.mp h
  | cons hi ends ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, h.1.1.2, hs _ _ h.1.2, ih _ h.2⟩

def triCheck (b : Request) (lo hi : ℕ) : Bool :=
  Fast.TFB b.shape.m b.shape.B b.shape.J b.shape.U b.bank.nodeRows b.bank.poleMoment
    b.reserve b.jet b.slope b.weight b.seed lo hi

def rectCheck (b : Request) (width lo hi : ℕ) : Bool :=
  Fast.RF b.shape.m b.shape.B b.shape.J b.shape.U width b.bank.nodeRows b.bank.poleMoment
    b.reserve b.jet b.slope b.weight b.seed lo hi

theorem triangleCover {b : Request} {last first : ℕ} {ends : List ℕ}
    (h : check (triCheck b) last first ends = true) : Cover (Triangular b) last first ends :=
  sound (triCheck b) (Triangular b) (triangular_of_fast b) last first ends h

theorem rectangleCover {b : Request} {width last first : ℕ} {ends : List ℕ}
    (h : check (rectCheck b width) last first ends = true) : Cover (Rectangle b width) last first ends :=
  sound (rectCheck b width) (Rectangle b width) (rectangle_of_fast b width) last first ends h

end Research6969.PhysicalWindow.Compact
